module
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.FundamentalExactSequenceSectionsSupplement
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Geometrically.CurveClassesBaseChange
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.VeryGeneralFibreLineBundles
import MMP.AlgebraicGeometry.Geometrically.NumericalDivisorClassesBaseChange
import MMP.AlgebraicGeometry.Resolution.OrderUpperSemicontinuous
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.AlgebraicGeometry.Curves.DegreeEuler
import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.NormChernAverage
import MMP.AlgebraicGeometry.Resolution.DivisorTupleRestrictionLift
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.RingTheory.Kaehler.PluriformProduct
import MMP.AlgebraicGeometry.Resolution.SNCHypersurfaceCentres
import MMP.AlgebraicGeometry.Resolution.SNCFieldChange
import MMP.AlgebraicGeometry.Intersection.PairingSeparation
import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.MMP.Threefold.Basic
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
import MMP.AlgebraicGeometry.Modules.CurveFibreLineBundle
import MMP.AlgebraicGeometry.Resolution.SncPairStratumBlowup
import MMP.AlgebraicGeometry.Positivity.SemiampleDescent
import MMP.AlgebraicGeometry.Divisor.DivisorialPullback
import MMP.AlgebraicGeometry.ProjectiveSpectrum.ConeAlgebraRelativelyAmple
import MMP.AlgebraicGeometry.Positivity.RelativelyAmple
import MMP.AlgebraicGeometry.SpreadingOut.LocalEquations
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
import MMP.AlgebraicGeometry.Singularities.BoundaryLowering
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
public import StacksFrontier.AlgebraicGeometry.Varieties.FunctionFieldEquivalence.Basic
public import MMP.AlgebraicGeometry.Morphisms.FiniteFunctionField

/-!
# Programs are detected after algebraically closed base extension

Let `k₀ ⊆ K` be algebraically closed fields of characteristic zero. Take the data of a
would-be program over `k₀` (`MMP.Fourfold.Program`): models `(X_i, B_i)` with canonical
divisors `K_i`, all cut out by one rational top form over `k₀`, rays `R_i ⊆ NE̅(X_i)`, contractions
`f_i : X_i ⟶ Z_i`, small
morphisms `f_i⁺ : X_{i+1} ⟶ Z_i`, and possibly a last contraction `g : X_n ⟶ T` of fibre type.
Base change everything to `K`. The models, targets, morphisms, canonical divisors and boundaries
are base changed, and each ray `R_i` is transported to `φ_i(R_i)` by the base-extension map
`φ_i : N₁(X_i)_ℝ → N₁(X_{i,K})_ℝ` of curve classes. The data over `k₀` satisfy every condition
of `MMP.Fourfold.Program` if and only if their base change over `K` does.

## Main results

* `MMP.Fourfold.program_conditions_iff_of_isPullback`: the conditions of a program hold over
  `k₀` if and only if they hold after base change to `K`.

## Implementation notes

Base change is encoded abstractly. Each model `X_{i,K}` comes with a pullback square over
`Spec K ⟶ Spec k₀` (`π i`), and likewise each target `Z_{i,K}` (`πZ i`) and `T_K` (`πT`). The
morphisms over `K` lie over `K` and are compatible with the projections, which pins them as the
base changes. A divisor `D` on `X_{i,K}` is the base change of `D₀` on `X_i` when two things hold.
First, the coefficient of `D` at a prime divisor `P` is that of `D₀` at `P₀` whenever
`closure P = π⁻¹(closure P₀)`. Second, every prime divisor in the support of `D` is of this
form. Curves are base changed the same way in
`MMP.Fourfold.map_closedConeOfCurves_eq_of_isPullback`, and the maps `φ_i` are pinned by the
same property used there.

Base change is only required where a program has data: for the models `X_i` with `i ≤ n`, for
the steps `X_i ⟶ Z_i ⟵ X_{i+1}` with `i < n`, and for the final contraction when there is one.
The remaining entries of the sequences are unconstrained, as in `MMP.Fourfold.Program`.

The conditions of a program are the propositional fields of `MMP.Fourfold.Program`, stated for
the given data. The data themselves, together with the typeclass assumptions the structure
carries, are fixed on both sides.

## References

* [KM98] Kollár, Mori, *Birational Geometry of Algebraic Varieties*.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MMP.Mori MMP.Fourfold
open MMP.Spreading (chart_dim_eq_of_isPullback form_eq_smul_of_isPullback
  functionFieldMap_germToFunctionField germToFunctionField_app_map)

universe u

namespace MMP.ProgramBaseChange

section FieldChangeBasics

variable {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K] [IsAlgClosed k₀]

/-- Normality, integrality and dimension are insensitive to a base change along
`Spec K ⟶ Spec k₀`, in any pullback square. -/
public theorem invariants_of_isPullback {X W : Scheme.{u}} (f : X ⟶ Spec (.of k₀))
    [LocallyOfFiniteType f] {p : W ⟶ X} {s : W ⟶ Spec (.of K)}
    (h : IsPullback p s f (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))) :
    (IsNormal X ↔ IsNormal W) ∧ (IsIntegral X ↔ IsIntegral W) ∧
      topologicalKrullDim W = topologicalKrullDim X := by
  obtain ⟨-, hint, hnor, -, hdim⟩ :=
    MMP.isReduced_isIntegral_isNormal_dim_baseChange_of_isAlgClosed (K := K) f
  let e := h.isoPullback
  refine ⟨hnor.trans ⟨fun _ => isNormal_of_iso e, fun _ => isNormal_of_iso e.symm⟩,
    hint.trans ⟨fun _ => MMP.isIntegral_of_iso e.symm,
      fun _ => MMP.isIntegral_of_iso e⟩, ?_⟩
  have h1 := hdim Set.univ (IsOpen.isLocallyClosed isOpen_univ)
  rw [Set.preimage_univ] at h1
  rw [(Scheme.homeoOfIso e).isHomeomorph.topologicalKrullDim_eq,
    ← (Homeomorph.Set.univ _).isHomeomorph.topologicalKrullDim_eq,
    ← (Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq]
  exact h1

end FieldChangeBasics

section Square

variable {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K] [IsAlgClosed k₀] {X W : Scheme.{u}}
  (f : X ⟶ Spec (.of k₀)) [LocallyOfFiniteType f] {p : W ⟶ X} {s : W ⟶ Spec (.of K)}

/-- The preimage of a locally closed subset under the projection of a base change of the ground
field has the same dimension. -/
private lemma topologicalKrullDim_preimage_of_isPullback
    (h : IsPullback p s f (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))) {Z : Set X}
    (hZ : IsLocallyClosed Z) : topologicalKrullDim (p ⁻¹' Z) = topologicalKrullDim Z := by
  obtain ⟨-, -, -, -, hdim⟩ :=
    MMP.isReduced_isIntegral_isNormal_dim_baseChange_of_isAlgClosed (K := K) f
  rw [← hdim Z hZ]
  have hp (w : W) : p w = pullback.fst f _ (h.isoPullback.hom w) := by
    rw [← Scheme.Hom.comp_apply, h.isoPullback_hom_fst]
  refine (Homeomorph.subtype (Scheme.homeoOfIso h.isoPullback) fun w => ?_).isHomeomorph
    |>.topologicalKrullDim_eq
  simp only [Set.mem_preimage, Scheme.homeoOfIso_apply]
  rw [hp w]

/-- The preimage of an irreducible closed subset under the projection of a base change of an
algebraically closed ground field is irreducible. -/
private lemma isIrreducible_preimage_of_isPullback
    (h : IsPullback p s f (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))) {Z : Set X}
    (hZc : IsClosed Z) (hZ : IsIrreducible Z) : IsIrreducible (p ⁻¹' Z) := by
  let C : TopologicalSpace.Closeds X := ⟨Z, hZc⟩
  let I := Scheme.IdealSheafData.vanishingIdeal C
  have : IsIntegral I.subscheme :=
    StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible C hZ
  have : LocallyOfFiniteType (I.subschemeι ≫ f) := inferInstance
  have hsq : IsPullback (pullback.snd p I.subschemeι) (pullback.fst p I.subschemeι ≫ s)
      (I.subschemeι ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) :=
    (IsPullback.of_hasPullback p I.subschemeι).flip.paste_vert h
  obtain ⟨-, hint, -⟩ :=
    MMP.isReduced_isIntegral_isNormal_dim_baseChange_of_isAlgClosed (K := K) (I.subschemeι ≫ f)
  have : IsIntegral (pullback (I.subschemeι ≫ f)
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))) := hint.1 ‹_›
  have : IsIntegral (pullback p I.subschemeι) :=
    MMP.isIntegral_of_iso hsq.isoPullback.symm
  have hr : Set.range (pullback.fst p I.subschemeι) = p ⁻¹' Z := by
    rw [Scheme.Pullback.range_fst, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  rw [← hr, ← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ _).image _ (Scheme.Hom.continuous _).continuousOn

/-- Under a base change of an algebraically closed ground field of an integral scheme, coheights
can only grow, and every point has a preimage of the same coheight (the generic point of its
preimage closure). -/
private lemma coheight_le_of_isPullback
    (h : IsPullback p s f (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))) [IsIntegral X]
    [IsIntegral W] [LocallyOfFiniteType s] [Surjective p] :
    (∀ w : W, Order.coheight (p w) ≤ Order.coheight w) ∧
      ∀ x : X, ∃ w, p w = x ∧ Order.coheight w ≤ Order.coheight x := by
  have hD : topologicalKrullDim W = topologicalKrullDim X := (invariants_of_isPullback f h).2.2
  have hn := MMP.Fourfold.topologicalKrullDim_eq_toNat_trdeg f
  have hX (x : X) := (MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight f x).trans hn
  have hW (w : W) := ((MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight s w).trans
    hD).trans hn
  have hcl (x : X) : topologicalKrullDim (p ⁻¹' closure {x}) =
      topologicalKrullDim (closure {x} : Set X) :=
    topologicalKrullDim_preimage_of_isPullback f h isClosed_closure.isLocallyClosed
  constructor
  · intro w
    have hsub : closure {w} ⊆ p ⁻¹' closure {p w} :=
      closure_minimal (Set.singleton_subset_iff.mpr (subset_closure rfl))
        (isClosed_closure.preimage p.continuous)
    have hle : topologicalKrullDim (closure {w} : Set W) ≤
        topologicalKrullDim (closure {p w} : Set X) := by
      rw [← hcl]; exact (Topology.IsEmbedding.inclusion hsub).isInducing.topologicalKrullDim_le
    exact le_of_add_eq_add_of_le (hW w) (hX (p w)) hle
  · intro x
    have hirr := isIrreducible_preimage_of_isPullback f h (isClosed_closure (s := {x}))
      isIrreducible_singleton.closure
    obtain ⟨w, hw⟩ := QuasiSober.sober hirr (isClosed_closure.preimage p.continuous)
    have hpw : p w = x := map_eq_of_closure_eq hw.def
    refine ⟨w, hpw, ?_⟩
    have heq : topologicalKrullDim (closure {w} : Set W) =
        topologicalKrullDim (closure {x} : Set X) := by
      rw [← hcl, ← hw.def]
    exact le_of_add_eq_add_of_le (hX x) (hW w) heq.ge

/-- Codimension bounds of a closed subset are insensitive to a base change of an algebraically
closed ground field of an integral scheme. -/
private lemma le_closedsCodimension_iff_of_isPullback
    (h : IsPullback p s f (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))) [IsIntegral X]
    [IsIntegral W] [LocallyOfFiniteType s] [Surjective p] (n : ℕ∞)
    (C : TopologicalSpace.Closeds X) (C' : TopologicalSpace.Closeds W)
    (hC : (C' : Set W) = p ⁻¹' C) :
    n ≤ MMP.Mori.closedsCodimension C' ↔ n ≤ MMP.Mori.closedsCodimension C := by
  obtain ⟨h1, h2⟩ := coheight_le_of_isPullback f h
  rw [MMP.Flips.le_closedsCodimension_iff_le_coheight,
    MMP.Flips.le_closedsCodimension_iff_le_coheight, hC]
  constructor
  · intro H x hx
    obtain ⟨w, rfl, hw⟩ := h2 x
    exact (H w hx).trans hw
  · intro H w hw
    exact (H (p w) hw).trans (h1 w)

/-- The generic point of the preimage of the closure of a point `x` lies over `x` and has the
coheight of `x`. -/
private lemma coheight_eq_of_isGenericPoint_preimage
    (h : IsPullback p s f (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))) [IsIntegral X]
    [IsIntegral W] [LocallyOfFiniteType s] [Surjective p] {x : X} {w : W}
    (hw : IsGenericPoint w (p ⁻¹' closure {x})) :
    p w = x ∧ Order.coheight w = Order.coheight x := by
  have hD : topologicalKrullDim W = topologicalKrullDim X := (invariants_of_isPullback f h).2.2
  have hn := MMP.Fourfold.topologicalKrullDim_eq_toNat_trdeg f
  have hX (x : X) := (MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight f x).trans hn
  have hW (w : W) := ((MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight s w).trans
    hD).trans hn
  have hcl : topologicalKrullDim (p ⁻¹' closure {x}) =
      topologicalKrullDim (closure {x} : Set X) :=
    topologicalKrullDim_preimage_of_isPullback f h isClosed_closure.isLocallyClosed
  have hpw : p w = x := map_eq_of_closure_eq hw.def
  refine ⟨hpw, le_antisymm ?_ ?_⟩
  · have heq : topologicalKrullDim (closure {w} : Set W) =
        topologicalKrullDim (closure {x} : Set X) := by
      rw [← hcl, ← hw.def]
    exact le_of_add_eq_add_of_le (hX x) (hW w) heq.ge
  · exact hpw ▸ (coheight_le_of_isPullback f h).1 w

/-- A closed subset of pure codimension one has a preimage of pure codimension one under a base
change of an algebraically closed ground field of an integral scheme: every irreducible component
of the preimage is the preimage of an irreducible component. -/
private lemma isPureCodimOne_of_isPullback
    (h : IsPullback p s f (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))) [IsIntegral X]
    [IsIntegral W] [LocallyOfFiniteType s] [Surjective p] [TopologicalSpace.NoetherianSpace X]
    {C : TopologicalSpace.Closeds X} (hC : MMP.Mori.IsPureCodimOne C)
    {C' : TopologicalSpace.Closeds W} (hC' : (C' : Set W) = p ⁻¹' C) :
    MMP.Mori.IsPureCodimOne C' := by
  intro Z hZ
  obtain ⟨w, hw⟩ := QuasiSober.sober Z.isIrreducible Z.isClosed
  have hwC : p w ∈ (C : Set X) := by
    have : w ∈ (C' : Set W) := hZ.1 hw.mem
    rwa [hC'] at this
  obtain ⟨V, hV, hpV⟩ := (MMP.Resolution.Aux.finite_and_cover_componentsOf C.isClosed).2 hwC
  obtain ⟨ξ, hVξ, hξ⟩ := exists_coheight_eq_one_of_mem_componentsOf C.isClosed hC hV
  have hVC : V ⊆ (C : Set X) := hV.1.2
  have hirr := isIrreducible_preimage_of_isPullback f h (isClosed_closure (s := {ξ}))
    isIrreducible_singleton.closure
  obtain ⟨w', hw'⟩ := QuasiSober.sober hirr (isClosed_closure.preimage p.continuous)
  obtain ⟨-, hcoh⟩ := coheight_eq_of_isGenericPoint_preimage f h hw'
  let T : TopologicalSpace.IrreducibleCloseds W :=
    ⟨p ⁻¹' closure {ξ}, hirr, isClosed_closure.preimage p.continuous⟩
  have hTC : (T : Set W) ⊆ C' := by
    rw [hC']
    exact Set.preimage_mono (hVξ ▸ hVC)
  have hZT : Z ≤ T := by
    change (Z : Set W) ⊆ p ⁻¹' closure {ξ}
    rw [← hw.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr (show p w ∈ closure {ξ} from hVξ ▸ hpV))
      (isClosed_closure.preimage p.continuous)
  have hTZ : T = Z := le_antisymm (hZ.2 hTC hZT) hZT
  rw [← hTZ]
  have hT : T = TopologicalSpace.IrreducibleCloseds.closureSingleton w' :=
    SetLike.coe_injective hw'.def.symm
  rw [hT, MMP.Flips.codimension_closureSingleton, hcoh, hξ]

/-- The base change of a normal variety along an extension of an algebraically closed ground
field is a normal variety. -/
public theorem isNormalVariety_of_isPullback
    (h : IsPullback p s f (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hv : MMP.Mori.IsNormalVariety k₀ f) : MMP.Mori.IsNormalVariety K s := by
  obtain ⟨hn, hi, -⟩ := invariants_of_isPullback f h
  have := hv.1.toIsIntegral
  exact ⟨{ toIsIntegral := hi.1 ‹_›
           toIsSeparated := MorphismProperty.of_isPullback (P := @IsSeparated) h
             hv.1.toIsSeparated
           toLocallyOfFiniteType :=
             MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h ‹_›
           toQuasiCompact := MorphismProperty.of_isPullback (P := @QuasiCompact) h
             hv.1.toQuasiCompact }, hn.1 hv.2⟩

end Square

section Helpers

variable {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K] [IsAlgClosed k₀] [IsAlgClosed K]

/-! ### Varieties and morphisms -/

/-- A morphism of finite type over `k₀` whose base change to `K` is H-projective is
H-projective. -/
private lemma isProjectiveMorphism_of_isPullback {X₀ X : Scheme.{u}}
    {s₀ : X₀ ⟶ Spec (.of k₀)} {s : X ⟶ Spec (.of K)} {π : X ⟶ X₀}
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    [LocallyOfFiniteType s₀] [QuasiCompact s₀] (hs : IsProjectiveMorphism s) :
    IsProjectiveMorphism s₀ := by
  set φ := Spec.map (CommRingCat.ofHom (algebraMap k₀ K))
  have hY : Stacks.HProjective.IsQuasiProjective (𝟙 (Spec (.of k₀))) :=
    (isQuasiProjective_iff_hProjectiveIsQuasiProjective _).mp
      (isProjectiveMorphism_id _).isQuasiProjective
  have : LocallyOfFiniteType (s₀ ≫ 𝟙 _) := by rw [Category.comp_id]; infer_instance
  have : QuasiCompact (s₀ ≫ 𝟙 _) := by rw [Category.comp_id]; infer_instance
  haveI := Stacks.Ample.isInvertibleModule_unit X₀
  have key := (MMP.isRelativelyAmple_iff_and_isProjectiveMorphism_iff_of_fieldExtension k₀ K
    (𝟙 _) s₀ hY (Stacks.Ample.unitModule X₀)).2
  refine key.2 ?_
  set q := pullback.fst (𝟙 (Spec (.of k₀))) φ
  have hsq1 : IsPullback (pullback.fst s₀ q) (pullback.snd s₀ q) s₀ q :=
    IsPullback.of_hasPullback s₀ q
  have hsq2 : IsPullback q (pullback.snd (𝟙 _) φ) (𝟙 _) φ := IsPullback.of_hasPullback _ _
  have hsq := hsq1.paste_vert hsq2
  rw [Category.comp_id] at hsq
  let e : X ≅ pullback s₀ q := h.isoIsPullback _ _ hsq
  refine IsProjectiveMorphism.of_iso e (asIso (pullback.snd (𝟙 (Spec (.of k₀))) φ)).symm ?_ hs
  rw [Iso.symm_hom, asIso_inv, IsIso.eq_comp_inv, Category.assoc]
  exact h.isoIsPullback_hom_snd _ _ hsq

/-- Projectivity of a variety is unchanged by base change along `Spec K ⟶ Spec k₀`. -/
public theorem isProjectiveVariety_iff_of_isPullback {X₀ X : Scheme.{u}}
    (s₀ : X₀ ⟶ Spec (.of k₀)) (s : X ⟶ Spec (.of K)) (π : X ⟶ X₀)
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))) :
    MMP.Mori.IsProjectiveVariety k₀ s₀ ↔ MMP.Mori.IsProjectiveVariety K s := by
  have hφ := specMap_mem_surjective_flat_quasiCompact (algebraMap k₀ K)
  simp only [MMP.Mori.isProjectiveVariety_iff, MMP.Mori.isVariety_iff]
  constructor
  · rintro ⟨⟨hi, hsep, hlft, hqc⟩, hp⟩
    have hint := (invariants_of_isPullback s₀ h).2.1
    have : IsProjectiveMorphism (h.isoPullback.hom ≫ pullback.snd s₀ _) :=
      IsProjectiveMorphism.iso_comp _ (hp.baseChange _)
    rw [h.isoPullback_hom_snd] at this
    exact ⟨⟨hint.1 hi, MorphismProperty.of_isPullback (P := @IsSeparated) h hsep,
      MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h hlft,
      MorphismProperty.of_isPullback (P := @QuasiCompact) h hqc⟩, this⟩
  · rintro ⟨⟨hi, hsep, hlft, hqc⟩, hp⟩
    have : LocallyOfFiniteType s₀ :=
      MorphismProperty.of_isPullback_of_descendsAlong (P := @LocallyOfFiniteType) h.flip hφ hlft
    have : QuasiCompact s₀ :=
      MorphismProperty.of_isPullback_of_descendsAlong (P := @QuasiCompact) h.flip hφ hqc
    have hp₀ := isProjectiveMorphism_of_isPullback h hp
    have := (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hp₀).2
    exact ⟨⟨(invariants_of_isPullback s₀ h).2.1.2 hi, inferInstance, inferInstance,
      inferInstance⟩, hp₀⟩

/-- Dimension is unchanged by base change along `Spec K ⟶ Spec k₀`. -/
public theorem topologicalKrullDim_eq_of_isPullback {X₀ X : Scheme.{u}}
    (s₀ : X₀ ⟶ Spec (.of k₀)) (s : X ⟶ Spec (.of K)) (π : X ⟶ X₀)
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) :
    topologicalKrullDim X = topologicalKrullDim X₀ := by
  have : LocallyOfFiniteType s₀ := hX₀.toLocallyOfFiniteType
  exact (invariants_of_isPullback s₀ h).2.2

/-! ### Prime divisors under base change -/

/-- The base change of a prime divisor: `π⁻¹(closure P₀)` is the closure of the generic point of a
prime divisor of `X`, lying over the generic point of `P₀`. -/
public theorem exists_primeDivisor_baseChange {X₀ X : Scheme.{u}} [IsIntegral X₀] [IsIntegral X]
    {s₀ : X₀ ⟶ Spec (.of k₀)} {s : X ⟶ Spec (.of K)} {π : X ⟶ X₀} [LocallyOfFiniteType s₀]
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (P₀ : MMP.Mori.PrimeDivisor X₀) :
    ∃ P : MMP.Mori.PrimeDivisor X, closure {P.genericPoint} = π.base ⁻¹' closure {P₀.genericPoint} ∧
      π P.genericPoint = P₀.genericPoint := by
  have : LocallyOfFiniteType s := MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h ‹_›
  have : Surjective π := surjective_of_isPullback h
  set x := P₀.genericPoint
  have hirr := isIrreducible_preimage_of_isPullback s₀ h (isClosed_closure (s := {x}))
    isIrreducible_singleton.closure
  obtain ⟨w, hw⟩ := QuasiSober.sober hirr (isClosed_closure.preimage π.continuous)
  obtain ⟨hpw, hcw⟩ := coheight_eq_of_isGenericPoint_preimage s₀ h hw
  have hcoh : Order.coheight w = 1 :=
    hcw.trans (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P₀)
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne w hcoh, ?_, ?_⟩
  · change closure {(AlgebraicGeometry.PrimeDivisor.ofCoheightOne w hcoh).genericPoint} = _
    rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
    exact hw.def
  · change π (AlgebraicGeometry.PrimeDivisor.ofCoheightOne w hcoh).genericPoint = _
    rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
    exact hpw

/-- Every proper curve on `X` is numerically equivalent to the base change of a proper curve on
`X₀`. -/
private theorem exists_properCurve_numericalClass_eq {X₀ X : Scheme.{u}}
    {s₀ : X₀ ⟶ Spec (.of k₀)} {s : X ⟶ Spec (.of K)} {π : X ⟶ X₀}
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) (C : ProperCurve s) :
    ∃ (C₀ : ProperCurve s₀) (C₀K : ProperCurve s),
      closure {C₀K.point} = π.base ⁻¹' closure {C₀.point} ∧
      OneCycle.numericalClass s (C₀K.cycle ℝ) = OneCycle.numericalClass s (C.cycle ℝ) ∧
      ∀ (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L],
        C₀K.degree K L = C.degree K L := by
  obtain ⟨C₀, C₀K, hcl, hdeg⟩ := exists_properCurve_degree_eq_of_isPullback s₀ s π h hX₀ C
  refine ⟨C₀, C₀K, hcl, ?_, hdeg⟩
  rw [OneCycle.numericalClass_eq_iff]
  intro L _
  rw [OneCycle.degree_cycle, OneCycle.degree_cycle, hdeg L]

/-! ### Birational transforms of prime divisors under base change -/

section Transforms

open TopologicalSpace

/-- **Prime divisors over a point of codimension one are base changes.** A prime divisor of the
base change `X` whose generic point does not lie over the generic point of `X₀` is the base
change of a prime divisor of `X₀`. -/
private theorem exists_closure_eq_of_map_ne_genericPoint {X₀ X : Scheme.{u}} [IsIntegral X₀]
    [IsIntegral X] {s₀ : X₀ ⟶ Spec (.of k₀)} {s : X ⟶ Spec (.of K)} {π : X ⟶ X₀}
    [LocallyOfFiniteType s₀]
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (P : MMP.Mori.PrimeDivisor X) (hP : π P.genericPoint ≠ genericPoint X₀) :
    ∃ P₀ : MMP.Mori.PrimeDivisor X₀,
      closure {P.genericPoint} = π.base ⁻¹' closure {P₀.genericPoint} := by
  have : LocallyOfFiniteType s := MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h ‹_›
  have : Surjective π := surjective_of_isPullback h
  obtain ⟨h1, -⟩ := coheight_le_of_isPullback s₀ h
  have hP1 : Order.coheight P.genericPoint = 1 :=
    AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P
  have hx : Order.coheight (π P.genericPoint) = 1 := by
    refine le_antisymm (hP1 ▸ h1 _) ?_
    have hgen : genericPoint X₀ ⤳ π P.genericPoint := (genericPoint_spec X₀).specializes trivial
    have hle : π P.genericPoint ≤ genericPoint X₀ := hgen
    have hlt : π P.genericPoint < genericPoint X₀ :=
      lt_of_le_not_ge hle fun h' => hP (hgen.antisymm h').eq.symm
    exact le_add_self.trans (Order.coheight_add_one_le hlt)
  obtain ⟨P', hP'c, hP'π⟩ := exists_primeDivisor_baseChange h
    (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hx)
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hx, ?_⟩
  have hgp : (AlgebraicGeometry.PrimeDivisor.ofCoheightOne (π P.genericPoint) hx).genericPoint =
      π P.genericPoint := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  have hsp : P'.genericPoint ⤳ P.genericPoint := by
    rw [specializes_iff_mem_closure, hP'c, Set.mem_preimage]
    change π P.genericPoint ∈ closure {(AlgebraicGeometry.PrimeDivisor.ofCoheightOne
      (π P.genericPoint) hx).genericPoint}
    rw [hgp]; exact subset_closure rfl
  have heq := eq_of_specializes_of_coheight_eq_one hsp
    (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P') hP1
  rw [← hP'c, heq]

end Transforms

section Decomposition

variable {X₀ X : Scheme.{u}} [IsIntegral X₀] [IsIntegral X] [IsNormal X₀] [IsNormal X]
  [IsLocallyNoetherian X₀] [IsLocallyNoetherian X]
  {s₀ : X₀ ⟶ Spec (.of k₀)} {s : X ⟶ Spec (.of K)} {π : X ⟶ X₀}

/-- **Orders of the coefficients of a base-changed section.** If a regular function `u` on
`π⁻¹U₀` has order at least `n(E₀)` along the base change of every prime divisor `E₀` meeting
`U₀`, then so do the coefficients of `u` along a `k₀`-basis of `K`. -/
private theorem exists_sum_basis_ordGE [LocallyOfFiniteType s₀] [Surjective π] [IsDominant π]
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))) {U₀ : X₀.Opens}
    (hU₀ : IsAffineOpen U₀) (u : Γ(X, π ⁻¹ᵁ U₀)) (n : MMP.Mori.PrimeDivisor X₀ → ℤ)
    (hu : ∀ (E₀ : MMP.Mori.PrimeDivisor X₀) (E : MMP.Mori.PrimeDivisor X)
      (hE : closure {E.genericPoint} = π.base ⁻¹' closure {E₀.genericPoint})
      (hEU : E.genericPoint ∈ π ⁻¹ᵁ U₀), E.OrdGE (n E₀)
        ((X.presheaf.germ (π ⁻¹ᵁ U₀) (componentGenericPoint X E.component)
          (E.specializes_genericPoint.mem_open (π ⁻¹ᵁ U₀).isOpen hEU)).hom u)) :
    ∃ (t : Finset (Module.Basis.ofVectorSpaceIndex k₀ K))
      (a : Module.Basis.ofVectorSpaceIndex k₀ K → Γ(X₀, U₀)),
      u = ∑ β ∈ t, (π.app U₀).hom (a β) *
        (s.appLE ⊤ (π ⁻¹ᵁ U₀) (by simp)).hom ((Scheme.ΓSpecIso (.of K)).inv.hom
          (Module.Basis.ofVectorSpace k₀ K β)) ∧
      ∀ β ∈ t, ∀ (E₀ : MMP.Mori.PrimeDivisor X₀) (hE₀ : E₀.genericPoint ∈ U₀),
        E₀.OrdGE (n E₀) ((X₀.presheaf.germ U₀ (componentGenericPoint X₀ E₀.component)
          (E₀.specializes_genericPoint.mem_open U₀.isOpen hE₀)).hom (a β)) := by
  obtain ⟨t, a, hua⟩ := exists_sum_basis_of_isPullback h hU₀ u
  refine ⟨t, a, hua, fun β hβ E₀ hE₀ => ?_⟩
  obtain ⟨E, hE, hπE⟩ := exists_primeDivisor_baseChange h E₀
  have hEU : E.genericPoint ∈ π ⁻¹ᵁ U₀ := by
    show π E.genericPoint ∈ U₀; rw [hπE]; exact hE₀
  have h1 := hu E₀ E hE hEU
  rw [hua, map_sum] at h1
  let b := Module.Basis.ofVectorSpace k₀ K
  refine ordGE_of_ordGE_sum h hE (ι := t)
    (fun j => (X₀.presheaf.germ U₀ (componentGenericPoint X₀ E₀.component)
      (E₀.specializes_genericPoint.mem_open U₀.isOpen hE₀)).hom (a j))
    (fun j => b j) (b.linearIndependent.comp _ Subtype.val_injective) (n E₀) ?_ ⟨β, hβ⟩
  convert h1 using 1
  rw [← Finset.sum_coe_sort t]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, germ_appLE_top, MMP.Fourfold.fieldMap_germ]

end Decomposition

section CartierDescent

attribute [local instance] MMP.Resolution.componentField

variable {X₀ X : Scheme.{u}} [IsIntegral X₀] [IsIntegral X] [IsNormal X₀] [IsNormal X]
  [IsLocallyNoetherian X₀] [IsLocallyNoetherian X] [CompactSpace X₀] [CompactSpace X]
  {s₀ : X₀ ⟶ Spec (.of k₀)} {s : X ⟶ Spec (.of K)} {π : X ⟶ X₀}

/-- **Cartier descent.** A divisor whose base change is Cartier is Cartier. -/
private theorem isCartier_of_isBaseChange [LocallyOfFiniteType s₀] [Surjective π] [IsDominant π]
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    {D₀ : Divisor X₀} {D : Divisor X} (hD : IsBaseChange π D₀ D) (hDc : D.IsCartier) :
    D₀.IsCartier := by
  classical
  intro x₀
  obtain ⟨y, rfl⟩ := π.surjective x₀
  obtain ⟨V, hyV, φ, hφ⟩ := hDc y
  obtain ⟨U₀, hU₀, hyU₀, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X₀.isBasis_affineOpens
    (U := ⊤) (x := π y) trivial
  haveI : Nonempty U₀ := ⟨⟨π y, hyU₀⟩⟩
  haveI : IsAffineHom π := MorphismProperty.of_isPullback (P := @IsAffineHom) h.flip inferInstance
  have hU : IsAffineOpen (π ⁻¹ᵁ U₀) := IsAffineOpen.preimage hU₀ π
  have hyU : y ∈ π ⁻¹ᵁ U₀ := hyU₀
  haveI : Nonempty (π ⁻¹ᵁ U₀) := ⟨⟨y, hyU⟩⟩
  obtain ⟨s', hsV, hys⟩ := hU.exists_basicOpen_le (V := V) ⟨y, hyV⟩ hyU
  obtain ⟨N, hN⟩ := exists_pow_ordGE hφ s' hsV
  obtain ⟨c₀, hc₀g, hc₀⟩ := exists_section_ordGE_natAbs hU₀ D₀
  -- the factor `s^N φ^ε` has order at least `ε D`
  have hpart (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (E : MMP.Mori.PrimeDivisor X)
      (hEU : E.genericPoint ∈ π ⁻¹ᵁ U₀) :
      E.OrdGE (ε * D.coeff E) (((X.presheaf.germ _ _
        (E.specializes_genericPoint.mem_open (π ⁻¹ᵁ U₀).isOpen hEU)).hom s') ^ N *
          ((φ ^ ε : (RationalFunctions X)ˣ) : RationalFunctions X) E.component) := by
    rcases hε with rfl | rfl
    · simpa using (hN E hEU).2
    · simpa using (hN E hEU).1
  -- the regular functions `u = π^*c₀ · s^N φ⁻¹` and `u' = π^*c₀ · s^N φ` on `π⁻¹U₀`
  have hsec (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
      (0 : Divisor X).IsDivisorialSection (π ⁻¹ᵁ U₀) (fun Z =>
        (X.presheaf.germ _ _ Z.2).hom ((π.app U₀).hom c₀) *
          (((X.presheaf.germ _ _ Z.2).hom s') ^ N *
            ((φ ^ ε : (RationalFunctions X)ˣ) : RationalFunctions X) Z.1)) := by
    intro E hE
    have hEU := E.genericPoint_mem_of_nonempty hE
    have h2 := hpart ε hε E hEU
    rw [DivisorWithCoeffs.coeff_zero, neg_zero]
    by_cases hb : ∃ E₀ : MMP.Mori.PrimeDivisor X₀,
        closure {E.genericPoint} = π.base ⁻¹' closure {E₀.genericPoint}
    · obtain ⟨E₀, hE₀⟩ := hb
      have hπE := map_eq_of_closure_eq hE₀
      have hE₀U : E₀.genericPoint ∈ U₀ := hπE ▸ hEU
      have h1 := ordGE_fieldMap h hE₀ (hc₀ E₀ hE₀U)
      rw [MMP.Fourfold.fieldMap_germ] at h1
      refine (h1.mul h2).mono ?_
      rw [show D.coeff E = D₀.coeff E₀ from hD.1 E₀ E hE₀]
      have := le_abs_self (D₀.coeff E₀)
      have := neg_abs_le (D₀.coeff E₀)
      rcases hε with rfl | rfl <;> simp only [Int.natCast_natAbs] <;> linarith
    · have hDE : D.coeff E = 0 := by
        by_contra hne; exact hb (hD.2 E hne)
      rw [hDE, mul_zero] at h2
      simpa using (ordGE_zero_germ ((π.app U₀).hom c₀) E hEU).mul h2
  obtain ⟨u, hu⟩ := (hsec (-1) (Or.inr rfl)).exists_eq
  obtain ⟨u', hu'⟩ := (hsec 1 (Or.inl rfl)).exists_eq
  -- the order of `c₀`
  obtain ⟨ordc, hordc⟩ := exists_valuation_germ_eq_exp hc₀g
  -- the coefficients of `u` and `u'`
  have hbound (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (w : Γ(X, π ⁻¹ᵁ U₀))
      (hw : (toRationalFunctionsPresheaf X).app (Opposite.op (π ⁻¹ᵁ U₀)) w = (fun Z =>
        (X.presheaf.germ _ _ Z.2).hom ((π.app U₀).hom c₀) *
          (((X.presheaf.germ _ _ Z.2).hom s') ^ N *
            ((φ ^ ε : (RationalFunctions X)ˣ) : RationalFunctions X) Z.1)))
      (E₀ : MMP.Mori.PrimeDivisor X₀) (E : MMP.Mori.PrimeDivisor X)
      (hE : closure {E.genericPoint} = π.base ⁻¹' closure {E₀.genericPoint})
      (hEU : E.genericPoint ∈ π ⁻¹ᵁ U₀) :
      E.OrdGE (ordc E₀ + ε * D₀.coeff E₀)
        ((X.presheaf.germ (π ⁻¹ᵁ U₀) (componentGenericPoint X E.component)
          (E.specializes_genericPoint.mem_open (π ⁻¹ᵁ U₀).isOpen hEU)).hom w) := by
    have hπE := map_eq_of_closure_eq hE
    have hE₀U : E₀.genericPoint ∈ U₀ := hπE ▸ hEU
    have e1 := congrFun hw ⟨E.component, E.specializes_genericPoint.mem_open
      (π ⁻¹ᵁ U₀).isOpen hEU⟩
    rw [toRationalFunctionsPresheaf_app_apply] at e1
    rw [e1]
    have hv : E.valuation ((X.presheaf.germ (π ⁻¹ᵁ U₀) (componentGenericPoint X E.component)
        (E.specializes_genericPoint.mem_open (π ⁻¹ᵁ U₀).isOpen hEU)).hom ((π.app U₀).hom c₀)) =
        WithZero.exp (ordc E₀) := by
      rw [← MMP.Fourfold.fieldMap_germ π E₀.component E.component
        (E₀.specializes_genericPoint.mem_open U₀.isOpen hE₀U),
        valuation_fieldMap_of_closure_eq h hE, hordc E₀ hE₀U]
    have h2 := hpart ε hε E hEU
    rw [show D.coeff E = D₀.coeff E₀ from hD.1 E₀ E hE] at h2
    exact ordGE_mul_of_valuation_eq h2 hv
  obtain ⟨t, a, hua, ha⟩ := exists_sum_basis_ordGE h hU₀ u (fun E₀ => ordc E₀ + -1 * D₀.coeff E₀)
    (hbound (-1) (Or.inr rfl) u hu)
  obtain ⟨t', a', hua', ha'⟩ :=
    exists_sum_basis_ordGE h hU₀ u' (fun E₀ => ordc E₀ + 1 * D₀.coeff E₀)
    (hbound 1 (Or.inl rfl) u' hu')
  -- the products `a_β a'_γ / c₀²` are regular on `U₀`
  have hprod (β γ) (hβ : β ∈ t) (hγ : γ ∈ t') :
      (0 : Divisor X₀).IsDivisorialSection U₀ (fun Z =>
        (X₀.presheaf.germ _ _ Z.2).hom (a β) * (X₀.presheaf.germ _ _ Z.2).hom (a' γ) /
          (X₀.presheaf.germ _ _ Z.2).hom c₀ ^ 2) := by
    intro E₀ hE₀
    have hE₀U := E₀.genericPoint_mem_of_nonempty hE₀
    have h1 := (ha β hβ E₀ hE₀U).mul (ha' γ hγ E₀ hE₀U)
    have hv2 : E₀.valuation ((X₀.presheaf.germ U₀ (componentGenericPoint X₀ E₀.component)
        (E₀.specializes_genericPoint.mem_open U₀.isOpen hE₀U)).hom c₀ ^ 2) =
        WithZero.exp (2 * ordc E₀) := by
      rw [map_pow, hordc E₀ hE₀U, ← WithZero.exp_nsmul]; simp
    have h3 := ordGE_div_of_valuation_eq h1 hv2
    rw [DivisorWithCoeffs.coeff_zero, neg_zero]
    refine h3.mono (le_of_eq ?_)
    ring
  choose r hr using fun β γ (hβ : β ∈ t) (hγ : γ ∈ t') => (hprod β γ hβ hγ).exists_eq
  -- the generic point of `X₀` lies in `U₀`
  have hgU₀ : genericPoint X₀ ∈ U₀ := (genericPoint_spec X₀).specializes trivial
    |>.mem_open U₀.isOpen hyU₀
  have hZU₀ (Z : irreducibleComponents X₀) : componentGenericPoint X₀ Z ∈ U₀ := by
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint]; exact hgU₀
  have hc₀Z (Z : irreducibleComponents X₀) :
      (X₀.presheaf.germ U₀ (componentGenericPoint X₀ Z) (hZU₀ Z)).hom c₀ ≠ 0 :=
    (isUnit_germ_componentGenericPoint hc₀g Z (hZU₀ Z)).ne_zero
  -- `c₀² r_{βγ} = a_β a'_γ`
  have hr_eq (β γ) (hβ : β ∈ t) (hγ : γ ∈ t') : c₀ ^ 2 * r β γ hβ hγ = a β * a' γ := by
    apply toRationalFunctionsPresheaf_app_injective U₀
    funext Z
    have e := congrFun (hr β γ hβ hγ) Z
    rw [toRationalFunctionsPresheaf_app_apply] at e
    rw [toRationalFunctionsPresheaf_app_apply, toRationalFunctionsPresheaf_app_apply, map_mul,
      map_pow, e, map_mul, mul_div_cancel₀ _ (pow_ne_zero 2 (hc₀Z Z.1))]
  -- the constants
  set κ : Module.Basis.ofVectorSpaceIndex k₀ K → Γ(X, π ⁻¹ᵁ U₀) := fun β =>
    (s.appLE ⊤ (π ⁻¹ᵁ U₀) (by simp)).hom ((Scheme.ΓSpecIso (.of K)).inv.hom
      (Module.Basis.ofVectorSpace k₀ K β)) with hκ
  let r' : Module.Basis.ofVectorSpaceIndex k₀ K → Module.Basis.ofVectorSpaceIndex k₀ K →
      Γ(X₀, U₀) := fun β γ => if hh : β ∈ t ∧ γ ∈ t' then r β γ hh.1 hh.2 else 0
  -- `u u' = (π^*c₀)² s^{2N}`
  have huu : u * u' = ((π.app U₀).hom c₀) ^ 2 * s' ^ (2 * N) := by
    apply toRationalFunctionsPresheaf_app_injective (π ⁻¹ᵁ U₀)
    funext Z
    have e := congrFun hu Z
    have e' := congrFun hu' Z
    rw [toRationalFunctionsPresheaf_app_apply] at e e'
    rw [toRationalFunctionsPresheaf_app_apply, toRationalFunctionsPresheaf_app_apply, map_mul, e,
      e', map_mul, map_pow, map_pow]
    have h1 : ((φ ^ (-1 : ℤ) : (RationalFunctions X)ˣ) : RationalFunctions X) Z.1 *
        ((φ ^ (1 : ℤ) : (RationalFunctions X)ˣ) : RationalFunctions X) Z.1 = 1 := by
      rw [← Pi.mul_apply, ← Units.val_mul, ← zpow_add]; simp
    linear_combination ((X.presheaf.germ _ _ Z.2).hom ((π.app U₀).hom c₀) ^ 2 *
      (X.presheaf.germ _ _ Z.2).hom s' ^ (2 * N)) * h1
  -- `u u' = (π^*c₀)² ∑ π^*r_{βγ} b_β b_γ`
  have huu' : u * u' = ((π.app U₀).hom c₀) ^ 2 *
      ∑ β ∈ t, ∑ γ ∈ t', (π.app U₀).hom (r' β γ) * (κ β * κ γ) := by
    rw [hua, hua', Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β hβ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun γ hγ => ?_
    have e : a β * a' γ = c₀ ^ 2 * r' β γ := by
      simp only [r', dif_pos (And.intro hβ hγ)]; exact (hr_eq β γ hβ hγ).symm
    calc (π.app U₀).hom (a β) * κ β * ((π.app U₀).hom (a' γ) * κ γ)
        = (π.app U₀).hom (a β * a' γ) * (κ β * κ γ) := by rw [map_mul]; ring
      _ = ((π.app U₀).hom c₀) ^ 2 * ((π.app U₀).hom (r' β γ) * (κ β * κ γ)) := by
        rw [e, map_mul, map_pow]; ring
  -- `π^*c₀ ≠ 0`
  obtain ⟨Z, hyZ⟩ := exists_mem_irreducibleComponents y
  have hZ : componentGenericPoint X Z ∈ π ⁻¹ᵁ U₀ := (genericPoint_mem_iff Z _).mpr ⟨y, hyU, hyZ⟩
  obtain ⟨Z₀, -⟩ := exists_mem_irreducibleComponents (π y)
  have hπc : (π.app U₀).hom c₀ ≠ 0 := by
    intro h0
    have e := congrArg (X.presheaf.germ _ _ hZ).hom h0
    rw [map_zero, ← MMP.Fourfold.fieldMap_germ π Z₀ Z (hZU₀ Z₀)] at e
    exact ((isUnit_germ_componentGenericPoint hc₀g Z₀ (hZU₀ Z₀)).map
      (MMP.Fourfold.fieldMap π Z₀ Z)).ne_zero e
  haveI : IsDomain Γ(X, π ⁻¹ᵁ U₀) := IsIntegral.component_integral _
  have hS : s' ^ (2 * N) = ∑ β ∈ t, ∑ γ ∈ t', (π.app U₀).hom (r' β γ) * (κ β * κ γ) :=
    mul_left_cancel₀ (pow_ne_zero 2 hπc) (huu.symm.trans huu')
  -- some `r_{βγ}` is invertible at `π y`
  have hex : ∃ β ∈ t, ∃ γ ∈ t', π y ∈ X₀.basicOpen (r' β γ) := by
    by_contra hne
    push Not at hne
    have hunit : IsUnit ((X.presheaf.germ _ y hyU).hom (s' ^ (2 * N))) := by
      rw [map_pow]; exact ((Scheme.mem_basicOpen X s' y hyU).mp hys).pow _
    have hmem : (X.presheaf.germ _ y hyU).hom (∑ β ∈ t, ∑ γ ∈ t',
        (π.app U₀).hom (r' β γ) * (κ β * κ γ)) ∈ IsLocalRing.maximalIdeal _ := by
      rw [map_sum]
      refine Ideal.sum_mem _ fun β hβ => ?_
      rw [map_sum]
      refine Ideal.sum_mem _ fun γ hγ => ?_
      rw [map_mul]
      refine Ideal.mul_mem_right _ _ ?_
      have e : (X.presheaf.germ (π ⁻¹ᵁ U₀) y hyU).hom ((π.app U₀).hom (r' β γ)) =
          (π.stalkMap y).hom ((X₀.presheaf.germ U₀ (π y) hyU₀).hom (r' β γ)) :=
        (Scheme.Hom.germ_stalkMap_apply π U₀ y hyU₀ _).symm
      rw [e]
      have hnu : (X₀.presheaf.germ U₀ (π y) hyU₀).hom (r' β γ) ∈
          IsLocalRing.maximalIdeal _ := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        exact hne β hβ γ hγ ((Scheme.mem_basicOpen _ _ _ hyU₀).mpr hu)
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hnu ⊢
      exact fun hu => hnu (isUnit_of_map_unit _ _ hu)
    rw [hS] at hunit
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem hunit
  obtain ⟨β, hβ, γ, hγ, hW⟩ := hex
  have hρeq : c₀ ^ 2 * r' β γ = a β * a' γ := by
    simp only [r', dif_pos (And.intro hβ hγ)]; exact hr_eq β γ hβ hγ
  have hρZ (Z : irreducibleComponents X₀) :
      IsUnit ((X₀.presheaf.germ U₀ (componentGenericPoint X₀ Z) (hZU₀ Z)).hom (r' β γ)) := by
    have hm : componentGenericPoint X₀ Z ∈ X₀.basicOpen (r' β γ) := by
      rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint]
      exact (genericPoint_spec X₀).specializes trivial |>.mem_open (X₀.basicOpen _).isOpen hW
    exact (Scheme.mem_basicOpen _ _ _ _).mp hm
  have haZ (Z : irreducibleComponents X₀) :
      (X₀.presheaf.germ U₀ (componentGenericPoint X₀ Z) (hZU₀ Z)).hom (a β) ≠ 0 ∧
      (X₀.presheaf.germ U₀ (componentGenericPoint X₀ Z) (hZU₀ Z)).hom (a' γ) ≠ 0 := by
    have e := congrArg (X₀.presheaf.germ U₀ (componentGenericPoint X₀ Z) (hZU₀ Z)).hom hρeq
    rw [map_mul, map_pow, map_mul] at e
    have hne : (X₀.presheaf.germ U₀ (componentGenericPoint X₀ Z) (hZU₀ Z)).hom c₀ ^ 2 *
        (X₀.presheaf.germ U₀ (componentGenericPoint X₀ Z) (hZU₀ Z)).hom (r' β γ) ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 (hc₀Z Z)) (hρZ Z).ne_zero
    rw [e] at hne
    exact ⟨left_ne_zero_of_mul hne, right_ne_zero_of_mul hne⟩
  -- the local equation
  let ψ : (RationalFunctions X₀)ˣ := (RationalFunctions.unitsEquiv X₀).symm fun Z =>
    Units.mk0 ((X₀.presheaf.germ U₀ (componentGenericPoint X₀ Z) (hZU₀ Z)).hom c₀ /
      (X₀.presheaf.germ U₀ (componentGenericPoint X₀ Z) (hZU₀ Z)).hom (a β))
      (div_ne_zero (hc₀Z Z) (haZ Z).1)
  have hψ (Z : irreducibleComponents X₀) : (ψ : RationalFunctions X₀) Z =
      (X₀.presheaf.germ U₀ (componentGenericPoint X₀ Z) (hZU₀ Z)).hom c₀ /
        (X₀.presheaf.germ U₀ (componentGenericPoint X₀ Z) (hZU₀ Z)).hom (a β) := rfl
  refine ⟨X₀.basicOpen (r' β γ), hW, ψ, fun E₀ hE₀ => ?_⟩
  have hηW := E₀.genericPoint_mem_of_nonempty hE₀
  have hηU : E₀.genericPoint ∈ U₀ := X₀.basicOpen_le _ hηW
  have hvρ := valuation_germ_eq_one (r' β γ) E₀ hηU hηW
  have e := congrArg (fun w => E₀.valuation
    ((X₀.presheaf.germ U₀ (componentGenericPoint X₀ E₀.component) (hZU₀ E₀.component)).hom w)) hρeq
  simp only [map_mul, map_pow] at e
  rw [hvρ, mul_one, hordc E₀ hηU] at e
  have hva := (ha β hβ E₀ hηU).resolve_left (haZ E₀.component).1
  have hva' := (ha' γ hγ E₀ hηU).resolve_left (haZ E₀.component).2
  set va := E₀.valuation ((X₀.presheaf.germ U₀ (componentGenericPoint X₀ E₀.component)
    (hZU₀ E₀.component)).hom (a β)) with hva_def
  set va' := E₀.valuation ((X₀.presheaf.germ U₀ (componentGenericPoint X₀ E₀.component)
    (hZU₀ E₀.component)).hom (a' γ)) with hva'_def
  have hva0 : va ≠ 0 := (map_ne_zero _).mpr (haZ E₀.component).1
  have hva'0 : va' ≠ 0 := (map_ne_zero _).mpr (haZ E₀.component).2
  rw [← WithZero.exp_log hva0] at hva e
  rw [← WithZero.exp_log hva'0] at hva' e
  rw [WithZero.exp_le_exp] at hva hva'
  rw [← WithZero.exp_nsmul, ← WithZero.exp_add, WithZero.exp_inj] at e
  have hp : WithZero.log va = ordc E₀ - D₀.coeff E₀ := by
    simp only [Int.nsmul_eq_mul, Nat.cast_ofNat] at e
    omega
  have hv := E₀.valuation_component ψ
  rw [hψ, map_div₀, hordc E₀ hηU, ← hva_def, ← WithZero.exp_log hva0, hp, ← WithZero.exp_sub,
    WithZero.exp_inj] at hv
  rw [← hv]
  ring

end CartierDescent

section TopForms

variable {X₀ X : Scheme.{u}} [IsIntegral X₀] [IsIntegral X] [IsNormal X₀] [IsNormal X]
  [IsLocallyNoetherian X₀] [IsLocallyNoetherian X] [CompactSpace X₀] [CompactSpace X]
  {s₀ : X₀ ⟶ Spec (.of k₀)} {s : X ⟶ Spec (.of K)} {π : X ⟶ X₀}

/-- An étale chart of a smooth open of a variety of dimension `n` has `n` coordinates. -/
private theorem exists_etale_chart_of_topologicalKrullDim_eq [LocallyOfFiniteType s₀] {n : ℕ}
    (hn : topologicalKrullDim X₀ = n) (U : X₀.Opens) [Smooth (U.ι ≫ s₀)] (x : X₀)
    (hx : x ∈ U) :
    ∃ (V : X₀.Opens) (_ : IsAffineOpen V) (_ : x ∈ V)
      (g : MvPolynomial (Fin n) Γ(Spec (.of k₀), ⊤) →+* Γ(X₀, V)),
      g.Etale ∧ g.comp MvPolynomial.C = (s₀.appLE ⊤ V le_top).hom := by
  have h₀sq : IsPullback (𝟙 X₀) s₀ s₀ (𝟙 (Spec (.of k₀))) := IsPullback.of_id_fst
  obtain ⟨V, -, hV, hxV, m, g, hg, hgC⟩ := MMP.Spreading.exists_etale_chart_of_smooth_on s₀ U x hx
  have hgV : genericPoint X₀ ∈ V :=
    (genericPoint_spec X₀).specializes trivial |>.mem_open V.isOpen hxV
  have hmn : m = n := chart_dim_eq_of_isPullback h₀sq hn V hV g hg hgC hgV
  subst m
  exact ⟨V, hV, hxV, g, hg, hgC⟩

/-- If a nonzero rational top form `dz` is `h₀ · dg(X)` on a basic open `D(f)` through the generic
point, then `h₀` is nonzero at the generic point. -/
private theorem germ_ne_zero_of_wedge_eq_smul [LocallyOfFiniteType s₀] {n : ℕ} {V₁ : X₀.Opens}
    [Nonempty ((𝟙 X₀) ⁻¹ᵁ V₁)] (z : Fin n → Γ(X₀, V₁)) (ω₀ : MMP.Mori.RationalTopForms s₀ n)
    (hω₀def : letI := MMP.Mori.functionFieldAlgebra s₀
      ω₀ = (exteriorPower.ιMulti X₀.functionField n fun i =>
        KaehlerDifferential.D k₀ X₀.functionField
          (X₀.germToFunctionField ((𝟙 X₀) ⁻¹ᵁ V₁) (Scheme.Hom.app (𝟙 X₀) V₁ (z i)))))
    (hω₀ : ω₀ ≠ 0) {V : X₀.Opens} (g : MvPolynomial (Fin n) Γ(Spec (.of k₀), ⊤) →+* Γ(X₀, V))
    (f : Γ(X₀, V)) (hf : X₀.basicOpen f ≤ V₁) (hgf : genericPoint X₀ ∈ X₀.basicOpen f)
    (h₀ : Γ(X₀, X₀.basicOpen f))
    (hrel : letI := (s₀.appLE ⊤ (X₀.basicOpen f) le_top).hom.toAlgebra
      exteriorPower.ιMulti Γ(X₀, X₀.basicOpen f) n
          (fun i => KaehlerDifferential.D Γ(Spec (.of k₀), ⊤) Γ(X₀, X₀.basicOpen f)
            (X₀.presheaf.map (homOfLE hf).op (z i))) =
        h₀ • exteriorPower.ιMulti Γ(X₀, X₀.basicOpen f) n (fun i =>
          KaehlerDifferential.D Γ(Spec (.of k₀), ⊤) Γ(X₀, X₀.basicOpen f)
            (X₀.presheaf.map (homOfLE (X₀.basicOpen_le f)).op (g (MvPolynomial.X i))))) :
    (X₀.presheaf.germ (X₀.basicOpen f) (genericPoint X₀) hgf).hom h₀ ≠ 0 := by
  classical
  letI := MMP.Mori.functionFieldAlgebra s₀
  have h₀sq : IsPullback (𝟙 X₀) s₀ s₀ (𝟙 (Spec (.of k₀))) := IsPullback.of_id_fst
  intro h0
  apply hω₀
  haveI : Nonempty (X₀.basicOpen f) := ⟨⟨_, hgf⟩⟩
  haveI : Nonempty ((𝟙 X₀) ⁻¹ᵁ X₀.basicOpen f) := ⟨⟨_, hgf⟩⟩
  have e := form_eq_smul_of_isPullback h₀sq g (X₀.basicOpen f) (X₀.basicOpen_le f)
    (fun i => X₀.presheaf.map (homOfLE hf).op (z i)) h₀ hrel
  have e2 : (fun i => KaehlerDifferential.D k₀ X₀.functionField
        (X₀.germToFunctionField ((𝟙 X₀) ⁻¹ᵁ X₀.basicOpen f)
          (Scheme.Hom.app (𝟙 X₀) _ (X₀.presheaf.map (homOfLE hf).op (z i))))) =
      fun i => KaehlerDifferential.D k₀ X₀.functionField
        (X₀.germToFunctionField ((𝟙 X₀) ⁻¹ᵁ V₁) (Scheme.Hom.app (𝟙 X₀) V₁ (z i))) := by
    funext i
    rw [germToFunctionField_app_map (𝟙 X₀) hf (z i)]
  rw [e2, germToFunctionField_id_app, h0, zero_smul] at e
  rw [hω₀def]
  exact e

/-- **Charts adapted to a top form.** Let `dz` be a nonzero rational top form given by sections
`z` over an open `V₁` through the generic point of `X₀`. Around every point `x` of a smooth open
`U` there is an étale chart `g` on an affine open `V`, and a basic open `D(f) ⊆ V₁` of `V` through
the generic point on which `dz = h₀ · dg(X)` with `h₀` nonzero at the generic point. -/
private theorem exists_chart_wedge_eq_smul [LocallyOfFiniteType s₀] {n : ℕ}
    (hn : topologicalKrullDim X₀ = n) {V₁ : X₀.Opens} (hgV₁ : genericPoint X₀ ∈ V₁)
    [Nonempty ((𝟙 X₀) ⁻¹ᵁ V₁)] (z : Fin n → Γ(X₀, V₁)) (ω₀ : MMP.Mori.RationalTopForms s₀ n)
    (hω₀def : letI := MMP.Mori.functionFieldAlgebra s₀
      ω₀ = (exteriorPower.ιMulti X₀.functionField n fun i =>
        KaehlerDifferential.D k₀ X₀.functionField
          (X₀.germToFunctionField ((𝟙 X₀) ⁻¹ᵁ V₁) (Scheme.Hom.app (𝟙 X₀) V₁ (z i)))))
    (hω₀ : ω₀ ≠ 0) (U : X₀.Opens) [Smooth (U.ι ≫ s₀)] (x : X₀) (hx : x ∈ U) :
    ∃ (V : X₀.Opens) (hV : IsAffineOpen V) (_ : x ∈ V)
      (g : MvPolynomial (Fin n) Γ(Spec (.of k₀), ⊤) →+* Γ(X₀, V)) (hg : g.Etale)
      (hgC : g.comp MvPolynomial.C = (s₀.appLE ⊤ V le_top).hom) (f : Γ(X₀, V))
      (hf : X₀.basicOpen f ≤ V₁) (hgf : genericPoint X₀ ∈ X₀.basicOpen f)
      (h₀ : Γ(X₀, X₀.basicOpen f)),
      (letI := (s₀.appLE ⊤ (X₀.basicOpen f) le_top).hom.toAlgebra;
        exteriorPower.ιMulti Γ(X₀, X₀.basicOpen f) n
          (fun i => KaehlerDifferential.D Γ(Spec (.of k₀), ⊤) Γ(X₀, X₀.basicOpen f)
            (X₀.presheaf.map (homOfLE hf).op (z i))) =
        h₀ • exteriorPower.ιMulti Γ(X₀, X₀.basicOpen f) n (fun i =>
          KaehlerDifferential.D Γ(Spec (.of k₀), ⊤) Γ(X₀, X₀.basicOpen f)
            (X₀.presheaf.map (homOfLE (X₀.basicOpen_le f)).op (g (MvPolynomial.X i))))) ∧
      (X₀.presheaf.germ (X₀.basicOpen f) (genericPoint X₀) hgf).hom h₀ ≠ 0 := by
  -- `Exists.elim` rather than `obtain`: case splits against this goal are slow
  refine (exists_etale_chart_of_topologicalKrullDim_eq (s₀ := s₀) hn U x hx).elim
    fun V h => h.elim fun hV h => h.elim fun hxV h => h.elim fun g hg => ?_
  have hgV : genericPoint X₀ ∈ V :=
    (genericPoint_spec X₀).specializes trivial |>.mem_open V.isOpen hxV
  refine (hV.exists_basicOpen_le (V := V ⊓ V₁) ⟨genericPoint X₀, hgV, hgV₁⟩ hgV).elim
    fun f h => h.elim fun hfV hgf => ?_
  have hf : X₀.basicOpen f ≤ V₁ := hfV.trans inf_le_right
  refine (MMP.Spreading.exists_wedge_eq_smul s₀ V hV g hg.1 hg.2 f
    (fun i => X₀.presheaf.map (homOfLE hf).op (z i))).elim fun h₀ hrel => ?_
  exact ⟨V, hV, hxV, g, hg.1, hg.2, f, hf, hgf, h₀, hrel,
    germ_ne_zero_of_wedge_eq_smul z ω₀ hω₀def hω₀ g f hf hgf h₀ hrel⟩

/-- **The divisor of a form `dz₁ ∧ ⋯ ∧ dzₙ` and its base change.** For sections `z` of a normal
variety `X₀` over an open through its generic point with `dz ≠ 0`, the base change of `dz` is
nonzero and its divisor is the base change of the divisor of `dz`. -/
private theorem isBaseChange_topFormDivisor_of_sections [LocallyOfFiniteType s₀] [Surjective π]
    [IsDominant π] (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsNormalVariety k₀ s₀) {n : ℕ} (hn : topologicalKrullDim X₀ = n)
    {V₁ : X₀.Opens} (hgV₁ : genericPoint X₀ ∈ V₁) [Nonempty ((𝟙 X₀) ⁻¹ᵁ V₁)]
    [Nonempty (π ⁻¹ᵁ V₁)] (z : Fin n → Γ(X₀, V₁)) :
    haveI : LocallyOfFiniteType s :=
      MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h ‹_›
    letI := MMP.Mori.functionFieldAlgebra s₀
    letI := MMP.Mori.functionFieldAlgebra s
    ∀ (ω₀ : MMP.Mori.RationalTopForms s₀ n) (ω : MMP.Mori.RationalTopForms s n),
      ω₀ = (exteriorPower.ιMulti X₀.functionField n fun i =>
        KaehlerDifferential.D k₀ X₀.functionField
          (X₀.germToFunctionField ((𝟙 X₀) ⁻¹ᵁ V₁) (Scheme.Hom.app (𝟙 X₀) V₁ (z i)))) →
      ω = (exteriorPower.ιMulti X.functionField n fun i =>
        KaehlerDifferential.D K X.functionField
          (X.germToFunctionField (π ⁻¹ᵁ V₁) (π.app V₁ (z i)))) →
      ω₀ ≠ 0 → ω ≠ 0 ∧
        IsBaseChange π (MMP.Mori.topFormDivisor s₀ ω₀) (MMP.Mori.topFormDivisor s ω) := by
  classical
  haveI : LocallyOfFiniteType s := MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h ‹_›
  have h₀sq : IsPullback (𝟙 X₀) s₀ s₀ (𝟙 (Spec (.of k₀))) := IsPullback.of_id_fst
  obtain ⟨U, -, hUsm, hU⟩ := MMP.Spreading.exists_smooth_open_of_isNormalVariety s₀ hX₀
  have hcoh0 : Order.coheight (genericPoint X₀) ≤ 1 :=
    (Stacks.EtaleCohomology.coheight_genericPoint_eq_zero X₀).trans_le zero_le_one
  have hgenU : genericPoint X₀ ∈ U := hU _ hcoh0
  have hgen (V : X₀.Opens) {x : X₀} (hx : x ∈ V) : genericPoint X₀ ∈ V :=
    (genericPoint_spec X₀).specializes trivial |>.mem_open V.isOpen hx
  have hnonempty (V : X₀.Opens) (hV : genericPoint X₀ ∈ V) : Nonempty (π ⁻¹ᵁ V) := by
    obtain ⟨y, hy⟩ := π.surjective (genericPoint X₀)
    exact ⟨⟨y, show π y ∈ V by rw [hy]; exact hV⟩⟩
  letI := MMP.Mori.functionFieldAlgebra s₀
  letI := MMP.Mori.functionFieldAlgebra s
  intro ω₀ ω hω₀def hωdef hω₀
  -- a chart around every point of `U`, with the Jacobian of `z`
  have key := fun x (hx : x ∈ U) =>
    exists_chart_wedge_eq_smul (s₀ := s₀) hn hgV₁ z ω₀ hω₀def hω₀ U x hx
  -- `ω ≠ 0`
  have hω : ω ≠ 0 := by
    obtain ⟨V, hV, hxV, g, hg, hgC, f, hf, hgf, h₀, hrel, hne⟩ := key _ hgenU
    haveI : Nonempty (X₀.basicOpen f) := ⟨⟨_, hgf⟩⟩
    haveI : Nonempty (π ⁻¹ᵁ X₀.basicOpen f) := hnonempty _ hgf
    haveI : Nonempty (π ⁻¹ᵁ V) := hnonempty _ (hgen V hxV)
    have e := form_eq_smul_of_isPullback h g (X₀.basicOpen f) (X₀.basicOpen_le f)
      (fun i => X₀.presheaf.map (homOfLE hf).op (z i)) h₀ hrel
    have e2 : (fun i => KaehlerDifferential.D K X.functionField
          (X.germToFunctionField (π ⁻¹ᵁ X₀.basicOpen f)
            (π.app _ (X₀.presheaf.map (homOfLE hf).op (z i))))) =
        fun i => KaehlerDifferential.D K X.functionField
          (X.germToFunctionField (π ⁻¹ᵁ V₁) (π.app V₁ (z i))) := by
      funext i
      rw [germToFunctionField_app_map π hf (z i)]
    have e3 : (fun i => KaehlerDifferential.D K X.functionField
          (X.germToFunctionField (π ⁻¹ᵁ X₀.basicOpen f)
            (π.app _ (X₀.presheaf.map (homOfLE (X₀.basicOpen_le f)).op (g (MvPolynomial.X i)))))) =
        fun i => KaehlerDifferential.D K X.functionField
          (X.germToFunctionField (π ⁻¹ᵁ V) (π.app V (g (MvPolynomial.X i)))) := by
      funext i
      rw [germToFunctionField_app_map π (X₀.basicOpen_le f) (g (MvPolynomial.X i))]
    rw [e2, e3] at e
    rw [hωdef, e]
    exact smul_ne_zero (germToFunctionField_app_ne_zero h₀ hne)
      (MMP.Spreading.coordForm_ne_zero_of_isPullback h hV g hg hgC)
  refine ⟨hω, fun P₀ P hP => ?_, fun P hP => ?_⟩
  · have hπP := map_eq_of_closure_eq hP
    have hcoh : Order.coheight P₀.genericPoint ≤ 1 :=
      (MMP.Mori.PrimeDivisor.coheight_genericPoint P₀).le
    obtain ⟨V, hV, hxV, g, hg, hgC, f, hf, hgf, h₀, hrel, hne⟩ := key _ (hU _ hcoh)
    haveI : Nonempty (X₀.basicOpen f) := ⟨⟨_, hgf⟩⟩
    haveI : Nonempty ((𝟙 X₀) ⁻¹ᵁ X₀.basicOpen f) := ⟨⟨_, hgf⟩⟩
    haveI : Nonempty (π ⁻¹ᵁ X₀.basicOpen f) := hnonempty _ hgf
    change P.ordForm (ω.toPluriForms s) = P₀.ordForm (ω₀.toPluriForms s₀)
    rw [ordForm_chart h hV g hg hgC z f hf h₀ hrel P (show π P.genericPoint ∈ V by
        rw [hπP]; exact hxV) ω hωdef,
      ordForm_chart h₀sq hV g hg hgC z f hf h₀ hrel P₀ hxV ω₀ hω₀def, germToFunctionField_id_app]
    exact ord_germToFunctionField_app_of_closure_eq h hP h₀ hne
  · by_contra hno
    have hπP : π P.genericPoint = genericPoint X₀ := by
      by_contra hne
      exact hno (exists_closure_eq_of_map_ne_genericPoint h P hne)
    apply hP
    obtain ⟨V, hV, hxV, g, hg, hgC, f, hf, hgf, h₀, hrel, hne⟩ := key _ hgenU
    haveI : Nonempty (X₀.basicOpen f) := ⟨⟨_, hgf⟩⟩
    haveI : Nonempty (π ⁻¹ᵁ X₀.basicOpen f) := hnonempty _ hgf
    change P.ordForm (ω.toPluriForms s) = 0
    rw [ordForm_chart h hV g hg hgC z f hf h₀ hrel P (show π P.genericPoint ∈ V by
        rw [hπP]; exact hxV) ω hωdef]
    exact ord_germToFunctionField_app_eq_zero hπP h₀ hne

/-- **A rational top form and its base change have base-changed divisors.** -/
private theorem exists_topForm_isBaseChange [LocallyOfFiniteType s₀] [Surjective π] [IsDominant π]
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsNormalVariety k₀ s₀) {n : ℕ} (hn : topologicalKrullDim X₀ = n) :
    haveI : LocallyOfFiniteType s :=
      MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h ‹_›
    ∃ (ω₀ : MMP.Mori.RationalTopForms s₀ n) (ω : MMP.Mori.RationalTopForms s n), ω₀ ≠ 0 ∧ ω ≠ 0 ∧
      IsBaseChange π (MMP.Mori.topFormDivisor s₀ ω₀) (MMP.Mori.topFormDivisor s ω) := by
  classical
  haveI : LocallyOfFiniteType s := MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h ‹_›
  have h₀sq : IsPullback (𝟙 X₀) s₀ s₀ (𝟙 (Spec (.of k₀))) := IsPullback.of_id_fst
  obtain ⟨U, -, hUsm, hU⟩ := MMP.Spreading.exists_smooth_open_of_isNormalVariety s₀ hX₀
  have hcoh0 : Order.coheight (genericPoint X₀) ≤ 1 :=
    (Stacks.EtaleCohomology.coheight_genericPoint_eq_zero X₀).trans_le zero_le_one
  obtain ⟨V₁, -, hV₁, hgV₁, n₁, g₁, hg₁, hg₁C⟩ :=
    MMP.Spreading.exists_etale_chart_of_smooth_on s₀ U (genericPoint X₀) (hU _ hcoh0)
  obtain rfl : n₁ = n := chart_dim_eq_of_isPullback h₀sq hn V₁ hV₁ g₁ hg₁ hg₁C hgV₁
  haveI : Nonempty ((𝟙 X₀) ⁻¹ᵁ V₁) := ⟨⟨_, hgV₁⟩⟩
  haveI : Nonempty (π ⁻¹ᵁ V₁) := by
    obtain ⟨y, hy⟩ := π.surjective (genericPoint X₀)
    exact ⟨⟨y, show π y ∈ V₁ by rw [hy]; exact hgV₁⟩⟩
  letI := MMP.Mori.functionFieldAlgebra s₀
  letI := MMP.Mori.functionFieldAlgebra s
  have hω₀ := MMP.Spreading.coordForm_ne_zero_of_isPullback h₀sq hV₁ g₁ hg₁ hg₁C
  obtain ⟨hω, hb⟩ := isBaseChange_topFormDivisor_of_sections h hX₀ hn hgV₁
    (fun i => g₁ (MvPolynomial.X i)) _ _ rfl rfl hω₀
  exact ⟨_, _, hω₀, hω, hb⟩

end TopForms

/-! ### Principal divisors under base change -/

section PrincipalDescent

attribute [local instance] MMP.Resolution.componentField

variable {X₀ X : Scheme.{u}} [IsIntegral X₀] [IsIntegral X] [IsNormal X₀] [IsNormal X]
  [IsLocallyNoetherian X₀] [IsLocallyNoetherian X] [CompactSpace X₀] [CompactSpace X]
  {s₀ : X₀ ⟶ Spec (.of k₀)} {s : X ⟶ Spec (.of K)} {π : X ⟶ X₀}

/-- **Principal divisors base change to principal divisors.** -/
private theorem exists_isBaseChange_principalDivisor [LocallyOfFiniteType s₀] [Surjective π]
    [IsDominant π] (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (φ₀ : (RationalFunctions X₀)ˣ) :
    ∃ φ : (RationalFunctions X)ˣ, IsBaseChange π (principalDivisor φ₀) (principalDivisor φ) := by
  obtain ⟨Z₀⟩ : Nonempty (irreducibleComponents X₀) :=
    ⟨⟨_, irreducibleComponent_mem_irreducibleComponents (genericPoint X₀)⟩⟩
  have hne (Z : irreducibleComponents X) :
      MMP.Fourfold.fieldMap π Z₀ Z ((φ₀ : RationalFunctions X₀) Z₀) ≠ 0 :=
    (map_ne_zero _).mpr ((φ₀.isUnit.map (RationalFunctions.component X₀ Z₀)).ne_zero)
  let φ : (RationalFunctions X)ˣ := (RationalFunctions.unitsEquiv X).symm fun Z =>
    Units.mk0 _ (hne Z)
  have hφ (Z : irreducibleComponents X) : (φ : RationalFunctions X) Z =
      MMP.Fourfold.fieldMap π Z₀ Z ((φ₀ : RationalFunctions X₀) Z₀) := rfl
  have hsub : Subsingleton (irreducibleComponents X₀) := by
    rw [irreducibleComponents_eq_singleton]; infer_instance
  refine ⟨φ, ⟨fun P₀ P hP => ?_, fun P hP => ?_⟩⟩
  · change P.ord φ = P₀.ord φ₀
    have e1 := P.valuation_component φ
    rw [hφ, Subsingleton.elim Z₀ P₀.component,
      valuation_fieldMap_of_closure_eq h hP, P₀.valuation_component] at e1
    exact (WithZero.exp_injective e1).symm
  · by_contra hno
    have hπP : π P.genericPoint = genericPoint X₀ := by
      by_contra hne
      exact hno (exists_closure_eq_of_map_ne_genericPoint h P hne)
    apply hP
    change P.ord φ = 0
    have e1 := P.valuation_component φ
    rw [hφ, valuation_fieldMap_eq_one hπP Z₀ (a := (φ₀ : RationalFunctions X₀) Z₀)
      (φ₀.isUnit.map (RationalFunctions.component X₀ Z₀))] at e1
    exact (WithZero.exp_eq_one.mp e1.symm)

/-- **Uniqueness of coefficients.** If `∑ x_β b_β = 0` in `K(X)` for a `k₀`-basis `(b_β)` of `K`
and `x_β ∈ K(X₀)`, then all `x_β = 0`. -/
private theorem eq_zero_of_sum_fieldMap_eq_zero [LocallyOfFiniteType s₀] [Surjective π]
    [IsDominant π] (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (P₀ : MMP.Mori.PrimeDivisor X₀) {Z₀ : irreducibleComponents X₀} {Z : irreducibleComponents X}
    {t : Finset (Module.Basis.ofVectorSpaceIndex k₀ K)}
    (x : Module.Basis.ofVectorSpaceIndex k₀ K → X₀.presheaf.stalk (componentGenericPoint X₀ Z₀))
    (hx : ∑ β ∈ t, MMP.Fourfold.fieldMap π Z₀ Z (x β) *
      cstGerm s Z (Module.Basis.ofVectorSpace k₀ K β) = 0) :
    ∀ β ∈ t, x β = 0 := by
  obtain ⟨P, hP, -⟩ := exists_primeDivisor_baseChange h P₀
  have hsub₀ : Subsingleton (irreducibleComponents X₀) := by
    rw [irreducibleComponents_eq_singleton]; infer_instance
  have hsub : Subsingleton (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]; infer_instance
  obtain rfl : Z₀ = P₀.component := Subsingleton.elim _ _
  obtain rfl : Z = P.component := Subsingleton.elim _ _
  intro β hβ
  by_contra hne
  let b := Module.Basis.ofVectorSpace k₀ K
  have hG (n : ℤ) : P₀.OrdGE n (x β) := by
    refine ordGE_of_ordGE_sum h hP (ι := t) (fun j => x j) (fun j => b j)
      (b.linearIndependent.comp _ Subtype.val_injective) n ?_ ⟨β, hβ⟩
    refine Or.inl ?_
    rw [← hx, ← Finset.sum_coe_sort t]
  have hv : P₀.valuation (x β) ≠ 0 := (map_ne_zero _).mpr hne
  have h1 := (hG (WithZero.log (P₀.valuation (x β)) + 1)).resolve_left hne
  conv_rhs at h1 => rw [← WithZero.exp_log hv]
  rw [WithZero.exp_le_exp] at h1
  omega

/-- **Local decomposition of a unit.** Over an affine open `U₀`, a unit `ψ` of `K(X)` with
`div ψ ≥ -B` for the base change `B` of `B₀` is `∑ m_β b_β` along a `k₀`-basis `(b_β)` of `K`, with
coefficients `m_β ∈ K(X₀)` satisfying `div m_β ≥ -B₀` along every prime divisor meeting `U₀`. -/
private theorem exists_decomposition_of_isBaseChange [LocallyOfFiniteType s₀] [Surjective π]
    [IsDominant π] (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    {U₀ : X₀.Opens} (hU₀ : IsAffineOpen U₀) [Nonempty U₀] {B₀ : Divisor X₀} {B : Divisor X}
    (hB : IsBaseChange π B₀ B) (ψ : (RationalFunctions X)ˣ)
    (hψ : ∀ E : MMP.Mori.PrimeDivisor X, -B.coeff E ≤ E.ord ψ) (Z₀ : irreducibleComponents X₀) :
    ∃ (t : Finset (Module.Basis.ofVectorSpaceIndex k₀ K))
      (m : Module.Basis.ofVectorSpaceIndex k₀ K → RationalFunctions X₀),
      (∀ β ∉ t, m β = 0) ∧
      (∀ Z : irreducibleComponents X, (ψ : RationalFunctions X) Z =
        ∑ β ∈ t, MMP.Fourfold.fieldMap π Z₀ Z (m β Z₀) *
          cstGerm s Z (Module.Basis.ofVectorSpace k₀ K β)) ∧
      ∀ β (E₀ : MMP.Mori.PrimeDivisor X₀), E₀.genericPoint ∈ U₀ →
        E₀.OrdGE (-B₀.coeff E₀) (m β E₀.component) := by
  classical
  haveI : IsAffineHom π := MorphismProperty.of_isPullback (P := @IsAffineHom) h.flip inferInstance
  haveI : Nonempty (π ⁻¹ᵁ U₀) := by
    obtain ⟨x⟩ := ‹Nonempty U₀›
    obtain ⟨y, hy⟩ := π.surjective x.1
    exact ⟨⟨y, show π y ∈ U₀ by rw [hy]; exact x.2⟩⟩
  obtain ⟨c₀, hc₀g, hc₀⟩ := exists_section_ordGE_natAbs hU₀ B₀
  have hψE (E : MMP.Mori.PrimeDivisor X) : E.OrdGE (-B.coeff E) ((ψ : RationalFunctions X)
      E.component) := (ordGE_component E ψ).mono (hψ E)
  have hsec : (0 : Divisor X).IsDivisorialSection (π ⁻¹ᵁ U₀) (fun Z =>
      (X.presheaf.germ _ _ Z.2).hom ((π.app U₀).hom c₀) * (ψ : RationalFunctions X) Z.1) := by
    intro E hE
    have hEU := E.genericPoint_mem_of_nonempty hE
    rw [DivisorWithCoeffs.coeff_zero, neg_zero]
    by_cases hb : ∃ E₀ : MMP.Mori.PrimeDivisor X₀,
        closure {E.genericPoint} = π.base ⁻¹' closure {E₀.genericPoint}
    · obtain ⟨E₀, hE₀⟩ := hb
      have hE₀U : E₀.genericPoint ∈ U₀ := map_eq_of_closure_eq hE₀ ▸ hEU
      have h1 := ordGE_fieldMap h hE₀ (hc₀ E₀ hE₀U)
      rw [MMP.Fourfold.fieldMap_germ] at h1
      refine (h1.mul (hψE E)).mono ?_
      rw [show B.coeff E = B₀.coeff E₀ from hB.1 E₀ E hE₀]
      have := le_abs_self (B₀.coeff E₀)
      simp only [Int.natCast_natAbs]
      linarith
    · have hBE : B.coeff E = 0 := by
        by_contra hne; exact hb (hB.2 E hne)
      have h2 := hψE E
      rw [hBE, neg_zero] at h2
      simpa using (ordGE_zero_germ ((π.app U₀).hom c₀) E hEU).mul h2
  obtain ⟨u, hu⟩ := hsec.exists_eq
  obtain ⟨ordc, hordc⟩ := exists_valuation_germ_eq_exp hc₀g
  have hbound (E₀ : MMP.Mori.PrimeDivisor X₀) (E : MMP.Mori.PrimeDivisor X)
      (hE : closure {E.genericPoint} = π.base ⁻¹' closure {E₀.genericPoint})
      (hEU : E.genericPoint ∈ π ⁻¹ᵁ U₀) :
      E.OrdGE (ordc E₀ + -B₀.coeff E₀)
        ((X.presheaf.germ (π ⁻¹ᵁ U₀) (componentGenericPoint X E.component)
          (E.specializes_genericPoint.mem_open (π ⁻¹ᵁ U₀).isOpen hEU)).hom u) := by
    have hE₀U : E₀.genericPoint ∈ U₀ := map_eq_of_closure_eq hE ▸ hEU
    have e1 := congrFun hu ⟨E.component, E.specializes_genericPoint.mem_open
      (π ⁻¹ᵁ U₀).isOpen hEU⟩
    rw [toRationalFunctionsPresheaf_app_apply] at e1
    rw [e1]
    have hv : E.valuation ((X.presheaf.germ (π ⁻¹ᵁ U₀) (componentGenericPoint X E.component)
        (E.specializes_genericPoint.mem_open (π ⁻¹ᵁ U₀).isOpen hEU)).hom ((π.app U₀).hom c₀)) =
        WithZero.exp (ordc E₀) := by
      rw [← MMP.Fourfold.fieldMap_germ π E₀.component E.component
        (E₀.specializes_genericPoint.mem_open U₀.isOpen hE₀U),
        valuation_fieldMap_of_closure_eq h hE, hordc E₀ hE₀U]
    have h2 := hψE E
    rw [show B.coeff E = B₀.coeff E₀ from hB.1 E₀ E hE] at h2
    exact ordGE_mul_of_valuation_eq h2 hv
  obtain ⟨t, a, hua, ha⟩ := exists_sum_basis_ordGE h hU₀ u (fun E₀ => ordc E₀ + -B₀.coeff E₀)
    hbound
  have hZU₀ (Z : irreducibleComponents X₀) : componentGenericPoint X₀ Z ∈ U₀ := by
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint]
    obtain ⟨x⟩ := ‹Nonempty U₀›
    exact (genericPoint_spec X₀).specializes trivial |>.mem_open U₀.isOpen x.2
  let m : Module.Basis.ofVectorSpaceIndex k₀ K → RationalFunctions X₀ := fun β Z =>
    if β ∈ t then (X₀.presheaf.germ U₀ (componentGenericPoint X₀ Z) (hZU₀ Z)).hom (a β) /
      (X₀.presheaf.germ U₀ (componentGenericPoint X₀ Z) (hZU₀ Z)).hom c₀ else 0
  refine ⟨t, m, fun β hβ => funext fun Z => by simp [m, hβ], fun Z => ?_, fun β E₀ hE₀ => ?_⟩
  · have hZ : componentGenericPoint X Z ∈ π ⁻¹ᵁ U₀ := by
      show π (componentGenericPoint X Z) ∈ U₀
      rw [MMP.Fourfold.map_componentGenericPoint π Z Z₀]; exact hZU₀ Z₀
    have e1 := congrFun hu ⟨Z, hZ⟩
    rw [toRationalFunctionsPresheaf_app_apply] at e1
    have hc : MMP.Fourfold.fieldMap π Z₀ Z
        ((X₀.presheaf.germ U₀ (componentGenericPoint X₀ Z₀) (hZU₀ Z₀)).hom c₀) ≠ 0 :=
      (map_ne_zero _).mpr (isUnit_germ_componentGenericPoint hc₀g Z₀ (hZU₀ Z₀)).ne_zero
    have e3 : (X.presheaf.germ (π ⁻¹ᵁ U₀) (componentGenericPoint X Z) hZ).hom u =
        ∑ β ∈ t, MMP.Fourfold.fieldMap π Z₀ Z
          ((X₀.presheaf.germ U₀ (componentGenericPoint X₀ Z₀) (hZU₀ Z₀)).hom (a β)) *
            cstGerm s Z (Module.Basis.ofVectorSpace k₀ K β) := by
      rw [hua, map_sum]
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [map_mul, germ_appLE_top, ← MMP.Fourfold.fieldMap_germ π Z₀ Z (hZU₀ Z₀)]
    rw [e1, ← MMP.Fourfold.fieldMap_germ π Z₀ Z (hZU₀ Z₀)] at e3
    have e4 : ∑ β ∈ t, MMP.Fourfold.fieldMap π Z₀ Z (m β Z₀) *
          cstGerm s Z (Module.Basis.ofVectorSpace k₀ K β) =
        (∑ β ∈ t, MMP.Fourfold.fieldMap π Z₀ Z
          ((X₀.presheaf.germ U₀ (componentGenericPoint X₀ Z₀) (hZU₀ Z₀)).hom (a β)) *
            cstGerm s Z (Module.Basis.ofVectorSpace k₀ K β)) /
          MMP.Fourfold.fieldMap π Z₀ Z
            ((X₀.presheaf.germ U₀ (componentGenericPoint X₀ Z₀) (hZU₀ Z₀)).hom c₀) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun β hβ => ?_
      simp only [m, if_pos hβ, map_div₀]
      ring
    rw [e4, ← e3, mul_div_cancel_left₀ _ hc]
  · by_cases hβ : β ∈ t
    · have h1 := ordGE_div_of_valuation_eq (ha β hβ E₀ hE₀) (hordc E₀ hE₀)
      simp only [m, if_pos hβ]
      refine h1.mono (le_of_eq ?_)
      ring
    · simp only [m, if_neg hβ]
      exact PrimeDivisor.OrdGE.zero _

/-- **Principal descent.** Over an algebraically closed field `k₀`, a divisor on a proper `X₀`
whose base change is principal is principal. -/
private theorem exists_eq_principalDivisor_of_isBaseChange [LocallyOfFiniteType s₀] [Surjective π]
    [IsDominant π] [UniversallyClosed s₀]
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    {D₀ : Divisor X₀} {φ : (RationalFunctions X)ˣ} (hD : IsBaseChange π D₀ (principalDivisor φ)) :
    ∃ φ₀ : (RationalFunctions X₀)ˣ, D₀ = principalDivisor φ₀ := by
  classical
  by_cases hemp : IsEmpty (MMP.Mori.PrimeDivisor X₀)
  · exact ⟨1, Finsupp.ext fun E₀ => isEmptyElim E₀⟩
  rw [not_isEmpty_iff] at hemp
  obtain ⟨P₀⟩ := hemp
  obtain ⟨Z₀⟩ : Nonempty (irreducibleComponents X₀) :=
    ⟨⟨_, irreducibleComponent_mem_irreducibleComponents (genericPoint X₀)⟩⟩
  obtain ⟨Z⟩ : Nonempty (irreducibleComponents X) :=
    ⟨⟨_, irreducibleComponent_mem_irreducibleComponents (genericPoint X)⟩⟩
  have hsub₀ : Subsingleton (irreducibleComponents X₀) := by
    rw [irreducibleComponents_eq_singleton]; infer_instance
  have haff (x : X₀) : ∃ U₀ : X₀.Opens, IsAffineOpen U₀ ∧ x ∈ U₀ := by
    obtain ⟨U₀, hU₀, hxU₀, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X₀.isBasis_affineOpens
      (U := ⊤) (x := x) trivial
    exact ⟨U₀, hU₀, hxU₀⟩
  have hord_inv (E : MMP.Mori.PrimeDivisor X) :
      -(principalDivisor φ).coeff E ≤ E.ord φ⁻¹ := by simp
  have hord (E : MMP.Mori.PrimeDivisor X) : -(-principalDivisor φ).coeff E ≤ E.ord φ := by simp
  -- coefficients of a decomposition do not depend on the affine open
  have huniq {t₁ t₂ : Finset (Module.Basis.ofVectorSpaceIndex k₀ K)}
      {m₁ m₂ : Module.Basis.ofVectorSpaceIndex k₀ K → RationalFunctions X₀}
      (ψ : (RationalFunctions X)ˣ) (h₁0 : ∀ β ∉ t₁, m₁ β = 0) (h₂0 : ∀ β ∉ t₂, m₂ β = 0)
      (h₁ : ∀ Z : irreducibleComponents X, (ψ : RationalFunctions X) Z =
        ∑ β ∈ t₁, MMP.Fourfold.fieldMap π Z₀ Z (m₁ β Z₀) *
          cstGerm s Z (Module.Basis.ofVectorSpace k₀ K β))
      (h₂ : ∀ Z : irreducibleComponents X, (ψ : RationalFunctions X) Z =
        ∑ β ∈ t₂, MMP.Fourfold.fieldMap π Z₀ Z (m₂ β Z₀) *
          cstGerm s Z (Module.Basis.ofVectorSpace k₀ K β)) (β) : m₁ β = m₂ β := by
    have hz := eq_zero_of_sum_fieldMap_eq_zero h P₀ (Z := Z) (t := t₁ ∪ t₂)
      (fun γ => m₁ γ Z₀ - m₂ γ Z₀) (by
        simp only [map_sub, sub_mul, Finset.sum_sub_distrib]
        rw [← Finset.sum_subset Finset.subset_union_left (fun γ _ hγ => by
            rw [h₁0 γ hγ]; simp),
          ← Finset.sum_subset Finset.subset_union_right (fun γ _ hγ => by
            rw [h₂0 γ hγ]; simp), ← h₁ Z, ← h₂ Z, sub_self])
    have hβ : m₁ β Z₀ = m₂ β Z₀ := by
      by_cases hβ : β ∈ t₁ ∪ t₂
      · exact sub_eq_zero.mp (hz β hβ)
      · rw [Finset.mem_union, not_or] at hβ
        rw [h₁0 β hβ.1, h₂0 β hβ.2]
    funext Z'
    obtain rfl : Z' = Z₀ := Subsingleton.elim _ _
    exact hβ
  -- decompositions of `φ⁻¹` and `φ`
  obtain ⟨U₁, hU₁, hxU₁⟩ := haff (genericPoint X₀)
  haveI : Nonempty U₁ := ⟨⟨_, hxU₁⟩⟩
  obtain ⟨t, m, hm0, hmid, -⟩ := exists_decomposition_of_isBaseChange h hU₁ hD φ⁻¹ hord_inv Z₀
  obtain ⟨t', m', hm0', hmid', -⟩ :=
    exists_decomposition_of_isBaseChange h hU₁ hD.neg φ hord Z₀
  have hglob (β) (E₀ : MMP.Mori.PrimeDivisor X₀) :
      E₀.OrdGE (-D₀.coeff E₀) (m β E₀.component) := by
    obtain ⟨U₂, hU₂, hxU₂⟩ := haff E₀.genericPoint
    haveI : Nonempty U₂ := ⟨⟨_, hxU₂⟩⟩
    obtain ⟨t₂, m₂, hm₂0, hm₂id, hm₂b⟩ :=
      exists_decomposition_of_isBaseChange h hU₂ hD φ⁻¹ hord_inv Z₀
    rw [huniq φ⁻¹ hm0 hm₂0 hmid hm₂id β]
    exact hm₂b β E₀ hxU₂
  have hglob' (β) (E₀ : MMP.Mori.PrimeDivisor X₀) :
      E₀.OrdGE (D₀.coeff E₀) (m' β E₀.component) := by
    obtain ⟨U₂, hU₂, hxU₂⟩ := haff E₀.genericPoint
    haveI : Nonempty U₂ := ⟨⟨_, hxU₂⟩⟩
    obtain ⟨t₂, m₂, hm₂0, hm₂id, hm₂b⟩ :=
      exists_decomposition_of_isBaseChange h hU₂ hD.neg φ hord Z₀
    rw [huniq φ hm0' hm₂0 hmid' hm₂id β]
    simpa using hm₂b β E₀ hxU₂
  -- some product of coefficients is nonzero
  have hprod : (1 : X.presheaf.stalk (componentGenericPoint X Z)) =
      ∑ β ∈ t, ∑ γ ∈ t', MMP.Fourfold.fieldMap π Z₀ Z (m β Z₀ * m' γ Z₀) *
        (cstGerm s Z (Module.Basis.ofVectorSpace k₀ K β) *
          cstGerm s Z (Module.Basis.ofVectorSpace k₀ K γ)) := by
    have e := congrFun (congrArg Units.val (inv_mul_cancel φ)) Z
    rw [Units.val_mul, Pi.mul_apply, hmid Z, hmid' Z, Finset.sum_mul_sum, Units.val_one,
      Pi.one_apply] at e
    rw [← e]
    refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun γ _ => ?_
    rw [map_mul]
    ring
  obtain ⟨β, -, γ, -, hne⟩ : ∃ β ∈ t, ∃ γ ∈ t', m β Z₀ * m' γ Z₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    exact one_ne_zero <| hprod.trans <| Finset.sum_eq_zero fun β hβ =>
      Finset.sum_eq_zero fun γ hγ => by rw [hall β hβ γ hγ, map_zero, zero_mul]
  have hneZ (Z' : irreducibleComponents X₀) : m β Z' ≠ 0 ∧ m' γ Z' ≠ 0 := by
    obtain rfl : Z' = Z₀ := Subsingleton.elim _ _
    exact ⟨left_ne_zero_of_mul hne, right_ne_zero_of_mul hne⟩
  -- the product is a regular function, hence a constant
  have hsecr : (0 : Divisor X₀).IsDivisorialSection ⊤ (fun Z' => m β Z'.1 * m' γ Z'.1) := by
    intro E₀ _
    rw [DivisorWithCoeffs.coeff_zero, neg_zero]
    simpa using (hglob β E₀).mul (hglob' γ E₀)
  obtain ⟨ρ, hρ⟩ := hsecr.exists_eq
  have hfield : IsField Γ(X₀, ⊤) := isField_of_universallyClosed k₀ s₀
  letI := hfield.toField
  have hρ0 : ρ ≠ 0 := by
    intro h0
    apply hne
    have e := congrFun hρ ⟨Z₀, trivial⟩
    rw [toRationalFunctionsPresheaf_app_apply, h0, map_zero] at e
    exact e.symm
  have hρu : IsUnit ρ := isUnit_iff_ne_zero.mpr hρ0
  have hval (E₀ : MMP.Mori.PrimeDivisor X₀) :
      E₀.valuation (m β E₀.component * m' γ E₀.component) = 1 := by
    have e := congrFun hρ ⟨E₀.component, trivial⟩
    rw [toRationalFunctionsPresheaf_app_apply] at e
    rw [← e]
    refine valuation_germ_eq_one ρ E₀ trivial ?_
    rw [X₀.basicOpen_of_isUnit hρu]
    trivial
  -- the local equation
  let ψ₀ : (RationalFunctions X₀)ˣ := (RationalFunctions.unitsEquiv X₀).symm fun Z' =>
    Units.mk0 (m β Z')⁻¹ (inv_ne_zero (hneZ Z').1)
  have hψ₀ (Z' : irreducibleComponents X₀) : (ψ₀ : RationalFunctions X₀) Z' = (m β Z')⁻¹ := rfl
  refine ⟨ψ₀, Finsupp.ext fun E₀ => ?_⟩
  change D₀.coeff E₀ = E₀.ord ψ₀
  have hv := E₀.valuation_component ψ₀
  have h1 := (hglob β E₀).resolve_left (hneZ E₀.component).1
  have h2 := (hglob' γ E₀).resolve_left (hneZ E₀.component).2
  have e := hval E₀
  rw [map_mul] at e
  set va := E₀.valuation (m β E₀.component) with hva_def
  set va' := E₀.valuation (m' γ E₀.component) with hva'_def
  have hva0 : va ≠ 0 := (map_ne_zero _).mpr (hneZ E₀.component).1
  have hva'0 : va' ≠ 0 := (map_ne_zero _).mpr (hneZ E₀.component).2
  rw [← WithZero.exp_log hva0] at h1 e
  rw [← WithZero.exp_log hva'0] at h2 e
  rw [WithZero.exp_le_exp] at h1 h2
  rw [← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_inj] at e
  rw [hψ₀, map_inv₀, ← hva_def, ← WithZero.exp_log hva0, ← WithZero.exp_neg,
    WithZero.exp_inj] at hv
  omega

end PrincipalDescent

section CoeffBaseChange

variable {X₀ X : Scheme.{u}} [IsIntegral X₀] [IsIntegral X] {s₀ : X₀ ⟶ Spec (.of k₀)}
  {s : X ⟶ Spec (.of K)} {π : X ⟶ X₀}

/-- A condition on coefficients holding at `0` holds for all coefficients of a divisor over `k₀`
iff it holds for all coefficients of its base change. -/
public theorem forall_coeff_iff_of_isBaseChange [LocallyOfFiniteType s₀]
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))) {R : Type*} [Zero R]
    {B₀ : DivisorWithCoeffs R X₀} {B : DivisorWithCoeffs R X} (hB : IsBaseChange π B₀ B)
    {p : R → Prop} (hp : p 0) : (∀ P, p (B₀.coeff P)) ↔ ∀ P, p (B.coeff P) := by
  constructor
  · intro H P
    by_cases hP : B P = 0
    · change p (B P)
      rw [hP]
      exact hp
    · obtain ⟨P₀, hP₀⟩ := hB.2 P hP
      change p (B P)
      rw [hB.1 P₀ P hP₀]
      exact H P₀
  · intro H P₀
    obtain ⟨P, hP, -⟩ := exists_primeDivisor_baseChange h P₀
    change p (B₀ P₀)
    rw [← hB.1 P₀ P hP]
    exact H P

/-- The support of a base change is the preimage of the support. -/
public theorem coe_supp_eq_preimage_of_isBaseChange [LocallyOfFiniteType s₀]
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))) {R : Type*} [Zero R]
    {D₀ : DivisorWithCoeffs R X₀} {D : DivisorWithCoeffs R X} (hD : IsBaseChange π D₀ D) :
    (D.supp : Set X) = π ⁻¹' (D₀.supp : Set X₀) := by
  ext x
  simp only [SetLike.mem_coe, Set.mem_preimage, DivisorWithCoeffs.mem_supp_iff]
  constructor
  · rintro ⟨E, hE, hx⟩
    obtain ⟨E₀, hE₀⟩ := hD.2 E hE
    refine ⟨E₀, ?_, ?_⟩
    · change D₀ E₀ ≠ 0
      rw [← hD.1 E₀ E hE₀]
      exact hE
    · have hx' : x ∈ closure {E.genericPoint} := by
        rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact hx
      rw [hE₀] at hx'
      show π x ∈ E₀.support
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact hx'
  · rintro ⟨E₀, hE₀, hx⟩
    obtain ⟨E, hE, -⟩ := exists_primeDivisor_baseChange h E₀
    refine ⟨E, ?_, ?_⟩
    · change D E ≠ 0
      rw [hD.1 E₀ E hE]
      exact hE₀
    · have hx' : π x ∈ closure {E₀.genericPoint} := by
        rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact hx
      show x ∈ E.support
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, hE]
      exact hx'

end CoeffBaseChange

section Model

variable {X₀ X : Scheme.{u}} [IsIntegral X₀] [CompactSpace X₀] [IsLocallyNoetherian X₀]
  [IsNormal X₀] [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {s₀ : X₀ ⟶ Spec (.of k₀)} {s : X ⟶ Spec (.of K)} {π : X ⟶ X₀}

/-- **Base change of Cartier divisors.** The pull-back of a Cartier divisor `L₀` to the base change
is the base change of `L₀`. -/
public theorem isBaseChange_pullback
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) {L₀ : Divisor X₀} (hL₀ : L₀.IsCartier)
    (hB : ∀ Z : irreducibleComponents X, π (componentGenericPoint X Z) ∉ L₀.supp) :
    IsBaseChange π L₀ (L₀.pullback hL₀ hB) := by
  have : LocallyOfFiniteType s₀ := hX₀.toLocallyOfFiniteType
  have : Surjective π := surjective_of_isPullback h
  have : IsDominant π := inferInstance
  have hL := Divisor.isPullback_pullback hL₀ hB
  refine ⟨fun P₀ P hP => ?_, fun P hP => ?_⟩
  · have hπ : π P.genericPoint = P₀.genericPoint := map_eq_of_closure_eq hP
    obtain ⟨U, hU, φ, hφ⟩ := hL₀ P₀.genericPoint
    have hE : (P.support ∩ π ⁻¹ᵁ U).Nonempty :=
      (P.genericPoint_mem_iff (π ⁻¹ᵁ U)).mp (show π P.genericPoint ∈ U by rw [hπ]; exact hU)
    have h1 := MMP.Fourfold.valuation_fieldMap_of_isPullback π hL hφ P hE P₀.component
    rw [valuation_fieldMap_of_closure_eq h hP, P₀.valuation_component,
      ← hφ P₀ ((P₀.genericPoint_mem_iff U).mp hU)] at h1
    exact (WithZero.exp_injective h1).symm
  · by_contra hne
    have hgen : π P.genericPoint = genericPoint X₀ := by
      by_contra hg
      exact hne (exists_closure_eq_of_map_ne_genericPoint h P hg)
    obtain ⟨U, hU, φ, hφ⟩ := hL₀ (π P.genericPoint)
    have hE : (P.support ∩ π ⁻¹ᵁ U).Nonempty := (P.genericPoint_mem_iff (π ⁻¹ᵁ U)).mp hU
    obtain ⟨Z₀⟩ : Nonempty (irreducibleComponents X₀) := ⟨pointComponent (genericPoint X₀)⟩
    have h1 := MMP.Fourfold.valuation_fieldMap_of_isPullback π hL hφ P hE Z₀
    have hu : IsUnit ((φ : RationalFunctions X₀) Z₀) :=
      φ.isUnit.map (RationalFunctions.component X₀ Z₀)
    rw [valuation_fieldMap_eq_one hgen Z₀ hu] at h1
    exact hP (WithZero.exp_injective (h1.symm.trans WithZero.exp_zero.symm))

/-- **Base change of Cartier divisors.** The pull-back of a Cartier divisor `L₀` to the base change
is a Cartier divisor which is the base change of `L₀`, and its sheaf is the pull-back of
`𝒪_{X₀}(L₀)`. -/
public theorem exists_isBaseChange_of_isCartier
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) {L₀ : Divisor X₀} (hL₀ : L₀.IsCartier) :
    ∃ L : Divisor X, L.IsCartier ∧ IsBaseChange π L₀ L ∧
      Nonempty (L.divisorialSheaf ≅ (Scheme.Modules.pullback π).obj L₀.divisorialSheaf) := by
  have : LocallyOfFiniteType s₀ := hX₀.toLocallyOfFiniteType
  have : Surjective π := surjective_of_isPullback h
  have : IsDominant π := inferInstance
  have hB : ∀ Z : irreducibleComponents X, π (componentGenericPoint X Z) ∉ L₀.supp :=
    MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant π L₀
  exact ⟨L₀.pullback hL₀ hB, Divisor.IsCartier.isCartier_pullback hL₀ π hB,
    isBaseChange_pullback h hX₀ hL₀ hB, Divisor.nonempty_divisorialSheaf_pullback_iso hL₀ π hB⟩

/-- Equality of base-changed divisors is detected over `k₀`. -/
public theorem eq_iff_of_isBaseChange {R : Type*} [Zero R]
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) {D₀ E₀ : DivisorWithCoeffs R X₀}
    {D E : DivisorWithCoeffs R X} (hD : IsBaseChange π D₀ D) (hE : IsBaseChange π E₀ E) :
    D₀ = E₀ ↔ D = E := by
  have : LocallyOfFiniteType s₀ := hX₀.toLocallyOfFiniteType
  constructor
  · rintro rfl
    ext P
    change D P = E P
    by_cases hP : D P = 0 ∧ E P = 0
    · rw [hP.1, hP.2]
    · obtain ⟨P₀, hP₀⟩ : ∃ P₀ : MMP.Mori.PrimeDivisor X₀,
          closure {P.genericPoint} = π.base ⁻¹' closure {P₀.genericPoint} := by
        by_cases hD0 : D P = 0
        · exact hE.2 P fun h0 => hP ⟨hD0, h0⟩
        · exact hD.2 P hD0
      rw [hD.1 P₀ P hP₀, hE.1 P₀ P hP₀]
  · intro hDE
    ext P₀
    change D₀ P₀ = E₀ P₀
    obtain ⟨P, hP, -⟩ := exists_primeDivisor_baseChange h P₀
    rw [← hD.1 P₀ P hP, ← hE.1 P₀ P hP, hDE]

/-- **Descent of divisors.** A divisor on the base change all of whose components are base
changes of prime divisors of `X₀` is the base change of a divisor of `X₀`. -/
public theorem exists_isBaseChange_of_forall {R : Type*} [Zero R]
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) {D : DivisorWithCoeffs R X}
    (hD : ∀ P : MMP.Mori.PrimeDivisor X, D P ≠ 0 → ∃ P₀ : MMP.Mori.PrimeDivisor X₀,
      closure {P.genericPoint} = π.base ⁻¹' closure {P₀.genericPoint}) :
    ∃ D₀ : DivisorWithCoeffs R X₀, IsBaseChange π D₀ D := by
  classical
  have : LocallyOfFiniteType s₀ := hX₀.toLocallyOfFiniteType
  have : Surjective π := surjective_of_isPullback h
  choose β hβ _ using exists_primeDivisor_baseChange h
  have hβinj : Function.Injective β := fun P₀ Q₀ e =>
    primeDivisor_eq_of_closure_eq (hβ P₀) (by rw [e]; exact hβ Q₀)
  let D₀ : DivisorWithCoeffs R X₀ := Finsupp.ofSupportFinite (fun P₀ => D (β P₀)) (by
    refine (D.support.finite_toSet.preimage hβinj.injOn).subset fun P₀ hP₀ => ?_
    simpa [Finsupp.mem_support_iff] using hP₀)
  refine ⟨D₀, fun P₀ P hP => ?_, hD⟩
  rw [primeDivisor_eq_of_closure_eq' hP (hβ P₀)]
  rfl

/-- Base changes are unique. -/
public theorem IsBaseChange.unique {R : Type*} [Zero R]
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) {D₀ : DivisorWithCoeffs R X₀}
    {D D' : DivisorWithCoeffs R X} (hD : IsBaseChange π D₀ D) (hD' : IsBaseChange π D₀ D') :
    D = D' :=
  (eq_iff_of_isBaseChange h hX₀ hD hD').mp rfl

/-- **Cartier divisors are detected over `k₀`.** -/
public theorem isCartier_iff_of_isBaseChange
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) {D₀ : Divisor X₀} {D : Divisor X}
    (hD : IsBaseChange π D₀ D) : D₀.IsCartier ↔ D.IsCartier := by
  constructor
  · intro hc
    obtain ⟨L, hL, hLb, -⟩ := exists_isBaseChange_of_isCartier h hX₀ hc
    rwa [IsBaseChange.unique h hX₀ hD hLb]
  · intro hc
    have : LocallyOfFiniteType s₀ := hX₀.toLocallyOfFiniteType
    have : Surjective π := surjective_of_isPullback h
    have : IsDominant π := inferInstance
    exact isCartier_of_isBaseChange h hD hc

/-- **`ℚ`-Cartier divisors are detected over `k₀`.** -/
public theorem isQCartier_iff_of_isBaseChange
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) {D₀ : QDivisor X₀} {D : QDivisor X}
    (hD : IsBaseChange π D₀ D) : D₀.IsQCartier ↔ D.IsQCartier := by
  constructor
  · rintro ⟨m, hm, L₀, hL₀, hc⟩
    obtain ⟨L, hLc, hLb, -⟩ := exists_isBaseChange_of_isCartier h hX₀ hc
    exact ⟨m, hm, L, (eq_iff_of_isBaseChange h hX₀ hLb.toQDivisor (hD.zsmul m)).mp hL₀, hLc⟩
  · rintro ⟨m, hm, L, hL, hc⟩
    obtain ⟨L₀, hL₀b⟩ := exists_isBaseChange_of_forall h hX₀ (D := L) fun P hP =>
      (hD.zsmul m).2 P (by
        rw [← hL]
        change ((L P : ℤ) : ℚ) ≠ 0
        exact_mod_cast hP)
    exact ⟨m, hm, L₀, (eq_iff_of_isBaseChange h hX₀ hL₀b.toQDivisor (hD.zsmul m)).mpr hL,
      (isCartier_iff_of_isBaseChange h hX₀ hL₀b).mpr hc⟩

/-- Canonical divisors are detected over `k₀`. -/
public theorem exists_isCanonicalDivisor_iff
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) {K₀ : Divisor X₀} {KK : Divisor X}
    (hK : IsBaseChange π K₀ KK) :
    (∃ m : ℕ, K₀.IsCanonicalDivisor s₀ m) ↔ ∃ m : ℕ, KK.IsCanonicalDivisor s m := by
  have : LocallyOfFiniteType s₀ := hX₀.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType s := MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h ‹_›
  haveI : Surjective π := surjective_of_isPullback h
  haveI : IsDominant π := inferInstance
  have hXK := (isProjectiveVariety_iff_of_isPullback _ _ _ h).1 hX₀
  have hdim := topologicalKrullDim_eq_of_isPullback s₀ s π h hX₀
  have hnv₀ : MMP.Mori.IsNormalVariety k₀ s₀ := ⟨hX₀.toIsVariety, inferInstance⟩
  have hnvK : MMP.Mori.IsNormalVariety K s := ⟨hXK.toIsVariety, inferInstance⟩
  constructor
  · rintro ⟨m, hm⟩
    have hn₀ : topologicalKrullDim X₀ = m := hm.1
    obtain ⟨ω₀, ω, hω₀, hω, hb⟩ := exists_topForm_isBaseChange h hnv₀ hn₀
    obtain ⟨φ₀, hφ₀⟩ :=
      MMP.Spreading.CanonExist.linearlyEquivalent_topFormDivisor hnv₀ hn₀ hω₀ hm
    obtain ⟨φ, hφ⟩ := exists_isBaseChange_principalDivisor h φ₀
    have hbc : IsBaseChange π (MMP.Mori.topFormDivisor s₀ ω₀ - K₀)
        (MMP.Mori.topFormDivisor s ω - KK) := by
      simpa only [sub_eq_add_neg] using hb.add hK.neg
    rw [hφ₀] at hbc
    have heq : MMP.Mori.topFormDivisor s ω - KK = principalDivisor φ :=
      IsBaseChange.unique h hX₀ hbc hφ
    exact ⟨m,
      (MMP.Spreading.CanonExist.isCanonicalDivisor_topFormDivisor hnvK (hdim.trans hn₀)
        hω).of_linearlyEquivalent
      (MMP.Mori.Divisor.LinearlyEquivalent.symm
        (⟨φ, heq⟩ : (MMP.Mori.topFormDivisor s ω).LinearlyEquivalent KK))⟩
  · rintro ⟨m, hm⟩
    have hnK : topologicalKrullDim X = m := hm.1
    have hn₀ : topologicalKrullDim X₀ = m := hdim.symm.trans hnK
    haveI : IsProper s₀ :=
      (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp
        ((MMP.Mori.isProjectiveVariety_iff _ _).mp hX₀).2).2
    obtain ⟨ω₀, ω, hω₀, hω, hb⟩ := exists_topForm_isBaseChange h hnv₀ hn₀
    obtain ⟨φ, hφ⟩ := MMP.Spreading.CanonExist.linearlyEquivalent_topFormDivisor hnvK hnK hω hm
    have hbc : IsBaseChange π (MMP.Mori.topFormDivisor s₀ ω₀ - K₀)
        (MMP.Mori.topFormDivisor s ω - KK) := by
      simpa only [sub_eq_add_neg] using hb.add hK.neg
    rw [hφ] at hbc
    obtain ⟨φ₀, hφ₀⟩ := exists_eq_principalDivisor_of_isBaseChange h hbc
    exact ⟨m,
      (MMP.Spreading.CanonExist.isCanonicalDivisor_topFormDivisor hnv₀ hn₀
        hω₀).of_linearlyEquivalent
      (MMP.Mori.Divisor.LinearlyEquivalent.symm
        (⟨φ₀, hφ₀⟩ : (MMP.Mori.topFormDivisor s₀ ω₀).LinearlyEquivalent K₀))⟩

/-- **Pairs are detected over `k₀`.** -/
public theorem isPair_iff_of_isBaseChange
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) {B₀ : QDivisor X₀} {B : QDivisor X}
    (hB : IsBaseChange π B₀ B) : MMP.Mori.IsPair s₀ B₀ ↔ MMP.Mori.IsPair s B := by
  have : LocallyOfFiniteType s₀ := hX₀.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType s := MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h ‹_›
  haveI : Surjective π := surjective_of_isPullback h
  haveI : IsDominant π := inferInstance
  have hXK := (isProjectiveVariety_iff_of_isPullback _ _ _ h).1 hX₀
  have hdim := topologicalKrullDim_eq_of_isPullback s₀ s π h hX₀
  have hnv₀ : MMP.Mori.IsNormalVariety k₀ s₀ := ⟨hX₀.toIsVariety, inferInstance⟩
  have hnvK : MMP.Mori.IsNormalVariety K s := ⟨hXK.toIsVariety, inferInstance⟩
  constructor
  · rintro ⟨-, n, K₀, hK₀, hQ⟩
    have hn₀ : topologicalKrullDim X₀ = n := hK₀.1
    obtain ⟨ω₀, ω, hω₀, hω, hb⟩ := exists_topForm_isBaseChange h hnv₀ hn₀
    have hQ₀ : (Divisor.toQDivisor (MMP.Mori.topFormDivisor s₀ ω₀) + B₀).IsQCartier :=
      MMP.Mori.QDivisor.IsQCartier.add_of_linearlyEquivalent hQ
        (MMP.Spreading.CanonExist.linearlyEquivalent_topFormDivisor hnv₀ hn₀ hω₀ hK₀).symm
    refine ⟨hnvK, n, MMP.Mori.topFormDivisor s ω,
      MMP.Spreading.CanonExist.isCanonicalDivisor_topFormDivisor hnvK (hdim.trans hn₀) hω, ?_⟩
    exact (isQCartier_iff_of_isBaseChange h hX₀ (hb.toQDivisor.add hB)).mp hQ₀
  · rintro ⟨-, n, KK, hKK, hQ⟩
    have hnK : topologicalKrullDim X = n := hKK.1
    have hn₀ : topologicalKrullDim X₀ = n := hdim.symm.trans hnK
    obtain ⟨ω₀, ω, hω₀, hω, hb⟩ := exists_topForm_isBaseChange h hnv₀ hn₀
    have hQK : (Divisor.toQDivisor (MMP.Mori.topFormDivisor s ω) + B).IsQCartier :=
      MMP.Mori.QDivisor.IsQCartier.add_of_linearlyEquivalent hQ
        (MMP.Spreading.CanonExist.linearlyEquivalent_topFormDivisor hnvK hnK hω hKK).symm
    refine ⟨hnv₀, n, MMP.Mori.topFormDivisor s₀ ω₀,
      MMP.Spreading.CanonExist.isCanonicalDivisor_topFormDivisor hnv₀ hn₀ hω₀, ?_⟩
    exact (isQCartier_iff_of_isBaseChange h hX₀ (hb.toQDivisor.add hB)).mpr hQK

/-- Effectivity is detected over `k₀`. -/
public theorem forall_coeff_nonneg_iff_of_isBaseChange
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) {B₀ : QDivisor X₀} {B : QDivisor X}
    (hB : IsBaseChange π B₀ B) :
    (∀ P, 0 ≤ B₀.coeff P) ↔ ∀ P, 0 ≤ B.coeff P :=
  have : LocallyOfFiniteType s₀ := hX₀.toLocallyOfFiniteType
  forall_coeff_iff_of_isBaseChange h hB (p := fun c => 0 ≤ c) le_rfl

/-- **Curve forms are detected over `k₀`.** On the base change `C` of a proper curve `C₀`, the
curve form of the base change of a `ℚ`-Cartier divisor is that of the divisor on `C₀`. -/
public theorem curveForm_numericalClass_eq_of_isBaseChange
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) {D₀ : QDivisor X₀} {D : QDivisor X}
    (hD : IsBaseChange π D₀ D) (hD₀ : D₀.IsQCartier) (hD' : D.IsQCartier)
    (C₀ : ProperCurve s₀) (C : ProperCurve s)
    (hC : closure {C.point} = π.base ⁻¹' closure {C₀.point}) :
    QDivisor.curveForm s D hD' (OneCycle.numericalClass s (C.cycle ℝ)) =
      QDivisor.curveForm s₀ D₀ hD₀ (OneCycle.numericalClass s₀ (C₀.cycle ℝ)) := by
  haveI : QuasiCompact s₀ := hX₀.toQuasiCompact
  haveI : QuasiCompact s := MorphismProperty.of_isPullback h hX₀.toQuasiCompact
  obtain ⟨m, hm, L₀, hL₀, hL₀c⟩ := hD₀.exists_pos
  obtain ⟨L, hLc, hLb, ⟨eL⟩⟩ := exists_isBaseChange_of_isCartier h hX₀ hL₀c
  have hL : Divisor.toQDivisor L = ((m : ℤ) • D) :=
    (eq_iff_of_isBaseChange h hX₀ hLb.toQDivisor (hD.zsmul m)).mp hL₀
  rw [curveForm_numericalClass_cycle, curveForm_numericalClass_cycle,
    QDivisor.intersectionNumber_eq_of_toQDivisor_eq_smul K s C.ι C.dim_le
      (Divisor.degreeOn_add K s C.ι C.dim_le) D hD' hm L hLc hL,
    QDivisor.intersectionNumber_eq_of_toQDivisor_eq_smul k₀ s₀ C₀.ι C₀.dim_le
      (Divisor.degreeOn_add k₀ s₀ C₀.ι C₀.dim_le) D₀ hD₀ hm L₀ hL₀c hL₀]
  haveI := hLc.isInvertibleModule_divisorialSheaf
  haveI := hL₀c.isInvertibleModule_divisorialSheaf
  rw [← ProperCurve.degree_divisorialSheaf C L hLc, ← ProperCurve.degree_divisorialSheaf C₀ L₀ hL₀c,
    degree_congr C eL]
  congr 3
  exact degree_pullback_eq_of_closure_eq s₀ s π h hC _

/-- Negative extremal rays are detected over `k₀`, the ray being transported by `φ`. -/
public theorem isNegativeExtremalRayOf_iff
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) {D₀ : QDivisor X₀} {D : QDivisor X}
    (hD : IsBaseChange π D₀ D)
    (φ : NumericalCurveClasses s₀ →ₗ[ℝ] NumericalCurveClasses s)
    (hφ : ∀ (C₀ : ProperCurve s₀) (C : ProperCurve s),
      closure {C.point} = π.base ⁻¹' closure {C₀.point} →
        φ (OneCycle.numericalClass _ (C₀.cycle ℝ)) = OneCycle.numericalClass _ (C.cycle ℝ))
    (R₀ : Set (NumericalCurveClasses s₀)) :
    IsNegativeExtremalRayOf s₀ D₀ R₀ ↔ IsNegativeExtremalRayOf s D (φ '' R₀) := by
  have hQ := isQCartier_iff_of_isBaseChange h hX₀ hD
  let e := numericalCurveClassesBaseChange s₀ s π h hX₀
  have he := numericalCurveClassesBaseChange_eq_of_isPullback s₀ s π h hX₀
  have hφe : φ = e.toLinearMap := linearMap_ext_numericalClass_cycle s₀ fun C₀ => by
    obtain ⟨C, hC, -⟩ := exists_properCurve_baseChange s₀ s π h C₀
    rw [hφ C₀ C hC, LinearEquiv.coe_coe, he C₀ C hC]
  have hcone : (closedConeOfCurves s : Set (NumericalCurveClasses s)) =
      e '' (closedConeOfCurves s₀ : Set (NumericalCurveClasses s₀)) := by
    rw [← map_closedConeOfCurves_eq_of_isPullback s₀ s π h hX₀ φ hφ, PointedCone.coe_map, hφe,
      LinearEquiv.coe_coe]
  have hRim : φ '' R₀ = e '' R₀ := by rw [hφe, LinearEquiv.coe_coe]
  have hform (hD₀ : D₀.IsQCartier) (hD' : D.IsQCartier) (u : NumericalCurveClasses s₀) :
      QDivisor.curveForm s D hD' (e u) = QDivisor.curveForm s₀ D₀ hD₀ u := by
    refine LinearMap.congr_fun (linearMap_ext_numericalClass_cycle s₀
      (φ := (QDivisor.curveForm s D hD').comp e.toLinearMap)
      (ψ := QDivisor.curveForm s₀ D₀ hD₀) fun C₀ => ?_) u
    obtain ⟨C, hC, -⟩ := exists_properCurve_baseChange s₀ s π h C₀
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, he C₀ C hC]
    exact curveForm_numericalClass_eq_of_isBaseChange h hX₀ hD hD₀ hD' C₀ C hC
  rw [hRim]
  constructor
  · rintro ⟨hD₀, hext, hneg⟩
    refine ⟨hQ.mp hD₀, ?_, ?_⟩
    · rw [hcone]; exact isExtremalRay_image e hext
    · rintro _ ⟨u, hu, rfl⟩ hne
      rw [hform hD₀]
      exact hneg u hu fun h0 => hne (by rw [h0, map_zero])
  · rintro ⟨hD', hext, hneg⟩
    refine ⟨hQ.mpr hD', ?_, ?_⟩
    · rw [hcone] at hext; exact (isExtremalRay_image_iff e).mp hext
    · intro u hu hne
      rw [← hform (hQ.mpr hD') hD']
      exact hneg (e u) ⟨u, hu, rfl⟩ fun h0 => hne (e.injective (h0.trans (map_zero e).symm))

variable {Z₀ Z : Scheme.{u}} {t₀ : Z₀ ⟶ Spec (.of k₀)} {t : Z ⟶ Spec (.of K)} {πZ : Z ⟶ Z₀}

/-- Relative Picard numbers are unchanged by base change: the base-change isomorphism
`N¹(X₀)_ℝ ≃ N¹(X)_ℝ` carries `f₀^* N¹(Z₀)_ℝ` onto `f^* N¹(Z)_ℝ`. -/
public theorem relativePicardNumberN1_eq
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hZ : IsPullback πZ t t₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) (hZ₀ : MMP.Mori.IsProjectiveVariety k₀ t₀)
    (f₀ : X₀ ⟶ Z₀) (f : X ⟶ Z) (hf : f ≫ t = s) (hfπ : f ≫ πZ = π ≫ f₀) :
    relativePicardNumberN1 s₀ f₀ = relativePicardNumberN1 s f := by
  have hZK := (isProjectiveVariety_iff_of_isPullback _ _ _ hZ).1 hZ₀
  have hv₀ : AlgebraicGeometry.IsVariety k₀ t₀ := hZ₀.toIsVariety
  haveI : IsIntegral Z₀ := hv₀.toIsIntegral
  haveI : IsIntegral Z := hZK.toIsVariety.toIsIntegral
  haveI : IsSeparated t := MorphismProperty.of_isPullback hZ hv₀.toIsSeparated
  haveI : LocallyOfFiniteType t := MorphismProperty.of_isPullback hZ hv₀.toLocallyOfFiniteType
  have hφsurj := specMap_mem_surjective_flat_quasiCompact (algebraMap k₀ K)
  haveI : Surjective π := MorphismProperty.of_isPullback (P := @Surjective) h.flip hφsurj.1.1
  haveI : Surjective πZ := MorphismProperty.of_isPullback (P := @Surjective) hZ.flip hφsurj.1.1
  haveI : IsDominant π := inferInstance
  haveI : IsDominant πZ := inferInstance
  let e := numericalDivisorClassesBaseChange s₀ s π h hX₀
  have he := numericalDivisorClassesBaseChange_eq_of_isPullback s₀ s π h hX₀
  let eZ := numericalDivisorClassesBaseChange t₀ t πZ hZ hZ₀
  have heZ := numericalDivisorClassesBaseChange_eq_of_isPullback t₀ t πZ hZ hZ₀
  -- chosen lifts of Cartier divisors
  choose pX hpX using exists_isPullback s₀ s π h hX₀
  choose pZ hpZ using exists_isPullback t₀ t πZ hZ hZ₀
  have hq (G : Z₀.CartierDivisor) := exists_nonempty_iso_cartierDivisor_sheaf
    ((Scheme.Modules.pullback f₀).obj (MMP.CartierDivisor.sheaf G))
  choose q hq using hq
  have hqK (G : Z.CartierDivisor) := exists_nonempty_iso_cartierDivisor_sheaf
    ((Scheme.Modules.pullback f).obj (MMP.CartierDivisor.sheaf G))
  choose qK hqK using hqK
  have hsh (D₀ : X₀.CartierDivisor) : Nonempty (MMP.CartierDivisor.sheaf (pX D₀) ≅
      (Scheme.Modules.pullback π).obj (MMP.CartierDivisor.sheaf D₀)) :=
    ⟨(nonempty_pullback_sheaf_iso π (hpX D₀)).some.symm⟩
  have hshZ (G : Z₀.CartierDivisor) : Nonempty (MMP.CartierDivisor.sheaf (pZ G) ≅
      (Scheme.Modules.pullback πZ).obj (MMP.CartierDivisor.sheaf G)) :=
    ⟨(nonempty_pullback_sheaf_iso πZ (hpZ G)).some.symm⟩
  -- `f^* πZ^* = π^* f₀^*`
  have hcomm (M : Z₀.Modules) : (Scheme.Modules.pullback f).obj
      ((Scheme.Modules.pullback πZ).obj M) ≅
        (Scheme.Modules.pullback π).obj ((Scheme.Modules.pullback f₀).obj M) :=
    (Scheme.Modules.pullbackComp f πZ).app M ≪≫ (Scheme.Modules.pullbackCongr hfπ).app M ≪≫
      ((Scheme.Modules.pullbackComp π f₀).app M).symm
  have hcomp : e.toLinearMap ∘ₗ numericalDivisorClass s₀ =
      numericalDivisorClass s ∘ₗ Finsupp.lmapDomain ℝ ℝ pX := by
    ext D₀
    simpa [KCartierDivisor.ofCartier] using he D₀ (pX D₀) (hpX D₀)
  -- the classes of the lifts `q c₀` lie in `f₀^* N¹(Z₀)`
  have h4 (c₀ : KCartierDivisor ℝ Z₀) : numericalDivisorClass s₀ (Finsupp.lmapDomain ℝ ℝ q c₀) ∈
      pullbackNumericalClasses s₀ f₀ := by
    induction c₀ using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add]; exact Submodule.add_mem _ ha hb
    | single G r =>
      rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, ← mul_one r, ← smul_eq_mul,
        ← Finsupp.smul_single, map_smul]
      exact Submodule.smul_mem _ r (Submodule.subset_span ⟨q G,
        MMP.CartierDivisor.sheaf G, inferInstance, ⟨(hq G).some.symm⟩, rfl⟩)
  have key : (pullbackNumericalClasses s₀ f₀).map e.toLinearMap = pullbackNumericalClasses s f := by
    apply le_antisymm
    · rw [pullbackNumericalClasses, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨E₀, M₀, hM₀, ⟨σ⟩, rfl⟩, rfl⟩
      refine Submodule.subset_span ⟨pX E₀, (Scheme.Modules.pullback πZ).obj M₀, inferInstance,
        ⟨(hsh E₀).some ≪≫ (Scheme.Modules.pullback π).mapIso σ ≪≫ (hcomm M₀).symm⟩,
        he E₀ (pX E₀) (hpX E₀)⟩
    · rw [pullbackNumericalClasses, Submodule.span_le]
      rintro _ ⟨E, M, hM, ⟨σ⟩, rfl⟩
      obtain ⟨EM, ⟨τ⟩⟩ := exists_nonempty_iso_cartierDivisor_sheaf M
      obtain ⟨c₀, hc₀⟩ := exists_numericalDivisorClass_eq_lmapDomain pZ eZ
        (fun G => heZ G (pZ G) (hpZ G)) (KCartierDivisor.ofCartier ℝ EM)
      -- `[E] = [qK EM]`
      have hlm (p : Z.CartierDivisor → X.CartierDivisor) (G : Z.CartierDivisor) :
          Finsupp.lmapDomain ℝ ℝ p (KCartierDivisor.ofCartier ℝ G) =
            KCartierDivisor.ofCartier ℝ (p G) := by
        simp [KCartierDivisor.ofCartier, Finsupp.lmapDomain_apply]
      have h1 : numericalDivisorClass s (KCartierDivisor.ofCartier ℝ E) =
          numericalDivisorClass s (Finsupp.lmapDomain ℝ ℝ qK (KCartierDivisor.ofCartier ℝ EM)) := by
        rw [hlm]
        refine numericalDivisorClass_eq_of_forall fun C => ?_
        rw [intersectionNumber_cycle_ofCartier, intersectionNumber_cycle_ofCartier,
          degree_congr C (σ ≪≫ (Scheme.Modules.pullback f).mapIso τ ≪≫ (hqK EM).some)]
      -- `[qK EM] = [qK (pZ c₀)]`
      have h2 := numericalDivisorClass_lmapDomain_eq_of_forall f hf qK
        (fun G => ⟨(hqK G).some.symm⟩) (intersectionNumber_eq_of_numericalDivisorClass_eq' hc₀)
      -- `[qK (pZ c₀)] = [pX (q c₀)]`
      have h3 : numericalDivisorClass s (Finsupp.lmapDomain ℝ ℝ qK
            (Finsupp.lmapDomain ℝ ℝ pZ c₀)) =
          numericalDivisorClass s (Finsupp.lmapDomain ℝ ℝ pX (Finsupp.lmapDomain ℝ ℝ q c₀)) := by
        have e1 : Finsupp.lmapDomain ℝ ℝ qK (Finsupp.lmapDomain ℝ ℝ pZ c₀) =
            Finsupp.lmapDomain ℝ ℝ (qK ∘ pZ) c₀ := by
          simp only [Finsupp.lmapDomain_apply]; exact Finsupp.mapDomain_comp.symm
        have e2 : Finsupp.lmapDomain ℝ ℝ pX (Finsupp.lmapDomain ℝ ℝ q c₀) =
            Finsupp.lmapDomain ℝ ℝ (pX ∘ q) c₀ := by
          simp only [Finsupp.lmapDomain_apply]; exact Finsupp.mapDomain_comp.symm
        rw [e1, e2]
        exact numericalDivisorClass_lmapDomain_eq _ _ (fun G =>
          ⟨(hqK (pZ G)).some.symm ≪≫ (Scheme.Modules.pullback f).mapIso (hshZ G).some ≪≫
            hcomm _ ≪≫ (Scheme.Modules.pullback π).mapIso (hq G).some ≪≫
            (hsh (q G)).some.symm⟩) c₀
      refine ⟨_, h4 c₀, ?_⟩
      change e.toLinearMap _ = _
      rw [← LinearMap.comp_apply, hcomp, LinearMap.comp_apply, ← h3, ← h2, h1]
  unfold relativePicardNumberN1
  exact congrArg Cardinal.toENat
    (Submodule.Quotient.equiv _ _ e key).rank_eq

/-- Relatively ample multiples are detected over `k₀`. -/
public theorem hasRelativelyAmpleMultiple_iff
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hZ : IsPullback πZ t t₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) (hZ₀ : MMP.Mori.IsProjectiveVariety k₀ t₀)
    (f₀ : X₀ ⟶ Z₀) (hf₀ : f₀ ≫ t₀ = s₀) (f : X ⟶ Z) (hf : f ≫ t = s)
    (hfπ : f ≫ πZ = π ≫ f₀) {D₀ : QDivisor X₀} {D : QDivisor X} (hD : IsBaseChange π D₀ D) :
    D₀.HasRelativelyAmpleMultiple f₀ ↔ D.HasRelativelyAmpleMultiple f := by
  have hsq := isPullback_of_isPullback_comp h hZ hf₀ hf hfπ
  have hZK := (isProjectiveVariety_iff_of_isPullback _ _ _ hZ).1 hZ₀
  have hXK := (isProjectiveVariety_iff_of_isPullback _ _ _ h).1 hX₀
  haveI : IsProper f₀ := isProper_of_comp_eq hX₀ hZ₀ hf₀
  haveI : IsProper f := isProper_of_comp_eq hXK hZK hf
  have hφsurj := specMap_mem_surjective_flat_quasiCompact (algebraMap k₀ K)
  haveI : Flat πZ := MorphismProperty.of_isPullback (P := @Flat) hZ.flip hφsurj.1.2
  haveI : Surjective πZ := MorphismProperty.of_isPullback (P := @Surjective) hZ.flip hφsurj.1.1
  haveI : QuasiCompact πZ := MorphismProperty.of_isPullback (P := @QuasiCompact) hZ.flip hφsurj.2
  have hamp (L₀ : Divisor X₀) (hL₀ : L₀.IsCartier) (L : Divisor X) (hL : L.IsCartier)
      (e : L.divisorialSheaf ≅ (Scheme.Modules.pullback π).obj L₀.divisorialSheaf) :
      L₀.IsRelativelyAmple f₀ hL₀ ↔ L.IsRelativelyAmple f hL := by
    haveI := hL₀.isInvertibleModule_divisorialSheaf
    haveI := hL.isInvertibleModule_divisorialSheaf
    exact isRelativelyAmple_iff_of_isPullback hsq _ _ e
  constructor
  · rintro ⟨m, hm, L₀, hL₀c, hL₀, hA⟩
    obtain ⟨L, hLc, hLb, ⟨eL⟩⟩ := exists_isBaseChange_of_isCartier h hX₀ hL₀c
    exact ⟨m, hm, L, hLc, (eq_iff_of_isBaseChange h hX₀ hLb.toQDivisor (hD.zsmul m)).mp hL₀,
      (hamp L₀ hL₀c L hLc eL).mp hA⟩
  · rintro ⟨m, hm, L, hLc, hL, hA⟩
    obtain ⟨L₀, hL₀b⟩ := exists_isBaseChange_of_forall h hX₀ (D := L) fun P hP =>
      (hD.zsmul m).2 P (by
        rw [← hL]
        change ((L P : ℤ) : ℚ) ≠ 0
        exact_mod_cast hP)
    have hL₀c := (isCartier_iff_of_isBaseChange h hX₀ hL₀b).mpr hLc
    obtain ⟨L', hL'c, hL'b, ⟨eL'⟩⟩ := exists_isBaseChange_of_isCartier h hX₀ hL₀c
    obtain rfl := IsBaseChange.unique h hX₀ hL'b hL₀b
    exact ⟨m, hm, L₀, hL₀c, (eq_iff_of_isBaseChange h hX₀ hL₀b.toQDivisor (hD.zsmul m)).mpr hL,
      (hamp L₀ hL₀c L' hL'c eL').mpr hA⟩

/-- Birational morphisms are detected over `k₀`. -/
public theorem isBirationalMorphism_iff
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hZ : IsPullback πZ t t₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) (hZ₀ : MMP.Mori.IsProjectiveVariety k₀ t₀)
    [IsNormal Z₀] (f₀ : X₀ ⟶ Z₀) (hf₀ : f₀ ≫ t₀ = s₀) (f : X ⟶ Z) (hf : f ≫ t = s)
    (hfπ : f ≫ πZ = π ≫ f₀) :
    IsBirationalMorphism f₀ ↔ IsBirationalMorphism f := by
  have hsq := isPullback_of_isPullback_comp h hZ hf₀ hf hfπ
  have hZK := (isProjectiveVariety_iff_of_isPullback _ _ _ hZ).1 hZ₀
  have hXK := (isProjectiveVariety_iff_of_isPullback _ _ _ h).1 hX₀
  have : IsIntegral Z₀ := hZ₀.toIsIntegral
  have : IsIntegral Z := hZK.toIsIntegral
  have : LocallyOfFiniteType t₀ := hZ₀.toLocallyOfFiniteType
  have : IsNormal Z := (invariants_of_isPullback t₀ hZ).1.1 ‹_›
  have : IsProper f₀ := isProper_of_comp_eq hX₀ hZ₀ hf₀
  have : IsProper f := isProper_of_comp_eq hXK hZK hf
  have : Surjective πZ := surjective_of_isPullback hZ
  rw [isBirationalMorphism_iff_isIso_fiberToSpecResidueField f₀,
    isBirationalMorphism_iff_isIso_fiberToSpecResidueField f,
    isIso_fiberToSpecResidueField_iff_of_isPullback hsq,
      AlgebraicGeometry.map_genericPoint_of_isDominant πZ]

/-- Small morphisms are detected over `k₀`. -/
public theorem isSmallMorphism_iff
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hZ : IsPullback πZ t t₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) (hZ₀ : MMP.Mori.IsProjectiveVariety k₀ t₀)
    (f₀ : X₀ ⟶ Z₀) (hf₀ : f₀ ≫ t₀ = s₀) (f : X ⟶ Z) (hf : f ≫ t = s)
    (hfπ : f ≫ πZ = π ≫ f₀) :
    IsSmallMorphism s₀ t₀ f₀ ↔ IsSmallMorphism s t f := by
  have hsq := isPullback_of_isPullback_comp h hZ hf₀ hf hfπ
  have hZK := (isProjectiveVariety_iff_of_isPullback _ _ _ hZ).1 hZ₀
  have hXK := (isProjectiveVariety_iff_of_isPullback _ _ _ h).1 hX₀
  have : IsIntegral Z₀ := hZ₀.toIsIntegral
  have : IsIntegral Z := hZK.toIsIntegral
  have : LocallyOfFiniteType t₀ := hZ₀.toLocallyOfFiniteType
  have : LocallyOfFiniteType s₀ := hX₀.toLocallyOfFiniteType
  have : LocallyOfFiniteType s := hXK.toLocallyOfFiniteType
  have : IsProper f₀ := isProper_of_comp_eq hX₀ hZ₀ hf₀
  have : IsProper f := isProper_of_comp_eq hXK hZK hf
  have : Surjective π := surjective_of_isPullback h
  have hnor := (invariants_of_isPullback t₀ hZ).1
  have hcod : IsNormal Z₀ → IsBirationalMorphism f₀ → IsBirationalMorphism f →
      (2 ≤ closedsCodimension (exceptionalSet f₀) ↔ 2 ≤ closedsCodimension (exceptionalSet f)) :=
    fun _ hb hb' => by
      have : IsNormal Z := hnor.1 ‹_›
      exact (le_closedsCodimension_iff_of_isPullback s₀ h 2 _ _
        (coe_exceptionalSet_eq_preimage_of_isPullback hsq hb hb')).symm
  constructor
  · intro H
    have : IsNormal Z₀ := H.isNormalVariety_target.2
    have hb := H.isBirationalMorphism
    have hb' := (isBirationalMorphism_iff h hZ hX₀ hZ₀ f₀ hf₀ f hf hfπ).1 hb
    exact
      { isNormalVariety_source := isNormalVariety_of_isPullback s₀ h H.isNormalVariety_source
        isNormalVariety_target := isNormalVariety_of_isPullback t₀ hZ H.isNormalVariety_target
        comp_eq := hf
        isProper := inferInstance
        isBirationalMorphism := hb'
        two_le_codimension := (hcod ‹_› hb hb').1 H.two_le_codimension }
  · intro H
    have : IsNormal Z₀ := hnor.2 H.isNormalVariety_target.2
    have hb' := H.isBirationalMorphism
    have hb := (isBirationalMorphism_iff h hZ hX₀ hZ₀ f₀ hf₀ f hf hfπ).2 hb'
    exact
      { isNormalVariety_source := ⟨hX₀.toIsVariety, ‹_›⟩
        isNormalVariety_target := ⟨hZ₀.toIsVariety, ‹_›⟩
        comp_eq := hf₀
        isProper := inferInstance
        isBirationalMorphism := hb
        two_le_codimension := (hcod ‹_› hb hb').2 H.two_le_codimension }

/-- Projective morphisms are detected over `k₀`. -/
public theorem isProjectiveMorphism_iff
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hZ : IsPullback πZ t t₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) (hZ₀ : MMP.Mori.IsProjectiveVariety k₀ t₀)
    (f₀ : X₀ ⟶ Z₀) (hf₀ : f₀ ≫ t₀ = s₀) (f : X ⟶ Z) (hf : f ≫ t = s)
    (hfπ : f ≫ πZ = π ≫ f₀) :
    IsProjectiveMorphism f₀ ↔ IsProjectiveMorphism f := by
  have hsq := isPullback_of_isPullback_comp h hZ hf₀ hf hfπ
  constructor
  · intro hp
    have := IsProjectiveMorphism.iso_comp hsq.isoPullback (hp.baseChange πZ)
    rwa [hsq.isoPullback_hom_snd] at this
  · intro hp
    have hY : Stacks.HProjective.IsQuasiProjective t₀ :=
      (isQuasiProjective_iff_hProjectiveIsQuasiProjective _).mp
        ((MMP.Mori.isProjectiveVariety_iff _ _).mp hZ₀).2.isQuasiProjective
    have : LocallyOfFiniteType (f₀ ≫ t₀) := by rw [hf₀]; exact hX₀.toLocallyOfFiniteType
    have : QuasiCompact (f₀ ≫ t₀) := by rw [hf₀]; exact hX₀.toQuasiCompact
    haveI := Stacks.Ample.isInvertibleModule_unit X₀
    refine (MMP.isRelativelyAmple_iff_and_isProjectiveMorphism_iff_of_fieldExtension k₀ K
      t₀ f₀ hY (Stacks.Ample.unitModule X₀)).2.2 ?_
    obtain ⟨e, eZ, he, -, -⟩ := exists_iso_pullback_of_isPullback hsq hZ
    exact IsProjectiveMorphism.of_iso e eZ he hp

/-- Contractions of rays are detected over `k₀`. -/
public theorem isContractionOfRay_iff
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hZ : IsPullback πZ t t₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) (hZ₀ : MMP.Mori.IsProjectiveVariety k₀ t₀)
    (f₀ : X₀ ⟶ Z₀) (hf₀ : f₀ ≫ t₀ = s₀) (f : X ⟶ Z) (hf : f ≫ t = s)
    (hfπ : f ≫ πZ = π ≫ f₀)
    (φ : NumericalCurveClasses s₀ →ₗ[ℝ] NumericalCurveClasses s)
    (hφ : ∀ (C₀ : ProperCurve s₀) (C : ProperCurve s),
      closure {C.point} = π.base ⁻¹' closure {C₀.point} →
        φ (OneCycle.numericalClass _ (C₀.cycle ℝ)) = OneCycle.numericalClass _ (C.cycle ℝ))
    (R₀ : Set (NumericalCurveClasses s₀)) :
    IsContractionOfRay s₀ t₀ R₀ f₀ ↔ IsContractionOfRay s t (φ '' R₀) f := by
  have hsq := isPullback_of_isPullback_comp h hZ hf₀ hf hfπ
  have hZK := (isProjectiveVariety_iff_of_isPullback _ _ _ hZ).1 hZ₀
  have hv₀ : AlgebraicGeometry.IsVariety k₀ t₀ := hZ₀.toIsVariety
  haveI : IsSeparated t := MorphismProperty.of_isPullback hZ hv₀.toIsSeparated
  haveI : LocallyOfFiniteType t := MorphismProperty.of_isPullback hZ hv₀.toLocallyOfFiniteType
  haveI : IsSeparated t₀ := hv₀.toIsSeparated
  haveI : LocallyOfFiniteType t₀ := hv₀.toLocallyOfFiniteType
  haveI : QuasiCompact t₀ := hv₀.toQuasiCompact
  haveI : QuasiCompact t := MorphismProperty.of_isPullback hZ hv₀.toQuasiCompact
  haveI : LocallyOfFiniteType s₀ := hX₀.toLocallyOfFiniteType
  haveI : QuasiCompact s₀ := hX₀.toQuasiCompact
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace t
  haveI : IsAffineHom πZ := MorphismProperty.of_isPullback hZ.flip inferInstance
  haveI : IsProper f₀ := isProper_of_comp_eq hX₀ hZ₀ hf₀
  have hφsurj := specMap_mem_surjective_flat_quasiCompact (algebraMap k₀ K)
  haveI : Surjective πZ := MorphismProperty.of_isPullback (P := @Surjective) hZ.flip hφsurj.1.1
  -- an ample invertible sheaf `H` on `Z₀`, whose pull-back `H_K` to `Z` is ample
  obtain ⟨H, _, hHa⟩ := exists_isAmple_of_isProjectiveVariety hZ₀
  have hHKa : Scheme.Modules.IsAmple Z ((Scheme.Modules.pullback πZ).obj H) :=
    Scheme.Modules.isAmple_pullback_of_isAffineHom πZ H hHa
  have hdegH {C₀ : ProperCurve s₀} {C : ProperCurve s}
      (hC : closure {C.point} = π.base ⁻¹' closure {C₀.point}) :
      C.degree K ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback πZ).obj H)) =
        C₀.degree k₀ ((Scheme.Modules.pullback f₀).obj H) := by
    have e : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback πZ).obj H) ≅
        (Scheme.Modules.pullback π).obj ((Scheme.Modules.pullback f₀).obj H) :=
      (Scheme.Modules.pullbackComp f πZ).app H ≪≫ (Scheme.Modules.pullbackCongr hfπ).app H ≪≫
        ((Scheme.Modules.pullbackComp π f₀).app H).symm
    rw [degree_congr C e]
    exact degree_pullback_eq_of_closure_eq s₀ s π h hC _
  -- contraction is read off the degree of `f^* H_K`
  have hcontrK (C : ProperCurve s) : C.IsContractedBy f ↔
      C.degree K ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback πZ).obj H)) = 0 :=
    ⟨fun hc => ProperCurve.degree_pullback_eq_zero_of_isContractedBy f hf C hc _,
      fun h0 => isContractedBy_of_degree_pullback_eq_zero f hf _ hHKa C h0⟩
  have hcontr {C₀ : ProperCurve s₀} {C : ProperCurve s}
      (hC : closure {C.point} = π.base ⁻¹' closure {C₀.point}) :
      C₀.IsContractedBy f₀ ↔ C.IsContractedBy f := by
    rw [hcontrK, hdegH hC]
    exact ⟨fun hc => ProperCurve.degree_pullback_eq_zero_of_isContractedBy f₀ hf₀ C₀ hc H,
      fun h0 => isContractedBy_of_degree_pullback_eq_zero f₀ hf₀ H hHa C₀ h0⟩
  have hinj : Function.Injective φ := injective_of_map_numericalClass s₀ s π h φ hφ
  -- the contraction conditions
  have hpush := (MMP.Foundations.isPushout_app_pullbackMap_and_isIso_app_iff (K := K) s₀ t₀ f₀
    hf₀).2
  obtain ⟨eX, heX⟩ : ∃ eX : X ≅ pullback s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))),
      eX.hom ≫ pullback.fst _ _ = π ∧ eX.hom ≫ pullback.snd _ _ = s :=
    ⟨h.isoPullback, h.isoPullback_hom_fst, h.isoPullback_hom_snd⟩
  have hw : eX.hom ≫ pullback.map s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) t₀
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) f₀ (𝟙 _) (𝟙 _) (by simp [hf₀])
      (by simp) = f ≫ hZ.isoPullback.hom := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, heX.1, Category.assoc,
        hZ.isoPullback_hom_fst, hfπ]
    · rw [Category.assoc, pullback.lift_snd, Category.comp_id, heX.2, Category.assoc,
        hZ.isoPullback_hom_snd, hf]
  have hiso : (∀ U : Z₀.Opens, IsIso (f₀.app U)) ↔ ∀ U : Z.Opens, IsIso (f.app U) := by
    rw [hpush]
    exact ⟨fun H U => forall_isIso_app_of_iso eX.symm hZ.isoPullback.symm (by
        rw [Iso.symm_hom, Iso.symm_hom, Iso.eq_comp_inv, Category.assoc, ← hw,
          Iso.inv_hom_id_assoc]) H U,
      fun H U => forall_isIso_app_of_iso eX hZ.isoPullback hw H U⟩
  have hproj := isProjectiveMorphism_iff h hZ hX₀ hZ₀ f₀ hf₀ f hf hfπ
  have hnor := (invariants_of_isPullback t₀ hZ).1
  constructor
  · intro H₀
    refine
      { isNormalVariety_source := isNormalVariety_of_isPullback s₀ h H₀.isNormalVariety_source
        isNormalVariety_target := isNormalVariety_of_isPullback t₀ hZ H₀.isNormalVariety_target
        comp_eq := hf
        isProjectiveMorphism := hproj.1 H₀.isProjectiveMorphism
        surjective := ?_
        isIso_app := hiso.1 H₀.isIso_app
        isContractedBy_iff := fun C => ?_ }
    · haveI : Surjective f₀ := ⟨H₀.surjective⟩
      exact (MorphismProperty.of_isPullback (P := @Surjective) hsq ‹_›).surj
    · obtain ⟨C₀, C₀K, hcl, hcls, hdeg⟩ := exists_properCurve_numericalClass_eq h hX₀ C
      rw [hcontrK, ← hdeg, ← hcontrK, ← hcontr hcl, H₀.isContractedBy_iff C₀, ← hcls,
        ← hφ C₀ C₀K hcl, hinj.mem_set_image]
  · intro H
    refine
      { isNormalVariety_source := ⟨hX₀.toIsVariety, inferInstance⟩
        isNormalVariety_target := ⟨hZ₀.toIsVariety, hnor.2 H.isNormalVariety_target.2⟩
        comp_eq := hf₀
        isProjectiveMorphism := hproj.2 H.isProjectiveMorphism
        surjective := fun z₀ => ?_
        isIso_app := hiso.2 H.isIso_app
        isContractedBy_iff := fun C₀ => ?_ }
    · obtain ⟨z, rfl⟩ := πZ.surjective z₀
      obtain ⟨x, rfl⟩ := H.surjective z
      exact ⟨π x, by rw [← Scheme.Hom.comp_apply, ← hfπ, Scheme.Hom.comp_apply]⟩
    · obtain ⟨C, hC, -⟩ := exists_properCurve_baseChange s₀ s π h C₀
      rw [hcontr hC, H.isContractedBy_iff C, ← hφ C₀ C hC, hinj.mem_set_image]

variable {X'₀ X' : Scheme.{u}} [IsIntegral X'₀] [CompactSpace X'₀] [IsLocallyNoetherian X'₀]
  [IsNormal X'₀] [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
  {s'₀ : X'₀ ⟶ Spec (.of k₀)} {s' : X' ⟶ Spec (.of K)} {π' : X' ⟶ X'₀}

/-- Strict transforms through `X ⟶ Z ⟵ X'` commute with base change. -/
public theorem isBaseChange_flipTransform {R : Type*} [AddCommMonoid R]
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hZ : IsPullback πZ t t₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (h' : IsPullback π' s' s'₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) (hZ₀ : MMP.Mori.IsProjectiveVariety k₀ t₀)
    (hX'₀ : MMP.Mori.IsProjectiveVariety k₀ s'₀) [IsNormal Z₀]
    (f₀ : X₀ ⟶ Z₀) (hf₀ : f₀ ≫ t₀ = s₀) (f : X ⟶ Z) (hf : f ≫ t = s)
    (hfπ : f ≫ πZ = π ≫ f₀)
    (fp₀ : X'₀ ⟶ Z₀) (hfp₀ : fp₀ ≫ t₀ = s'₀) (fp : X' ⟶ Z) (hfp : fp ≫ t = s')
    (hfpπ : fp ≫ πZ = π' ≫ fp₀)
    (hbp₀ : IsBirationalMorphism fp₀)
    {D₀ : DivisorWithCoeffs R X₀} {D : DivisorWithCoeffs R X} (hD : IsBaseChange π D₀ D) :
    IsBaseChange π' (flipTransform f₀ fp₀ D₀) (flipTransform f fp D) := by
  have hsq := isPullback_of_isPullback_comp h hZ hf₀ hf hfπ
  have hsq' := isPullback_of_isPullback_comp h' hZ hfp₀ hfp hfpπ
  have hZK := (isProjectiveVariety_iff_of_isPullback _ _ _ hZ).1 hZ₀
  have hXK := (isProjectiveVariety_iff_of_isPullback _ _ _ h).1 hX₀
  have hX'K := (isProjectiveVariety_iff_of_isPullback _ _ _ h').1 hX'₀
  have : IsIntegral Z₀ := hZ₀.toIsIntegral
  have : IsIntegral Z := hZK.toIsIntegral
  have : LocallyOfFiniteType t₀ := hZ₀.toLocallyOfFiniteType
  have : LocallyOfFiniteType s₀ := hX₀.toLocallyOfFiniteType
  have : LocallyOfFiniteType s'₀ := hX'₀.toLocallyOfFiniteType
  have : IsNormal Z := (invariants_of_isPullback t₀ hZ).1.1 ‹_›
  have : IsProper f₀ := isProper_of_comp_eq hX₀ hZ₀ hf₀
  have : IsProper f := isProper_of_comp_eq hXK hZK hf
  have : IsProper fp₀ := isProper_of_comp_eq hX'₀ hZ₀ hfp₀
  have : IsProper fp := isProper_of_comp_eq hX'K hZK hfp
  have hφsurj := (specMap_mem_surjective_flat_quasiCompact (algebraMap k₀ K)).1.1
  have : Surjective π := MorphismProperty.of_isPullback (P := @Surjective) h.flip hφsurj
  have : Surjective π' := MorphismProperty.of_isPullback (P := @Surjective) h'.flip hφsurj
  have : Surjective πZ := MorphismProperty.of_isPullback (P := @Surjective) hZ.flip hφsurj
  have : IsSeparated t := hZK.toIsSeparated
  have : IsSeparated t₀ := hZ₀.toIsSeparated
  have : IsSeparated (Z ↘ ⊤_ Scheme) := by
    rw [show (Z ↘ ⊤_ Scheme) = t ≫ (Spec (.of K) ↘ ⊤_ Scheme) from Subsingleton.elim _ _]
    infer_instance
  have : IsSeparated (Z₀ ↘ ⊤_ Scheme) := by
    rw [show (Z₀ ↘ ⊤_ Scheme) = t₀ ≫ (Spec (.of k₀) ↘ ⊤_ Scheme) from Subsingleton.elim _ _]
    infer_instance
  have hbp := (isBirationalMorphism_iff h' hZ hX'₀ hZ₀ fp₀ hfp₀ fp hfp hfpπ).1 hbp₀
  have : IsDominant fp₀ := hbp₀.isDominant
  -- the biregular locus of `fp` is the preimage of that of `fp₀`
  have : LocallyOfFiniteType fp₀ := locallyOfFiniteType_of_comp fp₀ t₀
  have hV (z : Z) : z ∈ MMP.Mori.biregularLocus fp ↔ πZ z ∈ MMP.Mori.biregularLocus fp₀ := by
    rw [← SetLike.mem_coe, coe_biregularLocus_eq_finiteFibreLocus fp hbp, ← SetLike.mem_coe,
      coe_biregularLocus_eq_finiteFibreLocus fp₀ hbp₀]
    exact finite_preimage_singleton_iff_of_isPullback hsq' z
  -- points with base-changed closures
  have heq {w w' : Z} {x x' : Z₀} (hw : closure {w} = πZ.base ⁻¹' closure {x})
      (hw' : closure {w'} = πZ.base ⁻¹' closure {x'}) : w = w' ↔ x = x' := by
    constructor
    · rintro rfl
      exact (inseparable_iff_closure_eq.mpr
        ((Set.preimage_injective.mpr πZ.surjective) (hw.symm.trans hw'))).eq
    · rintro rfl
      exact (inseparable_iff_closure_eq.mpr (hw.trans hw'.symm)).eq
  have hcoh (E : MMP.Mori.PrimeDivisor Z) : E.genericPoint ≠ genericPoint Z := by
    intro he
    have h1 : Order.coheight E.genericPoint = 1 := MMP.Mori.PrimeDivisor.coheight_genericPoint E
    rw [he, Stacks.EtaleCohomology.coheight_genericPoint_eq_zero] at h1
    exact zero_ne_one h1
  have hcoh₀ (E : MMP.Mori.PrimeDivisor Z₀) : E.genericPoint ≠ genericPoint Z₀ := by
    intro he
    have h1 : Order.coheight E.genericPoint = 1 := MMP.Mori.PrimeDivisor.coheight_genericPoint E
    rw [he, Stacks.EtaleCohomology.coheight_genericPoint_eq_zero] at h1
    exact zero_ne_one h1
  have hexX : ∀ P₀ : MMP.Mori.PrimeDivisor X₀, ∃ P : MMP.Mori.PrimeDivisor X,
      closure {P.genericPoint} = π.base ⁻¹' closure {P₀.genericPoint} :=
    fun P₀ => (exists_primeDivisor_baseChange h P₀).imp fun _ hP => hP.1
  have hexZ : ∀ P₀ : MMP.Mori.PrimeDivisor Z₀, ∃ P : MMP.Mori.PrimeDivisor Z,
      closure {P.genericPoint} = πZ.base ⁻¹' closure {P₀.genericPoint} :=
    fun P₀ => (exists_primeDivisor_baseChange hZ P₀).imp fun _ hP => hP.1
  -- the transform under `f`
  have step1 : IsBaseChange πZ (MMP.Mori.RationalMap.transformDivisor f₀.toRationalMap D₀)
      (MMP.Mori.RationalMap.transformDivisor f.toRationalMap D) := by
    refine IsBaseChange.mapPrimeDivisors hexX (fun P₀ P hP F₀ F hF => ?_)
      (fun P₀ P hP F hPF => ?_) hD
    · rw [MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff,
        MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff, eq_comm (a := f₀ _),
        eq_comm (a := f _)]
      exact heq hF (closure_singleton_map_eq hsq f.isClosedMap f₀.isClosedMap hP)
    · rw [MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff, eq_comm] at hPF
      refine exists_closure_eq_of_map_ne_genericPoint hZ F fun hgen => ?_
      have hc := closure_singleton_map_eq hsq f.isClosedMap f₀.isClosedMap hP
      have h1 : πZ F.genericPoint = f₀ P₀.genericPoint := by
        rw [hPF, ← Scheme.Hom.comp_apply, hfπ, Scheme.Hom.comp_apply,
          map_eq_of_closure_eq hP]
      rw [h1] at hgen
      rw [hgen, (genericPoint_spec Z₀).def, Set.preimage_univ, ← hPF] at hc
      exact hcoh F ((genericPoint_spec Z).eq (isGenericPoint_def.mpr hc)).symm
  -- the inverse transform under `fp`
  have step2 := IsBaseChange.mapPrimeDivisors hexZ (πY := π')
    (φ₀ := MMP.Mori.inverseTransformPrimeDivisor fp₀)
    (φ := MMP.Mori.inverseTransformPrimeDivisor fp) (fun E₀ E hE F₀ F hF => ?_)
    (fun E₀ E hE F hEF => ?_) step1
  · exact step2
  · rw [inverseTransformPrimeDivisor_eq_some_iff', inverseTransformPrimeDivisor_eq_some_iff',
      hV, map_eq_of_closure_eq hE]
    exact and_congr_right fun _ =>
      heq (closure_singleton_map_eq hsq' fp.isClosedMap fp₀.isClosedMap hF) hE
  · obtain ⟨-, hFE⟩ := (inverseTransformPrimeDivisor_eq_some_iff' fp E F).mp hEF
    refine exists_closure_eq_of_map_ne_genericPoint h' F fun hgen => ?_
    have h1 : fp₀ (π' F.genericPoint) = E₀.genericPoint := by
      rw [← Scheme.Hom.comp_apply, ← hfpπ, Scheme.Hom.comp_apply, hFE, map_eq_of_closure_eq hE]
    rw [hgen, map_genericPoint_of_isDominant] at h1
    exact hcoh₀ E₀ h1.symm

/-- **Base change of a log resolution.** A projective log resolution `μ₀ : W₀ ⟶ X₀` of
`(X₀, B₀)` (Hironaka) base changes to a projective log resolution `μ : W ⟶ X` of `(X, B)`: smooth,
proper, projective and birational morphisms are stable under the base change, the exceptional set
of `μ` is the preimage of that of `μ₀`, and snc subsets correspond. -/
public theorem exists_isLogResolution_isPullback [CharZero k₀]
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) {B₀ : QDivisor X₀} {B : QDivisor X}
    (hB : IsBaseChange π B₀ B) :
    ∃ (W₀ W : Scheme.{u}) (μ₀ : W₀ ⟶ X₀) (μ : W ⟶ X) (πW : W ⟶ W₀),
      IsPullback πW (μ ≫ s) (μ₀ ≫ s₀) (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) ∧
      μ ≫ π = πW ≫ μ₀ ∧ MMP.Mori.IsProjectiveVariety k₀ (μ₀ ≫ s₀) ∧ Smooth (μ₀ ≫ s₀) ∧
      MMP.Fourfold.IsLogResolution s₀ B₀ μ₀ ∧ MMP.Fourfold.IsLogResolution s B μ := by
  classical
  set φ := Spec.map (CommRingCat.ofHom (algebraMap k₀ K))
  have : LocallyOfFiniteType s₀ := hX₀.toLocallyOfFiniteType
  have : QuasiCompact s₀ := hX₀.toQuasiCompact
  have hnv₀ : MMP.Mori.IsNormalVariety k₀ s₀ := ⟨hX₀.toIsVariety, inferInstance⟩
  have hXK := (isProjectiveVariety_iff_of_isPullback _ _ _ h).1 hX₀
  -- Hironaka over `k₀`
  obtain ⟨W₀, μ₀, hres, hpure, hS, -⟩ :=
    MMP.Resolution.exists_isLogResolution_isIso_restrict_of_isSNCClosedSubset s₀ hnv₀ B₀.support
  have hW₀v : AlgebraicGeometry.IsVariety k₀ (μ₀ ≫ s₀) := hres.isVariety_source
  haveI : IsProper μ₀ := hres.isProjective.isProper
  obtain ⟨M, hM, hMa⟩ := Stacks.HProjective.exists_isAmple_of_isAffine (Spec (.of k₀))
  obtain ⟨H, hH, hHa⟩ :=
    AlgebraicGeometry.exists_isAmple_of_isProjectiveMorphism s₀ M hMa hX₀.isProjective
  have hμ₀p : IsProjectiveMorphism μ₀ :=
    AlgebraicGeometry.isProjectiveMorphism_of_isProjective μ₀ H hHa hres.isProjective
  have hW₀ : MMP.Mori.IsProjectiveVariety k₀ (μ₀ ≫ s₀) :=
    (MMP.Mori.isProjectiveVariety_iff _ _).mpr ⟨hW₀v, hμ₀p.comp hX₀.isProjective⟩
  haveI : LocallyOfFiniteType (μ₀ ≫ s₀) := hW₀v.toLocallyOfFiniteType
  haveI : LocallyOfFinitePresentation (μ₀ ≫ s₀) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := μ₀ ≫ s₀)).mpr inferInstance
  have hsm₀ : Smooth (μ₀ ≫ s₀) := (MMP.Mori.isSmoothScheme_iff _).mp hres.isSmoothScheme
  haveI : IsIntegral W₀ := hW₀v.toIsIntegral
  haveI : IsNoetherian W₀ := isNoetherian_of_isVariety hW₀v
  haveI : Smooth (μ₀ ≫ s₀) := hsm₀
  haveI : IsNormal W₀ := AlgebraicGeometry.isNormal_of_smooth_over_field (μ₀ ≫ s₀)
  haveI : CompactSpace W₀ := inferInstance
  have hsupp₀ : ((B₀.supp : TopologicalSpace.Closeds X₀) : Set X₀) =
      B₀.support.sup fun E => (E.idealSheaf.support : Set X₀) := by
    rw [DivisorWithCoeffs.supp, TopologicalSpace.Closeds.coe_finset_sup]
    rfl
  have hlog₀ : MMP.Fourfold.IsLogResolution s₀ B₀ μ₀ := by
    refine ⟨⟨⟨inferInstance, hres.isBirationalMorphism, hres.isSmoothScheme⟩, hpure, ?_⟩, hμ₀p⟩
    apply isSNCSubset_of_isSNCClosedSubset hres.isSmoothScheme
    change MMP.Resolution.IsSNCClosedSubset (μ₀ ≫ s₀)
      ((exceptionalSet μ₀ : Set W₀) ∪ μ₀ ⁻¹' ((QDivisor.toRDivisor B₀).supp : Set X₀))
    rw [QDivisor.supp_toRDivisor, hsupp₀]
    exact hS
  -- the base change
  let q := pullback.fst s₀ φ
  let πW := pullback.fst μ₀ q
  let μ : pullback μ₀ q ⟶ X := pullback.snd μ₀ q ≫ h.isoPullback.inv
  have hμs : μ ≫ s = pullback.snd μ₀ q ≫ pullback.snd s₀ φ := by
    simp only [μ, Category.assoc, IsPullback.isoPullback_inv_snd]
  have hcomm : μ ≫ π = πW ≫ μ₀ := by
    simp only [μ, πW, Category.assoc, IsPullback.isoPullback_inv_fst]
    exact pullback.condition.symm
  have hWsq : IsPullback πW (μ ≫ s) (μ₀ ≫ s₀) φ := by
    rw [hμs]
    exact (IsPullback.of_hasPullback μ₀ q).paste_vert (IsPullback.of_hasPullback s₀ φ)
  have hsq : IsPullback πW μ μ₀ π := isPullback_of_isPullback_comp hWsq h rfl rfl hcomm
  have hWK := (isProjectiveVariety_iff_of_isPullback _ _ _ hWsq).1 hW₀
  haveI : IsIntegral (pullback μ₀ q) := hWK.toIsIntegral
  haveI : LocallyOfFiniteType (μ ≫ s) := hWK.toLocallyOfFiniteType
  haveI : LocallyOfFinitePresentation (μ ≫ s) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := μ ≫ s)).mpr inferInstance
  have hsm : Smooth (μ ≫ s) := MorphismProperty.of_isPullback (P := @Smooth) hWsq hsm₀
  haveI : Smooth (μ ≫ s) := hsm
  haveI : IsNormal (pullback μ₀ q) := AlgebraicGeometry.isNormal_of_smooth_over_field (μ ≫ s)
  haveI : IsNoetherian (pullback μ₀ q) := isNoetherian_of_isVariety hWK.toIsVariety
  haveI : Surjective πW := surjective_of_isPullback hWsq
  haveI : IsProper μ := isProper_of_comp_eq hWK hXK rfl
  have hb : MMP.Mori.IsBirationalMorphism μ :=
    (isBirationalMorphism_iff hWsq h hW₀ hX₀ μ₀ rfl μ rfl hcomm).1 hres.isBirationalMorphism
  have hEx : (exceptionalSet μ : Set ↥(pullback μ₀ q)) = πW ⁻¹' exceptionalSet μ₀ :=
    coe_exceptionalSet_eq_preimage_of_isPullback hsq hres.isBirationalMorphism hb
  have hpureK : MMP.Mori.IsPureCodimOne (exceptionalSet μ) :=
    isPureCodimOne_of_isPullback (μ₀ ≫ s₀) hWsq hpure hEx
  have hqp : Stacks.HProjective.IsQuasiProjective s₀ :=
    (isQuasiProjective_iff_hProjectiveIsQuasiProjective _).mp
      ((MMP.Mori.isProjectiveVariety_iff _ _).mp hX₀).2.isQuasiProjective
  have key := (MMP.Fourfold.baseChange_iff_of_isAlgClosed k₀ K s₀ μ₀ hqp).2.2.2.2.2.2.2.2.2.2
    hsm₀ ((exceptionalSet μ₀ : Set W₀) ∪
      μ₀ ⁻¹' (B₀.support.sup fun E => (E.idealSheaf.support : Set X₀)))
  have hSK : MMP.Resolution.IsSNCClosedSubset (μ ≫ s) (πW ⁻¹' ((exceptionalSet μ₀ : Set W₀) ∪
      μ₀ ⁻¹' (B₀.support.sup fun E => (E.idealSheaf.support : Set X₀)))) := by
    rw [hμs]
    exact key.1 hS
  have hlog : MMP.Fourfold.IsLogResolution s B μ := by
    refine ⟨⟨⟨inferInstance, hb, (MMP.Mori.isSmoothScheme_iff _).mpr hsm⟩, hpureK, ?_⟩,
      (isProjectiveMorphism_iff hWsq h hW₀ hX₀ μ₀ rfl μ rfl hcomm).1 hμ₀p⟩
    apply isSNCSubset_of_isSNCClosedSubset ((MMP.Mori.isSmoothScheme_iff _).mpr hsm)
    change MMP.Resolution.IsSNCClosedSubset (μ ≫ s)
      ((exceptionalSet μ : Set ↥(pullback μ₀ q)) ∪ μ ⁻¹' ((QDivisor.toRDivisor B).supp : Set X))
    rw [QDivisor.supp_toRDivisor, coe_supp_eq_preimage_of_isBaseChange h hB, hsupp₀, hEx]
    rw [Set.preimage_union] at hSK
    convert hSK using 2
    ext x
    simp only [Set.mem_preimage]
    rw [← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply]
  exact ⟨W₀, _, μ₀, μ, πW, hWsq, hcomm, hW₀, hsm₀, hlog₀, hlog⟩

/-- **Crepant boundaries under base change.** For a projective log resolution `μ₀` of `(X₀, B₀)`
and its base change `μ`, the crepant boundary `(1/m) μ^*L - div(μ^*ω)` on the base change is the
base change of that on `W₀`, for `ω₀ = dz₁ ∧ ⋯ ∧ dzₙ` and `L₀ = m(div ω₀ + B₀)` Cartier. -/
public theorem exists_isCrepantBoundary_isBaseChange [CharZero k₀]
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) {B₀ : QDivisor X₀} {B : QDivisor X}
    (hB : IsBaseChange π B₀ B) (hP₀ : MMP.Mori.IsPair s₀ B₀)
    {W₀ W : Scheme.{u}} {μ₀ : W₀ ⟶ X₀} {μ : W ⟶ X} {πW : W ⟶ W₀}
    (hWsq : IsPullback πW (μ ≫ s) (μ₀ ≫ s₀) (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hcomm : μ ≫ π = πW ≫ μ₀) (hW₀ : MMP.Mori.IsProjectiveVariety k₀ (μ₀ ≫ s₀))
    (hsm₀ : Smooth (μ₀ ≫ s₀)) (hb₀ : MMP.Mori.IsBirationalMorphism μ₀)
    (hb : MMP.Mori.IsBirationalMorphism μ) :
    ∃ (n : ℕ) (K₀ : Divisor X₀) (KK : Divisor X) (hW₀n : MMP.Mori.IsNormalVariety k₀ (μ₀ ≫ s₀))
      (hWn : MMP.Mori.IsNormalVariety K (μ ≫ s)) (BW₀ : QDivisor W₀) (BW : QDivisor W),
      MMP.Mori.IsCrepantBoundary s₀ n K₀ B₀ μ₀ hW₀n hb₀ BW₀ ∧
        MMP.Mori.IsCrepantBoundary s n KK B μ hWn hb BW ∧ IsBaseChange πW BW₀ BW := by
  classical
  haveI : CharZero K := (RingHom.charZero_iff (algebraMap k₀ K).injective).mp inferInstance
  have : LocallyOfFiniteType s₀ := hX₀.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType s := MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h ‹_›
  haveI : Surjective π := surjective_of_isPullback h
  haveI : IsDominant π := inferInstance
  have hXK := (isProjectiveVariety_iff_of_isPullback _ _ _ h).1 hX₀
  have hnv₀ : MMP.Mori.IsNormalVariety k₀ s₀ := ⟨hX₀.toIsVariety, inferInstance⟩
  have hnvK : MMP.Mori.IsNormalVariety K s := ⟨hXK.toIsVariety, inferInstance⟩
  -- the varieties `W₀` and `W`
  have hWK := (isProjectiveVariety_iff_of_isPullback _ _ _ hWsq).1 hW₀
  haveI : IsIntegral W₀ := hW₀.toIsIntegral
  haveI : IsIntegral W := hWK.toIsIntegral
  haveI : LocallyOfFiniteType (μ₀ ≫ s₀) := hW₀.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (μ ≫ s) := hWK.toLocallyOfFiniteType
  haveI : Smooth (μ₀ ≫ s₀) := hsm₀
  haveI : Smooth (μ ≫ s) := MorphismProperty.of_isPullback (P := @Smooth) hWsq hsm₀
  haveI : IsNormal W₀ := AlgebraicGeometry.isNormal_of_smooth_over_field (μ₀ ≫ s₀)
  haveI : IsNormal W := AlgebraicGeometry.isNormal_of_smooth_over_field (μ ≫ s)
  haveI : IsNoetherian W₀ := isNoetherian_of_isVariety hW₀.toIsVariety
  haveI : IsNoetherian W := isNoetherian_of_isVariety hWK.toIsVariety
  haveI : CompactSpace W₀ := inferInstance
  haveI : CompactSpace W := inferInstance
  haveI : Surjective πW := surjective_of_isPullback hWsq
  haveI : IsDominant πW := inferInstance
  haveI : IsDominant μ₀ := hb₀.isDominant
  haveI : IsDominant μ := hb.isDominant
  have hW₀n : MMP.Mori.IsNormalVariety k₀ (μ₀ ≫ s₀) := ⟨hW₀.toIsVariety, inferInstance⟩
  have hWn : MMP.Mori.IsNormalVariety K (μ ≫ s) := ⟨hWK.toIsVariety, inferInstance⟩
  -- dimensions
  obtain ⟨-, n, K₀', hK₀', hQ⟩ := hP₀
  have hn₀ : topologicalKrullDim X₀ = n := hK₀'.1
  have hnK : topologicalKrullDim X = n :=
    (topologicalKrullDim_eq_of_isPullback s₀ s π h hX₀).trans hn₀
  haveI : AlgebraicGeometry.IsVariety k₀ s₀ := hX₀.toIsVariety
  haveI : AlgebraicGeometry.IsVariety k₀ (μ₀ ≫ s₀) := hW₀.toIsVariety
  have hnW₀ : topologicalKrullDim W₀ = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism s₀ (μ₀ ≫ s₀) hb₀).symm.trans
      hn₀
  have hnW : topologicalKrullDim W = n :=
    (topologicalKrullDim_eq_of_isPullback _ _ _ hWsq hW₀).trans hnW₀
  -- the form `ω₀ = dz₁ ∧ ⋯ ∧ dzₙ` on an étale chart and its base change `ω`
  have h₀sq : IsPullback (𝟙 X₀) s₀ s₀ (𝟙 (Spec (.of k₀))) := IsPullback.of_id_fst
  obtain ⟨U, -, hUsm, hU⟩ := MMP.Spreading.exists_smooth_open_of_isNormalVariety s₀ hnv₀
  have hcoh0 : Order.coheight (genericPoint X₀) ≤ 1 :=
    (Stacks.EtaleCohomology.coheight_genericPoint_eq_zero X₀).trans_le zero_le_one
  obtain ⟨V₁, -, hV₁, hgV₁, n₁, g₁, hg₁, hg₁C⟩ :=
    MMP.Spreading.exists_etale_chart_of_smooth_on s₀ U (genericPoint X₀) (hU _ hcoh0)
  obtain rfl : n₁ = n := chart_dim_eq_of_isPullback h₀sq hn₀ V₁ hV₁ g₁ hg₁ hg₁C hgV₁
  haveI : Nonempty ((𝟙 X₀) ⁻¹ᵁ V₁) := ⟨⟨_, hgV₁⟩⟩
  haveI : Nonempty (π ⁻¹ᵁ V₁) := by
    obtain ⟨y, hy⟩ := π.surjective (genericPoint X₀)
    exact ⟨⟨y, show π y ∈ V₁ by rw [hy]; exact hgV₁⟩⟩
  letI := MMP.Mori.functionFieldAlgebra s₀
  letI := MMP.Mori.functionFieldAlgebra s
  set z : Fin n₁ → Γ(X₀, V₁) := fun i => g₁ (MvPolynomial.X i)
  obtain ⟨ω₀, hω₀def⟩ : ∃ ω₀ : MMP.Mori.RationalTopForms s₀ n₁,
      ω₀ = (exteriorPower.ιMulti X₀.functionField n₁ fun i =>
        KaehlerDifferential.D k₀ X₀.functionField
          (X₀.germToFunctionField ((𝟙 X₀) ⁻¹ᵁ V₁) (Scheme.Hom.app (𝟙 X₀) V₁ (z i)))) := ⟨_, rfl⟩
  obtain ⟨ω, hωdef⟩ : ∃ ω : MMP.Mori.RationalTopForms s n₁,
      ω = (exteriorPower.ιMulti X.functionField n₁ fun i =>
        KaehlerDifferential.D K X.functionField
          (X.germToFunctionField (π ⁻¹ᵁ V₁) (π.app V₁ (z i)))) := ⟨_, rfl⟩
  have hω₀ : ω₀ ≠ 0 := by
    rw [hω₀def]
    exact MMP.Spreading.coordForm_ne_zero_of_isPullback h₀sq hV₁ g₁ hg₁ hg₁C
  obtain ⟨hω, hbω⟩ := isBaseChange_topFormDivisor_of_sections h hnv₀ hn₀ hgV₁ z ω₀ ω
    hω₀def hωdef hω₀
  -- a Cartier multiple `L₀ = m (div ω₀ + B₀)` and its base change `L`
  have hQ' : (Divisor.toQDivisor (MMP.Mori.topFormDivisor s₀ ω₀) + B₀).IsQCartier :=
    MMP.Mori.QDivisor.IsQCartier.add_of_linearlyEquivalent hQ
      (MMP.Spreading.CanonExist.linearlyEquivalent_topFormDivisor hnv₀ hn₀ hω₀ hK₀').symm
  obtain ⟨m, hm, L₀, hL₀, hL₀c⟩ := hQ'.exists_pos
  have hBπ := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant π L₀
  have hLb : IsBaseChange π L₀ (L₀.pullback hL₀c hBπ) := isBaseChange_pullback h hX₀ hL₀c hBπ
  have hLc : (L₀.pullback hL₀c hBπ).IsCartier := Divisor.IsCartier.isCartier_pullback hL₀c π hBπ
  have hL : Divisor.toQDivisor (L₀.pullback hL₀c hBπ) =
      (m : ℤ) • (Divisor.toQDivisor (MMP.Mori.topFormDivisor s ω) + B) :=
    (eq_iff_of_isBaseChange h hX₀ hLb.toQDivisor ((hbω.toQDivisor.add hB).zsmul m)).mp hL₀
  -- the crepant boundaries
  have hcb₀ := isCrepantBoundary_pullback hnv₀ hn₀ hW₀n hb₀ hnW₀ hω₀ hm hL₀ hL₀c
  have hcb := isCrepantBoundary_pullback hnvK hnK hWn hb hnW hω hm hL hLc
  refine ⟨n₁, _, _, hW₀n, hWn, _, _, hcb₀, hcb, ?_⟩
  -- the Cartier parts
  have hB₁ := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant μ₀ L₀
  have hB₂ := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant μ
    (L₀.pullback hL₀c hBπ)
  have hD₀c : (L₀.pullback hL₀c hB₁).IsCartier := Divisor.IsCartier.isCartier_pullback hL₀c μ₀ hB₁
  have hB₃ := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant πW
    (L₀.pullback hL₀c hB₁)
  have hDb : IsBaseChange πW (L₀.pullback hL₀c hB₁) ((L₀.pullback hL₀c hB₁).pullback hD₀c hB₃) :=
    isBaseChange_pullback hWsq hW₀ hD₀c hB₃
  haveI : IsDominant (μ ≫ π) := inferInstance
  have hBe := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant (μ ≫ π) L₀
  have hA := divisor_isPullback_comp hcomm.symm (Divisor.isPullback_pullback hL₀c hB₁)
    (Divisor.isPullback_pullback hD₀c hB₃) hBe
  have hA' := divisor_isPullback_comp rfl (Divisor.isPullback_pullback hL₀c hBπ)
    (Divisor.isPullback_pullback hLc hB₂) hBe
  rw [hA.eq hL₀c hA'] at hDb
  -- the forms on `W₀` and `W`
  have hgV₁' : genericPoint W₀ ∈ μ₀ ⁻¹ᵁ V₁ := by
    show μ₀ (genericPoint W₀) ∈ V₁
    rw [map_genericPoint_of_isDominant μ₀]
    exact hgV₁
  haveI : Nonempty ((𝟙 W₀) ⁻¹ᵁ (μ₀ ⁻¹ᵁ V₁)) := ⟨⟨_, hgV₁'⟩⟩
  haveI : Nonempty (μ₀ ⁻¹ᵁ ((𝟙 X₀) ⁻¹ᵁ V₁)) := ⟨⟨_, hgV₁'⟩⟩
  haveI : Nonempty (πW ⁻¹ᵁ (μ₀ ⁻¹ᵁ V₁)) := by
    obtain ⟨y, hy⟩ := πW.surjective (genericPoint W₀)
    exact ⟨⟨y, show πW y ∈ μ₀ ⁻¹ᵁ V₁ by rw [hy]; exact hgV₁'⟩⟩
  haveI : Nonempty (μ ⁻¹ᵁ (π ⁻¹ᵁ V₁)) := by
    obtain ⟨y, hy⟩ := πW.surjective (genericPoint W₀)
    refine ⟨⟨y, ?_⟩⟩
    show (μ ≫ π) y ∈ V₁
    rw [hcomm, Scheme.Hom.comp_apply, hy]
    exact hgV₁'
  letI := MMP.Mori.functionFieldAlgebra (μ₀ ≫ s₀)
  letI := MMP.Mori.functionFieldAlgebra (μ ≫ s)
  letI := MMP.Mori.functionFieldMapAlgebra μ₀
  letI := MMP.Mori.functionFieldMapAlgebra μ
  haveI := MMP.Mori.isScalarTower_functionFieldMap s₀ μ₀
  haveI := MMP.Mori.isScalarTower_functionFieldMap s μ
  obtain ⟨ω'₀, hω'₀def⟩ : ∃ ω'₀ : MMP.Mori.RationalTopForms (μ₀ ≫ s₀) n₁,
      ω'₀ = (exteriorPower.ιMulti W₀.functionField n₁ fun i =>
        KaehlerDifferential.D k₀ W₀.functionField
          (W₀.germToFunctionField ((𝟙 W₀) ⁻¹ᵁ (μ₀ ⁻¹ᵁ V₁))
            (Scheme.Hom.app (𝟙 W₀) (μ₀ ⁻¹ᵁ V₁) (μ₀.app V₁ (z i))))) := ⟨_, rfl⟩
  obtain ⟨ω', hω'def⟩ : ∃ ω' : MMP.Mori.RationalTopForms (μ ≫ s) n₁,
      ω' = (exteriorPower.ιMulti W.functionField n₁ fun i =>
        KaehlerDifferential.D K W.functionField
          (W.germToFunctionField (πW ⁻¹ᵁ (μ₀ ⁻¹ᵁ V₁)) (πW.app (μ₀ ⁻¹ᵁ V₁) (μ₀.app V₁ (z i))))) :=
    ⟨_, rfl⟩
  have hmap₀ : ω'₀ = MMP.Mori.topFormsMap k₀ X₀.functionField W₀.functionField n₁ ω₀ := by
    rw [hω'₀def, hω₀def]
    exact (topFormsMap_ιMulti_germ s₀ μ₀ ((𝟙 X₀) ⁻¹ᵁ V₁)
      (fun i => Scheme.Hom.app (𝟙 X₀) V₁ (z i))).symm
  haveI : Nonempty ((μ ≫ π) ⁻¹ᵁ V₁) := ‹Nonempty (μ ⁻¹ᵁ (π ⁻¹ᵁ V₁))›
  haveI : Nonempty ((πW ≫ μ₀) ⁻¹ᵁ V₁) := ‹Nonempty (πW ⁻¹ᵁ (μ₀ ⁻¹ᵁ V₁))›
  have hmap : ω' = MMP.Mori.topFormsMap K X.functionField W.functionField n₁ ω := by
    rw [hω'def, hωdef]
    refine Eq.trans ?_ (topFormsMap_ιMulti_germ s μ (π ⁻¹ᵁ V₁) (fun i => π.app V₁ (z i))).symm
    congr 1
    funext i
    congr 1
    exact (germToFunctionField_app_congr hcomm V₁ (z i)).symm
  have htr : Cardinal.toNat (Algebra.trdeg k₀ X₀.functionField) = n₁ := by
    exact_mod_cast (MMP.Fourfold.topologicalKrullDim_eq_toNat_trdeg s₀).symm.trans hn₀
  have hω'₀ : ω'₀ ≠ 0 := by
    obtain ⟨g, hg⟩ := MMP.Mori.exists_isPullbackGenerator_of_bijective s₀ μ₀
      hb₀.functionFieldMap_bijective htr
    rw [hmap₀]
    exact (MMP.Spreading.isPullbackGenerator_of_ne_zero hg hω₀).2.2
  obtain ⟨hω', hbW⟩ := isBaseChange_topFormDivisor_of_sections hWsq hW₀n hnW₀ hgV₁'
    (fun i => μ₀.app V₁ (z i)) ω'₀ ω' hω'₀def hω'def hω'₀
  have hp₀ := pullbackRationalPluriForms_toPluriForms_eq s₀ μ₀ hn₀ hnW₀ ω₀ ω'₀ hmap₀ hω'₀
  have hp := pullbackRationalPluriForms_toPluriForms_eq s μ hnK hnW ω ω' hmap hω'
  rw [hp₀, hp, sub_eq_add_neg, sub_eq_add_neg]
  exact (hDb.toQDivisor.smul (1 / (m : ℚ))).add hbW.toQDivisor.neg

/-- Log canonical pairs are detected over `k₀`. -/
public theorem isLogCanonicalPair_iff [CharZero k₀]
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) {B₀ : QDivisor X₀} {B : QDivisor X}
    (hB : IsBaseChange π B₀ B) :
    MMP.Intersection.IsLogCanonicalPair s₀ B₀ ↔ MMP.Intersection.IsLogCanonicalPair s B := by
  haveI : CharZero K := (RingHom.charZero_iff (algebraMap k₀ K).injective).mp inferInstance
  by_cases hp : MMP.Mori.IsPair s₀ B₀ ∧ ∀ P, 0 ≤ B₀.coeff P
  swap
  · have hp' : ¬ (MMP.Mori.IsPair s B ∧ ∀ P, 0 ≤ B.coeff P) := by
      rwa [← isPair_iff_of_isBaseChange h hX₀ hB,
        ← forall_coeff_nonneg_iff_of_isBaseChange h hX₀ hB]
    exact ⟨fun H => absurd ⟨H.1, H.2.1⟩ hp, fun H => absurd ⟨H.1, H.2.1⟩ hp'⟩
  obtain ⟨hP₀, hnn₀⟩ := hp
  have hP := (isPair_iff_of_isBaseChange h hX₀ hB).1 hP₀
  have hnn := (forall_coeff_nonneg_iff_of_isBaseChange h hX₀ hB).1 hnn₀
  obtain ⟨W₀, W, μ₀, μ, πW, hWsq, hcomm, hW₀, hsm₀, hlog₀, hlog⟩ :=
    exists_isLogResolution_isPullback h hX₀ hB
  obtain ⟨n, K₀, KK, hW₀n, hWn, BW₀, BW, hcb₀, hcb, hbc⟩ :=
    exists_isCrepantBoundary_isBaseChange h hX₀ hB hP₀ hWsq hcomm hW₀ hsm₀
      hlog₀.isBirationalMorphism hlog.isBirationalMorphism
  rw [MMP.Fourfold.isLogCanonicalPair_iff_forall_coeff_le_one s₀
      ⟨inferInstance, inferInstance, hP₀, hnn₀⟩ hlog₀ hW₀n hcb₀,
    MMP.Fourfold.isLogCanonicalPair_iff_forall_coeff_le_one s
      ⟨inferInstance, inferInstance, hP, hnn⟩ hlog hWn hcb]
  haveI : IsIntegral W₀ := hW₀.toIsIntegral
  haveI : IsIntegral W := hWn.1.toIsIntegral
  haveI : LocallyOfFiniteType (μ₀ ≫ s₀) := hW₀.toLocallyOfFiniteType
  exact forall_coeff_iff_of_isBaseChange hWsq hbc (p := fun c => c ≤ 1) zero_le_one

end Model

section Step

variable {X₀ X : Scheme.{u}} [IsIntegral X₀] [CompactSpace X₀] [IsLocallyNoetherian X₀]
  [IsNormal X₀] [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {X'₀ X' : Scheme.{u}} [IsIntegral X'₀] [CompactSpace X'₀] [IsLocallyNoetherian X'₀]
  [IsNormal X'₀] [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
  {Z₀ Z : Scheme.{u}}

/-- Permitted steps are detected over `k₀`. -/
private theorem isPermittedStep_iff [CharZero k₀]
    {s₀ : X₀ ⟶ Spec (.of k₀)} {s : X ⟶ Spec (.of K)} {π : X ⟶ X₀}
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    {t₀ : Z₀ ⟶ Spec (.of k₀)} {t : Z ⟶ Spec (.of K)} {πZ : Z ⟶ Z₀}
    (hZ : IsPullback πZ t t₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    {s'₀ : X'₀ ⟶ Spec (.of k₀)} {s' : X' ⟶ Spec (.of K)} {π' : X' ⟶ X'₀}
    (h' : IsPullback π' s' s'₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    {K₀ : Divisor X₀} {KK : Divisor X} (hK : IsBaseChange π K₀ KK)
    {B₀ : QDivisor X₀} {B : QDivisor X} (hB : IsBaseChange π B₀ B)
    (f₀ : X₀ ⟶ Z₀) (hf₀ : f₀ ≫ t₀ = s₀) (f : X ⟶ Z) (hf : f ≫ t = s)
    (hfπ : f ≫ πZ = π ≫ f₀)
    (fp₀ : X'₀ ⟶ Z₀) (hfp₀ : fp₀ ≫ t₀ = s'₀) (fp : X' ⟶ Z) (hfp : fp ≫ t = s')
    (hfpπ : fp ≫ πZ = π' ≫ fp₀)
    (φ : NumericalCurveClasses s₀ →ₗ[ℝ] NumericalCurveClasses s)
    (hφ : ∀ (C₀ : ProperCurve s₀) (C : ProperCurve s),
      closure {C.point} = π.base ⁻¹' closure {C₀.point} →
        φ (OneCycle.numericalClass _ (C₀.cycle ℝ)) = OneCycle.numericalClass _ (C.cycle ℝ))
    (R₀ : Set (NumericalCurveClasses s₀)) :
    IsPermittedStep s₀ t₀ s'₀ K₀ B₀ R₀ f₀ fp₀ ↔ IsPermittedStep s t s' KK B (φ '' R₀) f fp := by
  have hD := hK.toQDivisor.add hB
  have hproj := isProjectiveVariety_iff_of_isPullback _ _ _ h
  have hprojZ := isProjectiveVariety_iff_of_isPullback _ _ _ hZ
  have hproj' := isProjectiveVariety_iff_of_isPullback _ _ _ h'
  have key : ∀ (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀)
      (hZ₀ : MMP.Mori.IsProjectiveVariety k₀ t₀) (hX'₀ : MMP.Mori.IsProjectiveVariety k₀ s'₀)
      (_ : IsNormal Z₀) (_ : IsBirationalMorphism f₀) (_ : IsBirationalMorphism fp₀),
      IsPermittedStep s₀ t₀ s'₀ K₀ B₀ R₀ f₀ fp₀ ↔
        IsPermittedStep s t s' KK B (φ '' R₀) f fp := by
    intro hX₀ hZ₀ hX'₀ hZn hb₀ hbp₀
    haveI := hZn
    have hKf := isBaseChange_flipTransform h hZ h' hX₀ hZ₀ hX'₀ f₀ hf₀ f
      hf hfπ fp₀ hfp₀ fp hfp hfpπ hbp₀ hK
    have hBf := isBaseChange_flipTransform h hZ h' hX₀ hZ₀ hX'₀ f₀ hf₀ f
      hf hfπ fp₀ hfp₀ fp hfp hfpπ hbp₀ hB
    have e1 := isLogCanonicalPair_iff h hX₀ hB
    have e2 := exists_isCanonicalDivisor_iff h hX₀ hK
    have e3 := isNegativeExtremalRayOf_iff h hX₀ hD φ hφ R₀
    have e4 := isContractionOfRay_iff h hZ hX₀ hZ₀ f₀ hf₀ f hf hfπ φ hφ R₀
    have e5 := relativePicardNumberN1_eq h hZ hX₀ hZ₀ f₀ f hf hfπ
    have e6 := hasRelativelyAmpleMultiple_iff h hZ hX₀ hZ₀ f₀ hf₀ f hf hfπ hD.neg
    have e7 := isBirationalMorphism_iff h hZ hX₀ hZ₀ f₀ hf₀ f hf hfπ
    have e8 := isSmallMorphism_iff h' hZ hX'₀ hZ₀ fp₀ hfp₀ fp hfp hfpπ
    have e9 := isProjectiveMorphism_iff h' hZ hX'₀ hZ₀ fp₀ hfp₀ fp hfp hfpπ
    have e10 := isLogCanonicalPair_iff h' hX'₀ hBf
    have e11 := hasRelativelyAmpleMultiple_iff h' hZ hX'₀ hZ₀ fp₀ hfp₀ fp hfp
      hfpπ (hKf.toQDivisor.add hBf)
    constructor
    · intro H
      exact
        { isProjectiveVariety := hproj.1 H.isProjectiveVariety
          isLogCanonicalPair := e1.1 H.isLogCanonicalPair
          isCanonicalDivisor := e2.1 H.isCanonicalDivisor
          isNegativeExtremalRayOf := e3.1 H.isNegativeExtremalRayOf
          isContractionOfRay := e4.1 H.isContractionOfRay
          isProjectiveVariety_target := hprojZ.1 H.isProjectiveVariety_target
          relativePicardNumber_eq_one := e5 ▸ H.relativePicardNumber_eq_one
          hasRelativelyAmpleMultiple := e6.1 H.hasRelativelyAmpleMultiple
          isBirationalMorphism := e7.1 H.isBirationalMorphism
          isProjectiveVariety_step := hproj'.1 H.isProjectiveVariety_step
          isSmallMorphism_step := e8.1 H.isSmallMorphism_step
          isProjectiveMorphism_step := e9.1 H.isProjectiveMorphism_step
          isLogCanonicalPair_step := e10.1 H.isLogCanonicalPair_step
          hasRelativelyAmpleMultiple_step := e11.1 H.hasRelativelyAmpleMultiple_step }
    · intro H
      exact
        { isProjectiveVariety := hproj.2 H.isProjectiveVariety
          isLogCanonicalPair := e1.2 H.isLogCanonicalPair
          isCanonicalDivisor := e2.2 H.isCanonicalDivisor
          isNegativeExtremalRayOf := e3.2 H.isNegativeExtremalRayOf
          isContractionOfRay := e4.2 H.isContractionOfRay
          isProjectiveVariety_target := hprojZ.2 H.isProjectiveVariety_target
          relativePicardNumber_eq_one := e5 ▸ H.relativePicardNumber_eq_one
          hasRelativelyAmpleMultiple := e6.2 H.hasRelativelyAmpleMultiple
          isBirationalMorphism := e7.2 H.isBirationalMorphism
          isProjectiveVariety_step := hproj'.2 H.isProjectiveVariety_step
          isSmallMorphism_step := e8.2 H.isSmallMorphism_step
          isProjectiveMorphism_step := e9.2 H.isProjectiveMorphism_step
          isLogCanonicalPair_step := e10.2 H.isLogCanonicalPair_step
          hasRelativelyAmpleMultiple_step := e11.2 H.hasRelativelyAmpleMultiple_step }
  constructor
  · intro H
    exact (key H.isProjectiveVariety H.isProjectiveVariety_target H.isProjectiveVariety_step
      H.isContractionOfRay.isNormalVariety_target.2 H.isBirationalMorphism
      H.isSmallMorphism_step.isBirationalMorphism).1 H
  · intro H
    have hX₀ := hproj.2 H.isProjectiveVariety
    have hZ₀ := hprojZ.2 H.isProjectiveVariety_target
    have hX'₀ := hproj'.2 H.isProjectiveVariety_step
    have : LocallyOfFiniteType t₀ := hZ₀.toLocallyOfFiniteType
    have hZn : IsNormal Z₀ :=
      (invariants_of_isPullback t₀ hZ).1.2 H.isContractionOfRay.isNormalVariety_target.2
    exact (key hX₀ hZ₀ hX'₀ hZn
      ((isBirationalMorphism_iff h hZ hX₀ hZ₀ f₀ hf₀ f hf hfπ).2
        H.isBirationalMorphism)
      ((isSmallMorphism_iff h' hZ hX'₀ hZ₀ fp₀ hfp₀ fp hfp hfpπ).2
        H.isSmallMorphism_step).isBirationalMorphism).2 H

end Step

end Helpers

end MMP.ProgramBaseChange

@[expose] public section

namespace MMP.Fourfold

open MMP.ProgramBaseChange in
/-- **Programs are detected after algebraically closed base extension.** Let `k₀ → K` be
algebraically closed fields of characteristic zero. Take data over `k₀` for a sequence of diagrams
`X_i ⟶ Z_i ⟵ X_{i+1}` with an optional final contraction `X_n ⟶ T`: models `X₀ = X`,
`X_{i+1} = Y₀ i`, canonical divisors and boundaries, rays `R₀ i ⊆ NE̅(X_i)`, contractions `f₀ i`
and small morphisms `fp₀ i`. Let the corresponding data over `K` be their base change. The
models, targets and morphisms sit in pullback squares over `Spec K ⟶ Spec k₀`. The divisors are
base changed prime divisor by prime divisor. Each ray is transported by the linear map `φ i`
induced by base extension of curves. Then the data over `k₀` satisfy the conditions of
`MMP.Fourfold.Program` from `(X₀, B₀)` if and only if the base-changed data satisfy them from
`(X₀_K, B₀_K)`. -/
@[mmp "lem_oai4_c3_program_base_change_iff"]
public theorem program_conditions_iff_of_isPullback
    {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K] [IsAlgClosed k₀] [IsAlgClosed K]
    [CharZero k₀]
    (n : ℕ∞) (hasFinal : Prop)
    -- the data over `k₀`
    {X₀ : Scheme.{u}} [IsIntegral X₀] [CompactSpace X₀] [IsLocallyNoetherian X₀] [IsNormal X₀]
    (sX₀ : X₀ ⟶ Spec (.of k₀)) (KX₀ : Divisor X₀) (BX₀ : QDivisor X₀)
    {Y₀ : ℕ → Scheme.{u}} [∀ i, IsIntegral (Y₀ i)] [∀ i, CompactSpace (Y₀ i)]
    [∀ i, IsLocallyNoetherian (Y₀ i)] [∀ i, IsNormal (Y₀ i)]
    (sY₀ : ∀ i, Y₀ i ⟶ Spec (.of k₀)) (KY₀ : ∀ i, Divisor (Y₀ i)) (BY₀ : ∀ i, QDivisor (Y₀ i))
    (R₀ : ∀ i, Set (NumericalCurveClasses (modelStr sX₀ sY₀ i)))
    (hR₀ : ∀ i : ℕ, (i : ℕ∞) < n → R₀ i ⊆ closedConeOfCurves (modelStr sX₀ sY₀ i))
    {Z₀ : ℕ → Scheme.{u}} (sZ₀ : ∀ i, Z₀ i ⟶ Spec (.of k₀))
    (f₀ : ∀ i, modelSeq X₀ Y₀ i ⟶ Z₀ i)
    (hf₀ : ∀ i : ℕ, (i : ℕ∞) < n → f₀ i ≫ sZ₀ i = modelStr sX₀ sY₀ i)
    (fp₀ : ∀ i, Y₀ i ⟶ Z₀ i) (hfp₀ : ∀ i : ℕ, (i : ℕ∞) < n → fp₀ i ≫ sZ₀ i = sY₀ i)
    (finalRay₀ : Set (NumericalCurveClasses (modelStr sX₀ sY₀ n.toNat)))
    (hfinal₀ : hasFinal → finalRay₀ ⊆ closedConeOfCurves (modelStr sX₀ sY₀ n.toNat))
    {T₀ : Scheme.{u}} (sT₀ : T₀ ⟶ Spec (.of k₀)) (g₀ : modelSeq X₀ Y₀ n.toNat ⟶ T₀)
    (hg₀ : hasFinal → g₀ ≫ sT₀ = modelStr sX₀ sY₀ n.toNat)
    -- the data over `K`
    {X : Scheme.{u}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of K)) (KX : Divisor X) (BX : QDivisor X)
    {Y : ℕ → Scheme.{u}} [∀ i, IsIntegral (Y i)] [∀ i, CompactSpace (Y i)]
    [∀ i, IsLocallyNoetherian (Y i)] [∀ i, IsNormal (Y i)]
    (sY : ∀ i, Y i ⟶ Spec (.of K)) (KY : ∀ i, Divisor (Y i)) (BY : ∀ i, QDivisor (Y i))
    (R : ∀ i, Set (NumericalCurveClasses (modelStr sX sY i)))
    {Z : ℕ → Scheme.{u}} (sZ : ∀ i, Z i ⟶ Spec (.of K))
    (f : ∀ i, modelSeq X Y i ⟶ Z i) (hf : ∀ i : ℕ, (i : ℕ∞) < n → f i ≫ sZ i = modelStr sX sY i)
    (fp : ∀ i, Y i ⟶ Z i) (hfp : ∀ i : ℕ, (i : ℕ∞) < n → fp i ≫ sZ i = sY i)
    (finalRay : Set (NumericalCurveClasses (modelStr sX sY n.toNat)))
    {T : Scheme.{u}} (sT : T ⟶ Spec (.of K)) (g : modelSeq X Y n.toNat ⟶ T)
    (hg : hasFinal → g ≫ sT = modelStr sX sY n.toNat)
    -- the data over `K` are the base change of the data over `k₀`
    (π : ∀ i, modelSeq X Y i ⟶ modelSeq X₀ Y₀ i)
    (hπ : ∀ i : ℕ, (i : ℕ∞) ≤ n → IsPullback (π i) (modelStr sX sY i) (modelStr sX₀ sY₀ i)
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (πZ : ∀ i, Z i ⟶ Z₀ i)
    (hπZ : ∀ i : ℕ, (i : ℕ∞) < n →
      IsPullback (πZ i) (sZ i) (sZ₀ i) (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (πT : T ⟶ T₀)
    (hπT : hasFinal → IsPullback πT sT sT₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hfπ : ∀ i : ℕ, (i : ℕ∞) < n → f i ≫ πZ i = π i ≫ f₀ i)
    (hfpπ : ∀ i : ℕ, (i : ℕ∞) < n → fp i ≫ πZ i = π (i + 1) ≫ fp₀ i)
    (hgπ : hasFinal → g ≫ πT = π n.toNat ≫ g₀)
    (hKB : ∀ i : ℕ, (i : ℕ∞) ≤ n → ∀ (P₀ : MMP.Mori.PrimeDivisor (modelSeq X₀ Y₀ i))
      (P : MMP.Mori.PrimeDivisor (modelSeq X Y i)),
      closure {P.genericPoint} = (π i).base ⁻¹' closure {P₀.genericPoint} →
        divisorSeq KX KY i P = divisorSeq KX₀ KY₀ i P₀ ∧
          divisorSeq BX BY i P = divisorSeq BX₀ BY₀ i P₀)
    (hKBsupp : ∀ i : ℕ, (i : ℕ∞) ≤ n → ∀ (P : MMP.Mori.PrimeDivisor (modelSeq X Y i)),
      (divisorSeq KX KY i P ≠ 0 ∨ divisorSeq BX BY i P ≠ 0) →
        ∃ P₀ : MMP.Mori.PrimeDivisor (modelSeq X₀ Y₀ i),
          closure {P.genericPoint} = (π i).base ⁻¹' closure {P₀.genericPoint})
    -- the rays are transported by base extension of curves
    (φ : ∀ i, NumericalCurveClasses (modelStr sX₀ sY₀ i) →ₗ[ℝ]
      NumericalCurveClasses (modelStr sX sY i))
    (hφ : ∀ i : ℕ, (i : ℕ∞) ≤ n → ∀ (C₀ : ProperCurve (modelStr sX₀ sY₀ i))
      (C : ProperCurve (modelStr sX sY i)),
      closure {C.point} = (π i).base ⁻¹' closure {C₀.point} →
        φ i (OneCycle.numericalClass _ (C₀.cycle ℝ)) = OneCycle.numericalClass _ (C.cycle ℝ))
    (hR : ∀ i : ℕ, (i : ℕ∞) < n → R i = φ i '' R₀ i)
    (hfinal : hasFinal → finalRay = φ n.toNat '' finalRay₀) :
    (MMP.Mori.IsProjectiveVariety k₀ sX₀ ∧ MMP.Intersection.IsLogCanonicalPair sX₀ BX₀ ∧
      (∃ m : ℕ, KX₀.IsCanonicalDivisor sX₀ m) ∧
      (∀ i : ℕ, (i : ℕ∞) < n →
        IsPermittedStep (modelStr sX₀ sY₀ i) (sZ₀ i) (sY₀ i) (divisorSeq KX₀ KY₀ i)
          (divisorSeq BX₀ BY₀ i) (R₀ i) (f₀ i) (fp₀ i)) ∧
      (∀ i : ℕ, (i : ℕ∞) < n → KY₀ i = flipTransform (f₀ i) (fp₀ i) (divisorSeq KX₀ KY₀ i)) ∧
      (∀ i : ℕ, (i : ℕ∞) < n → BY₀ i = flipTransform (f₀ i) (fp₀ i) (divisorSeq BX₀ BY₀ i)) ∧
      (hasFinal → n ≠ ⊤ ∧
        IsNegativeExtremalRayOf (modelStr sX₀ sY₀ n.toNat)
          (Divisor.toQDivisor (divisorSeq KX₀ KY₀ n.toNat) + divisorSeq BX₀ BY₀ n.toNat)
          finalRay₀ ∧
        IsContractionOfRay (modelStr sX₀ sY₀ n.toNat) sT₀ finalRay₀ g₀ ∧
        MMP.Mori.IsProjectiveVariety k₀ sT₀ ∧
        relativePicardNumberN1 (modelStr sX₀ sY₀ n.toNat) g₀ = 1 ∧
        (-(Divisor.toQDivisor (divisorSeq KX₀ KY₀ n.toNat) +
          divisorSeq BX₀ BY₀ n.toNat)).HasRelativelyAmpleMultiple g₀ ∧
        topologicalKrullDim T₀ < topologicalKrullDim (modelSeq X₀ Y₀ n.toNat))) ↔
    (MMP.Mori.IsProjectiveVariety K sX ∧ MMP.Intersection.IsLogCanonicalPair sX BX ∧
      (∃ m : ℕ, KX.IsCanonicalDivisor sX m) ∧
      (∀ i : ℕ, (i : ℕ∞) < n →
        IsPermittedStep (modelStr sX sY i) (sZ i) (sY i) (divisorSeq KX KY i)
          (divisorSeq BX BY i) (R i) (f i) (fp i)) ∧
      (∀ i : ℕ, (i : ℕ∞) < n → KY i = flipTransform (f i) (fp i) (divisorSeq KX KY i)) ∧
      (∀ i : ℕ, (i : ℕ∞) < n → BY i = flipTransform (f i) (fp i) (divisorSeq BX BY i)) ∧
      (hasFinal → n ≠ ⊤ ∧
        IsNegativeExtremalRayOf (modelStr sX sY n.toNat)
          (Divisor.toQDivisor (divisorSeq KX KY n.toNat) + divisorSeq BX BY n.toNat)
          finalRay ∧
        IsContractionOfRay (modelStr sX sY n.toNat) sT finalRay g ∧
        MMP.Mori.IsProjectiveVariety K sT ∧
        relativePicardNumberN1 (modelStr sX sY n.toNat) g = 1 ∧
        (-(Divisor.toQDivisor (divisorSeq KX KY n.toNat) +
          divisorSeq BX BY n.toNat)).HasRelativelyAmpleMultiple g ∧
        topologicalKrullDim T < topologicalKrullDim (modelSeq X Y n.toNat))) := by
  have hKc : ∀ i : ℕ, (i : ℕ∞) ≤ n →
      IsBaseChange (π i) (divisorSeq KX₀ KY₀ i) (divisorSeq KX KY i) :=
    fun i hi => ⟨fun P₀ P hP => (hKB i hi P₀ P hP).1, fun P hP => hKBsupp i hi P (Or.inl hP)⟩
  have hBc : ∀ i : ℕ, (i : ℕ∞) ≤ n →
      IsBaseChange (π i) (divisorSeq BX₀ BY₀ i) (divisorSeq BX BY i) :=
    fun i hi => ⟨fun P₀ P hP => (hKB i hi P₀ P hP).2, fun P hP => hKBsupp i hi P (Or.inr hP)⟩
  have hsucc : ∀ i : ℕ, (i : ℕ∞) < n → ((i + 1 : ℕ) : ℕ∞) ≤ n := fun i hi => by
    push_cast; exact Order.add_one_le_of_lt hi
  have hproj : ∀ i : ℕ, (i : ℕ∞) ≤ n → (MMP.Mori.IsProjectiveVariety k₀ (modelStr sX₀ sY₀ i) ↔
      MMP.Mori.IsProjectiveVariety K (modelStr sX sY i)) := fun i hi =>
    isProjectiveVariety_iff_of_isPullback _ _ _ (hπ i hi)
  have hstep : ∀ i : ℕ, (hi : (i : ℕ∞) < n) →
      (IsPermittedStep (modelStr sX₀ sY₀ i) (sZ₀ i) (sY₀ i) (divisorSeq KX₀ KY₀ i)
          (divisorSeq BX₀ BY₀ i) (R₀ i) (f₀ i) (fp₀ i) ↔
        IsPermittedStep (modelStr sX sY i) (sZ i) (sY i) (divisorSeq KX KY i)
          (divisorSeq BX BY i) (R i) (f i) (fp i)) := by
    intro i hi
    have h' : IsPullback (π (i + 1)) (sY i) (sY₀ i)
        (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) := hπ (i + 1) (hsucc i hi)
    rw [hR i hi]
    exact isPermittedStep_iff (hπ i hi.le) (hπZ i hi) h' (hKc i hi.le) (hBc i hi.le) (f₀ i)
      (hf₀ i hi) (f i) (hf i hi) (hfπ i hi) (fp₀ i) (hfp₀ i hi) (fp i) (hfp i hi) (hfpπ i hi)
      (φ i) (hφ i hi.le) (R₀ i)
  -- the strict-transform identities, given the steps over `k₀`
  have hflip : ∀ i : ℕ, (hi : (i : ℕ∞) < n) →
      IsPermittedStep (modelStr sX₀ sY₀ i) (sZ₀ i) (sY₀ i) (divisorSeq KX₀ KY₀ i)
          (divisorSeq BX₀ BY₀ i) (R₀ i) (f₀ i) (fp₀ i) →
      ((KY₀ i = flipTransform (f₀ i) (fp₀ i) (divisorSeq KX₀ KY₀ i) ↔
          KY i = flipTransform (f i) (fp i) (divisorSeq KX KY i)) ∧
        (BY₀ i = flipTransform (f₀ i) (fp₀ i) (divisorSeq BX₀ BY₀ i) ↔
          BY i = flipTransform (f i) (fp i) (divisorSeq BX BY i))) := by
    intro i hi H
    have h' : IsPullback (π (i + 1)) (sY i) (sY₀ i)
        (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) := hπ (i + 1) (hsucc i hi)
    have hX'₀ := H.isProjectiveVariety_step
    have hbp := H.isSmallMorphism_step.isBirationalMorphism
    haveI : IsNormal (Z₀ i) := H.isContractionOfRay.isNormalVariety_target.2
    exact ⟨eq_iff_of_isBaseChange h' hX'₀ (hKc (i + 1) (hsucc i hi))
        (isBaseChange_flipTransform (hπ i hi.le) (hπZ i hi) h' H.isProjectiveVariety
          H.isProjectiveVariety_target hX'₀ (f₀ i) (hf₀ i hi) (f i) (hf i hi) (hfπ i hi) (fp₀ i)
          (hfp₀ i hi) (fp i) (hfp i hi) (hfpπ i hi) hbp (hKc i hi.le)),
      eq_iff_of_isBaseChange h' hX'₀ (hBc (i + 1) (hsucc i hi))
        (isBaseChange_flipTransform (hπ i hi.le) (hπZ i hi) h' H.isProjectiveVariety
          H.isProjectiveVariety_target hX'₀ (f₀ i) (hf₀ i hi) (f i) (hf i hi) (hfπ i hi) (fp₀ i)
          (hfp₀ i hi) (fp i) (hfp i hi) (hfpπ i hi) hbp (hBc i hi.le))⟩
  -- the final contraction
  have hfin : ∀ (hF : hasFinal), n ≠ ⊤ →
      MMP.Mori.IsProjectiveVariety k₀ (modelStr sX₀ sY₀ n.toNat) →
      ((IsNegativeExtremalRayOf (modelStr sX₀ sY₀ n.toNat)
          (Divisor.toQDivisor (divisorSeq KX₀ KY₀ n.toNat) + divisorSeq BX₀ BY₀ n.toNat)
          finalRay₀ ∧
        IsContractionOfRay (modelStr sX₀ sY₀ n.toNat) sT₀ finalRay₀ g₀ ∧
        MMP.Mori.IsProjectiveVariety k₀ sT₀ ∧
        relativePicardNumberN1 (modelStr sX₀ sY₀ n.toNat) g₀ = 1 ∧
        (-(Divisor.toQDivisor (divisorSeq KX₀ KY₀ n.toNat) +
          divisorSeq BX₀ BY₀ n.toNat)).HasRelativelyAmpleMultiple g₀ ∧
        topologicalKrullDim T₀ < topologicalKrullDim (modelSeq X₀ Y₀ n.toNat)) ↔
      (IsNegativeExtremalRayOf (modelStr sX sY n.toNat)
          (Divisor.toQDivisor (divisorSeq KX KY n.toNat) + divisorSeq BX BY n.toNat)
          finalRay ∧
        IsContractionOfRay (modelStr sX sY n.toNat) sT finalRay g ∧
        MMP.Mori.IsProjectiveVariety K sT ∧
        relativePicardNumberN1 (modelStr sX sY n.toNat) g = 1 ∧
        (-(Divisor.toQDivisor (divisorSeq KX KY n.toNat) +
          divisorSeq BX BY n.toNat)).HasRelativelyAmpleMultiple g ∧
        topologicalKrullDim T < topologicalKrullDim (modelSeq X Y n.toNat))) := by
    intro hF hn hX₀
    have hN : ((n.toNat : ℕ) : ℕ∞) ≤ n := ENat.coe_toNat_le_self n
    have h := hπ n.toNat hN
    have hT := hπT hF
    have hD := (hKc n.toNat hN).toQDivisor.add (hBc n.toNat hN)
    have hprojT := isProjectiveVariety_iff_of_isPullback _ _ _ hT
    have hdX := topologicalKrullDim_eq_of_isPullback _ _ _ h hX₀
    rw [hfinal hF]
    have key : MMP.Mori.IsProjectiveVariety k₀ sT₀ → ((IsNegativeExtremalRayOf
          (modelStr sX₀ sY₀ n.toNat)
          (Divisor.toQDivisor (divisorSeq KX₀ KY₀ n.toNat) + divisorSeq BX₀ BY₀ n.toNat)
          finalRay₀ ∧
        IsContractionOfRay (modelStr sX₀ sY₀ n.toNat) sT₀ finalRay₀ g₀ ∧
        MMP.Mori.IsProjectiveVariety k₀ sT₀ ∧
        relativePicardNumberN1 (modelStr sX₀ sY₀ n.toNat) g₀ = 1 ∧
        (-(Divisor.toQDivisor (divisorSeq KX₀ KY₀ n.toNat) +
          divisorSeq BX₀ BY₀ n.toNat)).HasRelativelyAmpleMultiple g₀ ∧
        topologicalKrullDim T₀ < topologicalKrullDim (modelSeq X₀ Y₀ n.toNat)) ↔
      (IsNegativeExtremalRayOf (modelStr sX sY n.toNat)
          (Divisor.toQDivisor (divisorSeq KX KY n.toNat) + divisorSeq BX BY n.toNat)
          (φ n.toNat '' finalRay₀) ∧
        IsContractionOfRay (modelStr sX sY n.toNat) sT (φ n.toNat '' finalRay₀) g ∧
        MMP.Mori.IsProjectiveVariety K sT ∧
        relativePicardNumberN1 (modelStr sX sY n.toNat) g = 1 ∧
        (-(Divisor.toQDivisor (divisorSeq KX KY n.toNat) +
          divisorSeq BX BY n.toNat)).HasRelativelyAmpleMultiple g ∧
        topologicalKrullDim T < topologicalKrullDim (modelSeq X Y n.toNat))) := by
      intro hT₀
      rw [isNegativeExtremalRayOf_iff h hX₀ hD (φ n.toNat) (hφ n.toNat hN) finalRay₀,
        isContractionOfRay_iff h hT hX₀ hT₀ g₀ (hg₀ hF) g (hg hF) (hgπ hF) (φ n.toNat)
          (hφ n.toNat hN) finalRay₀,
        hprojT, relativePicardNumberN1_eq h hT hX₀ hT₀ g₀ g (hg hF) (hgπ hF),
        hasRelativelyAmpleMultiple_iff h hT hX₀ hT₀ g₀ (hg₀ hF) g (hg hF) (hgπ hF) hD.neg,
        topologicalKrullDim_eq_of_isPullback _ _ _ hT hT₀]
      change _ ↔ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧
        topologicalKrullDim T₀ < topologicalKrullDim (modelSeq X Y n.toNat)
      rw [hdX]
    exact ⟨fun H => (key H.2.2.1).1 H, fun H => (key (hprojT.2 H.2.2.1)).2 H⟩
  -- projectivity of every model, from either side
  have hmodels₀ : MMP.Mori.IsProjectiveVariety k₀ sX₀ →
      (∀ i : ℕ, (i : ℕ∞) < n →
        IsPermittedStep (modelStr sX₀ sY₀ i) (sZ₀ i) (sY₀ i) (divisorSeq KX₀ KY₀ i)
          (divisorSeq BX₀ BY₀ i) (R₀ i) (f₀ i) (fp₀ i)) →
      ∀ i : ℕ, (i : ℕ∞) ≤ n → MMP.Mori.IsProjectiveVariety k₀ (modelStr sX₀ sY₀ i) := by
    intro h0 hs i hi
    cases i with
    | zero => exact h0
    | succ j =>
      have hj : (j : ℕ∞) < n := lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self j) hi
      exact (hs j hj).isProjectiveVariety_step
  have hπ0 : IsPullback (π 0) sX sX₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) :=
    hπ 0 (by simp)
  have hX := isProjectiveVariety_iff_of_isPullback _ _ _ hπ0
  constructor
  · rintro ⟨hP, hlc, hcan, hs, hKY, hBY, hF⟩
    refine ⟨hX.1 hP, (isLogCanonicalPair_iff hπ0 hP (hBc 0 (by simp))).1 hlc,
      (exists_isCanonicalDivisor_iff hπ0 hP (hKc 0 (by simp))).1 hcan,
      fun i hi => (hstep i hi).1 (hs i hi),
      fun i hi => ((hflip i hi (hs i hi)).1).1 (hKY i hi),
      fun i hi => ((hflip i hi (hs i hi)).2).1 (hBY i hi), fun hf => ?_⟩
    obtain ⟨hn, hrest⟩ := hF hf
    exact ⟨hn, (hfin hf hn (hmodels₀ hP hs _ (ENat.coe_toNat_le_self n))).1 hrest⟩
  · rintro ⟨hP, hlc, hcan, hs, hKY, hBY, hF⟩
    have hP₀ := hX.2 hP
    have hs₀ : ∀ i : ℕ, (i : ℕ∞) < n →
        IsPermittedStep (modelStr sX₀ sY₀ i) (sZ₀ i) (sY₀ i) (divisorSeq KX₀ KY₀ i)
          (divisorSeq BX₀ BY₀ i) (R₀ i) (f₀ i) (fp₀ i) := fun i hi => (hstep i hi).2 (hs i hi)
    refine ⟨hP₀, (isLogCanonicalPair_iff hπ0 hP₀ (hBc 0 (by simp))).2 hlc,
      (exists_isCanonicalDivisor_iff hπ0 hP₀ (hKc 0 (by simp))).2 hcan, hs₀,
      fun i hi => ((hflip i hi (hs₀ i hi)).1).2 (hKY i hi),
      fun i hi => ((hflip i hi (hs₀ i hi)).2).2 (hBY i hi), fun hf => ?_⟩
    obtain ⟨hn, hrest⟩ := hF hf
    exact ⟨hn, (hfin hf hn (hmodels₀ hP₀ hs₀ _ (ENat.coe_toNat_le_self n))).2 hrest⟩

end MMP.Fourfold

end
