module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.MMP.Fourfold.ProgramBaseChange.AlgClosedExtension
public import MMP.AlgebraicGeometry.Geometrically.CurveClassesBaseChange
public import MMP.AlgebraicGeometry.SpreadingOut.ProjectiveDiagram
public import MMP.AlgebraicGeometry.MMP.Fourfold.ProgramBaseChange.CountableDescent
public import MMP.AlgebraicGeometry.MMP.Fourfold.Contraction.LcRay
public import MMP.AlgebraicGeometry.MMP.Contraction.VerticalFactorization
public import MMP.AlgebraicGeometry.Geometrically.NumericalDivisorClassesBaseChange
public import MMP.AlgebraicGeometry.Resolution.OrderUpperSemicontinuous
public import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
public import MMP.Analysis.Convex.FiniteDimensional
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Valuation
public import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
public import MMP.AlgebraicGeometry.Resolution.SncPairStratumBlowup
public import MMP.AlgebraicGeometry.Morphisms.FiniteFunctionField

/-!
# Contractions of negative extremal rays over any algebraically closed field

Let `k` be an algebraically closed field of characteristic zero and `(X, B)` a projective lc
fourfold pair over `k` with rational boundary, with canonical divisor `K` and `D = K + B`. Every
`D`-negative extremal ray `R` of `NE̅(X)` has a contraction `f : X ⟶ Z`: a projective surjective
morphism onto a normal projective variety with `f_* 𝒪_X = 𝒪_Z`, contracting exactly the integral
curves whose classes lie in `R`, with `ρ(X/Z) = 1` and `-D` `f`-ample. Over `ℂ` this is the lc
contraction theorem; over a general `k` the pair is defined over a countable algebraically closed
subfield `k₀ ⊆ k`, which embeds in `ℂ`, and the complex contraction is spread out, specialised
to a `k₀`-point and base changed to `k`.

## Main results

* `MMP.Fourfold.exists_isContractionOfRay_of_isNegativeExtremalRayOf_of_isAlgClosed`: the
  contraction exists.

## Implementation notes

"Fourfold" is `topologicalKrullDim X = 4`; the boundary is a `ℚ`-divisor, so it is rational.
The condition `f_* 𝒪_X = 𝒪_Z` and the normality of `Z` are fields of
`MMP.Fourfold.IsContraction`, which `MMP.Fourfold.IsContractionOfRay` extends; `-D` being
`f`-ample is `MMP.Mori.QDivisor.HasRelativelyAmpleMultiple`.

## References

* [KM98] Kollár, Mori, *Birational Geometry of Algebraic Varieties*.
-/

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MMP.Mori MMP.Fourfold
  MMP.ProgramBaseChange

namespace Proof_lem_oai4_finite_existence_transfer_b

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

section FieldChangeBasics

variable {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K] [IsAlgClosed k₀]

/-- Normality, integrality and dimension are insensitive to a base change along
`Spec K ⟶ Spec k₀`, in any pullback square. -/
private lemma invariants_of_isPullback {X W : Scheme.{u}} (f : X ⟶ Spec (.of k₀))
    [LocallyOfFiniteType f] {p : W ⟶ X} {s : W ⟶ Spec (.of K)}
    (h : IsPullback p s f (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))) :
    (IsNormal X ↔ IsNormal W) ∧ (IsIntegral X ↔ IsIntegral W) ∧
      topologicalKrullDim W = topologicalKrullDim X := by
  obtain ⟨-, hint, hnor, -, hdim⟩ :=
    MMP.isReduced_isIntegral_isNormal_dim_baseChange_of_isAlgClosed (K := K) f
  let e := h.isoPullback
  refine ⟨hnor.trans ⟨fun _ => MMP.ProgramBaseChange.isNormal_of_iso e,
    fun _ => MMP.ProgramBaseChange.isNormal_of_iso e.symm⟩,
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

/-- The base change of a normal variety along an extension of an algebraically closed ground
field is a normal variety. -/
private lemma isNormalVariety_of_isPullback
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
  have : IsIso (pullback.snd (𝟙 (Spec (.of k₀))) φ) := inferInstance
  refine IsProjectiveMorphism.of_iso e (asIso (pullback.snd (𝟙 (Spec (.of k₀))) φ)).symm ?_ hs
  rw [Iso.symm_hom, asIso_inv, IsIso.eq_comp_inv, Category.assoc]
  exact h.isoIsPullback_hom_snd _ _ hsq

/-- Projectivity of a variety is unchanged by base change along `Spec K ⟶ Spec k₀`. -/
private theorem isProjectiveVariety_iff_of_isPullback {X₀ X : Scheme.{u}}
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
private theorem topologicalKrullDim_eq_of_isPullback {X₀ X : Scheme.{u}}
    (s₀ : X₀ ⟶ Spec (.of k₀)) (s : X ⟶ Spec (.of K)) (π : X ⟶ X₀)
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) :
    topologicalKrullDim X = topologicalKrullDim X₀ := by
  have : LocallyOfFiniteType s₀ := hX₀.toLocallyOfFiniteType
  exact (invariants_of_isPullback s₀ h).2.2

/-! ### Prime divisors under base change -/

/-- The base change of a prime divisor: `π⁻¹(closure P₀)` is the closure of the generic point of a
prime divisor of `X`, lying over the generic point of `P₀`. -/
private theorem exists_primeDivisor_baseChange {X₀ X : Scheme.{u}} [IsIntegral X₀] [IsIntegral X]
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
  have hpw : π w = x := map_eq_of_closure_eq hw.def
  obtain ⟨h1, h2⟩ := coheight_le_of_isPullback s₀ h
  obtain ⟨w', hw'x, hw'⟩ := h2 x
  have hww' : w ⤳ w' := by
    rw [specializes_iff_mem_closure, hw.def]
    show π w' ∈ closure {x}
    rw [hw'x]; exact subset_closure rfl
  have hcoh : Order.coheight w = 1 := by
    have hx1 : Order.coheight x = 1 := AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P₀
    have hle : Order.coheight w ≤ Order.coheight w' := Order.coheight_anti hww'
    refine le_antisymm (hle.trans (hw'.trans hx1.le)) ?_
    rw [← hx1, ← hpw]
    exact h1 w
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

open RingedSpaceModuleAdjunction in
/-- `𝒪_Y(nL) ≅ 𝒪_Y(L)^{⊗ n}` for a Cartier divisor `L` and `n ≥ 1`. -/
private theorem nonempty_divisorialSheaf_nsmul_iso {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] {L : Divisor Y} (hL : L.IsCartier) (n : ℕ) (hn : 1 ≤ n) :
    haveI := hL.isInvertibleModule_divisorialSheaf
    Nonempty ((n • L).divisorialSheaf ≅
      Stacks.Ample.tensorPowModule Y L.divisorialSheaf (n : ℤ)) := by
  have := hL.isInvertibleModule_divisorialSheaf
  induction n, hn using Nat.le_induction with
  | base =>
    exact ⟨eqToIso (congrArg Divisor.divisorialSheaf (one_nsmul L)) ≪≫
      (Stacks.Ample.tensorPowModuleOneIso Y _).symm⟩
  | succ n hn ih =>
    obtain ⟨e⟩ := ih
    refine ⟨eqToIso (congrArg Divisor.divisorialSheaf (succ_nsmul L n)) ≪≫
      ((hL.nsmul n).divisorialSheafTensorIso hL).symm ≪≫ ?_ ≪≫
      Stacks.Ample.tensorPowModuleAddIso Y _ (n : ℤ) 1 ≪≫
      Stacks.RelativeVeryAmple.tensorPowModuleCongr Y _ (by push_cast; rfl)⟩
    exact ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso e).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).obj _).mapIso
        (Stacks.Ample.tensorPowModuleOneIso Y _).symm

open RingedSpaceModuleAdjunction in
/-- A positive multiple of an `f`-ample Cartier divisor is `f`-ample. -/
private theorem isRelativelyAmple_nsmul {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {f : X ⟶ Y} {L : Divisor X} (hL : L.IsCartier)
    (h : L.IsRelativelyAmple f hL) (n : ℕ) (hn : 0 < n) :
    (n • L).IsRelativelyAmple f (hL.nsmul n) := by
  have := hL.isInvertibleModule_divisorialSheaf
  have := (hL.nsmul n).isInvertibleModule_divisorialSheaf
  intro y
  obtain ⟨V, hV, hyV, hA⟩ := h y
  refine ⟨V, hV, hyV, ?_⟩
  obtain ⟨e0⟩ := nonempty_divisorialSheaf_nsmul_iso hL n hn
  have := Stacks.Ample.isInvertibleModule_tensorPowModule (f ⁻¹ᵁ V).toScheme
    ((modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj L.divisorialSheaf) (n : ℤ)
  let e := (modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).mapIso e0 ≪≫
    Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso (f ⁻¹ᵁ V).ι _ n
  rw [Stacks.RelativeVeryAmple.isAmple_congr _ _ e]
  exact (Stacks.AmplePositivePower.isAmple_iff_isAmple_tensorPowModule _ n hn).1 hA

section Model

variable {X₀ X : Scheme.{u}} [IsIntegral X₀] [CompactSpace X₀] [IsLocallyNoetherian X₀]
  [IsNormal X₀] [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {s₀ : X₀ ⟶ Spec (.of k₀)} {s : X ⟶ Spec (.of K)} {π : X ⟶ X₀}

/-- **Base change of Cartier divisors.** The pull-back of a Cartier divisor `L₀` to the base change
is the base change of `L₀`. -/
private theorem isBaseChange_pullback
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
    apply hP
    have := WithZero.exp_injective (h1.symm.trans WithZero.exp_zero.symm)
    exact this

/-- **Base change of Cartier divisors.** The pull-back of a Cartier divisor `L₀` to the base change
is a Cartier divisor which is the base change of `L₀`, and its sheaf is the pull-back of
`𝒪_{X₀}(L₀)`. -/
private theorem exists_isBaseChange_of_isCartier
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
private theorem eq_iff_of_isBaseChange {R : Type*} [Zero R]
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

/-- **Curve forms are detected over `k₀`.** On the base change `C` of a proper curve `C₀`, the
curve form of the base change of a `ℚ`-Cartier divisor is that of the divisor on `C₀`. -/
private theorem curveForm_numericalClass_eq_of_isBaseChange
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
private theorem isNegativeExtremalRayOf_iff
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) {D₀ : QDivisor X₀} {D : QDivisor X}
    (hD : IsBaseChange π D₀ D) (hQD₀ : D₀.IsQCartier) (hQD : D.IsQCartier)
    (φ : NumericalCurveClasses s₀ →ₗ[ℝ] NumericalCurveClasses s)
    (hφ : ∀ (C₀ : ProperCurve s₀) (C : ProperCurve s),
      closure {C.point} = π.base ⁻¹' closure {C₀.point} →
        φ (OneCycle.numericalClass _ (C₀.cycle ℝ)) = OneCycle.numericalClass _ (C.cycle ℝ))
    (R₀ : Set (NumericalCurveClasses s₀)) :
    IsNegativeExtremalRayOf s₀ D₀ R₀ ↔ IsNegativeExtremalRayOf s D (φ '' R₀) := by
  have hQ : D₀.IsQCartier ↔ D.IsQCartier := ⟨fun _ => hQD, fun _ => hQD₀⟩
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
    have := linearMap_ext_numericalClass_cycle s₀
      (φ := (QDivisor.curveForm s D hD').comp e.toLinearMap)
      (ψ := QDivisor.curveForm s₀ D₀ hD₀) fun C₀ => by
        obtain ⟨C, hC, -⟩ := exists_properCurve_baseChange s₀ s π h C₀
        rw [LinearMap.comp_apply, LinearEquiv.coe_coe, he C₀ C hC]
        exact curveForm_numericalClass_eq_of_isBaseChange h hX₀ hD hD₀ hD' C₀ C hC
    exact congrArg (fun F : NumericalCurveClasses s₀ →ₗ[ℝ] ℝ => F u) this
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
private theorem relativePicardNumberN1_eq
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hZ : IsPullback πZ t t₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) (hZ₀ : MMP.Mori.IsProjectiveVariety k₀ t₀)
    (f₀ : X₀ ⟶ Z₀) (hf₀ : f₀ ≫ t₀ = s₀) (f : X ⟶ Z) (hf : f ≫ t = s)
    (hfπ : f ≫ πZ = π ≫ f₀) :
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
private theorem hasRelativelyAmpleMultiple_iff
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hZ : IsPullback πZ t t₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) (hZ₀ : MMP.Mori.IsProjectiveVariety k₀ t₀)
    (f₀ : X₀ ⟶ Z₀) (hf₀ : f₀ ≫ t₀ = s₀) (f : X ⟶ Z) (hf : f ≫ t = s)
    (hfπ : f ≫ πZ = π ≫ f₀) {D₀ : QDivisor X₀} {D : QDivisor X} (hD : IsBaseChange π D₀ D)
    (hQD₀ : D₀.IsQCartier) :
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
    obtain ⟨n, hn, N₀, hN₀, hN₀c⟩ := hQD₀.exists_pos
    have hM₀c : (m • N₀).IsCartier := hN₀c.nsmul m
    obtain ⟨M, hMc, hMb, ⟨eM⟩⟩ := exists_isBaseChange_of_isCartier h hX₀ hM₀c
    have hM₀ : Divisor.toQDivisor (m • N₀) = ((n * m : ℕ) : ℤ) • D₀ := by
      rw [map_nsmul, hN₀, ← natCast_zsmul, smul_smul]
      congr 1
      push_cast
      ring
    have hM : Divisor.toQDivisor M = Divisor.toQDivisor (n • L) := by
      rw [(eq_iff_of_isBaseChange h hX₀ hMb.toQDivisor (hD.zsmul ((n * m : ℕ) : ℤ))).mp hM₀,
        map_nsmul, hL, ← natCast_zsmul, smul_smul]
      congr 1
    have hnL := isRelativelyAmple_nsmul hLc hA n hn
    have hMa : M.IsRelativelyAmple f hMc := by
      obtain rfl := Divisor.toQDivisor_injective hM
      exact hnL
    exact ⟨n * m, Nat.mul_pos hn hm, m • N₀, hM₀c, hM₀, (hamp _ hM₀c M hMc eM).mpr hMa⟩

/-- Projective morphisms are detected over `k₀`. -/
private theorem isProjectiveMorphism_iff
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
private theorem isContractionOfRay_iff
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

end Model

end Helpers

section BaseChange

variable {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K] [IsAlgClosed k₀] [IsAlgClosed K]

/-- The base change of an integral normal scheme of finite type over `k₀` along
`Spec K ⟶ Spec k₀` is a normal integral Noetherian scheme. -/
private theorem isIntegral_isNormal_of_isPullback {X₀ X : Scheme.{u}}
    (s₀ : X₀ ⟶ Spec (.of k₀)) (s : X ⟶ Spec (.of K)) (π : X ⟶ X₀)
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) [IsNormal X₀] :
    IsIntegral X ∧ CompactSpace X ∧ IsLocallyNoetherian X ∧ IsNormal X := by
  have : LocallyOfFiniteType s₀ := hX₀.toLocallyOfFiniteType
  have : QuasiCompact s₀ := hX₀.toQuasiCompact
  have : IsIntegral X₀ := hX₀.toIsIntegral
  have hinv := invariants_of_isPullback s₀ h
  have : LocallyOfFiniteType s := MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h ‹_›
  have : QuasiCompact s := MorphismProperty.of_isPullback (P := @QuasiCompact) h ‹_›
  exact ⟨hinv.2.1.1 ‹_›, QuasiCompact.compactSpace_of_compactSpace s,
    LocallyOfFiniteType.isLocallyNoetherian s, hinv.1.1 ‹_›⟩

/-- **Base change of divisors.** Every divisor of `X₀` has a base change to `X`. -/
private theorem exists_isBaseChange {R : Type*} [AddCommMonoid R] {X₀ X : Scheme.{u}}
    [IsIntegral X₀] [IsIntegral X] {s₀ : X₀ ⟶ Spec (.of k₀)} {s : X ⟶ Spec (.of K)}
    {π : X ⟶ X₀} [LocallyOfFiniteType s₀]
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (D₀ : DivisorWithCoeffs R X₀) : ∃ D : DivisorWithCoeffs R X, IsBaseChange π D₀ D := by
  have : Surjective π := surjective_of_isPullback h
  choose b hb _ using exists_primeDivisor_baseChange h
  have hinj : Function.Injective b := fun P₀ Q₀ e =>
    primeDivisor_eq_of_closure_eq (hb P₀) (e ▸ hb Q₀)
  refine ⟨Finsupp.mapDomain b D₀, fun P₀ P hP => ?_, fun P hP => ?_⟩
  · obtain rfl : b P₀ = P := primeDivisor_eq_of_closure_eq' (hb P₀) hP
    exact Finsupp.mapDomain_apply_of_injective hinj D₀ P₀
  · by_contra hne
    push Not at hne
    exact hP (Finsupp.mapDomain_notin_range D₀ P fun ⟨P₀, e⟩ => hne P₀ (e ▸ hb P₀))

/-- A prime divisor of `X` lying over the generic point of a prime divisor `P₀` of `X₀` is the
base change of `P₀`. -/
private theorem closure_eq_of_map_eq {X₀ X : Scheme.{u}}
    [IsIntegral X₀] [IsIntegral X] {s₀ : X₀ ⟶ Spec (.of k₀)} {s : X ⟶ Spec (.of K)}
    {π : X ⟶ X₀} [LocallyOfFiniteType s₀]
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    {P₀ : MMP.Mori.PrimeDivisor X₀} {P : MMP.Mori.PrimeDivisor X}
    (hP : π P.genericPoint = P₀.genericPoint) :
    closure {P.genericPoint} = π.base ⁻¹' closure {P₀.genericPoint} := by
  obtain ⟨Q, hQ, -⟩ := exists_primeDivisor_baseChange h P₀
  have hsp : Q.genericPoint ⤳ P.genericPoint := by
    rw [specializes_iff_mem_closure, hQ, Set.mem_preimage]
    change π P.genericPoint ∈ closure {P₀.genericPoint}
    rw [hP]
    exact subset_closure rfl
  have heq := eq_of_specializes_of_coheight_eq_one hsp
    (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Q)
    (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P)
  rw [← heq, hQ]

/-- A divisor on the base change is the base change of `D₀` as soon as its coefficient along every
prime divisor over a prime divisor `E₀` of `X₀` is that of `E₀`, and all its other coefficients
vanish. -/
private theorem isBaseChange_of_coeff {R : Type*} [Zero R] {X₀ X : Scheme.{u}}
    [IsIntegral X₀] [IsIntegral X] {s₀ : X₀ ⟶ Spec (.of k₀)} {s : X ⟶ Spec (.of K)}
    {π : X ⟶ X₀} [LocallyOfFiniteType s₀]
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    {D₀ : DivisorWithCoeffs R X₀} {D : DivisorWithCoeffs R X}
    (h1 : ∀ (E : MMP.Mori.PrimeDivisor X) (E₀ : MMP.Mori.PrimeDivisor X₀),
      π E.genericPoint = E₀.genericPoint → D.coeff E = D₀.coeff E₀)
    (h2 : ∀ E : MMP.Mori.PrimeDivisor X,
      (∀ E₀ : MMP.Mori.PrimeDivisor X₀, π E.genericPoint ≠ E₀.genericPoint) → D.coeff E = 0) :
    IsBaseChange π D₀ D := by
  have : Surjective π := surjective_of_isPullback h
  refine ⟨fun P₀ P hP => h1 P P₀ (map_eq_of_closure_eq hP), fun P hP => ?_⟩
  by_contra hne
  push Not at hne
  exact hP (h2 P fun E₀ hE => hne E₀ (closure_eq_of_map_eq h hE))

end BaseChange

/-- The negative of a `ℚ`-Cartier divisor is `ℚ`-Cartier. -/
private theorem neg_isQCartier {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] {D : QDivisor X} (h : D.IsQCartier) :
    (-D).IsQCartier := by
  obtain ⟨m, hm, hD⟩ := h
  exact ⟨-m, neg_ne_zero.mpr hm, by rwa [neg_smul_neg]⟩

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

/-- **Contractions of a ray are unique.** Two contractions of the same extremal ray of a
projective variety differ by a unique isomorphism of their targets. -/
private theorem exists_iso_of_isContractionOfRay {k : Type u} [Field k] {U V V' : Scheme.{u}}
    {sU : U ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)} {sV' : V' ⟶ Spec (.of k)}
    (hU : MMP.Mori.IsProjectiveVariety k sU) {R : Set (NumericalCurveClasses sU)}
    (hR : IsExtremalRay ℝ (closedConeOfCurves sU : Set (NumericalCurveClasses sU)) R)
    {g : U ⟶ V} {g' : U ⟶ V'} (hg : IsContractionOfRay sU sV R g)
    (hg' : IsContractionOfRay sU sV' R g') : ∃ e : V ≅ V', g' = g ≫ e.hom := by
  have u {W : Scheme.{u}} {sW : W ⟶ Spec (.of k)} {h : U ⟶ W} (hh : IsContractionOfRay sU sW R h)
      {W' : Scheme.{u}} {sW' : W' ⟶ Spec (.of k)} {h' : U ⟶ W'}
      (hh' : IsContractionOfRay sU sW' R h') : ∃! a : W' ⟶ W, h' ≫ a = h :=
    existsUnique_comp_eq_of_isContractionOfRay hU hh.isProjectiveMorphism hh.comp_eq hR
      (fun C hC => (hh.isContractedBy_iff C).mpr hC) hh'
  obtain ⟨a, ha, -⟩ := u hg' hg
  obtain ⟨b, hb, -⟩ := u hg hg'
  exact ⟨⟨a, b, (u hg hg).unique (by rw [← Category.assoc, ha, hb]) (Category.comp_id _),
    (u hg' hg').unique (by rw [← Category.assoc, hb, ha]) (Category.comp_id _)⟩, ha.symm⟩

section Spreading

/-- **Points of finitely generated algebras.** A finitely generated subalgebra `A ⊆ K` over an
algebraically closed field `k₀` has a `k₀`-point: `Spec k₀ ⟶ Spec A` is a section of the structure
morphism (Hilbert's Nullstellensatz). -/
private theorem exists_comp_specMap_eq_id {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K]
    [IsAlgClosed k₀] (A : Subalgebra k₀ K) (hA : A.FG) :
    ∃ x : Spec (.of k₀) ⟶ Spec (.of A),
      x ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ A)) = 𝟙 _ := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite k₀ (A ⧸ m) :=
    AlgebraicGeometry.FieldExtensionDescent.finite_quotient_of_isMaximal k₀ K ⟨A, hA⟩ m
  haveI : Algebra.IsIntegral k₀ (A ⧸ m) := Algebra.IsIntegral.of_finite k₀ _
  let e : k₀ ≃ₐ[k₀] A ⧸ m :=
    AlgEquiv.ofBijective (Algebra.ofId k₀ (A ⧸ m)) IsAlgClosed.algebraMap_bijective_of_isIntegral
  let ψ : A →ₐ[k₀] k₀ := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k₀ m)
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom), ?_⟩
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have : ψ.toRingHom.comp (algebraMap k₀ A) = RingHom.id k₀ := by
    ext a
    simp
  rw [this]
  exact Spec.map_id _

variable {I : Type u} [Category.{u} I] [IsCofiltered I] [Quiver.IsThin I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
  [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]

include hc in
/-- **An ample invertible sheaf descends to a stage.** Let `C` be the base change to the limit of
a scheme `W` of finite presentation over a stage `i`. An ample invertible sheaf `H` on `C` is, at
every late enough stage `m`, the pull-back of an ample invertible sheaf on `W ×_{D i} D m`. -/
private theorem exists_isAmple_stage (i : I) {W C : Scheme.{u}} [CompactSpace C]
    (p : W ⟶ D.obj i) [QuasiCompact p] [QuasiSeparated p]
    (a : C ⟶ W) (φ : C ⟶ c.pt) (hpb : IsPullback a φ p (c.π.app i))
    (H : C.Modules) [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 H]
    (hH : Scheme.Modules.IsAmple C H) :
    ∃ (b : I) (_ : b ⟶ i), ∀ (m : I) (_ : m ⟶ b) (hmi : m ⟶ i),
      ∃ (M : (pullback (D.map hmi) p).Modules)
        (_ : SheafOfModules.IsInvertible (pullback (D.map hmi) p).presheaf
          (pullback (D.map hmi) p).ringCatSheaf.2 M),
        Scheme.Modules.IsAmple _ M ∧
        Nonempty ((Scheme.Modules.pullback (pullback.lift (φ ≫ c.π.app m) a
          (by rw [Category.assoc, c.w hmi, hpb.w]))).obj M ≅ H) := by
  -- the system of base changes of `W` to the later stages, with limit `C`
  let Y : Over (D.obj i) := Over.mk p
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace p
  haveI : QuasiSeparatedSpace W := quasiSeparatedSpace_of_quasiSeparated p
  haveI : CompactSpace Y.left := inferInstanceAs (CompactSpace W)
  haveI : QuasiSeparatedSpace Y.left := inferInstanceAs (QuasiSeparatedSpace W)
  let D' := AlgebraicGeometry.baseChangeDiagram D i Y
  let c' := AlgebraicGeometry.baseChangeCone D c i Y
  have hc' : IsLimit c' := AlgebraicGeometry.baseChangeConeIsLimit D hc i Y
  haveI : ∀ {a b : Over i} (g : a ⟶ b), IsAffineHom (D'.map g) := fun g =>
    AlgebraicGeometry.isAffineHom_baseChangeDiagram_map D i Y g
  haveI : ∀ a, CompactSpace (D'.obj a) := fun a =>
    AlgebraicGeometry.compactSpace_baseChangeDiagram_obj D i Y a
  haveI : ∀ a, QuasiSeparatedSpace (D'.obj a) := fun a =>
    AlgebraicGeometry.quasiSeparatedSpace_baseChangeDiagram_obj D i Y a
  let ιC : C ≅ c'.pt := hpb.flip.isoPullback
  haveI : CompactSpace c'.pt := QuasiCompact.compactSpace_of_compactSpace ιC.inv
  haveI := MMP.Mori.isInvertible_pullback_obj ιC.inv H
  have hH' : Scheme.Modules.IsAmple c'.pt ((Scheme.Modules.pullback ιC.inv).obj H) :=
    Scheme.Modules.isAmple_pullback_of_isAffineHom ιC.inv H hH
  -- the sheaf descends to a stage `a₁`, and its ampleness to a later stage `b'`
  obtain ⟨a₁, L₁, hL₁, ⟨eL⟩⟩ :=
    Stacks.AlgebraicGeometry.ModuleLimits.exists_isInvertible_pullback_iso_of_isLimit D' c' hc'
      ((Scheme.Modules.pullback ιC.inv).obj H) inferInstance
  haveI := hL₁
  haveI := MMP.Mori.isInvertible_pullback_obj (c'.π.app a₁) L₁
  have hamp₁ : Scheme.Modules.IsAmple c'.pt ((Scheme.Modules.pullback (c'.π.app a₁)).obj L₁) :=
    Scheme.Modules.isAmple_of_iso eL hH'
  obtain ⟨b', g, hg⟩ :=
    Stacks.AlgebraicGeometry.AmpleLimit.exists_isAmple_pullback_map_of_isLimit_of_qcqs D' c' hc'
      a₁ L₁ hamp₁
  refine ⟨b'.left, b'.hom, fun m hm hmi => ?_⟩
  let m' : Over i := Over.mk hmi
  let gm : m' ⟶ b' := Over.homMk hm (Subsingleton.elim _ _)
  haveI := MMP.Mori.isInvertible_pullback_obj (D'.map g) L₁
  have hMinv := MMP.Mori.isInvertible_pullback_obj (D'.map gm)
    ((Scheme.Modules.pullback (D'.map g)).obj L₁)
  have hMa : Scheme.Modules.IsAmple (D'.obj m')
      ((Scheme.Modules.pullback (D'.map gm)).obj ((Scheme.Modules.pullback (D'.map g)).obj L₁)) :=
    Scheme.Modules.isAmple_pullback_of_isAffineHom _ _ hg
  refine ⟨(Scheme.Modules.pullback (D'.map gm)).obj ((Scheme.Modules.pullback (D'.map g)).obj L₁),
    hMinv, hMa, ?_⟩
  -- the canonical map `C ⟶ D m ×_{D i} W` is the leg of the limit cone
  have t1 : c'.π.app m' ≫ pullback.fst (D.map hmi) p = pullback.fst (c.π.app i) p ≫ c.π.app m :=
    AlgebraicGeometry.baseChangeTransition_fst _ _ _ (Over.w _) _
  have t2 : c'.π.app m' ≫ pullback.snd (D.map hmi) p = pullback.snd (c.π.app i) p :=
    AlgebraicGeometry.baseChangeTransition_snd _ _ _ (Over.w _) _
  have i1 : ιC.hom ≫ pullback.fst (c.π.app i) p = φ := hpb.flip.isoPullback_hom_fst
  have i2 : ιC.hom ≫ pullback.snd (c.π.app i) p = a := hpb.flip.isoPullback_hom_snd
  have h0 : (φ ≫ c.π.app m) ≫ D.map hmi = a ≫ p := by rw [Category.assoc, c.w hmi, hpb.w]
  have hκ : (pullback.lift (φ ≫ c.π.app m) a h0 : C ⟶ pullback (D.map hmi) p) =
      ιC.hom ≫ c'.π.app m' := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      calc φ ≫ c.π.app m = (ιC.hom ≫ pullback.fst (c.π.app i) p) ≫ c.π.app m := by rw [i1]
        _ = ιC.hom ≫ (c'.π.app m' ≫ pullback.fst (D.map hmi) p) := by
          rw [t1]; exact Category.assoc _ _ _
        _ = (ιC.hom ≫ c'.π.app m') ≫ pullback.fst (D.map hmi) p := (Category.assoc _ _ _).symm
    · rw [pullback.lift_snd]
      calc a = ιC.hom ≫ pullback.snd (c.π.app i) p := i2.symm
        _ = ιC.hom ≫ (c'.π.app m' ≫ pullback.snd (D.map hmi) p) := by rw [t2]
        _ = (ιC.hom ≫ c'.π.app m') ≫ pullback.snd (D.map hmi) p := (Category.assoc _ _ _).symm
  have hw : ((ιC.hom ≫ c'.π.app m') ≫ D'.map gm) ≫ D'.map g = ιC.hom ≫ c'.π.app a₁ := by
    rw [Category.assoc, Category.assoc, ← Functor.map_comp, c'.w (gm ≫ g)]
  rw [hκ]
  exact ⟨(Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackCongr hw).app L₁ ≪≫ ((Scheme.Modules.pullbackComp _ _).app L₁).symm ≪≫
    (Scheme.Modules.pullback ιC.hom).mapIso eL.symm ≪≫ (Scheme.Modules.pullbackComp _ _).app H ≪≫
    (Scheme.Modules.pullbackCongr ιC.hom_inv_id).app H ≪≫ (Scheme.Modules.pullbackId C).app H⟩

include hc in
/-- **A morphism descends to a stage.** Let `X = X₀ ×_T c.pt` and let `C` be the base change to
the limit of a scheme `W` of finite presentation over a stage `i`. A morphism `F : X ⟶ C` over the
limit is, at every late enough stage `m`, the base change of a morphism
`X₀ ×_T D m ⟶ D m ×_{D i} W` over `D m`. -/
private theorem exists_morphism_stage [EssentiallySmall.{u} I]
    {T X₀ : Scheme.{u}} (s₀ : X₀ ⟶ T) [LocallyOfFinitePresentation s₀] [QuasiCompact s₀]
    [QuasiSeparated s₀] (t : ∀ i, D.obj i ⟶ T) (ht : ∀ {i j : I} (e : j ⟶ i), D.map e ≫ t i = t j)
    (tc : c.pt ⟶ T) (htc : ∀ i, c.π.app i ≫ t i = tc)
    (i : I) {W C X : Scheme.{u}} (p : W ⟶ D.obj i) (hp : FinitePresentation p)
    (a : C ⟶ W) (φ : C ⟶ c.pt) (hpb : IsPullback a φ p (c.π.app i))
    (π : X ⟶ X₀) (s : X ⟶ c.pt) (hX : IsPullback π s s₀ tc) (F : X ⟶ C) (hF : F ≫ φ = s) :
    ∃ (j : I) (_ : j ⟶ i), ∀ (m : I) (_ : m ⟶ j) (hmi : m ⟶ i),
      ∃ v : pullback s₀ (t m) ⟶ pullback (D.map hmi) p,
        v ≫ pullback.fst (D.map hmi) p = pullback.snd s₀ (t m) ∧
        pullback.lift π (s ≫ c.π.app m) (by rw [hX.w, Category.assoc, htc]) ≫ v =
          F ≫ pullback.lift (φ ≫ c.π.app m) a (by rw [Category.assoc, c.w hmi, hpb.w]) := by
  let Xo : Over (D.obj i) := (Over.pullback (t i)).obj (Over.mk s₀)
  let Yo : Over (D.obj i) := Over.mk p
  have hXo : FinitePresentation Xo.hom :=
    ⟨inferInstanceAs (LocallyOfFinitePresentation (pullback.snd s₀ (t i))),
    inferInstanceAs (QuasiCompact (pullback.snd s₀ (t i))),
    inferInstanceAs (QuasiSeparated (pullback.snd s₀ (t i)))⟩
  -- `X` is the base change of `Xo` to the limit
  let κ : X ⟶ pullback s₀ (t i) :=
    pullback.lift π (s ≫ c.π.app i) (by rw [hX.w, Category.assoc, htc])
  have hXi : IsPullback κ s (pullback.snd s₀ (t i)) (c.π.app i) := by
    have H : IsPullback (κ ≫ pullback.fst s₀ (t i)) s s₀ (c.π.app i ≫ t i) := by
      rw [pullback.lift_fst, htc]
      exact hX
    exact IsPullback.of_right H (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback s₀ (t i))
  let fo : (Over.pullback (c.π.app i)).obj Xo ⟶ (Over.pullback (c.π.app i)).obj Yo :=
    Over.homMk (hXi.isoPullback.inv ≫ F ≫ hpb.isoPullback.hom) (by
      change (hXi.isoPullback.inv ≫ F ≫ hpb.isoPullback.hom) ≫ pullback.snd p (c.π.app i) =
        pullback.snd (pullback.snd s₀ (t i)) (c.π.app i)
      rw [Category.assoc, Category.assoc, hpb.isoPullback_hom_snd, hF, Iso.inv_comp_eq,
        hXi.isoPullback_hom_snd])
  obtain ⟨j, e, g, α, β, hα, hβ, hcomm⟩ :=
    exists_morphism_after_baseChange D c hc i Xo Yo hXo hp fo
  refine ⟨j, e, fun m hm hmi => ?_⟩
  obtain rfl : hmi = hm ≫ e := Subsingleton.elim _ _
  -- the base change of `X₀` to the stage `m`, mapped to its base change to the stage `j`
  let ρ₀ : pullback s₀ (t m) ⟶ pullback s₀ (t i) :=
    pullback.lift (pullback.fst s₀ (t m)) (pullback.snd s₀ (t m) ≫ D.map (hm ≫ e))
      (by rw [pullback.condition, Category.assoc, ht])
  let ρ : pullback s₀ (t m) ⟶ pullback (pullback.snd s₀ (t i)) (D.map e) :=
    pullback.lift ρ₀ (pullback.snd s₀ (t m) ≫ D.map hm)
      (by rw [pullback.lift_snd, Functor.map_comp, Category.assoc])
  have hgw : g.left ≫ pullback.snd p (D.map e) =
      pullback.snd (pullback.snd s₀ (t i)) (D.map e) := Over.w g
  let v : pullback s₀ (t m) ⟶ pullback (D.map (hm ≫ e)) p :=
    pullback.lift (pullback.snd s₀ (t m)) (ρ ≫ g.left ≫ pullback.fst p (D.map e)) (by
      rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc g.left, hgw,
        pullback.lift_snd_assoc, Functor.map_comp, Category.assoc])
  set lm : X ⟶ pullback s₀ (t m) := pullback.lift π (s ≫ c.π.app m)
    (by rw [hX.w, Category.assoc, htc]) with hlm
  set lZ : C ⟶ pullback (D.map (hm ≫ e)) p := pullback.lift (φ ≫ c.π.app m) a
    (by rw [Category.assoc, c.w (hm ≫ e), hpb.w]) with hlZ
  have hlm1 : lm ≫ pullback.fst s₀ (t m) = π := pullback.lift_fst _ _ _
  have hlm2 : lm ≫ pullback.snd s₀ (t m) = s ≫ c.π.app m := pullback.lift_snd _ _ _
  have hκ1 : κ ≫ pullback.fst s₀ (t i) = π := pullback.lift_fst _ _ _
  have hκ2 : κ ≫ pullback.snd s₀ (t i) = s ≫ c.π.app i := pullback.lift_snd _ _ _
  have hρ₀1 : ρ₀ ≫ pullback.fst s₀ (t i) = pullback.fst s₀ (t m) := pullback.lift_fst _ _ _
  have hρ₀2 : ρ₀ ≫ pullback.snd s₀ (t i) = pullback.snd s₀ (t m) ≫ D.map (hm ≫ e) :=
    pullback.lift_snd _ _ _
  have hρ1 : ρ ≫ pullback.fst Xo.hom (D.map e) = ρ₀ := pullback.lift_fst _ _ _
  have hρ2 : ρ ≫ ((Over.pullback (D.map e)).obj Xo).hom = pullback.snd s₀ (t m) ≫ D.map hm :=
    pullback.lift_snd _ _ _
  have hv1 : v ≫ pullback.fst (D.map (hm ≫ e)) p = pullback.snd s₀ (t m) := pullback.lift_fst _ _ _
  have hv2 : v ≫ pullback.snd (D.map (hm ≫ e)) p = ρ ≫ g.left ≫ pullback.fst p (D.map e) :=
    pullback.lift_snd _ _ _
  have hl1 : lZ ≫ pullback.fst (D.map (hm ≫ e)) p = φ ≫ c.π.app m := pullback.lift_fst _ _ _
  have hl2 : lZ ≫ pullback.snd (D.map (hm ≫ e)) p = a := pullback.lift_snd _ _ _
  refine ⟨v, hv1, ?_⟩
  apply pullback.hom_ext
  · rw [Category.assoc, hv1, hlm2, Category.assoc, hl1, ← Category.assoc, hF]
  · rw [Category.assoc, hv2, Category.assoc, hl2]
    -- the comparison through the stage `j`
    let θ : X ⟶ pullback ((Over.pullback (D.map e)).obj Xo).hom (c.π.app j) :=
      pullback.lift (lm ≫ ρ) s (by rw [Category.assoc, hρ2, ← Category.assoc, hlm2,
        Category.assoc, c.w hm])
    have hθ1 : θ ≫ pullback.fst ((Over.pullback (D.map e)).obj Xo).hom (c.π.app j) = lm ≫ ρ :=
      pullback.lift_fst _ _ _
    have hθ2 : θ ≫ pullback.snd ((Over.pullback (D.map e)).obj Xo).hom (c.π.app j) = s :=
      pullback.lift_snd _ _ _
    have e1 : hXi.isoPullback.hom ≫ pullback.fst Xo.hom (c.π.app i) = κ :=
      hXi.isoPullback_hom_fst
    have e2 : hXi.isoPullback.hom ≫ pullback.snd Xo.hom (c.π.app i) = s :=
      hXi.isoPullback_hom_snd
    have e3 : α.hom.left ≫ pullback.snd Xo.hom (c.π.app i) =
        pullback.snd ((Over.pullback (D.map e)).obj Xo).hom (c.π.app j) := Over.w α.hom
    have hlmρ₀ : lm ≫ ρ₀ = κ := by
      apply pullback.hom_ext
      · rw [Category.assoc, hρ₀1, hlm1, hκ1]
      · rw [Category.assoc, hρ₀2, ← Category.assoc, hlm2, hκ2, Category.assoc, c.w (hm ≫ e)]
    have hθα : θ ≫ α.hom.left = hXi.isoPullback.hom := by
      apply pullback.hom_ext
      · rw [Category.assoc, hα, ← Category.assoc, hθ1, e1, Category.assoc, hρ1, hlmρ₀]
      · rw [Category.assoc, e3, e2, hθ2]
    have hleft : α.hom.left ≫ fo.left = ((Over.pullback (c.π.app j)).map g).left ≫ β.hom.left :=
      congrArg Over.Hom.left hcomm
    have hβ' : β.hom.left ≫ pullback.fst p (c.π.app i) =
        pullback.fst ((Over.pullback (D.map e)).obj Yo).hom (c.π.app j) ≫
          pullback.fst p (D.map e) := hβ
    have hmap : ((Over.pullback (c.π.app j)).map g).left ≫
        pullback.fst ((Over.pullback (D.map e)).obj Yo).hom (c.π.app j) =
          pullback.fst ((Over.pullback (D.map e)).obj Xo).hom (c.π.app j) ≫ g.left := by
      simp only [Over.pullback_map_left, pullback.lift_fst]
    have hfo : hXi.isoPullback.hom ≫ fo.left ≫ pullback.fst p (c.π.app i) = F ≫ a := by
      change hXi.isoPullback.hom ≫ (hXi.isoPullback.inv ≫ F ≫ hpb.isoPullback.hom) ≫
        pullback.fst p (c.π.app i) = F ≫ a
      simp only [Category.assoc, Iso.hom_inv_id_assoc, hpb.isoPullback_hom_fst]
    calc lm ≫ ρ ≫ g.left ≫ pullback.fst p (D.map e)
        = θ ≫ pullback.fst ((Over.pullback (D.map e)).obj Xo).hom (c.π.app j) ≫ g.left ≫
            pullback.fst p (D.map e) := by
          rw [← Category.assoc θ, hθ1, Category.assoc]
      _ = θ ≫ ((Over.pullback (c.π.app j)).map g).left ≫
            pullback.fst ((Over.pullback (D.map e)).obj Yo).hom (c.π.app j) ≫
              pullback.fst p (D.map e) := by
          rw [← Category.assoc (pullback.fst _ _) g.left, ← hmap, Category.assoc]
      _ = θ ≫ ((Over.pullback (c.π.app j)).map g).left ≫ β.hom.left ≫
            pullback.fst p (c.π.app i) := by
          rw [hβ']
      _ = θ ≫ α.hom.left ≫ fo.left ≫ pullback.fst p (c.π.app i) := by
          rw [← Category.assoc _ β.hom.left, ← hleft, Category.assoc]
      _ = F ≫ a := by
          rw [← Category.assoc θ, hθα, hfo]

open CategoryTheory.Limits in
/-- A flat proper model at some stage. -/
private theorem exists_flat_proper_model
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    [∀ i, AlgebraicGeometry.IsNoetherian (D.obj i)]
    {S' : Scheme.{u}} (φ : S' ⟶ c.pt) [Flat φ] [IsProper φ] [LocallyOfFinitePresentation φ] :
    ∃ (j : I) (W : Scheme.{u}) (p : W ⟶ D.obj j) (a : S' ⟶ W), IsPullback a φ p (c.π.app j) ∧
      Flat p ∧ IsProper p ∧ LocallyOfFinitePresentation p := by
  have hqc : QuasiCompact φ := instQuasiCompactOfUniversallyClosed φ
  have hqs : QuasiSeparated φ := IsSeparated.instQuasiSeparated φ
  have hφfp : FinitePresentation φ :=
    ⟨‹LocallyOfFinitePresentation φ›, hqc, hqs⟩
  obtain ⟨i, Z, hZfp, hZflat, ⟨e⟩⟩ := exists_flat_model_of_small_limit D c hc φ hφfp
  have hpbC : IsPullback (e.hom.left ≫ pullback.fst Z.hom (c.π.app i)) φ Z.hom (c.π.app i) := by
    have hw : e.hom.left ≫ pullback.snd Z.hom (c.π.app i) = φ := Over.w e.hom
    refine IsPullback.of_iso_pullback ⟨?_⟩ ((Over.forget _).mapIso e) rfl hw
    rw [Category.assoc, pullback.condition, ← Category.assoc, hw]
  have hZp : IsProper (pullback.snd Z.hom (c.π.app i)) := by
    rw [← hpbC.isoPullback_inv_snd]
    infer_instance
  have : LocallyOfFinitePresentation Z.hom := hZfp.1
  have : QuasiCompact Z.hom := hZfp.2.1
  have : QuasiSeparated Z.hom := hZfp.2.2
  have : Flat Z.hom := hZflat
  have : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  have : QuasiSeparatedSpace Z.left := quasiSeparatedSpace_of_quasiSeparated Z.hom
  have : CompactSpace (Over.mk (𝟙 (D.obj i))).left := inferInstanceAs (CompactSpace (D.obj i))
  have : QuasiSeparatedSpace (Over.mk (𝟙 (D.obj i))).left :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj i))
  let f₀ : Z ⟶ Over.mk (𝟙 (D.obj i)) := Over.homMk Z.hom (by simp)
  have : LocallyOfFiniteType f₀.left := inferInstanceAs (LocallyOfFiniteType Z.hom)
  have : IsProper ((Over.pullback (c.π.app i)).map f₀).left :=
    (overPullback_map_homMk_left_iff @IsProper Z.hom (c.π.app i)).mpr hZp
  obtain ⟨j, w, hprop⟩ := exists_isProper_baseChange_of_isLimit D c i hc Z _ f₀
  have hprop' : IsProper (pullback.snd Z.hom (D.map w)) :=
    (overPullback_map_homMk_left_iff @IsProper Z.hom (D.map w)).mp hprop
  exact ⟨j, _, pullback.snd Z.hom (D.map w), _, IsPullback.pullbackSnd_of_isLimit c w hpbC,
    inferInstance, hprop', inferInstance⟩

end Spreading

/-- **Spreading out and specialising a contraction.** Let `k₀ ⊆ K` be algebraically closed
fields, `X₀` a normal projective variety over `k₀` with base change `X` to `K`, and
`f : X ⟶ Z` the contraction of the transport of an extremal ray `R₀` of `NE̅(X₀)`, onto a
projective variety. Then some morphism `f_x : X₀ ⟶ Z_x` to a projective `k₀`-scheme contracts
exactly the curves of `X₀` whose class lies in `R₀`. -/
private theorem exists_isContractedBy_iff_of_isContractionOfRay
    {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K] [IsAlgClosed k₀] [IsAlgClosed K]
    {X₀ X : Scheme.{u}} (s₀ : X₀ ⟶ Spec (.of k₀)) (s : X ⟶ Spec (.of K)) (π : X ⟶ X₀)
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) [IsNormal X₀]
    (φ : NumericalCurveClasses s₀ →ₗ[ℝ] NumericalCurveClasses s)
    (hφ : ∀ (C₀ : ProperCurve s₀) (C : ProperCurve s),
      closure {C.point} = π.base ⁻¹' closure {C₀.point} →
        φ (OneCycle.numericalClass s₀ (C₀.cycle ℝ)) = OneCycle.numericalClass s (C.cycle ℝ))
    {R₀ : Set (NumericalCurveClasses s₀)}
    (hR₀ : IsExtremalRay ℝ (closedConeOfCurves s₀ : Set (NumericalCurveClasses s₀)) R₀)
    {Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of K)) (f : X ⟶ Z)
    (hf : IsContractionOfRay s sZ (φ '' R₀) f) (hZ : MMP.Mori.IsProjectiveVariety K sZ) :
    ∃ (Zx : Scheme.{u}) (tx : Zx ⟶ Spec (.of k₀)) (fx : X₀ ⟶ Zx),
      fx ≫ tx = s₀ ∧ LocallyOfFiniteType tx ∧ IsSeparated tx ∧ IsProjectiveMorphism tx ∧
        ∀ C : ProperCurve s₀, C.IsContractedBy fx ↔ OneCycle.numericalClass s₀ (C.cycle ℝ) ∈ R₀ := by
  classical
  -- `Spec K` as the limit of the spectra of the finitely generated `k₀`-subalgebras of `K`
  let D : (AlgebraicGeometry.FieldExtensionDescent.FGSubalgebra k₀ K)ᵒᵖ ⥤ Scheme.{u} :=
    AlgebraicGeometry.FieldExtensionDescent.specDiagram k₀ K ⋙ Over.forget _
  let c₀ : Cone D :=
    (Over.forget _).mapCone (AlgebraicGeometry.FieldExtensionDescent.specLimitCone k₀ K).cone
  have hc₀ : IsLimit c₀ :=
    isLimitOfPreserves _ (AlgebraicGeometry.FieldExtensionDescent.specLimitCone k₀ K).isLimit
  let c : Cone D := { pt := Spec (.of K), π := c₀.π }
  have hc : IsLimit c := hc₀
  have : ∀ {i j : (AlgebraicGeometry.FieldExtensionDescent.FGSubalgebra k₀ K)ᵒᵖ} (e : i ⟶ j),
      IsAffineHom (D.map e) := by
    intro i j e
    change IsAffineHom (Spec.map _)
    infer_instance
  have : ∀ i, CompactSpace (D.obj i) := fun i => by
    change CompactSpace (Spec _)
    infer_instance
  have : ∀ i, QuasiSeparatedSpace (D.obj i) := fun i => by
    change QuasiSeparatedSpace (Spec _)
    infer_instance
  have : ∀ i, AlgebraicGeometry.IsNoetherian (D.obj i) := fun i => by
    have : Algebra.FiniteType k₀ (i.unop : Subalgebra k₀ K) :=
      AlgebraicGeometry.FieldExtensionDescent.finiteType_coe k₀ K i.unop
    have : IsNoetherianRing (i.unop : Subalgebra k₀ K) := Algebra.FiniteType.isNoetherianRing k₀ _
    change AlgebraicGeometry.IsNoetherian (Spec (CommRingCat.of (i.unop : Subalgebra k₀ K)))
    infer_instance
  let σ : ∀ i, D.obj i ⟶ Spec (.of k₀) :=
    fun i => ((AlgebraicGeometry.FieldExtensionDescent.specDiagram k₀ K).obj i).hom
  have hσ : ∀ {i j : (AlgebraicGeometry.FieldExtensionDescent.FGSubalgebra k₀ K)ᵒᵖ} (e : j ⟶ i),
      D.map e ≫ σ i = σ j :=
    fun e => Over.w ((AlgebraicGeometry.FieldExtensionDescent.specDiagram k₀ K).map e)
  have hcσ : ∀ i, c.π.app i ≫ σ i = Spec.map (CommRingCat.ofHom (algebraMap k₀ K)) :=
    fun i => Over.w ((AlgebraicGeometry.FieldExtensionDescent.specLimitCone k₀ K).cone.π.app i)
  -- a proper model of `Z` at some stage
  have hv : AlgebraicGeometry.IsVariety K sZ := hZ.toIsVariety
  have hPr : IsProper sZ := isProper_of_isProjectiveMorphism _ hZ.isProjective
  haveI : LocallyOfFiniteType sZ := hv.toLocallyOfFiniteType
  have hFl : Flat sZ := inferInstance
  have hLf : LocallyOfFinitePresentation sZ :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  obtain ⟨i, W, pW, a, hpb, -, hpr, hlfp⟩ :=
    @exists_flat_proper_model _ _ _ D c hc _ _ _ _ _ sZ hFl hPr hLf
  have hpfp : FinitePresentation pW := ⟨hlfp, inferInstance, inferInstance⟩
  -- an ample sheaf on `Z` and the morphism `f`, at a common stage `m`
  obtain ⟨H, hHinv, hHa⟩ := exists_isAmple_of_isProjectiveVariety hZ
  obtain ⟨b, -, hA⟩ := exists_isAmple_stage D c hc i pW a sZ hpb H hHa
  have hv₀ : AlgebraicGeometry.IsVariety k₀ s₀ := hX₀.toIsVariety
  haveI : LocallyOfFiniteType s₀ := hv₀.toLocallyOfFiniteType
  haveI : IsProper s₀ := isProper_of_isProjectiveMorphism _ hX₀.isProjective
  haveI : LocallyOfFinitePresentation s₀ :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  obtain ⟨j, hj, hB⟩ := exists_morphism_stage D c hc s₀ σ hσ _ hcσ i pW hpfp a sZ hpb π s h f
    hf.comp_eq
  let m := IsCofiltered.min b j
  let hmi : m ⟶ i := IsCofiltered.minToRight b j ≫ hj
  obtain ⟨M, hMinv, hMa, ⟨eM⟩⟩ := hA m (IsCofiltered.minToLeft b j) hmi
  obtain ⟨v, hv₁, hv₂⟩ := hB m (IsCofiltered.minToRight b j) hmi
  -- the base `S = Spec A_m` and a `k₀`-point of it
  haveI : IsIntegral (D.obj m) := by
    change IsIntegral (Spec (CommRingCat.of (m.unop : Subalgebra k₀ K)))
    infer_instance
  haveI : LocallyOfFiniteType (σ m) := by
    have : Algebra.FiniteType k₀ (m.unop : Subalgebra k₀ K) :=
      AlgebraicGeometry.FieldExtensionDescent.finiteType_coe k₀ K m.unop
    change LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ (m.unop : Subalgebra k₀ K))))
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  haveI : QuasiCompact (σ m) := by
    change QuasiCompact (Spec.map _)
    infer_instance
  haveI : IsDominant (c.π.app m) := by
    change IsDominant (Spec.map (CommRingCat.ofHom (algebraMap (m.unop : Subalgebra k₀ K) K)))
    exact AlgebraicGeometry.isDominant_Spec_map_of_injective _ Subtype.val_injective
  obtain ⟨x₁, hx⟩ := exists_comp_specMap_eq_id (m.unop : Subalgebra k₀ K) m.unop.2
  let x : Spec (.of k₀) ⟶ D.obj m := x₁
  have hx' : x ≫ σ m = 𝟙 _ := hx
  -- the spread data
  haveI : IsAffine (D.obj m) := by
    change IsAffine (Spec _)
    infer_instance
  set t := pullback.fst (D.map hmi) pW
  haveI : IsProper t := inferInstance
  haveI := (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
    (pullback (D.map hmi) pW).presheaf _ M).mpr hMinv
  have hMs : Stacks.Ample.IsAmple _ M :=
    (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple _ _).mp hMa
  have hMr : Stacks.RelativeAmple.IsRelativelyAmple t M :=
    (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple t M).mpr hMs
  have htp : IsProjectiveMorphism t :=
    AlgebraicGeometry.isProjectiveMorphism_of_isProper_of_isRelativelyAmple_of_isAffine t M hMr
  have hq : IsProjectiveMorphism (pullback.snd s₀ (σ m)) := hX₀.isProjective.baseChange _
  have hvp : IsProjectiveMorphism v := IsProjectiveMorphism.of_comp v t (by rw [hv₁]; exact hq)
  let ι : X ⟶ pullback s₀ (σ m) :=
    pullback.lift π (s ≫ c.π.app m) (by rw [h.w, Category.assoc, hcσ])
  let ιZ : Z ⟶ pullback (D.map hmi) pW :=
    pullback.lift (sZ ≫ c.π.app m) a (by rw [Category.assoc, c.w hmi, hpb.w])
  have hZpb : IsPullback ιZ sZ t (c.π.app m) := by
    have H : IsPullback (ιZ ≫ pullback.snd (D.map hmi) pW) sZ pW (c.π.app m ≫ D.map hmi) := by
      rw [pullback.lift_snd, c.w hmi]
      exact hpb
    exact IsPullback.of_right H (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback _ _).flip
  haveI := MMP.Mori.isInvertible_pullback_obj ιZ M
  have hH : Stacks.Ample.IsAmple Z
      ((RingedSpaceModuleAdjunction.modulePullback ιZ.toLRSHom.toShHom).obj M) :=
    (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple _ _).mp
      (Scheme.Modules.isAmple_of_iso eM.symm hHa)
  let j₀ : X₀ ⟶ pullback s₀ (σ m) := pullback.lift (𝟙 X₀) (s₀ ≫ x)
    (by rw [Category.id_comp, Category.assoc, hx', Category.comp_id])
  let fx : X₀ ⟶ pullback t x := pullback.lift (j₀ ≫ v) s₀ (by
    rw [Category.assoc, hv₁, pullback.lift_snd])
  have key := IsContractionOfRay.isContractedBy_fibre_iff s₀ s π h hX₀ φ hφ hR₀ sZ f hf (σ m)
    (c.π.app m) (hcσ m) (pullback.fst s₀ (σ m)) (pullback.snd s₀ (σ m))
    (IsPullback.of_hasPullback _ _) t v hv₁ hvp M (IsRelativelyAmple.of_stacks _ _ hMr) ι
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) ιZ hZpb hv₂.symm hH x hx' j₀
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) (pullback.snd t x) (pullback.fst t x)
    (IsPullback.of_hasPullback t x) fx (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  haveI : LocallyOfFiniteType t := inferInstance
  haveI : IsSeparated t := inferInstance
  have h1 : LocallyOfFiniteType (pullback.snd t x) := inferInstance
  have h2 : IsSeparated (pullback.snd t x) := inferInstance
  exact ⟨pullback t x, pullback.snd t x, fx, pullback.lift_snd _ _ _, h1, h2,
    htp.baseChange _, key⟩

/-- On a log canonical pair `K + B` is `ℚ`-Cartier, for every canonical divisor `K`. -/
theorem isQCartier_of_isLogCanonicalPair {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} {K : Divisor X} {B : QDivisor X}
    (hlc : MMP.Intersection.IsLogCanonicalPair sX B) (hK : ∃ n : ℕ, K.IsCanonicalDivisor sX n) :
    (Divisor.toQDivisor K + B).IsQCartier := by
  obtain ⟨n, hn⟩ := hK
  obtain ⟨m, K', hK', hQ⟩ := hlc.1.isQCartier_of_linearlyEquivalent
  exact hQ K (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX hlc.1.1 hn hK')

/-- The models of the program without steps are all `X`. -/
private def constSeqHom {X₀ X : Scheme.{u}} (π : X ⟶ X₀) :
    ∀ i, modelSeq X (fun _ => X) i ⟶ modelSeq X₀ (fun _ => X₀) i
  | 0 => π
  | _ + 1 => π

/-- The identification of the models of the program without steps with `X`. -/
private def constSeqTo (X : Scheme.{u}) : ∀ i, modelSeq X (fun _ => X) i ⟶ X
  | 0 => 𝟙 X
  | _ + 1 => 𝟙 X

/-- The program from `(X, B)` with no step and no final contraction. -/
private def trivialProgram {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    {K : Divisor X} {B : QDivisor X}
    (hproj : MMP.Mori.IsProjectiveVariety k sX) (hlc : MMP.Intersection.IsLogCanonicalPair sX B)
    (hK : ∃ n : ℕ, K.IsCanonicalDivisor sX n) : Program sX K B where
  n := 0
  Y _ := X
  sY _ := sX
  KY _ := K
  BY _ := B
  R _ := ∅
  Z _ := X
  sZ _ := sX
  f := constSeqTo X
  fp _ := 𝟙 X
  isProjectiveVariety := hproj
  isLogCanonicalPair := hlc
  isCanonicalDivisor := hK
  isPermittedStep i hi := absurd hi (by simp)
  KY_eq i hi := absurd hi (by simp)
  BY_eq i hi := absurd hi (by simp)
  hasFinal := False
  finalRay := ∅
  T := X
  sT := sX
  g := constSeqTo X _
  final_spec h := h.elim

/-- **Descent of the pair.** A projective lc pair over `k` is the base change of a projective lc
pair over a countable algebraically closed subfield `k₀ ⊆ k`, with base-changed canonical divisor
and boundary. -/
private theorem exists_descent {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {K : Divisor X} {B : QDivisor X}
    (hproj : MMP.Mori.IsProjectiveVariety k sX) (hlc : MMP.Intersection.IsLogCanonicalPair sX B)
    (hK : ∃ n : ℕ, K.IsCanonicalDivisor sX n) :
    ∃ (k₀ : Subfield k) (_ : Countable k₀) (_ : IsAlgClosed k₀)
      (X₀ : Scheme.{0}) (_ : IsIntegral X₀) (_ : CompactSpace X₀) (_ : IsLocallyNoetherian X₀)
      (_ : IsNormal X₀) (s₀ : X₀ ⟶ Spec (.of k₀)) (K₀ : Divisor X₀) (B₀ : QDivisor X₀)
      (π : X ⟶ X₀),
      IsPullback π sX s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ k))) ∧
      MMP.Mori.IsProjectiveVariety k₀ s₀ ∧ MMP.Intersection.IsLogCanonicalPair s₀ B₀ ∧
      (∃ n : ℕ, K₀.IsCanonicalDivisor s₀ n) ∧ IsBaseChange π K₀ K ∧ IsBaseChange π B₀ B := by
  obtain ⟨k₀, hc, ha, X₀, _, _, _, _, s₀, K₀, B₀, P₀, -, πX, -, -, h0, -, -, -⟩ :=
    (trivialProgram hproj hlc hK).exists_countable_isAlgClosed_subfield_program
  obtain ⟨hpb, hcoef, hzero⟩ := h0 0 (by simp [trivialProgram])
  have hpb' : IsPullback (πX 0) sX s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ k))) := hpb
  have hproj₀ : MMP.Mori.IsProjectiveVariety k₀ s₀ := P₀.isProjectiveVariety
  haveI : LocallyOfFiniteType s₀ := hproj₀.toLocallyOfFiniteType
  exact ⟨k₀, hc, ha, X₀, inferInstance, inferInstance, inferInstance, inferInstance, s₀, K₀, B₀,
    πX 0, hpb', hproj₀, P₀.isLogCanonicalPair, P₀.isCanonicalDivisor,
    isBaseChange_of_coeff (s₀ := s₀) hpb' (fun E E₀ hE => (hcoef E E₀ hE).1) (fun E hE => (hzero E hE).1),
    isBaseChange_of_coeff (s₀ := s₀) hpb' (fun E E₀ hE => (hcoef E E₀ hE).2) (fun E hE => (hzero E hE).2)⟩

/-- **The contraction over a countable algebraically closed field.** -/
private theorem exists_of_countable {k₀ : Type} [Field k₀] [IsAlgClosed k₀] [CharZero k₀]
    [Countable k₀] {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Spec (.of k₀)} [IsIntegral X₀]
    [CompactSpace X₀] [IsLocallyNoetherian X₀] [IsNormal X₀] {K₀ : Divisor X₀} {B₀ : QDivisor X₀}
    (hproj : MMP.Mori.IsProjectiveVariety k₀ s₀) (hlc : MMP.Intersection.IsLogCanonicalPair s₀ B₀)
    (hK : ∃ n : ℕ, K₀.IsCanonicalDivisor s₀ n) (hdim : topologicalKrullDim X₀ = 4)
    {R₀ : Set (NumericalCurveClasses s₀)}
    (hR : IsNegativeExtremalRayOf s₀ (Divisor.toQDivisor K₀ + B₀) R₀) :
    ∃ (Z : Scheme.{0}) (sZ : Z ⟶ Spec (.of k₀)) (f : X₀ ⟶ Z),
      IsContractionOfRay s₀ sZ R₀ f ∧ MMP.Mori.IsProjectiveVariety k₀ sZ ∧
        relativePicardNumberN1 s₀ f = 1 ∧
        (-(Divisor.toQDivisor K₀ + B₀)).HasRelativelyAmpleMultiple f := by
  classical
  obtain ⟨σ⟩ := MMP.Resolution.Bridges.nonempty_ringHom_complex_and_countable_algebraicClosure.1 k₀
  letI : Algebra k₀ ℂ := σ.toAlgebra
  haveI : LocallyOfFiniteType s₀ := hproj.toLocallyOfFiniteType
  set φC := Spec.map (CommRingCat.ofHom (algebraMap k₀ ℂ))
  have hC : IsPullback (pullback.fst s₀ φC) (pullback.snd s₀ φC) s₀ φC :=
    IsPullback.of_hasPullback _ _
  set XC := pullback s₀ φC
  set πC := pullback.fst s₀ φC
  set sC := pullback.snd s₀ φC
  obtain ⟨_, _, _, _⟩ := isIntegral_isNormal_of_isPullback s₀ sC πC hC hproj
  obtain ⟨KC, hKC⟩ : ∃ KC : Divisor XC, IsBaseChange πC K₀ KC := exists_isBaseChange hC K₀
  obtain ⟨BC, hBC⟩ : ∃ BC : QDivisor XC, IsBaseChange πC B₀ BC := exists_isBaseChange hC B₀
  let eC := numericalCurveClassesBaseChange s₀ sC πC hC hproj
  have heC := numericalCurveClassesBaseChange_eq_of_isPullback s₀ sC πC hC hproj
  -- the pair over `ℂ`
  have hiff := program_conditions_iff_of_isPullback (K := ℂ) 0 False s₀ K₀ B₀
    (Y₀ := fun _ => X₀) (fun _ => s₀) (fun _ => K₀) (fun _ => B₀) (fun _ => ∅)
    (fun i hi => absurd hi (by simp)) (Z₀ := fun _ => X₀) (fun _ => s₀) (constSeqTo X₀)
    (fun i hi => absurd hi (by simp)) (fun _ => 𝟙 X₀) (fun i hi => absurd hi (by simp)) ∅
    (fun h => h.elim) s₀ (constSeqTo X₀ _) (fun h => h.elim) sC KC BC (Y := fun _ => XC)
    (fun _ => sC) (fun _ => KC) (fun _ => BC) (fun _ => ∅) (Z := fun _ => XC) (fun _ => sC)
    (constSeqTo XC) (fun i hi => absurd hi (by simp)) (fun _ => 𝟙 XC)
    (fun i hi => absurd hi (by simp)) ∅ sC (constSeqTo XC _) (fun h => h.elim)
    (constSeqHom πC) (fun i hi => by obtain rfl : i = 0 := (by simpa using hi); exact hC)
    (fun _ => πC) (fun i hi => absurd hi (by simp)) πC (fun h => h.elim)
    (fun i hi => absurd hi (by simp)) (fun i hi => absurd hi (by simp)) (fun h => h.elim)
    (fun i hi P₀ P hP => by
      obtain rfl : i = 0 := by simpa using hi
      exact ⟨hKC.1 P₀ P hP, hBC.1 P₀ P hP⟩)
    (fun i hi P hP => by
      obtain rfl : i = 0 := by simpa using hi
      rcases hP with hP | hP
      · exact hKC.2 P hP
      · exact hBC.2 P hP)
    (fun i => match i with
      | 0 => eC.toLinearMap
      | _ + 1 => 0)
    (fun i hi => by obtain rfl : i = 0 := (by simpa using hi); exact heC)
    (fun i hi => absurd hi (by simp)) (fun h => h.elim)
  obtain ⟨hprojC, hlcC, hKC', -⟩ := hiff.mp ⟨hproj, hlc, hK, fun i hi => absurd hi (by simp),
    fun i hi => absurd hi (by simp), fun i hi => absurd hi (by simp), fun h => h.elim⟩
  have hdimC : topologicalKrullDim XC = 4 :=
    (topologicalKrullDim_eq_of_isPullback s₀ sC πC hC hproj).trans hdim
  have hKC4 : KC.IsCanonicalDivisor sC 4 := by
    obtain ⟨m, hm⟩ := hKC'
    have h4 : (m : WithBot ℕ∞) = 4 := hm.1.symm.trans hdimC
    obtain rfl : m = 4 := by exact_mod_cast h4
    exact hm
  have hDC : IsBaseChange πC (Divisor.toQDivisor K₀ + B₀) (Divisor.toQDivisor KC + BC) :=
    hKC.toQDivisor.add hBC
  have hQ₀ := isQCartier_of_isLogCanonicalPair hlc hK
  have hQC := isQCartier_of_isLogCanonicalPair hlcC hKC'
  have hRC := (isNegativeExtremalRayOf_iff hC hproj hDC hR.1 hQC eC.toLinearMap heC R₀).mp hR
  -- the complex contraction
  obtain ⟨Z, sZ, fC, hfC, hZC, hρC, haC⟩ :=
    exists_isContractionOfRay_of_isNegativeExtremalRayOf sC hprojC hdimC hKC4 hlcC hRC
  -- spreading out and specialising
  obtain ⟨Zx, tx, fx, hfx, hlft, hsep, hprx, hcontr⟩ :=
    exists_isContractedBy_iff_of_isContractionOfRay s₀ sC πC hC hproj eC.toLinearMap heC
      hR.2.1 sZ fC hfC hZC
  -- its Stein factorization is a contraction of `R₀`
  haveI : AlgebraicGeometry.IsVariety k₀ s₀ := hproj.toIsVariety
  haveI : IsProper s₀ := isProper_of_isProjectiveMorphism _ hproj.isProjective
  haveI : IsProper fx := by
    have : IsProper (fx ≫ tx) := by rw [hfx]; infer_instance
    exact IsProper.of_comp fx tx
  obtain ⟨Y', f', g, ⟨hS⟩, -, hsurj, hiso, -, -, -, hprojY, hnorm, -, hcon⟩ :=
    MMP.Resolution.Bridges.exists_steinFactorization_of_isVariety s₀ tx fx hfx
  have hY' : MMP.Mori.IsProjectiveVariety k₀ (g ≫ tx) := hprojY hprx
  haveI : IsNormal Y' := hnorm inferInstance
  have hcomp : f' ≫ g ≫ tx = s₀ := by rw [← Category.assoc, hS.comp, hfx]
  haveI : IsSeparated (g ≫ tx) := hY'.toIsSeparated
  have hc₀ : IsContractionOfRay s₀ (g ≫ tx) R₀ f' :=
    { isNormalVariety_source := ⟨hproj.toIsVariety, inferInstance⟩
      isNormalVariety_target := ⟨hY'.toIsVariety, inferInstance⟩
      comp_eq := hcomp
      isProjectiveMorphism :=
        IsProjectiveMorphism.of_comp f' (g ≫ tx) (by rw [hcomp]; exact hproj.isProjective)
      surjective := hsurj.surj
      isIso_app := hiso
      isContractedBy_iff := fun C => (hcon C).symm.trans (hcontr C) }
  -- its base change to `ℂ` is a contraction of the complex ray
  have hYC : IsPullback (pullback.fst (g ≫ tx) φC) (pullback.snd (g ≫ tx) φC) (g ≫ tx) φC :=
    IsPullback.of_hasPullback _ _
  let f'C : XC ⟶ pullback (g ≫ tx) φC :=
    pullback.lift (πC ≫ f') sC (by rw [Category.assoc, hcomp, hC.w])
  have hf'C : f'C ≫ pullback.snd (g ≫ tx) φC = sC := pullback.lift_snd _ _ _
  have hf'Cπ : f'C ≫ pullback.fst (g ≫ tx) φC = πC ≫ f' := pullback.lift_fst _ _ _
  have hcC := isContractionOfRay_iff hC hYC hproj hY' f' hcomp f'C hf'C hf'Cπ eC.toLinearMap
    heC R₀ |>.mp hc₀
  -- the two complex contractions of the ray agree up to an isomorphism of the targets
  obtain ⟨eZ, hf'Ceq⟩ := exists_iso_of_isContractionOfRay hprojC hRC.2.1 hfC hcC
  -- descent of `ρ = 1` and of the relative ampleness of `-D`
  refine ⟨Y', g ≫ tx, f', hc₀, hY', ?_, ?_⟩
  · rw [relativePicardNumberN1_eq hC hYC hproj hY' f' hcomp f'C hf'C hf'Cπ, hf'Ceq,
      relativePicardNumberN1_comp_iso, hρC]
  · rw [hasRelativelyAmpleMultiple_iff hC hYC hproj hY' f' hcomp f'C hf'C hf'Cπ hDC.neg
      (neg_isQCartier hQ₀), hf'Ceq, hasRelativelyAmpleMultiple_comp_iso]
    exact haC

private theorem solution : ∀ {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {K : Divisor X} {B : QDivisor X}
    (hproj : MMP.Mori.IsProjectiveVariety k sX) (hlc : MMP.Intersection.IsLogCanonicalPair sX B)
    (hK : ∃ n : ℕ, K.IsCanonicalDivisor sX n) (hdim : topologicalKrullDim X = 4)
    {R : Set (NumericalCurveClasses sX)}
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R),
    ∃ (Z : Scheme.{0}) (sZ : Z ⟶ Spec (.of k)) (f : X ⟶ Z),
      IsContractionOfRay sX sZ R f ∧ MMP.Mori.IsProjectiveVariety k sZ ∧
        relativePicardNumberN1 sX f = 1 ∧
        (-(Divisor.toQDivisor K + B)).HasRelativelyAmpleMultiple f := by
  intro k _ _ _ X sX _ _ _ _ K B hproj hlc hK hdim R hR
  obtain ⟨k₀, _, _, X₀, _, _, _, _, s₀, K₀, B₀, π, hπ, hproj₀, hlc₀, hK₀, hKb, hBb⟩ :=
    exists_descent hproj hlc hK
  have hdim₀ : topologicalKrullDim X₀ = 4 :=
    (topologicalKrullDim_eq_of_isPullback s₀ sX π hπ hproj₀).symm.trans hdim
  have hDb : IsBaseChange π (Divisor.toQDivisor K₀ + B₀) (Divisor.toQDivisor K + B) :=
    hKb.toQDivisor.add hBb
  have hQ₀ := isQCartier_of_isLogCanonicalPair hlc₀ hK₀
  let e := numericalCurveClassesBaseChange s₀ sX π hπ hproj₀
  have he := numericalCurveClassesBaseChange_eq_of_isPullback s₀ sX π hπ hproj₀
  have hRe : e '' (e ⁻¹' R) = R := Set.image_preimage_eq R e.surjective
  have hR₀ : IsNegativeExtremalRayOf s₀ (Divisor.toQDivisor K₀ + B₀) (e ⁻¹' R) := by
    rw [isNegativeExtremalRayOf_iff hπ hproj₀ hDb hQ₀ hR.1 e.toLinearMap he, LinearEquiv.coe_coe,
      hRe]
    exact hR
  obtain ⟨Z₀, t₀, f₀, hc₀, hZ₀, hρ₀, ha₀⟩ := exists_of_countable hproj₀ hlc₀ hK₀ hdim₀ hR₀
  set φk := Spec.map (CommRingCat.ofHom (algebraMap k₀ k))
  have hZ : IsPullback (pullback.fst t₀ φk) (pullback.snd t₀ φk) t₀ φk :=
    IsPullback.of_hasPullback t₀ φk
  let f : X ⟶ pullback t₀ φk := pullback.lift (π ≫ f₀) sX (by rw [Category.assoc, hc₀.comp_eq, hπ.w])
  have hf : f ≫ pullback.snd t₀ φk = sX := pullback.lift_snd _ _ _
  have hfπ : f ≫ pullback.fst t₀ φk = π ≫ f₀ := pullback.lift_fst _ _ _
  refine ⟨pullback t₀ φk, pullback.snd t₀ φk, f, ?_, ?_, ?_, ?_⟩
  · have := (isContractionOfRay_iff hπ hZ hproj₀ hZ₀ f₀ hc₀.comp_eq f hf hfπ
      e.toLinearMap he (e ⁻¹' R)).mp hc₀
    rwa [LinearEquiv.coe_coe, hRe] at this
  · exact (isProjectiveVariety_iff_of_isPullback t₀ _ _ hZ).1 hZ₀
  · rw [← relativePicardNumberN1_eq hπ hZ hproj₀ hZ₀ f₀ hc₀.comp_eq f hf hfπ, hρ₀]
  · exact (hasRelativelyAmpleMultiple_iff hπ hZ hproj₀ hZ₀ f₀ hc₀.comp_eq f hf hfπ hDb.neg
      (neg_isQCartier hQ₀)).1 ha₀

end Proof_lem_oai4_finite_existence_transfer_b

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori

/-- **Contractions exist over any algebraically closed field of characteristic zero.** Let
`(X, B)` be a projective lc fourfold pair over `k` with canonical divisor `K`, and `R` a
`(K + B)`-negative extremal ray of `NE̅(X)`. Then `R` has a contraction `f : X ⟶ Z` onto a normal
projective variety over `k` (so `f_* 𝒪_X = 𝒪_Z`), with `ρ(X/Z) = 1` and `-(K + B)` `f`-ample. -/
@[mmp "lem_oai4_finite_existence_transfer_b"]
public theorem exists_isContractionOfRay_of_isNegativeExtremalRayOf_of_isAlgClosed {k : Type}
    [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {K : Divisor X} {B : QDivisor X}
    (hproj : MMP.Mori.IsProjectiveVariety k sX) (hlc : MMP.Intersection.IsLogCanonicalPair sX B)
    (hK : ∃ n : ℕ, K.IsCanonicalDivisor sX n) (hdim : topologicalKrullDim X = 4)
    {R : Set (NumericalCurveClasses sX)}
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R) :
    ∃ (Z : Scheme.{0}) (sZ : Z ⟶ Spec (.of k)) (f : X ⟶ Z),
      IsContractionOfRay sX sZ R f ∧ MMP.Mori.IsProjectiveVariety k sZ ∧
        relativePicardNumberN1 sX f = 1 ∧
        (-(Divisor.toQDivisor K + B)).HasRelativelyAmpleMultiple f :=
          by revert k X sX K B hproj hlc hK hdim R hR; first | exact Proof_lem_oai4_finite_existence_transfer_b.solution | exact Proof_lem_oai4_finite_existence_transfer_b.solution _ | exact Proof_lem_oai4_finite_existence_transfer_b.solution _ _ | exact Proof_lem_oai4_finite_existence_transfer_b.solution _ _ _ | exact Proof_lem_oai4_finite_existence_transfer_b.solution _ _ _ _

end MMP.Fourfold

