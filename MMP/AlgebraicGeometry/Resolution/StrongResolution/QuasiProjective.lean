module
public import MMP.AlgebraicGeometry.Resolution.StrongResolution.Embeddable
import MMP.AlgebraicGeometry.Morphisms.ChowLemma
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Resolution.StrongResolutionCharZero
import MMP.AlgebraicGeometry.Resolution.CommonNormalModel
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import StacksFrontier.AlgebraicGeometry.NagataCompactification.Basic

/-!
# Strong resolution of quasi-projective varieties, and common smooth projective models

Two consequences of strong resolution over a field `k` of characteristic `0`.

A quasi-projective variety `X` over `k` has a strong resolution: a projective birational morphism
`Π : R(X) → X` from a smooth variety which is an isomorphism over the smooth locus `X^ns` and such
that `Π⁻¹(Sing X)` is a divisor with simple normal crossings. Since `X` is H-quasi-projective over
`Spec k`, it is immersed in some `ℙᴺ_k`, a smooth variety, and this is the case `P = ℙᴺ_k` of
`MMP.Resolution.exists_strongResolution_of_isImmersion`.

Given finitely many proper birational morphisms `f_i : X_i ⟶ S` from normal varieties onto a
normal variety `S`, and finitely many divisorial valuations `v_j` of `k(S)` with nonempty centre
on `S`, there is a smooth variety `W` with a projective birational morphism `w : W ⟶ S`
factoring through every `f_i` by projective birational morphisms, on which every `v_j` is the
valuation of a prime divisor; if `S` is projective over `k`, so is `W`. The valuations are carried
by models added to the `X_i`; a common proper birational normal model of all of them is
compactified (Nagata), dominated by a projective variety (Chow) and resolved, and the preimage of
the common model in the resolution is `W`. A proper birational morphism onto a normal variety is
an isomorphism at the generic point of each prime divisor of the target, so the prime divisors
carrying the `v_j` have strict transforms on `W` with the same valuations.

## Main results

* `MMP.Resolution.exists_strongResolution_of_isQuasiProjectiveVariety`: strong resolution of
  quasi-projective varieties (Kollár, Theorem 3.27).
* `MMP.Resolution.exists_isSmoothScheme_isProjectiveMorphism_forall_valuation_eq`: the common
  smooth model retaining finitely many valuations.

## Implementation notes

"Resolution" (smooth variety `R(X)`, `Π` projective and birational) is
`MMP.Resolution.IsResolutionOfVariety`; "isomorphism over `X^ns`" is the restriction of `Π` to
the preimage of `MMP.Mori.smoothLocus s_X` being an isomorphism, and "divisor with simple normal
crossings" is `MMP.Resolution.IsSNCClosedSubset`.

For the common model, projectivity is H-projectivity, `AlgebraicGeometry.IsProjectiveMorphism`. A
divisorial valuation centred on `S` is a valuation `v` of `k(S)` with
`MMP.Flips.HasNonemptyCenter k sS v`; it is carried by `W` when `v = ord_E` for a prime divisor
`E` of `W`, regarded as a divisor over `S` along `w` (`MMP.Mori.DivisorOver.valuation`). The
source makes the common model projective over `S` by the relative Chow lemma; since a resolution
is only projective in the sense of EGA, the common model is instead compactified and made
projective over `k`, so that the smooth model is quasi-projective over `k`, and H-projectivity over
`S` and over each `X_i` follows by cancellation. The auxiliary lemmas live in the namespace
`Proof_lem_mmp_common_projective_resolution_with_valuations`.

## References

* [J. Kollár, *Lectures on resolution of singularities*][Kollar2007], 3.3, Thm. 3.27
* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 1.6.2
-/

@[expose] public section

universe u

namespace MMP.Resolution

open CategoryTheory AlgebraicGeometry MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- **Strong resolution of quasi-projective varieties** (Kollár, Theorem 3.27). Let `X` be a
quasi-projective variety over a field `k` of characteristic `0`. Then there is a projective
birational morphism `f : R ⟶ X` such that
1. `R` is a smooth variety over `k` (`f` is a resolution, `IsResolutionOfVariety`);
2. `f` is an isomorphism over the smooth locus `smoothLocus sX`;
3. `f⁻¹(singularLocus sX)` is a divisor with simple normal crossings on `R`. -/
@[mmp "thm_kr3f_strong_resolution_quasiprojective"]
public theorem exists_strongResolution_of_isQuasiProjectiveVariety {k : Type u} [Field k]
    [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (hX : AlgebraicGeometry.IsQuasiProjectiveVariety k sX) :
    ∃ (R : Scheme.{u}) (f : R ⟶ X), IsResolutionOfVariety sX f ∧
      IsIso (f ∣_ smoothLocus sX) ∧
      IsSNCClosedSubset (f ≫ sX) (f.base ⁻¹' (singularLocus sX : Set X)) := by
  haveI := Stacks.Ample.isInvertibleModule_unit (Spec (.of k))
  have hM := Stacks.Ample.isAmple_unitModule_of_isAffine (Spec (.of k))
  obtain ⟨n, ι, _, -, hιs⟩ := isHQuasiProjective_of_isQuasiProjective sX _ hM hX.isQuasiProjective
  obtain ⟨R, f, hRv, hRs, hproj, hbir, hiso, hsnc⟩ :=
    exists_strongResolution_of_isImmersion sX hX.toIsVariety _
      (projectiveSpaceOverRing.isVariety k n) ((isSmoothScheme_iff _).2 inferInstance) ι hιs
  exact ⟨R, f, ⟨hX.toIsVariety, hRv, hproj, hbir, hRs⟩, hiso, hsnc⟩

end MMP.Resolution

namespace Proof_lem_mmp_common_projective_resolution_with_valuations

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Flips

/-! ### Birational morphisms -/

/-- The partial isomorphism given by a dominant morphism which is an open immersion on a dense
open. -/
private noncomputable def partialIsoOfIsOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) [IsDominant f]
    (U : X.Opens) (hU : Dense (U : Set X)) [IsOpenImmersion (U.ι ≫ f)] : X.PartialIso Y where
  source := U
  dense_source := hU
  target := (U.ι ≫ f).opensRange
  dense_target := by
    rw [Scheme.Hom.coe_opensRange, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι]
    exact f.denseRange.dense_image f.continuous hU
  iso := (U.ι ≫ f).isoOpensRange

/-- A dominant morphism which is an open immersion on a dense open is birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsDominant f] (U : X.Opens) (hU : Dense (U : Set X)) [IsOpenImmersion (U.ι ≫ f)] :
    IsBirationalMorphism f := by
  refine ⟨partialIsoOfIsOpenImmersion f U hU, ?_⟩
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨U, hU, le_rfl, le_top, ?_⟩
  simp only [Scheme.PartialMap.restrict, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom, partialIsoOfIsOpenImmersion, Scheme.Hom.isoOpensRange_hom_ι]
  refine (Scheme.homOfLE_ι_assoc _ _ _).trans ?_
  rw [Scheme.topIso_hom]
  exact (Scheme.homOfLE_ι_assoc _ _ _).symm

/-- A birational morphism is an open immersion on a dense open. -/
private theorem exists_isOpenImmersion_of_isBirationalMorphism {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : IsBirationalMorphism f) :
    ∃ U : X.Opens, Dense (U : Set X) ∧ IsOpenImmersion (U.ι ≫ f) := by
  obtain ⟨e, he⟩ := hf
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff] at he
  obtain ⟨W, hW, hWe, hWf, h⟩ := he
  simp only [Scheme.PartialMap.restrict_hom] at h
  have : IsOpenImmersion e.toPartialMap.hom := by
    change IsOpenImmersion (e.iso.hom ≫ e.target.ι)
    infer_instance
  refine ⟨W, hW, ?_⟩
  have : W.ι ≫ f = X.homOfLE hWf ≫ f.toPartialMap.hom := by
    change W.ι ≫ f = (X.homOfLE (le_top : W ≤ ⊤) ≫ X.topIso.hom) ≫ f
    simp only [Scheme.topIso_hom, Scheme.homOfLE_ι]
  rw [this, ← h]
  infer_instance

/-- A composite of birational morphisms out of an irreducible scheme is birational. -/
private theorem isBirationalMorphism_comp {X Y Z : Scheme.{u}} [IrreducibleSpace X]
    {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsBirationalMorphism f) (hg : IsBirationalMorphism g) :
    IsBirationalMorphism (f ≫ g) := by
  haveI := hf.isDominant
  haveI := hg.isDominant
  obtain ⟨U₁, hU₁, h₁⟩ := exists_isOpenImmersion_of_isBirationalMorphism hf
  obtain ⟨U₂, hU₂, h₂⟩ := exists_isOpenImmersion_of_isBirationalMorphism hg
  let U : X.Opens := U₁ ⊓ f ⁻¹ᵁ U₂
  have hne : (U : Set X).Nonempty := by
    obtain ⟨x₀⟩ := (IrreducibleSpace.isIrreducible_univ X).nonempty
    haveI : Nonempty Y := ⟨f x₀⟩
    have hd : Dense (f '' U₁) := f.denseRange.dense_image f.continuous hU₁
    obtain ⟨y, hy₂, x, hx₁, rfl⟩ := (hU₂.inter_of_isOpen_left hd U₂.2).nonempty
    exact ⟨x, hx₁, hy₂⟩
  have hle : U ≤ f ⁻¹ᵁ U₂ := inf_le_right
  have : IsOpenImmersion (f.resLE U₂ U hle ≫ U₂.ι) := by
    rw [Scheme.Hom.resLE_comp_ι, ← Scheme.homOfLE_ι X (inf_le_left : U ≤ U₁), Category.assoc]
    infer_instance
  have := IsOpenImmersion.of_comp (f.resLE U₂ U hle) U₂.ι
  haveI : IsOpenImmersion (U.ι ≫ f ≫ g) := by
    rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι f hle, Category.assoc]
    infer_instance
  exact isBirationalMorphism_of_isOpenImmersion (f ≫ g) U (U.2.dense hne)

/-- A morphism of integral schemes, locally of finite type and birational in the sense of
`AlgebraicGeometry.IsBirational`, is a birational morphism. -/
private theorem isBirationalMorphism_of_isBirational {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : IsBirational f) :
    IsBirationalMorphism f := by
  haveI : Finite (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]
    exact Set.finite_singleton _
  haveI : Finite (irreducibleComponents Y) := by
    rw [irreducibleComponents_eq_singleton]
    exact Set.finite_singleton _
  obtain ⟨U, V, hUV, hU, hV, hiso⟩ :=
    exists_dense_opens_isIso_resLE_of_isBirational f hf (Or.inl ⟨inferInstance, inferInstance⟩)
  exact isBirationalMorphism_of_isIso_resLE f U V hU.nonempty hV.nonempty hUV hiso

/-! ### H-projectivity from a quasi-projective source -/

/-- A proper morphism `w : W ⟶ S` whose composite with a separated `s : S ⟶ T` is the
restriction of the structure morphism of `ℙⁿ_T` along an immersion is H-projective. -/
private theorem isProjectiveMorphism_of_isImmersion {W S T : Scheme.{u}} {n : ℕ}
    (i : W ⟶ projectiveSpaceOver n T) [IsImmersion i] (w : W ⟶ S) [IsProper w]
    (s : S ⟶ T) [IsSeparated s] (h : i ≫ (projectiveSpaceOver n T ↘ T) = w ≫ s) :
    IsProjectiveMorphism w := by
  have := isProper_projectiveSpaceOver n T
  let κ := Limits.pullback.lift i w h
  have : IsImmersion (κ ≫ Limits.pullback.fst (projectiveSpaceOver n T ↘ T) s) := by
    rw [Limits.pullback.lift_fst]
    infer_instance
  have : IsImmersion κ := IsImmersion.of_comp κ (Limits.pullback.fst _ _)
  have : IsProper (κ ≫ Limits.pullback.snd (projectiveSpaceOver n T ↘ T) s) := by
    rw [Limits.pullback.lift_snd]
    infer_instance
  have : IsProper κ := IsProper.of_comp κ (Limits.pullback.snd _ _)
  have : IsClosedImmersion κ := IsClosedImmersion.of_isPreimmersion κ κ.isClosedMap.isClosed_range
  exact ⟨n, κ ≫ (projectiveSpaceOverBaseChangeIso n s).hom, inferInstance, by
    rw [Category.assoc, projectiveSpaceOverBaseChangeIso_hom_over, Limits.pullback.lift_snd]⟩

/-! ### A smooth quasi-projective model of a variety -/

/-- **Nagata compactification of a variety.** A variety is an open subvariety of a proper
variety. -/
private theorem exists_isOpenImmersion_isProper {k : Type u} [Field k] {M : Scheme.{u}}
    (sM : M ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sM] :
    ∃ (Mb : Scheme.{u}) (e : M ⟶ Mb) (sMb : Mb ⟶ Spec (.of k)),
      AlgebraicGeometry.IsVariety k sMb ∧ IsProper sMb ∧ IsOpenImmersion e ∧ e ≫ sMb = sM := by
  obtain ⟨c, hqc⟩ := hasCompactification_of_compactSpace_quasiSeparatedSpace sM
  refine ⟨c.immersion.image, c.immersion.toImage, c.immersion.imageι ≫ c.toBase,
    Scheme.Hom.isVariety_image k c.immersion c.toBase, inferInstance,
    isOpenImmersion_toImage _ (.inl hqc), ?_⟩
  rw [← Category.assoc, Scheme.Hom.toImage_imageι]
  exact Over.w c.obj.hom

/-- A nonempty open subscheme of a smooth variety is a smooth variety. -/
private theorem isVariety_and_isSmoothScheme_ι_comp {k : Type u} [Field k] {Y : Scheme.{u}}
    (s : Y ⟶ Spec (.of k)) [hY : AlgebraicGeometry.IsVariety k s] (hs : IsSmoothScheme s)
    (W : Y.Opens) [Nonempty W] :
    AlgebraicGeometry.IsVariety k (W.ι ≫ s) ∧ IsSmoothScheme (W.ι ≫ s) := by
  haveI := hY.toLocallyOfFiniteType
  haveI := hY.toQuasiCompact
  haveI := hY.toIsSeparated
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
  haveI : IsNoetherian Y := ⟨⟩
  haveI : IsIntegral Y := hY.toIsIntegral
  haveI : IsIntegral W := isIntegral_of_isOpenImmersion W.ι
  refine ⟨AlgebraicGeometry.IsVariety.mk, ?_⟩
  haveI : IsLocallyNoetherian (Spec (.of k)) := isLocallyNoetherian_Spec.mpr inferInstance
  haveI : LocallyOfFinitePresentation s :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 hY.toLocallyOfFiniteType
  haveI : Smooth s := (isSmoothScheme_iff _).1 hs
  exact MMP.Mori.isSmoothScheme_of_smooth inferInstance

/-- If `p ≫ e = W.ι ≫ q` for an open immersion `e`, a nonempty open `W`, and a morphism `q`
which is an open immersion on a dense open, then `p` is birational. -/
private theorem isBirationalMorphism_of_comp_eq_ι_comp {Y M N : Scheme.{u}} [IrreducibleSpace M]
    {q : Y ⟶ N} {U : Y.Opens} (hU : Dense (U : Set Y)) [IsOpenImmersion (U.ι ≫ q)]
    {W : Y.Opens} [IsIntegral W] (hWne : (W : Set Y).Nonempty) {p : W.toScheme ⟶ M}
    {e : M ⟶ N} [IsOpenImmersion e] (hpe : p ≫ e = W.ι ≫ q) : IsBirationalMorphism p := by
  let U' : W.toScheme.Opens := W.ι ⁻¹ᵁ U
  have hU'ne : (U' : Set W.toScheme).Nonempty := by
    obtain ⟨y, hyW, hyU⟩ := hU.inter_open_nonempty W W.isOpen hWne
    exact ⟨⟨y, hyW⟩, hyU⟩
  haveI : Nonempty U' := hU'ne.to_subtype
  have : IsOpenImmersion (W.ι.resLE U U' le_rfl ≫ U.ι) := by
    rw [Scheme.Hom.resLE_comp_ι]
    infer_instance
  have := IsOpenImmersion.of_comp (W.ι.resLE U U' le_rfl) U.ι
  have : IsOpenImmersion ((U'.ι ≫ p) ≫ e) := by
    rw [Category.assoc, hpe, ← Category.assoc, ← Scheme.Hom.resLE_comp_ι W.ι le_rfl,
      Category.assoc]
    infer_instance
  have : IsOpenImmersion (U'.ι ≫ p) := IsOpenImmersion.of_comp _ e
  haveI : IsDominant p := ⟨(((U'.ι ≫ p).isOpenEmbedding.isOpen_range.dense
    (Set.range_nonempty _)).mono (by rintro _ ⟨x, rfl⟩; exact ⟨U'.ι x, rfl⟩))⟩
  exact isBirationalMorphism_of_isOpenImmersion p U' (U'.isOpen.dense hU'ne)

/-- **A smooth quasi-projective model.** Over a field of characteristic zero, every variety `M`
is the target of a proper birational morphism `p : W ⟶ M` from a smooth variety `W` immersed in
some `ℙⁿ_k`. -/
private theorem exists_isImmersion_isSmoothScheme {k : Type u} [Field k] [CharZero k]
    {M : Scheme.{u}} (sM : M ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sM] :
    ∃ (W : Scheme.{u}) (p : W ⟶ M) (n : ℕ) (i : W ⟶ projectiveSpaceOver n (Spec (.of k))),
      IsImmersion i ∧ i ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = p ≫ sM ∧
      AlgebraicGeometry.IsVariety k (p ≫ sM) ∧ IsSmoothScheme (p ≫ sM) ∧ IsProper p ∧
      IsBirationalMorphism p := by
  obtain ⟨Mb, e, sMb, hMb, hMbp, he, hes⟩ := exists_isOpenImmersion_isProper sM
  obtain ⟨P, π, hP, hPproj, -, hπb⟩ :=
    (MMP.Resolution.Bridges.exists_isProjectiveMorphism_isBirational_chowModification k).2 hMb hMbp
  obtain ⟨Y, g, hY, hg, hgb, hYs, -, -⟩ := MMP.Resolution.exists_isStrongResolution (π ≫ sMb) hP
  obtain ⟨A, hA, hAa⟩ := Stacks.HProjective.exists_isAmple_of_isAffine (Spec (.of k))
  obtain ⟨L, hL, hLa⟩ := exists_isAmple_of_isProjectiveMorphism (π ≫ sMb) A hAa hPproj
  obtain ⟨n, c, hc, hcY⟩ := (isProjectiveMorphism_of_isProjective g L hLa hg).comp hPproj
  haveI := hc
  haveI := hY
  haveI := hP
  haveI := hMb
  haveI : IsIntegral Y := hY.toIsIntegral
  haveI : LocallyOfFiniteType π :=
    haveI := hP.toLocallyOfFiniteType
    locallyOfFiniteType_of_comp π sMb
  haveI : IsProper π :=
    haveI := isProper_of_isProjectiveMorphism _ hPproj
    IsProper.of_comp π sMb
  haveI : IsProper g := hg.isProper
  have hgπ : IsBirationalMorphism (g ≫ π) :=
    isBirationalMorphism_comp hgb (isBirationalMorphism_of_isBirational π hπb)
  haveI := hgπ.isDominant
  obtain ⟨U, hU, hUi⟩ := exists_isOpenImmersion_of_isBirationalMorphism hgπ
  let V : Mb.Opens := e.opensRange
  let W : Y.Opens := (g ≫ π) ⁻¹ᵁ V
  have hVne : (V : Set Mb).Nonempty := by
    obtain ⟨x⟩ := (IrreducibleSpace.isIrreducible_univ M).nonempty
    exact ⟨e x, x, rfl⟩
  have hWne : (W : Set Y).Nonempty := by
    obtain ⟨_, hy, y, rfl⟩ := (g ≫ π).denseRange.inter_open_nonempty V V.isOpen hVne
    exact ⟨y, hy⟩
  haveI : Nonempty W := hWne.to_subtype
  let p : W.toScheme ⟶ M := ((g ≫ π) ∣_ V) ≫ e.isoOpensRange.inv
  have hpe : p ≫ e = W.ι ≫ g ≫ π := by
    simp only [p, Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]
    exact morphismRestrict_ι _ _
  have hps : p ≫ sM = W.ι ≫ g ≫ π ≫ sMb := by
    rw [← hes, ← Category.assoc, hpe, Category.assoc, Category.assoc]
  haveI : IsProper p := by
    haveI : IsProper ((g ≫ π) ∣_ V) := IsZariskiLocalAtTarget.restrict (P := @IsProper)
      (inferInstanceAs (IsProper (g ≫ π))) V
    infer_instance
  haveI : IsIntegral W := isIntegral_of_isOpenImmersion W.ι
  obtain ⟨hWv, hWs⟩ := isVariety_and_isSmoothScheme_ι_comp (g ≫ π ≫ sMb) hYs W
  rw [← hps] at hWv hWs
  exact ⟨W, p, n, W.ι ≫ c, inferInstance, by rw [Category.assoc, hcY, hps], hWv, hWs,
    inferInstance, isBirationalMorphism_of_comp_eq_ι_comp hU hWne hpe⟩

/-! ### A common normal model of finitely many models -/

/-- A birational morphism `f : X ⟶ S` restricts to an isomorphism of dense opens over `S`. -/
private theorem exists_partialIso_isOver {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : IsBirationalMorphism f) : ∃ e : X.PartialIso S, e.IsOver f (𝟙 S) := by
  haveI := hf.isDominant
  obtain ⟨U, hU, _⟩ := exists_isOpenImmersion_of_isBirationalMorphism hf
  exact ⟨partialIsoOfIsOpenImmersion f U hU,
    by simp [partialIsoOfIsOpenImmersion, Scheme.PartialIso.IsOver]⟩

/-- If a partial isomorphism `e : X ⇢ Y` lies over `S`, then composing it with `sY : Y ⟶ S`
gives the rational map of `sX`. -/
private theorem toRationalMap_compHom_of_isOver {S X Y : Scheme.{u}} {sX : X ⟶ S}
    {sY : Y ⟶ S} (e : X.PartialIso Y) (he : e.IsOver sX sY) :
    e.toRationalMap.compHom sY = sX.toRationalMap := by
  rw [← Scheme.RationalMap.compHom_toRationalMap, Scheme.Hom.toRationalMap,
    Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨e.source, e.dense_source, le_rfl, le_top, ?_⟩
  simp only [Scheme.PartialMap.restrict, Scheme.PartialMap.compHom, Scheme.PartialIso.toPartialMap,
    Scheme.Hom.toPartialMap]
  rw [Category.assoc, he, Scheme.homOfLE_ι_assoc, Scheme.topIso_hom, Scheme.homOfLE_ι_assoc]

/-- Two proper birational morphisms of normal varieties onto `S` have a common proper birational
normal model over `S`. -/
private theorem exists_common_model_two {k : Type u} [Field k] {S M X : Scheme.{u}}
    (sS : S ⟶ Spec (.of k)) (m : M ⟶ S) [IsProper m]
    (hm : IsBirationalMorphism m) (hM : IsNormalVariety k (m ≫ sS)) (f : X ⟶ S) [IsProper f]
    (hf : IsBirationalMorphism f) (hX : IsNormalVariety k (f ≫ sS)) :
    ∃ (Z : Scheme.{u}) (g₁ : Z ⟶ M) (g₂ : Z ⟶ X), IsNormalVariety k (g₁ ≫ m ≫ sS) ∧
      IsProper g₁ ∧ IsProper g₂ ∧ IsBirationalMorphism g₁ ∧ IsBirationalMorphism g₂ ∧
      g₁ ≫ m = g₂ ≫ f := by
  obtain ⟨e₁, he₁⟩ := exists_partialIso_isOver hm
  obtain ⟨e₂, he₂⟩ := exists_partialIso_isOver hf
  obtain ⟨Z, g₁, g₂, hZ, hg₁, hg₂, hb₁, hb₂, -, hc⟩ :=
    exists_isNormalVariety_isProper_isBirationalMorphism hM hX m f (e₁.trans e₂.symm).toRationalMap
      (RationalMap.isBirational_toRationalMap _)
      (toRationalMap_compHom_of_isOver _ (he₁.trans he₂.symm))
  exact ⟨Z, g₁, g₂, hZ, hg₁, hg₂, hb₁, hb₂, hc⟩

/-- Finitely many proper birational morphisms of normal varieties onto `S` have a common proper
birational normal model over `S`. -/
private theorem exists_common_model {k : Type u} [Field k] {S : Scheme.{u}}
    (sS : S ⟶ Spec (.of k)) (hS : IsNormalVariety k sS) {ι : Type*} [Finite ι]
    (X : ι → Scheme.{u}) (f : ∀ i, X i ⟶ S) [∀ i, IsProper (f i)]
    (hfb : ∀ i, IsBirationalMorphism (f i)) (hX : ∀ i, IsNormalVariety k (f i ≫ sS)) :
    ∃ (M : Scheme.{u}) (m : M ⟶ S) (h : ∀ i, M ⟶ X i), IsNormalVariety k (m ≫ sS) ∧
      IsProper m ∧ IsBirationalMorphism m ∧
      ∀ i, h i ≫ f i = m ∧ IsProper (h i) ∧ IsBirationalMorphism (h i) := by
  classical
  have := Fintype.ofFinite ι
  suffices H : ∀ s : Finset ι, ∃ (M : Scheme.{u}) (m : M ⟶ S), IsNormalVariety k (m ≫ sS) ∧
      IsProper m ∧ IsBirationalMorphism m ∧
      ∀ i ∈ s, ∃ h : M ⟶ X i, h ≫ f i = m ∧ IsProper h ∧ IsBirationalMorphism h by
    obtain ⟨M, m, hM, hm, hmb, hh⟩ := H Finset.univ
    choose h hh using fun i => hh i (Finset.mem_univ i)
    exact ⟨M, m, h, hM, hm, hmb, hh⟩
  intro s
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨S, 𝟙 S, by rwa [Category.id_comp], inferInstance, isBirationalMorphism_of_isIso _,
      fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a s ha ih =>
    obtain ⟨M, m, hM, hm, hmb, hh⟩ := ih
    haveI := hm
    obtain ⟨Z, g₁, g₂, hZ, hg₁, hg₂, hb₁, hb₂, hc⟩ :=
      exists_common_model_two sS m hmb hM (f a) (hfb a) (hX a)
    haveI := hg₁
    haveI := hg₂
    haveI : IsIntegral Z := hZ.1.toIsIntegral
    refine ⟨Z, g₁ ≫ m, by rwa [Category.assoc], inferInstance, isBirationalMorphism_comp hb₁ hmb,
      fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact ⟨g₂, hc.symm, hg₂, hb₂⟩
    · obtain ⟨h, hhf, hhp, hhb⟩ := hh i hi
      haveI := hhp
      exact ⟨g₁ ≫ h, by rw [Category.assoc, hhf], inferInstance, isBirationalMorphism_comp hb₁ hhb⟩

/-! ### Strict transforms of prime divisors -/

/-- If a dominant morphism `f : Y ⟶ X` of normal integral schemes inducing a surjection of
function fields maps the generic point of a prime divisor `E` of `Y` to that of a prime divisor
`P` of `X`, then `ord_E`, read in `k(X)`, is `ord_P`. -/
private theorem valuationOver_eq_of_map_genericPoint {X Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (f : Y ⟶ X) [IsDominant f] (hf : Function.Surjective (functionFieldMap f))
    (E : MMP.Mori.PrimeDivisor Y) (P : MMP.Mori.PrimeDivisor X)
    (h : f E.genericPoint = P.genericPoint) :
    E.valuationOver f = P.divisorialValuation := by
  have := P.isDiscreteValuationRing_localRing
  have h1 : ∀ z, f E.genericPoint = z → ∀ a : X.presheaf.stalk z,
      E.valuationOver f (algebraMap _ X.functionField a) ≤ 1 := by
    rintro z rfl a
    rw [MMP.Mori.PrimeDivisor.valuationOver_apply, MMP.Mori.functionFieldMap_algebraMap_stalk,
      MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff]
    exact ⟨_, rfl⟩
  have h2 : ∀ z, f E.genericPoint = z → ∀ a : X.presheaf.stalk z,
      a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk z) →
      E.valuationOver f (algebraMap _ X.functionField a) < 1 := by
    rintro z rfl a ha
    rw [MMP.Mori.PrimeDivisor.valuationOver_apply, MMP.Mori.functionFieldMap_algebraMap_stalk,
      MMP.Mori.PrimeDivisor.divisorialValuation_algebraMap_lt_one_iff]
    exact (IsLocalRing.mem_maximalIdeal _).2 fun hu =>
      (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit _ _ hu)
  have h3 : ∃ g, E.valuationOver f g = WithZero.exp (-1) := by
    have := E.isDiscreteValuationRing_localRing
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible E.localRing
    obtain ⟨g, hg⟩ := hf (algebraMap E.localRing Y.functionField ϖ)
    exact ⟨g, by rw [MMP.Mori.PrimeDivisor.valuationOver_apply, hg,
      MMP.Mori.PrimeDivisor.divisorialValuation_algebraMap_of_irreducible _ hϖ]⟩
  have h3' : ∃ g, P.divisorialValuation g = WithZero.exp (-1) := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible P.localRing
    exact ⟨_, P.divisorialValuation_algebraMap_of_irreducible hϖ⟩
  exact MMP.Positivity.DivisorOver.valuation_eq_of_isDiscreteValuationRing (R := P.localRing)
    (h1 _ h) (h2 _ h) h3 (fun r => (P.divisorialValuation_le_one_iff _).2 ⟨r, rfl⟩)
    (fun r hr => (P.divisorialValuation_algebraMap_lt_one_iff r).2 hr) h3'

/-- A normal birational model `w : W ⟶ S` factoring through the model of a proper divisor `D`
over `S` by a proper birational `g` carries a prime divisor whose valuation is that of `D`. -/
private theorem exists_primeDivisor_valuation_eq {k : Type u} [Field k] {S : Scheme.{u}}
    [IsIntegral S] {sS : S ⟶ Spec (.of k)} (D : ProperDivisorOver k sS) {W : Scheme.{u}}
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] (w : W ⟶ S)
    (hW : IsNormalVariety k (w ≫ sS)) (hwb : IsBirationalMorphism w) (g : W ⟶ D.Y) [IsProper g]
    (hgb : IsBirationalMorphism g) (hg : g ≫ D.f = w) :
    ∃ E : MMP.Mori.PrimeDivisor W,
      (⟨W, w, hW, hwb, E⟩ : MMP.Mori.DivisorOver k sS).valuation = D.valuation := by
  have hWD : IsNormalVariety k (g ≫ D.f ≫ sS) := by
    rw [← Category.assoc, hg]
    exact hW
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isIntegral
  haveI := hgb.isDominant
  haveI := D.isDominant
  haveI := hwb.isDominant
  obtain ⟨E, hE, -, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0}
      D.isNormalVariety hWD hgb D.E
  refine ⟨E, ?_⟩
  ext t
  change E.divisorialValuation (functionFieldMap w t) =
    D.E.divisorialValuation (functionFieldMap D.f t)
  rw [← valuationOver_eq_of_map_genericPoint g hgb.functionFieldMap_bijective.2 E D.E hE,
    MMP.Mori.PrimeDivisor.valuationOver_apply,
    MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
    MMP.Positivity.DivisorOver.functionFieldMap_congr hg]

end Proof_lem_mmp_common_projective_resolution_with_valuations

namespace MMP.Resolution

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Flips
  Proof_lem_mmp_common_projective_resolution_with_valuations
open scoped WithZero

/-- **A common smooth model, projective over `S`, retaining finitely many valuations.**
Let `S` be a normal variety over a field `k` of characteristic zero, `f i : X i ⟶ S` (`i : ι`,
finite) proper birational morphisms from normal varieties, and `v j` (`j : κ`, finite) divisorial
valuations of `k(S)` with nonempty centre on `S`. Then there is a smooth variety `W` with a
projective birational morphism `w : W ⟶ S`, projective birational morphisms `g i : W ⟶ X i`
with `g i ≫ f i = w`, and for each `j` a prime divisor `E` of `W` whose valuation is `v j`.
Moreover, if `S` is a projective variety, so is `W`. -/
@[mmp "lem_mmp_common_projective_resolution_with_valuations"]
public theorem exists_isSmoothScheme_isProjectiveMorphism_forall_valuation_eq
    {k : Type u} [Field k] [CharZero k] {S : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    [AlgebraicGeometry.IsVariety k sS] [IsNormal S]
    {ι : Type*} [Finite ι] {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ S)
    [∀ i, IsProper (f i)] (hfb : ∀ i, IsBirationalMorphism (f i))
    (hX : ∀ i, IsNormalVariety k (f i ≫ sS))
    {κ : Type*} [Finite κ] (v : κ → Valuation S.functionField ℤᵐ⁰)
    (hv : ∀ j, HasNonemptyCenter k sS (v j)) :
    ∃ (W : Scheme.{u}) (w : W ⟶ S) (hW : IsNormalVariety k (w ≫ sS))
      (hwb : IsBirationalMorphism w) (g : ∀ i, W ⟶ X i),
      IsSmoothScheme (w ≫ sS) ∧ IsProjectiveMorphism w ∧
      (∀ i, g i ≫ f i = w ∧ IsProjectiveMorphism (g i) ∧ IsBirationalMorphism (g i)) ∧
      (∀ j, ∃ E : Mori.PrimeDivisor W,
        (⟨W, w, hW, hwb, E⟩ : DivisorOver k sS).valuation = v j) ∧
      (AlgebraicGeometry.IsProjectiveVariety k sS →
        AlgebraicGeometry.IsProjectiveVariety k (w ≫ sS)) := by
  choose D hD using fun j => (hv j).2
  let Y : ι ⊕ κ → Scheme.{u} := fun s => Sum.rec X (fun j => (D j).Y) s
  let F : ∀ s, Y s ⟶ S := fun s => match s with
    | .inl i => f i
    | .inr j => (D j).f
  haveI hFp : ∀ s, IsProper (F s) := fun s => match s with
    | .inl i => inferInstanceAs (IsProper (f i))
    | .inr j => (D j).isProper
  have hFb : ∀ s, IsBirationalMorphism (F s) := fun s => match s with
    | .inl i => hfb i
    | .inr j => (D j).isBirationalMorphism
  have hY : ∀ s, IsNormalVariety k (F s ≫ sS) := fun s => match s with
    | .inl i => hX i
    | .inr j => (D j).isNormalVariety
  obtain ⟨M, m, h, hM, hmp, hmb, hmh⟩ :=
    @exists_common_model k _ S sS ⟨inferInstance, inferInstance⟩ (ι ⊕ κ) _ Y F hFp hFb hY
  haveI := hmp
  haveI : AlgebraicGeometry.IsVariety k (m ≫ sS) := hM.1
  haveI : IsIntegral M := hM.1.toIsIntegral
  obtain ⟨W, p, n, i, hi, hip, hWv, hWs, hpp, hpb⟩ := exists_isImmersion_isSmoothScheme (m ≫ sS)
  haveI := hpp
  haveI := hi
  haveI : IsIntegral W := hWv.toIsIntegral
  obtain ⟨hWn1, hWn2⟩ :=
    MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hWs
  have hW : IsNormalVariety k ((p ≫ m) ≫ sS) := by
    rw [Category.assoc]
    exact ⟨hWv, hWn2⟩
  have hwb : IsBirationalMorphism (p ≫ m) := isBirationalMorphism_comp hpb hmb
  have hwp : IsProjectiveMorphism (p ≫ m) :=
    isProjectiveMorphism_of_isImmersion i (p ≫ m) sS (by rw [hip, Category.assoc])
  have hgs : ∀ s, IsProper (p ≫ h s) := fun s =>
    MorphismProperty.comp_mem @IsProper p (h s) hpp (hmh s).2.1
  refine ⟨W, p ≫ m, hW, hwb, fun i => p ≫ h (.inl i), by rw [Category.assoc]; exact hWs, hwp,
    fun i' => ⟨?_, ?_, isBirationalMorphism_comp hpb (hmh (.inl i')).2.2⟩, fun j => ?_, ?_⟩
  · rw [Category.assoc]
    exact congrArg (p ≫ ·) (hmh (.inl i')).1
  · haveI := hgs (.inl i')
    haveI : IsSeparated (f i' ≫ sS) := (hX i').1.toIsSeparated
    exact isProjectiveMorphism_of_isImmersion i (p ≫ h (.inl i')) (f i' ≫ sS)
      (by
        rw [hip, ← (hmh (.inl i')).1]
        simp only [Category.assoc]
        rfl)
  · haveI := hgs (.inr j)
    rw [← hD j]
    exact exists_primeDivisor_valuation_eq (D j) (p ≫ m) hW hwb (p ≫ h (.inr j))
      (isBirationalMorphism_comp hpb (hmh (.inr j)).2.2)
      (by rw [Category.assoc]; exact congrArg (p ≫ ·) (hmh (.inr j)).1)
  · exact fun hSp =>
      (AlgebraicGeometry.isProjectiveVariety_iff k _).2 ⟨hW.1, hwp.comp hSp.isProjective⟩

end MMP.Resolution
