module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupEmbedded
public import MMP.AlgebraicGeometry.Resolution.Blowup.PointBlowupIsoOff
public import MMP.AlgebraicGeometry.Divisor.SNC
public import MMP.AlgebraicGeometry.Resolution.Blowup
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.Monomial
import MMP.AlgebraicGeometry.MMP.Fourfold.AffineBaseRegularGeneration
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupFactorization
import MMP.AlgebraicGeometry.Morphisms.Birational.RationalMap
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleEmbedding
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Resolution.BirationalTransformTriple
import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCentre
import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.Sequence
import MMP.AlgebraicGeometry.MMP.Steps
import MMP.AlgebraicGeometry.Resolution.OrderAlongExceptional
import MMP.AlgebraicGeometry.Resolution.DisjoiningCenter
import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC

/-!
# Point blow-ups of surfaces and the monomial step of order reduction

This file collects results on blow-ups used in Kollár's resolution of surfaces and in the
monomial step of order reduction:

* the exceptional set of a composite with a point blow-up of a regular surface, and the
  decomposition `π_m⁻¹(C) = C_m ∪ Ex(π_m)` along a sequence of point blow-ups (Kollár 1.48);
* the contraction of `(x^b, y)^m` from a chart of the blow-up of a regular local surface
  (Kollár 1.70);
* the normalized graph of two resolutions of a surface (Kollár, proof of 2.16);
* the Step-3.`r` blow-up of monomial data, the lexicographic decrease of `(m_r, n_r)` for `r ≥ 2`
  and the termination of the Step-3.1 blow-ups (Kollár 3.111).

## Main results

* `MMP.Resolution.Kollar.exceptionalSet_blowUpToBase_comp`
* `MMP.Resolution.PointBlowupSequence.support_comap_π_eq_union_exceptionalSet`
* `MMP.Resolution.Kollar.comap_map_span_pow_of_isLocalization_adjoin_div`
* `MMP.Resolution.IsProjectiveSurfaceResolution.graphNormalization_spec`
* `MMP.Resolution.MonomialData.step_spec`
* `MMP.Resolution.MonomialData.toLex_maxStratumWeight_maxStratumCount_step_lt`
* `MMP.Resolution.MonomialData.exists_maxStratumWeight_iterate_one_lt`

## References

* [J. Kollár, *Lectures on resolution of singularities*][kollar2007]
-/

universe u

/-!
### The exceptional set of a composite with a point blow-up (Kollár 1.48)

Let `S'` be a regular surface, `g : S' ⟶ S` a morphism of schemes, `p ∈ S'` a closed point and
`σ : B_pS' → S'` the blow-up of `p`, with exceptional curve `E = σ⁻¹(p)`. Then the exceptional
set of `σ ≫ g` is `σ⁻¹(Ex(g)) ∪ E`.

### Main results

* `MMP.Resolution.Kollar.exceptionalSet_blowUpToBase_comp`:
  `Ex(σ ≫ g) = σ⁻¹(Ex(g)) ∪ E`.

### References

* [J. Kollár, *Lectures on resolution of singularities*][kollar2007], 1.48.
-/

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori MMP.Resolution MMP.Resolution.Kollar

namespace MMP.Proofs.lem_kr1b_exceptional_set_composite

variable {S' S : Scheme.{u}} {p : S'} (hp : IsClosed ({p} : Set S'))

/-- A point of the blow-up lies on the exceptional curve iff it maps to the centre. -/
private lemma mem_support_exceptionalIdeal_iff (y : blowUp (pointIdeal hp)) :
    y ∈ ((exceptionalIdeal (pointIdeal hp)).support : Set (blowUp (pointIdeal hp))) ↔
      blowUpToBase (pointIdeal hp) y = p := by
  have h := congrArg (y ∈ ·) (preimage_compl_eq_compl_support_exceptionalIdeal hp)
  simp only [eq_iff_iff, Set.mem_compl_iff] at h
  change blowUpToBase (pointIdeal hp) y ∈ (({p} : Set S')ᶜ) ↔ _ at h
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at h
  tauto

/-- The blow-up is an isomorphism over every open missing the centre. -/
private lemma isBiregular_blowUpToBase {U : S'.Opens} (hU : p ∉ U) :
    IsBiregular (blowUpToBase (pointIdeal hp)) U := by
  have h : IsBiregular (blowUpToBase (pointIdeal hp)) (complPoint hp) :=
    isIso_blowUpToBase_restrict_compl_point hp
  refine isBiregular_iff_le_biregularLocus.mpr
    (le_trans (fun x hx ↦ ?_) (isBiregular_iff_le_biregularLocus.mp h))
  change x ∈ (({p} : Set S')ᶜ)
  rintro rfl
  exact hU hx

/-- Over an open missing `g(p)`, `σ ≫ g` is an isomorphism iff `g` is. -/
private lemma isBiregular_comp_iff (g : S' ⟶ S) {V : S.Opens} (hV : g p ∉ V) :
    IsBiregular (blowUpToBase (pointIdeal hp) ≫ g) V ↔ IsBiregular g V := by
  have : IsIso (blowUpToBase (pointIdeal hp) ∣_ g ⁻¹ᵁ V) :=
    isBiregular_blowUpToBase hp (U := g ⁻¹ᵁ V) hV
  unfold IsBiregular
  rw [morphismRestrict_comp]
  exact ⟨fun h ↦ @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ this h,
    fun h ↦ @IsIso.comp_isIso _ _ _ _ _ _ _ this h⟩

/-- The exceptional curve of the blow-up of a regular surface at a closed point has two distinct
points. -/
private lemma exists_ne_mem_support_exceptionalIdeal (hS' : IsRegularSurface S') :
    ∃ y₁ ∈ ((exceptionalIdeal (pointIdeal hp)).support : Set (blowUp (pointIdeal hp))),
      ∃ y₂ ∈ ((exceptionalIdeal (pointIdeal hp)).support : Set (blowUp (pointIdeal hp))),
        y₁ ≠ y₂ := by
  obtain ⟨e, -⟩ :=
    Stacks.Blowup.exists_isExceptionalCurveOfFirstKind_exceptionalIdeal_vanishingIdeal
    p hp (hS'.2.1 p) (hS'.2.2 p hp)
  obtain ⟨a, b, hab⟩ := not_subsingleton_iff_nontrivial.mp
    (ExceptionalCurveContraction.not_subsingleton_projectiveLineProj (e := e)) |>.exists_pair_ne
  set ι := (exceptionalIdeal (pointIdeal hp)).subschemeι
  refine ⟨ι (e.hom a), ?_, ι (e.hom b), ?_,
    fun h ↦ hab (e.hom.homeomorph.injective (ι.isClosedEmbedding.injective h))⟩ <;>
  exact Scheme.IdealSheafData.range_subschemeι _ ▸ ⟨_, rfl⟩

/-- An open over which `σ ≫ g` is an isomorphism does not contain `g(p)`. -/
private lemma notMem_of_isBiregular_comp (hS' : IsRegularSurface S') (g : S' ⟶ S)
    {V : S.Opens} (hV : IsBiregular (blowUpToBase (pointIdeal hp) ≫ g) V) : g p ∉ V := by
  intro hpV
  obtain ⟨y₁, h₁, y₂, h₂, hne⟩ := exists_ne_mem_support_exceptionalIdeal hp hS'
  rw [mem_support_exceptionalIdeal_iff] at h₁ h₂
  set f := blowUpToBase (pointIdeal hp) ≫ g
  have : IsIso (f ∣_ V) := hV
  have hinj : Function.Injective (f ∣_ V).base := (f ∣_ V).homeomorph.injective
  have m₁ : y₁ ∈ f ⁻¹ᵁ V := by
    change g (blowUpToBase (pointIdeal hp) y₁) ∈ V; rwa [h₁]
  have m₂ : y₂ ∈ f ⁻¹ᵁ V := by
    change g (blowUpToBase (pointIdeal hp) y₂) ∈ V; rwa [h₂]
  refine hne (congrArg Subtype.val (hinj (a₁ := ⟨y₁, m₁⟩) (a₂ := ⟨y₂, m₂⟩) (Subtype.ext ?_)))
  erw [morphismRestrict_base_coe, morphismRestrict_base_coe]
  change g (blowUpToBase (pointIdeal hp) y₁) = g (blowUpToBase (pointIdeal hp) y₂)
  rw [h₁, h₂]

include hp in
/-- A point `x ≠ p` with `g(x)` in the biregular locus of `g` lies in an open `V` over which `g`
is an isomorphism and which misses `g(p)`. -/
private lemma exists_isBiregular_notMem (g : S' ⟶ S) {x : S'} (hx : x ≠ p)
    (hgx : g x ∈ biregularLocus g) :
    ∃ V : S.Opens, IsBiregular g V ∧ g x ∈ V ∧ g p ∉ V := by
  by_cases hgp : g p ∈ biregularLocus g
  · set W := biregularLocus g
    refine ⟨W ⊓ ⟨(closure {g p})ᶜ, isClosed_closure.isOpen_compl⟩,
      isBiregular_iff_le_biregularLocus.mpr inf_le_left, ⟨hgx, ?_⟩,
      fun h ↦ h.2 (subset_closure rfl)⟩
    change g x ∉ closure {g p}
    intro hsp
    have hspec : g p ⤳ g x := specializes_iff_mem_closure.mpr hsp
    have : IsIso (g ∣_ W) := isBiregular_biregularLocus g
    have hind := (g ∣_ W).homeomorph.isInducing
    have hs : (⟨p, hgp⟩ : g ⁻¹ᵁ W) ⤳ ⟨x, hgx⟩ := by
      apply hind.specializes_iff.mp
      apply (Topology.IsInducing.subtypeVal).specializes_iff.mp
      erw [morphismRestrict_base_coe, morphismRestrict_base_coe]
      exact hspec
    have hs' : p ⤳ x := (Topology.IsInducing.subtypeVal).specializes_iff.mpr hs
    exact hx (hs'.mem_closed hp rfl)
  · exact ⟨biregularLocus g, isBiregular_biregularLocus g, hgx, hgp⟩

end MMP.Proofs.lem_kr1b_exceptional_set_composite

namespace MMP.Resolution.Kollar

open MMP.Proofs.lem_kr1b_exceptional_set_composite in
/-- **Kollár 1.48.** If `S'` is a regular surface, `g : S' ⟶ S` is a morphism and
`σ : B_pS' ⟶ S'` is the blow-up of a closed point `p` with exceptional curve `E`, then
`Ex(σ ≫ g) = σ⁻¹(Ex(g)) ∪ E`. -/
@[mmp "lem_kr1b_exceptional_set_composite"]
public theorem exceptionalSet_blowUpToBase_comp {S' S : Scheme.{u}}
    (hS' : IsRegularSurface S') (g : S' ⟶ S) {p : S'} (hp : IsClosed ({p} : Set S')) :
    (MMP.Mori.exceptionalSet (blowUpToBase (pointIdeal hp) ≫ g) : Set (blowUp (pointIdeal hp))) =
      blowUpToBase (pointIdeal hp) ⁻¹' (MMP.Mori.exceptionalSet g : Set S') ∪
        ((exceptionalIdeal (pointIdeal hp)).support : Set (blowUp (pointIdeal hp))) := by
  set σ := blowUpToBase (pointIdeal hp)
  ext y
  simp only [Set.mem_union, Set.mem_preimage, SetLike.mem_coe, mem_exceptionalSet,
    mem_support_exceptionalIdeal_iff hp]
  change (σ ≫ g) y ∉ _ ↔ g (σ y) ∉ _ ∨ _
  constructor
  · intro hy
    by_contra! h
    obtain ⟨V, hV, hxV, hpV⟩ := exists_isBiregular_notMem hp g h.2 h.1
    exact hy (le_biregularLocus ((isBiregular_comp_iff hp g hpV).mpr hV) hxV)
  · have hn := notMem_of_isBiregular_comp hp hS' g (isBiregular_biregularLocus (σ ≫ g))
    rintro (hy | hy) hmem
    · exact hy (le_biregularLocus ((isBiregular_comp_iff hp g hn).mp
        (isBiregular_biregularLocus _)) hmem)
    · change g (σ y) ∈ _ at hmem
      exact hn (by rwa [hy] at hmem)

end MMP.Resolution.Kollar

end

/-!
### The inverse image of a curve under a composite of point blow-ups (Kollár 1.48)

Let `S` be a regular surface, `C ⊆ S` a closed subscheme and `S_m → ⋯ → S_0 = S` a sequence of
blow-ups of closed points `p_i ∈ S_i`, with composites `π_i : S_i → S` and iterated birational
transforms `C_i ⊆ S_i`. If every centre `p_i` lies over `C`, then set-theoretically
`π_m⁻¹(C) = C_m ∪ Ex(π_m)`.

### Main results

* `MMP.Resolution.PointBlowupSequence.support_comap_π_eq_union_exceptionalSet`:
  `π_m⁻¹(C) = C_m ∪ Ex(π_m)` as sets.

### References

* [J. Kollár, *Lectures on resolution of singularities*][kollar2007], 1.48.
-/

section

open CategoryTheory AlgebraicGeometry Topology MMP.Resolution MMP.Resolution.Kollar

namespace MMP.Proofs.lem_kr1b_preimage_decomposition

/-- The exceptional set of `e ≫ f` for an isomorphism `e` is the preimage of that of `f`. -/
private theorem exceptionalSet_iso_comp {X X' Y : Scheme.{u}} (e : X' ≅ X) (f : X ⟶ Y) :
    (MMP.Mori.exceptionalSet (e.hom ≫ f) : Set X') =
      e.hom ⁻¹' (MMP.Mori.exceptionalSet f : Set X) := by
  have h : MMP.Mori.biregularLocus (e.hom ≫ f) = MMP.Mori.biregularLocus f := by
    have key : ∀ V, MMP.Mori.IsBiregular (e.hom ≫ f) V ↔ MMP.Mori.IsBiregular f V := by
      intro V
      simp only [MMP.Mori.IsBiregular, morphismRestrict_comp]
      have : IsIso (e.hom ∣_ f ⁻¹ᵁ V) :=
        IsZariskiLocalAtTarget.restrict (P := MorphismProperty.isomorphisms Scheme)
          (inferInstanceAs (IsIso e.hom)) _
      exact ⟨fun h ↦ @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ this h,
        fun h ↦ @IsIso.comp_isIso _ _ _ _ _ _ _ this h⟩
    simp only [MMP.Mori.biregularLocus, key]
  ext x
  simp [MMP.Mori.exceptionalSet, h]

/-- An isomorphism has empty exceptional set. -/
private theorem exceptionalSet_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    (MMP.Mori.exceptionalSet f : Set X) = ∅ := by
  have h : MMP.Mori.biregularLocus f = ⊤ :=
    top_le_iff.mp (MMP.Mori.le_biregularLocus ((MMP.Mori.isBiregular_top_iff f).mpr ‹_›))
  ext x
  simp [MMP.Mori.exceptionalSet, h]

/-- Being a regular surface is invariant under isomorphism. -/
private theorem isRegularSurface_of_iso {X Y : Scheme.{u}} (e : X ≅ Y) (h : IsRegularSurface Y) :
    IsRegularSurface X := by
  obtain ⟨hN, hR, hD⟩ := h
  have : IsLocallyNoetherian Y := hN.toIsLocallyNoetherian
  have : CompactSpace Y := hN.toCompactSpace
  have : IsLocallyNoetherian X := isLocallyNoetherian_of_isOpenImmersion e.hom
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace e.hom
  have hst : ∀ x : X, Y.presheaf.stalk (e.hom x) ≃+* X.presheaf.stalk x := fun x =>
    have := isIso_stalkMap_hom_of_iso e x
    (asIso (e.hom.stalkMap x)).commRingCatIsoToRingEquiv
  refine ⟨⟨⟩, fun x => IsRegularLocalRing.of_ringEquiv (hst x), fun x hx => ?_⟩
  rw [← ringKrullDim_eq_of_ringEquiv (hst x)]
  apply hD
  rw [← Set.image_singleton]
  exact e.hom.isClosedEmbedding.isClosedMap _ hx

/-- In a Noetherian quasi-sober space, a point outside a dense open set has a proper
generalization. -/
private theorem exists_ne_specializes_of_notMem_dense {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X] [QuasiSober X] {U : Set X} (hU : IsOpen U)
    (hd : Dense U) {x : X} (hx : x ∉ U) : ∃ y, y ⤳ x ∧ y ≠ x := by
  obtain ⟨Z, hZ, hxZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
    (isIrreducible_singleton (x := x)).closure
  obtain ⟨y, hy⟩ := QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents Z hZ)
  have hyx : y ⤳ x := specializes_iff_mem_closure.mpr (hy.symm ▸ hxZ (subset_closure rfl))
  refine ⟨y, hyx, fun hxy => ?_⟩
  subst hxy
  obtain ⟨o, ho, hne, hoZ⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent Z hZ
  obtain ⟨u, huo, huU⟩ := hd.inter_open_nonempty o ho hne
  have : y ⤳ u := specializes_iff_mem_closure.mpr (hy.symm ▸ hoZ huo)
  exact hx (this.mem_open hU huU)

/-- The dimension of local rings grows along specialization. -/
private theorem ringKrullDim_stalk_le_of_specializes {X : Scheme.{u}} {x y : X} (h : x ⤳ y) :
    ringKrullDim (X.presheaf.stalk x) ≤ ringKrullDim (X.presheaf.stalk y) := by
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight]
  exact_mod_cast Order.coheight_anti (α := X) (show y ≤ x from h)

/-- A regular surface with a closed point has dimension two. -/
private theorem topologicalKrullDim_eq_two {S : Scheme.{u}} (hS : IsRegularSurface S) {p : S}
    (hp : IsClosed ({p} : Set S)) : topologicalKrullDim S = 2 := by
  obtain ⟨hN, -, hD⟩ := hS
  rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
  apply le_antisymm
  · refine iSup_le fun x => ?_
    obtain ⟨y, hy, hyc⟩ := (isClosed_closure (s := ({x} : Set S))).exists_closed_singleton
      ⟨x, subset_closure rfl⟩
    exact (ringKrullDim_stalk_le_of_specializes (specializes_iff_mem_closure.mpr hy)).trans
      (hD y hyc).le
  · exact (hD p hp).symm.le.trans (le_iSup (fun z => ringKrullDim (S.presheaf.stalk z)) p)

/-- A scheme-theoretically dense open of a Noetherian scheme is dense. -/
private theorem dense_of_isSchemeTheoreticallyDense {X : Scheme.{u}} [IsNoetherian X]
    (U : X.Opens) (h : U.IsSchemeTheoreticallyDense) : Dense (U : Set X) := by
  have : IsLocallyNoetherian X := IsNoetherian.toIsLocallyNoetherian
  have : QuasiCompact U.ι := instQuasiCompactOfIsLocallyNoetherianOfIsOpenImmersion (f := U.ι)
  have := (Scheme.Opens.isSchemeTheoreticallyDense_iff_isSchemeTheoreticallyDominant U).1 h
  have hd : Dense (Set.range U.ι) := by
    rw [dense_iff_closure_eq, ← Scheme.Hom.support_ker, U.ι.ker_eq_bot,
      Scheme.IdealSheafData.support_bot, TopologicalSpace.Closeds.coe_top]
  rwa [Scheme.Opens.range_ι] at hd

/-- The complement of the exceptional divisor of a Noetherian blow-up is dense. -/
private theorem dense_compl_support_exceptionalIdeal {X : Scheme.{u}} (I : X.IdealSheafData)
    [IsNoetherian (blowUp I)] :
    Dense (((exceptionalIdeal I).support.compl : (blowUp I).Opens) : Set (blowUp I)) := by
  set φ := (Stacks.Blowup.blowUpIso I).hom
  have : IsLocallyNoetherian (blowUp I) := IsNoetherian.toIsLocallyNoetherian
  have : IsLocallyNoetherian (Stacks.Blowup.blowUp I) := isLocallyNoetherian_of_isOpenImmersion φ
  have : CompactSpace (Stacks.Blowup.blowUp I) := QuasiCompact.compactSpace_of_compactSpace φ
  have : IsNoetherian (Stacks.Blowup.blowUp I) := ⟨⟩
  have hd := dense_of_isSchemeTheoreticallyDense _
    (Stacks.Blowup.isSchemeTheoreticallyDense_compl_support_exceptionalIdeal I)
  have hsurj : Function.Surjective φ := φ.homeomorph.surjective
  have key := hsurj.denseRange.dense_image φ.continuous hd
  have heq : Stacks.Blowup.exceptionalIdeal I = (exceptionalIdeal I).comap φ := by
    rw [exceptionalIdeal, ← Scheme.IdealSheafData.comap_comp, Stacks.Blowup.blowUpIso_hom_comp]
    rfl
  have hpre : ((((exceptionalIdeal I).comap φ).support.compl : (Stacks.Blowup.blowUp I).Opens) :
      Set (Stacks.Blowup.blowUp I)) =
      φ ⁻¹' (((exceptionalIdeal I).support.compl : (blowUp I).Opens) : Set (blowUp I)) := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  rwa [heq, hpre, Set.image_preimage_eq _ hsurj] at key

/-- The blow-up of a regular surface at a closed point is a regular surface. -/
private theorem isRegularSurface_blowUp {S : Scheme.{u}} (hS : IsRegularSurface S) {p : S}
    (hp : IsClosed ({p} : Set S)) : IsRegularSurface (blowUp (pointIdeal hp)) := by
  have hN : IsNoetherian S := hS.1
  have hLN : IsLocallyNoetherian S := IsNoetherian.toIsLocallyNoetherian
  have hreg : IsRegular S := (isRegular_iff_regular_stalks S).2 ⟨hLN, hS.2.1⟩
  obtain ⟨hreg', hdim'⟩ := isRegular_and_topologicalKrullDim_blowUp_vanishingIdeal_singleton S
    hreg (topologicalKrullDim_eq_two hS hp) p hp
  have hN' : IsNoetherian (blowUp (pointIdeal hp)) :=
    Stacks.ResolutionOfSurfaces.isNoetherian_blowUp _
  refine ⟨hN', ((isRegular_iff_regular_stalks _).1 hreg').2, fun q hq => ?_⟩
  set b := blowUpToBase (pointIdeal hp)
  set E := (exceptionalIdeal (pointIdeal hp)).support
  apply le_antisymm
  · rw [← hdim', topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
    exact le_iSup (fun z => ringKrullDim ((blowUp (pointIdeal hp)).presheaf.stalk z)) q
  have hE := Set.ext_iff.mp (preimage_compl_eq_compl_support_exceptionalIdeal hp) q
  by_cases hqE : q ∈ (E : Set (blowUp (pointIdeal hp)))
  · -- `q` lies on the exceptional curve
    obtain ⟨e, -⟩ :=
      Stacks.Blowup.exists_isExceptionalCurveOfFirstKind_exceptionalIdeal_vanishingIdeal
      p hp (hS.2.1 p) (hS.2.2 p hp)
    have hint := isIntegral_subscheme_of_iso_projectiveLineProj _ _ e
    set ι := (exceptionalIdeal (pointIdeal hp)).subschemeι
    have hrange : Set.range ι.base = (E : Set _) := Scheme.IdealSheafData.range_subschemeι _
    set η := ι (genericPoint (exceptionalIdeal (pointIdeal hp)).subscheme)
    have hη : ∀ z, η ⤳ ι z := fun z => (genericPoint_specializes z).map ι.continuous
    obtain ⟨q', rfl⟩ : q ∈ Set.range ι.base := by rw [hrange]; exact hqE
    have hηq : η ≠ ι q' := by
      intro h
      have hns := ExceptionalCurveContraction.not_subsingleton_projectiveLineProj (e := e)
      obtain ⟨a, a', haa'⟩ := not_subsingleton_iff_nontrivial.mp hns |>.exists_pair_ne
      have hpt : ∀ z, ι z = ι q' := fun z => by
        have := specializes_iff_mem_closure.mp (hη z)
        rwa [h, hq.closure_eq, Set.mem_singleton_iff] at this
      have hinj : Function.Injective ι.base := ι.isClosedEmbedding.injective
      exact haa' (e.hom.homeomorph.injective (hinj ((hpt _).trans (hpt _).symm)))
    have hηE : η ∉ ((E.compl : (blowUp (pointIdeal hp)).Opens) : Set _) := by
      simp only [TopologicalSpace.Closeds.compl, TopologicalSpace.Opens.coe_mk, Set.mem_compl_iff,
        not_not]
      rw [← hrange]
      exact ⟨_, rfl⟩
    have : TopologicalSpace.NoetherianSpace (blowUp (pointIdeal hp)) := inferInstance
    have : QuasiSober (blowUp (pointIdeal hp)) := inferInstance
    obtain ⟨ξ, hξη, hξne⟩ := exists_ne_specializes_of_notMem_dense (X := blowUp (pointIdeal hp))
      E.compl.2
      (dense_compl_support_exceptionalIdeal _) hηE
    have h1 : ι q' < η := lt_of_le_not_ge (show ι q' ≤ η from hη q')
      (fun h => hηq ((hη q').antisymm h).eq)
    have h2 : η < ξ := lt_of_le_not_ge (show η ≤ ξ from hξη)
      (fun h => hξne (hξη.antisymm h).eq)
    rw [ringKrullDim_stalk_eq_coheight]
    refine WithBot.coe_le_coe.mpr ?_
    calc (2 : ℕ∞) ≤ Order.coheight ξ + 1 + 1 := by
          rw [add_assoc]
          exact le_add_self
      _ ≤ Order.coheight η + 1 := by
          gcongr
          exact Order.coheight_add_one_le h2
      _ ≤ _ := Order.coheight_add_one_le h1
  · -- off the exceptional curve the blow-up is a local isomorphism
    have hqU : q ∈ b ⁻¹ᵁ complPoint hp := hE.mpr hqE
    have := isIso_stalkMap_of_isIso_morphismRestrict b
      (isIso_blowUpToBase_restrict_compl_point hp) hqU
    have hbq : IsClosed ({b q} : Set S) := by
      rw [← Set.image_singleton]
      exact b.isClosedMap _ hq
    rw [← ringKrullDim_eq_of_ringEquiv (asIso (b.stalkMap q)).commRingCatIsoToRingEquiv,
      hS.2.2 _ hbq]

/-- Every scheme of a point blow-up sequence of a regular surface is a regular surface. -/
private theorem isRegularSurface_S {S : Scheme.{u}} (s : PointBlowupSequence S)
    (hS : IsRegularSurface S) : ∀ (i : ℕ), (i : ℕ∞) ≤ s.length → IsRegularSurface (s.S i)
  | 0, _ => isRegularSurface_of_iso s.zeroIso hS
  | i + 1, h =>
    isRegularSurface_of_iso (s.blowupIso i (PointBlowupSequence.coe_lt_of_succ_le h))
      (isRegularSurface_blowUp
        (isRegularSurface_S s hS i (PointBlowupSequence.coe_lt_of_succ_le h).le)
        (s.isClosed_p i (PointBlowupSequence.coe_lt_of_succ_le h)))

/-- The set-theoretic step: if `b⁻¹(p) = E`, `T` is closed and `p ∈ T ∪ X`, then
`b⁻¹(T ∪ X) = closure (b⁻¹ T ∖ E) ∪ (b⁻¹ X ∪ E)`. -/
private theorem preimage_union_eq {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (b : α → β) (hb : Continuous b) {p : β} {E : Set α} (hE : E = b ⁻¹' {p}) {T X : Set β}
    (hT : IsClosed T) (hp : p ∈ T ∪ X) :
    b ⁻¹' (T ∪ X) = closure (b ⁻¹' T \ E) ∪ (b ⁻¹' X ∪ E) := by
  subst hE
  apply Set.Subset.antisymm
  · intro x hx
    by_cases hxE : b x = p
    · exact Or.inr (Or.inr hxE)
    rcases hx with hx | hx
    · exact Or.inl (subset_closure ⟨hx, hxE⟩)
    · exact Or.inr (Or.inl hx)
  · rintro x (hx | hx | hx)
    · exact Or.inl (closure_minimal Set.diff_subset (hT.preimage hb) hx)
    · exact Or.inr hx
    · simpa [show b x = p from hx] using hp

/-- The exceptional curve of the blow-up of a closed point `p` is the fibre over `p`. -/
private theorem support_exceptionalIdeal_eq_preimage {S : Scheme.{u}} {p : S}
    (hp : IsClosed ({p} : Set S)) :
    ((exceptionalIdeal (pointIdeal hp)).support : Set (blowUp (pointIdeal hp))) =
      blowUpToBase (pointIdeal hp) ⁻¹' {p} := by
  rw [← compl_inj_iff, ← preimage_compl_eq_compl_support_exceptionalIdeal hp]
  rfl

/-- The support of the birational transform of `T` in the blow-up of a closed point `p` of a
regular surface is the closure of `π⁻¹(T) ∖ E`. -/
private theorem support_birationalTransform {S : Scheme.{u}} (hS : IsRegularSurface S) {p : S}
    (hp : IsClosed ({p} : Set S)) (T : S.IdealSheafData) :
    ((birationalTransform p hp T).support : Set (blowUp (pointIdeal hp))) =
      closure (blowUpToBase (pointIdeal hp) ⁻¹' (T.support : Set S) \
        (exceptionalIdeal (pointIdeal hp)).support) := by
  have : IsNoetherian (blowUp (pointIdeal hp)) := (isRegularSurface_blowUp hS hp).1
  set q := Limits.pullback.snd T.subschemeι (blowUpToBase (pointIdeal hp))
  set U := q ⁻¹ᵁ (exceptionalIdeal (pointIdeal hp)).support.compl
  have : TopologicalSpace.NoetherianSpace U.toScheme :=
    (q.isClosedEmbedding.isInducing.comp U.ι.isOpenEmbedding.isInducing).noetherianSpace
  rw [birationalTransform, Scheme.Hom.support_ker]
  congr 1
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
    Scheme.Hom.coe_preimage, Set.image_preimage_eq_inter_range, Scheme.Pullback.range_snd,
    Scheme.IdealSheafData.range_subschemeι, Set.diff_eq, Set.inter_comm]
  rfl

end MMP.Proofs.lem_kr1b_preimage_decomposition

namespace MMP.Resolution.PointBlowupSequence

open MMP.Proofs.lem_kr1b_preimage_decomposition in
/-- **Kollár 1.48.** Let `S` be a regular surface, `C ⊆ S` a closed subscheme and `s` a sequence
of point blow-ups of `S` whose first `m` centres `p_i` lie in `π_i⁻¹(C)`. Then
`π_m⁻¹(C) = C_m ∪ Ex(π_m)` as sets, `C_m` the `m`-th birational transform of `C`. -/
@[mmp "lem_kr1b_preimage_decomposition"]
public theorem support_comap_π_eq_union_exceptionalSet {S : Scheme.{u}}
    (s : PointBlowupSequence S) (hS : IsRegularSurface S) (C : S.IdealSheafData)
    (m : ℕ) (hm : (m : ℕ∞) ≤ s.length)
    (hp : ∀ (i : ℕ) (hi : i < m),
      s.p i ∈ (C.comap (s.π i ((ENat.natCast_lt_natCast.mpr hi).le.trans hm))).support) :
    ((C.comap (s.π m hm)).support : Set (s.S m)) =
      ((s.transformedSubscheme C m).support : Set (s.S m)) ∪
        (MMP.Mori.exceptionalSet (s.π m hm) : Set (s.S m)) := by
  revert hm hp
  induction m with
  | zero =>
    intro hm _
    simp only [PointBlowupSequence.π, PointBlowupSequence.transformedSubscheme,
      exceptionalSet_of_isIso, Set.union_empty]
  | succ m ih =>
    intro hm hp
    have hi : (m : ℕ∞) < s.length := PointBlowupSequence.coe_lt_of_succ_le hm
    have ih' := ih hi.le (fun i hi' => hp i (Nat.lt_succ_of_lt hi'))
    have hpm := hp m (Nat.lt_succ_self m)
    have hSm := isRegularSurface_S s hS m hi.le
    set ho := s.isClosed_p m hi
    set b := blowUpToBase (pointIdeal ho)
    set φ := (s.blowupIso m hi).hom
    set T := s.transformedSubscheme C m
    set E := ((exceptionalIdeal (pointIdeal ho)).support : Set (blowUp (pointIdeal ho)))
    have hπ : s.π (m + 1) hm = φ ≫ b ≫ s.π m hi.le := by
      simp only [PointBlowupSequence.π, PointBlowupSequence.σ, Category.assoc]; rfl
    have hT : ((s.transformedSubscheme C (m + 1)).support : Set _) =
        φ ⁻¹' closure (b ⁻¹' (T.support : Set (s.S m)) \ E) := by
      simp only [PointBlowupSequence.transformedSubscheme, dif_pos hi,
        Scheme.IdealSheafData.support_comap]
      rw [← support_birationalTransform hSm ho T]
      rfl
    have hEx : (MMP.Mori.exceptionalSet (s.π (m + 1) hm) : Set (s.S (m + 1))) =
        φ ⁻¹' (b ⁻¹' (MMP.Mori.exceptionalSet (s.π m hi.le) : Set (s.S m)) ∪ E) := by
      rw [hπ, exceptionalSet_iso_comp, exceptionalSet_blowUpToBase_comp hSm]
    have hP : ((C.comap (s.π (m + 1) hm)).support : Set (s.S (m + 1))) =
        φ ⁻¹' (b ⁻¹' ((C.comap (s.π m hi.le)).support : Set (s.S m))) := by
      simp only [Scheme.IdealSheafData.support_comap, hπ]
      rfl
    rw [hP, hT, hEx, ← Set.preimage_union, ih']
    congr 1
    exact preimage_union_eq b b.continuous (support_exceptionalIdeal_eq_preimage ho)
      T.support.isClosed (ih' ▸ hpm)

end MMP.Resolution.PointBlowupSequence

end

/-!
### Contraction of `(x^b, y)^m` from a blow-up chart (Kollár 1.70)

Let `(R, 𝔪)` be a two-dimensional regular local ring with regular system of parameters
`(x, y)`, with fraction field `K`, and let `b > a ≥ 1`, `m ≥ 1`. Let `A = R[y/x^a] ⊆ K` and
`t = y/x^a ∈ A`. If `O` is a localization of `A` at a submonoid `S` disjoint from the ideal
`(x, t)A` (for instance the local ring of `A` at the maximal ideal `(x, t)A`), then the
ideal `(x^b, y)^m` of `R` is contracted from `O`: `R ∩ (x^b, y)^m O = (x^b, y)^m`.

The proof uses the monomial valuation `v` of `K` with `v(x) = 1`, `v(y) = b`, which is
non-negative on `O` and at least `bm` on `(x^b, y)^m O`.

### Main results

* `MMP.Resolution.Kollar.comap_map_span_pow_of_isLocalization_adjoin_div`:
  `(I.map (algebraMap R O)).comap (algebraMap R O) = I` for `I = (x^b, y)^m`.

### References

* [J. Kollár, *Lectures on resolution of singularities*][kollar2007], 1.69–1.70.
-/

section

open MMP.Resolution IsLocalRing

namespace MMP.Proofs.lem_kr1c_contraction_of_mth_power_ideal_from_chart

open IsLocalRing MMP.Resolution

private lemma span_pair_eq {R : Type*} [CommRing R] [IsLocalRing R] {x y : R}
    (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y]) :
    Ideal.span {x, y} = maximalIdeal R := by
  rw [← hxy.1]; congr 1; ext; simp [Matrix.range_cons, Set.pair_comm]

private lemma notMem_span_sq {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {x y : R} (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y]) :
    x ∉ Ideal.span {x ^ 2, y} := by
  intro h
  have hm := span_pair_eq hxy
  have hxm : x ∈ maximalIdeal R := hm ▸ Ideal.subset_span (by simp)
  obtain ⟨r, s, hrs⟩ := Ideal.mem_span_pair.1 h
  have hu : IsUnit (1 - r * x) := by
    by_contra hc
    have := (maximalIdeal R).add_mem ((IsLocalRing.mem_maximalIdeal _).2 hc)
      ((maximalIdeal R).mul_mem_left r hxm)
    rw [sub_add_cancel] at this
    exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 this)
  have hxy' : x ∈ Ideal.span {y} := by
    rw [Ideal.mem_span_singleton']
    refine ⟨s * ↑hu.unit⁻¹, ?_⟩
    have : x * (1 - r * x) = s * y := by linear_combination -hrs
    calc s * ↑hu.unit⁻¹ * y = x * (1 - r * x) * ↑hu.unit⁻¹ := by rw [this]; ring
      _ = x := by rw [mul_assoc, IsUnit.mul_val_inv, mul_one]
  have hmy : maximalIdeal R = Ideal.span {y} := by
    rw [← hm]
    refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.span_mono (by simp))
    rintro z (rfl | rfl)
    · exact hxy'
    · exact Ideal.subset_span rfl
  have h1 := ringKrullDim_le_spanFinrank_maximalIdeal (R := R)
  rw [hmy, hxy.2] at h1
  have h2 := Submodule.spanFinrank_span_le_ncard_of_finite (R := R) (Set.finite_singleton y)
  rw [Set.ncard_singleton] at h2
  have : ((2 : ℕ) : WithBot ℕ∞) ≤ ((1 : ℕ) : WithBot ℕ∞) := h1.trans (by exact_mod_cast h2)
  norm_num at this

section Monomial

variable {R : Type*} [CommRing R] (x y : R) (w : ℕ)

private lemma monomialIdeal_zero : monomialIdeal x y w 0 = ⊤ :=
  (Ideal.eq_top_iff_one _).2 (Ideal.subset_span ⟨0, 0, by simp, by simp⟩)

private lemma monomialIdeal_anti {ν μ : ℕ} (h : ν ≤ μ) :
    monomialIdeal x y w μ ≤ monomialIdeal x y w ν :=
  Ideal.span_mono fun _ ⟨i, j, hij, hr⟩ => ⟨i, j, h.trans hij, hr⟩

private lemma le_monomialValuation {s : R} {ν : ℕ} (hs : s ∈ monomialIdeal x y w ν) :
    (ν : ℕ∞) ≤ monomialValuation x y w s :=
  le_iSup₂ (f := fun (μ : ℕ) (_ : s ∈ monomialIdeal x y w μ) => (μ : ℕ∞)) ν hs

private lemma mem_of_le_monomialValuation {s : R} {ν : ℕ}
    (hs : (ν : ℕ∞) ≤ monomialValuation x y w s) : s ∈ monomialIdeal x y w ν := by
  by_contra hc
  rcases Nat.eq_zero_or_pos ν with rfl | hν
  · have h1 : (1 : R) ∈ monomialIdeal x y w 0 := Ideal.subset_span ⟨0, 0, by simp, by simp⟩
    exact hc (by simpa using Ideal.mul_mem_left _ s h1)
  have : monomialValuation x y w s ≤ ((ν - 1 : ℕ) : ℕ∞) := by
    refine iSup₂_le fun μ hμ => ?_
    have : μ < ν := by
      by_contra h; exact hc (monomialIdeal_anti x y w (not_lt.1 h) hμ)
    exact_mod_cast Nat.le_sub_one_of_lt this
  have := hs.trans this
  norm_cast at this
  omega

private lemma monomialIdeal_mul_pow_eq (m : ℕ) :
    monomialIdeal x y w (w * m) = Ideal.span {x ^ w, y} ^ m := by
  apply le_antisymm
  · rw [monomialIdeal, Ideal.span_le]
    rintro _ ⟨i, j, hij, rfl⟩
    rcases le_or_gt m j with hj | hj
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
      rw [pow_add]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _
        (Ideal.pow_mem_pow (Ideal.subset_span (by simp)) m))
    · have hi : w * (m - j) ≤ i := by
        have : w * m = w * (m - j) + w * j := by rw [← mul_add, Nat.sub_add_cancel hj.le]
        omega
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
      have : x ^ (w * (m - j) + k) * y ^ j = x ^ k * ((x ^ w) ^ (m - j) * y ^ j) := by
        rw [pow_add, pow_mul]; ring
      rw [this]
      refine Ideal.mul_mem_left _ _ ?_
      have := Ideal.mul_mem_mul
        (Ideal.pow_mem_pow (I := Ideal.span {x ^ w, y})
          (Ideal.subset_span (Set.mem_insert _ _)) (m - j))
        (Ideal.pow_mem_pow (I := Ideal.span {x ^ w, y})
          (Ideal.subset_span (Set.mem_insert_of_mem _ rfl)) j)
      rwa [← pow_add, Nat.sub_add_cancel hj.le] at this
  · induction m with
    | zero => simp [monomialIdeal, Ideal.eq_top_iff_one]; exact Ideal.subset_span ⟨0, 0, by simp⟩
    | succ k ih =>
      rw [pow_succ]
      refine (Ideal.mul_mono_left ih).trans ?_
      rw [monomialIdeal, Ideal.span_mul_span, Ideal.span_le]
      rintro _ ⟨_, ⟨i, j, hij, rfl⟩, _, hg, rfl⟩
      rcases hg with rfl | rfl
      · exact Ideal.subset_span ⟨i + w, j, by rw [mul_add]; omega, by ring⟩
      · exact Ideal.subset_span ⟨i, j + 1, by rw [mul_add, mul_add]; omega, by ring⟩

private lemma monomialIdeal_two_le {w : ℕ} (hw : 2 ≤ w) :
    monomialIdeal x y w 2 ≤ Ideal.span {x ^ 2, y} := by
  rw [monomialIdeal, Ideal.span_le]
  rintro _ ⟨i, j, hij, rfl⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show 2 ≤ i by omega)
    rw [pow_add, pow_zero, mul_one]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [pow_add, pow_one]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))

/-- For a valuation `V` of `K` extending `monomialValuation x y w`, `n ≤ V r` iff `r ∈ I_n`. -/
private lemma coe_le_iff_mem_monomialIdeal {K : Type*} [Field K] [Algebra R K]
    {V : AddValuation K (WithTop ℤ)}
    (hV : ∀ s : R, V (algebraMap R K s) = (monomialValuation x y w s).map (Nat.cast : ℕ → ℤ))
    (r : R) (n : ℕ) :
    ((n : ℤ) : WithTop ℤ) ≤ V (algebraMap R K r) ↔ r ∈ monomialIdeal x y w n := by
  have key : ∀ v : ℕ∞, ((n : ℤ) : WithTop ℤ) ≤ v.map (Nat.cast : ℕ → ℤ) ↔ (n : ℕ∞) ≤ v := by
    refine ENat.recTopCoe (by simp) fun k => ?_
    simp only [ENat.map_coe, Nat.cast_le]
    norm_cast
  rw [hV, key]
  exact ⟨mem_of_le_monomialValuation x y w, le_monomialValuation x y w⟩

end Monomial

private lemma monomialValuation_eq_one {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {x y : R} (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y]) {w : ℕ}
    (hw : 2 ≤ w) : monomialValuation x y w x = 1 := by
  refine le_antisymm (iSup₂_le fun μ hμ => ?_) ?_
  · by_contra h
    exact notMem_span_sq hxy (monomialIdeal_two_le x y hw
      (monomialIdeal_anti x y w (show 2 ≤ μ by exact_mod_cast (not_le.1 h)) hμ))
  · exact_mod_cast le_monomialValuation x y w (ν := 1) (Ideal.subset_span ⟨1, 0, by simp, by simp⟩)

/-- Every element of `R[t]` is `r₀ + t γ` with `r₀ ∈ R` and `γ ∈ R[t]`. -/
private lemma exists_eq_algebraMap_add_mul {R K : Type*} [CommRing R] [CommRing K] [Algebra R K]
    {t z : K} (hz : z ∈ Algebra.adjoin R {t}) :
    ∃ r₀ : R, ∃ γ ∈ Algebra.adjoin R {t}, z = algebraMap R K r₀ + t * γ := by
  have htA : t ∈ Algebra.adjoin R {t} := Algebra.subset_adjoin rfl
  induction hz using Algebra.adjoin_induction with
  | mem z hz => exact ⟨0, 1, Subalgebra.one_mem _, by simp [Set.mem_singleton_iff.1 hz]⟩
  | algebraMap r => exact ⟨r, 0, Subalgebra.zero_mem _, by simp⟩
  | add _ _ _ _ h₁ h₂ =>
    obtain ⟨r, γ, hγ, rfl⟩ := h₁
    obtain ⟨r', γ', hγ', rfl⟩ := h₂
    exact ⟨r + r', γ + γ', Subalgebra.add_mem _ hγ hγ', by rw [map_add]; ring⟩
  | mul _ _ _ _ h₁ h₂ =>
    obtain ⟨r, γ, hγ, rfl⟩ := h₁
    obtain ⟨r', γ', hγ', rfl⟩ := h₂
    refine ⟨r * r', γ * algebraMap R K r' + algebraMap R K r * γ' + t * γ * γ', ?_,
      by rw [map_mul]; ring⟩
    have := Subalgebra.algebraMap_mem (Algebra.adjoin R {t})
    exact add_mem (add_mem (mul_mem hγ (this r')) (mul_mem (this r) hγ'))
      (mul_mem (mul_mem htA hγ) hγ')

/-- A valuation nonnegative on `R` and on `t` is nonnegative on `R[t]`. -/
private lemma addValuation_nonneg_of_mem_adjoin {R K : Type*} [CommRing R] [Field K]
    [Algebra R K] {V : AddValuation K (WithTop ℤ)} (hV0 : ∀ r : R, 0 ≤ V (algebraMap R K r))
    {t z : K} (hVt : 0 ≤ V t) (hz : z ∈ Algebra.adjoin R {t}) : 0 ≤ V z := by
  induction hz using Algebra.adjoin_induction with
  | mem z hz => rwa [Set.mem_singleton_iff.1 hz]
  | algebraMap r => exact hV0 r
  | add _ _ _ _ h₁ h₂ => exact (le_min h₁ h₂).trans (V.map_add _ _)
  | mul _ _ _ _ h₁ h₂ => rw [V.map_mul]; exact add_nonneg h₁ h₂

/-- Let `𝔪 = (x, y)` and `t = y / x^a`. A valuation nonnegative on `R` with `V t > 0` vanishes on
every element of `R[t]` outside `(x, t) R[t]`: such an element is `r₀ + t γ` with `r₀` a unit. -/
private lemma addValuation_eq_zero_of_notMem_span {R K : Type*} [CommRing R] [IsLocalRing R]
    [Field K] [Algebra R K] {x y : R} (hm : Ideal.span {x, y} = maximalIdeal R) {a : ℕ} {t : K}
    (hxt : algebraMap R K x ^ a * t = algebraMap R K y) {V : AddValuation K (WithTop ℤ)}
    (hV0 : ∀ r : R, 0 ≤ V (algebraMap R K r)) (hVt : 0 < V t) {u : Algebra.adjoin R {t}}
    (hu : u ∉ Ideal.span {algebraMap R _ x, ⟨t, Algebra.subset_adjoin rfl⟩}) :
    V (u : K) = 0 := by
  obtain ⟨r₀, γ, hγ, hu'⟩ := exists_eq_algebraMap_add_mul u.2
  have hunit : IsUnit r₀ := by
    by_contra h
    obtain ⟨p, q, hpq⟩ := Ideal.mem_span_pair.1 (hm ▸ (mem_maximalIdeal _).2 h)
    apply hu
    have : u = algebraMap R _ p * algebraMap R _ x +
        (algebraMap R _ q * algebraMap R _ x ^ a + ⟨γ, hγ⟩) * ⟨t, Algebra.subset_adjoin rfl⟩ :=
      Subtype.ext (by simp [hu', ← hpq, ← hxt]; ring)
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl)))
  have hVr₀ : V (algebraMap R K r₀) = 0 := by
    refine le_antisymm ?_ (hV0 r₀)
    have h := congrArg V (congrArg (algebraMap R K) hunit.mul_val_inv)
    rw [map_mul, V.map_mul, map_one, V.map_one] at h
    exact h ▸ le_add_of_nonneg_right (hV0 _)
  have hlt : V (algebraMap R K r₀) < V (t * γ) := by
    rw [hVr₀, V.map_mul]
    exact add_pos_of_pos_of_nonneg hVt (addValuation_nonneg_of_mem_adjoin hV0 hVt.le hγ)
  rw [hu', V.map_add_eq_of_lt_left hlt, hVr₀]

end MMP.Proofs.lem_kr1c_contraction_of_mth_power_ideal_from_chart

namespace MMP.Resolution.Kollar

open MMP.Proofs.lem_kr1c_contraction_of_mth_power_ideal_from_chart in
/-- Let `(x, y)` be a regular system of parameters of a two-dimensional regular local ring `R`
with fraction field `K`, let `b > a ≥ 1` and `m ≥ 1`, and let `O` be a localization of
`A = R[y/x^a] ⊆ K` at a submonoid disjoint from `(x, y/x^a)A`. Then the ideal `(x^b, y)^m` of `R`
is contracted from `O`. -/
@[mmp "lem_kr1c_contraction_of_mth_power_ideal_from_chart"]
public theorem comap_map_span_pow_of_isLocalization_adjoin_div
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {x y : R} (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y])
    {a b m : ℕ} (ha : 1 ≤ a) (hab : a < b) (hm : 1 ≤ m)
    (S : Submonoid (Algebra.adjoin R {algebraMap R K y / algebraMap R K x ^ a}))
    (hS : ∀ s ∈ S, s ∉ Ideal.span
      {algebraMap R (Algebra.adjoin R {algebraMap R K y / algebraMap R K x ^ a}) x,
        ⟨algebraMap R K y / algebraMap R K x ^ a, Algebra.subset_adjoin rfl⟩})
    (O : Type*) [CommRing O]
    [Algebra (Algebra.adjoin R {algebraMap R K y / algebraMap R K x ^ a}) O]
    [IsLocalization S O] [Algebra R O]
    [IsScalarTower R (Algebra.adjoin R {algebraMap R K y / algebraMap R K x ^ a}) O] :
    ((Ideal.span {x ^ b, y} ^ m).map (algebraMap R O)).comap (algebraMap R O) =
      Ideal.span {x ^ b, y} ^ m := by
  obtain ⟨-, -, -, V, hV, -⟩ := exists_addValuation_monomialValuation K hxy (w := b) (by omega)
  have hle := coe_le_iff_mem_monomialIdeal x y b hV
  have hV0 (r : R) : 0 ≤ V (algebraMap R K r) := by
    simpa using (hle r 0).2 (by rw [monomialIdeal_zero]; trivial)
  have hx0 : x ≠ 0 := by rintro rfl; exact notMem_span_sq hxy (Ideal.zero_mem _)
  have hVy := (hle y b).2 (Ideal.subset_span ⟨0, 1, by simp, by simp⟩)
  generalize ht : algebraMap R K y / algebraMap R K x ^ a = t at *
  have hxt : algebraMap R K x ^ a * t = algebraMap R K y := by rw [← ht]; field_simp [hx0]
  have hVt : 0 < V t := by
    rw [← hxt, V.map_mul, V.map_pow, hV, monomialValuation_eq_one hxy (by omega)] at hVy
    cases h' : V t with
    | top => exact WithTop.coe_lt_top 0
    | coe n => rw [h'] at hVy; simp at hVy; norm_cast at hVy ⊢; omega
  have hA (z : Algebra.adjoin R {t}) : 0 ≤ V (z : K) :=
    addValuation_nonneg_of_mem_adjoin hV0 hVt.le z.2
  have hJ : ∀ j ∈ (Ideal.span {x ^ b, y} ^ m).map (algebraMap R (Algebra.adjoin R {t})),
      (((b * m : ℕ) : ℤ) : WithTop ℤ) ≤ V (j : K) := by
    intro j hj
    induction hj using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨g, hg, rfl⟩ := hz
      exact (hle g _).2 (by rwa [monomialIdeal_mul_pow_eq])
    | zero => simp
    | add _ _ _ _ h1 h2 => exact (le_min h1 h2).trans (V.map_add _ _)
    | smul c z _ h =>
      rw [smul_eq_mul, Subalgebra.coe_mul, V.map_mul]
      exact le_add_of_nonneg_of_le (hA c) h
  have hSle : S ≤ nonZeroDivisors (Algebra.adjoin R {t}) := fun u hu =>
    mem_nonZeroDivisors_of_ne_zero fun h => hS u hu (h ▸ Ideal.zero_mem _)
  refine le_antisymm (fun s hs => ?_) Ideal.le_comap_map
  rw [Ideal.mem_comap, IsScalarTower.algebraMap_eq R (Algebra.adjoin R {t}) O, ← Ideal.map_map,
    RingHom.comp_apply] at hs
  obtain ⟨⟨j, u⟩, hju⟩ := (IsLocalization.mem_map_algebraMap_iff S O).1 hs
  rw [← map_mul] at hju
  have hK := congrArg (fun z : Algebra.adjoin R {t} => V (z : K))
    (IsLocalization.injective O hSle hju)
  simp only [Subalgebra.coe_mul, V.map_mul, add_zero,
    addValuation_eq_zero_of_notMem_span (span_pair_eq hxy) hxt hV0 hVt (hS u u.2)] at hK
  rw [← monomialIdeal_mul_pow_eq, ← hle]
  exact hK ▸ hJ j j.2

end MMP.Resolution.Kollar

end

/-!
### The normalized graph of two resolutions of a surface

Let `f₁ : X₁ ⟶ Y` and `f₂ : X₂ ⟶ Y` be resolutions of a quasi-projective surface `Y` over a
field `k`. The birational map `f₂⁻¹ ∘ f₁ : X₁ ⇢ X₂` is represented by a morphism `h : U ⟶ X₂`
on a nonempty open `U ⊆ X₁` with `h ≫ f₂ = U.ι ≫ f₁`. Let `Γ ⊆ X₁ ×_Y X₂` be the closure of the
graph of `h`, `S ⟶ Γ` its normalization, and `gᵢ : S ⟶ Xᵢ` the two projections. Then `S` is a
normal quasi-projective surface, both `gᵢ` are projective and birational, `f₁ ∘ g₁ = f₂ ∘ g₂`,
and no curve of `S` is contracted by both `g₁` and `g₂`.

### Main results

* `MMP.Resolution.IsProjectiveSurfaceResolution.graphNormalization_spec`: the properties of the
  normalized graph `S` of two resolutions.

### Implementation notes

The normalization `S` of the graph closure `Γ` is Mathlib's relative normalization
`AlgebraicGeometry.Scheme.Hom.normalization` of `X₁ ×_Y X₂` in `U`, along the graph morphism
`φ = (U.ι, h) : U ⟶ X₁ ×_Y X₂`: the integral closure of `𝒪_{X₁ ×_Y X₂}` in `φ_* 𝒪_U`. Since
`U` is integral, this factors through the scheme-theoretic image `Γ` of `φ`, and it is the
integral closure of `𝒪_Γ` in the function field `k(U) = k(Γ)`, that is, the normalization of
`Γ`. The structure morphism `S ⟶ X₁ ×_Y X₂` is
`AlgebraicGeometry.Scheme.Hom.fromNormalization`, and `gᵢ` is its composite with the `i`-th
projection. The quasi-compactness and quasi-separatedness of `φ`, which the relative
normalization requires, hold automatically because `U` is Noetherian.

### References

* [J. Kollár, *Lectures on resolution of singularities*, proof of Theorem 2.16]
-/

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MMP.Resolution

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Proofs.lem_kr2a_graph_normalization_two_resolutions

variable {k : Type u} [Field k]

/-- An isomorphism followed by an H-projective morphism is H-projective. -/
private theorem isProjectiveMorphism_iso_comp {X X' S : Scheme.{u}} (e : X' ≅ X) {f : X ⟶ S}
    (hf : IsProjectiveMorphism f) : IsProjectiveMorphism (e.hom ≫ f) := by
  obtain ⟨n, i, hi, rfl⟩ := hf
  exact ⟨n, e.hom ≫ i, inferInstance, by rw [Category.assoc]⟩

/-- The first projection of `X₁ ×_Y X₂` is H-projective when `f₂` is. -/
private theorem isProjectiveMorphism_pullback_fst {X₁ X₂ Y : Scheme.{u}} (f₁ : X₁ ⟶ Y)
    {f₂ : X₂ ⟶ Y} (hf₂ : IsProjectiveMorphism f₂) : IsProjectiveMorphism (pullback.fst f₁ f₂) := by
  rw [← pullbackSymmetry_hom_comp_snd]
  exact isProjectiveMorphism_iso_comp _ (hf₂.baseChange f₁)

/-- A finite morphism into a scheme quasi-projective over a field is H-projective. -/
private theorem isProjectiveMorphism_of_isFinite {Y' Y : Scheme.{u}} (g : Y' ⟶ Y) [IsFinite g]
    (sY : Y ⟶ Spec (.of k)) (hY : IsQuasiProjective sY) : IsProjectiveMorphism g := by
  obtain ⟨L, hL, hLa⟩ := exists_isAmple_of_isQuasiProjective sY
    (Stacks.Ample.unitModule (Spec (.of k)))
    (Stacks.Ample.isAmple_unitModule_of_isAffine _) hY
  exact isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mpr
    ⟨isHQuasiProjective_of_isQuasiProjective g L hLa (isQuasiProjective_of_isFinite g),
      inferInstance⟩

/-- Composition of quasi-projective morphisms into `Spec k`. -/
private theorem isQuasiProjective_comp_spec {X Y : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Spec (.of k)) (hf : IsQuasiProjective f) (hg : IsQuasiProjective g) :
    IsQuasiProjective (f ≫ g) :=
  isQuasiProjective_comp_of_exists_isAmple f g ⟨_, inferInstance,
    Stacks.Ample.isAmple_unitModule_of_isAffine _⟩ hf hg

/-- The source of a partial isomorphism onto an irreducible scheme is irreducible. -/
private theorem irreducibleSpace_of_partialIso {X Y : Scheme.{u}} [IrreducibleSpace Y]
    (e : X.PartialIso Y) : IrreducibleSpace X := by
  have hne : (e.target : Set Y).Nonempty := e.dense_target.nonempty
  have hT : IsIrreducible (e.target : Set Y) :=
    ⟨hne, (IrreducibleSpace.isIrreducible_univ Y).isPreirreducible.open_subset e.target.isOpen
      (Set.subset_univ _)⟩
  have : IrreducibleSpace (e.target : Set Y) := isIrreducible_iff_irreducibleSpace.mp hT
  have : IrreducibleSpace e.target.toScheme := ‹_›
  have : IrreducibleSpace e.source.toScheme :=
    Function.Surjective.irreducibleSpace e.iso.inv.continuous e.iso.inv.surjective
  have hS := (isIrreducible_iff_irreducibleSpace.mpr this).closure
  rw [e.dense_source.closure_eq] at hS
  exact (irreducibleSpace_def X).mpr hS

/-- A nonempty open subset of an irreducible scheme locally of finite type over a field has the
dimension of the scheme. -/
private theorem topologicalKrullDim_isOpen_eq {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] [IrreducibleSpace X] {V : Set X} (hV : IsOpen V) (hne : V.Nonempty) :
    topologicalKrullDim V = topologicalKrullDim X := by
  refine le_antisymm (topologicalKrullDim_subspace_le X V) ?_
  obtain ⟨x, hx⟩ := hne
  have h1 : topologicalKrullDim X ≤ topologicalKrullDimAt X x := by
    rw [topologicalKrullDimAt_eq_iSup_irreducibleComponents k X p x]
    have huniv : (Set.univ : Set X) ∈ irreducibleComponents X := by
      rw [irreducibleComponents_eq_singleton]; rfl
    refine le_trans (le_of_eq ?_) (le_iSup₂_of_le Set.univ ⟨huniv, Set.mem_univ x⟩ le_rfl)
    exact ((Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq).symm
  have h2 : topologicalKrullDimAt X x = topologicalKrullDimAt V ⟨x, hx⟩ :=
    hV.isOpenEmbedding_subtypeVal.topologicalKrullDimAt_eq ⟨x, hx⟩
  exact h1.trans (h2 ▸ topologicalKrullDimAt_le_topologicalKrullDim _)

/-- Two irreducible schemes locally of finite type over `k` related by a partial isomorphism
have the same dimension. -/
private theorem topologicalKrullDim_eq_of_partialIso {X X' : Scheme.{u}} (p : X ⟶ Spec (.of k))
    (p' : X' ⟶ Spec (.of k)) [LocallyOfFiniteType p] [LocallyOfFiniteType p']
    [IrreducibleSpace X] [IrreducibleSpace X'] (e : X.PartialIso X') :
    topologicalKrullDim X = topologicalKrullDim X' := by
  have hs := topologicalKrullDim_isOpen_eq p e.source.isOpen e.dense_source.nonempty
  have ht := topologicalKrullDim_isOpen_eq p' e.target.isOpen e.dense_target.nonempty
  rw [← hs, ← ht]
  exact (e.iso.hom.homeomorph).isHomeomorph.topologicalKrullDim_eq

/-- **Incomparability.** Over an integral ring map, two comparable primes with the same
contraction are equal. -/
private theorem eq_of_le_of_comap_eq_of_isIntegral {R S : Type*} [CommRing R]
    [CommRing S] (φ : R →+* S) (hφ : φ.IsIntegral) {P Q : Ideal S} [P.IsPrime] (hPQ : P ≤ Q)
    (h : P.comap φ = Q.comap φ) : P = Q := by
  letI := φ.toAlgebra
  haveI : Algebra.IsIntegral R S := ⟨hφ⟩
  by_contra hne
  exact (Ideal.IsIntegral.comap_lt_comap (R := R) (lt_of_le_of_ne hPQ hne)).ne h

/-- Incomparability on spectra: for an integral ring map `φ`, two points of `Spec S` related by
specialization and with the same image under `Spec φ` are equal. -/
private theorem eq_of_specializes_of_isIntegral_specMap {R S : CommRingCat} (φ : R ⟶ S)
    (hφ : φ.hom.IsIntegral) (p q : PrimeSpectrum S) (hpq : p ⤳ q)
    (hc : Spec.map φ p = Spec.map φ q) : p = q := by
  rw [← PrimeSpectrum.le_iff_specializes] at hpq
  exact PrimeSpectrum.ext (eq_of_le_of_comap_eq_of_isIntegral _ hφ hpq
    (congrArg PrimeSpectrum.asIdeal hc))

/-- Incomparability for an integral morphism of affine schemes. -/
private theorem eq_of_specializes_of_isIntegralHom_of_isAffine {X Z : Scheme} [IsAffine X]
    [IsAffine Z] (f : X ⟶ Z) [IsIntegralHom f] {t t' : X} (h : t ⤳ t') (he : f t = f t') :
    t = t' := by
  have hg : (f.appTop).hom.IsIntegral := f.isIntegral_app ⊤ (isAffineOpen_top Z)
  have hc : (Spec.map f.appTop) (X.isoSpec.hom t) = (Spec.map f.appTop) (X.isoSpec.hom t') := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Scheme.isoSpec_hom_naturality,
      Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, he]
  have heq := congrArg X.isoSpec.inv (eq_of_specializes_of_isIntegral_specMap _ hg _ _
    (h.map X.isoSpec.hom.continuous) hc)
  rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Iso.hom_inv_id] at heq

/-- **Incomparability.** The fibres of an integral morphism carry no nontrivial
specializations. -/
private theorem eq_of_specializes_of_isIntegralHom {X Z : Scheme} (f : X ⟶ Z) [IsIntegralHom f]
    {t t' : X} (h : t ⤳ t') (he : f t = f t') : t = t' := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hmem, -⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f t')) isOpen_univ
  have ht' : t' ∈ f ⁻¹ᵁ U := hmem
  have ht : t ∈ f ⁻¹ᵁ U := h.mem_open (f ⁻¹ᵁ U).isOpen ht'
  haveI : IsAffine U := hU
  haveI : IsAffine (f ⁻¹ᵁ U) := hU.preimage f
  let a : (f ⁻¹ᵁ U).toScheme := ⟨t, ht⟩
  let b : (f ⁻¹ᵁ U).toScheme := ⟨t', ht'⟩
  have hab : a ⤳ b := subtype_specializes_iff _ _ |>.2 h
  have hfab : (f ∣_ U) a = (f ∣_ U) b := Subtype.ext
    ((morphismRestrict_base_coe f U a).trans (he.trans (morphismRestrict_base_coe f U b).symm))
  exact congrArg Subtype.val (eq_of_specializes_of_isIntegralHom_of_isAffine (f ∣_ U) hab hfab)

/-- A morphism of irreducible schemes which becomes an open immersion after precomposing with an
open immersion from a nonempty scheme is birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion_comp {X Y V : Scheme.{u}}
    [IrreducibleSpace X] [IrreducibleSpace Y] [Nonempty V] (f : X ⟶ Y) (ψ : V ⟶ X)
    [IsOpenImmersion ψ] [IsOpenImmersion (ψ ≫ f)] : MMP.Mori.IsBirationalMorphism f := by
  obtain ⟨v⟩ := ‹Nonempty V›
  have hle : ψ.opensRange ≤ f ⁻¹ᵁ (ψ ≫ f).opensRange := by
    rintro _ ⟨w, rfl⟩
    exact ⟨w, rfl⟩
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE f ψ.opensRange (ψ ≫ f).opensRange
    ⟨ψ v, v, rfl⟩ ⟨(ψ ≫ f) v, v, rfl⟩ hle ?_
  have : f.resLE _ _ hle = ψ.isoOpensRange.inv ≫ (ψ ≫ f).isoOpensRange.hom := by
    rw [← cancel_epi ψ.isoOpensRange.hom, ← cancel_mono (ψ ≫ f).opensRange.ι]
    simp [Scheme.Hom.resLE_comp_ι]
  rw [this]
  infer_instance

/-- If a separated morphism `f` restricts to an open immersion on a dense open `W`, then `W` is
the whole preimage of its image. -/
private theorem preimage_opensRange_le {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f]
    (W : X.Opens) (hW : Dense (W : Set X)) [IsOpenImmersion (W.ι ≫ f)] :
    f ⁻¹ᵁ (W.ι ≫ f).opensRange ≤ W := by
  set T := (W.ι ≫ f).opensRange
  have hle : W ≤ f ⁻¹ᵁ T := fun x hx ↦ ⟨⟨x, hx⟩, rfl⟩
  let s : T.toScheme ⟶ (f ⁻¹ᵁ T).toScheme := (W.ι ≫ f).isoOpensRange.inv ≫ X.homOfLE hle
  have hsι : s ≫ (f ⁻¹ᵁ T).ι = (W.ι ≫ f).isoOpensRange.inv ≫ W.ι := by
    simp [s]
  have hs : s ≫ f ∣_ T = 𝟙 _ := by
    rw [← cancel_mono T.ι, Category.assoc, morphismRestrict_ι, reassoc_of% hsι]
    simp [T]
  have : IsClosedImmersion (s ≫ f ∣_ T) := by rw [hs]; infer_instance
  have : IsClosedImmersion s := IsClosedImmersion.of_comp s (f ∣_ T)
  have hr : Set.range s = (f ⁻¹ᵁ T).ι ⁻¹' (W : Set X) := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      change (s ≫ (f ⁻¹ᵁ T).ι) z ∈ W
      rw [hsι]
      exact ((W.ι ≫ f).isoOpensRange.inv z).2
    · intro hw
      refine ⟨(W.ι ≫ f).isoOpensRange.hom ⟨_, hw⟩, (f ⁻¹ᵁ T).ι.isOpenEmbedding.injective ?_⟩
      change (s ≫ (f ⁻¹ᵁ T).ι) _ = _
      rw [hsι]
      change ((W.ι ≫ f).isoOpensRange.hom ≫ (W.ι ≫ f).isoOpensRange.inv ≫ W.ι) _ = _
      rw [Iso.hom_inv_id_assoc]
      rfl
  have hcl : IsClosed (Set.range s) := s.isClosedEmbedding.isClosed_range
  have hd : Dense (Set.range s) := hr ▸ hW.preimage (f ⁻¹ᵁ T).ι.isOpenEmbedding.isOpenMap
  intro x hx
  have : (⟨x, hx⟩ : (f ⁻¹ᵁ T).toScheme) ∈ Set.range s := by
    rw [← hcl.closure_eq, hd.closure_eq]; trivial
  rw [hr] at this
  exact this

/-- The canonical map `U ⟶ S` into the normalization of `P` along `ψ ≫ W.ι` is an open immersion
when `ψ : U ⟶ W` is a closed immersion into an open `W ⊆ P`: normalization commutes with the
open base change `W ⟶ P`, and the normalization of a closed immersion is its source. -/
private theorem isOpenImmersion_toNormalization {U P : Scheme.{u}} (W : P.Opens)
    (ψ : U ⟶ W.toScheme) [IsClosedImmersion ψ] [QuasiCompact (ψ ≫ W.ι)]
    [QuasiSeparated (ψ ≫ W.ι)] : IsOpenImmersion (ψ ≫ W.ι).toNormalization := by
  set a := pullback.snd (ψ ≫ W.ι) W.ι
  have ha : pullback.fst (ψ ≫ W.ι) W.ι ≫ ψ = a := by
    rw [← cancel_mono W.ι, Category.assoc, pullback.condition]
  have : IsClosedImmersion a := by rw [← ha]; infer_instance
  have hfac : (ψ ≫ W.ι).toNormalization = inv (pullback.fst (ψ ≫ W.ι) W.ι) ≫
      a.toNormalization ≫ (ψ ≫ W.ι).normalizationPullback W.ι ≫ pullback.fst _ _ := by
    rw [Scheme.Hom.toNormalization_normalizationPullback_fst, IsIso.inv_hom_id_assoc]
  rw [hfac]
  infer_instance

variable {X₁ X₂ Y : Scheme.{u}} {f₁ : X₁ ⟶ Y} {f₂ : X₂ ⟶ Y}

/-- The graph `U ⟶ X₁ ×_Y X₂` is a closed immersion into the open `pr₁⁻¹ U` followed by its
inclusion. -/
private theorem exists_isClosedImmersion_graph [IsSeparated f₂] (U : X₁.Opens)
    (h : U.toScheme ⟶ X₂) (hh : h ≫ f₂ = U.ι ≫ f₁) :
    ∃ ψ : U.toScheme ⟶ (pullback.fst f₁ f₂ ⁻¹ᵁ U).toScheme, IsClosedImmersion ψ ∧
      ψ ≫ (pullback.fst f₁ f₂ ⁻¹ᵁ U).ι = pullback.lift U.ι h hh.symm := by
  set W := pullback.fst f₁ f₂ ⁻¹ᵁ U
  have hr : Set.range (pullback.lift U.ι h hh.symm) ⊆ Set.range W.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change (pullback.lift U.ι h hh.symm ≫ pullback.fst f₁ f₂) x ∈ U
    rw [pullback.lift_fst]
    exact x.2
  set ψ := IsOpenImmersion.lift W.ι _ hr
  have hψ : ψ ≫ W.ι = pullback.lift U.ι h hh.symm := IsOpenImmersion.lift_fac _ _ _
  refine ⟨ψ, ?_, hψ⟩
  have hid : ψ ≫ pullback.fst f₁ f₂ ∣_ U = 𝟙 _ := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, reassoc_of% hψ, Category.id_comp]
    exact pullback.lift_fst _ _ _
  have : IsClosedImmersion (ψ ≫ pullback.fst f₁ f₂ ∣_ U) := by rw [hid]; infer_instance
  exact IsClosedImmersion.of_comp ψ (pullback.fst f₁ f₂ ∣_ U)

/-- The canonical map `U ⟶ S` of the normalized graph is an open immersion. -/
private theorem isOpenImmersion_toNormalization_graph [IsSeparated f₂] (U : X₁.Opens)
    (h : U.toScheme ⟶ X₂) (hh : h ≫ f₂ = U.ι ≫ f₁)
    [QuasiCompact (pullback.lift U.ι h hh.symm)] [QuasiSeparated (pullback.lift U.ι h hh.symm)] :
    IsOpenImmersion (pullback.lift U.ι h hh.symm).toNormalization := by
  obtain ⟨ψ, hψ, e⟩ := exists_isClosedImmersion_graph U h hh
  revert ‹QuasiCompact (pullback.lift U.ι h hh.symm)›
    ‹QuasiSeparated (pullback.lift U.ι h hh.symm)›
  rw [← e]
  intro _ _
  exact isOpenImmersion_toNormalization _ ψ

/-- The first projection `g₁ : S ⟶ X₁` of the normalized graph is birational: over `U` it is
inverse to `U ⟶ S`. -/
private theorem isBirationalMorphism_g₁ [IsSeparated f₂] [IrreducibleSpace X₁]
    (U : X₁.Opens) [Nonempty U] (h : U.toScheme ⟶ X₂) (hh : h ≫ f₂ = U.ι ≫ f₁)
    [QuasiCompact (pullback.lift U.ι h hh.symm)] [QuasiSeparated (pullback.lift U.ι h hh.symm)]
    [IrreducibleSpace (pullback.lift U.ι h hh.symm).normalization] :
    MMP.Mori.IsBirationalMorphism
      ((pullback.lift U.ι h hh.symm).fromNormalization ≫ pullback.fst f₁ f₂) := by
  have := isOpenImmersion_toNormalization_graph U h hh
  have : IsOpenImmersion ((pullback.lift U.ι h hh.symm).toNormalization ≫
      (pullback.lift U.ι h hh.symm).fromNormalization ≫ pullback.fst f₁ f₂) := by
    rw [Scheme.Hom.toNormalization_fromNormalization_assoc, pullback.lift_fst]
    infer_instance
  exact isBirationalMorphism_of_isOpenImmersion_comp _
    (pullback.lift U.ι h hh.symm).toNormalization

/-- The second projection `g₂ : S ⟶ X₂` of the normalized graph is birational: on the open of
`U` where `f₁` and `f₂` are both open immersions, `U ⟶ S ⟶ X₂` is an open immersion. -/
private theorem isBirationalMorphism_g₂ [IsSeparated f₂] [IrreducibleSpace X₁]
    [IrreducibleSpace X₂] [IrreducibleSpace Y]
    (hb₁ : MMP.Mori.IsBirationalMorphism f₁) (hb₂ : MMP.Mori.IsBirationalMorphism f₂)
    (U : X₁.Opens) [Nonempty U] (h : U.toScheme ⟶ X₂) (hh : h ≫ f₂ = U.ι ≫ f₁)
    [QuasiCompact (pullback.lift U.ι h hh.symm)] [QuasiSeparated (pullback.lift U.ι h hh.symm)]
    [IrreducibleSpace (pullback.lift U.ι h hh.symm).normalization] :
    MMP.Mori.IsBirationalMorphism
      ((pullback.lift U.ι h hh.symm).fromNormalization ≫ pullback.snd f₁ f₂) := by
  have : Nonempty X₁ := ⟨(Classical.arbitrary U).1⟩
  obtain ⟨W₁, hW₁, _⟩ := hb₁.exists_isOpenImmersion
  have : Nonempty X₂ := ⟨h (Classical.arbitrary U)⟩
  obtain ⟨W₂, hW₂, _⟩ := hb₂.exists_isOpenImmersion
  set T₂ := (W₂.ι ≫ f₂).opensRange
  have hT₂ : f₂ ⁻¹ᵁ T₂ ≤ W₂ := preimage_opensRange_le f₂ W₂ (W₂.isOpen.dense hW₂)
  set O : X₁.Opens := U ⊓ (W₁ ⊓ f₁ ⁻¹ᵁ T₂)
  have hO : (O : Set X₁).Nonempty := by
    obtain ⟨y, hy₂, w, rfl⟩ := nonempty_preirreducible_inter T₂.isOpen
      (W₁.ι ≫ f₁).opensRange.isOpen ⟨_, ⟨hW₂.choose, hW₂.choose_spec⟩, rfl⟩
      ⟨_, ⟨hW₁.choose, hW₁.choose_spec⟩, rfl⟩
    exact nonempty_preirreducible_inter U.isOpen (W₁ ⊓ f₁ ⁻¹ᵁ T₂).isOpen
      ⟨_, (Classical.arbitrary U).2⟩ ⟨W₁.ι w, w.2, hy₂⟩
  set U' : U.toScheme.Opens := U.ι ⁻¹ᵁ O
  obtain ⟨x, hx⟩ := hO
  have : Nonempty U' := ⟨⟨⟨x, hx.1⟩, hx⟩⟩
  have hr₂ : Set.range (U'.ι ≫ h) ⊆ Set.range W₂.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    apply hT₂
    change ((U'.ι ≫ h) ≫ f₂) z ∈ T₂
    rw [Category.assoc, hh]
    exact z.2.2.2
  have hr₁ : Set.range (U'.ι ≫ U.ι) ⊆ Set.range W₁.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact z.2.2.1
  set m := IsOpenImmersion.lift W₁.ι _ hr₁
  have hm : m ≫ W₁.ι = U'.ι ≫ U.ι := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion m := by
    have : IsOpenImmersion (m ≫ W₁.ι) := by rw [hm]; infer_instance
    exact IsOpenImmersion.of_comp m W₁.ι
  set n := IsOpenImmersion.lift W₂.ι _ hr₂
  have hn : n ≫ W₂.ι = U'.ι ≫ h := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion n := by
    have : IsOpenImmersion (n ≫ W₂.ι ≫ f₂) := by
      rw [reassoc_of% hn, hh, ← reassoc_of% hm]
      infer_instance
    exact IsOpenImmersion.of_comp n (W₂.ι ≫ f₂)
  have := isOpenImmersion_toNormalization_graph U h hh
  have : IsOpenImmersion ((U'.ι ≫ (pullback.lift U.ι h hh.symm).toNormalization) ≫
      (pullback.lift U.ι h hh.symm).fromNormalization ≫ pullback.snd f₁ f₂) := by
    rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization_assoc, pullback.lift_snd,
      ← hn]
    infer_instance
  exact isBirationalMorphism_of_isOpenImmersion_comp _
    (U'.ι ≫ (pullback.lift U.ι h hh.symm).toNormalization)

/-- No proper curve of the normalized graph is contracted by both projections: its image in
`X₁ ×_Y X₂` would lie in a finite set, while `S ⟶ X₁ ×_Y X₂` is finite. -/
private theorem not_isContracted_g₁_and_g₂ {sY : Y ⟶ Spec (.of k)} [IsSeparated sY]
    [IsProper f₁] (U : X₁.Opens) (h : U.toScheme ⟶ X₂) (hh : h ≫ f₂ = U.ι ≫ f₁)
    [QuasiCompact (pullback.lift U.ι h hh.symm)] [QuasiSeparated (pullback.lift U.ι h hh.symm)]
    [IsProper ((pullback.lift U.ι h hh.symm).fromNormalization ≫ pullback.fst f₁ f₂)]
    (C : MMP.Mori.ProperCurve ((pullback.lift U.ι h hh.symm).fromNormalization ≫
      pullback.fst f₁ f₂ ≫ f₁ ≫ sY)) :
    ¬ (IsContractedProjectiveCurve _
        ((pullback.lift U.ι h hh.symm).fromNormalization ≫ pullback.fst f₁ f₂) C ∧
      IsContractedProjectiveCurve _
        ((pullback.lift U.ι h hh.symm).fromNormalization ≫ pullback.snd f₁ f₂) C) := by
  rintro ⟨⟨-, h₁⟩, ⟨-, h₂⟩⟩
  let ν := (pullback.lift U.ι h hh.symm).fromNormalization
  let g₁ := ν ≫ pullback.fst f₁ f₂
  let c := C.point
  -- the curve has a point other than its generic point
  obtain ⟨z, hz, hzc⟩ : ∃ z ∈ closure ({c} : Set _), z ≠ c := by
    by_contra! H
    have hmem : ∀ a : C.scheme, C.ι a ∈ closure ({c} : Set _) := fun a ↦ by
      have : C.ι a ∈ Set.range C.ι := ⟨a, rfl⟩
      rwa [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
    have : Subsingleton C.scheme := ⟨fun a b ↦ C.ι.isClosedEmbedding.injective (by
      rw [H _ (hmem a), H _ (hmem b)])⟩
    have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
    rw [C.dim_eq] at h0
    exact absurd h0 (by decide)
  have hcz : c ⤳ z := specializes_iff_mem_closure.mpr hz
  -- `g₁` contracts the curve to a closed point `x₁`
  have hx₁ : IsClosed {g₁ c} := by
    have : g₁ '' closure {c} = {g₁ c} :=
      Set.eq_singleton_iff_unique_mem.mpr ⟨⟨c, subset_closure rfl, rfl⟩,
        by rintro _ ⟨x, hx, rfl⟩; exact h₁ x hx⟩
    rw [← this]
    exact g₁.isClosedMap _ isClosed_closure
  set e := X₁.fromSpecResidueField (g₁ c)
  have : IsClosedImmersion e := isClosed_singleton_iff_isClosedImmersion.mp hx₁
  have : IsAffineHom (e ≫ f₁) := IsAffineHom.of_comp _ sY
  have : IsIntegralHom (e ≫ f₁) := IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr
    ⟨inferInstance, inferInstance⟩
  set s := pullback.snd e (pullback.fst f₁ f₂)
  have : IsIntegralHom (s ≫ pullback.snd f₁ f₂) := by
    rw [← pullbackRightPullbackFstIso_hom_snd]
    infer_instance
  set o : Spec (X₁.residueField (g₁ c)) := IsLocalRing.closedPoint _
  have ho : e o = g₁ c := Scheme.fromSpecResidueField_apply _ _
  obtain ⟨a, -, ha⟩ := Scheme.Pullback.exists_preimage_pullback (f := e)
    (g := pullback.fst f₁ f₂) o (ν c) ho
  obtain ⟨b, -, hb⟩ := Scheme.Pullback.exists_preimage_pullback (f := e)
    (g := pullback.fst f₁ f₂) o (ν z) (ho.trans (h₁ z hz).symm)
  have hab : a ⤳ b := by
    rw [← s.isClosedEmbedding.isInducing.specializes_iff, ha, hb]
    exact hcz.map ν.continuous
  have hab' := eq_of_specializes_of_isIntegralHom (s ≫ pullback.snd f₁ f₂) hab (by
    change pullback.snd f₁ f₂ (s a) = pullback.snd f₁ f₂ (s b)
    rw [ha, hb]
    exact (h₂ z hz).symm)
  have hνcz : ν c = ν z := by rw [← ha, ← hb, hab']
  exact hzc (eq_of_specializes_of_isIntegralHom ν hcz hνcz).symm

end MMP.Proofs.lem_kr2a_graph_normalization_two_resolutions

namespace MMP.Resolution.IsProjectiveSurfaceResolution

open MMP.Proofs.lem_kr2a_graph_normalization_two_resolutions in
/-- **The normalized graph of two resolutions** (Kollár, proof of Thm. 2.16). Let
`f₁ : X₁ ⟶ Y`, `f₂ : X₂ ⟶ Y` be resolutions of a quasi-projective surface `Y` over `k`, and
let `h : U ⟶ X₂`, on a nonempty open `U ⊆ X₁` with `h ≫ f₂ = U.ι ≫ f₁`, represent the birational
map `f₂⁻¹ ∘ f₁`. Let `S` be the normalization of the closure of the graph of `h` in
`X₁ ×_Y X₂` (the relative normalization of `X₁ ×_Y X₂` in `U` along `(U.ι, h)`), with
projections `g₁ : S ⟶ X₁`, `g₂ : S ⟶ X₂`. Then `S` is a normal quasi-projective surface over
`k`, each `gᵢ` is projective and birational, `f₁ ∘ g₁ = f₂ ∘ g₂`, and no curve of `S` is both
`g₁`-exceptional and `g₂`-exceptional. -/
@[mmp "lem_kr2a_graph_normalization_two_resolutions"]
public theorem graphNormalization_spec {k : Type u} [Field k] {X₁ X₂ Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} (hY : IsQuasiProjectiveVariety k sY)
    {f₁ : X₁ ⟶ Y} {f₂ : X₂ ⟶ Y}
    (hf₁ : IsProjectiveSurfaceResolution sY f₁) (hf₂ : IsProjectiveSurfaceResolution sY f₂)
    (U : X₁.Opens) (hU : (U : Set X₁).Nonempty) (h : U.toScheme ⟶ X₂)
    (hh : h ≫ f₂ = U.ι ≫ f₁)
    [QuasiCompact (pullback.lift U.ι h hh.symm)] [QuasiSeparated (pullback.lift U.ι h hh.symm)] :
    let φ := pullback.lift U.ι h hh.symm
    let g₁ : φ.normalization ⟶ X₁ := φ.fromNormalization ≫ pullback.fst f₁ f₂
    let g₂ : φ.normalization ⟶ X₂ := φ.fromNormalization ≫ pullback.snd f₁ f₂
    let sS : φ.normalization ⟶ Spec (.of k) := g₁ ≫ f₁ ≫ sY
    IsNormal φ.normalization ∧ IsQuasiProjectiveVariety k sS ∧
      topologicalKrullDim φ.normalization = 2 ∧
      (IsProjectiveMorphism g₁ ∧ MMP.Mori.IsBirationalMorphism g₁) ∧
      (IsProjectiveMorphism g₂ ∧ MMP.Mori.IsBirationalMorphism g₂) ∧
      g₁ ≫ f₁ = g₂ ≫ f₂ ∧
      ∀ C : MMP.Mori.ProperCurve sS,
        ¬ (IsContractedProjectiveCurve sS g₁ C ∧ IsContractedProjectiveCurve sS g₂ C) := by
  intro φ g₁ g₂ sS
  have := hY.toIsVariety
  have hp₁ := hf₁.isProjectiveMorphism
  have hp₂ := hf₂.isProjectiveMorphism
  have : IsProper f₁ := isProper_of_isProjectiveMorphism f₁ hp₁
  have : IsProper f₂ := isProper_of_isProjectiveMorphism f₂ hp₂
  have hpf := isProjectiveMorphism_pullback_fst f₁ hp₂
  have : IsProper (pullback.fst f₁ f₂) := isProper_of_isProjectiveMorphism _ hpf
  obtain ⟨_, _⟩ :=
    MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hf₁.isSmoothScheme
  have : IsFinite φ.fromNormalization :=
    isFinite_fromNormalization_of_locallyOfFiniteType_over_field k
      (pullback.fst f₁ f₂ ≫ f₁ ≫ sY) (U.ι ≫ f₁ ≫ sY) φ (by simp only [φ, pullback.lift_fst_assoc])
  have hqP : IsQuasiProjective (pullback.fst f₁ f₂ ≫ f₁ ≫ sY) :=
    isQuasiProjective_comp_spec _ _
      (isQuasiProjective_of_isHQuasiProjective _ hpf.isHQuasiProjective)
      (isQuasiProjective_comp_spec _ _
        (isQuasiProjective_of_isHQuasiProjective _ hp₁.isHQuasiProjective)
        hY.isQuasiProjective)
  have hν := isProjectiveMorphism_of_isFinite φ.fromNormalization _ hqP
  have hcomm : g₁ ≫ f₁ = g₂ ≫ f₂ := by
    simp only [g₁, g₂, Category.assoc, pullback.condition]
  have : IsIntegral Y := hY.toIsIntegral
  have : IrreducibleSpace X₁ := by
    obtain ⟨e, -⟩ := hf₁.isBirationalMorphism
    exact irreducibleSpace_of_partialIso e
  have : IsIntegral X₁ := isIntegral_of_irreducibleSpace_of_isReduced X₁
  have : Nonempty U := hU.to_subtype
  have : CompactSpace X₁ := (quasiCompact_iff_compactSpace (f₁ ≫ sY)).mp inferInstance
  have : IsNoetherian X₁ := ⟨⟩
  have hNS : IsNormal φ.normalization :=
    isNormal_normalization φ fun V _ ↦
      @TopologicalSpace.NoetherianSpace.finite_irreducibleComponents _ _
        (@TopologicalSpace.NoetherianSpace.set _ _
          (TopologicalSpace.NoetherianSpace.set (U : Set X₁)) (V : Set U.toScheme))
  have hqS : IsQuasiProjectiveVariety k sS := by
    have hs : sS = φ.fromNormalization ≫ pullback.fst f₁ f₂ ≫ f₁ ≫ sY := by
      simp only [sS, g₁, Category.assoc]
    have : IsVariety k sS := by rw [hs]; exact ⟨⟩
    refine (isQuasiProjectiveVariety_iff k sS).mpr ⟨this, ?_⟩
    rw [hs]
    exact isQuasiProjective_comp_spec _ _ (isQuasiProjective_of_isFinite _) hqP
  have : IrreducibleSpace X₂ := by
    obtain ⟨e, -⟩ := hf₂.isBirationalMorphism
    exact irreducibleSpace_of_partialIso e
  have hb₁ := isBirationalMorphism_g₁ U h hh
  have : IsProper g₁ := isProper_of_isProjectiveMorphism _ (hν.comp hpf)
  refine ⟨hNS, hqS, ?_, ⟨hν.comp hpf, hb₁⟩,
    ⟨hν.comp (hp₁.baseChange f₂),
      isBirationalMorphism_g₂ hf₁.isBirationalMorphism hf₂.isBirationalMorphism U h hh⟩, hcomm,
    fun C ↦ not_isContracted_g₁_and_g₂ U h hh C⟩
  have : LocallyOfFiniteType sS := hqS.toLocallyOfFiniteType
  obtain ⟨e, -⟩ := hb₁
  rw [topologicalKrullDim_eq_of_partialIso sS (f₁ ≫ sY) e, hf₁.dim_source_eq]

end MMP.Resolution.IsProjectiveSurfaceResolution

end

/-!
### The Step-3.`r` blow-up of monomial data

Let `(X, E, A)` be monomial data over a field `k`, `m ≥ 1`, `r ≥ 1` with `m_r(E, A) ≥ m`, and
let `π : X' = B_ZX → X` be the Step-3.`r` blow-up, `Z` the union of the pieces of `E^{J_*}` of
maximal weight `σ_{J_*} = m_r(E, A)`. Then `π` is a smooth blow-up of the marked triple
`(X, I_{E,A}, m, E)`, the order of `I_{E,A} = 𝒪_X(-A)` along `Z` is exactly `m_r(E, A)`, and
the birational transform `π⁻¹_*(I_{E,A}, m) = 𝒪(mF)·π^*𝒪_X(-A)` is the monomial ideal of the new
data `(X', E', A')`, `A' = π^*A - mF`, which are again monomial data. Explicitly, `A'` keeps the
coefficient `a_{ik}` on the birational transform of every `E^{ik}` not contained in `Z`, and has
coefficient `m_r(E, A) - m` along every prime divisor lying over `Z`: for `r ≥ 2` these are the
components of the exceptional divisor `F`, the last member of `E'`; for `r = 1` they are the
transforms of the components of `Z`, whose coefficient `m_1(E, A)` is lowered by `m`.

### Main results

* `MMP.Resolution.MonomialData.step_spec`: the Step-3.`r` blow-up is a smooth blow-up of
  `(X, I_{E,A}, m, E)` with `ord_Z I_{E,A} = m_r(E, A)`, its birational transform is `I_{E',A'}`,
  `(X', E', A')` are monomial data, and the coefficients of `A'` are as above.

### Implementation notes

A prime divisor `D'` of `X'` is the birational transform of the prime divisor `D` of `X` when
`π` maps the generic point of `D'` to that of `D`. For `r = 1` the coefficient of a component
`D ⊆ Z` is `m_1(E, A)` (the weight of a piece of `E^{j}` is the coefficient of its component),
so "lowered by `m`" and "equal to `m_1(E, A) - m`" are the same statement; both are recorded.

### References

* [J. Kollár, *Lectures on resolution of singularities*, 3.111, Steps 3.1, 3.2, 3.`r`]
-/

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Resolution

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Proofs.lem_kr3e_monomial_stratum_blowup

variable {X : Scheme.{u}} (C : MonomialData X)

/-- The centre `Z` lies in the stratum `E^{J_*}`. -/
private theorem stepCenter_support_subset_stratum (r : ℕ) :
    ((C.stepCenter r).support : Set X) ⊆ C.stratum (C.stepIndex r) := by
  rw [MonomialData.stepCenter, Scheme.IdealSheafData.coe_support_vanishingIdeal,
    Closeds.coe_closure]
  refine closure_minimal ?_ (isClosed_biInter fun j _ => (C.E.E j).support.isClosed)
  rintro y ⟨P, ⟨-, ⟨x0, -, rfl⟩, -⟩, hy⟩
  exact connectedComponentIn_subset _ _ hy

/-- If the centre `Z` is nonempty, then `|J_*| = r`. -/
private theorem card_stepIndex_of_mem_stepCenter {r : ℕ} {x : X}
    (hx : x ∈ ((C.stepCenter r).support : Set X)) : (C.stepIndex r).card = r := by
  rw [MonomialData.stepCenter, Scheme.IdealSheafData.coe_support_vanishingIdeal,
    Closeds.coe_closure] at hx
  obtain ⟨P, ⟨hP, -⟩, -⟩ := Set.nonempty_sUnion.1 (closure_nonempty_iff.1 ⟨x, hx⟩)
  exact hP

/-- Every irreducible component of `Z` has codimension `≥ 1`: at its generic point `η` some
member `E^j` passes, so a regular system of parameters at `η` is nonempty and the generic point of
`Spec 𝒪_{X,η}` gives a strictly larger irreducible closed set. -/
private theorem hasComponentsOfPositiveCodim_stepCenter (hC : C.IsMonomialData) {r : ℕ}
    (hr : 1 ≤ r) : HasComponentsOfPositiveCodim ((C.stepCenter r).support : Set X) := by
  obtain ⟨-, hlft, -, hE, -, -⟩ := id hC
  haveI := hlft
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian C.sX
  intro W hW
  obtain ⟨η, hηZ, rfl⟩ :=
    Aux.exists_eq_closure_of_mem_componentsOf (C.stepCenter r).support.isClosed hW
  obtain ⟨a, ha⟩ := Finset.card_pos.1
    ((card_stepIndex_of_mem_stepCenter C hηZ).symm ▸ hr : 0 < (C.stepIndex r).card)
  have hηa : η ∈ ((C.E.E a).support : Set X) :=
    Set.mem_iInter₂.1 (stepCenter_support_subset_stratum C r hηZ) a ha
  obtain ⟨n, z, c, hz, -, -⟩ := hE.2.2 η
  have := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk η)
  let i := c ⟨a, hηa⟩
  let q₀ : PrimeSpectrum (X.presheaf.stalk η) := ⟨⊥, Ideal.isPrime_bot⟩
  have hlt : q₀.asIdeal < (IsLocalRing.closedPoint (X.presheaf.stalk η)).asIdeal := by
    refine bot_lt_iff_ne_bot.2 fun h => ?_
    have hmem : z i ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk η) := by
      rw [← hz.1]; exact Ideal.subset_span ⟨i, rfl⟩
    rw [show (IsLocalRing.closedPoint (X.presheaf.stalk η)).asIdeal =
      IsLocalRing.maximalIdeal _ from rfl] at h
    rw [h] at hmem
    exact ne_zero_of_isRegularSystemOfParameters hz i ((Submodule.mem_bot _).1 hmem)
  let C₀ : IrreducibleCloseds X :=
    ⟨closure {X.fromSpecStalk η q₀}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hl : irreducibleClosure hW.1.1 < C₀ := by
    change closure (closure {η}) ⊂ _
    rw [closure_closure]
    have h := closure_fromSpecStalk_ssubset (x := η) hlt
    rwa [Scheme.fromSpecStalk_closedPoint] at h
  have e := Order.coheight_add_one_le hl
  unfold codimension
  calc (1 : ℕ∞) = 0 + 1 := by norm_num
    _ ≤ Order.coheight C₀ + 1 := by gcongr; exact bot_le
    _ ≤ _ := e

/-- The union of the max pieces of `E^J` is closed: each piece is a union of irreducible
components of `E^J`, of which there are finitely many. -/
private theorem isClosed_sUnion_isMaxPiece (hC : C.IsMonomialData) (r : ℕ)
    (J : Finset (Fin C.E.s)) : IsClosed (⋃₀ {P | C.IsMaxPiece r J P}) := by
  obtain ⟨-, hlft, hqc, -, -, -⟩ := id hC
  haveI := hlft
  haveI := hqc
  haveI : NoetherianSpace X := Aux.noetherianSpace_of_finiteType C.sX
  have hS : IsClosed (C.stratum J) := isClosed_biInter fun j _ => (C.E.E j).support.isClosed
  obtain ⟨hfin, hcov⟩ := Aux.finite_and_cover_componentsOf hS
  have heq : ⋃₀ {P | C.IsMaxPiece r J P} =
      ⋃₀ {W | W ∈ componentsOf (C.stratum J) ∧ ∃ P, C.IsMaxPiece r J P ∧ W ⊆ P} := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro y ⟨P, hP, hy⟩
      obtain ⟨x0, -, rfl⟩ := hP.2.1
      obtain ⟨W, hW, hyW⟩ := Set.mem_sUnion.1 (hcov (connectedComponentIn_subset _ _ hy))
      refine ⟨W, ⟨hW, _, hP, ?_⟩, hyW⟩
      rw [connectedComponentIn_eq hy]
      exact (IsIrreducible.isConnected hW.1.1).isPreconnected.subset_connectedComponentIn hyW hW.1.2
    · rintro y ⟨W, ⟨-, P, hP, hWP⟩, hyW⟩
      exact ⟨P, hP, hWP hyW⟩
  rw [heq]
  refine (hfin.subset fun W hW => hW.1).isClosed_sUnion fun W hW => ?_
  have hW := hW.1
  rw [← closure_subset_iff_isClosed]
  exact hW.2 ⟨hW.1.1.closure, closure_minimal hW.1.2 hS⟩ subset_closure

/-- `Z` is the union of the max pieces of `E^{J_*}`. -/
private theorem coe_support_stepCenter (hC : C.IsMonomialData) (r : ℕ) :
    ((C.stepCenter r).support : Set X) = ⋃₀ {P | C.IsMaxPiece r (C.stepIndex r) P} := by
  rw [MonomialData.stepCenter, Scheme.IdealSheafData.coe_support_vanishingIdeal,
    Closeds.coe_closure, (isClosed_sUnion_isMaxPiece C hC r _).closure_eq]

/-- A point of `E^{J_*}` specializing to a point of `Z` lies on `Z`: its closure is connected and
meets the piece through that point. -/
private theorem mem_stepCenter_of_specializes (hC : C.IsMonomialData) (r : ℕ) {x y : X}
    (hx : x ∈ ((C.stepCenter r).support : Set X)) (hy : y ∈ C.stratum (C.stepIndex r))
    (hyx : y ⤳ x) : y ∈ ((C.stepCenter r).support : Set X) := by
  rw [coe_support_stepCenter C hC] at hx ⊢
  obtain ⟨P, hP, hxP⟩ := hx
  refine ⟨P, hP, ?_⟩
  obtain ⟨x0, -, rfl⟩ := hP.2.1
  have hS : IsClosed (C.stratum (C.stepIndex r)) :=
    isClosed_biInter fun j _ => (C.E.E j).support.isClosed
  rw [connectedComponentIn_eq hxP]
  exact (IsIrreducible.isConnected isIrreducible_singleton.closure).isPreconnected
    |>.subset_connectedComponentIn (specializes_iff_mem_closure.1 hyx)
      (closure_minimal (Set.singleton_subset_iff.2 hy) hS)
    (subset_closure rfl)

/-- If the inverse image of a closed set `T` in `Spec 𝒪_{Y,y}` is the zero locus of a prime `P`,
then the stalk at `y` of the reduced ideal of `T` is `P`. -/
private theorem stalk_vanishingIdeal_eq_of_isPrime {Y : Scheme.{u}} (T : Closeds Y) (y : Y)
    {P : Ideal (Y.presheaf.stalk y)} (hP : P.IsPrime)
    (hT : ∀ p : PrimeSpectrum (Y.presheaf.stalk y),
      Y.fromSpecStalk y p ∈ (T : Set Y) ↔ P ≤ p.asIdeal) :
    IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal T) y = P := by
  set K := IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal T) y
  have hzl : PrimeSpectrum.zeroLocus (K : Set (Y.presheaf.stalk y)) =
      PrimeSpectrum.zeroLocus (P : Set (Y.presheaf.stalk y)) := by
    rw [← preimage_fromSpecStalk_support, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    ext (p : PrimeSpectrum (Y.presheaf.stalk y))
    exact hT p
  calc K = K.radical := (isRadical_stalk_vanishingIdeal T y).radical.symm
    _ = P.radical := by
      rw [← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical,
        ← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, hzl]
    _ = P := hP.radical

/-- In coordinates `z` at `x ∈ Z` in which the members of `E` through `x` are `(z_{c(j)})`, the
stalk of `Z` at `x` is spanned by the coordinates of the members in `J_*`: near `x`, `Z` is the
stratum `E^{J_*}`, whose inverse image in `Spec 𝒪_{X,x}` is the zero locus of that prime. -/
private theorem stalk_stepCenter_eq_span (hC : C.IsMonomialData) (r : ℕ) {x : X}
    (hx : x ∈ ((C.stepCenter r).support : Set X)) {n : ℕ} {z : Fin n → X.presheaf.stalk x}
    {c : {j // x ∈ ((C.E.E j).support : Set X)} → Fin n}
    (hz : MMP.Mori.IsRegularSystemOfParameters z)
    (hst : ∀ j, IdealSheafData.stalk (C.E.E j.1) x = Ideal.span {z (c j)}) {J : Finset (Fin n)}
    (hJ : ∀ i, i ∈ J ↔ ∃ t, t.1 ∈ C.stepIndex r ∧ c t = i) :
    IdealSheafData.stalk (C.stepCenter r) x = Ideal.span (z '' (J : Set (Fin n))) := by
  haveI := hC.2.1
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian C.sX
  have hxS := stepCenter_support_subset_stratum C r hx
  refine stalk_vanishingIdeal_eq_of_isPrime _ x
    (span_image_isPrime_of_isRegularSystemOfParameters hz J) fun p => ?_
  rw [Ideal.span_le]
  have hmem : ∀ j (hj : x ∈ ((C.E.E j).support : Set X)),
      (X.fromSpecStalk x p ∈ ((C.E.E j).support : Set X) ↔ z (c ⟨j, hj⟩) ∈ p.asIdeal) := by
    intro j hj
    rw [fromSpecStalk_mem_support_iff_stalk_le, hst ⟨j, hj⟩, Ideal.span_le,
      Set.singleton_subset_iff]
    rfl
  change X.fromSpecStalk x p ∈ ((C.stepCenter r).support : Set X) ↔ _
  constructor
  · rintro hp _ ⟨i, hi, rfl⟩
    obtain ⟨t, ht, rfl⟩ := (hJ i).1 hi
    exact (hmem t.1 t.2).1
      (Set.mem_iInter₂.1 (stepCenter_support_subset_stratum C r hp) t.1 ht)
  · intro hp
    refine mem_stepCenter_of_specializes C hC r hx (Set.mem_iInter₂.2 fun j hj => ?_)
      (fromSpecStalk_specializes_self x p)
    have hxj : x ∈ ((C.E.E j).support : Set X) := Set.mem_iInter₂.1 hxS j hj
    exact (hmem j hxj).2 (hp ⟨c ⟨j, hxj⟩, (hJ _).2 ⟨⟨j, hxj⟩, hj, rfl⟩, rfl⟩)

/-- `Z` has simple normal crossings with `E`: near `x ∈ Z`, `Z = E^{J_*}` and the members through
`x` are coordinate hyperplanes of one regular system of parameters. -/
private theorem hasSNCWith_stepCenter (hC : C.IsMonomialData) (r : ℕ) :
    HasSNCWith C.E.E (C.stepCenter r) := by
  classical
  intro x hx
  obtain ⟨n, z, c, hz, hst, hc⟩ := hC.2.2.2.1.2.2 x
  exact ⟨n, z, c, (Finset.univ.filter fun t => t.1 ∈ C.stepIndex r).image c, hz, hst, hc,
    stalk_stepCenter_eq_span C hC r hx hz hst fun i => by simp⟩

section RegularLocal

open IsLocalRing

/-- In a regular local ring, the monomial `x^e` in a minimal generating list `x` of `𝔪` does not
lie in `𝔪^(|e| + 1)`: its class in `𝔪^|e|/𝔪^(|e|+1)` is the image of the monomial `X^e` under the
isomorphism `κ[X_1, …, X_d] ≅ Gr_𝔪(R)`. -/
private theorem prod_pow_notMem_of_ofList {R : Type*} [CommRing R] [IsRegularLocalRing R]
    (xs : List R) (hxs : Ideal.ofList xs = maximalIdeal R)
    (hmin : xs.length = (maximalIdeal R).spanFinrank) (e : Fin xs.length →₀ ℕ) :
    ∏ i, xs[i] ^ e i ∉ maximalIdeal R ^ (∑ i, e i + 1) := by
  intro hmem
  have hx : ∀ i : Fin xs.length, xs[i] ∈ maximalIdeal R := fun i => by
    rw [← hxs]; exact Ideal.subset_span (List.getElem_mem _)
  have hinj :=
    (IsRegularLocalRing.gradedRing_maximalIdeal_isPolynomialAlgebra xs hxs hmin hx).1.1
  have hmem' : (1 : R) * ∏ i, xs[i] ^ e i ∈ maximalIdeal R ^ (∑ i, e i) := by
    rw [one_mul]
    exact AssociatedGraded.prod_mem_pow_sum _ e (fun i => xs[i] ^ e i)
      (fun i => Ideal.pow_mem_pow (hx i) _) Finset.univ
  have h0 := AssociatedGraded.polyGradedHom_monomial (maximalIdeal R)
    (fun i : Fin xs.length => xs[i]) hx e 1 rfl hmem'
  have hz : AssociatedGraded.classOfPow (maximalIdeal R) (∑ i, e i)
      ⟨(1 : R) * ∏ i, xs[i] ^ e i, hmem'⟩ = 0 := by
    change DFinsupp.single _ _ = 0
    rw [DFinsupp.single_eq_zero]
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    change _ ∈ AssociatedGraded.power (M := R) (maximalIdeal R) (∑ i, e i + 1)
    rw [AssociatedGraded.ring_power_eq]
    simpa using hmem
  rw [hz, ← map_zero (AssociatedGraded.polyGradedHom (maximalIdeal R)
    (fun i : Fin xs.length => xs[i]) hx)] at h0
  have h1 := congrArg (·.coeff e) (hinj h0)
  rw [MvPolynomial.coeff_monomial, if_pos rfl, MvPolynomial.coeff_zero, Finsupp.coe_zero,
    Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem] at h1
  exact (maximalIdeal.isMaximal R).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)

/-- In a Noetherian local ring with a regular system of parameters `z`, the monomial `z^e` does
not lie in `𝔪^(|e| + 1)`. -/
private theorem prod_pow_notMem_of_isRegularSystemOfParameters {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] {n : ℕ} {z : Fin n → R}
    (hz : MMP.Mori.IsRegularSystemOfParameters z) (e : Fin n → ℕ) :
    ∏ i, z i ^ e i ∉ maximalIdeal R ^ (∑ i, e i + 1) := by
  haveI := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz
  have hlen : (List.ofFn z).length = n := List.length_ofFn
  have hxs : Ideal.ofList (List.ofFn z) = maximalIdeal R := by
    rw [← hz.1, Ideal.ofList]
    congr 1
    ext r; simp [List.mem_ofFn]
  have hmin : (List.ofFn z).length = (maximalIdeal R).spanFinrank := by
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
    rw [hz.2] at h
    rw [hlen]; exact_mod_cast h.symm
  have := prod_pow_notMem_of_ofList (List.ofFn z) hxs hmin
    (Finsupp.equivFunOnFinite.symm fun i => e (Fin.cast hlen i))
  simp only [Finsupp.coe_equivFunOnFinite_symm, List.getElem_ofFn] at this
  have hp : ∏ i : Fin (List.ofFn z).length, (List.ofFn z)[i] ^ e (Fin.cast hlen i) =
      ∏ i, z i ^ e i := by
    rw [← Fin.prod_congr' (fun i => z i ^ e i) hlen]
    simp [Fin.cast]
  have hsum : ∑ i : Fin (List.ofFn z).length, e (Fin.cast hlen i) = ∑ i, e i :=
    Fin.sum_congr' e hlen
  rwa [hp, hsum] at this

/-- The order is antitone in the ideal. -/
private theorem idealOrder_antitone {R : Type*} [CommRing R] [IsLocalRing R] {I J : Ideal R}
    (h : I ≤ J) : idealOrder J ≤ idealOrder I :=
  iSup₂_le fun j hj =>
    le_iSup₂_of_le (f := fun (j : ℕ) (_ : I ≤ maximalIdeal R ^ j) => (j : ℕ∞)) j (h.trans hj)
      le_rfl

/-- An element outside `𝔪^(d+1)` generates an ideal of order at most `d`. -/
private theorem idealOrder_span_singleton_le {R : Type*} [CommRing R] [IsLocalRing R] {f : R}
    {d : ℕ} (hf : f ∉ maximalIdeal R ^ (d + 1)) : idealOrder (Ideal.span {f}) ≤ d :=
  iSup₂_le fun j hj => by
    by_contra hlt
    have : d + 1 ≤ j := by exact_mod_cast Order.add_one_le_of_lt (not_le.1 hlt)
    exact hf (Ideal.pow_le_pow_right this ((Ideal.span_singleton_le_iff_mem _).1 hj))

end RegularLocal

/-- An ideal sheaf whose support contains a prime divisor `D` is contained in the ideal of `D`. -/
private theorem le_idealSheaf_of_support_subset {X : Scheme.{u}} (I : X.IdealSheafData)
    (D : AlgebraicGeometry.PrimeDivisor X) (h : (D.support : Set X) ⊆ I.support) :
    I ≤ D.idealSheaf := by
  haveI := D.integral
  have hD : Scheme.IdealSheafData.vanishingIdeal D.idealSheaf.support = D.idealSheaf := by
    have h' : Closeds.closure (D.idealSheaf.subschemeι.base ''
        ((⊤ : Closeds D.idealSheaf.subscheme) : Set D.idealSheaf.subscheme)) =
        D.idealSheaf.support := by
      apply SetLike.coe_injective
      simp only [Closeds.coe_closure, Closeds.coe_top, Set.image_univ]
      rw [show Set.range D.idealSheaf.subschemeι.base = (D.idealSheaf.support : Set X) from
        D.idealSheaf.range_subschemeι]
      exact D.idealSheaf.support.isClosed.closure_eq
    rw [← h', ← Scheme.IdealSheafData.map_vanishingIdeal,
      Scheme.IdealSheafData.vanishingIdeal_top, Scheme.nilradical_eq_bot,
      Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι]
  rw [← hD]
  exact Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.1 h

/-- An irreducible component of `D` lies in `D`. -/
private theorem subset_of_mem_componentsOf {T : Type*} [TopologicalSpace T] {D W : Set T}
    (h : W ∈ componentsOf D) : W ⊆ D := by
  simp only [componentsOf, Set.mem_setOf_eq] at h
  exact h.prop.2

open Classical in
/-- The prime divisors through `x` with nonzero coefficient in `A`. -/
private noncomputable def throughDivisors {X : Scheme.{u}} (C : MonomialData X)
    (hfin : (Function.support C.A).Finite) (x : X) : Finset (AlgebraicGeometry.PrimeDivisor X) :=
  hfin.toFinset.filter fun D => x ∈ (D.support : Set X)

private theorem mem_throughDivisors {X : Scheme.{u}} {C : MonomialData X}
    {hfin : (Function.support C.A).Finite} {x : X} {D : AlgebraicGeometry.PrimeDivisor X} :
    D ∈ throughDivisors C hfin x ↔ C.A D ≠ 0 ∧ x ∈ (D.support : Set X) := by
  simp [throughDivisors]

/-- The stalk of `𝒪_X(-A)` at `x` is `∏_{D ∋ x} (𝒪_X(-D))_x ^ a_D`. -/
private theorem stalk_monomialIdeal_eq_prod {X : Scheme.{u}} (C : MonomialData X)
    (hfin : (Function.support C.A).Finite) (x : X) :
    IdealSheafData.stalk C.monomialIdeal x =
      ∏ D ∈ throughDivisors C hfin x, IdealSheafData.stalk D.idealSheaf x ^ C.A D := by
  classical
  unfold MonomialData.monomialIdeal divisorIdeal
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := hfin.toFinset) fun D hD => by
      simpa using fun h0 => hD (by simp [h0]),
    Aux.stalk_prod, ← Finset.prod_filter_mul_prod_filter_not hfin.toFinset
      fun D => x ∈ (D.support : Set X)]
  conv_rhs => rw [← mul_one (∏ D ∈ _, _)]
  congr 1
  · exact Finset.prod_congr rfl fun D _ => Aux.stalk_pow _ _ _
  · refine Finset.prod_eq_one fun D hD => ?_
    rw [Aux.stalk_pow, (IdealSheafData.stalk_eq_top_iff_notMem_support _ _).2
      (Finset.mem_filter.1 hD).2, Ideal.top_pow, Ideal.one_eq_top]

/-- Each prime divisor through `x` with nonzero coefficient is a component of a member of `E`
through `x`. -/
private theorem exists_component_of_mem_throughDivisors {X : Scheme.{u}} {C : MonomialData X}
    (hC : C.IsMonomialData) {x : X} {D : AlgebraicGeometry.PrimeDivisor X}
    (hD : D ∈ throughDivisors C hC.2.2.2.2.1 x) : ∃ i : Fin C.E.s,
      D.support ∈ componentsOf ((C.E.E i).support : Set X) ∧ x ∈ ((C.E.E i).support : Set X) := by
  rw [mem_throughDivisors] at hD
  obtain ⟨i, hi⟩ := hC.2.2.2.2.2 D hD.1
  exact ⟨i, hi, subset_of_mem_componentsOf hi hD.2⟩

/-- In coordinates `z` at `x` in which the members of `E` through `x` are `(z_{c(j)})`, the stalk
of `𝒪_X(-A)` contains a monomial in `z` of degree `∑_{D ∋ x} a_D`. -/
private theorem exists_monomial_le_stalk {X : Scheme.{u}} (C : MonomialData X)
    (hC : C.IsMonomialData) {x : X} {n : ℕ} (z : Fin n → X.presheaf.stalk x)
    (c : {j // x ∈ ((C.E.E j).support : Set X)} → Fin n)
    (hzE : ∀ j, IdealSheafData.stalk (C.E.E j.1) x = Ideal.span {z (c j)}) :
    ∃ e : Fin n → ℕ, ∑ i, e i = ∑ D ∈ throughDivisors C hC.2.2.2.2.1 x, C.A D ∧
      Ideal.span {∏ i, z i ^ e i} ≤ IdealSheafData.stalk C.monomialIdeal x := by
  classical
  rw [stalk_monomialIdeal_eq_prod C hC.2.2.2.2.1]
  suffices ∀ t ⊆ throughDivisors C hC.2.2.2.2.1 x, ∃ e : Fin n → ℕ, ∑ i, e i = ∑ D ∈ t, C.A D ∧
      Ideal.span {∏ i, z i ^ e i} ≤ ∏ D ∈ t, IdealSheafData.stalk D.idealSheaf x ^ C.A D from
    this _ le_rfl
  intro t
  induction t using Finset.induction_on with
  | empty => intro _; exact ⟨0, by simp, by simp⟩
  | insert D t hDt IH =>
    intro ht
    obtain ⟨e, he, hle⟩ := IH ((Finset.subset_insert _ _).trans ht)
    obtain ⟨i, hi, hxi⟩ := exists_component_of_mem_throughDivisors hC (ht (t.mem_insert_self D))
    refine ⟨fun j => e j + if j = c ⟨i, hxi⟩ then C.A D else 0, ?_, ?_⟩
    · simp [Finset.sum_insert hDt, Finset.sum_add_distrib, ← he, add_comm]
    · have hprod : ∏ j, z j ^ (e j + if j = c ⟨i, hxi⟩ then C.A D else 0) =
          z (c ⟨i, hxi⟩) ^ C.A D * ∏ j, z j ^ e j := by
        simp only [pow_add, Finset.prod_mul_distrib, pow_ite, pow_zero]
        rw [mul_comm]
        simp
      rw [hprod, Finset.prod_insert hDt, ← Ideal.span_singleton_mul_span_singleton,
        ← Ideal.span_singleton_pow, ← hzE ⟨i, hxi⟩]
      exact Ideal.mul_mono (Ideal.pow_right_mono (stalk_le_stalk_of_le
        (le_idealSheaf_of_support_subset _ _ (subset_of_mem_componentsOf hi)) x) _) hle

/-- No nonempty set is an irreducible component of two distinct members of the snc divisor `E`:
at a point of it, both members are cut out by the closure of the point given by their local
equations, which are distinct members of a regular system of parameters. -/
private theorem false_of_mem_componentsOf_of_ne (hC : C.IsMonomialData) {W : Set X}
    {a b : Fin C.E.s} (hab : a ≠ b) (ha : W ∈ componentsOf ((C.E.E a).support : Set X))
    (hb : W ∈ componentsOf ((C.E.E b).support : Set X)) {x : X} (hxW : x ∈ W) : False := by
  obtain ⟨-, hlft, -, hE, -, -⟩ := id hC
  haveI := hlft
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian C.sX
  obtain ⟨n, z, c, hz, hst, hc⟩ := hE.2.2 x
  let ia := c ⟨a, ha.1.2 hxW⟩
  let ib := c ⟨b, hb.1.2 hxW⟩
  have hne : ib ≠ ia := fun h => hab (congrArg Subtype.val (hc h)).symm
  have hJ : ∀ (j : Fin C.E.s) (hj : x ∈ ((C.E.E j).support : Set X)),
      IdealSheafData.stalk (C.E.E j) x = (coordPrime hz {c ⟨j, hj⟩}).asIdeal := by
    intro j hj
    rw [hst ⟨j, hj⟩]
    simp [coordPrime]
  have hWa := eq_closure_coordPrime_of_mem_componentsOf hz (hJ a (ha.1.2 hxW)) ha hxW
  have hWb := eq_closure_coordPrime_of_mem_componentsOf hz (hJ b (hb.1.2 hxW)) hb hxW
  have hle : (coordPrime hz {ia}).asIdeal ≤ (coordPrime hz {ib}).asIdeal := by
    rw [← fromSpecStalk_mem_closure_iff, ← hWa, hWb]
    exact subset_closure rfl
  have hsp : ∀ i : Fin n, (coordPrime hz {i}).asIdeal = Ideal.span {z i} := fun i => by
    simp [coordPrime]
  rw [hsp, hsp] at hle
  exact notMem_span_singleton_of_ne_of_isRegularSystemOfParameters hz hne
    (hle (Ideal.subset_span rfl))

/-- At the generic point `η` of a component of `Z`, the members of `E` through `η` are exactly
those of `J_*`: the `r` local equations of `E^{J_*}` generate `𝔪_η`, so they are the whole
regular system of parameters at `η`. -/
private theorem mem_stepIndex_of_genericPoint (hC : C.IsMonomialData) {r : ℕ} {W : Set X}
    (hW : W ∈ componentsOf ((C.stepCenter r).support : Set X)) {η : X}
    (hη : closure {η} = W) {i : Fin C.E.s} (hi : η ∈ ((C.E.E i).support : Set X)) :
    i ∈ C.stepIndex r := by
  classical
  obtain ⟨-, hlft, -, hE, -, -⟩ := id hC
  haveI := hlft
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian C.sX
  have hηZ : η ∈ ((C.stepCenter r).support : Set X) := hW.1.2 (hη ▸ subset_closure rfl)
  obtain ⟨n, z, c, hz, hst, hc⟩ := hE.2.2 η
  have := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz
  set J : Finset (Fin n) := (Finset.univ.filter fun t => t.1 ∈ C.stepIndex r).image c
  have hZ0 : IdealSheafData.stalk (C.stepCenter r) η = Ideal.span (z '' (J : Set (Fin n))) :=
    stalk_stepCenter_eq_span C hC r hηZ hz hst fun i => by simp [J]
  have hZ : IdealSheafData.stalk (C.stepCenter r) η = (coordPrime hz J).asIdeal := hZ0
  have hWJ := eq_closure_coordPrime_of_mem_componentsOf hz hZ hW (hη ▸ subset_closure rfl)
  -- so `𝔪_η ≤ (z_j : j ∈ J)`
  have hm : IsLocalRing.maximalIdeal (X.presheaf.stalk η) ≤
      Ideal.span (z '' (J : Set (Fin n))) := by
    have h1 : X.fromSpecStalk η (coordPrime hz J) ∈ closure {(X.fromSpecStalk η
        (IsLocalRing.closedPoint _))} := by
      rw [Scheme.fromSpecStalk_closedPoint, hη, hWJ]; exact subset_closure rfl
    exact (fromSpecStalk_mem_closure_iff η _ _).1 h1
  -- hence `J` is everything
  have hJ : J = Finset.univ := by
    refine Finset.eq_univ_of_card _ (le_antisymm (Finset.card_le_univ _) ?_)
    have hspan : Ideal.span (z '' (J : Set (Fin n))) =
        IsLocalRing.maximalIdeal (X.presheaf.stalk η) := by
      refine le_antisymm (Ideal.span_le.2 ?_) hm
      rintro _ ⟨l, -, rfl⟩
      rw [← hz.1]; exact Ideal.subset_span ⟨l, rfl⟩
    have hle := Submodule.spanFinrank_span_le_ncard_of_finite
      (R := X.presheaf.stalk η) (Set.toFinite (z '' (J : Set (Fin n))))
    rw [show Submodule.span (X.presheaf.stalk η) (z '' (J : Set (Fin n))) =
      IsLocalRing.maximalIdeal _ from hspan] at hle
    have hcard : (z '' (J : Set (Fin n))).ncard ≤ J.card :=
      (Set.ncard_image_le (Set.toFinite _)).trans (by rw [Set.ncard_coe_finset])
    have hrank := IsRegularLocalRing.spanFinrank_maximalIdeal (R := X.presheaf.stalk η)
    rw [hz.2] at hrank
    have : (IsLocalRing.maximalIdeal (X.presheaf.stalk η)).spanFinrank = n := by
      exact_mod_cast hrank
    simp only [Fintype.card_fin]
    omega
  have hci : c ⟨i, hi⟩ ∈ J := hJ ▸ Finset.mem_univ _
  simp only [J, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hci
  obtain ⟨t, ht, hct⟩ := hci
  rw [← show t.1 = i from congrArg Subtype.val (hc hct)]
  exact ht

/-- `ord_Z I_{E,A} = m_r(E, A)`: the order of a monomial in a regular system of parameters is its
degree, and at the generic point of a max piece that degree is `σ_{J_*} = m_r(E, A)`. -/
private theorem orderAlongEq_stepCenter (hC : C.IsMonomialData) (r : ℕ) :
    OrderAlongEq C.monomialIdeal ((C.stepCenter r).support : Set X)
      (C.maxStratumWeight r : ℕ∞) := by
  classical
  obtain ⟨-, hlft, -, hE, hfin, -⟩ := id hC
  haveI := hlft
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian C.sX
  intro W hW
  unfold orderAlong
  obtain ⟨η₀, -, hW₀⟩ :=
    Aux.exists_eq_closure_of_mem_componentsOf (C.stepCenter r).support.isClosed hW
  set η := hW.1.1.genericPoint
  have hη : closure {η} = W := by
    have hWc : IsClosed W := hW₀ ▸ isClosed_closure
    exact (show closure {η} = closure W from
      hW.1.1.isGenericPoint_genericPoint_closure).trans hWc.closure_eq
  have hηZ : η ∈ ((C.stepCenter r).support : Set X) := hW.1.2 (hη ▸ subset_closure rfl)
  set T := throughDivisors C hfin η
  -- `∑_{D ∋ η} a_D = σ_{J_*}(η)`
  have hsum : ∑ D ∈ T, C.A D = C.stratumWeight (C.stepIndex r) η := by
    let f : Fin C.E.s → AlgebraicGeometry.PrimeDivisor X → ℕ := fun j D =>
      if D.support ∈ componentsOf ((C.E.E j).support : Set X) ∧ η ∈ (D.support : Set X)
      then C.A D else 0
    have hcoeff : ∀ j, C.coeffAt j η = ∑ D ∈ T, f j D := by
      intro j
      unfold MonomialData.coeffAt
      refine finsum_eq_sum_of_support_subset _ fun D hD => ?_
      rw [Function.mem_support] at hD
      rw [Finset.mem_coe, mem_throughDivisors]
      by_cases h : D.support ∈ componentsOf ((C.E.E j).support : Set X) ∧ η ∈ (D.support : Set X)
      · rw [if_pos h] at hD; exact ⟨hD, h.2⟩
      · exact absurd (if_neg h) hD
    unfold MonomialData.stratumWeight
    rw [Finset.sum_congr rfl fun j _ => hcoeff j, Finset.sum_comm]
    refine Finset.sum_congr rfl fun D hD => ?_
    obtain ⟨i, hi, hηi⟩ := exists_component_of_mem_throughDivisors hC hD
    have hiJ := mem_stepIndex_of_genericPoint C hC hW hη hηi
    have hηD : η ∈ (D.support : Set X) := (mem_throughDivisors.1 hD).2
    rw [← Finset.sum_erase_add _ _ hiJ, Finset.sum_eq_zero, zero_add]
    · simp only [f]; rw [if_pos ⟨hi, hηD⟩]
    · intro j hj
      simp only [f]
      refine if_neg fun h => ?_
      exact false_of_mem_componentsOf_of_ne C hC (Finset.ne_of_mem_erase hj) h.1 hi hηD
  have hσ : C.stratumWeight (C.stepIndex r) η = C.maxStratumWeight r := by
    rw [coe_support_stepCenter C hC] at hηZ
    obtain ⟨P, hP, hηP⟩ := hηZ
    exact hP.2.2 η hηP
  rw [← hσ, ← hsum]
  refine le_antisymm ?_ ?_
  · obtain ⟨n, z, c, hz, hzE, -⟩ := hE.2.2 η
    obtain ⟨e, he, hle⟩ := exists_monomial_le_stalk C hC z c hzE
    refine (idealOrder_antitone hle).trans <| (idealOrder_span_singleton_le
      (prod_pow_notMem_of_isRegularSystemOfParameters hz e)).trans ?_
    rw [he]
  · refine le_iSup₂_of_le (f := fun (j : ℕ)
      (_ : IdealSheafData.stalk C.monomialIdeal η ≤ IsLocalRing.maximalIdeal _ ^ j) => (j : ℕ∞))
      _ ?_ le_rfl
    rw [stalk_monomialIdeal_eq_prod C hfin, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod' fun D hD => Ideal.pow_right_mono ?_ _
    refine IsLocalRing.le_maximalIdeal fun htop => ?_
    exact (IdealSheafData.stalk_eq_top_iff_notMem_support _ _).1 htop
      (mem_throughDivisors.1 hD).2

/-- The order of an ideal sheaf at a point outside its support is `0`. -/
private theorem mem_support_of_multAt_ne_zero {Y : Scheme.{u}} (J : Y.IdealSheafData) (y : Y)
    (h : multAt J y ≠ 0) : y ∈ (J.support : Set Y) := by
  by_contra hy
  apply h
  rw [multAt, (IdealSheafData.stalk_eq_top_iff_notMem_support J y).2 hy]
  refine le_antisymm (iSup₂_le fun j hj => ?_) bot_le
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp
  · exact absurd ((top_le_iff.1 hj).symm ▸ Ideal.pow_le_self hj0.ne' :
      (⊤ : Ideal (Y.presheaf.stalk y)) ≤ IsLocalRing.maximalIdeal _)
      fun h' => (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.1 h')

/-- The support of a pull-back ideal sheaf lies over the support. -/
private theorem mem_support_of_mem_support_comap {Y Y' : Scheme.{u}} (f : Y' ⟶ Y)
    (J : Y.IdealSheafData) {y : Y'} (hy : y ∈ ((J.comap f).support : Set Y')) :
    f y ∈ (J.support : Set Y) := by
  by_contra hfy
  refine (IdealSheafData.stalk_eq_top_iff_notMem_support _ y).1 ?_ hy
  rw [IdealSheafData.stalk_comap, (IdealSheafData.stalk_eq_top_iff_notMem_support J _).2 hfy,
    Ideal.map_top]

/-- The support of `𝒪_X(-A)` lies in `Supp E`. -/
private theorem exists_mem_E_of_mem_support_monomialIdeal (hC : C.IsMonomialData) {x : X}
    (hx : x ∈ (C.monomialIdeal.support : Set X)) :
    ∃ i : Fin C.E.s, x ∈ ((C.E.E i).support : Set X) := by
  classical
  by_contra hno
  push Not at hno
  refine (IdealSheafData.stalk_eq_top_iff_notMem_support _ x).1 ?_ hx
  rw [stalk_monomialIdeal_eq_prod C hC.2.2.2.2.1, ← Ideal.one_eq_top]
  refine Finset.prod_eq_one fun D hD => ?_
  obtain ⟨i, -, hxi⟩ := exists_component_of_mem_throughDivisors hC hD
  exact absurd hxi (hno i)

/-- In a Noetherian space, a prime divisor whose generic point lies in a closed set of pure
codimension one is an irreducible component of it. -/
private theorem support_mem_componentsOf_of_isPureCodimOne {Y : Scheme.{u}} [NoetherianSpace Y]
    (S : Closeds Y) (hS : MMP.Mori.IsPureCodimOne S) (D : AlgebraicGeometry.PrimeDivisor Y)
    (hD : D.genericPoint ∈ (S : Set Y)) : (D.support : Set Y) ∈ componentsOf (S : Set Y) := by
  have hDS : (D.support : Set Y) ⊆ S := by
    rw [Aux.support_eq_closure_genericPoint]
    exact closure_minimal (Set.singleton_subset_iff.2 hD) S.isClosed
  have hDirr : IsIrreducible (D.support : Set Y) := by
    rw [Aux.support_eq_closure_genericPoint]; exact isIrreducible_singleton.closure
  refine ⟨⟨hDirr, hDS⟩, fun W hW hle => ?_⟩
  obtain ⟨hfin, hcov⟩ := Aux.finite_and_cover_componentsOf S.isClosed
  obtain ⟨V, hV, hWV⟩ := isIrreducible_iff_sUnion_isClosed.mp hW.1 hfin.toFinset
    (fun V hV => Aux.isClosed_of_mem_componentsOf S.isClosed (hfin.mem_toFinset.1 hV))
    (by rw [Set.Finite.coe_toFinset]; exact hW.2.trans hcov)
  rw [Set.Finite.mem_toFinset] at hV
  have hVc : IsClosed V := Aux.isClosed_of_mem_componentsOf S.isClosed hV
  let V' : IrreducibleCloseds Y := ⟨V, hV.1.1, hVc⟩
  have hV1 : codimension V' = 1 := hS V' ⟨hV.1.2, fun W' hW' hle' => hV.2 ⟨W'.2, hW'⟩ hle'⟩
  have hD1 := D.codimension_one
  suffices hDV : (D.support : Set Y) = V from hDV ▸ hWV
  refine (hle.trans hWV).antisymm' ?_ |>.symm
  by_contra hne
  have hlt : IrreducibleCloseds.closureSingleton D.genericPoint < V' := by
    refine lt_of_le_of_ne (fun y hy => ?_) fun heq => hne ?_
    · have : closure {D.genericPoint} ⊆ V := by
        rw [← Aux.support_eq_closure_genericPoint]; exact hle.trans hWV
      exact this hy
    · intro y hy
      have : y ∈ (V' : Set Y) := hy
      rw [← heq] at this
      change y ∈ closure {D.genericPoint} at this
      rwa [← Aux.support_eq_closure_genericPoint] at this
  have e := Order.coheight_add_one_le hlt
  have h2 : codimension V' + 1 ≤ codimension (IrreducibleCloseds.closureSingleton D.genericPoint) :=
    e
  have hD1' : codimension (IrreducibleCloseds.closureSingleton D.genericPoint) = 1 := hD1
  rw [hV1, hD1'] at h2
  exact absurd h2 (by decide)

/-- A component of `Z` of codimension `≥ 2` is no component of `Supp E`. -/
private theorem notMem_componentsOf_support_of_two_le_codimension (hC : C.IsMonomialData)
    {r : ℕ} {W : Set X} (hW : W ∈ componentsOf ((C.stepCenter r).support : Set X))
    (h2 : 2 ≤ codimension (irreducibleClosure hW.1.1)) : W ∉ componentsOf C.E.support := by
  intro hWE
  obtain ⟨-, -, -, hE, -, -⟩ := id hC
  have hWc : IsClosed W := Aux.isClosed_of_mem_componentsOf (C.stepCenter r).support.isClosed hW
  have hcl : (irreducibleClosure hW.1.1 : Set X) = W := hWc.closure_eq
  obtain ⟨j, hj⟩ : ∃ j, W ⊆ ((C.E.E j).support : Set X) := by
    have := isIrreducible_iff_sUnion_isClosed.mp hWE.1.1
      (Finset.univ.image fun i => ((C.E.E i).support : Set X))
      (fun V hV => by
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hV
        obtain ⟨i, rfl⟩ := hV
        exact (C.E.E i).support.isClosed)
      (by
        intro y hy
        obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hWE.1.2 hy)
        exact Set.mem_sUnion.2 ⟨_, by simp, hi⟩)
    obtain ⟨V, hV, hWV⟩ := this
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hV
    obtain ⟨i, rfl⟩ := hV
    exact ⟨i, hWV⟩
  have h1 : codimension (irreducibleClosure hW.1.1) = 1 := by
    refine (hE.2.1 j).2.1 _ ⟨?_, fun W' hW' hle => ?_⟩
    · show closure W ⊆ _
      rw [hWc.closure_eq]; exact hj
    · show (W' : Set X) ⊆ closure W
      rw [hWc.closure_eq]
      have hle' : W ⊆ W' := fun y hy => hle (subset_closure hy)
      exact hWE.2 ⟨W'.2, (show (W' : Set X) ⊆ _ from hW').trans
        (Set.subset_iUnion (fun i => ((C.E.E i).support : Set X)) j)⟩ hle'
  rw [h1] at h2
  exact absurd h2 (by decide)

/-- `A'` is supported on `E'`: a prime divisor with nonzero coefficient in `A'` is a component
of `Supp E'`. -/
private theorem isComponent_of_step_A_ne_zero (hC : C.IsMonomialData) (hk : CharZero C.k)
    {m r : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) (hmr : m ≤ C.maxStratumWeight r)
    (D' : AlgebraicGeometry.PrimeDivisor (blowUp (C.stepCenter r))) (hD' : (C.step m r).A D' ≠ 0) :
    (C.step m r).E.IsComponent D' := by
  obtain ⟨-, hlft, hqc, hE, -, -⟩ := id hC
  haveI := hlft
  haveI := hqc
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian C.sX
  haveI : LocallyOfFiniteType (blowUpToBase (C.stepCenter r) ≫ C.sX) := inferInstance
  haveI : QuasiCompact (blowUpToBase (C.stepCenter r) ≫ C.sX) := inferInstance
  haveI : NoetherianSpace (blowUp (C.stepCenter r)) :=
    Aux.noetherianSpace_of_finiteType (blowUpToBase (C.stepCenter r) ≫ C.sX)
  have hsnc := hasSNCWith_stepCenter C hC r
  have hE' := isOrderedSNC_totalTransform C.sX hE.2 hsnc
  -- the generic point of `D'` lies on the support of `π^*𝒪(-A)`
  have hmult : multAt ((divisorIdeal C.A).comap (blowUpToBase (C.stepCenter r)))
      D'.genericPoint ≠ 0 := by
    intro h0
    apply hD'
    change (multAt ((divisorIdeal C.A).comap (blowUpToBase (C.stepCenter r)))
      D'.genericPoint).toNat - _ = 0
    rw [h0]; simp
  have hx := mem_support_of_mem_support_comap (blowUpToBase (C.stepCenter r)) _
    (mem_support_of_multAt_ne_zero _ D'.genericPoint hmult)
  obtain ⟨i, hi⟩ := exists_mem_E_of_mem_support_monomialIdeal C hC hx
  -- it lies on a member of `E'`
  obtain ⟨j, hj⟩ : ∃ j, D'.genericPoint ∈
      (((C.E.totalTransform (C.stepCenter r)).E j).support : Set (blowUp (C.stepCenter r))) := by
    have hsub : ∀ j, totalTransformSet C.E (C.stepCenter r) j ⊆
        (((C.E.totalTransform (C.stepCenter r)).E j).support :
          Set (blowUp (C.stepCenter r))) := fun j => by
      rw [totalTransform_E_eq, Scheme.IdealSheafData.coe_support_vanishingIdeal,
        Closeds.coe_closure]
      exact subset_closure
    by_cases h2 : blowUpToBase (C.stepCenter r) D'.genericPoint ∈
        componentsOfCodimAtLeastTwo ((C.stepCenter r).support : Set X)
    · refine ⟨Fin.last _, hsub _ ?_⟩
      simp only [componentsOfCodimAtLeastTwo, Set.mem_iUnion] at h2
      obtain ⟨W, hW, hcod, hηW⟩ := h2
      simp only [totalTransformSet, Fin.snoc_last, Set.mem_iUnion, Set.mem_preimage]
      exact ⟨W, hW, notMem_componentsOf_support_of_two_le_codimension C hC hW hcod, hηW⟩
    · refine ⟨Fin.castSucc i, hsub _ ?_⟩
      simp only [totalTransformSet, Fin.snoc_castSucc, Set.mem_preimage]
      exact ⟨hi, h2⟩
  exact ⟨j, support_mem_componentsOf_of_isPureCodimOne _ (hE'.2.1 j).2.1 D' hj⟩

/-- The coefficients of `A'` have finite support. -/
private theorem finite_support_step_A (hC : C.IsMonomialData) (hk : CharZero C.k)
    {m r : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) (hmr : m ≤ C.maxStratumWeight r) :
    (Function.support (C.step m r).A).Finite := by
  obtain ⟨-, hlft, hqc, -, -, -⟩ := id hC
  haveI := hlft
  haveI := hqc
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian C.sX
  exact (Aux.finite_primeDivisor_of_isComponent (blowUpToBase (C.stepCenter r) ≫ C.sX)
    (C.step m r).E.E).subset fun D' hD' => isComponent_of_step_A_ne_zero C hC hk hr hm hmr D' hD'

/-- The new data `(X', E', A')` are monomial data: `X'` is smooth (char `0`, smooth centre),
`E'` is ordered snc, and `A'` is supported on `E'`. -/
private theorem isMonomialData_step (hC : C.IsMonomialData) (hk : CharZero C.k)
    {m r : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) (hmr : m ≤ C.maxStratumWeight r)
    (hsnc : HasSNCWith C.E.E (C.stepCenter r)) :
    (C.step m r).IsMonomialData := by
  obtain ⟨hsm, hlft, hqc, hE, -, -⟩ := id hC
  haveI := hlft
  haveI := hqc
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian C.sX
  have hZsm := isSmoothScheme_subschemeι_of_hasSNCWith C.sX hsm (C.stepCenter r) hsnc
  have hB : Smooth (blowUpToBase (C.stepCenter r) ≫ C.sX) :=
    (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup C.sX (C.stepCenter r)
      ⟨hsm, hZsm⟩).1
  refine ⟨@isSmoothScheme_of_smooth _ _ _ hB, (inferInstance : LocallyOfFiniteType
      (blowUpToBase (C.stepCenter r) ≫ C.sX)), (inferInstance : QuasiCompact
      (blowUpToBase (C.stepCenter r) ≫ C.sX)),
    isOrderedSNC_totalTransform C.sX hE.2 hsnc,
    finite_support_step_A C hC hk hr hm hmr, isComponent_of_step_A_ne_zero C hC hk hr hm hmr⟩

/-- Two prime divisors with nested supports are equal: both have codimension one. -/
private theorem primeDivisor_eq_of_support_subset {Y : Scheme.{u}}
    {D D'' : AlgebraicGeometry.PrimeDivisor Y} (h : (D.support : Set Y) ⊆ D''.support) :
    D = D'' := by
  refine Aux.PrimeDivisor.eq_of_support_eq (h.antisymm ?_)
  by_contra hne
  have hlt : IrreducibleCloseds.closureSingleton D.genericPoint <
      IrreducibleCloseds.closureSingleton D''.genericPoint := by
    refine lt_of_le_of_ne (fun y hy => ?_) fun heq => hne ?_
    · have : closure {D.genericPoint} ⊆ closure {D''.genericPoint} := by
        rw [← Aux.support_eq_closure_genericPoint, ← Aux.support_eq_closure_genericPoint]
        exact h
      exact this hy
    · have := congrArg (fun W : IrreducibleCloseds Y => (W : Set Y)) heq
      change closure {D.genericPoint} = closure {D''.genericPoint} at this
      rw [Aux.support_eq_closure_genericPoint, Aux.support_eq_closure_genericPoint, this]
  have e := Order.coheight_add_one_le hlt
  have h2 : codimension (IrreducibleCloseds.closureSingleton D''.genericPoint) + 1 ≤
      codimension (IrreducibleCloseds.closureSingleton D.genericPoint) := e
  have h1 : codimension (IrreducibleCloseds.closureSingleton D.genericPoint) = 1 :=
    D.codimension_one
  have h1' : codimension (IrreducibleCloseds.closureSingleton D''.genericPoint) = 1 :=
    D''.codimension_one
  rw [h1, h1'] at h2
  exact absurd h2 (by decide)

/-- The order of `𝔪^a` is `a` in a Noetherian local domain which is not a field. -/
private theorem idealOrder_maximalIdeal_pow {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsDomain R] (h : IsLocalRing.maximalIdeal R ≠ ⊥) (a : ℕ) :
    idealOrder (IsLocalRing.maximalIdeal R ^ a) = a := by
  refine le_antisymm (iSup₂_le fun j hj => ?_) (le_iSup₂_of_le
    (f := fun (j : ℕ) (_ : IsLocalRing.maximalIdeal R ^ a ≤ IsLocalRing.maximalIdeal R ^ j) =>
      (j : ℕ∞)) a le_rfl le_rfl)
  by_contra hlt
  have hlt' : a + 1 ≤ j := by exact_mod_cast Order.add_one_le_of_lt (not_le.1 hlt)
  have heq : IsLocalRing.maximalIdeal R ^ a = IsLocalRing.maximalIdeal R ^ (a + 1) :=
    le_antisymm (hj.trans (Ideal.pow_le_pow_right hlt')) (Ideal.pow_le_pow_right (by omega))
  have := MMP.Resolution.maximalIdeal_pow_injective h heq
  omega

/-- The order is invariant under a bijective ring map of local rings. -/
private theorem idealOrder_map_of_bijective {R S : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] (φ : R →+* S) (hφ : Function.Bijective φ) (J : Ideal R) :
    idealOrder (J.map φ) = idealOrder J := by
  let e : R ≃+* S := RingEquiv.ofBijective φ hφ
  have hm : (IsLocalRing.maximalIdeal R).map e = IsLocalRing.maximalIdeal S :=
    IsLocalRing.map_ringEquiv_maximalIdeal e
  have key : ∀ j : ℕ, J.map φ ≤ IsLocalRing.maximalIdeal S ^ j ↔
      J ≤ IsLocalRing.maximalIdeal R ^ j := by
    intro j
    change J.map e ≤ _ ↔ _
    rw [← hm, ← Ideal.map_pow, Ideal.map_le_iff_le_comap, Ideal.comap_map_of_bijective _
      e.bijective]
  simp only [idealOrder, key]

/-- The stalk maps of an isomorphism are isomorphisms. -/
private theorem isIso_stalkMap_of_isIso {Y₁ Y₂ : Scheme.{u}} (f : Y₁ ⟶ Y₂) [IsIso f] (y : Y₁) :
    IsIso (f.stalkMap y) := by
  haveI : IsOpenImmersion f := inferInstance
  infer_instance

/-- The blow-up is an isomorphism off the centre: its stalk maps there are isomorphisms. -/
private theorem bijective_stalkMap_of_notMem {Y : Scheme.{u}} (Z : Y.IdealSheafData)
    (y : blowUp Z) (hy : blowUpToBase Z y ∉ (Z.support : Set Y)) :
    Function.Bijective ((blowUpToBase Z).stalkMap y).hom := by
  let x : (blowUpToBase Z ⁻¹ᵁ Z.support.compl : Scheme.Opens _) := ⟨y, hy⟩
  have e := morphismRestrictStalkMap (blowUpToBase Z) Z.support.compl x
  haveI : IsIso (blowUpToBase Z ∣_ Z.support.compl) := isIso_blowUpToBase_restrict_compl_support Z
  have hI := isIso_stalkMap_of_isIso (blowUpToBase Z ∣_ Z.support.compl) x
  have : IsIso ((blowUpToBase Z).stalkMap y) :=
    (Arrow.isIso_hom_iff_isIso_hom_of_isIso e.hom).1 hI
  exact ConcreteCategory.bijective_of_isIso _

/-- The order of `𝒪_X(-A)` along a prime divisor `D` is its coefficient `a_D`. -/
private theorem multAt_monomialIdeal_genericPoint (hC : C.IsMonomialData)
    (D : AlgebraicGeometry.PrimeDivisor X) :
    multAt C.monomialIdeal D.genericPoint = C.A D := by
  classical
  obtain ⟨hsm, hlft, -, -, hfin, -⟩ := id hC
  haveI := hlft
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian C.sX
  haveI := Aux.smooth_of_isSmoothScheme' C.sX hsm
  have := isRegularLocalRing_stalk_of_smooth_over_field C.sX D.genericPoint
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk D.genericPoint)
  rw [multAt, stalk_monomialIdeal_eq_prod C hfin]
  have hT : throughDivisors C hfin D.genericPoint ⊆ {D} := by
    intro D'' hD''
    rw [Finset.mem_singleton]
    refine (primeDivisor_eq_of_support_subset ?_).symm
    rw [Aux.support_eq_closure_genericPoint D]
    exact closure_minimal (Set.singleton_subset_iff.2 (mem_throughDivisors.1 hD'').2)
      D''.idealSheaf.support.isClosed
  rw [Finset.prod_subset hT fun D'' hD'' hnot => by
    rw [Finset.mem_singleton] at hD''
    subst hD''
    have : C.A D'' = 0 := by
      by_contra h0
      exact hnot (mem_throughDivisors.2 ⟨h0, by
        rw [Aux.support_eq_closure_genericPoint]; exact subset_closure rfl⟩)
    rw [this, pow_zero], Finset.prod_singleton, Aux.stalk_idealSheaf_genericPoint]
  exact idealOrder_maximalIdeal_pow (maximalIdeal_stalk_genericPoint_ne_bot D) _

/-- In a local domain of dimension one, a nonzero prime is the maximal ideal. -/
private theorem eq_maximalIdeal_of_ringKrullDim_eq_one {R : Type*} [CommRing R] [IsLocalRing R]
    [IsDomain R] (h : ringKrullDim R = 1) {p : Ideal R} [p.IsPrime] (hp : p ≠ ⊥) :
    p = IsLocalRing.maximalIdeal R := by
  haveI : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.2 (h ▸ le_rfl)
  exact IsLocalRing.eq_maximalIdeal
    ((Ring.krullDimLE_one_iff_of_isPrime_bot.1 inferInstance) p hp inferInstance)

/-- The blow-up of `X` along `Z` is smooth, and so is its exceptional divisor. -/
private theorem smooth_blowUp_stepCenter (hC : C.IsMonomialData) (hk : CharZero C.k) (r : ℕ) :
    Smooth (blowUpToBase (C.stepCenter r) ≫ C.sX) ∧
      Smooth ((exceptionalIdeal (C.stepCenter r)).subschemeι ≫
        blowUpToBase (C.stepCenter r) ≫ C.sX) := by
  obtain ⟨hsm, hlft, hqc, -, -, -⟩ := id hC
  haveI := hlft
  haveI := hqc
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian C.sX
  have hZsm := isSmoothScheme_subschemeι_of_hasSNCWith C.sX hsm (C.stepCenter r)
    (hasSNCWith_stepCenter C hC r)
  obtain ⟨h1, h2, -⟩ :=
    Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup C.sX (C.stepCenter r)
      ⟨hsm, hZsm⟩
  exact ⟨h1, h2⟩

/-- Over a point of the support of `Z`, the stalk of `π^*I_Z` is a proper ideal. -/
private theorem stalk_comap_ne_top {Y Y' : Scheme.{u}} {f : Y' ⟶ Y} (Z : Y.IdealSheafData)
    {y : Y'} (h : f y ∈ (Z.support : Set Y)) : IdealSheafData.stalk (Z.comap f) y ≠ ⊤ := by
  rw [Ne, IdealSheafData.stalk_eq_top_iff_notMem_support, Scheme.IdealSheafData.support_comap,
    not_not]
  exact h

/-- Over the centre, `π^*I_Z = 𝒪(-F)` has order `1` along a prime divisor of `B_Z X`: the
exceptional divisor is reduced and invertible, so its stalk at the generic point of a prime
divisor in it is a nonzero radical ideal of a one-dimensional local domain. -/
private theorem multAt_comap_stepCenter_eq_one (hC : C.IsMonomialData) (hk : CharZero C.k)
    {r : ℕ}
    (D' : AlgebraicGeometry.PrimeDivisor (blowUp (C.stepCenter r)))
    (h : blowUpToBase (C.stepCenter r) D'.genericPoint ∈ ((C.stepCenter r).support : Set X)) :
    multAt ((C.stepCenter r).comap (blowUpToBase (C.stepCenter r))) D'.genericPoint = 1 := by
  obtain ⟨-, hlft, hqc, -, -, -⟩ := id hC
  haveI := hlft
  haveI := hqc
  obtain ⟨hB, hF⟩ := smooth_blowUp_stepCenter C hC hk r
  haveI := hB
  haveI : LocallyOfFiniteType (blowUpToBase (C.stepCenter r) ≫ C.sX) := inferInstance
  haveI : IsLocallyNoetherian (blowUp (C.stepCenter r)) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase (C.stepCenter r) ≫ C.sX)
  have := isRegularLocalRing_stalk_of_smooth_over_field (blowUpToBase (C.stepCenter r) ≫ C.sX)
    D'.genericPoint
  have := IsRegularLocalRing.isDomain ((blowUp (C.stepCenter r)).presheaf.stalk D'.genericPoint)
  have hred : IsReduced ((C.stepCenter r).comap (blowUpToBase (C.stepCenter r))).subscheme :=
    Aux.isReduced_subscheme_of_isSmoothScheme (blowUpToBase (C.stepCenter r) ≫ C.sX) _
      (@isSmoothScheme_of_smooth _ _ _ hF)
  have hrad : (IdealSheafData.stalk ((C.stepCenter r).comap (blowUpToBase (C.stepCenter r)))
      D'.genericPoint).IsRadical := by
    rw [Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme
      ((C.stepCenter r).comap (blowUpToBase (C.stepCenter r))) _ rfl]
    exact isRadical_stalk_vanishingIdeal _ _
  obtain ⟨g, hg, hKg⟩ := exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor _
    (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal (C.stepCenter r)) D'.genericPoint
  have hK0 : IdealSheafData.stalk ((C.stepCenter r).comap (blowUpToBase (C.stepCenter r)))
      D'.genericPoint ≠ ⊥ := by
    change IdealSheafData.stalk (exceptionalIdeal (C.stepCenter r)) D'.genericPoint ≠ ⊥
    rw [hKg, Ne, Ideal.span_singleton_eq_bot]
    exact hg.ne_zero
  have hKtop := stalk_comap_ne_top _ h
  have hKm : IdealSheafData.stalk ((C.stepCenter r).comap (blowUpToBase (C.stepCenter r)))
      D'.genericPoint = IsLocalRing.maximalIdeal _ := by
    rw [← hrad.radical, Ideal.radical_eq_sInf]
    refine le_antisymm (sInf_le ⟨IsLocalRing.le_maximalIdeal hKtop, inferInstance⟩)
      (le_sInf fun p ⟨hKp, hp⟩ => ?_)
    have hp0 : p ≠ ⊥ := fun h0 => hK0 (le_bot_iff.1 (h0 ▸ hKp))
    exact (eq_maximalIdeal_of_ringKrullDim_eq_one D'.ringKrullDim_stalk_genericPoint_eq_one
      hp0).ge
  rw [multAt, hKm, ← pow_one (IsLocalRing.maximalIdeal _),
    idealOrder_maximalIdeal_pow (maximalIdeal_stalk_genericPoint_ne_bot D')]
  rfl

/-- Over the centre, `π^*𝒪_X(-A)` has order `≥ m_r(E, A)` along a prime divisor of `B_Z X`:
`ord_Z 𝒪_X(-A) = m_r(E, A)` gives `π^*𝒪_X(-A) ⊆ 𝒪(-m_r F)`. -/
private theorem le_multAt_comap_monomialIdeal (hC : C.IsMonomialData) (hk : CharZero C.k)
    {r : ℕ}
    (D' : AlgebraicGeometry.PrimeDivisor (blowUp (C.stepCenter r)))
    (h : blowUpToBase (C.stepCenter r) D'.genericPoint ∈ ((C.stepCenter r).support : Set X)) :
    (C.maxStratumWeight r : ℕ∞) ≤
      multAt ((divisorIdeal C.A).comap (blowUpToBase (C.stepCenter r))) D'.genericPoint := by
  obtain ⟨hsm, hlft, hqc, -, -, -⟩ := id hC
  haveI := hlft
  haveI := hqc
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian C.sX
  have hZsm := isSmoothScheme_subschemeι_of_hasSNCWith C.sX hsm (C.stepCenter r)
    (hasSNCWith_stepCenter C hC r)
  have hord := orderAlongEq_stepCenter C hC r
  have hle := comap_le_comap_pow_of_stalk_le (blowUpToBase (C.stepCenter r)) _ _ _
    (stalk_le_pow_of_orderAlongGE C.sX hsm (C.stepCenter r) hZsm C.monomialIdeal
      (C.maxStratumWeight r) fun W hW => (hord W hW).ge)
  have hs := stalk_le_stalk_of_le hle D'.genericPoint
  rw [IdealSheafData.stalk_pow] at hs
  have hKtop := stalk_comap_ne_top _ h
  refine le_iSup₂_of_le (f := fun (j : ℕ) (_ : IdealSheafData.stalk
      ((divisorIdeal C.A).comap (blowUpToBase (C.stepCenter r))) D'.genericPoint ≤
        IsLocalRing.maximalIdeal _ ^ j) => (j : ℕ∞)) (C.maxStratumWeight r) ?_ le_rfl
  exact hs.trans (Ideal.pow_right_mono (IsLocalRing.le_maximalIdeal hKtop) _)

/-- The order of an ideal sheaf is preserved by pull-back along an open immersion. -/
private theorem multAt_comap_of_isOpenImmersion {Y Y' : Scheme.{u}} (f : Y' ⟶ Y)
    [IsOpenImmersion f] (J : Y.IdealSheafData) (y : Y') :
    multAt (J.comap f) y = multAt J (f y) := by
  rw [multAt, IdealSheafData.stalk_comap,
    idealOrder_map_of_bijective _ (ConcreteCategory.bijective_of_isIso _)]
  rfl

/-- The centre `Z` restricted to the complement `U` of the components of `Z` other than `W`. -/
private theorem coe_support_comap_opens_eq {Y : Scheme.{u}} (Z : Y.IdealSheafData) (W : Set Y)
    (U : Y.Opens) (hZU : ∀ y ∈ U, y ∈ (Z.support : Set Y) → y ∈ W)
    (hWZ : W ⊆ Z.support) :
    ((Z.comap U.ι).support : Set U) = U.ι ⁻¹' W := by
  rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage]
  ext y
  exact ⟨fun hy => hZU _ y.2 hy, fun hy => hWZ hy⟩

/-- **Kollár 3.47 for a smooth reducible centre.** Let `X` be smooth over `k`, `Z ⊆ X` smooth
with components of codimension `≥ 1`, and `D'` a prime divisor of `B_Z X` lying over `Z`, over
the component `W` of `Z`. Then `ord_{D'}(π^*J) ≤ ord_W J`: away from the other components of `Z`
the blow-up is the blow-up of `W`, `D'` is its exceptional divisor, and there the order along the
exceptional divisor is the order along the centre. -/
private theorem multAt_comap_le_of_mem_support {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] [QuasiCompact sY]
    (hY : MMP.Mori.IsSmoothScheme sY) (Z : Y.IdealSheafData)
    (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sY))
    (hcodim : HasComponentsOfPositiveCodim (Z.support : Set Y)) (J : Y.IdealSheafData) (n : ℕ∞)
    (hJ : ∀ W (hW : W ∈ componentsOf (Z.support : Set Y)), orderAlong J hW.1.1 ≤ n)
    (D' : AlgebraicGeometry.PrimeDivisor (blowUp Z))
    (h : blowUpToBase Z D'.genericPoint ∈ (Z.support : Set Y)) :
    multAt (J.comap (blowUpToBase Z)) D'.genericPoint ≤ n := by
  classical
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  haveI : NoetherianSpace Y := Aux.noetherianSpace_of_finiteType sY
  haveI := Aux.smooth_of_isSmoothScheme' sY hY
  haveI := Aux.smooth_of_isSmoothScheme' _ hZ
  obtain ⟨W, hW, hxW, huniq, -, -⟩ := exists_component_through sY hY Z hZ ⊥ _ h
  obtain ⟨hfin, hcov⟩ := Aux.finite_and_cover_componentsOf Z.support.isClosed
  -- the open `U`: the complement of the other components
  let O : Set Y := ⋃ W' ∈ {W' | W' ∈ componentsOf (Z.support : Set Y) ∧ W' ≠ W}, W'
  have hO : IsClosed O := Set.Finite.isClosed_biUnion (hfin.subset fun _ h => h.1)
    fun W' hW' => Aux.isClosed_of_mem_componentsOf Z.support.isClosed hW'.1
  let U : Y.Opens := ⟨Oᶜ, hO.isOpen_compl⟩
  have hxU : blowUpToBase Z D'.genericPoint ∈ U := by
    change _ ∉ O
    simp only [O, Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_and]
    intro W' hW' hx
    exact hW'.2 (huniq W' hW'.1 hx)
  have hZU : ∀ y ∈ U, y ∈ (Z.support : Set Y) → y ∈ W := by
    intro y hyU hy
    obtain ⟨W', hW', hyW'⟩ := Set.mem_sUnion.1 (hcov hy)
    by_cases hne : W' = W
    · exact hne ▸ hyW'
    · exact absurd (Set.mem_iUnion₂.2 ⟨W', ⟨hW', hne⟩, hyW'⟩) hyU
  have hZUeq := coe_support_comap_opens_eq Z W U hZU hW.1.2
  have hWc : IsClosed W := Aux.isClosed_of_mem_componentsOf Z.support.isClosed hW
  -- the base change of the blow-up to `U`
  obtain ⟨hmap, H⟩ := exists_isPullback_blowUpToBase_comap U.ι Z
  have hmapOI : IsOpenImmersion hmap := by rw [← H.isoPullback_hom_snd]; infer_instance
  obtain ⟨p, hp⟩ : ∃ p : ↥(Limits.pullback (C := Scheme.{u}) U.ι (blowUpToBase Z)),
      Limits.pullback.snd U.ι (blowUpToBase Z) p = D'.genericPoint := by
    have : D'.genericPoint ∈ Set.range (Limits.pullback.snd U.ι (blowUpToBase Z)) := by
      rw [Scheme.Pullback.range_snd, Scheme.Opens.range_ι]; exact hxU
    exact this
  set η'' := H.isoPullback.inv p with hη''def
  have hη'' : hmap η'' = D'.genericPoint := by
    rw [← H.isoPullback_hom_snd, ← Scheme.Hom.comp_apply, Iso.inv_hom_id_assoc, hp]
  have hmult : multAt (J.comap (blowUpToBase Z)) D'.genericPoint =
      multAt ((J.comap U.ι).comap (blowUpToBase (Z.comap U.ι))) η'' := by
    rw [← Scheme.IdealSheafData.comap_comp, H.w, Scheme.IdealSheafData.comap_comp,
      multAt_comap_of_isOpenImmersion hmap, hη'']
  -- the smooth data on `U`
  have hZUs : Smooth ((Z.comap U.ι).subschemeι ≫ U.ι ≫ sY) := by
    have e : (Z.comap U.ι).subschemeι ≫ U.ι = (Z.comapIso U.ι).hom ≫
        Limits.pullback.snd U.ι Z.subschemeι ≫ Z.subschemeι := by
      rw [← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc, Limits.pullback.condition]
    rw [← Category.assoc, e]
    simp only [Category.assoc]
    infer_instance
  have hsb : IsSmoothBlowup (U.ι ≫ sY) (Z.comap U.ι) :=
    ⟨isSmoothScheme_of_smooth _, isSmoothScheme_of_smooth _⟩
  have hirr : IsIrreducible ((Z.comap U.ι).support : Set U) := by
    rw [hZUeq]
    exact ⟨⟨⟨_, hxU⟩, hxW⟩, hW.1.1.2.preimage U.ι.isOpenEmbedding⟩
  have hcodU : 1 ≤ codimension (⟨(Z.comap U.ι).support, hirr,
      (Z.comap U.ι).support.isClosed⟩ : IrreducibleCloseds U) := by
    have hcW := hcodim W hW
    have hnmax : ¬ IsMax (irreducibleClosure hW.1.1) := by
      intro hmax
      have h0 : Order.coheight (irreducibleClosure hW.1.1) = 0 := Order.coheight_eq_zero.2 hmax
      have h0' : codimension (irreducibleClosure hW.1.1) = 0 := h0
      rw [h0'] at hcW
      exact absurd hcW (by decide)
    obtain ⟨C', hC'⟩ := not_isMax_iff.1 hnmax
    have hζgen : closure {C'.isIrreducible.genericPoint} = (C' : Set Y) :=
      (C'.isIrreducible.isGenericPoint_genericPoint_closure : closure _ = _).trans
        C'.isClosed.closure_eq
    have hWC : W ⊆ C' := fun y hy => hC'.le (subset_closure hy)
    have hζspec : ∀ y ∈ W, C'.isIrreducible.genericPoint ⤳ y := fun y hy =>
      specializes_iff_mem_closure.2 (by rw [hζgen]; exact hWC hy)
    have hζU : C'.isIrreducible.genericPoint ∈ U :=
      (hζspec _ hxW).mem_open U.isOpen hxU
    let ζU : U := ⟨_, hζU⟩
    have hlt : (⟨(Z.comap U.ι).support, hirr, (Z.comap U.ι).support.isClosed⟩ :
        IrreducibleCloseds U) < IrreducibleCloseds.closureSingleton ζU := by
      refine lt_of_le_of_ne (fun y hy => ?_) fun heq => ?_
      · have hyW : U.ι y ∈ W := (Set.ext_iff.1 hZUeq y).1 hy
        exact specializes_iff_mem_closure.1
          ((U.ι.isOpenEmbedding.isInducing.specializes_iff (x := ζU) (y := y)).1
            (hζspec _ hyW))
      · have hmem : ζU ∈ ((Z.comap U.ι).support : Set U) := by
          have : ζU ∈ ((IrreducibleCloseds.closureSingleton ζU : IrreducibleCloseds _) :
            Set _) := subset_closure rfl
          rw [← heq] at this; exact this
        rw [hZUeq] at hmem
        have hCW : (C' : Set Y) ⊆ W := by
          rw [← hζgen]
          exact closure_minimal (Set.singleton_subset_iff.2 hmem) hWc
        refine hC'.not_ge fun y hy => ?_
        change y ∈ closure W
        exact subset_closure (hCW hy)
    have e := Order.coheight_add_one_le hlt
    change 1 ≤ Order.coheight _
    exact le_trans (le_add_self) e
  -- the generic point of the exceptional divisor of the blow-up of `U` is `η''`
  have hBU := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup (U.ι ≫ sY)
    (Z.comap U.ι) hsb).1
  haveI := hBU
  haveI : IsLocallyNoetherian (blowUp (Z.comap U.ι)) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase (Z.comap U.ι) ≫ U.ι ≫ sY)
  have := isRegularLocalRing_stalk_of_smooth_over_field
    (blowUpToBase (Z.comap U.ι) ≫ U.ι ≫ sY) η''
  have := IsRegularLocalRing.isDomain ((blowUp (Z.comap U.ι)).presheaf.stalk η'')
  have hF := isIrreducible_support_exceptionalPrimeDivisor (U.ι ≫ sY) (Z.comap U.ι) hsb hirr
    hcodU
  have hSc : IsClosed ((((Z.comap U.ι).comap (blowUpToBase (Z.comap U.ι))).support :
      Set (blowUp (Z.comap U.ι)))) := TopologicalSpace.Closeds.isClosed _
  have h1 : closure {hF.genericPoint} = ((((Z.comap U.ι).comap
      (blowUpToBase (Z.comap U.ι))).support : Set (blowUp (Z.comap U.ι)))) :=
    (hF.isGenericPoint_genericPoint_closure : closure _ = _).trans hSc.closure_eq
  have hmemS : η'' ∈ ((((Z.comap U.ι).comap (blowUpToBase (Z.comap U.ι))).support :
      Set (blowUp (Z.comap U.ι)))) := by
    simp only [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
      Set.mem_preimage]
    rw [← Scheme.Hom.comp_apply, H.w, Scheme.Hom.comp_apply, hη'']
    exact h
  have hgenF : hF.genericPoint = η'' := by
    have hspec : hF.genericPoint ⤳ η'' := specializes_iff_mem_closure.2 (h1 ▸ hmemS)
    obtain ⟨q, hq⟩ := exists_fromSpecStalk_eq_of_specializes hspec
    have hqS : (blowUp (Z.comap U.ι)).fromSpecStalk η'' q ∈ ((((Z.comap U.ι).comap
        (blowUpToBase (Z.comap U.ι))).support : Set (blowUp (Z.comap U.ι)))) := by
      rw [hq, ← h1]; exact subset_closure rfl
    rw [fromSpecStalk_mem_support_iff_stalk_le] at hqS
    obtain ⟨g, hg, hKg⟩ := exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor _
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal (Z.comap U.ι)) η''
    have hq0 : q.asIdeal ≠ ⊥ := by
      intro h0
      have : g ∈ q.asIdeal := hqS (by
        change g ∈ IdealSheafData.stalk (exceptionalIdeal (Z.comap U.ι)) η''
        rw [hKg]; exact Ideal.subset_span rfl)
      rw [h0] at this
      exact hg.ne_zero this
    have hdim : ringKrullDim ((blowUp (Z.comap U.ι)).presheaf.stalk η'') = 1 := by
      have h2 : ringKrullDim ((blowUp Z).presheaf.stalk (hmap η'')) = 1 := by
        rw [hη'']; exact D'.ringKrullDim_stalk_genericPoint_eq_one
      rw [← h2]
      exact (ringKrullDim_eq_of_ringEquiv (RingEquiv.ofBijective _
        (ConcreteCategory.bijective_of_isIso (hmap.stalkMap η'')))).symm
    have hqm : q = IsLocalRing.closedPoint _ :=
      PrimeSpectrum.ext (eq_maximalIdeal_of_ringKrullDim_eq_one hdim hq0)
    rw [← hq, hqm, Scheme.fromSpecStalk_closedPoint]
  have e := orderAlong_comap_blowUpToBase_eq (U.ι ≫ sY) (Z.comap U.ι) hsb hirr hcodU
    (J.comap U.ι)
  unfold orderAlong at e
  rw [hgenF] at e
  rw [hmult, e, multAt_comap_of_isOpenImmersion]
  -- the generic point of `Z ∩ U` is the generic point of `W`
  have hgenW : U.ι hirr.genericPoint = hW.1.1.genericPoint := by
    have hWgen : closure {hW.1.1.genericPoint} = W :=
      (hW.1.1.isGenericPoint_genericPoint_closure : closure _ = _).trans hWc.closure_eq
    have hξx : hW.1.1.genericPoint ⤳ blowUpToBase Z D'.genericPoint :=
      specializes_iff_mem_closure.2 (by rw [hWgen]; exact hxW)
    have hξU : hW.1.1.genericPoint ∈ U := hξx.mem_open U.isOpen hxU
    have hUgen : closure {hirr.genericPoint} = ((Z.comap U.ι).support : Set U) :=
      (hirr.isGenericPoint_genericPoint_closure : closure _ = _).trans
        (Z.comap U.ι).support.isClosed.closure_eq
    have hmemξ : (⟨_, hξU⟩ : U) ∈ ((Z.comap U.ι).support : Set U) := by
      rw [hZUeq]
      exact hWgen.le (subset_closure (Set.mem_singleton _))
    have s1 : U.ι hirr.genericPoint ⤳ hW.1.1.genericPoint :=
      (specializes_iff_mem_closure.2 (by rw [hUgen]; exact hmemξ)).map U.ι.continuous
    have hιW : U.ι hirr.genericPoint ∈ W := by
      have : hirr.genericPoint ∈ ((Z.comap U.ι).support : Set U) :=
        hUgen.le (subset_closure (Set.mem_singleton _))
      exact (Set.ext_iff.1 hZUeq _).1 this
    have s2 : hW.1.1.genericPoint ⤳ U.ι hirr.genericPoint :=
      specializes_iff_mem_closure.2 (by rw [hWgen]; exact hιW)
    exact (s1.antisymm s2).eq
  rw [hgenW]
  exact hJ W hW

/-- Over the centre, `π^*𝒪_X(-A)` has order `≤ m_r(E, A)` along a prime divisor of `B_Z X`. -/
private theorem multAt_comap_monomialIdeal_le (hC : C.IsMonomialData) (hk : CharZero C.k)
    {r : ℕ} (hr : 1 ≤ r)
    (D' : AlgebraicGeometry.PrimeDivisor (blowUp (C.stepCenter r)))
    (h : blowUpToBase (C.stepCenter r) D'.genericPoint ∈ ((C.stepCenter r).support : Set X)) :
    multAt ((divisorIdeal C.A).comap (blowUpToBase (C.stepCenter r))) D'.genericPoint ≤
      C.maxStratumWeight r := by
  obtain ⟨hsm, hlft, hqc, -, -, -⟩ := id hC
  haveI := hlft
  haveI := hqc
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian C.sX
  have hZsm := isSmoothScheme_subschemeι_of_hasSNCWith C.sX hsm (C.stepCenter r)
    (hasSNCWith_stepCenter C hC r)
  have hord := orderAlongEq_stepCenter C hC r
  exact multAt_comap_le_of_mem_support C.sX hsm (C.stepCenter r) hZsm
    (hasComponentsOfPositiveCodim_stepCenter C hC hr) C.monomialIdeal _
    (fun W hW => (hord W hW).le) D' h

/-- Over the centre: `π^*I_Z` has order `1` and `π^*𝒪_X(-A)` has order `m_r(E, A)` along a prime
divisor `D'` of `B_Z X` lying over `Z`. -/
private theorem multAt_comap_of_mem_stepCenter (hC : C.IsMonomialData) (hk : CharZero C.k)
    {r : ℕ} (hr : 1 ≤ r)
    (D' : AlgebraicGeometry.PrimeDivisor (blowUp (C.stepCenter r)))
    (h : blowUpToBase (C.stepCenter r) D'.genericPoint ∈ ((C.stepCenter r).support : Set X)) :
    multAt ((C.stepCenter r).comap (blowUpToBase (C.stepCenter r))) D'.genericPoint = 1 ∧
      multAt ((divisorIdeal C.A).comap (blowUpToBase (C.stepCenter r))) D'.genericPoint =
        C.maxStratumWeight r :=
  ⟨multAt_comap_stepCenter_eq_one C hC hk D' h,
    le_antisymm (multAt_comap_monomialIdeal_le C hC hk hr D' h)
      (le_multAt_comap_monomialIdeal C hC hk D' h)⟩

/-- The coefficient of `A'` along a prime divisor lying over `Z` is `m_r(E, A) - m`. -/
private theorem step_A_of_mem_stepCenter (hC : C.IsMonomialData) (hk : CharZero C.k)
    {m r : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) (hmr : m ≤ C.maxStratumWeight r)
    (D' : AlgebraicGeometry.PrimeDivisor (blowUp (C.stepCenter r)))
    (h : blowUpToBase (C.stepCenter r) D'.genericPoint ∈ ((C.stepCenter r).support : Set X)) :
    (C.step m r).A D' = C.maxStratumWeight r - m := by
  obtain ⟨h1, h2⟩ := multAt_comap_of_mem_stepCenter C hC hk hr D' h
  change (multAt ((divisorIdeal C.A).comap (blowUpToBase (C.stepCenter r)))
      D'.genericPoint).toNat - m * (multAt ((C.stepCenter r).comap
        (blowUpToBase (C.stepCenter r))) D'.genericPoint).toNat = _
  rw [h1, h2]
  simp

/-- A prime divisor contained in `Z` is an irreducible component of `Z`, and its coefficient in
`A` is `m_r(E, A)`. -/
private theorem A_eq_maxStratumWeight_of_subset (hC : C.IsMonomialData) {r : ℕ} (hr : 1 ≤ r)
    (D : AlgebraicGeometry.PrimeDivisor X)
    (hDZ : (D.support : Set X) ⊆ ((C.stepCenter r).support : Set X)) :
    C.A D = C.maxStratumWeight r := by
  obtain ⟨-, hlft, hqc, -, -, -⟩ := id hC
  haveI := hlft
  haveI := hqc
  haveI : NoetherianSpace X := Aux.noetherianSpace_of_finiteType C.sX
  have hDirr : IsIrreducible (D.support : Set X) := by
    rw [Aux.support_eq_closure_genericPoint]; exact isIrreducible_singleton.closure
  have hZc := (C.stepCenter r).support.isClosed
  obtain ⟨hfin, hcov⟩ := Aux.finite_and_cover_componentsOf hZc
  obtain ⟨W, hW, hDW⟩ := isIrreducible_iff_sUnion_isClosed.mp hDirr hfin.toFinset
    (fun V hV => Aux.isClosed_of_mem_componentsOf hZc (hfin.mem_toFinset.1 hV))
    (by rw [Set.Finite.coe_toFinset]; exact hDZ.trans hcov)
  rw [Set.Finite.mem_toFinset] at hW
  have hWc : IsClosed W := Aux.isClosed_of_mem_componentsOf hZc hW
  have hcodim := hasComponentsOfPositiveCodim_stepCenter C hC hr W hW
  have hDWeq : (D.support : Set X) = W := by
    refine hDW.antisymm ?_
    by_contra hne
    have hlt : IrreducibleCloseds.closureSingleton D.genericPoint < irreducibleClosure hW.1.1 := by
      refine lt_of_le_of_ne (fun y hy => ?_) fun heq => hne ?_
      · change y ∈ closure W
        rw [hWc.closure_eq]
        have : closure {D.genericPoint} ⊆ W := by
          rw [← Aux.support_eq_closure_genericPoint]; exact hDW
        exact this hy
      · have := congrArg (fun W : IrreducibleCloseds X => (W : Set X)) heq
        change closure {D.genericPoint} = closure W at this
        rw [hWc.closure_eq, ← Aux.support_eq_closure_genericPoint] at this
        rw [this]
    have e := Order.coheight_add_one_le hlt
    have h2 : codimension (irreducibleClosure hW.1.1) + 1 ≤
        codimension (IrreducibleCloseds.closureSingleton D.genericPoint) := e
    have h1 : codimension (IrreducibleCloseds.closureSingleton D.genericPoint) = 1 :=
      D.codimension_one
    rw [h1] at h2
    have : (1 : ℕ∞) + 1 ≤ 1 := le_trans (by gcongr) h2
    exact absurd this (by decide)
  subst hDWeq
  have hord := orderAlongEq_stepCenter C hC r _ hW
  have hgen : hW.1.1.genericPoint = D.genericPoint := by
    have h1 := hW.1.1.isGenericPoint_genericPoint_closure
    rw [hWc.closure_eq] at h1
    have h2 : IsGenericPoint D.genericPoint (D.support : Set X) := by
      rw [Aux.support_eq_closure_genericPoint]; exact isGenericPoint_closure
    exact h1.eq h2
  unfold orderAlong at hord
  rw [hgen, multAt_monomialIdeal_genericPoint C hC] at hord
  exact_mod_cast hord

open Classical in
/-- The coefficient of `A'` along the transform of a prime divisor `D` of `X`. -/
private theorem step_A_of_genericPoint (hC : C.IsMonomialData) (hk : CharZero C.k)
    {m r : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) (hmr : m ≤ C.maxStratumWeight r)
    (D : AlgebraicGeometry.PrimeDivisor X)
    (D' : AlgebraicGeometry.PrimeDivisor (blowUp (C.stepCenter r)))
    (h : blowUpToBase (C.stepCenter r) D'.genericPoint = D.genericPoint) :
    (C.step m r).A D' =
      if D.support ⊆ ((C.stepCenter r).support : Set X) then C.A D - m else C.A D := by
  have hηD : D.genericPoint ∈ (D.support : Set X) := by
    rw [Aux.support_eq_closure_genericPoint]; exact subset_closure rfl
  by_cases hDZ : (D.support : Set X) ⊆ ((C.stepCenter r).support : Set X)
  · rw [if_pos hDZ, step_A_of_mem_stepCenter C hC hk hr hm hmr D' (h ▸ hDZ hηD),
      A_eq_maxStratumWeight_of_subset C hC hr D hDZ]
  · rw [if_neg hDZ]
    have hx : blowUpToBase (C.stepCenter r) D'.genericPoint ∉
        ((C.stepCenter r).support : Set X) := by
      rw [h]
      intro hη
      apply hDZ
      rw [Aux.support_eq_closure_genericPoint]
      exact closure_minimal (Set.singleton_subset_iff.2 hη) (C.stepCenter r).support.isClosed
    have hZ0 : multAt ((C.stepCenter r).comap (blowUpToBase (C.stepCenter r)))
        D'.genericPoint = 0 := by
      by_contra h
      exact hx (mem_support_of_mem_support_comap _ _ (mem_support_of_multAt_ne_zero _ _ h))
    have hI : multAt ((divisorIdeal C.A).comap (blowUpToBase (C.stepCenter r)))
        D'.genericPoint = C.A D := by
      rw [multAt, IdealSheafData.stalk_comap, idealOrder_map_of_bijective _
        (bijective_stalkMap_of_notMem _ _ hx)]
      change multAt C.monomialIdeal _ = _
      rw [h, multAt_monomialIdeal_genericPoint C hC]
    change (multAt ((divisorIdeal C.A).comap (blowUpToBase (C.stepCenter r)))
        D'.genericPoint).toNat - m * (multAt ((C.stepCenter r).comap
          (blowUpToBase (C.stepCenter r))) D'.genericPoint).toNat = _
    rw [hZ0, hI]
    simp

/-- For `r ≥ 2` no component of `Z` is a component of `Supp E`: such a component would be a
component of two distinct members `E^{j_1}, E^{j_2}`, whose local equations at its generic point
are two distinct members of a regular system of parameters, hence generate distinct ideals. -/
private theorem notMem_componentsOf_support_of_mem_componentsOf_stepCenter
    (hC : C.IsMonomialData) (hk : CharZero C.k)
    {m r : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) (hmr : m ≤ C.maxStratumWeight r)
    {W : Set X} (hW : W ∈ componentsOf ((C.stepCenter r).support : Set X)) :
    W ∉ componentsOf C.E.support := by
  intro hWE
  obtain ⟨x, hxW⟩ := hW.1.1.nonempty
  have hZsub := stepCenter_support_subset_stratum C r
  have hcard := card_stepIndex_of_mem_stepCenter C (hW.1.2 hxW)
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (show 1 < (C.stepIndex r).card by omega)
  have hmem : ∀ j ∈ C.stepIndex r, W ⊆ ((C.E.E j).support : Set X) := fun j hj y hy =>
    Set.mem_iInter₂.1 (hZsub (hW.1.2 hy)) j hj
  have hcomp : ∀ j ∈ C.stepIndex r, W ∈ componentsOf ((C.E.E j).support : Set X) :=
    fun j hj => ⟨⟨hW.1.1, hmem j hj⟩, fun W' hW' hle => hWE.2
      ⟨hW'.1, hW'.2.trans (Set.subset_iUnion (fun i => ((C.E.E i).support : Set X)) j)⟩ hle⟩
  exact false_of_mem_componentsOf_of_ne C hC hab (hcomp a ha) (hcomp b hb) hxW

/-- For `r ≥ 2` the last member of `E'` is `π⁻¹(Z)`. -/
private theorem support_last_totalTransform (hC : C.IsMonomialData) (hk : CharZero C.k)
    {m r : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) (hmr : m ≤ C.maxStratumWeight r) :
    (((C.E.totalTransform (C.stepCenter r)).E (Fin.last C.E.s)).support :
        Set (blowUp (C.stepCenter r))) =
      blowUpToBase (C.stepCenter r) ⁻¹' ((C.stepCenter r).support : Set X) := by
  obtain ⟨-, hlft, hqc, -, -, -⟩ := id hC
  haveI := hlft
  haveI := hqc
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian C.sX
  haveI : NoetherianSpace X := Aux.noetherianSpace_of_finiteType C.sX
  set Z := C.stepCenter r
  have hcov := (Aux.finite_and_cover_componentsOf (Z.support.isClosed)).2
  have hS : totalTransformSet C.E Z (Fin.last C.E.s) = blowUpToBase Z ⁻¹' (Z.support : Set X) := by
    simp only [totalTransformSet, Fin.snoc_last]
    ext x'
    simp only [Set.mem_iUnion, Set.mem_preimage, exists_prop]
    constructor
    · rintro ⟨W, hW, -, hx⟩
      exact hW.1.2 hx
    · intro hx
      obtain ⟨W, hW, hxW⟩ := Set.mem_sUnion.1 (hcov hx)
      exact ⟨W, hW,
        notMem_componentsOf_support_of_mem_componentsOf_stepCenter C hC hk hr hm hmr hW, hxW⟩
  rw [totalTransform_E_eq, Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure,
    hS,
    (Z.support.isClosed.preimage (blowUpToBase Z).continuous).closure_eq]

/-! ### Ideal sheaves of divisors on a smooth scheme are determined by their orders -/

section DivisorialIdeals

open IsLocalRing

/-- In a discrete valuation ring the order of `(x)` is the valuation of `x`. -/
private theorem idealOrder_span_eq_addVal {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {x : R} (hx : x ≠ 0) :
    idealOrder (Ideal.span {x}) = IsDiscreteValuationRing.addVal R x := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  rw [IsDiscreteValuationRing.addVal_def _ u hϖ n rfl]
  have hm : maximalIdeal R = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have key : ∀ j : ℕ, Ideal.span {(u : R) * ϖ ^ n} ≤ maximalIdeal R ^ j ↔ j ≤ n := by
    intro j
    rw [hm, Ideal.span_singleton_pow, Ideal.span_singleton_le_span_singleton,
      Units.dvd_mul_left]
    exact _root_.pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit
  refine le_antisymm (iSup₂_le fun j hj => by exact_mod_cast (key j).1 hj) ?_
  exact le_iSup₂_of_le (f := fun (j : ℕ) (_ : Ideal.span {(u : R) * ϖ ^ n} ≤
    maximalIdeal R ^ j) => (j : ℕ∞)) n ((key n).2 le_rfl) le_rfl

/-- A regular local ring of dimension one is a discrete valuation ring. -/
private theorem isDiscreteValuationRing_of_ringKrullDim_eq_one {R : Type*} [CommRing R]
    [IsRegularLocalRing R] [IsDomain R] (h : ringKrullDim R = 1) : IsDiscreteValuationRing R := by
  haveI := IsRegularLocalRing.uniqueFactorizationMonoid R
  have hnf : ¬ IsField R := fun hf => by
    have := ringKrullDim_eq_zero_of_isField hf
    rw [h] at this
    exact absurd this (by decide)
  have e := (IsDiscreteValuationRing.TFAE R hnf).out 1 4
  refine e.2 ⟨inferInstance, maximalIdeal R,
    ⟨fun h0 => hnf ((isField_iff_maximalIdeal_eq).2 h0), inferInstance⟩, fun P hP => ?_⟩
  haveI := hP.2
  exact eq_maximalIdeal_of_ringKrullDim_eq_one h hP.1

/-- In the localization `S` of a domain at a principal prime `(p)`, the maximal ideal is
`(p)` and is nonzero. -/
private theorem maximalIdeal_eq_span_of_isLocalization {R S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [IsLocalRing S] [Algebra R S] {p : R} (hp : Prime p)
    [(Ideal.span {p}).IsPrime] [IsLocalization.AtPrime S (Ideal.span {p})] :
    maximalIdeal S = Ideal.span {algebraMap R S p} ∧ maximalIdeal S ≠ ⊥ := by
  have hm : maximalIdeal S = Ideal.span {algebraMap R S p} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {p}) S, Ideal.map_span,
      Set.image_singleton]
  refine ⟨hm, ?_⟩
  rw [hm, Ne, Ideal.span_singleton_eq_bot]
  intro h0
  obtain ⟨⟨c, hc⟩, hc0⟩ := (IsLocalization.map_eq_zero_iff (Ideal.span {p}).primeCompl S p).1 h0
  have : c = 0 := (mul_eq_zero.1 hc0).resolve_right hp.ne_zero
  exact hc (by rw [this]; exact Ideal.zero_mem _)

/-- In the localization `S` of a UFD at a principal prime `(p)`, the order of `(f)` is the
multiplicity of `p` in `f`. -/
private theorem idealOrder_span_algebraMap_eq_emultiplicity {R S : Type*} [CommRing R]
    [IsDomain R] [UniqueFactorizationMonoid R] [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    [IsDomain S] [Algebra R S] {p : R} (hp : Prime p) [(Ideal.span {p}).IsPrime]
    [IsLocalization.AtPrime S (Ideal.span {p})] {f : R} (hf : f ≠ 0) :
    idealOrder (Ideal.span {algebraMap R S f}) = emultiplicity p f := by
  have hfin := FiniteMultiplicity.of_prime_left hp hf
  obtain ⟨h, hfh, hndvd⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  rw [hfin.emultiplicity_eq_multiplicity]
  generalize multiplicity p f = e at hfh ⊢
  have hunit : IsUnit (algebraMap R S h) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff S _ h).2 (by
      change h ∉ Ideal.span {p}
      rwa [Ideal.mem_span_singleton])
  obtain ⟨hm, hm0⟩ := maximalIdeal_eq_span_of_isLocalization (S := S) hp
  have hspan : Ideal.span {algebraMap R S f} = maximalIdeal S ^ e := by
    rw [hfh, map_mul, map_pow, ← Ideal.span_singleton_mul_span_singleton,
      Ideal.span_singleton_eq_top.2 hunit, Ideal.mul_top, ← Ideal.span_singleton_pow, ← hm]
  rw [hspan]
  exact idealOrder_maximalIdeal_pow hm0 _

/-- On a scheme with regular local rings, the generization of `x` cut out by a prime element `p`
of `𝒪_{Y,x}` has coheight one, and there the order of an invertible ideal with local generator
`f` is the multiplicity of `p` in `f`. -/
private theorem coheight_and_multAt_fromSpecStalk {Y : Scheme.{u}}
    (hreg : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) (x : Y)
    {p : Y.presheaf.stalk x} (hp : Prime p) (q : PrimeSpectrum (Y.presheaf.stalk x))
    (hq : q.asIdeal = Ideal.span {p}) :
    Order.coheight (Y.fromSpecStalk x q) = 1 ∧
      ∀ (J : Y.IdealSheafData) (f : Y.presheaf.stalk x), IdealSheafData.stalk J x =
        Ideal.span {f} → f ≠ 0 → multAt J (Y.fromSpecStalk x q) = emultiplicity p f := by
  obtain ⟨I, hI⟩ := q
  simp only at hq
  subst hq
  have hyx := fromSpecStalk_specializes_self x ⟨Ideal.span {p}, hI⟩
  letI : Algebra (Y.presheaf.stalk x) (Y.presheaf.stalk (Y.fromSpecStalk x ⟨_, hI⟩)) :=
    (Y.presheaf.stalkSpecializes hyx).hom.toAlgebra
  haveI := Stacks.Chow.isLocalization_stalk_of_specializes hyx ⟨Ideal.span {p}, hI⟩ rfl
  haveI := hreg x
  haveI := hreg (Y.fromSpecStalk x ⟨_, hI⟩)
  haveI := IsRegularLocalRing.isDomain (Y.presheaf.stalk x)
  haveI := IsRegularLocalRing.isDomain (Y.presheaf.stalk (Y.fromSpecStalk x ⟨_, hI⟩))
  haveI := IsRegularLocalRing.uniqueFactorizationMonoid (Y.presheaf.stalk x)
  haveI : IsLocalization.AtPrime (Y.presheaf.stalk (Y.fromSpecStalk x ⟨_, hI⟩))
      (Ideal.span {p}) := by assumption
  obtain ⟨hm, hm0⟩ := maximalIdeal_eq_span_of_isLocalization
    (S := Y.presheaf.stalk (Y.fromSpecStalk x ⟨_, hI⟩)) hp
  have hnf : ¬ IsField (Y.presheaf.stalk (Y.fromSpecStalk x ⟨_, hI⟩)) :=
    fun hf => hm0 ((isField_iff_maximalIdeal_eq).1 hf)
  have hdvr : IsDiscreteValuationRing (Y.presheaf.stalk (Y.fromSpecStalk x ⟨_, hI⟩)) :=
    ((IsDiscreteValuationRing.TFAE _ hnf).out 1 5).2 (show (maximalIdeal _).IsPrincipal from
      ⟨⟨_, hm⟩⟩)
  refine ⟨?_, fun J f hJ hf => ?_⟩
  · have h1 := ringKrullDim_stalk_eq_coheight (Y.fromSpecStalk x ⟨_, hI⟩)
    rw [IsDiscreteValuationRing.ringKrullDim_eq_one] at h1
    exact_mod_cast h1.symm
  · rw [multAt, Aux.stalk_eq_map_stalkSpecializes J hyx, hJ, Ideal.map_span, Set.image_singleton]
    exact idealOrder_span_algebraMap_eq_emultiplicity hp hf

/-- **Invertible ideals on a scheme with regular local rings are determined by their orders along
prime divisors.** The local rings are factorial, and the multiplicity of a prime element `p` in a
local generator is the order along the prime divisor with generic point `(p)`. -/
private theorem eq_of_forall_multAt_genericPoint_eq {Y : Scheme.{u}}
    (hreg : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) (J₁ J₂ : Y.IdealSheafData)
    (h₁ : Stacks.Divisors.IsEffectiveCartierDivisor J₁)
    (h₂ : Stacks.Divisors.IsEffectiveCartierDivisor J₂)
    (h : ∀ D : AlgebraicGeometry.PrimeDivisor Y,
      multAt J₁ D.genericPoint = multAt J₂ D.genericPoint) : J₁ = J₂ := by
  refine AlgebraicGeometry.IdealSheafData.eq_of_stalk_eq _ _ fun x => ?_
  haveI := hreg x
  haveI := IsRegularLocalRing.isDomain (Y.presheaf.stalk x)
  haveI := IsRegularLocalRing.uniqueFactorizationMonoid (Y.presheaf.stalk x)
  obtain ⟨f, hf, hJf⟩ := exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor _ h₁ x
  obtain ⟨g, hg, hJg⟩ := exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor _ h₂ x
  have key : ∀ p, Prime p → emultiplicity p f = emultiplicity p g := fun p hp => by
    obtain ⟨hcoh, hmult⟩ := coheight_and_multAt_fromSpecStalk hreg x hp
      ⟨Ideal.span {p}, (Ideal.span_singleton_prime hp.ne_zero).2 hp⟩ rfl
    have := h (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh)
    rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne] at this
    rw [← hmult J₁ f hJf hf.ne_zero, ← hmult J₂ g hJg hg.ne_zero, this]
  rw [hJf, hJg, Ideal.span_singleton_eq_span_singleton]
  exact associated_of_dvd_dvd
    ((UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hf.ne_zero).2 fun p hp => (key p hp).le)
    ((UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hg.ne_zero).2 fun p hp => (key p hp).ge)

end DivisorialIdeals

/-- The ideal sheaf `𝒪_Y(-A)` of an effective divisor on a smooth scheme is invertible. -/
private theorem isEffectiveCartierDivisor_divisorIdeal {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (hY : MMP.Mori.IsSmoothScheme sY)
    (A : AlgebraicGeometry.PrimeDivisor Y → ℕ) (hA : (Function.support A).Finite) :
    Stacks.Divisors.IsEffectiveCartierDivisor (divisorIdeal A) := by
  classical
  have hM : divisorIdeal A = ∏ D ∈ hA.toFinset, D.idealSheaf ^ A D := by
    unfold divisorIdeal
    refine finprod_eq_prod_of_mulSupport_subset _ fun D hD => ?_
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    intro h0
    exact hD (by show D.idealSheaf ^ A D = 1; rw [h0, pow_zero])
  rw [hM]
  exact Stacks.Divisors.isEffectiveCartierDivisor_prod _ _ _
    fun D _ => Aux.isEffectiveCartierDivisor_idealSheaf sY hY D

/-- `π⁻¹_*(I_{E,A}, m) = 𝒪(mF) π^*𝒪(-A) = 𝒪(-(π^*A - mF))`: both sides are invertible ideals on
the smooth scheme `B_Z X`, and they have the same order `ord_{D'}(π^*𝒪(-A)) - m·ord_{D'}(F)` along
every prime divisor `D'`, computed in the discrete valuation ring at its generic point. -/
private theorem birationalTransform_eq (hC : C.IsMonomialData) (hk : CharZero C.k)
    {m r : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) (hmr : m ≤ C.maxStratumWeight r) :
    (MarkedIdeal.birationalTransform (C.stepCenter r) ⟨C.monomialIdeal, m⟩).I =
      (C.step m r).monomialIdeal := by
  obtain ⟨hsm, hlft, hqc, -, hfin, -⟩ := id hC
  haveI := hlft
  haveI := hqc
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian C.sX
  haveI := Aux.smooth_of_isSmoothScheme' C.sX hsm
  have hZsm := isSmoothScheme_subschemeι_of_hasSNCWith C.sX hsm (C.stepCenter r)
    (hasSNCWith_stepCenter C hC r)
  obtain ⟨hB, -⟩ := smooth_blowUp_stepCenter C hC hk r
  haveI := hB
  haveI : LocallyOfFiniteType (blowUpToBase (C.stepCenter r) ≫ C.sX) := inferInstance
  haveI : IsLocallyNoetherian (blowUp (C.stepCenter r)) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase (C.stepCenter r) ≫ C.sX)
  have hreg : ∀ y, IsRegularLocalRing ((blowUp (C.stepCenter r)).presheaf.stalk y) := fun y =>
    isRegularLocalRing_stalk_of_smooth_over_field (blowUpToBase (C.stepCenter r) ≫ C.sX) y
  have hord := orderAlongEq_stepCenter C hC r
  have hmul := MarkedIdeal.birationalTransform_mul_eq C.sX hsm (C.stepCenter r) hZsm
    (hasComponentsOfPositiveCodim_stepCenter C hC hr) ⟨C.monomialIdeal, m⟩
    (fun W hW => by
      change (m : ℕ∞) ≤ _
      rw [hord W hW]; exact_mod_cast hmr)
  have hIcart := isEffectiveCartierDivisor_divisorIdeal C.sX hsm C.A hfin
  -- local generators
  have hloc : ∀ y : blowUp (C.stepCenter r), ∃ t g h : (blowUp (C.stepCenter r)).presheaf.stalk y,
      IdealSheafData.stalk (MarkedIdeal.birationalTransform (C.stepCenter r)
        ⟨C.monomialIdeal, m⟩).I y = Ideal.span {t} ∧
      IdealSheafData.stalk ((C.stepCenter r).comap (blowUpToBase (C.stepCenter r))) y =
        Ideal.span {g} ∧
      IdealSheafData.stalk ((divisorIdeal C.A).comap (blowUpToBase (C.stepCenter r))) y =
        Ideal.span {h} ∧ t * g ^ m = h ∧ t ≠ 0 ∧ g ≠ 0 := by
    intro y
    haveI := hreg y
    haveI := IsRegularLocalRing.isDomain ((blowUp (C.stepCenter r)).presheaf.stalk y)
    haveI := isRegularLocalRing_stalk_of_smooth_over_field C.sX (blowUpToBase (C.stepCenter r) y)
    haveI := IsRegularLocalRing.isDomain (X.presheaf.stalk (blowUpToBase (C.stepCenter r) y))
    obtain ⟨g, hg, hFg⟩ := exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor _
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal (C.stepCenter r)) y
    obtain ⟨f, hf, hIf⟩ := exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor _ hIcart
      (blowUpToBase (C.stepCenter r) y)
    have hIh : IdealSheafData.stalk ((divisorIdeal C.A).comap (blowUpToBase (C.stepCenter r))) y =
        Ideal.span {((blowUpToBase (C.stepCenter r)).stalkMap y).hom f} := by
      rw [IdealSheafData.stalk_comap, hIf, Ideal.map_span, Set.image_singleton]
    have hh0 : ((blowUpToBase (C.stepCenter r)).stalkMap y).hom f ≠ 0 := fun h0 =>
      hf.ne_zero (injective_stalkMap_blowUpToBase (C.stepCenter r) y (by rw [h0, map_zero]))
    have hstalk := congrArg (fun J => IdealSheafData.stalk J y) hmul
    simp only at hstalk
    rw [IdealSheafData.stalk_mul, IdealSheafData.stalk_pow] at hstalk
    change _ * IdealSheafData.stalk (exceptionalIdeal (C.stepCenter r)) y ^ m = _ at hstalk
    rw [hFg, Ideal.span_singleton_pow] at hstalk
    change _ = IdealSheafData.stalk ((divisorIdeal C.A).comap _) y at hstalk
    rw [hIh] at hstalk
    have hmem : ((blowUpToBase (C.stepCenter r)).stalkMap y).hom f ∈
        Ideal.span {g ^ m} * IdealSheafData.stalk (MarkedIdeal.birationalTransform
          (C.stepCenter r) ⟨C.monomialIdeal, m⟩).I y := by
      rw [mul_comm, hstalk]; exact Ideal.mem_span_singleton_self _
    obtain ⟨t, htT, hth⟩ := Ideal.mem_span_singleton_mul.1 hmem
    refine ⟨t, g, _, ?_, hFg, hIh, by rw [← hth, mul_comm], ?_, hg.ne_zero⟩
    · refine le_antisymm (fun a ha => ?_) ?_
      · have : a * g ^ m ∈ Ideal.span {((blowUpToBase (C.stepCenter r)).stalkMap y).hom f} := by
          rw [← hstalk]; exact Ideal.mul_mem_mul ha (Ideal.mem_span_singleton_self _)
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 this
        rw [← hth] at hc
        have : a = c * t := mul_right_cancel₀ (pow_ne_zero m hg.ne_zero) (by rw [← hc]; ring)
        exact Ideal.mem_span_singleton'.2 ⟨c, this.symm⟩
      · rw [Ideal.span_le, Set.singleton_subset_iff]; exact htT
    · rintro rfl; apply hh0; rw [← hth, mul_zero]
  have hTcart : Stacks.Divisors.IsEffectiveCartierDivisor
      (MarkedIdeal.birationalTransform (C.stepCenter r) ⟨C.monomialIdeal, m⟩).I := by
    refine Stacks.Divisors.isEffectiveCartierDivisor_of_stalk_isPrincipal_nonZeroDivisor _
      fun y _ => ?_
    obtain ⟨t, -, -, ht, -, -, -, ht0, -⟩ := hloc y
    haveI := hreg y
    haveI := IsRegularLocalRing.isDomain ((blowUp (C.stepCenter r)).presheaf.stalk y)
    exact ⟨t, mem_nonZeroDivisors_of_ne_zero ht0, ht⟩
  have hAcart : Stacks.Divisors.IsEffectiveCartierDivisor (C.step m r).monomialIdeal :=
    isEffectiveCartierDivisor_divisorIdeal (blowUpToBase (C.stepCenter r) ≫ C.sX)
      (isSmoothScheme_of_smooth _) _ (finite_support_step_A C hC hk hr hm hmr)
  refine eq_of_forall_multAt_genericPoint_eq hreg _ _ hTcart hAcart fun D' => ?_
  rw [multAt_monomialIdeal_genericPoint (C.step m r)
    (isMonomialData_step C hC hk hr hm hmr (hasSNCWith_stepCenter C hC r)) D']
  obtain ⟨t, g, h, ht, hg, hh, hthg, ht0, hg0⟩ := hloc D'.genericPoint
  haveI := hreg D'.genericPoint
  haveI := IsRegularLocalRing.isDomain ((blowUp (C.stepCenter r)).presheaf.stalk D'.genericPoint)
  haveI := isDiscreteValuationRing_of_ringKrullDim_eq_one
    D'.ringKrullDim_stalk_genericPoint_eq_one
  have hh0 : h ≠ 0 := by rw [← hthg]; exact mul_ne_zero ht0 (pow_ne_zero _ hg0)
  change multAt _ _ = (((multAt ((divisorIdeal C.A).comap (blowUpToBase (C.stepCenter r)))
      D'.genericPoint).toNat - m * (multAt ((C.stepCenter r).comap
        (blowUpToBase (C.stepCenter r))) D'.genericPoint).toNat : ℕ) : ℕ∞)
  rw [multAt, multAt, multAt, ht, hg, hh, idealOrder_span_eq_addVal ht0,
    idealOrder_span_eq_addVal hg0, idealOrder_span_eq_addVal hh0, ← hthg,
    IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow]
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1
    ((IsDiscreteValuationRing.addVal_eq_top_iff).not.2 ht0)
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.1
    ((IsDiscreteValuationRing.addVal_eq_top_iff).not.2 hg0)
  rw [← ha, ← hb]
  simp only [nsmul_eq_mul, ← Nat.cast_mul, ← Nat.cast_add, ENat.toNat_coe]
  rw [Nat.add_sub_cancel]

end MMP.Proofs.lem_kr3e_monomial_stratum_blowup

namespace MMP.Resolution

namespace MonomialData

open MMP.Proofs.lem_kr3e_monomial_stratum_blowup in
open Classical in
/-- **The Step-3.`r` blow-up of monomial data** (Kollár 3.111, Steps 3.1, 3.2, 3.`r`). For
monomial data `C = (X, E, A)` over a field of characteristic `0`, `1 ≤ r` and
`1 ≤ m ≤ m_r(E, A)`, with `Z = C.stepCenter r` and `π : B_ZX → X`:
* `π` is a smooth blow-up of the marked triple `(X, I_{E,A}, m, E)` and
  `ord_Z I_{E,A} = m_r(E, A)`;
* `π⁻¹_*(I_{E,A}, m) = I_{E',A'}` for `(X', E', A') = C.step m r`, and these are monomial data;
* a prime divisor `D'` of `X'` that is the birational transform of a prime divisor `D ⊄ Z` of `X`
  has coefficient `a_D`, one that is the transform of a `D ⊆ Z` has coefficient `a_D - m`, and
  every prime divisor of `X'` lying over `Z` has coefficient `m_r(E, A) - m`;
* for `r ≥ 2`, the last member `F` of `E'` is supported on `π⁻¹(Z)`. -/
@[mmp "lem_kr3e_monomial_stratum_blowup"]
public theorem step_spec {X : Scheme.{u}} (C : MonomialData X) (hC : C.IsMonomialData)
    (hk : CharZero C.k)
    {m r : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) (hmr : m ≤ C.maxStratumWeight r) :
    IsSmoothBlowupOfMarkedTriple
        { X := X, I := C.monomialIdeal, E := C.E, k := C.k, sX := C.sX, m := m }
        (C.stepCenter r) ∧
      OrderAlongEq C.monomialIdeal ((C.stepCenter r).support : Set X)
        (C.maxStratumWeight r : ℕ∞) ∧
      (MarkedIdeal.birationalTransform (C.stepCenter r) ⟨C.monomialIdeal, m⟩).I =
        (C.step m r).monomialIdeal ∧
      (C.step m r).IsMonomialData ∧
      (∀ (D : AlgebraicGeometry.PrimeDivisor X)
          (D' : AlgebraicGeometry.PrimeDivisor (blowUp (C.stepCenter r))),
          blowUpToBase (C.stepCenter r) D'.genericPoint = D.genericPoint →
          (C.step m r).A D' =
            if D.support ⊆ ((C.stepCenter r).support : Set X) then C.A D - m else C.A D) ∧
      (∀ D' : AlgebraicGeometry.PrimeDivisor (blowUp (C.stepCenter r)),
          blowUpToBase (C.stepCenter r) D'.genericPoint ∈
            ((C.stepCenter r).support : Set X) →
          (C.step m r).A D' = C.maxStratumWeight r - m) ∧
      (2 ≤ r →
        (((C.E.totalTransform (C.stepCenter r)).E (Fin.last C.E.s)).support :
            Set (blowUp (C.stepCenter r))) =
          blowUpToBase (C.stepCenter r) ⁻¹' ((C.stepCenter r).support : Set X)) := by
  have hord := orderAlongEq_stepCenter C hC r
  have hcodim := hasComponentsOfPositiveCodim_stepCenter C hC hr
  have hsnc := hasSNCWith_stepCenter C hC r
  refine ⟨⟨hcodim, hsnc, fun W hW => ?_⟩, hord, birationalTransform_eq C hC hk hr hm hmr,
    isMonomialData_step C hC hk hr hm hmr hsnc, step_A_of_genericPoint C hC hk hr hm hmr,
    step_A_of_mem_stepCenter C hC hk hr hm hmr,
    fun h2 => support_last_totalTransform C hC hk h2 hm hmr⟩
  change (m : ℕ∞) ≤ orderAlong C.monomialIdeal hW.1.1
  rw [hord W hW]
  exact_mod_cast hmr

end MonomialData

end MMP.Resolution

end

/-!
### The Step-3.`r` blow-up lowers `(m_r, n_r)` lexicographically

Let `(X, E, A)` be monomial data over a field `k` of characteristic `0`, `m ≥ 1` and `r ≥ 2`,
such that `m_t(E, A) < m` for every `1 ≤ t < r` and `m_r(E, A) ≥ m`. Let `(X', E', A')` be the
result of the Step-3.`r` blow-up, the blow-up of the union `Z` of the pieces of `E^{J_*}` of
maximal weight `σ_{J_*} = m_r(E, A)`. Away from the exceptional divisor `F` nothing changes; the
pieces of `E^{J_*}` of weight `m_r(E, A)` blown up disappear, an `r`-fold piece not involving `F`
keeps its weight, and an `r`-fold piece involving `F` has weight
`σ(x) + m_r(E, A) - m ≤ m_{r-1}(E, A) + m_r(E, A) - m < m_r(E, A)`. Hence the pair
`(m_r, n_r)` of the maximal `r`-fold weight and the number of `r`-fold pieces attaining it
strictly decreases in the lexicographic order on `ℕ × ℕ`.

### Main results

* `MMP.Resolution.MonomialData.toLex_maxStratumWeight_maxStratumCount_step_lt`:
  `(m_r(E', A'), n_r(E', A')) <_lex (m_r(E, A), n_r(E, A))`.

### References

* [J. Kollár, *Lectures on resolution of singularities*, 3.111, Steps 3.2, 3.`r`]
-/

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Resolution

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Proofs.lem_kr3e_monomial_step_decreases

/-- A coefficient `a_j(x)` is at most the sum of all coefficients of `A`. -/
private theorem coeffAt_le_finsum {X : Scheme.{u}} (C : MonomialData X)
    (hfin : (Function.support C.A).Finite) (j : Fin C.E.s) (x : X) :
    C.coeffAt j x ≤ ∑ᶠ D, C.A D := by
  classical
  unfold MonomialData.coeffAt
  refine finsum_le_finsum' (hfin.subset fun D hD => ?_) hfin fun D => ?_
  · by_contra h
    exact hD (by simp [Function.notMem_support.1 h])
  · dsimp only
    split_ifs <;> simp

private theorem bddAbove_range_of_le {α : Type*} [Preorder α] {ι : Sort*} {f : ι → α} {B : α}
    (h : ∀ i, f i ≤ B) :
    BddAbove (Set.range f) :=
  ⟨B, Set.forall_mem_range.2 h⟩

/-- Every weight `σ_J(x)`, `|J| = r`, is at most `m_r(E, A)`. -/
private theorem stratumWeight_le_maxStratumWeight {X : Scheme.{u}} (C : MonomialData X)
    (hfin : (Function.support C.A).Finite) {r : ℕ} {J : Finset (Fin C.E.s)} (hJ : J.card = r)
    {x : X} (hx : x ∈ C.stratum J) : C.stratumWeight J x ≤ C.maxStratumWeight r := by
  set B := r * ∑ᶠ D, C.A D
  have hB : ∀ J' : Finset (Fin C.E.s), J'.card = r → ∀ x', C.stratumWeight J' x' ≤ B := by
    intro J' hJ' x'
    unfold MonomialData.stratumWeight
    calc ∑ j ∈ J', C.coeffAt j x' ≤ ∑ _j ∈ J', ∑ᶠ D, C.A D :=
          Finset.sum_le_sum fun j _ => coeffAt_le_finsum C hfin j x'
      _ = B := by rw [Finset.sum_const, hJ', smul_eq_mul]
  unfold MonomialData.maxStratumWeight
  exact le_ciSup_of_le (bddAbove_range_of_le fun J' => ciSup_le' fun hJ' => ciSup_le' fun x' =>
      ciSup_le' fun _ => hB J' hJ' x') J
    (le_ciSup_of_le (bddAbove_range_of_le fun hJ' => ciSup_le' fun x' => ciSup_le' fun _ =>
      hB J hJ' x') hJ
    (le_ciSup_of_le (bddAbove_range_of_le fun x' => ciSup_le' fun _ => hB J hJ x') x
    (le_ciSup_of_le (bddAbove_range_of_le fun _ => hB J hJ x) hx le_rfl)))

/-- The support of the birational transform `π⁻¹_*E^i` is the closure of the preimage of the
part of `E^i` off the components of codimension `≥ 2` of the centre. -/
private theorem coe_support_step_castSucc {X : Scheme.{u}} (C : MonomialData X) (m r : ℕ)
    (i : Fin C.E.s) :
    (((C.step m r).E.E (Fin.castSucc i)).support : Set (blowUp (C.stepCenter r))) =
      closure (blowUpToBase (C.stepCenter r) ⁻¹' ((C.E.E i).support \
        componentsOfCodimAtLeastTwo ((C.stepCenter r).support : Set X))) := by
  have he : (C.step m r).E.E (Fin.castSucc i) = Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure (blowUpToBase (C.stepCenter r) ⁻¹' ((C.E.E i).support \
        componentsOfCodimAtLeastTwo ((C.stepCenter r).support : Set X)))) := by
    simp [MonomialData.step, OrderedDivisor.totalTransform]
  rw [he, Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure]

/-- The support of the Step-3.`r` centre is the closure of the maximal pieces of `E^{J_*}`. -/
private theorem coe_support_stepCenter {X : Scheme.{u}} (C : MonomialData X) (r : ℕ) :
    ((C.stepCenter r).support : Set X) = closure (⋃₀ {P | C.IsMaxPiece r (C.stepIndex r) P}) := by
  rw [MonomialData.stepCenter, Scheme.IdealSheafData.coe_support_vanishingIdeal,
    Closeds.coe_closure]

/-- The birational transform `π⁻¹_*E^i` lies over `E^i`. -/
private theorem mem_support_of_mem_support_step {X : Scheme.{u}} (C : MonomialData X)
    (m r : ℕ) (i : Fin C.E.s) {x : blowUp (C.stepCenter r)}
    (hx : x ∈ ((C.step m r).E.E (Fin.castSucc i)).support) :
    blowUpToBase (C.stepCenter r) x ∈ (C.E.E i).support := by
  have hx' : x ∈ (((C.step m r).E.E (Fin.castSucc i)).support : Set _) := hx
  rw [coe_support_step_castSucc] at hx'
  exact closure_minimal (Set.preimage_mono Set.diff_subset)
    ((C.E.E i).support.isClosed.preimage (blowUpToBase (C.stepCenter r)).continuous) hx'

/-- Case (b), coefficientwise: the coefficient in `A'` of the component of `π⁻¹_*E^i` through
`x'` is at most the coefficient in `A` of the component of `E^i` through `π(x')`. (Both members
are smooth, so at most one component passes through a point; the transform of a component `D`
has coefficient `a_D` or `a_D - m` by `step_spec`.) -/
private theorem coeffAt_step_castSucc_le {X : Scheme.{u}} (C : MonomialData X)
    (hC : C.IsMonomialData) (hk : CharZero C.k) {m r : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m)
    (hmr : m ≤ C.maxStratumWeight r) (i : Fin C.E.s) (x : blowUp (C.stepCenter r)) :
    (C.step m r).coeffAt (Fin.castSucc i) x ≤ C.coeffAt i (blowUpToBase (C.stepCenter r) x) := by
  classical
  obtain ⟨-, -, -, hmd, h5, -, h7⟩ :=
    MMP.Resolution.MonomialData.step_spec C hC hk (by omega : 1 ≤ r) hm hmr
  obtain ⟨-, hlft', -, hsnc', -⟩ := hmd
  haveI : LocallyOfFiniteType (C.step m r).sX := hlft'
  set π := blowUpToBase (C.stepCenter r)
  set E' := (C.step m r).E.E (Fin.castSucc i)
  have hsm := (hsnc'.2.1 (Fin.castSucc i)).2.2
  unfold MonomialData.coeffAt
  by_cases hex : ∃ D : AlgebraicGeometry.PrimeDivisor (blowUp (C.stepCenter r)),
      D.support ∈ componentsOf (E'.support : Set _) ∧ x ∈ D.support
  swap
  · simp only [not_exists, not_and] at hex
    rw [finsum_eq_zero_of_forall_eq_zero fun D => if_neg fun h => hex D h.1 h.2]
    exact Nat.zero_le _
  obtain ⟨D₀, hD₀c, hxD₀⟩ := hex
  rw [finsum_eq_single _ D₀ fun D hD => if_neg fun hDx => hD
    (Aux.PrimeDivisor.eq_of_support_eq (Aux.eq_of_mem_componentsOf_of_isSmoothScheme _ _ hsm
      hDx.1 hD₀c hDx.2 hxD₀))]
  rw [if_pos ⟨hD₀c, hxD₀⟩]
  set η := D₀.genericPoint
  have hηD₀ : η ∈ (D₀.support : Set _) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have hηE' : η ∈ (E'.support : Set _) := hD₀c.1.2 hηD₀
  have hη1 : Order.coheight η = 1 := D₀.coheight_genericPoint
  -- `π η ∉ Z`: otherwise `η` lies on both `π⁻¹_*E^i` and `F`, two members of an snc divisor
  -- through a point of codimension one.
  have hyZ : π η ∉ ((C.stepCenter r).support : Set X) := by
    intro hyZ
    have hηF : η ∈ (((C.step m r).E.E (Fin.last C.E.s)).support : Set _) := by
      have h := h7 hr
      change η ∈ (((C.E.totalTransform (C.stepCenter r)).E (Fin.last C.E.s)).support :
        Set (blowUp (C.stepCenter r)))
      rw [h]
      exact hyZ
    obtain ⟨n, z, c, hz, -, hc⟩ := hsnc'.2.2 η
    have hn : (n : WithBot ℕ∞) = 1 := by
      rw [← hz.2, AlgebraicGeometry.ringKrullDim_stalk_eq_coheight, hη1]
      rfl
    have hn1 : n = 1 := by exact_mod_cast hn
    subst hn1
    have := hc (a₁ := ⟨Fin.castSucc i, hηE'⟩) (a₂ := ⟨Fin.last C.E.s, hηF⟩)
      (Subsingleton.elim _ _)
    exact (Fin.castSucc_lt_last i).ne (congrArg Subtype.val this)
  -- over `X ∖ Z` the blow-up is an isomorphism, so `π η` has coheight one
  have hy1 : Order.coheight (π η) = 1 := by
    set V : X.Opens := ⟨((C.stepCenter r).support : Set X)ᶜ,
      (C.stepCenter r).support.isClosed.isOpen_compl⟩
    haveI : IsIso (π ∣_ V) := isIso_blowUp_restrict_compl_support (C.stepCenter r)
    let p : (π ⁻¹ᵁ V).toScheme := ⟨η, hyZ⟩
    have e1 : Order.coheight ((π ⁻¹ᵁ V).ι p) = Order.coheight p :=
      Topology.IsOpenEmbedding.coheight_eq _ (π ⁻¹ᵁ V).ι.isOpenEmbedding
    have e2 : Order.coheight ((π ∣_ V) p) = Order.coheight p :=
      Topology.IsOpenEmbedding.coheight_eq _ (π ∣_ V).isOpenEmbedding
    have e3 : Order.coheight (V.ι ((π ∣_ V) p)) = Order.coheight ((π ∣_ V) p) :=
      Topology.IsOpenEmbedding.coheight_eq _ V.ι.isOpenEmbedding
    have h : V.ι ((π ∣_ V) p) = π η := by
      rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
      rfl
    have h' : (π ⁻¹ᵁ V).ι p = η := rfl
    rw [← h, e3, e2, ← e1, h', hη1]
  set D := AlgebraicGeometry.PrimeDivisor.ofCoheightOne (π η) hy1
  have hDη : D.genericPoint = π η := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hy1
  have hDs : (D.support : Set X) = closure {π η} := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, hDη]
  have hyE : π η ∈ ((C.E.E i).support : Set X) := mem_support_of_mem_support_step C m r i hηE'
  -- `D` is a component of `E^i`
  have hDc : (D.support : Set X) ∈ componentsOf ((C.E.E i).support : Set X) := by
    rw [hDs]
    refine ⟨⟨isIrreducible_singleton.closure,
      closure_minimal (Set.singleton_subset_iff.2 hyE) (C.E.E i).support.isClosed⟩, ?_⟩
    rintro W ⟨hWi, hWE⟩ hyW
    have hWc : IsIrreducible (closure W) := hWi.closure
    have hWE' : closure W ⊆ ((C.E.E i).support : Set X) :=
      closure_minimal hWE (C.E.E i).support.isClosed
    set w := hWc.genericPoint
    have hw : IsGenericPoint w (closure W) := by
      have := hWc.isGenericPoint_genericPoint_closure
      rwa [closure_closure] at this
    have hyw : w ⤳ π η := hw.specializes (subset_closure (hyW (subset_closure rfl)))
    suffices hwy : w = π η by
      refine subset_closure.trans ?_
      rw [← hw.def, hwy]
    by_contra hne
    have hlt : π η < w := lt_of_le_not_ge hyw fun h => hne (hyw.antisymm h).eq
    have hw0 : Order.coheight w = 0 := by
      have hle : Order.coheight w ≤ 1 := hy1 ▸ Order.coheight_anti hlt.le
      have := Order.coheight_strictAnti hlt (hle.trans_lt (by decide))
      rw [hy1] at this
      exact ENat.lt_one_iff_eq_zero.1 this
    have hmax : IsMax w := Order.coheight_eq_zero.1 hw0
    -- `closure {w}` is an irreducible component of `E^i` of codimension `0`
    have hpure := (hC.2.2.2.1.2.1 i).2.1
    have hcod := hpure (IrreducibleCloseds.closureSingleton w) ⟨?_, ?_⟩
    · rw [codimension_eq_coheight, show IrreducibleCloseds.closureSingleton w =
        (irreducibleSetEquivPoints (α := X)).symm w from rfl, Order.coheight_orderIso,
        hw0] at hcod
      exact zero_ne_one hcod
    · change closure {w} ⊆ _
      rw [hw.def]
      exact hWE'
    · intro T hT hwT
      have hTi : IsIrreducible (T : Set X) := T.isIrreducible
      have ht : IsGenericPoint hTi.genericPoint (T : Set X) := by
        have := hTi.isGenericPoint_genericPoint_closure
        rwa [T.isClosed.closure_eq] at this
      have hwT' : w ∈ (T : Set X) := hwT (subset_closure rfl)
      have htw : hTi.genericPoint ⤳ w := ht.specializes hwT'
      have hle : hTi.genericPoint ≤ w := hmax htw
      change (T : Set X) ⊆ closure {w}
      rw [← ht.def]
      exact closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 hle))
        isClosed_closure
  -- `π x ∈ D`
  have hxD : π x ∈ (D.support : Set X) := by
    rw [hDs]
    have hsp : η ⤳ x := Aux.genericPoint_specializes_of_mem_support D₀ hxD₀
    exact specializes_iff_mem_closure.1 (hsp.map π.continuous)
  have hA : (C.step m r).A D₀ ≤ C.A D := by
    rw [h5 D D₀ hDη.symm]
    split_ifs <;> omega
  refine hA.trans ?_
  have hfin : (Function.support C.A).Finite := hC.2.2.2.2.1
  refine le_trans ?_ (single_le_finsum D (hfin.subset ?_) ?_)
  · rw [if_pos ⟨hDc, hxD⟩]
  · intro D' hD'
    by_contra h
    exact hD' (by simp [Function.notMem_support.1 h])
  · intro D'
    exact Nat.zero_le _

/-- Case (c), coefficientwise: the coefficient in `A'` of the component of `F` through `x'` is
`m_r(E, A) - m`. (`F` is smooth and lies over `Z`, so at most one component passes through a
point, with coefficient `m_r - m` by `step_spec`.) -/
private theorem coeffAt_step_last_le {X : Scheme.{u}} (C : MonomialData X)
    (hC : C.IsMonomialData) (hk : CharZero C.k) {m r : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m)
    (hmr : m ≤ C.maxStratumWeight r) (x : blowUp (C.stepCenter r)) :
    (C.step m r).coeffAt (Fin.last C.E.s) x ≤ C.maxStratumWeight r - m := by
  classical
  obtain ⟨-, -, -, hmd, -, h6, h7⟩ :=
    MMP.Resolution.MonomialData.step_spec C hC hk (by omega : 1 ≤ r) hm hmr
  obtain ⟨-, hlft', -, hsnc', -⟩ := hmd
  haveI : LocallyOfFiniteType (C.step m r).sX := hlft'
  set F := (C.step m r).E.E (Fin.last C.E.s)
  have hsm := (hsnc'.2.1 (Fin.last C.E.s)).2.2
  have hF : (F.support : Set (blowUp (C.stepCenter r))) =
      blowUpToBase (C.stepCenter r) ⁻¹' ((C.stepCenter r).support : Set X) := h7 hr
  unfold MonomialData.coeffAt
  by_cases hex : ∃ D : AlgebraicGeometry.PrimeDivisor (blowUp (C.stepCenter r)),
      D.support ∈ componentsOf (F.support : Set _) ∧ x ∈ D.support
  · obtain ⟨D₀, hD₀c, hxD₀⟩ := hex
    rw [finsum_eq_single _ D₀ fun D hD => if_neg fun hDx => hD
      (Aux.PrimeDivisor.eq_of_support_eq (Aux.eq_of_mem_componentsOf_of_isSmoothScheme _ _ hsm
        hDx.1 hD₀c hDx.2 hxD₀))]
    rw [if_pos ⟨hD₀c, hxD₀⟩]
    have hgen : D₀.genericPoint ∈ (D₀.support : Set _) := by
      have hall : ∀ y, D₀.idealSheaf.subschemeι y ∈ (D₀.support : Set _) := fun y => by
        rw [AlgebraicGeometry.PrimeDivisor.support, ← D₀.idealSheaf.range_subschemeι]
        exact Set.mem_range_self y
      unfold AlgebraicGeometry.PrimeDivisor.genericPoint
      exact hall _
    have hgenF : D₀.genericPoint ∈ (F.support : Set _) := hD₀c.1.2 hgen
    rw [hF] at hgenF
    exact (h6 D₀ hgenF).le
  · simp only [not_exists, not_and] at hex
    rw [finsum_eq_zero_of_forall_eq_zero fun D => if_neg fun h => hex D h.1 h.2]
    exact Nat.zero_le _

/-- The indices `i ≤ s` with `E'^i = π⁻¹_*E^i` in `J ⊆ {1, …, s + 1}`. -/
private def castSuccPreimage {n : ℕ} (J : Finset (Fin (n + 1))) : Finset (Fin n) :=
  Finset.univ.filter fun i => Fin.castSucc i ∈ J

private theorem mem_castSuccPreimage {n : ℕ} {J : Finset (Fin (n + 1))} {i : Fin n} :
    i ∈ castSuccPreimage J ↔ Fin.castSucc i ∈ J := by
  simp [castSuccPreimage]

/-- A sum over `J ⊆ {1, …, n + 1}` splits into the part over `{1, …, n}` and the last term. -/
private theorem sum_eq_sum_castSuccPreimage_add {n : ℕ} (J : Finset (Fin (n + 1)))
    (f : Fin (n + 1) → ℕ) : ∑ j ∈ J, f j =
      ∑ i ∈ castSuccPreimage J, f (Fin.castSucc i) +
        if Fin.last n ∈ J then f (Fin.last n) else 0 := by
  rw [castSuccPreimage, Finset.sum_filter,
    ← Fin.sum_univ_castSucc (f := fun j => if j ∈ J then f j else 0), ← Finset.sum_filter,
    Finset.filter_mem_eq_inter, Finset.univ_inter]

private theorem card_eq_card_castSuccPreimage_add {n : ℕ} (J : Finset (Fin (n + 1))) :
    J.card = (castSuccPreimage J).card + if Fin.last n ∈ J then 1 else 0 := by
  simpa [← Finset.card_eq_sum_ones] using sum_eq_sum_castSuccPreimage_add J fun _ => 1

private theorem card_castSuccPreimage {n : ℕ} {J : Finset (Fin (n + 1))}
    (hl : Fin.last n ∉ J) : (castSuccPreimage J).card = J.card := by
  simp [card_eq_card_castSuccPreimage_add J, hl]

private theorem eq_of_castSuccPreimage_eq {n : ℕ} {J J' : Finset (Fin (n + 1))}
    (hl : Fin.last n ∉ J) (hl' : Fin.last n ∉ J')
    (h : castSuccPreimage J = castSuccPreimage J') : J = J' := by
  ext j
  induction j using Fin.lastCases with
  | last => exact iff_of_false hl hl'
  | cast i => rw [← mem_castSuccPreimage, ← mem_castSuccPreimage, h]

/-- A closed subset of a noetherian space has finitely many connected components. -/
private theorem finite_connectedComponentIn {α : Type*} [TopologicalSpace α]
    [TopologicalSpace.NoetherianSpace α] {s : Set α} (hs : IsClosed s) :
    {c | ∃ x ∈ s, c = connectedComponentIn s x}.Finite := by
  obtain ⟨S, hSf, -, hSi, rfl⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hs
  refine (hSf.biUnion (t := fun t => {c | ∃ y ∈ t, c = connectedComponentIn (⋃₀ S) y})
    fun t ht => ?_).subset ?_
  · refine Set.Subsingleton.finite ?_
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    exact connectedComponentIn_eq
      ((hSi t ht).2.isPreconnected.subset_connectedComponentIn hy
        (Set.subset_sUnion_of_mem ht) hz)
  · rintro _ ⟨x, ⟨t, ht, hxt⟩, rfl⟩
    exact Set.mem_biUnion ht ⟨x, hxt, rfl⟩

/-- For monomial data there are finitely many pieces of `r`-fold intersections of maximal
weight. -/
private theorem finite_isMaxPiece {X : Scheme.{u}} (C : MonomialData X)
    (hC : C.IsMonomialData) (r : ℕ) :
    {p : Finset (Fin C.E.s) × Set X | C.IsMaxPiece r p.1 p.2}.Finite := by
  obtain ⟨-, hlft, hqc, -⟩ := hC
  haveI : LocallyOfFiniteType C.sX := hlft
  haveI : QuasiCompact C.sX := hqc
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian C.sX
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace C.sX
  haveI : IsNoetherian X := {}
  have hcl : ∀ J, IsClosed (C.stratum J) := fun J =>
    isClosed_biInter fun j _ => (C.E.E j).support.isClosed
  refine ((Set.finite_univ (α := Finset (Fin C.E.s))).biUnion fun J _ =>
    (Set.finite_singleton J).prod (finite_connectedComponentIn (hcl J))).subset ?_
  rintro ⟨J, P⟩ ⟨-, ⟨x, hx, hP⟩, -⟩
  exact Set.mem_biUnion (Set.mem_univ J) ⟨rfl, x, hx, hP⟩

/-- The birational transform `π⁻¹_*E^J` lies over `E^J`. -/
private theorem mem_stratum_castSuccPreimage {X : Scheme.{u}} (C : MonomialData X) (m r : ℕ)
    {J : Finset (Fin (C.E.s + 1))} {x : blowUp (C.stepCenter r)}
    (hx : x ∈ (C.step m r).stratum J) :
    blowUpToBase (C.stepCenter r) x ∈ C.stratum (castSuccPreimage J) := by
  simp only [MonomialData.stratum, Set.mem_iInter] at hx ⊢
  intro i hi
  exact mem_support_of_mem_support_step C m r i (hx (Fin.castSucc i) (mem_castSuccPreimage.1 hi))

/-- The new weight `σ'_J(x)` splits into the transforms of the `E^i` and possibly `F`. -/
private theorem stratumWeight_step_eq {X : Scheme.{u}} (C : MonomialData X) (m r : ℕ)
    (J : Finset (Fin (C.E.s + 1))) (x : blowUp (C.stepCenter r)) :
    (C.step m r).stratumWeight J x =
      ∑ i ∈ castSuccPreimage J, (C.step m r).coeffAt (Fin.castSucc i) x +
        if Fin.last C.E.s ∈ J then (C.step m r).coeffAt (Fin.last C.E.s) x else 0 :=
  sum_eq_sum_castSuccPreimage_add J _

/-- Case (b), summed: the transforms of the `E^i`, `i ∈ J`, carry at most the old weight below. -/
private theorem sum_coeffAt_step_castSucc_le {X : Scheme.{u}} (C : MonomialData X)
    (hC : C.IsMonomialData) (hk : CharZero C.k) {m r : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m)
    (hmr : m ≤ C.maxStratumWeight r) (J : Finset (Fin (C.E.s + 1)))
    (x : blowUp (C.stepCenter r)) :
    ∑ i ∈ castSuccPreimage J, (C.step m r).coeffAt (Fin.castSucc i) x ≤
      C.stratumWeight (castSuccPreimage J) (blowUpToBase (C.stepCenter r) x) :=
  Finset.sum_le_sum fun i _ => coeffAt_step_castSucc_le C hC hk hr hm hmr i x

/-- Case (b), weightwise: on an `r`-fold intersection not involving `F`, the new weight is at most
the old weight below. -/
private theorem stratumWeight_step_le_of_last_notMem {X : Scheme.{u}} (C : MonomialData X)
    (hC : C.IsMonomialData) (hk : CharZero C.k) {m r : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m)
    (hmr : m ≤ C.maxStratumWeight r) {J : Finset (Fin (C.E.s + 1))} (hl : Fin.last C.E.s ∉ J)
    (x : blowUp (C.stepCenter r)) :
    (C.step m r).stratumWeight J x ≤
      C.stratumWeight (castSuccPreimage J) (blowUpToBase (C.stepCenter r) x) := by
  rw [stratumWeight_step_eq, if_neg hl, add_zero]
  exact sum_coeffAt_step_castSucc_le C hC hk hr hm hmr J x

/-- Case (c), strictly: an `r`-fold weight of the new data on an intersection involving `F` is
`< m_r(E, A)`: the transforms of the `r - 1` other members carry at most `m_{r-1} < m`, and `F`
carries `m_r - m`. -/
private theorem stratumWeight_step_lt_of_last_mem {X : Scheme.{u}} (C : MonomialData X)
    (hC : C.IsMonomialData) (hk : CharZero C.k) {m r : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m)
    (hlow : ∀ t, 1 ≤ t → t < r → C.maxStratumWeight t < m)
    (hmr : m ≤ C.maxStratumWeight r) {J : Finset (Fin (C.E.s + 1))} (hJ : J.card = r)
    (hl : Fin.last C.E.s ∈ J) {x : blowUp (C.stepCenter r)}
    (hx : x ∈ (C.step m r).stratum J) :
    (C.step m r).stratumWeight J x < C.maxStratumWeight r := by
  have hJ₀ : (castSuccPreimage J).card = r - 1 := by
    have := card_eq_card_castSuccPreimage_add J
    rw [if_pos hl] at this
    omega
  have h1 := stratumWeight_le_maxStratumWeight C hC.2.2.2.2.1 hJ₀
    (mem_stratum_castSuccPreimage C m r hx)
  have h2 := hlow (r - 1) (by omega) (by omega)
  have h3 := coeffAt_step_last_le C hC hk hr hm hmr x
  have h4 := sum_coeffAt_step_castSucc_le C hC hk hr hm hmr J x
  rw [stratumWeight_step_eq, if_pos hl]
  omega

/-- If `m_r(E, A) ≥ 1`, some piece of `E^{J_*}` has maximal weight. -/
private theorem exists_isMaxPiece_stepIndex {X : Scheme.{u}} (C : MonomialData X)
    (hC : C.IsMonomialData) {r : ℕ} (hpos : 1 ≤ C.maxStratumWeight r) :
    ∃ P, C.IsMaxPiece r (C.stepIndex r) P := by
  classical
  have hfin : (Function.support C.A).Finite := hC.2.2.2.2.1
  have h0 : C.maxStratumWeight r - 1 < C.maxStratumWeight r := by omega
  obtain ⟨J, h0⟩ := exists_lt_of_lt_ciSup' h0
  obtain ⟨hJ, h0⟩ := exists_lt_of_lt_ciSup' h0
  obtain ⟨x, h0⟩ := exists_lt_of_lt_ciSup' h0
  obtain ⟨hx, h0⟩ := exists_lt_of_lt_ciSup' h0
  have hle := stratumWeight_le_maxStratumWeight C hfin hJ hx
  have hmax : C.IsMaxPiece r J (connectedComponentIn (C.stratum J) x) :=
    ⟨hJ, ⟨x, hx, rfl⟩, fun y hy => by
      rw [C.stratumWeight_eq_of_mem_connectedComponentIn hC J hx hy]; omega⟩
  have hS : (Finset.univ.filter fun J => ∃ P, C.IsMaxPiece r J P).Nonempty :=
    ⟨J, Finset.mem_filter.2 ⟨Finset.mem_univ _, _, hmax⟩⟩
  unfold MonomialData.stepIndex
  simp only [dif_pos hS]
  exact (Finset.mem_filter.1
    (Finset.exists_min_image _ (fun J => J.sort (· ≤ ·)) hS).choose_spec.1).2

/-- In a closed subset of a topological space, connected components are closed. -/
private theorem isClosed_connectedComponentIn {α : Type*} [TopologicalSpace α] {s : Set α}
    (hs : IsClosed s) (x : α) : IsClosed (connectedComponentIn s x) := by
  by_cases hx : x ∈ s
  · refine closure_subset_iff_isClosed.1 ?_
    exact isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
      (subset_closure (mem_connectedComponentIn hx))
      (closure_minimal (connectedComponentIn_subset _ _) hs)
  · rw [connectedComponentIn_eq_empty hx]
    exact isClosed_empty

/-- Near a point of the closure of a union of connected components of a closed subset `s` of a
noetherian space, that closure agrees with `s`. -/
private theorem exists_isOpen_closure_sUnion_inter_eq {α : Type*} [TopologicalSpace α]
    [NoetherianSpace α] {s : Set α} (hs : IsClosed s) {T : Set (Set α)}
    (hT : ∀ t ∈ T, ∃ y ∈ s, t = connectedComponentIn s y) {x : α} (hx : x ∈ closure (⋃₀ T)) :
    ∃ V : Set α, IsOpen V ∧ x ∈ V ∧ closure (⋃₀ T) ∩ V = s ∩ V := by
  have hfin := finite_connectedComponentIn hs
  have hTK : T ⊆ {c | ∃ z ∈ s, c = connectedComponentIn s z} := hT
  have hcl : IsClosed (⋃₀ T) := (hfin.subset hTK).isClosed_sUnion fun t ht => by
    obtain ⟨y, -, rfl⟩ := hT t ht
    exact isClosed_connectedComponentIn hs y
  rw [hcl.closure_eq] at hx ⊢
  obtain ⟨t, ht, hxt⟩ := hx
  obtain ⟨y, -, rfl⟩ := hT t ht
  set K := {c | (∃ z ∈ s, c = connectedComponentIn s z) ∧ x ∉ c}
  refine ⟨(⋃ c ∈ K, c)ᶜ, ?_, ?_, ?_⟩
  · refine (Set.Finite.isClosed_biUnion (hfin.subset fun c hc => hc.1) fun c hc => ?_).isOpen_compl
    obtain ⟨z, -, rfl⟩ := hc.1
    exact isClosed_connectedComponentIn hs z
  · rw [Set.mem_compl_iff, Set.mem_iUnion₂]
    rintro ⟨c, hc, hxc⟩
    exact hc.2 hxc
  · ext z
    rw [Set.mem_inter_iff, Set.mem_inter_iff]
    refine and_congr_left fun hzV => ⟨fun ⟨t', ht', hzt'⟩ => ?_, fun hz => ?_⟩
    · obtain ⟨y', -, rfl⟩ := hT t' ht'
      exact connectedComponentIn_subset _ _ hzt'
    · have hxz : x ∈ connectedComponentIn s z := by
        by_contra h
        exact hzV (Set.mem_iUnion₂.2 ⟨_, ⟨⟨z, hz, rfl⟩, h⟩, mem_connectedComponentIn hz⟩)
      refine ⟨_, ht, ?_⟩
      rw [connectedComponentIn_eq hxt, ← connectedComponentIn_eq hxz]
      exact mem_connectedComponentIn hz

/-- Case (a): the birational transform `π⁻¹_*E^{J_*}` does not meet `F = π⁻¹(Z)`. In the chart
`U_l` of the blow-up along `Z = (y_1 = ⋯ = y_r = 0)` the transform of `E^{j_l}` is empty, so the
transforms of the `E^{j_t}`, `j_t ∈ J_*`, have no common point over `Z`. -/
private theorem notMem_stepCenter_of_mem_stratum_step {X : Scheme.{u}} (C : MonomialData X)
    (hC : C.IsMonomialData) (hk : CharZero C.k) {m r : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m)
    (hmr : m ≤ C.maxStratumWeight r) {J : Finset (Fin (C.E.s + 1))} (hl : Fin.last C.E.s ∉ J)
    (hJ : castSuccPreimage J = C.stepIndex r) {x : blowUp (C.stepCenter r)}
    (hx : x ∈ (C.step m r).stratum J) :
    blowUpToBase (C.stepCenter r) x ∉ ((C.stepCenter r).support : Set X) := by
  classical
  intro hyZ
  obtain ⟨P₀, hP₀⟩ := exists_isMaxPiece_stepIndex C hC (r := r) (by omega)
  have hScard : (C.stepIndex r).card = r := hP₀.1
  obtain ⟨-, hlft, hqc, hsnc, -⟩ := hC
  haveI : LocallyOfFiniteType C.sX := hlft
  haveI : QuasiCompact C.sX := hqc
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian C.sX
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace C.sX
  haveI : IsNoetherian X := {}
  set S := C.stepIndex r
  have hyS : (blowUpToBase (C.stepCenter r) x) ∈ C.stratum S :=
    hJ ▸ mem_stratum_castSuccPreimage C m r hx
  have hyE : ∀ j ∈ S, (blowUpToBase (C.stepCenter r) x) ∈ (C.E.E j).support := by
    simp only [MonomialData.stratum, Set.mem_iInter] at hyS
    exact hyS
  have hxE : ∀ j ∈ S, x ∈ ((C.step m r).E.E (Fin.castSucc j)).support := fun j hj => by
    simp only [MonomialData.stratum, Set.mem_iInter] at hx
    exact hx _ (mem_castSuccPreimage.1 (hJ ▸ hj))
  have hstrat_cl : IsClosed (C.stratum S) :=
    isClosed_biInter fun j _ => (C.E.E j).support.isClosed
  have hZcoe : ((C.stepCenter r).support : Set X) = closure (⋃₀ {P | C.IsMaxPiece r S P}) :=
    coe_support_stepCenter C r
  have hZS : ((C.stepCenter r).support : Set X) ⊆ C.stratum S := by
    rw [hZcoe]
    refine closure_minimal (Set.sUnion_subset fun P hP => ?_) hstrat_cl
    obtain ⟨-, ⟨w, -, rfl⟩, -⟩ := hP
    exact connectedComponentIn_subset _ _
  -- every component of `(C.stepCenter r)` has codimension `≥ 2`: it lies on two members of `E`
  have hZC₂ : ((C.stepCenter r).support : Set X) ⊆
      componentsOfCodimAtLeastTwo ((C.stepCenter r).support : Set X) := by
    intro u hu
    obtain ⟨-, hcov⟩ := Aux.finite_and_cover_componentsOf (C.stepCenter r).support.isClosed
    obtain ⟨W, hW, huW⟩ := hcov hu
    rw [componentsOfCodimAtLeastTwo_eq]
    refine Set.mem_iUnion₂.2 ⟨W, hW, Set.mem_iUnion.2 ⟨⟨hW.1.1, ?_⟩, huW⟩⟩
    set W' := irreducibleClosure hW.1.1
    have hcod : codimension W' = Order.coheight W'.isIrreducible.genericPoint := by
      rw [codimension_eq_coheight]
      exact (Order.coheight_orderIso (irreducibleSetEquivPoints (α := X)) W').symm
    rw [hcod]
    set ξ := W'.isIrreducible.genericPoint
    have hξ : ξ ∈ closure W := by
      have h := W'.isIrreducible.isGenericPoint_genericPoint_closure.mem
      change ξ ∈ closure (closure W) at h
      rwa [closure_closure] at h
    have hξZ : ξ ∈ ((C.stepCenter r).support : Set X) :=
      closure_minimal hW.1.2 (C.stepCenter r).support.isClosed hξ
    have hξS := hZS hξZ
    simp only [MonomialData.stratum, Set.mem_iInter] at hξS
    by_contra hlt
    push Not at hlt
    obtain ⟨n', z', c', hz', -, hinj⟩ := hsnc.2.2 ξ
    have hn' : (n' : ℕ∞) = Order.coheight ξ := by
      have h : (n' : WithBot ℕ∞) = Order.coheight ξ := by
        rw [← hz'.2, AlgebraicGeometry.ringKrullDim_stalk_eq_coheight]
      exact_mod_cast h
    have hn'2 : n' ≤ 1 := by
      have : (n' : ℕ∞) < 2 := hn' ▸ hlt
      have : n' < 2 := by exact_mod_cast this
      omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < S.card)
    haveI : Subsingleton (Fin n') := Fin.subsingleton_iff_le_one.2 hn'2
    exact hab (congrArg Subtype.val
      (hinj (a₁ := ⟨a, hξS a ha⟩) (a₂ := ⟨b, hξS b hb⟩) (Subsingleton.elim _ _)))
  -- near `(blowUpToBase (C.stepCenter r) x)`, `(C.stepCenter r)` is `E^S`
  obtain ⟨V, hVo, hyV, hV⟩ := exists_isOpen_closure_sUnion_inter_eq hstrat_cl
    (T := {P | C.IsMaxPiece r S P}) (fun P hP => hP.2.1) (by rw [← hZcoe]; exact hyZ)
  have hIsupp : (((⨆ j : S, C.E.E j : X.IdealSheafData)).support : Set X) = C.stratum S := by
    rw [Scheme.IdealSheafData.support_iSup, Closeds.coe_iInf]
    ext w
    simp [MonomialData.stratum]
  have hstalk0 : IdealSheafData.stalk (C.stepCenter r) (blowUpToBase (C.stepCenter r) x) =
      (⨆ j : S, IdealSheafData.stalk (C.E.E j) (blowUpToBase (C.stepCenter r) x)).radical := by
    have h := IdealSheafData.stalk_vanishingIdeal_congr
      (S := Closeds.closure (⋃₀ {P | C.IsMaxPiece r S P}))
      (T := (⨆ j : S, C.E.E j : X.IdealSheafData).support) (V := ⟨V, hVo⟩) hyV
      (by rw [Closeds.coe_closure, hIsupp]; exact hV)
    rw [Scheme.IdealSheafData.vanishingIdeal_support] at h
    change IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal _)
      (blowUpToBase (C.stepCenter r) x) = _
    rw [h, stalk_radical, stalk_iSup]
  obtain ⟨n, z, c, hz, hc, -⟩ := hsnc.2.2 (blowUpToBase (C.stepCenter r) x)
  have hspan : ⨆ j : S, IdealSheafData.stalk (C.E.E j) (blowUpToBase (C.stepCenter r) x) =
      Ideal.span (z '' ((S.attach.image fun j => c ⟨j.1, hyE j.1 j.2⟩ : Finset (Fin n)) :
        Set (Fin n))) := by
    have hi : ∀ j : S, IdealSheafData.stalk (C.E.E j) (blowUpToBase (C.stepCenter r) x) =
        Ideal.span {z (c ⟨j.1, hyE j.1 j.2⟩)} := fun j => hc ⟨j.1, _⟩
    simp_rw [hi, ← Ideal.span_iUnion]
    congr 1
    ext a
    simp only [Set.mem_iUnion, Set.mem_singleton_iff, Finset.coe_image, Finset.coe_attach,
      Set.image_univ, Set.mem_image, Set.mem_range, Subtype.exists]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      exact ⟨i, hi, rfl⟩
  have := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz
  have hstalk : IdealSheafData.stalk (C.stepCenter r) (blowUpToBase (C.stepCenter r) x) =
      ⨆ j : S, IdealSheafData.stalk (C.E.E j) (blowUpToBase (C.stepCenter r) x) := by
    rw [hstalk0, hspan, radical_span_image_of_isRegularSystemOfParameters hz]
  -- the chart argument
  obtain ⟨U, hU, hyU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := (blowUpToBase (C.stepCenter r) x)) (U := ⊤)
      (by simp)
  let Ua : X.affineOpens := ⟨U, hU⟩
  have hex : ∀ i : S, ∃ e ∈ (C.E.E i).ideal Ua,
      IdealSheafData.stalk (C.E.E i) (blowUpToBase (C.stepCenter r) x) =
      Ideal.span {(X.presheaf.germ U (blowUpToBase (C.stepCenter r) x) hyU).hom e} := fun i =>
    exists_mem_ideal_stalk_eq_span_germ (C.E.E i) Ua hyU (hc ⟨i.1, hyE i.1 i.2⟩)
  choose e he hspan' using hex
  have hstalk' : IdealSheafData.stalk (C.stepCenter r) (blowUpToBase (C.stepCenter r) x) =
      Ideal.span (Set.range fun i : S =>
        (X.presheaf.germ U (blowUpToBase (C.stepCenter r) x) hyU).hom (e i)) := by
    rw [hstalk]
    simp_rw [hspan', ← Ideal.span_iUnion]
    congr 1
    ext a
    simp
  obtain ⟨U', hU'U, hyU', hgen⟩ :=
    MMP.Flips.ResolutionInputs.exists_ideal_eq_span_of_stalk_eq (C.stepCenter r) (V := U) hyU
      (fun i : S => e i) hstalk'
  obtain ⟨W, hW, hyW, hWU'⟩ := exists_isAffineOpen_mem_and_subset hyU'
  let Wa : X.affineOpens := ⟨W, hW⟩
  let σ : S ≃ Fin S.card := S.equivFin
  let f : Fin S.card → Γ(X, W) := fun m => restrictSection Wa (hWU'.trans hU'U) (e (σ.symm m))
  have hf : (C.stepCenter r).ideal Wa = Ideal.span (Set.range f) := by
    rw [hgen Wa hWU']
    congr 1
    exact (σ.symm.surjective.range_comp
      (fun i : S => restrictSection Wa (hWU'.trans hU'U) (e i))).symm
  have hq : x ∈ blowUpToBase (C.stepCenter r) ⁻¹ᵁ W := hyW
  rw [← MMP.Flips.ResolutionInputs.iSup_blowUpChartOpen_eq_preimage (C.stepCenter r) Wa f hf] at hq
  obtain ⟨m', hm'⟩ := Opens.mem_iSup.1 hq
  set ℓ : S := σ.symm m'
  have hfm : f m' ∈ (C.E.E ℓ).ideal Wa :=
    Scheme.IdealSheafData.ideal_le_comap_ideal (C.E.E ℓ) (U := Wa) (V := Ua)
      (hWU'.trans hU'U) (he ℓ)
  have hqℓ := hxE ℓ ℓ.2
  change x ∈ (((C.step m r).E.E (Fin.castSucc ℓ.1)).support : Set _) at hqℓ
  rw [coe_support_step_castSucc] at hqℓ
  obtain ⟨w, hwC, hw⟩ := mem_closure_iff.1 hqℓ _
    (blowUpChartOpen (C.stepCenter r) Wa
      (MMP.Flips.ResolutionInputs.generatorSection (C.stepCenter r) Wa f hf m')).1.isOpen hm'
  exact hw.2 (hZC₂ (mem_support_of_mem_blowUpChartOpen (C.stepCenter r) (C.E.E ℓ) Wa f hf m' hfm
    hwC hw.1))

/-- A member of a regular system of parameters outside `s` is not in the ideal spanned by the
members indexed by `s`. -/
private theorem notMem_span_image_of_isRegularSystemOfParameters {R : Type*} [CommRing R]
    [IsRegularLocalRing R] {n : ℕ} {z : Fin n → R}
    (hz : MMP.Mori.IsRegularSystemOfParameters z) {s : Finset (Fin n)} {m : Fin n}
    (hm : m ∉ s) : z m ∉ Ideal.span (z '' (s : Set (Fin n))) := by
  intro hmem
  obtain ⟨hreg, -, hsop⟩ :=
    MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_quotient_image hz s
  have := hreg
  have hm' : m ∈ (sᶜ : Finset (Fin n)) := by simpa using hm
  obtain ⟨j, hj⟩ : ∃ j, (sᶜ).orderEmbOfFin rfl j = m := by
    have hr := Finset.range_orderEmbOfFin (sᶜ) rfl
    have : m ∈ Set.range ((sᶜ).orderEmbOfFin rfl) := by
      rw [hr]; exact hm'
    exact this
  refine ne_zero_of_isRegularSystemOfParameters hsop j ?_
  simp only [hj]
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact hmem

/-- At a point `w` with snc coordinates for the family `E`, the intersection `⋂_{j ∈ J} E_j` has a
generic point `ξ ⤳ w` near `w`: every point of the intersection specializing to `w` is a
specialization of `ξ`, and `ξ` lies on no `E_i`, `i ∉ J`. -/
private theorem exists_generization_stratum {X : Scheme.{u}} [IsLocallyNoetherian X] {Λ : Type*}
    (E : Λ → X.IdealSheafData) (J : Finset Λ) {w : X} {n : ℕ}
    {z : Fin n → X.presheaf.stalk w} {c : {i // w ∈ (E i).support} → Fin n}
    (hz : MMP.Mori.IsRegularSystemOfParameters z)
    (hc : ∀ i, IdealSheafData.stalk (E i.1) w = Ideal.span {z (c i)})
    (hinj : Function.Injective c) (hw : ∀ j ∈ J, w ∈ (E j).support) :
    ∃ ξ : X, ξ ⤳ w ∧ (∀ j ∈ J, ξ ∈ (E j).support) ∧
      (∀ y : X, (∀ j ∈ J, y ∈ (E j).support) → y ⤳ w → ξ ⤳ y) ∧
      (∀ i, i ∉ J → ξ ∉ (E i).support) := by
  classical
  have := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz
  set s : Finset (Fin n) := J.attach.image fun j => c ⟨j.1, hw j.1 j.2⟩
  set 𝔭 : Ideal (X.presheaf.stalk w) := Ideal.span (z '' (s : Set (Fin n)))
  have h𝔭 : 𝔭.IsPrime := by
    obtain ⟨hreg, -, -⟩ :=
      MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_quotient_image hz s
    have : IsDomain (X.presheaf.stalk w ⧸ 𝔭) := IsRegularLocalRing.isDomain _
    exact (Ideal.Quotient.isDomain_iff_prime _).1 inferInstance
  have hzs : ∀ j (hj : j ∈ J), z (c ⟨j, hw j hj⟩) ∈ 𝔭 := fun j hj =>
    Ideal.subset_span ⟨_, Finset.mem_coe.2 (Finset.mem_image.2 ⟨⟨j, hj⟩, Finset.mem_attach _ _,
      rfl⟩), rfl⟩
  let P : PrimeSpectrum (X.presheaf.stalk w) := ⟨𝔭, h𝔭⟩
  have hξ := specializes_fromSpecStalk w P
  have hprime := primeOfSpecializes_fromSpecStalk w P hξ
  refine ⟨X.fromSpecStalk w P, hξ, fun j hj => ?_, fun y hy hyw => ?_, fun i hi hξi => ?_⟩
  · rw [mem_support_iff_stalk_le_primeOfSpecializes (E j) hξ, hprime, hc ⟨j, hw j hj⟩,
      Ideal.span_le, Set.singleton_subset_iff]
    exact hzs j hj
  · have hle : 𝔭 ≤ MMP.Intersection.primeOfSpecializes hyw := by
      rw [Ideal.span_le]
      rintro _ ⟨m, hm, rfl⟩
      obtain ⟨⟨j, hj⟩, -, rfl⟩ := Finset.mem_image.1 hm
      have h := (mem_support_iff_stalk_le_primeOfSpecializes (E j) hyw).1 (hy j hj)
      rw [hc ⟨j, hw j hj⟩] at h
      exact h (Ideal.mem_span_singleton_self _)
    have hsp : P ⤳ (⟨_, inferInstance⟩ : PrimeSpectrum (X.presheaf.stalk w)) :=
      (PrimeSpectrum.le_iff_specializes P ⟨MMP.Intersection.primeOfSpecializes hyw,
        inferInstance⟩).1 hle
    have := hsp.map (X.fromSpecStalk w).continuous
    rwa [MMP.Intersection.fromSpecStalk_primeOfSpecializes hyw] at this
  · have hwi : w ∈ (E i).support := hξ.mem_closed (E i).support.isClosed hξi
    have h := (mem_support_iff_stalk_le_primeOfSpecializes (E i) hξ).1 hξi
    rw [hprime, hc ⟨i, hwi⟩] at h
    refine notMem_span_image_of_isRegularSystemOfParameters hz ?_
      (h (Ideal.mem_span_singleton_self _))
    intro hmem
    obtain ⟨⟨j, hj⟩, -, hji⟩ := Finset.mem_image.1 hmem
    have : j = i := congrArg Subtype.val (hinj hji)
    exact hi (this ▸ hj)

/-- In a noetherian sober space, if every point `w` of a closed set `S` has a generization in `S`
of which every generization of `w` in `S` is a specialization, the connected components of `S`
are the closures of points. -/
private theorem connectedComponentIn_eq_closure_of_generization {α : Type*} [TopologicalSpace α]
    [NoetherianSpace α] [QuasiSober α] {S : Set α} (hS : IsClosed S)
    (hg : ∀ w ∈ S, ∃ ξ ∈ S, ξ ⤳ w ∧ ∀ y ∈ S, y ⤳ w → ξ ⤳ y) {x : α} (hx : x ∈ S) :
    ∃ ξ ∈ S, connectedComponentIn S x = closure {ξ} := by
  obtain ⟨ξ, hξS, hξx, hξ⟩ := hg x hx
  set Tx := closure ({ξ} : Set α)
  have hTxS : Tx ⊆ S := closure_minimal (Set.singleton_subset_iff.2 hξS) hS
  have hxT : x ∈ Tx := specializes_iff_mem_closure.1 hξx
  have key : ∀ w ∈ Tx, ∃ η ∈ S, closure {η} = Tx ∧ ∀ y ∈ S, y ⤳ w → η ⤳ y := by
    intro w hw
    obtain ⟨η, hηS, hηw, hη⟩ := hg w (hTxS hw)
    have h1 : η ⤳ ξ := hη ξ hξS (specializes_iff_mem_closure.2 hw)
    have h2 : ξ ⤳ η := hξ η hηS (h1.trans hξx)
    exact ⟨η, hηS, (specializes_iff_closure_subset.1 h2).antisymm
      (specializes_iff_closure_subset.1 h1), hη⟩
  obtain ⟨𝒯, h𝒯f, h𝒯c, h𝒯i, h𝒯⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hS
  have hmeet : ∀ T ∈ 𝒯, (T ∩ Tx).Nonempty → T ⊆ Tx := by
    rintro T hT ⟨w, hwT, hwTx⟩
    obtain ⟨η, -, hηT, hη⟩ := key w hwTx
    have hTc := h𝒯c T hT
    have hgen := (h𝒯i T hT).isGenericPoint_genericPoint_closure
    rw [hTc.closure_eq] at hgen
    have htS : (h𝒯i T hT).genericPoint ∈ S := h𝒯 ▸ Set.mem_sUnion_of_mem hgen.mem hT
    have := hη _ htS (hgen.specializes hwT)
    rw [← hgen.def, ← hηT]
    exact specializes_iff_closure_subset.1 this
  set K := ⋃₀ {T ∈ 𝒯 | Disjoint T Tx}
  have hKc : IsClosed K :=
    (h𝒯f.subset fun T hT => hT.1).isClosed_sUnion fun T hT => h𝒯c T hT.1
  have hSK : S ⊆ Tx ∪ K := by
    intro v hv
    rw [h𝒯] at hv
    obtain ⟨T, hT, hvT⟩ := hv
    by_cases hd : Disjoint T Tx
    · exact Or.inr ⟨T, ⟨hT, hd⟩, hvT⟩
    · exact Or.inl (hmeet T hT (Set.not_disjoint_iff_nonempty_inter.1 hd) hvT)
  have hKTx : Disjoint Tx K := by
    rw [Set.disjoint_left]
    rintro v hvT ⟨T, ⟨-, hd⟩, hvT'⟩
    exact Set.disjoint_left.1 hd hvT' hvT
  refine ⟨ξ, hξS, (Set.Subset.antisymm ?_ ?_)⟩
  · rcases isPreconnected_iff_subset_of_disjoint_closed.1 isPreconnected_connectedComponentIn
      Tx K isClosed_closure hKc ((connectedComponentIn_subset _ _).trans hSK)
      (by
        rw [Set.disjoint_iff_inter_eq_empty.1 hKTx, Set.inter_empty]) with h | h
    · exact h
    · exact absurd (h (mem_connectedComponentIn hx)) (Set.disjoint_left.1 hKTx hxT)
  · exact isIrreducible_singleton.closure.isConnected.isPreconnected.subset_connectedComponentIn
      hxT hTxS

/-- Case (b), piecewise: the part of an `r`-fold intersection `π⁻¹_*E^J` of `E'` not involving
`F` lying over one piece `P` of `E^J` is connected. The piece `P` is irreducible (at each of its
points `E^J` is cut out by part of a regular system of parameters, a prime), so
`π⁻¹(P ∖ Z) ≅ P ∖ Z` is irreducible; and every point of `π⁻¹_*E^J` over `P` is a specialization
of a point of `π⁻¹_*E^J` off `F`, which lies in `π⁻¹(P ∖ Z)`. -/
private theorem connectedComponentIn_stratum_step_eq {X : Scheme.{u}} (C : MonomialData X)
    (hC : C.IsMonomialData) (hk : CharZero C.k) {m r : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m)
    (hmr : m ≤ C.maxStratumWeight r) {J : Finset (Fin (C.E.s + 1))} (hl : Fin.last C.E.s ∉ J)
    {x y : blowUp (C.stepCenter r)} (hx : x ∈ (C.step m r).stratum J)
    (hy : y ∈ (C.step m r).stratum J)
    (hxy : connectedComponentIn (C.stratum (castSuccPreimage J)) (blowUpToBase (C.stepCenter r) x) =
      connectedComponentIn (C.stratum (castSuccPreimage J)) (blowUpToBase (C.stepCenter r) y)) :
    connectedComponentIn ((C.step m r).stratum J) x =
      connectedComponentIn ((C.step m r).stratum J) y := by
  classical
  obtain ⟨-, -, -, hmd, -, -, h7⟩ :=
    MMP.Resolution.MonomialData.step_spec C hC hk (by omega : 1 ≤ r) hm hmr
  obtain ⟨-, hlft', -, hsnc', -⟩ := hmd
  haveI : LocallyOfFiniteType (C.step m r).sX := hlft'
  haveI : IsLocallyNoetherian (blowUp (C.stepCenter r)) :=
    LocallyOfFiniteType.isLocallyNoetherian (C.step m r).sX
  obtain ⟨-, hlft, hqc, hsnc, -⟩ := hC
  haveI : LocallyOfFiniteType C.sX := hlft
  haveI : QuasiCompact C.sX := hqc
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian C.sX
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace C.sX
  haveI : IsNoetherian X := {}
  set π := blowUpToBase (C.stepCenter r)
  set J₀ := castSuccPreimage J
  set S := C.stratum J₀
  set S' := (C.step m r).stratum J
  set Z : Set X := ((C.stepCenter r).support : Set X)
  have hF : ((((C.step m r).E.E (Fin.last C.E.s)).support : Set (blowUp (C.stepCenter r)))) =
      π ⁻¹' Z := h7 hr
  have hSc : IsClosed S := isClosed_biInter fun j _ => (C.E.E j).support.isClosed
  have hS'c : IsClosed S' :=
    isClosed_biInter fun j _ => ((C.step m r).E.E j).support.isClosed
  have hZo : IsOpen Zᶜ := (C.stepCenter r).support.isClosed.isOpen_compl
  -- the pieces of `E^{J₀}` are irreducible
  have hgen : ∀ w ∈ S, ∃ ξ ∈ S, ξ ⤳ w ∧ ∀ v ∈ S, v ⤳ w → ξ ⤳ v := by
    intro w hw
    have hw' : ∀ j ∈ J₀, w ∈ (C.E.E j).support := by
      simp only [S, MonomialData.stratum, Set.mem_iInter] at hw
      exact hw
    obtain ⟨n, z, c, hz, hc, hinj⟩ := hsnc.2.2 w
    obtain ⟨ξ, hξw, hξS, hξ, -⟩ := exists_generization_stratum C.E.E J₀ hz hc hinj hw'
    refine ⟨ξ, ?_, hξw, fun v hv hvw => hξ v ?_ hvw⟩
    · simp only [S, MonomialData.stratum, Set.mem_iInter]
      exact hξS
    · simp only [S, MonomialData.stratum, Set.mem_iInter] at hv
      exact hv
  have hπx : π x ∈ S := mem_stratum_castSuccPreimage C m r hx
  have hπy : π y ∈ S := mem_stratum_castSuccPreimage C m r hy
  set P := connectedComponentIn S (π x)
  obtain ⟨ξP, -, hPξ⟩ := connectedComponentIn_eq_closure_of_generization hSc hgen hπx
  have hPirr : IsPreirreducible P := by
    rw [show P = closure {ξP} from hPξ]
    exact isIrreducible_singleton.closure.isPreirreducible
  have hyP : π y ∈ P := hxy ▸ mem_connectedComponentIn hπy
  have hPc : IsClosed P := isClosed_connectedComponentIn hSc _
  have hPopen : ∀ v ∈ P, ∃ V : Set X, IsOpen V ∧ v ∈ V ∧ P ∩ V = S ∩ V := by
    intro v hv
    have h := exists_isOpen_closure_sUnion_inter_eq hSc (T := {P})
      (fun t ht => ⟨π x, hπx, ht⟩) (x := v) (by rw [Set.sUnion_singleton, hPc.closure_eq]; exact hv)
    rwa [Set.sUnion_singleton, hPc.closure_eq] at h
  -- `M = π⁻¹(P ∖ Z) ⊆ π⁻¹_*E^J` is preirreducible
  set M := π ⁻¹' (P ∩ Zᶜ)
  have hMS' : M ⊆ S' := by
    intro v hv
    simp only [S', MonomialData.stratum, Set.mem_iInter]
    intro j hj
    induction j using Fin.lastCases with
    | last => exact absurd hj hl
    | cast i =>
      change v ∈ (((C.step m r).E.E (Fin.castSucc i)).support : Set _)
      rw [coe_support_step_castSucc]
      refine subset_closure ⟨?_, fun h2 => hv.2 ?_⟩
      · have h := connectedComponentIn_subset _ _ hv.1
        simp only [S, MonomialData.stratum, Set.mem_iInter] at h
        exact h i (mem_castSuccPreimage.2 hj)
      · simp only [componentsOfCodimAtLeastTwo, Set.mem_iUnion] at h2
        obtain ⟨W, hW, -, hW'⟩ := h2
        exact hW.1.2 hW'
  have hPZ : IsPreirreducible (P ∩ Zᶜ) := by
    rintro u v hu hv ⟨a, ha, hau⟩ ⟨b, hb, hbv⟩
    obtain ⟨c, hcP, ⟨hcu, hcZ⟩, hcv, -⟩ := hPirr (u ∩ Zᶜ) (v ∩ Zᶜ) (hu.inter hZo)
      (hv.inter hZo) ⟨a, ha.1, hau, ha.2⟩ ⟨b, hb.1, hbv, hb.2⟩
    exact ⟨c, ⟨hcP, hcZ⟩, hcu, hcv⟩
  have hMirr : IsPreirreducible M := by
    set V₀ : X.Opens := ⟨Zᶜ, hZo⟩
    haveI : IsIso (π ∣_ V₀) := isIso_blowUp_restrict_compl_support (C.stepCenter r)
    have h1 : IsPreirreducible (V₀.ι ⁻¹' (P ∩ Zᶜ)) := hPZ.preimage V₀.ι.isOpenEmbedding
    have h2 : IsPreirreducible ((π ∣_ V₀) ⁻¹' (V₀.ι ⁻¹' (P ∩ Zᶜ))) :=
      h1.preimage (π ∣_ V₀).isOpenEmbedding
    have h3 := h2.image (π ⁻¹ᵁ V₀).ι (π ⁻¹ᵁ V₀).ι.continuous.continuousOn
    have hcomm : ∀ p, V₀.ι ((π ∣_ V₀) p) = π ((π ⁻¹ᵁ V₀).ι p) := fun p => by
      rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
    convert h3 using 1
    ext v
    constructor
    · intro hv
      have hv' : π v ∈ P ∧ π v ∈ Zᶜ := hv
      have hvU : v ∈ π ⁻¹ᵁ V₀ := hv'.2
      let p : (π ⁻¹ᵁ V₀).toScheme := ⟨v, hvU⟩
      refine ⟨p, ?_, rfl⟩
      change V₀.ι ((π ∣_ V₀) p) ∈ P ∩ Zᶜ
      rw [hcomm p]
      exact hv'
    · rintro ⟨p, hp, rfl⟩
      change V₀.ι ((π ∣_ V₀) p) ∈ P ∩ Zᶜ at hp
      rw [hcomm] at hp
      exact hp
  -- every point of `π⁻¹_*E^J` over `P` lies in the closure of `M`
  have hcl : ∀ v ∈ S', π v ∈ P → v ∈ closure M := by
    intro v hv hvP
    have hv' : ∀ j ∈ J, v ∈ ((C.step m r).E.E j).support := by
      simp only [S', MonomialData.stratum, Set.mem_iInter] at hv
      exact hv
    obtain ⟨n, z, c, hz, hc, hinj⟩ := hsnc'.2.2 v
    obtain ⟨ξ, hξv, hξS', -, hξF⟩ :=
      exists_generization_stratum (C.step m r).E.E J hz hc hinj hv'
    have hξS'' : ξ ∈ S' := by
      simp only [S', MonomialData.stratum, Set.mem_iInter]
      exact hξS'
    have hξZ : π ξ ∉ Z := by
      intro h
      apply hξF (Fin.last C.E.s) hl
      change ξ ∈ ((((C.step m r).E.E (Fin.last C.E.s)).support :
        Set (blowUp (C.stepCenter r))))
      rw [hF]
      exact h
    obtain ⟨V, hVo, hvV, hPV⟩ := hPopen _ hvP
    have hξV : π ξ ∈ V := (hξv.map π.continuous).mem_open hVo hvV
    have hξP : π ξ ∈ P := by
      have : π ξ ∈ S ∩ V := ⟨mem_stratum_castSuccPreimage C m r hξS'', hξV⟩
      rw [← hPV] at this
      exact this.1
    exact closure_mono (Set.singleton_subset_iff.2 (show ξ ∈ M from ⟨hξP, hξZ⟩))
      (specializes_iff_mem_closure.1 hξv)
  have hK := (isPreirreducible_iff_closure.2 hMirr).isPreconnected
  have hKS' : closure M ⊆ S' := closure_minimal hMS' hS'c
  have hxK := hcl x hx (mem_connectedComponentIn hπx)
  have hyK := hcl y hy hyP
  exact connectedComponentIn_eq (hK.subset_connectedComponentIn hxK hKS' hyK)

/-- Cases (a), (b), (c) for one new maximal piece `(J, P')`, `y ∈ P'`: `F` is not involved, `P'`
is the piece of `y`, and the piece of `π(y)` in `E^J` is a maximal piece of `E`. -/
private theorem isMaxPiece_of_isMaxPiece_step {X : Scheme.{u}} (C : MonomialData X)
    (hC : C.IsMonomialData) (hk : CharZero C.k) {m r : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m)
    (hlow : ∀ t, 1 ≤ t → t < r → C.maxStratumWeight t < m)
    (hmr : m ≤ C.maxStratumWeight r)
    (heq : (C.step m r).maxStratumWeight r = C.maxStratumWeight r)
    {J : Finset (Fin (C.E.s + 1))} {P : Set (blowUp (C.stepCenter r))}
    (hP : (C.step m r).IsMaxPiece r J P) {y : blowUp (C.stepCenter r)} (hy : y ∈ P) :
    Fin.last C.E.s ∉ J ∧ y ∈ (C.step m r).stratum J ∧
      P = connectedComponentIn ((C.step m r).stratum J) y ∧
      C.IsMaxPiece r (castSuccPreimage J)
        (connectedComponentIn (C.stratum (castSuccPreimage J))
          (blowUpToBase (C.stepCenter r) y)) := by
  have hfin : (Function.support C.A).Finite := hC.2.2.2.2.1
  obtain ⟨hJ, ⟨x, hx, rfl⟩, hw⟩ := hP
  have hyS : y ∈ (C.step m r).stratum J := connectedComponentIn_subset _ _ hy
  have hwy : (C.step m r).stratumWeight J y = C.maxStratumWeight r := (hw y hy).trans heq
  have hl : Fin.last C.E.s ∉ J := fun hl =>
    (stratumWeight_step_lt_of_last_mem C hC hk hr hm hlow hmr hJ hl hyS).ne hwy
  refine ⟨hl, hyS, (connectedComponentIn_eq hy), ?_⟩
  have hJ₀ : (castSuccPreimage J).card = r := (card_castSuccPreimage hl).trans hJ
  have hπy := mem_stratum_castSuccPreimage C m r hyS
  have h1 := stratumWeight_step_le_of_last_notMem C hC hk hr hm hmr hl y
  have h2 := stratumWeight_le_maxStratumWeight C hfin hJ₀ hπy
  refine ⟨hJ₀, ⟨_, hπy, rfl⟩, fun z hz => ?_⟩
  rw [C.stratumWeight_eq_of_mem_connectedComponentIn hC _ hπy hz]
  omega

open Classical in
/-- Cases (a) and (b): if `m_r` does not drop, the new maximal pieces are birational transforms
of old maximal pieces, injectively, and at least one old maximal piece (one of `E^{J_*}`, blown
up) is not hit. -/
private theorem exists_injOn_isMaxPiece_step {X : Scheme.{u}} (C : MonomialData X)
    (hC : C.IsMonomialData) (hk : CharZero C.k) {m r : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m)
    (hlow : ∀ t, 1 ≤ t → t < r → C.maxStratumWeight t < m)
    (hmr : m ≤ C.maxStratumWeight r)
    (heq : (C.step m r).maxStratumWeight r = C.maxStratumWeight r) :
    ∃ (f : Finset (Fin (C.step m r).E.s) × Set (blowUp (C.stepCenter r)) →
        Finset (Fin C.E.s) × Set X) (p₀ : Finset (Fin C.E.s) × Set X),
      C.IsMaxPiece r p₀.1 p₀.2 ∧
      Set.InjOn f {p | (C.step m r).IsMaxPiece r p.1 p.2} ∧
      Set.MapsTo f {p | (C.step m r).IsMaxPiece r p.1 p.2}
        ({p | C.IsMaxPiece r p.1 p.2} \ {p₀}) := by
  set π := blowUpToBase (C.stepCenter r)
  obtain ⟨P₀, hP₀⟩ := exists_isMaxPiece_stepIndex C hC (r := r) (by omega)
  let f : Finset (Fin (C.E.s + 1)) × Set (blowUp (C.stepCenter r)) →
      Finset (Fin C.E.s) × Set X := fun p =>
    (castSuccPreimage p.1, if h : p.2.Nonempty then
      connectedComponentIn (C.stratum (castSuccPreimage p.1)) (π h.some) else ∅)
  have hf : ∀ p : Finset (Fin (C.E.s + 1)) × Set (blowUp (C.stepCenter r)),
      (C.step m r).IsMaxPiece r p.1 p.2 → ∃ h : p.2.Nonempty,
        f p = (castSuccPreimage p.1,
          connectedComponentIn (C.stratum (castSuccPreimage p.1)) (π h.some)) := by
    rintro p ⟨-, ⟨x, hx, hP⟩, -⟩
    have hne : p.2.Nonempty := ⟨x, hP ▸ mem_connectedComponentIn hx⟩
    exact ⟨hne, by simp only [f, dif_pos hne]⟩
  refine ⟨f, (C.stepIndex r, P₀), hP₀, ?_, ?_⟩
  · rintro p hp q hq hpq
    obtain ⟨hpn, hfp⟩ := hf p hp
    obtain ⟨hqn, hfq⟩ := hf q hq
    obtain ⟨hlp, hyp, hPp, -⟩ :=
      isMaxPiece_of_isMaxPiece_step C hC hk hr hm hlow hmr heq hp hpn.some_mem
    obtain ⟨hlq, hyq, hPq, -⟩ :=
      isMaxPiece_of_isMaxPiece_step C hC hk hr hm hlow hmr heq hq hqn.some_mem
    rw [hfp, hfq, Prod.mk.injEq] at hpq
    have hJ : p.1 = q.1 := eq_of_castSuccPreimage_eq hlp hlq hpq.1
    refine Prod.ext hJ ?_
    rw [hPp, hPq]
    rw [← hJ] at hyq ⊢
    rw [hJ] at hpq
    exact connectedComponentIn_stratum_step_eq C hC hk hr hm hmr hlp hyp hyq (by
      rw [hJ]; exact hpq.2)
  · intro p hp
    obtain ⟨hpn, hfp⟩ := hf p hp
    obtain ⟨hlp, hyp, -, hmax⟩ :=
      isMaxPiece_of_isMaxPiece_step C hC hk hr hm hlow hmr heq hp hpn.some_mem
    refine ⟨by rw [hfp]; exact hmax, fun h => ?_⟩
    rw [hfp, Set.mem_singleton_iff, Prod.mk.injEq] at h
    refine notMem_stepCenter_of_mem_stratum_step C hC hk hr hm hmr hlp h.1 hyp ?_
    have hmem : π hpn.some ∈ P₀ := by
      rw [← h.2]
      exact mem_connectedComponentIn (mem_stratum_castSuccPreimage C m r hyp)
    rw [coe_support_stepCenter]
    exact subset_closure (Set.mem_sUnion_of_mem hmem hP₀)

/-- `m_r(E', A') ≤ m_r(E, A)`. -/
private theorem maxStratumWeight_step_le {X : Scheme.{u}} (C : MonomialData X)
    (hC : C.IsMonomialData) (hk : CharZero C.k) {m r : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m)
    (hlow : ∀ t, 1 ≤ t → t < r → C.maxStratumWeight t < m)
    (hmr : m ≤ C.maxStratumWeight r) :
    (C.step m r).maxStratumWeight r ≤ C.maxStratumWeight r := by
  conv_lhs => unfold MonomialData.maxStratumWeight
  refine ciSup_le' fun J => ciSup_le' fun hJ => ciSup_le' fun x => ciSup_le' fun hx => ?_
  by_cases hl : Fin.last C.E.s ∈ J
  · exact (stratumWeight_step_lt_of_last_mem C hC hk hr hm hlow hmr hJ hl hx).le
  · exact (stratumWeight_step_le_of_last_notMem C hC hk hr hm hmr hl x).trans
      (stratumWeight_le_maxStratumWeight C hC.2.2.2.2.1 ((card_castSuccPreimage hl).trans hJ)
        (mem_stratum_castSuccPreimage C m r hx))

end MMP.Proofs.lem_kr3e_monomial_step_decreases

namespace MMP.Resolution

namespace MonomialData

open MMP.Proofs.lem_kr3e_monomial_step_decreases in
/-- **The Step-3.`r` blow-up lowers `(m_r, n_r)`** (Kollár 3.111, Steps 3.2, 3.`r`). For monomial
data `C = (X, E, A)` over a field of characteristic `0`, `2 ≤ r` and `1 ≤ m ≤ m_r(E, A)` with
`m_t(E, A) < m` for all `1 ≤ t < r`, the Step-3.`r` blow-up `C.step m r` satisfies
`(m_r(E', A'), n_r(E', A')) <_lex (m_r(E, A), n_r(E, A))`. -/
@[mmp "lem_kr3e_monomial_step_decreases"]
public theorem toLex_maxStratumWeight_maxStratumCount_step_lt {X : Scheme.{u}}
    (C : MonomialData X) (hC : C.IsMonomialData) (hk : CharZero C.k)
    {m r : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m)
    (hlow : ∀ t, 1 ≤ t → t < r → C.maxStratumWeight t < m)
    (hmr : m ≤ C.maxStratumWeight r) :
    toLex ((C.step m r).maxStratumWeight r, (C.step m r).maxStratumCount r) <
      toLex (C.maxStratumWeight r, C.maxStratumCount r) := by
  rw [Prod.Lex.toLex_lt_toLex]
  rcases (maxStratumWeight_step_le C hC hk hr hm hlow hmr).lt_or_eq with hlt | heq
  · exact Or.inl hlt
  · refine Or.inr ⟨heq, ?_⟩
    obtain ⟨f, p₀, hp₀, hinj, hmaps⟩ :=
      exists_injOn_isMaxPiece_step C hC hk hr hm hlow hmr heq
    exact (Set.ncard_le_ncard_of_injOn f hmaps hinj (finite_isMaxPiece C hC r).diff).trans_lt
      (Set.ncard_diff_singleton_lt_of_mem hp₀ (finite_isMaxPiece C hC r))

end MonomialData

end MMP.Resolution

end

/-!
### Termination of the Step-3.1 blow-ups of monomial data

Let `(X, E, A)` be monomial data over a field `k` of characteristic zero and `m ≥ 1`. A Step-3.1
blow-up blows up the
union `Z` of the components of the members of `E` whose coefficient in `A` is maximal, equal to
`m_1(E, A)`; when `m_1(E, A) ≥ m` it leaves `X` and `E` unchanged and lowers the coefficients of
the components in `Z` by `m`. Since the coefficients are natural numbers, finitely many of them
nonzero, their sum strictly decreases, so after finitely many Step-3.1 blow-ups one reaches data
`C_N` with `m_1(C_N) < m`. In particular the Step-3.1 sequence
`MMP.Resolution.MonomialData.stepSequence m 1` is not replaced by the empty sequence.

### Main results

* `MMP.Resolution.MonomialData.exists_maxStratumWeight_iterate_one_lt`: for monomial data `C`
  over a field of characteristic zero and `1 ≤ m`, some iterate `C.iterate m 1 N` has `m_1 < m`.

### Implementation notes

The hypothesis `CharZero C.k` is the standing characteristic-zero convention of Kollár's §3;
it is the hypothesis under which the description of a single Step-3.1 blow-up,
`MMP.Resolution.MonomialData.step_spec`, is available.

### References

* [J. Kollár, *Lectures on resolution of singularities*, 3.111, Step 3.1]
-/

section

open CategoryTheory AlgebraicGeometry MMP.Resolution MMP.Resolution.MonomialData

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Proofs.lem_kr3e_monomial_step_one_terminates

/-- The open immersion `π⁻¹(X ∖ Z) → X` induced by the blow-up `π : B_Z X → X`. -/
private theorem isOpenImmersion_ι_comp_blowUpToBase {X : Scheme.{u}} (Z : X.IdealSheafData) :
    IsOpenImmersion ((blowUpToBase Z ⁻¹ᵁ
      (⟨(Z.support : Set X)ᶜ, Z.support.isClosed.isOpen_compl⟩ : X.Opens)).ι ≫
        blowUpToBase Z) := by
  haveI := isIso_blowUp_restrict_compl_support Z
  rw [← morphismRestrict_ι]
  infer_instance

/-- A prime divisor of `B_Z X` not lying over `Z` maps its generic point to the generic point of
a prime divisor of `X`. -/
private theorem exists_genericPoint_eq_of_notMem_support {X : Scheme.{u}} (Z : X.IdealSheafData)
    (D' : AlgebraicGeometry.PrimeDivisor (blowUp Z))
    (h : blowUpToBase Z D'.genericPoint ∉ (Z.support : Set X)) :
    ∃ D : AlgebraicGeometry.PrimeDivisor X, blowUpToBase Z D'.genericPoint = D.genericPoint := by
  set U : X.Opens := ⟨(Z.support : Set X)ᶜ, Z.support.isClosed.isOpen_compl⟩
  haveI := isOpenImmersion_ι_comp_blowUpToBase Z
  let y : (blowUpToBase Z ⁻¹ᵁ U : Scheme) := ⟨D'.genericPoint, h⟩
  have hc : Order.coheight (blowUpToBase Z D'.genericPoint) = 1 := by
    have h1 : ((blowUpToBase Z ⁻¹ᵁ U).ι ≫ blowUpToBase Z) y = blowUpToBase Z D'.genericPoint :=
      rfl
    have h2 : (blowUpToBase Z ⁻¹ᵁ U).ι y = D'.genericPoint := rfl
    rw [← h1, coheight_eq_of_isOpenImmersion, ← coheight_eq_of_isOpenImmersion
      (blowUpToBase Z ⁻¹ᵁ U).ι, h2]
    exact D'.coheight_genericPoint
  exact ⟨.ofCoheightOne _ hc, (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hc).symm⟩

/-- The blow-up is injective on the generic points of prime divisors not lying over `Z`. -/
private theorem eq_of_blowUpToBase_genericPoint_eq {X : Scheme.{u}} (Z : X.IdealSheafData)
    {D₁ D₂ : AlgebraicGeometry.PrimeDivisor (blowUp Z)}
    (h₁ : blowUpToBase Z D₁.genericPoint ∉ (Z.support : Set X))
    (h : blowUpToBase Z D₁.genericPoint = blowUpToBase Z D₂.genericPoint) : D₁ = D₂ := by
  set U : X.Opens := ⟨(Z.support : Set X)ᶜ, Z.support.isClosed.isOpen_compl⟩
  have h₂ : blowUpToBase Z D₂.genericPoint ∉ (Z.support : Set X) := h ▸ h₁
  let y₁ : (blowUpToBase Z ⁻¹ᵁ U : Scheme) := ⟨D₁.genericPoint, h₁⟩
  let y₂ : (blowUpToBase Z ⁻¹ᵁ U : Scheme) := ⟨D₂.genericPoint, h₂⟩
  haveI := isOpenImmersion_ι_comp_blowUpToBase Z
  have : y₁ = y₂ :=
    ((blowUpToBase Z ⁻¹ᵁ U).ι ≫ blowUpToBase Z).isOpenEmbedding.injective h
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (congrArg Subtype.val this)

private theorem genericPoint_mem_support {X : Scheme.{u}}
    (D : AlgebraicGeometry.PrimeDivisor X) : D.genericPoint ∈ D.support := by
  rw [D.support_eq_closure]
  exact subset_closure rfl

variable {X : Scheme.{u}} (C : MonomialData X)

/-- For monomial data, `a_j(x)` is the coefficient of the component of `E^j` through `x`. -/
private theorem coeffAt_eq (hC : C.IsMonomialData) {j : Fin C.E.s} {x : X}
    {D : AlgebraicGeometry.PrimeDivisor X}
    (hD : D.support ∈ componentsOf ((C.E.E j).support : Set X)) (hx : x ∈ D.support) :
    C.coeffAt j x = C.A D := by
  classical
  obtain ⟨-, hlft, -, hsnc, -, -⟩ := hC
  haveI : LocallyOfFiniteType C.sX := hlft
  unfold coeffAt
  rw [finsum_eq_single _ D]
  · simp [hD, hx]
  · intro D₂ hne
    rw [if_neg]
    rintro ⟨hD₂, hx₂⟩
    exact hne (Aux.PrimeDivisor.eq_of_support_eq
      (Aux.eq_of_mem_componentsOf_of_isSmoothScheme C.sX _ (hsnc.2.1 j).2.2 hD₂ hD hx₂ hx))

/-- If no component of `E^j` passes through `x`, then `a_j(x) = 0`. -/
private theorem coeffAt_eq_zero {j : Fin C.E.s} {x : X}
    (h : ∀ D : AlgebraicGeometry.PrimeDivisor X,
      D.support ∈ componentsOf ((C.E.E j).support : Set X) → x ∉ D.support) :
    C.coeffAt j x = 0 := by
  classical
  unfold coeffAt
  exact finsum_eq_zero_of_forall_eq_zero fun D => if_neg fun hD => h D hD.1 hD.2

/-- Only finitely many prime divisors have a given nonzero coefficient. -/
private theorem finite_setOf_A_eq (hC : C.IsMonomialData) {b : ℕ} (hb0 : b ≠ 0) :
    {D | C.A D = b}.Finite :=
  hC.2.2.2.2.1.subset fun D (hD : C.A D = b) => by simp [hD, hb0]

private theorem coeffAt_le (hC : C.IsMonomialData) {b : ℕ} (hb : ∀ D, C.A D ≤ b)
    (j : Fin C.E.s) (x : X) : C.coeffAt j x ≤ b := by
  by_cases h : ∃ D : AlgebraicGeometry.PrimeDivisor X,
      D.support ∈ componentsOf ((C.E.E j).support : Set X) ∧ x ∈ D.support
  · obtain ⟨D, hD, hx⟩ := h
    rw [coeffAt_eq C hC hD hx]
    exact hb D
  · push Not at h
    rw [coeffAt_eq_zero C h]
    exact Nat.zero_le _

private theorem stratumWeight_le (hC : C.IsMonomialData) {b : ℕ} (hb : ∀ D, C.A D ≤ b)
    {J : Finset (Fin C.E.s)} (hJ : J.card = 1) (x : X) : C.stratumWeight J x ≤ b := by
  obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hJ
  simpa [stratumWeight] using coeffAt_le C hC hb j x

private theorem maxStratumWeight_le (hC : C.IsMonomialData) {b : ℕ} (hb : ∀ D, C.A D ≤ b) :
    C.maxStratumWeight 1 ≤ b := by
  unfold maxStratumWeight
  refine ciSup_le' fun J => ciSup_le' fun hJ => ciSup_le' fun x => ciSup_le' fun _ => ?_
  exact stratumWeight_le C hC hb hJ x

private theorem coeffAt_le_maxStratumWeight (hC : C.IsMonomialData) {b : ℕ}
    (hb : ∀ D, C.A D ≤ b) {j : Fin C.E.s} {x : X} (hx : x ∈ ((C.E.E j).support : Set X)) :
    C.coeffAt j x ≤ C.maxStratumWeight 1 := by
  have hxs : x ∈ C.stratum {j} := by simpa [stratum] using hx
  have hw : C.stratumWeight {j} x = C.coeffAt j x := by simp [stratumWeight]
  unfold maxStratumWeight
  refine le_ciSup_of_le ⟨b, ?_⟩ {j} ?_
  · rintro _ ⟨J, rfl⟩
    exact ciSup_le' fun hJ => ciSup_le' fun x => ciSup_le' fun _ => stratumWeight_le C hC hb hJ x
  refine le_ciSup_of_le ⟨b, ?_⟩ (Finset.card_singleton j) ?_
  · rintro _ ⟨hJ, rfl⟩
    exact ciSup_le' fun x => ciSup_le' fun _ => stratumWeight_le C hC hb hJ x
  refine le_ciSup_of_le ⟨b, ?_⟩ x ?_
  · rintro _ ⟨y, rfl⟩
    exact ciSup_le' fun _ => stratumWeight_le C hC hb (Finset.card_singleton j) y
  refine le_ciSup_of_le ⟨b, ?_⟩ hxs ?_
  · rintro _ ⟨_, rfl⟩
    exact stratumWeight_le C hC hb (Finset.card_singleton j) x
  rw [hw]

/-- If a coefficient attains the bound `b`, then `m_1 = b` and some component `D₀` of a member of
`E` with `a_{D₀} = b` has its generic point in the Step-3.1 centre. -/
private theorem exists_coeff_eq_mem_stepCenter (hC : C.IsMonomialData) {b : ℕ}
    (hb : ∀ D, C.A D ≤ b) {D₁ : AlgebraicGeometry.PrimeDivisor X} (hD₁ : C.A D₁ = b)
    (hb0 : b ≠ 0) :
    C.maxStratumWeight 1 = b ∧ ∃ D₀ : AlgebraicGeometry.PrimeDivisor X, C.A D₀ = b ∧
      D₀.genericPoint ∈ ((C.stepCenter 1).support : Set X) := by
  classical
  obtain ⟨j, hj⟩ := hC.2.2.2.2.2 D₁ (hD₁ ▸ hb0)
  have hη : D₁.genericPoint ∈ ((C.E.E j).support : Set X) :=
    MMP.Proofs.lem_kr3e_monomial_stratum_blowup.subset_of_mem_componentsOf hj
      (genericPoint_mem_support D₁)
  have hc₁ : C.coeffAt j D₁.genericPoint = b :=
    (coeffAt_eq C hC hj (genericPoint_mem_support D₁)).trans hD₁
  have hmax : C.maxStratumWeight 1 = b :=
    le_antisymm (maxStratumWeight_le C hC hb) (hc₁ ▸ coeffAt_le_maxStratumWeight C hC hb hη)
  refine ⟨hmax, ?_⟩
  -- a max piece of `E^{J_*}`
  have hS : (Finset.univ.filter fun J => ∃ P, C.IsMaxPiece 1 J P).Nonempty := by
    refine ⟨{j}, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    have hxs : D₁.genericPoint ∈ C.stratum {j} := by simpa [stratum] using hη
    refine ⟨connectedComponentIn (C.stratum {j}) D₁.genericPoint, Finset.card_singleton j,
      ⟨_, hxs, rfl⟩, fun y hy => ?_⟩
    rw [stratumWeight_eq_of_mem_connectedComponentIn C hC {j} hxs hy, hmax]
    simpa [stratumWeight] using hc₁
  have hP : ∃ P, C.IsMaxPiece 1 (C.stepIndex 1) P := by
    unfold stepIndex
    simp only
    rw [dif_pos hS]
    exact (Finset.mem_filter.mp (Finset.exists_min_image _ _ hS).choose_spec.1).2
  obtain ⟨P, hcard, ⟨x, hx, rfl⟩, hw⟩ := hP
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
  have hcx : C.coeffAt i x = b := by
    simpa [hi, stratumWeight, hmax] using hw x (mem_connectedComponentIn hx)
  have hex : ∃ D₀ : AlgebraicGeometry.PrimeDivisor X,
      D₀.support ∈ componentsOf ((C.E.E i).support : Set X) ∧ x ∈ D₀.support := by
    by_contra hne
    push Not at hne
    exact hb0 (hcx ▸ coeffAt_eq_zero C hne)
  obtain ⟨D₀, hD₀, hxD₀⟩ := hex
  refine ⟨D₀, (coeffAt_eq C hC hD₀ hxD₀).symm.trans hcx, ?_⟩
  have hsub : D₀.support ⊆ connectedComponentIn (C.stratum (C.stepIndex 1)) x := by
    refine IsPreconnected.subset_connectedComponentIn ?_ hxD₀ ?_
    · rw [D₀.support_eq_closure]
      exact isPreconnected_singleton.closure
    · rw [hi]
      simpa [stratum] using
        MMP.Proofs.lem_kr3e_monomial_stratum_blowup.subset_of_mem_componentsOf hD₀
  rw [stepCenter, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  exact subset_closure (Set.mem_sUnion.mpr ⟨_, ⟨hcard, ⟨x, hx, rfl⟩, hw⟩,
    hsub (genericPoint_mem_support D₀)⟩)

/-- **One Step-3.1 blow-up.** Every coefficient of `C.step m 1` is `≤ b`. If some coefficient of
`C` equals `b`, the number of prime divisors with coefficient `b` strictly drops. -/
private theorem step_bound (hC : C.IsMonomialData) (hk : CharZero C.k) {m : ℕ} (hm : 1 ≤ m)
    (hmr : m ≤ C.maxStratumWeight 1) {b : ℕ} (hb : ∀ D, C.A D ≤ b)
    {D₁ : AlgebraicGeometry.PrimeDivisor X} (hD₁ : C.A D₁ = b) :
    (∀ D', (C.step m 1).A D' ≤ b) ∧
      {D' | (C.step m 1).A D' = b}.ncard < {D | C.A D = b}.ncard := by
  classical
  have hmb := maxStratumWeight_le C hC hb
  have hb0 : b ≠ 0 := by omega
  obtain ⟨hmax, D₀, hD₀, hD₀Z⟩ := exists_coeff_eq_mem_stepCenter C hC hb hD₁ hb0
  have spec := step_spec C hC hk (le_refl 1) hm hmr
  have htr := spec.2.2.2.2.1
  have hover := spec.2.2.2.2.2.1
  set Z := C.stepCenter 1
  have hle : ∀ D', (C.step m 1).A D' ≤ b := by
    intro D'
    by_cases hz : blowUpToBase Z D'.genericPoint ∈ (Z.support : Set X)
    · rw [hover D' hz]; omega
    · obtain ⟨D, hD⟩ := exists_genericPoint_eq_of_notMem_support Z D' hz
      rw [htr D D' hD]
      have := hb D
      split_ifs <;> omega
  refine ⟨hle, ?_⟩
  have hfin := finite_setOf_A_eq C hC hb0
  have hex : ∀ D' : AlgebraicGeometry.PrimeDivisor (blowUp Z),
      ∃ D : AlgebraicGeometry.PrimeDivisor X,
      blowUpToBase Z D'.genericPoint ∉ (Z.support : Set X) →
        blowUpToBase Z D'.genericPoint = D.genericPoint := by
    intro D'
    by_cases h : blowUpToBase Z D'.genericPoint ∈ (Z.support : Set X)
    · exact ⟨D₀, absurd h⟩
    · obtain ⟨D, hD⟩ := exists_genericPoint_eq_of_notMem_support Z D' h
      exact ⟨D, fun _ => hD⟩
  choose f hf using hex
  have hnz : ∀ D' ∈ {D' | (C.step m 1).A D' = b},
      blowUpToBase Z D'.genericPoint ∉ (Z.support : Set X) := by
    intro D' hD' hz
    simp only [Set.mem_setOf_eq] at hD'
    rw [hover D' hz, hmax] at hD'
    omega
  calc {D' | (C.step m 1).A D' = b}.ncard ≤ ({D | C.A D = b} \ {D₀}).ncard := by
        refine Set.ncard_le_ncard_of_injOn f ?_ ?_ (hfin.diff)
        · intro D' hD'
          have hz := hnz D' hD'
          have hfD := hf D' hz
          have hA := htr (f D') D' hfD
          simp only [Set.mem_setOf_eq] at hD'
          refine ⟨?_, ?_⟩
          · simp only [Set.mem_setOf_eq]
            have := hb (f D')
            split_ifs at hA <;> omega
          · rintro rfl
            exact hz (hfD ▸ hD₀Z)
        · intro D₂ h₂ D₃ h₃ heq
          have hz₂ := hnz D₂ h₂
          exact eq_of_blowUpToBase_genericPoint_eq Z hz₂
            ((hf D₂ hz₂).trans ((congrArg _ heq).trans (hf D₃ (hnz D₃ h₃)).symm))
    _ < {D | C.A D = b}.ncard := Set.ncard_diff_singleton_lt_of_mem hD₀ hfin

/-- The induction behind `solution`: on the bound `b`, then on the number of prime divisors
with coefficient `b`. -/
private theorem exists_iterate_lt {m : ℕ} (hm : 1 ≤ m) (b : ℕ) :
    ∀ (n : ℕ) {X : Scheme.{u}} (C : MonomialData X), C.IsMonomialData → CharZero C.k →
      (∀ D, C.A D ≤ b) → {D | C.A D = b}.ncard ≤ n →
      ∃ N : ℕ, (C.iterate m 1 N).2.maxStratumWeight 1 < m := by
  induction b with
  | zero =>
    intro n X C hC _ hb _
    exact ⟨0, lt_of_le_of_lt (maxStratumWeight_le C hC hb) hm⟩
  | succ b ihb =>
    intro n
    induction n with
    | zero =>
      intro X C hC hk hb hn
      have hemp :=
        (Set.ncard_eq_zero (finite_setOf_A_eq C hC (b := b + 1) (by omega))).mp (by omega)
      refine ihb _ C hC hk (fun D => Nat.le_of_lt_succ ((hb D).lt_of_ne fun h => ?_)) le_rfl
      exact (hemp ▸ h : D ∈ (∅ : Set _))
    | succ n ihn =>
      intro X C hC hk hb hn
      by_cases hlt : C.maxStratumWeight 1 < m
      · exact ⟨0, hlt⟩
      by_cases hex : ∃ D, C.A D = b + 1
      · obtain ⟨D₁, hD₁⟩ := hex
        obtain ⟨hle, hcnt⟩ := step_bound C hC hk hm (not_lt.mp hlt) hb hD₁
        obtain ⟨N, hN⟩ := ihn (C.step m 1)
          (step_spec C hC hk (le_refl 1) hm (not_lt.mp hlt)).2.2.2.1 hk hle (by omega)
        exact ⟨N + 1, hN⟩
      · push Not at hex
        exact ihb _ C hC hk (fun D => by have := hb D; have := hex D; omega) le_rfl

end MMP.Proofs.lem_kr3e_monomial_step_one_terminates

namespace MMP.Resolution

namespace MonomialData

open MMP.Proofs.lem_kr3e_monomial_step_one_terminates in
/-- **Step 3.1 terminates** (Kollár 3.111, Step 3.1). For monomial data `C = (X, E, A)` over a
field of characteristic zero and `1 ≤ m`, iterating the Step-3.1 blow-up
`MonomialData.step m 1` reaches, after finitely many
steps, data `C_N = C.iterate m 1 N` with `m_1(C_N) < m`. -/
@[mmp "lem_kr3e_monomial_step_one_terminates"]
public theorem exists_maxStratumWeight_iterate_one_lt {X : Scheme.{u}} (C : MonomialData X)
    (hC : C.IsMonomialData) (hk : CharZero C.k) {m : ℕ} (hm : 1 ≤ m) :
    ∃ N : ℕ, (C.iterate m 1 N).2.maxStratumWeight 1 < m := by
  obtain ⟨b, hb⟩ : ∃ b, ∀ D, C.A D ≤ b := by
    obtain ⟨b, hb⟩ := (hC.2.2.2.2.1.image C.A).bddAbove
    refine ⟨b, fun D => ?_⟩
    by_cases hD : C.A D = 0
    · omega
    · exact hb ⟨D, hD, rfl⟩
  exact exists_iterate_lt hm b _ C hC hk hb le_rfl

end MonomialData

end MMP.Resolution

end
