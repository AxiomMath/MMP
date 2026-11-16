module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
public import MMP.AlgebraicGeometry.MMP.Fourfold.LogMinimalModel
import MMP.AlgebraicGeometry.Singularities.Adjunction.DltStratum
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Resolution.BirationalTransformTriple
import MMP.AlgebraicGeometry.Resolution.DisjoiningCenter
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Singularities.SncStrata.ZeroPlaceExtraction
import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Bertini.ReducedGeneralMember
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeLineBundle
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction
import StacksFrontier.AlgebraicGeometry.Limits.ProjectiveSpace
import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso
import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceZero
import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
import StacksFrontier.AlgebraicGeometry.FiniteMorphismProjective.Projective
import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Composition
import MMP.AlgebraicGeometry.MMP.Fourfold.Defs
import MMP.AlgebraicGeometry.Divisor.PullbackExistence
import MMP.AlgebraicGeometry.Singularities.LogResolution.ReducedUnion
import MMP.AlgebraicGeometry.Divisor.SNC
import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.Sequence
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Divisor.SmoothDivisorRestriction
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferent
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueLift
import MMP.AlgebraicGeometry.Singularities.Adjunction.SmoothDivisorResidueRestriction
import MMP.AlgebraicGeometry.Singularities.Adjunction.PoincareResidueSmoothDivisor
import MMP.AlgebraicGeometry.Resolution.DivisorTupleRestrictionLift
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.Divisor.SectionAlgebra.Cartier
import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres
import MMP.AlgebraicGeometry.Singularities.Surface.PointBlowupLogDiscrepancy
import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
import MMP.AlgebraicGeometry.Singularities.CrepantBoundaryPushforward
import MMP.AlgebraicGeometry.Resolution.Blowup.ProjectiveBirationalIsBlowup
import MMP.AlgebraicGeometry.Resolution.Principalization.ResolutionPrincipalization
import MMP.AlgebraicGeometry.Divisor.EffectiveCartierCoheight
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBoundaryChange
public import MMP.AlgebraicGeometry.Morphisms.HProjective
public import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport

/-!
# Section reduction for a floor stratum of a crepant snc model

Let `h : (Y, C) → (X, B)` be a projective birational morphism of smooth projective varieties
carrying snc subboundaries (rational coefficients at most one), with `K_Y + C = h^*(K_X + B)`.
The *floor strata* are the strata of the reduced coefficient-one parts `C^{=1}`, `B^{=1}`. For a
proper floor stratum `W ⊂ Y` with image `Z = h(W)`, the image `Z` is a floor stratum of `X`, and
there is a floor stratum `F ⊆ W` mapping birationally onto `Z` such that restriction
`H⁰(W, 𝒪_Y(m(K_Y + C))|_W) → H⁰(F, 𝒪_Y(m(K_Y + C))|_F)` is bijective for every even `m > 0`
with `mB` integral; moreover `F → Z` is crepant from the snc restriction
`(F, C_F)`, `C_F = (C - ∑_{G ⊇ F} G)|_F`, to the iterated adjunction pairs on `Z`.

## Main results

* `MMP.Fourfold.IsSNCSubboundaryPair.isSNCStratum_image_and_exists_bijective_restriction`.

## Implementation notes

The strata `W`, `Z`, `F` are reduced closed subschemes, given by closed immersions. The sheaf
`𝒪_Y(m(K_Y + C))` is the divisorial sheaf of `mK_Y + ⌊mC⌋`, which is `m(K_Y + C)` once `mC` is
integral, and its restriction to `W` is the pull-back along `W ⟶ Y`; the restriction to `F ⊆ W`
is the unit of the pull-back/push-forward adjunction along `F ⟶ W` on global sections.
The boundary on `F` is the snc restriction `C_F`, the pull-back
(`MMP.Mori.QDivisor.IsPullback`) along `F ⟶ Y` of `C` minus the components of `C^{=1}`
containing `F`; no component of that divisor contains `F`, so the pull-back is defined. Since
`C` is only a subboundary, flags of iterated adjunction out of `(Y, C)` need not exist (an
adjunction step requires an effective difference), so the boundary on `F` is not taken from
such flags. The iterated adjunction pairs on `Z` are the final pairs of the flags of iterated
adjunction (`MMP.Fourfold.StratumAdjunctionData`) ending at `Z`; crepancy is asserted for every
such flag, through the crepant boundary `MMP.Mori.IsCrepantBoundary`. The base field is
an algebraically closed field of characteristic zero; the source works over `ℂ`.
-/

@[expose] public section

section

namespace Proof_lem_fourfold_crepant_snc_stratum_section_reduction

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### Closed subschemes with reduced sources and equal ranges -/

/-- A closed immersion with reduced source, whose ideal contains the kernel of `i` and whose
support is the range of `i`, is isomorphic to its source. -/
private lemma exists_iso_subscheme {A P : Scheme.{0}} (i : A ⟶ P) [IsClosedImmersion i]
    [IsReduced A] (K : P.IdealSheafData) (hK : i.ker ≤ K)
    (hs : (K.support : Set P) = Set.range i) :
    ∃ e : K.subscheme ≅ A, e.hom ≫ i = K.subschemeι := by
  let a : K.subscheme ⟶ A := IsClosedImmersion.lift i K.subschemeι (by rwa [K.ker_subschemeι])
  have ha : a ≫ i = K.subschemeι := IsClosedImmersion.lift_fac _ _ _
  have : IsClosedImmersion a := by
    have : IsClosedImmersion (a ≫ i) := by rw [ha]; infer_instance
    exact IsClosedImmersion.of_comp_isClosedImmersion a i
  have : Surjective a := ⟨fun x => by
    obtain ⟨c, hc⟩ : i x ∈ Set.range K.subschemeι := by
      rw [Scheme.IdealSheafData.range_subschemeι, hs]; exact ⟨x, rfl⟩
    exact ⟨c, i.isEmbedding.injective (by rw [← Scheme.Hom.comp_apply, ha]; exact hc)⟩⟩
  have := isIso_of_isClosedImmersion_of_surjective a
  exact ⟨asIso a, ha⟩

/-- Two closed immersions with reduced sources and the same range are isomorphic over the
target. -/
private lemma exists_iso_of_range_eq {A B P : Scheme.{0}} (i₁ : A ⟶ P) (i₂ : B ⟶ P)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsReduced A] [IsReduced B]
    (h : Set.range i₁ = Set.range i₂) : ∃ e : A ≅ B, e.hom ≫ i₂ = i₁ := by
  let K : P.IdealSheafData := i₁.ker ⊔ i₂.ker
  have hK : (K.support : Set P) = Set.range i₁ := by
    simp only [K, Scheme.IdealSheafData.support_sup, TopologicalSpace.Closeds.coe_inf,
      Scheme.Hom.support_ker, i₁.isClosedEmbedding.isClosed_range.closure_eq,
      i₂.isClosedEmbedding.isClosed_range.closure_eq, ← h, Set.inter_self]
  obtain ⟨e₁, h₁⟩ := exists_iso_subscheme i₁ K le_sup_left hK
  obtain ⟨e₂, h₂⟩ := exists_iso_subscheme i₂ K le_sup_right (hK.trans h)
  refine ⟨e₁.symm ≪≫ e₂, ?_⟩
  simp [h₂, ← h₁]

/-- **Lifting through a closed immersion.** A quasi-compact morphism `φ : F ⟶ X` from a reduced
scheme whose image lies in the range of a closed immersion `ι : Z ⟶ X` factors through `ι`: its
scheme-theoretic image is reduced and is a closed subscheme of `Z`. -/
private lemma exists_comp_eq_of_range_subset {F Z X : Scheme.{0}} [IsReduced F] [IsReduced Z]
    (ι : Z ⟶ X) [IsClosedImmersion ι] (φ : F ⟶ X) [QuasiCompact φ]
    (hφ : Set.range φ ⊆ Set.range ι) : ∃ g : F ⟶ Z, g ≫ ι = φ := by
  haveI : IsSchemeTheoreticallyDominant φ.toImage := inferInstance
  haveI : IsReduced φ.image := IsSchemeTheoreticallyDominant.isReduced φ.toImage
  let K : X.IdealSheafData := ι.ker ⊔ φ.imageι.ker
  have hrange : Set.range φ.imageι = closure (Set.range φ) := by
    rw [← Scheme.Hom.support_ker]
    exact φ.ker.range_subschemeι
  have hK : (K.support : Set X) = Set.range φ.imageι := by
    simp only [K, Scheme.IdealSheafData.support_sup, TopologicalSpace.Closeds.coe_inf,
      Scheme.Hom.support_ker, ι.isClosedEmbedding.isClosed_range.closure_eq,
      φ.imageι.isClosedEmbedding.isClosed_range.closure_eq]
    refine Set.inter_eq_right.mpr ?_
    rw [hrange]
    exact closure_minimal hφ ι.isClosedEmbedding.isClosed_range
  obtain ⟨e, he⟩ := exists_iso_subscheme φ.imageι K le_sup_right hK
  let l : K.subscheme ⟶ Z := IsClosedImmersion.lift ι K.subschemeι (by
    rw [K.ker_subschemeι]; exact le_sup_left)
  refine ⟨φ.toImage ≫ e.inv ≫ l, ?_⟩
  rw [Category.assoc, Category.assoc, IsClosedImmersion.lift_fac, ← he, Iso.inv_hom_id_assoc,
    Scheme.Hom.toImage_imageι]

/-- Birationality of a morphism between integral closed subschemes is unchanged when source and
target are replaced by reduced closed subschemes with the same ranges. -/
private lemma isBirationalMorphism_of_range_eq {Y X F Z S T : Scheme.{0}}
    (ιF : F ⟶ Y) (ιZ : Z ⟶ X) (ιS : S ⟶ Y) (ιT : T ⟶ X) [IsClosedImmersion ιF]
    [IsClosedImmersion ιZ] [IsClosedImmersion ιS] [IsClosedImmersion ιT] [IsReduced F]
    [IsReduced Z] [IsIntegral S] [IsIntegral T] (h : Y ⟶ X) (g : F ⟶ Z)
    (hg : g ≫ ιZ = ιF ≫ h) (hgb : IsBirationalMorphism g)
    (hS : Set.range ιS = Set.range ιF) (hT : Set.range ιT = Set.range ιZ)
    (gST : S ⟶ T) (hgST : gST ≫ ιT = ιS ≫ h) : IsBirationalMorphism gST := by
  obtain ⟨e₁, he₁⟩ := exists_iso_of_range_eq ιS ιF hS
  obtain ⟨e₂, he₂⟩ := exists_iso_of_range_eq ιZ ιT hT.symm
  have hgST' : gST = e₁.hom ≫ g ≫ e₂.hom := by
    rw [← cancel_mono ιT, hgST, Category.assoc, Category.assoc, he₂, hg, ← Category.assoc,
      he₁]
  haveI : IrreducibleSpace F :=
    (Scheme.homeoOfIso e₁).surjective.irreducibleSpace (Scheme.homeoOfIso e₁).continuous
  haveI : IrreducibleSpace Z := (Scheme.homeoOfIso e₂.symm).surjective.irreducibleSpace
    (Scheme.homeoOfIso e₂.symm).continuous
  rw [hgST']
  exact isBirationalMorphism_comp (isBirationalMorphism_of_isIso _)
    (isBirationalMorphism_comp hgb (isBirationalMorphism_of_isIso _))

/-! ### Strata of snc divisors -/

/-- At a point `x` of a scheme with an snc divisor `D`, at most `codim x` prime components of `D`
pass through `x`, and `codim x` is finite. -/
private lemma card_le_coheight_of_isSNC {R : Type*} [Zero R] {k : Type} [Field k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {D : DivisorWithCoeffs R X} (hD : D.IsSNC sX)
    (x : X) (T : Finset (MMP.Mori.PrimeDivisor X)) (hT : T ⊆ D.support)
    (hx : ∀ G ∈ T, x ∈ G.support) :
    ∃ c : ℕ, Order.coheight x = c ∧ T.card ≤ c := by
  classical
  obtain ⟨c, z, j, hz, hj, -⟩ := hD.2 x
  refine ⟨c, ?_, ?_⟩
  · have h := hz.2
    rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight] at h
    exact_mod_cast h
  · let ι : T → {E : MMP.Mori.PrimeDivisor X // E ∈ D.support ∧ x ∈ E.support} :=
      fun G => ⟨G.1, hT G.2, hx G.1 G.2⟩
    have hι : Function.Injective ι := fun a b hab =>
      Subtype.ext (by simpa [ι] using congrArg Subtype.val hab)
    simpa using Fintype.card_le_of_injective (j ∘ ι) (hj.comp hι)

/-- **The generic point of an snc stratum has codimension the number of its components.** Let
`W` be an irreducible component of `⋂_{G ∈ J} G` for prime components `J` of an snc divisor `D`.
Then `W` is the closure of its generic point `w`, and `codim w = |J|`: at `w` the ideal of
`⋂_{G ∈ J} G` is generated by `|J|` members of a regular system of parameters, the maximal ideal
of `𝒪_{X,w}` is minimal over it, and Krull's height theorem bounds `codim w` by `|J|`; the
reverse bound is `card_le_coheight_of_isSNC`. -/
private lemma coheight_eq_card_of_isSNCStratum {R : Type*} [Zero R] {k : Type} [Field k]
    {X : Scheme.{0}} [IsLocallyNoetherian X] {sX : X ⟶ Spec (.of k)}
    {D : DivisorWithCoeffs R X} (hD : D.IsSNC sX) {J : Finset (MMP.Mori.PrimeDivisor X)}
    (hJ : J ⊆ D.support) {W : Set X}
    (hW : Maximal (fun T : Set X => IsIrreducible T ∧ T ⊆ ⋂ E ∈ J, (E.support : Set X)) W) :
    ∃ w : X, W = closure {w} ∧ (∀ G ∈ J, w ∈ G.support) ∧ Order.coheight w = J.card := by
  classical
  have hcl : IsClosed (⋂ E ∈ J, (E.support : Set X)) :=
    isClosed_biInter fun G _ => G.idealSheaf.support.isClosed
  have hWc : closure W = W :=
    (hW.2 ⟨hW.1.1.closure, closure_minimal hW.1.2 hcl⟩ subset_closure).antisymm subset_closure
  obtain ⟨w, hw⟩ := QuasiSober.sober hW.1.1.closure isClosed_closure
  rw [hWc] at hw
  have hWw : W = closure {w} := hw.symm
  have hwG : ∀ G ∈ J, w ∈ G.support := fun G hG =>
    Set.biInter_subset_of_mem hG (hW.1.2 (hWw ▸ subset_closure rfl))
  refine ⟨w, hWw, hwG, ?_⟩
  obtain ⟨c, hc, hcard⟩ := card_le_coheight_of_isSNC hD w J hJ hwG
  rw [hc]
  refine congrArg _ (le_antisymm ?_ hcard)
  obtain ⟨N, z, j, hz, hj, hI⟩ := hD.2 w
  let jJ : J → Fin N := fun G => j ⟨G.1, hJ G.2, hwG G.1 G.2⟩
  let J' : Finset (Fin N) := Finset.univ.image jJ
  let Z : X.IdealSheafData := ⨆ G : J, G.1.idealSheaf
  have hZsupp : (Z.support : Set X) = ⋂ E ∈ J, (E.support : Set X) := by
    simp only [Z, Scheme.IdealSheafData.support_iSup, TopologicalSpace.Closeds.coe_iInf]
    ext x
    simp only [Set.mem_iInter, Subtype.forall]
  have hZst : IdealSheafData.stalk Z w = (MMP.Resolution.coordPrime hz J').asIdeal := by
    change _ = Ideal.span (z '' (J' : Set (Fin N)))
    rw [MMP.Resolution.stalk_iSup]
    refine le_antisymm (iSup_le fun G => ?_) (Ideal.span_le.mpr ?_)
    · rw [hI ⟨G.1, hJ G.2, hwG G.1 G.2⟩]
      exact Ideal.span_mono (Set.singleton_subset_iff.mpr
        ⟨jJ G, by simp [J'], rfl⟩)
    · rintro _ ⟨i, hi, rfl⟩
      obtain ⟨G, -, rfl⟩ := Finset.mem_image.mp hi
      have : z (jJ G) ∈ IdealSheafData.stalk G.1.idealSheaf w := by
        rw [hI ⟨G.1, hJ G.2, hwG G.1 G.2⟩]; exact Ideal.mem_span_singleton_self _
      exact (le_iSup (fun G : J => IdealSheafData.stalk G.1.idealSheaf w) G) this
  have hWcomp : W ∈ MMP.Resolution.componentsOf (Z.support : Set X) := by
    rwa [hZsupp]
  have hWq := MMP.Resolution.eq_closure_coordPrime_of_mem_componentsOf hz hZst hWcomp
    (hWw ▸ subset_closure rfl)
  have hmax : IsLocalRing.maximalIdeal (X.presheaf.stalk w) ≤
      (MMP.Resolution.coordPrime hz J').asIdeal := by
    have hmem : X.fromSpecStalk w (MMP.Resolution.coordPrime hz J') ∈
        closure {X.fromSpecStalk w (IsLocalRing.closedPoint _)} := by
      rw [Scheme.fromSpecStalk_closedPoint, ← hWw, hWq]
      exact subset_closure rfl
    exact (MMP.Resolution.fromSpecStalk_mem_closure_iff w _ _).mp hmem
  have hmin : IsLocalRing.maximalIdeal (X.presheaf.stalk w) ∈
      (Ideal.span ((J'.image z : Finset _) : Set (X.presheaf.stalk w))).minimalPrimes := by
    have heq : Ideal.span ((J'.image z : Finset _) : Set (X.presheaf.stalk w)) =
        IsLocalRing.maximalIdeal (X.presheaf.stalk w) := by
      rw [Finset.coe_image]
      exact le_antisymm (IsLocalRing.le_maximalIdeal fun h =>
        (MMP.Resolution.coordPrime hz J').2.ne_top h) hmax
    rw [heq, Ideal.minimalPrimes_eq_subsingleton_self]
    rfl
  have hht := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin
  have h1 : ((IsLocalRing.maximalIdeal (X.presheaf.stalk w)).height : WithBot ℕ∞) = c := by
    rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
      AlgebraicGeometry.ringKrullDim_stalk_eq_coheight, hc]
    rfl
  have h1' : (IsLocalRing.maximalIdeal (X.presheaf.stalk w)).height = c := by
    exact_mod_cast h1
  have h3 : (J'.image z).card ≤ J.card :=
    Finset.card_image_le.trans (Finset.card_image_le.trans (by simp))
  have h2 : (c : ℕ∞) ≤ (J.card : ℕ∞) := h1' ▸ hht.trans (by exact_mod_cast h3)
  exact_mod_cast h2

/-- **A point with `codim x` components through it spans a component of their intersection.** If
`codim x` prime components `T` of an snc divisor `D` pass through `x`, then the closure of `x` is
an irreducible component of `⋂_{G ∈ T} G`. -/
private lemma maximal_closure_singleton {R : Type*} [Zero R] {k : Type} [Field k]
    {X : Scheme.{0}} [IsLocallyNoetherian X] {sX : X ⟶ Spec (.of k)}
    {D : DivisorWithCoeffs R X} (hD : D.IsSNC sX) (x : X) (T : Finset (MMP.Mori.PrimeDivisor X))
    (hT : T ⊆ D.support) (hx : ∀ G ∈ T, x ∈ G.support)
    (hc : Order.coheight x = T.card) :
    Maximal (fun V : Set X => IsIrreducible V ∧ V ⊆ ⋂ E ∈ T, (E.support : Set X))
      (closure {x}) := by
  refine ⟨⟨isIrreducible_singleton.closure, ?_⟩, ?_⟩
  · refine closure_minimal ?_ (isClosed_biInter fun G _ => G.idealSheaf.support.isClosed)
    rw [Set.singleton_subset_iff, Set.mem_iInter₂]
    exact hx
  · rintro V ⟨hVirr, hVsub⟩ hxV
    -- the generic point `v` of `closure V` specializes to `x` and lies on every `G ∈ T`
    obtain ⟨v, hv⟩ := QuasiSober.sober hVirr.closure isClosed_closure
    have hxv : v ⤳ x := by
      rw [specializes_iff_mem_closure, hv.def]
      exact subset_closure (hxV (subset_closure rfl))
    have hvT : ∀ G ∈ T, v ∈ G.support := by
      intro G hG
      have hcl : closure V ⊆ G.support :=
        closure_minimal (hVsub.trans (Set.biInter_subset_of_mem hG)) G.idealSheaf.support.isClosed
      exact hcl (hv.def ▸ subset_closure rfl)
    obtain ⟨c', hc', hcard⟩ := card_le_coheight_of_isSNC hD v T hT hvT
    have hvx : v = x := by
      by_contra hne
      have hlt : x < v := lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hxv)
        (fun h => hne (hxv.antisymm (Scheme.le_iff_specializes.mp h)).eq)
      have := Order.coheight_strictAnti hlt (by rw [hc']; exact WithTop.coe_lt_top _)
      rw [hc', hc] at this
      exact absurd (by exact_mod_cast this : c' < T.card) (not_lt.mpr hcard)
    subst hvx
    calc V ⊆ closure V := subset_closure
      _ = closure {v} := hv.def.symm

/-- **A point with `codim x` floor components through it spans a stratum.** If exactly
`codim x` prime components `T` of an snc divisor `D` pass through `x`, then the closure of `x` is
a stratum of `D`. -/
private lemma isSNCStratum_closure_singleton {R : Type*} [Zero R] {k : Type} [Field k]
    {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    {D : DivisorWithCoeffs R X} (hD : D.IsSNC sX) (x : X) (T : Finset (MMP.Mori.PrimeDivisor X))
    (hT : T ⊆ D.support) (hx : ∀ G ∈ T, x ∈ G.support)
    (hc : Order.coheight x = T.card) :
    IsSNCStratum D (closure {x}) :=
  ⟨T, hT, maximal_closure_singleton hD x T hT hx hc⟩

/-! ### Centres of divisors of discrepancy `-1` over an snc subboundary -/

/-- The prime divisors of the reduced coefficient-one part `B^{=1}` are among those of `B`. -/
private lemma support_coeffOnePart_subset {X : Scheme.{0}} (B : QDivisor X) :
    (coeffOnePart B).support ⊆ B.support := by
  intro G hG
  rw [Finsupp.mem_support_iff] at hG ⊢
  intro h0
  apply hG
  change (coeffOnePart B).coeff G = 0
  rw [coeff_coeffOnePart]
  rw [show B.coeff G = 0 from h0, if_neg (by norm_num)]

/-- A prime divisor of `B` with coefficient one is a prime divisor of `B^{=1}`. -/
private lemma mem_support_coeffOnePart {X : Scheme.{0}} {B : QDivisor X}
    {G : MMP.Mori.PrimeDivisor X} (hG : B.coeff G = 1) : G ∈ (coeffOnePart B).support := by
  rw [Finsupp.mem_support_iff]
  change (coeffOnePart B).coeff G ≠ 0
  rw [coeff_coeffOnePart, if_pos hG]
  exact one_ne_zero

/-- The reduced divisor `∑_{E ∈ S} E` on components `S` of an snc divisor is snc. -/
private lemma isSNC_sum_single {R : Type*} [Zero R] {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {D : DivisorWithCoeffs R X} (hD : D.IsSNC sX)
    {S : Finset (MMP.Mori.PrimeDivisor X)} (hS : S ⊆ D.support) :
    DivisorWithCoeffs.IsSNC sX (∑ E ∈ S, Finsupp.single E (1 : ℤ)) := by
  classical
  refine hD.of_support_subset fun G hG => hS ?_
  by_contra hGS
  apply Finsupp.mem_support_iff.mp hG
  rw [Finsupp.finset_sum_apply]
  exact Finset.sum_eq_zero fun E hE => by
    rw [Finsupp.single_apply, if_neg (fun h : E = G => hGS (h ▸ hE))]

/-- **The centre of a divisor of discrepancy `-1` is a floor stratum.** For a smooth projective
variety `X` with an snc subboundary `B` and a divisor `E` over `X` with `a(E, X, B) = -1`, the
closure of the centre of `E` is a stratum of `B^{=1}`. If `E` is exceptional, the snc lower bound
forces exactly `codim` components of `B` through the centre, all of coefficient one; otherwise
`E` is a prime divisor `P` of `X` with `-B_P = -1`. -/
private theorem isSNCStratum_closure_of_isDiscrepancy_eq_neg_one {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {B : QDivisor X}
    (hB : IsSNCSubboundaryPair sX B) {n : ℕ} {KX : Divisor X} (hKX : KX.IsCanonicalDivisor sX n)
    (D : DivisorOver k sX) (hD : IsDiscrepancy sX n KX B D (-1)) :
    IsSNCStratum (coeffOnePart B) (closure {D.f D.E.genericPoint}) := by
  classical
  have hX : IsNormalVariety k sX := hD.1
  have hsncB : (coeffOnePart B).IsSNC sX :=
    hB.isSNC.of_support_subset (support_coeffOnePart_subset B)
  by_cases hE : D.IsExceptional
  · have hsnc := isSNC_sum_single hB.isSNC subset_rfl
    obtain ⟨c, T, hc, hT, -, hcard, -, -, hle⟩ := MMP.Mori.le_isDiscrepancy_of_isSNC hX
      hB.isSmoothScheme hKX subset_rfl hsnc (fun E _ => hB.coeff_le_one E) D hE hD
    have hterm : ∀ G ∈ T, 0 ≤ 1 - B.coeff G := fun G _ => by linarith [hB.coeff_le_one G]
    have hsum0 := Finset.sum_nonneg hterm
    have hct : (T.card : ℚ) ≤ c := by exact_mod_cast hcard
    have hzero : ∑ G ∈ T, (1 - B.coeff G) = 0 := by linarith
    have hTc : T.card = c := le_antisymm hcard (by exact_mod_cast (show (c : ℚ) ≤ T.card by
      linarith))
    have h1 : ∀ G ∈ T, B.coeff G = 1 := fun G hG => by
      have := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hzero G hG
      linarith
    refine isSNCStratum_closure_singleton hsncB _ T (fun G hG => mem_support_coeffOnePart
      (h1 G hG)) (fun G hG => by rw [hT] at hG; exact (Finset.mem_filter.mp hG).2) ?_
    rw [← hc, hTc]
  · obtain ⟨P, hcen, hP⟩ := MMP.Mori.DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff
      ⟨hX, hKX, isQCartier_of_isSmoothScheme hB.isSmoothScheme _⟩ D hE
    have hP1 : B.coeff P = 1 := by linarith [hD.eq hP]
    have hcl : closure {D.f D.E.genericPoint} = (P.support : Set X) := by
      rw [← hcen, MMP.Positivity.DivisorOver.center_eq_closureSingleton]
      rfl
    rw [hcl]
    refine ⟨{P}, by simpa using mem_support_coeffOnePart hP1, ⟨?_, by simp⟩, ?_⟩
    · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact isIrreducible_singleton.closure
    · rintro V ⟨-, hV⟩ -
      simpa using hV

/-- The coefficient of `C` along a prime divisor of `C^{=1}` is one. -/
private lemma coeff_eq_one_of_mem_support_coeffOnePart {X : Scheme.{0}} {B : QDivisor X}
    {G : MMP.Mori.PrimeDivisor X} (hG : G ∈ (coeffOnePart B).support) : B.coeff G = 1 := by
  rw [Finsupp.mem_support_iff] at hG
  change (coeffOnePart B).coeff G ≠ 0 at hG
  rw [coeff_coeffOnePart] at hG
  by_contra h
  exact hG (if_neg h)

/-- The stalk of a finite supremum of ideal sheaves is the supremum of the stalks. -/
private lemma stalk_finset_sup {Y : Scheme.{0}} {ι : Type*} (s : Finset ι)
    (f : ι → Y.IdealSheafData) (x : Y) :
    IdealSheafData.stalk (s.sup f) x = ⨆ i ∈ s, IdealSheafData.stalk (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sup_empty]
    simp only [Finset.notMem_empty, iSup_false, iSup_bot]
    rw [IdealSheafData.stalk]
    refine le_bot_iff.mp (iSup₂_le fun U hs => ?_)
    rw [show (⊥ : Y.IdealSheafData).ideal U = ⊥ from rfl, Ideal.map_bot]
  | insert i s hi ih =>
    rw [Finset.sup_insert, IdealSheafData.stalk_sup, ih, Finset.iSup_insert]

/-- The support of a finite supremum of ideal sheaves is the intersection of the supports. -/
private lemma coe_support_finset_sup {Y : Scheme.{0}} {ι : Type*} (s : Finset ι)
    (f : ι → Y.IdealSheafData) :
    ((s.sup f).support : Set Y) = ⋂ i ∈ s, ((f i).support : Set Y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sup_insert, Scheme.IdealSheafData.support_sup,
      TopologicalSpace.Closeds.coe_inf, ih, Finset.set_biInter_insert]

open scoped Classical in
/-- At a point `x` with local parameters `z` of an snc divisor, `j` choosing for each component
through `x` the parameter generating its ideal, the sum of the ideals of components `T` through `x`
is spanned by their parameters. -/
private theorem iSup_stalk_idealSheaf_eq_span {X : Scheme.{0}}
    {S : Finset (MMP.Mori.PrimeDivisor X)} {x : X} {N : ℕ} (z : Fin N → X.presheaf.stalk x)
    (j : {G : MMP.Mori.PrimeDivisor X // G ∈ S ∧ x ∈ G.support} → Fin N)
    (hI : ∀ G, IdealSheafData.stalk G.1.idealSheaf x = Ideal.span {z (j G)})
    {T : Finset (MMP.Mori.PrimeDivisor X)} (hT : ∀ G ∈ T, G ∈ S ∧ x ∈ G.support) :
    ⨆ G ∈ T, IdealSheafData.stalk G.idealSheaf x = Ideal.span (z ''
      ((Finset.univ.image fun G : T => j ⟨G.1, hT G.1 G.2⟩ : Finset (Fin N)) : Set (Fin N))) := by
  refine le_antisymm (iSup₂_le fun G hG => ?_) (Ideal.span_le.mpr ?_)
  · rw [hI ⟨G, hT G hG⟩]
    exact Ideal.span_mono (Set.singleton_subset_iff.mpr
      ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ ⟨G, hG⟩), rfl⟩)
  · rintro _ ⟨i, hi, rfl⟩
    obtain ⟨G, -, rfl⟩ := Finset.mem_image.mp hi
    have : z (j ⟨G.1, hT G.1 G.2⟩) ∈ IdealSheafData.stalk G.1.idealSheaf x := by
      rw [hI ⟨G.1, hT G.1 G.2⟩]; exact Ideal.mem_span_singleton_self _
    exact (le_iSup₂ (f := fun G _ => IdealSheafData.stalk
      (G : MMP.Mori.PrimeDivisor X).idealSheaf x) G.1 G.2) this

/-- **The intersection of snc components is regular.** Along `⋂_{G ∈ T} G` for components `T` of
an snc divisor, the local ring modulo `∑_{G ∈ T} I_G` is regular: the ideal is generated by part of
a regular system of parameters. -/
private theorem isRegularLocalRing_quotient_stalk_finset_sup {R : Type*} [Zero R] {k : Type}
    [Field k] {Y : Scheme.{0}} [IsLocallyNoetherian Y] {sY : Y ⟶ Spec (.of k)}
    {D : DivisorWithCoeffs R Y} (hD : D.IsSNC sY) {T : Finset (MMP.Mori.PrimeDivisor Y)}
    (hT : T ⊆ D.support) :
    ∀ x ∈ (T.sup fun G => G.idealSheaf).support, IsRegularLocalRing
      (Y.presheaf.stalk x ⧸ IdealSheafData.stalk (T.sup fun G => G.idealSheaf) x) := by
  intro x hx
  rw [← SetLike.mem_coe, coe_support_finset_sup, Set.mem_iInter₂] at hx
  obtain ⟨N, z, j, hz, -, hI⟩ := hD.2 x
  have := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz
  rw [stalk_finset_sup, iSup_stalk_idealSheaf_eq_span z j hI fun G hG => ⟨hT hG, hx G hG⟩]
  exact MMP.Resolution.isRegularLocalRing_quotient_span_image z hz _

/-- **The closure of a point of a stratum is smooth, cut out by the components.** Let `D` be an
snc divisor on a scheme `Y` smooth over a perfect field, `T` a set of components of `D`, and `y`
a point of codimension `|T|` lying on every `G ∈ T`. Then `closure {y}` is smooth with its reduced
structure, and along it its ideal is `∑_{G ∈ T} I_G`: near `y` the ideal `∑_{G ∈ T} I_G` is
generated by part of a regular system of parameters, so its zero set is smooth, and the
component through `y` is `closure {y}` by the codimension count. -/
private theorem stratum_closure {R : Type*} [Zero R] {k : Type} [Field k] [PerfectField k]
    {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] [QuasiCompact sY]
    {D : DivisorWithCoeffs R Y} (hD : D.IsSNC sY) {T : Finset (MMP.Mori.PrimeDivisor Y)}
    (hT : T ⊆ D.support) {y : Y} (hyT : ∀ G ∈ T, y ∈ G.support)
    (hc : Order.coheight y = T.card) :
    IsSmoothScheme
        ((Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure {y})).subschemeι ≫
          sY) ∧
      ∀ x ∈ closure {y},
        IdealSheafData.stalk
            (Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure {y})) x =
          ⨆ G ∈ T, IdealSheafData.stalk G.idealSheaf x := by
  classical
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : IsNoetherian Y := {}
  set Dt := T.sup (fun G => G.idealSheaf) with hDdef
  have hDsupp : (Dt.support : Set Y) = ⋂ G ∈ T, (G.support : Set Y) :=
    coe_support_finset_sup _ _
  have hDreg := isRegularLocalRing_quotient_stalk_finset_sup hD hT
  have hDsm : IsSmoothScheme (Dt.subschemeι ≫ sY) :=
    MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isSmoothScheme_subscheme_of_isRegularLocalRing_quotient
      sY Dt hDreg
  haveI hDred : IsReduced Dt.subscheme := by
    have : LocallyOfFinitePresentation (Dt.subschemeι ≫ sY) :=
      (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := Dt.subschemeι ≫ sY)).mpr
        inferInstance
    have hsm : Smooth (Dt.subschemeι ≫ sY) := (MMP.Mori.isSmoothScheme_iff _).1 hDsm
    haveI : ∀ x : Dt.subscheme, _root_.IsReduced (Dt.subscheme.presheaf.stalk x) := fun x => by
      have := isRegularLocalRing_stalk_of_smooth_over_field (Dt.subschemeι ≫ sY) x
      have := IsRegularLocalRing.isDomain (Dt.subscheme.presheaf.stalk x)
      exact isReduced_of_noZeroDivisors
    exact isReduced_of_isReduced_stalk _
  have hyD : y ∈ (Dt.support : Set Y) := by rw [hDsupp]; exact Set.mem_iInter₂.mpr hyT
  have hDcl : IsClosed (Dt.support : Set Y) := Dt.support.isClosed
  obtain ⟨hfin, hcov⟩ := MMP.Resolution.Aux.finite_and_cover_componentsOf hDcl
  obtain ⟨Cc, hC, hyC⟩ := hcov hyD
  -- the component through `y` is the closure of `y`
  obtain ⟨ξ, hξD, hCξ⟩ := MMP.Resolution.Aux.exists_eq_closure_of_mem_componentsOf hDcl hC
  have hξy : ξ = y := by
    have hsp : ξ ⤳ y := specializes_iff_mem_closure.mpr (hCξ ▸ hyC)
    have hξT : ∀ G ∈ T, ξ ∈ G.support := by
      rw [hDsupp, Set.mem_iInter₂] at hξD; exact hξD
    obtain ⟨c', hc', hcard⟩ := card_le_coheight_of_isSNC hD ξ T hT hξT
    by_contra hne
    have hlt : y < ξ := lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hsp)
      fun hle' => hne (hsp.antisymm (Scheme.le_iff_specializes.mp hle')).eq
    have := Order.coheight_strictAnti hlt (by rw [hc']; exact ENat.coe_lt_top _)
    rw [hc, hc'] at this
    exact absurd (by exact_mod_cast this : c' < T.card) (not_lt.mpr hcard)
  rw [hξy] at hCξ
  subst hCξ
  set Bc := ⋃₀ (MMP.Resolution.componentsOf (Dt.support : Set Y) \ {closure {y}}) with hB
  have hBcl : IsClosed Bc := (hfin.subset Set.diff_subset).isClosed_sUnion
    fun W hW => MMP.Resolution.Aux.isClosed_of_mem_componentsOf hDcl hW.1
  have hdisj : ∀ x ∈ closure {y}, x ∉ Bc := by
    rintro x hxC ⟨W, ⟨hW, hWC⟩, hxW⟩
    exact hWC (MMP.Resolution.Aux.eq_of_mem_componentsOf_of_isSmoothScheme sY Dt hDsm hW hC
      hxW hxC)
  have hCB : closure {y} ∪ Bc = Dt.support := by
    refine le_antisymm (Set.union_subset hC.1.2 ?_) fun x hx => ?_
    · rintro x ⟨W, ⟨hW, -⟩, hxW⟩; exact hW.1.2 hxW
    · obtain ⟨W, hW, hxW⟩ := hcov hx
      by_cases h : W = closure {y}
      · exact Or.inl (h ▸ hxW)
      · exact Or.inr ⟨W, ⟨hW, h⟩, hxW⟩
  have hstalk : ∀ x ∈ closure {y}, IdealSheafData.stalk
      (Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure {y})) x =
        IdealSheafData.stalk Dt x := fun x hx =>
    MMP.Mori.stalk_vanishingIdeal_eq_stalk_of_sup_eq Dt (TopologicalSpace.Closeds.closure {y})
      ⟨Bc, hBcl⟩ (TopologicalSpace.Closeds.ext hCB) (hdisj x hx)
  have hsupp : ((Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure {y})).support : Set Y) = closure {y} := by
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, TopologicalSpace.Closeds.coe_closure]
  refine ⟨?_, fun x hx => by rw [hstalk x hx, hDdef, stalk_finset_sup]⟩
  refine
    MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isSmoothScheme_subscheme_of_isRegularLocalRing_quotient
      sY _ fun x hx => ?_
  rw [← SetLike.mem_coe, hsupp] at hx
  rw [hstalk x hx]
  exact hDreg x (hC.1.2 hx)

section ExcEDiscrepancy

open MMP MMP.Mori MMP.Resolution MMP.Fourfold
open TopologicalSpace

universe u

variable {k : Type u} [Field k] {Y : Scheme.{u}}

private theorem mem_support_sum_single {X : Scheme.{u}} (S : Finset (MMP.Mori.PrimeDivisor X))
    (G : MMP.Mori.PrimeDivisor X) :
    G ∈ (∑ E ∈ S, Finsupp.single E (1 : ℤ)).support ↔ G ∈ S := by
  classical
  rw [Finsupp.mem_support_iff, Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply]

/-- The local description of `∑_{E ∈ S} E` snc at a point `y`: a regular system of parameters of
`𝒪_{X,y}` and an injective choice, for each `E ∈ S` through `y`, of a parameter generating the
ideal of `E`. -/
private theorem exists_at_of_isSNC {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {S : Finset (MMP.Mori.PrimeDivisor X)}
    (hsnc : DivisorWithCoeffs.IsSNC sX (∑ E ∈ S, Finsupp.single E (1 : ℤ))) (y : X) :
    ∃ (N : ℕ) (z : Fin N → X.presheaf.stalk y)
      (j : {G : MMP.Mori.PrimeDivisor X // G ∈ S ∧ y ∈ G.support} → Fin N),
      IsRegularSystemOfParameters z ∧ Function.Injective j ∧
        ∀ G, IdealSheafData.stalk G.1.idealSheaf y = Ideal.span {z (j G)} := by
  obtain ⟨N, z, j, hz, hj, hI⟩ := hsnc.2 y
  let e : {G : MMP.Mori.PrimeDivisor X // G ∈ S ∧ y ∈ G.support} →
      {G : MMP.Mori.PrimeDivisor X //
        G ∈ (∑ E ∈ S, Finsupp.single E (1 : ℤ)).support ∧ y ∈ G.support} :=
    fun G => ⟨G.1, (mem_support_sum_single S G.1).mpr G.2.1, G.2.2⟩
  refine ⟨N, z, j ∘ e, hz, hj.comp fun G G' h => Subtype.ext (congrArg Subtype.val h :), ?_⟩
  exact fun G => hI (e G)

/-- A supremum of principal ideals generated by members `z_j`, `j ∈ J`, of a family. -/
private theorem iSup_eq_span_image {R : Type*} [CommRing R] {N : ℕ} (z : Fin N → R)
    {ι : Type*} (T : Finset ι) (I : ι → Ideal R) (J : Finset (Fin N))
    (h1 : ∀ G ∈ T, ∃ j ∈ J, I G = Ideal.span {z j})
    (h2 : ∀ j ∈ J, ∃ G ∈ T, I G = Ideal.span {z j}) :
    ⨆ G ∈ T, I G = Ideal.span (z '' (J : Set (Fin N))) := by
  refine le_antisymm (iSup₂_le fun G hG => ?_) (Ideal.span_le.mpr ?_)
  · obtain ⟨j, hj, hIj⟩ := h1 G hG
    rw [hIj]
    exact Ideal.span_mono (Set.singleton_subset_iff.mpr ⟨j, hj, rfl⟩)
  · rintro _ ⟨j, hj, rfl⟩
    obtain ⟨G, hG, hIj⟩ := h2 j hj
    have : z j ∈ I G := by rw [hIj]; exact Ideal.mem_span_singleton_self _
    exact (le_iSup₂ (f := fun G _ => I G) G hG) this

open scoped Classical in
open MMP.Threefold.Resolution MMP.Fourfold.SNCWeight.StratumBlowup
  MMP.Fourfold.SNCWeight.LocalEquation MMP.Fourfold.SNCWeight.BlowupCrepancy in
/-- **The discrepancy of the exceptional divisor of a stratum blow-up.** Let `Z` be a smooth
centre of codimension `c = |T|` on a smooth variety `Y` whose ideal is `∑_{G ∈ T} I_G` along `Z`,
for the components `G ∈ T` of an snc divisor, and let `Δ` have coefficient `t_G` along the
`G ∈ T` and zero along the other prime divisors through `Z`. Then the exceptional divisor `E` of
`Bl_Z Y` has discrepancy `a(E, Y, Δ) = (c - 1) - ∑_{G ∈ T} t_G`. -/
private theorem isDiscrepancy_excE_of_coeff [PerfectField k] (sY : Y ⟶ Spec (.of k))
    [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {n : ℕ} {KY : Divisor Y}
    (hKY : KY.IsCanonicalDivisor sY n) {ΔY : QDivisor Y} (hPY : Mori.IsPair sY ΔY)
    {I : Y.IdealSheafData} (h : IsSmoothBlowup sY I) (hirr : IsIrreducible (I.support : Set Y))
    {T : Finset (Mori.PrimeDivisor Y)}
    (hc : (T.card : ℕ∞) =
      codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y))
    (hc1 : 1 ≤ T.card)
    (hsnc : DivisorWithCoeffs.IsSNC sY (∑ G ∈ T, Finsupp.single G (1 : ℤ)))
    (hIT : ∀ G ∈ T, (I.support : Set Y) ⊆ G.support)
    (hIst : ∀ x ∈ I.support, IdealSheafData.stalk I x =
      ⨆ G ∈ T, IdealSheafData.stalk G.idealSheaf x)
    (t : Mori.PrimeDivisor Y → ℚ)
    (hΔ : ∀ Γ : Mori.PrimeDivisor Y, (I.support : Set Y) ⊆ Γ.support →
      ΔY.coeff Γ = if Γ ∈ T then t Γ else 0)
    (hN : IsNormalVariety k (blowUpToBase I ≫ sY))
    (hc1' : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y))
    (hb : haveI := isIntegral_blowUp_of_one_le_codimension I hirr hc1'
      IsBirationalMorphism (blowUpToBase I)) :
    haveI := isIntegral_blowUp_of_one_le_codimension I hirr hc1'
    IsDiscrepancy sY n KY ΔY ⟨blowUp I, blowUpToBase I, hN, hb, excE sY h hirr hc1'⟩
      ((T.card : ℚ) - 1 - ∑ G ∈ T, t G) := by
  classical
  haveI := isIntegral_blowUp_of_one_le_codimension I hirr hc1'
  haveI := isDominant_blowUpToBase I hirr hc1'
  haveI := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sY I h).1
  haveI : IsLocallyNoetherian (blowUp I) := isLocallyNoetherian_of_smooth (blowUpToBase I ≫ sY)
  haveI : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
  haveI := AlgebraicGeometry.isNormal_of_smooth (blowUpToBase I ≫ sY)
  haveI : Smooth sY := smooth_of_isSmoothScheme h.1
  set E := excE sY h hirr hc1' with hE
  set x₀ := blowUpToBase I E.genericPoint with hx₀
  have hx₀I : closure {x₀} = (I.support : Set Y) := closure_map_genericPoint_excE sY h hirr hc1'
  have hx₀mem : x₀ ∈ (I.support : Set Y) := hx₀I ▸ subset_closure rfl
  have hmemΓ : ∀ Γ : Mori.PrimeDivisor Y, x₀ ∈ Γ.support → (I.support : Set Y) ⊆ Γ.support :=
    fun Γ hx => hx₀I ▸ closure_minimal (Set.singleton_subset_iff.mpr hx)
      (MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isClosed_support Γ)
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPY hKY
    (⟨blowUp I, blowUpToBase I, hN, hb, E⟩ : DivisorOver k sY)
  suffices hae : a = (T.card : ℚ) - 1 - ∑ G ∈ T, t G by rwa [hae] at ha
  have hn := hKY.topologicalKrullDim_eq
  obtain ⟨-, -, m, hm, -, U, hU, τ, hτ, hτa⟩ := ha
  -- generators of the top forms and the comparison along `E`
  obtain ⟨σA, hσA, h0A, σB, hσB, h0B, h', hrel, hh, hord⟩ :=
    MMP.Threefold.Resolution.exists_topForms_rel I sY h hirr hc hc1 hn E
  rw [if_pos rfl] at hord
  let := stalkAlgebra sY x₀
  let := functionFieldAlgebra sY
  have := isScalarTower_stalk_functionField sY x₀
  have hordτ := MMP.Threefold.Resolution.ordForm_pullbackRationalPluriForms_eq sY
    (blowUpToBase I) E hσA h0A hσB h0B h' hrel hh hτ.1
  set g := formCoeff (k := k) (Y.presheaf.stalk x₀) hσA h0A
    (show PluriForms k Y.functionField n m from τ) with hgdef
  have hg0 : g ≠ 0 := fun h0 => hτ.1 ((formCoeff_eq_zero_iff hσA h0A _).mp h0)
  have hgΓ : ∀ Γ : Mori.PrimeDivisor Y, x₀ ∈ Γ.support →
      (Y.ord g Γ.genericPoint : ℝ) = -((m : ℝ) * (ΔY.coeff Γ : ℝ)) := by
    intro Γ hΓ
    have e1 := MMP.Threefold.Resolution.ordForm_eq_ord_formCoeff sY x₀ Γ hΓ hσA h0A τ
    have e2 := hτ.2 Γ ⟨_, hΓ, hU⟩
    rw [e1] at e2
    have := congrArg (fun q : ℚ => (q : ℝ)) e2
    push_cast at this
    linarith
  -- coordinates at the centre
  obtain ⟨N, z, j, hz, hj, hI⟩ := exists_at_of_isSNC hsnc x₀
  have hxT : ∀ G ∈ T, x₀ ∈ G.support := fun G hG => hIT G hG hx₀mem
  let jT : T → Fin N := fun G => j ⟨G.1, G.2, hxT G.1 G.2⟩
  have hJ : IdealSheafData.stalk I x₀ =
      Ideal.span (z '' ((Finset.univ.image jT : Finset (Fin N)) : Set (Fin N))) := by
    rw [hIst x₀ hx₀mem]
    refine iSup_eq_span_image z T _ _ (fun G hG => ⟨jT ⟨G, hG⟩,
      Finset.mem_image_of_mem _ (Finset.mem_univ _), hI ⟨G, hG, hxT G hG⟩⟩) fun i hi => ?_
    obtain ⟨G, -, rfl⟩ := Finset.mem_image.mp hi
    exact ⟨G.1, G.2, hI ⟨G.1, G.2, hxT G.1 G.2⟩⟩
  have hzE : ∀ G : T, (blowUp I).ord (functionFieldMap (blowUpToBase I)
      (algebraMap _ Y.functionField (z (jT G)))) E.genericPoint = 1 := by
    intro G
    rw [MMP.Mori.functionFieldMap_algebraMap_stalk]
    have hv := divisorialValuation_excE_param sY h hirr hc1' hz hJ
      (Finset.mem_image_of_mem jT (Finset.mem_univ G))
    refine ord_eq_of_divisorialValuation_eq E (fun h0 => ?_) hv
    rw [h0, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  have hzΓ : ∀ (G : T) (Γ : Mori.PrimeDivisor Y), x₀ ∈ Γ.support →
      Y.ord (algebraMap _ Y.functionField (z (jT G))) Γ.genericPoint =
        if Γ = G.1 then 1 else 0 :=
    fun G Γ hΓ => ord_localEq Γ G.1 hΓ (hxT G.1 G.2) (hI ⟨G.1, G.2, hxT G.1 G.2⟩)
  -- the Hartogs relation along `E`
  let Gf : Option T → Y.functionField := fun i =>
    Option.elim i g fun G => algebraMap _ Y.functionField (z (jT G))
  let wt : Option T → ℝ := fun i => Option.elim i 1 fun G => (m : ℝ) * (t G.1 : ℝ)
  have hGf : ∀ i, Gf i ≠ 0 := by
    rintro (_ | G)
    · exact hg0
    · exact localEq_ne_zero G.1 (hxT G.1 G.2) (hI ⟨G.1, G.2, hxT G.1 G.2⟩)
  have key := MMP.Threefold.Bridges.sum_ord_functionFieldMap_eq_zero (f := blowUpToBase I) E Gf
    hGf wt fun Γ hΓ => by
      simp only [Fintype.sum_option, Gf, wt, Option.elim]
      rw [hgΓ Γ hΓ]
      simp_rw [hzΓ _ Γ hΓ]
      rw [hΔ Γ (hmemΓ Γ hΓ)]
      by_cases hΓT : Γ ∈ T
      · rw [Finset.sum_eq_single ⟨Γ, hΓT⟩]
        · simp [hΓT]
          try ring
        · rintro G - hne
          have : Γ ≠ G.1 := fun h => hne (Subtype.ext h.symm)
          simp [this]
        · simp
      · rw [if_neg hΓT]
        simp only [Rat.cast_zero, mul_zero, neg_zero, mul_one, zero_add]
        refine Finset.sum_eq_zero fun G _ => ?_
        have : Γ ≠ G.1 := fun h => hΓT (h ▸ G.2)
        simp [this]
  simp only [Fintype.sum_option, Gf, wt, Option.elim, mul_one] at key
  simp_rw [hzE] at key
  simp only [Int.cast_one, mul_one, one_mul] at key
  have hsum : ∑ G : T, (m : ℝ) * (t G.1 : ℝ) = (m : ℝ) * ((∑ G ∈ T, t G : ℚ) : ℝ) := by
    rw [← Finset.mul_sum]
    push_cast
    rw [Finset.sum_coe_sort T (fun G => (t G : ℝ))]
  -- the numerical conclusion
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmain : (m : ℝ) * (a : ℝ) =
      ((blowUp I).ord (functionFieldMap (blowUpToBase I) g) E.genericPoint : ℝ) +
      (m : ℝ) * ((blowUp I).ord (algebraMap E.localRing (blowUp I).functionField h')
        E.genericPoint : ℝ) := by
    have h1 : (m : ℚ) * a = E.ordForm (pullbackRationalPluriForms sY (blowUpToBase I) τ) := hτa
    rw [hordτ] at h1
    have := congrArg (fun q : ℚ => (q : ℝ)) h1
    push_cast at this
    exact this
  rw [hord] at hmain
  push_cast at hmain
  have h2 : (m : ℝ) * (a : ℝ) =
      (m : ℝ) * ((T.card : ℝ) - 1 - ((∑ G ∈ T, t G : ℚ) : ℝ)) := by
    linear_combination hmain + key - hsum
  have h3 := mul_left_cancel₀ hm'.ne' h2
  exact_mod_cast h3

/-- A scheme separated over a field is separated over the terminal scheme. -/
private theorem isSeparated_toTerminal {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (hsX : IsSeparated sX) : IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

/-- A divisor over a normal variety is exceptional if and only if its center has codimension at
least two. -/
private theorem isExceptional_iff_two_le_coheight {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) (D : DivisorOver k sX) :
    D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := isSeparated_toTerminal hX.1.toIsSeparated
  unfold DivisorOver.IsExceptional
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  have hcl : Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set X), D.center.isClosed⟩ := Closeds.ext rfl
  rw [hcl, closedsCodimension_coe, MMP.Positivity.DivisorOver.codimension_center]

end ExcEDiscrepancy

open MMP.Threefold.Resolution MMP.Fourfold.SNCWeight.StratumBlowup in
/-- **Blowing up a stratum.** Let `w` be a point of a smooth variety `Y` with an snc subboundary
`C`, lying on `|J| ≥ 2` components of `C` with `codim w = |J|`. The exceptional divisor `E` of
the blow-up of `closure {w}` has `a(E, Y, C) = (|J| - 1) - ∑_{G ∈ J} C_G`: no other component of
`C` passes through `w`. -/
private theorem exists_isDiscrepancy_of_coheight_eq_card {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of k)}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {C : QDivisor Y}
    (hC : IsSNCSubboundaryPair sY C) {n : ℕ} {KY : Divisor Y} (hKY : KY.IsCanonicalDivisor sY n)
    {J : Finset (MMP.Mori.PrimeDivisor Y)} (hJC : J ⊆ C.support) {w : Y}
    (hwJ : ∀ G ∈ J, w ∈ G.support) (hcw : Order.coheight w = J.card) (h2 : 2 ≤ J.card) :
    ∃ E : DivisorOver k sY, E.f E.E.genericPoint = w ∧ IsProper E.f ∧
      IsDiscrepancy sY n KY C E ((J.card : ℚ) - 1 - ∑ G ∈ J, C.coeff G) := by
  classical
  have hYv : IsNormalVariety k sY := ⟨hC.isProjectiveVariety.toIsVariety, inferInstance⟩
  haveI : LocallyOfFiniteType sY := hYv.1.toLocallyOfFiniteType
  haveI : QuasiCompact sY := hYv.1.toQuasiCompact
  have hPY : MMP.Mori.IsPair sY C :=
    ⟨hYv, n, KY, hKY, isQCartier_of_isSmoothScheme hC.isSmoothScheme _⟩
  have hdim := hKY.topologicalKrullDim_eq
  have hsnc := isSNC_sum_single hC.isSNC hJC
  obtain ⟨hZsm, hZst⟩ := stratum_closure sY hC.isSNC hJC hwJ hcw
  set Z := Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure {w}) with hZdef
  have hZsupp : (Z.support : Set Y) = closure {w} := by
    rw [hZdef, Scheme.IdealSheafData.coe_support_vanishingIdeal,
      TopologicalSpace.Closeds.coe_closure]
  have hZst' : ∀ x ∈ Z.support, IdealSheafData.stalk Z x =
      ⨆ G ∈ J, IdealSheafData.stalk G.idealSheaf x := fun x hx => by
    rw [← SetLike.mem_coe, hZsupp] at hx
    exact hZst x hx
  have hZT : ∀ G ∈ J, (Z.support : Set Y) ⊆ G.support := fun G hG => by
    rw [hZsupp]
    exact closure_minimal (Set.singleton_subset_iff.mpr (hwJ G hG))
      (MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isClosed_support G)
  have hirr : IsIrreducible (Z.support : Set Y) := hZsupp ▸ isIrreducible_singleton.closure
  have hcodim : codimension (⟨Z.support, hirr, Z.support.isClosed⟩ :
      TopologicalSpace.IrreducibleCloseds Y) = J.card := by
    have heq : (⟨Z.support, hirr, Z.support.isClosed⟩ : TopologicalSpace.IrreducibleCloseds Y) =
        TopologicalSpace.IrreducibleCloseds.closureSingleton w := by
      ext1; exact hZsupp
    rw [heq, Stacks.Divisors.PrimeDivisor.codimension_closureSingleton, hcw]
  have hc1' : 1 ≤ codimension (⟨Z.support, hirr, Z.support.isClosed⟩ :
      TopologicalSpace.IrreducibleCloseds Y) := by
    rw [hcodim]; exact_mod_cast (by omega : 1 ≤ J.card)
  have hsb : MMP.Resolution.IsSmoothBlowup sY Z := ⟨hC.isSmoothScheme, hZsm⟩
  obtain ⟨hvar, hsmB, hproj, hbir, -, -, -⟩ :=
    isVariety_smooth_blowUpToBase_divisorOfForm_pullbackRationalPluriForms
      sY hYv.1 hdim Z hsb hirr hcodim.symm h2
  set π := blowUpToBase Z with hπ
  haveI := isIntegral_blowUp_of_one_le_codimension Z hirr hc1'
  haveI : Smooth (π ≫ sY) := hsmB
  haveI : IsLocallyNoetherian (AlgebraicGeometry.blowUp Z) :=
    MMP.Resolution.isLocallyNoetherian_of_smooth (π ≫ sY)
  haveI : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
  haveI : IsNormal (AlgebraicGeometry.blowUp Z) := AlgebraicGeometry.isNormal_of_smooth (π ≫ sY)
  have hNπ : IsNormalVariety k (π ≫ sY) := ⟨hvar, inferInstance⟩
  set E := excE sY hsb hirr hc1' with hE
  have hEgen : π E.genericPoint = w := by
    have h1 := MMP.Fourfold.SNCWeight.BlowupCrepancy.closure_map_genericPoint_excE sY hsb
      hirr hc1'
    rw [hZsupp] at h1
    exact (inseparable_iff_closure_eq.2 h1).eq
  refine ⟨⟨AlgebraicGeometry.blowUp Z, π, hNπ, hbir, E⟩, hEgen, hproj.isProper, ?_⟩
  refine isDiscrepancy_excE_of_coeff sY hKY hPY hsb hirr hcodim.symm (by omega) hsnc hZT hZst'
    C.coeff (fun Γ hΓ => ?_) hNπ hc1' hbir
  have hwΓ : w ∈ Γ.support := hΓ (hZsupp ▸ subset_closure rfl)
  by_cases hΓJ : Γ ∈ J
  · rw [if_pos hΓJ]
  · rw [if_neg hΓJ]
    by_contra hΓ0
    have hΓC : Γ ∈ C.support := Finsupp.mem_support_iff.mpr hΓ0
    obtain ⟨c, hc, hcard⟩ := card_le_coheight_of_isSNC hC.isSNC w (insert Γ J)
      (Finset.insert_subset hΓC hJC) (fun G hG => by
        rcases Finset.mem_insert.mp hG with rfl | hG
        · exact hwΓ
        · exact hwJ G hG)
    rw [hcw] at hc
    have hcJ : c = J.card := by exact_mod_cast hc.symm
    rw [Finset.card_insert_of_notMem hΓJ, hcJ] at hcard
    omega

open scoped Classical in
/-- **Blowing up a floor stratum creates a zero place.** Let `w` be a point of a smooth variety
`Y` with an snc subboundary `C`, lying on `|J| ≥ 2` components of `C^{=1}` with
`codim w = |J|`. The exceptional divisor `E` of the blow-up of `closure {w}` has
`a(E, Y, C) = (|J| - 1) - |J| = -1`. -/
private theorem exists_isDiscrepancy_eq_neg_one_of_coheight_eq_card {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of k)}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {C : QDivisor Y}
    (hC : IsSNCSubboundaryPair sY C) {n : ℕ} {KY : Divisor Y} (hKY : KY.IsCanonicalDivisor sY n)
    {J : Finset (MMP.Mori.PrimeDivisor Y)} (hJ : J ⊆ (coeffOnePart C).support) {w : Y}
    (hwJ : ∀ G ∈ J, w ∈ G.support) (hcw : Order.coheight w = J.card) (h2 : 2 ≤ J.card) :
    ∃ E : DivisorOver k sY, E.f E.E.genericPoint = w ∧ IsProper E.f ∧
      IsDiscrepancy sY n KY C E (-1) := by
  obtain ⟨E, hEc, hEp, hE⟩ := exists_isDiscrepancy_of_coheight_eq_card hC hKY
    (hJ.trans (support_coeffOnePart_subset C)) hwJ hcw h2
  refine ⟨E, hEc, hEp, ?_⟩
  rwa [Finset.sum_congr rfl fun G hG => coeff_eq_one_of_mem_support_coeffOnePart (hJ hG),
    Finset.sum_const, nsmul_eq_mul, mul_one, sub_sub_cancel_left] at hE

/-! ### Local structure of snc strata and restriction of divisors -/

section StratumLocalRings

open CategoryTheory AlgebraicGeometry

open IsLocalRing in
private theorem ringKrullDim_quotient_span_image' {A : Type*} [CommRing A] [IsRegularLocalRing A]
    {n : ℕ}
    (z : Fin n → A) (hz : MMP.Mori.IsRegularSystemOfParameters z) (J : Finset (Fin n)) :
    ringKrullDim (A ⧸ Ideal.span (z '' (J : Set (Fin n)))) = (n - J.card : ℕ) := by
  classical
  have hreg := MMP.Resolution.isRegularLocalRing_quotient_span_image z hz J
  set I := Ideal.span (z '' (J : Set (Fin n))) with hI
  have hIm : I ≤ maximalIdeal A := by
    rw [hI, Ideal.span_le]
    rintro _ ⟨j, -, rfl⟩
    rw [← hz.1]; exact Ideal.subset_span ⟨j, rfl⟩
  have hmax : (maximalIdeal A).map (Ideal.Quotient.mk I) = maximalIdeal (A ⧸ I) := by
    have := IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [sup_eq_left.mpr hIm]
  have hgen : maximalIdeal (A ⧸ I) =
      Ideal.span (Ideal.Quotient.mk I '' (z '' ((Jᶜ : Finset (Fin n)) : Set (Fin n)))) := by
    rw [← hmax, ← hz.1, Ideal.map_span]
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      by_cases hi : i ∈ J
      · have : Ideal.Quotient.mk I (z i) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.subset_span ⟨i, hi, rfl⟩)
        simp [this]
      · exact Ideal.subset_span ⟨_, ⟨i, by simpa using hi, rfl⟩, rfl⟩
    · rw [Ideal.span_le]
      rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      exact Ideal.subset_span ⟨z i, ⟨i, rfl⟩, rfl⟩
  have h1 : (maximalIdeal (A ⧸ I)).spanFinrank ≤ (n - J.card : ℕ) := by
    rw [hgen]
    refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.Finite.image _
      (Set.Finite.image _ (Finset.finite_toSet _)))).trans ?_
    calc _ ≤ ((Jᶜ : Finset (Fin n)) : Set (Fin n)).ncard := by
          refine (Set.ncard_image_le (Set.Finite.image _ (Finset.finite_toSet _))).trans ?_
          exact Set.ncard_image_le (Finset.finite_toSet _)
      _ = (n - J.card : ℕ) := by
          rw [Set.ncard_coe_finset, Finset.card_compl]; simp
  have h2 : ringKrullDim A ≤ ringKrullDim (A ⧸ Ideal.span ((J.image z : Finset A) : Set A)) +
      (J.image z).card :=
    ringKrullDim_le_ringKrullDim_quotient_add_card (J.image z) (by
      intro a ha
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
      rw [SetLike.mem_coe, IsLocalRing.ringJacobson_eq_maximalIdeal]
      exact hIm (Ideal.subset_span ⟨j, hj, rfl⟩))
  rw [Finset.coe_image] at h2
  have hcard : (J.image z).card ≤ J.card := Finset.card_image_le
  rw [hz.2] at h2
  have h3 : ((n - J.card : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ I) := by
    generalize ringKrullDim (A ⧸ I) = d at *
    induction d using WithBot.recBotCoe with
    | bot => simp at h2
    | coe d =>
      induction d using WithTop.recTopCoe with
      | top => exact le_top
      | coe m =>
        have h2' : (n : ℕ∞) ≤ ((m : ℕ) : ℕ∞) + ((J.image z).card : ℕ∞) :=
          WithBot.coe_le_coe.mp h2
        have h4 : n ≤ m + (J.image z).card := by exact_mod_cast h2'
        exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (by omega))
  refine le_antisymm ?_ h3
  refine (ringKrullDim_le_spanFinrank_maximalIdeal (R := A ⧸ I)).trans ?_
  exact_mod_cast h1

/-- The stalk of a closed subscheme is the quotient of the ambient stalk by the stalk of the
ideal. -/
private noncomputable def stalkEquivQuotient {S X : Scheme.{0}} (ι : S ⟶ X) [IsClosedImmersion ι]
    (y : S) : X.presheaf.stalk (ι y) ⧸ IdealSheafData.stalk ι.ker (ι y) ≃+* S.presheaf.stalk y :=
  (Ideal.quotEquivOfEq
      (MMP.Resolution.Internal.TupleRestrictionLift.ker_stalkMap_eq_stalk_ker ι y).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (SurjectiveOnStalks.stalkMap_surjective ι y))

/-- **Codimension of a point of an snc stratum.** If the ideal of a closed subscheme `S` is,
at `ι y`, the sum of the ideals of the components `G ∈ J` of an snc divisor through `ι y`, then
`dim 𝒪_{S,y} + |J| = codim (ι y)`. -/
private theorem ringKrullDim_stalk_add_card_eq_coheight {R : Type*} [Zero R] {k : Type} [Field k]
    {X S : Scheme.{0}} [IsLocallyNoetherian X] {sX : X ⟶ Spec (.of k)}
    {D : MMP.Mori.DivisorWithCoeffs R X} (hD : D.IsSNC sX) {J : Finset (MMP.Mori.PrimeDivisor X)}
    (hJ : J ⊆ D.support) (ι : S ⟶ X) [IsClosedImmersion ι] (y : S)
    (hyJ : ∀ G ∈ J, ι y ∈ G.support)
    (hker : IdealSheafData.stalk ι.ker (ι y) =
      ⨆ G ∈ J, IdealSheafData.stalk G.idealSheaf (ι y)) :
    ringKrullDim (S.presheaf.stalk y) + J.card = Order.coheight (ι y) := by
  classical
  obtain ⟨N, z, j, hz, hj, hI⟩ := hD.2 (ι y)
  haveI := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz
  let jJ : J → Fin N := fun G => j ⟨G.1, hJ G.2, hyJ G.1 G.2⟩
  have hjJ : Function.Injective jJ := fun a b hab =>
    Subtype.ext (by simpa [jJ] using congrArg Subtype.val (hj hab))
  set J' : Finset (Fin N) := Finset.univ.image jJ with hJ'
  have hcard : J'.card = J.card := by
    rw [hJ', Finset.card_image_of_injective _ hjJ, Finset.card_univ, Fintype.card_coe]
  have hst : IdealSheafData.stalk ι.ker (ι y) = Ideal.span (z '' (J' : Set (Fin N))) := by
    rw [hker]
    exact iSup_stalk_idealSheaf_eq_span z j hI fun G hG => ⟨hJ hG, hyJ G hG⟩
  have hdim : ringKrullDim (S.presheaf.stalk y) = (N - J'.card : ℕ) := by
    rw [← ringKrullDim_eq_of_ringEquiv (stalkEquivQuotient ι y), hst]
    exact ringKrullDim_quotient_span_image' z hz J'
  have hN : ringKrullDim (X.presheaf.stalk (ι y)) = N := hz.2
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight] at hN
  have hle : J'.card ≤ N := (Finset.card_le_univ _).trans (by simp)
  rw [hdim, hN, ← hcard]
  norm_cast
  rw [Nat.sub_add_cancel hle]

private theorem stalkEquivQuotient_mk {S X : Scheme.{0}} (ι : S ⟶ X) [IsClosedImmersion ι] (y : S)
    (a : X.presheaf.stalk (ι y)) :
    stalkEquivQuotient ι y (Ideal.Quotient.mk _ a) = (ι.stalkMap y).hom a := rfl

open IsLocalRing in
/-- **The extra component restricts to a uniformizer.** In the situation of
`ringKrullDim_stalk_add_card_eq_coheight`, if `𝒪_{S,y}` has dimension one and `G ∉ J` is a
component of the snc divisor through `ι y` with local equation `π`, then the restriction of `π`
generates the maximal ideal of `𝒪_{S,y}`. -/
private theorem maximalIdeal_eq_span_stalkMap {R : Type*} [Zero R] {k : Type} [Field k]
    {X S : Scheme.{0}} [IsLocallyNoetherian X] {sX : X ⟶ Spec (.of k)}
    {D : MMP.Mori.DivisorWithCoeffs R X} (hD : D.IsSNC sX) {J : Finset (MMP.Mori.PrimeDivisor X)}
    (hJ : J ⊆ D.support) (ι : S ⟶ X) [IsClosedImmersion ι] (y : S)
    (hyJ : ∀ G ∈ J, ι y ∈ G.support)
    (hker : IdealSheafData.stalk ι.ker (ι y) =
      ⨆ G ∈ J, IdealSheafData.stalk G.idealSheaf (ι y))
    (hdim1 : ringKrullDim (S.presheaf.stalk y) = 1) {G : MMP.Mori.PrimeDivisor X}
    (hGD : G ∈ D.support) (hGJ : G ∉ J) (hyG : ι y ∈ G.support)
    {π : X.presheaf.stalk (ι y)} (hπ : IdealSheafData.stalk G.idealSheaf (ι y) = Ideal.span {π}) :
    maximalIdeal (S.presheaf.stalk y) = Ideal.span {(ι.stalkMap y).hom π} := by
  classical
  obtain ⟨N, z, j, hz, hj, hI⟩ := hD.2 (ι y)
  haveI := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz
  let jJ : J → Fin N := fun G => j ⟨G.1, hJ G.2, hyJ G.1 G.2⟩
  have hjJ : Function.Injective jJ := fun a b hab =>
    Subtype.ext (by simpa [jJ] using congrArg Subtype.val (hj hab))
  set J' : Finset (Fin N) := Finset.univ.image jJ with hJ'
  have hcard : J'.card = J.card := by
    rw [hJ', Finset.card_image_of_injective _ hjJ, Finset.card_univ, Fintype.card_coe]
  have hst : IdealSheafData.stalk ι.ker (ι y) = Ideal.span (z '' (J' : Set (Fin N))) := by
    rw [hker]
    exact iSup_stalk_idealSheaf_eq_span z j hI fun G hG => ⟨hJ hG, hyJ G hG⟩
  -- the index of `G`
  set iG := j ⟨G, hGD, hyG⟩ with hiG
  have hiGJ : iG ∉ J' := by
    intro h
    obtain ⟨G', -, hG'⟩ := Finset.mem_image.mp h
    have h1 : (G' : MMP.Mori.PrimeDivisor X) = G := by
      simpa using congrArg Subtype.val (hj hG')
    exact hGJ (h1 ▸ G'.2)
  have hdimq : ringKrullDim (X.presheaf.stalk (ι y) ⧸ Ideal.span (z '' (J' : Set (Fin N)))) =
      (N - J'.card : ℕ) := ringKrullDim_quotient_span_image' z hz J'
  have hN1 : N - J'.card = 1 := by
    rw [← ringKrullDim_eq_of_ringEquiv (stalkEquivQuotient ι y), hst, hdimq] at hdim1
    exact_mod_cast hdim1
  have hcompl : (J'ᶜ : Finset (Fin N)) = {iG} := by
    have hc : J'ᶜ.card = 1 := by rw [Finset.card_compl, Fintype.card_fin]; omega
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
    have : iG ∈ J'ᶜ := Finset.mem_compl.mpr hiGJ
    rw [ha, Finset.mem_singleton] at this
    rw [ha, this]
  set I := Ideal.span (z '' (J' : Set (Fin N))) with hIdef
  have hIm : I ≤ maximalIdeal _ := by
    rw [hIdef, Ideal.span_le]
    rintro _ ⟨i, -, rfl⟩
    rw [← hz.1]; exact Ideal.subset_span ⟨i, rfl⟩
  haveI : Nontrivial (X.presheaf.stalk (ι y) ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
    fun h => (maximalIdeal.isMaximal _).ne_top (top_le_iff.mp (h ▸ hIm))
  haveI := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hmax : (maximalIdeal _).map (Ideal.Quotient.mk I) = maximalIdeal (_ ⧸ I) := by
    have := IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [sup_eq_left.mpr hIm]
  have hgen : maximalIdeal (_ ⧸ I) = Ideal.span {Ideal.Quotient.mk I (z iG)} := by
    rw [← hmax, ← hz.1, Ideal.map_span]
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      by_cases hi : i ∈ J'
      · have : Ideal.Quotient.mk I (z i) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.subset_span ⟨i, hi, rfl⟩)
        simp [this]
      · have : i = iG := by
          have : i ∈ J'ᶜ := Finset.mem_compl.mpr hi
          rw [hcompl, Finset.mem_singleton] at this; exact this
        subst this
        exact Ideal.subset_span rfl
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.subset_span ⟨z iG, ⟨iG, rfl⟩, rfl⟩
  -- transport along `𝒪_{S,y} ≅ 𝒪_{X,ιy}/I`
  have e := (Ideal.quotEquivOfEq hst).symm.trans (stalkEquivQuotient ι y)
  have he : ∀ a, ((Ideal.quotEquivOfEq hst).symm.trans (stalkEquivQuotient ι y))
      (Ideal.Quotient.mk I a) = (ι.stalkMap y).hom a := fun a => rfl
  have hmaxS : maximalIdeal (S.presheaf.stalk y) =
      (maximalIdeal (_ ⧸ I)).map ((Ideal.quotEquivOfEq hst).symm.trans
        (stalkEquivQuotient ι y)) := by
    refine (IsLocalRing.eq_maximalIdeal ?_).symm
    exact Ideal.map_isMaximal_of_equiv _
  rw [hmaxS, hgen, Ideal.map_span, Set.image_singleton, he]
  -- `π` and `z iG` generate the same ideal
  haveI : IsDomain (X.presheaf.stalk (ι y)) := IsRegularLocalRing.isDomain _
  have hassoc : Associated π (z iG) := by
    have h1 := hI ⟨G, hGD, hyG⟩
    rw [hπ] at h1
    exact Ideal.span_singleton_eq_span_singleton.mp h1
  obtain ⟨u, hu⟩ := hassoc
  rw [← hu, map_mul]
  exact Ideal.span_singleton_mul_right_unit (u.isUnit.map _) _

private theorem stalk_eq_stalkIdeal {Z : Scheme.{0}} (I : Z.IdealSheafData) (x : Z) :
    IdealSheafData.stalk I x = I.stalkIdeal x := by
  unfold IdealSheafData.stalk Scheme.IdealSheafData.stalkIdeal
  exact iSup_subtype'

open IsLocalRing in
/-- If the ideal of `E` at `ι(η_P)` is principal, generated by `π`, and the restriction of `π`
generates the maximal ideal of `𝒪_{S,P}`, then the intersection length of `E` along `P` is one. -/
private theorem intersectionLength_eq_one {X S : Scheme.{0}} [IsLocallyNoetherian X]
    (ι : S ⟶ X) (E : MMP.Mori.PrimeDivisor X) (P : MMP.Mori.PrimeDivisor S)
    {π : X.presheaf.stalk (ι P.genericPoint)}
    (hπ : IdealSheafData.stalk E.idealSheaf (ι P.genericPoint) = Ideal.span {π})
    (hm : maximalIdeal (S.presheaf.stalk P.genericPoint) =
      Ideal.span {(ι.stalkMap P.genericPoint).hom π}) :
    E.intersectionLength ι P = 1 := by
  rw [MMP.Mori.PrimeDivisor.intersectionLength, ← stalk_eq_stalkIdeal, hπ, Ideal.map_span,
    Set.image_singleton, ← hm]
  rw [Module.length_eq_one_iff.mpr (isSimpleModule_iff_isCoatom.mpr
    (Ideal.isMaximal_def.mp (maximalIdeal.isMaximal _)))]
  rfl

open scoped Classical in
/-- **The restriction coefficient at a codimension-one point of a stratum.** For a divisor `Γ`
supported on an snc divisor `D`, with no component in `J`, and the stratum `S` cut out by `J`,
the coefficient of `Γ|_S` at a prime `P` of `S` is the sum of the coefficients of the components
of `Γ` through `ι(η_P)` (there is at most one). -/
private theorem coeff_restrict_eq_sum {k : Type} [Field k] {X S : Scheme.{0}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian S] {sX : X ⟶ Spec (.of k)} {R : Type*} [Zero R]
    {D : MMP.Mori.DivisorWithCoeffs R X} (hD : D.IsSNC sX) {J : Finset (MMP.Mori.PrimeDivisor X)}
    (hJ : J ⊆ D.support) (ι : S ⟶ X) [IsClosedImmersion ι] (P : MMP.Mori.PrimeDivisor S)
    (hyJ : ∀ G ∈ J, ι P.genericPoint ∈ G.support)
    (hker : IdealSheafData.stalk ι.ker (ι P.genericPoint) =
      ⨆ G ∈ J, IdealSheafData.stalk G.idealSheaf (ι P.genericPoint))
    (Γ : MMP.Mori.Divisor X) (hΓD : Γ.support ⊆ D.support) (hΓJ : ∀ G ∈ J, Γ.coeff G = 0)
    (hfin : (Function.support (MMP.Mori.DivisorWithCoeffs.restrictCoeff ι Γ)).Finite) :
    (Γ.restrict ι).coeff P =
      ∑ E ∈ Γ.support.filter (fun E => ι P.genericPoint ∈ E.support), Γ.coeff E := by
  classical
  have hdim1 : ringKrullDim (S.presheaf.stalk P.genericPoint) = 1 := by
    rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight, P.coheight_genericPoint]; rfl
  rw [MMP.Mori.DivisorWithCoeffs.coeff_restrict ι hfin P, Finsupp.sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun E hE => ?_
  by_cases hEy : ι P.genericPoint ∈ E.support
  · rw [if_pos hEy]
    have hEJ : E ∉ J := fun h => (Finsupp.mem_support_iff.mp hE) (hΓJ E h)
    obtain ⟨N, z, j, hz, hj, hI⟩ := hD.2 (ι P.genericPoint)
    have hπ := hI ⟨E, hΓD hE, hEy⟩
    have hm := maximalIdeal_eq_span_stalkMap hD hJ ι P.genericPoint hyJ hker hdim1 (hΓD hE) hEJ
      hEy hπ
    rw [intersectionLength_eq_one ι E P hπ hm, one_smul]
    rfl
  · rw [if_neg hEy, MMP.Mori.PrimeDivisor.intersectionLength_eq_zero_of_notMem ι E hEy, zero_smul]

end StratumLocalRings

section RestrictionToStrata

open CategoryTheory AlgebraicGeometry MMP.Mori

universe u

/-- Pull-back of `ℚ`-Cartier `ℚ`-divisors is additive. -/
private theorem qdivisor_isPullback_add {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} {G₁ G₂ : QDivisor Y}
    (hG₁ : G₁.IsQCartier) (hG₂ : G₂.IsQCartier)
    {h₁ : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ G₁.supp}
    {h₂ : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ G₂.supp}
    {R₁ R₂ : QDivisor X} (p₁ : G₁.IsPullback f h₁ R₁) (p₂ : G₂.IsPullback f h₂ R₂)
    (h : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ (G₁ + G₂).supp) :
    (G₁ + G₂).IsPullback f h (R₁ + R₂) := by
  intro m hm D hD hDc
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  obtain ⟨m₁, hm₁, A₁, hA₁, hA₁c⟩ := hG₁.exists_pos
  obtain ⟨m₂, hm₂, A₂, hA₂, hA₂c⟩ := hG₂.exists_pos
  have hm₁' : (m₁ : ℤ) ≠ 0 := by exact_mod_cast hm₁.ne'
  have hm₂' : (m₂ : ℤ) ≠ 0 := by exact_mod_cast hm₂.ne'
  obtain ⟨A₁', hA₁', p₁'⟩ := p₁ m₁ hm₁ A₁ hA₁ hA₁c
  obtain ⟨A₂', hA₂', p₂'⟩ := p₂ m₂ hm₂ A₂ hA₂ hA₂c
  have hsuppD : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ D.supp :=
    fun W hW => h W (by rwa [QDivisor.supp_eq_of_toQDivisor_eq hm' hD] at hW)
  -- the supports of the auxiliary divisors
  have hsupp : ∀ {G : QDivisor Y} (A : Divisor Y) (c : ℤ), c ≠ 0 →
      Divisor.toQDivisor A = c • G →
      (∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ G.supp) →
      ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ A.supp :=
    fun A c hc hA hG W hW => hG W (by rwa [QDivisor.supp_eq_of_toQDivisor_eq hc hA] at hW)
  set N : ℤ := (m₁ : ℤ) * m₂
  have hN : N ≠ 0 := mul_ne_zero hm₁' hm₂'
  set A : Divisor Y := (m : ℤ) • ((m₂ : ℤ) • A₁ + (m₁ : ℤ) • A₂)
  have hAD : A = N • D := by
    apply Divisor.toQDivisor_injective
    simp only [A, N, map_zsmul, map_add, hA₁, hA₂, hD, smul_add, smul_smul]
    congr 1 <;> congr 1 <;> ring
  have hAc : A.IsCartier := ((hA₁c.zsmul _).add (hA₂c.zsmul _)).zsmul _
  have hA₁N : Divisor.toQDivisor ((m₂ : ℤ) • A₁) = N • G₁ := by
    simp only [map_zsmul, hA₁, smul_smul, N]; congr 1; ring
  have hA₂N : Divisor.toQDivisor ((m₁ : ℤ) • A₂) = N • G₂ := by
    simp only [map_zsmul, hA₂, smul_smul, N]
  have hsum : Divisor.toQDivisor ((m₂ : ℤ) • A₁ + (m₁ : ℤ) • A₂) = N • (G₁ + G₂) := by
    rw [map_add, hA₁N, hA₂N, smul_add]
  have hAq : Divisor.toQDivisor A = ((m : ℤ) * N) • (G₁ + G₂) := by
    simp only [A, map_zsmul, hsum, smul_smul]
  have pA := ((p₁'.zsmul hA₁c (m₂ : ℤ) (hsupp _ _ hN hA₁N h₁)).add (hA₁c.zsmul _)
    (hA₂c.zsmul _) (hsupp _ _ hN hsum h) (p₂'.zsmul hA₂c (m₁ : ℤ) (hsupp _ _ hN hA₂N h₂))).zsmul
    ((hA₁c.zsmul _).add (hA₂c.zsmul _)) (m : ℤ)
    (hsupp _ _ (mul_ne_zero hm' hN) hAq h)
  obtain ⟨D', hD'⟩ := hDc.exists_isPullback hsuppD
  refine ⟨D', ?_, hD'⟩
  have pND := hD'.zsmul hDc N (hsupp _ _ (mul_ne_zero hN hm') (by
    rw [map_zsmul, hD, smul_smul]) h)
  have heq := pA.eq hAc (pND.of_eq hAD.symm)
  have heqQ := congrArg Divisor.toQDivisor heq
  simp only [map_zsmul, map_add, hA₁', hA₂', smul_smul] at heqQ
  ext E
  have := congrArg (fun G : QDivisor X => G.coeff E) heqQ
  simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add, zsmul_eq_mul,
    Divisor.coeff_toQDivisor, N] at this ⊢
  have hNq : ((m₁ : ℚ) * m₂) ≠ 0 := by positivity
  apply mul_left_cancel₀ hNq
  push_cast at this ⊢
  linear_combination -this

/-- On an integral scheme, the order `v_Q` of a unit of the factor `K(X)` is the order of
vanishing of its image in the function field. -/
private theorem ordUnit_eq_ord {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (Q : MMP.Mori.PrimeDivisor X) (v : (X.presheaf.stalk (componentGenericPoint X Q.component))ˣ) :
    Q.ordUnit v = X.ord ((MMP.Positivity.componentToFunctionField Q.component).hom v.val)
      Q.genericPoint := by
  classical
  let φ : (RationalFunctions X)ˣ :=
    (RationalFunctions.unitsEquiv X).symm (Pi.mulSingle Q.component v)
  have hφ : Units.map (RationalFunctions.component X Q.component).toMonoidHom φ = v := by
    ext
    change ((RationalFunctions.unitsEquiv X φ) Q.component).val = v.val
    simp [φ]
  have := MMP.Positivity.ord_eq_ord_componentToFunctionField Q φ
  rw [PrimeDivisor.ord_eq_ordUnit, hφ] at this
  rw [this]
  congr 2
  exact congrArg Units.val hφ

/-- Generization to the generic point commutes with generization between stalks. -/
private theorem algebraMap_stalkSpecializes' (X : Scheme.{u}) [IsIntegral X] {x x' : X}
    (h : x ⤳ x') (z : X.presheaf.stalk x') :
    algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.stalkSpecializes h z) =
      algebraMap (X.presheaf.stalk x') X.functionField z := by
  change (X.presheaf.stalkSpecializes h ≫ X.presheaf.stalkSpecializes _).hom z = _
  rw [TopCat.Presheaf.stalkSpecializes_comp]
  rfl

/-- Generization from a stalk to a component, then to the function field, is generization to the
function field. -/
private theorem componentToFunctionField_stalkSpecializes (X : Scheme.{u}) [IsIntegral X]
    (Z : irreducibleComponents X) {x : X} (h : componentGenericPoint X Z ⤳ x)
    (z : X.presheaf.stalk x) :
    (MMP.Positivity.componentToFunctionField Z).hom (X.presheaf.stalkSpecializes h z) =
      algebraMap (X.presheaf.stalk x) X.functionField z :=
  algebraMap_stalkSpecializes' X h z

/-- `componentToFunctionField_stalkSpecializes` for `stalkToRationalFunctions`. -/
private theorem componentToFunctionField_stalkToRationalFunctions (X : Scheme.{u}) [IsIntegral X]
    {Z : irreducibleComponents X} {x : X} (hx : x ∈ Z.1) (z : X.presheaf.stalk x) :
    (MMP.Positivity.componentToFunctionField Z).hom ((stalkToRationalFunctions X hx).hom z) =
      algebraMap (X.presheaf.stalk x) X.functionField z :=
  componentToFunctionField_stalkSpecializes X Z _ z

/-- If `f b = a` with `f, b ≠ 0`, then `ord f = ord a - ord b`. -/
private theorem ord_eq_sub_of_mul_eq {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {f a b : X.functionField}
    (hf : f ≠ 0) (hb : b ≠ 0) (h : f * b = a) (z : X) : X.ord f z = X.ord a z - X.ord b z := by
  rw [← h, Scheme.ord_mul hf hb]; ring

/-- **Restriction to a smooth divisor is the Cartier pull-back.** For a smooth variety `Y` and a
smooth integral `j : T ⟶ Y` of codimension one, the restriction `G|_T` by intersection lengths is
the pull-back `j^*G` of every divisor `G` not containing `T`. -/
private theorem divisor_isPullback_restrict {k : Type u} [Field k] {Y T : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [Smooth sY]
    (j : T ⟶ Y) [IsClosedImmersion j] [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    [CompactSpace T] [Smooth (j ≫ sY)]
    (G : Divisor Y) (hG : ∀ W : irreducibleComponents T, j (componentGenericPoint T W) ∉ G.supp) :
    G.IsPullback j hG (G.restrict j) := by
  classical
  have : AlgebraicGeometry.IsNoetherian T := ⟨⟩
  intro U φ hφ Q hQ
  set η := componentGenericPoint T Q.component
  have hηT : η = genericPoint T := componentGenericPoint_eq_genericPoint _
  have hgen : ∀ s : T, Order.coheight s = 0 → s = η := fun s hs => by
    have hle : s ≤ genericPoint T := genericPoint_specializes s
    rw [hηT]
    exact (Specializes.antisymm (Order.coheight_eq_zero.mp hs hle) hle).eq
  have hηQ : η ⤳ Q.genericPoint := Q.specializes_genericPoint
  set y' := j Q.genericPoint
  set y := j η with hydef
  have hsp : y ⤳ y' := j.base.hom.map_specializes hηQ
  have hy'U : y' ∈ U := (Q.genericPoint_mem_iff (j ⁻¹ᵁ U)).mpr hQ
  have hyU : y ∈ U := hsp.mem_open U.isOpen hy'U
  have hyG : y ∉ G.supp := hG Q.component
  -- the coefficient of the restriction
  have hD : ∀ E ∈ G.support, ∀ s : T, Order.coheight s = 0 → j s ∉ E.support := by
    intro E hE s hs hjs
    rw [hgen s hs] at hjs
    exact hyG (DivisorWithCoeffs.support_subset_supp (Finsupp.mem_support_iff.mp hE) hjs)
  rw [DivisorWithCoeffs.coeff_restrict j (DivisorWithCoeffs.finite_support_restrictCoeff j G hD) Q]
  -- the local equation as a fraction at `y'`
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hyU hyG (mem_pointComponent y)
  rw [pullbackComponent_eq hG hφ _ (mem_pointComponent y) a ha]
  let := (Y.presheaf.stalkSpecializes hsp).hom.toAlgebra
  have := MMP.Intersection.isLocalization_stalkSpecializes hsp
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.mk'_surjective
    ((IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).comap
      (Y.presheaf.stalkSpecializes hsp).hom).primeCompl a.val
  have hrs' : a.val * Y.presheaf.stalkSpecializes hsp s.val =
      Y.presheaf.stalkSpecializes hsp r := by
    rw [← hrs]
    exact IsLocalization.mk'_spec _ r s
  have hsU : IsUnit (Y.presheaf.stalkSpecializes hsp s.val) := by
    have := s.2
    simpa [Ideal.primeCompl, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using this
  have hrU : IsUnit (Y.presheaf.stalkSpecializes hsp r) := hrs' ▸ a.isUnit.mul hsU
  -- the restrictions to `T`
  have hcomp : ∀ x, (j.stalkMap η).hom (Y.presheaf.stalkSpecializes hsp x) =
      T.presheaf.stalkSpecializes hηQ ((j.stalkMap Q.genericPoint).hom x) := fun x =>
    Scheme.Hom.stalkSpecializes_stalkMap_apply j _ _ hηQ x
  have hTne : ∀ x, IsUnit (Y.presheaf.stalkSpecializes hsp x) →
      algebraMap (T.presheaf.stalk Q.genericPoint) T.functionField
        ((j.stalkMap Q.genericPoint).hom x) ≠ 0 ∧ (j.stalkMap Q.genericPoint).hom x ≠ 0 := by
    intro x hx
    have h1 : IsUnit (algebraMap (T.presheaf.stalk Q.genericPoint) T.functionField
        ((j.stalkMap Q.genericPoint).hom x)) := by
      rw [← componentToFunctionField_stalkSpecializes T Q.component hηQ, ← hcomp]
      exact (hx.map _).map _
    refine ⟨h1.ne_zero, fun h0 => h1.ne_zero (by rw [h0, map_zero])⟩
  have hYne : ∀ x, IsUnit (Y.presheaf.stalkSpecializes hsp x) →
      algebraMap (Y.presheaf.stalk y') Y.functionField x ≠ 0 := by
    intro x hx
    rw [← algebraMap_stalkSpecializes' Y hsp]
    exact (hx.map _).ne_zero
  -- the right-hand side
  rw [ordUnit_eq_ord]
  have hu : (MMP.Positivity.componentToFunctionField Q.component).hom
      (Units.map (j.stalkMap η).hom.toMonoidHom a).val *
        algebraMap (T.presheaf.stalk Q.genericPoint) T.functionField
          ((j.stalkMap Q.genericPoint).hom s.val) =
      algebraMap (T.presheaf.stalk Q.genericPoint) T.functionField
        ((j.stalkMap Q.genericPoint).hom r) := by
    rw [← componentToFunctionField_stalkSpecializes T Q.component hηQ,
      ← componentToFunctionField_stalkSpecializes T Q.component hηQ, ← hcomp, ← hcomp, ← hrs',
      map_mul, map_mul]
    rfl
  rw [ord_eq_sub_of_mul_eq (((Units.map (j.stalkMap η).hom.toMonoidHom a).isUnit.map _).ne_zero)
    (hTne _ hsU).1 hu]
  obtain ⟨Sr, -, hfr⟩ := Q.ord_stalkMap_eq_sum_intersectionLength_mul_ord sY j r (hTne _ hrU).2
  obtain ⟨Ss, -, hfs⟩ := Q.ord_stalkMap_eq_sum_intersectionLength_mul_ord sY j s.val
    (hTne _ hsU).2
  set S := G.support ∪ Sr ∪ Ss
  rw [hfr S (fun E hE => by simp [S, hE]), hfs S (fun E hE => by simp [S, hE]),
    ← Finset.sum_sub_distrib]
  -- the left-hand side
  have hGE : ∀ E : MMP.Mori.PrimeDivisor Y, y' ∈ E.support →
      G E = Y.ord (algebraMap (Y.presheaf.stalk y') Y.functionField r) E.genericPoint -
        Y.ord (algebraMap (Y.presheaf.stalk y') Y.functionField s.val) E.genericPoint := by
    intro E hE
    have h1 := hφ E ⟨y', hE, hy'U⟩
    rw [MMP.Positivity.ord_eq_ord_componentToFunctionField] at h1
    rw [(subsingleton_irreducibleComponents (X := Y)).elim E.component (pointComponent y)] at h1
    change G.coeff E = _
    rw [h1, ← ha, componentToFunctionField_stalkToRationalFunctions]
    have hmul : algebraMap (Y.presheaf.stalk y) Y.functionField a.val *
        algebraMap (Y.presheaf.stalk y') Y.functionField s.val =
        algebraMap (Y.presheaf.stalk y') Y.functionField r := by
      rw [← algebraMap_stalkSpecializes' Y hsp, ← algebraMap_stalkSpecializes' Y hsp r, ← hrs',
        map_mul]
    exact ord_eq_sub_of_mul_eq ((a.isUnit.map _).ne_zero) (hYne _ hsU) hmul _
  rw [Finsupp.sum, Finset.sum_subset (s₁ := G.support) (s₂ := S) (by
    intro E hE; simp [S, hE]) (by
    intro E _ hE
    rw [Finsupp.notMem_support_iff] at hE
    simp [hE])]
  refine Finset.sum_congr rfl fun E _ => ?_
  by_cases hE : j Q.genericPoint ∈ E.support
  · simp only [hE, ↓reduceIte]
    rw [← mul_sub, nsmul_eq_mul, hGE E hE]
  · simp only [hE, ↓reduceIte, PrimeDivisor.intersectionLength_eq_zero_of_notMem j E hE, zero_smul,
      sub_zero]

open scoped Classical in
/-- **Coefficients of the restriction to a floor component.** On an snc subboundary pair
`(S, B_S)`, for a prime `P` with `B_S(P) = 1` and `ι : T ⟶ S` the closed immersion of the
smooth subscheme `P`, the pull-back `B_T` of `B_S - P` has, at a prime `Q` of `T`, the sum of the
coefficients of the other components of `B_S` through `ι(η_Q)`. -/
private theorem coeff_isPullback_sub_single {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {S T : Scheme.{0}} {sS : S ⟶ Spec (.of k)} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    {BS : QDivisor S} (h : IsSNCSubboundaryPair sS BS) (P : MMP.Mori.PrimeDivisor S)
    (hP : BS.coeff P = 1) (ι : T ⟶ S) [IsClosedImmersion ι] [IsIntegral T]
    [IsLocallyNoetherian T] [IsNormal T] [Smooth (ι ≫ sS)] (hker : ι.ker = P.idealSheaf)
    {hgen : ∀ Z : irreducibleComponents T, ι (componentGenericPoint T Z) ∉
      (BS - Finsupp.single P 1).supp}
    {BT : QDivisor T} (hBT : (BS - Finsupp.single P 1).IsPullback ι hgen BT)
    (Q : MMP.Mori.PrimeDivisor T) :
    BT.coeff Q = ∑ E ∈ BS.support.filter
      (fun E => ι Q.genericPoint ∈ E.support ∧ E ≠ P), BS.coeff E := by
  haveI : LocallyOfFiniteType sS := h.isProjectiveVariety.toIsVariety.toLocallyOfFiniteType
  haveI : LocallyOfFinitePresentation sS :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := sS)).mpr inferInstance
  haveI : Smooth sS := (MMP.Mori.isSmoothScheme_iff sS).1 h.isSmoothScheme
  haveI : CompactSpace S := haveI := h.isProjectiveVariety.toIsVariety.toQuasiCompact
    QuasiCompact.compactSpace_of_compactSpace sS
  haveI : CompactSpace T := ι.isClosedEmbedding.compactSpace
  haveI : AlgebraicGeometry.IsNoetherian T := {}
  -- an integral multiple
  obtain ⟨m, hm, hmc⟩ :=
    (isQCartier_of_isSmoothScheme h.isSmoothScheme (BS - Finsupp.single P 1)).exists_pos
  obtain ⟨D, hD, hDc⟩ := hmc
  obtain ⟨D', hD', hpb⟩ := hBT m hm D hD hDc
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have hgenD : ∀ Z : irreducibleComponents T, ι (componentGenericPoint T Z) ∉ D.supp :=
    fun Z hZ => hgen Z (by rwa [QDivisor.supp_eq_of_toQDivisor_eq hm' hD] at hZ)
  have hres := divisor_isPullback_restrict sS ι D hgenD
  have hDD : D' = D.restrict ι := hpb.eq hDc hres
  -- the coefficients of `D`
  have hDcoeff : ∀ E, (D.coeff E : ℚ) = m * (BS.coeff E - if E = P then 1 else 0) := by
    intro E
    have := congrArg (fun G : QDivisor S => G.coeff E) hD
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_sub,
      zsmul_eq_mul] at this
    rw [this]
    congr 2
    change (Finsupp.single P (1 : ℚ)) E = _
    rw [Finsupp.single_apply]
    by_cases hE : E = P
    · subst hE; simp
    · simp [hE, Ne.symm hE]
  have hDP : D.coeff P = 0 := by
    have := hDcoeff P; rw [hP, if_pos rfl, sub_self, mul_zero] at this; exact_mod_cast this
  have hDsupp : D.support ⊆ BS.support := by
    intro E hE
    rw [Finsupp.mem_support_iff] at hE ⊢
    intro h0
    apply hE
    have := hDcoeff E
    change BS.coeff E = 0 at h0
    by_cases hEP : E = P
    · subst hEP; exact hDP
    · rw [h0, if_neg hEP] at this; simp at this; exact_mod_cast this
  have hrange : Set.range ι.base = (P.support : Set S) := by
    have h1 : (ι.ker.support : Set S) = closure (Set.range ι) := Scheme.Hom.support_ker ι
    rw [ι.isClosedEmbedding.isClosed_range.closure_eq, hker] at h1
    exact h1.symm
  have hyJ : ∀ G ∈ ({P} : Finset _), ι Q.genericPoint ∈ G.support := by
    intro G hG; rw [Finset.mem_singleton] at hG; subst hG
    rw [← hrange]; exact ⟨_, rfl⟩
  have hkerst : IdealSheafData.stalk ι.ker (ι Q.genericPoint) =
      ⨆ G ∈ ({P} : Finset _), IdealSheafData.stalk G.idealSheaf (ι Q.genericPoint) := by
    rw [hker]; simp
  have hD0 : ∀ E ∈ D.support, ∀ s : T, Order.coheight s = 0 → ι s ∉ E.support := by
    intro E hE s hs hmem
    have : s = componentGenericPoint T (MMP.Mori.pointComponent s) := by
      rw [componentGenericPoint_eq_genericPoint]
      have hle : s ≤ genericPoint T := genericPoint_specializes s
      exact (Specializes.antisymm (Order.coheight_eq_zero.mp hs hle) hle).eq
    rw [this] at hmem
    exact hgenD _ (DivisorWithCoeffs.support_subset_supp (Finsupp.mem_support_iff.mp hE) hmem)
  have hsum := coeff_restrict_eq_sum h.isSNC (J := {P})
    (Finset.singleton_subset_iff.mpr (Finsupp.mem_support_iff.mpr (by
      change BS.coeff P ≠ 0; rw [hP]; norm_num))) ι Q hyJ hkerst D hDsupp
    (fun G hG => by rw [Finset.mem_singleton] at hG; subst hG; exact hDP)
    (DivisorWithCoeffs.finite_support_restrictCoeff ι D hD0)
  rw [← hDD] at hsum
  have hBQ : (m : ℚ) * BT.coeff Q = D'.coeff Q := by
    have := congrArg (fun G : QDivisor T => G.coeff Q) hD'
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at this
    exact this.symm
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  apply mul_left_cancel₀ hmq
  rw [hBQ, hsum]
  push_cast
  rw [Finset.mul_sum]
  have h1 : ∑ x ∈ D.support.filter (fun x => ι Q.genericPoint ∈ x.support),
      ((D.coeff x : ℤ) : ℚ) =
      ∑ x ∈ BS.support.filter (fun x => ι Q.genericPoint ∈ x.support ∧ x ≠ P),
        ((D.coeff x : ℤ) : ℚ) := by
    refine Finset.sum_subset_zero_on_sdiff ?_ ?_ (fun _ _ => rfl)
    · intro E hE
      obtain ⟨hE1, hE2⟩ := Finset.mem_filter.mp hE
      refine Finset.mem_filter.mpr ⟨hDsupp hE1, hE2, fun hEP => ?_⟩
      subst hEP
      exact (Finsupp.mem_support_iff.mp hE1) hDP
    · intro E hE
      obtain ⟨hE1, hE2⟩ := Finset.mem_sdiff.mp hE
      obtain ⟨-, hthr, -⟩ := Finset.mem_filter.mp hE1
      have : E ∉ D.support := fun h => hE2 (Finset.mem_filter.mpr ⟨h, hthr⟩)
      rw [Finsupp.notMem_support_iff] at this
      change ((D.coeff E : ℤ) : ℚ) = 0
      rw [show D.coeff E = 0 from this]; simp
  rw [h1]
  refine Finset.sum_congr rfl fun E hE => ?_
  obtain ⟨-, -, hEP⟩ := Finset.mem_filter.mp hE
  rw [hDcoeff E, if_neg hEP, sub_zero]

open scoped Classical in
/-- **Adjunction to a floor component of an snc subboundary pair.** For an snc subboundary pair
`(S, B_S)` and a prime `P` with `B_S(P) = 1`, the pull-back of `B_S - P` to `P` makes `P` an snc
subboundary pair. -/
private theorem isSNCSubboundaryPair_of_isPullback_sub_single {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {S : Scheme.{0}} {sS : S ⟶ Spec (.of k)} [IsIntegral S] [IsLocallyNoetherian S]
    [IsNormal S] {BS : QDivisor S} (h : IsSNCSubboundaryPair sS BS) (P : MMP.Mori.PrimeDivisor S)
    (hP : BS.coeff P = 1) [IsLocallyNoetherian P.idealSheaf.subscheme]
    [IsNormal P.idealSheaf.subscheme]
    {hgen : ∀ Z : irreducibleComponents P.idealSheaf.subscheme,
      P.idealSheaf.subschemeι (componentGenericPoint _ Z) ∉ (BS - Finsupp.single P 1).supp}
    {BT : QDivisor P.idealSheaf.subscheme}
    (hBT : (BS - Finsupp.single P 1).IsPullback P.idealSheaf.subschemeι hgen BT) :
    IsSNCSubboundaryPair (P.idealSheaf.subschemeι ≫ sS) BT := by
  set ι := P.idealSheaf.subschemeι with hι
  haveI := P.integral
  have hPsupp : P ∈ BS.support := Finsupp.mem_support_iff.mpr (by
    change BS.coeff P ≠ 0; rw [hP]; norm_num)
  haveI hv : AlgebraicGeometry.IsVariety k sS := h.isProjectiveVariety.toIsVariety
  haveI : LocallyOfFiniteType sS := hv.toLocallyOfFiniteType
  haveI : LocallyOfFinitePresentation sS :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := sS)).mpr inferInstance
  haveI : Smooth sS := (MMP.Mori.isSmoothScheme_iff sS).1 h.isSmoothScheme
  have hsmT : IsSmoothScheme (ι ≫ sS) := h.isSNC.1 P hPsupp
  haveI : LocallyOfFinitePresentation (ι ≫ sS) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := ι ≫ sS)).mpr inferInstance
  haveI : Smooth (ι ≫ sS) := (MMP.Mori.isSmoothScheme_iff _).1 hsmT
  haveI : AlgebraicGeometry.IsVariety k (ι ≫ sS) := ⟨⟩
  haveI : CompactSpace S := haveI := hv.toQuasiCompact
    QuasiCompact.compactSpace_of_compactSpace sS
  haveI : CompactSpace P.idealSheaf.subscheme := ι.isClosedEmbedding.compactSpace
  haveI : AlgebraicGeometry.IsNoetherian P.idealSheaf.subscheme := {}
  have hker : ι.ker = P.idealSheaf := P.idealSheaf.ker_subschemeι
  have hrange : Set.range ι.base = (P.support : Set S) := by
    rw [hι, Scheme.IdealSheafData.range_subschemeι]
  have hyJ : ∀ (y : P.idealSheaf.subscheme), ∀ G ∈ ({P} : Finset _), ι y ∈ G.support := by
    intro y G hG
    rw [Finset.mem_singleton.mp hG, ← hrange]
    exact ⟨y, rfl⟩
  have hkerst : ∀ y : P.idealSheaf.subscheme, IdealSheafData.stalk ι.ker (ι y) =
      ⨆ G ∈ ({P} : Finset _), IdealSheafData.stalk G.idealSheaf (ι y) := fun y => by
    rw [hker]; simp
  have hcoeff := coeff_isPullback_sub_single h P hP ι hker hBT
  refine ⟨?_, hsmT, ?_, ?_⟩
  · exact (AlgebraicGeometry.isProjectiveVariety_iff_isProjectiveMorphism k _).mpr
      ((MMP.isProjectiveMorphism_of_isClosedImmersion ι).comp
        h.isProjectiveVariety.isProjective)
  · set D' := BS.support.erase P with hD'
    set R : MMP.Mori.Divisor S := ∑ E ∈ D', Finsupp.single E (1 : ℤ) with hRdef
    have hRcoeff : ∀ E, R.coeff E = if E ∈ D' then 1 else 0 := by
      intro E
      change (∑ E' ∈ D', Finsupp.single E' (1 : ℤ)) E = _
      rw [Finsupp.finset_sum_apply]
      simp only [Finsupp.single_apply]
      rw [Finset.sum_ite_eq']
    have hsnc0 : MMP.Mori.DivisorWithCoeffs.IsSNC sS (Finsupp.single P (1 : ℤ) + R) := by
      refine h.isSNC.of_support_subset fun E hE => ?_
      rw [Finsupp.mem_support_iff] at hE
      by_cases hEP : E = P
      · subst hEP; exact hPsupp
      · have : R.coeff E ≠ 0 := by
          intro h0; apply hE
          change (Finsupp.single P (1 : ℤ)) E + R.coeff E = 0
          rw [h0, Finsupp.single_apply, if_neg (Ne.symm hEP)]; rfl
        rw [hRcoeff] at this
        split_ifs at this with hED
        · exact Finset.mem_of_mem_erase hED
        · exact absurd rfl this
    obtain ⟨hR, -⟩ := MMP.Mori.DivisorWithCoeffs.isSNC_restrictPrimeDivisor_sum_single sS P D'
      (Finset.notMem_erase P _) hsnc0
    refine hR.of_support_subset fun Q hQ => ?_
    have hQ0 : BT.coeff Q ≠ 0 := Finsupp.mem_support_iff.mp hQ
    rw [hcoeff Q] at hQ0
    obtain ⟨E, hEF, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hQ0
    obtain ⟨hEB, hEx, hEP⟩ := Finset.mem_filter.mp hEF
    have hRsupp : R.support ⊆ BS.support := by
      intro E' hE'
      have : R.coeff E' ≠ 0 := Finsupp.mem_support_iff.mp hE'
      rw [hRcoeff] at this
      split_ifs at this with hED
      · exact Finset.mem_of_mem_erase hED
      · exact absurd rfl this
    have hRP : R.coeff P = 0 := by rw [hRcoeff, if_neg (Finset.notMem_erase P _)]
    have hgenP : ι (genericPoint P.idealSheaf.subscheme) = P.genericPoint := by
      have h1 : IsGenericPoint (ι (genericPoint P.idealSheaf.subscheme)) (P.support : Set S) := by
        have := (genericPoint_spec P.idealSheaf.subscheme).image ι.base.hom.continuous
        rwa [Set.image_univ, ι.isClosedEmbedding.isClosed_range.closure_eq, hrange] at this
      have h2 : IsGenericPoint P.genericPoint (P.support : Set S) := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact isGenericPoint_closure
      exact h1.eq h2
    have hR0 : ∀ E' ∈ R.support, ∀ s : P.idealSheaf.subscheme, Order.coheight s = 0 →
        ι s ∉ E'.support := by
      intro E' hE' s hs hmem
      have hs' : s = genericPoint P.idealSheaf.subscheme := by
        have hle : s ≤ genericPoint _ := genericPoint_specializes s
        exact (Specializes.antisymm (Order.coheight_eq_zero.mp hs hle) hle).eq
      rw [hs', hgenP] at hmem
      obtain rfl := MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support hmem
      exact (Finsupp.mem_support_iff.mp hE') hRP
    have hsumR := coeff_restrict_eq_sum h.isSNC (J := {P})
      (Finset.singleton_subset_iff.mpr hPsupp) ι Q (hyJ _) (hkerst _) R hRsupp
      (fun G hG => by rw [Finset.mem_singleton] at hG; subst hG; exact hRP)
      (MMP.Mori.DivisorWithCoeffs.finite_support_restrictCoeff ι R hR0)
    rw [Finsupp.mem_support_iff]
    change (R.restrict ι).coeff Q ≠ 0
    rw [hsumR]
    have hED' : E ∈ D' := Finset.mem_erase.mpr ⟨hEP, hEB⟩
    have hER : E ∈ R.support := Finsupp.mem_support_iff.mpr (by
      change R.coeff E ≠ 0; rw [hRcoeff, if_pos hED']; norm_num)
    refine ne_of_gt (Finset.sum_pos' (fun E' hE' => ?_) ⟨E, Finset.mem_filter.mpr ⟨hER, hEx⟩, ?_⟩)
    · have : E' ∈ D' := by
        have := Finsupp.mem_support_iff.mp (Finset.mem_filter.mp hE').1
        change R.coeff E' ≠ 0 at this
        rw [hRcoeff] at this
        split_ifs at this with h'
        · exact h'
        · exact absurd rfl this
      rw [hRcoeff, if_pos this]; norm_num
    · rw [hRcoeff, if_pos hED']; norm_num
  · intro Q
    rw [hcoeff Q]
    set x := ι Q.genericPoint
    set F := BS.support.filter (fun E => x ∈ E.support ∧ E ≠ P) with hF
    have hxP : x ∈ P.support := hyJ _ P (Finset.mem_singleton_self P)
    have hdim := ringKrullDim_stalk_add_card_eq_coheight h.isSNC
      (Finset.singleton_subset_iff.mpr hPsupp) ι Q.genericPoint (hyJ _) (hkerst _)
    rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight, Q.coheight_genericPoint] at hdim
    obtain ⟨c, hc, hcard⟩ := card_le_coheight_of_isSNC h.isSNC x (insert P F)
      (Finset.insert_subset hPsupp (Finset.filter_subset _ _)) (fun G hG => by
        rcases Finset.mem_insert.mp hG with rfl | hG
        · exact hxP
        · exact (Finset.mem_filter.mp hG).2.1)
    have hc2 : c = 2 := by
      rw [hc, Finset.card_singleton] at hdim
      have h3 : ((1 + 1 : ℕ) : WithBot ℕ∞) = ((c : ℕ) : WithBot ℕ∞) := by exact_mod_cast hdim
      have h4 : (1 + 1 : ℕ) = c := by exact_mod_cast h3
      omega
    have hPF : P ∉ F := fun h' => (Finset.mem_filter.mp h').2.2 rfl
    rw [Finset.card_insert_of_notMem hPF, hc2] at hcard
    rcases Finset.eq_empty_or_nonempty F with hF0 | ⟨E, hE⟩
    · rw [hF0, Finset.sum_empty]; norm_num
    · have : F = {E} := by
        refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hE, fun E' hE' => ?_⟩
        by_contra hne
        have : 2 ≤ F.card := Finset.one_lt_card.mpr ⟨E', hE', E, hE, hne⟩
        omega
      rw [this, Finset.sum_singleton]
      exact h.coeff_le_one E

/-- In a domain, a nonzero prime contained in a prime of height one is equal to it. -/
private theorem eq_of_le_of_height_eq_one {A : Type*} [CommRing A] [IsDomain A] {I q : Ideal A}
    [I.IsPrime] [q.IsPrime] (hI : I ≠ ⊥) (hle : I ≤ q) (hq : q.height = 1) : I = q := by
  by_contra hne
  have : q.FiniteHeight := Ideal.finiteHeight_iff_lt.mpr (Or.inr (by rw [hq]; simp))
  have h1 := Ideal.height_strict_mono_of_isPrime_of_isPrime (lt_of_le_of_ne hle hne)
  rw [hq, ENat.lt_one_iff_eq_zero, Ideal.height_eq_zero_iff_eq_bot] at h1
  exact hI h1

/-- A member of a regular system of parameters lying in the stalk of the ideal of a prime divisor
generates it. -/
private theorem stalk_idealSheaf_eq_span_of_mem {X : Scheme.{0}} [IsLocallyNoetherian X]
    (P : MMP.Mori.PrimeDivisor X) {y : X} (hy : y ∈ P.support) {m : ℕ}
    {w : Fin m → X.presheaf.stalk y} (hw : MMP.Mori.IsRegularSystemOfParameters w) (j0 : Fin m)
    (hmem : w j0 ∈ AlgebraicGeometry.IdealSheafData.stalk P.idealSheaf y) :
    AlgebraicGeometry.IdealSheafData.stalk P.idealSheaf y = Ideal.span {w j0} := by
  obtain ⟨q, -, hPq, hq1⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support P hy
  have := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hw
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk y)
  have := MMP.Resolution.isPrime_span_singleton_of_isRegularSystemOfParameters hw j0
  rw [hPq]
  refine (eq_of_le_of_height_eq_one ?_ ?_ hq1).symm
  · rw [Ne, Ideal.span_singleton_eq_bot]
    exact MMP.Resolution.ne_zero_of_isRegularSystemOfParameters hw j0
  · rw [Ideal.span_le, Set.singleton_subset_iff, ← hPq]
    exact hmem

/-- If the image of the generic point of a prime divisor `E` of `T` lies on a prime divisor `G` of
`S`, the pull-back of a local equation of `G` lies in the ideal of `E`. -/
private theorem stalkMap_mem_stalk_idealSheaf {S T : Scheme.{0}} [IsLocallyNoetherian S]
    [IsLocallyNoetherian T] (ι : T ⟶ S) (E : MMP.Mori.PrimeDivisor T)
    (G : MMP.Mori.PrimeDivisor S) (hEG : ι E.genericPoint ∈ G.support) (y : T)
    {π : S.presheaf.stalk (ι y)}
    (hπ : AlgebraicGeometry.IdealSheafData.stalk G.idealSheaf (ι y) = Ideal.span {π}) :
    (ι.stalkMap y).hom π ∈ AlgebraicGeometry.IdealSheafData.stalk E.idealSheaf y := by
  have hJ : G.idealSheaf.comap ι ≤ E.idealSheaf := by
    have := E.integral
    rw [Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme E.idealSheaf _ rfl,
      ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
    intro z hz
    rw [Scheme.IdealSheafData.support_comap]
    change ι z ∈ G.support
    have hzE : z ∈ closure {E.genericPoint} := by
      rwa [← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    have hcl : closure {E.genericPoint} ⊆ ι.base ⁻¹' (G.support : Set S) :=
      closure_minimal (Set.singleton_subset_iff.mpr hEG)
        (G.idealSheaf.support.isClosed.preimage ι.continuous)
    exact hcl hzE
  apply MMP.Resolution.stalk_le_stalk_of_le hJ y
  rw [AlgebraicGeometry.IdealSheafData.stalk_comap, hπ, Ideal.map_span, Set.image_singleton]
  exact Ideal.subset_span rfl

end RestrictionToStrata

section QuotientParameters

open IsLocalRing

/-- Modulo part `z(J)` of a regular system of parameters, the remaining members form a regular
system of parameters of the quotient. -/
private theorem isRegularSystemOfParameters_quotient {A : Type*} [CommRing A] [IsRegularLocalRing A]
    {n : ℕ} (z : Fin n → A) (hz : MMP.Mori.IsRegularSystemOfParameters z) (J : Finset (Fin n))
    (e : Fin (n - J.card) ≃ (Jᶜ : Finset (Fin n))) :
    haveI := (MMP.Resolution.isRegularLocalRing_quotient_span_image z hz J).toIsLocalRing
    MMP.Mori.IsRegularSystemOfParameters
      (fun i => Ideal.Quotient.mk (Ideal.span (z '' (J : Set (Fin n)))) (z (e i))) := by
  classical
  haveI := (MMP.Resolution.isRegularLocalRing_quotient_span_image z hz J).toIsLocalRing
  set I := Ideal.span (z '' (J : Set (Fin n))) with hI
  have hIm : I ≤ maximalIdeal A := by
    rw [hI, Ideal.span_le]
    rintro _ ⟨j, -, rfl⟩
    rw [← hz.1]; exact Ideal.subset_span ⟨j, rfl⟩
  have hmax : (maximalIdeal A).map (Ideal.Quotient.mk I) = maximalIdeal (A ⧸ I) := by
    have := IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [sup_eq_left.mpr hIm]
  refine ⟨?_, ?_⟩
  · rw [← hmax, ← hz.1, Ideal.map_span]
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact Ideal.subset_span ⟨z (e i), ⟨e i, rfl⟩, rfl⟩
    · rw [Ideal.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      by_cases hi : i ∈ J
      · have : Ideal.Quotient.mk I (z i) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.subset_span ⟨i, hi, rfl⟩)
        rw [SetLike.mem_coe, this]; exact Submodule.zero_mem _
      · obtain ⟨a, ha⟩ := e.surjective ⟨i, Finset.mem_compl.mpr hi⟩
        exact Ideal.subset_span ⟨a, by simp only [ha]; rfl⟩
  · rw [ringKrullDim_quotient_span_image' z hz J]

end QuotientParameters

section AdjunctionSteps

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold

/-- One adjunction step on a smooth variety, given a form with a simple pole: the different is
the restriction of `B_S - P`. -/
private theorem isPullback_sub_single_of_isAdjunctionStep_of_form {k : Type} [Field k] [CharZero k]
    {S T : Scheme.{0}} {sS : S ⟶ Spec (.of k)} [IsIntegral S] [IsNormal S]
    [IsLocallyNoetherian S] [CompactSpace S] [LocallyOfFiniteType sS]
    (hSv : AlgebraicGeometry.IsVariety k sS) [Smooth sS] {n : ℕ}
    (hdim : topologicalKrullDim S = n + 1) {BS : QDivisor S} {j : T ⟶ S} {BT : QDivisor T}
    (hstep : IsAdjunctionStep sS BS j BT) [IsClosedImmersion j] [IsIntegral T] [IsNormal T]
    [IsLocallyNoetherian T]
    [CompactSpace T] [Smooth (j ≫ sS)] (P : MMP.Mori.PrimeDivisor S)
    (hP : Set.range j.base = (P.support : Set S))
    (hQ : ∀ D : QDivisor S, D.IsQCartier)
    (σ : RationalPluriForms sS (n + 1) 1) (hσ0 : σ ≠ 0) (hσ : P.ordForm σ = -1)
    (ρσ : RationalPluriForms (j ≫ sS) n 1) (hρσ : IsPoincareResidue sS j n 1 σ ρσ) :
    ∃ hgen : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉
        (BS - Finsupp.single P 1).supp,
      (BS - Finsupp.single P 1).IsPullback j hgen BT := by
  obtain ⟨hgenD, hpbD⟩ := hstep.isPullback_divisorOfForm_add_of_isPoincareResidue hdim P hP σ hσ0
    hσ ρσ hρσ (hQ _)
  obtain ⟨R, ⟨hgen', hR⟩, hpbD'⟩ :=
    (isPullback_divisorOfForm_add_of_isPoincareResidue sS hSv hdim j P hP σ hσ0 hσ ρσ hρσ).2.2
      _ BS (hQ _) hgenD rfl
  refine ⟨hgen', ?_⟩
  have h1 := hpbD.pullback_eq (hQ _)
  have h2 := hpbD'.pullback_eq (hQ _)
  have : BT = R := add_left_cancel (h1.symm.trans h2)
  rw [this]; exact hR

private theorem isPullback_sub_single_of_isAdjunctionStep {k : Type} [Field k] [CharZero k]
    {S T : Scheme.{0}} {sS : S ⟶ Spec (.of k)} [IsIntegral S] [IsNormal S]
    [IsLocallyNoetherian S] [CompactSpace S] [LocallyOfFiniteType sS]
    (hSv : AlgebraicGeometry.IsVariety k sS) [Smooth sS] {n : ℕ}
    (hdim : topologicalKrullDim S = n + 1) {BS : QDivisor S} {j : T ⟶ S} {BT : QDivisor T}
    (hstep : IsAdjunctionStep sS BS j BT) [IsClosedImmersion j] [IsIntegral T] [IsNormal T]
    [IsLocallyNoetherian T]
    [CompactSpace T] [Smooth (j ≫ sS)] (P : MMP.Mori.PrimeDivisor S)
    (hP : Set.range j.base = (P.support : Set S)) (hBP : BS.coeff P = 1)
    (hQ : ∀ D : QDivisor S, D.IsQCartier) :
    ∃ hgen : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉
        (BS - Finsupp.single P 1).supp,
      (BS - Finsupp.single P 1).IsPullback j hgen BT := by
  classical
  by_cases hT : Nonempty (MMP.Mori.PrimeDivisor T)
  · obtain ⟨Q⟩ := hT
    obtain ⟨σ, hσ0, hσ, -, ρσ, hρσ, -, -⟩ :=
      exists_form_of_residue_order sS ⟨hSv, inferInstance⟩ hdim j hstep.1 P hP Q
    exact isPullback_sub_single_of_isAdjunctionStep_of_form hSv hdim hstep P hP hQ σ hσ0 hσ ρσ hρσ
  · have hsub : Subsingleton (QDivisor T) := by
      refine ⟨fun a b => Finsupp.ext fun Q => (hT ⟨Q⟩).elim⟩
    have hgen : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉
        (BS - Finsupp.single P 1).supp := by
      intro Z hZ
      obtain ⟨E, hE, hmem⟩ := DivisorWithCoeffs.mem_supp_iff.mp hZ
      have hjT : j (componentGenericPoint T Z) = P.genericPoint := by
        rw [componentGenericPoint_eq_genericPoint]
        have h1 : IsGenericPoint (j (genericPoint T)) (P.support : Set S) := by
          have := (genericPoint_spec T).image j.base.hom.continuous
          rwa [Set.image_univ, j.isClosedEmbedding.isClosed_range.closure_eq, hP] at this
        have h2 : IsGenericPoint P.genericPoint (P.support : Set S) := by
          rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
          exact isGenericPoint_closure
        exact h1.eq h2
      rw [hjT] at hmem
      obtain rfl := MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support hmem
      apply hE
      rw [DivisorWithCoeffs.coeff_sub, hBP]
      change (1 : ℚ) - (Finsupp.single E (1 : ℚ)) E = 0
      rw [Finsupp.single_eq_same, sub_self]
    refine ⟨hgen, fun m hm D hD hDc => ⟨0, Subsingleton.elim _ _, fun U φ hφ E => (hT ⟨E⟩).elim⟩⟩

/-- On an integral scheme, `ord φ⁻¹ = -ord φ` for a nonzero rational function `φ`. -/
private lemma ord_inv_eq_neg {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    {φ : X.functionField} (hφ : φ ≠ 0) (x : X) : X.ord φ⁻¹ x = -X.ord φ x := by
  have h1 := Scheme.ord_mul (x := x) hφ (inv_ne_zero hφ)
  have h2 := Scheme.ord_mul (x := x) (one_ne_zero (α := X.functionField))
    (one_ne_zero (α := X.functionField))
  rw [mul_inv_cancel₀ hφ] at h1
  rw [mul_one] at h2
  omega

/-- On a proper normal integral scheme over an algebraically closed field, a nonzero rational
function with no poles along prime divisors has no zeros either. -/
private theorem ord_eq_zero_of_forall_zero_le_ord {k : Type} [Field k] [IsAlgClosed k]
    {T : Scheme.{0}}
    (sT : T ⟶ Spec (.of k)) [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    [IsProper sT] {φ : T.functionField} (hφ : φ ≠ 0)
    (h : ∀ P : MMP.Mori.PrimeDivisor T, 0 ≤ Scheme.ord φ P.genericPoint)
    (P : MMP.Mori.PrimeDivisor T) : Scheme.ord φ P.genericPoint = 0 := by
  haveI : Nonempty (⊤ : T.Opens) := ⟨⟨genericPoint T, trivial⟩⟩
  obtain ⟨r, hr⟩ := (MMP.Intersection.exists_germToFunctionField_eq_iff_forall_zero_le_ord
    (⊤ : T.Opens) hφ).2 fun P _ => h P
  let f : k →+* Γ(T, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ sT.appTop).hom
  have hfin : f.Finite := by
    have h1 := finite_appTop_of_universallyClosed k sT
    have h2 : ((Scheme.ΓSpecIso (.of k)).inv).hom.Finite :=
      RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (.of k)).inv).2
    exact h1.comp h2
  obtain ⟨c, hc⟩ := (IsAlgClosed.ringHom_bijective_of_isIntegral f hfin.to_isIntegral).2 r
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hφ
    rw [← hr, ← hc, map_zero, map_zero]
  have hinv : ∃ r' : Γ(T, ⊤), T.germToFunctionField ⊤ r' = φ⁻¹ := by
    refine ⟨f c⁻¹, ?_⟩
    rw [← hr, ← hc]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, ← map_mul, inv_mul_cancel₀ hc0, map_one, map_one]
  have h2 := (MMP.Intersection.exists_germToFunctionField_eq_iff_forall_zero_le_ord
    (⊤ : T.Opens) (inv_ne_zero hφ)).1 hinv P
    ⟨P.genericPoint, by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl, trivial⟩
  have h3 := ord_inv_eq_neg hφ P.genericPoint
  have h1 := h P
  omega

end AdjunctionSteps

/-- A scheme smooth over a field is reduced. -/
private lemma isReduced_of_smooth {k : Type} [Field k] {S : Scheme.{0}} (s : S ⟶ Spec (.of k))
    [Smooth s] : IsReduced S := by
  haveI : ∀ x : S, _root_.IsReduced (S.presheaf.stalk x) := fun x => by
    have := isRegularLocalRing_stalk_of_smooth_over_field s x
    have := IsRegularLocalRing.isDomain (S.presheaf.stalk x)
    exact isReduced_of_noZeroDivisors
  exact isReduced_of_isReduced_stalk _

/-- **A reduced closed subscheme on a stratum of an snc divisor.** Let `w` be a point of
codimension `|J|` on the components `J` of an snc divisor `D` of a scheme smooth over a perfect
field, and `ι : S ⟶ M` a reduced closed subscheme with range `closure {w}`. Then `S` is smooth,
its ideal is `∑_{G ∈ J} I_G` along `S`, and `S` lies on every `G ∈ J`. -/
private theorem stratum_package {R : Type*} [Zero R] {k : Type} [Field k] [PerfectField k]
    {M S : Scheme.{0}} (sM : M ⟶ Spec (.of k)) [LocallyOfFiniteType sM] [QuasiCompact sM]
    {D : DivisorWithCoeffs R M} (hD : D.IsSNC sM) {J : Finset (MMP.Mori.PrimeDivisor M)}
    (hJ : J ⊆ D.support) {w : M} (hwJ : ∀ G ∈ J, w ∈ G.support)
    (hc : Order.coheight w = J.card) (ι : S ⟶ M) [IsClosedImmersion ι] [IsReduced S]
    (hι : Set.range ι.base = closure {w}) :
    Smooth (ι ≫ sM) ∧
      (∀ y : S, IdealSheafData.stalk ι.ker (ι y) =
        ⨆ G ∈ J, IdealSheafData.stalk G.idealSheaf (ι y)) ∧
      ∀ y : S, ∀ G ∈ J, ι y ∈ G.support := by
  obtain ⟨hsm, hst⟩ := stratum_closure sM hD hJ hwJ hc
  set V := Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure {w}) with hV
  haveI : LocallyOfFinitePresentation (V.subschemeι ≫ sM) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := V.subschemeι ≫ sM)).mpr
      inferInstance
  haveI hVs : Smooth (V.subschemeι ≫ sM) := (MMP.Mori.isSmoothScheme_iff _).1 hsm
  haveI : IsReduced V.subscheme := isReduced_of_smooth (V.subschemeι ≫ sM)
  have hrV : Set.range V.subschemeι.base = closure {w} := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal,
      TopologicalSpace.Closeds.coe_closure]
  obtain ⟨e, he⟩ := exists_iso_of_range_eq ι V.subschemeι (by
    change Set.range ι.base = Set.range V.subschemeι.base
    rw [hι, hrV])
  have hker : ι.ker = V := by
    rw [← he, Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_subschemeι]
  have hmem : ∀ y : S, ι y ∈ closure {w} := fun y => hι ▸ ⟨y, rfl⟩
  refine ⟨?_, fun y => by rw [hker]; exact hst _ (hmem y), fun y G hG => ?_⟩
  · rw [← he, Category.assoc]; infer_instance
  · exact closure_minimal (Set.singleton_subset_iff.mpr (hwJ G hG))
      G.idealSheaf.support.isClosed (hmem y)

/-- On a stratum `S` cut out by components `J` of an snc divisor,
`codim (ι y) = codim_S y + |J|`. -/
private lemma coheight_map_eq_add_card {R : Type*} [Zero R] {k : Type} [Field k]
    {M S : Scheme.{0}} [IsLocallyNoetherian M] {sM : M ⟶ Spec (.of k)}
    {D : DivisorWithCoeffs R M} (hD : D.IsSNC sM) {J : Finset (MMP.Mori.PrimeDivisor M)}
    (hJ : J ⊆ D.support) (ι : S ⟶ M) [IsClosedImmersion ι] (y : S)
    (hyJ : ∀ G ∈ J, ι y ∈ G.support)
    (hker : IdealSheafData.stalk ι.ker (ι y) =
      ⨆ G ∈ J, IdealSheafData.stalk G.idealSheaf (ι y)) :
    ((Order.coheight y : ℕ∞) : WithBot ℕ∞) + J.card = Order.coheight (ι y) := by
  have h := ringKrullDim_stalk_add_card_eq_coheight hD hJ ι y hyJ hker
  rwa [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight] at h

/-- On a stratum `S` cut out by components `J` of an snc divisor, a point `y` with
`codim_S y ≤ c` lies on at most `c` components of the divisor outside `J`. -/
private lemma card_le_of_stratum {R : Type*} [Zero R] {k : Type} [Field k]
    {M S : Scheme.{0}} [IsLocallyNoetherian M] {sM : M ⟶ Spec (.of k)}
    {D : DivisorWithCoeffs R M} (hD : D.IsSNC sM) {J : Finset (MMP.Mori.PrimeDivisor M)}
    (hJ : J ⊆ D.support) (ι : S ⟶ M) [IsClosedImmersion ι] (y : S)
    (hyJ : ∀ G ∈ J, ι y ∈ G.support)
    (hker : IdealSheafData.stalk ι.ker (ι y) =
      ⨆ G ∈ J, IdealSheafData.stalk G.idealSheaf (ι y)) {c : ℕ}
    (hc : Order.coheight y ≤ c) (T : Finset (MMP.Mori.PrimeDivisor M)) (hT : T ⊆ D.support)
    (hTJ : Disjoint T J) (hTy : ∀ G ∈ T, ι y ∈ G.support) : T.card ≤ c := by
  classical
  have h := coheight_map_eq_add_card hD hJ ι y hyJ hker
  obtain ⟨c', hc', hcard⟩ := card_le_coheight_of_isSNC hD (ι y) (T ∪ J)
    (Finset.union_subset hT hJ) (fun G hG => by
      rcases Finset.mem_union.mp hG with hG | hG
      · exact hTy G hG
      · exact hyJ G hG)
  rw [hc'] at h
  rw [Finset.card_union_of_disjoint hTJ] at hcard
  obtain ⟨a, ha⟩ : ∃ a : ℕ, Order.coheight y = a := by
    refine ⟨(Order.coheight y).toNat, (ENat.coe_toNat ?_).symm⟩
    exact ne_top_of_le_ne_top (ENat.coe_ne_top c) hc
  rw [ha] at h hc
  have h' : a + J.card = c' := by exact_mod_cast h
  have hc'' : a ≤ c := by exact_mod_cast hc
  omega

/-- On a stratum `S` cut out by components `J` of an snc divisor, the generic point of `S` lies on
no component of the divisor outside `J`. -/
private lemma map_notMem_of_coheight_eq_zero {R : Type*} [Zero R] {k : Type} [Field k]
    {M S : Scheme.{0}} [IsLocallyNoetherian M] {sM : M ⟶ Spec (.of k)}
    {D : DivisorWithCoeffs R M} (hD : D.IsSNC sM) {J : Finset (MMP.Mori.PrimeDivisor M)}
    (hJ : J ⊆ D.support) (ι : S ⟶ M) [IsClosedImmersion ι] (y : S)
    (hyJ : ∀ G ∈ J, ι y ∈ G.support)
    (hker : IdealSheafData.stalk ι.ker (ι y) =
      ⨆ G ∈ J, IdealSheafData.stalk G.idealSheaf (ι y))
    (hy : Order.coheight y = 0) (E : MMP.Mori.PrimeDivisor M) (hE : E ∈ D.support)
    (hEJ : E ∉ J) : ι y ∉ E.support := fun hmem => by
  have := card_le_of_stratum hD hJ ι y hyJ hker (c := 0) (by rw [hy]; rfl) {E}
    (Finset.singleton_subset_iff.mpr hE) (Finset.disjoint_singleton_left.mpr hEJ)
    (fun G hG => by rw [Finset.mem_singleton] at hG; subst hG; exact hmem)
  simp at this

/-- On a stratum `S` cut out by components `J` of an snc divisor `D`, a `ℚ`-divisor supported on
`D` with no component in `J` satisfies the condition `(∗)` for pulling back to `S`. -/
private lemma stratum_hgen {R : Type*} [Zero R] {k : Type} [Field k]
    {M S : Scheme.{0}} [IsLocallyNoetherian M] {sM : M ⟶ Spec (.of k)}
    {D : DivisorWithCoeffs R M} (hD : D.IsSNC sM) {J : Finset (MMP.Mori.PrimeDivisor M)}
    (hJ : J ⊆ D.support) (ι : S ⟶ M) [IsClosedImmersion ι] [IsIntegral S]
    (hyJ : ∀ y : S, ∀ G ∈ J, ι y ∈ G.support)
    (hker : ∀ y : S, IdealSheafData.stalk ι.ker (ι y) =
      ⨆ G ∈ J, IdealSheafData.stalk G.idealSheaf (ι y))
    (A : QDivisor M) (hAD : A.support ⊆ D.support) (hAJ : ∀ G ∈ J, A.coeff G = 0) :
    ∀ W : irreducibleComponents S, ι (componentGenericPoint S W) ∉ A.supp := by
  intro W hW
  rw [componentGenericPoint_eq_genericPoint] at hW
  obtain ⟨E, hE, hmem⟩ := DivisorWithCoeffs.mem_supp_iff.mp hW
  have hEs : E ∈ A.support := Finsupp.mem_support_iff.mpr hE
  have h0 : Order.coheight (genericPoint S) = 0 :=
    Order.coheight_eq_zero.mpr fun b _ => Scheme.le_iff_specializes.mpr (genericPoint_specializes b)
  exact map_notMem_of_coheight_eq_zero hD hJ ι _ (hyJ _) (hker _) h0 E (hAD hEs)
    (fun hEJ => hE (hAJ E hEJ)) hmem

open scoped Classical in
/-- **Coefficients of the pull-back to a stratum.** On a smooth `M` with an snc divisor `D`, let
`S` be a smooth stratum cut out by components `J` of `D`. For a `ℚ`-divisor `A` supported on `D`
with no component in `J`, the coefficient of `A|_S` at a prime `Q` of `S` is the sum of the
coefficients of the components of `A` through `ι(η_Q)`. -/
private theorem coeff_isPullback_of_stratum {R : Type*} [Zero R] {k : Type} [Field k]
    {M S : Scheme.{0}} (sM : M ⟶ Spec (.of k)) [IsIntegral M] [IsLocallyNoetherian M] [IsNormal M]
    [Smooth sM] {D : DivisorWithCoeffs R M} (hD : D.IsSNC sM)
    {J : Finset (MMP.Mori.PrimeDivisor M)} (hJ : J ⊆ D.support) (ι : S ⟶ M) [IsClosedImmersion ι]
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S] [Smooth (ι ≫ sM)]
    (hyJ : ∀ y : S, ∀ G ∈ J, ι y ∈ G.support)
    (hker : ∀ y : S, IdealSheafData.stalk ι.ker (ι y) =
      ⨆ G ∈ J, IdealSheafData.stalk G.idealSheaf (ι y))
    (A : QDivisor M) (hAD : A.support ⊆ D.support) (hAJ : ∀ G ∈ J, A.coeff G = 0)
    (hQ : A.IsQCartier)
    {hgen : ∀ W : irreducibleComponents S, ι (componentGenericPoint S W) ∉ A.supp}
    {A' : QDivisor S} (hA : A.IsPullback ι hgen A') (Q : MMP.Mori.PrimeDivisor S) :
    A'.coeff Q = ∑ E ∈ A.support.filter (fun E => ι Q.genericPoint ∈ E.support), A.coeff E := by
  haveI : AlgebraicGeometry.IsNoetherian S := ⟨⟩
  obtain ⟨m, hm, Dm, hDm, hDmc⟩ := hQ.exists_pos
  obtain ⟨D', hD', hpb⟩ := hA m hm Dm hDm hDmc
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hgenD : ∀ Z : irreducibleComponents S, ι (componentGenericPoint S Z) ∉ Dm.supp :=
    fun Z hZ => hgen Z (by rwa [QDivisor.supp_eq_of_toQDivisor_eq hm' hDm] at hZ)
  have hres := divisor_isPullback_restrict sM ι Dm hgenD
  have hDD : D' = Dm.restrict ι := hpb.eq hDmc hres
  have hDcoeff : ∀ E, (Dm.coeff E : ℚ) = m * A.coeff E := by
    intro E
    have := congrArg (fun G : QDivisor M => G.coeff E) hDm
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at this
    push_cast at this
    exact this
  have hsupp : Dm.support = A.support := by
    ext E
    rw [Finsupp.mem_support_iff, Finsupp.mem_support_iff]
    change Dm.coeff E ≠ 0 ↔ A.coeff E ≠ 0
    constructor
    · intro h h0; apply h
      have := hDcoeff E; rw [h0, mul_zero] at this; exact_mod_cast this
    · intro h h0; apply h
      have := hDcoeff E; rw [h0, Int.cast_zero] at this
      exact (mul_eq_zero.mp this.symm).resolve_left hmq
  have hDJ : ∀ G ∈ J, Dm.coeff G = 0 := fun G hG => by
    have := hDcoeff G; rw [hAJ G hG, mul_zero] at this; exact_mod_cast this
  have hD0 : ∀ E ∈ Dm.support, ∀ s : S, Order.coheight s = 0 → ι s ∉ E.support := by
    intro E hE s hs
    rw [hsupp] at hE
    exact map_notMem_of_coheight_eq_zero hD hJ ι s (hyJ s) (hker s) hs E (hAD hE)
      (fun hEJ => (Finsupp.mem_support_iff.mp hE) (hAJ E hEJ))
  have hsum := coeff_restrict_eq_sum hD hJ ι Q (hyJ _) (hker _) Dm (hsupp ▸ hAD) hDJ
    (DivisorWithCoeffs.finite_support_restrictCoeff ι Dm hD0)
  rw [← hDD, hsupp] at hsum
  have hBQ : (m : ℚ) * A'.coeff Q = D'.coeff Q := by
    have := congrArg (fun G : QDivisor S => G.coeff Q) hD'
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at this
    exact this.symm
  apply mul_left_cancel₀ hmq
  rw [hBQ, hsum]
  push_cast
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun E _ => hDcoeff E

/-- A regular system of parameters is carried to one by a ring isomorphism. -/
private lemma isRegularSystemOfParameters_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) {n : ℕ} {z : Fin n → A}
    (hz : MMP.Mori.IsRegularSystemOfParameters z) :
    MMP.Mori.IsRegularSystemOfParameters (e ∘ z) := by
  refine ⟨?_, (ringKrullDim_eq_of_ringEquiv e).symm.trans hz.2⟩
  have h := Ideal.map_span (e : A →+* B) (Set.range z)
  rw [hz.1, IsLocalRing.map_maximalIdeal_of_surjective (e : A →+* B) e.surjective] at h
  rw [Set.range_comp]
  exact h.symm

/-- **Coordinates on a stratum.** At a point `y` of a stratum `S` cut out by components `J` of an
snc divisor, the restriction of the local equation `π` of a further component `E ∋ ι y` is a member
of a regular system of parameters of `𝒪_{S,y}`. -/
private theorem exists_isRegularSystemOfParameters_stalk_stratum {R : Type*} [Zero R] {k : Type}
    [Field k] {M S : Scheme.{0}} [IsLocallyNoetherian M] {sM : M ⟶ Spec (.of k)}
    {D : DivisorWithCoeffs R M} (hD : D.IsSNC sM) {J : Finset (MMP.Mori.PrimeDivisor M)}
    (hJ : J ⊆ D.support) (ι : S ⟶ M) [IsClosedImmersion ι] (y : S)
    (hyJ : ∀ G ∈ J, ι y ∈ G.support)
    (hker : IdealSheafData.stalk ι.ker (ι y) =
      ⨆ G ∈ J, IdealSheafData.stalk G.idealSheaf (ι y))
    {E : MMP.Mori.PrimeDivisor M} (hED : E ∈ D.support) (hEJ : E ∉ J) (hyE : ι y ∈ E.support) :
    ∃ (m : ℕ) (w : Fin m → S.presheaf.stalk y) (j0 : Fin m) (π : M.presheaf.stalk (ι y)),
      MMP.Mori.IsRegularSystemOfParameters w ∧
        IdealSheafData.stalk E.idealSheaf (ι y) = Ideal.span {π} ∧
        w j0 = (ι.stalkMap y).hom π := by
  classical
  obtain ⟨N, z, j, hz, hj, hI⟩ := hD.2 (ι y)
  haveI := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz
  let jJ : J → Fin N := fun G => j ⟨G.1, hJ G.2, hyJ G.1 G.2⟩
  set J' : Finset (Fin N) := Finset.univ.image jJ with hJ'
  have hst : IdealSheafData.stalk ι.ker (ι y) = Ideal.span (z '' (J' : Set (Fin N))) := by
    rw [hker]
    exact iSup_stalk_idealSheaf_eq_span z j hI fun G hG => ⟨hJ hG, hyJ G hG⟩
  set iE := j ⟨E, hED, hyE⟩ with hiE
  have hiEJ : iE ∉ J' := by
    intro h
    obtain ⟨G, -, hG⟩ := Finset.mem_image.mp h
    have := congrArg Subtype.val (hj hG)
    simp only at this
    exact hEJ (this ▸ G.2)
  have hcard : Fintype.card (Fin (N - J'.card)) = Fintype.card (J'ᶜ : Finset (Fin N)) := by
    simp [Finset.card_compl]
  let e : Fin (N - J'.card) ≃ (J'ᶜ : Finset (Fin N)) := Fintype.equivOfCardEq hcard
  haveI := (MMP.Resolution.isRegularLocalRing_quotient_span_image z hz J').toIsLocalRing
  have hw0 := isRegularSystemOfParameters_quotient z hz J' e
  have hmemc : iE ∈ (J'ᶜ : Finset (Fin N)) := Finset.mem_compl.mpr hiEJ
  obtain ⟨φ, hφ⟩ : ∃ φ : (M.presheaf.stalk (ι y) ⧸ Ideal.span (z '' (J' : Set (Fin N)))) ≃+*
      S.presheaf.stalk y, φ = (Ideal.quotEquivOfEq hst.symm).trans (stalkEquivQuotient ι y) :=
    ⟨_, rfl⟩
  have hw0' : MMP.Mori.IsRegularSystemOfParameters
      (fun i => Ideal.Quotient.mk (Ideal.span (z '' (J' : Set (Fin N)))) (z (e i))) := hw0
  have hw : MMP.Mori.IsRegularSystemOfParameters
      (φ ∘ fun i => Ideal.Quotient.mk (Ideal.span (z '' (J' : Set (Fin N)))) (z (e i))) :=
    isRegularSystemOfParameters_ringEquiv φ hw0'
  refine ⟨N - J'.card, _, e.symm ⟨iE, hmemc⟩, z iE, hw, hI ⟨E, hED, hyE⟩, ?_⟩
  show φ (Ideal.Quotient.mk _ (z (e (e.symm ⟨iE, hmemc⟩)))) = _
  rw [Equiv.apply_symm_apply, hφ, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    stalkEquivQuotient_mk]

/-- **Components of a divisor on a stratum are disjoint.** On a stratum `S` cut out by components
`J` of an snc divisor, two prime divisors of `S` both lying on a further component `E` of the snc
divisor and meeting each other are equal: at a common point, both have the ideal generated by the
restriction of the local equation of `E`. -/
private theorem eq_of_mem_support_of_stratum {R : Type*} [Zero R] {k : Type}
    [Field k] {M S : Scheme.{0}} [IsLocallyNoetherian M] [IsLocallyNoetherian S]
    {sM : M ⟶ Spec (.of k)} {D : DivisorWithCoeffs R M} (hD : D.IsSNC sM)
    {J : Finset (MMP.Mori.PrimeDivisor M)} (hJ : J ⊆ D.support) (ι : S ⟶ M) [IsClosedImmersion ι]
    (hyJ : ∀ y : S, ∀ G ∈ J, ι y ∈ G.support)
    (hker : ∀ y : S, IdealSheafData.stalk ι.ker (ι y) =
      ⨆ G ∈ J, IdealSheafData.stalk G.idealSheaf (ι y))
    {E : MMP.Mori.PrimeDivisor M} (hED : E ∈ D.support) (hEJ : E ∉ J)
    {Q₁ Q₂ : MMP.Mori.PrimeDivisor S} (h₁ : ι Q₁.genericPoint ∈ E.support)
    (h₂ : ι Q₂.genericPoint ∈ E.support) {y : S} (hy₁ : y ∈ Q₁.support) (hy₂ : y ∈ Q₂.support) :
    Q₁ = Q₂ := by
  have hsp : Q₁.genericPoint ⤳ y := by
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hy₁
  have hyE : ι y ∈ E.support :=
    (ι.base.hom.map_specializes hsp).mem_closed E.idealSheaf.support.isClosed h₁
  obtain ⟨m, w, j0, π, hw, hπ, hwj⟩ :=
    exists_isRegularSystemOfParameters_stalk_stratum hD hJ ι y (hyJ y) (hker y) hED hEJ hyE
  have hst : ∀ Q : MMP.Mori.PrimeDivisor S, ι Q.genericPoint ∈ E.support → y ∈ Q.support →
      IdealSheafData.stalk Q.idealSheaf y = Ideal.span {w j0} := fun Q hQ hyQ => by
    refine stalk_idealSheaf_eq_span_of_mem Q hyQ hw j0 ?_
    rw [hwj]
    exact stalkMap_mem_stalk_idealSheaf ι Q E hQ y hπ
  obtain ⟨q₁, hq₁, hs₁, -⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support Q₁ hy₁
  obtain ⟨q₂, hq₂, hs₂, -⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support Q₂ hy₂
  have hq : q₁ = q₂ := PrimeSpectrum.ext (by rw [← hs₁, ← hs₂, hst Q₁ h₁ hy₁, hst Q₂ h₂ hy₂])
  refine AlgebraicGeometry.PrimeDivisor.genericPoint_injective ?_
  change Q₁.genericPoint = Q₂.genericPoint
  rw [← hq₁, ← hq₂, hq]

/-- A reduced closed subscheme with irreducible range is integral. -/
private lemma isIntegral_of_isIrreducible_range {A P : Scheme.{0}} (ι : A ⟶ P)
    [IsClosedImmersion ι] [IsReduced A] (hirr : IsIrreducible (Set.range ι.base)) :
    IsIntegral A := by
  haveI : IrreducibleSpace (Set.range ι.base) := Subtype.irreducibleSpace hirr
  haveI : IrreducibleSpace A := (ι.isEmbedding.toHomeomorph).symm.surjective.irreducibleSpace
    (ι.isEmbedding.toHomeomorph).symm.continuous
  exact isIntegral_of_irreducibleSpace_of_isReduced A

section PullbackAlgebra

open MMP.Mori

universe u

/-- Pull-back of divisors is functorial for composites. -/
private theorem divisor_isPullback_comp {X Y Z : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsLocallyNoetherian Z] [IsNormal Z]
    {f : Y ⟶ Z} {g : X ⟶ Y} {B : Divisor Z} (hBc : B.IsCartier)
    {hB : ∀ W : irreducibleComponents Y, f (componentGenericPoint Y W) ∉ B.supp}
    {B' : Divisor Y} (h₁ : B.IsPullback f hB B')
    {hB' : ∀ W : irreducibleComponents X, g (componentGenericPoint X W) ∉ B'.supp}
    {B'' : Divisor X} (h₂ : B'.IsPullback g hB' B'')
    (hB'' : ∀ W : irreducibleComponents X, (g ≫ f) (componentGenericPoint X W) ∉ B.supp) :
    B.IsPullback (g ≫ f) hB'' B'' := by
  classical
  refine Divisor.IsPullback.of_forall_exists fun E => ?_
  obtain ⟨U, hU, φ, hφ⟩ := hBc ((g ≫ f) E.genericPoint)
  let ψ : (RationalFunctions Y)ˣ := (RationalFunctions.unitsEquiv Y).symm fun W =>
    if hW : f (componentGenericPoint Y W) ∈ U then pullbackComponent f hB hφ W hW else 1
  have hψW : ∀ (W : irreducibleComponents Y) (hW : f (componentGenericPoint Y W) ∈ U),
      Units.map (RationalFunctions.component Y W).toMonoidHom ψ =
        pullbackComponent f hB hφ W hW := by
    intro W hW
    ext
    change (if hW : f (componentGenericPoint Y W) ∈ U then
      pullbackComponent f hB hφ W hW else 1).val = _
    rw [dif_pos hW]
  have hψ : B'.IsLocalEquation (f ⁻¹ᵁ U) ψ := by
    intro E' hE'
    rw [h₁ U φ hφ E' hE', PrimeDivisor.ord_eq_ordUnit, hψW]
  have hE : (E.support ∩ (g ≫ f) ⁻¹ᵁ U).Nonempty := (E.genericPoint_mem_iff _).mp hU
  have hE' : (E.support ∩ g ⁻¹ᵁ (f ⁻¹ᵁ U)).Nonempty := hE
  refine ⟨U, φ, hφ, hE, ?_⟩
  rw [h₂ (f ⁻¹ᵁ U) ψ hψ E hE']
  congr 1
  -- the two pulled-back components agree
  set η := componentGenericPoint X E.component
  have hzU : f (g η) ∈ U := E.map_componentGenericPoint_mem (g ≫ f) hE
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hzU (hB'' E.component) (mem_pointComponent _)
  rw [pullbackComponent_eq hB'' hφ _ (mem_pointComponent _) a ha]
  set W' := pointComponent (g η)
  have hsp : componentGenericPoint Y W' ⤳ g η :=
    (isGenericPoint_componentGenericPoint Y W').specializes (mem_pointComponent _)
  have hsp' : f (componentGenericPoint Y W') ⤳ f (g η) := f.base.hom.map_specializes hsp
  have hW'U : f (componentGenericPoint Y W') ∈ U := hsp'.mem_open U.isOpen hzU
  have hzW'' : f (g η) ∈ (pointComponent (f (componentGenericPoint Y W'))).1 :=
    hsp'.mem_closed (isClosed_of_mem_irreducibleComponents _
      (pointComponent (f (componentGenericPoint Y W'))).2) (mem_pointComponent _)
  have hWW : pointComponent (f (componentGenericPoint Y W')) = pointComponent (f (g η)) :=
    eq_of_mem_irreducibleComponents hzW'' (mem_pointComponent _)
  have hmem : f (componentGenericPoint Y W') ∈ (pointComponent (f (g η))).1 :=
    hWW ▸ mem_pointComponent _
  let a' : (Z.presheaf.stalk (f (componentGenericPoint Y W')))ˣ :=
    Units.map (Z.presheaf.stalkSpecializes hsp').hom.toMonoidHom a
  have ha' : (stalkToRationalFunctions Z hmem).hom a' =
      (φ : RationalFunctions Z) (pointComponent (f (g η))) := by
    rw [← ha]
    change (Z.presheaf.stalkSpecializes hsp' ≫ Z.presheaf.stalkSpecializes _).hom a.val =
      (Z.presheaf.stalkSpecializes _).hom a.val
    rw [TopCat.Presheaf.stalkSpecializes_comp]
  let b : (Y.presheaf.stalk (g η))ˣ := Units.map (f.stalkMap (g η)).hom.toMonoidHom a
  have hb : (stalkToRationalFunctions Y (mem_pointComponent (g η))).hom b =
      (ψ : RationalFunctions Y) W' := by
    have h1 := congrArg Units.val (hψW W' hW'U)
    change _ = (Units.map (RationalFunctions.component Y W').toMonoidHom ψ).val
    rw [h1, pullbackComponent_eq hB hφ hW'U hmem a' ha']
    change (Y.presheaf.stalkSpecializes hsp).hom ((f.stalkMap (g η)).hom a.val) =
      (f.stalkMap _).hom ((Z.presheaf.stalkSpecializes hsp').hom a.val)
    rw [Scheme.Hom.stalkSpecializes_stalkMap_apply]
  rw [pullbackComponent_eq hB' hψ _ (mem_pointComponent _) b hb]
  ext
  change (g.stalkMap η).hom ((f.stalkMap (g η)).hom a.val) = ((g ≫ f).stalkMap η).hom a.val
  rw [Scheme.Hom.stalkMap_comp]
  rfl

/-- The pull-back along `f` of the `ℚ`-pull-back along `g` is the `ℚ`-pull-back along `g ≫ f`. -/
private theorem qdivisor_isPullback_comp {X Y Z : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsLocallyNoetherian Z] [IsNormal Z]
    {f : Y ⟶ Z} {g : X ⟶ Y} {D : QDivisor Z}
    {hD : ∀ W : irreducibleComponents Y, f (componentGenericPoint Y W) ∉ D.supp}
    {D₁ : QDivisor Y} (h₁ : D.IsPullback f hD D₁)
    {hD₁ : ∀ W : irreducibleComponents X, g (componentGenericPoint X W) ∉ D₁.supp}
    {D₂ : QDivisor X} (h₂ : D₁.IsPullback g hD₁ D₂)
    (hD₂ : ∀ W : irreducibleComponents X, (g ≫ f) (componentGenericPoint X W) ∉ D.supp) :
    D.IsPullback (g ≫ f) hD₂ D₂ := by
  intro m hm E hE hEc
  obtain ⟨E', hE', hp⟩ := h₁ m hm E hE hEc
  obtain ⟨E'', hE'', hp'⟩ := h₂ m hm E' hE' (hp.isCartier hEc)
  exact ⟨E'', hE'', divisor_isPullback_comp hEc hp hp' _⟩

/-- A prime divisor whose generic point maps off the support of a Cartier divisor has
coefficient zero in its pull-back. -/
private theorem divisor_coeff_eq_zero_of_isPullback {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} {B : Divisor Y}
    (hBc : B.IsCartier) {hB : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ B.supp}
    {B' : Divisor X} (h : B.IsPullback f hB B') (E : MMP.Mori.PrimeDivisor X)
    (hE : f E.genericPoint ∉ B.supp) : B'.coeff E = 0 := by
  obtain ⟨U, hU, φ, hφ⟩ := hBc (f E.genericPoint)
  have hEU : (E.support ∩ f ⁻¹ᵁ U).Nonempty := (E.genericPoint_mem_iff _).mp hU
  rw [h U φ hφ E hEU]
  have hsp : componentGenericPoint X E.component ⤳ E.genericPoint := E.specializes_genericPoint
  have hsp' : f (componentGenericPoint X E.component) ⤳ f E.genericPoint :=
    f.base.hom.map_specializes hsp
  set W := pointComponent (f (componentGenericPoint X E.component))
  have hW : f (componentGenericPoint X E.component) ∈ W.1 := mem_pointComponent _
  have hyW : f E.genericPoint ∈ W.1 :=
    hsp'.mem_closed (isClosed_of_mem_irreducibleComponents _ W.2) hW
  obtain ⟨c, hc⟩ := hφ.exists_unit_stalk hU hE hyW
  let c' : (Y.presheaf.stalk (f (componentGenericPoint X E.component)))ˣ :=
    Units.map (Y.presheaf.stalkSpecializes hsp').hom.toMonoidHom c
  have hc' : (stalkToRationalFunctions Y hW).hom c' = (φ : RationalFunctions Y) W := by
    rw [← hc]
    change (Y.presheaf.stalkSpecializes hsp' ≫ Y.presheaf.stalkSpecializes _).hom c.val =
      (Y.presheaf.stalkSpecializes _).hom c.val
    rw [TopCat.Presheaf.stalkSpecializes_comp]
  rw [pullbackComponent_eq hB hφ _ hW c' hc']
  refine E.ordUnit_eq_zero_of_isUnit ((c.isUnit).map (f.stalkMap E.genericPoint).hom) ?_
  change (X.presheaf.stalkSpecializes _).hom ((f.stalkMap E.genericPoint).hom
    c.val) = (f.stalkMap _).hom ((Y.presheaf.stalkSpecializes hsp').hom c.val)
  rw [Scheme.Hom.stalkSpecializes_stalkMap_apply]

/-- The same for `ℚ`-divisors. -/
private theorem qdivisor_coeff_eq_zero_of_isPullback {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} {B : QDivisor Y}
    (hBq : B.IsQCartier)
    {hB : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ B.supp}
    {B' : QDivisor X} (h : B.IsPullback f hB B') (E : MMP.Mori.PrimeDivisor X)
    (hE : f E.genericPoint ∉ B.supp) : B'.coeff E = 0 := by
  obtain ⟨m, hm, D, hD, hDc⟩ := hBq.exists_pos
  obtain ⟨D', hD', hp⟩ := h m hm D hD hDc
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have h0 := divisor_coeff_eq_zero_of_isPullback hDc hp E (by
    rwa [QDivisor.supp_eq_of_toQDivisor_eq hm' hD])
  have := congrArg (fun G : QDivisor X => G.coeff E) hD'
  simp only [Divisor.coeff_toQDivisor, h0, DivisorWithCoeffs.coeff_smul, Int.cast_zero] at this
  rcases smul_eq_zero.mp this.symm with h | h
  · exact absurd h hm'
  · exact h

/-- `f^*(-B) = -f^*B` for a `ℚ`-Cartier `ℚ`-divisor `B`. -/
private theorem qdivisor_isPullback_neg {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} {B : QDivisor Y}
    {hB : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ B.supp}
    {B' : QDivisor X} (h : B.IsPullback f hB B')
    (hB' : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ (-B).supp) :
    (-B).IsPullback f hB' (-B') := by
  intro m hm D hD hDc
  have hD' : Divisor.toQDivisor (-D) = (m : ℤ) • B := by rw [map_neg, hD, smul_neg, neg_neg]
  obtain ⟨E, hE, hp⟩ := h m hm (-D) hD' (by simpa using hDc.zsmul (-1))
  refine ⟨-E, by rw [map_neg, hE, smul_neg], ?_⟩
  have := hp.zsmul (by simpa using hDc.zsmul (-1)) (-1) (by
    intro W hW
    refine hB' W ?_
    rwa [show (-1 : ℤ) • -D = D by simp,
      QDivisor.supp_eq_of_toQDivisor_eq (by exact_mod_cast hm.ne') hD] at hW)
  simpa using this

/-- `Supp (-B) = Supp B`. -/
private lemma supp_neg_qdivisor {Y : Scheme.{u}} (B : QDivisor Y) : (-B).supp = B.supp := by
  ext y
  simp only [SetLike.mem_coe, DivisorWithCoeffs.mem_supp_iff, DivisorWithCoeffs.coeff_neg, ne_eq,
    neg_eq_zero]

/-- The pull-back predicate only depends on the `ℚ`-divisor, not on the proof of `(∗)`. -/
private lemma qdivisor_isPullback_congr {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} {B₁ B₂ : QDivisor Y} (h : B₁ = B₂)
    {hB₁ : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ B₁.supp}
    {hB₂ : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ B₂.supp}
    {B' : QDivisor X} (hp : B₁.IsPullback f hB₁ B') : B₂.IsPullback f hB₂ B' := by
  subst h
  exact hp

/-- `f^*(B₁ - B₂) = f^*B₁ - f^*B₂`. -/
private theorem qdivisor_isPullback_sub {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y}
    (hQ : ∀ A : QDivisor Y, A.IsQCartier) {G₁ G₂ : QDivisor Y}
    {h₁ : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ G₁.supp}
    {h₂ : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ G₂.supp}
    {R₁ R₂ : QDivisor X} (p₁ : G₁.IsPullback f h₁ R₁) (p₂ : G₂.IsPullback f h₂ R₂)
    (h : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ (G₁ - G₂).supp) :
    (G₁ - G₂).IsPullback f h (R₁ - R₂) := by
  have hn := qdivisor_isPullback_neg p₂ (fun W => by rw [supp_neg_qdivisor]; exact h₂ W)
  have hadd := qdivisor_isPullback_add (hQ _) (hQ _) p₁ hn (fun W => by
    rw [← sub_eq_add_neg]; exact h W)
  have := qdivisor_isPullback_congr (sub_eq_add_neg G₁ G₂).symm (hB₂ := h) hadd
  rwa [← sub_eq_add_neg] at this

/-- A `ℚ`-Cartier `ℚ`-divisor whose support contains the image of no point of codimension one
of `X` pulls back to zero. -/
private theorem qdivisor_isPullback_zero_of_forall {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y}
    {B : QDivisor Y} (hBq : B.IsQCartier)
    (hB : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ B.supp)
    (h : ∀ E : MMP.Mori.PrimeDivisor X, f E.genericPoint ∉ B.supp) : B.IsPullback f hB 0 := by
  have hp := QDivisor.isPullback_pullback hBq hB
  have h0 : B.pullback hBq hB = 0 := by
    ext E
    exact qdivisor_coeff_eq_zero_of_isPullback hBq hp E (h E)
  rwa [h0] at hp

/-- The pull-back predicate only depends on the morphism, not on the proof of `(∗)`. -/
private lemma qdivisor_isPullback_morphism_congr {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] {f f' : X ⟶ Y} (e : f = f')
    {B : QDivisor Y} {hB : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ B.supp}
    {hB' : ∀ W : irreducibleComponents X, f' (componentGenericPoint X W) ∉ B.supp}
    {B' : QDivisor X} (hp : B.IsPullback f hB B') : B.IsPullback f' hB' B' := by
  subst e
  exact hp

end PullbackAlgebra

section StratumChain

open MMP.Mori

/-- The generic point of a closed integral subscheme onto a prime divisor is the generic point
of the divisor. -/
private lemma map_genericPoint_eq_of_range {S T : Scheme.{0}} [IsIntegral T] (j : T ⟶ S)
    [IsClosedImmersion j] (P : MMP.Mori.PrimeDivisor S)
    (hP : Set.range j.base = (P.support : Set S)) : j (genericPoint T) = P.genericPoint := by
  have h1 : IsGenericPoint (j (genericPoint T)) (P.support : Set S) := by
    have := (genericPoint_spec T).image j.base.hom.continuous
    rwa [Set.image_univ, j.isClosedEmbedding.isClosed_range.closure_eq, hP] at this
  have h2 : IsGenericPoint P.genericPoint (P.support : Set S) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isGenericPoint_closure
  exact h1.eq h2

open scoped Classical in
/-- **One step down a chain of strata.** Let `S` be a smooth stratum of an snc divisor `D` on a
smooth `M`, cut out by `J`, let `E ∉ J` be a further component of `D` and `T ⊂ S` a closed
integral subscheme onto a prime divisor `P` of `S` lying on `E`. For a `ℚ`-divisor `A`
supported on `D` with no component in `J`, if `R = (A|_S - P)|_T` then `R = (A - E)|_T`: the
restriction `E|_S` is `P` plus components of `S ∩ E` disjoint from `P`. -/
private theorem isPullback_sub_single_comp_of_stratum {R : Type*} [Zero R] {k : Type} [Field k]
    {M S T : Scheme.{0}} (sM : M ⟶ Spec (.of k)) [IsIntegral M] [IsLocallyNoetherian M]
    [IsNormal M] [Smooth sM] {D : DivisorWithCoeffs R M} (hD : D.IsSNC sM)
    {J : Finset (MMP.Mori.PrimeDivisor M)} (hJ : J ⊆ D.support) (ι : S ⟶ M) [IsClosedImmersion ι]
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S] [Smooth (ι ≫ sM)]
    (hyJ : ∀ y : S, ∀ G ∈ J, ι y ∈ G.support)
    (hker : ∀ y : S, IdealSheafData.stalk ι.ker (ι y) =
      ⨆ G ∈ J, IdealSheafData.stalk G.idealSheaf (ι y))
    (hQM : ∀ A : QDivisor M, A.IsQCartier) (hQS : ∀ A : QDivisor S, A.IsQCartier)
    (j : T ⟶ S) [IsClosedImmersion j] [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    [CompactSpace T] (P : MMP.Mori.PrimeDivisor S) (hP : Set.range j.base = (P.support : Set S))
    {E : MMP.Mori.PrimeDivisor M} (hED : E ∈ D.support) (hEJ : E ∉ J)
    (hPE : ι P.genericPoint ∈ E.support)
    (A : QDivisor M) (hAD : A.support ⊆ D.support) (hAJ : ∀ G ∈ J, A.coeff G = 0)
    {hgenA : ∀ W : irreducibleComponents S, ι (componentGenericPoint S W) ∉ A.supp}
    {AS : QDivisor S} (hAS : A.IsPullback ι hgenA AS)
    {hgen1 : ∀ W : irreducibleComponents T, j (componentGenericPoint T W) ∉
      (AS - Finsupp.single P 1).supp}
    {RT : QDivisor T} (hR : (AS - Finsupp.single P 1).IsPullback j hgen1 RT)
    (hgen2 : ∀ W : irreducibleComponents T, (j ≫ ι) (componentGenericPoint T W) ∉
      (A - Finsupp.single E 1).supp) :
    (A - Finsupp.single E 1).IsPullback (j ≫ ι) hgen2 RT := by
  have hjT : j (genericPoint T) = P.genericPoint := map_genericPoint_eq_of_range j P hP
  have hcgp : ∀ W : irreducibleComponents T, componentGenericPoint T W = genericPoint T :=
    fun W => componentGenericPoint_eq_genericPoint _
  -- `A(E) = 1`
  have hAE : A.coeff E = 1 := by
    by_contra hne
    apply hgen2 (MMP.Mori.pointComponent (genericPoint T))
    rw [hcgp, Scheme.Hom.comp_apply, hjT]
    refine DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, ?_, hPE⟩
    rw [DivisorWithCoeffs.coeff_sub]
    change A.coeff E - (Finsupp.single E (1 : ℚ)) E ≠ 0
    rw [Finsupp.single_eq_same]
    exact sub_ne_zero.mpr hne
  -- `E|_S`
  set E1 : QDivisor M := Finsupp.single E 1 with hE1
  have hE1s : E1.support = {E} := Finsupp.support_single_ne_zero _ one_ne_zero
  have hE1D : E1.support ⊆ D.support := by rw [hE1s]; exact Finset.singleton_subset_iff.mpr hED
  have hE1J : ∀ G ∈ J, E1.coeff G = 0 := fun G hG => by
    change (Finsupp.single E (1 : ℚ)) G = 0
    rw [Finsupp.single_apply, if_neg (fun h : E = G => hEJ (h ▸ hG))]
  have hgenE := stratum_hgen hD hJ ι hyJ hker E1 hE1D hE1J
  have hES := QDivisor.isPullback_pullback (hQM E1) hgenE
  set ES := E1.pullback (hQM E1) hgenE with hESdef
  have hEScoeff : ∀ Q : MMP.Mori.PrimeDivisor S,
      ES.coeff Q = if ι Q.genericPoint ∈ E.support then 1 else 0 := by
    intro Q
    rw [coeff_isPullback_of_stratum sM hD hJ ι hyJ hker E1 hE1D hE1J (hQM E1) hES Q, hE1s,
      Finset.filter_singleton]
    split_ifs with h
    · rw [Finset.sum_singleton]
      change (Finsupp.single E (1 : ℚ)) E = 1
      exact Finsupp.single_eq_same
    · rfl
  -- `A|_S(P) = 1`
  have hASP : AS.coeff P = 1 := by
    rw [coeff_isPullback_of_stratum sM hD hJ ι hyJ hker A hAD hAJ (hQM A) hAS P]
    have hfil : A.support.filter (fun E' => ι P.genericPoint ∈ E'.support) = {E} := by
      ext E'
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hE', hPE'⟩
        by_contra hne
        have hE'J : E' ∉ J := fun h => (Finsupp.mem_support_iff.mp hE') (hAJ E' h)
        have := card_le_of_stratum hD hJ ι P.genericPoint (hyJ _) (hker _) (c := 1)
          (by rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]; rfl) {E', E}
          (Finset.insert_subset (hAD hE') (Finset.singleton_subset_iff.mpr hED))
          (Finset.disjoint_left.mpr fun G hG hGJ => by
            rcases Finset.mem_insert.mp hG with rfl | hG
            · exact hE'J hGJ
            · rw [Finset.mem_singleton] at hG; subst hG; exact hEJ hGJ)
          (fun G hG => by
            rcases Finset.mem_insert.mp hG with rfl | hG
            · exact hPE'
            · rw [Finset.mem_singleton] at hG; subst hG; exact hPE)
        rw [Finset.card_pair hne] at this
        omega
      · rintro rfl
        exact ⟨Finsupp.mem_support_iff.mpr (by change A.coeff E' ≠ 0; rw [hAE]; norm_num), hPE⟩
    rw [hfil, Finset.sum_singleton, hAE]
  -- `(A - E)|_S = A|_S - E|_S`
  have hsubD : (A - E1).support ⊆ D.support := fun G hG =>
    (Finset.union_subset hAD hE1D) (Finsupp.support_sub hG)
  have hsubJ : ∀ G ∈ J, (A - E1).coeff G = 0 := fun G hG => by
    rw [DivisorWithCoeffs.coeff_sub, hAJ G hG, hE1J G hG, sub_zero]
  have hgenSub := stratum_hgen hD hJ ι hyJ hker (A - E1) hsubD hsubJ
  have hSub : (A - E1).IsPullback ι hgenSub (AS - ES) :=
    qdivisor_isPullback_sub hQM hAS hES hgenSub
  -- `R' = E|_S - P` pulls back to zero on `T`
  set R' : QDivisor S := ES - Finsupp.single P 1 with hR'
  have hR'coeff : ∀ Q, R'.coeff Q ≠ 0 → Q ≠ P ∧ ι Q.genericPoint ∈ E.support := by
    intro Q hQ
    rw [hR', DivisorWithCoeffs.coeff_sub, hEScoeff] at hQ
    change ((if ι Q.genericPoint ∈ E.support then (1 : ℚ) else 0) -
      (Finsupp.single P (1 : ℚ)) Q) ≠ 0 at hQ
    by_cases hQP : Q = P
    · subst hQP
      rw [if_pos hPE, Finsupp.single_eq_same, sub_self] at hQ
      exact absurd rfl hQ
    · rw [Finsupp.single_apply, if_neg (Ne.symm hQP)] at hQ
      split_ifs at hQ with h
      · exact ⟨hQP, h⟩
      · simp at hQ
  have hR'pt : ∀ t : T, j t ∉ R'.supp := by
    intro t ht
    obtain ⟨Q, hQ0, htQ⟩ := DivisorWithCoeffs.mem_supp_iff.mp ht
    obtain ⟨hQP, hQE⟩ := hR'coeff Q hQ0
    have htP : j t ∈ P.support := hP ▸ ⟨t, rfl⟩
    exact hQP (eq_of_mem_support_of_stratum hD hJ ι hyJ hker hED hEJ hQE hPE htQ htP)
  have hR'0 : R'.IsPullback j (fun W => hR'pt _) 0 :=
    qdivisor_isPullback_zero_of_forall (hQS R') _ (fun E => hR'pt _)
  -- `(A|_S - E|_S)|_T = R`
  have hgen3 : ∀ W : irreducibleComponents T, j (componentGenericPoint T W) ∉ (AS - ES).supp := by
    intro W hW
    rw [hcgp, hjT] at hW
    obtain ⟨Q, hQ0, hQ⟩ := DivisorWithCoeffs.mem_supp_iff.mp hW
    obtain rfl := MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support hQ
    apply hQ0
    rw [DivisorWithCoeffs.coeff_sub, hASP, hEScoeff, if_pos hPE, sub_self]
  have hAS' : AS - ES = (AS - Finsupp.single P 1) - R' := by rw [hR']; abel
  have h3 : (AS - ES).IsPullback j hgen3 RT := by
    have := qdivisor_isPullback_sub hQS hR hR'0 (by rw [← hAS']; exact hgen3)
    rw [sub_zero] at this
    exact qdivisor_isPullback_congr hAS'.symm this
  exact qdivisor_isPullback_comp hSub h3 hgen2

/-- A closed subscheme onto the closure of `w` in an integral scheme of finite type over `k` has
dimension `dim M - codim w`. -/
private lemma topologicalKrullDim_add_coheight_of_range {k : Type} [Field k] {M S : Scheme.{0}}
    (sM : M ⟶ Spec (.of k)) [IsIntegral M] [LocallyOfFiniteType sM] (ι : S ⟶ M)
    [IsClosedImmersion ι] {w : M} (hι : Set.range ι.base = closure {w}) :
    topologicalKrullDim S + Order.coheight w = topologicalKrullDim M := by
  have h1 : topologicalKrullDim S = topologicalKrullDim (Set.range ι.base) :=
    IsHomeomorph.topologicalKrullDim_eq _ ι.isEmbedding.toHomeomorph.isHomeomorph
  rw [h1, hι]
  exact MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sM w

/-- **The stratum through a point.** A point `w` on components `J'` of an snc divisor lies on a
stratum `closure {ξ}` cut out by `J'`, with `codim ξ = |J'|`. -/
private theorem exists_stratum_specializes {R : Type*} [Zero R] {k : Type} [Field k]
    {M : Scheme.{0}} [IsLocallyNoetherian M] [CompactSpace M] {sM : M ⟶ Spec (.of k)}
    {D : DivisorWithCoeffs R M} (hD : D.IsSNC sM) {J' : Finset (MMP.Mori.PrimeDivisor M)}
    (hJ' : J' ⊆ D.support) {w : M} (hwJ : ∀ G ∈ J', w ∈ G.support) :
    ∃ ξ : M, ξ ⤳ w ∧ (∀ G ∈ J', ξ ∈ G.support) ∧ Order.coheight ξ = J'.card ∧
      Maximal (fun T : Set M => IsIrreducible T ∧ T ⊆ ⋂ E ∈ J', (E.support : Set M))
        (closure {ξ}) := by
  haveI : AlgebraicGeometry.IsNoetherian M := ⟨⟩
  have hcl : IsClosed (⋂ E ∈ J', (E.support : Set M)) :=
    isClosed_biInter fun G _ => G.idealSheaf.support.isClosed
  obtain ⟨-, hcov⟩ := MMP.Resolution.Aux.finite_and_cover_componentsOf hcl
  obtain ⟨V, hV, hwV⟩ := hcov (Set.mem_iInter₂.mpr hwJ)
  obtain ⟨ξ, hVξ, hξJ, hc⟩ := coheight_eq_card_of_isSNCStratum hD hJ' hV
  refine ⟨ξ, ?_, hξJ, hc, hVξ ▸ hV⟩
  rw [specializes_iff_mem_closure, ← hVξ]
  exact hwV

/-- Transport of a rational pluriform along an equality of structure morphisms does not change
its divisor. -/
private lemma divisorOfForm_eqRec {k : Type} [Field k] {W : Scheme.{0}} [IsIntegral W]
    [IsLocallyNoetherian W] [CompactSpace W] {s₁ s₂ : W ⟶ Spec (.of k)} [LocallyOfFiniteType s₁]
    [LocallyOfFiniteType s₂] (h : s₁ = s₂) {d : ℕ} {m : ℤ} (ρ : RationalPluriForms s₁ d m) :
    divisorOfForm (h ▸ ρ : RationalPluriForms s₂ d m) = divisorOfForm ρ := by
  subst h
  rfl

/-- `a + b = n` in `WithBot ℕ∞` with `b, n` natural numbers forces `a = n - b`. -/
private lemma withBot_eq_sub_of_add_eq {a : WithBot ℕ∞} {b n : ℕ} (h : a + (b : ℕ∞) = (n : ℕ∞)) :
    a = ((n - b : ℕ) : ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => simp at h
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have h2 : ((⊤ + (b : ℕ∞) : ℕ∞) : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast h
      rw [top_add] at h2
      exact ENat.top_ne_coe n (WithBot.coe_injective h2)
    | coe a =>
      have h2 : a + b = n := by exact_mod_cast h
      have : a = n - b := by omega
      rw [this]

/-- `a + b = n` in `WithBot ℕ∞` with `b, n` natural numbers forces `b ≤ n`. -/
private lemma le_of_withBot_add_eq {a : WithBot ℕ∞} {b n : ℕ} (h : a + (b : ℕ∞) = (n : ℕ∞)) :
    b ≤ n := by
  induction a using WithBot.recBotCoe with
  | bot => simp at h
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have h2 : ((⊤ + (b : ℕ∞) : ℕ∞) : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast h
      rw [top_add] at h2
      exact ENat.top_ne_coe n (WithBot.coe_injective h2)
    | coe a =>
      have h2 : a + b = n := by exact_mod_cast h
      omega

/-- Transport along an equality of structure morphisms preserves nonvanishing. -/
private lemma eqRec_ne_zero {k : Type} [Field k] {W : Scheme.{0}} [IsIntegral W]
    {s₁ s₂ : W ⟶ Spec (.of k)} (h : s₁ = s₂) {d : ℕ} {m : ℤ} {ρ : RationalPluriForms s₁ d m}
    (hρ : ρ ≠ 0) : (h ▸ ρ : RationalPluriForms s₂ d m) ≠ 0 := by
  subst h
  exact hρ

open scoped Classical in
/-- The coefficients of `B - ∑_{G ∈ J} G`. -/
private lemma coeff_sub_sum_single {X : Scheme.{0}} (B : QDivisor X)
    (J : Finset (MMP.Mori.PrimeDivisor X)) (G : MMP.Mori.PrimeDivisor X) :
    (B - ∑ G' ∈ J, Finsupp.single G' (1 : ℚ)).coeff G = B.coeff G - if G ∈ J then 1 else 0 := by
  rw [DivisorWithCoeffs.coeff_sub]
  congr 1
  change (∑ G' ∈ J, Finsupp.single G' (1 : ℚ)) G = _
  rw [Finsupp.finset_sum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq']

/-- Removing components of `B` does not enlarge the support. -/
private lemma support_sub_sum_single_subset {X : Scheme.{0}} (B : QDivisor X)
    {J : Finset (MMP.Mori.PrimeDivisor X)} (hJ : J ⊆ B.support) :
    (B - ∑ G ∈ J, Finsupp.single G (1 : ℚ)).support ⊆ B.support := by
  classical
  intro G hG
  rw [Finsupp.mem_support_iff] at hG ⊢
  intro h0
  apply hG
  change (B - ∑ G ∈ J, Finsupp.single G (1 : ℚ)).coeff G = 0
  change B.coeff G = 0 at h0
  rw [coeff_sub_sum_single, h0,
    if_neg (fun hGJ => (Finsupp.mem_support_iff.mp (hJ hGJ)) h0), sub_zero]

/-- Removing coefficient-one components `J` of `B` leaves coefficient zero along `J`. -/
private lemma coeff_sub_sum_single_eq_zero {X : Scheme.{0}} (B : QDivisor X)
    {J : Finset (MMP.Mori.PrimeDivisor X)} (hJ1 : ∀ G ∈ J, B.coeff G = 1) :
    ∀ G ∈ J, (B - ∑ G ∈ J, Finsupp.single G (1 : ℚ)).coeff G = 0 := fun G hG => by
  classical
  rw [coeff_sub_sum_single, if_pos hG, hJ1 G hG, sub_self]

open scoped Classical in
/-- Sums of coefficients of `B - ∑_{G ∈ J} G` over its components with a property `p`, when `B`
has coefficient one along `J`. -/
private lemma sum_filter_sub_sum_single {X : Scheme.{0}} (B : QDivisor X)
    (J : Finset (MMP.Mori.PrimeDivisor X)) (hJ1 : ∀ G ∈ J, B.coeff G = 1)
    (p : MMP.Mori.PrimeDivisor X → Prop) :
    ∑ E ∈ (B - ∑ G ∈ J, Finsupp.single G (1 : ℚ)).support.filter p,
        (B - ∑ G ∈ J, Finsupp.single G (1 : ℚ)).coeff E =
      ∑ E ∈ B.support.filter (fun E => E ∉ J ∧ p E), B.coeff E := by
  have hset : (B - ∑ G ∈ J, Finsupp.single G (1 : ℚ)).support.filter p =
      B.support.filter (fun E => E ∉ J ∧ p E) := by
    ext E
    simp only [Finset.mem_filter, Finsupp.mem_support_iff]
    change ((B - ∑ G ∈ J, Finsupp.single G (1 : ℚ)).coeff E ≠ 0 ∧ p E) ↔
      (B.coeff E ≠ 0 ∧ E ∉ J ∧ p E)
    rw [coeff_sub_sum_single]
    by_cases hE : E ∈ J
    · simp [hE, hJ1 E hE]
    · simp [hE]
  rw [hset]
  refine Finset.sum_congr rfl fun E hE => ?_
  rw [coeff_sub_sum_single, if_neg (Finset.mem_filter.mp hE).2.1, sub_zero]

open scoped Classical in
/-- **Iterated residues along a stratum.** Let `M` be a smooth variety of dimension `N` with an snc
`ℚ`-divisor `Γ`, `τ` a nonzero rational top form, and `S` a reduced closed subscheme onto a
stratum `closure {w}` cut out by `c + 1` components `J` of `Γ` of coefficient one, with
`w ∉ Supp (div τ + Γ)`. Then there is a nonzero top form `ρ` on `S` (an iterated residue of `τ`)
with `(div τ + Γ)|_S = div ρ + (Γ - ∑_{G ∈ J} G)|_S`. -/
private theorem exists_isPullback_divisorOfForm_add_of_stratum {k : Type} [Field k]
    [PerfectField k] {M : Scheme.{0}} (sM : M ⟶ Spec (.of k)) [IsIntegral M]
    [IsLocallyNoetherian M] [IsNormal M] [CompactSpace M] [LocallyOfFiniteType sM]
    [QuasiCompact sM] [IsSeparated sM] [Smooth sM] {N : ℕ} (hdim : topologicalKrullDim M = N)
    {Γ : QDivisor M} (hΓ : Γ.IsSNC sM) (hQM : ∀ A : QDivisor M, A.IsQCartier)
    (τ : RationalPluriForms sM N 1) (hτ0 : τ ≠ 0) (c : ℕ) :
    ∀ {J : Finset (MMP.Mori.PrimeDivisor M)} (_hJc : J.card = c + 1) (_hJ : J ⊆ Γ.support)
      (_hJ1 : ∀ G ∈ J, Γ.coeff G = 1) {w : M} (_hwJ : ∀ G ∈ J, w ∈ G.support)
      (_hcw : Order.coheight w = J.card)
      (_hwD : w ∉ (Divisor.toQDivisor (divisorOfForm τ) + Γ).supp)
      {S : Scheme.{0}} (ι : S ⟶ M) [IsClosedImmersion ι] [IsIntegral S] [IsLocallyNoetherian S]
      [IsNormal S] [CompactSpace S] (_hι : Set.range ι.base = closure {w}) {d : ℕ}
      (_hd : d + J.card = N)
      {hgenΓ : ∀ W : irreducibleComponents S, ι (componentGenericPoint S W) ∉
        (Γ - ∑ G ∈ J, Finsupp.single G 1).supp}
      {ΓS : QDivisor S} (_hΓS : (Γ - ∑ G ∈ J, Finsupp.single G 1).IsPullback ι hgenΓ ΓS),
      ∃ ρ : RationalPluriForms (ι ≫ sM) d 1, ρ ≠ 0 ∧
        ∃ hgenD : ∀ W : irreducibleComponents S, ι (componentGenericPoint S W) ∉
            (Divisor.toQDivisor (divisorOfForm τ) + Γ).supp,
          (Divisor.toQDivisor (divisorOfForm τ) + Γ).IsPullback ι hgenD
            (Divisor.toQDivisor (divisorOfForm ρ) + ΓS) := by
  induction c with
  | zero =>
    intro J hJc hJ hJ1 w hwJ hcw hwD S ι _ _ _ _ _ hι d hd hgenΓ ΓS hΓS
    obtain ⟨E, rfl⟩ := Finset.card_eq_one.mp hJc
    have hEw : w = E.genericPoint := by
      have hsp : E.genericPoint ⤳ w := by
        rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact hwJ E (Finset.mem_singleton_self E)
      by_contra hne
      have hlt : w < E.genericPoint := lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hsp)
        (fun h => hne (hsp.antisymm (Scheme.le_iff_specializes.mp h)).eq.symm)
      have := Order.coheight_strictAnti hlt (by
        rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]; exact ENat.coe_lt_top _)
      rw [hcw, AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at this
      simp at this
    subst hEw
    have hιE : Set.range ι.base = (E.support : Set M) := by
      rw [hι, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    obtain ⟨hsm, -, -⟩ := stratum_package sM hΓ hJ hwJ hcw ι hι
    have hd' : d + 1 = N := by simpa using hd
    subst hd'
    have hjE : ι (genericPoint S) = E.genericPoint := map_genericPoint_eq_of_range ι E hιE
    have hE1 : Γ.coeff E = 1 := hJ1 E (Finset.mem_singleton_self E)
    have hord : E.ordForm τ = -1 := by
      have h0 : (Divisor.toQDivisor (divisorOfForm τ) + Γ).coeff E = 0 := by
        by_contra h
        exact hwD (DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, h, by
          rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl⟩)
      rw [DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_divisorOfForm, hE1] at h0
      have : ((E.ordForm τ : ℤ) : ℚ) = -1 := by linarith
      exact_mod_cast this
    haveI hvar : AlgebraicGeometry.IsVariety k sM := ⟨⟩
    obtain ⟨ρ, hρu, hρ0, -, -⟩ :=
      MMP.Mori.existsUnique_isPoincareResidue_of_ordForm_eq_neg_one sM hdim ι E hjE τ hτ0 hord
    have hD : ∀ W : irreducibleComponents S, ι (componentGenericPoint S W) ∉
        (Divisor.toQDivisor (divisorOfForm τ) + Γ).supp := fun W => by
      rw [componentGenericPoint_eq_genericPoint, hjE]; exact hwD
    obtain ⟨-, -, h3⟩ := MMP.Fourfold.isPullback_divisorOfForm_add_of_isPoincareResidue sM hvar
      hdim ι E hιE τ hτ0 hord ρ ((hρu ρ).mpr rfl)
    obtain ⟨R, ⟨hgen', hR⟩, hpb⟩ := h3 _ Γ (hQM _) hD rfl
    have hsum : (Γ - ∑ G ∈ ({E} : Finset _), Finsupp.single G 1) = Γ - Finsupp.single E 1 := by
      rw [Finset.sum_singleton]
    have hΓS' := qdivisor_isPullback_congr hsum (hB₂ := hgen') hΓS
    have hRS : R = ΓS := (hR.pullback_eq (hQM _)).symm.trans (hΓS'.pullback_eq (hQM _))
    subst hRS
    exact ⟨ρ, hρ0, hD, hpb⟩
  | succ c ih =>
    intro J hJc hJ hJ1 w hwJ hcw hwD S ι _ _ _ _ _ hι d hd hgenΓ ΓS hΓS
    haveI : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
    obtain ⟨hsmS, -, -⟩ := stratum_package sM hΓ hJ hwJ hcw ι hι
    -- a component `E ∈ J` and the remaining `J'`
    obtain ⟨E, hEJ⟩ : J.Nonempty := Finset.card_pos.mp (by omega)
    set J' := J.erase E with hJ'
    have hJ'c : J'.card = c + 1 := by rw [hJ', Finset.card_erase_of_mem hEJ, hJc]; rfl
    have hJ'J : J' ⊆ J := Finset.erase_subset E J
    have hEJ' : E ∉ J' := Finset.notMem_erase E J
    have hJ'Γ : J' ⊆ Γ.support := hJ'J.trans hJ
    -- the stratum `S'` through `w` cut out by `J'`
    obtain ⟨ξ, hξw, hξJ, hcξ, -⟩ := exists_stratum_specializes hΓ hJ'Γ (fun G hG => hwJ G (hJ'J hG))
    obtain ⟨hsmV, -⟩ := stratum_closure sM hΓ hJ'Γ hξJ hcξ
    set V := Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure {ξ}) with hV
    haveI : LocallyOfFinitePresentation (V.subschemeι ≫ sM) :=
      (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := V.subschemeι ≫ sM)).mpr
        inferInstance
    haveI : Smooth (V.subschemeι ≫ sM) := (MMP.Mori.isSmoothScheme_iff _).1 hsmV
    haveI : IsReduced V.subscheme := isReduced_of_smooth (V.subschemeι ≫ sM)
    have hrV : Set.range V.subschemeι.base = closure {ξ} := by
      rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal,
        TopologicalSpace.Closeds.coe_closure]
    haveI : IsIntegral V.subscheme :=
      isIntegral_of_isIrreducible_range V.subschemeι (hrV ▸ isIrreducible_singleton.closure)
    haveI : IsLocallyNoetherian V.subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian (V.subschemeι ≫ sM)
    haveI : IsNormal V.subscheme := AlgebraicGeometry.isNormal_of_smooth (V.subschemeι ≫ sM)
    haveI : CompactSpace V.subscheme := V.subschemeι.isClosedEmbedding.compactSpace
    obtain ⟨-, hkerV, hyJV⟩ := stratum_package sM hΓ hJ'Γ hξJ hcξ V.subschemeι hrV
    have hQV : ∀ A : QDivisor V.subscheme, A.IsQCartier :=
      MMP.Fourfold.isQCartier_of_isSmoothScheme hsmV
    -- `ι` factors through `S'`
    have hwV : w ∈ closure {ξ} := specializes_iff_mem_closure.mp hξw
    have hsub : Set.range ι.base ⊆ Set.range V.subschemeι.base := by
      rw [hι, hrV]
      exact closure_minimal (Set.singleton_subset_iff.mpr hwV) isClosed_closure
    obtain ⟨j, hjι⟩ := exists_comp_eq_of_range_subset V.subschemeι ι hsub
    haveI : IsClosedImmersion j := by
      have : IsClosedImmersion (j ≫ V.subschemeι) := by rw [hjι]; infer_instance
      exact IsClosedImmersion.of_comp_isClosedImmersion j V.subschemeι
    subst hjι
    -- the prime divisor `P` of `S'` under `w`
    obtain ⟨y, hy⟩ : w ∈ Set.range V.subschemeι.base := hrV ▸ hwV
    have hcy : Order.coheight y = 1 := by
      have h := coheight_map_eq_add_card hΓ hJ'Γ V.subschemeι y (hyJV y) (hkerV y)
      have hy' : V.subschemeι y = w := hy
      rw [hy', hcw, hJc, hJ'c] at h
      obtain ⟨a, ha⟩ : ∃ a : ℕ, Order.coheight y = a := by
        refine ⟨(Order.coheight y).toNat, (ENat.coe_toNat ?_).symm⟩
        intro htop
        rw [htop] at h
        have h2 : ((⊤ + (c + 1 : ℕ∞) : ℕ∞) : WithBot ℕ∞) = ((c + 1 + 1 : ℕ∞) : WithBot ℕ∞) := by
          exact_mod_cast h
        rw [top_add] at h2
        exact absurd (WithBot.coe_injective h2) (by
          intro h3; exact ENat.top_ne_coe (c + 1 + 1) (by exact_mod_cast h3))
      rw [ha] at h ⊢
      have : a + (c + 1) = c + 1 + 1 := by exact_mod_cast h
      exact_mod_cast (by omega : a = 1)
    set P : MMP.Mori.PrimeDivisor V.subscheme :=
      AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hcy with hPdef
    have hPy : P.genericPoint = y := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne y hcy
    have hjP : Set.range j.base = (P.support : Set V.subscheme) := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      change Set.range j.base = closure {P.genericPoint}
      rw [hPy, V.subschemeι.isEmbedding.isInducing.closure_eq_preimage_closure_image,
        Set.image_singleton, hy, ← hι]
      ext x
      constructor
      · rintro ⟨t, rfl⟩; exact ⟨t, rfl⟩
      · rintro ⟨t, ht⟩
        exact ⟨t, V.subschemeι.isEmbedding.injective (by
          rw [← Scheme.Hom.comp_apply]; exact ht)⟩
    have hjS : j (genericPoint S) = P.genericPoint := map_genericPoint_eq_of_range j P hjP
    have hPE : V.subschemeι P.genericPoint ∈ E.support := by
      rw [hPy, hy]; exact hwJ E hEJ
    have hPw : V.subschemeι P.genericPoint = w := by rw [hPy]; exact hy
    -- `Γ_{S'}`
    set A := Γ - ∑ G ∈ J', Finsupp.single G (1 : ℚ) with hA
    have hAD : A.support ⊆ Γ.support := support_sub_sum_single_subset Γ hJ'Γ
    have hAJ := coeff_sub_sum_single_eq_zero Γ (fun G hG => hJ1 G (hJ'J hG))
    have hgenV := stratum_hgen hΓ hJ'Γ V.subschemeι hyJV hkerV A hAD hAJ
    have hΓV := QDivisor.isPullback_pullback (hQM A) hgenV
    set ΓV := A.pullback (hQM A) hgenV with hΓVdef
    -- the induction hypothesis on `S'`
    have hξD : ξ ∉ (Divisor.toQDivisor (divisorOfForm τ) + Γ).supp := fun h =>
      hwD (hξw.mem_closed (Divisor.toQDivisor (divisorOfForm τ) + Γ).supp.isClosed h)
    have hdV : d + 1 + J'.card = N := by rw [hJ'c]; rw [hJc] at hd; omega
    obtain ⟨ρ', hρ'0, hgenD', hpb'⟩ := ih hJ'c hJ'Γ (fun G hG => hJ1 G (hJ'J hG)) hξJ hcξ hξD
      V.subschemeι hrV hdV hΓV
    -- `ord_P ρ' = -1`
    have h0P : (Divisor.toQDivisor (divisorOfForm ρ') + ΓV).coeff P = 0 :=
      qdivisor_coeff_eq_zero_of_isPullback (hQM _) hpb' P (by rw [hPw]; exact hwD)
    have hΓVP : ΓV.coeff P = 1 := by
      rw [coeff_isPullback_of_stratum sM hΓ hJ'Γ V.subschemeι hyJV hkerV A hAD hAJ (hQM A) hΓV P]
      have hfil : A.support.filter (fun E' => V.subschemeι P.genericPoint ∈ E'.support) = {E} := by
        ext E'
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hE', hPE'⟩
          by_contra hne
          have hE'J : E' ∉ J' := fun h => (Finsupp.mem_support_iff.mp hE') (hAJ E' h)
          have := card_le_of_stratum hΓ hJ'Γ V.subschemeι P.genericPoint (hyJV _) (hkerV _)
            (c := 1) (by rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]; rfl) {E', E}
            (Finset.insert_subset (hAD hE') (Finset.singleton_subset_iff.mpr (hJ hEJ)))
            (Finset.disjoint_left.mpr fun G hG hGJ => by
              rcases Finset.mem_insert.mp hG with rfl | hG
              · exact hE'J hGJ
              · rw [Finset.mem_singleton] at hG; subst hG; exact hEJ' hGJ)
            (fun G hG => by
              rcases Finset.mem_insert.mp hG with rfl | hG
              · exact hPE'
              · rw [Finset.mem_singleton] at hG; subst hG; exact hPE)
          rw [Finset.card_pair hne] at this
          omega
        · rintro rfl
          refine ⟨Finsupp.mem_support_iff.mpr ?_, hPE⟩
          change A.coeff E' ≠ 0
          rw [hA, coeff_sub_sum_single, if_neg hEJ', hJ1 E' hEJ]
          norm_num
      rw [hfil, Finset.sum_singleton, hA, coeff_sub_sum_single, if_neg hEJ', hJ1 E hEJ, sub_zero]
    have hordP : P.ordForm ρ' = -1 := by
      rw [DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_divisorOfForm, hΓVP] at h0P
      have : ((P.ordForm ρ' : ℤ) : ℚ) = -1 := by linarith
      exact_mod_cast this
    -- the dimension of `S'`
    have hdimV : topologicalKrullDim V.subscheme = (d : WithBot ℕ∞) + 1 := by
      have h := topologicalKrullDim_add_coheight_of_range sM V.subschemeι hrV
      rw [hcξ, hdim, hJ'c] at h
      have h' := withBot_eq_sub_of_add_eq (b := c + 1) (n := N) (by exact_mod_cast h)
      rw [h']
      rw [hJc] at hd
      have : N - (c + 1) = d + 1 := by omega
      rw [this]
      push_cast
      rfl
    -- the residue along `P`
    haveI hvarV : AlgebraicGeometry.IsVariety k (V.subschemeι ≫ sM) := ⟨⟩
    haveI : Smooth (j ≫ V.subschemeι ≫ sM) := by rw [← Category.assoc]; exact hsmS
    obtain ⟨ρ, hρu, hρ0, -, -⟩ := MMP.Mori.existsUnique_isPoincareResidue_of_ordForm_eq_neg_one
      (V.subschemeι ≫ sM) hdimV j P hjS ρ' hρ'0 hordP
    obtain ⟨-, -, h3⟩ := MMP.Fourfold.isPullback_divisorOfForm_add_of_isPoincareResidue
      (V.subschemeι ≫ sM) hvarV hdimV j P hjP ρ' hρ'0 hordP ρ ((hρu ρ).mpr rfl)
    have hDj : ∀ W : irreducibleComponents S, j (componentGenericPoint S W) ∉
        (Divisor.toQDivisor (divisorOfForm ρ') + ΓV).supp := by
      intro W hW
      rw [componentGenericPoint_eq_genericPoint, hjS] at hW
      obtain ⟨Q, hQ0, hQ⟩ := DivisorWithCoeffs.mem_supp_iff.mp hW
      obtain rfl := MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support hQ
      exact hQ0 h0P
    obtain ⟨R, ⟨hgenR, hR⟩, hpbR⟩ := h3 _ ΓV (hQV _) hDj rfl
    -- `R = Γ_S`
    have hJsum : ∑ G ∈ J, Finsupp.single G (1 : ℚ) =
        Finsupp.single E 1 + ∑ G ∈ J', Finsupp.single G (1 : ℚ) := by
      rw [hJ', Finset.add_sum_erase J (fun G => Finsupp.single G (1 : ℚ)) hEJ]
    have hsumJ : Γ - ∑ G ∈ J, Finsupp.single G 1 = A - Finsupp.single E 1 := by
      rw [hJsum, hA]; abel
    have hgen2 : ∀ W : irreducibleComponents S, (j ≫ V.subschemeι) (componentGenericPoint S W) ∉
        (A - Finsupp.single E 1).supp := by
      rw [← hsumJ]; exact hgenΓ
    have hRA := isPullback_sub_single_comp_of_stratum sM hΓ hJ'Γ V.subschemeι hyJV hkerV hQM hQV
      j P hjP (hJ hEJ) hEJ' hPE A hAD hAJ hΓV hR hgen2
    have hΓS' := qdivisor_isPullback_congr hsumJ (hB₂ := hgen2) hΓS
    have hRS : R = ΓS := (hRA.pullback_eq (hQM _)).symm.trans (hΓS'.pullback_eq (hQM _))
    subst hRS
    -- compose, and transport the form
    have hgenC : ∀ W : irreducibleComponents S, (j ≫ V.subschemeι) (componentGenericPoint S W) ∉
        (Divisor.toQDivisor (divisorOfForm τ) + Γ).supp := fun W => by
      rw [componentGenericPoint_eq_genericPoint, Scheme.Hom.comp_apply, hjS, hPw]
      exact hwD
    have hcomp := qdivisor_isPullback_comp hpb' hpbR hgenC
    have hs : j ≫ V.subschemeι ≫ sM = (j ≫ V.subschemeι) ≫ sM := (Category.assoc _ _ _).symm
    refine ⟨hs ▸ ρ, eqRec_ne_zero hs hρ0, hgenC, ?_⟩
    rw [divisorOfForm_eqRec hs]
    exact hcomp

open scoped Classical in
/-- **Flags of iterated adjunction on an snc subboundary pair.** The final stratum `T` of a flag
of iterated adjunction of an snc subboundary pair `(X, B)` is a smooth stratum `closure {w}` cut
out by `length` components `J` of `B` of coefficient one, and its different is the restriction
`B_T = (B - ∑_{G ∈ J} G)|_T`, given here by its coefficients: `B_T(Q)` is the sum of the
coefficients of the components of `B` outside `J` through `ι(η_Q)`. -/
private theorem flag_isStratum_coeff {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} (hB : IsSNCSubboundaryPair sX B) {N : ℕ}
    (hdim : topologicalKrullDim X = N) {T : Scheme.{0}} {ιT : T ⟶ X} {BT : QDivisor T}
    (FT : StratumAdjunctionData sX B ιT BT) :
    haveI := FT.isIntegral_stratum
    haveI := FT.isClosedImmersion
    ∃ (J : Finset (MMP.Mori.PrimeDivisor X)) (w : X), J ⊆ B.support ∧
      (∀ G ∈ J, B.coeff G = 1) ∧ J.card = FT.length ∧ (∀ G ∈ J, w ∈ G.support) ∧
      Order.coheight w = J.card ∧ Set.range ιT.base = closure {w} ∧ Smooth (ιT ≫ sX) ∧
      ∀ Q : MMP.Mori.PrimeDivisor T, BT.coeff Q =
        ∑ E ∈ B.support.filter (fun E => E ∉ J ∧ ιT Q.genericPoint ∈ E.support), B.coeff E := by
  haveI : LocallyOfFiniteType sX := hB.isProjectiveVariety.toIsVariety.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hB.isProjectiveVariety.toIsVariety.toQuasiCompact
  haveI : LocallyOfFinitePresentation sX :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := sX)).mpr inferInstance
  haveI hsmX : Smooth sX := (MMP.Mori.isSmoothScheme_iff sX).1 hB.isSmoothScheme
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have hQX : ∀ A : QDivisor X, A.IsQCartier :=
    MMP.Fourfold.isQCartier_of_isSmoothScheme hB.isSmoothScheme
  induction FT with
  | refl h =>
    refine ⟨∅, genericPoint X, by simp, by simp, rfl, by simp, ?_, ?_, ?_, ?_⟩
    · simp only [Finset.card_empty, CharP.cast_eq_zero]
      exact Order.coheight_eq_zero.mpr fun b _ =>
        Scheme.le_iff_specializes.mpr (genericPoint_specializes b)
    · simp [(genericPoint_spec X).def]
    · rw [Category.id_comp]; exact hsmX
    · intro Q
      have hid : ∀ x : X, (𝟙 X : X ⟶ X) x = x := fun x => rfl
      have hQmem : Q.genericPoint ∈ Q.support := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
      have hset : B.support.filter (fun E => E ∉ (∅ : Finset (MMP.Mori.PrimeDivisor X)) ∧
          (𝟙 X : X ⟶ X) Q.genericPoint ∈ E.support) = B.support.filter (fun E => E = Q) := by
        refine Finset.filter_congr fun E _ => ?_
        simp only [Finset.notMem_empty, not_false_eq_true, true_and, hid]
        exact ⟨MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support,
          fun h => h ▸ hQmem⟩
      rw [hset, Finset.sum_filter, Finset.sum_ite_eq']
      split_ifs with h
      · rfl
      · exact Finsupp.notMem_support_iff.mp h
  | @step S T ι BS F j BT hj ih =>
    obtain ⟨J, w, hJ, hJ1, hJl, hwJ, hcw, hι, hsmS, hBS⟩ := ih
    haveI := F.isIntegral_stratum
    haveI := F.isNormal_stratum
    haveI := F.isLocallyNoetherian_stratum
    haveI := F.isClosedImmersion
    haveI : CompactSpace S := ι.isClosedEmbedding.compactSpace
    obtain ⟨hTv, P, hP1, hjP, hjc, -⟩ := id hj
    haveI := hjc
    haveI : IsIntegral T := hTv.1.toIsIntegral
    haveI : IsNormal T := hTv.2
    haveI : LocallyOfFiniteType (j ≫ ι ≫ sX) := hTv.1.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (j ≫ ι ≫ sX)
    haveI : CompactSpace T := j.isClosedEmbedding.compactSpace
    haveI := hsmS
    haveI : LocallyOfFinitePresentation (ι ≫ sX) :=
      (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := ι ≫ sX)).mpr inferInstance
    have hQS : ∀ A : QDivisor S, A.IsQCartier :=
      MMP.Fourfold.isQCartier_of_isSmoothScheme ((MMP.Mori.isSmoothScheme_iff _).2 hsmS)
    obtain ⟨-, hkerS, hyJS⟩ := stratum_package sX hB.isSNC hJ hwJ hcw ι hι
    -- `B_S(P) = 1`, through a unique further component `E`
    have hPcoh : Order.coheight P.genericPoint = 1 :=
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P
    set Fl := B.support.filter (fun E => E ∉ J ∧ ι P.genericPoint ∈ E.support) with hFl
    have hFlc : Fl.card ≤ 1 := card_le_of_stratum hB.isSNC hJ ι P.genericPoint (hyJS _) (hkerS _)
      (c := 1) (by rw [hPcoh]; rfl) Fl (Finset.filter_subset _ _)
      (Finset.disjoint_left.mpr fun G hG hGJ => (Finset.mem_filter.mp hG).2.1 hGJ)
      (fun G hG => (Finset.mem_filter.mp hG).2.2)
    have hBSP := hBS P
    rw [← hFl] at hBSP
    obtain ⟨E, hFlE⟩ : ∃ E, Fl = {E} := by
      have hne : Fl.Nonempty := by
        by_contra h
        rw [Finset.not_nonempty_iff_eq_empty] at h
        rw [hBSP, h, Finset.sum_empty] at hP1
        norm_num at hP1
      exact Finset.card_eq_one.mp (le_antisymm hFlc (Finset.card_pos.mpr hne))
    have hEFl : E ∈ Fl := hFlE ▸ Finset.mem_singleton_self E
    obtain ⟨hEB, hEJ, hPE⟩ := Finset.mem_filter.mp hEFl
    have hBSP1 : BS.coeff P = B.coeff E := by rw [hBSP, hFlE, Finset.sum_singleton]
    have hBE : B.coeff E = 1 := le_antisymm (hB.coeff_le_one E) (hBSP1 ▸ hP1)
    have hBSP' : BS.coeff P = 1 := hBSP1.trans hBE
    -- the new stratum
    set JT := insert E J with hJTdef
    set wT := ι P.genericPoint with hwT
    have hJT : JT ⊆ B.support := Finset.insert_subset hEB hJ
    have hJT1 : ∀ G ∈ JT, B.coeff G = 1 := by
      intro G hG
      rcases Finset.mem_insert.mp hG with rfl | hG
      · exact hBE
      · exact hJ1 G hG
    have hwTJ : ∀ G ∈ JT, wT ∈ G.support := by
      intro G hG
      rcases Finset.mem_insert.mp hG with rfl | hG
      · exact hPE
      · exact hyJS _ G hG
    have hcwT : Order.coheight wT = JT.card := by
      have h := coheight_map_eq_add_card hB.isSNC hJ ι P.genericPoint (hyJS _) (hkerS _)
      rw [hPcoh] at h
      rw [Finset.card_insert_of_notMem hEJ]
      have h' : ((1 + J.card : ℕ) : WithBot ℕ∞) = ((Order.coheight wT : ℕ∞) : WithBot ℕ∞) := by
        rw [← h]; push_cast; rfl
      have h'' := WithBot.coe_injective h'
      rw [← h'']
      push_cast
      ring
    have hrT : Set.range (j ≫ ι).base = closure {wT} := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hjP,
        AlgebraicGeometry.PrimeDivisor.support_eq_closure,
        ← ι.isClosedMap.closure_image_eq_of_continuous ι.continuous, Set.image_singleton]
    obtain ⟨hsmT, hkerT, hyJT⟩ := stratum_package sX hB.isSNC hJT hwTJ hcwT (j ≫ ι) hrT
    -- the dimension of `S`
    have hdS := topologicalKrullDim_add_coheight_of_range sX ι hι
    rw [hcw, hdim] at hdS
    have hdS' := withBot_eq_sub_of_add_eq (b := J.card) (n := N) (by exact_mod_cast hdS)
    have hdT := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX wT
    rw [hcwT, hdim, Finset.card_insert_of_notMem hEJ] at hdT
    have hle := le_of_withBot_add_eq (b := J.card + 1) (n := N) (by exact_mod_cast hdT)
    have hdimS : topologicalKrullDim S = ((N - J.card - 1 : ℕ) : WithBot ℕ∞) + 1 := by
      rw [hdS']
      have : N - J.card = (N - J.card - 1) + 1 := by omega
      rw [this]
      push_cast
      rfl
    -- one adjunction step: `B_T = (B_S - P)|_T`
    haveI hSv : AlgebraicGeometry.IsVariety k (ι ≫ sX) := F.isNormalVariety.1
    haveI : Smooth (j ≫ ι ≫ sX) := by rw [← Category.assoc]; exact hsmT
    obtain ⟨hgen1, hR⟩ := isPullback_sub_single_of_isAdjunctionStep hSv hdimS hj P hjP hBSP' hQS
    -- `B_S = (B - ∑_J G)|_S`
    set A := B - ∑ G ∈ J, Finsupp.single G (1 : ℚ) with hA
    have hAD : A.support ⊆ B.support := support_sub_sum_single_subset B hJ
    have hAJ := coeff_sub_sum_single_eq_zero B hJ1
    have hgenA := stratum_hgen hB.isSNC hJ ι hyJS hkerS A hAD hAJ
    have hAS := QDivisor.isPullback_pullback (hQX A) hgenA
    have hBSeq : A.pullback (hQX A) hgenA = BS := by
      ext Q
      rw [coeff_isPullback_of_stratum sX hB.isSNC hJ ι hyJS hkerS A hAD hAJ (hQX A) hAS Q, hA,
        sum_filter_sub_sum_single B J hJ1, hBS Q]
    rw [hBSeq] at hAS
    -- `B_T = (B - ∑_{J_T} G)|_T`
    have hsumJT : B - ∑ G ∈ JT, Finsupp.single G (1 : ℚ) = A - Finsupp.single E 1 := by
      rw [hJTdef, Finset.sum_insert hEJ, hA]; abel
    have hAT : (B - ∑ G ∈ JT, Finsupp.single G (1 : ℚ)).support ⊆ B.support :=
      support_sub_sum_single_subset B hJT
    have hATJ := coeff_sub_sum_single_eq_zero B hJT1
    have hgen2' := stratum_hgen hB.isSNC hJT (j ≫ ι) hyJT hkerT _ hAT hATJ
    have hgen2 : ∀ W : irreducibleComponents T, (j ≫ ι) (componentGenericPoint T W) ∉
        (A - Finsupp.single E 1).supp := by
      rw [← hsumJT]; exact hgen2'
    have hRT := isPullback_sub_single_comp_of_stratum sX hB.isSNC hJ ι hyJS hkerS hQX hQS j P hjP
      hEB hEJ hPE A hAD hAJ hAS hR hgen2
    have hRT' := qdivisor_isPullback_congr hsumJT.symm (hB₂ := hgen2') hRT
    refine ⟨JT, wT, hJT, hJT1, ?_, hwTJ, hcwT, hrT, hsmT, fun Q => ?_⟩
    · rw [Finset.card_insert_of_notMem hEJ, hJl]; rfl
    · rw [coeff_isPullback_of_stratum sX hB.isSNC hJT (j ≫ ι) hyJT hkerT _ hAT hATJ (hQX _) hRT' Q,
        sum_filter_sub_sum_single B JT hJT1]

/-- **A form adapted to a point.** On a normal variety of dimension `N` over a perfect field on
which every divisor is Cartier, for every divisor `A` and point `x` there is a nonzero rational
top form `σ` with `x ∉ Supp (div σ + A)`: divide any nonzero form by a local equation of
`div σ₀ + A` near `x`. -/
private theorem exists_form_notMem_supp {k : Type} [Field k] [PerfectField k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] {N : ℕ} (hdim : topologicalKrullDim X = N)
    (hcart : ∀ D : Divisor X, D.IsCartier) (σ₀ : RationalPluriForms sX N 1) (hσ₀ : σ₀ ≠ 0)
    (A : Divisor X) (x : X) :
    ∃ σ : RationalPluriForms sX N 1, σ ≠ 0 ∧ x ∉ (divisorOfForm σ + A).supp := by
  obtain ⟨U, hxU, φ, hφ⟩ := hcart (divisorOfForm σ₀ + A) x
  obtain ⟨g, hg0, hg⟩ := MMP.Positivity.exists_ord_eq_of_units φ
  have hgi : g⁻¹ ≠ 0 := inv_ne_zero hg0
  refine ⟨g⁻¹ • σ₀, smul_ne_zero hgi hσ₀, fun hx => ?_⟩
  obtain ⟨E, hE0, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hx
  apply hE0
  have hEU : (E.support ∩ U).Nonempty := ⟨x, hxE, hxU⟩
  have h1 := hφ E hEU
  rw [DivisorWithCoeffs.coeff_add, coeff_divisorOfForm] at h1 ⊢
  rw [E.ordForm_smul_of_topologicalKrullDim_eq hdim hgi hσ₀]
  have h2 := ord_inv_eq_neg hg0 E.genericPoint
  have h4 := hg E
  omega

end StratumChain

/-- The generic point of an integral scheme lies on no prime divisor. -/
private theorem genericPoint_notMem_supp {X : Scheme.{0}} [IsIntegral X] {R : Type*} [Zero R]
    (D : DivisorWithCoeffs R X) : genericPoint X ∉ D.supp := by
  intro h
  obtain ⟨E, -, hE⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hE
  have h1 : E.genericPoint ⤳ genericPoint X := specializes_iff_mem_closure.mpr hE
  have h2 : genericPoint X ⤳ E.genericPoint := (genericPoint_spec X).specializes trivial
  have heq : E.genericPoint = genericPoint X := (h1.antisymm h2).eq
  have hmax : Order.coheight (genericPoint X) = 0 :=
    Order.coheight_eq_zero.mpr fun b _ => (genericPoint_spec X).specializes trivial
  have := E.coheight_genericPoint
  rw [heq, hmax] at this
  exact zero_ne_one this

section Constancy

open MMP.Mori

/-- `f^♯` on sections followed by the germ at the generic point is the germ followed by the map of
function fields. -/
private theorem functionFieldMap_germToFunctionField {X T : Scheme.{0}} [IsIntegral X]
    [IsIntegral T] (h : T ⟶ X) [IsDominant h] {W : X.Opens} {W' : T.Opens} [Nonempty W]
    [Nonempty W'] (hle : W' ≤ h ⁻¹ᵁ W) (a : Γ(X, W)) :
    functionFieldMap h (X.germToFunctionField W a) =
      T.germToFunctionField W' (h.appLE W W' hle a) := by
  obtain ⟨⟨y, hy⟩⟩ := (inferInstance : Nonempty W')
  have hfy : h y ∈ W := hle hy
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) hfy,
    MMP.Mori.functionFieldMap_algebraMap_stalk,
    ← Scheme.algebraMap_germ_eq_germToFunctionField (X := T) hy]
  congr 1
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.germ_stalkMap, ← ConcreteCategory.comp_apply,
    Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]

/-- **Regular rational functions on a proper normal variety are constant**, in the form used
here: a nonzero rational function with no poles on a proper normal variety over an algebraically
closed field pulls back to a function with no zeros or poles along any dominant morphism. -/
private theorem ord_functionFieldMap_eq_zero {k : Type} [Field k] [IsAlgClosed k]
    {F T : Scheme.{0}} (sT : T ⟶ Spec (.of k)) [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    [IsProper sT] [IsIntegral F] [IsLocallyNoetherian F] [IsNormal F] (g : F ⟶ T) [IsDominant g]
    {φ : T.functionField} (hφ : φ ≠ 0)
    (h : ∀ P : MMP.Mori.PrimeDivisor T, 0 ≤ Scheme.ord φ P.genericPoint)
    (Q : MMP.Mori.PrimeDivisor F) : Scheme.ord (functionFieldMap g φ) Q.genericPoint = 0 := by
  haveI : Nonempty (⊤ : T.Opens) := ⟨⟨genericPoint T, trivial⟩⟩
  haveI : Nonempty (⊤ : F.Opens) := ⟨⟨genericPoint F, trivial⟩⟩
  have h0 := ord_eq_zero_of_forall_zero_le_ord sT hφ h
  have hφi : φ⁻¹ ≠ 0 := inv_ne_zero hφ
  have hinv : ∀ P : MMP.Mori.PrimeDivisor T, 0 ≤ Scheme.ord φ⁻¹ P.genericPoint := fun P => by
    rw [ord_inv_eq_neg hφ, h0 P, neg_zero]
  obtain ⟨r, hr⟩ := (MMP.Intersection.exists_germToFunctionField_eq_iff_forall_zero_le_ord
    (⊤ : T.Opens) hφ).2 fun P _ => h P
  obtain ⟨r', hr'⟩ := (MMP.Intersection.exists_germToFunctionField_eq_iff_forall_zero_le_ord
    (⊤ : T.Opens) hφi).2 fun P _ => hinv P
  have hmap : ∀ {ψ : T.functionField} (s : Γ(T, ⊤)), T.germToFunctionField ⊤ s = ψ →
      ∃ s' : Γ(F, ⊤), F.germToFunctionField ⊤ s' = functionFieldMap g ψ := fun s hs =>
    ⟨g.appLE ⊤ ⊤ le_top s, by
      rw [← hs, functionFieldMap_germToFunctionField (W := ⊤) (W' := ⊤) g le_top]⟩
  have hne : functionFieldMap g φ ≠ 0 := (map_ne_zero _).mpr hφ
  have hnei : functionFieldMap g φ⁻¹ ≠ 0 := (map_ne_zero _).mpr hφi
  have hQ : (Q.support ∩ ((⊤ : F.Opens) : Set F)).Nonempty :=
    ⟨Q.genericPoint, by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl, trivial⟩
  have h1 := (MMP.Intersection.exists_germToFunctionField_eq_iff_forall_zero_le_ord
    (⊤ : F.Opens) hne).1 (hmap r hr) Q hQ
  have h2 := (MMP.Intersection.exists_germToFunctionField_eq_iff_forall_zero_le_ord
    (⊤ : F.Opens) hnei).1 (hmap r' hr') Q hQ
  rw [map_inv₀, ord_inv_eq_neg hne] at h2
  omega

/-- In a line `L` with a basis, every vector is a multiple of a nonzero one. -/
private theorem exists_eq_smul_of_basis {K L : Type*} [Field K] [AddCommGroup L] [Module K L]
    (e : Module.Basis Unit K L) {a : L} (ha : a ≠ 0) (b : L) : ∃ c : K, b = c • a := by
  have ha' : a = e.repr a () • e () := (basis_unit_repr_smul e a).symm
  have hr : e.repr a () ≠ 0 := fun h0 => ha (by rw [ha', h0, zero_smul])
  refine ⟨e.repr b () / e.repr a (), ?_⟩
  calc b = e.repr b () • e () := (basis_unit_repr_smul e b).symm
    _ = (e.repr b () / e.repr a () * e.repr a ()) • e () := by rw [div_mul_cancel₀ _ hr]
    _ = (e.repr b () / e.repr a ()) • a := by rw [mul_smul, ← ha']

/-- Along a dominant `f : Y ⟶ X` with `f^* : k(X) ≅ k(Y)`, over a perfect field, the pull-back of
a nonzero rational `m`-canonical form is nonzero, and every rational `m`-canonical form on `Y` is
a multiple of it. -/
private theorem pullbackRationalPluriForms_ne_zero_and_exists_eq_smul {k : Type} [Field k]
    [PerfectField k] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] (f : Y ⟶ X) [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d) {m : ℤ}
    {τ : RationalPluriForms sX d m} (hτ : τ ≠ 0) (σ : RationalPluriForms (f ≫ sX) d m) :
    pullbackRationalPluriForms sX f τ ≠ 0 ∧
      ∃ c : Y.functionField, σ = c • pullbackRationalPluriForms sX f τ := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  obtain ⟨ω₀, hω₀⟩ := exists_isPullbackGenerator_of_bijective sX f hf hd
  let e := ZTensorPower.basis (basisOfSpanSingleton hω₀.2.1 hω₀.2.2) m
  have hr0 : e.repr (pullbackFormsAlong hω₀ m τ) () ≠ 0 := by
    change (ZTensorPower.basis (basisOfSpanSingleton hω₀.2.1 hω₀.2.2) m).repr
      (pullbackFormsAlong hω₀ m τ) () ≠ 0
    rw [repr_pullbackFormsAlong hω₀ m τ]
    exact (map_ne_zero _).mpr (repr_ne_zero_of_ne_zero _ hτ)
  have hne : pullbackFormsAlong hω₀ m τ ≠ 0 := fun h0 => hr0 (by rw [h0]; simp)
  rw [show pullbackRationalPluriForms sX f τ = pullbackFormsAlong hω₀ m τ from
    pullbackForms_eq hω₀ m τ]
  exact ⟨hne, exists_eq_smul_of_basis e hne σ⟩

/-- **Coefficients of a pull-back where the morphism is a local isomorphism.** If the stalk map
of `f` at the generic point of `H` is an isomorphism and `f(η_H) = η_P`, then
`coeff_H(f^*C) = coeff_P(C)`. -/
private theorem coeff_isPullback_eq_of_isIso {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {f : Y ⟶ X} [IsDominant f] {C : Divisor X} (hCc : C.IsCartier)
    {hC : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ C.supp}
    {C' : Divisor Y} (h : C.IsPullback f hC C') (H : MMP.Mori.PrimeDivisor Y)
    (P : MMP.Mori.PrimeDivisor X) (hHP : f H.genericPoint = P.genericPoint)
    [IsIso (f.stalkMap H.genericPoint)] : C'.coeff H = C.coeff P := by
  obtain ⟨V, hV, φ, hφ⟩ := hCc (f H.genericPoint)
  rw [MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF h hφ H hV P.component,
    MMP.Positivity.ord_functionFieldMap_of_isIso f H P hHP,
    ← MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord,
    hφ P ⟨P.genericPoint, MMP.Positivity.PrimeDivisor.genericPoint_mem_support' P, hHP ▸ hV⟩]

/-- The same for `ℚ`-divisors. -/
private theorem qcoeff_isPullback_eq_of_isIso {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {f : Y ⟶ X} [IsDominant f] {C : QDivisor X} (hCq : C.IsQCartier)
    {hC : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ C.supp}
    {C' : QDivisor Y} (h : C.IsPullback f hC C') (H : MMP.Mori.PrimeDivisor Y)
    (P : MMP.Mori.PrimeDivisor X) (hHP : f H.genericPoint = P.genericPoint)
    [IsIso (f.stalkMap H.genericPoint)] : C'.coeff H = C.coeff P := by
  obtain ⟨m, hm, D, hD, hDc⟩ := hCq.exists_pos
  obtain ⟨D', hD', hp⟩ := h m hm D hD hDc
  have h1 := coeff_isPullback_eq_of_isIso hDc hp H P hHP
  have e1 := congrArg (fun G : QDivisor Y => G.coeff H) hD'
  have e2 := congrArg (fun G : QDivisor X => G.coeff P) hD
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at e1 e2
  rw [h1] at e1
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  apply mul_left_cancel₀ hmq
  push_cast at e1 e2
  rw [← e1, e2]

/-- **Crepancy from a restricted identity.** Let `g : F ⟶ T` be a proper birational morphism of
normal varieties, `T` proper over an algebraically closed field, and `σ_T`, `σ_F` nonzero top
forms with `div σ_F + C_F = g^*(div σ_T + B_T)`. If `C_F(Q) ≤ B_T(Q_T)` whenever `Q` is the strict
transform of `Q_T`, then `div σ_F = div g^*σ_T`: the ratio `σ_F / g^*σ_T` is the pull-back of a
rational function on `T` with order `B_T(Q_T) - C_F(Q) ≥ 0` along every `Q_T`, hence constant. -/
private theorem divisorOfForm_eq_of_isPullback_of_le {k : Type} [Field k] [IsAlgClosed k]
    {F T : Scheme.{0}} (sT : T ⟶ Spec (.of k)) [IsIntegral T] [IsLocallyNoetherian T]
    [IsNormal T] [CompactSpace T] [LocallyOfFiniteType sT] [IsProper sT] [IsIntegral F]
    [IsLocallyNoetherian F] [IsNormal F] [CompactSpace F] (g : F ⟶ T) [IsProper g]
    [IsDominant g] (hg : IsBirationalMorphism g) {d : ℕ} (hdT : topologicalKrullDim T = d)
    (σT : RationalPluriForms sT d 1) (hσT : σT ≠ 0) (σF : RationalPluriForms (g ≫ sT) d 1)
    (hσF : σF ≠ 0) (BT : QDivisor T) (CF : QDivisor F)
    (hQT : (Divisor.toQDivisor (divisorOfForm σT) + BT).IsQCartier)
    {hgen : ∀ Z : irreducibleComponents F, g (componentGenericPoint F Z) ∉
      (Divisor.toQDivisor (divisorOfForm σT) + BT).supp}
    (hpb : (Divisor.toQDivisor (divisorOfForm σT) + BT).IsPullback g hgen
      (Divisor.toQDivisor (divisorOfForm σF) + CF))
    (hle : ∀ (QT : MMP.Mori.PrimeDivisor T) (Q : MMP.Mori.PrimeDivisor F),
      g Q.genericPoint = QT.genericPoint → CF.coeff Q ≤ BT.coeff QT) :
    divisorOfForm σF = divisorOfForm (pullbackRationalPluriForms sT g σT) := by
  have hbij := hg.functionFieldMap_bijective
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sT) hdT
  obtain ⟨hτ0, r, hr⟩ := pullbackRationalPluriForms_ne_zero_and_exists_eq_smul sT g hbij hd hσT σF
  set τ := pullbackRationalPluriForms sT g σT with hτ
  have hr0 : r ≠ 0 := by rintro rfl; rw [zero_smul] at hr; exact hσF hr
  have hdF : (letI := functionFieldAlgebra (g ≫ sT)
      (Algebra.trdeg k F.functionField).toNat = d) := by
    rw [← trdeg_functionField_eq_of_bijective sT g hbij]; exact hd
  -- the ratio comes from `T`
  obtain ⟨rT, hrT⟩ := hbij.2 r
  have hrT0 : rT ≠ 0 := by rintro rfl; rw [map_zero] at hrT; exact hr0 hrT.symm
  have hord : ∀ Q : MMP.Mori.PrimeDivisor F, Scheme.ord r Q.genericPoint = 0 := by
    intro Q
    rw [← hrT]
    refine ord_functionFieldMap_eq_zero sT g hrT0 (fun QT => ?_) Q
    have hreg := MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal g hg
      (y := QT.genericPoint) (by rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint])
    obtain ⟨Q', -, hQ'⟩ := MMP.Flips.exists_inverseTransformPrimeDivisor_eq_some QT hreg
    haveI := MMP.isIso_stalkMap_of_mem_biregularLocus g (x := Q'.genericPoint) (hQ' ▸ hreg)
    rw [← MMP.Positivity.ord_functionFieldMap_of_isIso g Q' QT hQ' rT, hrT]
    have h1 := MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso g hbij hd Q' QT hQ' σT
    have h2 := qcoeff_isPullback_eq_of_isIso hQT hpb Q' QT hQ'
    have h3 := hle QT Q' hQ'
    have h4 := Q'.ordForm_smul hdF hr0 hτ0
    rw [← hr] at h4
    simp only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_divisorOfForm] at h2
    rw [← hτ] at h1
    rw [h4, h1] at h2
    have : ((Scheme.ord r Q'.genericPoint : ℤ) : ℚ) = BT.coeff QT - CF.coeff Q' := by
      push_cast at h2; linarith
    have h5 : (0 : ℚ) ≤ ((Scheme.ord r Q'.genericPoint : ℤ) : ℚ) := by rw [this]; linarith
    exact_mod_cast h5
  ext Q
  rw [coeff_divisorOfForm, coeff_divisorOfForm, hr, Q.ordForm_smul hdF hr0 hτ0, hord Q, zero_add]

/-- A birational morphism of integral schemes of finite type over `k` preserves dimension. -/
private lemma topologicalKrullDim_eq_of_isBirationalMorphism {k : Type} [Field k]
    {F T : Scheme.{0}} [IsIntegral F] [IsIntegral T] (sT : T ⟶ Spec (.of k))
    [LocallyOfFiniteType sT] (g : F ⟶ T) [IsDominant g] [LocallyOfFiniteType (g ≫ sT)]
    (hg : IsBirationalMorphism g) {d : ℕ} (hd : topologicalKrullDim T = d) :
    topologicalKrullDim F = d := by
  rw [MMP.Fourfold.topologicalKrullDim_eq_toNat_trdeg (g ≫ sT),
    ← trdeg_functionField_eq_of_bijective sT g hg.functionFieldMap_bijective,
    toNat_trdeg_functionField_of_topologicalKrullDim_eq hd]

/-- Every nonzero rational `1`-canonical form is a nonzero rational top form. -/
private theorem exists_toPluriForms_eq {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    {sX : X ⟶ Spec (.of k)} {n : ℕ} {τ : RationalPluriForms sX n 1} (hτ : τ ≠ 0) :
    ∃ ω : RationalTopForms sX n, ω ≠ 0 ∧ ω.toPluriForms sX = τ := by
  letI := functionFieldAlgebra sX
  have hω : RationalTopForms.toPluriForms sX (PiTensorProduct.subsingletonEquiv
      (R := X.functionField) (s := fun _ : Fin 1 => ⋀[X.functionField]^n Ω[X.functionField⁄k])
      0 τ : RationalTopForms sX n) = τ := by
    change PiTensorProduct.tprod X.functionField (fun _ : Fin 1 => PiTensorProduct.subsingletonEquiv
      (R := X.functionField) (s := fun _ : Fin 1 => ⋀[X.functionField]^n Ω[X.functionField⁄k])
      0 τ) = τ
    rw [← PiTensorProduct.subsingletonEquiv_symm_apply' (i₀ := (0 : Fin 1))]
    exact LinearEquiv.symm_apply_apply _ _
  refine ⟨_, fun h0 => hτ ?_, hω⟩
  rw [← hω, h0]
  change PiTensorProduct.tprod X.functionField (fun _ : Fin 1 =>
    (0 : ⋀[X.functionField]^n Ω[X.functionField⁄k])) = 0
  exact MultilinearMap.map_coord_zero _ (0 : Fin 1) rfl

/-- A point whose image lies off the support of a `ℚ`-Cartier `ℚ`-divisor lies off the support
of its pull-back. -/
private lemma notMem_supp_of_isPullback {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} {D : QDivisor Y} (hDq : D.IsQCartier)
    {hD : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ D.supp}
    {D' : QDivisor X} (h : D.IsPullback f hD D') {y : X} (hy : f y ∉ D.supp) : y ∉ D'.supp := by
  intro hmem
  obtain ⟨E, hE0, hyE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
  apply hE0
  refine qdivisor_coeff_eq_zero_of_isPullback hDq h E fun hEm => hy ?_
  have hsp : E.genericPoint ⤳ y := by
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hyE
  exact (f.base.hom.map_specializes hsp).mem_closed D.supp.isClosed hEm

end Constancy

/-! ### The three steps -/

/-- **The image of a floor stratum is a floor stratum.** The valuation of a proper floor stratum
`W` of `(Y, C)` (of `W` itself if it is a divisor, of the exceptional divisor of the blow-up of
`W` otherwise) has log discrepancy zero over `(Y, C)`, hence over `(X, B)` by crepancy; on an snc
subboundary the centres of such valuations are exactly the floor strata. -/
private theorem isSNCStratum_image {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {B : QDivisor X} {C : QDivisor Y} (hB : IsSNCSubboundaryPair sX B)
    (hC : IsSNCSubboundaryPair sY C) {n : ℕ} {KX : Divisor X} (hKX : KX.IsCanonicalDivisor sX n)
    {KY : Divisor Y} (hKY : KY.IsCanonicalDivisor sY n)
    (h : Y ⟶ X) (hh : h ≫ sX = sY) (hproj : IsProjectiveMorphism h)
    (hbir : IsBirationalMorphism h)
    (hcrep : ∀ hY : IsNormalVariety k (h ≫ sX), IsCrepantBoundary sX n KX B h hY hbir C)
    {W : Scheme.{0}} (ιW : W ⟶ Y) [IsClosedImmersion ιW] [IsReduced W]
    (hW : IsSNCStratum (coeffOnePart C) (Set.range ιW.base))
    (hW' : Set.range ιW.base ≠ Set.univ) :
    IsSNCStratum (coeffOnePart B) (h.base '' Set.range ιW.base) := by
  classical
  subst hh
  have hsncC : (coeffOnePart C).IsSNC (h ≫ sX) :=
    hC.isSNC.of_support_subset (support_coeffOnePart_subset C)
  obtain ⟨J, hJ, hmax⟩ := hW
  obtain ⟨w, hWw, hwJ, hcw⟩ := coheight_eq_card_of_isSNCStratum hsncC hJ hmax
  have hX : IsNormalVariety k sX := ⟨hB.isProjectiveVariety.toIsVariety, inferInstance⟩
  have hY : IsNormalVariety k (h ≫ sX) := ⟨hC.isProjectiveVariety.toIsVariety, inferInstance⟩
  have hP : MMP.Mori.IsPair sX B :=
    ⟨hX, n, KX, hKX, isQCartier_of_isSmoothScheme hB.isSmoothScheme _⟩
  -- a divisor over `X` of discrepancy `-1` with centre `h(w)`
  obtain ⟨D, hDc, hD⟩ : ∃ D : DivisorOver k sX, D.f D.E.genericPoint = h w ∧
      IsDiscrepancy sX n KX B D (-1) := by
    rcases Nat.lt_or_ge J.card 2 with hJ2 | hJ2
    · rcases Nat.lt_or_ge J.card 1 with hJ1 | hJ1
      · -- `J = ∅`: the stratum is all of `Y`
        exfalso
        have hJe : J = ∅ := Finset.card_eq_zero.mp (Nat.lt_one_iff.mp hJ1)
        subst hJe
        apply hW'
        refine hmax.eq_of_ge ⟨IrreducibleSpace.isIrreducible_univ Y, by simp⟩
          (Set.subset_univ _) |>.symm
      · -- `J = {G}`: the stratum is the prime divisor `G`
        obtain ⟨G, rfl⟩ := Finset.card_eq_one.mp (le_antisymm (Nat.lt_succ_iff.mp hJ2) hJ1)
        have hWG : Set.range ιW.base = G.support := by
          refine (hmax.eq_of_ge ⟨?_, by simp⟩ ?_).symm
          · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
            exact isIrreducible_singleton.closure
          · simpa using hmax.1.2
        have hwG : w = G.genericPoint := by
          have h1 : IsGenericPoint w (G.support) := by
            rw [← hWG, hWw]; exact isGenericPoint_closure
          have h2 : IsGenericPoint G.genericPoint (G.support) := by
            rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isGenericPoint_closure
          exact h1.eq h2
        refine ⟨⟨Y, h, hY, hbir, G⟩, by rw [hwG], ?_⟩
        have := hcrep hY G
        rwa [coeff_eq_one_of_mem_support_coeffOnePart (hJ (Finset.mem_singleton_self G))]
          at this
    · obtain ⟨E, hEc, -, hE⟩ :=
        exists_isDiscrepancy_eq_neg_one_of_coheight_eq_card hC hKY hJ hwJ hcw hJ2
      refine ⟨compDivisorOver h hY hbir E, by rw [← hEc]; rfl, ?_⟩
      haveI : IsDominant h := hbir.isDominant
      exact ((MMP.Mori.IsPair.isDiscrepancy_iff_of_crepant hP h hY hbir hKX hKY
        (Or.inl (hcrep hY))).2 E _ (valuation_compDivisorOver h hY hbir E) (-1)).mp hE
  -- the image of `closure {w}` is `closure {h w}`
  haveI := isProper_of_isProjectiveMorphism h hproj
  have himg : h.base '' Set.range ιW.base = closure {D.f D.E.genericPoint} := by
    rw [hWw, hDc, ← h.isClosedMap.closure_image_eq_of_continuous h.continuous, Set.image_singleton]
  rw [himg]
  exact isSNCStratum_closure_of_isDiscrepancy_eq_neg_one hB hKX D hD

open scoped Classical in
/-- **Primes over a boundary component.** For a crepant projective birational morphism
`h : (Y, C) ⟶ (X, B)` of snc subboundary pairs, a prime divisor `G` of `Y` whose generic point
maps into a component `E` of `B` has `C_G ≤ B_E`: if `G` is exceptional, the snc lower bound at its
centre on `E` gives `-C_G = a(G, X, B) ≥ -B_E`; otherwise `G` is the strict transform of `E`. -/
private theorem coeff_le_of_map_genericPoint_mem {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {B : QDivisor X} {C : QDivisor Y} (hB : IsSNCSubboundaryPair sX B)
    (h : Y ⟶ X) (hC : IsSNCSubboundaryPair (h ≫ sX) C) {n : ℕ} {KX : Divisor X}
    (hKX : KX.IsCanonicalDivisor sX n) (hbir : IsBirationalMorphism h)
    (hcrep : ∀ hY : IsNormalVariety k (h ≫ sX), IsCrepantBoundary sX n KX B h hY hbir C)
    {E : MMP.Mori.PrimeDivisor X} (hE : E ∈ B.support) (G : MMP.Mori.PrimeDivisor Y)
    (hG : h G.genericPoint ∈ E.support) : C.coeff G ≤ B.coeff E := by
  have hX : IsNormalVariety k sX := ⟨hB.isProjectiveVariety.toIsVariety, inferInstance⟩
  have hY : IsNormalVariety k (h ≫ sX) := ⟨hC.isProjectiveVariety.toIsVariety, inferInstance⟩
  have hd := hcrep hY G
  by_cases hex : (⟨Y, h, hY, hbir, G⟩ : DivisorOver k sX).IsExceptional
  · have hsnc := isSNC_sum_single hB.isSNC subset_rfl
    obtain ⟨c, T, -, hT, -, hcard, -, -, hle⟩ := MMP.Mori.le_isDiscrepancy_of_isSNC hX
      hB.isSmoothScheme hKX subset_rfl hsnc (fun E _ => hB.coeff_le_one E) _ hex hd
    have hET : E ∈ T := by rw [hT]; exact Finset.mem_filter.mpr ⟨hE, hG⟩
    have h1 : 1 - B.coeff E ≤ ∑ G ∈ T, (1 - B.coeff G) :=
      Finset.single_le_sum (f := fun G => 1 - B.coeff G)
        (fun G _ => sub_nonneg.2 (hB.coeff_le_one G)) hET
    have h2 : (0 : ℚ) ≤ (c : ℚ) - T.card := sub_nonneg.2 (by exact_mod_cast hcard)
    linarith
  · obtain ⟨P, hcen, hP⟩ := MMP.Mori.DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff
      ⟨hX, hKX, isQCartier_of_isSmoothScheme hB.isSmoothScheme _⟩ _ hex
    have hcl : closure {h G.genericPoint} = (P.support : Set X) := by
      rw [← hcen, MMP.Positivity.DivisorOver.center_eq_closureSingleton]
      rfl
    have hPE : E = P := MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support (by
      have : P.genericPoint ∈ closure {h G.genericPoint} := by
        rw [hcl]; exact MMP.Positivity.PrimeDivisor.genericPoint_mem_support' P
      exact closure_minimal (Set.singleton_subset_iff.mpr hG) E.idealSheaf.support.isClosed this)
    subst hPE
    have := hd.eq hP
    linarith

/-- **Further components through the image are effective.** In the situation of
`sum_coeff_le_of_crepant`, if no further component of `C` passes through `q`, every further
component `E` of `B` through `h(q)` has `B_E ≥ 0`: some prime `G` of `Y` through `q` lies over `E`
(the support of `h^*E` is `h⁻¹ E`), and `C_G ≤ B_E` with `C_G ≠ 0` would put `G` among the
components of `C` through `q`. -/
private theorem coeff_nonneg_of_forall_notMem {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {B : QDivisor X} {C : QDivisor Y} (hB : IsSNCSubboundaryPair sX B)
    (h : Y ⟶ X) (hC : IsSNCSubboundaryPair (h ≫ sX) C) {n : ℕ} {KX : Divisor X}
    (hKX : KX.IsCanonicalDivisor sX n) (hbir : IsBirationalMorphism h)
    (hcrep : ∀ hY : IsNormalVariety k (h ≫ sX), IsCrepantBoundary sX n KX B h hY hbir C)
    {q : Y} (hq : ∀ G ∈ C.support, q ∈ G.support → C.coeff G = 1)
    {E : MMP.Mori.PrimeDivisor X} (hE : E ∈ B.support) (hqE : h q ∈ E.support) :
    0 ≤ B.coeff E := by
  classical
  by_contra hneg
  replace hneg := not_le.mp hneg
  haveI : CompactSpace Y := haveI := hC.isProjectiveVariety.toIsVariety.toQuasiCompact
    QuasiCompact.compactSpace_of_compactSpace (h ≫ sX)
  haveI : IsDominant h := hbir.isDominant
  set D : Divisor X := Finsupp.single E (1 : ℤ) with hD
  have hDc : D.IsCartier := isCartier_of_isSmoothScheme hB.isSmoothScheme D
  have hDe : DivisorWithCoeffs.IsEffective D := fun G => by
    change 0 ≤ (Finsupp.single E (1 : ℤ)) G
    rw [Finsupp.single_apply]; split_ifs <;> norm_num
  have hgen : ∀ Z : irreducibleComponents Y, h (componentGenericPoint Y Z) ∉ D.supp := fun Z => by
    rw [componentGenericPoint_eq_genericPoint, map_genericPoint_of_isDominant h]
    exact genericPoint_notMem_supp D
  obtain ⟨D', hD'⟩ := hDc.exists_isPullback hgen
  have hqD : h q ∈ (D.supp : Set X) :=
    DivisorWithCoeffs.support_subset_supp (by
      change (Finsupp.single E (1 : ℤ)) E ≠ 0; simp) hqE
  obtain ⟨G, hG0, hqG⟩ := DivisorWithCoeffs.mem_supp_iff.mp
    (MMP.Flips.preimage_supp_subset_supp_of_isPullback hDc hDe hD' hqD)
  have hGE : h G.genericPoint ∈ E.support := by
    by_contra hn
    exact hG0 (divisor_coeff_eq_zero_of_isPullback hDc hD' G
      (fun hm => hn (DivisorWithCoeffs.supp_single_le E (1 : ℤ) hm)))
  have hle := coeff_le_of_map_genericPoint_mem hB h hC hKX hbir hcrep hE G hGE
  have hGC : G ∈ C.support := Finsupp.mem_support_iff.mpr (by
    change C.coeff G ≠ 0; intro h0; linarith)
  have := hq G hGC hqG
  linarith [hB.coeff_le_one E]

open scoped Classical in
/-- **Restricted boundaries under a crepant morphism.** Let `h : (Y, C) ⟶ (X, B)` be crepant, with
snc subboundaries and `B` effective, `q ∈ Y` a point of codimension `|J_Y| + 1` on components
`J_Y` of `C^{=1}`, and `h(q)` of codimension `|J_X| + 1` on components `J_X` of `B^{=1}`. Then the
sum of the coefficients of the further components of `C` through `q` is at most that of the
further components of `B` through `h(q)`. If a further component `H` of `C` with `C_H > 0` passes
through `q`, the exceptional divisor of the blow-up of `closure {q}` has discrepancy `-C_H` over
`(Y, C)`, hence over `(X, B)`, and the snc bound at `h(q)` gives `-C_H ≥ -∑ B_E`. -/
private theorem sum_coeff_le_of_crepant {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {B : QDivisor X} {C : QDivisor Y} (hB : IsSNCSubboundaryPair sX B)
    (h : Y ⟶ X) (hC : IsSNCSubboundaryPair (h ≫ sX) C) {n : ℕ} {KX : Divisor X}
    (hKX : KX.IsCanonicalDivisor sX n) {KY : Divisor Y} (hKY : KY.IsCanonicalDivisor (h ≫ sX) n)
    (hbir : IsBirationalMorphism h)
    (hcrep : ∀ hY : IsNormalVariety k (h ≫ sX), IsCrepantBoundary sX n KX B h hY hbir C)
    {JY : Finset (MMP.Mori.PrimeDivisor Y)} (hJY : JY ⊆ C.support)
    (hJY1 : ∀ G ∈ JY, C.coeff G = 1) (hJYc : 1 ≤ JY.card) {q : Y}
    (hqJ : ∀ G ∈ JY, q ∈ G.support) (hcq : Order.coheight q = JY.card + 1)
    {JX : Finset (MMP.Mori.PrimeDivisor X)} (hJX : JX ⊆ B.support)
    (hJX1 : ∀ G ∈ JX, B.coeff G = 1) (hpJ : ∀ G ∈ JX, h q ∈ G.support)
    (hcp : Order.coheight (h q) = JX.card + 1) (hJXc : 1 ≤ JX.card) :
    ∑ E ∈ C.support.filter (fun E => E ∉ JY ∧ q ∈ E.support), C.coeff E ≤
      ∑ E ∈ B.support.filter (fun E => E ∉ JX ∧ h q ∈ E.support), B.coeff E := by
  set FlY := C.support.filter (fun E => E ∉ JY ∧ q ∈ E.support) with hFlY
  set FlX := B.support.filter (fun E => E ∉ JX ∧ h q ∈ E.support) with hFlX
  have hdisjY : Disjoint FlY JY :=
    Finset.disjoint_left.mpr fun G hG hGJ => (Finset.mem_filter.mp hG).2.1 hGJ
  have hFlYc : FlY.card ≤ 1 := by
    obtain ⟨c, hc, hcard⟩ := card_le_coheight_of_isSNC hC.isSNC q (FlY ∪ JY)
      (Finset.union_subset (Finset.filter_subset _ _) hJY) (fun G hG => by
        rcases Finset.mem_union.mp hG with hG | hG
        · exact (Finset.mem_filter.mp hG).2.2
        · exact hqJ G hG)
    rw [hcq] at hc
    have hc' : c = JY.card + 1 := by exact_mod_cast hc.symm
    rw [Finset.card_union_of_disjoint hdisjY] at hcard
    omega
  by_cases hFlY0 : FlY = ∅
  · rw [hFlY0, Finset.sum_empty]
    refine Finset.sum_nonneg fun E hEF => ?_
    obtain ⟨hEB, -, hqE⟩ := Finset.mem_filter.mp hEF
    refine coeff_nonneg_of_forall_notMem hB h hC hKX hbir hcrep (fun G hGC hqG => ?_) hEB hqE
    by_cases hGJ : G ∈ JY
    · exact hJY1 G hGJ
    · have : G ∈ FlY := Finset.mem_filter.mpr ⟨hGC, hGJ, hqG⟩
      rw [hFlY0] at this; exact absurd this (Finset.notMem_empty _)
  obtain ⟨H, hFlYH⟩ : ∃ H, FlY = {H} := Finset.card_eq_one.mp
    (le_antisymm hFlYc (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hFlY0)))
  rw [hFlYH, Finset.sum_singleton]
  obtain ⟨hHC, hHJ, hqH⟩ := Finset.mem_filter.mp (hFlYH ▸ Finset.mem_singleton_self H)
  -- the blow-up of the stratum through `q` cut out by `J_Y ∪ {H}`
  set T := insert H JY with hT
  have hTC : T ⊆ C.support := Finset.insert_subset hHC hJY
  have hqT : ∀ G ∈ T, q ∈ G.support := fun G hG => by
    rcases Finset.mem_insert.mp hG with rfl | hG
    · exact hqH
    · exact hqJ G hG
  have hTc : T.card = JY.card + 1 := Finset.card_insert_of_notMem hHJ
  have hcqT : Order.coheight q = T.card := by rw [hTc, hcq]; push_cast; rfl
  obtain ⟨μ, hμc, -, hμ⟩ := exists_isDiscrepancy_of_coheight_eq_card hC hKY hTC hqT hcqT
    (by omega)
  have hval : (T.card : ℚ) - 1 - ∑ G ∈ T, C.coeff G = -C.coeff H := by
    rw [hT, Finset.sum_insert hHJ, Finset.sum_congr rfl hJY1, Finset.sum_const, hTc]
    simp only [nsmul_eq_mul, mul_one]
    push_cast
    ring
  rw [hval] at hμ
  -- transfer to `(X, B)`
  have hX : IsNormalVariety k sX := ⟨hB.isProjectiveVariety.toIsVariety, inferInstance⟩
  have hY : IsNormalVariety k (h ≫ sX) := ⟨hC.isProjectiveVariety.toIsVariety, inferInstance⟩
  have hP : MMP.Mori.IsPair sX B :=
    ⟨hX, n, KX, hKX, isQCartier_of_isSmoothScheme hB.isSmoothScheme _⟩
  haveI : IsDominant h := hbir.isDominant
  have hμX := ((MMP.Mori.IsPair.isDiscrepancy_iff_of_crepant hP h hY hbir hKX hKY
    (Or.inl (hcrep hY))).2 μ _ (valuation_compDivisorOver h hY hbir μ) _).mp hμ
  set μX := compDivisorOver h hY hbir μ with hμXdef
  have hcen : μX.f μX.E.genericPoint = h q := by rw [← hμc]; rfl
  have hexc : μX.IsExceptional := (isExceptional_iff_two_le_coheight hX μX).mpr (by
    rw [hcen, hcp]; exact_mod_cast (by omega : 2 ≤ JX.card + 1))
  have hsnc := isSNC_sum_single hB.isSNC subset_rfl
  obtain ⟨c, T', hc, hT', -, -, -, -, hle⟩ := MMP.Mori.le_isDiscrepancy_of_isSNC hX
    hB.isSmoothScheme hKX subset_rfl hsnc (fun E _ => hB.coeff_le_one E) μX hexc hμX
  subst hT'
  rw [hcen] at hc hle
  rw [hcp] at hc
  have hc' : c = JX.card + 1 := by exact_mod_cast hc
  -- the components of `B` through `h q`: `J_X` and the further ones
  have hsplit : B.support.filter (fun G => h q ∈ G.support) = JX ∪ FlX := by
    ext G
    simp only [Finset.mem_filter, Finset.mem_union, hFlX]
    constructor
    · rintro ⟨hG, hqG⟩
      by_cases hGJ : G ∈ JX
      · exact Or.inl hGJ
      · exact Or.inr ⟨hG, hGJ, hqG⟩
    · rintro (hGJ | ⟨hG, -, hqG⟩)
      · exact ⟨hJX hGJ, hpJ G hGJ⟩
      · exact ⟨hG, hqG⟩
  have hdisjX : Disjoint JX FlX :=
    Finset.disjoint_left.mpr fun G hGJ hG => (Finset.mem_filter.mp hG).2.1 hGJ
  rw [hsplit, Finset.sum_union hdisjX, Finset.card_union_of_disjoint hdisjX,
    Finset.sum_eq_zero (fun G hG => by rw [hJX1 G hG, sub_self]), zero_add, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul, mul_one, hc'] at hle
  push_cast at hle
  linarith

/-! ### Restriction of sections along strata -/

/-- **Restriction is bijective when both pull-backs from the base are.** For `j : F ⟶ W`,
`q : W ⟶ Z` and an `𝒪_Z`-module `N`, if pulling back global sections of `N` along `q` and along
`j ≫ q` is bijective, then restricting global sections of `q^* N` from `W` to `F` is bijective:
the composite of the two units is the unit of `j ≫ q`, up to the isomorphism
`(j ≫ q)^* ≅ j^* q^*`. -/
private lemma bijective_unit_app_top_of_comp {F W Z : Scheme.{0}} (j : F ⟶ W) (q : W ⟶ Z)
    (N : Z.Modules)
    (hq : Function.Bijective (((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app N).app ⊤))
    (hg : Function.Bijective
      (((Scheme.Modules.pullbackPushforwardAdjunction (j ≫ q)).unit.app N).app ⊤)) :
    Function.Bijective (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
      ((Scheme.Modules.pullback q).obj N)).app ⊤) := by
  have h2 := unit_conjugateEquiv ((Scheme.Modules.pullbackPushforwardAdjunction q).comp
    (Scheme.Modules.pullbackPushforwardAdjunction j))
    (Scheme.Modules.pullbackPushforwardAdjunction (j ≫ q)) (Scheme.Modules.pullbackComp j q).inv N
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h2
  have key : ∀ x, (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
      ((Scheme.Modules.pullback q).obj N)).app ⊤)
        (((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app N).app ⊤ x) =
      (((Scheme.Modules.pullbackComp j q).inv.app N).app ⊤)
        (((Scheme.Modules.pullbackPushforwardAdjunction (j ≫ q)).unit.app N).app ⊤ x) := by
    intro x
    exact congrArg (fun φ => (Scheme.Modules.Hom.app φ ⊤) x) h2
  have hα : Function.Bijective (((Scheme.Modules.pullbackComp j q).inv.app N).app ⊤) :=
    ConcreteCategory.bijective_of_isIso _
  have hc := hα.comp hg
  have heq : (((Scheme.Modules.pullbackComp j q).inv.app N).app ⊤) ∘
      (((Scheme.Modules.pullbackPushforwardAdjunction (j ≫ q)).unit.app N).app ⊤) =
      (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
      ((Scheme.Modules.pullback q).obj N)).app ⊤) ∘
        (((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app N).app ⊤) :=
    funext fun x => (key x).symm
  rw [heq] at hc
  exact (Function.Bijective.of_comp_iff _ hq).mp hc

/-- Bijectivity of restriction of global sections along `j` is invariant under isomorphism of
the module, by naturality of the unit. -/
private lemma bijective_unit_app_top_of_iso {F W : Scheme.{0}} (j : F ⟶ W) {M M' : W.Modules}
    (e : M ≅ M')
    (h : Function.Bijective
      (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M').app ⊤)) :
    Function.Bijective (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M).app ⊤) := by
  have hn := (Scheme.Modules.pullbackPushforwardAdjunction j).unit.naturality e.hom
  have key : ∀ x, ((Scheme.Modules.pushforward j).map ((Scheme.Modules.pullback j).map e.hom)).app ⊤
      (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M).app ⊤ x) =
      ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M').app ⊤ (e.hom.app ⊤ x) :=
    fun x => (congrArg (fun φ => (Scheme.Modules.Hom.app φ ⊤) x) hn).symm
  have h1 : Function.Bijective (e.hom.app ⊤) := ConcreteCategory.bijective_of_isIso _
  have h2 : Function.Bijective (((Scheme.Modules.pushforward j).map
      ((Scheme.Modules.pullback j).map e.hom)).app ⊤) := ConcreteCategory.bijective_of_isIso _
  have hc := h.comp h1
  have heq : (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M').app ⊤) ∘
      (e.hom.app ⊤) =
      (((Scheme.Modules.pushforward j).map ((Scheme.Modules.pullback j).map e.hom)).app ⊤) ∘
        (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M).app ⊤) :=
    funext fun x => (key x).symm
  rw [heq] at hc
  exact (Function.Bijective.of_comp_iff' h2 _).mp hc

/-- If `𝒪_Z ⟶ q_* 𝒪_W` is an isomorphism, pulling back global sections of an invertible
`𝒪_Z`-module along `q` is bijective. -/
private lemma bijective_unit_app_top_of_isIso_c {W Z : Scheme.{0}} (q : W ⟶ Z) [IsIso q.c]
    (N : Z.Modules) [Stacks.Ample.IsInvertibleModule Z N] :
    Function.Bijective (((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app N).app ⊤) := by
  haveI := Scheme.Modules.isIso_unit_app_of_isIso_c q N
  exact ConcreteCategory.bijective_of_isIso _

/-- **Stein factorization through a birational substratum.** Let `q : W ⟶ Z` be a proper dominant
morphism of integral schemes with `Z` normal, and `j : F ⟶ W` a morphism from an integral scheme
with `j ≫ q` birational. Then `𝒪_Z ⟶ q_* 𝒪_W` is an isomorphism: over the generic point `η` of
`Z` the global functions of the fibre `W_η` form a field, finite over `κ(η)`, which maps to the
global functions `κ(η)` of the fibre `F_η`; so it is `κ(η)`, and the normal base forces the Stein
factorization of `q` to be trivial. -/
private lemma isIso_c_of_isBirational_comp {F W Z : Scheme.{0}} [IsIntegral F] [IsIntegral W]
    [IsIntegral Z] [IsNormal Z] (j : F ⟶ W) (q : W ⟶ Z) [IsProper q] [IsDominant q]
    (hb : IsBirational (j ≫ q)) : IsIso q.c := by
  set η := genericPoint Z
  have hF : IsIso ((j ≫ q).fiberToSpecResidueField η) :=
    isIso_fiberToSpecResidueField_genericPoint_of_isBirational _ hb
  let m : (j ≫ q).fiber η ⟶ q.fiber η :=
    IsPullback.lift (IsPullback.of_hasPullback q (Z.fromSpecResidueField η))
      ((j ≫ q).fiberι η ≫ j) ((j ≫ q).fiberToSpecResidueField η) (by
      rw [Category.assoc, Scheme.Hom.fiber_fac])
  have hm : m ≫ q.fiberToSpecResidueField η = (j ≫ q).fiberToSpecResidueField η :=
    IsPullback.lift_snd _ _ _ _
  haveI : IsProper (q.fiberToSpecResidueField η) := by
    have key : ∀ {Y : Scheme.{0}} (g : Y ⟶ Z), IsProper (Limits.pullback.snd q g) :=
      fun g => inferInstance
    exact key (Z.fromSpecResidueField η)
  have hfield : IsField Γ(q.fiber η, ⊤) :=
    Scheme.isField_globalSections_of_isProper (k := Z.residueField η) (q.fiberToSpecResidueField η)
  have hgen : ∀ x : W, x ∈ genericPoints W → q x = genericPoint Z := by
    intro x hx
    rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
    rw [hx]; exact map_genericPoint_of_isDominant q
  refine Stacks.SteinFactorization.isIso_c_of_isNormal q hgen ?_
  set φW := (Scheme.ΓSpecIso (Z.residueField η)).inv ≫ (q.fiberToSpecResidueField η).appTop
  have hφF : IsIso (φW ≫ m.appTop) := by
    have : φW ≫ m.appTop = (Scheme.ΓSpecIso (Z.residueField η)).inv ≫
        ((j ≫ q).fiberToSpecResidueField η).appTop := by
      rw [← hm, Scheme.Hom.comp_appTop, Category.assoc]
    have h1 : IsIso ((j ≫ q).fiberToSpecResidueField η).c :=
      PresheafedSpace.c_isIso_of_iso ((j ≫ q).fiberToSpecResidueField η).toPshHom
    have h2 : IsIso ((j ≫ q).fiberToSpecResidueField η).appTop :=
      NatIso.isIso_app_of_isIso _ (Opposite.op ⊤)
    rw [this]; infer_instance
  haveI : Nontrivial Γ((j ≫ q).fiber η, ⊤) :=
    (asIso (φW ≫ m.appTop)).commRingCatIsoToRingEquiv.symm.toEquiv.nontrivial
  have hinj : Function.Injective m.appTop := by
    letI := hfield.toField
    exact RingHom.injective m.appTop.hom
  have hmb : IsIso m.appTop := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨hinj, fun y => ?_⟩
    obtain ⟨x, hx⟩ := ((ConcreteCategory.isIso_iff_bijective _).mp hφF).2 y
    exact ⟨φW x, by simpa using hx⟩
  exact IsIso.of_isIso_comp_right φW m.appTop

/-- **The adjoint sheaf is a pull-back from `X`.** For a crepant projective birational morphism
`h : (Y, C) ⟶ (X, B)` of snc subboundary pairs and `m > 0` with `mB` integral, there is a
Cartier divisor `D` on `X` (namely `mK_X + mB`) with `𝒪_Y(mK_Y + ⌊mC⌋) ≅ h^* 𝒪_X(D)`: the
crepant identity gives `m(K'_Y + C) = h^* D` for the canonical divisor `K'_Y = div(h^*ω)`,
`K_X = div ω`, and `K'_Y ∼ K_Y`. -/
private lemma exists_isCartier_divisorialSheaf_iso_pullback {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {B : QDivisor X} {C : QDivisor Y} (h : Y ⟶ X) (hB : IsSNCSubboundaryPair sX B)
    (hC : IsSNCSubboundaryPair (h ≫ sX) C) {n : ℕ} {KX : Divisor X}
    (hKX : KX.IsCanonicalDivisor sX n) {KY : Divisor Y} (hKY : KY.IsCanonicalDivisor (h ≫ sX) n)
    (hbir : IsBirationalMorphism h)
    (hcrep : ∀ hY : IsNormalVariety k (h ≫ sX), IsCrepantBoundary sX n KX B h hY hbir C)
    (m : ℕ) (hm : 0 < m) (hden : ∀ P, ((m : ℚ) * B.coeff P).den = 1) :
    ∃ D : Divisor X, D.IsCartier ∧
      Nonempty (((m : ℤ) • KY + DivisorWithCoeffs.roundDown ((m : ℤ) • C)).divisorialSheaf ≅
        (Scheme.Modules.pullback h).obj D.divisorialSheaf) := by
  have hX : IsNormalVariety k sX := ⟨hB.isProjectiveVariety.toIsVariety, inferInstance⟩
  have hY : IsNormalVariety k (h ≫ sX) := ⟨hC.isProjectiveVariety.toIsVariety, inferInstance⟩
  have hP : MMP.Mori.IsPair sX B :=
    ⟨hX, n, KX, hKX, isQCartier_of_isSmoothScheme hB.isSmoothScheme _⟩
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : CompactSpace X := haveI := hX.1.toQuasiCompact
    QuasiCompact.compactSpace_of_compactSpace sX
  haveI : LocallyOfFiniteType (h ≫ sX) := hY.1.toLocallyOfFiniteType
  haveI : CompactSpace Y := haveI := hY.1.toQuasiCompact
    QuasiCompact.compactSpace_of_compactSpace (h ≫ sX)
  haveI : IsDominant h := hbir.isDominant
  obtain ⟨ω, hω0, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hKX
  have hωK' : divisorOfForm ω = KX := by
    ext Γ
    rw [coeff_divisorOfForm, hωK]
  have hpb0 : pullbackRationalPluriForms sX h ω ≠ 0 :=
    MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' h
      hbir.functionFieldMap_bijective
      (toNat_trdeg_functionField_of_topologicalKrullDim_eq hKX.topologicalKrullDim_eq) hω0
  have hlin : (divisorOfForm (pullbackRationalPluriForms sX h ω)).LinearlyEquivalent KY := by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hY hKY hpb0
  set KY' := divisorOfForm (pullbackRationalPluriForms sX h ω) with hKY'
  have hfloor : ∀ q : ℚ, q.den = 1 → ((⌊q⌋ : ℤ) : ℚ) = q := fun q hq => by
    rw [Rat.floor_def', hq]
    simpa using Rat.coe_int_num_of_den_eq_one hq
  set D : Divisor X := (m : ℤ) • KX + DivisorWithCoeffs.roundDown ((m : ℤ) • B) with hDdef
  have hDq : Divisor.toQDivisor D = (m : ℤ) • (Divisor.toQDivisor KX + B) := by
    ext P
    simp only [hDdef, map_add, map_zsmul, DivisorWithCoeffs.coeff_add,
      DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_roundDown,
      smul_add]
    rw [hfloor _ (by simpa [zsmul_eq_mul] using hden P)]
  have hDc : D.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hB.isSmoothScheme D
  obtain ⟨hpbm, -, -⟩ := MMP.Mori.IsPair.isPullback_of_isCrepantBoundary hP h hY hbir hKX
    (hKY.of_linearlyEquivalent hlin) (Or.inl ⟨ω, hω0, hωK', rfl⟩) (hcrep hY)
  obtain ⟨DY, hDYq, -, hBpb, hpb⟩ := hpbm m hm D hDq hDc
  have hDm : (m : ℤ) • KY + DivisorWithCoeffs.roundDown ((m : ℤ) • C) =
      DY + (m : ℤ) • (KY - KY') := by
    ext P
    have hP := congrArg (fun A : QDivisor Y => A.coeff P) hDYq
    simp only [map_add, map_zsmul, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
      Divisor.coeff_toQDivisor, smul_add, zsmul_eq_mul] at hP
    have hCq : ((m : ℤ) • C).coeff P = ((DY.coeff P - (m : ℤ) * KY'.coeff P : ℤ) : ℚ) := by
      rw [DivisorWithCoeffs.coeff_smul, zsmul_eq_mul]; push_cast at hP ⊢; linarith
    simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
      DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_sub, hCq, Int.floor_intCast,
      smul_eq_mul]
    ring
  have hlinD : ((m : ℤ) • KY +
      DivisorWithCoeffs.roundDown ((m : ℤ) • C)).LinearlyEquivalent DY := by
    rw [Divisor.linearlyEquivalent_iff_sub_mem_range, hDm, add_sub_cancel_left]
    exact AddSubgroup.zsmul_mem _ (Divisor.linearlyEquivalent_iff_sub_mem_range.mp hlin.symm) _
  exact ⟨D, hDc, ⟨Divisor.LinearlyEquivalent.divisorialSheafIso hlinD ≪≫
    (Divisor.IsPullback.divisorialSheafIso (hBc := hDc) hpb)⟩⟩

/-- **Floor strata are normal.** A reduced closed subscheme of a smooth variety with snc
subboundary `B`, supported on a stratum of `B^{=1}`, is smooth by `stratum_closure`, hence
normal. -/
private lemma isNormal_of_isSNCStratum {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} (hB : IsSNCSubboundaryPair sX B) {Z : Scheme.{0}} (ιZ : Z ⟶ X)
    [IsClosedImmersion ιZ] [IsReduced Z]
    (hZ : IsSNCStratum (coeffOnePart B) (Set.range ιZ.base)) : IsNormal Z := by
  have hsnc : (coeffOnePart B).IsSNC sX :=
    hB.isSNC.of_support_subset (support_coeffOnePart_subset B)
  obtain ⟨J, hJ, hmax⟩ := hZ
  obtain ⟨w, hWw, hwJ, hcw⟩ := coheight_eq_card_of_isSNCStratum hsnc hJ hmax
  haveI : LocallyOfFiniteType sX := hB.isProjectiveVariety.toIsVariety.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hB.isProjectiveVariety.toIsVariety.toQuasiCompact
  obtain ⟨hsm, -⟩ := stratum_closure sX hsnc hJ hwJ hcw
  set V := Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure {w})
  haveI : Smooth (V.subschemeι ≫ sX) := (MMP.Mori.isSmoothScheme_iff _).1 hsm
  haveI : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
  haveI : IsNormal V.subscheme := AlgebraicGeometry.isNormal_of_smooth (V.subschemeι ≫ sX)
  have hr : Set.range ιZ = Set.range V.subschemeι := by
    change Set.range ιZ.base = _
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal,
      TopologicalSpace.Closeds.coe_closure, hWw]
  obtain ⟨e, -⟩ := exists_iso_of_range_eq ιZ V.subschemeι hr
  exact isNormal_of_isOpenImmersion e.hom

/-- **Section bijectivity on a birational substratum.** In the setting of the crepant snc model
`h`, let `F ⊆ W` be a floor stratum mapping birationally onto `Z = h(W)`. Then restriction of
sections of `𝒪_Y(mK_Y + ⌊mC⌋)` from `W` to `F` is bijective for every `m > 0` with `mB`
integral: this sheaf is the pull-back of an invertible sheaf `N` on `Z`, both `W ⟶ Z` and
`F ⟶ Z` have `𝒪_Z` as push-forward of the structure sheaf (Stein factorization through the
birational `F ⟶ Z`), so pull-back of sections of `N` to `W` and to `F` is bijective. -/
private theorem bijective_restriction_of_isBirationalMorphism {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    {sY : Y ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {B : QDivisor X} {C : QDivisor Y} (hB : IsSNCSubboundaryPair sX B)
    (hC : IsSNCSubboundaryPair sY C) {n : ℕ} {KX : Divisor X} (hKX : KX.IsCanonicalDivisor sX n)
    {KY : Divisor Y} (hKY : KY.IsCanonicalDivisor sY n)
    (h : Y ⟶ X) (hh : h ≫ sX = sY) (hproj : IsProjectiveMorphism h)
    (hbir : IsBirationalMorphism h)
    (hcrep : ∀ hY : IsNormalVariety k (h ≫ sX), IsCrepantBoundary sX n KX B h hY hbir C)
    {W : Scheme.{0}} (ιW : W ⟶ Y) [IsClosedImmersion ιW] [IsReduced W]
    (hW : IsSNCStratum (coeffOnePart C) (Set.range ιW.base))
    {Z : Scheme.{0}} (ιZ : Z ⟶ X) [IsClosedImmersion ιZ] [IsReduced Z]
    (hZ : Set.range ιZ.base = h.base '' Set.range ιW.base)
    (hZst : IsSNCStratum (coeffOnePart B) (Set.range ιZ.base))
    {F : Scheme.{0}} (j : F ⟶ W) [IsClosedImmersion j] [IsReduced F] (g : F ⟶ Z)
    (hFst : IsSNCStratum (coeffOnePart C) (Set.range (j ≫ ιW).base))
    (hg : g ≫ ιZ = j ≫ ιW ≫ h) (hgb : IsBirationalMorphism g)
    (m : ℕ) (hm : 0 < m) (hden : ∀ P, ((m : ℚ) * B.coeff P).den = 1) :
    Function.Bijective
      (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
        ((Scheme.Modules.pullback ιW).obj
          ((m : ℤ) • KY + DivisorWithCoeffs.roundDown ((m : ℤ) • C)).divisorialSheaf)).app ⊤) := by
  subst hh
  haveI : IsIntegral W := by
    obtain ⟨_, _, hmax⟩ := hW; exact isIntegral_of_isIrreducible_range ιW hmax.1.1
  haveI : IsIntegral Z := by
    obtain ⟨_, _, hmax⟩ := hZst; exact isIntegral_of_isIrreducible_range ιZ hmax.1.1
  haveI : IsIntegral F := by
    obtain ⟨_, _, hmax⟩ := hFst; exact isIntegral_of_isIrreducible_range (j ≫ ιW) hmax.1.1
  haveI : IsNormal Z := isNormal_of_isSNCStratum hB ιZ hZst
  haveI : IsProper h := isProper_of_isProjectiveMorphism h hproj
  -- the induced morphism `q : W ⟶ Z`
  obtain ⟨q, hq⟩ := exists_comp_eq_of_range_subset ιZ (ιW ≫ h) (by
    change Set.range (ιW ≫ h).base ⊆ Set.range ιZ.base
    rw [hZ]; rintro _ ⟨x, rfl⟩; exact ⟨ιW x, ⟨x, rfl⟩, rfl⟩)
  have hjq : j ≫ q = g := by rw [← cancel_mono ιZ, Category.assoc, hq, hg]
  haveI : IsProper q := MorphismProperty.of_postcomp @IsProper q ιZ
    (inferInstance : IsSeparated ιZ) (by rw [hq]; exact (inferInstance : IsProper (ιW ≫ h)))
  haveI : IsProper (j ≫ q) := MorphismProperty.of_postcomp @IsProper (j ≫ q) ιZ
    (inferInstance : IsSeparated ιZ)
    (by rw [hjq, hg]; exact (inferInstance : IsProper (j ≫ ιW ≫ h)))
  haveI : IsDominant q := by
    refine ⟨Function.Surjective.denseRange fun z => ?_⟩
    obtain ⟨_, ⟨w, rfl⟩, hw⟩ : ιZ z ∈ h.base '' Set.range ιW.base := hZ ▸ ⟨z, rfl⟩
    refine ⟨w, ιZ.isEmbedding.injective ?_⟩
    change (q ≫ ιZ) w = _
    rw [hq]; exact hw
  haveI : IsDominant (j ≫ q) := hjq ▸ hgb.isDominant
  have hgB : IsBirational (j ≫ q) :=
    hjq ▸ MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hgb
  haveI hqc : IsIso q.c := isIso_c_of_isBirational_comp j q hgB
  haveI hgc : IsIso (j ≫ q).c := isIso_c_of_isBirational_comp (𝟙 F) (j ≫ q)
    (by rwa [Category.id_comp])
  -- the adjoint sheaf is a pull-back from `Z`
  obtain ⟨D, hDc, ⟨e⟩⟩ := exists_isCartier_divisorialSheaf_iso_pullback h hB hC hKX hKY hbir
    hcrep m hm hden
  haveI : CompactSpace X := haveI := hB.isProjectiveVariety.toIsVariety.toQuasiCompact
    QuasiCompact.compactSpace_of_compactSpace sX
  haveI := hDc.isInvertibleModule_divisorialSheaf
  set N := (Scheme.Modules.pullback ιZ).obj D.divisorialSheaf
  let e' : (Scheme.Modules.pullback ιW).obj
      ((m : ℤ) • KY + DivisorWithCoeffs.roundDown ((m : ℤ) • C)).divisorialSheaf ≅
      (Scheme.Modules.pullback q).obj N :=
    (Scheme.Modules.pullback ιW).mapIso e ≪≫
      (Scheme.Modules.pullbackComp ιW h).app _ ≪≫
      (Scheme.Modules.pullbackCongr hq.symm).app _ ≪≫
      ((Scheme.Modules.pullbackComp q ιZ).app _).symm
  refine bijective_unit_app_top_of_iso j e' ?_
  exact bijective_unit_app_top_of_comp j q N (bijective_unit_app_top_of_isIso_c q N)
    (bijective_unit_app_top_of_isIso_c (j ≫ q) N)

open scoped Classical in
/-- **The generic point of a floor stratum avoids the rest of the boundary.** The generic point
of a stratum `F` of `C^{=1}` lies on no component of `C` other than the coefficient-one components
containing `F`: such a component would be one more component of the snc divisor `C` through a
point of codimension `|J|` already lying on the `|J|` components defining `F`. -/
private lemma map_genericPoint_notMem_supp_sub_floor {k : Type} [Field k] {Y : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} [IsLocallyNoetherian Y] {C : QDivisor Y}
    (hC : IsSNCSubboundaryPair sY C) {F : Scheme.{0}} (ι : F ⟶ Y) [IsClosedImmersion ι]
    [IsIntegral F] (hF : IsSNCStratum (coeffOnePart C) (Set.range ι.base)) :
    ι (genericPoint F) ∉ (C - Divisor.toQDivisor ((coeffOnePart C).filter
      fun G => Set.range ι.base ⊆ G.support)).supp := by
  classical
  have hsncC : (coeffOnePart C).IsSNC sY :=
    hC.isSNC.of_support_subset (support_coeffOnePart_subset C)
  set y := ι (genericPoint F) with hy
  have hrange : Set.range ι.base = closure {y} := by
    have h1 := ι.isClosedMap.closure_image_eq_of_continuous ι.continuous {genericPoint F}
    rw [Set.image_singleton, (genericPoint_spec F).def, Set.image_univ] at h1
    exact h1.symm
  obtain ⟨J, hJ, hmax⟩ := hF
  obtain ⟨w, hWw, hwJ, hcw⟩ := coheight_eq_card_of_isSNCStratum hsncC hJ hmax
  have hwy : w = y := by
    have h1 : IsGenericPoint w (Set.range ι.base) := by rw [hWw]; exact isGenericPoint_closure
    have h2 : IsGenericPoint y (Set.range ι.base) := by rw [hrange]; exact isGenericPoint_closure
    exact h1.eq h2
  subst hwy
  intro hmem
  obtain ⟨P, hP0, hyP⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
  have hFP : Set.range ι.base ⊆ P.support := by
    rw [hrange]
    exact closure_minimal (Set.singleton_subset_iff.mpr hyP) P.idealSheaf.support.isClosed
  by_cases hP1 : C.coeff P = 1
  · apply hP0
    simp only [DivisorWithCoeffs.coeff_sub, Divisor.coeff_toQDivisor]
    change C.coeff P - (((coeffOnePart C).filter fun G => Set.range ι.base ⊆ G.support) P : ℚ) = 0
    rw [Finsupp.filter_apply, if_pos hFP]
    change C.coeff P - (((coeffOnePart C).coeff P : ℤ) : ℚ) = 0
    rw [coeff_coeffOnePart, if_pos hP1, hP1]; norm_num
  · have hfil : ((coeffOnePart C).filter fun G => Set.range ι.base ⊆ G.support) P = 0 := by
      rw [Finsupp.filter_apply]
      split_ifs
      · change (coeffOnePart C).coeff P = 0
        rw [coeff_coeffOnePart, if_neg hP1]
    have hPC : P ∈ C.support := by
      rw [Finsupp.mem_support_iff]
      intro h0
      apply hP0
      simp only [DivisorWithCoeffs.coeff_sub, Divisor.coeff_toQDivisor]
      change C.coeff P - ((((coeffOnePart C).filter fun G => Set.range ι.base ⊆ G.support) P :
        ℤ) : ℚ) = 0
      rw [hfil]
      change C.coeff P - _ = 0
      have h0' : C.coeff P = 0 := h0
      rw [h0']; simp
    have hPJ : P ∉ J := fun hPJ => hP1 (coeff_eq_one_of_mem_support_coeffOnePart (hJ hPJ))
    have hJC : J ⊆ C.support := hJ.trans (support_coeffOnePart_subset C)
    obtain ⟨c, hc, hcard⟩ := card_le_coheight_of_isSNC hC.isSNC (ι (genericPoint F)) (insert P J)
      (Finset.insert_subset hPC hJC) (fun G hG => by
        rcases Finset.mem_insert.mp hG with rfl | hG
        · exact hyP
        · exact hwJ G hG)
    rw [hcw] at hc
    have hcJ : c = J.card := by exact_mod_cast hc.symm
    rw [Finset.card_insert_of_notMem hPJ, hcJ] at hcard
    omega

open scoped Classical in
/-- The coefficient-one components of an snc subboundary `C` containing the stratum
`closure {w}` cut out by `J` are exactly those of `J`. -/
private lemma toQDivisor_filter_coeffOnePart_eq_sum {k : Type} [Field k] {Y : Scheme.{0}}
    [IsLocallyNoetherian Y] {sY : Y ⟶ Spec (.of k)} {C : QDivisor Y}
    (hC : IsSNCSubboundaryPair sY C) {J : Finset (MMP.Mori.PrimeDivisor Y)} (hJ : J ⊆ C.support)
    (hJ1 : ∀ G ∈ J, C.coeff G = 1) {w : Y} (hwJ : ∀ G ∈ J, w ∈ G.support)
    (hcw : Order.coheight w = J.card) {S : Scheme.{0}} (ι : S ⟶ Y)
    (hι : Set.range ι.base = closure {w}) :
    Divisor.toQDivisor ((coeffOnePart C).filter fun G => Set.range ι.base ⊆ G.support) =
      ∑ G ∈ J, Finsupp.single G (1 : ℚ) := by
  ext G
  rw [Divisor.coeff_toQDivisor]
  change (((coeffOnePart C).filter fun G => Set.range ι.base ⊆ G.support) G : ℚ) =
    (∑ G ∈ J, Finsupp.single G (1 : ℚ)) G
  rw [Finsupp.filter_apply, Finsupp.finset_sum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq']
  have hiff : (Set.range ι.base ⊆ G.support ∧ C.coeff G = 1) ↔ G ∈ J := by
    constructor
    · rintro ⟨hsub, hG1⟩
      by_contra hGJ
      have hwG : w ∈ G.support := hsub (hι ▸ subset_closure rfl)
      have hGC : G ∈ C.support := Finsupp.mem_support_iff.mpr (by
        change C.coeff G ≠ 0; rw [hG1]; norm_num)
      obtain ⟨c, hc, hcard⟩ := card_le_coheight_of_isSNC hC.isSNC w (insert G J)
        (Finset.insert_subset hGC hJ) (fun G' hG' => by
          rcases Finset.mem_insert.mp hG' with rfl | hG'
          · exact hwG
          · exact hwJ G' hG')
      rw [hcw] at hc
      have hcJ : c = J.card := by exact_mod_cast hc.symm
      rw [Finset.card_insert_of_notMem hGJ, hcJ] at hcard
      omega
    · intro hGJ
      refine ⟨?_, hJ1 G hGJ⟩
      rw [hι]
      exact closure_minimal (Set.singleton_subset_iff.mpr (hwJ G hGJ))
        G.idealSheaf.support.isClosed
  by_cases hGJ : G ∈ J
  · obtain ⟨hsub, hG1⟩ := hiff.mpr hGJ
    rw [if_pos hsub, if_pos hGJ]
    change (((coeffOnePart C).coeff G : ℤ) : ℚ) = 1
    rw [coeff_coeffOnePart, if_pos hG1]
    norm_num
  · rw [if_neg hGJ]
    split_ifs with hsub
    · change (((coeffOnePart C).coeff G : ℤ) : ℚ) = 0
      rw [coeff_coeffOnePart, if_neg (fun hG1 => hGJ (hiff.mp ⟨hsub, hG1⟩))]
      norm_num
    · rfl

open scoped Classical in
/-- **Restriction to strata is crepant.** Let `F` be a floor stratum of `(Y, C)` with the
restricted boundary `C_F = (C - ∑_{G ∈ C^{=1}, F ⊆ G} G)|_F`, and `T` a floor stratum of `(X, B)`,
cut out by the components `J_X` of `B^{=1}`, with the restricted boundary
`B_T = (B - ∑_{G ∈ J_X} G)|_T` (given by its coefficients), and `h` inducing a birational
`F ⟶ T`. Then `C_F` is the crepant boundary of `(T, B_T)` on `F`: residue adjunction of the ambient
crepant identity `K_Y + C = h^*(K_X + B)`. -/
private theorem isCrepantBoundary_of_isSNCStratum {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {B : QDivisor X} {C : QDivisor Y} (hB : IsSNCSubboundaryPair sX B)
    (hC : IsSNCSubboundaryPair sY C) {n : ℕ} {KX : Divisor X} (hKX : KX.IsCanonicalDivisor sX n)
    {KY : Divisor Y} (hKY : KY.IsCanonicalDivisor sY n)
    (h : Y ⟶ X) (hh : h ≫ sX = sY) (hproj : IsProjectiveMorphism h)
    (hbir : IsBirationalMorphism h)
    (hcrep : ∀ hY : IsNormalVariety k (h ≫ sX), IsCrepantBoundary sX n KX B h hY hbir C)
    {F : Scheme.{0}} (ιF : F ⟶ Y) [IsClosedImmersion ιF] [IsIntegral F] [IsLocallyNoetherian F]
    [IsNormal F] (hFst : IsSNCStratum (coeffOnePart C) (Set.range ιF.base))
    (hFY : Set.range ιF.base ≠ Set.univ) {CF : QDivisor F}
    (hgen : ∀ V : irreducibleComponents F, ιF (componentGenericPoint F V) ∉
      (C - Divisor.toQDivisor ((coeffOnePart C).filter
        fun G => Set.range ιF.base ⊆ G.support)).supp)
    (hCF : (C - Divisor.toQDivisor ((coeffOnePart C).filter
        fun G => Set.range ιF.base ⊆ G.support)).IsPullback ιF hgen CF)
    {T : Scheme.{0}} (ιT : T ⟶ X) [IsClosedImmersion ιT] [IsIntegral T] [IsNormal T]
    [IsLocallyNoetherian T] (hTv : IsNormalVariety k (ιT ≫ sX)) {BT : QDivisor T}
    {JX : Finset (MMP.Mori.PrimeDivisor X)} {wX : X} (hJX : JX ⊆ B.support)
    (hJX1 : ∀ G ∈ JX, B.coeff G = 1) (hwXJ : ∀ G ∈ JX, wX ∈ G.support)
    (hcwX : Order.coheight wX = JX.card) (hrT : Set.range ιT.base = closure {wX})
    (hBTc : ∀ Q : MMP.Mori.PrimeDivisor T, BT.coeff Q =
      ∑ E ∈ B.support.filter (fun E => E ∉ JX ∧ ιT Q.genericPoint ∈ E.support), B.coeff E)
    (gT : F ⟶ T) (hgT : gT ≫ ιT = ιF ≫ h) :
    ∀ (hg : IsBirationalMorphism gT) (d : ℕ) (KT : Divisor T),
      KT.IsCanonicalDivisor (ιT ≫ sX) d → ∀ hS : IsNormalVariety k (gT ≫ ιT ≫ sX),
        IsCrepantBoundary (ιT ≫ sX) d KT BT gT hS hg CF := by
  intro hg d KT hKT hS
  subst hh
  -- the ambient varieties
  have hXv : IsNormalVariety k sX := ⟨hB.isProjectiveVariety.toIsVariety, inferInstance⟩
  have hYv : IsNormalVariety k (h ≫ sX) := ⟨hC.isProjectiveVariety.toIsVariety, inferInstance⟩
  haveI : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hXv.1.toQuasiCompact
  haveI : IsSeparated sX := hXv.1.toIsSeparated
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : LocallyOfFiniteType (h ≫ sX) := hYv.1.toLocallyOfFiniteType
  haveI : QuasiCompact (h ≫ sX) := hYv.1.toQuasiCompact
  haveI : IsSeparated (h ≫ sX) := hYv.1.toIsSeparated
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (h ≫ sX)
  haveI : LocallyOfFinitePresentation sX :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := sX)).mpr inferInstance
  haveI : Smooth sX := (MMP.Mori.isSmoothScheme_iff sX).1 hB.isSmoothScheme
  haveI : LocallyOfFinitePresentation (h ≫ sX) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := h ≫ sX)).mpr inferInstance
  haveI : Smooth (h ≫ sX) := (MMP.Mori.isSmoothScheme_iff _).1 hC.isSmoothScheme
  have hQX : ∀ A : QDivisor X, A.IsQCartier := isQCartier_of_isSmoothScheme hB.isSmoothScheme
  have hQY : ∀ A : QDivisor Y, A.IsQCartier := isQCartier_of_isSmoothScheme hC.isSmoothScheme
  haveI : IsProper h := isProper_of_isProjectiveMorphism h hproj
  haveI : IsDominant h := hbir.isDominant
  haveI : IsDominant gT := hg.isDominant
  haveI : CompactSpace F := ιF.isClosedEmbedding.compactSpace
  haveI : CompactSpace T := ιT.isClosedEmbedding.compactSpace
  have hn := hKX.topologicalKrullDim_eq
  have hnY := hKY.topologicalKrullDim_eq
  -- the flag ends at a smooth stratum, with `B_T = (B - ∑_{J_X} G)|_T`
  obtain ⟨hsmT, hkerT, hyJT⟩ := stratum_package sX hB.isSNC hJX hwXJ hcwX ιT hrT
  -- the floor stratum `F`
  have hsncC1 : (coeffOnePart C).IsSNC (h ≫ sX) :=
    hC.isSNC.of_support_subset (support_coeffOnePart_subset C)
  obtain ⟨JF, hJF, hmaxF⟩ := id hFst
  obtain ⟨wF, hFw, hwFJ, hcwF⟩ := coheight_eq_card_of_isSNCStratum hsncC1 hJF hmaxF
  have hJFC : JF ⊆ C.support := hJF.trans (support_coeffOnePart_subset C)
  have hJF1 : ∀ G ∈ JF, C.coeff G = 1 := fun G hG =>
    coeff_eq_one_of_mem_support_coeffOnePart (hJF hG)
  obtain ⟨hsmF, hkerF, hyJF⟩ := stratum_package (h ≫ sX) hC.isSNC hJFC hwFJ hcwF ιF hFw
  have hfilt := toQDivisor_filter_coeffOnePart_eq_sum hC hJFC hJF1 hwFJ hcwF ιF hFw
  have hAFD : (C - ∑ G ∈ JF, Finsupp.single G (1 : ℚ)).support ⊆ C.support :=
    support_sub_sum_single_subset C hJFC
  have hAFJ := coeff_sub_sum_single_eq_zero C hJF1
  have hgenAF := stratum_hgen hC.isSNC hJFC ιF hyJF hkerF _ hAFD hAFJ
  have hCF' : (C - ∑ G ∈ JF, Finsupp.single G (1 : ℚ)).IsPullback ιF hgenAF CF :=
    qdivisor_isPullback_congr (by rw [hfilt]) hCF
  -- dimensions
  have hdT := hKT.topologicalKrullDim_eq
  haveI : LocallyOfFiniteType (gT ≫ ιT ≫ sX) := hS.1.toLocallyOfFiniteType
  have hdF : topologicalKrullDim F = d :=
    topologicalKrullDim_eq_of_isBirationalMorphism (ιT ≫ sX) gT hg hdT
  have hdT' := topologicalKrullDim_add_coheight_of_range sX ιT hrT
  rw [hcwX, hn, hdT] at hdT'
  have hdF' := topologicalKrullDim_add_coheight_of_range (h ≫ sX) ιF hFw
  rw [hcwF, hnY, hdF] at hdF'
  have hdJX : d + JX.card = n := by exact_mod_cast hdT'
  have hdJF : d + JF.card = n := by exact_mod_cast hdF'
  have hJFpos : 1 ≤ JF.card := by
    by_contra h0
    have hJFe : JF = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hJFe
    exact hFY (hmaxF.eq_of_ge ⟨IrreducibleSpace.isIrreducible_univ Y, by simp⟩
      (Set.subset_univ _)).symm
  have hJXpos : 1 ≤ JX.card := by omega
  -- `B_T` as a pull-back
  have hAXD : (B - ∑ G ∈ JX, Finsupp.single G (1 : ℚ)).support ⊆ B.support :=
    support_sub_sum_single_subset B hJX
  have hAXJ := coeff_sub_sum_single_eq_zero B hJX1
  have hgenAX := stratum_hgen hB.isSNC hJX ιT hyJT hkerT _ hAXD hAXJ
  haveI := hsmT
  have hBTpb : (B - ∑ G ∈ JX, Finsupp.single G (1 : ℚ)).IsPullback ιT hgenAX BT := by
    have hp := QDivisor.isPullback_pullback (hQX _) hgenAX
    have heq : (B - ∑ G ∈ JX, Finsupp.single G (1 : ℚ)).pullback (hQX _) hgenAX = BT := by
      ext Q
      rw [coeff_isPullback_of_stratum sX hB.isSNC hJX ιT hyJT hkerT _ hAXD hAXJ (hQX _) hp Q,
        sum_filter_sub_sum_single B JX hJX1, hBTc Q]
    rwa [heq] at hp
  -- a top form on `X` adapted to the generic point of `T`
  obtain ⟨ω, hω0, -⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hXv hKX
  obtain ⟨σ, hσ0, hσw⟩ := exists_form_notMem_supp sX hn
    (fun D => isCartier_of_isSmoothScheme hB.isSmoothScheme D) ω hω0
    (∑ G ∈ JX, Finsupp.single G (1 : ℤ)) wX
  have hwD : wX ∉ (Divisor.toQDivisor (divisorOfForm σ) + B).supp := by
    have hsplit : Divisor.toQDivisor (divisorOfForm σ) + B =
        Divisor.toQDivisor (divisorOfForm σ + ∑ G ∈ JX, Finsupp.single G (1 : ℤ)) +
          (B - ∑ G ∈ JX, Finsupp.single G (1 : ℚ)) := by
      ext G
      simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_sub,
        Divisor.coeff_toQDivisor]
      change _ = ((divisorOfForm σ + ∑ G ∈ JX, Finsupp.single G (1 : ℤ)) G : ℚ) + _
      rw [Finsupp.add_apply, Finsupp.finset_sum_apply]
      change _ = (((divisorOfForm σ).coeff G + ∑ i ∈ JX, (Finsupp.single i (1 : ℤ)) G : ℤ) : ℚ) +
        (B.coeff G - (∑ G ∈ JX, Finsupp.single G (1 : ℚ)) G)
      rw [Finsupp.finset_sum_apply]
      push_cast
      simp only [Finsupp.single_apply]
      push_cast
      ring
    rw [hsplit]
    intro hmem
    obtain ⟨E, hE0, hwE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
    rw [DivisorWithCoeffs.coeff_add] at hE0
    have h1 : (Divisor.toQDivisor (divisorOfForm σ + ∑ G ∈ JX, Finsupp.single G (1 : ℤ))).coeff E
        = 0 := by
      rw [Divisor.coeff_toQDivisor]
      by_contra h
      exact hσw (DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, by exact_mod_cast h, hwE⟩)
    have h2 : (B - ∑ G ∈ JX, Finsupp.single G (1 : ℚ)).coeff E = 0 := by
      by_contra h
      have hEB : E ∈ B.support := hAXD (Finsupp.mem_support_iff.mpr h)
      have hEJ : E ∉ JX := fun hEJ => h (hAXJ E hEJ)
      obtain ⟨c, hc, hcard⟩ := card_le_coheight_of_isSNC hB.isSNC wX (insert E JX)
        (Finset.insert_subset hEB hJX) (fun G hG => by
          rcases Finset.mem_insert.mp hG with rfl | hG
          · exact hwE
          · exact hwXJ G hG)
      rw [hcwX] at hc
      have hcJ : c = JX.card := by exact_mod_cast hc.symm
      rw [Finset.card_insert_of_notMem hEJ, hcJ] at hcard
      omega
    exact hE0 (by rw [h1, h2, add_zero])
  -- iterated residues on `X`: `(div σ + B)|_T = div σ_T + B_T`
  obtain ⟨c, hc⟩ : ∃ c, JX.card = c + 1 := ⟨JX.card - 1, by omega⟩
  obtain ⟨σT, hσT0, hgenDT, hpbT⟩ := exists_isPullback_divisorOfForm_add_of_stratum sX hn
    hB.isSNC hQX σ hσ0 c hc hJX hJX1 hwXJ hcwX hwD ιT hrT hdJX hBTpb
  -- the crepant identity `div h^*σ + C = h^*(div σ + B)`
  have hbij := hbir.functionFieldMap_bijective
  have hdX := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨hσY0, -⟩ := pullbackRationalPluriForms_ne_zero_and_exists_eq_smul sX h hbij hdX hσ0
    (pullbackRationalPluriForms sX h σ)
  have hlinX : (divisorOfForm σ).LinearlyEquivalent KX := by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hXv hKX hσ0
  have hlinY : (divisorOfForm (pullbackRationalPluriForms sX h σ)).LinearlyEquivalent KY := by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hYv hKY hσY0
  have hKXσ : (divisorOfForm σ).IsCanonicalDivisor sX n := hKX.of_linearlyEquivalent hlinX
  have hKYσ : (divisorOfForm (pullbackRationalPluriForms sX h σ)).IsCanonicalDivisor (h ≫ sX) n :=
    hKY.of_linearlyEquivalent hlinY
  have hcrepσ : IsCrepantBoundary sX n (divisorOfForm σ) B h hYv hbir C := fun G =>
    MMP.Spreading.isDiscrepancy_of_linearlyEquivalent (hcrep hYv G) hlinX
  have hP : MMP.Mori.IsPair sX B := ⟨hXv, n, KX, hKX, hQX _⟩
  obtain ⟨-, -, hgenY, hpbY⟩ := MMP.Mori.IsPair.isPullback_of_isCrepantBoundary hP h hYv hbir
    hKXσ hKYσ (Or.inl ⟨σ, hσ0, rfl, rfl⟩) hcrepσ
  -- the generic points
  have hgTgen : gT (genericPoint F) = genericPoint T := map_genericPoint_of_isDominant gT
  have hιTgen : ιT (genericPoint T) = wX := by
    have h1 : IsGenericPoint (ιT (genericPoint T)) (Set.range ιT.base) := by
      have := (genericPoint_spec T).image ιT.base.hom.continuous
      rwa [Set.image_univ, ιT.isClosedEmbedding.isClosed_range.closure_eq] at this
    have h2 : IsGenericPoint wX (Set.range ιT.base) := by rw [hrT]; exact isGenericPoint_closure
    exact h1.eq h2
  have hιFgen : ιF (genericPoint F) = wF := by
    have h1 : IsGenericPoint (ιF (genericPoint F)) (Set.range ιF.base) := by
      have := (genericPoint_spec F).image ιF.base.hom.continuous
      rwa [Set.image_univ, ιF.isClosedEmbedding.isClosed_range.closure_eq] at this
    have h2 : IsGenericPoint wF (Set.range ιF.base) := by rw [hFw]; exact isGenericPoint_closure
    exact h1.eq h2
  have hhwF : h wF = wX := by
    rw [← hιFgen, ← hιTgen, ← hgTgen, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hgT]
  -- iterated residues on `Y`: `(div h^*σ + C)|_F = div σ_F + C_F`
  have hwFD : wF ∉ (Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms sX h σ)) +
      C).supp := notMem_supp_of_isPullback (hQX _) hpbY (by rw [hhwF]; exact hwD)
  obtain ⟨σF, hσF0, hgenDF, hpbF⟩ := exists_isPullback_divisorOfForm_add_of_stratum (h ≫ sX) hnY
    hC.isSNC hQY (pullbackRationalPluriForms sX h σ) hσY0 c (by omega) hJFC hJF1 hwFJ hcwF hwFD
    ιF hFw hdJF hCF'
  -- `div σ_F + C_F = g_T^*(div σ_T + B_T)`
  have hgenC : ∀ W : irreducibleComponents F, (ιF ≫ h) (componentGenericPoint F W) ∉
      (Divisor.toQDivisor (divisorOfForm σ) + B).supp := fun W => by
    rw [componentGenericPoint_eq_genericPoint, Scheme.Hom.comp_apply, hιFgen, hhwF]; exact hwD
  have hcompY := qdivisor_isPullback_comp hpbY hpbF hgenC
  have hQT : ∀ A : QDivisor T, A.IsQCartier :=
    isQCartier_of_isSmoothScheme ((MMP.Mori.isSmoothScheme_iff _).2 hsmT)
  have hgenG : ∀ W : irreducibleComponents F, gT (componentGenericPoint F W) ∉
      (Divisor.toQDivisor (divisorOfForm σT) + BT).supp := fun W => by
    rw [componentGenericPoint_eq_genericPoint, hgTgen]; exact genericPoint_notMem_supp _
  have hpbG := QDivisor.isPullback_pullback (hQT _) hgenG
  have hgenC' : ∀ W : irreducibleComponents F, (gT ≫ ιT) (componentGenericPoint F W) ∉
      (Divisor.toQDivisor (divisorOfForm σ) + B).supp := by rw [hgT]; exact hgenC
  have hcompY' : (Divisor.toQDivisor (divisorOfForm σ) + B).IsPullback (gT ≫ ιT) hgenC'
      (Divisor.toQDivisor (divisorOfForm σF) + CF) :=
    qdivisor_isPullback_morphism_congr hgT.symm hcompY
  have hcompX := qdivisor_isPullback_comp hpbT hpbG hgenC'
  have hGeq := (hcompX.pullback_eq (hQX _)).symm.trans (hcompY'.pullback_eq (hQX _))
  rw [hGeq] at hpbG
  -- the form `σ_F` as a form on `F` over `T`
  have hsF : ιF ≫ h ≫ sX = gT ≫ ιT ≫ sX := by
    rw [← Category.assoc, ← hgT, Category.assoc]
  have hpbG' : (Divisor.toQDivisor (divisorOfForm σT) + BT).IsPullback gT hgenG
      (Divisor.toQDivisor (divisorOfForm (hsF ▸ σF : RationalPluriForms (gT ≫ ιT ≫ sX) d 1)) +
        CF) := by
    rw [divisorOfForm_eqRec hsF]; exact hpbG
  -- the comparison of restricted coefficients
  have hle : ∀ (QT : MMP.Mori.PrimeDivisor T) (Q : MMP.Mori.PrimeDivisor F),
      gT Q.genericPoint = QT.genericPoint → CF.coeff Q ≤ BT.coeff QT := by
    intro QT Q hQ
    rw [hBTc QT, coeff_isPullback_of_stratum (h ≫ sX) hC.isSNC hJFC ιF hyJF hkerF _ hAFD hAFJ
      (hQY _) hCF' Q, sum_filter_sub_sum_single C JF hJF1]
    have hcQ := coheight_map_eq_add_card hC.isSNC hJFC ιF Q.genericPoint (hyJF _) (hkerF _)
    have hcQT := coheight_map_eq_add_card hB.isSNC hJX ιT QT.genericPoint (hyJT _) (hkerT _)
    rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at hcQ hcQT
    have hhq : h (ιF Q.genericPoint) = ιT QT.genericPoint := by
      rw [← hQ, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hgT]
    have hcQ' : Order.coheight (ιF Q.genericPoint) = JF.card + 1 := by
      have : ((Order.coheight (ιF Q.genericPoint) : ℕ∞) : WithBot ℕ∞) =
          (((JF.card + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by rw [← hcQ]; push_cast; ring
      exact_mod_cast WithBot.coe_injective this
    have hcQT' : Order.coheight (h (ιF Q.genericPoint)) = JX.card + 1 := by
      rw [hhq]
      have : ((Order.coheight (ιT QT.genericPoint) : ℕ∞) : WithBot ℕ∞) =
          (((JX.card + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by rw [← hcQT]; push_cast; ring
      exact_mod_cast WithBot.coe_injective this
    have key := sum_coeff_le_of_crepant hB h hC hKX hKY hbir hcrep hJFC hJF1 hJFpos
      (hyJF _) hcQ' hJX hJX1 (fun G hG => by rw [hhq]; exact hyJT _ G hG) hcQT' hJXpos
    rwa [hhq] at key
  -- constancy of the ratio
  haveI : IsProper sX := isProper_of_isProjectiveMorphism sX hB.isProjectiveVariety.isProjective
  haveI : IsProper (ιT ≫ sX) := inferInstance
  haveI : IsProper gT := MorphismProperty.of_postcomp @IsProper gT ιT
    (inferInstance : IsSeparated ιT) (by rw [hgT]; exact (inferInstance : IsProper (ιF ≫ h)))
  have hdiv := divisorOfForm_eq_of_isPullback_of_le (ιT ≫ sX) gT hg hdT σT hσT0 _
    (eqRec_ne_zero hsF hσF0) BT CF (hQT _) hpbG' hle
  -- the crepant boundary
  obtain ⟨ωT, hωT0, hωT⟩ := exists_toPluriForms_eq hσT0
  have hPairT : MMP.Mori.IsPair (ιT ≫ sX) BT := ⟨hTv, d, KT, hKT, hQT _⟩
  have hKω : topFormDivisor (ιT ≫ sX) ωT = divisorOfForm σT := by
    unfold topFormDivisor; rw [hωT]
  have hcb : IsCrepantBoundary (ιT ≫ sX) d (topFormDivisor (ιT ≫ sX) ωT) BT gT hS hg CF := by
    refine (MMP.Mori.isCrepantBoundary_iff_isPullback_topFormDivisor_add (ιT ≫ sX) hPairT hdT
      ωT hωT0 gT hS hg CF).mpr fun hB' => ?_
    rw [hωT, ← hdiv]
    revert hB'
    rw [hKω]
    intro hB'
    exact hpbG'
  have hlinT : KT.LinearlyEquivalent (topFormDivisor (ιT ≫ sX) ωT) :=
    MMP.Flips.linearlyEquivalent_of_isCanonicalDivisor ((MMP.Mori.isSmoothScheme_iff _).2 hsmT)
      hKT (MMP.Spreading.CanonExist.isCanonicalDivisor_topFormDivisor hTv hdT hωT0)
  exact fun Q => MMP.Spreading.isDiscrepancy_of_linearlyEquivalent (hcb Q) hlinT

open scoped Classical in
/-- **Iterated adjunction is crepant.** Let `F` be a floor stratum of `(Y, C)` with the
restricted boundary `C_F = (C - ∑_{G ∈ C^{=1}, F ⊆ G} G)|_F`, and let a flag of iterated
adjunction of `(X, B)` end at `(T, B_T)` with `h` inducing a birational `F ⟶ T`. Then `C_F` is
the crepant boundary of `(T, B_T)` on `F`: residue adjunction of the ambient crepant identity
`K_Y + C = h^*(K_X + B)`. -/
private theorem isCrepantBoundary_of_stratumAdjunctionData {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {B : QDivisor X} {C : QDivisor Y} (hB : IsSNCSubboundaryPair sX B)
    (hC : IsSNCSubboundaryPair sY C) {n : ℕ} {KX : Divisor X} (hKX : KX.IsCanonicalDivisor sX n)
    {KY : Divisor Y} (hKY : KY.IsCanonicalDivisor sY n)
    (h : Y ⟶ X) (hh : h ≫ sX = sY) (hproj : IsProjectiveMorphism h)
    (hbir : IsBirationalMorphism h)
    (hcrep : ∀ hY : IsNormalVariety k (h ≫ sX), IsCrepantBoundary sX n KX B h hY hbir C)
    {F : Scheme.{0}} (ιF : F ⟶ Y) [IsClosedImmersion ιF] [IsIntegral F] [IsLocallyNoetherian F]
    [IsNormal F] (hFst : IsSNCStratum (coeffOnePart C) (Set.range ιF.base))
    (hFY : Set.range ιF.base ≠ Set.univ) {CF : QDivisor F}
    (hgen : ∀ V : irreducibleComponents F, ιF (componentGenericPoint F V) ∉
      (C - Divisor.toQDivisor ((coeffOnePart C).filter
        fun G => Set.range ιF.base ⊆ G.support)).supp)
    (hCF : (C - Divisor.toQDivisor ((coeffOnePart C).filter
        fun G => Set.range ιF.base ⊆ G.support)).IsPullback ιF hgen CF)
    {T : Scheme.{0}} {ιT : T ⟶ X} {BT : QDivisor T} (FT : StratumAdjunctionData sX B ιT BT)
    (gT : F ⟶ T) (hgT : gT ≫ ιT = ιF ≫ h) :
    haveI := FT.isIntegral_stratum
    haveI := FT.isNormal_stratum
    haveI := FT.isLocallyNoetherian_stratum
    ∀ (hg : IsBirationalMorphism gT) (d : ℕ) (KT : Divisor T),
      KT.IsCanonicalDivisor (ιT ≫ sX) d → ∀ hS : IsNormalVariety k (gT ≫ ιT ≫ sX),
        IsCrepantBoundary (ιT ≫ sX) d KT BT gT hS hg CF := by
  haveI := FT.isIntegral_stratum
  haveI := FT.isNormal_stratum
  haveI := FT.isLocallyNoetherian_stratum
  haveI := FT.isClosedImmersion
  have hn := hKX.topologicalKrullDim_eq
  obtain ⟨JX, wX, hJX, hJX1, hJXl, hwXJ, hcwX, hrT, -, hBTc⟩ := flag_isStratum_coeff hB hn FT
  exact isCrepantBoundary_of_isSNCStratum hB hC hKX hKY h hh hproj hbir hcrep ιF hFst hFY hgen hCF
    ιT FT.isNormalVariety hJX hJX1 hwXJ hcwX hrT hBTc gT hgT

/-! ### Lifting inside a birational stratum -/

/-- `x + b = n` in `WithBot ℕ∞` with `b, n` natural numbers forces `x = n - b`. -/
private lemma coheight_eq_sub_of_add_eq {x : ℕ∞} {b n : ℕ}
    (h : ((x : ℕ∞) : WithBot ℕ∞) + (b : WithBot ℕ∞) = (n : WithBot ℕ∞)) :
    x = ((n - b : ℕ) : ℕ∞) := by
  have := withBot_eq_sub_of_add_eq (a := (x : WithBot ℕ∞)) (b := b) (n := n) (by exact_mod_cast h)
  exact_mod_cast this

/-- **Components of an snc intersection are disjoint.** The intersection `⋂_{G ∈ T} G` of
components of an snc divisor on a scheme smooth over a perfect field is smooth, so two of its
irreducible components meeting at a point coincide. -/
private theorem eq_of_mem_componentsOf_biInter {R : Type*} [Zero R] {k : Type} [Field k]
    [PerfectField k] {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY]
    [QuasiCompact sY] {D : DivisorWithCoeffs R Y} (hD : D.IsSNC sY)
    {T : Finset (MMP.Mori.PrimeDivisor Y)} (hT : T ⊆ D.support) {V W : Set Y}
    (hV : Maximal (fun V' : Set Y => IsIrreducible V' ∧ V' ⊆ ⋂ G ∈ T, (G.support : Set Y)) V)
    (hW : Maximal (fun V' : Set Y => IsIrreducible V' ∧ V' ⊆ ⋂ G ∈ T, (G.support : Set Y)) W)
    {x : Y} (hxV : x ∈ V) (hxW : x ∈ W) : V = W := by
  classical
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  set Dt := T.sup (fun G => G.idealSheaf) with hDdef
  have hDsupp : (Dt.support : Set Y) = ⋂ G ∈ T, (G.support : Set Y) :=
    coe_support_finset_sup _ _
  have hDreg := isRegularLocalRing_quotient_stalk_finset_sup hD hT
  have hDsm : IsSmoothScheme (Dt.subschemeι ≫ sY) :=
    MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isSmoothScheme_subscheme_of_isRegularLocalRing_quotient
      sY Dt hDreg
  refine MMP.Resolution.Aux.eq_of_mem_componentsOf_of_isSmoothScheme sY Dt hDsm ?_ ?_ hxV hxW
  · simp only [MMP.Resolution.componentsOf, Set.mem_setOf_eq]; rw [hDsupp]; exact hV
  · simp only [MMP.Resolution.componentsOf, Set.mem_setOf_eq]; rw [hDsupp]; exact hW

/-- On an snc divisor, a point `x` of `⋂_{G ∈ T} G` whose closure meets the stratum
`closure {w}` cut out by `T` lies in it. -/
private theorem mem_closure_of_specializes_of_stratum {R : Type*} [Zero R] {k : Type} [Field k]
    [PerfectField k] {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY]
    [QuasiCompact sY] {D : DivisorWithCoeffs R Y} (hD : D.IsSNC sY)
    {T : Finset (MMP.Mori.PrimeDivisor Y)} (hT : T ⊆ D.support) {w : Y}
    (hwT : ∀ G ∈ T, w ∈ G.support) (hcw : Order.coheight w = T.card) {x v : Y}
    (hxT : ∀ G ∈ T, x ∈ G.support) (hxv : x ⤳ v) (hvw : v ∈ closure {w}) : x ∈ closure {w} := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : AlgebraicGeometry.IsNoetherian Y := {}
  have hcl : IsClosed (⋂ E ∈ T, (E.support : Set Y)) :=
    isClosed_biInter fun G _ => G.idealSheaf.support.isClosed
  obtain ⟨-, hcov⟩ := MMP.Resolution.Aux.finite_and_cover_componentsOf hcl
  obtain ⟨C, hC, hxC⟩ := hcov (Set.mem_iInter₂.mpr hxT)
  have hCcl : IsClosed C := MMP.Resolution.Aux.isClosed_of_mem_componentsOf hcl hC
  have hvC : v ∈ C := hxv.mem_closed hCcl hxC
  have := eq_of_mem_componentsOf_biInter sY hD hT hC
    (maximal_closure_singleton hD w T hT hwT hcw) hvC hvw
  exact this ▸ hxC

open scoped Classical in
/-- **Floor strata inside a stratum are floor strata of the restricted pair.** Let `ι : S ⟶ X` be
an integral closed subscheme onto a stratum `closure {w}` cut out by components `J` of `B` of
coefficient one, with `B_S = (B - ∑_{G ∈ J} G)|_S` making `S` an snc subboundary pair. Then the
preimage of a floor stratum `F ⊆ closure {w}` of `(X, B)` is a floor stratum of `(S, B_S)`: each
further floor component `G` through the generic point of `F` restricts to a coefficient-one prime
of `S`, the component of `ι⁻¹ G` through it. -/
private theorem isSNCStratum_preimage_of_stratum {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {B : QDivisor X} (hB : IsSNCSubboundaryPair sX B)
    {J : Finset (MMP.Mori.PrimeDivisor X)} (hJ : J ⊆ B.support) (hJ1 : ∀ G ∈ J, B.coeff G = 1)
    {w : X} (hwJ : ∀ G ∈ J, w ∈ G.support) (hcw : Order.coheight w = J.card)
    {S : Scheme.{0}} (ι : S ⟶ X) [IsClosedImmersion ι] [IsIntegral S] [IsLocallyNoetherian S]
    [IsNormal S] (hι : Set.range ι.base = closure {w})
    {hgen : ∀ W : irreducibleComponents S, ι (componentGenericPoint S W) ∉
      (B - ∑ G ∈ J, Finsupp.single G 1).supp}
    {BS : QDivisor S} (hpb : (B - ∑ G ∈ J, Finsupp.single G 1).IsPullback ι hgen BS)
    (hpair : IsSNCSubboundaryPair (ι ≫ sX) BS) {F : Set X}
    (hF : IsSNCStratum (coeffOnePart B) F) (hFw : F ⊆ closure {w}) :
    IsSNCStratum (coeffOnePart BS) (ι.base ⁻¹' F) := by
  haveI : LocallyOfFiniteType sX := hB.isProjectiveVariety.toIsVariety.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hB.isProjectiveVariety.toIsVariety.toQuasiCompact
  haveI : LocallyOfFinitePresentation sX :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := sX)).mpr inferInstance
  haveI : Smooth sX := (MMP.Mori.isSmoothScheme_iff sX).1 hB.isSmoothScheme
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : CompactSpace S := ι.isClosedEmbedding.compactSpace
  have hQX : ∀ A : QDivisor X, A.IsQCartier :=
    MMP.Fourfold.isQCartier_of_isSmoothScheme hB.isSmoothScheme
  obtain ⟨hsmι, hker, hyJ⟩ := stratum_package sX hB.isSNC hJ hwJ hcw ι hι
  haveI := hsmι
  have hsnc1 : (coeffOnePart B).IsSNC sX :=
    hB.isSNC.of_support_subset (support_coeffOnePart_subset B)
  obtain ⟨JF, hJF, hmax⟩ := hF
  obtain ⟨v, hFv, hvJF, hcv⟩ := coheight_eq_card_of_isSNCStratum hsnc1 hJF hmax
  have hJFB : JF ⊆ B.support := hJF.trans (support_coeffOnePart_subset B)
  have hvw : v ∈ closure {w} := hFw (hFv ▸ subset_closure rfl)
  obtain ⟨u, hu⟩ : v ∈ Set.range ι.base := hι ▸ hvw
  have hu' : ι u = v := hu
  -- the components of `B` through `v`
  set T := B.support.filter (fun G => v ∈ G.support) with hT
  have hJT : J ⊆ T := fun G hG => Finset.mem_filter.mpr ⟨hJ hG,
    closure_minimal (Set.singleton_subset_iff.mpr (hwJ G hG)) G.idealSheaf.support.isClosed hvw⟩
  have hJFT : JF ⊆ T := fun G hG => Finset.mem_filter.mpr ⟨hJFB hG, hvJF G hG⟩
  obtain ⟨cT, hcT, hTcard⟩ := card_le_coheight_of_isSNC hB.isSNC v T (Finset.filter_subset _ _)
    (fun G hG => (Finset.mem_filter.mp hG).2)
  have hTJF : T = JF := by
    refine (Finset.eq_of_subset_of_card_le hJFT ?_).symm
    rw [hcv] at hcT
    have : cT = JF.card := by exact_mod_cast hcT.symm
    omega
  have hT1 : ∀ G ∈ T, B.coeff G = 1 := fun G hG =>
    coeff_eq_one_of_mem_support_coeffOnePart (hJF (hTJF ▸ hG))
  -- for each further component `G`, the stratum point of `J ∪ {G}` under `v`
  have hpt : ∀ G ∈ T \ J, ∃ Q : MMP.Mori.PrimeDivisor S, ι Q.genericPoint ∈ G.support ∧
      u ∈ Q.support ∧ BS.coeff Q = 1 := by
    intro G hG
    obtain ⟨hGT, hGJ⟩ := Finset.mem_sdiff.mp hG
    have hGB : G ∈ B.support := (Finset.mem_filter.mp hGT).1
    obtain ⟨ξ, hξv, hξJ, hcξ, -⟩ := exists_stratum_specializes hB.isSNC
      (Finset.insert_subset hGB hJ) (fun G' hG' => by
        rcases Finset.mem_insert.mp hG' with rfl | hG'
        · exact (Finset.mem_filter.mp hGT).2
        · exact (Finset.mem_filter.mp (hJT hG')).2)
    have hξw : ξ ∈ closure {w} := mem_closure_of_specializes_of_stratum sX hB.isSNC hJ hwJ hcw
      (fun G' hG' => hξJ G' (Finset.mem_insert_of_mem hG')) hξv hvw
    obtain ⟨y, hy⟩ : ξ ∈ Set.range ι.base := hι ▸ hξw
    have hy' : ι y = ξ := hy
    have hcy : Order.coheight y = 1 := by
      have h := coheight_map_eq_add_card hB.isSNC hJ ι y (hyJ y) (hker y)
      rw [hy', hcξ, Finset.card_insert_of_notMem hGJ] at h
      rw [coheight_eq_sub_of_add_eq h]
      simp
    set Q : MMP.Mori.PrimeDivisor S := AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hcy
    have hQy : Q.genericPoint = y := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne y hcy
    refine ⟨Q, by rw [hQy, hy']; exact hξJ G (Finset.mem_insert_self G J), ?_, ?_⟩
    · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      change u ∈ closure {Q.genericPoint}
      rw [hQy, ← specializes_iff_mem_closure]
      exact (ι.isEmbedding.isInducing.specializes_iff).mp (by rw [hy', hu']; exact hξv)
    · -- the restricted coefficient
      set A := B - ∑ G ∈ J, Finsupp.single G (1 : ℚ) with hA
      have hAD : A.support ⊆ B.support := support_sub_sum_single_subset B hJ
      have hAJ := coeff_sub_sum_single_eq_zero B hJ1
      rw [coeff_isPullback_of_stratum sX hB.isSNC hJ ι hyJ hker A hAD hAJ (hQX A) hpb Q, hA,
        sum_filter_sub_sum_single B J hJ1]
      have hfil : B.support.filter (fun E => E ∉ J ∧ ι Q.genericPoint ∈ E.support) = {G} := by
        ext E
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hEB, hEJ, hQE⟩
          by_contra hne
          have := card_le_of_stratum hB.isSNC hJ ι Q.genericPoint (hyJ _) (hker _)
            (c := 1) (by rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]; rfl) {E, G}
            (Finset.insert_subset hEB (Finset.singleton_subset_iff.mpr hGB))
            (Finset.disjoint_left.mpr fun G' hG' hG'J => by
              rcases Finset.mem_insert.mp hG' with rfl | hG'
              · exact hEJ hG'J
              · rw [Finset.mem_singleton] at hG'; subst hG'; exact hGJ hG'J)
            (fun G' hG' => by
              rcases Finset.mem_insert.mp hG' with rfl | hG'
              · exact hQE
              · rw [Finset.mem_singleton] at hG'; subst hG'
                rw [hQy, hy']; exact hξJ _ (Finset.mem_insert_self _ J))
          rw [Finset.card_pair hne] at this
          omega
        · rintro rfl
          exact ⟨hGB, hGJ, by rw [hQy, hy']; exact hξJ _ (Finset.mem_insert_self _ J)⟩
      rw [hfil, Finset.sum_singleton, hT1 G hGT]
  choose Qf hQfG hQfu hQf1 using hpt
  set Qg : {G // G ∈ T \ J} → MMP.Mori.PrimeDivisor S := fun G => Qf G.1 G.2 with hQg
  -- the restricted components are distinct
  have hinj : Function.Injective Qg := by
    rintro ⟨G₁, hG₁⟩ ⟨G₂, hG₂⟩ h12
    simp only [hQg] at h12
    refine Subtype.ext ?_
    by_contra hne
    obtain ⟨hG₁T, hG₁J⟩ := Finset.mem_sdiff.mp hG₁
    obtain ⟨hG₂T, hG₂J⟩ := Finset.mem_sdiff.mp hG₂
    have := card_le_of_stratum hB.isSNC hJ ι (Qf G₁ hG₁).genericPoint (hyJ _) (hker _)
      (c := 1) (by rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]; rfl) {G₁, G₂}
      (Finset.insert_subset (Finset.mem_filter.mp hG₁T).1
        (Finset.singleton_subset_iff.mpr (Finset.mem_filter.mp hG₂T).1))
      (Finset.disjoint_left.mpr fun G' hG' hG'J => by
        rcases Finset.mem_insert.mp hG' with rfl | hG'
        · exact hG₁J hG'J
        · rw [Finset.mem_singleton] at hG'; subst hG'; exact hG₂J hG'J)
      (fun G' hG' => by
        rcases Finset.mem_insert.mp hG' with rfl | hG'
        · exact hQfG _ hG₁
        · rw [Finset.mem_singleton] at hG'; subst hG'; rw [h12]; exact hQfG _ hG₂)
    rw [Finset.card_pair hne] at this
    omega
  -- the codimension of `u` in `S`
  have hcu : Order.coheight u = ((T \ J).attach.image Qg).card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_attach, Finset.card_sdiff_of_subset hJT,
      hTJF]
    have h := coheight_map_eq_add_card hB.isSNC hJ ι u (hyJ u) (hker u)
    rw [hu', hcv] at h
    rw [coheight_eq_sub_of_add_eq h]
  have hsncS : (coeffOnePart BS).IsSNC (ι ≫ sX) :=
    hpair.isSNC.of_support_subset (support_coeffOnePart_subset BS)
  have hst := isSNCStratum_closure_singleton hsncS u ((T \ J).attach.image Qg) (fun Q hQ => by
      obtain ⟨G, -, rfl⟩ := Finset.mem_image.mp hQ
      exact mem_support_coeffOnePart (hQf1 G.1 G.2))
    (fun Q hQ => by
      obtain ⟨G, -, rfl⟩ := Finset.mem_image.mp hQ
      exact hQfu G.1 G.2) hcu
  have hpre : ι.base ⁻¹' F = closure {u} := by
    rw [hFv, ι.isEmbedding.isInducing.closure_eq_preimage_closure_image, Set.image_singleton, hu']
  rw [hpre]
  exact hst

open scoped Classical in
/-- **Floor strata of the restricted pair are floor strata.** In the situation of
`isSNCStratum_preimage_of_stratum`, the image in `X` of a floor stratum of `(S, B_S)` is a floor
stratum of `(X, B)`: a coefficient-one prime `Q` of `S` lies on exactly one component `E_Q ∉ J`
of `B`, of coefficient one, distinct primes give distinct `E_Q`, and with `J` these are
`codim` floor components through the image of the generic point. -/
private theorem isSNCStratum_image_of_stratum {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {B : QDivisor X} (hB : IsSNCSubboundaryPair sX B)
    {J : Finset (MMP.Mori.PrimeDivisor X)} (hJ : J ⊆ B.support) (hJ1 : ∀ G ∈ J, B.coeff G = 1)
    {w : X} (hwJ : ∀ G ∈ J, w ∈ G.support) (hcw : Order.coheight w = J.card)
    {S : Scheme.{0}} (ι : S ⟶ X) [IsClosedImmersion ι] [IsIntegral S] [IsLocallyNoetherian S]
    [IsNormal S] (hι : Set.range ι.base = closure {w})
    {hgen : ∀ W : irreducibleComponents S, ι (componentGenericPoint S W) ∉
      (B - ∑ G ∈ J, Finsupp.single G 1).supp}
    {BS : QDivisor S} (hpb : (B - ∑ G ∈ J, Finsupp.single G 1).IsPullback ι hgen BS)
    (hpair : IsSNCSubboundaryPair (ι ≫ sX) BS) {A : Set S}
    (hA : IsSNCStratum (coeffOnePart BS) A) :
    IsSNCStratum (coeffOnePart B) (ι.base '' A) := by
  haveI : LocallyOfFiniteType sX := hB.isProjectiveVariety.toIsVariety.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hB.isProjectiveVariety.toIsVariety.toQuasiCompact
  haveI : LocallyOfFinitePresentation sX :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := sX)).mpr inferInstance
  haveI : Smooth sX := (MMP.Mori.isSmoothScheme_iff sX).1 hB.isSmoothScheme
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : CompactSpace S := ι.isClosedEmbedding.compactSpace
  have hQX : ∀ A : QDivisor X, A.IsQCartier :=
    MMP.Fourfold.isQCartier_of_isSmoothScheme hB.isSmoothScheme
  obtain ⟨hsmι, hker, hyJ⟩ := stratum_package sX hB.isSNC hJ hwJ hcw ι hι
  haveI := hsmι
  have hsncS : (coeffOnePart BS).IsSNC (ι ≫ sX) :=
    hpair.isSNC.of_support_subset (support_coeffOnePart_subset BS)
  obtain ⟨JA, hJA, hmax⟩ := hA
  obtain ⟨a, hAa, haJA, hca⟩ := coheight_eq_card_of_isSNCStratum hsncS hJA hmax
  set Bd := B - ∑ G ∈ J, Finsupp.single G (1 : ℚ) with hBd
  have hBdD : Bd.support ⊆ B.support := support_sub_sum_single_subset B hJ
  have hBdJ := coeff_sub_sum_single_eq_zero B hJ1
  -- each coefficient-one prime of `S` lies on a unique further component of coefficient one
  have hcomp : ∀ Q ∈ JA, ∃ E ∈ B.support, E ∉ J ∧ ι Q.genericPoint ∈ E.support ∧
      B.coeff E = 1 := by
    intro Q hQ
    have h1 := coeff_eq_one_of_mem_support_coeffOnePart (hJA hQ)
    rw [coeff_isPullback_of_stratum sX hB.isSNC hJ ι hyJ hker Bd hBdD hBdJ (hQX Bd) hpb Q, hBd,
      sum_filter_sub_sum_single B J hJ1] at h1
    set Fl := B.support.filter (fun E => E ∉ J ∧ ι Q.genericPoint ∈ E.support) with hFl
    have hFlc : Fl.card ≤ 1 := card_le_of_stratum hB.isSNC hJ ι Q.genericPoint (hyJ _) (hker _)
      (c := 1) (by rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]; rfl) Fl
      (Finset.filter_subset _ _)
      (Finset.disjoint_left.mpr fun G hG hGJ => (Finset.mem_filter.mp hG).2.1 hGJ)
      (fun G hG => (Finset.mem_filter.mp hG).2.2)
    obtain ⟨E, hFlE⟩ : ∃ E, Fl = {E} := by
      have hne : Fl.Nonempty := by
        by_contra h
        rw [Finset.not_nonempty_iff_eq_empty] at h
        rw [h, Finset.sum_empty] at h1
        norm_num at h1
      exact Finset.card_eq_one.mp (le_antisymm hFlc (Finset.card_pos.mpr hne))
    have hEFl : E ∈ Fl := hFlE ▸ Finset.mem_singleton_self E
    obtain ⟨hEB, hEJ, hQE⟩ := Finset.mem_filter.mp hEFl
    rw [hFlE, Finset.sum_singleton] at h1
    exact ⟨E, hEB, hEJ, hQE, h1⟩
  choose Ef hEfB hEfJ hEfQ hEf1 using hcomp
  set Eg : {Q // Q ∈ JA} → MMP.Mori.PrimeDivisor X := fun Q => Ef Q.1 Q.2 with hEg
  have hinj : Function.Injective Eg := by
    rintro ⟨Q₁, hQ₁⟩ ⟨Q₂, hQ₂⟩ h12
    simp only [hEg] at h12
    refine Subtype.ext ?_
    exact eq_of_mem_support_of_stratum hB.isSNC hJ ι hyJ hker (hEfB Q₁ hQ₁) (hEfJ Q₁ hQ₁)
      (hEfQ Q₁ hQ₁) (h12 ▸ hEfQ Q₂ hQ₂) (haJA Q₁ hQ₁) (haJA Q₂ hQ₂)
  -- the floor components through `ι a`
  set T := J ∪ JA.attach.image Eg with hT
  have hdisj : Disjoint J (JA.attach.image Eg) := Finset.disjoint_left.mpr fun G hGJ hG => by
    obtain ⟨Q, -, rfl⟩ := Finset.mem_image.mp hG
    exact hEfJ Q.1 Q.2 hGJ
  have hTc : T.card = J.card + JA.card := by
    rw [hT, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinj,
      Finset.card_attach]
  have hTsupp : T ⊆ (coeffOnePart B).support := by
    intro G hG
    rcases Finset.mem_union.mp hG with hG | hG
    · exact mem_support_coeffOnePart (hJ1 G hG)
    · obtain ⟨Q, -, rfl⟩ := Finset.mem_image.mp hG
      exact mem_support_coeffOnePart (hEf1 Q.1 Q.2)
  have hTa : ∀ G ∈ T, ι a ∈ G.support := by
    intro G hG
    rcases Finset.mem_union.mp hG with hG | hG
    · exact hyJ a G hG
    · obtain ⟨Q, -, rfl⟩ := Finset.mem_image.mp hG
      have hsp : Q.1.genericPoint ⤳ a := by
        rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact haJA Q.1 Q.2
      exact (ι.base.hom.map_specializes hsp).mem_closed (Ef Q.1 Q.2).idealSheaf.support.isClosed
        (hEfQ Q.1 Q.2)
  have hcaι : Order.coheight (ι a) = T.card := by
    have h := coheight_map_eq_add_card hB.isSNC hJ ι a (hyJ a) (hker a)
    rw [hca] at h
    have h2 : (((JA.card + J.card : ℕ) : ℕ∞) : WithBot ℕ∞) =
        ((Order.coheight (ι a) : ℕ∞) : WithBot ℕ∞) := by rw [← h]; push_cast; rfl
    have h3 := WithBot.coe_injective h2
    rw [hTc, ← h3]
    push_cast
    ring
  have hsnc1 : (coeffOnePart B).IsSNC sX :=
    hB.isSNC.of_support_subset (support_coeffOnePart_subset B)
  have hst := isSNCStratum_closure_singleton hsnc1 (ι a) T hTsupp hTa hcaι
  have himg : ι.base '' A = closure {ι a} := by
    rw [hAa, ← ι.isClosedMap.closure_image_eq_of_continuous ι.continuous, Set.image_singleton]
  rw [himg]
  exact hst

/-- The underlying function of a composite of ring homomorphisms. -/
private lemma coe_comp_hom {P Q R : CommRingCat.{0}} (a : P ⟶ Q) (b : Q ⟶ R) :
    (⇑(ConcreteCategory.hom (a ≫ b)) : P → R) =
      ⇑(ConcreteCategory.hom b) ∘ ⇑(ConcreteCategory.hom a) :=
  funext fun t => ConcreteCategory.comp_apply a b t

/-- The residue field maps of a closed immersion are bijective. -/
private lemma bijective_residueFieldMap_of_isClosedImmersion {P Q : Scheme.{0}} (ι : P ⟶ Q)
    [IsClosedImmersion ι] (x : P) : Function.Bijective (ι.residueFieldMap x) := by
  refine ⟨(ι.residueFieldMap x).hom.injective, ?_⟩
  have hs : Function.Surjective (ι.stalkMap x ≫ P.residue x) := by
    rw [coe_comp_hom]
    exact (P.residue_surjective x).comp (SurjectiveOnStalks.stalkMap_surjective ι x)
  rw [← Scheme.residue_residueFieldMap, coe_comp_hom] at hs
  exact Function.Surjective.of_comp hs

/-- An isomorphism of stalks induces a bijection of residue fields. -/
private lemma bijective_residueFieldMap_of_isIso_stalkMap {P Q : Scheme.{0}} (f : P ⟶ Q) (x : P)
    [IsIso (f.stalkMap x)] : Function.Bijective (f.residueFieldMap x) := by
  refine ⟨(f.residueFieldMap x).hom.injective, ?_⟩
  have hs : Function.Surjective (f.stalkMap x ≫ P.residue x) := by
    rw [coe_comp_hom]
    exact (P.residue_surjective x).comp (ConcreteCategory.bijective_of_isIso _).2
  rw [← Scheme.residue_residueFieldMap, coe_comp_hom] at hs
  exact Function.Surjective.of_comp hs

/-- The residue field map of a composite, as a function. -/
private lemma coe_residueFieldMap_comp {P Q R : Scheme.{0}} (f : P ⟶ Q) (g : Q ⟶ R) (x : P) :
    (⇑(ConcreteCategory.hom ((f ≫ g).residueFieldMap x)) : _ → _) =
      ⇑(ConcreteCategory.hom (f.residueFieldMap x)) ∘
        ⇑(ConcreteCategory.hom (g.residueFieldMap (f x))) := by
  ext t
  exact congrArg (fun φ : R.residueField ((f ≫ g) x) ⟶ P.residueField x => ConcreteCategory.hom φ t)
    (Scheme.residueFieldMap_comp f g x)

/-- Bijectivity of residue field maps is compatible with composition by a bijective one. -/
private lemma bijective_residueFieldMap_comp_iff {P Q R : Scheme.{0}} (f : P ⟶ Q) (g : Q ⟶ R)
    (x : P) (hf : Function.Bijective (f.residueFieldMap x)) :
    Function.Bijective ((f ≫ g).residueFieldMap x) ↔
      Function.Bijective (g.residueFieldMap (f x)) := by
  rw [coe_residueFieldMap_comp]
  exact Function.Bijective.of_comp_iff' hf _

/-- **Birationality of a map of strata from residue fields.** Let `ι_A : A ⟶ Y`, `ι_B : B ⟶ X` be
integral closed subschemes and `g : A ⟶ B` a morphism over `h : Y ⟶ X` sending the generic point
of `A` to that of `B`. If `h` induces a bijection `κ(h(η_A)) → κ(η_A)` of residue fields, then
`g` is birational: at the generic points the stalks are these residue fields. -/
private lemma isBirationalMorphism_of_bijective_residueFieldMap {A B Y X : Scheme.{0}}
    [IsIntegral A] [IsIntegral B] (ιA : A ⟶ Y) (ιB : B ⟶ X) [IsClosedImmersion ιA]
    [IsClosedImmersion ιB] (h : Y ⟶ X) (g : A ⟶ B) [LocallyOfFiniteType g]
    (hg : g ≫ ιB = ιA ≫ h) (hgen : h (ιA (genericPoint A)) = ιB (genericPoint B))
    (hbij : Function.Bijective (h.residueFieldMap (ιA (genericPoint A)))) :
    IsBirationalMorphism g := by
  have hgA : g (genericPoint A) = genericPoint B := ιB.isEmbedding.injective (by
    rw [← Scheme.Hom.comp_apply, hg, Scheme.Hom.comp_apply, hgen])
  haveI : IsDominant g := ⟨by
    refine dense_iff_closure_eq.mpr (Set.eq_univ_of_univ_subset ?_)
    rw [← (genericPoint_spec B).def]
    exact closure_mono (Set.singleton_subset_iff.mpr ⟨_, hgA⟩)⟩
  have h1 : Function.Bijective ((ιA ≫ h).residueFieldMap (genericPoint A)) :=
    (bijective_residueFieldMap_comp_iff ιA h _
      (bijective_residueFieldMap_of_isClosedImmersion ιA _)).mpr hbij
  have h2 : Function.Bijective ((g ≫ ιB).residueFieldMap (genericPoint A)) := by
    rw [hg]; exact h1
  rw [coe_residueFieldMap_comp] at h2
  have h3 : Function.Bijective (g.residueFieldMap (genericPoint A)) :=
    (Function.Bijective.of_comp_iff _ (bijective_residueFieldMap_of_isClosedImmersion ιB _)).mp h2
  have hB : IsIso (B.residue (g (genericPoint A))) := by
    rw [hgA]; exact isIso_residue_genericPoint B
  haveI := isIso_residue_genericPoint A
  have hfac : g.stalkMap (genericPoint A) = B.residue (g (genericPoint A)) ≫
      g.residueFieldMap (genericPoint A) ≫ inv (A.residue (genericPoint A)) := by
    rw [← Category.assoc, IsIso.eq_comp_inv]
    exact (Scheme.residue_residueFieldMap g _).symm
  haveI : IsIso (g.residueFieldMap (genericPoint A)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr h3
  haveI : IsIso (g.stalkMap (genericPoint A)) := by rw [hfac]; infer_instance
  have hbir : AlgebraicGeometry.IsBirational g := by
    simp only [AlgebraicGeometry.isBirational_iff, genericPoints_eq_singleton, Set.bijOn_singleton,
      Set.mem_singleton_iff, forall_eq]
    exact ⟨hgA, inferInstance⟩
  haveI : Finite (irreducibleComponents A) := by
    rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
  haveI : Finite (irreducibleComponents B) := by
    rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
  obtain ⟨U, V, hUV, hU, hV, hiso⟩ :=
    exists_dense_opens_isIso_resLE_of_isBirational g hbir (Or.inl ⟨inferInstance, inferInstance⟩)
  exact MMP.Flips.isBirationalMorphism_of_isIso_resLE g U V hU.nonempty hV.nonempty hUV hiso

/-- At the generic points, a birational morphism of integral schemes induces a bijection of
residue fields. -/
private lemma bijective_residueFieldMap_genericPoint {P Q : Scheme.{0}} [IsIntegral P]
    [IsIntegral Q] (f : P ⟶ Q) [IsDominant f] (hf : Function.Bijective (functionFieldMap f)) :
    Function.Bijective (f.residueFieldMap (genericPoint P)) := by
  let e := Q.presheaf.stalkCongr (Inseparable.of_eq (map_genericPoint_of_isDominant f).symm)
  haveI : IsIso (e.hom ≫ f.stalkMap (genericPoint P)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hf
  haveI : IsIso (f.stalkMap (genericPoint P)) := IsIso.of_isIso_comp_left e.hom _
  exact bijective_residueFieldMap_of_isIso_stalkMap f _

open scoped Classical in
/-- **Floor strata are snc subboundary pairs.** Let `(X, B)` be an snc subboundary pair and
`closure {w}` a stratum cut out by `c` components `J` of `B` of coefficient one, with
`codim w = |J|`. Then there is an integral closed subscheme `ι : S ⟶ X` onto `closure {w}` such
that the restriction `B_S = (B - ∑_{G ∈ J} G)|_S` makes `(S, B_S)` an snc subboundary pair: peel
off one component at a time, each step being adjunction to a coefficient-one prime divisor. -/
private theorem exists_isSNCSubboundaryPair_of_stratum {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {B : QDivisor X} (hB : IsSNCSubboundaryPair sX B) (c : ℕ) :
    ∀ {J : Finset (MMP.Mori.PrimeDivisor X)}, J.card = c → J ⊆ B.support →
      (∀ G ∈ J, B.coeff G = 1) → ∀ {w : X}, (∀ G ∈ J, w ∈ G.support) →
      Order.coheight w = J.card →
      ∃ (S : Scheme.{0}) (ι : S ⟶ X) (_ : IsClosedImmersion ι) (_ : IsIntegral S)
        (_ : IsLocallyNoetherian S) (_ : IsNormal S) (BS : QDivisor S)
        (hgen : ∀ W : irreducibleComponents S, ι (componentGenericPoint S W) ∉
          (B - ∑ G ∈ J, Finsupp.single G 1).supp),
        Set.range ι.base = closure {w} ∧
          (B - ∑ G ∈ J, Finsupp.single G 1).IsPullback ι hgen BS ∧
          IsSNCSubboundaryPair (ι ≫ sX) BS := by
  haveI : LocallyOfFiniteType sX := hB.isProjectiveVariety.toIsVariety.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hB.isProjectiveVariety.toIsVariety.toQuasiCompact
  haveI : LocallyOfFinitePresentation sX :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := sX)).mpr inferInstance
  haveI : Smooth sX := (MMP.Mori.isSmoothScheme_iff sX).1 hB.isSmoothScheme
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have hQX : ∀ A : QDivisor X, A.IsQCartier :=
    MMP.Fourfold.isQCartier_of_isSmoothScheme hB.isSmoothScheme
  induction c with
  | zero =>
    intro J hJc hJ hJ1 w hwJ hcw
    have hJe : J = ∅ := Finset.card_eq_zero.mp hJc
    subst hJe
    have hw : w = genericPoint X := by
      have hle : w ≤ genericPoint X := genericPoint_specializes w
      rw [Finset.card_empty, CharP.cast_eq_zero] at hcw
      exact (Specializes.antisymm (Order.coheight_eq_zero.mp hcw hle) hle).eq
    subst hw
    have hgen : ∀ W : irreducibleComponents X, (𝟙 X : X ⟶ X) (componentGenericPoint X W) ∉
        (B - ∑ G ∈ (∅ : Finset (MMP.Mori.PrimeDivisor X)), Finsupp.single G 1).supp :=
      fun W => by
        rw [componentGenericPoint_eq_genericPoint]
        exact genericPoint_notMem_supp _
    have hp := QDivisor.isPullback_pullback (hQX _) hgen
    have heq : (B - ∑ G ∈ (∅ : Finset (MMP.Mori.PrimeDivisor X)), Finsupp.single G 1).pullback
        (hQX _) hgen = B := by
      ext Q
      rw [qcoeff_isPullback_eq_of_isIso (hQX _) hp Q Q rfl, Finset.sum_empty, sub_zero]
    rw [heq] at hp
    refine ⟨X, 𝟙 X, inferInstance, inferInstance, inferInstance, inferInstance, B, hgen, ?_, hp,
      by rw [Category.id_comp]; exact hB⟩
    simp [(genericPoint_spec X).def]
  | succ c ih =>
    intro J hJc hJ hJ1 w hwJ hcw
    -- a component `E ∈ J` and the remaining `J'`
    obtain ⟨E, hEJ⟩ : J.Nonempty := Finset.card_pos.mp (by omega)
    set J' := J.erase E with hJ'
    have hJ'c : J'.card = c := by rw [hJ', Finset.card_erase_of_mem hEJ, hJc]; rfl
    have hJ'J : J' ⊆ J := Finset.erase_subset E J
    have hEJ' : E ∉ J' := Finset.notMem_erase E J
    have hJ'B : J' ⊆ B.support := hJ'J.trans hJ
    -- the stratum through `w` cut out by `J'`
    obtain ⟨ξ, hξw, hξJ, hcξ, -⟩ :=
      exists_stratum_specializes hB.isSNC hJ'B (fun G hG => hwJ G (hJ'J hG))
    obtain ⟨V, ιV, _, _, _, _, BV, hgenV, hrV, hpbV, hpairV⟩ :=
      ih hJ'c hJ'B (fun G hG => hJ1 G (hJ'J hG)) hξJ hcξ
    haveI : CompactSpace V := ιV.isClosedEmbedding.compactSpace
    obtain ⟨hsmV, hkerV, hyJV⟩ := stratum_package sX hB.isSNC hJ'B hξJ hcξ ιV hrV
    have hQV : ∀ A : QDivisor V, A.IsQCartier :=
      MMP.Fourfold.isQCartier_of_isSmoothScheme hpairV.isSmoothScheme
    -- the prime divisor `P` of `V` under `w`
    have hwV : w ∈ closure {ξ} := specializes_iff_mem_closure.mp hξw
    obtain ⟨y, hy⟩ : w ∈ Set.range ιV.base := hrV ▸ hwV
    have hcy : Order.coheight y = 1 := by
      have h := coheight_map_eq_add_card hB.isSNC hJ'B ιV y (hyJV y) (hkerV y)
      have hy' : ιV y = w := hy
      rw [hy', hcw, hJc, hJ'c] at h
      obtain ⟨a, ha⟩ : ∃ a : ℕ, Order.coheight y = a := by
        refine ⟨(Order.coheight y).toNat, (ENat.coe_toNat ?_).symm⟩
        intro htop
        rw [htop] at h
        have h2 : ((⊤ + (c : ℕ∞) : ℕ∞) : WithBot ℕ∞) = ((c + 1 : ℕ∞) : WithBot ℕ∞) := by
          exact_mod_cast h
        rw [top_add] at h2
        exact absurd (WithBot.coe_injective h2) (by
          intro h3; exact ENat.top_ne_coe (c + 1) (by exact_mod_cast h3))
      rw [ha] at h ⊢
      have : a + c = c + 1 := by exact_mod_cast h
      exact_mod_cast (by omega : a = 1)
    set P : MMP.Mori.PrimeDivisor V :=
      AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hcy with hPdef
    have hPy : P.genericPoint = y := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne y hcy
    have hPE : ιV P.genericPoint ∈ E.support := by rw [hPy, hy]; exact hwJ E hEJ
    have hPw : ιV P.genericPoint = w := by rw [hPy]; exact hy
    -- `A = B - ∑_{J'} G`
    set A := B - ∑ G ∈ J', Finsupp.single G (1 : ℚ) with hA
    have hAD : A.support ⊆ B.support := support_sub_sum_single_subset B hJ'B
    have hAJ := coeff_sub_sum_single_eq_zero B (fun G hG => hJ1 G (hJ'J hG))
    -- `B_V(P) = 1`
    have hBVP : BV.coeff P = 1 := by
      rw [coeff_isPullback_of_stratum sX hB.isSNC hJ'B ιV hyJV hkerV A hAD hAJ (hQX A) hpbV P]
      have hfil : A.support.filter (fun E' => ιV P.genericPoint ∈ E'.support) = {E} := by
        ext E'
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hE', hPE'⟩
          by_contra hne
          have hE'J : E' ∉ J' := fun h => (Finsupp.mem_support_iff.mp hE') (hAJ E' h)
          have := card_le_of_stratum hB.isSNC hJ'B ιV P.genericPoint (hyJV _) (hkerV _)
            (c := 1) (by rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]; rfl) {E', E}
            (Finset.insert_subset (hAD hE') (Finset.singleton_subset_iff.mpr (hJ hEJ)))
            (Finset.disjoint_left.mpr fun G hG hGJ => by
              rcases Finset.mem_insert.mp hG with rfl | hG
              · exact hE'J hGJ
              · rw [Finset.mem_singleton] at hG; subst hG; exact hEJ' hGJ)
            (fun G hG => by
              rcases Finset.mem_insert.mp hG with rfl | hG
              · exact hPE'
              · rw [Finset.mem_singleton] at hG; subst hG; exact hPE)
          rw [Finset.card_pair hne] at this
          omega
        · rintro rfl
          refine ⟨Finsupp.mem_support_iff.mpr ?_, hPE⟩
          change A.coeff E' ≠ 0
          rw [hA, coeff_sub_sum_single, if_neg hEJ', hJ1 E' hEJ]
          norm_num
      rw [hfil, Finset.sum_singleton, hA, coeff_sub_sum_single, if_neg hEJ', hJ1 E hEJ, sub_zero]
    -- the prime divisor `P` as a smooth integral scheme
    have hPsupp : P ∈ BV.support := Finsupp.mem_support_iff.mpr (by
      change BV.coeff P ≠ 0; rw [hBVP]; norm_num)
    haveI := P.integral
    have hsmP : IsSmoothScheme (P.idealSheaf.subschemeι ≫ ιV ≫ sX) := hpairV.isSNC.1 P hPsupp
    haveI : LocallyOfFiniteType (ιV ≫ sX) :=
      hpairV.isProjectiveVariety.toIsVariety.toLocallyOfFiniteType
    haveI : LocallyOfFinitePresentation (P.idealSheaf.subschemeι ≫ ιV ≫ sX) :=
      (LocallyOfFinitePresentation.iff_locallyOfFiniteType
        (f := P.idealSheaf.subschemeι ≫ ιV ≫ sX)).mpr inferInstance
    haveI : Smooth (P.idealSheaf.subschemeι ≫ ιV ≫ sX) := (MMP.Mori.isSmoothScheme_iff _).1 hsmP
    haveI : IsLocallyNoetherian P.idealSheaf.subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian (P.idealSheaf.subschemeι ≫ ιV ≫ sX)
    haveI : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
    haveI : IsNormal P.idealSheaf.subscheme :=
      AlgebraicGeometry.isNormal_of_smooth (P.idealSheaf.subschemeι ≫ ιV ≫ sX)
    haveI : CompactSpace P.idealSheaf.subscheme :=
      P.idealSheaf.subschemeι.isClosedEmbedding.compactSpace
    have hjP : Set.range P.idealSheaf.subschemeι.base = (P.support : Set V) := by
      rw [Scheme.IdealSheafData.range_subschemeι]
    have hjgen : P.idealSheaf.subschemeι (genericPoint P.idealSheaf.subscheme) = P.genericPoint :=
      map_genericPoint_eq_of_range _ P hjP
    have hgen1 : ∀ W : irreducibleComponents P.idealSheaf.subscheme,
        P.idealSheaf.subschemeι (componentGenericPoint _ W) ∉ (BV - Finsupp.single P 1).supp := by
      intro W hW
      rw [componentGenericPoint_eq_genericPoint, hjgen] at hW
      obtain ⟨Q, hQ0, hQ⟩ := DivisorWithCoeffs.mem_supp_iff.mp hW
      obtain rfl := MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support hQ
      apply hQ0
      rw [DivisorWithCoeffs.coeff_sub, hBVP]
      change (1 : ℚ) - (Finsupp.single P (1 : ℚ)) P = 0
      rw [Finsupp.single_eq_same, sub_self]
    have hBT := QDivisor.isPullback_pullback (hQV _) hgen1
    have hpairT := isSNCSubboundaryPair_of_isPullback_sub_single hpairV P hBVP hBT
    -- the composite pull-back
    have hJsum : ∑ G ∈ J, Finsupp.single G (1 : ℚ) =
        Finsupp.single E 1 + ∑ G ∈ J', Finsupp.single G (1 : ℚ) := by
      rw [hJ', Finset.add_sum_erase J (fun G => Finsupp.single G (1 : ℚ)) hEJ]
    have hsumJ : B - ∑ G ∈ J, Finsupp.single G 1 = A - Finsupp.single E 1 := by
      rw [hJsum, hA]; abel
    have hgen2' : ∀ W : irreducibleComponents P.idealSheaf.subscheme,
        (P.idealSheaf.subschemeι ≫ ιV) (componentGenericPoint _ W) ∉
          (B - ∑ G ∈ J, Finsupp.single G 1).supp := by
      intro W
      rw [componentGenericPoint_eq_genericPoint, Scheme.Hom.comp_apply, hjgen, hPw]
      intro hmem
      obtain ⟨G, hG0, hwG⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
      rw [coeff_sub_sum_single] at hG0
      by_cases hGJ : G ∈ J
      · rw [if_pos hGJ, hJ1 G hGJ, sub_self] at hG0; exact hG0 rfl
      · rw [if_neg hGJ, sub_zero] at hG0
        have hGB : G ∈ B.support := Finsupp.mem_support_iff.mpr hG0
        obtain ⟨c', hc', hcard⟩ := card_le_coheight_of_isSNC hB.isSNC w (insert G J)
          (Finset.insert_subset hGB hJ) (fun G' hG' => by
            rcases Finset.mem_insert.mp hG' with rfl | hG'
            · exact hwG
            · exact hwJ G' hG')
        rw [hcw] at hc'
        have hcJ : c' = J.card := by exact_mod_cast hc'.symm
        rw [Finset.card_insert_of_notMem hGJ, hcJ] at hcard
        omega
    have hgen2 : ∀ W : irreducibleComponents P.idealSheaf.subscheme,
        (P.idealSheaf.subschemeι ≫ ιV) (componentGenericPoint _ W) ∉
          (A - Finsupp.single E 1).supp := by
      rw [← hsumJ]; exact hgen2'
    have hRT := isPullback_sub_single_comp_of_stratum sX hB.isSNC hJ'B ιV hyJV hkerV hQX hQV
      P.idealSheaf.subschemeι P hjP (hJ hEJ) hEJ' hPE A hAD hAJ hpbV hBT hgen2
    have hRT' := qdivisor_isPullback_congr hsumJ.symm (hB₂ := hgen2') hRT
    refine ⟨P.idealSheaf.subscheme, P.idealSheaf.subschemeι ≫ ιV, inferInstance, inferInstance,
      inferInstance, inferInstance, _, hgen2', ?_, hRT', by rw [Category.assoc]; exact hpairT⟩
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hjP,
      AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      ← ιV.isClosedMap.closure_image_eq_of_continuous ιV.continuous, Set.image_singleton, hPw]

/-- The generic point of a closed integral subscheme onto `closure {w}` is `w`. -/
private lemma map_genericPoint_eq_of_range_closure {S X : Scheme.{0}} [IsIntegral S] (ι : S ⟶ X)
    [IsClosedImmersion ι] {w : X} (hι : Set.range ι.base = closure {w}) :
    ι (genericPoint S) = w := by
  have h1 : IsGenericPoint (ι (genericPoint S)) (Set.range ι.base) := by
    have := (genericPoint_spec S).image ι.base.hom.continuous
    rwa [Set.image_univ, ι.isClosedEmbedding.isClosed_range.closure_eq] at this
  have h2 : IsGenericPoint w (Set.range ι.base) := by rw [hι]; exact isGenericPoint_closure
  exact h1.eq h2

/-- **The lifting property in dimension `n`.** Every floor stratum of the target of a crepant
projective birational morphism `(Y, C) ⟶ (X, B)` of `n`-dimensional snc subboundary pairs, with
`B` effective, is the image of a floor stratum of `Y` mapping birationally onto it, in the form:
the generic point of the source stratum maps to that of the target with bijective residue field
map. -/
private def LiftProperty (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (n : ℕ) : Prop :=
  ∀ {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {B : QDivisor X} {C : QDivisor Y}, IsSNCSubboundaryPair sX B → (∀ P, 0 ≤ B.coeff P) →
    IsSNCSubboundaryPair sY C → ∀ {KX : Divisor X}, KX.IsCanonicalDivisor sX n →
    ∀ {KY : Divisor Y}, KY.IsCanonicalDivisor sY n → ∀ (h : Y ⟶ X), h ≫ sX = sY →
    IsProjectiveMorphism h → ∀ (hbir : IsBirationalMorphism h),
    (∀ hY : IsNormalVariety k (h ≫ sX), IsCrepantBoundary sX n KX B h hY hbir C) →
    ∀ {F : Set X}, IsSNCStratum (coeffOnePart B) F →
    ∃ f' : Y, IsSNCStratum (coeffOnePart C) (closure {f'}) ∧ IsGenericPoint (h f') F ∧
      Function.Bijective (h.residueFieldMap f')

open scoped Classical in
/-- **Lifting inside a birational stratum.** Let `h : (Y, C) ⟶ (X, B)` be crepant, `B`
effective, `closure {r₀}` a floor stratum of `Y` (cut out by `J₀`) and `closure {r}` one of `X`
(cut out by `J`), with `h(r₀) = r` and `κ(r) → κ(r₀)` bijective. Granting the lifting property
in the dimension of these strata, every floor stratum `F ⊆ closure {r}` is the image of a floor
stratum of `Y` inside `closure {r₀}` mapping birationally onto it: restrict both pairs to the
strata, where `h` induces a crepant birational morphism of snc subboundary pairs, lift there and
come back. -/
private theorem exists_lift_of_stratum {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {B : QDivisor X} {C : QDivisor Y} (hB : IsSNCSubboundaryPair sX B) (hB0 : ∀ P, 0 ≤ B.coeff P)
    (hC : IsSNCSubboundaryPair sY C) {n : ℕ} {KX : Divisor X} (hKX : KX.IsCanonicalDivisor sX n)
    {KY : Divisor Y} (hKY : KY.IsCanonicalDivisor sY n)
    (h : Y ⟶ X) (hh : h ≫ sX = sY) (hproj : IsProjectiveMorphism h)
    (hbir : IsBirationalMorphism h)
    (hcrep : ∀ hY : IsNormalVariety k (h ≫ sX), IsCrepantBoundary sX n KX B h hY hbir C)
    {J₀ : Finset (MMP.Mori.PrimeDivisor Y)} (hJ₀ : J₀ ⊆ C.support) (hJ₀1 : ∀ G ∈ J₀, C.coeff G = 1)
    {r₀ : Y} (hr₀J : ∀ G ∈ J₀, r₀ ∈ G.support) (hcr₀ : Order.coheight r₀ = J₀.card)
    {J : Finset (MMP.Mori.PrimeDivisor X)} (hJ : J ⊆ B.support) (hJ1 : ∀ G ∈ J, B.coeff G = 1)
    {r : X} (hrJ : ∀ G ∈ J, r ∈ G.support) (hcr : Order.coheight r = J.card)
    (hr₀r : h r₀ = r) (hbij : Function.Bijective (h.residueFieldMap r₀))
    {m : ℕ} (hm : m + J.card = n) (hL : LiftProperty k m)
    {F : Set X} (hF : IsSNCStratum (coeffOnePart B) F) (hFr : F ⊆ closure {r}) :
    ∃ f' : Y, f' ∈ closure {r₀} ∧ IsSNCStratum (coeffOnePart C) (closure {f'}) ∧
      IsGenericPoint (h f') F ∧ Function.Bijective (h.residueFieldMap f') := by
  classical
  subst hh
  haveI hXv : AlgebraicGeometry.IsVariety k sX := hB.isProjectiveVariety.toIsVariety
  haveI : LocallyOfFiniteType sX := hXv.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hXv.toQuasiCompact
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : LocallyOfFinitePresentation sX :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := sX)).mpr inferInstance
  haveI : Smooth sX := (MMP.Mori.isSmoothScheme_iff sX).1 hB.isSmoothScheme
  haveI hYv : AlgebraicGeometry.IsVariety k (h ≫ sX) := hC.isProjectiveVariety.toIsVariety
  haveI : LocallyOfFiniteType (h ≫ sX) := hYv.toLocallyOfFiniteType
  haveI : QuasiCompact (h ≫ sX) := hYv.toQuasiCompact
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (h ≫ sX)
  haveI : IsProper h := isProper_of_isProjectiveMorphism h hproj
  haveI : IsDominant h := hbir.isDominant
  have hn := hKX.topologicalKrullDim_eq
  by_cases hJ₀e : J₀ = ∅
  · -- the whole of `Y`
    subst hJ₀e
    have hr₀ : r₀ = genericPoint Y := by
      have hle : r₀ ≤ genericPoint Y := genericPoint_specializes r₀
      rw [Finset.card_empty, CharP.cast_eq_zero] at hcr₀
      exact (Specializes.antisymm (Order.coheight_eq_zero.mp hcr₀ hle) hle).eq
    subst hr₀
    have hrg : r = genericPoint X := by rw [← hr₀r]; exact map_genericPoint_of_isDominant h
    subst hrg
    have hJc : J.card = 0 := by
      have : Order.coheight (genericPoint X) = 0 := Order.coheight_eq_zero.mpr fun b _ =>
        Scheme.le_iff_specializes.mpr (genericPoint_specializes b)
      rw [this] at hcr
      exact_mod_cast hcr.symm
    rw [hJc, add_zero] at hm
    subst hm
    obtain ⟨f', hf'1, hf'2, hf'3⟩ := hL hB hB0 hC hKX hKY h rfl hproj hbir hcrep hF
    refine ⟨f', ?_, hf'1, hf'2, hf'3⟩
    rw [(genericPoint_spec Y).def]; trivial
  -- the restricted pairs
  obtain ⟨SR, ιR, _, _, _, _, BR, hgenR, hrR, hpbR, hpairR⟩ :=
    exists_isSNCSubboundaryPair_of_stratum hB J.card rfl hJ hJ1 hrJ hcr
  obtain ⟨S₀, ι₀, _, _, _, _, C₀, hgen₀, hr₀', hpb₀, hpair₀⟩ :=
    exists_isSNCSubboundaryPair_of_stratum hC J₀.card rfl hJ₀ hJ₀1 hr₀J hcr₀
  haveI : CompactSpace S₀ := ι₀.isClosedEmbedding.compactSpace
  haveI : CompactSpace SR := ιR.isClosedEmbedding.compactSpace
  -- the induced morphism `g : S₀ ⟶ S_R`
  have hsub : Set.range (ι₀ ≫ h).base ⊆ Set.range ιR.base := by
    rw [hrR, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hr₀', ← hr₀r]
    exact image_closure_subset_closure_image h.continuous |>.trans (by rw [Set.image_singleton])
  obtain ⟨g, hg⟩ := exists_comp_eq_of_range_subset ιR (ι₀ ≫ h) hsub
  haveI : IsProper g := MorphismProperty.of_postcomp @IsProper g ιR
    (inferInstance : IsSeparated ιR) (by rw [hg]; exact (inferInstance : IsProper (ι₀ ≫ h)))
  have hgproj : IsProjectiveMorphism g := IsProjectiveMorphism.of_comp g ιR (by
    rw [hg]
    exact (MMP.isProjectiveMorphism_of_isClosedImmersion ι₀).comp hproj)
  have hgen0 : ι₀ (genericPoint S₀) = r₀ := map_genericPoint_eq_of_range_closure ι₀ hr₀'
  have hgenR : ιR (genericPoint SR) = r := map_genericPoint_eq_of_range_closure ιR hrR
  have hgb : IsBirationalMorphism g :=
    isBirationalMorphism_of_bijective_residueFieldMap ι₀ ιR h g hg (by rw [hgen0, hr₀r, hgenR])
      (by rw [hgen0]; exact hbij)
  haveI : IsDominant g := hgb.isDominant
  -- dimensions and canonical divisors
  have hdimR : topologicalKrullDim SR = m := by
    have h1 := topologicalKrullDim_add_coheight_of_range sX ιR hrR
    rw [hcr, hn] at h1
    have h2 := withBot_eq_sub_of_add_eq (b := J.card) (n := n) (by exact_mod_cast h1)
    rw [h2, ← hm, Nat.add_sub_cancel]
    rfl
  haveI : AlgebraicGeometry.IsVariety k (ιR ≫ sX) := hpairR.isProjectiveVariety.toIsVariety
  haveI : AlgebraicGeometry.IsVariety k (ι₀ ≫ h ≫ sX) := hpair₀.isProjectiveVariety.toIsVariety
  haveI : LocallyOfFiniteType (ιR ≫ sX) :=
    (inferInstance : AlgebraicGeometry.IsVariety k (ιR ≫ sX)).toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (g ≫ ιR ≫ sX) := by
    rw [← Category.assoc, hg, Category.assoc]
    exact (inferInstance : AlgebraicGeometry.IsVariety k (ι₀ ≫ h ≫ sX)).toLocallyOfFiniteType
  have hdim₀ : topologicalKrullDim S₀ = m :=
    topologicalKrullDim_eq_of_isBirationalMorphism (ιR ≫ sX) g hgb hdimR
  obtain ⟨KT, hKT⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (ιR ≫ sX)
    hpairR.isSmoothScheme hdimR
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (ι₀ ≫ h ≫ sX)
    hpair₀.isSmoothScheme hdim₀
  -- crepancy of the restriction
  have hFst : IsSNCStratum (coeffOnePart C) (Set.range ι₀.base) := by
    rw [hr₀']
    exact isSNCStratum_closure_singleton
      (hC.isSNC.of_support_subset (support_coeffOnePart_subset C)) r₀ J₀
      (fun G hG => mem_support_coeffOnePart (hJ₀1 G hG)) hr₀J hcr₀
  have hFY : Set.range ι₀.base ≠ Set.univ := by
    intro hu
    have hr0g : r₀ = genericPoint Y :=
      (show IsGenericPoint r₀ Set.univ by rw [← hu, hr₀']; exact isGenericPoint_closure).eq
        (genericPoint_spec Y)
    rw [hr0g, Order.coheight_eq_zero.mpr (fun b _ =>
      Scheme.le_iff_specializes.mpr (genericPoint_specializes b))] at hcr₀
    have : J₀.card = 0 := by exact_mod_cast hcr₀.symm
    exact hJ₀e (Finset.card_eq_zero.mp this)
  have hfilt := toQDivisor_filter_coeffOnePart_eq_sum hC hJ₀ hJ₀1 hr₀J hcr₀ ι₀ hr₀'
  have hgen₀' : ∀ V : irreducibleComponents S₀, ι₀ (componentGenericPoint S₀ V) ∉
      (C - Divisor.toQDivisor ((coeffOnePart C).filter
        fun G => Set.range ι₀.base ⊆ G.support)).supp := by
    rw [hfilt]; exact hgen₀
  have hCF : (C - Divisor.toQDivisor ((coeffOnePart C).filter
      fun G => Set.range ι₀.base ⊆ G.support)).IsPullback ι₀ hgen₀' C₀ :=
    qdivisor_isPullback_congr (by rw [hfilt]) hpb₀
  obtain ⟨hsmR, hkerR, hyJR⟩ := stratum_package sX hB.isSNC hJ hrJ hcr ιR hrR
  haveI := hsmR
  have hQX : ∀ A : QDivisor X, A.IsQCartier :=
    MMP.Fourfold.isQCartier_of_isSmoothScheme hB.isSmoothScheme
  set A := B - ∑ G ∈ J, Finsupp.single G (1 : ℚ) with hA
  have hAD : A.support ⊆ B.support := support_sub_sum_single_subset B hJ
  have hAJ := coeff_sub_sum_single_eq_zero B hJ1
  have hBTc : ∀ Q : MMP.Mori.PrimeDivisor SR, BR.coeff Q =
      ∑ E ∈ B.support.filter (fun E => E ∉ J ∧ ιR Q.genericPoint ∈ E.support), B.coeff E := by
    intro Q
    rw [coeff_isPullback_of_stratum sX hB.isSNC hJ ιR hyJR hkerR A hAD hAJ (hQX A) hpbR Q, hA,
      sum_filter_sub_sum_single B J hJ1]
  have hTv : IsNormalVariety k (ιR ≫ sX) := ⟨inferInstance, inferInstance⟩
  have hcrep' := isCrepantBoundary_of_isSNCStratum hB hC hKX hKY h rfl hproj hbir hcrep ι₀ hFst
    hFY hgen₀' hCF ιR hTv hJ hJ1 hrJ hcr hrR hBTc g hg hgb m KT hKT
  -- effectivity of the restricted target
  have hBR0 : ∀ Q, 0 ≤ BR.coeff Q := fun Q => by
    rw [hBTc Q]; exact Finset.sum_nonneg fun E _ => hB0 E
  -- lift on the strata
  have hF' := isSNCStratum_preimage_of_stratum hB hJ hJ1 hrJ hcr ιR hrR hpbR hpairR hF hFr
  have hh' : g ≫ ιR ≫ sX = ι₀ ≫ h ≫ sX := by rw [← Category.assoc, hg, Category.assoc]
  obtain ⟨f'', hf''1, hf''2, hf''3⟩ := hL hpairR hBR0 hpair₀ hKT hK₀ g hh' hgproj hgb
    hcrep' hF'
  refine ⟨ι₀ f'', hr₀' ▸ ⟨f'', rfl⟩, ?_, ?_, ?_⟩
  · have := isSNCStratum_image_of_stratum hC hJ₀ hJ₀1 hr₀J hcr₀ ι₀ hr₀' hpb₀ hpair₀ hf''1
    rwa [← ι₀.isClosedMap.closure_image_eq_of_continuous ι₀.continuous, Set.image_singleton]
      at this
  · have hhf : h (ι₀ f'') = ιR (g f'') := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hg]
    rw [hhf]
    have hcl := hf''2.def
    have : closure {ιR (g f'')} = F := by
      rw [← Set.image_singleton, ιR.isClosedMap.closure_image_eq_of_continuous ιR.continuous, hcl,
        Set.image_preimage_eq_inter_range, hrR, Set.inter_eq_left.mpr hFr]
    exact this ▸ isGenericPoint_closure
  · have h1 : Function.Bijective ((g ≫ ιR).residueFieldMap f'') :=
      (bijective_residueFieldMap_comp_iff g ιR f'' hf''3).mpr
        (bijective_residueFieldMap_of_isClosedImmersion ιR _)
    rw [hg] at h1
    exact (bijective_residueFieldMap_comp_iff ι₀ h f''
      (bijective_residueFieldMap_of_isClosedImmersion ι₀ _)).mp h1

/-- The case split of the lifting property: either the stratum is the whole of `X`, lifted by
the generic point of `Y`, or it lies on a floor divisor `D`, where the given construction
applies. -/
private theorem lift_aux {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {B : QDivisor X} {C : QDivisor Y} (hB : IsSNCSubboundaryPair sX B)
    (hC : IsSNCSubboundaryPair sY C) {n : ℕ} {KX : Divisor X} (hKX : KX.IsCanonicalDivisor sX n)
    (h : Y ⟶ X) (hbir : IsBirationalMorphism h) {F : Set X}
    (hF : IsSNCStratum (coeffOnePart B) F)
    (hD : ∀ D : MMP.Mori.PrimeDivisor X, D ∈ B.support ∧ B.coeff D = 1 ∧
      F ⊆ (D.support : Set X) →
      ∃ f' : Y, IsSNCStratum (coeffOnePart C) (closure {f'}) ∧ IsGenericPoint (h f') F ∧
        Function.Bijective (h.residueFieldMap f')) :
    ∃ f' : Y, IsSNCStratum (coeffOnePart C) (closure {f'}) ∧ IsGenericPoint (h f') F ∧
      Function.Bijective (h.residueFieldMap f') := by
  obtain ⟨JF, hJF, hmax⟩ := hF
  by_cases hJFe : JF = ∅
  · subst hJFe
    have hFu : F = Set.univ :=
      (hmax.eq_of_ge ⟨IrreducibleSpace.isIrreducible_univ X, by simp⟩ (Set.subset_univ _)).symm
    subst hFu
    haveI : IsDominant h := hbir.isDominant
    refine ⟨genericPoint Y, ?_, ?_, bijective_residueFieldMap_genericPoint h
      hbir.functionFieldMap_bijective⟩
    · rw [(genericPoint_spec Y).def]
      exact ⟨∅, Finset.empty_subset _, ⟨IrreducibleSpace.isIrreducible_univ Y, by simp⟩,
        fun _ _ _ => Set.subset_univ _⟩
    · rw [map_genericPoint_of_isDominant h]; exact genericPoint_spec X
  · obtain ⟨D, hD'⟩ := Finset.nonempty_iff_ne_empty.mpr hJFe
    exact hD D ⟨support_coeffOnePart_subset B (hJF hD'),
      coeff_eq_one_of_mem_support_coeffOnePart (hJF hD'),
      hmax.1.2.trans (Set.biInter_subset_of_mem hD')⟩

/-- **The lifting property holds in every dimension**, by induction on the dimension: restrict to
the strict transform of a floor divisor containing the stratum. -/
private theorem liftProperty (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (n : ℕ) :
    LiftProperty k n := by
  classical
  induction n with
  | zero =>
    intro X Y sX sY _ _ _ _ _ _ B C hB hB0 hC KX hKX KY hKY h hh hproj hbir hcrep F hF
    exact lift_aux hB hC hKX h hbir hF fun D _ => by
      haveI : LocallyOfFiniteType sX := hB.isProjectiveVariety.toIsVariety.toLocallyOfFiniteType
      haveI := D.integral
      have hr : Set.range D.idealSheaf.subschemeι.base = closure {D.genericPoint} := by
        rw [Scheme.IdealSheafData.range_subschemeι,
          ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      have h1 := topologicalKrullDim_add_coheight_of_range sX D.idealSheaf.subschemeι hr
      rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint, hKX.topologicalKrullDim_eq] at h1
      have := le_of_withBot_add_eq (b := 1) (n := 0) (by exact_mod_cast h1)
      omega
  | succ n ih =>
    intro X Y sX sY _ _ _ _ _ _ B C hB hB0 hC KX hKX KY hKY h hh hproj hbir hcrep F hF
    refine lift_aux hB hC hKX h hbir hF fun D hD => ?_
    obtain ⟨hDB, hD1, hFD⟩ := hD
    subst hh
    have hX : IsNormalVariety k sX := ⟨hB.isProjectiveVariety.toIsVariety, inferInstance⟩
    have hY : IsNormalVariety k (h ≫ sX) := ⟨hC.isProjectiveVariety.toIsVariety, inferInstance⟩
    haveI : IsProper h := isProper_of_isProjectiveMorphism h hproj
    haveI : IsDominant h := hbir.isDominant
    -- the strict transform of `D`
    have hreg := MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal h hbir
      (y := D.genericPoint) (by rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint])
    obtain ⟨D', -, hD'⟩ := MMP.Flips.exists_inverseTransformPrimeDivisor_eq_some D hreg
    haveI := MMP.isIso_stalkMap_of_mem_biregularLocus h (x := D'.genericPoint) (hD' ▸ hreg)
    -- `C(D') = B(D) = 1`
    have hD'1 : C.coeff D' = 1 := by
      have hE : ¬ (⟨Y, h, hY, hbir, D'⟩ : DivisorOver k sX).IsExceptional := by
        rw [isExceptional_iff_two_le_coheight hX]
        change ¬ 2 ≤ Order.coheight (h D'.genericPoint)
        rw [hD', AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
        decide
      obtain ⟨P, hcen, hP⟩ := MMP.Mori.DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff
        ⟨hX, hKX, isQCartier_of_isSmoothScheme hB.isSmoothScheme _⟩ _ hE
      have hcl : closure {h D'.genericPoint} = (P.support : Set X) := by
        rw [← hcen, MMP.Positivity.DivisorOver.center_eq_closureSingleton]
        rfl
      have hPD : D = P := by
        rw [hD'] at hcl
        have hmem : D.genericPoint ∈ P.support := by rw [← hcl]; exact subset_closure rfl
        have := MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support hmem
        first | exact this | exact this.symm
      subst hPD
      have := (hcrep hY D').eq hP
      linarith
    have hD'C : D' ∈ C.support := Finsupp.mem_support_iff.mpr (by
      change C.coeff D' ≠ 0; rw [hD'1]; norm_num)
    have hFr : F ⊆ closure {D.genericPoint} := by
      rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact hFD
    obtain ⟨f', -, hf'⟩ := exists_lift_of_stratum hB hB0 hC hKX hKY h rfl hproj hbir hcrep
      (J₀ := {D'}) (by simpa using hD'C) (by simpa using hD'1)
      (by simpa using MMP.Positivity.PrimeDivisor.genericPoint_mem_support' D')
      (by simp [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint])
      (J := {D}) (by simpa using hDB) (by simpa using hD1)
      (by simpa using MMP.Positivity.PrimeDivisor.genericPoint_mem_support' D)
      (by simp [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]) hD'
      (bijective_residueFieldMap_of_isIso_stalkMap h _) (m := n) (by simp) ih hF hFr
    exact ⟨f', hf'⟩

/-! ### Strata of snc closed subsets -/

/-- A *stratum* of a closed subset `T`: an irreducible component of an intersection of
irreducible components of `T` (the empty intersection giving the whole space). -/
private def IsComponentStratum {Y : Scheme.{0}} (T S : Set Y) : Prop :=
  ∃ J : Set (Set Y), J ⊆ MMP.Resolution.componentsOf T ∧ S ∈ MMP.Resolution.componentsOf (⋂₀ J)

/-- The support of a prime divisor contained in an snc closed subset `T` is a component of
`T`. -/
private theorem support_mem_componentsOf_of_isSNCClosedSubset {k : Type} [Field k]
    {Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian Y] {sY : Y ⟶ Spec (.of k)} {T : Set Y}
    (hT : MMP.Resolution.IsSNCClosedSubset sY T) {P : MMP.Mori.PrimeDivisor Y}
    (hP : (P.support : Set Y) ⊆ T) : (P.support : Set Y) ∈ MMP.Resolution.componentsOf T := by
  obtain ⟨hSc, hempty | ⟨hpure, -, -⟩⟩ := hT
  · exfalso
    have := hP (MMP.Positivity.PrimeDivisor.genericPoint_mem_support' P)
    rw [hempty] at this
    exact this
  · obtain ⟨-, hcov⟩ := MMP.Resolution.Aux.finite_and_cover_componentsOf hSc
    obtain ⟨W, hW, hηW⟩ := hcov (hP (MMP.Positivity.PrimeDivisor.genericPoint_mem_support' P))
    obtain ⟨ξ, -, hWξ⟩ := MMP.Resolution.Aux.exists_eq_closure_of_mem_componentsOf hSc hW
    have hξ1 : Order.coheight ξ = 1 := by
      rw [← MMP.Flips.codimension_closureSingleton]
      apply hpure
      refine ⟨?_, fun W' hW' hle => ?_⟩
      · change closure {ξ} ⊆ T
        rw [← hWξ]
        exact hW.1.2
      · have : (W' : Set Y) ⊆ W := hW.2 ⟨W'.isIrreducible, hW'⟩ (by rw [hWξ]; exact hle)
        change (W' : Set Y) ⊆ closure {ξ}
        rw [← hWξ]
        exact this
    have hsp : ξ ⤳ P.genericPoint := specializes_iff_mem_closure.mpr (hWξ ▸ hηW)
    have hξη : ξ = P.genericPoint := by
      by_contra hne
      have hlt : P.genericPoint < ξ := lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hsp)
        fun hle => hne (hsp.antisymm (Scheme.le_iff_specializes.mp hle)).eq
      have := Order.coheight_strictAnti hlt
      rw [hξ1, P.coheight_genericPoint] at this
      exact lt_irrefl _ (this (by simp))
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    change closure {P.genericPoint} ∈ _
    rw [← hξη, ← hWξ]
    exact hW

/-- Every component of an snc closed subset is the support of a prime divisor. -/
private theorem exists_primeDivisor_of_mem_componentsOf {k : Type} [Field k]
    {Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian Y] {sY : Y ⟶ Spec (.of k)} {T : Set Y}
    (hT : MMP.Resolution.IsSNCClosedSubset sY T) {W : Set Y}
    (hW : W ∈ MMP.Resolution.componentsOf T) :
    ∃ P : MMP.Mori.PrimeDivisor Y, (P.support : Set Y) ⊆ T ∧ W = P.support := by
  obtain ⟨hSc, hempty | ⟨hpure, -, -⟩⟩ := id hT
  · exfalso
    obtain ⟨x, hx⟩ := hW.1.1.nonempty
    have := hW.1.2 hx
    rw [hempty] at this
    exact this
  · obtain ⟨ξ, -, hWξ⟩ := MMP.Resolution.Aux.exists_eq_closure_of_mem_componentsOf hSc hW
    have hξ1 : Order.coheight ξ = 1 := by
      rw [← MMP.Flips.codimension_closureSingleton]
      apply hpure
      refine ⟨?_, fun W' hW' hle => ?_⟩
      · change closure {ξ} ⊆ T
        rw [← hWξ]
        exact hW.1.2
      · have : (W' : Set Y) ⊆ W := hW.2 ⟨W'.isIrreducible, hW'⟩ (by rw [hWξ]; exact hle)
        change (W' : Set Y) ⊆ closure {ξ}
        rw [← hWξ]
        exact this
    set P : MMP.Mori.PrimeDivisor Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne ξ hξ1
    have hPξ : P.genericPoint = ξ := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne ξ hξ1
    have hPW : W = P.support := by
      rw [hWξ, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      change closure {ξ} = closure {P.genericPoint}
      rw [hPξ]
    exact ⟨P, hPW ▸ hW.1.2, hPW⟩

/-- Only finitely many prime divisors lie in an snc closed subset. -/
private theorem finite_setOf_support_subset_of_isSNCClosedSubset {k : Type} [Field k]
    {Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian Y] {sY : Y ⟶ Spec (.of k)} {T : Set Y}
    (hT : MMP.Resolution.IsSNCClosedSubset sY T) :
    {P : MMP.Mori.PrimeDivisor Y | (P.support : Set Y) ⊆ T}.Finite := by
  refine Set.Finite.of_finite_image (f := fun P : MMP.Mori.PrimeDivisor Y => (P.support : Set Y))
    ((MMP.Resolution.Aux.finite_and_cover_componentsOf hT.1).1.subset ?_)
    fun P _ Q _ h => AlgebraicGeometry.PrimeDivisor.genericPoint_injective ?_
  · rintro - ⟨P, hP, rfl⟩
    exact support_mem_componentsOf_of_isSNCClosedSubset hT hP
  · have h' : closure {P.genericPoint} = closure {Q.genericPoint} := by
      rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure,
        ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact (h : (P.support : Set Y) = Q.support)
    exact (inseparable_iff_closure_eq.2 h').eq

/-- The reduced divisor of an snc closed subset: the sum of the prime divisors it contains. -/
private noncomputable def reducedDivisorOfSet {Y : Scheme.{0}} (T : Set Y)
    (hT : {P : MMP.Mori.PrimeDivisor Y | (P.support : Set Y) ⊆ T}.Finite) : QDivisor Y :=
  Divisor.toQDivisor (MMP.Intersection.reducedDivisorOf hT.toFinset)

open scoped Classical in
private theorem coeff_reducedDivisorOfSet {Y : Scheme.{0}} (T : Set Y)
    (hT : {P : MMP.Mori.PrimeDivisor Y | (P.support : Set Y) ⊆ T}.Finite)
    (G : MMP.Mori.PrimeDivisor Y) :
    (reducedDivisorOfSet T hT).coeff G = if (G.support : Set Y) ⊆ T then 1 else 0 := by
  rw [reducedDivisorOfSet, Divisor.coeff_toQDivisor, MMP.Intersection.coeff_reducedDivisorOf]
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  split_ifs <;> simp

private theorem support_coeffOnePart_reducedDivisorOfSet {Y : Scheme.{0}} (T : Set Y)
    (hT : {P : MMP.Mori.PrimeDivisor Y | (P.support : Set Y) ⊆ T}.Finite)
    (G : MMP.Mori.PrimeDivisor Y) :
    G ∈ (coeffOnePart (reducedDivisorOfSet T hT)).support ↔ (G.support : Set Y) ⊆ T := by
  constructor
  · intro hG
    have := coeff_eq_one_of_mem_support_coeffOnePart hG
    rw [coeff_reducedDivisorOfSet] at this
    by_contra h
    rw [if_neg h] at this
    exact zero_ne_one this
  · intro hG
    exact mem_support_coeffOnePart (by rw [coeff_reducedDivisorOfSet, if_pos hG])

open scoped Classical in
/-- **Strata of an snc closed subset are the floor strata of its reduced divisor.** -/
private theorem isComponentStratum_iff_isSNCStratum {k : Type} [Field k]
    {Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian Y] {sY : Y ⟶ Spec (.of k)} {T : Set Y}
    (hT : MMP.Resolution.IsSNCClosedSubset sY T)
    (hTf : {P : MMP.Mori.PrimeDivisor Y | (P.support : Set Y) ⊆ T}.Finite) (S : Set Y) :
    IsComponentStratum T S ↔ IsSNCStratum (coeffOnePart (reducedDivisorOfSet T hTf)) S := by
  constructor
  · rintro ⟨J, hJ, hS⟩
    refine ⟨hTf.toFinset.filter fun G => (G.support : Set Y) ∈ J, fun G hG => ?_, ?_⟩
    · obtain ⟨hG1, -⟩ := Finset.mem_filter.mp hG
      exact (support_coeffOnePart_reducedDivisorOfSet T hTf _).mpr
        ((Set.Finite.mem_toFinset _).mp hG1)
    · have heq : (⋂ E ∈ hTf.toFinset.filter fun G => (G.support : Set Y) ∈ J,
          (E.support : Set Y)) = ⋂₀ J := by
        ext x
        simp only [Set.mem_iInter, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
          Set.mem_sInter]
        constructor
        · intro h W hW
          obtain ⟨P, hPT, hPW⟩ := exists_primeDivisor_of_mem_componentsOf hT (hJ hW)
          rw [hPW]
          exact h P ⟨hPT, hPW ▸ hW⟩
        · intro h G hG
          exact h _ hG.2
      rw [heq]
      exact hS
  · rintro ⟨J, hJ, hS⟩
    refine ⟨(fun G : MMP.Mori.PrimeDivisor Y => (G.support : Set Y)) '' J, ?_, ?_⟩
    · rintro _ ⟨G, hG, rfl⟩
      exact support_mem_componentsOf_of_isSNCClosedSubset hT
        ((support_coeffOnePart_reducedDivisorOfSet T hTf G).mp (hJ hG))
    · rw [Set.sInter_image]
      exact hS

/-- **The reduced divisor of an snc closed subset is an snc subboundary.** -/
private theorem isSNCSubboundaryPair_reducedDivisorOfSet {k : Type} [Field k] {Y : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} [IsLocallyNoetherian Y] [AlgebraicGeometry.IsNoetherian Y]
    (hproj : MMP.Mori.IsProjectiveVariety k sY) (hsm : IsSmoothScheme sY) {T : Set Y}
    (hT : MMP.Resolution.IsSNCClosedSubset sY T)
    (hTf : {P : MMP.Mori.PrimeDivisor Y | (P.support : Set Y) ⊆ T}.Finite) :
    IsSNCSubboundaryPair sY (reducedDivisorOfSet T hTf) := by
  classical
  set s := hTf.toFinset with hs
  have hsT : ∀ P ∈ s, (P.support : Set Y) ⊆ T := fun P hP => (Set.Finite.mem_toFinset _).mp hP
  have hc : ∀ P ∈ s, (P.support : Set Y) ∈ MMP.Resolution.componentsOf T := fun P hP =>
    support_mem_componentsOf_of_isSNCClosedSubset hT (hsT P hP)
  have hDsnc : (MMP.Intersection.reducedDivisorOf s).IsSNC sY := by
    obtain ⟨hSc, hempty | ⟨-, -, hfam⟩⟩ := id hT
    · have hs0 : s = ∅ := Finset.eq_empty_of_forall_notMem fun P hP => by
        have := hsT P hP (MMP.Positivity.PrimeDivisor.genericPoint_mem_support' P)
        rw [hempty] at this
        exact this
      rw [hs0, MMP.Intersection.reducedDivisorOf, Finset.sum_empty]
      exact DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme sY hsm
    have hG : (MMP.Intersection.reducedDivisorOf s).support = s :=
      MMP.Intersection.support_reducedDivisorOf s
    have hideal : ∀ P (hP : P ∈ s),
        P.idealSheaf = MMP.Resolution.componentsFamily T ⟨(P.support : Set Y), hc P hP⟩ :=
      fun P hP => (MMP.Fourfold.SNCWeight.PrimeDivisorUnion.componentsFamily_eq_idealSheaf
        ⟨(P.support : Set Y), hc P hP⟩ P rfl).symm
    refine ⟨fun P hP => ?_, fun x => ?_⟩
    · rw [hG] at hP
      rw [hideal P hP]
      exact (hfam.1 _).2.2
    · obtain ⟨m, z, c, hz, hcI, hcinj⟩ := hfam.2 x
      have hs' : ∀ P : {P : MMP.Mori.PrimeDivisor Y //
          P ∈ (MMP.Intersection.reducedDivisorOf s).support ∧ x ∈ P.support},
          P.1 ∈ s := fun P => hG.subset P.2.1
      have hmem : ∀ P : {P : MMP.Mori.PrimeDivisor Y //
          P ∈ (MMP.Intersection.reducedDivisorOf s).support ∧ x ∈ P.support},
          x ∈ (MMP.Resolution.componentsFamily T
            ⟨(P.1.support : Set Y), hc P.1 (hs' P)⟩).support := fun P => by
        rw [← hideal P.1 (hs' P)]
        exact P.2.2
      refine ⟨m, z, fun P => c ⟨_, hmem P⟩, hz, fun P Q h => ?_, fun P => ?_⟩
      · have h1 := congrArg (fun V => (V.1.1 : Set Y)) (hcinj h)
        refine Subtype.ext (AlgebraicGeometry.PrimeDivisor.genericPoint_injective ?_)
        have h' : closure {P.1.genericPoint} = closure {Q.1.genericPoint} := by
          rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure,
            ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
          exact h1
        exact (inseparable_iff_closure_eq.2 h').eq
      · rw [hideal P.1 (hs' P)]
        exact hcI ⟨_, hmem P⟩
  refine ⟨hproj, hsm, hDsnc.of_support_subset fun G hG => ?_, fun G => ?_⟩
  · rw [Finsupp.mem_support_iff] at hG ⊢
    intro h0
    apply hG
    change (reducedDivisorOfSet T hTf).coeff G = 0
    rw [reducedDivisorOfSet, Divisor.coeff_toQDivisor]
    change (((MMP.Intersection.reducedDivisorOf s).coeff G : ℤ) : ℚ) = 0
    rw [show (MMP.Intersection.reducedDivisorOf s).coeff G = 0 from h0]
    rfl
  · rw [coeff_reducedDivisorOfSet]
    split_ifs <;> norm_num

/-- A homeomorphism carries the components of a set to those of its preimage. -/
private theorem preimage_mem_componentsOf_iff {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] (h : α ≃ₜ β) (A S : Set β) :
    h ⁻¹' S ∈ MMP.Resolution.componentsOf (h ⁻¹' A) ↔ S ∈ MMP.Resolution.componentsOf A := by
  have hirr : ∀ W : Set β, IsIrreducible (h ⁻¹' W) ↔ IsIrreducible W := fun W => by
    constructor
    · intro hW
      have := hW.image h h.continuous.continuousOn
      rwa [Set.image_preimage_eq _ h.surjective] at this
    · intro hW
      have := hW.image h.symm h.symm.continuous.continuousOn
      rwa [Homeomorph.image_symm] at this
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨(hirr S).mp h1, (Set.preimage_subset_preimage_iff (by
      rw [h.surjective.range_eq]; exact Set.subset_univ _)).mp h2⟩, fun W hW hSW => ?_⟩
    have := h3 ⟨(hirr W).mpr hW.1, Set.preimage_mono hW.2⟩ (Set.preimage_mono hSW)
    exact (Set.preimage_subset_preimage_iff (by
      rw [h.surjective.range_eq]; exact Set.subset_univ _)).mp this
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨(hirr S).mpr h1, Set.preimage_mono h2⟩, fun W hW hSW => ?_⟩
    have hW' : W = h ⁻¹' (h '' W) := (h.preimage_image W).symm
    rw [hW'] at hW hSW ⊢
    refine Set.preimage_mono (h3 ⟨(hirr _).mp hW.1, ?_⟩ ?_)
    · exact (Set.preimage_subset_preimage_iff (by
        rw [h.surjective.range_eq]; exact Set.subset_univ _)).mp hW.2
    · exact (Set.preimage_subset_preimage_iff (by
        rw [h.surjective.range_eq]; exact Set.subset_univ _)).mp hSW

/-- A homeomorphism carries the strata of a set to those of its preimage. -/
private theorem isComponentStratum_preimage_iff {Y' Y : Scheme.{0}} (h : Y' ≃ₜ Y) (A S : Set Y) :
    IsComponentStratum (h ⁻¹' A) (h ⁻¹' S) ↔ IsComponentStratum A S := by
  constructor
  · rintro ⟨J, hJ, hS⟩
    refine ⟨(fun W => h '' W) '' J, ?_, ?_⟩
    · rintro _ ⟨W, hW, rfl⟩
      rw [← preimage_mem_componentsOf_iff h, h.preimage_image]
      exact hJ hW
    · have heq : h ⁻¹' ⋂₀ ((fun W => h '' W) '' J) = ⋂₀ J := by
        rw [Set.sInter_image, Set.preimage_iInter₂, Set.sInter_eq_biInter]
        simp only [h.preimage_image]
      rw [← preimage_mem_componentsOf_iff h, heq]
      exact hS
  · rintro ⟨J, hJ, hS⟩
    refine ⟨(fun W => h ⁻¹' W) '' J, ?_, ?_⟩
    · rintro _ ⟨W, hW, rfl⟩
      exact (preimage_mem_componentsOf_iff h A W).mpr (hJ hW)
    · have : ⋂₀ ((fun W => h ⁻¹' W) '' J) = h ⁻¹' (⋂₀ J) := by
        rw [Set.sInter_image, Set.preimage_sInter]
      rw [this]
      exact (preimage_mem_componentsOf_iff h _ S).mpr hS

/-- The coefficient-one locus `⋃_{B_D = 1} D` of an `ℝ`-divisor `B`. -/
private def oneLocus {X : Scheme.{0}} (B : RDivisor X) : Set X :=
  {x | ∃ D : MMP.Mori.PrimeDivisor X, B.coeff D = 1 ∧ x ∈ D.support}

/-- A prime divisor lies over the coefficient-one locus exactly when it is a coefficient-one
component. -/
private theorem genericPoint_mem_oneLocus_iff {X : Scheme.{0}} {B : RDivisor X}
    (G : MMP.Mori.PrimeDivisor X) : G.genericPoint ∈ oneLocus B ↔ B.coeff G = 1 := by
  constructor
  · rintro ⟨D, hD, hGD⟩
    rwa [MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support hGD] at hD
  · intro h
    exact ⟨G, h, MMP.Positivity.PrimeDivisor.genericPoint_mem_support' G⟩

/-- **The invariant of the extraction tower.** For a model `q : Y ⟶ X` and a point `y` of `Y`:
`Y` is a smooth projective variety of dimension `n` on which the preimage of the coefficient-one
locus `L` is an snc closed subset, and every stratum of `q⁻¹ L` through `y` contains a stratum
mapping birationally onto `closure {ξ₀}`. -/
private def TowerGood {k : Type} [Field k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) (n : ℕ)
    (L : Set X) (ξ₀ : X) {Y : Scheme.{0}} (q : Y ⟶ X) (y : Y) : Prop :=
  ∃ (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (_ : IsNormal Y),
    IsSmoothScheme (q ≫ sX) ∧ MMP.Mori.IsProjectiveVariety k (q ≫ sX) ∧
      topologicalKrullDim Y = n ∧ MMP.Resolution.IsSNCClosedSubset (q ≫ sX) (q.base ⁻¹' L) ∧
      ∀ S, IsComponentStratum (q.base ⁻¹' L) S → y ∈ S →
        ∃ f ∈ S, IsComponentStratum (q.base ⁻¹' L) (closure {f}) ∧ q f = ξ₀ ∧
          Function.Bijective (q.residueFieldMap f)

/-- The invariant of the extraction tower is transported along isomorphisms. -/
private theorem TowerGood.comp_iso {k : Type} [Field k] [PerfectField k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {n : ℕ} {L : Set X} {ξ₀ : X} {Y Y' : Scheme.{0}} (e : Y' ⟶ Y)
    [IsIso e] {q : Y ⟶ X} {y : Y'} (hq : TowerGood sX n L ξ₀ q (e y)) :
    TowerGood sX n L ξ₀ (e ≫ q) y := by
  obtain ⟨_, _, _, hsm, hproj, hdim, hsnc, hinv⟩ := hq
  haveI : Nonempty Y' := ⟨y⟩
  haveI : IsIntegral Y' := isIntegral_of_isOpenImmersion e
  haveI : IsLocallyNoetherian Y' := isLocallyNoetherian_of_isOpenImmersion e
  haveI : IsNormal Y' := isNormal_of_isOpenImmersion e
  haveI : LocallyOfFiniteType (q ≫ sX) := hproj.toIsVariety.toLocallyOfFiniteType
  haveI : QuasiCompact (q ≫ sX) := hproj.toIsVariety.toQuasiCompact
  haveI : IsSeparated (q ≫ sX) := hproj.toIsVariety.toIsSeparated
  haveI : AlgebraicGeometry.IsVariety k (e ≫ q ≫ sX) := ⟨⟩
  set φ : Y' ≃ₜ Y := Scheme.homeoOfIso (asIso e) with hφ
  have hφe : ∀ x, φ x = e x := fun x => rfl
  have hpre : (e ≫ q).base ⁻¹' L = φ ⁻¹' (q.base ⁻¹' L) := rfl
  refine ⟨inferInstance, inferInstance, inferInstance, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc]
    haveI : LocallyOfFinitePresentation (q ≫ sX) :=
      (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := q ≫ sX)).mpr inferInstance
    haveI : Smooth (q ≫ sX) := (MMP.Mori.isSmoothScheme_iff _).1 hsm
    exact (MMP.Mori.isSmoothScheme_iff _).2 inferInstance
  · rw [Category.assoc]
    exact (AlgebraicGeometry.isProjectiveVariety_iff_isProjectiveMorphism k _).mpr
      ((MMP.isProjectiveMorphism_of_isClosedImmersion e).comp hproj.isProjective)
  · rw [← hdim]
    exact IsHomeomorph.topologicalKrullDim_eq _ φ.isHomeomorph
  · rw [Category.assoc]
    exact MMP.Resolution.IsSNCClosedSubset.preimage_of_isIso e hsnc
  · intro S hS hyS
    have hS' : IsComponentStratum (q.base ⁻¹' L) (φ.symm ⁻¹' S) := by
      rw [← isComponentStratum_preimage_iff φ, ← hpre]
      convert hS using 1
      ext x; simp
    obtain ⟨f, hfS, hfst, hfq, hfb⟩ := hinv _ hS' (by
      change φ.symm (e y) ∈ S
      rw [← hφe, Homeomorph.symm_apply_apply]; exact hyS)
    refine ⟨φ.symm f, hfS, ?_, ?_, ?_⟩
    · have : φ ⁻¹' closure {f} = closure {φ.symm f} := by
        have h1 : φ ⁻¹' {f} = {φ.symm f} := by
          ext x
          simp only [Set.mem_preimage, Set.mem_singleton_iff]
          exact ⟨fun h => by rw [← h, Homeomorph.symm_apply_apply],
            fun h => by rw [h, Homeomorph.apply_symm_apply]⟩
        rw [φ.preimage_closure, h1]
      rw [hpre, ← this]
      exact (isComponentStratum_preimage_iff φ _ _).mpr hfst
    · change q (e (φ.symm f)) = ξ₀
      rw [← hφe, Homeomorph.apply_symm_apply]; exact hfq
    · haveI : IsIso (e.stalkMap (φ.symm f)) := inferInstance
      refine (bijective_residueFieldMap_comp_iff e q _
        (bijective_residueFieldMap_of_isIso_stalkMap e _)).mpr ?_
      rw [← hφe, Homeomorph.apply_symm_apply]; exact hfb

/-- Under a proper birational morphism onto a normal integral scheme, the preimage of a closed
connected set is connected: the fibres are connected by Zariski's main theorem. -/
private theorem isConnected_preimage_of_isBirationalMorphism {A B : Scheme.{0}} [IsIntegral A]
    [IsIntegral B] [IsNormal B] (g : A ⟶ B) [IsProper g] (hg : IsBirationalMorphism g)
    {t : Set B} (ht : IsClosed t) (ht' : _root_.IsConnected t) :
    _root_.IsConnected (g.base ⁻¹' t) := by
  haveI : IsDominant g := hg.isDominant
  haveI hc : IsIso g.c := isIso_c_of_isBirational_comp (𝟙 A) g (by
    rw [Category.id_comp]; exact MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hg)
  have hiso : ∀ U : B.Opens, IsIso (g.app U) := fun U =>
    NatIso.isIso_app_of_isIso g.c (Opposite.op U)
  have hfib : ∀ b : B, _root_.IsConnected (g.base ⁻¹' {b}) := fun b =>
    g.isConnected_preimage_singleton_of_isIso_app hiso b
  have hsurj : Function.Surjective g.base := fun b => (hfib b).nonempty
  have hq : Topology.IsQuotientMap g.base :=
    g.isClosedMap.isQuotientMap g.continuous hsurj
  exact Topology.IsCoinducing.isConnected_preimage_of_isClosed hfib hq.isCoinducing ht ht'

/-- A connected subset of a finite union of disjoint closed sets meeting one of them lies in it. -/
private theorem subset_of_isPreconnected_of_pairwise_disjoint {α : Type*} [TopologicalSpace α]
    {𝒞 : Set (Set α)} (hfin : 𝒞.Finite) (hcl : ∀ C ∈ 𝒞, IsClosed C)
    (hdisj : ∀ C ∈ 𝒞, ∀ C' ∈ 𝒞, ∀ x, x ∈ C → x ∈ C' → C = C') {A : Set α}
    (hA : IsPreconnected A) (hAU : A ⊆ ⋃₀ 𝒞) {C : Set α} (hC : C ∈ 𝒞) {y : α} (hyA : y ∈ A)
    (hyC : y ∈ C) : A ⊆ C := by
  set W := ⋃₀ (𝒞 \ {C}) with hW
  have hWcl : IsClosed W := (hfin.subset Set.diff_subset).isClosed_sUnion
    fun C' hC' => hcl C' hC'.1
  have hcov : A ⊆ C ∪ W := fun x hx => by
    obtain ⟨C', hC', hxC'⟩ := hAU hx
    by_cases h : C' = C
    · exact Or.inl (h ▸ hxC')
    · exact Or.inr ⟨C', ⟨hC', h⟩, hxC'⟩
  have hempty : A ∩ (C ∩ W) = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    rintro - hxC ⟨C', ⟨hC', hne⟩, hxC'⟩
    exact hne (hdisj C' hC' C hC x hxC' hxC)
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hA) C W (hcl C hC) hWcl hcov hempty
    with h | h
  · exact h
  · exfalso
    obtain ⟨C', ⟨hC', hne⟩, hyC'⟩ := h hyA
    exact hne (hdisj C' hC' C hC y hyC' hyC)

open scoped Classical in
/-- **Lifting strata through one stratum blow-up.** Let `π : (Y', D') ⟶ (Y, D)` be a crepant
projective birational morphism of snc subboundary pairs with `D` effective, isomorphic away from
an exceptional floor divisor `E` lying over a floor stratum `V = closure {v}` of `Y`, every other
floor divisor of `Y'` lying over a floor divisor of `Y`. If every floor stratum of `Y` through
`π y` contains a floor stratum mapping birationally onto `closure {ξ₀}` under `q`, the same holds
on `Y'` at `y` for `π ≫ q`. A stratum `S' ∋ y` is a component of `E^{ε} ∩ R₀` for a stratum `R₀`
not in `E`; `R₀` maps birationally onto a stratum `R`, inside which the required stratum of `Y`
is lifted (`exists_lift_of_stratum`); when `S' ⊆ E` the lift lies in `S'` because the preimage
in `R₀` of a stratum of `V ∩ R` is connected. -/
private theorem towerStep_inv {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {ξ₀ : X} {Y Y' : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y'] (q : Y ⟶ X) (π : Y' ⟶ Y)
    {D : QDivisor Y} {D' : QDivisor Y'} (hD : IsSNCSubboundaryPair (q ≫ sX) D)
    (hD0 : ∀ P, 0 ≤ D.coeff P) (hD' : IsSNCSubboundaryPair (π ≫ q ≫ sX) D') {n : ℕ}
    {KY : Divisor Y} (hKY : KY.IsCanonicalDivisor (q ≫ sX) n) {KY' : Divisor Y'}
    (hKY' : KY'.IsCanonicalDivisor (π ≫ q ≫ sX) n) (hproj : IsProjectiveMorphism π)
    (hbir : IsBirationalMorphism π)
    (hcrep : ∀ hY' : IsNormalVariety k (π ≫ q ≫ sX),
      IsCrepantBoundary (q ≫ sX) n KY D π hY' hbir D')
    (E : MMP.Mori.PrimeDivisor Y') (hE : E ∈ (coeffOnePart D').support)
    {JV : Finset (MMP.Mori.PrimeDivisor Y)} (hJV : JV ⊆ (coeffOnePart D).support) {v : Y}
    (hvJ : ∀ G ∈ JV, v ∈ G.support) (hcv : Order.coheight v = JV.card)
    (hEV : (E.support : Set Y') = π.base ⁻¹' closure {v})
    (hiso : ∀ x : Y', x ∉ E.support → IsIso (π.stalkMap x))
    (hinj : ∀ x x' : Y', x ∉ E.support → π x = π x' → x = x')
    (hdown : ∀ G ∈ (coeffOnePart D').support, G ≠ E →
      ∃ G₂ ∈ (coeffOnePart D).support, π G.genericPoint = G₂.genericPoint)
    {y : Y'}
    (hinv : ∀ S, IsSNCStratum (coeffOnePart D) S → π y ∈ S → ∃ f ∈ S,
      IsSNCStratum (coeffOnePart D) (closure {f}) ∧ q f = ξ₀ ∧
        Function.Bijective (q.residueFieldMap f))
    (S' : Set Y') (hS' : IsSNCStratum (coeffOnePart D') S') (hyS : y ∈ S') :
    ∃ f ∈ S', IsSNCStratum (coeffOnePart D') (closure {f}) ∧ (π ≫ q) f = ξ₀ ∧
      Function.Bijective ((π ≫ q).residueFieldMap f) := by
  classical
  haveI hYv : AlgebraicGeometry.IsVariety k (q ≫ sX) := hD.isProjectiveVariety.toIsVariety
  haveI : LocallyOfFiniteType (q ≫ sX) := hYv.toLocallyOfFiniteType
  haveI : QuasiCompact (q ≫ sX) := hYv.toQuasiCompact
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (q ≫ sX)
  haveI hY'v : AlgebraicGeometry.IsVariety k (π ≫ q ≫ sX) := hD'.isProjectiveVariety.toIsVariety
  haveI : LocallyOfFiniteType (π ≫ q ≫ sX) := hY'v.toLocallyOfFiniteType
  haveI : QuasiCompact (π ≫ q ≫ sX) := hY'v.toQuasiCompact
  haveI : CompactSpace Y' := QuasiCompact.compactSpace_of_compactSpace (π ≫ q ≫ sX)
  haveI : IsProper π := isProper_of_isProjectiveMorphism π hproj
  haveI : IsDominant π := hbir.isDominant
  have hsnc1 : (coeffOnePart D).IsSNC (q ≫ sX) :=
    hD.isSNC.of_support_subset (support_coeffOnePart_subset D)
  have hsnc1' : (coeffOnePart D').IsSNC (π ≫ q ≫ sX) :=
    hD'.isSNC.of_support_subset (support_coeffOnePart_subset D')
  have hn := hKY.topologicalKrullDim_eq
  obtain ⟨J', hJ', hmax'⟩ := hS'
  obtain ⟨s', hS's, hs'J, hcs'⟩ := coheight_eq_card_of_isSNCStratum hsnc1' hJ' hmax'
  set J'' := J'.erase E with hJ''
  have hJ''sub : J'' ⊆ (coeffOnePart D').support := (Finset.erase_subset _ _).trans hJ'
  obtain ⟨r₀, hr₀s, hr₀J, hcr₀, -⟩ := exists_stratum_specializes hsnc1' hJ''sub
    (fun G hG => hs'J G (Finset.mem_of_mem_erase hG))
  have hS'r₀ : S' ⊆ closure {r₀} := by
    rw [hS's]
    exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hr₀s))
      isClosed_closure
  have hyr₀ : y ∈ closure {r₀} := hS'r₀ hyS
  -- `r₀` is off `E`
  have hEJ'' : E ∉ J'' := Finset.notMem_erase E J'
  have hr₀E : r₀ ∉ E.support := by
    intro hmem
    obtain ⟨c, hc, hcard⟩ := card_le_coheight_of_isSNC hsnc1' r₀ (insert E J'')
      (Finset.insert_subset hE hJ''sub) (fun G hG => by
        rcases Finset.mem_insert.mp hG with rfl | hG
        · exact hmem
        · exact hr₀J G hG)
    rw [hcr₀] at hc
    have : c = J''.card := by exact_mod_cast hc.symm
    rw [Finset.card_insert_of_notMem hEJ'', this] at hcard
    omega
  haveI := hiso r₀ hr₀E
  set r := π r₀ with hr
  -- the floor components downstairs
  have hdown' : ∀ G ∈ J'', ∃ G₂ ∈ (coeffOnePart D).support, π G.genericPoint = G₂.genericPoint :=
    fun G hG => hdown G (hJ''sub hG) (Finset.ne_of_mem_erase hG)
  choose Gd hGdD hGd using hdown'
  set Gg : {G // G ∈ J''} → MMP.Mori.PrimeDivisor Y := fun G => Gd G.1 G.2 with hGg
  have hgenE : ∀ G ∈ J'', G.genericPoint ∉ E.support := by
    intro G hG hmem
    apply Finset.ne_of_mem_erase hG
    apply MMP.Fourfold.SNCWeight.PrimeDivisorUnion.eq_of_support_subset
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact closure_minimal (Set.singleton_subset_iff.mpr hmem) E.idealSheaf.support.isClosed
  have hGginj : Function.Injective Gg := by
    rintro ⟨G₁, hG₁⟩ ⟨G₂, hG₂⟩ h12
    simp only [hGg] at h12
    have h1 : π G₁.genericPoint = π G₂.genericPoint := by
      rw [hGd G₁ hG₁, hGd G₂ hG₂, h12]
    have h2 := hinj _ _ (hgenE G₁ hG₁) h1
    exact Subtype.ext (AlgebraicGeometry.PrimeDivisor.genericPoint_injective h2)
  set JY := J''.attach.image Gg with hJYdef
  have hJYsub : JY ⊆ (coeffOnePart D).support := by
    intro G hG
    obtain ⟨G', -, rfl⟩ := Finset.mem_image.mp hG
    exact hGdD G'.1 G'.2
  have hJYcard : JY.card = J''.card := by
    rw [hJYdef, Finset.card_image_of_injective _ hGginj, Finset.card_attach]
  have hrJY : ∀ G ∈ JY, r ∈ G.support := by
    intro G hG
    obtain ⟨G', -, rfl⟩ := Finset.mem_image.mp hG
    have hsp : G'.1.genericPoint ⤳ r₀ := by
      rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact hr₀J G'.1 G'.2
    have hsp' := π.base.hom.map_specializes hsp
    change π G'.1.genericPoint ⤳ r at hsp'
    rw [hGd G'.1 G'.2] at hsp'
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact specializes_iff_mem_closure.mp hsp'
  have hcr : Order.coheight r = JY.card := by
    have h := ringKrullDim_eq_of_ringEquiv (asIso (π.stalkMap r₀)).commRingCatIsoToRingEquiv
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight] at h
    have h' : Order.coheight r = Order.coheight r₀ := by exact_mod_cast h
    rw [h', hcr₀, hJYcard]
  have hbij := bijective_residueFieldMap_of_isIso_stalkMap π r₀
  -- the dimension of the stratum `closure {r}`
  have hJYn : JY.card ≤ n := by
    set Vr := Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure {r})
    have hrV : Set.range Vr.subschemeι.base = closure {r} := by
      rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal,
        TopologicalSpace.Closeds.coe_closure]
    have h1 := topologicalKrullDim_add_coheight_of_range (q ≫ sX) Vr.subschemeι hrV
    rw [hcr, hn] at h1
    exact le_of_withBot_add_eq (by exact_mod_cast h1)
  have hm : (n - JY.card) + JY.card = n := Nat.sub_add_cancel hJYn
  have hJ''C : J'' ⊆ D'.support := hJ''sub.trans (support_coeffOnePart_subset D')
  have hJ''1 : ∀ G ∈ J'', D'.coeff G = 1 := fun G hG =>
    coeff_eq_one_of_mem_support_coeffOnePart (hJ''sub hG)
  have hJYB : JY ⊆ D.support := hJYsub.trans (support_coeffOnePart_subset D)
  have hJY1 : ∀ G ∈ JY, D.coeff G = 1 := fun G hG =>
    coeff_eq_one_of_mem_support_coeffOnePart (hJYsub hG)
  have hπyr : π y ∈ closure {r} := by
    have := image_closure_subset_closure_image π.continuous ⟨y, hyr₀, rfl⟩
    rwa [Set.image_singleton] at this
  have hfin : ∀ {f : Y}, IsSNCStratum (coeffOnePart D) (closure {f}) → q f = ξ₀ →
      Function.Bijective (q.residueFieldMap f) → closure {f} ⊆ closure {r} →
      ∃ f' ∈ closure {r₀}, IsSNCStratum (coeffOnePart D') (closure {f'}) ∧
        (π ≫ q) f' = ξ₀ ∧ Function.Bijective ((π ≫ q).residueFieldMap f') ∧ π f' = f := by
    intro f hfst hfq hfb hFr
    obtain ⟨f', hf'r₀, hf'st, hf'gen, hf'b⟩ := exists_lift_of_stratum hD hD0 hD' hKY hKY' π rfl
      hproj hbir hcrep hJ''C hJ''1 hr₀J hcr₀ hJYB hJY1 hrJY hcr rfl hbij hm
      (liftProperty k _) hfst hFr
    have hπf' : π f' = f := hf'gen.eq isGenericPoint_closure
    refine ⟨f', hf'r₀, hf'st, ?_, ?_, hπf'⟩
    · rw [Scheme.Hom.comp_apply, hπf', hfq]
    · refine (bijective_residueFieldMap_comp_iff π q f' hf'b).mpr ?_
      rw [hπf']; exact hfb
  by_cases hEJ' : E ∈ J'
  · -- the stratum lies on `E`
    have hS'E : S' ⊆ E.support := hmax'.1.2.trans (Set.biInter_subset_of_mem hEJ')
    have hπyV : π y ∈ closure {v} := by
      have := hS'E hyS
      rw [hEV] at this
      exact this
    have hJVY : JV ∪ JY ⊆ (coeffOnePart D).support := Finset.union_subset hJV hJYsub
    have hπyJ : ∀ G ∈ JV ∪ JY, π y ∈ G.support := by
      intro G hG
      rcases Finset.mem_union.mp hG with hG | hG
      · exact closure_minimal (Set.singleton_subset_iff.mpr (hvJ G hG))
          G.idealSheaf.support.isClosed hπyV
      · exact closure_minimal (Set.singleton_subset_iff.mpr (hrJY G hG))
          G.idealSheaf.support.isClosed hπyr
    obtain ⟨ξS, hξS, hξSJ, hcξS, -⟩ := exists_stratum_specializes hsnc1 hJVY hπyJ
    have hSst : IsSNCStratum (coeffOnePart D) (closure {ξS}) :=
      isSNCStratum_closure_singleton hsnc1 ξS _ hJVY hξSJ hcξS
    obtain ⟨f, hfS, hfst, hfq, hfb⟩ := hinv _ hSst (specializes_iff_mem_closure.mp hξS)
    have hξSr : ξS ∈ closure {r} := mem_closure_of_specializes_of_stratum (q ≫ sX) hsnc1 hJYsub
      hrJY hcr (fun G hG => hξSJ G (Finset.mem_union_right _ hG)) hξS hπyr
    have hξSv : ξS ∈ closure {v} := mem_closure_of_specializes_of_stratum (q ≫ sX) hsnc1 hJV
      hvJ hcv (fun G hG => hξSJ G (Finset.mem_union_left _ hG)) hξS hπyV
    have hSr : closure {ξS} ⊆ closure {r} :=
      closure_minimal (Set.singleton_subset_iff.mpr hξSr) isClosed_closure
    have hSv : closure {ξS} ⊆ closure {v} :=
      closure_minimal (Set.singleton_subset_iff.mpr hξSv) isClosed_closure
    have hFr : closure {f} ⊆ closure {r} :=
      closure_minimal (Set.singleton_subset_iff.mpr (hSr hfS)) isClosed_closure
    obtain ⟨f', hf'r₀, hf'st, hf'q, hf'b, hπf'⟩ := hfin hfst hfq hfb hFr
    -- the lift lies in `S'`: the preimage in `closure {r₀}` of `closure {ξS}` is connected
    haveI : PerfectField k := inferInstance
    obtain ⟨hsm₀, -⟩ := stratum_closure (π ≫ q ≫ sX) hsnc1' hJ''sub hr₀J hcr₀
    obtain ⟨hsmR, -⟩ := stratum_closure (q ≫ sX) hsnc1 hJYsub hrJY hcr
    set V₀ := Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure {r₀})
      with hV₀
    set VR := Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure {r})
      with hVR
    haveI : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
    haveI : LocallyOfFinitePresentation (V₀.subschemeι ≫ π ≫ q ≫ sX) :=
      (LocallyOfFinitePresentation.iff_locallyOfFiniteType
        (f := V₀.subschemeι ≫ π ≫ q ≫ sX)).mpr inferInstance
    haveI : Smooth (V₀.subschemeι ≫ π ≫ q ≫ sX) := (MMP.Mori.isSmoothScheme_iff _).1 hsm₀
    haveI : LocallyOfFinitePresentation (VR.subschemeι ≫ q ≫ sX) :=
      (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := VR.subschemeι ≫ q ≫ sX)).mpr
        inferInstance
    haveI : Smooth (VR.subschemeι ≫ q ≫ sX) := (MMP.Mori.isSmoothScheme_iff _).1 hsmR
    haveI : IsReduced V₀.subscheme := isReduced_of_smooth (V₀.subschemeι ≫ π ≫ q ≫ sX)
    haveI : IsReduced VR.subscheme := isReduced_of_smooth (VR.subschemeι ≫ q ≫ sX)
    have hr₀V : Set.range V₀.subschemeι.base = closure {r₀} := by
      rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal,
        TopologicalSpace.Closeds.coe_closure]
    have hrV : Set.range VR.subschemeι.base = closure {r} := by
      rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal,
        TopologicalSpace.Closeds.coe_closure]
    haveI : IsIntegral V₀.subscheme :=
      isIntegral_of_isIrreducible_range V₀.subschemeι (hr₀V ▸ isIrreducible_singleton.closure)
    haveI : IsIntegral VR.subscheme :=
      isIntegral_of_isIrreducible_range VR.subschemeι (hrV ▸ isIrreducible_singleton.closure)
    haveI : IsNormal VR.subscheme := AlgebraicGeometry.isNormal_of_smooth (VR.subschemeι ≫ q ≫ sX)
    have hsub : Set.range (V₀.subschemeι ≫ π).base ⊆ Set.range VR.subschemeι.base := by
      rw [hrV, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hr₀V]
      exact image_closure_subset_closure_image π.continuous |>.trans (by rw [Set.image_singleton])
    obtain ⟨g, hg⟩ := exists_comp_eq_of_range_subset VR.subschemeι (V₀.subschemeι ≫ π) hsub
    haveI : IsProper g := MorphismProperty.of_postcomp @IsProper g VR.subschemeι
      (inferInstance : IsSeparated VR.subschemeι)
      (by rw [hg]; exact (inferInstance : IsProper (V₀.subschemeι ≫ π)))
    have hgen0 : V₀.subschemeι (genericPoint V₀.subscheme) = r₀ :=
      map_genericPoint_eq_of_range_closure _ hr₀V
    have hgenR : VR.subschemeι (genericPoint VR.subscheme) = r :=
      map_genericPoint_eq_of_range_closure _ hrV
    have hgb : IsBirationalMorphism g :=
      isBirationalMorphism_of_bijective_residueFieldMap V₀.subschemeι VR.subschemeι π g hg
        (by rw [hgen0, hgenR]) (by rw [hgen0]; exact hbij)
    -- the connected set
    obtain ⟨u, hu⟩ : ξS ∈ Set.range VR.subschemeι.base := hrV ▸ hξSr
    have ht : VR.subschemeι.base ⁻¹' closure {ξS} = closure {u} := by
      rw [VR.subschemeι.isEmbedding.isInducing.closure_eq_preimage_closure_image,
        Set.image_singleton, hu]
    have hconn := isConnected_preimage_of_isBirationalMorphism g hgb
      (t := VR.subschemeι.base ⁻¹' closure {ξS}) (ht ▸ isClosed_closure)
      (ht ▸ isIrreducible_singleton.closure.isConnected)
    set A := V₀.subschemeι.base '' (g.base ⁻¹' (VR.subschemeι.base ⁻¹' closure {ξS})) with hA
    have hAconn : _root_.IsPreconnected A :=
      (hconn.image _ V₀.subschemeι.continuous.continuousOn).isPreconnected
    have hgapp : ∀ a, π (V₀.subschemeι a) = VR.subschemeι (g a) := fun a => by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hg]
    have hmemA : ∀ x ∈ closure {r₀}, π x ∈ closure {ξS} → x ∈ A := by
      intro x hx hπx
      obtain ⟨a, rfl⟩ : x ∈ Set.range V₀.subschemeι.base := hr₀V ▸ hx
      refine ⟨a, ?_, rfl⟩
      change VR.subschemeι (g a) ∈ closure {ξS}
      rw [← hgapp]; exact hπx
    have hAJ : A ⊆ ⋂ G ∈ J', (G.support : Set Y') := by
      rintro _ ⟨a, ha, rfl⟩
      have hx0 : V₀.subschemeι a ∈ closure {r₀} := hr₀V ▸ ⟨a, rfl⟩
      refine Set.mem_iInter₂.mpr fun G hG => ?_
      by_cases hGE : G = E
      · subst hGE
        rw [hEV]
        change π (V₀.subschemeι a) ∈ closure {v}
        rw [hgapp]
        exact hSv ha
      · exact closure_minimal (Set.singleton_subset_iff.mpr
          (hr₀J G (Finset.mem_erase.mpr ⟨hGE, hG⟩))) G.idealSheaf.support.isClosed hx0
    haveI : AlgebraicGeometry.IsNoetherian Y' := ⟨⟩
    have hcl' : IsClosed (⋂ G ∈ J', (G.support : Set Y')) :=
      isClosed_biInter fun G _ => G.idealSheaf.support.isClosed
    obtain ⟨hfin, hcov⟩ := MMP.Resolution.Aux.finite_and_cover_componentsOf hcl'
    have hsubS' := subset_of_isPreconnected_of_pairwise_disjoint hfin
      (fun C hC => MMP.Resolution.Aux.isClosed_of_mem_componentsOf hcl' hC)
      (fun C hC C' hC' x hxC hxC' =>
        eq_of_mem_componentsOf_biInter (π ≫ q ≫ sX) hsnc1' hJ' hC hC' hxC hxC')
      hAconn (fun x hx => by
        obtain ⟨C, hC, hxC⟩ := hcov (hAJ hx)
        exact ⟨C, hC, hxC⟩)
      (hmax' : S' ∈ MMP.Resolution.componentsOf _)
      (hmemA y hyr₀ (specializes_iff_mem_closure.mp hξS)) hyS
    have hf'S' : f' ∈ S' := hsubS' (hmemA f' hf'r₀ (by rw [hπf']; exact hfS))
    exact ⟨f', hf'S', hf'st, hf'q, hf'b⟩
  · -- the stratum is the strict transform `closure {r₀}`
    have hJ''eq : J'' = J' := Finset.erase_eq_of_notMem hEJ'
    have hS'eq : S' = closure {r₀} := by
      refine (hmax'.eq_of_ge ⟨isIrreducible_singleton.closure, ?_⟩ hS'r₀).symm
      rw [← hJ''eq]
      exact closure_minimal (Set.singleton_subset_iff.mpr (Set.mem_iInter₂.mpr hr₀J))
        (isClosed_biInter fun G _ => G.idealSheaf.support.isClosed)
    have hSst : IsSNCStratum (coeffOnePart D) (closure {r}) :=
      isSNCStratum_closure_singleton hsnc1 r JY hJYsub hrJY hcr
    obtain ⟨f, hfS, hfst, hfq, hfb⟩ := hinv _ hSst hπyr
    have hFr : closure {f} ⊆ closure {r} :=
      closure_minimal (Set.singleton_subset_iff.mpr hfS) isClosed_closure
    obtain ⟨f', hf'r₀, hf'st, hf'q, hf'b, -⟩ := hfin hfst hfq hfb hFr
    exact ⟨f', hS'eq ▸ hf'r₀, hf'st, hf'q, hf'b⟩

/-- The centre of a stratum blow-up has snc with the boundary. -/
private theorem hasSNCWith_of_stalk_eq' {k : Type} [Field k] {Y : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} [AlgebraicGeometry.IsNoetherian Y] {T : Set Y}
    (hT : MMP.Resolution.IsSNCClosedSubset sY T) {Z : Y.IdealSheafData}
    {JV : Finset (MMP.Mori.PrimeDivisor Y)}
    (hJne : JV.Nonempty) (hJT : ∀ G ∈ JV, (G.support : Set Y) ⊆ T)
    (hZT : ∀ G ∈ JV, (Z.support : Set Y) ⊆ G.support)
    (hZst : ∀ x ∈ Z.support, IdealSheafData.stalk Z x =
      ⨆ G ∈ JV, IdealSheafData.stalk G.idealSheaf x) :
    MMP.Resolution.HasSNCWith (MMP.Resolution.componentsFamily T) Z := by
  classical
  intro x hx
  have hGc : ∀ G ∈ JV, (G.support : Set Y) ∈ MMP.Resolution.componentsOf T := fun G hG =>
    support_mem_componentsOf_of_isSNCClosedSubset hT (hJT G hG)
  obtain ⟨hDc, hempty | ⟨-, -, hfam⟩⟩ := hT
  · exfalso
    obtain ⟨G, hG⟩ := hJne
    have := hJT G hG (hZT G hG hx)
    rw [hempty] at this
    exact this
  have hideal : ∀ G (hG : G ∈ JV), MMP.Resolution.componentsFamily T ⟨_, hGc G hG⟩ =
      G.idealSheaf := fun G hG =>
    MMP.Fourfold.SNCWeight.PrimeDivisorUnion.componentsFamily_eq_idealSheaf ⟨_, hGc G hG⟩ G rfl
  have hmem : ∀ G (hG : G ∈ JV), x ∈ (MMP.Resolution.componentsFamily T ⟨_, hGc G hG⟩).support :=
    fun G hG => by rw [hideal G hG]; exact hZT G hG hx
  obtain ⟨N, z, c, hz, hI, hcinj⟩ := hfam.2 x
  refine ⟨N, z, c, Finset.univ.filter
    (fun i => ∃ G, ∃ hG : G ∈ JV, i = c ⟨⟨_, hGc G hG⟩, hmem G hG⟩), hz, hI, hcinj, ?_⟩
  rw [hZst x hx]
  refine iSup_eq_span_image z JV _ _ (fun G hG => ⟨_, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, G, hG, rfl⟩, ?_⟩) fun i hi => ?_
  · rw [← hideal G hG]; exact hI ⟨⟨_, hGc G hG⟩, hmem G hG⟩
  · obtain ⟨-, G, hG, rfl⟩ := Finset.mem_filter.mp hi
    exact ⟨G, hG, by rw [← hideal G hG]; exact hI ⟨⟨_, hGc G hG⟩, hmem G hG⟩⟩

open scoped Classical in
open MMP.Threefold.Resolution MMP.Fourfold.SNCWeight.StratumBlowup in
/-- **The invariant survives a stratum blow-up.** Blowing up a stratum `V` of `q⁻¹ L` through
the image of `y` gives a model satisfying the invariant at `y`: the blow-up is smooth and
projective, the total transform of `q⁻¹ L` is snc, `(Bl_V Y, π⁻¹ q⁻¹ L)` is crepant over
`(Y, q⁻¹ L)` with reduced boundaries, and strata lift by `towerStep_inv`. -/
private theorem TowerGood.blowUp {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {n : ℕ} {L : Set X} {ξ₀ : X} {Y : Scheme.{0}}
    (q : Y ⟶ X) (Z : Y.IdealSheafData) (y : blowUp Z)
    (hq : TowerGood sX n L ξ₀ q (blowUpToBase Z y))
    (hJ : ∃ J : Set (Set Y), J.Nonempty ∧ J ⊆ MMP.Resolution.componentsOf (q.base ⁻¹' L) ∧
      (Z.support : Set Y) ∈ MMP.Resolution.componentsOf (⋂₀ J))
    (hZ : Z = Scheme.IdealSheafData.vanishingIdeal Z.support)
    (hy : blowUpToBase Z y ∈ Z.support) :
    TowerGood sX n L ξ₀ (blowUpToBase Z ≫ q) y := by
  classical
  have hq' := hq
  obtain ⟨_, _, _, hsm, hprojY, hdim, hsnc, hinv⟩ := hq
  haveI hYv : AlgebraicGeometry.IsVariety k (q ≫ sX) := hprojY.toIsVariety
  haveI : LocallyOfFiniteType (q ≫ sX) := hYv.toLocallyOfFiniteType
  haveI : QuasiCompact (q ≫ sX) := hYv.toQuasiCompact
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (q ≫ sX)
  haveI : AlgebraicGeometry.IsNoetherian Y := ⟨⟩
  haveI : LocallyOfFinitePresentation (q ≫ sX) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := q ≫ sX)).mpr inferInstance
  haveI : Smooth (q ≫ sX) := (MMP.Mori.isSmoothScheme_iff _).1 hsm
  set T := q.base ⁻¹' L with hT
  have hTf := finite_setOf_support_subset_of_isSNCClosedSubset hsnc
  set DY := reducedDivisorOfSet T hTf with hDY
  have hDYp := isSNCSubboundaryPair_reducedDivisorOfSet hprojY hsm hsnc hTf
  have hsncD1 : (coeffOnePart DY).IsSNC (q ≫ sX) :=
    hDYp.isSNC.of_support_subset (support_coeffOnePart_subset _)
  -- the centre is a stratum
  obtain ⟨J, hJne, hJT, hZJ⟩ := hJ
  have hVst : IsSNCStratum (coeffOnePart DY) (Z.support : Set Y) :=
    (isComponentStratum_iff_isSNCStratum hsnc hTf _).mp ⟨J, hJT, hZJ⟩
  obtain ⟨JV, hJV, hmaxV⟩ := hVst
  obtain ⟨v, hVv, hvJ, hcv⟩ := coheight_eq_card_of_isSNCStratum hsncD1 hJV hmaxV
  have hJVT : ∀ G ∈ JV, (G.support : Set Y) ⊆ T := fun G hG =>
    (support_coeffOnePart_reducedDivisorOfSet T hTf G).mp (hJV hG)
  have hJVne : JV.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    obtain ⟨W, hW⟩ := hJne
    obtain ⟨P, -, hPW⟩ := exists_primeDivisor_of_mem_componentsOf hsnc (hJT hW)
    have hZu : (Z.support : Set Y) = Set.univ :=
      (hmaxV.eq_of_ge ⟨IrreducibleSpace.isIrreducible_univ Y, by simp⟩ (Set.subset_univ _)).symm
    have hsub : (Set.univ : Set Y) ⊆ P.support := by
      rw [← hZu, ← hPW]; exact hZJ.1.2.trans (Set.sInter_subset_of_mem hW)
    have hgY : genericPoint Y ∈ P.support := hsub trivial
    have hsp : P.genericPoint ⤳ genericPoint Y := by
      rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact hgY
    have heq : P.genericPoint = genericPoint Y := (hsp.antisymm (genericPoint_specializes _)).eq
    have h1 := MMP.Mori.PrimeDivisor.coheight_genericPoint P
    rw [heq, Order.coheight_eq_zero.mpr fun b _ =>
      Scheme.le_iff_specializes.mpr (genericPoint_specializes b)] at h1
    exact absurd h1 (by decide)
  have hZeq : Z = Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure {v}) := by
    rw [hZ]; congr 1; ext1; rw [hVv]; rfl
  have hZsupp : (Z.support : Set Y) = closure {v} := by
    rw [hZeq, Scheme.IdealSheafData.coe_support_vanishingIdeal,
      TopologicalSpace.Closeds.coe_closure]
  have hZT : ∀ G ∈ JV, (Z.support : Set Y) ⊆ G.support := fun G hG => by
    rw [hZsupp]
    exact closure_minimal (Set.singleton_subset_iff.mpr (hvJ G hG)) G.idealSheaf.support.isClosed
  obtain ⟨hZsm, hZst⟩ := stratum_closure (q ≫ sX) hsncD1 hJV hvJ hcv
  rw [← hZeq] at hZsm hZst
  have hZst' : ∀ x ∈ Z.support, IdealSheafData.stalk Z x =
      ⨆ G ∈ JV, IdealSheafData.stalk G.idealSheaf x := fun x hx => by
    rw [← SetLike.mem_coe, hZsupp] at hx
    exact hZst x hx
  by_cases hJV1 : JV.card = 1
  · -- a divisorial centre: the blow-up is an isomorphism
    obtain ⟨P, rfl⟩ := Finset.card_eq_one.mp hJV1
    have hvP : v = P.genericPoint := by
      have hsp : P.genericPoint ⤳ v := by
        rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact hvJ P (Finset.mem_singleton_self P)
      by_contra hne
      have hlt : v < P.genericPoint := lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hsp)
        (fun h => hne (hsp.antisymm (Scheme.le_iff_specializes.mp h)).eq.symm)
      have := Order.coheight_strictAnti hlt (by
        rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]; exact ENat.coe_lt_top _)
      rw [hcv, AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at this
      simp at this
    have hZP : Z = P.idealSheaf := by
      haveI := P.integral
      rw [hZeq]
      refine (Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme P.idealSheaf _ ?_).symm
      ext1
      rw [TopologicalSpace.Closeds.coe_closure, hvP,
        ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    have hcart : Stacks.Divisors.IsEffectiveCartierDivisor Z := by
      rw [hZP]; exact MMP.Resolution.Aux.isEffectiveCartierDivisor_idealSheaf (q ≫ sX) hsm P
    haveI := Stacks.Blowup.isIso_blowUpToBase_of_isEffectiveCartierDivisor Z hcart
    exact TowerGood.comp_iso (blowUpToBase Z) hq'
  have hc2 : 2 ≤ JV.card := by
    have := Finset.card_pos.mpr hJVne
    omega
  -- the blow-up
  have hirr : IsIrreducible (Z.support : Set Y) := hZsupp ▸ isIrreducible_singleton.closure
  have hcodim : codimension (⟨Z.support, hirr, Z.support.isClosed⟩ :
      TopologicalSpace.IrreducibleCloseds Y) = JV.card := by
    have heq : (⟨Z.support, hirr, Z.support.isClosed⟩ : TopologicalSpace.IrreducibleCloseds Y) =
        TopologicalSpace.IrreducibleCloseds.closureSingleton v := by
      ext1; exact hZsupp
    rw [heq, Stacks.Divisors.PrimeDivisor.codimension_closureSingleton, hcv]
  have hc1' : 1 ≤ codimension (⟨Z.support, hirr, Z.support.isClosed⟩ :
      TopologicalSpace.IrreducibleCloseds Y) := by
    rw [hcodim]; exact_mod_cast (by omega : 1 ≤ JV.card)
  have hsb : MMP.Resolution.IsSmoothBlowup (q ≫ sX) Z := ⟨hsm, hZsm⟩
  obtain ⟨hvar, hsmB, hprojB, hbirB, -, hprojV, -⟩ :=
    isVariety_smooth_blowUpToBase_divisorOfForm_pullbackRationalPluriForms
      (q ≫ sX) hYv hdim Z hsb hirr hcodim.symm hc2
  set π := blowUpToBase Z with hπ
  haveI := isIntegral_blowUp_of_one_le_codimension Z hirr hc1'
  haveI := isDominant_blowUpToBase Z hirr hc1'
  haveI : Smooth (π ≫ q ≫ sX) := hsmB
  haveI : IsLocallyNoetherian (AlgebraicGeometry.blowUp Z) :=
    MMP.Resolution.isLocallyNoetherian_of_smooth (π ≫ q ≫ sX)
  haveI : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
  haveI : IsNormal (AlgebraicGeometry.blowUp Z) := AlgebraicGeometry.isNormal_of_smooth (π ≫ q ≫ sX)
  haveI : IsProper π := hprojB.isProper
  haveI : LocallyOfFiniteType (π ≫ q ≫ sX) := hvar.toLocallyOfFiniteType
  haveI : QuasiCompact (π ≫ q ≫ sX) := hvar.toQuasiCompact
  haveI : CompactSpace (AlgebraicGeometry.blowUp Z) :=
    QuasiCompact.compactSpace_of_compactSpace (π ≫ q ≫ sX)
  haveI : AlgebraicGeometry.IsNoetherian (AlgebraicGeometry.blowUp Z) := ⟨⟩
  have hNπ : IsNormalVariety k (π ≫ q ≫ sX) := ⟨hvar, inferInstance⟩
  have hYnv : IsNormalVariety k (q ≫ sX) := ⟨hYv, inferInstance⟩
  have hprojY' : MMP.Mori.IsProjectiveVariety k (π ≫ q ≫ sX) := hprojV hprojY
  have hsmY' : IsSmoothScheme (π ≫ q ≫ sX) := (MMP.Mori.isSmoothScheme_iff _).mpr hsmB
  have hdim' : topologicalKrullDim (AlgebraicGeometry.blowUp Z) = n :=
    topologicalKrullDim_eq_of_isBirationalMorphism (q ≫ sX) π hbirB hdim
  -- the total transform
  have hZS : (Z.support : Set Y) ⊆ T := by
    obtain ⟨G₀, hG₀⟩ := hJVne
    exact (hZT G₀ hG₀).trans (hJVT G₀ hG₀)
  have hsnc' : MMP.Resolution.IsSNCClosedSubset (π ≫ q ≫ sX) (π.base ⁻¹' T) := by
    have hZ' := hasSNCWith_of_stalk_eq' hsnc hJVne hJVT hZT hZst'
    have h := MMP.Resolution.isSNCClosedSubset_totalTransformStep (q ≫ sX) hsm hsnc hZ'
    rw [MMP.Fourfold.SNCWeight.SNCBlowup.totalTransformStep_eq hsnc.1 hZS] at h
    exact h
  have hT' : (π ≫ q).base ⁻¹' L = π.base ⁻¹' T := rfl
  refine ⟨inferInstance, inferInstance, inferInstance, by rw [Category.assoc]; exact hsmY',
    by rw [Category.assoc]; exact hprojY', hdim', by rw [Category.assoc, hT']; exact hsnc', ?_⟩
  intro S' hS' hyS'
  have hT'f := finite_setOf_support_subset_of_isSNCClosedSubset hsnc'
  set DY' := reducedDivisorOfSet (π.base ⁻¹' T) hT'f with hDY'
  have hDY'p := isSNCSubboundaryPair_reducedDivisorOfSet hprojY' hsmY' hsnc' hT'f
  rw [hT'] at hS'
  have hS'st := (isComponentStratum_iff_isSNCStratum hsnc' hT'f _).mp hS'
  obtain ⟨KY, hKY⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (q ≫ sX) hsm hdim
  obtain ⟨KY', hKY'⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (π ≫ q ≫ sX)
    hsmY' hdim'
  haveI : IsSeparated (q ≫ sX) := hYv.toIsSeparated
  have hπproj : IsProjectiveMorphism π := IsProjectiveMorphism.of_comp π (q ≫ sX)
    hprojY'.isProjective
  set E := excE (q ≫ sX) hsb hirr hc1' with hE
  have hEsupp : (E.support : Set (AlgebraicGeometry.blowUp Z)) = π.base ⁻¹' Z.support :=
    coe_support_excE (q ≫ sX) hsb hirr hc1'
  have hEmem : E ∈ (coeffOnePart DY').support :=
    (support_coeffOnePart_reducedDivisorOfSet _ _ E).mpr (by
      rw [hEsupp]; exact Set.preimage_mono hZS)
  have hPY : MMP.Mori.IsPair (q ≫ sX) DY :=
    ⟨hYnv, n, KY, hKY, MMP.Fourfold.isQCartier_of_isSmoothScheme hsm _⟩
  have hsncJV : DivisorWithCoeffs.IsSNC (q ≫ sX) (∑ G ∈ JV, Finsupp.single G (1 : ℤ)) :=
    hsncD1.of_support_subset fun G hG => hJV ((mem_support_sum_single JV G).mp hG)
  have hΔ : ∀ Γ : MMP.Mori.PrimeDivisor Y, (Z.support : Set Y) ⊆ Γ.support →
      DY.coeff Γ = if Γ ∈ JV then 1 else 0 := by
    intro Γ hΓ
    rw [hDY, coeff_reducedDivisorOfSet]
    by_cases hΓJ : Γ ∈ JV
    · rw [if_pos (hJVT Γ hΓJ), if_pos hΓJ]
    · rw [if_neg hΓJ, if_neg]
      intro hΓT
      have hvΓ : v ∈ Γ.support := hΓ (hZsupp ▸ subset_closure rfl)
      obtain ⟨c, hc, hcard⟩ := card_le_coheight_of_isSNC hsncD1 v (insert Γ JV)
        (Finset.insert_subset ((support_coeffOnePart_reducedDivisorOfSet T hTf Γ).mpr hΓT) hJV)
        (fun G hG => by
          rcases Finset.mem_insert.mp hG with rfl | hG
          · exact hvΓ
          · exact hvJ G hG)
      rw [hcv] at hc
      have hcJ : c = JV.card := by exact_mod_cast hc.symm
      rw [Finset.card_insert_of_notMem hΓJ, hcJ] at hcard
      omega
  have hcrep : ∀ hY' : IsNormalVariety k (π ≫ q ≫ sX),
      IsCrepantBoundary (q ≫ sX) n KY DY π hY' hbirB DY' := by
    intro hY' H
    by_cases hHE : H = E
    · subst hHE
      have h1 := MMP.Fourfold.isDiscrepancy_excE_neg_one (q ≫ sX) hKY hPY hsb hirr (by rw [hcodim])
        (by omega) hsncJV hZT hZst' hΔ hY' hc1' hbirB
      rw [hDY', coeff_reducedDivisorOfSet, if_pos (by rw [hEsupp]; exact Set.preimage_mono hZS)]
      exact h1
    · have hnex : ¬ (⟨AlgebraicGeometry.blowUp Z, π, hY', hbirB, H⟩ :
          DivisorOver k (q ≫ sX)).IsExceptional := by
        rw [isExceptional_iff_two_le_coheight hYnv]
        change ¬ 2 ≤ Order.coheight (π H.genericPoint)
        rw [coheight_map_genericPoint (q ≫ sX) hsb hirr hc1' hHE]
        decide
      obtain ⟨P, hcen, hP⟩ := MMP.Mori.DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff
        ⟨hYnv, hKY, MMP.Fourfold.isQCartier_of_isSmoothScheme hsm _⟩ _ hnex
      have hcl : closure {π H.genericPoint} = (P.support : Set Y) := by
        rw [← hcen, MMP.Positivity.DivisorOver.center_eq_closureSingleton]
        rfl
      have hiff : (H.support : Set (AlgebraicGeometry.blowUp Z)) ⊆ π.base ⁻¹' T ↔
          (P.support : Set Y) ⊆ T := by
        constructor
        · intro h
          rw [← hcl]
          exact closure_minimal (Set.singleton_subset_iff.mpr
            (h (MMP.Positivity.PrimeDivisor.genericPoint_mem_support' H))) hsnc.1
        · intro h
          rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
          exact closure_minimal (Set.singleton_subset_iff.mpr
            (h (hcl ▸ subset_closure rfl))) (hsnc.1.preimage π.continuous)
      have hcoeq : DY'.coeff H = DY.coeff P := by
        rw [hDY', hDY, coeff_reducedDivisorOfSet, coeff_reducedDivisorOfSet]
        by_cases h : (P.support : Set Y) ⊆ T
        · rw [if_pos (hiff.mpr h), if_pos h]
        · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]
      rw [hcoeq]
      exact hP
  have hdown : ∀ G ∈ (coeffOnePart DY').support, G ≠ E →
      ∃ G₂ ∈ (coeffOnePart DY).support, π G.genericPoint = G₂.genericPoint := by
    intro G hG hGE
    refine ⟨downPrime (q ≫ sX) hsb hirr hc1' hGE, ?_,
      (genericPoint_downPrime (q ≫ sX) hsb hirr hc1' hGE).symm⟩
    refine (support_coeffOnePart_reducedDivisorOfSet T hTf _).mpr ?_
    have hGT := (support_coeffOnePart_reducedDivisorOfSet _ hT'f G).mp hG
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    change closure {MMP.Mori.PrimeDivisor.genericPoint (downPrime (q ≫ sX) hsb hirr hc1' hGE)} ⊆ T
    rw [genericPoint_downPrime (q ≫ sX) hsb hirr hc1' hGE]
    exact closure_minimal (Set.singleton_subset_iff.mpr
      (hGT (MMP.Positivity.PrimeDivisor.genericPoint_mem_support' G))) hsnc.1
  have hiso : ∀ x : AlgebraicGeometry.blowUp Z, x ∉ E.support → IsIso (π.stalkMap x) := by
    intro x hx
    have hx' : π x ∉ (Z.support : Set Y) := fun h => hx (by
      change x ∈ (E.support : Set (AlgebraicGeometry.blowUp Z)); rw [hEsupp]; exact h)
    exact MMP.isIso_stalkMap_of_mem_biregularLocus π (mem_biregularLocus_of_notMem Z hx')
  have hinj : ∀ x x' : AlgebraicGeometry.blowUp Z, x ∉ E.support → π x = π x' → x = x' := by
    intro x x' hx h
    have hx' : π x ∉ (Z.support : Set Y) := fun h' => hx (by
      change x ∈ (E.support : Set (AlgebraicGeometry.blowUp Z)); rw [hEsupp]; exact h')
    exact eq_of_map_eq_of_notMem Z hx' h
  have hEV : (E.support : Set (AlgebraicGeometry.blowUp Z)) = π.base ⁻¹' closure {v} := by
    rw [hEsupp, hZsupp]
  have hinv' : ∀ S, IsSNCStratum (coeffOnePart DY) S → π y ∈ S → ∃ f ∈ S,
      IsSNCStratum (coeffOnePart DY) (closure {f}) ∧ q f = ξ₀ ∧
        Function.Bijective (q.residueFieldMap f) := by
    intro S hS hπyS
    obtain ⟨f, hfS, hfst, hfq, hfb⟩ :=
      hinv S ((isComponentStratum_iff_isSNCStratum hsnc hTf S).mpr hS) hπyS
    exact ⟨f, hfS, (isComponentStratum_iff_isSNCStratum hsnc hTf _).mp hfst, hfq, hfb⟩
  have hD0 : ∀ P, 0 ≤ DY.coeff P := fun P => by
    rw [hDY, coeff_reducedDivisorOfSet]; split_ifs <;> norm_num
  obtain ⟨f, hfS', hfst, hfq, hfb⟩ := towerStep_inv q π hDYp hD0 hDY'p hKY hKY' hπproj hbirB
    hcrep E hEmem hJV hvJ hcv hEV hiso hinj hdown hinv' S' hS'st hyS'
  refine ⟨f, hfS', ?_, hfq, hfb⟩
  rw [hT']
  exact (isComponentStratum_iff_isSNCStratum hsnc' hT'f _).mpr hfst

/-- The floor part `B^{=1}` of an snc subboundary, as an `ℝ`-divisor. -/
private noncomputable abbrev floorRDivisor {X : Scheme.{0}} (B : QDivisor X) : RDivisor X :=
  QDivisor.toRDivisor (Divisor.toQDivisor (coeffOnePart B))

private theorem coeff_floorRDivisor {X : Scheme.{0}} (B : QDivisor X)
    (G : MMP.Mori.PrimeDivisor X) :
    (floorRDivisor B).coeff G = if B.coeff G = 1 then 1 else 0 := by
  rw [floorRDivisor, QDivisor.coeff_toRDivisor, Divisor.coeff_toQDivisor, coeff_coeffOnePart]
  split_ifs <;> simp

/-- The coefficient-one locus of `B^{=1}` is the union of the floor components of `B`. -/
private theorem oneLocus_floorRDivisor {X : Scheme.{0}} (B : QDivisor X) :
    oneLocus (floorRDivisor B) =
      ⋃ G ∈ (coeffOnePart B).support, (G.support : Set X) := by
  ext x
  simp only [oneLocus, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨G, hG, hx⟩
    rw [coeff_floorRDivisor] at hG
    split_ifs at hG with h
    · exact ⟨G, mem_support_coeffOnePart h, hx⟩
    · norm_num at hG
  · rintro ⟨G, hG, hx⟩
    refine ⟨G, ?_, hx⟩
    rw [coeff_floorRDivisor, if_pos (coeff_eq_one_of_mem_support_coeffOnePart hG)]

/-- **The base of the tower.** -/
private theorem towerGood_id {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} (hB : IsSNCSubboundaryPair sX B) {n : ℕ}
    (hdim : topologicalKrullDim X = n) {ξ₀ : X}
    (hZ : IsSNCStratum (coeffOnePart B) (closure {ξ₀})) :
    TowerGood sX n (oneLocus (floorRDivisor B)) ξ₀ (𝟙 X) ξ₀ := by
  haveI : LocallyOfFiniteType sX := hB.isProjectiveVariety.toIsVariety.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hB.isProjectiveVariety.toIsVariety.toQuasiCompact
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : AlgebraicGeometry.IsNoetherian X := ⟨⟩
  have hsnc1 : (coeffOnePart B).IsSNC sX :=
    hB.isSNC.of_support_subset (support_coeffOnePart_subset B)
  have hL : MMP.Resolution.IsSNCClosedSubset sX (oneLocus (floorRDivisor B)) := by
    rw [oneLocus_floorRDivisor]
    exact MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isSNCClosedSubset_of_isSNC sX hsnc1
  have hpre : (𝟙 X : X ⟶ X).base ⁻¹' oneLocus (floorRDivisor B) =
      oneLocus (floorRDivisor B) := rfl
  refine ⟨inferInstance, inferInstance, inferInstance, by rw [Category.id_comp]; exact
    hB.isSmoothScheme, by rw [Category.id_comp]; exact hB.isProjectiveVariety, hdim,
    by rw [Category.id_comp, hpre]; exact hL, ?_⟩
  intro S _ hξS
  refine ⟨ξ₀, hξS, ?_, rfl, ?_⟩
  · rw [hpre]
    have hTf := finite_setOf_support_subset_of_isSNCClosedSubset hL
    refine (isComponentStratum_iff_isSNCStratum hL hTf _).mpr ?_
    obtain ⟨J, hJ, hmax⟩ := hZ
    refine ⟨J, fun G hG => ?_, hmax⟩
    refine (support_coeffOnePart_reducedDivisorOfSet _ hTf G).mpr ?_
    rw [oneLocus_floorRDivisor]
    exact Set.subset_biUnion_of_mem (u := fun G : MMP.Mori.PrimeDivisor X => (G.support : Set X))
      (hJ hG)
  · exact bijective_residueFieldMap_of_isIso_stalkMap (𝟙 X) ξ₀

/-- **The toroidal model.** Let `ξ₀` be the generic point of a floor stratum of an snc subboundary
pair `(X, B)` and `v` an exceptional divisor over `X` centred at `ξ₀` with log discrepancy zero
over the floor part `B^{=1}`. The zero-place extraction realizes `v` as a prime divisor `E_W` on a
composite `p : W ⟶ X` of floor-stratum blow-ups, and `E_W` contains a stratum of
`p⁻¹ (B^{=1})` mapping birationally onto `closure {ξ₀}`. -/
private theorem exists_tower {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} (hB : IsSNCSubboundaryPair sX B) {n : ℕ} (hdim : topologicalKrullDim X = n)
    {ξ₀ : X} (hZ : IsSNCStratum (coeffOnePart B) (closure {ξ₀}))
    (hξL : ξ₀ ∈ oneLocus (floorRDivisor B))
    (v : MMP.Flips.ProperDivisorOver k sX) (hv : v.IsExceptional)
    (hv0 : MMP.Intersection.IsLogDiscrepancy sX n (floorRDivisor B) v.toDivisorOver 0)
    (hvc : v.f v.E.genericPoint = ξ₀) :
    ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W) (_ : IsNormal W)
      (_ : CompactSpace W) (p : W ⟶ X) (hN : IsNormalVariety k (p ≫ sX))
      (hb : IsBirationalMorphism p) (EW : MMP.Mori.PrimeDivisor W),
      MMP.Mori.IsProjectiveVariety k (p ≫ sX) ∧ IsSmoothScheme (p ≫ sX) ∧
      (⟨W, p, hN, hb, EW⟩ : DivisorOver k sX).valuation = v.valuation ∧
      (∀ F : MMP.Mori.PrimeDivisor W,
        MMP.Mori.RationalMap.IsExceptional (X := W) p.toRationalMap F →
        MMP.Intersection.IsLogDiscrepancy sX n (floorRDivisor B) ⟨W, p, hN, hb, F⟩ 0) ∧
      MMP.Resolution.IsSNCClosedSubset (p ≫ sX)
        (p.base ⁻¹' oneLocus (floorRDivisor B)) ∧
      ∃ f ∈ (EW.support : Set W),
        IsComponentStratum (p.base ⁻¹' oneLocus (floorRDivisor B)) (closure {f}) ∧
          p f = ξ₀ ∧ Function.Bijective (p.residueFieldMap f) := by
  haveI : LocallyOfFiniteType sX := hB.isProjectiveVariety.toIsVariety.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hB.isProjectiveVariety.toIsVariety.toQuasiCompact
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have hsnc1 : (coeffOnePart B).IsSNC sX :=
    hB.isSNC.of_support_subset (support_coeffOnePart_subset B)
  have hB0 : (0 : RDivisor X) ≤ floorRDivisor B := Finsupp.le_def.mpr fun P => by
    change (0 : ℝ) ≤ (floorRDivisor B).coeff P
    rw [coeff_floorRDivisor]; split_ifs <;> norm_num
  have hB1 : ∀ P, (floorRDivisor B).coeff P ≤ 1 := fun P => by
    rw [coeff_floorRDivisor]; split_ifs <;> norm_num
  have hBs : (floorRDivisor B).IsSNC sX := hsnc1.of_support_subset fun G hG => by
    rw [Finsupp.mem_support_iff] at hG ⊢
    intro h0
    apply hG
    change (floorRDivisor B).coeff G = 0
    rw [floorRDivisor, QDivisor.coeff_toRDivisor, Divisor.coeff_toQDivisor]
    have h0' : (coeffOnePart B).coeff G = 0 := h0
    rw [h0']
    simp
  obtain ⟨W, _, _, _, _, p, hN, hb, EW, hproj, hsm, hP, hval, hexc, hsncS, -⟩ :=
    exists_stratumBlowups_valuation_eq_of_isLogDiscrepancy_eq_zero sX hB.isProjectiveVariety
      hB.isSmoothScheme (floorRDivisor B) hB0 hB1 hBs v hv n hv0
  have hpη : p EW.genericPoint = ξ₀ := by
    rw [← hvc]
    exact MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq
      hB.isProjectiveVariety.toIsVariety hval
  have hgood := hP (fun q y => q y = ξ₀ →
      TowerGood sX n (oneLocus (floorRDivisor B)) ξ₀ q y)
    (fun x hx => by obtain rfl : x = ξ₀ := hx; exact towerGood_id hB hdim hZ)
    (fun e _ q y h hey => TowerGood.comp_iso e (h hey))
    (fun q Z y h hJ hZ' hy hqy => TowerGood.blowUp q Z y (h hqy) hJ hZ' hy) hpη
  obtain ⟨_, _, _, -, -, -, hsncT, hinv⟩ := hgood
  have hLcl : IsClosed (oneLocus (floorRDivisor B)) := by
    rw [oneLocus_floorRDivisor]
    exact MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isClosed_iUnion_support _
  haveI : AlgebraicGeometry.IsNoetherian W := ⟨⟩
  have hEWT : (EW.support : Set W) ⊆ p.base ⁻¹' oneLocus (floorRDivisor B) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    refine closure_minimal (Set.singleton_subset_iff.mpr ?_) (hLcl.preimage p.continuous)
    rw [Set.mem_preimage]
    change p (MMP.Mori.PrimeDivisor.genericPoint EW) ∈ _
    rw [hpη]; exact hξL
  have hEWst : IsComponentStratum (p.base ⁻¹' oneLocus (floorRDivisor B))
      (EW.support : Set W) := by
    refine ⟨{(EW.support : Set W)}, Set.singleton_subset_iff.mpr
      (support_mem_componentsOf_of_isSNCClosedSubset hsncT hEWT), ?_⟩
    rw [Set.sInter_singleton]
    refine ⟨⟨MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isIrreducible_support EW, subset_rfl⟩,
      fun V hV _ => hV.2⟩
  obtain ⟨f, hf, hfst, hfq, hfb⟩ :=
    hinv _ hEWst (MMP.Positivity.PrimeDivisor.genericPoint_mem_support' EW)
  have hsuppL : ((floorRDivisor B).supp : Set X) ⊆ oneLocus (floorRDivisor B) := by
    intro x hx
    obtain ⟨G, hG0, hxG⟩ := DivisorWithCoeffs.mem_supp_iff.mp hx
    rw [coeff_floorRDivisor] at hG0
    refine ⟨G, ?_, hxG⟩
    rw [coeff_floorRDivisor]
    split_ifs at hG0 ⊢ with h
    · rfl
    · exact absurd rfl hG0
  have hsncL : MMP.Resolution.IsSNCClosedSubset sX (oneLocus (floorRDivisor B)) := by
    rw [oneLocus_floorRDivisor]
    exact MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isSNCClosedSubset_of_isSNC sX hsnc1
  exact ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, p, hN, hb, EW, hproj, hsm,
    hval, hexc, hsncS _ hsuppL hsncL, f, hf, hfst, hfq, hfb⟩

section LogResolution

open TopologicalSpace

/-! ### Log resolutions principalizing an ideal -/

/-- The union of two closed subsets of pure codimension one is of pure codimension one. -/
private theorem isPureCodimOne_sup {T : Type*} [TopologicalSpace T] {A B : Closeds T}
    (hA : IsPureCodimOne A) (hB : IsPureCodimOne B) : IsPureCodimOne (A ⊔ B) := by
  intro W hW
  have hsub : (W : Set T) ⊆ (A : Set T) ∪ B := hW.1
  rcases (isPreirreducible_iff_isClosed_union_isClosed.mp W.isIrreducible.isPreirreducible)
    _ _ A.isClosed B.isClosed hsub with h | h
  · exact hA W ⟨h, fun W' hW' hle ↦ hW.2 (hW'.trans Set.subset_union_left) hle⟩
  · exact hB W ⟨h, fun W' hW' hle ↦ hW.2 (hW'.trans Set.subset_union_right) hle⟩

/-- The support of an effective Cartier divisor on a scheme locally of finite type over a field
is of pure codimension one. -/
private theorem isPureCodimOne_support_of_isEffectiveCartierDivisor {k : Type} [Field k]
    {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] {D : Y.IdealSheafData}
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) : IsPureCodimOne D.support := by
  letI : Y.Over (Spec (.of k)) := ⟨sY⟩
  haveI : LocallyOfFiniteType (Y ↘ Spec (.of k)) := ‹LocallyOfFiniteType sY›
  intro W hW
  set e := irreducibleSetEquivPoints (α := Y)
  have hWη : (W : Set Y) = closure {e W} := by
    conv_lhs => rw [← e.symm_apply_apply W]
    rfl
  have hηW : e W ∈ (W : Set Y) := by rw [hWη]; exact subset_closure rfl
  have h1 : codimension W = Order.coheight (e W) := by
    change Order.coheight W = _
    rw [← Order.coheight_orderIso e W]
  rw [h1]
  refine MMP.coheight_eq_one_of_isEffectiveCartierDivisor k hD (hW.1 hηW)
    fun y hy hyη => ?_
  have hle : W ≤ e.symm y := by
    rw [← e.le_iff_le, e.apply_symm_apply, Scheme.le_iff_specializes]
    exact hyη
  have hsub : ((e.symm y : IrreducibleCloseds Y) : Set Y) ⊆ D.support := by
    change closure {y} ⊆ _
    exact closure_minimal (Set.singleton_subset_iff.mpr hy) D.support.isClosed
  have heq : e.symm y = W := le_antisymm (hW.2 hsub hle) hle
  rw [← heq, e.apply_symm_apply]

/-- The preimage in a subspace `C` of a preirreducible subset of `C` is preirreducible. -/
private theorem isPreirreducible_preimage_val {Y : Type*} [TopologicalSpace Y] {C W : Set Y}
    (hW : IsPreirreducible W) (hWC : W ⊆ C) : IsPreirreducible (Subtype.val ⁻¹' W : Set C) := by
  rintro u v hu hv ⟨a, ha, hau⟩ ⟨b, hb, hbv⟩
  obtain ⟨u', hu', rfl⟩ := isOpen_induced_iff.mp hu
  obtain ⟨v', hv', rfl⟩ := isOpen_induced_iff.mp hv
  obtain ⟨y, hyW, hyu, hyv⟩ := hW u' v' hu' hv' ⟨a, ha, hau⟩ ⟨b, hb, hbv⟩
  exact ⟨⟨y, hWC hyW⟩, hyW, hyu, hyv⟩

/-- An irreducible closed set contained in a closed set lies in an irreducible closed subset
maximal in it. -/
private theorem exists_maximal_ge {Y : Type*} [TopologicalSpace Y] {C : Set Y} (hC : IsClosed C)
    (Z : IrreducibleCloseds Y) (hZ : (Z : Set Y) ⊆ C) :
    ∃ W : IrreducibleCloseds Y, Maximal (fun W' : IrreducibleCloseds Y ↦ (W' : Set Y) ⊆ C) W ∧
      Z ≤ W := by
  obtain ⟨t, ht, hxt, hmax⟩ := exists_preirreducible (Subtype.val ⁻¹' (Z : Set Y) : Set C)
    (isPreirreducible_preimage_val Z.isIrreducible.isPreirreducible hZ)
  obtain ⟨z, hz⟩ := Z.isIrreducible.nonempty
  let W : IrreducibleCloseds Y := ⟨closure (Subtype.val '' t),
    (IsIrreducible.closure ⟨⟨z, ⟨z, hZ hz⟩, hxt hz, rfl⟩,
      ht.image _ continuous_subtype_val.continuousOn⟩), isClosed_closure⟩
  have hWC : (W : Set Y) ⊆ C := closure_minimal (by rintro _ ⟨y, -, rfl⟩; exact y.2) hC
  refine ⟨W, ⟨hWC, fun W' hW'C hWW' y hy ↦ ?_⟩, fun y hy ↦ subset_closure ⟨⟨y, hZ hy⟩, hxt hy, rfl⟩⟩
  have := hmax _ (isPreirreducible_preimage_val W'.isIrreducible.isPreirreducible hW'C)
    fun y hy ↦ hWW' (subset_closure ⟨y, hy, rfl⟩)
  have : (⟨y, hW'C hy⟩ : C) ∈ t := by rw [← this]; exact hy
  exact subset_closure ⟨_, this, rfl⟩

/-- The support of a prime divisor, as an irreducible closed subset. -/
private noncomputable def primeIrr {X : Scheme.{0}} (E : AlgebraicGeometry.PrimeDivisor X) :
    IrreducibleCloseds X :=
  IrreducibleCloseds.closureSingleton E.genericPoint

private theorem coe_primeIrr {X : Scheme.{0}} (E : AlgebraicGeometry.PrimeDivisor X) :
    (primeIrr E : Set X) = E.support := by
  rw [E.support_eq_closure]; rfl

private theorem codimension_primeIrr {X : Scheme.{0}} (E : AlgebraicGeometry.PrimeDivisor X) :
    codimension (primeIrr E) = 1 := E.codimension_one

private theorem exists_mem_of_subset_iUnion {X : Scheme.{0}}
    {s : Finset (AlgebraicGeometry.PrimeDivisor X)}
    (W : IrreducibleCloseds X) (hW : (W : Set X) ⊆ ⋃ E ∈ s, E.support) :
    ∃ E ∈ s, W ≤ primeIrr E := by
  classical
  obtain ⟨z, hz, hWz⟩ := (isIrreducible_iff_sUnion_isClosed.mp W.isIrreducible)
    (s.image AlgebraicGeometry.PrimeDivisor.support)
    (by
      intro z hz
      obtain ⟨E, -, rfl⟩ := Finset.mem_image.mp hz
      rw [← coe_primeIrr]; exact (primeIrr E).isClosed)
    (by
      intro x hx
      obtain ⟨E, hE, hxE⟩ := Set.mem_iUnion₂.mp (hW hx)
      exact ⟨E.support, Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hE), hxE⟩)
  obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hz
  exact ⟨E, hE, fun x hx ↦ by
    change x ∈ (primeIrr E : Set X); rw [coe_primeIrr]; exact hWz hx⟩

/-- A closed subset of pure codimension one of an snc divisor is an snc divisor. -/
private theorem isSNCSubset_of_le {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {S C : Closeds X}
    (hS : IsSNCSubset sX S) (hC : IsPureCodimOne C) (hCS : C ≤ S) : IsSNCSubset sX C := by
  classical
  rcases hS with rfl | ⟨s, hs, hsnc⟩
  · exact Or.inl (le_bot_iff.mp hCS)
  right
  refine ⟨s.filter (fun E ↦ E.support ⊆ C), ?_, ?_⟩
  · apply subset_antisymm
    · intro x hx
      obtain ⟨E, hE, hxE⟩ := Set.mem_iUnion₂.mp hx
      exact (Finset.mem_filter.mp hE).2 hxE
    · intro x hx
      obtain ⟨W, hW, hxW⟩ := exists_maximal_ge C.isClosed
        (IrreducibleCloseds.closureSingleton x) (by
          change closure {x} ⊆ (C : Set X)
          exact closure_minimal (by simpa using hx) C.isClosed)
      have hxW' : x ∈ (W : Set X) := hxW (subset_closure rfl)
      obtain ⟨E, hE, hWE⟩ := exists_mem_of_subset_iUnion W (hs ▸ hW.1.trans hCS)
      have hWE' : W = primeIrr E := by
        by_contra hne
        have hlt : W < primeIrr E := lt_of_le_of_ne hWE hne
        have := Order.coheight_add_one_le hlt
        rw [← codimension_eq_coheight, ← codimension_eq_coheight, codimension_primeIrr,
          hC W hW] at this
        exact absurd this (by decide)
      refine Set.mem_iUnion₂.mpr ⟨E, Finset.mem_filter.mpr ⟨hE, ?_⟩, ?_⟩
      · rw [← coe_primeIrr, ← hWE']; exact hW.1
      · rw [← coe_primeIrr, ← hWE']; exact hxW'
  · refine hsnc.of_support_subset ?_
    intro E hE
    rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply] at hE ⊢
    simp only [Finsupp.single_apply] at hE ⊢
    rw [Finset.sum_ite_eq'] at hE ⊢
    split_ifs at hE with h1
    · rw [if_pos (Finset.mem_filter.mp h1).1]; exact one_ne_zero
    · exact absurd rfl hE

/-- **A log resolution principalizing an ideal.** For a variety `X` over a field of
characteristic zero, an `ℝ`-divisor `D` and a nonzero ideal sheaf `J`, there is a projective log
resolution `f : Y ⟶ X` of `(X, D)` on which `J 𝒪_Y` is invertible. -/
private theorem exists_isLogResolution_isEffectiveCartierDivisor_comap {k : Type} [Field k]
    [CharZero k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) (hX : AlgebraicGeometry.IsVariety k sX)
    (D : RDivisor X) (J : X.IdealSheafData) (hJ : J ≠ ⊥) :
    ∃ (Y : Scheme.{0}) (f : Y ⟶ X), AlgebraicGeometry.IsVariety k (f ≫ sX) ∧ IsProjective f ∧
      MMP.Mori.IsLogResolution sX D f ∧ Stacks.Divisors.IsEffectiveCartierDivisor (J.comap f) := by
  haveI : IsIntegral X := hX.toIsIntegral
  set IS := Scheme.IdealSheafData.vanishingIdeal D.supp
  have hsupp : (J * IS).support = J.support ⊔ D.supp := by
    rw [Scheme.IdealSheafData.support_mul]; rfl
  have hI : J * IS ≠ ⊥ := by
    intro h
    have hξ : genericPoint X ∈ (J * IS).support := by
      rw [h, Scheme.IdealSheafData.support_bot]; trivial
    rw [hsupp] at hξ
    rcases hξ with h1 | h2
    · exact genericPoint_notMem_supportSet J hJ (by simpa using h1)
    · exact genericPoint_notMem_supp D h2
  obtain ⟨Y, f, hYv, hproj, hbir, hsm, -, hcart, hsnc, hpure⟩ :=
    MMP.Resolution.exists_isResolutionOfVariety_isEffectiveCartierDivisor_comap sX hX (J * IS) hI
  rw [Stacks.IdealSheaf.comap_mul] at hcart
  haveI : LocallyOfFiniteType (f ≫ sX) := hYv.toLocallyOfFiniteType
  have hSp : IsPureCodimOne (D.supp.preimage f.continuous) := by
    have := isPureCodimOne_support_of_isEffectiveCartierDivisor (f ≫ sX)
      (isEffectiveCartierDivisor_right_of_mul _ _ hcart)
    rwa [Scheme.IdealSheafData.support_comap] at this
  have hsupY : ((J * IS).comap f).support =
      J.support.preimage f.continuous ⊔ D.supp.preimage f.continuous := by
    rw [Scheme.IdealSheafData.support_comap, hsupp]; rfl
  rw [hsupY] at hsnc
  refine ⟨Y, f, hYv, hproj, ⟨⟨hproj.isProper, hbir, hsm⟩, hpure, ?_⟩,
    isEffectiveCartierDivisor_left_of_mul _ _ hcart⟩
  exact isSNCSubset_of_le hsnc (isPureCodimOne_sup hpure hSp)
    (sup_le_sup_left le_sup_right _)

/-! ### The crepant boundary on a log resolution -/

/-- **The crepant boundary of an snc subboundary on a log resolution is an snc subboundary.** -/
private theorem exists_isSNCSubboundaryPair_isCrepantBoundary {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} (hB : IsSNCSubboundaryPair sX B)
    {n : ℕ} {KX : Divisor X} (hKX : KX.IsCanonicalDivisor sX n) {Y : Scheme.{0}} (f : Y ⟶ X)
    (hYv : AlgebraicGeometry.IsVariety k (f ≫ sX)) (hproj : IsProjective f)
    {B₀ : QDivisor X} (hBB₀ : (QDivisor.toRDivisor B).supp ≤ (QDivisor.toRDivisor B₀).supp)
    (hlog : MMP.Mori.IsLogResolution sX (QDivisor.toRDivisor B₀) f) :
    ∃ B' : QDivisor Y, IsSNCSubboundaryPair (f ≫ sX) B' ∧
      ∀ (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f),
        IsCrepantBoundary sX n KX B f hY hf B' := by
  classical
  have hX : IsNormalVariety k sX := ⟨hB.isProjectiveVariety.toIsVariety, inferInstance⟩
  have hres : IsSmoothResolution sX f := hlog.toIsSmoothResolution
  obtain ⟨hY, -, -⟩ := hres.isNormalVariety hX
  have hf := hres.isBirationalMorphism
  have hqc := isQCartier_of_isSmoothScheme hB.isSmoothScheme (Divisor.toQDivisor KX + B)
  have hP : MMP.Mori.IsPair sX B := ⟨hX, n, KX, hKX, hqc⟩
  have hPw : IsPairWith sX n KX B := ⟨hX, hKX, hqc⟩
  obtain ⟨⟨B', hB'c, -⟩, -⟩ := IsPair.existsUnique_isCrepantBoundary hP hKX f hY hf
  -- a non-exceptional prime divisor of `Y` is the transform of a prime divisor of `X`
  have hnex : ∀ G : MMP.Mori.PrimeDivisor Y,
      ¬ (⟨Y, f, hY, hf, G⟩ : DivisorOver k sX).IsExceptional →
        ∃ P : MMP.Mori.PrimeDivisor X, B'.coeff G = B.coeff P ∧
          f G.genericPoint = P.genericPoint := by
    intro G hG
    obtain ⟨P, hc, hd⟩ := DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff hPw _ hG
    have hη : f G.genericPoint = P.genericPoint := by
      refine (inseparable_iff_closure_eq.2 ?_).eq
      rw [← DivisorOver.center_eq_closure_genericPoint (⟨Y, f, hY, hf, G⟩ : DivisorOver k sX),
        hc, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact ⟨P, neg_injective ((hB'c G).eq hd), hη⟩
  -- the support of `B'` lies in `Ex(f) ∪ f⁻¹(Supp B)`
  have hsupp : ∀ G ∈ B'.support, G.genericPoint ∈
      (exceptionalSet f ⊔ (QDivisor.toRDivisor B₀).supp.preimage f.continuous : Closeds Y) := by
    intro G hG
    by_cases hGe : (⟨Y, f, hY, hf, G⟩ : DivisorOver k sX).IsExceptional
    · exact Or.inl (MMP.Positivity.support_subset_exceptionalSet G hGe
        (MMP.Flips.primeDivisor_genericPoint_mem_support G))
    · obtain ⟨P, hc, hη⟩ := hnex G hGe
      refine Or.inr (hBB₀ ?_)
      change f G.genericPoint ∈ (QDivisor.toRDivisor B).supp
      rw [hη, DivisorWithCoeffs.mem_supp_iff]
      refine ⟨P, ?_, MMP.Flips.primeDivisor_genericPoint_mem_support P⟩
      rw [QDivisor.coeff_toRDivisor, ← hc]
      have : B'.coeff G ≠ 0 := by
        rwa [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply] at hG
      exact_mod_cast this
  have hsncB := isSNC_sum_single hB.isSNC subset_rfl
  refine ⟨B', ⟨?_, hres.isSmoothScheme, ?_, fun G => ?_⟩, fun _ _ => hB'c⟩
  · exact (MMP.Mori.isProjectiveVariety_iff k (f ≫ sX)).2 ⟨hYv,
      isProjectiveMorphism_of_isProjective_of_isAffine (f ≫ sX)
        (hproj.comp hB.isProjectiveVariety.isProjective.isProjective)⟩
  · rcases hlog.isSNCSubset with hbot | ⟨S, hS, hsncS⟩
    · haveI : LocallyOfFinitePresentation (f ≫ sX) := by
        haveI := (MMP.Mori.isSmoothScheme_iff _).1 hres.isSmoothScheme
        infer_instance
      refine (DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme (R := ℤ) (f ≫ sX)
        hres.isSmoothScheme).of_support_subset fun G hG => ?_
      have := hsupp G hG
      rw [hbot, ← SetLike.mem_coe, TopologicalSpace.Closeds.coe_bot] at this
      exact absurd this (Set.notMem_empty _)
    · refine hsncS.of_support_subset fun G hG => (mem_support_sum_single S G).2 ?_
      have h := hsupp G hG
      rw [← SetLike.mem_coe, ← hS] at h
      obtain ⟨E, hE, hGE⟩ := Set.mem_iUnion₂.mp h
      rwa [MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hGE] at hE
  · by_cases hGe : (⟨Y, f, hY, hf, G⟩ : DivisorOver k sX).IsExceptional
    · obtain ⟨c, T, -, -, -, hTc, hTS, -, hle⟩ := le_isDiscrepancy_of_isSNC hX hB.isSmoothScheme hKX
        subset_rfl hsncB (fun E _ => hB.coeff_le_one E) _ hGe (hB'c G)
      have h1 : 0 ≤ ∑ E ∈ T, (1 - B.coeff E) :=
        Finset.sum_nonneg fun E _ => sub_nonneg.2 (hB.coeff_le_one E)
      have h2 : (0 : ℚ) ≤ (c : ℚ) - T.card := sub_nonneg.2 (by exact_mod_cast hTc)
      linarith
    · obtain ⟨P, hc, -⟩ := hnex G hGe
      rw [hc]
      exact hB.coeff_le_one P

end LogResolution

/-- **Crepant boundaries compose.** If `(Y, Δ_Y)` and `(Y', Δ_{Y'})` are both crepant over
`(X, Δ)`, through `f` and `g ≫ f`, then `(Y', Δ_{Y'})` is crepant over `(Y, Δ_Y)` through `g`. -/
private theorem isCrepantBoundary_of_comp {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X Y Y' : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y']
    [IsLocallyNoetherian Y'] [IsNormal Y'] {Δ : QDivisor X} (hP : MMP.Mori.IsPair sX Δ) {n : ℕ}
    {KX : Divisor X} (hKX : KX.IsCanonicalDivisor sX n) (f : Y ⟶ X)
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) {KY : Divisor Y}
    (hKY : KY.IsCanonicalDivisor (f ≫ sX) n) {ΔY : QDivisor Y}
    (hcrep : IsCrepantBoundary sX n KX Δ f hY hf ΔY) (g : Y' ⟶ Y)
    (hY' : IsNormalVariety k (g ≫ f ≫ sX)) (hg : IsBirationalMorphism g)
    (hY'X : IsNormalVariety k ((g ≫ f) ≫ sX)) (hgf : IsBirationalMorphism (g ≫ f))
    {ΔY' : QDivisor Y'} (hcrep' : IsCrepantBoundary sX n KX Δ (g ≫ f) hY'X hgf ΔY') :
    IsCrepantBoundary (f ≫ sX) n KY ΔY g hY' hg ΔY' := by
  intro H
  have h1 := hcrep' H
  exact ((MMP.Mori.IsPair.isDiscrepancy_iff_of_crepant hP f hY hf hKX hKY (Or.inl hcrep)).2
    ⟨Y', g, hY', hg, H⟩ ⟨Y', g ≫ f, hY'X, hgf, H⟩
    (valuation_compDivisorOver f hY hf ⟨Y', g, hY', hg, H⟩) _).mpr h1

private theorem withBot_add_two_le_iff' {d : WithBot ℕ∞} {c : ℕ∞} {n : ℕ} (h : d + c = n) :
    d + 2 ≤ n ↔ 2 ≤ c := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe d =>
    induction d using ENat.recTopCoe with
    | top =>
      exfalso
      have : ((⊤ : ℕ∞) : WithBot ℕ∞) + c = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
        rw [← WithBot.coe_add, top_add]
      rw [this] at h
      exact ENat.top_ne_natCast n (WithBot.coe_injective h)
    | coe d =>
      induction c using ENat.recTopCoe with
      | top =>
        exfalso
        have : ((d : ℕ∞) : WithBot ℕ∞) + ((⊤ : ℕ∞) : WithBot ℕ∞) = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
          rw [← WithBot.coe_add, add_top]
        rw [this] at h
        exact ENat.top_ne_natCast n (WithBot.coe_injective h)
      | coe c =>
        have h' : d + c = n := by exact_mod_cast h
        have e1 : (((d : ℕ∞) : WithBot ℕ∞) + 2 ≤ (n : WithBot ℕ∞)) ↔ d + 2 ≤ n := by
          rw [show ((d : ℕ∞) : WithBot ℕ∞) + 2 = (((d + 2 : ℕ) : ℕ∞) : WithBot ℕ∞) from rfl,
            show (n : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) from rfl, WithBot.coe_le_coe,
            Nat.cast_le]
        rw [e1]
        constructor
        · intro h2; exact_mod_cast (show 2 ≤ c by omega)
        · intro h2; have : 2 ≤ c := by exact_mod_cast h2
          omega

/-- A proper divisor over `X` is exceptional exactly when its centre has codimension at least
two. -/
private theorem properDivisorOver_isExceptional_iff' {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX] {n : ℕ}
    (hn : topologicalKrullDim X = n) (D : MMP.Flips.ProperDivisorOver k sX) :
    D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  unfold MMP.Flips.ProperDivisorOver.IsExceptional
  rw [D.center_eq_toDivisorOver_center, D.toDivisorOver.center_eq_closure_genericPoint, hn]
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX (D.f D.E.genericPoint)
  rw [hn] at h
  exact withBot_add_two_le_iff' h

/-- **A common log resolution.** For two projective birational models `h : Y ⟶ X` and
`p : X̃ ⟶ X` of a smooth projective variety `X` with an snc divisor `B`, a log resolution
`q : Y⁺ ⟶ X` of `(X, B)` principalizing the two ideals presenting `Y` and `X̃` as blow-ups of `X`
factors through both. -/
private theorem exists_isLogResolution_factors {k : Type} [Field k] [CharZero k]
    {X Y X' : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral Y] [IsIntegral X']
    (hX : MMP.Mori.IsProjectiveVariety k sX) (D : RDivisor X) (h : Y ⟶ X)
    (hproj : IsProjectiveMorphism h) (hbir : IsBirationalMorphism h) (p : X' ⟶ X)
    (hpproj : IsProjectiveMorphism p) (hpbir : IsBirationalMorphism p) :
    ∃ (Y' : Scheme.{0}) (q : Y' ⟶ X) (fP : Y' ⟶ Y) (gP : Y' ⟶ X'),
      AlgebraicGeometry.IsVariety k (q ≫ sX) ∧ IsProjective q ∧ MMP.Mori.IsLogResolution sX D q ∧
      fP ≫ h = q ∧ gP ≫ p = q := by
  haveI hXv : AlgebraicGeometry.IsVariety k sX := hX.toIsVariety
  haveI : IsQuasiProjectiveVariety k sX := by
    rw [isQuasiProjectiveVariety_iff_isHQuasiProjective]
    refine ⟨hXv, ?_⟩
    obtain ⟨N, ιV, hιV, hιVs⟩ := hX.isProjective
    exact ⟨N, ιV, inferInstance, inferInstance, hιVs⟩
  obtain ⟨J₁, hJ₁0, -, e₁, he₁⟩ := MMP.exists_blowUp_iso_of_isProjective_of_isBirational sX h
    hproj.isProjective (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hbir)
  obtain ⟨J₂, hJ₂0, -, e₂, he₂⟩ := MMP.exists_blowUp_iso_of_isProjective_of_isBirational sX p
    hpproj.isProjective (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hpbir)
  have hJ : J₁ * J₂ ≠ ⊥ := by
    intro h0
    have hξ : genericPoint X ∈ (J₁ * J₂).support := by
      rw [h0, Scheme.IdealSheafData.support_bot]; trivial
    rw [Scheme.IdealSheafData.support_mul] at hξ
    rcases hξ with h1 | h2
    · exact genericPoint_notMem_supportSet J₁ hJ₁0 (by simpa using h1)
    · exact genericPoint_notMem_supportSet J₂ hJ₂0 (by simpa using h2)
  obtain ⟨Y', q, hYv, hqproj, hlog, hcart⟩ :=
    exists_isLogResolution_isEffectiveCartierDivisor_comap sX hXv D (J₁ * J₂) hJ
  rw [Stacks.IdealSheaf.comap_mul] at hcart
  have h₁ := isEffectiveCartierDivisor_left_of_mul _ _ hcart
  have h₂ := isEffectiveCartierDivisor_right_of_mul _ _ hcart
  refine ⟨Y', q, blowUpLift J₁ q h₁ ≫ e₁.inv, blowUpLift J₂ q h₂ ≫ e₂.inv, hYv, hqproj, hlog,
    ?_, ?_⟩
  · rw [Category.assoc, ← he₁, Iso.inv_hom_id_assoc, blowUpLift_comp]
  · rw [Category.assoc, ← he₂, Iso.inv_hom_id_assoc, blowUpLift_comp]

open scoped Classical in
/-- **The reduced boundary of the tower model is crepant over the floor part.** On a smooth
projective model `p : X̃ ⟶ X` on which `p⁻¹ (B^{=1})` is snc and every `p`-exceptional prime has
log discrepancy zero over `B^{=1}`, the reduced divisor of `p⁻¹ (B^{=1})` is an snc subboundary
crepant over `(X, B^{=1})`: exceptional primes have discrepancy `-1` and lie over floor strata,
and a non-exceptional prime has the coefficient of its image. -/
private theorem isCrepantBoundary_reducedDivisorOfSet_of_tower {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {B : QDivisor X} (hB : IsSNCSubboundaryPair sX B)
    {n : ℕ} {KX : Divisor X} (hKX : KX.IsCanonicalDivisor sX n) {W : Scheme.{0}}
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] (p : W ⟶ X)
    (hN : IsNormalVariety k (p ≫ sX)) (hb : IsBirationalMorphism p)
    (hexc : ∀ F : MMP.Mori.PrimeDivisor W,
      MMP.Mori.RationalMap.IsExceptional (X := W) p.toRationalMap F →
      MMP.Intersection.IsLogDiscrepancy sX n (floorRDivisor B) ⟨W, p, hN, hb, F⟩ 0)
    (hsnc : MMP.Resolution.IsSNCClosedSubset (p ≫ sX)
      (p.base ⁻¹' oneLocus (floorRDivisor B)))
    (hTf : {P : MMP.Mori.PrimeDivisor W |
      (P.support : Set W) ⊆ p.base ⁻¹' oneLocus (floorRDivisor B)}.Finite) :
    IsCrepantBoundary sX n KX (Divisor.toQDivisor (coeffOnePart B)) p hN hb
      (reducedDivisorOfSet _ hTf) := by
  have hX : IsNormalVariety k sX := ⟨hB.isProjectiveVariety.toIsVariety, inferInstance⟩
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hX.1.toQuasiCompact
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  set Q₁ := Divisor.toQDivisor (coeffOnePart B) with hQ₁
  have hQ₁c : ∀ G, Q₁.coeff G = if B.coeff G = 1 then 1 else 0 := fun G => by
    rw [hQ₁, Divisor.coeff_toQDivisor, coeff_coeffOnePart]; split_ifs <;> simp
  have hQ₁B : (coeffOnePart Q₁).support = (coeffOnePart B).support := by
    ext G
    constructor
    · intro hG
      have := coeff_eq_one_of_mem_support_coeffOnePart hG
      rw [hQ₁c] at this
      split_ifs at this with h
      · exact mem_support_coeffOnePart h
      · exact absurd this (by norm_num)
    · intro hG
      exact mem_support_coeffOnePart (by
        rw [hQ₁c, if_pos (coeff_eq_one_of_mem_support_coeffOnePart hG)])
  have hBQ : IsSNCSubboundaryPair sX Q₁ := by
    refine ⟨hB.isProjectiveVariety, hB.isSmoothScheme, hB.isSNC.of_support_subset fun G hG => ?_,
      fun G => by rw [hQ₁c]; split_ifs <;> norm_num⟩
    rw [Finsupp.mem_support_iff] at hG ⊢
    intro h0
    apply hG
    change Q₁.coeff G = 0
    rw [hQ₁c, if_neg]
    intro h1
    change B.coeff G = 0 at h0
    rw [h0] at h1
    norm_num at h1
  have hPQ : MMP.Mori.IsPair sX Q₁ :=
    ⟨hX, n, KX, hKX, isQCartier_of_isSmoothScheme hB.isSmoothScheme _⟩
  have hL : oneLocus (floorRDivisor B) =
      ⋃ G ∈ (coeffOnePart B).support, (G.support : Set X) := oneLocus_floorRDivisor B
  intro G
  set Dov : DivisorOver k sX := ⟨W, p, hN, hb, G⟩ with hDov
  rw [coeff_reducedDivisorOfSet]
  by_cases hex : Dov.IsExceptional
  · have hlog := hexc G hex
    obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPQ hKX Dov
    have ha1 : a = -1 := by
      have := ((MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy ha 0).mp hlog).2
      have : (a : ℝ) = -1 := by linarith
      exact_mod_cast this
    rw [ha1] at ha
    have hst := isSNCStratum_closure_of_isDiscrepancy_eq_neg_one hBQ hKX Dov ha
    have hsub : (G.support : Set W) ⊆ p.base ⁻¹' oneLocus (floorRDivisor B) := by
      obtain ⟨J, hJ, hmax⟩ := hst
      have hJne : J.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        rintro rfl
        have hu : closure {Dov.f Dov.E.genericPoint} = Set.univ :=
          (hmax.eq_of_ge ⟨IrreducibleSpace.isIrreducible_univ X, by simp⟩
            (Set.subset_univ _)).symm
        have h2 := (isExceptional_iff_two_le_coheight hX Dov).mp hex
        have hgp : Dov.f Dov.E.genericPoint = genericPoint X :=
          (show IsGenericPoint _ Set.univ by rw [← hu]; exact isGenericPoint_closure).eq
            (genericPoint_spec X)
        rw [hgp, Order.coheight_eq_zero.mpr fun b _ =>
          Scheme.le_iff_specializes.mpr (genericPoint_specializes b)] at h2
        exact absurd h2 (by decide)
      obtain ⟨G', hG'⟩ := hJne
      have hG'B : G' ∈ (coeffOnePart B).support := hQ₁B ▸ hJ hG'
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      refine closure_minimal (Set.singleton_subset_iff.mpr ?_)
        (hsnc.1)
      rw [Set.mem_preimage]
      show p (MMP.Mori.PrimeDivisor.genericPoint G) ∈ oneLocus (floorRDivisor B)
      rw [hL]
      exact Set.mem_biUnion hG'B (hmax.1.2.trans (Set.biInter_subset_of_mem hG')
        (subset_closure rfl))
    rw [if_pos hsub]
    exact ha
  · obtain ⟨P, hcen, hP⟩ := MMP.Mori.DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff
      ⟨hX, hKX, isQCartier_of_isSmoothScheme hB.isSmoothScheme _⟩ Dov hex
    have hcl : closure {p G.genericPoint} = (P.support : Set X) := by
      rw [← hcen, MMP.Positivity.DivisorOver.center_eq_closureSingleton]
      rfl
    have hLcl : IsClosed (oneLocus (floorRDivisor B)) := by
      rw [hL]; exact MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isClosed_iUnion_support _
    have hiff : (G.support : Set W) ⊆ p.base ⁻¹' oneLocus (floorRDivisor B) ↔
        B.coeff P = 1 := by
      constructor
      · intro h
        have hPL : (P.support : Set X) ⊆ oneLocus (floorRDivisor B) := by
          rw [← hcl]
          exact closure_minimal (Set.singleton_subset_iff.mpr
            (h (MMP.Positivity.PrimeDivisor.genericPoint_mem_support' G))) hLcl
        have hη := hPL (MMP.Positivity.PrimeDivisor.genericPoint_mem_support' P)
        rw [genericPoint_mem_oneLocus_iff, coeff_floorRDivisor] at hη
        split_ifs at hη with h1
        · exact h1
        · norm_num at hη
      · intro h1
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        refine closure_minimal (Set.singleton_subset_iff.mpr ?_) (hLcl.preimage p.continuous)
        rw [Set.mem_preimage]
        show p (MMP.Mori.PrimeDivisor.genericPoint G) ∈ oneLocus (floorRDivisor B)
        have : p G.genericPoint ∈ (P.support : Set X) := hcl ▸ subset_closure rfl
        exact ⟨P, by rw [coeff_floorRDivisor, if_pos h1], this⟩
    by_cases h1 : B.coeff P = 1
    · rw [if_pos (hiff.mpr h1)]
      have := hP
      rw [hQ₁c, if_pos h1] at this
      exact this
    · rw [if_neg (fun h => h1 (hiff.mp h))]
      have := hP
      rw [hQ₁c, if_neg h1] at this
      simpa using this

/-- If `g ≫ h` is dominant and `h` is proper birational onto a normal integral scheme, then `g`
sends the generic point to the generic point. -/
private lemma map_genericPoint_eq_of_comp {A B C : Scheme.{0}} [IsIntegral A] [IsIntegral B]
    [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C] (g : A ⟶ B) (h : B ⟶ C) [IsProper h]
    (hh : IsBirationalMorphism h) [IsDominant (g ≫ h)] : g (genericPoint A) = genericPoint B := by
  haveI : IsDominant h := hh.isDominant
  have hη : (g ≫ h) (genericPoint A) = genericPoint C := map_genericPoint_of_isDominant _
  have hηB : h (genericPoint B) = genericPoint C := map_genericPoint_of_isDominant h
  have hreg := MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal h hh
    (y := genericPoint C) (by
      rw [Order.coheight_eq_zero.mpr fun b _ =>
        Scheme.le_iff_specializes.mpr (genericPoint_specializes b)]
      exact zero_le_one)
  have h1 : h (g (genericPoint A)) = h (genericPoint B) := by
    rw [← Scheme.Hom.comp_apply, hη, hηB]
  have ha : h (g (genericPoint A)) ∈ MMP.Mori.biregularLocus h := by
    rw [← Scheme.Hom.comp_apply, hη]; exact hreg
  have hb : h (genericPoint B) ∈ MMP.Mori.biregularLocus h := by rw [hηB]; exact hreg
  exact (MMP.Threefold.Resolution.specializes_of_mem_biregularLocus h ha hb (h1 ▸ specializes_rfl)
    |>.antisymm (MMP.Threefold.Resolution.specializes_of_mem_biregularLocus h hb ha
      (h1 ▸ specializes_rfl))).eq

/-- The first factor of a birational composite with a birational second factor is birational. -/
private lemma isBirationalMorphism_of_comp_of_isBirationalMorphism {A B C : Scheme.{0}}
    [IsIntegral A] [IsIntegral B] [IsIntegral C] (g : A ⟶ B) (h : B ⟶ C) [LocallyOfFiniteType g]
    [IsDominant g] (hh : IsBirationalMorphism h) (hgh : IsBirationalMorphism (g ≫ h)) :
    IsBirationalMorphism g := by
  haveI : IsDominant h := hh.isDominant
  haveI : IsDominant (g ≫ h) := hgh.isDominant
  have hbij : Function.Bijective (functionFieldMap g) := by
    have h1 := hgh.functionFieldMap_bijective
    have h2 := hh.functionFieldMap_bijective
    have heq : (⇑(functionFieldMap g) ∘ ⇑(functionFieldMap h)) = ⇑(functionFieldMap (g ≫ h)) :=
      funext fun t => MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply g h t
    rw [← heq] at h1
    exact (Function.Bijective.of_comp_iff _ h2).mp h1
  let e := B.presheaf.stalkCongr (Inseparable.of_eq (map_genericPoint_of_isDominant g).symm)
  haveI : IsIso (e.hom ≫ g.stalkMap (genericPoint A)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  haveI : IsIso (g.stalkMap (genericPoint A)) := IsIso.of_isIso_comp_left e.hom _
  have hbir : AlgebraicGeometry.IsBirational g := by
    simp only [AlgebraicGeometry.isBirational_iff, genericPoints_eq_singleton, Set.bijOn_singleton,
      Set.mem_singleton_iff, forall_eq]
    exact ⟨map_genericPoint_of_isDominant g, inferInstance⟩
  haveI : Finite (irreducibleComponents A) := by
    rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
  haveI : Finite (irreducibleComponents B) := by
    rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
  obtain ⟨U, V, hUV, hU, hV, hiso⟩ :=
    exists_dense_opens_isIso_resLE_of_isBirational g hbir (Or.inl ⟨inferInstance, inferInstance⟩)
  exact MMP.Flips.isBirationalMorphism_of_isIso_resLE g U V hU.nonempty hV.nonempty hUV hiso

/-- Two divisors over `X` related by a birational morphism of their models over `X` matching the
generic points of the prime divisors have the same valuation. -/
private theorem valuation_eq_of_comp_eq' {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] (D₁ D₂ : DivisorOver k sX) (g : D₁.Y ⟶ D₂.Y)
    (hg : g ≫ D₂.f = D₁.f) (hbg : IsBirationalMorphism g)
    (hgen : g D₁.E.genericPoint = D₂.E.genericPoint) : D₁.valuation = D₂.valuation := by
  haveI := D₁.isIntegral
  haveI := D₂.isIntegral
  haveI := D₁.isNormal
  haveI := D₂.isNormal
  haveI := D₁.isLocallyNoetherian
  haveI := D₂.isLocallyNoetherian
  haveI := D₁.isDominant
  haveI := D₂.isDominant
  haveI : IsDominant g := hbg.isDominant
  let D' : DivisorOver k (D₂.f ≫ sX) :=
    ⟨D₁.Y, g, by rw [← Category.assoc, hg]; exact D₁.isNormalVariety, hbg, D₁.E⟩
  have h := MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq D₂.isNormalVariety
    D' D₂.E hgen
  ext t
  have h' := congrArg (fun v => v (functionFieldMap D₂.f t)) h
  change D₁.E.divisorialValuation (functionFieldMap D₁.f t) =
    D₂.E.divisorialValuation (functionFieldMap D₂.f t)
  change D₁.E.divisorialValuation (functionFieldMap g (functionFieldMap D₂.f t)) =
    D₂.E.divisorialValuation (functionFieldMap (𝟙 _) (functionFieldMap D₂.f t)) at h'
  rw [MMP.Mori.functionFieldMap_id_apply,
    MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply] at h'
  have key : ∀ (φ : D₁.Y ⟶ X) [IsDominant φ], φ = D₁.f →
      functionFieldMap φ t = functionFieldMap D₁.f t := by
    rintro φ _ rfl; rfl
  rwa [key (g ≫ D₂.f) hg] at h'

open scoped Classical in
/-- **A floor stratum inside `W` mapping birationally onto `h(W)`, at the level of points.** -/
private theorem exists_point_isSNCStratum_birational {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {B : QDivisor X} {C : QDivisor Y} (hB : IsSNCSubboundaryPair sX B)
    (hC : IsSNCSubboundaryPair sY C) {n : ℕ} {KX : Divisor X} (hKX : KX.IsCanonicalDivisor sX n)
    {KY : Divisor Y} (hKY : KY.IsCanonicalDivisor sY n)
    (h : Y ⟶ X) (hh : h ≫ sX = sY) (hproj : IsProjectiveMorphism h)
    (hbir : IsBirationalMorphism h)
    (hcrep : ∀ hY : IsNormalVariety k (h ≫ sX), IsCrepantBoundary sX n KX B h hY hbir C)
    {w : Y} (hW : IsSNCStratum (coeffOnePart C) (closure {w}))
    (hW' : closure {w} ≠ Set.univ) :
    ∃ y ∈ closure {w}, IsSNCStratum (coeffOnePart C) (closure {y}) ∧ h y = h w ∧
      Function.Bijective (h.residueFieldMap y) := by
  subst hh
  have hX : IsNormalVariety k sX := ⟨hB.isProjectiveVariety.toIsVariety, inferInstance⟩
  have hY : IsNormalVariety k (h ≫ sX) := ⟨hC.isProjectiveVariety.toIsVariety, inferInstance⟩
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hX.1.toQuasiCompact
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : LocallyOfFiniteType (h ≫ sX) := hY.1.toLocallyOfFiniteType
  haveI : QuasiCompact (h ≫ sX) := hY.1.toQuasiCompact
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (h ≫ sX)
  haveI : IsProper h := isProper_of_isProjectiveMorphism h hproj
  haveI : IsDominant h := hbir.isDominant
  have hn := hKX.topologicalKrullDim_eq
  by_cases hlow : Order.coheight (h w) ≤ 1
  · have hreg := MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal h hbir hlow
    haveI := MMP.isIso_stalkMap_of_mem_biregularLocus h (x := w) hreg
    exact ⟨w, subset_closure rfl, hW, rfl, bijective_residueFieldMap_of_isIso_stalkMap h w⟩
  have h2 : 2 ≤ Order.coheight (h w) := Order.add_one_le_of_lt (not_le.mp hlow)
  -- the floor structure of `W`
  have hsncC1 : (coeffOnePart C).IsSNC (h ≫ sX) :=
    hC.isSNC.of_support_subset (support_coeffOnePart_subset C)
  have hsncB1 : (coeffOnePart B).IsSNC sX :=
    hB.isSNC.of_support_subset (support_coeffOnePart_subset B)
  obtain ⟨JW, hJW, hmaxW⟩ := id hW
  obtain ⟨w', hWw', hw'J, hcw'⟩ := coheight_eq_card_of_isSNCStratum hsncC1 hJW hmaxW
  have hww' : w = w' := (inseparable_iff_closure_eq.2 hWw').eq
  subst hww'
  have hJWne : JW.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    exact hW' (hmaxW.eq_of_ge ⟨IrreducibleSpace.isIrreducible_univ Y, by simp⟩
      (Set.subset_univ _)).symm
  -- the image stratum
  obtain ⟨hsmW, -⟩ := stratum_closure (h ≫ sX) hsncC1 hJW hw'J hcw'
  set Vw := Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure {w}) with hVw
  haveI : LocallyOfFinitePresentation (Vw.subschemeι ≫ h ≫ sX) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := Vw.subschemeι ≫ h ≫ sX)).mpr
      inferInstance
  haveI : Smooth (Vw.subschemeι ≫ h ≫ sX) := (MMP.Mori.isSmoothScheme_iff _).1 hsmW
  haveI : IsReduced Vw.subscheme := isReduced_of_smooth (Vw.subschemeι ≫ h ≫ sX)
  have hrV : Set.range Vw.subschemeι.base = closure {w} := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal,
      TopologicalSpace.Closeds.coe_closure]
  have hZst : IsSNCStratum (coeffOnePart B) (closure {h w}) := by
    have := isSNCStratum_image hB hC hKX hKY h rfl hproj hbir hcrep Vw.subschemeι
      (by rw [hrV]; exact hW) (by rw [hrV]; exact hW')
    rwa [hrV, ← h.isClosedMap.closure_image_eq_of_continuous h.continuous, Set.image_singleton]
      at this
  obtain ⟨JZ, hJZ, hmaxZ⟩ := id hZst
  obtain ⟨ξ', hZξ', hξ'J, hcξ'⟩ := coheight_eq_card_of_isSNCStratum hsncB1 hJZ hmaxZ
  have hξξ' : h w = ξ' := (inseparable_iff_closure_eq.2 hZξ').eq
  rw [← hξξ'] at hξ'J hcξ'
  have hJZne : JZ.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    rw [hcξ'] at h2
    simp at h2
  have hξL : h w ∈ oneLocus (floorRDivisor B) := by
    obtain ⟨G, hG⟩ := hJZne
    exact ⟨G, by rw [coeff_floorRDivisor, if_pos (coeff_eq_one_of_mem_support_coeffOnePart
      (hJZ hG))], hξ'J G hG⟩
  have hξoff : ∀ G : MMP.Mori.PrimeDivisor X, h w ∈ G.support → B.coeff G ≠ 0 →
      B.coeff G = 1 := by
    intro G hG hG0
    by_contra hG1
    have hGJ : G ∉ JZ := fun hGJ => hG1 (coeff_eq_one_of_mem_support_coeffOnePart (hJZ hGJ))
    obtain ⟨c, hc, hcard⟩ := card_le_coheight_of_isSNC hB.isSNC (h w) (insert G JZ)
      (Finset.insert_subset (Finsupp.mem_support_iff.mpr hG0)
        (hJZ.trans (support_coeffOnePart_subset B))) (fun G' hG' => by
          rcases Finset.mem_insert.mp hG' with rfl | hG'
          · exact hG
          · exact hξ'J G' hG')
    rw [hcξ'] at hc
    have hcJ : c = JZ.card := by exact_mod_cast hc.symm
    rw [Finset.card_insert_of_notMem hGJ, hcJ] at hcard
    omega
  -- a divisor over `Y` centred at `w` with discrepancy `-1`
  have hPY : MMP.Mori.IsPair (h ≫ sX) C :=
    ⟨hY, n, KY, hKY, isQCartier_of_isSmoothScheme hC.isSmoothScheme _⟩
  obtain ⟨vY, hvYc, hvYp, hvY⟩ : ∃ vY : DivisorOver k (h ≫ sX), vY.f vY.E.genericPoint = w ∧
      IsProper vY.f ∧ IsDiscrepancy (h ≫ sX) n KY C vY (-1) := by
    by_cases hJ1 : JW.card = 1
    · obtain ⟨G, rfl⟩ := Finset.card_eq_one.mp hJ1
      have hwG : w = G.genericPoint := by
        have hsp : G.genericPoint ⤳ w := by
          rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
          exact hw'J G (Finset.mem_singleton_self G)
        by_contra hne
        have hlt : w < G.genericPoint := lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hsp)
          (fun h' => hne (hsp.antisymm (Scheme.le_iff_specializes.mp h')).eq.symm)
        have := Order.coheight_strictAnti hlt (by
          rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]; exact ENat.coe_lt_top _)
        rw [hcw', AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at this
        simp at this
      obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPY hKY
        (DivisorOver.ofPrimeDivisor k hY G)
      have ha' := IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hY ha
      rw [coeff_eq_one_of_mem_support_coeffOnePart (hJW (Finset.mem_singleton_self G))] at ha'
      rw [ha'] at ha
      refine ⟨DivisorOver.ofPrimeDivisor k hY G, ?_, ?_, ha⟩
      · rw [hwG]; rfl
      · change IsProper (𝟙 Y); infer_instance
    · exact exists_isDiscrepancy_eq_neg_one_of_coheight_eq_card hC hKY hJW hw'J hcw' (by
        have := Finset.card_pos.mpr hJWne; omega)
  -- as a divisor over `X`
  have hP : MMP.Mori.IsPair sX B :=
    ⟨hX, n, KX, hKX, isQCartier_of_isSmoothScheme hB.isSmoothScheme _⟩
  set vX := compDivisorOver h hY hbir vY with hvXdef
  have hvX : IsDiscrepancy sX n KX B vX (-1) :=
    ((MMP.Mori.IsPair.isDiscrepancy_iff_of_crepant hP h hY hbir hKX hKY (Or.inl (hcrep hY))).2 vY
      vX (valuation_compDivisorOver h hY hbir vY) (-1)).mp hvY
  have hvXc : vX.f vX.E.genericPoint = h w := by
    change h (vY.f vY.E.genericPoint) = h w; rw [hvYc]
  have hvXp : IsProper vX.f := by
    haveI := hvYp; change IsProper (vY.f ≫ h); infer_instance
  -- the discrepancy over the floor part
  set Q₁ := Divisor.toQDivisor (coeffOnePart B) with hQ₁
  have hPW : MMP.Mori.IsPairWith sX n KX B :=
    ⟨hX, hKX, isQCartier_of_isSmoothScheme hB.isSmoothScheme _⟩
  obtain ⟨-, hgenΔ, hiffΔ⟩ := hPW.isDiscrepancy_add_smul_iff (Δ' := Q₁ - B)
    (isQCartier_of_isSmoothScheme hB.isSmoothScheme _) vX
  have hvXQ : IsDiscrepancy sX n KX Q₁ vX (-1) := by
    haveI := vX.isLocallyNoetherian
    haveI := vX.isNormal
    haveI := vX.isIntegral
    haveI : CompactSpace vX.Y := by
      have := vX.isNormalVariety.1
      exact QuasiCompact.compactSpace_of_compactSpace (vX.f ≫ sX)
    have hpb := QDivisor.isPullback_pullback (isQCartier_of_isSmoothScheme hB.isSmoothScheme
      (Q₁ - B)) hgenΔ
    have h0 : ((Q₁ - B).pullback (isQCartier_of_isSmoothScheme hB.isSmoothScheme _) hgenΔ).coeff
        vX.E = 0 := by
      refine qdivisor_coeff_eq_zero_of_isPullback (isQCartier_of_isSmoothScheme hB.isSmoothScheme _)
        hpb vX.E ?_
      rw [hvXc]
      intro hmem
      obtain ⟨G, hG0, hwG⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
      apply hG0
      rw [DivisorWithCoeffs.coeff_sub, hQ₁, Divisor.coeff_toQDivisor, coeff_coeffOnePart]
      by_cases hG1 : B.coeff G = 1
      · rw [if_pos hG1, hG1]; norm_num
      · rw [if_neg hG1]
        by_contra hG2
        exact hG1 (hξoff G hwG (by intro h0; apply hG2; rw [h0]; norm_num))
    have := ((hiffΔ _ hpb).1 (-1)).mpr hvX
    rwa [h0, sub_zero, add_sub_cancel] at this
  have hvlog : MMP.Intersection.IsLogDiscrepancy sX n (floorRDivisor B) vX 0 := by
    have := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hvXQ hvXp
    convert this using 1
    norm_num
  set v : MMP.Flips.ProperDivisorOver k sX := ⟨vX, hvXp⟩ with hvdef
  have hvexc : v.IsExceptional := (properDivisorOver_isExceptional_iff' hn v).mpr (by
    change 2 ≤ Order.coheight (vX.f vX.E.genericPoint)
    rw [hvXc]; exact h2)
  obtain ⟨Xt, _, _, _, _, p, hN, hb, EW, hprojXt, hsmXt, hval, hexc, hsncS, ft, hftEW, hftst, hpft,
    hbijp⟩ := exists_tower hB hn hZst hξL v hvexc hvlog hvXc
  -- the tower model as a crepant pair over the floor part
  haveI : LocallyOfFiniteType (p ≫ sX) := hN.1.toLocallyOfFiniteType
  haveI : AlgebraicGeometry.IsNoetherian Xt := ⟨⟩
  have hTf := finite_setOf_support_subset_of_isSNCClosedSubset hsncS
  set Dt := reducedDivisorOfSet _ hTf with hDt
  have hDtp := isSNCSubboundaryPair_reducedDivisorOfSet hprojXt hsmXt hsncS hTf
  have hDtcrep := isCrepantBoundary_reducedDivisorOfSet_of_tower hB hKX p hN hb hexc hsncS hTf
  have hDt0 : ∀ P, 0 ≤ Dt.coeff P := fun P => by
    rw [hDt, coeff_reducedDivisorOfSet]; split_ifs <;> norm_num
  have hpEW : p EW.genericPoint = h w := by
    rw [← hvXc]
    exact MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hval
  have hLcl : IsClosed (oneLocus (floorRDivisor B)) := by
    rw [oneLocus_floorRDivisor]
    exact MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isClosed_iUnion_support _
  have hEWL : (EW.support : Set Xt) ⊆ p.base ⁻¹' oneLocus (floorRDivisor B) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    refine closure_minimal (Set.singleton_subset_iff.mpr ?_) (hLcl.preimage p.continuous)
    rw [Set.mem_preimage]
    show p (MMP.Mori.PrimeDivisor.genericPoint EW) ∈ _
    rw [hpEW]; exact hξL
  have hDtEW : Dt.coeff EW = 1 := by rw [hDt, coeff_reducedDivisorOfSet, if_pos hEWL]
  haveI : IsSeparated sX := hX.1.toIsSeparated
  have hpproj : IsProjectiveMorphism p := IsProjectiveMorphism.of_comp p sX hprojXt.isProjective
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hpproj
  haveI : IsDominant p := hb.isDominant
  -- the floor part as an snc subboundary
  have hQ₁c : ∀ G, Q₁.coeff G = if B.coeff G = 1 then 1 else 0 := fun G => by
    rw [hQ₁, Divisor.coeff_toQDivisor, coeff_coeffOnePart]; split_ifs <;> simp
  have hBQ : IsSNCSubboundaryPair sX Q₁ := by
    refine ⟨hB.isProjectiveVariety, hB.isSmoothScheme, hB.isSNC.of_support_subset fun G hG => ?_,
      fun G => by rw [hQ₁c]; split_ifs <;> norm_num⟩
    rw [Finsupp.mem_support_iff] at hG ⊢
    intro h0
    apply hG
    change Q₁.coeff G = 0
    rw [hQ₁c, if_neg]
    intro h1
    change B.coeff G = 0 at h0
    rw [h0] at h1
    norm_num at h1
  have hPQ : MMP.Mori.IsPair sX Q₁ :=
    ⟨hX, n, KX, hKX, isQCartier_of_isSmoothScheme hB.isSmoothScheme _⟩
  have hQB : (QDivisor.toRDivisor Q₁).supp ≤ (QDivisor.toRDivisor B).supp := by
    intro x hx
    obtain ⟨G, hG0, hxG⟩ := DivisorWithCoeffs.mem_supp_iff.mp hx
    refine DivisorWithCoeffs.mem_supp_iff.mpr ⟨G, ?_, hxG⟩
    rw [QDivisor.coeff_toRDivisor] at hG0 ⊢
    rw [hQ₁c] at hG0
    split_ifs at hG0 with h1
    · rw [h1]; norm_num
    · norm_num at hG0
  -- the common log resolution
  obtain ⟨Y', q, fP, gP, hY'v, hqproj, hlog, hfP, hgP⟩ := exists_isLogResolution_factors
    hB.isProjectiveVariety (QDivisor.toRDivisor B) h hproj hbir p hpproj hb
  have hres := hlog.toIsSmoothResolution
  obtain ⟨hY'N, hY'dim, -⟩ := hres.isNormalVariety hX
  haveI : IsIntegral Y' := hY'N.1.toIsIntegral
  haveI : LocallyOfFiniteType (q ≫ sX) := hY'N.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian (q ≫ sX)
  haveI : IsNormal Y' := hY'N.2
  haveI : CompactSpace Y' := haveI := hY'N.1.toQuasiCompact
    QuasiCompact.compactSpace_of_compactSpace (q ≫ sX)
  have hqb := hres.isBirationalMorphism
  obtain ⟨Cp, hCpp, hCpcrep⟩ := exists_isSNCSubboundaryPair_isCrepantBoundary hB hKX q hY'v hqproj
    le_rfl hlog
  obtain ⟨C₁p, hC₁pp, hC₁pcrep⟩ := exists_isSNCSubboundaryPair_isCrepantBoundary hBQ hKX q hY'v
    hqproj hQB hlog
  haveI : IsProper q := hqproj.isProper
  haveI : IsDominant q := hqb.isDominant
  -- the two factors
  haveI : IsProper fP := MorphismProperty.of_postcomp @IsProper fP h
    (inferInstance : IsSeparated h) (by rw [hfP]; infer_instance)
  haveI : IsProper gP := MorphismProperty.of_postcomp @IsProper gP p
    (inferInstance : IsSeparated p) (by rw [hgP]; infer_instance)
  haveI : IsDominant (fP ≫ h) := by rw [hfP]; infer_instance
  haveI : IsDominant (gP ≫ p) := by rw [hgP]; infer_instance
  have hfPgen := map_genericPoint_eq_of_comp fP h hbir
  have hgPgen := map_genericPoint_eq_of_comp gP p hb
  haveI : IsDominant fP := ⟨by
    refine dense_iff_closure_eq.mpr (Set.eq_univ_of_univ_subset ?_)
    rw [← (genericPoint_spec Y).def]
    exact closure_mono (Set.singleton_subset_iff.mpr ⟨_, hfPgen⟩)⟩
  haveI : IsDominant gP := ⟨by
    refine dense_iff_closure_eq.mpr (Set.eq_univ_of_univ_subset ?_)
    rw [← (genericPoint_spec Xt).def]
    exact closure_mono (Set.singleton_subset_iff.mpr ⟨_, hgPgen⟩)⟩
  have hfPb : IsBirationalMorphism fP :=
    isBirationalMorphism_of_comp_of_isBirationalMorphism fP h hbir (hfP ▸ hqb)
  have hgPb : IsBirationalMorphism gP :=
    isBirationalMorphism_of_comp_of_isBirationalMorphism gP p hb (hgP ▸ hqb)
  -- structure morphisms and canonical divisors on the models
  have hXtdim : topologicalKrullDim Xt = n :=
    topologicalKrullDim_eq_of_isBirationalMorphism sX p hb hn
  obtain ⟨KXt, hKXt⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (p ≫ sX) hsmXt hXtdim
  have hY'gp : IsNormalVariety k (gP ≫ p ≫ sX) := by
    rw [← Category.assoc, hgP]; exact hY'N
  have hY'gp' : IsNormalVariety k ((gP ≫ p) ≫ sX) := by rw [hgP]; exact hY'N
  have hY'fh : IsNormalVariety k (fP ≫ h ≫ sX) := by
    rw [← Category.assoc, hfP]; exact hY'N
  have hY'fh' : IsNormalVariety k ((fP ≫ h) ≫ sX) := by rw [hfP]; exact hY'N
  have hC₁gp : IsSNCSubboundaryPair (gP ≫ p ≫ sX) C₁p := by
    rw [← Category.assoc, hgP]; exact hC₁pp
  have hCfh : IsSNCSubboundaryPair (fP ≫ h ≫ sX) Cp := by
    rw [← Category.assoc, hfP]; exact hCpp
  haveI : LocallyOfFiniteType (gP ≫ p ≫ sX) := hY'gp.1.toLocallyOfFiniteType
  haveI : AlgebraicGeometry.IsVariety k (gP ≫ p ≫ sX) := hY'gp.1
  have hY'dimn : topologicalKrullDim Y' = n :=
    topologicalKrullDim_eq_of_isBirationalMorphism (p ≫ sX) gP hgPb hXtdim
  obtain ⟨KY'g, hKY'g⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (gP ≫ p ≫ sX)
    hC₁gp.isSmoothScheme hY'dimn
  haveI : LocallyOfFiniteType (fP ≫ h ≫ sX) := hY'fh.1.toLocallyOfFiniteType
  haveI : AlgebraicGeometry.IsVariety k (fP ≫ h ≫ sX) := hY'fh.1
  obtain ⟨KY'f, hKY'f⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (fP ≫ h ≫ sX)
    hCfh.isSmoothScheme hY'dimn
  have hgPp : IsBirationalMorphism (gP ≫ p) := hgP ▸ hqb
  have hfPh : IsBirationalMorphism (fP ≫ h) := hfP ▸ hqb
  -- crepancy of the common resolution
  have hC₁g : ∀ (hY : IsNormalVariety k ((gP ≫ p) ≫ sX)) (hf : IsBirationalMorphism (gP ≫ p)),
      IsCrepantBoundary sX n KX Q₁ (gP ≫ p) hY hf C₁p := by
    rw [hgP]; exact hC₁pcrep
  have hCf : ∀ (hY : IsNormalVariety k ((fP ≫ h) ≫ sX)) (hf : IsBirationalMorphism (fP ≫ h)),
      IsCrepantBoundary sX n KX B (fP ≫ h) hY hf Cp := by
    rw [hfP]; exact hCpcrep
  have hcrepXt : IsCrepantBoundary (p ≫ sX) n KXt Dt gP hY'gp hgPb C₁p :=
    isCrepantBoundary_of_comp hPQ hKX p hN hb hKXt hDtcrep gP hY'gp hgPb hY'gp' hgPp
      (hC₁g hY'gp' hgPp)
  have hcrepY : IsCrepantBoundary (h ≫ sX) n KY C fP hY'fh hfPb Cp :=
    isCrepantBoundary_of_comp hP hKX h hY hbir hKY (hcrep hY) fP hY'fh hfPb hY'fh' hfPh
      (hCf hY'fh' hfPh)
  haveI : IsSeparated (p ≫ sX) := hN.1.toIsSeparated
  haveI : IsSeparated (h ≫ sX) := hY.1.toIsSeparated
  have hgPproj : IsProjectiveMorphism gP :=
    IsProjectiveMorphism.of_comp gP (p ≫ sX) hC₁gp.isProjectiveVariety.isProjective
  have hfPproj : IsProjectiveMorphism fP :=
    IsProjectiveMorphism.of_comp fP (h ≫ sX) hCfh.isProjectiveVariety.isProjective
  -- the strict transform of `E_W`
  have hreg := MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal gP hgPb
    (y := EW.genericPoint) (by rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint])
  obtain ⟨Wp, -, hWp⟩ := MMP.Flips.exists_inverseTransformPrimeDivisor_eq_some EW hreg
  haveI := MMP.isIso_stalkMap_of_mem_biregularLocus gP (x := Wp.genericPoint) (hWp ▸ hreg)
  have hXtN : IsNormalVariety k (p ≫ sX) := hN
  have hC₁Wp : C₁p.coeff Wp = 1 := by
    have hE : ¬ (⟨Y', gP, hY'gp, hgPb, Wp⟩ : DivisorOver k (p ≫ sX)).IsExceptional := by
      rw [isExceptional_iff_two_le_coheight hXtN]
      change ¬ 2 ≤ Order.coheight (gP Wp.genericPoint)
      rw [hWp, AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
      decide
    obtain ⟨P, hcen, hP'⟩ := MMP.Mori.DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff
      ⟨hXtN, hKXt, isQCartier_of_isSmoothScheme hsmXt _⟩ _ hE
    have hcl : closure {gP Wp.genericPoint} = (P.support : Set Xt) := by
      rw [← hcen, MMP.Positivity.DivisorOver.center_eq_closureSingleton]
      rfl
    have hPEW : EW = P := by
      rw [hWp] at hcl
      have hmem : EW.genericPoint ∈ P.support := by rw [← hcl]; exact subset_closure rfl
      have := MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support hmem
      first | exact this | exact this.symm
    subst hPEW
    have := (hcrepXt Wp).eq hP'
    rw [hDtEW] at this
    linarith
  have hWpC : Wp ∈ C₁p.support := Finsupp.mem_support_iff.mpr (by
    change C₁p.coeff Wp ≠ 0; rw [hC₁Wp]; norm_num)
  have hEWD : EW ∈ Dt.support := Finsupp.mem_support_iff.mpr (by
    change Dt.coeff EW ≠ 0; rw [hDtEW]; norm_num)
  -- the lift inside `W⁺`
  have hJZn : JZ.card ≤ n := by
    set Vξ := Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure {h w})
    have hrξ : Set.range Vξ.subschemeι.base = closure {h w} := by
      rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal,
        TopologicalSpace.Closeds.coe_closure]
    have h1 := topologicalKrullDim_add_coheight_of_range sX Vξ.subschemeι hrξ
    rw [hcξ', hn] at h1
    exact le_of_withBot_add_eq (by exact_mod_cast h1)
  have hJZ2 : 2 ≤ JZ.card := by rw [hcξ'] at h2; exact_mod_cast h2
  have hm : (n - 1) + ({EW} : Finset (MMP.Mori.PrimeDivisor Xt)).card = n := by
    rw [Finset.card_singleton]; omega
  have hFst : IsSNCStratum (coeffOnePart Dt) (closure {ft}) :=
    (isComponentStratum_iff_isSNCStratum hsncS hTf _).mp hftst
  have hFr : closure {ft} ⊆ closure {EW.genericPoint} := by
    rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact closure_minimal (Set.singleton_subset_iff.mpr hftEW) EW.idealSheaf.support.isClosed
  obtain ⟨fp, hfpW, hfpst, hfpgen, hfpb⟩ := exists_lift_of_stratum hDtp hDt0 hC₁gp hKXt hKY'g
    gP rfl hgPproj hgPb (fun _ => hcrepXt) (J₀ := {Wp}) (by simpa using hWpC)
    (by simpa using hC₁Wp)
    (by simpa using MMP.Positivity.PrimeDivisor.genericPoint_mem_support' Wp)
    (by simp [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]) (J := {EW})
    (by simpa using hEWD) (by simpa using hDtEW)
    (by simpa using MMP.Positivity.PrimeDivisor.genericPoint_mem_support' EW)
    (by simp [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]) hWp
    (bijective_residueFieldMap_of_isIso_stalkMap gP _) hm (liftProperty k _) hFst hFr
  have hgfp : gP fp = ft := hfpgen.eq isGenericPoint_closure
  -- `C₁⁺` and `C⁺` agree along the prime divisors through `fp`
  have hξnot : h w ∉ (Q₁ - B).supp := by
    intro hmem
    obtain ⟨G, hG0, hwG⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
    apply hG0
    rw [DivisorWithCoeffs.coeff_sub, hQ₁c]
    by_cases hG1 : B.coeff G = 1
    · rw [if_pos hG1, hG1]; norm_num
    · rw [if_neg hG1]
      by_contra hG2
      exact hG1 (hξoff G hwG (by intro h0; apply hG2; rw [h0]; norm_num))
  have hqfp : q fp = h w := by
    rw [← hgP, Scheme.Hom.comp_apply, hgfp, hpft]
  have hagree : ∀ G : MMP.Mori.PrimeDivisor Y', fp ∈ G.support → Cp.coeff G = C₁p.coeff G := by
    intro G hG
    set E : DivisorOver k sX := ⟨Y', q, hY'N, hqb, G⟩
    have hE1 := hCpcrep hY'N hqb G
    have hE2 := hC₁pcrep hY'N hqb G
    obtain ⟨-, hgenE, hiffE⟩ := hPW.isDiscrepancy_add_smul_iff (Δ' := Q₁ - B)
      (isQCartier_of_isSmoothScheme hB.isSmoothScheme _) E
    have hpb := QDivisor.isPullback_pullback (isQCartier_of_isSmoothScheme hB.isSmoothScheme
      (Q₁ - B)) hgenE
    have h0 : ((Q₁ - B).pullback (isQCartier_of_isSmoothScheme hB.isSmoothScheme _) hgenE).coeff
        G = 0 := by
      refine qdivisor_coeff_eq_zero_of_isPullback (isQCartier_of_isSmoothScheme hB.isSmoothScheme _)
        hpb G ?_
      intro hmem
      apply hξnot
      have hsp : G.genericPoint ⤳ fp := by
        rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact hG
      have := (q.base.hom.map_specializes hsp).mem_closed (Q₁ - B).supp.isClosed hmem
      rwa [show q.base.hom fp = h w from hqfp] at this
    have h3 := ((hiffE _ hpb).1 (-Cp.coeff G)).mpr hE1
    rw [h0, sub_zero, add_sub_cancel] at h3
    have := h3.eq hE2
    linarith
  have hfpstC : IsSNCStratum (coeffOnePart Cp) (closure {fp}) := by
    have hsnc1 : (coeffOnePart C₁p).IsSNC (q ≫ sX) :=
      hC₁pp.isSNC.of_support_subset (support_coeffOnePart_subset C₁p)
    obtain ⟨J, hJ, hmax⟩ := hfpst
    obtain ⟨u, hu, huJ, hcu⟩ := coheight_eq_card_of_isSNCStratum (sX := gP ≫ p ≫ sX)
      (hC₁gp.isSNC.of_support_subset (support_coeffOnePart_subset C₁p)) hJ hmax
    have hfpu : fp = u := (inseparable_iff_closure_eq.2 hu).eq
    subst hfpu
    refine isSNCStratum_closure_singleton (hCpp.isSNC.of_support_subset
      (support_coeffOnePart_subset Cp)) fp J (fun G hG => ?_) huJ hcu
    refine mem_support_coeffOnePart ?_
    rw [hagree G (huJ G hG)]
    exact coeff_eq_one_of_mem_support_coeffOnePart (hJ hG)
  -- the image in `Y`
  set Vf := Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure {fp}) with hVf
  have hsncCp1 : (coeffOnePart Cp).IsSNC (fP ≫ h ≫ sX) :=
    hCfh.isSNC.of_support_subset (support_coeffOnePart_subset Cp)
  obtain ⟨Jf, hJf, hmaxf⟩ := id hfpstC
  obtain ⟨u', hu', hu'J, hcu'⟩ := coheight_eq_card_of_isSNCStratum hsncCp1 hJf hmaxf
  have hfpu' : fp = u' := (inseparable_iff_closure_eq.2 hu').eq
  subst hfpu'
  obtain ⟨hsmf, -⟩ := stratum_closure (fP ≫ h ≫ sX) hsncCp1 hJf hu'J hcu'
  haveI : LocallyOfFinitePresentation (Vf.subschemeι ≫ fP ≫ h ≫ sX) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType
      (f := Vf.subschemeι ≫ fP ≫ h ≫ sX)).mpr inferInstance
  haveI : Smooth (Vf.subschemeι ≫ fP ≫ h ≫ sX) := (MMP.Mori.isSmoothScheme_iff _).1 hsmf
  haveI : IsReduced Vf.subscheme := isReduced_of_smooth (Vf.subschemeι ≫ fP ≫ h ≫ sX)
  have hrVf : Set.range Vf.subschemeι.base = closure {fp} := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal,
      TopologicalSpace.Closeds.coe_closure]
  have hfpne : closure {fp} ≠ Set.univ := by
    intro hu
    have : (Set.univ : Set Y') ⊆ Wp.support := by
      rw [← hu, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact closure_minimal (Set.singleton_subset_iff.mpr hfpW) isClosed_closure
    have hgY : genericPoint Y' ∈ Wp.support := this trivial
    have hsp : Wp.genericPoint ⤳ genericPoint Y' := by
      rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact hgY
    have heq : Wp.genericPoint = genericPoint Y' := (hsp.antisymm (genericPoint_specializes _)).eq
    have h1 := MMP.Mori.PrimeDivisor.coheight_genericPoint Wp
    rw [heq, Order.coheight_eq_zero.mpr fun b _ =>
      Scheme.le_iff_specializes.mpr (genericPoint_specializes b)] at h1
    exact absurd h1 (by decide)
  have hFY := isSNCStratum_image hC hCfh hKY hKY'f fP rfl hfPproj hfPb (fun _ => hcrepY)
    Vf.subschemeι (by rw [hrVf]; exact hfpstC) (by rw [hrVf]; exact hfpne)
  rw [hrVf, ← fP.isClosedMap.closure_image_eq_of_continuous fP.continuous, Set.image_singleton]
    at hFY
  -- the centre of `W⁺` on `Y` is `w`
  have hvW : fP Wp.genericPoint = w := by
    set D₁ : DivisorOver k sX := ⟨Y', q, hY'N, hqb, Wp⟩
    set D₂ : DivisorOver k sX := ⟨Xt, p, hN, hb, EW⟩
    have h1 : D₁.valuation = D₂.valuation := valuation_eq_of_comp_eq' D₁ D₂ gP hgP hgPb hWp
    set D₃ : DivisorOver k (h ≫ sX) := ⟨Y', fP, hY'fh, hfPb, Wp⟩
    have h2 : (compDivisorOver h hY hbir D₃).valuation = D₁.valuation :=
      valuation_eq_of_comp_eq' _ D₁ (𝟙 Y') (by
        change 𝟙 Y' ≫ q = fP ≫ h; rw [Category.id_comp, hfP])
        (@isBirationalMorphism_of_isIso _ _ (𝟙 Y') (IsIso.id Y')) rfl
    have h3 : D₃.valuation = vY.valuation := by
      have e1 := valuation_compDivisorOver h hY hbir D₃
      have e2 := valuation_compDivisorOver h hY hbir vY
      have e3 : (compDivisorOver h hY hbir D₃).valuation = vX.valuation := by
        rw [h2, h1, hval]
      rw [e1, hvXdef, e2] at e3
      ext t
      obtain ⟨s, rfl⟩ := hbir.functionFieldMap_bijective.2 t
      exact congrArg (fun v => v s) e3
    have := MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hY.1 h3
    rw [← hvYc]
    exact this
  refine ⟨fP fp, ?_, hFY, ?_, ?_⟩
  · have h1 : fP fp ∈ fP.base '' closure {Wp.genericPoint} :=
      ⟨fp, hfpW, rfl⟩
    have h2 := image_closure_subset_closure_image fP.continuous h1
    rwa [Set.image_singleton, show fP.base.hom Wp.genericPoint = w from hvW] at h2
  · rw [← Scheme.Hom.comp_apply, hfP, ← hgP, Scheme.Hom.comp_apply, hgfp, hpft]
  · have hb1 : Function.Bijective ((gP ≫ p).residueFieldMap fp) :=
      (bijective_residueFieldMap_comp_iff gP p fp hfpb).mpr (by rw [hgfp]; exact hbijp)
    have hb2 : Function.Bijective ((fP ≫ h).residueFieldMap fp) := by
      rw [hfP, ← hgP]; exact hb1
    rw [coe_residueFieldMap_comp] at hb2
    have hfs : Function.Surjective (fP.residueFieldMap fp) := hb2.2.of_comp
    have hfb : Function.Bijective (fP.residueFieldMap fp) :=
      ⟨(fP.residueFieldMap fp).hom.injective, hfs⟩
    exact (Function.Bijective.of_comp_iff' hfb _).mp hb2

/-- **A floor substratum birational to the image.** A proper floor stratum `W` of the crepant snc
model `(Y, C)` contains a floor stratum `F` mapping birationally onto `Z = h(W)`. -/
private theorem exists_isSNCStratum_isBirationalMorphism {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {B : QDivisor X} {C : QDivisor Y} (hB : IsSNCSubboundaryPair sX B)
    (hC : IsSNCSubboundaryPair sY C) {n : ℕ} {KX : Divisor X} (hKX : KX.IsCanonicalDivisor sX n)
    {KY : Divisor Y} (hKY : KY.IsCanonicalDivisor sY n)
    (h : Y ⟶ X) (hh : h ≫ sX = sY) (hproj : IsProjectiveMorphism h)
    (hbir : IsBirationalMorphism h)
    (hcrep : ∀ hY : IsNormalVariety k (h ≫ sX), IsCrepantBoundary sX n KX B h hY hbir C)
    {W : Scheme.{0}} (ιW : W ⟶ Y) [IsClosedImmersion ιW] [IsReduced W]
    (hW : IsSNCStratum (coeffOnePart C) (Set.range ιW.base))
    (hW' : Set.range ιW.base ≠ Set.univ)
    {Z : Scheme.{0}} (ιZ : Z ⟶ X) [IsClosedImmersion ιZ] [IsReduced Z]
    (hZ : Set.range ιZ.base = h.base '' Set.range ιW.base) :
    ∃ (F : Scheme.{0}) (j : F ⟶ W) (_ : IsClosedImmersion j) (_ : IsReduced F) (g : F ⟶ Z),
        IsSNCStratum (coeffOnePart C) (Set.range (j ≫ ιW).base) ∧
        g ≫ ιZ = j ≫ ιW ≫ h ∧ IsBirationalMorphism g := by
  subst hh
  have hX : IsNormalVariety k sX := ⟨hB.isProjectiveVariety.toIsVariety, inferInstance⟩
  have hY : IsNormalVariety k (h ≫ sX) := ⟨hC.isProjectiveVariety.toIsVariety, inferInstance⟩
  haveI : LocallyOfFiniteType (h ≫ sX) := hY.1.toLocallyOfFiniteType
  haveI : QuasiCompact (h ≫ sX) := hY.1.toQuasiCompact
  haveI : IsProper h := isProper_of_isProjectiveMorphism h hproj
  have hsncC1 : (coeffOnePart C).IsSNC (h ≫ sX) :=
    hC.isSNC.of_support_subset (support_coeffOnePart_subset C)
  obtain ⟨JW, hJW, hmaxW⟩ := id hW
  obtain ⟨w, hWw, -, -⟩ := coheight_eq_card_of_isSNCStratum hsncC1 hJW hmaxW
  obtain ⟨y, hyW, hyst, hyh, hyb⟩ := exists_point_isSNCStratum_birational hB hC hKX hKY h rfl
    hproj hbir hcrep (w := w) (hWw ▸ hW) (hWw ▸ hW')
  -- the reduced subscheme on `closure {y}`
  obtain ⟨Jy, hJy, hmaxy⟩ := id hyst
  obtain ⟨y', hyy', hy'J, hcy'⟩ := coheight_eq_card_of_isSNCStratum hsncC1 hJy hmaxy
  have hyeq : y = y' := (inseparable_iff_closure_eq.2 hyy').eq
  subst hyeq
  obtain ⟨hsmy, -⟩ := stratum_closure (h ≫ sX) hsncC1 hJy hy'J hcy'
  set V := Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure {y}) with hV
  haveI : LocallyOfFinitePresentation (V.subschemeι ≫ h ≫ sX) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := V.subschemeι ≫ h ≫ sX)).mpr
      inferInstance
  haveI : Smooth (V.subschemeι ≫ h ≫ sX) := (MMP.Mori.isSmoothScheme_iff _).1 hsmy
  haveI : IsReduced V.subscheme := isReduced_of_smooth (V.subschemeι ≫ h ≫ sX)
  have hrV : Set.range V.subschemeι.base = closure {y} := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal,
      TopologicalSpace.Closeds.coe_closure]
  haveI : IsIntegral V.subscheme :=
    isIntegral_of_isIrreducible_range V.subschemeι (hrV ▸ isIrreducible_singleton.closure)
  -- the factorizations
  have hsubW : Set.range V.subschemeι.base ⊆ Set.range ιW.base := by
    rw [hrV, hWw]
    exact closure_minimal (Set.singleton_subset_iff.mpr hyW) isClosed_closure
  obtain ⟨j, hj⟩ := exists_comp_eq_of_range_subset ιW V.subschemeι hsubW
  haveI : IsClosedImmersion j := by
    have : IsClosedImmersion (j ≫ ιW) := by rw [hj]; infer_instance
    exact IsClosedImmersion.of_comp_isClosedImmersion j ιW
  have hrange : Set.range (j ≫ ιW).base = closure {y} := by rw [hj, hrV]
  have hsubZ : Set.range (j ≫ ιW ≫ h).base ⊆ Set.range ιZ.base := by
    rw [hZ]
    rintro _ ⟨x, rfl⟩
    exact ⟨(j ≫ ιW) x, ⟨j x, rfl⟩, rfl⟩
  obtain ⟨g, hg⟩ := exists_comp_eq_of_range_subset ιZ (j ≫ ιW ≫ h) hsubZ
  haveI : IsIntegral Z := by
    refine isIntegral_of_isIrreducible_range ιZ ?_
    rw [hZ]
    obtain ⟨_, _, hmax⟩ := hW
    exact hmax.1.1.image _ h.continuous.continuousOn
  haveI : IsProper g := MorphismProperty.of_postcomp @IsProper g ιZ
    (inferInstance : IsSeparated ιZ) (by rw [hg]; infer_instance)
  have hgenF : (j ≫ ιW) (genericPoint V.subscheme) = y :=
    map_genericPoint_eq_of_range_closure (j ≫ ιW) hrange
  have hZw : Set.range ιZ.base = closure {h w} := by
    rw [hZ, hWw, ← h.isClosedMap.closure_image_eq_of_continuous h.continuous, Set.image_singleton]
  have hgenZ : ιZ (genericPoint Z) = h w := map_genericPoint_eq_of_range_closure ιZ hZw
  refine ⟨V.subscheme, j, inferInstance, inferInstance, g, by rw [hrange]; exact hyst, hg, ?_⟩
  refine isBirationalMorphism_of_bijective_residueFieldMap (j ≫ ιW) ιZ h g
    (by rw [hg, Category.assoc]) (by rw [hgenF, hgenZ, hyh]) (by rw [hgenF]; exact hyb)

/-- **A section-equivalent floor substratum birational to the image.** For a proper floor stratum
`W` of `(Y, C)` with image `Z`, there is a floor stratum `F ⊆ W` mapping birationally onto `Z` such
that restriction of sections of `𝒪_Y(m(K_Y + C))` from `W` to `F` is bijective in every even
degree `m > 0` clearing the denominators of `B`. -/
private theorem exists_isSNCStratum_bijective_restriction {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k]
    {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {B : QDivisor X} {C : QDivisor Y} (hB : IsSNCSubboundaryPair sX B)
    (hC : IsSNCSubboundaryPair sY C) {n : ℕ} {KX : Divisor X} (hKX : KX.IsCanonicalDivisor sX n)
    {KY : Divisor Y} (hKY : KY.IsCanonicalDivisor sY n)
    (h : Y ⟶ X) (hh : h ≫ sX = sY) (hproj : IsProjectiveMorphism h)
    (hbir : IsBirationalMorphism h)
    (hcrep : ∀ hY : IsNormalVariety k (h ≫ sX), IsCrepantBoundary sX n KX B h hY hbir C)
    {W : Scheme.{0}} (ιW : W ⟶ Y) [IsClosedImmersion ιW] [IsReduced W]
    (hW : IsSNCStratum (coeffOnePart C) (Set.range ιW.base))
    (hW' : Set.range ιW.base ≠ Set.univ)
    {Z : Scheme.{0}} (ιZ : Z ⟶ X) [IsClosedImmersion ιZ] [IsReduced Z]
    (hZ : Set.range ιZ.base = h.base '' Set.range ιW.base) :
    ∃ (F : Scheme.{0}) (j : F ⟶ W) (_ : IsClosedImmersion j) (_ : IsReduced F) (g : F ⟶ Z),
        IsSNCStratum (coeffOnePart C) (Set.range (j ≫ ιW).base) ∧
        g ≫ ιZ = j ≫ ιW ≫ h ∧ IsBirationalMorphism g ∧
        (∀ m : ℕ, 0 < m → Even m → (∀ P, ((m : ℚ) * B.coeff P).den = 1) →
          Function.Bijective
            (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
              ((Scheme.Modules.pullback ιW).obj
                ((m : ℤ) • KY + DivisorWithCoeffs.roundDown ((m : ℤ) • C)).divisorialSheaf)).app
                ⊤)) := by
  obtain ⟨F, j, hj, hF, g, hFst, hg, hgb⟩ :=
    exists_isSNCStratum_isBirationalMorphism hB hC hKX hKY h hh hproj hbir hcrep ιW hW hW' ιZ hZ
  have hZst := hZ ▸ isSNCStratum_image hB hC hKX hKY h hh hproj hbir hcrep ιW hW hW'
  exact ⟨F, j, hj, hF, g, hFst, hg, hgb, fun m hm _ hden =>
    bijective_restriction_of_isBirationalMorphism hB hC hKX hKY h hh hproj hbir hcrep ιW hW ιZ hZ
      hZst j g hFst hg hgb m hm hden⟩

end Proof_lem_fourfold_crepant_snc_stratum_section_reduction

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori

open scoped Classical in
open Proof_lem_fourfold_crepant_snc_stratum_section_reduction in
/-- **A floor stratum has a section-equivalent substratum birational to its image.** Let
`h : Y ⟶ X` be a projective birational morphism over `k` of smooth projective varieties carrying
snc subboundaries `C`, `B` (`MMP.Fourfold.IsSNCSubboundaryPair`) with `K_Y + C = h^*(K_X + B)`
(`MMP.Mori.IsCrepantBoundary`). Let `W ⊂ Y` be a proper stratum of `C^{=1}`
(`MMP.Fourfold.IsSNCStratum`, `MMP.Fourfold.coeffOnePart`) and `Z ⊆ X` the reduced closed
subscheme on `h(W)`. Then `Z` is a stratum of `B^{=1}`, and there are a stratum `F ⊆ W` of
`C^{=1}` and a birational morphism `g : F ⟶ Z` induced by `h` such that
* for every even `m > 0` with `mB` integral, restriction
  `H⁰(W, 𝒪_Y(m(K_Y + C))|_W) → H⁰(F, 𝒪_Y(m(K_Y + C))|_F)` is bijective;
* `F` is normal, and `C_F`, the pull-back to `F` of `C` minus the components of `C^{=1}`
  containing `F`, is defined;
* for every flag of iterated adjunction with final pair `(T, B_T)` on `Z`, the induced morphism
  `F ⟶ T` is birational and `C_F` is the crepant boundary of `(T, B_T)`. -/
@[mmp "lem_fourfold_crepant_snc_stratum_section_reduction"]
public theorem IsSNCSubboundaryPair.isSNCStratum_image_and_exists_bijective_restriction
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {B : QDivisor X} {C : QDivisor Y} (hB : IsSNCSubboundaryPair sX B)
    (hC : IsSNCSubboundaryPair sY C) {n : ℕ} {KX : Divisor X} (hKX : KX.IsCanonicalDivisor sX n)
    {KY : Divisor Y} (hKY : KY.IsCanonicalDivisor sY n)
    (h : Y ⟶ X) (hh : h ≫ sX = sY) (hproj : IsProjectiveMorphism h)
    (hbir : IsBirationalMorphism h)
    (hcrep : ∀ hY : IsNormalVariety k (h ≫ sX), IsCrepantBoundary sX n KX B h hY hbir C)
    {W : Scheme.{0}} (ιW : W ⟶ Y) [IsClosedImmersion ιW] [IsReduced W]
    (hW : IsSNCStratum (coeffOnePart C) (Set.range ιW.base))
    (hW' : Set.range ιW.base ≠ Set.univ)
    {Z : Scheme.{0}} (ιZ : Z ⟶ X) [IsClosedImmersion ιZ] [IsReduced Z]
    (hZ : Set.range ιZ.base = h.base '' Set.range ιW.base) :
    IsSNCStratum (coeffOnePart B) (Set.range ιZ.base) ∧
      ∃ (F : Scheme.{0}) (j : F ⟶ W) (_ : IsClosedImmersion j) (_ : IsReduced F) (g : F ⟶ Z),
        IsSNCStratum (coeffOnePart C) (Set.range (j ≫ ιW).base) ∧
        g ≫ ιZ = j ≫ ιW ≫ h ∧ IsBirationalMorphism g ∧
        (∀ m : ℕ, 0 < m → Even m → (∀ P, ((m : ℚ) * B.coeff P).den = 1) →
          Function.Bijective
            (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
              ((Scheme.Modules.pullback ιW).obj
                ((m : ℤ) • KY + DivisorWithCoeffs.roundDown ((m : ℤ) • C)).divisorialSheaf)).app
                ⊤)) ∧
        ∃ (_ : IsIntegral F) (_ : IsLocallyNoetherian F) (_ : IsNormal F) (CF : QDivisor F)
          (hgen : ∀ V : irreducibleComponents F, (j ≫ ιW) (componentGenericPoint F V) ∉
            (C - Divisor.toQDivisor ((coeffOnePart C).filter
              fun G => Set.range (j ≫ ιW).base ⊆ G.support)).supp),
          (C - Divisor.toQDivisor ((coeffOnePart C).filter
              fun G => Set.range (j ≫ ιW).base ⊆ G.support)).IsPullback (j ≫ ιW) hgen CF ∧
          ∀ {T : Scheme.{0}} {ιT : T ⟶ X} {BT : QDivisor T}
            (FT : StratumAdjunctionData sX B ιT BT), Set.range ιT.base = Set.range ιZ.base →
          ∀ gT : F ⟶ T, gT ≫ ιT = j ≫ ιW ≫ h →
            haveI := FT.isIntegral_stratum
            haveI := FT.isNormal_stratum
            haveI := FT.isLocallyNoetherian_stratum
            ∃ hg : IsBirationalMorphism gT, ∀ (d : ℕ) (KT : Divisor T),
              KT.IsCanonicalDivisor (ιT ≫ sX) d → ∀ hS : IsNormalVariety k (gT ≫ ιT ≫ sX),
                IsCrepantBoundary (ιT ≫ sX) d KT BT gT hS hg CF := by
  refine ⟨hZ ▸ isSNCStratum_image hB hC hKX hKY h hh hproj hbir hcrep ιW hW hW', ?_⟩
  obtain ⟨F, j, hj, hF, g, hFst, hg, hgb, hbij⟩ :=
    exists_isSNCStratum_bijective_restriction hB hC hKX hKY h hh hproj hbir hcrep ιW hW hW' ιZ hZ
  refine ⟨F, j, hj, hF, g, hFst, hg, hgb, hbij, ?_⟩
  haveI hFi : IsIntegral F := by
    obtain ⟨_, _, hmax⟩ := hFst; exact isIntegral_of_isIrreducible_range (j ≫ ιW) hmax.1.1
  haveI hFn : IsLocallyNoetherian F := by
    subst hh
    have hYv := hC.isProjectiveVariety.toIsVariety
    haveI : LocallyOfFiniteType (h ≫ sX) := hYv.toLocallyOfFiniteType
    exact LocallyOfFiniteType.isLocallyNoetherian ((j ≫ ιW) ≫ h ≫ sX)
  haveI hFN : IsNormal F := isNormal_of_isSNCStratum hC (j ≫ ιW) hFst
  have hgen : ∀ V : irreducibleComponents F, (j ≫ ιW) (componentGenericPoint F V) ∉
      (C - Divisor.toQDivisor ((coeffOnePart C).filter
        fun G => Set.range (j ≫ ιW).base ⊆ G.support)).supp := fun V => by
    rw [componentGenericPoint_eq_genericPoint]
    exact map_genericPoint_notMem_supp_sub_floor hC (j ≫ ιW) hFst
  haveI : CompactSpace Y := by
    subst hh
    haveI := hC.isProjectiveVariety.toIsVariety.toQuasiCompact
    exact QuasiCompact.compactSpace_of_compactSpace (h ≫ sX)
  haveI : CompactSpace F := (j ≫ ιW).isClosedEmbedding.compactSpace
  have hQ : (C - Divisor.toQDivisor ((coeffOnePart C).filter
      fun G => Set.range (j ≫ ιW).base ⊆ G.support)).IsQCartier :=
    isQCartier_of_isSmoothScheme hC.isSmoothScheme _
  refine ⟨hFi, hFn, hFN, _, hgen, QDivisor.isPullback_pullback hQ hgen, ?_⟩
  intro T ιT BT FT hT gT hgT
  haveI := FT.isIntegral_stratum
  haveI := FT.isClosedImmersion
  have hgTb : IsBirationalMorphism gT :=
    isBirationalMorphism_of_range_eq (j ≫ ιW) ιZ (j ≫ ιW) ιT h g (by rw [hg, Category.assoc]) hgb
      rfl hT gT (by rw [hgT, Category.assoc])
  have hFY : Set.range (j ≫ ιW).base ≠ Set.univ := by
    intro hu
    apply hW'
    refine Set.eq_univ_of_univ_subset (hu ▸ ?_)
    rintro _ ⟨x, rfl⟩
    exact ⟨j x, rfl⟩
  exact ⟨hgTb, isCrepantBoundary_of_stratumAdjunctionData hB hC hKX hKY h hh hproj hbir hcrep
    (j ≫ ιW) hFst hFY hgen (QDivisor.isPullback_pullback hQ hgen) FT gT
    (by rw [hgT, Category.assoc]) hgTb⟩

end MMP.Fourfold
