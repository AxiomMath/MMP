module
public import MMP.AlgebraicGeometry.Resolution.EmbeddedResolution.GluingAndIndependence
public import MMP.AlgebraicGeometry.Resolution.EmbeddedResolution.FieldChange
public import MMP.AlgebraicGeometry.Resolution.EmbeddedResolution.StrongProperties

/-!
# Strong resolution of disjoint unions of varieties (Kollár, Resolution of singularities, III)

Over a field `k` of characteristic `0`, there is a rule `𝓑𝓡` assigning to every disjoint union of
varieties `X` over `k` a blow-up sequence `Π : X_r → ⋯ → X_0 = X` such that `X_r` is smooth, `Π`
is an isomorphism over the smooth locus `X^ns`, and `Π⁻¹(Sing X)` is a divisor with simple normal
crossings on `X_r`. The rule is functorial: it commutes (after deleting empty blow-ups) with
smooth morphisms of constant relative dimension, and without deleting them when these are
surjective; it also commutes with change of the ground field.

For a disjoint union of varieties `X` over `k` of characteristic `0`, choose a surjective
local isomorphism `q : X' → X` from an affine scheme (for instance `X' = ∐ U_α` for a finite
affine open cover) and an admissible embedding `X' ⊆ A'` over `k`. The embedded resolution
`𝓑𝓡_{A'}(X')` descends to a unique blow-up sequence `𝓑𝓡(X)` of `X` with `q^*𝓑𝓡(X) = 𝓑𝓡_{A'}(X')`,
and `𝓑𝓡(X)` does not depend on the choices: two such data are compared on the affine scheme
`Y' ×_X X'`, on which both pull back to the embedded resolution by the smooth functoriality of
embedded resolutions. The properties (1)–(3) of `𝓑𝓡(X)` descend from those of `𝓑𝓡_{A'}(X')`
along the surjective local isomorphism `X_r ×_X X' → X_r`, and (4) is the same comparison with
`h : Y → X` in place of the identity, resp. the field change of the embedded resolution.

## Main results

* `MMP.Resolution.exists_strongResolution_blowupSequenceFunctor`: existence of `𝓑𝓡`.

## Implementation notes

The functor is a dependent function on the data `(k, X, X → Spec k)` together with a proof that
`X` is a disjoint union of varieties (`MMP.Resolution.IsDisjointUnionOfVarieties`); it is defined
for fields of every characteristic, and every property is required over fields of
characteristic `0` only, which is equivalent to giving it on characteristic `0` alone. A smooth
morphism `h : Y → X` is a morphism of `k`-schemes, `Y` being over `k` by `h ≫ s_X`. The field
change `X_{L,σ}` is `X ×_{Spec K} Spec L` over `L` by the second projection, and the field change
of a blow-up sequence is its pull-back along the first projection.

For a disjoint union of varieties `X = ⨆_C C` the components `C` are open, so
`⨆_C Sing C = Sing X` and `⨆_C C^ns = X^ns` are the singular and smooth loci of `X → Spec k`
(`MMP.Mori.singularLocus`, `MMP.Mori.smoothLocus`). The auxiliary lemmas of the proof live in the
namespace `Proof_thm_kr3f_strong_resolution`.

## References

* [J. Kollár, *Lectures on resolution of singularities*, Thm. 3.36, Prop. 3.37]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MMP.Mori

universe u

namespace Proof_thm_kr3f_strong_resolution

open CategoryTheory.Limits MMP.Resolution Topology

/-! ### Local isomorphisms -/

private theorem flat_of_isLocalIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocalIso f] : Flat f :=
  have : IsZariskiLocalAtSource @Flat.{u} := HasRingHomProperty.instIsZariskiLocalAtSource
  have : MorphismProperty.ContainsIdentities @Flat.{u} :=
    MorphismProperty.IsMultiplicative.toContainsIdentities
  IsLocalIso.le_of_isZariskiLocalAtSource @Flat.{u} _ _ f ‹_›

private theorem smoothOfRelativeDimension_zero_of_isLocalIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsLocalIso f] : SmoothOfRelativeDimension 0 f :=
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{u} 0) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  have : MorphismProperty.ContainsIdentities (@SmoothOfRelativeDimension.{u} 0) :=
    MorphismProperty.IsMultiplicative.toContainsIdentities
  IsLocalIso.le_of_isZariskiLocalAtSource (@SmoothOfRelativeDimension.{u} 0) _ _ f ‹_›

private theorem locallyOfFiniteType_of_isLocalIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsLocalIso f] : LocallyOfFiniteType f :=
  have : IsZariskiLocalAtSource @LocallyOfFiniteType.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  have : MorphismProperty.ContainsIdentities @LocallyOfFiniteType.{u} :=
    MorphismProperty.IsMultiplicative.toContainsIdentities
  IsLocalIso.le_of_isZariskiLocalAtSource @LocallyOfFiniteType.{u} _ _ f ‹_›

private theorem locallyOfFinitePresentation_of_isLocalIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsLocalIso f] : LocallyOfFinitePresentation f :=
  have : IsZariskiLocalAtSource @LocallyOfFinitePresentation.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  have : MorphismProperty.ContainsIdentities @LocallyOfFinitePresentation.{u} :=
    ⟨fun _ ↦ inferInstance⟩
  IsLocalIso.le_of_isZariskiLocalAtSource @LocallyOfFinitePresentation.{u} _ _ f ‹_›

/-- The morphism `∐ U_α → X` induced by a family of open subschemes is a local isomorphism. -/
private theorem isLocalIso_sigmaDesc {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) :
    IsLocalIso (Sigma.desc fun α ↦ (U α).ι) :=
  have : MorphismProperty.ContainsIdentities @IsLocalIso.{u} :=
    MorphismProperty.IsMultiplicative.toContainsIdentities
  IsZariskiLocalAtSource.sigmaDesc fun _ ↦ IsZariskiLocalAtSource.of_isOpenImmersion _

/-- The morphism `∐ U_α → X` induced by an open cover is surjective. -/
private theorem surjective_sigmaDesc {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (hU : TopologicalSpace.IsOpenCover U) : Surjective (Sigma.desc fun α ↦ (U α).ι) := by
  refine ⟨fun x ↦ ?_⟩
  have hx : x ∈ iSup U := by rw [hU]; trivial
  obtain ⟨α, hα⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  obtain ⟨y, rfl⟩ : x ∈ Set.range (U α).ι.base := by rwa [Scheme.Opens.range_ι]
  refine ⟨(Sigma.ι (fun α ↦ (U α).toScheme) α).base y, ?_⟩
  change (Sigma.ι (fun α ↦ (U α).toScheme) α ≫ Sigma.desc fun α ↦ (U α).ι).base y = _
  rw [Sigma.ι_desc]

/-- A scheme with a local isomorphism to a reduced scheme is reduced. -/
private theorem isReduced_of_isLocalIso {Y X : Scheme.{u}} (f : Y ⟶ X) [IsLocalIso f]
    [IsReduced X] : IsReduced Y := by
  choose V hyV hV using fun y : Y ↦ IsLocalIso.exists_isOpenImmersion (f := f) y
  have hcov : TopologicalSpace.IsOpenCover V :=
    eq_top_iff.mpr fun y _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hyV y⟩
  rw [IsReduced.iff_of_openCover Y (Y.openCoverOfIsOpenCover V hcov)]
  intro y
  exact @isReduced_of_isOpenImmersion _ _ ((V y).ι ≫ f) (hV y) _

/-- If every point has an irreducible open neighbourhood, distinct irreducible components are
disjoint. -/
private theorem disjoint_of_forall_exists_isIrreducible {Y : Type*} [TopologicalSpace Y]
    (h : ∀ y : Y, ∃ N : Set Y, IsOpen N ∧ y ∈ N ∧ IsIrreducible N) :
    ∀ C ∈ irreducibleComponents Y, ∀ C' ∈ irreducibleComponents Y, C ≠ C' → Disjoint C C' := by
  intro C hC C' hC' hne
  refine Set.disjoint_left.mpr fun y hy hy' ↦ hne ?_
  obtain ⟨N, hNo, hyN, hN⟩ := h y
  have key : ∀ D ∈ irreducibleComponents Y, y ∈ D → D = closure N := fun D hD hyD ↦
    have hle : D ⊆ closure N :=
      (subset_closure_inter_of_isPreirreducible_of_isOpen hD.1.2 hNo ⟨y, hyD, hyN⟩).trans
        (closure_mono Set.inter_subset_right)
    le_antisymm hle (hD.2 hN.closure hle)
  rw [key C hC hy, key C' hC' hy']

/-- In a space with finitely many, pairwise disjoint, irreducible components every point has an
irreducible open neighbourhood. -/
private theorem exists_isOpen_isIrreducible_of_disjoint {X : Type*} [TopologicalSpace X]
    (hfin : (irreducibleComponents X).Finite)
    (hdisj : ∀ C ∈ irreducibleComponents X, ∀ C' ∈ irreducibleComponents X, C ≠ C' →
      Disjoint C C') (x : X) :
    ∃ N : Set X, IsOpen N ∧ x ∈ N ∧ IsIrreducible N := by
  obtain ⟨C, hC, hxC⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible {x} isIrreducible_singleton
  set F := ⋃ C' ∈ {C' | C' ∈ irreducibleComponents X ∧ C' ≠ C}, C' with hF_def
  have hF : IsClosed F := (hfin.subset fun C' h ↦ h.1).isClosed_biUnion fun C' h ↦
    isClosed_of_mem_irreducibleComponents C' h.1
  have hsub : Fᶜ ⊆ C := by
    intro z hz
    obtain ⟨C', hC', hzC'⟩ :=
      exists_mem_irreducibleComponents_subset_of_isIrreducible {z} isIrreducible_singleton
    by_contra hzC
    exact hz (Set.mem_biUnion ⟨hC', fun h ↦ hzC (h ▸ hzC' rfl)⟩ (hzC' rfl))
  have hxF : x ∈ Fᶜ := by
    rw [hF_def, Set.mem_compl_iff, Set.mem_iUnion₂]
    rintro ⟨C', ⟨hC', hne⟩, hxC'⟩
    exact Set.disjoint_left.mp (hdisj C' hC' C hC hne) hxC' (hxC rfl)
  exact ⟨Fᶜ, hF.isOpen_compl, hxF, ⟨⟨x, hxF⟩, hC.1.2.open_subset hF.isOpen_compl hsub⟩⟩

/-- Local irreducibility lifts along a local isomorphism. -/
private theorem exists_isOpen_isIrreducible_of_isLocalIso {Y X : Scheme.{u}} (f : Y ⟶ X)
    [IsLocalIso f] (hX : ∀ x : X, ∃ N : Set X, IsOpen N ∧ x ∈ N ∧ IsIrreducible N) (y : Y) :
    ∃ N : Set Y, IsOpen N ∧ y ∈ N ∧ IsIrreducible N := by
  obtain ⟨U, hyU, hU⟩ := IsLocalIso.exists_isOpenImmersion (f := f) y
  obtain ⟨N, hNo, hfy, hN⟩ := hX (f y)
  have hg : IsOpenEmbedding (U.ι ≫ f).base := (U.ι ≫ f).isOpenEmbedding
  have hy : (⟨y, hyU⟩ : U) ∈ (U.ι ≫ f).base ⁻¹' N := hfy
  refine ⟨U.ι.base '' ((U.ι ≫ f).base ⁻¹' N),
    U.ι.isOpenEmbedding.isOpenMap _ (hNo.preimage (U.ι ≫ f).base.hom.continuous),
    ⟨⟨y, hyU⟩, hy, rfl⟩, ⟨⟨_, ⟨⟨y, hyU⟩, hy, rfl⟩⟩, ?_⟩⟩
  exact (hN.2.preimage hg).image _ U.ι.base.hom.continuous.continuousOn

/-- An affine scheme with a local isomorphism to a disjoint union of varieties is again one. -/
private theorem isDisjointUnionOfVarieties_comp_of_isLocalIso {k : Type u} [Field k]
    {X Y : Scheme.{u}} [IsAffine Y] {sX : X ⟶ Spec (.of k)} (hX : IsDisjointUnionOfVarieties sX)
    (f : Y ⟶ X) [IsLocalIso f] : IsDisjointUnionOfVarieties (f ≫ sX) := by
  have : IsReduced X := hX.2.2.1
  have : LocallyOfFiniteType sX := hX.1
  have : QuasiCompact sX := hX.2.1
  have := locallyOfFiniteType_of_isLocalIso f
  have : IsReduced Y := isReduced_of_isLocalIso f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : AlgebraicGeometry.IsNoetherian X := ⟨⟩
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    disjoint_of_forall_exists_isIrreducible (exists_isOpen_isIrreducible_of_isLocalIso f
      (exists_isOpen_isIrreducible_of_disjoint
        TopologicalSpace.NoetherianSpace.finite_irreducibleComponents hX.2.2.2.2))⟩

/-! ### Admissible embeddings into affine space -/

private theorem isSmoothScheme_affineSpace {k : Type u} [Field k] (n : Type u) [Finite n] :
    MMP.Mori.IsSmoothScheme (𝔸(n; Spec (.of k)) ↘ Spec (.of k)) := by
  refine (MMP.Mori.isSmoothScheme_iff _).mpr ?_
  have : Smooth (Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := n) (R := k)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    simp only [CommRingCat.hom_ofHom]
    have : Fintype n := Fintype.ofFinite n
    change RingHom.Smooth (algebraMap k (MvPolynomial n k))
    rw [RingHom.smooth_algebraMap]
    exact ⟨inferInstance, inferInstance⟩
  have e : 𝔸(n; Spec (.of k)) ↘ Spec (.of k) =
      (AffineSpace.SpecIso n (.of k)).hom ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) := by
    rw [← AffineSpace.SpecIso_inv_over, Iso.hom_inv_id_assoc]
  rw [e]
  infer_instance

/-- An affine scheme of finite type over an affine scheme `S` admits a closed embedding over `S`
into an affine space of finite rank over `S`. -/
private theorem exists_isClosedImmersion_affineSpace {S A : Scheme.{u}} [IsAffine S] [IsAffine A]
    (sA : A ⟶ S) [LocallyOfFiniteType sA] :
    ∃ (n : Type u) (_ : Finite n) (j : A ⟶ 𝔸(n; S)),
      IsClosedImmersion j ∧ j ≫ 𝔸(n; S) ↘ S = sA := by
  have hft : RingHom.FiniteType sA.appTop.hom :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
  let := sA.appTop.hom.toAlgebra
  obtain ⟨s, hs⟩ := hft.out
  refine ⟨s, inferInstance, AffineSpace.homOfVector sA (fun x ↦ x.1), ?_,
    AffineSpace.homOfVector_over _ _⟩
  apply IsClosedImmersion.of_surjective_of_isAffine
  intro g
  have hg : g ∈ Algebra.adjoin Γ(S, ⊤) (s : Set Γ(A, ⊤)) := hs ▸ Algebra.mem_top
  rw [Algebra.adjoin_eq_range] at hg
  obtain ⟨p, rfl⟩ := hg
  refine ⟨MvPolynomial.eval₂Hom (𝔸(s; S) ↘ S).appTop.hom (AffineSpace.coord S) p, ?_⟩
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left]
  change _ = MvPolynomial.eval₂ (algebraMap _ _) _ p
  congr 1
  · rw [← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, AffineSpace.homOfVector_over]; rfl
  · funext x
    exact AffineSpace.homOfVector_appTop_coord _ _ _

/-- The coordinate inclusion `𝔸^m_k → 𝔸^{m+1}_k`, `x ↦ (x, 0)`, is a closed immersion over `k`
that is not surjective. -/
private theorem exists_isClosedImmersion_not_surjective (k : Type u) [Field k] (m : Type u) :
    ∃ c : 𝔸(m; Spec (.of k)) ⟶ 𝔸(Option m; Spec (.of k)), IsClosedImmersion c ∧
      ¬ Function.Surjective c.base ∧
      c ≫ 𝔸(Option m; Spec (.of k)) ↘ Spec (.of k) = 𝔸(m; Spec (.of k)) ↘ Spec (.of k) := by
  have happ : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : Γ(Z, ⊤)),
      (f ≫ g).appTop x = f.appTop (g.appTop x) := fun _ _ _ ↦ rfl
  let c : 𝔸(m; Spec (.of k)) ⟶ 𝔸(Option m; Spec (.of k)) :=
    AffineSpace.homOfVector (𝔸(m; Spec (.of k)) ↘ Spec (.of k))
      fun o ↦ o.elim 0 (AffineSpace.coord _)
  let r := AffineSpace.reindex (some : m → Option m) (Spec (.of k))
  have hcr : c ≫ r = 𝟙 _ := by
    apply AffineSpace.hom_ext
    · simp [c, r, AffineSpace.reindex_over]
    · intro i
      rw [happ, AffineSpace.reindex_appTop_coord]
      simp [c, AffineSpace.homOfVector_appTop_coord]
  have hci : IsClosedImmersion c := by
    have : IsClosedImmersion (c ≫ r) := hcr ▸ inferInstance
    exact .of_comp c r
  refine ⟨c, hci, fun hs ↦ ?_, AffineSpace.homOfVector_over _ _⟩
  have : Surjective c := ⟨hs⟩
  have := isIso_of_isClosedImmersion_of_surjective c
  have hrc : r ≫ c = 𝟙 _ := by
    rw [← IsIso.inv_eq_of_hom_inv_id hcr]
    exact IsIso.inv_hom_id c
  have h0 : AffineSpace.coord (Spec (.of k)) (none : Option m) = 0 := by
    have := congrArg (fun φ ↦ φ.appTop (AffineSpace.coord (Spec (.of k)) (none : Option m))) hrc
    simp only [happ, c, AffineSpace.homOfVector_appTop_coord, Option.elim_none, map_zero] at this
    simpa using this.symm
  let t : Spec (.of k) ⟶ 𝔸(Option m; Spec (.of k)) := AffineSpace.homOfVector (𝟙 _) fun _ ↦ 1
  have := congrArg t.appTop h0
  rw [AffineSpace.homOfVector_appTop_coord, map_zero] at this
  exact one_ne_zero this

/-- Every affine disjoint union of varieties over a field of characteristic `0` has an admissible
embedding: into an affine space, with two extra coordinates to make room for codimension `2`. -/
private theorem exists_isAdmissibleEmbedding {k : Type u} [Field k] [CharZero k]
    {Y : Scheme.{u}} [IsAffine Y] (sY : Y ⟶ Spec (.of k)) (hY : IsDisjointUnionOfVarieties sY) :
    ∃ (A : Scheme.{u}) (sA : A ⟶ Spec (.of k)) (i : Y ⟶ A),
      IsAdmissibleEmbedding sA i ∧ i ≫ sA = sY := by
  have : LocallyOfFiniteType sY := hY.1
  obtain ⟨n, _, j, hj, hjs⟩ := exists_isClosedImmersion_affineSpace sY
  obtain ⟨c₁, hc₁, hs₁, ho₁⟩ := exists_isClosedImmersion_not_surjective k n
  obtain ⟨c₂, hc₂, hs₂, ho₂⟩ := exists_isClosedImmersion_not_surjective k (Option n)
  have hover : (j ≫ c₁ ≫ c₂) ≫ 𝔸(Option (Option n); Spec (.of k)) ↘ Spec (.of k) = sY := by
    simp only [Category.assoc, ho₂, ho₁, hjs]
  refine ⟨_, _, j ≫ c₁ ≫ c₂, ⟨‹_›, ‹_›, hover ▸ hY, inferInstance, inferInstance,
    isSmoothScheme_affineSpace _, .of_preirreducibleSpace _, ?_⟩, hover⟩
  intro W _ T hT _
  have hTu : T = Set.univ :=
    Set.eq_univ_of_univ_subset (hT.2 (IrreducibleSpace.isIrreducible_univ _) (Set.subset_univ T))
  obtain ⟨x, hx⟩ := not_forall.mp hs₁
  have hirr : IsIrreducible (Set.range c₂.base) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ c₂.base.hom.continuous.continuousOn
  refine ⟨⟨Set.range c₂.base, hirr, c₂.isClosedEmbedding.isClosed_range⟩,
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩, ?_, ?_, ?_⟩
  · have hsub : (j ≫ c₁ ≫ c₂).base '' W ⊆ Set.range c₂.base := by
      rintro _ ⟨w, -, rfl⟩
      exact ⟨c₁.base (j.base w), rfl⟩
    refine (Set.ssubset_iff_of_subset hsub).mpr ⟨c₂.base x, ⟨x, rfl⟩, ?_⟩
    rintro ⟨w, -, hw⟩
    exact hx ⟨j.base w, c₂.isClosedEmbedding.injective hw⟩
  · exact Set.ssubset_univ_iff.mpr fun h ↦ hs₂ (Set.range_eq_univ.mp h)
  · rw [hTu]
    exact Set.subset_univ _

/-! ### Blow-up sequences -/

/-- Pulling back twice is pulling back along the composite. -/
private theorem pullback_pullback {X W Y : Scheme.{u}} (S : ClosedBlowupSequence X) (h : W ⟶ X)
    (k : Y ⟶ W) : (S.pullback h).pullback k = S.pullback (k ≫ h) :=
  eq_of_heq (S.pullback_pullback_heq h k (k ≫ h) rfl (by simp))

/-- Along a flat surjective morphism, deleting empty blow-ups commutes with pulling back. -/
private theorem reduction_pullback_eq_pullback_reduction {X Y : Scheme.{u}}
    (S : ClosedBlowupSequence X) (f : Y ⟶ X) [Flat f] [Surjective f] :
    (S.pullback f).reduction = S.reduction.pullback f := by
  rw [ClosedBlowupSequence.reduction_pullback,
    ← ClosedBlowupSequence.pullbackReduced_reduction, ← ClosedBlowupSequence.reduction_pullback,
    ClosedBlowupSequence.reduction_eq_self (ClosedBlowupSequence.hasNoEmptyBlowups_pullback _
      (ClosedBlowupSequence.hasNoEmptyBlowups_reduction S) f)]

/-- `𝓑𝓡_A(X)` blows up no empty centre. -/
private theorem hasNoEmptyBlowups_embeddedResolution {k : Type u} [Field k] {X A : Scheme.{u}}
    (sA : A ⟶ Spec (.of k)) (i : X ⟶ A) : (embeddedResolution sA i).HasNoEmptyBlowups := by
  unfold embeddedResolution
  split
  · exact ClosedBlowupSequence.hasNoEmptyBlowups_reduction _
  · trivial

/-- The composite of a blow-up sequence of a locally noetherian scheme is proper. -/
private theorem isProper_toBase :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X] (B : ClosedBlowupSequence X), IsProper B.toBase
  | X, _, .nil _ => by
    change IsProper (𝟙 X)
    infer_instance
  | _, _, .cons Z B => by
    have := isProper_blowUpToBase Z
    have : IsLocallyNoetherian (blowUp Z) :=
      LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase Z)
    have := isProper_toBase B
    change IsProper (B.toBase ≫ blowUpToBase Z)
    infer_instance

/-! ### Blow-up sequences glued from embedded resolutions -/

/-- `G` is *glued from an embedded resolution*: there are a surjective local isomorphism
`q : X' → X` and an admissible embedding `i' : X' → A'` over `k` with `q^*G = 𝓑𝓡_{A'}(X')`. -/
private def IsGluedResolution {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (G : ClosedBlowupSequence X) : Prop :=
  ∃ (X' A' : Scheme.{u}) (q : X' ⟶ X) (sA' : A' ⟶ Spec (.of k)) (i' : X' ⟶ A'),
    IsLocalIso q ∧ Surjective q ∧ IsAdmissibleEmbedding sA' i' ∧ i' ≫ sA' = q ≫ sX ∧
      G.pullback q = embeddedResolution sA' i'

section Glued

variable {k : Type u} [Field k]

/-- A glued blow-up sequence has no empty blow-ups. -/
private theorem hasNoEmptyBlowups_of_isGluedResolution {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {G : ClosedBlowupSequence X} (hG : IsGluedResolution sX G) : G.HasNoEmptyBlowups := by
  obtain ⟨X', A', q, sA', i', hql, hqs, -, -, hGq⟩ := hG
  have := flat_of_isLocalIso q
  have h1 : G.reduction.pullback q = G.pullback q := by
    rw [← reduction_pullback_eq_pullback_reduction, hGq,
      ClosedBlowupSequence.reduction_eq_self (hasNoEmptyBlowups_embeddedResolution _ _)]
  rw [← Kollar.eq_of_pullback_eq_of_flat_of_surjective q h1]
  exact ClosedBlowupSequence.hasNoEmptyBlowups_reduction G

/-- **Comparison of glued sequences along a smooth morphism.** If `G` is glued for `X` and `G_Y`
for `Y`, and `h : Y → X` is smooth of constant relative dimension, then `G_Y = (h^*G)^red`. Both
sides pull back to `𝓑𝓡_{C}(W)` on the affine scheme `W = Y' ×_X X'`. -/
private theorem eq_reduction_pullback_of_isGluedResolution {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (hX : IsDisjointUnionOfVarieties sX) (h : Y ⟶ X) (n : ℕ)
    [SmoothOfRelativeDimension n h] (hY : IsDisjointUnionOfVarieties (h ≫ sX))
    {G : ClosedBlowupSequence X} {GY : ClosedBlowupSequence Y}
    (hG : IsGluedResolution sX G) (hGY : IsGluedResolution (h ≫ sX) GY) :
    GY = (G.pullback h).reduction := by
  have hne := hasNoEmptyBlowups_of_isGluedResolution hGY
  obtain ⟨X', A', q, sA', i', hql, hqs, hadm, hk, hGq⟩ := hG
  obtain ⟨Y', B', qY, sB', j', hqYl, hqYs, hadmY, hkY, hGYq⟩ := hGY
  have : CharZero k := hadm.1
  have : IsAffine X' := hadm.2.1
  have : IsAffine Y' := hadmY.2.1
  have : IsSeparated sX := hX.2.2.2.1
  have : IsAffineHom q := IsAffineHom.of_comp q sX
  have hpb := IsPullback.of_hasPullback (qY ≫ h) q
  set fst := pullback.fst (qY ≫ h) q
  set snd := pullback.snd (qY ≫ h) q
  have : IsAffineHom fst := MorphismProperty.of_isPullback hpb.flip ‹_›
  have : IsAffine (pullback (qY ≫ h) q) := isAffine_of_isAffineHom fst
  have : IsLocalIso fst := MorphismProperty.of_isPullback hpb.flip ‹_›
  have : Surjective fst := MorphismProperty.of_isPullback hpb.flip ‹_›
  have := smoothOfRelativeDimension_zero_of_isLocalIso fst
  have := smoothOfRelativeDimension_zero_of_isLocalIso qY
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := 0 + n)
  have : SmoothOfRelativeDimension (0 + n) (qY ≫ h) := inferInstance
  have : SmoothOfRelativeDimension (0 + n) snd := MorphismProperty.of_isPullback hpb ‹_›
  have : MorphismProperty.IsStableUnderComposition @IsLocalIso.{u} :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  have : IsLocalIso (fst ≫ qY) := MorphismProperty.comp_mem _ _ _ ‹_› ‹_›
  have : Surjective (fst ≫ qY) := inferInstance
  have := flat_of_isLocalIso (fst ≫ qY)
  obtain ⟨C, sC, l, hadmW, hl⟩ := exists_isAdmissibleEmbedding _
    (isDisjointUnionOfVarieties_comp_of_isLocalIso hY (fst ≫ qY))
  have e1 := embeddedResolution_eq_reduction_pullback_of_smoothOfRelativeDimension hadmY hadmW 0
    fst (by rw [hl, hkY]; simp)
  have e2 := embeddedResolution_eq_reduction_pullback_of_smoothOfRelativeDimension hadm hadmW
    (0 + n) snd (by rw [hl, hk, ← Category.assoc, ← pullback.condition]; simp [fst])
  have hsq : snd ≫ q = (fst ≫ qY) ≫ h := by rw [← pullback.condition, Category.assoc]
  refine Kollar.eq_of_pullback_eq_of_flat_of_surjective (fst ≫ qY) ?_
  calc GY.pullback (fst ≫ qY)
      = (GY.pullback (fst ≫ qY)).reduction :=
        (ClosedBlowupSequence.reduction_eq_self
          (ClosedBlowupSequence.hasNoEmptyBlowups_pullback _ hne _)).symm
    _ = embeddedResolution sC l := by rw [← pullback_pullback, hGYq, e1]
    _ = ((G.pullback h).pullback (fst ≫ qY)).reduction := by
        rw [e2, ← hGq, pullback_pullback, pullback_pullback, hsq]
    _ = (G.pullback h).reduction.pullback (fst ≫ qY) :=
        reduction_pullback_eq_pullback_reduction _ _

/-- A glued blow-up sequence is unique. -/
private theorem eq_of_isGluedResolution {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    (hX : IsDisjointUnionOfVarieties sX) {G G' : ClosedBlowupSequence X}
    (hG : IsGluedResolution sX G) (hG' : IsGluedResolution sX G') : G' = G := by
  have hX' : IsDisjointUnionOfVarieties (𝟙 X ≫ sX) := by rwa [Category.id_comp]
  have hG'' : IsGluedResolution (𝟙 X ≫ sX) G' := by rwa [Category.id_comp]
  rw [eq_reduction_pullback_of_isGluedResolution hX (𝟙 X) 0 hX' hG hG'']
  obtain ⟨X', A', q, sA', i', hql, hqs, -, -, hGq⟩ := hG
  have := flat_of_isLocalIso q
  refine Kollar.eq_of_pullback_eq_of_flat_of_surjective q ?_
  rw [← reduction_pullback_eq_pullback_reduction, pullback_pullback, Category.comp_id, hGq,
    ClosedBlowupSequence.reduction_eq_self (hasNoEmptyBlowups_embeddedResolution _ _)]

/-- **Existence of a glued blow-up sequence** (Kollár Prop. 3.37): over a field of
characteristic `0`, the embedded resolution of `∐ U_α`, `(U_α)` a finite affine open cover,
descends to `X`. -/
private theorem exists_isGluedResolution [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    (hX : IsDisjointUnionOfVarieties sX) :
    ∃ G : ClosedBlowupSequence X, IsGluedResolution sX G := by
  have : QuasiCompact sX := hX.2.1
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  choose V hV hxV using fun x : X ↦ (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    X.isBasis_affineOpens (show x ∈ (⊤ : X.Opens) from trivial))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (V x : Set X))
    (fun x ↦ (V x).isOpen) (fun x _ ↦ Set.mem_iUnion.2 ⟨x, (hxV x).1⟩)
  let U : t → X.Opens := fun x ↦ V x.1
  have hU : TopologicalSpace.IsOpenCover U := by
    refine eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ?_
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact ⟨⟨y, hy⟩, hxy⟩
  have hUa : ∀ α, IsAffineOpen (U α) := fun α ↦ hV α.1
  have : ∀ α, IsAffine (U α).toScheme := hUa
  have := isLocalIso_sigmaDesc U
  have := surjective_sigmaDesc U hU
  obtain ⟨A', sA', i', hadm, hi'⟩ := exists_isAdmissibleEmbedding _
    (isDisjointUnionOfVarieties_comp_of_isLocalIso hX (Sigma.desc fun α ↦ (U α).ι))
  obtain ⟨G, hG, -⟩ :=
    existsUnique_pullback_sigmaDesc_eq_embeddedResolution hX U hU hUa hadm hi'
  exact ⟨G, _, A', _, sA', i', ‹_›, ‹_›, hadm, hi', hG⟩

end Glued

/-! ### Descent along surjective local isomorphisms -/

/-- The smooth locus of `p ≫ g`, `p` a local isomorphism, is the preimage of that of `g`. -/
private theorem smoothLocus_comp_of_isLocalIso {T T' S : Scheme.{u}} (p : T' ⟶ T) [IsLocalIso p]
    (g : T ⟶ S) : smoothLocus (p ≫ g) = p ⁻¹ᵁ smoothLocus g := by
  ext y
  change y ∈ smoothLocus (p ≫ g) ↔ p y ∈ smoothLocus g
  rw [mem_smoothLocus_iff, mem_smoothLocus_iff]
  constructor
  · rintro ⟨U, hyU, hU⟩
    obtain ⟨V, hyV, hV⟩ := IsLocalIso.exists_isOpenImmersion (f := p) y
    have hW : (U ⊓ V).ι = T'.homOfLE inf_le_right ≫ V.ι := (Scheme.homOfLE_ι _ _).symm
    have : IsOpenImmersion ((U ⊓ V).ι ≫ p) := by rw [hW, Category.assoc]; infer_instance
    refine ⟨((U ⊓ V).ι ≫ p).opensRange, ⟨⟨y, hyU, hyV⟩, rfl⟩, ?_⟩
    have e : ((U ⊓ V).ι ≫ p).opensRange.ι ≫ g =
        ((U ⊓ V).ι ≫ p).isoOpensRange.inv ≫ T'.homOfLE inf_le_left ≫ U.ι ≫ p ≫ g := by
      rw [← Category.assoc (T'.homOfLE _), Scheme.homOfLE_ι, Iso.eq_inv_comp,
        ← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, Category.assoc]
    rw [e]
    infer_instance
  · rintro ⟨U, hyU, hU⟩
    refine ⟨p ⁻¹ᵁ U, hyU, ?_⟩
    have : Smooth p := (smoothOfRelativeDimension_zero_of_isLocalIso p).smooth
    rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    infer_instance

/-- The singular locus of `p ≫ g`, `p` a local isomorphism, is the preimage of that of `g`. -/
private theorem coe_singularLocus_comp_of_isLocalIso {T T' S : Scheme.{u}} (p : T' ⟶ T)
    [IsLocalIso p] (g : T ⟶ S) :
    (singularLocus (p ≫ g) : Set T') = p ⁻¹' (singularLocus g : Set T) := by
  ext y
  change y ∉ smoothLocus (p ≫ g) ↔ p y ∉ smoothLocus g
  rw [smoothLocus_comp_of_isLocalIso]
  rfl

/-- Smoothness over `S` descends along a surjective local isomorphism. -/
private theorem isSmoothScheme_of_isLocalIso {T T' S : Scheme.{u}} (p : T' ⟶ T) [IsLocalIso p]
    [Surjective p] (g : T ⟶ S) (h : IsSmoothScheme (p ≫ g)) : IsSmoothScheme g := by
  rw [IsSmoothScheme, smoothLocus_comp_of_isLocalIso] at h
  refine eq_top_iff.mpr fun x _ ↦ ?_
  obtain ⟨y, rfl⟩ := p.surjective x
  exact (h ▸ trivial : y ∈ p ⁻¹ᵁ smoothLocus g)

/-- **Being an isomorphism over an open set descends along a surjective local isomorphism.**
In a cartesian square `A = T ×_X X'` with `q : X' → X` a surjective local isomorphism, if the
base change `A → X'` of `g : T → X` is an isomorphism over `q⁻¹S`, then `g` is one over `S`. -/
private theorem isIso_morphismRestrict_of_isPullback {A T X X' : Scheme.{u}} {fst : A ⟶ X'}
    {snd : A ⟶ T} {q : X' ⟶ X} {g : T ⟶ X} (H : IsPullback fst snd q g) [IsLocalIso q]
    [Surjective q] (S : X.Opens) (h : IsIso (fst ∣_ q ⁻¹ᵁ S)) : IsIso (g ∣_ S) := by
  have hEq : fst ⁻¹ᵁ (q ⁻¹ᵁ S) = snd ⁻¹ᵁ (g ⁻¹ᵁ S) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, H.w]
  have H' := Scheme.Hom.isPullback_resLE H.flip (US := S) (UT := q ⁻¹ᵁ S) (UX := g ⁻¹ᵁ S)
    le_rfl le_rfl (UY := fst ⁻¹ᵁ (q ⁻¹ᵁ S)) (by rw [hEq, inf_idem])
  have := flat_of_isLocalIso q
  have := locallyOfFinitePresentation_of_isLocalIso q
  have hq : (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u})
      (q.resLE S (q ⁻¹ᵁ S) le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    have hpb := isPullback_morphismRestrict q S
    exact ⟨⟨MorphismProperty.of_isPullback hpb.flip ‹_›,
      MorphismProperty.of_isPullback hpb.flip ‹_›⟩, MorphismProperty.of_isPullback hpb.flip ‹_›⟩
  have hfst : MorphismProperty.isomorphisms Scheme
      (fst.resLE (q ⁻¹ᵁ S) (fst ⁻¹ᵁ (q ⁻¹ᵁ S)) le_rfl) := by
    rwa [Scheme.Hom.resLE_eq_morphismRestrict]
  have := MorphismProperty.of_isPullback_of_descendsAlong H'.flip hq hfst
  rwa [Scheme.Hom.resLE_eq_morphismRestrict] at this

/-- Being snc at a point descends along a morphism which is an isomorphism on the stalk. -/
private theorem isSNCAt_of_preimage {Y Y' : Scheme.{u}} (f : Y' ⟶ Y) (y : Y')
    [IsIso (f.stalkMap y)] {T : Set Y} (h : IsSNCAt (f ⁻¹' T) y) : IsSNCAt T (f y) := by
  obtain ⟨n, w, C, hw, hT⟩ := h
  let e : Y.presheaf.stalk (f y) ≃+* Y'.presheaf.stalk y :=
    (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv
  refine ⟨n, fun i ↦ e.symm (w i), C, hw.map_ringEquiv e.symm, ?_⟩
  ext a
  let b : Spec (Y'.presheaf.stalk y) :=
    PrimeSpectrum.comap (e.symm : Y'.presheaf.stalk y →+* Y.presheaf.stalk (f y)) a
  have hab : Spec.map (f.stalkMap y) b = a := by
    change PrimeSpectrum.comap (f.stalkMap y).hom b = a
    ext x
    change e.symm (e x) ∈ a.asIdeal ↔ _
    rw [e.symm_apply_apply]
  have hp : Y.fromSpecStalk (f y) a = f (Y'.fromSpecStalk y b) := by
    rw [← hab, ← Scheme.Hom.comp_apply, Scheme.SpecMap_stalkMap_fromSpecStalk,
      Scheme.Hom.comp_apply]
  have key : ∀ c, b ∈ PrimeSpectrum.zeroLocus {w c} ↔
      a ∈ PrimeSpectrum.zeroLocus {e.symm (w c)} := fun c ↦
    (PrimeSpectrum.mem_zeroLocus _ _).trans (Set.singleton_subset_iff.trans
      (Ideal.mem_comap.trans (Set.singleton_subset_iff.symm.trans
        (PrimeSpectrum.mem_zeroLocus _ _).symm)))
  have hb : b ∈ Y'.fromSpecStalk y ⁻¹' (f ⁻¹' T) ↔
      b ∈ ⋃ c ∈ C, PrimeSpectrum.zeroLocus {w c} :=
    Iff.of_eq (congrArg (b ∈ ·) hT)
  change Y.fromSpecStalk (f y) a ∈ T ↔ _
  rw [hp]
  exact hb.trans ((Set.mem_iUnion₂.trans (exists_congr fun c ↦ exists_congr fun _ ↦ key c)).trans
    Set.mem_iUnion₂.symm)

/-- A local isomorphism is an isomorphism on stalks. -/
private theorem isIso_stalkMap_of_isLocalIso {T T' : Scheme.{u}} (p : T' ⟶ T) [IsLocalIso p]
    (y : T') : IsIso (p.stalkMap y) := by
  obtain ⟨V, hyV, hV⟩ := IsLocalIso.exists_isOpenImmersion (f := p) y
  obtain ⟨x, rfl⟩ : ∃ x : V.toScheme, V.ι x = y := ⟨⟨y, hyV⟩, rfl⟩
  have h1 : IsIso (p.stalkMap (V.ι x) ≫ V.ι.stalkMap x) := by
    rw [← Scheme.Hom.stalkMap_comp]
    exact (IsOpenImmersion.iff_isIso_stalkMap.mp hV).2 x
  have h2 : IsIso (V.ι.stalkMap x) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp (inferInstance : IsOpenImmersion V.ι)).2 x
  exact IsIso.of_isIso_comp_right (p.stalkMap (V.ι x)) (V.ι.stalkMap x)

/-- **Divisors with simple normal crossings descend along a surjective local isomorphism.** -/
private theorem isSNCClosedSubset_of_isLocalIso {k : Type u} [Field k] [PerfectField k]
    {T T' : Scheme.{u}} (p : T' ⟶ T) [IsLocalIso p] [Surjective p] (g : T ⟶ Spec (.of k))
    [LocallyOfFiniteType g] [CompactSpace T'] {D : Set T} (hD : IsClosed D)
    (h : IsSNCClosedSubset (p ≫ g) (p ⁻¹' D)) : IsSNCClosedSubset g D := by
  obtain ⟨hc, h0 | ⟨-, -, hfam⟩⟩ := h
  · refine ⟨hD, Or.inl (Set.eq_empty_of_forall_notMem fun x hx ↦ ?_)⟩
    obtain ⟨y, rfl⟩ := p.surjective x
    exact (h0 ▸ (show y ∈ p ⁻¹' D from hx) : y ∈ (∅ : Set T'))
  · have := locallyOfFiniteType_of_isLocalIso p
    have : IsLocallyNoetherian T' := LocallyOfFiniteType.isLocallyNoetherian (p ≫ g)
    have : AlgebraicGeometry.IsNoetherian T' := {}
    have : CompactSpace T := by
      refine ⟨?_⟩
      rw [← Set.image_univ_of_surjective p.surjective]
      exact isCompact_univ.image p.continuous
    refine isSNCClosedSubset_of_forall_isSNCAt g hD fun x ↦ ?_
    obtain ⟨y, rfl⟩ := p.surjective x
    have := isIso_stalkMap_of_isLocalIso p y
    exact isSNCAt_of_preimage p y (IsSNCClosedSubset.isSNCAt_of_nonempty hc hfam y)

/-! ### The properties of the glued sequence -/

section Properties

variable {k : Type u} [Field k]

/-- **(1)–(3) for a glued sequence.** `X_r` is smooth, `Π` is an isomorphism over `X^ns`, and
`Π⁻¹(Sing X)` is a divisor with simple normal crossings: all three descend from the embedded
resolution along the surjective local isomorphism `X_r ×_X X' → X_r`. -/
private theorem isSmoothScheme_and_isIso_and_isSNCClosedSubset_of_isGluedResolution {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)}
    (hX : IsDisjointUnionOfVarieties sX) {G : ClosedBlowupSequence X}
    (hG : IsGluedResolution sX G) :
    IsSmoothScheme (G.toBase ≫ sX) ∧ IsIso (G.toBase ∣_ smoothLocus sX) ∧
      IsSNCClosedSubset (G.toBase ≫ sX) (G.toBase ⁻¹' (singularLocus sX : Set X)) := by
  obtain ⟨X', A', q, sA', i', hql, hqs, hadm, hk, hGq⟩ := hG
  have : CharZero k := hadm.1
  have hs := isSmoothScheme_and_isIso_and_isSNCClosedSubset_embeddedResolution hadm
  rw [← hGq, hk] at hs
  obtain ⟨hs1, hs2, hs3⟩ := hs
  have := flat_of_isLocalIso q
  have H := Kollar.isPullback_pullback_toBase_of_flat G q
  have : IsLocalIso (G.pullbackHom q) := MorphismProperty.of_isPullback H ‹_›
  have : Surjective (G.pullbackHom q) := MorphismProperty.of_isPullback H ‹_›
  have hw : (G.pullback q).toBase ≫ q ≫ sX = G.pullbackHom q ≫ G.toBase ≫ sX := by
    rw [← Category.assoc, H.w, Category.assoc]
  refine ⟨?_, ?_, ?_⟩
  · rw [hw] at hs1
    exact isSmoothScheme_of_isLocalIso _ _ hs1
  · rw [smoothLocus_comp_of_isLocalIso] at hs2
    exact isIso_morphismRestrict_of_isPullback H (smoothLocus sX) hs2
  · have hset : (G.pullback q).toBase ⁻¹' (q ⁻¹' (singularLocus sX : Set X)) =
        G.pullbackHom q ⁻¹' (G.toBase ⁻¹' (singularLocus sX : Set X)) := by
      ext z
      change q ((G.pullback q).toBase z) ∈ (singularLocus sX : Set X) ↔
        G.toBase (G.pullbackHom q z) ∈ (singularLocus sX : Set X)
      rw [← Scheme.Hom.comp_apply, H.w, Scheme.Hom.comp_apply]
    rw [hw, coe_singularLocus_comp_of_isLocalIso, hset] at hs3
    have : LocallyOfFiniteType sX := hX.1
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    have : LocallyOfFiniteType G.toBase := (isProper_toBase G).toLocallyOfFiniteType
    have : IsAffine X' := hadm.2.1
    have : LocallyOfFiniteType (q ≫ sX) := hk ▸ hadm.2.2.1.1
    have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (q ≫ sX)
    have := isProper_toBase (G.pullback q)
    have : QuasiCompact (G.pullback q).toBase := inferInstance
    have : CompactSpace (G.pullback q).target :=
      QuasiCompact.compactSpace_of_compactSpace (G.pullback q).toBase
    exact isSNCClosedSubset_of_isLocalIso (G.pullbackHom q) (G.toBase ≫ sX)
      ((singularLocus sX).isClosed.preimage G.toBase.continuous) hs3

/-- **Field change of a glued sequence.** If `G` is glued for `X` over `K`, then its pull-back to
`X_{L,σ}` is glued for `X_{L,σ}` over `L`: the field change of `X' ⊆ A'` is an admissible
embedding of `X'_{L,σ}`, whose embedded resolution is the field change of `𝓑𝓡_{A'}(X')`. -/
private theorem isGluedResolution_fieldChange {K : Type u} [Field K] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of K)} {G : ClosedBlowupSequence X} (hG : IsGluedResolution sX G)
    (L : Type u) [Field L] (σ : K →+* L)
    (hXL : IsDisjointUnionOfVarieties (pullback.snd sX (Spec.map (CommRingCat.ofHom σ)))) :
    IsGluedResolution (pullback.snd sX (Spec.map (CommRingCat.ofHom σ)))
      (G.pullback (pullback.fst sX (Spec.map (CommRingCat.ofHom σ)))) := by
  obtain ⟨X', A', q, sA', i', hql, hqs, hadm, hk, hGq⟩ := hG
  have : IsAffine X' := hadm.2.1
  set s' := Spec.map (CommRingCat.ofHom σ)
  let qL : pullback (i' ≫ sA') s' ⟶ pullback sX s' :=
    pullback.map (i' ≫ sA') s' sX s' q (𝟙 _) (𝟙 _) (by rw [hk, Category.comp_id]) (by simp)
  have hsnd : qL ≫ pullback.snd sX s' = pullback.snd (i' ≫ sA') s' := by simp [qL]
  have hsq : IsPullback qL (pullback.fst (i' ≫ sA') s') (pullback.fst sX s') q := by
    refine IsPullback.of_right ?_ (by simp [qL]) (IsPullback.of_hasPullback sX s').flip
    rw [hsnd, ← hk]
    exact (IsPullback.of_hasPullback (i' ≫ sA') s').flip
  have : IsLocalIso qL := MorphismProperty.of_isPullback hsq.flip ‹_›
  have : Surjective qL := MorphismProperty.of_isPullback hsq.flip ‹_›
  have hXL' : IsDisjointUnionOfVarieties (pullback.snd (i' ≫ sA') s') :=
    hsnd ▸ isDisjointUnionOfVarieties_comp_of_isLocalIso hXL qL
  obtain ⟨hadmL, hEq⟩ :=
    isAdmissibleEmbedding_fieldChange_and_embeddedResolution_eq σ sA' i' hadm hXL'
  refine ⟨_, _, qL, _, _, ‹_›, ‹_›, hadmL, by simp [qL, s'], ?_⟩
  rw [hEq, ← hGq, pullback_pullback, pullback_pullback, hsq.w]

end Properties

/-! ### The functor `𝓑𝓡` -/

open Classical in
/-- `𝓑𝓡(X)`: the glued blow-up sequence of `X`, when there is one (always, in characteristic
`0`), and the empty sequence otherwise. -/
private noncomputable def gluedResolution {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) : ClosedBlowupSequence X :=
  if h : ∃ G, IsGluedResolution sX G then h.choose else .nil X

private theorem gluedResolution_eq_of_isGluedResolution {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (hX : IsDisjointUnionOfVarieties sX) {G : ClosedBlowupSequence X}
    (hG : IsGluedResolution sX G) : gluedResolution sX = G := by
  have h : ∃ G, IsGluedResolution sX G := ⟨G, hG⟩
  rw [gluedResolution, dite_cond_eq_true (eq_true h)]
  exact eq_of_isGluedResolution hX hG h.choose_spec

private theorem isGluedResolution_gluedResolution {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} (hX : IsDisjointUnionOfVarieties sX) :
    IsGluedResolution sX (gluedResolution sX) := by
  obtain ⟨G, hG⟩ := exists_isGluedResolution hX
  rwa [gluedResolution_eq_of_isGluedResolution hX hG]

end Proof_thm_kr3f_strong_resolution

namespace MMP.Resolution

open Proof_thm_kr3f_strong_resolution

/-- **Resolution of singularities, III** (Kollár Thm. 3.36). There is a blow-up sequence functor
`𝓑𝓡`, assigning to every disjoint union of varieties `X` over a field `k` a blow-up sequence
`𝓑𝓡(X) : X_r → ⋯ → X_0 = X` with composite `Π`, such that, when `k` has characteristic `0`,
1. `X_r` is smooth over `k`;
2. `Π` is an isomorphism over the smooth locus `X^ns`;
3. `Π⁻¹(Sing X)` is a divisor with simple normal crossings on `X_r`;
4. for every smooth morphism `h : Y → X` of constant relative dimension with `Y` a disjoint union
   of varieties over `k`, `𝓑𝓡(Y) = (h^*𝓑𝓡(X))^red`, and `𝓑𝓡(Y) = h^*𝓑𝓡(X)` if `h` is
   surjective; and for every field extension `σ : K → L` with `X_{L,σ}` a disjoint union of
   varieties over `L`, `𝓑𝓡(X_{L,σ}) = 𝓑𝓡(X)_{L,σ}`, the pull-back along `X_{L,σ} → X`. -/
@[mmp "thm_kr3f_strong_resolution"]
public theorem exists_strongResolution_blowupSequenceFunctor :
    ∃ BR : ∀ {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)),
        IsDisjointUnionOfVarieties sX → ClosedBlowupSequence X,
      (∀ {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
          (hX : IsDisjointUnionOfVarieties sX),
        IsSmoothScheme ((BR sX hX).toBase ≫ sX) ∧
        IsIso ((BR sX hX).toBase ∣_ smoothLocus sX) ∧
        IsSNCClosedSubset ((BR sX hX).toBase ≫ sX)
          ((BR sX hX).toBase ⁻¹' (singularLocus sX : Set X))) ∧
      (∀ {k : Type u} [Field k] [CharZero k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
          (hX : IsDisjointUnionOfVarieties sX) (h : Y ⟶ X) (n : ℕ)
          [SmoothOfRelativeDimension n h] (hY : IsDisjointUnionOfVarieties (h ≫ sX)),
        BR (h ≫ sX) hY = ((BR sX hX).pullback h).reduction ∧
          (Surjective h → BR (h ≫ sX) hY = (BR sX hX).pullback h)) ∧
      (∀ {K : Type u} [Field K] [CharZero K] {X : Scheme.{u}} (sX : X ⟶ Spec (.of K))
          (hX : IsDisjointUnionOfVarieties sX) (L : Type u) [Field L] (σ : K →+* L)
          (hXL : IsDisjointUnionOfVarieties
            (Limits.pullback.snd sX (Spec.map (CommRingCat.ofHom σ)))),
        BR (Limits.pullback.snd sX (Spec.map (CommRingCat.ofHom σ))) hXL =
          (BR sX hX).pullback (Limits.pullback.fst sX (Spec.map (CommRingCat.ofHom σ)))) := by
  refine ⟨fun sX _ ↦ gluedResolution sX, ?_, ?_, ?_⟩
  · intro k _ _ X sX hX
    exact isSmoothScheme_and_isIso_and_isSNCClosedSubset_of_isGluedResolution hX
      (isGluedResolution_gluedResolution hX)
  · intro k _ _ X Y sX hX h n _ hY
    have hG := isGluedResolution_gluedResolution hX
    have e := eq_reduction_pullback_of_isGluedResolution hX h n hY hG
      (isGluedResolution_gluedResolution hY)
    refine ⟨e, fun hs ↦ ?_⟩
    have := hs
    have := SmoothOfRelativeDimension.smooth n h
    change gluedResolution (h ≫ sX) = (gluedResolution sX).pullback h
    rw [e]
    exact ClosedBlowupSequence.reduction_eq_self (ClosedBlowupSequence.hasNoEmptyBlowups_pullback _
      (hasNoEmptyBlowups_of_isGluedResolution hG) h)
  · intro K _ _ X sX hX L _ σ hXL
    exact gluedResolution_eq_of_isGluedResolution hXL
      (isGluedResolution_fieldChange (isGluedResolution_gluedResolution hX) L σ hXL)

end MMP.Resolution
