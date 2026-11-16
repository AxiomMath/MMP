module

public import MMP.AlgebraicGeometry.Resolution.Principalization.CanonicalFunctor
public import MMP.AlgebraicGeometry.Resolution.Principalization.BlowupSequencePushforward
public import MMP.AlgebraicGeometry.AffineSpace.StableEmbeddings
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence.FlatBaseChange
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.MonomialPart
public import MMP.AlgebraicGeometry.Resolution.MaximalContact.DerivativeIdealTransform
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence.FlatDescent

/-!
# Embedded resolution `𝓑𝓡`: independence of the embedding, smooth pull-back and gluing

For an affine disjoint union of varieties `X` over a field `k` of characteristic `0` and an
admissible embedding `X ⊆ A`, the blow-up sequence `𝓑𝓡_A(X) = (𝓑𝓡_𝐁(X ⊆ A))^red`,
`𝐁 = 𝓑𝓟^can(A, I_X, ∅)`, is the embedded resolution of `X` (Kollár, *Lectures on resolution of
singularities*, pp. 146–147). This file proves that it does not depend on the admissible
embedding, that it commutes with smooth base change of the ambient space, with principal open
covers and with smooth morphisms of constant relative dimension, and that the embedded
resolutions of a finite affine open cover glue to a unique blow-up sequence of `X`.

## Main results

* `MMP.Resolution.embeddedResolution_eq_of_isAdmissibleEmbedding`: `𝓑𝓡_A(X) = 𝓑𝓡_{A'}(X)` for
  two admissible embeddings of the same `k`-scheme `X`.
* `MMP.Resolution.embeddedResolution_pullback_snd_eq_reduction_pullback`: for a smooth
  `h_A : A' ⟶ A`, `𝓑𝓡_{A'}(X ×_A A') = (h^* 𝓑𝓡_A(X))^red`.
* `MMP.Resolution.embeddedResolution_sigmaBasicOpen_eq_pullback`: for `g_α` generating the unit
  ideal, `𝓑𝓡_{A'}(∐ D_X(g_α)) = q^* 𝓑𝓡_A(X)` (Kollár 3.34).
* `MMP.Resolution.embeddedResolution_eq_reduction_pullback_of_smoothOfRelativeDimension`: for a
  smooth `k`-morphism `h : Y ⟶ X` of constant relative dimension, `𝓑𝓡(Y) = (h^* 𝓑𝓡(X))^red`.
* `MMP.Resolution.existsUnique_pullback_sigmaDesc_eq_embeddedResolution`: for a finite affine
  open cover `U` of `X`, there is a unique blow-up sequence `G` of `X` with
  `q^* G = 𝓑𝓡_{A'}(∐ U_α)` (Kollár Prop. 3.37).

## Implementation notes

Each result's auxiliary lemmas live in a namespace `Proof_<tag>` named after its label,
opened for that result and for the later results that reuse them. Pull-back of a blow-up sequence is
`MMP.Resolution.ClosedBlowupSequence.pullback` and the deletion of empty blow-ups is
`MMP.Resolution.ClosedBlowupSequence.reduction`; characteristic `0`, affineness, smoothness and
equidimensionality of the ambient space are part of `MMP.Resolution.IsAdmissibleEmbedding`.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.34, 3.37, 3.39, 3.41, pp. 146–147]
-/

@[expose] public section

namespace Proof_lem_kr3f_embedded_resolution_independent_of_embedding

open CategoryTheory AlgebraicGeometry MMP.Resolution

universe u

/-- Affine space of finite rank over a field is a smooth `k`-scheme. -/
private theorem isSmoothScheme_affineSpace {k : Type u} [Field k] (n : Type u) [Finite n] :
    MMP.Mori.IsSmoothScheme (𝔸(n; Spec (.of k)) ↘ Spec (.of k)) :=
  (MMP.Mori.isSmoothScheme_iff _).mpr (AlgebraicGeometry.smooth_affineSpace_over n _)

/-- An affine scheme of finite type over an affine scheme `S` admits a closed embedding over `S`
into an affine space of finite rank over `S`. -/
private theorem exists_isClosedImmersion_affineSpace_over {S A : Scheme.{u}}
    [IsAffine S] [IsAffine A] (sA : A ⟶ S) [LocallyOfFiniteType sA] :
    ∃ (n : Type u) (_ : Finite n) (j : A ⟶ 𝔸(n; S)),
      IsClosedImmersion j ∧ j ≫ 𝔸(n; S) ↘ S = sA := by
  have hft : RingHom.FiniteType sA.appTop.hom :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
  letI := sA.appTop.hom.toAlgebra
  obtain ⟨s, hs⟩ := hft.out
  refine ⟨s, inferInstance, AffineSpace.homOfVector sA (fun x => x.1), ?_,
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

section Coordinate

variable {R : CommRingCat.{u}} {X : Scheme.{u}} {ι κ : Type u}

private lemma comp_appTop_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : Γ(Z, ⊤)) :
    (f ≫ g).appTop x = f.appTop (g.appTop x) := rfl

/-- `MMP.Resolution.Kollar.embedFst` is `i₁` followed by the coordinate inclusion
`x ↦ (x, 0)`. -/
private theorem embedFst_eq_comp (sX : X ⟶ Spec R) (i₁ : X ⟶ 𝔸(ι; Spec R))
    (h : i₁ ≫ 𝔸(ι; Spec R) ↘ Spec R = sX) :
    Kollar.embedFst (κ := κ) sX i₁ = i₁ ≫ Kollar.embedFst (𝔸(ι; Spec R) ↘ Spec R) (𝟙 _) := by
  apply AffineSpace.hom_ext
  · simp [Kollar.embedFst, AffineSpace.homOfVector_over, h]
  · rintro (i | i)
    · rw [comp_appTop_apply]
      simp only [Kollar.embedFst, AffineSpace.homOfVector_appTop_coord, Sum.elim_inl]
      rfl
    · rw [comp_appTop_apply]
      simp only [Kollar.embedFst, AffineSpace.homOfVector_appTop_coord, Sum.elim_inr,
        Pi.zero_apply, map_zero]

/-- `MMP.Resolution.Kollar.embedSnd` is `i₂` followed by the coordinate inclusion
`y ↦ (0, y)`. -/
private theorem embedSnd_eq_comp (sX : X ⟶ Spec R) (i₂ : X ⟶ 𝔸(κ; Spec R))
    (h : i₂ ≫ 𝔸(κ; Spec R) ↘ Spec R = sX) :
    Kollar.embedSnd (ι := ι) sX i₂ = i₂ ≫ Kollar.embedSnd (𝔸(κ; Spec R) ↘ Spec R) (𝟙 _) := by
  apply AffineSpace.hom_ext
  · simp [Kollar.embedSnd, AffineSpace.homOfVector_over, h]
  · rintro (i | i)
    · rw [comp_appTop_apply]
      simp only [Kollar.embedSnd, AffineSpace.homOfVector_appTop_coord, Sum.elim_inl,
        Pi.zero_apply, map_zero]
    · rw [comp_appTop_apply]
      simp only [Kollar.embedSnd, AffineSpace.homOfVector_appTop_coord, Sum.elim_inr]
      rfl

/-- The coordinate inclusion `𝔸(ι) → 𝔸(ι ⊕ κ)`, `x ↦ (x, 0)`, is a closed immersion. -/
private theorem isClosedImmersion_embedFst_id :
    IsClosedImmersion (Kollar.embedFst (κ := κ) (𝔸(ι; Spec R) ↘ Spec R) (𝟙 _)) := by
  refine Stacks.AlgebraicGeometry.RelativeProjSeparated.isClosedImmersion_of_section
    (AffineSpace.reindex Sum.inl (Spec R)) _ ?_
  apply AffineSpace.hom_ext
  · simp [Kollar.embedFst, AffineSpace.homOfVector_over, AffineSpace.reindex_over]
  · intro i
    rw [comp_appTop_apply, AffineSpace.reindex_appTop_coord]
    simp only [Kollar.embedFst, AffineSpace.homOfVector_appTop_coord, Sum.elim_inl]

/-- The coordinate inclusion `𝔸(κ) → 𝔸(ι ⊕ κ)`, `y ↦ (0, y)`, is a closed immersion. -/
private theorem isClosedImmersion_embedSnd_id :
    IsClosedImmersion (Kollar.embedSnd (ι := ι) (𝔸(κ; Spec R) ↘ Spec R) (𝟙 _)) := by
  refine Stacks.AlgebraicGeometry.RelativeProjSeparated.isClosedImmersion_of_section
    (AffineSpace.reindex Sum.inr (Spec R)) _ ?_
  apply AffineSpace.hom_ext
  · simp [Kollar.embedSnd, AffineSpace.homOfVector_over, AffineSpace.reindex_over]
  · intro i
    rw [comp_appTop_apply, AffineSpace.reindex_appTop_coord]
    simp only [Kollar.embedSnd, AffineSpace.homOfVector_appTop_coord, Sum.elim_inr]

end Coordinate

variable {k : Type u} [Field k]

/-- An admissible embedding `X ⊆ A` followed by a closed embedding `j : A ↪ A'` over `k` into an
irreducible affine smooth `k`-scheme is admissible: the chain `i(W) ⊊ Y₁ ⊊ Y₂` of irreducible
closed subsets of `A` is carried by `j` to one in `A'`. -/
private theorem isAdmissibleEmbedding_comp {X A A' : Scheme.{u}} {sA : A ⟶ Spec (.of k)}
    {sA' : A' ⟶ Spec (.of k)} {i : X ⟶ A} (h : IsAdmissibleEmbedding sA i) (j : A ⟶ A')
    [IsClosedImmersion j] (hj : j ≫ sA' = sA) [IsAffine A'] (hsm : MMP.Mori.IsSmoothScheme sA')
    [IrreducibleSpace A'] : IsAdmissibleEmbedding sA' (i ≫ j) := by
  obtain ⟨hchar, hXa, hdu, hci, -, -, -, hcod⟩ := h
  refine ⟨hchar, hXa, by rwa [Category.assoc, hj], ?_, ‹_›, hsm,
    TopologicalSpace.Equidimensional.of_preirreducibleSpace A', ?_⟩
  · have := hci; infer_instance
  · intro W hW T hT _
    obtain ⟨T₀, hT₀, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
      (i.base '' W) ((hW.1).image _ i.base.hom.continuous.continuousOn)
    obtain ⟨Y₁, Y₂, h1, h2, -⟩ := hcod W hW T₀ hT₀ hsub
    have hinj : Function.Injective j.base := j.isClosedEmbedding.injective
    let F : TopologicalSpace.IrreducibleCloseds A → TopologicalSpace.IrreducibleCloseds A' :=
      fun Y => ⟨j.base '' Y, Y.isIrreducible.image _ j.base.hom.continuous.continuousOn,
        j.isClosedEmbedding.isClosedMap _ Y.isClosed⟩
    refine ⟨F Y₁, F Y₂, ?_, ?_, ?_⟩
    · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp]
      exact hinj.image_strictMono h1
    · exact hinj.image_strictMono h2
    · intro x _
      exact hT.2 (IrreducibleSpace.isIrreducible_univ A') (Set.subset_univ T) (Set.mem_univ x)

/-- `𝓑𝓟^can` of the triple `(A, I, E)` over `k` depends only on `I`, `E` and the structure
morphism, up to equality. -/
private theorem canonicalPrincipalization_congr {A : Scheme.{u}} (I : A.IdealSheafData)
    {E E' : OrderedDivisor A} {s s' : A ⟶ Spec (.of k)} (hE : E = E') (hs : s = s')
    (h₁ : (⟨⟨A, I, E⟩, k, s⟩ : FieldBlowupTriple.{u}) ∈ sncTriples)
    (h₂ : (⟨⟨A, I, E'⟩, k, s'⟩ : FieldBlowupTriple.{u}) ∈ sncTriples) :
    canonicalPrincipalization ⟨⟨A, I, E⟩, k, s⟩ h₁ =
      canonicalPrincipalization ⟨⟨A, I, E'⟩, k, s'⟩ h₂ := by
  subst hE hs; rfl

/-- **Step 1.** For an admissible embedding `X ⊆ A` and a closed embedding `j : A ↪ A'` over `k`
such that `X ⊆ A'` is admissible, `𝓑𝓡_{A'}(X) = 𝓑𝓡_A(X)`. -/
private theorem embeddedResolution_comp_eq {X A A' : Scheme.{u}} {sA : A ⟶ Spec (.of k)}
    {sA' : A' ⟶ Spec (.of k)} {i : X ⟶ A} (j : A ⟶ A') [hjc : IsClosedImmersion j]
    (hj : j ≫ sA' = sA) (h : IsAdmissibleEmbedding sA i)
    (h' : IsAdmissibleEmbedding sA' (i ≫ j)) :
    embeddedResolution sA' (i ≫ j) = embeddedResolution sA i := by
  have hs := embeddingTriple_mem_sncTriples h
  have hs' := embeddingTriple_mem_sncTriples h'
  have ht : embeddingTriple sA i ∈ triples := mem_triples_iff.2 ⟨hs, h.2.2.2.2.2.2.1⟩
  have ht' : embeddingTriple sA' (i ≫ j) ∈ triples :=
    mem_triples_iff.2 ⟨hs', h'.2.2.2.2.2.2.1⟩
  have : IsClosedImmersion i := h.2.2.2.1
  have : LocallyOfFiniteType sA' := hs'.2.2.1
  have : QuasiCompact sA' := hs'.2.2.2.1
  let d : ClosedEmbeddingData.{u} :=
    { k := k, X := A', sX := sA', Y := A, j := j, isClosedImmersion := hjc, IX := (i ≫ j).ker,
      IY := i.ker, E := OrderedDivisor.empty A', IX_eq := Scheme.Hom.ker_comp i j }
  have hE : (OrderedDivisor.empty A').comap j = OrderedDivisor.empty A := by
    simp only [OrderedDivisor.comap, OrderedDivisor.empty]
    congr 1
    funext x
    exact x.elim0
  have hX : d.ambientTriple ∈ triples := ht'
  have hY : d.embeddedTriple ∈ triples := by
    change (⟨⟨A, i.ker, (OrderedDivisor.empty A').comap j⟩, k, j ≫ sA'⟩ : FieldBlowupTriple.{u})
      ∈ triples
    rw [hE, hj]
    exact ht
  have hP := (canonicalPrincipalization_properties.{u, u, u}).2.2.2.2.2.2 d rfl hX hY
  have hdu : IsDisjointUnionOfVarieties (i ≫ j ≫ sA') := by rw [hj]; exact h.2.2.1
  have key := Kollar.embeddedResolutionSequence_comp_eq_of_isPushforward sA' j i hdu _ _ hP
  unfold embeddedResolution
  rw [dif_pos hs', dif_pos hs]
  congr 1
  refine key.trans ?_
  congr 1
  exact canonicalPrincipalization_congr i.ker hE hj _ _

end Proof_lem_kr3f_embedded_resolution_independent_of_embedding

namespace MMP.Resolution

open CategoryTheory AlgebraicGeometry
open Proof_lem_kr3f_embedded_resolution_independent_of_embedding

universe u

/-- **`𝓑𝓡_A(X)` is independent of the embedding** (Kollár p. 146): if `i : X ⟶ A` and
`i' : X ⟶ A'` are two admissible embeddings (`IsAdmissibleEmbedding`) of the same affine disjoint
union of varieties `X` over a field `k` of characteristic `0` (i.e. `i ≫ sA = i' ≫ sA'`), then
`embeddedResolution sA i = embeddedResolution sA' i'`. -/
@[mmp "lem_kr3f_embedded_resolution_independent_of_embedding"]
public theorem embeddedResolution_eq_of_isAdmissibleEmbedding {k : Type u} [Field k]
    {X A A' : Scheme.{u}} {sA : A ⟶ Spec (.of k)} {sA' : A' ⟶ Spec (.of k)}
    {i : X ⟶ A} {i' : X ⟶ A'} (h : IsAdmissibleEmbedding sA i)
    (h' : IsAdmissibleEmbedding sA' i') (hk : i ≫ sA = i' ≫ sA') :
    embeddedResolution sA i = embeddedResolution sA' i' := by
  have hs := embeddingTriple_mem_sncTriples h
  have hs' := embeddingTriple_mem_sncTriples h'
  have : IsAffine A := h.2.2.2.2.1
  have : IsAffine A' := h'.2.2.2.2.1
  have : IsAffine X := h.2.1
  have : LocallyOfFiniteType sA := hs.2.2.1
  have : LocallyOfFiniteType sA' := hs'.2.2.1
  have : IsClosedImmersion i := h.2.2.2.1
  have : IsClosedImmersion i' := h'.2.2.2.1
  obtain ⟨n, _, j, hjc, hj⟩ := exists_isClosedImmersion_affineSpace_over sA
  obtain ⟨m, _, j', hjc', hj'⟩ := exists_isClosedImmersion_affineSpace_over sA'
  have h₁ := isAdmissibleEmbedding_comp h j hj (isSmoothScheme_affineSpace n)
  have h₂ := isAdmissibleEmbedding_comp h' j' hj' (isSmoothScheme_affineSpace m)
  let c₁ := Kollar.embedFst (κ := m) (𝔸(n; Spec (.of k)) ↘ Spec (.of k)) (𝟙 _)
  let c₂ := Kollar.embedSnd (ι := n) (𝔸(m; Spec (.of k)) ↘ Spec (.of k)) (𝟙 _)
  have : IsClosedImmersion c₁ := isClosedImmersion_embedFst_id
  have : IsClosedImmersion c₂ := isClosedImmersion_embedSnd_id
  have hc₁ : c₁ ≫ 𝔸(n ⊕ m; Spec (.of k)) ↘ Spec (.of k) = 𝔸(n; Spec (.of k)) ↘ Spec (.of k) :=
    AffineSpace.homOfVector_over _ _
  have hc₂ : c₂ ≫ 𝔸(n ⊕ m; Spec (.of k)) ↘ Spec (.of k) = 𝔸(m; Spec (.of k)) ↘ Spec (.of k) :=
    AffineSpace.homOfVector_over _ _
  have h₁' := isAdmissibleEmbedding_comp h₁ c₁ hc₁ (isSmoothScheme_affineSpace _)
  have h₂' := isAdmissibleEmbedding_comp h₂ c₂ hc₂ (isSmoothScheme_affineSpace _)
  have hX₁ : (i ≫ j) ≫ 𝔸(n; Spec (.of k)) ↘ Spec (.of k) = i ≫ sA := by
    rw [Category.assoc, hj]
  have hX₂ : (i' ≫ j') ≫ 𝔸(m; Spec (.of k)) ↘ Spec (.of k) = i ≫ sA := by
    rw [Category.assoc, hj', hk]
  obtain ⟨φ, hφ, hφe⟩ := Kollar.exists_iso_affineSpace_comp_eq (R := CommRingCat.of k)
    (sX := i ≫ sA) (i ≫ j) (i' ≫ j') hX₁ hX₂
  rw [embedFst_eq_comp _ _ hX₁, embedSnd_eq_comp _ _ hX₂] at hφe
  have hφa := isAdmissibleEmbedding_comp h₁' φ.hom hφ (isSmoothScheme_affineSpace _)
  calc embeddedResolution sA i
      = embeddedResolution _ (i ≫ j) := (embeddedResolution_comp_eq j hj h h₁).symm
    _ = embeddedResolution _ ((i ≫ j) ≫ c₁) := (embeddedResolution_comp_eq c₁ hc₁ h₁ h₁').symm
    _ = embeddedResolution _ (((i ≫ j) ≫ c₁) ≫ φ.hom) :=
        (embeddedResolution_comp_eq φ.hom hφ h₁' hφa).symm
    _ = embeddedResolution _ ((i' ≫ j') ≫ c₂) := by rw [hφe]
    _ = embeddedResolution _ (i' ≫ j') := embeddedResolution_comp_eq c₂ hc₂ h₂ h₂'
    _ = embeddedResolution sA' i' := embeddedResolution_comp_eq j' hj' h' h₂

end MMP.Resolution

namespace Proof_lem_kr3f_br_open_cover

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MMP.Resolution
open MMP.Resolution.ClosedBlowupSequence

universe u

/-! ### Topology of irreducible components -/

/-- If every point has an irreducible open neighbourhood, distinct irreducible components are
disjoint. -/
private theorem disjoint_of_forall_exists_isIrreducible {T : Type*} [TopologicalSpace T]
    (hT : ∀ x : T, ∃ U : Set T, IsOpen U ∧ x ∈ U ∧ IsIrreducible U) :
    ∀ C ∈ irreducibleComponents T, ∀ C' ∈ irreducibleComponents T, C ≠ C' → Disjoint C C' := by
  intro C hC C' hC' hne
  refine Set.disjoint_left.2 fun y hyC hyC' => hne ?_
  obtain ⟨U, hU, hyU, hUi⟩ := hT y
  have key : ∀ D ∈ irreducibleComponents T, y ∈ D → D = closure U := fun D hD hyD => by
    have h2 : D ⊆ closure U :=
      (subset_closure_inter_of_isPreirreducible_of_isOpen hD.1.2 hU ⟨y, hyD, hyU⟩).trans
        (closure_mono Set.inter_subset_right)
    exact ((hD.2 hUi.closure h2).antisymm h2).symm
  rw [key C hC hyC, key C' hC' hyC']

/-- In a noetherian space with pairwise disjoint irreducible components every point has an
irreducible open neighbourhood. -/
private theorem exists_isIrreducible_of_disjoint {T : Type*} [TopologicalSpace T]
    [NoetherianSpace T]
    (hT : ∀ C ∈ irreducibleComponents T, ∀ C' ∈ irreducibleComponents T, C ≠ C' → Disjoint C C')
    (x : T) : ∃ U : Set T, IsOpen U ∧ x ∈ U ∧ IsIrreducible U := by
  set C := irreducibleComponent x
  have hC := irreducibleComponent_mem_irreducibleComponents x
  set U := (⋃ D ∈ {D | D ∈ irreducibleComponents T ∧ D ≠ C}, D)ᶜ
  have hUo : IsOpen U :=
    (Set.Finite.isClosed_biUnion (NoetherianSpace.finite_irreducibleComponents.subset
      fun D hD => hD.1) fun D hD => isClosed_of_mem_irreducibleComponents D hD.1).isOpen_compl
  have hmem : ∀ y, y ∈ U ↔ ∀ D ∈ irreducibleComponents T, D ≠ C → y ∉ D := by
    intro y; simp [U]
  have hxU : x ∈ U := (hmem x).2 fun D hD hDC hxD =>
    Set.disjoint_left.1 (hT D hD C hC hDC) hxD mem_irreducibleComponent
  have hUC : U ⊆ C := fun y hy => by
    by_contra hyC
    refine (hmem y).1 hy _ (irreducibleComponent_mem_irreducibleComponents y) ?_
      mem_irreducibleComponent
    rintro h
    exact hyC (h ▸ mem_irreducibleComponent)
  exact ⟨U, hUo, hxU, ⟨x, hxU⟩, hC.1.2.open_subset hUo hUC⟩

/-! ### Blow-up sequences -/

/-- Deleting empty blow-ups commutes with pull-back along a flat surjective morphism. -/
private theorem reduction_pullback_eq_pullback_reduction {X Y : Scheme.{u}}
    (S : ClosedBlowupSequence X) (f : Y ⟶ X) [Flat f] [Surjective f] :
    (S.pullback f).reduction = S.reduction.pullback f := by
  rw [← reduction_pullback_reduction,
    reduction_eq_self (hasNoEmptyBlowups_pullback _ (hasNoEmptyBlowups_reduction S) f)]

/-! ### Dimension -/

/-- The dimension of an irreducible component of a scheme locally of finite type over a field is
the local dimension at its generic point. -/
private theorem topologicalKrullDim_eq_topologicalKrullDimAt_genericPoint {k : Type u} [Field k]
    {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s] {Z : Set Y}
    (hZ : Z ∈ irreducibleComponents Y) :
    topologicalKrullDim Z = topologicalKrullDimAt Y hZ.1.genericPoint := by
  have hη := hZ.1.closure_genericPoint (isClosed_of_mem_irreducibleComponents Z hZ)
  have hηZ : hZ.1.genericPoint ∈ Z := hη.le (subset_closure rfl)
  rw [topologicalKrullDimAt_eq_iSup_irreducibleComponents k Y s]
  refine le_antisymm
    (le_iSup₂ (f := fun Z' (_ : Z' ∈ {Z' | Z' ∈ irreducibleComponents Y ∧
      hZ.1.genericPoint ∈ Z'}) => topologicalKrullDim Z') Z ⟨hZ, hηZ⟩) (iSup₂_le fun Z' hZ' => ?_)
  have hle : Z ⊆ Z' := by
    rw [← hη]
    exact (isClosed_of_mem_irreducibleComponents Z' hZ'.1).closure_subset_iff.2
      (Set.singleton_subset_iff.2 hZ'.2)
  rw [(hZ.2 hZ'.1.1 hle).antisymm hle]

/-- In an equidimensional scheme locally of finite type over a field, the local dimension at
every point is the dimension of every irreducible component. -/
private theorem topologicalKrullDimAt_eq_of_mem_irreducibleComponents {k : Type u} [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (hX : TopologicalSpace.Equidimensional X) (x : X) {C : Set X}
    (hC : C ∈ irreducibleComponents X) : topologicalKrullDimAt X x = topologicalKrullDim C := by
  rw [topologicalKrullDimAt_eq_iSup_irreducibleComponents k X s x]
  refine le_antisymm (iSup₂_le fun D hD => (hX D hD.1 C hC).le) ?_
  exact (hX _ (irreducibleComponent_mem_irreducibleComponents x) C hC).symm.le.trans
    (le_iSup₂ (f := fun D (_ : D ∈ {D | D ∈ irreducibleComponents X ∧ x ∈ D}) =>
      topologicalKrullDim D) _ ⟨irreducibleComponent_mem_irreducibleComponents x,
        mem_irreducibleComponent⟩)

/-! ### Codimension under flat base change -/

/-- If the local ring at `a` is a domain, every generalization of `a` lies on every irreducible
component through `a`: the generalizations of `a` are the image of the irreducible space
`Spec 𝒪_{Y,a}`. -/
private theorem mem_of_specializes_of_isDomain {Y : Scheme.{u}} {a : Y}
    [IsDomain (Y.presheaf.stalk a)] {T : Set Y} (hT : T ∈ irreducibleComponents Y) (ha : a ∈ T)
    {y : Y} (hy : y ⤳ a) : y ∈ T := by
  have hTc := isClosed_of_mem_irreducibleComponents T hT
  have hξ : closure {hT.1.genericPoint} = T := IsIrreducible.closure_genericPoint hT.1 hTc
  have hξa : hT.1.genericPoint ⤳ a := specializes_iff_mem_closure.mpr (by rw [hξ]; exact ha)
  obtain ⟨p, hp⟩ : hT.1.genericPoint ∈ Set.range (Y.fromSpecStalk a) := by
    rw [Scheme.range_fromSpecStalk]; exact hξa
  obtain ⟨q, hq⟩ : y ∈ Set.range (Y.fromSpecStalk a) := by
    rw [Scheme.range_fromSpecStalk]; exact hy
  haveI : IrreducibleSpace (Spec (Y.presheaf.stalk a)) :=
    inferInstanceAs (IrreducibleSpace (PrimeSpectrum (Y.presheaf.stalk a)))
  have hg : ∀ z, genericPoint (Spec (Y.presheaf.stalk a)) ⤳ z := fun z =>
    (genericPoint_spec _).specializes (Set.mem_univ z)
  have h1 := (hg p).map (Y.fromSpecStalk a).continuous
  have h2 := (hg q).map (Y.fromSpecStalk a).continuous
  rw [hp] at h1
  rw [hq] at h2
  have hsub : T ⊆ closure {Y.fromSpecStalk a (genericPoint (Spec (Y.presheaf.stalk a)))} :=
    hξ ▸ h1.closure_subset
  exact hT.2 isIrreducible_singleton.closure hsub (specializes_iff_mem_closure.mp h2)

/-- A flat morphism maps the generic point of an irreducible component of the source to the
generic point of an irreducible component of the target: a generalization of `f w` lifts, by
going-down, to a generalization of `w`, which is `w` itself. -/
private theorem closure_apply_genericPoint_mem_irreducibleComponents {X X' : Scheme.{u}}
    (f : X' ⟶ X) [Flat f] {W : Set X'} (hW : W ∈ irreducibleComponents X') :
    closure {f hW.1.genericPoint} ∈ irreducibleComponents X := by
  have hw := hW.1.closure_genericPoint (isClosed_of_mem_irreducibleComponents W hW)
  obtain ⟨W0, hW0, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
    (isIrreducible_singleton (x := f hW.1.genericPoint)).closure
  have h0 := hW0.1.closure_genericPoint (isClosed_of_mem_irreducibleComponents W0 hW0)
  obtain ⟨w', hw'w, hfw'⟩ := Flat.generalizingMap f
    (specializes_iff_mem_closure.mpr (h0 ▸ hsub (subset_closure rfl)))
  have h2 : closure {w'} ⊆ W := hW.2 isIrreducible_singleton.closure (hw ▸ hw'w.closure_subset)
  have hww' : hW.1.genericPoint ⤳ w' :=
    specializes_iff_mem_closure.mpr (by rw [hw]; exact h2 (subset_closure rfl))
  rw [← (hw'w.antisymm hww').eq, hfw', h0]
  exact hW0

/-- **Codimension `≥ 2` under flat base change.** Let `i' ≫ h_A = f ≫ i` with `i`, `i'` closed
immersions, `f`, `h_A` flat and the local rings of `A'` domains. If every irreducible component of
`X` has codimension `≥ 2` in the components of `A` containing it, the same holds for `X' ⊆ A'`:
the generic point of a component `W` of `X'` maps to that of a component of `X`, and by going-down
along `h_A` a chain `i(W₀) ⊊ Y₁ ⊊ Y₂` lifts to a chain of generalizations in `A'`. -/
private theorem codim_of_flat {X A X' A' : Scheme.{u}} (i : X ⟶ A) [IsClosedImmersion i]
    (hA : A' ⟶ A) [Flat hA] (f : X' ⟶ X) [Flat f] (i' : X' ⟶ A') [IsClosedImmersion i']
    (hsq : i' ≫ hA = f ≫ i) (hdom : ∀ a : A', IsDomain (A'.presheaf.stalk a))
    (hcod : ∀ W ∈ irreducibleComponents X, ∀ T ∈ irreducibleComponents A, i.base '' W ⊆ T →
      ∃ Y₁ Y₂ : IrreducibleCloseds A,
        i.base '' W ⊂ (Y₁ : Set A) ∧ (Y₁ : Set A) ⊂ Y₂ ∧ (Y₂ : Set A) ⊆ T) :
    ∀ W ∈ irreducibleComponents X', ∀ T ∈ irreducibleComponents A', i'.base '' W ⊆ T →
      ∃ Y₁ Y₂ : IrreducibleCloseds A',
        i'.base '' W ⊂ (Y₁ : Set A') ∧ (Y₁ : Set A') ⊂ Y₂ ∧ (Y₂ : Set A') ⊆ T := by
  intro W hW T hT hWT
  have hWc := isClosed_of_mem_irreducibleComponents W hW
  have hw : closure {hW.1.genericPoint} = W := IsIrreducible.closure_genericPoint hW.1 hWc
  set w := hW.1.genericPoint
  have hfw := closure_apply_genericPoint_mem_irreducibleComponents f hW
  obtain ⟨T0, hT0, hsub0⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (i.base '' closure {f w}) (hfw.1.image _ i.base.hom.continuous.continuousOn)
  obtain ⟨Y1, Y2, h1, h2, h3⟩ := hcod _ hfw T0 hT0 hsub0
  have hy1 : closure {Y1.isIrreducible'.genericPoint} = (Y1 : Set A) :=
    IsIrreducible.closure_genericPoint Y1.isIrreducible' Y1.isClosed'
  have hy2 : closure {Y2.isIrreducible'.genericPoint} = (Y2 : Set A) :=
    IsIrreducible.closure_genericPoint Y2.isIrreducible' Y2.isClosed'
  set y1 := Y1.isIrreducible'.genericPoint
  set y2 := Y2.isIrreducible'.genericPoint
  have haW0 : i (f w) ∈ i.base '' closure {f w} := ⟨_, subset_closure rfl, rfl⟩
  have hW0cl : IsClosed (i.base '' closure {f w}) :=
    i.isClosedEmbedding.isClosedMap _ isClosed_closure
  have hy1a : y1 ⤳ i (f w) := specializes_iff_mem_closure.mpr (hy1 ▸ h1.subset haW0)
  have hy2y1 : y2 ⤳ y1 := by
    refine specializes_iff_mem_closure.mpr (hy2 ▸ h2.subset ?_)
    rw [← hy1]; exact subset_closure rfl
  have haL : hA (i' w) = i (f w) := by
    rw [← Scheme.Hom.comp_apply, hsq, Scheme.Hom.comp_apply]
  obtain ⟨y1', hy1'aL, hy1'e⟩ := Flat.generalizingMap hA (show y1 ⤳ hA (i' w) from haL ▸ hy1a)
  obtain ⟨y2', hy2'y1', hy2'e⟩ := Flat.generalizingMap hA (show y2 ⤳ hA y1' from hy1'e ▸ hy2y1)
  have hWsub : i'.base '' W ⊆ closure {i' w} := by
    rw [← hw]
    refine (image_closure_subset_closure_image i'.continuous).trans ?_
    rw [Set.image_singleton]
  refine ⟨⟨closure {y1'}, isIrreducible_singleton.closure, isClosed_closure⟩,
    ⟨closure {y2'}, isIrreducible_singleton.closure, isClosed_closure⟩, ?_, ?_, ?_⟩
  · refine HasSubset.Subset.ssubset_of_not_subset (hWsub.trans hy1'aL.closure_subset)
      fun hc => h1.not_subset ?_
    have hm : y1' ∈ closure {i' w} := hWsub (hc (subset_closure rfl))
    have : i (f w) ⤳ y1 := by
      rw [← haL, ← hy1'e]; exact (specializes_iff_mem_closure.mpr hm).map hA.continuous
    rw [← hy1]
    exact hW0cl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr
      (hW0cl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr haW0)
        (specializes_iff_mem_closure.mp this)))
  · refine HasSubset.Subset.ssubset_of_not_subset hy2'y1'.closure_subset fun hc => h2.not_subset ?_
    have : y1' ⤳ y2' := specializes_iff_mem_closure.mpr (hc (subset_closure rfl))
    have h' : y1 ⤳ y2 := by rw [← hy1'e, ← hy2'e]; exact this.map hA.continuous
    rw [← hy2, ← hy1]
    exact h'.closure_subset
  · have hTc := isClosed_of_mem_irreducibleComponents T hT
    have hwW : w ∈ W := by rw [← hw]; exact subset_closure rfl
    have haLT : i' w ∈ T := hWT ⟨w, hwW, rfl⟩
    haveI := hdom (i' w)
    have : y2' ∈ T := mem_of_specializes_of_isDomain hT haLT (hy2'y1'.trans hy1'aL)
    exact hTc.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr this)

/-- `𝓑𝓟^can` evaluated at equal triples. -/
private theorem canonicalPrincipalization_heq {t₁ t₂ : FieldBlowupTriple.{u}} (e : t₁ = t₂)
    (h₁ : t₁ ∈ sncTriples) (h₂ : t₂ ∈ sncTriples) :
    canonicalPrincipalization t₁ h₁ ≍ canonicalPrincipalization t₂ h₂ := by
  subst e; rfl

attribute [local instance 2000] AlgebraicGeometry.IsNoetherian.toIsLocallyNoetherian

private theorem isNoetherian_of_isDisjointUnionOfVarieties {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} (hX : IsDisjointUnionOfVarieties s) :
    AlgebraicGeometry.IsNoetherian X := by
  obtain ⟨_, _, -⟩ := hX
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  exact { toIsLocallyNoetherian := ‹_›, toCompactSpace := ‹_› }

/-- A finite disjoint union of open subschemes of a disjoint union of varieties is a disjoint
union of varieties, provided it is affine. -/
private theorem isDisjointUnionOfVarieties_sigmaDesc {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (hX : IsDisjointUnionOfVarieties sX) {ι : Type u} [Finite ι]
    (V : ι → X.Opens) [IsAffine (∐ fun α ↦ (V α).toScheme)] :
    IsDisjointUnionOfVarieties (Sigma.desc (fun α ↦ (V α).ι) ≫ sX) := by
  have := isNoetherian_of_isDisjointUnionOfVarieties hX
  obtain ⟨hlft, -, hred, -, hdisj⟩ := hX
  have : IsZariskiLocalAtSource @LocallyOfFiniteType.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFiniteType)
  haveI : LocallyOfFiniteType (Sigma.desc fun α ↦ (V α).ι) :=
    IsZariskiLocalAtSource.sigmaDesc fun α ↦ inferInstance
  refine ⟨inferInstance, inferInstance, ?_, inferInstance, ?_⟩
  · haveI : ∀ α, IsReduced ((sigmaOpenCover fun α ↦ (V α).toScheme).X α) :=
      fun α ↦ inferInstanceAs (IsReduced (V α).toScheme)
    exact IsReduced.of_openCover (X := ∐ fun α ↦ (V α).toScheme)
      (sigmaOpenCover fun α ↦ (V α).toScheme)
  · refine disjoint_of_forall_exists_isIrreducible fun x ↦ ?_
    obtain ⟨⟨α, z⟩, rfl⟩ := (sigmaMk fun α ↦ (V α).toScheme).surjective x
    rw [sigmaMk_mk]
    obtain ⟨U, hU, hzU, hUi⟩ := exists_isIrreducible_of_disjoint hdisj ((V α).ι z)
    refine ⟨Sigma.ι (fun α ↦ (V α).toScheme) α '' ((V α).ι ⁻¹' U),
      (Sigma.ι (fun α ↦ (V α).toScheme) α).isOpenEmbedding.isOpenMap _
        (hU.preimage (V α).ι.continuous), ⟨z, hzU, rfl⟩, ?_⟩
    exact (show IsIrreducible ((V α).ι ⁻¹' U) from
      ⟨⟨z, hzU⟩, hUi.2.preimage (V α).ι.isOpenEmbedding⟩).image _
        (Sigma.ι (fun α ↦ (V α).toScheme) α).continuous.continuousOn

/-! ### Embedded resolution along a cartesian square with smooth ambient morphism -/

/-- **Kollár p. 146, for a cartesian square.** Let `sq : IsPullback j f h_A i` be a cartesian
square with `h_A` smooth, and `X ⊆ A` and `X' ⊆ A'` admissible.
Then `𝓑𝓡_{A'}(X') = (f^*𝓑𝓡_A(X))^red`. -/
private theorem embeddedResolution_eq_reduction_pullback_of_isPullback {k : Type u} [Field k]
    {X A X' A' : Scheme.{u}} {sA : A ⟶ Spec (.of k)} {i : X ⟶ A} {hA : A' ⟶ A} [Smooth hA]
    {f : X' ⟶ X} {j : X' ⟶ A'} (sq : IsPullback j f hA i) (h : IsAdmissibleEmbedding sA i)
    (h' : IsAdmissibleEmbedding (hA ≫ sA) j) :
    embeddedResolution (hA ≫ sA) j = ((embeddedResolution sA i).pullback f).reduction := by
  have hs := embeddingTriple_mem_sncTriples h
  have hs' := embeddingTriple_mem_sncTriples h'
  have hequi := h.2.2.2.2.2.2.1
  have hequi' := h'.2.2.2.2.2.2.1
  have hXd := h.2.2.1
  have hXd' := h'.2.2.1
  haveI : IsClosedImmersion i := h.2.2.2.1
  haveI : Flat f := MorphismProperty.of_isPullback (P := @Flat) sq inferInstance
  have ht : embeddingTriple sA i ∈ triples := mem_triples_iff.2 ⟨hs, hequi⟩
  have hE : (OrderedDivisor.empty A).comap hA = OrderedDivisor.empty _ := by
    unfold OrderedDivisor.comap OrderedDivisor.empty
    congr 1
    funext j
    exact j.elim0
  have he : embeddingTriple (hA ≫ sA) j = (embeddingTriple sA i).pullback hA := by
    unfold embeddingTriple FieldBlowupTriple.pullback
    rw [Kollar.ker_eq_comap_of_isPullback sq]
    erw [hE]
  have htA : (embeddingTriple sA i).pullback hA ∈ triples :=
    he ▸ mem_triples_iff.2 ⟨hs', hequi'⟩
  have hcomm := (canonicalPrincipalization_properties.{u, u, u}).2.2.2.2.1.2 _ ht _ hA
    ‹Smooth hA› hs'.2.2.1 hs'.2.2.2.1 htA
  obtain ⟨B, hBeq⟩ : ∃ B : ClosedBlowupSequence A,
      canonicalPrincipalization (embeddingTriple sA i) hs = B := ⟨_, rfl⟩
  have hB : canonicalPrincipalization (embeddingTriple (hA ≫ sA) j) hs' =
      (B.pullback hA).reduction :=
    (eq_of_heq (canonicalPrincipalization_heq he hs' (triples_subset_sncTriples htA))).trans
      (hcomm.trans (congrArg (fun C : ClosedBlowupSequence A => (C.pullback hA).reduction) hBeq))
  have e1 : embeddedResolution (hA ≫ sA) j =
      (embeddedResolutionSequence (B.pullback hA).reduction j).reduction := by
    unfold embeddedResolution; rw [dif_pos hs']
    exact congrArg (fun C ↦ (embeddedResolutionSequence C j).reduction) hB
  have e2 : embeddedResolution sA i = (embeddedResolutionSequence B i).reduction := by
    unfold embeddedResolution; rw [dif_pos hs]
    exact congrArg (fun C : ClosedBlowupSequence A ↦ (embeddedResolutionSequence C i).reduction)
      hBeq
  have := isNoetherian_of_isDisjointUnionOfVarieties hXd'
  rw [e1, Kollar.reduction_embeddedResolutionSequence_reduction,
    Kollar.reduction_embeddedResolutionSequence_pullback_of_flat_of_comm sA i hXd B (hA ≫ sA) hA f j
      sq.w hXd', e2,
    reduction_pullback_reduction]

/-! ### Finite disjoint unions of cartesian squares -/

/-- A finite disjoint union of cartesian squares over a common base `X → A` is cartesian. -/
private theorem isPullback_sigmaDesc {X A : Scheme.{u}} (i : X ⟶ A) {ι : Type u} [Finite ι]
    (P V : ι → Scheme.{u}) (hP : ∀ α, P α ⟶ A) (f : ∀ α, V α ⟶ X) (j : ∀ α, V α ⟶ P α)
    (H : ∀ α, IsPullback (j α) (f α) (hP α) i) :
    IsPullback (Sigma.desc fun α ↦ j α ≫ Sigma.ι P α) (Sigma.desc f) (Sigma.desc hP) i := by
  have hau := FinitaryPreExtensive.isUniversal_finiteCoproducts (coproductIsCoproduct P)
  have := hau.isPullback_of_isColimit_right hP (Sigma.desc hP) i j f H
    (coproductIsCoproduct V) (fun α ↦ Sigma.ι_desc _ _)
  have e1 : Cofan.IsColimit.desc (coproductIsCoproduct V) (fun α ↦ j α ≫ Sigma.ι P α) =
      Sigma.desc fun α ↦ j α ≫ Sigma.ι P α :=
    Sigma.hom_ext _ _ fun α ↦ (Cofan.IsColimit.fac _ _ α).trans
      (Sigma.ι_desc (fun α ↦ j α ≫ Sigma.ι P α) α).symm
  have e2 : Cofan.IsColimit.desc (coproductIsCoproduct V) f = Sigma.desc f :=
    Sigma.hom_ext _ _ fun α ↦ (Cofan.IsColimit.fac _ _ α).trans (Sigma.ι_desc f α).symm
  rwa [← e1, ← e2]

/-! ### Smooth morphisms locally lift to the ambient space -/

/-- A smooth morphism is smooth of some relative dimension near every point of the source. -/
private theorem exists_smoothOfRelativeDimension_nbhd {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    (x : X) : ∃ V : X.Opens, x ∈ V ∧ ∃ n : ℕ, SmoothOfRelativeDimension n (V.ι ≫ f) := by
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ := Smooth.exists_isStandardSmooth f x
  obtain ⟨n, hn⟩ : ∃ n, (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension n := by
    letI := (f.appLE U V e).hom.toAlgebra
    obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hf.toAlgebra.out
    exact ⟨P.dimension, P.isStandardSmoothOfRelativeDimension rfl⟩
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have hQi := (HasRingHomProperty.isLocal_ringHomProperty
    (@SmoothOfRelativeDimension n)).respectsIso
  have : (RingHom.toMorphismProperty
      (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n))).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp hQi
  have h : SmoothOfRelativeDimension n (f.resLE U V e) := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension n)]
    exact (MorphismProperty.arrow_mk_iso_iff (RingHom.toMorphismProperty
      (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)))
      (arrowResLEAppIso f U V e)).mpr
      (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ hn)
  refine ⟨V, hx, n, ?_⟩
  rw [← Scheme.Hom.resLE_comp_ι f e]
  exact inferInstanceAs (SmoothOfRelativeDimension (n + 0) _)

/-- A scheme smooth of relative dimension `N` over a field has local dimension `N` everywhere. -/
private theorem topologicalKrullDimAt_eq_of_smoothOfRelativeDimension {k : Type u} [Field k]
    {T : Scheme.{u}} (s : T ⟶ Spec (.of k)) (N : ℕ) [SmoothOfRelativeDimension N s] (t : T) :
    topologicalKrullDimAt T t = N := by
  have : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have hpre : s.base ⁻¹' {s.base t} = (Set.univ : Set T) := by
    ext y; simp [Subsingleton.elim (s.base y) (s.base t)]
  let e : s.fiber (s.base t) ≃ₜ T :=
    (s.fiberHomeo _).trans ((Homeomorph.setCongr hpre).trans (Homeomorph.Set.univ T))
  have he : e (s.asFiber t) = t := s.fiberι_asFiber t
  rw [← he, e.isOpenEmbedding.topologicalKrullDimAt_eq]
  exact fiberDimensionAt_eq_of_smoothOfRelativeDimension s N t

/-- Along a morphism smooth of relative dimension `d` to a scheme smooth over a field, local
dimension goes up by `d`. -/
private theorem topologicalKrullDimAt_eq_add {k : Type u} [Field k] {A A' : Scheme.{u}}
    (sA : A ⟶ Spec (.of k)) [Smooth sA] (f : A' ⟶ A) (d : ℕ) [SmoothOfRelativeDimension d f]
    (a : A') : topologicalKrullDimAt A' a = topologicalKrullDimAt A (f a) + d := by
  obtain ⟨V, hV, m, hm⟩ := exists_smoothOfRelativeDimension_nbhd sA (f a)
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
  haveI : SmoothOfRelativeDimension d (f ∣_ V) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f V).flip ‹_›
  let a' : (f ⁻¹ᵁ V).toScheme := ⟨a, hV⟩
  have h1 := topologicalKrullDimAt_eq_of_smoothOfRelativeDimension
    ((f ∣_ V) ≫ V.ι ≫ sA) (d + m) a'
  have h2 := topologicalKrullDimAt_eq_of_smoothOfRelativeDimension (V.ι ≫ sA) m ((f ∣_ V) a')
  rw [← (f ⁻¹ᵁ V).ι.isOpenEmbedding.topologicalKrullDimAt_eq] at h1
  rw [← V.ι.isOpenEmbedding.topologicalKrullDimAt_eq, ← Scheme.Hom.comp_apply,
    morphismRestrict_ι, Scheme.Hom.comp_apply] at h2
  change topologicalKrullDimAt A' a = _ at h1
  change topologicalKrullDimAt A (f a) = _ at h2
  rw [h1, h2]
  push_cast
  exact add_comm _ _

/-! ### Admissibility under smooth base change of the ambient space -/

/-- **Admissibility is preserved by smooth base change of the ambient space.** If `X ⊆ A` is
admissible, `h_A : A' → A` is smooth of relative dimension `d` with `A'` affine, and
`X' = X ×_A A'` is a disjoint union of varieties, then `X' ⊆ A'` is admissible. At every point
of `A'` the local dimension is `dim A + d`, so `A'` is equidimensional; codimension `≥ 2` is
carried over by going-down along the flat `h_A`. -/
private theorem isAdmissibleEmbedding_of_isPullback {k : Type u} [Field k]
    {X A X' A' : Scheme.{u}} {sA : A ⟶ Spec (.of k)} {i : X ⟶ A}
    (h : IsAdmissibleEmbedding sA i) (d : ℕ) {hA : A' ⟶ A} [SmoothOfRelativeDimension d hA]
    [IsAffine A'] {f : X' ⟶ X} {j : X' ⟶ A'} (sq : IsPullback j f hA i)
    (hX' : IsDisjointUnionOfVarieties (j ≫ hA ≫ sA)) :
    IsAdmissibleEmbedding (hA ≫ sA) j := by
  haveI : IsClosedImmersion i := h.2.2.2.1
  haveI : LocallyOfFiniteType sA := (embeddingTriple_mem_sncTriples h).2.2.1
  haveI : Smooth sA := (MMP.Mori.isSmoothScheme_iff sA).mp h.2.2.2.2.2.1
  haveI : Smooth hA := SmoothOfRelativeDimension.smooth d hA
  haveI : Flat f := MorphismProperty.of_isPullback (P := @Flat) sq inferInstance
  haveI : IsClosedImmersion j := MorphismProperty.of_isPullback sq.flip ‹_›
  have hdim : ∀ a : A', ∀ C ∈ irreducibleComponents A,
      topologicalKrullDimAt A' a = topologicalKrullDim C + d := fun a C hC ↦ by
    rw [topologicalKrullDimAt_eq_add sA hA d a,
      topologicalKrullDimAt_eq_of_mem_irreducibleComponents sA h.2.2.2.2.2.2.1 _ hC]
  refine ⟨h.1, isAffine_of_isAffineHom j, hX', inferInstance, inferInstance,
    (MMP.Mori.isSmoothScheme_iff _).mpr inferInstance, fun Z hZ W hW ↦ ?_,
    codim_of_flat i hA f j sq.w (fun a ↦ by
      haveI := isRegularLocalRing_stalk_of_smooth_over_field (hA ≫ sA) a
      exact IsRegularLocalRing.isDomain _) h.2.2.2.2.2.2.2⟩
  have hC := irreducibleComponent_mem_irreducibleComponents (hA hZ.1.genericPoint)
  rw [topologicalKrullDim_eq_topologicalKrullDimAt_genericPoint (hA ≫ sA) hZ,
    topologicalKrullDim_eq_topologicalKrullDimAt_genericPoint (hA ≫ sA) hW, hdim _ _ hC,
    hdim _ _ hC]

/-! ### Main proof -/

/-- The inclusion of `V = f⁻¹(U)`, restricted from `f`, is the base change of `U ⊆ Y` along `f`. -/
private theorem isPullback_resLE_of_eq {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} {V : X.Opens}
    (e : f ⁻¹ᵁ U = V) : IsPullback (f.resLE U V e.ge) V.ι U.ι f := by
  subst e
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  exact isPullback_morphismRestrict f U

/-- `𝓑𝓡_A(X)` blows up no empty centre. -/
private theorem hasNoEmptyBlowups_embeddedResolution {k : Type u} [Field k] {X A : Scheme.{u}}
    (sA : A ⟶ Spec (.of k)) (i : X ⟶ A) : (embeddedResolution sA i).HasNoEmptyBlowups := by
  unfold embeddedResolution
  split
  · exact ClosedBlowupSequence.hasNoEmptyBlowups_reduction _
  · trivial

/-- On an affine scheme, the basic opens of functions generating the unit ideal cover: the
morphism from their disjoint union is surjective. -/
private theorem surjective_sigmaDesc_basicOpen_ι {X : Scheme.{u}} [IsAffine X] {ι : Type u}
    (g : ι → Γ(X, ⊤)) (hg : Ideal.span (Set.range g) = ⊤) :
    Surjective (Sigma.desc fun α ↦ (X.basicOpen (g α)).ι) := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨⟨_, α, rfl⟩, hxα⟩ := Opens.mem_iSup.mp
    ((isAffineOpen_top X).self_le_iSup_basicOpen_iff.mpr hg (Set.mem_univ x))
  obtain ⟨z, rfl⟩ : x ∈ Set.range (X.basicOpen (g α)).ι := by
    rw [Scheme.Opens.range_ι]; exact hxα
  refine ⟨Sigma.ι (fun α ↦ (X.basicOpen (g α)).toScheme) α z, ?_⟩
  rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]

end Proof_lem_kr3f_br_open_cover

namespace MMP.Resolution

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open MMP.Resolution.ClosedBlowupSequence
open Proof_lem_kr3f_br_open_cover

universe u

/-- **`𝓑𝓡` is compatible with a principal open cover** (Kollár 3.34): let `i : X ⟶ A` be an
admissible embedding over `k`, `g : ι → Γ(X, ⊤)` a finite family generating the unit ideal, and
`q : ∐ D_X(g α) ⟶ X` the morphism induced by the inclusions of the basic opens. For every
admissible embedding `i' : ∐ D_X(g α) ⟶ A'` over `k`,
`embeddedResolution sA' i' = (embeddedResolution sA i).pullback q`. -/
@[mmp "lem_kr3f_br_open_cover"]
public theorem embeddedResolution_sigmaBasicOpen_eq_pullback {k : Type u} [Field k]
    {X A A' : Scheme.{u}} {sA : A ⟶ Spec (.of k)} {i : X ⟶ A}
    (h : IsAdmissibleEmbedding sA i) {ι : Type u} [Finite ι] (g : ι → Γ(X, ⊤))
    (hg : Ideal.span (Set.range g) = ⊤) {sA' : A' ⟶ Spec (.of k)}
    {i' : (∐ fun α ↦ (X.basicOpen (g α)).toScheme) ⟶ A'}
    (h' : IsAdmissibleEmbedding sA' i')
    (hk : i' ≫ sA' = Sigma.desc (fun α ↦ (X.basicOpen (g α)).ι) ≫ i ≫ sA) :
    embeddedResolution sA' i' =
      (embeddedResolution sA i).pullback (Sigma.desc fun α ↦ (X.basicOpen (g α)).ι) := by
  haveI : IsClosedImmersion i := h.2.2.2.1
  haveI : IsAffine A := h.2.2.2.2.1
  haveI : IsAffine X := h.2.1
  -- lift the `g α` to `G α ∈ 𝒪(A)`
  choose G hG using fun α ↦ i.app_surjective ⊤ (isAffineOpen_top A) (g α)
  have hpre : ∀ α, i ⁻¹ᵁ A.basicOpen (G α) = X.basicOpen (g α) := fun α ↦ by
    rw [Scheme.preimage_basicOpen, hG]; rfl
  -- the ambient space `A'' = ∐ D_A(G α)` and the cartesian square
  set q : (∐ fun α ↦ (X.basicOpen (g α)).toScheme) ⟶ X :=
    Sigma.desc fun α ↦ (X.basicOpen (g α)).ι
  set hA : (∐ fun α ↦ (A.basicOpen (G α)).toScheme) ⟶ A :=
    Sigma.desc fun α ↦ (A.basicOpen (G α)).ι
  set j : (∐ fun α ↦ (X.basicOpen (g α)).toScheme) ⟶ ∐ fun α ↦ (A.basicOpen (G α)).toScheme :=
    Sigma.desc fun α ↦ i.resLE _ _ (hpre α).ge ≫
      Sigma.ι (fun α ↦ (A.basicOpen (G α)).toScheme) α
  have sq : IsPullback j q hA i :=
    isPullback_sigmaDesc i (fun α ↦ (A.basicOpen (G α)).toScheme)
      (fun α ↦ (X.basicOpen (g α)).toScheme) (fun α ↦ (A.basicOpen (G α)).ι)
      (fun α ↦ (X.basicOpen (g α)).ι) (fun α ↦ i.resLE _ _ (hpre α).ge)
      (fun α ↦ isPullback_resLE_of_eq i (hpre α))
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{u} 0) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension 0)
  have : IsZariskiLocalAtSource @Flat.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat)
  haveI : SmoothOfRelativeDimension 0 hA :=
    IsZariskiLocalAtSource.sigmaDesc fun α ↦ inferInstance
  haveI : Smooth hA := SmoothOfRelativeDimension.smooth 0 hA
  haveI : Flat q := IsZariskiLocalAtSource.sigmaDesc fun α ↦ inferInstance
  haveI : Surjective q := surjective_sigmaDesc_basicOpen_ι g hg
  haveI : ∀ α, IsAffine (X.basicOpen (g α)).toScheme :=
    fun α ↦ (isAffineOpen_top X).basicOpen (g α)
  haveI : ∀ α, IsAffine (A.basicOpen (G α)).toScheme :=
    fun α ↦ (isAffineOpen_top A).basicOpen (G α)
  have hX' : IsDisjointUnionOfVarieties (j ≫ hA ≫ sA) := by
    rw [sq.w_assoc]
    exact isDisjointUnionOfVarieties_sigmaDesc h.2.2.1 _
  have hadm := isAdmissibleEmbedding_of_isPullback h 0 sq hX'
  -- `𝓑𝓡_{A'}(X') = 𝓑𝓡_{A''}(X') = (q^*𝓑𝓡_A(X))^red = q^*𝓑𝓡_A(X)`
  rw [embeddedResolution_eq_of_isAdmissibleEmbedding h' hadm (by rw [hk, sq.w_assoc]),
    embeddedResolution_eq_reduction_pullback_of_isPullback sq h hadm,
    reduction_pullback_eq_pullback_reduction,
    reduction_eq_self (hasNoEmptyBlowups_embeddedResolution sA i)]

/-- **Embedded resolution and smooth ambient pull-back** (Kollár p. 146): let `hA : A' ⟶ A` be a
smooth morphism, `i : X ⟶ A` an admissible embedding over `k` (`IsAdmissibleEmbedding sA i`), and
suppose the base change `Limits.pullback.snd i hA : X ×_A A' ⟶ A'` is an admissible embedding over
`k` (`A'` over `k` by `hA ≫ sA`). Then `𝓑𝓡_{A'}(X') = (h^* 𝓑𝓡_A(X))^red`, where
`h = Limits.pullback.fst i hA`. -/
@[mmp "lem_kr3f_br_ambient_smooth_pullback"]
public theorem embeddedResolution_pullback_snd_eq_reduction_pullback {k : Type u} [Field k]
    {X A A' : Scheme.{u}} {sA : A ⟶ Spec (.of k)} {i : X ⟶ A} (hA : A' ⟶ A) [Smooth hA]
    (h : IsAdmissibleEmbedding sA i)
    (h' : IsAdmissibleEmbedding (hA ≫ sA) (Limits.pullback.snd i hA)) :
    embeddedResolution (hA ≫ sA) (Limits.pullback.snd i hA) =
      ((embeddedResolution sA i).pullback (Limits.pullback.fst i hA)).reduction :=
  embeddedResolution_eq_reduction_pullback_of_isPullback (IsPullback.of_hasPullback i hA).flip h h'

end MMP.Resolution

namespace Proof_lem_kr3f_embedded_resolution_smooth_morphisms

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MMP.Resolution
open MMP.Resolution.ClosedBlowupSequence
open Proof_lem_kr3f_br_open_cover

universe u

/-- **Kollár 3.41, on basic opens.** Around every point `y` of an affine `Y`, a morphism
`h : Y → X` smooth of relative dimension `d` is, on a basic open `D_Y(g) ∋ y`, the base change
along the closed immersion `X → A` of a morphism `h_P : P → A` from an affine scheme, smooth of
relative dimension `d`. -/
private theorem exists_basicOpen_isPullback {k : Type u} [Field k] {X Y A : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [A.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (A ↘ Spec (.of k))] [QuasiCompact (A ↘ Spec (.of k))]
    [IsAffine A] [IsAffine Y]
    (d : ℕ) (h : Y ⟶ X) [h.IsOver (Spec (.of k))] [SmoothOfRelativeDimension d h]
    (i : X ⟶ A) [i.IsOver (Spec (.of k))] [IsClosedImmersion i] (y : Y) :
    ∃ (g : Γ(Y, ⊤)) (_ : y ∈ Y.basicOpen g) (P : Scheme.{u}) (_ : IsAffine P) (hP : P ⟶ A)
      (_ : SmoothOfRelativeDimension d hP) (jP : (Y.basicOpen g).toScheme ⟶ P),
      IsPullback jP ((Y.basicOpen g).ι ≫ h) hP i := by
  haveI : Smooth h := SmoothOfRelativeDimension.smooth d h
  obtain ⟨Y₀, hy, A₀, -, AY₀, hA, j, hle, hsm, -, hj, sq1⟩ :=
    exists_isPullback_smooth_surjective_of_isClosedImmersion (k := k) h i y
  have sqB : IsPullback j (Y₀.ι ≫ h) (hA ≫ A₀.ι) i := by
    have := sq1.paste_vert (isPullback_morphismRestrict i A₀)
    rwa [Scheme.Hom.resLE_comp_ι] at this
  let y₀ : Y₀.toScheme := ⟨y, hy⟩
  obtain ⟨V, hjV, e, he⟩ := exists_smoothOfRelativeDimension_nbhd hA (j y₀)
  obtain ⟨_, ⟨(W : AY₀.Opens), hW, rfl⟩, hjW, hWV⟩ :=
    AY₀.isBasis_affineOpens.exists_subset_of_mem_open hjV V.2
  have hWV' : W ≤ V := hWV
  let ψ : (j ⁻¹ᵁ W).toScheme ⟶ Y := (j ⁻¹ᵁ W).ι ≫ Y₀.ι
  have hyψ : y ∈ ψ.opensRange := ⟨⟨y₀, hjW⟩, rfl⟩
  obtain ⟨g, hgψ, hyg⟩ := (isAffineOpen_top Y).exists_basicOpen_le ⟨y, hyψ⟩ trivial
  let jW : (j ⁻¹ᵁ W).toScheme ⟶ W.toScheme := j ∣_ W
  haveI : IsAffine W.toScheme := hW
  obtain ⟨G, hG⟩ := jW.app_surjective ⊤ (isAffineOpen_top _) (ψ.appTop g)
  let D : W.toScheme.Opens := W.toScheme.basicOpen G
  have hpre : jW ⁻¹ᵁ D = ψ ⁻¹ᵁ Y.basicOpen g := by
    rw [Scheme.preimage_basicOpen, hG, Scheme.preimage_basicOpen]; rfl
  let m : (jW ⁻¹ᵁ D).toScheme ⟶ Y := (jW ⁻¹ᵁ D).ι ≫ ψ
  have hrange : Set.range (Y.basicOpen g).ι = Set.range m := by
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι, hpre]
    simp only [Scheme.Hom.coe_preimage, Set.image_preimage_eq_inter_range]
    exact (Set.inter_eq_left.mpr hgψ).symm
  let eiso := IsOpenImmersion.isoOfRangeEq (Y.basicOpen g).ι m hrange
  have hfac : eiso.hom ≫ m = (Y.basicOpen g).ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have sq5 := ((isPullback_morphismRestrict jW D).paste_vert
    (isPullback_morphismRestrict j W)).paste_vert sqB
  have sq6 := (IsPullback.of_vert_isIso (fst := eiso.hom ≫ jW ∣_ D) (snd := eiso.hom)
    (f := 𝟙 _) (g := jW ∣_ D) ⟨by simp⟩).paste_vert sq5
  have hl : eiso.hom ≫ ((jW ⁻¹ᵁ D).ι ≫ (j ⁻¹ᵁ W).ι) ≫ Y₀.ι ≫ h = (Y.basicOpen g).ι ≫ h := by
    rw [← hfac]; simp [m, ψ]
  rw [hl, Category.id_comp] at sq6
  set hP : D.toScheme ⟶ A := (D.ι ≫ W.ι) ≫ hA ≫ A₀.ι with hhP
  haveI : SmoothOfRelativeDimension e hP := by
    have hW' : W.ι = AY₀.homOfLE hWV' ≫ V.ι := (Scheme.homOfLE_ι _ _).symm
    have : SmoothOfRelativeDimension (0 + e + 0) (((D.ι ≫ AY₀.homOfLE hWV') ≫ V.ι ≫ hA) ≫ A₀.ι) :=
      inferInstance
    simp only [add_zero, zero_add] at this
    rw [hhP, hW']
    simpa only [Category.assoc] using this
  have hed : e = d := by
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := e)
    have h1 : SmoothOfRelativeDimension e ((Y.basicOpen g).ι ≫ h) :=
      MorphismProperty.of_isPullback sq6 ‹_›
    have h2 : SmoothOfRelativeDimension (0 + d) ((Y.basicOpen g).ι ≫ h) := inferInstance
    rw [zero_add] at h2
    let z : (Y.basicOpen g).toScheme := ⟨y, hyg⟩
    have := (@fiberDimensionAt_eq_of_smoothOfRelativeDimension _ _ _ e h1 z).symm.trans
      (@fiberDimensionAt_eq_of_smoothOfRelativeDimension _ _ _ d h2 z)
    exact_mod_cast this
  subst hed
  exact ⟨g, hyg, D.toScheme, (isAffineOpen_top W.toScheme).basicOpen G, hP, ‹_›, _, sq6⟩

end Proof_lem_kr3f_embedded_resolution_smooth_morphisms

namespace MMP.Resolution

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open MMP.Resolution.ClosedBlowupSequence
open Proof_lem_kr3f_br_open_cover
open Proof_lem_kr3f_embedded_resolution_smooth_morphisms

universe u

/-- **Embedded resolution commutes with smooth morphisms** (Kollár pp. 146–147): if
`iX : X ⟶ AX` and `iY : Y ⟶ AY` are admissible embeddings (`IsAdmissibleEmbedding`) over a field
`k` and `h : Y ⟶ X` is a `k`-morphism that is smooth of constant relative dimension `d`, then
`embeddedResolution sAY iY = ((embeddedResolution sAX iX).pullback h).reduction`. -/
@[mmp "lem_kr3f_embedded_resolution_smooth_morphisms"]
public theorem embeddedResolution_eq_reduction_pullback_of_smoothOfRelativeDimension
    {k : Type u} [Field k] {X Y AX AY : Scheme.{u}} {sAX : AX ⟶ Spec (.of k)}
    {sAY : AY ⟶ Spec (.of k)} {iX : X ⟶ AX} {iY : Y ⟶ AY}
    (hX : IsAdmissibleEmbedding sAX iX) (hY : IsAdmissibleEmbedding sAY iY)
    (d : ℕ) (h : Y ⟶ X) [SmoothOfRelativeDimension d h] (hk : h ≫ iX ≫ sAX = iY ≫ sAY) :
    embeddedResolution sAY iY = ((embeddedResolution sAX iX).pullback h).reduction := by
  have hsX := embeddingTriple_mem_sncTriples hX
  have hXd := hX.2.2.1
  have hYd := hY.2.2.1
  haveI : IsClosedImmersion iX := hX.2.2.2.1
  haveI : IsAffine AX := hX.2.2.2.2.1
  haveI : IsAffine Y := hY.2.1
  haveI : LocallyOfFiniteType sAX := hsX.2.2.1
  haveI : QuasiCompact sAX := hsX.2.2.2.1
  haveI : Smooth sAX := (MMP.Mori.isSmoothScheme_iff sAX).mp hX.2.2.2.2.2.1
  haveI : Smooth h := SmoothOfRelativeDimension.smooth d h
  -- local lifts of `h` to the ambient space
  letI : X.Over (Spec (.of k)) := ⟨iX ≫ sAX⟩
  letI : Y.Over (Spec (.of k)) := ⟨iY ≫ sAY⟩
  letI : AX.Over (Spec (.of k)) := ⟨sAX⟩
  haveI : LocallyOfFiniteType (X ↘ Spec (.of k)) := hXd.1
  haveI : QuasiCompact (X ↘ Spec (.of k)) := hXd.2.1
  haveI : LocallyOfFiniteType (Y ↘ Spec (.of k)) := hYd.1
  haveI : QuasiCompact (Y ↘ Spec (.of k)) := hYd.2.1
  haveI : LocallyOfFiniteType (AX ↘ Spec (.of k)) := ‹LocallyOfFiniteType sAX›
  haveI : QuasiCompact (AX ↘ Spec (.of k)) := ‹QuasiCompact sAX›
  haveI : h.IsOver (Spec (.of k)) := ⟨hk⟩
  haveI : iX.IsOver (Spec (.of k)) := ⟨rfl⟩
  choose g hyg P hPaff hP hPsm jP hsq using fun y : Y ↦
    exists_basicOpen_isPullback (k := k) d h iX y
  -- finitely many of the basic opens cover `Y`
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover (fun y ↦ (Y.basicOpen (g y) : Set Y))
    (fun y _ ↦ (Y.basicOpen (g y)).2.mem_nhds (hyg y))
  let g' : t → Γ(Y, ⊤) := fun α ↦ g α.1
  have hcov : ∀ x : Y, ∃ α : t, x ∈ Y.basicOpen (g' α) := fun x ↦ by
    have := ht (Set.mem_univ x)
    simp only [Set.mem_iUnion] at this
    obtain ⟨y, hy, hx⟩ := this
    exact ⟨⟨y, hy⟩, hx⟩
  have hspan : Ideal.span (Set.range g') = ⊤ := by
    refine (isAffineOpen_top Y).self_le_iSup_basicOpen_iff.mp fun x _ ↦ ?_
    obtain ⟨α, hα⟩ := hcov x
    exact Opens.mem_iSup.mpr ⟨⟨g' α, α, rfl⟩, hα⟩
  -- the ambient space `A' = ∐ P_α` and the cartesian square
  set q : (∐ fun α : t ↦ (Y.basicOpen (g' α)).toScheme) ⟶ Y :=
    Sigma.desc fun α ↦ (Y.basicOpen (g' α)).ι with hq
  set hA' : (∐ fun α : t ↦ P α.1) ⟶ AX := Sigma.desc fun α ↦ hP α.1 with hhA'
  set j' : (∐ fun α : t ↦ (Y.basicOpen (g' α)).toScheme) ⟶ ∐ fun α : t ↦ P α.1 :=
    Sigma.desc fun α ↦ jP α.1 ≫ Sigma.ι (fun α : t ↦ P α.1) α with hj'
  have sq : IsPullback j' (q ≫ h) hA' iX := by
    have := isPullback_sigmaDesc iX (fun α : t ↦ P α.1)
      (fun α : t ↦ (Y.basicOpen (g' α)).toScheme) (fun α ↦ hP α.1)
      (fun α ↦ (Y.basicOpen (g' α)).ι ≫ h) (fun α ↦ jP α.1) (fun α ↦ hsq α.1)
    have hqh : (Sigma.desc fun α : t ↦ (Y.basicOpen (g' α)).ι ≫ h) = q ≫ h :=
      Sigma.hom_ext _ _ fun α ↦ by simp [hq]
    rwa [hqh] at this
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{u} d) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension d)
  have : IsZariskiLocalAtSource @Flat.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat)
  haveI : SmoothOfRelativeDimension d hA' :=
    IsZariskiLocalAtSource.sigmaDesc fun α ↦ hPsm α.1
  haveI : Smooth hA' := SmoothOfRelativeDimension.smooth d hA'
  haveI : Flat q := IsZariskiLocalAtSource.sigmaDesc fun α ↦ inferInstance
  haveI : Surjective q := surjective_sigmaDesc_basicOpen_ι g' hspan
  haveI : ∀ α : t, IsAffine (Y.basicOpen (g' α)).toScheme :=
    fun α ↦ (isAffineOpen_top Y).basicOpen (g' α)
  haveI : ∀ α : t, IsAffine (P α.1) := fun α ↦ hPaff α.1
  have hk' : j' ≫ hA' ≫ sAX = q ≫ iY ≫ sAY := by
    rw [sq.w_assoc, Category.assoc, hk]
  have hYd' : IsDisjointUnionOfVarieties (j' ≫ hA' ≫ sAX) := by
    rw [hk']
    exact isDisjointUnionOfVarieties_sigmaDesc hYd _
  have hadm := isAdmissibleEmbedding_of_isPullback hX d sq hYd'
  -- `𝓑𝓡_{A'}(Y')` computed in two ways
  have e1 := embeddedResolution_eq_reduction_pullback_of_isPullback sq hX hadm
  have e2 := embeddedResolution_sigmaBasicOpen_eq_pullback hY g' hspan hadm hk'
  have hpc : (embeddedResolution sAX iX).pullback (q ≫ h) =
      ((embeddedResolution sAX iX).pullback h).pullback q :=
    (eq_of_heq ((embeddedResolution sAX iX).pullback_pullback_heq h q (q ≫ h) rfl
      (by simp))).symm
  refine Kollar.eq_of_pullback_eq_of_flat_of_surjective q ?_
  rw [← e2, e1, hpc, reduction_pullback_eq_pullback_reduction]

end MMP.Resolution

namespace Proof_lem_kr3f_br_glues

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MMP.Resolution Topology
open Proof_lem_kr3f_embedded_resolution_independent_of_embedding

universe u

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
  obtain ⟨y, rfl⟩ : x ∈ Set.range (U α).ι.base := by rw [Scheme.Opens.range_ι]; exact hα
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

/-! ### Locally irreducible spaces -/

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

/-! ### Descent along a surjective local isomorphism -/

/-- **Descent of ideal sheaves along a surjective local isomorphism.** An ideal sheaf on `X'`
whose two pull-backs to `X' ×_X X'` agree is the pull-back of an ideal sheaf on `X`. -/
private theorem exists_comap_eq_of_isLocalIso {X X' : Scheme.{u}} (q : X' ⟶ X) [IsLocalIso q]
    [Surjective q] (I : X'.IdealSheafData)
    (hI : I.comap (pullback.fst q q) = I.comap (pullback.snd q q)) :
    ∃ J : X.IdealSheafData, J.comap q = I := by
  choose V hxV hV using fun x : X' ↦ IsLocalIso.exists_isOpenImmersion (f := q) x
  have hsurj : ∀ w : X, ∃ x, ∃ v : V x, ((V x).ι ≫ q) v = w := by
    intro w
    obtain ⟨x, rfl⟩ := q.surjective w
    exact ⟨x, ⟨x, hxV x⟩, rfl⟩
  have hcompat : ∀ x y, (I.comap (V x).ι).comap (pullback.fst ((V x).ι ≫ q) ((V y).ι ≫ q)) =
      (I.comap (V y).ι).comap (pullback.snd ((V x).ι ≫ q) ((V y).ι ≫ q)) := by
    intro x y
    let m := pullback.map ((V x).ι ≫ q) ((V y).ι ≫ q) q q (V x).ι (V y).ι (𝟙 X) (by simp)
      (by simp)
    have h1 : pullback.fst ((V x).ι ≫ q) ((V y).ι ≫ q) ≫ (V x).ι = m ≫ pullback.fst q q := by
      simp [m]
    have h2 : pullback.snd ((V x).ι ≫ q) ((V y).ι ≫ q) ≫ (V y).ι = m ≫ pullback.snd q q := by
      simp [m]
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, h1, h2,
      Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, hI]
  obtain ⟨J, hJ⟩ := Scheme.IdealSheafData.exists_comap_eq_of_isOpenImmersion
    (fun x ↦ (V x).ι ≫ q) hsurj (fun x ↦ I.comap (V x).ι) hcompat
  refine ⟨J, Scheme.IdealSheafData.ext_of_comap_eq_of_isOpenImmersion (fun x ↦ (V x).ι)
    (fun x ↦ ⟨x, ⟨x, hxV x⟩, rfl⟩) fun x ↦ ?_⟩
  rw [← Scheme.IdealSheafData.comap_comp, hJ]

/-- Pulling back twice is pulling back along the composite. -/
private theorem pullback_pullback {X W Y : Scheme.{u}} (S : ClosedBlowupSequence X) (h : W ⟶ X)
    (k : Y ⟶ W) : (S.pullback h).pullback k = S.pullback (k ≫ h) :=
  congrArg Sigma.fst (eq_of_heq (ClosedBlowupSequence.pullback_pullback_sigma_heq S h k (k ≫ h)
    rfl (by simp)))

private theorem pullback_congr_heq {T Y₁ Y₂ : Scheme.{u}} (e : Y₁ = Y₂)
    {S₁ : ClosedBlowupSequence Y₁} {S₂ : ClosedBlowupSequence Y₂} {f₁ : T ⟶ Y₁} {f₂ : T ⟶ Y₂}
    (hS : S₁ ≍ S₂) (hf : f₁ ≍ f₂) : S₁.pullback f₁ = S₂.pullback f₂ := by
  subst e
  obtain rfl := eq_of_heq hS
  obtain rfl := eq_of_heq hf
  rfl

private theorem blowUpLift_heq {X Y : Scheme.{u}} {I I' : X.IdealSheafData} (e : I = I')
    (g : Y ⟶ X) (hg : Stacks.Blowup.IsCartierOver I (Over.mk g))
    (hg' : Stacks.Blowup.IsCartierOver I' (Over.mk g)) :
    blowUpLift I g hg ≍ blowUpLift I' g hg' := by
  subst e
  rfl

/-- Let `q : X' → X` be a morphism and `Z ⊆ X` closed. For `r : T → B_{q⁻¹Z}X'` with
`T → B_ZX` flat and a morphism `ψ : T → P` with `ψ ≫ p = r ≫ π` for some `p : P → X'`, the
morphism `ψ` lifts to `B_{p⁻¹q⁻¹Z}P`, and the lift followed by the canonical lift of `p` is `r`. -/
private theorem exists_blowUpLift_comp_canonicalLift {X X' T P : Scheme.{u}} (q : X' ⟶ X)
    (Z : X.IdealSheafData) (p : P ⟶ X') (ψ : T ⟶ P) (r : T ⟶ blowUp (Z.comap q))
    (hψ : ψ ≫ p = r ≫ blowUpToBase (Z.comap q)) [Flat (r ≫ canonicalLift q Z)] :
    ∃ hc : Stacks.Blowup.IsCartierOver ((Z.comap q).comap p) (Over.mk ψ),
      blowUpLift _ ψ hc ≫ canonicalLift p (Z.comap q) = r := by
  have hcart : Stacks.Divisors.IsEffectiveCartierDivisor
      (Z.comap (r ≫ blowUpToBase (Z.comap q) ≫ q)) := by
    rw [← canonicalLift_comp_blowUpToBase, ← Category.assoc, Scheme.IdealSheafData.comap_comp]
    exact Stacks.Divisors.isPullbackDefined_of_flat _ _
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal Z)
  have hc : Stacks.Blowup.IsCartierOver ((Z.comap q).comap p) (Over.mk ψ) := by
    change Stacks.Divisors.IsEffectiveCartierDivisor (((Z.comap q).comap p).comap ψ)
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hψ,
      Category.assoc]
    exact hcart
  have hc' : Stacks.Blowup.IsCartierOver (Z.comap q) (Over.mk (r ≫ blowUpToBase (Z.comap q))) := by
    change Stacks.Divisors.IsEffectiveCartierDivisor
      ((Z.comap q).comap (r ≫ blowUpToBase (Z.comap q)))
    rw [← Scheme.IdealSheafData.comap_comp, Category.assoc]
    exact hcart
  refine ⟨hc, (blowUpLift_unique _ _ hc' _ ?_).trans (blowUpLift_unique _ _ hc' r rfl).symm⟩
  rw [Category.assoc, canonicalLift_comp_blowUpToBase, ← Category.assoc, blowUpLift_comp, hψ]

/-- The agreement of the two pull-backs to `X' ×_X X'` passes from a blow-up sequence of
`B_{q⁻¹Z}X'` to the canonical lift `B_{q⁻¹Z}X' → B_ZX`. -/
private theorem pullback_fst_eq_pullback_snd_canonicalLift {X X' : Scheme.{u}} (q : X' ⟶ X)
    [IsLocalIso q] (Z : X.IdealSheafData) (B : ClosedBlowupSequence (blowUp (Z.comap q)))
    (hB : B.pullback (canonicalLift (pullback.fst q q) (Z.comap q)) ≍
      B.pullback (canonicalLift (pullback.snd q q) (Z.comap q))) :
    B.pullback (pullback.fst (canonicalLift q Z) (canonicalLift q Z)) =
      B.pullback (pullback.snd (canonicalLift q Z) (canonicalLift q Z)) := by
  have := flat_of_isLocalIso q
  have : Flat (canonicalLift q Z) := Kollar.flat_canonicalLift q Z
  let q₁ := canonicalLift q Z
  have hq : ∀ r : pullback q₁ q₁ ⟶ blowUp (Z.comap q),
      r ≫ blowUpToBase (Z.comap q) ≫ q = r ≫ q₁ ≫ blowUpToBase Z := fun r ↦ by
    rw [canonicalLift_comp_blowUpToBase]
  let ψ : pullback q₁ q₁ ⟶ pullback q q :=
    pullback.lift (pullback.fst q₁ q₁ ≫ blowUpToBase (Z.comap q))
      (pullback.snd q₁ q₁ ≫ blowUpToBase (Z.comap q)) (by
      simp only [Category.assoc]
      rw [hq, hq, pullback.condition_assoc])
  obtain ⟨hc₁, e₁⟩ := exists_blowUpLift_comp_canonicalLift q Z (pullback.fst q q) ψ
    (pullback.fst q₁ q₁) (pullback.lift_fst _ _ _)
  obtain ⟨hc₂, e₂⟩ := exists_blowUpLift_comp_canonicalLift q Z (pullback.snd q q) ψ
    (pullback.snd q₁ q₁) (pullback.lift_snd _ _ _)
  have hW : (Z.comap q).comap (pullback.fst q q) = (Z.comap q).comap (pullback.snd q q) := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      pullback.condition]
  calc B.pullback (pullback.fst q₁ q₁)
      = (B.pullback (canonicalLift (pullback.fst q q) (Z.comap q))).pullback
          (blowUpLift _ ψ hc₁) := by rw [pullback_pullback, e₁]
    _ = (B.pullback (canonicalLift (pullback.snd q q) (Z.comap q))).pullback
          (blowUpLift _ ψ hc₂) :=
        pullback_congr_heq (congrArg blowUp hW) hB (blowUpLift_heq hW ψ _ _)
    _ = B.pullback (pullback.snd q₁ q₁) := by rw [pullback_pullback, e₂]

/-- **Descent of blow-up sequences along a surjective local isomorphism.** A blow-up sequence
of `X'` whose pull-backs along the two projections `X' ×_X X' → X'` agree is the pull-back of a
blow-up sequence of `X`. -/
private theorem exists_pullback_eq_of_isLocalIso {X' : Scheme.{u}}
    (B : ClosedBlowupSequence X') :
    ∀ {X : Scheme.{u}} (q : X' ⟶ X) [IsLocalIso q] [Surjective q],
      B.pullback (pullback.fst q q) = B.pullback (pullback.snd q q) →
        ∃ G : ClosedBlowupSequence X, G.pullback q = B := by
  induction B with
  | nil X' => intro X q _ _ _; exact ⟨.nil X, rfl⟩
  | cons Z' B ih =>
    intro X q _ _ hB
    obtain ⟨hZ, hT⟩ := ClosedBlowupSequence.cons_eq_cons_iff.mp hB
    obtain ⟨Z, rfl⟩ := exists_comap_eq_of_isLocalIso q Z' hZ
    have := flat_of_isLocalIso q
    have : IsLocalIso (canonicalLift q Z) := MorphismProperty.of_isPullback (P := @IsLocalIso)
      (Kollar.isPullback_canonicalLift_of_flat q Z) ‹_›
    have := Kollar.surjective_canonicalLift q Z
    obtain ⟨G, hG⟩ := ih (canonicalLift q Z) (pullback_fst_eq_pullback_snd_canonicalLift q Z B hT)
    exact ⟨.cons Z G, by rw [ClosedBlowupSequence.pullback, hG]⟩

/-! ### Admissible embeddings into affine space -/

/-- The coordinate inclusion `𝔸^m_k → 𝔸^{m+1}_k`, `x ↦ (x, 0)`, is a closed immersion over `k`
that is not surjective. -/
private theorem exists_isClosedImmersion_not_surjective (k : Type u) [Field k] (m : Type u) :
    ∃ c : 𝔸(m; Spec (.of k)) ⟶ 𝔸(Option m; Spec (.of k)), IsClosedImmersion c ∧
      ¬ Function.Surjective c.base ∧
      c ≫ 𝔸(Option m; Spec (.of k)) ↘ Spec (.of k) = 𝔸(m; Spec (.of k)) ↘ Spec (.of k) := by
  let c : 𝔸(m; Spec (.of k)) ⟶ 𝔸(Option m; Spec (.of k)) :=
    AffineSpace.homOfVector (𝔸(m; Spec (.of k)) ↘ Spec (.of k))
      fun o ↦ o.elim 0 (AffineSpace.coord _)
  let r := AffineSpace.reindex (some : m → Option m) (Spec (.of k))
  have hcr : c ≫ r = 𝟙 _ := by
    apply AffineSpace.hom_ext
    · simp [c, r, AffineSpace.homOfVector_over, AffineSpace.reindex_over]
    · intro i
      rw [comp_appTop_apply, AffineSpace.reindex_appTop_coord]
      simp [c, AffineSpace.homOfVector_appTop_coord]
  have hci :=
    Stacks.AlgebraicGeometry.RelativeProjSeparated.isClosedImmersion_of_section r c hcr
  refine ⟨c, hci, fun hs ↦ ?_, AffineSpace.homOfVector_over _ _⟩
  have : Surjective c := ⟨hs⟩
  have := isIso_of_isClosedImmersion_of_surjective c
  have hrc : r ≫ c = 𝟙 _ := by
    rw [← IsIso.inv_eq_of_hom_inv_id hcr]
    exact IsIso.inv_hom_id c
  have h0 : AffineSpace.coord (Spec (.of k)) (none : Option m) = 0 := by
    have := congrArg (fun φ ↦ φ.appTop (AffineSpace.coord (Spec (.of k)) (none : Option m))) hrc
    simp only [comp_appTop_apply, c, AffineSpace.homOfVector_appTop_coord, Option.elim_none,
      map_zero] at this
    simpa using this.symm
  let t : Spec (.of k) ⟶ 𝔸(Option m; Spec (.of k)) := AffineSpace.homOfVector (𝟙 _) fun _ ↦ 1
  have := congrArg t.appTop h0
  rw [AffineSpace.homOfVector_appTop_coord, map_zero] at this
  exact one_ne_zero this

/-- **Every affine disjoint union of varieties has an admissible embedding**: into an affine
space, with two extra coordinates to make room for codimension `2`. -/
private theorem exists_isAdmissibleEmbedding {k : Type u} [Field k] [CharZero k]
    {Y : Scheme.{u}} [IsAffine Y] (sY : Y ⟶ Spec (.of k)) (hY : IsDisjointUnionOfVarieties sY) :
    ∃ (A : Scheme.{u}) (sA : A ⟶ Spec (.of k)) (i : Y ⟶ A),
      IsAdmissibleEmbedding sA i ∧ i ≫ sA = sY := by
  have : LocallyOfFiniteType sY := hY.1
  obtain ⟨n, _, j, hj, hjs⟩ := exists_isClosedImmersion_affineSpace_over sY
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

/-! ### The two pull-backs of `𝓑𝓡_{A'}(X')` to `X' ×_X X'` agree -/

/-- A scheme with a local isomorphism to a disjoint union of varieties is again one, provided it
is affine. -/
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
    Proof_lem_kr3f_br_open_cover.disjoint_of_forall_exists_isIrreducible
      (exists_isOpen_isIrreducible_of_isLocalIso f
        (Proof_lem_kr3f_br_open_cover.exists_isIrreducible_of_disjoint hX.2.2.2.2))⟩

/-- Let `q : X' → X` be a surjective local isomorphism to a disjoint union of varieties and
`X' ⊆ A'` an admissible embedding over `X`. Then `𝓑𝓡_{A'}(X')` has the same pull-back along both
projections `X' ×_X X' → X'`: each equals `𝓑𝓡_{A''}(X' ×_X X')` for an admissible embedding of the
affine scheme `X' ×_X X'`, the projections being smooth of relative dimension `0`, and there are no
empty blow-ups to delete. -/
private theorem embeddedResolution_pullback_fst_eq_pullback_snd {k : Type u} [Field k]
    {X X' A' : Scheme.{u}} {sX : X ⟶ Spec (.of k)} (hX : IsDisjointUnionOfVarieties sX)
    (q : X' ⟶ X) [IsLocalIso q] [Surjective q] {sA' : A' ⟶ Spec (.of k)} {i' : X' ⟶ A'}
    (h' : IsAdmissibleEmbedding sA' i') (hk : i' ≫ sA' = q ≫ sX) :
    (embeddedResolution sA' i').pullback (pullback.fst q q) =
      (embeddedResolution sA' i').pullback (pullback.snd q q) := by
  have : CharZero k := h'.1
  have : IsAffine X' := h'.2.1
  have : IsSeparated sX := hX.2.2.2.1
  have : IsAffineHom q := IsAffineHom.of_comp q sX
  have hpb := IsPullback.of_hasPullback q q
  have : IsAffineHom (pullback.fst q q) := MorphismProperty.of_isPullback hpb.flip ‹_›
  have : IsAffine (pullback q q) := isAffine_of_isAffineHom (pullback.fst q q)
  have : IsLocalIso (pullback.fst q q) := MorphismProperty.of_isPullback hpb.flip ‹_›
  have : IsLocalIso (pullback.snd q q) := MorphismProperty.of_isPullback hpb ‹_›
  have : Surjective (pullback.fst q q) := MorphismProperty.of_isPullback hpb.flip ‹_›
  have : Surjective (pullback.snd q q) := MorphismProperty.of_isPullback hpb ‹_›
  have := smoothOfRelativeDimension_zero_of_isLocalIso (pullback.fst q q)
  have := smoothOfRelativeDimension_zero_of_isLocalIso (pullback.snd q q)
  have := flat_of_isLocalIso (pullback.fst q q)
  have := flat_of_isLocalIso (pullback.snd q q)
  have : MorphismProperty.IsStableUnderComposition @IsLocalIso.{u} :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  have : IsLocalIso (pullback.fst q q ≫ q) := MorphismProperty.comp_mem _ _ _ ‹_› ‹_›
  obtain ⟨A'', sA'', i'', hadm, hover⟩ := exists_isAdmissibleEmbedding _
    (Category.assoc (pullback.fst q q) q sX ▸
      isDisjointUnionOfVarieties_comp_of_isLocalIso hX (pullback.fst q q ≫ q))
  have hBR := Proof_lem_kr3f_br_open_cover.hasNoEmptyBlowups_embeddedResolution sA' i'
  rw [← ClosedBlowupSequence.reduction_eq_self
      (ClosedBlowupSequence.hasNoEmptyBlowups_pullback _ hBR (pullback.fst q q)),
    ← embeddedResolution_eq_reduction_pullback_of_smoothOfRelativeDimension h' hadm 0
      (pullback.fst q q) (by rw [hover, hk]),
    embeddedResolution_eq_reduction_pullback_of_smoothOfRelativeDimension h' hadm 0
      (pullback.snd q q) (by rw [hover, hk, pullback.condition_assoc]),
    ClosedBlowupSequence.reduction_eq_self
      (ClosedBlowupSequence.hasNoEmptyBlowups_pullback _ hBR (pullback.snd q q))]

end Proof_lem_kr3f_br_glues

namespace MMP.Resolution

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology
open Proof_lem_kr3f_br_glues

universe u

/-- **Embedded resolutions of an affine cover glue** (Kollár Prop. 3.37): let `X` be a disjoint
union of varieties over `k`, `U : ι → X.Opens` a finite cover of `X` by affine opens, and
`q : ∐ U α ⟶ X` the morphism induced by the open immersions. For every admissible embedding
`i' : ∐ U α ⟶ A'` over `k` there is a unique blow-up sequence `G` of `X` with
`G.pullback q = embeddedResolution sA' i'`. -/
@[mmp "lem_kr3f_br_glues"]
public theorem existsUnique_pullback_sigmaDesc_eq_embeddedResolution {k : Type u} [Field k]
    {X A' : Scheme.{u}} {sX : X ⟶ Spec (.of k)} (hX : IsDisjointUnionOfVarieties sX)
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (hU : TopologicalSpace.IsOpenCover U)
    (hUa : ∀ α, IsAffineOpen (U α)) {sA' : A' ⟶ Spec (.of k)}
    {i' : (∐ fun α ↦ (U α).toScheme) ⟶ A'} (h' : IsAdmissibleEmbedding sA' i')
    (hk : i' ≫ sA' = Sigma.desc (fun α ↦ (U α).ι) ≫ sX) :
    ∃! G : ClosedBlowupSequence X,
      G.pullback (Sigma.desc fun α ↦ (U α).ι) = embeddedResolution sA' i' := by
  have := isLocalIso_sigmaDesc U
  have := surjective_sigmaDesc U hU
  have := flat_of_isLocalIso (Sigma.desc fun α ↦ (U α).ι)
  obtain ⟨G, hG⟩ := exists_pullback_eq_of_isLocalIso _ _
    (embeddedResolution_pullback_fst_eq_pullback_snd hX _ h' hk)
  exact ⟨G, hG, fun G' hG' ↦
    Kollar.eq_of_pullback_eq_of_flat_of_surjective _ (hG'.trans hG.symm)⟩

end MMP.Resolution

end
