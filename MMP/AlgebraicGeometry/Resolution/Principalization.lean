module

public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.Basic
public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.Sequence
public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.Functor
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.Monomial
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.Functor
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierWeilDivisor
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import StacksFrontier.AlgebraicGeometry.Blowup.ClassifyingMorphism

/-!
# Principalization and embedded resolution from order reduction (Kollár, *Resolution*, §3.f)

Kollár assembles the order reduction functors of 3.70 into an order reduction functor
`𝓑𝓜𝓞^can_m` in all dimensions (3.69, 3.70), builds the principalization functor
`𝓑𝓟^can = 𝓑𝓟_{𝓑𝓜𝓞^can_1}` from it (3.72), and resolves an affine disjoint union of varieties
`X` by principalizing its ideal sheaf in an ambient smooth scheme `A ⊇ X` and following the
pieces of `X` until the step at which they enter a center (p. 137, p. 146, Warning 3.23).

## Main definitions

* `MMP.Resolution.IsDisjointUnionOfVarieties`: schemes of finite type, reduced and separated, with
  pairwise disjoint irreducible components (Kollár 3.36).
* `MMP.Resolution.IsAdmissibleEmbedding`: closed embeddings `X ⊆ A` into a smooth equidimensional
  affine `A` in which every component of `X` has codimension `≥ 2`.
* `MMP.Resolution.assembledMarkedOrderReduction`: `𝓑𝓜𝓞^can_m`.
* `MMP.Resolution.canonicalPrincipalization`: `𝓑𝓟^can`.
* `MMP.Resolution.ClosedBlowupSequence.entryIndex`: the entry index `j_𝐁(η)`.
* `MMP.Resolution.embeddedResolutionSequence`: `𝓑𝓡_𝐁(X ⊆ A)`.
* `MMP.Resolution.embeddedResolution`: `𝓑𝓡_A(X)`.

## Implementation notes

Closed embeddings are closed immersions `i : X ⟶ A`, over `k` by `i ≫ s_A`; the ideal sheaf
`I_X` is `i.ker` and the restriction `𝐁|_X` is the pull-back along `i`. Disjoint unions of
schemes are Mathlib's coproducts (`Limits.Sigma.desc`), recorded, not restated.

"Codimension `≥ 2` in the irreducible component `T` of `A` containing it" is stated by a strict
chain `i(W) ⊊ Y₁ ⊊ Y₂ ⊆ T` of irreducible closed subsets (the irreducible closed subsets of the
closed set `T` are those of `A` contained in `T`).

The blow-up sequence `𝓑𝓡_𝐁(X ⊆ A) = (X_i, W_i)` is built by recursion along `𝐁`, carrying the
open `U_i ⊆ X_i` of the pieces `C` with `i < j_C` and a morphism `U_i → A_i`; the centre `W_i` is
the inverse image of `Z_i` in `U_i`, pushed to `X_i` (so it is empty on the frozen pieces, which
blow-up leaves unchanged up to the isomorphism `B_∅ ≅ id`). Which pieces are frozen at step `i` is
read off on `X` from `j_C`, computed once on the base. `𝓑𝓟^can` is defined on
the snc triples of 3.35; `embeddedResolution` takes the empty sequence when `(A, I_X, ∅)` is not
one (it always is for an admissible embedding).

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.36, 3.69–3.72, pp. 137, 146]
-/

@[expose] public noncomputable section

open CategoryTheory hiding ConnectedComponents
open AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Resolution

/-! ### Disjoint unions of varieties and admissible embeddings -/

section DisjointUnion

variable {k : Type u} [Field k] {X A : Scheme.{u}}

/-- A scheme `X` of finite type over a field `k` is a *disjoint union of varieties* (Kollár 3.36):
`X` is reduced and separated over `k` and its irreducible components are pairwise disjoint. -/
@[mmp "def_kr3f_disjoint_union_of_varieties"]
def IsDisjointUnionOfVarieties (sX : X ⟶ Spec (.of k)) : Prop :=
  LocallyOfFiniteType sX ∧ QuasiCompact sX ∧ IsReduced X ∧ IsSeparated sX ∧
    ∀ C ∈ irreducibleComponents X, ∀ C' ∈ irreducibleComponents X, C ≠ C' → Disjoint C C'

section Coproduct

open CategoryTheory.Limits

/-- The canonical morphism `Y a ×_{⊤} Y b ⟶ (∐ Y) ×_{⊤} (∐ Y)`. -/
private noncomputable def sigmaTerminalPullbackMap {σ : Type u} (Y : σ → Scheme.{u}) (a b : σ) :
    pullback (Sigma.ι Y a ≫ terminal.from (∐ Y)) (Sigma.ι Y b ≫ terminal.from (∐ Y)) ⟶
      pullback (terminal.from (∐ Y)) (terminal.from (∐ Y)) :=
  pullback.map _ _ _ _ (Sigma.ι Y a) (Sigma.ι Y b) (𝟙 _) (Category.comp_id _) (Category.comp_id _)

private theorem isSeparated_sigma {σ : Type u} (Y : σ → Scheme.{u})
    (hY : ∀ j, (Y j).IsSeparated) : (∐ Y).IsSeparated := by
  refine ⟨⟨?_⟩⟩
  refine IsZariskiLocalAtTarget.of_openCover
    (Scheme.Pullback.openCoverOfLeftRight (sigmaOpenCover Y) (sigmaOpenCover Y)
      (terminal.from (∐ Y)) (terminal.from (∐ Y))) ?_
  rintro ⟨a, b⟩
  change IsClosedImmersion
    (pullback.snd (pullback.diagonal (terminal.from (∐ Y))) (sigmaTerminalPullbackMap Y a b))
  by_cases hab : a = b
  · subst hab
    have hoi : IsOpenImmersion (Sigma.ι Y a) := (sigmaOpenCover Y).map_prop a
    have hd : IsClosedImmersion (pullback.diagonal (terminal.from (Y a))) :=
      (hY a).isSeparated_terminal_from.isClosedImmersion_diagonal
    rwa [← terminal.comp_from (Sigma.ι Y a), pullback.diagonal_comp,
      MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion,
      MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion] at hd
  · have he : IsEmpty ↑(pullback (pullback.diagonal (terminal.from (∐ Y)))
        (sigmaTerminalPullbackMap Y a b)) :=
      ⟨fun x ↦ (isEmpty_pullback_sigmaι_of_ne Y hab).elim
        ((pullbackDiagonalMapIdIso (Sigma.ι Y a) (Sigma.ι Y b) (terminal.from (∐ Y))).hom x)⟩
    infer_instance

private theorem exists_eq_openComponent_of_mem_irreducibleComponents
    (U : ConnectedComponents X → X.Opens)
    (hU : ∀ c, (U c : Set X) = ConnectedComponents.mk ⁻¹' {c}) (hint : ∀ c, IsIntegral (U c))
    {C : Set X} (hC : C ∈ irreducibleComponents X) : ∃ c, C = (U c : Set X) := by
  obtain ⟨x, hx⟩ := hC.1.nonempty
  refine ⟨ConnectedComponents.mk x, hC.eq_of_le ?_ ?_⟩
  · have h := (IrreducibleSpace.isIrreducible_univ (U (ConnectedComponents.mk x))).image
      (U (ConnectedComponents.mk x)).ι.base.hom
      (U (ConnectedComponents.mk x)).ι.base.hom.continuous.continuousOn
    rwa [Set.image_univ, Scheme.Opens.range_ι] at h
  · rw [hU, connectedComponents_preimage_singleton]
    exact hC.1.2.isPreconnected.subset_connectedComponent hx

private theorem isReduced_and_isSeparated_and_disjoint_of_openComponents (sX : X ⟶ Spec (.of k))
    (U : ConnectedComponents X → X.Opens)
    (hU : ∀ c, (U c : Set X) = ConnectedComponents.mk ⁻¹' {c})
    (hvar : ∀ c, IsVariety k ((U c).ι ≫ sX))
    (hiso : IsIso (Limits.Sigma.desc fun c => (U c).ι)) :
    IsReduced X ∧ IsSeparated sX ∧
      ∀ C ∈ irreducibleComponents X, ∀ C' ∈ irreducibleComponents X, C ≠ C' → Disjoint C C' := by
  have hint : ∀ c, IsIntegral (U c) := fun c => (hvar c).toIsIntegral
  have hcov : iSup U = ⊤ := by
    rw [eq_top_iff]
    intro x _
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨ConnectedComponents.mk x, ?_⟩
    change x ∈ (U (ConnectedComponents.mk x) : Set X)
    rw [hU]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [IsReduced.iff_of_openCover X (X.openCoverOfIsOpenCover U hcov)]
    intro c
    have := hint c
    exact isReduced_of_isIntegral (U c).toScheme
  · have hs : ∀ c, Scheme.IsSeparated (U c).toScheme := fun c => by
      have := (hvar c).toIsSeparated
      refine ⟨?_⟩
      have : ((U c).ι ≫ sX) ≫ terminal.from (Spec (.of k)) = terminal.from (U c).toScheme :=
        Subsingleton.elim _ _
      rw [← this]
      infer_instance
    have h1 := isSeparated_sigma (fun c => (U c).toScheme) hs
    have h2 := Scheme.IsSeparated.of_iso (asIso (Limits.Sigma.desc fun c => (U c).ι))
    have h3 : IsSeparated (sX ≫ terminal.from (Spec (.of k))) := by
      have : sX ≫ terminal.from (Spec (.of k)) = terminal.from X := Subsingleton.elim _ _
      rw [this]
      exact h2.isSeparated_terminal_from
    exact IsSeparated.of_comp sX (terminal.from _)
  · intro C hC C' hC' hne
    obtain ⟨c, rfl⟩ := exists_eq_openComponent_of_mem_irreducibleComponents U hU hint hC
    obtain ⟨c', rfl⟩ := exists_eq_openComponent_of_mem_irreducibleComponents U hU hint hC'
    have : c ≠ c' := fun h => hne (by rw [h])
    rw [hU, hU]
    exact Set.disjoint_left.mpr fun x h1 h2 => this (h1.symm.trans h2)

private theorem isClopen_of_mem_irreducibleComponents_of_pairwise_disjoint
    {Y : Type*} [TopologicalSpace Y] (hfin : (irreducibleComponents Y).Finite)
    (hdisj : ∀ C ∈ irreducibleComponents Y, ∀ C' ∈ irreducibleComponents Y, C ≠ C' →
      Disjoint C C')
    {C : Set Y} (hC : C ∈ irreducibleComponents Y) : IsClopen C := by
  refine ⟨isClosed_of_mem_irreducibleComponents C hC, ?_⟩
  have hcompl : Cᶜ = ⋃ C' ∈ {C' | C' ∈ irreducibleComponents Y ∧ C' ≠ C}, C' := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro hx
      obtain ⟨C', hC', hxC'⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {x}
        isIrreducible_singleton
      exact ⟨C', ⟨hC', fun h => hx (h ▸ hxC' rfl)⟩, hxC' rfl⟩
    · rintro ⟨C', ⟨hC', hne⟩, hx'⟩ hx
      exact Set.disjoint_left.mp (hdisj C' hC' C hC hne) hx' hx
  rw [← isClosed_compl_iff, hcompl]
  exact (hfin.subset fun C' hC' => hC'.1).isClosed_biUnion fun C' hC' =>
    isClosed_of_mem_irreducibleComponents C' hC'.1

private theorem exists_connectedComponent_eq_of_pairwise_disjoint
    {Y : Type*} [TopologicalSpace Y] (hfin : (irreducibleComponents Y).Finite)
    (hdisj : ∀ C ∈ irreducibleComponents Y, ∀ C' ∈ irreducibleComponents Y, C ≠ C' →
      Disjoint C C') (x : Y) :
    ∃ C ∈ irreducibleComponents Y, connectedComponent x = C := by
  obtain ⟨C, hC, hxC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {x}
    isIrreducible_singleton
  have hCl := isClopen_of_mem_irreducibleComponents_of_pairwise_disjoint hfin hdisj hC
  exact ⟨C, hC, le_antisymm (hCl.connectedComponent_subset (hxC rfl))
    (hC.1.2.isPreconnected.subset_connectedComponent (hxC rfl))⟩

private theorem exists_openComponents_of_disjoint (sX : X ⟶ Spec (.of k))
    (hlft : LocallyOfFiniteType sX) (hqc : QuasiCompact sX) (hred : IsReduced X)
    (hsep : IsSeparated sX)
    (hdisj : ∀ C ∈ irreducibleComponents X, ∀ C' ∈ irreducibleComponents X, C ≠ C' →
      Disjoint C C') :
    ∃ U : ConnectedComponents X → X.Opens,
        (∀ c, (U c : Set X) = ConnectedComponents.mk ⁻¹' {c}) ∧
        (∀ c, IsVariety k ((U c).ι ≫ sX)) ∧
        IsIso (Limits.Sigma.desc fun c => (U c).ι) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : AlgebraicGeometry.IsNoetherian X := {}
  have hfin := NoetherianSpace.finite_irreducibleComponents (α := X)
  have hopen : ∀ c : ConnectedComponents X, IsOpen (ConnectedComponents.mk ⁻¹' {c}) := by
    intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    obtain ⟨C, hC, h1⟩ := exists_connectedComponent_eq_of_pairwise_disjoint hfin hdisj x
    rw [connectedComponents_preimage_singleton, h1]
    exact (isClopen_of_mem_irreducibleComponents_of_pairwise_disjoint hfin hdisj hC).isOpen
  have hirr : ∀ c : ConnectedComponents X,
      IsIrreducible (ConnectedComponents.mk ⁻¹' {c} : Set X) := by
    intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    obtain ⟨C, hC, h1⟩ := exists_connectedComponent_eq_of_pairwise_disjoint hfin hdisj x
    rw [connectedComponents_preimage_singleton, h1]
    exact hC.1
  let V : ConnectedComponents X → X.Opens := fun c => ⟨_, hopen c⟩
  have hVint : ∀ c, IsIntegral (V c) := fun c => by
    have : IrreducibleSpace (V c) := (irreducibleSpace_def _).mpr
      ((isIrreducible_iff_irreducibleSpace (s := (ConnectedComponents.mk ⁻¹' {c} : Set X))).mp
        (hirr c)).isIrreducible_univ
    exact isIntegral_of_irreducibleSpace_of_isReduced _
  have hdisjV : Pairwise (Function.onFun Disjoint fun c => (V c).ι.opensRange) := by
    intro c c' hcc'
    simp only [Function.onFun, Scheme.Opens.opensRange_ι]
    rw [disjoint_iff, Opens.ext_iff]
    ext x
    simp only [V, Opens.coe_inf, Set.mem_inter_iff,
      Opens.coe_bot, Set.mem_empty_iff_false, iff_false, not_and]
    intro h1 h2
    exact hcc' (h1.symm.trans h2)
  have hcovV : ⨆ c, (V c).ι.opensRange = ⊤ := by
    rw [eq_top_iff]
    intro x _
    refine Opens.mem_iSup.mpr ⟨ConnectedComponents.mk x, ?_⟩
    simp [V]
  refine ⟨V, fun c => rfl, ?_, ?_⟩
  · intro c
    have := hVint c
    have : QuasiCompact (V c).ι := by
      have : NoetherianSpace (V c) := NoetherianSpace.set (V c : Set X)
      infer_instance
    exact { toIsIntegral := hVint c }
  · exact (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc (Cofan.mk X fun c => (V c).ι)).mp
      (nonempty_isColimit_cofanMk_of _ hcovV hdisjV)

end Coproduct

/-- Equivalently (Kollár 3.36), for `X` of finite type over `k`: the connected components `C` of
`X` are open subschemes which are varieties over `k`, and `X = ⨆_C C`, the canonical morphism
`∐_C C → X` being an isomorphism. -/
@[mmp "def_kr3f_disjoint_union_of_varieties"]
theorem isDisjointUnionOfVarieties_iff (sX : X ⟶ Spec (.of k)) :
    IsDisjointUnionOfVarieties sX ↔ LocallyOfFiniteType sX ∧ QuasiCompact sX ∧
      ∃ U : ConnectedComponents X → X.Opens,
        (∀ c, (U c : Set X) = ConnectedComponents.mk ⁻¹' {c}) ∧
        (∀ c, IsVariety k ((U c).ι ≫ sX)) ∧
        IsIso (Limits.Sigma.desc fun c => (U c).ι) :=
  ⟨fun ⟨hlft, hqc, hred, hsep, hdisj⟩ =>
      ⟨hlft, hqc, exists_openComponents_of_disjoint sX hlft hqc hred hsep hdisj⟩,
    fun ⟨hlft, hqc, U, hU, hvar, hiso⟩ =>
      ⟨hlft, hqc,
        isReduced_and_isSeparated_and_disjoint_of_openComponents sX U hU hvar hiso⟩⟩

/-- A closed immersion `i : X ⟶ A` is an *admissible embedding* of `X` (Kollár p. 146, "any
embedding `X ↪ A` such that `dim A ≥ dim X + 2`"), `X` being over `k` by `i ≫ s_A`: `k` has
characteristic `0`, `X` is an affine disjoint union of varieties, `A` is affine, smooth and
equidimensional over `k`, and every irreducible component `W` of `X` has codimension `≥ 2` in the
irreducible component `T` of `A` containing it, i.e. there is a strict chain `i(W) ⊊ Y₁ ⊊ Y₂ ⊆ T`
of irreducible closed subsets. -/
@[mmp "def_kr3f_admissible_embedding"]
def IsAdmissibleEmbedding (sA : A ⟶ Spec (.of k)) (i : X ⟶ A) : Prop :=
  CharZero k ∧ IsAffine X ∧ IsDisjointUnionOfVarieties (i ≫ sA) ∧ IsClosedImmersion i ∧
    IsAffine A ∧ MMP.Mori.IsSmoothScheme sA ∧ TopologicalSpace.Equidimensional A ∧
    ∀ W ∈ irreducibleComponents X, ∀ T ∈ irreducibleComponents A, i.base '' W ⊆ T →
      ∃ Y₁ Y₂ : IrreducibleCloseds A,
        i.base '' W ⊂ (Y₁ : Set A) ∧ (Y₁ : Set A) ⊂ Y₂ ∧ (Y₂ : Set A) ⊆ T

end DisjointUnion

/-! ### The canonical order reduction and principalization functors -/

/-- The *order reduction functor in all dimensions* `𝓑𝓜𝓞^can_m` (Kollár 3.69, 3.70): it sends a
marked triple `(X, I, m, E)` to `𝓑𝓜𝓞_{dim X, m}(X, I, m, E)`, `(𝓑𝓜𝓞_{n,μ})` the canonical family
of 3.70. (Meant for `m ≥ 1`.) -/
@[mmp "def_kr3f_assembled_marked_order_reduction"]
def assembledMarkedOrderReduction (m : ℕ) :
    BlowupSequenceFunctor MarkedTriple.toTriple (markedTriplesOfMarking.{u} m) :=
  fun t _ => bmoFamily (dimNat t.X) m t

/-- The *principalization functor* `𝓑𝓟^can = 𝓑𝓟_{𝓑𝓜𝓞^can_1}` (Kollár 3.72): the construction of
3.72 applied to `𝓑𝓜𝓞^can_1`, on the snc triples `(X, I, E)` of 3.35. -/
@[mmp "def_kr3f_canonical_principalization"]
def canonicalPrincipalization : SNCBlowupSequenceFunctor.{u} :=
  principalizationConstruction (assembledMarkedOrderReduction 1)

/-- `𝓑𝓟^can` is defined on all triples `(X, I, E)` (Kollár 3.72): `X` smooth equidimensional of
finite type over a field of characteristic `0`, `I` nonzero on every irreducible component and `E`
an snc divisor; these are snc triples. -/
@[mmp "def_kr3f_canonical_principalization"]
theorem triples_subset_sncTriples : triples.{u} ⊆ sncTriples.{u} := by
  rintro t ⟨h0, h1, h2, h3, -, h5, h6, h7⟩
  exact ⟨h0, h1, h2, h3, h5, h6, h7⟩

/-! ### The entry index -/

namespace ClosedBlowupSequence

open Classical in
/-- `j_𝐁(S)` for a subset `S ⊆ X`: the least `i < r` with `Z_i ∩ Π_i⁻¹(S) ≠ ∅`, and `r` if there is
none. -/
def entryIndexOfSet : {X : Scheme.{u}} → ClosedBlowupSequence X → Set X → ℕ
  | _, nil _, _ => 0
  | _, cons Z B, S =>
    if ((Z.support : Set _) ∩ S).Nonempty then 0
    else B.entryIndexOfSet (blowUpToBase Z ⁻¹' S) + 1

/-- The *entry index* of a point `η ∈ X` for a blow-up sequence `𝐁 = (X_i, Z_i)_{i ≤ r}` starting
with `X` (Kollár p. 137): `j_𝐁(η) = min {i < r : Z_i ∩ Π_i⁻¹(η) ≠ ∅}`, and `j_𝐁(η) = r` if no
center meets the fibre of `Π_i` over `η`. -/
@[mmp "def_kr3f_entry_index"]
def entryIndex {X : Scheme.{u}} (B : ClosedBlowupSequence X) (η : X) : ℕ :=
  B.entryIndexOfSet {η}

/-- The entry index of a set is at most the length `r`. -/
theorem entryIndexOfSet_le_length {X : Scheme.{u}} (B : ClosedBlowupSequence X) (S : Set X) :
    B.entryIndexOfSet S ≤ B.length := by
  induction B with
  | nil X => simp [entryIndexOfSet]
  | cons Z B ih =>
    simp only [entryIndexOfSet, length]
    split_ifs
    · omega
    · have := ih (blowUpToBase Z ⁻¹' S)
      omega

/-- The entry index is at most the length `r`. -/
@[mmp "def_kr3f_entry_index"]
theorem entryIndex_le_length {X : Scheme.{u}} (B : ClosedBlowupSequence X) (η : X) :
    B.entryIndex η ≤ B.length :=
  B.entryIndexOfSet_le_length _

end ClosedBlowupSequence

/-! ### The blow-up sequence induced by an ambient sequence -/

section Embedded

variable {X A : Scheme.{u}}

/-- `r_X = max_C j_C`, the largest entry index `j_𝐁(η_C)` of the generic points `η_C` of the
connected components `C` of `X` (`0` if `X = ∅`). -/
@[mmp "def_kr3f_embedded_resolution_sequence"]
def embeddedResolutionLength (B : ClosedBlowupSequence A) (i : X ⟶ A) : ℕ :=
  sSup {j | ∃ η : X, connectedComponent η ⊆ closure {η} ∧ j = B.entryIndex (i.base η)}

open Classical in
/-- The entry index `j_C = j_𝐁(i(η_C))` of the connected component `C` of `x ∈ X`, `η_C` its
generic point (chosen; `x` itself if `C` has none). -/
@[mmp "def_kr3f_embedded_resolution_sequence"]
def componentEntryIndex (B : ClosedBlowupSequence A) (i : X ⟶ A) (x : X) : ℕ :=
  if h : ∃ η ∈ connectedComponent x, connectedComponent x ⊆ closure {η} then
    B.entryIndex (i.base h.choose)
  else B.entryIndex (i.base x)

open Classical in
/-- The open set of points of `X` on the connected components `C` that are not yet frozen at step
`n`, i.e. with `n < j_C` (`⊥` if this set is not open; it is open when `X` has finitely many
connected components). -/
@[mmp "def_kr3f_embedded_resolution_sequence"]
def activeLocus (B : ClosedBlowupSequence A) (i : X ⟶ A) (n : ℕ) : X.Opens :=
  if h : IsOpen {x : X | n < componentEntryIndex B i x} then ⟨_, h⟩ else ⊥

namespace ClosedBlowupSequence

open Classical in
/-- The recursion behind `𝓑𝓡_𝐁(X ⊆ A)`. At step `n` the state is the scheme `Y = X_n` with
`p : X_n → X`, the open `U ⊆ X_n` of the pieces not yet frozen, and `h : U → A_n`; the remaining
ambient sequence is `𝐂 = (A_n, Z_n, …)`. For `𝐂 = cons Z 𝐂'` the centre is
`W_n = h⁻¹Z_n ⊆ U`, as a closed subscheme of `X_n` (its scheme-theoretic image along `U ↪ X_n`;
empty on the frozen pieces, so these are left unchanged), `X_{n+1} = B_{W_n}X_n`, the new open is
the part of `π_n⁻¹(U)` over the pieces with `n + 1 < j_C`, and `h` is lifted to
`A_{n+1} = B_{Z_n}A_n` (when the inverse image of `Z_n` there is Cartier, as it is in the source's
setting; otherwise the sequence stops). -/
def embeddedAux (act : ℕ → X.Opens) : {A' : Scheme.{u}} → ClosedBlowupSequence A' → ℕ →
    (Y : Scheme.{u}) → (Y ⟶ X) → (U : Y.Opens) → (U.toScheme ⟶ A') → ClosedBlowupSequence Y
  | _, nil _, _, Y, _, _, _ => nil Y
  | _, cons Z C, n, _, p, U, h =>
    let W := (Z.comap h).map U.ι
    let p' := blowUpToBase W ≫ p
    let U' := blowUpToBase W ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ act (n + 1)
    let g : U'.toScheme ⟶ _ := (blowUpToBase W).resLE U U' inf_le_left ≫ h
    if hc : Stacks.Blowup.IsCartierOver Z (Over.mk g) then
      cons W (embeddedAux act C (n + 1) _ p' U' (blowUpLift Z g hc))
    else cons W (nil _)

end ClosedBlowupSequence

/-- The blow-up sequence `𝓑𝓡_𝐁(X ⊆ A) = (X_i, W_i)` of `X` induced by a blow-up sequence
`𝐁 = (A_i, Z_i)_{i ≤ r}` of `A` (Kollár p. 146 and Warning 3.23), for a closed subscheme
`i : X ↪ A` that is a disjoint union of varieties: for each connected component `C` of `X`, with
generic point `η_C`, `j_C = j_𝐁(η_C)` and `𝐁|_C = (C_i, Z_i ∩ C_i)`, it has length
`r_X = max_C j_C`, `i`-th scheme `X_i = ⨆_C C_{min(i, j_C)}` and `i`-th centre
`W_i = ⨆_{C : i < j_C} (Z_i ∩ C_i)`; thus `B_{W_i}X_i = X_{i+1}`, the pieces with `i ≥ j_C` being
left unchanged. Built by `ClosedBlowupSequence.embeddedAux` from `X_0 = X`, `U_0` the pieces with
`0 < j_C` and `h_0 = i|_{U_0}`, truncated at `r_X`. -/
@[mmp "def_kr3f_embedded_resolution_sequence"]
def embeddedResolutionSequence (B : ClosedBlowupSequence A) (i : X ⟶ A) :
    ClosedBlowupSequence X :=
  (ClosedBlowupSequence.embeddedAux (activeLocus B i) B 0 X (𝟙 X) (activeLocus B i 0)
    ((activeLocus B i 0).ι ≫ i)).truncate (embeddedResolutionLength B i)

private theorem isNoetherian_blowUp {Y : Scheme.{u}} [AlgebraicGeometry.IsNoetherian Y]
    (W : Y.IdealSheafData) : AlgebraicGeometry.IsNoetherian (blowUp W) :=
  have : IsLocallyNoetherian (blowUp W) := LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase W)
  have : CompactSpace (blowUp W) := QuasiCompact.compactSpace_of_compactSpace (blowUpToBase W)
  {}

private theorem isCartierOver_resLE {Y A' : Scheme.{u}} [AlgebraicGeometry.IsNoetherian Y]
    (U : Y.Opens) (h : U.toScheme ⟶ A') (Z : A'.IdealSheafData)
    (U' : (blowUp ((Z.comap h).map U.ι)).Opens)
    (hle : U' ≤ blowUpToBase ((Z.comap h).map U.ι) ⁻¹ᵁ U) :
    Stacks.Blowup.IsCartierOver Z
      (Over.mk ((blowUpToBase ((Z.comap h).map U.ι)).resLE U U' hle ≫ h)) := by
  have hq : QuasiCompact U.ι := by
    have : NoetherianSpace U := TopologicalSpace.NoetherianSpace.set (U : Set Y)
    infer_instance
  have h1 : (Z.comap h) = ((Z.comap h).map U.ι).comap U.ι :=
    (ClosedBlowupSequence.comap_map_eq_of_isOpenImmersion U.ι (Z.comap h)).symm
  change Stacks.Divisors.IsEffectiveCartierDivisor
    (Z.comap (((blowUpToBase ((Z.comap h).map U.ι)).resLE U U' hle) ≫ h))
  rw [Scheme.IdealSheafData.comap_comp,
    congrArg (fun J => J.comap ((blowUpToBase ((Z.comap h).map U.ι)).resLE U U' hle)) h1,
    ← Scheme.IdealSheafData.comap_comp, Scheme.Hom.resLE_comp_ι,
    Scheme.IdealSheafData.comap_comp]
  exact Stacks.Blowup.isEffectiveCartierDivisor_comap_of_isOpenImmersion _
    (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal _) _

open ClosedBlowupSequence in
private theorem length_le_length_embeddedAux {X : Scheme.{u}} (act : ℕ → X.Opens) {A' : Scheme.{u}}
    (C : ClosedBlowupSequence A') : ∀ (n : ℕ) (Y : Scheme.{u}) [AlgebraicGeometry.IsNoetherian Y]
    (p : Y ⟶ X) (U : Y.Opens) (h : U.toScheme ⟶ A'),
    C.length ≤ (embeddedAux act C n Y p U h).length := by
  induction C with
  | nil _ =>
    intro n Y _ p U h
    simp [embeddedAux, length]
  | cons Z C ih =>
    intro n Y _ p U h
    rw [embeddedAux.eq_2,
      dite_eq_left_of_eq_true (eq_true (isCartierOver_resLE U h Z _ inf_le_left))]
    have := isNoetherian_blowUp ((Z.comap h).map U.ι)
    exact Nat.succ_le_succ (ih _ _ _ _ _)

open ClosedBlowupSequence in
private theorem length_truncate {X : Scheme.{u}} (B : ClosedBlowupSequence X) (i : ℕ) :
    (B.truncate i).length = min i B.length := by
  induction B generalizing i with
  | nil _ => simp [truncate, length]
  | cons Z B ih =>
    cases i with
    | zero => simp [truncate, length]
    | succ i =>
      simp only [truncate, length, ih]
      omega

/-- For `A` of finite type over a field and a closed subscheme `i : X ↪ A`, `𝓑𝓡_𝐁(X ⊆ A)` has
length `r_X = max_C j_C`. -/
@[mmp "def_kr3f_embedded_resolution_sequence"]
theorem length_embeddedResolutionSequence {k : Type u} [Field k]
    (sA : A ⟶ Spec (.of k)) [LocallyOfFiniteType sA] [QuasiCompact sA] (i : X ⟶ A)
    [IsClosedImmersion i] (B : ClosedBlowupSequence A) :
    (embeddedResolutionSequence B i).length = embeddedResolutionLength B i := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (i ≫ sA)
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (i ≫ sA)
  have : AlgebraicGeometry.IsNoetherian X := {}
  have hr : embeddedResolutionLength B i ≤ B.length := by
    refine csSup_le' ?_
    rintro j ⟨η, -, rfl⟩
    exact B.entryIndex_le_length _
  have hge := length_le_length_embeddedAux (activeLocus B i) B 0 X (𝟙 X) (activeLocus B i 0)
    ((activeLocus B i 0).ι ≫ i)
  rw [embeddedResolutionSequence, length_truncate]
  omega

end Embedded

/-! ### Embedded resolution of affine disjoint unions of varieties -/

section EmbeddedResolution

variable {k : Type u} [Field k] {X A : Scheme.{u}}

private theorem smooth_of_isSmoothScheme {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : MMP.Mori.IsSmoothScheme f) : Smooth f := by
  have hc : iSup (fun U : {U : X.Opens // Smooth (U.ι ≫ f)} => (U.1 : X.Opens)) = ⊤ := by
    rw [MMP.Mori.IsSmoothScheme, MMP.Mori.smoothLocus] at h
    rw [← h, sSup_eq_iSup']
    exact le_antisymm (iSup_le fun _ => le_iSup _ _) (iSup_le fun _ => le_iSup _ _)
  have : IsZariskiLocalAtSource @Smooth.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth)
  rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @Smooth) _ hc]
  exact fun U => U.2

/-- The snc triple `(A, I_X, ∅)` of a closed immersion `i : X ⟶ A`, `A` over `k`. -/
@[mmp "def_kr3f_embedded_resolution"]
def embeddingTriple (sA : A ⟶ Spec (.of k)) (i : X ⟶ A) : FieldBlowupTriple.{u} :=
  ⟨⟨A, i.ker, OrderedDivisor.empty A⟩, k, sA⟩

open Classical in
/-- `𝓑𝓡_A(X)` for an admissible embedding `X ⊆ A` (Kollár p. 146):
`𝓑𝓡_A(X) = (𝓑𝓡_𝐁(X ⊆ A))^red` with `𝐁 = 𝓑𝓟^can(A, I_X, ∅)` (the empty sequence if `(A, I_X, ∅)`
is not an snc triple). -/
@[mmp "def_kr3f_embedded_resolution"]
def embeddedResolution (sA : A ⟶ Spec (.of k)) (i : X ⟶ A) : ClosedBlowupSequence X :=
  if h : embeddingTriple sA i ∈ sncTriples then
    (embeddedResolutionSequence (canonicalPrincipalization _ h) i).reduction
  else .nil X

/-- For an admissible embedding `X ⊆ A`, `(A, I_X, ∅)` is an snc triple, so `𝓑𝓟^can(A, I_X, ∅)` is
defined. -/
@[mmp "def_kr3f_embedded_resolution"]
theorem embeddingTriple_mem_sncTriples {sA : A ⟶ Spec (.of k)} {i : X ⟶ A}
    (h : IsAdmissibleEmbedding sA i) : embeddingTriple sA i ∈ sncTriples := by
  obtain ⟨hchar, -, -, hclosed, hAaff, hsm, -, hcod⟩ := h
  have hsmooth : Smooth sA := smooth_of_isSmoothScheme sA hsm
  refine ⟨hchar, hsm, (inferInstance : LocallyOfFiniteType sA),
    (inferInstance : QuasiCompact sA), ?_, fun j => j.elim0, ?_⟩
  · intro η hη hbot
    have hsupp : η ∈ i.ker.support :=
      (IdealSheafData.stalk_le_maximalIdeal_iff_mem_support i.ker η).mp
        (by
          change IdealSheafData.stalk i.ker η = ⊥ at hbot
          rw [hbot]
          exact bot_le)
    have hrange : η ∈ Set.range i.base := by
      have h2 : η ∈ (i.ker.support : Set A) := hsupp
      rwa [Scheme.Hom.support_ker i, i.isClosedEmbedding.isClosed_range.closure_eq] at h2
    obtain ⟨x, rfl⟩ := hrange
    obtain ⟨W, hW, hxW⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
      (closure {x}) isIrreducible_singleton.closure
    have hxW' : x ∈ W := hxW (subset_closure rfl)
    have hirr : IsIrreducible (i.base '' W) :=
      (hW.1).image _ i.base.hom.continuous.continuousOn
    obtain ⟨T', hT', hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hirr
    have hηT' : i.base x ∈ T' := hsub ⟨x, hxW', rfl⟩
    have hTle : closure {i.base x} ⊆ T' :=
      closure_minimal (by simpa using hηT') (isClosed_of_mem_irreducibleComponents T' hT')
    have hTeq : closure {i.base x} = T' := hη.eq_of_le (hT'.1) hTle
    rw [← hTeq] at hsub
    obtain ⟨Y₁, Y₂, h1, h2, h3⟩ := hcod W hW _ hη hsub
    have hWcl : IsClosed (i.base '' W) :=
      i.isClosedEmbedding.isClosedMap _ (isClosed_of_mem_irreducibleComponents W hW)
    have : closure {i.base x} ⊆ i.base '' W :=
      closure_minimal (by simpa using ⟨x, hxW', rfl⟩) hWcl
    exact absurd (h1.trans_le (h2.le.trans h3)) (not_lt_of_ge this)
  · refine ⟨fun j => j.elim0, fun x => ?_⟩
    have := isRegularLocalRing_stalk_of_smooth_over_field sA x
    obtain ⟨n, z, hz⟩ := MMP.Mori.exists_isRegularSystemOfParameters (A.presheaf.stalk x)
    exact ⟨n, z, fun j => j.1.elim0, hz, fun j => j.1.elim0, fun j => j.1.elim0⟩

end EmbeddedResolution

end MMP.Resolution
