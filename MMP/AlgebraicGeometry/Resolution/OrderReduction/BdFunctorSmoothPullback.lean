module

public import MMP.AlgebraicGeometry.Resolution.OrderReduction.BdFunctorFieldChange

/-!
# The functor `𝓑𝓓_{n,m,j}`: smooth morphisms, closed embeddings and separation of `E^j`

Fix `N ≥ 1` and a marked order-reduction family `𝓜` on dimensions `0, …, N - 1`. For a triple
`(X, I, E)` of dimension `n ≤ N`, an index `j` and `m ≥ 1` with `maxord I ≤ m`, the blow-up
sequence `𝓑𝓓_{n,m,j}(X, I, E)` (`MMP.Resolution.bdFunctor`) first blows up the union `Z_{-1}` of
the components of `E^j` inside `cosupp(W_{m!}(I), m!)`, then pushes forward along the transform
`S ↪ B_Z X` of `E^j` the sequence `𝓜_{n-1,m!}(S, W_0𝒪_S, m!, E_S)`, and finally deletes the empty
blow-ups. This file proves three properties of it.

* It commutes with smooth morphisms on the class of triples with `1 ≤ dim X ≤ N`,
  `maxord I ≤ m` and `j < s`. The maximal coefficient ideals and the centres `Z_{-1}` on `X` and
  `Y` correspond, property (2a) of `𝓜` applies to the restrictions to `E^j` and `h⁻¹E^j`, and
  push-forward along a closed immersion commutes with flat pull-back.
* If `𝒪_X/I = τ_*(𝒪_S/J)` for the inclusion `τ : S = E^j ↪ X` and an ideal `J` nonzero at the
  generic points of `S`, then `𝓑𝓓_{n,1,j}(X, I, E) = τ_*𝓜_{n-1,1}(S, J, 1, (E^i ∩ S)_{i ≠ j})`.
  If `maxord I = 0` then `J = 𝒪_S` and both sides are empty. If `maxord I = 1` then
  `W_1(I) = I`, the centre `Z_{-1}` is empty and `W_0𝒪_S = J`.
* At the end `(X_r, I_r, E_r)` of `𝓑𝓓_{n,m,j}(X, I, E)`, the cosupport of `(I_r, m)` is disjoint
  from `E_r^j`. On the transform of `E^j` the restriction of `I_r` is the last ideal of
  `𝓜_{n-1,m!}`, whose maximal order is `< m!`.

## Main results

* `MMP.Resolution.bdFunctor_eq_pushforward_of_eq_map`: Kollár 3.102 (3).
* `MMP.Resolution.commutesWithSmoothOn_bdFunctor`: Kollár 3.102 (2).
* `MMP.Resolution.disjoint_cosupport_bdFunctor`: the separation property of Kollár 3.102.

## Implementation notes

The index `j` is `0`-based, so the source's `1 ≤ j ≤ s` is `j < s`. The file runs in four parts:
push-forward of blow-up sequences and its compatibility with flat pull-back, the closed-embedding
statement, the smooth-morphism statement, and the separation statement.

## References

* [J. Kollár, *Lectures on resolution of singularities*, Lemma 3.102 and its proof]
-/

public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Resolution

attribute [local instance] Bridges.isClosedImmersion_canonicalLift

/-! ### Push-forward of blow-up sequences along closed immersions -/

section Pushforward

open CategoryTheory.Limits ClosedBlowupSequence

private theorem isPushforward_unique : ∀ {S X : Scheme.{u}} (j : S ⟶ X)
    (BS : ClosedBlowupSequence S)
    (B1 B2 : ClosedBlowupSequence X), IsPushforward j BS B1 → IsPushforward j BS B2 → B1 = B2
  | _, _, _, .nil _, .nil _, .nil _, _, _ => rfl
  | _, _, _, .nil _, .nil _, .cons _ _, _, h => h.elim
  | _, _, _, .nil _, .cons _ _, _, h, _ => h.elim
  | _, _, j, .cons ZS BS, .cons Z1 B1, .cons Z2 B2, hP1, hP2 => by
    obtain ⟨h1, e1, p1⟩ := hP1
    obtain ⟨h2, e2, p2⟩ := hP2
    obtain rfl : Z1 = Z2 := e1.trans e2.symm
    rw [isPushforward_unique _ BS B1 B2 p1 p2]
  | _, _, _, .cons _ _, .nil _, _, h, _ => h.elim
  | _, _, _, .cons _ _, .cons _ _, .nil _, _, h => h.elim

private theorem exists_isPushforward : ∀ {S X : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j]
    (BS : ClosedBlowupSequence S), ∃ BX, IsPushforward j BS BX
  | _, _, _, _, .nil _ => ⟨.nil _, trivial⟩
  | _, _, j, _, .cons ZS BS => by
    have h : (ZS.map j).comap j = ZS := ZS.comap_map_of_isClosedImmersion j
    obtain ⟨BX, hBX⟩ :=
      exists_isPushforward (eqToHom (congrArg blowUp h.symm) ≫ canonicalLift j (ZS.map j)) BS
    exact ⟨.cons _ BX, h, rfl, hBX⟩

private theorem comap_map_eq_map_comap_of_isPullback {S X S' X' : Scheme.{u}} (j : S ⟶ X)
    [IsClosedImmersion j] (g : X' ⟶ X) (gS : S' ⟶ S) (j' : S' ⟶ X')
    (sq : IsPullback gS j' j g) (ZS : S.IdealSheafData) :
    (ZS.map j).comap g = (ZS.comap gS).map j' := by
  have sq1 : IsPullback (ZS.comap gS).subschemeι
      ((ZS.comapIso gS).hom ≫ pullback.snd gS ZS.subschemeι) gS ZS.subschemeι := by
    refine IsPullback.of_iso_pullback ⟨?_⟩ (ZS.comapIso gS) ?_ ?_
    · simp [pullback.condition]
    · simp
    · simp
  have sq3 := sq1.paste_horiz sq.flip
  rw [Scheme.IdealSheafData.map, Scheme.IdealSheafData.map,
    ← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion (ZS.subschemeι ≫ j) g]
  rw [← sq3.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

private theorem isPullback_canonicalLift_square {S X S' X' : Scheme.{u}} (j : S ⟶ X)
    (g : X' ⟶ X) [Flat g]
    (gS : S' ⟶ S) [Flat gS] (j' : S' ⟶ X') (sq : IsPullback gS j' j g) (ZX : X.IdealSheafData)
    (j'₁ : blowUp ((ZX.comap j).comap gS) ⟶ blowUp (ZX.comap g))
    (hj : j'₁ ≫ blowUpToBase (ZX.comap g) = blowUpToBase ((ZX.comap j).comap gS) ≫ j') :
    IsPullback (canonicalLift gS (ZX.comap j)) j'₁ (canonicalLift j ZX) (canonicalLift g ZX) := by
  have α := Kollar.isPullback_canonicalLift_of_flat gS (ZX.comap j)
  have β := Kollar.isPullback_canonicalLift_of_flat g ZX
  have hcart : Stacks.Blowup.IsCartierOver ZX
      (Over.mk (blowUpToBase ((ZX.comap j).comap gS) ≫ gS ≫ j)) := by
    change Stacks.Divisors.IsEffectiveCartierDivisor
      (ZX.comap (blowUpToBase ((ZX.comap j).comap gS) ≫ gS ≫ j))
    rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp]
    exact Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal _
  have w : canonicalLift gS (ZX.comap j) ≫ canonicalLift j ZX = j'₁ ≫ canonicalLift g ZX := by
    refine (blowUpLift_unique ZX _ hcart _ ?_).trans (blowUpLift_unique ZX _ hcart _ ?_).symm
    · rw [Category.assoc, canonicalLift_comp_blowUpToBase, ← Category.assoc,
        canonicalLift_comp_blowUpToBase, Category.assoc]
    · rw [Category.assoc, canonicalLift_comp_blowUpToBase, reassoc_of% hj, ← sq.w]
  have outer : IsPullback (canonicalLift gS (ZX.comap j)) (j'₁ ≫ blowUpToBase (ZX.comap g))
      (canonicalLift j ZX ≫ blowUpToBase ZX) g := by
    have := (α.paste_horiz sq.flip).flip
    rwa [hj, canonicalLift_comp_blowUpToBase]
  exact outer.of_bot w β.flip

private theorem isIso_blowUpToBase_of_eq_top {X : Scheme.{u}} {Z : X.IdealSheafData} (h : Z = ⊤) :
    IsIso (blowUpToBase Z) := by
  subst h; exact ClosedBlowupSequence.isIso_blowUpToBase_top X

private theorem blowUpLift_eq_inv_comp {X X' : Scheme.{u}} (Z : X.IdealSheafData) (g : X' ⟶ X)
    (hZ : Z.comap g = ⊤) [IsIso (blowUpToBase (Z.comap g))] :
    blowUpLift Z g (ClosedBlowupSequence.isCartierOver_of_comap_eq_top g Z hZ) =
      inv (blowUpToBase (Z.comap g)) ≫ canonicalLift g Z := by
  refine (blowUpLift_unique Z g _ _ ?_).symm
  rw [Category.assoc, canonicalLift_comp_blowUpToBase]
  simp

private theorem isPushforward_pullbackReduced : ∀ {S X : Scheme.{u}} (j : S ⟶ X)
    [IsClosedImmersion j]
    (BS : ClosedBlowupSequence S) (BX : ClosedBlowupSequence X), IsPushforward j BS BX →
    ∀ {S' X' : Scheme.{u}} (g : X' ⟶ X) [Flat g] (gS : S' ⟶ S) (j' : S' ⟶ X'),
      IsPullback gS j' j g →
      IsPushforward j' (BS.pullbackReduced gS) (BX.pullbackReduced g)
  | _, _, _, _, .nil _, .nil _, _, _, _, _, _, _, _, _ => trivial
  | _, _, _, _, .nil _, .cons _ _, hP, _, _, _, _, _, _, _ => hP.elim
  | _, _, _, _, .cons _ _, .nil _, hP, _, _, _, _, _, _, _ => hP.elim
  | _, _, j, _, .cons ZS BS, .cons ZX BX, hP, S', X', g, _, gS, j', sq => by
    obtain ⟨hc, hm, hP'⟩ := hP
    subst hc
    haveI : Flat gS := MorphismProperty.of_isPullback (P := @Flat) sq.flip inferInstance
    have hcomm : (ZX.comap j).comap gS = (ZX.comap g).comap j' := by
      rw [← Scheme.IdealSheafData.comap_comp, sq.w, Scheme.IdealSheafData.comap_comp]
    have hL1 : ZX.comap g = ((ZX.comap j).comap gS).map j' := by
      calc ZX.comap g = ((ZX.comap j).map j).comap g := by rw [← hm]
        _ = _ := comap_map_eq_map_comap_of_isPullback j g gS j' sq _
    have hiff : (ZX.comap g = ⊤) ↔ ((ZX.comap j).comap gS = ⊤) := by
      constructor
      · intro h; rw [hcomm, h]; simp
      · intro h; rw [hL1, h]; simp
    haveI : IsClosedImmersion (eqToHom (congrArg blowUp rfl) ≫ canonicalLift j ZX) := by
      rw [eqToHom_refl, Category.id_comp]; infer_instance
    simp only [eqToHom_refl, Category.id_comp] at hP'
    by_cases hZ : ZX.comap g = ⊤
    · have hZS := hiff.1 hZ
      simp only [ClosedBlowupSequence.pullbackReduced, hZ, hZS, dite_true]
      haveI hiX := isIso_blowUpToBase_of_eq_top hZ
      haveI hiS := isIso_blowUpToBase_of_eq_top hZS
      rw [blowUpLift_eq_inv_comp ZX g hZ, blowUpLift_eq_inv_comp (ZX.comap j) gS hZS]
      haveI : Flat (canonicalLift g ZX) := Kollar.flat_canonicalLift g ZX
      have hj : (blowUpToBase ((ZX.comap j).comap gS) ≫ j' ≫ inv (blowUpToBase (ZX.comap g))) ≫
          blowUpToBase (ZX.comap g) = blowUpToBase ((ZX.comap j).comap gS) ≫ j' := by simp
      have Q := isPullback_canonicalLift_square j g gS j' sq ZX _ hj
      refine isPushforward_pullbackReduced (canonicalLift j ZX) BS BX hP' _ _ j' ?_
      refine Q.of_iso (asIso (blowUpToBase ((ZX.comap j).comap gS))) (Iso.refl _)
        (asIso (blowUpToBase (ZX.comap g))) (Iso.refl _) ?_ ?_ ?_ ?_
      · simp
      · simp
      · simp
      · simp
    · have hZS : ¬ ((ZX.comap j).comap gS = ⊤) := fun h => hZ (hiff.2 h)
      simp only [ClosedBlowupSequence.pullbackReduced, hZ, hZS, dite_false]
      refine ⟨hcomm.symm, hL1, ?_⟩
      haveI : Flat (canonicalLift g ZX) := Kollar.flat_canonicalLift g ZX
      haveI : Flat (canonicalLift gS (ZX.comap j)) := Kollar.flat_canonicalLift gS (ZX.comap j)
      have hj : (eqToHom (congrArg blowUp hcomm) ≫
          canonicalLift j' (ZX.comap g)) ≫ blowUpToBase (ZX.comap g) =
          blowUpToBase ((ZX.comap j).comap gS) ≫ j' := by
        rw [Category.assoc, canonicalLift_comp_blowUpToBase, ← Category.assoc,
          ClosedBlowupSequence.eqToHom_comp_blowUpToBase hcomm]
      have Q := isPullback_canonicalLift_square j g gS j' sq ZX _ hj
      exact isPushforward_pullbackReduced (canonicalLift j ZX) BS BX hP' _ _ _ Q

private theorem pushforward_eq_of_isPushforward {S X : Scheme.{u}} (j : S ⟶ X)
    {B : ClosedBlowupSequence S}
    {B' : ClosedBlowupSequence X} (h : IsPushforward j B B') : B.pushforward j = B' := by
  have hex : ∃ B'', IsPushforward j B B'' := ⟨B', h⟩
  unfold ClosedBlowupSequence.pushforward
  rw [dif_pos hex]
  exact isPushforward_unique j B _ _ hex.choose_spec h

private theorem pushforward_pullbackReduced {S X S' X' : Scheme.{u}} (j : S ⟶ X)
    [IsClosedImmersion j]
    (g : X' ⟶ X) [Flat g] (gS : S' ⟶ S) (j' : S' ⟶ X') (sq : IsPullback gS j' j g)
    (BS : ClosedBlowupSequence S) :
    (BS.pullbackReduced gS).pushforward j' = (BS.pushforward j).pullbackReduced g := by
  obtain ⟨B, hB⟩ := exists_isPushforward j BS
  rw [pushforward_eq_of_isPushforward j hB]
  exact pushforward_eq_of_isPushforward j' (isPushforward_pullbackReduced j BS B hB g gS j' sq)

/-- The push-forward of the empty sequence is empty. -/
private theorem pushforward_nil {S X : Scheme.{u}} (j : S ⟶ X) :
    (ClosedBlowupSequence.nil S).pushforward j = .nil X :=
  pushforward_eq_of_isPushforward j (B' := .nil X) trivial

/-- The chosen push-forward along a closed immersion is a push-forward. -/
private theorem isPushforward_pushforward {S X : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j]
    (BS : ClosedBlowupSequence S) :
    ClosedBlowupSequence.IsPushforward j BS (BS.pushforward j) := by
  have h := exists_isPushforward j BS
  rw [ClosedBlowupSequence.pushforward, dif_pos h]
  exact h.choose_spec

end Pushforward

/-! ### Deleting the empty entries of an ordered divisor -/

section DeleteEmptyAux

variable {X : Scheme.{u}}

open Classical in
/-- The indices of the nonempty entries. -/
private noncomputable def flatIdx (E : OrderedDivisor X) : List (Fin E.s) :=
  (List.finRange E.s).filter fun i => E.E i ≠ ⊤

private theorem injective_flatIdx_get (E : OrderedDivisor X) :
    Function.Injective (flatIdx E).get :=
  List.nodup_iff_injective_get.1 ((List.nodup_finRange _).filter _)

private theorem exists_flatIdx_get (E : OrderedDivisor X) (i : Fin E.s) (hi : E.E i ≠ ⊤) :
    ∃ j, (flatIdx E).get j = i :=
  List.mem_iff_get.1 (by simp [flatIdx, hi])

section Reindex

variable {Λ Λ' : Type*} (E : Λ → X.IdealSheafData) (g : Λ' → Λ)

/-- A property of all entries may be checked on the nonempty ones. -/
private theorem forall_iff_forall_comp (hg : ∀ i, E i ≠ ⊤ → ∃ j, g j = i)
    (R : X.IdealSheafData → Prop) (hR : R ⊤) :
    (∀ i, R (E i)) ↔ ∀ j, R (E (g j)) := by
  refine ⟨fun h j => h _, fun h i => ?_⟩
  by_cases hi : E i = ⊤
  · rwa [hi]
  · obtain ⟨j, rfl⟩ := hg i hi
    exact h j

/-- The coordinate assignment of an snc family at a point may be taken over the nonempty
entries. -/
private theorem exists_coord_iff (hginj : Function.Injective g)
    (hg : ∀ i, E i ≠ ⊤ → ∃ j, g j = i) (x : X) {n : ℕ} (z : Fin n → X.presheaf.stalk x) :
    (∃ c : {i // x ∈ (E i).support} → Fin n,
        (∀ i, IdealSheafData.stalk (E i.1) x = Ideal.span {z (c i)}) ∧ Function.Injective c) ↔
      ∃ c : {j // x ∈ (E (g j)).support} → Fin n,
        (∀ j, IdealSheafData.stalk (E (g j.1)) x = Ideal.span {z (c j)}) ∧
          Function.Injective c := by
  let φ : {j // x ∈ (E (g j)).support} → {i // x ∈ (E i).support} := fun j => ⟨g j.1, j.2⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun a b hab => Subtype.ext (hginj (congrArg Subtype.val hab)), fun i => ?_⟩
    obtain ⟨j, hj⟩ := hg i.1 fun h => by
      have := i.2
      rwa [h, Scheme.IdealSheafData.support_top] at this
    exact ⟨⟨j, hj ▸ i.2⟩, Subtype.ext hj⟩
  let e := Equiv.ofBijective φ hφ
  refine ⟨fun ⟨c, hc, hinj⟩ => ⟨c ∘ φ, fun j => hc (φ j), hinj.comp hφ.1⟩, ?_⟩
  rintro ⟨c, hc, hinj⟩
  refine ⟨c ∘ e.symm, fun i => ?_, hinj.comp e.symm.injective⟩
  have h := hc (e.symm i)
  have hi : g (e.symm i).1 = i.1 := congrArg Subtype.val (e.apply_symm_apply i)
  rwa [hi] at h

private theorem isSNCFamily_iff_comp {k : Type u} [Field k] (sX : X ⟶ Spec (.of k))
    (hginj : Function.Injective g) (hg : ∀ i, E i ≠ ⊤ → ∃ j, g j = i) :
    IsSNCFamily sX E ↔ IsSNCFamily sX (E ∘ g) := by
  refine and_congr (forall_iff_forall_comp E g hg (fun D => IsReduced D.subscheme ∧
      MMP.Mori.IsPureCodimOne D.support ∧ MMP.Mori.IsSmoothScheme (D.subschemeι ≫ sX))
      ⟨?_, ?_, ?_⟩)
    (forall_congr' fun x => exists_congr fun n => exists_congr fun z => ?_)
  · exact isReduced_of_isAffine_isReduced _
  · intro W hW
    have h := hW.prop
    rw [Scheme.IdealSheafData.support_top] at h
    obtain ⟨w, hw⟩ := W.isIrreducible.nonempty
    exact (h hw).elim
  · unfold MMP.Mori.IsSmoothScheme
    ext x
    exact isEmptyElim x
  · have key := exists_coord_iff E g hginj hg x z
    constructor
    · rintro ⟨c, h1, h2, h3⟩
      obtain ⟨c', h2', h3'⟩ := key.1 ⟨c, h2, h3⟩
      exact ⟨c', h1, h2', h3'⟩
    · rintro ⟨c, h1, h2, h3⟩
      obtain ⟨c', h2', h3'⟩ := key.2 ⟨c, h2, h3⟩
      exact ⟨c', h1, h2', h3'⟩

end Reindex

section DeleteEmpty

variable {X : Scheme.{u}} (E : OrderedDivisor X)

private theorem isOrderedSNC_deleteEmpty_iff {k : Type u} [Field k] (sX : X ⟶ Spec (.of k)) :
    E.IsOrderedSNC sX ↔ E.deleteEmpty.IsOrderedSNC sX :=
  and_congr
    (forall_iff_forall_comp E.E _ (exists_flatIdx_get E)
      (fun D => IsReduced D.subscheme ∧ Stacks.Divisors.IsEffectiveCartierDivisor D)
      ⟨isReduced_of_isAffine_isReduced _, Stacks.Divisors.isEffectiveCartierDivisor_top⟩)
    (isSNCFamily_iff_comp E.E _ sX (injective_flatIdx_get E) (exists_flatIdx_get E))

end DeleteEmpty

end DeleteEmptyAux

/-- Inserting empty entries into an ordered snc divisor keeps it an ordered snc divisor. -/
private theorem isTriple_of_deleteEmpty {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {I : X.IdealSheafData} {E : OrderedDivisor X}
    (h : IsTriple s I E.deleteEmpty) : IsTriple s I E :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    (isOrderedSNC_deleteEmpty_iff E s).2 h.2.2.2.2.2.2⟩

/-! ### Closed embeddings -/

section ClosedEmbedding

/-- The unit ideal has order `0` along every irreducible subset. -/
private theorem orderAlong_top {X : Scheme.{u}} {Z : Set X} (hZ : IsIrreducible Z) :
    orderAlong (⊤ : X.IdealSheafData) hZ = 0 := by
  unfold orderAlong multAt
  rw [MMP.Resolution.Aux.stalk_top]
  refine le_antisymm (iSup₂_le fun j hj => ?_) bot_le
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp
  · exact absurd (top_le_iff.mp (hj.trans (Ideal.pow_le_self hj0.ne')))
      (IsLocalRing.maximalIdeal.isMaximal _).ne_top

/-- A sequence of order `≥ m ≥ 1` for the unit ideal, without empty blow-ups, is empty. -/
private theorem eq_nil_of_isOrderGe_of_top {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X) (E : OrderedDivisor X)
    (B : ClosedBlowupSequence X) (hI : a.I = ⊤) (hm : 1 ≤ a.m)
    (hB : B.IsOrderGeMarkedTripleSeq s a E) (hne : B.HasNoEmptyBlowups) : B = .nil X := by
  cases B with
  | nil => rfl
  | cons Z B =>
    exfalso
    obtain ⟨-, -, -, -, hord, -⟩ := hB
    have hZ : Z.support ≠ ⊥ := fun h => hne.1 ((Scheme.IdealSheafData.support_eq_bot_iff Z).mp h)
    obtain ⟨x, hx⟩ : (Z.support : Set X).Nonempty := by
      by_contra h
      exact hZ (by ext1; simpa [Set.not_nonempty_iff_eq_empty] using h)
    obtain ⟨W, hW, -⟩ := exists_mem_componentsOf hx
    have := hord W hW
    rw [hI, orderAlong_top] at this
    have : ((a.m : ℕ) : ℕ∞) = 0 := le_zero_iff.mp this
    norm_cast at this
    omega

open MMP.Mori

section SNC

variable {k : Type u} [Field k] {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}

/-- A subfamily of a simple normal crossing family is a simple normal crossing family. -/
private theorem isSNCFamily_comp {Λ Λ' : Type*} {E : Λ → Y.IdealSheafData}
    (hE : IsSNCFamily sY E) {e : Λ' → Λ} (he : Function.Injective e) :
    IsSNCFamily sY (E ∘ e) := by
  refine ⟨fun i => hE.1 (e i), fun x => ?_⟩
  obtain ⟨n, z, c, hz, hc, hinj⟩ := hE.2 x
  refine ⟨n, z, fun i => c ⟨e i.1, i.2⟩, hz, fun i => hc ⟨e i.1, i.2⟩, fun i i' h => ?_⟩
  exact Subtype.ext (he (congrArg Subtype.val (hinj h)))

/-- A member `E^j` of a simple normal crossing family has simple normal crossings with any
subfamily. -/
private theorem hasSNCWith_comp {Λ Λ' : Type*} {E : Λ → Y.IdealSheafData}
    (hE : IsSNCFamily sY E) {e : Λ' → Λ} (he : Function.Injective e) (j : Λ) :
    HasSNCWith (E ∘ e) (E j) := by
  intro x hx
  obtain ⟨n, z, c, hz, hc, hinj⟩ := hE.2 x
  refine ⟨n, z, fun i => c ⟨e i.1, i.2⟩, {c ⟨j, hx⟩}, hz, fun i => hc ⟨e i.1, i.2⟩, ?_, ?_⟩
  · exact fun i i' h => Subtype.ext (he (congrArg Subtype.val (hinj h)))
  · rw [hc ⟨j, hx⟩]; simp

/-- In a simple normal crossing family no member contains an irreducible component of
another. -/
private theorem not_subset_support_of_mem_componentsOf [IsLocallyNoetherian Y] {Λ : Type*}
    {E : Λ → Y.IdealSheafData} (hE : IsSNCFamily sY E) {i j : Λ} (hij : i ≠ j) {C : Set Y}
    (hC : C ∈ componentsOf ((E j).support : Set Y)) : ¬ C ⊆ (E i).support := by
  intro hsub
  obtain ⟨x, hxC⟩ := hC.1.1.nonempty
  have hxj : x ∈ (E j).support := hC.1.2 hxC
  obtain ⟨n, z, c, hz, hc, hinj⟩ := hE.2 x
  have hJ : IdealSheafData.stalk (E j) x = (coordPrime hz {c ⟨j, hxj⟩}).asIdeal := by
    rw [hc ⟨j, hxj⟩]; simp [coordPrime]
  have hCeq := eq_closure_coordPrime_of_mem_componentsOf hz hJ hC hxC
  have hmem : Y.fromSpecStalk x (coordPrime hz {c ⟨j, hxj⟩}) ∈ ((E i).support : Set Y) :=
    hsub (hCeq ▸ subset_closure rfl)
  rw [fromSpecStalk_mem_support_iff_stalk_le, hc ⟨i, hsub hxC⟩] at hmem
  have hne : c ⟨i, hsub hxC⟩ ≠ c ⟨j, hxj⟩ := fun h => hij (congrArg Subtype.val (hinj h))
  refine notMem_span_singleton_of_ne_of_isRegularSystemOfParameters hz hne.symm ?_
  have := hmem (Ideal.subset_span rfl)
  simpa [coordPrime] using this

end SNC

section Dimension

variable {Y : Scheme.{u}} [IsLocallyNoetherian Y]

/-- If the stalks of `D` are generated by members of regular systems of parameters, the local
ring of `D` at a point has dimension one less than that of `Y`. -/
private theorem exists_ringKrullDim_stalk_subscheme (D : Y.IdealSheafData)
    (hD : ∀ y ∈ D.support, ∃ (m : ℕ) (w : Fin m → Y.presheaf.stalk y) (j : Fin m),
      IsRegularSystemOfParameters w ∧ IdealSheafData.stalk D y = Ideal.span {w j})
    (s : D.subscheme) : ∃ m : ℕ, ringKrullDim (Y.presheaf.stalk (D.subschemeι s)) = m ∧
      ringKrullDim (D.subscheme.presheaf.stalk s) = (((m - 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  have hz : D.subschemeι s ∈ D.support := by
    rw [← SetLike.mem_coe, ← D.range_subschemeι]; exact ⟨s, rfl⟩
  obtain ⟨m, w, j, hw, hy⟩ := hD _ hz
  haveI := isRegularLocalRing_of_isRegularSystemOfParameters hw
  refine ⟨m, hw.2, ?_⟩
  rw [← ringKrullDim_eq_of_ringEquiv (IdealSheafData.subschemeStalkQuotEquiv D s), hy]
  exact ringKrullDim_quotient_span_singleton_of_isRegularSystemOfParameters hw j

/-- On an equidimensional scheme of dimension `d` locally of finite type over a field, a
nonempty quasi-compact closed subscheme whose stalk ideals are generated by members of regular
systems of parameters is equidimensional of dimension `d - 1`. -/
private theorem equidimensional_and_topologicalKrullDim_subscheme {k : Type u} [Field k]
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (he : Equidimensional Y) {d : ℕ}
    (hd : topologicalKrullDim Y = ((d : ℕ∞) : WithBot ℕ∞)) (D : Y.IdealSheafData)
    (hD : ∀ y ∈ D.support, ∃ (m : ℕ) (w : Fin m → Y.presheaf.stalk y) (j : Fin m),
      IsRegularSystemOfParameters w ∧ IdealSheafData.stalk D y = Ideal.span {w j})
    [CompactSpace D.subscheme] [Nonempty D.subscheme] :
    Equidimensional D.subscheme ∧
      topologicalKrullDim D.subscheme = (((d - 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  have hle : ∀ s, ringKrullDim (D.subscheme.presheaf.stalk s) ≤
      (((d - 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    intro s
    obtain ⟨m, hm, hs⟩ := exists_ringKrullDim_stalk_subscheme D hD s
    have h1 : ringKrullDim (Y.presheaf.stalk (D.subschemeι s)) ≤ topologicalKrullDim Y := by
      rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
      exact le_iSup (fun y => ringKrullDim (Y.presheaf.stalk y)) _
    rw [hm, hd] at h1
    have h2 : m ≤ d := by exact_mod_cast h1
    rw [hs]
    exact WithBot.coe_le_coe.2 (by exact_mod_cast Nat.sub_le_sub_right h2 1)
  have hcl : ∀ s : D.subscheme, IsClosed ({s} : Set D.subscheme) →
      ringKrullDim (D.subscheme.presheaf.stalk s) = (((d - 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    intro s hs
    obtain ⟨m, hm, hs'⟩ := exists_ringKrullDim_stalk_subscheme D hD s
    have hy : IsClosed ({D.subschemeι s} : Set Y) := by
      simpa using D.subschemeι.isClosedEmbedding.isClosedMap _ hs
    have h1 := topologicalKrullDimAt_eq_ringKrullDim_stalk_of_closed_point sY _ hy
    rw [topologicalKrullDimAt_eq_of_equidimensional k Y sY he
      (d := d) (by rw [hd]; rfl), hm] at h1
    have h2 : m = d := by exact_mod_cast h1.symm
    rw [hs', h2]
  have hat : ∀ s : D.subscheme,
      topologicalKrullDimAt D.subscheme s = ((d - 1 : ℕ) : WithBot ℕ∞) := by
    intro s
    rw [topologicalKrullDimAt_eq_iInf_closedSpecializations (D.subschemeι ≫ sY) s]
    obtain ⟨s', hs'mem, hs'cl⟩ :=
      (isClosed_closure (s := ({s} : Set D.subscheme))).exists_closed_singleton
        ⟨s, subset_closure rfl⟩
    refine le_antisymm (iInf_le_of_le ⟨s', specializes_iff_mem_closure.2 hs'mem, hs'cl⟩
      (hcl s' hs'cl).le) (le_iInf fun x => (hcl x.1 x.2.2).ge)
  refine ⟨equidimensional_of_topologicalKrullDimAt_eq k _ (D.subschemeι ≫ sY) hat, ?_⟩
  rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
  obtain ⟨s0, -, hs0⟩ :=
    isClosed_univ.exists_closed_singleton (Set.univ_nonempty (α := D.subscheme))
  exact le_antisymm (iSup_le hle) (le_iSup_of_le s0 (hcl s0 hs0).ge)

end Dimension

/-- `E^j` is smooth over `k` and
`(E^i ∩ E^j)_{i ≠ j}` is an ordered snc divisor on it (Kollár 3.25,
i.e. `isSmoothScheme_and_isSNCFamily_comap_subschemeι` with `Z = E^j`, plus the Cartier property
of each `E^i ∩ E^j` on `E^j`). -/
private theorem isSmoothScheme_and_isOrderedSNC_restrict {j : ℕ} (t : FieldBlowupTriple.{u})
    (ht : t ∈ triples) (hj : j < t.E.s) :
    MMP.Mori.IsSmoothScheme ((t.E.E ⟨j, hj⟩).subschemeι ≫ t.sX) ∧
      ((t.E.deleteIndex j).comap (t.E.E ⟨j, hj⟩).subschemeι).IsOrderedSNC
        ((t.E.E ⟨j, hj⟩).subschemeι ≫ t.sX) := by
  obtain ⟨hchar, hsm, hlft, hqc, hequi, hI, hEo, hEsnc⟩ := ht
  haveI := hchar
  haveI := hlft
  haveI : IsLocallyNoetherian t.X := LocallyOfFiniteType.isLocallyNoetherian t.sX
  have hE0 : IsSNCFamily t.sX t.E.E := hEsnc
  haveI : IsLocallyNoetherian (t.E.E ⟨j, hj⟩).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((t.E.E ⟨j, hj⟩).subschemeι ≫ t.sX)
  set L := (List.finRange t.E.s).filter fun i : Fin t.E.s => i.val ≠ j with hL
  have hLinj : Function.Injective L.get :=
    List.Nodup.injective_get ((List.nodup_finRange _).filter _)
  have hLne : ∀ i, L.get i ≠ ⟨j, hj⟩ := fun i h => by
    have := List.of_mem_filter (L.get_mem i)
    simp only [ne_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not] at this
    exact this (congrArg Fin.val h :)
  have hres := isSmoothScheme_and_isSNCFamily_comap_subschemeι t.sX hsm
    (isSNCFamily_comp hE0 hLinj) (hasSNCWith_comp hE0 hLinj ⟨j, hj⟩)
    (fun i C hC => not_subset_support_of_mem_componentsOf hE0 (hLne i) hC)
  refine ⟨hres.1, fun i => ?_, hres.2⟩
  exact ⟨isReduced_subscheme_of_stalk_eq_span_parameter _
      (hres.2.exists_stalk_eq_span_parameter i),
    isEffectiveCartierDivisor_of_stalk_eq_span_parameter _
      (hres.2.exists_stalk_eq_span_parameter i)⟩

/-- A non-empty entry `E^j` of the ordered snc
divisor on the smooth equidimensional `X` of dimension `n` is equidimensional of dimension
`n - 1`: its support is of pure codimension one (`IsSNCFamily`), and `X` is of finite type over
a field. -/
private theorem equidimensional_and_topologicalKrullDim_restrict {n j : ℕ}
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞))
    (hj : j < t.E.s) (hS : ((t.E.E ⟨j, hj⟩).support : Set t.X).Nonempty) :
    Equidimensional (t.E.E ⟨j, hj⟩).subscheme ∧
      topologicalKrullDim (t.E.E ⟨j, hj⟩).subscheme = (((n - 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  obtain ⟨hchar, hsm, hlft, hqc, hequi, hI, hEo, hEsnc⟩ := ht
  haveI := hchar
  haveI := hlft
  haveI := hqc
  haveI : IsLocallyNoetherian t.X := LocallyOfFiniteType.isLocallyNoetherian t.sX
  have hE0 : IsSNCFamily t.sX t.E.E := hEsnc
  haveI : IsLocallyNoetherian (t.E.E ⟨j, hj⟩).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((t.E.E ⟨j, hj⟩).subschemeι ≫ t.sX)
  haveI : CompactSpace (t.E.E ⟨j, hj⟩).subscheme :=
    QuasiCompact.compactSpace_of_compactSpace ((t.E.E ⟨j, hj⟩).subschemeι ≫ t.sX)
  haveI : Nonempty (t.E.E ⟨j, hj⟩).subscheme := by
    obtain ⟨x, hx⟩ := hS
    rw [← (t.E.E ⟨j, hj⟩).range_subschemeι] at hx
    obtain ⟨s, -⟩ := hx
    exact ⟨s⟩
  exact equidimensional_and_topologicalKrullDim_subscheme t.sX hequi hdim _
    (hE0.exists_stalk_eq_span_parameter ⟨j, hj⟩)

/-- `(E^j, J, (E^i ∩ E^j)_{i ≠ j})` is a triple of dimension `n - 1`. -/
private theorem mem_triples_restrict {n j : ℕ} (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞))
    (hj : j < t.E.s) (hS : ((t.E.E ⟨j, hj⟩).support : Set t.X).Nonempty)
    (J : (t.E.E ⟨j, hj⟩).subscheme.IdealSheafData) (hJ : IsNonzeroAtGenericPoints J) :
    IsTriple ((t.E.E ⟨j, hj⟩).subschemeι ≫ t.sX) J
        ((t.E.deleteIndex j).comap (t.E.E ⟨j, hj⟩).subschemeι) ∧
      topologicalKrullDim (t.E.E ⟨j, hj⟩).subscheme = (((n - 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  obtain ⟨hsm, hsnc⟩ := isSmoothScheme_and_isOrderedSNC_restrict t ht hj
  obtain ⟨heq, hd⟩ := equidimensional_and_topologicalKrullDim_restrict t ht hdim hj hS
  obtain ⟨hchar, -, hlft, hqc, -, -, -⟩ := ht
  haveI := hlft; haveI := hqc
  exact ⟨⟨hchar, hsm, inferInstance, inferInstance, heq, hJ, hsnc⟩, hd⟩

/-- A scheme smooth over a field has regular local rings. -/
private theorem isRegularLocalRing_stalk_of_isSmoothScheme {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} (h : MMP.Mori.IsSmoothScheme s) (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) :=
  ((isRegular_iff_regular_stalks X).1 (MMP.Threefold.Resolution.isRegular_of_isSmoothScheme h)).2 x

/-- No member of an snc family contains an irreducible component of the ambient scheme. -/
private theorem not_subset_support_of_mem_irreducibleComponents {k : Type u} [Field k]
    {X : Scheme.{u}} {s : X ⟶ Spec (.of k)} {Λ : Type*} {D : Λ → X.IdealSheafData}
    (hD : IsSNCFamily s D) (i : Λ) {Z : Set X} (hZ : Z ∈ irreducibleComponents X) :
    ¬ Z ⊆ ((D i).support : Set X) := by
  intro hsub
  have hirr : IsIrreducible Z := hZ.1
  have hcl : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
  have hgen := hirr.isGenericPoint_genericPoint_closure
  rw [hcl.closure_eq] at hgen
  refine hD.notMem_support_of_mem_irreducibleComponents (η := hirr.genericPoint) ?_ i
    (hsub (hgen.mem))
  rwa [hgen.def]

/-- Case `maxord I ≠ 1`: then `maxord I = 0` (Kollár 3.71), so `I = 𝒪_X` and `J = 𝒪_S`. -/
private theorem eq_top_of_maxOrder_ne_one {j : ℕ} (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hj : j < t.E.s)
    (J : (t.E.E ⟨j, hj⟩).subscheme.IdealSheafData)
    (hI : t.I = J.map (t.E.E ⟨j, hj⟩).subschemeι) (h1 : maxOrder t.I ≠ 1) : J = ⊤ := by
  obtain ⟨-, hsm, -, -, -, -, -, hsnc⟩ := ht
  haveI := isRegularLocalRing_stalk_of_isSmoothScheme hsm
  haveI := isRegularLocalRing_stalk_of_isSmoothScheme ((hsnc.1 ⟨j, hj⟩).2.2)
  have hle := MMP.Resolution.Kollar.maxOrder_le_one_of_eq_ker (t.E.E ⟨j, hj⟩) J t.I
    (fun _ => not_subset_support_of_mem_irreducibleComponents hsnc ⟨j, hj⟩) hI
  have hItop := eq_top_of_maxOrder_lt_one (lt_of_le_of_ne hle h1)
  have h := Scheme.IdealSheafData.comap_map_le J (t.E.E ⟨j, hj⟩).subschemeι
  rw [← hI, hItop, Scheme.IdealSheafData.comap_top] at h
  exact top_le_iff.mp h

/-- Case `maxord I ≠ 1`: the right-hand side is empty. -/
private theorem pushforward_eq_nil_of_maxOrder_ne_one {N n j : ℕ} (M : MarkedFamily.{u})
    (hM : IsMarkedOrderReductionFamily 0 (N - 1) M)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hnN : n ≤ N)
    (hj : j < t.E.s) (hS : ((t.E.E ⟨j, hj⟩).support : Set t.X).Nonempty)
    (J : (t.E.E ⟨j, hj⟩).subscheme.IdealSheafData) (hJ : IsNonzeroAtGenericPoints J)
    (hI : t.I = J.map (t.E.E ⟨j, hj⟩).subschemeι) (h1 : maxOrder t.I ≠ 1) :
    (M (n - 1) 1 ⟨⟨⟨(t.E.E ⟨j, hj⟩).subscheme, J,
        (t.E.deleteIndex j).comap (t.E.E ⟨j, hj⟩).subschemeι⟩, t.k,
        (t.E.E ⟨j, hj⟩).subschemeι ≫ t.sX⟩, 1⟩).pushforward (t.E.E ⟨j, hj⟩).subschemeι =
      .nil t.X := by
  obtain ⟨hT, hd⟩ := mem_triples_restrict t ht hdim hj hS J hJ
  have hJt := eq_top_of_maxOrder_ne_one t ht hj J hI h1
  obtain ⟨F, hF, -⟩ := hM 1 le_rfl
  set tS : MarkedTriple.{u} := ⟨⟨⟨(t.E.E ⟨j, hj⟩).subscheme, J,
        (t.E.deleteIndex j).comap (t.E.E ⟨j, hj⟩).subschemeι⟩, t.k,
        (t.E.E ⟨j, hj⟩).subschemeι ≫ t.sX⟩, 1⟩ with htS
  have hmem : tS ∈ markedTriplesOfDim (Set.Icc 0 (N - 1)) 1 :=
    ⟨hT, rfl, n - 1, ⟨Nat.zero_le _, by omega⟩, hd⟩
  have hdn : dimNat tS.X = n - 1 := by
    change ((topologicalKrullDim (t.E.E ⟨j, hj⟩).subscheme).unbotD 0).toNat = n - 1
    rw [hd]; rfl
  have hnil : M (n - 1) 1 tS = .nil _ := by
    rw [← hdn, ← hF tS hmem]
    exact eq_nil_of_isOrderGe_of_top _ tS.markedIdeal tS.E _ hJt le_rfl
      (F.isOrderGeMarkedTripleSeq tS hmem) (F.hasNoEmptyBlowups tS hmem)
  rw [hnil]
  exact pushforward_nil _

/-- For `maxord I = 1`, the maximal coefficient ideal `W_1(I)` is `I` itself: every weight
vector `c` of weight `≥ 1` has `c_0 ≥ 1`, and `c = (1, 0)` contributes `D^0(I) = I`. -/
private theorem maximalCoefficientIdeal_one_of_maxOrder_eq_one {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (I : X.IdealSheafData) (h1 : maxOrder I = 1) :
    maximalCoefficientIdeal sX I 1 = I := by
  unfold maximalCoefficientIdeal
  have hm : (maxOrder I).toNat = 1 := by rw [h1]; rfl
  generalize (maxOrder I).toNat = m at hm ⊢
  subst hm
  refine le_antisymm (iSup₂_le fun c hc => ?_) ?_
  · have hc0 : 1 ≤ c 0 := by
      simp [coefficientWeight, Fin.sum_univ_two] at hc; exact_mod_cast hc
    rw [Fin.prod_univ_two]
    refine (mul_le_of_le_one_right' le_top).trans ?_
    simp only [Fin.val_zero, higherDerivativeIdeal_zero]
    obtain ⟨c', hc'⟩ := Nat.exists_eq_add_of_le hc0
    rw [hc', pow_add, pow_one]
    exact mul_le_of_le_one_right' le_top
  · refine le_trans ?_ (le_iSup₂ (f := fun (c : Fin 2 → ℕ)
      (_ : (1 : ℤ) ≤ (coefficientWeight 1 c : ℤ)) =>
        ∏ j : Fin 2, higherDerivativeIdeal sX I (j : ℕ) ^ c j) ![1, 0]
      (by simp [coefficientWeight]))
    simp [Fin.prod_univ_two, higherDerivativeIdeal_zero]

/-- The image of an irreducible component of the source of a closed embedding is an irreducible
component of the range. -/
private theorem closure_singleton_mem_irreducibleComponents_of_range {A B : Type*}
    [TopologicalSpace A] [TopologicalSpace B] {g : A → B} (hg : Topology.IsClosedEmbedding g)
    {η : A} (hη : closure {g η} ∈ componentsOf (Set.range g)) :
    closure {η} ∈ irreducibleComponents A := by
  refine ⟨isIrreducible_singleton.closure, fun T hT hle => ?_⟩
  have hT' : IsIrreducible (closure (g '' T)) := (hT.image g hg.continuous.continuousOn).closure
  have hsub : closure (g '' T) ⊆ closure {g η} :=
    hη.2 ⟨hT', closure_minimal (Set.image_subset_range _ _) hg.isClosed_range⟩
      (closure_mono (Set.singleton_subset_iff.2 ⟨η, hle (subset_closure rfl), rfl⟩))
  intro x hx
  have h1 : g x ∈ closure {g η} := hsub (subset_closure ⟨x, hx, rfl⟩)
  rw [← Set.image_singleton, hg.isClosedMap.closure_image_eq_of_continuous hg.continuous] at h1
  obtain ⟨y, hy, hyx⟩ := h1
  exact hg.injective hyx ▸ hy

/-- A point of the cosupport of `(I, 1)` lies in the support of `I`. -/
private theorem mem_support_of_mem_cosupport_one {X : Scheme.{u}} {I : X.IdealSheafData} {x : X}
    (hx : x ∈ (⟨I, 1⟩ : MarkedIdeal X).cosupport) : x ∈ (I.support : Set X) := by
  have h : ((1 : ℕ) : ℕ∞) ≤ multAt I x := hx
  rw [multAt, natCast_le_idealOrder_iff', pow_one] at h
  by_contra hxs
  have := (IdealSheafData.stalk_eq_top_iff_notMem_support I x).2 hxs
  rw [this] at h
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp h)

/-- `Z_{-1}(I, 1, E^j)` is empty: a component
`C` of `E^j` inside `cosupp(I, 1) = Supp(𝒪_X/I) = τ(Supp(𝒪_S/J))` would have `J_η` proper at its
generic point `η`, where `𝒪_{S,η}` is a field (`E^j` reduced), so `J_η = 0`, contradicting `hJ`. -/
private theorem divisorComponentCentre_eq_top {j : ℕ} (t : FieldBlowupTriple.{u})
    (ht : t ∈ triples) (hj : j < t.E.s)
    (J : (t.E.E ⟨j, hj⟩).subscheme.IdealSheafData) (hJ : IsNonzeroAtGenericPoints J)
    (hI : t.I = J.map (t.E.E ⟨j, hj⟩).subschemeι) :
    divisorComponentCentre (⟨t.I, 1⟩ : MarkedIdeal t.X) (t.E.E ⟨j, hj⟩) = ⊤ := by
  have hred : IsReduced (t.E.E ⟨j, hj⟩).subscheme := (ht.2.2.2.2.2.2.2.1 ⟨j, hj⟩).1
  have hempty : {W | W ∈ componentsOf ((t.E.E ⟨j, hj⟩).support : Set t.X) ∧
      W ⊆ (⟨t.I, 1⟩ : MarkedIdeal t.X).cosupport} = ∅ := by
    ext W
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hWc hWsub
    obtain ⟨hirr, hsubD⟩ := hWc.1
    have hcl : IsClosed W := isClosed_of_mem_componentsOf (t.E.E ⟨j, hj⟩).support.isClosed hWc
    have hgen := hirr.isGenericPoint_genericPoint_closure
    rw [hcl.closure_eq] at hgen
    have hη : hirr.genericPoint ∈ W := hgen.mem
    obtain ⟨η', hη'⟩ : hirr.genericPoint ∈ Set.range (t.E.E ⟨j, hj⟩).subschemeι := by
      rw [(t.E.E ⟨j, hj⟩).range_subschemeι]; exact hsubD hη
    have hW : closure {(t.E.E ⟨j, hj⟩).subschemeι η'} ∈
        componentsOf (Set.range (t.E.E ⟨j, hj⟩).subschemeι) := by
      rw [hη', ← (t.E.E ⟨j, hj⟩).range_subschemeι] at *
      rwa [hgen.def]
    have hc' := closure_singleton_mem_irreducibleComponents_of_range
      (t.E.E ⟨j, hj⟩).subschemeι.isClosedEmbedding hW
    have hfield := isField_stalk_of_closure_mem_irreducibleComponents _ η' hc'
    have hbot := hJ η' hc'
    have hnt : IdealSheafData.stalk J η' ≠ ⊤ := by
      intro htop
      have hnot := (IdealSheafData.stalk_eq_top_iff_notMem_support J η').1 htop
      apply hnot
      have hJc : J = t.I.comap (t.E.E ⟨j, hj⟩).subschemeι := by
        rw [hI]; exact (J.comap_map_of_isClosedImmersion _).symm
      rw [hJc, Scheme.IdealSheafData.support_comap]
      exact mem_support_of_mem_cosupport_one (hWsub (hη' ▸ hη))
    letI := hfield.toField
    rcases Ideal.eq_bot_or_top (IdealSheafData.stalk J η') with h | h
    · exact hbot h
    · exact hnt h
  unfold divisorComponentCentre
  rw [hempty]
  have : Closeds.closure (⋃₀ (∅ : Set (Set t.X))) = ⊥ := by ext; simp
  rw [this]
  simp

open CategoryTheory.Limits in
/-- Push-forward along `τ` of the pull-back along `q⁻¹` is the pull-back along `lam` of the
push-forward along `τ'`, for a commuting square of isomorphisms `q`, `lam`. -/
private theorem pushforward_pullbackReduced_inv {S S' X B : Scheme.{u}} (τ : S ⟶ X)
    (τ' : S' ⟶ B) [IsClosedImmersion τ'] (π : B ⟶ X) [IsIso π] (lam : X ⟶ B)
    (hlam : lam ≫ π = 𝟙 X) (q : S' ⟶ S) [IsIso q] (hq : τ' ≫ π = q ≫ τ)
    (BS' : ClosedBlowupSequence S') :
    (BS'.pullbackReduced (inv q)).pushforward τ = (BS'.pushforward τ').pullbackReduced lam := by
  have hl : lam = inv π := IsIso.eq_inv_of_inv_hom_id hlam
  haveI : IsIso lam := by rw [hl]; infer_instance
  have hcomm : inv q ≫ τ' = τ ≫ lam := by
    have : τ' = τ' ≫ π ≫ lam := by rw [hl]; simp
    calc inv q ≫ τ' = inv q ≫ τ' ≫ π ≫ lam := by rw [← this]
      _ = τ ≫ lam := by rw [← Category.assoc τ' π lam, hq]; simp
  have sq : IsPullback (inv q) τ τ' lam := IsPullback.of_horiz_isIso ⟨hcomm⟩
  exact pushforward_pullbackReduced τ' lam (inv q) τ sq BS'

open CategoryTheory.Limits in
/-- Along an isomorphism `π`, the pull-back `π⁻¹D` of a closed subscheme `D` is isomorphic to
`D`, compatibly with the inclusions. -/
private theorem exists_isIso_comap_square {X B : Scheme.{u}} (π : B ⟶ X) [IsIso π]
    (D : X.IdealSheafData) :
    ∃ q : (D.comap π).subscheme ⟶ D.subscheme, IsIso q ∧
      (D.comap π).subschemeι ≫ π = q ≫ D.subschemeι := by
  have sq1 : IsPullback (D.comap π).subschemeι
      ((D.comapIso π).hom ≫ pullback.snd π D.subschemeι) π D.subschemeι := by
    refine IsPullback.of_iso_pullback ⟨?_⟩ (D.comapIso π) ?_ ?_
    · simp [pullback.condition]
    · simp
    · simp
  exact ⟨_, sq1.isIso_snd_of_isIso, sq1.w⟩

/-- The quotient of an ideal sheaf by the unit ideal is the ideal itself. -/
private theorem idealColon_top {X : Scheme.{u}} (A : X.IdealSheafData) : idealColon A ⊤ = A := by
  unfold idealColon
  conv_rhs => rw [← Scheme.IdealSheafData.ofIdeals_ideal A]
  congr 1
  funext V
  rw [Scheme.IdealSheafData.ideal_top]
  simpa using Ideal.colon_univ (I := A.ideal V)

/-- The birational transform of `(I, m)` along the blow-up of the unit ideal is the pull-back of
`I`. -/
private theorem I_birationalTransform_top {X : Scheme.{u}} (a : MarkedIdeal X) :
    (a.birationalTransform ⊤).I = a.I.comap (blowUpToBase (⊤ : X.IdealSheafData)) := by
  unfold MarkedIdeal.birationalTransform
  simp only [Scheme.IdealSheafData.comap_top]
  rw [show (⊤ : (blowUp (⊤ : X.IdealSheafData)).IdealSheafData) ^ a.m = ⊤ from one_pow a.m,
    idealColon_top]

private theorem bd_core {N n j : ℕ} (M : MarkedFamily.{u})
    (hM : IsMarkedOrderReductionFamily 0 (N - 1) M)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hnN : n ≤ N)
    (hj : j < t.E.s) (hS : ((t.E.E ⟨j, hj⟩).support : Set t.X).Nonempty)
    (J : (t.E.E ⟨j, hj⟩).subscheme.IdealSheafData) (hJ : IsNonzeroAtGenericPoints J)
    {Y : Scheme.{u}} (q : Y ⟶ (t.E.E ⟨j, hj⟩).subscheme) [IsIso q]
    (sY : Y ⟶ Spec (.of t.k)) (hsY : sY = q ≫ (t.E.E ⟨j, hj⟩).subschemeι ≫ t.sX)
    (I' : Y.IdealSheafData) (hI' : I' = J.comap q) (E' : OrderedDivisor Y)
    (hE' : E' = ((t.E.deleteIndex j).comap (t.E.E ⟨j, hj⟩).subschemeι).comap q)
    (m' : ℕ) (hm' : m' = 1) :
    (⟨⟨⟨Y, I', E'⟩, t.k, sY⟩, m'⟩ : MarkedTriple.{u}) ∈ markedTriples ∧
    (M (n - 1) m' ⟨⟨⟨Y, I', E'⟩, t.k, sY⟩, m'⟩).pullbackReduced (inv q) =
      M (n - 1) 1 ⟨⟨⟨(t.E.E ⟨j, hj⟩).subscheme, J,
        (t.E.deleteIndex j).comap (t.E.E ⟨j, hj⟩).subschemeι⟩, t.k,
        (t.E.E ⟨j, hj⟩).subschemeι ≫ t.sX⟩, 1⟩ := by
  subst hsY hI' hE' hm'
  rename_i hqiso
  haveI := hqiso
  obtain ⟨hT, hd⟩ := mem_triples_restrict t ht hdim hj hS J hJ
  obtain ⟨F, hF, -, hcomm, -⟩ := hM 1 le_rfl
  set tS : MarkedTriple.{u} := ⟨⟨⟨(t.E.E ⟨j, hj⟩).subscheme, J,
        (t.E.deleteIndex j).comap (t.E.E ⟨j, hj⟩).subschemeι⟩, t.k,
        (t.E.E ⟨j, hj⟩).subschemeι ≫ t.sX⟩, 1⟩ with htS
  have hmem : tS ∈ markedTriplesOfDim (Set.Icc 0 (N - 1)) 1 :=
    ⟨hT, rfl, n - 1, ⟨Nat.zero_le _, by omega⟩, hd⟩
  have hdn : dimNat tS.X = n - 1 := by
    change ((topologicalKrullDim (t.E.E ⟨j, hj⟩).subscheme).unbotD 0).toNat = n - 1
    rw [hd]; rfl
  have hsnc : tS.toFieldBlowupTriple ∈ sncTriples := mem_sncTriples_of_mem_triples hT
  haveI : QuasiCompact (q ≫ tS.sX) := by
    obtain ⟨-, -, -, hqc, -⟩ := hT
    haveI := hqc
    change QuasiCompact (q ≫ _)
    infer_instance
  haveI : LocallyOfFiniteType (q ≫ tS.sX) := by
    obtain ⟨-, -, hlft, -⟩ := hT
    haveI := hlft
    change LocallyOfFiniteType (q ≫ _)
    infer_instance
  have hsnc' := pullback_mem_sncTriples hsnc (h := q)
  have hequi : Equidimensional Y :=
    TopologicalSpace.Equidimensional.of_homeomorph q.homeomorph hT.2.2.2.2.1
  have hmk : (tS.pullback q) ∈ markedTriples := mem_triples_iff.2 ⟨hsnc', hequi⟩
  have hdY : topologicalKrullDim Y = (((n - 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    rw [← hd]; exact IsHomeomorph.topologicalKrullDim_eq _ q.homeomorph.isHomeomorph
  have hmem' : tS.pullback q ∈ markedTriplesOfDim (Set.Icc 0 (N - 1)) 1 :=
    ⟨hmk, rfl, n - 1, ⟨Nat.zero_le _, by omega⟩, hdY⟩
  have hdn' : dimNat (tS.pullback q).X = n - 1 := by
    change ((topologicalKrullDim Y).unbotD 0).toNat = n - 1
    rw [hdY]; rfl
  refine ⟨hmk, ?_⟩
  have e1 : M (n - 1) 1 (tS.pullback q) = F.toFun (tS.pullback q) hmem' := by
    rw [hF _ hmem', hdn']
  have e2 : M (n - 1) 1 tS = F.toFun tS hmem := by rw [hF _ hmem, hdn]
  change (M (n - 1) 1 (tS.pullback q)).pullbackReduced
    (inv q : (t.E.E ⟨j, hj⟩).subscheme ⟶ Y) = M (n - 1) 1 tS
  rw [e1, e2, hcomm.2 tS hmem Y q inferInstance inferInstance inferInstance hmem',
    ClosedBlowupSequence.reduction_pullback]
  refine (eq_of_heq (ClosedBlowupSequence.pullbackReduced_pullbackReduced_heq _ q (inv q)
    (𝟙 _) rfl (by simp))).trans ?_
  exact ClosedBlowupSequence.reduction_eq_self (F.hasNoEmptyBlowups tS hmem)

private theorem bd_step_top {N n j : ℕ} (M : MarkedFamily.{u})
    (hM : IsMarkedOrderReductionFamily 0 (N - 1) M)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hnN : n ≤ N)
    (hj : j < t.E.s) (hS : ((t.E.E ⟨j, hj⟩).support : Set t.X).Nonempty)
    (J : (t.E.E ⟨j, hj⟩).subscheme.IdealSheafData) (hJ : IsNonzeroAtGenericPoints J)
    (hI : t.I = J.map (t.E.E ⟨j, hj⟩).subschemeι) :
    ∃ (q : ((t.E.E ⟨j, hj⟩).comap (blowUpToBase (⊤ : t.X.IdealSheafData))).subscheme ⟶
        (t.E.E ⟨j, hj⟩).subscheme) (hq : IsIso q),
      ((t.E.E ⟨j, hj⟩).comap (blowUpToBase (⊤ : t.X.IdealSheafData))).subschemeι ≫
          blowUpToBase (⊤ : t.X.IdealSheafData) = q ≫ (t.E.E ⟨j, hj⟩).subschemeι ∧
      ((((t.E.E ⟨j, hj⟩).comap (blowUpToBase (⊤ : t.X.IdealSheafData))).support :
          Set (blowUp (⊤ : t.X.IdealSheafData))).Nonempty ∧
        (⟨⟨⟨((t.E.E ⟨j, hj⟩).comap (blowUpToBase (⊤ : t.X.IdealSheafData))).subscheme,
          (MarkedIdeal.birationalTransform ⊤
            (⟨t.I, Nat.factorial 1⟩ : MarkedIdeal t.X)).I.comap
            ((t.E.E ⟨j, hj⟩).comap (blowUpToBase (⊤ : t.X.IdealSheafData))).subschemeι,
          ((t.E.comap (blowUpToBase (⊤ : t.X.IdealSheafData))).deleteIndex j).comap
            ((t.E.E ⟨j, hj⟩).comap (blowUpToBase (⊤ : t.X.IdealSheafData))).subschemeι⟩, t.k,
          ((t.E.E ⟨j, hj⟩).comap (blowUpToBase (⊤ : t.X.IdealSheafData))).subschemeι ≫
            blowUpToBase (⊤ : t.X.IdealSheafData) ≫ t.sX⟩, Nat.factorial 1⟩ : MarkedTriple.{u}) ∈
          markedTriples) ∧
      (M (n - 1) (Nat.factorial 1)
        ⟨⟨⟨((t.E.E ⟨j, hj⟩).comap (blowUpToBase (⊤ : t.X.IdealSheafData))).subscheme,
          (MarkedIdeal.birationalTransform ⊤
            (⟨t.I, Nat.factorial 1⟩ : MarkedIdeal t.X)).I.comap
            ((t.E.E ⟨j, hj⟩).comap (blowUpToBase (⊤ : t.X.IdealSheafData))).subschemeι,
          ((t.E.comap (blowUpToBase (⊤ : t.X.IdealSheafData))).deleteIndex j).comap
            ((t.E.E ⟨j, hj⟩).comap (blowUpToBase (⊤ : t.X.IdealSheafData))).subschemeι⟩, t.k,
          ((t.E.E ⟨j, hj⟩).comap (blowUpToBase (⊤ : t.X.IdealSheafData))).subschemeι ≫
            blowUpToBase (⊤ : t.X.IdealSheafData) ≫ t.sX⟩, Nat.factorial 1⟩).pullbackReduced
        (@inv _ _ _ _ q hq) =
      M (n - 1) 1 ⟨⟨⟨(t.E.E ⟨j, hj⟩).subscheme, J,
        (t.E.deleteIndex j).comap (t.E.E ⟨j, hj⟩).subschemeι⟩, t.k,
        (t.E.E ⟨j, hj⟩).subschemeι ≫ t.sX⟩, 1⟩ := by
  haveI hπ := ClosedBlowupSequence.isIso_blowUpToBase_top t.X
  obtain ⟨q, hq, hcomm⟩ := exists_isIso_comap_square (blowUpToBase (⊤ : t.X.IdealSheafData))
    (t.E.E ⟨j, hj⟩)
  have hJc : t.I.comap (t.E.E ⟨j, hj⟩).subschemeι = J := by
    rw [hI]; exact J.comap_map_of_isClosedImmersion _
  have hne : (((t.E.E ⟨j, hj⟩).comap (blowUpToBase (⊤ : t.X.IdealSheafData))).support :
      Set (blowUp (⊤ : t.X.IdealSheafData))).Nonempty := by
    obtain ⟨x, hx⟩ := hS
    obtain ⟨y, rfl⟩ := (blowUpToBase (⊤ : t.X.IdealSheafData)).surjective x
    refine ⟨y, ?_⟩
    rw [SetLike.mem_coe, Scheme.IdealSheafData.support_comap]
    exact hx
  have hsY : ((t.E.E ⟨j, hj⟩).comap (blowUpToBase (⊤ : t.X.IdealSheafData))).subschemeι ≫
      blowUpToBase (⊤ : t.X.IdealSheafData) ≫ t.sX =
      q ≫ (t.E.E ⟨j, hj⟩).subschemeι ≫ t.sX := by
    rw [← Category.assoc, hcomm, Category.assoc]
  have hI' : (MarkedIdeal.birationalTransform ⊤ (⟨t.I, Nat.factorial 1⟩ : MarkedIdeal t.X)).I.comap
      ((t.E.E ⟨j, hj⟩).comap (blowUpToBase (⊤ : t.X.IdealSheafData))).subschemeι =
      J.comap q := by
    rw [I_birationalTransform_top]
    show (t.I.comap _).comap _ = _
    rw [← Scheme.IdealSheafData.comap_comp, hcomm, Scheme.IdealSheafData.comap_comp, hJc]
  have hE' : ((t.E.comap (blowUpToBase (⊤ : t.X.IdealSheafData))).deleteIndex j).comap
      ((t.E.E ⟨j, hj⟩).comap (blowUpToBase (⊤ : t.X.IdealSheafData))).subschemeι =
      ((t.E.deleteIndex j).comap (t.E.E ⟨j, hj⟩).subschemeι).comap q := by
    unfold OrderedDivisor.comap OrderedDivisor.deleteIndex
    congr 1
    funext i
    rw [← Scheme.IdealSheafData.comap_comp, hcomm, Scheme.IdealSheafData.comap_comp]
  have core := bd_core M hM t ht hdim hnN hj hS J hJ q _ hsY _ hI' _ hE'
    (Nat.factorial 1) rfl
  exact ⟨q, hq, hcomm, ⟨hne, core.1⟩, core.2⟩

/-- Case `maxord I = 1`: `W_1(I) = I`, `Z_{-1}` is empty, `W_0𝒪_S = J`, and the reduction
deletes the trivial blow-up, so `𝓑𝓓_{n,1,j}(X, I, E) = τ_*𝓜_{n-1,1}(E^j, J, 1, E_S)`. -/
private theorem bdFunctor_eq_of_maxOrder_eq_one {N n j : ℕ} (M : MarkedFamily.{u})
    (hM : IsMarkedOrderReductionFamily 0 (N - 1) M)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hnN : n ≤ N)
    (hj : j < t.E.s) (hS : ((t.E.E ⟨j, hj⟩).support : Set t.X).Nonempty)
    (J : (t.E.E ⟨j, hj⟩).subscheme.IdealSheafData) (hJ : IsNonzeroAtGenericPoints J)
    (hI : t.I = J.map (t.E.E ⟨j, hj⟩).subschemeι) (h1 : maxOrder t.I = 1) :
    bdFunctor M n 1 j t =
      (M (n - 1) 1 ⟨⟨⟨(t.E.E ⟨j, hj⟩).subscheme, J,
        (t.E.deleteIndex j).comap (t.E.E ⟨j, hj⟩).subschemeι⟩, t.k,
        (t.E.E ⟨j, hj⟩).subschemeι ≫ t.sX⟩, 1⟩).pushforward (t.E.E ⟨j, hj⟩).subschemeι := by
  have hZ := divisorComponentCentre_eq_top t ht hj J hJ hI
  unfold bdFunctor
  rw [dif_pos ⟨h1, hj⟩]
  dsimp only
  generalize hW : maximalCoefficientIdeal t.sX t.I ((Nat.factorial 1 : ℕ) : ℤ) = W
  obtain rfl : W = t.I := hW.symm.trans (maximalCoefficientIdeal_one_of_maxOrder_eq_one t.sX t.I h1)
  generalize hZ' : divisorComponentCentre (⟨t.I, Nat.factorial 1⟩ : MarkedIdeal t.X)
    (t.E.E ⟨j, hj⟩) = Z
  obtain rfl : Z = ⊤ := hZ'.symm.trans hZ
  rw [ClosedBlowupSequence.reduction, ClosedBlowupSequence.pullbackReduced,
    dif_pos (Scheme.IdealSheafData.comap_top _)]
  obtain ⟨q, hq, hcomm, hcond, hMeq⟩ := bd_step_top M hM t ht hdim hnN hj hS J hJ hI
  rw [if_pos hcond, ← hMeq]
  haveI := ClosedBlowupSequence.isIso_blowUpToBase_top t.X
  exact (pushforward_pullbackReduced_inv (t.E.E ⟨j, hj⟩).subschemeι _ _ _
    (blowUpLift_comp _ _ _) q hcomm _).symm

end ClosedEmbedding

/-- **Kollár, Lemma 3.102 (3), closed embeddings.** Let `M` be a marked order-reduction family on
dimensions `0, …, N - 1` (`IsMarkedOrderReductionFamily`) and `(X, I, E)` a triple of dimension
`n` with `1 ≤ n ≤ N`. Let `S = E^j` (`0`-based `j < s`) be non-empty with inclusion `τ : S ↪ X`,
and let `J` be an ideal sheaf on `S`, nonzero at the generic point of every irreducible component
of `S` (`IsNonzeroAtGenericPoints`), with `I = J.map τ`, i.e. `𝒪_X/I = τ_*(𝒪_S/J)`. Then
`bdFunctor M n 1 j (X, I, E)` is the push-forward along `τ` of
`M (n - 1) 1 (S, J, 1, (E^i ∩ S)_{i ≠ j})`. -/
@[mmp "lem_kr3e_bd_closed_embedding"]
public theorem bdFunctor_eq_pushforward_of_eq_map {N n j : ℕ} (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hj : j < t.E.s) (hS : ((t.E.E ⟨j, hj⟩).support : Set t.X).Nonempty)
    (J : (t.E.E ⟨j, hj⟩).subscheme.IdealSheafData) (hJ : IsNonzeroAtGenericPoints J)
    (hI : t.I = J.map (t.E.E ⟨j, hj⟩).subschemeι) :
    let τ := (t.E.E ⟨j, hj⟩).subschemeι
    let tS : MarkedTriple.{u} :=
      ⟨⟨⟨(t.E.E ⟨j, hj⟩).subscheme, J, (t.E.deleteIndex j).comap τ⟩, t.k, τ ≫ t.sX⟩, 1⟩
    bdFunctor M n 1 j t = (M (n - 1) 1 tS).pushforward τ := by
  intro τ tS
  by_cases h1 : maxOrder t.I = 1
  · exact bdFunctor_eq_of_maxOrder_eq_one M hM t ht hdim hnN hj hS J hJ hI h1
  · have hl : bdFunctor M n 1 j t = .nil t.X := by
      unfold bdFunctor
      rw [dif_neg (fun h => h1 h.1)]
    rw [hl]
    exact (pushforward_eq_nil_of_maxOrder_ne_one M hM t ht hdim hnN hj hS J hJ hI h1).symm

/-! ### Smooth morphisms -/

section Smooth

/-- `𝓑𝓓` is a reduction (or empty), so it has no empty blow-ups. -/
private theorem hasNoEmptyBlowups_bdFunctor (M : MarkedFamily.{u}) (n m j : ℕ)
    (t : FieldBlowupTriple.{u}) : (bdFunctor M n m j t).HasNoEmptyBlowups := by
  unfold bdFunctor
  split
  · exact ClosedBlowupSequence.hasNoEmptyBlowups_reduction _
  · trivial

/-- On an equidimensional space of dimension `≥ 1` every irreducible component has positive
dimension. -/
private theorem pos_topologicalKrullDim_of_mem_irreducibleComponents {T : Type*}
    [TopologicalSpace T] (he : TopologicalSpace.Equidimensional T)
    (hd : 1 ≤ topologicalKrullDim T) :
    ∀ Z ∈ irreducibleComponents T, 0 < topologicalKrullDim Z := by
  intro Z hZ
  by_contra hle
  rw [not_lt] at hle
  have : topologicalKrullDim T ≤ 0 := by
    rw [topologicalKrullDim_eq_iSup_irreducibleComponents T]
    exact iSup₂_le fun W hW => (he W hW Z hZ) ▸ hle
  exact absurd (hd.trans this) (by decide)

/-- A scheme smooth over a field is locally noetherian with regular local rings. -/
private theorem regular_stalks_of_smooth {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [Smooth s] :
    IsLocallyNoetherian X ∧ ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) :=
  ((isRegular_tfae X).out 1 2).mp (isRegular_of_smooth_over_field s)

/-- `ord_y h^*I = ord_{h(y)} I` for smooth `h` (on a scheme smooth over a field). -/
private theorem multAt_comap_of_smooth {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [Smooth sX] (h : Y ⟶ X) [Smooth h] (I : X.IdealSheafData) (y : Y) :
    multAt (I.comap h) y = multAt I (h y) := by
  obtain ⟨hXn, hX⟩ := regular_stalks_of_smooth sX
  obtain ⟨hYn, hY⟩ := regular_stalks_of_smooth (h ≫ sX)
  exact MMP.Flips.ResolutionInputs.multAt_comap_eq h hX hY
    (fun y => AlgebraicGeometry.isRegularLocalRing_closedFibre_of_smooth h y) I y

private theorem multAt_comap_of_smooth_of_mem_triples (t : FieldBlowupTriple.{u})
    (ht : t ∈ triples) {Y : Scheme.{u}} (h : Y ⟶ t.X) [Smooth h] (y : Y) :
    multAt (t.I.comap h) y = multAt t.I (h y) := by
  haveI : LocallyOfFinitePresentation t.sX :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := t.sX)).mpr ht.2.2.1
  haveI : Smooth t.sX := (MMP.Mori.isSmoothScheme_iff _).1 ht.2.1
  exact multAt_comap_of_smooth t.sX h t.I y

/-- The pulled-back ideal has no larger maximal order. -/
private theorem maxOrder_comap_le_of_smooth (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    {Y : Scheme.{u}} (h : Y ⟶ t.X) [Smooth h] : maxOrder (t.I.comap h) ≤ maxOrder t.I := by
  simp only [maxOrder, maxOrderAlong, Set.mem_univ, iSup_pos]
  exact iSup_le fun y =>
    (multAt_comap_of_smooth_of_mem_triples t ht h y).symm ▸ le_iSup (multAt t.I) (h y)

/-- A member of the class has dimension `≥ 1`. -/
private theorem one_le_topologicalKrullDim {N m j : ℕ} {t : FieldBlowupTriple.{u}}
    (ht : t ∈ idealTriplesOfDim (Set.Icc 1 N) m ∧ j < t.E.s) : 1 ≤ topologicalKrullDim t.X := by
  obtain ⟨n, hn, hX⟩ := ht.1.2.1
  rw [hX]
  exact_mod_cast hn.1

/-- The marked transform of a one-step sequence is the birational transform. -/
private theorem cosupport_birationalTransform_subset_of_isOrderGe {k : Type u} [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X) (E : OrderedDivisor X)
    (Z : X.IdealSheafData) (B : ClosedBlowupSequence (blowUp Z))
    (hB : (ClosedBlowupSequence.cons Z B).IsOrderGeMarkedTripleSeq s a E) :
    (a.birationalTransform Z).cosupport ⊆ blowUpToBase Z ⁻¹' a.cosupport := by
  have e : B.truncate 0 = .nil _ := by cases B <;> rfl
  have := ClosedBlowupSequence.cosupport_markedTransform_truncate_subset s a E _ hB 1
  change ((ClosedBlowupSequence.cons Z (B.truncate 0)).markedTransform a).cosupport ⊆
    (ClosedBlowupSequence.cons Z (B.truncate 0)).toBase ⁻¹' a.cosupport at this
  rw [e] at this
  intro y hy
  have hy' : y ∈ (𝟙 (blowUp Z) ≫ blowUpToBase Z) ⁻¹' a.cosupport := this hy
  rwa [Category.id_comp] at hy'

/-- A smooth blow-up sequence of order `≥ m` for `(X, I, m, E)` has all its centres over
`cosupp(I, m)`, so its pull-back along a morphism missing `cosupp(I, m)` is empty after
deleting empty blow-ups. -/
private theorem pullbackReduced_eq_nil_of_isOrderGe {k : Type u} [Field k] :
    ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X)
      (E : OrderedDivisor X), B.IsOrderGeMarkedTripleSeq s a E →
      ∀ {Y : Scheme.{u}} (h : Y ⟶ X), (∀ y, h y ∉ a.cosupport) → B.pullbackReduced h = .nil Y
  | _, .nil _, _, _, _, _, _, _, _ => rfl
  | X, .cons Z B, s, a, E, hB, Y, h, hh => by
    have hsupp : (Z.support : Set X) ⊆ a.cosupport := by
      obtain ⟨hT, hZ, -, -, ha, -⟩ := hB
      intro x hx
      change (a.m : ℕ∞) ≤ multAt a.I x
      rw [multAt, natCast_le_idealOrder_iff']
      refine (stalk_le_pow_of_orderAlongGE s hT.2.1 Z hZ a.I a.m ha x).trans ?_
      refine Ideal.pow_right_mono (IsLocalRing.le_maximalIdeal fun h => ?_) a.m
      exact ((IdealSheafData.stalk_eq_top_iff_notMem_support Z x).1 h) hx
    have hZc : Z.comap h = ⊤ := by
      rw [← Scheme.IdealSheafData.support_eq_bot_iff]
      refine eq_bot_iff.2 fun y hy => ?_
      exact hh y (hsupp ((mem_support_comap_iff h Z y).1 hy))
    simp only [ClosedBlowupSequence.pullbackReduced, hZc, dite_true]
    refine pullbackReduced_eq_nil_of_isOrderGe B _ _ _ hB.2.2.2.2.2 _ fun y hy => hh y ?_
    have := cosupport_birationalTransform_subset_of_isOrderGe s a E Z B hB hy
    rwa [Set.mem_preimage, ← Scheme.Hom.comp_apply, blowUpLift_comp] at this

/-- Case `maxord h^*I < m = maxord I`: every centre of `𝓑𝓓(X, I, E)` lies over
`cosupp(I, m)`, which `h(Y)` misses, so the reduced pull-back is empty. -/
private theorem pullback_bdFunctor_reduction_eq_nil {N m j : ℕ} (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M) (hm : 1 ≤ m)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ idealTriplesOfDim (Set.Icc 1 N) m ∧ j < t.E.s)
    {Y : Scheme.{u}} (h : Y ⟶ t.X) [Smooth h]
    (hY : t.pullback h ∈ idealTriplesOfDim (Set.Icc 1 N) m ∧ j < (t.pullback h).E.s)
    (hX : maxOrder t.I = m) (hYm : maxOrder (t.pullback h).I ≠ m) :
    ((bdFunctor M (dimNat t.X) m j t).pullback h).reduction = .nil Y := by
  rw [ClosedBlowupSequence.reduction_pullback]
  obtain ⟨n, hn, hXd⟩ := ht.1.2.1
  have hnX : dimNat t.X = n := by simp [dimNat, hXd]
  have hOrd := (bdFunctor_isOrderMTripleSeq (n := n) M hN hM t ht.1.1 hXd hn.1 hn.2 hm
    ht.1.2.2 ht.2).1
  rw [← hnX] at hOrd
  have hGe := ((ClosedBlowupSequence.isOrderGeMarkedTripleSeq_iff_isOrderMTripleSeq t.sX t.I t.E
    ht.1.1 m hX _).1).2 hOrd
  refine pullbackReduced_eq_nil_of_isOrderGe _ _ _ _ hGe h fun y hy => hYm ?_
  have hy' : (m : ℕ∞) ≤ multAt (t.I.comap h) y := by
    rwa [multAt_comap_of_smooth_of_mem_triples t ht.1.1 h y]
  refine le_antisymm hY.1.2.2 (hy'.trans ?_)
  change multAt (t.I.comap h) y ≤ maxOrderAlong (t.I.comap h) Set.univ
  exact le_iSup₂_of_le (f := fun z (_ : z ∈ Set.univ) => multAt (t.I.comap h) z) y
    (Set.mem_univ y) le_rfl

section PartIII

open CategoryTheory.Limits ClosedBlowupSequence

/-- The marked triple `(S, W_0𝒪_S, μ, E_S)` fed to `𝓜` by `𝓑𝓓`, for a given `S ⊆ B_ZX`. -/
private noncomputable def bdTS (m j : ℕ) (t : FieldBlowupTriple.{u}) (W : MarkedIdeal t.X)
    (Z : t.X.IdealSheafData) (S : (blowUp Z).IdealSheafData) : MarkedTriple.{u} :=
  ⟨⟨⟨S.subscheme, (W.birationalTransform Z).I.comap S.subschemeι,
    ((t.E.comap (blowUpToBase Z)).deleteIndex j).comap S.subschemeι⟩, t.k,
    S.subschemeι ≫ blowUpToBase Z ≫ t.sX⟩, m.factorial⟩

open Classical in
/-- The blow-up sequence `𝐁_S = 𝓜_{n-1,μ}(S, W_0𝒪_S, μ, E_S)` of `𝓑𝓓` (empty if `S = ∅` or the
input is not a marked triple). -/
private noncomputable def bdBS (M : MarkedFamily.{u}) (n m j : ℕ) (t : FieldBlowupTriple.{u})
    (W : MarkedIdeal t.X) (Z : t.X.IdealSheafData) (S : (blowUp Z).IdealSheafData) :
    ClosedBlowupSequence S.subscheme :=
  if (S.support : Set (blowUp Z)).Nonempty ∧ bdTS m j t W Z S ∈ markedTriples
    then M (n - 1) m.factorial (bdTS m j t W Z S) else .nil _

/-- The body of `𝓑𝓓`, with the centre `Z` and the divisor `S = π⁻¹E^j` as parameters. -/
private noncomputable def bdBody (M : MarkedFamily.{u}) (n m j : ℕ) (t : FieldBlowupTriple.{u})
    (W : MarkedIdeal t.X) (Z : t.X.IdealSheafData) (S : (blowUp Z).IdealSheafData) :
    ClosedBlowupSequence t.X :=
  (ClosedBlowupSequence.cons Z ((bdBS M n m j t W Z S).pushforward S.subschemeι)).reduction

private theorem bdFunctor_eq_bdBody (M : MarkedFamily.{u}) (n m j : ℕ) (t : FieldBlowupTriple.{u})
    (h : maxOrder t.I = m ∧ j < t.E.s) :
    bdFunctor M n m j t = bdBody M n m j t
      ⟨maximalCoefficientIdeal t.sX t.I m.factorial, m.factorial⟩
      (divisorComponentCentre ⟨maximalCoefficientIdeal t.sX t.I m.factorial, m.factorial⟩
        (t.E.E ⟨j, h.2⟩))
      ((t.E.E ⟨j, h.2⟩).comap (blowUpToBase (divisorComponentCentre
        ⟨maximalCoefficientIdeal t.sX t.I m.factorial, m.factorial⟩ (t.E.E ⟨j, h.2⟩)))) := by
  unfold bdFunctor
  rw [dif_pos h]
  rfl

private theorem reduction_cons_pullbackReduced {X Y : Scheme.{u}} (Z : X.IdealSheafData)
    (B : ClosedBlowupSequence (blowUp Z)) (h : Y ⟶ X) :
    (ClosedBlowupSequence.cons (Z.comap h) (B.pullbackReduced (canonicalLift h Z))).reduction =
      ((ClosedBlowupSequence.cons Z B).pullback h).reduction := by
  change _ = (ClosedBlowupSequence.cons (Z.comap h) (B.pullback (canonicalLift h Z))).reduction
  rw [← reduction_pullback]
  exact reduction_append_congr (ClosedBlowupSequence.cons (Z.comap h) (.nil _))
    (reduction_reduction _)

/-- A blow-up sequence pulled back (with deletion of empty blow-ups) along a morphism from an
empty scheme is empty. -/
private theorem pullbackReduced_eq_nil_of_isEmpty : ∀ {X Y : Scheme.{u}} [IsEmpty Y]
    (B : ClosedBlowupSequence X) (g : Y ⟶ X), B.pullbackReduced g = .nil Y
  | _, _, _, .nil _, _ => rfl
  | _, _, _, .cons Z B, g => by
    have hZ : Z.comap g = ⊤ := by
      rw [← Scheme.IdealSheafData.support_eq_bot_iff]
      refine eq_bot_iff.2 fun y => (IsEmpty.false y).elim
    simp only [ClosedBlowupSequence.pullbackReduced, hZ, dite_true]
    exact pullbackReduced_eq_nil_of_isEmpty B _

/-- The induced morphism `f⁻¹S → S` of closed subschemes. -/
private noncomputable def subschemeComapMap {X' X : Scheme.{u}} (S : X.IdealSheafData)
    (f : X' ⟶ X) : (S.comap f).subscheme ⟶ S.subscheme :=
  (S.comapIso f).hom ≫ pullback.snd f S.subschemeι

private theorem isPullback_subschemeComapMap {X' X : Scheme.{u}} (S : X.IdealSheafData)
    (f : X' ⟶ X) :
    IsPullback (subschemeComapMap S f) (S.comap f).subschemeι S.subschemeι f := by
  refine (IsPullback.of_iso_pullback (fst := (S.comap f).subschemeι)
    (snd := subschemeComapMap S f) ⟨?_⟩ (S.comapIso f) ?_ ?_).flip
  · simp [subschemeComapMap, pullback.condition]
  · simp
  · simp [subschemeComapMap]

private theorem orderedDivisor_comap_comap {X Y W : Scheme.{u}} (E : OrderedDivisor X)
    (f : Y ⟶ X) (g : W ⟶ Y) : (E.comap f).comap g = E.comap (g ≫ f) := by
  unfold OrderedDivisor.comap
  simp only [← Scheme.IdealSheafData.comap_comp]

private theorem orderedDivisor_deleteIndex_comap {X Y : Scheme.{u}} (E : OrderedDivisor X)
    (f : Y ⟶ X) (j : ℕ) : (E.comap f).deleteIndex j = (E.deleteIndex j).comap f := rfl

private theorem markedTriple_ext {k : Type u} [Field k] {X : Scheme.{u}} {I₁ I₂ : X.IdealSheafData}
    {E₁ E₂ : OrderedDivisor X} {s₁ s₂ : X ⟶ Spec (.of k)} {m : ℕ} (hI : I₁ = I₂) (hE : E₁ = E₂)
    (hs : s₁ = s₂) :
    (⟨⟨⟨X, I₁, E₁⟩, k, s₁⟩, m⟩ : MarkedTriple.{u}) = ⟨⟨⟨X, I₂, E₂⟩, k, s₂⟩, m⟩ := by
  subst hI hE hs; rfl

/-- The marked triple fed to `𝓜` on `Y` is the pull-back of the one on `X` along `h_S`. -/
private theorem bdTS_pullback (m j : ℕ) (t : FieldBlowupTriple.{u}) {Y : Scheme.{u}}
    (h : Y ⟶ t.X) (W : MarkedIdeal t.X) (Z : t.X.IdealSheafData)
    (S : (blowUp Z).IdealSheafData)
    (hbt : ((⟨W.I.comap h, W.m⟩ : MarkedIdeal Y).birationalTransform (Z.comap h)).I =
      (W.birationalTransform Z).I.comap (canonicalLift h Z)) :
    bdTS m j (t.pullback h) ⟨W.I.comap h, W.m⟩ (Z.comap h) (S.comap (canonicalLift h Z)) =
      (bdTS m j t W Z S).pullback (subschemeComapMap S (canonicalLift h Z)) := by
  have w1 := (isPullback_subschemeComapMap S (canonicalLift h Z)).w
  have w2 := canonicalLift_comp_blowUpToBase h Z
  unfold bdTS MarkedTriple.pullback FieldBlowupTriple.pullback
  refine markedTriple_ext ?_ ?_ ?_
  · change ((⟨W.I.comap h, W.m⟩ : MarkedIdeal Y).birationalTransform (Z.comap h)).I.comap _ = _
    rw [hbt, ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, w1]
  · change (((t.E.comap h).comap (blowUpToBase (Z.comap h))).deleteIndex j).comap _ = _
    rw [orderedDivisor_comap_comap, orderedDivisor_deleteIndex_comap,
      orderedDivisor_deleteIndex_comap, orderedDivisor_comap_comap, orderedDivisor_comap_comap,
      w1, orderedDivisor_comap_comap, Category.assoc, w2]
  · change _ ≫ blowUpToBase (Z.comap h) ≫ h ≫ t.sX = _
    rw [← Category.assoc (blowUpToBase (Z.comap h)), ← w2, reassoc_of% w1]
    simp

private theorem isEmpty_subscheme_of_support_eq_empty {X : Scheme.{u}} (S : X.IdealSheafData)
    (h : ¬ (S.support : Set X).Nonempty) : IsEmpty S.subscheme := by
  refine ⟨fun x => h ⟨S.subschemeι x, ?_⟩⟩
  rw [← Scheme.IdealSheafData.range_subschemeι]
  exact Set.mem_range_self x

private theorem support_comap_nonempty {X' X : Scheme.{u}} (S : X.IdealSheafData) (f : X' ⟶ X)
    (h : ((S.comap f).support : Set X').Nonempty) : (S.support : Set X).Nonempty := by
  obtain ⟨x, hx⟩ := h
  rw [Scheme.IdealSheafData.support_comap] at hx
  exact ⟨f x, hx⟩

private theorem dimNat_eq_of_hasDimensionIn_singleton {X : Scheme.{u}} {n : ℕ}
    (h : HasDimensionIn X {n}) : dimNat X = n := by
  obtain ⟨d, hd, hdd⟩ := h
  rw [Set.mem_singleton_iff] at hd
  simp [dimNat, hdd, hd]

private theorem hasDimensionIn_Icc_of_singleton {X : Scheme.{u}} {n N : ℕ}
    (h : HasDimensionIn X {n}) (hn : n ≤ N) : HasDimensionIn X (Set.Icc 0 N) := by
  obtain ⟨d, hd, hdd⟩ := h
  exact ⟨d, ⟨Nat.zero_le _, (Set.mem_singleton_iff.1 hd).trans_le hn⟩, hdd⟩

/-- The sequence `𝐁_S` fed to `𝓜` by `𝓑𝓓` commutes with smooth pull-back along `ĥ⁻¹S → S`:
property (2a) of `𝓜` applied to the marked triple on `S`. -/
private theorem bdBS_pullback {N m j : ℕ} (M : MarkedFamily.{u})
    (hM : IsMarkedOrderReductionFamily 0 (N - 1) M) (nX nY : ℕ)
    (t : FieldBlowupTriple.{u}) {Y : Scheme.{u}} (h : Y ⟶ t.X)
    (W : MarkedIdeal t.X) (Z : t.X.IdealSheafData) (S : (blowUp Z).IdealSheafData)
    [Smooth (canonicalLift h Z)]
    (hbt : ((⟨W.I.comap h, W.m⟩ : MarkedIdeal Y).birationalTransform (Z.comap h)).I =
      (W.birationalTransform Z).I.comap (canonicalLift h Z))
    (hX : (S.support : Set (blowUp Z)).Nonempty → bdTS m j t W Z S ∈ markedTriples ∧
      HasDimensionIn S.subscheme {nX - 1} ∧ nX - 1 ≤ N - 1)
    (hY : ((S.comap (canonicalLift h Z)).support : Set (blowUp (Z.comap h))).Nonempty →
      bdTS m j (t.pullback h) ⟨W.I.comap h, W.m⟩ (Z.comap h) (S.comap (canonicalLift h Z)) ∈
        markedTriples ∧ HasDimensionIn (S.comap (canonicalLift h Z)).subscheme {nY - 1} ∧
        nY - 1 ≤ N - 1) :
    bdBS M nY m j (t.pullback h) ⟨W.I.comap h, W.m⟩ (Z.comap h) (S.comap (canonicalLift h Z)) =
      (bdBS M nX m j t W Z S).pullbackReduced (subschemeComapMap S (canonicalLift h Z)) := by
  classical
  have hTS := bdTS_pullback m j t h W Z S hbt
  set ĥ := canonicalLift h Z
  by_cases hSY : ((S.comap ĥ).support : Set (blowUp (Z.comap h))).Nonempty
  · have hS := support_comap_nonempty S ĥ hSY
    obtain ⟨hXm, hXd, hXN⟩ := hX hS
    obtain ⟨hYm, hYd, hYN⟩ := hY hSY
    have hsm : Smooth (subschemeComapMap S ĥ) :=
      MorphismProperty.of_isPullback (P := @Smooth) (isPullback_subschemeComapMap S ĥ).flip
        inferInstance
    have hmtX : bdTS m j t W Z S ∈ markedTriplesOfDim (Set.Icc 0 (N - 1)) m.factorial :=
      ⟨hXm, rfl, hasDimensionIn_Icc_of_singleton hXd hXN⟩
    have hmtY : (bdTS m j t W Z S).pullback (subschemeComapMap S ĥ) ∈
        markedTriplesOfDim (Set.Icc 0 (N - 1)) m.factorial :=
      hTS ▸ ⟨hYm, rfl, hasDimensionIn_Icc_of_singleton hYd hYN⟩
    obtain ⟨F, hF, hFc⟩ := hM m.factorial (Nat.factorial_pos m)
    obtain ⟨-, -, hlft, hqc, -⟩ := hmtY.1
    have key := hFc.2.1.2 (bdTS m j t W Z S) hmtX (S.comap ĥ).subscheme
      (subschemeComapMap S ĥ) hsm hlft hqc hmtY
    have hnX : dimNat (bdTS m j t W Z S).X = nX - 1 := dimNat_eq_of_hasDimensionIn_singleton hXd
    have hnY : dimNat ((bdTS m j t W Z S).pullback (subschemeComapMap S ĥ)).X = nY - 1 :=
      dimNat_eq_of_hasDimensionIn_singleton hYd
    rw [hF _ hmtY, hF _ hmtX, hnY, hnX] at key
    have hBS : bdBS M nX m j t W Z S = M (nX - 1) m.factorial (bdTS m j t W Z S) := by
      unfold bdBS; exact if_pos ⟨hS, hXm⟩
    have hBSY : bdBS M nY m j (t.pullback h) ⟨W.I.comap h, W.m⟩ (Z.comap h) (S.comap ĥ) =
        M (nY - 1) m.factorial
          (bdTS m j (t.pullback h) ⟨W.I.comap h, W.m⟩ (Z.comap h) (S.comap ĥ)) := by
      unfold bdBS; exact if_pos ⟨hSY, hYm⟩
    rw [hBS, hBSY]
    have hM' := congr_arg_heq (M (nY - 1) m.factorial) hTS
    exact (eq_of_heq hM').trans (key.trans (reduction_pullback _ _))
  · have hBSY : bdBS M nY m j (t.pullback h) ⟨W.I.comap h, W.m⟩ (Z.comap h) (S.comap ĥ) =
        .nil _ := by
      unfold bdBS; exact if_neg fun hh => hSY hh.1
    rw [hBSY]
    exact (@pullbackReduced_eq_nil_of_isEmpty _ _
      (isEmpty_subscheme_of_support_eq_empty _ hSY) _ _).symm

/-- The two branches of `𝓑𝓓` correspond: `𝐁_S` does by `bdBS_pullback`, and push-forward along
`S ↪ B_Z X` commutes with the flat pull-back `ĥ`. -/
private theorem bdBody_pullback {N m j : ℕ} (M : MarkedFamily.{u})
    (hM : IsMarkedOrderReductionFamily 0 (N - 1) M) (nX nY : ℕ)
    (t : FieldBlowupTriple.{u}) {Y : Scheme.{u}} (h : Y ⟶ t.X) [Smooth h]
    (W : MarkedIdeal t.X) (Z : t.X.IdealSheafData) (S : (blowUp Z).IdealSheafData)
    (hbt : ((⟨W.I.comap h, W.m⟩ : MarkedIdeal Y).birationalTransform (Z.comap h)).I =
      (W.birationalTransform Z).I.comap (canonicalLift h Z))
    (hX : (S.support : Set (blowUp Z)).Nonempty → bdTS m j t W Z S ∈ markedTriples ∧
      HasDimensionIn S.subscheme {nX - 1} ∧ nX - 1 ≤ N - 1)
    (hY : ((S.comap (canonicalLift h Z)).support : Set (blowUp (Z.comap h))).Nonempty →
      bdTS m j (t.pullback h) ⟨W.I.comap h, W.m⟩ (Z.comap h) (S.comap (canonicalLift h Z)) ∈
        markedTriples ∧ HasDimensionIn (S.comap (canonicalLift h Z)).subscheme {nY - 1} ∧
        nY - 1 ≤ N - 1) :
    bdBody M nY m j (t.pullback h) ⟨W.I.comap h, W.m⟩ (Z.comap h) (S.comap (canonicalLift h Z)) =
      ((bdBody M nX m j t W Z S).pullback h).reduction := by
  haveI : Flat (canonicalLift h Z) := Kollar.flat_canonicalLift h Z
  haveI : Smooth (canonicalLift h Z) :=
    MorphismProperty.of_isPullback (P := @Smooth) (Kollar.isPullback_canonicalLift_of_flat h Z)
      inferInstance
  unfold bdBody
  rw [bdBS_pullback M hM nX nY t h W Z S hbt hX hY]
  refine (congrArg (fun B => (ClosedBlowupSequence.cons (Z.comap h) B).reduction)
    (pushforward_pullbackReduced S.subschemeι _ _ _ (isPullback_subschemeComapMap S _) _)).trans ?_
  rw [reduction_cons_pullbackReduced]
  exact (reduction_pullback_reduction _ h).symm

/-- Maximal coefficient ideals commute with smooth pull-back when the maximal order is kept. -/
private theorem maximalCoefficientIdeal_comap_of_smooth_of_mem_triples (t : FieldBlowupTriple.{u})
    (ht : t ∈ triples) (hd : 1 ≤ topologicalKrullDim t.X) {Y : Scheme.{u}} (h : Y ⟶ t.X)
    [Smooth h] (hmY : maxOrder (t.I.comap h) = maxOrder t.I) (s : ℤ) :
    maximalCoefficientIdeal (h ≫ t.sX) (t.I.comap h) s =
      (maximalCoefficientIdeal t.sX t.I s).comap h := by
  obtain ⟨hchar, hsm, hlft, -, he, -⟩ := ht
  haveI : Smooth t.sX := (MMP.Mori.isSmoothScheme_iff _).1 hsm
  have hdim := pos_topologicalKrullDim_of_mem_irreducibleComponents he hd
  have hD (r : ℕ) : higherDerivativeIdeal (h ≫ t.sX) (t.I.comap h) r =
      (higherDerivativeIdeal t.sX t.I r).comap h := by
    induction r with
    | zero => rfl
    | succ r ih =>
      rw [higherDerivativeIdeal_succ, higherDerivativeIdeal_succ, ih,
        derivativeIdeal_comap_of_smooth t.sX (h ≫ t.sX) h rfl hdim]
  unfold maximalCoefficientIdeal
  rw [hmY]
  simp only [(Scheme.IdealSheafData.map_gc h).l_iSup, Stacks.IdealSheaf.comap_finset_prod,
    Stacks.IdealSheaf.comap_pow, hD]

section Centre

open Aux

/-- The generic point of a component of a closed set is a generic point of that component. -/
theorem isGenericPoint_genericPoint_of_isClosed_of_mem_componentsOf {α : Type*}
    [TopologicalSpace α] [QuasiSober α] {T C : Set α} (hT : IsClosed T) (hC : C ∈ componentsOf T) :
    IsGenericPoint hC.1.1.genericPoint C :=
  hC.1.1.isGenericPoint_genericPoint (Aux.isClosed_of_mem_componentsOf hT hC)

/-- Under a flat morphism, the closure of the image of the generic point of an irreducible
component of `h⁻¹T` is an irreducible component of `T`. -/
private theorem closure_image_genericPoint_mem_componentsOf {X Y : Scheme.{u}} (h : Y ⟶ X)
    [Flat h] {T : Set X} (hT : IsClosed T) {C' : Set Y} (hC' : C' ∈ componentsOf (h ⁻¹' T)) :
    closure {h hC'.1.1.genericPoint} ∈ componentsOf T := by
  have hirr := hC'.1.1
  have hTY : IsClosed (h ⁻¹' T) := hT.preimage h.continuous
  have hgen := isGenericPoint_genericPoint_of_isClosed_of_mem_componentsOf hTY hC'
  have hηC : hirr.genericPoint ∈ C' := hgen.mem
  refine ⟨⟨isIrreducible_singleton.closure, closure_minimal
    (Set.singleton_subset_iff.2 (hC'.1.2 hηC)) hT⟩, ?_⟩
  rintro W' ⟨hW'irr, hW'T⟩ hle
  have hσ := hW'irr.isGenericPoint_genericPoint_closure
  have hξσ : hW'irr.genericPoint ⤳ h hirr.genericPoint := by
    rw [specializes_iff_mem_closure, hσ.def]
    exact subset_closure (hle (subset_closure (Set.mem_singleton _)))
  obtain ⟨η'', hη''spec, hη''eq⟩ := Flat.generalizingMap h hξσ
  have hσT : hW'irr.genericPoint ∈ T := closure_minimal hW'T hT hσ.mem
  have hη''T : η'' ∈ h ⁻¹' T := by
    change h η'' ∈ T
    rwa [hη''eq]
  have hsub : C' ⊆ closure {η''} := by
    rw [← hgen.def]
    exact closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 hη''spec))
      isClosed_closure
  have h2 := hC'.2 ⟨isIrreducible_singleton.closure,
    closure_minimal (Set.singleton_subset_iff.2 hη''T) hTY⟩ hsub
  have hη''C : η'' ∈ C' := h2 (subset_closure (Set.mem_singleton _))
  have hs : hirr.genericPoint ⤳ η'' := by
    rwa [specializes_iff_mem_closure, hgen.def]
  have hσmem : hW'irr.genericPoint ∈ closure {h hirr.genericPoint} := by
    rw [← hη''eq]
    exact specializes_iff_mem_closure.1 (hs.map h.continuous)
  calc W' ⊆ closure W' := subset_closure
    _ = closure {hW'irr.genericPoint} := hσ.def.symm
    _ ⊆ closure {h hirr.genericPoint} :=
      closure_minimal (Set.singleton_subset_iff.2 hσmem) isClosed_closure

/-- Membership in the support of `Z_{-1}(K, D)`: the point lies on an irreducible component of
`D` contained in `cosupp K`. -/
private theorem mem_support_divisorComponentCentre {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [QuasiCompact sX] (K : MarkedIdeal X)
    (D : X.IdealSheafData) (x : X) :
    x ∈ ((divisorComponentCentre K D).support : Set X) ↔
      ∃ C ∈ componentsOf (D.support : Set X), C ⊆ K.cosupport ∧ x ∈ C := by
  set S : Set (Set X) := {W | W ∈ componentsOf (D.support : Set X) ∧ W ⊆ K.cosupport} with hSdef
  have hS : S ⊆ componentsOf (D.support : Set X) := fun W hW => hW.1
  have hU := isClosed_sUnion_of_subset_componentsOf sX D S hS
  have hsupC : (divisorComponentCentre K D).support = Closeds.closure (⋃₀ S) := by
    ext x; simp [divisorComponentCentre, hSdef]
  have hT : ((Closeds.closure (⋃₀ S) : Closeds X) : Set X) = ⋃₀ S := by
    simp [hU.closure_eq]
  rw [hsupC, hT]
  simp only [hSdef, Set.mem_sUnion, Set.mem_setOf_eq, and_assoc]

/-- Orders at the points of `Y` are those of the image, for the pull-back of the marked ideal;
then `Z_{-1}` of the pull-back has support `h⁻¹` of that of `Z_{-1}`. -/
private theorem mem_support_divisorComponentCentre_comap {k : Type u} [Field k] [CharZero k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX] [LocallyOfFiniteType sX]
    [QuasiCompact sX] (h : Y ⟶ X) [Smooth h] [QuasiCompact (h ≫ sX)]
    (K : MarkedIdeal X) (D : X.IdealSheafData)
    (hD : MMP.Mori.IsSmoothScheme (D.subschemeι ≫ sX))
    (hmult : ∀ y, multAt (K.I.comap h) y = multAt K.I (h y)) (y : Y) :
    y ∈ ((divisorComponentCentre (⟨K.I.comap h, K.m⟩ : MarkedIdeal Y) (D.comap h)).support :
        Set Y) ↔ h y ∈ ((divisorComponentCentre K D).support : Set X) := by
  rw [mem_support_divisorComponentCentre (h ≫ sX), mem_support_divisorComponentCentre sX]
  have hTc : IsClosed (D.support : Set X) := D.support.isClosed
  have hsupp : ((D.comap h).support : Set Y) = h ⁻¹' (D.support : Set X) := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  have hcosY : ∀ z : Y, z ∈ (⟨K.I.comap h, K.m⟩ : MarkedIdeal Y).cosupport ↔
      h z ∈ K.cosupport := fun z => by
    change (K.m : ℕ∞) ≤ multAt (K.I.comap h) z ↔ (K.m : ℕ∞) ≤ multAt K.I (h z)
    rw [hmult]
  have hclK : IsClosed K.cosupport := isClosed_setOf_le_multAt sX K.I K.m
  have hclKY : IsClosed (⟨K.I.comap h, K.m⟩ : MarkedIdeal Y).cosupport :=
    isClosed_setOf_le_multAt (h ≫ sX) _ _
  have hTY : IsClosed (h ⁻¹' (D.support : Set X)) := hTc.preimage h.continuous
  simp only [hsupp]
  constructor
  · rintro ⟨C', hC', hsub, hyC'⟩
    have hgenC := closure_image_genericPoint_mem_componentsOf h hTc hC'
    have hirr := hC'.1.1
    have hgen := isGenericPoint_genericPoint_of_isClosed_of_mem_componentsOf hTY hC'
    refine ⟨_, hgenC, closure_minimal (Set.singleton_subset_iff.2
      ((hcosY _).1 (hsub hgen.mem))) hclK, ?_⟩
    have : hirr.genericPoint ⤳ y := by
      rwa [specializes_iff_mem_closure, hgen.def]
    exact (this.map h.continuous).mem_closure
  · rintro ⟨C, hC, hsub, hyC⟩
    have hyT : y ∈ h ⁻¹' (D.support : Set X) := hC.1.2 hyC
    haveI : NoetherianSpace Y := noetherianSpace_of_finiteType (h ≫ sX)
    obtain ⟨C', hC', hyC'⟩ := (finite_and_cover_componentsOf hTY).2 hyT
    have hgenC := closure_image_genericPoint_mem_componentsOf h hTc hC'
    have hirr := hC'.1.1
    have hgen := isGenericPoint_genericPoint_of_isClosed_of_mem_componentsOf hTY hC'
    have hyc : h y ∈ closure {h hirr.genericPoint} := by
      have : hirr.genericPoint ⤳ y := by
        rwa [specializes_iff_mem_closure, hgen.def]
      exact (this.map h.continuous).mem_closure
    have hCeq := eq_of_mem_componentsOf_of_isSmoothScheme sX D hD hC hgenC hyC hyc
    have hξ : h hirr.genericPoint ∈ K.cosupport :=
      hsub (hCeq ▸ subset_closure (Set.mem_singleton _))
    refine ⟨C', hC', ?_, hyC'⟩
    rw [← hgen.def]
    exact closure_minimal (Set.singleton_subset_iff.2 ((hcosY _).2 hξ)) hclKY

/-- The inverse image of a smooth closed subscheme under a smooth morphism is reduced. -/
private theorem isReduced_comap_subscheme_of_smooth {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (h : Y ⟶ X) [Smooth h]
    (Z : X.IdealSheafData) (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX)) :
    IsReduced (Z.comap h).subscheme := by
  haveI : LocallyOfFinitePresentation (Z.subschemeι ≫ sX) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := Z.subschemeι ≫ sX)).mpr
      inferInstance
  haveI : Smooth (Z.subschemeι ≫ sX) := (MMP.Mori.isSmoothScheme_iff _).1 hZ
  obtain ⟨-, hreg⟩ := regular_stalks_of_smooth (pullback.snd h Z.subschemeι ≫ Z.subschemeι ≫ sX)
  haveI : ∀ x : (pullback h Z.subschemeι : Scheme.{u}),
      _root_.IsReduced ((pullback h Z.subschemeι : Scheme.{u}).presheaf.stalk x) :=
    fun x => by
      haveI := hreg x
      haveI : IsDomain ((pullback h Z.subschemeι : Scheme.{u}).presheaf.stalk x) :=
        IsRegularLocalRing.isDomain _
      infer_instance
  haveI : IsReduced (pullback h Z.subschemeι : Scheme.{u}) :=
    isReduced_of_isReduced_stalk (pullback h Z.subschemeι : Scheme.{u})
  exact isReduced_of_isOpenImmersion (Z.comapIso h).hom

/-- `Z_{-1}` commutes with smooth pull-back. -/
private theorem divisorComponentCentre_comap {k : Type u} [Field k] [CharZero k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX] [LocallyOfFiniteType sX]
    [QuasiCompact sX] (h : Y ⟶ X) [Smooth h] [QuasiCompact (h ≫ sX)]
    (K : MarkedIdeal X) (D : X.IdealSheafData)
    (hD : MMP.Mori.IsSmoothScheme (D.subschemeι ≫ sX)) (hD' : MMP.Mori.IsPureCodimOne D.support)
    (hmult : ∀ y, multAt (K.I.comap h) y = multAt K.I (h y)) :
    divisorComponentCentre (⟨K.I.comap h, K.m⟩ : MarkedIdeal Y) (D.comap h) =
      (divisorComponentCentre K D).comap h := by
  have hZsm := (divisorComponentCentre_spec sX K D hD hD').1
  haveI := isReduced_comap_subscheme_of_smooth sX h _ hZsm
  have hsupp : (((divisorComponentCentre K D).comap h).support : Closeds Y) =
      (divisorComponentCentre (⟨K.I.comap h, K.m⟩ : MarkedIdeal Y) (D.comap h)).support := by
    ext y
    rw [Scheme.IdealSheafData.support_comap]
    exact (mem_support_divisorComponentCentre_comap sX h K D hD hmult y).symm
  haveI : IsReduced (divisorComponentCentre (⟨K.I.comap h, K.m⟩ : MarkedIdeal Y)
      (D.comap h)).subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  exact (Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ rfl).trans
    (Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ hsupp).symm

/-- `π^*W ⊆ (π^*I_Z)^μ` for the centre `Z_{-1}`: the order of `W` along `Z_{-1}` is `≥ μ`. -/
private theorem comap_le_comap_pow_divisorComponentCentre {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [QuasiCompact sX]
    (hX : MMP.Mori.IsSmoothScheme sX) (K : MarkedIdeal X) (D : X.IdealSheafData)
    (hD : MMP.Mori.IsSmoothScheme (D.subschemeι ≫ sX)) (hD' : MMP.Mori.IsPureCodimOne D.support) :
    K.I.comap (blowUpToBase (divisorComponentCentre K D)) ≤
      (divisorComponentCentre K D).comap (blowUpToBase (divisorComponentCentre K D)) ^ K.m := by
  refine comap_le_comap_pow_of_stalk_le _ _ _ _ fun x => ?_
  refine stalk_le_pow_of_orderAlongGE sX hX _ (divisorComponentCentre_spec sX K D hD hD').1
    K.I K.m ?_ x
  intro W hW
  have hcl : IsClosed W := Aux.isClosed_of_mem_componentsOf
    (divisorComponentCentre K D).support.isClosed hW
  have hgen : IsGenericPoint hW.1.1.genericPoint W := by
    simpa [hcl.closure_eq] using hW.1.1.isGenericPoint_genericPoint_closure
  have hmem : hW.1.1.genericPoint ∈ ((divisorComponentCentre K D).support : Set X) :=
    hW.1.2 hgen.mem
  obtain ⟨C, -, hsub, hxC⟩ := (mem_support_divisorComponentCentre sX K D _).1 hmem
  exact hsub hxC

end Centre

/-- The input of `𝓜` in `𝓑𝓓`: marked triple of dimension `n - 1` when `S ≠ ∅`. -/
private theorem bd_input_facts {m j n : ℕ} (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hm : 1 ≤ m) (hmax : maxOrder t.I = m) (hj : j < t.E.s) (hn : 1 ≤ n)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞))
    (W : MarkedIdeal t.X)
    (hW : W = ⟨maximalCoefficientIdeal t.sX t.I m.factorial, m.factorial⟩)
    (Z : t.X.IdealSheafData) (hZ : Z = divisorComponentCentre W (t.E.E ⟨j, hj⟩))
    (S : (blowUp Z).IdealSheafData) (hS : S = (t.E.E ⟨j, hj⟩).comap (blowUpToBase Z)) :
    (S.support : Set (blowUp Z)).Nonempty →
      bdTS m j t W Z S ∈ markedTriples ∧ HasDimensionIn S.subscheme {n - 1} := by
  subst hW hZ hS
  intro hne
  have h2 := bdFunctor_input_mem_markedTriplesOfDim (m := m) (n := n) (j := j) t ht hm hmax hj hn
    hdim hne
  exact ⟨isTriple_of_deleteEmpty h2.1, h2.2.2⟩

private theorem bdBody_congr (M : MarkedFamily.{u}) (n m j : ℕ) (tY : FieldBlowupTriple.{u})
    (W₁ W₂ : MarkedIdeal tY.X) (hW : W₁ = W₂) (Z₁ Z₂ : tY.X.IdealSheafData) (hZ : Z₁ = Z₂)
    (S₁ : (blowUp Z₁).IdealSheafData) (S₂ : (blowUp Z₂).IdealSheafData) (hS : HEq S₁ S₂) :
    bdBody M n m j tY W₁ Z₁ S₁ = bdBody M n m j tY W₂ Z₂ S₂ := by
  subst hW hZ
  obtain rfl := eq_of_heq hS
  rfl

private theorem heq_comap_blowUpToBase {X : Scheme.{u}} (D : X.IdealSheafData)
    {Z₁ Z₂ : X.IdealSheafData} (hZ : Z₁ = Z₂) :
    HEq (D.comap (blowUpToBase Z₁)) (D.comap (blowUpToBase Z₂)) := by
  subst hZ; rfl

end PartIII

/-- Case `maxord h^*I = maxord I = m`: the centres `Z_{-1}` and the restrictions to `E^j`
correspond under `h`, (2a) for `𝓜` applies on `E^j`, and push-forward commutes with flat
pull-back. -/
private theorem bdFunctor_pullback_of_maxOrder_eq {N m j : ℕ} (M : MarkedFamily.{u})
    (hM : IsMarkedOrderReductionFamily 0 (N - 1) M) (hm : 1 ≤ m)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ idealTriplesOfDim (Set.Icc 1 N) m ∧ j < t.E.s)
    {Y : Scheme.{u}} (h : Y ⟶ t.X) [Smooth h]
    (hlft : LocallyOfFiniteType (h ≫ t.sX)) (hqc : QuasiCompact (h ≫ t.sX))
    (hY : t.pullback h ∈ idealTriplesOfDim (Set.Icc 1 N) m ∧ j < (t.pullback h).E.s)
    (hX : maxOrder t.I = m) (hYm : maxOrder (t.pullback h).I = m) :
    bdFunctor M (dimNat Y) m j (t.pullback h) =
      ((bdFunctor M (dimNat t.X) m j t).pullback h).reduction := by
  classical
  have htr : t ∈ triples := ht.1.1
  have hd : 1 ≤ topologicalKrullDim t.X := one_le_topologicalKrullDim ht
  obtain ⟨hchar, hsm, hlft0, hqc0, he, hnz, hOD, hSNC⟩ := id htr
  haveI : CharZero t.k := hchar
  haveI : LocallyOfFiniteType t.sX := hlft0
  haveI : QuasiCompact t.sX := hqc0
  haveI : LocallyOfFinitePresentation t.sX :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := t.sX)).mpr hlft0
  haveI : Smooth t.sX := (MMP.Mori.isSmoothScheme_iff _).1 hsm
  haveI : LocallyOfFiniteType (h ≫ t.sX) := hlft
  haveI : QuasiCompact (h ≫ t.sX) := hqc
  obtain ⟨nX, hnX, hdX⟩ := ht.1.2.1
  obtain ⟨nY, hnY, hdY⟩ := hY.1.2.1
  have hdimX : dimNat t.X = nX := dimNat_eq_of_hasDimensionIn_singleton ⟨_, rfl, hdX⟩
  have hdimY : dimNat Y = nY := dimNat_eq_of_hasDimensionIn_singleton ⟨_, rfl, hdY⟩
  rw [bdFunctor_eq_bdBody M (dimNat Y) m j (t.pullback h) ⟨hYm, hY.2⟩,
    bdFunctor_eq_bdBody M (dimNat t.X) m j t ⟨hX, ht.2⟩, hdimX, hdimY]
  set μ := m.factorial with hμ
  set WX : MarkedIdeal t.X := ⟨maximalCoefficientIdeal t.sX t.I μ, μ⟩ with hWXdef
  set DX := t.E.E ⟨j, ht.2⟩ with hDX
  have hDsm : MMP.Mori.IsSmoothScheme (DX.subschemeι ≫ t.sX) := (hSNC.1 ⟨j, ht.2⟩).2.2
  have hDcod : MMP.Mori.IsPureCodimOne DX.support := (hSNC.1 ⟨j, ht.2⟩).2.1
  have hmY : maxOrder (t.I.comap h) = maxOrder t.I := hYm.trans hX.symm
  have hWY : (⟨maximalCoefficientIdeal (t.pullback h).sX (t.pullback h).I μ, μ⟩ :
      MarkedIdeal Y) = ⟨WX.I.comap h, WX.m⟩ := by
    congr 1
    exact maximalCoefficientIdeal_comap_of_smooth_of_mem_triples t htr hd h hmY μ
  have hmult : ∀ y, multAt (WX.I.comap h) y = multAt WX.I (h y) := fun y =>
    multAt_comap_of_smooth t.sX h WX.I y
  have hZY2 : divisorComponentCentre (⟨WX.I.comap h, WX.m⟩ : MarkedIdeal Y)
      ((t.pullback h).E.E ⟨j, hY.2⟩) = (divisorComponentCentre WX DX).comap h :=
    divisorComponentCentre_comap t.sX h WX DX hDsm hDcod hmult
  have hZY : divisorComponentCentre (⟨maximalCoefficientIdeal (t.pullback h).sX
      (t.pullback h).I μ, μ⟩ : MarkedIdeal Y) ((t.pullback h).E.E ⟨j, hY.2⟩) =
      (divisorComponentCentre WX DX).comap h := by
    rwa [hWY]
  set ZX := divisorComponentCentre WX DX with hZXdef
  set SX := DX.comap (blowUpToBase ZX) with hSXdef
  have hbt : ((⟨WX.I.comap h, WX.m⟩ : MarkedIdeal Y).birationalTransform (ZX.comap h)).I =
      (WX.birationalTransform ZX).I.comap (canonicalLift h ZX) :=
    congrArg MarkedIdeal.I (MMP.Resolution.Kollar.birationalTransform_comap_eq_comap_canonicalLift
      h ZX WX (comap_le_comap_pow_divisorComponentCentre t.sX hsm WX DX hDsm hDcod))
  have hSeq : ((t.pullback h).E.E ⟨j, hY.2⟩).comap (blowUpToBase (ZX.comap h)) =
      SX.comap (canonicalLift h ZX) := by
    change (DX.comap h).comap (blowUpToBase (ZX.comap h)) = _
    rw [hSXdef, ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      canonicalLift_comp_blowUpToBase]
  have hX' : (SX.support : Set (blowUp ZX)).Nonempty → bdTS m j t WX ZX SX ∈ markedTriples ∧
      HasDimensionIn SX.subscheme {nX - 1} ∧ nX - 1 ≤ N - 1 := by
    intro hne
    obtain ⟨h1, h2⟩ := bd_input_facts t htr hm hX ht.2 hnX.1 hdX WX rfl ZX rfl SX rfl hne
    exact ⟨h1, h2, by have := hnX.2; omega⟩
  have hY' : ((SX.comap (canonicalLift h ZX)).support : Set (blowUp (ZX.comap h))).Nonempty →
      bdTS m j (t.pullback h) ⟨WX.I.comap h, WX.m⟩ (ZX.comap h) (SX.comap (canonicalLift h ZX)) ∈
        markedTriples ∧ HasDimensionIn (SX.comap (canonicalLift h ZX)).subscheme {nY - 1} ∧
        nY - 1 ≤ N - 1 := by
    intro hne
    obtain ⟨h1, h2⟩ := bd_input_facts (m := m) (j := j) (n := nY) (t.pullback h) hY.1.1 hm hYm
      hY.2 hnY.1 hdY ⟨WX.I.comap h, WX.m⟩ hWY.symm (ZX.comap h) hZY2.symm
      (SX.comap (canonicalLift h ZX)) hSeq.symm hne
    exact ⟨h1, h2, by have := hnY.2; omega⟩
  have key := bdBody_pullback (m := m) (j := j) M hM nX nY t h WX ZX SX hbt hX' hY'
  refine (bdBody_congr M nY m j (t.pullback h) _ _ hWY _ _ hZY _ _ ?_).trans key
  exact (heq_comap_blowUpToBase _ hZY).trans (heq_of_eq hSeq)

/-- Part (b): `𝓑𝓓(Y, h^*I, h⁻¹E) = (h^*𝓑𝓓(X, I, E))^red`. -/
private theorem bdFunctor_pullback {N m j : ℕ} (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M) (hm : 1 ≤ m)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ idealTriplesOfDim (Set.Icc 1 N) m ∧ j < t.E.s)
    {Y : Scheme.{u}} (h : Y ⟶ t.X) [Smooth h]
    (hlft : LocallyOfFiniteType (h ≫ t.sX)) (hqc : QuasiCompact (h ≫ t.sX))
    (hY : t.pullback h ∈ idealTriplesOfDim (Set.Icc 1 N) m ∧ j < (t.pullback h).E.s) :
    bdFunctor M (dimNat Y) m j (t.pullback h) =
      ((bdFunctor M (dimNat t.X) m j t).pullback h).reduction := by
  by_cases hYm : maxOrder (t.pullback h).I = m
  · have hX : maxOrder t.I = m := le_antisymm ht.1.2.2
      (hYm ▸ maxOrder_comap_le_of_smooth t ht.1.1 h)
    exact bdFunctor_pullback_of_maxOrder_eq M hM hm t ht h hlft hqc hY hX hYm
  · have hL : bdFunctor M (dimNat Y) m j (t.pullback h) = .nil Y := by
      unfold bdFunctor
      rw [dif_neg (fun hc => hYm hc.1)]
      rfl
    rw [hL]
    by_cases hX : maxOrder t.I = m
    · exact (pullback_bdFunctor_reduction_eq_nil M hN hM hm t ht h hY hX hYm).symm
    · have hR : bdFunctor M (dimNat t.X) m j t = .nil t.X := by
        unfold bdFunctor
        rw [dif_neg (fun hc => hX hc.1)]
      rw [hR]
      rfl

end Smooth

/-- **Kollár, Lemma 3.102 (2), smooth morphisms.** Let `N ≥ 1`, let `𝓜` be a marked
order-reduction family on dimensions `0, …, N - 1` (`IsMarkedOrderReductionFamily`), `m ≥ 1`
and `j` a (`0`-based) index. On the class of triples `(X, I, E)` with `1 ≤ dim X ≤ N`,
`maxord I ≤ m` and `j < s` (`E = (E^0, …, E^{s-1})`), the functor
`(X, I, E) ↦ bdFunctor M (dim X) m j (X, I, E)` commutes with smooth morphisms
(`CommutesWithSmoothOn`). -/
@[mmp "lem_kr3e_bd_commutes_smooth"]
public theorem commutesWithSmoothOn_bdFunctor {N m j : ℕ} (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M) (hm : 1 ≤ m) :
    CommutesWithSmoothOn {t | t ∈ idealTriplesOfDim (Set.Icc 1 N) m ∧ j < t.E.s}
      (fun t _ => bdFunctor M (dimNat t.X) m j t) := by
  refine ⟨fun t ht Y h hs hsurj hlft hqc hY => ?_, fun t ht Y h hs hlft hqc hY => ?_⟩
  · exact (bdFunctor_pullback M hN hM hm t ht h hlft hqc hY).trans
      (ClosedBlowupSequence.reduction_eq_self
        (ClosedBlowupSequence.hasNoEmptyBlowups_pullback _ (hasNoEmptyBlowups_bdFunctor ..) h))
  · exact bdFunctor_pullback M hN hM hm t ht h hlft hqc hY

/-! ### Separation of the marked cosupport from `E^j` -/

section Separation

section Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {f : β → α}

/-- A closed subset `C` in the image of an open embedding `f` is an irreducible component of
`D` exactly when `f⁻¹C` is an irreducible component of `f⁻¹D`. -/
private theorem mem_componentsOf_iff_preimage (hf : Topology.IsOpenEmbedding f) {D C : Set α}
    (hC : IsClosed C) (hCf : C ⊆ Set.range f) :
    C ∈ componentsOf D ↔ f ⁻¹' C ∈ componentsOf (f ⁻¹' D) := by
  constructor
  · rintro ⟨⟨hirr, hCD⟩, hmax⟩
    have hne : (f ⁻¹' C).Nonempty := by
      obtain ⟨c, hc⟩ := hirr.nonempty
      obtain ⟨b, rfl⟩ := hCf hc
      exact ⟨b, hc⟩
    refine ⟨⟨⟨hne, hirr.isPreirreducible.preimage hf⟩, Set.preimage_mono hCD⟩, ?_⟩
    rintro T ⟨hT, hTD⟩ hle
    have hCT : C ⊆ f '' T := by
      intro c hc
      obtain ⟨b, rfl⟩ := hCf hc
      exact ⟨b, hle hc, rfl⟩
    have := hmax ⟨hT.image f hf.continuous.continuousOn,
      (Set.image_mono hTD).trans (Set.image_preimage_subset f D)⟩ hCT
    intro b hb
    exact this ⟨b, hb, rfl⟩
  · rintro ⟨⟨hirr, hCD⟩, hmax⟩
    have hCeq : f '' (f ⁻¹' C) = C := Set.image_preimage_eq_of_subset hCf
    refine ⟨⟨hCeq ▸ hirr.image f hf.continuous.continuousOn, ?_⟩, ?_⟩
    · rw [← hCeq]
      exact (Set.image_mono hCD).trans (Set.image_preimage_subset f D)
    · rintro S ⟨hS, hSD⟩ hle
      have hSne : (f ⁻¹' S).Nonempty := hirr.nonempty.mono (Set.preimage_mono hle)
      have h1 := hmax ⟨⟨hSne, hS.isPreirreducible.preimage hf⟩, Set.preimage_mono hSD⟩
        (Set.preimage_mono hle)
      have hSU : (S ∩ Set.range f).Nonempty := by
        obtain ⟨b, hb⟩ := hSne
        exact ⟨f b, hb, b, rfl⟩
      refine (subset_closure_inter_of_isPreirreducible_of_isOpen hS.isPreirreducible
        hf.isOpen_range hSU).trans (hC.closure_subset_iff.2 ?_)
      rintro _ ⟨hx, b, rfl⟩
      exact h1 hx

end Topology

/-- The codimension of an irreducible closed subset meeting the image of an open embedding
`f` is that of its inverse image. -/
private theorem codimension_irreducibleClosure_preimage {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] {C : Set X} (hC : IsIrreducible C) (hC' : IsIrreducible (j ⁻¹' C))
    (hCf : C ⊆ Set.range j) :
    codimension (irreducibleClosure hC) = codimension (irreducibleClosure hC') := by
  have hf := j.isOpenEmbedding
  have hmap : irreducibleClosure hC =
      TopologicalSpace.IrreducibleCloseds.map j hf.continuous (irreducibleClosure hC') := by
    ext1
    exact (show closure (j '' closure (j ⁻¹' C)) = closure C by
      rw [closure_image_closure hf.continuous, Set.image_preimage_eq_of_subset hCf]).symm
  rw [hmap, codimension_eq_coheight, codimension_eq_coheight]
  refine (Order.coheight_eq_of_strictMono _
    (TopologicalSpace.IrreducibleCloseds.map_strictMono_of_isInducing hf.isInducing) ?_ _).symm
  intro a b hab
  let e := TopologicalSpace.IrreducibleCloseds.orderIsoOfIsOpenEmbedding j hf
  have hb : (j ⁻¹' (b : Set X)).Nonempty := by
    obtain ⟨x, hx⟩ := a.isIrreducible.nonempty
    exact ⟨x, hab.le (subset_closure ⟨x, hx, rfl⟩)⟩
  refine ⟨e.symm ⟨b, hb⟩, ?_, ?_⟩
  · rw [← e.lt_iff_lt, OrderIso.apply_symm_apply]
    exact hab
  · exact congrArg Subtype.val (e.apply_symm_apply ⟨b, hb⟩)

/-- The support of `j⁻¹I` is the inverse image of the support of `I`. -/
private theorem coe_support_comap {U X : Scheme.{u}} (j : U ⟶ X) (I : X.IdealSheafData) :
    ((I.comap j).support : Set U) = j ⁻¹' (I.support : Set X) :=
  Set.ext (mem_support_comap_iff j I)

/-- An irreducible component of `j⁻¹D`, for `D` closed in the image of `j`, is the inverse image
of an irreducible component of `D`. -/
private theorem exists_mem_componentsOf_preimage_eq {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] {D : Set X} (hD : IsClosed D) (hDj : D ⊆ Set.range j) {T : Set U}
    (hT : T ∈ componentsOf (j ⁻¹' D)) : ∃ C, C ∈ componentsOf D ∧ j ⁻¹' C = T := by
  have hTc : IsClosed T := Aux.isClosed_of_mem_componentsOf (hD.preimage j.continuous) hT
  have hCD : closure (j '' T) ⊆ D :=
    closure_minimal ((Set.image_mono hT.1.2).trans (Set.image_preimage_subset _ _)) hD
  have hpre : j ⁻¹' closure (j '' T) = T := by
    rw [j.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage j.continuous,
      Set.preimage_image_eq _ j.isOpenEmbedding.injective, hTc.closure_eq]
  refine ⟨closure (j '' T), ?_, hpre⟩
  rw [mem_componentsOf_iff_preimage j.isOpenEmbedding isClosed_closure (hCD.trans hDj), hpre]
  exact hT

/-- `j⁻¹(Z^{≥2}) = (j⁻¹Z)^{≥2}` for a closed `Z` in the image of an open immersion `j`. -/
private theorem preimage_componentsOfCodimAtLeastTwo {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] {D : Set X} (hD : IsClosed D) (hDj : D ⊆ Set.range j) :
    j ⁻¹' componentsOfCodimAtLeastTwo D = componentsOfCodimAtLeastTwo (j ⁻¹' D) := by
  ext y
  simp only [componentsOfCodimAtLeastTwo, Set.mem_preimage, Set.mem_iUnion]
  constructor
  · rintro ⟨C, hC, hcod, hy⟩
    have hCf : C ⊆ Set.range j := hC.1.2.trans hDj
    have hpre := (mem_componentsOf_iff_preimage j.isOpenEmbedding
      (Aux.isClosed_of_mem_componentsOf hD hC) hCf).1 hC
    refine ⟨j ⁻¹' C, hpre, ?_, hy⟩
    rwa [← codimension_irreducibleClosure_preimage j hC.1.1 hpre.1.1 hCf]
  · rintro ⟨T, hT, hcod, hy⟩
    obtain ⟨C, hC, rfl⟩ := exists_mem_componentsOf_preimage_eq j hD hDj hT
    refine ⟨C, hC, ?_, hy⟩
    rwa [codimension_irreducibleClosure_preimage j hC.1.1 hT.1.1 (hC.1.2.trans hDj)]

/-! ### The `j`-th entry of the total transform, on supports -/

/-- The support of the `j`-th entry of the iterated total transform along a blow-up sequence,
computed from the support of the `j`-th entry of `E`: `T ↦ closure (π⁻¹ (T ∖ Z^{≥2}))`. -/
private def entS : {X : Scheme.{u}} → (B : ClosedBlowupSequence X) → Set X → Set B.target
  | _, .nil _, T => T
  | _, .cons Z B, T =>
      entS B (closure (blowUpToBase Z ⁻¹' (T \ componentsOfCodimAtLeastTwo (Z.support : Set _))))

private theorem componentsOfCodimAtLeastTwo_empty {X : Scheme.{u}} :
    componentsOfCodimAtLeastTwo (∅ : Set X) = ∅ := by
  ext x
  simp only [componentsOfCodimAtLeastTwo, Set.mem_iUnion, Set.mem_empty_iff_false, iff_false]
  rintro ⟨W, hW, -, -⟩
  obtain ⟨w, hw⟩ := hW.1.1.nonempty
  exact hW.1.2 hw

private theorem entStep_comap {X Y : Scheme.{u}} (g : Y ⟶ X) [IsIso g] (Z : X.IdealSheafData)
    (T : Set X) :
    closure (blowUpToBase (Z.comap g) ⁻¹' (g ⁻¹' T \
        componentsOfCodimAtLeastTwo ((Z.comap g).support : Set Y))) =
      canonicalLift g Z ⁻¹' closure (blowUpToBase Z ⁻¹'
        (T \ componentsOfCodimAtLeastTwo (Z.support : Set X))) := by
  have := Kollar.isIso_canonicalLift g Z
  have hc : ∀ A : Set X, blowUpToBase (Z.comap g) ⁻¹' (g ⁻¹' A) =
      canonicalLift g Z ⁻¹' (blowUpToBase Z ⁻¹' A) := fun A => by
    ext x
    simp only [Set.mem_preimage]
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, canonicalLift_comp_blowUpToBase]
  have hs : ((Z.comap g).support : Set Y) = g ⁻¹' (Z.support : Set X) := coe_support_comap g Z
  have hr : (Z.support : Set X) ⊆ Set.range g := by
    intro x _
    exact (inferInstance : Surjective g).surj x
  rw [hs, ← preimage_componentsOfCodimAtLeastTwo g (D := (Z.support : Set X)) Z.support.isClosed hr,
    ← Set.preimage_sdiff, hc,
    (canonicalLift g Z).isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
      (canonicalLift g Z).continuous]

/-- **Deleting empty blow-ups after an isomorphism** (Kollár 3.32): the end of
`B.pullbackReduced g` is isomorphic to that of `B`, compatibly with the supports of the entries
of the total transform and with the marked transforms. -/
private theorem pullbackReduced_iso : ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X)
    {Y : Scheme.{u}} (g : Y ⟶ X) [IsIso g],
    ∃ φ : (B.pullbackReduced g).target ⟶ B.target, IsIso φ ∧
      (∀ T : Set X, IsClosed T → entS (B.pullbackReduced g) (g ⁻¹' T) = φ ⁻¹' entS B T) ∧
      (∀ {k : Type u} [Field k] (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X) (E : OrderedDivisor X),
        B.IsOrderGeMarkedTripleSeq s a E →
          (B.pullbackReduced g).markedTransform ⟨a.I.comap g, a.m⟩ =
            ⟨(B.markedTransform a).I.comap φ, a.m⟩) := by
  intro X B
  induction B with
  | nil X => intro Y g hg; exact ⟨g, hg, fun T _ => rfl, fun s a E _ => rfl⟩
  | @cons X Z B ih =>
    intro Y g hg
    by_cases hZ : Z.comap g = ⊤
    · have hZt : Z = ⊤ := (Kollar.comap_eq_top_iff_of_isIso g Z).1 hZ
      have hc := ClosedBlowupSequence.isCartierOver_of_comap_eq_top g Z hZ
      have e : (ClosedBlowupSequence.cons Z B).pullbackReduced g =
          B.pullbackReduced (blowUpLift Z g hc) := by
        simp [ClosedBlowupSequence.pullbackReduced, hZ]
      have := Kollar.isIso_blowUpLift_of_eq_top hZt g hc
      obtain ⟨φ, hφ, hT, hM⟩ := ih (blowUpLift Z g hc)
      rw [e]
      refine ⟨φ, hφ, fun T hTc => ?_, fun s a E hB => ?_⟩
      · subst hZt
        have h1 : closure (blowUpToBase (⊤ : X.IdealSheafData) ⁻¹' (T \
            componentsOfCodimAtLeastTwo ((⊤ : X.IdealSheafData).support : Set X))) =
            blowUpToBase (⊤ : X.IdealSheafData) ⁻¹' T := by
          rw [Scheme.IdealSheafData.support_top]
          simp only [TopologicalSpace.Closeds.coe_bot]
          rw [componentsOfCodimAtLeastTwo_empty, Set.sdiff_empty]
          exact (hTc.preimage (blowUpToBase _).continuous).closure_eq
        have h2 : blowUpLift (⊤ : X.IdealSheafData) g hc ⁻¹'
            (blowUpToBase (⊤ : X.IdealSheafData) ⁻¹' T) = g ⁻¹' T := by
          ext y
          simp only [Set.mem_preimage]
          rw [← Scheme.Hom.comp_apply, blowUpLift_comp]
        have := hT (blowUpToBase (⊤ : X.IdealSheafData) ⁻¹' T)
          (hTc.preimage (blowUpToBase _).continuous)
        rw [h2] at this
        change entS (B.pullbackReduced (blowUpLift (⊤ : X.IdealSheafData) g hc)) (g ⁻¹' T) =
          φ ⁻¹' entS B (closure _)
        rw [h1]
        exact this
      · obtain ⟨hT0, hZs, hcod, -, hord, hB'⟩ := hB
        have hmul := MarkedIdeal.birationalTransform_mul_eq s hT0.2.1 Z hZs hcod a hord
        subst hZt
        have h1 : ∀ {W : Scheme.{u}} (n : ℕ), (⊤ : W.IdealSheafData) ^ n = ⊤ := fun n => by
          rw [← Scheme.IdealSheafData.one_eq_top, one_pow]
        have h2 : ∀ {W : Scheme.{u}} (J : W.IdealSheafData), J * ⊤ = J := fun J => by
          rw [← Scheme.IdealSheafData.one_eq_top, mul_one]
        rw [Scheme.IdealSheafData.comap_top, h1, h2] at hmul
        have h3 := hM (blowUpToBase (⊤ : X.IdealSheafData) ≫ s) (a.birationalTransform ⊤)
          (E.totalTransform ⊤) hB'
        have h4 : (⟨a.I.comap g, a.m⟩ : MarkedIdeal Y) =
            ⟨((a.birationalTransform (⊤ : X.IdealSheafData)).I).comap
              (blowUpLift (⊤ : X.IdealSheafData) g hc), a.m⟩ := by
          congr 1
          rw [hmul, ← Scheme.IdealSheafData.comap_comp, blowUpLift_comp]
        rw [h4]
        exact h3
    · have e : (ClosedBlowupSequence.cons Z B).pullbackReduced g =
          ClosedBlowupSequence.cons (Z.comap g) (B.pullbackReduced (canonicalLift g Z)) := by
        simp [ClosedBlowupSequence.pullbackReduced, hZ]
      have := Kollar.isIso_canonicalLift g Z
      obtain ⟨φ, hφ, hT, hM⟩ := ih (canonicalLift g Z)
      rw [e]
      refine ⟨φ, hφ, fun T hTc => ?_, fun s a E hB => ?_⟩
      · change entS (B.pullbackReduced (canonicalLift g Z)) (closure (blowUpToBase (Z.comap g) ⁻¹'
          (g ⁻¹' T \ componentsOfCodimAtLeastTwo ((Z.comap g).support : Set Y)))) =
          φ ⁻¹' entS B (closure (blowUpToBase Z ⁻¹' (T \
            componentsOfCodimAtLeastTwo (Z.support : Set X))))
        rw [entStep_comap g Z T]
        exact hT _ isClosed_closure
      · obtain ⟨hT0, hZs, hcod, -, hord, hB'⟩ := hB
        have hmul := MarkedIdeal.birationalTransform_mul_eq s hT0.2.1 Z hZs hcod a hord
        have ha : a.I.comap (blowUpToBase Z) ≤ Z.comap (blowUpToBase Z) ^ a.m := by
          rw [← hmul]; first | exact Ideal.mul_le_left | exact mul_le_of_le_one_left bot_le le_top
        have h3 := hM (blowUpToBase Z ≫ s) (a.birationalTransform Z) (E.totalTransform Z) hB'
        change (B.pullbackReduced (canonicalLift g Z)).markedTransform
          (MarkedIdeal.birationalTransform (Z.comap g) ⟨a.I.comap g, a.m⟩) = _
        rw [Kollar.birationalTransform_comap_eq_comap_canonicalLift g Z a ha]
        exact h3

private theorem entS_mono : ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X) {T T' : Set X},
    T ⊆ T' → entS B T ⊆ entS B T'
  | _, .nil _, _, _, h => h
  | _, .cons _ B, _, _, h =>
      entS_mono B (closure_mono (Set.preimage_mono (Set.sdiff_subset_sdiff_left h)))

private theorem length_orderedTotalTransform : ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X)
    (E : OrderedDivisor X), (B.orderedTotalTransform E).s = E.s + B.length
  | _, .nil _, E => rfl
  | _, .cons Z B, E => by
      change (B.orderedTotalTransform (E.totalTransform Z)).s = _
      rw [length_orderedTotalTransform B]
      change E.s + 1 + B.length = E.s + (B.length + 1)
      omega

private theorem support_orderedTotalTransform_entry : ∀ {X : Scheme.{u}}
    (B : ClosedBlowupSequence X) (E : OrderedDivisor X) (i : ℕ) (hi : i < E.s)
    (hi' : i < (B.orderedTotalTransform E).s),
    (((B.orderedTotalTransform E).E ⟨i, hi'⟩).support : Set _) =
      entS B ((E.E ⟨i, hi⟩).support : Set X)
  | _, .nil _, E, i, hi, hi' => rfl
  | _, .cons Z B, E, i, hi, hi' => by
      have hi'' : i < (E.totalTransform Z).s := by
        change i < E.s + 1; omega
      have := support_orderedTotalTransform_entry B (E.totalTransform Z) i hi'' hi'
      show (((B.orderedTotalTransform (E.totalTransform Z)).E ⟨i, hi'⟩).support : Set B.target) = _
      rw [this]
      have e : (E.totalTransform Z).E ⟨i, hi''⟩ = Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure (blowUpToBase Z ⁻¹' ((E.E ⟨i, hi⟩).support \
            componentsOfCodimAtLeastTwo (Z.support : Set _)))) := by
        change (E.totalTransform Z).E (Fin.castSucc ⟨i, hi⟩) = _
        simp only [OrderedDivisor.totalTransform, Fin.snoc_castSucc]
      rw [e]
      change entS B _ = entS B (closure _)
      rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure]

/-- The complement of an effective Cartier divisor is dense. -/
private theorem dense_compl_support_of_isEffectiveCartierDivisor {Y : Scheme.{u}}
    (D : Y.IdealSheafData) (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) :
    Dense (D.support.compl : Set Y) := by
  have : IsAffineHom (Scheme.Opens.ι D.support.compl) :=
    Stacks.Divisors.isAffineHom_compl_of_isEffectiveCartierDivisor D hD
  have : IsSchemeTheoreticallyDominant (Scheme.Opens.ι D.support.compl) :=
    (Scheme.Opens.isSchemeTheoreticallyDense_iff_isSchemeTheoreticallyDominant
      D.support.compl).mp
      (Stacks.Divisors.isSchemeTheoreticallyDense_compl_of_isEffectiveCartierDivisor D hD)
  have hdense := (Scheme.Opens.ι D.support.compl).denseRange
  rwa [DenseRange, Scheme.Opens.range_ι] at hdense

/-- For a closed immersion `j : S ⟶ X` of a reduced scheme and a closed subscheme `Z ⊆ X`, the
canonical lift `B_{j⁻¹Z}S ⟶ B_ZX` has image the closure of `π⁻¹(j(S) ∖ Z)`. -/
private theorem range_canonicalLift_eq_closure {X S : Scheme.{u}} (j : S ⟶ X)
    [IsClosedImmersion j] [IsReduced S] (Z : X.IdealSheafData) :
    Set.range (canonicalLift j Z) =
      closure (blowUpToBase Z ⁻¹' (Set.range j \ (Z.support : Set X))) := by
  set f := canonicalLift j Z with hf
  set T : Set (blowUp Z) := blowUpToBase Z ⁻¹' (Set.range j \ (Z.support : Set X)) with hT
  have hsq : ∀ v, blowUpToBase Z (f v) = j (blowUpToBase (Z.comap j) v) := fun v ↦ by
    rw [← Scheme.Hom.comp_apply, hf, canonicalLift_comp_blowUpToBase, Scheme.Hom.comp_apply]
  have : IsReduced (blowUp (Z.comap j)) := isReduced_blowUp (Z.comap j)
  set V : Set (blowUp (Z.comap j)) :=
    blowUpToBase (Z.comap j) ⁻¹' ((Z.comap j).support : Set S)ᶜ with hV
  have hVdense : closure V = Set.univ := by
    have h := dense_compl_support_of_isEffectiveCartierDivisor
      ((Z.comap j).comap (blowUpToBase (Z.comap j)))
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal (Z.comap j))
    have hV' : (((Z.comap j).comap (blowUpToBase (Z.comap j))).support.compl :
        Set (blowUp (Z.comap j))) = V := by
      ext v
      simp [hV, Scheme.IdealSheafData.support_comap]
    rw [← hV']
    exact h.closure_eq
  have himage : f '' V = T := by
    ext y
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨⟨_, (hsq v).symm⟩, ?_⟩
      rw [hsq v]
      simpa [hV] using hv
    · rintro ⟨⟨s, hs⟩, hyZ⟩
      have hs' : s ∉ ((Z.comap j).support : Set S) := by
        simpa [hs] using hyZ
      obtain ⟨v, hv⟩ := exists_blowUpToBase_eq_of_notMem_support (Z.comap j) hs'
      refine ⟨v, by simpa [hV, hv] using hs', ?_⟩
      have hfv : blowUpToBase Z (f v) = blowUpToBase Z y := by rw [hsq v, hv, hs]
      exact blowUpToBase_injective_of_notMem_support Z (by rwa [hfv]) hfv
  apply subset_antisymm
  · rw [← Set.image_univ, ← hVdense, ← himage]
    exact image_closure_subset_closure_image f.continuous
  · rw [← himage]
    exact closure_minimal (Set.image_subset_range _ _) f.isClosedEmbedding.isClosed_range

/-- Let `H` be a closed subset of pure codimension one of a noetherian scheme and `Z ⊆ H` a closed
subset no irreducible component of which is an irreducible component of `H`. Then every
irreducible component of `Z` has codimension at least two. -/
private theorem two_le_codimension_of_mem_componentsOf {X : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace X]
    {H Z : TopologicalSpace.Closeds X} (hH1 : MMP.Mori.IsPureCodimOne H) (hZH : (Z : Set X) ⊆ H)
    (hcomp : ∀ W ∈ componentsOf (Z : Set X), W ∉ componentsOf (H : Set X)) {W : Set X}
    (hW : W ∈ componentsOf (Z : Set X)) : 2 ≤ codimension (irreducibleClosure hW.1.1) := by
  classical
  have hWc : IsClosed W := Aux.isClosed_of_mem_componentsOf Z.isClosed hW
  obtain ⟨hfin, hcov⟩ := Aux.finite_and_cover_componentsOf H.isClosed
  obtain ⟨H', hH'mem, hWH'⟩ : ∃ H' ∈ componentsOf (H : Set X), W ⊆ H' := by
    obtain ⟨z, hz, hWz⟩ := isIrreducible_iff_sUnion_isClosed.mp hW.1.1 hfin.toFinset
      (fun z hz => Aux.isClosed_of_mem_componentsOf H.isClosed (hfin.mem_toFinset.mp hz))
      (by rw [hfin.coe_toFinset]; exact hW.1.2.trans (hZH.trans hcov))
    exact ⟨z, hfin.mem_toFinset.mp hz, hWz⟩
  have hne : W ≠ H' := fun h => hcomp W hW (h ▸ hH'mem)
  have hH'c : IsClosed H' := Aux.isClosed_of_mem_componentsOf H.isClosed hH'mem
  let C' : TopologicalSpace.IrreducibleCloseds X := ⟨H', hH'mem.1.1, hH'c⟩
  have hC' : codimension C' = 1 :=
    hH1 C' ⟨hH'mem.1.2, fun W' hW' hle => hH'mem.2 ⟨W'.isIrreducible, hW'⟩ hle⟩
  have hlt : irreducibleClosure hW.1.1 < C' := by
    refine lt_of_le_of_ne ?_ ?_
    · show closure W ⊆ H'
      rw [hWc.closure_eq]
      exact hWH'
    · intro h
      apply hne
      have := congrArg (fun C : TopologicalSpace.IrreducibleCloseds X => (C : Set X)) h
      simpa [irreducibleClosure, hWc.closure_eq, C'] using this
  have := Order.coheight_add_one_le hlt
  rw [codimension_eq_coheight] at hC' ⊢
  rw [hC'] at this
  exact le_trans (by norm_num) this

/-- Every centre of the sequence has components of positive codimension. -/
private def HasCentresOfPositiveCodim : {S : Scheme.{u}} → ClosedBlowupSequence S → Prop
  | _, .nil _ => True
  | S, .cons Z B =>
    HasComponentsOfPositiveCodim (Z.support : Set S) ∧ HasCentresOfPositiveCodim B

private theorem hasCentresOfPositiveCodim_of_isOrderGe {k : Type u} [Field k] : ∀ {S : Scheme.{u}}
    (B : ClosedBlowupSequence S) (s : S ⟶ Spec (.of k)) (a : MarkedIdeal S) (E : OrderedDivisor S),
    B.IsOrderGeMarkedTripleSeq s a E → HasCentresOfPositiveCodim B
  | _, .nil _, _, _, _, _ => by simp only [HasCentresOfPositiveCodim]
  | _, .cons Z B, s, a, E, h =>
    ⟨h.2.2.1, hasCentresOfPositiveCodim_of_isOrderGe B _ _ _ h.2.2.2.2.2⟩

/-- If `f '' s` is preirreducible for an inducing map `f` then so is `s`. -/
private theorem isPreirreducible_of_isInducing_image {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {f : β → α} (hf : Topology.IsInducing f) {s : Set β}
    (h : IsPreirreducible (f '' s)) : IsPreirreducible s := by
  intro u v hu hv ⟨a, ha, hau⟩ ⟨b, hb, hbv⟩
  obtain ⟨u', hu', rfl⟩ := hf.isOpen_iff.1 hu
  obtain ⟨v', hv', rfl⟩ := hf.isOpen_iff.1 hv
  obtain ⟨_, ⟨c, hc, rfl⟩, hcu, hcv⟩ := h u' v' hu' hv' ⟨f a, ⟨a, ha, rfl⟩, hau⟩
    ⟨f b, ⟨b, hb, rfl⟩, hbv⟩
  exact ⟨c, hc, hcu, hcv⟩

/-- The components of a centre which is the push-forward of a centre of positive codimension in a
closed subscheme `S' ↪ X` lying in a hypersurface with support `j(S')` all have codimension
`≥ 2`. -/
private theorem two_le_codim_pushforward {X S' : Scheme.{u}} [NoetherianSpace X] (j : S' ⟶ X)
    [IsClosedImmersion j] (ZX : X.IdealSheafData) (hmap : ZX = (ZX.comap j).map j)
    (H : X.IdealSheafData) (hH : (H.support : Set X) = Set.range j)
    (hH1 : MMP.Mori.IsPureCodimOne H.support)
    (hpos : HasComponentsOfPositiveCodim ((ZX.comap j).support : Set S')) :
    ∀ W (hW : W ∈ componentsOf (ZX.support : Set X)),
      2 ≤ codimension (irreducibleClosure hW.1.1) := by
  have hZr : (ZX.support : Set X) ⊆ Set.range j := by
    have hle0 : j.ker ≤ (ZX.comap j).map j := by
      rw [← Scheme.IdealSheafData.map_bot]
      exact Scheme.IdealSheafData.map_mono j bot_le
    have hle : j.ker ≤ ZX := hle0.trans hmap.symm.le
    have h : ((ZX).support : Set X) ⊆ (j.ker.support : Set X) :=
      Scheme.IdealSheafData.support_antitone hle
    rwa [Scheme.Hom.support_ker, j.isClosedEmbedding.isClosed_range.closure_eq] at h
  have hemb := j.isClosedEmbedding
  intro W hW
  refine two_le_codimension_of_mem_componentsOf hH1 (by rwa [hH]) ?_ hW
  intro W hW hWH
  change W ∈ componentsOf (H.support : Set X) at hWH
  rw [hH] at hWH
  have hWc : IsClosed W := Aux.isClosed_of_mem_componentsOf ZX.support.isClosed hW
  have hWr : W ⊆ Set.range j := hW.1.2.trans hZr
  set W' : Set S' := j ⁻¹' W with hW'
  have himg : j '' W' = W := Set.image_preimage_eq_of_subset hWr
  have hW'irr : IsIrreducible W' := by
    refine ⟨?_, isPreirreducible_of_isInducing_image hemb.isInducing (by rw [himg]; exact hW.1.1.2)⟩
    obtain ⟨w, hw⟩ := hW.1.1.nonempty
    obtain ⟨u, rfl⟩ := hWr hw
    exact ⟨u, hw⟩
  have hmaxX : ∀ C : Set S', IsIrreducible C → W' ⊆ C → C ⊆ W' := by
    intro C hC hle
    have h1 : IsIrreducible (j '' C) := hC.image j hemb.continuous.continuousOn
    have h2 : W ⊆ j '' C := by rw [← himg]; exact Set.image_mono hle
    have h3 := hWH.2 ⟨h1, Set.image_subset_range _ _⟩ h2
    intro c hc
    exact h3 ⟨c, hc, rfl⟩
  have hcomp : W' ∈ componentsOf ((ZX.comap j).support : Set S') := by
    refine ⟨⟨hW'irr, ?_⟩, ?_⟩
    · rw [Scheme.IdealSheafData.support_comap]
      exact Set.preimage_mono hW.1.2
    · rintro V ⟨hV, hVs⟩ hle
      exact hmaxX V hV hle
  have h1 := hpos W' hcomp
  have hmax : IsMax (irreducibleClosure hcomp.1.1) := by
    intro C hC
    have hCs : closure W' ⊆ (C : Set S') := hC
    have h2 : (C : Set S') ⊆ W' := hmaxX C C.isIrreducible (subset_closure.trans hCs)
    show (C : Set S') ⊆ closure W'
    exact h2.trans subset_closure
  have h0 : codimension (irreducibleClosure hcomp.1.1) = 0 := Order.coheight_eq_zero.2 hmax
  rw [h0] at h1
  exact absurd h1 (by decide)

/-- If every irreducible component of `Z` has codimension at least two, then the union of the
components of codimension at least two is `Z` itself. -/
private theorem componentsOfCodimAtLeastTwo_eq_self {X : Scheme.{u}} {Z : Set X}
    (h2 : ∀ W (hW : W ∈ componentsOf Z), 2 ≤ codimension (irreducibleClosure hW.1.1)) :
    componentsOfCodimAtLeastTwo Z = Z := by
  ext x
  rw [mem_componentsOfCodimAtLeastTwo]
  refine ⟨fun ⟨_, hW, _, hx⟩ => hW.1.2 hx, fun hx => ?_⟩
  obtain ⟨W, hW, hxW⟩ := exists_mem_componentsOf hx
  exact ⟨W, hW, h2 W hW, hxW⟩

private theorem support_totalTransform_castSucc {X : Scheme.{u}} (E : OrderedDivisor X)
    (Z : X.IdealSheafData) (i : Fin E.s) :
    (((E.totalTransform Z).E (Fin.castSucc i)).support : Set _) =
      closure (blowUpToBase Z ⁻¹' ((E.E i).support \
        componentsOfCodimAtLeastTwo (Z.support : Set X))) := by
  have e : (E.totalTransform Z).E (Fin.castSucc i) = Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure (blowUpToBase Z ⁻¹' ((E.E i).support \
        componentsOfCodimAtLeastTwo (Z.support : Set _)))) := by
    simp only [OrderedDivisor.totalTransform, Fin.snoc_castSucc]
  rw [e, Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure]

private theorem noetherianSpace_of_isTriple {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {I : X.IdealSheafData} {E : OrderedDivisor X}
    (h : IsTriple s I E) : NoetherianSpace X := by
  obtain ⟨-, -, hlft, hqc, -⟩ := h
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  have : IsNoetherian X := {}
  infer_instance

/-- **The strict transform of `S'` in `X_i`** (Kollár 3.102, "the sequence on `S`"): along a
push-forward `B` of a sequence `BS` with centres of positive codimension in a reduced closed
subscheme `j : S' ↪ X` which is the support of the entry `E^i`, the supports of the entries
`E^i_r` are the images of the `S'_r`. -/
private theorem entS_eq_range : ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X)
    {S' : Scheme.{u}} (j : S' ⟶ X) [IsClosedImmersion j] [IsReduced S']
    (BS : ClosedBlowupSequence S') {k : Type u} [Field k] (s : X ⟶ Spec (.of k))
    (I : X.IdealSheafData) (E : OrderedDivisor X) (m : ℕ) (i : Fin E.s),
    ClosedBlowupSequence.IsPushforward j BS B → HasCentresOfPositiveCodim BS →
    B.IsOrderMTripleSeq s I E m →
    ((E.E i).support : Set X) = Set.range j →
    entS B (Set.range j) = Set.range (B.pullbackHom j) := by
  intro X B
  induction B with
  | nil X =>
    intro S' j _ _ BS k _ s I E m i hP hpos hB hE
    rfl
  | @cons X ZX BX ih =>
    intro S' j _ _ BS k _ s I E m i hP hpos hB hE
    cases BS with
    | nil => exact hP.elim
    | cons ZS BS' =>
      obtain ⟨h, hmap, hP'⟩ := hP
      subst h
      obtain ⟨hT, hZsm, hcodim, hsnc, hord, hB'⟩ := hB
      have := noetherianSpace_of_isTriple hT
      have hK1 := two_le_codim_pushforward j ZX hmap (E.E i) hE (hT.2.2.2.2.2.2.2.1 i).2.1
        hpos.1
      have hcomp2 := componentsOfCodimAtLeastTwo_eq_self hK1
      have hrange := range_canonicalLift_eq_closure j ZX
      have : IsReduced (blowUp (ZX.comap j)) := isReduced_blowUp _
      rw [eqToHom_refl, Category.id_comp] at hP'
      have hE' : (((E.totalTransform ZX).E (Fin.castSucc i)).support : Set _) =
          Set.range (canonicalLift j ZX) := by
        rw [support_totalTransform_castSucc, hrange, hE, hcomp2]
      have key := ih (canonicalLift j ZX) BS' (blowUpToBase ZX ≫ s) _ (E.totalTransform ZX) m
        (Fin.castSucc i) hP' hpos.2 hB' hE'
      change entS BX (closure (blowUpToBase ZX ⁻¹' (Set.range j \
        componentsOfCodimAtLeastTwo (ZX.support : Set X)))) = _
      rw [hcomp2, ← hrange]
      exact key

section CoreHelpers

open IsLocalRing

private theorem truncate_eq_self : ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X) {i : ℕ},
    B.length ≤ i → B.truncate i = B
  | _, .nil _, _, _ => rfl
  | _, .cons Z B, 0, h => by simp [ClosedBlowupSequence.length] at h
  | _, .cons Z B, i + 1, h => congrArg (ClosedBlowupSequence.cons Z)
      (truncate_eq_self B (by simp [ClosedBlowupSequence.length] at h; omega))

private theorem num_formalTransformAux : ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X)
    (N D : X.IdealSheafData) (μ : ℕ), (B.formalTransformAux N D μ).num = N.comap B.toBase
  | _, .nil _, N, D, μ => by
      change N = N.comap (𝟙 _)
      rw [Scheme.IdealSheafData.comap_id]
  | _, .cons Z B, N, D, μ => by
      change (B.formalTransformAux _ _ μ).num = N.comap (B.toBase ≫ blowUpToBase Z)
      rw [num_formalTransformAux B, Scheme.IdealSheafData.comap_comp]

private theorem pullbackHom_comp_toBase : ∀ {X Y : Scheme.{u}} (B : ClosedBlowupSequence X)
    (h : Y ⟶ X), B.pullbackHom h ≫ B.toBase = (B.pullback h).toBase ≫ h
  | _, _, .nil _, h => by
      change h ≫ 𝟙 _ = 𝟙 _ ≫ h
      simp
  | _, _, .cons Z B, h => by
      change B.pullbackHom (canonicalLift h Z) ≫ (B.toBase ≫ blowUpToBase Z) =
        (B.pullback (canonicalLift h Z)).toBase ≫ blowUpToBase (Z.comap h) ≫ h
      rw [← Category.assoc, pullbackHom_comp_toBase B, Category.assoc,
        canonicalLift_comp_blowUpToBase]

private theorem isNonzeroAtGenericPoints_comap_toBase : ∀ {X : Scheme.{u}}
    (B : ClosedBlowupSequence X) {K : X.IdealSheafData}, IsNonzeroAtGenericPoints K →
      IsNonzeroAtGenericPoints (K.comap B.toBase)
  | _, .nil _, K, h => by
      change IsNonzeroAtGenericPoints (K.comap (𝟙 _))
      rwa [Scheme.IdealSheafData.comap_id]
  | _, .cons Z B, K, h => by
      have := isNonzeroAtGenericPoints_comap_toBase B
        (isNonzeroAtGenericPoints_comap_blowUpToBase Z h)
      change IsNonzeroAtGenericPoints (K.comap (B.toBase ≫ blowUpToBase Z))
      rwa [Scheme.IdealSheafData.comap_comp]

/-- An ideal sheaf nonzero at the generic points has nonzero stalks everywhere. -/
private theorem stalk_ne_bot {X : Scheme.{u}} {I : X.IdealSheafData}
    (hI : IsNonzeroAtGenericPoints I) (x : X) : IdealSheafData.stalk I x ≠ ⊥ := by
  obtain ⟨Z, hZ, hxZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {x}
    isIrreducible_singleton
  have hZc : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
  have hgen := hZ.1.isGenericPoint_genericPoint_closure
  rw [hZc.closure_eq] at hgen
  have hsp : hZ.1.genericPoint ⤳ x := by
    rw [specializes_iff_mem_closure, hgen.def]; exact hxZ rfl
  intro hb
  refine hI hZ.1.genericPoint (by rwa [hgen.def]) ?_
  rw [Stacks.Chow.idealStalk_eq_map_stalkSpecializes I hsp, hb, Ideal.map_bot]

variable {k : Type u} [Field k]

private theorem exists_mem_notMem_of_idealOrder_eq {R : Type*} [CommRing R] [IsLocalRing R]
    {A : Ideal R} {a : ℕ} (ha : (a : ℕ∞) = idealOrder A) :
    ∃ φ ∈ A, φ ∈ maximalIdeal R ^ a ∧ φ ∉ maximalIdeal R ^ (a + 1) := by
  have h1 : A ≤ maximalIdeal R ^ a := (natCast_le_idealOrder_iff' A a).1 ha.le
  have h2 : ¬ A ≤ maximalIdeal R ^ (a + 1) := fun h => by
    have := (natCast_le_idealOrder_iff' A (a + 1)).2 h
    rw [← ha] at this
    norm_cast at this
    omega
  obtain ⟨φ, hφ, hφ'⟩ := SetLike.not_le_iff_exists.mp h2
  exact ⟨φ, hφ, h1 hφ, hφ'⟩

/-- In a regular local ring, `ord (A * B) ≤ ord A + ord B`. -/
private theorem idealOrder_mul_le {S : Type*} [CommRing S] [IsRegularLocalRing S]
    (A B : Ideal S) : idealOrder (A * B) ≤ idealOrder A + idealOrder B := by
  rcases eq_or_ne (idealOrder A) ⊤ with hA | hA
  · simp [hA]
  rcases eq_or_ne (idealOrder B) ⊤ with hB | hB
  · simp [hB]
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hA
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp hB
  obtain ⟨φ, hφA, hφ1, hφ2⟩ := exists_mem_notMem_of_idealOrder_eq ha
  obtain ⟨ψ, hψB, hψ1, hψ2⟩ := exists_mem_notMem_of_idealOrder_eq hb
  have hn : ¬ A * B ≤ maximalIdeal S ^ (a + b + 1) := fun h =>
    MMP.Flips.mul_notMem_maximalIdeal_pow_add_succ hφ1 hφ2 hψ1 hψ2 (h (Ideal.mul_mem_mul hφA hψB))
  rw [← ha, ← hb]
  by_contra hlt
  apply hn
  rw [← natCast_le_idealOrder_iff']
  have : ((a + b : ℕ) : ℕ∞) < idealOrder (A * B) := by
    push_cast
    exact lt_of_not_ge hlt
  exact_mod_cast Order.add_one_le_of_lt this

/-- In a noetherian local ring a nonzero ideal has finite order. -/
private theorem idealOrder_ne_top {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {A : Ideal R} (hA : A ≠ ⊥) : idealOrder A ≠ ⊤ := by
  intro h
  refine hA (eq_bot_iff.2 ?_)
  rw [← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal R) (maximalIdeal.isMaximal R).ne_top]
  exact le_iInf fun n => (natCast_le_idealOrder_iff' A n).1 (h ▸ le_top)

/-! ### Orders of ideal sheaves -/

/-- In a regular local ring, a factor of finite order cancels on orders: if `A * D ≤ K * D` then
`ord A ≥ ord K`. -/
private theorem le_idealOrder_of_mul_le_mul {S : Type*} [CommRing S] [IsRegularLocalRing S]
    {A D K : Ideal S} {n : ℕ} (hK : (n : ℕ∞) ≤ idealOrder K) (hD : idealOrder D ≠ ⊤)
    (h : A * D ≤ K * D) : (n : ℕ∞) ≤ idealOrder A := by
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp hD
  have hKD : ((n + d : ℕ) : ℕ∞) ≤ idealOrder (K * D) := by
    rw [natCast_le_idealOrder_iff', pow_add]
    exact Ideal.mul_mono ((natCast_le_idealOrder_iff' _ _).1 hK)
      ((natCast_le_idealOrder_iff' _ _).1 hd.le)
  have := (hKD.trans (MMP.Resolution.Kollar.idealOrder_antitone h)).trans (idealOrder_mul_le A D)
  rw [← hd, Nat.cast_add] at this
  exact (ENat.add_le_add_iff_right (ENat.natCast_ne_top d)).1 this

private theorem isOrderGeMarkedTripleSeq_truncate {X : Scheme.{u}} (B : ClosedBlowupSequence X) :
    ∀ {s : X ⟶ Spec (.of k)} {a : MarkedIdeal X} {E : OrderedDivisor X},
      B.IsOrderGeMarkedTripleSeq s a E → ∀ i, (B.truncate i).IsOrderGeMarkedTripleSeq s a E := by
  induction B with
  | nil X => intro s a E h i; exact h
  | cons Z B ih =>
    intro s a E h i
    cases i with
    | zero => exact h.1
    | succ i => exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, ih h.2.2.2.2.2 i⟩

/-- The last triple `(X_r, I_r, E_r)` of a sequence of order `≥ m` is a triple. -/
private theorem isTriple_markedTransform {X : Scheme.{u}} (B : ClosedBlowupSequence X) :
    ∀ {s : X ⟶ Spec (.of k)} {a : MarkedIdeal X} {E : OrderedDivisor X},
      B.IsOrderGeMarkedTripleSeq s a E →
        IsTriple (B.toBase ≫ s) (B.markedTransform a).I (B.orderedTotalTransform E) := by
  induction B with
  | nil X =>
    intro s a E h
    change IsTriple (𝟙 X ≫ s) a.I E
    rw [Category.id_comp]
    exact h
  | cons Z B ih =>
    intro s a E h
    change IsTriple ((B.toBase ≫ blowUpToBase Z) ≫ s) _ _
    rw [Category.assoc]
    exact ih h.2.2.2.2.2

/-- Along a sequence of order `≥ μ` for `(J, μ)`, `J_r · D_r = N_r` for the iterated formal
transform `N_r · D_r⁻¹` of `N · D⁻¹ = J`. -/
private theorem markedTransform_mul_den {X : Scheme.{u}} (B : ClosedBlowupSequence X) :
    ∀ {s : X ⟶ Spec (.of k)} {b : MarkedIdeal X} {E : OrderedDivisor X} (N D : X.IdealSheafData),
      B.IsOrderGeMarkedTripleSeq s b E → b.I * D = N →
        (B.markedTransform b).I * (B.formalTransformAux N D b.m).den =
          (B.formalTransformAux N D b.m).num := by
  induction B with
  | nil X => intro s b E N D _ h; exact h
  | cons Z B ih =>
    intro s b E N D h hND
    obtain ⟨hT, hZ, hcod, -, hord, hB⟩ := h
    refine ih (N.comap (blowUpToBase Z)) (D.comap (blowUpToBase Z) * Z.comap (blowUpToBase Z) ^ b.m)
      hB ?_
    rw [← hND, Stacks.IdealSheaf.comap_mul,
      ← MarkedIdeal.birationalTransform_mul_eq s hT.2.1 Z hZ hcod b hord]
    change _ * (_ * _) = _
    ring

private theorem multAt_le_multAt_comap {Y X : Scheme.{u}} (f : Y ⟶ X) (K : X.IdealSheafData)
    (y : Y) : multAt K (f y) ≤ multAt (K.comap f) y := by
  unfold multAt
  rw [IdealSheafData.stalk_comap]
  unfold idealOrder
  refine iSup₂_le fun j hj => le_iSup₂_of_le j ?_ le_rfl
  set φ := (f.stalkMap y).hom
  calc (IdealSheafData.stalk K (f y)).map φ ≤ (maximalIdeal _ ^ j).map φ := Ideal.map_mono hj
    _ = ((maximalIdeal _).map φ) ^ j := Ideal.map_pow _ _ _
    _ ≤ maximalIdeal _ ^ j := by
      refine Ideal.pow_right_mono ?_ j
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      exact fun h => ha (isUnit_of_map_unit φ a h)

end CoreHelpers

/-- The first ideal of a smooth blow-up sequence of order `≥ m` is nonzero at the generic
points. -/
private theorem isNonzeroAtGenericPoints_of_isOrderGe {k : Type u} [Field k] {X : Scheme.{u}}
    {B : ClosedBlowupSequence X} {s : X ⟶ Spec (.of k)} {a : MarkedIdeal X} {E : OrderedDivisor X}
    (h : B.IsOrderGeMarkedTripleSeq s a E) : IsNonzeroAtGenericPoints a.I := by
  cases B with
  | nil => exact h.2.2.2.2.2.1
  | cons Z B => exact h.1.2.2.2.2.2.1

/-- **The order argument of Kollár 3.102.** -/
private theorem core_order {X0 : Scheme.{u}} {k : Type u} [Field k] (S : X0.IdealSheafData)
    (P : ClosedBlowupSequence X0) (BS : ClosedBlowupSequence S.subscheme)
    (s0 : X0 ⟶ Spec (.of k)) (W₀ : X0.IdealSheafData) (μ : ℕ) (E0 : OrderedDivisor X0)
    {sS : S.subscheme ⟶ Spec (.of k)} {ES : OrderedDivisor S.subscheme}
    (hP : P.IsOrderGeMarkedTripleSeq s0 ⟨W₀, μ⟩ E0)
    (hBS : BS.IsOrderGeMarkedTripleSeq sS ⟨W₀.comap S.subschemeι, μ⟩ ES)
    (hlast : ∀ y : BS.target, multAt (BS.markedTransform ⟨W₀.comap S.subschemeι, μ⟩).I y < μ)
    (hres : ∀ i : ℕ, (P.truncate i).restrict S = BS.truncate i ∧
        (P.formalTransform W₀ μ i).num.comap ((P.truncate i).restrictHom S) =
          (((P.truncate i).restrict S).markedTransform ⟨W₀.comap S.subschemeι, μ⟩).I *
            (P.formalTransform W₀ μ i).den.comap ((P.truncate i).restrictHom S))
    (x : P.target) (hxr : x ∈ Set.range (P.restrictHom S))
    (hx : μ ≤ multAt (P.markedTransform ⟨W₀, μ⟩).I x) : False := by
  have hPi : P.truncate (P.length + BS.length) = P := truncate_eq_self P (Nat.le_add_right _ _)
  have hBi : BS.truncate (P.length + BS.length) = BS := truncate_eq_self BS (Nat.le_add_left _ _)
  obtain ⟨hres1, hres2⟩ := hres (P.length + BS.length)
  have key : ∀ Q : ClosedBlowupSequence X0, Q = P.truncate (P.length + BS.length) →
      ∀ x : Q.target, x ∈ Set.range (Q.restrictHom S) →
        μ ≤ multAt (Q.markedTransform ⟨W₀, μ⟩).I x → False := by
    intro Q hQ
    subst hQ
    intro x hxr hx
    obtain ⟨y, hy⟩ := hxr
    have hR : (P.truncate (P.length + BS.length)).restrict S = BS := hres1.trans hBi
    have hlast' : ∀ y : ((P.truncate (P.length + BS.length)).restrict S).target,
        multAt (((P.truncate (P.length + BS.length)).restrict S).markedTransform
          ⟨W₀.comap S.subschemeι, μ⟩).I y < μ := by
      rwa [hR]
    have hreg : ∀ y : ((P.truncate (P.length + BS.length)).restrict S).target,
        IsRegularLocalRing (((P.truncate (P.length + BS.length)).restrict S).target.presheaf.stalk
          y) := by
      rw [hR]
      exact isRegularLocalRing_stalk_of_isSmoothScheme (isTriple_markedTransform BS hBS).2.1
    have hNz : ∀ y : ((P.truncate (P.length + BS.length)).restrict S).target,
        IdealSheafData.stalk ((W₀.comap S.subschemeι).comap
          ((P.truncate (P.length + BS.length)).restrict S).toBase) y ≠ ⊥ := by
      rw [hR]
      exact fun y => stalk_ne_bot (isNonzeroAtGenericPoints_comap_toBase BS
        (isNonzeroAtGenericPoints_of_isOrderGe hBS)) y
    have hQge : (P.truncate (P.length + BS.length)).IsOrderGeMarkedTripleSeq s0 ⟨W₀, μ⟩ E0 :=
      isOrderGeMarkedTripleSeq_truncate P hP _
    have hnum : (P.formalTransform W₀ μ (P.length + BS.length)).num =
        W₀.comap (P.truncate (P.length + BS.length)).toBase :=
      num_formalTransformAux _ W₀ ⊤ μ
    have hden_eq : ((P.truncate (P.length + BS.length)).markedTransform ⟨W₀, μ⟩).I *
        (P.formalTransform W₀ μ (P.length + BS.length)).den =
        (P.formalTransform W₀ μ (P.length + BS.length)).num :=
      markedTransform_mul_den _ (b := ⟨W₀, μ⟩) W₀ ⊤ hQge
        (by rw [← Scheme.IdealSheafData.one_eq_top, mul_one])
    have hN : (P.formalTransform W₀ μ (P.length + BS.length)).num.comap
        ((P.truncate (P.length + BS.length)).restrictHom S) =
        (W₀.comap S.subschemeι).comap ((P.truncate (P.length + BS.length)).restrict S).toBase := by
      rw [hnum, ← Scheme.IdealSheafData.comap_comp,
        show (P.truncate (P.length + BS.length)).restrictHom S ≫
            (P.truncate (P.length + BS.length)).toBase =
          ((P.truncate (P.length + BS.length)).restrict S).toBase ≫ S.subschemeι from
          pullbackHom_comp_toBase _ S.subschemeι, Scheme.IdealSheafData.comap_comp]
    have hEq : ((P.truncate (P.length + BS.length)).markedTransform ⟨W₀, μ⟩).I.comap
          ((P.truncate (P.length + BS.length)).restrictHom S) *
        (P.formalTransform W₀ μ (P.length + BS.length)).den.comap
          ((P.truncate (P.length + BS.length)).restrictHom S) =
        (((P.truncate (P.length + BS.length)).restrict S).markedTransform
          ⟨W₀.comap S.subschemeι, μ⟩).I *
        (P.formalTransform W₀ μ (P.length + BS.length)).den.comap
          ((P.truncate (P.length + BS.length)).restrictHom S) := by
      rw [← Stacks.IdealSheaf.comap_mul, hden_eq, hres2]
    have hD'ne : IdealSheafData.stalk ((P.formalTransform W₀ μ (P.length + BS.length)).den.comap
          ((P.truncate (P.length + BS.length)).restrictHom S)) y ≠ ⊥ := by
      intro hb
      apply hNz y
      rw [← hN, hres2, IdealSheafData.stalk_mul, hb, Ideal.mul_bot]
    have := hreg y
    have hord := idealOrder_ne_top hD'ne
    have hge : (μ : ℕ∞) ≤ idealOrder (IdealSheafData.stalk
        (((P.truncate (P.length + BS.length)).markedTransform ⟨W₀, μ⟩).I.comap
          ((P.truncate (P.length + BS.length)).restrictHom S)) y) := by
      have h1 := multAt_le_multAt_comap ((P.truncate (P.length + BS.length)).restrictHom S)
        ((P.truncate (P.length + BS.length)).markedTransform ⟨W₀, μ⟩).I y
      rw [hy] at h1
      exact hx.trans h1
    have hle := le_idealOrder_of_mul_le_mul (A := IdealSheafData.stalk
        (((P.truncate (P.length + BS.length)).restrict S).markedTransform
          ⟨W₀.comap S.subschemeι, μ⟩).I y) hge hord (le_of_eq (by
        rw [← IdealSheafData.stalk_mul, ← IdealSheafData.stalk_mul, hEq]))
    have h2 := hlast' y
    unfold multAt at h2
    exact absurd h2 (not_lt.2 hle)
  exact key P hPi.symm x hxr hx

section Misc

private theorem pow_le_maximalCoefficientIdeal {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (I : X.IdealSheafData) (s : ℕ) :
    I ^ s ≤ maximalCoefficientIdeal sX I (((maxOrder I).toNat * s : ℕ) : ℤ) := by
  unfold maximalCoefficientIdeal
  set c : Fin ((maxOrder I).toNat + 1) → ℕ := Pi.single 0 s with hc
  have hw : ((maxOrder I).toNat * s : ℕ) ≤ (coefficientWeight _ c : ℤ) := by
    unfold coefficientWeight
    rw [Finset.sum_eq_single (0 : Fin ((maxOrder I).toNat + 1))]
    · simp [hc]
    · intro b _ hb
      simp [hc, hb]
    · simp
  refine le_trans (le_of_eq ?_) (le_iSup₂_of_le c hw le_rfl)
  rw [Finset.prod_eq_single (0 : Fin ((maxOrder I).toNat + 1))]
  · simp [hc, higherDerivativeIdeal_zero]
  · intro b _ hb
    simp [hc, hb]
  · simp

private theorem entS_empty : ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X),
    entS B (∅ : Set X) = ∅
  | _, .nil _ => rfl
  | _, .cons Z B => by
      change entS B (closure (blowUpToBase Z ⁻¹' ((∅ : Set _) \ _))) = ∅
      simp only [Set.empty_sdiff, Set.preimage_empty, closure_empty]
      exact entS_empty B

private theorem entS_cons {X : Scheme.{u}} (Z : X.IdealSheafData)
    (B : ClosedBlowupSequence (blowUp Z)) (T : Set X) :
    entS (ClosedBlowupSequence.cons Z B) T =
      entS B (closure (blowUpToBase Z ⁻¹' (T \ componentsOfCodimAtLeastTwo (Z.support : Set _)))) :=
  rfl

end Misc

private theorem componentsOfCodimAtLeastTwo_eq_empty_of_isPureCodimOne {X : Scheme.{u}}
    {H : Closeds X} (hH : MMP.Mori.IsPureCodimOne H) :
    componentsOfCodimAtLeastTwo (H : Set X) = ∅ := by
  ext x
  simp only [componentsOfCodimAtLeastTwo, Set.mem_iUnion, Set.mem_empty_iff_false, iff_false]
  rintro ⟨W, hW, h2, hx⟩
  have hWc : IsClosed W := Aux.isClosed_of_mem_componentsOf H.isClosed hW
  have h1 : codimension (irreducibleClosure hW.1.1) = 1 := by
    refine hH _ ⟨?_, fun W' hW' hle => ?_⟩
    · change closure W ⊆ H
      rw [hWc.closure_eq]; exact hW.1.2
    · have : (W' : Set X) ⊆ W := hW.2 ⟨W'.isIrreducible, hW'⟩ (by
        have : closure W ⊆ (W' : Set X) := hle
        rwa [hWc.closure_eq] at this)
      change (W' : Set X) ⊆ closure W
      rwa [hWc.closure_eq]
  rw [h1] at h2
  exact absurd h2 (by decide)

section CartierCentre

open IsLocalRing

/-- Let `S` be a set of components of a smooth divisor `D`, and `Z` the reduced ideal of their
union. At a point `x` of a component `W ∈ S`, the ideal of `Z` agrees with that of `D`: the
components of `D` are disjoint, so near `x` the union of `S` is all of `D`. -/
private theorem stalk_vanishingIdeal_sUnion_eq {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [QuasiCompact sX] (D : X.IdealSheafData)
    (hD : MMP.Mori.IsSmoothScheme (D.subschemeι ≫ sX)) {S : Set (Set X)}
    (hS : S ⊆ componentsOf (D.support : Set X)) {W : Set X} (hWS : W ∈ S) {x : X} (hxW : x ∈ W) :
    IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure (⋃₀ S))) x =
      IdealSheafData.stalk D x := by
  have := Aux.isReduced_subscheme_of_isSmoothScheme sX D hD
  have hU : IsClosed (⋃₀ S) := Aux.isClosed_sUnion_of_subset_componentsOf sX D S hS
  set R : Set X := ⋃₀ (componentsOf (D.support : Set X) \ S)
  have hR : IsClosed R := Aux.isClosed_sUnion_of_subset_componentsOf sX D _ Set.diff_subset
  have hxR : x ∉ R := by
    rintro ⟨W', hW', hxW'⟩
    exact hW'.2 (Aux.eq_of_mem_componentsOf_of_isSmoothScheme sX D hD hW'.1 (hS hWS) hxW' hxW ▸
      hWS)
  rw [Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme D D.support rfl]
  refine IdealSheafData.stalk_vanishingIdeal_congr (V := ⟨Rᶜ, hR.isOpen_compl⟩) hxR ?_
  ext z
  simp only [Closeds.coe_closure, hU.closure_eq, Set.mem_inter_iff, Opens.coe_mk,
    Set.mem_compl_iff]
  constructor
  · rintro ⟨⟨W', hW', hzW'⟩, hzR⟩
    exact ⟨(hS hW').1.2 hzW', hzR⟩
  · rintro ⟨hzD, hzR⟩
    obtain ⟨W', hW', hzW'⟩ := exists_mem_componentsOf hzD
    by_cases h : W' ∈ S
    · exact ⟨⟨W', h, hzW'⟩, hzR⟩
    · exact absurd ⟨W', ⟨hW', h⟩, hzW'⟩ hzR

/-- At each point `x`, the ideal of `Z_{-1}(K, D)` in `𝒪_{X,x}` is generated by a single
non-zero-divisor: a local equation of `D` if `x ∈ Z_{-1}(K, D)`, and `1` otherwise. -/
private theorem exists_isRegular_stalk_centre {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme sX)
    [LocallyOfFiniteType sX] [QuasiCompact sX] (K : MarkedIdeal X) (D : X.IdealSheafData)
    (hD : MMP.Mori.IsSmoothScheme (D.subschemeι ≫ sX)) (hD' : MMP.Mori.IsPureCodimOne D.support)
    (x : X) : ∃ t, _root_.IsRegular t ∧
      IdealSheafData.stalk (divisorComponentCentre K D) x = Ideal.span {t} := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  set S : Set (Set X) := {W | W ∈ componentsOf (D.support : Set X) ∧ W ⊆ K.cosupport}
  have hS : S ⊆ componentsOf (D.support : Set X) := fun W hW => hW.1
  have hU : IsClosed (⋃₀ S) := Aux.isClosed_sUnion_of_subset_componentsOf sX D S hS
  change ∃ t, _ ∧ IdealSheafData.stalk
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure (⋃₀ S))) x = _
  by_cases hx : x ∈ ⋃₀ S
  · obtain ⟨W, hWS, hxW⟩ := hx
    obtain ⟨t, ht, htD⟩ := exists_isRegular_stalk_eq_span sX hX D hD hD' ((hS hWS).1.2 hxW)
    exact ⟨t, ht, by rw [stalk_vanishingIdeal_sUnion_eq sX D hD hS hWS hxW, htD]⟩
  · refine ⟨1, isRegular_one, ?_⟩
    rw [Ideal.span_singleton_one, IdealSheafData.stalk_eq_top_iff_notMem_support]
    simpa [hU.closure_eq, Stacks.AffineClosedUnion.support_vanishingIdeal] using hx

/-- On a smooth scheme over a field, for a smooth divisor `D` of pure codimension one, the
centre `Z_{-1}(K, D)` is an effective Cartier divisor. -/
private theorem isEffectiveCartier_centre {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme sX)
    [LocallyOfFiniteType sX] [QuasiCompact sX] (K : MarkedIdeal X) (D : X.IdealSheafData)
    (hD : MMP.Mori.IsSmoothScheme (D.subschemeι ≫ sX))
    (hD' : MMP.Mori.IsPureCodimOne D.support) :
    Stacks.Divisors.IsEffectiveCartierDivisor (divisorComponentCentre K D) :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  isEffectiveCartierDivisor_of_stalk_regular_principal _ fun x _ =>
    exists_isRegular_stalk_centre sX hX K D hD hD' x

/-- The blow-up of `Z_{-1}(K, D)` is an isomorphism, `Z_{-1}(K, D)` being an effective Cartier
divisor . -/
private theorem isIso_centre {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme sX)
    [LocallyOfFiniteType sX] [QuasiCompact sX] (K : MarkedIdeal X) (D : X.IdealSheafData)
    (hD : MMP.Mori.IsSmoothScheme (D.subschemeι ≫ sX))
    (hD' : MMP.Mori.IsPureCodimOne D.support) :
    IsIso (blowUpToBase (divisorComponentCentre K D)) :=
  Stacks.Blowup.isIso_blowUpToBase_of_isEffectiveCartierDivisor _
    (isEffectiveCartier_centre sX hX K D hD hD')

end CartierCentre

/-- The case analysis of `𝓑𝓓` after the first blow-up, for a given `𝐁_S`. -/
private theorem main_case {N n m j : ℕ} (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hm : 1 ≤ m) (hmax : maxOrder t.I = m) (hj : j < t.E.s) :
    let μ := m.factorial
    let W : MarkedIdeal t.X := ⟨maximalCoefficientIdeal t.sX t.I μ, μ⟩
    let Z := divisorComponentCentre W (t.E.E ⟨j, hj⟩)
    let π := blowUpToBase Z
    let S := (t.E.E ⟨j, hj⟩).comap π
    let τ := S.subschemeι
    let tS : MarkedTriple.{u} :=
      ⟨⟨⟨S.subscheme, (W.birationalTransform Z).I.comap τ,
        ((t.E.comap π).deleteIndex j).comap τ⟩, t.k, τ ≫ π ≫ t.sX⟩, μ⟩
    ∀ BS : ClosedBlowupSequence S.subscheme,
      ((S.support : Set (blowUp Z)) = ∅ ∧ BS = .nil _ ∨
        ((S.support : Set (blowUp Z)).Nonempty ∧ BS = M (n - 1) μ tS)) →
      (ClosedBlowupSequence.cons Z (BS.pushforward τ)).reduction.IsOrderMTripleSeq
        t.sX t.I t.E m →
      let tr := t.endOf (ClosedBlowupSequence.cons Z (BS.pushforward τ)).reduction
      ∃ hjr : j < tr.E.s, Disjoint (⟨tr.I, m⟩ : MarkedIdeal tr.X).cosupport
        ((tr.E.E ⟨j, hjr⟩).support : Set tr.X) := by
  intro μ W Z π S τ tS BS hBS hB1 tr
  obtain ⟨hchar, hsm, hlft, hqc, heq, hnz, hE⟩ := id ht
  have hjr : j < tr.E.s := by
    change j < ((ClosedBlowupSequence.cons Z (BS.pushforward τ)).reduction.orderedTotalTransform
      t.E).s
    rw [length_orderedTotalTransform]
    omega
  refine ⟨hjr, ?_⟩
  obtain ⟨φ, hφ, hT, hMt⟩ :=
    pullbackReduced_iso (ClosedBlowupSequence.cons Z (BS.pushforward τ)) (𝟙 t.X)
  have hT0c : IsClosed ((t.E.E ⟨j, hj⟩).support : Set t.X) := (t.E.E ⟨j, hj⟩).support.isClosed
  have hsupp : ((tr.E.E ⟨j, hjr⟩).support : Set tr.X) =
      φ ⁻¹' entS (ClosedBlowupSequence.cons Z (BS.pushforward τ))
        ((t.E.E ⟨j, hj⟩).support : Set t.X) :=
    (support_orderedTotalTransform_entry
      (ClosedBlowupSequence.cons Z (BS.pushforward τ)).reduction t.E j hj hjr).trans (hT _ hT0c)
  have hsub : entS (ClosedBlowupSequence.cons Z (BS.pushforward τ))
      ((t.E.E ⟨j, hj⟩).support : Set t.X) ⊆ entS (BS.pushforward τ) (S.support : Set _) := by
    rw [entS_cons]
    refine entS_mono _ ?_
    rw [coe_support_comap]
    exact closure_minimal (Set.preimage_mono Set.diff_subset)
      (hT0c.preimage (blowUpToBase Z).continuous)
  rcases hBS with ⟨hS0, -⟩ | ⟨hSne, rfl⟩
  · refine Set.disjoint_left.2 fun y _ hy2 => ?_
    rw [hsupp] at hy2
    have := hsub hy2
    rw [hS0, entS_empty] at this
    exact this
  · have hdE := bdFunctor_input_mem_markedTriplesOfDim (m := m) (n := n) (j := j) t ht hm hmax
      hj hn hdim hSne
    have htS : tS ∈ markedTriples := isTriple_of_deleteEmpty hdE.1
    obtain ⟨F, hF1, hF2⟩ := hM μ (Nat.factorial_pos m)
    obtain ⟨d, hd, hdd⟩ := hdE.2.2
    rw [Set.mem_singleton_iff] at hd
    subst hd
    have htS' : tS ∈ markedTriplesOfDim (Set.Icc 0 (N - 1)) μ :=
      ⟨htS, rfl, n - 1, ⟨Nat.zero_le _, by omega⟩, hdd⟩
    have hdimNat : dimNat tS.X = n - 1 := by
      change ((topologicalKrullDim S.subscheme).unbotD 0).toNat = n - 1
      rw [hdd]; rfl
    have hBSeq : M (n - 1) μ tS = F.toFun tS htS' := by rw [hF1 tS htS', hdimNat]
    have hge : (M (n - 1) μ tS).IsOrderGeMarkedTripleSeq tS.sX tS.markedIdeal tS.E := by
      rw [hBSeq]; exact F.isOrderGeMarkedTripleSeq tS htS'
    have hlastmax : maxOrder ((M (n - 1) μ tS).markedTransform tS.markedIdeal).I < μ := by
      rw [hBSeq]; exact hF2.1 tS htS'
    have hlast : ∀ y : (M (n - 1) μ tS).target,
        multAt ((M (n - 1) μ tS).markedTransform tS.markedIdeal).I y < μ := fun y =>
      lt_of_le_of_lt (le_iSup₂ (f := fun z (_ : z ∈ Set.univ) =>
        multAt ((M (n - 1) μ tS).markedTransform tS.markedIdeal).I z) y (Set.mem_univ y))
        hlastmax
    have hSeq := bdFunctor_isOrderMTripleSeq M hN hM t ht hdim hn hnN hm hmax.le hj
    have hC := hSeq.2 hmax hSne
    have hres := bdFunctor_formalTransform_restrict_eq M hN hM t ht hdim hn hnN hm hmax hj hSne
    have : CharZero t.k := hchar
    have : LocallyOfFiniteType t.sX := hlft
    have : QuasiCompact t.sX := hqc
    have : Smooth t.sX := MMP.Mori.IsSmoothScheme.smooth hsm
    have hm' : (maxOrder t.I).toNat = m := by rw [hmax]; rfl
    have hdim1 : 1 ≤ topologicalKrullDim t.X := by rw [hdim]; exact_mod_cast hn
    have hcomp := pos_topologicalKrullDim_of_mem_irreducibleComponents heq hdim1
    have hCI : (ClosedBlowupSequence.cons Z
        ((M (n - 1) μ tS).pushforward τ)).IsOrderGeMarkedTripleSeq t.sX ⟨t.I, m⟩ t.E :=
      ((ClosedBlowupSequence.isOrderGeMarkedTripleSeq_iff_isOrderMTripleSeq t.sX t.I t.E ht m hmax
        _).1).2 hC
    have hCsm := (ClosedBlowupSequence.IsOrderGeMarkedTripleSeq.isSmooth_and_centersHaveSNCWith
      _ _ _ _ hCI).1
    have hCW : (ClosedBlowupSequence.cons Z
        ((M (n - 1) μ tS).pushforward τ)).IsOrderGeMarkedTripleSeq t.sX W t.E :=
      (ClosedBlowupSequence.isOrderGeMarkedTripleSeq_iff_maximalCoefficientIdeal_of_dvd
        t.sX t.I t.E ht hcomp (by omega) μ (Nat.factorial_pos m)
        (hm' ▸ Nat.dvd_factorial (by omega) le_rfl) _ hCsm).1 (by rwa [hm'])
    have hmdvd : m ∣ m.factorial := Nat.dvd_factorial (by omega) le_rfl
    have hs1 : 1 ≤ m.factorial / m :=
      Nat.div_pos (Nat.le_of_dvd (Nat.factorial_pos m) hmdvd) (by omega)
    have hmul : m * (m.factorial / m) = μ := Nat.mul_div_cancel' hmdvd
    have hmul' : (maxOrder t.I).toNat * (m.factorial / m) = μ := by rwa [hm']
    have hcos :=
      ClosedBlowupSequence.cosupport_markedTransform_eq_of_pow_le_of_le_maximalCoefficientIdeal
        t.sX heq hdim1 t.I (by omega) (m.factorial / m) hs1 W.I
        (by have := pow_le_maximalCoefficientIdeal t.sX t.I (m.factorial / m)
            rwa [hmul'] at this)
        (by rw [hmul']) t.E _ hCsm (by rwa [hm'])
    rw [hm', hmul] at hcos
    have hMt' := hMt t.sX ⟨t.I, m⟩ t.E hCI
    rw [Scheme.IdealSheafData.comap_id] at hMt'
    have htrI : tr.I = ((ClosedBlowupSequence.cons Z
        ((M (n - 1) μ tS).pushforward τ)).markedTransform ⟨t.I, m⟩).I.comap φ :=
      ((ClosedBlowupSequence.isOrderGeMarkedTripleSeq_iff_isOrderMTripleSeq t.sX t.I t.E
        ht m hmax _).2 hB1).symm.trans (congrArg MarkedIdeal.I hMt')
    obtain ⟨hDr, hDp, hDsm⟩ := hE.2.1 ⟨j, hj⟩
    have hπiso : IsIso π := isIso_centre t.sX hsm W _ hDsm hDp
    have hZspec := divisorComponentCentre_spec t.sX W (t.E.E ⟨j, hj⟩) hDsm hDp
    have hcomp2 := componentsOfCodimAtLeastTwo_eq_empty_of_isPureCodimOne hZspec.2.1
    have hSrange : Set.range τ = (S.support : Set (blowUp Z)) :=
      Scheme.IdealSheafData.range_subschemeι S
    have hE0 : (((t.E.totalTransform Z).E (Fin.castSucc ⟨j, hj⟩)).support : Set (blowUp Z)) =
        Set.range τ := by
      rw [support_totalTransform_castSucc, hSrange, coe_support_comap, hcomp2, Set.diff_empty]
      exact (hT0c.preimage (blowUpToBase Z).continuous).closure_eq
    have : IsReduced S.subscheme := by
      have : IsReduced (Limits.pullback π (t.E.E ⟨j, hj⟩).subschemeι) :=
        isReduced_of_isOpenImmersion (Limits.pullback.snd π (t.E.E ⟨j, hj⟩).subschemeι)
      exact isReduced_of_isOpenImmersion ((t.E.E ⟨j, hj⟩).comapIso π).hom
    have hposBS : HasCentresOfPositiveCodim (M (n - 1) μ tS) :=
      hasCentresOfPositiveCodim_of_isOrderGe _ _ _ _ hge
    have hPush := isPushforward_pushforward τ (M (n - 1) μ tS)
    have hCtail : ((M (n - 1) μ tS).pushforward τ).IsOrderMTripleSeq (π ≫ t.sX)
        (MMP.Resolution.controlledTransform Z t.I) (t.E.totalTransform Z) m := hC.2.2.2.2.2
    have hInv := entS_eq_range ((M (n - 1) μ tS).pushforward τ) τ (M (n - 1) μ tS) (π ≫ t.sX)
      (MMP.Resolution.controlledTransform Z t.I) (t.E.totalTransform Z) m (Fin.castSucc ⟨j, hj⟩)
      hPush hposBS hCtail hE0
    refine Set.disjoint_left.2 fun y hy1 hy2 => ?_
    rw [hsupp] at hy2
    have hx1 := hsub hy2
    have hx2 : φ y ∈ Set.range (((M (n - 1) μ tS).pushforward τ).pullbackHom τ) := by
      rwa [← hInv, hSrange]
    have h1 : (m : ℕ∞) ≤ multAt tr.I y := hy1
    rw [htrI] at h1
    have := hφ
    have h2 := le_multAt_of_le_multAt_comap φ _ y h1
    have h3 : φ y ∈ ((ClosedBlowupSequence.cons Z ((M (n - 1) μ tS).pushforward τ)).markedTransform
        ⟨t.I, m⟩).cosupport := by
      show (((ClosedBlowupSequence.cons Z ((M (n - 1) μ tS).pushforward τ)).markedTransform
        ⟨t.I, m⟩).m : ℕ∞) ≤ _
      rwa [ClosedBlowupSequence.markedTransform_m]
    rw [hcos] at h3
    have h5 : (μ : ℕ∞) ≤ multAt (((M (n - 1) μ tS).pushforward τ).markedTransform
        ⟨(W.birationalTransform Z).I, μ⟩).I (φ y) := by
      have h4 : (((ClosedBlowupSequence.cons Z ((M (n - 1) μ tS).pushforward τ)).markedTransform
          ⟨W.I, m.factorial⟩).m : ℕ∞) ≤ _ := h3
      rw [ClosedBlowupSequence.markedTransform_m] at h4
      exact h4
    exact core_order S ((M (n - 1) μ tS).pushforward τ) (M (n - 1) μ tS) (π ≫ t.sX)
      (W.birationalTransform Z).I μ (t.E.totalTransform Z) hCW.2.2.2.2.2 hge hlast hres
      (φ y) hx2 h5

/-- A marked ideal whose marking exceeds the maximal order has empty cosupport. -/
private theorem cosupport_eq_empty_of_maxOrder_lt {X : Scheme.{u}} (I : X.IdealSheafData)
    {m : ℕ} (h : maxOrder I < m) : (⟨I, m⟩ : MarkedIdeal X).cosupport = ∅ := by
  ext x
  simp only [MarkedIdeal.cosupport, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
  refine lt_of_le_of_lt ?_ h
  exact le_iSup₂ (f := fun z (_ : z ∈ Set.univ) => multAt I z) x (Set.mem_univ x)

/-- The case `maxord I = m` of `MMP.Resolution.disjoint_cosupport_bdFunctor`. -/
private theorem disjoint_of_maxOrder_eq {N n m j : ℕ} (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hm : 1 ≤ m) (hmax : maxOrder t.I = m) (hj : j < t.E.s) :
    let tr := t.endOf (bdFunctor M n m j t)
    ∃ hjr : j < tr.E.s,
      Disjoint (⟨tr.I, m⟩ : MarkedIdeal tr.X).cosupport
        ((tr.E.E ⟨j, hjr⟩).support : Set tr.X) := by
  dsimp only
  let μ := m.factorial
  let W : MarkedIdeal t.X := ⟨maximalCoefficientIdeal t.sX t.I μ, μ⟩
  let Z := divisorComponentCentre W (t.E.E ⟨j, hj⟩)
  let π := blowUpToBase Z
  let S := (t.E.E ⟨j, hj⟩).comap π
  let τ := S.subschemeι
  let tS : MarkedTriple.{u} :=
    ⟨⟨⟨S.subscheme, (W.birationalTransform Z).I.comap τ,
      ((t.E.comap π).deleteIndex j).comap τ⟩, t.k, τ ≫ π ≫ t.sX⟩, μ⟩
  classical
  let BS' : ClosedBlowupSequence S.subscheme :=
    if (S.support : Set (blowUp Z)).Nonempty ∧ tS ∈ markedTriples then M (n - 1) μ tS else .nil _
  have hbd : bdFunctor M n m j t =
      (ClosedBlowupSequence.cons Z (BS'.pushforward τ)).reduction := by
    rw [bdFunctor, dif_pos ⟨hmax, hj⟩]
  have hSeq := (bdFunctor_isOrderMTripleSeq M hN hM t ht hdim hn hnN hm hmax.le hj).1
  rw [hbd] at hSeq
  have hBS : ((S.support : Set (blowUp Z)) = ∅ ∧ BS' = .nil _) ∨
      ((S.support : Set (blowUp Z)).Nonempty ∧ BS' = M (n - 1) μ tS) := by
    by_cases hc : (S.support : Set (blowUp Z)).Nonempty ∧ tS ∈ markedTriples
    · exact Or.inr ⟨hc.1, if_pos hc⟩
    · refine Or.inl ⟨?_, if_neg hc⟩
      by_contra hne
      have hne' : (S.support : Set (blowUp Z)).Nonempty := Set.nonempty_iff_ne_empty.2 hne
      exact hc ⟨hne', isTriple_of_deleteEmpty
        (bdFunctor_input_mem_markedTriplesOfDim (m := m) (n := n) (j := j) t ht hm hmax hj hn
          hdim hne').1⟩
  have key := main_case M hN hM t ht hdim hn hnN hm hmax hj BS' hBS hSeq
  rw [hbd]
  exact key

end Separation

/-- **Kollár, Lemma 3.102.** Let `M` be a marked order-reduction family on dimensions
`0, …, N - 1` (`IsMarkedOrderReductionFamily`), `(X, I, E)` a triple of dimension `n` with
`1 ≤ n ≤ N`, `m ≥ 1` with `maxord I ≤ m`, and `j < s` (`0`-based). If `bdFunctor M n m j (X, I, E)`
ends with `(X_r, I_r, E_r)` (`FieldBlowupTriple.endOf`), then `E_r` has a `j`-th member `E_r^j`
(the birational transform of `E^j`), and `cosupp(I_r, m)` is disjoint from `Supp E_r^j`. -/
@[mmp "lem_kr3e_bd_separates_divisor"]
public theorem disjoint_cosupport_bdFunctor {N n m j : ℕ} (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hm : 1 ≤ m) (hmax : maxOrder t.I ≤ m) (hj : j < t.E.s) :
    let tr := t.endOf (bdFunctor M n m j t)
    ∃ hjr : j < tr.E.s,
      Disjoint (⟨tr.I, m⟩ : MarkedIdeal tr.X).cosupport
        ((tr.E.E ⟨j, hjr⟩).support : Set tr.X) := by
  rcases hmax.lt_or_eq with hlt | heq
  · have hB : bdFunctor M n m j t = .nil t.X := by
      rw [bdFunctor, dif_neg (fun h => hlt.ne h.1)]
    dsimp only
    generalize hb : bdFunctor M n m j t = B
    rw [hB] at hb
    subst hb
    refine ⟨hj, ?_⟩
    change Disjoint (⟨t.I, m⟩ : MarkedIdeal t.X).cosupport _
    rw [cosupport_eq_empty_of_maxOrder_lt t.I hlt]
    exact Set.empty_disjoint _
  · exact disjoint_of_maxOrder_eq M hN hM t ht hdim hn hnN hm heq hj

end MMP.Resolution
