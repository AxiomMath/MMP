module

public import StacksFrontier.Topology.Dimension.MaximalPointDrop
public import StacksFrontier.Topology.Dimension.ClosedSubsetDimension
public import Mathlib.Order.CompletePartialOrder

/-!
# Proper closed subsets have smaller Krull dimension

In an irreducible space, a proper closed subset of finite Krull dimension has strictly smaller
Krull dimension; more generally a proper closed subset `Y` of an irreducible subset `T` of finite
dimension has `dim Y < dim T`.

Stacks records the first statement under the hypothesis that the ambient space has finite
dimension (`topologicalKrullDim_lt_of_isClosed_ne_univ`); MMP uses it with the hypothesis on the
closed subset instead.

Cutting a closed set `T` by a closed set `H` missing a generization of each point of `T ∩ H`
lowers the dimension by one (`MMP.topologicalKrullDim_inter_le_pred_of_forall_exists_specializes`).
-/

@[expose] public section

open TopologicalSpace

namespace MMP

/-- In an irreducible space, a proper closed subset of finite Krull dimension has strictly smaller
Krull dimension. -/
theorem topologicalKrullDim_lt_of_isClosed_of_ne_univ {T : Type*} [TopologicalSpace T]
    [IrreducibleSpace T] {Y : Set T} (hY : IsClosed Y) (hne : Y ≠ Set.univ)
    (hfin : topologicalKrullDim Y ≠ ⊤) : topologicalKrullDim Y < topologicalKrullDim T := by
  let top : IrreducibleCloseds T := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ T, isClosed_univ⟩
  rcases isEmpty_or_nonempty (IrreducibleCloseds Y) with hE | hE
  · have h1 : topologicalKrullDim Y = ⊥ := Order.krullDim_eq_bot
    haveI : Nonempty (IrreducibleCloseds T) := ⟨top⟩
    rw [h1]
    exact (WithBot.bot_lt_coe 0).trans_le Order.krullDim_nonneg
  · let g : IrreducibleCloseds Y → IrreducibleCloseds T := fun S =>
      ⟨Subtype.val '' (S : Set Y), S.isIrreducible.image _ continuous_subtype_val.continuousOn,
        hY.isClosedEmbedding_subtypeVal.isClosedMap _ S.isClosed⟩
    have hg : StrictMono g := fun _ _ h => Subtype.val_injective.image_strictMono h
    let f : WithTop (IrreducibleCloseds Y) → IrreducibleCloseds T := fun x =>
      match x with
      | ⊤ => top
      | (S : IrreducibleCloseds Y) => g S
    have hf : StrictMono f := by
      refine WithTop.strictMono_iff.mpr ⟨hg, fun S => ?_⟩
      show (Subtype.val '' (S : Set Y)) ⊂ Set.univ
      exact (Subtype.coe_image_subset _ _).trans_ssubset (Set.ssubset_univ_iff.mpr hne)
    have hle := Order.krullDim_le_of_strictMono f hf
    rw [Order.krullDim_WithTop] at hle
    refine lt_of_lt_of_le ?_ hle
    obtain ⟨n, hn⟩ : ∃ n : ℕ, topologicalKrullDim Y = n := by
      have hbot : topologicalKrullDim Y ≠ ⊥ := Order.krullDim_ne_bot_iff.mpr hE
      induction h : topologicalKrullDim Y with
      | bot => exact absurd h hbot
      | coe m =>
        induction m with
        | top => exact absurd h hfin
        | coe m => exact ⟨m, rfl⟩
    change topologicalKrullDim Y < topologicalKrullDim Y + 1
    rw [hn]
    exact WithBot.coe_lt_coe.mpr (ENat.coe_lt_coe.mpr n.lt_succ_self)

/-- **A proper closed subset has smaller dimension.** If `Y` is a closed subset of an irreducible
subset `T`, `Y ≠ T`, and `T` has finite dimension, then `dim Y < dim T`. -/
theorem topologicalKrullDim_lt_of_subset_of_ne {X : Type*} [TopologicalSpace X] {T Y : Set X}
    (hT : IsIrreducible T) (hY : IsClosed Y) (hYT : Y ⊆ T) (hne : Y ≠ T)
    (hfin : topologicalKrullDim T ≠ ⊤) : topologicalKrullDim Y < topologicalKrullDim T := by
  haveI : IrreducibleSpace T := isIrreducible_iff_irreducibleSpace.mp hT
  rw [← topologicalKrullDim_preimage_val T Y hYT]
  refine topologicalKrullDim_lt_of_isClosed_of_ne_univ (hY.preimage continuous_subtype_val)
    (fun h ↦ hne (subset_antisymm hYT fun x hx ↦ Set.eq_univ_iff_forall.mp h ⟨x, hx⟩)) ?_
  rw [topologicalKrullDim_preimage_val T Y hYT]
  exact ne_top_of_le_ne_top hfin (topologicalKrullDim_le_of_subset hYT)

/-- **Cutting a closed set by a closed set missing a generization of each of its points lowers
the dimension.** Let `T, H ⊆ X` be closed, `X` quasi-sober, `dim T ≤ d`, and suppose every point
`x` of `T ∩ H` is a specialization of a point of `T` outside `H`. If `T ∩ H` is nonempty then
`1 ≤ d` and `dim (T ∩ H) ≤ d - 1`. -/
theorem topologicalKrullDim_inter_le_pred_of_forall_exists_specializes {X : Type*}
    [TopologicalSpace X] [QuasiSober X] {T H : Set X} (hT : IsClosed T) (hH : IsClosed H)
    {d : ℕ} (hd : topologicalKrullDim T ≤ d) (hgen : ∀ x ∈ T ∩ H, ∃ η ∈ T, η ⤳ x ∧ η ∉ H)
    (hne : (T ∩ H).Nonempty) :
    1 ≤ d ∧ topologicalKrullDim (T ∩ H : Set X) ≤ ((d - 1 : ℕ) : WithBot ℕ∞) := by
  have key : ∀ x ∈ T ∩ H, 1 ≤ d ∧
      topologicalKrullDim (closure ({x} : Set X)) ≤ ((d - 1 : ℕ) : WithBot ℕ∞) := by
    intro x hx
    obtain ⟨η, hηT, hηx, hηH⟩ := hgen x hx
    have hCT : closure ({η} : Set X) ⊆ T := hT.closure_subset_iff.mpr (by simpa using hηT)
    have hxC : x ∈ closure ({η} : Set X) := specializes_iff_mem_closure.mp hηx
    have hCH : ¬ closure ({η} : Set X) ⊆ H := fun hsub => hηH (hsub (subset_closure rfl))
    obtain ⟨h1, h2⟩ := topologicalKrullDim_inter_le_pred_of_not_subset
      isIrreducible_singleton.closure hH hCH ⟨x, hxC, hx.2⟩
      ((topologicalKrullDim_le_of_subset hCT).trans hd)
    refine ⟨h1, le_trans (topologicalKrullDim_le_of_subset ?_) h2⟩
    exact (isClosed_closure.inter hH).closure_subset_iff.mpr (by simpa using ⟨hxC, hx.2⟩)
  obtain ⟨x, hx⟩ := hne
  exact ⟨(key x hx).1, topologicalKrullDim_le_of_forall_closure (hT.inter hH) fun y hy =>
    (key y hy).2⟩

end MMP
