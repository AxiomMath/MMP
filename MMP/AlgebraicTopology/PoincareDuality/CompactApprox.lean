module

public import MMP.AlgebraicTopology.PoincareDuality.MayerVietoris
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Order.Interval.Set.Pi

/-!
# Local homology vanishing for arbitrary compact sets from a basis of closed sets

Hatcher's Lemma 3.27 deduces the vanishing of the local homology `H_i(Y, Y - K)` for every
compact `K` from the case of convex compact sets in a chart, in two steps.

* **Finite unions.** Let `𝔅` be a family of closed sets stable under pairwise intersection
  (empty intersections are allowed). If `H_{k+1}(Y, Y - B) = 0` for every `B ∈ 𝔅` and every
  `k ≥ m`, then `H_{k+1}(Y, Y - L) = 0` for every finite union `L` of members of `𝔅` and
  `k ≥ m`: by the Mayer–Vietoris step
  (`MMP.SingularChain.RelVanishing.union`), by induction on the number of
  members, since `B ∩ (B₁ ∪ ⋯ ∪ B_r) = (B ∩ B₁) ∪ ⋯ ∪ (B ∩ B_r)`.
* **Approximation.** If moreover every compact `K` inside an open `V` lies in a finite union of
  members of `𝔅` inside `V`, then `H_{m+1}(Y, Y - K) = 0` for every compact `K` of a Hausdorff
  `Y`: a relative cycle `c` of `(Y, Y - K)` has finitely many simplices in its boundary, whose
  compact images avoid `K`; a finite union `L ⊇ K` of members of `𝔅` avoiding them makes `c` a
  relative cycle of `(Y, Y - L)`, hence `c = ∂ w + f` with `f` in `Y - L ⊆ Y - K`.

For `ℝⁿ = Fin n → ℝ` the closed boxes `Set.Icc a b` form such a family.

## Main results

* `MMP.SingularChain.relVanishing_sUnion`: finite unions.
* `MMP.SingularChain.relVanishing_of_isCompact_euclidean`: the case of boxes in
  `ℝⁿ`.

## References

* [A. Hatcher, *Algebraic Topology*][hatcher2002], §3.3, Lemma 3.27.
-/

@[expose] public noncomputable section

open Set Finsupp Topology

namespace MMP

namespace SingularChain

variable {R : Type*} [CommRing R] {Y : Type*} [TopologicalSpace Y]

/-- `H_{m+1}(Y, Y - ∅) = 0`. -/
lemma relVanishing_empty (m : ℕ) : RelVanishing R Y m ∅ := fun c _ ↦
  ⟨0, by simp [inside, Finsupp.supported_univ]⟩

/-- **Finite unions** (Hatcher, Lemma 3.27): local homology vanishing in degrees `> m` for the
members of a family of closed sets stable under intersection gives it for their finite
unions. -/
theorem relVanishing_sUnion {𝔅 : Set (Set Y)} (hclosed : ∀ B ∈ 𝔅, IsClosed B)
    (hinter : ∀ B ∈ 𝔅, ∀ B' ∈ 𝔅, B ∩ B' ∈ 𝔅) {m : ℕ}
    (hbase : ∀ B ∈ 𝔅, ∀ k, m ≤ k → RelVanishing R Y k B) :
    ∀ s : Finset (Set Y), ↑s ⊆ 𝔅 → ∀ k, m ≤ k → RelVanishing R Y k (⋃₀ (s : Set (Set Y))) := by
  classical
  suffices h : ∀ N, ∀ s : Finset (Set Y), s.card ≤ N → ↑s ⊆ 𝔅 →
      ∀ k, m ≤ k → RelVanishing R Y k (⋃₀ (s : Set (Set Y))) from
    fun s hs ↦ h s.card s le_rfl hs
  intro N
  induction N with
  | zero =>
    intro s hs _ k _
    rw [Finset.card_eq_zero.1 (Nat.le_zero.1 hs), Finset.coe_empty, sUnion_empty]
    exact relVanishing_empty k
  | succ N ih =>
    intro s hs hs𝔅 k hk
    rcases s.eq_empty_or_nonempty with rfl | ⟨B, hB⟩
    · rw [Finset.coe_empty, sUnion_empty]
      exact relVanishing_empty k
    have hs' : s = insert B (s.erase B) := (Finset.insert_erase hB).symm
    have hcard : (s.erase B).card ≤ N := by
      rw [Finset.card_erase_of_mem hB]
      omega
    have hsub : ↑(s.erase B) ⊆ 𝔅 := fun x hx ↦ hs𝔅 (Finset.mem_of_mem_erase hx)
    have hB𝔅 : B ∈ 𝔅 := hs𝔅 hB
    have himg : ↑((s.erase B).image (B ∩ ·)) ⊆ 𝔅 := by
      intro x hx
      rw [Finset.coe_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact hinter B hB𝔅 y (hsub hy)
    have hcard' : ((s.erase B).image (B ∩ ·)).card ≤ N :=
      Finset.card_image_le.trans hcard
    have hclosedU : IsClosed (⋃₀ ((s.erase B : Finset (Set Y)) : Set (Set Y))) := by
      rw [sUnion_eq_biUnion]
      exact isClosed_biUnion_finset fun t ht ↦ hclosed t (hsub ht)
    have heq : B ∩ ⋃₀ ((s.erase B : Finset (Set Y)) : Set (Set Y)) =
        ⋃₀ (((s.erase B).image (B ∩ ·) : Finset (Set Y)) : Set (Set Y)) := by
      rw [Finset.coe_image, sUnion_image, sUnion_eq_biUnion, inter_iUnion₂]
    rw [hs', Finset.coe_insert, sUnion_insert]
    refine RelVanishing.union (hclosed B hB𝔅) hclosedU (hbase B hB𝔅 k hk)
      (ih (s.erase B) hcard hsub k hk) ?_
    rw [heq]
    exact ih _ hcard' himg (k + 1) (by omega)

/-- **Approximation** (Hatcher, Lemma 3.27): in a Hausdorff space, if every compact subset of
an open set `V` lies in a finite union of members of `𝔅` inside `V`, and
`H_{m+1}(Y, Y - L) = 0` for these finite unions `L`, then `H_{m+1}(Y, Y - K) = 0` for every
compact `K`. -/
theorem relVanishing_of_isCompact_of_approx [T2Space Y] {𝔅 : Set (Set Y)} {m : ℕ}
    (happrox : ∀ K V : Set Y, IsCompact K → IsOpen V → K ⊆ V →
      ∃ s : Finset (Set Y), ↑s ⊆ 𝔅 ∧ K ⊆ ⋃₀ (s : Set (Set Y)) ∧ ⋃₀ (s : Set (Set Y)) ⊆ V)
    (hunion : ∀ s : Finset (Set Y), ↑s ⊆ 𝔅 → RelVanishing R Y m (⋃₀ (s : Set (Set Y))))
    {K : Set Y} (hK : IsCompact K) : RelVanishing R Y m K := by
  intro c hc
  -- the union of the images of the simplices of `∂ c`
  set T : Set Y := ⋃ τ ∈ (bd R m c).support, range τ
  have hT : IsClosed T :=
    ((bd R m c).support.isCompact_biUnion fun τ _ ↦
      isCompact_range τ.continuous).isClosed
  have hKT : K ⊆ Tᶜ := by
    intro x hx hxT
    obtain ⟨τ, hτ, hxτ⟩ := mem_iUnion₂.1 hxT
    exact (mem_supported R _ |>.1 hc hτ) hxτ hx
  obtain ⟨s, hs𝔅, hKs, hsT⟩ := happrox K Tᶜ hK hT.isOpen_compl hKT
  have hc' : bd R m c ∈ inside R m (⋃₀ (s : Set (Set Y)))ᶜ := by
    refine (mem_supported R _).2 fun τ hτ y hy hys ↦ ?_
    exact hsT hys (mem_iUnion₂.2 ⟨τ, hτ, hy⟩)
  exact (hunion s hs𝔅 c hc').mono hKs

/-- The closed boxes of `ℝⁿ` approximate compact sets from inside open sets. -/
lemma exists_finset_Icc_of_isCompact {n : ℕ} {K V : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ s : Finset (Set (Fin n → ℝ)), (s : Set (Set (Fin n → ℝ))) ⊆ {B | ∃ a b, B = Icc a b} ∧
      K ⊆ ⋃₀ (s : Set (Set (Fin n → ℝ))) ∧ ⋃₀ (s : Set (Set (Fin n → ℝ))) ⊆ V := by
  classical
  have hδ : ∀ x ∈ V, ∃ ε > 0, Metric.closedBall x ε ⊆ V := fun x hx ↦
    Metric.nhds_basis_closedBall.mem_iff.1 (hV.mem_nhds hx)
  choose! δ hδpos hδV using hδ
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover (fun x ↦ Metric.closedBall x (δ x))
    fun x hx ↦ Metric.closedBall_mem_nhds x (hδpos x (hKV hx))
  refine ⟨t.image fun x ↦ Metric.closedBall x (δ x), ?_, ?_, ?_⟩
  · intro B hB
    rw [Finset.coe_image] at hB
    obtain ⟨x, hx, rfl⟩ := hB
    refine ⟨x - fun _ ↦ δ x, x + fun _ ↦ δ x, ?_⟩
    ext y
    rw [Metric.mem_closedBall, dist_pi_le_iff (hδpos x (hKV (htK x hx))).le, mem_Icc, Pi.le_def,
      Pi.le_def, ← forall_and]
    refine forall_congr' fun i ↦ ?_
    rw [Real.dist_eq, abs_le, Pi.sub_apply, Pi.add_apply]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  · rw [Finset.coe_image, sUnion_image]
    exact hcover
  · rw [Finset.coe_image, sUnion_image]
    exact iUnion₂_subset fun x hx ↦ hδV x (hKV (htK x hx))

/-- **Local homology vanishing for compact sets of `ℝⁿ`** (Hatcher, Lemma 3.27, steps 2–3): if
`H_{k+1}(ℝⁿ, ℝⁿ - Q) = 0` for every closed box `Q` and every `k ≥ m`, then
`H_{m+1}(ℝⁿ, ℝⁿ - K) = 0` for every compact `K`. -/
theorem relVanishing_of_isCompact_euclidean {n m : ℕ}
    (hbox : ∀ a b : Fin n → ℝ, ∀ k, m ≤ k → RelVanishing R (Fin n → ℝ) k (Icc a b))
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) : RelVanishing R (Fin n → ℝ) m K := by
  have hclosed : ∀ B ∈ {B : Set (Fin n → ℝ) | ∃ a b, B = Icc a b}, IsClosed B := by
    rintro B ⟨a, b, rfl⟩
    exact isClosed_Icc
  have hinter : ∀ B ∈ {B : Set (Fin n → ℝ) | ∃ a b, B = Icc a b},
      ∀ B' ∈ {B : Set (Fin n → ℝ) | ∃ a b, B = Icc a b},
      B ∩ B' ∈ {B : Set (Fin n → ℝ) | ∃ a b, B = Icc a b} := by
    rintro B ⟨a, b, rfl⟩ B' ⟨c, d, rfl⟩
    exact ⟨a ⊔ c, b ⊓ d, Icc_inter_Icc⟩
  have hbase : ∀ B ∈ {B : Set (Fin n → ℝ) | ∃ a b, B = Icc a b}, ∀ k, m ≤ k →
      RelVanishing R (Fin n → ℝ) k B := by
    rintro B ⟨a, b, rfl⟩ k hk
    exact hbox a b k hk
  exact relVanishing_of_isCompact_of_approx
    (fun K V hK hV hKV ↦ exists_finset_Icc_of_isCompact hK hV hKV)
    (fun s hs ↦ relVanishing_sUnion hclosed hinter hbase s hs m le_rfl) hK

/-- **Gluing over charts** (Hatcher, Lemma 3.27, step 4): in a locally compact Hausdorff space
covered by open sets `U ∈ 𝒰` such that `H_{k+1}(Y, Y - K) = 0` for every compact `K` inside a
member of `𝒰` and every `k ≥ m`, the same holds for every compact `K`. -/
theorem relVanishing_of_isCompact_of_local [T2Space Y] [LocallyCompactSpace Y]
    {𝒰 : Set (Set Y)} (h𝒰 : ∀ U ∈ 𝒰, IsOpen U) (hcover : ∀ x, ∃ U ∈ 𝒰, x ∈ U) {m : ℕ}
    (hloc : ∀ U ∈ 𝒰, ∀ K : Set Y, IsCompact K → K ⊆ U → ∀ k, m ≤ k → RelVanishing R Y k K)
    {K : Set Y} (hK : IsCompact K) : ∀ k, m ≤ k → RelVanishing R Y k K := by
  classical
  set 𝔅 : Set (Set Y) := {B | IsCompact B ∧ ∃ U ∈ 𝒰, B ⊆ U}
  have hclosed : ∀ B ∈ 𝔅, IsClosed B := fun B hB ↦ hB.1.isClosed
  have hinter : ∀ B ∈ 𝔅, ∀ B' ∈ 𝔅, B ∩ B' ∈ 𝔅 := by
    rintro B ⟨hB, U, hU, hBU⟩ B' ⟨hB', -, -, -⟩
    exact ⟨hB.inter hB', U, hU, inter_subset_left.trans hBU⟩
  have hbase : ∀ B ∈ 𝔅, ∀ k, m ≤ k → RelVanishing R Y k B := by
    rintro B ⟨hB, U, hU, hBU⟩ k hk
    exact hloc U hU B hB hBU k hk
  -- a compact neighbourhood of each point inside a member of `𝒰`
  have hC : ∀ x : Y, ∃ C : Set Y, IsCompact C ∧ C ∈ 𝓝 x ∧ ∃ U ∈ 𝒰, C ⊆ U := fun x ↦ by
    obtain ⟨U, hU, hxU⟩ := hcover x
    obtain ⟨C, hC, hxC, hCU⟩ := exists_compact_subset (h𝒰 U hU) hxU
    exact ⟨C, hC, mem_interior_iff_mem_nhds.1 hxC, U, hU, hCU⟩
  choose C hCc hCn hCU using hC
  obtain ⟨t, -, hcov⟩ := hK.elim_nhds_subcover C fun x _ ↦ hCn x
  have hKeq : K = ⋃₀ ((t.image fun x ↦ K ∩ C x : Finset (Set Y)) : Set (Set Y)) := by
    rw [Finset.coe_image, sUnion_image, ← inter_iUnion₂]
    exact (inter_eq_left.2 hcov).symm
  have hs : ((t.image fun x ↦ K ∩ C x : Finset (Set Y)) : Set (Set Y)) ⊆ 𝔅 := by
    intro B hB
    rw [Finset.coe_image] at hB
    obtain ⟨x, -, rfl⟩ := hB
    obtain ⟨U, hU, hCxU⟩ := hCU x
    exact ⟨hK.inter_right (hCc x).isClosed, U, hU, inter_subset_right.trans hCxU⟩
  intro k hk
  rw [hKeq]
  exact relVanishing_sUnion hclosed hinter hbase _ hs k hk

end SingularChain

end MMP
