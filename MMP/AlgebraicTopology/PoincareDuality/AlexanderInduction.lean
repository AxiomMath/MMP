module

public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Bases
public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Analysis.Normed.Module.Convex

/-!
# Induction on open sets (Bredon's lemma)

The step of the proof of Poincaré duality for a noncompact manifold that passes from convex
pieces in charts to arbitrary open sets (Bredon, *Topology and Geometry*, VI.7.9; Hatcher,
Lemma 3.36 for the compactly supported form). Let `Z` be a locally compact, second-countable
space and `𝔅` a family of open sets, stable under binary intersection. Let `P` be a property of
open sets of `Z` such that

1. `P B` for every `B ∈ 𝔅`, and `P ∅`;
2. (Mayer–Vietoris) `P U`, `P V` and `P (U ∩ V)` give `P (U ∪ V)`;
3. (disjoint unions) `P (⋃ i, U i)` for pairwise disjoint opens `U i`, `i : ℕ`, with `P (U i)`.

Then `P U` holds for every open `U` in which `𝔅` is a basis at every point.

* Finite unions of members of `𝔅`: by induction on the number of members, as
  `B ∩ (B₁ ∪ ⋯ ∪ B_r) = (B ∩ B₁) ∪ ⋯ ∪ (B ∩ B_r)`.
* General `U`: for a compact exhaustion `∅ = M₀ ⊆ M₁ ⊆ ⋯` of `U` (`Mₖ ⊆ interior Mₖ₊₁`), the
  compact `Aₙ = M₂ₙ₊₂ - interior M₂ₙ` lies in the open `Wₙ = interior M₂ₙ₊₃ - M₂ₙ₋₁`, hence in a
  finite union `Uₙ ⊆ Wₙ` of members of `𝔅`; and `Uₙ ∩ Uₘ = ∅` for `m ≥ n + 2`. So the even
  `Uₙ`, the odd `Uₙ`, and the `Uₙ ∩ Uₙ₊₁` are three disjoint families, and
  `U = (⋃ U₂ₖ) ∪ (⋃ U₂ₖ₊₁)` with intersection `⋃ (Uₙ ∩ Uₙ₊₁)`.

For a manifold modelled on `H`, the two-stage form: with `𝔅` the open sets convex in a chart
`e` (stable under intersection, `e` being injective on its source), `P` holds for every open set
inside a chart domain; these form a basis stable under intersection, so `P` holds everywhere.

## Main results

* `MMP.forall_isOpen_of_finite_unions`: finite unions of members of `𝔅`.
* `MMP.isOpen_induction`: Bredon's lemma for an open set.
* `MMP.isOpen_induction_chartedSpace`: the manifold form.

## References

* [G. Bredon, *Topology and Geometry*][bredon1993], VI.7.9.
* [A. Hatcher, *Algebraic Topology*][hatcher2002], §3.3, Lemma 3.36.
-/

@[expose] public section

open Set Topology Filter Function

namespace MMP

section Abstract

variable {Z : Type*} [TopologicalSpace Z] {𝔅 : Set (Set Z)} {P : Set Z → Prop}

/-- **Finite unions.** If `𝔅` is stable under binary intersection, `P` holds on `𝔅` and on `∅`,
and `P` has the Mayer–Vietoris property, then `P` holds on every finite union of members of
`𝔅`. -/
theorem forall_isOpen_of_finite_unions (h𝔅o : ∀ B ∈ 𝔅, IsOpen B)
    (h𝔅i : ∀ B ∈ 𝔅, ∀ B' ∈ 𝔅, B ∩ B' ∈ 𝔅) (hP𝔅 : ∀ B ∈ 𝔅, P B) (hP0 : P ∅)
    (hMV : ∀ U V : Set Z, IsOpen U → IsOpen V → P U → P V → P (U ∩ V) → P (U ∪ V))
    (s : Finset (Set Z)) (hs : (s : Set (Set Z)) ⊆ 𝔅) : P (⋃₀ (s : Set (Set Z))) := by
  classical
  have hopen : ∀ t : Finset (Set Z), (t : Set (Set Z)) ⊆ 𝔅 → IsOpen (⋃₀ (t : Set (Set Z))) :=
    fun t ht ↦ isOpen_sUnion fun B hB ↦ h𝔅o B (ht hB)
  suffices H : ∀ n : ℕ, ∀ t : Finset (Set Z), t.card ≤ n → (t : Set (Set Z)) ⊆ 𝔅 →
      P (⋃₀ (t : Set (Set Z))) from H _ s le_rfl hs
  intro n
  induction n with
  | zero =>
    intro t ht _
    obtain rfl := Finset.card_eq_zero.1 (Nat.le_zero.1 ht)
    simpa using hP0
  | succ n ih =>
    intro t ht ht𝔅
    rcases t.eq_empty_or_nonempty with rfl | ⟨B, hB⟩
    · simpa using hP0
    set t' := t.erase B
    have hcard : t'.card ≤ n := by
      have : t'.card < t.card := Finset.card_erase_lt_of_mem hB
      omega
    have ht'𝔅 : (t' : Set (Set Z)) ⊆ 𝔅 := fun C hC ↦ ht𝔅 (Finset.mem_of_mem_erase hC)
    have hB𝔅 : B ∈ 𝔅 := ht𝔅 hB
    have heq : ⋃₀ (t : Set (Set Z)) = B ∪ ⋃₀ (t' : Set (Set Z)) := by
      rw [← Finset.insert_erase hB, Finset.coe_insert, sUnion_insert]
    set t'' := t'.image (B ∩ ·)
    have ht''𝔅 : (t'' : Set (Set Z)) ⊆ 𝔅 := by
      intro C hC
      simp only [Finset.coe_image, mem_image, t''] at hC
      obtain ⟨D, hD, rfl⟩ := hC
      exact h𝔅i B hB𝔅 D (ht'𝔅 hD)
    have hinter : B ∩ ⋃₀ (t' : Set (Set Z)) = ⋃₀ (t'' : Set (Set Z)) := by
      rw [Finset.coe_image, sUnion_image, sUnion_eq_biUnion, inter_iUnion₂]
    rw [heq]
    refine hMV _ _ (h𝔅o B hB𝔅) (hopen t' ht'𝔅) (hP𝔅 B hB𝔅) (ih t' hcard ht'𝔅) ?_
    rw [hinter]
    exact ih t'' (Finset.card_image_le.trans hcard) ht''𝔅

/-- An exhaustion of an open subset `U` of a locally compact, second-countable space by compact
sets starting at `∅`: `M 0 = ∅`, `M k ⊆ interior (M (k + 1))`, `⋃ k, M k = U`. -/
theorem exists_compact_exhaustion_of_isOpen [LocallyCompactSpace Z] [SecondCountableTopology Z]
    {U : Set Z} (hU : IsOpen U) :
    ∃ M : ℕ → Set Z, M 0 = ∅ ∧ (∀ k, IsCompact (M k)) ∧ (∀ k, M k ⊆ interior (M (k + 1))) ∧
      ⋃ k, M k = U := by
  have : LocallyCompactSpace U := hU.locallyCompactSpace
  let K := CompactExhaustion.choice U
  refine ⟨fun k ↦ Nat.casesOn k ∅ fun k ↦ Subtype.val '' K k, rfl, ?_, ?_, ?_⟩
  · intro k
    cases k with
    | zero => exact isCompact_empty
    | succ k => exact (K.isCompact k).image continuous_subtype_val
  · intro k
    cases k with
    | zero => exact empty_subset _
    | succ k =>
      refine (image_mono (K.subset_interior_succ k)).trans ?_
      exact hU.isOpenMap_subtype_val.image_interior_subset _
  · apply Subset.antisymm
    · refine iUnion_subset fun k ↦ ?_
      cases k with
      | zero => exact empty_subset _
      | succ k => exact Subtype.coe_image_subset _ _
    · intro x hx
      obtain ⟨k, hk⟩ := mem_iUnion.1 (K.iUnion_eq.symm ▸ mem_univ (⟨x, hx⟩ : U))
      exact mem_iUnion.2 ⟨k + 1, ⟨x, hx⟩, hk, rfl⟩

/-- In an exhaustion with `M k ⊆ interior (M (k + 1))`, `M i ⊆ M j` for `i ≤ j`. -/
lemma exhaustion_mono {M : ℕ → Set Z} (hM : ∀ k, M k ⊆ interior (M (k + 1))) {i j : ℕ}
    (hij : i ≤ j) : M i ⊆ M j := by
  induction hij with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans ((hM _).trans interior_subset)

/-- In an exhaustion with `M k ⊆ interior (M (k + 1))`, `M i ⊆ interior (M j)` for `i < j`. -/
lemma exhaustion_subset_interior {M : ℕ → Set Z} (hM : ∀ k, M k ⊆ interior (M (k + 1)))
    {i j : ℕ} (hij : i < j) : M i ⊆ interior (M j) :=
  (hM i).trans (interior_mono (exhaustion_mono hM hij))

/-- If `P` holds on finite unions of members of `𝔅` (as in `forall_isOpen_of_finite_unions`),
it holds on the intersection of two such unions. -/
theorem sUnion_inter_sUnion_of_finite_unions (h𝔅o : ∀ B ∈ 𝔅, IsOpen B)
    (h𝔅i : ∀ B ∈ 𝔅, ∀ B' ∈ 𝔅, B ∩ B' ∈ 𝔅) (hP𝔅 : ∀ B ∈ 𝔅, P B) (hP0 : P ∅)
    (hMV : ∀ U V : Set Z, IsOpen U → IsOpen V → P U → P V → P (U ∩ V) → P (U ∪ V))
    {s s' : Finset (Set Z)} (hs : (s : Set (Set Z)) ⊆ 𝔅) (hs' : (s' : Set (Set Z)) ⊆ 𝔅) :
    P (⋃₀ (s : Set (Set Z)) ∩ ⋃₀ (s' : Set (Set Z))) := by
  classical
  have heq : ⋃₀ (s : Set (Set Z)) ∩ ⋃₀ (s' : Set (Set Z)) =
      ⋃₀ (((s ×ˢ s').image fun p ↦ p.1 ∩ p.2 : Finset (Set Z)) : Set (Set Z)) := by
    simp only [sUnion_inter_sUnion, Finset.coe_image, Finset.coe_product, sUnion_image]
  rw [heq]
  refine forall_isOpen_of_finite_unions h𝔅o h𝔅i hP𝔅 hP0 hMV _ ?_
  intro C hC
  simp only [Finset.coe_image, Finset.coe_product, mem_image, mem_prod] at hC
  obtain ⟨p, ⟨hp1, hp2⟩, rfl⟩ := hC
  exact h𝔅i _ (hs hp1) _ (hs' hp2)

/-- A compact set `A`, each point of which lies in a member of `𝔅` inside `W`, is covered by a
finite union of members of `𝔅` inside `W`. -/
theorem exists_finset_of_isCompact (h𝔅o : ∀ B ∈ 𝔅, IsOpen B) {A W : Set Z} (hA : IsCompact A)
    (hloc : ∀ x ∈ A, ∃ B ∈ 𝔅, x ∈ B ∧ B ⊆ W) :
    ∃ s : Finset (Set Z), (s : Set (Set Z)) ⊆ 𝔅 ∧
      A ⊆ ⋃₀ (s : Set (Set Z)) ∧ ⋃₀ (s : Set (Set Z)) ⊆ W := by
  classical
  choose! B hB𝔅 hxB hBW using hloc
  obtain ⟨t, htA, htfin, htcov⟩ := hA.elim_finite_subcover_image (b := A) (c := B)
    (fun x hx ↦ h𝔅o _ (hB𝔅 x hx)) fun x hx ↦ mem_biUnion hx (hxB x hx)
  refine ⟨htfin.toFinset.image B, ?_, ?_, ?_⟩
  · rw [Finset.coe_image, Finite.coe_toFinset]
    rintro _ ⟨x, hx, rfl⟩
    exact hB𝔅 x (htA hx)
  · rwa [Finset.coe_image, Finite.coe_toFinset, sUnion_image]
  · rw [Finset.coe_image, Finite.coe_toFinset, sUnion_image]
    exact iUnion₂_subset fun x hx ↦ hBW x (htA hx)

/-- If `V n` and `V m` are disjoint whenever `n + 2 ≤ m`, the union of the even `V`s meets the
union of the odd `V`s in `⋃ n, V n ∩ V (n + 1)`. -/
theorem iUnion_even_inter_iUnion_odd {α : Type*} {V : ℕ → Set α}
    (hV : ∀ n m, n + 2 ≤ m → Disjoint (V n) (V m)) :
    (⋃ k, V (2 * k)) ∩ (⋃ k, V (2 * k + 1)) = ⋃ n, V n ∩ V (n + 1) := by
  apply Subset.antisymm
  · rintro x ⟨hx1, hx2⟩
    obtain ⟨k, hk⟩ := mem_iUnion.1 hx1
    obtain ⟨l, hl⟩ := mem_iUnion.1 hx2
    by_cases h1 : 2 * k + 2 ≤ 2 * l + 1
    · exact absurd hl (Set.disjoint_left.1 (hV _ _ h1) hk)
    by_cases h2 : 2 * l + 1 + 2 ≤ 2 * k
    · exact absurd hk (Set.disjoint_left.1 (hV _ _ h2) hl)
    rcases (show l = k ∨ k = l + 1 by omega) with rfl | rfl
    · exact mem_iUnion.2 ⟨2 * l, hk, hl⟩
    · exact mem_iUnion.2 ⟨2 * l + 1, hl, by rwa [show 2 * l + 1 + 1 = 2 * (l + 1) by omega]⟩
  · intro x hx
    obtain ⟨n, hn1, hn2⟩ := mem_iUnion.1 hx
    obtain ⟨k, rfl | rfl⟩ : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := ⟨n / 2, by omega⟩
    · exact ⟨mem_iUnion.2 ⟨k, hn1⟩, mem_iUnion.2 ⟨k, hn2⟩⟩
    · refine ⟨mem_iUnion.2 ⟨k + 1, ?_⟩, mem_iUnion.2 ⟨k, hn1⟩⟩
      rwa [show 2 * (k + 1) = 2 * k + 1 + 1 by omega]

/-- The union of the even and the odd members of a sequence of sets is the union of all of
them. -/
theorem iUnion_even_union_iUnion_odd {α : Type*} (V : ℕ → Set α) :
    (⋃ k, V (2 * k)) ∪ (⋃ k, V (2 * k + 1)) = ⋃ n, V n := by
  refine (union_subset (iUnion_subset fun k ↦ subset_iUnion V _)
    (iUnion_subset fun k ↦ subset_iUnion V _)).antisymm fun x hx ↦ ?_
  obtain ⟨n, hn⟩ := mem_iUnion.1 hx
  obtain ⟨k, rfl | rfl⟩ : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := ⟨n / 2, by omega⟩
  · exact Or.inl (mem_iUnion.2 ⟨k, hn⟩)
  · exact Or.inr (mem_iUnion.2 ⟨k, hn⟩)

/-- If `V n` and `V m` are disjoint whenever `n + 2 ≤ m`, the overlaps `V n ∩ V (n + 1)` are
pairwise disjoint. -/
theorem pairwise_disjoint_inter_succ {α : Type*} {V : ℕ → Set α}
    (hV : ∀ n m, n + 2 ≤ m → Disjoint (V n) (V m)) :
    Pairwise (Disjoint on fun n ↦ V n ∩ V (n + 1)) := by
  refine (pairwise_disjoint_on _).2 fun n m hnm ↦ ?_
  rcases Nat.lt_or_ge (n + 1) m with h | h
  · exact (hV n m (by omega)).mono inter_subset_left inter_subset_left
  · obtain rfl : m = n + 1 := by omega
    exact (hV n (n + 2) le_rfl).mono inter_subset_left inter_subset_right

/-- **Bredon's lemma** (Bredon, VI.7.9). Let `Z` be locally compact and second countable, `𝔅`
a family of open sets stable under binary intersection, and `P` a property of open sets which
holds on `𝔅` and on `∅`, has the Mayer–Vietoris property, and passes to countable disjoint
unions. Then `P U` holds for every open `U` at each point of which `𝔅` is a neighbourhood
basis. -/
theorem isOpen_induction [T2Space Z] [LocallyCompactSpace Z] [SecondCountableTopology Z]
    (h𝔅o : ∀ B ∈ 𝔅, IsOpen B) (h𝔅i : ∀ B ∈ 𝔅, ∀ B' ∈ 𝔅, B ∩ B' ∈ 𝔅)
    (hP𝔅 : ∀ B ∈ 𝔅, P B) (hP0 : P ∅)
    (hMV : ∀ U V : Set Z, IsOpen U → IsOpen V → P U → P V → P (U ∩ V) → P (U ∪ V))
    (hdisj : ∀ U : ℕ → Set Z, (∀ i, IsOpen (U i)) → Pairwise (Disjoint on U) →
      (∀ i, P (U i)) → P (⋃ i, U i))
    {U : Set Z} (hU : IsOpen U) (hU𝔅 : ∀ x ∈ U, ∀ W ∈ 𝓝 x, ∃ B ∈ 𝔅, x ∈ B ∧ B ⊆ W) : P U := by
  classical
  obtain ⟨M, hM0, hMc, hM, hMU⟩ := exists_compact_exhaustion_of_isOpen hU
  -- the compact pieces and their open neighbourhoods
  set A : ℕ → Set Z := fun n ↦ M (2 * n + 2) \ interior (M (2 * n))
  set W : ℕ → Set Z := fun n ↦ interior (M (2 * n + 3)) \ M (2 * n - 1)
  have hAc : ∀ n, IsCompact (A n) := fun n ↦ (hMc _).diff isOpen_interior
  have hWo : ∀ n, IsOpen (W n) := fun n ↦ isOpen_interior.sdiff (hMc _).isClosed
  have hAW : ∀ n, A n ⊆ W n := by
    intro n x ⟨hx1, hx2⟩
    refine ⟨exhaustion_subset_interior hM (by omega) hx1, fun hx3 ↦ hx2 ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hM0] at hx3
    · exact exhaustion_subset_interior hM (by omega) hx3
  have hWU : ∀ n, W n ⊆ U := fun n ↦
    diff_subset.trans (interior_subset.trans (hMU ▸ subset_iUnion M _))
  have hAcov : ∀ x ∈ U, ∃ n, x ∈ A n := by
    intro x hx
    have hex : ∃ k, x ∈ M k := mem_iUnion.1 (hMU.symm ▸ hx)
    set k := Nat.find hex
    have hk : x ∈ M k := Nat.find_spec hex
    have hk0 : k ≠ 0 := fun h ↦ by simp [h, hM0] at hk
    have hk1 : x ∉ M (k - 1) := Nat.find_min hex (by omega)
    refine ⟨(k - 1) / 2, exhaustion_mono hM (by omega) hk, fun h ↦ hk1 ?_⟩
    exact exhaustion_mono hM (by omega) (interior_subset h)
  -- finite unions of members of `𝔅` between `A n` and `W n`
  have hfin : ∀ n, ∃ s : Finset (Set Z), (s : Set (Set Z)) ⊆ 𝔅 ∧
      A n ⊆ ⋃₀ (s : Set (Set Z)) ∧ ⋃₀ (s : Set (Set Z)) ⊆ W n := fun n ↦
    exists_finset_of_isCompact h𝔅o (hAc n) fun x hx ↦
      hU𝔅 x (hWU n (hAW n hx)) (W n) ((hWo n).mem_nhds (hAW n hx))
  choose s hs𝔅 hAs hsW using hfin
  set V : ℕ → Set Z := fun n ↦ ⋃₀ (s n : Set (Set Z))
  have hVo : ∀ n, IsOpen (V n) := fun n ↦ isOpen_sUnion fun B hB ↦ h𝔅o B (hs𝔅 n hB)
  have hVP : ∀ n, P (V n) := fun n ↦
    forall_isOpen_of_finite_unions h𝔅o h𝔅i hP𝔅 hP0 hMV (s n) (hs𝔅 n)
  have hVdisj : ∀ n m, n + 2 ≤ m → Disjoint (V n) (V m) := by
    intro n m hnm
    refine Set.disjoint_left.2 fun x hxn hxm ↦ ?_
    exact (hsW m hxm).2 (exhaustion_mono hM (by omega) (interior_subset (hsW n hxn).1))
  have hVU : ⋃ n, V n = U := by
    refine (iUnion_subset fun n ↦ (hsW n).trans (hWU n)).antisymm fun x hx ↦ ?_
    obtain ⟨n, hn⟩ := hAcov x hx
    exact mem_iUnion.2 ⟨n, hAs n hn⟩
  -- the even, the odd, and the overlapping pieces
  have hPe : P (⋃ k, V (2 * k)) := hdisj _ (fun k ↦ hVo _)
    ((pairwise_disjoint_on _).2 fun k l hkl ↦ hVdisj _ _ (by omega)) fun k ↦ hVP _
  have hPo : P (⋃ k, V (2 * k + 1)) := hdisj _ (fun k ↦ hVo _)
    ((pairwise_disjoint_on _).2 fun k l hkl ↦ hVdisj _ _ (by omega)) fun k ↦ hVP _
  have hPi : P (⋃ n, V n ∩ V (n + 1)) :=
    hdisj _ (fun n ↦ (hVo n).inter (hVo _)) (pairwise_disjoint_inter_succ hVdisj) fun n ↦
      sUnion_inter_sUnion_of_finite_unions h𝔅o h𝔅i hP𝔅 hP0 hMV (hs𝔅 n) (hs𝔅 (n + 1))
  rw [← hVU, ← iUnion_even_union_iUnion_odd]
  refine hMV _ _ (isOpen_iUnion fun k ↦ hVo _) (isOpen_iUnion fun k ↦ hVo _) hPe hPo ?_
  rwa [iUnion_even_inter_iUnion_odd hVdisj]

end Abstract

section ChartedSpace

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {Y : Type*} [TopologicalSpace Y]
  {P : Set Y → Prop}

/-- In an open partial homeomorphism `e : Y → H` into a normed space, the open sets inside
`e.source` with bounded convex image form a neighbourhood basis at every point of `e.source`. -/
theorem exists_convex_image_subset (e : OpenPartialHomeomorph Y H) {x : Y} (hx : x ∈ e.source)
    {W : Set Y} (hW : W ∈ 𝓝 x) :
    ∃ B, (IsOpen B ∧ B ⊆ e.source ∧ Convex ℝ (e '' B) ∧ Bornology.IsBounded (e '' B)) ∧
      x ∈ B ∧ B ⊆ W := by
  have hS : e.target ∩ e.symm ⁻¹' W ∈ 𝓝 (e x) := by
    refine Filter.inter_mem (e.open_target.mem_nhds (e.map_source hx)) ?_
    refine (e.continuousAt_symm (e.map_source hx)).preimage_mem_nhds ?_
    rwa [e.left_inv hx]
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hS
  have hbt : Metric.ball (e x) ε ⊆ e.target := hball.trans inter_subset_left
  have himg : e '' (e.symm '' Metric.ball (e x) ε) = Metric.ball (e x) ε :=
    e.image_symm_image_of_subset_target hbt
  refine ⟨e.symm '' Metric.ball (e x) ε, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [e.symm_image_eq_source_inter_preimage hbt]
    exact e.isOpen_inter_preimage Metric.isOpen_ball
  · rw [e.symm_image_eq_source_inter_preimage hbt]
    exact inter_subset_left
  · rw [himg]
    exact convex_ball _ _
  · rw [himg]
    exact Metric.isBounded_ball
  · exact ⟨e x, Metric.mem_ball_self hε, e.left_inv hx⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact (hball hy).2

variable [T2Space Y] [LocallyCompactSpace Y] [SecondCountableTopology Y]

/-- **Bredon's lemma inside a chart.** If `P` holds on the open sets inside the source of `e`
with bounded convex image, on `∅`, has the Mayer–Vietoris property and passes to countable disjoint
unions, then `P` holds on every open set inside `e.source`. -/
theorem isOpen_induction_chart (e : OpenPartialHomeomorph Y H)
    (hconv : ∀ U, IsOpen U → U ⊆ e.source → Convex ℝ (e '' U) → Bornology.IsBounded (e '' U) →
      P U) (hP0 : P ∅)
    (hMV : ∀ U V : Set Y, IsOpen U → IsOpen V → P U → P V → P (U ∩ V) → P (U ∪ V))
    (hdisj : ∀ U : ℕ → Set Y, (∀ i, IsOpen (U i)) → Pairwise (Disjoint on U) →
      (∀ i, P (U i)) → P (⋃ i, U i))
    {U : Set Y} (hU : IsOpen U) (hUe : U ⊆ e.source) : P U := by
  refine isOpen_induction (𝔅 := {B | IsOpen B ∧ B ⊆ e.source ∧ Convex ℝ (e '' B) ∧
      Bornology.IsBounded (e '' B)})
    (fun B hB ↦ hB.1) ?_ (fun B hB ↦ hconv B hB.1 hB.2.1 hB.2.2.1 hB.2.2.2) hP0 hMV hdisj hU
    fun x hx W hW ↦ exists_convex_image_subset e (hUe hx) hW
  rintro B ⟨hB, hBe, hBc, hBb⟩ B' ⟨hB', hB'e, hB'c, -⟩
  refine ⟨hB.inter hB', inter_subset_left.trans hBe, ?_, hBb.subset (image_mono inter_subset_left)⟩
  rw [e.injOn.image_inter hBe hB'e]
  exact hBc.inter hB'c

/-- **Bredon's lemma on a manifold** (Bredon, VI.7.9). Let `Y` be a Hausdorff, locally compact,
second-countable space modelled on a real normed space `H`, and `P` a property of open subsets
of `Y` which holds on every open set inside a chart domain whose image in the chart is bounded
and convex,
and on `∅`, has the Mayer–Vietoris property (`P U`, `P V`, `P (U ∩ V)` give `P (U ∪ V)`) and
passes to countable disjoint unions. Then `P` holds on every open subset of `Y`. -/
theorem isOpen_induction_chartedSpace [ChartedSpace H Y]
    (hconv : ∀ e ∈ atlas H Y, ∀ U, IsOpen U → U ⊆ e.source → Convex ℝ (e '' U) →
      Bornology.IsBounded (e '' U) → P U)
    (hP0 : P ∅)
    (hMV : ∀ U V : Set Y, IsOpen U → IsOpen V → P U → P V → P (U ∩ V) → P (U ∪ V))
    (hdisj : ∀ U : ℕ → Set Y, (∀ i, IsOpen (U i)) → Pairwise (Disjoint on U) →
      (∀ i, P (U i)) → P (⋃ i, U i))
    {U : Set Y} (hU : IsOpen U) : P U := by
  refine isOpen_induction (𝔅 := {B | IsOpen B ∧ ∃ e ∈ atlas H Y, B ⊆ e.source})
    (fun B hB ↦ hB.1) ?_ ?_ hP0 hMV hdisj hU ?_
  · rintro B ⟨hB, e, he, hBe⟩ B' ⟨hB', -⟩
    exact ⟨hB.inter hB', e, he, inter_subset_left.trans hBe⟩
  · rintro B ⟨hB, e, he, hBe⟩
    exact isOpen_induction_chart e (hconv e he) hP0 hMV hdisj hB hBe
  · intro x _ W hW
    refine ⟨interior W ∩ (chartAt H x).source,
      ⟨isOpen_interior.inter (chartAt H x).open_source, chartAt H x, chart_mem_atlas H x,
        inter_subset_right⟩, ⟨mem_interior_iff_mem_nhds.2 hW, mem_chart_source H x⟩,
      inter_subset_left.trans interior_subset⟩

end ChartedSpace

end MMP
