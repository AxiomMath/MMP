module

public import MMP.AlgebraicTopology.PoincareDuality.Box
public import MMP.AlgebraicTopology.PoincareDuality.Punctured
public import MMP.AlgebraicTopology.PoincareDuality.CompactApprox

/-!
# Relative cycles which bound locally bound on compact sets of `ℝⁿ`

This is Hatcher's Lemma 3.27(b) in `ℝⁿ`, at the chain level: a relative cycle `c` of
`(ℝⁿ, ℝⁿ - K)`, with `K` compact and `c` of degree `m + 1 ≥ n`, which is a relative boundary for
every point `x ∈ K` (its image in `H_{m+1}(ℝⁿ, ℝⁿ - x)` vanishes) is a relative boundary for `K`.

The box step: for `Q` star-shaped about `q` and bounded, a relative cycle for `Q` which is a
relative boundary for `q` is one for `Q`. Write `c = ∂ w + f` with `f` in `E - q`; the radial
homotopy `P` on `E - q` from the inclusion to the radial map `g : E - q → E - Q` keeps `E - Q`
inside `E - Q`, and `f = g_# f - P ∂ f - ∂ P f` with `g_# f - P ∂ f` in `E - Q`, as `∂ f = ∂ c`
lies in `E - Q`.

The compact step: cover `K` by finitely many closed sup-norm balls centred at points of `K` and
avoiding the simplices of `∂ c`; `c` is a relative boundary for each of them by the box step, and
for their union by the Mayer–Vietoris step `isRelBoundary_union`, the local homology of finite
unions of boxes vanishing in degrees `≥ n`.

## Main results

* `MMP.SingularChain.isRelBoundary_of_starConvex`: the box step.
* `MMP.SingularChain.isRelBoundary_of_convex`,
  `MMP.SingularChain.isRelBoundary_Icc`: the box step at any point of a bounded
  convex set, and of a box.
* `MMP.SingularChain.isRelBoundary_sUnion`: finite unions.
* `MMP.SingularChain.isRelBoundary_of_isCompact`: Hatcher, Lemma 3.27(b) for
  compact subsets of `ℝⁿ`.

## References

* [A. Hatcher, *Algebraic Topology*][hatcher2002], §3.3, Lemma 3.27.
-/

@[expose] public noncomputable section

open Finsupp Set

namespace MMP

namespace SingularChain

variable {R : Type*} [CommRing R]

section box

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The box step** (Hatcher, Lemma 3.27(b)): for `Q` star-shaped about `q` and within distance
`D` of `q`, a relative cycle for `Q` which is a relative boundary for `q` is a relative boundary
for `Q`. -/
theorem isRelBoundary_of_starConvex {Q : Set E} {q : E} (hQ : StarConvex ℝ q Q) {D : ℝ}
    (hD0 : 0 ≤ D) (hD : ∀ y ∈ Q, ‖y - q‖ ≤ D) {m : ℕ} {c : Chain R E (m + 1)}
    (hbd : bd R m c ∈ inside R m Qᶜ) (hc : IsRelBoundary R (m + 1) {q} c) :
    IsRelBoundary R (m + 1) Q c := by
  obtain ⟨w, hf⟩ := hc
  set ι := ContinuousMap.subtypeVal ({q}ᶜ : Set E)
  obtain ⟨f', hf'⟩ := exists_postcomp_subtypeVal_eq hf
  have hbf' : bd R m f' ∈ inside R m (ι ⁻¹' Qᶜ) := by
    refine mem_inside_preimage_of_postcomp_mem_inside Subtype.val_injective ?_
    rw [postcomp_bd, hf', map_sub, bd_bd, sub_zero]
    exact hbd
  have hrel := bd_prism_add_prism_bd (R := R) (radialHomotopy q D) (f := ι)
    (g := radialMap q D) (radialHomotopy_zero q D) (radialHomotopy_one q D) m f'
  rw [hf'] at hrel
  refine ⟨w - prism R (radialHomotopy q D) (m + 1) f', ?_⟩
  rw [show c - bd R (m + 1) (w - prism R (radialHomotopy q D) (m + 1) f') =
      postcomp R (radialMap q D) (m + 1) f' - prism R (radialHomotopy q D) m (bd R m f') by
    rw [map_sub, eq_sub_of_add_eq hrel]
    abel]
  exact Submodule.sub_mem _
    (postcomp_mem_inside _ (radialMap_mapsTo hD0 hD) (mem_inside_univ f'))
    (prism_mem_inside _ (radialHomotopy_mapsTo hQ hD0) hbf')

/-- **The box step at any point** of a bounded convex set `Q`: a relative cycle for `Q` which is
a relative boundary for some `x ∈ Q` is a relative boundary for `Q`. -/
theorem isRelBoundary_of_convex {Q : Set E} (hQ : Convex ℝ Q) (hQb : Bornology.IsBounded Q)
    {x : E} (hx : x ∈ Q) {m : ℕ} {c : Chain R E (m + 1)} (hbd : bd R m c ∈ inside R m Qᶜ)
    (hc : IsRelBoundary R (m + 1) {x} c) : IsRelBoundary R (m + 1) Q c := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall x).1 hQb
  refine isRelBoundary_of_starConvex (hQ.starConvex hx) (le_max_right r 0) (fun y hy ↦ ?_) hbd hc
  simpa [dist_eq_norm] using (hr hy).trans (le_max_left r 0)

/-- **The box step for a box** `Q = [a, b]` in `ℝⁿ`, at any of its points. -/
theorem isRelBoundary_Icc {n : ℕ} {a b x : Fin n → ℝ} (hx : x ∈ Icc a b) {m : ℕ}
    {c : Chain R (Fin n → ℝ) (m + 1)} (hbd : bd R m c ∈ inside R m (Icc a b)ᶜ)
    (hc : IsRelBoundary R (m + 1) {x} c) : IsRelBoundary R (m + 1) (Icc a b) c :=
  isRelBoundary_of_convex (convex_Icc a b) (Metric.isBounded_Icc a b) hx hbd hc

end box

section sUnion

variable {Y : Type*} [TopologicalSpace Y]

/-- **Finite unions.** For a family `𝔅` of closed sets stable under intersection whose finite
unions `L` satisfy `H_{m+1}(Y, Y - L) = 0`, a chain which is a relative boundary for each member
of a finite subfamily is a relative boundary for its union. -/
theorem isRelBoundary_sUnion {𝔅 : Set (Set Y)} (hclosed : ∀ B ∈ 𝔅, IsClosed B)
    (hinter : ∀ B ∈ 𝔅, ∀ B' ∈ 𝔅, B ∩ B' ∈ 𝔅) {m : ℕ}
    (hvan : ∀ s : Finset (Set Y), ↑s ⊆ 𝔅 → RelVanishing R Y m (⋃₀ (s : Set (Set Y))))
    {c : Chain R Y m} (s : Finset (Set Y)) (hs : ↑s ⊆ 𝔅) (hc : ∀ B ∈ s, IsRelBoundary R m B c) :
    IsRelBoundary R m (⋃₀ (s : Set (Set Y))) c := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.coe_empty, sUnion_empty]
    exact isRelBoundary_of_mem_inside (by simpa using mem_inside_univ c)
  | insert B s hBs ih =>
    have hB𝔅 : B ∈ 𝔅 := hs (by simp)
    have hsub : ↑s ⊆ 𝔅 := fun x hx ↦ hs (by simp [Finset.mem_coe.1 hx])
    have himg : ↑(s.image (B ∩ ·)) ⊆ 𝔅 := by
      intro x hx
      rw [Finset.coe_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact hinter B hB𝔅 y (hsub hy)
    have hclosedU : IsClosed (⋃₀ (s : Set (Set Y))) := by
      rw [sUnion_eq_biUnion]
      exact isClosed_biUnion_finset fun t ht ↦ hclosed t (hsub ht)
    have heq : B ∩ ⋃₀ (s : Set (Set Y)) =
        ⋃₀ ((s.image (B ∩ ·) : Finset (Set Y)) : Set (Set Y)) := by
      rw [Finset.coe_image, sUnion_image, sUnion_eq_biUnion, inter_iUnion₂]
    rw [Finset.coe_insert, sUnion_insert]
    refine isRelBoundary_union (hclosed B hB𝔅) hclosedU ?_ (hc B (by simp))
      (ih hsub fun B' hB' ↦ hc B' (by simp [hB']))
    rw [heq]
    exact hvan _ himg

end sUnion

section compact

/-- A closed sup-norm ball of `ℝⁿ` is a box. -/
lemma closedBall_eq_Icc_sub_add {ι : Type*} [Fintype ι] (x : ι → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    Metric.closedBall x r = Icc (x - fun _ ↦ r) (x + fun _ ↦ r) := by
  rw [closedBall_pi x hr, ← pi_univ_Icc]
  simp [Real.closedBall_eq_Icc]

/-- **Hatcher, Lemma 3.27(b), in `ℝⁿ`**: for `K ⊆ ℝⁿ` compact, an `(m+1)`-chain `c` with
`m + 1 ≥ n` and boundary in `ℝⁿ - K` which is a relative boundary for every point of `K` is a
relative boundary for `K`. -/
theorem isRelBoundary_of_isCompact {n m : ℕ} (hn : n ≤ m + 1) {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) {c : Chain R (Fin n → ℝ) (m + 1)} (hbd : bd R m c ∈ inside R m Kᶜ)
    (hpt : ∀ x ∈ K, IsRelBoundary R (m + 1) {x} c) : IsRelBoundary R (m + 1) K c := by
  classical
  set 𝔅 : Set (Set (Fin n → ℝ)) := {B | ∃ a b, B = Icc a b}
  have hclosed : ∀ B ∈ 𝔅, IsClosed B := by
    rintro B ⟨a, b, rfl⟩
    exact isClosed_Icc
  have hinter : ∀ B ∈ 𝔅, ∀ B' ∈ 𝔅, B ∩ B' ∈ 𝔅 := by
    rintro B ⟨a, b, rfl⟩ B' ⟨a', b', rfl⟩
    exact ⟨a ⊔ a', b ⊓ b', Icc_inter_Icc⟩
  have hbase : ∀ B ∈ 𝔅, ∀ k, m + 1 ≤ k → RelVanishing R (Fin n → ℝ) k B := by
    rintro B ⟨a, b, rfl⟩ k hk
    exact relVanishing_Icc cycleVanishing_compl_zero n a b k (hn.trans hk)
  -- the union of the images of the simplices of `∂ c`
  set T : Set (Fin n → ℝ) := ⋃ τ ∈ (bd R m c).support, range τ
  have hT : IsClosed T :=
    ((bd R m c).support.isCompact_biUnion fun τ _ ↦
      isCompact_range τ.continuous).isClosed
  have hKT : K ⊆ Tᶜ := by
    intro x hx hxT
    obtain ⟨τ, hτ, hxτ⟩ := mem_iUnion₂.1 hxT
    exact (mem_supported R _ |>.1 hbd hτ) hxτ hx
  have hδ : ∀ x ∈ K, ∃ ε > 0, Metric.closedBall x ε ⊆ Tᶜ := fun x hx ↦
    Metric.nhds_basis_closedBall.mem_iff.1 (hT.isOpen_compl.mem_nhds (hKT hx))
  choose! δ hδpos hδT using hδ
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover (fun x ↦ Metric.closedBall x (δ x))
    fun x hx ↦ Metric.closedBall_mem_nhds x (hδpos x hx)
  set s : Finset (Set (Fin n → ℝ)) := t.image fun x ↦ Metric.closedBall x (δ x)
  have hs𝔅 : ↑s ⊆ 𝔅 := by
    intro B hB
    rw [Finset.coe_image] at hB
    obtain ⟨x, hx, rfl⟩ := hB
    exact ⟨_, _, closedBall_eq_Icc_sub_add x (hδpos x (htK x hx)).le⟩
  have hbox : ∀ B ∈ s, IsRelBoundary R (m + 1) B c := by
    intro B hB
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hB
    have hxK : x ∈ K := htK x hx
    exact isRelBoundary_of_convex (convex_closedBall x (δ x)) Metric.isBounded_closedBall
      (Metric.mem_closedBall_self (hδpos x hxK).le)
      ((mem_supported R _).2 fun τ hτ y hy hyB ↦ hδT x hxK hyB (mem_iUnion₂.2 ⟨τ, hτ, hy⟩))
      (hpt x hxK)
  have hL := isRelBoundary_sUnion hclosed hinter
    (fun s hs ↦ relVanishing_sUnion hclosed hinter hbase s hs (m + 1) le_rfl) s hs𝔅 hbox
  refine hL.mono ?_
  rw [Finset.coe_image, sUnion_image]
  exact hcover

end compact

end SingularChain

end MMP
