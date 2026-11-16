module

public import MMP.AlgebraicTopology.PoincareDuality.Localize
public import MMP.AlgebraicTopology.PoincareDuality.Homotopy
public import MMP.AlgebraicTopology.PoincareDuality.CompactApprox

/-!
# Local homology of `ℝⁿ` at a closed box

In the finite chain model of `MMP.AlgebraicTopology.SingularHomology.Excision.SmallChains`,
the local homology `H_{k+1}(ℝⁿ, ℝⁿ - Q; R)` of `ℝⁿ = Fin n → ℝ` at a closed box `Q = Set.Icc a c`
vanishes for `k ≥ n`, given that `H_{j+1}(ℝⁿ - 0; R)` vanishes for `j + 1 ≥ n`.

* For `Q` star-shaped about `q ∈ Q` and bounded, `ℝⁿ - Q` is a deformation retract up to
  homotopy of `ℝⁿ - q`: the radial map `x ↦ x + (D / ‖x - q‖) (x - q)` pushes `ℝⁿ - q` into
  `ℝⁿ - Q`, and the straight-line homotopy from the inclusion to it keeps `ℝⁿ - Q` inside
  `ℝⁿ - Q`, since the points beyond `x` on the ray from `q` through `x` avoid `Q`. Hence the
  vanishing of `H_{j+1}(ℝⁿ - q)` gives that of `H_{j+1}(ℝⁿ - Q)`.
* `ℝⁿ` is star-shaped, so by the long exact sequence of the pair (at the chain level,
  `exists_bd_add_of_starConvex`) `H_{k+1}(ℝⁿ, ℝⁿ - Q) = 0` once `H_k(ℝⁿ - Q) = 0`.

## Main results

* `MMP.SingularChain.cycleVanishing_compl_of_starConvex`: the radial retraction.
* `MMP.SingularChain.cycleVanishing_compl_Icc`: the case of a box.
* `MMP.SingularChain.relVanishing_Icc_of_cycleVanishing`: the long exact sequence
  step.
* `MMP.SingularChain.relVanishing_Icc`: the vanishing of the local homology at a
  box above degree `n`.

## References

* [A. Hatcher, *Algebraic Topology*][hatcher2002], §3.3, Lemma 3.27.
-/

@[expose] public noncomputable section

open Finsupp Set

namespace MMP

namespace SingularChain

variable {R : Type*} [CommRing R]

section radial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The straight-line homotopy on `E - q` from the inclusion to the radial map
`x ↦ x + (D / ‖x - q‖) (x - q)`: `(x, t) ↦ x + (t D / ‖x - q‖) (x - q)`. -/
def radialHomotopy (q : E) (D : ℝ) : C((({q}ᶜ : Set E)) × unitInterval, E) where
  toFun p := (p.1 : E) + ((p.2 : ℝ) * (D / ‖(p.1 : E) - q‖)) • ((p.1 : E) - q)
  continuous_toFun := by
    have h1 : Continuous fun p : (({q}ᶜ : Set E)) × unitInterval ↦ (p.1 : E) :=
      continuous_subtype_val.comp continuous_fst
    have h2 : Continuous fun p : (({q}ᶜ : Set E)) × unitInterval ↦ (p.2 : ℝ) :=
      continuous_subtype_val.comp continuous_snd
    have h3 : Continuous fun p : (({q}ᶜ : Set E)) × unitInterval ↦ D / ‖(p.1 : E) - q‖ :=
      continuous_const.div (continuous_norm.comp (h1.sub continuous_const)) fun p ↦
        norm_ne_zero_iff.2 (sub_ne_zero.2 p.1.2)
    exact h1.add ((h2.mul h3).smul (h1.sub continuous_const))

/-- The value of the radial homotopy at `(x, t)` is `x + (t D / ‖x - q‖) (x - q)`. -/
lemma radialHomotopy_apply (q : E) (D : ℝ) (x : ({q}ᶜ : Set E)) (t : unitInterval) :
    radialHomotopy q D (x, t) = (x : E) + ((t : ℝ) * (D / ‖(x : E) - q‖)) • ((x : E) - q) :=
  rfl

/-- The radial map `x ↦ x + (D / ‖x - q‖) (x - q)` on `E - q`. -/
def radialMap (q : E) (D : ℝ) : C(({q}ᶜ : Set E), E) :=
  (radialHomotopy q D).comp ((ContinuousMap.id _).prodMk (ContinuousMap.const _ 1))

/-- At time `0` the radial homotopy is the inclusion of `E - q` into `E`. -/
lemma radialHomotopy_zero (q : E) (D : ℝ) (x : ({q}ᶜ : Set E)) :
    radialHomotopy q D (x, 0) = ContinuousMap.subtypeVal _ x := by
  simp [radialHomotopy_apply]

/-- At time `1` the radial homotopy is the radial map. -/
lemma radialHomotopy_one (q : E) (D : ℝ) (x : ({q}ᶜ : Set E)) :
    radialHomotopy q D (x, 1) = radialMap q D x :=
  rfl

/-- The point `q + s (x - q)` with `s ≥ 1` lies outside a set `Q` star-shaped about `q` that does
not contain `x`. -/
lemma add_smul_sub_notMem_of_starConvex {Q : Set E} {q x : E} (hQ : StarConvex ℝ q Q)
    (hx : x ∉ Q) {s : ℝ} (hs : 1 ≤ s) : q + s • (x - q) ∉ Q := by
  intro hmem
  have heq : (1 - s⁻¹) • q + s⁻¹ • (q + s • (x - q)) = x := by
    rw [smul_add, smul_smul, inv_mul_cancel₀ (by positivity), one_smul, sub_smul, one_smul]
    abel
  exact hx (heq ▸ hQ hmem (sub_nonneg.2 (inv_le_one_of_one_le₀ hs)) (by positivity)
    (sub_add_cancel 1 s⁻¹))

/-- The radial homotopy keeps `E - Q` inside `E - Q`, for `Q` star-shaped about `q`. -/
lemma radialHomotopy_mapsTo {Q : Set E} {q : E} (hQ : StarConvex ℝ q Q) {D : ℝ} (hD0 : 0 ≤ D) :
    MapsTo (radialHomotopy q D) ((ContinuousMap.subtypeVal ({q}ᶜ : Set E) ⁻¹' Qᶜ) ×ˢ univ)
      Qᶜ := by
  rintro ⟨x, t⟩ ⟨hx, -⟩
  have heq : radialHomotopy q D (x, t) =
      q + (1 + (t : ℝ) * (D / ‖(x : E) - q‖)) • ((x : E) - q) := by
    rw [radialHomotopy_apply, add_smul, one_smul]
    abel
  rw [mem_compl_iff, heq]
  exact add_smul_sub_notMem_of_starConvex hQ hx
    (le_add_of_nonneg_right (mul_nonneg t.2.1 (div_nonneg hD0 (norm_nonneg _))))

/-- The radial map sends `E - q` into `E - Q`, for `Q` within distance `D` of `q`. -/
lemma radialMap_mapsTo {Q : Set E} {q : E} {D : ℝ} (hD0 : 0 ≤ D) (hD : ∀ y ∈ Q, ‖y - q‖ ≤ D) :
    MapsTo (radialMap q D) univ Qᶜ := by
  intro x _ hmem
  have hr : 0 < ‖(x : E) - q‖ := norm_pos_iff.2 (sub_ne_zero.2 x.2)
  have hgx : radialMap q D x - q = (1 + D / ‖(x : E) - q‖) • ((x : E) - q) := by
    rw [← radialHomotopy_one, radialHomotopy_apply, Set.Icc.coe_one, one_mul, add_smul,
      one_smul]
    abel
  have hnorm : ‖radialMap q D x - q‖ = ‖(x : E) - q‖ + D := by
    rw [hgx, norm_smul, Real.norm_of_nonneg (by positivity), add_mul, one_mul,
      div_mul_cancel₀ _ hr.ne']
  linarith [hD _ hmem]

/-- **Radial retraction.** For `Q` star-shaped about `q ∈ Q` and within distance `D` of `q`,
the vanishing of `H_{j+1}(E - q)` gives the vanishing of `H_{j+1}(E - Q)`. -/
theorem cycleVanishing_compl_of_starConvex {Q : Set E} {q : E} (hq : q ∈ Q)
    (hQ : StarConvex ℝ q Q) {D : ℝ} (hD0 : 0 ≤ D) (hD : ∀ y ∈ Q, ‖y - q‖ ≤ D) {j : ℕ}
    (h : CycleVanishing R E j {q}ᶜ) : CycleVanishing R E j Qᶜ := by
  intro z hz hbz
  have hzq : z ∈ inside R (j + 1) ({q}ᶜ : Set E) :=
    inside_mono _ (compl_subset_compl.2 (singleton_subset_iff.2 hq)) hz
  obtain ⟨w, hw, hbw⟩ := h z hzq hbz
  set ι := ContinuousMap.subtypeVal ({q}ᶜ : Set E)
  have hinj : ∀ n, Function.Injective (postcomp R ι n) :=
    postcomp_injective Subtype.val_injective
  obtain ⟨z', rfl⟩ := exists_postcomp_subtypeVal_eq hzq
  obtain ⟨w', rfl⟩ := exists_postcomp_subtypeVal_eq hw
  have hbw' : bd R (j + 1) w' = z' := hinj (j + 1) (by rw [postcomp_bd, hbw])
  have hbz' : bd R j z' = 0 := hinj j (by rw [postcomp_bd, hbz, map_zero])
  have hz'Q : z' ∈ inside R (j + 1) (ι ⁻¹' Qᶜ) :=
    mem_inside_preimage_of_postcomp_mem_inside Subtype.val_injective hz
  have hrel := bd_prism_add_prism_bd (R := R) (radialHomotopy q D) (f := ι)
    (g := radialMap q D) (radialHomotopy_zero q D) (radialHomotopy_one q D) j z'
  rw [hbz', map_zero, add_zero] at hrel
  refine ⟨postcomp R (radialMap q D) (j + 2) w' - prism R (radialHomotopy q D) (j + 1) z',
    Submodule.sub_mem _ (postcomp_mem_inside _ (radialMap_mapsTo hD0 hD) (mem_inside_univ w'))
      (prism_mem_inside _ (radialHomotopy_mapsTo hQ hD0) hz'Q), ?_⟩
  rw [map_sub, ← postcomp_bd, hbw', hrel]
  change _ = postcomp R ι (j + 1) z'
  abel

end radial

section box

/-- In `ℝ⁰` every box is everything. -/
lemma Icc_eq_univ_of_fin_zero (a c : Fin 0 → ℝ) : Icc a c = univ :=
  eq_univ_of_forall fun _ ↦ ⟨fun i ↦ i.elim0, fun i ↦ i.elim0⟩

/-- A point `y` of the box `[a, c]` in `ℝⁿ` satisfies `‖y - a‖ ≤ ‖c - a‖` in the sup norm. -/
lemma norm_sub_le_of_mem_Icc {n : ℕ} {a c y : Fin n → ℝ} (hy : y ∈ Icc a c) :
    ‖y - a‖ ≤ ‖c - a‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i ↦ ?_
  have h1 : ‖(y - a) i‖ ≤ ‖(c - a) i‖ := by
    rw [Pi.sub_apply, Pi.sub_apply, Real.norm_of_nonneg (sub_nonneg.2 (hy.1 i)),
      Real.norm_of_nonneg (sub_nonneg.2 ((hy.1 i).trans (hy.2 i)))]
    linarith [hy.2 i]
  exact h1.trans (norm_le_pi_norm (c - a) i)

/-- **The complement of a box.** For a nonempty box `Q = [a, c]` in `ℝⁿ`, the vanishing of
`H_{j+1}(ℝⁿ - 0)` gives the vanishing of `H_{j+1}(ℝⁿ - Q)`. -/
theorem cycleVanishing_compl_Icc {n : ℕ} {a c : Fin n → ℝ} (hac : (Icc a c).Nonempty) {j : ℕ}
    (h : CycleVanishing R (Fin n → ℝ) j {0}ᶜ) : CycleVanishing R (Fin n → ℝ) j (Icc a c)ᶜ := by
  have ha : a ∈ Icc a c := left_mem_Icc.2 (nonempty_Icc.1 hac)
  have ht := h.of_homeomorph (Homeomorph.addRight a)
  rw [image_compl_eq (Homeomorph.addRight a).bijective, image_singleton] at ht
  simp only [Homeomorph.coe_addRight, zero_add] at ht
  exact cycleVanishing_compl_of_starConvex ha ((convex_Icc a c).starConvex ha) (norm_nonneg _)
    (fun y hy ↦ norm_sub_le_of_mem_Icc hy) ht

/-- The only chain supported in the empty set is `0`. -/
lemma eq_zero_of_mem_inside_empty_set {Y : Type*} [TopologicalSpace Y] {n : ℕ} {c : Chain R Y n}
    (hc : c ∈ inside R n (∅ : Set Y)) : c = 0 := by
  by_contra h0
  exact not_nonempty_empty (nonempty_of_mem_inside hc h0)

/-- **Long exact sequence step for a box.** If `H_{j+1}(ℝⁿ - Q) = 0` for every `j + 1 ≥ n`,
then `H_{k+1}(ℝⁿ, ℝⁿ - Q) = 0` for every `k ≥ n`. -/
theorem relVanishing_Icc_of_cycleVanishing {n : ℕ} {a c : Fin n → ℝ}
    (h : ∀ j, n ≤ j + 1 → CycleVanishing R (Fin n → ℝ) j (Icc a c)ᶜ) :
    ∀ k, n ≤ k → RelVanishing R (Fin n → ℝ) k (Icc a c) := by
  rintro (_ | j) hk γ hγ
  · obtain rfl : n = 0 := Nat.le_zero.1 hk
    have hQ : (Icc a c)ᶜ = ∅ := by rw [Icc_eq_univ_of_fin_zero, compl_univ]
    obtain ⟨w, -, f, hf, hγw⟩ := exists_bd_add_of_starConvex_zero (R := R)
      (starConvex_univ (0 : Fin 0 → ℝ)) (subset_univ (Icc a c)ᶜ)
      (fun z hz _ ↦ by
        rw [hQ] at hz
        exact ⟨0, Submodule.zero_mem _, by rw [map_zero, eq_zero_of_mem_inside_empty_set hz]⟩)
      (mem_inside_univ γ) hγ
    exact ⟨w, by rwa [hγw, add_sub_cancel_left]⟩
  · obtain ⟨w, -, f, hf, hγw⟩ := exists_bd_add_of_starConvex (R := R)
      (starConvex_univ (0 : Fin n → ℝ)) (subset_univ (Icc a c)ᶜ) (m := j) (h j hk)
      (mem_inside_univ γ) hγ
    exact ⟨w, by rwa [hγw, add_sub_cancel_left]⟩

/-- **Local homology of `ℝⁿ` at a box.** Given the vanishing of `H_{j+1}(ℝⁿ - 0)` for
`j + 1 ≥ n ≥ 1`, the local homology `H_{k+1}(ℝⁿ, ℝⁿ - Q)` at every closed box `Q = [a, c]`
vanishes for `k ≥ n`. -/
theorem relVanishing_Icc
    (hpunct : ∀ n, 1 ≤ n → ∀ j, n ≤ j + 1 → CycleVanishing R (Fin n → ℝ) j {0}ᶜ) :
    ∀ (n : ℕ) (a c : Fin n → ℝ) (k : ℕ), n ≤ k → RelVanishing R (Fin n → ℝ) k (Icc a c) := by
  intro n a c k hk
  rcases (Icc a c).eq_empty_or_nonempty with hQ | hQ
  · rw [hQ]
    exact relVanishing_empty k
  refine relVanishing_Icc_of_cycleVanishing (fun j hj ↦ ?_) k hk
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Icc_eq_univ_of_fin_zero, compl_univ]
    exact fun z hz _ ↦ ⟨0, Submodule.zero_mem _, by
      rw [map_zero, eq_zero_of_mem_inside_empty_set hz]⟩
  · exact cycleVanishing_compl_Icc hQ (hpunct n hn j hj)

end box

end SingularChain

end MMP
