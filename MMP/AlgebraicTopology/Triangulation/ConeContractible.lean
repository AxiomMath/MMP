module

public import Mathlib.Topology.Homotopy.LocallyContractible
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.UnitInterval

/-!
# Balls with a conic structure are contractible

Let `X` be a metric space, `p ∈ X` and `ε > 0`. Suppose the punctured ball `B(p, ε) ∖ {p}` is
trivialised by the distance to `p`: there are a set `L` (the *link*) in a space `F`, a map
`Φ : L × (0, ε) → X`, continuous, with `d(Φ(y, t), p) = t`, and a continuous map
`ρ : B(p, ε) ∖ {p} → L` with `Φ(ρ(x), d(x, p)) = x`. Then `B(p, ε)` is, morally, the open cone
over `L`; in particular it is contractible: `H(s, x) = Φ(ρ(x), (1 - s) d(x, p))` for `x ≠ p`,
`s < 1`, and `H = p` otherwise, is a homotopy from the identity to the constant map, continuous at
the vertex since `d(H(s, x), p) ≤ (1 - s) d(x, p)`.

If every point has such a conic structure, then every smaller ball about it has one too, so the
space has a basis of contractible open neighbourhoods.

## Main results

* `MMP.contractibleSpace_ball_of_conic`: a ball with a conic structure is
  contractible.
* `MMP.hasBasis_contractible_of_conic`: if every point has a ball with a conic
  structure, the contractible open neighbourhoods of each point form a basis.
* `MMP.stronglyLocallyContractibleSpace_of_conic`: such a space is strongly
  locally contractible.

## References

* [J. Milnor, *Singular points of complex hypersurfaces*][milnor1968], Theorem 2.10.
-/

@[expose] public section

open Set Topology Filter Metric unitInterval

namespace MMP

variable {X F : Type*} [MetricSpace X] [TopologicalSpace F]

/-- **A ball with a conic structure is contractible.** If `Φ : L × (0, ε) → X` is continuous
with `d(Φ(y, t), p) = t`, and `ρ : B(p, ε) ∖ {p} → L` is continuous with `Φ(ρ(x), d(x, p)) = x`,
then `B(p, ε)` is contractible. -/
theorem contractibleSpace_ball_of_conic {p : X} {ε : ℝ} (hε : 0 < ε) {L : Set F}
    (Φ : F × ℝ → X) (ρ : X → F) (hΦ : ContinuousOn Φ (L ×ˢ Ioo 0 ε))
    (hΦd : ∀ y ∈ L, ∀ t ∈ Ioo 0 ε, dist (Φ (y, t)) p = t)
    (hρ : ContinuousOn ρ (ball p ε \ {p})) (hρL : MapsTo ρ (ball p ε \ {p}) L)
    (hΦρ : ∀ x ∈ ball p ε \ {p}, Φ (ρ x, dist x p) = x) :
    ContractibleSpace (ball p ε) := by
  classical
  let p' : ball p ε := ⟨p, mem_ball_self hε⟩
  let O : Set (I × ball p ε) := {w | (w.1 : ℝ) < 1 ∧ (w.2 : X) ≠ p}
  let k : I × ball p ε → X := fun w ↦ Φ (ρ w.2, (1 - w.1) * dist (w.2 : X) p)
  let g : I × ball p ε → X := fun w ↦ if w ∈ O then k w else p
  have hpunct : ∀ w : I × ball p ε, (w.2 : X) ≠ p → (w.2 : X) ∈ ball p ε \ {p} :=
    fun w hw ↦ ⟨w.2.2, hw⟩
  have hlt : ∀ w : I × ball p ε, (1 - (w.1 : ℝ)) * dist (w.2 : X) p < ε := fun w ↦
    (mul_le_of_le_one_left dist_nonneg (by linarith [w.1.2.1])).trans_lt w.2.2
  have hIoo : ∀ w ∈ O, (1 - (w.1 : ℝ)) * dist (w.2 : X) p ∈ Ioo 0 ε := fun w hw ↦
    ⟨mul_pos (sub_pos.2 hw.1) (dist_pos.2 hw.2), hlt w⟩
  have hdist : ∀ w, dist (g w) p ≤ (1 - (w.1 : ℝ)) * dist (w.2 : X) p := by
    intro w
    by_cases hw : w ∈ O
    · simp only [g, hw, ↓reduceIte, k]
      rw [hΦd _ (hρL (hpunct w hw.2)) _ (hIoo w hw)]
    · simp only [g, hw, ↓reduceIte, dist_self]
      exact mul_nonneg (by linarith [w.1.2.2]) dist_nonneg
  have hmem : ∀ w, g w ∈ ball p ε := fun w ↦ (hdist w).trans_lt (hlt w)
  have hO : IsOpen O := by
    refine (isOpen_lt (by fun_prop : Continuous fun w : I × ball p ε ↦ (w.1 : ℝ))
      continuous_const).inter ?_
    exact isOpen_ne_fun (by fun_prop : Continuous fun w : I × ball p ε ↦ (w.2 : X))
      continuous_const
  have hk : ContinuousOn k O := by
    refine hΦ.comp (ContinuousOn.prodMk ?_ ?_) fun w hw ↦ ⟨hρL (hpunct w hw.2), hIoo w hw⟩
    · exact hρ.comp (by fun_prop : Continuous fun w : I × ball p ε ↦ (w.2 : X)).continuousOn
        fun w hw ↦ hpunct w hw.2
    · exact (by fun_prop : Continuous fun w : I × ball p ε ↦
        (1 - (w.1 : ℝ)) * dist (w.2 : X) p).continuousOn
  have hg : Continuous g := by
    refine continuous_iff_continuousAt.2 fun z ↦ ?_
    by_cases hz : z ∈ O
    · refine (hk.continuousAt (hO.mem_nhds hz)).congr ?_
      filter_upwards [hO.mem_nhds hz] with w hw
      simp only [g, hw, ↓reduceIte]
    · have hgz : g z = p := by simp only [g, hz, ↓reduceIte]
      have h0 : (1 - (z.1 : ℝ)) * dist (z.2 : X) p = 0 := by
        simp only [O, mem_ofPred_eq, not_and_or, not_lt, not_not] at hz
        rcases hz with h | h
        · rw [show (z.1 : ℝ) = 1 from le_antisymm z.1.2.2 h, sub_self, zero_mul]
        · rw [h, dist_self, mul_zero]
      rw [ContinuousAt, hgz, tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun w ↦ dist_nonneg) hdist ?_
      rw [← h0]
      exact (by fun_prop : Continuous fun w : I × ball p ε ↦
        (1 - (w.1 : ℝ)) * dist (w.2 : X) p).continuousAt
  rw [contractible_iff_id_nullhomotopic]
  refine ⟨p', ⟨{
    toFun := fun w ↦ ⟨g w, hmem w⟩
    continuous_toFun := hg.subtype_mk _
    map_zero_left := fun x ↦ ?_
    map_one_left := fun x ↦ ?_ }⟩⟩
  · apply Subtype.ext
    by_cases hx : (x : X) = p
    · have : (0, x) ∉ O := fun h ↦ h.2 hx
      simp only [g, this, ↓reduceIte, ContinuousMap.id_apply]
      exact hx.symm
    · have : (0, x) ∈ O := ⟨by simp, hx⟩
      simp only [g, this, ↓reduceIte, k, ContinuousMap.id_apply, Icc.coe_zero, sub_zero, one_mul]
      exact hΦρ x ⟨x.2, hx⟩
  · apply Subtype.ext
    have : ((1 : I), x) ∉ O := fun h ↦ absurd h.1 (by simp)
    change (if ((1 : I), x) ∈ O then k ((1 : I), x) else p) = p
    simp only [this, ↓reduceIte]

/-- **Conic structures give a basis of contractible open neighbourhoods.** If the ball
`B(p, ε₀)` has a conic structure (`contractibleSpace_ball_of_conic`), then the contractible
open neighbourhoods of `p` form a basis of its neighbourhoods. -/
theorem hasBasis_contractible_of_conic {p : X} {ε₀ : ℝ} (hε₀ : 0 < ε₀) {L : Set F}
    (Φ : F × ℝ → X) (ρ : X → F) (hΦ : ContinuousOn Φ (L ×ˢ Ioo 0 ε₀))
    (hΦd : ∀ y ∈ L, ∀ t ∈ Ioo 0 ε₀, dist (Φ (y, t)) p = t)
    (hρ : ContinuousOn ρ (ball p ε₀ \ {p})) (hρL : MapsTo ρ (ball p ε₀ \ {p}) L)
    (hΦρ : ∀ x ∈ ball p ε₀ \ {p}, Φ (ρ x, dist x p) = x) :
    (𝓝 p).HasBasis (fun s : Set X ↦ IsOpen s ∧ p ∈ s ∧ ContractibleSpace s) id := by
  refine ⟨fun t ↦ ⟨fun ht ↦ ?_, fun ⟨s, ⟨hs, hps, _⟩, hst⟩ ↦
    mem_of_superset (hs.mem_nhds hps) hst⟩⟩
  obtain ⟨ε, hε, hεt⟩ := Metric.mem_nhds_iff.1 ht
  set δ := min ε ε₀
  have hδ : 0 < δ := lt_min hε hε₀
  have hsub : ball p δ \ {p} ⊆ ball p ε₀ \ {p} :=
    sdiff_subset_sdiff_left (ball_subset_ball (min_le_right _ _))
  have hIoo : Ioo 0 δ ⊆ Ioo 0 ε₀ := Ioo_subset_Ioo_right (min_le_right _ _)
  refine ⟨ball p δ, ⟨isOpen_ball, mem_ball_self hδ, ?_⟩,
    (ball_subset_ball (min_le_left _ _)).trans hεt⟩
  exact contractibleSpace_ball_of_conic hδ Φ ρ (hΦ.mono (prod_mono subset_rfl hIoo))
    (fun y hy t ht ↦ hΦd y hy t (hIoo ht)) (hρ.mono hsub) (hρL.mono_left hsub)
    fun x hx ↦ hΦρ x (hsub hx)

/-- A metric space in which every point has a ball with a conic structure is strongly locally
contractible. -/
theorem stronglyLocallyContractibleSpace_of_conic
    (h : ∀ p : X, ∃ ε > 0, ∃ (L : Set F) (Φ : F × ℝ → X) (ρ : X → F),
      ContinuousOn Φ (L ×ˢ Ioo 0 ε) ∧ (∀ y ∈ L, ∀ t ∈ Ioo 0 ε, dist (Φ (y, t)) p = t) ∧
      ContinuousOn ρ (ball p ε \ {p}) ∧ MapsTo ρ (ball p ε \ {p}) L ∧
      ∀ x ∈ ball p ε \ {p}, Φ (ρ x, dist x p) = x) :
    StronglyLocallyContractibleSpace X :=
  .of_bases (p := fun p s ↦ IsOpen s ∧ p ∈ s ∧ ContractibleSpace s) (s := fun _ ↦ id)
    (fun p ↦ by
      obtain ⟨ε, hε, L, Φ, ρ, hΦ, hΦd, hρ, hρL, hΦρ⟩ := h p
      exact hasBasis_contractible_of_conic hε Φ ρ hΦ hΦd hρ hρL hΦρ)
    fun _ _ h ↦ h.2.2

end MMP
