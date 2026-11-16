module

public import MMP.AlgebraicTopology.ProperNeighbourhoodRetract.Basic
public import Mathlib.Topology.UnitInterval

/-!
# A proper homotopy from the identity to the retraction

Let `Y` have a closed imbedding in `ℝᴺ`, with `Y` locally contractible, and `X ⊆ Y` closed and
locally contractible. Inside any neighbourhood `M` of `X` there is a closed neighbourhood `N` of
`X` with a proper retraction `r : N → X` and a proper homotopy `G : N × [0, 1] → Y`, with values
in `M`, from the inclusion to `r`, fixing `X`: `G(y, t) = ρ((1 - t) y + t r(y))`, where `ρ` is a
retraction of a neighbourhood of `Y` in `ℝᴺ` onto `Y` (Borsuk), `N` is chosen so small that the
segments stay where `ρ` is defined, moves points by less than `1`, and lands in `M`.

The homotopy takes values in `M`, not in `N`.

Local contractibility of `Y` is needed: in the Hawaiian earring `Y ⊆ ℝ²` with `X` its base point,
every neighbourhood of `X` contains a circle that is a retract of `Y`, hence not null-homotopic in
`Y`; so no neighbourhood of `X` deforms into `X` inside `Y`.

## Main results

* `MMP.exists_isClosed_isProperMap_retraction_homotopy`.
-/

@[expose] public section

open Set Topology Filter Metric unitInterval

namespace MMP

open MMP

/-- Local contractibility of `Y`, in the form Borsuk's construction uses, for the image of `Y`
under an imbedding into a metric space. -/
theorem exists_contractible_range_of_isEmbedding {Y E : Type*} [TopologicalSpace Y]
    [MetricSpace E] {F : Y → E} (hF : IsEmbedding F)
    (hYc : ∀ y : Y, (𝓝 y).HasBasis (fun V : Set Y ↦ IsOpen V ∧ y ∈ V ∧ ContractibleSpace V) id) :
    ∀ x' ∈ range F, ∀ ε > 0, ∃ W ⊆ range F, W ⊆ ball x' ε ∧ ContractibleSpace W ∧
      ∃ ρ > 0, ball x' ρ ∩ range F ⊆ W := by
  rintro _ ⟨x, rfl⟩ ε hε
  have hP : F ⁻¹' ball (F x) ε ∈ 𝓝 x :=
    (isOpen_ball.preimage hF.continuous).mem_nhds (mem_ball_self hε)
  obtain ⟨V, ⟨hVo, hxV, hVc⟩, hVP⟩ := (hYc x).mem_iff.1 hP
  obtain ⟨O, hO, hOV⟩ := hF.isInducing.isOpen_iff.1 hVo
  have hxO : F x ∈ O := by
    have : x ∈ F ⁻¹' O := hOV ▸ hxV
    exact this
  obtain ⟨ρ, hρ, hρO⟩ := Metric.isOpen_iff.1 hO _ hxO
  refine ⟨F '' V, image_subset_range _ _, ?_, (hF.homeomorphImage V).symm.contractibleSpace, ρ, hρ,
    ?_⟩
  · rintro _ ⟨v, hv, rfl⟩; exact hVP hv
  · rintro _ ⟨hb, y, rfl⟩
    refine ⟨y, ?_, rfl⟩
    rw [← hOV]
    exact hρO hb

/-- **A proper deformation of a closed neighbourhood onto `X`** (Fulton, §19.1). Let `Y` be locally
contractible with a closed imbedding in some `ℝᴺ`, and `X ⊆ Y` closed and locally contractible.
For every neighbourhood `M` of `X` there are a closed `N ⊆ M` with `X ⊆ interior N`, a proper
retraction `r : N → X`, and a proper homotopy `G : N × [0, 1] → Y` with values in `M`, from the
inclusion to `r`, fixing `X`. -/
theorem exists_isClosed_isProperMap_retraction_homotopy {Y : Type*} [TopologicalSpace Y]
    {n : ℕ} {F : Y → EuclideanSpace ℝ (Fin n)} (hF : IsClosedEmbedding F) {X : Set Y}
    (hX : IsClosed X)
    (hXc : ∀ x : X, (𝓝 x).HasBasis (fun V : Set X ↦ IsOpen V ∧ x ∈ V ∧ ContractibleSpace V) id)
    (hYc : ∀ y : Y, (𝓝 y).HasBasis (fun V : Set Y ↦ IsOpen V ∧ y ∈ V ∧ ContractibleSpace V) id)
    {M : Set Y} (hM : M ∈ 𝓝ˢ X) :
    ∃ N : Set Y, IsClosed N ∧ X ⊆ interior N ∧ N ⊆ M ∧
      ∃ r : C(N, X), IsProperMap r ∧ (∀ y : N, (y : Y) ∈ X → (r y : Y) = y) ∧
        ∃ G : C(N × I, Y), IsProperMap G ∧ (∀ y, G (y, 0) = y) ∧ (∀ y, G (y, 1) = r y) ∧
          (∀ y : N, ∀ t, (y : Y) ∈ X → G (y, t) = y) ∧ ∀ q, G q ∈ M := by
  set F' : Y → (Fin n → ℝ) := (EuclideanSpace.equiv (Fin n) ℝ) ∘ F
  have hF' : IsClosedEmbedding F' :=
    (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.isClosedEmbedding.comp hF
  have : TopologicalSpace.MetrizableSpace Y := hF'.isEmbedding.metrizableSpace
  have hX' : IsClosed (F' '' X) := hF'.isClosedMap X hX
  obtain ⟨V, hV, hYV, ρ, hρc, hρY, hρid⟩ := NbhdRetract.exists_retraction_pi hF'.isClosed_range
    (exists_contractible_range_of_isEmbedding hF'.isEmbedding hYc)
  obtain ⟨U, hU, hXU, r', hr'c, hr'X, hr'id⟩ :=
    NbhdRetract.exists_retraction_pi hX' (exists_contractible_of_isEmbedding hF'.isEmbedding hXc)
  obtain ⟨O, hO, hOM⟩ := hF'.isInducing.isOpen_iff.1 (isOpen_interior : IsOpen (interior M))
  have hXO : ∀ x ∈ X, F' x ∈ O := fun x hx ↦ by
    have : x ∈ F' ⁻¹' O := hOM ▸ (subset_interior_iff_mem_nhdsSet.2 hM hx)
    exact this
  -- where `ρ` is defined, moves points by less than `1`, and lands in `O`
  set V'' : Set (Fin n → ℝ) := V ∩ (fun p ↦ (p, ρ p)) ⁻¹'
    ({q : (Fin n → ℝ) × (Fin n → ℝ) | dist q.1 q.2 < 1} ∩ univ ×ˢ O) with hV''def
  have hV'' : IsOpen V'' := (continuousOn_id.prodMk hρc).isOpen_inter_preimage hV
    ((isOpen_lt continuous_dist continuous_const).inter (isOpen_univ.prod hO))
  set seg : (Fin n → ℝ) → ℝ → Fin n → ℝ := fun p t ↦ p + t • (r' p - p) with hseg
  have hsegc : ContinuousOn (fun q : (Fin n → ℝ) × ℝ ↦ seg q.1 q.2) (U ×ˢ univ) :=
    continuousOn_fst.add (continuousOn_snd.smul
      ((hr'c.comp continuousOn_fst fun q hq ↦ hq.1).sub continuousOn_fst))
  -- the points whose segment to their image stays in `V''`
  set W : Set (Fin n → ℝ) := {p | p ∈ U ∧ ∀ t ∈ Icc (0 : ℝ) 1, seg p t ∈ V''}
  have hW : IsOpen W := by
    rw [isOpen_iff_mem_nhds]
    intro p₀ hp₀
    have hU₀ : U ×ˢ (univ : Set ℝ) ∈ 𝓝 (p₀, (0 : ℝ)) := prod_mem_nhds (hU.mem_nhds hp₀.1) univ_mem
    have hP : ∀ t ∈ Icc (0 : ℝ) 1, ∀ᶠ z : (Fin n → ℝ) × ℝ in 𝓝 (p₀, t),
        z.1 ∈ U ∧ seg z.1 z.2 ∈ V'' := by
      intro t ht
      have hUt : U ×ˢ (univ : Set ℝ) ∈ 𝓝 (p₀, t) := prod_mem_nhds (hU.mem_nhds hp₀.1) univ_mem
      have hc : ContinuousAt (fun q : (Fin n → ℝ) × ℝ ↦ seg q.1 q.2) (p₀, t) :=
        hsegc.continuousAt hUt
      exact Filter.Eventually.and (Filter.mem_of_superset hUt fun z hz ↦ hz.1)
        (hc.eventually (hV''.mem_nhds (hp₀.2 t ht)))
    have := isCompact_Icc.eventually_forall_of_forall_eventually (x₀ := p₀)
      (P := fun p t ↦ p ∈ U ∧ seg p t ∈ V'') hP
    filter_upwards [this, hU.mem_nhds hp₀.1] with p hp hpU
    exact ⟨hpU, fun t ht ↦ (hp t ht).2⟩
  have hsegX : ∀ x ∈ X, ∀ t, seg (F' x) t = F' x := fun x hx t ↦ by
    simp [hseg, hr'id _ ⟨x, hx, rfl⟩]
  have hXW : F' '' X ⊆ W := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨hXU ⟨x, hx, rfl⟩, fun t _ ↦ ?_⟩
    rw [hsegX x hx t]
    have hρx : ρ (F' x) = F' x := hρid _ ⟨x, rfl⟩
    refine ⟨hYV ⟨x, rfl⟩, ?_, trivial, ?_⟩
    · change dist (F' x) (ρ (F' x)) < 1
      rw [hρx, dist_self]; exact one_pos
    · change ρ (F' x) ∈ O
      rw [hρx]; exact hXO x hx
  obtain ⟨N', hN'c, hN'W, hXN', hN'K, hN'd⟩ := exists_isClosed_subset_isCompact_inter_preimage hX'
    hW hXW (hr'c.mono fun p hp ↦ hp.1) (hr'X.mono_left fun p hp ↦ hp.1) hr'id
  have hN'U : N' ⊆ U := fun p hp ↦ (hN'W hp).1
  obtain ⟨r, hr, hrid, hFr⟩ := exists_isProperMap_retraction_preimage hF' (hr'c.mono hN'U)
    (hr'X.mono_left hN'U) hr'id hN'K
  have hsegV : ∀ p ∈ N', ∀ t ∈ Icc (0 : ℝ) 1, seg p t ∈ V'' := fun p hp ↦ (hN'W hp).2
  -- the homotopy
  have hGmem : ∀ q : (F' ⁻¹' N') × I, ρ (seg (F' q.1) q.2) ∈ range F' := fun q ↦
    hρY (hsegV _ q.1.2 _ q.2.2).1
  set G : (F' ⁻¹' N') × I → Y := fun q ↦ (hGmem q).choose
  have hFG : ∀ q, F' (G q) = ρ (seg (F' q.1) q.2) := fun q ↦ (hGmem q).choose_spec
  have hGc : Continuous G := by
    rw [hF'.isInducing.continuous_iff]
    have : F' ∘ G = fun q ↦ ρ (seg (F' q.1) q.2) := funext hFG
    rw [this]
    refine hρc.comp_continuous ?_ fun q ↦ (hsegV _ q.1.2 _ q.2.2).1
    exact hsegc.comp_continuous ((hF'.continuous.comp (continuous_subtype_val.comp
      continuous_fst)).prodMk (continuous_subtype_val.comp continuous_snd))
      fun q ↦ ⟨hN'U q.1.2, trivial⟩
  have hGO : ∀ q, F' (G q) ∈ O := fun q ↦ by
    rw [hFG]; exact (hsegV _ q.1.2 _ q.2.2).2.2.2
  have hGM : ∀ q, G q ∈ M := fun q ↦ by
    have : G q ∈ F' ⁻¹' O := hGO q
    rw [hOM] at this
    exact interior_subset this
  refine ⟨F' ⁻¹' N', hN'c.preimage hF'.continuous, fun x hx ↦ ?_, fun y hy ↦ ?_, r, hr, hrid,
    ⟨G, hGc⟩, ?_, fun y ↦ ?_, fun y ↦ ?_, fun y t hy ↦ ?_, hGM⟩
  · exact interior_mono (preimage_mono interior_subset)
      ((isOpen_interior.preimage hF'.continuous).subset_interior_iff.2 subset_rfl
        (hXN' ⟨x, hx, rfl⟩))
  · have h0 := hsegV _ hy 0 ⟨le_rfl, zero_le_one⟩
    have hs0 : seg (F' y) 0 = F' y := by simp [hseg]
    rw [hs0] at h0
    have : y ∈ F' ⁻¹' O := by
      change F' y ∈ O
      rw [← hρid _ ⟨y, rfl⟩]; exact h0.2.2.2
    rw [hOM] at this
    exact interior_subset this
  · -- properness
    refine isProperMap_iff_isCompact_preimage.2 ⟨hGc, fun K hK ↦ ?_⟩
    set Φ : (F' ⁻¹' N') × I → (Fin n → ℝ) × ℝ := fun q ↦ (F' q.1, (q.2 : ℝ))
    have hΦ : IsClosedEmbedding Φ :=
      (hF'.comp (hN'c.preimage hF'.continuous).isClosedEmbedding_subtypeVal).prodMap
        isClosed_Icc.isClosedEmbedding_subtypeVal
    set C : Set ((Fin n → ℝ) × ℝ) :=
      (N' ×ˢ Icc 0 1) ∩ (fun q ↦ ρ (seg q.1 q.2)) ⁻¹' (F' '' K)
    have hCcl : IsClosed C := by
      refine ContinuousOn.preimage_isClosed_of_isClosed ?_ (hN'c.prod isClosed_Icc)
        (hK.image hF'.continuous).isClosed
      exact hρc.comp (hsegc.mono fun q hq ↦ ⟨hN'U hq.1, trivial⟩)
        fun q hq ↦ (hsegV _ hq.1 _ hq.2).1
    have hCb : Bornology.IsBounded C := by
      refine ((Bornology.IsBounded.cthickening (δ := 2) (hK.image hF'.continuous).isBounded).prod
        (isBounded_Icc (0 : ℝ) 1)).subset ?_
      rintro ⟨p, t⟩ ⟨⟨hp, ht⟩, k, hk, hkρ⟩
      refine ⟨mem_cthickening_of_dist_le p (F' k) 2 _ ⟨k, hk, rfl⟩ ?_, ht⟩
      have h1 : dist p (seg p t) ≤ 1 := by
        simp only [hseg, dist_self_add_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        rw [← dist_eq_norm, dist_comm]
        nlinarith [hN'd p hp, ht.2, dist_nonneg (x := p) (y := r' p)]
      have h2 : dist (seg p t) (ρ (seg p t)) < 1 := (hsegV p hp t ht).2.1
      rw [hkρ] at *
      linarith [dist_triangle p (seg p t) (ρ (seg p t))]
    have hCc : IsCompact C := Metric.isCompact_of_isClosed_isBounded hCcl hCb
    convert hΦ.isCompact_preimage hCc using 1
    ext q
    simp only [mem_preimage, C, Φ, mem_inter_iff, mem_prod]
    refine ⟨fun h ↦ ⟨⟨q.1.2, q.2.2⟩, G q, h, hFG q⟩, fun ⟨_, k, hk, hkq⟩ ↦ ?_⟩
    have : k = G q := hF'.injective (hkq.trans (hFG q).symm)
    rw [ContinuousMap.coe_mk, ← this]
    exact hk
  · change G (y, 0) = y
    refine hF'.injective ?_
    rw [hFG]
    simp [hseg, hρid _ ⟨(y : Y), rfl⟩]
  · change G (y, 1) = r y
    refine hF'.injective ?_
    rw [hFG, hFr]
    have : seg (F' y) ((1 : I) : ℝ) = r' (F' y) := by simp [hseg]
    rw [this]
    obtain ⟨x, hx, hxe⟩ := hr'X (hN'U y.2)
    rw [← hxe, hρid _ ⟨x, rfl⟩]
  · change G (y, t) = y
    refine hF'.injective ?_
    rw [hFG, hsegX _ hy, hρid _ ⟨(y : Y), rfl⟩]

end MMP
