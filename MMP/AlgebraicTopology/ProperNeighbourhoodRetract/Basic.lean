module

public import MMP.AlgebraicTopology.ProperNeighbourhoodRetract.Whitney
public import MMP.AlgebraicTopology.ProperNeighbourhoodRetract.Shrink
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated
public import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
public import Mathlib.Topology.Metrizable.Basic

/-!
# Closed neighbourhoods with a proper retraction (Fulton, §19.1)

Let `Y` be a space with a closed imbedding in some `ℝᴺ` and `X ⊆ Y` a closed subset whose points
have arbitrarily small open contractible neighbourhoods in `X` (for instance the underlying space
of a closed subscheme of a complex scheme). Then `X` has a closed neighbourhood `N` in `Y` with a
proper retraction `r : N → X`. This is the input of the cap product
`H^j(Y, Y - X) ⊗ H_k Y → H_{k-j} X` of [BT] 3.1.7.

The image of `X` in `ℝᴺ` is closed and locally contractible, hence a retract of an open
neighbourhood (Borsuk, `NbhdRetract.exists_retraction_pi`); the retraction is proper on a closed
neighbourhood (`exists_isClosed_subset_isCompact_inter_preimage`), and both pull back along the
closed imbedding.

Some local contractibility is forced: for the Warsaw circle `W ⊆ ℝ²` there is no such pair, since
`H^1(ℝ², ℝ² - W) = ℤ` while the singular `H_1 W` vanishes.

## Main results

* `MMP.exists_isClosed_isProperMap_retraction`: the closed neighbourhood with a
  proper retraction.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [A. Hatcher, *Algebraic Topology*][hatcher2002], Appendix, Theorem A.7.
-/

@[expose] public section

open Set Topology Filter Metric

namespace MMP

/-- Local contractibility of `X ⊆ Y` in the form Borsuk's construction uses, for the image of `X`
under an imbedding into a metric space. -/
theorem exists_contractible_of_isEmbedding {Y E : Type*} [TopologicalSpace Y] [MetricSpace E]
    {F : Y → E} (hF : IsEmbedding F) {X : Set Y}
    (hXc : ∀ x : X, (𝓝 x).HasBasis (fun V : Set X ↦ IsOpen V ∧ x ∈ V ∧ ContractibleSpace V) id) :
    ∀ x' ∈ F '' X, ∀ ε > 0, ∃ W ⊆ F '' X, W ⊆ ball x' ε ∧ ContractibleSpace W ∧
      ∃ ρ > 0, ball x' ρ ∩ F '' X ⊆ W := by
  rintro _ ⟨x, hx, rfl⟩ ε hε
  set G : X → E := F ∘ Subtype.val
  have hG : IsEmbedding G := hF.comp IsEmbedding.subtypeVal
  have hP : G ⁻¹' ball (F x) ε ∈ 𝓝 (⟨x, hx⟩ : X) :=
    (isOpen_ball.preimage hG.continuous).mem_nhds (mem_ball_self hε)
  obtain ⟨V, ⟨hVo, hxV, hVc⟩, hVP⟩ := (hXc ⟨x, hx⟩).mem_iff.1 hP
  obtain ⟨O, hO, hOV⟩ := hG.isInducing.isOpen_iff.1 hVo
  have hxO : F x ∈ O := (hOV ▸ hxV : (⟨x, hx⟩ : X) ∈ G ⁻¹' O)
  obtain ⟨ρ, hρ, hρO⟩ := Metric.isOpen_iff.1 hO _ hxO
  refine ⟨G '' V, image_subset_iff.2 fun v _ ↦ ⟨v, v.2, rfl⟩, image_subset_iff.2 hVP,
    (hG.homeomorphImage V).symm.contractibleSpace, ρ, hρ, ?_⟩
  rintro _ ⟨hb, y, hy, rfl⟩
  refine ⟨⟨y, hy⟩, ?_, rfl⟩
  rw [← hOV]
  exact hρO hb

/-- A retraction of a closed neighbourhood `N'` of the image of `X` under a closed imbedding
`F' : Y → E`, proper over `X`, pulls back to a proper retraction of `F'⁻¹ N'` onto `X`. -/
theorem exists_isProperMap_retraction_preimage {Y E : Type*} [TopologicalSpace Y] [MetricSpace E]
    {F' : Y → E} (hF' : IsClosedEmbedding F') {X : Set Y} {N' : Set E} {r' : E → E}
    (hr'c : ContinuousOn r' N') (hr'X : MapsTo r' N' (F' '' X)) (hr'id : ∀ x ∈ F' '' X, r' x = x)
    (hN'K : ∀ K : Set E, IsCompact K → K ⊆ F' '' X → IsCompact (N' ∩ r' ⁻¹' K)) :
    ∃ r : C(F' ⁻¹' N', X), IsProperMap r ∧ (∀ y : F' ⁻¹' N', (y : Y) ∈ X → (r y : Y) = y) ∧
      ∀ y, F' (r y : Y) = r' (F' y) := by
  have hmem : ∀ y : F' ⁻¹' N', ∃ x ∈ X, F' x = r' (F' y) := fun y ↦ hr'X y.2
  set r : F' ⁻¹' N' → X := fun y ↦ ⟨(hmem y).choose, (hmem y).choose_spec.1⟩
  have hFr : ∀ y, F' (r y : Y) = r' (F' y) := fun y ↦ (hmem y).choose_spec.2
  have hrc : Continuous r := by
    rw [IsInducing.subtypeVal.continuous_iff, hF'.isInducing.continuous_iff,
      show F' ∘ Subtype.val ∘ r = r' ∘ F' ∘ Subtype.val from funext hFr]
    exact hr'c.comp_continuous (hF'.continuous.comp continuous_subtype_val) fun y ↦ y.2
  have : TopologicalSpace.MetrizableSpace Y := hF'.isEmbedding.metrizableSpace
  refine ⟨⟨r, hrc⟩, ?_, fun y hy ↦ ?_, hFr⟩
  · refine isProperMap_iff_isCompact_preimage.2 ⟨hrc, fun K hK ↦ ?_⟩
    have hc := hF'.isCompact_preimage (hN'K _ ((hK.image continuous_subtype_val).image
      hF'.continuous) (image_mono (Subtype.coe_image_subset X K)))
    rw [IsInducing.subtypeVal.isCompact_iff]
    convert hc using 1
    ext y
    constructor
    · rintro ⟨y, hyK, rfl⟩
      exact ⟨y.2, ⟨_, ⟨_, hyK, rfl⟩, hFr y⟩⟩
    · rintro ⟨hyN, _, ⟨k, hk, rfl⟩, hk'⟩
      obtain rfl : k = r ⟨y, hyN⟩ := Subtype.ext (hF'.injective (hk'.trans (hFr ⟨y, hyN⟩).symm))
      exact ⟨⟨y, hyN⟩, hk, rfl⟩
  · exact hF'.injective ((hFr y).trans (hr'id _ ⟨y, hy, rfl⟩))

/-- **A closed neighbourhood with a proper retraction** (Fulton, §19.1; [BT] 3.1.7). Let `Y` have
a closed imbedding in some `ℝᴺ` and let `X ⊆ Y` be closed, every point of `X` having a basis of
open contractible neighbourhoods in `X`. Then there is a closed `N ⊆ Y` with `X ⊆ interior N` and
a proper continuous retraction `r : N → X`. -/
theorem exists_isClosed_isProperMap_retraction {Y : Type*} [TopologicalSpace Y] {n : ℕ}
    {F : Y → EuclideanSpace ℝ (Fin n)} (hF : IsClosedEmbedding F) {X : Set Y} (hX : IsClosed X)
    (hXc : ∀ x : X, (𝓝 x).HasBasis (fun V : Set X ↦ IsOpen V ∧ x ∈ V ∧ ContractibleSpace V) id) :
    ∃ N : Set Y, IsClosed N ∧ X ⊆ interior N ∧
      ∃ r : C(N, X), IsProperMap r ∧ ∀ y : N, (y : Y) ∈ X → (r y : Y) = y := by
  set F' : Y → (Fin n → ℝ) := (EuclideanSpace.equiv (Fin n) ℝ) ∘ F
  have hF' : IsClosedEmbedding F' :=
    (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.isClosedEmbedding.comp hF
  have hX' : IsClosed (F' '' X) := hF'.isClosedMap X hX
  obtain ⟨U, hU, hXU, r', hr'c, hr'X, hr'id⟩ :=
    NbhdRetract.exists_retraction_pi hX' (exists_contractible_of_isEmbedding hF'.isEmbedding hXc)
  obtain ⟨N', hN'c, hN'U, hXN', hN'K, -⟩ :=
    exists_isClosed_subset_isCompact_inter_preimage hX' hU hXU hr'c hr'X hr'id
  obtain ⟨r, hr, hrid, -⟩ := exists_isProperMap_retraction_preimage hF' (hr'c.mono hN'U)
    (hr'X.mono_left hN'U) hr'id hN'K
  exact ⟨F' ⁻¹' N', hN'c.preimage hF'.continuous,
    fun x hx ↦ preimage_interior_subset_interior_preimage hF'.continuous (hXN' ⟨x, hx, rfl⟩),
    r, hr, hrid⟩

end MMP
