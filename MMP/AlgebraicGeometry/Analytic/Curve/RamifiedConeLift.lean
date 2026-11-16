module

public import MMP.AlgebraicGeometry.Analytic.Curve.ChartConeCellulation
public import MMP.AlgebraicGeometry.Analytic.CurveNormalFormChart

/-!
# Lifts of flat cones from a branch value

Let `p : Y → Z` be a map which, over a disc `D = {‖z - s₀‖ < δ}` of a chart `z` of `Z`, is the
disjoint union of finitely many branched discs: on the source of the `i`-th coordinate `wᵢ` of
`Y`, `z ∘ p = s₀ + wᵢ ^ eᵢ`, every point of `p⁻¹(D)` lies in one of the sources, and the sources
are pairwise disjoint (`RamifiedDisc`). This is the shape of a holomorphic map of Riemann surfaces
over a small disc around a value `s₀`, in the local normal form.

A lift of a singular simplex `T` of `D` lies in one branched disc, by connectedness, and in the
`i`-th one it is `wᵢ⁻¹ ∘ (u L)` for an `eᵢ`-th root `L` of `z ∘ T - s₀` and an `eᵢ`-th root of
unity `u`, as soon as `L` is continuous and its nonvanishing locus is preconnected
(`exists_pow_eq_one_forall_eq_mul`). For the flat cone `C` from `s₀` over an arc `γ` of `D` which
avoids `s₀`, the root is the cone from `0` over an `eᵢ`-th root `R` of `γ - s₀`, with the radial
profile `rootProfile eᵢ`; so `C` has exactly `eᵢ` lifts in the `i`-th disc
(`ncard_simplexLifts_coneSimplex_inter`), and restricting lifts to a face is a bijection onto the
lifts of the face (`bijOn_comp_face_coneSimplex`), which is what the transfer of a cycle through a
ramification point needs (`bd_transfer_eq_zero_of_bijOn`).

Read in a chart `c` of `Y` in which `c ∘ wᵢ⁻¹` is holomorphic, a lift is `(c ∘ wᵢ⁻¹) ∘ g` for the
cone map `g` of profile `rootProfile eᵢ` over `u R`. A holomorphic map multiplies the Jacobian
`Im(conj(∂₁ g) ∂₂ g)` by `|h'|²` (`im_star_fderiv_comp_eq`), and the turning of `R` around `0`
has the sign of the turning of `γ` around `s₀` (`im_star_sub_mul_deriv_eq_of_pow_eq`), so the
reading has nonnegative Jacobian when `γ` turns counterclockwise
(`exists_reading_rootCone`).

## Main definitions

* `MMP.Analytic.ChartConeCellulation.RamifiedDisc`: a map that is a finite disjoint union of
  branched discs `w ↦ s₀ + w ^ e` over a disc of a chart.

## Main results

* `MMP.Analytic.ChartConeCellulation.exists_pow_eq_one_forall_eq_mul`: two continuous `e`-th
  roots of one function differ by an `e`-th root of unity, where the function does not vanish on
  a preconnected set.
* `MMP.Analytic.ChartConeCellulation.RamifiedDisc.bijOn_comp_face`: over a ramified disc, lifts
  of a simplex with a continuous root restrict bijectively to the lifts of a face.
* `MMP.Analytic.ChartConeCellulation.RamifiedDisc.simplexLifts_coneSimplex_inter_eq`: the lifts of
  a flat cone from the branch value in one branched disc.
* `MMP.Analytic.ChartConeCellulation.RamifiedDisc.bijOn_comp_face_coneSimplex`,
  `MMP.Analytic.ChartConeCellulation.RamifiedDisc.finite_simplexLifts_coneSimplex`: the
  hypotheses of `bd_transfer_eq_zero_of_bijOn` for a flat cone from the branch value.
* `MMP.Analytic.ChartConeCellulation.exists_reading_rootCone`: the reading of a lift in a chart.
* `MMP.Analytic.ChartConeCellulation.exists_contDiff_pow_eq_segmentCurve_sub`: a smooth `e`-th
  root of `γ - s₀` along a flat segment `γ` with `s₀` strictly on its left.
* `MMP.Analytic.ChartConeCellulation.exists_pow_normalForm_of_analyticAt`,
  `MMP.Analytic.ChartConeCellulation.exists_pow_normalForm_realize`: the local normal form
  `z ∘ p = z(p q) + φ ^ e` of a map holomorphic in charts, and of a realized morphism of curves.
* `MMP.Analytic.ChartConeCellulation.exists_ramifiedDisc`,
  `MMP.Analytic.ChartConeCellulation.exists_ramifiedDisc_realize`: a closed map with a finite
  fibre, in the local normal form at each point of the fibre, is a ramified disc near the fibre.

## References

* [S. Donaldson, *Riemann Surfaces*], §8 (triangulation by pulling back along a meromorphic
  function).
-/

@[expose] public noncomputable section

open Set Finsupp MMP.SingularChain Polynomial
open MMP.Analytic MMP.Analytic.CurveCupPositivity

namespace MMP.Analytic.ChartConeCellulation

/-! ### Roots of unity and continuous roots -/

section Roots

/-- **Continuous roots differ by a root of unity.** Two continuous `e`-th roots `W`, `L` of one
function are proportional, `W = u L` with `u ^ e = 1`, when the locus where `L` does not vanish
is preconnected. -/
theorem exists_pow_eq_one_forall_eq_mul {S : Type*} [TopologicalSpace S] {W L : S → ℂ}
    (hW : Continuous W) (hL : Continuous L) {e : ℕ} (he : 0 < e)
    (h : ∀ t, W t ^ e = L t ^ e) (hA : IsPreconnected {t | L t ≠ 0}) :
    ∃ u : ℂ, u ^ e = 1 ∧ ∀ t, W t = u * L t := by
  have hz : ∀ t, L t = 0 → W t = 0 := fun t ht ↦
    (pow_eq_zero_iff he.ne').1 (by rw [h t, ht, zero_pow he.ne'])
  by_cases hne : ∃ t₀, L t₀ ≠ 0
  · obtain ⟨t₀, ht₀⟩ := hne
    have hdisc : IsDiscrete ((nthRootsFinset e (1 : ℂ) : Finset ℂ) : Set ℂ) :=
      (Finset.finite_toSet _).isDiscrete
    have hc : ContinuousOn (fun t ↦ W t / L t) {t | L t ≠ 0} :=
      hW.continuousOn.div hL.continuousOn fun t ht ↦ ht
    have hm : MapsTo (fun t ↦ W t / L t) {t | L t ≠ 0}
        ((nthRootsFinset e (1 : ℂ) : Finset ℂ) : Set ℂ) := fun t ht ↦ by
      simp only [Finset.mem_coe, mem_nthRootsFinset he]
      rw [div_pow, h t, div_self (pow_ne_zero _ ht)]
    refine ⟨W t₀ / L t₀, (mem_nthRootsFinset he _).1 (hm ht₀), fun t ↦ ?_⟩
    by_cases ht : L t = 0
    · rw [ht, mul_zero, hz t ht]
    · rw [hA.constant_of_mapsTo hdisc hc hm ht₀ ht, div_mul_cancel₀ _ ht]
  · push Not at hne
    exact ⟨1, one_pow _, fun t ↦ by rw [hne t, mul_zero, hz t (hne t)]⟩

/-- An `e`-th root of `z - s₀` with `z ≠ s₀` is nonzero. -/
theorem ne_zero_of_pow_eq_sub {r z s₀ : ℂ} {e : ℕ} (he : 0 < e) (h : r ^ e = z - s₀)
    (hz : z ≠ s₀) : r ≠ 0 := by
  rintro rfl
  rw [zero_pow he.ne'] at h
  exact hz (sub_eq_zero.1 h.symm)

/-- The points of a standard simplex where a sum of coordinates does not vanish form a
preconnected set. -/
theorem isPreconnected_setOf_sum_ne_zero {m : ℕ} (s : Finset (Fin m)) :
    IsPreconnected {x : stdSimplex ℝ (Fin m) | ∑ i ∈ s, x i ≠ 0} := by
  rw [← Topology.IsInducing.subtypeVal.isPreconnected_image]
  refine Convex.isPreconnected ?_
  have heq : Subtype.val '' {x : stdSimplex ℝ (Fin m) | ∑ i ∈ s, x i ≠ 0} =
      stdSimplex ℝ (Fin m) ∩ {x | 0 < ∑ i ∈ s, x i} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, lt_of_le_of_ne (Finset.sum_nonneg fun i _ ↦ y.2.1 i) (Ne.symm hy)⟩
    · rintro ⟨hx, hpos⟩
      exact ⟨⟨x, hx⟩, hpos.ne', rfl⟩
  rw [heq]
  refine (convex_stdSimplex ℝ (Fin m)).inter (convex_halfSpace_gt ?_ 0)
  exact { map_add := fun x y ↦ by simp [Finset.sum_add_distrib]
          map_smul := fun c x ↦ by simp [Finset.mul_sum] }

end Roots

/-! ### Lifts in a branched coordinate -/

section LocalLifts

variable {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
  {zc : OpenPartialHomeomorph Z ℂ} {s₀ : ℂ} {φ : OpenPartialHomeomorph Y ℂ} {e : ℕ}

/-- On a lift with values in the source of a branched coordinate `φ`, `φ ^ e` is the reading of
the simplex minus the branch value. -/
theorem pow_apply_eq_of_mem_simplexLifts
    (hnf : ∀ y ∈ φ.source, p y ∈ zc.source ∧ zc (p y) = s₀ + φ y ^ e) {k : ℕ}
    {T : Simplex Z k} {T' : Simplex Y k} (hT' : T' ∈ simplexLifts p T) {t}
    (ht : T' t ∈ φ.source) : φ (T' t) ^ e = zc (T t) - s₀ := by
  have hp : p (T' t) = T t := congrFun hT' t
  rw [← hp, (hnf _ ht).2]
  ring

/-- **A root in the branched coordinate is a lift.** -/
theorem mapSimplex_symm_mem_simplexLifts
    (hnf : ∀ y ∈ φ.source, p y ∈ zc.source ∧ zc (p y) = s₀ + φ y ^ e) {k : ℕ}
    {T : Simplex Z k} (hT : ∀ t, T t ∈ zc.source) (W : Simplex ℂ k) (hW : range W ⊆ φ.target)
    (hpow : ∀ t, W t ^ e = zc (T t) - s₀) :
    mapSimplex φ.symm φ.continuousOn_symm W hW ∈ simplexLifts p T := by
  funext t
  have hWt : W t ∈ φ.target := hW ⟨t, rfl⟩
  have hy : φ.symm (W t) ∈ φ.source := φ.map_target hWt
  obtain ⟨hps, hpz⟩ := hnf _ hy
  refine zc.injOn hps (hT t) ?_
  change zc (p (φ.symm (W t))) = zc (T t)
  rw [hpz, φ.right_inv hWt, hpow t]
  ring

/-- **A lift in the branched coordinate is a root, up to a root of unity.** If `L` is a
continuous `e`-th root of the reading of `T` minus the branch value, with preconnected
nonvanishing locus, every lift of `T` with values in the source of `φ` is `φ⁻¹ ∘ (u L)` for an
`e`-th root of unity `u`. -/
theorem exists_eq_symm_mul_of_mem_simplexLifts
    (hnf : ∀ y ∈ φ.source, p y ∈ zc.source ∧ zc (p y) = s₀ + φ y ^ e) (he : 0 < e) {k : ℕ}
    {T : Simplex Z k} {T' : Simplex Y k} (hT' : T' ∈ simplexLifts p T)
    (hsrc : ∀ t, T' t ∈ φ.source) (L : Simplex ℂ k) (hL : ∀ t, L t ^ e = zc (T t) - s₀)
    (hA : IsPreconnected {t | L t ≠ 0}) :
    ∃ u : ℂ, u ^ e = 1 ∧ ∀ t, T' t = φ.symm (u * L t) := by
  have hW : Continuous fun t ↦ φ (T' t) :=
    φ.continuousOn.comp_continuous T'.continuous hsrc
  obtain ⟨u, hu, hWu⟩ := exists_pow_eq_one_forall_eq_mul hW L.continuous he
    (fun t ↦ by rw [pow_apply_eq_of_mem_simplexLifts hnf hT' (hsrc t), hL t]) hA
  exact ⟨u, hu, fun t ↦ by rw [← hWu t, φ.left_inv (hsrc t)]⟩

end LocalLifts

/-! ### Ramified discs -/

section RamifiedDisc

variable {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]

/-- A map `p : Y → Z` is, over the disc `‖z - s₀‖ < δ` of a chart `z` of `Z`, a finite disjoint
union of branched discs: on the source of the `i`-th coordinate `wᵢ`, `z ∘ p = s₀ + wᵢ ^ eᵢ`;
the target of `wᵢ` contains every `w` with `‖w ^ eᵢ‖ < δ`; the sources are pairwise disjoint and
cover the preimage of the disc. -/
structure RamifiedDisc.{w} (p : Y → Z) where
  /-- The chart of `Z`. -/
  chart : OpenPartialHomeomorph Z ℂ
  /-- The branch value, in the chart. -/
  centre : ℂ
  /-- The radius of the disc. -/
  radius : ℝ
  /-- The index set of the branched discs. -/
  ι : Type w
  /-- There are finitely many branched discs. -/
  finite_ι : Finite ι
  /-- The ramification indices. -/
  index : ι → ℕ
  /-- The ramification indices are positive. -/
  index_pos : ∀ i, 0 < index i
  /-- The branched coordinates. -/
  coord : ι → OpenPartialHomeomorph Y ℂ
  /-- On the source of `coord i`, the chart of `p` is `centre + (coord i) ^ index i`. -/
  normalForm : ∀ i, ∀ y ∈ (coord i).source,
    p y ∈ chart.source ∧ chart (p y) = centre + coord i y ^ index i
  /-- The target of `coord i` contains every `w` with `‖w ^ index i‖ < radius`. -/
  mem_target : ∀ i (w : ℂ), ‖w ^ index i‖ < radius → w ∈ (coord i).target
  /-- The sources of the coordinates cover the preimage of the disc. -/
  exists_mem_source : ∀ y, p y ∈ chart.source → ‖chart (p y) - centre‖ < radius →
    ∃ i, y ∈ (coord i).source
  /-- The sources of the coordinates are pairwise disjoint. -/
  pairwise_disjoint : Pairwise fun i j ↦ Disjoint (coord i).source (coord j).source

namespace RamifiedDisc

variable {p : Y → Z} (d : RamifiedDisc p)

instance : Finite d.ι := d.finite_ι

/-- A simplex of `Z` lies over the disc. -/
def IsOver {k : ℕ} (T : Simplex Z k) : Prop :=
  ∀ t, T t ∈ d.chart.source ∧ ‖d.chart (T t) - d.centre‖ < d.radius

/-- Every face of a simplex lying over the disc lies over the disc. -/
theorem IsOver.comp_face {d : RamifiedDisc p} {k : ℕ} {T : Simplex Z (k + 1)} (hT : d.IsOver T)
    (j : Fin (k + 2)) : d.IsOver (T.comp (face k j)) :=
  fun _ ↦ hT _

/-- **A lift over the disc lies in one branched disc**, by connectedness of the simplex. -/
theorem exists_forall_mem_source {k : ℕ} {T : Simplex Z k} (hT : d.IsOver T)
    {T' : Simplex Y k} (hT' : T' ∈ simplexLifts p T) :
    ∃ i, ∀ t, T' t ∈ (d.coord i).source := by
  have hmem : ∀ t, ∃ i, T' t ∈ (d.coord i).source := fun t ↦ by
    have hp : p (T' t) = T t := congrFun hT' t
    exact d.exists_mem_source _ (hp ▸ (hT t).1) (hp ▸ (hT t).2)
  let t₀ : stdSimplex ℝ (Fin (k + 1)) := ⟨_, single_mem_stdSimplex ℝ 0⟩
  obtain ⟨i, hi⟩ := hmem t₀
  refine ⟨i, fun t ↦ ?_⟩
  have hsub : range T' ⊆ (d.coord i).source ∪ ⋃ j ∈ ({i}ᶜ : Set d.ι), (d.coord j).source := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨j, hj⟩ := hmem t
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hj)
    · exact Or.inr (mem_biUnion (x := j) hji hj)
  have hdis : Disjoint (d.coord i).source (⋃ j ∈ ({i}ᶜ : Set d.ι), (d.coord j).source) := by
    rw [disjoint_iUnion₂_right]
    exact fun j hj ↦ d.pairwise_disjoint (Ne.symm hj)
  exact (isPreconnected_range T'.continuous).subset_left_of_subset_union (d.coord i).open_source
    (isOpen_biUnion fun j _ ↦ (d.coord j).open_source) hdis hsub ⟨T' t₀, ⟨t₀, rfl⟩, hi⟩ ⟨t, rfl⟩

/-- An `e`-th root of the reading of a simplex over the disc lies in the target of the branched
coordinate. -/
theorem mem_target_of_pow_eq {k : ℕ} {T : Simplex Z k} (hT : d.IsOver T) (i : d.ι)
    {w : ℂ} {t} (hw : w ^ d.index i = d.chart (T t) - d.centre) : w ∈ (d.coord i).target :=
  d.mem_target i w (by rw [hw]; exact (hT t).2)

/-- If `L` is an `index i`-th root of `chart ∘ T - centre` for a simplex `T` over the disc, then
`u • L` lands in the target of `coord i` for every `index i`-th root of unity `u`. -/
theorem range_smul_subset_target {k : ℕ} {T : Simplex Z k} (hT : d.IsOver T) (i : d.ι)
    (L : Simplex ℂ k) (hL : ∀ t, L t ^ d.index i = d.chart (T t) - d.centre) {u : ℂ}
    (hu : u ^ d.index i = 1) : range (u • L) ⊆ (d.coord i).target := by
  rintro _ ⟨t, rfl⟩
  refine d.mem_target_of_pow_eq hT i (t := t) ?_
  rw [ContinuousMap.smul_apply, smul_eq_mul, mul_pow, hu, one_mul, hL t]

/-- If `L` is an `index i`-th root of `chart ∘ T - centre` for a simplex `T` over the disc and `u`
is an `index i`-th root of unity, then `(coord i)⁻¹ ∘ (u • L)` is a lift of `T`. -/
theorem mapSimplex_coord_symm_smul_mem_simplexLifts {k : ℕ} {T : Simplex Z k} (hT : d.IsOver T)
    (i : d.ι) (L : Simplex ℂ k) (hL : ∀ t, L t ^ d.index i = d.chart (T t) - d.centre) {u : ℂ}
    (hu : u ^ d.index i = 1) :
    mapSimplex (d.coord i).symm (d.coord i).continuousOn_symm (u • L)
      (d.range_smul_subset_target hT i L hL hu) ∈ simplexLifts p T :=
  mapSimplex_symm_mem_simplexLifts (d.normalForm i) (fun t ↦ (hT t).1) _ _ fun t ↦ by
    rw [ContinuousMap.smul_apply, smul_eq_mul, mul_pow, hu, one_mul, hL t]

/-- **The lifts of a simplex in one branched disc.** For a continuous `eᵢ`-th root `L` of the
reading of `T` minus the branch value, with preconnected nonvanishing locus, the lifts of `T` in
the `i`-th branched disc are the `φᵢ⁻¹ ∘ (u L)`, `u ^ eᵢ = 1`. -/
theorem simplexLifts_inter_eq {k : ℕ} {T : Simplex Z k} (hT : d.IsOver T) (i : d.ι)
    (L : Simplex ℂ k) (hL : ∀ t, L t ^ d.index i = d.chart (T t) - d.centre)
    (hA : IsPreconnected {t | L t ≠ 0}) :
    simplexLifts p T ∩ {T' | ∀ t, T' t ∈ (d.coord i).source} =
      {T' | ∃ u : ℂ, u ^ d.index i = 1 ∧ ∀ t, T' t = (d.coord i).symm (u * L t)} := by
  ext T'
  constructor
  · rintro ⟨hT', hsrc⟩
    exact exists_eq_symm_mul_of_mem_simplexLifts (d.normalForm i) (d.index_pos i) hT' hsrc L hL hA
  · rintro ⟨u, hu, hT'⟩
    have heq : T' = mapSimplex (d.coord i).symm (d.coord i).continuousOn_symm (u • L)
        (d.range_smul_subset_target hT i L hL hu) := by
      ext t
      exact hT' t
    refine ⟨heq ▸ d.mapSimplex_coord_symm_smul_mem_simplexLifts hT i L hL hu, fun t ↦ ?_⟩
    rw [hT' t]
    exact (d.coord i).map_target (d.range_smul_subset_target hT i L hL hu ⟨t, rfl⟩)

/-- Over the disc, a lift `φᵢ⁻¹ ∘ (u L)` is read back as `u L` by `φᵢ`. -/
theorem coord_coord_symm_mul {k : ℕ} {T : Simplex Z k} (hT : d.IsOver T) (i : d.ι)
    (L : Simplex ℂ k) (hL : ∀ t, L t ^ d.index i = d.chart (T t) - d.centre) {u : ℂ}
    (hu : u ^ d.index i = 1) (t) : d.coord i ((d.coord i).symm (u * L t)) = u * L t :=
  (d.coord i).right_inv (d.range_smul_subset_target hT i L hL hu ⟨t, rfl⟩)

/-- **Finiteness of lifts over the disc**, given continuous roots in every branched disc. -/
theorem finite_simplexLifts {k : ℕ} {T : Simplex Z k} (hT : d.IsOver T)
    (L : d.ι → Simplex ℂ k) (hL : ∀ i t, L i t ^ d.index i = d.chart (T t) - d.centre)
    (hA : ∀ i, IsPreconnected {t | L i t ≠ 0}) : (simplexLifts p T).Finite := by
  have hsub : simplexLifts p T ⊆ ⋃ i, ⋃ u ∈ ((nthRootsFinset (d.index i) (1 : ℂ) : Finset ℂ) :
      Set ℂ), {T' : Simplex Y k | ∀ t, T' t = (d.coord i).symm (u * L i t)} := by
    intro T' hT'
    obtain ⟨i, hi⟩ := d.exists_forall_mem_source hT hT'
    have hmem : T' ∈ simplexLifts p T ∩ {T' | ∀ t, T' t ∈ (d.coord i).source} := ⟨hT', hi⟩
    rw [d.simplexLifts_inter_eq hT i (L i) (hL i) (hA i)] at hmem
    obtain ⟨u, hu, hT'u⟩ := hmem
    exact mem_iUnion.2 ⟨i, mem_biUnion (by simpa [mem_nthRootsFinset (d.index_pos i)]) hT'u⟩
  refine Set.Finite.subset (finite_iUnion fun i ↦ (Finset.finite_toSet _).biUnion fun u _ ↦ ?_)
    hsub
  refine Set.Subsingleton.finite fun T₁ h₁ T₂ h₂ ↦ ?_
  ext t
  rw [h₁ t, h₂ t]

/-- **Lifts over a ramified disc restrict bijectively to the lifts of a face.** Let `T` lie over
the disc, and suppose that in every branched disc there is a continuous root `Lᵢ` of the reading
of `T` minus the branch value, whose nonvanishing locus is preconnected, and whose restriction to
the `j`-th face has a preconnected nonempty nonvanishing locus. Then restricting lifts of `T` to
the `j`-th face is a bijection onto the lifts of that face. -/
theorem bijOn_comp_face {k : ℕ} {T : Simplex Z (k + 1)} (hT : d.IsOver T)
    (L : d.ι → Simplex ℂ (k + 1)) (hL : ∀ i t, L i t ^ d.index i = d.chart (T t) - d.centre)
    (hA : ∀ i, IsPreconnected {t | L i t ≠ 0}) (j : Fin (k + 2))
    (hAj : ∀ i, IsPreconnected {t | L i (face k j t) ≠ 0})
    (hne : ∀ i, ∃ t, L i (face k j t) ≠ 0) :
    BijOn (fun T' : Simplex Y (k + 1) ↦ T'.comp (face k j)) (simplexLifts p T)
      (simplexLifts p (T.comp (face k j))) := by
  have hTj := hT.comp_face j
  have hLj : ∀ i t, (L i).comp (face k j) t ^ d.index i =
      d.chart (T.comp (face k j) t) - d.centre := fun i t ↦ hL i _
  have hlift : ∀ T' ∈ simplexLifts p T, ∃ i u, u ^ d.index i = 1 ∧
      ∀ t, T' t = (d.coord i).symm (u * L i t) := fun T' hT' ↦ by
    obtain ⟨i, hi⟩ := d.exists_forall_mem_source hT hT'
    have hmem : T' ∈ simplexLifts p T ∩ {T' | ∀ t, T' t ∈ (d.coord i).source} := ⟨hT', hi⟩
    rw [d.simplexLifts_inter_eq hT i (L i) (hL i) (hA i)] at hmem
    exact ⟨i, hmem⟩
  refine ⟨mapsTo_comp_simplexLifts p T j, fun T₁ h₁ T₂ h₂ h ↦ ?_, fun ε hε ↦ ?_⟩
  · obtain ⟨i₁, u₁, hu₁, hT₁⟩ := hlift T₁ h₁
    obtain ⟨i₂, u₂, hu₂, hT₂⟩ := hlift T₂ h₂
    obtain ⟨t₀, ht₀⟩ := hne i₁
    have hpt : T₁ (face k j t₀) = T₂ (face k j t₀) :=
      congrArg (fun f : Simplex Y k ↦ f t₀) h
    have hs₁ : T₁ (face k j t₀) ∈ (d.coord i₁).source := by
      rw [hT₁]
      exact (d.coord i₁).map_target
        (d.range_smul_subset_target hT i₁ (L i₁) (hL i₁) hu₁ ⟨_, rfl⟩)
    have hs₂ : T₂ (face k j t₀) ∈ (d.coord i₂).source := by
      rw [hT₂]
      exact (d.coord i₂).map_target
        (d.range_smul_subset_target hT i₂ (L i₂) (hL i₂) hu₂ ⟨_, rfl⟩)
    have hi : i₁ = i₂ := by
      by_contra hne'
      exact (d.pairwise_disjoint hne').le_bot ⟨hs₁, hpt ▸ hs₂⟩
    subst hi
    have hu : u₁ = u₂ := by
      have h1 := congrArg (d.coord i₁) hpt
      rw [hT₁, hT₂, d.coord_coord_symm_mul hT i₁ (L i₁) (hL i₁) hu₁,
        d.coord_coord_symm_mul hT i₁ (L i₁) (hL i₁) hu₂] at h1
      exact mul_right_cancel₀ ht₀ h1
    subst hu
    ext t
    rw [hT₁ t, hT₂ t]
  · obtain ⟨i, hi⟩ := d.exists_forall_mem_source hTj hε
    have hmem : ε ∈ simplexLifts p (T.comp (face k j)) ∩
        {T' | ∀ t, T' t ∈ (d.coord i).source} := ⟨hε, hi⟩
    rw [d.simplexLifts_inter_eq hTj i ((L i).comp (face k j)) (hLj i) (hAj i)] at hmem
    obtain ⟨u, hu, hεu⟩ := hmem
    refine ⟨_, d.mapSimplex_coord_symm_smul_mem_simplexLifts hT i (L i) (hL i) hu, ?_⟩
    ext t
    exact (hεu t).symm

end RamifiedDisc

end RamifiedDisc

/-! ### The root of a flat cone from the branch value -/

section ConeRoot

/-- `coneProfile x ≤ 1` for `x ≤ 1`. -/
theorem coneProfile_le_one {x : ℝ} (hx : x ≤ 1) : coneProfile x ≤ 1 := by
  rw [coneProfile, div_le_one expNegInvGlue_one_pos]
  exact expNegInvGlue.monotone hx

/-- For `e > 0` and `x ≥ 0`, `rootProfile e x = 0` if and only if `x = 0`. -/
theorem rootProfile_eq_zero_iff {e : ℕ} (he : 0 < e) {x : ℝ} (hx : 0 ≤ x) :
    rootProfile e x = 0 ↔ x = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rootProfile_zero e⟩
  by_contra hne
  exact (rootProfile_pos he (lt_of_le_of_ne hx (Ne.symm hne))).ne' h

/-- The cone from `0` over `u R` is `u` times the cone over `R`. -/
theorem coneSimplex_zero_smul {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hρ0 : ρ 0 = 0) {R : ℝ → ℂ}
    (hR : ContinuousOn R (Icc 0 1)) (u : ℂ) (t : stdSimplex ℝ (Fin 3)) :
    coneSimplex hρ hρ0 (0 : ℂ) (hR.const_smul u) t = u * coneSimplex hρ hρ0 (0 : ℂ) hR t := by
  simp only [coneSimplex_apply, clampCurve, Pi.smul_apply, smul_eq_mul, zero_add, sub_zero,
    Complex.real_smul]
  ring

/-- **The `e`-th power of the root cone.** If `R ^ e = γ - s₀` on `[0, 1]`, the `e`-th power of
the cone from `0` over `R` with profile `rootProfile e` is the flat cone from `s₀` over `γ`,
minus `s₀`. -/
theorem coneSimplex_rootProfile_pow {e : ℕ} (he : 0 < e) {R γ : ℝ → ℂ} {s₀ : ℂ}
    (hR : ContinuousOn R (Icc 0 1)) (hγ : ContinuousOn γ (Icc 0 1))
    (hRγ : ∀ y ∈ Icc (0 : ℝ) 1, R y ^ e = γ y - s₀) (t : stdSimplex ℝ (Fin 3)) :
    coneSimplex (continuous_rootProfile e) (rootProfile_zero e) (0 : ℂ) hR t ^ e =
      coneSimplex continuous_coneProfile coneProfile_zero s₀ hγ t - s₀ := by
  simp only [coneSimplex_apply, clampCurve, zero_add, sub_zero, Complex.real_smul, mul_pow,
    add_sub_cancel_left]
  rw [← Complex.ofReal_pow, rootProfile_pow he, hRγ _ (Set.projIcc (0 : ℝ) 1 zero_le_one _).2]

/-- The cone with profile `rootProfile e` from `0` over a nowhere-vanishing `R` is nonzero at a
point of the simplex exactly when the sum of its coordinates `1` and `2` is nonzero. -/
theorem coneSimplex_rootProfile_ne_zero_iff {e : ℕ} (he : 0 < e) {R : ℝ → ℂ}
    (hR : ContinuousOn R (Icc 0 1)) (hR0 : ∀ y ∈ Icc (0 : ℝ) 1, R y ≠ 0)
    (t : stdSimplex ℝ (Fin 3)) :
    coneSimplex (continuous_rootProfile e) (rootProfile_zero e) (0 : ℂ) hR t ≠ 0 ↔
      ∑ i ∈ ({1, 2} : Finset (Fin 3)), t i ≠ 0 := by
  rw [Finset.sum_pair (by decide)]
  simp only [coneSimplex_apply, clampCurve, zero_add, sub_zero, Complex.real_smul, ne_eq,
    mul_eq_zero, Complex.ofReal_eq_zero, not_or]
  rw [rootProfile_eq_zero_iff he (add_nonneg (stdSimplex_apply_nonneg t 1)
    (stdSimplex_apply_nonneg t 2))]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, hR0 _ (Set.projIcc (0 : ℝ) 1 zero_le_one _).2⟩⟩

/-- The nonvanishing locus of the root cone over a nowhere-vanishing `R` is preconnected. -/
theorem isPreconnected_coneSimplex_rootProfile_ne_zero {e : ℕ} (he : 0 < e) {R : ℝ → ℂ}
    (hR : ContinuousOn R (Icc 0 1)) (hR0 : ∀ y ∈ Icc (0 : ℝ) 1, R y ≠ 0) :
    IsPreconnected
      {t | coneSimplex (continuous_rootProfile e) (rootProfile_zero e) (0 : ℂ) hR t ≠ 0} := by
  rw [show {t | coneSimplex (continuous_rootProfile e) (rootProfile_zero e) (0 : ℂ) hR t ≠ 0} =
      {t : stdSimplex ℝ (Fin 3) | ∑ i ∈ ({1, 2} : Finset (Fin 3)), t i ≠ 0} from
    Set.ext (coneSimplex_rootProfile_ne_zero_iff he hR hR0)]
  exact isPreconnected_setOf_sum_ne_zero _

/-- On every face, the root cone has a preconnected nonempty nonvanishing locus. -/
theorem isPreconnected_and_exists_coneSimplex_rootProfile_face_ne_zero {e : ℕ} (he : 0 < e)
    {R : ℝ → ℂ} (hR : ContinuousOn R (Icc 0 1)) (hR0 : ∀ y ∈ Icc (0 : ℝ) 1, R y ≠ 0) (j : Fin 3) :
    IsPreconnected {t | coneSimplex (continuous_rootProfile e) (rootProfile_zero e) (0 : ℂ) hR
        (face 1 j t) ≠ 0} ∧
      ∃ t, coneSimplex (continuous_rootProfile e) (rootProfile_zero e) (0 : ℂ) hR
        (face 1 j t) ≠ 0 := by
  have key : ∀ t : stdSimplex ℝ (Fin 2),
      coneSimplex (continuous_rootProfile e) (rootProfile_zero e) (0 : ℂ) hR (face 1 j t) ≠ 0 ↔
        ∑ i ∈ (if j = 0 then ({0, 1} : Finset (Fin 2)) else {1}), t i ≠ 0 := by
    intro t
    rw [coneSimplex_rootProfile_ne_zero_iff he hR hR0, Finset.sum_pair (by decide),
      face_apply_one, face_apply_two]
    fin_cases j <;> simp [stdSimplex_two_add]
  have hset : {t | coneSimplex (continuous_rootProfile e) (rootProfile_zero e) (0 : ℂ) hR
      (face 1 j t) ≠ 0} =
      {t : stdSimplex ℝ (Fin 2) |
        ∑ i ∈ (if j = 0 then ({0, 1} : Finset (Fin 2)) else {1}), t i ≠ 0} :=
    Set.ext key
  refine ⟨hset ▸ isPreconnected_setOf_sum_ne_zero _, ⟨_, single_mem_stdSimplex ℝ 1⟩, ?_⟩
  rw [key]
  split_ifs <;> simp

end ConeRoot

/-! ### Lifts of a flat cone from the branch value -/

section ConeLifts

variable {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}

namespace RamifiedDisc

variable (d : RamifiedDisc p) {γ : ℝ → ℂ} {hγ : ContinuousOn γ (Icc 0 1)}

/-- The flat cone from the branch value over an arc of the disc lies over the disc. -/
theorem isOver_coneSimplex
    (hC : range (coneSimplex continuous_coneProfile coneProfile_zero d.centre hγ) ⊆
      d.chart.target)
    (hγδ : ∀ y ∈ Icc (0 : ℝ) 1, ‖γ y - d.centre‖ < d.radius) :
    d.IsOver (mapSimplex d.chart.symm d.chart.continuousOn_symm
      (coneSimplex continuous_coneProfile coneProfile_zero d.centre hγ) hC) := by
  intro t
  have ht := hC ⟨t, rfl⟩
  refine ⟨d.chart.map_target ht, ?_⟩
  rw [mapSimplex_apply, d.chart.right_inv ht, coneSimplex_apply, add_sub_cancel_left,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (coneProfile_nonneg _)]
  have hr : t 1 + t 2 ≤ 1 := by
    linarith [stdSimplex_three_add t, stdSimplex_apply_nonneg t 0]
  exact (mul_le_of_le_one_left (norm_nonneg _) (coneProfile_le_one hr)).trans_lt
    (hγδ _ (Set.projIcc (0 : ℝ) 1 zero_le_one (t 2 / (t 1 + t 2))).2)

/-- Reading the pulled-back cone in the chart recovers the cone. -/
theorem chart_mapSimplex_coneSimplex
    (hC : range (coneSimplex continuous_coneProfile coneProfile_zero d.centre hγ) ⊆
      d.chart.target) (t : stdSimplex ℝ (Fin 3)) :
    d.chart (mapSimplex d.chart.symm d.chart.continuousOn_symm
      (coneSimplex continuous_coneProfile coneProfile_zero d.centre hγ) hC t) =
      coneSimplex continuous_coneProfile coneProfile_zero d.centre hγ t := by
  rw [mapSimplex_apply, d.chart.right_inv (hC ⟨t, rfl⟩)]

/-- The root cone over an `eᵢ`-th root of `γ - s₀` is an `eᵢ`-th root of the reading of the
pulled-back flat cone, minus the branch value. -/
theorem coneSimplex_rootProfile_pow_eq_chart_sub
    (hC : range (coneSimplex continuous_coneProfile coneProfile_zero d.centre hγ) ⊆
      d.chart.target) (i : d.ι) {R : ℝ → ℂ} (hR : ContinuousOn R (Icc 0 1))
    (hRγ : ∀ y ∈ Icc (0 : ℝ) 1, R y ^ d.index i = γ y - d.centre) (t : stdSimplex ℝ (Fin 3)) :
    coneSimplex (continuous_rootProfile (d.index i)) (rootProfile_zero _) (0 : ℂ) hR t ^
        d.index i =
      d.chart (mapSimplex d.chart.symm d.chart.continuousOn_symm
        (coneSimplex continuous_coneProfile coneProfile_zero d.centre hγ) hC t) - d.centre := by
  rw [d.chart_mapSimplex_coneSimplex hC, coneSimplex_rootProfile_pow (d.index_pos i) hR hγ hRγ]

/-- **The lifts of a flat cone from the branch value in one branched disc.** Let `C` be the
flat cone from the branch value `s₀` over an arc `γ` of the disc, read through the chart, and
`R` a continuous `eᵢ`-th root of `γ - s₀` on `[0, 1]` (so `γ` avoids `s₀`). The lifts of `C` in
the `i`-th branched disc are the `wᵢ⁻¹ ∘ cone(rootProfile eᵢ, 0, u R)` for the `eᵢ`-th roots of
unity `u`. -/
theorem simplexLifts_coneSimplex_inter_eq
    (hC : range (coneSimplex continuous_coneProfile coneProfile_zero d.centre hγ) ⊆
      d.chart.target)
    (hγδ : ∀ y ∈ Icc (0 : ℝ) 1, ‖γ y - d.centre‖ < d.radius) (i : d.ι) {R : ℝ → ℂ}
    (hR : ContinuousOn R (Icc 0 1)) (hRγ : ∀ y ∈ Icc (0 : ℝ) 1, R y ^ d.index i = γ y - d.centre)
    (hγs : ∀ y ∈ Icc (0 : ℝ) 1, γ y ≠ d.centre) :
    simplexLifts p (mapSimplex d.chart.symm d.chart.continuousOn_symm
        (coneSimplex continuous_coneProfile coneProfile_zero d.centre hγ) hC) ∩
        {T' | ∀ t, T' t ∈ (d.coord i).source} =
      {T' | ∃ u : ℂ, u ^ d.index i = 1 ∧ ∀ t, T' t = (d.coord i).symm
        (coneSimplex (continuous_rootProfile (d.index i)) (rootProfile_zero _) (0 : ℂ)
          (hR.const_smul u) t)} := by
  rw [d.simplexLifts_inter_eq (d.isOver_coneSimplex hC hγδ) i
    (coneSimplex (continuous_rootProfile (d.index i)) (rootProfile_zero _) (0 : ℂ) hR)
    (d.coneSimplex_rootProfile_pow_eq_chart_sub hC i hR hRγ)
    (isPreconnected_coneSimplex_rootProfile_ne_zero (d.index_pos i) hR
      fun y hy ↦ ne_zero_of_pow_eq_sub (d.index_pos i) (hRγ y hy) (hγs y hy))]
  ext T'
  refine exists_congr fun u ↦ and_congr_right fun _ ↦ forall_congr' fun t ↦ ?_
  rw [coneSimplex_zero_smul]

/-- **A flat cone from the branch value has `eᵢ` lifts in the `i`-th branched disc.** -/
theorem ncard_simplexLifts_coneSimplex_inter
    (hC : range (coneSimplex continuous_coneProfile coneProfile_zero d.centre hγ) ⊆
      d.chart.target)
    (hγδ : ∀ y ∈ Icc (0 : ℝ) 1, ‖γ y - d.centre‖ < d.radius) (i : d.ι) {R : ℝ → ℂ}
    (hR : ContinuousOn R (Icc 0 1)) (hRγ : ∀ y ∈ Icc (0 : ℝ) 1, R y ^ d.index i = γ y - d.centre)
    (hγs : ∀ y ∈ Icc (0 : ℝ) 1, γ y ≠ d.centre) :
    (simplexLifts p (mapSimplex d.chart.symm d.chart.continuousOn_symm
        (coneSimplex continuous_coneProfile coneProfile_zero d.centre hγ) hC) ∩
        {T' | ∀ t, T' t ∈ (d.coord i).source}).ncard = d.index i := by
  have he := d.index_pos i
  have hR0 : ∀ y ∈ Icc (0 : ℝ) 1, R y ≠ 0 := fun y hy ↦
    ne_zero_of_pow_eq_sub he (hRγ y hy) (hγs y hy)
  have hT := d.isOver_coneSimplex hC hγδ
  set L := coneSimplex (continuous_rootProfile (d.index i)) (rootProfile_zero _) (0 : ℂ) hR
  have hL := d.coneSimplex_rootProfile_pow_eq_chart_sub hC i hR hRγ
  rw [d.simplexLifts_inter_eq hT i L hL (isPreconnected_coneSimplex_rootProfile_ne_zero he hR hR0)]
  -- a point off the apex
  let t₁ : stdSimplex ℝ (Fin 3) := ⟨_, single_mem_stdSimplex ℝ 1⟩
  have ht₁ : L t₁ ≠ 0 := by
    rw [coneSimplex_rootProfile_ne_zero_iff he hR hR0, Finset.sum_pair (by decide)]
    simp [t₁]
  have key : ((nthRootsFinset (d.index i) (1 : ℂ) : Finset ℂ) : Set ℂ).ncard =
      {T' : Simplex Y 2 | ∃ u : ℂ, u ^ d.index i = 1 ∧
        ∀ t, T' t = (d.coord i).symm (u * L t)}.ncard := by
    refine Set.ncard_congr (fun u hu ↦ mapSimplex (d.coord i).symm (d.coord i).continuousOn_symm
      (u • L) (d.range_smul_subset_target hT i L hL ((mem_nthRootsFinset he _).1 hu)))
      (fun u hu ↦ ⟨u, (mem_nthRootsFinset he _).1 hu, fun t ↦ rfl⟩)
      (fun u v hu hv h ↦ ?_)
      (fun T' ⟨u, hu, hT'⟩ ↦ ⟨u, Finset.mem_coe.2 ((mem_nthRootsFinset he _).2 hu), ?_⟩)
    · have h1 := congrArg (fun f : Simplex Y 2 ↦ d.coord i (f t₁)) h
      simp only [mapSimplex_apply, ContinuousMap.smul_apply, smul_eq_mul] at h1
      rw [d.coord_coord_symm_mul hT i L hL ((mem_nthRootsFinset he _).1 hu),
        d.coord_coord_symm_mul hT i L hL ((mem_nthRootsFinset he _).1 hv)] at h1
      exact mul_right_cancel₀ ht₁ h1
    · ext t
      exact (hT' t).symm
  rw [← key, Set.ncard_coe_finset, (Complex.isPrimitiveRoot_exp _ he.ne').card_nthRootsFinset]

/-- **The lifts of a flat cone from the branch value are finite.** -/
theorem finite_simplexLifts_coneSimplex
    (hC : range (coneSimplex continuous_coneProfile coneProfile_zero d.centre hγ) ⊆
      d.chart.target)
    (hγδ : ∀ y ∈ Icc (0 : ℝ) 1, ‖γ y - d.centre‖ < d.radius) {R : d.ι → ℝ → ℂ}
    (hR : ∀ i, ContinuousOn (R i) (Icc 0 1))
    (hRγ : ∀ i, ∀ y ∈ Icc (0 : ℝ) 1, R i y ^ d.index i = γ y - d.centre)
    (hγs : ∀ y ∈ Icc (0 : ℝ) 1, γ y ≠ d.centre) :
    (simplexLifts p (mapSimplex d.chart.symm d.chart.continuousOn_symm
        (coneSimplex continuous_coneProfile coneProfile_zero d.centre hγ) hC)).Finite := by
  have hR0 : ∀ i, ∀ y ∈ Icc (0 : ℝ) 1, R i y ≠ 0 := fun i y hy ↦
    ne_zero_of_pow_eq_sub (d.index_pos i) (hRγ i y hy) (hγs y hy)
  exact d.finite_simplexLifts (d.isOver_coneSimplex hC hγδ)
    (fun i ↦ coneSimplex (continuous_rootProfile (d.index i)) (rootProfile_zero _) (0 : ℂ) (hR i))
    (fun i ↦ d.coneSimplex_rootProfile_pow_eq_chart_sub hC i (hR i) (hRγ i))
    (fun i ↦ isPreconnected_coneSimplex_rootProfile_ne_zero (d.index_pos i) (hR i) (hR0 i))

/-- **The lifts of a flat cone from the branch value restrict bijectively to the lifts of its
faces.** This is the hypothesis of `bd_transfer_eq_zero_of_bijOn` at a cone from a branch
value, given continuous `eᵢ`-th roots of `γ - s₀` along the arc in every branched disc. -/
theorem bijOn_comp_face_coneSimplex
    (hC : range (coneSimplex continuous_coneProfile coneProfile_zero d.centre hγ) ⊆
      d.chart.target)
    (hγδ : ∀ y ∈ Icc (0 : ℝ) 1, ‖γ y - d.centre‖ < d.radius) {R : d.ι → ℝ → ℂ}
    (hR : ∀ i, ContinuousOn (R i) (Icc 0 1))
    (hRγ : ∀ i, ∀ y ∈ Icc (0 : ℝ) 1, R i y ^ d.index i = γ y - d.centre)
    (hγs : ∀ y ∈ Icc (0 : ℝ) 1, γ y ≠ d.centre) (j : Fin 3) :
    BijOn (fun T' : Simplex Y 2 ↦ T'.comp (face 1 j))
      (simplexLifts p (mapSimplex d.chart.symm d.chart.continuousOn_symm
        (coneSimplex continuous_coneProfile coneProfile_zero d.centre hγ) hC))
      (simplexLifts p ((mapSimplex d.chart.symm d.chart.continuousOn_symm
        (coneSimplex continuous_coneProfile coneProfile_zero d.centre hγ) hC).comp
          (face 1 j))) := by
  have hR0 : ∀ i, ∀ y ∈ Icc (0 : ℝ) 1, R i y ≠ 0 := fun i y hy ↦
    ne_zero_of_pow_eq_sub (d.index_pos i) (hRγ i y hy) (hγs y hy)
  exact d.bijOn_comp_face (d.isOver_coneSimplex hC hγδ)
    (fun i ↦ coneSimplex (continuous_rootProfile (d.index i)) (rootProfile_zero _) (0 : ℂ) (hR i))
    (fun i ↦ d.coneSimplex_rootProfile_pow_eq_chart_sub hC i (hR i) (hRγ i))
    (fun i ↦ isPreconnected_coneSimplex_rootProfile_ne_zero (d.index_pos i) (hR i) (hR0 i)) j
    (fun i ↦ (isPreconnected_and_exists_coneSimplex_rootProfile_face_ne_zero (d.index_pos i) (hR i)
      (hR0 i) j).1)
    (fun i ↦ (isPreconnected_and_exists_coneSimplex_rootProfile_face_ne_zero (d.index_pos i) (hR i)
      (hR0 i) j).2)

/-- The cone of profile `rootProfile eᵢ` over a unit multiple of an `eᵢ`-th root of `γ - s₀`
sends the square into the target of the `i`-th branched coordinate, the hypothesis of
`exists_reading_rootCone`. -/
theorem mapsTo_coneMap_rootProfile (i : d.ι) {R : ℝ → ℂ}
    (hRγ : ∀ y ∈ Icc (0 : ℝ) 1, R y ^ d.index i = γ y - d.centre)
    (hγδ : ∀ y ∈ Icc (0 : ℝ) 1, ‖γ y - d.centre‖ < d.radius) {u : ℂ} (hu : ‖u‖ = 1) :
    MapsTo (CurveCupPositivity.coneMap (rootProfile (d.index i)) 0 (u • R)) unitSquare
      (d.coord i).target := by
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  refine d.mem_target i _ ?_
  simp only [coneMap_apply, Pi.smul_apply, smul_eq_mul, sub_zero, zero_add, Complex.real_smul,
    mul_pow, norm_mul]
  rw [← Complex.ofReal_pow, rootProfile_pow (d.index_pos i), hRγ y hy, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (coneProfile_nonneg x), norm_pow, hu, one_pow, one_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (coneProfile_le_one hx.2)).trans_lt (hγδ y hy)

end RamifiedDisc

end ConeLifts

/-! ### Readings of the lifts in a chart -/

section Reading

/-- **A holomorphic map scales the Jacobian by `|h'|²`.** For `h : ℂ → ℂⁿ` complex
differentiable at `G q`, the Jacobian of the `i`-th coordinate of `h ∘ G` at `q` is
`|∂hᵢ|² Im(conj(∂₁ G) ∂₂ G)`. -/
theorem im_star_fderiv_comp_eq {n : ℕ} {h : ℂ → Fin n → ℂ} {G : ℝ × ℝ → ℂ} {q : ℝ × ℝ}
    (hh : DifferentiableAt ℂ h (G q)) (hG : DifferentiableAt ℝ G q) (i : Fin n) :
    (star (fderiv ℝ (fun x ↦ h (G x)) q (1, 0) i) * fderiv ℝ (fun x ↦ h (G x)) q (0, 1) i).im =
      Complex.normSq (deriv h (G q) i) *
        (star (fderiv ℝ G q (1, 0)) * fderiv ℝ G q (0, 1)).im := by
  have hd : HasFDerivAt (fun x ↦ h (G x))
      (((ContinuousLinearMap.toSpanSingleton ℂ (deriv h (G q))).restrictScalars ℝ).comp
        (fderiv ℝ G q)) q :=
    (hh.hasDerivAt.hasFDerivAt.restrictScalars ℝ).comp q hG.hasFDerivAt
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    Pi.smul_apply, smul_eq_mul]
  set c := deriv h (G q) i
  rw [show star (fderiv ℝ G q (1, 0) * c) * (fderiv ℝ G q (0, 1) * c) =
      ((Complex.normSq c : ℝ) : ℂ) * (star (fderiv ℝ G q (1, 0)) * fderiv ℝ G q (0, 1)) by
    rw [Complex.normSq_eq_conj_mul_self, star_mul', Complex.star_def]; ring,
    Complex.im_ofReal_mul]

/-- **The turning of an `e`-th root.** If `R ^ e = γ - s₀` near `y`, the turning of `γ` around
`s₀` is `e |R|^{2(e-1)}` times the turning of `R` around `0`. -/
theorem im_star_sub_mul_deriv_eq_of_pow_eq {R γ : ℝ → ℂ} {s₀ : ℂ} {e : ℕ} (he : 0 < e) {y : ℝ}
    (hRγ : ∀ᶠ y' in nhds y, R y' ^ e = γ y' - s₀) (hR : DifferentiableAt ℝ R y) :
    (star (γ y - s₀) * deriv γ y).im =
      e * Complex.normSq (R y) ^ (e - 1) * (star (R y) * deriv R y).im := by
  have hγ : γ =ᶠ[nhds y] fun y' ↦ s₀ + R y' ^ e := by
    filter_upwards [hRγ] with y' hy'
    rw [hy']; ring
  have hd : HasDerivAt γ ((e : ℂ) * R y ^ (e - 1) * deriv R y) y := by
    have := (hR.hasDerivAt.pow e).const_add s₀
    exact this.congr_of_eventuallyEq hγ
  rw [hd.deriv, ← hRγ.self_of_nhds]
  obtain ⟨m, rfl⟩ : ∃ m, e = m + 1 := ⟨e - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [show star (R y ^ (m + 1)) * ((((m + 1 : ℕ) : ℂ)) * R y ^ m * deriv R y) =
      ((((m + 1 : ℕ) : ℝ) * Complex.normSq (R y) ^ m : ℝ) : ℂ) * (star (R y) * deriv R y) by
    push_cast
    rw [Complex.normSq_eq_conj_mul_self, star_pow, Complex.star_def]; ring,
    Complex.im_ofReal_mul]

/-- The turning of an `e`-th root has the sign of the turning of the curve. -/
theorem im_star_mul_deriv_nonneg_of_pow_eq {R γ : ℝ → ℂ} {s₀ : ℂ} {e : ℕ} (he : 0 < e) {y : ℝ}
    (hRγ : ∀ᶠ y' in nhds y, R y' ^ e = γ y' - s₀) (hR : DifferentiableAt ℝ R y)
    (hγs : γ y ≠ s₀) (hturn : 0 ≤ (star (γ y - s₀) * deriv γ y).im) :
    0 ≤ (star (R y) * deriv R y).im := by
  rw [im_star_sub_mul_deriv_eq_of_pow_eq he hRγ hR] at hturn
  have hpos : 0 < (e : ℝ) * Complex.normSq (R y) ^ (e - 1) := mul_pos (by exact_mod_cast he)
    (pow_pos (Complex.normSq_pos.2 (ne_zero_of_pow_eq_sub he hRγ.self_of_nhds hγs)) _)
  exact (mul_nonneg_iff_of_pos_left hpos).1 hturn

/-- Multiplying a curve by a unit complex number does not change its turning around `0`. -/
theorem im_star_smul_mul_deriv {R : ℝ → ℂ} {u : ℂ} (hu : ‖u‖ = 1) {y : ℝ}
    (hR : DifferentiableAt ℝ R y) :
    (star ((u • R) y) * deriv (u • R) y).im = (star (R y) * deriv R y).im := by
  rw [show deriv (u • R) y = u * deriv R y from (hR.hasDerivAt.const_smul u).deriv,
    Pi.smul_apply, smul_eq_mul, show star (u * R y) * (u * deriv R y) =
      ((Complex.normSq u : ℝ) : ℂ) * (star (R y) * deriv R y) by
    rw [Complex.normSq_eq_conj_mul_self, star_mul', Complex.star_def]; ring,
    Complex.normSq_eq_norm_sq, hu]
  simp

/-- The cone over `γ` on the square has its range in any set into which the cone map sends the
square. -/
theorem range_coneSimplex_subset_of_mapsTo {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hρ0 : ρ 0 = 0) (P : E) {γ : ℝ → E}
    (hγ : ContinuousOn γ (Icc 0 1)) {S : Set E}
    (hT : MapsTo (CurveCupPositivity.coneMap ρ P γ) unitSquare S) :
    range (coneSimplex hρ hρ0 P hγ) ⊆ S := by
  rintro _ ⟨t, rfl⟩
  have h1 := stdSimplex_apply_nonneg t 1
  have h2 := stdSimplex_apply_nonneg t 2
  have hs1 : t 1 + t 2 ≤ 1 := by
    linarith [stdSimplex_three_add t, stdSimplex_apply_nonneg t 0]
  have hu : t 2 / (t 1 + t 2) ∈ Icc (0 : ℝ) 1 := by
    rcases eq_or_lt_of_le (add_nonneg h1 h2 : 0 ≤ t 1 + t 2) with h0 | h0
    · rw [← h0, div_zero]; exact ⟨le_rfl, zero_le_one⟩
    · exact ⟨div_nonneg h2 h0.le, (div_le_one h0).2 (by linarith)⟩
  have hp : (t 1 + t 2, t 2 / (t 1 + t 2)) ∈ unitSquare := ⟨⟨add_nonneg h1 h2, hs1⟩, hu⟩
  have := hT hp
  simp only [coneMap_apply] at this
  change P + ρ (t 1 + t 2) • (clampCurve γ (t 2 / (t 1 + t 2)) - P) ∈ S
  rw [clampCurve_of_mem _ hu]
  exact this

/-- **The reading of a lift of a cone from a branch value.** Let `φ` be a branched coordinate of
`Y` whose source lies in the source of a chart `c` of `Y`, with `c ∘ φ⁻¹` holomorphic on the
target of `φ`, and let `R` be `C²` on an open `V ⊇ [0, 1]`, turning counterclockwise around `0`.
If the cone with profile `rootProfile e` from `0` over `R` sends the square into the target of
`φ`, the lift `φ⁻¹ ∘ cone` is read on the square, through the collapse, as `c⁻¹ ∘ g` for
`g = c ∘ φ⁻¹ ∘ CurveCupPositivity.coneMap`, which is `C²` on an open neighbourhood `U` of the
square, maps `U` into the target of `c`, and has nonnegative Jacobian on `U` in every
coordinate. -/
theorem exists_reading_rootCone {Y : Type*} [TopologicalSpace Y] {n : ℕ}
    (c : OpenPartialHomeomorph Y (Fin n → ℂ)) (φ : OpenPartialHomeomorph Y ℂ)
    (hφc : φ.source ⊆ c.source)
    (han : ∀ w ∈ φ.target, AnalyticAt ℂ (fun w ↦ c (φ.symm w)) w) {e : ℕ} {R : ℝ → ℂ}
    {V : Set ℝ} (hVo : IsOpen V) (hV : Icc (0 : ℝ) 1 ⊆ V) (hR : ContDiffOn ℝ 2 R V)
    (hturn : ∀ y ∈ V, 0 ≤ (star (R y) * deriv R y).im)
    (hT : MapsTo (CurveCupPositivity.coneMap (rootProfile e) 0 R) unitSquare φ.target) :
    ∃ (hσ : range (coneSimplex (continuous_rootProfile e) (rootProfile_zero e) (0 : ℂ)
        (hR.continuousOn.mono hV)) ⊆ φ.target) (U : Set (ℝ × ℝ)),
      IsOpen U ∧ unitSquare ⊆ U ∧
      ContDiffOn ℝ 2 (fun q ↦ c (φ.symm (CurveCupPositivity.coneMap (rootProfile e) 0 R q))) U ∧
      MapsTo (fun q ↦ c (φ.symm (CurveCupPositivity.coneMap (rootProfile e) 0 R q))) U c.target ∧
      (∀ q ∈ unitSquare, mapSimplex φ.symm φ.continuousOn_symm
        (coneSimplex (continuous_rootProfile e) (rootProfile_zero e) (0 : ℂ)
          (hR.continuousOn.mono hV)) hσ (squareCollapse q) =
            c.symm (c (φ.symm (CurveCupPositivity.coneMap (rootProfile e) 0 R q)))) ∧
      ∀ q ∈ U, ∀ i : Fin n,
        0 ≤ (star (fderiv ℝ (fun q ↦ c (φ.symm (CurveCupPositivity.coneMap (rootProfile e) 0 R q)))
            q (1, 0) i) *
          fderiv ℝ (fun q ↦ c (φ.symm (CurveCupPositivity.coneMap (rootProfile e) 0 R q)))
            q (0, 1) i).im := by
  set G := CurveCupPositivity.coneMap (rootProfile e) (0 : ℂ) R
  have hG : ContDiffOn ℝ 2 G (univ ×ˢ V) :=
    contDiffOn_coneMap (contDiff_rootProfile e (by simp)) hR
  have hσ := range_coneSimplex_subset_of_mapsTo (continuous_rootProfile e) (rootProfile_zero e)
    (0 : ℂ) (hR.continuousOn.mono hV) hT
  obtain ⟨U, hUo, hsU, hUW, hUT⟩ := exists_isOpen_mapsTo_of_square (isOpen_univ.prod hVo)
    (unitSquare_subset_univ_prod hV) hG.continuousOn φ.open_target hT
  have hGat : ∀ q ∈ U, ContDiffAt ℝ 2 G q := fun q hq ↦
    hG.contDiffAt ((isOpen_univ.prod hVo).mem_nhds (hUW hq))
  have hhat : ∀ q ∈ U, ContDiffAt ℝ 2 (fun w ↦ c (φ.symm w)) (G q) := fun q hq ↦
    ((han _ (hUT hq)).contDiffAt (n := 2)).restrict_scalars ℝ
  refine ⟨hσ, U, hUo, hsU, fun q hq ↦ ((hhat q hq).comp q (hGat q hq)).contDiffWithinAt,
    fun q hq ↦ c.map_source (hφc (φ.map_target (hUT hq))), fun q hq ↦ ?_, fun q hq i ↦ ?_⟩
  · rw [mapSimplex_apply, coneSimplex_squareCollapse _ _ _ _ hq,
      c.left_inv (hφc (φ.map_target (hT hq)))]
  · obtain ⟨x, y⟩ := q
    have hy : y ∈ V := (hUW hq).2
    have hRd : DifferentiableAt ℝ R y :=
      (hR.contDiffAt (hVo.mem_nhds hy)).differentiableAt (by norm_num)
    have hρd : DifferentiableAt ℝ (rootProfile e) x := differentiable_rootProfile e x
    rw [im_star_fderiv_comp_eq ((han _ (hUT hq)).differentiableAt)
      ((hGat _ hq).differentiableAt (by norm_num))]
    refine mul_nonneg (Complex.normSq_nonneg _) ?_
    rw [fderiv_coneMap_one_zero hρd hRd, fderiv_coneMap_zero_one hρd hRd]
    have h1 := im_ofReal_mul_star_mul_ofReal_mul (deriv (rootProfile e) x) (rootProfile e x)
      (R y) (deriv R y)
    simp only [Complex.star_def] at h1
    simp only [sub_zero, Complex.real_smul, star_mul', Complex.star_def, Complex.conj_ofReal]
    rw [h1]
    exact mul_nonneg (rootProfile_mul_deriv_nonneg e x) (hturn y hy)

end Reading

/-! ### Smooth roots along an arc -/

section SmoothRoot

/-- **A smooth `e`-th root away from a ray.** If `a (γ - s₀)` stays in the slit
plane on `V` for some `a ≠ 0`, then `γ - s₀` has an `e`-th root `C²` on `V`, through the
principal logarithm. -/
theorem exists_contDiffOn_pow_eq_sub {γ : ℝ → ℂ} {s₀ a : ℂ} {V : Set ℝ} {e : ℕ} (he : 0 < e)
    (ha : a ≠ 0) (hγ : ContDiffOn ℝ 2 γ V) (hslit : ∀ y ∈ V, a * (γ y - s₀) ∈ Complex.slitPlane) :
    ∃ R : ℝ → ℂ, ContDiffOn ℝ 2 R V ∧ ∀ y ∈ V, R y ^ e = γ y - s₀ := by
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq a⁻¹ he
  refine ⟨fun y ↦ b * Complex.exp (Complex.log (a * (γ y - s₀)) / e), ?_, fun y hy ↦ ?_⟩
  · have hin : ContDiffOn ℝ 2 (fun y ↦ a * (γ y - s₀)) V :=
      contDiffOn_const.mul (hγ.sub contDiffOn_const)
    have hlog : ContDiffOn ℝ 2 (fun y ↦ Complex.log (a * (γ y - s₀))) V := fun y hy ↦ by
      have h1 : ContDiffAt ℝ 2 Complex.log (a * (γ y - s₀)) :=
        (Complex.contDiffAt_log (hslit y hy)).restrict_scalars ℝ
      exact h1.comp_contDiffWithinAt y (hin y hy)
    exact contDiffOn_const.mul ((hlog.div_const _).cexp)
  · change (b * Complex.exp (Complex.log (a * (γ y - s₀)) / e)) ^ e = _
    rw [mul_pow, ← Complex.exp_nat_mul, mul_div_cancel₀ _ (by exact_mod_cast he.ne'),
      Complex.exp_log (mul_ne_zero ha fun h ↦ by
        have := hslit y hy; rw [h, mul_zero] at this; exact Complex.zero_notMem_slitPlane this),
      hb, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]

/-- The turning of a flat segment in `ℂ` around a point `P`. -/
theorem im_star_sub_mul_deriv_segmentCurve_complex (P b c : ℂ) (y : ℝ) :
    (star (segmentCurve b c y - P) * deriv (segmentCurve b c) y).im =
      deriv coneProfile y * (star (b - P) * (c - b)).im := by
  rw [deriv_segmentCurve]
  simp only [segmentCurve, Complex.real_smul, star_add, star_sub, star_mul', Complex.star_def,
    Complex.conj_ofReal]
  simp only [Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **A smooth `e`-th root along a flat segment.** If `P` lies strictly on the left of `b → c`,
the flat segment minus `P` has an `e`-th root smooth on `ℝ`, turning counterclockwise around
`0` everywhere. -/
theorem exists_contDiff_pow_eq_segmentCurve_sub {P b c : ℂ} {e : ℕ} (he : 0 < e)
    (hleft : 0 < (star (b - P) * (c - b)).im) :
    ∃ R : ℝ → ℂ, ContDiff ℝ 2 R ∧ (∀ y, R y ^ e = segmentCurve b c y - P) ∧
      ∀ y, 0 ≤ (star (R y) * deriv R y).im := by
  have hcb : c - b ≠ 0 := fun h ↦ by rw [h, mul_zero, Complex.zero_im] at hleft; exact hleft.false
  set a := Complex.I * star (c - b)
  have ha : a ≠ 0 := mul_ne_zero Complex.I_ne_zero (star_ne_zero.2 hcb)
  have hslit : ∀ y ∈ (univ : Set ℝ), a * (segmentCurve b c y - P) ∈ Complex.slitPlane := by
    intro y _
    refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
    have : (a * (segmentCurve b c y - P)).re = (star (b - P) * (c - b)).im := by
      simp only [a, segmentCurve, Complex.real_smul, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im, Complex.sub_re,
        Complex.sub_im, Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
        Complex.ofReal_im]
      ring
    rw [this]; exact hleft
  obtain ⟨R, hR, hRγ⟩ := exists_contDiffOn_pow_eq_sub he ha
    (contDiff_segmentCurve b c (by simp)).contDiffOn hslit
  have hR' : ContDiff ℝ 2 R := contDiffOn_univ.1 hR
  refine ⟨R, hR', fun y ↦ hRγ y (mem_univ y), fun y ↦ ?_⟩
  have hne : segmentCurve b c y ≠ P := fun h ↦ by
    have := hslit y (mem_univ y); rw [h, sub_self, mul_zero] at this
    exact Complex.zero_notMem_slitPlane this
  refine im_star_mul_deriv_nonneg_of_pow_eq he (Filter.Eventually.of_forall fun y' ↦
    hRγ y' (mem_univ y')) (hR'.differentiable (by norm_num) y) hne ?_
  rw [im_star_sub_mul_deriv_segmentCurve_complex]
  exact mul_nonneg (deriv_coneProfile_nonneg y) hleft.le

end SmoothRoot

/-! ### The local normal form of a map holomorphic in charts -/

section NormalForm

/-- If `E⁻¹` is holomorphic on the target of `E`, then for a one-dimensional chart `c` of `Y` and
`φ = (κ ∘ c) ≫ E`, with `κ` the identification `(Fin 1 → ℂ) ≃ ℂ`, the map `c ∘ φ⁻¹` is
holomorphic on the target of `φ`. -/
theorem analyticAt_comp_symm_transHomeomorph_trans {Y : Type*} [TopologicalSpace Y]
    (c : OpenPartialHomeomorph Y (Fin 1 → ℂ)) (E : OpenPartialHomeomorph ℂ ℂ)
    (hE : ∀ w ∈ E.target, AnalyticAt ℂ E.symm w) {w : ℂ}
    (hw : w ∈ ((c.transHomeomorph
      (ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ).toHomeomorph).trans E).target) :
    AnalyticAt ℂ (fun w ↦ c (((c.transHomeomorph
      (ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ).toHomeomorph).trans E).symm w)) w := by
  set κ := ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ
  set φ := (c.transHomeomorph κ.toHomeomorph).trans E
  have htgt : ∀ w' ∈ φ.target, w' ∈ E.target ∧ κ.symm (E.symm w') ∈ c.target := fun w' hw' ↦ by
    rw [OpenPartialHomeomorph.trans_target] at hw'
    refine ⟨hw'.1, ?_⟩
    have h2 := hw'.2
    simp only [Set.mem_preimage, OpenPartialHomeomorph.transHomeomorph_target] at h2
    exact h2
  have hev : (fun w ↦ c (φ.symm w)) =ᶠ[nhds w] fun w ↦ κ.symm (E.symm w) := by
    filter_upwards [φ.open_target.mem_nhds hw] with w' hw'
    have h1 : φ.symm w' = c.symm (κ.symm (E.symm w')) := rfl
    rw [h1, c.right_inv (htgt w' hw').2]
  exact (((κ.symm : ℂ →L[ℂ] (Fin 1 → ℂ)).analyticAt _).comp (hE w (htgt w hw).1)).congr hev.symm

/-- **The local normal form of a map that is holomorphic in charts.** Let `p : Y → Z` be
continuous at `q`, with `zc ∘ p ∘ c⁻¹` holomorphic at `c q` for a one-dimensional chart `c` of `Y`
at `q` and a chart `zc` of `Z` at `p q`, and not locally constant at `q`. Then near `q`,
`zc ∘ p = zc (p q) + φ ^ e` for some `e ≥ 1` and a coordinate `φ` centred at `q`, with source in
a given neighbourhood of `q` and in the source of `c`, and `c ∘ φ⁻¹` holomorphic. -/
theorem exists_pow_normalForm_of_analyticAt {Y Z : Type*} [TopologicalSpace Y]
    [TopologicalSpace Z] {p : Y → Z} (c : OpenPartialHomeomorph Y (Fin 1 → ℂ))
    (zc : OpenPartialHomeomorph Z ℂ) {q : Y} (hq : q ∈ c.source) (hpq : p q ∈ zc.source)
    (hp : ContinuousAt p q) (han : AnalyticAt ℂ (fun v ↦ zc (p (c.symm v))) (c q))
    (hnc : ¬ ∀ᶠ y in nhds q, zc (p y) = zc (p q)) {N : Set Y} (hN : N ∈ nhds q) :
    ∃ (e : ℕ) (φ : OpenPartialHomeomorph Y ℂ), 0 < e ∧ q ∈ φ.source ∧
      φ.source ⊆ c.source ∩ N ∧ φ q = 0 ∧
      (∀ y ∈ φ.source, p y ∈ zc.source ∧ zc (p y) = zc (p q) + φ y ^ e) ∧
      ∀ w ∈ φ.target, AnalyticAt ℂ (fun w ↦ c (φ.symm w)) w := by
  set κ := ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ
  set G' : ℂ → ℂ := fun z ↦ zc (p (c.symm (κ.symm z)))
  set z₀ := κ (c q)
  have hκz₀ : κ.symm z₀ = c q := κ.symm_apply_apply _
  have hG' : AnalyticAt ℂ G' z₀ := by
    have h1 : AnalyticAt ℂ (fun v ↦ zc (p (c.symm v))) (κ.symm z₀) := hκz₀ ▸ han
    exact h1.comp ((κ.symm : ℂ →L[ℂ] (Fin 1 → ℂ)).analyticAt _)
  have hG'q : G' z₀ = zc (p q) := by simp only [G', hκz₀, c.left_inv hq]
  -- the reading back of `y` near `q`
  have hcont : ContinuousAt (fun y ↦ κ (c y)) q :=
    κ.continuous.continuousAt.comp (c.continuousAt hq)
  have hback : ∀ y ∈ c.source, G' (κ (c y)) = zc (p y) := fun y hy ↦ by
    simp only [G', κ.symm_apply_apply, c.left_inv hy]
  have hnc' : ¬ ∀ᶠ z in nhds z₀, G' z = G' z₀ := by
    intro hev
    apply hnc
    filter_upwards [hcont.eventually hev, c.open_source.mem_nhds hq] with y h1 h2
    rw [← hback y h2, h1, hG'q]
  obtain ⟨n, ψ, hn, hψa, hψd, hψ0, hψeq⟩ := exists_analyticAt_pow_normalForm hG' hnc'
  -- the neighbourhood of `q` on which everything is defined
  set M := c.source ∩ N ∩ p ⁻¹' zc.source
  have hM : M ∈ nhds q :=
    Filter.inter_mem (Filter.inter_mem (c.open_source.mem_nhds hq) hN)
      (hp.preimage_mem_nhds (zc.open_source.mem_nhds hpq))
  have hcs : ContinuousAt (fun z ↦ c.symm (κ.symm z)) z₀ := by
    refine ContinuousAt.comp (f := fun z ↦ κ.symm z) ?_ κ.symm.continuous.continuousAt
    rw [hκz₀]
    exact c.continuousAt_symm (c.map_source hq)
  have hMz : (fun z ↦ c.symm (κ.symm z)) ⁻¹' M ∈ nhds z₀ := by
    refine hcs.preimage_mem_nhds ?_
    simpa only [hκz₀, c.left_inv hq] using hM
  have htz : κ.symm ⁻¹' c.target ∈ nhds z₀ := by
    refine κ.symm.continuous.continuousAt.preimage_mem_nhds ?_
    rw [hκz₀]
    exact c.open_target.mem_nhds (c.map_source hq)
  have hN' : {z | G' z = G' z₀ + ψ z ^ n} ∩ κ.symm ⁻¹' c.target ∩
      (fun z ↦ c.symm (κ.symm z)) ⁻¹' M ∈ nhds z₀ :=
    Filter.inter_mem (Filter.inter_mem hψeq htz) hMz
  obtain ⟨E, hz₀E, hEN, hEψ, -, hEsymm⟩ := exists_analytic_openPartialHomeomorph hψa hψd hN'
  set c' := c.transHomeomorph κ.toHomeomorph
  set φ := c'.trans E
  have hφsrc : ∀ y, y ∈ φ.source ↔ y ∈ c.source ∧ κ (c y) ∈ E.source := fun y ↦ by
    simp [φ, c']
  have hφapp : ∀ y, φ y = E (κ (c y)) := fun y ↦ rfl
  have hyM : ∀ y ∈ φ.source, y ∈ M := fun y hy ↦ by
    obtain ⟨hyc, hyE⟩ := (hφsrc y).1 hy
    have := (hEN hyE).2
    simpa only [Set.mem_preimage, κ.symm_apply_apply, c.left_inv hyc] using this
  refine ⟨n, φ, hn, (hφsrc q).2 ⟨hq, hz₀E⟩, fun y hy ↦ (hyM y hy).1, ?_, fun y hy ↦ ?_,
    fun w hw ↦ ?_⟩
  · rw [hφapp, hEψ hz₀E]
    exact hψ0
  · obtain ⟨hyc, hyE⟩ := (hφsrc y).1 hy
    refine ⟨(hyM y hy).2, ?_⟩
    rw [← hback y hyc, ← hG'q, hφapp, hEψ hyE]
    exact (hEN hyE).1.1
  · exact analyticAt_comp_symm_transHomeomorph_trans c E hEsymm hw

end NormalForm

/-! ### Ramified discs of a closed map with finite fibres -/

section ExistsRamifiedDisc

/-- A finite family of positive reals is bounded below by a positive real. -/
theorem exists_pos_forall_le_of_finite {ι : Type*} [Finite ι] {f : ι → ℝ} (hf : ∀ i, 0 < f i) :
    ∃ δ > 0, ∀ i, δ ≤ f i := by
  have := Fintype.ofFinite ι
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun i ↦ (IsEmpty.false i).elim⟩
  · obtain ⟨i₀, -, hi₀⟩ := Finset.univ.exists_min_image f Finset.univ_nonempty
    exact ⟨f i₀, hf i₀, fun i ↦ hi₀ i (Finset.mem_univ i)⟩

universe u v

variable {Y : Type u} {Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]

/-- A coordinate `φ` vanishing at `y₀` restricts, inside any open neighbourhood `O` of `y₀`, to a
coordinate at `y₀` whose target contains a disc around `0`. -/
theorem exists_restr_ball_subset_target (φ : OpenPartialHomeomorph Y ℂ) {y₀ : Y}
    (hy₀ : y₀ ∈ φ.source) (h0 : φ y₀ = 0) {O : Set Y} (hO : IsOpen O) (hyO : y₀ ∈ O) :
    ∃ r > 0, ∃ ψ : OpenPartialHomeomorph Y ℂ, y₀ ∈ ψ.source ∧ ψ.source ⊆ φ.source ∩ O ∧
      Metric.ball 0 r ⊆ ψ.target ∧ (∀ w ∈ ψ.target, w ∈ φ.target ∧ ψ.symm w = φ.symm w) ∧
      ∀ y ∈ ψ.source, ψ y = φ y := by
  have hn := φ.image_mem_nhds hy₀ ((φ.open_source.inter hO).mem_nhds ⟨hy₀, hyO⟩)
  rw [h0] at hn
  obtain ⟨r, hr, hrW⟩ := Metric.mem_nhds_iff.1 hn
  have hS : IsOpen (φ.source ∩ φ ⁻¹' Metric.ball 0 r ∩ O) :=
    (φ.isOpen_inter_preimage Metric.isOpen_ball).inter hO
  have htgt : ∀ w, w ∈ (φ.restrOpen _ hS).target ↔
      w ∈ φ.target ∧ φ.symm w ∈ φ.source ∩ φ ⁻¹' Metric.ball 0 r ∩ O :=
    fun w ↦ by simp [OpenPartialHomeomorph.restrOpen]
  refine ⟨r, hr, φ.restrOpen _ hS, ?_, ?_, fun w hw ↦ ?_, fun w hw ↦ ⟨((htgt w).1 hw).1, rfl⟩,
    fun y _ ↦ rfl⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    refine ⟨hy₀, ⟨hy₀, ?_⟩, hyO⟩
    rw [mem_preimage, h0]
    exact Metric.mem_ball_self hr
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact fun y hy ↦ ⟨hy.1, hy.2.2⟩
  · obtain ⟨y, ⟨hys, hyO⟩, rfl⟩ := hrW hw
    rw [htgt, φ.left_inv hys]
    exact ⟨φ.map_source hys, ⟨hys, hw⟩, hyO⟩

/-- For a closed map `p` and an open `U` containing the fibre over `s`, every point whose image
is close to `s` in a chart `zc` at `s` lies in `U`. -/
theorem exists_pos_forall_mem_of_isClosedMap {p : Y → Z} (hcl : IsClosedMap p)
    (zc : OpenPartialHomeomorph Z ℂ) {s : Z} (hs : s ∈ zc.source) {U : Set Y} (hU : IsOpen U)
    (hsU : p ⁻¹' {s} ⊆ U) :
    ∃ δ > 0, ∀ y, p y ∈ zc.source → zc (p y) ∈ Metric.ball (zc s) δ → y ∈ U := by
  have hK : IsClosed (p '' Uᶜ) := hcl _ hU.isClosed_compl
  have hB : zc.symm ⁻¹' (zc.source ∩ (p '' Uᶜ)ᶜ) ∈ nhds (zc s) := by
    refine (zc.continuousAt_symm (zc.map_source hs)).preimage_mem_nhds ?_
    rw [zc.left_inv hs]
    exact (zc.open_source.inter hK.isOpen_compl).mem_nhds
      ⟨hs, fun ⟨y, hyU, hys⟩ ↦ hyU (hsU hys)⟩
  obtain ⟨δ, hδ, hδB⟩ := Metric.mem_nhds_iff.1 hB
  refine ⟨δ, hδ, fun y hy hyδ ↦ ?_⟩
  have := hδB hyδ
  simp only [mem_preimage, zc.left_inv hy] at this
  by_contra h
  exact this.2 ⟨y, h, rfl⟩

/-- **A closed map with a finite fibre is a ramified disc near the fibre.** Let `p : Y → Z` be a
closed map, `Y` Hausdorff, whose fibre over `s` is finite, with a branched coordinate `φ_q`,
`zc ∘ p = zc s + φ_q ^ {e_q}`, at each point `q` of the fibre. Then over a small enough disc around
`zc s` in the chart `zc`, of radius at most a given `ε > 0`, `p` is a ramified disc whose
coordinates are restrictions of the `φ_q`. -/
theorem exists_ramifiedDisc [T2Space Y] {p : Y → Z} (hcl : IsClosedMap p)
    (zc : OpenPartialHomeomorph Z ℂ) {s : Z} (hs : s ∈ zc.source) (hfin : (p ⁻¹' {s}).Finite)
    (e : p ⁻¹' {s} → ℕ) (he : ∀ q, 0 < e q) (φ : p ⁻¹' {s} → OpenPartialHomeomorph Y ℂ)
    (hq : ∀ q, (q : Y) ∈ (φ q).source)
    (hnf : ∀ q, ∀ y ∈ (φ q).source, p y ∈ zc.source ∧ zc (p y) = zc s + φ q y ^ e q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ d : RamifiedDisc.{u, v, u} p, d.chart = zc ∧ d.centre = zc s ∧ 0 < d.radius ∧ d.radius ≤ ε ∧
      ∀ i, ∃ q, d.index i = e q ∧ (d.coord i).source ⊆ (φ q).source ∧
        ∀ w ∈ (d.coord i).target, w ∈ (φ q).target ∧ (d.coord i).symm w = (φ q).symm w := by
  have : Finite (p ⁻¹' {s}) := hfin.to_subtype
  obtain ⟨O, hO, hOd⟩ := hfin.t2_separation
  have h0 : ∀ q, φ q q = 0 := fun q ↦ by
    have h := (hnf q q (hq q)).2
    rw [show p q = s from q.2] at h
    exact (pow_eq_zero_iff (he q).ne').1 (by linear_combination -h)
  choose r hr coord hqc hsub hball htgt happ using fun q : p ⁻¹' {s} ↦
    exists_restr_ball_subset_target (φ q) (hq q) (h0 q) (hO q).2 (hO q).1
  -- the radius
  obtain ⟨δ₁, hδ₁, hδ₁r⟩ := exists_pos_forall_le_of_finite fun q ↦ pow_pos (hr q) (e q)
  obtain ⟨δ₂, hδ₂, hδ₂U⟩ := exists_pos_forall_mem_of_isClosedMap hcl zc hs
    (isOpen_iUnion fun q ↦ (coord q).open_source) fun y hys ↦ mem_iUnion.2 ⟨⟨y, hys⟩, hqc _⟩
  set δ := min (min δ₁ δ₂) ε
  have hδ : 0 < δ := lt_min (lt_min hδ₁ hδ₂) hε
  refine ⟨{ chart := zc
            centre := zc s
            radius := δ
            ι := p ⁻¹' {s}
            finite_ι := inferInstance
            index := e
            index_pos := he
            coord := coord
            normalForm := fun q y hy ↦ by
              rw [happ q y hy]
              exact hnf q y (hsub q hy).1
            mem_target := fun q w hw ↦ ?_
            exists_mem_source := fun y hy hyδ ↦ ?_
            pairwise_disjoint := fun i j hij ↦ ?_ }, rfl, rfl, hδ, min_le_right _ _,
          fun q ↦ ⟨q, rfl, fun y hy ↦ (hsub q hy).1, htgt q⟩⟩
  · -- the roots of small values lie in the target
    refine hball q (mem_ball_zero_iff.2 ((pow_lt_pow_iff_left₀ (norm_nonneg _) (hr q).le
      (he q).ne').1 ?_))
    rw [← norm_pow]
    exact hw.trans_le ((min_le_left _ _).trans ((min_le_left _ _).trans (hδ₁r q)))
  · -- the preimage of the disc is covered
    exact mem_iUnion.1 (hδ₂U y hy (by
      rw [Metric.mem_ball, dist_eq_norm]
      exact hyδ.trans_le ((min_le_left _ _).trans (min_le_right _ _))))
  · -- the coordinates have disjoint sources
    exact Disjoint.mono (fun y hy ↦ (hsub i hy).2) (fun y hy ↦ (hsub j hy).2)
      (hOd i.2 j.2 (Subtype.coe_injective.ne hij))

end ExistsRamifiedDisc

/-! ### Realized morphisms of curves -/

section Realize

open CategoryTheory AlgebraicGeometry MMP.Analytic.ComplexPoints

variable {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)}

/-- **The local normal form of a realized morphism of curves.** For a morphism `g : X ⟶ Y` over
`ℂ`, `X` smooth of relative dimension one, étale charts `c` at `q` and `c'` at `g(q)`, if the
realized map is not locally constant at `q` then near `q`, in the chart `c'` read in `ℂ`,
`c' ∘ g = c'(g q) + φ ^ e` for some `e ≥ 1` and a coordinate `φ` centred at `q`, with source in
`c.W` and in a given neighbourhood of `q`, and `c ∘ φ⁻¹` holomorphic. -/
theorem exists_pow_normalForm_realize [SmoothOfRelativeDimension 1 sX] (g : X ⟶ Y)
    (hg : g ≫ sY = sX) (c : EtaleCoordinateChart sX 1) (c' : EtaleCoordinateChart sY 1)
    {q : ComplexPoints sX} (hq : q ∈ c.W) (hgq : realize g hg q ∈ c'.W)
    (hnc : ¬ ∀ᶠ y in nhds q, realize g hg y = realize g hg q) {N : Set (ComplexPoints sX)}
    (hN : N ∈ nhds q) :
    ∃ (e : ℕ) (φ : OpenPartialHomeomorph (ComplexPoints sX) ℂ), 0 < e ∧ q ∈ φ.source ∧
      φ.source ⊆ c.W ∩ N ∧ φ q = 0 ∧
      (∀ y ∈ φ.source, realize g hg y ∈ c'.W ∧
        (c'.toOpenPartialHomeomorph.transHomeomorph
          (ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ).toHomeomorph) (realize g hg y) =
        (c'.toOpenPartialHomeomorph.transHomeomorph
          (ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ).toHomeomorph) (realize g hg q) +
          φ y ^ e) ∧
      ∀ w ∈ φ.target, AnalyticAt ℂ (fun w ↦ c.toOpenPartialHomeomorph (φ.symm w)) w := by
  set κ := ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ
  set zc := c'.toOpenPartialHomeomorph.transHomeomorph κ.toHomeomorph
  have hzs : zc.source = c'.W := by
    simp [zc]
  have hcs : c.toOpenPartialHomeomorph.source = c.W := c.source_toOpenPartialHomeomorph
  have hcont := continuous_realize g hg
  have han : AnalyticAt ℂ (fun v ↦ zc (realize g hg (c.toOpenPartialHomeomorph.symm v)))
      (c.toOpenPartialHomeomorph q) :=
    ((κ : (Fin 1 → ℂ) →L[ℂ] ℂ).analyticAt _).comp (c.analyticAt_realize g hg c' hq hgq)
  have hnc' : ¬ ∀ᶠ y in nhds q, zc (realize g hg y) = zc (realize g hg q) := by
    intro hev
    apply hnc
    have hW : ∀ᶠ y in nhds q, realize g hg y ∈ zc.source := by
      rw [hzs]; exact hcont.continuousAt.preimage_mem_nhds (c'.isOpen.mem_nhds hgq)
    filter_upwards [hev, hW] with y h1 h2
    exact zc.injOn h2 (hzs ▸ hgq) h1
  obtain ⟨e, φ, he, hqφ, hφs, hφ0, hnf, hφan⟩ := exists_pow_normalForm_of_analyticAt
    c.toOpenPartialHomeomorph zc (hcs ▸ hq) (hzs ▸ hgq) hcont.continuousAt han hnc' hN
  refine ⟨e, φ, he, hqφ, by rw [← hcs]; exact hφs, hφ0, fun y hy ↦ ?_, hφan⟩
  obtain ⟨h1, h2⟩ := hnf y hy
  exact ⟨hzs ▸ h1, h2⟩

/-- **A realized morphism of curves is a ramified disc near a fibre.** Let `g : X ⟶ Y` be a
morphism over `ℂ`, `X` smooth of relative dimension one, whose realized map is closed, with
`X(ℂ)` Hausdorff, a finite fibre over `s`, and not locally constant at any point of that fibre.
For an étale chart `c'` of `Y` at `s`, read in `ℂ`, neighbourhoods `N q` of the points of `X(ℂ)`
and `ε > 0`, the realized map is a ramified disc over a disc of radius at most `ε` around the
reading of `s`, each of whose coordinates has source in `c.W ∩ N q` for some point `q` of the
fibre and some étale chart `c`, with `c ∘ φ⁻¹` holomorphic on its target. -/
theorem exists_ramifiedDisc_realize [SmoothOfRelativeDimension 1 sX] [T2Space (ComplexPoints sX)]
    (g : X ⟶ Y) (hg : g ≫ sY = sX) (hcl : IsClosedMap (realize g hg))
    (c' : EtaleCoordinateChart sY 1) {s : ComplexPoints sY} (hs : s ∈ c'.W)
    (hfin : (realize g hg ⁻¹' {s}).Finite)
    (hnc : ∀ q ∈ realize g hg ⁻¹' {s}, ¬ ∀ᶠ y in nhds q, realize g hg y = realize g hg q)
    (N : ComplexPoints sX → Set (ComplexPoints sX)) (hN : ∀ q, N q ∈ nhds q) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ d : RamifiedDisc.{0, 0, 0} (realize g hg),
      d.chart = c'.toOpenPartialHomeomorph.transHomeomorph
        (ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ).toHomeomorph ∧
      d.centre = c'.toOpenPartialHomeomorph.transHomeomorph
        (ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ).toHomeomorph s ∧
      0 < d.radius ∧ d.radius ≤ ε ∧
      ∀ i, ∃ q ∈ realize g hg ⁻¹' {s}, ∃ c : EtaleCoordinateChart sX 1,
        (d.coord i).source ⊆ c.W ∩ N q ∧
        ∀ w ∈ (d.coord i).target,
          AnalyticAt ℂ (fun w ↦ c.toOpenPartialHomeomorph ((d.coord i).symm w)) w := by
  set zc := c'.toOpenPartialHomeomorph.transHomeomorph
    (ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ).toHomeomorph
  have hzs : zc.source = c'.W := by
    simp [zc]
  have hc : ∀ q : realize g hg ⁻¹' {s}, ∃ c : EtaleCoordinateChart sX 1,
      (q : ComplexPoints sX) ∈ c.W :=
    fun q ↦ EtaleCoordinateChart.exists_mem_W _
  choose c hc using hc
  have hnf : ∀ q : realize g hg ⁻¹' {s}, ∃ (e : ℕ) (φ : OpenPartialHomeomorph (ComplexPoints sX) ℂ),
      0 < e ∧ (q : ComplexPoints sX) ∈ φ.source ∧ φ.source ⊆ (c q).W ∩ N q ∧
      (∀ y ∈ φ.source, realize g hg y ∈ zc.source ∧ zc (realize g hg y) = zc s + φ y ^ e) ∧
      ∀ w ∈ φ.target, AnalyticAt ℂ (fun w ↦ (c q).toOpenPartialHomeomorph (φ.symm w)) w :=
    fun q ↦ by
      have hgq : realize g hg q = s := q.2
      obtain ⟨e, φ, he, hqφ, hφs, -, hφ, hφan⟩ := exists_pow_normalForm_realize g hg (c q) c'
        (hc q) (by rw [hgq]; exact hs) (hnc q q.2) (hN q)
      refine ⟨e, φ, he, hqφ, hφs, fun y hy ↦ ?_, hφan⟩
      obtain ⟨h1, h2⟩ := hφ y hy
      exact ⟨hzs ▸ h1, by rw [h2, hgq]⟩
  choose e φ he hqφ hφs hφ hφan using hnf
  obtain ⟨d, hdc, hdz, hd0, hdε, hdi⟩ := exists_ramifiedDisc hcl zc (hzs ▸ hs) hfin e he φ hqφ
    hφ hε
  refine ⟨d, hdc, hdz, hd0, hdε, fun i ↦ ?_⟩
  obtain ⟨q, -, hsrc, htgt⟩ := hdi i
  refine ⟨q, q.2, c q, hsrc.trans (hφs q), fun w hw ↦ ?_⟩
  obtain ⟨hw', -⟩ := htgt w hw
  refine (hφan q w hw').congr ?_
  filter_upwards [(d.coord i).open_target.mem_nhds hw] with w' hw''
  rw [(htgt w' hw'').2]

end Realize

end MMP.Analytic.ChartConeCellulation
