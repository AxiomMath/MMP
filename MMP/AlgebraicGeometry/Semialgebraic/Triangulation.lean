module

public import MMP.AlgebraicGeometry.Semialgebraic.Basic
public import MMP.AlgebraicGeometry.Semialgebraic.RootClosureExtension
public import Mathlib.Analysis.Convex.SimplicialComplex.Basic
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Homotopy.LocallyContractible
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Triangulable semialgebraic sets are locally contractible

The *open simplex* of a finite set `t` of points of a real vector space is the set of the
combinations `∑ wᵢ vᵢ` with all `wᵢ > 0` and `∑ wᵢ = 1`. Its closure is the closed simplex
(the convex hull of `t`), and every point of the closed simplex lies in the open simplex of a
nonempty subset of `t`.

The **triangulation theorem for compact semialgebraic sets** (Bochnak–Coste–Roy, Theorem 9.2.1)
says: a compact semialgebraic set `S ⊆ ℝⁿ` is homeomorphic to the polyhedron `|K|` of a finite
simplicial complex `K` in `ℝⁿ`, by a homeomorphism `h : |K| → S` compatible with finitely many
given semialgebraic subsets `A_j ⊆ S` (each `A_j` is a union of images of open simplices). We
state it as `MMP.SemialgebraicTriangulation`, and show that it implies the strong
local contractibility of closed semialgebraic sets, in particular of real algebraic sets.

The proof. Let `V` be closed semialgebraic, `x ∈ V`, and `U` a neighbourhood of `x`. Triangulate
`S = V ∩ {|y - x|² ≤ 1}` compatibly with `{x}` and `A = V ∩ {|y - x|² < ρ²}`, `ρ` small. The
point `u = h⁻¹(x)` is a vertex of `K` (the open simplex containing it is mapped into `{x}`). The
closed star `St(u)`, the union of the closed simplices with vertex `u`, is star-convex about `u`
hence contractible, and it is a neighbourhood of `u` in `|K|`: its complement in `|K|` lies in
the union of the closed simplices without vertex `u`, a closed set missing `u`. A simplex with
vertex `u` has its open simplex mapped into `A` (its image accumulates at `x`), so `h(St(u))`
lies in the closure of `A`, inside `U`. Hence `h(St(u))` is a contractible neighbourhood of `x`
in `V` inside `U`. No subdivision is needed: the compatibility with `A` makes the star small.

## Main definitions

* `MMP.openSimplex`: the open simplex of a finite set of points.
* `MMP.SemialgebraicTriangulation`: the triangulation theorem for compact
  semialgebraic sets, as a proposition.

## Main results

* `MMP.convexHull_subset_closure_openSimplex`: the closed simplex is the closure
  of the open one.
* `MMP.exists_mem_openSimplex_of_mem_convexHull`: every point of the closed
  simplex lies in the open simplex of a face.
* `MMP.exists_continuousOn_convexHull_of_specAt`: the root functions of a
  polynomial with constant leading coefficient, over an open simplex, extend continuously to the
  closed simplex (the lifting step of the triangulation theorem).
* `MMP.SemialgebraicTriangulation.exists_contractible_mem_nhdsWithin`: under the
  triangulation theorem, a point of a closed semialgebraic set `V` has arbitrarily small
  contractible neighbourhoods in `V`.
* `MMP.SemialgebraicTriangulation.stronglyLocallyContractibleSpace`: under the
  triangulation theorem, closed semialgebraic sets are strongly locally contractible.
* `MMP.SemialgebraicTriangulation.stronglyLocallyContractibleSpace_zeroLocus`: under the
  triangulation theorem, real algebraic sets are strongly locally contractible.

## References

* [J. Bochnak, M. Coste, M.-F. Roy, *Real algebraic geometry*][bochnak1998], Theorem 9.2.1.
-/

@[expose] public section

open Set Filter Topology Metric

namespace MMP

section OpenSimplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The open simplex of a finite set `t`: the combinations `∑ wᵢ vᵢ`, `vᵢ ∈ t`, with all
weights `wᵢ > 0` and `∑ wᵢ = 1`. -/
def openSimplex (t : Finset E) : Set E :=
  {z | ∃ w : E → ℝ, (∀ i ∈ t, 0 < w i) ∧ ∑ i ∈ t, w i = 1 ∧ ∑ i ∈ t, w i • i = z}

/-- Membership in the open simplex of `t`. -/
theorem mem_openSimplex_iff {t : Finset E} {z : E} :
    z ∈ openSimplex t ↔
      ∃ w : E → ℝ, (∀ i ∈ t, 0 < w i) ∧ ∑ i ∈ t, w i = 1 ∧ ∑ i ∈ t, w i • i = z :=
  Iff.rfl

/-- The open simplex of a finite set is contained in its convex hull. -/
theorem openSimplex_subset_convexHull (t : Finset E) :
    openSimplex t ⊆ convexHull ℝ (t : Set E) := by
  rintro z ⟨w, hw, h1, rfl⟩
  exact Finset.mem_convexHull'.2 ⟨w, fun i hi ↦ (hw i hi).le, h1, rfl⟩

/-- The open segment from a point of the closed simplex to a point of the open simplex lies in
the open simplex. -/
theorem openSegment_subset_openSimplex {t : Finset E} {y z : E}
    (hy : y ∈ convexHull ℝ (t : Set E)) (hz : z ∈ openSimplex t) :
    openSegment ℝ y z ⊆ openSimplex t := by
  obtain ⟨v, hv0, hv1, rfl⟩ := Finset.mem_convexHull'.1 hy
  obtain ⟨w, hw0, hw1, rfl⟩ := hz
  rintro _ ⟨a, b, ha, hb, hab, rfl⟩
  refine ⟨fun i ↦ a * v i + b * w i, fun i hi ↦ ?_, ?_, ?_⟩
  · exact add_pos_of_nonneg_of_pos (mul_nonneg ha.le (hv0 i hi)) (mul_pos hb (hw0 i hi))
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hv1, hw1, mul_one, mul_one,
      hab]
  · simp only [add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum]

/-- The open simplex of a nonempty finite set is nonempty: it contains the barycentre. -/
theorem openSimplex_nonempty {t : Finset E} (ht : t.Nonempty) : (openSimplex t).Nonempty := by
  have hc : (0 : ℝ) < t.card := by exact_mod_cast ht.card_pos
  refine ⟨∑ i ∈ t, (t.card : ℝ)⁻¹ • i, fun _ ↦ (t.card : ℝ)⁻¹, fun _ _ ↦ inv_pos.2 hc, ?_, rfl⟩
  rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hc.ne']

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- **The closed simplex is the closure of the open simplex.** -/
theorem convexHull_subset_closure_openSimplex {t : Finset E} (ht : t.Nonempty) :
    convexHull ℝ (t : Set E) ⊆ closure (openSimplex t) := by
  obtain ⟨z, hz⟩ := openSimplex_nonempty ht
  intro y hy
  have h1 : y ∈ closure (openSegment ℝ y z) :=
    segment_subset_closure_openSegment (left_mem_segment ℝ y z)
  exact closure_mono (openSegment_subset_openSimplex hy hz) h1

/-- The open simplex is convex. -/
theorem convex_openSimplex (t : Finset E) : Convex ℝ (openSimplex t) :=
  convex_iff_openSegment_subset.2 fun _ hy _ hz ↦
    openSegment_subset_openSimplex (openSimplex_subset_convexHull t hy) hz

/-- The closure of the open simplex of a nonempty finite set is its convex hull. -/
theorem closure_openSimplex [T2Space E] {t : Finset E} (ht : t.Nonempty) :
    closure (openSimplex t) = convexHull ℝ (t : Set E) :=
  ((t.finite_toSet.isClosed_convexHull ℝ).closure_subset_iff.2
    (openSimplex_subset_convexHull t)).antisymm (convexHull_subset_closure_openSimplex ht)

end OpenSimplex

/-- **Root functions over an open simplex extend to the closed simplex.** Let `F ∈ ℝ[X_σ][T]`
have constant nonzero leading coefficient, `t` a nonempty finite set in a normed space, `Φ`
continuous on the closed simplex of `t` (a triangulation of the base, restricted to one
simplex), and `ξ` continuous on the open simplex with `F(Φ(a), ξ(a)) = 0`. Then `ξ` extends to a
continuous function on the closed simplex with `F(Φ(b), ξ(b)) = 0`. -/
theorem exists_continuousOn_convexHull_of_specAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {σ : Type*} [Fintype σ] {F : Polynomial (MvPolynomial σ ℝ)} {c : ℝ}
    (hc : c ≠ 0) (hF : F.leadingCoeff = MvPolynomial.C c) {t : Finset E} (ht : t.Nonempty)
    {Φ : E → σ → ℝ} (hΦ : ContinuousOn Φ (convexHull ℝ (t : Set E))) {ξ : E → ℝ}
    (hξ : ContinuousOn ξ (openSimplex t))
    (hξF : ∀ a ∈ openSimplex t, (TarskiSeidenberg.specAt (Φ a) F).eval (ξ a) = 0) :
    ∃ g : E → ℝ, ContinuousOn g (convexHull ℝ (t : Set E)) ∧ EqOn g ξ (openSimplex t) ∧
      ∀ b ∈ convexHull ℝ (t : Set E), (TarskiSeidenberg.specAt (Φ b) F).eval (g b) = 0 := by
  rw [← closure_openSimplex ht] at hΦ ⊢
  exact Convex.exists_continuousOn_closure_of_specAt hc hF (convex_openSimplex t) hΦ hξ hξF

/-- Every point of the closed simplex of `t` lies in the open simplex of a nonempty subset of
`t`: the points of `t` with positive weight. -/
theorem exists_mem_openSimplex_of_mem_convexHull {E : Type*} [AddCommGroup E] [Module ℝ E]
    {t : Finset E} {y : E} (hy : y ∈ convexHull ℝ (t : Set E)) :
    ∃ t' ⊆ t, t'.Nonempty ∧ y ∈ openSimplex t' := by
  classical
  obtain ⟨w, hw0, hw1, rfl⟩ := Finset.mem_convexHull'.1 hy
  have hsum : ∑ i ∈ t with 0 < w i, w i = 1 := by
    rw [Finset.sum_filter_of_ne fun i hi hne ↦ lt_of_le_of_ne (hw0 i hi) (Ne.symm hne), hw1]
  refine ⟨t.filter (0 < w ·), Finset.filter_subset _ _, ?_, w,
    fun i hi ↦ (Finset.mem_filter.1 hi).2, hsum, ?_⟩
  · by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.1 h, Finset.sum_empty] at hsum
    exact zero_ne_one hsum
  · refine Finset.sum_filter_of_ne fun i hi hne ↦ lt_of_le_of_ne (hw0 i hi) (Ne.symm ?_)
    rintro h
    exact hne (by rw [h, zero_smul])

/-- **The triangulation theorem for compact semialgebraic sets** (Bochnak–Coste–Roy, Theorem
9.2.1), as a proposition: for a compact semialgebraic `S ⊆ ℝ^σ` and finitely many semialgebraic
subsets `A_j ⊆ S`, there are a finite simplicial complex `K` in some `ℝ^ν` and a homeomorphism
`h : |K| → S` (a continuous bijection from the compact polyhedron `|K|`) such that each `A_j`
contains or misses the image of each open simplex of `K`. The ambient space of `K` is left free
(Bochnak–Coste–Roy build `K` in `ℝ^σ` itself; any finite simplicial complex is realized in the
standard simplex of its vertex set, `MMP.stdSimplicialComplex`). -/
def SemialgebraicTriangulation : Prop :=
  ∀ (σ : Type) [Fintype σ] (S : Set (σ → ℝ)) (ι : Type) [Finite ι] (A : ι → Set (σ → ℝ)),
    IsCompact S → IsSemialgebraic S → (∀ j, IsSemialgebraic (A j)) → (∀ j, A j ⊆ S) →
    ∃ (ν : Type) (_ : Fintype ν) (K : Geometry.SimplicialComplex ℝ (ν → ℝ))
      (h : (ν → ℝ) → σ → ℝ),
      K.faces.Finite ∧ ContinuousOn h K.space ∧ InjOn h K.space ∧ h '' K.space = S ∧
      ∀ j, ∀ t ∈ K.faces, h '' openSimplex t ⊆ A j ∨ Disjoint (h '' openSimplex t) (A j)

section SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : Geometry.SimplicialComplex ℝ E} {h : E → F}

/-- A point at squared Euclidean distance at most `ρ ^ 2` lies at sup-distance at most `ρ`. -/
theorem dist_le_of_sum_sq_sub_le {σ : Type*} [Fintype σ] {x y : σ → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hy : ∑ i, (y i - x i) ^ 2 ≤ ρ ^ 2) : dist y x ≤ ρ := by
  refine (dist_pi_le_iff hρ).2 fun i ↦ ?_
  have h₁ : (y i - x i) ^ 2 ≤ ρ ^ 2 :=
    (Finset.single_le_sum (f := fun i ↦ (y i - x i) ^ 2) (fun i _ ↦ sq_nonneg _)
      (Finset.mem_univ i)).trans hy
  rw [Real.dist_eq]
  nlinarith [abs_nonneg (y i - x i), sq_abs (y i - x i)]

/-- The open simplex of a face of a simplicial complex lies in its space. -/
theorem openSimplex_subset_space {s : Finset E} (hs : s ∈ K.faces) : openSimplex s ⊆ K.space :=
  (openSimplex_subset_convexHull s).trans (K.convexHull_subset_space hs)

/-- A union of closed faces of a simplicial complex lies in its space. -/
theorem biUnion_convexHull_subset_space (p : Finset E → Prop) :
    ⋃ s ∈ {s ∈ K.faces | p s}, convexHull ℝ (s : Set E) ⊆ K.space :=
  iUnion₂_subset fun _ hs ↦ K.convexHull_subset_space hs.1

/-- A union of closed faces of a finite simplicial complex is compact. -/
theorem isCompact_biUnion_convexHull (hK : K.faces.Finite) (p : Finset E → Prop) :
    IsCompact (⋃ s ∈ {s ∈ K.faces | p s}, convexHull ℝ (s : Set E)) :=
  (hK.subset fun _ hs ↦ hs.1).isCompact_biUnion fun s _ ↦ s.finite_toSet.isCompact_convexHull ℝ

/-- The space of a simplicial complex is covered by the closed star of `u` and the closed faces
not containing `u`. -/
theorem space_subset_closedStar_union (u : E) :
    K.space ⊆ (⋃ s ∈ {s ∈ K.faces | u ∈ s}, convexHull ℝ (s : Set E)) ∪
      ⋃ s ∈ {s ∈ K.faces | u ∉ s}, convexHull ℝ (s : Set E) := by
  intro y hy
  obtain ⟨s, hs, hys⟩ := K.mem_space_iff.1 hy
  by_cases hus : u ∈ s
  · exact Or.inl (mem_biUnion (x := s) ⟨hs, hus⟩ hys)
  · exact Or.inr (mem_biUnion (x := s) ⟨hs, hus⟩ hys)

/-- A vertex lies in no closed face not containing it. -/
theorem vertex_notMem_biUnion_convexHull {u : E} (hu : u ∈ K.vertices) :
    u ∉ ⋃ s ∈ {s ∈ K.faces | u ∉ s}, convexHull ℝ (s : Set E) := fun hu' ↦ by
  obtain ⟨s, hs, hus⟩ := mem_iUnion₂.1 hu'
  exact hs.2 ((K.vertex_mem_convexHull_iff hu hs.1).1 hus)

/-- The closed star of `u` is star-convex about `u`. -/
theorem starConvex_closedStar (u : E) :
    StarConvex ℝ u (⋃ s ∈ {s ∈ K.faces | u ∈ s}, convexHull ℝ (s : Set E)) :=
  starConvex_iUnion₂ fun _ hs ↦
    (convex_convexHull ℝ _).starConvex (subset_convexHull ℝ _ (Finset.mem_coe.2 hs.2))

/-- A vertex lies in its closed star. -/
theorem vertex_mem_closedStar {u : E} (hu : u ∈ K.vertices) :
    u ∈ ⋃ s ∈ {s ∈ K.faces | u ∈ s}, convexHull ℝ (s : Set E) :=
  mem_biUnion (x := {u}) ⟨K.mem_vertices.1 hu, Finset.mem_singleton_self u⟩
    (subset_convexHull ℝ _ (Finset.mem_coe.2 (Finset.mem_singleton_self u)))

/-- The image of a closed face under a map continuous on the space lies in the closure of the
image of the open face. -/
theorem image_convexHull_subset_closure_image_openSimplex [TopologicalSpace F]
    (hh : ContinuousOn h K.space) {s : Finset E} (hs : s ∈ K.faces) (hsne : s.Nonempty) :
    h '' convexHull ℝ (s : Set E) ⊆ closure (h '' openSimplex s) :=
  (image_mono (convexHull_subset_closure_openSimplex hsne)).trans
    (hh.mono (((s.finite_toSet.isClosed_convexHull ℝ).closure_subset_iff.2
      (openSimplex_subset_convexHull s)).trans (K.convexHull_subset_space hs))).image_closure

/-- If the image of an open face is either inside `B` or disjoint from it, and a vertex of the
face has a neighbourhood `W` whose points of the image lie in `B`, then the image of the closed
face lies in the closure of `B`. -/
theorem image_convexHull_subset_closure_of_subset_or_disjoint [TopologicalSpace F]
    (hh : ContinuousOn h K.space) {s : Finset E} (hs : s ∈ K.faces) {u : E} (hus : u ∈ s)
    {B W : Set F} (hW : IsOpen W) (huW : h u ∈ W) (hWB : W ∩ h '' K.space ⊆ B)
    (hB : h '' openSimplex s ⊆ B ∨ Disjoint (h '' openSimplex s) B) :
    h '' convexHull ℝ (s : Set E) ⊆ closure B := by
  have hsub := image_convexHull_subset_closure_image_openSimplex hh hs ⟨u, hus⟩
  refine hsub.trans (closure_mono (hB.resolve_right fun h₁ ↦ ?_))
  obtain ⟨z, hzW, y, hy, rfl⟩ := mem_closure_iff.1
    (hsub ⟨u, subset_convexHull ℝ _ (Finset.mem_coe.2 hus), rfl⟩) W hW huW
  exact Set.disjoint_left.1 h₁ ⟨y, hy, rfl⟩ (hWB ⟨hzW, y, openSimplex_subset_space hs hy, rfl⟩)

/-- If `h` is injective on a simplicial complex and each open face maps into or away from `{x}`,
then a point `x` of the image is the image of a vertex. -/
theorem exists_mem_vertices_eq_of_injOn (hi : InjOn h K.space) {x : F}
    (hx : ∀ t ∈ K.faces, h '' openSimplex t ⊆ {x} ∨ Disjoint (h '' openSimplex t) {x})
    (hxK : x ∈ h '' K.space) : ∃ u ∈ K.vertices, h u = x := by
  obtain ⟨u, huK, hux⟩ := hxK
  obtain ⟨t₀, ht₀, hut₀⟩ := K.mem_space_iff.1 huK
  obtain ⟨t, htt₀, htne, hut⟩ := exists_mem_openSimplex_of_mem_convexHull hut₀
  have htK : t ∈ K.faces := K.down_closed ht₀ htt₀ htne
  have hto : openSimplex t ⊆ {u} := by
    rcases hx t htK with h₁ | h₁
    · exact fun z hz ↦ hi (openSimplex_subset_space htK hz) huK ((h₁ ⟨z, hz, rfl⟩).trans hux.symm)
    · exact absurd rfl (Set.disjoint_left.1 h₁ ⟨u, hut, hux⟩)
  have htu : t = {u} := by
    refine (Finset.Nonempty.subset_singleton_iff htne).1 fun i hi ↦ ?_
    have : i ∈ closure ({u} : Set E) :=
      closure_mono hto (convexHull_subset_closure_openSimplex htne (subset_convexHull ℝ _ hi))
    rw [closure_singleton] at this
    exact Finset.mem_singleton.2 this
  exact ⟨u, K.mem_vertices.2 (htu ▸ htK), hux⟩

/-- Under a continuous injection of a finite simplicial complex into a Hausdorff space, the image
of the closed star of a vertex `u` contains a neighbourhood of `h u` in the image. -/
theorem exists_isOpen_inter_image_subset_image_closedStar [TopologicalSpace F] [T2Space F]
    (hK : K.faces.Finite) (hh : ContinuousOn h K.space) (hi : InjOn h K.space) {u : E}
    (hu : u ∈ K.vertices) :
    ∃ O, IsOpen O ∧ h u ∈ O ∧
      O ∩ h '' K.space ⊆ h '' ⋃ s ∈ {s ∈ K.faces | u ∈ s}, convexHull ℝ (s : Set E) := by
  set G := ⋃ s ∈ {s ∈ K.faces | u ∉ s}, convexHull ℝ (s : Set E)
  have hGK : G ⊆ K.space := biUnion_convexHull_subset_space _
  refine ⟨(h '' G)ᶜ, ((isCompact_biUnion_convexHull hK _).image_of_continuousOn
    (hh.mono hGK)).isClosed.isOpen_compl, ?_, ?_⟩
  · rintro ⟨y, hy, hyu⟩
    obtain rfl := hi (hGK hy) (biUnion_convexHull_subset_space _ (vertex_mem_closedStar hu)) hyu
    exact vertex_notMem_biUnion_convexHull hu hy
  · rintro _ ⟨hyG, z, hz, rfl⟩
    exact ⟨z, (space_subset_closedStar_union u hz).resolve_right fun hz' ↦ hyG ⟨z, hz', rfl⟩, rfl⟩

end SimplicialComplex

/-- The image of a compact contractible set under a continuous injection into a Hausdorff space
is contractible. -/
theorem contractibleSpace_image_of_injOn {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] {f : X → Y} {s : Set X} (hs : IsCompact s) [ContractibleSpace s]
    (hf : ContinuousOn f s) (hi : InjOn f s) : ContractibleSpace (f '' s) := by
  have : CompactSpace s := isCompact_iff_compactSpace.1 hs
  have hemb : Topology.IsEmbedding (s.domRestrict f) :=
    (hf.domRestrict.isClosedEmbedding fun a b hab ↦ Subtype.ext (hi a.2 b.2 hab)).isEmbedding
  exact ((Homeomorph.setCongr (image_eq_range f s : f '' s = range (s.domRestrict f))).trans
    hemb.toHomeomorph.symm).contractibleSpace

/-- A point is a semialgebraic set. -/
theorem isSemialgebraic_singleton {σ R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] [Finite σ] (x : σ → R) : IsSemialgebraic {x} := by
  convert isSemialgebraic_zeroLocus (fun i : σ ↦ MvPolynomial.X i - MvPolynomial.C (x i)) using 1
  ext y
  simp only [mem_singleton_iff, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C, sub_eq_zero,
    mem_ofPred_eq, funext_iff]

namespace SemialgebraicTriangulation

/-- **Under the triangulation theorem, closed semialgebraic sets have small contractible
neighbourhoods.** If `V ⊆ ℝ^σ` is closed and semialgebraic, `x ∈ V` and `U` is a neighbourhood
of `x`, there is a contractible neighbourhood of `x` in `V` inside `U`. -/
theorem exists_contractible_mem_nhdsWithin (H : SemialgebraicTriangulation) {σ : Type}
    [Fintype σ] {V : Set (σ → ℝ)} (hV : IsSemialgebraic V) (hVc : IsClosed V) {x : σ → ℝ}
    (hx : x ∈ V) {U : Set (σ → ℝ)} (hU : U ∈ 𝓝 x) :
    ∃ N ∈ 𝓝[V] x, N ⊆ V ∩ U ∧ ContractibleSpace N := by
  classical
  set q : (σ → ℝ) → ℝ := fun y ↦ ∑ i, (y i - x i) ^ 2
  have hqc : Continuous q := continuous_finsetSum _ fun i _ ↦
    ((continuous_apply i).sub continuous_const).pow 2
  have hqx : q x = 0 := by simp [q]
  have hball : ∀ ρ : ℝ, 0 ≤ ρ → {y | q y ≤ ρ ^ 2} ⊆ closedBall x ρ := fun _ hρ _ hy ↦
    mem_closedBall.2 (dist_le_of_sum_sq_sub_le hρ hy)
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU
  set ρ := min (ε / 2) (1 / 2)
  have hρ : 0 < ρ := lt_min (half_pos hε) one_half_pos
  have hρε : ρ < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hρ1 : ρ ^ 2 < 1 := by nlinarith [(min_le_right _ _ : ρ ≤ 1 / 2)]
  set S := V ∩ {y | q y ≤ 1}
  have hSc : IsCompact S := by
    refine isCompact_of_isClosed_isBounded (hVc.inter (isClosed_le hqc continuous_const))
      (isBounded_closedBall (x := x) (r := 1) |>.subset ?_)
    refine inter_subset_right.trans ?_
    simpa using hball 1 zero_le_one
  have hSs : IsSemialgebraic S := hV.inter (isSemialgebraic_sqDist_le x 1)
  set W := {y | q y < ρ ^ 2}
  have hWo : IsOpen W := isOpen_lt hqc continuous_const
  have hxW : x ∈ W := by simpa [W, hqx] using pow_pos hρ 2
  set A₂ := V ∩ W
  let A : Bool → Set (σ → ℝ) := fun b ↦ if b then {x} else A₂
  have hxS : x ∈ S := ⟨hx, by simp [hqx]⟩
  have hAs : ∀ b, IsSemialgebraic (A b) :=
    Bool.forall_bool.2 ⟨hV.inter (isSemialgebraic_sqDist_lt x _), isSemialgebraic_singleton x⟩
  have hAS : ∀ b, A b ⊆ S :=
    Bool.forall_bool.2 ⟨fun y hy ↦ ⟨hy.1, (le_of_lt hy.2).trans hρ1.le⟩, by simpa [A] using hxS⟩
  obtain ⟨ν, _, K, h, hKf, hhc, hhi, hhS, hcompat⟩ := H σ S Bool A hSc hSs hAs hAS
  obtain ⟨u, huv, hux⟩ := exists_mem_vertices_eq_of_injOn (x := x) hhi (hcompat true) (hhS ▸ hxS)
  set St := ⋃ s ∈ {s ∈ K.faces | u ∈ s}, convexHull ℝ (s : Set (ν → ℝ))
  have hStK : St ⊆ K.space := biUnion_convexHull_subset_space _
  have hWB : W ∩ h '' K.space ⊆ A₂ := fun y ⟨hyW, hyK⟩ ↦ ⟨(hhS ▸ hyK : y ∈ S).1, hyW⟩
  have hNVU : h '' St ⊆ V ∩ U := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨s, hs, hys⟩ := mem_iUnion₂.1 hy
    refine ⟨(hhS ▸ mem_image_of_mem h (hStK hy) : h y ∈ S).1,
      hεU (closedBall_subset_ball hρε (hball ρ hρ.le ?_))⟩
    refine closure_lt_subset_le hqc continuous_const (closure_mono (inter_subset_right (s := V)) ?_)
    exact image_convexHull_subset_closure_of_subset_or_disjoint hhc hs.1 hs.2 hWo (hux ▸ hxW) hWB
      (hcompat false s hs.1) ⟨y, hys, rfl⟩
  obtain ⟨O, hO, huO, hOSt⟩ := exists_isOpen_inter_image_subset_image_closedStar hKf hhc hhi huv
  have : ContractibleSpace St :=
    (starConvex_closedStar (K := K) u).contractibleSpace ⟨u, vertex_mem_closedStar huv⟩
  refine ⟨h '' St, mem_nhdsWithin.2 ⟨{y | q y < 1} ∩ O, (isOpen_lt hqc continuous_const).inter hO,
    ⟨by simp [hqx], hux ▸ huO⟩, fun y ⟨⟨hy1, hyO⟩, hyV⟩ ↦
      hOSt ⟨hyO, hhS ▸ ⟨hyV, (le_of_lt hy1 : q y ≤ 1)⟩⟩⟩, hNVU, ?_⟩
  exact contractibleSpace_image_of_injOn (s := St) (isCompact_biUnion_convexHull hKf _)
    (hhc.mono hStK) (hhi.mono hStK)

/-- **Under the triangulation theorem, closed semialgebraic sets are strongly locally
contractible.** -/
theorem stronglyLocallyContractibleSpace (H : SemialgebraicTriangulation) {σ : Type}
    [Fintype σ] {V : Set (σ → ℝ)} (hV : IsSemialgebraic V) (hVc : IsClosed V) :
    StronglyLocallyContractibleSpace V := by
  refine ⟨fun y ↦ ⟨fun s ↦ ⟨fun hs ↦ ?_, fun ⟨t, ⟨ht, _⟩, hts⟩ ↦ mem_of_superset ht hts⟩⟩⟩
  obtain ⟨U, hU, hUs⟩ := mem_nhds_subtype V y s |>.1 hs
  obtain ⟨N, hN, hNVU, hNc⟩ := exists_contractible_mem_nhdsWithin H hV hVc y.2 hU
  have hNV : N ⊆ V := fun z hz ↦ (hNVU hz).1
  refine ⟨Subtype.val ⁻¹' N, ⟨?_, ?_⟩, fun z hz ↦ hUs (hNVU hz).2⟩
  · rw [mem_nhds_subtype_iff_nhdsWithin, Subtype.image_preimage_coe]
    exact inter_mem self_mem_nhdsWithin hN
  · let e : (Subtype.val ⁻¹' N : Set V) ≃ₜ N :=
      { toFun := fun z ↦ ⟨z.1.1, z.2⟩
        invFun := fun z ↦ ⟨⟨z.1, hNV z.2⟩, z.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
        continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
    exact e.contractibleSpace

/-- **Under the triangulation theorem, real algebraic sets are strongly locally contractible.** -/
theorem stronglyLocallyContractibleSpace_zeroLocus (H : SemialgebraicTriangulation) {σ κ : Type}
    [Fintype σ] [Finite κ] (g : κ → MvPolynomial σ ℝ) :
    StronglyLocallyContractibleSpace {x : σ → ℝ | ∀ j, MvPolynomial.eval x (g j) = 0} := by
  refine H.stronglyLocallyContractibleSpace (isSemialgebraic_zeroLocus g) ?_
  simp only [ofPred_forall]
  exact isClosed_iInter fun j ↦ isClosed_eq (MvPolynomial.continuous_eval _) continuous_const

end SemialgebraicTriangulation

end MMP
