module

public import MMP.AlgebraicTopology.SingularHomology.BarycentricSubdivision
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Triangulations by standard simplicial complexes, and their barycentric subdivision

A *standard triangulation* of a set `S ⊆ ℝ^σ` is a down-closed family `Δ` of nonempty finite
subsets of a finite type `ν` (an abstract simplicial complex) together with a map
`h : ℝ^ν → ℝ^σ` that is continuous and injective on the polyhedron `|Δ| ⊆ ℝ^ν` of the standard
realization and maps it onto `S`. Such a triangulation gives the data asked for by
`MMP.SemialgebraicTriangulation` (`MMP.IsStdTriangulation.exists_simplicialComplex`).

The *barycentric subdivision* `sd Δ` has vertex set `Finset ν` and as simplices the nonempty
chains of faces of `Δ`. Composing with the barycentre map gives a standard triangulation of the
same set (`MMP.IsStdTriangulation.subdivision`), and the open simplex of a chain is mapped into the
open simplex of its top face (`MMP.exists_baryMap_image_openSimplex_subset`), so the subdivision
stays compatible with any family of sets the triangulation was compatible with.

## Main definitions

* `MMP.stdSpace`: the polyhedron `|Δ| ⊆ ℝ^ν`.
* `MMP.IsStdTriangulation`: a standard triangulation of a set.
* `MMP.sdFaces`: the barycentric subdivision of an abstract simplicial complex.

## Main results

* `MMP.IsStdTriangulation.subdivision`: the subdivision of a triangulation.
* `MMP.IsStdTriangulation.subdivision_compat`: compatibility passes to it.
* `MMP.baryMap_image_openSimplex_subset_iff`: after subdivision, a closed union of open
  simplices contains an open simplex as soon as it contains the barycentres of its vertices.
-/

@[expose] public section

open Set

namespace MMP

section Space

variable {ν : Type*} [Fintype ν] [DecidableEq ν]

/-- The polyhedron of the standard realization of `Δ`: the union of the closed simplices. -/
def stdSpace (Δ : Set (Finset ν)) : Set (ν → ℝ) :=
  ⋃ s ∈ Δ, convexHull ℝ (s.map (stdVertex ν) : Set (ν → ℝ))

/-- The space of the standard simplicial complex on `Δ` is the polyhedron `stdSpace Δ`. -/
@[simp]
theorem space_stdSimplicialComplex {Δ : Set (Finset ν)} {hne : ∀ s ∈ Δ, s.Nonempty}
    {hdown : ∀ s ∈ Δ, ∀ t ⊆ s, t.Nonempty → t ∈ Δ} :
    (stdSimplicialComplex Δ hne hdown).space = stdSpace Δ := by
  ext x
  simp only [Geometry.SimplicialComplex.mem_space_iff, mem_faces_stdSimplicialComplex, stdSpace,
    mem_iUnion, exists_prop]
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, hx⟩
    exact ⟨s, hs, hx⟩
  · rintro ⟨s, hs, hx⟩
    exact ⟨_, ⟨s, hs, rfl⟩, hx⟩

end Space

/-- A **standard triangulation** of `S ⊆ ℝ^σ`: an abstract simplicial complex `Δ` on a finite
type `ν` and a map `h` continuous and injective on the polyhedron `|Δ|` with `h(|Δ|) = S`. -/
structure IsStdTriangulation {ν σ : Type*} [DecidableEq ν] (Δ : Set (Finset ν))
    (h : (ν → ℝ) → σ → ℝ) (S : Set (σ → ℝ)) : Prop where
  /-- Every face of `Δ` is nonempty. -/
  nonempty : ∀ s ∈ Δ, s.Nonempty
  /-- Every nonempty subset of a face of `Δ` is a face of `Δ`. -/
  down_closed : ∀ s ∈ Δ, ∀ t ⊆ s, t.Nonempty → t ∈ Δ
  /-- The map `h` is continuous on the polyhedron `|Δ|`. -/
  continuousOn : ContinuousOn h (stdSpace Δ)
  /-- The map `h` is injective on the polyhedron `|Δ|`. -/
  injOn : InjOn h (stdSpace Δ)
  /-- The image of the polyhedron `|Δ|` under `h` is `S`. -/
  image_eq : h '' stdSpace Δ = S

/-- A standard triangulation compatible with `A` gives the data of
`MMP.SemialgebraicTriangulation`. -/
theorem IsStdTriangulation.exists_simplicialComplex {ν : Type} [Finite ν] [DecidableEq ν]
    {σ : Type*} {Δ : Set (Finset ν)} {h : (ν → ℝ) → σ → ℝ} {S : Set (σ → ℝ)}
    (hT : IsStdTriangulation Δ h S) {ι : Type*} {A : ι → Set (σ → ℝ)}
    (hA : ∀ j, ∀ s ∈ Δ, h '' openSimplex (s.map (stdVertex ν)) ⊆ A j ∨
      Disjoint (h '' openSimplex (s.map (stdVertex ν))) (A j)) :
    ∃ (ν' : Type) (_ : Fintype ν') (K : Geometry.SimplicialComplex ℝ (ν' → ℝ))
      (h' : (ν' → ℝ) → σ → ℝ),
      K.faces.Finite ∧ ContinuousOn h' K.space ∧ InjOn h' K.space ∧ h' '' K.space = S ∧
      ∀ j, ∀ t ∈ K.faces, h' '' openSimplex t ⊆ A j ∨ Disjoint (h' '' openSimplex t) (A j) := by
  have := Fintype.ofFinite ν
  refine ⟨ν, inferInstance, stdSimplicialComplex Δ hT.nonempty hT.down_closed, h,
    finite_faces_stdSimplicialComplex, ?_, ?_, ?_, ?_⟩
  · rw [space_stdSimplicialComplex]
    exact hT.continuousOn
  · rw [space_stdSimplicialComplex]
    exact hT.injOn
  · rw [space_stdSimplicialComplex]
    exact hT.image_eq
  · rintro j _ ⟨s, hs, rfl⟩
    exact hA j s hs

section Subdivision

variable {ν : Type*} [Fintype ν] [DecidableEq ν]

/-- The **barycentric subdivision** of `Δ`: the nonempty chains of faces of `Δ`. -/
def sdFaces (Δ : Set (Finset ν)) : Set (Finset (Finset ν)) :=
  {c | c.Nonempty ∧ (∀ τ ∈ c, τ ∈ Δ) ∧ IsChain (· ⊆ ·) (↑c : Set (Finset ν))}

omit [Fintype ν] [DecidableEq ν] in
/-- Membership in the barycentric subdivision: a nonempty chain of faces of `Δ`. -/
@[simp]
theorem mem_sdFaces_iff {Δ : Set (Finset ν)} {c : Finset (Finset ν)} :
    c ∈ sdFaces Δ ↔ c.Nonempty ∧ (∀ τ ∈ c, τ ∈ Δ) ∧ IsChain (· ⊆ ·) (↑c : Set (Finset ν)) :=
  Iff.rfl

/-- A point of a closed simplex of the subdivision is a chain-supported vector. -/
theorem isChainSupported_of_mem_convexHull {Δ : Set (Finset ν)} (hne : ∀ s ∈ Δ, s.Nonempty)
    {c : Finset (Finset ν)} (hc : c ∈ sdFaces Δ) {y : Finset ν → ℝ}
    (hy : y ∈ convexHull ℝ (c.map (stdVertex (Finset ν)) : Set (Finset ν → ℝ))) :
    IsChainSupported y ∧ ∑ τ, y τ = 1 ∧ ∀ τ, y τ ≠ 0 → τ ∈ c := by
  obtain ⟨h0, h1, hoff⟩ := (mem_convexHull_stdVertex_iff _ _).1 hy
  have hsupp : ∀ τ, y τ ≠ 0 → τ ∈ c := fun τ hτ ↦
    Classical.byContradiction fun h ↦ hτ (hoff τ h)
  exact ⟨⟨h0, fun τ hτ ↦ hne τ (hc.2.1 τ (hsupp τ hτ)), hc.2.2.mono fun τ hτ ↦ hsupp τ hτ⟩,
    h1, hsupp⟩

/-- **The barycentre map takes the subdivided polyhedron onto the polyhedron.** -/
theorem baryMap_image_stdSpace_sdFaces {Δ : Set (Finset ν)} (hne : ∀ s ∈ Δ, s.Nonempty)
    (hdown : ∀ s ∈ Δ, ∀ t ⊆ s, t.Nonempty → t ∈ Δ) :
    baryMap '' stdSpace (sdFaces Δ) = stdSpace Δ := by
  classical
  ext x
  simp only [stdSpace, mem_image, mem_iUnion, exists_prop]
  constructor
  · rintro ⟨y, ⟨c, hc, hy⟩, rfl⟩
    obtain ⟨hyc, hy1, hyc'⟩ := isChainSupported_of_mem_convexHull hne hc hy
    have h0 : ∃ τ, y τ ≠ 0 := by
      by_contra! hcon
      simp [hcon] at hy1
    obtain ⟨M, hMy, -, hMs, -⟩ := exists_top_of_isChainSupported hyc h0
    refine ⟨M, hc.2.1 M (hyc' M hMy), (mem_convexHull_stdVertex_iff M _).2
      ⟨baryMap_nonneg hyc.1, by rw [sum_baryMap hyc.2.1, hy1], fun v hv ↦ ?_⟩⟩
    exact Classical.byContradiction fun h ↦ hv ((hMs v).1 h)
  · rintro ⟨s, hs, hx⟩
    obtain ⟨hx0, hx1, hxs⟩ := (mem_convexHull_stdVertex_iff s x).1 hx
    obtain ⟨y, hyc, hyx, rfl⟩ := exists_baryMap_eq x hx0
    have hτΔ : ∀ τ, y τ ≠ 0 → τ ∈ Δ := fun τ hτ ↦
      hdown s hs τ (fun v hv ↦ Classical.byContradiction fun h ↦ hyx τ hτ v hv (hxs v h))
        (hyc.2.1 τ hτ)
    set c := Finset.univ.filter (y · ≠ 0)
    have hy1 : ∑ τ, y τ = 1 := by rw [← sum_baryMap hyc.2.1, hx1]
    have hcne : c.Nonempty := by
      obtain ⟨τ, hτ⟩ : ∃ τ, y τ ≠ 0 := by
        by_contra! h
        simp [h] at hy1
      exact ⟨τ, by simp [c, hτ]⟩
    refine ⟨y, ⟨c, ⟨hcne, fun τ hτ ↦ hτΔ τ (by simpa [c] using hτ), ?_⟩, ?_⟩, rfl⟩
    · exact hyc.2.2.mono fun τ hτ ↦ by simpa [c] using hτ
    · refine (mem_convexHull_stdVertex_iff c y).2 ⟨hyc.1, hy1, fun τ hτ ↦ ?_⟩
      exact Classical.byContradiction fun h ↦ hτ (by simp [c, h])

/-- **The open simplex of a chain is mapped into the open simplex of its top face.** -/
theorem exists_baryMap_image_openSimplex_subset {Δ : Set (Finset ν)}
    (hne : ∀ s ∈ Δ, s.Nonempty) {c : Finset (Finset ν)} (hc : c ∈ sdFaces Δ) :
    ∃ M ∈ c, (∀ τ ∈ c, τ ⊆ M) ∧ baryMap '' openSimplex (c.map (stdVertex (Finset ν))) ⊆
      openSimplex (M.map (stdVertex ν)) := by
  obtain ⟨M, hMc, hMmax⟩ := exists_greatest_of_isChain hc.2.2 hc.1
  refine ⟨M, hMc, hMmax, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have hy' := (mem_openSimplex_stdVertex_iff c y).1 hy
  obtain ⟨hyc, hy1, -⟩ := isChainSupported_of_mem_convexHull hne hc
    (openSimplex_subset_convexHull _ hy)
  have hyM : y M ≠ 0 := (hy'.1 M hMc).ne'
  have hsupp := support_baryMap hyc hyM fun τ hτ ↦ hMmax τ
    (Classical.byContradiction fun h ↦ hτ (hy'.2.2 τ h))
  refine (mem_openSimplex_stdVertex_iff M _).2 ⟨fun v hv ↦ ?_, ?_, fun v hv ↦ ?_⟩
  · exact (baryMap_nonneg hyc.1 v).lt_of_ne' ((hsupp v).2 hv)
  · rw [sum_baryMap hyc.2.1, hy1]
  · exact Classical.byContradiction fun h ↦ hv ((hsupp v).1 h)

/-- The barycentre of a nonempty face `τ ⊆ M` lies in the open simplex of `τ` and in the closed
simplex of `M`. -/
theorem baryMap_stdVertex_mem {τ M : Finset ν} (hτ : τ.Nonempty) (hτM : τ ⊆ M) :
    baryMap (stdVertex (Finset ν) τ) ∈ openSimplex (τ.map (stdVertex ν)) ∧
      baryMap (stdVertex (Finset ν) τ) ∈ convexHull ℝ (M.map (stdVertex ν) : Set (ν → ℝ)) := by
  have hc : (0 : ℝ) < τ.card := by exact_mod_cast hτ.card_pos
  have hval : ∀ v, baryMap (stdVertex (Finset ν) τ) v = if v ∈ τ then ((τ.card : ℝ))⁻¹ else 0 :=
    fun v ↦ by rw [stdVertex_eq, baryMap_single, one_mul]
  have hsum : ∑ v, baryMap (stdVertex (Finset ν) τ) v = 1 := by
    rw [sum_baryMap fun σ' h ↦ ?_]
    · rw [stdVertex_eq, Finset.sum_eq_single τ (fun b _ hb ↦ by simp [hb])
        (fun h ↦ absurd (Finset.mem_univ τ) h), Pi.single_eq_same]
    · by_cases hσ : σ' = τ
      · exact hσ ▸ hτ
      · simp [stdVertex_eq, hσ] at h
  refine ⟨(mem_openSimplex_stdVertex_iff τ _).2 ⟨fun v hv ↦ ?_, hsum, fun v hv ↦ ?_⟩,
    (mem_convexHull_stdVertex_iff M _).2 ⟨fun v ↦ ?_, hsum, fun v hv ↦ ?_⟩⟩
  · simp only [hval, hv, ↓reduceIte]
    positivity
  · simp [hval, hv]
  · rw [hval]
    split_ifs <;> positivity
  · simp [hval, show v ∉ τ from fun h ↦ hv (hτM h)]

/-- **After subdivision, a closed union of open simplices is determined by the vertices.** Let
`Z ⊆ ℝ^ν` be closed and, on each open simplex of `Δ`, contain it or miss it. Then the image of
the open simplex of a chain `c` lies in `Z` if and only if the barycentres of all members of `c`
lie in `Z`. -/
theorem baryMap_image_openSimplex_subset_iff {Δ : Set (Finset ν)} (hne : ∀ s ∈ Δ, s.Nonempty)
    {Z : Set (ν → ℝ)} (hZ : IsClosed Z)
    (hZc : ∀ s ∈ Δ, openSimplex (s.map (stdVertex ν)) ⊆ Z ∨
      Disjoint (openSimplex (s.map (stdVertex ν))) Z)
    {c : Finset (Finset ν)} (hc : c ∈ sdFaces Δ) :
    baryMap '' openSimplex (c.map (stdVertex (Finset ν))) ⊆ Z ↔
      ∀ τ ∈ c, baryMap (stdVertex (Finset ν) τ) ∈ Z := by
  obtain ⟨M, hMc, hMmax, hM⟩ := exists_baryMap_image_openSimplex_subset hne hc
  have hMΔ := hc.2.1 M hMc
  have hMne := hne M hMΔ
  refine ⟨fun hsub τ hτ ↦ ?_, fun hall ↦ hM.trans ?_⟩
  · obtain ⟨y, hy⟩ := openSimplex_nonempty (hc.1.map (f := stdVertex (Finset ν)))
    have hcl := hZ.closure_subset_iff.2 <| (hZc M hMΔ).resolve_right fun h1 ↦
      Set.disjoint_left.1 h1 (hM ⟨y, hy, rfl⟩) (hsub ⟨y, hy, rfl⟩)
    rw [closure_openSimplex (hMne.map (f := stdVertex ν))] at hcl
    exact hcl (baryMap_stdVertex_mem (hne τ (hc.2.1 τ hτ)) (hMmax τ hτ)).2
  · exact (hZc M hMΔ).resolve_right fun h1 ↦
      Set.disjoint_left.1 h1 (baryMap_stdVertex_mem hMne subset_rfl).1 (hall M hMc)

/-- **The barycentric subdivision of a standard triangulation is a standard triangulation.** -/
theorem IsStdTriangulation.subdivision {σ : Type*} {Δ : Set (Finset ν)}
    {h : (ν → ℝ) → σ → ℝ} {S : Set (σ → ℝ)} (hT : IsStdTriangulation Δ h S) :
    IsStdTriangulation (sdFaces Δ) (h ∘ baryMap) S := by
  have himg := baryMap_image_stdSpace_sdFaces hT.nonempty hT.down_closed
  have hmaps : MapsTo baryMap (stdSpace (sdFaces Δ)) (stdSpace Δ) := fun y hy ↦
    himg ▸ mem_image_of_mem _ hy
  refine ⟨fun c hc ↦ hc.1, fun c hc d hdc hdne ↦ ⟨hdne, fun τ hτ ↦ hc.2.1 τ (hdc hτ),
    hc.2.2.mono (Finset.coe_subset.2 hdc)⟩, ?_, ?_, ?_⟩
  · exact hT.continuousOn.comp (LinearMap.continuous_of_finiteDimensional baryMap).continuousOn
      hmaps
  · intro y hy y' hy' hyy
    obtain ⟨c, hc, hyc⟩ := mem_iUnion₂.1 hy
    obtain ⟨c', hc', hyc'⟩ := mem_iUnion₂.1 hy'
    exact baryMap_injOn (isChainSupported_of_mem_convexHull hT.nonempty hc hyc).1
      (isChainSupported_of_mem_convexHull hT.nonempty hc' hyc').1
      (hT.injOn (hmaps hy) (hmaps hy') hyy)
  · rw [image_comp, himg, hT.image_eq]

/-- Compatibility passes to the barycentric subdivision. -/
theorem IsStdTriangulation.subdivision_compat {σ : Type*} {Δ : Set (Finset ν)}
    {h : (ν → ℝ) → σ → ℝ} {S : Set (σ → ℝ)} (hT : IsStdTriangulation Δ h S) {A : Set (σ → ℝ)}
    (hA : ∀ s ∈ Δ, h '' openSimplex (s.map (stdVertex ν)) ⊆ A ∨
      Disjoint (h '' openSimplex (s.map (stdVertex ν))) A) :
    ∀ c ∈ sdFaces Δ, (h ∘ baryMap) '' openSimplex (c.map (stdVertex (Finset ν))) ⊆ A ∨
      Disjoint ((h ∘ baryMap) '' openSimplex (c.map (stdVertex (Finset ν)))) A := by
  intro c hc
  obtain ⟨M, hMc, -, hM⟩ := exists_baryMap_image_openSimplex_subset hT.nonempty hc
  rw [image_comp]
  rcases hA M (hc.2.1 M hMc) with h1 | h1
  · exact Or.inl ((image_mono hM).trans h1)
  · exact Or.inr (h1.mono_left (image_mono hM))

end Subdivision

end MMP
