module

public import MMP.AlgebraicGeometry.Semialgebraic.Triangulation

/-!
# The standard realization of a finite abstract simplicial complex

A down-closed family `Δ` of nonempty finite subsets of a finite type `ν` (an abstract simplicial
complex with vertex set `ν`) is realized in `ℝ^ν` by sending the vertex `v` to the standard
basis vector `eᵥ = Pi.single v 1`. The faces are affinely independent and meet along common
faces automatically: a point of the convex hull of `{eᵥ | v ∈ s}` is a weight vector, that is a
nonnegative function on `ν` of total mass one vanishing off `s`
(`MMP.mem_convexHull_stdVertex_iff`), and it lies in the open simplex of `s` exactly when it is
moreover positive on `s` (`MMP.mem_openSimplex_stdVertex_iff`).

## Main definitions

* `MMP.stdVertex`: the vertex `v ↦ eᵥ`, as an embedding `ν ↪ (ν → ℝ)`.
* `MMP.stdSimplicialComplex`: the realization of `Δ` in `ℝ^ν`.

## Main results

* `MMP.mem_convexHull_stdVertex_iff`: the closed simplex is the set of weight vectors supported
  on `s`.
* `MMP.mem_openSimplex_stdVertex_iff`: the open simplex is the set of weight vectors with support
  exactly `s`.
* `MMP.mem_space_stdSimplicialComplex_iff`: the polyhedron of the realization.
-/

@[expose] public section

open Set

namespace MMP

variable {ν : Type*}

/-- The vertex `v ↦ eᵥ = Pi.single v 1` of the standard realization. -/
noncomputable def stdVertex (ν : Type*) [DecidableEq ν] : ν ↪ (ν → ℝ) where
  toFun v := Pi.single v 1
  inj' a b h := by
    have := congrFun h a
    by_contra hab
    simp [Ne.symm hab] at this

variable [DecidableEq ν]

/-- The standard vertex `stdVertex ν v` is `Pi.single v 1`. -/
theorem stdVertex_eq (v : ν) : stdVertex ν v = Pi.single v 1 := rfl

/-- The coordinate `u` of the standard vertex `stdVertex ν v` is `1` if `u = v` and `0`
otherwise. -/
theorem stdVertex_apply (v u : ν) : stdVertex ν v u = if u = v then 1 else 0 := by
  rw [stdVertex_eq, Pi.single_apply]

/-- The `u`-coordinate of `∑ v ∈ s, w v • eᵥ` is `w u` if `u ∈ s` and `0` otherwise. -/
theorem sum_smul_stdVertex_apply (s : Finset ν) (w : ν → ℝ) (u : ν) :
    (∑ v ∈ s, w v • stdVertex ν v) u = if u ∈ s then w u else 0 := by
  simp only [Finset.sum_apply, Pi.smul_apply, stdVertex_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq]

variable [Fintype ν]

/-- The weights `y ↦ ∑ u, y u * x u` of a weight vector `x` supported on `s` sum to one over the
standard vertices of `s`. -/
theorem sum_map_stdVertex_weight_eq_one (s : Finset ν) {x : ν → ℝ}
    (h1 : ∑ v, x v = 1) (hs : ∀ v ∉ s, x v = 0) :
    ∑ y ∈ s.map (stdVertex ν), ∑ u, y u * x u = 1 := by
  have hsx : ∑ v ∈ s, x v = 1 := by
    rw [← h1, ← Finset.sum_subset (Finset.subset_univ s) fun v _ hv ↦ hs v hv]
  simp only [Finset.sum_map, stdVertex_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, hsx]

/-- A weight vector `x` supported on `s` is the combination of the standard vertices of `s`
with the weights `y ↦ ∑ u, y u * x u`. -/
theorem sum_map_stdVertex_weight_smul (s : Finset ν) {x : ν → ℝ} (hs : ∀ v ∉ s, x v = 0) :
    ∑ y ∈ s.map (stdVertex ν), (∑ u, y u * x u) • y = x := by
  funext u
  simp only [Finset.sum_map, stdVertex_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [sum_smul_stdVertex_apply]
  split_ifs with h
  · rfl
  · exact (hs u h).symm

/-- **The closed simplex of standard vertices** is the set of weight vectors supported on `s`. -/
theorem mem_convexHull_stdVertex_iff (s : Finset ν) (x : ν → ℝ) :
    x ∈ convexHull ℝ (s.map (stdVertex ν) : Set (ν → ℝ)) ↔
      (∀ v, 0 ≤ x v) ∧ ∑ v, x v = 1 ∧ ∀ v ∉ s, x v = 0 := by
  rw [Finset.mem_convexHull']
  constructor
  · rintro ⟨w, hw0, hw1, rfl⟩
    simp only [Finset.sum_map] at hw1 ⊢
    have hev := sum_smul_stdVertex_apply s (fun v ↦ w (stdVertex ν v))
    refine ⟨fun u ↦ ?_, ?_, fun u hu ↦ ?_⟩
    · rw [hev]
      split_ifs with h
      exacts [hw0 _ (Finset.mem_map_of_mem _ h), le_rfl]
    · simp only [hev, Finset.sum_ite_mem, Finset.univ_inter, hw1]
    · simp [hev, hu]
  · rintro ⟨h0, h1, hs⟩
    refine ⟨fun y ↦ ∑ u, y u * x u, fun y hy ↦ ?_, sum_map_stdVertex_weight_eq_one s h1 hs,
      sum_map_stdVertex_weight_smul s hs⟩
    obtain ⟨v, -, rfl⟩ := Finset.mem_map.1 hy
    simpa [stdVertex_apply] using h0 v

/-- **The open simplex of standard vertices** is the set of weight vectors with support `s`. -/
theorem mem_openSimplex_stdVertex_iff (s : Finset ν) (x : ν → ℝ) :
    x ∈ openSimplex (s.map (stdVertex ν)) ↔
      (∀ v ∈ s, 0 < x v) ∧ ∑ v, x v = 1 ∧ ∀ v ∉ s, x v = 0 := by
  constructor
  · rintro ⟨w, hw0, hw1, rfl⟩
    simp only [Finset.sum_map] at hw1 ⊢
    have hev := sum_smul_stdVertex_apply s (fun v ↦ w (stdVertex ν v))
    refine ⟨fun u hu ↦ ?_, ?_, fun u hu ↦ ?_⟩
    · simp only [hev, hu, ↓reduceIte]
      exact hw0 _ (Finset.mem_map_of_mem _ hu)
    · simp only [hev, Finset.sum_ite_mem, Finset.univ_inter, hw1]
    · simp [hev, hu]
  · rintro ⟨h0, h1, hs⟩
    refine ⟨fun y ↦ ∑ u, y u * x u, fun y hy ↦ ?_, sum_map_stdVertex_weight_eq_one s h1 hs,
      sum_map_stdVertex_weight_smul s hs⟩
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.1 hy
    simpa [stdVertex_apply] using h0 v hv

omit [Fintype ν] in
/-- The standard vertices indexed by a finite set `s` are affinely independent. -/
theorem affineIndependent_stdVertex (s : Finset ν) :
    AffineIndependent ℝ ((↑) : (s.map (stdVertex ν) : Set (ν → ℝ)) → ν → ℝ) := by
  have hli : LinearIndependent ℝ (stdVertex ν) := Pi.linearIndependent_single_one ν ℝ
  refine (hli.affineIndependent ℝ).range.mono ?_
  intro y hy
  obtain ⟨v, -, rfl⟩ := Finset.mem_map.1 hy
  exact mem_range_self v

/-- **The standard realization** of a down-closed family `Δ` of nonempty finite subsets of `ν`:
the simplicial complex in `ℝ^ν` whose faces are the sets `{eᵥ | v ∈ s}`, `s ∈ Δ`. -/
noncomputable def stdSimplicialComplex (Δ : Set (Finset ν)) (hne : ∀ s ∈ Δ, s.Nonempty)
    (hdown : ∀ s ∈ Δ, ∀ t ⊆ s, t.Nonempty → t ∈ Δ) : Geometry.SimplicialComplex ℝ (ν → ℝ) where
  faces := (fun s ↦ s.map (stdVertex ν)) '' Δ
  isRelLowerSet_faces := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨(hne s hs).map, fun t hts htne ↦ ?_⟩
    refine ⟨t.preimage (stdVertex ν) (stdVertex ν).injective.injOn, hdown s hs _ ?_ ?_, ?_⟩
    · intro v hv
      rw [Finset.mem_preimage] at hv
      obtain ⟨u, hu, huv⟩ := Finset.mem_map.1 (hts hv)
      exact (stdVertex ν).injective huv ▸ hu
    · obtain ⟨y, hy⟩ := htne
      obtain ⟨v, -, rfl⟩ := Finset.mem_map.1 (hts hy)
      exact ⟨v, Finset.mem_preimage.2 hy⟩
    · ext y
      simp only [Finset.mem_map, Finset.mem_preimage]
      refine ⟨fun ⟨v, hv, hvy⟩ ↦ hvy ▸ hv, fun hy ↦ ?_⟩
      obtain ⟨v, -, rfl⟩ := Finset.mem_map.1 (hts hy)
      exact ⟨v, hy, rfl⟩
  indep := by
    rintro _ ⟨s, -, rfl⟩
    exact affineIndependent_stdVertex s
  inter_subset_convexHull := by
    rintro _ _ ⟨s, -, rfl⟩ ⟨t, -, rfl⟩ x ⟨hxs, hxt⟩
    rw [mem_convexHull_stdVertex_iff] at hxs hxt
    have h := (mem_convexHull_stdVertex_iff (s ∩ t) x).2
      ⟨hxs.1, hxs.2.1, fun v hv ↦ by
        rw [Finset.mem_inter, not_and_or] at hv
        rcases hv with hv | hv
        exacts [hxs.2.2 v hv, hxt.2.2 v hv]⟩
    rwa [Finset.map_inter, Finset.coe_inter] at h

/-- The faces of `stdSimplicialComplex Δ hne hdown` are the images `{eᵥ | v ∈ s}` of the sets
`s ∈ Δ`. -/
theorem mem_faces_stdSimplicialComplex {Δ : Set (Finset ν)} {hne : ∀ s ∈ Δ, s.Nonempty}
    {hdown : ∀ s ∈ Δ, ∀ t ⊆ s, t.Nonempty → t ∈ Δ} {t : Finset (ν → ℝ)} :
    t ∈ (stdSimplicialComplex Δ hne hdown).faces ↔ ∃ s ∈ Δ, s.map (stdVertex ν) = t :=
  Iff.rfl

/-- The polyhedron of the standard realization: the weight vectors supported on a face. -/
theorem mem_space_stdSimplicialComplex_iff {Δ : Set (Finset ν)} {hne : ∀ s ∈ Δ, s.Nonempty}
    {hdown : ∀ s ∈ Δ, ∀ t ⊆ s, t.Nonempty → t ∈ Δ} {x : ν → ℝ} :
    x ∈ (stdSimplicialComplex Δ hne hdown).space ↔
      ∃ s ∈ Δ, (∀ v, 0 ≤ x v) ∧ ∑ v, x v = 1 ∧ ∀ v ∉ s, x v = 0 := by
  rw [Geometry.SimplicialComplex.mem_space_iff]
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, hx⟩
    exact ⟨s, hs, (mem_convexHull_stdVertex_iff s x).1 hx⟩
  · rintro ⟨s, hs, hx⟩
    exact ⟨_, ⟨s, hs, rfl⟩, (mem_convexHull_stdVertex_iff s x).2 hx⟩

/-- The standard realization has finitely many faces. -/
theorem finite_faces_stdSimplicialComplex {Δ : Set (Finset ν)} {hne : ∀ s ∈ Δ, s.Nonempty}
    {hdown : ∀ s ∈ Δ, ∀ t ⊆ s, t.Nonempty → t ∈ Δ} :
    (stdSimplicialComplex Δ hne hdown).faces.Finite :=
  (Set.toFinite Δ).image _

end MMP
