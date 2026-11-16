module
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.PairClasses
public import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGermTypes
public import MMP.AlgebraicGeometry.Singularities.Basic
import MMP.Combinatorics.WeightedGraph.BranchValues
import MMP.Combinatorics.WeightedGraph.Shapes
import MMP.AlgebraicGeometry.Morphisms.Birational.RationalMap
import MMP.AlgebraicGeometry.Divisor.Principal
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.Corollaries
import MMP.AlgebraicGeometry.Singularities.Surface.PointBlowupLogDiscrepancy
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Resolution.Surface.MinimalResolution
import MMP.AlgebraicGeometry.Singularities.Surface.WeightedDualGraph
import MMP.AlgebraicGeometry.Intersection.Surface.BlowupGenusDropAdjunction
import MMP.AlgebraicGeometry.Singularities.Surface.LcRationalTree
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBirationalTransform
import MMP.AlgebraicGeometry.Singularities.Surface.WeightedGraphLogDiscrepancy
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.NormalThreefoldSlice
import MMP.AlgebraicGeometry.Singularities.Surface.DualGraphBoundaryDegree
import MMP.AlgebraicGeometry.Singularities.LogCanonicalOneResolution
import MMP.AlgebraicGeometry.Resolution.CurveOnSurface.PointBlowupCharts
import MMP.AlgebraicGeometry.Curves.PluricanonicalSectionsSeparatePoints
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Singularities.Surface.ReducedBoundaryLc
import MMP.AlgebraicGeometry.Singularities.SurfaceNodalBoundary

/-!
# Log terminal surface germs with reduced boundary

Let `(X, P; B)` be a surface germ with reduced boundary over an algebraically closed field `k`,
and let `f` be its minimal resolution, with exceptional curves `E_1, …, E_n`. If `(X, B)` is log
terminal near `P`, then `(X, P; B)` is of type (1), (2) or (3) of FA Fig. 3, or of type (9) with
`n = 0` and `B` having exactly two components (the node `xy = 0` at a smooth point).

The case `B ≠ 0`, `n ≥ 1` is the heart of it. Let `Γ = Γ(f)` and `a = a(Γ)`; log terminality
makes every `a_j > 0`. The boundary points `(C, y)` of `f` are finite in number: `y` lies on the
connected fibre `f⁻¹(P)`, hence on some `E_j`, and `C ∩ E_j` is finite. So `Γ^*(f)` exists, the
`β_j` are integers, and some `β_j ≥ 1`. Hence `Γ` is a rational tree, a chain or a star with
three arms. For a star with centre `v` the branch decomposition writes `a_v` as a positive
multiple of `c_v + ∑_i σ_i / Δ_i ≤ 0`, which is impossible. For a chain, positivity of `a`
excludes the two-ended chains (Fig. 3 (9)) and the fork of length one (Fig. 3 (10)), leaving
`β = e_{w_1}`: exactly one boundary point, joined to `w_1` only, which is type (3).

If `B = 0` and `n ≥ 1`, `Γ` is neither a vertex of genus one nor a circle (both have `a = 0`),
so it is a negative definite rational tree with `β = 0`: a chain (type (1)) or a platonic star
(type (2)). If `n = 0`, the germ is log canonical, hence of type (1), (3) or (9); in type (9)
`mult_P B = 2`, so `B` has one or two components, and one component (a node) is not log
terminal.

## Main results

* `MMP.Flips.IsMinimalGermResolution.isFig3Type3_of_pos`: a germ with nonzero reduced boundary,
  `n ≥ 1` and positive log discrepancy vector is of type (3).
* `MMP.Flips.IsMinimalGermResolution.isFig3Type3_of_isLogTerminal`: a log terminal germ with
  nonzero reduced boundary and `n ≥ 1` is of type (3).
* `MMP.Flips.IsMinimalGermResolution.isFig3Type1_or_isFig3Type2_or_isFig3Type3_of_isLogTerminal`:
  the classification of log terminal surface germs with reduced boundary.

## Implementation notes

The source passes through the log canonical list of types (3), (9), (10) and excludes (9) and
(10) by the vanishing of a log discrepancy. Here positivity of `a` is used throughout: it
excludes the two-ended chains and the forked chain of length one directly from the list of
chains with boundary, and it excludes stars by the branch decomposition at the centre.
Log terminality enters the case `B ≠ 0`, `n ≥ 1` only through positivity of `a`, so that case
is stated for any germ with `a > 0`, in `isFig3Type3_of_pos`; positivity can also be known
numerically, for instance from a larger log terminal boundary.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.17.3,
  3.0.1, 3.2.7, 3.3.1, Fig. 3
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Flips

open MMP.Mori

/-! ### Weighted graphs -/

section Graph

open WeightedGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The weighted graph `Γ[0]`: `Γ` with all boundary degrees set to `0`. -/
private def zeroBoundary (Γ : WeightedGraph V) : WeightedGraph V :=
  { Γ with boundary := 0, boundary_nonneg := fun _ => le_rfl }

private theorem c_eq_c_zeroBoundary_sub (Γ : WeightedGraph V) (k : V) :
    Γ.c k = (zeroBoundary Γ).c k - Γ.boundary k := by
  simp only [WeightedGraph.c, zeroBoundary, Pi.zero_apply]
  ring

/-- `σ(Γ, v, Γ_i) = 1 - ∑_{k ∈ Γ_i} Δ(Γ_i - path(w_i, k)) β_k` for a chain arm. -/
private theorem branchValue_eq_one_sub (Γ : WeightedGraph V) (hs : Γ.HasSimpleEdges) {v : V}
    {C : Finset V} (hC : Γ.IsChainAttachedAtEnd v C) :
    Γ.branchValue v C = 1 - ∑ k ∈ C,
      (Γ.delta (C \ Γ.treePath (Γ.branchNeighbor v C) k) : ℚ) * Γ.boundary k := by
  obtain ⟨ht, hcomp, s, hs0, e, he, hadj, huniq⟩ := hC
  have h1 : (zeroBoundary Γ).branchValue v C = 1 :=
    (zeroBoundary Γ).branchValue_eq_one_of_isChainAttachedAtEnd hs
      ⟨ht, hcomp, s, hs0, e, ⟨he.genus_eq_zero, he.edgeWeight_eq⟩, hadj, huniq⟩
      (fun _ _ => rfl)
  rw [← h1]
  simp only [branchValue, c_eq_c_zeroBoundary_sub Γ, mul_sub, Finset.sum_sub_distrib]
  rfl

/-- A negative definite weighted graph has positive determinant. -/
private theorem det_pos {Γ : WeightedGraph V} (hneg : Γ.IsNegDef) : 0 < Γ.det := by
  have h := hneg.delta_pos Finset.univ
  rw [← det_restrict, WeightedGraph.det, ← Matrix.det_submatrix_equiv_self
    (Equiv.subtypeUnivEquiv Finset.mem_univ).symm] at h
  convert h using 1
  rw [WeightedGraph.det]
  congr 1
  ext x y
  simp only [WeightedGraph.matrix, Matrix.neg_apply, Matrix.of_apply, Matrix.submatrix_apply,
    Equiv.subtypeUnivEquiv_symm_apply, Subtype.ext_iff]
  rfl

/-- A chain arm with all weights `≥ 2` has determinant `≥ 2`. -/
private theorem two_le_delta {Γ : WeightedGraph V} (hw : ∀ j, 2 ≤ Γ.weight j) {v : V}
    {C : Finset V} (hC : Γ.IsChainAttachedAtEnd v C) : 2 ≤ Γ.delta C := by
  obtain ⟨-, -, s, hs, e, he, -, -⟩ := hC
  have := add_one_le_det_of_isChainOrder (Γ.restrict C) hs e he fun w => hw w
  unfold WeightedGraph.delta
  push_cast at this
  omega

/-- A negative definite rational tree with integral boundary degrees, not all zero, which is a
star with three arms, has no log discrepancy vector positive at the centre `v`. -/
private theorem false_of_isStar {Γ : WeightedGraph V} (hΓ : Γ.IsRationalTree)
    (hneg : Γ.IsNegDef) {v : V} {arms : Fin 3 → Finset V} (hstar : Γ.IsStar v arms)
    (hβ : ∀ j, ∃ N : ℕ, Γ.boundary j = N) (hpos : ∃ j, 0 < Γ.boundary j)
    {a : V → ℚ} (ha : Γ.IsLogDiscrepancyVector a) (hv : 0 < a v) : False := by
  have hs := hstar.hasSimpleEdges
  let D : Fin 3 → V → ℚ := fun i k =>
    (Γ.delta (arms i \ Γ.treePath (Γ.branchNeighbor v (arms i)) k) : ℚ)
  let S : Fin 3 → ℚ := fun i => ∑ k ∈ arms i, D i k * Γ.boundary k
  have hD : ∀ i k, 1 ≤ D i k := fun i k => by
    have := hneg.delta_pos (arms i \ Γ.treePath (Γ.branchNeighbor v (arms i)) k)
    simp only [D]
    exact_mod_cast this
  have hS0 : ∀ i, 0 ≤ S i := fun i => Finset.sum_nonneg fun k _ =>
    mul_nonneg (by linarith [hD i k]) (Γ.boundary_nonneg k)
  have hσ : ∀ i, Γ.branchValue v (arms i) = 1 - S i := fun i =>
    branchValue_eq_one_sub Γ hs (hstar.isChainAttachedAtEnd i)
  have hΔ : ∀ i, (2 : ℚ) ≤ Γ.delta (arms i) := fun i => by
    exact_mod_cast two_le_delta hΓ.two_le_weight (hstar.isChainAttachedAtEnd i)
  have hterm : ∀ i, (1 - S i) / Γ.delta (arms i) ≤ 1 / 2 := fun i => by
    rw [div_le_iff₀ (by linarith [hΔ i])]
    linarith [hS0 i, hΔ i]
  have hterm1 : ∀ i, 1 ≤ S i → (1 - S i) / Γ.delta (arms i) ≤ 0 := fun i h =>
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith [hΔ i])
  have hQ : 0 < Γ.c v + ∑ i, Γ.branchValue v (arms i) / Γ.delta (arms i) := by
    rw [ha.apply_eq_branchValue_of_isTree hneg hs hstar.isTree v arms hstar.isComponent
      hstar.pairwise_disjoint hstar.biUnion_eq] at hv
    have h1 := hneg.delta_pos (Finset.univ \ {v})
    rw [← Γ.det_removeSet {v}] at h1
    refine pos_of_mul_pos_right hv (div_pos ?_ ?_).le
    · exact_mod_cast h1
    · exact_mod_cast det_pos hneg
  rw [Γ.c_eq_of_hasSimpleEdges hs, hΓ.genus_eq_zero, hstar.degree_eq] at hQ
  simp only [hσ, Fin.sum_univ_three] at hQ
  push_cast at hQ
  have hβv := Γ.boundary_nonneg v
  obtain ⟨j, hj⟩ := hpos
  obtain ⟨N, hN⟩ := hβ j
  have hj1 : 1 ≤ Γ.boundary j := by
    rw [hN] at hj ⊢
    exact_mod_cast (show 0 < N by exact_mod_cast hj)
  by_cases hjv : j = v
  · subst hjv
    linarith [hterm 0, hterm 1, hterm 2]
  have hjU : j ∈ Finset.univ.biUnion arms := by
    rw [hstar.biUnion_eq]
    simp [hjv]
  obtain ⟨i, -, hji⟩ := Finset.mem_biUnion.1 hjU
  have hSi : 1 ≤ S i :=
    le_trans (one_le_mul_of_one_le_of_one_le (hD i j) hj1)
      (Finset.single_le_sum (f := fun k => D i k * Γ.boundary k)
        (fun k _ => mul_nonneg (by linarith [hD i k]) (Γ.boundary_nonneg k)) hji)
  obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  all_goals linarith [hterm 0, hterm 1, hterm 2, hterm1 _ hSi]

omit [DecidableEq V] in
/-- Reading a chain backwards is a chain. -/
private theorem isChainOrder_revPerm {Γ : WeightedGraph V} {s : ℕ} {e : Fin s ≃ V}
    (he : Γ.IsChainOrder e) : Γ.IsChainOrder (Fin.revPerm.trans e) := by
  refine ⟨fun i => he.genus_eq_zero _, fun i j => ?_⟩
  simp only [Equiv.trans_apply, Fin.revPerm_apply]
  rw [he.edgeWeight_eq]
  simp only [Fin.val_rev]
  have := i.2
  have := j.2
  split_ifs <;> omega

/-- The forked chain of length one: on a negative definite rational chain `w_0, w_1, w_2` with
`β = e_{w_1}` and both ends of weight `2`, the log discrepancy at `w_1` vanishes. -/
private theorem logDiscrepancy_eq_zero_of_fork {Γ : WeightedGraph V} (hΓ : Γ.IsRationalTree)
    (hneg : Γ.IsNegDef) {e : Fin 3 ≃ V} (he : Γ.IsChainOrder e)
    (hb : ∀ i : Fin 3, Γ.boundary (e i) = (if (i : ℕ) = 1 then 1 else 0) ∧
      ((i : ℕ) ≠ 1 → Γ.weight (e i) = 2))
    {a : V → ℚ} (ha : Γ.IsLogDiscrepancyVector a) : a (e 1) = 0 := by
  have hbij : Function.Bijective (Sum.elim (fun _ : Fin 1 => e 1) ![e 0, e 2]) := by
    have : Sum.elim (fun _ : Fin 1 => e 1) ![e 0, e 2] =
        e ∘ Sum.elim (fun _ : Fin 1 => (1 : Fin 3)) ![(0 : Fin 3), 2] := by
      funext x
      rcases x with x | x
      · rfl
      · fin_cases x <;> rfl
    rw [this]
    exact e.bijective.comp (by decide)
  have hw : ∀ i : Fin 2, Γ.weight (![e 0, e 2] i) = 2 := by
    intro i
    fin_cases i
    · exact (hb 0).2 (by decide)
    · exact (hb 2).2 (by decide)
  have hβ : ∀ w, Γ.boundary w = if w = e 1 then 1 else 0 := by
    intro w
    obtain ⟨i, rfl⟩ := e.surjective w
    rw [(hb i).1]
    fin_cases i <;> simp [e.apply_eq_iff_eq]
  exact ((WeightedGraph.isLogDiscrepancyVector_iff_of_fork_of_boundary_eq_single hΓ hneg
    Nat.one_pos hbij hw (fun i j => by fin_cases i; fin_cases j; simp [Γ.edgeWeight_self])
    (fun i l => by fin_cases i; fin_cases l <;> simp [he.edgeWeight_eq])
    (fun i l => by fin_cases i <;> fin_cases l <;> simp [he.edgeWeight_eq, Γ.edgeWeight_self])
    hβ).1 ha).1 0

/-- A negative definite rational chain with integral boundary degrees, not all zero, and
positive log discrepancy vector, can be numbered so that `β` is `1` at the first vertex and
`0` elsewhere: in the other cases of the list of chains with boundary some log discrepancy
vanishes. -/
private theorem exists_isChainOrder_boundary_eq_ite {Γ : WeightedGraph V}
    (hΓ : Γ.IsRationalTree) (hneg : Γ.IsNegDef) {s : ℕ} (hs : 0 < s) {e : Fin s ≃ V}
    (he : Γ.IsChainOrder e) (hβ : ∀ j, ∃ N : ℕ, Γ.boundary j = N)
    (hpos : ∃ j, 0 < Γ.boundary j) {a : V → ℚ} (ha : Γ.IsLogDiscrepancyVector a)
    (hapos : ∀ j, 0 < a j) :
    ∃ e' : Fin s ≃ V, Γ.IsChainOrder e' ∧
      ∀ i : Fin s, Γ.boundary (e' i) = if (i : ℕ) = 0 then 1 else 0 := by
  -- two boundary ends force `a = 0`
  have htwo (hb : ∀ i : Fin s, Γ.boundary (e i) =
      (if (i : ℕ) = 0 then 1 else 0) + (if (i : ℕ) + 1 = s then 1 else 0)) : False :=
    (hapos (e ⟨0, hs⟩)).ne' <| congrFun
      ((WeightedGraph.isLogDiscrepancyVector_iff_eq_zero_of_isChainOrder hΓ hneg hs he hb).1
        ha) _
  rcases ha.boundary_cases_of_isChainOrder hΓ hneg hs he hβ hpos fun k => (hapos k).le with
    (hfirst | hlast) | ⟨rfl, hb⟩ | ⟨-, hb⟩ | ⟨rfl, hb⟩
  · exact ⟨e, he, hfirst⟩
  · refine ⟨Fin.revPerm.trans e, isChainOrder_revPerm he, fun i => ?_⟩
    rw [Equiv.trans_apply, Fin.revPerm_apply, hlast, Fin.val_rev]
    have := i.2
    by_cases h : (i : ℕ) = 0
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h]
  · exact absurd (logDiscrepancy_eq_zero_of_fork hΓ hneg he hb ha) (hapos _).ne'
  · exact (htwo hb).elim
  · exact (htwo fun i => by rw [hb i, Subsingleton.elim i 0]; norm_num).elim

end Graph

/-! ### Boundary points -/

section Geometry

/-- In a Noetherian space every point `y` of a closed set `F` lies on a maximal irreducible
subset `Z` of `F`, and `F ⊆ Z ∪ C` for a closed set `C` not containing `Z`. -/
private lemma exists_maximal_isIrreducible_subset {T : Type*} [TopologicalSpace T]
    [TopologicalSpace.NoetherianSpace T] {F : Set T} (hF : IsClosed F) {y : T} (hy : y ∈ F) :
    ∃ Z C : Set T, Maximal (fun W : Set T => IsIrreducible W ∧ W ⊆ F) Z ∧ IsClosed Z ∧ y ∈ Z ∧
      IsClosed C ∧ F ⊆ Z ∪ C ∧ ¬ Z ⊆ C := by
  obtain ⟨S, hSfin, hScl, hSirr, hSeq⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hF
  obtain ⟨T₀, hT₀, hyT₀⟩ : y ∈ ⋃₀ S := hSeq ▸ hy
  obtain ⟨Z, hT₀Z, hZ⟩ := hSfin.exists_le_maximal hT₀
  have hZS : Z ∈ S := hZ.prop
  have hZF : Z ⊆ F := hSeq ▸ Set.subset_sUnion_of_mem hZS
  -- an irreducible subset of `F` lies in a member of `S`
  have hsub : ∀ {W : Set T}, IsIrreducible W → ∀ {S' : Set (Set T)}, S' ⊆ S →
      W ⊆ ⋃₀ S' → ∃ t ∈ S', W ⊆ t := by
    intro W hW S' hS' hWS
    have hfin : S'.Finite := hSfin.subset hS'
    obtain ⟨t, ht, hWt⟩ := (isIrreducible_iff_sUnion_isClosed.mp hW) hfin.toFinset
      (fun t ht => hScl t (hS' (hfin.mem_toFinset.mp ht))) (by simpa using hWS)
    exact ⟨t, hfin.mem_toFinset.mp ht, hWt⟩
  have hmax : Maximal (fun W : Set T => IsIrreducible W ∧ W ⊆ F) Z := by
    refine ⟨⟨hSirr Z hZS, hZF⟩, fun W hW hZW => ?_⟩
    obtain ⟨t, htS, hWt⟩ := hsub hW.1 le_rfl (hSeq ▸ hW.2)
    exact (hZ.2 htS (hZW.trans hWt)).trans' hWt
  refine ⟨Z, ⋃₀ (S \ {Z}), hmax, hScl Z hZS, hT₀Z hyT₀,
    (hSfin.subset Set.diff_subset).isClosed_sUnion fun t ht => hScl t ht.1, ?_, ?_⟩
  · intro x hx
    obtain ⟨t, htS, hxt⟩ := (hSeq ▸ hx : x ∈ ⋃₀ S)
    by_cases htZ : t = Z
    · exact Or.inl (htZ ▸ hxt)
    · exact Or.inr ⟨t, ⟨htS, htZ⟩, hxt⟩
  · intro hZC
    obtain ⟨t, ⟨htS, htZ⟩, hZt⟩ := hsub (hSirr Z hZS) Set.diff_subset hZC
    exact htZ (le_antisymm (hZ.2 htS hZt) hZt)

/-- If there is at least one exceptional curve, every point of the fibre `f⁻¹(P)` lies on an
exceptional curve: the fibre is connected, so an irreducible component of it which is not a
curve would be an isolated closed point. -/
private lemma exists_mem_support_of_fibre {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {P : X} {B : QDivisor X} {f : Y ⟶ X}
    [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y] {n : ℕ}
    {E : Fin n → Mori.PrimeDivisor Y} {Γ : WeightedGraph (Fin n)}
    (hΓ : IsWeightedDualGraph sX P B f E Γ) (u : Fin n) {y : Y} (hy : f y = P) :
    ∃ j, y ∈ (E j).support := by
  have hg := hΓ.isGermResolution
  have hconn : _root_.IsPreconnected (f.base ⁻¹' {P}) := by
    have : IsProper f := hg.isSmoothResolution.isProper
    exact ((MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism
      (f ≫ sX) sX hg.isVariety hg.isSurfaceGerm.1 f
      hg.isSmoothResolution.isBirationalMorphism).2 P).isPreconnected
  have hE := hΓ.isExceptionalCurveEnumeration
  have hYv := hg.isVariety
  have : IsIntegral Y := hYv.toIsIntegral
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  have : IsNoetherian Y := {}
  have hP : IsClosed ({P} : Set X) := hg.isSurfaceGerm.2.2.1
  have hFcl : IsClosed (f.base ⁻¹' {P}) := hP.preimage f.base.hom.continuous
  obtain ⟨Z, C, hZ, hZcl, hyZ, hCcl, hFZC, hZC⟩ := exists_maximal_isIrreducible_subset hFcl hy
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hZ.prop.1 hZcl
  have hξZ : ξ ∈ Z := hξ.mem
  have hEuF : ((E u).support : Set Y) ⊆ f.base ⁻¹' {P} :=
    (hE.isGermExceptionalCurve u).1.prop.2
  -- `ξ` is not a closed point: otherwise `{ξ}` would be open and closed in `f⁻¹(P)`
  have hξncl : ¬ IsClosed ({ξ} : Set Y) := by
    intro hcl
    have hZξ : Z = {ξ} := by rw [← hξ.def, hcl.closure_eq]
    have hξC : ξ ∉ C := fun h => hZC (hZξ ▸ Set.singleton_subset_iff.mpr h)
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hconn {ξ} C hcl hCcl
        (hZξ ▸ hFZC) (by
          ext x
          simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
            iff_false, not_and]
          rintro - rfl
          exact hξC) with h | h
    · exact (((hE.isGermExceptionalCurve u).2).not_subsingleton)
        ((Set.subsingleton_singleton).anti (hEuF.trans h))
    · exact hξC (h (hZ.prop.2 hξZ))
  -- a closed point `c` of `Z` other than `ξ`
  obtain ⟨c, hcZ, hccl⟩ := hZcl.exists_closed_singleton ⟨ξ, hξZ⟩
  have hcξ : c ≠ ξ := fun h => hξncl (h ▸ hccl)
  have hξc : ξ ⤳ c := hξ.specializes hcZ
  have hco2 := MMP.Threefold.Resolution.coheight_eq_two_of_isClosed hYv
    hg.topologicalKrullDim_eq hccl
  -- `ξ` is not the generic point of `Y`, since `f` is an isomorphism away from `P`
  have hξmax : ¬ IsMax ξ := by
    intro hmax
    have : IsIntegral X := hg.isSurfaceGerm.1.1.toIsIntegral
    have := hg.isSmoothResolution.isBirationalMorphism.isDominant
    have h2 : ξ ⤳ genericPoint Y := hmax (genericPoint_specializes ξ)
    have hgη : f (genericPoint Y) = P := hZ.prop.2 (h2.mem_closed hZcl hξZ)
    rw [map_genericPoint_of_isDominant] at hgη
    have : Subsingleton X := ⟨fun a b => by
      have ha := (genericPoint_specializes a).mem_closed hP (by rw [hgη]; rfl)
      have hb := (genericPoint_specializes b).mem_closed hP (by rw [hgη]; rfl)
      rw [Set.mem_singleton_iff] at ha hb
      rw [ha, hb]⟩
    have h0 := topologicalKrullDim_zero_of_discreteTopology X
    rw [hg.isSurfaceGerm.2.1] at h0
    exact absurd h0 (by decide)
  have hco : Order.coheight ξ = 1 := by
    have hcξlt : c < ξ := lt_of_le_not_ge hξc fun h =>
      hcξ ((h : c ⤳ ξ).mem_closed hccl rfl).symm
    have hlt : Order.coheight ξ < 2 := hco2 ▸ Order.coheight_strictAnti hcξlt
      (lt_of_le_of_lt (hco2 ▸ Order.coheight_anti hcξlt.le) (by decide))
    have hne : Order.coheight ξ ≠ 0 := fun h => hξmax (Order.coheight_eq_zero.mp h)
    generalize Order.coheight ξ = d at hlt hne ⊢
    induction d using ENat.recTopCoe with
    | top => exact absurd hlt (by decide)
    | coe d =>
      norm_cast at hlt hne ⊢
      omega
  let D : MMP.Mori.PrimeDivisor Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne ξ hco
  have hDsupp : (D.support : Set Y) = Z := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne, hξ.def]
  obtain ⟨j, hj⟩ := hE.exists_eq D ⟨hDsupp ▸ hZ,
    isCurveIn_idealSheaf_of_topologicalKrullDim_eq_two hYv hg.topologicalKrullDim_eq D⟩
  exact ⟨j, by rwa [hj, hDsupp]⟩

/-- A prime divisor in the support of the transform `mapPrimeDivisors φ D` is the image under `φ`
of some prime divisor. -/
private theorem exists_eq_some_of_mem_support_mapPrimeDivisors {X Y : Scheme.{u}} {R : Type*}
    [AddCommMonoid R] {φ : Mori.PrimeDivisor X → Option (Mori.PrimeDivisor Y)}
    {D : DivisorWithCoeffs R X} {Q : Mori.PrimeDivisor Y}
    (hQ : Q ∈ (DivisorWithCoeffs.mapPrimeDivisors φ D).support) : ∃ E, φ E = some Q := by
  classical
  by_contra! h
  refine Finsupp.mem_support_iff.mp hQ ?_
  clear hQ
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' hD hD' => rw [map_add, Finsupp.add_apply, hD, hD', add_zero]
  | single E r =>
    rw [DivisorWithCoeffs.mapPrimeDivisors_single]
    rcases hφ : φ E with _ | Q'
    · rfl
    · simp [Finsupp.single_apply, show Q' ≠ Q from fun h' => h E (h' ▸ hφ)]

/-- The coefficient of `g⁻¹_*(D)` in `g⁻¹_* B` is that of `D` in `B`. -/
private theorem inverseTransformDivisor_apply_of_eq_some {X Y : Scheme.{u}} {R : Type*}
    [AddCommMonoid R] {g : Y ⟶ X} {D : Mori.PrimeDivisor X} {C : Mori.PrimeDivisor Y}
    (hD : inverseTransformPrimeDivisor g D = some C) (B : DivisorWithCoeffs R X) :
    inverseTransformDivisor g B C = B D :=
  MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hD (fun _ hD' =>
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective <|
      (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
        hD').1.symm.trans
      (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hD).1) B

/-- A component of `g⁻¹_* B` does not lie over the closed point `P` of a surface germ. -/
private theorem map_genericPoint_ne_of_mem_support {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {P : X} (hX : IsSurfaceGerm sX P)
    {g : Y ⟶ X} {B : QDivisor X} {C : Mori.PrimeDivisor Y}
    (hC : C ∈ (inverseTransformDivisor g B).support) : g.base C.genericPoint ≠ P := by
  intro hP
  obtain ⟨D, hD⟩ := exists_eq_some_of_mem_support_mapPrimeDivisors hC
  have h := MMP.Positivity.coheight_map_of_mem_biregularLocus g
    (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hD).2
  rw [hP, MMP.Threefold.Resolution.coheight_eq_two_of_isClosed hX.1.1 hX.2.1 hX.2.2.1,
    C.coheight_genericPoint] at h
  exact absurd h (by decide)

/-- For a resolution `g` with at least one exceptional curve and `B` reduced, the boundary
points of `g` are finite in number, so the extended dual graph `Γ^*(g)` exists, with
`∘`-part any given `Γ(g)`. -/
private theorem exists_isExtendedDualGraph {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {P : X} {B : QDivisor X} {g : Y ⟶ X}
    [QuasiCompact (g ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y] {n : ℕ}
    {E : Fin n → Mori.PrimeDivisor Y} {Γ : WeightedGraph (Fin n)}
    (hΓ : IsWeightedDualGraph sX P B g E Γ) (hred : IsReducedBoundary B) (u : Fin n) :
    ∃ (m : ℕ) (pt : Fin m → Mori.PrimeDivisor Y × Y)
      (Γ' : ExtendedWeightedGraph (Fin n) (Fin m)),
      IsExtendedDualGraph sX P B g E pt Γ' ∧ Γ'.toWeightedGraph = Γ := by
  classical
  have hres := hΓ.isGermResolution
  have hEn := hΓ.isExceptionalCurveEnumeration
  let S : Set (Mori.PrimeDivisor Y × Y) := {p | IsGermBoundaryPoint g P B p.1 p.2}
  have hfin : S.Finite := by
    have hsub : S ⊆ ⋃ C ∈ ((inverseTransformDivisor g B).support : Set (Mori.PrimeDivisor Y)),
        ⋃ j : Fin n, ({C} : Set (Mori.PrimeDivisor Y)) ×ˢ ((E j).support ∩ C.support) := by
      rintro ⟨C, y⟩ ⟨hC, hy, hyP⟩
      obtain ⟨j, hj⟩ := exists_mem_support_of_fibre hΓ u hyP
      simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff, Set.mem_inter_iff,
        Finset.mem_coe]
      exact ⟨C, Finsupp.mem_support_iff.mpr hC, j, rfl, hj, hy⟩
    refine Set.Finite.subset ?_ hsub
    refine Set.Finite.biUnion (Finset.finite_toSet _) fun C hC => Set.finite_iUnion fun j => ?_
    refine (Set.finite_singleton C).prod ?_
    have hEj := hEn.isGermExceptionalCurve j
    have hne : E j ≠ C := fun hCE =>
      map_genericPoint_ne_of_mem_support hres.isSurfaceGerm (Finset.mem_coe.mp hC) <|
        hEj.1.prop.2 <| by
          rw [← hCE, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
          exact subset_closure rfl
    exact (isIntersectionNumber_finsum_localIntersectionNumber_of_ne (g ≫ sX) hres.isVariety
      hres.isSmoothResolution.isSmoothScheme hres.topologicalKrullDim_eq hne
      (IsGermExceptionalCurve.isProper sX hres hEj).2).1
  let F := hfin.toFinset
  let pt : Fin F.card → Mori.PrimeDivisor Y × Y := fun l => (F.equivFin.symm l).1
  refine ⟨F.card, pt, ⟨Γ, fun j l =>
    haveI := Classical.propDecidable ((pt l).2 ∈ (E j).support)
    if (pt l).2 ∈ (E j).support then
      localIntersectionNumber (g ≫ sX) (pt l).2 (Finsupp.single (pt l).1 1)
        (Finsupp.single (E j) 1)
    else 0⟩, ⟨hred, hΓ, ?_, ?_, ?_, fun j l => rfl⟩, rfl⟩
  · exact fun l l' h => F.equivFin.symm.injective (Subtype.ext h)
  · exact fun l => hfin.mem_toFinset.mp (F.equivFin.symm l).2
  · intro C y hCy
    refine ⟨F.equivFin ⟨(C, y), hfin.mem_toFinset.mpr hCy⟩, ?_⟩
    simp [pt]

/-- If `B ≠ 0`, a resolution `g` of the surface germ has a boundary point: a component `C` of
`B` passes through `P`, and `g` is proper, so the transform `g⁻¹_* C` meets `g⁻¹(P)`. -/
private theorem exists_isGermBoundaryPoint {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {P : X} {B : QDivisor X} {g : Y ⟶ X}
    [QuasiCompact (g ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y]
    (hB : IsSurfaceGermWithBoundary sX P B) (hg : IsGermResolution sX P g) (hB0 : B ≠ 0) :
    ∃ C y, IsGermBoundaryPoint g P B C y := by
  obtain ⟨C, hC⟩ := Finsupp.support_nonempty_iff.mpr hB0
  have hXs := hg.isSurfaceGerm
  have : IsProper g := hg.isSmoothResolution.isProper
  obtain ⟨U, hU, hiso⟩ := hg.isIso_away
  obtain ⟨C', hC', hgC'⟩ := exists_inverseTransformPrimeDivisor_eq_some C <|
    le_biregularLocus (V := U) hiso <| show C.genericPoint ∈ (U : Set X) by
      rw [hU]
      intro h
      have h2 := C.coheight_genericPoint
      rw [h, MMP.Threefold.Resolution.coheight_eq_two_of_isClosed hXs.1.1 hXs.2.1
        hXs.2.2.1] at h2
      exact absurd h2 (by decide)
  obtain ⟨y, hyC', hyP⟩ : ∃ y ∈ C'.support, g y = P :=
    (AlgebraicGeometry.PrimeDivisor.support_eq_closure C ▸
      (g.isClosedMap _ C'.idealSheaf.support.isClosed).closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr ⟨_, show C'.genericPoint ∈ C'.support by
          rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
          exact subset_closure rfl, hgC'⟩)) (hB.2.1 C hC)
  exact ⟨C', y, by rwa [inverseTransformDivisor_apply_of_eq_some hC' B,
    ← Finsupp.mem_support_iff], hyC', hyP⟩

section Extended

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {P : X} {B : QDivisor X} {g : Y ⟶ X} [QuasiCompact (g ≫ sX)] [IsLocallyNoetherian Y]
  [IsNormal Y] {n m : ℕ} {E : Fin n → Mori.PrimeDivisor Y} {pt : Fin m → Mori.PrimeDivisor Y × Y}
  {Γ : ExtendedWeightedGraph (Fin n) (Fin m)}

/-- A boundary point on `E_j` contributes at least `1` to `β_j`. -/
private theorem one_le_boundary_of_mem (hext : IsExtendedDualGraph sX P B g E pt Γ) {j : Fin n}
    {l : Fin m} (hl : (pt l).2 ∈ (E j).support) : (1 : ℚ) ≤ Γ.toWeightedGraph.boundary j := by
  classical
  have hdeg := hext.boundary_eq_sum_boundaryEdgeWeight j
  rw [hdeg.1]
  exact le_trans (by exact_mod_cast hdeg.2 l hl)
    (Finset.single_le_sum (f := fun l => (Γ.boundaryEdgeWeight j l : ℚ))
      (fun _ _ => Nat.cast_nonneg _) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hl⟩))

/-- If `β = e_{j₁}` and there is an exceptional curve, then `Γ^*(g)` has exactly one boundary
point, joined by an edge of weight `1` to `j₁` and to no other vertex. -/
private theorem eq_one_and_boundaryEdgeWeight_eq (hext : IsExtendedDualGraph sX P B g E pt Γ)
    (u : Fin n) {j₁ : Fin n} (hβ : ∀ j, Γ.toWeightedGraph.boundary j = if j = j₁ then 1 else 0) :
    m = 1 ∧ ∀ j l, Γ.boundaryEdgeWeight j l = if j = j₁ then 1 else 0 := by
  classical
  have hoff : ∀ l j, j ≠ j₁ → (pt l).2 ∉ (E j).support := fun l j hj h => by
    have := one_le_boundary_of_mem hext h
    rw [hβ, if_neg hj] at this
    norm_num at this
  have hon : ∀ l, (pt l).2 ∈ (E j₁).support := fun l => by
    obtain ⟨j, hj⟩ := exists_mem_support_of_fibre hext.isWeightedDualGraph u
      (hext.isGermBoundaryPoint l).2.2
    by_cases hjj : j = j₁
    · exact hjj ▸ hj
    · exact absurd hj (hoff l j hjj)
  have hdeg := hext.boundary_eq_sum_boundaryEdgeWeight j₁
  have hsum : ∑ l, Γ.boundaryEdgeWeight j₁ l = 1 := by
    have := hdeg.1
    rw [hβ, if_pos rfl, Finset.filter_true_of_mem fun l _ => hon l] at this
    exact_mod_cast this.symm
  obtain rfl : m = 1 := by
    have hle := Finset.card_nsmul_le_sum Finset.univ (Γ.boundaryEdgeWeight j₁) 1
      fun l _ => hdeg.2 l (hon l)
    rcases m with _ | _ | m
    · simp at hsum
    · rfl
    · simp [hsum] at hle
  refine ⟨rfl, fun j l => ?_⟩
  rw [Subsingleton.elim l 0]
  split_ifs with hj
  · rwa [hj, ← Fin.sum_univ_one (Γ.boundaryEdgeWeight j₁)]
  · rw [hext.boundaryEdgeWeight_eq, if_neg (hoff 0 j hj)]

end Extended

end Geometry

/-- **Germs with nonzero reduced boundary and positive log discrepancies** (FA 3.3.1,
Fig. 3 (3)). Let `(X, P; B)` be a surface germ over an algebraically closed field `k` with
reduced boundary `B ≠ 0`, and let `f` be its minimal resolution, with `n ≥ 1` exceptional curves
`E_1, …, E_n`. If the log discrepancy vector of `(X, P; B)` along `f` is positive, then
`(X, P; B)` is of type (3). -/
public theorem IsMinimalGermResolution.isFig3Type3_of_pos
    {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {P : X} {B : QDivisor X} {f : Y ⟶ X} [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y]
    [IsNormal Y] {n : ℕ} {E : Fin n → Mori.PrimeDivisor Y}
    (hB : IsSurfaceGermWithBoundary sX P B) (hred : IsReducedBoundary B) (hB0 : B ≠ 0)
    (hf : IsMinimalGermResolution sX P f) (hE : IsExceptionalCurveEnumeration f P E)
    (hn : 1 ≤ n)
    (hpos : ∀ a : Fin n → ℚ, IsGermLogDiscrepancyVector sX P B f E a → ∀ j, 0 < a j) :
    IsFig3Type3 sX P B := by
  classical
  obtain ⟨Γ₀, hΓ₀⟩ := hf.1.exists_isWeightedDualGraph hB hE
  obtain ⟨m, pt, Γe, hext, rfl⟩ := exists_isExtendedDualGraph hΓ₀ hred ⟨0, hn⟩
  have hΓ := hext.isWeightedDualGraph
  have hneg := hΓ.isNegDef
  have hβint : ∀ j, ∃ N : ℕ, Γe.toWeightedGraph.boundary j = N := fun j =>
    ⟨_, (hext.boundary_eq_sum_boundaryEdgeWeight j).1.trans (Nat.cast_sum _ _).symm⟩
  -- a boundary point exists, so some `β_j ≥ 1`
  obtain ⟨C, y, hbp⟩ := exists_isGermBoundaryPoint hB hf.1 hB0
  obtain ⟨jp, hjy⟩ := exists_mem_support_of_fibre hΓ ⟨0, hn⟩ hbp.2.2
  obtain ⟨lp, hlp⟩ := hext.exists_eq C y hbp
  have hjp : 0 < Γe.toWeightedGraph.boundary jp :=
    zero_lt_one.trans_le (one_le_boundary_of_mem hext (l := lp) (by rwa [hlp]))
  -- the log discrepancy vector, positive by hypothesis
  obtain ⟨a, ha, -⟩ := Γe.toWeightedGraph.existsUnique_isLogDiscrepancyVector (det_pos hneg).ne'
  have hapos : ∀ j, 0 < a j := hpos a ((hΓ.isGermLogDiscrepancyVector_iff a).2 ha)
  have ha0 : ∀ j, 0 ≤ a j := fun j => (hapos j).le
  -- `Γ` is a rational tree, and a chain or a star
  have hrat : Γe.toWeightedGraph.IsRationalTree :=
    hf.isRationalTree_of_logDiscrepancy_nonneg hΓ ha ha0
      (fun h => by have := (h.2 jp).2; linarith)
      (fun ⟨e, he⟩ => by
        have := he.boundary_eq_zero (e.symm jp)
        rw [Equiv.apply_symm_apply] at this
        linarith)
  rcases hf.isWeightedChain_or_isStar_of_boundary_pos hΓ hrat ⟨jp, hjp⟩ ha ha0 with
    ⟨s, e, he⟩ | ⟨v, arms, hstar, -⟩
  swap
  · exact (false_of_isStar hrat hneg hstar hβint ⟨jp, hjp⟩ ha (hapos v)).elim
  obtain rfl : n = s := by simpa using (Fintype.card_congr e).symm
  obtain ⟨e', he', hb'⟩ :=
    exists_isChainOrder_boundary_eq_ite hrat hneg hn he hβint ⟨jp, hjp⟩ ha hapos
  obtain ⟨rfl, hw⟩ := eq_one_and_boundaryEdgeWeight_eq hext ⟨0, hn⟩ (j₁ := e' ⟨0, hn⟩)
    fun j => by
      obtain ⟨i, rfl⟩ := e'.surjective j
      simp [hb', Fin.ext_iff]
  exact ⟨hB, Y, f, inferInstance, inferInstance, inferInstance, n, E, hf, hE,
    Or.inr ⟨hn, pt, Γe, e', hext, he', hrat.two_le_weight, fun j => hw j 0⟩⟩

/-- **Log terminal germs with nonzero reduced boundary** (FA 3.3.1, Fig. 3 (3)). Let
`(X, P; B)` be a surface germ over an algebraically closed field `k` with reduced boundary
`B ≠ 0`, and let `f` be its minimal resolution, with `n ≥ 1` exceptional curves
`E_1, …, E_n`. If `(X, B)` is log terminal near `P` (on some open neighbourhood `U` of `P`,
`(U, B|_U)` is log terminal with canonical divisor `K_X|_U`), then `(X, P; B)` is of
type (3). -/
@[mmp "lem_fa3_reduced_boundary_lt_graph_list"]
public theorem IsMinimalGermResolution.isFig3Type3_of_isLogTerminal
    {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    {P : X} {B : QDivisor X} {f : Y ⟶ X} [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y]
    [IsNormal Y] {n : ℕ} {E : Fin n → Mori.PrimeDivisor Y}
    (hB : IsSurfaceGermWithBoundary sX P B) (hred : IsReducedBoundary B) (hB0 : B ≠ 0)
    (hf : IsMinimalGermResolution sX P f) (hE : IsExceptionalCurveEnumeration f P E)
    (hn : 1 ≤ n) {K : Divisor X} (hK : K.IsCanonicalDivisor sX 2)
    (hlt : HoldsOnGerm {P} fun U : X.Opens => ∀ [Nonempty U],
      haveI : CompactSpace U := isCompact_iff_compactSpace.mp
        (@NoetherianSpace.isCompact _ _ (haveI : IsNoetherian X := {}; inferInstance) _)
      IsLogTerminal (U.ι ≫ sX) 2 (DivisorWithCoeffs.restrictOpen U K)
        (DivisorWithCoeffs.restrictOpen U (QDivisor.toRDivisor B))) :
    IsFig3Type3 sX P B :=
  hf.isFig3Type3_of_pos hB hred hB0 hE hn fun _ ha => ha.pos_of_isLogTerminal hf hK hlt

/-! ### The classification -/

section Classification

open WeightedGraph

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
  {P : X} {B : QDivisor X} {K : Divisor X}

/-- Log terminal near `P` implies log canonical near `P`. -/
private theorem holdsOnGerm_isLogCanonical
    (hlt : HoldsOnGerm {P} fun U : X.Opens => ∀ [Nonempty U],
      haveI : CompactSpace U := isCompact_iff_compactSpace.mp
        (@NoetherianSpace.isCompact _ _ (haveI : IsNoetherian X := {}; inferInstance) _)
      IsLogTerminal (U.ι ≫ sX) 2 (DivisorWithCoeffs.restrictOpen U K)
        (DivisorWithCoeffs.restrictOpen U (QDivisor.toRDivisor B))) :
    HoldsOnGerm {P} fun U : X.Opens => ∀ [Nonempty U],
      haveI : CompactSpace U := isCompact_iff_compactSpace.mp
        (@NoetherianSpace.isCompact _ _ (haveI : IsNoetherian X := {}; inferInstance) _)
      IsLogCanonical (U.ι ≫ sX) 2 (DivisorWithCoeffs.restrictOpen U K)
        (DivisorWithCoeffs.restrictOpen U (QDivisor.toRDivisor B)) := by
  obtain ⟨U, hPU, hU⟩ := hlt
  refine ⟨U, hPU, ?_⟩
  intro _
  have : CompactSpace U := isCompact_iff_compactSpace.mp
    (@NoetherianSpace.isCompact _ _ (haveI : IsNoetherian X := {}; inferInstance) _)
  exact hU.isLogCanonical

/-- A chain `Γ(f)` whose two ends each meet one of two distinct boundary points with weight `1`
has log discrepancy vector `0`, so such a germ is not log terminal near `P`. -/
private theorem not_isLogTerminal_of_isChainOrder {Y : Scheme.{u}} {f : Y ⟶ X}
    [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y] {n : ℕ}
    {E : Fin n → Mori.PrimeDivisor Y} {pt : Fin 2 → Mori.PrimeDivisor Y × Y}
    {Γ : ExtendedWeightedGraph (Fin n) (Fin 2)} {e : Fin n ≃ Fin n}
    (hf : IsMinimalGermResolution sX P f) (hn : 1 ≤ n)
    (hext : IsExtendedDualGraph sX P B f E pt Γ) (he : Γ.toWeightedGraph.IsChainOrder e)
    (h0 : ∀ j, Γ.boundaryEdgeWeight j 0 = if j = e ⟨0, hn⟩ then 1 else 0)
    (h1 : ∀ j, Γ.boundaryEdgeWeight j 1 = if j = e ⟨n - 1, by omega⟩ then 1 else 0)
    (hK : K.IsCanonicalDivisor sX 2) :
    ¬ HoldsOnGerm {P} fun U : X.Opens => ∀ [Nonempty U],
      haveI : CompactSpace U := isCompact_iff_compactSpace.mp
        (@NoetherianSpace.isCompact _ _ (haveI : IsNoetherian X := {}; inferInstance) _)
      IsLogTerminal (U.ι ≫ sX) 2 (DivisorWithCoeffs.restrictOpen U K)
        (DivisorWithCoeffs.restrictOpen U (QDivisor.toRDivisor B)) := by
  classical
  intro hlt
  have hΓ := hext.isWeightedDualGraph
  have hneg := hΓ.isNegDef
  obtain ⟨a, ha, -⟩ :=
    Γ.toWeightedGraph.existsUnique_isLogDiscrepancyVector (det_pos hneg).ne'
  have hapos : ∀ j, 0 < a j :=
    ((hΓ.isGermLogDiscrepancyVector_iff a).2 ha).pos_of_isLogTerminal hf hK hlt
  have hβ : ∀ i : Fin n, Γ.toWeightedGraph.boundary (e i) =
      (if (i : ℕ) = 0 then 1 else 0) + (if (i : ℕ) + 1 = n then 1 else 0) := fun i => by
    have hi := i.2
    rw [(hext.boundary_eq_sum_boundaryEdgeWeight (e i)).1, Finset.sum_filter_of_ne,
      Fin.sum_univ_two, h0, h1]
    · simp only [e.apply_eq_iff_eq, Fin.ext_iff]
      split_ifs <;> first | omega | norm_num
    · intro l _ hl
      by_contra hmem
      rw [hext.boundaryEdgeWeight_eq, if_neg hmem] at hl
      simp at hl
  have hrat : Γ.toWeightedGraph.IsRationalTree :=
    hf.isRationalTree_of_logDiscrepancy_nonneg hΓ ha (fun j => (hapos j).le)
      (fun h => by
        have h2 := (h.2 (e ⟨0, hn⟩)).2
        rw [hβ, if_pos (show ((⟨0, hn⟩ : Fin n) : ℕ) = 0 from rfl)] at h2
        split_ifs at h2 <;> norm_num at h2)
      (fun ⟨c, hc⟩ => by
        have h2 := hc.boundary_eq_zero (c.symm (e ⟨0, hn⟩))
        rw [Equiv.apply_symm_apply, hβ,
          if_pos (show ((⟨0, hn⟩ : Fin n) : ℕ) = 0 from rfl)] at h2
        split_ifs at h2 <;> norm_num at h2)
  have ha0 := (isLogDiscrepancyVector_iff_eq_zero_of_isChainOrder hrat hneg hn he hβ).1 ha
  exact (hapos (e ⟨0, hn⟩)).ne' (congrFun ha0 _)

/-- In the `n = 0` case, a log terminal germ of type (9) has exactly two boundary components. -/
private theorem card_support_eq_two {Y : Scheme.{u}} {f : Y ⟶ X} [QuasiCompact (f ≫ sX)]
    [IsLocallyNoetherian Y] [IsNormal Y] {E : Fin 0 → Mori.PrimeDivisor Y}
    (hB : IsSurfaceGermWithBoundary sX P B) (hred : IsReducedBoundary B)
    (hf : IsMinimalGermResolution sX P f) (hE : IsExceptionalCurveEnumeration f P E)
    (hK : K.IsCanonicalDivisor sX 2)
    (hlt : HoldsOnGerm {P} fun U : X.Opens => ∀ [Nonempty U],
      haveI : CompactSpace U := isCompact_iff_compactSpace.mp
        (@NoetherianSpace.isCompact _ _ (haveI : IsNoetherian X := {}; inferInstance) _)
      IsLogTerminal (U.ι ≫ sX) 2 (DivisorWithCoeffs.restrictOpen U K)
        (DivisorWithCoeffs.restrictOpen U (QDivisor.toRDivisor B)))
    (h9 : IsFig3Type9 sX P B) :
    B.support.card = 2 := by
  obtain ⟨-, Y', f', _, _, _, n', E', hf', -, hcase⟩ := id h9
  rcases hcase with ⟨-, -, m, hm, hsum, -⟩ | ⟨hn', pt, Γe, e, hext, he, -, -, h0, h1⟩
  · -- the `n = 0` branch: `∑ mult_P C = 2` over the components `C` of `B`
    have hm1 : ∀ C ∈ B.support, 1 ≤ m C := fun C hC => by
      have := MMP.Resolution.Kr1c.one_le_multAt_of_mem_support (hB.2.1 C hC)
      rw [hm C hC] at this
      exact_mod_cast this
    have hsumN : ∑ C ∈ B.support, m C = 2 := by
      have : ∑ C ∈ B.support, B C * (m C : ℚ) = ∑ C ∈ B.support, (m C : ℚ) :=
        Finset.sum_congr rfl fun C hC => by rw [hred C hC, one_mul]
      rw [this] at hsum
      exact_mod_cast hsum
    have hcard : B.support.card ≤ 2 := by
      calc B.support.card = ∑ _C ∈ B.support, 1 := by simp
        _ ≤ ∑ C ∈ B.support, m C := Finset.sum_le_sum hm1
        _ = 2 := hsumN
    have hcard0 : B.support.card ≠ 0 := fun h => by
      rw [Finset.card_eq_zero] at h
      rw [h, Finset.sum_empty] at hsumN
      exact absurd hsumN (by norm_num)
    have hcard1 : B.support.card ≠ 1 := fun h => by
      obtain ⟨C, hC⟩ := Finset.card_eq_one.1 h
      obtain ⟨Γ₀, hΓ₀⟩ := hf.1.exists_isWeightedDualGraph hB hE
      exact h9.not_isLogTerminal_near hred
        ⟨Γ₀, Y, f, inferInstance, inferInstance, inferInstance, E, hf, hΓ₀⟩ hC K hlt
    omega
  · -- a chain with two boundary ends has log discrepancy vector `0`, which is not positive
    exact (not_isLogTerminal_of_isChainOrder hf' hn' hext he h0 h1 hK hlt).elim

/-- A log terminal germ without boundary, whose minimal resolution has `n ≥ 1` exceptional curves,
is of type (1) or (2). -/
private theorem isFig3Type1_or_isFig3Type2_of_eq_zero {Y : Scheme.{u}} {f : Y ⟶ X}
    [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y] {n : ℕ}
    {E : Fin n → Mori.PrimeDivisor Y}
    (hB : IsSurfaceGermWithBoundary sX P B) (hB0 : B = 0)
    (hf : IsMinimalGermResolution sX P f) (hE : IsExceptionalCurveEnumeration f P E)
    (hn : 1 ≤ n) (hK : K.IsCanonicalDivisor sX 2)
    (hlt : HoldsOnGerm {P} fun U : X.Opens => ∀ [Nonempty U],
      haveI : CompactSpace U := isCompact_iff_compactSpace.mp
        (@NoetherianSpace.isCompact _ _ (haveI : IsNoetherian X := {}; inferInstance) _)
      IsLogTerminal (U.ι ≫ sX) 2 (DivisorWithCoeffs.restrictOpen U K)
        (DivisorWithCoeffs.restrictOpen U (QDivisor.toRDivisor B))) :
    IsFig3Type1 sX P B ∨ IsFig3Type2 sX P B := by
  classical
  obtain ⟨Γ, hΓ⟩ := hf.1.exists_isWeightedDualGraph hB hE
  have hneg := hΓ.isNegDef
  obtain ⟨a, ha, -⟩ := Γ.existsUnique_isLogDiscrepancyVector (det_pos hneg).ne'
  have hapos : ∀ j, 0 < a j :=
    ((hΓ.isGermLogDiscrepancyVector_iff a).2 ha).pos_of_isLogTerminal hf hK hlt
  have hβ0 : ∀ j, Γ.boundary j = 0 := fun j => by
    have hb := hΓ.boundary j
    rw [hB0, map_zero] at hb
    exact ((isIntersectionNumber_zero hb).unique hb).symm
  have hrat : Γ.IsRationalTree :=
    hf.isRationalTree_of_logDiscrepancy_nonneg hΓ ha (fun j => (hapos j).le)
      (by
        rintro ⟨rfl, h⟩
        have h0 := (isLogDiscrepancyVector_iff_eq_zero_of_genus_eq_one (h default).1 (h default).2
          (show 0 < Γ.weight default by
            simpa [WeightedGraph.matrix] using hneg.diag_pos (i := default)).ne').1 ha
        exact (hapos default).ne' (congrFun h0 default))
      (fun hc => (hapos ⟨0, hn⟩).ne' (congrFun
        ((isLogDiscrepancyVector_iff_eq_zero_of_isCircle hc (det_pos hneg).ne').1 ha) _))
  rcases ha.isWeightedChain_or_isStar_of_pos hrat hneg hβ0 hapos with hch | ⟨v, arms, hstar, hΔ⟩
  · exact .inl ⟨hB0, n, Γ, ⟨Y, f, inferInstance, inferInstance, inferInstance, E, hf, hΓ⟩, hch,
      hrat.two_le_weight⟩
  · exact .inr ⟨hB0, n, Γ, v, arms, ⟨Y, f, inferInstance, inferInstance, inferInstance, E, hf, hΓ⟩,
      hstar, hrat.two_le_weight, hΔ⟩

end Classification

/-- **Classification of log terminal surface germs** (FA Fig. 3 (1)–(3), 3.2.7, 3.3.1, and the
exception of 3.0.1). Let `(X, P; B)` be a surface germ with reduced boundary over an
algebraically closed field `k`, and let `f` be its minimal resolution, with exceptional curves
`E_1, …, E_n`. If `(X, B)` is log terminal near `P` (on some open neighbourhood `U` of `P`,
`(U, B|_U)` is log terminal with canonical divisor `K_X|_U`), then `(X, P; B)` is of type (1),
(2) or (3), or it is of type (9) with `n = 0` and `B` has exactly two components. -/
@[mmp "thm_fa3_lt_classification_only_if"]
public theorem IsMinimalGermResolution.isFig3Type1_or_isFig3Type2_or_isFig3Type3_of_isLogTerminal
    {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    {P : X} {B : QDivisor X} {f : Y ⟶ X} [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y]
    [IsNormal Y] {n : ℕ} {E : Fin n → Mori.PrimeDivisor Y}
    (hB : IsSurfaceGermWithBoundary sX P B) (hred : IsReducedBoundary B)
    (hf : IsMinimalGermResolution sX P f) (hE : IsExceptionalCurveEnumeration f P E)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 2)
    (hlt : HoldsOnGerm {P} fun U : X.Opens => ∀ [Nonempty U],
      haveI : CompactSpace U := isCompact_iff_compactSpace.mp
        (@NoetherianSpace.isCompact _ _ (haveI : IsNoetherian X := {}; inferInstance) _)
      IsLogTerminal (U.ι ≫ sX) 2 (DivisorWithCoeffs.restrictOpen U K)
        (DivisorWithCoeffs.restrictOpen U (QDivisor.toRDivisor B))) :
    IsFig3Type1 sX P B ∨ IsFig3Type2 sX P B ∨ IsFig3Type3 sX P B ∨
      (IsFig3Type9 sX P B ∧ n = 0 ∧ B.support.card = 2) := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rcases hf.isFig3Type1_or_isFig3Type3_or_isFig3Type9 hB hred hE hK
      (holdsOnGerm_isLogCanonical hlt) with h1 | h3 | h9
    · exact .inl h1
    · exact .inr (.inr (.inl h3))
    · exact .inr (.inr (.inr ⟨h9, rfl, card_support_eq_two hB hred hf hE hK hlt h9⟩))
  · by_cases hB0 : B = 0
    · rcases isFig3Type1_or_isFig3Type2_of_eq_zero hB hB0 hf hE hn hK hlt with h1 | h2
      · exact .inl h1
      · exact .inr (.inl h2)
    · exact .inr (.inr (.inl (hf.isFig3Type3_of_isLogTerminal hB hred hB0 hE hn hK hlt)))

end MMP.Flips
