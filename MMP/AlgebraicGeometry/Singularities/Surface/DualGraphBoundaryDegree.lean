module

public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.NormalThreefoldSlice

/-!
# Boundary degrees of the dual graph as sums over boundary points

Let `(X, P; B)` be a surface germ with reduced boundary and `g : Y ⟶ X` a resolution of
`(X, P)` with exceptional curves `E_1, …, E_n`. The boundary degree `β_j = (g⁻¹_* B · E_j)` of
the vertex `v_j` of the weighted dual graph `Γ(g)` is the sum of the local intersection numbers
`(C · E_j)_y` over the boundary points `(C, y)` of `g` with `y ∈ E_j`, and each of these local
intersection numbers is at least `1`. In terms of the extended dual graph `Γ^*(g)`: `β_j` is the
sum of the weights of the edges joining `v_j` to the `•`-vertices, and every such edge has
weight at least `1`.

## Main results

* `MMP.Flips.IsExtendedDualGraph.boundary_eq_sum_boundaryEdgeWeight`: `β_j` is the sum of the
  edge weights `(C_l · E_j)_{y_l}` over the boundary points `(C_l, y_l)` with `y_l ∈ E_j`, each
  of which is `≥ 1`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], (3.1.10),
  (3.1.14)
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace MMP.Flips

open MMP.Mori

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
    · simp [show Q' ≠ Q from fun h' => h E (h' ▸ hφ)]

/-- The coefficient of `g⁻¹_*(D)` in `g⁻¹_* B` is that of `D` in `B`: the inverse transform of
prime divisors is injective, as `g` sends the generic point of `g⁻¹_*(D)` to that of `D`. -/
private theorem inverseTransformDivisor_apply_of_eq_some {X Y : Scheme.{u}} {R : Type*}
    [AddCommMonoid R] {g : Y ⟶ X} {D : Mori.PrimeDivisor X} {C : Mori.PrimeDivisor Y}
    (hD : inverseTransformPrimeDivisor g D = some C) (B : DivisorWithCoeffs R X) :
    inverseTransformDivisor g B C = B D :=
  MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hD (fun _ hD' =>
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective <|
      (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
        hD').1.symm.trans
      (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hD).1) B

/-- A component of the birational transform `g⁻¹_* B` does not lie over the closed point `P` of a
surface germ: its generic point maps into the biregular locus, so to a point of coheight `1`,
while `P` has coheight `2`. -/
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

/-- The local intersection number is symmetric. -/
private theorem localIntersectionNumber_comm {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) (q : Y) (C C' : Divisor Y) :
    localIntersectionNumber sY q C C' = localIntersectionNumber sY q C' C := by
  rw [localIntersectionNumber, localIntersectionNumber, sup_comm]

/-- If every coefficient of `B` is `1`, then `g⁻¹_* B` is the sum of its components. -/
private theorem inverseTransformDivisor_eq_sum_single {X Y : Scheme.{u}} {g : Y ⟶ X}
    {B : QDivisor X} (hB : ∀ D ∈ B.support, B D = 1) :
    inverseTransformDivisor g B =
      ∑ C ∈ (inverseTransformDivisor g B).support, Finsupp.single C (1 : ℚ) := by
  conv_lhs => rw [← Finsupp.sum_single (inverseTransformDivisor g B)]
  refine Finset.sum_congr rfl fun C hC => ?_
  obtain ⟨D, hD⟩ := exists_eq_some_of_mem_support_mapPrimeDivisors hC
  rw [Finsupp.mem_support_iff, inverseTransformDivisor_apply_of_eq_some hD] at hC
  rw [inverseTransformDivisor_apply_of_eq_some hD, hB D (Finsupp.mem_support_iff.mpr hC)]

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {P : X} {B : QDivisor X} {g : Y ⟶ X} [QuasiCompact (g ≫ sX)] [IsLocallyNoetherian Y]
  [IsNormal Y] {n m : ℕ} {E : Fin n → Mori.PrimeDivisor Y}
  {pt : Fin m → Mori.PrimeDivisor Y × Y} {Γ : ExtendedWeightedGraph (Fin n) (Fin m)}

open Classical in
/-- The boundary points of `g` on `E_j` are the pairs `(C, y)` with `C` a component of
`g⁻¹_* B` and `y ∈ E_j ∩ C`. -/
private theorem mem_image_pt_iff (h : IsExtendedDualGraph sX P B g E pt Γ) (j : Fin n)
    {F : Mori.PrimeDivisor Y → Finset Y}
    (hF : ∀ C ∈ (inverseTransformDivisor g B).support,
      ∀ y, y ∈ F C ↔ y ∈ (E j).support ∩ C.support) (p : Mori.PrimeDivisor Y × Y) :
    p ∈ ({l | (pt l).2 ∈ (E j).support} : Finset (Fin m)).image pt ↔
      p.1 ∈ (inverseTransformDivisor g B).support ∧ p.2 ∈ F p.1 := by
  have hover : ∀ y ∈ (E j).support, g.base y = P := fun y hy =>
    (h.isWeightedDualGraph.isExceptionalCurveEnumeration.isGermExceptionalCurve j).1.prop.2 hy
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨hC, hy, -⟩ := h.isGermBoundaryPoint l
    have hC' : (pt l).1 ∈ (inverseTransformDivisor g B).support := Finsupp.mem_support_iff.mpr hC
    exact ⟨hC', (hF _ hC' _).mpr ⟨hl, hy⟩⟩
  · rintro ⟨hC, hy⟩
    rw [hF _ hC] at hy
    obtain ⟨l, hl⟩ := h.exists_eq p.1 p.2 ⟨Finsupp.mem_support_iff.mp hC, hy.2, hover _ hy.1⟩
    exact ⟨l, hl ▸ hy.1, hl⟩

open Classical in
/-- For a resolution `g` of a surface germ `(X, P; B)` with reduced boundary and extended dual
graph `Γ^*(g) = Γ`, the boundary degree `β_j = (g⁻¹_* B · E_j)` is the sum of the edge weights
`(C_l · E_j)_{y_l}` over the boundary points `(C_l, y_l)` with `y_l ∈ E_j`, and each of these
weights is at least `1` (FA 3.1.10). -/
@[mmp "lem_fa3_boundary_degree_points"]
public theorem IsExtendedDualGraph.boundary_eq_sum_boundaryEdgeWeight
    (h : IsExtendedDualGraph sX P B g E pt Γ) (j : Fin n) :
    Γ.toWeightedGraph.boundary j =
        ∑ l with (pt l).2 ∈ (E j).support, (Γ.boundaryEdgeWeight j l : ℚ) ∧
      ∀ l, (pt l).2 ∈ (E j).support → 1 ≤ Γ.boundaryEdgeWeight j l := by
  have hW := h.isWeightedDualGraph
  have hres := hW.isGermResolution
  have hEj := hW.isExceptionalCurveEnumeration.isGermExceptionalCurve j
  have hBt_eq := inverseTransformDivisor_eq_sum_single (g := g) fun D hD =>
    h.isReducedBoundary D hD
  set Bt : QDivisor Y := inverseTransformDivisor g B
  have hover : ∀ y ∈ (E j).support, g.base y = P := fun y hy => hEj.1.prop.2 hy
  have hne : ∀ C ∈ Bt.support, E j ≠ C := fun C hC hCE =>
    map_genericPoint_ne_of_mem_support hres.isSurfaceGerm hC <| hover _ <| by
      rw [hCE, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
  have hloc := fun C (hC : C ∈ Bt.support) =>
    isIntersectionNumber_finsum_localIntersectionNumber_of_ne (g ≫ sX) hres.isVariety
      hres.isSmoothResolution.isSmoothScheme hres.topologicalKrullDim_eq (hne C hC)
      (IsGermExceptionalCurve.isProper sX hres hEj).2
  let F : Mori.PrimeDivisor Y → Finset Y := fun C =>
    if hC : C ∈ Bt.support then (hloc C hC).1.toFinset else ∅
  have hF : ∀ C (hC : C ∈ Bt.support), F C = (hloc C hC).1.toFinset := fun C hC => by
    simp only [F, dif_pos hC]
  let f : Mori.PrimeDivisor Y × Y → ℚ := fun p =>
    (localIntersectionNumber (g ≫ sX) p.2 (Finsupp.single (E j) 1) (Finsupp.single p.1 1) : ℚ)
  have hw : ∀ l, (pt l).2 ∈ (E j).support → Γ.boundaryEdgeWeight j l =
      localIntersectionNumber (g ≫ sX) (pt l).2 (Finsupp.single (E j) 1)
        (Finsupp.single (pt l).1 1) := fun l hl => by
    rw [h.boundaryEdgeWeight_eq, if_pos hl, localIntersectionNumber_comm]
  have hsum : IsIntersectionNumber (g ≫ sX) Bt (E j).idealSheaf
      (∑ C ∈ Bt.support, ∑ y ∈ F C, f (C, y)) := by
    have := isIntersectionNumber_sum Bt.support (D := fun C => Finsupp.single C (1 : ℚ))
      (C := (E j).idealSheaf) (x := fun C => ∑ y ∈ F C, f (C, y))
      (isIntersectionNumber_zero (hW.boundary j)) (fun C hC => by
        rw [hF C hC, ← finsum_mem_eq_finite_toFinset_sum]
        exact (hloc C hC).2.1)
    rwa [← hBt_eq] at this
  refine ⟨?_, fun l hl => ?_⟩
  · rw [(hW.boundary j).unique hsum, ← Finset.sum_finset_product _ _ _
        (mem_image_pt_iff h j fun C hC _ => by rw [hF C hC, Set.Finite.mem_toFinset]),
      Finset.sum_image fun a _ b _ hab => h.injective hab]
    exact Finset.sum_congr rfl fun l hl => by rw [hw l (Finset.mem_filter.mp hl).2]
  · obtain ⟨hC, hy, -⟩ := h.isGermBoundaryPoint l
    rw [hw l hl]
    exact (hloc _ (Finsupp.mem_support_iff.mpr hC)).2.2 _ ⟨hl, hy⟩

end MMP.Flips
