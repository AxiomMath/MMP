module

public import MMP.AlgebraicGeometry.CycleMap.TopClassComponentBasis
public import MMP.AlgebraicGeometry.SubschemeOver
public import MMP.AlgebraicGeometry.Dimension.PureDimensional
/-!
# Top-dimensional classes are detected locally (Fulton, §19.1)

Let `D` be a complex scheme of pure dimension `m` with irreducible components `Z_1, …, Z_r`, and
for each `j` let `W_j ⊆ D(ℂ)` be a non-empty open subset (classical topology) contained in the
regular part of `Z_j` and meeting no other component. A class `c ∈ H_{2m} D` restricting to `0`
on every `W_j` is zero. Indeed `H_{2m} D` is free on the cycle classes `cl_D(Z_i)`
(`MMP.linearIndependent_and_span_eq_top_of_isCycleClassOf`), so
`c = ∑ a_i cl_D(Z_i)`; for `i ≠ j` the class `cl_D(Z_i)` restricts to `0` on `W_j`, which misses
`Z_i`, while `cl_D(Z_j)|_{W_j}` is, up to push-forward along homeomorphisms, a fundamental class
of the non-empty complex manifold `W_j`, which has no torsion. Hence `a_j = 0` for all `j`.

## Main results

* `MMP.eq_zero_of_forall_restrict_eq_zero`: the statement, for `D` of pure
  dimension `m`.
* `MMP.eq_zero_of_forall_restrict_eq_zero_of_dimension_le`: the same for `D` of
  dimension `≤ m`.
* `MMP.IsPureDimensional.dimension_le`: a scheme of pure dimension `m` has
  dimension `≤ m`.

## Implementation notes

The regular part `(Z_j)_reg` is read in `D(ℂ)` as the image of the regular `ℂ`-points of the
reduced component `Z_j` under the closed embedding `Z_j(ℂ) → D(ℂ)`, and `Z_i(ℂ) ⊆ D(ℂ)` as the
range of that embedding. Of the pure-dimensionality only `dim D ≤ m` is used: components of
smaller dimension contribute nothing to `H_{2m} D`. The coefficients are an arbitrary commutative
ring `R`; Fulton's are `ℤ`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, proof of Lemma 19.1.3.
-/

@[expose] public noncomputable section

open AlgebraicGeometry TopologicalSpace
open MMP.UnderlyingSpace
open scoped MMP.SubschemeOver

universe u

namespace MMP

open MMP.Intersection.Scheme (dimension)

/-- A pure-dimensional scheme of dimension `k` has dimension at most `k`. -/
theorem IsPureDimensional.dimension_le {X : Scheme.{u}} {k : ℕ} (hX : IsPureDimensional X k) :
    dimension X ≤ k := by
  by_cases hne : Nonempty X
  · obtain ⟨m, hm, hd⟩ := hX.hasDim_of_nonempty
    have : m = k := by exact_mod_cast hm
    rw [dimension, hd, this]
  · rw [not_nonempty_iff] at hne
    have : IsEmpty (IrreducibleCloseds X) :=
      ⟨fun C ↦ hne.elim C.isIrreducible.nonempty.some⟩
    rw [dimension, topologicalKrullDim, Order.krullDim_eq_bot]
    exact bot_le

variable {D : Scheme.{0}} [D.Over (Spec (.of ℂ))] [IsComplexScheme D]

/-- A class `c ∈ H_{2m} D` of a complex scheme of dimension `≤ m` vanishes as soon as it
restricts to `0` on non-empty open sets `W_j ⊆ (Z_j)_reg(ℂ)` meeting no other component, one
for each irreducible component `Z_j`. -/
theorem eq_zero_of_forall_restrict_eq_zero_of_dimension_le (R : Type) [CommRing R] {m : ℕ}
    (hD : dimension D ≤ m) (W : irreducibleComponents D → Opens (UnderlyingSpace ℂ D))
    (hne : ∀ j, (W j : Set (UnderlyingSpace ℂ D)).Nonempty)
    (hreg : ∀ j, (W j : Set (UnderlyingSpace ℂ D)) ⊆
      mapFun (K := ℂ) (irreducibleComponentι D j) '' regularPart ℂ (irreducibleComponentScheme D j))
    (hdisj : ∀ i j, i ≠ j → Disjoint (W j : Set (UnderlyingSpace ℂ D))
      (Set.range (mapFun (K := ℂ) (irreducibleComponentι D i))))
    (c : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ D)) (2 * m : ℕ))
    (hc : ∀ j, borelMooreHomology.restrict R (ModuleCat.of R R)
      (Y := TopCat.of (UnderlyingSpace ℂ D)) (W j) (2 * m : ℕ) c = 0) :
    c = 0 := by
  classical
  have := (finite_irreducibleComponents_of_isAlgebraicScheme ℂ D).to_subtype
  let : Fintype (irreducibleComponents D) := Fintype.ofFinite _
  obtain ⟨b, hb⟩ := exists_basis_isCycleClassOf R hD
  choose a ha hab using hb
  refine b.ext_elem fun Z ↦ ?_
  rw [map_zero, Finsupp.zero_apply]
  obtain ⟨j, hj⟩ := Z
  have hsum := congrArg (borelMooreHomology.restrict R (ModuleCat.of R R)
    (Y := TopCat.of (UnderlyingSpace ℂ D)) (W j) (2 * m : ℕ)).hom (b.sum_repr c)
  rw [hc j, map_sum, Finset.sum_eq_single ⟨j, hj⟩ (fun Z _ hZ ↦ ?_)
    (fun h ↦ absurd (Finset.mem_univ _) h), map_smul, ← hab ⟨j, hj⟩] at hsum
  · exact eq_zero_of_smul_restrict_pushforward_eq_zero R _ (ha ⟨j, hj⟩) (W j) (hreg j) (hne j)
      (r := b.repr c ⟨j, hj⟩) hsum
  · rw [map_smul, ← hab Z, restrict_pushforward_map_eq_zero_of_disjoint R _ _ (W j)
      (hdisj Z.1 j fun h ↦ hZ (Subtype.ext h)), smul_zero]

/-- **A top-dimensional class is detected on open subsets of the components** (Fulton, proof of
Lemma 19.1.3). Let `D` be a complex scheme of pure dimension `m` with irreducible components
`Z_j`, and for each `j` let `W_j ⊆ D(ℂ)` be a non-empty open subset (classical topology) lying in
the regular part `(Z_j)_reg(ℂ)` (read in `D(ℂ)` through the closed embedding `Z_j(ℂ) → D(ℂ)`)
and meeting no other component `Z_i(ℂ)`, `i ≠ j`. If `c ∈ H_{2m} D` restricts to `0` on every
`W_j`, then `c = 0`. -/
theorem eq_zero_of_forall_restrict_eq_zero (R : Type) [CommRing R] {m : ℕ}
    (hD : IsPureDimensional D m) (W : irreducibleComponents D → Opens (UnderlyingSpace ℂ D))
    (hne : ∀ j, (W j : Set (UnderlyingSpace ℂ D)).Nonempty)
    (hreg : ∀ j, (W j : Set (UnderlyingSpace ℂ D)) ⊆
      mapFun (K := ℂ) (irreducibleComponentι D j) '' regularPart ℂ (irreducibleComponentScheme D j))
    (hdisj : ∀ i j, i ≠ j → Disjoint (W j : Set (UnderlyingSpace ℂ D))
      (Set.range (mapFun (K := ℂ) (irreducibleComponentι D i))))
    (c : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ D)) (2 * m : ℕ))
    (hc : ∀ j, borelMooreHomology.restrict R (ModuleCat.of R R)
      (Y := TopCat.of (UnderlyingSpace ℂ D)) (W j) (2 * m : ℕ) c = 0) :
    c = 0 :=
  eq_zero_of_forall_restrict_eq_zero_of_dimension_le R hD.dimension_le W hne hreg hdisj c hc

end MMP
