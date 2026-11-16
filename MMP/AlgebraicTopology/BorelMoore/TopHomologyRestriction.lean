module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.BorelMooreVanishing
public import MMP.AlgebraicTopology.BorelMoore.RestrictionFunctorial
public import MMP.AlgebraicGeometry.SubschemeOver
/-!
# Top-dimensional Borel–Moore homology is detected off a small closed subset (Fulton, §19.1)

Let `X` be a complex scheme of dimension `n`, `Z ⊆ X` a Zariski closed subset with
`dim Z ≤ n - 1`, and `U = X - Z`. Then the restriction `H_{2n} X → H_{2n} U` is an isomorphism
(Fulton, Lemma 19.1.1, exact sequence (6)).

In the exact sequence `H_{2n} Z → H_{2n} X → H_{2n} U → H_{2n-1} Z`
(`lem_ext_c19_bm_long_exact_sequence`) both outer groups vanish, since `2n - 1 > 2 (n - 1)`
(`lem_c19_homology_vanishes_above_twice_dimension`).

The dimension hypothesis is written `dim Z < n`, which for `n = 0` says `Z = ∅`. The statement
holds for every closed subscheme `Z ⟶ X` over `ℂ` (no hypothesis on `dim X` is needed); the
Zariski closed subset form takes the reduced structure.

## Main results

* `MMP.IsComplexScheme.isIso_restrict_of_dimension_lt`: for a closed subscheme.
* `MMP.IsComplexScheme.isIso_restrict_compl_of_setDimension_lt`: for a Zariski
  closed subset.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], Lemma 19.1.1, (6).
-/

@[expose] public noncomputable section

open CategoryTheory Limits Topology AlgebraicGeometry TopologicalSpace
open scoped MMP.SubschemeOver

namespace MMP

open MMP.Intersection.Scheme

namespace IsComplexScheme

open UnderlyingSpace borelMooreHomology

/-- A closed subscheme over `ℂ` of a complex scheme is a complex scheme. -/
theorem of_isClosedImmersion {X Z : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X]
    [Z.Over (Spec (.of ℂ))] (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of ℂ))] :
    IsComplexScheme Z where
  toLocallyOfFiniteType := by
    rw [← comp_over (i) (Spec (.of ℂ))]
    infer_instance
  toQuasiCompact := by
    rw [← comp_over (i) (Spec (.of ℂ))]
    infer_instance
  exists_isClosedImmersion := by
    obtain ⟨W, _, _, j, hj, _⟩ := IsComplexScheme.exists_isClosedImmersion (X := X)
    exact ⟨W, inferInstance, inferInstance, i ≫ j, inferInstance, inferInstance⟩

/-- A complex scheme of dimension `< n` has vanishing Borel–Moore homology in every degree
`j ≥ 2n - 1`. -/
theorem isZero_borelMooreHomology_of_dimension_lt (R : Type) [CommRing R] (Z : Scheme.{0})
    [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z] {n : ℕ} (hZ : dimension Z < n) {j : ℤ}
    (hj : 2 * (n : ℤ) - 1 ≤ j) :
    IsZero (IsComplexScheme.borelMooreHomology R (ModuleCat.of R R) Z j) := by
  cases n with
  | zero =>
    haveI : IsEmpty (UnderlyingSpace ℂ Z) := ⟨fun p ↦ by
      haveI : Nonempty (IrreducibleCloseds Z) :=
        ⟨⟨closure {p.toHom (IsLocalRing.closedPoint ℂ)}, isIrreducible_singleton.closure,
          isClosed_closure⟩⟩
      have h0 : (0 : WithBot ℕ∞) ≤ dimension Z := Order.krullDim_nonneg
      have := h0.trans_lt hZ
      simp at this⟩
    exact isZero_borelMooreHomology_of_isEmpty R (ModuleCat.of R R) _ j
  | succ m =>
    have hle : dimension Z ≤ (m : WithBot ℕ∞) := by
      generalize dimension Z = x at hZ
      induction x with
      | bot => exact bot_le
      | coe y =>
        have : y < ((m + 1 : ℕ) : ℕ∞) := by exact_mod_cast hZ
        have : y ≤ (m : ℕ∞) := Order.le_of_lt_succ (by simpa using this)
        exact_mod_cast this
    exact isZero_borelMooreHomology_of_dimension_le Z R hle (by push_cast at hj; lia)

/-- **Restriction to the complement of a small closed subscheme is an isomorphism in degree
`2n`** (Fulton, Lemma 19.1.1, (6)). Let `X` be a complex scheme, `i : Z → X` a closed subscheme
over `ℂ` with `dim Z < n`, and `U = X(ℂ) - i(Z(ℂ))`. Then the restriction
`H_{2n} X → H_{2n} U` is an isomorphism. -/
theorem isIso_restrict_of_dimension_lt (R : Type) [CommRing R] (X : Scheme.{0})
    [X.Over (Spec (.of ℂ))] [IsComplexScheme X] {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of ℂ))] {n : ℕ}
    (hZ : dimension Z < n) :
    IsIso (restrict R (ModuleCat.of R R) (complOpens (Y := TopCat.of (UnderlyingSpace ℂ X))
      (isClosed_range_map_of_isClosedImmersion i)) (2 * n)) := by
  haveI := of_isClosedImmersion i
  obtain ⟨δ, -, h2, h3⟩ := exists_borelMooreHomology_longExact R (ModuleCat.of R R) X i
  obtain ⟨k, hk⟩ : ∃ k : ℤ, 2 * (n : ℤ) = k + 1 := ⟨2 * n - 1, by lia⟩
  have hZ₁ := isZero_borelMooreHomology_of_dimension_lt R Z hZ (j := k + 1) (by lia)
  have hZ₀ := isZero_borelMooreHomology_of_dimension_lt R Z hZ (j := k) (by lia)
  rw [ModuleCat.isZero_iff_subsingleton] at hZ₁ hZ₀
  rw [hk]
  refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨?_, fun y ↦ ?_⟩
  · rw [← LinearMap.ker_eq_bot (f := (restrict R (ModuleCat.of R R) _ (k + 1)).hom),
      LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨a, rfl⟩ := (h2 (k + 1) x).mp hx
    rw [Subsingleton.elim a 0, map_zero]
  · exact (h3 k y).mp (Subsingleton.elim _ _)

/-- **Restriction to the complement of a small Zariski closed subset is an isomorphism in degree
`2n`** (Fulton, Lemma 19.1.1, (6)). Let `X` be a complex scheme, `Z ⊆ X` a Zariski closed subset
with `dim Z < n` (i.e. `dim Z ≤ n - 1`), and `U = X - Z`: the points of `X(ℂ)` whose closed point
lies off `Z`. Then the restriction `H_{2n} X → H_{2n} U` is an isomorphism. -/
theorem isIso_restrict_compl_of_setDimension_lt (R : Type) [CommRing R] (X : Scheme.{0})
    [X.Over (Spec (.of ℂ))] [IsComplexScheme X] (Z : Closeds X) {n : ℕ}
    (hZ : topologicalKrullDim (Z : Set X) < n) :
    IsIso (restrict R (ModuleCat.of R R) (complOpens (Y := TopCat.of (UnderlyingSpace ℂ X))
      (isClosed_range_map_of_isClosedImmersion
        (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι)) (2 * n)) := by
  refine isIso_restrict_of_dimension_lt R X _ (lt_of_le_of_lt ?_ hZ)
  set I := Scheme.IdealSheafData.vanishingIdeal Z
  have hmem : ∀ z, I.subschemeι.base z ∈ (Z : Set X) := fun z ↦ by
    have : I.subschemeι.base z ∈ Set.range I.subschemeι.base := Set.mem_range_self z
    rwa [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
  exact (I.subschemeι.isClosedEmbedding.isInducing.codRestrict hmem).topologicalKrullDim_le

end IsComplexScheme

end MMP
