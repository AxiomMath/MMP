module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.BorelMooreLongExact
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.SingularStratumComplement
public import MMP.AlgebraicTopology.FundamentalClass.ComplexOrientation
public import MMP.AlgebraicTopology.PoincareDuality.Vanishing
public import MMP.AlgebraicGeometry.SubschemeOver

/-!
# Borel–Moore homology vanishes above twice the dimension

If `X` is a complex scheme of dimension at most `n`, then `H_i X = 0` for `i > 2n` (Fulton,
Lemma 19.1.1).

The proof is by induction on `n`. The singular stratum `S = S_X`, with its reduced structure, is
a closed complex subscheme of dimension `< n` (`topologicalKrullDim_singularStratum_lt`), and
`X(ℂ) - S(ℂ)` is the disjoint union of the open sets `Uⱼ(ℂ)`, each homeomorphic to an open subset
of the complex manifold `(Xⱼ)_reg(ℂ)` of complex dimension `dim Xⱼ ≤ n`
(`singularStratumComplement_isManifold_isConnected`). So `H_i U = 0` for `i > 2n`
(`borelMooreHomology.isZero_of_dim_lt`, `borelMooreHomology.isZero_of_isZero_disjoint_cover`),
`H_i S = 0` by induction, and the exact sequence `H_i S → H_i X → H_i U`
(`exists_borelMooreHomology_longExact`) gives `H_i X = 0`.

## Main definitions

* `MMP.IsComplexScheme.singularStratumScheme`: the singular stratum of a complex scheme with its
  reduced structure.

## Main results

* `MMP.IsComplexScheme.isZero_borelMooreHomology_of_dimension_le`: a complex scheme of dimension
  at most `n` has vanishing Borel–Moore homology in degrees `i > 2n`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], Lemma 19.1.1.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Topology AlgebraicGeometry TopologicalSpace
open scoped MMP.SubschemeOver Manifold

namespace MMP

open MMP.Intersection.Scheme

namespace borelMooreHomology

universe u

variable (R : Type u) [CommRing R]

/-- A Hausdorff, second countable space homeomorphic to a charted space modelled on a real
vector space with a basis of `m` vectors has vanishing Borel–Moore homology above degree `m`. -/
theorem isZero_of_homeomorph_chartedSpace {H : Type*} [AddCommGroup H] [Module ℝ H]
    [TopologicalSpace H] [ContinuousAdd H] [ContinuousSMul ℝ H] [T2Space H]
    {Y : Type u} {Y' : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [TopologicalSpace Y'] [ChartedSpace H Y'] (e : Y ≃ₜ Y') {m : ℕ}
    (b : Module.Basis (Fin m) ℝ H) {i : ℤ} (hi : (m : ℤ) < i) :
    IsZero (borelMooreHomology R (ModuleCat.of R R) (TopCat.of Y) i) := by
  letI : ChartedSpace Y' Y :=
    e.toOpenPartialHomeomorph.singletonChartedSpace e.toOpenPartialHomeomorph_source
  letI : ChartedSpace H Y := ChartedSpace.comp H Y' Y
  exact isZero_of_dim_lt R b hi

/-- The Borel–Moore homology of an empty space vanishes in positive degrees. -/
theorem isZero_of_isEmpty {Y : Type u} [TopologicalSpace Y] [IsEmpty Y] {i : ℤ} (hi : 0 < i) :
    IsZero (borelMooreHomology R (ModuleCat.of R R) (TopCat.of Y) i) :=
  letI := ChartedSpace.empty (Fin 0 → ℝ) Y
  isZero_of_dim_lt R (Pi.basisFun ℝ (Fin 0)) (by simpa using hi)

end borelMooreHomology

namespace IsComplexScheme

open UnderlyingSpace

variable (X : Scheme.{0}) [X.Over (Spec (.of ℂ))] [IsComplexScheme X]

/-- The singular stratum `S_X` of a complex scheme with its reduced structure. -/
abbrev singularStratumScheme : Scheme.{0} :=
  (Scheme.IdealSheafData.vanishingIdeal (singularStratumCloseds ℂ X)).subscheme

/-- The inclusion of the reduced singular stratum `S_X ⟶ X`. -/
abbrev singularStratumι : singularStratumScheme X ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal (singularStratumCloseds ℂ X)).subschemeι

/-- The reduced singular stratum of a complex scheme is a complex scheme. -/
instance isComplexScheme_singularStratumScheme : IsComplexScheme (singularStratumScheme X) where
  toLocallyOfFiniteType := by
    rw [← comp_over (singularStratumι X) (Spec (.of ℂ))]
    infer_instance
  toQuasiCompact := by
    rw [← comp_over (singularStratumι X) (Spec (.of ℂ))]
    infer_instance
  exists_isClosedImmersion := by
    obtain ⟨W, _, _, j, hj, _⟩ := IsComplexScheme.exists_isClosedImmersion (X := X)
    exact ⟨W, inferInstance, inferInstance, singularStratumι X ≫ j, inferInstance, inferInstance⟩

/-- The image of the inclusion `S_X ⟶ X` of the reduced singular stratum is `singularStratum X`. -/
lemma range_singularStratumι : Set.range (singularStratumι X).base = singularStratum X := by
  rw [Scheme.IdealSheafData.range_subschemeι]
  rfl

/-- The dimension of the reduced singular stratum `S_X` is at most the Krull dimension of the
singular stratum of `X` as a subspace of `X`. -/
lemma dimension_singularStratumScheme_le :
    dimension (singularStratumScheme X) ≤ topologicalKrullDim (singularStratum X) :=
  ((singularStratumι X).isClosedEmbedding.isInducing.codRestrict fun z ↦
    range_singularStratumι X ▸ Set.mem_range_self z).topologicalKrullDim_le

/-- A `ℂ`-point of `X` lies off `S_X(ℂ)` iff its closed point lies off the singular stratum. -/
lemma notMem_range_map_singularStratumι_iff (p : UnderlyingSpace ℂ X) :
    p ∉ Set.range (map (K := ℂ) (singularStratumι X)) ↔
      p.toHom (IsLocalRing.closedPoint ℂ) ∉ singularStratum X := by
  change p ∉ Set.range (mapFun (K := ℂ) (singularStratumι X)) ↔ _
  rw [range_mapFun_of_isClosedImmersion]
  change ¬ (_ ∈ Set.range (singularStratumι X).base) ↔ _
  rw [range_singularStratumι]

/-- **The complement of the singular stratum has no Borel–Moore homology above twice the
dimension** (Fulton, proof of Lemma 19.1.1): if `dim X ≤ n` and `i > 2n`, then
`H_i (X(ℂ) - S_X(ℂ)) = 0`. -/
theorem isZero_borelMooreHomology_compl_singularStratum (R : Type) [CommRing R] {n : ℕ}
    (hn : dimension X ≤ n) {i : ℤ} (hi : 2 * (n : ℤ) < i) :
    IsZero (MMP.borelMooreHomology R (ModuleCat.of R R)
      (TopCat.of (borelMooreHomology.complOpens (Y := TopCat.of (UnderlyingSpace ℂ X))
        (isClosed_range_map_of_isClosedImmersion (singularStratumι X)))) i) := by
  classical
  set Y : TopCat := TopCat.of (UnderlyingSpace ℂ X)
  set U := borelMooreHomology.complOpens (Y := Y)
    (isClosed_range_map_of_isClosedImmersion (singularStratumι X))
  haveI := (finite_irreducibleComponents_of_isAlgebraicScheme ℂ X).to_subtype
  letI : Fintype (irreducibleComponents X) := Fintype.ofFinite _
  let P : irreducibleComponents X → Set (UnderlyingSpace ℂ X) := fun Z ↦
    {p | p.toHom (IsLocalRing.closedPoint ℂ) ∈ singularStratumComplement X Z}
  let W : irreducibleComponents X → Opens (TopCat.of U) := fun Z ↦
    ⟨Subtype.val ⁻¹' P Z, (isOpen_preimage_of_isOpen
      (isOpen_singularStratumComplement ℂ X Z)).preimage continuous_subtype_val⟩
  refine borelMooreHomology.isZero_of_isZero_disjoint_cover R (ModuleCat.of R R) W
    (fun Z Z' h ↦ Set.disjoint_left.mpr fun p h1 h2 ↦
      Set.disjoint_left.mp (pairwise_disjoint_singularStratumComplement h) h1 h2) (fun p ↦ ?_) ?_
  · have h := (notMem_range_map_singularStratumι_iff X p.1).mp p.2
    rw [← Set.mem_compl_iff, singularStratum_compl_eq_iUnion, Set.mem_iUnion] at h
    exact h
  · intro Z
    obtain ⟨k, hk⟩ := ((singularStratumComplement_isManifold_isConnected X).2.2 Z).2.2.2.2.1
    letI := regularChartedSpace (𝕜 := ℂ) hk
    have hf₁ : IsEmbedding fun w : W Z ↦ (w.1.1 : UnderlyingSpace ℂ X) :=
      IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
    have hf₂ : IsEmbedding fun q : singularStratumComplementOpens X Z ↦
        map (K := ℂ) (irreducibleComponentι X Z) q.1.1 :=
      (isClosedEmbedding_map_of_isClosedImmersion (irreducibleComponentι X Z)).isEmbedding.comp
        (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal)
    have hr₁ : Set.range (fun w : W Z ↦ (w.1.1 : UnderlyingSpace ℂ X)) = P Z := by
      ext p
      refine ⟨fun ⟨w, hw⟩ ↦ hw ▸ w.2, fun hp ↦ ⟨⟨⟨p, ?_⟩, hp⟩, rfl⟩⟩
      exact (notMem_range_map_singularStratumι_iff X p).mpr
        (Set.disjoint_left.mp (disjoint_singularStratumComplement Z) hp)
    have hr₂ : Set.range (fun q : singularStratumComplementOpens X Z ↦
        map (K := ℂ) (irreducibleComponentι X Z) q.1.1) = P Z := by
      change _ = {p : UnderlyingSpace ℂ X | p.toHom (IsLocalRing.closedPoint ℂ) ∈
        singularStratumComplement X Z}
      rw [← image_mapFun_singularStratumComplementPoints (K := ℂ) X Z,
        ← image_val_singularStratumComplementOpens X Z, Set.image_image]
      ext p
      exact ⟨fun ⟨q, hq⟩ ↦ ⟨q.1, q.2, hq⟩, fun ⟨q, hq, h⟩ ↦ ⟨⟨q, hq⟩, h⟩⟩
    let e : W Z ≃ₜ singularStratumComplementOpens X Z :=
      hf₁.toHomeomorph.trans ((Homeomorph.setCongr (hr₁.trans hr₂.symm)).trans
        hf₂.toHomeomorph.symm)
    have hkn : k ≤ n := by
      exact_mod_cast (show ((k : ℕ∞) : WithBot ℕ∞) = dimension (irreducibleComponentScheme X Z)
        from hk).le.trans
          ((irreducibleComponentι X Z).isClosedEmbedding.isInducing.topologicalKrullDim_le.trans hn)
    have hfin : Module.finrank ℝ (EuclideanSpace ℂ (Fin k)) = 2 * k := by
      rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
    exact borelMooreHomology.isZero_of_homeomorph_chartedSpace R e
      (Module.finBasisOfFinrankEq ℝ _ hfin) (by push_cast; lia)

/-- The induction step of Fulton's Lemma 19.1.1: if `dim X ≤ n`, `i > 2n` and the reduced
singular stratum has `H_i S_X = 0`, then `H_i X = 0`. -/
theorem isZero_borelMooreHomology_of_isZero_singularStratumScheme (R : Type) [CommRing R]
    {n : ℕ} (hn : dimension X ≤ n) {i : ℤ} (hi : 2 * (n : ℤ) < i)
    (hS : IsZero (IsComplexScheme.borelMooreHomology R (ModuleCat.of R R)
      (singularStratumScheme X) i)) :
    IsZero (IsComplexScheme.borelMooreHomology R (ModuleCat.of R R) X i) := by
  obtain ⟨-, -, h2, -⟩ :=
    exists_borelMooreHomology_longExact R (ModuleCat.of R R) X (singularStratumι X)
  have hU := isZero_borelMooreHomology_compl_singularStratum X R hn hi
  rw [ModuleCat.isZero_iff_subsingleton] at hS hU ⊢
  have hx : ∀ x : IsComplexScheme.borelMooreHomology R (ModuleCat.of R R) X i, x = 0 := by
    intro x
    obtain ⟨a, rfl⟩ := (h2 i x).mp (Subsingleton.elim _ _)
    rw [Subsingleton.elim a 0, map_zero]
  exact subsingleton_of_forall_eq 0 hx

/-- **Borel–Moore homology vanishes above twice the dimension** (Fulton, Lemma 19.1.1): if `X`
is a complex scheme of dimension at most `n`, then `H_i X = 0` for `i > 2n`. Fulton states it for
`X` of dimension `n` with integer coefficients; here `dim X ≤ n` and the coefficients are any
commutative ring `R`. -/
theorem isZero_borelMooreHomology_of_dimension_le (R : Type) [CommRing R] {n : ℕ}
    (hn : dimension X ≤ n) {i : ℤ} (hi : 2 * (n : ℤ) < i) :
    IsZero (IsComplexScheme.borelMooreHomology R (ModuleCat.of R R) X i) := by
  induction n generalizing X with
  | zero =>
    refine isZero_borelMooreHomology_of_isZero_singularStratumScheme X R hn hi ?_
    haveI : IsEmpty (UnderlyingSpace ℂ (singularStratumScheme X)) := ⟨fun p ↦ by
      have hlt := topologicalKrullDim_singularStratum_lt ℂ X hn
      haveI : Nonempty (IrreducibleCloseds (singularStratumScheme X)) :=
        ⟨⟨closure {p.toHom (IsLocalRing.closedPoint ℂ)}, isIrreducible_singleton.closure,
          isClosed_closure⟩⟩
      have h0 : (0 : WithBot ℕ∞) ≤ dimension (singularStratumScheme X) := Order.krullDim_nonneg
      have := h0.trans_lt ((dimension_singularStratumScheme_le X).trans_lt hlt)
      simp at this⟩
    exact borelMooreHomology.isZero_of_isEmpty R (by lia)
  | succ m ih =>
    refine isZero_borelMooreHomology_of_isZero_singularStratumScheme X R hn hi ?_
    have hlt := (dimension_singularStratumScheme_le X).trans_lt
      (topologicalKrullDim_singularStratum_lt ℂ X hn)
    have hle : dimension (singularStratumScheme X) ≤ (m : WithBot ℕ∞) := by
      generalize dimension (singularStratumScheme X) = x at hlt
      induction x with
      | bot => exact bot_le
      | coe y =>
        have : y < ((m + 1 : ℕ) : ℕ∞) := by exact_mod_cast hlt
        exact_mod_cast Order.le_of_lt_succ (by simpa using this)
    exact ih (singularStratumScheme X) hle (by lia)

end IsComplexScheme

end MMP
