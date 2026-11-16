module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.RegularPartConnected
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.SingularStratum
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.SingularStratumDimension
public import MMP.AlgebraicGeometry.SubschemeOver
/-!
# The complement of the singular stratum (Fulton, §19.1)

Let `X` be a complex scheme with irreducible components `X₁, …, X_r`. A point of `X - S_X` avoids
every intersection `Xⱼ ∩ X_l`, `j ≠ l`, so it lies in exactly one component; hence `X - S_X` is
the disjoint union of the open sets `Uⱼ = X - (S_X ∪ ⋃_{l ≠ j} X_l)`. Inside the component `Xⱼ`
(with its reduced structure, a variety), `Uⱼ` is the complement of the proper Zariski closed set
`Xⱼ - Uⱼ`, which contains the singular locus of `Xⱼ`; so `Uⱼ(ℂ)` is the set of regular
`ℂ`-points of `Xⱼ` off a proper Zariski closed set. By the connectedness of the regular part of a
complex variety, `Uⱼ(ℂ)` is a non-empty connected open subset of the complex manifold
`(Xⱼ)_reg(ℂ)`, of complex dimension `dim Xⱼ`, and the closed embedding `Xⱼ(ℂ) → X(ℂ)` carries it
onto the `ℂ`-points of `X` lying in `Uⱼ`.

## Main definitions

* `MMP.singularStratumComplementPoints`: `Uⱼ(K)`, as a set of `K`-points of `Xⱼ`.
* `MMP.singularStratumComplementOpens`: `Uⱼ(ℂ)` as an open subset of
  `(Xⱼ)_reg(ℂ)`.

## Main results

* `MMP.singularStratum_compl_eq_iUnion`,
  `MMP.pairwise_disjoint_singularStratumComplement`: `X - S_X = ⨆ⱼ Uⱼ`, a
  disjoint union.
* `MMP.singularStratumComplement_isManifold_isConnected`: each `Uⱼ(ℂ)` is a
  non-empty connected complex manifold of dimension `dim Xⱼ`, open in `(Xⱼ)_reg(ℂ)`.

## Implementation notes

The decomposition is proved for every scheme, the topological statements for an algebraic scheme
over `ℂ` (a complex scheme is one). `Uⱼ` is a set of scheme-theoretic points of `X`; its complex
points are read in the component, as the `ℂ`-points of `Xⱼ` whose closed point lies over `Uⱼ`,
which the closed embedding `Xⱼ(ℂ) → X(ℂ)` identifies with the `ℂ`-points of `X` in `Uⱼ`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology
open scoped ContDiff Manifold MMP.SubschemeOver

namespace MMP

universe u

section decomposition

variable {X : Scheme.{u}}

/-- The complement of the singular stratum is the union of the sets `Uⱼ`. -/
theorem singularStratum_compl_eq_iUnion :
    (singularStratum X)ᶜ = ⋃ Z : irreducibleComponents X, singularStratumComplement X Z := by
  ext x
  simp only [Set.mem_compl_iff, Set.mem_iUnion]
  refine ⟨fun hx ↦ ?_, fun ⟨_, hZ⟩ hS ↦ hZ (Or.inl hS)⟩
  obtain ⟨W, hW, hxW⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {x}
    isIrreducible_singleton
  refine ⟨⟨W, hW⟩, ?_⟩
  rintro (h | h)
  · exact hx h
  · obtain ⟨V, hV, hxV⟩ := Set.mem_iUnion₂.mp h
    exact hx (mem_singularStratum_iff.mpr (Or.inr ⟨⟨W, hW⟩, V, Ne.symm hV, hxW rfl, hxV⟩))

/-- The sets `Uⱼ` are pairwise disjoint. -/
theorem pairwise_disjoint_singularStratumComplement :
    Pairwise (Function.onFun Disjoint (singularStratumComplement X)) := fun Z W hZW ↦
  Set.disjoint_left.mpr fun _ hxZ hxW ↦ hxW (Or.inr (Set.mem_iUnion₂.mpr
    ⟨Z, hZW, singularStratumComplement_subset Z hxZ⟩))

/-- The generic point of a component `Xⱼ` lies in `Uⱼ`. -/
theorem genericPoint_mem_singularStratumComplement (Z : irreducibleComponents X) :
    haveI := isIntegral_irreducibleComponentScheme Z
    irreducibleComponentι X Z (genericPoint (irreducibleComponentScheme X Z)) ∈
      singularStratumComplement X Z := by
  have := isIntegral_irreducibleComponentScheme Z
  set g := genericPoint (irreducibleComponentScheme X Z)
  set ι := irreducibleComponentι X Z
  have hW : ∀ W : irreducibleComponents X, W ≠ Z → ι g ∉ W.1 := by
    intro W hWZ hg
    have hcl : IsClosed (ι ⁻¹' W.1) :=
      (isClosed_of_mem_irreducibleComponents _ W.2).preimage ι.continuous
    have huniv : ι ⁻¹' W.1 = Set.univ := by
      have := hcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hg)
      rw [(genericPoint_spec (irreducibleComponentScheme X Z)).def] at this
      exact Set.eq_univ_of_univ_subset this
    have hZW : Z.1 ⊆ W.1 := by
      rw [← range_irreducibleComponentι X Z]
      rintro _ ⟨y, rfl⟩
      exact (Set.eq_univ_iff_forall.mp huniv) y
    exact hWZ (Subtype.ext (subset_antisymm (Z.2.2 W.2.1 hZW) hZW))
  rintro (hS | hS)
  · rcases mem_singularStratum_iff.mp hS with ⟨Z', y, hy, hyg⟩ | ⟨Z₁, W₁, hne, h₁, h₂⟩
    · obtain rfl | hZ' := eq_or_ne Z' Z
      · exact hy ((irreducibleComponentι X Z').isClosedEmbedding.injective hyg ▸
          genericPoint_mem_regularLocus _)
      · refine hW Z' hZ' ?_
        rw [← hyg, ← range_irreducibleComponentι X Z']
        exact ⟨y, rfl⟩
    · obtain rfl | h := eq_or_ne Z₁ Z
      · exact hW W₁ (Ne.symm hne) h₂
      · exact hW Z₁ h h₁
  · obtain ⟨W, hWZ, hgW⟩ := Set.mem_iUnion₂.mp hS
    exact hW W hWZ hgW

end decomposition

section points

variable {K : Type u} [Field K] (X : Scheme.{u}) [X.Over (Spec (.of K))]

/-- `Uⱼ(K)`: the `K`-points of the component `Xⱼ` whose closed point lies over `Uⱼ`. -/
def singularStratumComplementPoints (Z : irreducibleComponents X) :
    Set (UnderlyingSpace K (irreducibleComponentScheme X Z)) :=
  {q | irreducibleComponentι X Z (q.toHom (IsLocalRing.closedPoint K)) ∈
    singularStratumComplement X Z}

/-- Membership in `Uⱼ(K)`: the closed point lies over `Uⱼ`. -/
@[simp]
theorem mem_singularStratumComplementPoints_iff {Z : irreducibleComponents X}
    {q : UnderlyingSpace K (irreducibleComponentScheme X Z)} :
    q ∈ singularStratumComplementPoints X Z ↔
      irreducibleComponentι X Z (q.toHom (IsLocalRing.closedPoint K)) ∈
        singularStratumComplement X Z :=
  Iff.rfl

/-- The closed set `Xⱼ - Uⱼ` is a proper subset of the component `Xⱼ`. -/
theorem preimage_singularStratumComplement_compl_ne_univ (Z : irreducibleComponents X) :
    irreducibleComponentι X Z ⁻¹' (singularStratumComplement X Z)ᶜ ≠ Set.univ := fun h ↦
  ((Set.eq_univ_iff_forall.mp h) _) (genericPoint_mem_singularStratumComplement Z)

/-- The closed embedding `Xⱼ(K) → X(K)` carries `Uⱼ(K)` onto the `K`-points of `X` in `Uⱼ`. -/
theorem image_mapFun_singularStratumComplementPoints (Z : irreducibleComponents X) :
    UnderlyingSpace.mapFun (irreducibleComponentι X Z) ''
        singularStratumComplementPoints (K := K) X Z =
      {p : UnderlyingSpace K X | p.toHom (IsLocalRing.closedPoint K) ∈
        singularStratumComplement X Z} := by
  ext p
  refine ⟨?_, fun hp ↦ ?_⟩
  · rintro ⟨q, hq, rfl⟩
    exact hq
  obtain ⟨q, rfl⟩ :
      p ∈ Set.range (UnderlyingSpace.mapFun (K := K) (irreducibleComponentι X Z)) := by
    rw [UnderlyingSpace.range_mapFun_of_isClosedImmersion, Set.mem_setOf_eq,
      range_irreducibleComponentι]
    exact singularStratumComplement_subset Z hp
  exact ⟨q, hp, rfl⟩

/-- `Uⱼ(K)` consists of regular points of `Xⱼ`, off the proper Zariski closed set `Xⱼ - Uⱼ`. -/
theorem singularStratumComplementPoints_eq_regularPart_diff (Z : irreducibleComponents X) :
    singularStratumComplementPoints (K := K) X Z =
      UnderlyingSpace.regularPart K (irreducibleComponentScheme X Z) \
        {q | q.toHom (IsLocalRing.closedPoint K) ∈
          irreducibleComponentι X Z ⁻¹' (singularStratumComplement X Z)ᶜ} := by
  ext q
  simp only [mem_singularStratumComplementPoints_iff, Set.mem_setOf_eq, Set.mem_diff,
    Set.mem_preimage, Set.mem_compl_iff, not_not]
  refine ⟨fun hq ↦ ⟨?_, hq⟩, fun hq ↦ hq.2⟩
  rw [UnderlyingSpace.mem_regularPart_iff]
  by_contra hreg
  exact hq (Or.inl (mem_singularStratum_iff.mpr (Or.inl ⟨Z, _, hreg, rfl⟩)))

/-- `Uⱼ(K)` consists of regular `K`-points of `Xⱼ`. -/
theorem singularStratumComplementPoints_subset_regularPart (Z : irreducibleComponents X) :
    singularStratumComplementPoints (K := K) X Z ⊆
      UnderlyingSpace.regularPart K (irreducibleComponentScheme X Z) :=
  (singularStratumComplementPoints_eq_regularPart_diff X Z).trans_subset Set.diff_subset

variable [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))]

include K in
/-- The preimage in `Xⱼ` of the complement of `Uⱼ` (the set `Xⱼ - Uⱼ`) is Zariski closed. -/
theorem isClosed_preimage_singularStratumComplement_compl (Z : irreducibleComponents X) :
    IsClosed (irreducibleComponentι X Z ⁻¹' (singularStratumComplement X Z)ᶜ) :=
  (isOpen_singularStratumComplement K X Z).isClosed_compl.preimage
    (irreducibleComponentι X Z).continuous

variable [TopologicalSpace K]

/-- `Uⱼ(K)` is open in `Xⱼ(K)`. -/
theorem isOpen_singularStratumComplementPoints (Z : irreducibleComponents X) :
    IsOpen (singularStratumComplementPoints (K := K) X Z) :=
  UnderlyingSpace.isOpen_preimage_of_isOpen
    ((isOpen_singularStratumComplement K X Z).preimage (irreducibleComponentι X Z).continuous)

end points

section complex

variable (X : Scheme.{0}) [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]
  [QuasiCompact (X ↘ Spec (.of ℂ))]

/-- `Uⱼ(ℂ)` is non-empty and connected. -/
theorem isConnected_singularStratumComplementPoints (Z : irreducibleComponents X) :
    IsConnected (singularStratumComplementPoints (K := ℂ) X Z) := by
  rw [singularStratumComplementPoints_eq_regularPart_diff]
  exact UnderlyingSpace.isConnected_regularPart_diff
    (isClosed_preimage_singularStratumComplement_compl (K := ℂ) X Z)
    (preimage_singularStratumComplement_compl_ne_univ X Z)

/-- `Uⱼ(ℂ)`, as an open subset of the complex manifold `(Xⱼ)_reg(ℂ)`. -/
def singularStratumComplementOpens (Z : irreducibleComponents X) :
    Opens (UnderlyingSpace.regularOpens ℂ (irreducibleComponentScheme X Z)) :=
  ⟨Subtype.val ⁻¹' singularStratumComplementPoints (K := ℂ) X Z,
    (isOpen_singularStratumComplementPoints X Z).preimage continuous_subtype_val⟩

/-- The open subset `singularStratumComplementOpens X Z` of `(Xⱼ)_reg(ℂ)` has underlying set
`Uⱼ(ℂ)`. -/
theorem image_val_singularStratumComplementOpens (Z : irreducibleComponents X) :
    Subtype.val '' (singularStratumComplementOpens X Z :
        Set (UnderlyingSpace.regularOpens ℂ (irreducibleComponentScheme X Z))) =
      singularStratumComplementPoints (K := ℂ) X Z := by
  rw [singularStratumComplementOpens, Opens.coe_mk, Set.image_preimage_eq_inter_range,
    Subtype.range_coe, UnderlyingSpace.coe_regularOpens, Set.inter_eq_left]
  exact singularStratumComplementPoints_subset_regularPart X Z

/-- **The complement of the singular stratum** (Fulton, §19.1). Let `X` be a complex scheme with
irreducible components `Xⱼ`. Then `X - S_X` is the disjoint union of the open sets `Uⱼ`, and each
`Uⱼ` is a non-empty connected complex manifold of complex dimension `dim Xⱼ`, open in
`(Xⱼ)_reg`: the set `Uⱼ(ℂ)` of `ℂ`-points of `Xⱼ` over `Uⱼ` lies in `(Xⱼ)_reg(ℂ)`, is open,
connected and non-empty, the closed embedding `Xⱼ(ℂ) → X(ℂ)` carries it onto the `ℂ`-points of
`X` in `Uⱼ`, and as an open subset of `(Xⱼ)_reg(ℂ)` it is a complex manifold of dimension
`dim Xⱼ`. -/
theorem singularStratumComplement_isManifold_isConnected :
    (singularStratum X)ᶜ = (⋃ Z : irreducibleComponents X, singularStratumComplement X Z) ∧
    Pairwise (Function.onFun Disjoint (singularStratumComplement X)) ∧
    ∀ Z : irreducibleComponents X,
      singularStratumComplementPoints (K := ℂ) X Z ⊆
          UnderlyingSpace.regularPart ℂ (irreducibleComponentScheme X Z) ∧
        IsOpen (singularStratumComplementPoints (K := ℂ) X Z) ∧
        IsConnected (singularStratumComplementPoints (K := ℂ) X Z) ∧
        UnderlyingSpace.mapFun (irreducibleComponentι X Z) ''
            singularStratumComplementPoints (K := ℂ) X Z =
          {p : UnderlyingSpace ℂ X | p.toHom (IsLocalRing.closedPoint ℂ) ∈
            singularStratumComplement X Z} ∧
        (∃ n : ℕ, (n : WithBot ℕ∞) = topologicalKrullDim (irreducibleComponentScheme X Z)) ∧
        ∀ (n : ℕ) (hn : (n : WithBot ℕ∞) = topologicalKrullDim (irreducibleComponentScheme X Z)),
          letI := UnderlyingSpace.regularChartedSpace (𝕜 := ℂ) hn
          IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω (singularStratumComplementOpens X Z) := by
  refine ⟨singularStratum_compl_eq_iUnion, pairwise_disjoint_singularStratumComplement,
    fun Z ↦ ⟨singularStratumComplementPoints_subset_regularPart X Z,
      isOpen_singularStratumComplementPoints X Z, isConnected_singularStratumComplementPoints X Z,
      image_mapFun_singularStratumComplementPoints X Z, ?_, fun n hn ↦ ?_⟩⟩
  · have hne : topologicalKrullDim (irreducibleComponentScheme X Z) ≠ ⊤ := by
      have : CompactSpace (irreducibleComponentScheme X Z) :=
        QuasiCompact.compactSpace_of_compactSpace (irreducibleComponentScheme X Z ↘ Spec (.of ℂ))
      exact AlgebraicGeometry.topologicalKrullDim_ne_top_of_locallyOfFiniteType ℂ
        (irreducibleComponentScheme X Z ↘ Spec (.of ℂ))
    have hbot : topologicalKrullDim (irreducibleComponentScheme X Z) ≠ ⊥ := by
      have := isIntegral_irreducibleComponentScheme Z
      exact Order.krullDim_ne_bot_iff.mpr ⟨⟨⊤, IrreducibleSpace.isIrreducible_univ _,
        isClosed_univ⟩⟩
    obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hbot
    have hm' : m ≠ ⊤ := by
      rintro rfl
      exact hne hm.symm
    obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp hm'
    exact ⟨n, hm⟩
  · letI := UnderlyingSpace.regularChartedSpace (𝕜 := ℂ) hn
    have := UnderlyingSpace.isManifold_regularOpens (𝕜 := ℂ) hn
    infer_instance

end complex

end MMP
