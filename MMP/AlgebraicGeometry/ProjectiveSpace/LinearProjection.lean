module

public import MMP.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.LocallyConstantAssembly
public import StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.PreimageDimension
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.IteratedProjection
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyDimension
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingLemma
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Dimension.AffineCone
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersectionLeadingTerm
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.LinearSubspaceDimension
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.SubvarietyIntersection
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.FiniteProjectionToProjectiveSpace
public import StacksFrontier.LinearAlgebra.SubspaceUnionCodim
public import StacksFrontier.Topology.Dimension.NowhereDense
public import StacksFrontier.Topology.Dimension.UnionDimension

/-!
# Hyperplane sections and linear projections of projective varieties

Let `V` be a finite-dimensional vector space over a field `k` and `𝐏(V) = Proj (Sym_k V)` its
projective space, whose degree-one forms are the elements of `V`. This file states three facts
about closed subvarieties of `𝐏(V)`.

* Cutting an irreducible closed subset `Z ⊆ 𝐏(V)` of dimension `d` by `r` hyperplanes leaves
  every irreducible component of the intersection of dimension at least `d - r`. In an affine
  chart meeting the generic point of a component, the hyperplanes give `r` functions on the
  coordinate ring of `Z` over which the prime of that generic point is minimal; Krull's height
  theorem bounds its height by `r`, and the dimension formula for finitely generated domains over
  a field turns that into the bound on dimensions.
* An integral surface `X ⊆ 𝐏(V)` over an algebraically closed field admits a linear projection
  `𝐏(V) ⇢ 𝐏(W) ≅ ℙ²`, for a three-dimensional space `W ≤ V` of linear forms, whose centre (the
  common zero locus of `W`) misses `X`, and which restricts to a finite surjective morphism
  `X ⟶ 𝐏(W)`.
* Over an uncountable algebraically closed field, the closed points of an irreducible closed
  surface in `𝐏(V)` are not covered by countably many closed subsets of dimension at most one.
  Among the uncountably many members of a pencil of hyperplanes whose base locus meets the
  surface in finitely many points, some member contains none of the countably many curves leaving
  the base locus; a component of its section is a curve meeting each of the given closed subsets
  in finitely many points, and a second pencil shows that such a curve is not a countable union of
  finite sets.

## Main results

* `MMP.topologicalKrullDim_le_irreducibleComponent_inter_hyperplanes_add`: every irreducible
  component `C` of `Z ∩ H₁ ∩ ⋯ ∩ H_r` satisfies `dim Z ≤ dim C + r`.
* `MMP.exists_isFinite_surjective_projection_plane`: a finite surjective linear projection of an
  integral projective surface onto `ℙ²` with centre disjoint from it.
* `MMP.exists_isClosed_singleton_notMem_iUnion_of_topologicalKrullDim_le_one`: an irreducible
  projective surface over an uncountable algebraically closed field has a closed point outside any
  countable union of curves.

## Implementation notes

Projective space is `AlgebraicGeometry.projectiveSpaceOfModule k V`, the hyperplane of a linear
form `f ∈ V` is `AlgebraicGeometry.ProjectiveSpaceOfModule.linearSubspace k V (k ∙ f)`, and the
linear projection away from the common zero locus of a subspace `W ≤ V` of linear forms is
`AlgebraicGeometry.ProjectiveSpaceOfModule.projection k V W`, a morphism from the complement
`projectionDomain k V W` of that zero locus to `𝐏(W)`. For `Module.finrank k W = 3` the target
`𝐏(W)` is the projective plane. The restriction of the projection to a closed subscheme
`i : X ⟶ 𝐏(V)` missing the centre is `j ≫ projection k V W` for the factorization `j` of `i`
through the domain of definition.

Dimensions are `topologicalKrullDim`, valued in `WithBot ℕ∞`, and the lower bound of the first
result is stated additively, `dim Z ≤ dim C + r`, with no truncated subtraction. The linear forms
cutting out the hyperplanes are not required to be nonzero: a zero form cuts out all of `𝐏(V)`,
and the bound still holds.

The first result holds over any field. The second is stated over an algebraically closed field,
the setting of the general-projection results it rests on, and the third over an uncountable
algebraically closed field: over a countable field such as the algebraic closure of `ℚ` a surface
is the union of the countably many curves through its countably many closed points. The
complex numbers are an instance of both. A curve of the third result is any closed subset of
`𝐏(V)` of dimension at most one, irreducible or not, and need not lie in the surface; the surface
is a closed irreducible subset of `𝐏(V)`, the statement depending only on the underlying space.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], Chapter 15
* [Stacks Project, Tag 0B0E](https://stacks.math.columbia.edu/tag/0B0E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

namespace MMP

private theorem eq_zeroLocus_genericPoint {A σ : Type*} [CommRing A] [SetLike σ A]
    [AddSubmonoidClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜] [QuasiSober (ProjectiveSpectrum 𝒜)]
    {Z : Set (ProjectiveSpectrum 𝒜)} (hZc : IsClosed Z) (hZi : IsIrreducible Z) :
    Z = ProjectiveSpectrum.zeroLocus 𝒜 (hZi.genericPoint.asHomogeneousIdeal.toIdeal : Set A) := by
  set z := hZi.genericPoint
  rw [← hZi.closure_genericPoint hZc, ← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure,
    ProjectiveSpectrum.vanishingIdeal_singleton]
  rfl

private theorem toIdeal_genericPoint_mem_minimalPrimes {A σ : Type*} [CommRing A] [SetLike σ A]
    [AddSubmonoidClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜] [QuasiSober (ProjectiveSpectrum 𝒜)]
    {I : Ideal A} (hI : I.IsHomogeneous 𝒜) {S : Set (ProjectiveSpectrum 𝒜)}
    (hS : ∀ y, y ∈ S ↔ I ≤ y.asHomogeneousIdeal.toIdeal)
    {C : Set S} (hC : C ∈ irreducibleComponents S) (hCc : IsClosed (Subtype.val '' C))
    (hCi : IsIrreducible (Subtype.val '' C)) :
    hCi.genericPoint.asHomogeneousIdeal.toIdeal ∈ I.minimalPrimes := by
  set c := hCi.genericPoint
  set Q := c.asHomogeneousIdeal.toIdeal
  have hCvc : Subtype.val '' C = ProjectiveSpectrum.zeroLocus 𝒜 (Q : Set A) :=
    eq_zeroLocus_genericPoint hCc hCi
  have hcCv : c ∈ Subtype.val '' C := by
    rw [hCvc]
    exact (ProjectiveSpectrum.mem_zeroLocus _ _ _).mpr le_rfl
  obtain ⟨w, -, hw⟩ := hcCv
  have hIQ : I ≤ Q := (hS c).mp (hw ▸ w.2)
  have : Q.IsPrime := c.isPrime
  obtain ⟨Q', hQ'min, hQ'Q⟩ := Ideal.exists_minimalPrimes_le hIQ
  set Q'' := Ideal.homogeneousCore 𝒜 Q'
  have h1 : I ≤ Q''.toIdeal := by
    rw [← hI.toIdeal_homogeneousCore_eq_self]
    exact Ideal.homogeneousCore_mono 𝒜 hQ'min.1.2
  have h2 : Q''.toIdeal ≤ Q' := Ideal.toIdeal_homogeneousCore_le 𝒜 Q'
  let y : ProjectiveSpectrum 𝒜 :=
    ⟨Q'', hQ'min.1.1.homogeneousCore, fun h => c.not_irrelevant_le
      (h.trans fun x hx => hQ'Q (h2 hx))⟩
  have hyS : y ∈ S := (hS y).mpr h1
  have hCK : C ⊆ closure {(⟨y, hyS⟩ : S)} := by
    intro w hw
    rw [← specializes_iff_mem_closure, subtype_specializes_iff, specializes_iff_mem_closure,
      ← ProjectiveSpectrum.le_iff_mem_closure]
    have hwQ : (Q : Set A) ⊆ (w.1.asHomogeneousIdeal : Set A) := by
      have : w.1 ∈ Subtype.val '' C := ⟨w, hw, rfl⟩
      rw [hCvc] at this
      exact (ProjectiveSpectrum.mem_zeroLocus _ _ _).mp this
    exact fun x hx => hwQ (hQ'Q (h2 hx))
  have hQy : Q ≤ Q''.toIdeal := by
    have : y ∈ Subtype.val '' C :=
      ⟨_, hC.2 isIrreducible_singleton.closure hCK (subset_closure rfl), rfl⟩
    rw [hCvc] at this
    exact (ProjectiveSpectrum.mem_zeroLocus _ _ _).mp this
  exact le_antisymm hQ'Q (hQy.trans h2) ▸ hQ'min

private theorem ringKrullDim_quotient_le_add_of_mem_minimalPrimes {k : Type u} [Field k]
    {N r : ℕ} {q Q : Ideal (MvPolynomial (Fin N) k)} [q.IsPrime] (hqQ : q ≤ Q)
    (g : Fin r → MvPolynomial (Fin N) k) (hQ : Q ∈ (q ⊔ Ideal.span (Set.range g)).minimalPrimes) :
    ringKrullDim (MvPolynomial (Fin N) k ⧸ q) ≤ ringKrullDim (MvPolynomial (Fin N) k ⧸ Q) + r := by
  classical
  have : Q.IsPrime := hQ.1.1
  set π := Ideal.Quotient.mk q
  have hQπ : (Q.map π).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  set s : Finset (MvPolynomial (Fin N) k ⧸ q) := Finset.univ.image fun i => π (g i)
  have hs : Ideal.span (s : Set (MvPolynomial (Fin N) k ⧸ q)) =
      (Ideal.span (Set.range g)).map π := by
    rw [Ideal.map_span]
    congr 1
    ext x
    simp [s]
  have hmin : Q.map π ∈ (Ideal.span (s : Set (MvPolynomial (Fin N) k ⧸ q))).minimalPrimes := by
    rw [hs, Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    exact ⟨Q, by rwa [sup_comm], rfl⟩
  have key := Stacks.Intersection.ringKrullDim_le_ringKrullDim_quotient_add_card k
    (MvPolynomial (Fin N) k ⧸ q) hmin
  rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hqQ)] at key
  have hcard : (s.card : WithBot ℕ∞) ≤ r := by
    have := Finset.card_image_le (s := Finset.univ) (f := fun i => π (g i))
    simp only [Finset.card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  exact key.trans (by gcongr)

open MvPolynomial in
/-- **The hyperplane bound in the polynomial model.** In `Proj k[X₀, …, X_{N-1}]`, let `Z` be an
irreducible closed subset and `g₁, …, g_r` linear forms. Every irreducible component `C` of
`Z ∩ V₊(g₁, …, g_r)` satisfies `dim Z ≤ dim C + r`. -/
private theorem topologicalKrullDim_le_irreducibleComponent_inter_zeroLocus_add
    {k : Type u} [Field k] {N : ℕ}
    {Z : Set (ProjectiveSpectrum (homogeneousSubmodule (Fin N) k))} (hZc : IsClosed Z)
    (hZi : IsIrreducible Z) {r : ℕ} (g : Fin r → MvPolynomial (Fin N) k)
    (hg : ∀ i, g i ∈ homogeneousSubmodule (Fin N) k 1)
    {S : Set (ProjectiveSpectrum (homogeneousSubmodule (Fin N) k))}
    (hS : S = Z ∩ ProjectiveSpectrum.zeroLocus _ (Set.range g))
    {C : Set S} (hC : C ∈ irreducibleComponents S) :
    topologicalKrullDim Z ≤ topologicalKrullDim C + r := by
  set 𝒜 := homogeneousSubmodule (Fin N) k
  have : QuasiSober (ProjectiveSpectrum 𝒜) :=
    inferInstanceAs (QuasiSober (AlgebraicGeometry.Proj 𝒜))
  have hSc : IsClosed S := hS ▸ hZc.inter (ProjectiveSpectrum.isClosed_zeroLocus _ _)
  set z := hZi.genericPoint
  set q : Ideal (MvPolynomial (Fin N) k) := z.asHomogeneousIdeal.toIdeal
  have hZz : Z = ProjectiveSpectrum.zeroLocus 𝒜 (q : Set _) := eq_zeroLocus_genericPoint hZc hZi
  set Cv : Set (ProjectiveSpectrum 𝒜) := Subtype.val '' C
  have hCc : IsClosed Cv :=
    hSc.isClosedMap_subtype_val _ (isClosed_of_mem_irreducibleComponents C hC)
  have hCi : IsIrreducible Cv := hC.1.image _ continuous_subtype_val.continuousOn
  set c := hCi.genericPoint
  set Q : Ideal (MvPolynomial (Fin N) k) := c.asHomogeneousIdeal.toIdeal
  have hCvc : Cv = ProjectiveSpectrum.zeroLocus 𝒜 (Q : Set _) := eq_zeroLocus_genericPoint hCc hCi
  have hdimC : topologicalKrullDim C = topologicalKrullDim Cv :=
    IsHomeomorph.topologicalKrullDim_eq _
      (Topology.IsEmbedding.subtypeVal.homeomorphImage C).isHomeomorph
  have hQmin : Q ∈ (q ⊔ Ideal.span (Set.range g)).minimalPrimes := by
    have hI : (q ⊔ Ideal.span (Set.range g)).IsHomogeneous 𝒜 :=
      z.asHomogeneousIdeal.isHomogeneous.sup
        (Ideal.homogeneous_span 𝒜 _ fun x ⟨i, hi⟩ => ⟨1, hi ▸ hg i⟩)
    refine toIdeal_genericPoint_mem_minimalPrimes hI (fun y => ?_) hC hCc hCi
    rw [hS, hZz, sup_le_iff, Ideal.span_le]
    exact Iff.rfl
  have : q.IsPrime := z.isPrime
  have key := ringKrullDim_quotient_le_add_of_mem_minimalPrimes
    (le_sup_left.trans hQmin.1.2) g hQmin
  have eZ := Stacks.ProjectiveSpace.topologicalKrullDim_projectiveSpectrum_zeroLocus_add_one q
    z.asHomogeneousIdeal.isHomogeneous ⟨z, (ProjectiveSpectrum.mem_zeroLocus _ _ _).mpr le_rfl⟩
  have eC := Stacks.ProjectiveSpace.topologicalKrullDim_projectiveSpectrum_zeroLocus_add_one Q
    c.asHomogeneousIdeal.isHomogeneous ⟨c, (ProjectiveSpectrum.mem_zeroLocus _ _ _).mpr le_rfl⟩
  rw [← hZz] at eZ
  rw [← hCvc] at eC
  rw [hdimC]
  refine (ENat.WithBot.add_le_add_natCast_right_iff (c := 1)).mp ?_
  calc topologicalKrullDim Z + ((1 : ℕ) : WithBot ℕ∞)
      = ringKrullDim (MvPolynomial (Fin N) k ⧸ q) := by rw [Nat.cast_one, eZ]
    _ ≤ ringKrullDim (MvPolynomial (Fin N) k ⧸ Q) + r := key
    _ = (topologicalKrullDim Cv + 1) + r := by rw [eC]
    _ = topologicalKrullDim Cv + r + ((1 : ℕ) : WithBot ℕ∞) := by
      rw [Nat.cast_one, add_right_comm]

variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V]

private theorem exists_finrank_eq_add_one [FiniteDimensional k V]
    (x : projectiveSpaceOfModule k V) : ∃ n, Module.finrank k V = n + 1 := by
  refine ⟨Module.finrank k V - 1, ?_⟩
  obtain ⟨v, hv⟩ := exists_ι_notMem k V x
  have : Nontrivial V := ⟨⟨v, 0, by rintro rfl; exact hv (by simp)⟩⟩
  have := Module.finrank_pos (R := k) (M := V)
  omega

/-- **Hyperplane sections have the expected lower dimension bound.** Let `Z ⊆ 𝐏(V)` be an
irreducible closed subset and `H_i = V(f_i)`, `i < r`, hyperplanes. Every irreducible component
`C` of `Z ∩ H₀ ∩ ⋯ ∩ H_{r-1}` has `dim C ≥ dim Z - r`, stated as `dim Z ≤ dim C + r`. -/
@[mmp "lem_mmp_foundation_projective_hyperplane_dimension_lower"]
theorem topologicalKrullDim_le_irreducibleComponent_inter_hyperplanes_add [FiniteDimensional k V]
    {Z : Set (projectiveSpaceOfModule k V)} (hZc : IsClosed Z) (hZi : IsIrreducible Z)
    {r : ℕ} (f : Fin r → V)
    (C : Set ↥(Z ∩ ⋂ i, linearSubspace k V (k ∙ f i)))
    (hC : C ∈ irreducibleComponents ↥(Z ∩ ⋂ i, linearSubspace k V (k ∙ f i))) :
    topologicalKrullDim ↥Z ≤ topologicalKrullDim ↥C + r := by
  obtain ⟨⟨x₀, -⟩, -⟩ := hC.1.nonempty
  obtain ⟨n, hn⟩ := exists_finrank_eq_add_one x₀
  let b : Module.Basis (Fin (n + 1)) k V := Module.finBasisOfFinrankEq k V hn
  let e : projectiveSpaceOfModule k V ≃ₜ
      ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) :=
    (projectiveSpaceOfModuleIsoProjMvPolynomial b).hom.homeomorph
  let ψ := SymPow.gradedMvPolynomialHom b
  let φ := SymPow.gradedMvPolynomialInv b
  have hφψ : ∀ a, φ (ψ a) = a := fun a =>
    DFunLike.congr_fun (SymPow.gradedMvPolynomialInv_comp_hom b) a
  let g : Fin r → MvPolynomial (Fin (n + 1)) k := fun i => ψ (SymmetricAlgebra.ι k V (f i))
  have hg : ∀ i, g i ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k 1 := fun i =>
    ψ.map_mem (ι_mem_symmetricPower_one k V (f i))
  have hmem : ∀ x : projectiveSpaceOfModule k V,
      e x ∈ ProjectiveSpectrum.zeroLocus _ (Set.range g) ↔
        x ∈ ⋂ i, linearSubspace k V (k ∙ f i) := by
    intro x
    rw [ProjectiveSpectrum.mem_zeroLocus, Set.mem_iInter, Set.range_subset_iff]
    refine forall_congr' fun i => ?_
    rw [mem_linearSubspace_iff, Submodule.span_singleton_le_iff_mem, mem_pointSubmodule_iff]
    change φ (ψ _) ∈ x.asHomogeneousIdeal ↔ _
    rw [hφψ]
  have hS' : e.symm ⁻¹' (Z ∩ ⋂ i, linearSubspace k V (k ∙ f i)) =
      e.symm ⁻¹' Z ∩ ProjectiveSpectrum.zeroLocus _ (Set.range g) := by
    ext y
    have := hmem (e.symm y)
    rw [e.apply_symm_apply] at this
    simp only [Set.mem_preimage, Set.mem_inter_iff, this]
  let es : ↥(e.symm ⁻¹' (Z ∩ ⋂ i, linearSubspace k V (k ∙ f i))) ≃ₜ
      ↥(Z ∩ ⋂ i, linearSubspace k V (k ∙ f i)) :=
    e.symm.subtype fun _ => Iff.rfl
  have hC' : es ⁻¹' C ∈
      irreducibleComponents ↥(e.symm ⁻¹' (Z ∩ ⋂ i, linearSubspace k V (k ∙ f i))) := by
    obtain ⟨w, hw⟩ := hC.1.nonempty
    exact preimage_mem_irreducibleComponents hC es.isOpenEmbedding
      ⟨w, hw, es.symm w, es.apply_symm_apply w⟩
  have key := topologicalKrullDim_le_irreducibleComponent_inter_zeroLocus_add
    (hZc.preimage e.symm.continuous)
    (by rw [e.preimage_symm]; exact hZi.image e e.continuous.continuousOn) g hg hS' hC'
  rwa [topologicalKrullDim_preimage_of_homeomorph, topologicalKrullDim_preimage_of_homeomorph]
    at key

/-- **A finite projection of a projective surface to the plane.** An integral surface
`i : X ⟶ 𝐏(V)`, closed in projective space over an algebraically closed field, admits a linear
projection to `ℙ² = 𝐏(W)`, `W ≤ V` a three-dimensional space of linear forms, whose centre (the
common zero locus of `W`) is disjoint from `X`, and whose restriction `X ⟶ 𝐏(W)` is finite and
surjective. -/
@[mmp "lem_mmp_fa15_finite_projection_plane"]
theorem exists_isFinite_surjective_projection_plane [IsAlgClosed k] [FiniteDimensional k V]
    {X : Scheme.{u}} [IsIntegral X] (i : X ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion i]
    (hdim : topologicalKrullDim X = 2) :
    ∃ W : Submodule k V, Module.finrank k ↥W = 3 ∧
      Disjoint (Set.range i.base) (linearSubspace k V W) ∧
      ∃ j : X ⟶ (projectionDomain k V W).toScheme,
        j ≫ (projectionDomain k V W).ι = i ∧
        IsFinite (j ≫ projection k V W) ∧ Surjective (j ≫ projection k V W) := by
  have hZdim : topologicalKrullDim (Set.range i.base) = 2 := by
    rw [← hdim]
    exact (i.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq).symm
  obtain ⟨x₀⟩ : Nonempty X := inferInstance
  obtain ⟨n, hn⟩ := exists_finrank_eq_add_one (i.base x₀)
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := k) (by omega)
  have h3 : 3 ≤ Module.finrank k V := by
    have h := topologicalKrullDim_subspace_le (projectiveSpaceOfModule k V) (Set.range i.base)
    rw [hZdim, topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq hn] at h
    have : (2 : ℕ) ≤ n := by exact_mod_cast h
    omega
  obtain ⟨W, hW, hdisj⟩ := Stacks.WeilDeRham.exists_finrank_eq_disjoint_linearSubspace 3 h3
    (Set.range i.base) i.isClosedEmbedding.isClosed_range (by rw [hZdim]; norm_num)
  obtain ⟨j, hj, hfin⟩ := exists_isFinite_projection_of_disjoint i W hdisj
  refine ⟨W, hW, hdisj, j, hj, hfin, ⟨?_⟩⟩
  set f := j ≫ projection k V W
  have hcl : IsClosed (Set.range f.base) := f.isClosedMap.isClosed_range
  have hrange : (2 : WithBot ℕ∞) ≤ topologicalKrullDim (Set.range f.base) := by
    rw [← hdim]
    exact Topology.topologicalKrullDim_le_of_continuous_of_specializes_injective
      (Set.rangeFactorization f.base) (f.continuous.rangeFactorization)
      fun x y hxy h => eq_of_specializes_of_base_eq_of_isIntegralHom f hxy
        (congrArg Subtype.val h)
  let b : Module.Basis (Fin (2 + 1)) k W := Module.finBasisOfFinrankEq k W hW
  have := irreducibleSpace_projectiveSpaceOfModule_of_basis k W b
  have hPW : topologicalKrullDim (projectiveSpaceOfModule k W) = 2 :=
    topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq hW
  rw [← Set.range_eq_univ]
  by_contra hne
  have := topologicalKrullDim_lt_of_isClosed_ne_univ hcl hne (by rw [hPW]; decide)
  rw [hPW] at this
  exact absurd hrange (not_le.mpr this)

private theorem zero_le_topologicalKrullDim_of_nonempty {X : Type*} [TopologicalSpace X] {S : Set X}
    (h : S.Nonempty) : 0 ≤ topologicalKrullDim S := by
  have hne : topologicalKrullDim S ≠ ⊥ := by
    rw [Ne, topologicalKrullDim_eq_bot_iff_isEmpty]
    exact fun h' => h'.false ⟨h.some, h.some_mem⟩
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hne
  rw [← hm]
  exact WithBot.coe_le_coe.mpr bot_le

private theorem topologicalKrullDim_add_one_le_of_forall_closure {X : Type*} [TopologicalSpace X]
    [QuasiSober X] {Y : Set X} (hY : IsClosed Y) {d : ℕ}
    (h : ∀ x ∈ Y, topologicalKrullDim ↥(closure {x}) + 1 ≤ d) :
    topologicalKrullDim ↥Y + 1 ≤ d := by
  rcases d with _ | m
  · have hY0 : Y = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun x hx => ?_
      have h2 := zero_le_topologicalKrullDim_of_nonempty (S := closure {x}) ⟨x, subset_closure rfl⟩
      have : (0 : WithBot ℕ∞) + 1 ≤ ((0 : ℕ) : WithBot ℕ∞) := le_trans (by gcongr) (h x hx)
      norm_num at this
    subst hY0
    have : topologicalKrullDim (∅ : Set X) = ⊥ := by
      rw [topologicalKrullDim_eq_bot_iff_isEmpty]
      exact Set.isEmpty_coe_sort.mpr rfl
    rw [this]
    simp
  · have hle : topologicalKrullDim ↥Y ≤ m := by
      refine topologicalKrullDim_le_of_forall_closure hY fun x hx => ?_
      have := h x hx
      rw [Nat.cast_succ] at this
      exact ENat.WithBot.add_le_add_natCast_right_iff (c := 1).mp (by exact_mod_cast this)
    rw [Nat.cast_succ]
    gcongr

private theorem noetherianSpace_projectiveSpaceOfModule [FiniteDimensional k V] :
    TopologicalSpace.NoetherianSpace (projectiveSpaceOfModule k V) := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · have : IsEmpty (projectiveSpaceOfModule k V) := ⟨fun x => by
      obtain ⟨v, hv⟩ := exists_ι_notMem k V x
      exact hv (by rw [Subsingleton.elim v 0]; simp)⟩
    infer_instance
  have := isProper_projectiveSpaceOfModuleToSpec k V
  have : IsLocallyNoetherian (projectiveSpaceOfModule k V) :=
    LocallyOfFiniteType.isLocallyNoetherian (projectiveSpaceOfModuleToSpec k V)
  have : CompactSpace (projectiveSpaceOfModule k V) :=
    QuasiCompact.compactSpace_of_compactSpace (projectiveSpaceOfModuleToSpec k V)
  have : IsNoetherian (projectiveSpaceOfModule k V) := {}
  infer_instance

/-- A linear form cutting a closed subset of `𝐏(V)` in dimension at least one less. -/
private theorem exists_topologicalKrullDim_inter_linearSubspace_add_one_le [Infinite k]
    [FiniteDimensional k V] {Z : Set (projectiveSpaceOfModule k V)} (hZ : IsClosed Z) :
    ∃ v : V, topologicalKrullDim ↥(Z ∩ linearSubspace k V (k ∙ v)) + 1 ≤
      topologicalKrullDim ↥Z := by
  classical
  have := noetherianSpace_projectiveSpaceOfModule (k := k) (V := V)
  have hfin : (irreducibleComponents Z).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  let Wc : Set Z → Submodule k V := fun C =>
    if h : C.Nonempty then pointSubmodule k V h.some.1 else ⊥
  have hWc : ∀ C ∈ hfin.toFinset, Wc C ≠ ⊤ := by
    intro C hC
    have hne : C.Nonempty := (hfin.mem_toFinset.mp hC).1.nonempty
    simp only [Wc, hne, ↓reduceDIte]
    intro htop
    obtain ⟨x, hx⟩ := exists_ι_notMem k V hne.some.1
    exact hx ((mem_pointSubmodule_iff k V _ x).mp (htop ▸ Submodule.mem_top))
  obtain ⟨v, hv⟩ := Stacks.LinearAlgebra.exists_notMem_biUnion_of_infinite hfin.toFinset Wc hWc
  refine ⟨v, ?_⟩
  have hAclosed : IsClosed (Z ∩ linearSubspace k V (k ∙ v)) :=
    hZ.inter (isClosed_linearSubspace k V _)
  have hnd : IsNowhereDense ((Subtype.val : Z → _) ⁻¹' (Z ∩ linearSubspace k V (k ∙ v))) := by
    rw [isNowhereDense_preimage_val_iff_forall_irreducibleComponents hAclosed]
    intro C hC hCA
    have hne : C.Nonempty := hC.1.nonempty
    have hmem : (hne.some : Z).1 ∈ linearSubspace k V (k ∙ v) :=
      (hCA ⟨hne.some, hne.some_mem, rfl⟩).2
    rw [mem_linearSubspace_iff, Submodule.span_singleton_le_iff_mem] at hmem
    have := hv C (hfin.mem_toFinset.mpr hC)
    simp only [Wc, hne, ↓reduceDIte] at this
    exact this hmem
  have h1 := hnd.topologicalKrullDim_add_one_le (hAclosed.preimage continuous_subtype_val)
  rwa [topologicalKrullDim_preimage_val Z _ Set.inter_subset_left] at h1

/-- Two members of a pencil of hyperplanes meet in its base locus. -/
private theorem linearSubspace_inter_linearSubspace_add_smul_subset {f g : V} {a b : k}
    (hab : a ≠ b) :
    linearSubspace k V (k ∙ (f + a • g)) ∩ linearSubspace k V (k ∙ (f + b • g)) ⊆
      linearSubspace k V (k ∙ f) ∩ linearSubspace k V (k ∙ g) := by
  rintro q ⟨ha, hb⟩
  simp only [mem_linearSubspace_iff, Submodule.span_singleton_le_iff_mem] at ha hb
  simp only [Set.mem_inter_iff, mem_linearSubspace_iff, Submodule.span_singleton_le_iff_mem]
  have hg : g ∈ pointSubmodule k V q := by
    have hsub := Submodule.sub_mem _ ha hb
    rw [add_sub_add_left_eq_sub, ← sub_smul] at hsub
    have := Submodule.smul_mem _ (a - b)⁻¹ hsub
    rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hab), one_smul] at this
  refine ⟨?_, hg⟩
  have := Submodule.sub_mem _ ha (Submodule.smul_mem _ a hg)
  rwa [add_sub_cancel_right] at this

private theorem exists_forall_subset_linearSubspace_add_smul [Uncountable k]
    {𝒟 : Set (Set (projectiveSpaceOfModule k V))} (h𝒟 : 𝒟.Countable) (f g : V) :
    ∃ a : k, ∀ D ∈ 𝒟, D ⊆ linearSubspace k V (k ∙ (f + a • g)) →
      D ⊆ linearSubspace k V (k ∙ f) ∩ linearSubspace k V (k ∙ g) := by
  set L := linearSubspace k V (k ∙ f) ∩ linearSubspace k V (k ∙ g)
  have hsub : ∀ D : Set (projectiveSpaceOfModule k V), ¬ D ⊆ L →
      ({a | D ⊆ linearSubspace k V (k ∙ (f + a • g))} : Set k).Subsingleton := by
    intro D hD a ha b hb
    by_contra hab
    exact hD ((Set.subset_inter ha hb).trans
      (linearSubspace_inter_linearSubspace_add_smul_subset hab))
  set bad : Set k := ⋃ D ∈ 𝒟, {a | D ⊆ linearSubspace k V (k ∙ (f + a • g)) ∧ ¬ D ⊆ L}
  have hbad : bad.Countable := by
    refine h𝒟.biUnion fun D _ => ?_
    by_cases hD : D ⊆ L
    · simp [hD]
    · exact ((hsub D hD).anti fun a ha => ha.1).countable
  obtain ⟨a, ha⟩ : ∃ a, a ∉ bad := by
    by_contra h
    push Not at h
    exact not_countable (α := k) (Set.countable_univ_iff.mp (hbad.mono fun a _ => h a))
  refine ⟨a, fun D hD hDH => ?_⟩
  by_contra hDL
  exact ha (Set.mem_biUnion hD ⟨hDH, hDL⟩)

private theorem topologicalKrullDim_inter_add_one_le_of_forall_irreducibleComponents
    [FiniteDimensional k V] {Y H M : Set (projectiveSpaceOfModule k V)} (hYc : IsClosed Y)
    (hHc : IsClosed H) {d : ℕ} (hYd : topologicalKrullDim ↥Y + 1 ≤ ((d + 1 : ℕ) : WithBot ℕ∞))
    (hM : topologicalKrullDim ↥M + 1 ≤ d)
    (hYM : ∀ D ∈ irreducibleComponents ↥Y, Subtype.val '' D ⊆ H → Subtype.val '' D ⊆ M) :
    topologicalKrullDim ↥(Y ∩ H) + 1 ≤ d := by
  have := noetherianSpace_projectiveSpaceOfModule (k := k) (V := V)
  refine topologicalKrullDim_add_one_le_of_forall_closure (hYc.inter hHc) fun x hx => ?_
  obtain ⟨D', hD', hxD'⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    ({⟨x, hx.1⟩} : Set ↥Y) isIrreducible_singleton
  have hDc : IsClosed (Subtype.val '' D') :=
    hYc.isClosedMap_subtype_val _ (isClosed_of_mem_irreducibleComponents _ hD')
  have hcl : closure {x} ⊆ Subtype.val '' D' :=
    hDc.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr ⟨_, hxD' rfl, rfl⟩)
  have hclH : closure {x} ⊆ H := hHc.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hx.2)
  by_cases hDH : Subtype.val '' D' ⊆ H
  · calc topologicalKrullDim ↥(closure {x}) + 1 ≤ topologicalKrullDim ↥M + 1 := by
          gcongr
          exact topologicalKrullDim_le_of_subset (hcl.trans (hYM D' hD' hDH))
      _ ≤ d := hM
  · have : IrreducibleSpace ↥(Subtype.val '' D') :=
      Subtype.irreducibleSpace (hD'.1.image _ continuous_subtype_val.continuousOn)
    have hprop := Topology.topologicalKrullDim_add_one_le_of_ne_univ
      (S := (Subtype.val : ↥(Subtype.val '' D') → _) ⁻¹' (Subtype.val '' D' ∩ H))
      ((hDc.inter hHc).preimage continuous_subtype_val) (by
        intro h
        apply hDH
        intro y hy
        have : (⟨y, hy⟩ : ↥(Subtype.val '' D')) ∈
            (Subtype.val : ↥(Subtype.val '' D') → _) ⁻¹' (Subtype.val '' D' ∩ H) :=
          h ▸ trivial
        exact this.2)
    rw [topologicalKrullDim_preimage_val _ _ Set.inter_subset_left] at hprop
    have h1 : topologicalKrullDim ↥(closure {x}) + 1 + 1 ≤ (d : WithBot ℕ∞) + 1 := by
      calc topologicalKrullDim ↥(closure {x}) + 1 + 1
          ≤ topologicalKrullDim ↥(Subtype.val '' D' ∩ H) + 1 + 1 := by
            gcongr
            exact topologicalKrullDim_le_of_subset (Set.subset_inter hcl hclH)
        _ ≤ topologicalKrullDim ↥(Subtype.val '' D') + 1 := by gcongr
        _ ≤ topologicalKrullDim ↥Y + 1 := by
            gcongr
            exact topologicalKrullDim_le_of_subset (Subtype.coe_image_subset _ _)
        _ ≤ _ := by exact_mod_cast hYd
    exact ENat.WithBot.add_le_add_natCast_right_iff (c := 1).mp (by exact_mod_cast h1)

private theorem nonempty_inter_linearSubspace_of_topologicalKrullDim_eq [IsAlgClosed k]
    [FiniteDimensional k V] {Z : Set (projectiveSpaceOfModule k V)} (hZc : IsClosed Z)
    (hZne : Z.Nonempty) {d : ℕ} (hZd : topologicalKrullDim ↥Z = ((d + 1 : ℕ) : WithBot ℕ∞))
    (v : V) : (Z ∩ linearSubspace k V (k ∙ v)).Nonempty := by
  obtain ⟨N, hN⟩ := exists_finrank_eq_add_one hZne.some
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := k) (by omega)
  have hPd : topologicalKrullDim (projectiveSpaceOfModule k V) = N :=
    topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq hN
  have hdN : d + 1 ≤ N := by
    have h := topologicalKrullDim_subspace_le (projectiveSpaceOfModule k V) Z
    rw [hZd, hPd] at h
    exact_mod_cast h
  have hq : Module.finrank k (V ⧸ k ∙ v) + Module.finrank k (k ∙ v) = N + 1 := by
    rw [Submodule.finrank_quotient_add_finrank, hN]
  have hv1 : Module.finrank k (k ∙ v) ≤ 1 := by
    simpa using finrank_span_le_card (R := k) ({v} : Set V)
  obtain ⟨m, hm⟩ : ∃ m, Module.finrank k (V ⧸ k ∙ v) = m + 1 :=
    ⟨Module.finrank k (V ⧸ k ∙ v) - 1, by omega⟩
  have hHd : topologicalKrullDim ↥(linearSubspace k V (k ∙ v)) = m :=
    topologicalKrullDim_linearSubspace_of_finrank_quotient_eq hm
  have hHne : (linearSubspace k V (k ∙ v)).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have : topologicalKrullDim ↥(linearSubspace k V (k ∙ v)) = ⊥ := by
      rw [topologicalKrullDim_eq_bot_iff_isEmpty, h]
      exact Set.isEmpty_coe_sort.mpr rfl
    rw [hHd] at this
    exact WithBot.coe_ne_bot this
  refine nonempty_inter_projectiveSpaceOfModule hZc (isClosed_linearSubspace k V _) hZne hHne ?_
  rw [hPd, hZd, hHd]
  exact_mod_cast (by omega : N ≤ d + 1 + m)

private theorem exists_isIrreducible_subset_inter_linearSubspace [FiniteDimensional k V]
    {Z : Set (projectiveSpaceOfModule k V)} (hZc : IsClosed Z) (hZi : IsIrreducible Z) {d : ℕ}
    (hZd : topologicalKrullDim ↥Z = ((d + 1 : ℕ) : WithBot ℕ∞)) {v : V}
    (hZv : ¬ Z ⊆ linearSubspace k V (k ∙ v)) (hne : (Z ∩ linearSubspace k V (k ∙ v)).Nonempty) :
    ∃ C ⊆ Z ∩ linearSubspace k V (k ∙ v), IsClosed C ∧ IsIrreducible C ∧
      topologicalKrullDim ↥C = d := by
  have := noetherianSpace_projectiveSpaceOfModule (k := k) (V := V)
  let fa : Fin 1 → V := fun _ => v
  have hS : (Z ∩ ⋂ i, linearSubspace k V (k ∙ fa i)) = Z ∩ linearSubspace k V (k ∙ v) := by
    simp only [fa, Set.iInter_const]
  obtain ⟨p, hp⟩ := hne
  have hp' : p ∈ Z ∩ ⋂ i, linearSubspace k V (k ∙ fa i) := by
    rw [hS]
    exact hp
  obtain ⟨C, hC, -⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    ({⟨p, hp'⟩} : Set ↥(Z ∩ ⋂ i, linearSubspace k V (k ∙ fa i))) isIrreducible_singleton
  have hdimC := topologicalKrullDim_le_irreducibleComponent_inter_hyperplanes_add hZc hZi fa C hC
  have hCvc : IsClosed (Subtype.val '' C) :=
    (hZc.inter (isClosed_iInter fun i => isClosed_linearSubspace k V _)).isClosedMap_subtype_val
      _ (isClosed_of_mem_irreducibleComponents _ hC)
  have hCvdim : topologicalKrullDim C = topologicalKrullDim (Subtype.val '' C) :=
    IsHomeomorph.topologicalKrullDim_eq _
      (Topology.IsEmbedding.subtypeVal.homeomorphImage C).isHomeomorph
  have hCvZH : Subtype.val '' C ⊆ Z ∩ linearSubspace k V (k ∙ v) := by
    rintro _ ⟨y, -, rfl⟩
    exact hS ▸ y.2
  refine ⟨_, hCvZH, hCvc, hC.1.image _ continuous_subtype_val.continuousOn, le_antisymm ?_ ?_⟩
  · have : IrreducibleSpace Z := Subtype.irreducibleSpace hZi
    have hne : (Subtype.val : Z → _) ⁻¹' (Subtype.val '' C) ≠ Set.univ := by
      intro h
      apply hZv
      intro y hy
      have : (⟨y, hy⟩ : Z) ∈ (Subtype.val : Z → _) ⁻¹' (Subtype.val '' C) := h ▸ trivial
      exact (hCvZH this).2
    have := Topology.topologicalKrullDim_add_one_le_of_ne_univ
      (hCvc.preimage continuous_subtype_val) hne
    rw [topologicalKrullDim_preimage_val Z _ fun y hy => (hCvZH hy).1, hZd] at this
    exact ENat.WithBot.add_le_add_natCast_right_iff (c := 1).mp (by exact_mod_cast this)
  · rw [hZd, hCvdim] at hdimC
    exact ENat.WithBot.add_le_add_natCast_right_iff (c := 1).mp (by exact_mod_cast hdimC)

/-- **An irreducible closed subset has a closed point outside countably many closed subsets
meeting it in smaller dimension.** An irreducible closed `Z ⊆ 𝐏(V)` of dimension `d` has a closed
point outside `⋃ n, B n` whenever each `Z ∩ B n` has dimension less than `d`. -/
private theorem exists_isClosed_singleton_notMem_iUnion_of_forall_inter [IsAlgClosed k]
    [Uncountable k] [FiniteDimensional k V] {ι : Type*} [Countable ι]
    (B : ι → Set (projectiveSpaceOfModule k V)) (hBc : ∀ n, IsClosed (B n)) (d : ℕ) :
    ∀ {Z : Set (projectiveSpaceOfModule k V)}, IsClosed Z → IsIrreducible Z →
      topologicalKrullDim ↥Z = d → (∀ n, topologicalKrullDim ↥(Z ∩ B n) + 1 ≤ d) →
      ∃ z ∈ Z, IsClosed ({z} : Set (projectiveSpaceOfModule k V)) ∧ z ∉ ⋃ n, B n := by
  have := noetherianSpace_projectiveSpaceOfModule (k := k) (V := V)
  induction d with
  | zero =>
    intro Z hZc hZi _ hB
    obtain ⟨z, hz, hzc⟩ := hZc.exists_closed_singleton hZi.nonempty
    refine ⟨z, hz, hzc, fun hzB => ?_⟩
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hzB
    have h2 := zero_le_topologicalKrullDim_of_nonempty (S := Z ∩ B n) ⟨z, hz, hn⟩
    have : (0 : WithBot ℕ∞) + 1 ≤ ((0 : ℕ) : WithBot ℕ∞) := le_trans (by gcongr) (hB n)
    norm_num at this
  | succ d ih =>
    intro Z hZc hZi hZd hB
    obtain ⟨f, hf⟩ := exists_topologicalKrullDim_inter_linearSubspace_add_one_le hZc
    obtain ⟨g, hg⟩ := exists_topologicalKrullDim_inter_linearSubspace_add_one_le
      (hZc.inter (isClosed_linearSubspace k V (k ∙ f)))
    set L := linearSubspace k V (k ∙ f) ∩ linearSubspace k V (k ∙ g) with hLdef
    have hL : topologicalKrullDim ↥(Z ∩ L) + 1 ≤ d := by
      have h1 : topologicalKrullDim ↥(Z ∩ L) + 1 + 1 ≤ (d : WithBot ℕ∞) + 1 := by
        rw [hLdef, ← Set.inter_assoc]
        calc _ ≤ topologicalKrullDim ↥(Z ∩ linearSubspace k V (k ∙ f)) + 1 := by gcongr
          _ ≤ _ := by
            rw [hZd] at hf
            exact_mod_cast hf
      exact ENat.WithBot.add_le_add_natCast_right_iff (c := 1).mp (by exact_mod_cast h1)
    have hZL : ¬ Z ⊆ L := by
      intro h
      rw [Set.inter_eq_left.mpr h, hZd] at hL
      have : ((d + 1 + 1 : ℕ) : WithBot ℕ∞) ≤ d := by exact_mod_cast hL
      have : d + 1 + 1 ≤ d := by exact_mod_cast this
      omega
    obtain ⟨a, ha⟩ := exists_forall_subset_linearSubspace_add_smul
      (𝒟 := insert Z (⋃ n, (Subtype.val '' ·) '' irreducibleComponents ↥(Z ∩ B n)))
      ((Set.countable_iUnion fun n =>
        (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.image _).countable).insert Z)
      f g
    have haZ : ¬ Z ⊆ linearSubspace k V (k ∙ (f + a • g)) :=
      fun h => hZL (ha Z (Set.mem_insert _ _) h)
    have hY : ∀ n, topologicalKrullDim ↥(Z ∩ B n ∩ linearSubspace k V (k ∙ (f + a • g))) + 1 ≤ d :=
      fun n => topologicalKrullDim_inter_add_one_le_of_forall_irreducibleComponents
        (hZc.inter (hBc n)) (isClosed_linearSubspace k V _) (hB n) hL fun D hD hDH y hy =>
          ⟨(Subtype.coe_image_subset _ D hy).1,
            ha _ (Set.mem_insert_of_mem _ (Set.mem_iUnion_of_mem n ⟨D, hD, rfl⟩)) hDH hy⟩
    obtain ⟨C, hCZH, hCc, hCi, hCd⟩ := exists_isIrreducible_subset_inter_linearSubspace hZc hZi
      hZd haZ (nonempty_inter_linearSubspace_of_topologicalKrullDim_eq hZc hZi.nonempty hZd _)
    obtain ⟨z, hz, hzc, hzB⟩ := ih hCc hCi hCd fun n =>
      calc topologicalKrullDim ↥(C ∩ B n) + 1
          ≤ topologicalKrullDim ↥(Z ∩ B n ∩ linearSubspace k V (k ∙ (f + a • g))) + 1 := by
            gcongr
            exact topologicalKrullDim_le_of_subset
              fun y hy => ⟨⟨(hCZH hy.1).1, hy.2⟩, (hCZH hy.1).2⟩
        _ ≤ d := hY n
    exact ⟨z, (hCZH hz).1, hzc, hzB⟩

/-- **A projective surface is not a countable union of curves.** Over an uncountable
algebraically closed field, an irreducible closed subset `Z ⊆ 𝐏(V)` of dimension two has a closed
point outside the union of any countably many closed subsets of `𝐏(V)` of dimension at most one.
-/
@[mmp "lem_fa15_surface_not_countable_union_curves"]
theorem exists_isClosed_singleton_notMem_iUnion_of_topologicalKrullDim_le_one [IsAlgClosed k]
    [Uncountable k] [FiniteDimensional k V] {Z : Set (projectiveSpaceOfModule k V)}
    (hZc : IsClosed Z) (hZi : IsIrreducible Z) (hZd : topologicalKrullDim ↥Z = 2)
    {ι : Type*} [Countable ι] (B : ι → Set (projectiveSpaceOfModule k V))
    (hBc : ∀ n, IsClosed (B n)) (hBd : ∀ n, topologicalKrullDim ↥(B n) ≤ 1) :
    ∃ z ∈ Z, IsClosed ({z} : Set (projectiveSpaceOfModule k V)) ∧ z ∉ ⋃ n, B n := by
  refine exists_isClosed_singleton_notMem_iUnion_of_forall_inter B hBc 2 hZc hZi
    (by exact_mod_cast hZd) fun n => ?_
  calc topologicalKrullDim ↥(Z ∩ B n) + 1 ≤ 1 + 1 := by
        gcongr
        exact (topologicalKrullDim_le_of_subset Set.inter_subset_right).trans (hBd n)
    _ = ((2 : ℕ) : WithBot ℕ∞) := by norm_num

end MMP
