module

public import MMP.AlgebraicTopology.FundamentalClass.Exists
public import MMP.AlgebraicTopology.BorelMoore.TopHomologyBasis
public import MMP.AlgebraicTopology.FundamentalClass.EuclideanComplexOrientation
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.RegularPartManifold
public import MMP.AlgebraicGeometry.Morphisms.SmoothStalkDimension
public import MMP.AlgebraicGeometry.Variety.RegularLocusSmooth
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import MMP.AlgebraicGeometry.Singularities.Surface.PointBlowupLogDiscrepancy

/-!
# Top Borel–Moore homology of smooth complex schemes and Mumford's negative definiteness

* For a smooth quasi-projective complex scheme `U` of pure dimension `d`, the group
  `H_{2d}^{BM}(U(ℂ); R)` has a basis indexed by the connected components of `U(ℂ)`, each
  generator restricting to the chart orientation class on algebraic charts inside its component
  and to zero on charts disjoint from it, and `H_j^{BM}(U(ℂ); R) = 0` for `j > 2d`. The proof
  takes the fundamental class of the oriented complex manifold `U(ℂ)` and splits it along the
  finitely many connected components.
* For a proper birational morphism `g : S ⟶ T` of normal quasi-projective surfaces and distinct
  curves `E₁, …, E_r` contracted by `g`, Mumford's intersection matrix `(Êᵢ · C'ⱼ)` computed on
  a resolution `p : S' ⟶ S` from the numerical pull-backs `Êᵢ` is negative definite, and it
  agrees with the intersection numbers on `S` when `Eᵢ` is `ℚ`-Cartier. The proof reduces to the
  negative definiteness of the exceptional curves of the proper birational morphism `p ≫ g` from
  a smooth surface.

## Main results

* `MMP.Analytic.exists_basis_borelMooreHomology_of_isQuasiProjective`: the basis of top
  Borel–Moore homology and the vanishing above the top degree.
* `MMP.Mori.posDef_neg_mumfordIntersectionMatrix_of_isBirationalMorphism`: Mumford's
  intersection matrix is negative definite.

## Implementation notes

The charts of `U(ℂ)` are the algebraic charts `IsAlgebraicChart e` with values in `ℂᵈ`; the
coefficients are an arbitrary commutative ring `R`. Negative definiteness is `(-M).PosDef` for
the real matrix of rational intersection numbers. The auxiliary lemmas of each proof live in the
namespace `Proof_<tag>` named after its label.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [B. Iversen, *Cohomology of Sheaves*][iversen1986], IX.4.
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], §4.1
* [D. Mumford, *The topology of normal singularities of an algebraic surface*][Mumford1961]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Proof_lem_mmp_smooth_quasiprojective_bm_orientation

open CategoryTheory.Limits TopologicalSpace
open MMP MMP.FundamentalClass MMP.UnderlyingSpace
open scoped Manifold ContDiff Function

/-- A `ℂ`-point of a complex scheme smooth over `ℂ` is a regular point. -/
private theorem mem_regularLocus_of_smoothOfRelativeDimension
    {U : Scheme.{0}} [U.Over (Spec (.of ℂ))] (d : ℕ)
    [SmoothOfRelativeDimension d (U ↘ Spec (.of ℂ))]
    (p : UnderlyingSpace ℂ U) :
    p.toHom (IsLocalRing.closedPoint ℂ) ∈ regularLocus U := by
  have : Smooth (U ↘ Spec (.of ℂ)) := SmoothOfRelativeDimension.smooth d _
  refine mem_regularLocus_of_smooth ℂ (𝟙 _) (U ↘ Spec (.of ℂ)) _ ?_
  have hS : IsRegular (Spec (.of ℂ)) := fun _ ↦ ⟨⟨⊤, isAffineOpen_top _⟩, trivial,
    IsRegularRing.of_ringEquiv (Scheme.ΓSpecIso (.of ℂ)).symm.commRingCatIsoToRingEquiv⟩
  have h12 := (isRegular_tfae (Spec (.of ℂ))).out 1 2
  exact (h12.mp hS).2 _

/-- The local ring at a `ℂ`-point of a complex scheme smooth of pure dimension `d` has
dimension `d`. -/
private theorem ringKrullDim_stalk_eq_of_smoothOfRelativeDimension
    {U : Scheme.{0}} [U.Over (Spec (.of ℂ))] (d : ℕ)
    [SmoothOfRelativeDimension d (U ↘ Spec (.of ℂ))] [IsSeparated (U ↘ Spec (.of ℂ))]
    (p : UnderlyingSpace ℂ U) :
    ringKrullDim (U.presheaf.stalk (p.toHom (IsLocalRing.closedPoint ℂ))) = d := by
  have : Smooth (U ↘ Spec (.of ℂ)) := SmoothOfRelativeDimension.smooth d _
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian (U ↘ Spec (.of ℂ))
  have : IsClosedImmersion (p.toHom ≫ U ↘ Spec (.of ℂ)) := by
    rw [p.toHom_comp_over]
    infer_instance
  have : IsClosedImmersion p.toHom := IsClosedImmersion.of_comp p.toHom (U ↘ Spec (.of ℂ))
  have h := MMP.ringKrullDim_stalk_eq_add_of_smoothOfRelativeDimension (n := d)
    p.toHom (U ↘ Spec (.of ℂ)) (IsLocalRing.closedPoint ℂ)
  have h0 : ∀ x : Spec (.of ℂ), ringKrullDim ((Spec (.of ℂ)).presheaf.stalk x) = 0 := by
    intro x
    have : x.asIdeal.IsPrime := x.isPrime
    rw [ringKrullDim_eq_of_ringEquiv (Spec.stalkIso (.of ℂ) x).commRingCatIsoToRingEquiv,
      IsLocalization.AtPrime.ringKrullDim_eq_height x.asIdeal, Ideal.eq_bot_of_prime x.asIdeal]
    simp
  rw [h0] at h
  simpa using h

/-- Every point of `U(ℂ)`, for `U` smooth of pure dimension `d` over `ℂ`, lies in the source of
an algebraic chart with values in `ℂᵈ`. -/
private theorem exists_isAlgebraicChart_of_smoothOfRelativeDimension
    {U : Scheme.{0}} [U.Over (Spec (.of ℂ))] [IsComplexScheme U] (d : ℕ)
    [SmoothOfRelativeDimension d (U ↘ Spec (.of ℂ))] [IsSeparated (U ↘ Spec (.of ℂ))]
    (p : UnderlyingSpace ℂ U) :
    ∃ e : OpenPartialHomeomorph (UnderlyingSpace ℂ U) (EuclideanSpace ℂ (Fin d)),
      p ∈ e.source ∧ IsAlgebraicChart e := by
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := p.toHom (IsLocalRing.closedPoint ℂ)) (U := ⊤) trivial
  letI : V.toScheme.Over (Spec (.of ℂ)) := ⟨V.ι ≫ U ↘ Spec (.of ℂ)⟩
  have : V.ι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  have : IsAffine V := hV
  have : LocallyOfFiniteType (V.toScheme ↘ Spec (.of ℂ)) := by
    change LocallyOfFiniteType (V.ι ≫ U ↘ Spec (.of ℂ))
    infer_instance
  letI : Algebra ℂ Γ(V, ⊤) := (structureRingHom ℂ V).toAlgebra
  have : Algebra.FiniteType ℂ Γ(V, ⊤) := finiteType_structureRingHom
  obtain ⟨q, hq⟩ : p ∈ Set.range (mapFun (K := ℂ) V.ι) := by
    rw [range_mapFun_of_isOpenImmersion, Set.mem_setOf_eq, Scheme.Opens.opensRange_ι,
      top_le_preimage_iff]
    exact hxV
  have hx : p.toHom (IsLocalRing.closedPoint ℂ) = V.ι (q.toHom (IsLocalRing.closedPoint ℂ)) := by
    rw [← hq, toHom_mapFun]
    rfl
  let y := q.toHom (IsLocalRing.closedPoint ℂ)
  let φ := (V.stalkIso y).commRingCatIsoToRingEquiv
  have hreg : y ∈ regularLocus V := by
    have hregU := mem_regularLocus_of_smoothOfRelativeDimension d p
    rw [hx] at hregU
    have : IsRegularLocalRing (U.presheaf.stalk (V.ι y)) := hregU
    exact IsRegularLocalRing.of_ringEquiv (R := U.presheaf.stalk (V.ι y)) φ.symm
  obtain ⟨m, e, hqe, he, hm⟩ := exists_isAlgebraicChart_of_isAffine rfl q hreg
  obtain rfl : m = d := by
    rw [ringKrullDim_eq_of_ringEquiv φ] at hm
    change _ = ringKrullDim (U.presheaf.stalk (V.ι y)) at hm
    rw [← hx, ringKrullDim_stalk_eq_of_smoothOfRelativeDimension d p] at hm
    exact_mod_cast hm
  exact ⟨e.lift_openEmbedding (isOpenEmbedding_map_of_isOpenImmersion V.ι), ⟨q, hqe, hq⟩,
    he.lift_openEmbedding V.ι⟩

/-- The algebraic charts of `U(ℂ)` with values in `ℂᵈ`, for `U` smooth of pure dimension `d`. -/
@[instance_reducible]
private noncomputable def algebraicChartedSpaceOfDimension
    (U : Scheme.{0}) [U.Over (Spec (.of ℂ))] [IsComplexScheme U] (d : ℕ)
    [SmoothOfRelativeDimension d (U ↘ Spec (.of ℂ))] [IsSeparated (U ↘ Spec (.of ℂ))] :
    ChartedSpace (EuclideanSpace ℂ (Fin d)) (UnderlyingSpace ℂ U) where
  atlas := {e | IsAlgebraicChart e}
  chartAt p := (exists_isAlgebraicChart_of_smoothOfRelativeDimension d p).choose
  mem_chart_source p := (exists_isAlgebraicChart_of_smoothOfRelativeDimension d p).choose_spec.1
  chart_mem_atlas p := (exists_isAlgebraicChart_of_smoothOfRelativeDimension d p).choose_spec.2

/-- The algebraic charts make `U(ℂ)` a complex manifold. -/
private theorem isManifold_algebraicChartedSpaceOfDimension
    (U : Scheme.{0}) [U.Over (Spec (.of ℂ))] [IsComplexScheme U] (d : ℕ)
    [SmoothOfRelativeDimension d (U ↘ Spec (.of ℂ))] [IsSeparated (U ↘ Spec (.of ℂ))] :
    letI := algebraicChartedSpaceOfDimension U d
    IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin d)) 1 (UnderlyingSpace ℂ U) := by
  letI := algebraicChartedSpaceOfDimension U d
  have : IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin d)) ω (UnderlyingSpace ℂ U) := by
    refine isManifold_of_contDiffOn _ _ _ ?_
    intro e e' he he'
    simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_id,
      Function.id_comp, Set.range_id, Set.inter_univ, Set.preimage_id_eq, id_eq]
    exact IsAlgebraicChart.contDiffOn_symm_trans he he'
  exact IsManifold.of_le le_top

section Restriction

open borelMooreHomology SingularChain LocallyFiniteChain Opposite Simplicial

variable (R : Type) [CommRing R] (M : ModuleCat.{0} R) {Y : TopCat.{0}} [T2Space Y]

/-- On chains, `ι_V^* ι_{U*} = 0` for an open and closed `U` and an open `V` disjoint from it. -/
private lemma chainMap_comp_restrictChainMap_eq_zero_of_disjoint
    (U V : TopologicalSpace.Opens Y) (hUV : Disjoint (U : Set Y) V)
    (hf : IsProperMap (clopenInclusion U)) :
    chainMap R M (clopenInclusion U) hf ≫ restrictChainMap R M V = 0 := by
  ext n c : 3
  apply Subtype.ext
  funext τ
  change kernelFun (restrictKernel V n)
    (pushforwardFun ((TopCat.toSSet.map (clopenInclusion U)).app _) c.1) τ = 0
  refine finsum_eq_zero_of_forall_eq_zero fun σ ↦ ?_
  by_cases hσ : σ ∈ Set.range ((TopCat.toSSet.map (clopenInclusion U)).app (op ⦋n⦌))
  · obtain ⟨τ', rfl⟩ := hσ
    rw [restrictKernel, restrCoeff_of_disjoint, zero_smul]
    exact hUV.mono_left (range_toSSetObjEquiv_map_clopenInclusion_subset U τ')
  · rw [pushforwardFun_apply_of_notMem_range _ hσ, smul_zero]

/-- `ι_V^* ι_{U*} = 0` on Borel–Moore homology, for an open and closed `U` and an open `V`
disjoint from it. -/
private lemma pushforward_comp_restrict_eq_zero_of_disjoint (U V : TopologicalSpace.Opens Y)
    (hUV : Disjoint (U : Set Y) V) (hf : IsProperMap (clopenInclusion U)) (j : ℤ) :
    pushforward R M (clopenInclusion U) hf j ≫ restrict R M V j = 0 := by
  have h := HomologicalComplex.homologyMap_comp
    (HomologicalComplex.extendMap (chainMap R M (clopenInclusion U) hf)
      ComplexShape.embeddingDownNat)
    (HomologicalComplex.extendMap (restrictChainMap R M V) ComplexShape.embeddingDownNat) (-j)
  rw [← HomologicalComplex.extendMap_comp,
    chainMap_comp_restrictChainMap_eq_zero_of_disjoint R M U V hUV hf,
    HomologicalComplex.extendMap_zero, HomologicalComplex.homologyMap_zero] at h
  exact h.symm

end Restriction

/-- A space covered by the images of continuously mapped spaces, finitely many, each with
finitely many connected components, has finitely many connected components. -/
private lemma finite_connectedComponents_of_cover {X : Type*} [TopologicalSpace X] {ι : Type*}
    [Finite ι] {Z : ι → Type*} [∀ i, TopologicalSpace (Z i)]
    [∀ i, Finite (ConnectedComponents (Z i))] (e : ∀ i, Z i → X) (he : ∀ i, Continuous (e i))
    (hcov : ∀ x, ∃ i z, e i z = x) : Finite (ConnectedComponents X) := by
  refine Finite.of_surjective (fun c : Σ i, ConnectedComponents (Z i) ↦
    (he c.1).connectedComponentsMap c.2) fun c ↦ ?_
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  obtain ⟨i, z, rfl⟩ := hcov x
  exact ⟨⟨i, ConnectedComponents.mk z⟩, rfl⟩

/-- The common zero set in `ℂⁿ` of finitely many polynomials has finitely many connected
components. -/
private lemma finite_connectedComponents_zeroLocus {n m : ℕ}
    (f : Fin m → MvPolynomial (Fin n) ℂ) :
    Finite (ConnectedComponents {v : Fin n → ℂ | ∀ j, MvPolynomial.eval v (f j) = 0}) := by
  obtain ⟨g, hg⟩ := exists_complexZeroLocus_eq f
  have hS := (isSemialgebraic_zeroLocus g).finite_connectedComponents
  have hiff : ∀ z : Fin n → ℂ, z ∈ {v : Fin n → ℂ | ∀ j, MvPolynomial.eval v (f j) = 0} ↔
      complexRealHomeomorph (Fin n) z ∈
        {x : Fin n × Fin 2 → ℝ | ∀ j, MvPolynomial.eval x (g j) = 0} := by
    intro z
    rw [← hg]
    change _ ↔ realToComplex (complexToReal z) ∈
      {v : Fin n → ℂ | ∀ j, MvPolynomial.eval v (f j) = 0}
    rw [realToComplex_complexToReal]
  let φ := (complexRealHomeomorph (Fin n)).subtype hiff
  exact finite_connectedComponents_of_cover (ι := Unit) (fun _ ↦ φ.symm)
    (fun _ ↦ φ.symm.continuous) fun x ↦ ⟨(), φ x, φ.symm_apply_apply x⟩

/-- The points of an affine open `V ⊆ X` form the image of a continuous map from a complex
algebraic set. -/
private lemma exists_zeroLocus_of_isAffineOpen (X : Scheme.{0}) [X.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] (V : X.Opens) (hV : IsAffineOpen V) :
    ∃ (n m : ℕ) (f : Fin m → MvPolynomial (Fin n) ℂ)
      (e : {v : Fin n → ℂ | ∀ j, MvPolynomial.eval v (f j) = 0} → UnderlyingSpace ℂ X),
      Continuous e ∧ ∀ p : UnderlyingSpace ℂ X, p.toHom (IsLocalRing.closedPoint ℂ) ∈ V →
        p ∈ Set.range e := by
  letI : V.toScheme.Over (Spec (.of ℂ)) := ⟨V.ι ≫ X ↘ Spec (.of ℂ)⟩
  have : V.ι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  have : IsAffine V := hV
  have : LocallyOfFiniteType (V.toScheme ↘ Spec (.of ℂ)) := by
    change LocallyOfFiniteType (V.ι ≫ X ↘ Spec (.of ℂ))
    infer_instance
  obtain ⟨n, m, f, ⟨φ⟩⟩ := exists_homeomorph_zeroLocus V
  refine ⟨n, m, f, map V.ι ∘ φ.symm,
    (isOpenEmbedding_map_of_isOpenImmersion V.ι).continuous.comp φ.symm.continuous,
    fun p hp ↦ ?_⟩
  rw [Set.range_comp, φ.symm.range_coe, Set.image_univ]
  exact mem_range_map_ι V p hp

/-- The underlying space of a complex scheme has finitely many connected components. -/
private theorem finite_connectedComponents_underlyingSpace (X : Scheme.{0})
    [X.Over (Spec (.of ℂ))] [IsComplexScheme X] :
    Finite (ConnectedComponents (UnderlyingSpace ℂ X)) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of ℂ))
  choose n m f e he hrange using fun V : X.affineOpens ↦ exists_zeroLocus_of_isAffineOpen X V.1 V.2
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun V : X.affineOpens ↦ (V : Set X))
    (fun V ↦ V.1.isOpen) fun x _ ↦ by
      obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
      exact Set.mem_iUnion.2 ⟨⟨V, hV⟩, hxV⟩
  have : ∀ V : t, Finite (ConnectedComponents
      {v : Fin (n V.1) → ℂ | ∀ j, MvPolynomial.eval v (f V.1 j) = 0}) :=
    fun V ↦ finite_connectedComponents_zeroLocus _
  refine finite_connectedComponents_of_cover (ι := t) (fun V ↦ e V.1) (fun V ↦ he V.1)
    fun p ↦ ?_
  obtain ⟨V, hVt, hpV⟩ :=
    Set.mem_iUnion₂.1 (ht (Set.mem_univ (p.toHom (IsLocalRing.closedPoint ℂ))))
  obtain ⟨z, hz⟩ := hrange V p hpV
  exact ⟨⟨V, hVt⟩, z, hz⟩

section Components

variable {R : Type} [CommRing R] {H : Type*} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H]
  [ContinuousAdd H] [ContinuousSMul ℝ H] [T2Space H] {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [ChartedSpace H M] [LocallyConnectedSpace M]
  [Finite (ConnectedComponents M)] {n : ℕ} {b : Module.Basis (Fin n) ℝ H}

/-- **The component basis of top Borel–Moore homology.** For a fundamental class `μ` of a
locally connected manifold `M` with finitely many connected components, `H_n M` has a basis
indexed by the components whose vector `[C]` restricts, on an open set inside `C`, as `μ` does,
and to zero on an open set disjoint from `C`. -/
private theorem exists_basis_connectedComponents_of_isFundamentalClass
    {μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of M) n}
    (hμ : IsFundamentalClass R b μ) :
    ∃ β : Module.Basis (ConnectedComponents M) R
        (borelMooreHomology R (ModuleCat.of R R) (TopCat.of M) n),
      ∀ (c : ConnectedComponents M) (V : Opens (TopCat.of M)),
        ((V : Set M) ⊆ ConnectedComponents.mk ⁻¹' {c} →
          borelMooreHomology.restrict R (ModuleCat.of R R) V n (β c) =
            borelMooreHomology.restrict R (ModuleCat.of R R) V n μ) ∧
        (Disjoint (V : Set M) (ConnectedComponents.mk ⁻¹' {c}) →
          borelMooreHomology.restrict R (ModuleCat.of R R) V n (β c) = 0) := by
  letI : Fintype (ConnectedComponents M) := Fintype.ofFinite _
  let C (c : ConnectedComponents M) : Opens M := ⟨ConnectedComponents.mk ⁻¹' {c}, by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    rw [connectedComponents_preimage_singleton]
    exact isOpen_connectedComponent⟩
  have hdisj : Pairwise (Disjoint on fun c ↦ (C c : Set M)) :=
    fun c c' hcc' ↦ (Set.disjoint_singleton.2 hcc').preimage _
  have hconn (c : ConnectedComponents M) : ConnectedSpace (C c) := by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    have h := isConnected_connectedComponent (x := x)
    rw [← connectedComponents_preimage_singleton] at h
    exact isConnected_iff_connectedSpace.mp h
  have hcover (x : M) : ∃ c, x ∈ C c := ⟨ConnectedComponents.mk x, rfl⟩
  have hzero (c : ConnectedComponents M) (V : Opens (TopCat.of M))
      (hV : Disjoint (V : Set M) (C c)) : borelMooreHomology.restrict R (ModuleCat.of R R) V n
        (hμ.topHomologyBasis hdisj hcover hconn c) = 0 := by
    rw [(hμ.topHomologyBasis_apply hdisj hcover hconn c).1, ← ConcreteCategory.comp_apply,
      pushforward_comp_restrict_eq_zero_of_disjoint R _ (C c) V hV.symm]
    rfl
  refine ⟨hμ.topHomologyBasis hdisj hcover hconn, fun c V ↦ ⟨fun hV ↦ ?_, hzero c V⟩⟩
  conv_rhs => rw [hμ.eq_sum_topHomologyBasis hdisj hcover hconn, map_sum,
    Finset.sum_eq_single c (fun c' _ hc' ↦ hzero c' V ((hdisj hc'.symm).mono_left hV))
      (by simp)]

end Components

end MMP.Proof_lem_mmp_smooth_quasiprojective_bm_orientation

namespace MMP.Analytic

open CategoryTheory.Limits TopologicalSpace
open MMP.FundamentalClass MMP.UnderlyingSpace
open MMP.Proof_lem_mmp_smooth_quasiprojective_bm_orientation

/-- **Top Borel–Moore homology of a smooth quasi-projective complex scheme.** Let `U` be a
smooth quasi-projective complex scheme of pure dimension `d`. Then `H_{2d}^{BM}(U(ℂ); R)` has a
basis `([C])_C` indexed by the connected components `C` of `U(ℂ)`. The generator `[C]`
restricts, on every algebraic chart `e : U(ℂ) ⇀ ℂᵈ` whose domain lies in `C`, to the orientation
class of `e` for the complex orientation, so its local orientation coefficient is one at every
point of `C`. It restricts to zero on every algebraic chart whose domain is disjoint from `C`.
Moreover `H_j^{BM}(U(ℂ); R) = 0` for every `j > 2d`. -/
@[mmp "lem_mmp_smooth_quasiprojective_bm_orientation"]
public theorem exists_basis_borelMooreHomology_of_isQuasiProjective
    (R : Type) [CommRing R]
    {U : Scheme.{0}} [U.Over (Spec (.of ℂ))] [IsComplexScheme U] (d : ℕ)
    [SmoothOfRelativeDimension d (U ↘ Spec (.of ℂ))]
    (hU : IsQuasiProjective (U ↘ Spec (.of ℂ))) :
    (∃ β : Module.Basis (ConnectedComponents (UnderlyingSpace ℂ U)) R
        (borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ U)) (2 * d : ℕ)),
      ∀ (c : ConnectedComponents (UnderlyingSpace ℂ U))
        (e : OpenPartialHomeomorph (UnderlyingSpace ℂ U) (EuclideanSpace ℂ (Fin d))),
        IsAlgebraicChart e →
        (e.source ⊆ ConnectedComponents.mk ⁻¹' {c} →
          IsChartOrientationClass R (euclideanComplexOrientationBasis d) e
            (borelMooreHomology.restrict R (ModuleCat.of R R) (chartOpens e) (2 * d : ℕ)
              (β c))) ∧
        (Disjoint e.source (ConnectedComponents.mk ⁻¹' {c}) →
          borelMooreHomology.restrict R (ModuleCat.of R R) (chartOpens e) (2 * d : ℕ)
            (β c) = 0)) ∧
      ∀ j : ℤ, 2 * (d : ℤ) < j →
        IsZero (borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ U)) j) := by
  have : IsSeparated (U ↘ Spec (.of ℂ)) := AlgebraicGeometry.IsQuasiProjective.isSeparated hU
  letI := algebraicChartedSpaceOfDimension U d
  have := isManifold_algebraicChartedSpaceOfDimension U d
  obtain ⟨μ, hμ⟩ := exists_isFundamentalClass (R := R) (M := UnderlyingSpace ℂ U)
    (isOrientedAtlas_of_isManifold_complex (UnderlyingSpace ℂ U))
    (euclideanComplexOrientationBasis d)
  have : LocallyConnectedSpace (UnderlyingSpace ℂ U) :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℂ (Fin d)) _
  have := finite_connectedComponents_underlyingSpace U
  obtain ⟨β, hβ⟩ := exists_basis_connectedComponents_of_isFundamentalClass hμ
  refine ⟨⟨β, fun c e he ↦ ⟨fun hsub ↦ ?_, (hβ c (chartOpens e)).2⟩⟩, fun j hj ↦ ?_⟩
  · rw [(hβ c (chartOpens e)).1 hsub]
    exact hμ e he
  · exact borelMooreHomology.isZero_of_dim_lt R (euclideanComplexOrientationBasis d)
      (by push_cast; omega)

end MMP.Analytic

namespace MMP.Proof_lem_mmp_surface_normal_exceptional_negative_definite

open TopologicalSpace MMP.Mori

universe v

/-- A `ℚ`-divisor whose components are among the distinct prime divisors `Fₐ` is
`∑ₐ D(Fₐ) Fₐ`. -/
private theorem eq_sum_smul_single {X : Scheme.{v}} {ι : Type*} [Fintype ι] (D : QDivisor X)
    (F : ι → MMP.Mori.PrimeDivisor X) (hF : Function.Injective F)
    (hD : ∀ Q, D Q ≠ 0 → ∃ a, F a = Q) :
    D = ∑ a, D (F a) • Divisor.toQDivisor (Finsupp.single (F a) 1) := by
  classical
  have h1 : ∀ a Q, (Divisor.toQDivisor (Finsupp.single (F a) 1)) Q = if F a = Q then 1 else 0 := by
    intro a Q
    by_cases h : F a = Q <;>
      simp [Divisor.toQDivisor, DivisorWithCoeffs.mapCoeffsAddMonoidHom, h]
  refine Finsupp.ext fun Q => ?_
  rw [Finsupp.finset_sum_apply]
  simp only [Finsupp.smul_apply, h1, smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases hQ : ∃ a, F a = Q
  · obtain ⟨a, rfl⟩ := hQ
    rw [Finset.sum_eq_single a (fun b _ hb => if_neg (hF.ne hb)) (by simp), if_pos rfl]
  · push Not at hQ
    rw [Finset.sum_eq_zero fun b _ => if_neg (hQ b)]
    by_contra h
    obtain ⟨a, ha⟩ := hD Q h
    exact hQ a ha

section Linear

variable {k : Type v} [Field k] {X Cs : Scheme.{v}} (sX : X ⟶ Spec (.of k))
  [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] (i : Cs ⟶ X) [IsProper (i ≫ sX)]
  (hdim : topologicalKrullDim Cs ≤ 1)

/-- On a scheme where every `ℚ`-divisor is `ℚ`-Cartier, the intersection number with a curve is
linear in the divisor: `((∑ cₐ Dₐ) · C) = ∑ cₐ (Dₐ · C)`. -/
private theorem intersectionNumber_sum_smul (hq : ∀ D : QDivisor X, D.IsQCartier)
    {ι : Type*} (s : Finset ι) (c : ι → ℚ) (D : ι → QDivisor X) :
    (∑ a ∈ s, c a • D a).intersectionNumber k sX i hdim (hq _) =
      ∑ a ∈ s, c a * (D a).intersectionNumber k sX i hdim (hq _) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [MMP.Fourfold.intersectionNumber_congr sX i hdim _ QDivisor.isQCartier_zero
      Finset.sum_empty, MMP.Fourfold.intersectionNumber_zero, Finset.sum_empty]
  | insert a s ha ih =>
    rw [MMP.Fourfold.intersectionNumber_congr sX i hdim _ (hq (c a • D a + ∑ b ∈ s, c b • D b))
        (Finset.sum_insert ha),
      QDivisor.intersectionNumber_add' k sX i hdim _ _ (hq _) (hq _),
      QDivisor.intersectionNumber_smul k sX i hdim (c a) (D a) (hq _), ih, Finset.sum_insert ha]

/-- **Expansion along the components.** On a scheme where every `ℚ`-divisor is `ℚ`-Cartier, a
divisor whose components are among the distinct prime divisors `Fₐ` has
`(D · C) = ∑ₐ D(Fₐ) (Fₐ · C)`. -/
private theorem intersectionNumber_eq_sum_coeff_mul (hq : ∀ D : QDivisor X, D.IsQCartier)
    {ι : Type*} [Fintype ι] (D : QDivisor X) (F : ι → MMP.Mori.PrimeDivisor X)
    (hF : Function.Injective F) (hD : ∀ Q, D Q ≠ 0 → ∃ a, F a = Q) :
    D.intersectionNumber k sX i hdim (hq D) = ∑ a, D (F a) *
      (Divisor.toQDivisor (Finsupp.single (F a) 1)).intersectionNumber k sX i hdim (hq _) := by
  rw [MMP.Fourfold.intersectionNumber_congr sX i hdim (hq D) (hq _)
    (eq_sum_smul_single D F hF hD)]
  exact intersectionNumber_sum_smul sX i hdim hq _ _ _

/-- The intersection number with the reduced closed subscheme of an ideal sheaf depends only on
the ideal sheaf. -/
private theorem intersectionNumber_subschemeι_congr {I J : X.IdealSheafData} (h : I = J)
    [IsProper (I.subschemeι ≫ sX)] [IsProper (J.subschemeι ≫ sX)]
    (hI : topologicalKrullDim I.subscheme ≤ 1) (hJ : topologicalKrullDim J.subscheme ≤ 1)
    (D : QDivisor X) (hD : D.IsQCartier) :
    D.intersectionNumber k sX I.subschemeι hI hD =
      D.intersectionNumber k sX J.subschemeι hJ hD := by
  subst h
  rfl

end Linear

/-- A vector orthogonal to every column of a matrix whose negative is positive definite is zero. -/
private theorem eq_zero_of_posDef_neg {ι : Type*} [Fintype ι] {M : Matrix ι ι ℚ}
    (hM : (-(Matrix.of fun a b => (M a b : ℝ))).PosDef) {x : ι → ℚ}
    (hx : ∀ b, ∑ a, x a * M a b = 0) : x = 0 := by
  by_contra hne
  have hx' : (fun a => (x a : ℝ)) ≠ 0 := fun h =>
    hne (funext fun a => Rat.cast_eq_zero.1 (congrFun h a))
  have h0 : Matrix.vecMul (fun a => (x a : ℝ)) (-(Matrix.of fun a b => (M a b : ℝ))) = 0 :=
    funext fun b => by
      simpa [Matrix.vecMul, dotProduct] using congrArg (fun q : ℚ => (q : ℝ)) (hx b)
  have := hM.dotProduct_mulVec_pos hx'
  rw [star_trivial, Matrix.dotProduct_mulVec, h0, zero_dotProduct] at this
  exact lt_irrefl _ this

/-- If `-M` is positive definite, the rows `v i = c i ⬝ M` vanish on the last `m` indices and
`c` is the identity on the first `r`, then `-(v i (castAdd m j))ᵢⱼ` is positive definite. -/
private theorem posDef_neg_of_posDef_neg_append {r m : ℕ}
    {M : Matrix (Fin (r + m)) (Fin (r + m)) ℝ} (hM : (-M).PosDef) (c v : Fin r → Fin (r + m) → ℝ)
    {w : Fin r → Fin r → ℝ} (hv : ∀ i β, v i β = ∑ α, c i α * M α β)
    (hc : ∀ i j, c i (Fin.castAdd m j) = if i = j then 1 else 0)
    (hv₀ : ∀ i a, v i (Fin.natAdd r a) = 0) (hw : ∀ i j, v i (Fin.castAdd m j) = w i j) :
    (-(Matrix.of w)).PosDef := by
  classical
  let A : Matrix (Fin (r + m)) (Fin r) ℝ := Matrix.of fun α i => c i α
  have hA : Function.Injective A.mulVec := fun x y hxy => funext fun i => by
    simpa [A, Matrix.mulVec, dotProduct, hc, ite_mul] using congrFun hxy (Fin.castAdd m i)
  convert hM.conjTranspose_mul_mul_same hA using 1
  ext i j
  simp only [Matrix.neg_apply, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    star_trivial, A, mul_neg, Finset.sum_neg_distrib, ← hv]
  simp [Fin.sum_univ_add, hv₀, hc, hw]

section Geometry

variable {k : Type v} [Field k] {S S' : Scheme.{v}} {sS : S ⟶ Spec (.of k)}
  [IsLocallyNoetherian S] [IsNormal S] [IsLocallyNoetherian S'] [IsNormal S']

omit [IsLocallyNoetherian S] [IsNormal S] in
/-- A variety over `k` is separated over the terminal scheme. -/
private theorem isSeparated_toTerminal (hS : IsNormalVariety k sS) :
    IsSeparated (S ↘ Limits.terminal Scheme) := by
  have := hS.1.toIsSeparated
  rw [Limits.terminal.hom_ext (S ↘ _) (sS ≫ (Spec (.of k) ↘ Limits.terminal Scheme))]
  infer_instance

/-- Over the generic point of a prime divisor of a normal variety, a resolution has exactly one
point. -/
private theorem eq_of_map_eq_genericPoint (hS : IsNormalVariety k sS) {p : S' ⟶ S}
    (hp : IsSmoothResolution sS p) (P : MMP.Mori.PrimeDivisor S) {x y : S'}
    (hx : p x = P.genericPoint) (hy : p y = P.genericPoint) : x = y := by
  obtain ⟨hYv, -, -⟩ := hp.isNormalVariety hS
  have : IsIntegral S := hS.1.toIsIntegral
  have : IsIntegral S' := hYv.1.toIsIntegral
  have : IsProper p := hp.isProper
  have : IsDominant p := hp.isBirationalMorphism.isDominant
  have hbij := hp.isBirationalMorphism.functionFieldMap_bijective
  have := P.isDiscreteValuationRing_localRing
  have : ValuationRing (S.presheaf.stalk (p x)) := by rw [hx]; infer_instance
  have : ValuationRing (S.presheaf.stalk (p y)) := by rw [hy]; infer_instance
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing p hbij x
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing p hbij y
  exact MMP.Positivity.eq_of_isIso_stalkMap p hbij (hy.trans hx.symm)

/-- If the transform of a prime divisor `Q` under a resolution is the prime divisor `P`, then
the generic point of `Q` maps to that of `P`. -/
private theorem map_genericPoint_of_transformPrimeDivisor_eq_some (hS : IsNormalVariety k sS)
    {p : S' ⟶ S} (hp : IsSmoothResolution sS p) {Q : MMP.Mori.PrimeDivisor S'}
    {P : MMP.Mori.PrimeDivisor S}
    (hQ : RationalMap.transformPrimeDivisor (X := S') p.toRationalMap Q = some P) :
    p Q.genericPoint = P.genericPoint := by
  obtain ⟨hYv, -, -⟩ := hp.isNormalVariety hS
  have : IsIntegral S' := hYv.1.toIsIntegral
  have := isSeparated_toTerminal hS
  exact (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff p Q P).1 hQ

/-- If the transform of a prime divisor `Q` under a resolution is the prime divisor `P`, the
coefficient of `P` in the transform of `D` is the coefficient of `Q` in `D`. -/
private theorem transformDivisor_apply_of_transformPrimeDivisor_eq_some
    (hS : IsNormalVariety k sS) {p : S' ⟶ S} (hp : IsSmoothResolution sS p)
    {Q : MMP.Mori.PrimeDivisor S'} {P : MMP.Mori.PrimeDivisor S}
    (hQ : RationalMap.transformPrimeDivisor (X := S') p.toRationalMap Q = some P)
    (D : QDivisor S') : RationalMap.transformDivisor (X := S') p.toRationalMap D P = D Q := by
  obtain ⟨hYv, -, -⟩ := hp.isNormalVariety hS
  have : IsProper p := hp.isProper
  have : IsIntegral S' := hYv.1.toIsIntegral
  have := isSeparated_toTerminal hS
  obtain ⟨E, hE, -, htr⟩ := MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply
    hS hYv hp.isBirationalMorphism P
  have hEQ : E = Q := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (eq_of_map_eq_genericPoint hS hp P hE
      (map_genericPoint_of_transformPrimeDivisor_eq_some hS hp hQ))
  rw [htr, hEQ]

/-- The image of the generic point of an exceptional prime divisor of a resolution of a normal
surface is a closed point. -/
private theorem isClosed_map_genericPoint_of_transformPrimeDivisor_eq_none
    (hS : IsNormalVariety k sS) (hSdim : topologicalKrullDim S = 2) {p : S' ⟶ S}
    (hp : IsSmoothResolution sS p) (Q : MMP.Mori.PrimeDivisor S')
    (hQ : RationalMap.transformPrimeDivisor (X := S') p.toRationalMap Q = none) :
    IsClosed ({p Q.genericPoint} : Set S) := by
  obtain ⟨hYv, hdim', hbir⟩ := hp.isNormalVariety hS
  have : IsIntegral S := hS.1.toIsIntegral
  have : IsIntegral S' := hYv.1.toIsIntegral
  have : IsProper p := hp.isProper
  have : LocallyOfFiniteType sS := hS.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (p ≫ sS) := hYv.1.toLocallyOfFiniteType
  have : QuasiCompact (p ≫ sS) := hYv.1.toQuasiCompact
  have : CompactSpace S' := QuasiCompact.compactSpace_of_compactSpace (p ≫ sS)
  have : IsNoetherian S' := ⟨⟩
  have := isSeparated_toTerminal hS
  by_contra hx
  have hmem := mem_biregularLocus_of_not_isClosed p hbir (hdim'.trans hSdim).le hx
  have hiso := MMP.Threefold.Resolution.isIso_stalkMap_of_mem_biregularLocus p hmem
  have hco : Order.coheight (p Q.genericPoint) = 1 := by
    have h1 : ringKrullDim (S'.presheaf.stalk Q.genericPoint) =
        ringKrullDim (S.presheaf.stalk (p Q.genericPoint)) :=
      (ringKrullDim_eq_of_ringEquiv
        (asIso (p.stalkMap Q.genericPoint)).commRingCatIsoToRingEquiv).symm
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight,
      Q.coheight_genericPoint] at h1
    exact_mod_cast h1.symm
  have hE := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco
  have := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff p Q
    (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco)).2 hE.symm
  rw [hQ] at this
  cases this

/-- A prime divisor of the resolution of a normal surface whose transform is not a prime divisor
is a proper curve contracted by the resolution. -/
private theorem exists_properCurve_of_transformPrimeDivisor_eq_none
    (hS : IsNormalVariety k sS) (hSdim : topologicalKrullDim S = 2) {p : S' ⟶ S}
    (hp : IsSmoothResolution sS p) (Q : MMP.Mori.PrimeDivisor S')
    (hQ : RationalMap.transformPrimeDivisor (X := S') p.toRationalMap Q = none) :
    ∃ F : ProperCurve (p ≫ sS), F.point = Q.genericPoint ∧ F.IsContractedBy p := by
  obtain ⟨hYv, hdim', -⟩ := hp.isNormalVariety hS
  have : IsIntegral S := hS.1.toIsIntegral
  have : IsIntegral S' := hYv.1.toIsIntegral
  have : IsProper p := hp.isProper
  have : LocallyOfFiniteType sS := hS.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (p ≫ sS) := hYv.1.toLocallyOfFiniteType
  have : QuasiCompact (p ≫ sS) := hYv.1.toQuasiCompact
  have : CompactSpace S' := QuasiCompact.compactSpace_of_compactSpace (p ≫ sS)
  have : IsNoetherian S' := ⟨⟩
  have := isSeparated_toTerminal hS
  have hdS' : topologicalKrullDim S' = 2 := hdim'.trans hSdim
  have hx := isClosed_map_genericPoint_of_transformPrimeDivisor_eq_none hS hSdim hp Q hQ
  have hcon : ∀ y ∈ closure ({Q.genericPoint} : Set S'), p y = p Q.genericPoint := by
    intro y hy
    have h := specializes_iff_mem_closure.mp
      ((specializes_iff_mem_closure.mpr hy).map p.continuous)
    rw [hx.closure_eq] at h
    exact h
  have hdimQ : topologicalKrullDim (curveSubschemeAt Q.genericPoint) = 1 := by
    have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (p ≫ sS)
      Q.genericPoint
    rw [Q.coheight_genericPoint, hdS'] at h
    change topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal _).subscheme = 1
    rw [topologicalKrullDim_subscheme_eq, Scheme.IdealSheafData.coe_support_vanishingIdeal,
      Closeds.coe_closure]
    exact ENat.WithBot.add_one_cancel.mp (h.trans one_add_one_eq_two.symm)
  have hprop : IsProper (curveSubschemeAtι Q.genericPoint ≫ p ≫ sS) := by
    have : IsIntegral (curveSubschemeAt Q.genericPoint) :=
      Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure Q.genericPoint
    have h := isProper_comp_of_range_subset_singleton sS (curveSubschemeAtι Q.genericPoint ≫ p) hx
      (by
        rintro _ ⟨z, rfl⟩
        have hz : curveSubschemeAtι Q.genericPoint z ∈ closure ({Q.genericPoint} : Set S') :=
          range_curveSubschemeAtι Q.genericPoint ▸ ⟨z, rfl⟩
        exact hcon _ hz)
    rwa [Category.assoc] at h
  exact ⟨⟨Q.genericPoint, hdimQ, hprop⟩, rfl, hcon⟩

/-- A finite set `T` of `p`-exceptional prime divisors is listed injectively by some `F`, with
proper curves `K a` at the generic points of `F a` contracted by `p`. -/
private theorem exists_properCurves_of_transformPrimeDivisor_eq_none
    (hS : IsNormalVariety k sS) (hSdim : topologicalKrullDim S = 2) {p : S' ⟶ S}
    (hp : IsSmoothResolution sS p) (T : Finset (MMP.Mori.PrimeDivisor S'))
    (hT : ∀ Q ∈ T, RationalMap.transformPrimeDivisor (X := S') p.toRationalMap Q = none) :
    ∃ (F : Fin T.card → MMP.Mori.PrimeDivisor S') (K : Fin T.card → ProperCurve (p ≫ sS)),
      Function.Injective F ∧ (∀ a, F a ∈ T) ∧ (∀ Q ∈ T, ∃ a, F a = Q) ∧
        (∀ a, (K a).point = (F a).genericPoint) ∧ ∀ a, (K a).IsContractedBy p := by
  let e : Fin T.card ≃ T := T.equivFin.symm
  choose K hK hKc using fun a =>
    exists_properCurve_of_transformPrimeDivisor_eq_none hS hSdim hp (e a).1 (hT _ (e a).2)
  exact ⟨fun a => (e a).1, K, fun a b h => e.injective (Subtype.ext h), fun a => (e a).2,
    fun Q hQ => ⟨e.symm ⟨Q, hQ⟩, by simp⟩, hK, hKc⟩

/-- **Uniqueness of the numerical pull-back.** On a resolution `p : S' ⟶ S` of a normal surface,
a `ℚ`-divisor `D` with `p_* D = 0` and `(D · F) = 0` for every curve `F` contracted by `p` is
zero. -/
private theorem eq_zero_of_transformDivisor_eq_zero (hS : IsNormalVariety k sS)
    (hSdim : topologicalKrullDim S = 2) {p : S' ⟶ S} (hp : IsSmoothResolution sS p)
    [QuasiCompact (p ≫ sS)] (D : QDivisor S')
    (hD : RationalMap.transformDivisor (X := S') p.toRationalMap D = 0)
    (horth : ∀ F : ProperCurve (p ≫ sS), F.IsContractedBy p →
      D.intersectionNumber k (p ≫ sS) F.ι F.dim_le
        (MMP.Fourfold.isQCartier_of_isSmoothScheme hp.isSmoothScheme D) = 0) : D = 0 := by
  classical
  obtain ⟨hYv, hdim', -⟩ := hp.isNormalVariety hS
  have : IsProper p := hp.isProper
  have hq := MMP.Fourfold.isQCartier_of_isSmoothScheme hp.isSmoothScheme
  have hexc : ∀ Q ∈ D.support,
      RationalMap.transformPrimeDivisor (X := S') p.toRationalMap Q = none := by
    intro Q hQ
    rcases h : RationalMap.transformPrimeDivisor (X := S') p.toRationalMap Q with _ | P
    · rfl
    · exfalso
      have := transformDivisor_apply_of_transformPrimeDivisor_eq_some hS hp h D
      rw [hD, Finsupp.zero_apply] at this
      exact (Finsupp.mem_support_iff.1 hQ) this.symm
  obtain ⟨F, K, hF, -, hTF, hK, hKc⟩ :=
    exists_properCurves_of_transformPrimeDivisor_eq_none hS hSdim hp D.support hexc
  have hN := MMP.Threefold.Resolution.posDef_neg_intersectionMatrix_of_isBirationalMorphism
    hYv.1 hp.isSmoothScheme (hdim'.trans hSdim) hS.1 rfl hp.isBirationalMorphism F hF K hK hKc
  have hsupp : ∀ Q, D Q ≠ 0 → ∃ a, F a = Q := fun Q hQ =>
    hTF Q (Finsupp.mem_support_iff.2 hQ)
  have hx := eq_zero_of_posDef_neg hN (x := fun a => D (F a)) fun b => by
    rw [← intersectionNumber_eq_sum_coeff_mul (p ≫ sS) (K b).ι (K b).dim_le hq D F hF hsupp]
    exact horth (K b) (hKc b)
  refine Finsupp.ext fun Q => by_contra fun hQ => ?_
  obtain ⟨a, rfl⟩ := hsupp Q hQ
  exact hQ (congrFun hx a)

/-- A component `Q'` of a `ℚ`-divisor with transform `P i` is exceptional unless it is one of the
strict transforms `Q j` of the `P j`. -/
private theorem transformPrimeDivisor_eq_none_of_ne_zero (hS : IsNormalVariety k sS)
    {p : S' ⟶ S} (hp : IsSmoothResolution sS p) {r : ℕ} (P : Fin r → MMP.Mori.PrimeDivisor S)
    (Q : Fin r → MMP.Mori.PrimeDivisor S') (hQp : ∀ i, p (Q i).genericPoint = (P i).genericPoint)
    {D : QDivisor S'} {i : Fin r}
    (hD : RationalMap.transformDivisor (X := S') p.toRationalMap D = Finsupp.single (P i) 1)
    {Q' : MMP.Mori.PrimeDivisor S'} (hne : D Q' ≠ 0) (hnot : Q' ∉ Set.range Q) :
    RationalMap.transformPrimeDivisor (X := S') p.toRationalMap Q' = none := by
  classical
  rcases h : RationalMap.transformPrimeDivisor (X := S') p.toRationalMap Q' with _ | P'
  · rfl
  · exfalso
    have h1 := transformDivisor_apply_of_transformPrimeDivisor_eq_some hS hp h D
    rw [hD, Finsupp.single_apply] at h1
    split_ifs at h1 with hP'
    · subst hP'
      exact hnot ⟨i, AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        (eq_of_map_eq_genericPoint hS hp (P i) (hQp i)
          (map_genericPoint_of_transformPrimeDivisor_eq_some hS hp h))⟩
    · exact hne h1.symm

omit [IsLocallyNoetherian S] [IsNormal S] [IsLocallyNoetherian S'] [IsNormal S'] in
/-- A curve lying over a curve contracted by `g` is contracted by `p ≫ g`. -/
private theorem isContractedBy_comp_of_map_point {T : Scheme.{v}} {sS' : S' ⟶ Spec (.of k)}
    {p : S' ⟶ S} {g : S ⟶ T} {F : ProperCurve sS'} {C : ProperCurve sS}
    (hF : p F.point = C.point) (hC : C.IsContractedBy g) : F.IsContractedBy (p ≫ g) := by
  intro y hy
  have h1 : p y ∈ closure {C.point} := by
    rw [← hF]
    exact specializes_iff_mem_closure.mp ((specializes_iff_mem_closure.mpr hy).map p.continuous)
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hC _ h1, hF]

omit [IsLocallyNoetherian S] [IsNormal S] [IsLocallyNoetherian S'] [IsNormal S'] in
/-- A curve contracted by `p` is contracted by `p ≫ g`. -/
private theorem isContractedBy_comp {T : Scheme.{v}} {sS' : S' ⟶ Spec (.of k)} {p : S' ⟶ S}
    {g : S ⟶ T} {F : ProperCurve sS'} (hF : F.IsContractedBy p) : F.IsContractedBy (p ≫ g) :=
  fun y hy => by rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hF y hy]

omit [IsLocallyNoetherian S'] [IsNormal S'] in
/-- A resolution of a normal variety followed by a proper birational morphism of normal varieties
is a birational morphism. -/
private theorem isBirationalMorphism_comp_of_isSmoothResolution {T : Scheme.{v}}
    {sT : T ⟶ Spec (.of k)} (hS : IsNormalVariety k sS) (hT : IsNormalVariety k sT)
    {p : S' ⟶ S} (hp : IsSmoothResolution sS p) (g : S ⟶ T) [IsProper g]
    (hgb : IsBirationalMorphism g) : IsBirationalMorphism (p ≫ g) := by
  obtain ⟨hYv, -, hbir⟩ := hp.isNormalVariety hS
  have : IsProper p := hp.isProper
  have : IsIntegral S := hS.1.toIsIntegral
  have : IsIntegral S' := hYv.1.toIsIntegral
  have : IsIntegral T := hT.1.toIsIntegral
  have : IsNormal T := hT.2
  have : LocallyOfFiniteType sT := hT.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
  exact isBirationalMorphism_comp_of_isBirational g p
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hgb) hbir

/-- Mumford's matrix `(Êᵢ · C'ⱼ)` is negative definite if the curves `C'ⱼ`, completed by curves
`Kₐ` orthogonal to the `Êᵢ`, have a negative definite intersection matrix with prime divisors
`Qⱼ, Fₐ` carrying the components of the `Êᵢ`, and `Êᵢ(Qⱼ) = δᵢⱼ`. -/
private theorem posDef_neg_intersectionMatrix_of_append {sX : S' ⟶ Spec (.of k)}
    [QuasiCompact sX] (hq : ∀ D : QDivisor S', D.IsQCartier) {r m : ℕ}
    (Q : Fin r → MMP.Mori.PrimeDivisor S') (F : Fin m → MMP.Mori.PrimeDivisor S')
    (C' : Fin r → ProperCurve sX) (K : Fin m → ProperCurve sX)
    (hinj : Function.Injective (Fin.append Q F))
    (hN : (-(Matrix.of fun α β : Fin (r + m) =>
      ((Divisor.toQDivisor (Finsupp.single (Fin.append Q F α) 1)).intersectionNumber k sX
        (Fin.append C' K β).ι (Fin.append C' K β).dim_le (hq _) : ℝ))).PosDef)
    (Ê : Fin r → QDivisor S') (hcoef : ∀ i j, Ê i (Q j) = if i = j then 1 else 0)
    (hsupp : ∀ i Q', Ê i Q' ≠ 0 → Q' ∈ Set.range Q ∨ Q' ∈ Set.range F)
    (horth : ∀ i a, (Ê i).intersectionNumber k sX (K a).ι (K a).dim_le (hq _) = 0) :
    (-(Matrix.of fun i j : Fin r =>
      ((Ê i).intersectionNumber k sX (C' j).ι (C' j).dim_le (hq _) : ℝ))).PosDef := by
  classical
  have hcurve : ∀ i (G H : ProperCurve sX), G = H →
      (Ê i).intersectionNumber k sX G.ι G.dim_le (hq _) =
        (Ê i).intersectionNumber k sX H.ι H.dim_le (hq _) := by
    rintro i G _ rfl
    rfl
  refine posDef_neg_of_posDef_neg_append hN (fun i α => (Ê i (Fin.append Q F α) : ℝ))
    (fun i β => ((Ê i).intersectionNumber k sX (Fin.append C' K β).ι
      (Fin.append C' K β).dim_le (hq _) : ℝ)) (fun i β => ?_)
    (fun i j => by simp [hcoef, apply_ite (fun q : ℚ => (q : ℝ))])
    (fun i a => by exact_mod_cast (hcurve i _ _ (Fin.append_right C' K a)).trans (horth i a))
    fun i j => by exact_mod_cast hcurve i _ _ (Fin.append_left C' K j)
  have hcov : ∀ Q', Ê i Q' ≠ 0 → ∃ α, Fin.append Q F α = Q' := fun Q' hQ' => by
    rcases hsupp i Q' hQ' with ⟨j, rfl⟩ | ⟨a, rfl⟩
    · exact ⟨Fin.castAdd m j, Fin.append_left Q F j⟩
    · exact ⟨Fin.natAdd r a, Fin.append_right Q F a⟩
  simp only [Matrix.of_apply, intersectionNumber_eq_sum_coeff_mul sX (Fin.append C' K β).ι
    (Fin.append C' K β).dim_le hq (Ê i) _ hinj hcov, Rat.cast_sum, Rat.cast_mul]

/-- **Negative definiteness of Mumford's matrix.** For curves `Cᵢ` contracted by `g` with strict
transforms `C'ᵢ` and numerical pull-backs `Êᵢ` on a resolution, `-(Êᵢ · C'ⱼ)` is positive
definite. -/
private theorem posDef_neg_mumfordIntersectionMatrix {T : Scheme.{v}} {sT : T ⟶ Spec (.of k)}
    (hS : IsNormalVariety k sS) (hT : IsNormalVariety k sT)
    (hSdim : topologicalKrullDim S = 2)
    (g : S ⟶ T) (hg : g ≫ sT = sS) [IsProper g] (hgb : IsBirationalMorphism g)
    {r : ℕ} (P : Fin r → MMP.Mori.PrimeDivisor S) (hP : Function.Injective P)
    (C : Fin r → ProperCurve sS) (hC : ∀ i, (C i).point = (P i).genericPoint)
    (hexc : ∀ i, (C i).IsContractedBy g)
    {p : S' ⟶ S} (hp : IsSmoothResolution sS p) [QuasiCompact (p ≫ sS)]
    (C' : Fin r → ProperCurve (p ≫ sS)) (hC' : ∀ i, p (C' i).point = (P i).genericPoint)
    (Ê : Fin r → QDivisor S')
    (hÊ : ∀ i, RationalMap.transformDivisor (X := S') p.toRationalMap (Ê i) =
      Finsupp.single (P i) 1)
    (hÊorth : ∀ i (F : ProperCurve (p ≫ sS)), F.IsContractedBy p →
      (Ê i).intersectionNumber k (p ≫ sS) F.ι F.dim_le
        (MMP.Fourfold.isQCartier_of_isSmoothScheme hp.isSmoothScheme (Ê i)) = 0) :
    (-(Matrix.of fun i j : Fin r =>
      ((Ê i).intersectionNumber k (p ≫ sS) (C' j).ι (C' j).dim_le
        (MMP.Fourfold.isQCartier_of_isSmoothScheme hp.isSmoothScheme (Ê i)) : ℝ))).PosDef := by
  classical
  obtain ⟨hYv, hdim', -⟩ := hp.isNormalVariety hS
  have : IsProper p := hp.isProper
  have hq := MMP.Fourfold.isQCartier_of_isSmoothScheme hp.isSmoothScheme
  choose Q hQp _ hQtr using fun i =>
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply
      hS hYv hp.isBirationalMorphism (P i)
  have hC'Q : ∀ i, (C' i).point = (Q i).genericPoint := fun i =>
    eq_of_map_eq_genericPoint hS hp (P i) (hC' i) (hQp i)
  have hQinj : Function.Injective Q := fun i j h => hP
    (AlgebraicGeometry.PrimeDivisor.genericPoint_injective ((hQp i).symm.trans (h ▸ hQp j)))
  have hcoefQ : ∀ i j, Ê i (Q j) = if i = j then 1 else 0 := by
    intro i j
    rw [← hQtr j, hÊ i, Finsupp.single_apply]
    exact if_congr hP.eq_iff rfl rfl
  let Tex : Finset (MMP.Mori.PrimeDivisor S') :=
    (Finset.univ.biUnion fun i => (Ê i).support).filter (· ∉ Set.range Q)
  have hTex : ∀ Q' ∈ Tex,
      RationalMap.transformPrimeDivisor (X := S') p.toRationalMap Q' = none := by
    intro Q' hQ'
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hQ'
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 h1
    exact transformPrimeDivisor_eq_none_of_ne_zero hS hp P Q hQp (hÊ i)
      (Finsupp.mem_support_iff.1 hi) h2
  obtain ⟨F, K, hF, hFT, hTF, hK, hKc⟩ :=
    exists_properCurves_of_transformPrimeDivisor_eq_none hS hSdim hp Tex hTex
  let R : Fin (r + Tex.card) → MMP.Mori.PrimeDivisor S' := Fin.append Q F
  let L : Fin (r + Tex.card) → ProperCurve (p ≫ sS) := Fin.append C' K
  have hRinj : Function.Injective R := Fin.append_injective_iff.2
    ⟨hQinj, hF, fun i a h => (Finset.mem_filter.1 (hFT a)).2 ⟨i, h⟩⟩
  have hL : ∀ α, (L α).point = (R α).genericPoint := Fin.addCases
    (fun i => by simpa only [L, R, Fin.append_left] using hC'Q i)
    fun a => by simpa only [L, R, Fin.append_right] using hK a
  have hLc : ∀ α, (L α).IsContractedBy (p ≫ g) := Fin.addCases
    (fun i => by simpa only [L, Fin.append_left] using
      isContractedBy_comp_of_map_point ((hC' i).trans (hC i).symm) (hexc i))
    fun a => by simpa only [L, Fin.append_right] using isContractedBy_comp (hKc a)
  have hN := MMP.Threefold.Resolution.posDef_neg_intersectionMatrix_of_isBirationalMorphism
    hYv.1 hp.isSmoothScheme (hdim'.trans hSdim) hT.1
    (show (p ≫ g) ≫ sT = p ≫ sS by rw [Category.assoc, hg])
    (isBirationalMorphism_comp_of_isSmoothResolution hS hT hp g hgb) R hRinj L hL hLc
  exact posDef_neg_intersectionMatrix_of_append hq Q F C' K hRinj hN Ê hcoefQ
    (fun i Q' hQ' => or_iff_not_imp_left.2 fun h => hTF Q' (Finset.mem_filter.2
      ⟨Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finsupp.mem_support_iff.2 hQ'⟩, h⟩))
    fun i a => hÊorth i (K a) (hKc a)

omit [IsLocallyNoetherian S] [IsNormal S] [IsLocallyNoetherian S'] [IsNormal S'] in
/-- The image of a curve contracted by `p` is a point. -/
private theorem exists_range_eq_singleton_of_isContractedBy {sS' : S' ⟶ Spec (.of k)}
    {p : S' ⟶ S} {F : ProperCurve sS'} (hF : F.IsContractedBy p) :
    ∃ w : S, Set.range (F.ι ≫ p) = {w} := by
  have := F.isCurve
  refine ⟨p F.point, Set.ext fun z => ⟨?_, ?_⟩⟩
  · rintro ⟨c, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hF _ (F.range_ι ▸ ⟨c, rfl⟩)
  · rintro rfl
    exact ⟨genericPoint F.scheme, by rw [Scheme.Hom.comp_apply, F.ι_genericPoint]⟩

/-- Two `ℚ`-divisors on a resolution of a normal surface with the same transform and the same
intersection numbers with the curves contracted by `p` are equal. -/
private theorem eq_of_transformDivisor_eq (hS : IsNormalVariety k sS)
    (hSdim : topologicalKrullDim S = 2) {p : S' ⟶ S} (hp : IsSmoothResolution sS p)
    [QuasiCompact (p ≫ sS)] {D D' : QDivisor S'}
    (htr : RationalMap.transformDivisor (X := S') p.toRationalMap D =
      RationalMap.transformDivisor (X := S') p.toRationalMap D')
    (horth : ∀ F : ProperCurve (p ≫ sS), F.IsContractedBy p →
      D.intersectionNumber k (p ≫ sS) F.ι F.dim_le
          (MMP.Fourfold.isQCartier_of_isSmoothScheme hp.isSmoothScheme D) =
        D'.intersectionNumber k (p ≫ sS) F.ι F.dim_le
          (MMP.Fourfold.isQCartier_of_isSmoothScheme hp.isSmoothScheme D')) : D = D' := by
  have hq := MMP.Fourfold.isQCartier_of_isSmoothScheme hp.isSmoothScheme
  refine sub_eq_zero.1 (eq_zero_of_transformDivisor_eq_zero hS hSdim hp (D - D')
    (by rw [map_sub, htr, sub_self]) fun F hF => ?_)
  rw [MMP.Fourfold.intersectionNumber_congr (p ≫ sS) F.ι F.dim_le (hq _) (hq _)
      (sub_eq_add_neg D D'),
    QDivisor.intersectionNumber_add' k (p ≫ sS) F.ι F.dim_le _ _ (hq _) (hq _),
    MMP.Fourfold.intersectionNumber_congr (p ≫ sS) F.ι F.dim_le (hq _) (hq _)
      (neg_one_smul ℚ D').symm,
    QDivisor.intersectionNumber_smul k (p ≫ sS) F.ι F.dim_le (-1) D' (hq _), horth F hF]
  ring

omit [IsLocallyNoetherian S] [IsNormal S] [IsLocallyNoetherian S'] [IsNormal S'] in
/-- The residue degree of `p` at the generic point of a curve `C'` is the degree of `C'`
over its image. -/
private theorem residueFieldDegree_eq_degreeOver_toImage
    {p : S' ⟶ S} [QuasiCompact (p ≫ sS)]
    (C' : ProperCurve (p ≫ sS)) [hφ : IsProper (C'.ι ≫ p)] :
    residueFieldDegree p C'.point = degreeOver (C'.ι ≫ p).toImage := by
  have h1 := residueDegree_comp C'.ι p (genericPoint C'.scheme)
  rw [C'.ι_genericPoint, Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion C'.ι, mul_one]
    at h1
  have h2 := residueDegree_comp (C'.ι ≫ p).toImage (C'.ι ≫ p).imageι (genericPoint C'.scheme)
  rw [Scheme.Hom.toImage_imageι,
    Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion (C'.ι ≫ p).imageι,
    one_mul, residueDegree_genericPoint_eq_degreeOver (C'.ι ≫ p).toImage] at h2
  exact h1.symm.trans h2

/-- **Mumford's product extends the ordinary intersection number.** If the prime divisor `P` of
the normal surface `S` is `ℚ`-Cartier and `Ê` is its numerical pull-back to a resolution `p`,
then `(P · C) = (Ê · C')` for a curve `C` of `S` with strict transform `C'`. -/
private theorem intersectionNumber_eq_of_isQCartier (hS : IsNormalVariety k sS)
    (hSdim : topologicalKrullDim S = 2) [QuasiCompact sS] {p : S' ⟶ S}
    (hp : IsSmoothResolution sS p) [QuasiCompact (p ≫ sS)] (P : MMP.Mori.PrimeDivisor S)
    (hP : (Divisor.toQDivisor (Finsupp.single P 1)).IsQCartier)
    (P' : MMP.Mori.PrimeDivisor S) (C : ProperCurve sS) (hCP' : C.point = P'.genericPoint)
    (C' : ProperCurve (p ≫ sS)) (hC : p C'.point = C.point) (Ê : QDivisor S')
    (hÊ : RationalMap.transformDivisor (X := S') p.toRationalMap Ê = Finsupp.single P 1)
    (hÊorth : ∀ F : ProperCurve (p ≫ sS), F.IsContractedBy p →
      Ê.intersectionNumber k (p ≫ sS) F.ι F.dim_le
        (MMP.Fourfold.isQCartier_of_isSmoothScheme hp.isSmoothScheme Ê) = 0) :
    (Divisor.toQDivisor (Finsupp.single P 1)).intersectionNumber k sS C.ι C.dim_le hP =
      Ê.intersectionNumber k (p ≫ sS) C'.ι C'.dim_le
        (MMP.Fourfold.isQCartier_of_isSmoothScheme hp.isSmoothScheme Ê) := by
  obtain ⟨hYv, -, -⟩ := hp.isNormalVariety hS
  have hq := MMP.Fourfold.isQCartier_of_isSmoothScheme hp.isSmoothScheme
  have : IsProper p := hp.isProper
  have : IsIntegral S := hS.1.toIsIntegral
  have : IsIntegral S' := hYv.1.toIsIntegral
  have : CompactSpace S' := QuasiCompact.compactSpace_of_compactSpace (p ≫ sS)
  have : IsDominant p := hp.isBirationalMorphism.isDominant
  have := hS.1
  have := hYv.1
  set E := Divisor.toQDivisor (Finsupp.single P 1)
  have hB : ∀ Z : irreducibleComponents S', p (componentGenericPoint S' Z) ∉ E.supp :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' p E
  set B := QDivisor.pullback (f := p) E hP hB
  have hBp : E.IsPullback p hB B := QDivisor.isPullback_pullback hP hB
  have htr := MMP.Positivity.transformDivisor_of_isPullback hS hYv hp.isBirationalMorphism hP hB hBp
  have horthB : ∀ F : ProperCurve (p ≫ sS), F.IsContractedBy p →
      B.intersectionNumber k (p ≫ sS) F.ι F.dim_le (hq B) = 0 := fun F hF => by
    have := F.isCurve
    exact intersectionNumber_pullback_eq_zero k (p ≫ sS) sS p rfl F.ι hP hBp
      (exists_range_eq_singleton_of_isContractedBy hF)
  have hEsingle : E = Finsupp.single P 1 :=
    (MMP.Threefold.Resolution.toQDivisor_single P 1).trans (by rw [Int.cast_one])
  have hEq : Ê = B := eq_of_transformDivisor_eq hS hSdim hp (by rw [hÊ, htr, hEsingle])
    fun F hF => by rw [hÊorth F hF, horthB F hF]
  rw [MMP.Fourfold.intersectionNumber_congr (p ≫ sS) C'.ι C'.dim_le (hq _) (hq _) hEq]
  have := P'.isDiscreteValuationRing_localRing
  have : ValuationRing (S.presheaf.stalk (p C'.point)) := by
    rw [hC, hCP']
    infer_instance
  have hres := MMP.Flips.residueFieldDegree_eq_one_of_isIso_stalkMap p C'.point
    (MMP.Positivity.isIso_stalkMap_of_valuationRing p
      hp.isBirationalMorphism.functionFieldMap_bijective C'.point)
  set φ := C'.ι ≫ p with hφdef
  have : IsProper (φ ≫ sS) := by
    rw [hφdef, Category.assoc]
    infer_instance
  have : IsProper φ := IsProper.of_comp _ sS
  have hdeg : residueFieldDegree p C'.point = degreeOver φ.toImage :=
    residueFieldDegree_eq_degreeOver_toImage C' (hφ := ‹_›)
  have hI : φ.ker = Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {C.point}) := by
    rw [hφdef, C'.ker_comp p, hC]
  have htransport : ∀ I J : S.IdealSheafData, I = J →
      AlgebraicGeometry.IsCurve k (J.subschemeι ≫ sS) →
        AlgebraicGeometry.IsCurve k (I.subschemeι ≫ sS) := fun _ _ h => h ▸ id
  have hcurve : AlgebraicGeometry.IsCurve k (φ.imageι ≫ sS) := htransport _ _ hI C.isCurve
  have := C'.isCurve
  refine Eq.trans ?_ (intersectionNumber_pullback_eq_degreeOver_mul k (p ≫ sS) sS p rfl C'.ι hP
    hBp hcurve).symm
  rw [← hdeg, hres, Nat.cast_one, one_mul]
  have : IsProper (φ.imageι ≫ sS) := isProper_imageι_comp φ sS
  exact intersectionNumber_subschemeι_congr sS hI.symm _ _ E hP

end Geometry

end MMP.Proof_lem_mmp_surface_normal_exceptional_negative_definite

namespace MMP.Mori

open MMP.Proof_lem_mmp_surface_normal_exceptional_negative_definite

/-- **Mumford's intersection matrix of curves contracted on a normal surface is negative
definite.** Let `g : S ⟶ T` be a proper birational morphism of normal quasi-projective surfaces
over `k`, and `E₁, …, E_r` distinct irreducible curves on `S` contracted by `g` (prime divisors
`Pᵢ` with proper curves `Cᵢ` having the same generic points). Let `p : S' ⟶ S` be a resolution,
`C'ᵢ` the strict transform of `Eᵢ`, and `Êᵢ` the numerical pull-back of `Eᵢ`: the `ℚ`-divisor on
`S'` with `p_* Êᵢ = Eᵢ` and `(Êᵢ · F) = 0` for every curve `F` contracted by `p`. Then the
matrix of Mumford products `(Êᵢ · C'ⱼ)` is negative definite, and when `Eᵢ` is `ℚ`-Cartier its
Mumford product with `Eⱼ` is the intersection number `(Eᵢ · Cⱼ)` on `S`. -/
@[mmp "lem_mmp_surface_normal_exceptional_negative_definite"]
public theorem posDef_neg_mumfordIntersectionMatrix_of_isBirationalMorphism
    {k : Type u} [Field k] {S T : Scheme.{u}} {sS : S ⟶ Spec (.of k)} {sT : T ⟶ Spec (.of k)}
    [IsLocallyNoetherian S] [IsNormal S] [QuasiCompact sS]
    (hS : IsNormalVariety k sS) (hT : IsNormalVariety k sT)
    (hSq : IsQuasiProjectiveVariety k sS) (hTq : IsQuasiProjectiveVariety k sT)
    (hSdim : topologicalKrullDim S = 2) (hTdim : topologicalKrullDim T = 2)
    (g : S ⟶ T) (hg : g ≫ sT = sS) [IsProper g] (hgb : IsBirationalMorphism g)
    {r : ℕ} (P : Fin r → PrimeDivisor S) (hP : Function.Injective P)
    (C : Fin r → ProperCurve sS) (hC : ∀ i, (C i).point = (P i).genericPoint)
    (hexc : ∀ i, (C i).IsContractedBy g)
    {S' : Scheme.{u}} {p : S' ⟶ S} (hp : IsSmoothResolution sS p)
    [IsLocallyNoetherian S'] [IsNormal S'] [QuasiCompact (p ≫ sS)]
    (C' : Fin r → ProperCurve (p ≫ sS)) (hC' : ∀ i, p (C' i).point = (P i).genericPoint)
    (Ê : Fin r → QDivisor S')
    (hÊ : ∀ i, RationalMap.transformDivisor (X := S') p.toRationalMap (Ê i) =
      Finsupp.single (P i) 1)
    (hÊorth : ∀ i (F : ProperCurve (p ≫ sS)), F.IsContractedBy p →
      (Ê i).intersectionNumber k (p ≫ sS) F.ι F.dim_le
        (MMP.Fourfold.isQCartier_of_isSmoothScheme hp.isSmoothScheme (Ê i)) = 0) :
    (-(Matrix.of fun i j : Fin r =>
      ((Ê i).intersectionNumber k (p ≫ sS) (C' j).ι (C' j).dim_le
        (MMP.Fourfold.isQCartier_of_isSmoothScheme hp.isSmoothScheme (Ê i)) : ℝ))).PosDef ∧
    ∀ (i : Fin r) (hi : (Divisor.toQDivisor (Finsupp.single (P i) 1)).IsQCartier) (j : Fin r),
      (Divisor.toQDivisor (Finsupp.single (P i) 1)).intersectionNumber k sS (C j).ι
          (C j).dim_le hi =
        (Ê i).intersectionNumber k (p ≫ sS) (C' j).ι (C' j).dim_le
          (MMP.Fourfold.isQCartier_of_isSmoothScheme hp.isSmoothScheme (Ê i)) :=
  ⟨posDef_neg_mumfordIntersectionMatrix hS hT hSdim g hg hgb P hP C hC hexc hp C' hC' Ê hÊ hÊorth,
    fun i hi j => intersectionNumber_eq_of_isQCartier hS hSdim hp (P i) hi (P j) (C j) (hC j)
      (C' j) ((hC' j).trans (hC j).symm) (Ê i) (hÊ i) (hÊorth i)⟩

end MMP.Mori
