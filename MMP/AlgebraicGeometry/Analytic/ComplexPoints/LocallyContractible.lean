module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ClassicalTopologyPullback
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.RegularPointEuclideanChart
public import MMP.AlgebraicGeometry.Semialgebraic.TriangulationProof
/-!
# Topology of the underlying space of a complex scheme

Let `X` be a scheme locally of finite type over `ℂ` and `X(ℂ)` its underlying space with the
classical topology. Every point of `X(ℂ)` lies in `U(ℂ)` for an affine open `U ⊆ X`; `U(ℂ)` is
open in `X(ℂ)` and homeomorphic to the common zero set in `ℂⁿ` of finitely many polynomials
(the relations of a finite presentation of `Γ(U, 𝒪_X)`). Hence `X(ℂ)` is weakly locally
compact, second countable when `X` is quasi-compact, and Hausdorff when `X` is separated. A
complex scheme is closed in a non-singular, hence separated, variety, so its underlying space is
Hausdorff, locally compact and σ-compact, and gluing the closed embeddings `U(ℂ) → ℂⁿ` of a
finite affine cover by Urysohn functions gives a closed embedding of `X(ℂ)` into some `ℝᴺ`
(Fulton, §19.1).

## Main results

* `MMP.StronglyLocallyContractibleSpace.of_isOpenEmbedding_cover`: a space covered by open
  embeddings of strongly locally contractible spaces is strongly locally contractible.
* `MMP.exists_isClosedEmbedding_of_finite_cover`: a normal space covered by finitely many open
  sets, each closed-embedded in a real normed space, closed-embeds in a real normed space.
* `MMP.UnderlyingSpace.exists_isOpenEmbedding_zeroLocus`: charts of `X(ℂ)` by
  complex affine algebraic sets.
* `MMP.UnderlyingSpace.t2Space_of_isSeparated`: `X(K)` is Hausdorff for `X`
  separated over `K`.
* `MMP.IsComplexScheme.isSeparated`: a complex scheme is separated over `ℂ`.
* `MMP.UnderlyingSpace.exists_isClosedEmbedding_euclideanSpace`: the underlying
  space of a complex scheme has a closed embedding into some `ℝᴺ`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [J. Milnor, *Singular points of complex hypersurfaces*][milnor1968], §2.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Topology

namespace MMP

/-- A space in which every point lies in the image of an open embedding of a strongly locally
contractible space is strongly locally contractible. -/
theorem StronglyLocallyContractibleSpace.of_isOpenEmbedding_cover {X : Type*} [TopologicalSpace X]
    (h : ∀ x : X, ∃ (Y : Type*) (_ : TopologicalSpace Y) (_ : StronglyLocallyContractibleSpace Y)
      (e : Y → X), IsOpenEmbedding e ∧ x ∈ Set.range e) :
    StronglyLocallyContractibleSpace X := by
  refine ⟨fun x ↦ ⟨fun t ↦ ⟨fun ht ↦ ?_, fun ⟨s, ⟨hs, _⟩, hst⟩ ↦ Filter.mem_of_superset hs hst⟩⟩⟩
  obtain ⟨Y, _, _, e, he, y, rfl⟩ := h x
  rw [← he.map_nhds_eq] at ht
  obtain ⟨s, ⟨hs, hc⟩, hst⟩ := (StronglyLocallyContractibleSpace.contractible_basis y).mem_iff.mp ht
  refine ⟨e '' s, ⟨he.map_nhds_eq y ▸ Filter.image_mem_map hs, ?_⟩, Set.image_subset_iff.mpr hst⟩
  exact (he.isEmbedding.homeomorphImage s).symm.contractibleSpace

/-- **Closed embeddings glue along a finite open cover.** Let `X` be a normal space covered by
finitely many open sets `U i`, each with a closed embedding `g i : U i → E i` into a real normed
space. Then `X` has a closed embedding into `(ι → ℝ) × Π i, E i`. -/
theorem exists_isClosedEmbedding_of_finite_cover {X : Type*} [TopologicalSpace X]
    [NormalSpace X] {ι : Type*} [Finite ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcov : ⋃ i, U i = Set.univ) (g : ∀ i, U i → E i) (hg : ∀ i, IsClosedEmbedding (g i)) :
    ∃ F : X → (ι → ℝ) × (∀ i, E i), IsClosedEmbedding F := by
  have hfin : ∀ (V : ι → Set X) (x : X), {i | x ∈ V i}.Finite := fun _ _ ↦ Set.toFinite _
  obtain ⟨W, hWcov, hWo, hWU⟩ := exists_iUnion_eq_closure_subset hU (hfin U) hcov
  obtain ⟨C, hCcov, hCc, hCW⟩ := exists_iUnion_eq_closed_subset hWo (hfin W) hWcov
  have hφ : ∀ i, ∃ φ : C(X, ℝ), Set.EqOn φ 0 (W i)ᶜ ∧ Set.EqOn φ 1 (C i) ∧
      ∀ x, φ x ∈ Set.Icc (0 : ℝ) 1 := fun i ↦
    exists_continuous_zero_one_of_isClosed (hWo i).isClosed_compl (hCc i)
      (Set.disjoint_compl_left_iff_subset.mpr (hCW i))
  choose φ hφ0 hφ1 _ using hφ
  have hWU' : ∀ i, W i ⊆ U i := fun i ↦ subset_closure.trans (hWU i)
  classical
  let ψ : ∀ i, X → E i := fun i x ↦ if h : x ∈ U i then φ i x • g i ⟨x, h⟩ else 0
  have hψ0 : ∀ i x, x ∉ W i → ψ i x = 0 := fun i x hx ↦ by
    simp only [ψ]
    split_ifs
    · rw [hφ0 i hx, Pi.zero_apply, zero_smul]
    · rfl
  have hψU : ∀ i (x : U i), ψ i x = φ i x • g i x := fun i x ↦ by
    simp only [ψ, dif_pos x.2]
  have hψc : ∀ i, Continuous (ψ i) := fun i ↦ by
    refine continuous_iff_continuousAt.mpr fun x ↦ ?_
    by_cases hx : x ∈ U i
    · have hc : ContinuousOn (ψ i) (U i) := by
        rw [continuousOn_iff_continuous_restrict]
        have : (U i).domRestrict (ψ i) = fun x : U i ↦ φ i x • g i x := funext (hψU i)
        rw [this]
        exact ((φ i).continuous.comp continuous_subtype_val).smul (hg i).continuous
      exact hc.continuousAt ((hU i).mem_nhds hx)
    · have hx' : x ∈ (closure (W i))ᶜ := fun h ↦ hx (hWU i h)
      refine (continuousAt_const (y := (0 : E i))).congr (Filter.eventuallyEq_of_mem
        (isClosed_closure.isOpen_compl.mem_nhds hx') fun y hy ↦ ?_)
      exact (hψ0 i y fun h ↦ hy (subset_closure h)).symm
  let F : X → (ι → ℝ) × (∀ i, E i) := fun x ↦ (fun i ↦ φ i x, fun i ↦ ψ i x)
  have hFc : Continuous F :=
    (continuous_pi fun i ↦ (φ i).continuous).prodMk (continuous_pi fun i ↦ hψc i)
  have hmemC : ∀ x, ∃ i, x ∈ C i := fun x ↦ Set.mem_iUnion.mp (hCcov ▸ Set.mem_univ x)
  -- on `C i`, the `i`-th component of `F` is `g i`
  have hFC : ∀ i (x : U i), (x : X) ∈ C i → ψ i x = g i x := fun i x hx ↦ by
    rw [hψU, hφ1 i hx, Pi.one_apply, one_smul]
  have hinj : Function.Injective F := by
    intro x y hxy
    obtain ⟨i, hi⟩ := hmemC x
    have h1 : φ i y = 1 :=
      (congrFun (congrArg Prod.fst hxy) i).symm.trans (hφ1 i hi)
    have hyW : y ∈ W i := by
      by_contra h
      have := hφ0 i h
      simp [h1] at this
    have hxU := hWU' i (hCW i hi)
    have hyU := hWU' i hyW
    have h2 := congrFun (congrArg Prod.snd hxy) i
    change ψ i x = ψ i y at h2
    rw [hFC i ⟨x, hxU⟩ hi, hψU i ⟨y, hyU⟩] at h2
    change g i ⟨x, hxU⟩ = φ i y • g i ⟨y, hyU⟩ at h2
    rw [h1, one_smul] at h2
    exact congrArg Subtype.val ((hg i).injective h2)
  have hproper : IsProperMap F := by
    refine isProperMap_iff_isCompact_preimage.mpr ⟨hFc, fun K hK ↦ ?_⟩
    have hsplit : F ⁻¹' K = ⋃ i, (F ⁻¹' K ∩ C i) := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_inter_iff]
      exact ⟨fun hx ↦ (hmemC x).imp fun _ hi ↦ ⟨hx, hi⟩, fun ⟨_, hx, _⟩ ↦ hx⟩
    rw [hsplit]
    refine isCompact_iUnion fun i ↦ ?_
    let L : Set (E i) := (fun z : (ι → ℝ) × (∀ i, E i) ↦ z.2 i) '' K
    have hL : IsCompact L := hK.image ((continuous_apply i).comp continuous_snd)
    have hpre : IsCompact (((↑) : U i → X) '' (g i ⁻¹' L)) :=
      ((hg i).isProperMap.isCompact_preimage hL).image continuous_subtype_val
    refine hpre.of_isClosed_subset ((hK.isClosed.preimage hFc).inter (hCc i)) ?_
    rintro x ⟨hxK, hxC⟩
    have hxU := hWU' i (hCW i hxC)
    refine ⟨⟨x, hxU⟩, ?_, rfl⟩
    exact ⟨F x, hxK, hFC i ⟨x, hxU⟩ hxC⟩
  exact ⟨F, IsClosedEmbedding.of_continuous_injective_isClosedMap hFc hinj
    hproper.isClosedMap⟩

namespace UnderlyingSpace

/-- The underlying space `U(ℂ)` of an affine scheme of finite type over `ℂ` is homeomorphic to
the common zero set in `ℂⁿ` of finitely many polynomials: the relations of a finite presentation
of `Γ(U, 𝒪_U)`, read through its generators. -/
theorem exists_homeomorph_zeroLocus (U : Scheme.{0}) [U.Over (Spec (.of ℂ))] [IsAffine U]
    [LocallyOfFiniteType (U ↘ Spec (.of ℂ))] :
    ∃ (n m : ℕ) (f : Fin m → MvPolynomial (Fin n) ℂ),
      Nonempty (UnderlyingSpace ℂ U ≃ₜ {v : Fin n → ℂ | ∀ j, MvPolynomial.eval v (f j) = 0}) := by
  letI : Algebra ℂ Γ(U, ⊤) := (structureRingHom ℂ U).toAlgebra
  haveI : Algebra.FiniteType ℂ Γ(U, ⊤) := finiteType_structureRingHom
  haveI : Algebra.FinitePresentation ℂ Γ(U, ⊤) :=
    Algebra.FinitePresentation.of_finiteType.mp ‹_›
  let P := Algebra.Presentation.ofFinitePresentation ℂ Γ(U, ⊤)
  exact ⟨_, _, P.relation, ⟨(isClosedEmbedding_evalFamily_val (K := ℂ) (X := U) rfl
    P).isEmbedding.toHomeomorph.trans (Homeomorph.setCongr (range_evalFamily_val (X := U) rfl P))⟩⟩

/-- If the image of the closed point under `p` lies in the open `U`, then `p` lies in the image
of `U(K) → X(K)`. -/
lemma mem_range_map_ι {K : Type} [Field K] [TopologicalSpace K] {X : Scheme.{0}}
    [X.Over (Spec (.of K))] (U : X.Opens) (p : UnderlyingSpace K X)
    (hp : p.toHom (IsLocalRing.closedPoint K) ∈ U) :
    letI : U.toScheme.Over (Spec (.of K)) := ⟨U.ι ≫ X ↘ Spec (.of K)⟩
    haveI : U.ι.IsOver (Spec (.of K)) := ⟨rfl⟩
    p ∈ Set.range (map (K := K) U.ι) := by
  letI : U.toScheme.Over (Spec (.of K)) := ⟨U.ι ≫ X ↘ Spec (.of K)⟩
  haveI : U.ι.IsOver (Spec (.of K)) := ⟨rfl⟩
  change p ∈ Set.range (mapFun U.ι)
  rw [range_mapFun_of_isOpenImmersion, Set.mem_setOf_eq, Scheme.Opens.opensRange_ι,
    top_le_preimage_iff]
  exact hp

/-- **Algebraic charts by zero sets.** Every point of the underlying space `X(ℂ)` of a scheme
locally of finite type over `ℂ` lies in the image of an open embedding of the common zero set in
`ℂⁿ` of finitely many polynomials: the points `U(ℂ)` of an affine open `U ∋ p`. -/
theorem exists_isOpenEmbedding_zeroLocus (X : Scheme.{0}) [X.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] (p : UnderlyingSpace ℂ X) :
    ∃ (n m : ℕ) (f : Fin m → MvPolynomial (Fin n) ℂ)
      (e : {v : Fin n → ℂ | ∀ j, MvPolynomial.eval v (f j) = 0} → UnderlyingSpace ℂ X),
      IsOpenEmbedding e ∧ p ∈ Set.range e := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := p.toHom (IsLocalRing.closedPoint ℂ)) (U := ⊤) trivial
  letI : U.toScheme.Over (Spec (.of ℂ)) := ⟨U.ι ≫ X ↘ Spec (.of ℂ)⟩
  haveI : U.ι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  haveI : IsAffine U := hU
  haveI : LocallyOfFiniteType (U.toScheme ↘ Spec (.of ℂ)) := by
    change LocallyOfFiniteType (U.ι ≫ X ↘ Spec (.of ℂ))
    infer_instance
  obtain ⟨n, m, f, ⟨φ⟩⟩ := exists_homeomorph_zeroLocus U
  refine ⟨n, m, f, map U.ι ∘ φ.symm,
    (isOpenEmbedding_map_of_isOpenImmersion U.ι).comp φ.symm.isOpenEmbedding, ?_⟩
  rw [Set.range_comp, φ.symm.range_coe, Set.image_univ]
  exact mem_range_map_ι U p hxU

/-- The common zero set of a family of polynomials over a Hausdorff topological semiring `R` is
closed in `R^σ`. -/
lemma isClosed_zeroLocus {R σ κ : Type*} [CommSemiring R] [TopologicalSpace R]
    [IsTopologicalSemiring R] [T2Space R] (f : κ → MvPolynomial σ R) :
    IsClosed {v : σ → R | ∀ j, MvPolynomial.eval v (f j) = 0} := by
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun j ↦ isClosed_eq (MvPolynomial.continuous_eval (f j))
    continuous_const

/-- The underlying space `X(ℂ)` of a scheme locally of finite type over `ℂ` is weakly locally
compact: every point has a compact neighbourhood, the image of one in a zero-set chart. -/
instance weaklyLocallyCompactSpace (X : Scheme.{0}) [X.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] :
    WeaklyLocallyCompactSpace (UnderlyingSpace ℂ X) where
  exists_compact_mem_nhds p := by
    obtain ⟨n, m, f, e, he, y, rfl⟩ := exists_isOpenEmbedding_zeroLocus X p
    haveI := (isClosed_zeroLocus f).locallyCompactSpace
    obtain ⟨s, hs, hsy⟩ := exists_compact_mem_nhds y
    exact ⟨e '' s, hs.image he.continuous, he.map_nhds_eq y ▸ Filter.image_mem_map hsy⟩

/-- The underlying space `X(ℂ)` of an algebraic scheme over `ℂ` is second countable: it is
covered by the finitely many open sets `U(ℂ)`, for a finite affine open cover of `X`, each
homeomorphic to a subset of `ℂⁿ`. -/
instance secondCountableTopology (X : Scheme.{0}) [X.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] [QuasiCompact (X ↘ Spec (.of ℂ))] :
    SecondCountableTopology (UnderlyingSpace ℂ X) := by
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of ℂ))
  have hV : ∀ x : X, ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V := fun x ↦ by
    obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
    exact ⟨V, hV, hxV⟩
  choose V hVa hxV using hV
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (V x : Set X))
    (fun x ↦ (V x).2) (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxV x⟩)
  letI (x : X) : (V x).toScheme.Over (Spec (.of ℂ)) := ⟨(V x).ι ≫ X ↘ Spec (.of ℂ)⟩
  haveI (x : X) : (V x).ι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  haveI (x : X) : IsAffine (V x) := hVa x
  haveI (x : X) : LocallyOfFiniteType ((V x).toScheme ↘ Spec (.of ℂ)) := by
    change LocallyOfFiniteType ((V x).ι ≫ X ↘ Spec (.of ℂ))
    infer_instance
  have hsc (x : X) : SecondCountableTopology (Set.range (map (K := ℂ) (V x).ι)) := by
    obtain ⟨n, m, f, ⟨φ⟩⟩ := exists_homeomorph_zeroLocus (V x)
    have e := (isOpenEmbedding_map_of_isOpenImmersion (K := ℂ) (V x).ι).isEmbedding.toHomeomorph
    exact (e.symm.trans φ).isEmbedding.secondCountableTopology
  haveI (x : t) : SecondCountableTopology (Set.range (map (K := ℂ) (V x.1).ι)) := hsc x.1
  refine TopologicalSpace.secondCountableTopology_of_countable_cover
    (ι := t) (U := fun x ↦ Set.range (map (K := ℂ) (V x.1).ι))
    (fun x ↦ (isOpenEmbedding_map_of_isOpenImmersion (K := ℂ) (V x.1).ι).isOpen_range) ?_
  refine Set.eq_univ_of_forall fun p ↦ ?_
  obtain ⟨x, hx, hpx⟩ :=
    Set.mem_iUnion₂.mp (ht (Set.mem_univ (p.toHom (IsLocalRing.closedPoint ℂ))))
  exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, mem_range_map_ι (V x) p hpx⟩

section Separated

variable {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [ContinuousInv₀ K]
  [T1Space K]

/-- The underlying space `X(K)` of a scheme `X` separated over a topological field `K` is
Hausdorff: the diagonal of `X(K)` is the image of the closed embedding induced by the diagonal
closed immersion `X → X ×_K X`, read in `X(K) × X(K)` through the homeomorphism
`(X ×_K X)(K) ≅ X(K) × X(K)`. -/
theorem t2Space_of_isSeparated (X : Scheme.{0}) [X.Over (Spec (.of K))]
    [IsSeparated (X ↘ Spec (.of K))] : T2Space (UnderlyingSpace K X) := by
  let f := X ↘ Spec (.of K)
  let P := Limits.pullback f f
  letI : P.Over (Spec (.of K)) := ⟨Limits.pullback.fst f f ≫ f⟩
  haveI : (Limits.pullback.fst f f).IsOver (Spec (.of K)) := ⟨rfl⟩
  haveI : (Limits.pullback.snd f f).IsOver (Spec (.of K)) := ⟨Limits.pullback.condition.symm⟩
  haveI : (Limits.pullback.diagonal f).IsOver (Spec (.of K)) :=
    ⟨Limits.pullback.diagonal_fst_assoc f f⟩
  have H : IsPullback (Limits.pullback.fst f f) (Limits.pullback.snd f f) f f :=
    IsPullback.of_hasPullback f f
  letI : (Spec (.of K)).Over (Spec (.of K)) := ⟨𝟙 _⟩
  haveI : f.IsOver (Spec (.of K)) := ⟨Category.comp_id _⟩
  have hpt : ∀ a b : UnderlyingSpace K X, mapFun f a = mapFun f b := fun a b ↦
    UnderlyingSpace.ext (by rw [toHom_mapFun, toHom_mapFun, a.toHom_comp_over, b.toHom_comp_over])
  have hrange : Set.range (prodMap (K := K) (Limits.pullback.fst f f) (Limits.pullback.snd f f)) =
      Set.univ := by
    rw [range_prodMap_of_isPullback H]
    exact Set.eq_univ_of_forall fun z ↦ hpt z.1 z.2
  have hP : IsClosedEmbedding
      (prodMap (K := K) (Limits.pullback.fst f f) (Limits.pullback.snd f f)) :=
    ⟨isEmbedding_prodMap_of_isPullback H, hrange ▸ isClosed_univ⟩
  have hΔ := hP.comp (isClosedEmbedding_map_of_isClosedImmersion (K := K)
    (Limits.pullback.diagonal f))
  rw [t2_iff_isClosed_diagonal]
  convert hΔ.isClosed_range using 1
  ext ⟨a, b⟩
  simp only [Set.mem_diagonal_iff, Set.mem_range, Function.comp_apply]
  refine ⟨fun h ↦ ⟨a, ?_⟩, fun ⟨p, hp⟩ ↦ ?_⟩
  · subst h
    refine Prod.ext (UnderlyingSpace.ext ?_) (UnderlyingSpace.ext ?_)
    · change (a.toHom ≫ Limits.pullback.diagonal f) ≫ Limits.pullback.fst f f = a.toHom
      simp
    · change (a.toHom ≫ Limits.pullback.diagonal f) ≫ Limits.pullback.snd f f = a.toHom
      simp
  · have h1 : a = p := (congrArg Prod.fst hp).symm.trans <|
      UnderlyingSpace.ext (by
        change (p.toHom ≫ Limits.pullback.diagonal f) ≫ Limits.pullback.fst f f = p.toHom
        simp)
    have h2 : b = p := (congrArg Prod.snd hp).symm.trans <|
      UnderlyingSpace.ext (by
        change (p.toHom ≫ Limits.pullback.diagonal f) ≫ Limits.pullback.snd f f = p.toHom
        simp)
    rw [h1, h2]

end Separated

section ComplexScheme

variable (X : Scheme.{0}) [X.Over (Spec (.of ℂ))] [IsComplexScheme X]

/-- A complex scheme is separated over `ℂ`: it is closed in a smooth variety, which is separated
over `ℂ`. -/
theorem _root_.MMP.IsComplexScheme.isSeparated : IsSeparated (X ↘ Spec (.of ℂ)) := by
  obtain ⟨V, _, hV, i, hio, hi⟩ := IsComplexScheme.exists_isClosedImmersion (X := X)
  rw [← hio.comp_over]
  infer_instance

/-- The underlying space of a complex scheme is Hausdorff. -/
instance t2Space_of_isComplexScheme : T2Space (UnderlyingSpace ℂ X) :=
  haveI := IsComplexScheme.isSeparated X
  t2Space_of_isSeparated X

/-- **Closed imbedding in Euclidean space** (Fulton, §19.1). The underlying space of a complex
scheme admits a closed embedding into some `ℝᴺ`. -/
theorem exists_isClosedEmbedding_euclideanSpace :
    ∃ (N : ℕ) (F : UnderlyingSpace ℂ X → EuclideanSpace ℝ (Fin N)), IsClosedEmbedding F := by
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of ℂ))
  have hV : ∀ x : X, ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V := fun x ↦ by
    obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
    exact ⟨V, hV, hxV⟩
  choose V hVa hxV using hV
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (V x : Set X))
    (fun x ↦ (V x).2) (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxV x⟩)
  letI (x : X) : (V x).toScheme.Over (Spec (.of ℂ)) := ⟨(V x).ι ≫ X ↘ Spec (.of ℂ)⟩
  haveI (x : X) : (V x).ι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  haveI (x : X) : IsAffine (V x) := hVa x
  haveI (x : X) : LocallyOfFiniteType ((V x).toScheme ↘ Spec (.of ℂ)) := by
    change LocallyOfFiniteType ((V x).ι ≫ X ↘ Spec (.of ℂ))
    infer_instance
  choose n m f φ using fun x : X ↦ exists_homeomorph_zeroLocus (V x)
  let U : t → Set (UnderlyingSpace ℂ X) := fun x ↦ Set.range (map (K := ℂ) (V x.1).ι)
  let g : ∀ x : t, U x → (Fin (n x.1) → ℂ) := fun x ↦
    Subtype.val ∘ (φ x.1).some ∘
      (isOpenEmbedding_map_of_isOpenImmersion (K := ℂ) (V x.1).ι).isEmbedding.toHomeomorph.symm
  have hg : ∀ x, IsClosedEmbedding (g x) := fun x ↦
    (isClosed_zeroLocus (f x.1)).isClosedEmbedding_subtypeVal.comp
      ((φ x.1).some.isClosedEmbedding.comp (Homeomorph.isClosedEmbedding _))
  have hcov : ⋃ x, U x = Set.univ := by
    refine Set.eq_univ_of_forall fun p ↦ ?_
    obtain ⟨x, hx, hpx⟩ :=
      Set.mem_iUnion₂.mp (ht (Set.mem_univ (p.toHom (IsLocalRing.closedPoint ℂ))))
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, mem_range_map_ι (V x) p hpx⟩
  obtain ⟨F, hF⟩ := exists_isClosedEmbedding_of_finite_cover U
    (fun x ↦ (isOpenEmbedding_map_of_isOpenImmersion (K := ℂ) (V x.1).ι).isOpen_range) hcov g hg
  let T := (t → ℝ) × (∀ x : t, Fin (n x.1) → ℂ)
  let e : T ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ T)) :=
    ContinuousLinearEquiv.ofFinrankEq (finrank_euclideanSpace_fin).symm
  exact ⟨_, e ∘ F, e.toHomeomorph.isClosedEmbedding.comp hF⟩

end ComplexScheme

end UnderlyingSpace

end MMP

/-!
## Complex algebraic sets as real algebraic sets

A complex algebraic set `Z ⊆ ℂⁿ`, the common zero set of finitely many complex polynomials, is in
real coordinates `ℂⁿ ≃ₜ ℝ^{n × 2}` a real algebraic set: the common zero set of the real and
imaginary parts of those polynomials.

* `MMP.complexRealHomeomorph`: `ℂ^σ ≃ₜ ℝ^{σ × Fin 2}`.
* `MMP.exists_homeomorph_complexZeroLocus`: a complex algebraic set is homeomorphic to a real
  algebraic set.
-/

@[expose] public section

open Set Topology AlgebraicGeometry CategoryTheory

namespace MMP

/-- The real coordinates `ℂ^σ ≃ₜ ℝ^{σ × Fin 2}`, `z ↦ (re z_i, im z_i)_i`. -/
def complexRealHomeomorph (σ : Type*) : (σ → ℂ) ≃ₜ (σ × Fin 2 → ℝ) where
  toEquiv := complexRealEquiv
  continuous_toFun := by
    refine continuous_pi fun i ↦ ?_
    change Continuous fun z : σ → ℂ ↦ if i.2 = 0 then (z i.1).re else (z i.1).im
    split_ifs <;> fun_prop
  continuous_invFun := by
    refine continuous_pi fun i ↦ ?_
    change Continuous fun x : σ × Fin 2 → ℝ ↦ (⟨x (i, 0), x (i, 1)⟩ : ℂ)
    have h : Continuous fun x : σ × Fin 2 → ℝ ↦ (x (i, 0) : ℂ) + (x (i, 1) : ℂ) * Complex.I := by
      fun_prop
    convert h using 2 with x
    apply Complex.ext <;> simp

/-- A complex algebraic set `Z ⊆ ℂⁿ` is homeomorphic to a real algebraic set in `ℝ^{n × 2}`. -/
theorem exists_homeomorph_complexZeroLocus {n m : ℕ} (f : Fin m → MvPolynomial (Fin n) ℂ) :
    ∃ g : Fin m × Fin 2 → MvPolynomial (Fin n × Fin 2) ℝ,
      Nonempty ({v : Fin n → ℂ | ∀ j, MvPolynomial.eval v (f j) = 0} ≃ₜ
        {x : Fin n × Fin 2 → ℝ | ∀ j, MvPolynomial.eval x (g j) = 0}) := by
  obtain ⟨g, hg⟩ := exists_complexZeroLocus_eq f
  let e := complexRealHomeomorph (Fin n)
  have he : e ⁻¹' {x | ∀ j, MvPolynomial.eval x (g j) = 0} =
      {v : Fin n → ℂ | ∀ j, MvPolynomial.eval v (f j) = 0} := by
    ext z
    change complexToReal z ∈ ({x | ∀ j, MvPolynomial.eval x (g j) = 0} : Set _) ↔ _
    rw [← hg, mem_preimage, realToComplex_complexToReal]
  exact ⟨g, ⟨(Homeomorph.setCongr he).symm.trans
    (e.subtype (p := fun z ↦ z ∈ e ⁻¹' {x | ∀ j, MvPolynomial.eval x (g j) = 0})
      (q := fun x ↦ x ∈ {x | ∀ j, MvPolynomial.eval x (g j) = 0}) fun _ ↦ Iff.rfl)⟩⟩

end MMP

/-!
## Complex schemes are locally contractible

By the triangulation theorem (`MMP.semialgebraicTriangulation`), every point `x`
of a closed semialgebraic set `V ⊆ ℝⁿ` has arbitrarily small open contractible neighbourhoods
in `V` (`MMP.exists_isOpen_contractibleSpace_inter`): the image of the open star
of the vertex over `x` in a triangulation compatible with `{x}` and a small ball. Complex
algebraic sets are real algebraic sets in real coordinates, and the underlying space of a scheme
locally of finite type over `ℂ` is covered by open charts onto complex algebraic sets, so it has
a basis of open contractible neighbourhoods (Fulton, §19.1).

## Main definitions

* `MMP.HasOpenContractibleBasis`: every point has a basis of open contractible
  neighbourhoods.

## Main results

* `MMP.HasOpenContractibleBasis.of_isSemialgebraic`: closed semialgebraic sets.
* `MMP.UnderlyingSpace.hasOpenContractibleBasis`: underlying spaces of schemes
  locally of finite type over `ℂ`.
* `MMP.UnderlyingSpace.hasBasis_contractible_and_exists_isClosedEmbedding`: the
  underlying space of a complex scheme is locally contractible, every point having a basis of
  open contractible neighbourhoods, and it has a closed imbedding in some `ℝᴺ`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [J. Bochnak, M. Coste, M.-F. Roy, *Real algebraic geometry*][bochnak1998], Theorem 9.2.1.
-/

@[expose] public section

open Set Topology Filter AlgebraicGeometry CategoryTheory

namespace MMP

/-- Every point of `X` has a basis of open contractible neighbourhoods. -/
def HasOpenContractibleBasis (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ x : X, (𝓝 x).HasBasis (fun V : Set X ↦ IsOpen V ∧ x ∈ V ∧ ContractibleSpace V) id

namespace HasOpenContractibleBasis

/-- A space in which every point has a basis of open contractible neighbourhoods is strongly
locally contractible. -/
theorem stronglyLocallyContractibleSpace {X : Type*} [TopologicalSpace X]
    (h : HasOpenContractibleBasis X) : StronglyLocallyContractibleSpace X := by
  refine ⟨fun x ↦ ⟨fun t ↦ ⟨fun ht ↦ ?_, fun ⟨s, ⟨hs, _⟩, hst⟩ ↦ mem_of_superset hs hst⟩⟩⟩
  obtain ⟨V, ⟨hV, hxV, hc⟩, hVt⟩ := (h x).mem_iff.1 ht
  exact ⟨V, ⟨hV.mem_nhds hxV, hc⟩, hVt⟩

/-- A space covered by open embeddings of spaces with bases of open contractible
neighbourhoods has such bases. -/
theorem of_isOpenEmbedding_cover {X : Type*} [TopologicalSpace X]
    (h : ∀ x : X, ∃ (Y : Type*) (_ : TopologicalSpace Y) (e : Y → X),
      HasOpenContractibleBasis Y ∧ IsOpenEmbedding e ∧ x ∈ range e) :
    HasOpenContractibleBasis X := by
  intro x
  obtain ⟨Y, _, e, hY, he, y, rfl⟩ := h x
  refine ⟨fun t ↦ ⟨fun ht ↦ ?_, fun ⟨V, ⟨hV, hxV, _⟩, hVt⟩ ↦ mem_of_superset (hV.mem_nhds hxV)
    hVt⟩⟩
  rw [← he.map_nhds_eq] at ht
  obtain ⟨V, ⟨hV, hyV, hc⟩, hVt⟩ := (hY y).mem_iff.1 ht
  exact ⟨e '' V, ⟨he.isOpenMap V hV, mem_image_of_mem e hyV,
    (he.isEmbedding.homeomorphImage V).symm.contractibleSpace⟩, image_subset_iff.2 hVt⟩

/-- A space homeomorphic to one with bases of open contractible neighbourhoods has such bases. -/
theorem of_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : HasOpenContractibleBasis Y) (e : Y ≃ₜ X) : HasOpenContractibleBasis X :=
  of_isOpenEmbedding_cover fun x ↦ ⟨Y, inferInstance, e, h, e.isOpenEmbedding, e.surjective x⟩

/-- **Closed semialgebraic sets have bases of open contractible neighbourhoods.** -/
theorem of_isSemialgebraic {σ : Type} [Fintype σ] {V : Set (σ → ℝ)} (hV : IsSemialgebraic V)
    (hVc : IsClosed V) : HasOpenContractibleBasis V := by
  intro y
  refine ⟨fun s ↦ ⟨fun hs ↦ ?_, fun ⟨W, ⟨hW, hyW, _⟩, hWs⟩ ↦ mem_of_superset (hW.mem_nhds hyW)
    hWs⟩⟩
  obtain ⟨U, hU, hUs⟩ := (mem_nhds_subtype V y s).1 hs
  obtain ⟨W, hWo, hyW, hWU, hc⟩ := exists_isOpen_contractibleSpace_inter hV hVc y.2 hU
  refine ⟨Subtype.val ⁻¹' W, ⟨hWo.preimage continuous_subtype_val, hyW, ?_⟩,
    fun z hz ↦ hUs (hWU ⟨hz, z.2⟩)⟩
  let e : (Subtype.val ⁻¹' W : Set V) ≃ₜ (W ∩ V : Set (σ → ℝ)) :=
    { toFun := fun z ↦ ⟨z.1.1, z.2, z.1.2⟩
      invFun := fun z ↦ ⟨⟨z.1, z.2.2⟩, z.2.1⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  haveI := hc
  exact e.contractibleSpace

end HasOpenContractibleBasis

/-- Complex algebraic sets `Z ⊆ ℂⁿ` have bases of open contractible neighbourhoods. -/
theorem hasOpenContractibleBasis_complexZeroLocus {n m : ℕ}
    (f : Fin m → MvPolynomial (Fin n) ℂ) :
    HasOpenContractibleBasis {v : Fin n → ℂ | ∀ j, MvPolynomial.eval v (f j) = 0} := by
  obtain ⟨g, ⟨φ⟩⟩ := exists_homeomorph_complexZeroLocus f
  exact (HasOpenContractibleBasis.of_isSemialgebraic (isSemialgebraic_zeroLocus g)
    (UnderlyingSpace.isClosed_zeroLocus g)).of_homeomorph φ.symm

namespace UnderlyingSpace

/-- The underlying space of a scheme locally of finite type over `ℂ` has a basis of open
contractible neighbourhoods at every point. -/
theorem hasOpenContractibleBasis (X : Scheme.{0}) [X.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] :
    HasOpenContractibleBasis (UnderlyingSpace ℂ X) :=
  HasOpenContractibleBasis.of_isOpenEmbedding_cover fun p ↦ by
    obtain ⟨n, m, f, e, he, hp⟩ := exists_isOpenEmbedding_zeroLocus X p
    exact ⟨_, inferInstance, e, hasOpenContractibleBasis_complexZeroLocus f,
      he, hp⟩

/-- **Fulton, §19.1.** The underlying space of a complex scheme is locally contractible: every
point has a basis of open contractible neighbourhoods. It has a closed imbedding in some
`ℝᴺ`. -/
theorem hasBasis_contractible_and_exists_isClosedEmbedding (X : Scheme.{0})
    [X.Over (Spec (.of ℂ))] [IsComplexScheme X] :
    (∀ p : UnderlyingSpace ℂ X,
      (𝓝 p).HasBasis (fun V : Set (UnderlyingSpace ℂ X) ↦ IsOpen V ∧ p ∈ V ∧ ContractibleSpace V)
        id) ∧
      ∃ (N : ℕ) (F : UnderlyingSpace ℂ X → EuclideanSpace ℝ (Fin N)), IsClosedEmbedding F :=
  ⟨hasOpenContractibleBasis X, exists_isClosedEmbedding_euclideanSpace X⟩

/-- The underlying space of a scheme locally of finite type over `ℂ` is strongly locally
contractible. -/
instance stronglyLocallyContractibleSpace_of_locallyOfFiniteType (X : Scheme.{0})
    [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] :
    StronglyLocallyContractibleSpace (UnderlyingSpace ℂ X) :=
  (hasOpenContractibleBasis X).stronglyLocallyContractibleSpace

end UnderlyingSpace

end MMP
