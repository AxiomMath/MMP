module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ProjectiveSpaceCompact
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.UnderlyingSpaceProper
public import StacksFrontier.AlgebraicGeometry.Limits.ChowLemmaAffineBase
public import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso

/-!
# Proper morphisms induce proper maps of underlying spaces

Let `K` be an algebraically closed normed field which is a proper metric space, such as `ℂ`, and
let `f : X → Y` be a proper morphism of schemes locally of finite type over `K`. Then the induced
map `X(K) → Y(K)` of underlying spaces with the classical topology is proper (Fulton, §19.1).

The proof follows the classical route. Properness of a continuous map is local on the target
(`MMP.isProperMap_of_isOpenEmbedding_cover`), so `Y` may be taken affine, hence Noetherian. Chow's
lemma over a Noetherian base gives a proper surjective `π : X' → X` and an immersion
`i : X' → ℙⁿ_Y` over `Y`; since `π ≫ f` is proper, `i` is proper, hence a closed immersion. So
`X'(K) → Y(K)` is a closed embedding into `ℙⁿ(K) × Y(K)` followed by the projection, which is
proper because `ℙⁿ(K)` is compact (`compactSpace_projectiveSpace`). Finally properness descends
along the surjection `X'(K) → X(K)`.

## Main results

* `MMP.isProperMap_of_isOpenEmbedding_cover`: properness of a continuous map is local on the
  target.
* `MMP.UnderlyingSpace.isProperMap_map`: a proper morphism over `K` induces a proper map of
  underlying spaces.
* `MMP.IsComplexScheme.isProperMap_map`: the case of complex schemes.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [Stacks Project, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Topology

universe u

namespace MMP

section LocalAtTarget

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/-- **Properness is local on the target.** Let `f : X → Y` be continuous, and let `Y` be covered
by open embeddings `jᵢ : Yᵢ → Y` over which `f` restricts, through open embeddings
`kᵢ : Xᵢ → X` onto `f⁻¹(jᵢ(Yᵢ))`, to proper maps `gᵢ : Xᵢ → Yᵢ`. Then `f` is proper. -/
theorem isProperMap_of_isOpenEmbedding_cover (hf : Continuous f) {ι : Type*}
    {X' Y' : ι → Type*} [∀ i, TopologicalSpace (X' i)] [∀ i, TopologicalSpace (Y' i)]
    (k : ∀ i, X' i → X) (j : ∀ i, Y' i → Y) (g : ∀ i, X' i → Y' i)
    (hk : ∀ i, IsOpenEmbedding (k i)) (hj : ∀ i, IsOpenEmbedding (j i))
    (hg : ∀ i, IsProperMap (g i)) (hcomm : ∀ i x, f (k i x) = j i (g i x))
    (hrange : ∀ i, f ⁻¹' Set.range (j i) ⊆ Set.range (k i))
    (hcover : ∀ y, ∃ i, y ∈ Set.range (j i)) : IsProperMap f := by
  -- a point of `X` over `jᵢ(y')` is `kᵢ(x')` for some `x'` with `gᵢ(x') = y'`
  have key : ∀ i x y', f x = j i y' → ∃ x', k i x' = x ∧ g i x' = y' := by
    intro i x y' hx
    obtain ⟨x', rfl⟩ := hrange i ⟨y', hx.symm⟩
    exact ⟨x', rfl, (hj i).injective ((hcomm i x').symm.trans hx)⟩
  refine isProperMap_iff_isClosedMap_and_compact_fibers.mpr ⟨hf, fun C hC ↦ ?_, fun y ↦ ?_⟩
  · refine isOpen_compl_iff.mp (isOpen_iff_forall_mem_open.mpr fun y hy ↦ ?_)
    obtain ⟨i, y', rfl⟩ := hcover y
    have hD : IsClosed (g i '' (k i ⁻¹' C)) :=
      (hg i).isClosedMap _ (hC.preimage (hk i).continuous)
    refine ⟨j i '' (g i '' (k i ⁻¹' C))ᶜ, ?_, (hj i).isOpenMap _ hD.isOpen_compl, ?_⟩
    · rintro _ ⟨z', hz', rfl⟩ ⟨x, hxC, hx⟩
      obtain ⟨x', rfl, rfl⟩ := key i x z' hx
      exact hz' ⟨x', hxC, rfl⟩
    · refine ⟨y', fun ⟨x', hx'C, hx'⟩ ↦ hy ⟨k i x', hx'C, ?_⟩, rfl⟩
      rw [hcomm, hx']
  · obtain ⟨i, y', rfl⟩ := hcover y
    have : f ⁻¹' {j i y'} = k i '' (g i ⁻¹' {y'}) := by
      ext x
      refine ⟨fun hx ↦ ?_, ?_⟩
      · obtain ⟨x', rfl, hx'⟩ := key i x y' hx
        exact ⟨x', hx', rfl⟩
      · rintro ⟨x', hx', rfl⟩
        change f (k i x') = j i y'
        rw [hcomm, show g i x' = y' from hx']
    rw [this]
    exact ((hg i).isCompact_preimage isCompact_singleton).image (hk i).continuous

end LocalAtTarget

namespace UnderlyingSpace

variable {K : Type u}

section Iso

variable [Field K] [TopologicalSpace K] {X Y : Scheme.{u}} [X.Over (Spec (.of K))]
  [Y.Over (Spec (.of K))]

/-- An isomorphism over `K` is surjective on `K`-points. -/
lemma mapFun_surjective_of_isIso (e : X ⟶ Y) [IsIso e] [e.IsOver (Spec (.of K))] :
    Function.Surjective (mapFun (K := K) e) := fun q ↦
  ⟨⟨q.toHom ≫ inv e, by
    rw [Category.assoc, ← comp_over e (Spec (.of K)), IsIso.inv_hom_id_assoc, q.toHom_comp_over]⟩,
    UnderlyingSpace.ext (by
      change (q.toHom ≫ inv e) ≫ e = q.toHom
      rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id])⟩

/-- Compactness of underlying spaces is transported along isomorphisms over `K`. -/
lemma compactSpace_of_isIso (e : X ⟶ Y) [IsIso e] [e.IsOver (Spec (.of K))]
    [CompactSpace (UnderlyingSpace K X)] : CompactSpace (UnderlyingSpace K Y) :=
  ⟨by
    rw [← (mapFun_surjective_of_isIso (K := K) e).range_eq]
    exact isCompact_range (map e).continuous⟩

end Iso

section ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- `ℙⁿ_{Spec K}(K)` is compact: it is isomorphic over `K` to `Proj K[x₀, …, xₙ]`
(`Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison`), whose `K`-points are compact. -/
instance compactSpace_projectiveSpaceOver [NormedField K] [ProperSpace K] (n : ℕ) :
    CompactSpace (UnderlyingSpace K (projectiveSpaceOver n (Spec (.of K)))) := by
  letI : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading K n)).Over
      (Spec (.of K)) := ⟨Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff K n⟩
  have := compactSpace_projectiveSpace (K := K) n rfl
  have hbase := (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison K n).toBase
  have : (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison K n).iso.inv.IsOver
      (Spec (.of K)) := ⟨by
    change _ ≫ pullback.fst _ _ = Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff K n
    rw [← hbase, Iso.inv_hom_id_assoc]
    rfl⟩
  exact compactSpace_of_isIso
    (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison K n).iso.inv

end ProjectiveSpace

section AffineBase

variable [NormedField K] [IsAlgClosed K] [ProperSpace K]
variable {X S : Scheme.{u}} [X.Over (Spec (.of K))] [S.Over (Spec (.of K))]

/-- Over an affine base `S` locally of finite type over `K`, a proper morphism `f : X → S` over
`K` induces a proper map `X(K) → S(K)`: by Chow's lemma it is dominated by a closed subscheme of
`ℙⁿ × S`. -/
theorem isProperMap_map_of_isAffine (f : X ⟶ S) [f.IsOver (Spec (.of K))] [IsProper f]
    [IsAffine S] [LocallyOfFiniteType (S ↘ Spec (.of K))] :
    IsProperMap (map (K := K) f) := by
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (S ↘ Spec (.of K))
  have : IsNoetherian S := ⟨⟩
  obtain ⟨n, X', π, i, -, hπ, hsurj, hi, hcomm, -, -⟩ :=
    hasChowModificationIsoOnDenseOpen_of_isAffine f
  have : IsProper π := hπ
  have : Surjective π := hsurj
  have : IsImmersion i := hi
  letI : X'.Over (Spec (.of K)) := ⟨π ≫ X ↘ Spec (.of K)⟩
  have : π.IsOver (Spec (.of K)) := ⟨rfl⟩
  have hiS : i ≫ (projectiveSpaceOver n S ↘ S) = π ≫ f := hcomm.symm
  have : i.IsOver (Spec (.of K)) := ⟨by
    change i ≫ (projectiveSpaceOver n S ↘ S) ≫ S ↘ Spec (.of K) = π ≫ X ↘ Spec (.of K)
    rw [← Category.assoc, hiS, Category.assoc, comp_over]⟩
  have : IsProper (i ≫ (projectiveSpaceOver n S ↘ S)) := by rw [hiS]; infer_instance
  have : IsProper i := IsProper.of_comp i (projectiveSpaceOver n S ↘ S)
  have : IsClosedImmersion i := IsClosedImmersion.of_isPreimmersion i (by
    simpa only [Set.image_univ] using i.isClosedMap _ isClosed_univ)
  -- the square `ℙⁿ_S → ℙⁿ_K` over `S → Spec K`
  letI : (Spec (.of K)).Over (Spec (.of K)) := ⟨𝟙 _⟩
  let fst : projectiveSpaceOver n S ⟶ projectiveSpaceOver n (Spec (.of K)) :=
    pullback.map (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} n))
      (terminal.from (Spec (.of K))) (terminal.from (projectiveSpaceAtUniverse.{u} n))
      (S ↘ Spec (.of K)) (𝟙 _) (𝟙 _) (by simp) (by simp)
  have H : IsPullback fst (projectiveSpaceOver n S ↘ S)
      (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K)) (S ↘ Spec (.of K)) := by
    refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback (terminal.from (Spec (.of K)))
        (terminal.from (projectiveSpaceAtUniverse.{u} n))).flip
    have e1 : fst ≫ pullback.snd _ _ =
        pullback.snd (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} n)) :=
      (pullback.lift_snd _ _ _).trans (Category.comp_id _)
    have e2 : (S ↘ Spec (.of K)) ≫ terminal.from (Spec (.of K)) = terminal.from S :=
      terminal.comp_from _
    rw [e1, e2]
    exact (IsPullback.of_hasPullback _ _).flip
  have : fst.IsOver (Spec (.of K)) := ⟨H.w⟩
  have : (projectiveSpaceOver n S ↘ S).IsOver (Spec (.of K)) := ⟨rfl⟩
  have : (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K)).IsOver (Spec (.of K)) :=
    ⟨Category.comp_id _⟩
  have : (S ↘ Spec (.of K)).IsOver (Spec (.of K)) := ⟨Category.comp_id _⟩
  have : Subsingleton (UnderlyingSpace K (Spec (.of K))) := ⟨fun p q ↦ UnderlyingSpace.ext
    (((Category.comp_id _).symm.trans p.toHom_comp_over).trans
      ((Category.comp_id _).symm.trans q.toHom_comp_over).symm)⟩
  have h := isProperMap_map_of_isClosedImmersion_comp_snd (K := K) H i
  have hfun : (map (K := K) (i ≫ (projectiveSpaceOver n S ↘ S)) : _ → _) = map (π ≫ f) := by
    funext p
    exact UnderlyingSpace.ext (by rw [toHom_map, toHom_map, hiS])
  have : LocallyOfFiniteType (X' ↘ Spec (.of K)) := by
    change LocallyOfFiniteType (π ≫ X ↘ Spec (.of K))
    rw [← comp_over f (Spec (.of K))]
    infer_instance
  exact isProperMap_map_of_comp π f (hfun ▸ h)

end AffineBase

section General

/-- The restriction `f⁻¹(V) → V` of a morphism over `S` lies over `S`. -/
instance isOver_morphismRestrict {S X Y : Scheme.{u}} [X.Over S] [Y.Over S] (f : X ⟶ Y)
    [f.IsOver S] (V : Y.Opens) : (f ∣_ V).IsOver S :=
  ⟨by rw [← Scheme.Opens.ι_comp_over V, ← Category.assoc, morphismRestrict_ι, Category.assoc,
    comp_over, Scheme.Opens.ι_comp_over]⟩

variable [NormedField K] [IsAlgClosed K] [ProperSpace K]
variable {X Y : Scheme.{u}} [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]

/-- **A proper morphism induces a proper map of underlying spaces** (Fulton, §19.1). Let `K` be
an algebraically closed normed field which is a proper metric space, such as `ℂ`, and
`f : X → Y` a proper morphism over `K` with `Y` locally of finite type over `K`. Then the
continuous map `X(K) → Y(K)` is proper. -/
theorem isProperMap_map (f : X ⟶ Y) [f.IsOver (Spec (.of K))] [IsProper f]
    [LocallyOfFiniteType (Y ↘ Spec (.of K))] : IsProperMap (map (K := K) f) := by
  refine isProperMap_of_isOpenEmbedding_cover (map f).continuous (ι := Y.affineOpens)
    (fun V ↦ map (K := K) (f ⁻¹ᵁ V.1).ι) (fun V ↦ map (K := K) V.1.ι)
    (fun V ↦ map (K := K) (f ∣_ V.1)) (fun V ↦ isOpenEmbedding_map_of_isOpenImmersion _)
    (fun V ↦ isOpenEmbedding_map_of_isOpenImmersion _) (fun V ↦ ?_) (fun V x ↦ ?_)
    (fun V ↦ ?_) (fun y ↦ ?_)
  · have : IsAffine V.1 := V.2
    have : LocallyOfFiniteType (V.1.toScheme ↘ Spec (.of K)) := by
      rw [← Scheme.Opens.ι_comp_over]
      infer_instance
    exact isProperMap_map_of_isAffine (f ∣_ V.1)
  · refine UnderlyingSpace.ext ?_
    simp only [toHom_map, Category.assoc, morphismRestrict_ι]
  · rintro p ⟨q, hq⟩
    have hp : mapFun (K := K) f p ∈ Set.range (mapFun (K := K) V.1.ι) := ⟨q, hq⟩
    rw [range_mapFun_of_isOpenImmersion, Scheme.Opens.opensRange_ι] at hp
    have : p ∈ Set.range (mapFun (K := K) (f ⁻¹ᵁ V.1).ι) := by
      rw [range_mapFun_of_isOpenImmersion, Scheme.Opens.opensRange_ι]
      exact hp
    exact this
  · have hy : y.toHom (IsLocalRing.closedPoint K) ∈ (⊤ : Y.Opens) := trivial
    obtain ⟨V, hV, hx, -⟩ := exists_isAffineOpen_mem_and_subset hy
    refine ⟨⟨V, hV⟩, ?_⟩
    have : y ∈ Set.range (mapFun (K := K) V.ι) := by
      rw [range_mapFun_of_isOpenImmersion, Scheme.Opens.opensRange_ι]
      exact (top_le_preimage_iff y V).mpr hx
    exact this

end General

/-- **A proper morphism of complex schemes induces a proper map of underlying spaces**
(Fulton, §19.1): for `f : X → Y` a proper morphism of complex schemes, the continuous map
`X(ℂ) → Y(ℂ)` of `MMP.UnderlyingSpace.map` is proper. -/
theorem _root_.MMP.IsComplexScheme.isProperMap_map {X Y : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))] [IsComplexScheme X] [IsComplexScheme Y]
    (f : X ⟶ Y) [f.IsOver (Spec (.of ℂ))] [IsProper f] : IsProperMap (map (K := ℂ) f) :=
  UnderlyingSpace.isProperMap_map f

end UnderlyingSpace

end MMP
