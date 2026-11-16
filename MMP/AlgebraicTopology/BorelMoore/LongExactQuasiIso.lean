module

public import MMP.AlgebraicTopology.BorelMoore.LongExactHomotopy
public import MMP.AlgebraicTopology.BorelMoore.SmallChains
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ProperNeighbourhoodRetractHomotopy

/-!
# The relative quasi-isomorphism of the Borel–Moore long exact sequence

Let `X` be a closed subset of a Hausdorff space `Y` with `U = Y - X`, and let `N' ⊆ interior N`
be closed neighbourhoods of `X` with a proper homotopy `G : N × [0, 1] → Y` from the inclusion
to a map into `X`, fixing `X`. Then the restriction `C^lf(Y) / C^lf(X) → C^lf(U)` is a
quasi-isomorphism (`IsRelativeQuasiIso`).

(S) A cycle `z` of `U` is subdivided (`smallChainMapLF`) for the cover `{interior N - X, U - N'}`
and split as `z' + z''`, `z''` the simplices in `N`; `z'` lies outside `N'`, so it is a locally
finite chain of `Y`; with `β = ∂ z'`, a cycle of `B = N - interior N'`, the chain
`b = z' - h_B β` has boundary in `X`, and `b|_U - z = ∂(-H z'' - D z)`.

(I) A chain `b` of `Y` with boundary in `X` and `b|_U = ∂ e` is subdivided for the cover
`{interior N, Y - N'}` and split as `b₁ + b₂`, `b₁` the simplices in `N`; subdividing `e` and
moving the parts of `e` outside `N` to `Y` replaces `b₂` by a chain `c₂` with
`(b₁ + c₂)|_U` supported in `N`; then `b₁ + c₂` is a chain of `N`, deformed into `X` by `G`.

## Main results

* `MMP.borelMooreHomology.isRelativeQuasiIso_of_homotopy`.
* `MMP.borelMooreHomology.isRelativeQuasiIso_of_isClosedEmbedding`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [A. Hatcher, *Algebraic Topology*][hatcher2002], §2.1, Prop. 2.21.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicTopology Opposite Topology Set Simplicial

universe u

namespace MMP

namespace borelMooreHomology

open LocallyFiniteChain

section support

variable {R : Type u} [CommRing R] {M : ModuleCat.{u} R} {P : TopCat.{u}}

/-- The boundary of a chain supported in `S` is supported in `S`. -/
lemma IsSupportedIn.d_of {S : Set P} {i j : ℕ} {c : (borelMooreChainComplex R M P).X i}
    (hc : IsSupportedIn R M S c) :
    IsSupportedIn R M S (((borelMooreChainComplex R M P).d i j).hom c) := by
  by_cases h : j + 1 = i
  · subst h
    exact hc.d
  · rw [(borelMooreChainComplex R M P).shape _ _ h]
    exact isSupportedIn_zero

/-- The subdivision of a chain supported in `S` is supported in `S`. -/
lemma IsSupportedIn.smallChainMapLF [T2Space P] {S : Set P} (𝒰 : Set (Set P)) {n : ℕ}
    {c : (borelMooreChainComplex R M P).X n} (hc : IsSupportedIn R M S c) :
    IsSupportedIn R M S (((borelMooreHomology.smallChainMapLF R M 𝒰).f n).hom c) := by
  intro τ hτ
  obtain ⟨σ, hσ, h⟩ := exists_of_smallChainMapLF_ne_zero R M 𝒰 c hτ
  exact h.trans (hc σ hσ)

/-- The subdivision homotopy applied to a chain supported in `S` is supported in `S`. -/
lemma IsSupportedIn.smallHomotopyMap [T2Space P] {S : Set P} (𝒰 : Set (Set P)) {n : ℕ}
    {c : (borelMooreChainComplex R M P).X n} (hc : IsSupportedIn R M S c) :
    IsSupportedIn R M S ((borelMooreHomology.smallHomotopyMap R M 𝒰 n).hom c) := by
  intro τ hτ
  obtain ⟨σ, hσ, h⟩ := exists_of_smallHomotopyMap_ne_zero R M 𝒰 c hτ
  exact h.trans (hc σ hσ)

/-- A simplex with nonzero coefficient in the part of `c` on the simplices of `s` lies in `s`
and has nonzero coefficient in `c`. -/
lemma mem_of_chainPart_ne_zero {n : ℕ} {s : Set ((TopCat.toSSet.obj P).obj (op ⦋n⦌))}
    {c : (borelMooreChainComplex R M P).X n} {σ : (TopCat.toSSet.obj P).obj (op ⦋n⦌)}
    (h : ((chainPart R M s).hom c).1 σ ≠ 0) : σ ∈ s ∧ c.1 σ ≠ 0 := by
  rw [chainPart_apply_coe] at h
  exact ⟨Set.mem_of_indicator_ne_zero h, fun h' ↦ h (by simp [h'])⟩

/-- A chain supported in a closed set `N` is the push-forward of a chain of `N`. -/
lemma exists_eq_chainMap_of_isSupportedIn {N : Set P} (hN : IsClosed N) {n : ℕ}
    {c : (borelMooreChainComplex R M P).X n} (hc : IsSupportedIn R M N c) :
    ∃ c' : (borelMooreChainComplex R M (TopCat.of N)).X n,
      c = ((chainMap R M (subsetInclusion N) (isProperMap_subsetInclusion hN)).f n).hom c' :=
  ⟨_, (chainMap_subsetRestrictMap R M hN hc).symm⟩

/-- A push-forward from a set `N` is supported in `N`. -/
lemma isSupportedIn_chainMap_subsetInclusion {N : Set P} (hN : IsClosed N) {n : ℕ}
    (c : (borelMooreChainComplex R M (TopCat.of N)).X n) :
    IsSupportedIn R M N
      (((chainMap R M (subsetInclusion N) (isProperMap_subsetInclusion hN)).f n).hom c) := by
  intro σ hσ
  change pushforwardFun ((TopCat.toSSet.map (subsetInclusion N)).app _) c.1 σ ≠ 0 at hσ
  obtain ⟨σ', -, rfl⟩ := support_pushforwardFun_subset _ c.1 hσ
  rw [singularSimplexImage_map_subsetInclusion]
  exact Subtype.coe_image_subset _ _

variable [T2Space P]

/-- The restriction of a chain supported in `S` is supported in `S`. -/
lemma IsSupportedIn.restrictChainMap {S : Set P} (V : TopologicalSpace.Opens P) {n : ℕ}
    {c : (borelMooreChainComplex R M P).X n} (hc : IsSupportedIn R M S c) :
    IsSupportedIn R M (Subtype.val ⁻¹' S : Set (TopCat.of V))
      (((borelMooreHomology.restrictChainMap R M V).f n).hom c) := by
  intro τ hτ
  change kernelFun (restrictKernel V n) c.1 τ ≠ 0 at hτ
  obtain ⟨σ, hσ⟩ : ∃ σ, restrictKernel V n σ τ • c.1 σ ≠ 0 := by
    by_contra h
    push Not at h
    exact hτ (finsum_eq_zero_of_forall_eq_zero h)
  have := (isAdmissibleKernel_restrictKernel V n).image_subset σ τ (smul_ne_zero_left hσ)
  intro x hx
  exact hc σ (smul_ne_zero_right hσ) (this ⟨x, hx, rfl⟩)

/-- A chain supported in an open set `V` is supported in `S` if its restriction to `V` is
supported in `S ∩ V`. -/
lemma isSupportedIn_of_restrictChainMap {S : Set P} (V : TopologicalSpace.Opens P) {n : ℕ}
    {c : (borelMooreChainComplex R M P).X n} (hc : IsSupportedIn R M (V : Set P) c)
    (h : IsSupportedIn R M (Subtype.val ⁻¹' S : Set (TopCat.of V))
      (((borelMooreHomology.restrictChainMap R M V).f n).hom c)) :
    IsSupportedIn R M S c := by
  intro σ hσ
  obtain ⟨τ, rfl⟩ := mem_range_map_subsetInclusion (hc σ hσ)
  rw [singularSimplexImage_map_subsetInclusion]
  rintro _ ⟨x, hx, rfl⟩
  exact h τ (by rwa [restrictChainMap_apply_of_isSupportedIn R M V hc]) hx

/-- A chain supported in an open set `V` whose restriction to `V` vanishes is zero. -/
lemma eq_zero_of_restrictChainMap {V : TopologicalSpace.Opens P} {n : ℕ}
    {c : (borelMooreChainComplex R M P).X n} (hc : IsSupportedIn R M (V : Set P) c)
    (h : ((borelMooreHomology.restrictChainMap R M V).f n).hom c = 0) : c = 0 := by
  have := isSupportedIn_of_restrictChainMap (S := ∅) V hc (h ▸ isSupportedIn_zero)
  apply Subtype.ext
  funext σ
  by_contra h'
  obtain ⟨x, hx⟩ := nonempty_singularSimplexImage σ
  exact this σ h' hx

/-- **Extension by zero.** A chain of the open set `V` supported in a closed set `F ⊆ V` of `P`
is the restriction of a chain of `P` supported in `F`. -/
lemma exists_restrictChainMap_eq {V : TopologicalSpace.Opens P} {F : Set P} (hF : IsClosed F)
    (hFV : F ⊆ V) {n : ℕ} {c : (borelMooreChainComplex R M (TopCat.of V)).X n}
    (hc : IsSupportedIn R M (Subtype.val ⁻¹' F : Set (TopCat.of V)) c) :
    ∃ c' : (borelMooreChainComplex R M P).X n, IsSupportedIn R M F c' ∧
      ((borelMooreHomology.restrictChainMap R M V).f n).hom c' = c := by
  set F' : Set (TopCat.of V) := Subtype.val ⁻¹' F
  have hF' : IsClosed F' := hF.preimage continuous_subtype_val
  let j : TopCat.of F' ⟶ P := subsetInclusion F' ≫ clopenInclusion V
  let e : F' ≃ₜ F :=
    { toFun := fun y ↦ ⟨y.1.1, y.2⟩
      invFun := fun y ↦ ⟨⟨y.1, hFV y.2⟩, y.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hj : IsProperMap j := hF.isClosedEmbedding_subtypeVal.isProperMap.comp e.isProperMap
  set d := (subsetRestrictMap R M F' n).hom c
  have hd : ((chainMap R M (subsetInclusion F') (isProperMap_subsetInclusion hF')).f n).hom d = c :=
    chainMap_subsetRestrictMap R M hF' hc
  set c' := ((chainMap R M j hj).f n).hom d
  have hsupp : IsSupportedIn R M F c' := by
    intro σ hσ
    change pushforwardFun ((TopCat.toSSet.map j).app _) d.1 σ ≠ 0 at hσ
    obtain ⟨σ', -, rfl⟩ := support_pushforwardFun_subset _ d.1 hσ
    rw [singularSimplexImage_map]
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  refine ⟨c', hsupp, ?_⟩
  apply Subtype.ext
  funext τ
  rw [restrictChainMap_apply_of_isSupportedIn R M V (hsupp.mono hFV)]
  change pushforwardFun ((TopCat.toSSet.map j).app _) d.1 _ = c.1 τ
  have e' : ⇑(ConcreteCategory.hom ((TopCat.toSSet.map j).app (op ⦋n⦌))) =
      ⇑(ConcreteCategory.hom ((TopCat.toSSet.map (clopenInclusion V)).app (op ⦋n⦌))) ∘
        ⇑(ConcreteCategory.hom ((TopCat.toSSet.map (subsetInclusion F')).app (op ⦋n⦌))) := by
    simp only [j, Functor.map_comp]
    rfl
  rw [e', pushforwardFun_comp_apply_of_injective (map_clopenInclusion_injective _ n)]
  exact congrFun (congrArg Subtype.val hd) τ

end support

section homotopySupport

variable (R : Type u) [CommRing R] (M : ModuleCat.{u} R) {X Y : TopCat.{u}}

/-- Evaluation of a negated integer combination of linear maps at a point. -/
lemma hom_neg_sum_zsmul_apply {A B : ModuleCat.{u} R} {ι : Type*} (s : Finset ι) (a : ι → ℤ)
    (φ : ι → (A ⟶ B)) (x : A) :
    (-∑ i ∈ s, a i • φ i).hom x = -∑ i ∈ s, a i • (φ i).hom x := by
  simp

/-- A simplex of `h c`, for the chain homotopy `h` of a proper homotopy `H`, lies in
`H([0, 1] × σ)` for a simplex `σ` of `c`. -/
lemma exists_of_chainMapHomotopy_hom_ne_zero {f g : X ⟶ Y} (hf : IsProperMap f)
    (hg : IsProperMap g) (H : TopCat.Homotopy f g) (hH : IsProperMap H) {k : ℕ}
    (c : (borelMooreChainComplex R M X).X k) {ω : (TopCat.toSSet.obj Y).obj (op ⦋k + 1⦌)}
    (hω : (((chainMapHomotopy R M hf hg H hH).hom k (k + 1)).hom c).1 ω ≠ 0) :
    ∃ σ, c.1 σ ≠ 0 ∧ singularSimplexImage Y ω ⊆ H '' (univ ×ˢ singularSimplexImage X σ) := by
  by_contra hne
  push Not at hne
  have key : ∀ i : Fin (k + 1),
      (((locallyFiniteSingularChainsHomotopy R M hf hg H hH).h i).hom c).1 ω = 0 := by
    intro i
    change pushforwardFun (H.toSSet.toSimplicialObjectHomotopy.h i) c.1 ω = 0
    refine finsum_eq_zero_of_forall_eq_zero fun σ ↦ ?_
    split_ifs with h
    · by_contra h'
      exact hne σ h' (h ▸ singularSimplexImage_homotopy_h_subset H i σ)
    · rfl
  apply hω
  have e : ((chainMapHomotopy R M hf hg H hH).hom k (k + 1)).hom c =
      -∑ i : Fin (k + 1), ((-1 : ℤ) ^ (i : ℕ)) •
        ((locallyFiniteSingularChainsHomotopy R M hf hg H hH).h i).hom c := by
    simp only [chainMapHomotopy, SimplicialObject.Homotopy.toChainHomotopy,
      SimplicialObject.Homotopy.ToChainHomotopy.hom, dite_true, eqToHom_refl, Category.comp_id]
    exact hom_neg_sum_zsmul_apply R _ _ _ _
  rw [e]
  erw [Submodule.coe_neg, Pi.neg_apply, Submodule.coe_sum, Finset.sum_apply, neg_eq_zero]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  erw [Submodule.coe_smul_of_tower, Pi.smul_apply, key i, smul_zero]

end homotopySupport

section deformN

variable (R : Type u) [CommRing R] (M : ModuleCat.{u} R) {Y : TopCat.{u}} [T2Space Y]
  {X : Set Y} (hX : IsClosed X) {N : Set Y} (hN : IsClosed N) {G : C(N × unitInterval, Y)}
  (hG : IsProperMap G) (hG0 : ∀ y, G (y, 0) = y) (hG1 : ∀ y, G (y, 1) ∈ X)
  (hGX : ∀ y : N, ∀ t, (y : Y) ∈ X → G (y, t) = y)

omit [T2Space Y] in
include hX in
/-- A chain supported in the closed set `X` is the push-forward of a chain of `X`. -/
lemma exists_eq_chainMap_subspaceInclusion {n : ℕ} {c : (borelMooreChainComplex R M Y).X n}
    (hc : IsSupportedIn R M X c) :
    ∃ a : (borelMooreChainComplex R M (TopCat.of X)).X n,
      c = ((chainMap R M (subspaceInclusion Y X) (isProperMap_subspaceInclusion hX)).f n).hom a :=
  exists_eq_chainMap_of_isSupportedIn hX hc

omit [T2Space Y] in
include hN hG hG0 hG1 hGX in
/-- **A chain of `N` with boundary in `X` is, up to a boundary, a chain of `X`**: the homotopy `G`
deforms it into `X`, and moves its boundary only inside `X`. -/
theorem exists_eq_d_add_of_isSupportedIn {n : ℕ} {b : (borelMooreChainComplex R M Y).X n}
    (hb : IsSupportedIn R M N b)
    (hdb : ∀ m, m + 1 = n → IsSupportedIn R M X (((borelMooreChainComplex R M Y).d n m).hom b)) :
    ∃ b' : (borelMooreChainComplex R M Y).X (n + 1),
      ∃ a' : (borelMooreChainComplex R M (TopCat.of X)).X n,
        b = ((borelMooreChainComplex R M Y).d (n + 1) n).hom b' +
          ((chainMap R M (subspaceInclusion Y X) (isProperMap_subspaceInclusion hX)).f n).hom
            a' := by
  obtain ⟨c, rfl⟩ := exists_eq_chainMap_of_isSupportedIn hN hb
  set h := fillChainHomotopy hG hN subset_rfl R M hG0 hG1
  have hend : ∀ (k : ℕ) (x : (borelMooreChainComplex R M (TopCat.of N)).X k),
      ((chainMap R M (fillEnd subset_rfl hG1 ≫ subspaceInclusion Y X)
        (isProperMap_of_properHomotopy_right _
          (isProperMap_fillHomotopy hG hN subset_rfl hG0 hG1))).f k).hom x =
      ((chainMap R M (subspaceInclusion Y X) (isProperMap_subspaceInclusion hX)).f k).hom
        (((chainMap R M (fillEnd subset_rfl hG1)
          (isProperMap_fillEnd hG hN subset_rfl hG0 hG1)).f k).hom x) := fun k x ↦ by
    rw [chainMap_comp R M _ _ (isProperMap_fillEnd hG hN subset_rfl hG0 hG1)
      (isProperMap_subspaceInclusion hX)]
    rfl
  rcases n with _ | k
  · refine ⟨(h.hom 0 1).hom c, ((chainMap R M (fillEnd subset_rfl hG1)
      (isProperMap_fillEnd hG hN subset_rfl hG0 hG1)).f 0).hom c, ?_⟩
    rw [← hend, ← MMP.ChainHomotopyAux.apply_zero h c]
    abel
  · have hsupp : IsSupportedIn R M X ((h.hom k (k + 1)).hom
        (((borelMooreChainComplex R M (TopCat.of N)).d (k + 1) k).hom c)) := by
      intro ω hω
      obtain ⟨σ, hσ, hω'⟩ := exists_of_chainMapHomotopy_hom_ne_zero R M _ _ _ _ _ hω
      have hσX : Subtype.val '' singularSimplexImage (TopCat.of N) σ ⊆ X := by
        have h1 := hdb k rfl ((TopCat.toSSet.map (subsetInclusion N)).app _ σ) (by
          have hc := (chainMap R M (subsetInclusion N) (isProperMap_subsetInclusion hN)).comm
            (k + 1) k
          have := congrArg (fun φ ↦ (φ.hom c).1 ((TopCat.toSSet.map (subsetInclusion N)).app _ σ))
            hc
          simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
          erw [this]
          change pushforwardFun _ _ _ ≠ 0
          rw [pushforwardFun_apply_of_injective (map_subsetInclusion_injective k)]
          exact hσ)
        rwa [singularSimplexImage_map_subsetInclusion] at h1
      refine hω'.trans ?_
      rintro _ ⟨⟨t, y⟩, ⟨-, hy⟩, rfl⟩
      have hyX : (y : Y) ∈ X := hσX ⟨y, hy, rfl⟩
      change G (⟨y.1, _⟩, t) ∈ X
      rw [hGX _ _ hyX]
      exact hyX
    obtain ⟨a'', ha''⟩ := exists_eq_chainMap_subspaceInclusion R M hX hsupp
    refine ⟨(h.hom (k + 1) (k + 2)).hom c, ((chainMap R M (fillEnd subset_rfl hG1)
      (isProperMap_fillEnd hG hN subset_rfl hG0 hG1)).f (k + 1)).hom c + a'', ?_⟩
    rw [map_add, ← hend, ← ha'', sub_eq_iff_eq_add.mp (MMP.ChainHomotopyAux.apply_succ h k c)]
    abel

end deformN

section chainHelpers

variable {R : Type u} [CommRing R] {C D : ChainComplex (ModuleCat.{u} R) ℕ}

/-- The composite of two differentials of a chain complex vanishes at every element. -/
lemma d_d_apply (i j k : ℕ) (x : C.X i) : (C.d j k).hom ((C.d i j).hom x) = 0 := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, C.d_comp_d]
  rfl

/-- A chain map commutes with the differentials, evaluated at an element. -/
lemma hom_f_d_apply (φ : C ⟶ D) (i j : ℕ) (x : C.X i) :
    (φ.f j).hom ((C.d i j).hom x) = (D.d i j).hom ((φ.f i).hom x) := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← φ.comm]
  rfl

end chainHelpers

section relative

variable (R : Type u) [CommRing R] (M : ModuleCat.{u} R) {Y : TopCat.{u}} [T2Space Y]
  {X : Set Y} (hX : IsClosed X) {N N' : Set Y} (hN : IsClosed N) (hN' : IsClosed N')
  (hXN' : X ⊆ interior N') (hN'N : N' ⊆ interior N) {G : C(N × unitInterval, Y)}
  (hG : IsProperMap G) (hG0 : ∀ y, G (y, 0) = y) (hG1 : ∀ y, G (y, 1) ∈ X)
  (hGX : ∀ y : N, ∀ t, (y : Y) ∈ X → G (y, t) = y)

/-- The cover `{interior N - X, U - N'}` of `U = Y - X`. -/
abbrev relCover (N N' : Set Y) : Set (Set (TopCat.of (complOpens hX))) :=
  {Subtype.val ⁻¹' interior N, Subtype.val ⁻¹' N'ᶜ}

omit [T2Space Y] in
include hXN' in
/-- The complement of `interior N'` is contained in `U = Y - X`. -/
lemma compl_interior_subset : (interior N')ᶜ ⊆ (complOpens hX : Set Y) :=
  fun _ hx hxX ↦ hx (hXN' hxX)

omit [T2Space Y] in
include hN' hN'N in
/-- Every simplex of the subdivision of a chain of `U` for `relCover` lies in `interior N` or
outside `N'`. -/
lemma relCover_small {n : ℕ} (c : (borelMooreChainComplex R M (TopCat.of (complOpens hX))).X n)
    {τ : (TopCat.toSSet.obj (TopCat.of (complOpens hX))).obj (op ⦋n⦌)}
    (hτ : (((smallChainMapLF R M (relCover hX N N')).f n).hom c).1 τ ≠ 0) :
    singularSimplexImage _ τ ⊆ Subtype.val ⁻¹' interior N ∨
      singularSimplexImage _ τ ⊆ Subtype.val ⁻¹' N'ᶜ := by
  refine smallChainMapLF_small_of_union R M (isOpen_interior.preimage continuous_subtype_val)
    (hN'.isOpen_compl.preimage continuous_subtype_val) ?_ n c hτ
  ext u
  simp only [mem_union, mem_preimage, mem_compl_iff, mem_univ, iff_true]
  by_contra h
  push Not at h
  exact h.1 (hN'N h.2)

omit [T2Space Y] in
include hN' hN'N in
/-- The part of the subdivision of a chain of `U` for `relCover` on the simplices not contained in
`N` lies outside `interior N'`. -/
lemma isSupportedIn_chainPart_compl_relCover {n : ℕ}
    (c : (borelMooreChainComplex R M (TopCat.of (complOpens hX))).X n) :
    IsSupportedIn R M (Subtype.val ⁻¹' (interior N')ᶜ : Set (TopCat.of (complOpens hX)))
      ((chainPart R M ({τ | singularSimplexImage _ τ ⊆ Subtype.val ⁻¹' N} :
        Set ((TopCat.toSSet.obj (TopCat.of (complOpens hX))).obj (op ⦋n⦌)))ᶜ).hom
          (((smallChainMapLF R M (relCover hX N N')).f n).hom c)) := by
  intro τ hτ
  obtain ⟨hτ', hΨτ⟩ := mem_of_chainPart_ne_zero hτ
  rcases relCover_small R M hX hN' hN'N c hΨτ with h | h
  · exact absurd (h.trans (preimage_mono interior_subset)) hτ'
  · exact h.trans (preimage_mono (compl_subset_compl.2 interior_subset))

/-- The boundary identity behind (I): if `ρ (b₁ + b₂) = ∂ e`, and `eY`, `gY` restrict to the part
`e'` of the subdivision `e'' + e'` of `e` and to the subdivision homotopy of `ρ b₂`, then
`ρ (b₁ + (b₂ - ∂ eY - ∂ gY)) = ∂ (e'' + D (ρ b₁))`. -/
lemma restrictChainMap_add_sub_d_sub_d_eq_d (V : TopologicalSpace.Opens Y)
    (𝒰 : Set (Set (TopCat.of V))) {n : ℕ} {b₁ b₂ : (borelMooreChainComplex R M Y).X n}
    {eY gY : (borelMooreChainComplex R M Y).X (n + 1)}
    {e e' e'' : (borelMooreChainComplex R M (TopCat.of V)).X (n + 1)}
    (hΨe : e'' + e' = ((smallChainMapLF R M 𝒰).f (n + 1)).hom e)
    (he : ((restrictChainMap R M V).f n).hom (b₁ + b₂) =
      ((borelMooreChainComplex R M (TopCat.of V)).d (n + 1) n).hom e)
    (heY : ((restrictChainMap R M V).f (n + 1)).hom eY = e')
    (hgY : ((restrictChainMap R M V).f (n + 1)).hom gY =
      (smallHomotopyMap R M 𝒰 n).hom (((restrictChainMap R M V).f n).hom b₂)) :
    ((restrictChainMap R M V).f n).hom
        (b₁ + (b₂ - ((borelMooreChainComplex R M Y).d (n + 1) n).hom eY -
          ((borelMooreChainComplex R M Y).d (n + 1) n).hom gY)) =
      ((borelMooreChainComplex R M (TopCat.of V)).d (n + 1) n).hom
        (e'' + (smallHomotopyMap R M 𝒰 n).hom (((restrictChainMap R M V).f n).hom b₁)) := by
  have h1 : ((restrictChainMap R M V).f n).hom (((borelMooreChainComplex R M Y).d (n + 1) n).hom
      eY) = ((borelMooreChainComplex R M (TopCat.of V)).d (n + 1) n).hom e' := by
    rw [hom_f_d_apply, heY]
  have h2 : ((restrictChainMap R M V).f n).hom (((borelMooreChainComplex R M Y).d (n + 1) n).hom
      gY) = ((borelMooreChainComplex R M (TopCat.of V)).d (n + 1) n).hom
        ((smallHomotopyMap R M 𝒰 n).hom (((restrictChainMap R M V).f n).hom b₂)) := by
    rw [hom_f_d_apply, hgY]
  have h3 : ((borelMooreChainComplex R M (TopCat.of V)).d (n + 1) n).hom e =
      ((borelMooreChainComplex R M (TopCat.of V)).d (n + 1) n).hom e' +
      ((borelMooreChainComplex R M (TopCat.of V)).d (n + 1) n).hom e'' +
      ((borelMooreChainComplex R M (TopCat.of V)).d (n + 1) n).hom
        ((smallHomotopyMap R M 𝒰 n).hom (((restrictChainMap R M V).f n).hom b₁)) +
      ((borelMooreChainComplex R M (TopCat.of V)).d (n + 1) n).hom
        ((smallHomotopyMap R M 𝒰 n).hom (((restrictChainMap R M V).f n).hom b₂)) := by
    conv_lhs => rw [eq_smallChainMapLF_add_succ R M 𝒰 n e]
    rw [← hΨe, ← he]
    simp only [map_add, d_d_apply]
    abel
  have h4 : ((restrictChainMap R M V).f n).hom b₁ + ((restrictChainMap R M V).f n).hom b₂ =
      ((borelMooreChainComplex R M (TopCat.of V)).d (n + 1) n).hom e := by
    rw [← map_add, he]
  rw [h3, ← sub_eq_zero] at h4
  simp only [map_add, map_sub, h1, h2]
  rw [← sub_eq_zero, ← h4]
  abel

include hN' hXN' hN'N in
/-- A chain of `Y` each of whose simplices lies in `interior N` or outside `N'`, and whose
restriction to `U` is a boundary, is a chain supported in `N` up to a boundary of `Y`. -/
theorem exists_isSupportedIn_add_d_of_small {n : ℕ} (b : (borelMooreChainComplex R M Y).X n)
    (hsmall : ∀ σ, b.1 σ ≠ 0 → singularSimplexImage Y σ ⊆ interior N ∨
      singularSimplexImage Y σ ⊆ N'ᶜ)
    (e : (borelMooreChainComplex R M (TopCat.of (complOpens hX))).X (n + 1))
    (he : ((restrictChainMap R M (complOpens hX)).f n).hom b =
      ((borelMooreChainComplex R M (TopCat.of (complOpens hX))).d (n + 1) n).hom e) :
    ∃ c : (borelMooreChainComplex R M Y).X n, IsSupportedIn R M N c ∧
      ∃ g : (borelMooreChainComplex R M Y).X (n + 1),
        b = c + ((borelMooreChainComplex R M Y).d (n + 1) n).hom g := by
  set F : Set Y := (interior N')ᶜ
  have hF : IsClosed F := isOpen_interior.isClosed_compl
  have hFU : F ⊆ (complOpens hX : Set Y) := compl_interior_subset hX hXN'
  set sY : Set ((TopCat.toSSet.obj Y).obj (op ⦋n⦌)) := {σ | singularSimplexImage Y σ ⊆ N}
  set b₁ := (chainPart R M sY).hom b
  set b₂ := (chainPart R M sYᶜ).hom b
  have hb : b₁ + b₂ = b := chainPart_add_chainPart_compl R M sY b
  have hb₁ : IsSupportedIn R M N b₁ := isSupportedIn_chainPart b
  have hb₂ : IsSupportedIn R M F b₂ := by
    intro σ hσ
    obtain ⟨hσ', hbσ⟩ := mem_of_chainPart_ne_zero hσ
    rcases hsmall σ hbσ with h | h
    · exact absurd (h.trans interior_subset) hσ'
    · exact h.trans (compl_subset_compl.2 interior_subset)
  set 𝒱 := relCover hX N N'
  set sU : Set ((TopCat.toSSet.obj (TopCat.of (complOpens hX))).obj (op ⦋n + 1⦌)) :=
    {τ | singularSimplexImage _ τ ⊆ Subtype.val ⁻¹' N}
  set e' := (chainPart R M sUᶜ).hom (((smallChainMapLF R M 𝒱).f (n + 1)).hom e)
  have he'F : IsSupportedIn R M (Subtype.val ⁻¹' F : Set (TopCat.of (complOpens hX))) e' :=
    isSupportedIn_chainPart_compl_relCover R M hX hN' hN'N e
  obtain ⟨eY, heYF, heY⟩ := exists_restrictChainMap_eq hF hFU he'F
  obtain ⟨gY, hgYF, hgY⟩ := exists_restrictChainMap_eq hF hFU
    ((hb₂.restrictChainMap (complOpens hX)).smallHomotopyMap 𝒱)
  set c₂ := b₂ - ((borelMooreChainComplex R M Y).d (n + 1) n).hom eY -
    ((borelMooreChainComplex R M Y).d (n + 1) n).hom gY
  have hc₂F : IsSupportedIn R M F c₂ := (hb₂.sub heYF.d_of).sub hgYF.d_of
  have hρ := restrictChainMap_add_sub_d_sub_d_eq_d R M (complOpens hX) 𝒱 (b₁ := b₁)
    (chainPart_add_chainPart_compl R M sU _) (by rwa [hb]) heY hgY
  have hc₂N : IsSupportedIn R M N c₂ := by
    refine isSupportedIn_of_restrictChainMap (complOpens hX) (hc₂F.mono hFU) ?_
    have : ((restrictChainMap R M (complOpens hX)).f n).hom c₂ =
        ((restrictChainMap R M (complOpens hX)).f n).hom (b₁ + c₂) -
          ((restrictChainMap R M (complOpens hX)).f n).hom b₁ := by
      rw [map_add]
      abel
    rw [this, hρ]
    exact ((isSupportedIn_chainPart _).add ((hb₁.restrictChainMap (complOpens hX)).smallHomotopyMap
      𝒱)).d_of.sub (hb₁.restrictChainMap (complOpens hX))
  refine ⟨b₁ + c₂, hb₁.add hc₂N, eY + gY, ?_⟩
  rw [map_add, ← hb]
  simp only [c₂]
  abel

include hN hN' hXN' hN'N hG hG0 hG1 hGX in
/-- (I) for a chain each of whose simplices lies in `interior N` or outside `N'`. -/
theorem exists_eq_d_add_of_small {n : ℕ} (b : (borelMooreChainComplex R M Y).X n)
    (hsmall : ∀ σ, b.1 σ ≠ 0 → singularSimplexImage Y σ ⊆ interior N ∨
      singularSimplexImage Y σ ⊆ N'ᶜ)
    (hdb : ∀ m, m + 1 = n → IsSupportedIn R M X (((borelMooreChainComplex R M Y).d n m).hom b))
    (e : (borelMooreChainComplex R M (TopCat.of (complOpens hX))).X (n + 1))
    (he : ((restrictChainMap R M (complOpens hX)).f n).hom b =
      ((borelMooreChainComplex R M (TopCat.of (complOpens hX))).d (n + 1) n).hom e) :
    ∃ b' : (borelMooreChainComplex R M Y).X (n + 1),
      ∃ a' : (borelMooreChainComplex R M (TopCat.of X)).X n,
        b = ((borelMooreChainComplex R M Y).d (n + 1) n).hom b' +
          ((chainMap R M (subspaceInclusion Y X) (isProperMap_subspaceInclusion hX)).f n).hom
            a' := by
  obtain ⟨c, hc, g, rfl⟩ := exists_isSupportedIn_add_d_of_small R M hX hN' hXN' hN'N b hsmall e he
  obtain ⟨b', a', h'⟩ := exists_eq_d_add_of_isSupportedIn R M hX hN hG hG0 hG1 hGX hc
    fun m hm ↦ by simpa only [map_add, d_d_apply, add_zero] using hdb m hm
  refine ⟨b' + g, a', ?_⟩
  rw [h', map_add]
  abel

include hX in
/-- The restriction to `U = Y - X` of a chain supported in `X` is zero. -/
lemma restrictChainMap_eq_zero_of_isSupportedIn {n : ℕ} {c : (borelMooreChainComplex R M Y).X n}
    (hc : IsSupportedIn R M X c) : ((restrictChainMap R M (complOpens hX)).f n).hom c = 0 :=
  restrictChainMap_eq_zero_of_disjoint R M _ fun σ hσ ↦
    Set.disjoint_left.2 fun _ hx hxU ↦ hxU (hc σ hσ hx)

include hN hN' hXN' hN'N hG hG0 hG1 hGX in
/-- **(I)**: a chain `b` of `Y` with boundary in `X` whose restriction to `U` is a boundary is a
boundary of `Y` up to a chain of `X`. -/
theorem exists_eq_d_add_of_restrictChainMap_eq_d {n : ℕ} (b : (borelMooreChainComplex R M Y).X n)
    (hdb : ∀ m, m + 1 = n → IsSupportedIn R M X (((borelMooreChainComplex R M Y).d n m).hom b))
    (e : (borelMooreChainComplex R M (TopCat.of (complOpens hX))).X (n + 1))
    (he : ((restrictChainMap R M (complOpens hX)).f n).hom b =
      ((borelMooreChainComplex R M (TopCat.of (complOpens hX))).d (n + 1) n).hom e) :
    ∃ b' : (borelMooreChainComplex R M Y).X (n + 1),
      ∃ a' : (borelMooreChainComplex R M (TopCat.of X)).X n,
        b = ((borelMooreChainComplex R M Y).d (n + 1) n).hom b' +
          ((chainMap R M (subspaceInclusion Y X) (isProperMap_subspaceInclusion hX)).f n).hom
            a' := by
  set 𝒲 : Set (Set Y) := {interior N, N'ᶜ}
  have hcov : interior N ∪ N'ᶜ = univ := compl_subset_iff_union.1 (compl_subset_compl.2 hN'N)
  set bs := ((smallChainMapLF R M 𝒲).f n).hom b
  have hsmall : ∀ σ, bs.1 σ ≠ 0 → singularSimplexImage Y σ ⊆ interior N ∨
      singularSimplexImage Y σ ⊆ N'ᶜ := fun σ hσ ↦
    smallChainMapLF_small_of_union R M isOpen_interior hN'.isOpen_compl hcov n b hσ
  have hdbs : ∀ m, m + 1 = n →
      IsSupportedIn R M X (((borelMooreChainComplex R M Y).d n m).hom bs) := by
    intro m hm
    rw [← hom_f_d_apply]
    exact (hdb m hm).smallChainMapLF 𝒲
  set ρ := restrictChainMap R M (complOpens hX)
  rcases n with _ | k
  · have hb : b = bs + ((borelMooreChainComplex R M Y).d 1 0).hom
        ((smallHomotopyMap R M 𝒲 0).hom b) := eq_smallChainMapLF_add_zero R M 𝒲 b
    have hbs : bs = b - ((borelMooreChainComplex R M Y).d 1 0).hom
        ((smallHomotopyMap R M 𝒲 0).hom b) := eq_sub_of_add_eq hb.symm
    have he' : (ρ.f 0).hom bs = ((borelMooreChainComplex R M (TopCat.of (complOpens hX))).d 1 0).hom
        (e - (ρ.f 1).hom ((smallHomotopyMap R M 𝒲 0).hom b)) := by
      rw [hbs, map_sub, map_sub, he, ← hom_f_d_apply]
    obtain ⟨b', a', h'⟩ := exists_eq_d_add_of_small R M hX hN hN' hXN' hN'N hG hG0 hG1 hGX bs
      hsmall hdbs _ he'
    refine ⟨b' + (smallHomotopyMap R M 𝒲 0).hom b, a', hb.trans ?_⟩
    rw [h']
    simp only [map_add]
    abel
  · have hb : b = bs + ((borelMooreChainComplex R M Y).d (k + 2) (k + 1)).hom
        ((smallHomotopyMap R M 𝒲 (k + 1)).hom b) + (smallHomotopyMap R M 𝒲 k).hom
          (((borelMooreChainComplex R M Y).d (k + 1) k).hom b) :=
      eq_smallChainMapLF_add_succ R M 𝒲 k b
    have hX0 : IsSupportedIn R M X ((smallHomotopyMap R M 𝒲 k).hom
        (((borelMooreChainComplex R M Y).d (k + 1) k).hom b)) := (hdb k rfl).smallHomotopyMap 𝒲
    obtain ⟨a₀, ha₀⟩ := exists_eq_chainMap_subspaceInclusion R M hX hX0
    have hbs : bs = b - (smallHomotopyMap R M 𝒲 k).hom
          (((borelMooreChainComplex R M Y).d (k + 1) k).hom b) -
        ((borelMooreChainComplex R M Y).d (k + 2) (k + 1)).hom
          ((smallHomotopyMap R M 𝒲 (k + 1)).hom b) :=
      eq_sub_of_add_eq (eq_sub_of_add_eq hb.symm)
    have he' : (ρ.f (k + 1)).hom bs =
        ((borelMooreChainComplex R M (TopCat.of (complOpens hX))).d (k + 2) (k + 1)).hom
        (e - (ρ.f (k + 2)).hom ((smallHomotopyMap R M 𝒲 (k + 1)).hom b)) := by
      rw [hbs, map_sub, map_sub, map_sub, he, restrictChainMap_eq_zero_of_isSupportedIn R M hX hX0,
        sub_zero, ← hom_f_d_apply]
    obtain ⟨b', a', h'⟩ := exists_eq_d_add_of_small R M hX hN hN' hXN' hN'N hG hG0 hG1 hGX bs
      hsmall hdbs _ he'
    refine ⟨b' + (smallHomotopyMap R M 𝒲 (k + 1)).hom b, a' + a₀, hb.trans ?_⟩
    rw [h', ha₀]
    simp only [map_add]
    abel

/-- For a chain homotopy `h` from `φ` to `ψ` and a cycle `c`, `∂ (h c) = φ c - ψ c`. -/
lemma _root_.MMP.ChainHomotopyAux.d_hom_of_cycle {C D : ChainComplex (ModuleCat.{u} R) ℕ}
    {φ ψ : C ⟶ D} (h : Homotopy φ ψ) {k : ℕ} (c : C.X k)
    (hc : ∀ m, m + 1 = k → (C.d k m).hom c = 0) :
    (D.d (k + 1) k).hom ((h.hom k (k + 1)).hom c) = (φ.f k).hom c - (ψ.f k).hom c := by
  rcases k with _ | j
  · exact (MMP.ChainHomotopyAux.apply_zero h c).symm
  · rw [MMP.ChainHomotopyAux.apply_succ h j c, hc j rfl, map_zero, zero_add]

include hX in
/-- The restriction to `U` of the push-forward of a chain of a closed set `B ⊆ N - X` is its
push-forward through `A = N - X`. -/
lemma restrictChainMap_chainMap_subsetInclusion {B : Set Y} (hB : IsClosed B) (hBN : B ⊆ N)
    (hBX : B ⊆ Xᶜ) {k : ℕ} (β : (borelMooreChainComplex R M (TopCat.of B)).X k) :
    ((restrictChainMap R M (complOpens hX)).f k).hom
        (((chainMap R M (subsetInclusion B) (isProperMap_subsetInclusion hB)).f k).hom β) =
      ((chainMap R M (subsetInclusion (deformDomain hX N))
        (isProperMap_deformDomainInclusion hX hN)).f k).hom
        (((chainMap R M (fillIncl hX hBN hBX) (isProperMap_fillIncl hX hB hBN hBX)).f k).hom
          β) := by
  have hsupp := (isSupportedIn_chainMap_subsetInclusion (M := M) hB β).mono hBX
  apply Subtype.ext
  funext τ
  rw [restrictChainMap_apply_of_isSupportedIn R M _ hsupp, ← LinearMap.comp_apply,
    ← ModuleCat.hom_comp, ← HomologicalComplex.comp_f, ← chainMap_comp]
  change pushforwardFun ((TopCat.toSSet.map (subsetInclusion B)).app _) β.1 _ =
    pushforwardFun ((TopCat.toSSet.map (fillIncl hX hBN hBX ≫
      subsetInclusion (deformDomain hX N))).app _) β.1 τ
  have e : subsetInclusion B = (fillIncl hX hBN hBX ≫ subsetInclusion (deformDomain hX N)) ≫
      clopenInclusion (complOpens hX) := rfl
  have e' : ⇑(ConcreteCategory.hom ((TopCat.toSSet.map (subsetInclusion B)).app (op ⦋k⦌))) =
      ⇑(ConcreteCategory.hom ((TopCat.toSSet.map (clopenInclusion (complOpens hX))).app
        (op ⦋k⦌))) ∘
        ⇑(ConcreteCategory.hom ((TopCat.toSSet.map (fillIncl hX hBN hBX ≫
          subsetInclusion (deformDomain hX N))).app (op ⦋k⦌))) := by
    rw [e, Functor.map_comp]
    rfl
  rw [e', pushforwardFun_comp_apply_of_injective (map_clopenInclusion_injective _ k)]

include hN hXN' hG hG0 hG1 hGX in
/-- **(S)** in positive degree, given a lift `b₀` outside `interior N'` of the part of the
subdivision of `z` outside `N`. -/
theorem exists_restrictChainMap_sub_eq_d_succ {k : ℕ}
    (z : (borelMooreChainComplex R M (TopCat.of (complOpens hX))).X (k + 1))
    (hz : ∀ m, m + 1 = k + 1 →
      ((borelMooreChainComplex R M (TopCat.of (complOpens hX))).d (k + 1) m).hom z = 0)
    {z'' : (borelMooreChainComplex R M (TopCat.of (complOpens hX))).X (k + 1)}
    (hz''N : IsSupportedIn R M (Subtype.val ⁻¹' N : Set (TopCat.of (complOpens hX))) z'')
    {zA : (borelMooreChainComplex R M (TopCat.of (deformDomain hX N))).X (k + 1)}
    (hzA : z'' = ((chainMap R M (subsetInclusion (deformDomain hX N))
      (isProperMap_deformDomainInclusion hX hN)).f (k + 1)).hom zA)
    {b₀ : (borelMooreChainComplex R M Y).X (k + 1)} (hb₀F : IsSupportedIn R M (interior N')ᶜ b₀)
    (hp : z'' + ((restrictChainMap R M (complOpens hX)).f (k + 1)).hom b₀ =
      ((smallChainMapLF R M (relCover hX N N')).f (k + 1)).hom z) :
    ∃ b : (borelMooreChainComplex R M Y).X (k + 1),
      (∀ m, m + 1 = k + 1 → ∃ a : (borelMooreChainComplex R M (TopCat.of X)).X m,
        ((borelMooreChainComplex R M Y).d (k + 1) m).hom b =
          ((chainMap R M (subspaceInclusion Y X) (isProperMap_subspaceInclusion hX)).f m).hom a) ∧
      ∃ e : (borelMooreChainComplex R M (TopCat.of (complOpens hX))).X (k + 1 + 1),
        ((restrictChainMap R M (complOpens hX)).f (k + 1)).hom b - z =
          ((borelMooreChainComplex R M (TopCat.of (complOpens hX))).d (k + 1 + 1) (k + 1)).hom
            e := by
  set F : Set Y := (interior N')ᶜ
  have hF : IsClosed F := isOpen_interior.isClosed_compl
  have hFU : F ⊆ (complOpens hX : Set Y) := compl_interior_subset hX hXN'
  have hA : IsClosed (deformDomain hX N) := hN.preimage continuous_subtype_val
  have hzp := sub_smallChainMapLF_eq_d_of_cycle R M (relCover hX N N') z hz
  set β' := ((borelMooreChainComplex R M Y).d (k + 1) k).hom b₀
  have hdp : ((borelMooreChainComplex R M (TopCat.of (complOpens hX))).d (k + 1) k).hom
      (((smallChainMapLF R M (relCover hX N N')).f (k + 1)).hom z) = 0 := by
    rw [← hom_f_d_apply, hz k rfl, map_zero]
  have hρβ' : ((restrictChainMap R M (complOpens hX)).f k).hom β' =
      -((borelMooreChainComplex R M (TopCat.of (complOpens hX))).d (k + 1) k).hom z'' := by
    rw [hom_f_d_apply, eq_neg_iff_add_eq_zero, add_comm, ← map_add, hp, hdp]
  have hβ'N : IsSupportedIn R M N β' := by
    refine isSupportedIn_of_restrictChainMap (complOpens hX) (hb₀F.d_of.mono hFU) ?_
    rw [hρβ']
    exact hz''N.d_of.neg
  set B := N ∩ F
  have hB : IsClosed B := hN.inter hF
  have hBN : B ⊆ N := inter_subset_left
  have hBX : B ⊆ Xᶜ := inter_subset_right.trans hFU
  obtain ⟨β, hβ⟩ := exists_eq_chainMap_of_isSupportedIn hB
    (fun σ hσ ↦ subset_inter (hβ'N σ hσ) (hb₀F.d_of σ hσ) : IsSupportedIn R M B β')
  have hdβ : ∀ m, m + 1 = k → ((borelMooreChainComplex R M (TopCat.of B)).d k m).hom β = 0 := by
    intro m hm
    apply chainMap_subsetInclusion_injective R M hB m
    rw [map_zero, hom_f_d_apply, ← hβ]
    exact d_d_apply _ _ _ b₀
  set h := fillChainHomotopy hG hB hBN R M hG0 hG1
  have hdh := MMP.ChainHomotopyAux.d_hom_of_cycle R h β hdβ
  refine ⟨b₀ - (h.hom k (k + 1)).hom β, fun m hm ↦ ?_, -(deformOp R M hX hG hGX (k + 1)).hom zA -
    (smallHomotopyMap R M (relCover hX N N') (k + 1)).hom z, ?_⟩
  · obtain rfl : m = k := by lia
    refine ⟨((chainMap R M (fillEnd hBN hG1) (isProperMap_fillEnd hG hB hBN hG0 hG1)).f m).hom β,
      ?_⟩
    rw [map_sub, hdh, ← hβ, sub_sub_cancel, ← LinearMap.comp_apply, ← ModuleCat.hom_comp,
      ← HomologicalComplex.comp_f, ← chainMap_comp]
  · have hs := chainMap_deformDomain_eq_succ R M hX hG hGX hN hG0 hG1 k zA
    have hdzA : ((borelMooreChainComplex R M _).d (k + 1) k).hom zA =
        -((chainMap R M (fillIncl hX hBN hBX) (isProperMap_fillIncl hX hB hBN hBX)).f k).hom
          β := by
      apply chainMap_subsetInclusion_injective R M hA k
      rw [map_neg, ← restrictChainMap_chainMap_subsetInclusion R M hX hN hB hBN hBX, ← hβ, hρβ',
        neg_neg, hom_f_d_apply, ← hzA]
    rw [hdzA, map_neg, ← hzA] at hs
    have hr := restrictChainMap_fillChainHomotopy hX hG hB hBN hBX R M hGX hG0 hG1 k β
    rw [map_sub, hr, map_sub, map_neg, ← hzp, ← hp, hs]
    abel

include hN hN' hXN' hN'N hG hG0 hG1 hGX in
/-- **(S)**: every locally finite cycle `z` of `U` is, up to a boundary of `U`, the restriction of
a locally finite chain of `Y` with boundary in `X`. -/
theorem exists_restrictChainMap_sub_eq_d {n : ℕ}
    (z : (borelMooreChainComplex R M (TopCat.of (complOpens hX))).X n)
    (hz : ∀ m, m + 1 = n →
      ((borelMooreChainComplex R M (TopCat.of (complOpens hX))).d n m).hom z = 0) :
    ∃ b : (borelMooreChainComplex R M Y).X n,
      (∀ m, m + 1 = n → ∃ a : (borelMooreChainComplex R M (TopCat.of X)).X m,
        ((borelMooreChainComplex R M Y).d n m).hom b =
          ((chainMap R M (subspaceInclusion Y X) (isProperMap_subspaceInclusion hX)).f m).hom a) ∧
      ∃ e : (borelMooreChainComplex R M (TopCat.of (complOpens hX))).X (n + 1),
        ((restrictChainMap R M (complOpens hX)).f n).hom b - z =
          ((borelMooreChainComplex R M (TopCat.of (complOpens hX))).d (n + 1) n).hom e := by
  set F : Set Y := (interior N')ᶜ
  have hF : IsClosed F := isOpen_interior.isClosed_compl
  have hFU : F ⊆ (complOpens hX : Set Y) := compl_interior_subset hX hXN'
  set 𝒱 := relCover hX N N'
  set p := ((smallChainMapLF R M 𝒱).f n).hom z
  have hzp : z - p = ((borelMooreChainComplex R M (TopCat.of (complOpens hX))).d (n + 1) n).hom
      ((smallHomotopyMap R M 𝒱 n).hom z) := sub_smallChainMapLF_eq_d_of_cycle R M 𝒱 z hz
  set sU : Set ((TopCat.toSSet.obj (TopCat.of (complOpens hX))).obj (op ⦋n⦌)) :=
    {τ | singularSimplexImage _ τ ⊆ Subtype.val ⁻¹' N}
  set z'' := (chainPart R M sU).hom p
  set z' := (chainPart R M sUᶜ).hom p
  have hp : z'' + z' = p := chainPart_add_chainPart_compl R M sU _
  have hz'F : IsSupportedIn R M (Subtype.val ⁻¹' F : Set (TopCat.of (complOpens hX))) z' :=
    isSupportedIn_chainPart_compl_relCover R M hX hN' hN'N z
  have hz''N : IsSupportedIn R M (Subtype.val ⁻¹' N : Set (TopCat.of (complOpens hX))) z'' :=
    isSupportedIn_chainPart _
  obtain ⟨b₀, hb₀F, hb₀⟩ := exists_restrictChainMap_eq hF hFU hz'F
  have hA : IsClosed (deformDomain hX N) := hN.preimage continuous_subtype_val
  obtain ⟨zA, hzA⟩ := exists_eq_chainMap_of_isSupportedIn hA hz''N
  rcases n with _ | k
  · refine ⟨b₀, fun m hm ↦ absurd hm (Nat.succ_ne_zero m), -(deformOp R M hX hG hGX 0).hom zA -
      (smallHomotopyMap R M 𝒱 0).hom z, ?_⟩
    have h0 := chainMap_deformDomain_eq_zero R M hX hG hGX hN hG0 hG1 zA
    rw [← hzA] at h0
    rw [hb₀, map_sub, map_neg, ← h0, ← hzp, ← hp]
    abel
  · exact exists_restrictChainMap_sub_eq_d_succ R M hX hN hXN' hG hG0 hG1 hGX z hz hz''N hzA hb₀F
      (by rwa [hb₀])

end relative

section quasiIso

variable (R : Type u) [CommRing R] (M : ModuleCat.{u} R)

/-- **The relative quasi-isomorphism from a proper deformation.** If closed neighbourhoods
`N' ⊆ interior N` of `X` carry a proper homotopy `G : N × [0, 1] → Y` from the inclusion to a map
into `X`, fixing `X`, then `C^lf(Y) / C^lf(X) → C^lf(Y - X)` is a quasi-isomorphism. -/
theorem isRelativeQuasiIso_of_homotopy {Y : TopCat.{u}} [T2Space Y] {X : Set Y} (hX : IsClosed X)
    {N N' : Set Y} (hN : IsClosed N) (hN' : IsClosed N') (hXN' : X ⊆ interior N')
    (hN'N : N' ⊆ interior N) {G : C(N × unitInterval, Y)} (hG : IsProperMap G)
    (hG0 : ∀ y, G (y, 0) = y) (hG1 : ∀ y, G (y, 1) ∈ X)
    (hGX : ∀ y : N, ∀ t, (y : Y) ∈ X → G (y, t) = y) :
    IsRelativeQuasiIso R M hX := by
  refine isRelativeQuasiIso_of_forall R M hX
    (fun n z hz ↦ exists_restrictChainMap_sub_eq_d R M hX hN hN' hXN' hN'N hG hG0 hG1 hGX z hz)
    (fun n b hb e he ↦ exists_eq_d_add_of_restrictChainMap_eq_d R M hX hN hN' hXN' hN'N hG hG0
      hG1 hGX b (fun m hm ↦ ?_) e he)
  obtain ⟨a, ha⟩ := hb m hm
  rw [ha]
  exact isSupportedIn_chainMap_subsetInclusion hX a

/-- **The relative quasi-isomorphism in Fulton's setting.** If `Y` is locally contractible with a
closed imbedding in some `ℝᴺ`, and `X ⊆ Y` is closed and locally contractible, then
`C^lf(Y) / C^lf(X) → C^lf(Y - X)` is a quasi-isomorphism. -/
theorem isRelativeQuasiIso_of_isClosedEmbedding {Y : TopCat.{u}} {n : ℕ}
    {F : Y → EuclideanSpace ℝ (Fin n)} (hF : IsClosedEmbedding F) {X : Set Y} (hX : IsClosed X)
    (hXc : ∀ x : X, (𝓝 x).HasBasis (fun V : Set X ↦ IsOpen V ∧ x ∈ V ∧ ContractibleSpace V) id)
    (hYc : ∀ y : Y, (𝓝 y).HasBasis (fun V : Set Y ↦ IsOpen V ∧ y ∈ V ∧ ContractibleSpace V) id) :
    haveI : T2Space Y := hF.isEmbedding.t2Space
    IsRelativeQuasiIso R M hX := by
  have : T2Space Y := hF.isEmbedding.t2Space
  obtain ⟨N, hN, hXN, -, r, -, -, G, hG, hG0, hG1, hGX, -⟩ :=
    exists_isClosed_isProperMap_retraction_homotopy hF hX hXc hYc Filter.univ_mem
  obtain ⟨N', hN', hXN', hN'N, -⟩ := exists_isClosed_isProperMap_retraction_homotopy hF hX hXc hYc
    (isOpen_interior.mem_nhdsSet.2 hXN)
  exact isRelativeQuasiIso_of_homotopy R M hX hN hN' hXN' hN'N hG hG0
    (fun y ↦ (hG1 y).symm ▸ (r y).2) hGX

end quasiIso

end borelMooreHomology

end MMP
