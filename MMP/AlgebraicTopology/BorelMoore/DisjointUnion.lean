module

public import MMP.AlgebraicTopology.BorelMoore.Restriction
public import MMP.AlgebraicTopology.BorelMoore.Pushforward
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
/-!
# Borel–Moore homology of a finite disjoint union (Fulton, §19.1)

Let a Hausdorff space `X` be the disjoint union of finitely many open subsets `X₁, …, X_m`, with
inclusions `ι_l`. Each `X_l` is then also closed, so `ι_l` is proper, and the image of a singular
simplex, being connected, lies in exactly one `X_l`. Restricting a simplex `σ` to an open and
closed subset `U` involves no subdivision: `σ|_U` is `σ` if `σ` lies in `U` and `0` otherwise.
Hence on locally finite chains `c ↦ (c|_{X_l})_l` and `(c_l)_l ↦ ∑_l ι_{l*} c_l` are mutually
inverse, and so

`⨁_l H_j X_l → H_j X`, `(a_l)_l ↦ ∑_l ι_{l*} a_l`

is an isomorphism with inverse `a ↦ (a|_{X_l})_l`.

## Main definitions

* `MMP.borelMooreHomology.clopenInclusion`: the inclusion of an open and closed
  subset, a morphism of `TopCat`.
* `MMP.borelMooreHomology.disjointUnionIso`: the isomorphism
  `⨁_l H_j X_l ≅ H_j X`.

## Main results

* `MMP.borelMooreHomology.restrictKernel_of_isClopen`: restricting a simplex to an
  open and closed subset keeps it or kills it.
* `MMP.borelMooreHomology.pushforward_restrict_self`,
  `pushforward_restrict_of_disjoint`, `sum_restrict_pushforward`: `ι_l^* ι_{l*} = 1`,
  `ι_m^* ι_{l*} = 0` for `l ≠ m`, and `∑_l ι_{l*} ι_l^* = 1`.

## Implementation notes

The space is assumed Hausdorff, as the restriction `MMP.borelMooreHomology.restrict`
is defined for Hausdorff spaces (Fulton's spaces are). The direct sum is the categorical
biproduct in `ModuleCat R`, whose finite biproducts are indexed by finite types in `Type`;
a finite family `X₁, …, X_m` is indexed by `Fin m`. The open subsets are only assumed pairwise
disjoint and covering: each is then closed (`isClopen_of_disjoint_cover`).

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1 and Example 19.1.1.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicTopology Opposite Topology Set Simplicial Function

universe u

namespace MMP

namespace borelMooreHomology

open SingularChain LocallyFiniteChain

section chains

variable {R : Type*} [CommRing R] {Y : Type*} [TopologicalSpace Y] {U : Set Y}

/-- No bad chains come from a chain inside `U`. -/
lemma badChain_eq_zero_of_mem_inside {N n : ℕ} {c : Chain R Y n} (hc : c ∈ inside R n U) :
    badChain R U N n c = 0 := by
  rw [badChain, LinearMap.comp_apply, badProj_eq_zero_of_mem_inside hc, map_zero]

/-- The homotopy `towardsHomotopy` vanishes on chains inside `U`. -/
lemma towardsHomotopy_eq_zero_of_mem_inside {N n : ℕ} {c : Chain R Y n}
    (hc : c ∈ inside R n U) : towardsHomotopy R U N n c = 0 := by
  simp [towardsHomotopy, badChain_eq_zero_of_mem_inside hc]

/-- `ρ_N` is the identity on chains inside `U`. -/
lemma towardsChainMap_eq_self_of_mem_inside {N n : ℕ} {c : Chain R Y n}
    (hc : c ∈ inside R n U) : towardsChainMap R U N n c = c := by
  cases n with
  | zero => rw [towardsChainMap_zero_apply, towardsHomotopy_eq_zero_of_mem_inside hc, map_zero,
      sub_zero]
  | succ n => rw [towardsChainMap_succ_apply, towardsHomotopy_eq_zero_of_mem_inside hc,
      towardsHomotopy_eq_zero_of_mem_inside (bd_mem_inside hc), map_zero, sub_zero, sub_zero]

/-- The projection `goodProj` is the identity on chains inside `U`. -/
lemma goodProj_eq_self_of_mem_inside {n : ℕ} {c : Chain R Y n} (hc : c ∈ inside R n U) :
    goodProj R U n c = c := by
  have h := goodProj_add_badProj (U := U) c
  rwa [badProj_eq_zero_of_mem_inside hc, add_zero] at h

/-- The restriction of a simplex lying in `U` is the simplex itself. -/
lemma restrCoeff_of_range_subset {n : ℕ} {σ : Simplex Y n} (hσ : range σ ⊆ U)
    (τ : Simplex Y n) : restrCoeff R U σ τ = Finsupp.single σ 1 τ := by
  have hin : Finsupp.single σ (1 : R) ∈ inside R n U :=
    Finsupp.single_mem_supported R _ hσ
  have hg : ∀ N, goodPart R U N σ = Finsupp.single σ 1 := fun N ↦ by
    rw [goodPart, towardsChainMap_eq_self_of_mem_inside hin, goodProj_eq_self_of_mem_inside hin]
  rw [restrCoeff_eq (N₀ := 0) (fun N _ ↦ by rw [hg N, hg 0]), hg 0]

/-- The restriction of a simplex missing `U` is zero. -/
lemma restrCoeff_of_disjoint {n : ℕ} {σ : Simplex Y n} (hσ : Disjoint (range σ) U)
    (τ : Simplex Y n) : restrCoeff R U σ τ = 0 := by
  by_contra h
  obtain ⟨y, hy⟩ := range_nonempty τ
  have := range_subset_of_restrCoeff_ne_zero h hy
  exact Set.disjoint_left.1 hσ this.1 this.2

end chains

section kernel

variable {Y : TopCat.{u}} (U : TopologicalSpace.Opens Y)

/-- The inclusion of an open subset `U`, as a morphism of `TopCat`. -/
def clopenInclusion : TopCat.of U ⟶ Y :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The image of a simplex `τ` of `U` under the inclusion, as a singular simplex of `Y`, is
`inclSimplex U τ`. -/
lemma toSSetObjEquiv_map_clopenInclusion {n : ℕ}
    (τ : (TopCat.toSSet.obj (TopCat.of U)).obj (op ⦋n⦌)) :
    (SingularCochain.simplexEquiv Y n ((TopCat.toSSet.map (clopenInclusion U)).app _ τ) : Simplex Y n) =
      inclSimplex U τ :=
  rfl

/-- The inclusion of `U` is injective on singular `n`-simplices. -/
lemma map_clopenInclusion_injective (n : ℕ) :
    Function.Injective ((TopCat.toSSet.map (clopenInclusion U)).app (op ⦋n⦌)) := fun τ τ' h ↦
  inclSimplex_injective U n (by
    rw [← toSSetObjEquiv_map_clopenInclusion, ← toSSetObjEquiv_map_clopenInclusion, h])

open Classical in
/-- **Restriction to an open and closed subset.** The restriction of a simplex `σ` to an open and
closed subset `U` is `σ` itself if `σ` lies in `U`, and `0` otherwise. -/
lemma restrictKernel_of_isClopen (hU : IsClopen (U : Set Y)) (n : ℕ)
    (σ : (TopCat.toSSet.obj Y).obj (op ⦋n⦌))
    (τ : (TopCat.toSSet.obj (TopCat.of U)).obj (op ⦋n⦌)) :
    restrictKernel U n σ τ =
      if (TopCat.toSSet.map (clopenInclusion U)).app _ τ = σ then 1 else 0 := by
  set σs : Simplex Y n := (SingularCochain.simplexEquiv Y n σ)
  have hiff : (TopCat.toSSet.map (clopenInclusion U)).app _ τ = σ ↔ inclSimplex U τ = σs := by
    rw [← toSSetObjEquiv_map_clopenInclusion]
    exact (SingularCochain.simplexEquiv Y n).injective.eq_iff.symm
  have hconn : IsPreconnected (range σs) :=
    isPreconnected_range σs.continuous
  by_cases hmeet : (range σs ∩ U).Nonempty
  · have hsub := hconn.subset_isClopen hU hmeet
    rw [restrictKernel, restrCoeff_of_range_subset hsub, Finsupp.single_apply]
    by_cases h : σs = inclSimplex U τ
    · rw [if_pos h, if_pos (hiff.2 h.symm)]
    · rw [if_neg h, if_neg (fun h' ↦ h (hiff.1 h').symm)]
  · have hdisj : Disjoint (range σs) U :=
      Set.disjoint_iff_inter_eq_empty.2 (Set.not_nonempty_iff_eq_empty.1 hmeet)
    rw [restrictKernel, restrCoeff_of_disjoint hdisj, if_neg]
    intro h
    obtain ⟨t⟩ : Nonempty (stdSimplex ℝ (Fin (n + 1))) := ⟨stdSimplex.vertex 0⟩
    exact hmeet ⟨σs t, ⟨t, rfl⟩, by
      rw [show σs = inclSimplex U τ from (hiff.1 h).symm]
      exact range_inclSimplex_subset U τ ⟨t, rfl⟩⟩

open Classical in
/-- The restriction of a locally finite chain `d` to an open and closed subset `U` takes the
value `d (ι ∘ τ)` at a simplex `τ` of `U`. -/
lemma kernelFun_restrictKernel_of_isClopen {M : Type*} [AddCommGroup M]
    (hU : IsClopen (U : Set Y)) (n : ℕ) (d : (TopCat.toSSet.obj Y).obj (op ⦋n⦌) → M)
    (τ : (TopCat.toSSet.obj (TopCat.of U)).obj (op ⦋n⦌)) :
    kernelFun (restrictKernel U n) d τ = d ((TopCat.toSSet.map (clopenInclusion U)).app _ τ) := by
  rw [kernelFun, finsum_eq_single _ ((TopCat.toSSet.map (clopenInclusion U)).app _ τ)
    (fun σ hσ ↦ by rw [restrictKernel_of_isClopen U hU, if_neg (Ne.symm hσ), zero_smul]),
    restrictKernel_of_isClopen U hU, if_pos rfl, one_smul]

/-- The image under the inclusion of a simplex of `U` lies in `U`. -/
lemma range_toSSetObjEquiv_map_clopenInclusion_subset {n : ℕ}
    (τ : (TopCat.toSSet.obj (TopCat.of U)).obj (op ⦋n⦌)) :
    range (SingularCochain.simplexEquiv Y n ((TopCat.toSSet.map (clopenInclusion U)).app _ τ) :
      Simplex Y n) ⊆ U := by
  rw [toSSetObjEquiv_map_clopenInclusion]
  exact range_inclSimplex_subset U τ

/-- A simplex lying in `U` comes from a simplex of `U`. -/
lemma mem_range_map_clopenInclusion {n : ℕ} {σ : (TopCat.toSSet.obj Y).obj (op ⦋n⦌)}
    (h : range (SingularCochain.simplexEquiv Y n σ : Simplex Y n) ⊆ U) :
    σ ∈ range ((TopCat.toSSet.map (clopenInclusion U)).app (op ⦋n⦌)) := by
  obtain ⟨τ, hτ⟩ := mem_range_inclSimplex U h
  exact ⟨τ, (SingularCochain.simplexEquiv Y n).injective (by rw [toSSetObjEquiv_map_clopenInclusion, hτ])⟩

/-- A simplex not lying in `U` does not come from a simplex of `U`. -/
lemma notMem_range_map_clopenInclusion {n : ℕ} {σ : (TopCat.toSSet.obj Y).obj (op ⦋n⦌)}
    (h : ¬ range (SingularCochain.simplexEquiv Y n σ : Simplex Y n) ⊆ U) :
    σ ∉ range ((TopCat.toSSet.map (clopenInclusion U)).app (op ⦋n⦌)) := by
  rintro ⟨τ, rfl⟩
  exact h (range_toSSetObjEquiv_map_clopenInclusion_subset U τ)

end kernel

section pushforwardFun

variable {S T M : Type*} [AddCommGroup M]

/-- For injective `φ`, the pushforward of `c` along `φ` takes the value `c σ` at `φ σ`. -/
lemma pushforwardFun_apply_of_injective {φ : S → T} (hφ : Function.Injective φ) (c : S → M)
    (σ : S) : pushforwardFun φ c (φ σ) = c σ := by
  classical
  rw [pushforwardFun, finsum_eq_single _ σ (fun σ' h ↦ if_neg (fun e ↦ h (hφ e))), if_pos rfl]

/-- The pushforward of `c` along `φ` vanishes outside the range of `φ`. -/
lemma pushforwardFun_apply_of_notMem_range {φ : S → T} (c : S → M) {τ : T}
    (h : τ ∉ range φ) : pushforwardFun φ c τ = 0 := by
  classical
  exact finsum_eq_zero_of_forall_eq_zero fun σ ↦ if_neg fun e ↦ h ⟨σ, e⟩

end pushforwardFun

section complex

variable (R : Type u) [CommRing R] (M : ModuleCat.{u} R) {Y : TopCat.{u}} [T2Space Y]

/-- In degree `n`, the chain map `chainMap R M f hf` sends a locally finite chain `c` to its
pushforward `pushforwardFun` along `f` on simplices. -/
lemma chainMap_f_apply_coe {X : TopCat.{u}} (f : X ⟶ Y) (hf : IsProperMap f) (n : ℕ)
    (c : (borelMooreChainComplex R M X).X n) :
    (((chainMap R M f hf).f n).hom c).1 = pushforwardFun ((TopCat.toSSet.map f).app _) c.1 :=
  rfl

/-- In degree `n`, the chain map `restrictChainMap R M U` sends a locally finite chain `c` to
`kernelFun (restrictKernel U n) c`. -/
lemma restrictChainMap_f_apply_coe (U : TopologicalSpace.Opens Y) (n : ℕ)
    (c : (borelMooreChainComplex R M Y).X n) :
    (((restrictChainMap R M U).f n).hom c).1 = kernelFun (restrictKernel U n) c.1 :=
  rfl

/-- On chains, `ι^* ι_* = 1` for an open and closed subset. -/
lemma chainMap_comp_restrictChainMap_self (U : TopologicalSpace.Opens Y)
    (hU : IsClopen (U : Set Y)) (hf : IsProperMap (clopenInclusion U)) :
    chainMap R M (clopenInclusion U) hf ≫ restrictChainMap R M U = 𝟙 _ := by
  ext n c : 3
  apply Subtype.ext
  funext τ
  change kernelFun (restrictKernel U n)
    (pushforwardFun ((TopCat.toSSet.map (clopenInclusion U)).app _) c.1) τ = c.1 τ
  rw [kernelFun_restrictKernel_of_isClopen U hU,
    pushforwardFun_apply_of_injective (map_clopenInclusion_injective U n)]

/-- On chains, `ι_V^* ι_{U*} = 0` for disjoint open and closed subsets `U`, `V`. -/
lemma chainMap_comp_restrictChainMap_of_disjoint (U V : TopologicalSpace.Opens Y)
    (hV : IsClopen (V : Set Y)) (hUV : Disjoint (U : Set Y) V)
    (hf : IsProperMap (clopenInclusion U)) :
    chainMap R M (clopenInclusion U) hf ≫ restrictChainMap R M V = 0 := by
  ext n c : 3
  apply Subtype.ext
  funext τ
  change kernelFun (restrictKernel V n)
    (pushforwardFun ((TopCat.toSSet.map (clopenInclusion U)).app _) c.1) τ = 0
  rw [kernelFun_restrictKernel_of_isClopen V hV]
  refine pushforwardFun_apply_of_notMem_range _ (notMem_range_map_clopenInclusion U fun h ↦ ?_)
  obtain ⟨t⟩ : Nonempty (stdSimplex ℝ (Fin (n + 1))) := ⟨stdSimplex.vertex 0⟩
  exact Set.disjoint_left.1 hUV (h ⟨t, rfl⟩)
    (range_toSSetObjEquiv_map_clopenInclusion_subset V τ ⟨t, rfl⟩)

variable {ι : Type*} [Fintype ι] (U : ι → TopologicalSpace.Opens Y)

/-- In a finite disjoint open cover, each member is closed. -/
lemma isClopen_of_disjoint_cover (hdisj : Pairwise (Disjoint on fun l ↦ (U l : Set Y)))
    (hcover : ∀ y, ∃ l, y ∈ U l) (l : ι) : IsClopen (U l : Set Y) := by
  classical
  refine ⟨?_, (U l).isOpen⟩
  have : (U l : Set Y)ᶜ = ⋃ m ∈ ({l}ᶜ : Set ι), (U m : Set Y) := by
    ext y
    simp only [mem_compl_iff, mem_iUnion, mem_compl_singleton_iff, exists_prop]
    constructor
    · intro hy
      obtain ⟨m, hm⟩ := hcover y
      exact ⟨m, fun h ↦ hy (h ▸ hm), hm⟩
    · rintro ⟨m, hm, hym⟩ hyl
      exact Set.disjoint_left.1 (hdisj hm) hym hyl
  rw [← isOpen_compl_iff, this]
  exact isOpen_biUnion fun m _ ↦ (U m).isOpen

/-- On chains, `∑_l ι_{l*} ι_l^* = 1` for a finite disjoint open cover. -/
lemma sum_restrictChainMap_comp_chainMap
    (hdisj : Pairwise (Disjoint on fun l ↦ (U l : Set Y))) (hcover : ∀ y, ∃ l, y ∈ U l)
    (hf : ∀ l, IsProperMap (clopenInclusion (U l))) :
    ∑ l, restrictChainMap R M (U l) ≫ chainMap R M (clopenInclusion (U l)) (hf l) = 𝟙 _ := by
  classical
  ext n c : 3
  apply Subtype.ext
  funext σ
  rw [show (∑ l, restrictChainMap R M (U l) ≫ chainMap R M (clopenInclusion (U l)) (hf l)).f n =
      ∑ l, (restrictChainMap R M (U l) ≫ chainMap R M (clopenInclusion (U l)) (hf l)).f n from
    map_sum (HomologicalComplex.Hom.fAddMonoidHom n) _ _]
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply,
    HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  erw [Submodule.coe_sum, Finset.sum_apply]
  change ∑ l, pushforwardFun ((TopCat.toSSet.map (clopenInclusion (U l))).app _)
    (kernelFun (restrictKernel (U l) n) c.1) σ = c.1 σ
  set σs : Simplex Y n := (SingularCochain.simplexEquiv Y n σ)
  obtain ⟨t⟩ : Nonempty (stdSimplex ℝ (Fin (n + 1))) := ⟨stdSimplex.vertex 0⟩
  obtain ⟨l₀, hl₀⟩ := hcover (σs t)
  have hsub : range σs ⊆ U l₀ := (isPreconnected_range σs.continuous).subset_isClopen
    (isClopen_of_disjoint_cover U hdisj hcover l₀) ⟨σs t, ⟨t, rfl⟩, hl₀⟩
  rw [Finset.sum_eq_single l₀ (fun l _ hl ↦ pushforwardFun_apply_of_notMem_range _
      (notMem_range_map_clopenInclusion (U l) fun h ↦
        Set.disjoint_left.1 (hdisj hl) (h ⟨t, rfl⟩) (hsub ⟨t, rfl⟩)))
    (fun h ↦ absurd (Finset.mem_univ _) h)]
  obtain ⟨τ, rfl⟩ := mem_range_map_clopenInclusion (U l₀) hsub
  rw [pushforwardFun_apply_of_injective (map_clopenInclusion_injective (U l₀) n),
    kernelFun_restrictKernel_of_isClopen (U l₀) (isClopen_of_disjoint_cover U hdisj hcover l₀)]

end complex

section homology

variable (R : Type u) [CommRing R] (M : ModuleCat.{u} R) {Y : TopCat.{u}} [T2Space Y]

/-- `ι^* ι_* = 1` on Borel–Moore homology, for an open and closed subset `U`. -/
lemma pushforward_restrict_self (U : TopologicalSpace.Opens Y) (hU : IsClopen (U : Set Y))
    (hf : IsProperMap (clopenInclusion U)) (j : ℤ) :
    pushforward R M (clopenInclusion U) hf j ≫ restrict R M U j = 𝟙 _ := by
  have h := HomologicalComplex.homologyMap_comp
    (HomologicalComplex.extendMap (chainMap R M (clopenInclusion U) hf)
      ComplexShape.embeddingDownNat)
    (HomologicalComplex.extendMap (restrictChainMap R M U) ComplexShape.embeddingDownNat) (-j)
  rw [← HomologicalComplex.extendMap_comp, chainMap_comp_restrictChainMap_self R M U hU hf,
    HomologicalComplex.extendMap_id, HomologicalComplex.homologyMap_id] at h
  exact h.symm

/-- `ι_V^* ι_{U*} = 0` on Borel–Moore homology, for disjoint open and closed `U`, `V`. -/
lemma pushforward_restrict_of_disjoint (U V : TopologicalSpace.Opens Y)
    (hV : IsClopen (V : Set Y)) (hUV : Disjoint (U : Set Y) V)
    (hf : IsProperMap (clopenInclusion U)) (j : ℤ) :
    pushforward R M (clopenInclusion U) hf j ≫ restrict R M V j = 0 := by
  have h := HomologicalComplex.homologyMap_comp
    (HomologicalComplex.extendMap (chainMap R M (clopenInclusion U) hf)
      ComplexShape.embeddingDownNat)
    (HomologicalComplex.extendMap (restrictChainMap R M V) ComplexShape.embeddingDownNat) (-j)
  rw [← HomologicalComplex.extendMap_comp,
    chainMap_comp_restrictChainMap_of_disjoint R M U V hV hUV hf,
    HomologicalComplex.extendMap_zero, HomologicalComplex.homologyMap_zero] at h
  exact h.symm

variable {ι : Type} [Fintype ι] (U : ι → TopologicalSpace.Opens Y)

/-- The inclusion of a member of a finite disjoint open cover is proper. -/
lemma isProperMap_clopenInclusion (hdisj : Pairwise (Disjoint on fun l ↦ (U l : Set Y)))
    (hcover : ∀ y, ∃ l, y ∈ U l) (l : ι) : IsProperMap (clopenInclusion (U l)) :=
  (isClopen_of_disjoint_cover U hdisj hcover l).isClosed.isClosedEmbedding_subtypeVal.isProperMap

/-- `∑_l ι_{l*} ι_l^* = 1` on Borel–Moore homology, for a finite disjoint open cover. -/
lemma sum_restrict_pushforward (hdisj : Pairwise (Disjoint on fun l ↦ (U l : Set Y)))
    (hcover : ∀ y, ∃ l, y ∈ U l) (hf : ∀ l, IsProperMap (clopenInclusion (U l))) (j : ℤ) :
    ∑ l, restrict R M (U l) j ≫ pushforward R M (clopenInclusion (U l)) (hf l) j = 𝟙 _ := by
  let F := ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} R) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) (-j)
  have hF : ∀ {A B : TopCat.{u}} (φ : borelMooreChainComplex R M A ⟶ borelMooreChainComplex R M B),
      F.map φ = HomologicalComplex.homologyMap
        (HomologicalComplex.extendMap φ ComplexShape.embeddingDownNat) (-j) := fun _ ↦ rfl
  have h : ∀ l, restrict R M (U l) j ≫ pushforward R M (clopenInclusion (U l)) (hf l) j =
      F.map (restrictChainMap R M (U l) ≫ chainMap R M (clopenInclusion (U l)) (hf l)) := by
    intro l
    rw [F.map_comp, hF, hF]
    rfl
  have e : ∑ l, F.map (restrictChainMap R M (U l) ≫ chainMap R M (clopenInclusion (U l)) (hf l)) =
      𝟙 _ := by
    rw [← F.map_sum, sum_restrictChainMap_comp_chainMap R M U hdisj hcover hf, F.map_id]
  exact (Finset.sum_congr rfl fun l _ ↦ h l).trans e

/-- **Borel–Moore homology of a finite disjoint union** (Fulton, §19.1 and Example 19.1.1). Let
the Hausdorff space `Y` be the disjoint union of finitely many open subsets `U l`, with
inclusions `ι_l`. Then `(a_l)_l ↦ ∑_l ι_{l*} a_l` is an isomorphism `⨁_l H_j (U l) ≅ H_j Y`,
with inverse `a ↦ (a|_{U l})_l`. -/
def disjointUnionIso (hdisj : Pairwise (Disjoint on fun l ↦ (U l : Set Y)))
    (hcover : ∀ y, ∃ l, y ∈ U l) (j : ℤ) :
    (⨁ fun l ↦ borelMooreHomology R M (TopCat.of (U l)) j) ≅ borelMooreHomology R M Y j where
  hom := biproduct.desc fun l ↦
    pushforward R M (clopenInclusion (U l)) (isProperMap_clopenInclusion U hdisj hcover l) j
  inv := biproduct.lift fun l ↦ restrict R M (U l) j
  hom_inv_id := by
    classical
    refine biproduct.hom_ext' _ _ fun l ↦ biproduct.hom_ext _ _ fun m ↦ ?_
    simp only [biproduct.ι_desc_assoc, Category.assoc, biproduct.lift_π, Category.comp_id]
    by_cases hlm : l = m
    · subst hlm
      rw [biproduct.ι_π_self, pushforward_restrict_self R M (U l)
        (isClopen_of_disjoint_cover U hdisj hcover l)]
    · rw [biproduct.ι_π_ne _ hlm, pushforward_restrict_of_disjoint R M (U l) (U m)
        (isClopen_of_disjoint_cover U hdisj hcover m) (hdisj hlm)]
  inv_hom_id :=
    biproduct.lift_desc.trans (sum_restrict_pushforward R M U hdisj hcover _ j)

/-- The `l`-th component of `disjointUnionIso` is the pushforward along the inclusion of `U l`. -/
@[simp]
lemma ι_disjointUnionIso_hom (hdisj : Pairwise (Disjoint on fun l ↦ (U l : Set Y)))
    (hcover : ∀ y, ∃ l, y ∈ U l) (j : ℤ) (l : ι) :
    biproduct.ι _ l ≫ (disjointUnionIso R M U hdisj hcover j).hom =
      pushforward R M (clopenInclusion (U l)) (isProperMap_clopenInclusion U hdisj hcover l) j :=
  biproduct.ι_desc _ _

/-- The `l`-th component of the inverse of `disjointUnionIso` is the restriction to `U l`. -/
@[simp]
lemma disjointUnionIso_inv_π (hdisj : Pairwise (Disjoint on fun l ↦ (U l : Set Y)))
    (hcover : ∀ y, ∃ l, y ∈ U l) (j : ℤ) (l : ι) :
    (disjointUnionIso R M U hdisj hcover j).inv ≫ biproduct.π _ l = restrict R M (U l) j :=
  biproduct.lift_π _ _

end homology

end borelMooreHomology

end MMP
