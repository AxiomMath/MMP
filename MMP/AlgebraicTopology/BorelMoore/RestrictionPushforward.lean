module

public import MMP.AlgebraicTopology.BorelMoore.Restriction
public import MMP.AlgebraicTopology.BorelMoore.Pushforward
/-!
# Restriction commutes with proper push-forward (Fulton, §19.1)

Let `f : X → Y` be a proper map of Hausdorff spaces, `U ⊆ Y` open, `U' = f⁻¹(U)` and
`f_U : U' → U` the restriction of `f`. Then `(f_* a)|_U = f_{U*}(a|_{U'})` for `a ∈ H_j X`.

On chains this is an identity. Barycentric subdivision, its homotopy and the boundary are natural
for post-composition with `f`, and a simplex `τ` of `X` lies in `U'` exactly when `f ∘ τ` lies in
`U`; so the chains `ρ_N` of the subdivision towards `U` and their good parts are natural:
`p_U ρ_N (f ∘ σ) = f_♯ (p_{U'} ρ_N σ)`. Passing to the limit, the coefficient of a simplex `τ'`
of `U` in `(f ∘ σ)|_U` is the sum of the coefficients in `σ|_{U'}` of the simplices `τ` of `U'`
with `f ∘ τ = τ'`; these lie in the compact set `f⁻¹(τ'(Δ))`, since `f` is proper, so the limits
are reached at a common stage. Summing over the simplices of a locally finite chain gives the
identity of chain maps.

## Main results

* `MMP.SingularChain.goodPart_postcomp`: naturality of the good parts.
* `MMP.SingularChain.restrCoeff_postcomp`: the coefficients of `(f ∘ σ)|_U`.
* `MMP.borelMooreHomology.chainMap_comp_restrictChainMap`: the identity on chains.
* `MMP.borelMooreHomology.pushforward_restrict`: `(f_* a)|_U = f_{U*}(a|_{U'})`.

## Implementation notes

`X` and `Y` are assumed Hausdorff, as the restriction
`MMP.borelMooreHomology.restrict` is defined for Hausdorff spaces (Fulton's spaces
are). `U'` is `TopologicalSpace.Opens.comap f U` and `f_U` is
`MMP.borelMooreHomology.restrictPreimage f U`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [A. Borel, J. C. Moore, *Homology theory for locally compact spaces*][borelmoore1960], §3.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicTopology Opposite Topology Set Simplicial Finsupp

universe u

namespace MMP

namespace SingularChain

section postcomp

variable {R : Type*} [CommRing R] {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

variable (f : C(X, Y))

open Classical in
/-- The coefficient of a simplex `τ` of `Y` in `f_♯ c` is the sum of the coefficients in `c` of
the simplices `σ` of `X` with `f ∘ σ = τ`. -/
lemma postcomp_apply {n : ℕ} (c : Chain R X n) (τ : Simplex Y n) :
    postcomp R f n c τ = ∑ σ ∈ c.support, if f.comp σ = τ then c σ else 0 := by
  classical
  rw [postcomp, lmapDomain_apply, mapDomain, Finsupp.sum, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [single_apply]

/-- Pushing a chain of the standard simplex forward along `σ` and then post-composing with `f`
is pushing it forward along `f ∘ σ`. -/
lemma postcomp_push {n : ℕ} (σ : Simplex X n) (k : ℕ)
    (c : VertexChain.Chain R (stdSimplex ℝ (Fin (n + 1))) (k + 1)) :
    postcomp R f k (push R σ k c) = push R (f.comp σ) k c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single w a =>
    rw [← mul_one a, ← smul_eq_mul, ← smul_single, map_smul, map_smul, map_smul, push_single,
      push_single, postcomp_single]
    rfl

/-- Barycentric subdivision commutes with post-composition with `f`. -/
lemma postcomp_subdiv {n : ℕ} (c : Chain R X n) :
    postcomp R f n (subdiv R n c) = subdiv R n (postcomp R f n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single σ a =>
    rw [← mul_one a, ← smul_eq_mul, ← smul_single]
    simp only [map_smul, postcomp_single]
    rw [subdiv_single, subdiv_single, postcomp_push]

/-- The subdivision homotopy commutes with post-composition with `f`. -/
lemma postcomp_subdivHomotopy {n : ℕ} (c : Chain R X n) :
    postcomp R f (n + 1) (subdivHomotopy R n c) = subdivHomotopy R n (postcomp R f n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single σ a =>
    rw [← mul_one a, ← smul_eq_mul, ← smul_single]
    simp only [map_smul, postcomp_single]
    rw [subdivHomotopy_single, subdivHomotopy_single, postcomp_push]

variable (U : Set Y)

/-- Post-composition with `f` carries the projection onto the simplices lying in `f⁻¹(U)` to the
projection onto the simplices lying in `U`. -/
lemma postcomp_goodProj {n : ℕ} (c : Chain R X n) :
    postcomp R f n (goodProj R (f ⁻¹' U) n c) = goodProj R U n (postcomp R f n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single σ a =>
    rw [← mul_one a, ← smul_eq_mul, ← smul_single]
    simp only [map_smul, postcomp_single]
    rw [goodProj_single, goodProj_single]
    congr 1
    have : range (f.comp σ) ⊆ U ↔ range σ ⊆ f ⁻¹' U := by
      simp only [range_subset_iff, ContinuousMap.comp_apply, mem_preimage]
    by_cases h : range σ ⊆ f ⁻¹' U
    · rw [if_pos h, if_pos (this.2 h), postcomp_single]
    · rw [if_neg h, if_neg (fun h' ↦ h (this.1 h')), map_zero]

/-- Post-composition with `f` carries the projection onto the simplices not lying in `f⁻¹(U)`
to the projection onto the simplices not lying in `U`. -/
lemma postcomp_badProj {n : ℕ} (c : Chain R X n) :
    postcomp R f n (badProj R (f ⁻¹' U) n c) = badProj R U n (postcomp R f n c) := by
  rw [badProj, badProj, LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.id_apply, map_sub, postcomp_goodProj]

/-- The bad part at stage `N` of the subdivision towards `U` commutes with post-composition
with `f`, the subdivision of a chain of `X` being taken towards `f⁻¹(U)`. -/
lemma postcomp_badChain (N n : ℕ) (c : Chain R X n) :
    postcomp R f n (badChain R (f ⁻¹' U) N n c) = badChain R U N n (postcomp R f n c) := by
  induction N with
  | zero => rw [badChain_zero, badChain_zero, postcomp_badProj]
  | succ N ih => rw [badChain_succ, badChain_succ, postcomp_badProj, postcomp_subdiv, ih]

/-- The homotopy at stage `N` of the subdivision towards `U` commutes with post-composition
with `f`, the subdivision of a chain of `X` being taken towards `f⁻¹(U)`. -/
lemma postcomp_towardsHomotopy (N n : ℕ) (c : Chain R X n) :
    postcomp R f (n + 1) (towardsHomotopy R (f ⁻¹' U) N n c) =
      towardsHomotopy R U N n (postcomp R f n c) := by
  induction N with
  | zero => rw [towardsHomotopy_zero, towardsHomotopy_zero, map_zero]
  | succ N ih => rw [towardsHomotopy_succ, towardsHomotopy_succ, map_add, ih,
      postcomp_subdivHomotopy, postcomp_badChain]

/-- The chain map `ρ_N` of the subdivision towards `U` commutes with post-composition with `f`,
the subdivision of a chain of `X` being taken towards `f⁻¹(U)`. -/
lemma postcomp_towardsChainMap (N n : ℕ) (c : Chain R X n) :
    postcomp R f n (towardsChainMap R (f ⁻¹' U) N n c) =
      towardsChainMap R U N n (postcomp R f n c) := by
  cases n with
  | zero => rw [towardsChainMap_zero_apply, towardsChainMap_zero_apply, map_sub, postcomp_bd,
      postcomp_towardsHomotopy]
  | succ n => rw [towardsChainMap_succ_apply, towardsChainMap_succ_apply, map_sub, map_sub,
      postcomp_bd, postcomp_towardsHomotopy, postcomp_towardsHomotopy, postcomp_bd]

/-- **Naturality of the good parts**: `p_U ρ_N (f ∘ σ) = f_♯ (p_{f⁻¹U} ρ_N σ)`. -/
lemma goodPart_postcomp (N : ℕ) {n : ℕ} (σ : Simplex X n) :
    goodPart R U N (f.comp σ) = postcomp R f n (goodPart R (f ⁻¹' U) N σ) := by
  rw [goodPart, goodPart, postcomp_goodProj, postcomp_towardsChainMap, postcomp_single]

end postcomp

section stable

variable {R : Type*} [CommRing R] {Y : Type*} [TopologicalSpace Y] [T2Space Y] {U : Set Y}

/-- The coefficients of the good parts of `σ` at the simplices meeting a compact subset `K` of
`U` stabilize at a common stage. -/
lemma exists_goodPart_stable (hU : IsOpen U) {n : ℕ} (σ : Simplex Y n) {K : Set Y}
    (hK : IsCompact K) (hKU : K ⊆ U) : ∃ N₀, ∀ τ : Simplex Y n, (range τ ∩ K).Nonempty →
      ∀ N ≥ N₀, restrCoeff R U σ τ = goodPart R U N σ τ := by
  obtain ⟨V, W, hV, -, hCV, hKW, hVW⟩ := separatedNhds_range_inter_compl hU σ hK hKU
  obtain ⟨N₀, h⟩ := eventually_goodPart_sub_mem_inside (R := R) hU σ hV hCV
  refine ⟨N₀, fun τ ⟨y, hy, hyK⟩ N hN ↦ ?_⟩
  have hnotV : ¬range τ ⊆ V := fun h ↦ Set.disjoint_left.1 hVW (h hy) (hKW hyK)
  have hstab : ∀ N ≥ N₀, goodPart R U N σ τ = goodPart R U N₀ σ τ := fun N hN ↦ by
    have h0 := eq_zero_of_mem_inside (goodProj_mem_inside (U := U) (h N hN).1) hnotV
    rwa [map_sub, Finsupp.sub_apply, sub_eq_zero] at h0
  rw [restrCoeff_eq hstab, hstab N hN]

end stable

section restrCoeff

variable {R : Type*} [CommRing R] {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [T2Space X] [T2Space Y] {f : C(X, Y)} {U : Set Y}

open Classical in
/-- **Restriction of `f ∘ σ`.** For a proper `f`, the coefficient of a simplex `τ'` of `U` in
`(f ∘ σ)|_U` is the sum of the coefficients in `σ|_{f⁻¹U}` of the simplices `τ` with
`f ∘ τ = τ'`. -/
lemma restrCoeff_postcomp (hf : IsProperMap f) (hU : IsOpen U) {n : ℕ} (σ : Simplex X n)
    {τ' : Simplex Y n} (hτ' : range τ' ⊆ U) :
    restrCoeff R U (f.comp σ) τ' =
      ∑ᶠ τ : Simplex X n, if f.comp τ = τ' then restrCoeff R (f ⁻¹' U) σ τ else 0 := by
  classical
  have hK : IsCompact (range τ') := isCompact_range τ'.continuous
  have hK' : IsCompact (f ⁻¹' range τ') := hf.isCompact_preimage hK
  obtain ⟨N₁, h₁⟩ := exists_goodPart_stable (R := R) hU (f.comp σ) hK hτ'
  obtain ⟨N₂, h₂⟩ := exists_goodPart_stable (R := R) (hU.preimage f.continuous) σ hK'
    (preimage_mono hτ')
  set N := max N₁ N₂
  obtain ⟨t⟩ : Nonempty (stdSimplex ℝ (Fin (n + 1))) := ⟨stdSimplex.vertex 0⟩
  have hmem : ∀ τ : Simplex X n, f.comp τ = τ' → (range τ ∩ f ⁻¹' range τ').Nonempty :=
    fun τ h ↦ ⟨τ t, ⟨t, rfl⟩, ⟨t, by rw [← h]; rfl⟩⟩
  rw [h₁ τ' ⟨τ' t, ⟨t, rfl⟩, ⟨t, rfl⟩⟩ N (le_max_left _ _), goodPart_postcomp, postcomp_apply,
    finsum_eq_sum_of_support_subset (s := (goodPart R (f ⁻¹' U) N σ).support)]
  · refine Finset.sum_congr rfl fun τ _ ↦ ?_
    split_ifs with h
    · rw [h₂ τ (hmem τ h) N (le_max_right _ _)]
    · rfl
  · intro τ hτ
    rw [Function.mem_support] at hτ
    split_ifs at hτ with h
    · rwa [Finset.mem_coe, Finsupp.mem_support_iff, ← h₂ τ (hmem τ h) N (le_max_right _ _)]
    · exact absurd rfl hτ

end restrCoeff

end SingularChain

namespace borelMooreHomology

open SingularChain LocallyFiniteChain

section sums

variable {S T S' T' M : Type*} [AddCommGroup M]

open Classical in
/-- The transform by a kernel `k` of the push-forward of `c` along `φ`, as a finite sum. -/
lemma kernelFun_pushforwardFun_eq_sum (k : T → T' → ℤ) (φ : S → T) (c : S → M) (τ' : T')
    (F : Finset S) (hF : ∀ σ, c σ ≠ 0 → k (φ σ) τ' ≠ 0 → σ ∈ F) :
    kernelFun k (pushforwardFun φ c) τ' = ∑ σ ∈ F, k (φ σ) τ' • c σ := by
  have h1 : ∀ σ', k σ' τ' • pushforwardFun φ c σ' =
      ∑ σ ∈ F, if φ σ = σ' then k σ' τ' • c σ else 0 := fun σ' ↦ by
    by_cases hk : k σ' τ' = 0
    · simp [hk]
    · rw [pushforwardFun_apply_eq_sum φ c σ' F (fun σ hc h ↦ hF σ hc (h ▸ hk)), Finset.smul_sum]
      refine Finset.sum_congr rfl fun σ _ ↦ ?_
      split_ifs <;> simp
  rw [kernelFun, finsum_congr h1, finsum_eq_sum_of_support_subset (s := F.image φ) _ (fun σ' h ↦ ?_)]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ hσ ↦ ?_
    rw [Finset.sum_ite_eq (F.image φ) (φ σ), if_pos (Finset.mem_image_of_mem φ hσ)]
  · by_contra hσ'
    apply h
    refine Finset.sum_eq_zero fun σ hσ ↦ ?_
    split_ifs with he
    · exact absurd (Finset.mem_coe.2 (he ▸ Finset.mem_image_of_mem φ hσ)) hσ'
    · rfl

open Classical in
/-- The push-forward along `ψ` of the transform of `c` by a kernel `k`, as a finite sum. -/
lemma pushforwardFun_kernelFun_eq_sum (k : S → S' → ℤ) (ψ : S' → T') (c : S → M) (τ' : T')
    (F : Finset S) (G : Finset S')
    (hFG : ∀ τ, ψ τ = τ' → ∀ σ, c σ ≠ 0 → k σ τ ≠ 0 → τ ∈ G ∧ σ ∈ F) :
    pushforwardFun ψ (kernelFun k c) τ' =
      ∑ σ ∈ F, (∑ τ ∈ G, if ψ τ = τ' then k σ τ else 0) • c σ := by
  have h1 : ∀ τ, ψ τ = τ' → kernelFun k c τ = ∑ σ ∈ F, k σ τ • c σ := fun τ h ↦
    finsum_eq_sum_of_support_subset _ fun σ hσ ↦
      (hFG τ h σ (smul_ne_zero_right hσ) (smul_ne_zero_left hσ)).2
  rw [pushforwardFun_apply_eq_sum ψ _ τ' G (fun τ hτ h ↦ ?_)]
  · simp_rw [Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ ↦ ?_
    split_ifs with h
    · exact h1 τ h
    · simp
  · obtain ⟨σ, hσ⟩ : ∃ σ, k σ τ • c σ ≠ 0 := by
      by_contra hne
      push Not at hne
      exact hτ (finsum_eq_zero_of_forall_eq_zero hne)
    exact (hFG τ h σ (smul_ne_zero_right hσ) (smul_ne_zero_left hσ)).1

end sums

section kernel

variable {X Y : TopCat.{u}} (f : X ⟶ Y) (U : TopologicalSpace.Opens Y)

/-- The restriction `f_U : f⁻¹(U) → U` of `f : X → Y` over an open subset `U` of `Y`. -/
def restrictPreimage :
    TopCat.of (TopologicalSpace.Opens.comap f.hom U) ⟶ TopCat.of U :=
  TopCat.ofHom ⟨fun x ↦ ⟨f x.1, x.2⟩, (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- The restriction `f_U : f⁻¹(U) → U` of a proper map `f` is proper. -/
lemma isProperMap_restrictPreimage (hf : IsProperMap f) :
    IsProperMap (restrictPreimage f U) :=
  hf.restrictPreimage U

/-- The singular simplex of `Y` underlying the image of a simplex `σ` of `X` under `f` is
`f ∘ σ`. -/
lemma toSSetObjEquiv_map {n : ℕ} (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) :
    (SingularCochain.simplexEquiv Y n ((TopCat.toSSet.map f).app _ σ)) =
      f.hom.comp (SingularCochain.simplexEquiv X n σ) :=
  rfl

/-- The image under `f_U` of a simplex `τ` of `f⁻¹(U)`, read as a simplex of `Y`, is `f ∘ τ`
with `τ` read as a simplex of `X`. -/
lemma inclSimplex_map_restrictPreimage {n : ℕ}
    (τ : (TopCat.toSSet.obj (TopCat.of (TopologicalSpace.Opens.comap f.hom U))).obj (op ⦋n⦌)) :
    inclSimplex U ((TopCat.toSSet.map (restrictPreimage f U)).app _ τ) =
      f.hom.comp (inclSimplex (TopologicalSpace.Opens.comap f.hom U) τ) :=
  rfl

variable [T2Space X] [T2Space Y]

open Classical in
/-- The kernel of the restriction to `U` of the push-forward of a simplex `σ` along a proper
map `f` is the push-forward along `f_U` of the kernel of its restriction to `f⁻¹(U)`. -/
lemma restrictKernel_map (hf : IsProperMap f) (n : ℕ) (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌))
    (τ' : (TopCat.toSSet.obj (TopCat.of U)).obj (op ⦋n⦌)) :
    restrictKernel U n ((TopCat.toSSet.map f).app _ σ) τ' =
      ∑ᶠ τ, if (TopCat.toSSet.map (restrictPreimage f U)).app _ τ = τ' then
        restrictKernel (TopologicalSpace.Opens.comap f.hom U) n σ τ else 0 := by
  set U' := TopologicalSpace.Opens.comap f.hom U
  rw [restrictKernel, toSSetObjEquiv_map,
    restrCoeff_postcomp (f := f.hom) hf U.isOpen _ (range_inclSimplex_subset U τ')]
  set g : Simplex X n → ℤ := fun τs ↦ if f.hom.comp τs = inclSimplex U τ' then
    restrCoeff ℤ (f.hom ⁻¹' U) (SingularCochain.simplexEquiv X n σ) τs else 0 with hg
  have hsupp : Function.support g ⊆ range (inclSimplex U' (n := n)) := fun τs h ↦ by
    rw [Function.mem_support, hg] at h
    beta_reduce at h
    split_ifs at h with he
    · refine mem_range_inclSimplex U' ?_
      rintro _ ⟨t, rfl⟩
      change f (τs t) ∈ U
      have := congrArg (fun s : Simplex Y n ↦ s t) he
      simp only [ContinuousMap.comp_apply] at this
      rw [this]
      exact range_inclSimplex_subset U τ' ⟨t, rfl⟩
    · exact absurd rfl h
  rw [← Set.indicator_eq_self.2 hsupp, ← finsum_mem_def,
    finsum_mem_range (inclSimplex_injective U' n)]
  refine finsum_congr fun τ ↦ ?_
  have hiff : (TopCat.toSSet.map (restrictPreimage f U)).app _ τ = τ' ↔
      f.hom.comp (inclSimplex U' τ) = inclSimplex U τ' := by
    rw [← inclSimplex_map_restrictPreimage]
    exact (inclSimplex_injective U n).eq_iff.symm
  rw [hg]
  beta_reduce
  by_cases h : f.hom.comp (inclSimplex U' τ) = inclSimplex U τ'
  · rw [if_pos h, if_pos (hiff.2 h)]
    rfl
  · rw [if_neg h, if_neg (fun h' ↦ h (hiff.1 h'))]

end kernel

section complex

variable (R : Type u) [CommRing R] (M : ModuleCat.{u} R) {X Y : TopCat.{u}} [T2Space X]
  [T2Space Y] (f : X ⟶ Y) (hf : IsProperMap f) (U : TopologicalSpace.Opens Y)

/-- **Restriction commutes with proper push-forward, on chains**: `(f_♯ c)|_U = f_{U♯}(c|_{f⁻¹U})`
for locally finite chains `c` of `X`. -/
lemma chainMap_comp_restrictChainMap :
    chainMap R M f hf ≫ restrictChainMap R M U =
      restrictChainMap R M (TopologicalSpace.Opens.comap f.hom U) ≫
        chainMap R M (restrictPreimage f U) (isProperMap_restrictPreimage f U hf) := by
  classical
  set U' := TopologicalSpace.Opens.comap f.hom U
  ext n c : 3
  apply Subtype.ext
  funext τ'
  change kernelFun (restrictKernel U n) (pushforwardFun ((TopCat.toSSet.map f).app _) c.1) τ' =
    pushforwardFun ((TopCat.toSSet.map (restrictPreimage f U)).app _)
      (kernelFun (restrictKernel U' n) c.1) τ'
  obtain ⟨t⟩ : Nonempty (stdSimplex ℝ (Fin (n + 1))) := ⟨stdSimplex.vertex 0⟩
  -- the compact set `K = f⁻¹(τ'(Δ))` of `X`, contained in `U'`
  set K : Set X := f ⁻¹' range (inclSimplex U τ') with hKdef
  have hK : IsCompact K := hf.isCompact_preimage (isCompact_range (inclSimplex U τ').continuous)
  have hKU' : K ⊆ U' := fun x hx ↦ by
    obtain ⟨s, hs⟩ := hx
    change f x ∈ U
    rw [← hs]
    exact range_inclSimplex_subset U τ' ⟨s, rfl⟩
  have hc : IsLocallyFiniteSet (singularSimplexImage X (n := op ⦋n⦌)) (Function.support c.1) :=
    c.2
  set S := (hc.finite_inter_compact hK).toFinset
  have hmemS : ∀ σ, c.1 σ ≠ 0 → (singularSimplexImage X σ ∩ K).Nonempty → σ ∈ S := fun σ h1 h2 ↦
    (Set.Finite.mem_toFinset _).2 ⟨h1, h2⟩
  -- the compact set `K' ⊆ U'`, `K` read in `U'`
  set K' : Set U' := Subtype.val ⁻¹' K
  have hK' : IsCompact K' := by
    rwa [Subtype.isCompact_iff, Set.image_preimage_eq_inter_range, Subtype.range_coe,
      Set.inter_eq_left.2 hKU']
  have hadm := isAdmissibleKernel_restrictKernel U' n
  let Tσ : (TopCat.toSSet.obj X).obj (op ⦋n⦌) → Finset _ := fun σ ↦
    ((hadm.isLocallyFiniteSet σ).finite_inter_compact hK').toFinset
  set G := S.biUnion Tσ
  -- a simplex of `U'` over `τ'` has image in `K'`
  have hover : ∀ τ, (TopCat.toSSet.map (restrictPreimage f U)).app _ τ = τ' →
      (singularSimplexImage (TopCat.of U') τ ∩ K').Nonempty := fun τ h ↦ by
    refine ⟨(SingularCochain.simplexEquiv (TopCat.of U') n τ) t, ⟨stdSimplexHomeo _ t, rfl⟩, ⟨t, ?_⟩⟩
    have := congrArg (fun s : Simplex Y n ↦ s t) (inclSimplex_map_restrictPreimage f U τ)
    rwa [h] at this
  have hFG : ∀ τ, (TopCat.toSSet.map (restrictPreimage f U)).app _ τ = τ' → ∀ σ, c.1 σ ≠ 0 →
      restrictKernel U' n σ τ ≠ 0 → τ ∈ G ∧ σ ∈ S := fun τ h σ hcσ hk ↦ by
    obtain ⟨y, hy, hyK⟩ := hover τ h
    have hσS : σ ∈ S := hmemS σ hcσ ⟨y.1, hadm.image_subset σ τ hk ⟨y, hy, rfl⟩, hyK⟩
    exact ⟨Finset.mem_biUnion.2 ⟨σ, hσS, (Set.Finite.mem_toFinset _).2 ⟨hk, hover τ h⟩⟩, hσS⟩
  have hF : ∀ σ, c.1 σ ≠ 0 → restrictKernel U n ((TopCat.toSSet.map f).app _ σ) τ' ≠ 0 →
      σ ∈ S := fun σ hcσ hk ↦ by
    refine hmemS σ hcσ ?_
    obtain ⟨s, hs⟩ :=
      ((isAdmissibleKernel_restrictKernel U n).image_subset _ τ' hk) ⟨_, ⟨stdSimplexHomeo _ t, rfl⟩, rfl⟩
    exact ⟨X.toSSetObjEquiv _ σ s, ⟨s, rfl⟩, ⟨t, hs.symm⟩⟩
  rw [kernelFun_pushforwardFun_eq_sum _ _ _ τ' S hF,
    pushforwardFun_kernelFun_eq_sum _ _ _ τ' S G hFG]
  refine Finset.sum_congr rfl fun σ hσ ↦ ?_
  have hcσ : c.1 σ ≠ 0 := ((Set.Finite.mem_toFinset _).1 hσ).1
  rw [restrictKernel_map f U hf n σ τ', finsum_eq_sum_of_support_subset (s := G) _ fun τ hτ ↦ ?_]
  rw [Function.mem_support] at hτ
  split_ifs at hτ with h
  · exact (hFG τ h σ hcσ hτ).1
  · exact absurd rfl hτ

/-- **Restriction commutes with proper push-forward** (Fulton, §19.1). Let `f : X → Y` be a
proper map of Hausdorff spaces, `U ⊆ Y` open, `U' = f⁻¹(U)` and `f_U : U' → U` the restriction
of `f`. Then `(f_* a)|_U = f_{U*}(a|_{U'})` for all `a ∈ H_j X`. -/
theorem pushforward_restrict (j : ℤ) :
    pushforward R M f hf j ≫ restrict R M U j =
      restrict R M (TopologicalSpace.Opens.comap f.hom U) j ≫
        pushforward R M (restrictPreimage f U) (isProperMap_restrictPreimage f U hf) j := by
  have h := HomologicalComplex.homologyMap_comp
    (HomologicalComplex.extendMap (chainMap R M f hf) ComplexShape.embeddingDownNat)
    (HomologicalComplex.extendMap (restrictChainMap R M U) ComplexShape.embeddingDownNat) (-j)
  have h' := HomologicalComplex.homologyMap_comp
    (HomologicalComplex.extendMap (restrictChainMap R M (TopologicalSpace.Opens.comap f.hom U))
      ComplexShape.embeddingDownNat)
    (HomologicalComplex.extendMap
      (chainMap R M (restrictPreimage f U) (isProperMap_restrictPreimage f U hf))
      ComplexShape.embeddingDownNat) (-j)
  rw [← HomologicalComplex.extendMap_comp, chainMap_comp_restrictChainMap,
    HomologicalComplex.extendMap_comp] at h
  exact h.symm.trans h'

/-- Elementwise form of `pushforward_restrict`: `(f_* a)|_U = f_{U*}(a|_{U'})`. -/
theorem restrict_pushforward_apply (j : ℤ) (a : borelMooreHomology R M X j) :
    restrict R M U j (pushforward R M f hf j a) =
      pushforward R M (restrictPreimage f U) (isProperMap_restrictPreimage f U hf) j
        (restrict R M (TopologicalSpace.Opens.comap f.hom U) j a) := by
  exact congrArg (fun φ ↦ φ.hom a) (pushforward_restrict R M f hf U j)

end complex

end borelMooreHomology

end MMP
