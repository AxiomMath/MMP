module

public import MMP.AlgebraicTopology.CapProduct.RestrictionHomotopy
public import MMP.AlgebraicTopology.CapProduct.RestrictionIntCast

/-!
# The cap product and restriction to an open subset: cycles

Let `U` be an open subset of a Hausdorff space `Y`, `φ` a `p`-cocycle and `z` a locally finite
`n`-cycle, `p + q = n`. Summing the homotopy identity of
`MMP.BorelMooreCap.restrFin_capFin_sub_capRestrCoeff_succ` over the simplices of
`z`, the restriction `(φ ∩ z)|_U` and the cap product `φ|_U ∩ z|_U` differ by the boundary of the
locally finite chain `h z` of `U`, `h z = ∑ z_σ h σ`; the terms `h (∂ σ)` add up to
`h (∂ z) = 0`.

## Main results

* `MMP.BorelMooreCap.exists_d_eq_restrictChainMap_capChain_sub`:
  `(φ ∩ z)|_U - φ|_U ∩ z|_U = ∂ u`, with `u` supported on the simplices of `z` on which `φ` does
  not vanish identically.
-/

@[expose] public noncomputable section

open CategoryTheory Set Finsupp Opposite Simplicial Topology

universe u

namespace MMP

open MMP

namespace BorelMooreCap

open SingularCochain SingularChain LocallyFiniteChain borelMooreHomology BorelMooreCross
  SingularCross

section finsum

variable {R : Type*} [CommRing R] {S T : Type*}

/-- Exchanging two finite sums, given finite sets containing the nonzero terms. -/
lemma finsum_mul_finsum_comm (a : T → R) (k : S → T → R) (c : S → R) (A : Finset S)
    (B : Finset T) (h : ∀ σ τ, a τ ≠ 0 → k σ τ ≠ 0 → c σ ≠ 0 → σ ∈ A ∧ τ ∈ B) :
    ∑ᶠ τ, a τ * ∑ᶠ σ, k σ τ * c σ = ∑ᶠ σ, (∑ᶠ τ, k σ τ * a τ) * c σ := by
  have h1 : ∀ τ, a τ * ∑ᶠ σ, k σ τ * c σ = ∑ σ ∈ A, a τ * (k σ τ * c σ) := fun τ ↦ by
    by_cases ha : a τ = 0
    · simp [ha]
    rw [finsum_eq_sum_of_support_subset (s := A) _ (fun σ hσ ↦ ?_), Finset.mul_sum]
    have := Function.mem_support.1 hσ
    exact (h σ τ ha (left_ne_zero_of_mul this) (right_ne_zero_of_mul this)).1
  have h2 : ∀ σ, (∑ᶠ τ, k σ τ * a τ) * c σ = ∑ τ ∈ B, a τ * (k σ τ * c σ) := fun σ ↦ by
    by_cases hc : c σ = 0
    · simp [hc]
    rw [finsum_eq_sum_of_support_subset (s := B) _ (fun τ hτ ↦ ?_), Finset.sum_mul]
    · exact Finset.sum_congr rfl fun τ _ ↦ by ring
    have := Function.mem_support.1 hτ
    exact (h σ τ (right_ne_zero_of_mul this) (left_ne_zero_of_mul this) hc).2
  have hB : ∀ τ, (∑ σ ∈ A, a τ * (k σ τ * c σ)) ≠ 0 → τ ∈ B := fun τ hτ ↦ by
    obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hτ
    exact (h σ τ (left_ne_zero_of_mul hσ) (left_ne_zero_of_mul (right_ne_zero_of_mul hσ))
      (right_ne_zero_of_mul (right_ne_zero_of_mul hσ))).2
  have hA : ∀ σ, (∑ τ ∈ B, a τ * (k σ τ * c σ)) ≠ 0 → σ ∈ A := fun σ hσ ↦ by
    obtain ⟨τ, -, hτ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hσ
    exact (h σ τ (left_ne_zero_of_mul hτ) (left_ne_zero_of_mul (right_ne_zero_of_mul hτ))
      (right_ne_zero_of_mul (right_ne_zero_of_mul hτ))).1
  rw [finsum_congr h1, finsum_congr h2,
    finsum_eq_sum_of_support_subset (s := B) _ (fun τ hτ ↦ hB τ hτ),
    finsum_eq_sum_of_support_subset (s := A) _ (fun σ hσ ↦ hA σ hσ), Finset.sum_comm]

open Classical in
/-- The push-forward `f_* g` at `τ` is the sum of `g σ` over the `σ` with `f σ = τ`. -/
lemma pushforwardFun_eq_finsum_mul (f : S → T) (g : S → R) (τ : T) :
    pushforwardFun f g τ = ∑ᶠ σ, (if f σ = τ then 1 else 0) * g σ := by
  classical
  exact finsum_congr fun σ ↦ by split_ifs <;> simp

open Classical in
/-- A sum against a push-forward is the sum against the composite. -/
lemma finsum_mul_pushforwardFun (k : T → R) (f : S → T) (g : S → R) (A : Finset S)
    (hA : ∀ σ, g σ ≠ 0 → k (f σ) ≠ 0 → σ ∈ A) :
    ∑ᶠ τ, k τ * pushforwardFun f g τ = ∑ᶠ σ, k (f σ) * g σ := by
  classical
  simp_rw [pushforwardFun_eq_finsum_mul]
  rw [finsum_mul_finsum_comm k _ g A (A.image f) (fun σ τ hk hi hg ↦ ?_)]
  · refine finsum_congr fun σ ↦ ?_
    rw [finsum_eq_single _ (f σ) (fun τ hτ ↦ by rw [if_neg (Ne.symm hτ), zero_mul]), if_pos rfl,
      one_mul]
  · have hfτ : f σ = τ := by
      by_contra h'
      exact hi (if_neg h')
    subst hfτ
    exact ⟨hA σ hg hk, Finset.mem_image_of_mem f (hA σ hg hk)⟩

end finsum

section kernel

variable {R : Type u} [CommRing R] {Y : TopCat.{u}} [T2Space Y] (U : TopologicalSpace.Opens Y)

/-- The inclusion into `Y` of a simplex of `U` commutes with the simplicial operator of `g`. -/
lemma inclSimplex_opS {a b : ℕ} (g : Fin (a + 1) → Fin (b + 1))
    (ν : Simp (TopCat.of U) b) :
    inclSimplex U (opS g ν) = (inclSimplex U ν).comp (smap g) := by
  change (⟨Subtype.val, continuous_subtype_val⟩ : C(U, Y)).comp (simplexEquiv _ a (opS g ν)) = _
  rw [simplexEquiv_opS]
  rfl

/-- The coefficient of the simplex `ν` of `U` in the homotopy `h σ`. -/
def capHomKernel (p q n : ℕ) (h : p + q = n + 1) (φ : Simplex Y p → R) (σ : Simp Y n)
    (ν : Simp (TopCat.of U) q) : R :=
  capHomCoeff R (U : Set Y) p q n h φ (simplexEquiv _ _ σ) (inclSimplex U ν)

/-- The homotopy `h c = ∑ c_σ h σ` of a locally finite chain, as a function on simplices of
`U`. -/
def capHomFun (p q n : ℕ) (h : p + q = n + 1) (φ : Simplex Y p → R) (c : Simp Y n → R)
    (ν : Simp (TopCat.of U) q) : R :=
  ∑ᶠ σ, capHomKernel U p q n h φ σ ν * c σ

variable {U}

/-- If the coefficient of `ν` in `h σ` is nonzero, the image of `ν` lies in the image of `σ`. -/
lemma range_subset_of_capHomKernel_ne_zero {p q n : ℕ} {h : p + q = n + 1}
    {φ : Simplex Y p → R} {σ : Simp Y n} {ν : Simp (TopCat.of U) q}
    (hne : capHomKernel U p q n h φ σ ν ≠ 0) : range (inclSimplex U ν) ⊆ range (toC σ) :=
  ((range_subset_of_capHomCoeff_ne_zero hne).trans inter_subset_left).trans
    (range_simplexEquiv σ).subset

/-- The simplices of `U` with nonzero coefficient in `h σ` form a locally finite set. -/
lemma isLocallyFiniteSet_capHomKernel (p q n : ℕ) (h : p + q = n + 1) (φ : Simplex Y p → R)
    (σ : Simp Y n) :
    IsLocallyFiniteSet (singularSimplexImage (TopCat.of U) (n := op ⦋q⦌))
      (Function.support (capHomKernel U p q n h φ σ)) := by
  intro x
  obtain ⟨G, hG, hxG, hfinG⟩ := exists_finite_capHomCoeff_ne_zero (R := R) (q := q) U.isOpen h φ
    (simplexEquiv _ _ σ) x.2
  refine ⟨Subtype.val ⁻¹' G, (hG.preimage continuous_subtype_val).mem_nhds hxG,
    (hfinG.preimage (inclSimplex_injective U q).injOn).subset ?_⟩
  rintro ν ⟨hν, y, hy, hyG⟩
  refine ⟨hν, y.1, ?_, hyG⟩
  rw [range_inclSimplex]
  exact ⟨y, hy, rfl⟩

/-- For a locally finite chain `c`, the support of the homotopy `h c` is locally finite. -/
lemma isLocallyFiniteSet_capHomFun (p q n : ℕ) (h : p + q = n + 1) (φ : Simplex Y p → R)
    {c : Simp Y n → R}
    (hc : IsLocallyFiniteSet (singularSimplexImage Y (n := op ⦋n⦌)) (Function.support c)) :
    IsLocallyFiniteSet (singularSimplexImage (TopCat.of U) (n := op ⦋q⦌))
      (Function.support (capHomFun U p q n h φ c)) := by
  intro x
  obtain ⟨V, hV, hfin⟩ := hc x.1
  choose W hW hWfin using fun σ ↦ isLocallyFiniteSet_capHomKernel (U := U) p q n h φ σ x
  refine ⟨Subtype.val ⁻¹' V ∩ ⋂ σ ∈ hfin.toFinset, W σ, Filter.inter_mem
    (continuous_subtype_val.continuousAt.preimage_mem_nhds hV)
    ((Filter.biInter_finset_mem _).2 fun σ _ ↦ hW σ), ?_⟩
  refine (hfin.toFinset.finite_toSet.biUnion fun σ _ ↦ hWfin σ).subset ?_
  rintro ν ⟨hν, y, hy, hyV, hyW⟩
  obtain ⟨σ, hσ⟩ : ∃ σ, capHomKernel U p q n h φ σ ν * c σ ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hν (finsum_eq_zero_of_forall_eq_zero h')
  have hσF : σ ∈ hfin.toFinset := by
    rw [Finite.mem_toFinset]
    refine ⟨right_ne_zero_of_mul hσ, y.1, ?_, hyV⟩
    have := range_subset_of_capHomKernel_ne_zero (left_ne_zero_of_mul hσ)
    rw [range_inclSimplex] at this
    exact this ⟨y, hy, rfl⟩
  exact mem_iUnion₂.2 ⟨σ, hσF, left_ne_zero_of_mul hσ, y, hy, mem_iInter₂.1 hyW σ hσF⟩

end kernel

section coefficients

variable {R : Type u} [CommRing R] {Y : TopCat.{u}} [T2Space Y] {U : TopologicalSpace.Opens Y}

/-- The simplices of `c` meeting the simplex `ν` of `U`. -/
def meetFinset {n q : ℕ} (c : (BM R Y).X n) (ν : Simp (TopCat.of U) q) : Finset (Simp Y n) :=
  ((coeff_mem R c).finite_inter_compact (isCompact_range (inclSimplex U ν).continuous)).toFinset

/-- A simplex of `c` with nonzero coefficient whose image contains that of `ν` meets `ν`. -/
lemma mem_meetFinset {n q : ℕ} {c : (BM R Y).X n} {ν : Simp (TopCat.of U) q} {σ : Simp Y n}
    (hc : coeff R c σ ≠ 0) (hσ : range (inclSimplex U ν) ⊆ range (toC σ)) :
    σ ∈ meetFinset c ν := by
  rw [meetFinset, Finite.mem_toFinset]
  exact ⟨hc, _, hσ ⟨stdSimplex.vertex 0, rfl⟩, ⟨stdSimplex.vertex 0, rfl⟩⟩

/-- A sum `∑ K σ c_σ`, with `K σ ≠ 0` only when the image of `σ` contains that of `ν`, is the
finite sum over the simplices of `c` meeting `ν`. -/
lemma finsum_mul_coeff_eq_sum {n q : ℕ} (c : (BM R Y).X n) (ν : Simp (TopCat.of U) q)
    (K : Simp Y n → R) (hK : ∀ σ, K σ ≠ 0 → range (inclSimplex U ν) ⊆ range (toC σ)) :
    ∑ᶠ σ, K σ * coeff R c σ = ∑ σ ∈ meetFinset c ν, K σ * coeff R c σ :=
  finsum_eq_sum_of_support_subset _ fun σ hσ ↦ mem_meetFinset
    (right_ne_zero_of_mul (Function.mem_support.1 hσ)) (hK σ (left_ne_zero_of_mul hσ))

/-- The coefficients of the restriction of a locally finite chain to `U`. -/
lemma coeff_restrictChainMap_apply {k : ℕ} (c : (BM R Y).X k) (ν : Simp (TopCat.of U) k) :
    coeff R (((restrictChainMap R (ModuleCat.of R R) U).f k).hom c) ν =
      ∑ᶠ τ, (restrictKernel U k τ ν : R) * coeff R c τ :=
  finsum_congr fun τ ↦ zsmul_eq_mul _ _

/-- The restriction kernel, cast to `R`, is the restriction coefficient `restrCoeff`. -/
lemma restrictKernel_eq_restrCoeff {k : ℕ} (τ : Simp Y k) (ν : Simp (TopCat.of U) k) :
    (restrictKernel U k τ ν : R) = restrCoeff R U (simplexEquiv _ _ τ) (inclSimplex U ν) :=
  (restrCoeff_eq_intCast U.isOpen _ _).symm

/-- The coefficients of the restriction of a cap product. -/
lemma coeff_restrictChainMap_capChain (p q n : ℕ) (h : p + q = n) (φ : Simplex Y p → R)
    (z : (BM R Y).X n) (ν : Simp (TopCat.of U) q) :
    coeff R (((restrictChainMap R (ModuleCat.of R R) U).f q).hom (capChain R p q n h φ z)) ν =
      ∑ᶠ σ, restrFin R U (capFin R p q n h φ (single (simplexEquiv _ _ σ) 1)) (inclSimplex U ν) *
        coeff R z σ := by
  rw [coeff_restrictChainMap_apply,
    show coeff R (capChain R p q n h φ z) = pushforwardFun (opS (front q n (by omega)))
      (fun σ ↦ wt φ (back p n q (by omega)) σ * coeff R z σ) from rfl,
    finsum_mul_pushforwardFun _ _ _ (meetFinset z ν) (fun σ hg hk ↦ ?_)]
  · refine finsum_congr fun σ ↦ ?_
    rw [restrictKernel_eq_restrCoeff, capFin_single, restrFin_single,
      show simplexEquiv _ _ (opS (front q n (by omega)) σ) = (simplexEquiv _ _ σ).comp (smap (front q n (by omega))) from
        simplexEquiv_opS _ σ]
    change _ * (φ ((simplexEquiv _ _ σ).comp _) * _) = _
    ring
  · refine mem_meetFinset (right_ne_zero_of_mul hg) ?_
    rw [restrictKernel_eq_restrCoeff] at hk
    exact ((range_subset_of_restrCoeff_ne_zero hk).trans (inter_subset_left.trans (range_simplexEquiv _).subset)).trans
      (image_opS_subset _ σ)

/-- The image of a simplicial operator applied to a simplex `ν` of `U` lies in the image of `ν`. -/
lemma range_inclSimplex_opS_subset {a b : ℕ} (g : Fin (a + 1) → Fin (b + 1))
    (ν : Simp (TopCat.of U) b) : range (inclSimplex U (opS g ν)) ⊆ range (inclSimplex U ν) := by
  rw [inclSimplex_opS]
  exact range_comp_smap_subset _ _

open Classical in
/-- The coefficients of the cap product of `φ|_U` with a restriction. -/
lemma coeff_capChain_restrictChainMap (p q n : ℕ) (h : p + q = n) (φ : Simplex Y p → R)
    (z : (BM R Y).X n) (ν : Simp (TopCat.of U) q) :
    coeff R (capChain R p q n h (cochainPullback R (inclHom U) p φ)
        (((restrictChainMap R (ModuleCat.of R R) U).f n).hom z)) ν =
      ∑ᶠ σ, capRestrCoeff R U p q n h φ (simplexEquiv _ _ σ) (inclSimplex U ν) * coeff R z σ := by
  set w := ((restrictChainMap R (ModuleCat.of R R) U).f n).hom z
  set a : Simp (TopCat.of U) n → R := fun τ' ↦
    (if opS (front q n (by omega)) τ' = ν then 1 else 0) *
      wt (cochainPullback R (inclHom U) p φ) (back p n q (by omega)) τ'
  have hk := isAdmissibleKernel_restrictKernel U n
  set B := (meetFinset z ν).biUnion fun σ ↦
    ((hk.isLocallyFiniteSet σ).finite_inter_compact (isCompact_singularSimplexImage ν)).toFinset
  rw [show coeff R (capChain R p q n h (cochainPullback R (inclHom U) p φ) w) =
      pushforwardFun (opS (front q n (by omega))) (fun τ' ↦
        wt (cochainPullback R (inclHom U) p φ) (back p n q (by omega)) τ' * coeff R w τ') from rfl,
    pushforwardFun_eq_finsum_mul]
  have e : ∀ τ', (if opS (front q n (by omega)) τ' = ν then (1 : R) else 0) *
      (wt (cochainPullback R (inclHom U) p φ) (back p n q (by omega)) τ' * coeff R w τ') =
      a τ' * ∑ᶠ σ, (restrictKernel U n σ τ' : R) * coeff R z σ := fun τ' ↦ by
    rw [coeff_restrictChainMap_apply]
    simp only [a]
    ring
  rw [finsum_congr e, finsum_mul_finsum_comm a (fun σ τ' ↦ (restrictKernel U n σ τ' : R))
    (coeff R z) (meetFinset z ν) B (fun σ τ' ha hk' hz ↦ ?_)]
  · refine finsum_congr fun σ ↦ congrArg (· * coeff R z σ) ?_
    rw [capRestrCoeff, ← finsum_comp_eq_of_support_subset_range (inclSimplex_injective U n)
      (fun τ hτ ↦ ?_)]
    · refine finsum_congr fun τ' ↦ ?_
      rw [restrictKernel_eq_restrCoeff, capFin_single, Finsupp.single_apply, ← inclSimplex_opS,
        (inclSimplex_injective U q).eq_iff]
      simp only [a]
      split_ifs <;> first | (simp only [one_mul, mul_one]; rfl) | simp
    · exact mem_range_inclSimplex U
        ((range_subset_of_restrCoeff_ne_zero (left_ne_zero_of_mul hτ)).trans inter_subset_right)
  · have hb : opS (front q n (by omega)) τ' = ν := by
      by_contra h'
      exact ha (by simp only [a, if_neg h', zero_mul])
    have hk'' : restrictKernel U n σ τ' ≠ 0 := fun h0 ↦ hk' (by simp [h0])
    have hr := range_subset_of_restrCoeff_ne_zero hk''
    have hντ : range (inclSimplex U ν) ⊆ range (inclSimplex U τ') :=
      hb ▸ range_inclSimplex_opS_subset _ τ'
    have hσF := mem_meetFinset hz (hντ.trans (hr.trans (inter_subset_left.trans (range_simplexEquiv _).subset)))
    refine ⟨hσF, Finset.mem_biUnion.2 ⟨σ, hσF, (Finite.mem_toFinset _).2 ⟨hk'', ?_⟩⟩⟩
    obtain ⟨x, hx⟩ := nonempty_singularSimplexImage ν
    have hx' : x ∈ singularSimplexImage _ (opS (front q n (by omega)) τ') := by rw [hb]; exact hx
    exact ⟨x, image_opS_subset _ τ' hx', hx⟩

open Classical in
/-- The coefficient of `ν` in the `i`-th face of `h σ`, as a sum over the simplices of `Y` whose
`i`-th face is `ν`. -/
lemma finsum_capHomKernel_δ {p q n : ℕ} (h : p + (q + 1) = n + 1) (φ : Simplex Y p → R)
    (σ : Simp Y n) (ν : Simp (TopCat.of U) q) (i : Fin (q + 2)) :
    ∑ᶠ ν', capHomKernel U p (q + 1) n h φ σ ν' *
        (if (TopCat.toSSet.obj (TopCat.of U)).δ i ν' = ν then 1 else 0) =
      ∑ᶠ ω' : Simplex Y (q + 1), if ω'.comp (face q i) = inclSimplex U ν then
        capHomCoeff R U p (q + 1) n h φ (simplexEquiv _ _ σ) ω' else 0 := by
  rw [← finsum_comp_eq_of_support_subset_range (inclSimplex_injective U (q + 1)) (fun ω' hω' ↦ ?_)]
  · refine finsum_congr fun ν' ↦ ?_
    have hiff : (TopCat.toSSet.obj (TopCat.of U)).δ i ν' = ν ↔
        (inclSimplex U ν').comp (face q i) = inclSimplex U ν := by
      rw [← inclSimplex_δ]
      exact (inclSimplex_injective U q).eq_iff.symm
    by_cases hd : (TopCat.toSSet.obj (TopCat.of U)).δ i ν' = ν
    · rw [if_pos hd, if_pos (hiff.1 hd), mul_one]
      rfl
    · rw [if_neg hd, if_neg (fun h' ↦ hd (hiff.2 h')), mul_zero]
  · rw [Function.mem_support] at hω'
    split_ifs at hω' with h'
    · exact mem_range_inclSimplex U
        ((range_subset_of_capHomCoeff_ne_zero hω').trans inter_subset_right)
    · exact absurd rfl hω'

open Classical in
/-- The coefficients of the boundary of the homotopy `h z`. -/
lemma coeff_d_capHomFun {p q n : ℕ} (h : p + (q + 1) = n + 1) (φ : Simplex Y p → R)
    (z : (BM R Y).X n) (ν : Simp (TopCat.of U) q) :
    coeff R (((BM R (TopCat.of U)).d (q + 1) q).hom (ofCoeff R
        (capHomFun U p (q + 1) n h φ (coeff R z))
        (mem_lfChains.2 (isLocallyFiniteSet_capHomFun p (q + 1) n h φ
          (mem_lfChains.1 (coeff_mem R z)))))) ν =
      ∑ᶠ σ, (∑ i : Fin (q + 2), (-1 : R) ^ (i : ℕ) * ∑ᶠ ω' : Simplex Y (q + 1),
        if ω'.comp (face q i) = inclSimplex U ν then
          capHomCoeff R U p (q + 1) n h φ (simplexEquiv _ _ σ) ω' else 0) * coeff R z σ := by
  set F := meetFinset z ν
  set X : Fin (q + 2) → Simp Y n → R := fun i σ ↦ ∑ᶠ ν', capHomKernel U p (q + 1) n h φ σ ν' *
    (if (TopCat.toSSet.obj (TopCat.of U)).δ i ν' = ν then 1 else 0)
  have hXs : ∀ i σ, X i σ ≠ 0 → range (inclSimplex U ν) ⊆ range (toC σ) := fun i σ hX ↦ by
    obtain ⟨ν', hν'⟩ : ∃ ν', capHomKernel U p (q + 1) n h φ σ ν' *
        (if (TopCat.toSSet.obj (TopCat.of U)).δ i ν' = ν then 1 else 0) ≠ 0 := by
      by_contra h'
      push Not at h'
      exact hX (finsum_eq_zero_of_forall_eq_zero h')
    have hd : (TopCat.toSSet.obj (TopCat.of U)).δ i ν' = ν := by
      by_contra h'
      exact hν' (by rw [if_neg h', mul_zero])
    have h1 := range_subset_of_capHomKernel_ne_zero (left_ne_zero_of_mul hν')
    refine Subset.trans ?_ h1
    rw [← hd, inclSimplex_δ]
    rintro _ ⟨t, rfl⟩
    exact ⟨_, rfl⟩
  set B := F.biUnion fun σ ↦ ((isLocallyFiniteSet_capHomKernel (U := U) p (q + 1) n h φ
    σ).finite_inter_compact (isCompact_singularSimplexImage ν)).toFinset
  have hi : ∀ i, pushforwardFun ((TopCat.toSSet.obj (TopCat.of U)).δ i)
      (capHomFun U p (q + 1) n h φ (coeff R z)) ν = ∑ᶠ σ, X i σ * coeff R z σ := fun i ↦ by
    rw [pushforwardFun_eq_finsum_mul]
    refine finsum_mul_finsum_comm _ _ _ F B (fun σ ν' ha hk hz ↦ ?_)
    have hd : (TopCat.toSSet.obj (TopCat.of U)).δ i ν' = ν := by
      by_contra h'
      exact ha (if_neg h')
    have hsub : singularSimplexImage _ ν ⊆ singularSimplexImage _ ν' :=
      hd ▸ singularSimplexImage_map_subset _ ν'
    have h1 := range_subset_of_capHomKernel_ne_zero hk
    have hσF : σ ∈ F := mem_meetFinset hz (Subset.trans (by
      rw [range_inclSimplex, range_inclSimplex]; exact image_mono hsub) h1)
    refine ⟨hσF, Finset.mem_biUnion.2 ⟨σ, hσF, (Finite.mem_toFinset _).2 ⟨hk, ?_⟩⟩⟩
    obtain ⟨x, hx⟩ := nonempty_singularSimplexImage ν
    exact ⟨x, hsub hx, hx⟩
  rw [coeff_d, coeff_ofCoeff, Finset.sum_apply]
  simp only [Pi.smul_apply, hi]
  simp_rw [← finsum_capHomKernel_δ (U := U) h φ _ ν]
  rw [finsum_mul_coeff_eq_sum z ν _ (fun σ hσ ↦ ?_)]
  · rw [Finset.sum_congr rfl fun i _ ↦ by rw [finsum_mul_coeff_eq_sum z ν _ (hXs i)]]
    simp_rw [Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [zsmul_eq_mul]
    push_cast
    ring
  · obtain ⟨i, -, hi'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hσ
    exact hXs i σ (right_ne_zero_of_mul hi')

/-- For a cycle `z`, the terms `h (∂ σ)` add up to `h (∂ z) = 0`. -/
lemma finsum_capHomCoeff_face_mul_coeff_eq_zero {p q m : ℕ} (h : p + q = m + 1)
    (φ : Simplex Y p → R) (z : Cyc (R := R) Y (m + 1)) (ν : Simp (TopCat.of U) q) :
    ∑ᶠ σ, (∑ i : Fin (m + 2), (-1 : R) ^ (i : ℕ) *
      capHomCoeff R U p q m h φ ((simplexEquiv _ _ σ).comp (face m i)) (inclSimplex U ν)) * coeff R z.1 σ = 0 := by
  classical
  set ω := inclSimplex U ν
  set F := meetFinset z.1 ν
  set H' : Simp Y m → R := fun τ ↦ capHomCoeff R U p q m h φ (simplexEquiv _ _ τ) ω
  set δ : Fin (m + 2) → Simp Y (m + 1) → Simp Y m := fun i ↦ (TopCat.toSSet.obj Y).δ i
  have hH' : ∀ τ, H' τ ≠ 0 → range ω ⊆ range (toC τ) := fun τ hτ ↦
    (range_subset_of_capHomCoeff_ne_zero hτ).trans (inter_subset_left.trans (range_simplexEquiv _).subset)
  have hδ : ∀ i σ, range (toC (δ i σ)) ⊆ range (toC σ) := fun i σ ↦ by
    rintro _ ⟨t, rfl⟩
    exact ⟨_, rfl⟩
  have e0 : ∀ σ, (∑ i : Fin (m + 2), (-1 : R) ^ (i : ℕ) *
      capHomCoeff R U p q m h φ ((simplexEquiv _ _ σ).comp (face m i)) ω) =
      ∑ i : Fin (m + 2), (-1 : R) ^ (i : ℕ) * H' (δ i σ) := fun σ ↦ by
    simp only [H', δ, borelMooreHomology.toSSetObjEquiv_δ]
  simp_rw [e0]
  rw [finsum_mul_coeff_eq_sum z.1 ν _ (fun σ hσ ↦ by
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hσ
    exact (hH' _ (right_ne_zero_of_mul hi)).trans (hδ i σ))]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have e1 : ∀ i : Fin (m + 2), ∑ σ ∈ F, (-1 : R) ^ (i : ℕ) * H' (δ i σ) * coeff R z.1 σ =
      (-1 : R) ^ (i : ℕ) * ∑ᶠ τ, H' τ * pushforwardFun (δ i) (coeff R z.1) τ := fun i ↦ by
    rw [finsum_mul_pushforwardFun H' (δ i) (coeff R z.1) F (fun σ hz hk ↦
      mem_meetFinset hz ((hH' _ hk).trans (hδ i σ))),
      finsum_mul_coeff_eq_sum z.1 ν (fun σ ↦ H' (δ i σ)) (fun σ hk ↦ (hH' _ hk).trans (hδ i σ)),
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ ↦ by ring
  rw [Finset.sum_congr rfl fun i _ ↦ e1 i]
  set T₀ := Finset.univ.biUnion fun i : Fin (m + 2) ↦ F.image (δ i)
  have e2 : ∀ i : Fin (m + 2), ∑ᶠ τ, H' τ * pushforwardFun (δ i) (coeff R z.1) τ =
      ∑ τ ∈ T₀, H' τ * pushforwardFun (δ i) (coeff R z.1) τ := fun i ↦
    finsum_eq_sum_of_support_subset _ fun τ hτ ↦ by
      have hτ' := Function.mem_support.1 hτ
      obtain ⟨σ, hσ, rfl⟩ := support_pushforwardFun_subset _ _ (right_ne_zero_of_mul hτ')
      exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finset.mem_image_of_mem _
        (mem_meetFinset hσ ((hH' _ (left_ne_zero_of_mul hτ')).trans (hδ i σ)))⟩
  simp_rw [e2, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun τ _ ↦ ?_
  have hz0 : ((BM R Y).d (m + 1) m).hom z.1 = 0 := (mem_cyc_iff z.1).1 z.2
  have hz := congrFun (congrArg (coeff R) hz0) τ
  rw [coeff_d] at hz
  have : ∑ i : Fin (m + 2), (-1 : R) ^ (i : ℕ) * (H' τ * pushforwardFun (δ i) (coeff R z.1) τ) =
      H' τ * ∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ) • pushforwardFun (δ i) (coeff R z.1) τ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [zsmul_eq_mul]
    push_cast
    ring
  rw [this]
  rw [Finset.sum_apply] at hz
  simp only [Pi.smul_apply] at hz
  rw [hz]
  exact mul_zero _

open Classical in
/-- The homotopy identity summed against a cycle, with the boundary terms collected in `K₁`. -/
lemma exists_capBdTerm (p q n : ℕ) (h : p + q = n) (h' : p + (q + 1) = n + 1)
    {φ : Simplex Y p → R} (hφ : coboundary R p φ = 0) (z : Cyc (R := R) Y n)
    (ν : Simp (TopCat.of U) q) :
    ∃ K₁ : Simp Y n → R, ∑ᶠ σ, K₁ σ * coeff R z.1 σ = 0 ∧
      (∀ σ, K₁ σ ≠ 0 → range (inclSimplex U ν) ⊆ range (toC σ)) ∧
      ∀ σ, restrFin R U (capFin R p q n h φ (single (simplexEquiv _ _ σ) 1)) (inclSimplex U ν) -
          capRestrCoeff R U p q n h φ (simplexEquiv _ _ σ) (inclSimplex U ν) =
        ∑ i : Fin (q + 2), (-1 : R) ^ (i : ℕ) * ∑ᶠ ω' : Simplex Y (q + 1),
          (if ω'.comp (face q i) = inclSimplex U ν then
            capHomCoeff R U p (q + 1) n h' φ (simplexEquiv _ _ σ) ω' else 0) + K₁ σ := by
  have hω : range (inclSimplex U ν) ⊆ U := range_inclSimplex_subset U ν
  cases n with
  | zero =>
    refine ⟨0, by simp, fun σ h0 ↦ absurd rfl h0, fun σ ↦ ?_⟩
    rw [restrFin_capFin_sub_capRestrCoeff_zero U.isOpen h hφ (simplexEquiv _ _ σ) hω, Pi.zero_apply, add_zero]
  | succ m =>
    refine ⟨fun σ ↦ ∑ i : Fin (m + 2), (-1 : R) ^ (i : ℕ) *
      capHomCoeff R U p q m h φ ((simplexEquiv _ _ σ).comp (face m i)) (inclSimplex U ν),
      finsum_capHomCoeff_face_mul_coeff_eq_zero h φ z ν, fun σ hσ ↦ ?_, fun σ ↦
      restrFin_capFin_sub_capRestrCoeff_succ U.isOpen h hφ (simplexEquiv _ _ σ) hω⟩
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hσ
    refine ((range_subset_of_capHomCoeff_ne_zero (right_ne_zero_of_mul hi)).trans
      inter_subset_left).trans ?_
    rintro _ ⟨t, rfl⟩
    exact ⟨_, rfl⟩

open Classical in
/-- **The cap product commutes with restriction on cycles, up to a boundary.** For an open
subset `U` of a Hausdorff space `Y`, a `p`-cocycle `φ` vanishing on `A` and a locally finite
cycle `z`, `(φ ∩ z)|_U - φ|_U ∩ z|_U = ∂ u` for a locally finite chain `u` of `U` whose
simplices each lie in a simplex of `z` not contained in `A`. -/
theorem exists_d_eq_restrictChainMap_capChain_sub (p q n : ℕ) (h : p + q = n) {A : Set Y}
    {φ : Simplex Y p → R} (hφ : coboundary R p φ = 0) (hφA : φ ∈ vanishing R p A)
    (z : Cyc (R := R) Y n) :
    ∃ u : (BM R (TopCat.of U)).X (q + 1),
      ((BM R (TopCat.of U)).d (q + 1) q).hom u =
        ((restrictChainMap R (ModuleCat.of R R) U).f q).hom (capChain R p q n h φ z.1) -
          capChain R p q n h (cochainPullback R (inclHom U) p φ)
            (((restrictChainMap R (ModuleCat.of R R) U).f n).hom z.1) ∧
      ∀ ν, coeff R u ν ≠ 0 → ∃ σ, coeff R z.1 σ ≠ 0 ∧ ¬ range (toC σ) ⊆ A ∧
        range (inclSimplex U ν) ⊆ range (toC σ) := by
  have h' : p + (q + 1) = n + 1 := by omega
  set u₀ := ofCoeff R (capHomFun U p (q + 1) n h' φ (coeff R z.1))
    (mem_lfChains.2 (isLocallyFiniteSet_capHomFun p (q + 1) n h' φ
      (mem_lfChains.1 (coeff_mem R z.1))))
  refine ⟨u₀, ?_, fun ν hν ↦ ?_⟩
  · apply coeff_injective R
    funext ν
    obtain ⟨K₁, hK₁, hK₁s, hpt⟩ := exists_capBdTerm p q n h h' hφ z ν
    rw [coeff_d_capHomFun]
    change _ = coeff R (((restrictChainMap R (ModuleCat.of R R) U).f q).hom
      (capChain R p q n h φ z.1)) ν - coeff R (capChain R p q n h
        (cochainPullback R (inclHom U) p φ)
          (((restrictChainMap R (ModuleCat.of R R) U).f n).hom z.1)) ν
    rw [coeff_restrictChainMap_capChain, coeff_capChain_restrictChainMap]
    set KD : Simp Y n → R := fun σ ↦ ∑ i : Fin (q + 2), (-1 : R) ^ (i : ℕ) *
      ∑ᶠ ω' : Simplex Y (q + 1), (if ω'.comp (face q i) = inclSimplex U ν then
        capHomCoeff R U p (q + 1) n h' φ (simplexEquiv _ _ σ) ω' else 0) with hKD
    set KA : Simp Y n → R := fun σ ↦
      restrFin R U (capFin R p q n h φ (single (simplexEquiv _ _ σ) 1)) (inclSimplex U ν) with hKA
    set KB : Simp Y n → R := fun σ ↦
      capRestrCoeff R U p q n h φ (simplexEquiv _ _ σ) (inclSimplex U ν) with hKB
    have sD : ∀ σ, KD σ ≠ 0 → range (inclSimplex U ν) ⊆ range (toC σ) := fun σ hσ ↦ by
      obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hσ
      obtain ⟨ω', hω'⟩ : ∃ ω' : Simplex Y (q + 1), (if ω'.comp (face q i) = inclSimplex U ν then
          capHomCoeff R U p (q + 1) n h' φ (simplexEquiv _ _ σ) ω' else 0) ≠ 0 := by
        by_contra h''
        push Not at h''
        exact right_ne_zero_of_mul hi (finsum_eq_zero_of_forall_eq_zero h'')
      split_ifs at hω' with hc
      · refine Subset.trans ?_ ((range_subset_of_capHomCoeff_ne_zero hω').trans (inter_subset_left.trans (range_simplexEquiv _).subset))
        rw [← hc]
        rintro _ ⟨t, rfl⟩
        exact ⟨_, rfl⟩
      · exact absurd rfl hω'
    have sA : ∀ σ, KA σ ≠ 0 → range (inclSimplex U ν) ⊆ range (toC σ) := fun σ hσ ↦
      (range_subset_of_restrFin_ne_zero (capFin_mem_inside p q n h φ
        (single_mem_inside_range (simplexEquiv _ _ σ))) hσ).trans (inter_subset_left.trans (range_simplexEquiv _).subset)
    have sB : ∀ σ, KB σ ≠ 0 → range (inclSimplex U ν) ⊆ range (toC σ) := fun σ hσ ↦
      (range_subset_of_capRestrCoeff_ne_zero hσ).trans (inter_subset_left.trans (range_simplexEquiv _).subset)
    rw [finsum_mul_coeff_eq_sum z.1 ν KD sD, finsum_mul_coeff_eq_sum z.1 ν KA sA,
      finsum_mul_coeff_eq_sum z.1 ν KB sB, ← Finset.sum_sub_distrib]
    rw [finsum_mul_coeff_eq_sum z.1 ν _ hK₁s] at hK₁
    have hpt' : ∀ σ ∈ meetFinset z.1 ν, KA σ * coeff R z.1 σ - KB σ * coeff R z.1 σ =
        KD σ * coeff R z.1 σ + K₁ σ * coeff R z.1 σ := fun σ _ ↦ by
      rw [← sub_mul, hpt σ]
      ring
    rw [Finset.sum_congr rfl hpt', Finset.sum_add_distrib, hK₁, add_zero]
  · obtain ⟨σ, hσ⟩ : ∃ σ, capHomKernel U p (q + 1) n h' φ σ ν * coeff R z.1 σ ≠ 0 := by
      by_contra h''
      push Not at h''
      exact hν (finsum_eq_zero_of_forall_eq_zero h'')
    refine ⟨σ, right_ne_zero_of_mul hσ, fun hA ↦ left_ne_zero_of_mul hσ ?_,
      range_subset_of_capHomKernel_ne_zero (left_ne_zero_of_mul hσ)⟩
    exact capHomCoeff_eq_zero_of_vanishing h' hφA ((range_simplexEquiv σ).le.trans hA) _

end coefficients

end BorelMooreCap

end MMP
