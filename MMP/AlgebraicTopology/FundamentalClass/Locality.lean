module

public import MMP.AlgebraicTopology.FundamentalClass.Restriction
public import MMP.AlgebraicTopology.ThomClass.Natural
/-!
# Local classes are detected on open neighbourhoods (Fulton, §19.1)

Let `U` be an open subset of a Hausdorff space `Y`, `x ∈ U`, and `Δ` a singular simplex of `U`.
If the restriction `ν|_U` of a Borel–Moore class `ν ∈ H_n Y` has the same image as `Δ` in the
local homology `H_n(U, U - x)`, then `ν` has the same image as `Δ` in `H_n(Y, Y - x)`: this is
the converse of the restriction of local classes, i.e. excision for local homology.

The proof is at the level of cochains. A relative cocycle `φ` of `(Y, Y - x)` restricts to the
relative cocycle `φ'` of `(U, U - x)`, and pairing with the restriction `z|_U` of a locally finite
cycle `z` is pairing `z` with the cochain `σ ↦ ∑_τ (σ|_U)_τ φ(τ)`. Write
`σ = ρ_N σ + ∂ D_N σ + D_N ∂ σ` with `ρ_N` the subdivision of `σ` towards `U` and `D_N` its
homotopy. Near `x` the bad part of `ρ_N σ` is empty for large `N`, and the good part is `σ|_U`,
so `∑_τ (σ|_U)_τ φ(τ) = φ(σ) - (δ ψ)(σ)` where `ψ(ω) = φ(D_∞ ω)` vanishes off `x`. The pairing of
the locally finite cycle `z` with `δ ψ` is the pairing of `∂ z = 0` with `ψ`.

## Main results

* `MMP.SingularChain.finsum_restrCoeff_mul_eq`: the cochain identity
  `∑_τ (σ|_U)_τ φ(τ) = φ(σ) - (δ ψ)(σ)` for a relative cocycle `φ` of `(Y, Y - x)`.
* `MMP.FundamentalClass.IsLocallyClassOf.of_restrict`: local classes on an open
  neighbourhood of `x` are local classes on the whole space.

## References

* [B. Iversen, *Cohomology of Sheaves*][iversen1986], IX.4.
* [A. Borel, J. C. Moore, *Homology theory for locally compact spaces*][borelmoore1960], §3.
-/

@[expose] public noncomputable section

open Finsupp Set

universe u

namespace MMP

namespace SingularChain

open SingularCochain borelMooreHomology

variable {R : Type*} [CommRing R] {Y : Type*} [TopologicalSpace Y]

/-- Evaluating an `R`-valued cochain on the boundary of an integral chain is evaluating its
coboundary. -/
lemma linearCombination_int_bd {n : ℕ} (φ : Simplex Y n → R) (c : Chain ℤ Y (n + 1)) :
    linearCombination ℤ φ (bd ℤ n c) = linearCombination ℤ (coboundary R n φ) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single σ a =>
    rw [← mul_one a, ← smul_eq_mul, ← smul_single, map_smul, map_smul, map_smul, bd_single,
      map_sum]
    simp [coboundary_apply, Finset.smul_sum, zsmul_eq_mul]

/-- A cochain vanishing on simplices inside `A` evaluates to zero on an integral chain supported
inside `A`. -/
lemma linearCombination_int_eq_zero_of_mem_inside {n : ℕ} {A : Set Y} {φ : Simplex Y n → R}
    (hφ : φ ∈ vanishing R n A) {c : Chain ℤ Y n} (hc : c ∈ inside ℤ n A) :
    linearCombination ℤ φ c = 0 := by
  rw [linearCombination_apply]
  exact Finset.sum_eq_zero fun τ hτ ↦ by simp [hφ τ (hc hτ)]

variable (U : Set Y)

/-- The cochain `ψ(ω) = ∑_k φ(T X_k ω)` evaluating `φ` on the homotopy `D_∞ ω` between `ω` and
its subdivision towards `U`. -/
def restrDefectCochain {n : ℕ} (φ : Simplex Y (n + 1) → R) (ω : Simplex Y n) : R :=
  ∑ᶠ k : ℕ, linearCombination ℤ φ (subdivHomotopy ℤ n (badChain ℤ U k n (single ω 1)))

variable {U}

/-- For an open `U ∋ x` in a Hausdorff space and a cochain `φ` vanishing off `x`, for all large `N`
the cochain `restrDefectCochain U φ` evaluates on `ω` to `φ` of the `N`-th homotopy towards `U`
applied to `ω`. -/
lemma restrDefectCochain_eq [T2Space Y] (hU : IsOpen U) {x : Y} (hx : x ∈ U) {n : ℕ}
    {φ : Simplex Y (n + 1) → R} (hφ : φ ∈ vanishing R (n + 1) ({x}ᶜ : Set Y))
    (ω : Simplex Y n) : ∃ N₀, ∀ N ≥ N₀, restrDefectCochain U φ ω =
      linearCombination ℤ φ (towardsHomotopy ℤ U N n (single ω 1)) := by
  have hUV : U ∪ ({x}ᶜ : Set Y) = univ :=
    eq_univ_of_forall fun y ↦ by
      by_cases hy : y = x
      · exact Or.inl (hy ▸ hx)
      · exact Or.inr hy
  obtain ⟨N₀, h⟩ := eventually_badChain_mem_inside (R := ℤ) hU isOpen_compl_singleton hUV ω
  refine ⟨N₀, fun N hN ↦ ?_⟩
  rw [restrDefectCochain, finsum_eq_sum_of_support_subset (s := Finset.range N) _ (fun k hk ↦ ?_),
    towardsHomotopy, LinearMap.sum_apply, map_sum]
  · rfl
  · rw [Finset.coe_range, mem_Iio]
    by_contra hkN
    exact hk (linearCombination_int_eq_zero_of_mem_inside hφ
      (subdivHomotopy_mem_inside (h k (hN.trans (not_lt.1 hkN)))))

/-- If `φ` vanishes off `x`, then so does `restrDefectCochain U φ`. -/
lemma restrDefectCochain_mem_vanishing {x : Y} {n : ℕ}
    {φ : Simplex Y (n + 1) → R} (hφ : φ ∈ vanishing R (n + 1) ({x}ᶜ : Set Y)) :
    restrDefectCochain U φ ∈ vanishing R n ({x}ᶜ : Set Y) := fun ω hω ↦
  finsum_eq_zero_of_forall_eq_zero fun _ ↦ linearCombination_int_eq_zero_of_mem_inside hφ
    (subdivHomotopy_mem_inside (badChain_mem_inside
      (fun τ hτ ↦ ((single_mem_inside_range (R := ℤ) ω hτ : range τ ⊆ range ω).trans hω :
        range τ ⊆ ({x}ᶜ : Set Y)))))

/-- **The restriction defect.** For an open `U ∋ x` and a relative cocycle `φ` of `(Y, Y - x)`,
`∑_τ (σ|_U)_τ φ(τ) = φ(σ) - (δ ψ)(σ)`, with `ψ = restrDefectCochain U φ`. -/
theorem finsum_restrCoeff_mul_eq [T2Space Y] (hU : IsOpen U) {x : Y} (hx : x ∈ U) {n : ℕ}
    {φ : Simplex Y (n + 1) → R} (hφ : φ ∈ vanishing R (n + 1) ({x}ᶜ : Set Y))
    (hδ : coboundary R (n + 1) φ = 0) (σ : Simplex Y (n + 1)) :
    ∑ᶠ τ, (restrCoeff ℤ U σ τ : R) * φ τ =
      φ σ - coboundary R n (restrDefectCochain U φ) σ := by
  classical
  set V : Set Y := {x}ᶜ
  have hσV : range σ ∩ Uᶜ ⊆ V := fun y hy (h : y = x) ↦ hy.2 (h ▸ hx)
  obtain ⟨N₁, h₁⟩ := eventually_goodPart_sub_mem_inside (R := ℤ) hU σ isOpen_compl_singleton hσV
  choose N₂ h₂ using fun i : Fin (n + 2) ↦ restrDefectCochain_eq hU hx hφ (σ.comp (face n i))
  set N := max N₁ (Finset.univ.sup N₂)
  have hN₁ : N₁ ≤ N := le_max_left _ _
  have hN₂ : ∀ i, N₂ i ≤ N := fun i ↦ (Finset.le_sup (f := N₂) (Finset.mem_univ i)).trans
    (le_max_right _ _)
  have hstab : ∀ τ : Simplex Y (n + 1), ¬range τ ⊆ V →
      restrCoeff ℤ U σ τ = goodPart ℤ U N σ τ := fun τ hτ ↦ restrCoeff_eq fun N' hN' ↦ by
    have hd : towardsChainMap ℤ U N' (n + 1) (single σ 1) -
        towardsChainMap ℤ U N (n + 1) (single σ 1) ∈ inside ℤ (n + 1) V := by
      rw [← sub_sub_sub_cancel_right _ _ (towardsChainMap ℤ U N₁ (n + 1) (single σ 1))]
      exact sub_mem (h₁ N' (hN₁.trans hN')).1 (h₁ N hN₁).1
    have h0 := eq_zero_of_mem_inside (goodProj_mem_inside (U := U) hd) hτ
    rwa [map_sub, Finsupp.sub_apply, sub_eq_zero] at h0
  have hL : ∑ᶠ τ, (restrCoeff ℤ U σ τ : R) * φ τ =
      linearCombination ℤ φ (goodPart ℤ U N σ) := by
    rw [linearCombination_apply, Finsupp.sum,
      finsum_eq_sum_of_support_subset (s := (goodPart ℤ U N σ).support) _ (fun τ hτ ↦ ?_)]
    · refine Finset.sum_congr rfl fun τ _ ↦ ?_
      by_cases hτ : range τ ⊆ V
      · simp [hφ τ hτ]
      · rw [hstab τ hτ, zsmul_eq_mul]
    · rw [Function.mem_support] at hτ
      have hφτ : φ τ ≠ 0 := fun h0 ↦ hτ (by rw [h0, mul_zero])
      have hτV : ¬range τ ⊆ V := fun h ↦ hφτ (hφ τ h)
      rw [Finset.mem_coe, Finsupp.mem_support_iff, ← hstab τ hτV]
      intro h0
      exact hτ (by rw [h0, Int.cast_zero, zero_mul])
  have hgood : goodPart ℤ U N σ = towardsChainMap ℤ U N (n + 1) (single σ 1) -
      badChain ℤ U N (n + 1) (single σ 1) := by
    rw [goodPart, ← badProj_towardsChainMap, eq_sub_iff_add_eq, goodProj_add_badProj]
  rw [hL, hgood, map_sub, linearCombination_int_eq_zero_of_mem_inside hφ (h₁ N hN₁).2, sub_zero,
    towardsChainMap_succ_apply, map_sub, map_sub, linearCombination_int_bd, hδ,
    linearCombination_zero, LinearMap.zero_apply, sub_zero, linearCombination_single, one_smul,
    bd_single, map_sum, map_sum, coboundary_apply]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, map_smul, ← h₂ i N (hN₂ i), zsmul_eq_mul]
  push_cast
  rfl

/-- In degree `0` the restriction of `σ` near a point `x ∈ U` is `σ` itself. -/
theorem finsum_restrCoeff_mul_eq_zero {x : Y} (hx : x ∈ U) {φ : Simplex Y 0 → R}
    (hφ : φ ∈ vanishing R 0 ({x}ᶜ : Set Y)) (σ : Simplex Y 0) :
    ∑ᶠ τ, (restrCoeff ℤ U σ τ : R) * φ τ = φ σ := by
  classical
  have hpt : ∀ s t : stdSimplex ℝ (Fin 1), s = t := fun s t ↦ by
    ext i
    have hs : ∑ j, (s : Fin 1 → ℝ) j = 1 := s.2.2
    have ht : ∑ j, (t : Fin 1 → ℝ) j = 1 := t.2.2
    rw [Fin.sum_univ_one] at hs ht
    rw [Subsingleton.elim i 0, hs, ht]
  by_cases h : range σ ⊆ U
  · simp_rw [restrCoeff_of_range_subset h]
    rw [finsum_eq_single _ σ (fun τ hτ ↦ by simp [hτ.symm])]
    simp
  · have hd : Disjoint (range σ) U := Set.disjoint_left.2 fun y ⟨s, hs⟩ hyU ↦ h fun z ⟨t, ht⟩ ↦
      by rwa [← ht, hpt t s, hs]
    simp_rw [restrCoeff_of_disjoint hd]
    simp only [Int.cast_zero, zero_mul, finsum_zero]
    exact (hφ σ fun y hy (hyx : y = x) ↦ Set.disjoint_left.1 hd hy (hyx ▸ hx)).symm

end SingularChain

namespace FundamentalClass

open CategoryTheory Opposite Simplicial SingularChain SingularCochain LocallyFiniteChain
  borelMooreHomology

section Coboundary

variable {R : Type u} [CommRing R] {X : TopCat.{u}}

/-- Collapsing the indicator `if g ω = τ` in a double sum over `τ ∈ T` and `ω ∈ F`, when `g`
maps `F` into `T`. -/
lemma sum_sum_ite_mul {α β : Type*} [DecidableEq β] (F : Finset α)
    (T : Finset β) (g : α → β) (hg : ∀ ω ∈ F, g ω ∈ T) (a : R) (c : α → R) (f : β → R) :
    ∑ τ ∈ T, ∑ ω ∈ F, a * ((if g ω = τ then c ω else 0) * f τ) =
      ∑ ω ∈ F, c ω * (a * f (g ω)) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω hω ↦ ?_
  simp_rw [ite_mul, zero_mul, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq, ite_eq_left_iff.2 fun h ↦ absurd (hg ω hω) h]
  ring

/-- `⟨ψ, ∂ w⟩ = ⟨δ ψ, w⟩` for a locally finite chain `w` and a cochain `ψ` vanishing off a
point. -/
lemma localPairing_d {n : ℕ}
    (w : (borelMooreChainComplex R (ModuleCat.of R R) X).X (n + 1)) {x : X}
    {φ : Simplex X n → R} (hφv : φ ∈ vanishing R n ({x}ᶜ : Set X)) :
    localPairing ((((borelMooreChainComplex R (ModuleCat.of R R) X).d (n + 1) n).hom w).1
      : (TopCat.toSSet.obj X).obj (op ⦋n⦌) → R) φ =
    localPairing (w.1 : (TopCat.toSSet.obj X).obj (op ⦋n + 1⦌) → R) (coboundary R n φ) := by
  classical
  rw [borelMooreChainComplex_d_apply R (ModuleCat.of R R) X n w]
  set c : (TopCat.toSSet.obj X).obj (op ⦋n + 1⦌) → R := w.1
  have hc : IsLocallyFiniteSet (singularSimplexImage X) (Function.support c) := w.2
  let F := (hc.finite_inter_compact (isCompact_singleton (x := x))).toFinset
  have hF : ∀ ω, c ω ≠ 0 → x ∈ singularSimplexImage X ω → ω ∈ F := fun ω h1 h2 ↦
    (Finite.mem_toFinset _).2 ⟨h1, x, h2, rfl⟩
  let T := F.biUnion fun ω ↦ Finset.univ.image fun i : Fin (n + 2) ↦
    (TopCat.toSSet.obj X).δ i ω
  have hxφ : ∀ τ : (TopCat.toSSet.obj X).obj (op ⦋n⦌), φ (SingularCochain.simplexEquiv X _ τ) ≠ 0 →
      x ∈ singularSimplexImage X τ := fun τ h ↦
    by_contra fun hx ↦ h (hφv _ fun y hy hyx ↦ hx (hyx ▸ (range_simplexEquiv _).subset hy))
  have hterm : ∀ τ, dFun (fun i : Fin (n + 2) ↦ (TopCat.toSSet.obj X).δ i) c τ *
      φ (SingularCochain.simplexEquiv X _ τ) = ∑ i : Fin (n + 2), ∑ ω ∈ F,
        (-1 : R) ^ (i : ℕ) * ((if (TopCat.toSSet.obj X).δ i ω = τ then c ω else 0) *
          φ (SingularCochain.simplexEquiv X _ τ)) := by
    intro τ
    by_cases h : φ (SingularCochain.simplexEquiv X _ τ) = 0
    · simp [h]
    rw [dFun, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [pushforwardFun_apply_eq_sum _ c τ F (fun ω h1 (h2 : (TopCat.toSSet.obj X).δ i ω = τ) ↦
      hF ω h1 (singularSimplexImage_map_subset _ ω (h2.symm ▸ hxφ τ h))), Finset.smul_sum,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun ω _ ↦ ?_
    rw [zsmul_eq_mul]
    push_cast
    ring
  rw [localPairing, finsum_eq_sum_of_support_subset (s := T) _ (fun τ hτ ↦ by
    rw [Function.mem_support, hterm] at hτ
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hτ
    obtain ⟨ω, hω, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
    have hδ : (TopCat.toSSet.obj X).δ i ω = τ := by
      by_contra h
      simp [h] at hi
    rw [Finset.coe_biUnion]
    exact mem_iUnion₂.2 ⟨ω, hω, by simp [← hδ]⟩)]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  have hinner : ∀ i : Fin (n + 2), ∑ τ ∈ T, ∑ ω ∈ F, (-1 : R) ^ (i : ℕ) *
      ((if (TopCat.toSSet.obj X).δ i ω = τ then c ω else 0) * φ (SingularCochain.simplexEquiv X _ τ)) =
      ∑ ω ∈ F, c ω * ((-1 : R) ^ (i : ℕ) *
        φ ((SingularCochain.simplexEquiv X _ ω : Simplex X (n + 1)).comp (face n i))) := by
    intro i
    rw [sum_sum_ite_mul F T _ fun ω hω ↦
      Finset.mem_biUnion.2 ⟨ω, hω, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩]
    simp_rw [← toSSetObjEquiv_δ]
  rw [Finset.sum_congr rfl fun i _ ↦ hinner i, Finset.sum_comm, localPairing,
    finsum_eq_sum_of_support_subset (s := F) _ (fun ω hω ↦ ?_)]
  · refine Finset.sum_congr rfl fun ω _ ↦ ?_
    rw [← Finset.mul_sum, coboundary_apply]
  · rw [Function.mem_support] at hω
    have h1 : c ω ≠ 0 := fun h ↦ hω (by simp [h])
    have h2 : coboundary R n φ (SingularCochain.simplexEquiv X _ ω) ≠ 0 := fun h ↦ hω (by simp [h])
    exact Finset.mem_coe.2 (hF ω h1 (by_contra fun hx ↦
      h2 (coboundary_mem_vanishing hφv _ fun y hy hyx ↦ hx (hyx ▸ (range_simplexEquiv _).subset hy))))

end Coboundary

section Excision

variable {R : Type u} [CommRing R] {Y : TopCat.{u}} [T2Space Y] (U : TopologicalSpace.Opens Y)

/-- The pull-back along the restriction to `U` of the restriction `φ|_U` of a cochain `φ` of
`Y` is `σ ↦ ∑_τ (σ|_U)_τ φ(τ)`. -/
lemma pullbackCochain_restrictChainMap_cochainPullback {n : ℕ} {x : U} {φ : Simplex Y n → R}
    (hφ : cochainPullback R (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
      TopCat.of U ⟶ Y) n φ ∈ vanishing R n ({x}ᶜ : Set U)) (σ : Simplex Y n) :
    pullbackCochain (restrictChainMap R (ModuleCat.of R R) U) hφ σ =
      ∑ᶠ τ : Simplex Y n, (restrCoeff ℤ (U : Set Y) σ τ : R) * φ τ := by
  obtain ⟨σ', rfl⟩ := (SingularCochain.simplexEquiv Y n).surjective σ
  rw [pullbackCochain_restrictChainMap_apply]
  set f : Simplex Y n → R := fun τ ↦ (restrCoeff ℤ (U : Set Y) (SingularCochain.simplexEquiv Y _ σ') τ : R) * φ τ
  change ∑ᶠ τ, f (inclSimplex U τ) = ∑ᶠ τ, f τ
  rw [← finsum_mem_range (inclSimplex_injective U n), ← finsum_mem_inter_support,
    inter_eq_right.2 fun τ hτ ↦ ?_, finsum_mem_support]
  have h : restrCoeff ℤ (U : Set Y) (SingularCochain.simplexEquiv Y _ σ') τ ≠ 0 := fun h0 ↦
    hτ (by simp [f, h0])
  exact mem_range_inclSimplex U ((range_subset_of_restrCoeff_ne_zero h).trans inter_subset_right)

/-- For a locally finite cycle `z` of `Y` and a relative cocycle `φ` of `(Y, Y - x)`, `x ∈ U`,
pairing the restriction `z|_U` with `φ|_U` is pairing `z` with `φ`. -/
lemma localPairing_pullbackCochain_restrictChainMap {n : ℕ}
    (c : (borelMooreChainComplex R (ModuleCat.of R R) Y).X n)
    (hc : ∀ j, ((borelMooreChainComplex R (ModuleCat.of R R) Y).d n j).hom c = 0)
    {x : U} {φ : Simplex Y n → R} (hφ : φ ∈ relCocycles R ({x.1}ᶜ : Set Y) n)
    (hφ' : cochainPullback R (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
      TopCat.of U ⟶ Y) n φ ∈ vanishing R n ({x}ᶜ : Set U)) :
    localPairing (c.1 : (TopCat.toSSet.obj Y).obj (op ⦋n⦌) → R)
        (pullbackCochain (restrictChainMap R (ModuleCat.of R R) U) hφ') =
      localPairing (c.1 : (TopCat.toSSet.obj Y).obj (op ⦋n⦌) → R) φ := by
  have hU : IsOpen (U : Set Y) := U.isOpen
  cases n with
  | zero =>
    refine finsum_congr fun σ ↦ ?_
    rw [pullbackCochain_restrictChainMap_cochainPullback, finsum_restrCoeff_mul_eq_zero x.2 hφ.1]
  | succ m =>
    have hδ : coboundary R (m + 1) φ = 0 := hφ.2
    have hpt : ∀ σ, pullbackCochain (restrictChainMap R (ModuleCat.of R R) U) hφ' σ =
        φ σ - coboundary R m (restrDefectCochain (U : Set Y) φ) σ := fun σ ↦ by
      rw [pullbackCochain_restrictChainMap_cochainPullback,
        finsum_restrCoeff_mul_eq hU x.2 hφ.1 hδ]
    have hψ := restrDefectCochain_mem_vanishing (U := (U : Set Y)) hφ.1
    have hfin1 := finite_support_mul c.2 hφ.1
    have hfin2 := finite_support_mul c.2 (coboundary_mem_vanishing hψ)
    have h0 : localPairing (c.1 : (TopCat.toSSet.obj Y).obj (op ⦋m + 1⦌) → R)
        (coboundary R m (restrDefectCochain (U : Set Y) φ)) = 0 := by
      rw [← localPairing_d c hψ, hc m]
      exact finsum_eq_zero_of_forall_eq_zero fun σ ↦ zero_mul _
    rw [localPairing]
    simp_rw [hpt, mul_sub]
    rw [finsum_sub_distrib hfin1 hfin2]
    change localPairing _ φ - localPairing _ _ = _
    rw [h0, sub_zero]

/-- **Local classes are local.** For an open subset `U` of a Hausdorff space `Y`, a point `x` of
`U` and a simplex `Δ` of `U`: if `ν|_U ∈ H_n U` is locally the class of `Δ` at `x`, then so is
`ν ∈ H_n Y`. This is the converse of `IsLocallyClassOf.restrict`. -/
theorem IsLocallyClassOf.of_restrict {n : ℕ} {ν : borelMooreHomology R (ModuleCat.of R R) Y n}
    {x : U} {Δ : Simplex (TopCat.of U) n}
    (h : IsLocallyClassOf R (borelMooreHomology.restrict R (ModuleCat.of R R) U n ν) x Δ) :
    IsLocallyClassOf R ν x.1 (inclChainSimplex U Δ) := by
  intro z hz φ hφ
  set Φ := restrictChainMap R (ModuleCat.of R R) U
  have hmor : HomologicalComplex.homologyMap
      (HomologicalComplex.extendMap Φ ComplexShape.embeddingDownNat) (-(n : ℤ)) ≫
        (borelMooreHomologyIsoOfNat R (ModuleCat.of R R) (TopCat.of U) n).hom =
      (borelMooreHomologyIsoOfNat R (ModuleCat.of R R) Y n).hom ≫
        HomologicalComplex.homologyMap Φ n :=
    HomologicalComplex.extendHomologyIso_hom_naturality Φ ComplexShape.embeddingDownNat _
  have e1 : (borelMooreChainComplex R (ModuleCat.of R R) (TopCat.of U)).homologyπ n
      (HomologicalComplex.cyclesMap Φ n z) =
      HomologicalComplex.homologyMap Φ n
        ((borelMooreChainComplex R (ModuleCat.of R R) Y).homologyπ n z) :=
    (ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality Φ n) z).symm
  have hz' : (borelMooreChainComplex R (ModuleCat.of R R) (TopCat.of U)).homologyπ n
      (HomologicalComplex.cyclesMap Φ n z) =
      (borelMooreHomologyIsoOfNat R (ModuleCat.of R R) (TopCat.of U) n).hom
        (borelMooreHomology.restrict R (ModuleCat.of R R) U n ν) := by
    rw [e1, hz]
    exact (ConcreteCategory.congr_hom hmor ν).symm
  have hsub : ({x}ᶜ : Set (TopCat.of U)) ⊆ (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
      TopCat.of U ⟶ Y) ⁻¹' ({x.1}ᶜ : Set Y) := fun y hy hyx ↦ hy (Subtype.ext hyx)
  have hφ' : cochainPullback R (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
      TopCat.of U ⟶ Y) n φ ∈ relCocycles R ({x}ᶜ : Set (TopCat.of U)) n :=
    cochainPullback_mem_relCocycles _ hsub hφ
  have key := h _ hz' _ hφ'
  have hi : (borelMooreChainComplex R (ModuleCat.of R R) (TopCat.of U)).iCycles n
      (HomologicalComplex.cyclesMap Φ n z) =
      Φ.f n ((borelMooreChainComplex R (ModuleCat.of R R) Y).iCycles n z) :=
    ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i Φ n) z
  have hd : ∀ j, ((borelMooreChainComplex R (ModuleCat.of R R) Y).d n j).hom
      ((borelMooreChainComplex R (ModuleCat.of R R) Y).iCycles n z) = 0 := fun j ↦
    congrArg (fun f ↦ ModuleCat.Hom.hom f z)
      (HomologicalComplex.iCycles_d (borelMooreChainComplex R (ModuleCat.of R R) Y) n j)
  rw [hi] at key
  change localPairing (((Φ.f n).hom _).1 : _) _ = _ at key
  rwa [localPairing_restrictChainMap U hφ'.1,
    localPairing_pullbackCochain_restrictChainMap U _ hd hφ hφ'.1] at key

end Excision

end FundamentalClass

end MMP
