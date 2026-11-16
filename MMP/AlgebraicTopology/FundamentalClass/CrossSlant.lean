module

public import MMP.AlgebraicTopology.FundamentalClass.Locality
public import MMP.AlgebraicTopology.BorelMoore.ExteriorProduct

/-!
# Local classes of exterior products

Let `μ ∈ H_p X` be locally the class of a simplex `Δ` at `x`, and `ν ∈ H_q Y` locally the class
of a simplex `Δ'` at `y`, where the faces of `Δ` avoid `x`. Then the exterior product `μ × ν` is
locally, at `(x, y)`, the class of the chain `Δ × Δ'`: for cycles `z`, `w` representing `μ`,
`ν` and every relative cocycle `φ` of `(X × Y, X × Y - (x, y))`, `⟨φ, z × w⟩ = φ(Δ × Δ')`.

The proof is the slant product. For a simplex `σ` of `X` the cochain `χ_σ(τ) = φ(σ × τ)` of `Y`
vanishes off `y`, and `ψ(σ) = ⟨χ_σ, w⟩` is a relative cocycle of `(X, X - x)`: by the Leibniz
rule `∂(σ × τ) = ∂σ × τ + (-1)^p σ × ∂τ` and `δφ = 0`, `δψ(σ) = ± ⟨δχ_σ, w⟩ = ± ⟨χ_σ, ∂w⟩ = 0`.
Then `⟨φ, z × w⟩ = ⟨ψ, z⟩ = ψ(Δ) = ⟨χ_Δ, w⟩`, and `χ_Δ` is a relative cocycle of `(Y, Y - y)`
because the faces of `Δ` avoid `x`, so `⟨χ_Δ, w⟩ = χ_Δ(Δ') = φ(Δ × Δ')`.

## Main definitions

* `MMP.FundamentalClass.evalSimp`: the evaluation of a cochain on an integral
  chain of simplicial singular simplices.
* `MMP.FundamentalClass.slantCochain`: the cochain `χ_σ(τ) = φ(σ × τ)`.
* `MMP.FundamentalClass.slantPairing`: the cochain `ψ(σ) = ⟨χ_σ, w⟩`.

## Main results

* `MMP.FundamentalClass.localPairing_crossFun`: `⟨φ, z × w⟩ = ⟨ψ, z⟩`.
* `MMP.FundamentalClass.localPairing_crossFun_eq_evalSimp`: `⟨φ, z × w⟩ = φ(Δ × Δ')`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Simplicial Finsupp Set MMP.LatticePath
  MMP.SingularCross MMP.SingularChain
  MMP.SingularCochain MMP.BorelMooreCross
  MMP.LocallyFiniteChain

universe u

namespace MMP

namespace FundamentalClass

variable {R : Type u} [CommRing R]

section Leibniz

variable {X Y : TopCat.{u}}

/-- The Leibniz rule for the cross product of simplices of positive dimensions. -/
lemma sum_δ_crossSimplex_succ_succ (m p q : ℕ) (σ : Simp X (p + 1)) (τ : Simp Y (q + 1)) :
    ∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ) •
        Finsupp.mapDomain ((TopCat.toSSet.obj (TopCat.of (X × Y))).δ i)
          (crossSimplex (m + 1) σ τ) =
      ∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) • crossSimplex m ((TopCat.toSSet.obj X).δ k σ) τ +
        (-1 : ℤ) ^ (p + 1) • ∑ l : Fin (q + 2), (-1 : ℤ) ^ (l : ℕ) •
          crossSimplex m σ ((TopCat.toSSet.obj Y).δ l τ) := by
  rw [sum_δ_crossSimplex, Finsupp.mapDomain_add, Finsupp.mapDomain_smul,
    mapDomain_pathSimplex_fst, mapDomain_pathSimplex_snd]

/-- The Leibniz rule for the cross product of a point with a simplex. -/
lemma sum_δ_crossSimplex_zero_succ (m q : ℕ) (σ : Simp X 0) (τ : Simp Y (q + 1)) :
    ∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ) •
        Finsupp.mapDomain ((TopCat.toSSet.obj (TopCat.of (X × Y))).δ i)
          (crossSimplex (m + 1) σ τ) =
      ∑ l : Fin (q + 2), (-1 : ℤ) ^ (l : ℕ) • crossSimplex m σ ((TopCat.toSSet.obj Y).δ l τ) := by
  rw [sum_δ_crossSimplex, Finsupp.mapDomain_add, Finsupp.mapDomain_smul,
    mapDomain_pathSimplex_snd]
  simp

/-- The Leibniz rule for the cross product of a simplex with a point. -/
lemma sum_δ_crossSimplex_succ_zero (m p : ℕ) (σ : Simp X (p + 1)) (τ : Simp Y 0) :
    ∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ) •
        Finsupp.mapDomain ((TopCat.toSSet.obj (TopCat.of (X × Y))).δ i)
          (crossSimplex (m + 1) σ τ) =
      ∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) • crossSimplex m ((TopCat.toSSet.obj X).δ k σ) τ := by
  rw [sum_δ_crossSimplex, Finsupp.mapDomain_add, Finsupp.mapDomain_smul,
    mapDomain_pathSimplex_fst]
  simp

end Leibniz

section Eval

variable {Z : TopCat.{u}}

/-- The evaluation `c ↦ ∑_ρ c_ρ φ(ρ)` of a cochain on an integral chain of simplicial singular
simplices. -/
def evalSimp {m : ℕ} (φ : Simplex Z m → R) : (Simp Z m →₀ ℤ) →ₗ[ℤ] R :=
  Finsupp.linearCombination ℤ fun ρ ↦ φ (SingularCochain.simplexEquiv Z _ ρ)

/-- The evaluation of a cochain on `a • ρ` is `a • φ(ρ)`. -/
lemma evalSimp_single {m : ℕ} (φ : Simplex Z m → R) (ρ : Simp Z m) (a : ℤ) :
    evalSimp φ (Finsupp.single ρ a) = a • φ (SingularCochain.simplexEquiv Z _ ρ) := by
  simp [evalSimp]

/-- Evaluating on a boundary is evaluating the coboundary. -/
lemma evalSimp_sum_δ {m : ℕ} (φ : Simplex Z m → R) (c : Simp Z (m + 1) →₀ ℤ) :
    evalSimp φ (∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ) •
      Finsupp.mapDomain ((TopCat.toSSet.obj Z).δ i) c) = evalSimp (coboundary R m φ) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    simp only [Finsupp.mapDomain_add, smul_add, Finset.sum_add_distrib, map_add, hc, hd]
  | single ρ a =>
    simp only [Finsupp.mapDomain_single, map_sum, map_zsmul, evalSimp_single, coboundary_apply,
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [show SingularCochain.simplexEquiv Z _ ((TopCat.toSSet.obj Z).δ i ρ) =
      (SingularCochain.simplexEquiv Z _ ρ).comp (face m i) from borelMooreHomology.toSSetObjEquiv_δ i ρ]
    simp only [zsmul_eq_mul]
    push_cast
    ring

/-- The zero cochain evaluates to zero on every chain. -/
@[simp]
lemma evalSimp_zero_cochain {m : ℕ} (c : Simp Z m →₀ ℤ) :
    evalSimp (0 : Simplex Z m → R) c = 0 := by
  rw [evalSimp, Finsupp.linearCombination_apply]
  simp

/-- A cochain vanishing off `x` vanishes on chains of simplices avoiding `x`. -/
lemma evalSimp_eq_zero {m : ℕ} {x : Z} {φ : Simplex Z m → R}
    (hφ : φ ∈ vanishing R m ({x}ᶜ : Set Z)) {c : Simp Z m →₀ ℤ}
    (hc : ∀ ρ, c ρ ≠ 0 → x ∉ singularSimplexImage Z ρ) : evalSimp φ c = 0 := by
  rw [evalSimp, Finsupp.linearCombination_apply]
  refine Finset.sum_eq_zero fun ρ hρ ↦ ?_
  dsimp only
  rw [hφ _ fun z hz ↦ ?_, smul_zero]
  rintro rfl
  exact hc ρ (Finsupp.mem_support_iff.1 hρ) ((range_simplexEquiv _).subset hz)

end Eval

section Slant

variable {X Y : TopCat.{u}}

/-- The singular simplex of `Z` attached to a continuous map `Δᵖ → Z`. -/
abbrev toSimp {Z : TopCat.{u}} {p : ℕ} (σ : Simplex Z p) : Simp Z p :=
  (SingularCochain.simplexEquiv Z _).symm σ

/-- The slant cochain `χ_σ(τ) = φ(σ × τ)` of `Y` attached to a simplex `σ` of `X` and a cochain
`φ` of `X × Y`. -/
def slantCochain {m p : ℕ} (q : ℕ) (φ : Simplex (TopCat.of (X × Y)) m → R) (σ : Simp X p) :
    Simplex Y q → R :=
  fun τ ↦ evalSimp φ (crossSimplex m σ (toSimp τ))

/-- If `x` lies off `σ` or `y` lies off `τ`, then `(x, y)` lies off every simplex in the support
of `σ × τ`. -/
lemma notMem_singularSimplexImage_of_crossSimplex {m p q : ℕ} {σ : Simp X p} {τ : Simp Y q} {x : X} {y : Y}
    (h : x ∉ singularSimplexImage X σ ∨ y ∉ singularSimplexImage Y τ) {ρ}
    (hρ : crossSimplex m σ τ ρ ≠ 0) : ((x, y) : X × Y) ∉ singularSimplexImage _ ρ := fun hxy ↦ by
  have := singularSimplexImage_subset_of_mem_support m σ τ hρ hxy
  rcases h with h | h
  · exact h this.1
  · exact h this.2

/-- A cochain vanishing off `(x, y)` vanishes on `σ × τ` when `x` lies off `σ` or `y` lies off
`τ`. -/
lemma evalSimp_crossSimplex_eq_zero {m p q : ℕ} {σ : Simp X p} {τ : Simp Y q} {x : X} {y : Y}
    {φ : Simplex (TopCat.of (X × Y)) m → R}
    (hφ : φ ∈ vanishing R m ({((x, y) : X × Y)}ᶜ : Set (TopCat.of (X × Y))))
    (h : x ∉ singularSimplexImage X σ ∨ y ∉ singularSimplexImage Y τ) :
    evalSimp φ (crossSimplex m σ τ) = 0 :=
  evalSimp_eq_zero hφ fun _ hρ ↦ notMem_singularSimplexImage_of_crossSimplex h hρ

/-- The slant cochain of a cochain vanishing off `(x, y)` vanishes off `y`. -/
lemma slantCochain_mem_vanishing {m p q : ℕ} {x : X} {y : Y}
    {φ : Simplex (TopCat.of (X × Y)) m → R}
    (hφ : φ ∈ vanishing R m ({((x, y) : X × Y)}ᶜ : Set (TopCat.of (X × Y)))) (σ : Simp X p) :
    slantCochain q φ σ ∈ vanishing R q ({y}ᶜ : Set Y) := fun τ hτ ↦
  evalSimp_crossSimplex_eq_zero hφ (Or.inr fun ⟨t, ht⟩ ↦ by
    apply hτ ⟨(SingularChain.stdSimplexHomeo _).symm t, _⟩ rfl
    simpa [toSimp, SingularCochain.simplexEquiv] using ht)

/-- A locally finite chain pairs with a cochain vanishing off `y` through any finite set of
simplices containing those of its support through `y`. -/
lemma localPairing_eq_sum_of_subset {Z : TopCat.{u}} {n : ℕ} {c : Simp Z n → R} {y : Z}
    {F : Finset (Simp Z n)} (hF : ∀ τ, c τ ≠ 0 → y ∈ singularSimplexImage Z τ → τ ∈ F)
    {χ : Simplex Z n → R} (hχ : χ ∈ vanishing R n ({y}ᶜ : Set Z)) :
    localPairing c χ = ∑ τ ∈ F, c τ * χ (SingularCochain.simplexEquiv Z _ τ) := by
  refine finsum_eq_sum_of_support_subset _ fun τ hτ ↦ ?_
  rw [Function.mem_support] at hτ
  refine Finset.mem_coe.2 (hF τ (fun h ↦ hτ (by simp [h])) ?_)
  by_contra hy
  exact hτ (by rw [hχ _ fun z hz ↦ by rintro rfl; exact hy ((range_simplexEquiv _).subset hz), mul_zero])

/-- A locally finite chain pairs with a cochain vanishing off `y` through the finitely many
simplices of its support through `y`. -/
lemma localPairing_eq_sum {Z : TopCat.{u}} {n : ℕ} {c : Simp Z n → R}
    (hc : IsLocallyFiniteSet (singularSimplexImage Z) (Function.support c)) {y : Z}
    {χ : Simplex Z n → R} (hχ : χ ∈ vanishing R n ({y}ᶜ : Set Z)) :
    localPairing c χ = ∑ τ ∈ (hc.finite_inter_compact (isCompact_singleton (x := y))).toFinset,
      c τ * χ (SingularCochain.simplexEquiv Z _ τ) := by
  refine localPairing_eq_sum_of_subset (fun _ h1 h2 ↦ ?_) hχ
  exact (Finite.mem_toFinset _).2 ⟨h1, y, h2, rfl⟩

/-- Pairing a locally finite chain with a finite linear combination of cochains vanishing off `y`
is the linear combination of the pairings. -/
lemma localPairing_finset_sum {Z : TopCat.{u}} {n : ℕ} {c : Simp Z n → R}
    (hc : IsLocallyFiniteSet (singularSimplexImage Z) (Function.support c)) {y : Z}
    {ι : Type*} (s : Finset ι) (a : ι → R) {χ : ι → Simplex Z n → R}
    (hχ : ∀ i, χ i ∈ vanishing R n ({y}ᶜ : Set Z)) :
    localPairing c (∑ i ∈ s, a i • χ i) = ∑ i ∈ s, a i * localPairing c (χ i) := by
  have hsum : ∑ i ∈ s, a i • χ i ∈ vanishing R n ({y}ᶜ : Set Z) :=
    Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (hχ i)
  rw [localPairing_eq_sum hc hsum]
  simp_rw [localPairing_eq_sum hc (hχ _), Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ ↦ ?_
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

variable {x : X} {y : Y}

/-- The `k`-th coordinate of the `k`-th face map `Δᵖ → Δᵖ⁺¹` vanishes. -/
lemma face_apply_self {p : ℕ} (k : Fin (p + 2)) (s : stdSimplex ℝ (Fin (p + 1))) :
    ((face p k s : stdSimplex ℝ (Fin (p + 2))) : Fin (p + 2) → ℝ) k = 0 := by
  change (FunOnFinite.linearMap ℝ ℝ k.succAbove) s k = 0
  rw [FunOnFinite.linearMap_apply_apply]
  refine Finset.sum_eq_zero fun j hj ↦ ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  exact absurd hj (Fin.succAbove_ne k j)

/-- The singular simplex of `τ ∘ d_l` is the `l`-th face of the singular simplex of `τ`. -/
lemma toSimp_comp_face {Z : TopCat.{u}} {q : ℕ} (τ : Simplex Z (q + 1)) (l : Fin (q + 2)) :
    toSimp (τ.comp (face q l)) = (TopCat.toSSet.obj Z).δ l (toSimp τ) := by
  apply (SingularCochain.simplexEquiv Z _).injective
  rw [Equiv.apply_symm_apply]
  change τ.comp (face q l) = (SingularCochain.simplexEquiv Z _ (toSimp τ)).comp (face q l)
  rw [Equiv.apply_symm_apply]

/-- The coboundary of a slant cochain, as the evaluation on the cross products with the faces. -/
lemma coboundary_slantCochain_apply {m p q : ℕ} (φ : Simplex (TopCat.of (X × Y)) m → R)
    (σ : Simp X p) (τ : Simplex Y (q + 1)) :
    coboundary R q (slantCochain q φ σ) τ = evalSimp φ (∑ l : Fin (q + 2), (-1 : ℤ) ^ (l : ℕ) •
      crossSimplex m σ ((TopCat.toSSet.obj Y).δ l (toSimp τ))) := by
  rw [coboundary_apply, map_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [map_zsmul, zsmul_eq_mul, slantCochain, toSimp_comp_face]
  push_cast
  rfl

/-- The slant cochain of a simplex whose faces avoid `x` is a relative cocycle of `(Y, Y - y)`. -/
lemma slantCochain_mem_relCocycles {p q : ℕ}
    {φ : Simplex (TopCat.of (X × Y)) (p + q) → R}
    (hφ : φ ∈ relCocycles R ({((x, y) : X × Y)}ᶜ : Set (TopCat.of (X × Y))) (p + q))
    (σ : Simp X p)
    (hσ : ∀ t : stdSimplex ℝ (Fin (p + 1)), (∃ i, (t : Fin (p + 1) → ℝ) i = 0) → SingularCochain.simplexEquiv X p σ t ≠ x) :
    slantCochain q φ σ ∈ relCocycles R ({y}ᶜ : Set Y) q := by
  refine ⟨slantCochain_mem_vanishing hφ.1 σ, ?_⟩
  have hδφ : coboundary R (p + q) φ = 0 := hφ.2
  change coboundary R q (slantCochain q φ σ) = 0
  funext τ
  rw [coboundary_slantCochain_apply, Pi.zero_apply]
  rcases p with _ | p
  · rw [← sum_δ_crossSimplex_zero_succ, evalSimp_sum_δ, hδφ, evalSimp_zero_cochain]
  · have h := congrArg (evalSimp φ) (sum_δ_crossSimplex_succ_succ (p + 1 + q) p q σ
      (toSimp τ))
    rw [evalSimp_sum_δ, hδφ, map_add, map_zsmul] at h
    have h0 : evalSimp φ (∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) •
        crossSimplex (p + 1 + q) ((TopCat.toSSet.obj X).δ k σ) (toSimp τ)) = 0 := by
      rw [map_sum]
      refine Finset.sum_eq_zero fun k _ ↦ ?_
      rw [map_zsmul, evalSimp_crossSimplex_eq_zero hφ.1 (Or.inl ?_), smul_zero]
      rintro ⟨s, hs⟩
      refine hσ _ ⟨k, face_apply_self k ((SingularChain.stdSimplexHomeo _).symm s)⟩ ?_
      change toC σ (SingularChain.stdSimplexHomeo _ _) = x
      rw [SingularChain.stdSimplexHomeo_face, Homeomorph.apply_symm_apply]
      exact hs
    rw [h0, zero_add, evalSimp_zero_cochain] at h
    have := congrArg (fun r : R ↦ (-1 : ℤ) ^ (p + 1) • r) h
    simp only [smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul,
      smul_zero] at this
    exact this.symm

/-- The slant `ψ(σ) = ⟨χ_σ, w⟩` of a cochain `φ` of `X × Y` by a locally finite chain `w`. -/
def slantPairing {p q : ℕ} (w : Simp Y q → R) (φ : Simplex (TopCat.of (X × Y)) (p + q) → R) :
    Simplex X p → R :=
  fun σ ↦ localPairing w (slantCochain q φ (toSimp σ))

/-- The slant of a cochain vanishing off `(x, y)` vanishes off `x`. -/
lemma slantPairing_mem_vanishing {p q : ℕ} (w : Simp Y q → R)
    {φ : Simplex (TopCat.of (X × Y)) (p + q) → R}
    (hφ : φ ∈ vanishing R (p + q) ({((x, y) : X × Y)}ᶜ : Set (TopCat.of (X × Y)))) :
    slantPairing w φ ∈ vanishing R p ({x}ᶜ : Set X) := fun σ hσ ↦ by
  have h0 : slantCochain q φ (toSimp σ) = 0 := by
    funext τ
    refine evalSimp_crossSimplex_eq_zero hφ (Or.inl fun ⟨t, ht⟩ ↦ ?_)
    apply hσ ⟨(SingularChain.stdSimplexHomeo _).symm t, _⟩ rfl
    simpa [toSimp, SingularCochain.simplexEquiv] using ht
  rw [slantPairing, h0]
  exact finsum_eq_zero_of_forall_eq_zero fun _ ↦ mul_zero _

/-- The slant of a relative cocycle by a cycle is a relative cocycle. -/
lemma slantPairing_mem_relCocycles {p q : ℕ}
    (w : (borelMooreChainComplex R (ModuleCat.of R R) Y).X q)
    (hw : ∀ j, ((borelMooreChainComplex R (ModuleCat.of R R) Y).d q j).hom w = 0)
    {φ : Simplex (TopCat.of (X × Y)) (p + q) → R}
    (hφ : φ ∈ relCocycles R ({((x, y) : X × Y)}ᶜ : Set (TopCat.of (X × Y))) (p + q)) :
    slantPairing (w.1 : (TopCat.toSSet.obj Y).obj (op ⦋q⦌) → R) φ ∈
      relCocycles R ({x}ᶜ : Set X) p := by
  refine ⟨slantPairing_mem_vanishing _ hφ.1, ?_⟩
  have hδφ : coboundary R (p + q) φ = 0 := hφ.2
  have hwlf : IsLocallyFiniteSet (singularSimplexImage Y)
      (Function.support (w.1 : (TopCat.toSSet.obj Y).obj (op ⦋q⦌) → R)) := w.2
  change coboundary R p (slantPairing (w.1 : (TopCat.toSSet.obj Y).obj (op ⦋q⦌) → R) φ) = 0
  funext σ
  rw [coboundary_apply, Pi.zero_apply]
  simp only [slantPairing, toSimp_comp_face]
  rw [← localPairing_finset_sum hwlf Finset.univ (fun k : Fin (p + 2) ↦ (-1 : R) ^ (k : ℕ))
    (fun k ↦ slantCochain_mem_vanishing hφ.1 _)]
  have hfun : ∀ τ : Simplex Y q, (∑ k : Fin (p + 2), (-1 : R) ^ (k : ℕ) •
      slantCochain q φ ((TopCat.toSSet.obj X).δ k (toSimp σ))) τ =
      evalSimp φ (∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) •
        crossSimplex (p + q) ((TopCat.toSSet.obj X).δ k (toSimp σ)) (toSimp τ)) := fun τ ↦ by
    rw [Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_zsmul, zsmul_eq_mul, Pi.smul_apply, smul_eq_mul, slantCochain]
    push_cast
    rfl
  rcases q with _ | q
  · have h0 : (∑ k : Fin (p + 2), (-1 : R) ^ (k : ℕ) •
        slantCochain 0 φ ((TopCat.toSSet.obj X).δ k (toSimp σ))) = 0 := by
      funext τ
      rw [hfun, Pi.zero_apply, ← sum_δ_crossSimplex_succ_zero, evalSimp_sum_δ, hδφ,
        evalSimp_zero_cochain]
    exact (congrArg (localPairing _) h0).trans
      (finsum_eq_zero_of_forall_eq_zero fun _ ↦ mul_zero _)
  · have h0 : (∑ k : Fin (p + 2), (-1 : R) ^ (k : ℕ) •
        slantCochain (q + 1) φ ((TopCat.toSSet.obj X).δ k (toSimp σ))) =
        (-(-1 : R) ^ (p + 1)) • coboundary R q (slantCochain q φ (toSimp σ)) := by
      funext τ
      rw [hfun, Pi.smul_apply, coboundary_slantCochain_apply, smul_eq_mul]
      have h := congrArg (evalSimp φ) (sum_δ_crossSimplex_succ_succ (p + (q + 1)) p q
        (toSimp σ) (toSimp τ))
      rw [evalSimp_sum_δ, hδφ, map_add, map_zsmul, evalSimp_zero_cochain, zsmul_eq_mul] at h
      push_cast at h
      linear_combination -h
    have hsm := localPairing_finset_sum hwlf {()} (fun _ ↦ -(-1 : R) ^ (p + 1))
      (fun _ ↦ coboundary_mem_vanishing (slantCochain_mem_vanishing hφ.1 (toSimp σ)))
    simp only [Finset.sum_singleton] at hsm
    have hd : localPairing (w.1 : (TopCat.toSSet.obj Y).obj (op ⦋q + 1⦌) → R)
        (coboundary R q (slantCochain q φ (toSimp σ))) = 0 := by
      rw [← localPairing_d w (slantCochain_mem_vanishing hφ.1 _), hw q]
      exact finsum_eq_zero_of_forall_eq_zero fun _ ↦ zero_mul _
    exact (congrArg (localPairing _) h0).trans (hsm.trans (by rw [hd, mul_zero]))

/-- **The slant identity** `⟨φ, z × w⟩ = ⟨ψ, z⟩` for locally finite chains `z`, `w` and a cochain
`φ` of `X × Y` vanishing off `(x, y)`, where `ψ(σ) = ⟨χ_σ, w⟩` and `χ_σ(τ) = φ(σ × τ)`. -/
theorem localPairing_crossFun {p q : ℕ} {zc : Simp X p → R} {wc : Simp Y q → R}
    (hz : IsLocallyFiniteSet (singularSimplexImage X) (Function.support zc))
    (hw : IsLocallyFiniteSet (singularSimplexImage Y) (Function.support wc))
    {φ : Simplex (TopCat.of (X × Y)) (p + q) → R}
    (hφ : φ ∈ vanishing R (p + q) ({((x, y) : X × Y)}ᶜ : Set (TopCat.of (X × Y)))) :
    localPairing (crossFun (p + q) p q zc wc) φ = localPairing zc (slantPairing wc φ) := by
  classical
  obtain ⟨Fz, hFz⟩ : ∃ F : Finset (Simp X p),
      ∀ σ, zc σ ≠ 0 → x ∈ singularSimplexImage X σ → σ ∈ F :=
    ⟨(hz.finite_inter_compact (isCompact_singleton (x := x))).toFinset, fun σ h1 h2 ↦
      (Finite.mem_toFinset _).2 ⟨h1, x, h2, rfl⟩⟩
  obtain ⟨Fw, hFw⟩ : ∃ F : Finset (Simp Y q),
      ∀ τ, wc τ ≠ 0 → y ∈ singularSimplexImage Y τ → τ ∈ F :=
    ⟨(hw.finite_inter_compact (isCompact_singleton (x := y))).toFinset, fun τ h1 h2 ↦
      (Finite.mem_toFinset _).2 ⟨h1, y, h2, rfl⟩⟩
  obtain ⟨T, hT⟩ : ∃ T : Finset (Simp (TopCat.of (X × Y)) (p + q)),
      ∀ st ∈ Fz ×ˢ Fw, (crossSimplex (p + q) st.1 st.2).support ⊆ T :=
    ⟨(Fz ×ˢ Fw).biUnion fun st ↦ (crossSimplex (p + q) st.1 st.2).support,
      fun st hst ρ hρ ↦ Finset.mem_biUnion.2 ⟨st, hst, hρ⟩⟩
  have hxφ : ∀ ρ, φ (SingularCochain.simplexEquiv _ _ ρ) ≠ 0 → ((x, y) : X × Y) ∈ singularSimplexImage _ ρ := fun ρ h ↦ by
    by_contra hx
    exact h (hφ _ fun z hz ↦ by rintro rfl; exact hx ((range_simplexEquiv _).subset hz))
  have step1 : ∀ ρ, crossFun (p + q) p q zc wc ρ * φ (SingularCochain.simplexEquiv _ _ ρ) =
      ∑ st ∈ Fz ×ˢ Fw, zc st.1 * wc st.2 * (crossSimplex (p + q) st.1 st.2 ρ : R) *
        φ (SingularCochain.simplexEquiv _ _ ρ) := by
    intro ρ
    by_cases h : φ (SingularCochain.simplexEquiv _ _ ρ) = 0
    · simp [h]
    have hxy := hxφ ρ h
    rw [← Finset.sum_mul]
    congr 1
    rw [crossFun, lfTransferFun]
    refine finsum_eq_sum_of_support_subset _ fun st hst ↦ ?_
    rw [Function.mem_support] at hst
    simp only [crossFamily, lfTensor] at hst
    have h1 : zc st.1 ≠ 0 := fun h0 ↦ hst (by simp [h0])
    have h2 : wc st.2 ≠ 0 := fun h0 ↦ hst (by simp [h0])
    have h3 : crossSimplex (p + q) st.1 st.2 ρ ≠ 0 := fun h0 ↦ hst (by simp [h0])
    have hsub := singularSimplexImage_subset_of_mem_support _ _ _ h3 hxy
    exact Finset.mem_coe.2 (Finset.mem_product.2 ⟨hFz _ h1 hsub.1, hFw _ h2 hsub.2⟩)
  have lhs : localPairing (crossFun (p + q) p q zc wc) φ =
      ∑ st ∈ Fz ×ˢ Fw, zc st.1 * wc st.2 * evalSimp φ (crossSimplex (p + q) st.1 st.2) := by
    rw [localPairing, finsum_congr step1, finsum_eq_sum_of_support_subset (s := T) _ ?_]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun st hst ↦ ?_
      rw [evalSimp, linearCombination_apply, Finsupp.sum, Finset.mul_sum]
      rw [← Finset.sum_subset (hT st hst) fun ρ _ hρ ↦ by
        simp [Finsupp.notMem_support_iff.1 hρ]]
      refine Finset.sum_congr rfl fun ρ _ ↦ ?_
      rw [zsmul_eq_mul]
      ring
    · intro ρ hρ
      rw [Function.mem_support] at hρ
      obtain ⟨st, hst, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hρ
      refine Finset.mem_coe.2 (hT st hst (Finsupp.mem_support_iff.2 ?_))
      intro h0
      exact hne (by simp [h0])
  have rhs : localPairing zc (slantPairing wc φ) =
      ∑ st ∈ Fz ×ˢ Fw, zc st.1 * wc st.2 * evalSimp φ (crossSimplex (p + q) st.1 st.2) := by
    rw [localPairing_eq_sum_of_subset hFz (slantPairing_mem_vanishing wc hφ), Finset.sum_product]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    simp only [slantPairing, toSimp, Equiv.symm_apply_apply]
    rw [localPairing_eq_sum_of_subset hFw (slantCochain_mem_vanishing hφ σ), Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ ↦ ?_
    simp only [slantCochain, toSimp, Equiv.symm_apply_apply]
    ring
  rw [lhs, rhs]

/-- **Local classes of exterior products.** If `μ ∈ H_p X` is locally the class of `Δ` at `x`,
whose faces avoid `x`, and `ν ∈ H_q Y` is locally the class of `Δ'` at `y`, then for cycles `z`,
`w` representing `μ`, `ν` and every relative cocycle `φ` of `(X × Y, X × Y - (x, y))`,
`⟨φ, z × w⟩ = φ(Δ × Δ')`. -/
theorem localPairing_crossFun_eq_evalSimp {p q : ℕ}
    {μ : borelMooreHomology R (ModuleCat.of R R) X p}
    {ν : borelMooreHomology R (ModuleCat.of R R) Y q} {Δ : Simplex X p} {Δ' : Simplex Y q}
    (hμ : IsLocallyClassOf R μ x Δ) (hν : IsLocallyClassOf R ν y Δ')
    (hΔ : ∀ t : stdSimplex ℝ (Fin (p + 1)), (∃ i, (t : Fin (p + 1) → ℝ) i = 0) → Δ t ≠ x)
    (z : (borelMooreChainComplex R (ModuleCat.of R R) X).cycles p)
    (hz : (borelMooreChainComplex R (ModuleCat.of R R) X).homologyπ p z =
      (borelMooreHomologyIsoOfNat R (ModuleCat.of R R) X p).hom μ)
    (w : (borelMooreChainComplex R (ModuleCat.of R R) Y).cycles q)
    (hw : (borelMooreChainComplex R (ModuleCat.of R R) Y).homologyπ q w =
      (borelMooreHomologyIsoOfNat R (ModuleCat.of R R) Y q).hom ν)
    {φ : Simplex (TopCat.of (X × Y)) (p + q) → R}
    (hφ : φ ∈ relCocycles R ({((x, y) : X × Y)}ᶜ : Set (TopCat.of (X × Y))) (p + q)) :
    localPairing (crossFun (p + q) p q
      (((borelMooreChainComplex R (ModuleCat.of R R) X).iCycles p z).1 :
        (TopCat.toSSet.obj X).obj (op ⦋p⦌) → R)
      (((borelMooreChainComplex R (ModuleCat.of R R) Y).iCycles q w).1 :
        (TopCat.toSSet.obj Y).obj (op ⦋q⦌) → R)) φ =
      evalSimp φ (crossSimplex (p + q) (toSimp Δ) (toSimp Δ')) := by
  have hwd : ∀ j, ((borelMooreChainComplex R (ModuleCat.of R R) Y).d q j).hom
      (((borelMooreChainComplex R (ModuleCat.of R R) Y).iCycles q).hom w) = 0 := fun j ↦ by
    have h := (borelMooreChainComplex R (ModuleCat.of R R) Y).iCycles_d q j
    exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) w :)
  rw [localPairing_crossFun (((borelMooreChainComplex R (ModuleCat.of R R) X).iCycles p z).2)
    (((borelMooreChainComplex R (ModuleCat.of R R) Y).iCycles q w).2) hφ.1,
    hμ z hz _ (slantPairing_mem_relCocycles _ hwd hφ), slantPairing]
  refine hν w hw _ (slantCochain_mem_relCocycles hφ (toSimp Δ) fun t ht ↦ ?_)
  simpa [toSimp] using hΔ t ht

end Slant

end FundamentalClass

end MMP
