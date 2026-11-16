module

public import MMP.AlgebraicTopology.BorelMoore.RestrictionHomotopy

/-!
# Restriction coefficients do not depend on the coefficient ring

The subdivision operators on singular chains (barycentric subdivision, its homotopy, the good
and bad projections towards an open set, and the chains `ρ_N`, `D_N`, `X_N` built from them)
have integer matrices: they commute with the map `ℤ → R` on coefficients. Hence the coefficients
`restrCoeff R U σ τ` of the restriction of a simplex to an open subset of a Hausdorff space are
the images of the integral ones `restrCoeff ℤ U σ τ`.

## Main definitions

* `MMP.SingularChain.castF`: the map `(α →₀ ℤ) → (α →₀ R)`.

## Main results

* `MMP.SingularChain.restrCoeff_eq_intCast`:
  `restrCoeff R U σ τ = (restrCoeff ℤ U σ τ : R)`.
-/

@[expose] public noncomputable section

open Finsupp Set

namespace MMP

namespace SingularChain

variable (R : Type*) [CommRing R]

/-- Integral finitely supported functions as `R`-valued ones. -/
def castF {α : Type*} : (α →₀ ℤ) →+ (α →₀ R) := mapRange.addMonoidHom (Int.castAddHom R)

variable {R}

/-- `castF` sends a single integer `k` at `a` to the single `(k : R)` at `a`. -/
@[simp] lemma castF_single {α : Type*} (a : α) (k : ℤ) : castF R (single a k) = single a (k : R) := by
  simp [castF]

/-- `castF` commutes with scalar multiplication by an integer. -/
lemma castF_zsmul {α : Type*} (k : ℤ) (c : α →₀ ℤ) : castF R (k • c) = (k : R) • castF R c := by
  rw [map_zsmul, Int.cast_smul_eq_zsmul]

/-- `castF` of an integral linear combination is the `R`-linear combination of the cast vectors
with the cast coefficients. -/
lemma castF_linearCombination {α β : Type*} (f : α → β →₀ ℤ) (c : α →₀ ℤ) :
    castF R (linearCombination ℤ f c) =
      linearCombination R (fun a ↦ castF R (f a)) (castF R c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single a k =>
    rw [linearCombination_single, castF_single, linearCombination_single, ← castF_zsmul]

/-- If `castF R (fZ a) = fR a` for all `a`, then `castF` sends the integral linear combination of
the `fZ a` to the `R`-linear combination of the `fR a` with the cast coefficients. -/
lemma castF_linearCombination_of_eq {α β : Type*} (fZ : α → β →₀ ℤ) (fR : α → β →₀ R)
    (h : ∀ a, castF R (fZ a) = fR a) (c : α →₀ ℤ) :
    castF R (linearCombination ℤ fZ c) = linearCombination R fR (castF R c) := by
  rw [castF_linearCombination, show (fun a ↦ castF R (fZ a)) = fR from funext h]

/-- `castF` commutes with `Finsupp.mapDomain`. -/
lemma castF_mapDomain {α β : Type*} (g : α → β) (c : α →₀ ℤ) :
    castF R (mapDomain g c) = mapDomain g (castF R c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, mapDomain_add, hc, hd]
  | single a k => simp [mapDomain_single]

/-- `castF` commutes with multiplication by the sign `(-1) ^ i`. -/
lemma castF_neg_one_pow_smul {α : Type*} (i : ℕ) (c : α →₀ ℤ) :
    castF R ((-1 : ℤ) ^ i • c) = (-1 : R) ^ i • castF R c := by
  rw [castF_zsmul]
  push_cast
  rfl

section vertex

variable {P : Type*}

/-- `castF` commutes with the boundary of vertex chains. -/
lemma castF_vertexBd (k : ℕ) (c : VertexChain.Chain ℤ P (k + 1)) :
    castF R (VertexChain.bd ℤ k c) = VertexChain.bd R k (castF R c) := by
  refine castF_linearCombination_of_eq _ _ (fun v ↦ ?_) c
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [castF_neg_one_pow_smul, castF_single, Int.cast_one]

/-- `castF` commutes with the cone on vertex chains with apex `b`. -/
lemma castF_cone (b : P) (k : ℕ) (c : VertexChain.Chain ℤ P k) :
    castF R (VertexChain.cone ℤ b k c) = VertexChain.cone R b k (castF R c) :=
  castF_mapDomain _ c

/-- `castF` commutes with the barycentric subdivision of vertex chains. -/
lemma castF_vertexSubdiv (bary : VertexChain.Bary P) :
    ∀ (k : ℕ) (c : VertexChain.Chain ℤ P k),
      castF R (VertexChain.subdiv ℤ bary k c) = VertexChain.subdiv R bary k (castF R c)
  | 0, _ => rfl
  | k + 1, c => by
    rw [VertexChain.subdiv.eq_2, VertexChain.subdiv.eq_2]
    change castF R (linearCombination ℤ _ c) = linearCombination R _ (castF R c)
    refine castF_linearCombination_of_eq _ _ (fun v ↦ ?_) c
    rw [castF_cone, castF_vertexSubdiv bary k, castF_vertexBd, castF_single, Int.cast_one]

/-- `castF` commutes with the subdivision homotopy of vertex chains. -/
lemma castF_vertexSubdivHomotopy (bary : VertexChain.Bary P) :
    ∀ (k : ℕ) (c : VertexChain.Chain ℤ P k),
      castF R (VertexChain.subdivHomotopy ℤ bary k c) =
        VertexChain.subdivHomotopy R bary k (castF R c)
  | 0, _ => by simp [VertexChain.subdivHomotopy_zero]
  | k + 1, c => by
    rw [VertexChain.subdivHomotopy.eq_2, VertexChain.subdivHomotopy.eq_2]
    change castF R (linearCombination ℤ _ c) = linearCombination R _ (castF R c)
    refine castF_linearCombination_of_eq _ _ (fun v ↦ ?_) c
    rw [castF_cone, map_sub, castF_vertexSubdivHomotopy bary k, castF_vertexBd, castF_single,
      Int.cast_one]

end vertex

variable {Y : Type*} [TopologicalSpace Y]

/-- `castF` commutes with pushing forward vertex chains of the standard simplex along `σ`. -/
lemma castF_push {n : ℕ} (σ : Simplex Y n) (k : ℕ)
    (c : VertexChain.Chain ℤ (stdSimplex ℝ (Fin (n + 1))) (k + 1)) :
    castF R (push ℤ σ k c) = push R σ k (castF R c) :=
  castF_mapDomain _ c

/-- `castF` commutes with the singular boundary. -/
lemma castF_bd (n : ℕ) (c : Chain ℤ Y (n + 1)) : castF R (bd ℤ n c) = bd R n (castF R c) := by
  refine castF_linearCombination_of_eq _ _ (fun σ ↦ ?_) c
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [castF_neg_one_pow_smul, castF_single, Int.cast_one]

/-- `castF` commutes with barycentric subdivision of singular chains. -/
lemma castF_subdiv (n : ℕ) (c : Chain ℤ Y n) : castF R (subdiv ℤ n c) = subdiv R n (castF R c) := by
  refine castF_linearCombination_of_eq _ _ (fun σ ↦ ?_) c
  rw [castF_push, castF_vertexSubdiv, castF_single, Int.cast_one]

/-- `castF` commutes with the subdivision homotopy of singular chains. -/
lemma castF_subdivHomotopy (n : ℕ) (c : Chain ℤ Y n) :
    castF R (subdivHomotopy ℤ n c) = subdivHomotopy R n (castF R c) := by
  refine castF_linearCombination_of_eq _ _ (fun σ ↦ ?_) c
  rw [castF_push, castF_vertexSubdivHomotopy, castF_single, Int.cast_one]

variable {U : Set Y}

/-- `castF` commutes with the projection onto simplices with image in `U`. -/
lemma castF_goodProj (n : ℕ) (c : Chain ℤ Y n) :
    castF R (goodProj ℤ U n c) = goodProj R U n (castF R c) := by
  classical
  refine castF_linearCombination_of_eq _ _ (fun σ ↦ ?_) c
  split_ifs <;> simp

/-- `castF` commutes with the projection onto simplices whose image is not contained in `U`. -/
lemma castF_badProj (n : ℕ) (c : Chain ℤ Y n) :
    castF R (badProj ℤ U n c) = badProj R U n (castF R c) := by
  simp only [badProj, LinearMap.sub_apply, LinearMap.id_apply, map_sub, castF_goodProj]

/-- `castF` commutes with the chain `badChain U N`. -/
lemma castF_badChain (N n : ℕ) (c : Chain ℤ Y n) :
    castF R (badChain ℤ U N n c) = badChain R U N n (castF R c) := by
  induction N with
  | zero => rw [badChain_zero, badChain_zero, castF_badProj]
  | succ N ih => rw [badChain_succ, badChain_succ, castF_badProj, castF_subdiv, ih]

/-- `castF` commutes with the homotopy `towardsHomotopy U N`. -/
lemma castF_towardsHomotopy (N n : ℕ) (c : Chain ℤ Y n) :
    castF R (towardsHomotopy ℤ U N n c) = towardsHomotopy R U N n (castF R c) := by
  simp only [towardsHomotopy, LinearMap.sum_apply, map_sum, LinearMap.comp_apply,
    castF_subdivHomotopy, castF_badChain]

/-- `castF` commutes with the chain map `towardsChainMap U N`. -/
lemma castF_towardsChainMap (N : ℕ) : ∀ (n : ℕ) (c : Chain ℤ Y n),
    castF R (towardsChainMap ℤ U N n c) = towardsChainMap R U N n (castF R c)
  | 0, c => by
    rw [towardsChainMap_zero_apply, towardsChainMap_zero_apply, map_sub, castF_bd,
      castF_towardsHomotopy]
  | n + 1, c => by
    rw [towardsChainMap_succ_apply, towardsChainMap_succ_apply, map_sub, map_sub, castF_bd,
      castF_towardsHomotopy, castF_towardsHomotopy, castF_bd]

/-- `castF` sends the integral chain `goodPart ℤ U N σ` to `goodPart R U N σ`. -/
lemma castF_goodPart (N : ℕ) {n : ℕ} (σ : Simplex Y n) :
    castF R (goodPart ℤ U N σ) = goodPart R U N σ := by
  rw [goodPart, goodPart, castF_goodProj, castF_towardsChainMap, castF_single, Int.cast_one]

/-- The coefficients of `goodPart R U N σ` are the images of those of `goodPart ℤ U N σ`. -/
lemma goodPart_apply_eq_intCast (N : ℕ) {n : ℕ} (σ τ : Simplex Y n) :
    goodPart R U N σ τ = (goodPart ℤ U N σ τ : R) := by
  rw [← castF_goodPart]
  rfl

/-- The restriction coefficients over `R` are the images of the integral ones. -/
lemma restrCoeff_eq_intCast [T2Space Y] (hU : IsOpen U) {n : ℕ} (σ τ : Simplex Y n) :
    restrCoeff R U σ τ = (restrCoeff ℤ U σ τ : R) := by
  by_cases hτ : range τ ⊆ U
  · obtain ⟨V, W, hV, -, hσV, hτW, hVW⟩ :=
      separatedNhds_range_inter_compl hU σ (isCompact_range τ.continuous) hτ
    have hτW' : (range τ ∩ W).Nonempty := ⟨_, ⟨stdSimplex.vertex 0, rfl⟩, hτW ⟨_, rfl⟩⟩
    obtain ⟨M₁, h₁⟩ := exists_restrCoeff_eq_goodPart_of_disjoint (R := R) hU σ hV hVW hσV
    obtain ⟨M₂, h₂⟩ := exists_restrCoeff_eq_goodPart_of_disjoint (R := ℤ) hU σ hV hVW hσV
    rw [h₁ (max M₁ M₂) (le_max_left _ _) τ hτW', h₂ (max M₁ M₂) (le_max_right _ _) τ hτW',
      goodPart_apply_eq_intCast]
  · have h1 : restrCoeff R U σ τ = 0 := by
      by_contra h
      exact hτ ((range_subset_of_restrCoeff_ne_zero h).trans inter_subset_right)
    have h2 : restrCoeff ℤ U σ τ = 0 := by
      by_contra h
      exact hτ ((range_subset_of_restrCoeff_ne_zero h).trans inter_subset_right)
    rw [h1, h2, Int.cast_zero]

end SingularChain

end MMP
