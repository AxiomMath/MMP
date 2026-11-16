module

public import MMP.AlgebraicTopology.SingularCohomology.CupProduct
/-!
# Graded commutativity of the cup product (Fulton, §19.1)

For closed subsets `X`, `W` of a space `Y`, `u ∈ H^i(Y, Y - X)` and `v ∈ H^j(Y, Y - W)`,
`v ∪ u = (-1)^{ij} u ∪ v` in `H^{i+j}(Y, Y - (X ∩ W))`.

The proof is Hatcher's (Theorem 3.11). The *reversal* of a singular `n`-simplex `σ` is
`σ̄ = σ ∘ rev`, `rev` the affine map reversing the order of the vertices, and the chain map
`r σ = ε_n σ̄`, `ε_n = (-1)^{n(n+1)/2}`, satisfies `r^* (φ ∪ ψ) = (-1)^{pq} r^* ψ ∪ r^* φ` on
cochains. The map `r` is chain homotopic to the identity by a natural homotopy `D`, built on
vertex chains by the cone construction `D [v] = v₀ · ([v] - r [v] - D ∂ [v])` (coning off from the
first vertex), so `D` sends chains of a subspace to chains of that subspace. Hence `r^*` is the
identity on relative cohomology and on the small-chains cohomology of the couple
`{Y - X, Y - W}`, which gives graded commutativity.

## Main definitions

* `MMP.VertexChain.reversal`: the reversal of vertex chains.
* `MMP.VertexChain.reversalHomotopy`: the cone homotopy from `1` to the reversal.
* `MMP.SingularChain.reversal`: the reversal `r` of singular chains.
* `MMP.SingularChain.reversalHomotopy`: the homotopy `D`, `∂ D + D ∂ = 1 - r`.

## Main results

* `MMP.SingularCochain.pullback_reversal_cup`:
  `r^* (φ ∪ ψ) = (-1)^{pq} r^* ψ ∪ r^* φ`.
* `MMP.cohomologyWithSupports.relCup_comm`: graded commutativity of the relative
  cup product of `H^*(Y, A)` and `H^*(Y, B)`, `A`, `B` open.
* `MMP.cohomologyWithSupports.cup_comm`: graded commutativity of the cup product.

## Implementation notes

The two sides of `v ∪ u = (-1)^{ij} u ∪ v` lie in `H^{j+i}(Y, Y - (W ∩ X))` and
`H^{i+j}(Y, Y - (X ∩ W))`, which agree only up to the equalities `W ∩ X = X ∩ W` and
`j + i = i + j`; the left side is transported along them by
`MMP.cohomologyWithSupports.congrIndex`. The sign is `(-1 : Rˣ) ^ (i * j)`; both
sides vanish in negative degrees.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [A. Hatcher, *Algebraic Topology*][hatcher2002], §3.2, Theorem 3.11.
-/

@[expose] public noncomputable section

open Finsupp Set

universe u

namespace MMP

/-- The sign `ε_n = (-1)^{n(n+1)/2}` of the reversal of an `n`-simplex. -/
def reversalSign (R : Type*) [CommRing R] (n : ℕ) : R := (-1) ^ (n * (n + 1) / 2)

section sign

variable {R : Type*} [CommRing R]

/-- `ε_0 = 1`. -/
lemma reversalSign_zero : reversalSign R 0 = 1 := by simp [reversalSign]

private lemma two_mul_triangle (n : ℕ) : 2 * (n * (n + 1) / 2) = n * (n + 1) :=
  Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self n)

/-- `ε_{p+q} = (-1)^{pq} ε_p ε_q`. -/
lemma reversalSign_add (p q : ℕ) :
    reversalSign R (p + q) = (-1) ^ (p * q) * reversalSign R p * reversalSign R q := by
  have h : (p + q) * (p + q + 1) / 2 = p * (p + 1) / 2 + q * (q + 1) / 2 + p * q := by
    have h1 := two_mul_triangle p
    have h2 := two_mul_triangle q
    have h3 := two_mul_triangle (p + q)
    have : 2 * ((p + q) * (p + q + 1) / 2) =
        2 * (p * (p + 1) / 2 + q * (q + 1) / 2 + p * q) := by
      rw [h3, Nat.mul_add 2, Nat.mul_add 2, h1, h2]; ring
    omega
  simp only [reversalSign, h, pow_add]
  ring

/-- `ε_{k+1} = (-1)^{k+1} ε_k`. -/
lemma reversalSign_succ (k : ℕ) : reversalSign R (k + 1) = (-1) ^ (k + 1) * reversalSign R k := by
  rw [reversalSign_add, reversalSign]
  simp [reversalSign, mul_comm, pow_succ]

end sign

namespace VertexChain

variable (R : Type*) [CommRing R] {P : Type*}

/-- The reversal `[v] ↦ ε_k [v ∘ rev]` of vertex chains of length `k + 1`; the identity in
length `0`. -/
def reversal : ∀ k : ℕ, Chain R P k →ₗ[R] Chain R P k
  | 0 => LinearMap.id
  | k + 1 => reversalSign R k • lmapDomain R R fun v : Fin (k + 1) → P ↦ v ∘ Fin.rev

variable {R}

/-- The reversal of a basis vertex chain: `r [v] = ε_k [v ∘ rev]`. -/
lemma reversal_single (k : ℕ) (v : Fin (k + 1) → P) :
    reversal R (k + 1) (single v 1) = reversalSign R k • single (v ∘ Fin.rev) 1 := by
  simp [reversal]

/-- The reversal is the identity on vertex chains of length `1`. -/
lemma reversal_one (c : Chain R P 1) : reversal R 1 c = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single v a =>
    rw [← mul_one a, ← smul_eq_mul, ← smul_single, map_smul, reversal_single, reversalSign_zero,
      one_smul]
    congr 2
    funext i
    have hi : i.rev = i := Fin.ext (by have := i.isLt; rw [Fin.val_rev]; omega)
    simp [hi]

/-- The reversal is a chain map. -/
lemma bd_reversal (k : ℕ) (c : Chain R P (k + 1)) :
    bd R k (reversal R (k + 1) c) = reversal R k (bd R k c) := by
  cases k with
  | zero => rw [reversal_one]; rfl
  | succ k =>
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => simp only [map_add, hc, hd]
    | single v a =>
      rw [← mul_one a, ← smul_eq_mul, ← smul_single, map_smul, map_smul, map_smul, map_smul,
        reversal_single, map_smul, bd_single, bd_single, map_sum]
      congr 1
      simp only [map_smul, reversal_single, Finset.smul_sum, smul_smul]
      refine Fintype.sum_equiv Fin.revPerm _ _ fun i ↦ ?_
      have hv : v ∘ Fin.rev ∘ i.succAbove = (v ∘ (Fin.revPerm i).succAbove) ∘ Fin.rev := by
        funext j
        simp [Fin.rev_succAbove]
      rw [Function.comp_assoc, hv]
      congr 1
      rw [reversalSign_succ, Fin.revPerm_apply, Fin.val_rev]
      have hi := i.isLt
      have : (-1 : R) ^ (k + 1 + 1 - (i + 1)) = (-1) ^ (i : ℕ) * (-1) ^ (k + 1) := by
        rw [← pow_add, neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := (i : ℕ) + _)]
        congr 1
        omega
      rw [this]
      ring

/-- The cone homotopy `D [v] = v₀ · ([v] - r [v] - D ∂ [v])`, `D = 0` in length `0`. -/
def reversalHomotopy : ∀ k : ℕ, Chain R P k →ₗ[R] Chain R P (k + 1)
  | 0 => 0
  | k + 1 => linearCombination R fun v ↦ cone R (v 0) (k + 1)
      (single v 1 - reversal R (k + 1) (single v 1) - reversalHomotopy k (bd R k (single v 1)))

/-- The cone homotopy on a basis vertex chain: `D [v] = v₀ · ([v] - r [v] - D ∂ [v])`. -/
lemma reversalHomotopy_single (k : ℕ) (v : Fin (k + 1) → P) :
    reversalHomotopy (k + 1) (single v 1) = cone R (v 0) (k + 1)
      (single v 1 - reversal R (k + 1) (single v 1) -
        reversalHomotopy k (bd R k (single v 1))) := by
  simp [reversalHomotopy]

/-- `∂ D + D ∂ = 1 - r`. -/
lemma bd_reversalHomotopy_add (k : ℕ) (c : Chain R P (k + 1)) :
    bd R (k + 1) (reversalHomotopy (k + 1) c) + reversalHomotopy k (bd R k c) =
      c - reversal R (k + 1) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    simp only [map_add]
    rw [add_add_add_comm, hc, hd]
    abel
  | single v a =>
    rw [← mul_one a, ← smul_eq_mul, ← smul_single]
    simp only [map_smul, ← smul_add, ← smul_sub]
    congr 1
    have hx : bd R k (single v 1 - reversal R (k + 1) (single v 1) -
        reversalHomotopy k (bd R k (single v 1))) = 0 := by
      cases k with
      | zero => simp [reversalHomotopy, reversal_one]
      | succ k =>
        have ih := bd_reversalHomotopy_add k (bd R (k + 1) (single v 1))
        rw [bd_bd, map_zero, add_zero] at ih
        rw [map_sub, map_sub, ih, bd_reversal]
        abel
    rw [reversalHomotopy_single, bd_cone, hx, map_zero, sub_zero]
    abel

section map

variable {Q : Type*} (f : P → Q)

/-- The reversal is natural in the points. -/
lemma map_reversal (k : ℕ) (c : Chain R P k) :
    map R f k (reversal R k c) = reversal R k (map R f k c) := by
  cases k with
  | zero => rfl
  | succ k =>
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => simp only [map_add, hc, hd]
    | single v a =>
      rw [← mul_one a, ← smul_eq_mul, ← smul_single, map_smul, map_smul, map_smul, map_smul,
        reversal_single, map_smul, map_single, map_single, reversal_single]
      rfl

/-- The homotopy is natural in the points. -/
lemma map_reversalHomotopy (k : ℕ) (c : Chain R P k) :
    map R f (k + 1) (reversalHomotopy k c) = reversalHomotopy k (map R f k c) := by
  induction k with
  | zero => simp [reversalHomotopy]
  | succ k ih =>
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => simp only [map_add, hc, hd]
    | single v a =>
      rw [← mul_one a, ← smul_eq_mul, ← smul_single, map_smul, map_smul, map_smul, map_smul,
        reversalHomotopy_single, map_single, reversalHomotopy_single, map_cone]
      simp only [map_sub, map_reversal, ih, map_bd, map_single]
      rfl

end map

end VertexChain

namespace SingularChain

open SingularCochain (smap comp_smap_comp)

variable {R : Type*} [CommRing R] {Y : Type*} [TopologicalSpace Y]

variable (R) in
/-- Push-forward of vertex chains on the vertex set of `Δⁿ` along a singular `n`-simplex `σ`: a
tuple `w` of vertices goes to the simplicial simplex `σ ∘ w`. -/
def pushVertices {n : ℕ} (σ : Simplex Y n) (k : ℕ) :
    VertexChain.Chain R (Fin (n + 1)) (k + 1) →ₗ[R] Chain R Y k :=
  lmapDomain R R fun w ↦ σ.comp (smap w)

/-- The push-forward of a basis vertex chain `[w]` along `σ` is the simplex `σ ∘ w`. -/
lemma pushVertices_single {n : ℕ} (σ : Simplex Y n) (k : ℕ) (w : Fin (k + 1) → Fin (n + 1)) :
    pushVertices R σ k (single w 1) = single (σ.comp (smap w)) 1 := by
  simp [pushVertices]

/-- The affine self-map of `Δⁿ` induced by the identity of the vertices is the identity. -/
lemma smap_id (n : ℕ) : smap (id : Fin (n + 1) → Fin (n + 1)) = ContinuousMap.id _ := by
  ext1 t; exact stdSimplex.map_id_apply t

/-- `σ ∘ id = σ` for a singular simplex `σ`. -/
lemma comp_smap_id {n : ℕ} (σ : Simplex Y n) : σ.comp (smap id) = σ := by
  rw [smap_id]; rfl

/-- Push-forward along a singular simplex commutes with the boundary. -/
lemma bd_pushVertices {n : ℕ} (σ : Simplex Y n) (k : ℕ)
    (c : VertexChain.Chain R (Fin (n + 1)) (k + 2)) :
    bd R k (pushVertices R σ (k + 1) c) = pushVertices R σ k (VertexChain.bd R (k + 1) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single w a =>
    rw [← mul_one a, ← smul_eq_mul, ← smul_single, map_smul, map_smul, map_smul, map_smul,
      pushVertices_single, bd_single, VertexChain.bd_single, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, pushVertices_single]
    congr 2
    exact comp_smap_comp σ w i.succAbove

/-- Push-forward along `σ ∘ u` is push-forward along `σ` after mapping the vertices by `u`. -/
lemma pushVertices_comp {n m : ℕ} (σ : Simplex Y n) (u : Fin (m + 1) → Fin (n + 1)) (k : ℕ)
    (c : VertexChain.Chain R (Fin (m + 1)) (k + 1)) :
    pushVertices R (σ.comp (smap u)) k c =
      pushVertices R σ k (VertexChain.map R u (k + 1) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single w a =>
    rw [← mul_one a, ← smul_eq_mul, ← smul_single, map_smul, map_smul, map_smul,
      pushVertices_single, VertexChain.map_single, pushVertices_single, comp_smap_comp]

/-- Push-forward along a simplex with image in `U` gives a chain of `U`. -/
lemma pushVertices_mem_inside {n : ℕ} (σ : Simplex Y n) (k : ℕ)
    (c : VertexChain.Chain R (Fin (n + 1)) (k + 1)) {U : Set Y} (hσ : range σ ⊆ U) :
    pushVertices R σ k c ∈ inside R k U := by
  have hc : c ∈ supported R R univ := by simp
  refine VertexChain.mem_of_mem_supported _ _ (fun w _ ↦ ?_) hc
  rw [pushVertices_single]
  exact single_mem_supported R _ (show range (σ.comp (smap w)) ⊆ U by
    rintro _ ⟨t, rfl⟩; exact hσ ⟨_, rfl⟩)

variable (R) in
/-- The reversal `r σ = ε_n σ ∘ rev` of singular `n`-chains, `rev` reversing the vertices. -/
def reversal (n : ℕ) : Chain R Y n →ₗ[R] Chain R Y n :=
  linearCombination R fun σ ↦ reversalSign R n • single (σ.comp (smap Fin.rev)) 1

/-- The reversal of a singular simplex: `r σ = ε_n σ ∘ rev`. -/
lemma reversal_single (n : ℕ) (σ : Simplex Y n) :
    reversal R n (single σ 1) = reversalSign R n • single (σ.comp (smap Fin.rev)) 1 := by
  simp [reversal]

/-- Pushing the reversed identity vertex chain forward along `σ` gives `r σ`. -/
lemma pushVertices_reversal {n : ℕ} (σ : Simplex Y n) :
    pushVertices R σ n (VertexChain.reversal R (n + 1) (single id 1)) =
      reversal R n (single σ 1) := by
  rw [VertexChain.reversal_single, map_smul, pushVertices_single, reversal_single]
  rfl

/-- The reversal is the identity in degree `0`. -/
lemma reversal_zero (c : Chain R Y 0) : reversal R 0 c = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single σ a =>
    rw [← mul_one a, ← smul_eq_mul, ← smul_single, map_smul, reversal_single, reversalSign_zero,
      one_smul]
    have : (Fin.rev : Fin 1 → Fin 1) = id := funext fun i ↦
      Fin.ext (by have := i.isLt; rw [Fin.val_rev]; omega)
    rw [this, comp_smap_id]

variable (R) in
/-- The natural chain homotopy `D` between the identity and the reversal. -/
def reversalHomotopy (n : ℕ) : Chain R Y n →ₗ[R] Chain R Y (n + 1) :=
  linearCombination R fun σ ↦
    pushVertices R σ (n + 1) (VertexChain.reversalHomotopy (n + 1) (single id 1))

/-- `D σ` is the push-forward along `σ` of the cone homotopy of the identity vertex chain. -/
lemma reversalHomotopy_single (n : ℕ) (σ : Simplex Y n) :
    reversalHomotopy R n (single σ 1) =
      pushVertices R σ (n + 1) (VertexChain.reversalHomotopy (n + 1) (single id 1)) := by
  simp [reversalHomotopy]

/-- `∂ D + D ∂ = 1 - r`. -/
lemma bd_reversalHomotopy_add (n : ℕ) (c : Chain R Y (n + 1)) :
    bd R (n + 1) (reversalHomotopy R (n + 1) c) + reversalHomotopy R n (bd R n c) =
      c - reversal R (n + 1) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add]; rw [add_add_add_comm, hc, hd]; abel
  | single σ a =>
    rw [← mul_one a, ← smul_eq_mul, ← smul_single]
    simp only [map_smul, ← smul_add, ← smul_sub]
    congr 1
    have e2 : reversalHomotopy R n (bd R n (single σ 1)) = pushVertices R σ (n + 1)
        (VertexChain.reversalHomotopy (n + 1) (VertexChain.bd R (n + 1) (single id 1))) := by
      rw [bd_single, VertexChain.bd_single, map_sum, map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [map_smul, map_smul, map_smul, reversalHomotopy_single]
      congr 1
      rw [show σ.comp (face n i) = σ.comp (smap i.succAbove) from rfl, pushVertices_comp,
        VertexChain.map_reversalHomotopy, VertexChain.map_single]
      rfl
    rw [reversalHomotopy_single, bd_pushVertices, e2, ← map_add,
      VertexChain.bd_reversalHomotopy_add, map_sub, pushVertices_single, comp_smap_id,
      pushVertices_reversal]

/-- `D` sends chains of `U` to chains of `U`. -/
lemma reversalHomotopy_mem_inside {n : ℕ} {U : Set Y} {c : Chain R Y n} (hc : c ∈ inside R n U) :
    reversalHomotopy R n c ∈ inside R (n + 1) U :=
  VertexChain.mem_of_mem_supported _ _ (fun σ hσ ↦ by
    rw [reversalHomotopy_single]; exact pushVertices_mem_inside σ _ _ hσ) hc

/-- `D` sends `𝒰`-small chains to `𝒰`-small chains. -/
lemma reversalHomotopy_mem_small {n : ℕ} {𝒰 : Set (Set Y)} {c : Chain R Y n}
    (hc : c ∈ small R n 𝒰) : reversalHomotopy R n c ∈ small R (n + 1) 𝒰 :=
  VertexChain.mem_of_mem_supported _ _ (fun σ hσ ↦ by
    obtain ⟨U, hU, hσU⟩ := hσ
    exact mem_small_of_mem_inside hU
      (reversalHomotopy_mem_inside (single_mem_supported R (1 : R) hσU))) hc

end SingularChain

namespace SingularCochain

open SingularChain

variable {R : Type*} [CommRing R] {Y : Type*} [TopologicalSpace Y]

/-- `(r^* θ)(σ) = ε_n θ(σ ∘ rev)`. -/
lemma pullback_reversal_apply (n : ℕ) (θ : Simplex Y n → R) (σ : Simplex Y n) :
    pullback (reversal R n) θ σ = reversalSign R n * θ (σ.comp (smap Fin.rev)) := by
  change eval θ (reversal R n (single σ 1)) = _
  rw [reversal_single, map_smul, eval, linearCombination_single, one_smul, smul_eq_mul]

/-- `r^* (φ ∪ ψ) = (-1)^{pq} r^* ψ ∪ r^* φ`. -/
lemma pullback_reversal_cup (p q n : ℕ) (h : p + q = n) (h' : q + p = n) (φ : Simplex Y p → R)
    (ψ : Simplex Y q → R) :
    pullback (reversal R n) (cup p q n h φ ψ) =
      (-1 : R) ^ (p * q) •
        cup q p n h' (pullback (reversal R q) ψ) (pullback (reversal R p) φ) := by
  subst h
  ext σ
  rw [Pi.smul_apply, smul_eq_mul]
  simp only [pullback_reversal_apply, cup_apply, comp_smap_comp]
  have e1 : (Fin.rev ∘ front p (p + q) (by omega)) = back p (p + q) q (by omega) ∘ Fin.rev := by
    funext j; apply Fin.ext; have := j.isLt
    simp only [Function.comp_apply, Fin.val_rev, front_val, back_val]; omega
  have e2 : (Fin.rev ∘ back q (p + q) p (by omega)) = front q (p + q) (by omega) ∘ Fin.rev := by
    funext j; apply Fin.ext; have := j.isLt
    simp only [Function.comp_apply, Fin.val_rev, front_val, back_val]; omega
  rw [e1, e2, reversalSign_add]
  ring

variable (R) in
/-- The dual `D^*` of the reversal homotopy, from `(n + 1)`-cochains to `n`-cochains. -/
def reversalHomotopyDual (n : ℕ) : (Simplex Y (n + 1) → R) →ₗ[R] (Simplex Y n → R) where
  toFun θ σ := eval θ (reversalHomotopy R n (single σ 1))
  map_add' φ ψ := by ext σ; simp [linearCombination_apply, mul_add, Finsupp.sum_add]
  map_smul' r φ := by ext σ; simp [linearCombination_apply, Finsupp.mul_sum, mul_left_comm]

/-- `D^* θ` evaluated on a chain `c` is `θ` evaluated on `D c`. -/
lemma eval_reversalHomotopyDual (n : ℕ) (θ : Simplex Y (n + 1) → R) (c : Chain R Y n) :
    eval (reversalHomotopyDual R n θ) c = eval θ (reversalHomotopy R n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single σ a =>
    rw [← mul_one a, ← smul_eq_mul, ← smul_single, map_smul, map_smul, map_smul]
    simp [reversalHomotopyDual]

/-- On cochains, `r^* = 1 - δ D^* - D^* δ`. -/
lemma pullback_reversal_succ (n : ℕ) (θ : Simplex Y (n + 1) → R) :
    pullback (reversal R (n + 1)) θ = θ - coboundary R n (reversalHomotopyDual R n θ) -
      reversalHomotopyDual R (n + 1) (coboundary R (n + 1) θ) := by
  ext σ
  have h := bd_reversalHomotopy_add (R := R) n (single σ 1)
  have h' : reversal R (n + 1) (single σ 1) = single σ 1 -
      reversalHomotopy R n (bd R n (single σ 1)) -
        bd R (n + 1) (reversalHomotopy R (n + 1) (single σ 1)) := by
    rw [sub_sub, add_comm (reversalHomotopy R n _), h, sub_sub_cancel]
  change eval θ (reversal R (n + 1) (single σ 1)) = _
  rw [h', map_sub, map_sub, ← eval_coboundary, ← eval_reversalHomotopyDual,
    ← eval_reversalHomotopyDual, ← eval_coboundary]
  simp

/-- `r^*` is the identity on `0`-cochains. -/
lemma pullback_reversal_zero (θ : Simplex Y 0 → R) : pullback (reversal R 0) θ = θ := by
  ext σ
  change eval θ (reversal R 0 (single σ 1)) = _
  rw [reversal_zero]
  simp

/-- A cochain vanishing on the simplices of `A` vanishes on every chain of `A`. -/
lemma eval_eq_zero_of_mem_inside {n : ℕ} {A : Set Y} {θ : Simplex Y n → R}
    (hθ : θ ∈ vanishing R n A) {c : Chain R Y n} (hc : c ∈ inside R n A) : eval θ c = 0 := by
  have := VertexChain.mem_of_mem_supported (eval θ) ⊥ (fun σ hσ ↦ by
    rw [Submodule.mem_bot, eval, linearCombination_single, one_smul]
    exact hθ σ hσ) hc
  simpa using this

/-- `D^*` sends cochains vanishing on `A` to cochains vanishing on `A`. -/
lemma reversalHomotopyDual_mem_vanishing {n : ℕ} {A : Set Y} {θ : Simplex Y (n + 1) → R}
    (hθ : θ ∈ vanishing R (n + 1) A) : reversalHomotopyDual R n θ ∈ vanishing R n A :=
  fun _ hσ ↦ eval_eq_zero_of_mem_inside hθ
    (reversalHomotopy_mem_inside (single_mem_supported R (1 : R) hσ))

variable (R) in
/-- The coboundaries of cochains vanishing on the simplices of `A` and on those of `B`. -/
def pairCoboundaries (A B : Set Y) : ∀ n : ℕ, Submodule R (Simplex Y n → R)
  | 0 => ⊥
  | n + 1 => (vanishing R n A ⊓ vanishing R n B).map (coboundary R n)

/-- For `B = A`, these are the relative coboundaries of `A`. -/
lemma pairCoboundaries_self (A : Set Y) (n : ℕ) :
    pairCoboundaries R A A n = relCoboundaries R A n := by
  cases n <;> simp [pairCoboundaries, relCoboundaries]

/-- `pairCoboundaries` is symmetric in `A` and `B`. -/
lemma pairCoboundaries_comm (A B : Set Y) (n : ℕ) :
    pairCoboundaries R A B n = pairCoboundaries R B A n := by
  cases n <;> simp [pairCoboundaries, inf_comm]

/-- For a cocycle `θ` vanishing on `A` and on `B`, `r^* θ - θ` is the coboundary of a cochain
vanishing on `A` and on `B`. -/
lemma pullback_reversal_sub_mem_pairCoboundaries {A B : Set Y} {m : ℕ} {θ : Simplex Y m → R}
    (hθ : θ ∈ vanishing R m A ⊓ vanishing R m B) (hδ : coboundary R m θ = 0) :
    pullback (reversal R m) θ - θ ∈ pairCoboundaries R A B m := by
  cases m with
  | zero => rw [pullback_reversal_zero, sub_self]; exact zero_mem _
  | succ m =>
    rw [pullback_reversal_succ, hδ, map_zero, sub_zero, sub_sub_cancel_left]
    exact ⟨-reversalHomotopyDual R m θ, neg_mem ⟨reversalHomotopyDual_mem_vanishing hθ.1,
      reversalHomotopyDual_mem_vanishing hθ.2⟩, map_neg _ _⟩

/-- For a relative cocycle `θ` of `A`, `r^* θ - θ` is a relative coboundary of `A`. -/
lemma pullback_reversal_sub_mem_relCoboundaries {A : Set Y} {m : ℕ} {θ : Simplex Y m → R}
    (hθ : θ ∈ relCocycles R A m) :
    pullback (reversal R m) θ - θ ∈ relCoboundaries R A m := by
  rw [← pairCoboundaries_self]
  exact pullback_reversal_sub_mem_pairCoboundaries ⟨hθ.1, hθ.1⟩ hθ.2

/-- The cup product of a relative coboundary of `A` with a relative cocycle of `B` is the
coboundary of a cochain vanishing on `A` and on `B`. -/
lemma cup_mem_pairCoboundaries_left {A B : Set Y} (p q n : ℕ) (h : p + q = n)
    {α : Simplex Y p → R} (hα : α ∈ relCoboundaries R A p) {β : Simplex Y q → R}
    (hβ : β ∈ relCocycles R B q) : cup p q n h α β ∈ pairCoboundaries R A B n := by
  cases p with
  | zero => rw [show α = 0 from hα, map_zero, LinearMap.zero_apply]; exact zero_mem _
  | succ p =>
    obtain rfl : n = p + q + 1 := by omega
    obtain ⟨γ, hγ, rfl⟩ := hα
    have h2 : coboundary R q β = 0 := hβ.2
    refine ⟨cup p q (p + q) rfl γ β, cup_mem_vanishing rfl hγ hβ.1, ?_⟩
    rw [coboundary_cup, h2]
    simp

/-- The cup product of a relative cocycle of `A` with a relative coboundary of `B` is the
coboundary of a cochain vanishing on `A` and on `B`. -/
lemma cup_mem_pairCoboundaries_right {A B : Set Y} (p q n : ℕ) (h : p + q = n)
    {α : Simplex Y p → R} (hα : α ∈ relCocycles R A p) {β : Simplex Y q → R}
    (hβ : β ∈ relCoboundaries R B q) : cup p q n h α β ∈ pairCoboundaries R A B n := by
  cases q with
  | zero => rw [show β = 0 from hβ, map_zero]; exact zero_mem _
  | succ q =>
    obtain rfl : n = p + q + 1 := by omega
    obtain ⟨γ, hγ, rfl⟩ := hβ
    have h1 : coboundary R p α = 0 := hα.2
    refine ⟨(-1 : R) ^ p • cup p q (p + q) rfl α γ,
      Submodule.smul_mem _ _ (cup_mem_vanishing rfl hα.1 hγ), ?_⟩
    rw [map_smul, coboundary_cup, h1]
    simp only [map_zero, LinearMap.zero_apply, zero_add, smul_smul, ← pow_add,
      ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]

/-- For `A`, `B` open, the pullback along the small-chains map of `{A, B}` of the coboundary
of a cochain vanishing on `A` and on `B` is a relative coboundary of `A ∪ B`. -/
lemma pullback_smallChainMap_mem_relCoboundaries {A B : Set Y} (hA : IsOpen A) (hB : IsOpen B)
    {n : ℕ} {χ : Simplex Y n → R} (hχ : χ ∈ pairCoboundaries R A B n) :
    pullback (smallChainMap R {A, B} n) χ ∈ relCoboundaries R (A ∪ B) n := by
  cases n with
  | zero => rw [show χ = 0 from hχ, map_zero]; exact zero_mem _
  | succ n =>
    obtain ⟨γ, hγ, rfl⟩ := hχ
    exact ⟨pullback (smallChainMap R {A, B} n) γ, pullback_mem_vanishing hA hB hγ,
      coboundary_pullback_smallChainMap _ n γ⟩

/-- Graded commutativity of the cup product of relative cocycles, up to coboundaries:
`ψ ∪ φ - (-1)^{pq} φ ∪ ψ` is the coboundary of a cochain vanishing on `A` and on `B`. -/
lemma cup_comm_sub_mem_pairCoboundaries {A B : Set Y} (p q n : ℕ) (h : p + q = n)
    (h' : q + p = n) {φ : Simplex Y p → R} (hφ : φ ∈ relCocycles R A p) {ψ : Simplex Y q → R}
    (hψ : ψ ∈ relCocycles R B q) :
    cup q p n h' ψ φ - (-1 : R) ^ (p * q) • cup p q n h φ ψ ∈ pairCoboundaries R A B n := by
  set a := pullback (reversal R p) φ - φ with ha_def
  set b := pullback (reversal R q) ψ - ψ with hb_def
  have ha : a ∈ relCoboundaries R A p := pullback_reversal_sub_mem_relCoboundaries hφ
  have hb : b ∈ relCoboundaries R B q := pullback_reversal_sub_mem_relCoboundaries hψ
  have hφa : φ + a ∈ relCocycles R A p := add_mem hφ (relCoboundaries_le A p ha)
  have hχ : coboundary R n (cup p q n h φ ψ) = 0 := by
    subst h
    have h1 : coboundary R p φ = 0 := hφ.2
    have h2 : coboundary R q ψ = 0 := hψ.2
    rw [coboundary_cup, h1, h2]
    simp
  have hc := pullback_reversal_sub_mem_pairCoboundaries (cup_mem_vanishing h hφ.1 hψ.1) hχ
  rw [pullback_reversal_cup p q n h h', show pullback (reversal R q) ψ = ψ + b by
    rw [hb_def]; abel, show pullback (reversal R p) φ = φ + a by rw [ha_def]; abel] at hc
  have hx : cup q p n h' (ψ + b) (φ + a) - cup q p n h' ψ φ ∈ pairCoboundaries R A B n := by
    rw [pairCoboundaries_comm]
    have : cup q p n h' (ψ + b) (φ + a) - cup q p n h' ψ φ =
        cup q p n h' ψ a + cup q p n h' b (φ + a) := by
      simp only [map_add, LinearMap.add_apply]; abel
    rw [this]
    exact add_mem (cup_mem_pairCoboundaries_right q p n h' hψ ha)
      (cup_mem_pairCoboundaries_left q p n h' hb hφa)
  have hε : (-1 : R) ^ (p * q) * (-1 : R) ^ (p * q) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have key : cup q p n h' ψ φ - (-1 : R) ^ (p * q) • cup p q n h φ ψ =
      (-1 : R) ^ (p * q) • ((-1 : R) ^ (p * q) • cup q p n h' (ψ + b) (φ + a) -
        cup p q n h φ ψ) - (cup q p n h' (ψ + b) (φ + a) - cup q p n h' ψ φ) := by
    rw [smul_sub, smul_smul, hε, one_smul]; abel
  rw [key]
  exact sub_mem (Submodule.smul_mem _ _ hc) hx

/-- For `A`, `B` open and relative cocycles `φ` of `A`, `ψ` of `B`, the difference
`ψ ∪ φ - (-1)^{pq} φ ∪ ψ` of relative cup cochains is a relative coboundary of `A ∪ B`. -/
lemma relCupCochain_comm_sub_mem_relCoboundaries {A B : Set Y} (hA : IsOpen A) (hB : IsOpen B)
    (p q n : ℕ) (h : p + q = n) (h' : q + p = n) {φ : Simplex Y p → R} (hφ : φ ∈ relCocycles R A p)
    {ψ : Simplex Y q → R} (hψ : ψ ∈ relCocycles R B q) :
    relCupCochain (A := B) (B := A) q p n h' ψ φ -
        (-1 : R) ^ (p * q) • relCupCochain (A := A) (B := B) p q n h φ ψ ∈
      relCoboundaries R (A ∪ B) n := by
  have := pullback_smallChainMap_mem_relCoboundaries hA hB
    (cup_comm_sub_mem_pairCoboundaries p q n h h' hφ hψ)
  rw [map_sub, map_smul] at this
  have e : relCupCochain (A := B) (B := A) q p n h' ψ φ =
      pullback (smallChainMap R {A, B} n) (cup q p n h' ψ φ) := by
    rw [Set.pair_comm]; rfl
  rw [e]
  exact this

end SingularCochain

namespace cohomologyWithSupports

open SingularCochain SingularChain

variable (R : Type u) [CommRing R]

/-- Two successive transports along equalities of supports and degrees compose to one. -/
lemma congrIndex_congrIndex (Y : TopCat.{u}) {S S' S'' : Set Y} {k k' k'' : ℤ} (h₁ : S = S')
    (h₂ : S' = S'') (k₁ : k = k') (k₂ : k' = k'')
    (x : relativeSingularCohomology R (ModuleCat.of R R) Y S k) :
    congrIndex R Y h₂ k₂ (congrIndex R Y h₁ k₁ x) =
      congrIndex R Y (h₁.trans h₂) (k₁.trans k₂) x := by
  subst h₁ h₂ k₁ k₂; rfl

/-- Transport along `S = S'` sends the class of a relative cocycle of `S` to the class of the
same cochain, as a relative cocycle of `S'`. -/
lemma congrIndex_symm_mk (Y : TopCat.{u}) {S S' : Set Y} (hS : S = S') (n : ℕ)
    (x : relCocycles R S n) (y : relCocycles R S' n) (hxy : (x : Simplex Y n → R) = y) :
    congrIndex R Y hS rfl
        ((relativeSingularCohomologyEquiv R S n).symm (Submodule.Quotient.mk x)) =
      (relativeSingularCohomologyEquiv R S' n).symm (Submodule.Quotient.mk y) := by
  subst hS
  obtain rfl := Subtype.ext hxy
  rfl

/-- Graded commutativity of the relative cup product:
`[ψ] ∪ [φ] = (-1)^{pq} [φ] ∪ [ψ]` in `H^n(Y, A ∪ B)`, `A`, `B` open. -/
lemma relCup_comm (Y : TopCat.{u}) {A B : Set Y} (hA : IsOpen A) (hB : IsOpen B) (p q n : ℕ)
    (h : p + q = n) (h' : q + p = n) (a : relCohomology R A p) (b : relCohomology R B q) :
    congrIndex R Y (union_comm B A) rfl
        ((relativeSingularCohomologyEquiv R (B ∪ A) n).symm (relCup (R := R) hB hA q p n h' b a)) =
      (-1 : R) ^ (p * q) •
        (relativeSingularCohomologyEquiv R (A ∪ B) n).symm (relCup (R := R) hA hB p q n h a b) := by
  induction a using Submodule.Quotient.induction_on with | _ x =>
  induction b using Submodule.Quotient.induction_on with | _ y =>
  rw [relCup_mk, relCup_mk, ← map_smul, ← Submodule.Quotient.mk_smul,
    congrIndex_symm_mk R Y (union_comm B A) n _
      ⟨(relCupCocycles hB hA q p n h' y x : Simplex Y n → R), by
        rw [union_comm A B]; exact (relCupCocycles hB hA q p n h' y x).2⟩ rfl]
  congr 1
  rw [Submodule.Quotient.eq]
  exact relCupCochain_comm_sub_mem_relCoboundaries hA hB p q n h h' x.2 y.2

/-- The cup product in degrees `p`, `q` is the relative cup product in `H^n(Y, Xᶜ ∪ Wᶜ)`,
`p + q = n`, transported along `Xᶜ ∪ Wᶜ = (X ∩ W)ᶜ`. -/
lemma cup_natCast_eq (Y : TopCat.{u}) {X W : Set Y} (hX : IsClosed X) (hW : IsClosed W)
    (p q n : ℕ) (h : p + q = n) (φ : cohomologyWithSupports R (ModuleCat.of R R) Y X p)
    (ψ : cohomologyWithSupports R (ModuleCat.of R R) Y W q) :
    cup R Y hX hW p q φ ψ =
      congrIndex R Y (Set.compl_inter X W).symm (by omega)
        ((relativeSingularCohomologyEquiv R (Xᶜ ∪ Wᶜ) n).symm
          (relCup (R := R) hX.isOpen_compl hW.isOpen_compl p q n h
            (relativeSingularCohomologyEquiv R Xᶜ p φ)
            (relativeSingularCohomologyEquiv R Wᶜ q ψ))) := by
  subst h
  exact cup_natCast R Y hX hW p q φ ψ

/-- The cup product is graded commutative (Fulton, §19.1): for closed subsets `X`, `W` of `Y`,
`u ∈ H^i(Y, Y - X)` and `v ∈ H^j(Y, Y - W)`, `v ∪ u = (-1)^{ij} u ∪ v` in
`H^{i+j}(Y, Y - (X ∩ W))`, the left side transported along `W ∩ X = X ∩ W`, `j + i = i + j`. -/
theorem cup_comm (Y : TopCat.{u}) {X W : Set Y} (hX : IsClosed X) (hW : IsClosed W) (i j : ℤ)
    (u : cohomologyWithSupports R (ModuleCat.of R R) Y X i)
    (v : cohomologyWithSupports R (ModuleCat.of R R) Y W j) :
    congrIndex R Y (congrArg compl (Set.inter_comm W X)) (add_comm j i) (cup R Y hW hX j i v u) =
      (((-1 : Rˣ) ^ (i * j) : Rˣ) : R) • cup R Y hX hW i j u v := by
  by_cases hij : 0 ≤ i ∧ 0 ≤ j
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hij.1
    obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hij.2
    have hε : (-1 : R) ^ (p * q) * (-1 : R) ^ (p * q) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    have hs : (((-1 : Rˣ) ^ ((p : ℤ) * (q : ℤ)) : Rˣ) : R) = (-1 : R) ^ (p * q) := by
      rw [← Nat.cast_mul, zpow_natCast, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
    have hc := relCup_comm R Y hX.isOpen_compl hW.isOpen_compl p q (p + q) rfl (add_comm q p)
      (relativeSingularCohomologyEquiv R Xᶜ p u) (relativeSingularCohomologyEquiv R Wᶜ q v)
    have hc' := congrArg (fun x ↦ (-1 : R) ^ (p * q) • x) hc
    simp only [smul_smul, hε, one_smul] at hc'
    rw [cup_natCast_eq R Y hW hX q p (p + q) (add_comm q p), cup_natCast_eq R Y hX hW p q (p + q)
      rfl, ← hc', hs, map_smul, smul_smul, hε, one_smul, congrIndex_congrIndex,
      congrIndex_congrIndex]
  · rw [cup_of_neg R Y hW hX (by omega), cup_of_neg R Y hX hW (by omega)]
    simp

end cohomologyWithSupports

end MMP
