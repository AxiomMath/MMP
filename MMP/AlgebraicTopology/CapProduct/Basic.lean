module

public import MMP.AlgebraicTopology.SingularCohomology.CupProduct
public import MMP.AlgebraicTopology.BorelMoore.ExteriorProduct
/-!
# The cap product with Borel–Moore homology (Fulton, §19.1)

For a `p`-cochain `φ` and a locally finite singular `n`-chain `c = ∑ a_σ σ` on a space `Y`, with
`n = p + q`, the cap product is the locally finite `q`-chain
`φ ∩ c = ∑ a_σ φ (σ ⌊ [q, …, n]) (σ ⌊ [0, …, q])` (the cochain on the back face, the front face
kept: Fulton's convention, for which `(φ ∪ ψ) ∩ c = φ ∩ (ψ ∩ c)` with the cup product
`(φ ∪ ψ) σ = φ (front face) ψ (back face)`). The front faces of the simplices of `c` form a locally
finite family, and a given `q`-simplex is the front face of only finitely many simplices of `c`,
so the sum makes sense. The Leibniz rule `φ ∩ ∂ c = ∂ (φ ∩ c) + (-1) ^ q δ φ ∩ c` shows that the
cap product of a cocycle and a cycle is a cycle, whose class only depends on the classes of both.

This gives the cap product `∩ : H^j(Y, Y - X) ⊗ H_k Y → H_{k-j} Y` for every subset `X ⊆ Y`
(through the forgetful map to `H^j Y`), in particular Fulton's cap product
`H^j Y ⊗ H_k Y → H_{k-j} Y`, and, for a continuous `f : Y' → Y`, the cap product
`c ∩ a = f^* c ∩ a` of `c ∈ H^j Y` and `a ∈ H_k Y'`.

## Main definitions

* `MMP.BorelMooreCap.capChain`: the cap product of a cochain and a locally finite
  chain.
* `MMP.BorelMooreCap.capHomQ`: the cap product on cocycles modulo coboundaries and
  cycles modulo boundaries.
* `MMP.borelMooreHomology.capProduct`: `∩ : H^j(Y, Y - X) ⊗ H_k Y → H_{k-j} Y`;
  the cap product into `H_{k-j} X` is `capProductSupport`.
* `MMP.borelMooreHomology.capProductPullback`: `c ∩ a = f^* c ∩ a`.

## Main results

* `MMP.BorelMooreCap.capChain_d`: the Leibniz rule.
* `MMP.BorelMooreCap.capHomQ_mk`: `[φ] ∩ [z] = [φ ∩ z]`.

## Implementation notes

Coefficients are in a commutative ring `R` (Fulton: `ℤ`, `ℚ`). The cap product is zero when
`j < 0`, `k < 0` or `j > k`, where one of the groups vanishes.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [A. Hatcher, *Algebraic Topology*][hatcher2002], §3.3.
* [A. Dold, *Lectures on Algebraic Topology*][dold1995], VII.12.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Simplicial AlgebraicTopology MMP.SingularCross
  MMP.LocallyFiniteChain MMP.BorelMooreCross
  MMP.SingularCochain MMP.SingularChain

universe u

namespace MMP

namespace BorelMooreCap

variable {R : Type u} [CommRing R] {Y : TopCat.{u}}

/-- The simplicial operator on singular simplices induced by a map of vertices. -/
def opS {a b : ℕ} (f : Fin (a + 1) → Fin (b + 1)) (σ : Simp Y b) : Simp Y a :=
  (simplexEquiv Y a).symm ((simplexEquiv Y b σ).comp (smap f))

/-- The continuous map of `opS f σ` is that of `σ` composed with the affine map of `f`. -/
lemma simplexEquiv_opS {a b : ℕ} (f : Fin (a + 1) → Fin (b + 1)) (σ : Simp Y b) :
    simplexEquiv Y a (opS f σ) = (simplexEquiv Y b σ).comp (smap f) :=
  Equiv.apply_symm_apply _ _

/-- The continuous map of `opS f σ` on the standard simplex is that of `σ` composed with the
map of standard simplices induced by `f`. -/
lemma toC_opS {a b : ℕ} (f : Fin (a + 1) → Fin (b + 1)) (σ : Simp Y b) :
    toC (opS f σ) = (toC σ).comp ⟨Convexity.StdSimplex.map f, Convexity.StdSimplex.continuous_map ℝ _⟩ := by
  ext t
  have h := DFunLike.congr_fun (simplexEquiv_opS f σ) ((SingularChain.stdSimplexHomeo _).symm t)
  change toC (opS f σ) (SingularChain.stdSimplexHomeo _ ((SingularChain.stdSimplexHomeo _).symm t)) =
    toC σ (SingularChain.stdSimplexHomeo _ (stdSimplex.map f ((SingularChain.stdSimplexHomeo _).symm t))) at h
  rw [SingularChain.stdSimplexHomeo_map, Homeomorph.apply_symm_apply] at h
  exact h

/-- The image of `opS f σ` is contained in the image of `σ`. -/
lemma image_opS_subset {a b : ℕ} (f : Fin (a + 1) → Fin (b + 1)) (σ : Simp Y b) :
    singularSimplexImage Y (opS f σ) ⊆ singularSimplexImage Y σ := by
  rw [← range_simplexEquiv, ← range_simplexEquiv]
  rw [simplexEquiv_opS]
  rintro _ ⟨t, rfl⟩
  exact ⟨_, rfl⟩

/-- The simplicial operators compose contravariantly: `opS g (opS f σ) = opS (f ∘ g) σ`. -/
lemma opS_opS {a b c : ℕ} (f : Fin (b + 1) → Fin (c + 1)) (g : Fin (a + 1) → Fin (b + 1))
    (σ : Simp Y c) : opS g (opS f σ) = opS (f ∘ g) σ := by
  simp only [opS, Equiv.apply_symm_apply, comp_smap_comp]

/-- The `i`-th face map of the singular simplicial set is the operator of `skip n i`. -/
lemma δ_eq_opS (n : ℕ) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj Y).δ i = opS (Y := Y) (skip n i) := by
  funext σ
  have := simplexEquiv_symm_δ Y n (simplexEquiv Y (n + 1) σ) i
  rw [Equiv.symm_apply_apply] at this
  rw [this, face_eq_smap]
  rfl

variable (R) in
/-- Push-forward of locally finite chains along the simplicial operator of a map of vertices. -/
def pf {a b : ℕ} (f : Fin (a + 1) → Fin (b + 1)) : (BM R Y).X b →ₗ[R] (BM R Y).X a :=
  pushforward (R := R) (M := R) (opS f) (image_opS_subset f) compact_nonempty

/-- The coefficients of `pf R f c` are the push-forward along `opS f` of those of `c`. -/
lemma coeff_pf {a b : ℕ} (f : Fin (a + 1) → Fin (b + 1)) (c : (BM R Y).X b) :
    coeff R (pf R f c) = pushforwardFun (opS f) (coeff R c) :=
  rfl

/-- Push-forwards compose: `pf R g ∘ pf R f = pf R (f ∘ g)`. -/
lemma pf_pf {a b c : ℕ} (f : Fin (b + 1) → Fin (c + 1)) (g : Fin (a + 1) → Fin (b + 1))
    (x : (BM R Y).X c) : pf R g (pf R f x) = pf R (f ∘ g) x := by
  apply coeff_injective R
  have h := congrArg (fun y ↦ coeff R y) (LinearMap.congr_fun (pushforward_comp (R := R) (M := R)
    (opS (Y := Y) f) (opS g) (image_opS_subset f) (image_opS_subset g) compact_nonempty
    compact_nonempty) x)
  refine (show coeff R (pf R g (pf R f x)) = _ from h.symm).trans ?_
  change pushforwardFun (opS g ∘ opS f) (coeff R x) = pushforwardFun (opS (f ∘ g)) (coeff R x)
  congr 1
  funext σ
  exact opS_opS f g σ

/-- The boundary of a locally finite `(n + 1)`-chain `c` is `∑ i, (-1) ^ i • pf R (skip n i) c`. -/
lemma d_eq_sum_pf (n : ℕ) (c : (BM R Y).X (n + 1)) :
    ((BM R Y).d (n + 1) n).hom c =
      ∑ i ∈ Finset.range (n + 2), (-1 : ℤ) ^ i • pf R (skip n i) c := by
  apply coeff_injective R
  rw [coeff_d, coeff_sum, ← Fin.sum_univ_eq_sum_range (fun i ↦ coeff R ((-1 : ℤ) ^ i •
    pf R (skip n i) c))]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [coeff_zsmul, coeff_pf, δ_eq_opS]

variable (R) in
/-- Multiplication of a locally finite chain by a function on simplices. -/
def W {n : ℕ} (g : Simp Y n → R) : (BM R Y).X n →ₗ[R] (BM R Y).X n where
  toFun c := ofCoeff R (fun σ ↦ g σ * coeff R c σ)
    ((coeff_mem R c).mono fun σ hσ ↦ by
      simp only [Function.mem_support, ne_eq] at hσ ⊢
      exact fun h ↦ hσ (by rw [h, mul_zero]))
  map_add' _ _ := coeff_injective R (funext fun _ ↦ mul_add _ _ _)
  map_smul' _ _ := coeff_injective R (funext fun _ ↦ mul_left_comm _ _ _)

/-- The coefficient of `W R g c` at `σ` is `g σ * coeff R c σ`. -/
lemma coeff_W {n : ℕ} (g : Simp Y n → R) (c : (BM R Y).X n) :
    coeff R (W R g c) = fun σ ↦ g σ * coeff R c σ :=
  rfl

/-- `W R` is additive in the function on simplices. -/
lemma W_add {n : ℕ} (g g' : Simp Y n → R) : W R (g + g') = W R g + W R g' := by
  ext c
  apply coeff_injective R
  funext σ
  simp [coeff_W, add_mul]

/-- `W R` commutes with scalar multiplication of the function on simplices. -/
lemma W_smul {n : ℕ} (r : R) (g : Simp Y n → R) : W R (r • g) = r • W R g := by
  ext c
  apply coeff_injective R
  funext σ
  simp [coeff_W, mul_assoc]

/-- `W R` sends a finite sum of functions on simplices to the sum of the operators. -/
lemma W_sum {n : ℕ} {ι : Type*} (s : Finset ι) (g : ι → Simp Y n → R) :
    W R (∑ i ∈ s, g i) = ∑ i ∈ s, W R (g i) :=
  map_sum (AddMonoidHom.mk' (W R) W_add) g s

/-- Projection formula: multiplying a push-forward by `g` is pushing forward the chain multiplied
by `g ∘ opS f`. -/
lemma W_pf {a b : ℕ} (f : Fin (a + 1) → Fin (b + 1)) (g : Simp Y a → R) (c : (BM R Y).X b) :
    W R g (pf R f c) = pf R f (W R (g ∘ opS f) c) := by
  apply coeff_injective R
  funext τ
  rw [coeff_W, coeff_pf, coeff_pf, coeff_W]
  have hfin := finite_fiber (coeff_mem R c) (opS f) (image_opS_subset f) τ
    (compact_nonempty τ).1 (compact_nonempty τ).2
  let F := hfin.toFinset
  have hF : ∀ σ, coeff R c σ ≠ 0 → opS f σ = τ → σ ∈ F := fun σ h1 h2 ↦ by
    simpa [F] using ⟨h1, h2⟩
  have hF' : ∀ σ, (fun σ ↦ (g ∘ opS f) σ * coeff R c σ) σ ≠ 0 → opS f σ = τ → σ ∈ F :=
    fun σ h1 h2 ↦ hF σ (fun h ↦ h1 (by simp [h])) h2
  simp only
  rw [pushforwardFun_apply_eq_sum _ _ τ F hF, pushforwardFun_apply_eq_sum _ _ τ F hF',
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  split_ifs with h
  · simp [h]
  · simp

/-- The weight `σ ↦ φ (σ ∘ f)` of a cochain `φ` along a map of vertices `f`. -/
def wt {a b : ℕ} (φ : Simplex Y a → R) (f : Fin (a + 1) → Fin (b + 1)) : Simp Y b → R :=
  fun σ ↦ φ ((simplexEquiv Y b σ).comp (smap f))

omit [CommRing R] in
/-- The weight along `f` precomposed with `opS g` is the weight along `g ∘ f`. -/
lemma wt_comp_opS {a b c : ℕ} (φ : Simplex Y a → R) (f : Fin (a + 1) → Fin (b + 1))
    (g : Fin (b + 1) → Fin (c + 1)) : wt φ f ∘ opS g = wt φ (g ∘ f) := by
  funext σ
  simp only [Function.comp_apply, wt, simplexEquiv_opS, comp_smap_comp]

/-- The weight is additive in the cochain. -/
lemma wt_add {a b : ℕ} (φ ψ : Simplex Y a → R) (f : Fin (a + 1) → Fin (b + 1)) :
    wt (φ + ψ) f = wt φ f + wt ψ f :=
  rfl

/-- The weight commutes with scalar multiplication of the cochain. -/
lemma wt_smul {a b : ℕ} (r : R) (φ : Simplex Y a → R) (f : Fin (a + 1) → Fin (b + 1)) :
    wt (r • φ) f = r • wt φ f :=
  rfl

/-- The weight of `δ φ` along `f` is `∑ i, (-1) ^ i • wt φ (f ∘ skip a i)`. -/
lemma wt_coboundary {a b : ℕ} (φ : Simplex Y a → R) (f : Fin (a + 2) → Fin (b + 1)) :
    wt (coboundary R a φ) f = ∑ i ∈ Finset.range (a + 2), (-1 : R) ^ i • wt φ (f ∘ skip a i) := by
  funext σ
  simp only [wt, coboundary_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Fin.sum_univ_eq_sum_range (fun i ↦ (-1 : R) ^ i * φ ((simplexEquiv Y b σ).comp
    (smap (f ∘ skip a i))))]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [face_eq_smap, comp_smap_comp]

section Cap

variable (R) in
/-- The cap product `φ ∩ c = ∑ a_σ φ (σ ⌊ [q, …, n]) (σ ⌊ [0, …, q])` of a `p`-cochain `φ` and a
locally finite `n`-chain `c = ∑ a_σ σ`, a locally finite `q`-chain, `p + q = n`: the cochain is
evaluated on the back `p`-face and the front `q`-face is kept (Fulton's convention, under which
`(φ ∪ ψ) ∩ c = φ ∩ (ψ ∩ c)`). -/
def capChain (p q n : ℕ) (h : p + q = n) :
    (Simplex Y p → R) →ₗ[R] (BM R Y).X n →ₗ[R] (BM R Y).X q where
  toFun φ := (pf R (front q n (by omega))).comp (W R (wt φ (back p n q (by omega))))
  map_add' φ ψ := by
    rw [wt_add, W_add, LinearMap.comp_add]
  map_smul' r φ := by
    rw [wt_smul, W_smul, LinearMap.comp_smul]
    rfl

/-- `φ ∩ c` is the push-forward to front faces of `c` weighted by `φ` on back faces. -/
lemma capChain_apply (p q n : ℕ) (h : p + q = n) (φ : Simplex Y p → R) (c : (BM R Y).X n) :
    capChain R p q n h φ c = pf R (front q n (by omega)) (W R (wt φ (back p n q (by omega))) c) :=
  rfl

private lemma neg_one_pow_smul_eq {M : Type*} [AddCommGroup M] [Module R M] (i : ℕ) (x : M) :
    (-1 : R) ^ i • x = (-1 : ℤ) ^ i • x := by
  rw [← Int.cast_smul_eq_zsmul R]
  push_cast
  rfl

/-- Skipping the last vertex of a front face gives the next smaller front face. -/
lemma front_comp_skip_self (q m : ℕ) (h : q + 1 ≤ m) :
    front (q + 1) m h ∘ skip q (q + 1) = front q m (by omega) := by
  funext j
  ext
  grind [skip_val, front_val]

/-- Skipping the first vertex of a back face gives the next smaller back face. -/
lemma back_comp_skip_zero (p m q : ℕ) (h : p + 1 + q ≤ m) :
    back (p + 1) m q h ∘ skip p 0 = back p m (q + 1) (by omega) := by
  funext j
  ext
  grind [skip_val, back_val]

/-- The Leibniz rule `φ ∩ ∂ c = ∂ (φ ∩ c) + (-1) ^ q δ φ ∩ c`, `q` the degree of `φ ∩ ∂ c`. -/
theorem capChain_d (p q n : ℕ) (h : p + q = n) (φ : Simplex Y p → R) (c : (BM R Y).X (n + 1)) :
    capChain R p q n h φ (((BM R Y).d (n + 1) n).hom c) =
      ((BM R Y).d (q + 1) q).hom (capChain R p (q + 1) (n + 1) (by omega) φ c) +
        (-1 : ℤ) ^ q • capChain R (p + 1) q (n + 1) (by omega) (coboundary R p φ) c := by
  simp only [capChain_apply, d_eq_sum_pf, map_sum, map_zsmul, W_pf, pf_pf, wt_comp_opS,
    wt_coboundary, W_sum, W_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    map_smul]
  simp only [neg_one_pow_smul_eq]
  rw [← Finset.sum_range_add_sum_Ico _ (show q + 1 ≤ n + 2 by omega),
    Finset.sum_Ico_eq_sum_range, show n + 2 - (q + 1) = p + 1 by omega,
    Finset.sum_range_succ _ (q + 1), Finset.sum_range_succ' _ (p + 1)]
  have hA : ∀ i ∈ Finset.range (q + 1),
      (-1 : ℤ) ^ i • pf R (skip n i ∘ front q n (by omega))
          (W R (wt φ (skip n i ∘ back p n q (by omega))) c) =
        (-1 : ℤ) ^ i • pf R (front (q + 1) (n + 1) (by omega) ∘ skip q i)
          (W R (wt φ (back p (n + 1) (q + 1) (by omega))) c) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have e1 : skip n i ∘ front q n (by omega) = front (q + 1) (n + 1) (by omega) ∘ skip q i := by
      funext j
      ext
      grind [skip_val, front_val]
    have e2 : skip n i ∘ back p n q (by omega) = back p (n + 1) (q + 1) (by omega) := by
      funext j
      ext
      grind [skip_val, back_val]
    rw [e1, e2]
  have hB : ∀ k ∈ Finset.range (p + 1),
      (-1 : ℤ) ^ (q + 1 + k) • pf R (skip n (q + 1 + k) ∘ front q n (by omega))
          (W R (wt φ (skip n (q + 1 + k) ∘ back p n q (by omega))) c) =
        (-1 : ℤ) ^ q • ((-1 : ℤ) ^ (k + 1) • pf R (front q (n + 1) (by omega))
          (W R (wt φ (back (p + 1) (n + 1) q (by omega) ∘ skip p (k + 1))) c)) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have e1 : skip n (q + 1 + k) ∘ front q n (by omega) = front q (n + 1) (by omega) := by
      funext j
      ext
      grind [skip_val, front_val]
    have e2 : skip n (q + 1 + k) ∘ back p n q (by omega) =
        back (p + 1) (n + 1) q (by omega) ∘ skip p (k + 1) := by
      funext j
      ext
      grind [skip_val, back_val]
    rw [e1, e2, smul_smul, ← pow_add, show q + (k + 1) = q + 1 + k by omega]
  rw [Finset.sum_congr rfl hA, Finset.sum_congr rfl hB, front_comp_skip_self,
    back_comp_skip_zero, ← Finset.smul_sum,
    smul_add, pow_zero, one_smul, pow_succ (-1 : ℤ) q, mul_neg_one, neg_smul]
  abel

end Cap

section Homology

variable (A : Set Y)

/-- The cap product of a relative cocycle and a locally finite cycle is a cycle. -/
lemma capChain_mem_cyc (p q n : ℕ) (h : p + q = n) (φ : relCocycles R A p)
    (z : Cyc (R := R) Y n) : capChain R p q n h φ.1 z.1 ∈ Cyc (R := R) Y q := by
  rw [mem_cyc_iff]
  rcases q with _ | q
  · rw [show (0 : ℕ) - 1 = 0 from rfl, (BM R _).shape 0 0 (by simp)]
    rfl
  · obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hz : ((BM R Y).d (n + 1) n).hom z.1 = 0 := (mem_cyc_iff z.1).1 z.2
    have hφ : coboundary R p φ.1 = 0 := φ.2.2
    have key := capChain_d p q n (by omega) φ.1 z.1
    rw [hz, map_zero, hφ, map_zero, LinearMap.zero_apply, smul_zero, add_zero] at key
    exact key.symm

/-- For a relative cocycle `φ`, `∂ (φ ∩ u) = φ ∩ ∂ u`. -/
lemma d_capChain_relCocycle (p q n : ℕ) (h : p + q = n) (φ : relCocycles R A p)
    (u : (BM R Y).X (n + 1)) :
    ((BM R Y).d (q + 1) q).hom (capChain R p (q + 1) (n + 1) (by omega) φ.1 u) =
      capChain R p q n h φ.1 (((BM R Y).d (n + 1) n).hom u) := by
  have hφ : coboundary R p φ.1 = 0 := φ.2.2
  rw [capChain_d p q n h φ.1 u, hφ, map_zero, LinearMap.zero_apply, smul_zero, add_zero]

/-- For a cycle `z`, `δ ψ ∩ z` is the boundary of `-((-1) ^ q • ψ ∩ z)`. -/
lemma d_neg_zsmul_capChain_cyc (p q n : ℕ) (h : p + q = n) (ψ : Simplex Y p → R)
    (z : Cyc (R := R) Y (n + 1)) :
    ((BM R Y).d (q + 1) q).hom (-((-1 : ℤ) ^ q • capChain R p (q + 1) (n + 1) (by omega) ψ z.1)) =
      capChain R (p + 1) q (n + 1) (by omega) (coboundary R p ψ) z.1 := by
  have hz : ((BM R Y).d (n + 1) n).hom z.1 = 0 := (mem_cyc_iff z.1).1 z.2
  have key := capChain_d p q n h ψ z.1
  rw [hz, map_zero] at key
  rw [map_neg, map_zsmul, eq_neg_of_add_eq_zero_left key.symm, smul_neg, neg_neg, smul_smul,
    ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]

variable (R) in
/-- The cap product of a relative cocycle and a cycle. -/
def capCyc (p q n : ℕ) (h : p + q = n) :
    relCocycles R A p →ₗ[R] Cyc (R := R) Y n →ₗ[R] Cyc (R := R) Y q :=
  LinearMap.mk₂ R (fun φ z ↦ ⟨capChain R p q n h φ.1 z.1, capChain_mem_cyc A p q n h φ z⟩)
    (fun _ _ _ ↦ Subtype.ext (by simp))
    (fun _ _ _ ↦ Subtype.ext (by simp))
    (fun _ _ _ ↦ Subtype.ext (by simp))
    (fun _ _ _ ↦ Subtype.ext (by simp))

/-- The cap product of a relative cocycle and a cycle, followed by the class map. -/
def capCycQ (p q n : ℕ) (h : p + q = n) :
    relCocycles R A p →ₗ[R] Cyc (R := R) Y n →ₗ[R] HomQ (R := R) Y q :=
  (capCyc R A p q n h).compr₂ (LinearMap.range ((BM R Y).sc q).moduleCatToCycles).mkQ

/-- The cap product of a relative coboundary and a cycle is zero in homology. -/
lemma capCycQ_coboundary (p q n : ℕ) (h : p + q = n) :
    (relCoboundaries R A p).comap (relCocycles R A p).subtype ≤
      LinearMap.ker (capCycQ (R := R) A p q n h) := by
  intro φ hφ
  change capCycQ A p q n h φ = 0
  ext z
  rcases p with _ | p
  · rw [show φ = 0 from Subtype.ext hφ, map_zero, LinearMap.zero_apply]
  · obtain ⟨ψ, -, hψ⟩ := hφ
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    refine (Submodule.Quotient.mk_eq_zero _).2
      (mem_bdry_of (capCyc R A (p + 1) q (n + 1) h φ z)
        (-((-1 : ℤ) ^ q • capChain R p (q + 1) (n + 1) (by omega) ψ z.1)) ?_)
    rw [d_neg_zsmul_capChain_cyc p q n (by omega) ψ z]
    change _ = capChain R (p + 1) q (n + 1) h φ.1 z.1
    rw [hψ]
    rfl

/-- The cap product of a relative cohomology class and a cycle, as a homology class. -/
def capHomQ₁ (p q n : ℕ) (h : p + q = n) :
    relCohomology R A p →ₗ[R] Cyc (R := R) Y n →ₗ[R] HomQ (R := R) Y q :=
  ((relCoboundaries R A p).comap (relCocycles R A p).subtype).liftQ (capCycQ A p q n h)
    (capCycQ_coboundary A p q n h)

/-- The cap product of a relative cohomology class and a boundary is zero. -/
lemma capHomQ₁_bdry (p q n : ℕ) (h : p + q = n) :
    LinearMap.range ((BM R Y).sc n).moduleCatToCycles ≤
      LinearMap.ker (capHomQ₁ (R := R) A p q n h).flip := by
  intro z hz
  obtain ⟨u, hu⟩ := exists_of_mem_bdry hz
  change (capHomQ₁ A p q n h).flip z = 0
  refine Submodule.linearMap_qext _ (LinearMap.ext fun φ ↦ ?_)
  refine (Submodule.Quotient.mk_eq_zero _).2
    (mem_bdry_of (capCyc R A p q n h φ z)
      (capChain R p (q + 1) (n + 1) (by omega) φ.1 u) ?_)
  rw [d_capChain_relCocycle A p q n h φ u, hu]
  rfl

variable (R) in
/-- The cap product on relative cohomology and Borel–Moore homology, cocycles modulo
coboundaries and cycles modulo boundaries: `[φ] ∩ [z] = [φ ∩ z]`. -/
def capHomQ (p q n : ℕ) (h : p + q = n) :
    relCohomology R A p →ₗ[R] HomQ (R := R) Y n →ₗ[R] HomQ (R := R) Y q :=
  ((LinearMap.range ((BM R Y).sc n).moduleCatToCycles).liftQ (capHomQ₁ A p q n h).flip
    (capHomQ₁_bdry A p q n h)).flip

/-- On classes, `[φ] ∩ [z] = [φ ∩ z]`. -/
lemma capHomQ_mk (p q n : ℕ) (h : p + q = n) (φ : relCocycles R A p) (z : Cyc (R := R) Y n) :
    capHomQ R A p q n h (Submodule.Quotient.mk φ) (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ⟨capChain R p q n h φ.1 z.1, capChain_mem_cyc A p q n h φ z⟩ :=
  rfl

end Homology

end BorelMooreCap

namespace borelMooreHomology

open BorelMooreCap

variable (R : Type u) [CommRing R]

/-- The cap product `∩ : H^j(Y, Y - X) ⊗ H_k Y → H_{k-j} Y` for a subset `X` of a space `Y`, with
coefficients in a commutative ring `R`: on classes of a cocycle `φ` (vanishing on the simplices
of `Y - X`) and a locally finite cycle `z` it is the class of
`φ ∩ z = ∑ a_σ φ (σ ⌊ [k - j, …, k]) (σ ⌊ [0, …, k - j])`. For `X = Y` it is the cap product
`H^j Y ⊗ H_k Y → H_{k-j} Y`. It is zero when `j < 0` or `j > k`, where a group vanishes. -/
def capProduct (Y : TopCat.{u}) (X : Set Y) (j k : ℤ) :
    cohomologyWithSupports R (ModuleCat.of R R) Y X j →ₗ[R]
      borelMooreHomology R (ModuleCat.of R R) Y k →ₗ[R]
        borelMooreHomology R (ModuleCat.of R R) Y (k - j) :=
  if h : 0 ≤ j ∧ j ≤ k then
    ((capHomQ R Xᶜ j.toNat (k.toNat - j.toNat) k.toNat (by omega)).compl₁₂
        ((cohomologyWithSupports.congrIndex R Y rfl (Int.toNat_of_nonneg h.1).symm).trans
          (relativeSingularCohomologyEquiv R Xᶜ j.toNat)).toLinearMap
        ((congrDegree R Y (Int.toNat_of_nonneg (h.1.trans h.2)).symm).trans
          (homologyEquiv R Y k.toNat)).toLinearMap).compr₂
      ((congrDegree R Y (by omega)).trans
        (homologyEquiv R Y (k.toNat - j.toNat))).symm.toLinearMap
  else 0

/-- The cap product vanishes when `j < 0` or `k < j`. -/
lemma capProduct_of_not_le (Y : TopCat.{u}) (X : Set Y) {j k : ℤ} (h : ¬ (0 ≤ j ∧ j ≤ k)) :
    capProduct R Y X j k = 0 := by
  rw [capProduct, dif_neg h]

/-- Fulton's notation `c ∩ a := f^* c ∩ a ∈ H_{k-j} Y'` for a continuous `f : Y' → Y`,
`c ∈ H^j(Y, Y - X)` and `a ∈ H_k Y'` (Example 19.1.10). -/
def capProductPullback {Y' Y : TopCat.{u}} (f : Y' ⟶ Y) (X : Set Y) (j k : ℤ) :
    cohomologyWithSupports R (ModuleCat.of R R) Y X j →ₗ[R]
      borelMooreHomology R (ModuleCat.of R R) Y' k →ₗ[R]
        borelMooreHomology R (ModuleCat.of R R) Y' (k - j) :=
  (capProduct R Y' (f ⁻¹' X) j k).comp (cohomologyWithSupports.pullback R _ f X j).hom

/-- `c ∩ a` is the cap product of `f^* c ∈ H^j(Y', Y' - f⁻¹ X)` and `a`. -/
lemma capProductPullback_apply {Y' Y : TopCat.{u}} (f : Y' ⟶ Y) (X : Set Y) (j k : ℤ)
    (c : cohomologyWithSupports R (ModuleCat.of R R) Y X j)
    (a : borelMooreHomology R (ModuleCat.of R R) Y' k) :
    capProductPullback R f X j k c a =
      capProduct R Y' (f ⁻¹' X) j k ((cohomologyWithSupports.pullback R _ f X j).hom c) a :=
  rfl

end borelMooreHomology

end MMP
