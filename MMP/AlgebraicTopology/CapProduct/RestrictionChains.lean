module

public import MMP.AlgebraicTopology.CapProduct.SupportLemmas
public import MMP.AlgebraicTopology.BorelMoore.FiniteChains
public import MMP.AlgebraicTopology.BorelMoore.RestrictionChains

/-!
# The cap product of a cochain with a finite chain

The first step towards the compatibility of the cap product with restriction to an open subset
(Fulton §19.1; [BT] 2.2). The restriction of locally finite chains to an open `U` is built from
the subdivision operators `ρ_N = 1 - ∂ D_N - D_N ∂` towards `U` on *finite* chains
(`MMP.SingularChain.towardsChainMap`), so the cap product is needed on finite
chains too: `φ ∩ σ = φ (σ ⌊ [q, …, n]) (σ ⌊ [0, …, q])`, extended linearly.

## Main definitions

* `MMP.BorelMooreCap.capFin`: the cap product `φ ∩ c` of a `p`-cochain and a finite
  `n`-chain, a finite `q`-chain, `p + q = n`.

## Main results

* `MMP.BorelMooreCap.ofFinsupp_capFin`: it is the cap product of locally finite
  chains, `capChain`.
* `MMP.BorelMooreCap.capFin_bd`: the Leibniz rule
  `φ ∩ ∂ c = ∂ (φ ∩ c) + (-1) ^ q δ φ ∩ c`.
* `MMP.BorelMooreCap.capFin_mem_inside`: `φ ∩ c` lies where `c` does.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [A. Hatcher, *Algebraic Topology*][hatcher2002], §3.3.
-/

@[expose] public noncomputable section

open CategoryTheory Set Opposite Simplicial

universe u

namespace MMP

namespace BorelMooreCap

open SingularCochain SingularChain LocallyFiniteChain borelMooreHomology SingularCross
  BorelMooreCross

variable {R : Type u} [CommRing R] {Y : TopCat.{u}}

variable (R) in
/-- The cap product `φ ∩ c = ∑ a_σ φ (σ ⌊ [q, …, n]) (σ ⌊ [0, …, q])` of a `p`-cochain `φ` and a
finite `n`-chain `c = ∑ a_σ σ`, a finite `q`-chain, `p + q = n`. -/
def capFin (p q n : ℕ) (h : p + q = n) (φ : Simplex Y p → R) : Chain R Y n →ₗ[R] Chain R Y q :=
  Finsupp.linearCombination R fun σ : Simplex Y n ↦
    φ (σ.comp (smap (back p n q (by omega)))) • Finsupp.single (σ.comp (smap (front q n
      (by omega)))) (1 : R)

/-- The cap product of `φ` with `a σ` is `a φ (σ ⌊ [q, …, n])` times the simplex
`σ ⌊ [0, …, q]`. -/
lemma capFin_single (p q n : ℕ) (h : p + q = n) (φ : Simplex Y p → R) (σ : Simplex Y n)
    (a : R) :
    capFin R p q n h φ (Finsupp.single σ a) =
      Finsupp.single (σ.comp (smap (front q n (by omega))))
        (a * φ (σ.comp (smap (back p n q (by omega))))) := by
  rw [capFin, Finsupp.linearCombination_single, smul_smul, Finsupp.smul_single, smul_eq_mul,
    mul_one]

open Classical in
/-- The coefficient of a `q`-simplex `τ` in `φ ∩ c` is the sum of `a_σ φ (σ ⌊ [q, …, n])` over the
simplices `σ` of `c` with front face `σ ⌊ [0, …, q] = τ`. -/
lemma capFin_apply (p q n : ℕ) (h : p + q = n) (φ : Simplex Y p → R) (c : Chain R Y n)
    (τ : Simplex Y q) :
    capFin R p q n h φ c τ = c.sum fun σ a ↦
      if σ.comp (smap (front q n (by omega))) = τ then
        a * φ (σ.comp (smap (back p n q (by omega)))) else 0 := by
  conv_lhs => rw [← Finsupp.sum_single c, map_finsuppSum]
  rw [Finsupp.sum_apply]
  refine Finsupp.sum_congr fun σ _ ↦ ?_
  rw [capFin_single, Finsupp.single_apply]

/-- The cap product with the zero cochain is zero. -/
@[simp] lemma capFin_zero_cochain (p q n : ℕ) (h : p + q = n) :
    capFin R p q n h (0 : Simplex Y p → R) = 0 := by
  ext c τ
  simp [capFin, Finsupp.linearCombination_apply]

/-- The image of a simplex precomposed with a simplicial map is contained in the image of the
simplex. -/
lemma range_comp_smap_subset {a b : ℕ} (σ : Simplex Y b) (f : Fin (a + 1) → Fin (b + 1)) :
    range (σ.comp (smap f)) ⊆ range σ := by
  rintro _ ⟨x, rfl⟩
  exact ⟨_, rfl⟩

/-- `ofFinsupp` is additive. -/
lemma ofFinsupp_add {n : ℕ} (f g : Chain R Y n) :
    ofFinsupp (f + g) = ofFinsupp f + ofFinsupp g := rfl

/-- `ofFinsupp` commutes with multiplication by an integer. -/
lemma ofFinsupp_zsmul {n : ℕ} (k : ℤ) (f : Chain R Y n) :
    ofFinsupp (k • f) = k • ofFinsupp f := rfl

/-- A finite chain is determined by the locally finite chain it defines. -/
lemma ofFinsupp_injective {n : ℕ} : Function.Injective (ofFinsupp (R := R) (X := Y) (n := n)) := by
  intro f g hfg
  ext σ
  simpa [ofFinsupp_apply] using congrArg (fun c ↦ c.1 ((SingularCochain.simplexEquiv Y _).symm σ)) hfg

/-- The cap product of finite chains is the cap product of locally finite chains. -/
theorem ofFinsupp_capFin (p q n : ℕ) (h : p + q = n) (φ : Simplex Y p → R) (c : Chain R Y n) :
    ofFinsupp (capFin R p q n h φ c) = capChain R p q n h φ (ofFinsupp c) := by
  classical
  apply coeff_injective R
  funext τ
  rw [capChain_apply, coeff_pf, coeff_W]
  change capFin R p q n h φ c (SingularCochain.simplexEquiv Y _ τ) = _
  rw [capFin_apply]
  let e := SingularCochain.simplexEquiv Y n
  rw [pushforwardFun_apply_eq_sum _ _ τ (c.support.map e.symm.toEmbedding) (fun σ hσ _ ↦ by
    rw [Finset.mem_map_equiv, Equiv.symm_symm, Finsupp.mem_support_iff]
    intro h0
    exact hσ (by rw [show coeff R (ofFinsupp c) σ = c (e σ) from rfl, h0, mul_zero]))]
  rw [Finset.sum_map, Finsupp.sum]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  simp only [Equiv.coe_toEmbedding]
  have e1 : (opS (front q n (by omega)) (e.symm σ) = τ) ↔
      σ.comp (smap (front q n (by omega))) = SingularCochain.simplexEquiv Y _ τ := by
    rw [← (SingularCochain.simplexEquiv Y q).apply_eq_iff_eq]
    change simplexEquiv Y q (opS _ (e.symm σ)) = _ ↔ _
    rw [simplexEquiv_opS]
    exact Iff.of_eq (by rw [show simplexEquiv Y n (e.symm σ) = σ from e.apply_symm_apply σ])
  by_cases hb : σ.comp (smap (front q n (by omega))) = SingularCochain.simplexEquiv Y _ τ
  · rw [ite_eq_left hb, ite_eq_left (e1.2 hb), show coeff R (ofFinsupp c) (e.symm σ) = c σ from
      congrArg c (e.apply_symm_apply σ), mul_comm (c σ)]
    change _ = φ ((simplexEquiv Y n (e.symm σ)).comp _) * _
    rw [show simplexEquiv Y n (e.symm σ) = σ from e.apply_symm_apply σ]
  · rw [ite_eq_right hb, ite_eq_right (fun h' ↦ hb (e1.1 h'))]

/-- **The Leibniz rule** for finite chains: `φ ∩ ∂ c = ∂ (φ ∩ c) + (-1) ^ q δ φ ∩ c`. -/
theorem capFin_bd (p q n : ℕ) (h : p + q = n) (φ : Simplex Y p → R) (c : Chain R Y (n + 1)) :
    capFin R p q n h φ (bd R n c) =
      bd R q (capFin R p (q + 1) (n + 1) (by omega) φ c) +
        (-1 : ℤ) ^ q • capFin R (p + 1) q (n + 1) (by omega) (coboundary R p φ) c := by
  apply ofFinsupp_injective
  rw [ofFinsupp_add, ofFinsupp_zsmul, ← d_ofFinsupp, ofFinsupp_capFin, ofFinsupp_capFin,
    ofFinsupp_capFin, ← d_ofFinsupp, capChain_d]

/-- For a cocycle `φ`, `φ ∩ ∂ c = ∂ (φ ∩ c)`. -/
lemma capFin_bd_of_cocycle (p q n : ℕ) (h : p + q = n) {φ : Simplex Y p → R}
    (hφ : coboundary R p φ = 0) (c : Chain R Y (n + 1)) :
    capFin R p q n h φ (bd R n c) =
      bd R q (capFin R p (q + 1) (n + 1) (by omega) φ c) := by
  rw [capFin_bd, hφ, capFin_zero_cochain, LinearMap.zero_apply, smul_zero, add_zero]

/-- The cap product `φ ∩ c` lies wherever `c` does. -/
lemma capFin_mem_inside (p q n : ℕ) (h : p + q = n) (φ : Simplex Y p → R) {A : Set Y}
    {c : Chain R Y n} (hc : c ∈ inside R n A) : capFin R p q n h φ c ∈ inside R q A := by
  classical
  rw [← Finsupp.sum_single c, map_finsuppSum]
  refine Submodule.sum_mem _ fun σ hσ ↦ ?_
  dsimp only
  rw [capFin_single]
  exact Finsupp.single_mem_supported R _
    ((range_comp_smap_subset _ _).trans (hc (by simpa using Finsupp.mem_support_iff.1 hσ)))

/-- A cochain vanishing on the simplices of `B` caps to zero with a simplex lying in `B`. -/
lemma capFin_single_eq_zero_of_vanishing (p q n : ℕ) (h : p + q = n) {B : Set Y}
    {φ : Simplex Y p → R} (hφ : φ ∈ vanishing R p B) {σ : Simplex Y n} (hσ : range σ ⊆ B)
    (a : R) : capFin R p q n h φ (Finsupp.single σ a) = 0 := by
  rw [capFin_single, hφ _ ((range_comp_smap_subset _ _).trans hσ), mul_zero,
    Finsupp.single_zero]

end BorelMooreCap

end MMP
