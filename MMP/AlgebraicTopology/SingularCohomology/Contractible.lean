module

public import MMP.AlgebraicTopology.PoincareDuality.AlexanderDisjoint
public import MMP.AlgebraicTopology.SingularCohomology.Relative.Homotopy

/-!
# Singular cohomology of a contractible space

Let `Z` be a space whose identity is homotopic to the constant map at a point `z₀`. Then, in the
model of cocycles modulo coboundaries,

* every `0`-cocycle is a constant function, so `r ↦ [r]` is surjective onto `H^0 Z`;
* `H^p Z = 0` for `p > 0`.

By homotopy invariance (`SingularCochain.relCohomologyMap_eq_of_homotopy`) a cocycle `φ` is
cohomologous to its pull-back along the constant map, the constant cochain with value
`a = φ(z₀)`. In degree `0` coboundaries vanish, so `φ` is constant. In degree `p > 0` the
coboundary of the constant `(p - 1)`-cochain `a` is `∑_{i ≤ p} (-1)^i a`, which is `a` for `p`
even; for `p` odd the constant `a` is a cocycle only if `a = 0`.

## Main results

* `MMP.PoincareAlexander.constCochain_eq_of_mem_relCocycles_zero`: `0`-cocycles
  are constant.
* `MMP.PoincareAlexander.mk_eq_zero_of_homotopy_const`: `H^p Z = 0`, `p > 0`.
* `MMP.PoincareAlexander.bijective_capHomQ_zero_of_homotopy_const`: cap product with a
  fundamental class is bijective in degree `0`.
-/

@[expose] public noncomputable section

open CategoryTheory Set Topology Function

universe u

namespace MMP

namespace PoincareAlexander

open SingularChain SingularCochain

variable {R : Type u} [CommRing R] {Z : TopCat.{u}}

/-- The constant `p`-cochain with value `a`. -/
def constCochain (p : ℕ) (a : R) : Simplex Z p → R := fun _ ↦ a

omit [CommRing R] in
@[simp] lemma constCochain_apply (p : ℕ) (a : R) (σ : Simplex Z p) :
    constCochain p a σ = a := rfl

/-- The coboundary of the constant `p`-cochain `a` is the constant `(p + 1)`-cochain with value
`a` if `p + 1` is even and `0` otherwise. -/
lemma coboundary_constCochain (p : ℕ) (a : R) :
    coboundary R p (constCochain (Z := Z) p a) =
      constCochain (p + 1) (if Even (p + 1) then a else 0) := by
  funext σ
  rw [coboundary_apply]
  simp only [constCochain_apply]
  rw [← Finset.sum_mul, Fin.sum_neg_one_pow]
  split_ifs <;> simp_all [Nat.even_add_one]

/-- The pull-back along a constant map is a constant cochain. -/
lemma cochainPullback_const (z₀ : Z) (p : ℕ) (φ : Simplex Z p → R) :
    cochainPullback R (TopCat.ofHom (ContinuousMap.const Z z₀)) p φ =
      constCochain p (φ (ContinuousMap.const _ z₀)) :=
  rfl

variable (z₀ : Z) (H : TopCat.Homotopy (𝟙 Z) (TopCat.ofHom (ContinuousMap.const Z z₀)))

include H in
/-- A cocycle is cohomologous to the constant cochain `φ(z₀)`. -/
lemma sub_constCochain_mem_relCoboundaries {p : ℕ} (φ : relCocycles R (∅ : Set Z) p) :
    φ.1 - constCochain p (φ.1 (ContinuousMap.const _ z₀)) ∈ relCoboundaries R (∅ : Set Z) p := by
  have := LinearMap.congr_fun (relCohomologyMap_eq_of_homotopy (R := R) H
      (A := (∅ : Set Z)) (A' := (∅ : Set Z)) (fun y hy ↦ absurd hy (notMem_empty y))
      (empty_subset _) (empty_subset _) p) (Submodule.Quotient.mk φ)
  erw [relCohomologyMap_mk, relCohomologyMap_mk, Submodule.Quotient.eq] at this
  rwa [← cochainPullback_const]

include H in
/-- On a contractible space, `0`-cocycles are constant. -/
theorem constCochain_eq_of_mem_relCocycles_zero (φ : relCocycles R (∅ : Set Z) 0) :
    φ.1 = constCochain 0 (φ.1 (ContinuousMap.const _ z₀)) :=
  sub_eq_zero.1 ((Submodule.mem_bot R).1 (sub_constCochain_mem_relCoboundaries z₀ H φ))

include H in
/-- On a contractible space, `H^p = 0` for `p > 0`. -/
theorem mk_eq_zero_of_homotopy_const {p : ℕ} (hp : 0 < p) (φ : relCocycles R (∅ : Set Z) p) :
    (Submodule.Quotient.mk φ : relCohomology R (∅ : Set Z) p) = 0 := by
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  change φ.1 ∈ relCoboundaries R ∅ p
  have h1 := sub_constCochain_mem_relCoboundaries z₀ H φ
  set a := φ.1 (ContinuousMap.const _ z₀)
  suffices h2 : constCochain p a ∈ relCoboundaries R (∅ : Set Z) p by
    simpa using add_mem h1 h2
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  by_cases hk : Even (k + 1)
  · refine ⟨constCochain k a, mem_vanishing_empty _, ?_⟩
    rw [coboundary_constCochain, ite_eq_left hk]
  · have hcoc : coboundary R (k + 1) (constCochain (Z := Z) (k + 1) a) = 0 := by
      have hφ := ((mem_relCocycles_iff R _ _ _).1 φ.2).2
      have hsub := ((mem_relCocycles_iff R _ _ _).1
        (relCoboundaries_le (R := R) (∅ : Set Z) (k + 1) h1)).2
      rwa [map_sub, hφ, zero_sub, neg_eq_zero] at hsub
    rw [coboundary_constCochain, ite_eq_left (Nat.not_even_iff_odd.1 hk).add_one] at hcoc
    rw [show a = 0 from congrFun hcoc (ContinuousMap.const _ z₀)]
    exact Submodule.zero_mem _

section cap

open SingularCross BorelMooreCross BorelMooreCap LocallyFiniteChain borelMooreHomology

/-- `front n n h` is the identity map. -/
@[simp] lemma front_self (n : ℕ) (h : n ≤ n) : front n n h = id := by
  funext j
  exact Fin.ext (by simp [front_val])

/-- `opS` along the identity map fixes every simplex. -/
@[simp] lemma opS_id {n : ℕ} (σ : Simp Z n) :
    opS (Y := Z) (id : Fin (n + 1) → Fin (n + 1)) σ = σ := by
  apply (simplexEquiv Z n).injective
  rw [simplexEquiv_opS]
  ext x : 1
  change simplexEquiv Z n σ (stdSimplex.map id x) = _
  rw [stdSimplex.map_id_apply]

/-- The cap product with the constant `0`-cochain `r` is multiplication by `r`. -/
lemma capChain_constCochain (n : ℕ) (h : 0 + n = n) (r : R) (c : (BM R Z).X n) :
    capChain R 0 n n h (constCochain 0 r) c = r • c := by
  apply coeff_injective R
  rw [capChain_apply, coeff_pf, front_self, coeff_W]
  funext σ
  rw [show (opS (Y := Z) (id : Fin (n + 1) → Fin (n + 1))) = id from funext opS_id]
  exact pushforwardFun_apply_of_injective (φ := id) injective_id _ σ

/-- A constant `0`-cochain is a cocycle. -/
lemma constCochain_zero_mem_relCocycles (r : R) :
    constCochain (Z := Z) 0 r ∈ relCocycles R (∅ : Set Z) 0 := by
  refine (mem_relCocycles_iff R _ _ _).2 ⟨mem_vanishing_empty _, ?_⟩
  rw [coboundary_constCochain, ite_eq_right (by decide)]
  rfl

include H in
/-- **Duality in degree `0` on a contractible space.** If `r ↦ r [z]` is a bijection
`R ≃ H_n Z`, then `[φ] ↦ [φ ∩ z]`, `H^0 Z → H_n Z`, is bijective. -/
theorem bijective_capHomQ_zero_of_homotopy_const (n : ℕ) (h : 0 + n = n) (z : Cyc (R := R) Z n)
    (hz : Bijective fun r : R ↦ r • (Submodule.Quotient.mk z : HomQ (R := R) Z n)) :
    Bijective fun c ↦ capHomQ R (∅ : Set Z) 0 n n h c (Submodule.Quotient.mk z) := by
  set e : R → relCohomology R (∅ : Set Z) 0 := fun r ↦
    Submodule.Quotient.mk ⟨constCochain 0 r, constCochain_zero_mem_relCocycles r⟩
  have he : Surjective e := by
    intro c
    obtain ⟨φ, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    exact ⟨φ.1 (ContinuousMap.const _ z₀), congrArg Submodule.Quotient.mk
      (Subtype.ext (constCochain_eq_of_mem_relCocycles_zero z₀ H φ).symm)⟩
  have hcomp : ∀ r, capHomQ R (∅ : Set Z) 0 n n h (e r) (Submodule.Quotient.mk z) =
      r • (Submodule.Quotient.mk z : HomQ (R := R) Z n) := by
    intro r
    change capHomQ R ∅ 0 n n h (Submodule.Quotient.mk _) (Submodule.Quotient.mk z) = _
    rw [capHomQ_mk]
    refine Eq.trans ?_
      ((Submodule.mkQ (LinearMap.range ((BM R Z).sc n).moduleCatToCycles)).map_smul r z)
    congr 1
    exact Subtype.ext (capChain_constCochain n h r z.1)
  refine ⟨fun c c' hcc ↦ ?_, fun x ↦ ?_⟩
  · obtain ⟨r, rfl⟩ := he c
    obtain ⟨r', rfl⟩ := he c'
    exact congrArg e (hz.1 ((hcomp r).symm.trans (hcc.trans (hcomp r'))))
  · obtain ⟨r, hr⟩ := hz.2 x
    exact ⟨e r, (hcomp r).trans hr⟩

end cap

end PoincareAlexander

end MMP
