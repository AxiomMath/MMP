module

public import MMP.AlgebraicGeometry.MMP.ConeTheorem.ConeDatum

/-!
# Positive bases and integral generators of rays for a cone datum (KM 3.3, 3.15)

Let `(N_ℤ, NE̅, K, a)` be a cone datum.

* If `rank N_ℤ = d + 1`, there are `H₁, …, H_d ∈ N_ℤ^*` positive on `NE̅ ∖ {0}` such that
  `K, H₁, …, H_d` is a basis of `N_ℝ^*`.
* Every `R ∈ 𝓡(NE̅, K)` is `ℝ_{≥0} ξ` for some `ξ ∈ N_ℤ` with `K(ξ) < 0`.

## Main results

* `MMP.Positivity.ConeDatum.exists_basis_cons_realOfIntForm`
* `MMP.Positivity.ConeDatum.exists_integral_generator`
-/

@[expose] public noncomputable section

universe u

open TensorProduct

namespace MMP.Positivity

open MMP.Mori

namespace ConeDatum

variable {N : Type u} [AddCommGroup N] [Module.Free ℤ N] [Module.Finite ℤ N]

/-- For a cone datum `(N_ℤ, NE̅, K, a)` and a basis `(eᵢ)` of `N_ℤ` with dual coordinates `xᵢ`,
there is `H₀ ∈ N_ℤ^*` such that `H₀` and every `H₀ + xⱼ` are positive on `NE̅ ∖ {0}`. -/
theorem exists_intForm_pos_and_add_coord_pos (D : ConeDatum N) {ι : Type*} [Finite ι]
    (b : Module.Basis ι ℤ N) :
    ∃ H₀ : Module.Dual ℤ N, (∀ z ∈ D.cone, z ≠ 0 → 0 < realOfIntForm N H₀ z) ∧
      ∀ j, ∀ z ∈ D.cone, z ≠ 0 → 0 < realOfIntForm N (H₀ + b.coord j) z := by
  have := Fintype.ofFinite ι
  let := moduleTopology ℝ (ℝ ⊗[ℤ] N)
  obtain ⟨h₁, h₂, h₃⟩ := moduleTopology_isTopologicalAddGroup_continuousSMul_t2Space (ℝ ⊗[ℤ] N)
  obtain ⟨G, hG⟩ := exists_dual_pos_of_salient (isCone_coe D.cone) D.cone.convex
    D.isClosed_cone D.inter_neg_eq
  obtain ⟨c, -, hc⟩ := exists_sum_abs_le_mul_of_forall_pos (isCone_coe D.cone)
    D.isClosed_cone hG Finset.univ fun i => realOfIntForm N (b.coord i)
  exact exists_intForm_pos_and_add_coord_pos_of_sum_abs_le D hG b hc

/-- The forms in `N_ℤ^*` positive on `NE̅ ∖ {0}` span `N_ℝ^*`. -/
theorem span_realOfIntForm_pos_eq_top (D : ConeDatum N) :
    Submodule.span ℝ (realOfIntForm N ''
      {H | ∀ z ∈ D.cone, z ≠ 0 → 0 < realOfIntForm N H z}) = ⊤ := by
  let b := Module.Free.chooseBasis ℤ N
  let bB := Algebra.TensorProduct.basis ℝ b
  obtain ⟨H₀, hH₀pos, hHjpos⟩ := exists_intForm_pos_and_add_coord_pos D b
  refine eq_top_iff.mpr ?_
  rw [← bB.dualBasis.span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  have e : realOfIntForm N (H₀ + b.coord j) - realOfIntForm N H₀ = bB.coord j :=
    LinearMap.ext fun z => by
      rw [LinearMap.sub_apply, realOfIntForm_add_apply, Module.Basis.coord_apply,
        ← realOfIntForm_coord_apply]
      ring
  rw [Module.Basis.coe_dualBasis, ← e]
  exact sub_mem (Submodule.subset_span ⟨_, hHjpos j, rfl⟩)
    (Submodule.subset_span ⟨_, hH₀pos, rfl⟩)

/-- **KM 3.3 Steps 2, 4, "choose ample divisors `H₁, …, H_d` … together with `K` a basis".**
Let `(N_ℤ, NE̅, K, a)` be a cone datum with `rank N_ℤ = d + 1`. Then there are
`H₁, …, H_d ∈ N_ℤ^*`, each positive on `NE̅ ∖ {0}`, such that `K, H₁, …, H_d` is a basis of
`N_ℝ^*`. -/
@[mmp "lem_km3b_cone_positive_basis"]
theorem exists_basis_cons_realOfIntForm (D : ConeDatum N) {d : ℕ}
    (hd : Module.finrank ℤ N = d + 1) :
    ∃ H : Fin d → Module.Dual ℤ N,
      (∀ i, ∀ z ∈ D.cone, z ≠ 0 → 0 < realOfIntForm N (H i) z) ∧
      ∃ b : Module.Basis (Fin (d + 1)) ℝ (Module.Dual ℝ (ℝ ⊗[ℤ] N)),
        ⇑b = Fin.cons (realOfRatForm N D.form) fun i => realOfIntForm N (H i) := by
  classical
  obtain ⟨z₀, -, hKz₀⟩ := D.exists_form_neg
  set K := realOfRatForm N D.form
  have hK0 : K ≠ 0 := fun h => by simp [h] at hKz₀
  let P : Set (Module.Dual ℤ N) := {H | ∀ z ∈ D.cone, z ≠ 0 → 0 < realOfIntForm N H z}
  let t : Set (Module.Dual ℝ (ℝ ⊗[ℤ] N)) := insert K (realOfIntForm N '' P)
  have hspan : ⊤ ≤ Submodule.span ℝ t :=
    (span_realOfIntForm_pos_eq_top D).ge.trans (Submodule.span_mono (Set.subset_insert _ _))
  obtain ⟨bs, hbst, hKbs, htbs, hli⟩ := exists_linearIndepOn_id_extension
    (LinearIndepOn.singleton (R := ℝ) (v := id) hK0)
    (Set.singleton_subset_iff.mpr (Set.mem_insert K _))
  have hKbs' : K ∈ bs := Set.singleton_subset_iff.mp hKbs
  let B := Module.Basis.mk (v := (Subtype.val : bs → _)) hli (by
    rw [Subtype.range_coe]
    exact hspan.trans (Submodule.span_le.mpr htbs))
  have hfr : Module.finrank ℝ (Module.Dual ℝ (ℝ ⊗[ℤ] N)) = d + 1 := by
    rw [Subspace.dual_finrank_eq, Module.finrank_baseChange, hd]
  have : Finite bs := Module.Finite.finite_basis B
  have hcard : Nat.card ↥(bs \ {K}) = d := by
    rw [Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem hKbs', ← Nat.card_coe_set_eq,
      ← Module.finrank_eq_nat_card_basis B, hfr, Nat.add_sub_cancel]
  have : Finite ↥(bs \ {K}) := ((Set.toFinite bs).sdiff).to_subtype
  let e : Fin d ≃ ↥(bs \ {K}) := (Finite.equivFinOfCardEq hcard).symm
  have hmem : ∀ i, ∃ H ∈ P, realOfIntForm N H = (e i).1 := fun i =>
    (Set.mem_insert_iff.mp (hbst (e i).2.1)).resolve_left (e i).2.2
  choose H hHP hHe using hmem
  refine ⟨H, hHP, ?_⟩
  let f : Fin (d + 1) → Module.Dual ℝ (ℝ ⊗[ℤ] N) := Fin.cons K fun i => realOfIntForm N (H i)
  have hv : (fun i => realOfIntForm N (H i)) = fun i => ((e i).1 : Module.Dual ℝ (ℝ ⊗[ℤ] N)) :=
    funext hHe
  have hinj : Function.Injective f := Fin.cons_injective_iff.mpr
    ⟨fun ⟨i, hi⟩ => (e i).2.2 ((hHe i).symm.trans hi),
      fun i j hij => e.injective (Subtype.ext ((hHe i).symm.trans (hij.trans (hHe j))))⟩
  have hrange : Set.range f = bs := by
    have : Set.range (fun i => ((e i).1 : Module.Dual ℝ (ℝ ⊗[ℤ] N))) = bs \ {K} := by
      ext x
      exact ⟨fun ⟨i, hi⟩ => hi ▸ (e i).2, fun hx => ⟨e.symm ⟨x, hx⟩, by simp⟩⟩
    simp only [f, Fin.range_cons, hv, this, Set.insert_sdiff_singleton,
      Set.insert_eq_of_mem hKbs']
  have hlif : LinearIndependent ℝ f := (linearIndepOn_id_range_iff hinj).mp (hrange ▸ hli)
  exact ⟨basisOfLinearIndependentOfCardEqFinrank hlif (by rw [Fintype.card_fin, hfr]),
    coe_basisOfLinearIndependentOfCardEqFinrank _ _⟩

/-- **KM Thm. 3.15, "`ξᵢ ∈ N_ℤ`".** Let `(N_ℤ, NE̅, K, a)` be a cone datum and
`R ∈ 𝓡(NE̅, K)`. Then `R = ℝ_{≥0} ξ` for some `ξ ∈ N_ℤ` with `K(ξ) < 0`. -/
@[mmp "lem_km3b_cone_rays_rational"]
theorem exists_integral_generator (D : ConeDatum N) {R : Set (ℝ ⊗[ℤ] N)}
    (hR : R ∈ D.negativeRationalRays) :
    ∃ ξ : N, realOfRatForm N D.form ((1 : ℝ) ⊗ₜ[ℤ] ξ) < 0 ∧
      R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • ((1 : ℝ) ⊗ₜ[ℤ] ξ) = w} := by
  let b := Module.Free.chooseBasis ℤ N
  let bB := Algebra.TensorProduct.basis ℝ b
  obtain ⟨H₀, hH₀pos, hHjpos⟩ := exists_intForm_pos_and_add_coord_pos D b
  obtain ⟨ξ, hξR, -, hKξ, hRξ⟩ := exists_eq_ray_of_mem_negativeRationalRays D hR
  have hξ0 : ξ ≠ 0 := fun h => by simp [h] at hKξ
  have ha : (0 : ℝ) < D.index := by exact_mod_cast D.index_pos
  choose k hk using fun j =>
    exists_realOfIntForm_eq_intCast_div_index D hH₀pos (hHjpos j) hR hξR hξ0 hKξ
  have hξa : (1 : ℝ) ⊗ₜ[ℤ] (∑ i, k i • b i) = (D.index : ℝ) • ξ := by
    rw [TensorProduct.tmul_sum]
    conv_rhs => rw [← bB.sum_repr ξ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← realOfIntForm_coord_apply, hk i, smul_smul, mul_div_cancel₀ _ ha.ne',
      TensorProduct.tmul_smul, ← Int.cast_smul_eq_zsmul ℝ, Algebra.TensorProduct.basis_apply]
  refine ⟨∑ i, k i • b i, ?_, ?_⟩
  · rw [hξa, map_smul, smul_eq_mul, hKξ]
    linarith
  · rw [hξa, setOf_exists_smul_smul_eq_of_pos ha, hRξ]

end ConeDatum

end MMP.Positivity
