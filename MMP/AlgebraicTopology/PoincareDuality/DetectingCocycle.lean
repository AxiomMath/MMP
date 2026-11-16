module

public import MMP.AlgebraicTopology.SingularCohomology.CupProduct.Cochains
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Projection

/-!
# A relative cocycle detecting a generator of the top relative homology

Let `C_•` be a chain complex of projective modules over a commutative ring `R`, indexed by `ℕ`,
which is exact in degrees `≤ m` (`H_0 = 0` and `H_{k+1} = 0` for `k < m`). Then each boundary
module `B_k = im (∂ : C_{k+1} → C_k)`, `k ≤ m`, is projective: `B_0 = C_0`, and if `B_k` is
projective the surjection `C_{k+1} → B_k` splits, so `Z_{k+1}` is a retract of `C_{k+1}` and
`B_{k+1} = Z_{k+1}`. Hence `Z_{m+1}` is a retract of `C_{m+1}`. If moreover `H_{m+1}` is free of
rank one on the class of a cycle `c₀`, the coordinate along `c₀` is a linear form on `Z_{m+1}`
vanishing on `B_{m+1}`; composed with the retraction it is a cocycle `φ` with `φ c₀ = 1` (the
universal-coefficient splitting).

Applied to the relative singular complex `C_k(Y) / C_k(A)`, whose terms are free on the simplices
not inside `A`, this gives a relative cocycle `φ ∈ Z^{m+1}(Y, A)` with `⟨φ, c₀⟩ = 1` whenever
`H_k(Y, A) = 0` for `k ≤ m` and `H_{m+1}(Y, A)` is free on the class of `c₀`.

## Main results

* `MMP.SingularCochain.exists_linearMap_eq_one_of_exact`: the algebraic statement
  for a complex of projective modules.
* `MMP.SingularCochain.exists_mem_relCocycles_eval_eq_one`: the relative singular
  cocycle detecting a free generator of the top relative homology.

## References

* [A. Hatcher, *Algebraic Topology*][hatcher2002], §3.1, Theorem 3.2.
-/

@[expose] public noncomputable section

open Finsupp Set

namespace MMP

namespace SingularCochain

open SingularChain

section algebra

variable {R : Type*} [Ring R] {P : ℕ → Type*} [∀ k, AddCommGroup (P k)]
  [∀ k, Module R (P k)]

/-- In a complex of projective modules exact in degrees `≤ m`, the boundary modules `B_k`,
`k ≤ m`, are projective. -/
theorem projective_range_of_exact [∀ k, Module.Projective R (P k)]
    (d : ∀ k, P (k + 1) →ₗ[R] P k) (hdd : ∀ k, d k ∘ₗ d (k + 1) = 0) {m : ℕ}
    (h0 : LinearMap.range (d 0) = ⊤)
    (hlow : ∀ k, k < m → LinearMap.ker (d k) ≤ LinearMap.range (d (k + 1))) :
    ∀ k, k ≤ m → Module.Projective R (LinearMap.range (d k)) := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [h0]
    exact Module.Projective.of_equiv (Submodule.topEquiv).symm
  | succ k ih =>
    intro hk
    have := ih (by omega)
    obtain ⟨s, hs⟩ := Module.projective_lifting_property (d k).rangeRestrict LinearMap.id
      (LinearMap.surjective_rangeRestrict _)
    have hker : LinearMap.ker (d k) = LinearMap.range (d (k + 1)) := by
      refine le_antisymm (hlow k (by omega)) ?_
      rintro _ ⟨y, rfl⟩
      rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hdd, LinearMap.zero_apply]
    have hπ : ∀ x, x - s ((d k).rangeRestrict x) ∈ LinearMap.ker (d k) := fun x ↦ by
      have : d k (s ((d k).rangeRestrict x)) = d k x :=
        congrArg Subtype.val (LinearMap.congr_fun hs ((d k).rangeRestrict x))
      rw [LinearMap.mem_ker, map_sub, this, sub_self]
    let π : P (k + 1) →ₗ[R] LinearMap.ker (d k) :=
      LinearMap.codRestrict _ (LinearMap.id - s ∘ₗ (d k).rangeRestrict) hπ
    have : Module.Projective R (LinearMap.ker (d k)) := by
      refine Module.Projective.of_split (LinearMap.ker (d k)).subtype π ?_
      ext ⟨z, hz⟩
      have hz' : (d k).rangeRestrict z = 0 := Subtype.ext (by simpa using hz)
      simp [π, hz']
    rw [← hker]
    infer_instance

/-- The universal-coefficient splitting: in a complex of projective modules exact in degrees
`≤ m` whose homology in degree `m + 1` is free on the class of the cycle `c₀`, some linear form
on `C_{m+1}` vanishes on the boundaries and takes the value `1` on `c₀`. -/
theorem exists_linearMap_eq_one_of_exact [∀ k, Module.Projective R (P k)]
    (d : ∀ k, P (k + 1) →ₗ[R] P k) (hdd : ∀ k, d k ∘ₗ d (k + 1) = 0) {m : ℕ}
    (h0 : LinearMap.range (d 0) = ⊤)
    (hlow : ∀ k, k < m → LinearMap.ker (d k) ≤ LinearMap.range (d (k + 1)))
    (c₀ : P (m + 1)) (hc₀ : d m c₀ = 0)
    (hgen : ∀ z, d m z = 0 → ∃ r : R, z - r • c₀ ∈ LinearMap.range (d (m + 1)))
    (hfree : ∀ r : R, r • c₀ ∈ LinearMap.range (d (m + 1)) → r = 0) :
    ∃ φ : P (m + 1) →ₗ[R] R, φ ∘ₗ d (m + 1) = 0 ∧ φ c₀ = 1 := by
  have := projective_range_of_exact d hdd h0 hlow m le_rfl
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (d m).rangeRestrict LinearMap.id
    (LinearMap.surjective_rangeRestrict _)
  have hs' : ∀ x, d m (s ((d m).rangeRestrict x)) = d m x := fun x ↦
    congrArg Subtype.val (LinearMap.congr_fun hs ((d m).rangeRestrict x))
  have hπ : ∀ x, x - s ((d m).rangeRestrict x) ∈ LinearMap.ker (d m) := fun x ↦ by
    rw [LinearMap.mem_ker, map_sub, hs', sub_self]
  let Z := LinearMap.ker (d m)
  let π : P (m + 1) →ₗ[R] Z :=
    LinearMap.codRestrict _ (LinearMap.id - s ∘ₗ (d m).rangeRestrict) hπ
  let B : Submodule R Z := (LinearMap.range (d (m + 1))).comap Z.subtype
  let z₀ : Z := ⟨c₀, hc₀⟩
  let f : R →ₗ[R] Z ⧸ B := LinearMap.toSpanSingleton R _ (B.mkQ z₀)
  have hf : Function.Bijective f := by
    refine ⟨fun r r' h ↦ ?_, fun q ↦ ?_⟩
    · have h' : (r - r') • c₀ ∈ LinearMap.range (d (m + 1)) := by
        have h1 : (Submodule.Quotient.mk (r • z₀) : Z ⧸ B) = Submodule.Quotient.mk (r' • z₀) := by
          rw [Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul]
          exact h
        simpa [B, z₀, sub_smul] using (Submodule.Quotient.eq B).1 h1
      exact sub_eq_zero.1 (hfree _ h')
    · obtain ⟨⟨z, hz⟩, rfl⟩ := B.mkQ_surjective q
      obtain ⟨r, hr⟩ := hgen z hz
      refine ⟨r, ?_⟩
      change r • B.mkQ z₀ = B.mkQ ⟨z, hz⟩
      rw [← map_smul, Submodule.mkQ_apply, Submodule.mkQ_apply]
      refine (Submodule.Quotient.eq B).2 ?_
      simpa [B, z₀] using sub_mem_comm_iff.1 hr
  let e := LinearEquiv.ofBijective f hf
  refine ⟨e.symm.toLinearMap ∘ₗ B.mkQ ∘ₗ π, ?_, ?_⟩
  · ext y
    have hdy : d m (d (m + 1) y) = 0 := LinearMap.congr_fun (hdd m) y
    have hr : (d m).rangeRestrict (d (m + 1) y) = 0 := Subtype.ext (by simpa using hdy)
    have hπy : π (d (m + 1) y) = ⟨d (m + 1) y, LinearMap.mem_ker.2 hdy⟩ :=
      Subtype.ext (by simp [π, hr])
    have hB : (⟨d (m + 1) y, LinearMap.mem_ker.2 hdy⟩ : Z) ∈ B := ⟨y, rfl⟩
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, hπy]
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero B).2 hB, map_zero]
  · have hr : (d m).rangeRestrict c₀ = 0 := Subtype.ext (by simpa using hc₀)
    have hπc : π c₀ = z₀ := Subtype.ext (by simp [π, hr, z₀])
    simp only [LinearMap.comp_apply, hπc, LinearEquiv.coe_coe]
    rw [LinearEquiv.symm_apply_eq]
    simp [e, f]

end algebra

section relative

variable {R : Type*} [CommRing R] {Y : Type*} [TopologicalSpace Y]

/-- The relative chains `C_k(Y) / C_k(A)` are projective: free on the simplices not inside
`A`. -/
instance projective_chain_quotient_inside (A : Set Y) (k : ℕ) :
    Module.Projective R (Chain R Y k ⧸ inside R k A) := by
  have hc : IsCompl (inside R k A) (supported R R {σ : Simplex Y k | range σ ⊆ A}ᶜ) :=
    ⟨disjoint_supported_supported disjoint_compl_right,
      codisjoint_iff.2 (by rw [← supported_union, union_compl_self, supported_univ])⟩
  have : Module.Projective R (supported R R {σ : Simplex Y k | range σ ⊆ A}ᶜ) :=
    Module.Projective.of_equiv (supportedEquivFinsupp _).symm
  exact Module.Projective.of_equiv (Submodule.quotientEquivOfIsCompl _ _ hc).symm

/-- The relative boundary `C_{k+1}(Y) / C_{k+1}(A) → C_k(Y) / C_k(A)`. -/
def relBd (A : Set Y) (k : ℕ) :
    (Chain R Y (k + 1) ⧸ inside R (k + 1) A) →ₗ[R] (Chain R Y k ⧸ inside R k A) :=
  (inside R (k + 1) A).mapQ (inside R k A) (bd R k) fun c hc ↦ by
    refine VertexChain.mem_of_mem_supported (bd R k) (inside R k A) (fun σ hσ ↦ ?_) hc
    rw [bd_single]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _
      (single_mem_supported R _ (range_comp_subset hσ _))

/-- The relative boundary of the class of a chain `c` is the class of `∂c`. -/
@[simp] theorem relBd_mk (A : Set Y) (k : ℕ) (c : Chain R Y (k + 1)) :
    relBd A k (Submodule.Quotient.mk c) = Submodule.Quotient.mk (bd R k c) := rfl

/-- The relative boundary squares to zero. -/
@[simp] theorem relBd_comp_relBd (A : Set Y) (k : ℕ) :
    relBd (R := R) A k ∘ₗ relBd A (k + 1) = 0 := by
  ext c
  change Submodule.Quotient.mk (bd R k (bd R (k + 1) (single c 1))) = 0
  rw [bd_bd, Submodule.Quotient.mk_zero]

/-- A relative cocycle detecting a free generator of the top relative homology: if
`H_k(Y, A; R) = 0` for `k ≤ m` and `H_{m+1}(Y, A; R)` is free of rank one on the class of the
relative cycle `c₀`, some `φ ∈ Z^{m+1}(Y, A; R)` has `⟨φ, c₀⟩ = 1`. -/
theorem exists_mem_relCocycles_eval_eq_one (A : Set Y) (m : ℕ)
    (h0 : ∀ c : Chain R Y 0, ∃ w : Chain R Y 1, c - bd R 0 w ∈ inside R 0 A)
    (hlow : ∀ k, k + 1 < m + 1 → ∀ c : Chain R Y (k + 1), bd R k c ∈ inside R k A →
      ∃ w : Chain R Y (k + 2), c - bd R (k + 1) w ∈ inside R (k + 1) A)
    (c₀ : Chain R Y (m + 1)) (hc₀ : bd R m c₀ ∈ inside R m A)
    (hgen : ∀ c : Chain R Y (m + 1), bd R m c ∈ inside R m A →
      ∃ r : R, ∃ w : Chain R Y (m + 2), c - r • c₀ - bd R (m + 1) w ∈ inside R (m + 1) A)
    (hfree : ∀ r : R, (∃ w : Chain R Y (m + 2), r • c₀ - bd R (m + 1) w ∈ inside R (m + 1) A) →
      r = 0) :
    ∃ φ ∈ relCocycles R A (m + 1), eval φ c₀ = 1 := by
  let P : ℕ → Type _ := fun k ↦ Chain R Y k ⧸ inside R k A
  let d : ∀ k, P (k + 1) →ₗ[R] P k := relBd A
  have hdd : ∀ k, d k ∘ₗ d (k + 1) = 0 := relBd_comp_relBd A
  have hmk : ∀ {k} {x y : Chain R Y k}, (Submodule.Quotient.mk x : P k) = Submodule.Quotient.mk y
      ↔ x - y ∈ inside R k A := fun {_ _ _} ↦ Submodule.Quotient.eq _
  have hmk0 : ∀ {k} {x : Chain R Y k}, (Submodule.Quotient.mk x : P k) = 0 ↔ x ∈ inside R k A :=
    fun {_ _} ↦ Submodule.Quotient.mk_eq_zero _
  obtain ⟨φ', hφd, hφc⟩ := exists_linearMap_eq_one_of_exact (P := P) d hdd (m := m)
    (by
      refine eq_top_iff.2 fun x _ ↦ ?_
      obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      obtain ⟨w, hw⟩ := h0 c
      exact ⟨Submodule.Quotient.mk w, hmk.2 (sub_mem_comm_iff.1 hw)⟩)
    (fun k hk x hx ↦ by
      obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      obtain ⟨w, hw⟩ := hlow k (by omega) c (hmk0.1 hx)
      exact ⟨Submodule.Quotient.mk w, hmk.2 (sub_mem_comm_iff.1 hw)⟩)
    (Submodule.Quotient.mk c₀) (hmk0.2 hc₀)
    (fun z hz ↦ by
      obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      obtain ⟨r, w, hw⟩ := hgen c (hmk0.1 hz)
      refine ⟨r, Submodule.Quotient.mk w, ?_⟩
      change Submodule.Quotient.mk (bd R (m + 1) w) = _
      rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_sub]
      exact hmk.2 (sub_mem_comm_iff.1 hw))
    (fun r ⟨y, hy⟩ ↦ by
      obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      refine hfree r ⟨w, ?_⟩
      have hy' : (Submodule.Quotient.mk (bd R (m + 1) w) : P (m + 1)) =
          Submodule.Quotient.mk (r • c₀) := hy.trans (Submodule.Quotient.mk_smul _ r c₀).symm
      exact sub_mem_comm_iff.1 (hmk.1 hy'))
  let φbar : Chain R Y (m + 1) →ₗ[R] R := φ' ∘ₗ (inside R (m + 1) A).mkQ
  have heval : eval (fun σ ↦ φbar (single σ 1)) = φbar := by
    ext σ
    simp [eval]
  refine ⟨fun σ ↦ φbar (single σ 1), ⟨fun σ hσ ↦ ?_, ?_⟩, ?_⟩
  · change φ' (Submodule.Quotient.mk (single σ 1)) = 0
    rw [hmk0.2 (single_mem_supported R _ hσ), map_zero]
  · change coboundary R (m + 1) _ = 0
    funext σ
    have h1 := eval_coboundary (m + 1) (fun σ ↦ φbar (single σ 1)) (single σ 1)
    rw [heval] at h1
    simp only [eval, linearCombination_single, one_smul] at h1
    rw [Pi.zero_apply, h1]
    change φ' (d (m + 1) (Submodule.Quotient.mk (single σ 1))) = 0
    rw [← LinearMap.comp_apply, hφd, LinearMap.zero_apply]
  · rwa [heval]

end relative

end SingularCochain

end MMP
