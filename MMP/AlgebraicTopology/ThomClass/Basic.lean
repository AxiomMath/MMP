module

public import MMP.AlgebraicTopology.SingularCohomology.CupProduct.Comparison
public import Mathlib.Topology.VectorBundle.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
/-!
# The Thom class of a complex vector bundle (Fulton, §19.1)

Let `V` be a real vector space of dimension `n`. An *oriented simplex around `0`* in `V` is an
affine singular `n`-simplex `σ` whose vertices `v₀, …, vₙ` contain `0` in the interior of their
convex hull and are positively ordered: the basis `v₁ - v₀, …, vₙ - v₀` defines the given
orientation. Its boundary lies in `V - 0`, so `σ` is a relative cycle of `(V, V - 0)`, and its
class is the generator `μ_V ∈ H_n(V, V - 0)` of the orientation (Dold, VIII.2; Milnor–Stasheff,
§9). A complex vector space of dimension `r` is oriented by its complex structure: for a complex
basis `e₁, …, e_r`, the real basis `e₁, i e₁, …, e_r, i e_r` (this orientation does not depend
on the complex basis, as the realification of a complex matrix has determinant `|det|² > 0`).

Let `E` be a complex topological vector bundle of rank `r` on a space `X`, with zero section
`0_E ⊆ E`. A *Thom class* of `E` (Milnor–Stasheff, §9) is a class `u ∈ H^{2r}(E, E - 0_E; R)`
whose restriction to every fibre `(E_x, E_x - 0)` is the generator dual to `μ_{E_x}`, i.e.
`⟨u, μ_{E_x}⟩ = 1`; Thom's theorem (Milnor–Stasheff, Thm. 10.4) says there is exactly one, the
Thom class `u_E`. As `H^{2r}(E_x, E_x - 0; R) ≅ R` through evaluation on `μ_{E_x}`, the condition
`⟨u, μ_{E_x}⟩ = 1` is equivalent to "the restriction of `u` to the fibre is the generator".

The Kronecker pairing used here is that of relative singular cohomology with relative cycles: a
chain `c` of `Y` annihilated by every relative coboundary (for instance a chain whose boundary
lies in `A`) defines `⟨-, c⟩ : H^n(Y, A; R) → R`.

## Main definitions

* `MMP.SingularCochain.relEval`: the Kronecker pairing `⟨-, c⟩` on relative
  cohomology with a relative cycle `c`.
* `MMP.ThomClass.complexOrientationBasis`: the real basis `e₁, i e₁, …, e_r, i e_r`
  of `ℂ^r`.
* `MMP.ThomClass.IsOrientedSimplexAroundZero`: oriented simplices around `0`.
* `MMP.ThomClass.fibreSimplex`: such a simplex in a fibre of a vector bundle, as a
  singular simplex of the total space.
* `MMP.IsThomClass`: Thom classes of a complex topological vector bundle.

## Main results

* `MMP.SingularCochain.eval_eq_zero_of_mem_relCoboundaries`: a chain whose boundary
  lies in `A` is annihilated by the relative coboundaries.
* `MMP.ThomClass.IsOrientedSimplexAroundZero.affineSimplex_ne_zero`: the faces of
  an oriented simplex around `0` avoid `0`.
* `MMP.ThomClass.exists_isOrientedSimplexAroundZero`: every orientation has an
  oriented simplex around `0`.

## Implementation notes

The vector bundle is a Mathlib topological vector bundle `Bundle.VectorBundle ℂ F E` over `X`
with finite-dimensional model fibre `F` (rank `r = dim F`), with total space
`Bundle.TotalSpace F E`. Fibres are assumed to be additive groups (as every module over a ring
is), so that they are real vector spaces through `ℝ ⊆ ℂ`.

The orientation of a fibre `E_x` is named through a complex frame `ψ : ℂ^r ≅ E_x`: the oriented
simplices around `0` in `E_x` are the images under `ψ` of those of `ℂ^r` for the basis
`e₁, i e₁, …, e_r, i e_r` (`MMP.ThomClass.complexOrientationBasis`). The Thom-class
condition is imposed for every frame and every such simplex. Since the complex orientation does
not depend on the frame and any two oriented simplices around `0` are homologous in
`(E_x, E_x - 0)`, this is the condition `⟨u, μ_{E_x}⟩ = 1` of Milnor–Stasheff.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [J. Milnor, J. Stasheff, *Characteristic classes*][milnorstasheff1974], §§9–10.
* [A. Dold, *Lectures on Algebraic Topology*][dold1995], VIII.2.
-/

@[expose] public noncomputable section

open Finsupp Set Bundle

universe u

namespace MMP

namespace SingularCochain

open SingularChain

variable {R : Type*} [CommRing R] {Y : Type*} [TopologicalSpace Y]

/-- A cochain vanishing on the simplices of `A` vanishes on every chain of simplices of `A`. -/
lemma eval_eq_zero_of_mem_vanishing {n : ℕ} {A : Set Y} {φ : Simplex Y n → R}
    (hφ : φ ∈ vanishing R n A) {c : Chain R Y n} (hc : c ∈ inside R n A) : eval φ c = 0 := by
  rw [linearCombination_apply, Finsupp.sum]
  refine Finset.sum_eq_zero fun σ hσ ↦ ?_
  rw [hφ σ ((mem_supported R c).1 hc hσ), smul_zero]

/-- A chain whose boundary lies in `A` is annihilated by the relative coboundaries `B^n(Y, A)`:
`⟨δ β, c⟩ = ⟨β, ∂ c⟩ = 0` for `β` vanishing on `A`. -/
lemma eval_eq_zero_of_mem_relCoboundaries {m : ℕ} {A : Set Y} {c : Chain R Y (m + 1)}
    (hc : bd R m c ∈ inside R m A) {φ : Simplex Y (m + 1) → R}
    (hφ : φ ∈ relCoboundaries R A (m + 1)) : eval φ c = 0 := by
  obtain ⟨β, hβ, rfl⟩ := hφ
  rw [eval_coboundary]
  exact eval_eq_zero_of_mem_vanishing hβ hc

/-- In degree `0` there are no relative coboundaries. -/
lemma eval_eq_zero_of_mem_relCoboundaries_zero {A : Set Y} (c : Chain R Y 0)
    {φ : Simplex Y 0 → R} (hφ : φ ∈ relCoboundaries R A 0) : eval φ c = 0 := by
  rw [show φ = 0 from (Submodule.mem_bot R).1 hφ]
  simp

/-- Evaluation `φ ↦ ⟨φ, c⟩` of cochains on a chain `c`, as a linear map. -/
def evalAt {n : ℕ} (c : Chain R Y n) : (Simplex Y n → R) →ₗ[R] R where
  toFun φ := eval φ c
  map_add' φ ψ := by simp [linearCombination_apply, mul_add, Finsupp.sum_add]
  map_smul' a φ := by simp [linearCombination_apply, Finsupp.mul_sum, mul_left_comm]

/-- `evalAt c` sends a cochain `φ` to `⟨φ, c⟩`. -/
lemma evalAt_apply {n : ℕ} (c : Chain R Y n) (φ : Simplex Y n → R) : evalAt c φ = eval φ c :=
  rfl

/-- The Kronecker pairing `⟨-, c⟩ : H^n(Y, A) → R` with a chain `c` annihilated by the relative
coboundaries (a *relative cycle*): the evaluation of a relative cocycle on `c`. -/
def relEval {A : Set Y} {n : ℕ} (c : Chain R Y n)
    (hc : ∀ φ ∈ relCoboundaries R A n, eval φ c = 0) : relCohomology R A n →ₗ[R] R :=
  Submodule.liftQ _ (evalAt c ∘ₗ (relCocycles R A n).subtype) fun x hx ↦
    LinearMap.mem_ker.2 (hc x.1 hx)

/-- The pairing `⟨-, c⟩` sends the class of a relative cocycle `φ` to `⟨φ, c⟩`. -/
@[simp]
lemma relEval_mk {A : Set Y} {n : ℕ} (c : Chain R Y n)
    (hc : ∀ φ ∈ relCoboundaries R A n, eval φ c = 0) (φ : relCocycles R A n) :
    relEval c hc (Submodule.Quotient.mk φ) = eval φ.1 c :=
  rfl

/-- A singular simplex all of whose points on the boundary of `Δⁿ` (some barycentric coordinate
`0`) lie in `A` is a relative cycle of `(Y, A)`. -/
lemma eval_single_eq_zero_of_mem_relCoboundaries {A : Set Y} {n : ℕ} (σ : Simplex Y n)
    (hσ : ∀ t : stdSimplex ℝ (Fin (n + 1)), (∃ i, t i = 0) → σ t ∈ A) :
    ∀ φ ∈ relCoboundaries R A n, eval φ (single σ 1) = 0 := by
  cases n with
  | zero => exact fun φ hφ ↦ eval_eq_zero_of_mem_relCoboundaries_zero _ hφ
  | succ m =>
    refine fun φ hφ ↦ eval_eq_zero_of_mem_relCoboundaries ?_ hφ
    rw [bd_single]
    refine Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ ?_
    refine single_mem_supported R _ ?_
    rintro _ ⟨t, rfl⟩
    refine hσ _ ⟨i, ?_⟩
    change (stdSimplex.map i.succAbove t : Fin (m + 2) → ℝ) i = 0
    rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
    refine Finset.sum_eq_zero fun k hk ↦ ?_
    exact absurd (Finset.mem_filter.1 hk).2 (Fin.succAbove_ne i k)

end SingularCochain

namespace ThomClass

open SingularChain SingularCochain

section Affine

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [ContinuousAdd V]
  [ContinuousSMul ℝ V]

/-- The affine singular simplex `t ↦ ∑ k, t k • v k` with vertices `v₀, …, vₙ`. -/
def affineSimplex {n : ℕ} (v : Fin (n + 1) → V) : Simplex V n :=
  ⟨fun t ↦ ∑ k, (t : Fin (n + 1) → ℝ) k • v k,
    continuous_finsetSum _ fun k _ ↦
      ((continuous_apply k).comp continuous_subtype_val).smul continuous_const⟩

/-- The affine simplex with vertices `v` sends `t` to `∑ k, t k • v k`. -/
lemma affineSimplex_apply {n : ℕ} (v : Fin (n + 1) → V) (t : stdSimplex ℝ (Fin (n + 1))) :
    affineSimplex v t = ∑ k, (t : Fin (n + 1) → ℝ) k • v k :=
  rfl

end Affine

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The vertices `v₀, …, vₙ` span an *oriented simplex around `0`* for the orientation of the
basis `b` of the real vector space `V`: `0` is in the interior of their convex hull, and the
basis `v₁ - v₀, …, vₙ - v₀` defines the orientation of `b` (positive determinant). The affine
simplex with these vertices represents the orientation generator `μ ∈ H_n(V, V - 0)`. -/
def IsOrientedSimplexAroundZero {n : ℕ} (b : Module.Basis (Fin n) ℝ V) (v : Fin (n + 1) → V) :
    Prop :=
  (∃ t : Fin (n + 1) → ℝ, (∀ k, 0 < t k) ∧ ∑ k, t k = 1 ∧ ∑ k, t k • v k = 0) ∧
    0 < b.det fun k ↦ v k.succ - v 0

namespace IsOrientedSimplexAroundZero

variable {n : ℕ} {b : Module.Basis (Fin n) ℝ V} {v : Fin (n + 1) → V}

/-- The vertices of an oriented simplex are affinely independent: `∑ cₖ vₖ = 0` with
`∑ cₖ = 0` forces `c = 0`. -/
lemma eq_zero_of_sum_eq_zero (h : IsOrientedSimplexAroundZero b v) {c : Fin (n + 1) → ℝ}
    (hc : ∑ k, c k = 0) (hcv : ∑ k, c k • v k = 0) : c = 0 := by
  have hli : LinearIndependent ℝ fun k : Fin n ↦ v k.succ - v 0 :=
    (b.is_basis_iff_det.2 (isUnit_iff_ne_zero.2 h.2.ne')).1
  rw [Fin.sum_univ_succ] at hc hcv
  have hsum : ∑ k : Fin n, c k.succ • (v k.succ - v 0) = 0 := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul]
    have : c 0 = -∑ k : Fin n, c k.succ := by linarith
    rw [this, neg_smul] at hcv
    rw [sub_eq_zero]
    linear_combination (norm := module) hcv
  have hs := Fintype.linearIndependent_iff.1 hli _ hsum
  funext k
  refine Fin.cases ?_ (fun k ↦ hs k) k
  simpa [hs] using hc

/-- A point on the boundary of an oriented simplex around `0` (some barycentric coordinate `0`)
is not `0`. -/
lemma sum_smul_ne_zero (h : IsOrientedSimplexAroundZero b v) (t : stdSimplex ℝ (Fin (n + 1)))
    {i : Fin (n + 1)} (hi : t i = 0) : ∑ k, (t : Fin (n + 1) → ℝ) k • v k ≠ 0 := by
  intro ht
  obtain ⟨s, hs, hs1, hsv⟩ := h.1
  have := congrFun (h.eq_zero_of_sum_eq_zero (c := s - t)
    (by simp [Finset.sum_sub_distrib, hs1, stdSimplex.sum_eq_one t])
    (by simp [sub_smul, Finset.sum_sub_distrib, hsv, ht])) i
  have := hs i
  simp_all

/-- The faces of an oriented simplex around `0` avoid `0`. -/
lemma affineSimplex_ne_zero [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul ℝ V]
    (h : IsOrientedSimplexAroundZero b v) (t : stdSimplex ℝ (Fin (n + 1))) (ht : ∃ i, t i = 0) :
    affineSimplex v t ≠ 0 :=
  ht.elim fun _ hi ↦ h.sum_smul_ne_zero t hi

end IsOrientedSimplexAroundZero

/-- Every orientation has an oriented simplex around `0`: for a basis `b₁, …, bₙ`, the vertices
`-(b₁ + ⋯ + bₙ), b₁, …, bₙ`. -/
lemma exists_isOrientedSimplexAroundZero {n : ℕ} (b : Module.Basis (Fin n) ℝ V) :
    ∃ v, IsOrientedSimplexAroundZero b v := by
  refine ⟨Fin.cons (-∑ j, b j) b, ⟨fun _ ↦ 1 / (n + 1), fun _ ↦ by positivity, ?_, ?_⟩, ?_⟩
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  · rw [Fin.sum_univ_succ]
    simp [← Finset.smul_sum]
  · have : (fun k : Fin n ↦ (Fin.cons (-∑ j, b j) b : Fin (n + 1) → V) k.succ -
        (Fin.cons (-∑ j, b j) b : Fin (n + 1) → V) 0) = fun k ↦ b k + ∑ j, b j := by
      funext k
      simp
    rw [this, Module.Basis.det_apply]
    have hm : b.toMatrix (fun k ↦ b k + ∑ j, b j) =
        (1 : Matrix (Fin n) (Fin n) ℝ) +
          Matrix.replicateCol Unit (fun _ : Fin n ↦ (1 : ℝ)) *
            Matrix.replicateRow Unit (fun _ : Fin n ↦ (1 : ℝ)) := by
      ext i k
      simp [Module.Basis.toMatrix_apply, Matrix.one_apply, Finsupp.single_apply, eq_comm,
        Matrix.mul_apply]
    rw [hm, Matrix.det_one_add_replicateCol_mul_replicateRow]
    simp only [dotProduct, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    positivity

/-- The real basis `e₁, i e₁, e₂, i e₂, …, e_r, i e_r` of `ℂ^r` attached to its standard complex
basis `e`: it defines the orientation of `ℂ^r` given by its complex structure. -/
def complexOrientationBasis (r : ℕ) : Module.Basis (Fin (2 * r)) ℝ (Fin r → ℂ) :=
  (Complex.basisOneI.smulTower (Pi.basisFun ℂ (Fin r))).reindex
    ((Equiv.prodComm (Fin 2) (Fin r)).trans (finProdFinEquiv.trans (finCongr (Nat.mul_comm r 2))))

/-- The `(2j + b)`-th vector of `complexOrientationBasis r` is `eⱼ` for `b = 0` and `i eⱼ` for
`b = 1`. -/
lemma complexOrientationBasis_apply (r : ℕ) (j : Fin r) (b : Fin 2) :
    complexOrientationBasis r (finCongr (Nat.mul_comm r 2) (finProdFinEquiv (j, b))) =
      Complex.basisOneI b • Pi.basisFun ℂ (Fin r) j := by
  simp [complexOrientationBasis, Module.Basis.smulTower_apply]

section Bundle

variable {B : Type u} [TopologicalSpace B] (F : Type*) [NormedAddCommGroup F]
  {E : B → Type u} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]

/-- The affine simplex with vertices `v` in `ℂ^r`, carried into the fibre `E_x` of a vector
bundle by a complex frame `ψ : ℂ^r ≅ E_x`, as a singular simplex of the total space. -/
def fibreSimplex {r : ℕ} (x : B) (ψ : (Fin r → ℂ) ≃L[ℂ] E x) {n : ℕ}
    (v : Fin (n + 1) → (Fin r → ℂ)) : Simplex (TotalSpace F E) n :=
  (⟨TotalSpace.mk x, FiberBundle.continuous_totalSpaceMk F E x⟩ : C(E x, TotalSpace F E)).comp
    ((ψ : C(Fin r → ℂ, E x)).comp (affineSimplex v))

/-- The fibre simplex sends `t` to the point `ψ (∑ k, t k • v k)` of the fibre `E_x`. -/
lemma fibreSimplex_apply {r : ℕ} (x : B) (ψ : (Fin r → ℂ) ≃L[ℂ] E x) {n : ℕ}
    (v : Fin (n + 1) → (Fin r → ℂ)) (t : stdSimplex ℝ (Fin (n + 1))) :
    fibreSimplex F x ψ v t = TotalSpace.mk x (ψ (affineSimplex v t)) :=
  rfl

/-- The boundary of an oriented simplex around `0` in a fibre avoids the zero section. -/
lemma fibreSimplex_notMem_range_zeroSection {r : ℕ} (x : B) (ψ : (Fin r → ℂ) ≃L[ℂ] E x)
    {n : ℕ} {b : Module.Basis (Fin n) ℝ (Fin r → ℂ)} {v : Fin (n + 1) → (Fin r → ℂ)}
    (hv : IsOrientedSimplexAroundZero b v) (t : stdSimplex ℝ (Fin (n + 1))) (ht : ∃ i, t i = 0) :
    fibreSimplex F x ψ v t ∈ (range (zeroSection F E))ᶜ := by
  rintro ⟨y, hy⟩
  have hyx : y = x := congrArg TotalSpace.proj hy
  subst hyx
  rw [fibreSimplex_apply, zeroSection, TotalSpace.mk_inj] at hy
  exact hv.affineSimplex_ne_zero t ht (ψ.map_eq_zero_iff.1 hy.symm)

end Bundle

end ThomClass

section Bundle

open ThomClass SingularChain SingularCochain

variable {R : Type u} [CommRing R] {B : Type u} [TopologicalSpace B]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  (E : B → Type u) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [_root_.VectorBundle ℂ F E]

/-- A *Thom class* of a complex topological vector bundle `E` of rank `r = dim F` on `X`
(Fulton, §19.1; Milnor–Stasheff, §9): a class `u ∈ H^{2r}(E, E - 0_E; R)` whose restriction to
every fibre `(E_x, E_x - 0)` is the generator of the orientation given by the complex
structure, i.e. `⟨u, μ_{E_x}⟩ = 1`, where `μ_{E_x} ∈ H_{2r}(E_x, E_x - 0)` is represented by any
simplex around `0` oriented by `ψ(e₁), ψ(i e₁), …, ψ(e_r), ψ(i e_r)` for a complex frame
`ψ : ℂ^r ≅ E_x`. By Thom's theorem (Milnor–Stasheff, Thm. 10.4) there is exactly one, the Thom
class `u_E` (`MMP.ThomClass.thomClass`). -/
def IsThomClass (u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace F E))
    (range (zeroSection F E)) (2 * Module.finrank ℂ F : ℕ)) : Prop :=
  ∀ (x : B) (ψ : (Fin (Module.finrank ℂ F) → ℂ) ≃L[ℂ] E x)
    (v : Fin (2 * Module.finrank ℂ F + 1) → (Fin (Module.finrank ℂ F) → ℂ))
    (hv : IsOrientedSimplexAroundZero (complexOrientationBasis (Module.finrank ℂ F)) v),
    relEval (R := R) (single (fibreSimplex F x ψ v) 1)
      (eval_single_eq_zero_of_mem_relCoboundaries _
        (fibreSimplex_notMem_range_zeroSection F x ψ hv))
      (relativeSingularCohomologyEquiv R (Y := TopCat.of (TotalSpace F E)) _ _ u) = 1

end Bundle

end MMP
