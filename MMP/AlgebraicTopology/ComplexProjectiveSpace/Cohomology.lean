module

public import MMP.AlgebraicTopology.SingularCohomology.PairSequence.Supports
public import MMP.AlgebraicTopology.SingularCohomology.Relative.Excision
public import MMP.AlgebraicTopology.SingularCohomology.Relative.Homotopy
public import MMP.AlgebraicTopology.PoincareDuality.LocalGenerator
public import MMP.AlgebraicTopology.PoincareDuality.DetectingCocycle
public import MMP.AlgebraicTopology.ThomClass.Natural
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Homotopy.TopCat.Basic
public import MMP.AlgebraicTopology.ThomClass.DirectSumEuclidean
public import MMP.AlgebraicTopology.OrientationClass.CupCompositeNaturality
public import MMP.AlgebraicTopology.ThomClass.Isomorphism.Trivial
public import MMP.AlgebraicTopology.SingularCohomology.EvenRing

/-!
# The cohomology of complex projective space

Complex projective space `ℙⁿ(ℂ)` is built from one cell in each even real dimension
`0, 2, …, 2n`: removing the point `p = [0 : ⋯ : 0 : 1]` from `ℙⁿ⁺¹(ℂ)` leaves a space which
deformation retracts onto the hyperplane `ℙⁿ(ℂ) = {x_{n+1} = 0}` along `[x : z] ↦ [x : t z]`, and
`p` has the Euclidean neighbourhood `{x_{n+1} ≠ 0} ≅ ℂⁿ⁺¹`. The long exact sequence of the pair
`(ℙⁿ⁺¹, ℙⁿ⁺¹ - p)`, excision of the complement of that neighbourhood, and the local cohomology
`H^k(ℝᵐ, ℝᵐ - 0; K)` (which is `K` for `k = m` and `0` otherwise) give, by induction on `n`, the
singular cohomology with coefficients in a field `K`:
`H^k(ℙⁿ(ℂ); K) ≅ K` for `k` even with `0 ≤ k ≤ 2n`, and `H^k(ℙⁿ(ℂ); K) = 0` otherwise.

The cup powers of any nonzero `x ∈ H²(ℙⁿ(ℂ); K)` (for instance the hyperplane class) span the
even cohomology: `x^{k+1} ≠ 0` for `k < n`, so `x^{k+1}` spans `H^{2k+2}(ℙⁿ(ℂ); K)`. Restriction
to a hyperplane is an isomorphism on `H²`, and restriction to a linear subspace commutes with
cup powers, so it suffices that `x^{m+1} ≠ 0` on `ℙᵐ⁺¹(ℂ)`. This is proved by induction on `m`
(Hatcher, Theorem 3.12), with `E = ℙᵐ⁺²(ℂ) - p` the tubular neighbourhood of the hyperplane
`H = ℙᵐ⁺¹(ℂ)` retracting onto it along `r`. The class `x` lifts to `v ∈ H²(ℙᵐ⁺², ℙᵐ⁺² - H)`
(the complement of `H` is a cell); by induction `(x|_H)^{m+1}` lifts to a class `z` supported at
a point `q ∈ H`, and `x^{m+1}|_E = r^*(x|_H)^{m+1}`. So `x^{m+2}` is the image of `r^* z ∪ v|_E`,
a class supported at the point `q`, under excision and the top-degree isomorphism
`H^{2m+4}(ℙᵐ⁺², ℙᵐ⁺² - q) ≅ H^{2m+4}(ℙᵐ⁺²)`. In the chart `(u, t) ↦ [u : 1 : t]` of `E` around
`q`, `r^* z` and `v|_E` become `pr₁^* a` and `pr₂^* b` for nonzero local classes
`a ∈ H^{2m+2}(ℂᵐ⁺¹, ℂᵐ⁺¹ - 0)` and `b ∈ H²(ℂ, ℂ - 0)` (for `b`, by the homotopy
`(τ, (u, t)) ↦ [τ u : 1 : t]` and the restriction of `x` to the line through `q` and `p`), and
`pr₁^* a ∪ pr₂^* b ≠ 0` is the product formula for the Thom classes of Euclidean spaces.

## Main definitions

* `MMP.Topology.lineProjection`: the matrix `v v^* / (v^* v)` of the projection onto `ℂ v`.
* `MMP.Topology.complexProjectiveSpace n`: `ℙⁿ(ℂ)`, as the space of these matrices for
  `v ∈ ℂⁿ⁺¹ - 0`.
* `MMP.Topology.projectiveSpaceCellHomeomorph`: the cell `{x_{n+1} ≠ 0} ≅ ℝ^{2n+2}` of `ℙⁿ⁺¹(ℂ)`.
* `MMP.Topology.hyperplaneInclusion`, `MMP.Topology.hyperplaneRetraction`,
  `MMP.Topology.hyperplaneHomotopy`: the homotopy equivalence `ℙⁿ⁺¹(ℂ) - p ≃ ℙⁿ(ℂ)`.
* `MMP.Topology.cohomologyWithSupportsEuclideanEquiv`: `H^m(ℝᵐ, ℝᵐ - 0; K) ≅ K`.
* `MMP.Topology.relativeSingularCohomologyIsoOfIso`, `MMP.Topology.cohomologyIsoOfHomotopy`:
  invariance of singular cohomology under homeomorphisms and homotopy equivalences.
* `MMP.Topology.cupPowSucc K x k`: the cup power `x^{k+1} ∈ H^{2k+2}(Y; K)` of `x ∈ H²(Y; K)`.
* `MMP.Topology.permHomeomorph`: the permutations of the homogeneous coordinates of `ℙⁿ(ℂ)`.
* `MMP.Topology.hyperplaneEmbedding`, `MMP.Topology.linearSubspaceEmbedding`,
  `MMP.Topology.lineEmbedding`, `MMP.Topology.lastLine`: inclusions of linear subspaces.
* `MMP.Topology.affineChartMap`, `MMP.Topology.complChart`: affine charts `u ↦ [u : 1]` of
  `ℙⁿ⁺¹(ℂ)` and `(u, t) ↦ [u : 1 : t]` of `ℙᵐ⁺²(ℂ) - [0 : ⋯ : 0 : 1]`.

## Main results

* `MMP.Topology.mem_relCoboundaries_of_forall_eval_eq_zero`: over a field, a relative cochain
  vanishing on all relative cycles is a relative coboundary.
* `MMP.Topology.subsingleton_cohomologyWithSupports_euclidean`: `H^k(ℝᵐ, ℝᵐ - 0; K) = 0` for
  `k ≠ m`.
* `MMP.Topology.bijective_restrictCompl_singleton`,
  `MMP.Topology.subsingleton_cohomology_of_compl_singleton`,
  `MMP.Topology.nonempty_cohomology_equiv_of_compl_singleton`: the cohomology of a space `Y`
  from that of `Y - p`, for a closed point `p` with a Euclidean neighbourhood `ℝᵐ⁺¹`.
* `MMP.Topology.cohomology_complexProjectiveSpace`: the cohomology of `ℙⁿ(ℂ)`, with the
  corollaries `nonempty_cohomology_complexProjectiveSpace_equiv` (`H^{2k} ≅ K`, `k ≤ n`),
  `subsingleton_cohomology_complexProjectiveSpace_of_odd`,
  `subsingleton_cohomology_complexProjectiveSpace_of_lt` and
  `finrank_cohomology_complexProjectiveSpace` (the Betti numbers).
* `MMP.Topology.cup_pullback_fst_snd_ne_zero`: `pr₁^* a ∪ pr₂^* b ≠ 0` for nonzero local classes
  `a`, `b` of `ℂᴿ`, `ℂˢ` at `0`.
* `MMP.Topology.map_cupPowSucc`: cup powers commute with pull-back.
* `MMP.Topology.cupPowSucc_ne_zero`: `x^{k+1} ≠ 0` in `H^{2k+2}(ℙⁿ(ℂ); K)` for `x ≠ 0` and `k < n`.
* `MMP.Topology.span_cupPowSucc_eq_top`, `MMP.Topology.exists_smul_cupPowSucc_eq`: `x^{k+1}`
  spans `H^{2k+2}(ℙⁿ(ℂ); K)`.
* `MMP.Topology.pow_succ_ne_zero_iff`: in the even cohomology ring `H^{ev}(ℙⁿ(ℂ); K)`,
  `ξ^{k+1} ≠ 0` iff `k < n`, for `ξ ∈ H²` nonzero.
* `MMP.Topology.bijective_map_hyperplaneEmbedding_two`: restriction to a hyperplane is bijective
  on `H²`.

## Implementation notes

* Cohomology is singular cohomology with coefficients in a field `K`, as
  `MMP.cohomologyWithSupports K (ModuleCat.of K K) Y Set.univ k`; for `K = ℚ` this
  is `MMP.Fourfold.rationalCohomology Y k`.
* `ℙⁿ(ℂ)` is realized inside the matrices `Fin (n + 1) → Fin (n + 1) → ℂ`, a line being
  represented by its orthogonal projection, so that it carries the subspace topology and every
  map in and out of it is given by a formula; this avoids quotient topologies. The base point
  and the cell use the last coordinate, `Fin.last`, and the hyperplane the first `n + 1`
  coordinates, `Fin.castSucc`.
* Over a field the cohomology of a complex of free modules is the dual of its homology, which is
  how the local homology of `(ℝᵐ, ℝᵐ - 0)` computed in this library gives its
  cohomology.
* The generator statements are made for every nonzero `x ∈ H²(ℙⁿ(ℂ); K)` rather than for a
  chosen hyperplane class: over a field `H²` is a line, so any nonzero class, in particular any
  normalisation of the hyperplane class, generates.

## References

* [A. Hatcher, *Algebraic Topology*][hatcher2002], §2.2 (Example 2.23) and §3.1.
-/

@[expose] public noncomputable section

open Set Finsupp MMP SingularChain SingularCochain

namespace MMP.Topology

/-! ### Relative cochains with coefficients in a field -/

section Field

variable {K : Type*} [Field K] {Y : Type*} [TopologicalSpace Y]

/-- Over a field, a relative `(m + 1)`-cochain of `(Y, A)` which vanishes on every relative
cycle is a relative coboundary. -/
theorem mem_relCoboundaries_of_forall_eval_eq_zero (A : Set Y) (m : ℕ)
    {φ : Simplex Y (m + 1) → K}
    (h : ∀ c : Chain K Y (m + 1), bd K m c ∈ inside K m A → eval φ c = 0) :
    φ ∈ relCoboundaries K A (m + 1) := by
  classical
  let F : Chain K Y (m + 1) →ₗ[K] Chain K Y m ⧸ inside K m A := (inside K m A).mkQ ∘ₗ bd K m
  have hker : LinearMap.ker F ≤ LinearMap.ker (eval φ) := fun c hc ↦ by
    refine h c ?_
    simpa [F, Submodule.Quotient.mk_eq_zero] using hc
  let f₀ : LinearMap.range F →ₗ[K] K :=
    (LinearMap.ker F).liftQ (eval φ) hker ∘ₗ F.quotKerEquivRange.symm.toLinearMap
  obtain ⟨g, hg⟩ := LinearMap.exists_extend f₀
  have hgF : ∀ c, g (F c) = eval φ c := fun c ↦ by
    have := LinearMap.congr_fun hg ⟨F c, LinearMap.mem_range_self F c⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at this
    rw [this]
    simp only [f₀, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    rw [LinearMap.quotKerEquivRange_symm_apply_image F c]
    rfl
  refine ⟨fun σ ↦ g ((inside K m A).mkQ (single σ 1)), fun σ hσ ↦ ?_, ?_⟩
  · have hs : single σ (1 : K) ∈ inside K m A :=
      Finsupp.single_mem_supported K (1 : K) (show σ ∈ {σ : Simplex Y m | Set.range σ ⊆ A} from hσ)
    change g ((inside K m A).mkQ (single σ 1)) = 0
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 hs, map_zero]
  · ext σ
    rw [coboundary_apply]
    have := hgF (single σ 1)
    simp only [F, LinearMap.comp_apply, bd_single, map_sum, map_smul] at this
    simp only [eval, linearCombination_single, one_smul] at this
    rw [← this]
    simp [smul_eq_mul]

/-- A relative cocycle vanishes on a relative boundary `∂ w + a`, `a` a chain of `A`. -/
lemma eval_eq_zero_of_mem_relCocycles {A : Set Y} {m : ℕ} {φ : Simplex Y (m + 1) → K}
    (hφ : φ ∈ relCocycles K A (m + 1)) {c : Chain K Y (m + 1)} (w : Chain K Y (m + 2))
    (hw : c - bd K (m + 1) w ∈ inside K (m + 1) A) : eval φ c = 0 := by
  have h1 : eval φ (bd K (m + 1) w) = 0 := by
    rw [← eval_coboundary, show coboundary K (m + 1) φ = 0 from hφ.2]
    simp
  have h2 := eval_eq_zero_of_mem_vanishing hφ.1 hw
  rw [map_sub, h1, sub_zero] at h2
  exact h2

/-- Over a field, the relative cohomology `H^{m+1}(Y, A; K)` vanishes when the relative homology
`H_{m+1}(Y, A; K)` does. -/
theorem subsingleton_relCohomology_succ (A : Set Y) (m : ℕ)
    (h : ∀ c : Chain K Y (m + 1), bd K m c ∈ inside K m A →
      ∃ w : Chain K Y (m + 2), c - bd K (m + 1) w ∈ inside K (m + 1) A) :
    Subsingleton (relCohomology K A (m + 1)) := by
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨φ, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  refine mem_relCoboundaries_of_forall_eval_eq_zero A m fun c hc ↦ ?_
  obtain ⟨w, hw⟩ := h c hc
  exact eval_eq_zero_of_mem_relCocycles φ.2 w hw

/-- The relative cohomology `H^0(Y, A; K)` vanishes when `H_0(Y, A; K)` does. -/
theorem subsingleton_relCohomology_zero (A : Set Y)
    (h : ∀ c : Chain K Y 0, ∃ w : Chain K Y 1, c - bd K 0 w ∈ inside K 0 A) :
    Subsingleton (relCohomology K A 0) := by
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨φ, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  change (φ : Simplex Y 0 → K) ∈ (⊥ : Submodule K _)
  rw [Submodule.mem_bot]
  ext σ
  obtain ⟨w, hw⟩ := h (single σ 1)
  have h1 : eval (φ : Simplex Y 0 → K) (bd K 0 w) = 0 := by
    rw [← eval_coboundary, show coboundary K 0 (φ : Simplex Y 0 → K) = 0 from φ.2.2]
    simp
  have h2 := eval_eq_zero_of_mem_vanishing φ.2.1 hw
  rw [map_sub, h1, sub_zero] at h2
  simpa [linearCombination_single] using h2

/-- Over a field, if the relative homology of `(Y, A)` vanishes below degree `m + 1` and
`H_{m+1}(Y, A; K)` is free of rank one on the class of the relative cycle `c₀`, the Kronecker
pairing with `c₀` identifies `H^{m+1}(Y, A; K)` with `K`. -/
def relCohomologyEquivOfGenerator (A : Set Y) (m : ℕ)
    (h0 : ∀ c : Chain K Y 0, ∃ w : Chain K Y 1, c - bd K 0 w ∈ inside K 0 A)
    (hlow : ∀ k, k + 1 < m + 1 → ∀ c : Chain K Y (k + 1), bd K k c ∈ inside K k A →
      ∃ w : Chain K Y (k + 2), c - bd K (k + 1) w ∈ inside K (k + 1) A)
    (c₀ : Chain K Y (m + 1)) (hc₀ : bd K m c₀ ∈ inside K m A)
    (hgen : ∀ c : Chain K Y (m + 1), bd K m c ∈ inside K m A →
      ∃ r : K, ∃ w : Chain K Y (m + 2), c - r • c₀ - bd K (m + 1) w ∈ inside K (m + 1) A)
    (hfree : ∀ r : K, (∃ w : Chain K Y (m + 2), r • c₀ - bd K (m + 1) w ∈ inside K (m + 1) A) →
      r = 0) :
    relCohomology K A (m + 1) ≃ₗ[K] K :=
  LinearEquiv.ofBijective (relEval c₀ fun _ hφ ↦ eval_eq_zero_of_mem_relCoboundaries hc₀ hφ) (by
    refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun r ↦ ?_⟩
    · obtain ⟨φ, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [relEval_mk] at hx
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      refine mem_relCoboundaries_of_forall_eval_eq_zero A m fun c hc ↦ ?_
      obtain ⟨s, w, hw⟩ := hgen c hc
      have := eval_eq_zero_of_mem_relCocycles φ.2 w (c := c - s • c₀) (by simpa using hw)
      rwa [map_sub, map_smul, hx, smul_zero, sub_zero] at this
    · obtain ⟨φ, hφ, h1⟩ := exists_mem_relCocycles_eval_eq_one A m h0 hlow c₀ hc₀ hgen hfree
      refine ⟨Submodule.Quotient.mk ⟨r • φ, Submodule.smul_mem _ r hφ⟩, ?_⟩
      rw [relEval_mk]
      change evalAt c₀ (r • φ) = r
      rw [map_smul, evalAt_apply, h1, smul_eq_mul, mul_one])

end Field

/-! ### Transport along homeomorphisms and homotopy equivalences -/

section Transport

open CategoryTheory

variable (K : Type) [Field K]

/-- The maps of relative singular cohomology induced by `f` and by `g` compose to the map
induced by `g ≫ f`. -/
lemma relativeSingularCohomology_map_comp_map {Y'' Y' Y : TopCat.{0}} (g : Y'' ⟶ Y')
    (f : Y' ⟶ Y) {A'' : Set Y''} {A' : Set Y'} {A : Set Y} (hf : A' ⊆ f ⁻¹' A)
    (hg : A'' ⊆ g ⁻¹' A') (h : A'' ⊆ (g ≫ f) ⁻¹' A) (j : ℤ) :
    relativeSingularCohomology.map K (ModuleCat.of K K) f hf j ≫
        relativeSingularCohomology.map K (ModuleCat.of K K) g hg j =
      relativeSingularCohomology.map K (ModuleCat.of K K) (g ≫ f) h j :=
  (relativeSingularCohomology.map_comp K _ g f hg hf j).symm

/-- A map of pairs equal to the identity induces the identity on relative singular cohomology. -/
lemma relativeSingularCohomology_map_eq_id {Y : TopCat.{0}} {f : Y ⟶ Y} (hf : f = 𝟙 Y)
    {A : Set Y} (h : A ⊆ f ⁻¹' A) (j : ℤ) :
    relativeSingularCohomology.map K (ModuleCat.of K K) f h j = 𝟙 _ := by
  subst hf
  exact relativeSingularCohomology.map_id _ _ _ _ _

/-- A homeomorphism `e : Y' ≅ Y` identifies `H^j(Y, A; K)` with `H^j(Y', e⁻¹ A; K)`. -/
def relativeSingularCohomologyIsoOfIso {Y' Y : TopCat.{0}} (e : Y' ≅ Y) (A : Set Y) (j : ℤ) :
    relativeSingularCohomology K (ModuleCat.of K K) Y A j ≅
      relativeSingularCohomology K (ModuleCat.of K K) Y' (e.hom ⁻¹' A) j where
  hom := relativeSingularCohomology.map K _ e.hom subset_rfl j
  inv := relativeSingularCohomology.map K _ e.inv
    (show A ⊆ e.inv ⁻¹' (e.hom ⁻¹' A) from fun x hx ↦ by
      change (e.inv ≫ e.hom) x ∈ A
      rwa [e.inv_hom_id, TopCat.id_app]) j
  hom_inv_id := by
    rw [relativeSingularCohomology_map_comp_map K _ _ _ _ (by
      intro x hx
      change (e.inv ≫ e.hom) x ∈ A
      rwa [e.inv_hom_id, TopCat.id_app])]
    exact relativeSingularCohomology_map_eq_id K e.inv_hom_id _ j
  inv_hom_id := by
    rw [relativeSingularCohomology_map_comp_map K _ _ _ _ (by
      intro x hx
      change (e.hom ≫ e.inv) x ∈ e.hom ⁻¹' A
      rwa [e.hom_inv_id, TopCat.id_app])]
    exact relativeSingularCohomology_map_eq_id K e.hom_inv_id _ j

/-- The empty set `univᶜ` is contained in the preimage of `univᶜ` under any map. -/
lemma compl_univ_subset_preimage {Y' Y : TopCat.{0}} (f : Y' ⟶ Y) :
    (Set.univ : Set Y')ᶜ ⊆ f ⁻¹' (Set.univ : Set Y)ᶜ :=
  fun x hx ↦ absurd (Set.mem_univ x) hx

/-- A homotopy equivalence `i : Z ⟶ W`, with homotopy inverse `r` such that `i ≫ r = 𝟙 Z`,
identifies the singular cohomology of `W` and of `Z`. -/
def cohomologyIsoOfHomotopy {Z W : TopCat.{0}} (i : Z ⟶ W) (r : W ⟶ Z) (hri : i ≫ r = 𝟙 Z)
    (H : TopCat.Homotopy (r ≫ i) (𝟙 W)) (j : ℤ) :
    cohomologyWithSupports K (ModuleCat.of K K) W Set.univ j ≅
      cohomologyWithSupports K (ModuleCat.of K K) Z Set.univ j where
  hom := relativeSingularCohomology.map K _ i (compl_univ_subset_preimage i) j
  inv := relativeSingularCohomology.map K _ r (compl_univ_subset_preimage r) j
  hom_inv_id := by
    rw [relativeSingularCohomology_map_comp_map K _ _ _ _ (compl_univ_subset_preimage _),
      relativeSingularCohomology.map_eq_of_homotopy K H (fun y hy ↦ absurd (Set.mem_univ y) hy)
        _ (compl_univ_subset_preimage _)]
    exact relativeSingularCohomology_map_eq_id K rfl _ j
  inv_hom_id := by
    rw [relativeSingularCohomology_map_comp_map K _ _ _ _ (compl_univ_subset_preimage _)]
    exact relativeSingularCohomology_map_eq_id K hri _ j

end Transport

/-! ### The local cohomology of `ℝᵐ` at the origin, and the cohomology of a point -/

section Local

variable (K : Type) [Field K]

/-- `H^k(ℝᵐ, ℝᵐ - 0; K) = 0` for `k ≠ m`, `m ≥ 1`. -/
theorem subsingleton_cohomologyWithSupports_euclidean {m : ℕ} (hm : 1 ≤ m) {k : ℕ} (hk : k ≠ m) :
    Subsingleton (cohomologyWithSupports K (ModuleCat.of K K) (TopCat.of (Fin m → ℝ)) {0} k) := by
  refine (relativeSingularCohomologyEquiv K (Y := TopCat.of (Fin m → ℝ))
    ({0}ᶜ : Set (Fin m → ℝ)) k).toEquiv.subsingleton_congr.2 ?_
  rcases k with _ | j
  · exact subsingleton_relCohomology_zero _ (isRelBoundary_singleton_zero_zero hm)
  · refine subsingleton_relCohomology_succ _ j fun c hc ↦ ?_
    rcases Nat.lt_or_gt_of_ne hk with h | h
    · exact relVanishing_singleton_zero_low m j h c hc
    · have := relVanishing_Icc (R := K) cycleVanishing_compl_zero m 0 0 j (by omega)
      rw [Set.Icc_self] at this
      exact this c hc

/-- `H^m(ℝᵐ, ℝᵐ - 0; K) ≅ K`, `m ≥ 1`, through the Kronecker pairing with an oriented simplex
around `0`. -/
def cohomologyWithSupportsEuclideanEquiv (m : ℕ) :
    cohomologyWithSupports K (ModuleCat.of K K) (TopCat.of (Fin (m + 1) → ℝ)) {0} (m + 1 : ℕ)
      ≃ₗ[K] K :=
  (relativeSingularCohomologyEquiv K (Y := TopCat.of (Fin (m + 1) → ℝ))
    ({0}ᶜ : Set (Fin (m + 1) → ℝ)) (m + 1)).trans
    (relCohomologyEquivOfGenerator _ m (isRelBoundary_singleton_zero_zero (by omega))
      (fun k hk c hc ↦ relVanishing_singleton_zero_low (m + 1) k hk c hc)
      _ (bd_localGenerator_mem m) (exists_sub_smul_localGenerator_mem m)
      (eq_zero_of_smul_localGenerator_mem m))

/-- `H^{k+1}(ℝ⁰; K) = 0`. -/
theorem subsingleton_cohomology_euclideanZero_succ (k : ℕ) :
    Subsingleton (cohomologyWithSupports K (ModuleCat.of K K) (TopCat.of (Fin 0 → ℝ)) Set.univ
      (k + 1 : ℕ)) := by
  refine (relativeSingularCohomologyEquiv K (Y := TopCat.of (Fin 0 → ℝ))
    (Set.univ : Set (Fin 0 → ℝ))ᶜ (k + 1)).toEquiv.subsingleton_congr.2 ?_
  refine subsingleton_relCohomology_succ _ k fun c hc ↦ ?_
  have hc' : bd K k c = 0 := eq_zero_of_mem_inside_empty_set (by rwa [Set.compl_univ] at hc)
  obtain ⟨w, -, hw⟩ := exists_bd_eq_of_starConvex (R := K) (starConvex_univ (0 : Fin 0 → ℝ))
    (mem_inside_univ c) hc'
  exact ⟨w, by rw [hw, sub_self]; exact Submodule.zero_mem _⟩

/-- The singular cohomology of a one-point space vanishes in positive degrees. -/
theorem subsingleton_cohomology_of_unique (Y : TopCat.{0}) [Unique Y] (k : ℕ) :
    Subsingleton (cohomologyWithSupports K (ModuleCat.of K K) Y Set.univ (k + 1 : ℕ)) := by
  let e : Y ≅ TopCat.of (Fin 0 → ℝ) := TopCat.isoOfHomeo (Homeomorph.homeomorphOfUnique _ _)
  have h := (relativeSingularCohomologyIsoOfIso K e (Set.univ : Set (Fin 0 → ℝ))ᶜ
    (k + 1 : ℕ)).toLinearEquiv.toEquiv.subsingleton_congr.1
    (subsingleton_cohomology_euclideanZero_succ K k)
  rwa [Set.preimage_compl, Set.preimage_univ] at h

/-- The singular cohomology `H^0` of a one-point space is `K`, by evaluation at the point. -/
theorem nonempty_cohomology_zero_equiv_of_unique (Y : TopCat.{0}) [Unique Y] :
    Nonempty (cohomologyWithSupports K (ModuleCat.of K K) Y Set.univ (0 : ℕ) ≃ₗ[K] K) := by
  let σ₀ : Simplex Y 0 := ContinuousMap.const _ default
  have hσ : ∀ σ : Simplex Y 0, σ = σ₀ := fun σ ↦ ContinuousMap.ext fun t ↦ Subsingleton.elim _ _
  let Θ : relCohomology K (Set.univ : Set Y)ᶜ 0 →ₗ[K] K :=
    relEval (single σ₀ 1) fun _ hφ ↦ eval_eq_zero_of_mem_relCoboundaries_zero _ hφ
  have hΘ : Function.Bijective Θ := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun r ↦ ?_⟩
    · obtain ⟨φ, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      change (φ : Simplex Y 0 → K) ∈ (⊥ : Submodule K _)
      rw [Submodule.mem_bot]
      ext σ
      rw [hσ σ]
      simpa [Θ, linearCombination_single] using hx
    · have hmem : (fun _ ↦ r : Simplex Y 0 → K) ∈ relCocycles K (Set.univ : Set Y)ᶜ 0 := by
        refine ⟨fun σ hσ' ↦ absurd (hσ' ⟨stdSimplex.vertex 0, rfl⟩) (by simp), ?_⟩
        change coboundary K 0 (fun _ ↦ r) = 0
        ext σ
        simp [coboundary_apply, Fin.sum_univ_two]
      refine ⟨Submodule.Quotient.mk ⟨_, hmem⟩, ?_⟩
      simp [Θ, linearCombination_single]
  exact ⟨(relativeSingularCohomologyEquiv K (Set.univ : Set Y)ᶜ 0).trans
    (LinearEquiv.ofBijective Θ hΘ)⟩

end Local

/-! ### Attaching a cell -/

section Cell

open CategoryTheory cohomologyWithSupports

/-- In an exact sequence `M → N → P` with `M` trivial, the map `N → P` is injective. -/
lemma injective_of_exact_of_subsingleton {M N P : Type*} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [Subsingleton M] {f : M →+ N} {g : N →+ P} (h : Function.Exact f g) :
    Function.Injective g := by
  refine (injective_iff_map_eq_zero g).2 fun y hy ↦ ?_
  obtain ⟨x, rfl⟩ := (h y).1 hy
  rw [Subsingleton.elim x 0, map_zero]

/-- In an exact sequence `M → N → P` with `P` trivial, the map `M → N` is surjective. -/
lemma surjective_of_exact_of_subsingleton {M N P : Type*} [Zero P] [Subsingleton P] {f : M → N}
    {g : N → P} (h : Function.Exact f g) :
    Function.Surjective f :=
  fun y ↦ (h y).1 (Subsingleton.elim _ _)

variable (K : Type) [Field K] {Y : TopCat.{0}} {p : Y} (hp : IsClosed ({p} : Set Y)) {V : Set Y}
  (hV : IsOpen V) (hpV : p ∈ V) {m : ℕ} (e : V ≃ₜ (Fin (m + 1) → ℝ)) (he : e ⟨p, hpV⟩ = 0)

include he in
/-- Under a chart `e : V ≃ₜ ℝᵐ⁺¹` sending `p` to `0`, the complement of `p` in `V` is the preimage
of `ℝᵐ⁺¹ - 0`. -/
lemma compl_preimage_singleton_eq_preimage :
    ((subspaceInclusion Y V) ⁻¹' {p})ᶜ =
      (TopCat.isoOfHomeo (X := TopCat.of V) (Y := TopCat.of (Fin (m + 1) → ℝ)) e).hom ⁻¹'
        ({0}ᶜ : Set (Fin (m + 1) → ℝ)) := by
  ext x
  simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff, not_iff_not]
  change x.1 = p ↔ e x = 0
  rw [← he, e.injective.eq_iff]
  exact ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩

/-- Excision and the chart `e` identify the local cohomology `H^k(Y, Y - p; K)` at a point with a
Euclidean neighbourhood with `H^k(ℝᵐ⁺¹, ℝᵐ⁺¹ - 0; K)`. -/
def cohomologyWithSupportsSingletonIso (k : ℤ) :
    cohomologyWithSupports K (ModuleCat.of K K) Y {p} k ≅
      cohomologyWithSupports K (ModuleCat.of K K) (TopCat.of (Fin (m + 1) → ℝ)) {0} k :=
  excisionIso K hV hp (Set.singleton_subset_iff.2 hpV) k ≪≫
    eqToIso (congrArg (fun A ↦ relativeSingularCohomology K (ModuleCat.of K K) (TopCat.of V) A k)
      (compl_preimage_singleton_eq_preimage hpV e he)) ≪≫
    (relativeSingularCohomologyIsoOfIso K
      (TopCat.isoOfHomeo (X := TopCat.of V) (Y := TopCat.of (Fin (m + 1) → ℝ)) e) _ k).symm

include hp hV he in
/-- The local cohomology `H^k(Y, Y - p; K)` at a point with a Euclidean neighbourhood `ℝᵐ⁺¹`
vanishes for `k ≠ m + 1`. -/
theorem subsingleton_cohomologyWithSupports_singleton {k : ℕ} (hk : k ≠ m + 1) :
    Subsingleton (cohomologyWithSupports K (ModuleCat.of K K) Y {p} k) :=
  (cohomologyWithSupportsSingletonIso K hp hV hpV e he k).toLinearEquiv.toEquiv.subsingleton_congr.2
    (subsingleton_cohomologyWithSupports_euclidean K (by omega) hk)

include hp hV he in
/-- In degrees `k` with `k ≠ m + 1` and `k + 1 ≠ m + 1`, restriction `H^k(Y; K) → H^k(Y - p; K)` is
bijective. -/
theorem bijective_restrictCompl_singleton {k : ℕ} (hk : k ≠ m + 1) (hk' : k + 1 ≠ m + 1) :
    Function.Bijective (restrictCompl K Y {p} k).hom := by
  have := subsingleton_cohomologyWithSupports_singleton K hp hV hpV e he hk
  have := subsingleton_cohomologyWithSupports_singleton K hp hV hpV e he hk'
  refine ⟨injective_of_exact_of_subsingleton (f := (toCohomology K _ Y {p} k).hom.toAddMonoidHom)
    (g := (restrictCompl K Y {p} k).hom.toAddMonoidHom)
    (exact_toCohomology_restrictCompl K Y {p} k), ?_⟩
  exact surjective_of_exact_of_subsingleton (exact_restrictCompl_delta K Y {p} k)

include hp hV he in
/-- If `H^m(Y - p; K) = 0` then `H^m(Y; K) = 0`. -/
theorem subsingleton_cohomology_of_compl_singleton
    (h : Subsingleton (cohomologyWithSupports K (ModuleCat.of K K) (TopCat.of ↥({p} : Set Y)ᶜ)
      Set.univ m)) :
    Subsingleton (cohomologyWithSupports K (ModuleCat.of K K) Y Set.univ m) := by
  have := subsingleton_cohomologyWithSupports_singleton K hp hV hpV e he (k := m) (by omega)
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨y, rfl⟩ := (exact_toCohomology_restrictCompl K Y {p} m x).1 (Subsingleton.elim _ _)
  rw [Subsingleton.elim y 0, map_zero]

include hp hV he in
/-- If `H^m(Y - p; K) = 0` and `H^{m+1}(Y - p; K) = 0` then `H^{m+1}(Y; K) ≅ K`. -/
theorem nonempty_cohomology_equiv_of_compl_singleton
    (h : Subsingleton (cohomologyWithSupports K (ModuleCat.of K K) (TopCat.of ↥({p} : Set Y)ᶜ)
      Set.univ m))
    (h' : Subsingleton (cohomologyWithSupports K (ModuleCat.of K K) (TopCat.of ↥({p} : Set Y)ᶜ)
      Set.univ (m + 1 : ℕ))) :
    Nonempty (cohomologyWithSupports K (ModuleCat.of K K) Y Set.univ (m + 1 : ℕ) ≃ₗ[K] K) := by
  have hb : Function.Bijective (toCohomology K (ModuleCat.of K K) Y {p} (m + 1 : ℕ)).hom :=
    ⟨injective_of_exact_of_subsingleton (f := (delta K Y {p} m).toAddMonoidHom)
      (g := (toCohomology K (ModuleCat.of K K) Y {p} (m + 1 : ℕ)).hom.toAddMonoidHom)
      (exact_delta_toCohomology K Y {p} m),
     surjective_of_exact_of_subsingleton (exact_toCohomology_restrictCompl K Y {p} (m + 1))⟩
  exact ⟨(LinearEquiv.ofBijective _ hb).symm.trans
    ((cohomologyWithSupportsSingletonIso K hp hV hpV e he (m + 1 : ℕ)).toLinearEquiv.trans
      (cohomologyWithSupportsEuclideanEquiv K m))⟩

end Cell

/-! ### Lines in `ℂⁿ⁺¹` -/

section LineProjection

open ComplexConjugate

/-- The matrix `v v^* / (v^* v)` of the orthogonal projection of `ℂ^ι` onto the line `ℂ v`. -/
def lineProjection {ι : Type*} [Fintype ι] (v : ι → ℂ) : ι → ι → ℂ :=
  fun i j ↦ v i * conj (v j) / ∑ k, v k * conj (v k)

variable {ι : Type*} [Fintype ι]

/-- The Hermitian square `∑ k, v k * conj (v k)` is the real number `∑ k, Complex.normSq (v k)`. -/
lemma sum_mul_conj_eq_ofReal (v : ι → ℂ) :
    ∑ k, v k * conj (v k) = ((∑ k, Complex.normSq (v k) : ℝ) : ℂ) := by
  push_cast [Complex.mul_conj]; rfl

open ComplexOrder in
/-- The Hermitian square `∑ k, v k * conj (v k)` of a nonzero vector `v` is nonzero. -/
lemma sum_mul_conj_ne_zero {v : ι → ℂ} (hv : v ≠ 0) : ∑ k, v k * conj (v k) ≠ 0 :=
  mt dotProduct_self_star_eq_zero.1 hv

/-- The projection onto the line `ℂ v` is unchanged by rescaling `v` by `c ≠ 0`. -/
lemma lineProjection_smul {v : ι → ℂ} (hv : v ≠ 0) {c : ℂ} (hc : c ≠ 0) :
    lineProjection (c • v) = lineProjection v := by
  have h := sum_mul_conj_ne_zero hv
  have hc' : c * conj c ≠ 0 := mul_ne_zero hc ((map_ne_zero _).2 hc)
  ext i j
  simp only [lineProjection, Pi.smul_apply, smul_eq_mul, map_mul]
  have : ∑ k, c * v k * (conj c * conj (v k)) = c * conj c * ∑ k, v k * conj (v k) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ ↦ by ring
  rw [this, div_eq_div_iff (mul_ne_zero hc' h) h]
  ring

/-- For `v l ≠ 0`, the ratio of the entries `(i, l)` and `(l, l)` of `lineProjection v` is
`v i / v l`. -/
lemma lineProjection_div_apply {v : ι → ℂ} (hv : v ≠ 0) {l : ι} (hl : v l ≠ 0) (i : ι) :
    lineProjection v i l / lineProjection v l l = v i / v l := by
  have h := sum_mul_conj_ne_zero hv
  have hl' : conj (v l) ≠ 0 := (map_ne_zero _).2 hl
  simp only [lineProjection]
  field_simp

/-- `x ↦ lineProjection (f x)` is continuous for a continuous `f` with nonzero values. -/
lemma continuous_lineProjection_comp {X : Type*} [TopologicalSpace X] {f : X → ι → ℂ}
    (hf : Continuous f) (h0 : ∀ x, f x ≠ 0) : Continuous fun x ↦ lineProjection (f x) := by
  have hc : ∀ i, Continuous fun x ↦ f x i := fun i ↦ (continuous_apply i).comp hf
  refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
  refine Continuous.div ((hc i).mul (Complex.continuous_conj.comp (hc j)))
    (continuous_finsetSum _ fun k _ ↦ (hc k).mul (Complex.continuous_conj.comp (hc k)))
    fun x ↦ sum_mul_conj_ne_zero (h0 x)

omit [Fintype ι] in
/-- Each entry `x ↦ f x i j` of a continuous matrix-valued map `f` is continuous. -/
lemma continuous_entry {X : Type*} [TopologicalSpace X] {f : X → ι → ι → ℂ} (hf : Continuous f)
    (i j : ι) : Continuous fun x ↦ f x i j :=
  (continuous_apply_apply i j).comp hf

variable {n : ℕ}

/-- The Hermitian square of `v ∈ ℂⁿ⁺¹` is that of `Fin.init v` plus the term of the last
coordinate. -/
lemma sum_mul_conj_castSucc (v : Fin (n + 1) → ℂ) :
    ∑ k, v k * conj (v k) = ∑ k, Fin.init v k * conj (Fin.init v k) +
      v (Fin.last n) * conj (v (Fin.last n)) :=
  Fin.sum_univ_castSucc _

/-- `1` minus the last diagonal entry of `lineProjection v` is the Hermitian square of `Fin.init v`
divided by that of `v`. -/
lemma one_sub_lineProjection_last {v : Fin (n + 1) → ℂ} (hv : v ≠ 0) :
    1 - lineProjection v (Fin.last n) (Fin.last n) =
      (∑ k, Fin.init v k * conj (Fin.init v k)) / ∑ k, v k * conj (v k) := by
  have h := sum_mul_conj_ne_zero hv
  rw [lineProjection, eq_div_iff h, sub_mul, div_mul_cancel₀ _ h, sum_mul_conj_castSucc]
  ring

/-- The last diagonal entry of `lineProjection v` is `1` iff all other coordinates of `v`
vanish. -/
lemma lineProjection_last_eq_one_iff {v : Fin (n + 1) → ℂ} (hv : v ≠ 0) :
    lineProjection v (Fin.last n) (Fin.last n) = 1 ↔ Fin.init v = 0 := by
  rw [← sub_eq_zero, ← neg_eq_zero, neg_sub, one_sub_lineProjection_last hv,
    div_eq_zero_iff, or_iff_left (sum_mul_conj_ne_zero hv)]
  refine ⟨fun h ↦ by_contra fun h' ↦ sum_mul_conj_ne_zero h' h, fun h ↦ by simp [h]⟩

/-- The last diagonal entry of the projection onto the last coordinate line is `1`. -/
lemma lineProjection_single_last :
    lineProjection (Pi.single (Fin.last n) 1 : Fin (n + 1) → ℂ) (Fin.last n) (Fin.last n) = 1 := by
  rw [lineProjection_last_eq_one_iff (by simp)]
  ext i; simp [Fin.init, Fin.castSucc_ne_last]

/-- The line `ℂ v` is the last coordinate line iff all other coordinates of `v` vanish. -/
lemma lineProjection_eq_single_last_iff {v : Fin (n + 1) → ℂ} (hv : v ≠ 0) :
    lineProjection v = lineProjection (Pi.single (Fin.last n) 1) ↔ Fin.init v = 0 := by
  refine ⟨fun h ↦ (lineProjection_last_eq_one_iff hv).1 (by rw [h, lineProjection_single_last]),
    fun h ↦ ?_⟩
  have hl : v (Fin.last n) ≠ 0 := fun hl ↦ hv (by
    ext i; induction i using Fin.lastCases with
    | last => exact hl
    | cast i => exact congrFun h i)
  have : v = v (Fin.last n) • Pi.single (Fin.last n) 1 := by
    ext i; induction i using Fin.lastCases with
    | last => simp
    | cast i => simpa [Fin.castSucc_ne_last, Fin.init] using congrFun h i
  rw [this, lineProjection_smul (by simp) hl]

end LineProjection

/-! ### Complex projective space -/

section ProjectiveSpace

open ComplexConjugate

/-- Complex projective space `ℙⁿ(ℂ)`, realized as the set of matrices `v v^* / (v^* v)` of the
orthogonal projections of `ℂⁿ⁺¹` onto its lines, with the subspace topology. -/
def lineProjections (n : ℕ) : Set (Fin (n + 1) → Fin (n + 1) → ℂ) :=
  {P | ∃ v, v ≠ 0 ∧ lineProjection v = P}

/-- Complex projective space `ℙⁿ(ℂ)` as a topological space: the space of lines of `ℂⁿ⁺¹`,
each line represented by its orthogonal projection. -/
abbrev complexProjectiveSpace (n : ℕ) : TopCat.{0} := TopCat.of (lineProjections n)

/-- The projection onto the line `ℂ v` of a nonzero `v` is a point of `ℙⁿ(ℂ)`. -/
lemma lineProjection_mem_lineProjections {n : ℕ} {v : Fin (n + 1) → ℂ} (hv : v ≠ 0) :
    lineProjection v ∈ lineProjections n :=
  ⟨v, hv, rfl⟩

/-- `ℙ⁰(ℂ)` is a point. -/
instance : Unique (complexProjectiveSpace 0) where
  default := ⟨lineProjection (fun _ ↦ 1), lineProjection_mem_lineProjections
    (fun h ↦ one_ne_zero (congrFun h 0))⟩
  uniq P := by
    have key : ∀ Q : complexProjectiveSpace 0, Q.1 = fun _ _ ↦ 1 := by
      rintro ⟨_, v, hv, rfl⟩
      ext i j
      obtain rfl : i = 0 := Fin.fin_one_eq_zero i
      obtain rfl : j = 0 := Fin.fin_one_eq_zero j
      simpa [lineProjection] using div_self (sum_mul_conj_ne_zero hv)
    exact Subtype.ext ((key P).trans (key _).symm)

variable (n : ℕ)

/-- The point `[0 : ⋯ : 0 : 1]` of `ℙⁿ⁺¹(ℂ)`. -/
def projectiveSpaceBasePoint : complexProjectiveSpace (n + 1) :=
  ⟨lineProjection (Pi.single (Fin.last (n + 1)) 1), lineProjection_mem_lineProjections (by simp)⟩

/-- The affine cell `{x_{n+1} ≠ 0}` of `ℙⁿ⁺¹(ℂ)` around the base point. -/
def projectiveSpaceCell : Set (complexProjectiveSpace (n + 1)) :=
  {P | P.1 (Fin.last (n + 1)) (Fin.last (n + 1)) ≠ 0}

/-- The cell `{x_{n+1} ≠ 0}` is open in `ℙⁿ⁺¹(ℂ)`. -/
lemma isOpen_projectiveSpaceCell : IsOpen (projectiveSpaceCell n) :=
  isOpen_ne_fun (continuous_entry continuous_subtype_val _ _) continuous_const

/-- The base point `[0 : ⋯ : 0 : 1]` lies in the cell `{x_{n+1} ≠ 0}`. -/
lemma projectiveSpaceBasePoint_mem_cell :
    projectiveSpaceBasePoint n ∈ projectiveSpaceCell n := by
  change lineProjection _ _ _ ≠ 0
  rw [lineProjection_single_last]; exact one_ne_zero

/-- If the last diagonal entry of `lineProjection v` is nonzero, so is the last coordinate of
`v`. -/
lemma lineProjection_last_ne_zero {v : Fin (n + 2) → ℂ}
    (h : lineProjection v (Fin.last (n + 1)) (Fin.last (n + 1)) ≠ 0) : v (Fin.last (n + 1)) ≠ 0 :=
  fun h0 ↦ h (by simp [lineProjection, h0])

/-- The vector `(w, 1)` is nonzero. -/
lemma snoc_one_ne_zero (w : Fin (n + 1) → ℂ) :
    (Fin.snoc (α := fun _ ↦ ℂ) w 1 : Fin (n + 2) → ℂ) ≠ 0 :=
  fun h ↦ one_ne_zero (α := ℂ) (by simpa using congrFun h (Fin.last _))

/-- The last diagonal entry of the projection onto the line `ℂ (w, 1)` is nonzero. -/
lemma lineProjection_snoc_one_last (w : Fin (n + 1) → ℂ) :
    lineProjection (Fin.snoc (α := fun _ ↦ ℂ) w 1 : Fin (n + 2) → ℂ) (Fin.last (n + 1))
      (Fin.last (n + 1)) ≠ 0 := by
  simpa [lineProjection] using sum_mul_conj_ne_zero (snoc_one_ne_zero n w)

/-- The affine chart `[x : 1] ↦ x` of the cell `{x_{n+1} ≠ 0}` of `ℙⁿ⁺¹(ℂ)`. -/
def projectiveSpaceChart : projectiveSpaceCell n ≃ₜ (Fin (n + 1) → ℂ) where
  toFun P i :=
    P.1.1 (Fin.castSucc i) (Fin.last (n + 1)) / P.1.1 (Fin.last (n + 1)) (Fin.last (n + 1))
  invFun w := ⟨⟨lineProjection (Fin.snoc (α := fun _ ↦ ℂ) w 1), lineProjection_mem_lineProjections
    (snoc_one_ne_zero n w)⟩, lineProjection_snoc_one_last n w⟩
  left_inv := by
    rintro ⟨⟨_, v, hv, rfl⟩, hP⟩
    have hl := lineProjection_last_ne_zero n hP
    refine Subtype.ext (Subtype.ext ?_)
    change lineProjection _ = lineProjection v
    have : (Fin.snoc (fun i ↦ lineProjection v (Fin.castSucc i) (Fin.last (n + 1)) /
        lineProjection v (Fin.last (n + 1)) (Fin.last (n + 1))) 1 : Fin (n + 2) → ℂ) =
        (v (Fin.last (n + 1)))⁻¹ • v := by
      ext i; induction i using Fin.lastCases with
      | last => simp [hl]
      | cast i => simp [lineProjection_div_apply hv hl, div_eq_inv_mul]
    rw [this, lineProjection_smul hv (inv_ne_zero hl)]
  right_inv w := by
    ext i
    change lineProjection _ _ _ / lineProjection _ _ _ = _
    rw [lineProjection_div_apply (snoc_one_ne_zero n w) (by simp)]
    simp
  continuous_toFun := continuous_pi fun i ↦ Continuous.div
    (continuous_entry (continuous_subtype_val.comp continuous_subtype_val) _ _)
    (continuous_entry (continuous_subtype_val.comp continuous_subtype_val) _ _) fun P ↦ P.2
  continuous_invFun := ((continuous_lineProjection_comp
    (Continuous.finSnoc continuous_id continuous_const) (snoc_one_ne_zero n)).subtype_mk
      _).subtype_mk _

/-- The affine chart sends the base point to `0`. -/
lemma projectiveSpaceChart_basePoint :
    projectiveSpaceChart n ⟨_, projectiveSpaceBasePoint_mem_cell n⟩ = 0 := by
  ext i
  change lineProjection _ _ _ / _ = 0
  simp [lineProjection, Fin.castSucc_ne_last]

/-- `ℂⁿ⁺¹` and `ℝ^{2n+2}` have the same real dimension. -/
lemma finrank_fun_complex_eq :
    Module.finrank ℝ (Fin (n + 1) → ℂ) = Module.finrank ℝ (Fin (2 * n + 1 + 1) → ℝ) := by
  simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]; ring

/-- The cell `{x_{n+1} ≠ 0}` of `ℙⁿ⁺¹(ℂ)` is a Euclidean space `ℝ^{2n+2}`, with the base point at
the origin. -/
def projectiveSpaceCellHomeomorph : projectiveSpaceCell n ≃ₜ (Fin (2 * n + 1 + 1) → ℝ) :=
  (projectiveSpaceChart n).trans
    (ContinuousLinearEquiv.ofFinrankEq (finrank_fun_complex_eq n)).toHomeomorph

/-- The homeomorphism of the cell with `ℝ^{2n+2}` sends the base point to `0`. -/
lemma projectiveSpaceCellHomeomorph_basePoint :
    projectiveSpaceCellHomeomorph n ⟨_, projectiveSpaceBasePoint_mem_cell n⟩ = 0 := by
  rw [projectiveSpaceCellHomeomorph, Homeomorph.trans_apply, projectiveSpaceChart_basePoint]
  simp

/-! ### The complement of the base point retracts onto a hyperplane -/

open CategoryTheory

/-- The complement of the base point `[0 : ⋯ : 0 : 1]` in `ℙⁿ⁺¹(ℂ)`. -/
abbrev projectiveSpaceBasePointCompl : TopCat.{0} :=
  TopCat.of ↥({projectiveSpaceBasePoint n} : Set (complexProjectiveSpace (n + 1)))ᶜ

/-- The matrix of `ℂⁿ⁺¹ ⊆ ℂⁿ⁺²` extended by zero: the hyperplane `{x_{n+1} = 0}`. -/
def hyperplaneMatrix (Q : Fin (n + 1) → Fin (n + 1) → ℂ) : Fin (n + 2) → Fin (n + 2) → ℂ :=
  Fin.snoc (α := fun _ ↦ Fin (n + 2) → ℂ) (fun i ↦ Fin.snoc (α := fun _ ↦ ℂ) (Q i) 0) 0

/-- Extending the projection onto `ℂ w` by zero gives the projection onto `ℂ (w, 0)`. -/
lemma hyperplaneMatrix_lineProjection (w : Fin (n + 1) → ℂ) :
    hyperplaneMatrix n (lineProjection w) = lineProjection (Fin.snoc (α := fun _ ↦ ℂ) w 0) := by
  have hS : ∑ k, (Fin.snoc (α := fun _ ↦ ℂ) w 0 : Fin (n + 2) → ℂ) k *
      conj ((Fin.snoc (α := fun _ ↦ ℂ) w 0 : Fin (n + 2) → ℂ) k) = ∑ k, w k * conj (w k) := by
    rw [sum_mul_conj_castSucc]; simp [Fin.init_snoc]
  ext i j
  induction i using Fin.lastCases with
  | last => simp [hyperplaneMatrix, lineProjection]
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [hyperplaneMatrix, lineProjection]
    | cast j => simp [hyperplaneMatrix, lineProjection, hS]

/-- The vector `(w, 0)` is nonzero for `w ≠ 0`. -/
lemma snoc_zero_ne_zero {w : Fin (n + 1) → ℂ} (hw : w ≠ 0) :
    (Fin.snoc (α := fun _ ↦ ℂ) w 0 : Fin (n + 2) → ℂ) ≠ 0 := fun h ↦
  hw (by ext i; simpa using congrFun h (Fin.castSucc i))

/-- Extending by zero sends a point of `ℙⁿ(ℂ)` to a point of `ℙⁿ⁺¹(ℂ)`. -/
lemma hyperplaneMatrix_mem (Q : complexProjectiveSpace n) :
    hyperplaneMatrix n Q.1 ∈ lineProjections (n + 1) := by
  obtain ⟨w, hw, hQ⟩ := Q.2
  rw [← hQ, hyperplaneMatrix_lineProjection]
  exact lineProjection_mem_lineProjections (snoc_zero_ne_zero n hw)

/-- The last diagonal entry of the base point `[0 : ⋯ : 0 : 1]` is `1`. -/
lemma basePoint_last : (projectiveSpaceBasePoint n).1 (Fin.last (n + 1)) (Fin.last (n + 1)) = 1 :=
  lineProjection_single_last

/-- A point of the hyperplane `{x_{n+1} = 0}` is not the base point. -/
lemma hyperplaneMatrix_mem_compl (Q : complexProjectiveSpace n) :
    (⟨hyperplaneMatrix n Q.1, hyperplaneMatrix_mem n Q⟩ : complexProjectiveSpace (n + 1)) ∈
      ({projectiveSpaceBasePoint n} : Set (complexProjectiveSpace (n + 1)))ᶜ := fun h ↦ by
  have := congrArg (fun x : complexProjectiveSpace (n + 1) ↦
    x.1 (Fin.last (n + 1)) (Fin.last (n + 1))) h
  simp only [basePoint_last] at this
  simp [hyperplaneMatrix] at this

/-- The inclusion `ℙⁿ(ℂ) ⟶ ℙⁿ⁺¹(ℂ) - [0 : ⋯ : 0 : 1]` of the hyperplane `{x_{n+1} = 0}`. -/
def hyperplaneInclusion : complexProjectiveSpace n ⟶ projectiveSpaceBasePointCompl n :=
  TopCat.ofHom ⟨fun Q ↦ ⟨⟨hyperplaneMatrix n Q.1, hyperplaneMatrix_mem n Q⟩,
    hyperplaneMatrix_mem_compl n Q⟩, by
      refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
      exact Continuous.finSnoc (continuous_pi fun i ↦ Continuous.finSnoc
        ((continuous_apply i).comp continuous_subtype_val) continuous_const) continuous_const⟩

/-- A point of `ℙⁿ⁺¹(ℂ)` other than the base point is the line `ℂ v` of a vector `v` whose first
`n + 1` coordinates are not all zero. -/
lemma exists_lineProjection_eq_of_ne {x : complexProjectiveSpace (n + 1)}
    (hx : x ≠ projectiveSpaceBasePoint n) :
    ∃ v : Fin (n + 2) → ℂ, v ≠ 0 ∧ Fin.init v ≠ 0 ∧ lineProjection v = x.1 := by
  obtain ⟨v, hv, hx'⟩ := x.2
  refine ⟨v, hv, fun h ↦ hx (Subtype.ext ?_), hx'⟩
  rw [← hx']
  exact (lineProjection_eq_single_last_iff hv).2 h

/-- The last diagonal entry of a point of `ℙⁿ⁺¹(ℂ)` other than the base point is not `1`. -/
lemma one_sub_last_ne_zero (x : projectiveSpaceBasePointCompl n) :
    1 - x.1.1 (Fin.last (n + 1)) (Fin.last (n + 1)) ≠ 0 := by
  obtain ⟨v, hv, hi, hx⟩ := exists_lineProjection_eq_of_ne n x.2
  rw [← hx, one_sub_lineProjection_last hv]
  exact div_ne_zero (sum_mul_conj_ne_zero hi) (sum_mul_conj_ne_zero hv)

/-- For a point `x` of `ℙⁿ⁺¹(ℂ)` other than the base point, the upper-left `(n + 1) × (n + 1)`
block of `x` divided by `1 - x_{n+1,n+1}` is a point of `ℙⁿ(ℂ)`. -/
lemma retractionMatrix_mem (x : projectiveSpaceBasePointCompl n) :
    (fun i j ↦ x.1.1 (Fin.castSucc i) (Fin.castSucc j) /
      (1 - x.1.1 (Fin.last (n + 1)) (Fin.last (n + 1)))) ∈ lineProjections n := by
  obtain ⟨v, hv, hi, hx⟩ := exists_lineProjection_eq_of_ne n x.2
  refine ⟨Fin.init v, hi, ?_⟩
  rw [← hx, one_sub_lineProjection_last hv]
  have h1 := sum_mul_conj_ne_zero hv
  have h2 := sum_mul_conj_ne_zero hi
  ext i j
  simp only [lineProjection, Fin.init]
  field_simp

/-- The retraction `[x : z] ↦ [x]` of `ℙⁿ⁺¹(ℂ) - [0 : ⋯ : 0 : 1]` onto `ℙⁿ(ℂ)`. -/
def hyperplaneRetraction : projectiveSpaceBasePointCompl n ⟶ complexProjectiveSpace n :=
  TopCat.ofHom ⟨fun x ↦ ⟨_, retractionMatrix_mem n x⟩, by
    refine Continuous.subtype_mk (continuous_pi fun i ↦ continuous_pi fun j ↦ ?_) _
    exact (continuous_entry (continuous_subtype_val.comp continuous_subtype_val) _ _).div
      (continuous_const.sub (continuous_entry (continuous_subtype_val.comp
        continuous_subtype_val) _ _)) (one_sub_last_ne_zero n)⟩

/-- The retraction restricts to the identity on the hyperplane. -/
lemma hyperplaneInclusion_comp_retraction :
    hyperplaneInclusion n ≫ hyperplaneRetraction n = 𝟙 _ := by
  ext Q i j
  simp [hyperplaneInclusion, hyperplaneRetraction, hyperplaneMatrix]

/-- The scaling `(x, z) ↦ (x, t z)` of the last coordinate of `ℂⁿ⁺²`. -/
def lastScale (t : ℝ) : Fin (n + 2) → ℂ := Fin.snoc (α := fun _ ↦ ℂ) 1 (t : ℂ)

/-- The coordinates of `lastScale n t` are real. -/
@[simp] lemma conj_lastScale (t : ℝ) (i : Fin (n + 2)) :
    conj (lastScale n t i) = lastScale n t i := by
  induction i using Fin.lastCases with
  | last => simp [lastScale]
  | cast i => simp [lastScale]

/-- `lastScale n 1` is the constant vector `1`. -/
@[simp] lemma lastScale_one : lastScale n 1 = 1 := by
  ext i; induction i using Fin.lastCases with
  | last => simp [lastScale]
  | cast i => simp [lastScale]

/-- The matrix of the line `ℂ (x, t z)`, from that of the line `ℂ (x, z)`, `x ≠ 0`. -/
def scaledMatrix (t : ℝ) (P : Fin (n + 2) → Fin (n + 2) → ℂ) : Fin (n + 2) → Fin (n + 2) → ℂ :=
  fun i j ↦ lastScale n t i * lastScale n t j * P i j /
    (1 - (1 - (t : ℂ) ^ 2) * P (Fin.last (n + 1)) (Fin.last (n + 1)))

/-- Scaling the last coordinate leaves the first `n + 1` coordinates unchanged. -/
lemma init_lastScale_mul (t : ℝ) (v : Fin (n + 2) → ℂ) :
    Fin.init (lastScale n t * v) = Fin.init v := by
  ext i; simp [Fin.init, lastScale]

/-- Scaling the last coordinate of `v` gives a nonzero vector when the first `n + 1` coordinates of
`v` are not all zero. -/
lemma lastScale_mul_ne_zero (t : ℝ) {v : Fin (n + 2) → ℂ} (hi : Fin.init v ≠ 0) :
    lastScale n t * v ≠ 0 := fun h ↦ hi (by rw [← init_lastScale_mul n t, h]; rfl)

/-- The denominator of `scaledMatrix n t` at `lineProjection v` is the Hermitian square of
`lastScale n t * v` divided by that of `v`. -/
lemma one_sub_mul_lineProjection_last (t : ℝ) {v : Fin (n + 2) → ℂ} (hv : v ≠ 0) :
    1 - (1 - (t : ℂ) ^ 2) * lineProjection v (Fin.last (n + 1)) (Fin.last (n + 1)) =
      (∑ k, (lastScale n t * v) k * conj ((lastScale n t * v) k)) / ∑ k, v k * conj (v k) := by
  have h := sum_mul_conj_ne_zero hv
  rw [eq_div_iff h, sum_mul_conj_castSucc (lastScale n t * v), init_lastScale_mul,
    sum_mul_conj_castSucc v]
  simp only [lineProjection, Pi.mul_apply, map_mul, conj_lastScale]
  rw [← sum_mul_conj_castSucc v]
  field_simp
  simp only [lastScale, Fin.snoc_last]
  rw [sum_mul_conj_castSucc v]
  ring

/-- `scaledMatrix n t` sends the line `ℂ (x, z)` to the line `ℂ (x, t z)`, for `x ≠ 0`. -/
lemma scaledMatrix_lineProjection (t : ℝ) {v : Fin (n + 2) → ℂ} (hv : v ≠ 0)
    (hi : Fin.init v ≠ 0) :
    scaledMatrix n t (lineProjection v) = lineProjection (lastScale n t * v) := by
  have h1 := sum_mul_conj_ne_zero hv
  have h2 := sum_mul_conj_ne_zero (lastScale_mul_ne_zero n t hi)
  ext i j
  rw [scaledMatrix, one_sub_mul_lineProjection_last n t hv]
  simp only [lineProjection, Pi.mul_apply, map_mul, conj_lastScale]
  field_simp

/-- `scaledMatrix n t` sends a point of `ℙⁿ⁺¹(ℂ) - [0 : ⋯ : 0 : 1]` to a point of `ℙⁿ⁺¹(ℂ)`. -/
lemma scaledMatrix_mem (t : ℝ) (x : projectiveSpaceBasePointCompl n) :
    scaledMatrix n t x.1.1 ∈ lineProjections (n + 1) := by
  obtain ⟨v, hv, hi, hx⟩ := exists_lineProjection_eq_of_ne n x.2
  rw [← hx, scaledMatrix_lineProjection n t hv hi]
  exact lineProjection_mem_lineProjections (lastScale_mul_ne_zero n t hi)

/-- `scaledMatrix n t` sends a point of `ℙⁿ⁺¹(ℂ) - [0 : ⋯ : 0 : 1]` to a point other than the base
point. -/
lemma scaledMatrix_mem_compl (t : ℝ) (x : projectiveSpaceBasePointCompl n) :
    (⟨scaledMatrix n t x.1.1, scaledMatrix_mem n t x⟩ : complexProjectiveSpace (n + 1)) ∈
      ({projectiveSpaceBasePoint n} : Set (complexProjectiveSpace (n + 1)))ᶜ := fun h ↦ by
  obtain ⟨v, hv, hi, hx⟩ := exists_lineProjection_eq_of_ne n x.2
  have h' := congrArg Subtype.val h
  simp only [← hx, scaledMatrix_lineProjection n t hv hi] at h'
  rw [projectiveSpaceBasePoint, lineProjection_eq_single_last_iff
    (lastScale_mul_ne_zero n t hi), init_lastScale_mul] at h'
  exact hi h'

/-- The denominator of `scaledMatrix n t` is nonzero away from the base point. -/
lemma scaledMatrix_denom_ne_zero (t : ℝ) (x : projectiveSpaceBasePointCompl n) :
    1 - (1 - (t : ℂ) ^ 2) * x.1.1 (Fin.last (n + 1)) (Fin.last (n + 1)) ≠ 0 := by
  obtain ⟨v, hv, hi, hx⟩ := exists_lineProjection_eq_of_ne n x.2
  rw [← hx, one_sub_mul_lineProjection_last n t hv]
  exact div_ne_zero (sum_mul_conj_ne_zero (lastScale_mul_ne_zero n t hi))
    (sum_mul_conj_ne_zero hv)

/-- Each coordinate of `lastScale n t` is continuous in `t`. -/
lemma continuous_lastScale (i : Fin (n + 2)) : Continuous fun t : ℝ ↦ lastScale n t i :=
  (continuous_apply i).comp (Continuous.finSnoc continuous_const Complex.continuous_ofReal)

/-- The deformation `[x : z] ↦ [x : t z]` of `ℙⁿ⁺¹(ℂ) - [0 : ⋯ : 0 : 1]` onto the hyperplane
`{x_{n+1} = 0}`, as a homotopy from the retraction to the identity. -/
def hyperplaneHomotopy :
    TopCat.Homotopy (hyperplaneRetraction n ≫ hyperplaneInclusion n) (𝟙 _) where
  toFun p := ⟨⟨scaledMatrix n p.1 p.2.1.1, scaledMatrix_mem n p.1 p.2⟩,
    scaledMatrix_mem_compl n p.1 p.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    have hP : Continuous fun p : unitInterval × projectiveSpaceBasePointCompl n ↦ p.2.1.1 :=
      continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
    have ht : ∀ i, Continuous fun p : unitInterval × projectiveSpaceBasePointCompl n ↦
        lastScale n p.1 i :=
      fun i ↦ (continuous_lastScale n i).comp (continuous_subtype_val.comp continuous_fst)
    refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
    refine (((ht i).mul (ht j)).mul (continuous_entry hP i j)).div
      (continuous_const.sub (((continuous_const.sub
        ((Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)).pow 2)).mul
          (continuous_entry hP _ _)))) fun p ↦ scaledMatrix_denom_ne_zero n p.1 p.2
  map_zero_left x := by
    refine Subtype.ext (Subtype.ext ?_)
    change scaledMatrix n 0 x.1.1 = hyperplaneMatrix n (fun i j ↦ x.1.1 (Fin.castSucc i)
      (Fin.castSucc j) / (1 - x.1.1 (Fin.last (n + 1)) (Fin.last (n + 1))))
    ext i j
    induction i using Fin.lastCases with
    | last => simp [scaledMatrix, hyperplaneMatrix, lastScale]
    | cast i =>
      induction j using Fin.lastCases with
      | last => simp [scaledMatrix, hyperplaneMatrix, lastScale]
      | cast j => simp [scaledMatrix, hyperplaneMatrix, lastScale]
  map_one_left x := by
    refine Subtype.ext (Subtype.ext ?_)
    change scaledMatrix n 1 x.1.1 = x.1.1
    ext i j
    simp [scaledMatrix, lastScale_one]

end ProjectiveSpace

/-! ### The cohomology of `ℙⁿ(ℂ)` -/

section Cohomology

open CategoryTheory

variable (K : Type) [Field K]

/-- **The cohomology of complex projective space.** `H^k(ℙⁿ(ℂ); K) ≅ K` for `k` even with
`k ≤ 2n`, and `H^k(ℙⁿ(ℂ); K) = 0` otherwise. -/
theorem cohomology_complexProjectiveSpace (n k : ℕ) :
    (Even k ∧ k ≤ 2 * n → Nonempty (cohomologyWithSupports K (ModuleCat.of K K)
      (complexProjectiveSpace n) Set.univ k ≃ₗ[K] K)) ∧
    (¬ (Even k ∧ k ≤ 2 * n) → Subsingleton (cohomologyWithSupports K (ModuleCat.of K K)
      (complexProjectiveSpace n) Set.univ k)) := by
  induction n generalizing k with
  | zero =>
    rcases k with _ | k
    · exact ⟨fun _ ↦ nonempty_cohomology_zero_equiv_of_unique K _,
        fun h ↦ absurd ⟨⟨0, rfl⟩, le_rfl⟩ h⟩
    · exact ⟨fun h ↦ absurd h.2 (by omega),
        fun _ ↦ subsingleton_cohomology_of_unique K _ k⟩
  | succ n ih =>
    have hp : IsClosed ({projectiveSpaceBasePoint n} : Set (complexProjectiveSpace (n + 1))) :=
      isClosed_singleton
    have he := projectiveSpaceCellHomeomorph_basePoint n
    let iso : ∀ j : ℤ, cohomologyWithSupports K (ModuleCat.of K K)
        (projectiveSpaceBasePointCompl n) Set.univ j ≅
        cohomologyWithSupports K (ModuleCat.of K K) (complexProjectiveSpace n) Set.univ j :=
      cohomologyIsoOfHomotopy K (hyperplaneInclusion n) (hyperplaneRetraction n)
        (hyperplaneInclusion_comp_retraction n) (hyperplaneHomotopy n)
    have hW : ∀ j : ℕ, ¬ (Even j ∧ j ≤ 2 * n) → Subsingleton (cohomologyWithSupports K
        (ModuleCat.of K K) (projectiveSpaceBasePointCompl n) Set.univ j) := fun j hj ↦
      (iso j).toLinearEquiv.toEquiv.subsingleton_congr.2 ((ih j).2 hj)
    have hodd : ¬ (Even (2 * n + 1) ∧ 2 * n + 1 ≤ 2 * n) := fun h ↦ by omega
    by_cases hk₁ : k = 2 * n + 1 + 1
    · subst hk₁
      refine ⟨fun _ ↦ nonempty_cohomology_equiv_of_compl_singleton K hp
        (isOpen_projectiveSpaceCell n) (projectiveSpaceBasePoint_mem_cell n)
        (projectiveSpaceCellHomeomorph n) he (hW _ hodd) (hW _ fun h ↦ by omega),
        fun h ↦ absurd ⟨⟨n + 1, by ring⟩, by omega⟩ h⟩
    by_cases hk₂ : k = 2 * n + 1
    · subst hk₂
      refine ⟨fun h ↦ absurd h (fun h ↦ by rcases h.1 with ⟨r, hr⟩; omega), fun _ ↦ ?_⟩
      exact subsingleton_cohomology_of_compl_singleton K hp (isOpen_projectiveSpaceCell n)
        (projectiveSpaceBasePoint_mem_cell n) (projectiveSpaceCellHomeomorph n) he (hW _ hodd)
    · have hb := bijective_restrictCompl_singleton K hp (isOpen_projectiveSpaceCell n)
        (projectiveSpaceBasePoint_mem_cell n) (projectiveSpaceCellHomeomorph n) he (k := k)
        hk₁ (by omega)
      let e := (LinearEquiv.ofBijective _ hb).trans (iso k).toLinearEquiv
      have hiff : (Even k ∧ k ≤ 2 * (n + 1)) ↔ (Even k ∧ k ≤ 2 * n) :=
        ⟨fun h ↦ ⟨h.1, by rcases h.1 with ⟨r, hr⟩; omega⟩, fun h ↦ ⟨h.1, by omega⟩⟩
      rw [hiff]
      exact ⟨fun h ↦ ((ih k).1 h).map e.trans,
        fun h ↦ e.toEquiv.subsingleton_congr.2 ((ih k).2 h)⟩

/-- `H^{2k}(ℙⁿ(ℂ); K) ≅ K` for `k ≤ n`. -/
theorem nonempty_cohomology_complexProjectiveSpace_equiv {n k : ℕ} (hk : k ≤ n) :
    Nonempty (cohomologyWithSupports K (ModuleCat.of K K) (complexProjectiveSpace n) Set.univ
      (2 * k : ℕ) ≃ₗ[K] K) :=
  (cohomology_complexProjectiveSpace K n (2 * k)).1 ⟨even_two_mul k, by omega⟩

/-- The odd cohomology of `ℙⁿ(ℂ)` vanishes. -/
theorem subsingleton_cohomology_complexProjectiveSpace_of_odd {n k : ℕ} (hk : Odd k) :
    Subsingleton (cohomologyWithSupports K (ModuleCat.of K K) (complexProjectiveSpace n)
      Set.univ k) :=
  (cohomology_complexProjectiveSpace K n k).2 fun h ↦ (Nat.not_even_iff_odd.2 hk) h.1

/-- The cohomology of `ℙⁿ(ℂ)` vanishes above the real dimension `2n`. -/
theorem subsingleton_cohomology_complexProjectiveSpace_of_lt {n k : ℕ} (hk : 2 * n < k) :
    Subsingleton (cohomologyWithSupports K (ModuleCat.of K K) (complexProjectiveSpace n)
      Set.univ k) :=
  (cohomology_complexProjectiveSpace K n k).2 fun h ↦ by omega

/-- The Betti numbers of `ℙⁿ(ℂ)`: `dim H^k(ℙⁿ(ℂ); K)` is `1` for `k` even with `k ≤ 2n`, and `0`
otherwise. -/
theorem finrank_cohomology_complexProjectiveSpace (n k : ℕ) :
    Module.finrank K (cohomologyWithSupports K (ModuleCat.of K K) (complexProjectiveSpace n)
      Set.univ k) = if Even k ∧ k ≤ 2 * n then 1 else 0 := by
  split_ifs with h
  · obtain ⟨e⟩ := (cohomology_complexProjectiveSpace K n k).1 h
    rw [e.finrank_eq, Module.finrank_self]
  · have := (cohomology_complexProjectiveSpace K n k).2 h
    exact Module.finrank_zero_of_subsingleton

/-- The Betti numbers of a space homeomorphic to `ℙⁿ(ℂ)`. -/
theorem finrank_cohomology_of_iso_complexProjectiveSpace {Y : TopCat.{0}} {n : ℕ}
    (e : Y ≅ complexProjectiveSpace n) (k : ℕ) :
    Module.finrank K (cohomologyWithSupports K (ModuleCat.of K K) Y Set.univ k) =
      if Even k ∧ k ≤ 2 * n then 1 else 0 := by
  have h := (relativeSingularCohomologyIsoOfIso K e (Set.univ : Set (complexProjectiveSpace n))ᶜ
    k).toLinearEquiv.finrank_eq
  rw [Set.preimage_compl, Set.preimage_univ] at h
  rw [← finrank_cohomology_complexProjectiveSpace K n k]
  exact h.symm

end Cohomology

/-! ### Naturality of the maps of pairs -/

section Naturality

open CategoryTheory

variable (K : Type) [Field K]

/-- Applying the maps induced by `f` and then by `g` to a relative class is applying the map
induced by `g ≫ f`. -/
lemma map_map_apply {Y'' Y' Y : TopCat.{0}} (g : Y'' ⟶ Y') (f : Y' ⟶ Y) {A'' : Set Y''}
    {A' : Set Y'} {A : Set Y} (hg : A'' ⊆ g ⁻¹' A') (hf : A' ⊆ f ⁻¹' A) (j : ℤ)
    (x : relativeSingularCohomology K (ModuleCat.of K K) Y A j) :
    (relativeSingularCohomology.map K (ModuleCat.of K K) g hg j).hom
        ((relativeSingularCohomology.map K (ModuleCat.of K K) f hf j).hom x) =
      (relativeSingularCohomology.map K (ModuleCat.of K K) (g ≫ f)
        (fun _ hx ↦ hf (hg hx)) j).hom x :=
  (congrArg (fun m ↦ ModuleCat.Hom.hom m x)
    (relativeSingularCohomology.map_comp K (ModuleCat.of K K) g f hg hf j)).symm

/-- Equal maps of pairs induce the same map on relative singular cohomology. -/
lemma map_congr_apply {Y' Y : TopCat.{0}} {f f' : Y' ⟶ Y} (hff' : f = f') {A' : Set Y'}
    {A : Set Y} (h : A' ⊆ f ⁻¹' A) (h' : A' ⊆ f' ⁻¹' A) (j : ℤ)
    (x : relativeSingularCohomology K (ModuleCat.of K K) Y A j) :
    (relativeSingularCohomology.map K (ModuleCat.of K K) f h j).hom x =
      (relativeSingularCohomology.map K (ModuleCat.of K K) f' h' j).hom x := by
  subst hff'; rfl

/-- The identity map of a pair induces the identity on relative singular cohomology. -/
lemma map_id_apply {Y : TopCat.{0}} {A : Set Y} (h : A ⊆ (𝟙 Y : Y ⟶ Y) ⁻¹' A) (j : ℤ)
    (x : relativeSingularCohomology K (ModuleCat.of K K) Y A j) :
    (relativeSingularCohomology.map K (ModuleCat.of K K) (𝟙 Y) h j).hom x = x := by
  rw [relativeSingularCohomology_map_eq_id K rfl h j]
  rfl

/-- If the map along `f` is injective for the pair `(Y', A'')`, it is for `(Y', A')`,
`A'' ⊆ A'`. -/
lemma injective_map_of_subset {Y' Y : TopCat.{0}} (f : Y' ⟶ Y) {A'' A' : Set Y'} {A : Set Y}
    (hA'' : A'' ⊆ f ⁻¹' A) (hA' : A' ⊆ f ⁻¹' A) (h : A'' ⊆ A') (j : ℤ)
    (hinj : Function.Injective (relativeSingularCohomology.map K (ModuleCat.of K K) f hA'' j).hom) :
    Function.Injective (relativeSingularCohomology.map K (ModuleCat.of K K) f hA' j).hom := by
  intro a b hab
  apply hinj
  have key : ∀ c, (relativeSingularCohomology.map K (ModuleCat.of K K) f hA'' j).hom c =
      (relativeSingularCohomology.map K (ModuleCat.of K K) (𝟙 Y')
        (show A'' ⊆ (𝟙 Y' : Y' ⟶ Y') ⁻¹' A' from h) j).hom
        ((relativeSingularCohomology.map K (ModuleCat.of K K) f hA' j).hom c) := fun c ↦ by
    rw [map_map_apply]
    exact map_congr_apply K (Category.id_comp f).symm _ _ _ _
  rw [key, key, hab]

/-- A homeomorphism induces an injection on the cohomology of pairs. -/
lemma injective_map_of_isIso {Y' Y : TopCat.{0}} (e : Y' ≅ Y) (A : Set Y) (j : ℤ) :
    Function.Injective
      (relativeSingularCohomology.map K (ModuleCat.of K K) e.hom (A' := e.hom ⁻¹' A)
        subset_rfl j).hom :=
  (relativeSingularCohomologyIsoOfIso K e A j).toLinearEquiv.injective

end Naturality

/-! ### Euclidean spaces are acyclic -/

section Contractible

open CategoryTheory

variable (K : Type) [Field K]

/-- A space homeomorphic to `ℝᴺ` has no cohomology in positive degrees. -/
theorem subsingleton_cohomology_of_homeomorph_euclidean {Z : TopCat.{0}} {N : ℕ}
    (e : Z ≃ₜ (Fin N → ℝ)) (k : ℕ) :
    Subsingleton (cohomologyWithSupports K (ModuleCat.of K K) Z Set.univ (k + 1 : ℕ)) := by
  let P : TopCat.{0} := TopCat.of (Fin 0 → ℝ)
  let i : P ⟶ Z := TopCat.ofHom (ContinuousMap.const _ (e.symm 0))
  let r : Z ⟶ P := TopCat.ofHom (ContinuousMap.const _ 0)
  have hri : i ≫ r = 𝟙 P := by
    ext x i
    exact Fin.elim0 i
  let H : TopCat.Homotopy (r ≫ i) (𝟙 Z) :=
    { toFun := fun p ↦ e.symm ((p.1 : ℝ) • e p.2)
      continuous_toFun := e.symm.continuous.comp
        ((continuous_subtype_val.comp continuous_fst).smul (e.continuous.comp continuous_snd))
      map_zero_left := fun z ↦ by
        simp [i, r]
        rfl
      map_one_left := fun z ↦ by simp }
  exact (cohomologyIsoOfHomotopy K i r hri H (k + 1 : ℕ)).toLinearEquiv.toEquiv
    |>.subsingleton_congr.2
    (subsingleton_cohomology_of_unique K P k)

end Contractible

/-! ### Powers of a degree-two class -/

section Powers

open CategoryTheory

variable (K : Type) [Field K]

/-- The cup product of absolute classes commutes with pull-back. -/
lemma map_cupUniv {Y' Y : TopCat.{0}} (g : Y' ⟶ Y) (p q : ℕ)
    (a : cohomologyWithSupports K (ModuleCat.of K K) Y Set.univ (2 * p : ℕ))
    (b : cohomologyWithSupports K (ModuleCat.of K K) Y Set.univ (2 * q : ℕ)) :
    (relativeSingularCohomology.map K (ModuleCat.of K K) g (compl_univ_subset_preimage g)
        (2 * (p + q) : ℕ)).hom (cupUniv K Y p q a b) =
      cupUniv K Y' p q
        ((relativeSingularCohomology.map K (ModuleCat.of K K) g (compl_univ_subset_preimage g)
          (2 * p : ℕ)).hom a)
        ((relativeSingularCohomology.map K (ModuleCat.of K K) g (compl_univ_subset_preimage g)
          (2 * q : ℕ)).hom b) := by
  simp only [cupUniv, LinearMap.compr₂_apply, LinearEquiv.coe_coe]
  rw [cohomologyWithSupports.map_congrIndex g (by rw [Set.univ_inter]) (by rw [Set.univ_inter])
    (by push_cast; ring) (compl_subset_preimage_compl
      (inter_subset_inter (subset_univ (g ⁻¹' Set.univ)) (subset_univ (g ⁻¹' Set.univ))))]
  rw [cohomologyWithSupports.map_cup g isClosed_univ isClosed_univ isClosed_univ isClosed_univ
    (subset_univ _) (subset_univ _)]

/-- The power `x^{k+1} ∈ H^{2(k+1)}(Y; K)` of a class `x ∈ H²(Y; K)`. -/
def cupPowSucc {Y : TopCat.{0}}
    (x : cohomologyWithSupports K (ModuleCat.of K K) Y Set.univ (2 * 1 : ℕ)) :
    (k : ℕ) → cohomologyWithSupports K (ModuleCat.of K K) Y Set.univ (2 * (k + 1) : ℕ)
  | 0 => x
  | k + 1 => cupUniv K Y (k + 1) 1 (cupPowSucc x k) x

/-- `x^1 = x`. -/
@[simp] lemma cupPowSucc_zero {Y : TopCat.{0}}
    (x : cohomologyWithSupports K (ModuleCat.of K K) Y Set.univ (2 * 1 : ℕ)) :
    cupPowSucc K x 0 = x := rfl

/-- `x^{k+2} = x^{k+1} ∪ x`. -/
lemma cupPowSucc_succ {Y : TopCat.{0}}
    (x : cohomologyWithSupports K (ModuleCat.of K K) Y Set.univ (2 * 1 : ℕ)) (k : ℕ) :
    cupPowSucc K x (k + 1) = cupUniv K Y (k + 1) 1 (cupPowSucc K x k) x := rfl

/-- Powers commute with pull-back. -/
lemma map_cupPowSucc {Y' Y : TopCat.{0}} (g : Y' ⟶ Y)
    (x : cohomologyWithSupports K (ModuleCat.of K K) Y Set.univ (2 * 1 : ℕ)) (k : ℕ) :
    (relativeSingularCohomology.map K (ModuleCat.of K K) g (compl_univ_subset_preimage g)
        (2 * (k + 1) : ℕ)).hom (cupPowSucc K x k) =
      cupPowSucc K ((relativeSingularCohomology.map K (ModuleCat.of K K) g
        (compl_univ_subset_preimage g) (2 * 1 : ℕ)).hom x) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [cupPowSucc_succ, cupPowSucc_succ, map_cupUniv, ih]

end Powers

/-! ### The top cohomology of `ℙⁿ⁺¹(ℂ)` is supported at a point -/

section TopDegree

open CategoryTheory cohomologyWithSupports

variable (K : Type) [Field K]

/-- `H^k(ℙⁿ⁺¹(ℂ) - [0 : ⋯ : 0 : 1]; K) = 0` for `k > 2n`. -/
lemma subsingleton_cohomology_basePointCompl (n k : ℕ) (hk : 2 * n < k) :
    Subsingleton (cohomologyWithSupports K (ModuleCat.of K K) (projectiveSpaceBasePointCompl n)
      Set.univ k) :=
  (cohomologyIsoOfHomotopy K (hyperplaneInclusion n) (hyperplaneRetraction n)
    (hyperplaneInclusion_comp_retraction n) (hyperplaneHomotopy n)
      k).toLinearEquiv.toEquiv.subsingleton_congr.2
    (subsingleton_cohomology_complexProjectiveSpace_of_lt K hk)

/-- In the top degree `2n + 2`, forgetting the supports `{p}` of a class of `ℙⁿ⁺¹(ℂ)` at the
base point `p` is injective. -/
theorem injective_forget_basePoint (n : ℕ) {S S' : Set (complexProjectiveSpace (n + 1))}
    (hS : S = {projectiveSpaceBasePoint n}) (hSS' : S ⊆ S') (hS' : S' = Set.univ) {k : ℤ}
    (hk : k = ((2 * n + 1 + 1 : ℕ) : ℤ)) :
    Function.Injective (forget K (ModuleCat.of K K) _ hSS' k).hom := by
  subst hS hS' hk
  have := subsingleton_cohomology_basePointCompl K n (2 * n + 1) (by omega)
  exact injective_of_exact_of_subsingleton
    (f := (delta K _ {projectiveSpaceBasePoint n} (2 * n + 1)).toAddMonoidHom)
    (g := (toCohomology K (ModuleCat.of K K) _ _ (2 * n + 1 + 1 : ℕ)).hom.toAddMonoidHom)
    (exact_delta_toCohomology K _ _ (2 * n + 1))

/-- Every top-degree class of `ℙⁿ⁺¹(ℂ)` comes from a class supported at the base point. -/
theorem exists_toCohomology_basePoint_eq (n k : ℕ) (hk : k = 2 * n + 1 + 1)
    (y : cohomologyWithSupports K (ModuleCat.of K K) (complexProjectiveSpace (n + 1)) Set.univ
      k) :
    ∃ z, (toCohomology K (ModuleCat.of K K) _ {projectiveSpaceBasePoint n} k).hom z = y := by
  subst hk
  have := subsingleton_cohomology_basePointCompl K n (2 * n + 1 + 1) (by omega)
  exact (exact_toCohomology_restrictCompl K _ {projectiveSpaceBasePoint n} (2 * n + 1 + 1) y).1
    (Subsingleton.elim _ _)

end TopDegree

/-! ### The affine chart -/

section AffineChart

open CategoryTheory cohomologyWithSupports

variable (K : Type) [Field K]

/-- The affine chart `u ↦ [u : 1]`, `ℂⁿ⁺¹ → ℙⁿ⁺¹(ℂ)`. -/
def affineChartMap (n : ℕ) : TopCat.of (Fin (n + 1) → ℂ) ⟶ complexProjectiveSpace (n + 1) :=
  TopCat.ofHom ⟨fun u ↦ ((projectiveSpaceChart n).symm u).1,
    continuous_subtype_val.comp (projectiveSpaceChart n).symm.continuous⟩

/-- The affine chart sends `u` to the projection onto the line `ℂ (u, 1)`. -/
lemma affineChartMap_apply_val (n : ℕ) (u : Fin (n + 1) → ℂ) :
    (affineChartMap n u).1 = lineProjection (Fin.snoc (α := fun _ ↦ ℂ) u 1) := rfl

/-- The affine chart sends `u` to the base point iff `u = 0`. -/
lemma affineChartMap_eq_basePoint_iff (n : ℕ) (u : Fin (n + 1) → ℂ) :
    affineChartMap n u = projectiveSpaceBasePoint n ↔ u = 0 := by
  have h0 : (projectiveSpaceChart n).symm 0 = ⟨_, projectiveSpaceBasePoint_mem_cell n⟩ :=
    (projectiveSpaceChart n).symm_apply_eq.2 (projectiveSpaceChart_basePoint n).symm
  constructor
  · intro h
    have h' : (projectiveSpaceChart n).symm u = ⟨_, projectiveSpaceBasePoint_mem_cell n⟩ :=
      Subtype.ext h
    rw [(projectiveSpaceChart n).symm_apply_eq] at h'
    rw [h', projectiveSpaceChart_basePoint]
  · rintro rfl
    exact congrArg Subtype.val h0

/-- The affine chart maps `ℂⁿ⁺¹ - 0` into the complement of the base point. -/
lemma compl_zero_subset_preimage_affineChartMap (n : ℕ) :
    ({0} : Set (Fin (n + 1) → ℂ))ᶜ ⊆
      affineChartMap n ⁻¹' ({projectiveSpaceBasePoint n} : Set (complexProjectiveSpace (n + 1)))ᶜ :=
  fun u hu h ↦ hu ((affineChartMap_eq_basePoint_iff n u).1 h)

/-- Restriction along the affine chart is injective on classes supported at the base point. -/
theorem injective_map_affineChartMap (n : ℕ) (k : ℤ) :
    Function.Injective (relativeSingularCohomology.map K (ModuleCat.of K K) (affineChartMap n)
      (compl_zero_subset_preimage_affineChartMap n) k).hom := by
  set b := projectiveSpaceBasePoint n
  let e : TopCat.of (Fin (n + 1) → ℂ) ≅ TopCat.of (projectiveSpaceCell n) :=
    TopCat.isoOfHomeo (projectiveSpaceChart n).symm
  let ι := subspaceInclusion (complexProjectiveSpace (n + 1)) (projectiveSpaceCell n)
  have hf : affineChartMap n = e.hom ≫ ι := by ext u; rfl
  have hX : ({b} : Set (complexProjectiveSpace (n + 1))) ⊆ projectiveSpaceCell n :=
    Set.singleton_subset_iff.2 (projectiveSpaceBasePoint_mem_cell n)
  have hι : (ι ⁻¹' {b})ᶜ ⊆ ι ⁻¹' ({b} : Set (complexProjectiveSpace (n + 1)))ᶜ :=
    Set.preimage_compl.ge
  have he : e.hom ⁻¹' (ι ⁻¹' {b})ᶜ ⊆ e.hom ⁻¹' (ι ⁻¹' {b})ᶜ := subset_rfl
  have h1 : Function.Injective (relativeSingularCohomology.map K (ModuleCat.of K K) (e.hom ≫ ι)
      (A' := e.hom ⁻¹' (ι ⁻¹' {b})ᶜ) (A := ({b} : Set (complexProjectiveSpace (n + 1)))ᶜ)
      (fun _ hx ↦ hι (he hx)) k).hom := by
    intro x y hxy
    rw [← map_map_apply K e.hom ι he hι k x, ← map_map_apply K e.hom ι he hι k y] at hxy
    exact (excisionIso K (isOpen_projectiveSpaceCell n) isClosed_singleton hX k)
      |>.toLinearEquiv.injective
      (injective_map_of_isIso K e _ k hxy)
  have hsub : e.hom ⁻¹' (ι ⁻¹' {b})ᶜ ⊆ ({0} : Set (Fin (n + 1) → ℂ))ᶜ := by
    rintro _ hu rfl
    exact hu ((affineChartMap_eq_basePoint_iff n 0).2 rfl)
  exact injective_map_of_subset K (affineChartMap n) (A'' := e.hom ⁻¹' (ι ⁻¹' {b})ᶜ)
    (A := ({b} : Set (complexProjectiveSpace (n + 1)))ᶜ) (fun u hu ↦ hu) _ hsub k
    fun x y hxy ↦ h1 ((map_congr_apply K hf _ _ k x).symm.trans
      (hxy.trans (map_congr_apply K hf _ _ k y)))

end AffineChart

/-! ### The local cup product on `ℂʳ × ℂˢ` -/

section Product

open CategoryTheory cohomologyWithSupports ThomClass

variable (K : Type) [Field K]

/-- `H^{2r+2}(ℂʳ⁺¹, ℂʳ⁺¹ - 0; K)` is one-dimensional. -/
lemma finrank_cohomologyWithSupports_complex (r : ℕ) :
    Module.finrank K (cohomologyWithSupports K (ModuleCat.of K K) (TopCat.of (Fin (r + 1) → ℂ))
      {0} (2 * (r + 1) : ℕ)) = 1 := by
  let L := ContinuousLinearEquiv.ofFinrankEq (finrank_fun_complex_eq r)
  let e : TopCat.of (Fin (r + 1) → ℂ) ≅ TopCat.of (Fin (2 * r + 1 + 1) → ℝ) :=
    TopCat.isoOfHomeo L.toHomeomorph
  have h := (relativeSingularCohomologyIsoOfIso K e ({0} : Set (Fin (2 * r + 1 + 1) → ℝ))ᶜ
    ((2 * r + 1 + 1 : ℕ))).toLinearEquiv.finrank_eq
  have hs : e.hom ⁻¹' ({0} : Set (Fin (2 * r + 1 + 1) → ℝ))ᶜ = ({0} : Set (Fin (r + 1) → ℂ))ᶜ := by
    ext u
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
    exact not_congr (L.map_eq_zero_iff (x := u))
  rw [hs, (cohomologyWithSupportsEuclideanEquiv K (2 * r + 1)).finrank_eq,
    Module.finrank_self] at h
  rw [show 2 * (r + 1) = 2 * r + 1 + 1 by ring]
  exact h.symm

/-- There is a relative `2r`-cocycle of `(ℂʳ, ℂʳ - 0)` taking the value `1` on every affine simplex
oriented around `0` for `complexOrientationBasis r`. -/
lemma exists_relCocycle_complexOrientation (r : ℕ) :
    ∃ α ∈ relCocycles K ({0}ᶜ : Set (Fin r → ℂ)) (2 * r),
      ∀ v, IsOrientedSimplexAroundZero (complexOrientationBasis r) v → α (affineSimplex v) = 1 := by
  obtain ⟨α, hα, h1⟩ := exists_relCocycles_eval_affineSimplex (R := K) r
  refine ⟨α, hα, fun v hv ↦ ?_⟩
  simpa [SingularCochain.eval, linearCombination_single] using h1 v hv

/-- The class of a relative cocycle taking the value `1` on a relative cycle is nonzero. -/
lemma relCohomology_mk_ne_zero {Y : TopCat.{0}} {A : Set Y} {n : ℕ} (α : relCocycles K A n)
    (σ : Simplex Y n) (hσ : ∀ t : stdSimplex ℝ (Fin (n + 1)), (∃ i, t i = 0) → σ t ∈ A)
    (h1 : (α : Simplex Y n → K) σ = 1) :
    (relativeSingularCohomologyEquiv K A n).symm (Submodule.Quotient.mk α) ≠ 0 := by
  intro h
  rw [LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h
  have h0 := eval_single_eq_zero_of_mem_relCoboundaries (R := K) σ hσ _ h
  simp only [SingularCochain.eval, linearCombination_single, one_smul, Submodule.coe_subtype] at h0
  exact one_ne_zero (h1.symm.trans h0)

/-- The pull-back along `g` of the class of a relative cocycle `φ` is the class of the pulled-back
cocycle. -/
lemma pullback_symm_mk {Y' Y : TopCat.{0}} (g : Y' ⟶ Y) (X : Set Y) (n : ℕ)
    (φ : relCocycles K Xᶜ n) :
    (cohomologyWithSupports.pullback K (ModuleCat.of K K) g X n).hom
        ((relativeSingularCohomologyEquiv K Xᶜ n).symm (Submodule.Quotient.mk φ)) =
      (relativeSingularCohomologyEquiv K (g ⁻¹' X)ᶜ n).symm
        (Submodule.Quotient.mk ⟨cochainPullback K g n φ.1,
          cochainPullback_mem_relCocycles g (A' := (g ⁻¹' X)ᶜ) (A := Xᶜ) Set.preimage_compl.ge
            φ.2⟩) := by
  rw [LinearEquiv.eq_symm_apply]
  refine (relativeSingularCohomologyEquiv_map (R := K) g (A' := (g ⁻¹' X)ᶜ) (A := Xᶜ)
    Set.preimage_compl.ge n _).trans ?_
  rw [LinearEquiv.apply_symm_apply]
  exact relCohomologyMap_mk _ _ _ _

/-- The cup product of the classes of relative cocycles `φ` and `ψ` is the class of their relative
cup product. -/
lemma cup_symm_mk {Y : TopCat.{0}} {X W : Set Y} (hX : IsClosed X) (hW : IsClosed W) (p q : ℕ)
    (φ : relCocycles K Xᶜ p) (ψ : relCocycles K Wᶜ q) :
    cup K Y hX hW p q ((relativeSingularCohomologyEquiv K Xᶜ p).symm (Submodule.Quotient.mk φ))
        ((relativeSingularCohomologyEquiv K Wᶜ q).symm (Submodule.Quotient.mk ψ)) =
      congrIndex K Y (Set.compl_inter X W).symm (Nat.cast_add p q)
        ((relativeSingularCohomologyEquiv K (Xᶜ ∪ Wᶜ) (p + q)).symm (Submodule.Quotient.mk
          (relCupCocycles hX.isOpen_compl hW.isOpen_compl p q (p + q) rfl φ ψ))) := by
  rw [cup_natCast, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, relCup_mk]

/-- **Product of local classes.** For `R, S ≥ 1` and nonzero `a ∈ H^{2R}(ℂᴿ, ℂᴿ - 0; K)` and
`b ∈ H^{2S}(ℂˢ, ℂˢ - 0; K)`, the cup product `pr₁^* a ∪ pr₂^* b` is nonzero in
`H^{2R+2S}(ℂᴿ × ℂˢ, ℂᴿ × ℂˢ - 0; K)`. -/
theorem cup_pullback_fst_snd_ne_zero {R S : ℕ} (hR : R ≠ 0) (hS : S ≠ 0)
    (a : cohomologyWithSupports K (ModuleCat.of K K) (TopCat.of (Fin R → ℂ)) {0}
      (2 * R : ℕ)) (ha : a ≠ 0)
    (b : cohomologyWithSupports K (ModuleCat.of K K) (TopCat.of (Fin S → ℂ)) {0}
      (2 * S : ℕ)) (hb : b ≠ 0) :
    cup K (TopCat.of ((Fin R → ℂ) × (Fin S → ℂ)))
      ((isClosed_singleton (x := (0 : Fin R → ℂ))).preimage
        (ConcreteCategory.hom (TopCat.ofHom (ContinuousMap.fst :
          C((Fin R → ℂ) × (Fin S → ℂ), Fin R → ℂ)))).continuous)
      ((isClosed_singleton (x := (0 : Fin S → ℂ))).preimage
        (ConcreteCategory.hom (TopCat.ofHom (ContinuousMap.snd :
          C((Fin R → ℂ) × (Fin S → ℂ), Fin S → ℂ)))).continuous)
      (2 * R : ℕ) (2 * S : ℕ)
      ((cohomologyWithSupports.pullback K (ModuleCat.of K K) (TopCat.ofHom (ContinuousMap.fst :
        C((Fin R → ℂ) × (Fin S → ℂ), Fin R → ℂ))) {0} _).hom a)
      ((cohomologyWithSupports.pullback K (ModuleCat.of K K) (TopCat.ofHom (ContinuousMap.snd :
        C((Fin R → ℂ) × (Fin S → ℂ), Fin S → ℂ))) {0} _).hom b) ≠ 0 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hR
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hS
  obtain ⟨α, hα, hα1⟩ := exists_relCocycle_complexOrientation K (r + 1)
  obtain ⟨β, hβ, hβ1⟩ := exists_relCocycle_complexOrientation K (s + 1)
  obtain ⟨vα, hvα⟩ := exists_isOrientedSimplexAroundZero (complexOrientationBasis (r + 1))
  obtain ⟨vβ, hvβ⟩ := exists_isOrientedSimplexAroundZero (complexOrientationBasis (s + 1))
  have hA := relCohomology_mk_ne_zero K (Y := TopCat.of (Fin (r + 1) → ℂ)) ⟨α, hα⟩
    (affineSimplex vα) (fun t ht ↦ hvα.affineSimplex_ne_zero t ht) (hα1 _ hvα)
  have hB := relCohomology_mk_ne_zero K (Y := TopCat.of (Fin (s + 1) → ℂ)) ⟨β, hβ⟩
    (affineSimplex vβ) (fun t ht ↦ hvβ.affineSimplex_ne_zero t ht) (hβ1 _ hvβ)
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' _ hA).1
    (finrank_cohomologyWithSupports_complex K r) a
  obtain ⟨c', rfl⟩ := (finrank_eq_one_iff_of_nonzero' _ hB).1
    (finrank_cohomologyWithSupports_complex K s) b
  have hc : c ≠ 0 := by
    rintro rfl
    exact ha (zero_smul _ _)
  have hc' : c' ≠ 0 := by
    rintro rfl
    exact hb (zero_smul _ _)
  simp only [map_smul]
  refine smul_ne_zero hc' ?_
  rw [LinearMap.smul_apply]
  refine smul_ne_zero hc ?_
  rw [pullback_symm_mk, pullback_symm_mk, cup_symm_mk]
  rw [Ne, LinearEquiv.map_eq_zero_iff]
  obtain ⟨w, hw⟩ := exists_isOrientedSimplexAroundZero
    ((((complexOrientationBasis (r + 1)).prod (complexOrientationBasis (s + 1))).reindex
      finSumFinEquiv).reindex (finCongr (rfl : 2 * (r + 1) + 2 * (s + 1) = _)))
  refine relCohomology_mk_ne_zero K
    (Y := TopCat.of ((Fin (r + 1) → ℂ) × (Fin (s + 1) → ℂ))) _ (affineSimplex w) (fun t ht ↦ ?_) ?_
  · have h0 := hw.affineSimplex_ne_zero t ht
    by_contra hmem
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff,
      not_or, not_not] at hmem
    exact h0 (Prod.ext hmem.1 hmem.2)
  · exact relCupCochain_cochainPullback_fst_snd_affineSimplex rfl _ _ hα hα1 hβ hβ1 hw

end Product

/-! ### Coordinate permutations, linear embeddings and a chart of `ℙⁿ⁺² - p` -/

section Geometry

open CategoryTheory ComplexConjugate

/-- Permuting the rows and columns of `lineProjection v` by `σ` gives `lineProjection (v ∘ σ)`. -/
lemma lineProjection_comp_perm {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (v : Fin (n + 1) → ℂ) :
    (fun i j ↦ lineProjection v (σ i) (σ j)) = lineProjection (v ∘ σ) := by
  ext i j
  simp only [lineProjection, Function.comp]
  congr 1
  exact (Equiv.sum_comp σ (fun k ↦ v k * conj (v k))).symm

/-- `v ∘ σ` is nonzero for `v ≠ 0`. -/
lemma comp_perm_ne_zero {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) {v : Fin (n + 1) → ℂ}
    (hv : v ≠ 0) : v ∘ σ ≠ 0 := fun h ↦
  hv (by ext k; simpa using congrFun h (σ.symm k))

/-- Permuting the rows and columns of a point of `ℙⁿ(ℂ)` by `σ` gives a point of `ℙⁿ(ℂ)`. -/
lemma permMatrix_mem {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (P : complexProjectiveSpace n) :
    (fun i j ↦ P.1 (σ i) (σ j)) ∈ lineProjections n := by
  obtain ⟨v, hv, hP⟩ := P.2
  rw [← hP, lineProjection_comp_perm]
  exact lineProjection_mem_lineProjections (comp_perm_ne_zero σ hv)

/-- The homeomorphism of `ℙⁿ(ℂ)` permuting the homogeneous coordinates by `σ`:
`[v] ↦ [v ∘ σ]`. -/
def permHomeomorph {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    complexProjectiveSpace n ≃ₜ complexProjectiveSpace n where
  toFun P := ⟨_, permMatrix_mem σ P⟩
  invFun P := ⟨_, permMatrix_mem σ.symm P⟩
  left_inv P := Subtype.ext (by ext i j; simp)
  right_inv P := Subtype.ext (by ext i j; simp)
  continuous_toFun := (continuous_pi fun i ↦ continuous_pi fun j ↦
    continuous_entry continuous_subtype_val _ _).subtype_mk _
  continuous_invFun := (continuous_pi fun i ↦ continuous_pi fun j ↦
    continuous_entry continuous_subtype_val _ _).subtype_mk _

/-- `permHomeomorph σ` sends the line `ℂ v` to the line `ℂ (v ∘ σ)`. -/
lemma permHomeomorph_apply_val {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (P : complexProjectiveSpace n) {v : Fin (n + 1) → ℂ} (hP : P.1 = lineProjection v) :
    (permHomeomorph σ P).1 = lineProjection (v ∘ σ) := by
  change (fun i j ↦ P.1 (σ i) (σ j)) = _
  rw [hP, lineProjection_comp_perm]

/-- The inclusion `ℙⁿ(ℂ) ⟶ ℙⁿ⁺¹(ℂ)` of the hyperplane `{x_{n+1} = 0}`. -/
def hyperplaneEmbedding (n : ℕ) : complexProjectiveSpace n ⟶ complexProjectiveSpace (n + 1) :=
  hyperplaneInclusion n ≫ subspaceInclusion _ _

/-- `hyperplaneEmbedding n` extends the matrix of a point by zero. -/
lemma hyperplaneEmbedding_apply_val (n : ℕ) (P : complexProjectiveSpace n) :
    (hyperplaneEmbedding n P).1 = hyperplaneMatrix n P.1 := rfl

/-- The inclusion `ℙ¹(ℂ) ⟶ ℙᵐ⁺¹(ℂ)` of the line of the first two coordinates. -/
def lineEmbedding : (m : ℕ) → complexProjectiveSpace 1 ⟶ complexProjectiveSpace (m + 1)
  | 0 => 𝟙 _
  | m + 1 => lineEmbedding m ≫ hyperplaneEmbedding (m + 1)

/-- The vector `(c₀, c₁, 0, …, 0) ∈ ℂᵐ⁺²`. -/
def zeroPad (m : ℕ) (c : Fin 2 → ℂ) : Fin (m + 2) → ℂ :=
  fun k ↦ if h : (k : ℕ) < 2 then c ⟨k, h⟩ else 0

/-- Appending `0` to `(c₀, c₁, 0, …, 0) ∈ ℂᵐ⁺²` gives `(c₀, c₁, 0, …, 0) ∈ ℂᵐ⁺³`. -/
lemma snoc_zeroPad (m : ℕ) (c : Fin 2 → ℂ) :
    (Fin.snoc (α := fun _ ↦ ℂ) (zeroPad m c) 0 : Fin (m + 3) → ℂ) = zeroPad (m + 1) c := by
  ext k
  induction k using Fin.lastCases with
  | last => simp [zeroPad]
  | cast k => simp [zeroPad]

/-- `lineEmbedding m` sends the line `ℂ c` to the line `ℂ (c₀, c₁, 0, …, 0)`. -/
lemma lineEmbedding_apply_val (m : ℕ) (P : complexProjectiveSpace 1) {c : Fin 2 → ℂ}
    (hP : P.1 = lineProjection c) : (lineEmbedding m P).1 = lineProjection (zeroPad m c) := by
  induction m with
  | zero =>
    change P.1 = _
    rw [hP]
    congr 1
    ext k
    simp [zeroPad, k.isLt]
  | succ m ih =>
    change hyperplaneMatrix (m + 1) (lineEmbedding m P).1 = _
    rw [ih, hyperplaneMatrix_lineProjection, snoc_zeroPad]

/-- The vector `(u, 1, t) ∈ ℂᵐ⁺³`. -/
def chartVector (m : ℕ) (u : Fin (m + 1) → ℂ) (t : Fin 1 → ℂ) : Fin (m + 3) → ℂ :=
  Fin.snoc (α := fun _ ↦ ℂ) (Fin.snoc (α := fun _ ↦ ℂ) u 1) (t 0)

/-- The vector `(u, 1, t)` is nonzero. -/
lemma chartVector_ne_zero (m : ℕ) (u : Fin (m + 1) → ℂ) (t : Fin 1 → ℂ) :
    chartVector m u t ≠ 0 := fun h ↦
  snoc_one_ne_zero m u (by ext k; simpa [chartVector] using congrFun h (Fin.castSucc k))

/-- Dropping the last coordinate of `(u, 1, t)` gives `(u, 1)`. -/
lemma init_chartVector (m : ℕ) (u : Fin (m + 1) → ℂ) (t : Fin 1 → ℂ) :
    Fin.init (chartVector m u t) = Fin.snoc (α := fun _ ↦ ℂ) u 1 := by
  simp [chartVector, Fin.init_snoc]

/-- The point `[u : 1 : t]` of `ℙᵐ⁺²(ℂ)` is not the base point. -/
lemma chartPoint_mem_compl (m : ℕ) (u : Fin (m + 1) → ℂ) (t : Fin 1 → ℂ) :
    (⟨lineProjection (chartVector m u t), lineProjection_mem_lineProjections
      (chartVector_ne_zero m u t)⟩ : complexProjectiveSpace (m + 2)) ∈
      ({projectiveSpaceBasePoint (m + 1)} : Set (complexProjectiveSpace (m + 2)))ᶜ := fun h ↦ by
  have h' := congrArg Subtype.val h
  change lineProjection _ = lineProjection _ at h'
  rw [lineProjection_eq_single_last_iff (chartVector_ne_zero m u t), init_chartVector] at h'
  exact snoc_one_ne_zero m u h'

/-- `(u, t) ↦ (u, 1, t)` is continuous. -/
lemma continuous_chartVector (m : ℕ) :
    Continuous fun x : (Fin (m + 1) → ℂ) × (Fin 1 → ℂ) ↦ chartVector m x.1 x.2 :=
  Continuous.finSnoc (Continuous.finSnoc continuous_fst continuous_const)
    ((continuous_apply 0).comp continuous_snd)

/-- The chart `(u, t) ↦ [u : 1 : t]` of `ℙᵐ⁺²(ℂ) - [0 : ⋯ : 0 : 1]` around the point
`[0 : ⋯ : 0 : 1 : 0]`. -/
def complChart (m : ℕ) :
    TopCat.of ((Fin (m + 1) → ℂ) × (Fin 1 → ℂ)) ⟶ projectiveSpaceBasePointCompl (m + 1) :=
  TopCat.ofHom ⟨fun x ↦ ⟨_, chartPoint_mem_compl m x.1 x.2⟩,
    ((continuous_lineProjection_comp (continuous_chartVector m)
      (fun x ↦ chartVector_ne_zero m x.1 x.2)).subtype_mk _).subtype_mk _⟩

/-- `complChart m` sends `(u, t)` to the projection onto the line `ℂ (u, 1, t)`. -/
lemma complChart_apply_val_val (m : ℕ) (x : (Fin (m + 1) → ℂ) × (Fin 1 → ℂ)) :
    (complChart m x).1.1 = lineProjection (chartVector m x.1 x.2) := rfl

/-- The retraction sends the line `ℂ v`, with `Fin.init v ≠ 0`, to the line `ℂ (Fin.init v)`. -/
lemma hyperplaneRetraction_apply_val (n : ℕ) (x : projectiveSpaceBasePointCompl n)
    {v : Fin (n + 2) → ℂ} (hv : v ≠ 0) (hi : Fin.init v ≠ 0) (hx : x.1.1 = lineProjection v) :
    (hyperplaneRetraction n x).1 = lineProjection (Fin.init v) := by
  change (fun i j ↦ x.1.1 (Fin.castSucc i) (Fin.castSucc j) /
      (1 - x.1.1 (Fin.last (n + 1)) (Fin.last (n + 1)))) = _
  rw [hx, one_sub_lineProjection_last hv]
  have h1 := sum_mul_conj_ne_zero hv
  have h2 := sum_mul_conj_ne_zero hi
  ext i j
  simp only [lineProjection, Fin.init]
  field_simp

/-- The retraction sends `[u : 1 : t]` to `[u : 1]`. -/
lemma complChart_comp_hyperplaneRetraction (m : ℕ) :
    complChart m ≫ hyperplaneRetraction (m + 1) =
      TopCat.ofHom (ContinuousMap.fst : C((Fin (m + 1) → ℂ) × (Fin 1 → ℂ), Fin (m + 1) → ℂ)) ≫
        affineChartMap m := by
  refine ConcreteCategory.hom_ext _ _ fun x ↦ Subtype.ext ?_
  change (hyperplaneRetraction (m + 1) (complChart m x)).1 = (affineChartMap m x.1).1
  rw [hyperplaneRetraction_apply_val (m + 1) _ (chartVector_ne_zero m x.1 x.2)
    (by rw [init_chartVector]; exact snoc_one_ne_zero m x.1) (complChart_apply_val_val m x),
    init_chartVector, affineChartMap_apply_val]

/-- The last diagonal entry of `lineProjection v` vanishes iff the last coordinate of `v` does. -/
lemma lineProjection_last_eq_zero_iff {n : ℕ} {v : Fin (n + 1) → ℂ} (hv : v ≠ 0) :
    lineProjection v (Fin.last n) (Fin.last n) = 0 ↔ v (Fin.last n) = 0 := by
  rw [lineProjection, div_eq_zero_iff, or_iff_left (sum_mul_conj_ne_zero hv), mul_eq_zero,
    map_eq_zero, or_self]

/-- The reversal `k ↦ m + 2 - k` of the coordinates of `ℙᵐ⁺²(ℂ)`. -/
abbrev reversePerm (m : ℕ) : Equiv.Perm (Fin (m + 3)) := Fin.revPerm

/-- The line `[c₀ : c₁] ↦ [0 : ⋯ : 0 : c₁ : c₀]` of `ℙᵐ⁺²(ℂ)` through the base point
`[0 : ⋯ : 0 : 1]` and the point `[0 : ⋯ : 0 : 1 : 0]`. -/
def lastLine (m : ℕ) : complexProjectiveSpace 1 ⟶ complexProjectiveSpace (m + 2) :=
  lineEmbedding (m + 1) ≫
    TopCat.ofHom ⟨permHomeomorph (reversePerm m), (permHomeomorph (reversePerm m)).continuous⟩

/-- Reversing the coordinates of `(t, 1, 0, …, 0)` gives `(0, …, 0, 1, t)`. -/
lemma zeroPad_comp_rev (m : ℕ) (t : Fin 1 → ℂ) :
    zeroPad (m + 1) (Fin.snoc (α := fun _ ↦ ℂ) t 1) ∘ (reversePerm m) = chartVector m 0 t := by
  ext k
  simp only [Function.comp_apply, zeroPad, chartVector]
  induction k using Fin.lastCases with
  | last =>
    have h0 : ((reversePerm m (Fin.last (m + 2)) : Fin (m + 3)) : ℕ) = 0 := by
      simp
    rw [dite_eq_left (by omega), Fin.snoc_last]
    have : (⟨_, (by omega : ((reversePerm m (Fin.last (m + 2)) : Fin (m + 3)) : ℕ) < 2)⟩ :
      Fin 2) = Fin.castSucc 0 := Fin.ext (by simp)
    rw [this, Fin.snoc_castSucc]
  | cast k =>
    induction k using Fin.lastCases with
    | last =>
      have h1 : ((reversePerm m (Fin.castSucc (Fin.last (m + 1))) : Fin (m + 3)) : ℕ) = 1 := by
        simp
      rw [dite_eq_left (by omega), Fin.snoc_castSucc, Fin.snoc_last]
      have : (⟨_, (by omega : ((reversePerm m (Fin.castSucc (Fin.last (m + 1))) :
        Fin (m + 3)) : ℕ) < 2)⟩ : Fin 2) = Fin.last 1 := Fin.ext (by simp)
      rw [this, Fin.snoc_last]
    | cast k =>
      have h2 : 2 ≤ ((reversePerm m (Fin.castSucc (Fin.castSucc k)) : Fin (m + 3)) : ℕ) := by
        simp only [reversePerm, Fin.revPerm_apply, Fin.val_rev, Fin.val_castSucc]
        omega
      rw [dite_eq_right (by omega), Fin.snoc_castSucc, Fin.snoc_castSucc, Pi.zero_apply]

/-- The axis `t ↦ (0, t)` of `ℂᵐ⁺¹ × ℂ`. -/
def axisInclusion (m : ℕ) : TopCat.of (Fin 1 → ℂ) ⟶ TopCat.of ((Fin (m + 1) → ℂ) × (Fin 1 → ℂ)) :=
  TopCat.ofHom ⟨fun t ↦ ((0 : Fin (m + 1) → ℂ), t), by fun_prop⟩

/-- `lastLine m` sends `[t : 1]` to `[0 : ⋯ : 0 : 1 : t]`, the image of `(0, t)` under
`complChart m`. -/
lemma affineChartMap_comp_lastLine (m : ℕ) :
    affineChartMap 0 ≫ lastLine m =
      axisInclusion m ≫ complChart m ≫ subspaceInclusion _ _ := by
  refine ConcreteCategory.hom_ext _ _ fun t ↦ Subtype.ext ?_
  change (permHomeomorph (reversePerm m) (lineEmbedding (m + 1) (affineChartMap 0 t))).1 =
    lineProjection (chartVector m 0 t)
  rw [permHomeomorph_apply_val _ _
    (lineEmbedding_apply_val (m + 1) _ (affineChartMap_apply_val 0 t)), zeroPad_comp_rev]

end Geometry

/-! ### Restriction to linear subspaces -/

section Restriction

open CategoryTheory cohomologyWithSupports

variable (K : Type) [Field K]

/-- Two factorisations `g ≫ f = g' ≫ f'` of a map of pairs induce the same map on relative singular
cohomology. -/
lemma map_map_eq {Y'' Y₁ Y₂ Y : TopCat.{0}} (g : Y'' ⟶ Y₁) (f : Y₁ ⟶ Y) (g' : Y'' ⟶ Y₂)
    (f' : Y₂ ⟶ Y) (hgf : g ≫ f = g' ≫ f') {A'' : Set Y''} {A₁ : Set Y₁} {A₂ : Set Y₂}
    {A : Set Y} (hg : A'' ⊆ g ⁻¹' A₁) (hf : A₁ ⊆ f ⁻¹' A) (hg' : A'' ⊆ g' ⁻¹' A₂)
    (hf' : A₂ ⊆ f' ⁻¹' A) (j : ℤ) (x : relativeSingularCohomology K (ModuleCat.of K K) Y A j) :
    (relativeSingularCohomology.map K (ModuleCat.of K K) g hg j).hom
        ((relativeSingularCohomology.map K (ModuleCat.of K K) f hf j).hom x) =
      (relativeSingularCohomology.map K (ModuleCat.of K K) g' hg' j).hom
        ((relativeSingularCohomology.map K (ModuleCat.of K K) f' hf' j).hom x) := by
  rw [map_map_apply, map_map_apply]
  exact map_congr_apply K hgf _ _ j x

/-- Forgetting supports along an equality of sets is injective. -/
lemma injective_forget_of_eq {Y : TopCat.{0}} {S S' : Set Y} (h : S ⊆ S') (h' : S' ⊆ S) (j : ℤ) :
    Function.Injective (forget K (ModuleCat.of K K) Y h j).hom := fun a b hab ↦ by
  have key : ∀ c, (forget K (ModuleCat.of K K) Y h' j).hom
      ((forget K (ModuleCat.of K K) Y h j).hom c) = c := fun c ↦
    (map_map_apply K _ _ _ _ j c).trans
      ((map_congr_apply K (Category.id_comp _) _ (fun _ hx ↦ hx) j c).trans
        (map_id_apply K (fun _ hx ↦ hx) j c))
  rw [← key a, ← key b, hab]

/-- Restriction `H^k(ℙⁿ⁺¹(ℂ); K) → H^k(ℙⁿ(ℂ); K)` to the hyperplane is bijective for
`k ≠ 2n + 2` and `k + 1 ≠ 2n + 2`. -/
theorem bijective_map_hyperplaneEmbedding (n k : ℕ) (hk : k ≠ 2 * n + 1 + 1)
    (hk' : k + 1 ≠ 2 * n + 1 + 1) :
    Function.Bijective (relativeSingularCohomology.map K (ModuleCat.of K K) (hyperplaneEmbedding n)
      (compl_univ_subset_preimage _) k).hom := by
  have hb := bijective_restrictCompl_singleton K
    (isClosed_singleton (x := projectiveSpaceBasePoint n)) (isOpen_projectiveSpaceCell n)
    (projectiveSpaceBasePoint_mem_cell n)
    (projectiveSpaceCellHomeomorph n) (projectiveSpaceCellHomeomorph_basePoint n) hk hk'
  have hi := (cohomologyIsoOfHomotopy K (hyperplaneInclusion n) (hyperplaneRetraction n)
    (hyperplaneInclusion_comp_retraction n) (hyperplaneHomotopy n) k).toLinearEquiv.bijective
  have heq : ⇑(relativeSingularCohomology.map K (ModuleCat.of K K) (hyperplaneEmbedding n)
      (compl_univ_subset_preimage _) k).hom =
      ⇑(cohomologyIsoOfHomotopy K (hyperplaneInclusion n) (hyperplaneRetraction n)
        (hyperplaneInclusion_comp_retraction n) (hyperplaneHomotopy n) k).toLinearEquiv ∘
      ⇑(restrictCompl K _ {projectiveSpaceBasePoint n} k).hom :=
    funext fun x ↦ (map_map_apply K (hyperplaneInclusion n) (subspaceInclusion _ _)
      (compl_univ_subset_preimage _) (compl_univ_subset_preimage_compl_univ _ _) k x).symm
  rw [heq]
  exact hi.comp hb

/-- Restriction `H²(ℙᵐ⁺¹(ℂ); K) → H²(ℙ¹(ℂ); K)` along `lineEmbedding m` is injective. -/
theorem injective_map_lineEmbedding (m : ℕ) :
    Function.Injective (relativeSingularCohomology.map K (ModuleCat.of K K) (lineEmbedding m)
      (compl_univ_subset_preimage _) (2 * 1 : ℕ)).hom := by
  induction m with
  | zero =>
    intro a b h
    exact (map_id_apply K _ _ a).symm.trans (h.trans (map_id_apply K _ _ b))
  | succ m ih =>
    intro a b h
    have key : ∀ c, (relativeSingularCohomology.map K (ModuleCat.of K K) (lineEmbedding (m + 1))
        (compl_univ_subset_preimage _) (2 * 1 : ℕ)).hom c =
        (relativeSingularCohomology.map K (ModuleCat.of K K) (lineEmbedding m)
          (compl_univ_subset_preimage _) (2 * 1 : ℕ)).hom
          ((relativeSingularCohomology.map K (ModuleCat.of K K) (hyperplaneEmbedding (m + 1))
            (compl_univ_subset_preimage _) (2 * 1 : ℕ)).hom c) :=
      fun c ↦ (map_map_apply K _ _ _ _ _ c).symm
    rw [key, key] at h
    exact (bijective_map_hyperplaneEmbedding K (m + 1) 2 (by omega) (by omega)).1 (ih h)

/-- Pull-back along a permutation of the homogeneous coordinates of `ℙⁿ(ℂ)` is injective. -/
lemma injective_map_permHomeomorph {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (k : ℤ) :
    Function.Injective (relativeSingularCohomology.map K (ModuleCat.of K K)
      (TopCat.ofHom ⟨permHomeomorph σ, (permHomeomorph σ).continuous⟩)
      (compl_univ_subset_preimage _) k).hom :=
  injective_map_of_isIso K (TopCat.isoOfHomeo (permHomeomorph σ)) Set.univᶜ k

/-- Restriction `H²(ℙᵐ⁺²(ℂ); K) → H²(ℙ¹(ℂ); K)` along `lastLine m` is injective. -/
theorem injective_map_lastLine (m : ℕ) :
    Function.Injective (relativeSingularCohomology.map K (ModuleCat.of K K) (lastLine m)
      (compl_univ_subset_preimage _) (2 * 1 : ℕ)).hom := by
  intro a b h
  have key : ∀ c, (relativeSingularCohomology.map K (ModuleCat.of K K) (lastLine m)
      (compl_univ_subset_preimage _) (2 * 1 : ℕ)).hom c =
      (relativeSingularCohomology.map K (ModuleCat.of K K) (lineEmbedding (m + 1))
        (compl_univ_subset_preimage _) (2 * 1 : ℕ)).hom
        ((relativeSingularCohomology.map K (ModuleCat.of K K)
          (TopCat.ofHom ⟨permHomeomorph (reversePerm m), (permHomeomorph _).continuous⟩)
          (compl_univ_subset_preimage _) (2 * 1 : ℕ)).hom c) :=
    fun c ↦ (map_map_apply K _ _ _ _ _ c).symm
  rw [key, key] at h
  exact injective_map_permHomeomorph K _ _ (injective_map_lineEmbedding K (m + 1) h)

/-- The point `[0 : ⋯ : 0 : 1 : 0]` of `ℙᵐ⁺²(ℂ)`. -/
def complChartBase (m : ℕ) : complexProjectiveSpace (m + 2) := (complChart m (0, 0)).1

/-- The transposition of the last two coordinates of `ℙᵐ⁺²(ℂ)`. -/
abbrev lastSwap (m : ℕ) : Equiv.Perm (Fin (m + 3)) :=
  Equiv.swap (Fin.castSucc (Fin.last (m + 1))) (Fin.last (m + 2))

/-- Swapping the last two coordinates sends `[0 : ⋯ : 0 : 1]` to `[0 : ⋯ : 0 : 1 : 0]`. -/
lemma permHomeomorph_lastSwap_basePoint (m : ℕ) :
    permHomeomorph (lastSwap m) (projectiveSpaceBasePoint (m + 1)) = complChartBase m := by
  apply Subtype.ext
  rw [permHomeomorph_apply_val _ _ rfl]
  change _ = lineProjection (chartVector m 0 0)
  congr 1
  ext k
  simp only [Function.comp_apply, chartVector]
  induction k using Fin.lastCases with
  | last =>
    rw [Fin.snoc_last, Equiv.swap_apply_right, Pi.single_apply,
      ite_eq_right (Fin.castSucc_ne_last _)]
    rfl
  | cast k =>
    induction k using Fin.lastCases with
    | last =>
      rw [Fin.snoc_castSucc, Fin.snoc_last, Equiv.swap_apply_left, Pi.single_eq_same]
    | cast k =>
      rw [Fin.snoc_castSucc, Fin.snoc_castSucc, Equiv.swap_apply_of_ne_of_ne
        (fun h ↦ Fin.castSucc_ne_last k (Fin.castSucc_injective _ h)) (Fin.castSucc_ne_last _),
        Pi.single_apply, ite_eq_right (Fin.castSucc_ne_last _)]
      rfl

/-- In the top degree, forgetting the supports `{[0 : ⋯ : 0 : 1 : 0]}` of a class of `ℙᵐ⁺²(ℂ)` is
injective. -/
theorem injective_forget_complChartBase (m : ℕ) {S S' : Set (complexProjectiveSpace (m + 2))}
    (hS : S = {complChartBase m}) (hSS' : S ⊆ S') (hS' : S' = Set.univ) {k : ℤ}
    (hk : k = ((2 * (m + 1) + 1 + 1 : ℕ) : ℤ)) :
    Function.Injective (forget K (ModuleCat.of K K) _ hSS' k).hom := by
  subst hS hS'
  let e := TopCat.isoOfHomeo (permHomeomorph (lastSwap m))
  have hpre : e.hom ⁻¹' {complChartBase m} = {projectiveSpaceBasePoint (m + 1)} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [← permHomeomorph_lastSwap_basePoint]
    exact (permHomeomorph (lastSwap m)).injective.eq_iff
  have hP : Function.Injective (relativeSingularCohomology.map K (ModuleCat.of K K) e.hom
      (A' := (e.hom ⁻¹' {complChartBase m})ᶜ) Set.preimage_compl.ge k).hom :=
    injective_map_of_subset K e.hom (A'' := e.hom ⁻¹' {complChartBase m}ᶜ) subset_rfl _
      Set.preimage_compl.le k (injective_map_of_isIso K e _ k)
  have hF := injective_forget_basePoint K (m + 1) hpre (Set.subset_univ _) rfl hk
  intro a b hab
  apply hP
  apply hF
  have comm : ∀ c, (forget K (ModuleCat.of K K) _ (Set.subset_univ (e.hom ⁻¹' {complChartBase m}))
      k).hom ((relativeSingularCohomology.map K (ModuleCat.of K K) e.hom
        (A' := (e.hom ⁻¹' {complChartBase m})ᶜ) Set.preimage_compl.ge k).hom c) =
      (relativeSingularCohomology.map K (ModuleCat.of K K) e.hom (compl_univ_subset_preimage _)
        k).hom ((forget K (ModuleCat.of K K) _ hSS' k).hom c) := fun c ↦
    map_map_eq K _ _ _ _ (by simp) _ _ _ _ k c
  rw [comm, comm, hab]

/-- A class of degree two of `ℙᵐ⁺²(ℂ)` lifts to a class supported on the hyperplane
`{x_{m+2} = 0}`. -/
theorem exists_toCohomology_hyperplane_eq (m : ℕ)
    (x : cohomologyWithSupports K (ModuleCat.of K K) (complexProjectiveSpace (m + 2)) Set.univ
      (2 * 1 : ℕ)) :
    ∃ v : cohomologyWithSupports K (ModuleCat.of K K) (complexProjectiveSpace (m + 2))
      (projectiveSpaceCell (m + 1))ᶜ (2 * 1 : ℕ),
      (toCohomology K (ModuleCat.of K K) _ _ _).hom v = x := by
  have := subsingleton_cohomology_of_homeomorph_euclidean K
    (Z := TopCat.of ↥((projectiveSpaceCell (m + 1))ᶜᶜ : Set (complexProjectiveSpace (m + 2))))
    ((Homeomorph.setCongr (compl_compl (projectiveSpaceCell (m + 1)))).trans
      (projectiveSpaceCellHomeomorph (m + 1))) 1
  exact (exact_toCohomology_restrictCompl K _ (projectiveSpaceCell (m + 1))ᶜ (2 * 1) x).1
    (Subsingleton.elim _ _)

end Restriction

/-! ### The inductive step: `x^{m+2} ≠ 0` on `ℙᵐ⁺²(ℂ)` -/

section Step

open CategoryTheory cohomologyWithSupports

variable (K : Type) [Field K]

/-- The point `[u : 1 : t]` lies on the hyperplane `{x_{m+2} = 0}` iff `t = 0`. -/
lemma complChart_mem_compl_cell_iff (m : ℕ) (x : (Fin (m + 1) → ℂ) × (Fin 1 → ℂ)) :
    (subspaceInclusion _ _ (complChart m x) : complexProjectiveSpace (m + 2)) ∈
      (projectiveSpaceCell (m + 1))ᶜ ↔ x.2 = 0 := by
  change ¬ (lineProjection (chartVector m x.1 x.2) (Fin.last (m + 2)) (Fin.last (m + 2)) ≠ 0) ↔ _
  rw [not_not, lineProjection_last_eq_zero_iff (chartVector_ne_zero m x.1 x.2)]
  simp only [chartVector, Fin.snoc_last]
  constructor
  · intro h; ext i; rw [Fin.fin_one_eq_zero i]; exact h
  · intro h; rw [h]; rfl

/-- The vector `(c₀, c₁, 0, …, 0)` is nonzero for `c ≠ 0`. -/
lemma zeroPad_ne_zero (m : ℕ) {c : Fin 2 → ℂ} (hc : c ≠ 0) : zeroPad m c ≠ 0 := fun h ↦ hc (by
  ext i
  have := congrFun h (Fin.castLE (by omega) i)
  simpa [zeroPad, i.isLt] using this)

/-- `lastLine m` sends the line `ℂ c` to the line `ℂ (0, …, 0, c₁, c₀)`. -/
lemma lastLine_apply_val (m : ℕ) (P : complexProjectiveSpace 1) {c : Fin 2 → ℂ}
    (hP : P.1 = lineProjection c) :
    (lastLine m P).1 = lineProjection (zeroPad (m + 1) c ∘ reversePerm m) :=
  permHomeomorph_apply_val _ _ (lineEmbedding_apply_val (m + 1) P hP)

/-- `lastLine m P` lies on the hyperplane `{x_{m+2} = 0}` iff `P` is the point `[0 : 1]` of
`ℙ¹(ℂ)`. -/
lemma lastLine_mem_compl_cell_iff (m : ℕ) (P : complexProjectiveSpace 1) :
    lastLine m P ∈ (projectiveSpaceCell (m + 1))ᶜ ↔ P = projectiveSpaceBasePoint 0 := by
  obtain ⟨c, hc, hP⟩ := P.2
  change ¬ ((lastLine m P).1 (Fin.last (m + 2)) (Fin.last (m + 2)) ≠ 0) ↔ _
  rw [not_not, lastLine_apply_val m P hP.symm,
    lineProjection_last_eq_zero_iff (comp_perm_ne_zero _ (zeroPad_ne_zero _ hc))]
  have h0 : (zeroPad (m + 1) c ∘ reversePerm m) (Fin.last (m + 2)) = c 0 := by
    simp [zeroPad, Fin.rev_last]
  rw [h0]
  constructor
  · intro h
    apply Subtype.ext
    change P.1 = lineProjection _
    rw [← hP, lineProjection_eq_single_last_iff hc]
    ext i; rw [Fin.fin_one_eq_zero i]; exact h
  · intro h
    have h' := congrArg Subtype.val h
    change P.1 = lineProjection _ at h'
    rw [← hP, lineProjection_eq_single_last_iff hc] at h'
    exact congrFun h' 0

/-- `lastLine m` maps the complement of `[0 : 1]` into the complement of the hyperplane
`{x_{m+2} = 0}`. -/
lemma compl_basePoint_subset_preimage_lastLine (m : ℕ) :
    ({projectiveSpaceBasePoint 0} : Set (complexProjectiveSpace 1))ᶜ ⊆
      lastLine m ⁻¹' ((projectiveSpaceCell (m + 1))ᶜ)ᶜ :=
  fun P hP h ↦ hP ((lastLine_mem_compl_cell_iff m P).1 h)

/-- The homotopy `(τ, (u, t)) ↦ [τ u : 1 : t]` from the projection to the axis to the chart. -/
def complChartHomotopy (m : ℕ) :
    TopCat.Homotopy (TopCat.ofHom (ContinuousMap.snd :
        C((Fin (m + 1) → ℂ) × (Fin 1 → ℂ), Fin 1 → ℂ)) ≫ axisInclusion m ≫ complChart m ≫
        subspaceInclusion _ _)
      (complChart m ≫ subspaceInclusion _ _) where
  toFun p := (complChart m ≫ subspaceInclusion _ _) ((p.1 : ℝ) • p.2.1, p.2.2)
  continuous_toFun := (complChart m ≫ subspaceInclusion _ _).hom.continuous.comp (by fun_prop)
  map_zero_left y := by simp [axisInclusion]
  map_one_left y := by simp

/-- Restricting along `lastLine m` keeps nonzero a class supported on the hyperplane
`{x_{m+2} = 0}` of `ℙᵐ⁺²(ℂ)` whose image in `H²(ℙᵐ⁺²(ℂ))` is nonzero. -/
theorem map_lastLine_ne_zero (m : ℕ)
    (v : cohomologyWithSupports K (ModuleCat.of K K) (complexProjectiveSpace (m + 2))
      (projectiveSpaceCell (m + 1))ᶜ (2 * 1 : ℕ))
    (hv : (toCohomology K (ModuleCat.of K K) _ _ _).hom v ≠ 0) :
    (relativeSingularCohomology.map K (ModuleCat.of K K) (lastLine m)
      (compl_basePoint_subset_preimage_lastLine m) (2 * 1 : ℕ)).hom v ≠ 0 := by
  intro h
  apply hv
  apply injective_map_lastLine K m
  rw [map_zero]
  refine (map_map_eq K (𝟙 _) (lastLine m) (lastLine m) (𝟙 _) (by simp)
    (compl_univ_subset_compl _ ({projectiveSpaceBasePoint 0} : Set (complexProjectiveSpace 1)))
    (compl_basePoint_subset_preimage_lastLine m) (compl_univ_subset_preimage _)
    (compl_univ_subset_compl _ _) (2 * 1 : ℕ) v).symm.trans ?_
  rw [h, map_zero]

/-- The chart `complChart m` sends the points retracting to the base point of `ℙᵐ⁺¹(ℂ)` into
`{0} × ℂ`. -/
lemma preimage_complChart_preimage_retraction_subset (m : ℕ) :
    complChart m ⁻¹' (hyperplaneRetraction (m + 1) ⁻¹' {projectiveSpaceBasePoint m}) ⊆
      TopCat.ofHom (ContinuousMap.fst :
        C((Fin (m + 1) → ℂ) × (Fin 1 → ℂ), Fin (m + 1) → ℂ)) ⁻¹' {0} := by
  intro x hx
  have : (complChart m ≫ hyperplaneRetraction (m + 1)) x = projectiveSpaceBasePoint m := hx
  rw [complChart_comp_hyperplaneRetraction] at this
  exact (affineChartMap_eq_basePoint_iff m x.1).1 this

/-- Along `complChart m`, the restriction to `ℙᵐ⁺²(ℂ) - [0 : ⋯ : 0 : 1]` of a class `v` supported
on the hyperplane `{x_{m+2} = 0}` is the pull-back along the second projection of the restriction
of `v` to the affine chart of the last line. -/
theorem map_complChart_pullback_subspaceInclusion (m : ℕ)
    (v : cohomologyWithSupports K (ModuleCat.of K K) (complexProjectiveSpace (m + 2))
      (projectiveSpaceCell (m + 1))ᶜ (2 * 1 : ℕ)) :
    (relativeSingularCohomology.map K (ModuleCat.of K K) (complChart m)
      (compl_subset_preimage_compl (show complChart m ⁻¹'
        (subspaceInclusion (complexProjectiveSpace (m + 2))
          ({projectiveSpaceBasePoint (m + 1)} : Set (complexProjectiveSpace (m + 2)))ᶜ ⁻¹'
            (projectiveSpaceCell (m + 1))ᶜ) ⊆ TopCat.ofHom (ContinuousMap.snd :
              C((Fin (m + 1) → ℂ) × (Fin 1 → ℂ), Fin 1 → ℂ)) ⁻¹' {0} from
        fun x hx ↦ (complChart_mem_compl_cell_iff m x).1 hx)) (2 * 1 : ℕ)).hom
        ((cohomologyWithSupports.pullback K (ModuleCat.of K K)
          (subspaceInclusion (complexProjectiveSpace (m + 2))
            ({projectiveSpaceBasePoint (m + 1)} : Set (complexProjectiveSpace (m + 2)))ᶜ)
          (projectiveSpaceCell (m + 1))ᶜ _).hom v) =
      (cohomologyWithSupports.pullback K (ModuleCat.of K K) (TopCat.ofHom (ContinuousMap.snd :
          C((Fin (m + 1) → ℂ) × (Fin 1 → ℂ), Fin 1 → ℂ))) {0} _).hom
        ((relativeSingularCohomology.map K (ModuleCat.of K K) (affineChartMap 0)
          (compl_zero_subset_preimage_affineChartMap 0) (2 * 1 : ℕ)).hom
          ((relativeSingularCohomology.map K (ModuleCat.of K K) (lastLine m)
            (compl_basePoint_subset_preimage_lastLine m) (2 * 1 : ℕ)).hom v)) := by
  let ιE := subspaceInclusion (complexProjectiveSpace (m + 2))
    ({projectiveSpaceBasePoint (m + 1)} : Set (complexProjectiveSpace (m + 2)))ᶜ
  let Φ := complChart m
  let H : Set (complexProjectiveSpace (m + 2)) := (projectiveSpaceCell (m + 1))ᶜ
  let snd := TopCat.ofHom (ContinuousMap.snd :
    C((Fin (m + 1) → ℂ) × (Fin 1 → ℂ), Fin 1 → ℂ))
  have hS : ((snd ⁻¹' {0})ᶜ : Set ((Fin (m + 1) → ℂ) × (Fin 1 → ℂ))) ⊆
      (Φ ≫ ιE) ⁻¹' Hᶜ := fun x hx h ↦ hx ((complChart_mem_compl_cell_iff m x).1 h)
  have hS' : ((snd ⁻¹' {0})ᶜ : Set ((Fin (m + 1) → ℂ) × (Fin 1 → ℂ))) ⊆
      (snd ≫ axisInclusion m ≫ Φ ≫ ιE) ⁻¹' Hᶜ := fun x hx h ↦
    hx ((complChart_mem_compl_cell_iff m (0, x.2)).1 h)
  have hhom := relativeSingularCohomology.map_eq_of_homotopy K (complChartHomotopy m)
    (A' := ((snd ⁻¹' {0})ᶜ : Set ((Fin (m + 1) → ℂ) × (Fin 1 → ℂ)))) (A := Hᶜ)
    (fun y hy t h ↦ hy ((complChart_mem_compl_cell_iff m ((t : ℝ) • y.1, y.2)).1 h))
    hS' hS (2 * 1 : ℕ)
  refine (map_map_apply K Φ ιE _ _ _ v).trans ?_
  refine (congrArg (fun f ↦ ModuleCat.Hom.hom f v) hhom).symm.trans ?_
  refine (map_map_apply K snd (axisInclusion m ≫ Φ ≫ ιE) (fun _ hx ↦ hx)
    (show ({0}ᶜ : Set (Fin 1 → ℂ)) ⊆ (axisInclusion m ≫ Φ ≫ ιE) ⁻¹' Hᶜ from fun t ht h ↦
      ht ((complChart_mem_compl_cell_iff m (0, t)).1 h)) _ v).symm.trans ?_
  congr 1
  refine (map_congr_apply K (affineChartMap_comp_lastLine m).symm _
    (fun _ hx ↦ compl_basePoint_subset_preimage_lastLine m
      (compl_zero_subset_preimage_affineChartMap 0 hx)) _ v).trans ?_
  exact (map_map_apply K (affineChartMap 0) (lastLine m) _ _ _ v).symm

/-- **The local computation.** For `z ≠ 0` supported at the base point `q` of `ℙᵐ⁺¹(ℂ)` and `v`
supported on the hyperplane `H = {x_{m+2} = 0}` of `ℙᵐ⁺²(ℂ)` with nonzero image in `H²(ℙᵐ⁺²)`, the
class `r^* z ∪ v|_E` on `E = ℙᵐ⁺²(ℂ) - [0 : ⋯ : 0 : 1]`, `r : E → ℙᵐ⁺¹(ℂ)` the retraction, is
nonzero. -/
theorem cup_pullback_retraction_ne_zero (m : ℕ)
    (z : cohomologyWithSupports K (ModuleCat.of K K) (complexProjectiveSpace (m + 1))
      {projectiveSpaceBasePoint m} (2 * (m + 1) : ℕ)) (hz : z ≠ 0)
    (v : cohomologyWithSupports K (ModuleCat.of K K) (complexProjectiveSpace (m + 2))
      (projectiveSpaceCell (m + 1))ᶜ (2 * 1 : ℕ))
    (hv : (toCohomology K (ModuleCat.of K K) _ _ _).hom v ≠ 0) :
    cup K (projectiveSpaceBasePointCompl (m + 1))
      ((isClosed_singleton (x := projectiveSpaceBasePoint m)).preimage
        (ConcreteCategory.hom (hyperplaneRetraction (m + 1))).continuous)
      ((isOpen_projectiveSpaceCell (m + 1)).isClosed_compl.preimage
        (ConcreteCategory.hom (subspaceInclusion (complexProjectiveSpace (m + 2))
          ({projectiveSpaceBasePoint (m + 1)} : Set (complexProjectiveSpace (m + 2)))ᶜ)).continuous)
      (2 * (m + 1) : ℕ) (2 * 1 : ℕ)
      ((cohomologyWithSupports.pullback K (ModuleCat.of K K) (hyperplaneRetraction (m + 1))
        {projectiveSpaceBasePoint m} _).hom z)
      ((cohomologyWithSupports.pullback K (ModuleCat.of K K)
        (subspaceInclusion (complexProjectiveSpace (m + 2))
          ({projectiveSpaceBasePoint (m + 1)} : Set (complexProjectiveSpace (m + 2)))ᶜ)
        (projectiveSpaceCell (m + 1))ᶜ _).hom v) ≠ 0 := by
  let ιE := subspaceInclusion (complexProjectiveSpace (m + 2))
    ({projectiveSpaceBasePoint (m + 1)} : Set (complexProjectiveSpace (m + 2)))ᶜ
  let r := hyperplaneRetraction (m + 1)
  let Φ := complChart m
  let H : Set (complexProjectiveSpace (m + 2)) := (projectiveSpaceCell (m + 1))ᶜ
  let fst := TopCat.ofHom (ContinuousMap.fst :
    C((Fin (m + 1) → ℂ) × (Fin 1 → ℂ), Fin (m + 1) → ℂ))
  let snd := TopCat.ofHom (ContinuousMap.snd :
    C((Fin (m + 1) → ℂ) × (Fin 1 → ℂ), Fin 1 → ℂ))
  let a := (relativeSingularCohomology.map K (ModuleCat.of K K) (affineChartMap m)
    (compl_zero_subset_preimage_affineChartMap m) (2 * (m + 1) : ℕ)).hom z
  have ha : a ≠ 0 := fun h ↦ hz ((injective_map_affineChartMap K m _) (h.trans (map_zero _).symm))
  let vL := (relativeSingularCohomology.map K (ModuleCat.of K K) (lastLine m)
    (compl_basePoint_subset_preimage_lastLine m) (2 * 1 : ℕ)).hom v
  have hvL : vL ≠ 0 := map_lastLine_ne_zero K m v hv
  let b := (relativeSingularCohomology.map K (ModuleCat.of K K) (affineChartMap 0)
    (compl_zero_subset_preimage_affineChartMap 0) (2 * 1 : ℕ)).hom vL
  have hb : b ≠ 0 := fun h ↦ hvL ((injective_map_affineChartMap K 0 _) (h.trans (map_zero _).symm))
  have hgX : Φ ⁻¹' (r ⁻¹' {projectiveSpaceBasePoint m}) ⊆ fst ⁻¹' {0} :=
    preimage_complChart_preimage_retraction_subset m
  have hgW : Φ ⁻¹' (ιE ⁻¹' H) ⊆ snd ⁻¹' {0} := fun x hx ↦
    (complChart_mem_compl_cell_iff m x).1 hx
  have h2 : (relativeSingularCohomology.map K (ModuleCat.of K K) Φ
      (compl_subset_preimage_compl hgX) (2 * (m + 1) : ℕ)).hom
        ((cohomologyWithSupports.pullback K (ModuleCat.of K K) r
          {projectiveSpaceBasePoint m} _).hom z) =
      (cohomologyWithSupports.pullback K (ModuleCat.of K K) fst {0} _).hom a :=
    map_map_eq K Φ r fst (affineChartMap m) (complChart_comp_hyperplaneRetraction m) _ _ _ _ _ z
  have h3 : (relativeSingularCohomology.map K (ModuleCat.of K K) Φ
      (compl_subset_preimage_compl hgW) (2 * 1 : ℕ)).hom
        ((cohomologyWithSupports.pullback K (ModuleCat.of K K) ιE H _).hom v) =
      (cohomologyWithSupports.pullback K (ModuleCat.of K K) snd {0} _).hom b :=
    map_complChart_pullback_subspaceInclusion K m v
  intro hw
  refine cup_pullback_fst_snd_ne_zero K (R := m + 1) (S := 1) (by omega) one_ne_zero a ha b hb ?_
  have h1 := map_cup Φ (R := K)
    ((isClosed_singleton (x := projectiveSpaceBasePoint m)).preimage
      (ConcreteCategory.hom r).continuous)
    ((isOpen_projectiveSpaceCell (m + 1)).isClosed_compl.preimage
      (ConcreteCategory.hom ιE).continuous)
    ((isClosed_singleton (x := (0 : Fin (m + 1) → ℂ))).preimage
      (ConcreteCategory.hom fst).continuous)
    ((isClosed_singleton (x := (0 : Fin 1 → ℂ))).preimage (ConcreteCategory.hom snd).continuous)
    hgX hgW (2 * (m + 1) : ℕ) (2 * 1 : ℕ)
    ((cohomologyWithSupports.pullback K (ModuleCat.of K K) r {projectiveSpaceBasePoint m} _).hom z)
    ((cohomologyWithSupports.pullback K (ModuleCat.of K K) ιE H _).hom v)
  rw [h2, h3] at h1
  exact h1.symm.trans ((congrArg (relativeSingularCohomology.map K (ModuleCat.of K K) Φ
    (compl_subset_preimage_compl (Set.inter_subset_inter hgX hgW)) _).hom hw).trans (map_zero _))

/-- In `ℙᵐ⁺²(ℂ) - [0 : ⋯ : 0 : 1]`, the points on the hyperplane `{x_{m+2} = 0}` which retract to
the base point of `ℙᵐ⁺¹(ℂ)` form the single point `[0 : ⋯ : 0 : 1 : 0]`. -/
lemma preimage_basePoint_inter_preimage_compl_cell (m : ℕ) :
    (hyperplaneRetraction (m + 1)) ⁻¹' {projectiveSpaceBasePoint m} ∩
        (subspaceInclusion (complexProjectiveSpace (m + 2))
          ({projectiveSpaceBasePoint (m + 1)} : Set (complexProjectiveSpace (m + 2)))ᶜ) ⁻¹'
          (projectiveSpaceCell (m + 1))ᶜ =
      (subspaceInclusion (complexProjectiveSpace (m + 2))
        ({projectiveSpaceBasePoint (m + 1)} : Set (complexProjectiveSpace (m + 2)))ᶜ) ⁻¹'
        {complChartBase m} := by
  ext e
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨v, hv, hi, hx⟩ := exists_lineProjection_eq_of_ne (m + 1) e.2
    have hr := hyperplaneRetraction_apply_val (m + 1) e hv hi hx.symm
    have h1' := congrArg Subtype.val h1
    rw [hr] at h1'
    change lineProjection _ = lineProjection _ at h1'
    rw [lineProjection_eq_single_last_iff hi] at h1'
    have h2' : lineProjection v (Fin.last (m + 2)) (Fin.last (m + 2)) = 0 := by
      change ¬ (e.1.1 (Fin.last (m + 2)) (Fin.last (m + 2)) ≠ 0) at h2
      rwa [not_not, ← hx] at h2
    rw [lineProjection_last_eq_zero_iff hv] at h2'
    set a := v (Fin.castSucc (Fin.last (m + 1)))
    have hva : v = a • chartVector m 0 0 := by
      ext k
      induction k using Fin.lastCases with
      | last => simp [chartVector, h2']
      | cast k =>
        induction k using Fin.lastCases with
        | last => simp [chartVector, a]
        | cast k =>
          have := congrFun h1' k
          simp only [Fin.init, Pi.zero_apply] at this
          simp [chartVector, this]
    have ha : a ≠ 0 := fun h ↦ hv (by rw [hva, h, zero_smul])
    apply Subtype.ext
    change e.1.1 = lineProjection (chartVector m 0 0)
    rw [← hx, hva, lineProjection_smul (chartVector_ne_zero m 0 0) ha]
  · intro h
    have he : e = complChart m (0, 0) := Subtype.ext h
    subst he
    refine ⟨?_, (complChart_mem_compl_cell_iff m (0, 0)).2 rfl⟩
    change (complChart m ≫ hyperplaneRetraction (m + 1)) (0, 0) = _
    rw [complChart_comp_hyperplaneRetraction]
    exact (affineChartMap_eq_basePoint_iff m 0).2 rfl

/-- If `z` lifts `y^{m+1}`, `y` the restriction of `x` to the hyperplane `ℙᵐ⁺¹(ℂ)`, then the
restriction of `x^{m+1}` to `E = ℙᵐ⁺²(ℂ) - [0 : ⋯ : 0 : 1]` is the pull-back of `z` along the
retraction `E → ℙᵐ⁺¹(ℂ)`. -/
theorem map_subspaceInclusion_cupPowSucc_eq (m : ℕ)
    (x : cohomologyWithSupports K (ModuleCat.of K K) (complexProjectiveSpace (m + 2)) Set.univ
      (2 * 1 : ℕ))
    (z : cohomologyWithSupports K (ModuleCat.of K K) (complexProjectiveSpace (m + 1))
      {projectiveSpaceBasePoint m} (2 * (m + 1) : ℕ))
    (hz : (toCohomology K (ModuleCat.of K K) _ _ _).hom z = cupPowSucc K
      ((relativeSingularCohomology.map K (ModuleCat.of K K) (hyperplaneEmbedding (m + 1))
        (compl_univ_subset_preimage _) (2 * 1 : ℕ)).hom x) m) :
    (relativeSingularCohomology.map K (ModuleCat.of K K)
      (subspaceInclusion (complexProjectiveSpace (m + 2))
        ({projectiveSpaceBasePoint (m + 1)} : Set (complexProjectiveSpace (m + 2)))ᶜ)
      (compl_subset_preimage_compl (Set.subset_univ
        ((subspaceInclusion (complexProjectiveSpace (m + 2))
          ({projectiveSpaceBasePoint (m + 1)} : Set (complexProjectiveSpace (m + 2)))ᶜ) ⁻¹'
            Set.univ)))
        (2 * (m + 1) : ℕ)).hom (cupPowSucc K x m) =
      (forget K (ModuleCat.of K K) _
        (Set.subset_univ (hyperplaneRetraction (m + 1) ⁻¹' {projectiveSpaceBasePoint m})) _).hom
        ((cohomologyWithSupports.pullback K (ModuleCat.of K K) (hyperplaneRetraction (m + 1))
          {projectiveSpaceBasePoint m} _).hom z) := by
  let ιE := subspaceInclusion (complexProjectiveSpace (m + 2))
        ({projectiveSpaceBasePoint (m + 1)} : Set (complexProjectiveSpace (m + 2)))ᶜ
  let r := hyperplaneRetraction (m + 1)
  let i := hyperplaneInclusion (m + 1)
  let iso := cohomologyIsoOfHomotopy K i r (hyperplaneInclusion_comp_retraction (m + 1))
    (hyperplaneHomotopy (m + 1)) (2 * 1 : ℕ)
  let xE := (relativeSingularCohomology.map K (ModuleCat.of K K) ιE
    (compl_univ_subset_preimage ιE) (2 * 1 : ℕ)).hom x
  have hxE : (relativeSingularCohomology.map K (ModuleCat.of K K) r
      (compl_univ_subset_preimage r) (2 * 1 : ℕ)).hom
      ((relativeSingularCohomology.map K (ModuleCat.of K K) i
        (compl_univ_subset_preimage i) (2 * 1 : ℕ)).hom xE) = xE :=
    congrArg (fun f ↦ ModuleCat.Hom.hom f xE) iso.hom_inv_id
  have hiy : (relativeSingularCohomology.map K (ModuleCat.of K K) i
      (compl_univ_subset_preimage i) (2 * 1 : ℕ)).hom xE =
      (relativeSingularCohomology.map K (ModuleCat.of K K) (hyperplaneEmbedding (m + 1))
        (compl_univ_subset_preimage _) (2 * 1 : ℕ)).hom x :=
    map_map_apply K i ιE _ _ _ x
  rw [hiy] at hxE
  refine (map_cupPowSucc K ιE x m).trans ?_
  change cupPowSucc K xE m = _
  rw [← hxE, ← map_cupPowSucc K r _ m, ← hz]
  exact map_map_eq K r (𝟙 _) (𝟙 _) r (by simp) _ _ _ _ _ z

/-- The point `[0 : ⋯ : 0 : 1 : 0]` lies on the hyperplane `{x_{m+2} = 0}` of `ℙᵐ⁺²(ℂ)`. -/
lemma singleton_complChartBase_subset (m : ℕ) :
    ({complChartBase m} : Set (complexProjectiveSpace (m + 2))) ⊆
      Set.univ ∩ (projectiveSpaceCell (m + 1))ᶜ := by
  rintro _ rfl
  exact ⟨Set.mem_univ _, (complChart_mem_compl_cell_iff m (0, 0)).2 rfl⟩

/-- If `x^{m+2} = 0` for `x ∈ H²(ℙᵐ⁺²(ℂ); K)` lifting to `v`, then a class `w'` supported at
`[0 : ⋯ : 0 : 1 : 0]` whose image is `x^{m+1} ∪ v` vanishes. -/
theorem eq_zero_of_forget_eq_cupPowSucc_cup (m : ℕ)
    (x : cohomologyWithSupports K (ModuleCat.of K K) (complexProjectiveSpace (m + 2)) Set.univ
      (2 * 1 : ℕ))
    (v : cohomologyWithSupports K (ModuleCat.of K K) (complexProjectiveSpace (m + 2))
      (projectiveSpaceCell (m + 1))ᶜ (2 * 1 : ℕ))
    (hv : (toCohomology K (ModuleCat.of K K) _ _ _).hom v = x)
    (w' : cohomologyWithSupports K (ModuleCat.of K K) (complexProjectiveSpace (m + 2))
      {complChartBase m} (((2 * (m + 1) : ℕ) : ℤ) + ((2 * 1 : ℕ) : ℤ)))
    (hc : (forget K (ModuleCat.of K K) (complexProjectiveSpace (m + 2))
        (singleton_complChartBase_subset m) _).hom w' =
      cup K (complexProjectiveSpace (m + 2)) isClosed_univ
        (isOpen_projectiveSpaceCell (m + 1)).isClosed_compl
        (2 * (m + 1) : ℕ) (2 * 1 : ℕ) (cupPowSucc K x m) v)
    (hzero : cupPowSucc K x (m + 1) = 0) : w' = 0 := by
  let Y := complexProjectiveSpace (m + 2)
  let H : Set Y := (projectiveSpaceCell (m + 1))ᶜ
  have hH : IsClosed H := (isOpen_projectiveSpaceCell (m + 1)).isClosed_compl
  have hTUH := singleton_complChartBase_subset m
  let k : ℤ := ((2 * (m + 1) : ℕ) : ℤ) + ((2 * 1 : ℕ) : ℤ)
  have hE1 : (forget K (ModuleCat.of K K) Y (Set.inter_subset_inter (subset_refl Set.univ)
      (Set.subset_univ H)) k).hom
        (cup K Y isClosed_univ hH (2 * (m + 1) : ℕ) (2 * 1 : ℕ) (cupPowSucc K x m) v) =
      cup K Y isClosed_univ isClosed_univ (2 * (m + 1) : ℕ) (2 * 1 : ℕ) (cupPowSucc K x m) x := by
    refine (forget_cup (R := K) isClosed_univ hH isClosed_univ isClosed_univ (subset_refl _)
      (Set.subset_univ H) _ _ (cupPowSucc K x m) v).trans ?_
    rw [forget_refl]
    exact congrArg _ hv
  have hcup : cup K Y isClosed_univ isClosed_univ (2 * (m + 1) : ℕ) (2 * 1 : ℕ)
      (cupPowSucc K x m) x = 0 := by
    have h0 : cupPowSucc K x (m + 1) = cohomologyWithSupports.congrIndex K Y
        (by rw [Set.univ_inter]) (by push_cast; ring)
        (cup K Y isClosed_univ isClosed_univ (2 * (m + 1) : ℕ) (2 * 1 : ℕ)
          (cupPowSucc K x m) x) := rfl
    rw [h0] at hzero
    exact (LinearEquiv.map_eq_zero_iff _).1 hzero
  have hTUU : ({complChartBase m} : Set Y) ⊆ Set.univ ∩ Set.univ :=
    fun _ _ ↦ ⟨Set.mem_univ _, Set.mem_univ _⟩
  apply injective_forget_complChartBase K m rfl hTUU (Set.univ_inter _)
    (k := k) (by simp only [k]; push_cast; ring)
  rw [map_zero]
  refine (map_congr_apply K (Category.id_comp (𝟙 Y)).symm _
    (show (Set.univ ∩ Set.univ)ᶜ ⊆ ({complChartBase m} : Set Y)ᶜ from
      compl_subset_compl.mpr hTUU) k w').trans ?_
  refine (map_map_apply K (𝟙 Y) (𝟙 Y)
    (show (Set.univ ∩ Set.univ)ᶜ ⊆ (Set.univ ∩ H)ᶜ from
      compl_subset_compl.mpr (Set.inter_subset_inter (subset_refl _) (Set.subset_univ H)))
    (show (Set.univ ∩ H)ᶜ ⊆ ({complChartBase m} : Set Y)ᶜ from compl_subset_compl.mpr hTUH) k
      w').symm.trans ?_
  change (forget K (ModuleCat.of K K) Y (Set.inter_subset_inter (subset_refl Set.univ)
    (Set.subset_univ H)) k).hom ((forget K (ModuleCat.of K K) Y hTUH k).hom w') = 0
  rw [hc, hE1, hcup]

/-- The excision preimage `w'`, supported at `[0 : ⋯ : 0 : 1 : 0]`, of the class `r^* z ∪ v|_E`
on `E = ℙᵐ⁺²(ℂ) - [0 : ⋯ : 0 : 1]` maps to `x^{m+1} ∪ v`, where `z` lifts the power `y^{m+1}` of
the restriction `y` of `x` to the hyperplane. -/
theorem forget_eq_cupPowSucc_cup_of_excisionIso_eq (m : ℕ)
    (x : cohomologyWithSupports K (ModuleCat.of K K) (complexProjectiveSpace (m + 2)) Set.univ
      (2 * 1 : ℕ))
    (z : cohomologyWithSupports K (ModuleCat.of K K) (complexProjectiveSpace (m + 1))
      {projectiveSpaceBasePoint m} (2 * (m + 1) : ℕ))
    (hz : (toCohomology K (ModuleCat.of K K) _ _ _).hom z = cupPowSucc K
      ((relativeSingularCohomology.map K (ModuleCat.of K K) (hyperplaneEmbedding (m + 1))
        (compl_univ_subset_preimage _) (2 * 1 : ℕ)).hom x) m)
    (v : cohomologyWithSupports K (ModuleCat.of K K) (complexProjectiveSpace (m + 2))
      (projectiveSpaceCell (m + 1))ᶜ (2 * 1 : ℕ))
    (w' : cohomologyWithSupports K (ModuleCat.of K K) (complexProjectiveSpace (m + 2))
      {complChartBase m} (((2 * (m + 1) : ℕ) : ℤ) + ((2 * 1 : ℕ) : ℤ)))
    (hw' : (excisionIso K (isOpen_compl_singleton (x := projectiveSpaceBasePoint (m + 1)))
      (isClosed_singleton (x := complChartBase m))
      (Set.singleton_subset_iff.2 (complChart m (0, 0)).2) _).toLinearEquiv w' =
      (forget K (ModuleCat.of K K) _ (preimage_basePoint_inter_preimage_compl_cell m).le _).hom
        (cup K (projectiveSpaceBasePointCompl (m + 1))
          ((isClosed_singleton (x := projectiveSpaceBasePoint m)).preimage
            (ConcreteCategory.hom (hyperplaneRetraction (m + 1))).continuous)
          ((isOpen_projectiveSpaceCell (m + 1)).isClosed_compl.preimage
            (ConcreteCategory.hom (subspaceInclusion (complexProjectiveSpace (m + 2))
              ({projectiveSpaceBasePoint (m + 1)} :
                Set (complexProjectiveSpace (m + 2)))ᶜ)).continuous)
          (2 * (m + 1) : ℕ) (2 * 1 : ℕ)
          ((cohomologyWithSupports.pullback K (ModuleCat.of K K) (hyperplaneRetraction (m + 1))
            {projectiveSpaceBasePoint m} _).hom z)
          ((cohomologyWithSupports.pullback K (ModuleCat.of K K)
            (subspaceInclusion (complexProjectiveSpace (m + 2))
              ({projectiveSpaceBasePoint (m + 1)} : Set (complexProjectiveSpace (m + 2)))ᶜ)
            (projectiveSpaceCell (m + 1))ᶜ _).hom v))) :
    (forget K (ModuleCat.of K K) (complexProjectiveSpace (m + 2))
        (singleton_complChartBase_subset m) _).hom w' =
      cup K (complexProjectiveSpace (m + 2)) isClosed_univ
        (isOpen_projectiveSpaceCell (m + 1)).isClosed_compl
        (2 * (m + 1) : ℕ) (2 * 1 : ℕ) (cupPowSucc K x m) v := by
  let Y := complexProjectiveSpace (m + 2)
  let ιE := subspaceInclusion Y ({projectiveSpaceBasePoint (m + 1)} : Set Y)ᶜ
  let r := hyperplaneRetraction (m + 1)
  let q := projectiveSpaceBasePoint m
  let H : Set Y := (projectiveSpaceCell (m + 1))ᶜ
  have hH : IsClosed H := (isOpen_projectiveSpaceCell (m + 1)).isClosed_compl
  have hX1 : IsClosed (r ⁻¹' {q}) :=
    (isClosed_singleton (x := q)).preimage (ConcreteCategory.hom r).continuous
  have hX2 : IsClosed (ιE ⁻¹' H) := hH.preimage (ConcreteCategory.hom ιE).continuous
  let k : ℤ := ((2 * (m + 1) : ℕ) : ℤ) + ((2 * 1 : ℕ) : ℤ)
  let c := cup K Y isClosed_univ hH (2 * (m + 1) : ℕ) (2 * 1 : ℕ) (cupPowSucc K x m) v
  let zE := (cohomologyWithSupports.pullback K (ModuleCat.of K K) r {q} _).hom z
  let vE := (cohomologyWithSupports.pullback K (ModuleCat.of K K) ιE H _).hom v
  have hE2 : (relativeSingularCohomology.map K (ModuleCat.of K K) ιE
      (compl_subset_preimage_compl (Set.inter_subset_inter (Set.subset_univ (ιE ⁻¹' Set.univ))
        (subset_refl (ιE ⁻¹' H)))) k).hom c =
      (forget K (ModuleCat.of K K) _ (Set.inter_subset_inter (Set.subset_univ (r ⁻¹' {q}))
        (subset_refl (ιE ⁻¹' H))) k).hom
        (cup K _ hX1 hX2 (2 * (m + 1) : ℕ) (2 * 1 : ℕ) zE vE) := by
    refine (map_cup ιE (R := K) isClosed_univ hH isClosed_univ hX2 (Set.subset_univ _)
      (subset_refl _) _ _ (cupPowSucc K x m) v).trans ?_
    rw [map_subspaceInclusion_cupPowSucc_eq K m x z hz,
      forget_cup (R := K) hX1 hX2 isClosed_univ hX2 (Set.subset_univ _) (subset_refl _) _ _ zE vE,
      forget_refl]
    rfl
  have hUH : Set.univ ∩ H ⊆ ({projectiveSpaceBasePoint (m + 1)} : Set Y)ᶜ :=
    fun _ he h ↦ he.2 (by
      rw [Set.mem_singleton_iff.1 h]
      exact projectiveSpaceBasePoint_mem_cell (m + 1))
  have hTUH := singleton_complChartBase_subset m
  apply (excisionIso K (isOpen_compl_singleton (x := projectiveSpaceBasePoint (m + 1)))
    (isClosed_univ.inter hH) hUH k).toLinearEquiv.injective
  refine (map_map_eq K ιE (𝟙 Y) (𝟙 _) ιE (by simp) _ _
    (compl_subset_compl.mpr (Set.preimage_mono hTUH)) Set.preimage_compl.ge k w').trans ?_
  refine (congrArg (relativeSingularCohomology.map K (ModuleCat.of K K) (𝟙 _)
    (compl_subset_compl.mpr (Set.preimage_mono hTUH)) k).hom hw').trans ?_
  refine (map_map_apply K (𝟙 _) (𝟙 _) _ _ k _).trans ?_
  refine (map_congr_apply K (Category.id_comp _) _
    (show (ιE ⁻¹' (Set.univ ∩ H))ᶜ ⊆ (r ⁻¹' {q} ∩ ιE ⁻¹' H)ᶜ from
      compl_subset_compl.mpr fun e h ↦ ⟨Set.mem_univ _, h.2⟩) k _).trans ?_
  exact hE2.symm

/-- **The inductive step.** If every nonzero `y ∈ H²(ℙᵐ⁺¹(ℂ); K)` has `y^{m+1} ≠ 0`, then every
nonzero `x ∈ H²(ℙᵐ⁺²(ℂ); K)` has `x^{m+2} ≠ 0`. -/
theorem cupPowSucc_ne_zero_step (m : ℕ)
    (ih : ∀ y : cohomologyWithSupports K (ModuleCat.of K K) (complexProjectiveSpace (m + 1))
      Set.univ (2 * 1 : ℕ), y ≠ 0 → cupPowSucc K y m ≠ 0)
    (x : cohomologyWithSupports K (ModuleCat.of K K) (complexProjectiveSpace (m + 2)) Set.univ
      (2 * 1 : ℕ)) (hx : x ≠ 0) : cupPowSucc K x (m + 1) ≠ 0 := by
  let Y := complexProjectiveSpace (m + 2)
  let ιE := subspaceInclusion Y ({projectiveSpaceBasePoint (m + 1)} : Set Y)ᶜ
  let r := hyperplaneRetraction (m + 1)
  let q := projectiveSpaceBasePoint m
  let H : Set Y := (projectiveSpaceCell (m + 1))ᶜ
  have hH : IsClosed H := (isOpen_projectiveSpaceCell (m + 1)).isClosed_compl
  have hX1 : IsClosed (r ⁻¹' {q}) :=
    (isClosed_singleton (x := q)).preimage (ConcreteCategory.hom r).continuous
  have hX2 : IsClosed (ιE ⁻¹' H) := hH.preimage (ConcreteCategory.hom ιE).continuous
  let y := (relativeSingularCohomology.map K (ModuleCat.of K K) (hyperplaneEmbedding (m + 1))
    (compl_univ_subset_preimage _) (2 * 1 : ℕ)).hom x
  have hy : y ≠ 0 := fun h ↦ hx ((bijective_map_hyperplaneEmbedding K (m + 1) 2 (by omega)
    (by omega)).1 (h.trans (map_zero _).symm))
  obtain ⟨z, hz⟩ := exists_toCohomology_basePoint_eq K m (2 * (m + 1)) (by ring)
    (cupPowSucc K y m)
  have hz0 : z ≠ 0 := fun h ↦ ih y hy (by rw [← hz, h, map_zero])
  obtain ⟨v, hv⟩ := exists_toCohomology_hyperplane_eq K m x
  have hv0 : (toCohomology K (ModuleCat.of K K) _ _ _).hom v ≠ 0 := by rw [hv]; exact hx
  have hw := cup_pullback_retraction_ne_zero K m z hz0 v hv0
  let k : ℤ := ((2 * (m + 1) : ℕ) : ℤ) + ((2 * 1 : ℕ) : ℤ)
  let zE := (cohomologyWithSupports.pullback K (ModuleCat.of K K) r {q} _).hom z
  let vE := (cohomologyWithSupports.pullback K (ModuleCat.of K K) ιE H _).hom v
  have hset := preimage_basePoint_inter_preimage_compl_cell m
  have hT : ({complChartBase m} : Set Y) ⊆ ({projectiveSpaceBasePoint (m + 1)} : Set Y)ᶜ :=
    Set.singleton_subset_iff.2 (complChart m (0, 0)).2
  let exc := excisionIso K (isOpen_compl_singleton (x := projectiveSpaceBasePoint (m + 1)))
    (isClosed_singleton (x := complChartBase m)) hT k
  obtain ⟨w', hw'⟩ := exc.toLinearEquiv.surjective
    ((forget K (ModuleCat.of K K) _ hset.le k).hom
      (cup K _ hX1 hX2 (2 * (m + 1) : ℕ) (2 * 1 : ℕ) zE vE))
  have hc := forget_eq_cupPowSucc_cup_of_excisionIso_eq K m x z hz v w' hw'
  intro hzero
  apply hw
  apply injective_forget_of_eq K hset.le hset.ge k
  rw [map_zero, ← hw', eq_zero_of_forget_eq_cupPowSucc_cup K m x v hv w' hc hzero,
    map_zero]

end Step

/-! ### The cohomology of `ℙⁿ(ℂ)` is generated by a class of degree two -/

section Generators

open CategoryTheory cohomologyWithSupports

variable (K : Type) [Field K]

/-- **Top power.** For every nonzero `x ∈ H²(ℙᵐ⁺¹(ℂ); K)`, `x^{m+1} ≠ 0` in
`H^{2m+2}(ℙᵐ⁺¹(ℂ); K)`. -/
theorem cupPowSucc_ne_zero_top (m : ℕ)
    (x : cohomologyWithSupports K (ModuleCat.of K K) (complexProjectiveSpace (m + 1)) Set.univ
      (2 * 1 : ℕ)) (hx : x ≠ 0) : cupPowSucc K x m ≠ 0 := by
  induction m with
  | zero => exact hx
  | succ m ih => exact cupPowSucc_ne_zero_step K m ih x hx

/-- The inclusion `ℙᵃ(ℂ) ⟶ ℙᵃ⁺ᵈ(ℂ)` of the linear subspace of the first `a + 1` coordinates. -/
def linearSubspaceEmbedding (a : ℕ) :
    (d : ℕ) → complexProjectiveSpace a ⟶ complexProjectiveSpace (a + d)
  | 0 => 𝟙 _
  | d + 1 => linearSubspaceEmbedding a d ≫ hyperplaneEmbedding (a + d)

/-- Restriction `H²(ℙᵃ⁺ᵈ(ℂ); K) → H²(ℙᵃ(ℂ); K)` to a linear subspace is injective for `a ≠ 0`. -/
theorem injective_map_linearSubspaceEmbedding (a : ℕ) (ha : a ≠ 0) (d : ℕ) :
    Function.Injective (relativeSingularCohomology.map K (ModuleCat.of K K)
      (linearSubspaceEmbedding a d) (compl_univ_subset_preimage _) (2 * 1 : ℕ)).hom := by
  induction d with
  | zero =>
    intro u w h
    exact (map_id_apply K _ _ u).symm.trans (h.trans (map_id_apply K _ _ w))
  | succ d ih =>
    intro u w h
    have key : ∀ c, (relativeSingularCohomology.map K (ModuleCat.of K K)
        (linearSubspaceEmbedding a (d + 1)) (compl_univ_subset_preimage _) (2 * 1 : ℕ)).hom c =
        (relativeSingularCohomology.map K (ModuleCat.of K K) (linearSubspaceEmbedding a d)
          (compl_univ_subset_preimage _) (2 * 1 : ℕ)).hom
          ((relativeSingularCohomology.map K (ModuleCat.of K K) (hyperplaneEmbedding (a + d))
            (compl_univ_subset_preimage _) (2 * 1 : ℕ)).hom c) :=
      fun c ↦ (map_map_apply K _ _ _ _ _ c).symm
    rw [key, key] at h
    exact (bijective_map_hyperplaneEmbedding K (a + d) 2 (by omega) (by omega)).1 (ih h)

/-- **The powers of a degree-two class.** For every nonzero `x ∈ H²(ℙⁿ(ℂ); K)` and `k < n`,
`x^{k+1} ≠ 0` in `H^{2k+2}(ℙⁿ(ℂ); K)`. -/
theorem cupPowSucc_ne_zero {n k : ℕ} (hk : k < n)
    (x : cohomologyWithSupports K (ModuleCat.of K K) (complexProjectiveSpace n) Set.univ
      (2 * 1 : ℕ)) (hx : x ≠ 0) : cupPowSucc K x k ≠ 0 := by
  obtain ⟨d, rfl⟩ : ∃ d, n = k + 1 + d := ⟨n - (k + 1), by omega⟩
  intro h
  have hx' : (relativeSingularCohomology.map K (ModuleCat.of K K)
      (linearSubspaceEmbedding (k + 1) d) (compl_univ_subset_preimage _) (2 * 1 : ℕ)).hom x ≠ 0 :=
    fun h' ↦ hx (injective_map_linearSubspaceEmbedding K (k + 1) (by omega) d
      (h'.trans (map_zero _).symm))
  apply cupPowSucc_ne_zero_top K k _ hx'
  rw [← map_cupPowSucc, h, map_zero]

/-- For `k < n`, the cohomology `H^{2k+2}(ℙⁿ(ℂ); K)` is one-dimensional. -/
theorem finrank_cohomology_complexProjectiveSpace_two_mul_succ {n k : ℕ} (hk : k < n) :
    Module.finrank K (cohomologyWithSupports K (ModuleCat.of K K)
      (complexProjectiveSpace n) Set.univ (2 * (k + 1) : ℕ)) = 1 := by
  rw [finrank_cohomology_complexProjectiveSpace, ite_eq_left ⟨even_two_mul _, by omega⟩]

/-- **Generators of the cohomology of `ℙⁿ(ℂ)`.** For every nonzero `x ∈ H²(ℙⁿ(ℂ); K)` (for
instance the hyperplane class) and every `k < n`, `H^{2k+2}(ℙⁿ(ℂ); K)` is the line spanned by
`x^{k+1}`. -/
theorem span_cupPowSucc_eq_top {n k : ℕ} (hk : k < n)
    (x : cohomologyWithSupports K (ModuleCat.of K K) (complexProjectiveSpace n) Set.univ
      (2 * 1 : ℕ)) (hx : x ≠ 0) :
    Submodule.span K {cupPowSucc K x k} = ⊤ :=
  (finrank_eq_one_iff_of_nonzero _ (cupPowSucc_ne_zero K hk x hx)).1
    (finrank_cohomology_complexProjectiveSpace_two_mul_succ K hk)

/-- Every class of `H^{2k+2}(ℙⁿ(ℂ); K)`, `k < n`, is a multiple of `x^{k+1}`, for any nonzero
`x ∈ H²(ℙⁿ(ℂ); K)`. -/
theorem exists_smul_cupPowSucc_eq {n k : ℕ} (hk : k < n)
    (x : cohomologyWithSupports K (ModuleCat.of K K) (complexProjectiveSpace n) Set.univ
      (2 * 1 : ℕ)) (hx : x ≠ 0)
    (c : cohomologyWithSupports K (ModuleCat.of K K) (complexProjectiveSpace n) Set.univ
      (2 * (k + 1) : ℕ)) : ∃ t : K, t • cupPowSucc K x k = c :=
  (finrank_eq_one_iff_of_nonzero' _ (cupPowSucc_ne_zero K hk x hx)).1
    (finrank_cohomology_complexProjectiveSpace_two_mul_succ K hk) c

/-- Restriction to a hyperplane `H²(ℙⁿ⁺¹(ℂ); K) → H²(ℙⁿ(ℂ); K)`, `n ≥ 1`, is bijective. -/
theorem bijective_map_hyperplaneEmbedding_two {n : ℕ} (hn : n ≠ 0) :
    Function.Bijective (relativeSingularCohomology.map K (ModuleCat.of K K) (hyperplaneEmbedding n)
      (compl_univ_subset_preimage _) (2 * 1 : ℕ)).hom :=
  bijective_map_hyperplaneEmbedding K n 2 (by omega) (by omega)

/-- In the even cohomology ring, the powers of `x ∈ H²` are the classes `cupPowSucc`. -/
theorem of_pow_succ {Y : TopCat.{0}}
    (x : cohomologyWithSupports K (ModuleCat.of K K) Y Set.univ (2 * 1 : ℕ)) (k : ℕ) :
    (DirectSum.of (fun p : ℕ ↦ cohomologyWithSupports K (ModuleCat.of K K) Y Set.univ (2 * p : ℕ))
      1 x) ^ (k + 1) = DirectSum.of _ (k + 1) (cupPowSucc K x k) := by
  induction k with
  | zero => exact pow_one _
  | succ k ih =>
    rw [pow_succ, ih, EvenCohomologyRing.of_mul_of]
    rfl

/-- **The even cohomology ring of `ℙⁿ(ℂ)`.** For every nonzero `x ∈ H²(ℙⁿ(ℂ); K)`, the powers
`ξ^{k+1}`, `k < n`, of `ξ = x ∈ H^{ev}(ℙⁿ(ℂ); K)` are nonzero, and `ξ^{k+1} = 0` for `k ≥ n`. -/
theorem pow_succ_ne_zero_iff {n : ℕ}
    (x : cohomologyWithSupports K (ModuleCat.of K K) (complexProjectiveSpace n) Set.univ
      (2 * 1 : ℕ)) (hx : x ≠ 0) (k : ℕ) :
    (DirectSum.of (fun p : ℕ ↦ cohomologyWithSupports K (ModuleCat.of K K)
      (complexProjectiveSpace n) Set.univ (2 * p : ℕ)) 1 x) ^ (k + 1) ≠ 0 ↔ k < n := by
  rw [of_pow_succ, ne_eq, map_eq_zero_iff _ (DirectSum.of_injective _)]
  refine ⟨fun h ↦ by_contra fun hkn ↦ ?_, fun hk ↦ cupPowSucc_ne_zero K hk x hx⟩
  have := subsingleton_cohomology_complexProjectiveSpace_of_lt K (n := n) (k := 2 * (k + 1))
    (by omega)
  exact h (Subsingleton.elim _ _)

end Generators

end MMP.Topology
