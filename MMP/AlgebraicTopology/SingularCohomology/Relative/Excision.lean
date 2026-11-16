module

public import MMP.AlgebraicTopology.ThomClass.Natural
/-!
# Excision for cohomology with supports

Let `Y` be a space, `X ⊆ Y` a closed subset and `V ⊆ Y` an open subset containing `X`. Then the
restriction `H^j(Y, Y - X; R) → H^j(V, V - X; R)` along the inclusion `V ⊆ Y` is an isomorphism
for every `j`. This is excision for the cover `{V, Y - X}` of `Y` by two open sets.

The proof is on cochains. With `ρ = 1 - ∂ D - D ∂` the chain map of the theorem of small chains
for the cover `{V, Y - X}`, a relative cocycle `ψ` of `(V, V - X)`, extended by zero to the
simplices of `Y` not lying in `V`, pulls back along `ρ` to a relative cocycle of `(Y, Y - X)`
restricting to `ψ` up to the coboundary of `D^* ψ`; and a relative cocycle `φ` of `(Y, Y - X)`
whose restriction to `V` is the coboundary `δ η` agrees with `δ η` (extended by zero) on small
simplices, so `φ = δ (ρ^* η + D^* φ)`.

## Main definitions

* `MMP.cohomologyWithSupports.excisionIso`: the isomorphism
  `H^j(Y, Y - X; R) ≅ H^j(V, V - X; R)`.

## Main results

* `MMP.SingularCochain.bijective_relCohomologyMap_subspaceInclusion`: excision
  on cocycles modulo coboundaries.
* `MMP.cohomologyWithSupports.isIso_pullback_subspaceInclusion`: excision.

## References

* [A. Hatcher, *Algebraic Topology*][hatcher2002], §2.1, Thm. 2.20 and §3.1.
* [A. Dold, *Lectures on Algebraic Topology*][dold1995], III.7.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite Set Finsupp

universe u

namespace MMP

namespace SingularChain

variable {R : Type*} [CommRing R] {Y : Type*} [TopologicalSpace Y]

/-- Chains supported in `U` are `{U}`-small. -/
lemma inside_le_small_singleton (n : ℕ) (U : Set Y) : inside R n U ≤ small R n {U} :=
  supported_mono fun _ h ↦ ⟨U, rfl, h⟩

/-- `{U}`-small chains are supported in `U`. -/
lemma small_singleton_le_inside (n : ℕ) (U : Set Y) : small R n {U} ≤ inside R n U :=
  supported_mono fun _ ⟨_, hV, h⟩ ↦ (mem_singleton_iff.1 hV) ▸ h

/-- A simplex with image in `U` is a chain supported in `U`. -/
lemma single_mem_inside {n : ℕ} {U : Set Y} {σ : Simplex Y n} (h : range σ ⊆ U) :
    single σ (1 : R) ∈ inside R n U :=
  single_mem_supported R _ h

/-- The subdivision homotopy `homotopyUpTo` preserves chains supported in `U`. -/
lemma homotopyUpTo_mem_inside (m n : ℕ) {U : Set Y} {c : Chain R Y n}
    (hc : c ∈ inside R n U) : homotopyUpTo R m n c ∈ inside R (n + 1) U := by
  rw [homotopyUpTo, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  rw [LinearMap.comp_apply]
  exact small_singleton_le_inside _ _
    (subdivHomotopy_mem_small (subdiv_pow_mem_small i (inside_le_small_singleton _ _ hc)))

/-- The homotopy `D` of the theorem of small chains preserves chains supported in `U`. -/
lemma smallHomotopy_mem_inside (𝒰 : Set (Set Y)) (n : ℕ) {U : Set Y} {c : Chain R Y n}
    (hc : c ∈ inside R n U) : smallHomotopy R 𝒰 n c ∈ inside R (n + 1) U :=
  VertexChain.mem_of_mem_supported _ _ (fun σ hσ ↦ by
    rw [smallHomotopy_single]
    exact homotopyUpTo_mem_inside _ _ (single_mem_inside hσ)) hc

/-- The chain map `ρ` of the theorem of small chains preserves chains supported in `U`. -/
lemma smallChainMap_mem_inside (𝒰 : Set (Set Y)) (n : ℕ) {U : Set Y} {c : Chain R Y n}
    (hc : c ∈ inside R n U) : smallChainMap R 𝒰 n c ∈ inside R n U := by
  cases n with
  | zero =>
    rw [smallChainMap_zero]
    exact Submodule.sub_mem _ hc (bd_mem_inside (smallHomotopy_mem_inside 𝒰 0 hc))
  | succ n =>
    rw [smallChainMap_succ]
    exact Submodule.sub_mem _ (Submodule.sub_mem _ hc
      (bd_mem_inside (smallHomotopy_mem_inside 𝒰 _ hc)))
      (smallHomotopy_mem_inside 𝒰 n (bd_mem_inside hc))

/-- `ρ σ + ∂ D σ + D ∂ σ = σ`. -/
lemma smallChainMap_add_succ (𝒰 : Set (Set Y)) (n : ℕ) (c : Chain R Y (n + 1)) :
    smallChainMap R 𝒰 (n + 1) c + bd R (n + 1) (smallHomotopy R 𝒰 (n + 1) c) +
      smallHomotopy R 𝒰 n (bd R n c) = c := by
  rw [smallChainMap_succ]
  abel

/-- `ρ σ + ∂ D σ = σ` in degree `0`. -/
lemma smallChainMap_add_zero (𝒰 : Set (Set Y)) (c : Chain R Y 0) :
    smallChainMap R 𝒰 0 c + bd R 0 (smallHomotopy R 𝒰 0 c) = c := by
  rw [smallChainMap_zero]
  abel

end SingularChain

namespace SingularCochain

open SingularChain

section chainMapPullback

variable {R : Type*} [CommRing R] {Y : Type*} [TopologicalSpace Y]

/-- The pull-back `σ ↦ φ (L σ)` of a cochain along a linear map of chains. -/
def chainMapPullback {m n : ℕ} (L : Chain R Y m →ₗ[R] Chain R Y n) (φ : Simplex Y n → R) :
    Simplex Y m → R :=
  fun σ ↦ eval φ (L (single σ 1))

/-- Evaluating the pull-back of `φ` along `L` on `c` is evaluating `φ` on `L c`. -/
lemma eval_chainMapPullback {m n : ℕ} (L : Chain R Y m →ₗ[R] Chain R Y n) (φ : Simplex Y n → R)
    (c : Chain R Y m) : eval (chainMapPullback L φ) c = eval φ (L c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single σ a =>
    rw [← mul_one a, ← smul_eq_mul, ← smul_single, map_smul, map_smul, map_smul]
    simp [chainMapPullback]

/-- Evaluating a cochain on a single simplex `σ` gives its value at `σ`. -/
lemma eval_single_one {n : ℕ} (φ : Simplex Y n → R) (σ : Simplex Y n) :
    eval φ (single σ 1) = φ σ := by
  simp

/-- `δ φ σ = φ (∂ σ)`. -/
lemma coboundary_apply_eq_eval (n : ℕ) (φ : Simplex Y n → R) (σ : Simplex Y (n + 1)) :
    coboundary R n φ σ = eval φ (bd R n (single σ 1)) := by
  rw [← eval_coboundary, eval_single_one]

/-- Evaluation of chains is additive in the cochain: `(φ - ψ)(c) = φ c - ψ c`. -/
lemma eval_sub_cochain {n : ℕ} (φ ψ : Simplex Y n → R) (c : Chain R Y n) :
    eval (φ - ψ) c = eval φ c - eval ψ c := by
  simp only [linearCombination_apply, smul_eq_mul, Pi.sub_apply, mul_sub]
  exact Finsupp.sum_sub

/-- Cochains agreeing on the simplices of `A` and of `B` agree on `{A, B}`-small chains. -/
lemma eval_eq_of_eqOn_small {n : ℕ} {A B : Set Y} {φ ψ : Simplex Y n → R}
    (h : ∀ σ : Simplex Y n, range σ ⊆ A ∨ range σ ⊆ B → φ σ = ψ σ) {c : Chain R Y n}
    (hc : c ∈ small R n {A, B}) : eval φ c = eval ψ c := by
  have := eval_eq_zero_of_mem_small (χ := φ - ψ)
    ⟨fun σ hσ ↦ sub_eq_zero.2 (h σ (Or.inl hσ)), fun σ hσ ↦ sub_eq_zero.2 (h σ (Or.inr hσ))⟩ hc
  rwa [eval_sub_cochain, sub_eq_zero] at this

/-- If `L` preserves chains supported in `A`, the pull-back along `L` of a cochain vanishing on
`A` vanishes on `A`. -/
lemma chainMapPullback_mem_vanishing {m n : ℕ} {L : Chain R Y m →ₗ[R] Chain R Y n} {A : Set Y}
    (hL : ∀ c, c ∈ inside R m A → L c ∈ inside R n A) {φ : Simplex Y n → R}
    (hφ : φ ∈ vanishing R n A) : chainMapPullback L φ ∈ vanishing R m A := fun _ hσ ↦
  eval_eq_zero_of_mem_vanishing hφ (hL _ (single_mem_inside hσ))

end chainMapPullback

section extend

variable {R : Type u} [CommRing R] {Y : TopCat.{u}} {V : Set Y}

/-- A singular simplex of `Y` with image in `V`, as a singular simplex of `V`. -/
def liftSimplex {n : ℕ} (σ : Simplex Y n) (h : range σ ⊆ V) : Simplex (TopCat.of V) n :=
  ⟨fun t ↦ ⟨σ t, h ⟨t, rfl⟩⟩, σ.continuous.subtype_mk _⟩

/-- Lifting a simplex into `V` commutes with precomposition by a map of standard simplices. -/
lemma liftSimplex_comp {m n : ℕ} (σ : Simplex Y n) (h : range σ ⊆ V)
    (f : C(stdSimplex ℝ (Fin (m + 1)), stdSimplex ℝ (Fin (n + 1)))) :
    liftSimplex (σ.comp f) (range_comp_subset h f) = (liftSimplex σ h).comp f :=
  rfl

/-- A simplex of `V`, viewed in `Y`, has image in `V`. -/
lemma range_subspaceInclusion_comp {n : ℕ} (τ : Simplex (TopCat.of V) n) :
    range ((subspaceInclusion Y V).hom.comp τ) ⊆ V := by
  rintro _ ⟨t, rfl⟩
  exact (τ t).2

/-- Lifting a simplex of `V`, viewed in `Y`, back into `V` gives the original simplex. -/
lemma liftSimplex_subspaceInclusion_comp {n : ℕ} (τ : Simplex (TopCat.of V) n) :
    liftSimplex ((subspaceInclusion Y V).hom.comp τ) (range_subspaceInclusion_comp τ) = τ :=
  rfl

/-- A simplex of `Y` with image in `V`, lifted into `V` and viewed in `Y`, is itself. -/
lemma subspaceInclusion_comp_liftSimplex {n : ℕ} (σ : Simplex Y n) (h : range σ ⊆ V) :
    (subspaceInclusion Y V).hom.comp (liftSimplex σ h) = σ :=
  rfl

open Classical in
/-- A cochain of `V ⊆ Y` extended by zero to the simplices of `Y` not lying in `V`. -/
def extendCochain {n : ℕ} (ψ : Simplex (TopCat.of V) n → R) : Simplex Y n → R :=
  fun σ ↦ if h : range σ ⊆ V then ψ (liftSimplex σ h) else 0

/-- On a simplex with image in `V`, the extension by zero of `ψ` is `ψ` of its lift. -/
lemma extendCochain_of_subset {n : ℕ} (ψ : Simplex (TopCat.of V) n → R) {σ : Simplex Y n}
    (h : range σ ⊆ V) : extendCochain ψ σ = ψ (liftSimplex σ h) := by
  simp [extendCochain, h]

/-- Restricting the extension by zero of `ψ` to `V` gives `ψ`. -/
lemma cochainPullback_extendCochain {n : ℕ} (ψ : Simplex (TopCat.of V) n → R) :
    cochainPullback R (subspaceInclusion Y V) n (extendCochain ψ) = ψ := by
  ext τ
  rw [cochainPullback_apply, extendCochain_of_subset ψ (range_subspaceInclusion_comp τ)]
  rfl

/-- The extension by zero of the zero cochain is zero. -/
lemma extendCochain_zero {n : ℕ} :
    extendCochain (V := V) (0 : Simplex (TopCat.of V) n → R) = 0 := by
  ext σ
  by_cases h : range σ ⊆ V <;> simp [extendCochain, h]

/-- Extension by zero commutes with negation. -/
lemma extendCochain_neg {n : ℕ} (ψ : Simplex (TopCat.of V) n → R) :
    extendCochain (-ψ) = -extendCochain (V := V) ψ := by
  ext σ
  by_cases h : range σ ⊆ V <;> simp [extendCochain, h]

/-- The extension by zero of a cochain of `V` vanishing on `V ∩ A` vanishes on `A`. -/
lemma extendCochain_mem_vanishing {n : ℕ} {A : Set Y} {ψ : Simplex (TopCat.of V) n → R}
    (hψ : ψ ∈ vanishing R n ((subspaceInclusion Y V) ⁻¹' A)) :
    extendCochain ψ ∈ vanishing R n A := fun σ hσ ↦ by
  by_cases h : range σ ⊆ V
  · rw [extendCochain_of_subset ψ h]
    exact hψ _ fun _ ⟨t, ht⟩ ↦ ht ▸ hσ ⟨t, rfl⟩
  · simp [extendCochain, h]

/-- On simplices lying in `V` or in `A`, the coboundary commutes with extension by zero, for a
cochain vanishing on `V ∩ A`. -/
lemma coboundary_extendCochain {n : ℕ} {A : Set Y} {ψ : Simplex (TopCat.of V) n → R}
    (hψ : ψ ∈ vanishing R n ((subspaceInclusion Y V) ⁻¹' A)) {σ : Simplex Y (n + 1)}
    (hσ : range σ ⊆ V ∨ range σ ⊆ A) :
    coboundary R n (extendCochain ψ) σ = extendCochain (coboundary R n ψ) σ := by
  rcases hσ with hσ | hσ
  · rw [extendCochain_of_subset _ hσ, coboundary_apply, coboundary_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [extendCochain_of_subset _ (range_comp_subset hσ _), liftSimplex_comp]
  · rw [coboundary_mem_vanishing (extendCochain_mem_vanishing hψ) σ hσ,
      extendCochain_mem_vanishing (coboundary_mem_vanishing hψ) σ hσ]

end extend

section excision

/-- `(g⁻¹ X)ᶜ ⊆ g⁻¹ (Xᶜ)`. -/
lemma compl_preimage_subset_preimage_compl {Y' Y : TopCat.{u}} (g : Y' ⟶ Y) (X : Set Y) :
    (g ⁻¹' X)ᶜ ⊆ g ⁻¹' Xᶜ :=
  fun _ hx ↦ hx

variable {R : Type u} [CommRing R] {Y : TopCat.{u}} {V X : Set Y}

/-- The cover `{V, Y - X}` of `Y`. -/
abbrev excisionCover (V X : Set Y) : Set (Set Y) := {V, Xᶜ}

/-- For `V` open and `X` closed, the cover `{V, Y - X}` consists of open sets. -/
lemma isOpen_of_mem_excisionCover (hV : IsOpen V) (hX : IsClosed X) :
    ∀ U ∈ excisionCover V X, IsOpen U := by
  rintro U (rfl | rfl)
  · exact hV
  · exact hX.isOpen_compl

/-- For `V` open, `X` closed and `X ⊆ V`, the chain map `ρ` of the theorem of small chains takes
values in `{V, Y - X}`-small chains. -/
lemma smallChainMap_mem_small_excisionCover (hV : IsOpen V) (hX : IsClosed X) (hXV : X ⊆ V)
    (n : ℕ) (c : Chain R Y n) : smallChainMap R (excisionCover V X) n c ∈
      small R n (excisionCover V X) :=
  smallChainMap_mem_small (isOpen_of_mem_excisionCover hV hX) n (by
    refine (mem_supported R c).2 fun σ _ ↦ ?_
    change range σ ⊆ ⋃₀ excisionCover V X
    intro y _
    by_cases hy : y ∈ X
    · exact mem_sUnion.2 ⟨V, Or.inl rfl, hXV hy⟩
    · exact mem_sUnion.2 ⟨Xᶜ, Or.inr rfl, hy⟩)

/-- Surjectivity half of excision: every relative cocycle of `(V, V - X)` is cohomologous to the
restriction of a relative cocycle of `(Y, Y - X)`. -/
lemma exists_relCocycles_cochainPullback_sub_mem (hV : IsOpen V) (hX : IsClosed X)
    (hXV : X ⊆ V) {n : ℕ} {ψ : Simplex (TopCat.of V) n → R}
    (hψ : ψ ∈ relCocycles R ((subspaceInclusion Y V) ⁻¹' X)ᶜ n) :
    ∃ φ ∈ relCocycles R Xᶜ n, cochainPullback R (subspaceInclusion Y V) n φ - ψ ∈
      relCoboundaries R ((subspaceInclusion Y V) ⁻¹' X)ᶜ n := by
  set g := subspaceInclusion Y V
  set 𝒰 := excisionCover V X
  rw [mem_relCocycles_iff] at hψ
  have hψv : ψ ∈ vanishing R n (g ⁻¹' Xᶜ) := hψ.1
  have hsmall := smallChainMap_mem_small_excisionCover (R := R) hV hX hXV
  have hδ : ∀ c : Chain R Y (n + 1), c ∈ small R (n + 1) 𝒰 →
      eval (coboundary R n (extendCochain ψ)) c = 0 := fun c hc ↦ by
    rw [eval_eq_of_eqOn_small (ψ := extendCochain (coboundary R n ψ))
      (fun σ hσ ↦ coboundary_extendCochain hψv hσ) hc, hψ.2, extendCochain_zero]
    simp
  refine ⟨chainMapPullback (smallChainMap R 𝒰 n) (extendCochain ψ), ?_, ?_⟩
  · rw [mem_relCocycles_iff]
    refine ⟨chainMapPullback_mem_vanishing (fun c hc ↦ smallChainMap_mem_inside 𝒰 n hc)
      (extendCochain_mem_vanishing hψv), ?_⟩
    ext σ
    rw [coboundary_apply_eq_eval, eval_chainMapPullback, ← bd_smallChainMap, ← eval_coboundary]
    exact hδ _ (hsmall _ _)
  · have hD : ∀ τ : Simplex (TopCat.of V) n,
        eval (extendCochain ψ) (bd R n (smallHomotopy R 𝒰 n (single (g.hom.comp τ) 1))) = 0 :=
      fun τ ↦ by
        rw [← eval_coboundary]
        exact hδ _ (mem_small_of_mem_inside (Or.inl rfl)
          (smallHomotopy_mem_inside 𝒰 n (single_mem_inside (range_subspaceInclusion_comp τ))))
    cases n with
    | zero =>
      have : cochainPullback R g 0 (chainMapPullback (smallChainMap R 𝒰 0) (extendCochain ψ)) =
          ψ := by
        ext τ
        change eval (extendCochain ψ) (smallChainMap R 𝒰 0 (single (g.hom.comp τ) 1)) = ψ τ
        have e := smallChainMap_add_zero (R := R) 𝒰 (single (g.hom.comp τ) 1)
        rw [← eq_sub_iff_add_eq] at e
        rw [e, map_sub, hD, sub_zero, eval_single_one, extendCochain_of_subset _
          (range_subspaceInclusion_comp τ), liftSimplex_subspaceInclusion_comp]
      rw [this, sub_self]
      exact Submodule.zero_mem _
    | succ k =>
      have hθ : chainMapPullback (smallHomotopy R 𝒰 k) (extendCochain ψ) ∈ vanishing R k Xᶜ :=
        chainMapPullback_mem_vanishing (fun c hc ↦ smallHomotopy_mem_inside 𝒰 k hc)
          (extendCochain_mem_vanishing hψv)
      refine ⟨-cochainPullback R g k (chainMapPullback (smallHomotopy R 𝒰 k) (extendCochain ψ)),
        Submodule.neg_mem _ (cochainPullback_mem_vanishing g (fun _ hx ↦ hx) hθ), ?_⟩
      rw [map_neg, coboundary_cochainPullback]
      ext τ
      change -(coboundary R k (chainMapPullback (smallHomotopy R 𝒰 k) (extendCochain ψ))
          (g.hom.comp τ)) = eval (extendCochain ψ) (smallChainMap R 𝒰 (k + 1)
            (single (g.hom.comp τ) 1)) - ψ τ
      have e := smallChainMap_add_succ (R := R) 𝒰 k (single (g.hom.comp τ) 1)
      rw [add_assoc, ← eq_sub_iff_add_eq] at e
      rw [e, map_sub, map_add, hD, zero_add, eval_single_one, extendCochain_of_subset _
        (range_subspaceInclusion_comp τ), liftSimplex_subspaceInclusion_comp,
        coboundary_apply_eq_eval, eval_chainMapPullback]
      ring

/-- Injectivity half of excision: a relative cocycle of `(Y, Y - X)` whose restriction to `V`
is a relative coboundary of `(V, V - X)` is a relative coboundary. -/
lemma mem_relCoboundaries_of_cochainPullback_mem (hV : IsOpen V) (hX : IsClosed X)
    (hXV : X ⊆ V) {n : ℕ} {φ : Simplex Y n → R} (hφ : φ ∈ relCocycles R Xᶜ n)
    (hg : cochainPullback R (subspaceInclusion Y V) n φ ∈
      relCoboundaries R ((subspaceInclusion Y V) ⁻¹' X)ᶜ n) :
    φ ∈ relCoboundaries R Xᶜ n := by
  set g := subspaceInclusion Y V
  set 𝒰 := excisionCover V X
  rw [mem_relCocycles_iff] at hφ
  have hsmall := smallChainMap_mem_small_excisionCover (R := R) hV hX hXV
  have hlift : ∀ σ : Simplex Y n, ∀ h : range σ ⊆ V,
      φ σ = cochainPullback R g n φ (liftSimplex σ h) := fun σ h ↦ by
    rw [cochainPullback_apply, subspaceInclusion_comp_liftSimplex]
  cases n with
  | zero =>
    have hg0 : cochainPullback R g 0 φ = 0 := (Submodule.mem_bot R).1 hg
    have : φ = 0 := by
      ext σ
      have e := smallChainMap_add_zero (R := R) 𝒰 (single σ 1)
      rw [Pi.zero_apply, ← eval_single_one φ σ, ← e, map_add, ← eval_coboundary, hφ.2]
      simp only [Finsupp.linearCombination_zero, LinearMap.zero_apply, add_zero]
      rw [eval_eq_of_eqOn_small (ψ := 0) (fun τ hτ ↦ ?_) (hsmall _ _)]
      · simp
      · rcases hτ with hτ | hτ
        · rw [hlift τ hτ, hg0]
          rfl
        · exact hφ.1 τ hτ
    rw [this]
    exact Submodule.zero_mem _
  | succ k =>
    obtain ⟨η, hη, hηφ⟩ := hg
    have hηv : η ∈ vanishing R k (g ⁻¹' Xᶜ) := hη
    let η' : Simplex Y k → R := extendCochain η
    have hη' : η' ∈ vanishing R k Xᶜ := extendCochain_mem_vanishing hηv
    have hagree : ∀ τ : Simplex Y (k + 1), range τ ⊆ V ∨ range τ ⊆ Xᶜ →
        φ τ = coboundary R k η' τ := fun τ hτ ↦ by
      rw [coboundary_extendCochain hηv hτ]
      rcases hτ with hτ | hτ
      · rw [hlift τ hτ, extendCochain_of_subset _ hτ, ← hηφ]
      · rw [hφ.1 τ hτ, extendCochain_mem_vanishing (coboundary_mem_vanishing hηv) τ hτ]
    refine ⟨chainMapPullback (smallChainMap R 𝒰 k) η' +
      chainMapPullback (smallHomotopy R 𝒰 k) φ, Submodule.add_mem _
        (chainMapPullback_mem_vanishing (fun c hc ↦ smallChainMap_mem_inside 𝒰 k hc) hη')
        (chainMapPullback_mem_vanishing (fun c hc ↦ smallHomotopy_mem_inside 𝒰 k hc) hφ.1), ?_⟩
    ext σ
    have h1 : φ σ = eval φ (smallChainMap R 𝒰 (k + 1) (single σ 1)) +
        eval φ (smallHomotopy R 𝒰 k (bd R k (single σ 1))) := by
      have e := smallChainMap_add_succ (R := R) 𝒰 k (single σ 1)
      conv_lhs => rw [← eval_single_one φ σ, ← e]
      rw [map_add, map_add, ← eval_coboundary (k + 1) φ, hφ.2]
      simp only [Finsupp.linearCombination_zero, LinearMap.zero_apply, add_zero]
    rw [h1, map_add, Pi.add_apply, coboundary_apply_eq_eval, coboundary_apply_eq_eval,
      eval_chainMapPullback, eval_chainMapPullback, ← bd_smallChainMap, ← eval_coboundary k η',
      eval_eq_of_eqOn_small hagree (hsmall _ _)]

variable (R) in
/-- Excision on cocycles modulo coboundaries: for `X ⊆ Y` closed and `V ⊇ X` open, restriction
`H^n(Y, Y - X) → H^n(V, V - X)` is bijective. -/
theorem bijective_relCohomologyMap_subspaceInclusion (hV : IsOpen V) (hX : IsClosed X)
    (hXV : X ⊆ V) (n : ℕ) :
    Function.Bijective (relCohomologyMap R (subspaceInclusion Y V)
      (compl_preimage_subset_preimage_compl (subspaceInclusion Y V) X) n) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H φ =>
      rw [relCohomologyMap_mk, Submodule.Quotient.mk_eq_zero] at hx
      rw [Submodule.Quotient.mk_eq_zero]
      exact mem_relCoboundaries_of_cochainPullback_mem hV hX hXV φ.2 hx
  · intro y
    induction y using Submodule.Quotient.induction_on with
    | H ψ =>
      obtain ⟨φ, hφ, hφψ⟩ := exists_relCocycles_cochainPullback_sub_mem hV hX hXV ψ.2
      refine ⟨Submodule.Quotient.mk ⟨φ, hφ⟩, ?_⟩
      rw [relCohomologyMap_mk, Submodule.Quotient.eq]
      exact hφψ

end excision

end SingularCochain

namespace cohomologyWithSupports

open SingularCochain

variable (R : Type u) [CommRing R] {Y : TopCat.{u}} {V X : Set Y}

/-- Relative singular cohomology vanishes in negative degrees. -/
lemma isZero_relativeSingularCohomology_of_neg (Y : TopCat.{u}) (A : Set Y) {j : ℤ}
    (hj : j < 0) : IsZero (relativeSingularCohomology R (ModuleCat.of R R) Y A j) :=
  ((relativeSingularCochainComplex R (ModuleCat.of R R) Y A).extend_exactAt
    ComplexShape.embeddingUpNat j (fun n hn ↦ by simp at hn; lia)).isZero_homology

/-- Excision: for `X ⊆ Y` closed and `V ⊇ X` open, the restriction
`H^j(Y, Y - X; R) → H^j(V, V - X; R)` along the inclusion of `V` is an isomorphism. -/
theorem isIso_pullback_subspaceInclusion (hV : IsOpen V) (hX : IsClosed X) (hXV : X ⊆ V)
    (j : ℤ) : IsIso (pullback R (ModuleCat.of R R) (subspaceInclusion Y V) X j) := by
  obtain ⟨n, rfl⟩ | hj := (le_or_gt 0 j).imp Int.eq_ofNat_of_zero_le id
  · rw [ConcreteCategory.isIso_iff_bijective]
    have key : ⇑(pullback R (ModuleCat.of R R) (subspaceInclusion Y V) X n).hom =
        (relativeSingularCohomologyEquiv R ((subspaceInclusion Y V) ⁻¹' X)ᶜ n).symm ∘
          relCohomologyMap R (subspaceInclusion Y V)
            (compl_preimage_subset_preimage_compl (subspaceInclusion Y V) X) n ∘
              relativeSingularCohomologyEquiv R Xᶜ n := by
      funext x
      simp only [Function.comp_apply]
      rw [← relativeSingularCohomologyEquiv_map, LinearEquiv.symm_apply_apply]
      rfl
    change Function.Bijective ⇑(pullback R (ModuleCat.of R R) (subspaceInclusion Y V) X n).hom
    rw [key]
    exact (LinearEquiv.bijective _).comp ((bijective_relCohomologyMap_subspaceInclusion R hV hX
      hXV n).comp (LinearEquiv.bijective _))
  · exact ⟨⟨0, (isZero_relativeSingularCohomology_of_neg R Y _ hj).eq_of_src _ _,
      (isZero_relativeSingularCohomology_of_neg R (TopCat.of V) _ hj).eq_of_src _ _⟩⟩

/-- Excision for cohomology with supports: `H^j(Y, Y - X; R) ≅ H^j(V, V - X; R)` for `X ⊆ Y`
closed and `V ⊇ X` open, by restriction along the inclusion of `V`. -/
def excisionIso (hV : IsOpen V) (hX : IsClosed X) (hXV : X ⊆ V) (j : ℤ) :
    cohomologyWithSupports R (ModuleCat.of R R) Y X j ≅
      cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of V) ((subspaceInclusion Y V) ⁻¹' X) j :=
  haveI := isIso_pullback_subspaceInclusion R hV hX hXV j
  asIso (pullback R (ModuleCat.of R R) (subspaceInclusion Y V) X j)

/-- The excision isomorphism is the restriction map along the inclusion of `V`. -/
@[simp]
lemma excisionIso_hom (hV : IsOpen V) (hX : IsClosed X) (hXV : X ⊆ V) (j : ℤ) :
    (excisionIso R hV hX hXV j).hom = pullback R (ModuleCat.of R R) (subspaceInclusion Y V) X j :=
  rfl

end cohomologyWithSupports

end MMP
