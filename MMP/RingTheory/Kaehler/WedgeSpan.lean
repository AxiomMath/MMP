module

public import MMP.RingTheory.Kaehler.TameLogBasis

/-!
# Wedge lattices and their coordinates

For an `R`-algebra `L` and an `L`-module `M`, the wedge lattice of an `R`-submodule `N` of `M` is
the `R`-span in `⋀[L]^p M` of the wedges of `p` vectors of `N`. When `N` is the `R`-span of a basis
`b` of `M`, the coordinates of its elements in the induced basis of `⋀[L]^p M` lie in `R`. For a
local ring `R`, a basis `b` indexed by `Fin (n + 1)` and the `R`-span `N` of `ν b₀, b₁, …, bₙ`, if
`τ` and `τ ν` come from the maximal ideal of `R`, then so does `τ` times each coordinate of an
element of the wedge lattice of `N`.

## Main definitions

* `MMP.FourfoldProofs.FractionalLogComplexProof.wedgeSpan`: the `R`-span of the `p`-fold wedges of
  vectors of an `R`-submodule.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.repr_mem_range_of_mem_wedgeSpan`: the coordinates of
  the wedge lattice of the `R`-span of a basis lie in `R`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.exteriorPower_repr_unitsSMul`: coordinates in the
  induced basis of `⋀^p` of a basis rescaled by units.
* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_mem_maximalIdeal_mul_repr`: `τ` times the
  coordinates of the wedge lattice of the span of `ν b₀, b₁, …, bₙ` lie in the maximal ideal.
-/

@[expose] public section

open IsLocalRing

namespace MMP.FourfoldProofs.FractionalLogComplexProof

section WedgeSpan

variable (R : Type*) {L M : Type*} [CommRing R] [CommRing L] [Algebra R L] [AddCommGroup M]
  [Module L M] [Module R M] [IsScalarTower R L M]

/-- The `R`-span of the `p`-fold wedges `w₁ ∧ ⋯ ∧ w_p` of vectors `wᵢ` of an `R`-submodule `N`. -/
def wedgeSpan (N : Submodule R M) (p : ℕ) : Submodule R (⋀[L]^p M) :=
  Submodule.span R {η | ∃ w : Fin p → M, (∀ i, w i ∈ N) ∧ η = exteriorPower.ιMulti L p w}

variable {R}

/-- The wedge lattice is monotone in the submodule. -/
theorem wedgeSpan_mono {N N' : Submodule R M} (h : N ≤ N') (p : ℕ) :
    wedgeSpan (L := L) R N p ≤ wedgeSpan R N' p :=
  Submodule.span_mono fun _ ⟨w, hw, he⟩ => ⟨w, fun i => h (hw i), he⟩

/-- The wedge of `p` vectors of `N` lies in the wedge lattice of `N`. -/
theorem ιMulti_mem_wedgeSpan {N : Submodule R M} {p : ℕ} {w : Fin p → M} (hw : ∀ i, w i ∈ N) :
    exteriorPower.ιMulti L p w ∈ wedgeSpan R N p :=
  Submodule.subset_span ⟨w, hw, rfl⟩

/-- The coordinates of the vectors of the `R`-span of a basis lie in `R`. -/
theorem repr_mem_range_of_mem_span {ι : Type*} (b : Module.Basis ι L M) {v : M}
    (hv : v ∈ Submodule.span R (Set.range b)) (j : ι) :
    b.repr v j ∈ (algebraMap R L).range := by
  classical
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact ⟨1, map_one _⟩
    · exact ⟨0, map_zero _⟩
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, Finsupp.add_apply]
    exact add_mem hx hy
  | smul a x _ hx =>
    rw [← algebraMap_smul L a x, map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact Subring.mul_mem _ ⟨a, rfl⟩ hx

/-- The coordinates of the elements of the wedge lattice of the `R`-span of a basis lie in `R`. -/
theorem repr_mem_range_of_mem_wedgeSpan {ι : Type*} [LinearOrder ι] (b : Module.Basis ι L M)
    {p : ℕ} {ω : ⋀[L]^p M} (hω : ω ∈ wedgeSpan R (Submodule.span R (Set.range b)) p)
    (s : Set.powersetCard ι p) :
    (b.exteriorPower p).repr ω s ∈ (algebraMap R L).range :=
  exteriorPower_repr_mem_range_of_mem_span b _ (fun _ hv j => repr_mem_range_of_mem_span b hv j)
    hω s

end WedgeSpan

section Rescale

variable {L M : Type*} [CommRing L] [AddCommGroup M] [Module L M]

/-- Rescaling a basis by units rescales the induced basis of `⋀^p` by the products of the
units. -/
theorem exteriorPower_unitsSMul_apply {ι : Type*} [LinearOrder ι] (b : Module.Basis ι L M)
    (w : ι → Lˣ) (p : ℕ) (S : Set.powersetCard ι p) :
    (b.unitsSMul w).exteriorPower p S =
      (∏ j, (w (Set.powersetCard.ofFinEmbEquiv.symm S j) : L)) • b.exteriorPower p S := by
  rw [exteriorPower.basis_apply, exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    exteriorPower.ιMulti_family, ← (exteriorPower.ιMulti L p).map_smul_univ]
  congr 1
  funext j
  simp [Module.Basis.unitsSMul_apply, Units.smul_def]

/-- The coordinates in the basis of `⋀^p` induced by `b` are the products of the units times
the coordinates in the basis induced by `b.unitsSMul w`. -/
theorem exteriorPower_repr_unitsSMul {ι : Type*} [LinearOrder ι] (b : Module.Basis ι L M)
    (w : ι → Lˣ) (p : ℕ) (x : ⋀[L]^p M) (S : Set.powersetCard ι p) :
    (b.exteriorPower p).repr x S =
      (∏ j, (w (Set.powersetCard.ofFinEmbEquiv.symm S j) : L)) *
        ((b.unitsSMul w).exteriorPower p).repr x S := by
  classical
  conv_lhs => rw [← ((b.unitsSMul w).exteriorPower p).linearCombination_repr x]
  rw [Finsupp.linearCombination_apply, map_finsuppSum, Finsupp.sum_apply]
  simp only [map_smul, exteriorPower_unitsSMul_apply, Module.Basis.repr_self, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finsupp.sum, Finset.sum_eq_single S]
  · simp only [↓reduceIte]
    rw [mul_comm]
  · intro T _ hT
    simp [hT]
  · intro hS
    simp only [↓reduceIte]
    rw [Finsupp.notMem_support_iff.1 hS, zero_mul]

end Rescale

section Regular

variable {R L M : Type*} [CommRing R] [IsLocalRing R] [CommRing L] [Algebra R L]
  [AddCommGroup M] [Module L M] [Module R M] [IsScalarTower R L M]

/-- **Coordinates of regular forms in the pulled-back regular basis.** Let `b` be a basis of `M`
indexed by `Fin (n + 1)`, and `N` the `R`-span of `ν b₀, b₁, …, bₙ` for a unit `ν` of `L`. If
`τ` and `τ ν` lie in (the image of) the maximal ideal of `R`, then for every `ω` in the wedge
lattice of `N`, `τ` times every coordinate of `ω` in the wedges of `b` lies in the maximal
ideal. -/
theorem exists_mem_maximalIdeal_mul_repr {n : ℕ} (b : Module.Basis (Fin (n + 1)) L M)
    (ν : Lˣ) {τ : L} (hτ : ∃ r ∈ maximalIdeal R, algebraMap R L r = τ)
    (hτν : ∃ r ∈ maximalIdeal R, algebraMap R L r = τ * ν) {p : ℕ} {ω : ⋀[L]^p M}
    (hω : ω ∈ wedgeSpan R (Submodule.span R (Set.range (Fin.cons ((ν : L) • b 0)
      fun i => b i.succ : Fin (n + 1) → M))) p)
    (S : Set.powersetCard (Fin (n + 1)) p) :
    ∃ r ∈ maximalIdeal R, algebraMap R L r = τ * (b.exteriorPower p).repr ω S := by
  classical
  let w : Fin (n + 1) → Lˣ := fun i => if i = 0 then ν else 1
  have hb' : ⇑(b.unitsSMul w) = (Fin.cons ((ν : L) • b 0) fun i => b i.succ :
      Fin (n + 1) → M) := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [w, Module.Basis.unitsSMul_apply, Units.smul_def]
    · simp [w, Module.Basis.unitsSMul_apply, Fin.succ_ne_zero]
  rw [← hb'] at hω
  obtain ⟨r', hr'⟩ := repr_mem_range_of_mem_wedgeSpan (b.unitsSMul w) hω S
  rw [exteriorPower_repr_unitsSMul b w, ← hr']
  set σ := Set.powersetCard.ofFinEmbEquiv.symm S
  have hprod : ∃ r ∈ maximalIdeal R, algebraMap R L r = τ * ∏ j, (w (σ j) : L) := by
    by_cases h0 : ∃ j, σ j = 0
    · obtain ⟨j₀, hj₀⟩ := h0
      have : ∏ j, (w (σ j) : L) = ν := by
        rw [Finset.prod_eq_single j₀]
        · simp [w, hj₀]
        · intro j _ hj
          have : σ j ≠ 0 := fun h => hj (σ.injective (h.trans hj₀.symm))
          simp [w, this]
        · simp
      rw [this]
      exact hτν
    · push Not at h0
      have : ∏ j, (w (σ j) : L) = 1 := Finset.prod_eq_one fun j _ => by simp [w, h0 j]
      rw [this, mul_one]
      exact hτ
  obtain ⟨r, hr, hre⟩ := hprod
  exact ⟨r * r', Ideal.mul_mem_right _ _ hr, by rw [map_mul, hre, mul_assoc]⟩

end Regular

end MMP.FourfoldProofs.FractionalLogComplexProof
