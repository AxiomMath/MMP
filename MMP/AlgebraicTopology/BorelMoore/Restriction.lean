module

public import MMP.AlgebraicTopology.BorelMoore.RestrictionChains
public import MMP.AlgebraicTopology.BorelMoore.Basic
/-!
# Restriction of Borel–Moore homology to an open subset (Fulton, §19.1)

For an open subset `U` of a Hausdorff space `Y` with inclusion `j`, the *restriction*
`j^* : H_i Y → H_i U` is induced by restricting locally finite chains to `U` after barycentric
subdivision (Borel–Moore, §3). A singular simplex `σ` of `Y` is subdivided over and over, a
piece being no longer subdivided once it lies in `U`; the pieces inside `U`, together with the
subdivision homotopies needed to glue them along common faces, form a chain `σ|_U` of `U`.
Precisely, the good parts `p ρ_N σ` of the chain maps `ρ_N` of
`MMP.SingularChain.towardsChainMap` stabilize on every compact subset of `U`
(`MMP.SingularChain.exists_restrCoeff_eq_goodPart`), and `σ|_U` is their limit.
It is locally finite on `U`: near a point of `U` only finitely many pieces occur. Hence a locally
finite chain `c = ∑ a_σ σ` of `Y` restricts to the locally finite chain `∑ a_σ σ|_U` of `U`, and
this is a chain map.

The restriction of chains is an instance of a general construction: an integer *kernel*
`k σ τ` from the simplices of a space `X` to those of a space `X'`, together with a continuous
`ι : X' → X`, such that `ι` maps the carrier of `τ` into that of `σ` whenever `k σ τ ≠ 0` and
the simplices `τ` with `k σ τ ≠ 0` form a locally finite family, sends locally finite chains of
`X` to locally finite chains of `X'` by `c ↦ (τ ↦ ∑ᶠ σ, k σ τ • c σ)`.

## Main definitions

* `MMP.LocallyFiniteChain.IsAdmissibleKernel`: admissible integer kernels.
* `MMP.LocallyFiniteChain.kernelMap`: the induced map of locally finite chains.
* `MMP.borelMooreHomology.restrictKernel`: the coefficients of `σ|_U`.
* `MMP.borelMooreHomology.restrictChainMap`: restriction of locally finite
  chains, a map of complexes.
* `MMP.borelMooreHomology.restrict`: the restriction `j^* : H_i Y → H_i U`.

## Main results

* `MMP.LocallyFiniteChain.kernelFun_dFun`: an admissible kernel compatible with
  the faces of single simplices commutes with the boundary of locally finite chains.

## Implementation notes

Fulton's spaces are Hausdorff, and the restriction is defined for Hausdorff `Y`. Some separation
is needed: in the line with two origins `0, 0'`, with `U` the complement of `0`, the restriction
of a path through `0` would accumulate at `0' ∈ U`, and would not be locally finite there.
Fulton also writes `a|_U` for `j^* a`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [A. Borel, J. C. Moore, *Homology theory for locally compact spaces*][borelmoore1960], §3.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicTopology Opposite Topology Set Simplicial

universe u

namespace MMP

namespace LocallyFiniteChain

variable {X X' : Type*} [TopologicalSpace X] [TopologicalSpace X'] {S T : Type*}
  {car : S → Set X} {car' : T → Set X'} {M : Type*} [AddCommGroup M]

/-- The transform of `c : S → M` by an integer kernel `k`: `τ ↦ ∑ᶠ σ, k σ τ • c σ`. -/
def kernelFun (k : S → T → ℤ) (c : S → M) : T → M := fun τ ↦ ∑ᶠ σ, k σ τ • c σ

/-- An integer kernel `k` from simplices of `X` (carriers `car`) to simplices of `X'` (carriers
`car'`) is *admissible* for `ι : X' → X` if `ι` is continuous, maps the carrier of `τ` into
that of `σ` whenever `k σ τ ≠ 0`, the carriers of `X'` are compact and nonempty, and for each
`σ` the simplices `τ` with `k σ τ ≠ 0` form a locally finite family. -/
structure IsAdmissibleKernel (ι : X' → X) (car : S → Set X) (car' : T → Set X')
    (k : S → T → ℤ) : Prop where
  /-- The map `ι` is continuous. -/
  continuous : Continuous ι
  /-- If `k σ τ ≠ 0`, then `ι` maps the carrier of `τ` into the carrier of `σ`. -/
  image_subset : ∀ σ τ, k σ τ ≠ 0 → ι '' car' τ ⊆ car σ
  /-- For each `σ`, the simplices `τ` with `k σ τ ≠ 0` form a locally finite family. -/
  isLocallyFiniteSet : ∀ σ, IsLocallyFiniteSet car' (Function.support (k σ))
  /-- The carriers of the simplices of `X'` are compact and nonempty. -/
  compact_nonempty : ∀ τ, IsCompact (car' τ) ∧ (car' τ).Nonempty

variable {ι : X' → X} {k : S → T → ℤ}

/-- If `a • m ≠ 0`, then `a ≠ 0`. -/
lemma smul_ne_zero_left {a : ℤ} {m : M} (h : a • m ≠ 0) : a ≠ 0 := fun ha ↦ h (by simp [ha])

/-- If `a • m ≠ 0`, then `m ≠ 0`. -/
lemma smul_ne_zero_right {a : ℤ} {m : M} (h : a • m ≠ 0) : m ≠ 0 := fun hm ↦ h (by simp [hm])

namespace IsAdmissibleKernel

variable (hk : IsAdmissibleKernel ι car car' k)

include hk

/-- For a locally finite chain `c`, only finitely many simplices `σ` in the support of `c` have
carrier meeting `ι '' car' τ`. -/
lemma finite_support {c : S → M} (hc : IsLocallyFiniteSet car (Function.support c)) (τ : T) :
    {σ | σ ∈ Function.support c ∧ (car σ ∩ ι '' car' τ).Nonempty}.Finite :=
  hc.finite_inter_compact ((hk.compact_nonempty τ).1.image hk.continuous)

/-- If `k σ τ ≠ 0`, then the carrier of `σ` meets `ι '' car' τ`. -/
lemma inter_nonempty {σ : S} {τ : T} (h : k σ τ ≠ 0) : (car σ ∩ ι '' car' τ).Nonempty :=
  ((hk.compact_nonempty τ).2.image ι).mono (subset_inter (hk.image_subset σ τ h) subset_rfl)

/-- The value `kernelFun k c τ` is the finite sum `∑ σ ∈ F, k σ τ • c σ` over any finset `F`
containing every `σ` with `c σ ≠ 0` and `k σ τ ≠ 0`. -/
lemma kernelFun_eq_sum (c : S → M) (τ : T) (F : Finset S)
    (hF : ∀ σ, c σ ≠ 0 → k σ τ ≠ 0 → σ ∈ F) :
    kernelFun k c τ = ∑ σ ∈ F, k σ τ • c σ :=
  finsum_eq_sum_of_support_subset _ fun σ hσ ↦
    hF σ (smul_ne_zero_right hσ) (smul_ne_zero_left hσ)

/-- The transform of a locally finite chain by an admissible kernel is locally finite. -/
lemma isLocallyFiniteSet_kernelFun {c : S → M} (hc : IsLocallyFiniteSet car (Function.support c)) :
    IsLocallyFiniteSet car' (Function.support (kernelFun k c)) := by
  intro x
  obtain ⟨V, hV, hfin⟩ := hc (ι x)
  choose W hW hWfin using fun σ ↦ hk.isLocallyFiniteSet σ x
  refine ⟨ι ⁻¹' V ∩ ⋂ σ ∈ hfin.toFinset, W σ, Filter.inter_mem
    (hk.continuous.continuousAt.preimage_mem_nhds hV)
    ((Filter.biInter_finset_mem _).2 fun σ _ ↦ hW σ), ?_⟩
  refine (hfin.toFinset.finite_toSet.biUnion fun σ _ ↦ hWfin σ).subset ?_
  rintro τ ⟨hτ, y, hy, hyV, hyW⟩
  obtain ⟨σ, hσ⟩ : ∃ σ, k σ τ • c σ ≠ 0 := by
    by_contra h
    push Not at h
    exact hτ (finsum_eq_zero_of_forall_eq_zero h)
  have hσF : σ ∈ hfin.toFinset := by
    rw [Finite.mem_toFinset]
    exact ⟨smul_ne_zero_right hσ, ι y,
      hk.image_subset σ τ (smul_ne_zero_left hσ) ⟨y, hy, rfl⟩, hyV⟩
  exact mem_iUnion₂.2 ⟨σ, hσF, smul_ne_zero_left hσ, y, hy, mem_iInter₂.1 hyW σ hσF⟩

end IsAdmissibleKernel

variable (R : Type*) [CommRing R] [Module R M]

/-- The map of locally finite chains induced by an admissible kernel. -/
def kernelMap (hk : IsAdmissibleKernel ι car car' k) :
    lfChains R M car →ₗ[R] lfChains R M car' where
  toFun c := ⟨kernelFun k c.1, hk.isLocallyFiniteSet_kernelFun c.2⟩
  map_add' c d := by
    ext τ
    classical
    let F := (hk.finite_support c.2 τ).toFinset ∪ (hk.finite_support d.2 τ).toFinset
    have hc : ∀ σ, c.1 σ ≠ 0 → k σ τ ≠ 0 → σ ∈ F := fun σ h1 h2 ↦
      Finset.mem_union_left _ ((Finite.mem_toFinset _).2 ⟨h1, hk.inter_nonempty h2⟩)
    have hd : ∀ σ, d.1 σ ≠ 0 → k σ τ ≠ 0 → σ ∈ F := fun σ h1 h2 ↦
      Finset.mem_union_right _ ((Finite.mem_toFinset _).2 ⟨h1, hk.inter_nonempty h2⟩)
    have hcd : ∀ σ, (c + d).1 σ ≠ 0 → k σ τ ≠ 0 → σ ∈ F := fun σ h1 h2 ↦ by
      by_cases h : c.1 σ = 0
      · exact hd σ (fun h' ↦ h1 (by simp [h, h'])) h2
      · exact hc σ h h2
    change kernelFun k (c + d).1 τ = kernelFun k c.1 τ + kernelFun k d.1 τ
    rw [hk.kernelFun_eq_sum _ τ F hcd, hk.kernelFun_eq_sum _ τ F hc,
      hk.kernelFun_eq_sum _ τ F hd, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    simp [smul_add]
  map_smul' r c := by
    ext τ
    let F := (hk.finite_support c.2 τ).toFinset
    have hc : ∀ σ, c.1 σ ≠ 0 → k σ τ ≠ 0 → σ ∈ F := fun σ h1 h2 ↦
      (Finite.mem_toFinset _).2 ⟨h1, hk.inter_nonempty h2⟩
    have hrc : ∀ σ, (r • c).1 σ ≠ 0 → k σ τ ≠ 0 → σ ∈ F := fun σ h1 h2 ↦
      hc σ (fun h ↦ h1 (by simp [h])) h2
    change kernelFun k (r • c).1 τ = r • kernelFun k c.1 τ
    rw [hk.kernelFun_eq_sum _ τ F hrc, hk.kernelFun_eq_sum _ τ F hc, Finset.smul_sum]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    simp [smul_comm r]

/-- The underlying function of `kernelMap R hk c` is `kernelFun k c`. -/
lemma kernelMap_apply_coe (hk : IsAdmissibleKernel ι car car' k) (c : lfChains R M car) :
    (kernelMap R hk c : T → M) = kernelFun k c.1 := rfl

/-- The alternating sum `∑ i, (-1) ^ i • φ_i` of the push-forwards along face maps `φ_i`. -/
def dFun {S' : Type*} {m : ℕ} (φ : Fin m → S' → S) (c : S' → M) : S → M :=
  fun σ ↦ ∑ i : Fin m, ((-1 : ℤ) ^ (i : ℕ)) • pushforwardFun (φ i) c σ

open Classical in
/-- An admissible kernel compatible with the faces of single simplices commutes with the
alternating sums of face maps on locally finite chains. -/
lemma kernelFun_dFun {S' T' : Type*} {carS' : S' → Set X} {carT' : T' → Set X'}
    {k' : S' → T' → ℤ} (hk : IsAdmissibleKernel ι car car' k)
    (hk' : IsAdmissibleKernel ι carS' carT' k') {m : ℕ} (φ : Fin m → S' → S)
    (ψ : Fin m → T' → T) (hφ : ∀ i σ, car (φ i σ) ⊆ carS' σ)
    (hψ : ∀ i τ, car' (ψ i τ) ⊆ carT' τ)
    (hcomm : ∀ σ τ, ∑ i : Fin m, (-1 : ℤ) ^ (i : ℕ) * ∑ᶠ τ', (if ψ i τ' = τ then k' σ τ' else 0) =
      ∑ i : Fin m, (-1 : ℤ) ^ (i : ℕ) * k (φ i σ) τ)
    {c : S' → M} (hc : IsLocallyFiniteSet carS' (Function.support c)) :
    kernelFun k (dFun φ c) = dFun ψ (kernelFun k' c) := by
  classical
  funext τ
  set K := ι '' car' τ
  have hK : IsCompact K := (hk.compact_nonempty τ).1.image hk.continuous
  have hKne : K.Nonempty := (hk.compact_nonempty τ).2.image ι
  let A := (hc.finite_inter_compact hK).toFinset
  have hA : ∀ σ, c σ ≠ 0 → K ⊆ carS' σ → σ ∈ A := fun σ h1 h2 ↦
    (Finite.mem_toFinset _).2 ⟨h1, hKne.mono (subset_inter h2 subset_rfl)⟩
  let A₀ := Finset.univ.biUnion fun i ↦ A.image (φ i)
  have hterm : ∀ σ₀, k σ₀ τ • dFun φ c σ₀ = ∑ i : Fin m, ∑ σ ∈ A,
      (-1 : ℤ) ^ (i : ℕ) • (if φ i σ = σ₀ then k σ₀ τ • c σ else 0) := by
    intro σ₀
    by_cases h : k σ₀ τ = 0
    · simp [h]
    rw [dFun, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [pushforwardFun_apply_eq_sum (φ i) c σ₀ A (fun σ h1 h2 ↦
      hA σ h1 ((hk.image_subset σ₀ τ h).trans (h2 ▸ hφ i σ))), Finset.smul_sum,
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    split_ifs <;> simp [smul_comm (k σ₀ τ)]
  have hL : kernelFun k (dFun φ c) τ =
      ∑ σ ∈ A, (∑ i : Fin m, (-1 : ℤ) ^ (i : ℕ) * k (φ i σ) τ) • c σ := by
    rw [kernelFun, finsum_eq_sum_of_support_subset (s := A₀) _ (fun σ₀ hσ₀ ↦ by
      have h1 : k σ₀ τ ≠ 0 := smul_ne_zero_left hσ₀
      obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (smul_ne_zero_right hσ₀)
      obtain ⟨σ, hσ, rfl⟩ := support_pushforwardFun_subset (φ i) c (smul_ne_zero_right hi)
      exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finset.mem_image_of_mem _
        (hA σ hσ ((hk.image_subset _ τ h1).trans (hφ i σ)))⟩)]
    simp_rw [hterm]
    rw [Finset.sum_comm]
    have : ∀ i : Fin m, ∑ σ₀ ∈ A₀, ∑ σ ∈ A, (-1 : ℤ) ^ (i : ℕ) •
        (if φ i σ = σ₀ then k σ₀ τ • c σ else 0) =
        ∑ σ ∈ A, (-1 : ℤ) ^ (i : ℕ) • (k (φ i σ) τ • c σ) := fun i ↦ by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun σ hσ ↦ ?_
      rw [← Finset.smul_sum, Finset.sum_ite_eq, if_pos (Finset.mem_biUnion.2
        ⟨i, Finset.mem_univ _, Finset.mem_image_of_mem _ hσ⟩)]
    rw [Finset.sum_congr rfl fun i _ ↦ this i, Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [mul_smul]
  let B := A.biUnion fun σ ↦
    ((hk'.isLocallyFiniteSet σ).finite_inter_compact (hk.compact_nonempty τ).1).toFinset
  have hB : ∀ σ ∈ A, ∀ i τ', k' σ τ' ≠ 0 → ψ i τ' = τ → τ' ∈ B := fun σ hσ i τ' h1 h2 ↦
    Finset.mem_biUnion.2 ⟨σ, hσ, (Finite.mem_toFinset _).2
      ⟨h1, (hk.compact_nonempty τ).2.mono (subset_inter (h2 ▸ hψ i τ') subset_rfl)⟩⟩
  have hKsub : ∀ σ i τ', k' σ τ' ≠ 0 → ψ i τ' = τ → K ⊆ carS' σ := fun σ i τ' h1 h2 ↦
    (image_mono (h2 ▸ hψ i τ')).trans (hk'.image_subset σ τ' h1)
  have hg : ∀ i τ', ψ i τ' = τ → kernelFun k' c τ' = ∑ σ ∈ A, k' σ τ' • c σ :=
    fun i τ' h ↦ hk'.kernelFun_eq_sum c τ' A fun σ h1 h2 ↦ hA σ h1 (hKsub σ i τ' h2 h)
  have hR : dFun ψ (kernelFun k' c) τ = ∑ σ ∈ A,
      (∑ i : Fin m, (-1 : ℤ) ^ (i : ℕ) * ∑ τ' ∈ B, if ψ i τ' = τ then k' σ τ' else 0) • c σ := by
    rw [dFun]
    have : ∀ i, pushforwardFun (ψ i) (kernelFun k' c) τ =
        ∑ τ' ∈ B, ∑ σ ∈ A, (if ψ i τ' = τ then k' σ τ' else 0) • c σ := fun i ↦ by
      rw [pushforwardFun_apply_eq_sum (ψ i) _ τ B (fun τ' h1 h2 ↦ by
        obtain ⟨σ, hσ⟩ : ∃ σ, k' σ τ' • c σ ≠ 0 := by
          by_contra h
          push Not at h
          exact h1 (finsum_eq_zero_of_forall_eq_zero h)
        exact hB σ (hA σ (smul_ne_zero_right hσ) (hKsub σ i τ' (smul_ne_zero_left hσ) h2)) i τ'
          (smul_ne_zero_left hσ) h2)]
      refine Finset.sum_congr rfl fun τ' _ ↦ ?_
      split_ifs with h
      · rw [hg i τ' h]
      · simp
    simp_rw [this, Finset.smul_sum, Finset.sum_smul, Finset.mul_sum, Finset.sum_smul]
    rw [Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ ↦ Finset.sum_congr rfl fun i _ ↦
      Finset.sum_congr rfl fun τ' _ ↦ ?_
    rw [mul_smul]
  rw [hL, hR]
  refine Finset.sum_congr rfl fun σ hσ ↦ ?_
  rw [← hcomm]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  exact finsum_eq_sum_of_support_subset (s := B) _ (fun τ' hτ' ↦ by
    rw [Function.mem_support] at hτ'
    by_cases h1 : ψ i τ' = τ
    · rw [if_pos h1] at hτ'
      exact hB σ hσ i τ' hτ' h1
    · rw [if_neg h1] at hτ'
      exact absurd rfl hτ')

end LocallyFiniteChain

namespace SingularChain

variable {R : Type*} [CommRing R] {Y : Type*} [TopologicalSpace Y]

open Classical in
/-- The coefficient of `τ` in the boundary of a finite chain `e` is
`∑ i, (-1) ^ i * ∑ τ' ∈ e.support, [τ' ∘ face n i = τ] e τ'`. -/
lemma bd_apply (n : ℕ) (e : Chain R Y (n + 1)) (τ : Simplex Y n) :
    bd R n e τ = ∑ i : Fin (n + 2), (-1 : R) ^ (i : ℕ) *
      ∑ τ' ∈ e.support, if τ'.comp (face n i) = τ then e τ' else 0 := by
  rw [bd, Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.finset_sum_apply]
  simp only [Finsupp.smul_apply, Finsupp.finset_sum_apply, Finsupp.single_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun τ' _ ↦ ?_
  split_ifs <;> ring

end SingularChain

namespace borelMooreHomology

open SingularChain LocallyFiniteChain

section kernel

variable {Y : TopCat.{u}} (U : TopologicalSpace.Opens Y)

/-- A singular simplex of `U`, as a singular simplex of `Y`. -/
def inclSimplex {n : ℕ} (τ : (TopCat.toSSet.obj (TopCat.of U)).obj (op ⦋n⦌)) : Simplex Y n :=
  (⟨Subtype.val, continuous_subtype_val⟩ : C(U, Y)).comp (SingularCochain.simplexEquiv (TopCat.of U) n τ)

/-- The map `inclSimplex U` on `n`-simplices is injective. -/
lemma inclSimplex_injective (n : ℕ) :
    Function.Injective (inclSimplex U (n := n)) := fun τ τ' h ↦ by
  apply (SingularCochain.simplexEquiv (TopCat.of U) n).injective
  ext t : 1
  exact Subtype.val_injective (congrArg (fun f : Simplex Y n ↦ f t) h)

/-- The range of `inclSimplex U τ` is the image in `Y` of the image of the simplex `τ`. -/
lemma range_inclSimplex {n : ℕ} (τ : (TopCat.toSSet.obj (TopCat.of U)).obj (op ⦋n⦌)) :
    range (inclSimplex U τ) = Subtype.val '' singularSimplexImage (TopCat.of U) τ := by
  rw [← range_simplexEquiv, ← range_comp]
  rfl

/-- The range of `inclSimplex U τ` lies in `U`. -/
lemma range_inclSimplex_subset {n : ℕ} (τ : (TopCat.toSSet.obj (TopCat.of U)).obj (op ⦋n⦌)) :
    range (inclSimplex U τ) ⊆ U := by
  rintro _ ⟨t, rfl⟩
  exact (SingularCochain.simplexEquiv (TopCat.of U) n τ t).2

/-- A singular simplex of `Y` with range in `U` is of the form `inclSimplex U τ`. -/
lemma mem_range_inclSimplex {n : ℕ} {τ : Simplex Y n} (h : range τ ⊆ U) :
    τ ∈ range (inclSimplex U (n := n)) :=
  ⟨(SingularCochain.simplexEquiv (TopCat.of U) n).symm ⟨fun t ↦ ⟨τ t, h ⟨t, rfl⟩⟩, τ.continuous.subtype_mk _⟩, by
    ext t
    simp [inclSimplex]⟩

/-- The map `inclSimplex U` commutes with the face maps. -/
lemma inclSimplex_δ {n : ℕ} (i : Fin (n + 2))
    (τ : (TopCat.toSSet.obj (TopCat.of U)).obj (op ⦋n + 1⦌)) :
    inclSimplex U ((TopCat.toSSet.obj (TopCat.of U)).δ i τ) =
      (inclSimplex U τ).comp (face n i) := by
  unfold inclSimplex
  conv_lhs => rw [← (SingularCochain.simplexEquiv (TopCat.of U) (n + 1)).symm_apply_apply τ,
    SingularCochain.simplexEquiv_symm_δ, Equiv.apply_symm_apply]
  rfl

/-- Under `simplexEquiv`, the `i`-th face of `σ` is the composite of `σ` with `face n i`. -/
lemma toSSetObjEquiv_δ {n : ℕ} (i : Fin (n + 2)) (σ : (TopCat.toSSet.obj Y).obj (op ⦋n + 1⦌)) :
    (SingularCochain.simplexEquiv Y n ((TopCat.toSSet.obj Y).δ i σ)) =
      (SingularCochain.simplexEquiv Y (n + 1) σ).comp (face n i) := by
  conv_lhs => rw [← (SingularCochain.simplexEquiv Y (n + 1)).symm_apply_apply σ,
    SingularCochain.simplexEquiv_symm_δ, Equiv.apply_symm_apply]

/-- The coefficient of a simplex `τ` of `U` in the restriction `σ|_U` of a simplex `σ` of `Y`. -/
def restrictKernel (n : ℕ) (σ : (TopCat.toSSet.obj Y).obj (op ⦋n⦌))
    (τ : (TopCat.toSSet.obj (TopCat.of U)).obj (op ⦋n⦌)) : ℤ :=
  restrCoeff ℤ (U : Set Y) (SingularCochain.simplexEquiv Y n σ) (inclSimplex U τ)

variable [T2Space Y]

/-- The kernel `restrictKernel U n` is admissible for the inclusion of `U` into `Y`, with the
images of singular simplices as carriers. -/
lemma isAdmissibleKernel_restrictKernel (n : ℕ) :
    IsAdmissibleKernel (Subtype.val : U → Y) (singularSimplexImage Y (n := op ⦋n⦌))
      (singularSimplexImage (TopCat.of U) (n := op ⦋n⦌)) (restrictKernel U n) where
  continuous := continuous_subtype_val
  image_subset σ τ h := by
    rw [← range_inclSimplex]
    exact ((range_subset_of_restrCoeff_ne_zero h).trans inter_subset_left).trans
      (range_simplexEquiv σ).subset
  isLocallyFiniteSet σ x := by
    obtain ⟨W, hW, hxW, hfin⟩ := exists_finite_restrCoeff_ne_zero (R := ℤ) U.isOpen
      (SingularCochain.simplexEquiv Y n σ) x.2
    refine ⟨Subtype.val ⁻¹' W, (hW.preimage continuous_subtype_val).mem_nhds hxW,
      (hfin.preimage (inclSimplex_injective U n).injOn).subset ?_⟩
    rintro τ ⟨hτ, y, hy, hyW⟩
    refine ⟨hτ, y.1, ?_, hyW⟩
    rw [range_inclSimplex]
    exact ⟨y, hy, rfl⟩
  compact_nonempty τ := ⟨isCompact_singularSimplexImage τ, nonempty_singularSimplexImage τ⟩

open Classical in
/-- The restriction of simplices is compatible with faces. -/
lemma restrictKernel_comm (n : ℕ) (σ : (TopCat.toSSet.obj Y).obj (op ⦋n + 1⦌))
    (τ : (TopCat.toSSet.obj (TopCat.of U)).obj (op ⦋n⦌)) :
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) * ∑ᶠ τ', (if (TopCat.toSSet.obj (TopCat.of U)).δ i τ' = τ
      then restrictKernel U (n + 1) σ τ' else 0) =
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) * restrictKernel U n ((TopCat.toSSet.obj Y).δ i σ) τ := by
  set σs : Simplex Y (n + 1) := (SingularCochain.simplexEquiv Y (n + 1) σ)
  set τs := inclSimplex U τ
  obtain ⟨W, -, hKW, N₀, ha, hb, hc⟩ := exists_restrCoeff_eq_goodPart (R := ℤ) U.isOpen σs
    (isCompact_range τs.continuous) (range_inclSimplex_subset U τ)
  have hne : (range τs ∩ W).Nonempty :=
    ⟨τs (stdSimplex.vertex 0), ⟨_, rfl⟩, hKW ⟨_, rfl⟩⟩
  set e := goodPart ℤ (U : Set Y) N₀ σs
  have hR : ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) *
      restrictKernel U n ((TopCat.toSSet.obj Y).δ i σ) τ = bd ℤ n e τs := by
    rw [hc τs hne]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [restrictKernel, toSSetObjEquiv_δ, hb i τs hne]
  rw [hR, bd_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  have hterm : ∀ τ', (if (TopCat.toSSet.obj (TopCat.of U)).δ i τ' = τ
      then restrictKernel U (n + 1) σ τ' else 0) =
      (fun τ'' ↦ if τ''.comp (face n i) = τs then e τ'' else 0) (inclSimplex U τ') := by
    intro τ'
    have hiff : (TopCat.toSSet.obj (TopCat.of U)).δ i τ' = τ ↔
        (inclSimplex U τ').comp (face n i) = τs := by
      rw [← inclSimplex_δ]
      exact (inclSimplex_injective U n).eq_iff.symm
    by_cases h : (TopCat.toSSet.obj (TopCat.of U)).δ i τ' = τ
    · rw [if_pos h]
      simp only
      rw [if_pos (hiff.1 h), restrictKernel]
      refine ha _ ⟨_, ?_, hKW ⟨stdSimplex.vertex 0, rfl⟩⟩
      rw [← hiff.1 h]
      exact ⟨_, rfl⟩
    · rw [if_neg h]
      simp only
      rw [if_neg (fun h' ↦ h (hiff.2 h'))]
  simp_rw [hterm]
  rw [finsum_eq_sum_of_support_subset (s := e.support.preimage (inclSimplex U)
    (inclSimplex_injective U (n + 1)).injOn) _ (fun τ' hτ' ↦ by
      rw [Finset.coe_preimage, mem_preimage, Finset.mem_coe, Finsupp.mem_support_iff]
      intro h0
      apply hτ'
      simp only
      split_ifs <;> simp [h0])]
  exact Finset.sum_preimage (inclSimplex U) e.support _
    (fun τ'' ↦ if τ''.comp (face n i) = τs then e τ'' else 0) fun τ'' hτ'' hnot ↦ absurd (mem_range_inclSimplex U
    ((goodPart_mem_inside (R := ℤ) (U := (U : Set Y)) (N := N₀) σs (Finset.mem_coe.2 hτ'')).trans inter_subset_right)) hnot

end kernel

section complex

variable (R : Type u) [CommRing R] (M : ModuleCat.{u} R)
  {Y : TopCat.{u}} (U : TopologicalSpace.Opens Y)

/-- The differential of the complex of locally finite chains is the alternating sum of the
push-forwards along the face maps. -/
lemma borelMooreChainComplex_d_apply (X : TopCat.{u}) (n : ℕ)
    (c : (borelMooreChainComplex R M X).X (n + 1)) :
    (((borelMooreChainComplex R M X).d (n + 1) n).hom c).1 =
      dFun (fun i : Fin (n + 2) ↦ (TopCat.toSSet.obj X).δ i) c.1 := by
  have h := congrArg (fun f ↦ (f.hom c).1)
    (AlternatingFaceMapComplex.obj_d_eq (locallyFiniteSingularChains R M X) n)
  refine h.trans ?_
  simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply, LinearMap.smul_apply,
    Submodule.coe_sum, Submodule.coe_smul_of_tower]
  funext σ
  erw [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rfl

variable [T2Space Y]

/-- Restriction of locally finite chains to the open subset `U`, a map of complexes. -/
def restrictChainMap :
    borelMooreChainComplex R M Y ⟶ borelMooreChainComplex R M (TopCat.of U) where
  f n := ModuleCat.ofHom (kernelMap R (isAdmissibleKernel_restrictKernel U n))
  comm' := by
    rintro _ n rfl
    ext c : 2
    apply Subtype.ext
    have h1 := borelMooreChainComplex_d_apply R M (TopCat.of U) n
      (kernelMap R (isAdmissibleKernel_restrictKernel U (n + 1)) c)
    have h2 := borelMooreChainComplex_d_apply R M Y n c
    change (((borelMooreChainComplex R M (TopCat.of U)).d (n + 1) n).hom
      (kernelMap R (isAdmissibleKernel_restrictKernel U (n + 1)) c)).1 =
      (kernelMap R (isAdmissibleKernel_restrictKernel U n)
        (((borelMooreChainComplex R M Y).d (n + 1) n).hom c)).1
    rw [h1]
    change dFun _ (kernelFun _ c.1) =
      kernelFun _ (((borelMooreChainComplex R M Y).d (n + 1) n).hom c).1
    rw [h2]
    exact (kernelFun_dFun (isAdmissibleKernel_restrictKernel U n)
      (isAdmissibleKernel_restrictKernel U (n + 1)) _ _
      (fun i σ ↦ singularSimplexImage_map_subset _ σ)
      (fun i τ ↦ singularSimplexImage_map_subset _ τ)
      (restrictKernel_comm U n) c.2).symm

/-- The *restriction* `j^* : H_i Y → H_i U` of Borel–Moore homology to an open subset `U` of a
Hausdorff space `Y` (Fulton, §19.1), induced by restricting locally finite chains to `U` after
barycentric subdivision. For `a ∈ H_i Y` Fulton writes `a|_U` for `j^* a`. -/
def restrict (i : ℤ) : borelMooreHomology R M Y i ⟶ borelMooreHomology R M (TopCat.of U) i :=
  HomologicalComplex.homologyMap
    (HomologicalComplex.extendMap (restrictChainMap R M U) ComplexShape.embeddingDownNat) (-i)

end complex

end borelMooreHomology

end MMP
