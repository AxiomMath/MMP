module

public import MMP.AlgebraicTopology.BorelMoore.Basic
public import MMP.AlgebraicTopology.BorelMoore.RestrictionHomotopy
public import MMP.AlgebraicTopology.BorelMoore.RestrictionPushforward
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
public import Mathlib.Topology.Maps.Proper.Basic
/-!
# Functoriality of restriction in Borel–Moore homology (Fulton, §19.1)

For open subsets `U' ⊆ U ⊆ Y` of a Hausdorff space and `a ∈ H_j Y`, `(a|_U)|_{U'} = a|_{U'}`;
and `H_j ∅ = 0`. Here `U'` is read as an open subset of `U` through the canonical
homeomorphism between `U'` and its preimage in `U`.

The empty space has no singular simplices, so its complex of locally finite chains is zero and
its Borel–Moore homology vanishes in every degree.

The two restrictions do not agree on chains: subdividing a simplex `σ` towards `U` and then
towards `U'` differs from subdividing it towards `U'` directly. The difference is the boundary of
a locally finite homotopy `h σ = ∑_i (T X_i σ)|_{U'}`, where `X_i σ` are the bad simplices of
the `i`-th subdivision of `σ` towards `U` and `T` is the subdivision homotopy
(Borel–Moore, §3). Coefficientwise this is
`MMP.SingularChain.restrCoeff_sub_compCoeff_succ`; it is assembled here into a
chain homotopy between the two maps of complexes of locally finite chains.

## Main definitions

* `MMP.borelMooreHomology.subOpens`: `U'` as an open subset of `U`.
* `MMP.borelMooreHomology.subOpensHomeo`: the homeomorphism of `U'` with it.

## Main results

* `MMP.isZero_borelMooreHomology_of_isEmpty`: `H_j ∅ = 0`.
* `MMP.borelMooreHomology.restrict_comp_restrict`: `(a|_U)|_{U'} = a|_{U'}`.
* `MMP.borelMooreHomology.restrict_restrict_apply`: its element-wise form.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [A. Borel, J. C. Moore, *Homology theory for locally compact spaces*][borelmoore1960], §3.
-/

public section

open CategoryTheory Limits AlgebraicTopology Opposite Simplicial

universe u

namespace MMP

variable (R : Type u) [CommRing R] (M : ModuleCat.{u} R)

/-- A space with no points has no singular simplices. -/
lemma isEmpty_singularSimplex_of_isEmpty (X : TopCat.{u}) [IsEmpty X] (n : SimplexCategoryᵒᵖ) :
    IsEmpty ((TopCat.toSSet.obj X).obj n) :=
  ⟨fun σ ↦ (nonempty_singularSimplexImage σ).elim fun x _ ↦ IsEmpty.false x⟩

/-- **Borel–Moore homology of the empty space vanishes** (Fulton, §19.1): `H_j ∅ = 0`. -/
theorem isZero_borelMooreHomology_of_isEmpty (X : TopCat.{u}) [IsEmpty X] (j : ℤ) :
    IsZero (borelMooreHomology R M X j) := by
  have hX : ∀ n, IsZero ((borelMooreChainComplex R M X).X n) := fun n ↦ by
    haveI := isEmpty_singularSimplex_of_isEmpty X (op ⦋n⦌)
    refine @ModuleCat.isZero_of_subsingleton _ _ _ ⟨fun a b ↦ ?_⟩
    exact Subtype.ext (funext fun σ ↦ isEmptyElim σ)
  have hX' : IsZero (((borelMooreChainComplex R M X).extend
      ComplexShape.embeddingDownNat).X (-j)) := by
    by_cases h : ∃ n, ComplexShape.embeddingDownNat.f n = -j
    · obtain ⟨n, hn⟩ := h
      exact (hX n).of_iso ((borelMooreChainComplex R M X).extendXIso _ hn)
    · exact HomologicalComplex.isZero_extend_X _ _ _ fun n hn ↦ h ⟨n, hn⟩
  exact ShortComplex.isZero_homology_of_isZero_X₂ _ hX'

end MMP

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicTopology Opposite Topology Set Simplicial Finsupp

namespace MMP

namespace SingularChain

variable {R : Type*} [CommRing R] {Y : Type*} [TopologicalSpace Y]

/-- The restriction coefficients only depend on the sequence of the good parts. -/
lemma restrCoeff_congr {Y' : Type*} [TopologicalSpace Y'] {U : Set Y} {U' : Set Y'} {n : ℕ}
    {σ τ : Simplex Y n} {σ' τ' : Simplex Y' n}
    (h : ∀ N, goodPart R U N σ τ = goodPart R U' N σ' τ') :
    restrCoeff R U σ τ = restrCoeff R U' σ' τ' := by
  classical
  by_cases hs : ∃ N₀, ∀ N ≥ N₀, goodPart R U N σ τ = goodPart R U N₀ σ τ
  · obtain ⟨N₀, hN₀⟩ := hs
    rw [restrCoeff_eq hN₀, restrCoeff_eq (N₀ := N₀) (fun N hN ↦ by rw [← h, ← h]; exact hN₀ N hN),
      h]
  · have hs' : ¬∃ N₀, ∀ N ≥ N₀, goodPart R U' N σ' τ' = goodPart R U' N₀ σ' τ' := by
      simpa only [h] using hs
    rw [restrCoeff, dif_neg hs, restrCoeff, dif_neg hs']

/-- Restriction coefficients of simplices of a subspace `A ⊆ Y`, towards the trace on `A` of an
open set `V`, are those of the simplices of `Y`. -/
lemma restrCoeff_val_comp {A : Set Y} (V : Set Y) {n : ℕ} (σ τ : Simplex A n) :
    restrCoeff R (Subtype.val ⁻¹' V) σ τ =
      restrCoeff R V ((⟨Subtype.val, continuous_subtype_val⟩ : C(A, Y)).comp σ)
        ((⟨Subtype.val, continuous_subtype_val⟩ : C(A, Y)).comp τ) := by
  set f : C(A, Y) := ⟨Subtype.val, continuous_subtype_val⟩
  have hinj : Function.Injective fun σ : Simplex A n ↦ f.comp σ := fun σ σ' h ↦ by
    ext t : 1
    exact Subtype.val_injective (congrArg (fun s : Simplex Y n ↦ s t) h)
  refine (restrCoeff_congr fun N ↦ ?_).symm
  rw [goodPart_postcomp, postcomp, lmapDomain_apply]
  exact Finsupp.mapDomain_apply_of_injective hinj _ _

end SingularChain

namespace LocallyFiniteChain

variable {X X' : Type*} [TopologicalSpace X] [TopologicalSpace X'] {S T : Type*}
  {car : S → Set X} {car' : T → Set X'} {M : Type*} [AddCommGroup M]

/-- A kernel transform at `τ` as a finite sum, over the simplices of `c` meeting a compact set
`K` that every simplex with `k σ τ ≠ 0` meets. -/
lemma kernelFun_eq_sum_of_inter_nonempty (k : S → T → ℤ) {c : S → M}
    (hc : IsLocallyFiniteSet car (Function.support c)) {K : Set X} (hK : IsCompact K) (τ : T)
    (hkK : ∀ σ, k σ τ ≠ 0 → (car σ ∩ K).Nonempty) :
    kernelFun k c τ = ∑ σ ∈ (hc.finite_inter_compact hK).toFinset, k σ τ • c σ :=
  finsum_eq_sum_of_support_subset _ fun σ hσ ↦ (Set.Finite.mem_toFinset _).2
    ⟨smul_ne_zero_right hσ, hkK σ (smul_ne_zero_left hσ)⟩

/-- The push-forward along a bijection `f` with inverse `g` is `c ∘ g`. -/
lemma pushforwardFun_eq_comp {f : S → T} {g : T → S} (hgf : ∀ σ, g (f σ) = σ)
    (hfg : ∀ τ, f (g τ) = τ) (c : S → M) : pushforwardFun f c = c ∘ g := by
  classical
  funext τ
  rw [pushforwardFun_apply_eq_sum f c τ {g τ} (fun σ _ h ↦ by
    rw [Finset.mem_singleton, ← h, hgf])]
  simp [hfg]

variable {ι : X' → X} {k : S → T → ℤ}

open Classical in
/-- The transform by an admissible kernel `k` of the alternating sum `∂ c` of face maps is the
transform of `c` by the kernel `(σ, τ) ↦ ∑ i, (-1) ^ i k (φ_i σ) τ`. -/
lemma kernelFun_dFun_eq {S' : Type*} {carS' : S' → Set X} (hk : IsAdmissibleKernel ι car car' k)
    {m : ℕ} (φ : Fin m → S' → S) (hφ : ∀ i σ, car (φ i σ) ⊆ carS' σ) {c : S' → M}
    (hc : IsLocallyFiniteSet carS' (Function.support c)) :
    kernelFun k (dFun φ c) =
      kernelFun (fun σ τ ↦ ∑ i : Fin m, (-1 : ℤ) ^ (i : ℕ) * k (φ i σ) τ) c := by
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
  rw [hL]
  refine (finsum_eq_sum_of_support_subset _ fun σ hσ ↦ hA σ (smul_ne_zero_right hσ) ?_).symm
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (smul_ne_zero_left hσ)
  exact (hk.image_subset _ τ (fun h0 ↦ hi (by rw [h0, mul_zero]))).trans (hφ i σ)

open Classical in
/-- At `τ`, the alternating sum `∂` of face maps of a kernel transform is a finite double sum,
given finite sets `A`, `B` controlling the simplices of `c` and the preimages of `τ`. -/
lemma dFun_kernelFun_apply_eq_sum {S' T' : Type*} {k' : S' → T' → ℤ} {m : ℕ}
    (ψ : Fin m → T' → T) {c : S' → M} {τ : T} (A : Finset S') (B : Finset T')
    (hB : ∀ i τ', kernelFun k' c τ' ≠ 0 → ψ i τ' = τ → τ' ∈ B)
    (hg : ∀ i τ', ψ i τ' = τ → kernelFun k' c τ' = ∑ σ ∈ A, k' σ τ' • c σ) :
    dFun ψ (kernelFun k' c) τ = ∑ σ ∈ A,
      (∑ i : Fin m, (-1 : ℤ) ^ (i : ℕ) * ∑ τ' ∈ B, if ψ i τ' = τ then k' σ τ' else 0) • c σ := by
  rw [dFun]
  have : ∀ i, pushforwardFun (ψ i) (kernelFun k' c) τ =
      ∑ τ' ∈ B, ∑ σ ∈ A, (if ψ i τ' = τ then k' σ τ' else 0) • c σ := fun i ↦ by
    rw [pushforwardFun_apply_eq_sum (ψ i) _ τ B (hB i)]
    refine Finset.sum_congr rfl fun τ' _ ↦ ?_
    split_ifs with h
    · rw [hg i τ' h]
    · simp
  simp_rw [this, Finset.smul_sum, Finset.sum_smul, Finset.mul_sum, Finset.sum_smul]
  rw [Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ ↦ Finset.sum_congr rfl fun i _ ↦
    Finset.sum_congr rfl fun τ' _ ↦ ?_
  rw [mul_smul]

open Classical in
/-- The alternating sum `∂` of face maps of the transform of `c` by an admissible kernel `k'` is
the transform of `c` by the kernel `(σ, τ) ↦ ∑ i, (-1) ^ i ∑_{ψ_i τ' = τ} k' σ τ'`. -/
lemma dFun_kernelFun_eq {S' T' : Type*} {carS' : S' → Set X} {carT' : T' → Set X'}
    {k' : S' → T' → ℤ} (hk' : IsAdmissibleKernel ι carS' carT' k') {m : ℕ}
    (ψ : Fin m → T' → T) (hψ : ∀ i τ, car' (ψ i τ) ⊆ carT' τ)
    (hT : ∀ τ, IsCompact (car' τ) ∧ (car' τ).Nonempty) {c : S' → M}
    (hc : IsLocallyFiniteSet carS' (Function.support c)) :
    dFun ψ (kernelFun k' c) = kernelFun (fun σ τ ↦ ∑ i : Fin m, (-1 : ℤ) ^ (i : ℕ) *
      ∑ᶠ τ', (if ψ i τ' = τ then k' σ τ' else 0)) c := by
  funext τ
  set K := ι '' car' τ
  have hK : IsCompact K := (hT τ).1.image hk'.continuous
  have hKne : K.Nonempty := (hT τ).2.image ι
  let A := (hc.finite_inter_compact hK).toFinset
  have hA : ∀ σ, c σ ≠ 0 → K ⊆ carS' σ → σ ∈ A := fun σ h1 h2 ↦
    (Finite.mem_toFinset _).2 ⟨h1, hKne.mono (subset_inter h2 subset_rfl)⟩
  let B := A.biUnion fun σ ↦
    ((hk'.isLocallyFiniteSet σ).finite_inter_compact (hT τ).1).toFinset
  have hB : ∀ σ ∈ A, ∀ i τ', k' σ τ' ≠ 0 → ψ i τ' = τ → τ' ∈ B := fun σ hσ i τ' h1 h2 ↦
    Finset.mem_biUnion.2 ⟨σ, hσ, (Finite.mem_toFinset _).2
      ⟨h1, (hT τ).2.mono (subset_inter (h2 ▸ hψ i τ') subset_rfl)⟩⟩
  have hKsub : ∀ σ i τ', k' σ τ' ≠ 0 → ψ i τ' = τ → K ⊆ carS' σ := fun σ i τ' h1 h2 ↦
    (image_mono (h2 ▸ hψ i τ')).trans (hk'.image_subset σ τ' h1)
  rw [dFun_kernelFun_apply_eq_sum ψ A B (fun i τ' h1 h2 ↦ by
      obtain ⟨σ, hσ⟩ : ∃ σ, k' σ τ' • c σ ≠ 0 :=
        not_forall.mp fun h ↦ h1 (finsum_eq_zero_of_forall_eq_zero h)
      exact hB σ (hA σ (smul_ne_zero_right hσ) (hKsub σ i τ' (smul_ne_zero_left hσ) h2)) i τ'
        (smul_ne_zero_left hσ) h2)
    fun i τ' h ↦ hk'.kernelFun_eq_sum c τ' A fun σ h1 h2 ↦ hA σ h1 (hKsub σ i τ' h2 h)]
  have hinner : ∀ σ ∈ A, ∀ i : Fin m, ∑ᶠ τ', (if ψ i τ' = τ then k' σ τ' else 0) =
      ∑ τ' ∈ B, if ψ i τ' = τ then k' σ τ' else 0 := fun σ hσ i ↦
    finsum_eq_sum_of_support_subset (s := B) _ fun τ' hτ' ↦
      hB σ hσ i τ' (ite_ne_right_iff.1 hτ').2 (ite_ne_right_iff.1 hτ').1
  symm
  rw [kernelFun, finsum_eq_sum_of_support_subset (s := A) _ (fun σ hσ ↦ by
    have h1 := smul_ne_zero_left hσ
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
    have hi' : ∑ᶠ τ', (if ψ i τ' = τ then k' σ τ' else 0) ≠ 0 := fun h0 ↦ hi (by rw [h0, mul_zero])
    obtain ⟨τ', hτ'⟩ : ∃ τ', (if ψ i τ' = τ then k' σ τ' else 0) ≠ 0 :=
      not_forall.mp fun h ↦ hi' (finsum_eq_zero_of_forall_eq_zero h)
    obtain ⟨h2, hτ'⟩ := ite_ne_right_iff.1 hτ'
    exact hA σ (smul_ne_zero_right hσ) (hKsub σ i τ' hτ' h2))]
  refine Finset.sum_congr rfl fun σ hσ ↦ ?_
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ by rw [hinner σ hσ i]

/-- The composite of the transforms by admissible kernels `k` and `k₂` is the transform by the
kernel `(σ, ω) ↦ ∑_τ k σ τ * k₂ τ ω`. -/
lemma kernelFun_kernelFun {X'' U'' : Type*} [TopologicalSpace X''] {car'' : U'' → Set X''}
    {ι₂ : X'' → X'} {k₂ : T → U'' → ℤ} (hk : IsAdmissibleKernel ι car car' k)
    (hk₂ : IsAdmissibleKernel ι₂ car' car'' k₂) {c : S → M}
    (hc : IsLocallyFiniteSet car (Function.support c)) :
    kernelFun k₂ (kernelFun k c) = kernelFun (fun σ ω ↦ ∑ᶠ τ, k σ τ * k₂ τ ω) c := by
  classical
  funext ω
  set K' := ι₂ '' car'' ω
  have hK' : IsCompact K' := (hk₂.compact_nonempty ω).1.image hk₂.continuous
  have hK'ne : K'.Nonempty := (hk₂.compact_nonempty ω).2.image ι₂
  set K := ι '' K'
  have hK : IsCompact K := hK'.image hk.continuous
  let A := (hc.finite_inter_compact hK).toFinset
  let B := A.biUnion fun σ ↦ ((hk.isLocallyFiniteSet σ).finite_inter_compact hK').toFinset
  have hτK : ∀ τ, k₂ τ ω ≠ 0 → K' ⊆ car' τ := fun τ h ↦ hk₂.image_subset τ ω h
  have hσA : ∀ σ τ, c σ ≠ 0 → k σ τ ≠ 0 → k₂ τ ω ≠ 0 → σ ∈ A := fun σ τ h1 h2 h3 ↦
    (Finite.mem_toFinset _).2 ⟨h1, (hK'ne.image ι).mono (subset_inter
      ((image_mono (hτK τ h3)).trans (hk.image_subset σ τ h2)) subset_rfl)⟩
  have hτB : ∀ σ ∈ A, ∀ τ, k σ τ ≠ 0 → k₂ τ ω ≠ 0 → τ ∈ B := fun σ hσ τ h2 h3 ↦
    Finset.mem_biUnion.2 ⟨σ, hσ, (Finite.mem_toFinset _).2 ⟨h2,
      hK'ne.mono (subset_inter (hτK τ h3) subset_rfl)⟩⟩
  have hfun : ∀ τ, k₂ τ ω ≠ 0 → kernelFun k c τ = ∑ σ ∈ A, k σ τ • c σ := fun τ h3 ↦
    finsum_eq_sum_of_support_subset _ fun σ hσ ↦
      hσA σ τ (smul_ne_zero_right hσ) (smul_ne_zero_left hσ) h3
  have hL : kernelFun k₂ (kernelFun k c) ω = ∑ τ ∈ B, k₂ τ ω • ∑ σ ∈ A, k σ τ • c σ := by
    rw [kernelFun, finsum_eq_sum_of_support_subset (s := B) _ (fun τ hτ ↦ by
      have h3 := smul_ne_zero_left hτ
      have h4 := smul_ne_zero_right hτ
      rw [hfun τ h3] at h4
      obtain ⟨σ, hσ, h5⟩ := Finset.exists_ne_zero_of_sum_ne_zero h4
      exact hτB σ hσ τ (smul_ne_zero_left h5) h3)]
    refine Finset.sum_congr rfl fun τ _ ↦ ?_
    by_cases h3 : k₂ τ ω = 0
    · simp [h3]
    · rw [hfun τ h3]
  rw [hL, kernelFun, finsum_eq_sum_of_support_subset (s := A) _ (fun σ hσ ↦ by
    have h1 := smul_ne_zero_right hσ
    obtain ⟨τ, hτ⟩ : ∃ τ, k σ τ * k₂ τ ω ≠ 0 :=
      not_forall.mp fun h ↦ smul_ne_zero_left hσ (finsum_eq_zero_of_forall_eq_zero h)
    exact hσA σ τ h1 (left_ne_zero_of_mul hτ) (right_ne_zero_of_mul hτ))]
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ hσ ↦ ?_
  rw [finsum_eq_sum_of_support_subset (s := B) _ (fun τ hτ ↦
    hτB σ hσ τ (left_ne_zero_of_mul hτ) (right_ne_zero_of_mul hτ)), Finset.sum_smul]
  refine Finset.sum_congr rfl fun τ _ ↦ ?_
  rw [smul_smul, mul_comm]

end LocallyFiniteChain

namespace borelMooreHomology

open SingularChain LocallyFiniteChain

section opens

variable {Y : TopCat.{u}} (U : TopologicalSpace.Opens Y) {U' : TopologicalSpace.Opens Y}

/-- An open subset `U'` of `Y`, as an open subset of `U`: the points of `U` lying in `U'`. -/
def subOpens (U' : TopologicalSpace.Opens Y) : TopologicalSpace.Opens (TopCat.of U) :=
  ⟨Subtype.val ⁻¹' (U' : Set Y), U'.isOpen.preimage continuous_subtype_val⟩

/-- A point of `U` lies in `subOpens U U'` exactly when its image in `Y` lies in `U'`. -/
@[simp]
lemma mem_subOpens {x : TopCat.of U} : x ∈ subOpens U U' ↔ x.1 ∈ U' :=
  Iff.rfl

/-- For `U' ⊆ U`, the homeomorphism of `U'` with its preimage in `U`. -/
def subOpensHomeo (h : U' ≤ U) : U' ≃ₜ subOpens U U' where
  toFun x := ⟨⟨x.1, h x.2⟩, x.2⟩
  invFun x := ⟨x.1.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- The homeomorphism `subOpensHomeo`, as a morphism of spaces. -/
def subOpensMap (h : U' ≤ U) : TopCat.of U' ⟶ TopCat.of (subOpens U U') :=
  TopCat.ofHom ⟨subOpensHomeo U h, (subOpensHomeo U h).continuous⟩

/-- The map `subOpensMap U h` is proper. -/
lemma isProperMap_subOpensMap (h : U' ≤ U) : IsProperMap (subOpensMap U h) := by
  change IsProperMap (subOpensHomeo U h)
  exact (subOpensHomeo U h).isProperMap

/-- A singular simplex of the preimage of `U'` in `U`, as a singular simplex of `Y`. -/
def subInclSimplex {n : ℕ}
    (τ : (TopCat.toSSet.obj (TopCat.of (subOpens U U'))).obj (op ⦋n⦌)) : Simplex Y n :=
  (⟨fun x : subOpens U U' ↦ x.1.1, continuous_subtype_val.comp continuous_subtype_val⟩ :
    C(subOpens U U', Y)).comp (SingularCochain.simplexEquiv (TopCat.of (subOpens U U')) n τ)

/-- The map `subInclSimplex U` on singular `n`-simplices is injective. -/
lemma subInclSimplex_injective (n : ℕ) :
    Function.Injective (subInclSimplex U (U' := U') (n := n)) := fun τ τ' h ↦ by
  apply (SingularCochain.simplexEquiv (TopCat.of (subOpens U U')) n).injective
  ext t : 1
  exact Subtype.val_injective (Subtype.val_injective (congrArg (fun f : Simplex Y n ↦ f t) h))

/-- The image of `subInclSimplex U τ` is contained in `U'`. -/
lemma range_subInclSimplex_subset {n : ℕ}
    (τ : (TopCat.toSSet.obj (TopCat.of (subOpens U U'))).obj (op ⦋n⦌)) :
    range (subInclSimplex U τ) ⊆ U' := by
  rintro _ ⟨t, rfl⟩
  exact (SingularCochain.simplexEquiv (TopCat.of (subOpens U U')) n τ t).2

/-- The image of `subInclSimplex U τ` is the image in `Y` of the image of `τ`. -/
lemma range_subInclSimplex {n : ℕ}
    (τ : (TopCat.toSSet.obj (TopCat.of (subOpens U U'))).obj (op ⦋n⦌)) :
    range (subInclSimplex U τ) =
      (fun x : subOpens U U' ↦ x.1.1) '' singularSimplexImage (TopCat.of (subOpens U U')) τ := by
  rw [← range_simplexEquiv, ← range_comp]
  rfl

/-- For `U' ≤ U`, a singular simplex of `Y` with image in `U'` is of the form
`subInclSimplex U τ`. -/
lemma mem_range_subInclSimplex (h : U' ≤ U) {n : ℕ} {τ : Simplex Y n} (hτ : range τ ⊆ U') :
    τ ∈ range (subInclSimplex U (U' := U') (n := n)) :=
  ⟨(SingularCochain.simplexEquiv (TopCat.of (subOpens U U')) n).symm
    ⟨fun t ↦ ⟨⟨τ t, h (hτ ⟨t, rfl⟩)⟩, hτ ⟨t, rfl⟩⟩,
      (τ.continuous.subtype_mk _).subtype_mk _⟩, by
    ext t
    simp [subInclSimplex]⟩

/-- `subInclSimplex U` sends the `i`-th face of `τ` to the composite of `subInclSimplex U τ` with
the `i`-th face inclusion. -/
lemma subInclSimplex_δ {n : ℕ} (i : Fin (n + 2))
    (τ : (TopCat.toSSet.obj (TopCat.of (subOpens U U'))).obj (op ⦋n + 1⦌)) :
    subInclSimplex U ((TopCat.toSSet.obj (TopCat.of (subOpens U U'))).δ i τ) =
      (subInclSimplex U τ).comp (face n i) := by
  unfold subInclSimplex
  conv_lhs => rw [← (SingularCochain.simplexEquiv (TopCat.of (subOpens U U')) (n + 1)).symm_apply_apply τ,
    SingularCochain.simplexEquiv_symm_δ, Equiv.apply_symm_apply]
  rfl

/-- The restriction kernel of the preimage of `U'` in `U` is that of `U'` in `Y`. -/
lemma restrictKernel_subOpens {n : ℕ} (ν : (TopCat.toSSet.obj (TopCat.of U)).obj (op ⦋n⦌))
    (τ : (TopCat.toSSet.obj (TopCat.of (subOpens U U'))).obj (op ⦋n⦌)) :
    restrictKernel (subOpens U U') n ν τ =
      restrCoeff ℤ (U' : Set Y) (inclSimplex U ν) (subInclSimplex U τ) :=
  restrCoeff_val_comp (A := (U : Set Y)) (U' : Set Y) (SingularCochain.simplexEquiv (TopCat.of U) n ν)
    (inclSimplex (subOpens U U') τ)

end opens

section kernels

variable {Y : TopCat.{u}} (U : TopologicalSpace.Opens Y) {U' : TopologicalSpace.Opens Y}

/-- For an injective `f` whose range contains the support of `g`,
`∑ᶠ a, g (f a) = ∑ᶠ b, g b`. -/
lemma finsum_comp_eq_of_support_subset_range {α β N : Type*} [AddCommMonoid N] {f : α → β}
    (hf : Function.Injective f) {g : β → N} (hg : Function.support g ⊆ range f) :
    ∑ᶠ a, g (f a) = ∑ᶠ b, g b := by
  rw [← finsum_mem_range hf, finsum_mem_def, Set.indicator_eq_self.2 hg]

/-- The inverse of `subOpensMap`. -/
def subOpensInv (h : U' ≤ U) : TopCat.of (subOpens U U') ⟶ TopCat.of U' :=
  TopCat.ofHom ⟨(subOpensHomeo U h).symm, (subOpensHomeo U h).symm.continuous⟩

/-- On singular simplices, `subOpensInv U h` followed by `subOpensMap U h` is the identity. -/
lemma subOpensMap_subOpensInv_app (h : U' ≤ U) {n : ℕ}
    (τ : (TopCat.toSSet.obj (TopCat.of (subOpens U U'))).obj (op ⦋n⦌)) :
    (TopCat.toSSet.map (subOpensMap U h)).app _ ((TopCat.toSSet.map (subOpensInv U h)).app _ τ) =
      τ := by
  apply (SingularCochain.simplexEquiv (TopCat.of (subOpens U U')) n).injective
  rw [toSSetObjEquiv_map, toSSetObjEquiv_map]
  rfl

/-- On singular simplices, `subOpensMap U h` followed by `subOpensInv U h` is the identity. -/
lemma subOpensInv_subOpensMap_app (h : U' ≤ U) {n : ℕ}
    (τ : (TopCat.toSSet.obj (TopCat.of U')).obj (op ⦋n⦌)) :
    (TopCat.toSSet.map (subOpensInv U h)).app _ ((TopCat.toSSet.map (subOpensMap U h)).app _ τ) =
      τ := by
  apply (SingularCochain.simplexEquiv (TopCat.of U') n).injective
  rw [toSSetObjEquiv_map, toSSetObjEquiv_map]
  rfl

/-- Transporting a simplex `τ` of `subOpens U U'` to `U'` along `subOpensInv U h` and including
it into `Y` gives `subInclSimplex U τ`. -/
lemma inclSimplex_subOpensInv (h : U' ≤ U) {n : ℕ}
    (τ : (TopCat.toSSet.obj (TopCat.of (subOpens U U'))).obj (op ⦋n⦌)) :
    inclSimplex U' ((TopCat.toSSet.map (subOpensInv U h)).app _ τ) = subInclSimplex U τ :=
  rfl

/-- The kernel of the homotopy between the two restrictions: the coefficient of `ω` in
`h σ = ∑_i (T X_i σ)|_{U'}`. -/
def homKernel (n : ℕ) (σ : (TopCat.toSSet.obj Y).obj (op ⦋n⦌))
    (ω : (TopCat.toSSet.obj (TopCat.of (subOpens U U'))).obj (op ⦋n + 1⦌)) : ℤ :=
  homCoeff ℤ (U : Set Y) (U' : Set Y) (SingularCochain.simplexEquiv Y n σ) (subInclSimplex U ω)

/-- The kernel of the iterated restriction `σ ↦ (σ|_U)|_{U'}`. -/
def compKernel (n : ℕ) (σ : (TopCat.toSSet.obj Y).obj (op ⦋n⦌))
    (τ : (TopCat.toSSet.obj (TopCat.of (subOpens U U'))).obj (op ⦋n⦌)) : ℤ :=
  ∑ᶠ ν, restrictKernel U n σ ν * restrictKernel (subOpens U U') n ν τ

/-- `compKernel U n σ τ` is the coefficient `compCoeff` of `subInclSimplex U τ` in the
restriction of `σ` to `U` and then to `U'`. -/
lemma compKernel_eq (n : ℕ) (σ : (TopCat.toSSet.obj Y).obj (op ⦋n⦌))
    (τ : (TopCat.toSSet.obj (TopCat.of (subOpens U U'))).obj (op ⦋n⦌)) :
    compKernel U n σ τ =
      compCoeff ℤ (U : Set Y) (U' : Set Y) (SingularCochain.simplexEquiv Y n σ) (subInclSimplex U τ) := by
  rw [compKernel, compCoeff]
  simp_rw [restrictKernel_subOpens]
  refine finsum_comp_eq_of_support_subset_range (inclSimplex_injective U n)
    (g := fun ν ↦ restrCoeff ℤ (U : Set Y) (SingularCochain.simplexEquiv Y n σ) ν *
      restrCoeff ℤ (U' : Set Y) ν (subInclSimplex U τ)) fun ν hν ↦ ?_
  have h1 : restrCoeff ℤ (U : Set Y) (SingularCochain.simplexEquiv Y n σ) ν ≠ 0 := fun h0 ↦
    hν (by simp only [h0, zero_mul])
  exact mem_range_inclSimplex U ((range_subset_of_restrCoeff_ne_zero h1).trans inter_subset_right)

variable [T2Space Y]

/-- For `U' ≤ U`, `homKernel U n` is an admissible kernel from the singular `n`-simplices of `Y`
to the singular `(n + 1)`-simplices of `subOpens U U'`. -/
lemma isAdmissibleKernel_homKernel (h : U' ≤ U) (n : ℕ) :
    IsAdmissibleKernel (fun x : subOpens U U' ↦ x.1.1) (singularSimplexImage Y (n := op ⦋n⦌))
      (singularSimplexImage (TopCat.of (subOpens U U')) (n := op ⦋n + 1⦌)) (homKernel U n) where
  continuous := continuous_subtype_val.comp continuous_subtype_val
  image_subset σ ω hk := by
    rw [← range_subInclSimplex]
    exact ((range_subset_of_homCoeff_ne_zero hk).trans inter_subset_left).trans
      (range_simplexEquiv σ).subset
  isLocallyFiniteSet σ x := by
    obtain ⟨W, hW, hxW, hfin⟩ := exists_finite_homCoeff_ne_zero (R := ℤ) U.isOpen U'.isOpen h
      (SingularCochain.simplexEquiv Y n σ) x.2
    refine ⟨(fun x : subOpens U U' ↦ x.1.1) ⁻¹' W,
      (hW.preimage (continuous_subtype_val.comp continuous_subtype_val)).mem_nhds hxW,
      (hfin.preimage (subInclSimplex_injective U (n + 1)).injOn).subset ?_⟩
    rintro ω ⟨hω, y, hy, hyW⟩
    refine ⟨hω, y.1.1, ?_, hyW⟩
    rw [range_subInclSimplex]
    exact ⟨y, hy, rfl⟩
  compact_nonempty τ := ⟨isCompact_singularSimplexImage τ, nonempty_singularSimplexImage τ⟩

open Classical in
/-- Pulling the coboundary of `homKernel` back along `subInclSimplex` turns it into a finite sum
of `homCoeff` over the simplices of `Y`. -/
lemma finsum_homKernel_eq_finsum_homCoeff {n : ℕ} (i : Fin (n + 2))
    (σ : (TopCat.toSSet.obj Y).obj (op ⦋n⦌))
    (τ : (TopCat.toSSet.obj (TopCat.of (subOpens U U'))).obj (op ⦋n⦌)) (h : U' ≤ U) :
    ∑ᶠ ω, (if (TopCat.toSSet.obj (TopCat.of (subOpens U U'))).δ i ω = τ then
      homKernel U n σ ω else 0) =
    ∑ᶠ ω : Simplex Y (n + 1), (if ω.comp (face n i) = subInclSimplex U τ then
      homCoeff ℤ (U : Set Y) (U' : Set Y) (SingularCochain.simplexEquiv Y n σ) ω else 0) := by
  have hiff : ∀ ω, (TopCat.toSSet.obj (TopCat.of (subOpens U U'))).δ i ω = τ ↔
      (subInclSimplex U ω).comp (face n i) = subInclSimplex U τ := fun ω ↦ by
    rw [← subInclSimplex_δ]
    exact (subInclSimplex_injective U _).eq_iff.symm
  set G : Simplex Y (n + 1) → ℤ := fun ω' ↦ if ω'.comp (face n i) = subInclSimplex U τ then
    homCoeff ℤ (U : Set Y) (U' : Set Y) (SingularCochain.simplexEquiv Y n σ) ω' else 0 with hG
  have hterm : ∀ ω, (if (TopCat.toSSet.obj (TopCat.of (subOpens U U'))).δ i ω = τ then
      homKernel U n σ ω else 0) = G (subInclSimplex U ω) := fun ω ↦ by
    rw [hG]
    beta_reduce
    by_cases hω : (TopCat.toSSet.obj (TopCat.of (subOpens U U'))).δ i ω = τ
    · rw [if_pos hω, if_pos ((hiff ω).1 hω)]
      rfl
    · rw [if_neg hω, if_neg fun h' ↦ hω ((hiff ω).2 h')]
  rw [finsum_congr hterm]
  refine finsum_comp_eq_of_support_subset_range (g := G) (subInclSimplex_injective U _)
    fun ω hω ↦ ?_
  rw [Function.mem_support, hG] at hω
  exact mem_range_subInclSimplex U h
    ((range_subset_of_homCoeff_ne_zero (ite_ne_right_iff.1 hω).2).trans inter_subset_right)

open Classical in
/-- The homotopy identity for kernels, degree `n + 1`. -/
lemma restrictKernel_eq_succ (h : U' ≤ U) {n : ℕ} (σ : (TopCat.toSSet.obj Y).obj (op ⦋n + 1⦌))
    (τ : (TopCat.toSSet.obj (TopCat.of (subOpens U U'))).obj (op ⦋n + 1⦌)) :
    restrictKernel U' (n + 1) σ ((TopCat.toSSet.map (subOpensInv U h)).app _ τ) =
      compKernel U (n + 1) σ τ +
      ∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) * ∑ᶠ ω,
        (if (TopCat.toSSet.obj (TopCat.of (subOpens U U'))).δ i ω = τ then
          homKernel U (n + 1) σ ω else 0) +
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) * homKernel U n ((TopCat.toSSet.obj Y).δ i σ) τ := by
  have key := restrCoeff_sub_compCoeff_succ (R := ℤ) U.isOpen U'.isOpen h
    (SingularCochain.simplexEquiv Y (n + 1) σ) (subInclSimplex U τ) (range_subInclSimplex_subset U τ)
  simp_rw [finsum_homKernel_eq_finsum_homCoeff (n := n + 1) U _ σ τ h]
  rw [restrictKernel, inclSimplex_subOpensInv, compKernel_eq]
  have e : ∀ i : Fin (n + 2), homKernel U n ((TopCat.toSSet.obj Y).δ i σ) τ =
      homCoeff ℤ (U : Set Y) (U' : Set Y) ((SingularCochain.simplexEquiv Y (n + 1) σ).comp (face n i))
        (subInclSimplex U τ) := fun i ↦ by
    rw [homKernel, toSSetObjEquiv_δ]
  simp_rw [e]
  linear_combination key

open Classical in
/-- The homotopy identity for kernels, degree `0`. -/
lemma restrictKernel_eq_zero (h : U' ≤ U) (σ : (TopCat.toSSet.obj Y).obj (op ⦋0⦌))
    (τ : (TopCat.toSSet.obj (TopCat.of (subOpens U U'))).obj (op ⦋0⦌)) :
    restrictKernel U' 0 σ ((TopCat.toSSet.map (subOpensInv U h)).app _ τ) =
      compKernel U 0 σ τ +
      ∑ i : Fin (0 + 2), (-1 : ℤ) ^ (i : ℕ) * ∑ᶠ ω,
        (if (TopCat.toSSet.obj (TopCat.of (subOpens U U'))).δ i ω = τ then
          homKernel U 0 σ ω else 0) := by
  have key := restrCoeff_sub_compCoeff_zero (R := ℤ) U.isOpen U'.isOpen h
    (SingularCochain.simplexEquiv Y 0 σ) (subInclSimplex U τ) (range_subInclSimplex_subset U τ)
  simp_rw [finsum_homKernel_eq_finsum_homCoeff (n := 0) U _ σ τ h]
  rw [restrictKernel, inclSimplex_subOpensInv, compKernel_eq]
  linear_combination key

end kernels

section complex

variable (R : Type u) [CommRing R] (M : ModuleCat.{u} R) {Y : TopCat.{u}} [T2Space Y]
  (U : TopologicalSpace.Opens Y) {U' : TopologicalSpace.Opens Y} (h : U' ≤ U)

/-- The homotopy `h` between the two restrictions, on locally finite chains of degree `n`. -/
def homotopyMap (n : ℕ) : (borelMooreChainComplex R M Y).X n ⟶
    (borelMooreChainComplex R M (TopCat.of (subOpens U U'))).X (n + 1) :=
  ModuleCat.ofHom (kernelMap R (isAdmissibleKernel_homKernel U h n))

/-- The iterated restriction `c ↦ (c|_U)|_{U'}` of locally finite chains. -/
abbrev iteratedRestrictChainMap :
    borelMooreChainComplex R M Y ⟶ borelMooreChainComplex R M (TopCat.of (subOpens U U')) :=
  restrictChainMap R M U ≫ restrictChainMap R M (subOpens U U')

/-- The restriction `c ↦ c|_{U'}` of locally finite chains, read in the preimage of `U'` in
`U`. -/
abbrev directRestrictChainMap :
    borelMooreChainComplex R M Y ⟶ borelMooreChainComplex R M (TopCat.of (subOpens U U')) :=
  restrictChainMap R M U' ≫ chainMap R M (subOpensMap U h) (isProperMap_subOpensMap U h)

/-- In degree `n`, `iteratedRestrictChainMap` is the kernel map of `compKernel U n`. -/
lemma iteratedRestrictChainMap_apply (n : ℕ) (c : (borelMooreChainComplex R M Y).X n) :
    (((iteratedRestrictChainMap R M U (U' := U')).f n).hom c).1 =
      kernelFun (compKernel U n) c.1 := by
  change kernelFun (restrictKernel (subOpens U U') n) (kernelFun (restrictKernel U n) c.1) = _
  rw [kernelFun_kernelFun (isAdmissibleKernel_restrictKernel U n)
    (isAdmissibleKernel_restrictKernel (subOpens U U') n) c.2]
  rfl

/-- In degree `n`, `directRestrictChainMap` is the kernel map of `restrictKernel U' n`, evaluated
at the transport of `τ` along `subOpensInv U h`. -/
lemma directRestrictChainMap_apply (n : ℕ) (c : (borelMooreChainComplex R M Y).X n) :
    (((directRestrictChainMap R M U h).f n).hom c).1 =
      kernelFun (fun σ τ ↦ restrictKernel U' n σ ((TopCat.toSSet.map (subOpensInv U h)).app _ τ))
        c.1 := by
  change pushforwardFun ((TopCat.toSSet.map (subOpensMap U h)).app _)
    (kernelFun (restrictKernel U' n) c.1) = _
  rw [pushforwardFun_eq_comp (subOpensInv_subOpensMap_app U h) (subOpensMap_subOpensInv_app U h)]
  rfl

/-- The boundary followed by `homotopyMap` is the kernel map of the alternating sum of
`homKernel U k` over the faces of `σ`. -/
lemma d_homotopyMap_apply (k : ℕ) (c : (borelMooreChainComplex R M Y).X (k + 1)) :
    (((borelMooreChainComplex R M Y).d (k + 1) k ≫ homotopyMap R M U h k).hom c).1 =
      kernelFun (fun σ τ ↦ ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) *
        homKernel U k ((TopCat.toSSet.obj Y).δ i σ) τ) c.1 := by
  change kernelFun (homKernel U k) (((borelMooreChainComplex R M Y).d (k + 1) k).hom c).1 = _
  rw [borelMooreChainComplex_d_apply]
  exact kernelFun_dFun_eq (isAdmissibleKernel_homKernel U h k)
    (fun i : Fin (k + 2) ↦ (TopCat.toSSet.obj Y).δ i)
    (fun i σ ↦ singularSimplexImage_map_subset _ σ) c.2

open Classical in
/-- `homotopyMap` followed by the boundary is the kernel map whose coefficient at `(σ, τ)` is the
alternating sum over `i` of the coefficients of `homKernel U k σ` at the simplices whose `i`-th
face is `τ`. -/
lemma homotopyMap_d_apply (k : ℕ) (c : (borelMooreChainComplex R M Y).X k) :
    ((homotopyMap R M U h k ≫
      (borelMooreChainComplex R M (TopCat.of (subOpens U U'))).d (k + 1) k).hom c).1 =
      kernelFun (fun σ τ ↦ ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) * ∑ᶠ ω,
        (if (TopCat.toSSet.obj (TopCat.of (subOpens U U'))).δ i ω = τ then
          homKernel U k σ ω else 0)) c.1 := by
  change (((borelMooreChainComplex R M (TopCat.of (subOpens U U'))).d (k + 1) k).hom
    (homotopyMap R M U h k c)).1 = _
  rw [borelMooreChainComplex_d_apply]
  change dFun _ (kernelFun (homKernel U k) c.1) = _
  exact dFun_kernelFun_eq (isAdmissibleKernel_homKernel U h k)
    (fun i : Fin (k + 2) ↦ (TopCat.toSSet.obj (TopCat.of (subOpens U U'))).δ i)
    (fun i τ ↦ singularSimplexImage_map_subset _ τ)
    (fun τ ↦ ⟨isCompact_singularSimplexImage τ, nonempty_singularSimplexImage τ⟩) c.2

end complex

section support

variable {Y : TopCat.{u}} [T2Space Y] (U : TopologicalSpace.Opens Y)
  {U' : TopologicalSpace.Opens Y} (h : U' ≤ U)

/-- If `restrictKernel U' n σ` is nonzero at the transport of `τ` along `subOpensInv U h`, then
the image of `subInclSimplex U τ` lies in the image of `σ`. -/
lemma range_subset_of_restrictKernel_subOpensInv_ne_zero {n : ℕ}
    {σ : (TopCat.toSSet.obj Y).obj (op ⦋n⦌)}
    {τ : (TopCat.toSSet.obj (TopCat.of (subOpens U U'))).obj (op ⦋n⦌)}
    (hk : restrictKernel U' n σ ((TopCat.toSSet.map (subOpensInv U h)).app _ τ) ≠ 0) :
    range (subInclSimplex U τ) ⊆ singularSimplexImage Y σ := by
  rw [← inclSimplex_subOpensInv U h, range_inclSimplex]
  exact (isAdmissibleKernel_restrictKernel U' n).image_subset σ _ hk

/-- If `compKernel U n σ τ ≠ 0`, the image of `subInclSimplex U τ` lies in the image of `σ`. -/
lemma range_subset_of_compKernel_ne_zero {n : ℕ} {σ : (TopCat.toSSet.obj Y).obj (op ⦋n⦌)}
    {τ : (TopCat.toSSet.obj (TopCat.of (subOpens U U'))).obj (op ⦋n⦌)}
    (hk : compKernel U n σ τ ≠ 0) : range (subInclSimplex U τ) ⊆ singularSimplexImage Y σ := by
  rw [compKernel_eq, compCoeff] at hk
  obtain ⟨ν, hν⟩ : ∃ ν, restrCoeff ℤ (U : Set Y) (SingularCochain.simplexEquiv Y n σ) ν *
      restrCoeff ℤ (U' : Set Y) ν (subInclSimplex U τ) ≠ 0 :=
    not_forall.mp fun h' ↦ hk (finsum_eq_zero_of_forall_eq_zero h')
  exact ((range_subset_of_restrCoeff_ne_zero (right_ne_zero_of_mul hν)).trans
    inter_subset_left).trans (((range_subset_of_restrCoeff_ne_zero (left_ne_zero_of_mul hν)).trans
    inter_subset_left).trans (range_simplexEquiv σ).subset)

/-- If the alternating sum of `homKernel U k` over the faces of `σ` is nonzero at `τ`, the image
of `subInclSimplex U τ` lies in the image of `σ`. -/
lemma range_subset_of_sum_homKernel_ne_zero {k : ℕ} {σ : (TopCat.toSSet.obj Y).obj (op ⦋k + 1⦌)}
    {τ : (TopCat.toSSet.obj (TopCat.of (subOpens U U'))).obj (op ⦋k + 1⦌)}
    (hk : ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) *
      homKernel U k ((TopCat.toSSet.obj Y).δ i σ) τ ≠ 0) :
    range (subInclSimplex U τ) ⊆ singularSimplexImage Y σ := by
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk
  have hi' : homKernel U k ((TopCat.toSSet.obj Y).δ i σ) τ ≠ 0 := fun h0 ↦
    hi (by rw [h0, mul_zero])
  exact (((range_subset_of_homCoeff_ne_zero hi').trans inter_subset_left).trans
    (range_simplexEquiv _).subset).trans (singularSimplexImage_map_subset _ σ)

open Classical in
/-- If the coefficient at `(σ, τ)` of `homotopyMap` followed by the boundary is nonzero, the
image of `subInclSimplex U τ` lies in the image of `σ`. -/
lemma range_subset_of_sum_finsum_homKernel_ne_zero {k : ℕ}
    {σ : (TopCat.toSSet.obj Y).obj (op ⦋k⦌)}
    {τ : (TopCat.toSSet.obj (TopCat.of (subOpens U U'))).obj (op ⦋k⦌)}
    (hk : ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) * ∑ᶠ ω,
      (if (TopCat.toSSet.obj (TopCat.of (subOpens U U'))).δ i ω = τ then
        homKernel U k σ ω else 0) ≠ 0) :
    range (subInclSimplex U τ) ⊆ singularSimplexImage Y σ := by
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk
  have hi' : ∑ᶠ ω, (if (TopCat.toSSet.obj (TopCat.of (subOpens U U'))).δ i ω = τ then
      homKernel U k σ ω else 0) ≠ 0 := fun h0 ↦ hi (by rw [h0, mul_zero])
  obtain ⟨ω, hω⟩ : ∃ ω, (if (TopCat.toSSet.obj (TopCat.of (subOpens U U'))).δ i ω = τ then
      homKernel U k σ ω else 0) ≠ 0 :=
    not_forall.mp fun h' ↦ hi' (finsum_eq_zero_of_forall_eq_zero h')
  obtain ⟨he, hω⟩ := ite_ne_right_iff.1 hω
  rw [← he, subInclSimplex_δ]
  rintro _ ⟨t, rfl⟩
  exact (range_simplexEquiv σ).subset
    (((range_subset_of_homCoeff_ne_zero hω).trans inter_subset_left) ⟨_, rfl⟩)

end support

section homotopy

variable (R : Type u) [CommRing R] (M : ModuleCat.{u} R) {Y : TopCat.{u}} [T2Space Y]
  (U : TopologicalSpace.Opens Y) {U' : TopologicalSpace.Opens Y} (h : U' ≤ U)

/-- In degree `k + 1`, the direct minus the iterated restriction is
`d ≫ homotopyMap + homotopyMap ≫ d`. -/
lemma directRestrictChainMap_sub_succ (k : ℕ) :
    (directRestrictChainMap R M U h).f (k + 1) - (iteratedRestrictChainMap R M U).f (k + 1) =
      (borelMooreChainComplex R M Y).d (k + 1) k ≫ homotopyMap R M U h k +
        homotopyMap R M U h (k + 1) ≫
          (borelMooreChainComplex R M (TopCat.of (subOpens U U'))).d (k + 1 + 1) (k + 1) := by
  ext c : 2
  apply Subtype.ext
  funext τ
  have e₁ := congrFun (directRestrictChainMap_apply R M U h (k + 1) c) τ
  have e₂ := congrFun (iteratedRestrictChainMap_apply R M U (U' := U') (k + 1) c) τ
  have e₃ := congrFun (d_homotopyMap_apply R M U h k c) τ
  have e₄ := congrFun (homotopyMap_d_apply R M U h (k + 1) c) τ
  change (((directRestrictChainMap R M U h).f (k + 1)).hom c).1 τ -
      (((iteratedRestrictChainMap R M U).f (k + 1)).hom c).1 τ =
    ((((borelMooreChainComplex R M Y).d (k + 1) k ≫ homotopyMap R M U h k).hom c).1 τ +
      ((homotopyMap R M U h (k + 1) ≫
        (borelMooreChainComplex R M (TopCat.of (subOpens U U'))).d (k + 1 + 1) (k + 1)).hom c).1 τ)
  rw [e₁, e₂, e₃, e₄]
  have hK := isCompact_range (subInclSimplex U τ).continuous
  have hne := fun {s : Set Y} (hs : range (subInclSimplex U τ) ⊆ s) ↦
    ((range_nonempty _).mono (subset_inter hs subset_rfl) :
      (s ∩ range (subInclSimplex U τ)).Nonempty)
  rw [kernelFun_eq_sum_of_inter_nonempty _ c.2 hK τ
      (fun σ hσ ↦ hne (range_subset_of_restrictKernel_subOpensInv_ne_zero U h hσ)),
    kernelFun_eq_sum_of_inter_nonempty _ c.2 hK τ
      (fun σ hσ ↦ hne (range_subset_of_compKernel_ne_zero U hσ)),
    kernelFun_eq_sum_of_inter_nonempty _ c.2 hK τ
      (fun σ hσ ↦ hne (range_subset_of_sum_homKernel_ne_zero U hσ)),
    kernelFun_eq_sum_of_inter_nonempty _ c.2 hK τ
      (fun σ hσ ↦ hne (range_subset_of_sum_finsum_homKernel_ne_zero U hσ)),
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [← sub_smul, ← add_smul, restrictKernel_eq_succ U h σ τ]
  congr 1
  ring

/-- In degree `0`, the direct minus the iterated restriction is `homotopyMap ≫ d`. -/
lemma directRestrictChainMap_sub_zero :
    (directRestrictChainMap R M U h).f 0 - (iteratedRestrictChainMap R M U).f 0 =
      homotopyMap R M U h 0 ≫
        (borelMooreChainComplex R M (TopCat.of (subOpens U U'))).d (0 + 1) 0 := by
  ext c : 2
  apply Subtype.ext
  funext τ
  have e₁ := congrFun (directRestrictChainMap_apply R M U h 0 c) τ
  have e₂ := congrFun (iteratedRestrictChainMap_apply R M U (U' := U') 0 c) τ
  have e₄ := congrFun (homotopyMap_d_apply R M U h 0 c) τ
  change (((directRestrictChainMap R M U h).f 0).hom c).1 τ -
      (((iteratedRestrictChainMap R M U).f 0).hom c).1 τ =
    ((homotopyMap R M U h 0 ≫
        (borelMooreChainComplex R M (TopCat.of (subOpens U U'))).d (0 + 1) 0).hom c).1 τ
  rw [e₁, e₂, e₄]
  have hK := isCompact_range (subInclSimplex U τ).continuous
  have hne := fun {s : Set Y} (hs : range (subInclSimplex U τ) ⊆ s) ↦
    ((range_nonempty _).mono (subset_inter hs subset_rfl) :
      (s ∩ range (subInclSimplex U τ)).Nonempty)
  rw [kernelFun_eq_sum_of_inter_nonempty _ c.2 hK τ
      (fun σ hσ ↦ hne (range_subset_of_restrictKernel_subOpensInv_ne_zero U h hσ)),
    kernelFun_eq_sum_of_inter_nonempty _ c.2 hK τ
      (fun σ hσ ↦ hne (range_subset_of_compKernel_ne_zero U hσ)),
    kernelFun_eq_sum_of_inter_nonempty _ c.2 hK τ
      (fun σ hσ ↦ hne (range_subset_of_sum_finsum_homKernel_ne_zero U hσ)),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [← sub_smul, restrictKernel_eq_zero U h σ τ]
  congr 1
  ring

/-- The components of the homotopy, indexed as Mathlib's null-homotopic maps require. -/
def homotopyHom (i j : ℕ) (r : (ComplexShape.down ℕ).Rel j i) :
    (borelMooreChainComplex R M Y).X i ⟶
      (borelMooreChainComplex R M (TopCat.of (subOpens U U'))).X j :=
  homotopyMap R M U h i ≫ ((borelMooreChainComplex R M _).XIsoOfEq r).hom

/-- The direct minus the iterated restriction is the null-homotopic map given by
`homotopyHom`. -/
lemma directRestrictChainMap_sub :
    directRestrictChainMap R M U h - iteratedRestrictChainMap R M U =
      Homotopy.nullHomotopicMap' (homotopyHom R M U h) := by
  ext1 n
  rw [HomologicalComplex.sub_f_apply]
  rcases n with _ | k
  · rw [Homotopy.nullHomotopicMap'_f_of_not_rel_left (k₁ := 0 + 1) (k₀ := 0) rfl
      (fun l hl ↦ by simp at hl), directRestrictChainMap_sub_zero]
    simp only [homotopyHom, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id]
  · rw [Homotopy.nullHomotopicMap'_f (k₂ := k + 1 + 1) (k₁ := k + 1) (k₀ := k) rfl rfl,
      directRestrictChainMap_sub_succ]
    simp only [homotopyHom, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id]

/-- The chain homotopy between the direct and the iterated restriction of locally finite chains
(Borel–Moore, §3). -/
def restrictHomotopy :
    Homotopy (directRestrictChainMap R M U h) (iteratedRestrictChainMap R M U) :=
  Homotopy.equivSubZero.symm ((Homotopy.ofEq (directRestrictChainMap_sub R M U h)).trans
    (Homotopy.nullHomotopy' (homotopyHom R M U h)))

/-- **Functoriality of restriction** (Fulton, §19.1, (5)): for open subsets `U' ⊆ U ⊆ Y` of a
Hausdorff space, restricting to `U` and then to `U'` (read in `U`) is restricting to `U'`,
transported along the homeomorphism of `U'` with its preimage in `U`. -/
theorem restrict_comp_restrict (j : ℤ) :
    restrict R M U j ≫ restrict R M (subOpens U U') j =
      restrict R M U' j ≫ pushforward R M (subOpensMap U h) (isProperMap_subOpensMap U h) j := by
  have h₁ := HomologicalComplex.homologyMap_comp
    (HomologicalComplex.extendMap (restrictChainMap R M U) ComplexShape.embeddingDownNat)
    (HomologicalComplex.extendMap (restrictChainMap R M (subOpens U U'))
      ComplexShape.embeddingDownNat) (-j)
  have h₂ := HomologicalComplex.homologyMap_comp
    (HomologicalComplex.extendMap (restrictChainMap R M U') ComplexShape.embeddingDownNat)
    (HomologicalComplex.extendMap (chainMap R M (subOpensMap U h) (isProperMap_subOpensMap U h))
      ComplexShape.embeddingDownNat) (-j)
  rw [← HomologicalComplex.extendMap_comp] at h₁ h₂
  refine h₁.symm.trans (Eq.trans ?_ h₂)
  exact (((restrictHomotopy R M U h).extend ComplexShape.embeddingDownNat).homologyMap_eq
    (-j)).symm

/-- **Functoriality of restriction** (Fulton, §19.1, (5)): `(a|_U)|_{U'} = a|_{U'}` for open
subsets `U' ⊆ U ⊆ Y` of a Hausdorff space and `a ∈ H_j Y`, where `U'` is read in `U` as its
preimage, identified with `U'` by `subOpensHomeo`. The other half of Fulton's (5),
`H_j ∅ = 0`, is `MMP.isZero_borelMooreHomology_of_isEmpty`. -/
theorem restrict_restrict_apply (j : ℤ) (a : borelMooreHomology R M Y j) :
    restrict R M (subOpens U U') j (restrict R M U j a) =
      pushforward R M (subOpensMap U h) (isProperMap_subOpensMap U h) j
        (restrict R M U' j a) :=
  congrArg (fun φ ↦ φ.hom a) (restrict_comp_restrict R M U h j)

end homotopy

end borelMooreHomology

end MMP
