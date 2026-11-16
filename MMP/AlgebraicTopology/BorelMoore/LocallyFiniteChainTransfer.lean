module

public import MMP.AlgebraicTopology.BorelMoore.Basic

/-!
# Transfer of locally finite chains along families of finite chains

Let `I` and `T` be types of "simplices" with carriers `carI : I → Set X` and `carT : T → Set X`,
the carriers of `T` compact and nonempty. A family `Ψ : I → (T →₀ ℤ)` of finite chains is
*carrier-decreasing* if every simplex `t` occurring in `Ψ i` has `carT t ⊆ carI i`. Such a family
sends a locally finite chain `c` on `I` to the locally finite chain `∑ i, c i • Ψ i` on `T`: near a
point only finitely many `i` with `c i ≠ 0` matter, and a given `t` occurs in only finitely many
`Ψ i`. This generalises the push-forward along a carrier-decreasing map `f : I → T`, the case
`Ψ i = single (f i) 1`.

The transfer is compatible with push-forward on both sides and is additive in `Ψ`. For the
product `X × Y` of two spaces, the *tensor* `c ⊗ d : (σ, τ) ↦ c σ * d τ` of locally finite chains
on `X` and `Y` is locally finite for the product carriers `carX σ ×ˢ carY τ`.

## Main definitions

* `MMP.LocallyFiniteChain.IsCarrierDecreasing`: every simplex in `Ψ i` has carrier inside that
  of `i`.
* `MMP.LocallyFiniteChain.lfTransferFun`: `t ↦ ∑ᶠ i, c i * Ψ i t`.
* `MMP.LocallyFiniteChain.prodCarrier`: the product carriers `carX σ ×ˢ carY τ`.
* `MMP.LocallyFiniteChain.lfTensor`: `(σ, τ) ↦ c σ * d τ`.

## Main results

* `MMP.LocallyFiniteChain.lfTransferFun_mem`: the transfer is locally finite.
* `MMP.LocallyFiniteChain.pushforwardFun_lfTransferFun`,
  `MMP.LocallyFiniteChain.lfTransferFun_pushforwardFun`: compatibility with
  push-forward.
* `MMP.LocallyFiniteChain.lfTensor_mem`: the tensor is locally finite.
-/

@[expose] public noncomputable section

namespace MMP

namespace LocallyFiniteChain

open Classical

section Transfer

variable {X : Type*} [TopologicalSpace X] {I I' T T' : Type*}
  {carI : I → Set X} {carI' : I' → Set X} {carT : T → Set X} {carT' : T' → Set X}
  {R : Type*} [CommRing R]

/-- A family of finite chains is *carrier-decreasing* if every simplex occurring in `Ψ i` has
carrier contained in that of `i`. -/
def IsCarrierDecreasing (carI : I → Set X) (carT : T → Set X) (Ψ : I → T →₀ ℤ) : Prop :=
  ∀ i t, Ψ i t ≠ 0 → carT t ⊆ carI i

/-- The coefficient function of the transfer of `c` along `Ψ`. -/
def lfTransferFun (Ψ : I → T →₀ ℤ) (c : I → R) : T → R :=
  fun t ↦ ∑ᶠ i, c i * (Ψ i t : R)

/-- The coefficient of `t` in the transfer of `c` along `Ψ`. -/
lemma lfTransferFun_apply (Ψ : I → T →₀ ℤ) (c : I → R) (t : T) :
    lfTransferFun Ψ c t = ∑ᶠ i, c i * (Ψ i t : R) := rfl

/-- A nonzero coefficient of the transfer comes from some `i` with `c i ≠ 0` and `Ψ i t ≠ 0`. -/
lemma exists_ne_zero_of_lfTransferFun_ne_zero {Ψ : I → T →₀ ℤ} {c : I → R} {t : T}
    (ht : lfTransferFun Ψ c t ≠ 0) : ∃ i, c i ≠ 0 ∧ Ψ i t ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, c i * (Ψ i t : R) ≠ 0 :=
    not_forall.1 (mt finsum_eq_zero_of_forall_eq_zero ht)
  exact ⟨i, fun h ↦ hi (by simp [h]), fun h ↦ hi (by simp [h])⟩

/-- For a locally finite chain `c` and a carrier-decreasing family `Ψ`, only finitely many `i`
with `c i ≠ 0` have `t` occurring in `Ψ i`, when the carrier of `t` is compact and nonempty. -/
lemma finite_setOf_ne_zero_and_ne_zero {c : I → R} (hc : c ∈ lfChains R R carI)
    {Ψ : I → T →₀ ℤ} (hΨ : IsCarrierDecreasing carI carT Ψ) (t : T)
    (ht : IsCompact (carT t) ∧ (carT t).Nonempty) : {i | c i ≠ 0 ∧ Ψ i t ≠ 0}.Finite := by
  refine (hc.finite_inter_compact ht.1).subset ?_
  rintro i ⟨hi, hit⟩
  obtain ⟨x, hx⟩ := ht.2
  exact ⟨hi, x, hΨ i t hit hx, hx⟩

/-- The coefficient of `t` in the transfer is the finite sum `∑ i ∈ F, c i * Ψ i t` over any
finset `F` containing every `i` with `c i ≠ 0` and `Ψ i t ≠ 0`. -/
lemma lfTransferFun_eq_sum (Ψ : I → T →₀ ℤ) (c : I → R) (t : T) (F : Finset I)
    (hF : ∀ i, c i ≠ 0 → Ψ i t ≠ 0 → i ∈ F) :
    lfTransferFun Ψ c t = ∑ i ∈ F, c i * (Ψ i t : R) := by
  refine finsum_eq_sum_of_support_subset _ fun i hi ↦ ?_
  have hi : c i * (Ψ i t : R) ≠ 0 := hi
  exact hF i (fun h ↦ hi (by simp [h])) (fun h ↦ hi (by simp [h]))

/-- The transfer of a locally finite chain is locally finite. -/
lemma lfTransferFun_mem {c : I → R} (hc : c ∈ lfChains R R carI) {Ψ : I → T →₀ ℤ}
    (hΨ : IsCarrierDecreasing carI carT Ψ) : lfTransferFun Ψ c ∈ lfChains R R carT := by
  intro x
  obtain ⟨V, hV, hfin⟩ := hc x
  refine ⟨V, hV, ?_⟩
  have hfin' : {i | c i ≠ 0 ∧ (carI i ∩ V).Nonempty}.Finite := hfin
  refine (hfin'.biUnion fun i _ ↦ (Ψ i).support.finite_toSet).subset ?_
  rintro t ⟨ht, y, hy, hyV⟩
  obtain ⟨i, hci, hΨi⟩ := exists_ne_zero_of_lfTransferFun_ne_zero ht
  exact Set.mem_biUnion (x := i) ⟨hci, y, hΨ i t hΨi hy, hyV⟩ (by simpa using hΨi)

/-- The transfer is additive in the locally finite chain. -/
lemma lfTransferFun_add (Ψ : I → T →₀ ℤ) (c d : I → R) (hc : c ∈ lfChains R R carI)
    (hd : d ∈ lfChains R R carI) (hΨ : IsCarrierDecreasing carI carT Ψ)
    (hT : ∀ t, IsCompact (carT t) ∧ (carT t).Nonempty) :
    lfTransferFun Ψ (c + d) = lfTransferFun Ψ c + lfTransferFun Ψ d := by
  ext t
  let F := (finite_setOf_ne_zero_and_ne_zero hc hΨ t (hT t)).toFinset ∪
    (finite_setOf_ne_zero_and_ne_zero hd hΨ t (hT t)).toFinset
  have h1 : ∀ i, c i ≠ 0 → Ψ i t ≠ 0 → i ∈ F := fun i h h' ↦
    Finset.mem_union_left _ (by simpa using And.intro h h')
  have h2 : ∀ i, d i ≠ 0 → Ψ i t ≠ 0 → i ∈ F := fun i h h' ↦
    Finset.mem_union_right _ (by simpa using And.intro h h')
  have h3 : ∀ i, (c + d) i ≠ 0 → Ψ i t ≠ 0 → i ∈ F := fun i h h' ↦ by
    by_cases hc0 : c i = 0
    · exact h2 i (fun hd0 ↦ h (by simp [hc0, hd0])) h'
    · exact h1 i hc0 h'
  rw [Pi.add_apply, lfTransferFun_eq_sum Ψ _ t F h3, lfTransferFun_eq_sum Ψ _ t F h1,
    lfTransferFun_eq_sum Ψ _ t F h2, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by simp [add_mul]

/-- The transfer commutes with scalar multiplication of the locally finite chain. -/
lemma lfTransferFun_smul (Ψ : I → T →₀ ℤ) (r : R) (c : I → R) (hc : c ∈ lfChains R R carI)
    (hΨ : IsCarrierDecreasing carI carT Ψ) (hT : ∀ t, IsCompact (carT t) ∧ (carT t).Nonempty) :
    lfTransferFun Ψ (r • c) = r • lfTransferFun Ψ c := by
  ext t
  let F := (finite_setOf_ne_zero_and_ne_zero hc hΨ t (hT t)).toFinset
  have h1 : ∀ i, c i ≠ 0 → Ψ i t ≠ 0 → i ∈ F := fun i h h' ↦ by simpa [F] using And.intro h h'
  have h2 : ∀ i, (r • c) i ≠ 0 → Ψ i t ≠ 0 → i ∈ F := fun i h h' ↦
    h1 i (fun h0 ↦ h (by simp [h0])) h'
  rw [Pi.smul_apply, lfTransferFun_eq_sum Ψ _ t F h2, lfTransferFun_eq_sum Ψ _ t F h1,
    Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by simp [smul_eq_mul, mul_assoc]

/-- The transfer is additive in the family, over a finite sum. -/
lemma lfTransferFun_finset_sum {κ : Type*} (s : Finset κ) (Ψ : κ → I → T →₀ ℤ) (c : I → R)
    (hc : c ∈ lfChains R R carI) (hΨ : ∀ k, IsCarrierDecreasing carI carT (Ψ k))
    (hT : ∀ t, IsCompact (carT t) ∧ (carT t).Nonempty) :
    lfTransferFun (fun i ↦ ∑ k ∈ s, Ψ k i) c = ∑ k ∈ s, lfTransferFun (Ψ k) c := by
  ext t
  let F := s.biUnion fun k ↦ (finite_setOf_ne_zero_and_ne_zero hc (hΨ k) t (hT t)).toFinset
  have hF : ∀ k ∈ s, ∀ i, c i ≠ 0 → Ψ k i t ≠ 0 → i ∈ F := fun k hk i h h' ↦
    Finset.mem_biUnion.2 ⟨k, hk, by simpa using And.intro h h'⟩
  have hF' : ∀ i, c i ≠ 0 → (∑ k ∈ s, Ψ k i) t ≠ 0 → i ∈ F := fun i h h' ↦ by
    rw [Finsupp.finset_sum_apply] at h'
    obtain ⟨k, hk, hk'⟩ := Finset.exists_ne_zero_of_sum_ne_zero h'
    exact hF k hk i h hk'
  rw [lfTransferFun_eq_sum _ c t F hF', Finset.sum_apply]
  rw [Finset.sum_congr rfl fun k hk ↦ lfTransferFun_eq_sum (Ψ k) c t F (hF k hk), Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finsupp.finset_sum_apply, Int.cast_sum, Finset.mul_sum]

/-- Transfer along `fun i ↦ z • Ψ i` is `z` times the transfer along `Ψ`. -/
lemma lfTransferFun_zsmul (z : ℤ) (Ψ : I → T →₀ ℤ) (c : I → R) (hc : c ∈ lfChains R R carI)
    (hΨ : IsCarrierDecreasing carI carT Ψ) (hT : ∀ t, IsCompact (carT t) ∧ (carT t).Nonempty) :
    lfTransferFun (fun i ↦ z • Ψ i) c = z • lfTransferFun Ψ c := by
  ext t
  let F := (finite_setOf_ne_zero_and_ne_zero hc hΨ t (hT t)).toFinset
  have h1 : ∀ i, c i ≠ 0 → Ψ i t ≠ 0 → i ∈ F := fun i h h' ↦ by simpa [F] using And.intro h h'
  have h2 : ∀ i, c i ≠ 0 → (z • Ψ i) t ≠ 0 → i ∈ F := fun i h h' ↦
    h1 i h (fun h0 ↦ h' (by simp [h0]))
  rw [Pi.smul_apply, lfTransferFun_eq_sum _ c t F h2, lfTransferFun_eq_sum Ψ c t F h1,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Finsupp.smul_apply, smul_eq_mul, Int.cast_mul, zsmul_eq_mul]
  ring

/-- Transfer along `fun i ↦ Ψ i + Ψ' i` is the sum of the transfers along `Ψ` and `Ψ'`. -/
lemma lfTransferFun_add_family (Ψ Ψ' : I → T →₀ ℤ) (c : I → R) (hc : c ∈ lfChains R R carI)
    (hΨ : IsCarrierDecreasing carI carT Ψ) (hΨ' : IsCarrierDecreasing carI carT Ψ')
    (hT : ∀ t, IsCompact (carT t) ∧ (carT t).Nonempty) :
    lfTransferFun (fun i ↦ Ψ i + Ψ' i) c = lfTransferFun Ψ c + lfTransferFun Ψ' c := by
  simpa [Fin.sum_univ_two] using lfTransferFun_finset_sum (Finset.univ : Finset (Fin 2)) ![Ψ, Ψ']
    c hc (fun k ↦ by fin_cases k <;> assumption) hT

/-- The coefficient of `b` in `Finsupp.mapDomain f x` is the sum of the coefficients `x a` over
the `a` in the support of `x` with `f a = b`. -/
lemma mapDomain_apply_eq_sum {α β M : Type*} [AddCommMonoid M] (f : α → β) (x : α →₀ M)
    (b : β) :
    Finsupp.mapDomain f x b = ∑ a ∈ x.support, if f a = b then x a else 0 := by
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  simp [Finsupp.single_apply, Finsupp.sum]

/-- The coefficient of `b` in `Finsupp.mapDomain f x` is the sum of the coefficients `x a` over
the `a ∈ S` with `f a = b`, for any finset `S` containing the support of `x`. -/
lemma mapDomain_apply_eq_sum' {α β M : Type*} [AddCommMonoid M] (f : α → β) (x : α →₀ M)
    (b : β) (S : Finset α) (hS : x.support ⊆ S) :
    Finsupp.mapDomain f x b = ∑ a ∈ S, if f a = b then x a else 0 := by
  rw [mapDomain_apply_eq_sum]
  exact Finset.sum_subset hS fun a _ ha ↦ by simp [Finsupp.notMem_support_iff.1 ha]

/-- Pushing a carrier-decreasing family forward along a carrier-decreasing map `φ : T → T'`
gives a carrier-decreasing family. -/
lemma IsCarrierDecreasing.mapDomain {Ψ : I → T →₀ ℤ} (hΨ : IsCarrierDecreasing carI carT Ψ)
    (φ : T → T') (hφ : ∀ t, carT' (φ t) ⊆ carT t) :
    IsCarrierDecreasing carI carT' fun i ↦ Finsupp.mapDomain φ (Ψ i) := fun i t' h ↦ by
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1
    (Finsupp.mapDomain_support (Finsupp.mem_support_iff.2 h))
  exact (hφ t).trans (hΨ i t (Finsupp.mem_support_iff.1 ht))

/-- An integer multiple of a carrier-decreasing family is carrier-decreasing. -/
lemma IsCarrierDecreasing.zsmul {Ψ : I → T →₀ ℤ} (hΨ : IsCarrierDecreasing carI carT Ψ) (z : ℤ) :
    IsCarrierDecreasing carI carT fun i ↦ z • Ψ i := fun i t h ↦
  hΨ i t fun h0 ↦ h (by simp [h0])

/-- The sum of two carrier-decreasing families is carrier-decreasing. -/
lemma IsCarrierDecreasing.add {Ψ Ψ' : I → T →₀ ℤ} (hΨ : IsCarrierDecreasing carI carT Ψ)
    (hΨ' : IsCarrierDecreasing carI carT Ψ') :
    IsCarrierDecreasing carI carT fun i ↦ Ψ i + Ψ' i := fun i t h ↦ by
  by_cases h0 : Ψ i t = 0
  · exact hΨ' i t fun h1 ↦ h (by simp [h0, h1])
  · exact hΨ i t h0

/-- A finite sum of carrier-decreasing families is carrier-decreasing. -/
lemma IsCarrierDecreasing.sum {κ : Type*} (s : Finset κ) {Ψ : κ → I → T →₀ ℤ}
    (hΨ : ∀ k, IsCarrierDecreasing carI carT (Ψ k)) :
    IsCarrierDecreasing carI carT fun i ↦ ∑ k ∈ s, Ψ k i := fun i t h ↦ by
  rw [Finsupp.finset_sum_apply] at h
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact hΨ k i t hk

/-- Precomposing a carrier-decreasing family with a carrier-decreasing map `g : I' → I` gives a
carrier-decreasing family. -/
lemma IsCarrierDecreasing.comp {Ψ : I → T →₀ ℤ} (hΨ : IsCarrierDecreasing carI carT Ψ)
    (g : I' → I) (hg : ∀ i', carI (g i') ⊆ carI' i') :
    IsCarrierDecreasing carI' carT (Ψ ∘ g) := fun i' t h ↦ (hΨ (g i') t h).trans (hg i')

/-- The transfer is additive in the chain, over a finite sum. -/
lemma lfTransferFun_finset_sum_chain {κ : Type*} (s : Finset κ) (Ψ : I → T →₀ ℤ)
    (c : κ → I → R) (hc : ∀ k, c k ∈ lfChains R R carI) (hΨ : IsCarrierDecreasing carI carT Ψ)
    (hT : ∀ t, IsCompact (carT t) ∧ (carT t).Nonempty) :
    lfTransferFun Ψ (∑ k ∈ s, c k) = ∑ k ∈ s, lfTransferFun Ψ (c k) := by
  induction s using Finset.induction_on with
  | empty =>
    ext t
    simp [lfTransferFun]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      lfTransferFun_add Ψ _ _ (hc a) (Submodule.sum_mem _ fun k _ ↦ hc k) hΨ hT, ih]

/-- Push-forward of a transfer is the transfer along the pushed-forward family. -/
lemma pushforwardFun_lfTransferFun {c : I → R} (hc : c ∈ lfChains R R carI)
    {Ψ : I → T →₀ ℤ} (hΨ : IsCarrierDecreasing carI carT Ψ) (φ : T → T')
    (hφ : ∀ t, carT' (φ t) ⊆ carT t) (hT' : ∀ t', IsCompact (carT' t') ∧ (carT' t').Nonempty) :
    pushforwardFun φ (lfTransferFun Ψ c) =
      lfTransferFun (fun i ↦ Finsupp.mapDomain φ (Ψ i)) c := by
  ext t'
  have hfin : {i | c i ≠ 0 ∧ (carI i ∩ carT' t').Nonempty}.Finite :=
    hc.finite_inter_compact (hT' t').1
  let FI := hfin.toFinset
  let FT := FI.biUnion fun i ↦ (Ψ i).support
  have hmem : ∀ i t, c i ≠ 0 → Ψ i t ≠ 0 → φ t = t' → i ∈ FI ∧ t ∈ FT := fun i t h h' h'' ↦ by
    have hi : i ∈ FI := by
      obtain ⟨x, hx⟩ := (hT' t').2
      simpa [FI] using And.intro h ⟨x, hΨ i t h' (hφ t (h'' ▸ hx)), hx⟩
    exact ⟨hi, Finset.mem_biUnion.2 ⟨i, hi, by simpa using h'⟩⟩
  have hL : pushforwardFun φ (lfTransferFun Ψ c) t' =
      ∑ t ∈ FT, if φ t = t' then ∑ i ∈ FI, c i * (Ψ i t : R) else 0 := by
    refine (pushforwardFun_apply_eq_sum φ _ t' FT fun t ht h ↦ ?_).trans
      (Finset.sum_congr rfl fun t _ ↦ ?_)
    · obtain ⟨i, hi, hi'⟩ := exists_ne_zero_of_lfTransferFun_ne_zero ht
      exact (hmem i t hi hi' h).2
    · split_ifs with h
      · exact lfTransferFun_eq_sum Ψ c t FI fun i hi hi' ↦ (hmem i t hi hi' h).1
      · rfl
  have hR : ∀ i ∈ FI, Finsupp.mapDomain φ (Ψ i) t' = ∑ t ∈ FT, if φ t = t' then Ψ i t else 0 :=
    fun i hi ↦ mapDomain_apply_eq_sum' φ (Ψ i) t' FT fun t ht ↦
      Finset.mem_biUnion.2 ⟨i, hi, ht⟩
  rw [hL, lfTransferFun_eq_sum _ c t' FI fun i hi hi' ↦ ?_]
  · symm
    calc ∑ i ∈ FI, c i * ((Finsupp.mapDomain φ (Ψ i) t' : ℤ) : R)
        = ∑ i ∈ FI, ∑ t ∈ FT, (if φ t = t' then c i * (Ψ i t : R) else 0) :=
          Finset.sum_congr rfl fun i hi ↦ by
            rw [hR i hi, Int.cast_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun t _ ↦ by split_ifs <;> simp
      _ = ∑ t ∈ FT, ∑ i ∈ FI, (if φ t = t' then c i * (Ψ i t : R) else 0) := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun t _ ↦ by split_ifs <;> simp
  · obtain ⟨t, ht, rfl⟩ : ∃ t, Ψ i t ≠ 0 ∧ φ t = t' := by
      by_contra hh
      push Not at hh
      refine hi' ?_
      rw [mapDomain_apply_eq_sum]
      exact Finset.sum_eq_zero fun t ht ↦ by
        split_ifs with h
        · exact absurd (hh t (by simpa using ht)) (by simp [h])
        · rfl
    exact (hmem i t hi ht rfl).1

/-- A transfer of a push-forward is the transfer along the composite family. -/
lemma lfTransferFun_pushforwardFun {c : I' → R} (hc : c ∈ lfChains R R carI') (g : I' → I)
    (hg : ∀ i', carI (g i') ⊆ carI' i') {Ψ : I → T →₀ ℤ} (hΨ : IsCarrierDecreasing carI carT Ψ)
    (hT : ∀ t, IsCompact (carT t) ∧ (carT t).Nonempty) :
    lfTransferFun Ψ (pushforwardFun g c) = lfTransferFun (Ψ ∘ g) c := by
  ext t
  have hfin : {i' | c i' ≠ 0 ∧ (carI' i' ∩ carT t).Nonempty}.Finite :=
    hc.finite_inter_compact (hT t).1
  let F' := hfin.toFinset
  have hmem : ∀ i', c i' ≠ 0 → Ψ (g i') t ≠ 0 → i' ∈ F' := fun i' h h' ↦ by
    obtain ⟨x, hx⟩ := (hT t).2
    simpa [F'] using And.intro h ⟨x, hg i' (hΨ _ t h' hx), hx⟩
  rw [lfTransferFun_eq_sum (Ψ ∘ g) c t F' hmem,
    lfTransferFun_eq_sum Ψ _ t (F'.image g) fun i hi hi' ↦ ?_]
  · have : ∀ i ∈ F'.image g, pushforwardFun g c i * (Ψ i t : R) =
        ∑ i' ∈ F', if g i' = i then c i' * (Ψ i t : R) else 0 := fun i _ ↦ by
      by_cases hΨi : Ψ i t = 0
      · simp [hΨi]
      · rw [pushforwardFun_apply_eq_sum g c i F' fun i' h h' ↦ hmem i' h (h' ▸ hΨi),
          Finset.sum_mul]
        exact Finset.sum_congr rfl fun i' _ ↦ by split_ifs <;> simp
    rw [Finset.sum_congr rfl this, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i' hi' ↦ ?_
    rw [Finset.sum_ite_eq (F'.image g) (g i'), if_pos (Finset.mem_image_of_mem g hi')]
    rfl
  · obtain ⟨i', hi'c, rfl⟩ := support_pushforwardFun_subset g c hi
    exact Finset.mem_image_of_mem g (hmem i' hi'c hi')

end Transfer

section Tensor

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {S S' U U' : Type*}
  {carS : S → Set X} {carS' : S' → Set Y} {carU : U → Set X} {carU' : U' → Set Y}
  {R : Type*} [CommRing R]

/-- The product carriers `carS σ ×ˢ carS' τ` in `X × Y`. -/
def prodCarrier (carS : S → Set X) (carS' : S' → Set Y) (p : S × S') : Set (X × Y) :=
  carS p.1 ×ˢ carS' p.2

/-- The product carrier of `(σ, τ)` is `carS σ ×ˢ carS' τ`. -/
lemma prodCarrier_apply (carS : S → Set X) (carS' : S' → Set Y) (p : S × S') :
    prodCarrier carS carS' p = carS p.1 ×ˢ carS' p.2 :=
  rfl

/-- The tensor of two chains: `(σ, τ) ↦ c σ * d τ`. -/
def lfTensor (c : S → R) (d : S' → R) : S × S' → R := fun p ↦ c p.1 * d p.2

/-- The coefficient of `(σ, τ)` in the tensor is `c σ * d τ`. -/
lemma lfTensor_apply (c : S → R) (d : S' → R) (p : S × S') : lfTensor c d p = c p.1 * d p.2 :=
  rfl

/-- The tensor of locally finite chains is locally finite for the product carriers. -/
lemma lfTensor_mem {c : S → R} {d : S' → R} (hc : c ∈ lfChains R R carS)
    (hd : d ∈ lfChains R R carS') : lfTensor c d ∈ lfChains R R (prodCarrier carS carS') := by
  rintro ⟨x, y⟩
  obtain ⟨V, hV, hfin⟩ := hc x
  obtain ⟨W, hW, hfin'⟩ := hd y
  refine ⟨V ×ˢ W, prod_mem_nhds hV hW, (hfin.prod hfin').subset ?_⟩
  rintro ⟨σ, τ⟩ ⟨hστ, ⟨a, b⟩, ⟨ha, hb⟩, ha', hb'⟩
  have hστ : c σ * d τ ≠ 0 := hστ
  exact ⟨⟨fun h ↦ hστ (by simp [h]), a, ha, ha'⟩, ⟨fun h ↦ hστ (by simp [h]), b, hb, hb'⟩⟩

/-- The tensor is additive in its first argument. -/
lemma lfTensor_add_left (c c' : S → R) (d : S' → R) :
    lfTensor (c + c') d = lfTensor c d + lfTensor c' d := by
  ext p
  simp [lfTensor, add_mul]

/-- The tensor is additive in its second argument. -/
lemma lfTensor_add_right (c : S → R) (d d' : S' → R) :
    lfTensor c (d + d') = lfTensor c d + lfTensor c d' := by
  ext p
  simp [lfTensor, mul_add]

/-- The tensor commutes with scalar multiplication in its first argument. -/
lemma lfTensor_smul_left (r : R) (c : S → R) (d : S' → R) :
    lfTensor (r • c) d = r • lfTensor c d := by
  ext p
  simp [lfTensor, mul_assoc]

/-- The tensor commutes with scalar multiplication in its second argument. -/
lemma lfTensor_smul_right (r : R) (c : S → R) (d : S' → R) :
    lfTensor c (r • d) = r • lfTensor c d := by
  ext p
  simp [lfTensor, mul_left_comm]

/-- Push-forward along `Prod.map f id` of the tensor `c ⊗ d` is the tensor of the push-forward of
`c` along `f` with `d`. -/
lemma pushforwardFun_prodMap_id_lfTensor {c : S → R} (hc : c ∈ lfChains R R carS) (f : S → U)
    (hf : ∀ σ, carU (f σ) ⊆ carS σ) (hU : ∀ u, IsCompact (carU u) ∧ (carU u).Nonempty)
    (d : S' → R) :
    pushforwardFun (Prod.map f id) (lfTensor c d) = lfTensor (pushforwardFun f c) d := by
  ext ⟨u, τ⟩
  let F := (finite_fiber hc f hf u (hU u).1 (hU u).2).toFinset
  have hF : ∀ σ, c σ ≠ 0 → f σ = u → σ ∈ F := fun σ h h' ↦ by simpa [F] using And.intro h h'
  rw [pushforwardFun_apply_eq_sum _ _ _ (F ×ˢ {τ}) fun p hp hp' ↦ ?_]
  · simp only [lfTensor]
    rw [pushforwardFun_apply_eq_sum f c u F hF, Finset.sum_mul, Finset.sum_product]
    simp only [Finset.sum_singleton]
    exact Finset.sum_congr rfl fun σ _ ↦ by simp [Prod.ext_iff]
  · obtain ⟨σ, τ'⟩ := p
    simp only [Prod.map, Prod.mk.injEq, id] at hp'
    obtain ⟨h1, rfl⟩ := hp'
    exact Finset.mem_product.2
      ⟨hF σ (fun h ↦ hp (by simp [lfTensor, h])) h1, Finset.mem_singleton_self _⟩

/-- Push-forward along `Prod.map id g` of the tensor `c ⊗ d` is the tensor of `c` with the
push-forward of `d` along `g`. -/
lemma pushforwardFun_prodMap_id_lfTensor' (c : S → R) {d : S' → R}
    (hd : d ∈ lfChains R R carS') (g : S' → U')
    (hg : ∀ τ, carU' (g τ) ⊆ carS' τ) (hU : ∀ u, IsCompact (carU' u) ∧ (carU' u).Nonempty) :
    pushforwardFun (Prod.map id g) (lfTensor c d) = lfTensor c (pushforwardFun g d) := by
  ext ⟨σ, u⟩
  let F := (finite_fiber hd g hg u (hU u).1 (hU u).2).toFinset
  have hF : ∀ τ, d τ ≠ 0 → g τ = u → τ ∈ F := fun τ h h' ↦ by simpa [F] using And.intro h h'
  rw [pushforwardFun_apply_eq_sum _ _ _ ({σ} ×ˢ F) fun p hp hp' ↦ ?_]
  · simp only [lfTensor]
    rw [pushforwardFun_apply_eq_sum g d u F hF, Finset.mul_sum,
      Finset.sum_product, Finset.sum_singleton]
    exact Finset.sum_congr rfl fun τ _ ↦ by simp [Prod.ext_iff]
  · obtain ⟨σ', τ⟩ := p
    simp only [Prod.map, Prod.mk.injEq, id] at hp'
    obtain ⟨rfl, h2⟩ := hp'
    exact Finset.mem_product.2
      ⟨Finset.mem_singleton_self _, hF τ (fun h ↦ hp (by simp [lfTensor, h])) h2⟩

end Tensor

end LocallyFiniteChain

end MMP
