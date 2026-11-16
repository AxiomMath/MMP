module

public import MMP.AlgebraicTopology.BorelMoore.CompactExhaustion
public import MMP.AlgebraicTopology.PoincareDuality.MayerVietoris
public import MMP.AlgebraicTopology.SingularCohomology.CupProduct.Comparison

/-!
# Finite singular chains as locally finite chains

A finite singular chain `f = ∑ a_σ σ` of a space `X` (a finitely supported function on the
continuous maps `Δⁿ → X`, `MMP.SingularChain.Chain`) is a locally finite chain,
and every finitely supported locally finite chain arises this way; the boundary of
`MMP.SingularChain.bd` is the differential of the complex of locally finite
chains. A finite chain lies in `X - K` exactly when, as a locally finite chain, it is off `K`.

Hence the vanishing of relative homology `H_{m+1}(X, X - K)`, stated on finite chains
(`MMP.SingularChain.RelVanishing`), is the hypothesis
`MMP.borelMooreHomology.RelVanishingBM` of the passage from local homology to
Borel–Moore homology.

## Main definitions

* `MMP.borelMooreHomology.ofFinsupp`: a finite chain as a locally finite chain.

## Main results

* `MMP.borelMooreHomology.d_ofFinsupp`: `∂` commutes with `ofFinsupp`.
* `MMP.borelMooreHomology.isOffChain_ofFinsupp_iff`: off `K` iff in `X - K`.
* `MMP.borelMooreHomology.relVanishingBM_of_relVanishing`.
* `MMP.borelMooreHomology.isZero_of_relVanishing`: `H_{m+1} X = 0` when
  `H_{m+1}(X, X - K; R) = H_{m+2}(X, X - K; R) = 0` for every compact `K`, on a weakly locally
  compact σ-compact space.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicTopology Opposite Topology Set Simplicial

universe u

namespace MMP

namespace borelMooreHomology

open LocallyFiniteChain SingularChain

variable {R : Type u} [CommRing R] {X : TopCat.{u}}

/-- A finite singular chain of `X`, as a locally finite chain. -/
def ofFinsupp {n : ℕ} (f : Chain R X n) :
    (borelMooreChainComplex R (ModuleCat.of R R) X).X n :=
  ⟨fun σ ↦ f (SingularCochain.simplexEquiv X _ σ), fun _ ↦ ⟨univ, Filter.univ_mem,
    ((f.support.finite_toSet.preimage (SingularCochain.simplexEquiv X _).injective.injOn)).subset
      fun σ hσ ↦ by simpa using hσ.1⟩⟩

/-- The coefficient of `ofFinsupp f` at a simplex is the coefficient of `f` at the corresponding
continuous map `Δⁿ → X`. -/
lemma ofFinsupp_apply {n : ℕ} (f : Chain R X n) (σ) :
    (ofFinsupp f).1 σ = f (SingularCochain.simplexEquiv X _ σ) := rfl

/-- `ofFinsupp` commutes with subtraction. -/
lemma ofFinsupp_sub {n : ℕ} (f g : Chain R X n) :
    ofFinsupp (f - g) = ofFinsupp f - ofFinsupp g := rfl

/-- The boundary of a finite chain, computed in the complex of locally finite chains. -/
lemma d_ofFinsupp {n : ℕ} (f : Chain R X (n + 1)) :
    ((borelMooreChainComplex R (ModuleCat.of R R) X).d (n + 1) n).hom (ofFinsupp f) =
      ofFinsupp (bd R n f) := by
  classical
  apply Subtype.ext
  funext τ
  rw [borelMooreChainComplex_d_apply]
  change dFun (M := R) (fun i : Fin (n + 2) ↦ (TopCat.toSSet.obj X).δ i) (ofFinsupp f).1 τ =
    bd R n f (SingularCochain.simplexEquiv X _ τ)
  rw [bd_apply, dFun]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  set e := SingularCochain.simplexEquiv X (n + 1)
  rw [pushforwardFun_apply_eq_sum _ _ τ (f.support.map e.symm.toEmbedding) (fun σ hσ _ ↦ by
    simp only [Finset.mem_map_equiv, Equiv.symm_symm, Finsupp.mem_support_iff]
    exact hσ), Finset.sum_map, zsmul_eq_mul, Finset.mul_sum]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ'' _ ↦ ?_
  congr 1
  have hiff : (TopCat.toSSet.obj X).δ i (e.symm τ'') = τ ↔
      τ''.comp (face n i) = (SingularCochain.simplexEquiv X _ τ) := by
    simp only [e, SingularCochain.simplexEquiv_symm_δ, Equiv.symm_apply_eq]
  simp only [Equiv.coe_toEmbedding]
  by_cases h : τ''.comp (face n i) = (SingularCochain.simplexEquiv X _ τ)
  · rw [if_pos (hiff.2 h), if_pos h, ofFinsupp_apply, e.apply_symm_apply]
  · rw [if_neg (fun h' ↦ h (hiff.1 h')), if_neg h]

/-- A finite chain is off `K` exactly when all its simplices lie in `X - K`. -/
lemma isOffChain_ofFinsupp_iff {n : ℕ} {K : Set X} {f : Chain R X n} :
    IsOffChain K (ofFinsupp f) ↔ f ∈ inside R n Kᶜ := by
  rw [inside, Finsupp.mem_supported]
  constructor
  · intro h τ hτ
    rw [Finset.mem_coe, Finsupp.mem_support_iff] at hτ
    rintro _ ⟨t, rfl⟩ htK
    apply hτ
    have := h ((SingularCochain.simplexEquiv X _).symm τ)
      ⟨τ t, ⟨stdSimplexHomeo _ t, by simp [SingularCochain.simplexEquiv]⟩, htK⟩
    rwa [ofFinsupp_apply, Equiv.apply_symm_apply] at this
  · rintro h σ ⟨x, ⟨t, rfl⟩, hx⟩
    rw [ofFinsupp_apply]
    by_contra hne
    exact h (Finsupp.mem_support_iff.2 hne)
      ⟨(stdSimplexHomeo _).symm t, by simp [SingularCochain.simplexEquiv]⟩ hx

/-- A finitely supported locally finite chain, as a finite chain. -/
def toFinsupp {n : ℕ} (c : (borelMooreChainComplex R (ModuleCat.of R R) X).X n)
    (hc : (Function.support c.1).Finite) : Chain R X n :=
  Finsupp.ofSupportFinite (fun τ ↦ c.1 ((SingularCochain.simplexEquiv X _).symm τ))
    (hc.preimage (SingularCochain.simplexEquiv X _).symm.injective.injOn |>.subset fun _ h ↦ h)

/-- `ofFinsupp` recovers a finitely supported locally finite chain from its `toFinsupp`. -/
lemma ofFinsupp_toFinsupp {n : ℕ} (c : (borelMooreChainComplex R (ModuleCat.of R R) X).X n)
    (hc : (Function.support c.1).Finite) : ofFinsupp (toFinsupp c hc) = c :=
  Subtype.ext <| funext fun σ ↦ congrArg c.1 ((SingularCochain.simplexEquiv X _).symm_apply_apply σ)

/-- The vanishing of `H_{m+1}(X, X - K; R)` on finite chains gives the hypothesis of the passage
to Borel–Moore homology. -/
lemma relVanishingBM_of_relVanishing {m : ℕ} {K : Set X} (h : RelVanishing R X m K) :
    RelVanishingBM X R (ModuleCat.of R R) m K := by
  intro c hc hdc
  have hcf : ofFinsupp (toFinsupp c hc) = c := ofFinsupp_toFinsupp c hc
  rw [← hcf, d_ofFinsupp, isOffChain_ofFinsupp_iff] at hdc
  obtain ⟨w, hw⟩ := h _ hdc
  refine ⟨ofFinsupp w, ?_⟩
  rwa [d_ofFinsupp, ← hcf, ← ofFinsupp_sub, isOffChain_ofFinsupp_iff]

/-- **Vanishing of Borel–Moore homology from local vanishing**, for finite singular chains: on a
weakly locally compact σ-compact space `X`, if `H_{m+1}(X, X - K; R) = 0` and
`H_{m+2}(X, X - K; R) = 0` for every compact `K`, then `H_{m+1} X = 0`. -/
theorem isZero_of_relVanishing [WeaklyLocallyCompactSpace X] [SigmaCompactSpace X] (m : ℕ)
    (h₁ : ∀ K : Set X, IsCompact K → RelVanishing R X m K)
    (h₂ : ∀ K : Set X, IsCompact K → RelVanishing R X (m + 1) K) :
    IsZero (borelMooreHomology R (ModuleCat.of R R) X ((m + 1 : ℕ) : ℤ)) :=
  isZero_of_relVanishingBM m (fun K hK ↦ relVanishingBM_of_relVanishing (h₁ K hK))
    (fun K hK ↦ relVanishingBM_of_relVanishing (h₂ K hK))

end borelMooreHomology

end MMP
