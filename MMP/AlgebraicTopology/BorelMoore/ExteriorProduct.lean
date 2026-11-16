module

public import MMP.AlgebraicTopology.SingularHomology.CrossProduct
public import MMP.AlgebraicTopology.BorelMoore.LocallyFiniteChainTransfer
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
/-!
# The exterior product in Borel–Moore homology (Fulton, §19.1)

For spaces `X`, `Y`, the exterior product `× : H_i X ⊗ H_j Y → H_{i+j}(X × Y)` is induced by
the cross product of locally finite chains: for locally finite chains `c = ∑ a_σ σ` on `X` and
`d = ∑ b_τ τ` on `Y`, `c × d = ∑ a_σ b_τ (σ × τ)`, where `σ × τ` is the Eilenberg–Zilber shuffle
product of singular simplices (`MMP.SingularCross.crossSimplex`). The sum is
locally finite: the simplices of `σ × τ` lie in `σ(Δᵖ) × τ(Δ^q)`, so near a point of `X × Y` only
finitely many pairs `(σ, τ)` contribute. The Leibniz rule `∂(c × d) = ∂c × d + (-1)^p c × ∂d`
shows that the cross product of cycles is a cycle, and that it vanishes on homology when one
factor is a boundary.

## Main definitions

* `MMP.BorelMooreCross.crossChain`: the cross product of locally finite chains.
* `MMP.BorelMooreCross.crossHomQ`: the cross product on cycles modulo boundaries.
* `MMP.borelMooreHomology.exteriorProduct`: `× : H_i X ⊗ H_j Y → H_{i+j}(X × Y)`.

## Main results

* `MMP.BorelMooreCross.d_crossChain`: the Leibniz rule.
* `MMP.BorelMooreCross.crossHomQ_mk`: `[z] × [w] = [z × w]`.
* `MMP.BorelMooreCross.exteriorProductBilin_natCast`: the exterior product in
  degrees `p, q : ℕ` is the cross product of classes of cycles.

## Implementation notes

Coefficients are in a commutative ring `R` (Fulton: `ℤ` and `ℚ`). The exterior product is zero
when `i < 0` or `j < 0`, where the groups vanish. The cross product of simplices is defined
through lattice paths in `[p] × [q]` (`MMP.LatticePath.shuffleSum`), whose Leibniz
rule is proved once, combinatorially, and transported to simplices.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [A. Borel, J. C. Moore, *Homology theory for locally compact spaces*][borelmoore1960], §6.
* [S. Eilenberg, S. MacLane, *On the groups H(Π, n), I*][eilenbergmaclane1953], §5.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Simplicial AlgebraicTopology MMP.LatticePath
  MMP.SingularCross MMP.LocallyFiniteChain

universe u

namespace MMP

namespace BorelMooreCross

variable (R : Type u) [CommRing R] {X Y : TopCat.{u}}

/-- The complex of locally finite singular chains with coefficients in `R`. -/
abbrev BM (X : TopCat.{u}) : ChainComplex (ModuleCat.{u} R) ℕ :=
  borelMooreChainComplex R (ModuleCat.of R R) X

/-- The image of a singular simplex is compact and nonempty. -/
lemma compact_nonempty {Z : TopCat.{u}} {n : ℕ} (ρ : Simp Z n) :
    IsCompact (singularSimplexImage Z ρ) ∧ (singularSimplexImage Z ρ).Nonempty :=
  ⟨isCompact_singularSimplexImage ρ, nonempty_singularSimplexImage ρ⟩

/-- The coefficient function of a locally finite chain. -/
def coeff {n : ℕ} (c : (BM R X).X n) : Simp X n → R :=
  (show lfChains R R (singularSimplexImage X (n := op ⦋n⦌)) from c).1

/-- The coefficient function of a locally finite chain is locally finite. -/
lemma coeff_mem {n : ℕ} (c : (BM R X).X n) :
    coeff R c ∈ lfChains R R (singularSimplexImage X (n := op ⦋n⦌)) :=
  (show lfChains R R (singularSimplexImage X (n := op ⦋n⦌)) from c).2

/-- A locally finite chain, as an element of the complex. -/
def ofCoeff {n : ℕ} (f : Simp X n → R)
    (hf : f ∈ lfChains R R (singularSimplexImage X (n := op ⦋n⦌))) : (BM R X).X n :=
  show lfChains R R (singularSimplexImage X (n := op ⦋n⦌)) from ⟨f, hf⟩

/-- The coefficient function of `ofCoeff R f hf` is `f`. -/
@[simp] lemma coeff_ofCoeff {n : ℕ} (f : Simp X n → R)
    (hf : f ∈ lfChains R R (singularSimplexImage X (n := op ⦋n⦌))) :
    coeff R (ofCoeff R (X := X) (n := n) f hf) = f :=
  rfl

/-- A locally finite chain is determined by its coefficient function. -/
lemma coeff_injective {n : ℕ} : Function.Injective (coeff R (X := X) (n := n)) :=
  fun _ _ h ↦ Subtype.ext h

/-- The coefficient function of a sum of two chains is the sum of their coefficient functions. -/
@[simp] lemma coeff_add {n : ℕ} (c d : (BM R X).X n) : coeff R (c + d) = coeff R c + coeff R d :=
  rfl

/-- The coefficient function of `r • c` is `r` times that of `c`. -/
@[simp] lemma coeff_smul {n : ℕ} (r : R) (c : (BM R X).X n) : coeff R (r • c) = r • coeff R c :=
  rfl

/-- The coefficient function of `z • c`, for an integer `z`, is `z` times that of `c`. -/
@[simp] lemma coeff_zsmul {n : ℕ} (z : ℤ) (c : (BM R X).X n) : coeff R (z • c) = z • coeff R c :=
  rfl

/-- The coefficient function of the zero chain is zero. -/
@[simp] lemma coeff_zero {n : ℕ} : coeff R (0 : (BM R X).X n) = 0 :=
  rfl

/-- The coefficient function of a finite sum of chains is the sum of their coefficient
functions. -/
lemma coeff_sum {n : ℕ} {ι : Type*} (s : Finset ι) (c : ι → (BM R X).X n) :
    coeff R (∑ i ∈ s, c i) = ∑ i ∈ s, coeff R (c i) :=
  Submodule.coe_sum _ _ _

/-- The boundary of locally finite chains is the alternating sum of the face push-forwards. -/
lemma coeff_d (n : ℕ) (c : (BM R X).X (n + 1)) :
    coeff R (((BM R X).d (n + 1) n).hom c) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • pushforwardFun ((TopCat.toSSet.obj X).δ i)
        (coeff R c) := by
  have h : (BM R X).d (n + 1) n = AlternatingFaceMapComplex.objD
      (locallyFiniteSingularChains R (ModuleCat.of R R) X) n :=
    alternatingFaceMapComplex_obj_d _ n
  rw [h, AlternatingFaceMapComplex.objD]
  erw [ModuleCat.hom_sum]
  funext σ
  erw [LinearMap.sum_apply, coeff_sum, Finset.sum_apply]

section Cross

variable {R}

/-- The product carriers on pairs of simplices. -/
abbrev carP (X Y : TopCat.{u}) (p q : ℕ) : Simp X p × Simp Y q → Set (TopCat.of (X × Y)) :=
  prodCarrier (singularSimplexImage X (n := op ⦋p⦌)) (singularSimplexImage Y (n := op ⦋q⦌))

/-- The family `(σ, τ) ↦ σ × τ` in degree `n`. -/
def crossFamily (n p q : ℕ) : Simp X p × Simp Y q → Simp (TopCat.of (X × Y)) n →₀ ℤ :=
  fun st ↦ crossSimplex n st.1 st.2

/-- Every simplex in the support of `σ × τ` has image contained in `σ(Δᵖ) × τ(Δ^q)`. -/
lemma isCarrierDecreasing_crossFamily (n p q : ℕ) :
    IsCarrierDecreasing (carP X Y p q) (singularSimplexImage (TopCat.of (X × Y)) (n := op ⦋n⦌))
      (crossFamily n p q) := fun st _ h ↦
  singularSimplexImage_subset_of_mem_support n st.1 st.2 h

/-- The coefficient function of the cross product of locally finite chains. -/
def crossFun (n p q : ℕ) (c : Simp X p → R) (d : Simp Y q → R) : Simp (TopCat.of (X × Y)) n → R :=
  lfTransferFun (crossFamily n p q) (lfTensor c d)

/-- The cross product of locally finite coefficient functions is locally finite. -/
lemma crossFun_mem (n p q : ℕ) {c : Simp X p → R} {d : Simp Y q → R}
    (hc : c ∈ lfChains R R (singularSimplexImage X (n := op ⦋p⦌)))
    (hd : d ∈ lfChains R R (singularSimplexImage Y (n := op ⦋q⦌))) :
    crossFun n p q c d ∈ lfChains R R (singularSimplexImage (TopCat.of (X × Y)) (n := op ⦋n⦌)) :=
  lfTransferFun_mem (lfTensor_mem hc hd) (isCarrierDecreasing_crossFamily n p q)

variable (R) in
/-- The cross product `c × d` of locally finite chains of degrees `p` and `q`, a locally finite
chain of degree `n` on `X × Y` (Fulton, §19.1; zero unless `n = p + q`). -/
def crossChain (n p q : ℕ) (c : (BM R X).X p) (d : (BM R Y).X q) : (BM R (TopCat.of (X × Y))).X n :=
  ofCoeff R (crossFun n p q (coeff R c) (coeff R d))
    (crossFun_mem n p q (coeff_mem R c) (coeff_mem R d))

/-- The coefficient function of `c × d` is `crossFun` of the coefficient functions. -/
lemma coeff_crossChain (n p q : ℕ) (c : (BM R X).X p) (d : (BM R Y).X q) :
    coeff R (crossChain R n p q c d) = crossFun n p q (coeff R c) (coeff R d) :=
  rfl

/-- The boundary of a cross product, in terms of lattice paths. -/
lemma coeff_d_crossChain (n p q : ℕ) (c : (BM R X).X p) (d : (BM R Y).X q) :
    coeff R (((BM R (TopCat.of (X × Y))).d (n + 1) n).hom (crossChain R (n + 1) p q c d)) =
      lfTransferFun (fun st : Simp X p × Simp Y q ↦ Finsupp.mapDomain (pathSimplex n st.1 st.2)
        (∑ k ∈ Finset.range (p + 1), (-1 : ℤ) ^ k • lmap (cofaceFst k) (lowerFst n p q) +
          (-1 : ℤ) ^ p • ∑ l ∈ Finset.range (q + 1),
            (-1 : ℤ) ^ l • lmap (cofaceSnd l) (lowerSnd n p q)))
        (lfTensor (coeff R c) (coeff R d)) := by
  have he := lfTensor_mem (coeff_mem R c) (coeff_mem R d)
  have hΨ := isCarrierDecreasing_crossFamily (X := X) (Y := Y) (n + 1) p q
  rw [coeff_d, coeff_crossChain, crossFun]
  have hsub : ∀ i : Fin (n + 2), ∀ ρ, singularSimplexImage (TopCat.of (X × Y))
      ((TopCat.toSSet.obj (TopCat.of (X × Y))).δ i ρ) ⊆ singularSimplexImage _ ρ :=
    fun i ρ ↦ singularSimplexImage_map_subset (SimplexCategory.δ i).op ρ
  have key : ∀ i : Fin (n + 2), pushforwardFun ((TopCat.toSSet.obj (TopCat.of (X × Y))).δ i)
      (lfTransferFun (crossFamily (n + 1) p q) (lfTensor (coeff R c) (coeff R d))) =
      lfTransferFun (fun st ↦ Finsupp.mapDomain ((TopCat.toSSet.obj (TopCat.of (X × Y))).δ i)
        (crossFamily (n + 1) p q st)) (lfTensor (coeff R c) (coeff R d)) := fun i ↦
    pushforwardFun_lfTransferFun he hΨ _ (hsub i) compact_nonempty
  rw [Finset.sum_congr rfl fun i _ ↦ by rw [key i]]
  rw [← funext fun st : Simp X p × Simp Y q ↦ sum_δ_crossSimplex n st.1 st.2]
  refine Eq.trans ?_ (lfTransferFun_finset_sum (s := Finset.univ) (Ψ := fun (i : Fin (n + 2)) st ↦
      (-1 : ℤ) ^ (i : ℕ) • Finsupp.mapDomain ((TopCat.toSSet.obj (TopCat.of (X × Y))).δ i)
        (crossFamily (n + 1) p q st)) _ he (fun i ↦ (hΨ.mapDomain _ (hsub i)).zsmul _)
    compact_nonempty).symm
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [lfTransferFun_zsmul _ _ _ he (hΨ.mapDomain _ (hsub i)) compact_nonempty]

/-- The image under `pathSimplex n σ τ` of the first-factor lattice-path faces is
`∑ₖ (-1)^k (∂ₖ σ) × τ`. -/
lemma mapDomain_pathSimplex_fst (n p q : ℕ) (σ : Simp X (p + 1)) (τ : Simp Y q) :
    Finsupp.mapDomain (pathSimplex n σ τ)
        (∑ k ∈ Finset.range (p + 1 + 1), (-1 : ℤ) ^ k • lmap (cofaceFst k) (lowerFst n (p + 1) q)) =
      ∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) • crossSimplex n ((TopCat.toSSet.obj X).δ k σ) τ := by
  rw [lowerFst_succ, Finsupp.mapDomain_finset_sum]
  simp_rw [Finsupp.mapDomain_smul]
  rw [← Fin.sum_univ_eq_sum_range (fun k ↦ (-1 : ℤ) ^ k •
    Finsupp.mapDomain (pathSimplex n σ τ) (lmap (cofaceFst k) (shuffleSum n p q))) (p + 2)]
  exact Finset.sum_congr rfl fun k _ ↦ by rw [mapDomain_pathSimplex_cofaceFst]

/-- The image under `pathSimplex n σ τ` of the second-factor lattice-path faces is
`∑ₗ (-1)^l σ × (∂ₗ τ)`. -/
lemma mapDomain_pathSimplex_snd (n p q : ℕ) (σ : Simp X p) (τ : Simp Y (q + 1)) :
    Finsupp.mapDomain (pathSimplex n σ τ)
        (∑ l ∈ Finset.range (q + 1 + 1), (-1 : ℤ) ^ l • lmap (cofaceSnd l) (lowerSnd n p (q + 1))) =
      ∑ l : Fin (q + 2), (-1 : ℤ) ^ (l : ℕ) • crossSimplex n σ ((TopCat.toSSet.obj Y).δ l τ) := by
  rw [lowerSnd_succ, Finsupp.mapDomain_finset_sum]
  simp_rw [Finsupp.mapDomain_smul]
  rw [← Fin.sum_univ_eq_sum_range (fun l ↦ (-1 : ℤ) ^ l •
    Finsupp.mapDomain (pathSimplex n σ τ) (lmap (cofaceSnd l) (shuffleSum n p q))) (q + 2)]
  exact Finset.sum_congr rfl fun l _ ↦ by rw [mapDomain_pathSimplex_cofaceSnd]

/-- Transfer along the zero family is zero. -/
lemma lfTransferFun_zero_family {I T : Type*} (c : I → R) :
    lfTransferFun (fun _ ↦ (0 : T →₀ ℤ)) c = 0 := by
  ext t; simp [lfTransferFun]

/-- The transfer of the zero chain is zero. -/
lemma lfTransferFun_zero_chain {I T : Type*} (Ψ : I → T →₀ ℤ) :
    lfTransferFun Ψ (0 : I → R) = 0 := by
  ext t; simp [lfTransferFun]

/-- `lfTensor 0 d = 0`. -/
lemma lfTensor_zero_left {S S' : Type*} (d : S' → R) : lfTensor (0 : S → R) d = 0 := by
  ext; simp [lfTensor]

/-- `lfTensor c 0 = 0`. -/
lemma lfTensor_zero_right {S S' : Type*} (c : S → R) : lfTensor c (0 : S' → R) = 0 := by
  ext; simp [lfTensor]

/-- `lfTensor` commutes with finite sums in the first variable. -/
lemma lfTensor_sum_left {S S' κ : Type*} (s : Finset κ) (f : κ → S → R) (d : S' → R) :
    lfTensor (∑ k ∈ s, f k) d = ∑ k ∈ s, lfTensor (f k) d := by
  ext p; simp [lfTensor, Finset.sum_apply, Finset.sum_mul]

/-- `lfTensor` commutes with finite sums in the second variable. -/
lemma lfTensor_sum_right {S S' κ : Type*} (s : Finset κ) (c : S → R) (f : κ → S' → R) :
    lfTensor c (∑ k ∈ s, f k) = ∑ k ∈ s, lfTensor c (f k) := by
  ext p; simp [lfTensor, Finset.sum_apply, Finset.mul_sum]

/-- `lfTensor (z • c) d = z • lfTensor c d` for an integer `z`. -/
lemma lfTensor_zsmul_left {S S' : Type*} (z : ℤ) (c : S → R) (d : S' → R) :
    lfTensor (z • c) d = z • lfTensor c d := by
  ext p; simp [lfTensor, mul_assoc]

/-- `lfTensor c (z • d) = z • lfTensor c d` for an integer `z`. -/
lemma lfTensor_zsmul_right {S S' : Type*} (z : ℤ) (c : S → R) (d : S' → R) :
    lfTensor c (z • d) = z • lfTensor c d := by
  ext p; simp [lfTensor, mul_left_comm]

/-- Transfer of a locally finite chain along a carrier-decreasing family commutes with integer
scalar multiplication of the chain. -/
lemma lfTransferFun_zsmul_chain {I T : Type*} {Z : Type*} [TopologicalSpace Z] {carI : I → Set Z}
    {carT : T → Set Z} (Ψ : I → T →₀ ℤ) (z : ℤ) (c : I → R) (hc : c ∈ lfChains R R carI)
    (hΨ : IsCarrierDecreasing carI carT Ψ) (hT : ∀ t, IsCompact (carT t) ∧ (carT t).Nonempty) :
    lfTransferFun Ψ (z • c) = z • lfTransferFun Ψ c := by
  simpa only [Int.cast_smul_eq_zsmul] using lfTransferFun_smul Ψ (z : R) c hc hΨ hT

/-- Transferring `c ⊗ d` along `(σ, τ) ↦ (∂ₖ σ) × τ` gives `(∂ₖ c) × d`. -/
lemma lfTransferFun_cross_δ_fst (n p q : ℕ) {c : Simp X (p + 1) → R} {d : Simp Y q → R}
    (hc : c ∈ lfChains R R (singularSimplexImage X (n := op ⦋p + 1⦌)))
    (hd : d ∈ lfChains R R (singularSimplexImage Y (n := op ⦋q⦌))) (k : Fin (p + 2)) :
    lfTransferFun (fun st : Simp X (p + 1) × Simp Y q ↦
        crossSimplex n ((TopCat.toSSet.obj X).δ k st.1) st.2) (lfTensor c d) =
      crossFun n p q (pushforwardFun ((TopCat.toSSet.obj X).δ k) c) d := by
  rw [crossFun, ← pushforwardFun_prodMap_id_lfTensor hc ((TopCat.toSSet.obj X).δ k)
    (fun σ ↦ singularSimplexImage_map_subset (SimplexCategory.δ k).op σ) compact_nonempty d,
    lfTransferFun_pushforwardFun (lfTensor_mem hc hd) (Prod.map ((TopCat.toSSet.obj X).δ k) id)
      (fun st ↦ Set.prod_mono (singularSimplexImage_map_subset (SimplexCategory.δ k).op st.1)
        subset_rfl) (isCarrierDecreasing_crossFamily n p q) compact_nonempty]
  rfl

/-- Transferring `c ⊗ d` along `(σ, τ) ↦ σ × (∂ₖ τ)` gives `c × (∂ₖ d)`. -/
lemma lfTransferFun_cross_δ_snd (n p q : ℕ) {c : Simp X p → R} {d : Simp Y (q + 1) → R}
    (hc : c ∈ lfChains R R (singularSimplexImage X (n := op ⦋p⦌)))
    (hd : d ∈ lfChains R R (singularSimplexImage Y (n := op ⦋q + 1⦌))) (k : Fin (q + 2)) :
    lfTransferFun (fun st : Simp X p × Simp Y (q + 1) ↦
        crossSimplex n st.1 ((TopCat.toSSet.obj Y).δ k st.2)) (lfTensor c d) =
      crossFun n p q c (pushforwardFun ((TopCat.toSSet.obj Y).δ k) d) := by
  rw [crossFun, ← pushforwardFun_prodMap_id_lfTensor' c hd ((TopCat.toSSet.obj Y).δ k)
    (fun τ ↦ singularSimplexImage_map_subset (SimplexCategory.δ k).op τ) compact_nonempty,
    lfTransferFun_pushforwardFun (lfTensor_mem hc hd) (Prod.map id ((TopCat.toSSet.obj Y).δ k))
      (fun st ↦ Set.prod_mono subset_rfl
        (singularSimplexImage_map_subset (SimplexCategory.δ k).op st.2))
      (isCarrierDecreasing_crossFamily n p q) compact_nonempty]
  rfl

/-- The push-forward of a locally finite chain along a face map is locally finite. -/
lemma pushforwardFun_δ_mem {Z : TopCat.{u}} {m : ℕ} (k : Fin (m + 2)) {c : Simp Z (m + 1) → R}
    (hc : c ∈ lfChains R R (singularSimplexImage Z (n := op ⦋m + 1⦌))) :
    pushforwardFun ((TopCat.toSSet.obj Z).δ k) c ∈
      lfChains R R (singularSimplexImage Z (n := op ⦋m⦌)) :=
  (pushforward (R := R) (M := R) ((TopCat.toSSet.obj Z).δ k)
    (singularSimplexImage_map_subset (SimplexCategory.δ k).op) compact_nonempty ⟨c, hc⟩).2

/-- The differential out of degree `0` is zero. -/
lemma d_zero_eq_zero (Z : TopCat.{u}) : (BM R Z).d 0 (0 - 1) = 0 :=
  (BM R Z).shape _ _ (by simp)

/-- The first-factor faces of the lattice paths contribute `∂c × d` to `∂(c × d)`. -/
lemma lfTransferFun_lowerFst (n p q : ℕ) (c : (BM R X).X p) (d : (BM R Y).X q) :
    lfTransferFun (fun st : Simp X p × Simp Y q ↦ Finsupp.mapDomain (pathSimplex n st.1 st.2)
        (∑ k ∈ Finset.range (p + 1), (-1 : ℤ) ^ k • lmap (cofaceFst k) (lowerFst n p q)))
        (lfTensor (coeff R c) (coeff R d)) =
      crossFun n (p - 1) q (coeff R (((BM R X).d p (p - 1)).hom c)) (coeff R d) := by
  rcases p with _ | p
  · simp only [lowerFst_zero, map_zero, smul_zero, Finset.sum_const_zero, Finsupp.mapDomain_zero]
    rw [lfTransferFun_zero_family, d_zero_eq_zero]
    simp only [ModuleCat.hom_zero, LinearMap.zero_apply, coeff_zero, crossFun, lfTensor_zero_left,
      lfTransferFun_zero_chain]
  · have he := lfTensor_mem (coeff_mem R c) (coeff_mem R d)
    have hΨ : ∀ k : Fin (p + 2), IsCarrierDecreasing (carP X Y (p + 1) q)
        (singularSimplexImage (TopCat.of (X × Y)) (n := op ⦋n⦌))
        (fun st ↦ crossSimplex n ((TopCat.toSSet.obj X).δ k st.1) st.2) := fun k st ρ h ↦
      (isCarrierDecreasing_crossFamily n p q (((TopCat.toSSet.obj X).δ k st.1), st.2) ρ h).trans
        (Set.prod_mono (singularSimplexImage_map_subset (SimplexCategory.δ k).op st.1) subset_rfl)
    simp_rw [mapDomain_pathSimplex_fst]
    rw [lfTransferFun_finset_sum (s := Finset.univ) (Ψ := fun (k : Fin (p + 2))
      (st : Simp X (p + 1) × Simp Y q) ↦
      (-1 : ℤ) ^ (k : ℕ) • crossSimplex n ((TopCat.toSSet.obj X).δ k st.1) st.2) _ he
      (fun k ↦ (hΨ k).zsmul _) compact_nonempty]
    change _ = crossFun n p q (coeff R (((BM R X).d (p + 1) p).hom c)) (coeff R d)
    rw [coeff_d, crossFun, lfTensor_sum_left,
      lfTransferFun_finset_sum_chain _ _ _ (fun k ↦ ?_) (isCarrierDecreasing_crossFamily n p q)
        compact_nonempty]
    · refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [lfTransferFun_zsmul _ _ _ he (hΨ k) compact_nonempty, lfTensor_zsmul_left,
        lfTransferFun_zsmul_chain _ _ _ (lfTensor_mem (pushforwardFun_δ_mem k (coeff_mem R c))
          (coeff_mem R d)) (isCarrierDecreasing_crossFamily n p q) compact_nonempty]
      congr 1
      exact lfTransferFun_cross_δ_fst n p q (coeff_mem R c) (coeff_mem R d) k
    · rw [lfTensor_zsmul_left]
      exact Submodule.smul_of_tower_mem _ _
        (lfTensor_mem (pushforwardFun_δ_mem k (coeff_mem R c)) (coeff_mem R d))

/-- The second-factor faces of the lattice paths contribute `c × ∂d` to `∂(c × d)`. -/
lemma lfTransferFun_lowerSnd (n p q : ℕ) (c : (BM R X).X p) (d : (BM R Y).X q) :
    lfTransferFun (fun st : Simp X p × Simp Y q ↦ Finsupp.mapDomain (pathSimplex n st.1 st.2)
        (∑ l ∈ Finset.range (q + 1), (-1 : ℤ) ^ l • lmap (cofaceSnd l) (lowerSnd n p q)))
        (lfTensor (coeff R c) (coeff R d)) =
      crossFun n p (q - 1) (coeff R c) (coeff R (((BM R Y).d q (q - 1)).hom d)) := by
  rcases q with _ | q
  · simp only [lowerSnd_zero, map_zero, smul_zero, Finset.sum_const_zero, Finsupp.mapDomain_zero]
    rw [lfTransferFun_zero_family, d_zero_eq_zero]
    simp only [ModuleCat.hom_zero, LinearMap.zero_apply, coeff_zero, crossFun, lfTensor_zero_right,
      lfTransferFun_zero_chain]
  · have he := lfTensor_mem (coeff_mem R c) (coeff_mem R d)
    have hΨ : ∀ k : Fin (q + 2), IsCarrierDecreasing (carP X Y p (q + 1))
        (singularSimplexImage (TopCat.of (X × Y)) (n := op ⦋n⦌))
        (fun st ↦ crossSimplex n st.1 ((TopCat.toSSet.obj Y).δ k st.2)) := fun k st ρ h ↦
      (isCarrierDecreasing_crossFamily n p q (st.1, ((TopCat.toSSet.obj Y).δ k st.2)) ρ h).trans
        (Set.prod_mono subset_rfl (singularSimplexImage_map_subset (SimplexCategory.δ k).op st.2))
    simp_rw [mapDomain_pathSimplex_snd]
    rw [lfTransferFun_finset_sum (s := Finset.univ) (Ψ := fun (k : Fin (q + 2))
      (st : Simp X p × Simp Y (q + 1)) ↦
      (-1 : ℤ) ^ (k : ℕ) • crossSimplex n st.1 ((TopCat.toSSet.obj Y).δ k st.2)) _ he
      (fun k ↦ (hΨ k).zsmul _) compact_nonempty]
    change _ = crossFun n p q (coeff R c) (coeff R (((BM R Y).d (q + 1) q).hom d))
    rw [coeff_d, crossFun, lfTensor_sum_right,
      lfTransferFun_finset_sum_chain _ _ _ (fun k ↦ ?_) (isCarrierDecreasing_crossFamily n p q)
        compact_nonempty]
    · refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [lfTransferFun_zsmul _ _ _ he (hΨ k) compact_nonempty, lfTensor_zsmul_right,
        lfTransferFun_zsmul_chain _ _ _ (lfTensor_mem (coeff_mem R c)
          (pushforwardFun_δ_mem k (coeff_mem R d))) (isCarrierDecreasing_crossFamily n p q)
          compact_nonempty]
      congr 1
      exact lfTransferFun_cross_δ_snd n p q (coeff_mem R c) (coeff_mem R d) k
    · rw [lfTensor_zsmul_right]
      exact Submodule.smul_of_tower_mem _ _
        (lfTensor_mem (coeff_mem R c) (pushforwardFun_δ_mem k (coeff_mem R d)))

/-- Every simplex in the image under `pathSimplex n σ τ` of a combination of lattice paths has
image contained in `σ(Δᵖ) × τ(Δ^q)`. -/
lemma isCarrierDecreasing_mapDomain_pathSimplex (n p q : ℕ)
    (x : Simp X p × Simp Y q → List (ℕ × ℕ) →₀ ℤ) :
    IsCarrierDecreasing (carP X Y p q) (singularSimplexImage (TopCat.of (X × Y)) (n := op ⦋n⦌))
      (fun st ↦ Finsupp.mapDomain (pathSimplex n st.1 st.2) (x st)) := fun st ρ h ↦ by
  classical
  have hρ : ρ ∈ (x st).support.image (pathSimplex n st.1 st.2) :=
    Finsupp.mapDomain_support (Finsupp.mem_support_iff.2 h)
  obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hρ
  rintro _ ⟨t, rfl⟩
  change toC (pathSimplex n st.1 st.2 l) t ∈ _
  rw [toC_pathSimplex]
  exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩

/-- The Leibniz rule for the cross product of locally finite chains:
`∂(c × d) = ∂c × d + (-1)^p c × ∂d`. -/
theorem d_crossChain (n p q : ℕ) (c : (BM R X).X p) (d : (BM R Y).X q) :
    ((BM R (TopCat.of (X × Y))).d (n + 1) n).hom (crossChain R (n + 1) p q c d) =
      crossChain R n (p - 1) q (((BM R X).d p (p - 1)).hom c) d +
        (-1 : ℤ) ^ p • crossChain R n p (q - 1) c (((BM R Y).d q (q - 1)).hom d) := by
  apply coeff_injective R
  have he := lfTensor_mem (coeff_mem R c) (coeff_mem R d)
  rw [coeff_d_crossChain, coeff_add, coeff_zsmul, coeff_crossChain, coeff_crossChain]
  simp_rw [Finsupp.mapDomain_add, Finsupp.mapDomain_smul]
  rw [lfTransferFun_add_family _ _ _ he (isCarrierDecreasing_mapDomain_pathSimplex n p q _)
      ((isCarrierDecreasing_mapDomain_pathSimplex n p q _).zsmul _) compact_nonempty,
    lfTransferFun_zsmul _ _ _ he (isCarrierDecreasing_mapDomain_pathSimplex n p q _)
      compact_nonempty, lfTransferFun_lowerFst, lfTransferFun_lowerSnd]

/-- `(c + c') × d = c × d + c' × d`. -/
lemma crossChain_add_left (n p q : ℕ) (c c' : (BM R X).X p) (d : (BM R Y).X q) :
    crossChain R n p q (c + c') d = crossChain R n p q c d + crossChain R n p q c' d := by
  apply coeff_injective R
  rw [coeff_add, coeff_crossChain, coeff_crossChain, coeff_crossChain, coeff_add, crossFun,
    lfTensor_add_left, lfTransferFun_add _ _ _ (lfTensor_mem (coeff_mem R c) (coeff_mem R d))
      (lfTensor_mem (coeff_mem R c') (coeff_mem R d)) (isCarrierDecreasing_crossFamily n p q)
      compact_nonempty]
  rfl

/-- `c × (d + d') = c × d + c × d'`. -/
lemma crossChain_add_right (n p q : ℕ) (c : (BM R X).X p) (d d' : (BM R Y).X q) :
    crossChain R n p q c (d + d') = crossChain R n p q c d + crossChain R n p q c d' := by
  apply coeff_injective R
  rw [coeff_add, coeff_crossChain, coeff_crossChain, coeff_crossChain, coeff_add, crossFun,
    lfTensor_add_right, lfTransferFun_add _ _ _ (lfTensor_mem (coeff_mem R c) (coeff_mem R d))
      (lfTensor_mem (coeff_mem R c) (coeff_mem R d')) (isCarrierDecreasing_crossFamily n p q)
      compact_nonempty]
  rfl

/-- `(r • c) × d = r • (c × d)`. -/
lemma crossChain_smul_left (n p q : ℕ) (r : R) (c : (BM R X).X p) (d : (BM R Y).X q) :
    crossChain R n p q (r • c) d = r • crossChain R n p q c d := by
  apply coeff_injective R
  rw [coeff_smul, coeff_crossChain, coeff_crossChain, coeff_smul, crossFun, lfTensor_smul_left,
    lfTransferFun_smul _ _ _ (lfTensor_mem (coeff_mem R c) (coeff_mem R d))
      (isCarrierDecreasing_crossFamily n p q) compact_nonempty]
  rfl

/-- `c × (r • d) = r • (c × d)`. -/
lemma crossChain_smul_right (n p q : ℕ) (r : R) (c : (BM R X).X p) (d : (BM R Y).X q) :
    crossChain R n p q c (r • d) = r • crossChain R n p q c d := by
  apply coeff_injective R
  rw [coeff_smul, coeff_crossChain, coeff_crossChain, coeff_smul, crossFun, lfTensor_smul_right,
    lfTransferFun_smul _ _ _ (lfTensor_mem (coeff_mem R c) (coeff_mem R d))
      (isCarrierDecreasing_crossFamily n p q) compact_nonempty]
  rfl

variable (R) in
/-- The cross product of locally finite chains, as a bilinear map. -/
def crossChainₗ (n p q : ℕ) :
    (BM R X).X p →ₗ[R] (BM R Y).X q →ₗ[R] (BM R (TopCat.of (X × Y))).X n :=
  LinearMap.mk₂ R (crossChain R n p q) (crossChain_add_left n p q) (crossChain_smul_left n p q)
    (crossChain_add_right n p q) (crossChain_smul_right n p q)

/-- The bilinear map `crossChainₗ` sends `(c, d)` to `c × d`. -/
@[simp] lemma crossChainₗ_apply (n p q : ℕ) (c : (BM R X).X p) (d : (BM R Y).X q) :
    crossChainₗ R n p q c d = crossChain R n p q c d :=
  rfl

/-- `0 × d = 0`. -/
@[simp] lemma crossChain_zero_left (n p q : ℕ) (d : (BM R Y).X q) :
    crossChain R n p q (0 : (BM R X).X p) d = 0 := by
  rw [← crossChainₗ_apply, map_zero, LinearMap.zero_apply]

/-- `c × 0 = 0`. -/
@[simp] lemma crossChain_zero_right (n p q : ℕ) (c : (BM R X).X p) :
    crossChain R n p q c (0 : (BM R Y).X q) = 0 := by
  rw [← crossChainₗ_apply, map_zero]

end Cross

section Homology

variable {R}

/-- The cycles of degree `n`. -/
abbrev Cyc (X : TopCat.{u}) (n : ℕ) : Submodule R ((BM R X).X n) :=
  LinearMap.ker ((BM R X).sc n).g.hom

/-- The explicit homology module of degree `n`: cycles modulo boundaries. -/
abbrev HomQ (X : TopCat.{u}) (n : ℕ) : ModuleCat.{u} R :=
  ((BM R X).sc n).moduleCatLeftHomologyData.H

/-- A chain of degree `n` is a cycle if and only if its boundary vanishes. -/
lemma mem_cyc_iff {n : ℕ} (x : (BM R X).X n) :
    x ∈ Cyc (R := R) X n ↔ ((BM R X).d n (n - 1)).hom x = 0 := by
  change ((BM R X).d n ((ComplexShape.down ℕ).next n)).hom x = 0 ↔ _
  rw [show (ComplexShape.down ℕ).next n = n - 1 by cases n <;> simp]

/-- A cycle `z` with `z = ∂u` for some chain `u` of degree `n + 1` is a boundary. -/
lemma mem_bdry_of {n : ℕ} (z : Cyc (R := R) X n) (u : (BM R X).X (n + 1))
    (hu : ((BM R X).d (n + 1) n).hom u = z.1) :
    z ∈ LinearMap.range ((BM R X).sc n).moduleCatToCycles := by
  obtain ⟨u', hu'⟩ : ∃ u' : (BM R X).X ((ComplexShape.down ℕ).prev n),
      ((BM R X).d ((ComplexShape.down ℕ).prev n) n).hom u' = z.1 := by
    rw [ChainComplex.prev ℕ n]
    exact ⟨u, hu⟩
  exact ⟨u', Subtype.ext hu'⟩

/-- The cross product of two cycles is a cycle. -/
lemma crossChain_mem_cyc (p q : ℕ) (z : Cyc (R := R) X p) (w : Cyc (R := R) Y q) :
    crossChain R (p + q) p q z.1 w.1 ∈ Cyc (R := R) (TopCat.of (X × Y)) (p + q) := by
  rw [mem_cyc_iff]
  have hz := (mem_cyc_iff z.1).1 z.2
  have hw := (mem_cyc_iff w.1).1 w.2
  generalize hm : p + q = m
  rcases m with _ | m
  · rw [show (0 : ℕ) - 1 = 0 from rfl, (BM R _).shape 0 0 (by simp)]
    rfl
  · rw [show m + 1 - 1 = m from rfl, d_crossChain, hz, hw]
    simp

/-- For a cycle `w`, `∂(u × w) = ∂u × w`. -/
lemma d_crossChain_cyc_right (p q : ℕ) (u : (BM R X).X (p + 1)) (w : Cyc (R := R) Y q) :
    ((BM R (TopCat.of (X × Y))).d (p + q + 1) (p + q)).hom
        (crossChain R (p + q + 1) (p + 1) q u w.1) =
      crossChain R (p + q) p q (((BM R X).d (p + 1) p).hom u) w.1 := by
  rw [d_crossChain, (mem_cyc_iff w.1).1 w.2, crossChain_zero_right, smul_zero, add_zero]
  rfl

/-- For a cycle `z` of degree `p`, `∂((-1)^p z × v) = z × ∂v`. -/
lemma d_zsmul_crossChain_cyc_left (p q : ℕ) (z : Cyc (R := R) X p) (v : (BM R Y).X (q + 1)) :
    ((BM R (TopCat.of (X × Y))).d (p + q + 1) (p + q)).hom
        ((-1 : ℤ) ^ p • crossChain R (p + q + 1) p (q + 1) z.1 v) =
      crossChain R (p + q) p q z.1 (((BM R Y).d (q + 1) q).hom v) := by
  rw [map_zsmul, d_crossChain, (mem_cyc_iff z.1).1 z.2, crossChain_zero_left, zero_add,
    smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]
  rfl

/-- A boundary of degree `n` is `∂u` for some chain `u` of degree `n + 1`. -/
lemma exists_of_mem_bdry {n : ℕ} {z : Cyc (R := R) X n}
    (hz : z ∈ LinearMap.range ((BM R X).sc n).moduleCatToCycles) :
    ∃ u : (BM R X).X (n + 1), ((BM R X).d (n + 1) n).hom u = z.1 := by
  obtain ⟨u, hu⟩ := hz
  have hu : ((BM R X).d ((ComplexShape.down ℕ).prev n) n).hom u = z.1 := congrArg Subtype.val hu
  have key : ∀ j (hj : (ComplexShape.down ℕ).prev n = j) (u : (BM R X).X j),
      ((BM R X).d j n).hom u = z.1 → ∃ u : (BM R X).X (n + 1),
        ((BM R X).d (n + 1) n).hom u = z.1 := by
    rintro j hj u hu
    rw [ChainComplex.prev] at hj
    subst hj
    exact ⟨u, hu⟩
  exact key _ rfl u hu

variable (R) in
/-- The cross product of cycles. -/
def crossCyc (X Y : TopCat.{u}) (p q : ℕ) :
    Cyc (R := R) X p →ₗ[R] Cyc (R := R) Y q →ₗ[R] Cyc (R := R) (TopCat.of (X × Y)) (p + q) :=
  LinearMap.mk₂ R (fun z w ↦ ⟨crossChain R (p + q) p q z.1 w.1, crossChain_mem_cyc p q z w⟩)
    (fun _ _ _ ↦ Subtype.ext (crossChain_add_left _ _ _ _ _ _))
    (fun _ _ _ ↦ Subtype.ext (crossChain_smul_left _ _ _ _ _ _))
    (fun _ _ _ ↦ Subtype.ext (crossChain_add_right _ _ _ _ _ _))
    (fun _ _ _ ↦ Subtype.ext (crossChain_smul_right _ _ _ _ _ _))

/-- The cross product of cycles followed by the class map. -/
def crossCycQ (p q : ℕ) :
    Cyc (R := R) X p →ₗ[R] Cyc (R := R) Y q →ₗ[R] HomQ (R := R) (TopCat.of (X × Y)) (p + q) :=
  (crossCyc R X Y p q).compr₂
    (LinearMap.range ((BM R (TopCat.of (X × Y))).sc (p + q)).moduleCatToCycles).mkQ

/-- The class of `z × w` vanishes when `z` is a boundary. -/
lemma crossCycQ_bdry_left (p q : ℕ) :
    LinearMap.range ((BM R X).sc p).moduleCatToCycles ≤ LinearMap.ker (crossCycQ (Y := Y) p q) := by
  intro z hz
  obtain ⟨u, hu⟩ := exists_of_mem_bdry hz
  change crossCycQ p q z = 0
  ext w
  refine (Submodule.Quotient.mk_eq_zero _).2
    (mem_bdry_of (crossCyc R X Y p q z w) (crossChain R (p + q + 1) (p + 1) q u w.1) ?_)
  rw [d_crossChain_cyc_right, hu]
  rfl

/-- The cross product of a homology class and a cycle: `[z] × w = [z × w]`. -/
def crossHomQ₁ (p q : ℕ) :
    HomQ (R := R) X p →ₗ[R] Cyc (R := R) Y q →ₗ[R] HomQ (R := R) (TopCat.of (X × Y)) (p + q) :=
  (LinearMap.range ((BM R X).sc p).moduleCatToCycles).liftQ (crossCycQ p q)
    (crossCycQ_bdry_left p q)

/-- The class `[z] × w` vanishes when `w` is a boundary. -/
lemma crossHomQ₁_bdry_right (p q : ℕ) :
    LinearMap.range ((BM R Y).sc q).moduleCatToCycles ≤
      LinearMap.ker (crossHomQ₁ (X := X) (R := R) p q).flip := by
  intro w hw
  obtain ⟨v, hv⟩ := exists_of_mem_bdry hw
  change (crossHomQ₁ p q).flip w = 0
  refine Submodule.linearMap_qext _ (LinearMap.ext fun z ↦ ?_)
  refine (Submodule.Quotient.mk_eq_zero _).2
    (mem_bdry_of (crossCyc R X Y p q z w)
      ((-1 : ℤ) ^ p • crossChain R (p + q + 1) p (q + 1) z.1 v) ?_)
  refine (d_zsmul_crossChain_cyc_left p q z v).trans ?_
  rw [hv]
  rfl

variable (R) in
/-- The cross product on homology, cycles modulo boundaries:
`[z] × [w] = [z × w]`. -/
def crossHomQ (X Y : TopCat.{u}) (p q : ℕ) :
    HomQ (R := R) X p →ₗ[R] HomQ (R := R) Y q →ₗ[R] HomQ (R := R) (TopCat.of (X × Y)) (p + q) :=
  ((LinearMap.range ((BM R Y).sc q).moduleCatToCycles).liftQ (crossHomQ₁ p q).flip
    (crossHomQ₁_bdry_right p q)).flip

/-- The cross product of the classes of cycles `z` and `w` is the class of `z × w`. -/
lemma crossHomQ_mk (p q : ℕ) (z : Cyc (R := R) X p) (w : Cyc (R := R) Y q) :
    crossHomQ R X Y p q (Submodule.Quotient.mk z) (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk ⟨crossChain R (p + q) p q z.1 w.1, crossChain_mem_cyc p q z w⟩ :=
  rfl

end Homology

section BorelMoore

/-- Borel–Moore homology in degree `n : ℕ` is cycles modulo boundaries. -/
def homologyEquiv (X : TopCat.{u}) (n : ℕ) :
    borelMooreHomology R (ModuleCat.of R R) X n ≃ₗ[R] HomQ (R := R) X n :=
  (borelMooreHomologyIsoOfNat R (ModuleCat.of R R) X n ≪≫
    ((BM R X).sc n).moduleCatHomologyIso).toLinearEquiv

/-- Transport of Borel–Moore homology along an equality of degrees. -/
def congrDegree (X : TopCat.{u}) {i i' : ℤ} (h : i = i') :
    borelMooreHomology R (ModuleCat.of R R) X i ≃ₗ[R]
      borelMooreHomology R (ModuleCat.of R R) X i' := by
  subst h
  exact LinearEquiv.refl R _

/-- Transport along `i = i` is the identity. -/
lemma congrDegree_self (X : TopCat.{u}) {i : ℤ} (h : i = i) :
    congrDegree R X h = LinearEquiv.refl R _ :=
  rfl

/-- The inverse of transport along `i = i'` is transport along `i' = i`. -/
lemma congrDegree_symm (X : TopCat.{u}) {i i' : ℤ} (h : i = i') :
    (congrDegree R X h).symm = congrDegree R X h.symm := by
  subst h
  rfl

/-- The exterior product as a bilinear map `H_i X × H_j Y → H_{i+j}(X × Y)`; zero in negative
degrees, where the groups vanish. -/
def exteriorProductBilin (X Y : TopCat.{u}) (i j : ℤ) :
    borelMooreHomology R (ModuleCat.of R R) X i →ₗ[R]
      borelMooreHomology R (ModuleCat.of R R) Y j →ₗ[R]
        borelMooreHomology R (ModuleCat.of R R) (TopCat.of (X × Y)) (i + j) :=
  if h : 0 ≤ i ∧ 0 ≤ j then
    ((crossHomQ R X Y i.toNat j.toNat).compl₁₂
        ((congrDegree R X (Int.toNat_of_nonneg h.1).symm).trans
          (homologyEquiv R X i.toNat)).toLinearMap
        ((congrDegree R Y (Int.toNat_of_nonneg h.2).symm).trans
          (homologyEquiv R Y j.toNat)).toLinearMap).compr₂
      ((congrDegree R (TopCat.of (X × Y))
          (by rw [Nat.cast_add, Int.toNat_of_nonneg h.1, Int.toNat_of_nonneg h.2])).trans
        (homologyEquiv R (TopCat.of (X × Y)) (i.toNat + j.toNat))).symm.toLinearMap
  else 0

/-- In degrees `p, q : ℕ`, through the identification of Borel–Moore homology with cycles
modulo boundaries, the exterior product is `MMP.BorelMooreCross.crossHomQ`:
`[z] × [w] = [z × w]` (`MMP.BorelMooreCross.crossHomQ_mk`). -/
lemma exteriorProductBilin_natCast (X Y : TopCat.{u}) (p q : ℕ) (x : HomQ (R := R) X p)
    (y : HomQ (R := R) Y q) :
    exteriorProductBilin R X Y p q ((homologyEquiv R X p).symm x) ((homologyEquiv R Y q).symm y) =
      congrDegree R (TopCat.of (X × Y)) (Nat.cast_add p q).symm
        ((homologyEquiv R (TopCat.of (X × Y)) (p + q)).symm (crossHomQ R X Y p q x y)) := by
  have h : (0 : ℤ) ≤ p ∧ (0 : ℤ) ≤ q := ⟨by positivity, by positivity⟩
  simp only [exteriorProductBilin, dif_pos h, Int.toNat_natCast, LinearMap.compr₂_apply,
    LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply, congrDegree_self,
    LinearEquiv.refl_apply, LinearEquiv.symm_trans_apply, congrDegree_symm]
  rw [(homologyEquiv R X p).apply_symm_apply, (homologyEquiv R Y q).apply_symm_apply]
  rfl

/-- The exterior product vanishes in negative degrees. -/
lemma exteriorProductBilin_of_neg (X Y : TopCat.{u}) {i j : ℤ} (h : i < 0 ∨ j < 0) :
    exteriorProductBilin R X Y i j = 0 := by
  rw [exteriorProductBilin, dif_neg]
  omega

end BorelMoore

end BorelMooreCross

namespace borelMooreHomology

open BorelMooreCross TensorProduct

variable (R : Type u) [CommRing R]

/-- The *exterior product* `× : H_i X ⊗ H_j Y → H_{i+j}(X × Y)` of Borel–Moore homology
(Fulton, §19.1; Borel–Moore §6), induced by the cross product of locally finite chains,
`(∑ a_σ σ) × (∑ b_τ τ) = ∑ a_σ b_τ (σ × τ)` with `σ × τ` the Eilenberg–Zilber shuffle product of
singular simplices. -/
def exteriorProduct (X Y : TopCat.{u}) (i j : ℤ) :
    borelMooreHomology R (ModuleCat.of R R) X i ⊗[R] borelMooreHomology R (ModuleCat.of R R) Y j
      →ₗ[R] borelMooreHomology R (ModuleCat.of R R) (TopCat.of (X × Y)) (i + j) :=
  TensorProduct.lift (exteriorProductBilin R X Y i j)

/-- The exterior product of `x ⊗ y` is `exteriorProductBilin R X Y i j x y`. -/
lemma exteriorProduct_tmul (X Y : TopCat.{u}) (i j : ℤ)
    (x : borelMooreHomology R (ModuleCat.of R R) X i)
    (y : borelMooreHomology R (ModuleCat.of R R) Y j) :
    exteriorProduct R X Y i j (x ⊗ₜ y) = exteriorProductBilin R X Y i j x y :=
  TensorProduct.lift.tmul _ _

end borelMooreHomology

end MMP
