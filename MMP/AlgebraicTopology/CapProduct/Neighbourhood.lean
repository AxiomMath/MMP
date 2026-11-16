module

public import MMP.AlgebraicTopology.BorelMoore.RestrictionFunctorial
public import MMP.AlgebraicTopology.SingularHomology.Excision.SmallChains
public import MMP.AlgebraicTopology.CapProduct.Basic
public import MMP.AlgebraicTopology.BorelMoore.DisjointUnion

/-!
# The cap product with values in a closed neighbourhood (Fulton, §19.1)

Let `X` be a closed subset of a space `Y`. Fulton's cap product
`∩ : H^j(Y, Y - X) ⊗ H_k Y → H_{k-j} X` is built in two steps on locally finite chains.

*Small locally finite chains.* Let `𝒰` be a family of open subsets of `Y`. Hatcher's chain map
`ρ = 1 - ∂ D - D ∂` of the theorem of small chains sends a singular simplex `σ` to a finite chain
of simplices inside the image of `σ`, and so does its homotopy `D`. Hence both act on locally
finite chains, `c = ∑ a_σ σ ↦ ∑ a_σ ρ σ`: near a point only finitely many simplices of `c`
matter, and each contributes finitely many simplices. The identities `∂ ρ = ρ ∂` and
`1 - ρ = ∂ D + D ∂` hold simplex by simplex, hence for locally finite chains. So `ρ` is a chain
map, chain homotopic to the identity, and when `𝒰` covers `Y` every simplex of `ρ c` lies in a
member of `𝒰`.

*Support of the cap product.* Let `N` be a closed neighbourhood of `X`. Take `𝒰 = {Y - X, int N}`.
For a cocycle `φ` vanishing on the simplices of `Y - X` and a locally finite cycle `z`, a simplex
of `ρ z` contributes to `φ ∩ ρ z` only if `φ` does not vanish on its back face. Such a simplex
does not lie in `Y - X`, so it lies in `int N`. Hence `φ ∩ ρ z` is a cycle of `Y` supported in
`N`, that is, a cycle of `N`, and its class only depends on the classes of `φ` and `z`. This gives
the cap product `H^j(Y, Y - X) ⊗ H_k Y → H_{k-j} N`, and, along a proper map `f : N → Z`, a cap
product with values in `H_{k-j} Z`. For a proper retraction `f : N → X` it lands in `H_{k-j} X`.

## Main definitions

* `MMP.borelMooreHomology.smallChainMapLF`: `ρ` on locally finite chains.
* `MMP.borelMooreHomology.smallChainMapLFHomotopy`: the chain homotopy from the
  identity to `ρ`.
* `MMP.borelMooreHomology.subsetRestrictMap`: the restriction to a subset `N` of
  locally finite chains, inverse to the push-forward on chains supported in `N`.
* `MMP.BorelMooreCap.capHomQNbhd`: the cap product on cocycles modulo coboundaries
  and cycles modulo boundaries, with values in a closed neighbourhood.
* `MMP.borelMooreHomology.capProductNbhd`:
  `∩ : H^j(Y, Y - X) ⊗ H_k Y → H_{k-j} N`.
* `MMP.borelMooreHomology.capProductAlong`: its push-forward along a proper map.

## Main results

* `MMP.borelMooreHomology.homologyMap_smallChainMapLF`: `ρ` induces the identity
  on Borel–Moore homology.
* `MMP.borelMooreHomology.smallChainMapLF_small`: the theorem of small chains for
  locally finite chains.
* `MMP.BorelMooreCap.singularSimplexImage_subset_of_coeff_capChain_ne_zero`: the
  support of the cap product.
* `MMP.borelMooreHomology.d_subsetRestrictMap`: restriction to a closed subset
  commutes with the boundary on chains supported in it.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* W. Fulton, R. MacPherson, *Categorical framework for the study of singular spaces*, 3.1.7.
* [A. Hatcher, *Algebraic Topology*][hatcher2002], §2.1, Prop. 2.21, and §3.3.
* [A. Borel, J. C. Moore, *Homology theory for locally compact spaces*][borelmoore1960], §3.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicTopology Opposite Topology Set Simplicial Finsupp

universe u

namespace MMP

namespace SingularChain

variable {R : Type*} [CommRing R] {Y : Type*} [TopologicalSpace Y]

/-- Iterated barycentric subdivision sends chains inside `A` to chains inside `A`. -/
lemma subdiv_pow_mem_inside {n : ℕ} {A : Set Y} (i : ℕ) {c : Chain R Y n}
    (hc : c ∈ inside R n A) : (subdiv R n ^ i) c ∈ inside R n A :=
  Module.End.pow_apply_mem_of_forall_mem i (fun _ h ↦ subdiv_mem_inside h) _ hc

/-- The subdivision homotopy up to stage `m` sends chains inside `A` to chains inside `A`. -/
lemma homotopyUpTo_mem_inside {m n : ℕ} {A : Set Y} {c : Chain R Y n}
    (hc : c ∈ inside R n A) : homotopyUpTo R m n c ∈ inside R (n + 1) A := by
  simp only [homotopyUpTo, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun i _ ↦ subdivHomotopy_mem_inside (subdiv_pow_mem_inside i hc)

/-- Hatcher's homotopy `D σ` of a simplex `σ` lies inside the image of `σ`. -/
lemma smallHomotopy_single_mem_inside (𝒰 : Set (Set Y)) (n : ℕ) (σ : Simplex Y n) :
    smallHomotopy R 𝒰 n (single σ 1) ∈ inside R (n + 1) (range σ) := by
  rw [smallHomotopy_single]
  exact homotopyUpTo_mem_inside (single_mem_supported R _ (show range σ ⊆ range σ from subset_rfl))

/-- Hatcher's homotopy `D` sends chains inside `A` to chains inside `A`. -/
lemma smallHomotopy_mem_inside (𝒰 : Set (Set Y)) {n : ℕ} {A : Set Y} {c : Chain R Y n}
    (hc : c ∈ inside R n A) : smallHomotopy R 𝒰 n c ∈ inside R (n + 1) A :=
  VertexChain.mem_of_mem_supported (smallHomotopy R 𝒰 n) (inside R (n + 1) A) (fun σ hσ ↦
    supported_mono (s := Set.ofPred fun τ : Simplex Y (n + 1) ↦ range τ ⊆ range σ)
      (fun τ (hτ : range τ ⊆ range σ) ↦ show range τ ⊆ A from hτ.trans hσ)
      (smallHomotopy_single_mem_inside 𝒰 n σ)) hc

/-- Hatcher's chain map `ρ σ` of a simplex `σ` lies inside the image of `σ`. -/
lemma smallChainMap_single_mem_inside (𝒰 : Set (Set Y)) (n : ℕ) (σ : Simplex Y n) :
    smallChainMap R 𝒰 n (single σ 1) ∈ inside R n (range σ) := by
  have hσ : single σ (1 : R) ∈ inside R n (range σ) :=
    single_mem_supported R _ (show range σ ⊆ range σ from subset_rfl)
  cases n with
  | zero =>
    rw [smallChainMap_zero]
    exact Submodule.sub_mem _ hσ (bd_mem_inside (smallHomotopy_mem_inside 𝒰 hσ))
  | succ n =>
    rw [smallChainMap_succ]
    exact Submodule.sub_mem _ (Submodule.sub_mem _ hσ
      (bd_mem_inside (smallHomotopy_mem_inside 𝒰 hσ)))
      (smallHomotopy_mem_inside 𝒰 (bd_mem_inside hσ))

/-- A simplex with nonzero coefficient in a chain inside `A` has its image in `A`. -/
lemma range_subset_of_mem_inside {n : ℕ} {A : Set Y} {c : Chain R Y n} (hc : c ∈ inside R n A)
    {τ : Simplex Y n} (hτ : c τ ≠ 0) : range τ ⊆ A :=
  hc (Finsupp.mem_support_iff.2 hτ)

end SingularChain

namespace borelMooreHomology

open SingularChain LocallyFiniteChain

section kernel

variable {Y : TopCat.{u}}

/-- The integer kernel of a family `f` of finite singular chains indexed by singular simplices:
the coefficient of `τ` in `f σ`. -/
def chainFamilyKernel {n m : ℕ} (f : Simplex Y n → Chain ℤ Y m)
    (σ : (TopCat.toSSet.obj Y).obj (op ⦋n⦌)) (τ : (TopCat.toSSet.obj Y).obj (op ⦋m⦌)) : ℤ :=
  f (SingularCochain.simplexEquiv Y n σ) (SingularCochain.simplexEquiv Y m τ)

/-- A family of finite chains with `f σ` inside the image of `σ` is an admissible kernel. -/
lemma isAdmissibleKernel_chainFamilyKernel {n m : ℕ} {f : Simplex Y n → Chain ℤ Y m}
    (hf : ∀ σ : Simplex Y n, f σ ∈ inside ℤ m (range σ)) :
    IsAdmissibleKernel (id : Y → Y) (singularSimplexImage Y (n := op ⦋n⦌))
      (singularSimplexImage Y (n := op ⦋m⦌)) (chainFamilyKernel f) where
  continuous := continuous_id
  image_subset σ τ h := by
    rw [image_id, ← range_simplexEquiv, ← range_simplexEquiv]
    exact range_subset_of_mem_inside (hf _) h
  isLocallyFiniteSet σ x := by
    refine ⟨univ, Filter.univ_mem, ?_⟩
    refine ((f (SingularCochain.simplexEquiv Y n σ)).support.finite_toSet.preimage
      (SingularCochain.simplexEquiv Y m).injective.injOn).subset ?_
    rintro τ ⟨hτ, -⟩
    exact Finsupp.mem_support_iff.2 hτ
  compact_nonempty τ := ⟨isCompact_singularSimplexImage τ, nonempty_singularSimplexImage τ⟩

/-- A simplex `τ` with `chainFamilyKernel f σ τ ≠ 0` lies in the image of `σ`. -/
lemma singularSimplexImage_subset_of_chainFamilyKernel_ne_zero {n m : ℕ}
    {f : Simplex Y n → Chain ℤ Y m} (hf : ∀ σ : Simplex Y n, f σ ∈ inside ℤ m (range σ))
    {σ : (TopCat.toSSet.obj Y).obj (op ⦋n⦌)} {τ : (TopCat.toSSet.obj Y).obj (op ⦋m⦌)}
    (h : chainFamilyKernel f σ τ ≠ 0) :
    singularSimplexImage Y τ ⊆ singularSimplexImage Y σ := by
  rw [← range_simplexEquiv, ← range_simplexEquiv]
  exact range_subset_of_mem_inside (hf _) h

open Classical in
/-- The finite sum over the simplices `ω` with `i`-th face `τ` of the coefficients of a finite
chain `e`, read through `TopCat.toSSetObjEquiv`. -/
lemma finsum_ite_δ_eq {n : ℕ} (i : Fin (n + 2)) (e : Chain ℤ Y (n + 1))
    (τ : (TopCat.toSSet.obj Y).obj (op ⦋n⦌)) :
    ∑ᶠ ω, (if (TopCat.toSSet.obj Y).δ i ω = τ then e (SingularCochain.simplexEquiv Y (n + 1) ω) else 0) =
      ∑ ω' ∈ e.support, if ω'.comp (face n i) = SingularCochain.simplexEquiv Y n τ then e ω' else 0 := by
  have hiff : ∀ ω, (TopCat.toSSet.obj Y).δ i ω = τ ↔
      (SingularCochain.simplexEquiv Y (n + 1) ω).comp (face n i) = SingularCochain.simplexEquiv Y n τ := by
    intro ω
    rw [← toSSetObjEquiv_δ]
    exact (SingularCochain.simplexEquiv Y n).injective.eq_iff.symm
  have : (fun ω ↦ if (TopCat.toSSet.obj Y).δ i ω = τ then e (SingularCochain.simplexEquiv Y (n + 1) ω) else 0) =
      (fun ω' : Simplex Y (n + 1) ↦
        if ω'.comp (face n i) = SingularCochain.simplexEquiv Y n τ then e ω' else 0) ∘
        (SingularCochain.simplexEquiv Y (n + 1)) := by
    funext ω
    simp only [Function.comp_apply]
    by_cases h : (TopCat.toSSet.obj Y).δ i ω = τ
    · rw [ite_eq_left h, ite_eq_left ((hiff ω).1 h)]
    · rw [ite_eq_right h, ite_eq_right (fun h' ↦ h ((hiff ω).2 h'))]
  rw [this]
  refine (finsum_comp_equiv (M := ℤ) (SingularCochain.simplexEquiv Y (n + 1))
    (f := fun ω' : Simplex Y (n + 1) ↦
      if ω'.comp (face n i) = SingularCochain.simplexEquiv Y n τ then e ω' else 0)).trans ?_
  refine finsum_eq_sum_of_support_subset _ fun ω' hω' ↦ ?_
  rw [Function.mem_support] at hω'
  rw [Finset.mem_coe, Finsupp.mem_support_iff]
  intro h0
  apply hω'
  split_ifs <;> simp [h0]

open Classical in
/-- A family of finite chains commuting with the boundary on single simplices satisfies the
compatibility of `MMP.LocallyFiniteChain.kernelFun_dFun`. -/
lemma chainFamilyKernel_comm {n : ℕ} (f₁ : Simplex Y (n + 1) → Chain ℤ Y (n + 1))
    (f₀ : Simplex Y n → Chain ℤ Y n)
    (hf : ∀ σ, bd ℤ n (f₁ σ) = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • f₀ (σ.comp (face n i)))
    (σ : (TopCat.toSSet.obj Y).obj (op ⦋n + 1⦌)) (τ : (TopCat.toSSet.obj Y).obj (op ⦋n⦌)) :
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) * ∑ᶠ τ', (if (TopCat.toSSet.obj Y).δ i τ' = τ
      then chainFamilyKernel f₁ σ τ' else 0) =
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) *
      chainFamilyKernel f₀ ((TopCat.toSSet.obj Y).δ i σ) τ := by
  have h := congrArg (fun e : Chain ℤ Y n ↦ e (SingularCochain.simplexEquiv Y n τ)) (hf (SingularCochain.simplexEquiv Y (n + 1) σ))
  simp only [bd_apply, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul] at h
  simp only [chainFamilyKernel, finsum_ite_δ_eq, toSSetObjEquiv_δ]
  exact h

/-- If the image of `τ` lies in the image of `σ`, the two images meet. -/
lemma inter_nonempty_of_singularSimplexImage_subset {n m : ℕ}
    {σ : (TopCat.toSSet.obj Y).obj (op ⦋n⦌)} {τ : (TopCat.toSSet.obj Y).obj (op ⦋m⦌)}
    (h : singularSimplexImage Y τ ⊆ singularSimplexImage Y σ) :
    (singularSimplexImage Y σ ∩ singularSimplexImage Y τ).Nonempty :=
  (nonempty_singularSimplexImage τ).mono (subset_inter h subset_rfl)

/-- The image of the `i`-th face of `σ` lies in the image of `σ`. -/
lemma singularSimplexImage_δ_subset {n : ℕ} (i : Fin (n + 2))
    (σ : (TopCat.toSSet.obj Y).obj (op ⦋n + 1⦌)) :
    singularSimplexImage Y ((TopCat.toSSet.obj Y).δ i σ) ⊆ singularSimplexImage Y σ :=
  singularSimplexImage_map_subset _ σ

/-- The kernel of the identity: `chainFamilyKernel (fun σ ↦ single σ 1)` transforms every chain
to itself. -/
lemma kernelFun_chainFamilyKernel_single {n : ℕ} {M : Type*} [AddCommGroup M]
    (c : (TopCat.toSSet.obj Y).obj (op ⦋n⦌) → M) :
    kernelFun (chainFamilyKernel (fun σ : Simplex Y n ↦ (single σ 1 : Chain ℤ Y n))) c = c := by
  classical
  funext τ
  have hk : ∀ σ, chainFamilyKernel (fun σ : Simplex Y n ↦ (single σ 1 : Chain ℤ Y n)) σ τ =
      if σ = τ then 1 else 0 := fun σ ↦ by
    simp only [chainFamilyKernel, Finsupp.single_apply, (SingularCochain.simplexEquiv Y n).injective.eq_iff]
  rw [kernelFun, finsum_eq_sum_of_support_subset (s := {τ}) _ (fun σ hσ ↦ by
    rw [Function.mem_support, hk] at hσ
    rw [Finset.coe_singleton, mem_singleton_iff]
    by_contra h
    exact hσ (by rw [ite_eq_right h, zero_smul]))]
  simp [hk]

end kernel

section complex

variable (R : Type u) [CommRing R] (M : ModuleCat.{u} R) {Y : TopCat.{u}} (𝒰 : Set (Set Y))

/-- The kernel of Hatcher's chain map `ρ` of the theorem of small chains. -/
abbrev smallKernel (n : ℕ) := chainFamilyKernel (Y := Y)
  (fun σ : Simplex Y n ↦ smallChainMap ℤ 𝒰 n (single σ 1))

/-- The kernel of Hatcher's chain homotopy `D` of the theorem of small chains. -/
abbrev smallHomotopyKernel (n : ℕ) := chainFamilyKernel (Y := Y)
  (fun σ : Simplex Y n ↦ smallHomotopy ℤ 𝒰 n (single σ 1))

/-- The kernel of `ρ` is an admissible kernel. -/
lemma isAdmissibleKernel_smallKernel (n : ℕ) :
    IsAdmissibleKernel (id : Y → Y) (singularSimplexImage Y (n := op ⦋n⦌))
      (singularSimplexImage Y (n := op ⦋n⦌)) (smallKernel 𝒰 n) :=
  isAdmissibleKernel_chainFamilyKernel (smallChainMap_single_mem_inside 𝒰 n)

/-- The kernel of `D` is an admissible kernel. -/
lemma isAdmissibleKernel_smallHomotopyKernel (n : ℕ) :
    IsAdmissibleKernel (id : Y → Y) (singularSimplexImage Y (n := op ⦋n⦌))
      (singularSimplexImage Y (n := op ⦋n + 1⦌)) (smallHomotopyKernel 𝒰 n) :=
  isAdmissibleKernel_chainFamilyKernel (smallHomotopy_single_mem_inside 𝒰 n)

/-- The boundary of `ρ σ` is the alternating sum of `ρ` of the faces of `σ`. -/
lemma bd_smallChainMap_single (n : ℕ) (σ : Simplex Y (n + 1)) :
    bd ℤ n (smallChainMap ℤ 𝒰 (n + 1) (single σ 1)) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        smallChainMap ℤ 𝒰 n (single (σ.comp (face n i)) 1) := by
  rw [bd_smallChainMap, bd_single, map_sum]
  simp only [map_smul]

/-- Hatcher's chain map `ρ` of the theorem of small chains, on locally finite chains:
`∑ a_σ σ ↦ ∑ a_σ ρ σ`. -/
def smallChainMapLF :
    borelMooreChainComplex R M Y ⟶ borelMooreChainComplex R M Y where
  f n := ModuleCat.ofHom (kernelMap R (isAdmissibleKernel_smallKernel 𝒰 n))
  comm' := by
    rintro _ n rfl
    ext c : 2
    apply Subtype.ext
    have h1 := borelMooreChainComplex_d_apply R M Y n
      (kernelMap R (isAdmissibleKernel_smallKernel 𝒰 (n + 1)) c)
    have h2 := borelMooreChainComplex_d_apply R M Y n c
    change (((borelMooreChainComplex R M Y).d (n + 1) n).hom
      (kernelMap R (isAdmissibleKernel_smallKernel 𝒰 (n + 1)) c)).1 =
      (kernelMap R (isAdmissibleKernel_smallKernel 𝒰 n)
        (((borelMooreChainComplex R M Y).d (n + 1) n).hom c)).1
    rw [h1]
    change dFun _ (kernelFun _ c.1) =
      kernelFun _ (((borelMooreChainComplex R M Y).d (n + 1) n).hom c).1
    rw [h2]
    exact (kernelFun_dFun (isAdmissibleKernel_smallKernel 𝒰 n)
      (isAdmissibleKernel_smallKernel 𝒰 (n + 1)) _ _
      (fun i σ ↦ singularSimplexImage_map_subset _ σ)
      (fun i τ ↦ singularSimplexImage_map_subset _ τ)
      (chainFamilyKernel_comm _ _ (bd_smallChainMap_single 𝒰 n)) c.2).symm

/-- `ρ` on a locally finite chain `c` is the transform of `c` by the kernel `smallKernel`. -/
lemma smallChainMapLF_f_apply (n : ℕ) (c : (borelMooreChainComplex R M Y).X n) :
    (((smallChainMapLF R M 𝒰).f n).hom c).1 = kernelFun (smallKernel 𝒰 n) c.1 :=
  rfl

variable {𝒰} in
open Classical in
/-- The identity `σ - ρ σ = ∂ D σ + D ∂ σ` of Hatcher's homotopy, coefficientwise, in positive
degree. -/
lemma chainFamilyKernel_single_sub_smallKernel_succ (k : ℕ)
    (σ τ : (TopCat.toSSet.obj Y).obj (op ⦋k + 1⦌)) :
    chainFamilyKernel (fun σ : Simplex Y (k + 1) ↦ (single σ 1 : Chain ℤ Y (k + 1))) σ τ -
        smallKernel 𝒰 (k + 1) σ τ =
      ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) *
          smallHomotopyKernel 𝒰 k ((TopCat.toSSet.obj Y).δ i σ) τ +
        ∑ i : Fin (k + 3), (-1 : ℤ) ^ (i : ℕ) * ∑ᶠ ω, (if (TopCat.toSSet.obj Y).δ i ω = τ then
          smallHomotopyKernel 𝒰 (k + 1) σ ω else 0) := by
  simp only [smallKernel, smallHomotopyKernel, chainFamilyKernel, finsum_ite_δ_eq,
    toSSetObjEquiv_δ]
  have h := congrArg (fun e : Chain ℤ Y (k + 1) ↦ e (SingularCochain.simplexEquiv Y (k + 1) τ))
    (smallChainMap_succ (R := ℤ) 𝒰 k (single (SingularCochain.simplexEquiv Y (k + 1) σ) 1))
  simp only [bd_single, map_sum, map_smul, Finsupp.sub_apply, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, smul_eq_mul, bd_apply] at h
  rw [h]
  ring

variable {𝒰} in
open Classical in
/-- The identity `σ - ρ σ = ∂ D σ` of Hatcher's homotopy, coefficientwise, in degree `0`. -/
lemma chainFamilyKernel_single_sub_smallKernel_zero (σ τ : (TopCat.toSSet.obj Y).obj (op ⦋0⦌)) :
    chainFamilyKernel (fun σ : Simplex Y 0 ↦ (single σ 1 : Chain ℤ Y 0)) σ τ -
        smallKernel 𝒰 0 σ τ =
      ∑ i : Fin (0 + 2), (-1 : ℤ) ^ (i : ℕ) * ∑ᶠ ω, (if (TopCat.toSSet.obj Y).δ i ω = τ then
          smallHomotopyKernel 𝒰 0 σ ω else 0) := by
  simp only [smallKernel, smallHomotopyKernel, chainFamilyKernel, finsum_ite_δ_eq]
  have h := congrArg (fun e : Chain ℤ Y 0 ↦ e (SingularCochain.simplexEquiv Y 0 τ))
    (smallChainMap_zero (R := ℤ) 𝒰 (single (SingularCochain.simplexEquiv Y 0 σ) 1))
  simp only [Finsupp.sub_apply, bd_apply] at h
  rw [h]
  ring

/-- Hatcher's chain homotopy `D` on locally finite chains of degree `n`. -/
def smallHomotopyMap (n : ℕ) :
    (borelMooreChainComplex R M Y).X n ⟶ (borelMooreChainComplex R M Y).X (n + 1) :=
  ModuleCat.ofHom (kernelMap R (isAdmissibleKernel_smallHomotopyKernel 𝒰 n))

/-- `D ∂` on a locally finite chain is the transform by the alternating sum of the kernels of `D`
on the faces. -/
lemma d_smallHomotopyMap_apply (k : ℕ) (c : (borelMooreChainComplex R M Y).X (k + 1)) :
    (((borelMooreChainComplex R M Y).d (k + 1) k ≫ smallHomotopyMap R M 𝒰 k).hom c).1 =
      kernelFun (fun σ τ ↦ ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) *
        smallHomotopyKernel 𝒰 k ((TopCat.toSSet.obj Y).δ i σ) τ) c.1 := by
  change kernelFun (smallHomotopyKernel 𝒰 k)
    (((borelMooreChainComplex R M Y).d (k + 1) k).hom c).1 = _
  rw [borelMooreChainComplex_d_apply]
  exact kernelFun_dFun_eq (isAdmissibleKernel_smallHomotopyKernel 𝒰 k)
    (fun i : Fin (k + 2) ↦ (TopCat.toSSet.obj Y).δ i)
    (fun i σ ↦ singularSimplexImage_map_subset _ σ) c.2

open Classical in
/-- `∂ D` on a locally finite chain is the transform by the boundary of the kernel of `D`. -/
lemma smallHomotopyMap_d_apply (k : ℕ) (c : (borelMooreChainComplex R M Y).X k) :
    ((smallHomotopyMap R M 𝒰 k ≫ (borelMooreChainComplex R M Y).d (k + 1) k).hom c).1 =
      kernelFun (fun σ τ ↦ ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) * ∑ᶠ ω,
        (if (TopCat.toSSet.obj Y).δ i ω = τ then smallHomotopyKernel 𝒰 k σ ω else 0)) c.1 := by
  change (((borelMooreChainComplex R M Y).d (k + 1) k).hom (smallHomotopyMap R M 𝒰 k c)).1 = _
  rw [borelMooreChainComplex_d_apply]
  change dFun _ (kernelFun (smallHomotopyKernel 𝒰 k) c.1) = _
  exact dFun_kernelFun_eq (isAdmissibleKernel_smallHomotopyKernel 𝒰 k)
    (fun i : Fin (k + 2) ↦ (TopCat.toSSet.obj Y).δ i)
    (fun i τ ↦ singularSimplexImage_map_subset _ τ)
    (fun τ ↦ ⟨isCompact_singularSimplexImage τ, nonempty_singularSimplexImage τ⟩) c.2

variable {𝒰} in
open Classical in
/-- If the kernel of `∂ D` at `σ` is nonzero at `τ`, the image of `τ` lies in that of `σ`. -/
lemma singularSimplexImage_subset_of_sum_finsum_smallHomotopyKernel_ne_zero {k : ℕ}
    {σ : (TopCat.toSSet.obj Y).obj (op ⦋k⦌)} {τ : (TopCat.toSSet.obj Y).obj (op ⦋k⦌)}
    (h : ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) * ∑ᶠ ω,
      (if (TopCat.toSSet.obj Y).δ i ω = τ then smallHomotopyKernel 𝒰 k σ ω else 0) ≠ 0) :
    singularSimplexImage Y τ ⊆ singularSimplexImage Y σ := by
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hi' := right_ne_zero_of_mul hi
  obtain ⟨ω, hω⟩ : ∃ ω, (if (TopCat.toSSet.obj Y).δ i ω = τ then
      smallHomotopyKernel 𝒰 k σ ω else 0) ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hi' (finsum_eq_zero_of_forall_eq_zero hc)
  split_ifs at hω with hδ
  · rw [← hδ]
    exact (singularSimplexImage_δ_subset i ω).trans
      (singularSimplexImage_subset_of_chainFamilyKernel_ne_zero
        (smallHomotopy_single_mem_inside 𝒰 k) hω)
  · exact absurd rfl hω

variable {𝒰} in
/-- If the kernel of `D ∂` at `σ` is nonzero at `τ`, the image of `τ` lies in that of `σ`. -/
lemma singularSimplexImage_subset_of_sum_smallHomotopyKernel_ne_zero {k : ℕ}
    {σ : (TopCat.toSSet.obj Y).obj (op ⦋k + 1⦌)} {τ : (TopCat.toSSet.obj Y).obj (op ⦋k + 1⦌)}
    (h : ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) *
      smallHomotopyKernel 𝒰 k ((TopCat.toSSet.obj Y).δ i σ) τ ≠ 0) :
    singularSimplexImage Y τ ⊆ singularSimplexImage Y σ := by
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact (singularSimplexImage_subset_of_chainFamilyKernel_ne_zero
    (smallHomotopy_single_mem_inside 𝒰 k) (right_ne_zero_of_mul hi)).trans
    (singularSimplexImage_δ_subset i σ)

/-- On locally finite chains of degree `k + 1`, `1 - ρ = D ∂ + ∂ D`. -/
lemma id_sub_smallChainMapLF_succ (k : ℕ) :
    HomologicalComplex.Hom.f (𝟙 (borelMooreChainComplex R M Y)) (k + 1) -
        (smallChainMapLF R M 𝒰).f (k + 1) =
      (borelMooreChainComplex R M Y).d (k + 1) k ≫ smallHomotopyMap R M 𝒰 k +
        smallHomotopyMap R M 𝒰 (k + 1) ≫ (borelMooreChainComplex R M Y).d (k + 1 + 1) (k + 1) := by
  ext c : 2
  apply Subtype.ext
  funext τ
  have e₁ := congrFun (kernelFun_chainFamilyKernel_single (Y := Y) (n := k + 1) c.1) τ
  have e₃ := congrFun (d_smallHomotopyMap_apply R M 𝒰 k c) τ
  have e₄ := congrFun (smallHomotopyMap_d_apply R M 𝒰 (k + 1) c) τ
  change c.1 τ - kernelFun (smallKernel 𝒰 (k + 1)) c.1 τ =
    ((((borelMooreChainComplex R M Y).d (k + 1) k ≫ smallHomotopyMap R M 𝒰 k).hom c).1 τ +
      ((smallHomotopyMap R M 𝒰 (k + 1) ≫
        (borelMooreChainComplex R M Y).d (k + 1 + 1) (k + 1)).hom c).1 τ)
  rw [← e₁, e₃, e₄]
  have hK := isCompact_singularSimplexImage τ
  rw [kernelFun_eq_sum_of_inter_nonempty _ c.2 hK τ (fun σ hσ ↦
      inter_nonempty_of_singularSimplexImage_subset
        (singularSimplexImage_subset_of_chainFamilyKernel_ne_zero (fun σ ↦
          single_mem_supported ℤ _ (show range σ ⊆ range σ from subset_rfl)) hσ)),
    kernelFun_eq_sum_of_inter_nonempty _ c.2 hK τ (fun σ hσ ↦
      inter_nonempty_of_singularSimplexImage_subset
        (singularSimplexImage_subset_of_chainFamilyKernel_ne_zero
          (smallChainMap_single_mem_inside 𝒰 (k + 1)) hσ)),
    kernelFun_eq_sum_of_inter_nonempty _ c.2 hK τ (fun σ hσ ↦
      inter_nonempty_of_singularSimplexImage_subset
        (singularSimplexImage_subset_of_sum_smallHomotopyKernel_ne_zero hσ)),
    kernelFun_eq_sum_of_inter_nonempty _ c.2 hK τ (fun σ hσ ↦
      inter_nonempty_of_singularSimplexImage_subset
        (singularSimplexImage_subset_of_sum_finsum_smallHomotopyKernel_ne_zero hσ)),
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [← sub_smul, ← add_smul, chainFamilyKernel_single_sub_smallKernel_succ k σ τ]

/-- On locally finite chains of degree `0`, `1 - ρ = ∂ D`. -/
lemma id_sub_smallChainMapLF_zero :
    HomologicalComplex.Hom.f (𝟙 (borelMooreChainComplex R M Y)) 0 - (smallChainMapLF R M 𝒰).f 0 =
      smallHomotopyMap R M 𝒰 0 ≫ (borelMooreChainComplex R M Y).d (0 + 1) 0 := by
  ext c : 2
  apply Subtype.ext
  funext τ
  have e₁ := congrFun (kernelFun_chainFamilyKernel_single (Y := Y) (n := 0) c.1) τ
  have e₄ := congrFun (smallHomotopyMap_d_apply R M 𝒰 0 c) τ
  change c.1 τ - kernelFun (smallKernel 𝒰 0) c.1 τ =
    ((smallHomotopyMap R M 𝒰 0 ≫ (borelMooreChainComplex R M Y).d (0 + 1) 0).hom c).1 τ
  rw [← e₁, e₄]
  have hK := isCompact_singularSimplexImage τ
  rw [kernelFun_eq_sum_of_inter_nonempty _ c.2 hK τ (fun σ hσ ↦
      inter_nonempty_of_singularSimplexImage_subset
        (singularSimplexImage_subset_of_chainFamilyKernel_ne_zero (fun σ ↦
          single_mem_supported ℤ _ (show range σ ⊆ range σ from subset_rfl)) hσ)),
    kernelFun_eq_sum_of_inter_nonempty _ c.2 hK τ (fun σ hσ ↦
      inter_nonempty_of_singularSimplexImage_subset
        (singularSimplexImage_subset_of_chainFamilyKernel_ne_zero
          (smallChainMap_single_mem_inside 𝒰 0) hσ)),
    kernelFun_eq_sum_of_inter_nonempty _ c.2 hK τ (fun σ hσ ↦
      inter_nonempty_of_singularSimplexImage_subset
        (singularSimplexImage_subset_of_sum_finsum_smallHomotopyKernel_ne_zero hσ)),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [← sub_smul, chainFamilyKernel_single_sub_smallKernel_zero σ τ]

/-- The components of Hatcher's homotopy, indexed as Mathlib's null-homotopic maps require. -/
def smallHomotopyHom (i j : ℕ) (r : (ComplexShape.down ℕ).Rel j i) :
    (borelMooreChainComplex R M Y).X i ⟶ (borelMooreChainComplex R M Y).X j :=
  smallHomotopyMap R M 𝒰 i ≫ ((borelMooreChainComplex R M Y).XIsoOfEq r).hom

/-- `1 - ρ` is the null-homotopic map given by Hatcher's homotopy `D`. -/
lemma id_sub_smallChainMapLF :
    𝟙 (borelMooreChainComplex R M Y) - smallChainMapLF R M 𝒰 =
      Homotopy.nullHomotopicMap' (smallHomotopyHom R M 𝒰) := by
  ext1 n
  rw [HomologicalComplex.sub_f_apply]
  rcases n with _ | k
  · rw [Homotopy.nullHomotopicMap'_f_of_not_rel_left (k₁ := 0 + 1) (k₀ := 0) rfl
      (fun l hl ↦ by simp at hl), id_sub_smallChainMapLF_zero]
    simp only [smallHomotopyHom, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id]
  · rw [Homotopy.nullHomotopicMap'_f (k₂ := k + 1 + 1) (k₁ := k + 1) (k₀ := k) rfl rfl,
      id_sub_smallChainMapLF_succ]
    simp only [smallHomotopyHom, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id]

/-- Hatcher's chain homotopy `1 - ρ = ∂ D + D ∂` on locally finite chains. -/
def smallChainMapLFHomotopy :
    Homotopy (𝟙 (borelMooreChainComplex R M Y)) (smallChainMapLF R M 𝒰) :=
  Homotopy.equivSubZero.symm ((Homotopy.ofEq (id_sub_smallChainMapLF R M 𝒰)).trans
    (Homotopy.nullHomotopy' (smallHomotopyHom R M 𝒰)))

/-- `ρ` induces the identity on Borel–Moore homology. -/
theorem homologyMap_smallChainMapLF (j : ℤ) :
    HomologicalComplex.homologyMap (HomologicalComplex.extendMap (smallChainMapLF R M 𝒰)
      ComplexShape.embeddingDownNat) (-j) = 𝟙 (borelMooreHomology R M Y j) := by
  rw [← (((smallChainMapLFHomotopy R M 𝒰).extend ComplexShape.embeddingDownNat).homologyMap_eq
    (-j)), HomologicalComplex.extendMap_id, HomologicalComplex.homologyMap_id]
  rfl

variable {𝒰} in
/-- **The theorem of small chains for locally finite chains.** If `𝒰` is an open cover of `Y`,
every simplex of `ρ c` lies in a member of `𝒰`. -/
theorem smallChainMapLF_small (h𝒰 : ∀ U ∈ 𝒰, IsOpen U) (hcov : ⋃₀ 𝒰 = univ) (n : ℕ)
    (c : (borelMooreChainComplex R M Y).X n) {τ : (TopCat.toSSet.obj Y).obj (op ⦋n⦌)}
    (hτ : (((smallChainMapLF R M 𝒰).f n).hom c).1 τ ≠ 0) :
    ∃ U ∈ 𝒰, singularSimplexImage Y τ ⊆ U := by
  rw [smallChainMapLF_f_apply] at hτ
  obtain ⟨σ, hσ⟩ : ∃ σ, smallKernel 𝒰 n σ τ • c.1 σ ≠ 0 := by
    by_contra h
    push Not at h
    exact hτ (finsum_eq_zero_of_forall_eq_zero h)
  have hmem := smallChainMap_single_mem_small (R := ℤ) h𝒰 n
    (σ := SingularCochain.simplexEquiv Y n σ) (hcov ▸ subset_univ _)
  obtain ⟨U, hU, hsub⟩ := hmem (Finsupp.mem_support_iff.2 (smul_ne_zero_left hσ))
  exact ⟨U, hU, (range_simplexEquiv τ).symm.subset.trans hsub⟩

end complex

section closed

variable {Y : TopCat.{u}} (N : Set Y)

/-- The inclusion of a subset `N`, as a morphism of `TopCat`. -/
def subsetInclusion : TopCat.of N ⟶ Y :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

variable {N}

/-- The inclusion of a closed subset is a proper map. -/
lemma isProperMap_subsetInclusion (hN : IsClosed N) : IsProperMap (subsetInclusion N) :=
  hN.isClosedEmbedding_subtypeVal.isProperMap

/-- The image in `Y` of the push-forward of a simplex `τ` of `N` is the image of `τ`. -/
lemma singularSimplexImage_map_subsetInclusion {n : ℕ}
    (τ : (TopCat.toSSet.obj (TopCat.of N)).obj (op ⦋n⦌)) :
    singularSimplexImage Y ((TopCat.toSSet.map (subsetInclusion N)).app _ τ) =
      Subtype.val '' singularSimplexImage (TopCat.of N) τ :=
  singularSimplexImage_map _ τ

/-- The push-forward of singular simplices along the inclusion of `N` is injective. -/
lemma map_subsetInclusion_injective (n : ℕ) :
    Function.Injective ((TopCat.toSSet.map (subsetInclusion N)).app (op ⦋n⦌)) := fun τ τ' h ↦ by
  apply (SingularCochain.simplexEquiv (TopCat.of N) n).injective
  ext t : 1
  exact Subtype.val_injective (congrArg (fun σ ↦ (SingularCochain.simplexEquiv Y n σ) t) h)

/-- The push-forward of a simplex `τ` of `N` is `τ` followed by the inclusion of `N`. -/
lemma toSSetObjEquiv_map_subsetInclusion {n : ℕ}
    (τ : (TopCat.toSSet.obj (TopCat.of N)).obj (op ⦋n⦌)) :
    SingularCochain.simplexEquiv Y n ((TopCat.toSSet.map (subsetInclusion N)).app _ τ) =
      (⟨Subtype.val, continuous_subtype_val⟩ : C(N, Y)).comp (SingularCochain.simplexEquiv (TopCat.of N) n τ) :=
  rfl

/-- A simplex lying in `N` comes from a simplex of `N`. -/
lemma mem_range_map_subsetInclusion {n : ℕ} {σ : (TopCat.toSSet.obj Y).obj (op ⦋n⦌)}
    (h : singularSimplexImage Y σ ⊆ N) :
    σ ∈ range ((TopCat.toSSet.map (subsetInclusion N)).app (op ⦋n⦌)) := by
  set σs : Simplex Y n := SingularCochain.simplexEquiv Y n σ
  refine ⟨(SingularCochain.simplexEquiv (TopCat.of N) n).symm
    ⟨fun t ↦ ⟨σs t, h ⟨stdSimplexHomeo _ t, rfl⟩⟩, σs.continuous.subtype_mk _⟩, ?_⟩
  apply (SingularCochain.simplexEquiv Y n).injective
  rw [toSSetObjEquiv_map_subsetInclusion, Equiv.apply_symm_apply]
  rfl

open Classical in
/-- The kernel of the restriction of chains supported in `N` to chains of `N`. -/
def subsetKernel (n : ℕ) (σ : (TopCat.toSSet.obj Y).obj (op ⦋n⦌))
    (τ : (TopCat.toSSet.obj (TopCat.of N)).obj (op ⦋n⦌)) : ℤ :=
  if (TopCat.toSSet.map (subsetInclusion N)).app _ τ = σ then 1 else 0

/-- The kernel `subsetKernel` is admissible along the inclusion of `N`. -/
lemma isAdmissibleKernel_subsetKernel (n : ℕ) :
    IsAdmissibleKernel (Subtype.val : N → Y) (singularSimplexImage Y (n := op ⦋n⦌))
      (singularSimplexImage (TopCat.of N) (n := op ⦋n⦌)) (subsetKernel n) where
  continuous := continuous_subtype_val
  image_subset σ τ h := by
    rw [subsetKernel] at h
    split_ifs at h with he
    · rw [← he, singularSimplexImage_map_subsetInclusion]
    · exact absurd rfl h
  isLocallyFiniteSet σ x := by
    have key : ∀ τ, τ ∈ Function.support (subsetKernel (N := N) n σ) →
        (TopCat.toSSet.map (subsetInclusion N)).app _ τ = σ := fun τ hτ ↦ by
      by_contra he
      exact hτ (ite_eq_right he)
    exact ⟨univ, Filter.univ_mem, Set.Subsingleton.finite fun τ hτ τ' hτ' ↦
      map_subsetInclusion_injective n ((key τ hτ.1).trans (key τ' hτ'.1).symm)⟩
  compact_nonempty τ := ⟨isCompact_singularSimplexImage τ, nonempty_singularSimplexImage τ⟩

end closed

section closedComplex

variable (R : Type u) [CommRing R] (M : ModuleCat.{u} R) {Y : TopCat.{u}} {N : Set Y}

variable (N) in
/-- A locally finite chain of `Y` is *supported in* `N` if all its simplices lie in `N`. -/
def IsSupportedIn {n : ℕ} (c : (borelMooreChainComplex R M Y).X n) : Prop :=
  ∀ σ, c.1 σ ≠ 0 → singularSimplexImage Y σ ⊆ N

variable (N) in
/-- The restriction `c ↦ c ∘ ι` of locally finite chains of `Y` to the subset `N`; on chains
supported in `N` it inverts the push-forward along the inclusion `ι`. -/
def subsetRestrictMap (n : ℕ) :
    (borelMooreChainComplex R M Y).X n ⟶ (borelMooreChainComplex R M (TopCat.of N)).X n :=
  ModuleCat.ofHom (kernelMap R (isAdmissibleKernel_subsetKernel (N := N) n))

/-- The restriction of `c` to `N` has, at a simplex `τ` of `N`, the coefficient of `c` at the
push-forward of `τ`. -/
lemma subsetRestrictMap_apply_coe {n : ℕ} (c : (borelMooreChainComplex R M Y).X n)
    (τ : (TopCat.toSSet.obj (TopCat.of N)).obj (op ⦋n⦌)) :
    ((subsetRestrictMap R M N n).hom c).1 τ =
      c.1 ((TopCat.toSSet.map (subsetInclusion N)).app _ τ) := by
  change kernelFun (subsetKernel n) c.1 τ = _
  rw [kernelFun, finsum_eq_single _ ((TopCat.toSSet.map (subsetInclusion N)).app _ τ)
    (fun σ hσ ↦ by rw [subsetKernel, ite_eq_right (Ne.symm hσ), zero_smul]),
    subsetKernel, ite_eq_left rfl, one_smul]

/-- For `N` closed, the push-forward along the inclusion of `N` of the restriction of a chain
supported in `N` is the chain itself. -/
lemma chainMap_subsetRestrictMap (hN : IsClosed N) {n : ℕ} {c : (borelMooreChainComplex R M Y).X n}
    (hc : IsSupportedIn R M N c) :
    ((chainMap R M (subsetInclusion N) (isProperMap_subsetInclusion hN)).f n).hom
      ((subsetRestrictMap R M N n).hom c) = c := by
  apply Subtype.ext
  funext σ
  change pushforwardFun ((TopCat.toSSet.map (subsetInclusion N)).app _)
    ((subsetRestrictMap R M N n).hom c).1 σ = c.1 σ
  by_cases hσ : σ ∈ range ((TopCat.toSSet.map (subsetInclusion N)).app (op ⦋n⦌))
  · obtain ⟨τ, rfl⟩ := hσ
    rw [pushforwardFun_apply_of_injective (map_subsetInclusion_injective n),
      subsetRestrictMap_apply_coe]
  · rw [pushforwardFun_apply_of_notMem_range _ hσ]
    by_contra h
    exact hσ (mem_range_map_subsetInclusion (hc σ (Ne.symm h)))

/-- For `N` closed, the push-forward of locally finite chains along the inclusion of `N` is
injective. -/
lemma chainMap_subsetInclusion_injective (hN : IsClosed N) (n : ℕ) :
    Function.Injective
      ((chainMap R M (subsetInclusion N) (isProperMap_subsetInclusion hN)).f n).hom := by
  intro c c' h
  apply Subtype.ext
  funext τ
  have := congrFun (congrArg Subtype.val h) ((TopCat.toSSet.map (subsetInclusion N)).app _ τ)
  change pushforwardFun ((TopCat.toSSet.map (subsetInclusion N)).app _) c.1 _ =
    pushforwardFun ((TopCat.toSSet.map (subsetInclusion N)).app _) c'.1 _ at this
  rwa [pushforwardFun_apply_of_injective (map_subsetInclusion_injective n),
    pushforwardFun_apply_of_injective (map_subsetInclusion_injective n)] at this

/-- The boundary of a chain supported in `N` is supported in `N`. -/
lemma IsSupportedIn.d {n : ℕ} {c : (borelMooreChainComplex R M Y).X (n + 1)}
    (hc : IsSupportedIn R M N c) :
    IsSupportedIn R M N (((borelMooreChainComplex R M Y).d (n + 1) n).hom c) := by
  intro σ hσ
  rw [borelMooreChainComplex_d_apply] at hσ
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hσ
  obtain ⟨σ', hσ', rfl⟩ := support_pushforwardFun_subset _ _ (smul_ne_zero_right hi)
  exact (singularSimplexImage_δ_subset i σ').trans (hc σ' hσ')

/-- On chains supported in a closed subset `N`, the restriction to `N` commutes with the
boundary. -/
lemma d_subsetRestrictMap (hN : IsClosed N) {n : ℕ} {c : (borelMooreChainComplex R M Y).X (n + 1)}
    (hc : IsSupportedIn R M N c) :
    ((borelMooreChainComplex R M (TopCat.of N)).d (n + 1) n).hom
        ((subsetRestrictMap R M N (n + 1)).hom c) =
      (subsetRestrictMap R M N n).hom (((borelMooreChainComplex R M Y).d (n + 1) n).hom c) := by
  apply chainMap_subsetInclusion_injective R M hN n
  rw [chainMap_subsetRestrictMap R M hN hc.d]
  have := congrArg (fun f ↦ f.hom ((subsetRestrictMap R M N (n + 1)).hom c))
    ((chainMap R M (subsetInclusion N) (isProperMap_subsetInclusion hN)).comm (n + 1) n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
  rw [← this, chainMap_subsetRestrictMap R M hN hc]

end closedComplex

end borelMooreHomology

namespace BorelMooreCap

open SingularCross BorelMooreCross SingularCochain SingularChain LocallyFiniteChain
  borelMooreHomology

variable {R : Type u} [CommRing R] {Y : TopCat.{u}}

/-- **Support of the cap product.** If every simplex of a locally finite chain `c` lies in `A` or
in `V`, and the cochain `φ` vanishes on the simplices of `A`, then every simplex of `φ ∩ c` lies
in `V`. -/
theorem singularSimplexImage_subset_of_coeff_capChain_ne_zero {A V : Set Y} (p q n : ℕ)
    (h : p + q = n) {φ : Simplex Y p → R} (hφ : φ ∈ vanishing R p A) (c : (BM R Y).X n)
    (hc : ∀ σ, coeff R c σ ≠ 0 → singularSimplexImage Y σ ⊆ A ∨ singularSimplexImage Y σ ⊆ V)
    {τ : Simp Y q} (hτ : coeff R (capChain R p q n h φ c) τ ≠ 0) :
    singularSimplexImage Y τ ⊆ V := by
  rw [capChain_apply, coeff_pf] at hτ
  obtain ⟨σ, hσ, rfl⟩ := support_pushforwardFun_subset _ _ hτ
  rw [Function.mem_support, coeff_W] at hσ
  have hw := left_ne_zero_of_mul hσ
  refine (image_opS_subset _ σ).trans ((hc σ (right_ne_zero_of_mul hσ)).resolve_left ?_)
  intro hA
  refine hw (hφ _ ?_)
  rintro _ ⟨t, rfl⟩
  exact hA ⟨_, rfl⟩

/-- The cap product of a cochain vanishing on `A` with `ρ c`, Hatcher's subdivision of `c`
towards the open cover `{A, V}`, is supported in `V`. -/
theorem singularSimplexImage_subset_of_coeff_capChain_smallChainMapLF_ne_zero {A V : Set Y}
    (hA : IsOpen A) (hV : IsOpen V) (hAV : A ∪ V = univ) (p q n : ℕ) (h : p + q = n)
    {φ : Simplex Y p → R} (hφ : φ ∈ vanishing R p A) (c : (BM R Y).X n) {τ : Simp Y q}
    (hτ : coeff R (capChain R p q n h φ
      (((smallChainMapLF R (ModuleCat.of R R) {A, V}).f n).hom c)) τ ≠ 0) :
    singularSimplexImage Y τ ⊆ V := by
  refine singularSimplexImage_subset_of_coeff_capChain_ne_zero p q n h hφ _ (fun σ hσ ↦ ?_) hτ
  obtain ⟨U, hU, hσU⟩ := smallChainMapLF_small R (ModuleCat.of R R)
    (by rintro U (rfl | rfl) <;> assumption) (by rwa [sUnion_insert, sUnion_singleton]) n c hσ
  rcases hU with rfl | rfl
  · exact Or.inl hσU
  · exact Or.inr hσU

section neighbourhood

/-! ### The cap product with supports in a closed neighbourhood

Let `A ⊆ Y` be open and `N ⊆ Y` closed with `A ∪ int N = Y` (for `A = Y - X`: `X ⊆ int N`).
For a cocycle `φ` vanishing on the simplices of `A` and a locally finite cycle `z` of `Y`, the
cap product `φ ∩ ρ z` with the subdivision `ρ z` of `z` towards `{A, int N}` is a cycle of `Y`
supported in `N`, hence a cycle of `N`. -/

variable {A N : Set Y} (hA : IsOpen A) (hN : IsClosed N) (hAN : A ∪ interior N = univ)

variable (R A N) in
/-- Hatcher's subdivision `ρ` towards `{A, int N}` on locally finite chains of degree `n`. -/
abbrev nbhdSubdiv (n : ℕ) : (BM R Y).X n ⟶ (BM R Y).X n :=
  (smallChainMapLF R (ModuleCat.of R R) {A, interior N}).f n

/-- The subdivision `ρ` of a cycle is a cycle. -/
lemma nbhdSubdiv_mem_cyc {n : ℕ} {z : (BM R Y).X n} (hz : z ∈ Cyc (R := R) Y n) :
    (nbhdSubdiv R A N n).hom z ∈ Cyc (R := R) Y n := by
  rw [mem_cyc_iff] at hz ⊢
  have := congrArg (fun f ↦ f.hom z) ((smallChainMapLF R (ModuleCat.of R R)
    {A, interior N}).comm n (n - 1))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
  exact this.trans ((congrArg _ hz).trans (map_zero _))

include hA hAN in
/-- For a cochain `ψ` vanishing on the simplices of `A`, the cap product `ψ ∩ ρ c` is supported in
`N`. -/
lemma isSupportedIn_capChain_nbhdSubdiv (p q n : ℕ) (h : p + q = n) {ψ : Simplex Y p → R}
    (hψ : ψ ∈ vanishing R p A) (c : (BM R Y).X n) :
    IsSupportedIn R (ModuleCat.of R R) N (capChain R p q n h ψ ((nbhdSubdiv R A N n).hom c)) :=
  fun _ hτ ↦ (singularSimplexImage_subset_of_coeff_capChain_smallChainMapLF_ne_zero hA
    isOpen_interior hAN p q n h hψ c hτ).trans interior_subset

/-- An integer multiple of a chain supported in `N` is supported in `N`. -/
lemma isSupportedIn_zsmul {n : ℕ} {c : (BM R Y).X n}
    (hc : IsSupportedIn R (ModuleCat.of R R) N c) (a : ℤ) :
    IsSupportedIn R (ModuleCat.of R R) N (a • c) :=
  fun σ hσ ↦ hc σ (fun h0 ↦ hσ (by
    change a • coeff R c σ = 0
    rw [show coeff R c σ = 0 from h0, smul_zero]))

/-- The negative of a chain supported in `N` is supported in `N`. -/
lemma isSupportedIn_neg {n : ℕ} {c : (BM R Y).X n}
    (hc : IsSupportedIn R (ModuleCat.of R R) N c) :
    IsSupportedIn R (ModuleCat.of R R) N (-c) := by
  simpa using isSupportedIn_zsmul hc (-1)

include hA hN hAN in
/-- For a relative cocycle `φ` and a cycle `z` of `Y`, the restriction to `N` of `φ ∩ ρ z` is a
cycle of `N`. -/
lemma capChain_nbhdSubdiv_restrict_mem_cyc (p q n : ℕ) (h : p + q = n)
    (φ : relCocycles R A p) (z : Cyc (R := R) Y n) :
    (subsetRestrictMap R (ModuleCat.of R R) N q).hom
      (capChain R p q n h φ.1 ((nbhdSubdiv R A N n).hom z.1)) ∈
        Cyc (R := R) (TopCat.of N) q := by
  rw [mem_cyc_iff]
  rcases q with _ | q
  · rw [show (0 : ℕ) - 1 = 0 from rfl, (BM R _).shape 0 0 (by simp)]
    rfl
  · have hw := capChain_mem_cyc A p (q + 1) n h φ ⟨_, nbhdSubdiv_mem_cyc (A := A) (N := N) z.2⟩
    rw [mem_cyc_iff] at hw
    change ((BM R (TopCat.of N)).d (q + 1) q).hom _ = 0
    rw [d_subsetRestrictMap R _ hN (isSupportedIn_capChain_nbhdSubdiv hA hAN p (q + 1) n h φ.2.1 _)]
    change (subsetRestrictMap R (ModuleCat.of R R) N q).hom
      (((BM R Y).d (q + 1) q).hom (capChain R p (q + 1) n h φ.1 ((nbhdSubdiv R A N n).hom z.1))) = 0
    rw [show ((BM R Y).d (q + 1) q).hom (capChain R p (q + 1) n h φ.1
      ((nbhdSubdiv R A N n).hom z.1)) = 0 from hw, map_zero]

variable (R) in
/-- The cap product of a relative cocycle and a cycle of `Y`, as a cycle of `N`. -/
def capCycNbhd (p q n : ℕ) (h : p + q = n) :
    relCocycles R A p →ₗ[R] Cyc (R := R) Y n →ₗ[R] Cyc (R := R) (TopCat.of N) q :=
  LinearMap.mk₂ R (fun φ z ↦ ⟨(subsetRestrictMap R (ModuleCat.of R R) N q).hom
      (capChain R p q n h φ.1 ((nbhdSubdiv R A N n).hom z.1)),
      capChain_nbhdSubdiv_restrict_mem_cyc hA hN hAN p q n h φ z⟩)
    (fun _ _ _ ↦ Subtype.ext (by simp))
    (fun _ _ _ ↦ Subtype.ext (by simp))
    (fun _ _ _ ↦ Subtype.ext (by simp))
    (fun _ _ _ ↦ Subtype.ext (by simp))

/-- The cap product of a relative cocycle with a cycle of `Y`, as a homology class of `N`. -/
def capCycQNbhd (p q n : ℕ) (h : p + q = n) :
    relCocycles R A p →ₗ[R] Cyc (R := R) Y n →ₗ[R] HomQ (R := R) (TopCat.of N) q :=
  (capCycNbhd R hA hN hAN p q n h).compr₂
    (LinearMap.range ((BM R (TopCat.of N)).sc q).moduleCatToCycles).mkQ

/-- The subdivision `ρ` commutes with the boundary. -/
lemma nbhdSubdiv_d {n : ℕ} (u : (BM R Y).X (n + 1)) :
    (nbhdSubdiv R A N n).hom (((BM R Y).d (n + 1) n).hom u) =
      ((BM R Y).d (n + 1) n).hom ((nbhdSubdiv R A N (n + 1)).hom u) := by
  have := congrArg (fun f ↦ f.hom u) ((smallChainMapLF R (ModuleCat.of R R)
    {A, interior N}).comm (n + 1) n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
  exact this.symm

include hN in
/-- The restriction to `N` of the boundary of a chain supported in `N` is a boundary of `N`. -/
lemma restrict_d_mem_bdry {q : ℕ} (u : (BM R Y).X (q + 1))
    (hu : IsSupportedIn R (ModuleCat.of R R) N u) (w : Cyc (R := R) (TopCat.of N) q)
    (hw : w.1 = (subsetRestrictMap R (ModuleCat.of R R) N q).hom (((BM R Y).d (q + 1) q).hom u)) :
    w ∈ LinearMap.range ((BM R (TopCat.of N)).sc q).moduleCatToCycles :=
  mem_bdry_of w ((subsetRestrictMap R (ModuleCat.of R R) N (q + 1)).hom u)
    ((d_subsetRestrictMap R _ hN hu).trans hw.symm)

/-- The cap product of a relative coboundary with a cycle of `Y` is zero in homology of `N`. -/
lemma capCycQNbhd_coboundary (p q n : ℕ) (h : p + q = n) :
    (relCoboundaries R A p).comap (relCocycles R A p).subtype ≤
      LinearMap.ker (capCycQNbhd hA hN hAN p q n h) := by
  intro φ hφ
  change capCycQNbhd hA hN hAN p q n h φ = 0
  ext z
  rcases p with _ | p
  · rw [show φ = 0 from Subtype.ext hφ, map_zero, LinearMap.zero_apply]
  · obtain ⟨ψ, hψ, hψφ⟩ := hφ
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    refine (Submodule.Quotient.mk_eq_zero _).2 (restrict_d_mem_bdry hN
      (-((-1 : ℤ) ^ q • capChain R p (q + 1) (n + 1) (by omega) ψ
        ((nbhdSubdiv R A N (n + 1)).hom z.1)))
      (isSupportedIn_neg (isSupportedIn_zsmul
        (isSupportedIn_capChain_nbhdSubdiv hA hAN p (q + 1) (n + 1) _ hψ _) _)) _ ?_)
    rw [d_neg_zsmul_capChain_cyc p q n (by omega) ψ ⟨_, nbhdSubdiv_mem_cyc z.2⟩, hψφ]
    rfl

/-- The cap product of a relative cohomology class with a cycle of `Y`, in the homology of `N`. -/
def capHomQNbhd₁ (p q n : ℕ) (h : p + q = n) :
    relCohomology R A p →ₗ[R] Cyc (R := R) Y n →ₗ[R] HomQ (R := R) (TopCat.of N) q :=
  ((relCoboundaries R A p).comap (relCocycles R A p).subtype).liftQ
    (capCycQNbhd hA hN hAN p q n h) (capCycQNbhd_coboundary hA hN hAN p q n h)

/-- The cap product of a relative cohomology class with a boundary of `Y` is zero. -/
lemma capHomQNbhd₁_bdry (p q n : ℕ) (h : p + q = n) :
    LinearMap.range ((BM R Y).sc n).moduleCatToCycles ≤
      LinearMap.ker (capHomQNbhd₁ hA hN hAN p q n h).flip := by
  intro z hz
  obtain ⟨u, hu⟩ := exists_of_mem_bdry hz
  change (capHomQNbhd₁ hA hN hAN p q n h).flip z = 0
  refine Submodule.linearMap_qext _ (LinearMap.ext fun φ ↦ ?_)
  refine (Submodule.Quotient.mk_eq_zero _).2 (restrict_d_mem_bdry hN
    (capChain R p (q + 1) (n + 1) (by omega) φ.1 ((nbhdSubdiv R A N (n + 1)).hom u))
    (isSupportedIn_capChain_nbhdSubdiv hA hAN p (q + 1) (n + 1) _ φ.2.1 _) _ ?_)
  rw [d_capChain_relCocycle A p q n h φ, ← nbhdSubdiv_d, hu]
  rfl

variable (R) in
/-- The cap product `H^p(Y, A) ⊗ H_n Y → H_q N` on cocycles modulo coboundaries and cycles
modulo boundaries, for `A` open and `N` closed with `A ∪ int N = Y`:
`[φ] ∩ [z] = [(φ ∩ ρ z)|_N]`. -/
def capHomQNbhd (p q n : ℕ) (h : p + q = n) :
    relCohomology R A p →ₗ[R] HomQ (R := R) Y n →ₗ[R] HomQ (R := R) (TopCat.of N) q :=
  ((LinearMap.range ((BM R Y).sc n).moduleCatToCycles).liftQ
    (capHomQNbhd₁ hA hN hAN p q n h).flip (capHomQNbhd₁_bdry hA hN hAN p q n h)).flip

/-- On the classes of a relative cocycle `φ` and a cycle `z`, `capHomQNbhd` is the class of
`capCycNbhd φ z`. -/
lemma capHomQNbhd_mk (p q n : ℕ) (h : p + q = n) (φ : relCocycles R A p)
    (z : Cyc (R := R) Y n) :
    capHomQNbhd R hA hN hAN p q n h (Submodule.Quotient.mk φ) (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (capCycNbhd R hA hN hAN p q n h φ z) :=
  rfl

end neighbourhood

end BorelMooreCap

namespace borelMooreHomology

open BorelMooreCap BorelMooreCross SingularCochain

variable (R : Type u) [CommRing R]

/-- If `X ⊆ int N`, then `Y - X` and `int N` cover `Y`. -/
lemma compl_union_interior_eq_univ {Y : Type*} [TopologicalSpace Y] {X N : Set Y}
    (hXN : X ⊆ interior N) : Xᶜ ∪ interior N = univ :=
  Set.compl_subset_iff_union.1 (by rwa [compl_compl])

/-- The cap product `∩ : H^j(Y, Y - X) ⊗ H_k Y → H_{k-j} N` with values in a closed
neighbourhood `N` of a closed subset `X`: on classes of a cocycle `φ` vanishing on the simplices
of `Y - X` and of a locally finite cycle `z`, it is the class of the cycle `φ ∩ ρ z` of `N`,
where `ρ z` is the subdivision of `z` towards the open cover `{Y - X, int N}`. Zero when `j < 0`
or `j > k`. -/
def capProductNbhd (Y : TopCat.{u}) {X N : Set Y} (hX : IsClosed X) (hN : IsClosed N)
    (hXN : X ⊆ interior N) (j k : ℤ) :
    cohomologyWithSupports R (ModuleCat.of R R) Y X j →ₗ[R]
      borelMooreHomology R (ModuleCat.of R R) Y k →ₗ[R]
        borelMooreHomology R (ModuleCat.of R R) (TopCat.of N) (k - j) :=
  if h : 0 ≤ j ∧ j ≤ k then
    ((capHomQNbhd R hX.isOpen_compl hN (compl_union_interior_eq_univ hXN) j.toNat
        (k.toNat - j.toNat) k.toNat (by omega)).compl₁₂
        ((cohomologyWithSupports.congrIndex R Y rfl (Int.toNat_of_nonneg h.1).symm).trans
          (relativeSingularCohomologyEquiv R Xᶜ j.toNat)).toLinearMap
        ((congrDegree R Y (Int.toNat_of_nonneg (h.1.trans h.2)).symm).trans
          (homologyEquiv R Y k.toNat)).toLinearMap).compr₂
      ((congrDegree R (TopCat.of N) (by omega)).trans
        (homologyEquiv R (TopCat.of N) (k.toNat - j.toNat))).symm.toLinearMap
  else 0

/-- The cap product `H^j(Y, Y - X) ⊗ H_k Y → H_{k-j} Z` along a proper map `f : N → Z` from a
closed neighbourhood `N` of `X`: `c ∩ a = f_* (c ∩_N a)`. For a proper retraction `f : N → X`
this is the cap product with values in `H_{k-j} X`. -/
def capProductAlong (Y : TopCat.{u}) {X N : Set Y} (hX : IsClosed X) (hN : IsClosed N)
    (hXN : X ⊆ interior N) {Z : TopCat.{u}} (f : TopCat.of N ⟶ Z) (hf : IsProperMap f)
    (j k : ℤ) :
    cohomologyWithSupports R (ModuleCat.of R R) Y X j →ₗ[R]
      borelMooreHomology R (ModuleCat.of R R) Y k →ₗ[R]
        borelMooreHomology R (ModuleCat.of R R) Z (k - j) :=
  (capProductNbhd R Y hX hN hXN j k).compr₂ (pushforward R _ f hf (k - j)).hom

end borelMooreHomology

end MMP
