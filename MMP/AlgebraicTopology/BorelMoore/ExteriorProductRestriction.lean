module

public import MMP.AlgebraicTopology.BorelMoore.ExteriorProductNatural
public import MMP.AlgebraicTopology.BorelMoore.RestrictionFunctorial
public import MMP.AlgebraicTopology.PoincareDuality.Localize
/-!
# The exterior product commutes with restriction to open subsets (Fulton, §19.1)

For open subsets `U ⊆ X`, `V ⊆ Y` of Hausdorff spaces and `a ∈ H_i X`, `b ∈ H_j Y`,
`(a × b)|_{U × V} = a|_U × b|_V`.

The two sides do not agree on chains, since subdividing `σ × τ` towards `U × V` differs from
crossing the subdivisions of `σ` towards `U` and of `τ` towards `V`. Let `ρ_N = 1 - ∂ D_N - D_N ∂`
and `ρ'_N = 1 - ∂ D'_N - D'_N ∂` be the chain maps of the subdivisions towards `U` and `V`. The
Leibniz rule for the cross product of finite chains gives the chain homotopy identity
`σ × τ = ρ_N σ × ρ'_N τ + ∂ h_N (σ, τ) + h_N (∂ σ, τ) + (-1) ^ p h_N (σ, ∂ τ)`, with
`h_N (σ, τ) = D_N σ × τ + (-1) ^ p ρ_N σ × D'_N τ`. Restricting to `U × V` near a simplex `ω` of
`U × V`, for large `N` the chains `ρ_N σ`, `ρ'_N τ` are their good parts plus chains away from
`ω`, the good parts give `σ|_U × τ|_V`, and the restrictions of `h_N (σ, τ)` stabilize to a
locally finite chain `h (σ, τ)` of `U × V` (Borel–Moore, §3). Hence
`(σ × τ)|_{U × V} - σ|_U × τ|_V = ∂ h (σ, τ) + h (∂ σ, τ) + (-1) ^ p h (σ, ∂ τ)`, and summing over
the simplices of cycles `z`, `w`, the difference `(z × w)|_{U × V} - z|_U × w|_V` is the boundary
of `h (z, w)`.

## Main definitions

* `MMP.SingularChain.cross`: the cross product of finite integral chains.
* `MMP.SingularChain.crossHomotopyChain`: the chain homotopy `h_N`.
* `MMP.SingularChain.crossHomotopyCoeff`: the coefficients of `h (σ, τ)`.
* `MMP.borelMooreHomology.prodOpens`: the open subset `U × V` of `X × Y`.
* `MMP.borelMooreHomology.prodOpensHomeo`: its homeomorphism with `U × V`.

## Main results

* `MMP.SingularChain.bd_cross`: the Leibniz rule for finite chains.
* `MMP.SingularChain.cross_eq_add_bd_crossHomotopyChain`: the homotopy identity
  of chains.
* `MMP.SingularChain.restrFin_crossSimplexChain_sub_crossRestrCoeff`: the
  homotopy identity after restriction.
* `MMP.borelMooreHomology.exists_d_eq_prodRestrictChainMap_crossChain_sub`: on
  cycles, `(z × w)|_{U × V} - z|_U × w|_V` is a boundary.
* `MMP.borelMooreHomology.restrict_exteriorProduct`:
  `(a × b)|_{U × V} = a|_U × b|_V`.

## Implementation notes

The spaces are Hausdorff, as the restriction `MMP.borelMooreHomology.restrict` is
defined for Hausdorff spaces (Fulton's spaces are). The open subset `U × V` of `X × Y` is a
subspace, while `a|_U × b|_V` lives on the product of the spaces `U` and `V`; the two are
identified by the homeomorphism `MMP.borelMooreHomology.prodOpensHomeo`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [A. Borel, J. C. Moore, *Homology theory for locally compact spaces*][borelmoore1960], §3.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Simplicial AlgebraicTopology Set Finsupp TensorProduct
  MMP.LatticePath MMP.SingularCross

universe u

namespace MMP

namespace SingularChain

section Cross

variable {X Y : TopCat.{u}}

/-- The cross product `σ × τ` of singular simplices, as an integral chain of degree `n` of
`X × Y` (zero unless `n = p + q`). -/
def crossSimplexChain (n : ℕ) {p q : ℕ} (σ : Simplex X p) (τ : Simplex Y q) :
    Chain ℤ (X × Y) n :=
  Finsupp.mapDomain (fun ρ ↦ (SingularCochain.simplexEquiv _ _ ρ : Simplex (X × Y) n))
    (crossSimplex n ((SingularCochain.simplexEquiv X p).symm σ) ((SingularCochain.simplexEquiv Y q).symm τ))

/-- The cross product of finite integral singular chains. -/
def cross (n p q : ℕ) : Chain ℤ X p →ₗ[ℤ] Chain ℤ Y q →ₗ[ℤ] Chain ℤ (X × Y) n :=
  Finsupp.linearCombination ℤ fun σ ↦ Finsupp.linearCombination ℤ fun τ ↦ crossSimplexChain n σ τ

/-- The cross product of `a • σ` and `b • τ` is `(a * b) • (σ × τ)`. -/
lemma cross_single (n : ℕ) {p q : ℕ} (σ : Simplex X p) (τ : Simplex Y q) (a b : ℤ) :
    cross n p q (single σ a) (single τ b) = (a * b) • crossSimplexChain n σ τ := by
  simp [cross, mul_smul, smul_comm a b]

/-- The boundary in degree `p`, landing in degree `p - 1`; zero in degree `0`. -/
def bdSub (R : Type*) [CommRing R] {Z : Type*} [TopologicalSpace Z] (p : ℕ) :
    Chain R Z p →ₗ[R] Chain R Z (p - 1) :=
  match p with
  | 0 => 0
  | p + 1 => bd R p

/-- The boundary `bdSub` in degree `0` is zero. -/
@[simp] lemma bdSub_zero {R : Type*} [CommRing R] {Z : Type*} [TopologicalSpace Z] :
    bdSub R (Z := Z) 0 = 0 := rfl

/-- The boundary `bdSub` in degree `p + 1` is the boundary `bd`. -/
@[simp] lemma bdSub_succ {R : Type*} [CommRing R] {Z : Type*} [TopologicalSpace Z] (p : ℕ) :
    bdSub R (Z := Z) (p + 1) = bd R p := rfl

/-- The boundary of a chain of simplices of the singular simplicial set, read as singular
simplices, is the alternating sum of its faces. -/
lemma bd_mapDomain_toC {Z : TopCat.{u}} (n : ℕ) (c : Simp Z (n + 1) →₀ ℤ) :
    bd ℤ n (Finsupp.mapDomain (fun ρ ↦ (SingularCochain.simplexEquiv _ _ ρ : Simplex Z (n + 1))) c) =
      Finsupp.mapDomain (fun ρ ↦ (SingularCochain.simplexEquiv _ _ ρ : Simplex Z n))
        (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          Finsupp.mapDomain ((TopCat.toSSet.obj Z).δ i) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    rw [Finsupp.mapDomain_add, map_add, hc, hd, ← Finsupp.mapDomain_add]
    simp only [Finsupp.mapDomain_add, smul_add, Finset.sum_add_distrib]
  | single ρ a =>
    rw [Finsupp.mapDomain_single, ← mul_one a, ← smul_eq_mul, ← Finsupp.smul_single, map_smul,
      bd_single, Finsupp.mapDomain_finsetSum]
    simp only [Finsupp.mapDomain_smul, Finsupp.mapDomain_single, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [smul_comm, Finsupp.smul_single, smul_eq_mul, mul_one, borelMooreHomology.toSSetObjEquiv_δ]

/-- `toC` inverts the identification of singular simplices with simplices of the singular
simplicial set. -/
lemma toC_symm_apply {Z : TopCat.{u}} {n : ℕ} (σ : Simplex Z n) :
    SingularCochain.simplexEquiv _ _ ((SingularCochain.simplexEquiv Z n).symm σ) = σ :=
  Equiv.apply_symm_apply _ _

/-- The cross product of `SingularCochain.simplexEquiv _ _ σ` and `SingularCochain.simplexEquiv _ _ τ` is the simplicial cross product `crossSimplex n σ τ`,
read as a singular chain. -/
lemma crossSimplexChain_toC (n : ℕ) {p q : ℕ} (σ : Simp X p) (τ : Simp Y q) :
    crossSimplexChain n (SingularCochain.simplexEquiv _ _ σ) (SingularCochain.simplexEquiv _ _ τ) =
      Finsupp.mapDomain (fun ρ ↦ (SingularCochain.simplexEquiv _ _ ρ : Simplex (X × Y) n)) (crossSimplex n σ τ) := by
  simp [crossSimplexChain]

/-- The Leibniz rule for the cross product of singular simplices:
`∂ (σ × τ) = ∂ σ × τ + (-1) ^ p σ × ∂ τ`. -/
lemma bd_crossSimplexChain (n : ℕ) {p q : ℕ} (σ : Simplex X p) (τ : Simplex Y q) :
    bd ℤ n (crossSimplexChain (n + 1) σ τ) =
      cross n (p - 1) q (bdSub ℤ p (single σ 1)) (single τ 1) +
        (-1 : ℤ) ^ p • cross n p (q - 1) (single σ 1) (bdSub ℤ q (single τ 1)) := by
  set σ₀ := (SingularCochain.simplexEquiv X p).symm σ
  set τ₀ := (SingularCochain.simplexEquiv Y q).symm τ
  have hσ : SingularCochain.simplexEquiv _ _ σ₀ = σ := toC_symm_apply σ
  have hτ : SingularCochain.simplexEquiv _ _ τ₀ = τ := toC_symm_apply τ
  rw [crossSimplexChain]
  refine (bd_mapDomain_toC (Z := TopCat.of (X × Y)) n _).trans ?_
  rw [sum_δ_crossSimplex, Finsupp.mapDomain_add,
    Finsupp.mapDomain_smul, Finsupp.mapDomain_add, Finsupp.mapDomain_smul]
  congr 1
  · rcases p with _ | p
    · simp
    · rw [BorelMooreCross.mapDomain_pathSimplex_fst, bdSub_succ, bd_single, map_sum,
        LinearMap.sum_apply,
        Finsupp.mapDomain_finsetSum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [Finsupp.mapDomain_smul, map_smul, LinearMap.smul_apply, cross_single, one_mul,
        ← crossSimplexChain_toC, ← hσ, ← hτ]
      simp only [one_smul]
      rfl
  · congr 1
    rcases q with _ | q
    · simp
    · rw [BorelMooreCross.mapDomain_pathSimplex_snd, bdSub_succ, bd_single, map_sum,
        Finsupp.mapDomain_finsetSum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [Finsupp.mapDomain_smul, map_smul, cross_single, one_mul,
        ← crossSimplexChain_toC, ← hσ, ← hτ]
      simp only [one_smul]
      rfl

/-- The Leibniz rule for the cross product of finite chains:
`∂ (c × d) = ∂ c × d + (-1) ^ p c × ∂ d`. -/
lemma bd_cross (n p q : ℕ) (c : Chain ℤ X p) (d : Chain ℤ Y q) :
    bd ℤ n (cross (n + 1) p q c d) =
      cross n (p - 1) q (bdSub ℤ p c) d + (-1 : ℤ) ^ p • cross n p (q - 1) c (bdSub ℤ q d) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c c' hc hc' =>
    simp only [map_add, LinearMap.add_apply, hc, hc', smul_add]
    abel
  | single σ a =>
    induction d using Finsupp.induction_linear with
    | zero => simp
    | add d d' hd hd' =>
      simp only [map_add, hd, hd', smul_add]
      abel
    | single τ b =>
      rw [← Finsupp.smul_single_one σ a, ← Finsupp.smul_single_one τ b]
      simp only [map_smul, LinearMap.smul_apply, cross_single, one_mul, one_smul,
        bd_crossSimplexChain, smul_add, smul_comm b ((-1 : ℤ) ^ p), smul_comm a ((-1 : ℤ) ^ p)]

/-- The Leibniz rule `bd_cross` for a first factor of degree `p + 1`. -/
lemma bd_cross_succ_left (n p q : ℕ) (c : Chain ℤ X (p + 1)) (d : Chain ℤ Y q) :
    bd ℤ n (cross (n + 1) (p + 1) q c d) =
      cross n p q (bd ℤ p c) d + (-1 : ℤ) ^ (p + 1) • cross n (p + 1) (q - 1) c (bdSub ℤ q d) :=
  bd_cross n (p + 1) q c d

/-- The Leibniz rule `bd_cross` for a second factor of degree `q + 1`. -/
lemma bd_cross_succ_right (n p q : ℕ) (c : Chain ℤ X p) (d : Chain ℤ Y (q + 1)) :
    bd ℤ n (cross (n + 1) p (q + 1) c d) =
      cross n (p - 1) (q + 1) (bdSub ℤ p c) d + (-1 : ℤ) ^ p • cross n p q c (bd ℤ q d) :=
  bd_cross n p (q + 1) c d

/-- `c × d = ∑_{σ, τ} (c σ * d τ) • (σ × τ)`, summed over the supports of `c` and `d`. -/
lemma cross_apply (n p q : ℕ) (c : Chain ℤ X p) (d : Chain ℤ Y q) :
    cross n p q c d = ∑ σ ∈ c.support, ∑ τ ∈ d.support, (c σ * d τ) • crossSimplexChain n σ τ := by
  simp only [cross, Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.sum_apply,
    LinearMap.smul_apply, Finset.smul_sum, mul_smul]

/-- The cross product `σ × τ` is a chain of `range σ × range τ`. -/
lemma crossSimplexChain_mem_inside (n : ℕ) {p q : ℕ} (σ : Simplex X p) (τ : Simplex Y q) :
    crossSimplexChain n σ τ ∈ inside ℤ n (range σ ×ˢ range τ) := by
  classical
  intro ρ hρ
  obtain ⟨ρ₀, hρ₀, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support (Finset.mem_coe.1 hρ))
  have h := singularSimplexImage_subset_of_mem_support n _ _ (Finsupp.mem_support_iff.1 hρ₀)
  change range (SingularCochain.simplexEquiv _ n ρ₀) ⊆ _
  rw [range_simplexEquiv]
  refine h.trans (Set.prod_mono ?_ ?_)
  · rw [← range_simplexEquiv, Equiv.apply_symm_apply]
  · rw [← range_simplexEquiv, Equiv.apply_symm_apply]

/-- The cross product of a chain of `A` and a chain of `B` is a chain of `A × B`. -/
lemma cross_mem_inside (n : ℕ) {p q : ℕ} {A : Set X} {B : Set Y} {c : Chain ℤ X p}
    {d : Chain ℤ Y q} (hc : c ∈ inside ℤ p A) (hd : d ∈ inside ℤ q B) :
    cross n p q c d ∈ inside ℤ n (A ×ˢ B) := by
  rw [cross_apply]
  refine Submodule.sum_mem _ fun σ hσ ↦ Submodule.sum_mem _ fun τ hτ ↦ Submodule.smul_mem _ _ ?_
  refine supported_mono ?_ (crossSimplexChain_mem_inside n σ τ)
  intro ρ (hρ : range ρ ⊆ _)
  exact hρ.trans (Set.prod_mono (hc (Finset.mem_coe.2 hσ)) (hd (Finset.mem_coe.2 hτ)))

end Cross

section Restriction

variable {R : Type*} [CommRing R] {Z : Type*} [TopologicalSpace Z] {U : Set Z}

/-- The bad part of a chain of `U` is zero. -/
lemma badChain_eq_zero_of_mem_inside {N n : ℕ} {c : Chain R Z n} (hc : c ∈ inside R n U) :
    badChain R U N n c = 0 := by
  induction N with
  | zero => rw [badChain_zero, badProj_eq_zero_of_mem_inside hc]
  | succ N ih => rw [badChain_succ, ih, map_zero, map_zero]

/-- The homotopy `D_N` of the subdivision towards `U` vanishes on chains of `U`. -/
lemma towardsHomotopy_eq_zero_of_mem_inside {N n : ℕ} {c : Chain R Z n}
    (hc : c ∈ inside R n U) : towardsHomotopy R U N n c = 0 := by
  rw [towardsHomotopy, LinearMap.sum_apply]
  exact Finset.sum_eq_zero fun i _ ↦ by
    rw [LinearMap.comp_apply, badChain_eq_zero_of_mem_inside hc, map_zero]

/-- The chain map `ρ_N` of the subdivision towards `U` fixes chains of `U`. -/
lemma towardsChainMap_eq_self_of_mem_inside {N n : ℕ} {c : Chain R Z n}
    (hc : c ∈ inside R n U) : towardsChainMap R U N n c = c := by
  cases n with
  | zero => rw [towardsChainMap_zero_apply, towardsHomotopy_eq_zero_of_mem_inside hc, map_zero,
      sub_zero]
  | succ n => rw [towardsChainMap_succ_apply, towardsHomotopy_eq_zero_of_mem_inside hc,
      towardsHomotopy_eq_zero_of_mem_inside (bd_mem_inside hc), map_zero, sub_zero, sub_zero]

/-- The restriction of a simplex lying in `U` is the simplex itself. -/
lemma restrCoeff_of_range_subset {n : ℕ} {μ : Simplex Z n} (hμ : range μ ⊆ U)
    (ω : Simplex Z n) : restrCoeff R U μ ω = single μ 1 ω := by
  have h : ∀ N, goodPart R U N μ = single μ 1 := fun N ↦ by
    rw [goodPart, towardsChainMap_eq_self_of_mem_inside (single_mem_supported R (1 : R) hμ),
      goodProj_single, ite_eq_left hμ]
  rw [restrCoeff_eq (N₀ := 0) fun N _ ↦ by rw [h, h], h]

/-- The restriction of a chain lying in `U` is the chain itself. -/
lemma restrFin_of_mem_inside {n : ℕ} {c : Chain R Z n} (hc : c ∈ inside R n U)
    (ω : Simplex Z n) : restrFin R U c ω = c ω := by
  classical
  calc restrFin R U c ω = c.sum fun ν a ↦ single ν a ω :=
        Finset.sum_congr rfl fun ν hν ↦ by
          change c ν * restrCoeff R U ν ω = single ν (c ν) ω
          rw [restrCoeff_of_range_subset (hc (Finset.mem_coe.2 hν)), single_apply, single_apply]
          split_ifs <;> simp
    _ = c ω := by rw [← Finsupp.sum_apply, Finsupp.sum_single]

/-- A chain lies in the union of the images of the simplices of its support. -/
lemma mem_inside_biUnion_range {n : ℕ} (c : Chain R Z n) :
    c ∈ inside R n (⋃ ν ∈ c.support, range ν) :=
  fun _ hν ↦ subset_biUnion_of_mem (u := fun ν : Simplex Z n ↦ range ν) hν

/-- The union of the images of the simplices of the support of a chain is compact. -/
lemma isCompact_biUnion_range {n : ℕ} (c : Chain R Z n) :
    IsCompact (⋃ ν ∈ c.support, range ν) :=
  c.support.isCompact_biUnion fun ν _ ↦ isCompact_range ν.continuous

open Classical in
/-- Restriction of finite chains commutes with the boundary, at a simplex of `U`. -/
lemma restrFin_bd [T2Space Z] (hU : IsOpen U) {n : ℕ} (c : Chain R Z (n + 1))
    {ω : Simplex Z n} (hω : range ω ⊆ U) :
    restrFin R U (bd R n c) ω = ∑ i : Fin (n + 2), (-1 : R) ^ (i : ℕ) *
      ∑ᶠ ω' : Simplex Z (n + 1), (if ω'.comp (face n i) = ω then restrFin R U c ω' else 0) := by
  set A := ⋃ ν ∈ c.support, range ν
  obtain ⟨V, W, hV, -, hAV, hωW, hVW⟩ := SeparatedNhds.of_isCompact_isCompact
    ((isCompact_biUnion_range c).inter_right hU.isClosed_compl) (isCompact_range ω.continuous)
    (Set.disjoint_left.2 fun _ hx hxω ↦ hx.2 (hω hxω))
  have hωW' : (range ω ∩ W).Nonempty := ⟨_, ⟨stdSimplex.vertex 0, rfl⟩, hωW ⟨_, rfl⟩⟩
  have hcA := mem_inside_biUnion_range c
  have hc := support_subset_of_mem_inside hcA hAV
  have hbc := support_subset_of_mem_inside (bd_mem_inside hcA) hAV
  obtain ⟨M₁, hM₁⟩ := exists_restrFin_eq (R := R) hU c hV hVW hc
  obtain ⟨M₂, hM₂⟩ := exists_restrFin_eq (R := R) hU (bd R n c) hV hVW hbc
  obtain ⟨M₃, hM₃⟩ := exists_badChain_mem_inside (R := R) hU c hV hc
  set m := max M₁ (max M₂ M₃)
  rw [bd_apply_eq_finsum (goodProj R U (n + 1) (towardsChainMap R U m (n + 1) c))
    (restrFin R U c) ω hωW' fun ω' hω' ↦ hM₁ m (le_max_left _ _) ω' hω',
    bd_goodProj_towardsChainMap, Finsupp.sub_apply,
    eq_zero_of_mem_inside (goodProj_mem_inside (bd_mem_inside (hM₃ m (by omega))))
      (not_range_subset_of_disjoint hVW hωW'), sub_zero, hM₂ m (by omega) ω hωW']

end Restriction

section Homotopy

variable {X Y : TopCat.{u}} (U : Set X) (V : Set Y)

/-- The chain homotopy `h (c, d) = D_N c × d + (-1) ^ p ρ_N c × D'_N d` between `c × d` and
`ρ_N c × ρ'_N d`, where `ρ_N`, `D_N` (resp. `ρ'_N`, `D'_N`) are the chain map and the homotopy of
the subdivision towards `U` (resp. `V`). -/
def crossHomotopyChain (N m p q : ℕ) (c : Chain ℤ X p) (d : Chain ℤ Y q) : Chain ℤ (X × Y) m :=
  cross m (p + 1) q (towardsHomotopy ℤ U N p c) d +
    (-1 : ℤ) ^ p • cross m p (q + 1) (towardsChainMap ℤ U N p c) (towardsHomotopy ℤ V N q d)

variable {U V}

/-- The chain map `ρ_N` commutes with the boundary `bdSub`. -/
lemma bdSub_towardsChainMap (N p : ℕ) (c : Chain ℤ X p) :
    bdSub ℤ p (towardsChainMap ℤ U N p c) = towardsChainMap ℤ U N (p - 1) (bdSub ℤ p c) := by
  rcases p with _ | p
  · simp
  · exact bd_towardsChainMap N p c

/-- `c × d = ρ_N c × d + ∂ D_N c × d + D_N ∂ c × d`. -/
lemma cross_eq_towardsChainMap_left (N m p q : ℕ) (c : Chain ℤ X p) (d : Chain ℤ Y q) :
    cross m p q c d = cross m p q (towardsChainMap ℤ U N p c) d +
      cross m p q (bd ℤ p (towardsHomotopy ℤ U N p c)) d +
      cross m (p - 1 + 1) q (towardsHomotopy ℤ U N (p - 1) (bdSub ℤ p c)) d := by
  rcases p with _ | p
  · simp only [towardsChainMap_zero_apply, bdSub_zero, LinearMap.zero_apply, map_zero,
      LinearMap.zero_apply, add_zero, map_sub, LinearMap.sub_apply, sub_add_cancel]
  · have e : cross m (p + 1 - 1 + 1) q (towardsHomotopy ℤ U N (p + 1 - 1) (bdSub ℤ (p + 1) c)) d =
        cross m (p + 1) q (towardsHomotopy ℤ U N p (bd ℤ p c)) d := rfl
    rw [e, towardsChainMap_succ_apply, map_sub, map_sub, LinearMap.sub_apply, LinearMap.sub_apply]
    abel

/-- `c × d = c × ρ'_N d + c × ∂ D'_N d + c × D'_N ∂ d`. -/
lemma cross_eq_towardsChainMap_right (N m p q : ℕ) (c : Chain ℤ X p) (d : Chain ℤ Y q) :
    cross m p q c d = cross m p q c (towardsChainMap ℤ V N q d) +
      cross m p q c (bd ℤ q (towardsHomotopy ℤ V N q d)) +
      cross m p (q - 1 + 1) c (towardsHomotopy ℤ V N (q - 1) (bdSub ℤ q d)) := by
  rcases q with _ | q
  · simp only [towardsChainMap_zero_apply, bdSub_zero, LinearMap.zero_apply, map_zero,
      add_zero, map_sub, sub_add_cancel]
  · have e : cross m p (q + 1 - 1 + 1) c (towardsHomotopy ℤ V N (q + 1 - 1) (bdSub ℤ (q + 1) d)) =
        cross m p (q + 1) c (towardsHomotopy ℤ V N q (bd ℤ q d)) := rfl
    rw [e, towardsChainMap_succ_apply, map_sub, map_sub]
    abel

/-- `(-1) ^ p • (-1) ^ p • x = x`. -/
lemma neg_one_pow_smul_neg_one_pow_smul {M : Type*} [AddCommGroup M] (p : ℕ) (x : M) :
    (-1 : ℤ) ^ p • (-1 : ℤ) ^ p • x = x := by
  rw [smul_smul, ← mul_pow, neg_mul_neg, one_mul, one_pow, one_smul]

/-- The chain homotopy identity
`c × d = ρ_N c × ρ'_N d + ∂ h (c, d) + h (∂ c, d) + (-1) ^ p h (c, ∂ d)`. -/
lemma cross_eq_add_bd_crossHomotopyChain (N m p q : ℕ) (c : Chain ℤ X p) (d : Chain ℤ Y q) :
    cross m p q c d =
      cross m p q (towardsChainMap ℤ U N p c) (towardsChainMap ℤ V N q d) +
        bd ℤ m (crossHomotopyChain U V N (m + 1) p q c d) +
        crossHomotopyChain U V N m (p - 1) q (bdSub ℤ p c) d +
        (-1 : ℤ) ^ p • crossHomotopyChain U V N m p (q - 1) c (bdSub ℤ q d) := by
  have h₁ := cross_eq_towardsChainMap_left (U := U) N m p q c d
  have h₂ := cross_eq_towardsChainMap_right (V := V) N m p q (towardsChainMap ℤ U N p c) d
  set E := cross m (p - 1) (q + 1) (towardsChainMap ℤ U N (p - 1) (bdSub ℤ p c))
    (towardsHomotopy ℤ V N q d) with hE_def
  have hE : (-1 : ℤ) ^ p • E + (-1 : ℤ) ^ (p - 1) • E = 0 := by
    rcases p with _ | p
    · simp [hE_def]
    · have e : (-1 : ℤ) ^ (p + 1 - 1) = (-1) ^ p := rfl
      rw [e, pow_succ, mul_neg_one, neg_smul, neg_add_cancel]
  rw [crossHomotopyChain, map_add, map_smul, bd_cross_succ_left, bd_cross_succ_right,
    bdSub_towardsChainMap, crossHomotopyChain, crossHomotopyChain, smul_add, smul_add,
    neg_one_pow_smul_neg_one_pow_smul, neg_one_pow_smul_neg_one_pow_smul, pow_succ, mul_neg_one,
    neg_smul, ← hE_def, h₁, h₂]
  refine sub_eq_zero.mp (neg_eq_zero.mp (Eq.trans ?_ hE))
  abel

/-- The chain homotopy `h_0` is zero. -/
lemma crossHomotopyChain_zero (m p q : ℕ) (c : Chain ℤ X p) (d : Chain ℤ Y q) :
    crossHomotopyChain U V 0 m p q c d = 0 := by
  simp [crossHomotopyChain, towardsHomotopy_zero]

/-- `h (c, d)` is bilinear. -/
def crossHomotopyBilin (U : Set X) (V : Set Y) (N m p q : ℕ) :
    Chain ℤ X p →ₗ[ℤ] Chain ℤ Y q →ₗ[ℤ] Chain ℤ (X × Y) m :=
  (cross (X := X) (Y := Y) m (p + 1) q).comp (towardsHomotopy ℤ U N p) +
    (-1 : ℤ) ^ p • ((cross (X := X) (Y := Y) m p (q + 1)).comp (towardsChainMap ℤ U N p)).compl₂
      (towardsHomotopy ℤ V N q)

/-- The bilinear map `crossHomotopyBilin` evaluates to `crossHomotopyChain`. -/
lemma crossHomotopyBilin_apply (N m p q : ℕ) (c : Chain ℤ X p) (d : Chain ℤ Y q) :
    crossHomotopyBilin U V N m p q c d = crossHomotopyChain U V N m p q c d := rfl

/-- A bilinear map on finitely supported functions is the sum of its values on pairs of basis
vectors, weighted by the coefficients. -/
lemma bilin_apply_eq_sum {α β M : Type*} [AddCommGroup M]
    (B : (α →₀ ℤ) →ₗ[ℤ] (β →₀ ℤ) →ₗ[ℤ] M) (c : α →₀ ℤ) (d : β →₀ ℤ) :
    B c d = ∑ σ ∈ c.support, ∑ τ ∈ d.support, (c σ * d τ) • B (single σ 1) (single τ 1) := by
  conv_lhs => rw [← Finsupp.sum_single c, ← Finsupp.sum_single d]
  simp only [Finsupp.sum, map_sum, LinearMap.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ ↦ Finset.sum_congr rfl fun τ _ ↦ ?_
  rw [← Finsupp.smul_single_one σ, ← Finsupp.smul_single_one τ, map_smul, map_smul,
    LinearMap.smul_apply, smul_smul, mul_comm]

/-- The step `h_{N+1} - h_N` of the chain homotopy. -/
lemma crossHomotopyChain_succ_sub (N m p q : ℕ) (c : Chain ℤ X p) (d : Chain ℤ Y q) :
    crossHomotopyChain U V (N + 1) m p q c d - crossHomotopyChain U V N m p q c d =
      cross m (p + 1) q (subdivHomotopy ℤ p (badChain ℤ U N p c)) d +
        (-1 : ℤ) ^ p • (cross m p (q + 1)
            (towardsChainMap ℤ U (N + 1) p c - towardsChainMap ℤ U N p c)
            (towardsHomotopy ℤ V (N + 1) q d) +
          cross m p (q + 1) (towardsChainMap ℤ U N p c)
            (subdivHomotopy ℤ q (badChain ℤ V N q d))) := by
  simp only [crossHomotopyChain, towardsHomotopy_succ, map_add, map_sub, LinearMap.add_apply,
    LinearMap.sub_apply, smul_add, smul_sub]
  abel

/-- The chain `h_N (σ, τ)` is a chain of `range σ × range τ`. -/
lemma crossHomotopyChain_mem_inside (N m : ℕ) {p q : ℕ} (σ : Simplex X p) (τ : Simplex Y q) :
    crossHomotopyChain U V N m p q (single σ 1) (single τ 1) ∈
      inside ℤ m (range σ ×ˢ range τ) :=
  add_mem (cross_mem_inside m (towardsHomotopy_mem_inside (single_mem_inside_range σ))
      (single_mem_inside_range τ))
    (Submodule.smul_of_tower_mem _ _ (cross_mem_inside m
      (towardsChainMap_mem_inside (single_mem_inside_range σ))
      (towardsHomotopy_mem_inside (single_mem_inside_range τ))))

end Homotopy

section Coefficients

variable {R : Type*} [CommRing R] {Z : Type*} [TopologicalSpace Z] {U : Set Z}

/-- The restriction of the zero chain is zero. -/
lemma restrFin_zero {n : ℕ} (ω : Simplex Z n) : restrFin R U 0 ω = 0 :=
  Finsupp.sum_zero_index

/-- Restriction of finite chains preserves differences. -/
lemma restrFin_sub {n : ℕ} (c d : Chain R Z n) (ω : Simplex Z n) :
    restrFin R U (c - d) ω = restrFin R U c ω - restrFin R U d ω := by
  have h := restrFin_add (U := U) (c - d) d ω
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

end Coefficients

section HomotopyCoeff

variable {X Y : TopCat.{u}} (U : Set X) (V : Set Y)

/-- The coefficient of `ω` in the restriction to `U × V` of the chain homotopy
`h (σ, τ) = ∑_N (h_{N+1} - h_N) (σ, τ)`, the limit of the chains `h_N (σ, τ)`. -/
def crossHomotopyCoeff (m : ℕ) {p q : ℕ} (σ : Simplex X p) (τ : Simplex Y q)
    (ω : Simplex (X × Y) m) : ℤ :=
  ∑ᶠ N : ℕ, restrFin ℤ (U ×ˢ V) (crossHomotopyChain U V (N + 1) m p q (single σ 1) (single τ 1) -
    crossHomotopyChain U V N m p q (single σ 1) (single τ 1)) ω

/-- The bilinear extension of `crossHomotopyCoeff` to finite chains. -/
def crossHomotopyFin (m p q : ℕ) (c : Chain ℤ X p) (d : Chain ℤ Y q) (ω : Simplex (X × Y) m) :
    ℤ :=
  c.sum fun σ a ↦ d.sum fun τ b ↦ a * b * crossHomotopyCoeff U V m σ τ ω

variable {U V}

/-- The restriction of `h_{N+1} (c, d) - h_N (c, d)` vanishes at a simplex meeting `G`, when the
bad parts of `c`, `d` and the step `ρ_{N+1} c - ρ_N c` lie in sets `V₁`, `V₂` with `V₁ × Y` and
`X × V₂` disjoint from `G`. -/
lemma restrFin_crossHomotopyChain_succ_sub_eq_zero {W : Set (X × Y)} {N m p q : ℕ}
    {c : Chain ℤ X p} {d : Chain ℤ Y q} {V₁ : Set X} {V₂ : Set Y} {G : Set (X × Y)}
    (hG₁ : Disjoint (V₁ ×ˢ univ) G) (hG₂ : Disjoint (univ ×ˢ V₂) G)
    (hX : badChain ℤ U N p c ∈ inside ℤ p V₁)
    (hρ : towardsChainMap ℤ U (N + 1) p c - towardsChainMap ℤ U N p c ∈ inside ℤ p V₁)
    (hY : badChain ℤ V N q d ∈ inside ℤ q V₂) {ω : Simplex (X × Y) m}
    (hω : (range ω ∩ G).Nonempty) :
    restrFin ℤ W (crossHomotopyChain U V (N + 1) m p q c d -
      crossHomotopyChain U V N m p q c d) ω = 0 := by
  rw [crossHomotopyChain_succ_sub, restrFin_add, restrFin_smul, restrFin_add,
    restrFin_eq_zero_of_mem_inside hG₁ (cross_mem_inside m (subdivHomotopy_mem_inside hX)
      (mem_inside_univ d)) hω,
    restrFin_eq_zero_of_mem_inside hG₁ (cross_mem_inside m hρ (mem_inside_univ _)) hω,
    restrFin_eq_zero_of_mem_inside hG₂ (cross_mem_inside m (mem_inside_univ _)
      (subdivHomotopy_mem_inside hY)) hω]
  simp

variable [T2Space X] [T2Space Y]

/-- Near `G`, away from neighbourhoods `V₁`, `V₂` of the points of `σ`, `τ` outside `U`, `V`,
the homotopy coefficients are those of the restriction of `h_N (σ, τ)`, for all large `N`. -/
lemma exists_crossHomotopyCoeff_eq (hU : IsOpen U) (hV : IsOpen V) (m : ℕ) {p q : ℕ}
    (σ : Simplex X p) (τ : Simplex Y q) {V₁ : Set X} {V₂ : Set Y} (hV₁ : IsOpen V₁)
    (hV₂ : IsOpen V₂) (hσ : range σ ∩ Uᶜ ⊆ V₁) (hτ : range τ ∩ Vᶜ ⊆ V₂) {G : Set (X × Y)}
    (hG₁ : Disjoint (V₁ ×ˢ univ) G) (hG₂ : Disjoint (univ ×ˢ V₂) G) :
    ∃ N₀, ∀ N ≥ N₀, ∀ ω : Simplex (X × Y) m, (range ω ∩ G).Nonempty →
      crossHomotopyCoeff U V m σ τ ω =
        restrFin ℤ (U ×ˢ V) (crossHomotopyChain U V N m p q (single σ 1) (single τ 1)) ω := by
  obtain ⟨Nσ, hNσ⟩ := eventually_goodPart_sub_mem_inside (R := ℤ) hU σ hV₁ hσ
  obtain ⟨Nτ, hNτ⟩ := eventually_goodPart_sub_mem_inside (R := ℤ) hV τ hV₂ hτ
  set N₀ := max Nσ Nτ
  set f : ℕ → Simplex (X × Y) m → ℤ := fun N ω ↦
    restrFin ℤ (U ×ˢ V) (crossHomotopyChain U V N m p q (single σ 1) (single τ 1)) ω
  have hinc : ∀ N ≥ N₀, ∀ ω : Simplex (X × Y) m, (range ω ∩ G).Nonempty →
      f (N + 1) ω - f N ω = 0 := fun N hN ω hω ↦ by
    simp only [f]
    rw [← restrFin_sub]
    refine restrFin_crossHomotopyChain_succ_sub_eq_zero hG₁ hG₂
      (hNσ N (le_of_max_le_left hN)).2 ?_ (hNτ N (le_of_max_le_right hN)).2 hω
    rw [← sub_sub_sub_cancel_right _ _ (towardsChainMap ℤ U Nσ p (single σ 1))]
    exact sub_mem (hNσ (N + 1) (by omega)).1 (hNσ N (by omega)).1
  have hstab : ∀ N ≥ N₀, ∀ ω : Simplex (X × Y) m, (range ω ∩ G).Nonempty →
      f N ω = f N₀ ω := fun N hN ω hω ↦ by
    induction N, hN using Nat.le_induction with
    | base => rfl
    | succ N hN ih => rw [← ih, ← sub_eq_zero, hinc N hN ω hω]
  refine ⟨N₀, fun N hN ω hω ↦ ?_⟩
  rw [crossHomotopyCoeff, finsum_eq_sum_of_support_subset (s := Finset.range N₀) _ (fun i hi ↦ by
    rw [Finset.coe_range, mem_Iio]
    by_contra h
    exact hi (by dsimp only; rw [restrFin_sub]; exact hinc i (not_lt.1 h) ω hω))]
  simp_rw [restrFin_sub]
  rw [Finset.sum_range_sub (fun N ↦ f N ω), show f 0 ω = 0 by
    simp only [f, crossHomotopyChain_zero, restrFin_zero], sub_zero]
  exact (hstab N hN ω hω).symm

omit [T2Space X] [T2Space Y] in
/-- The homotopy coefficients `h (σ, τ)` are those of a chain of `U × V` inside `σ × τ`. -/
lemma range_subset_of_crossHomotopyCoeff_ne_zero {m p q : ℕ} {σ : Simplex X p}
    {τ : Simplex Y q} {ω : Simplex (X × Y) m} (h : crossHomotopyCoeff U V m σ τ ω ≠ 0) :
    range ω ⊆ (range σ ×ˢ range τ) ∩ (U ×ˢ V) := by
  obtain ⟨N, hN⟩ : ∃ N, restrFin ℤ (U ×ˢ V)
      (crossHomotopyChain U V (N + 1) m p q (single σ 1) (single τ 1) -
        crossHomotopyChain U V N m p q (single σ 1) (single τ 1)) ω ≠ 0 := by
    by_contra h'
    push Not at h'
    exact h (finsum_eq_zero_of_forall_eq_zero h')
  exact range_subset_of_restrFin_ne_zero (sub_mem (crossHomotopyChain_mem_inside _ _ σ τ)
    (crossHomotopyChain_mem_inside _ _ σ τ)) hN

/-- The homotopy coefficients `h (σ, τ)` are locally finite on `U × V`. -/
lemma exists_finite_crossHomotopyCoeff_ne_zero (hU : IsOpen U) (hV : IsOpen V) (m : ℕ)
    {p q : ℕ} (σ : Simplex X p) (τ : Simplex Y q) {x : X × Y} (hx : x ∈ U ×ˢ V) :
    ∃ G, IsOpen G ∧ x ∈ G ∧
      {ω | crossHomotopyCoeff U V m σ τ ω ≠ 0 ∧ (range ω ∩ G).Nonempty}.Finite := by
  classical
  obtain ⟨V₁, W₁, hV₁, hW₁, hσV₁, hxW₁, hVW₁⟩ :=
    separatedNhds_range_inter_compl hU σ isCompact_singleton (singleton_subset_iff.2 hx.1)
  obtain ⟨V₂, W₂, hV₂, hW₂, hτV₂, hxW₂, hVW₂⟩ :=
    separatedNhds_range_inter_compl hV τ isCompact_singleton (singleton_subset_iff.2 hx.2)
  obtain ⟨N₀, hN₀⟩ := exists_crossHomotopyCoeff_eq hU hV m σ τ hV₁ hV₂ hσV₁ hτV₂
    (Set.disjoint_prod.2 (Or.inl hVW₁)) (Set.disjoint_prod.2 (Or.inr hVW₂))
  set c := crossHomotopyChain U V N₀ m p q (single σ 1) (single τ 1)
  have h : ∀ ν ∈ c.support, ∃ W', IsOpen W' ∧ x ∈ W' ∧
      {ω | restrCoeff ℤ (U ×ˢ V) ν ω ≠ 0 ∧ (range ω ∩ W').Nonempty}.Finite :=
    fun ν _ ↦ exists_finite_restrCoeff_ne_zero (hU.prod hV) ν hx
  choose! Wf hWf using h
  refine ⟨(W₁ ×ˢ W₂) ∩ ⋂ ν ∈ c.support, Wf ν,
    (hW₁.prod hW₂).inter (isOpen_biInter_finset fun ν hν ↦ (hWf ν hν).1),
    ⟨⟨hxW₁ rfl, hxW₂ rfl⟩, mem_iInter₂.2 fun ν hν ↦ (hWf ν hν).2.1⟩, ?_⟩
  refine (c.support.finite_toSet.biUnion fun ν hν ↦ (hWf ν hν).2.2).subset ?_
  rintro ω ⟨hω, y, hy, hyW, hyW'⟩
  rw [hN₀ N₀ le_rfl ω ⟨y, hy, hyW⟩] at hω
  obtain ⟨ν, hν, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hω
  have h' : restrCoeff ℤ (U ×ˢ V) ν ω ≠ 0 := fun h0 ↦ hne (by simp only [h0, mul_zero])
  exact mem_iUnion₂.2 ⟨ν, hν, h', y, hy, mem_iInter₂.1 hyW' ν hν⟩

omit [T2Space X] [T2Space Y] in
/-- If, for the simplices of `c` and `d`, the coefficient of `h (σ, τ)` at `ω` is that of the
restriction of `h_N (σ, τ)`, then so is the coefficient of `h (c, d)`. -/
lemma crossHomotopyFin_eq {N m p q : ℕ} {c : Chain ℤ X p} {d : Chain ℤ Y q}
    {ω : Simplex (X × Y) m} (h : ∀ σ ∈ c.support, ∀ τ ∈ d.support,
      crossHomotopyCoeff U V m σ τ ω =
        restrFin ℤ (U ×ˢ V) (crossHomotopyChain U V N m p q (single σ 1) (single τ 1)) ω) :
    crossHomotopyFin U V m p q c d ω =
      restrFin ℤ (U ×ˢ V) (crossHomotopyChain U V N m p q c d) ω := by
  rw [← crossHomotopyBilin_apply, bilin_apply_eq_sum, restrFin_sum, crossHomotopyFin,
    Finsupp.sum]
  refine Finset.sum_congr rfl fun σ hσ ↦ ?_
  rw [restrFin_sum, Finsupp.sum]
  refine Finset.sum_congr rfl fun τ hτ ↦ ?_
  rw [restrFin_smul, crossHomotopyBilin_apply, h σ hσ τ hτ]

end HomotopyCoeff

section Identity

variable {X Y : TopCat.{u}} (U : Set X) (V : Set Y)

/-- The coefficient of `ω` in the cross product `σ|_U × τ|_V` of the restrictions, read in
`X × Y`. -/
def crossRestrCoeff (n : ℕ) {p q : ℕ} (σ : Simplex X p) (τ : Simplex Y q)
    (ω : Simplex (X × Y) n) : ℤ :=
  ∑ᶠ ab : Simplex X p × Simplex Y q,
    restrCoeff ℤ U σ ab.1 * restrCoeff ℤ V τ ab.2 * crossSimplexChain n ab.1 ab.2 ω

variable {U V}

/-- The boundary of a chain of `A` is a chain of `A`. -/
lemma bdSub_mem_inside {R : Type*} [CommRing R] {Z : Type*} [TopologicalSpace Z] {p : ℕ}
    {A : Set Z} {c : Chain R Z p} (hc : c ∈ inside R p A) : bdSub R p c ∈ inside R (p - 1) A := by
  rcases p with _ | p
  · exact zero_mem _
  · exact bd_mem_inside hc

/-- A simplex with nonzero coefficient in `a × b` lies in `range a × range b`. -/
lemma range_subset_of_crossSimplexChain_ne_zero {n p q : ℕ} {a : Simplex X p} {b : Simplex Y q}
    {ω : Simplex (X × Y) n} (h : crossSimplexChain n a b ω ≠ 0) :
    range ω ⊆ range a ×ˢ range b :=
  crossSimplexChain_mem_inside n a b (Finsupp.mem_support_iff.2 h)

variable [T2Space X] [T2Space Y]

/-- For large `N`, the coefficient of `ω` in the cross product of the good parts of `σ` and `τ`
is that of `σ|_U × τ|_V`, when the parts of `σ`, `τ` outside `U`, `V` lie in open sets `V₁`, `V₂`
disjoint from sets `W₁`, `W₂` containing the projections of `ω`. -/
lemma cross_goodPart_apply (hU : IsOpen U) (hV : IsOpen V) {n p q : ℕ} (σ : Simplex X p)
    (τ : Simplex Y q) {ω : Simplex (X × Y) n} {V₁ W₁ : Set X} {V₂ W₂ : Set Y}
    (hV₁ : IsOpen V₁) (hV₂ : IsOpen V₂) (hVW₁ : Disjoint V₁ W₁) (hVW₂ : Disjoint V₂ W₂)
    (hσV₁ : range σ ∩ Uᶜ ⊆ V₁) (hτV₂ : range τ ∩ Vᶜ ⊆ V₂) (hωW₁ : Prod.fst '' range ω ⊆ W₁)
    (hωW₂ : Prod.snd '' range ω ⊆ W₂) :
    ∃ M, ∀ N ≥ M, cross n p q (goodPart ℤ U N σ) (goodPart ℤ V N τ) ω =
      crossRestrCoeff U V n σ τ ω := by
  classical
  obtain ⟨Mσ, hMσ⟩ := exists_restrCoeff_eq_goodPart_of_disjoint (R := ℤ) hU σ hV₁ hVW₁ hσV₁
  obtain ⟨Mτ, hMτ⟩ := exists_restrCoeff_eq_goodPart_of_disjoint (R := ℤ) hV τ hV₂ hVW₂ hτV₂
  refine ⟨max Mσ Mτ, fun N hN ↦ ?_⟩
  set gσ := goodPart ℤ U N σ
  set gτ := goodPart ℤ V N τ
  have hterm : ∀ ab : Simplex X p × Simplex Y q,
      restrCoeff ℤ U σ ab.1 * restrCoeff ℤ V τ ab.2 * crossSimplexChain n ab.1 ab.2 ω =
        gσ ab.1 * gτ ab.2 * crossSimplexChain n ab.1 ab.2 ω := by
    rintro ⟨a, b⟩
    by_cases h : crossSimplexChain n a b ω = 0
    · simp [h]
    have hsub := range_subset_of_crossSimplexChain_ne_zero h
    set t := ω (stdSimplex.vertex 0)
    have ht : t ∈ range ω := ⟨_, rfl⟩
    rw [hMσ N (le_of_max_le_left hN) a ⟨t.1, (hsub ht).1, hωW₁ ⟨t, ht, rfl⟩⟩,
      hMτ N (le_of_max_le_right hN) b ⟨t.2, (hsub ht).2, hωW₂ ⟨t, ht, rfl⟩⟩]
  rw [crossRestrCoeff, finsum_congr hterm, finsum_eq_sum_of_support_subset
    (s := gσ.support ×ˢ gτ.support) _ (fun ab hab ↦ by
      rw [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_coe,
        Finsupp.mem_support_iff, Finsupp.mem_support_iff]
      rw [Function.mem_support] at hab
      exact ⟨fun h0 ↦ hab (by simp [h0]), fun h0 ↦ hab (by simp [h0])⟩),
    Finset.sum_product, cross_apply, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [Finsupp.smul_apply, smul_eq_mul]

open Classical in
/-- **The homotopy identity**: for a simplex `ω` of `U × V`,
`(σ × τ)|_{U × V} - σ|_U × τ|_V = ∂ h (σ, τ) + h (∂ σ, τ) + (-1) ^ p h (σ, ∂ τ)` at `ω`. -/
theorem restrFin_crossSimplexChain_sub_crossRestrCoeff (hU : IsOpen U) (hV : IsOpen V)
    {n p q : ℕ} (σ : Simplex X p) (τ : Simplex Y q) {ω : Simplex (X × Y) n}
    (hω : range ω ⊆ U ×ˢ V) :
    restrFin ℤ (U ×ˢ V) (crossSimplexChain n σ τ) ω - crossRestrCoeff U V n σ τ ω =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) * ∑ᶠ ω' : Simplex (X × Y) (n + 1),
          (if ω'.comp (face n i) = ω then crossHomotopyCoeff U V (n + 1) σ τ ω' else 0) +
        crossHomotopyFin U V n (p - 1) q (bdSub ℤ p (single σ 1)) (single τ 1) ω +
        (-1 : ℤ) ^ p *
          crossHomotopyFin U V n p (q - 1) (single σ 1) (bdSub ℤ q (single τ 1)) ω := by
  have hK := isCompact_range ω.continuous
  obtain ⟨V₁, W₁, hV₁, -, hσV₁, hKW₁, hVW₁⟩ := separatedNhds_range_inter_compl hU σ
    (hK.image continuous_fst) (fun _ ⟨_, hy, h⟩ ↦ h ▸ (hω hy).1)
  obtain ⟨V₂, W₂, hV₂, -, hτV₂, hKW₂, hVW₂⟩ := separatedNhds_range_inter_compl hV τ
    (hK.image continuous_snd) (fun _ ⟨_, hy, h⟩ ↦ h ▸ (hω hy).2)
  set G := W₁ ×ˢ W₂
  have hG₁ : Disjoint (V₁ ×ˢ univ) G := Set.disjoint_prod.2 (Or.inl hVW₁)
  have hG₂ : Disjoint (univ ×ˢ V₂) G := Set.disjoint_prod.2 (Or.inr hVW₂)
  have hωG : (range ω ∩ G).Nonempty := ⟨_, ⟨stdSimplex.vertex 0, rfl⟩,
    hKW₁ ⟨_, ⟨_, rfl⟩, rfl⟩, hKW₂ ⟨_, ⟨_, rfl⟩, rfl⟩⟩
  -- the stages at which the coefficients near `ω` have stabilized
  obtain ⟨Na, ha⟩ := exists_crossHomotopyCoeff_eq hU hV (n + 1) σ τ hV₁ hV₂ hσV₁ hτV₂ hG₁ hG₂
  have hfσ := support_subset_of_mem_inside
    (bdSub_mem_inside (single_mem_inside_range (R := ℤ) σ)) hσV₁
  have hfτ := support_subset_of_mem_inside
    (bdSub_mem_inside (single_mem_inside_range (R := ℤ) τ)) hτV₂
  have hbσ : ∀ σ' ∈ (bdSub ℤ p (single σ 1)).support, ∃ N₀, ∀ N ≥ N₀,
      ∀ ω' : Simplex (X × Y) n, (range ω' ∩ G).Nonempty →
        crossHomotopyCoeff U V n σ' τ ω' = restrFin ℤ (U ×ˢ V)
          (crossHomotopyChain U V N n (p - 1) q (single σ' 1) (single τ 1)) ω' :=
    fun σ' hσ' ↦ exists_crossHomotopyCoeff_eq hU hV n σ' τ hV₁ hV₂ (hfσ σ' hσ') hτV₂ hG₁ hG₂
  have hbτ : ∀ τ' ∈ (bdSub ℤ q (single τ 1)).support, ∃ N₀, ∀ N ≥ N₀,
      ∀ ω' : Simplex (X × Y) n, (range ω' ∩ G).Nonempty →
        crossHomotopyCoeff U V n σ τ' ω' = restrFin ℤ (U ×ˢ V)
          (crossHomotopyChain U V N n p (q - 1) (single σ 1) (single τ' 1)) ω' :=
    fun τ' hτ' ↦ exists_crossHomotopyCoeff_eq hU hV n σ τ' hV₁ hV₂ hσV₁ (hfτ τ' hτ') hG₁ hG₂
  choose! Nσ hNσ using hbσ
  choose! Nτ hNτ using hbτ
  obtain ⟨Mg, hMg⟩ := cross_goodPart_apply (n := n) hU hV σ τ hV₁ hV₂ hVW₁ hVW₂ hσV₁ hτV₂ hKW₁ hKW₂
  obtain ⟨Bσ, hBσ⟩ := eventually_goodPart_sub_mem_inside (R := ℤ) hU σ hV₁ hσV₁
  obtain ⟨Bτ, hBτ⟩ := eventually_goodPart_sub_mem_inside (R := ℤ) hV τ hV₂ hτV₂
  set N := max (max Na Mg) (max (max Bσ Bτ)
    (max ((bdSub ℤ p (single σ 1)).support.sup Nσ) ((bdSub ℤ q (single τ 1)).support.sup Nτ)))
  have hN₅ : ∀ σ' ∈ (bdSub ℤ p (single σ 1)).support, Nσ σ' ≤ N := fun σ' h ↦
    (Finset.le_sup (f := Nσ) h).trans (by omega)
  have hN₆ : ∀ τ' ∈ (bdSub ℤ q (single τ 1)).support, Nτ τ' ≤ N := fun τ' h ↦
    (Finset.le_sup (f := Nτ) h).trans (by omega)
  -- the identity of chains at the stage `N`, restricted to `U × V` at `ω`
  have hst := congrArg (fun c ↦ restrFin ℤ (U ×ˢ V) c ω)
    (cross_eq_add_bd_crossHomotopyChain (U := U) (V := V) N n p q (single σ 1) (single τ 1))
  simp only [restrFin_add, restrFin_smul, cross_single, one_mul, one_smul] at hst
  rw [restrFin_bd (hU.prod hV) _ hω] at hst
  have e₂ : ∀ i : Fin (n + 2), ∑ᶠ ω' : Simplex (X × Y) (n + 1),
      (if ω'.comp (face n i) = ω then restrFin ℤ (U ×ˢ V)
        (crossHomotopyChain U V N (n + 1) p q (single σ 1) (single τ 1)) ω' else 0) =
      ∑ᶠ ω' : Simplex (X × Y) (n + 1),
        (if ω'.comp (face n i) = ω then crossHomotopyCoeff U V (n + 1) σ τ ω' else 0) :=
    fun i ↦ finsum_congr fun ω' ↦ by
      split_ifs with h
      · exact (ha N (by omega) ω' (range_inter_nonempty_of_comp hωG h)).symm
      · rfl
  have e₃ : crossHomotopyFin U V n (p - 1) q (bdSub ℤ p (single σ 1)) (single τ 1) ω =
      restrFin ℤ (U ×ˢ V) (crossHomotopyChain U V N n (p - 1) q (bdSub ℤ p (single σ 1))
        (single τ 1)) ω :=
    crossHomotopyFin_eq fun σ' hσ' τ' hτ' ↦ by
      rw [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at hτ'
      subst hτ'
      exact hNσ σ' hσ' N (hN₅ σ' hσ') ω hωG
  have e₄ : crossHomotopyFin U V n p (q - 1) (single σ 1) (bdSub ℤ q (single τ 1)) ω =
      restrFin ℤ (U ×ˢ V) (crossHomotopyChain U V N n p (q - 1) (single σ 1)
        (bdSub ℤ q (single τ 1))) ω :=
    crossHomotopyFin_eq fun σ' hσ' τ' hτ' ↦ by
      rw [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at hσ'
      subst hσ'
      exact hNτ τ' hτ' N (hN₆ τ' hτ') ω hωG
  -- the main term: `ρ_N σ × ρ'_N τ` restricts near `ω` to `σ|_U × τ|_V`
  have e₁ : restrFin ℤ (U ×ˢ V) (cross n p q (towardsChainMap ℤ U N p (single σ 1))
      (towardsChainMap ℤ V N q (single τ 1))) ω = crossRestrCoeff U V n σ τ ω := by
    set ρσ := towardsChainMap ℤ U N p (single σ 1)
    set ρτ := towardsChainMap ℤ V N q (single τ 1)
    have hσs : ρσ = goodPart ℤ U N σ + badChain ℤ U N p (single σ 1) := by
      rw [goodPart, ← badProj_towardsChainMap, goodProj_add_badProj]
    have hτs : ρτ = goodPart ℤ V N τ + badChain ℤ V N q (single τ 1) := by
      rw [goodPart, ← badProj_towardsChainMap, goodProj_add_badProj]
    have hsplit : cross n p q ρσ ρτ = cross n p q (goodPart ℤ U N σ) (goodPart ℤ V N τ) +
        cross n p q (goodPart ℤ U N σ) (badChain ℤ V N q (single τ 1)) +
        cross n p q (badChain ℤ U N p (single σ 1)) ρτ := by
      rw [hσs, map_add, LinearMap.add_apply, hτs, map_add]
    rw [hsplit, restrFin_add, restrFin_add,
      restrFin_eq_zero_of_mem_inside hG₂ (cross_mem_inside n (mem_inside_univ _)
        (hBτ N (by omega)).2) hωG,
      restrFin_eq_zero_of_mem_inside hG₁ (cross_mem_inside n (hBσ N (by omega)).2
        (mem_inside_univ _)) hωG, add_zero, add_zero,
      restrFin_of_mem_inside (c := cross n p q (goodPart ℤ U N σ) (goodPart ℤ V N τ))
        (cross_mem_inside n (goodProj_mem_inside_self _) (goodProj_mem_inside_self _)),
      hMg N (by omega)]
  rw [hst, e₁, e₃, e₄]
  simp only [e₂]
  ring

end Identity

end SingularChain

namespace borelMooreHomology

open SingularChain LocallyFiniteChain BorelMooreCross

section prodOpens

variable {X Y : TopCat.{u}} (U : TopologicalSpace.Opens X) (V : TopologicalSpace.Opens Y)

/-- The product `U × V` of open subsets `U ⊆ X`, `V ⊆ Y`, an open subset of `X × Y`. -/
def prodOpens : TopologicalSpace.Opens (TopCat.of (X × Y)) :=
  ⟨(U : Set X) ×ˢ (V : Set Y), U.isOpen.prod V.isOpen⟩

@[simp]
lemma coe_prodOpens : (prodOpens U V : Set (X × Y)) = (U : Set X) ×ˢ (V : Set Y) := rfl

@[simp]
lemma mem_prodOpens {x : X × Y} : x ∈ prodOpens U V ↔ x.1 ∈ U ∧ x.2 ∈ V := Iff.rfl

/-- The homeomorphism of the open subset `U × V` of `X × Y` with the product of the spaces `U`
and `V`. -/
def prodOpensHomeo : prodOpens U V ≃ₜ (U × V) := Homeomorph.Set.prod (U : Set X) (V : Set Y)

/-- The homeomorphism `prodOpensHomeo`, as a morphism of spaces. -/
def prodOpensMap : TopCat.of (prodOpens U V) ⟶ TopCat.of (TopCat.of U × TopCat.of V) :=
  TopCat.ofHom ⟨prodOpensHomeo U V, (prodOpensHomeo U V).continuous⟩

/-- The inverse of `prodOpensMap`. -/
def prodOpensInv : TopCat.of (TopCat.of U × TopCat.of V) ⟶ TopCat.of (prodOpens U V) :=
  TopCat.ofHom ⟨(prodOpensHomeo U V).symm, (prodOpensHomeo U V).symm.continuous⟩

/-- `prodOpensMap` is a proper map. -/
lemma isProperMap_prodOpensMap : IsProperMap (prodOpensMap U V) := by
  change IsProperMap (prodOpensHomeo U V)
  exact (prodOpensHomeo U V).isProperMap

/-- On singular simplices, `prodOpensMap` is a left inverse of `prodOpensInv`. -/
lemma prodOpensMap_prodOpensInv_app {n : ℕ}
    (ν : Simp (TopCat.of (TopCat.of U × TopCat.of V)) n) :
    (TopCat.toSSet.map (prodOpensMap U V)).app _ ((TopCat.toSSet.map (prodOpensInv U V)).app _ ν) =
      ν := by
  apply toC_injective
  rfl

/-- On singular simplices, `prodOpensInv` is a left inverse of `prodOpensMap`. -/
lemma prodOpensInv_prodOpensMap_app {n : ℕ} (μ : Simp (TopCat.of (prodOpens U V)) n) :
    (TopCat.toSSet.map (prodOpensInv U V)).app _ ((TopCat.toSSet.map (prodOpensMap U V)).app _ μ) =
      μ := by
  apply toC_injective
  rfl

/-- The inclusion of an open subset, as a morphism of spaces. -/
def inclHom {Z : TopCat.{u}} (W : TopologicalSpace.Opens Z) : TopCat.of W ⟶ Z :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- A singular simplex of `U × V`, as a singular simplex of `X × Y`. -/
def inclProdSimplex {n : ℕ} (ν : Simp (TopCat.of (TopCat.of U × TopCat.of V)) n) :
    Simplex (X × Y) n :=
  SingularCochain.simplexEquiv _ _ ((TopCat.toSSet.map (prodHom (inclHom U) (inclHom V))).app _ ν)

/-- `inclProdSimplex` is injective. -/
lemma inclProdSimplex_injective (n : ℕ) :
    Function.Injective (inclProdSimplex U V (n := n)) := fun ν ν' h ↦ by
  apply toC_injective
  ext t : 1
  obtain ⟨t, rfl⟩ := (SingularChain.stdSimplexHomeo (Fin (n + 1))).surjective t
  have := congrArg (fun f : Simplex (X × Y) n ↦ f t) h
  exact Prod.ext (Subtype.val_injective (congrArg Prod.fst this))
    (Subtype.val_injective (congrArg Prod.snd this))

/-- The image of `inclProdSimplex U V ν` is the image of `ν` under the inclusion of `U × V`. -/
lemma range_inclProdSimplex {n : ℕ} (ν : Simp (TopCat.of (TopCat.of U × TopCat.of V)) n) :
    range (inclProdSimplex U V ν) = (prodHom (inclHom U) (inclHom V)) '' singularSimplexImage _ ν :=
  (range_simplexEquiv _).trans (singularSimplexImage_map _ ν)

/-- The image of `inclProdSimplex U V ν` lies in `U × V`. -/
lemma range_inclProdSimplex_subset {n : ℕ}
    (ν : Simp (TopCat.of (TopCat.of U × TopCat.of V)) n) :
    range (inclProdSimplex U V ν) ⊆ (U : Set X) ×ˢ (V : Set Y) := by
  rintro _ ⟨t, rfl⟩
  exact ⟨(SingularCochain.simplexEquiv _ _ ν t).1.2, (SingularCochain.simplexEquiv _ _ ν t).2.2⟩

/-- A singular simplex of `X × Y` with image in `U × V` comes from a simplex of `U × V`. -/
lemma mem_range_inclProdSimplex {n : ℕ} {ω : Simplex (X × Y) n}
    (h : range ω ⊆ (U : Set X) ×ˢ (V : Set Y)) : ω ∈ range (inclProdSimplex U V (n := n)) :=
  ⟨(SingularCochain.simplexEquiv (TopCat.of (TopCat.of U × TopCat.of V)) n).symm
    ⟨fun t ↦ (⟨(ω t).1, (h ⟨t, rfl⟩).1⟩, ⟨(ω t).2, (h ⟨t, rfl⟩).2⟩),
      ((continuous_fst.comp ω.continuous).subtype_mk _).prodMk
        ((continuous_snd.comp ω.continuous).subtype_mk _)⟩, by
    ext t : 1
    rw [show ∀ ν, inclProdSimplex U V ν = (prodHom (inclHom U) (inclHom V)).hom.comp
      (SingularCochain.simplexEquiv _ n ν) from fun _ ↦ rfl, Equiv.apply_symm_apply]
    rfl⟩

/-- `inclProdSimplex` commutes with faces. -/
lemma inclProdSimplex_δ {n : ℕ} (i : Fin (n + 2))
    (ν : Simp (TopCat.of (TopCat.of U × TopCat.of V)) (n + 1)) :
    inclProdSimplex U V ((TopCat.toSSet.obj _).δ i ν) = (inclProdSimplex U V ν).comp (face n i) := by
  change SingularCochain.simplexEquiv _ n ((TopCat.toSSet.obj _).δ i
    ((TopCat.toSSet.map (prodHom (inclHom U) (inclHom V))).app _ ν)) = _
  rw [toSSetObjEquiv_δ]
  rfl

/-- `inclSimplex W a` is the image of `a` under `inclHom W`. -/
lemma inclSimplex_eq_toC_map {Z : TopCat.{u}} (W : TopologicalSpace.Opens Z) {n : ℕ}
    (a : Simp (TopCat.of W) n) :
    inclSimplex W a = SingularCochain.simplexEquiv _ _ ((TopCat.toSSet.map (inclHom W)).app _ a) :=
  rfl

/-- The cross product of simplices of `U` and `V`, read in `X × Y`. -/
lemma crossSimplexChain_inclSimplex (n : ℕ) {p q : ℕ} (a : Simp (TopCat.of U) p)
    (b : Simp (TopCat.of V) q) :
    crossSimplexChain n (inclSimplex U a) (inclSimplex V b) =
      Finsupp.mapDomain (inclProdSimplex U V) (crossSimplex n a b) := by
  rw [inclSimplex_eq_toC_map, inclSimplex_eq_toC_map, crossSimplexChain_toC,
    ← mapDomain_crossSimplex, ← Finsupp.mapDomain_comp]
  rfl

end prodOpens

end borelMooreHomology

namespace LocallyFiniteChain

section prodKernel

variable {X X' Y Y' : Type*} [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y]
  [TopologicalSpace Y'] {S S' T T' : Type*} {car : S → Set X} {car' : T → Set X'}
  {carS : S' → Set Y} {carS' : T' → Set Y'} {ι : X' → X} {ι' : Y' → Y}
  {k : S → T → ℤ} {k' : S' → T' → ℤ}

/-- The product `(σ, τ), (a, b) ↦ k σ a * k' τ b` of two integer kernels. -/
def prodKernel (k : S → T → ℤ) (k' : S' → T' → ℤ) : S × S' → T × T' → ℤ :=
  fun st ab ↦ k st.1 ab.1 * k' st.2 ab.2

/-- The product of two admissible kernels is admissible. -/
lemma IsAdmissibleKernel.prod (hk : IsAdmissibleKernel ι car car' k)
    (hk' : IsAdmissibleKernel ι' carS carS' k') :
    IsAdmissibleKernel (Prod.map ι ι') (prodCarrier car carS) (prodCarrier car' carS')
      (prodKernel k k') where
  continuous := hk.continuous.prodMap hk'.continuous
  image_subset st ab h := by
    change Prod.map ι ι' '' (car' ab.1 ×ˢ carS' ab.2) ⊆ car st.1 ×ˢ carS st.2
    rw [Set.prodMap_image_prod]
    exact Set.prod_mono (hk.image_subset _ _ (left_ne_zero_of_mul h))
      (hk'.image_subset _ _ (right_ne_zero_of_mul h))
  isLocallyFiniteSet st x := by
    obtain ⟨A, hA, hfin⟩ := hk.isLocallyFiniteSet st.1 x.1
    obtain ⟨B, hB, hfin'⟩ := hk'.isLocallyFiniteSet st.2 x.2
    refine ⟨A ×ˢ B, prod_mem_nhds hA hB, (hfin.prod hfin').subset ?_⟩
    rintro ⟨a, b⟩ ⟨hab, ⟨u, v⟩, ⟨hu, hv⟩, hu', hv'⟩
    exact ⟨⟨left_ne_zero_of_mul hab, u, hu, hu'⟩, ⟨right_ne_zero_of_mul hab, v, hv, hv'⟩⟩
  compact_nonempty ab := ⟨(hk.compact_nonempty ab.1).1.prod (hk'.compact_nonempty ab.2).1,
    (hk.compact_nonempty ab.1).2.prod (hk'.compact_nonempty ab.2).2⟩

open Classical in
/-- The tensor of two kernel transforms is the transform of the tensor by the product kernel. -/
lemma lfTensor_kernelFun {R : Type*} [CommRing R] (hk : IsAdmissibleKernel ι car car' k)
    (hk' : IsAdmissibleKernel ι' carS carS' k') {c : S → R} {d : S' → R}
    (hc : IsLocallyFiniteSet car (Function.support c))
    (hd : IsLocallyFiniteSet carS (Function.support d)) :
    lfTensor (kernelFun k c) (kernelFun k' d) = kernelFun (prodKernel k k') (lfTensor c d) := by
  funext ab
  obtain ⟨a, b⟩ := ab
  set F := (hk.finite_support hc a).toFinset
  set F' := (hk'.finite_support hd b).toFinset
  have hF : ∀ σ, c σ ≠ 0 → k σ a ≠ 0 → σ ∈ F := fun σ h1 h2 ↦
    (Finite.mem_toFinset _).2 ⟨h1, hk.inter_nonempty h2⟩
  have hF' : ∀ τ, d τ ≠ 0 → k' τ b ≠ 0 → τ ∈ F' := fun τ h1 h2 ↦
    (Finite.mem_toFinset _).2 ⟨h1, hk'.inter_nonempty h2⟩
  rw [lfTensor, hk.kernelFun_eq_sum c a F hF, hk'.kernelFun_eq_sum d b F' hF', kernelFun,
    finsum_eq_sum_of_support_subset (s := F ×ˢ F') _ (fun st hst ↦ by
      have h1 := smul_ne_zero_left hst
      have h2 := smul_ne_zero_right hst
      exact Finset.mem_product.2 ⟨hF _ (left_ne_zero_of_mul h2) (left_ne_zero_of_mul h1),
        hF' _ (right_ne_zero_of_mul h2) (right_ne_zero_of_mul h1)⟩),
    Finset.sum_mul_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun σ _ ↦ Finset.sum_congr rfl fun τ _ ↦ ?_
  rw [smul_mul_smul_comm]
  rfl

/-- A kernel whose support is contained in that of an admissible kernel is admissible. -/
lemma IsAdmissibleKernel.mono {k₀ : S → T → ℤ} (hk : IsAdmissibleKernel ι car car' k)
    (h : ∀ σ τ, k₀ σ τ ≠ 0 → k σ τ ≠ 0) : IsAdmissibleKernel ι car car' k₀ where
  continuous := hk.continuous
  image_subset σ τ h' := hk.image_subset σ τ (h σ τ h')
  isLocallyFiniteSet σ := (hk.isLocallyFiniteSet σ).mono fun τ hτ ↦ h σ τ hτ
  compact_nonempty := hk.compact_nonempty

end prodKernel

end LocallyFiniteChain

namespace borelMooreHomology

open SingularChain LocallyFiniteChain BorelMooreCross

section kernels

variable {X Y : TopCat.{u}}

/-- The kernel of the cross product of simplices. -/
def crossKernel (n p q : ℕ) (st : Simp X p × Simp Y q) (μ : Simp (TopCat.of (X × Y)) n) : ℤ :=
  crossSimplex n st.1 st.2 μ

/-- The kernel of the cross product is admissible. -/
lemma isAdmissibleKernel_crossKernel (n p q : ℕ) :
    IsAdmissibleKernel (id : TopCat.of (X × Y) → TopCat.of (X × Y)) (carP X Y p q)
      (singularSimplexImage (TopCat.of (X × Y)) (n := op ⦋n⦌)) (crossKernel n p q) where
  continuous := continuous_id
  image_subset st μ h := by
    rw [image_id]
    exact isCarrierDecreasing_crossFamily n p q st μ h
  isLocallyFiniteSet st _ := ⟨univ, Filter.univ_mem,
    (crossSimplex n st.1 st.2).support.finite_toSet.subset fun μ hμ ↦
      Finsupp.mem_support_iff.2 hμ.1⟩
  compact_nonempty μ := ⟨isCompact_singularSimplexImage μ, nonempty_singularSimplexImage μ⟩

/-- The cross product of locally finite chains is the transform of their tensor by
`crossKernel`. -/
lemma crossFun_eq_kernelFun {R : Type u} [CommRing R] (n p q : ℕ) (c : Simp X p → R)
    (d : Simp Y q → R) : crossFun n p q c d = kernelFun (crossKernel n p q) (lfTensor c d) := by
  funext μ
  refine finsum_congr fun st ↦ ?_
  rw [zsmul_eq_mul, mul_comm]
  rfl

variable (U : TopologicalSpace.Opens X) (V : TopologicalSpace.Opens Y)

/-- The kernel of the homotopy `h` between the restriction of the cross product and the cross
product of the restrictions, landing in `U × V`. -/
def crossHomotopyKernel (m p q : ℕ) (st : Simp X p × Simp Y q)
    (ν : Simp (TopCat.of (TopCat.of U × TopCat.of V)) m) : ℤ :=
  crossHomotopyCoeff (U : Set X) (V : Set Y) m (SingularCochain.simplexEquiv _ _ st.1) (SingularCochain.simplexEquiv _ _ st.2) (inclProdSimplex U V ν)

variable [T2Space X] [T2Space Y]

/-- The kernel of the homotopy `h` is admissible. -/
lemma isAdmissibleKernel_crossHomotopyKernel (m p q : ℕ) :
    IsAdmissibleKernel (prodHom (inclHom U) (inclHom V)) (carP X Y p q)
      (singularSimplexImage (TopCat.of (TopCat.of U × TopCat.of V)) (n := op ⦋m⦌))
      (crossHomotopyKernel U V m p q) where
  continuous := (prodHom (inclHom U) (inclHom V)).hom.continuous
  image_subset st ν h := by
    rw [← range_inclProdSimplex]
    exact (range_subset_of_crossHomotopyCoeff_ne_zero h).trans (inter_subset_left.trans
      (Set.prod_mono (range_simplexEquiv _).subset (range_simplexEquiv _).subset))
  isLocallyFiniteSet st x := by
    obtain ⟨G, hG, hxG, hfin⟩ := exists_finite_crossHomotopyCoeff_ne_zero U.isOpen V.isOpen m
      (SingularCochain.simplexEquiv _ _ st.1) (SingularCochain.simplexEquiv _ _ st.2) (x := (x.1.1, x.2.1)) ⟨x.1.2, x.2.2⟩
    refine ⟨prodHom (inclHom U) (inclHom V) ⁻¹' G,
      (hG.preimage (prodHom (inclHom U) (inclHom V)).hom.continuous).mem_nhds hxG,
      (hfin.preimage (inclProdSimplex_injective U V m).injOn).subset ?_⟩
    rintro ν ⟨hν, y, hy, hyG⟩
    refine ⟨hν, prodHom (inclHom U) (inclHom V) y, ?_, hyG⟩
    rw [range_inclProdSimplex]
    exact ⟨y, hy, rfl⟩
  compact_nonempty ν := ⟨isCompact_singularSimplexImage ν, nonempty_singularSimplexImage ν⟩

end kernels

end borelMooreHomology

namespace SingularChain

section supports

variable {X Y : TopCat.{u}} {U : Set X} {V : Set Y}

/-- A simplex with nonzero coefficient in the restriction of `σ × τ` lies in
`range σ × range τ`. -/
lemma range_subset_of_restrFin_crossSimplexChain_ne_zero {W : Set (X × Y)} {n p q : ℕ}
    {σ : Simplex X p} {τ : Simplex Y q} {ω : Simplex (X × Y) n}
    (h : restrFin ℤ W (crossSimplexChain n σ τ) ω ≠ 0) : range ω ⊆ range σ ×ˢ range τ :=
  (range_subset_of_restrFin_ne_zero (crossSimplexChain_mem_inside n σ τ) h).trans
    inter_subset_left

/-- A simplex with nonzero coefficient in `σ|_U × τ|_V` lies in `range σ × range τ`. -/
lemma range_subset_of_crossRestrCoeff_ne_zero {n p q : ℕ} {σ : Simplex X p} {τ : Simplex Y q}
    {ω : Simplex (X × Y) n} (h : crossRestrCoeff U V n σ τ ω ≠ 0) :
    range ω ⊆ range σ ×ˢ range τ := by
  obtain ⟨ab, hab⟩ : ∃ ab : Simplex X p × Simplex Y q,
      restrCoeff ℤ U σ ab.1 * restrCoeff ℤ V τ ab.2 * crossSimplexChain n ab.1 ab.2 ω ≠ 0 := by
    by_contra h'
    push Not at h'
    exact h (finsum_eq_zero_of_forall_eq_zero h')
  have h₁ := range_subset_of_restrCoeff_ne_zero (left_ne_zero_of_mul (left_ne_zero_of_mul hab))
  have h₂ := range_subset_of_restrCoeff_ne_zero (right_ne_zero_of_mul (left_ne_zero_of_mul hab))
  exact (range_subset_of_crossSimplexChain_ne_zero (right_ne_zero_of_mul hab)).trans
    (Set.prod_mono (h₁.trans inter_subset_left) (h₂.trans inter_subset_left))

open Classical in
/-- A simplex with nonzero coefficient in `∂ h (σ, τ)` lies in `range σ × range τ`. -/
lemma range_subset_of_sum_finsum_crossHomotopyCoeff_ne_zero {n p q : ℕ} {σ : Simplex X p}
    {τ : Simplex Y q} {ω : Simplex (X × Y) n}
    (h : ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) * ∑ᶠ ω' : Simplex (X × Y) (n + 1),
      (if ω'.comp (face n i) = ω then crossHomotopyCoeff U V (n + 1) σ τ ω' else 0) ≠ 0) :
    range ω ⊆ range σ ×ˢ range τ := by
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨ω', hω'⟩ : ∃ ω' : Simplex (X × Y) (n + 1),
      (if ω'.comp (face n i) = ω then crossHomotopyCoeff U V (n + 1) σ τ ω' else 0) ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hi (by rw [finsum_eq_zero_of_forall_eq_zero h', mul_zero])
  split_ifs at hω' with he
  · rw [← he]
    rintro _ ⟨t, rfl⟩
    exact ((range_subset_of_crossHomotopyCoeff_ne_zero hω').trans inter_subset_left) ⟨_, rfl⟩
  · exact absurd rfl hω'

/-- For chains `c` of `A` and `d` of `B`, a simplex with nonzero coefficient in `h (c, d)` lies
in `A × B`. -/
lemma range_subset_of_crossHomotopyFin_ne_zero {m p q : ℕ} {A : Set X} {B : Set Y}
    {c : Chain ℤ X p} {d : Chain ℤ Y q} (hc : c ∈ inside ℤ p A) (hd : d ∈ inside ℤ q B)
    {ω : Simplex (X × Y) m} (h : crossHomotopyFin U V m p q c d ω ≠ 0) :
    range ω ⊆ A ×ˢ B := by
  obtain ⟨σ, hσ, h₁⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨τ, hτ, h₂⟩ := Finset.exists_ne_zero_of_sum_ne_zero h₁
  exact ((range_subset_of_crossHomotopyCoeff_ne_zero (right_ne_zero_of_mul h₂)).trans
    inter_subset_left).trans (Set.prod_mono (hc (Finset.mem_coe.2 hσ)) (hd (Finset.mem_coe.2 hτ)))

end supports

/-- `h (∂ σ, τ) = ∑_i (-1) ^ i h (σ ∘ δ_i, τ)`. -/
lemma crossHomotopyFin_bd_single_left {X Y : TopCat.{u}} (U : Set X) (V : Set Y) (m p q : ℕ)
    (σ : Simplex X (p + 1)) (τ : Simplex Y q) (ω : Simplex (X × Y) m) :
    crossHomotopyFin U V m p q (bd ℤ p (single σ 1)) (single τ 1) ω =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) * crossHomotopyCoeff U V m (σ.comp (face p i)) τ ω := by
  have key : ∀ c : Chain ℤ X p, crossHomotopyFin U V m p q c (single τ 1) ω =
      c.sum fun σ' a ↦ a * crossHomotopyCoeff U V m σ' τ ω := fun c ↦
    Finsupp.sum_congr fun σ' _ ↦ by rw [Finsupp.sum_single_index (by simp), mul_one]
  rw [key, bd_single, ← Finsupp.sum_finsetSum_index (fun _ ↦ zero_mul _)
    (fun _ _ _ ↦ add_mul _ _ _)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.sum_single_index (zero_mul _)]

/-- `h (σ, ∂ τ) = ∑_j (-1) ^ j h (σ, τ ∘ δ_j)`. -/
lemma crossHomotopyFin_bd_single_right {X Y : TopCat.{u}} (U : Set X) (V : Set Y) (m p q : ℕ)
    (σ : Simplex X p) (τ : Simplex Y (q + 1)) (ω : Simplex (X × Y) m) :
    crossHomotopyFin U V m p q (single σ 1) (bd ℤ q (single τ 1)) ω =
      ∑ j : Fin (q + 2), (-1 : ℤ) ^ (j : ℕ) * crossHomotopyCoeff U V m σ (τ.comp (face q j)) ω := by
  have key : ∀ d : Chain ℤ Y q, crossHomotopyFin U V m p q (single σ 1) d ω =
      d.sum fun τ' b ↦ b * crossHomotopyCoeff U V m σ τ' ω := fun d ↦ by
    rw [crossHomotopyFin, Finsupp.sum_single_index (by simp)]
    exact Finsupp.sum_congr fun τ' _ ↦ by ring
  rw [key, bd_single, ← Finsupp.sum_finsetSum_index (fun _ ↦ zero_mul _)
    (fun _ _ _ ↦ add_mul _ _ _)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.sum_single_index (zero_mul _)]

end SingularChain

namespace borelMooreHomology

open SingularChain LocallyFiniteChain BorelMooreCross

section assembly

variable {X Y : TopCat.{u}} (U : TopologicalSpace.Opens X) (V : TopologicalSpace.Opens Y)

/-- The restriction of a chain of simplices of the singular simplicial set, read as singular
simplices, is the sum of the restrictions of its simplices. -/
lemma restrFin_mapDomain_toC {Z : TopCat.{u}} (A : Set Z) {n : ℕ} (cs : Simp Z n →₀ ℤ)
    (ω : Simplex Z n) :
    restrFin ℤ A (Finsupp.mapDomain (fun ρ ↦ (SingularCochain.simplexEquiv _ _ ρ : Simplex Z n)) cs) ω =
      ∑ᶠ μ, cs μ * restrCoeff ℤ A (SingularCochain.simplexEquiv _ _ μ) ω := by
  rw [restrFin, Finsupp.sum_mapDomain_index (fun _ ↦ zero_mul _) (fun _ _ _ ↦ add_mul _ _ _),
    Finsupp.sum]
  refine (finsum_eq_sum_of_support_subset _ fun μ hμ ↦ ?_).symm
  exact Finsupp.mem_support_iff.2 (left_ne_zero_of_mul (Function.mem_support.1 hμ))

/-- The composite of `crossKernel` with the restriction kernel of `prodOpens U V` gives the
coefficients of the restriction of `σ × τ` to `U × V`. -/
lemma finsum_crossKernel_restrictKernel (n p q : ℕ) (st : Simp X p × Simp Y q)
    (ν : Simp (TopCat.of (TopCat.of U × TopCat.of V)) n) :
    ∑ᶠ μ, crossKernel n p q st μ *
        restrictKernel (prodOpens U V) n μ ((TopCat.toSSet.map (prodOpensInv U V)).app _ ν) =
      restrFin ℤ ((U : Set X) ×ˢ (V : Set Y)) (crossSimplexChain n (SingularCochain.simplexEquiv _ _ st.1) (SingularCochain.simplexEquiv _ _ st.2))
        (inclProdSimplex U V ν) := by
  rw [crossSimplexChain_toC]
  exact (restrFin_mapDomain_toC (Z := TopCat.of (X × Y)) _ _ _).symm

/-- The composite of the product of the restriction kernels of `U` and `V` with `crossKernel`
gives the coefficients of `σ|_U × τ|_V`. -/
lemma finsum_prodKernel_crossKernel (n p q : ℕ) (st : Simp X p × Simp Y q)
    (ν : Simp (TopCat.of (TopCat.of U × TopCat.of V)) n) :
    ∑ᶠ ab, prodKernel (restrictKernel U p) (restrictKernel V q) st ab * crossKernel n p q ab ν =
      crossRestrCoeff (U : Set X) (V : Set Y) n (SingularCochain.simplexEquiv _ _ st.1) (SingularCochain.simplexEquiv _ _ st.2) (inclProdSimplex U V ν) := by
  have hinj : Function.Injective fun ab : Simp (TopCat.of U) p × Simp (TopCat.of V) q ↦
      (inclSimplex U ab.1, inclSimplex V ab.2) := fun ab ab' h ↦
    Prod.ext (inclSimplex_injective U p (congrArg Prod.fst h))
      (inclSimplex_injective V q (congrArg Prod.snd h))
  rw [crossRestrCoeff, ← finsum_comp_eq_of_support_subset_range hinj (fun ab hab ↦ by
    rw [Function.mem_support] at hab
    obtain ⟨a, ha⟩ := mem_range_inclSimplex U
      ((range_subset_of_restrCoeff_ne_zero (left_ne_zero_of_mul (left_ne_zero_of_mul hab))).trans
        inter_subset_right)
    obtain ⟨b, hb⟩ := mem_range_inclSimplex V
      ((range_subset_of_restrCoeff_ne_zero (right_ne_zero_of_mul (left_ne_zero_of_mul hab))).trans
        inter_subset_right)
    exact ⟨(a, b), Prod.ext ha hb⟩)]
  refine finsum_congr fun ab ↦ ?_
  rw [crossSimplexChain_inclSimplex, Finsupp.mapDomain_apply_of_injective (inclProdSimplex_injective U V n)]
  rfl

open Classical in
/-- The sum of `crossHomotopyKernel` over the simplices of `U × V` with `i`-th face `ν` equals
the sum of the coefficients of `h` over the simplices of `X × Y` with `i`-th face
`inclProdSimplex U V ν`. -/
lemma finsum_crossHomotopyKernel_δ (m p q : ℕ) (st : Simp X p × Simp Y q)
    (ν : Simp (TopCat.of (TopCat.of U × TopCat.of V)) m) (i : Fin (m + 2)) :
    ∑ᶠ ν', (if (TopCat.toSSet.obj (TopCat.of (TopCat.of U × TopCat.of V))).δ i ν' = ν then
        crossHomotopyKernel U V (m + 1) p q st ν' else 0) =
      ∑ᶠ ω' : Simplex (X × Y) (m + 1), (if ω'.comp (face m i) = inclProdSimplex U V ν then
        crossHomotopyCoeff (U : Set X) (V : Set Y) (m + 1) (SingularCochain.simplexEquiv _ _ st.1) (SingularCochain.simplexEquiv _ _ st.2) ω' else 0) := by
  rw [← finsum_comp_eq_of_support_subset_range (inclProdSimplex_injective U V (m + 1))
    (fun ω' hω' ↦ by
      rw [Function.mem_support] at hω'
      split_ifs at hω' with h
      · exact mem_range_inclProdSimplex U V
          ((range_subset_of_crossHomotopyCoeff_ne_zero hω').trans inter_subset_right)
      · exact absurd rfl hω')]
  refine finsum_congr fun ν' ↦ ?_
  have hiff : (TopCat.toSSet.obj (TopCat.of (TopCat.of U × TopCat.of V))).δ i ν' = ν ↔
      (inclProdSimplex U V ν').comp (face m i) = inclProdSimplex U V ν := by
    rw [← inclProdSimplex_δ]
    exact (inclProdSimplex_injective U V m).eq_iff.symm
  by_cases h : (TopCat.toSSet.obj (TopCat.of (TopCat.of U × TopCat.of V))).δ i ν' = ν
  · rw [ite_eq_left h, ite_eq_left (hiff.1 h)]
    rfl
  · rw [ite_eq_right h, ite_eq_right (fun h' ↦ h (hiff.2 h'))]

/-- The kernel transform of the zero chain is zero. -/
lemma kernelFun_zero_chain {S T M : Type*} [AddCommGroup M] (k : S → T → ℤ) :
    kernelFun k (0 : S → M) = 0 := by
  funext τ
  simp [kernelFun]

/-- The transform by the zero kernel is zero. -/
lemma kernelFun_zero_kernel {S T M : Type*} [AddCommGroup M] (c : S → M) :
    kernelFun (0 : S → T → ℤ) c = 0 := by
  funext τ
  simp [kernelFun]

variable {R : Type u} [CommRing R]

/-- The boundary in the first factor of the tensor `c ⊗ d` of locally finite chains is
`∂ c ⊗ d`. -/
lemma dFun_lfTensor_left {p q : ℕ} (c : Simp X (p + 1) → R)
    (hc : c ∈ lfChains R R (singularSimplexImage X (n := op ⦋p + 1⦌))) (d : Simp Y q → R) :
    dFun (fun (i : Fin (p + 2)) (st : Simp X (p + 1) × Simp Y q) ↦
        ((TopCat.toSSet.obj X).δ i st.1, st.2)) (lfTensor c d) =
      lfTensor (dFun (fun i : Fin (p + 2) ↦ (TopCat.toSSet.obj X).δ i) c) d := by
  funext st
  simp only [dFun, lfTensor]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have := congrFun (pushforwardFun_prodMap_id_lfTensor hc ((TopCat.toSSet.obj X).δ i)
    (fun σ ↦ singularSimplexImage_map_subset _ σ) compact_nonempty d) st
  rw [smul_mul_assoc]
  exact congrArg _ this

/-- The boundary in the second factor of the tensor `c ⊗ d` of locally finite chains is
`c ⊗ ∂ d`. -/
lemma dFun_lfTensor_right {p q : ℕ} (c : Simp X p → R) (d : Simp Y (q + 1) → R)
    (hd : d ∈ lfChains R R (singularSimplexImage Y (n := op ⦋q + 1⦌))) :
    dFun (fun (i : Fin (q + 2)) (st : Simp X p × Simp Y (q + 1)) ↦
        (st.1, (TopCat.toSSet.obj Y).δ i st.2)) (lfTensor c d) =
      lfTensor c (dFun (fun i : Fin (q + 2) ↦ (TopCat.toSSet.obj Y).δ i) d) := by
  funext st
  simp only [dFun, lfTensor]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have := congrFun (pushforwardFun_prodMap_id_lfTensor' c hd ((TopCat.toSSet.obj Y).δ i)
    (fun σ ↦ singularSimplexImage_map_subset _ σ) compact_nonempty) st
  rw [mul_smul_comm]
  exact congrArg _ this

variable [T2Space X] [T2Space Y]

/-- For a cycle `z`, the terms `h (∂ z, w)` vanish. -/
lemma kernelFun_crossHomotopyFin_bdSub_left (n p q : ℕ) (z : Cyc (R := R) X p)
    (w : (BM R Y).X q) :
    kernelFun (fun (st : Simp X p × Simp Y q) (ν : Simp (TopCat.of (TopCat.of U × TopCat.of V)) n) ↦
        crossHomotopyFin (U : Set X) (V : Set Y) n (p - 1) q (bdSub ℤ p (single (SingularCochain.simplexEquiv _ _ st.1) 1))
          (single (SingularCochain.simplexEquiv _ _ st.2) 1) (inclProdSimplex U V ν))
      (lfTensor (coeff R z.1) (coeff R w)) = 0 := by
  rcases p with _ | p
  · have : (fun (st : Simp X 0 × Simp Y q) (ν : Simp (TopCat.of (TopCat.of U × TopCat.of V)) n) ↦
        crossHomotopyFin (U : Set X) (V : Set Y) n (0 - 1) q (bdSub ℤ 0 (single (SingularCochain.simplexEquiv _ _ st.1) 1))
          (single (SingularCochain.simplexEquiv _ _ st.2) 1) (inclProdSimplex U V ν)) = 0 := by
      funext st ν
      simp [crossHomotopyFin]
    rw [this, kernelFun_zero_kernel]
  · have hk : (fun (st : Simp X (p + 1) × Simp Y q)
        (ν : Simp (TopCat.of (TopCat.of U × TopCat.of V)) n) ↦
        crossHomotopyFin (U : Set X) (V : Set Y) n (p + 1 - 1) q
          (bdSub ℤ (p + 1) (single (SingularCochain.simplexEquiv _ _ st.1) 1)) (single (SingularCochain.simplexEquiv _ _ st.2) 1) (inclProdSimplex U V ν)) =
        fun st ν ↦ ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) *
          crossHomotopyKernel U V n p q ((TopCat.toSSet.obj X).δ i st.1, st.2) ν := by
      funext st ν
      refine (crossHomotopyFin_bd_single_left _ _ n p q _ _ _).trans ?_
      simp only [crossHomotopyKernel, borelMooreHomology.toSSetObjEquiv_δ]
    rw [hk, ← kernelFun_dFun_eq (isAdmissibleKernel_crossHomotopyKernel U V n p q)
      (fun (i : Fin (p + 2)) (st : Simp X (p + 1) × Simp Y q) ↦
        ((TopCat.toSSet.obj X).δ i st.1, st.2))
      (fun i st ↦ Set.prod_mono (singularSimplexImage_map_subset _ st.1) subset_rfl)
      (lfTensor_mem (coeff_mem R z.1) (coeff_mem R w)),
      dFun_lfTensor_left _ (coeff_mem R z.1)]
    have hz : dFun (fun i : Fin (p + 2) ↦ (TopCat.toSSet.obj X).δ i) (coeff R z.1) = 0 := by
      refine (borelMooreChainComplex_d_apply R (ModuleCat.of R R) X p z.1).symm.trans ?_
      exact congrArg Subtype.val ((mem_cyc_iff z.1).1 z.2)
    rw [hz, lfTensor_zero_left, kernelFun_zero_chain]

/-- For a cycle `w`, the terms `h (z, ∂ w)` vanish. -/
lemma kernelFun_crossHomotopyFin_bdSub_right (n p q : ℕ) (z : (BM R X).X p)
    (w : Cyc (R := R) Y q) :
    kernelFun (fun (st : Simp X p × Simp Y q) (ν : Simp (TopCat.of (TopCat.of U × TopCat.of V)) n) ↦
        crossHomotopyFin (U : Set X) (V : Set Y) n p (q - 1) (single (SingularCochain.simplexEquiv _ _ st.1) 1)
          (bdSub ℤ q (single (SingularCochain.simplexEquiv _ _ st.2) 1)) (inclProdSimplex U V ν))
      (lfTensor (coeff R z) (coeff R w.1)) = 0 := by
  rcases q with _ | q
  · have : (fun (st : Simp X p × Simp Y 0) (ν : Simp (TopCat.of (TopCat.of U × TopCat.of V)) n) ↦
        crossHomotopyFin (U : Set X) (V : Set Y) n p (0 - 1) (single (SingularCochain.simplexEquiv _ _ st.1) 1)
          (bdSub ℤ 0 (single (SingularCochain.simplexEquiv _ _ st.2) 1)) (inclProdSimplex U V ν)) = 0 := by
      funext st ν
      simp [crossHomotopyFin]
    rw [this, kernelFun_zero_kernel]
  · have hk : (fun (st : Simp X p × Simp Y (q + 1))
        (ν : Simp (TopCat.of (TopCat.of U × TopCat.of V)) n) ↦
        crossHomotopyFin (U : Set X) (V : Set Y) n p (q + 1 - 1) (single (SingularCochain.simplexEquiv _ _ st.1) 1)
          (bdSub ℤ (q + 1) (single (SingularCochain.simplexEquiv _ _ st.2) 1)) (inclProdSimplex U V ν)) =
        fun st ν ↦ ∑ j : Fin (q + 2), (-1 : ℤ) ^ (j : ℕ) *
          crossHomotopyKernel U V n p q (st.1, (TopCat.toSSet.obj Y).δ j st.2) ν := by
      funext st ν
      refine (crossHomotopyFin_bd_single_right _ _ n p q _ _ _).trans ?_
      simp only [crossHomotopyKernel, borelMooreHomology.toSSetObjEquiv_δ]
    rw [hk, ← kernelFun_dFun_eq (isAdmissibleKernel_crossHomotopyKernel U V n p q)
      (fun (j : Fin (q + 2)) (st : Simp X p × Simp Y (q + 1)) ↦
        (st.1, (TopCat.toSSet.obj Y).δ j st.2))
      (fun j st ↦ Set.prod_mono subset_rfl (singularSimplexImage_map_subset _ st.2))
      (lfTensor_mem (coeff_mem R z) (coeff_mem R w.1)),
      dFun_lfTensor_right _ _ (coeff_mem R w.1)]
    have hw : dFun (fun j : Fin (q + 2) ↦ (TopCat.toSSet.obj Y).δ j) (coeff R w.1) = 0 := by
      refine (borelMooreChainComplex_d_apply R (ModuleCat.of R R) Y q w.1).symm.trans ?_
      exact congrArg Subtype.val ((mem_cyc_iff w.1).1 w.2)
    rw [hw, lfTensor_zero_right, kernelFun_zero_chain]

end assembly

end borelMooreHomology

namespace borelMooreHomology

open SingularChain LocallyFiniteChain BorelMooreCross

section main

variable (R : Type u) [CommRing R] {X Y : TopCat.{u}} [T2Space X] [T2Space Y]
  (U : TopologicalSpace.Opens X) (V : TopologicalSpace.Opens Y)

/-- Restriction of locally finite chains of `X × Y` to the open subset `U × V`, read in the
product of the spaces `U` and `V`. -/
abbrev prodRestrictChainMap :
    BM R (TopCat.of (X × Y)) ⟶ BM R (TopCat.of (TopCat.of U × TopCat.of V)) :=
  restrictChainMap R (ModuleCat.of R R) (prodOpens U V) ≫
    chainMap R (ModuleCat.of R R) (prodOpensMap U V) (isProperMap_prodOpensMap U V)

open Classical in
/-- On cycles, the restriction of a cross product and the cross product of the restrictions
differ by a boundary: `(z × w)|_{U × V} - z|_U × w|_V = ∂ h (z, w)`. -/
theorem exists_d_eq_prodRestrictChainMap_crossChain_sub (p q : ℕ) (z : Cyc (R := R) X p)
    (w : Cyc (R := R) Y q) :
    ∃ u : (BM R (TopCat.of (TopCat.of U × TopCat.of V))).X (p + q + 1),
      ((BM R (TopCat.of (TopCat.of U × TopCat.of V))).d (p + q + 1) (p + q)).hom u =
        ((prodRestrictChainMap R U V).f (p + q)).hom (crossChain R (p + q) p q z.1 w.1) -
          crossChain R (p + q) p q (((restrictChainMap R (ModuleCat.of R R) U).f p).hom z.1)
            (((restrictChainMap R (ModuleCat.of R R) V).f q).hom w.1) := by
  set n := p + q
  set c := lfTensor (coeff R z.1) (coeff R w.1)
  have hc : IsLocallyFiniteSet (carP X Y p q) (Function.support c) :=
    lfTensor_mem (coeff_mem R z.1) (coeff_mem R w.1)
  have hk := isAdmissibleKernel_crossHomotopyKernel U V (n + 1) p q
  refine ⟨ofCoeff R (kernelFun (crossHomotopyKernel U V (n + 1) p q) c)
    (hk.isLocallyFiniteSet_kernelFun hc), ?_⟩
  apply coeff_injective R
  funext ν
  set ω := inclProdSimplex U V ν
  -- the coefficient functions, read in `X × Y`
  set KA : Simp X p × Simp Y q → ℤ := fun st ↦
    restrFin ℤ ((U : Set X) ×ˢ (V : Set Y)) (crossSimplexChain n (SingularCochain.simplexEquiv _ _ st.1) (SingularCochain.simplexEquiv _ _ st.2)) ω
  set KB : Simp X p × Simp Y q → ℤ := fun st ↦
    crossRestrCoeff (U : Set X) (V : Set Y) n (SingularCochain.simplexEquiv _ _ st.1) (SingularCochain.simplexEquiv _ _ st.2) ω
  set KD : Simp X p × Simp Y q → ℤ := fun st ↦
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) * ∑ᶠ ω' : Simplex (X × Y) (n + 1),
      (if ω'.comp (face n i) = ω then
        crossHomotopyCoeff (U : Set X) (V : Set Y) (n + 1) (SingularCochain.simplexEquiv _ _ st.1) (SingularCochain.simplexEquiv _ _ st.2) ω' else 0)
  set K₁ : Simp X p × Simp Y q → ℤ := fun st ↦
    crossHomotopyFin (U : Set X) (V : Set Y) n (p - 1) q (bdSub ℤ p (single (SingularCochain.simplexEquiv _ _ st.1) 1))
      (single (SingularCochain.simplexEquiv _ _ st.2) 1) ω
  set K₂ : Simp X p × Simp Y q → ℤ := fun st ↦
    crossHomotopyFin (U : Set X) (V : Set Y) n p (q - 1) (single (SingularCochain.simplexEquiv _ _ st.1) 1)
      (bdSub ℤ q (single (SingularCochain.simplexEquiv _ _ st.2) 1)) ω
  -- the boundary of `u`
  have eD : coeff R (((BM R (TopCat.of (TopCat.of U × TopCat.of V))).d (n + 1) n).hom
      (ofCoeff R (kernelFun (crossHomotopyKernel U V (n + 1) p q) c)
        (hk.isLocallyFiniteSet_kernelFun hc))) ν = ∑ᶠ st, KD st • c st := by
    change (((BM R (TopCat.of (TopCat.of U × TopCat.of V))).d (n + 1) n).hom _).1 ν = _
    rw [borelMooreChainComplex_d_apply]
    change dFun _ (kernelFun _ c) ν = _
    rw [dFun_kernelFun_eq hk (fun i : Fin (n + 2) ↦
      (TopCat.toSSet.obj (TopCat.of (TopCat.of U × TopCat.of V))).δ i)
      (fun i τ ↦ singularSimplexImage_map_subset _ τ)
      (fun τ ↦ ⟨isCompact_singularSimplexImage τ, nonempty_singularSimplexImage τ⟩) hc]
    refine finsum_congr fun st ↦ ?_
    congr 1
    exact Finset.sum_congr rfl fun i _ ↦ by rw [finsum_crossHomotopyKernel_δ]
  -- the restriction of the cross product
  have eA : coeff R (((prodRestrictChainMap R U V).f n).hom (crossChain R n p q z.1 w.1)) ν =
      ∑ᶠ st, KA st • c st := by
    change pushforwardFun ((TopCat.toSSet.map (prodOpensMap U V)).app _)
      (kernelFun (restrictKernel (prodOpens U V) n) (crossFun n p q (coeff R z.1) (coeff R w.1)))
      ν = _
    rw [pushforwardFun_eq_comp (prodOpensInv_prodOpensMap_app U V)
      (prodOpensMap_prodOpensInv_app U V), Function.comp_apply, crossFun_eq_kernelFun,
      kernelFun_kernelFun (isAdmissibleKernel_crossKernel n p q)
        (isAdmissibleKernel_restrictKernel (prodOpens U V) n) hc]
    exact finsum_congr fun st ↦
      congrArg (· • c st) (finsum_crossKernel_restrictKernel U V n p q st ν)
  -- the cross product of the restrictions
  have eB : coeff R (crossChain R n p q (((restrictChainMap R (ModuleCat.of R R) U).f p).hom z.1)
      (((restrictChainMap R (ModuleCat.of R R) V).f q).hom w.1)) ν = ∑ᶠ st, KB st • c st := by
    rw [coeff_crossChain]
    change crossFun n p q (kernelFun (restrictKernel U p) (coeff R z.1))
      (kernelFun (restrictKernel V q) (coeff R w.1)) ν = _
    rw [crossFun_eq_kernelFun, lfTensor_kernelFun (isAdmissibleKernel_restrictKernel U p)
      (isAdmissibleKernel_restrictKernel V q) (coeff_mem R z.1) (coeff_mem R w.1),
      kernelFun_kernelFun ((isAdmissibleKernel_restrictKernel U p).prod
        (isAdmissibleKernel_restrictKernel V q))
        (isAdmissibleKernel_crossKernel (X := TopCat.of U) (Y := TopCat.of V) n p q) hc]
    exact finsum_congr fun st ↦ congrArg (· • c st) (finsum_prodKernel_crossKernel U V n p q st ν)
  have e₁ : ∑ᶠ st, K₁ st • c st = 0 :=
    congrFun (kernelFun_crossHomotopyFin_bdSub_left U V n p q z w.1) ν
  have e₂ : ∑ᶠ st, K₂ st • c st = 0 :=
    congrFun (kernelFun_crossHomotopyFin_bdSub_right U V n p q z.1 w) ν
  -- all are finite sums over the pairs of simplices of `z × w` meeting `ω`
  have hK := isCompact_range ω.continuous
  set F := (hc.finite_inter_compact hK).toFinset
  have hne : ∀ st : Simp X p × Simp Y q, range ω ⊆ carP X Y p q st →
      (carP X Y p q st ∩ range ω).Nonempty := fun st h ↦
    ⟨_, h ⟨stdSimplex.vertex 0, rfl⟩, ⟨stdSimplex.vertex 0, rfl⟩⟩
  have hsum : ∀ k : Simp X p × Simp Y q → ℤ, (∀ st, k st ≠ 0 → range ω ⊆ carP X Y p q st) →
      ∑ᶠ st, k st • c st = ∑ st ∈ F, k st • c st := fun k hk' ↦
    kernelFun_eq_sum_of_inter_nonempty (fun st (_ : Unit) ↦ k st) hc hK () fun st h ↦
      hne st (hk' st h)
  have hω : range ω ⊆ (U : Set X) ×ˢ (V : Set Y) := range_inclProdSimplex_subset U V ν
  rw [eD]
  change _ = coeff R (((prodRestrictChainMap R U V).f n).hom (crossChain R n p q z.1 w.1)) ν -
    coeff R (crossChain R n p q (((restrictChainMap R (ModuleCat.of R R) U).f p).hom z.1)
      (((restrictChainMap R (ModuleCat.of R R) V).f q).hom w.1)) ν
  have hcar : ∀ st : Simp X p × Simp Y q,
      range (SingularCochain.simplexEquiv _ _ st.1) ×ˢ range (SingularCochain.simplexEquiv _ _ st.2) ⊆
        carP X Y p q st := fun st ↦
    Set.prod_mono (range_simplexEquiv _).subset (range_simplexEquiv _).subset
  rw [eA, eB]
  rw [hsum KA fun st h ↦ (range_subset_of_restrFin_crossSimplexChain_ne_zero h).trans (hcar st)] at *
  rw [hsum KB fun st h ↦ (range_subset_of_crossRestrCoeff_ne_zero h).trans (hcar st),
    hsum KD fun st h ↦ (range_subset_of_sum_finsum_crossHomotopyCoeff_ne_zero h).trans (hcar st)]
  rw [hsum K₁ fun st h ↦ (range_subset_of_crossHomotopyFin_ne_zero
    (bdSub_mem_inside (single_mem_inside_range _)) (single_mem_inside_range _) h).trans (hcar st)] at e₁
  rw [hsum K₂ fun st h ↦ (range_subset_of_crossHomotopyFin_ne_zero
    (single_mem_inside_range _) (bdSub_mem_inside (single_mem_inside_range _)) h).trans (hcar st)] at e₂
  have hpt : ∀ st, KA st - KB st = KD st + K₁ st + (-1 : ℤ) ^ p * K₂ st := fun st ↦
    restrFin_crossSimplexChain_sub_crossRestrCoeff U.isOpen V.isOpen (SingularCochain.simplexEquiv _ _ st.1) (SingularCochain.simplexEquiv _ _ st.2) hω
  rw [← Finset.sum_sub_distrib]
  calc ∑ st ∈ F, KD st • c st =
        ∑ st ∈ F, KD st • c st + ∑ st ∈ F, K₁ st • c st +
          (-1 : ℤ) ^ p • ∑ st ∈ F, K₂ st • c st := by
          rw [e₁, e₂]
          simp
    _ = ∑ st ∈ F, (KA st • c st - KB st • c st) := by
      rw [Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun st _ ↦ ?_
      rw [← sub_smul, hpt, add_smul, add_smul, mul_smul]

/-- **The exterior product commutes with restriction** (Fulton, §19.1): for open subsets
`U ⊆ X`, `V ⊆ Y` of Hausdorff spaces and `a ∈ H_i X`, `b ∈ H_j Y`,
`(a × b)|_{U × V} = a|_U × b|_V`, where the open subset `U × V` of `X × Y` is identified with
the product of the spaces `U` and `V` by `prodOpensHomeo`. -/
theorem restrict_exteriorProduct (i j : ℤ) (a : borelMooreHomology R (ModuleCat.of R R) X i)
    (b : borelMooreHomology R (ModuleCat.of R R) Y j) :
    (pushforward R (ModuleCat.of R R) (prodOpensMap U V) (isProperMap_prodOpensMap U V)
        (i + j)).hom ((restrict R (ModuleCat.of R R) (prodOpens U V) (i + j)).hom
          (exteriorProduct R X Y i j (a ⊗ₜ b))) =
      exteriorProduct R (TopCat.of U) (TopCat.of V) i j
        ((restrict R (ModuleCat.of R R) U i).hom a ⊗ₜ
          (restrict R (ModuleCat.of R R) V j).hom b) := by
  have hcomp : restrict R (ModuleCat.of R R) (prodOpens U V) (i + j) ≫
      pushforward R (ModuleCat.of R R) (prodOpensMap U V) (isProperMap_prodOpensMap U V) (i + j) =
      homologyMap R (prodRestrictChainMap R U V) (i + j) := by
    have h₁ := HomologicalComplex.homologyMap_comp
      (HomologicalComplex.extendMap (restrictChainMap R (ModuleCat.of R R) (prodOpens U V))
        ComplexShape.embeddingDownNat)
      (HomologicalComplex.extendMap (chainMap R (ModuleCat.of R R) (prodOpensMap U V)
        (isProperMap_prodOpensMap U V)) ComplexShape.embeddingDownNat) (-(i + j))
    rw [← HomologicalComplex.extendMap_comp] at h₁
    exact h₁.symm
  have h := congrArg (fun φ ↦ φ.hom (exteriorProduct R X Y i j (a ⊗ₜ b))) hcomp
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [h]
  exact homologyMap_exteriorProduct_of_exists_d R _ _ _
    (exists_d_eq_prodRestrictChainMap_crossChain_sub R U V) i j a b

end main

end borelMooreHomology

end MMP
