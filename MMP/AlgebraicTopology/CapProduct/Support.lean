module

public import MMP.AlgebraicTopology.CapProduct.Neighbourhood
public import MMP.AlgebraicTopology.BorelMoore.ExteriorProductNatural
public import MMP.AlgebraicTopology.PoincareDuality.MayerVietoris

/-!
# The cap product with supports: compatibility of the neighbourhood cap product

Let `X` be a closed subset of a space `Y` and `N` a closed neighbourhood of `X`. The cap product
`capProductNbhd : H^j(Y, Y - X) ⊗ H_k Y → H_{k-j} N` pushes forward along the inclusion
`ι : N → Y` to the cap product `capProduct : H^j(Y, Y - X) ⊗ H_k Y → H_{k-j} Y`. On chains: for a
cocycle `φ` vanishing on `Y - X` and a locally finite cycle `z`, `z - ρ z = ∂ (D z)` (Hatcher's
subdivision `ρ` and homotopy `D`), so `φ ∩ z - φ ∩ ρ z = ± ∂ (φ ∩ D z)` by the Leibniz rule.

## Main results

* `MMP.borelMooreHomology.pushforward_subsetInclusion_capProductNbhd`:
  `ι_* (c ∩_N a) = c ∩ a` in `H_{k-j} Y`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [A. Hatcher, *Algebraic Topology*][hatcher2002], Prop. 2.21 and §3.3.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Set Simplicial AlgebraicTopology

universe u

namespace MMP

namespace SingularChain

variable {R : Type*} [CommRing R] {Y : Type*} [TopologicalSpace Y]

/-- Hatcher's `ρ` fixes a simplex lying in a member of `𝒰`. -/
lemma smallChainMap_single_of_subset {𝒰 : Set (Set Y)} {n : ℕ} {σ : Simplex Y n}
    (hσ : ∃ U ∈ 𝒰, range σ ⊆ U) :
    smallChainMap R 𝒰 n (Finsupp.single σ 1) = Finsupp.single σ 1 := by
  obtain ⟨U, hU, hσU⟩ := hσ
  have hin : Finsupp.single σ (1 : R) ∈ inside R n U :=
    Finsupp.single_mem_supported R _ (show range σ ⊆ U from hσU)
  have hD := smallHomotopy_eq_zero_of_mem_small (mem_small_of_mem_inside hU hin)
  rcases n with _ | n
  · rw [smallChainMap_zero, hD, map_zero, sub_zero]
  · rw [smallChainMap_succ, hD, map_zero, sub_zero,
      smallHomotopy_eq_zero_of_mem_small (mem_small_of_mem_inside hU (bd_mem_inside hin)), sub_zero]

end SingularChain

namespace borelMooreHomology

open SingularChain LocallyFiniteChain

variable (R : Type u) [CommRing R] (M : ModuleCat.{u} R) {Y : TopCat.{u}}

/-- Hatcher's `ρ` on locally finite chains fixes a chain whose simplices each lie in a member
of `𝒰`. -/
lemma smallChainMapLF_f_hom_of_small {𝒰 : Set (Set Y)} {n : ℕ}
    (c : (borelMooreChainComplex R M Y).X n)
    (hc : ∀ σ, c.1 σ ≠ 0 → ∃ U ∈ 𝒰, singularSimplexImage Y σ ⊆ U) :
    ((smallChainMapLF R M 𝒰).f n).hom c = c := by
  have hcτ : ∀ σ, c.1 σ ≠ 0 → ∃ U ∈ 𝒰, range (SingularCochain.simplexEquiv Y n σ) ⊆ U :=
    fun σ hσ ↦ by
      rw [range_simplexEquiv]
      exact hc σ hσ
  apply Subtype.ext
  funext τ
  rw [smallChainMapLF_f_apply, kernelFun]
  rw [finsum_eq_single _ τ (fun σ hστ ↦ ?_)]
  · by_cases hτ : c.1 τ = 0
    · rw [hτ, smul_zero]
    · change smallChainMap ℤ 𝒰 n (Finsupp.single (SingularCochain.simplexEquiv Y _ τ) 1)
        (SingularCochain.simplexEquiv Y _ τ) • c.1 τ = c.1 τ
      rw [smallChainMap_single_of_subset (hcτ τ hτ), Finsupp.single_eq_same, one_smul]
  · by_cases hσ : c.1 σ = 0
    · rw [hσ, smul_zero]
    · change smallChainMap ℤ 𝒰 n (Finsupp.single (SingularCochain.simplexEquiv Y _ σ) 1)
        (SingularCochain.simplexEquiv Y _ τ) • c.1 σ = 0
      rw [smallChainMap_single_of_subset (hcτ σ hσ), Finsupp.single_eq_of_ne
        (fun h ↦ hστ ((SingularCochain.simplexEquiv Y _).injective h).symm), zero_smul]

variable {R M} in
/-- The inclusion `N' ⊆ N` of subsets of `Y`, as a morphism of `TopCat`. -/
def subsetInclusionOfSubset {N' N : Set Y} (h : N' ⊆ N) : TopCat.of N' ⟶ TopCat.of N :=
  TopCat.ofHom ⟨Set.inclusion h, continuous_inclusion h⟩

omit [CommRing R] in
/-- The inclusion of a closed subset `N' ⊆ N` is a proper map. -/
lemma isProperMap_subsetInclusionOfSubset {N' N : Set Y} (hN' : IsClosed N') (h : N' ⊆ N) :
    IsProperMap (subsetInclusionOfSubset h) :=
  (Topology.IsClosedEmbedding.inclusion h (hN'.preimage continuous_subtype_val)).isProperMap

end borelMooreHomology

namespace BorelMooreCap

open SingularCross BorelMooreCross SingularCochain SingularChain LocallyFiniteChain
  borelMooreHomology

variable {R : Type u} [CommRing R] {Y : TopCat.{u}}

/-- For a locally finite cycle `z`, Hatcher's homotopy gives `z - ρ z = ∂ (D z)`. -/
lemma sub_smallChainMapLF_eq_d (𝒰 : Set (Set Y)) {n : ℕ} {z : (BM R Y).X n}
    (hz : z ∈ Cyc (R := R) Y n) :
    z - ((smallChainMapLF R (ModuleCat.of R R) 𝒰).f n).hom z =
      ((BM R Y).d (n + 1) n).hom ((smallHomotopyMap R (ModuleCat.of R R) 𝒰 n).hom z) := by
  rcases n with _ | k
  · have := congrArg (fun f ↦ f.hom z) (id_sub_smallChainMapLF_zero R (ModuleCat.of R R) 𝒰)
    simpa using this
  · have := congrArg (fun f ↦ f.hom z) (id_sub_smallChainMapLF_succ R (ModuleCat.of R R) 𝒰 k)
    have hz' : ((BM R Y).d (k + 1) k).hom z = 0 := (mem_cyc_iff z).1 hz
    simpa [hz'] using this

/-- `φ ∩ z - φ ∩ ρ z = ∂ (φ ∩ D z)` for a relative cocycle `φ` and a cycle `z`. -/
lemma capChain_sub_capChain_smallChainMapLF (A : Set Y) (𝒰 : Set (Set Y)) (p q n : ℕ)
    (h : p + q = n) (φ : relCocycles R A p) (z : Cyc (R := R) Y n) :
    capChain R p q n h φ.1 z.1 -
        capChain R p q n h φ.1 (((smallChainMapLF R (ModuleCat.of R R) 𝒰).f n).hom z.1) =
      ((BM R Y).d (q + 1) q).hom (capChain R p (q + 1) (n + 1) (by omega) φ.1
        ((smallHomotopyMap R (ModuleCat.of R R) 𝒰 n).hom z.1)) := by
  rw [← map_sub, sub_smallChainMapLF_eq_d 𝒰 z.2, d_capChain_relCocycle A p q n h φ]

/-- In `H_q Y`, `[φ ∩ ρ z] = [φ ∩ z]`. -/
lemma mk_capChain_smallChainMapLF (A : Set Y) (𝒰 : Set (Set Y)) (p q n : ℕ) (h : p + q = n)
    (φ : relCocycles R A p) (z : Cyc (R := R) Y n)
    (hc : capChain R p q n h φ.1 (((smallChainMapLF R (ModuleCat.of R R) 𝒰).f n).hom z.1) ∈
      Cyc (R := R) Y q) :
    (Submodule.Quotient.mk ⟨_, hc⟩ : HomQ (R := R) Y q) =
      Submodule.Quotient.mk (capCyc R A p q n h φ z) := by
  refine ((Submodule.Quotient.eq _).2 ?_).symm
  refine mem_bdry_of _ _ ((capChain_sub_capChain_smallChainMapLF A 𝒰 p q n h φ z).symm.trans ?_)
  rfl

variable {A N : Set Y} (hA : IsOpen A) (hN : IsClosed N) (hAN : A ∪ interior N = univ)

/-- The push-forward along `N ⊆ Y` of the neighbourhood cap product on cocycles modulo
coboundaries and cycles modulo boundaries is the cap product of `Y`. -/
theorem homologyMap_subsetInclusion_capHomQNbhd (p q n : ℕ) (h : p + q = n)
    (x : relCohomology R A p) (y : HomQ (R := R) Y n) :
    (homologyMap R (chainMap R (ModuleCat.of R R) (subsetInclusion N)
        (isProperMap_subsetInclusion hN)) q).hom
      ((homologyEquiv R (TopCat.of N) q).symm (capHomQNbhd R hA hN hAN p q n h x y)) =
      (homologyEquiv R Y q).symm (capHomQ R A p q n h x y) := by
  induction x using Submodule.Quotient.induction_on with | H φ => ?_
  induction y using Submodule.Quotient.induction_on with | H z => ?_
  erw [capHomQNbhd_mk, capHomQ_mk, homologyMap_homologyEquiv_symm_mk]
  congr 1
  have e := chainMap_subsetRestrictMap R (ModuleCat.of R R) hN
    (isSupportedIn_capChain_nbhdSubdiv hA hAN p q n h φ.2.1 z.1)
  refine Eq.trans ?_ (mk_capChain_smallChainMapLF A {A, interior N} p q n h φ z
    (e ▸ chainMap_mem_cyc R _ (capCycNbhd R hA hN hAN p q n h φ z)))
  congr 1
  exact Subtype.ext e

section mono

/-! ### Shrinking the neighbourhood -/

variable {N' : Set Y} (hN' : IsClosed N') (hAN' : A ∪ interior N' = univ) (hN'N : N' ⊆ N)

include hN in
/-- For chains supported in `N' ⊆ N`, restricting to `N'` and pushing forward to `N` is
restricting to `N`. -/
lemma chainMap_subsetInclusionOfSubset_subsetRestrictMap {n : ℕ} {c : (BM R Y).X n}
    (hc : IsSupportedIn R (ModuleCat.of R R) N' c) :
    ((chainMap R (ModuleCat.of R R) (subsetInclusionOfSubset hN'N)
        (isProperMap_subsetInclusionOfSubset hN' hN'N)).f n).hom
      ((subsetRestrictMap R (ModuleCat.of R R) N' n).hom c) =
      (subsetRestrictMap R (ModuleCat.of R R) N n).hom c := by
  apply chainMap_subsetInclusion_injective R _ hN n
  rw [chainMap_subsetRestrictMap R _ hN (fun σ hσ ↦ (hc σ hσ).trans hN'N)]
  have e := chainMap_comp R (ModuleCat.of R R) (subsetInclusionOfSubset hN'N) (subsetInclusion N)
    (isProperMap_subsetInclusionOfSubset hN' hN'N) (isProperMap_subsetInclusion hN)
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← HomologicalComplex.comp_f, ← e]
  exact chainMap_subsetRestrictMap R _ hN' hc

include hA hAN hAN' hN'N in
/-- Hatcher's subdivision towards `{A, int N}` fixes the subdivision towards `{A, int N'}`. -/
lemma nbhdSubdiv_nbhdSubdiv_of_subset {n : ℕ} (c : (BM R Y).X n) :
    (nbhdSubdiv R A N n).hom ((nbhdSubdiv R A N' n).hom c) = (nbhdSubdiv R A N' n).hom c := by
  refine smallChainMapLF_f_hom_of_small R _ _ fun σ hσ ↦ ?_
  obtain ⟨U, hU, hσU⟩ := smallChainMapLF_small R (ModuleCat.of R R)
    (𝒰 := {A, interior N'}) (by rintro U (rfl | rfl) <;> simp [hA])
    (by rwa [sUnion_insert, sUnion_singleton]) n c hσ
  rcases hU with rfl | rfl
  · exact ⟨_, Or.inl rfl, hσU⟩
  · exact ⟨_, Or.inr rfl, hσU.trans (interior_mono hN'N)⟩

include hA hN hAN hAN' hN'N in
/-- In `H_q N`, the classes of `(φ ∩ ρ' z)|_N` and `(φ ∩ ρ z)|_N` agree, for the subdivisions
`ρ'`, `ρ` towards `{A, int N'}` and `{A, int N}`. -/
lemma mk_restrict_capChain_nbhdSubdiv_of_subset (p q n : ℕ) (h : p + q = n)
    (φ : relCocycles R A p) (z : Cyc (R := R) Y n)
    (hc : (subsetRestrictMap R (ModuleCat.of R R) N q).hom
      (capChain R p q n h φ.1 ((nbhdSubdiv R A N' n).hom z.1)) ∈
        Cyc (R := R) (TopCat.of N) q) :
    (Submodule.Quotient.mk ⟨_, hc⟩ : HomQ (R := R) (TopCat.of N) q) =
      Submodule.Quotient.mk (capCycNbhd R hA hN hAN p q n h φ z) := by
  refine (Submodule.Quotient.eq _).2 ?_
  set D' := (smallHomotopyMap R (ModuleCat.of R R) {A, interior N'} n).hom z.1
  have hz : (nbhdSubdiv R A N' n).hom z.1 - (nbhdSubdiv R A N n).hom z.1 =
      -((BM R Y).d (n + 1) n).hom ((nbhdSubdiv R A N (n + 1)).hom D') := by
    have e := sub_smallChainMapLF_eq_d {A, interior N'} z.2
    rw [← nbhdSubdiv_d, ← nbhdSubdiv_nbhdSubdiv_of_subset hA hAN hAN' hN'N z.1, ← map_sub,
      ← map_neg, ← e, neg_sub]
  have hu := isSupportedIn_neg (isSupportedIn_capChain_nbhdSubdiv hA hAN
    p (q + 1) (n + 1) (by omega) φ.2.1 D')
  refine restrict_d_mem_bdry hN _ hu _ ?_
  change (subsetRestrictMap R (ModuleCat.of R R) N q).hom
      (capChain R p q n h φ.1 ((nbhdSubdiv R A N' n).hom z.1)) -
    (subsetRestrictMap R (ModuleCat.of R R) N q).hom
      (capChain R p q n h φ.1 ((nbhdSubdiv R A N n).hom z.1)) = _
  rw [← map_sub, ← map_sub, hz, map_neg, ← d_capChain_relCocycle A p q n h φ]
  simp only [map_neg]

include hN'N in
/-- Shrinking the neighbourhood: for closed neighbourhoods `N' ⊆ N`, the neighbourhood cap
product into `H_q N'` pushes forward to the one into `H_q N`. -/
theorem homologyMap_subsetInclusionOfSubset_capHomQNbhd (p q n : ℕ) (h : p + q = n)
    (x : relCohomology R A p) (y : HomQ (R := R) Y n) :
    (homologyMap R (chainMap R (ModuleCat.of R R) (subsetInclusionOfSubset hN'N)
        (isProperMap_subsetInclusionOfSubset hN' hN'N)) q).hom
      ((homologyEquiv R (TopCat.of N') q).symm (capHomQNbhd R hA hN' hAN' p q n h x y)) =
      (homologyEquiv R (TopCat.of N) q).symm (capHomQNbhd R hA hN hAN p q n h x y) := by
  induction x using Submodule.Quotient.induction_on with | H φ => ?_
  induction y using Submodule.Quotient.induction_on with | H z => ?_
  erw [capHomQNbhd_mk, capHomQNbhd_mk, homologyMap_homologyEquiv_symm_mk]
  congr 1
  have e := chainMap_subsetInclusionOfSubset_subsetRestrictMap hN hN' hN'N
    (isSupportedIn_capChain_nbhdSubdiv hA hAN' p q n h φ.2.1 z.1)
  refine Eq.trans ?_ (mk_restrict_capChain_nbhdSubdiv_of_subset hA hN hAN hAN' hN'N p q n h φ z
    (e ▸ chainMap_mem_cyc R _ (capCycNbhd R hA hN' hAN' p q n h φ z)))
  congr 1
  exact Subtype.ext e

end mono

end BorelMooreCap

namespace borelMooreHomology

open BorelMooreCap BorelMooreCross SingularCochain

variable (R : Type u) [CommRing R]

/-- **Compatibility of the neighbourhood cap product.** For a closed neighbourhood `N` of a closed
subset `X ⊆ Y`, the push-forward along the inclusion `ι : N → Y` of `c ∩_N a ∈ H_{k-j} N` is the
cap product `c ∩ a ∈ H_{k-j} Y`. -/
theorem pushforward_subsetInclusion_capProductNbhd (Y : TopCat.{u}) {X N : Set Y}
    (hX : IsClosed X) (hN : IsClosed N) (hXN : X ⊆ interior N) (j k : ℤ)
    (c : cohomologyWithSupports R (ModuleCat.of R R) Y X j)
    (a : borelMooreHomology R (ModuleCat.of R R) Y k) :
    (pushforward R (ModuleCat.of R R) (subsetInclusion N) (isProperMap_subsetInclusion hN)
        (k - j)).hom (capProductNbhd R Y hX hN hXN j k c a) = capProduct R Y X j k c a := by
  unfold capProductNbhd capProduct
  split_ifs with h
  · simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_trans_apply, congrDegree_symm, pushforward_eq_homologyMap]
    rw [homologyMap_congrDegree, homologyMap_subsetInclusion_capHomQNbhd]
  · simp

/-- **Shrinking the neighbourhood.** For closed neighbourhoods `N' ⊆ N` of a closed subset
`X ⊆ Y`, the push-forward along `N' ⊆ N` of `c ∩_{N'} a` is `c ∩_N a`. -/
theorem pushforward_subsetInclusionOfSubset_capProductNbhd (Y : TopCat.{u}) {X N N' : Set Y}
    (hX : IsClosed X) (hN : IsClosed N) (hXN : X ⊆ interior N) (hN' : IsClosed N')
    (hXN' : X ⊆ interior N') (hN'N : N' ⊆ N) (j k : ℤ)
    (c : cohomologyWithSupports R (ModuleCat.of R R) Y X j)
    (a : borelMooreHomology R (ModuleCat.of R R) Y k) :
    (pushforward R (ModuleCat.of R R) (subsetInclusionOfSubset hN'N)
        (isProperMap_subsetInclusionOfSubset hN' hN'N) (k - j)).hom
      (capProductNbhd R Y hX hN' hXN' j k c a) = capProductNbhd R Y hX hN hXN j k c a := by
  unfold capProductNbhd
  split_ifs with h
  · simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_trans_apply, congrDegree_symm, pushforward_eq_homologyMap]
    rw [homologyMap_congrDegree, homologyMap_subsetInclusionOfSubset_capHomQNbhd]
  · simp

/-- **Independence of the neighbourhood.** For closed neighbourhoods `N' ⊆ N` of `X` and a
proper map `f : N → Z`, the cap product along `f` agrees with the cap product along the
restriction of `f` to `N'`. -/
theorem capProductAlong_comp_subsetInclusionOfSubset (Y : TopCat.{u}) {X N N' : Set Y}
    (hX : IsClosed X) (hN : IsClosed N) (hXN : X ⊆ interior N) (hN' : IsClosed N')
    (hXN' : X ⊆ interior N') (hN'N : N' ⊆ N) {Z : TopCat.{u}} (f : TopCat.of N ⟶ Z)
    (hf : IsProperMap f) (j k : ℤ) :
    capProductAlong R Y hX hN' hXN' (subsetInclusionOfSubset hN'N ≫ f)
        (hf.comp (isProperMap_subsetInclusionOfSubset hN' hN'N)) j k =
      capProductAlong R Y hX hN hXN f hf j k := by
  ext c a
  simp only [capProductAlong, LinearMap.compr₂_apply]
  rw [pushforward_comp R (ModuleCat.of R R) _ f (isProperMap_subsetInclusionOfSubset hN' hN'N) hf,
    ModuleCat.hom_comp, LinearMap.comp_apply,
    pushforward_subsetInclusionOfSubset_capProductNbhd]

end borelMooreHomology

end MMP
