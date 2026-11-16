module

public import MMP.AlgebraicTopology.CapProduct.ExteriorProduct
public import MMP.AlgebraicTopology.CapProduct.Support
public import MMP.AlgebraicTopology.FundamentalClass.Product
public import MMP.AlgebraicTopology.FundamentalClass.Locality
public import MMP.AlgebraicTopology.BorelMoore.ExteriorProductNatural
public import MMP.AlgebraicTopology.OrientationClass.CapProductPointClass
public import MMP.AlgebraicTopology.FundamentalClass.Homeomorphism

/-!
# The cap product with a class supported at a point (Fulton, §19.1)

Let `x` be a closed point of a space `Y` with arbitrarily small proper neighbourhood deformations
(so that the cap product `∩ : H^n(Y, Y - x) ⊗ H_n Y → H_0 {x}` of `capProductSupport` is
defined). For `c` represented by a relative cocycle `φ` of `(Y, Y - x)` and `a` by a locally finite
cycle `z`, the class `c ∩ a ∈ H_0 {x} ≅ R` is the local pairing `⟨φ, z⟩_x`
(`MMP.borelMooreHomology.localPairing_capProductSupport_singleton`).

**Proof.** `c ∩ a = r_* [(φ ∩ ρ z)|_N]` for a compact neighbourhood `N` of `x` with retraction
`r : N → {x}`. On the point, a `0`-cycle pairs with `ψ` to the sum of its coefficients times
`ψ(pt)`; that sum is preserved by `r_*` and by restriction to `N`, and for the cap product of an
`n`-cochain with an `n`-chain it is `∑_σ (ρ z)_σ φ(σ) = ⟨φ, ρ z⟩`; finally
`⟨φ, ρ z⟩ = ⟨φ, z⟩` since `z - ρ z = ∂ (D z)` and `φ` is a cocycle.

As a consequence, the cap product of the local orientation class `u_t` at a point `t` of an
oriented manifold with its fundamental class is the class of the point
(`MMP.isLocallyClassOf_capProductSupport_of_isLocalOrientationClass`): the case of
a point of Fulton's `u_{M,P} ∩ μ_P = μ_M`.

## Main results

* `MMP.borelMooreHomology.localPairing_capProductSupport_singleton`.
* `MMP.borelMooreHomology.isLocallyClassOf_capProductSupport_singleton`: if `a`
  is locally the class of `Δ` at `x` and `c` takes the value `1` on `Δ`, then `c ∩ a` is the
  class of the point.
* `MMP.isLocallyClassOf_capProductSupport_of_isLocalOrientationClass`:
  `u_t ∩ μ = [t]`.

## Implementation notes

The chain-level formula of the cap product is used once, in
`MMP.BorelMooreCap.capChain_top_finite_and_finsum` (through `capChain_apply`'s
definitional unfolding `capChain φ c = pf front (W (wt φ back) c)`, Fulton's convention
`φ (σ ⌊ [q, …, n]) σ ⌊ [0, …, q]`): with `q = 0` the coefficient is `φ(σ)` on the vertex
`σ ⌊ [0]`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Simplicial Set

universe u

namespace MMP

open MMP

namespace LocallyFiniteChain

variable {S T M : Type*} [AddCommGroup M]

/-- Push-forward of a finitely supported coefficient function preserves the sum of the
coefficients. -/
lemma finsum_pushforwardFun (f : S → T) (g : S → M) (hg : (Function.support g).Finite) :
    ∑ᶠ τ, pushforwardFun f g τ = ∑ᶠ σ, g σ := by
  classical
  set F := hg.toFinset
  have h1 : ∀ τ, pushforwardFun f g τ = ∑ σ ∈ F, if f σ = τ then g σ else 0 := fun τ ↦
    pushforwardFun_apply_eq_sum f g τ F (fun σ h _ ↦ hg.mem_toFinset.2 h)
  rw [finsum_eq_sum_of_support_subset (s := F.image f) _ ?_,
    finsum_eq_sum_of_support_subset (s := F) _ (by simp [F])]
  · simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ hσ ↦ ?_
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_image_of_mem f hσ)]
  · intro τ hτ
    rw [Function.mem_support, h1] at hτ
    obtain ⟨σ, hσ, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero hτ
    split_ifs at h with he
    · exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨σ, hσ, he⟩)
    · exact absurd rfl h

/-- The push-forward of a finitely supported coefficient function is finitely supported. -/
lemma support_pushforwardFun_finite (f : S → T) (g : S → M) (hg : (Function.support g).Finite) :
    (Function.support (pushforwardFun f g)).Finite := by
  classical
  refine (hg.image f).subset fun τ hτ ↦ ?_
  rw [Function.mem_support, pushforwardFun_apply_eq_sum f g τ hg.toFinset
    (fun σ h _ ↦ hg.mem_toFinset.2 h)] at hτ
  obtain ⟨σ, hσ, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero hτ
  split_ifs at h with he
  · exact ⟨σ, hg.mem_toFinset.1 hσ, he⟩
  · exact absurd rfl h

end LocallyFiniteChain

namespace BorelMooreCap

open MMP.BorelMooreCap

open BorelMooreCross SingularCross SingularChain SingularCochain FundamentalClass LocallyFiniteChain

variable {R : Type u} [CommRing R] {Y : TopCat.{u}}

/-- For an `n`-simplex `σ`, whose back `n`-face `back n n 0 h` is `σ` itself, the weight
`wt φ (back n n 0 h) σ` is the value of `φ` on `σ`. -/
lemma wt_back_self {n : ℕ} (φ : Simplex Y n → R) (h : n + 0 ≤ n) (σ : Simp Y n) :
    wt φ (back n n 0 h) σ = φ (SingularCochain.simplexEquiv Y _ σ) := by
  have : back n n 0 h = id := funext fun j ↦ Fin.ext rfl
  rw [wt, this]
  congr 1
  ext1 t
  exact congrArg (simplexEquiv Y n σ) (stdSimplex.map_id_apply t)

/-- The cap product of an `n`-cochain `φ` vanishing off a point `x` with a locally finite
`n`-chain `c` is a finite `0`-chain, and the sum of its coefficients is the local pairing
`⟨φ, c⟩`. -/
lemma capChain_top_finite_and_finsum {n : ℕ} {x : Y} {φ : Simplex Y n → R}
    (hφ : φ ∈ vanishing R n ({x}ᶜ : Set Y)) (c : (BM R Y).X n) :
    (Function.support (coeff R (capChain R n 0 n (add_zero n) φ c))).Finite ∧
      ∑ᶠ τ, coeff R (capChain R n 0 n (add_zero n) φ c) τ = localPairing (coeff R c) φ := by
  have hg : (Function.support fun σ ↦ wt φ (back n n 0 (by omega)) σ * coeff R c σ).Finite := by
    refine (finite_support_mul (coeff_mem R c) hφ).subset fun σ hσ ↦ ?_
    rw [Function.mem_support, wt_back_self] at hσ
    rw [Function.mem_support, mul_comm]
    exact hσ
  have e : coeff R (capChain R n 0 n (add_zero n) φ c) =
      pushforwardFun (opS (front 0 n (by omega)))
        (fun σ ↦ wt φ (back n n 0 (by omega)) σ * coeff R c σ) := rfl
  refine ⟨e ▸ support_pushforwardFun_finite _ _ hg, ?_⟩
  rw [e, finsum_pushforwardFun _ _ hg, localPairing]
  exact finsum_congr fun σ ↦ by rw [wt_back_self, mul_comm]

end BorelMooreCap

namespace borelMooreHomology

open MMP.borelMooreHomology

open BorelMooreCross BorelMooreCap SingularCross SingularChain SingularCochain FundamentalClass
  LocallyFiniteChain

variable {R : Type u} [CommRing R]

/-- On a space with at most one point, the local pairing of a chain with a cochain is the sum of
its coefficients times the value of the cochain on the (unique) simplex. -/
lemma localPairing_of_subsingleton {X : TopCat.{u}} [Subsingleton X] {n : ℕ}
    (w : Simp X n → R) (ψ : Simplex X n → R)
    (Δ : Simplex X n) : localPairing w ψ = (∑ᶠ τ, w τ) * ψ Δ := by
  have hs : ∀ τ : Simp X n, SingularCochain.simplexEquiv X _ τ = Δ := fun τ ↦
    ContinuousMap.ext fun t ↦ Subsingleton.elim _ _
  haveI : Subsingleton (Simp X n) :=
    ⟨fun a b ↦ (SingularCochain.simplexEquiv X _).injective ((hs a).trans (hs b).symm)⟩
  rw [localPairing]
  simp_rw [hs]
  rw [finsum_mul' _ _ (Set.toFinite _)]

/-- The sum of the coefficients of a finitely supported chain is preserved by push-forward. -/
lemma finsum_coeff_chainMap {X X' : TopCat.{u}} (f : X ⟶ X') (hf : IsProperMap f) {n : ℕ}
    (c : (BM R X).X n) (hc : (Function.support (coeff R c)).Finite) :
    (Function.support (coeff R (((chainMap R (ModuleCat.of R R) f hf).f n).hom c))).Finite ∧
      ∑ᶠ τ, coeff R (((chainMap R (ModuleCat.of R R) f hf).f n).hom c) τ =
        ∑ᶠ σ, coeff R c σ := by
  have e : coeff R (((chainMap R (ModuleCat.of R R) f hf).f n).hom c) =
      pushforwardFun ((TopCat.toSSet.map f).app _) (coeff R c) := rfl
  rw [e]
  exact ⟨support_pushforwardFun_finite _ _ hc, finsum_pushforwardFun _ _ hc⟩

/-- The restriction to a closed subset `N` of a finitely supported chain supported in `N` is
finitely supported, with the same sum of coefficients. -/
lemma finsum_coeff_subsetRestrictMap {Y : TopCat.{u}} {N : Set Y} (hN : IsClosed N) {n : ℕ}
    (c : (BM R Y).X n) (hc : (Function.support (coeff R c)).Finite)
    (hcN : IsSupportedIn R (ModuleCat.of R R) N c) :
    (Function.support (coeff R ((subsetRestrictMap R (ModuleCat.of R R) N n).hom c))).Finite ∧
      ∑ᶠ τ, coeff R ((subsetRestrictMap R (ModuleCat.of R R) N n).hom c) τ =
        ∑ᶠ σ, coeff R c σ := by
  have hfin : (Function.support
      (coeff R ((subsetRestrictMap R (ModuleCat.of R R) N n).hom c))).Finite := by
    refine (hc.preimage (map_subsetInclusion_injective n).injOn).subset fun τ hτ ↦ ?_
    rw [Function.mem_support] at hτ
    change coeff R c _ ≠ 0
    rwa [show coeff R ((subsetRestrictMap R (ModuleCat.of R R) N n).hom c) τ =
      coeff R c _ from subsetRestrictMap_apply_coe R (ModuleCat.of R R) c τ] at hτ
  refine ⟨hfin, ?_⟩
  have h := (finsum_coeff_chainMap (subsetInclusion N) (isProperMap_subsetInclusion hN) _ hfin).2
  rw [chainMap_subsetRestrictMap R (ModuleCat.of R R) hN hcN] at h
  exact h.symm

/-- Hatcher's subdivision `ρ` of a locally finite cycle does not change its local pairings:
`z - ρ z = ∂ (D z)`. -/
lemma localPairing_smallChainMapLF {Y : TopCat.{u}} (𝒰 : Set (Set Y)) {n : ℕ}
    {z : (BM R Y).X n} (hz : z ∈ Cyc (R := R) Y n) {x : Y} {φ : Simplex Y n → R}
    (hφ : φ ∈ relCocycles R ({x}ᶜ : Set Y) n) :
    localPairing (coeff R (((smallChainMapLF R (ModuleCat.of R R) 𝒰).f n).hom z)) φ =
      localPairing (coeff R z) φ := by
  have e := sub_smallChainMapLF_eq_d 𝒰 hz
  have e2 : z = ((smallChainMapLF R (ModuleCat.of R R) 𝒰).f n).hom z +
      ((BM R Y).d (n + 1) n).hom ((smallHomotopyMap R (ModuleCat.of R R) 𝒰 n).hom z) := by
    rw [← e]
    abel
  conv_rhs => rw [e2]
  change _ = localPairing (coeff R (((smallChainMapLF R (ModuleCat.of R R) 𝒰).f n).hom z) +
    coeff R (((BM R Y).d (n + 1) n).hom ((smallHomotopyMap R (ModuleCat.of R R) 𝒰 n).hom z))) φ
  rw [localPairing_add (coeff_mem R _) (coeff_mem R _) hφ.1]
  rw [show localPairing (coeff R (((BM R Y).d (n + 1) n).hom
      ((smallHomotopyMap R (ModuleCat.of R R) 𝒰 n).hom z))) φ = 0 from
    localPairing_d_eq_zero _ hφ, add_zero]

/-- **The chain-level computation.** For a closed neighbourhood `N` of a point `x` with a proper
map `r : N → {x}`, a relative cocycle `φ` of `(Y, Y - x)` of degree `n` and a locally finite
`n`-cycle `z`, the push-forward to `{x}` of the cap product cycle `(φ ∩ ρ z)|_N` pairs with every
`0`-cochain `ψ` of the point to `⟨φ, z⟩ ψ(pt)`. -/
lemma localPairing_chainMap_capCycNbhd {Y : TopCat.{u}} {x : Y} {N : Set Y}
    (hA : IsOpen ({x}ᶜ : Set Y)) (hN : IsClosed N) (hAN : ({x}ᶜ : Set Y) ∪ interior N = univ)
    (r : TopCat.of N ⟶ TopCat.of ({x} : Set Y)) (hr : IsProperMap r) {n q : ℕ} (h : n + q = n)
    (φ : relCocycles R ({x}ᶜ : Set Y) n) (z : Cyc (R := R) Y n)
    (ψ : Simplex (TopCat.of ({x} : Set Y)) q → R) (Δ : Simplex (TopCat.of ({x} : Set Y)) q) :
    localPairing (coeff R (((chainMap R (ModuleCat.of R R) r hr).f q).hom
        (capCycNbhd R hA hN hAN n q n h φ z).1)) ψ =
      localPairing (coeff R z.1) φ.1 * ψ Δ := by
  obtain rfl : q = 0 := by omega
  set C := capChain R n 0 n h φ.1 ((nbhdSubdiv R ({x}ᶜ : Set Y) N n).hom z.1) with hC
  obtain ⟨h1, h2⟩ := capChain_top_finite_and_finsum φ.2.1
    ((nbhdSubdiv R ({x}ᶜ : Set Y) N n).hom z.1)
  have hCN : IsSupportedIn R (ModuleCat.of R R) N C :=
    isSupportedIn_capChain_nbhdSubdiv hA hAN n 0 n h φ.2.1 _
  obtain ⟨h3, h4⟩ := finsum_coeff_subsetRestrictMap hN C h1 hCN
  obtain ⟨-, h5⟩ := finsum_coeff_chainMap r hr _ h3
  rw [localPairing_of_subsingleton _ ψ Δ]
  change (∑ᶠ τ, coeff R (((chainMap R (ModuleCat.of R R) r hr).f 0).hom
    ((subsetRestrictMap R (ModuleCat.of R R) N 0).hom C)) τ) * _ = _
  rw [h5, h4, h2, localPairing_smallChainMapLF _ z.2 φ.2]

/-- Push-forward of Borel–Moore homology commutes with the reindexing isomorphisms
`congrDegree` between equal degrees. -/
lemma congrDegree_pushforward_congrDegree {X X' : TopCat.{u}} (f : X ⟶ X') (hf : IsProperMap f)
    {q : ℕ} {i j : ℤ} (h : (q : ℤ) = i) (h' : i = j)
    (v : borelMooreHomology R (ModuleCat.of R R) X q) :
    congrDegree R X' h' ((pushforward R (ModuleCat.of R R) f hf i).hom (congrDegree R X h v)) =
      congrDegree R X' (h.trans h') ((pushforward R (ModuleCat.of R R) f hf q).hom v) := by
  subst h h'
  rfl

/-- The class `(homologyEquiv X 0)⁻¹ [w]` is the class of the cycle `w`. -/
lemma homologyEquiv_symm_mk_eq {X : TopCat.{u}} {p : ℕ} (w : Cyc (R := R) X p) :
    (homologyEquiv R X p).symm (Submodule.Quotient.mk w) =
      (borelMooreHomologyIsoOfNat R (ModuleCat.of R R) X p).inv.hom
        ((borelMooreChainComplex R (ModuleCat.of R R) X).homologyπ p
          (((borelMooreChainComplex R (ModuleCat.of R R) X).sc p).moduleCatCyclesIso.inv.hom
            w)) := by
  have := congrArg (fun m ↦ m.hom w)
    ((borelMooreChainComplex R (ModuleCat.of R R) X).sc p).moduleCatCyclesIso_inv_π
  exact (congrArg (borelMooreHomologyIsoOfNat R (ModuleCat.of R R) X p).inv.hom this).symm

/-- The underlying chain of the homology cycle corresponding to a cycle `w` is `w`. -/
lemma iCycles_moduleCatCyclesIso_inv {X : TopCat.{u}} {p : ℕ} (w : Cyc (R := R) X p) :
    (borelMooreChainComplex R (ModuleCat.of R R) X).iCycles p
        (((borelMooreChainComplex R (ModuleCat.of R R) X).sc p).moduleCatCyclesIso.inv.hom w) =
      w.1 := by
  refine (coe_moduleCatCyclesIso_hom (R := R) _).symm.trans ?_
  exact congrArg Subtype.val (ConcreteCategory.congr_hom
    ((borelMooreChainComplex R (ModuleCat.of R R) X).sc p).moduleCatCyclesIso.inv_hom_id w)

/-- The homology form of `localPairing_chainMap_capCycNbhd`, in the degrees produced by
`capProductNbhd_natCast`. -/
lemma localPairing_of_homologyπ_eq_pushforward_capCycNbhd {Y : TopCat.{u}} {x : Y} {N : Set Y}
    (hA : IsOpen ({x}ᶜ : Set Y)) (hN : IsClosed N) (hAN : ({x}ᶜ : Set Y) ∪ interior N = univ)
    (r : TopCat.of N ⟶ TopCat.of ({x} : Set Y)) (hr : IsProperMap r) {n q : ℕ} (h : n + q = n)
    (h3 : (q : ℤ) = (n : ℤ) - n) (h0 : (n : ℤ) - n = ((0 : ℕ) : ℤ))
    (φ : relCocycles R ({x}ᶜ : Set Y) n) (z : Cyc (R := R) Y n)
    (w : (borelMooreChainComplex R (ModuleCat.of R R) (TopCat.of ({x} : Set Y))).cycles 0)
    (hw : (borelMooreChainComplex R (ModuleCat.of R R) (TopCat.of ({x} : Set Y))).homologyπ 0 w =
      (borelMooreHomologyIsoOfNat R (ModuleCat.of R R) (TopCat.of ({x} : Set Y)) 0).hom
        (congrDegree R _ h0 ((pushforward R (ModuleCat.of R R) r hr ((n : ℤ) - n)).hom
          (congrDegree R (TopCat.of N) h3 ((homologyEquiv R (TopCat.of N) q).symm
            (Submodule.Quotient.mk (capCycNbhd R hA hN hAN n q n h φ z)))))))
    {y : TopCat.of ({x} : Set Y)} (ψ : Simplex (TopCat.of ({x} : Set Y)) 0 → R)
    (hψ : ψ ∈ relCocycles R ({y}ᶜ : Set (TopCat.of ({x} : Set Y))) 0)
    (Δ : Simplex (TopCat.of ({x} : Set Y)) 0) :
    localPairing (((borelMooreChainComplex R (ModuleCat.of R R)
        (TopCat.of ({x} : Set Y))).iCycles 0 w).1 :
          (TopCat.toSSet.obj (TopCat.of ({x} : Set Y))).obj (op ⦋0⦌) → R) ψ =
      localPairing (coeff R z.1) φ.1 * ψ Δ := by
  obtain rfl : q = 0 := by omega
  rw [congrDegree_pushforward_congrDegree, congrDegree_self, LinearEquiv.refl_apply,
    pushforward_eq_homologyMap, homologyMap_homologyEquiv_symm_mk] at hw
  erw [homologyEquiv_symm_mk_eq, Iso.inv_hom_id_apply] at hw
  rw [localPairing_eq_of_homologyπ_eq hw hψ]
  erw [iCycles_moduleCatCyclesIso_inv]
  exact localPairing_chainMap_capCycNbhd hA hN hAN r hr h φ z ψ Δ

variable (R) in
/-- **The cap product into a point is the local pairing.** Let `x` be a closed point of a space
`Y` with arbitrarily small proper neighbourhood deformations, `c ∈ H^n(Y, Y - x)` represented by
a relative cocycle `φ` and `a ∈ H_n Y` represented by a locally finite cycle `z`. Then
`c ∩ a ∈ H_0 {x}` pairs with every `0`-cocycle `ψ` of the point to `⟨φ, z⟩_x ψ(pt)`: it is
`⟨φ, z⟩_x` times the class of the point. -/
theorem localPairing_capProductSupport_singleton {Y : TopCat.{u}} {x : Y}
    (hx : IsClosed ({x} : Set Y)) (hxd : HasProperNeighbourhoodDeformations ({x} : Set Y))
    {n : ℕ} (c : cohomologyWithSupports R (ModuleCat.of R R) Y {x} n)
    (a : borelMooreHomology R (ModuleCat.of R R) Y n)
    (z : (borelMooreChainComplex R (ModuleCat.of R R) Y).cycles n)
    (hz : (borelMooreChainComplex R (ModuleCat.of R R) Y).homologyπ n z =
      (borelMooreHomologyIsoOfNat R (ModuleCat.of R R) Y n).hom a)
    (φ : Simplex Y n → R) (hφ : φ ∈ relCocycles R ({x}ᶜ : Set Y) n)
    (hc : relativeSingularCohomologyEquiv R ({x}ᶜ : Set Y) n c = Submodule.Quotient.mk ⟨φ, hφ⟩)
    (h0 : (n : ℤ) - n = ((0 : ℕ) : ℤ))
    (w : (borelMooreChainComplex R (ModuleCat.of R R) (TopCat.of ({x} : Set Y))).cycles 0)
    (hw : (borelMooreChainComplex R (ModuleCat.of R R) (TopCat.of ({x} : Set Y))).homologyπ 0 w =
      (borelMooreHomologyIsoOfNat R (ModuleCat.of R R) (TopCat.of ({x} : Set Y)) 0).hom
        (congrDegree R _ h0 (capProductSupport R Y hx hxd n n c a)))
    {y : TopCat.of ({x} : Set Y)} (ψ : Simplex (TopCat.of ({x} : Set Y)) 0 → R)
    (hψ : ψ ∈ relCocycles R ({y}ᶜ : Set (TopCat.of ({x} : Set Y))) 0)
    (Δ : Simplex (TopCat.of ({x} : Set Y)) 0) :
    localPairing (((borelMooreChainComplex R (ModuleCat.of R R)
        (TopCat.of ({x} : Set Y))).iCycles 0 w).1 :
          (TopCat.toSSet.obj (TopCat.of ({x} : Set Y))).obj (op ⦋0⦌) → R) ψ =
      localPairing (((borelMooreChainComplex R (ModuleCat.of R R) Y).iCycles n z).1 :
          (TopCat.toSSet.obj Y).obj (op ⦋n⦌) → R) φ * ψ Δ := by
  obtain ⟨N, hN, hxN, r, hr, hrx⟩ := hxd.exists_retraction
  rw [capProductSupport_eq_capProductAlong R Y hx hxd hN hxN r hr hrx, capProductAlong,
    LinearMap.compr₂_apply, capProductNbhd_natCast R Y hx hN hxN (le_refl n), hc,
    homologyEquiv_eq_mk z hz] at hw
  rw [localPairing_of_homologyπ_eq_pushforward_capCycNbhd _ hN _ (TopCat.ofHom r) hr _ _ h0
    ⟨φ, hφ⟩ (((borelMooreChainComplex R (ModuleCat.of R R) Y).sc n).moduleCatCyclesIso.hom.hom z)
    w hw ψ hψ Δ]
  erw [coe_moduleCatCyclesIso_hom]
  rfl

variable (R) in
/-- **The cap product with a class supported at a point**, in local-class form: if `a ∈ H_n Y`
is locally the class of the simplex `Δ` at `x` and `c ∈ H^n(Y, Y - x)` takes the value `1` on
`Δ`, then `c ∩ a ∈ H_0 {x}` is the class of the point. -/
theorem isLocallyClassOf_capProductSupport_singleton {Y : TopCat.{u}} {x : Y}
    (hx : IsClosed ({x} : Set Y)) (hxd : HasProperNeighbourhoodDeformations ({x} : Set Y))
    {n : ℕ} (c : cohomologyWithSupports R (ModuleCat.of R R) Y {x} n)
    (a : borelMooreHomology R (ModuleCat.of R R) Y n) {Δ : Simplex Y n}
    (ha : IsLocallyClassOf R a x Δ)
    (hc : ∃ (φ : Simplex Y n → R) (hφ : φ ∈ relCocycles R ({x}ᶜ : Set Y) n),
      relativeSingularCohomologyEquiv R ({x}ᶜ : Set Y) n c = Submodule.Quotient.mk ⟨φ, hφ⟩ ∧
        φ Δ = 1)
    (h0 : (n : ℤ) - n = ((0 : ℕ) : ℤ)) (y : TopCat.of ({x} : Set Y))
    (Δ₀ : Simplex (TopCat.of ({x} : Set Y)) 0) :
    IsLocallyClassOf R (congrDegree R _ h0 (capProductSupport R Y hx hxd n n c a)) y Δ₀ := by
  intro w hw ψ hψ
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective
    ((borelMooreChainComplex R (ModuleCat.of R R) Y).homologyπ n)).1 inferInstance
    ((borelMooreHomologyIsoOfNat R (ModuleCat.of R R) Y n).hom a)
  obtain ⟨φ, hφ, hrep, h1⟩ := hc
  rw [localPairing_capProductSupport_singleton R hx hxd c a z hz φ hφ hrep h0 w hw ψ hψ Δ₀,
    ha z hz φ hφ, h1, one_mul]

end borelMooreHomology

open borelMooreHomology FundamentalClass ThomClass SingularChain SingularCochain BorelMooreCross

variable {R : Type u} [CommRing R]

/-- **`u_t ∩ μ = [t]`.** On a Hausdorff manifold `M` (charts in a finite-dimensional real
space `H`, oriented by the basis `b`), the cap product of the local orientation class
`u_t ∈ H^n(M, M - t)` at a point `t` with a fundamental class `μ_M ∈ H_n M` is the class of the
point in `H_0 {t}`. This is the case of a point of `lem_ext_c19_orientation_class_cap_fundamental`
(`u_{M,P} ∩ μ_P = μ_M`). -/
theorem isLocallyClassOf_capProductSupport_of_isLocalOrientationClass {M : Type u}
    [TopologicalSpace M] [T2Space M] {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [FiniteDimensional ℝ H] [ChartedSpace H M] {n : ℕ} (b : Module.Basis (Fin n) ℝ H) {t : M}
    (htd : HasProperNeighbourhoodDeformations ({t} : Set M))
    {μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of M) n}
    (hμ : IsFundamentalClass R b μ)
    {u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of M) {t} n}
    (hu : IsLocalOrientationClass R b (T := TopCat.of M) t u)
    (h0 : (n : ℤ) - n = ((0 : ℕ) : ℤ)) (y : TopCat.of ({t} : Set M))
    (Δ₀ : Simplex (TopCat.of ({t} : Set M)) 0) :
    IsLocallyClassOf R (congrDegree R _ h0
      (capProductSupport R (TopCat.of M) isClosed_singleton htd n n u μ)) y Δ₀ := by
  obtain ⟨α, hα, hcoc, hrep⟩ := hu
  set e := chartAt H t
  have ht : t ∈ e.source := mem_chart_source H t
  obtain ⟨v, hv, hvt⟩ := exists_isOrientedSimplexAroundZero_subset b (e t)
    (e.open_target.mem_nhds (e.map_source ht))
  have hloc := (hμ e (chart_mem_atlas H t) ⟨t, ht⟩ v hv hvt).of_restrict
  refine isLocallyClassOf_capProductSupport_singleton R isClosed_singleton htd u μ hloc
    ⟨α, hα, hrep, ?_⟩ h0 y Δ₀
  have h1 := hcoc.2 e (chart_mem_atlas H t) ht v hv hvt
  rw [SingularCochain.eval, Finsupp.linearCombination_single, one_smul] at h1
  exact h1

end MMP
