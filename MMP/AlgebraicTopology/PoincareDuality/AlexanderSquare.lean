module

public import MMP.AlgebraicTopology.PoincareDuality.AlexanderConnecting
public import MMP.AlgebraicTopology.PoincareDuality.DualClassSupport
public import MMP.AlgebraicTopology.CapProduct.Restriction

/-!
# The connecting square of Alexander duality on Borel–Moore homology groups

For a closed subset `X` of a Hausdorff space `Y`, `U = Y - X`, a closed neighbourhood `N` of `X`
with a proper retraction `r : N → X` and a proper deformation `G` of `N` into `X` fixing `X` and
ending at `r`: for `x ∈ H^p U` and `μ ∈ H_{p+k+1} Y`,
`∂ (x ∩ μ|_U) = -(-1) ^ k • (δ x ∩ μ)` in `H_k X`, `∂` the Borel–Moore connecting map of the
pair and `δ` the coboundary `H^p U → H^{p+1}(Y, U)`. This is the chain-level square
`connecting_homologyEquiv_symm_mk_capChain_eq_smul` read on Fulton's groups.

## Main results

* `MMP.borelMooreHomology.capProduct_natCast`: the cap product in degrees
  `j ≤ m : ℕ`, on cocycles and cycles.
* `MMP.borelMooreHomology.connecting_capProduct_restrict`: the connecting square.
-/

@[expose] public noncomputable section

open CategoryTheory Set Topology

universe u

namespace MMP

open MMP

namespace borelMooreHomology

open MMP.borelMooreHomology

open BorelMooreCap SingularChain SingularCochain BorelMooreCross

variable {R : Type u} [CommRing R]

/-- The cap product in degrees `j ≤ m : ℕ`, on cocycles modulo coboundaries and cycles modulo
boundaries. -/
lemma capProduct_natCast (Y : TopCat.{u}) (X : Set Y) {j m : ℕ} (hjm : j ≤ m)
    (c : cohomologyWithSupports R (ModuleCat.of R R) Y X j)
    (b : borelMooreHomology R (ModuleCat.of R R) Y m) :
    capProduct R Y X j m c b =
      congrDegree R Y (by omega)
        ((homologyEquiv R Y (m - j)).symm
          (capHomQ R Xᶜ j (m - j) m (by omega) (relativeSingularCohomologyEquiv R Xᶜ j c)
            (homologyEquiv R Y m b))) := by
  rw [capProduct, dif_pos ⟨by positivity, by exact_mod_cast hjm⟩]
  simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
    LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply, congrDegree_symm]
  have key : ∀ (j₁ m₁ : ℕ) (e1 : j = j₁) (e2 : m = m₁) (h1 : (j : ℤ) = j₁) (h2 : (m : ℤ) = m₁)
      (h3 : ((m₁ - j₁ : ℕ) : ℤ) = (m : ℤ) - j) (h4 : j₁ + (m₁ - j₁) = m₁),
      congrDegree R Y h3 ((homologyEquiv R Y (m₁ - j₁)).symm
        (capHomQ R Xᶜ j₁ (m₁ - j₁) m₁ h4
          (relativeSingularCohomologyEquiv R Xᶜ j₁ (cohomologyWithSupports.congrIndex R Y rfl h1 c))
          (homologyEquiv R Y m₁ (congrDegree R Y h2 b)))) =
      congrDegree R Y (by omega)
        ((homologyEquiv R Y (m - j)).symm
          (capHomQ R Xᶜ j (m - j) m (by omega) (relativeSingularCohomologyEquiv R Xᶜ j c)
            (homologyEquiv R Y m b))) := by
    rintro j₁ m₁ rfl rfl h1 h2 h3 h4
    rfl
  exact key _ _ (Int.toNat_natCast j).symm (Int.toNat_natCast m).symm _ _ _ _

/-- Two successive degree transports `congrDegree` compose to the transport along the composite
equality. -/
lemma congrDegree_congrDegree_eq (Z : TopCat.{u}) {i i' i'' : ℤ} (h₁ : i = i')
    (h₂ : i' = i'') (x : borelMooreHomology R (ModuleCat.of R R) Z i) :
    congrDegree R Z h₂ (congrDegree R Z h₁ x) = congrDegree R Z (h₁.trans h₂) x := by
  subst h₁ h₂
  rfl

/-- Transporting the cap product `capHomQ` in output degree `q` along `q = q'` gives the cap
product in output degree `q'`. -/
lemma congrDegree_homologyEquiv_symm_capHomQ {Z : TopCat.{u}} (A : Set Z) (p q q' m : ℕ)
    (h : p + q = m) (h' : p + q' = m) (e : (q : ℤ) = q') (φ : relCohomology R A p)
    (z : HomQ (R := R) Z m) :
    congrDegree R Z e ((homologyEquiv R Z q).symm (capHomQ R A p q m h φ z)) =
      (homologyEquiv R Z q').symm (capHomQ R A p q' m h' φ z) := by
  obtain rfl : q = q' := by omega
  rfl

/-- Transporting the cap product `capHomQNbhd` into the neighbourhood `N` in output degree `q`
along `q = q'` gives the same cap product in output degree `q'`. -/
lemma congrDegree_homologyEquiv_symm_capHomQNbhd {Z : TopCat.{u}} {A N : Set Z} (hA : IsOpen A)
    (hN : IsClosed N) (hAN : A ∪ interior N = univ) (p q q' m : ℕ)
    (h : p + q = m) (h' : p + q' = m) (e : (q : ℤ) = q') (φ : relCohomology R A p)
    (z : HomQ (R := R) Z m) :
    congrDegree R (TopCat.of N) e
        ((homologyEquiv R (TopCat.of N) q).symm (capHomQNbhd R hA hN hAN p q m h φ z)) =
      (homologyEquiv R (TopCat.of N) q').symm (capHomQNbhd R hA hN hAN p q' m h' φ z) := by
  obtain rfl : q = q' := by omega
  rfl

section square

variable {Y : TopCat.{u}} [T2Space Y] {X : Set Y} (hX : IsClosed X)

/-- **The connecting square of the pair `(Y, Y - X)`, on Fulton's groups.** Let `N` be a closed
neighbourhood of the closed set `X`, `r : N → X` a proper retraction and `G` a proper deformation
of `N` into `X`, fixing `X`, ending at `r`. For `x ∈ H^p(Y - X)` and `μ ∈ H_{p+k+1} Y`, the
Borel–Moore connecting map sends `x ∩ μ|_{Y - X}` to `-(-1) ^ k` times `δ x ∩ μ ∈ H_k X`. -/
theorem connecting_capProduct_restrict (h : IsRelativeQuasiIso R (ModuleCat.of R R) hX)
    (hXd : HasProperNeighbourhoodDeformations X) {N : Set Y} (hN : IsClosed N)
    (hXN : X ⊆ interior N) {r : C(N, X)} (hr : IsProperMap r)
    (hrX : ∀ y : N, (y : Y) ∈ X → (r y : Y) = y) {G : C(N × unitInterval, Y)}
    (hG : IsProperMap G) (hGX : ∀ y : N, ∀ t, (y : Y) ∈ X → G (y, t) = y)
    (hG0 : ∀ y, G (y, 0) = y) (hGr : ∀ y, G (y, 1) = r y) (p k : ℕ)
    (x : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (complOpens hX)) univ p)
    (μ : borelMooreHomology R (ModuleCat.of R R) Y (p + k + 1 : ℕ)) :
    (connecting R (ModuleCat.of R R) hX h k).hom
        (congrDegree R (TopCat.of (complOpens hX)) (by omega)
          (capProduct R (TopCat.of (complOpens hX)) univ p (p + k + 1 : ℕ) x
            ((restrict R (ModuleCat.of R R) (complOpens hX) (p + k + 1 : ℕ)).hom μ))) =
      (-(-1 : ℤ) ^ k) • congrDegree R (TopCat.of X) (by omega)
        (capProductSupport R Y hX hXd (p + 1 : ℕ) (p + k + 1 : ℕ)
          (cohomologyWithSupports.delta R Y X p x) μ) := by
  obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (homologyEquiv R Y (p + k + 1) μ)
  obtain ⟨ψ, hψ⟩ := Submodule.Quotient.mk_surjective _
    (relativeSingularCohomologyEquiv R (univᶜ : Set (TopCat.of (complOpens hX))) p x)
  set χ : Simplex Y p → R := extendCochain (V := Xᶜ) ψ.1
  have hχ : cochainPullback R (subspaceInclusion Y Xᶜ) p χ = ψ.1 :=
    cochainPullback_extendCochain _
  have hδ := cohomologyWithSupports.delta_mk p x ψ hψ.symm χ hχ
  have hχc : coboundary R p χ ∈ relCocycles R Xᶜ (p + 1) :=
    coboundary_mem_relCocycles_of_cochainPullback (by
      rw [hχ]
      exact ((mem_relCocycles_iff R _ p _).1 ψ.2).2)
  have hχv : coboundary R p χ ∈ vanishing R (p + 1) Xᶜ := ((mem_relCocycles_iff R _ _ _).1 hχc).1
  have hres : homologyEquiv R (TopCat.of (complOpens hX)) (p + k + 1)
      ((restrict R (ModuleCat.of R R) (complOpens hX) (p + k + 1 : ℕ)).hom μ) =
        Submodule.Quotient.mk ⟨((restrictChainMap R (ModuleCat.of R R) (complOpens hX)).f
          (p + k + 1)).hom w.1, chainMap_mem_cyc R _ w⟩ := by
    rw [← (homologyEquiv R Y (p + k + 1)).symm_apply_apply μ, ← hw]
    exact (LinearEquiv.eq_symm_apply _).1 (homologyMap_homologyEquiv_symm_mk R
      (restrictChainMap R (ModuleCat.of R R) (complOpens hX)) _ w)
  -- the `U` side
  have hL : congrDegree R (TopCat.of (complOpens hX)) (by omega)
      (capProduct R (TopCat.of (complOpens hX)) univ p (p + k + 1 : ℕ) x
        ((restrict R (ModuleCat.of R R) (complOpens hX) (p + k + 1 : ℕ)).hom μ)) =
      (homologyEquiv R (TopCat.of (complOpens hX)) (k + 1)).symm (Submodule.Quotient.mk
        ⟨capChain R p (k + 1) (p + k + 1) (by omega) ψ.1
          (((restrictChainMap R (ModuleCat.of R R) (complOpens hX)).f (p + k + 1)).hom w.1),
          capChain_mem_cyc _ p (k + 1) (p + k + 1) (by omega) ψ ⟨_, chainMap_mem_cyc R _ w⟩⟩) := by
    rw [capProduct_natCast _ _ (by omega), hres, ← hψ, congrDegree_congrDegree_eq]
    exact congrDegree_homologyEquiv_symm_capHomQ _ p (p + k + 1 - p) (k + 1) (p + k + 1) _
      (by omega) _ _ _
  -- the `X` side
  have hR : congrDegree R (TopCat.of X) (by omega)
      (capProductSupport R Y hX hXd (p + 1 : ℕ) (p + k + 1 : ℕ)
        (cohomologyWithSupports.delta R Y X p x) μ) =
      (pushforward R (ModuleCat.of R R) (TopCat.ofHom r) hr k).hom
        ((homologyEquiv R (TopCat.of N) k).symm (Submodule.Quotient.mk
          (capCycNbhd R hX.isOpen_compl hN (compl_union_interior_eq_univ hXN) (p + 1) k
            (p + k + 1) (by omega) ⟨coboundary R p χ, hχc⟩ w))) := by
    rw [capProductSupport_eq_capProductAlong R Y hX hXd hN hXN r hr hrX]
    simp only [capProductAlong, LinearMap.compr₂_apply]
    rw [capProductNbhd_natCast _ _ _ _ _ (by omega), hδ, ← hw, pushforward_congrDegree,
      congrDegree_congrDegree_eq, ← pushforward_congrDegree]
    exact congrArg _ (congrDegree_homologyEquiv_symm_capHomQNbhd (R := R) hX.isOpen_compl hN
      (compl_union_interior_eq_univ hXN) (p + 1) (p + k + 1 - (p + 1))
      k (p + k + 1) _ (by omega) _ _ _)
  rw [hL, hR]
  exact connecting_homologyEquiv_symm_mk_capChain_eq_smul hX hG hGX hG0 h hN hXN hr hGr p k hχv
    w _ (by rw [show cochainPullback R (inclHom (complOpens hX)) p χ = ψ.1 from hχ]) _ rfl

end square

section restriction

variable (R) in
/-- **The cap product of `Y` commutes with restriction to an open subset `U`**:
`(c ∩ a)|_U = c|_U ∩ a|_U`. -/
theorem restrict_capProduct_univ {Y : TopCat.{u}} [T2Space Y] (U : TopologicalSpace.Opens Y)
    (j k : ℤ) (c : cohomologyWithSupports R (ModuleCat.of R R) Y univ j)
    (a : borelMooreHomology R (ModuleCat.of R R) Y k) :
    (restrict R (ModuleCat.of R R) U (k - j)).hom (capProduct R Y univ j k c a) =
      capProduct R (TopCat.of U) univ j k
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (inclHom U) univ j).hom c)
        ((restrict R (ModuleCat.of R R) U k).hom a) := by
  rw [← pushforward_subsetInclusion_capProductNbhd R Y isClosed_univ isClosed_univ
    (by simp) j k c a]
  erw [restrict_pushforward_apply]
  erw [← pushforward_comp_apply R (opensInterMap U univ)
    (borelMooreHomology.subsetInclusion (setInter U univ)) (isProperMap_opensInterMap U univ)
    (isProperMap_subsetInclusion (isClosed_setInter isClosed_univ))
    (isProperMap_restrictPreimage _ U (isProperMap_subsetInclusion isClosed_univ))]
  erw [pushforward_opensInterMap_restrict_capProductNbhd R Y U isClosed_univ isClosed_univ]
  exact pushforward_subsetInclusion_capProductNbhd R (TopCat.of U) _ _ _ j k _ _

end restriction

end borelMooreHomology

end MMP
