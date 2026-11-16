module

public import MMP.AlgebraicTopology.ThomClass.Natural
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
/-!
# Homotopy invariance of the singular cohomology of pairs

Let `f g : Y' → Y` be continuous maps and `H : f ≃ g` a homotopy carrying `A' × [0, 1]` into
`A`, for subsets `A' ⊆ Y'` and `A ⊆ Y`. Then `f` and `g` induce the same map
`H^j(Y, A; R) → H^j(Y', A'; R)` for every `j`.

The singular chain complexes of `Y'` and `Y` carry the chain homotopy `P` between `f_#` and
`g_#` deduced from `H` (Mathlib's `TopCat.Homotopy.singularChainComplexFunctorObjMap`): on a
singular simplex `τ` it is `P τ = - ∑ₖ (-1) ^ k hₖ τ` for the prism simplices `hₖ τ`, and
`f_# = ∂ P + P ∂ + g_#`. A prism simplex of a simplex of `A'` is the image of the corresponding
prism simplex for the restricted homotopy `A' × [0, 1] → A`, so it lies in `A`, and the dual
`P^*` of `P` preserves the cochains vanishing on `A`; then `f^* φ - g^* φ = δ (P^* φ)` for every
relative cocycle `φ`.

## Main definitions

* `MMP.SingularCochain.prismSimplex`: the prism simplices `hₖ τ`.
* `MMP.SingularCochain.homotopyCochain`: the cochain homotopy `P^*`.

## Main results

* `MMP.SingularCochain.cochainPullback_eq_homotopyCochain_succ`: the identity
  `f^* = δ P^* + P^* δ + g^*`.
* `MMP.SingularCochain.relCohomologyMap_eq_of_homotopy`: homotopy invariance on
  cocycles modulo coboundaries.
* `MMP.relativeSingularCohomology.map_eq_of_homotopy`: homotopy invariance of
  `H^j(Y, A; R)`.

## References

* [A. Hatcher, *Algebraic Topology*][hatcher2002], §2.1, Thm. 2.10 and Prop. 2.19.
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal Opposite Simplicial Set
  AlgebraicTopology

universe u

namespace MMP

namespace SingularCochain

open SingularChain

section naturality

variable {X Y X' Y' : TopCat.{u}} {f g : X ⟶ Y} {f' g' : X' ⟶ Y'}
  (H : TopCat.Homotopy f g) (H' : TopCat.Homotopy f' g') (a : X' ⟶ X) (b : Y' ⟶ Y)

/-- The simplicial homotopy deduced from a homotopy is natural in commutative squares. -/
lemma toSSet_homotopy_h_naturality (hab : a ▷ TopCat.I ≫ H.h = H'.h ≫ b) :
    TopCat.toSSet.map a ▷ Δ[1] ≫ H.toSSet.h = H'.toSSet.h ≫ TopCat.toSSet.map b := by
  simp only [TopCat.Homotopy.toSSet]
  rw [← whisker_exchange_assoc, μ_natural_left_assoc, ← Functor.map_comp, hab,
    Functor.map_comp]
  simp

/-- The morphism `Δ[n] ⟶ TopCat.toSSet.obj X` classifying the image of an `n`-simplex under
`TopCat.toSSet.map a` is the composite of the morphism classifying it with
`TopCat.toSSet.map a`. -/
lemma yonedaEquiv_symm_toSSet_map_app {n : ℕ} (x : (TopCat.toSSet.obj X').obj (op ⦋n⦌)) :
    SSet.yonedaEquiv.symm ((TopCat.toSSet.map a).app _ x) =
      SSet.yonedaEquiv.symm x ≫ TopCat.toSSet.map a :=
  SSet.hom_ext (congrFun rfl)

/-- The maps `hₖ` of the simplicial homotopies deduced from homotopies are natural in commutative
squares. -/
lemma toSimplicialObjectHomotopy_h_naturality (hab : a ▷ TopCat.I ≫ H.h = H'.h ≫ b) {n : ℕ}
    (k : Fin (n + 1)) (x : (TopCat.toSSet.obj X').obj (op ⦋n⦌)) :
    H.toSSet.toSimplicialObjectHomotopy.h k ((TopCat.toSSet.map a).app _ x) =
      (TopCat.toSSet.map b).app _ (H'.toSSet.toSimplicialObjectHomotopy.h k x) := by
  have e : SSet.yonedaEquiv.symm ((TopCat.toSSet.map a).app _ x) ▷ Δ[1] ≫ H.toSSet.h =
      (SSet.yonedaEquiv.symm x ▷ Δ[1] ≫ H'.toSSet.h) ≫ TopCat.toSSet.map b := by
    rw [yonedaEquiv_symm_toSSet_map_app, comp_whiskerRight, Category.assoc,
      toSSet_homotopy_h_naturality H H' a b hab, Category.assoc]
  exact congr_arg (fun φ ↦ φ.app _ (SSet.prodStdSimplex.nonDegenerateEquiv₁ k).1) e

end naturality

variable (R : Type u) [CommRing R] {Y' Y : TopCat.{u}} {f g : Y' ⟶ Y}

/-- On the basis vector of a singular `n`-simplex `x`, the chain homotopy deduced from `H` is
`- ∑ₖ (-1) ^ k` times the basis vector of `hₖ x`. -/
lemma ι_homotopy_hom (H : TopCat.Homotopy f g) (n : ℕ) (x : (TopCat.toSSet.obj Y').obj (op ⦋n⦌)) :
    Sigma.ι (fun _ ↦ ModuleCat.of R R) x ≫
        (H.singularChainComplexFunctorObjMap (ModuleCat.of R R)).hom n (n + 1) =
      -∑ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) •
        Sigma.ι (fun _ ↦ ModuleCat.of R R) (H.toSSet.toSimplicialObjectHomotopy.h k x) := by
  dsimp only [TopCat.Homotopy.singularChainComplexFunctorObjMap, SSet.Homotopy.chainComplexMap,
    SimplicialObject.Homotopy.sSetChainComplexMap, SimplicialObject.Homotopy.toChainHomotopy]
  rw [SimplicialObject.Homotopy.ToChainHomotopy.hom_eq]
  simp only [SimplicialObject.Homotopy.whiskerRight_h]
  erw [Preadditive.comp_neg, Preadditive.comp_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  erw [Preadditive.comp_zsmul]
  congr 1
  simp only [sigmaConst]
  erw [Sigma.ι_comp_map', Category.id_comp]

variable {R}

/-- The `k`-th prism simplex `hₖ τ` of a singular `n`-simplex `τ` for a homotopy `H`. -/
def prismSimplex (H : TopCat.Homotopy f g) {n : ℕ} (k : Fin (n + 1)) (τ : Simplex Y' n) :
    Simplex Y (n + 1) :=
  simplexEquiv Y (n + 1) (H.toSSet.toSimplicialObjectHomotopy.h k ((simplexEquiv Y' n).symm τ))

/-- The cochain homotopy `(P^* φ) τ = - ∑ₖ (-1) ^ k φ (hₖ τ)` deduced from a homotopy. -/
def homotopyCochain (H : TopCat.Homotopy f g) (n : ℕ) :
    (Simplex Y (n + 1) → R) →ₗ[R] (Simplex Y' n → R) where
  toFun φ τ := -∑ k : Fin (n + 1), (-1 : R) ^ (k : ℕ) * φ (prismSimplex H k τ)
  map_add' φ ψ := by ext τ; simp [mul_add, Finset.sum_add_distrib, add_comm]
  map_smul' r φ := by ext τ; simp [Finset.mul_sum, mul_left_comm]

/-- The value `(P^* φ) τ = - ∑ₖ (-1) ^ k φ (hₖ τ)` of the cochain homotopy. -/
lemma homotopyCochain_apply (H : TopCat.Homotopy f g) (n : ℕ) (φ : Simplex Y (n + 1) → R)
    (τ : Simplex Y' n) :
    homotopyCochain H n φ τ = -∑ k : Fin (n + 1), (-1 : R) ^ (k : ℕ) * φ (prismSimplex H k τ) :=
  rfl

section evalFun

variable {Z : TopCat.{u}}

/-- The function on singular simplices of a morphism out of the module of singular chains. -/
def evalFun {n : ℕ} (Ψ : (chainCx R Z).X n ⟶ ModuleCat.of R R) : Simplex Z n → R :=
  fun τ ↦ (Sigma.ι (fun _ ↦ ModuleCat.of R R) ((simplexEquiv Z n).symm τ) ≫ Ψ).hom 1

/-- `evalFun` is additive. -/
lemma evalFun_add {n : ℕ} (Ψ₁ Ψ₂ : (chainCx R Z).X n ⟶ ModuleCat.of R R) :
    evalFun (Ψ₁ + Ψ₂) = evalFun Ψ₁ + evalFun Ψ₂ := by
  ext τ
  change (Sigma.ι (fun _ ↦ ModuleCat.of R R) ((simplexEquiv Z n).symm τ) ≫ (Ψ₁ + Ψ₂)).hom 1 = _
  erw [Preadditive.comp_add]
  rfl

/-- Every function on singular `n`-simplices is `evalFun Ψ` for some morphism `Ψ` out of the
module of singular `n`-chains. -/
lemma exists_evalFun_eq {n : ℕ} (φ : Simplex Z n → R) :
    ∃ Ψ : (chainCx R Z).X n ⟶ ModuleCat.of R R, evalFun Ψ = φ :=
  ⟨(cochainEquiv R Z n).symm φ, (cochainEquiv R Z n).apply_symm_apply φ⟩

/-- `evalFun` carries precomposition with the differential to the coboundary. -/
lemma evalFun_d {n : ℕ} (Ψ : (chainCx R Z).X n ⟶ ModuleCat.of R R) :
    evalFun ((chainCx R Z).d (n + 1) n ≫ Ψ) = coboundary R n (evalFun Ψ) := by
  ext τ
  rw [coboundary_apply]
  change (Sigma.ι (fun _ ↦ ModuleCat.of R R) ((simplexEquiv Z (n + 1)).symm τ) ≫
    (chainCx R Z).d (n + 1) n ≫ Ψ).hom 1 = _
  erw [ι_chainCx_d_assoc, Preadditive.sum_comp]
  simp only [ModuleCat.hom_sum, simplexEquiv_symm_δ]
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  erw [Preadditive.zsmul_comp]
  rw [ModuleCat.hom_zsmul, LinearMap.smul_apply, zsmul_eq_mul]
  push_cast
  rfl

/-- `evalFun` carries precomposition with the chain map induced by `h` to the pullback of
cochains along `h`. -/
lemma evalFun_map {Z' : TopCat.{u}} (h : Z' ⟶ Z) {n : ℕ}
    (Ψ : (chainCx R Z).X n ⟶ ModuleCat.of R R) :
    evalFun ((((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).map h).f n ≫
      Ψ) = cochainPullback R h n (evalFun Ψ) := by
  ext τ
  change (Sigma.ι (fun _ ↦ ModuleCat.of R R) ((simplexEquiv Z' n).symm τ) ≫
    (((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).map h).f n ≫
      Ψ).hom 1 = _
  erw [ι_chainCx_map_assoc]
  rfl

/-- `evalFun` carries precomposition with the chain homotopy deduced from `H` to the cochain
homotopy `homotopyCochain H n`. -/
lemma evalFun_homotopy_hom (H : TopCat.Homotopy f g) {n : ℕ}
    (Ψ : (chainCx R Y).X (n + 1) ⟶ ModuleCat.of R R) :
    evalFun ((H.singularChainComplexFunctorObjMap (ModuleCat.of R R)).hom n (n + 1) ≫ Ψ) =
      homotopyCochain H n (evalFun Ψ) := by
  ext τ
  change (Sigma.ι (fun _ ↦ ModuleCat.of R R) ((simplexEquiv Y' n).symm τ) ≫
    (H.singularChainComplexFunctorObjMap (ModuleCat.of R R)).hom n (n + 1) ≫ Ψ).hom 1 = _
  erw [← Category.assoc, ι_homotopy_hom]
  rw [homotopyCochain_apply]
  erw [Preadditive.neg_comp, Preadditive.sum_comp]
  simp only [ModuleCat.hom_neg, ModuleCat.hom_sum, LinearMap.neg_apply]
  rw [LinearMap.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  erw [Preadditive.zsmul_comp]
  rw [ModuleCat.hom_zsmul, LinearMap.smul_apply, zsmul_eq_mul]
  push_cast
  congr 1
  rw [evalFun, prismSimplex, Equiv.symm_apply_apply]
  rfl

end evalFun

/-- The cochain homotopy identity `f^* = P^* δ + g^*` in degree `0`. -/
theorem cochainPullback_eq_homotopyCochain_zero (H : TopCat.Homotopy f g)
    (φ : Simplex Y 0 → R) :
    cochainPullback R f 0 φ = homotopyCochain H 0 (coboundary R 0 φ) + cochainPullback R g 0 φ := by
  obtain ⟨Ψ, rfl⟩ := exists_evalFun_eq φ
  have e := (H.singularChainComplexFunctorObjMap (ModuleCat.of R R)).comm 0
  rw [dNext_eq_zero _ _ (by simp), prevD_eq _ (j' := 1) (by simp), zero_add] at e
  have := congrArg (fun F ↦ evalFun (F ≫ Ψ)) e
  simp only [Preadditive.add_comp, evalFun_add, Category.assoc, evalFun_map] at this
  rw [this, evalFun_homotopy_hom, evalFun_d]

/-- The cochain homotopy identity `f^* = δ P^* + P^* δ + g^*` in positive degrees. -/
theorem cochainPullback_eq_homotopyCochain_succ (H : TopCat.Homotopy f g) (n : ℕ)
    (φ : Simplex Y (n + 1) → R) :
    cochainPullback R f (n + 1) φ = coboundary R n (homotopyCochain H n φ) +
      homotopyCochain H (n + 1) (coboundary R (n + 1) φ) + cochainPullback R g (n + 1) φ := by
  obtain ⟨Ψ, rfl⟩ := exists_evalFun_eq φ
  have e := (H.singularChainComplexFunctorObjMap (ModuleCat.of R R)).comm (n + 1)
  rw [dNext_eq _ (i' := n) (by simp), prevD_eq _ (j' := n + 2) (by simp)] at e
  have := congrArg (fun F ↦ evalFun (F ≫ Ψ)) e
  simp only [Preadditive.add_comp, evalFun_add, Category.assoc, evalFun_map] at this
  rw [this, evalFun_homotopy_hom, evalFun_d, evalFun_homotopy_hom, evalFun_d]

section relative

variable {A' : Set Y'} {A : Set Y}

/-- The restriction `A' × [0, 1] → A` of a homotopy carrying `A' × [0, 1]` into `A`. -/
def restrictHomotopy (H : TopCat.Homotopy f g) (hH : ∀ y ∈ A', ∀ t, H (t, y) ∈ A) :
    TopCat.Homotopy (subspaceRestrict f (A' := A') (A := A) fun y hy ↦ by
        simpa using hH y hy 0)
      (subspaceRestrict g (A' := A') (A := A) fun y hy ↦ by simpa using hH y hy 1) where
  toFun p := ⟨H (p.1, p.2), hH p.2.1 p.2.2 p.1⟩
  continuous_toFun := by fun_prop
  map_zero_left y := Subtype.ext (H.apply_zero y.1)
  map_one_left y := Subtype.ext (H.apply_one y.1)

/-- A prism simplex of a simplex of `A'` lies in `A`. -/
lemma range_prismSimplex_subset (H : TopCat.Homotopy f g) (hH : ∀ y ∈ A', ∀ t, H (t, y) ∈ A)
    {n : ℕ} (k : Fin (n + 1)) {τ : Simplex Y' n} (hτ : range τ ⊆ A') :
    range (prismSimplex H k τ) ⊆ A := by
  have hab : subspaceInclusion Y' A' ▷ TopCat.I ≫ H.h =
      (restrictHomotopy H hH).h ≫ subspaceInclusion Y A := by
    ext p
    rfl
  have key : H.toSSet.toSimplicialObjectHomotopy.h k ((simplexEquiv Y' n).symm τ) = _ :=
    toSimplicialObjectHomotopy_h_naturality H (restrictHomotopy H hH)
      (subspaceInclusion Y' A') (subspaceInclusion Y A) hab k
      ((simplexEquiv (TopCat.of A') n).symm ⟨fun t ↦ ⟨τ t, hτ ⟨t, rfl⟩⟩, τ.continuous.subtype_mk _⟩)
  rw [prismSimplex, key]
  rintro _ ⟨t, rfl⟩
  exact Subtype.prop _

/-- For a homotopy carrying `A' × [0, 1]` into `A`, the cochain homotopy carries cochains
vanishing on `A` to cochains vanishing on `A'`. -/
lemma homotopyCochain_mem_vanishing (H : TopCat.Homotopy f g)
    (hH : ∀ y ∈ A', ∀ t, H (t, y) ∈ A) {n : ℕ} {φ : Simplex Y (n + 1) → R}
    (hφ : φ ∈ vanishing R (n + 1) A) : homotopyCochain H n φ ∈ vanishing R n A' := fun τ hτ ↦ by
  rw [homotopyCochain_apply]
  simp [hφ _ (range_prismSimplex_subset H hH _ hτ)]

/-- Homotopy invariance on cocycles modulo coboundaries: maps of pairs homotopic through a
homotopy carrying `A' × [0, 1]` into `A` induce the same map `H^n(Y, A) → H^n(Y', A')`. -/
theorem relCohomologyMap_eq_of_homotopy (H : TopCat.Homotopy f g)
    (hH : ∀ y ∈ A', ∀ t, H (t, y) ∈ A) (hf : A' ⊆ f ⁻¹' A) (hg : A' ⊆ g ⁻¹' A) (n : ℕ) :
    relCohomologyMap R f hf n = relCohomologyMap R g hg n := by
  ext φ
  change relCohomologyMap R f hf n (Submodule.Quotient.mk φ) =
    relCohomologyMap R g hg n (Submodule.Quotient.mk φ)
  rw [relCohomologyMap_mk, relCohomologyMap_mk, Submodule.Quotient.eq]
  have hφ := φ.2
  rw [mem_relCocycles_iff] at hφ
  change cochainPullback R f n φ.1 - cochainPullback R g n φ.1 ∈ relCoboundaries R A' n
  cases n with
  | zero =>
    rw [cochainPullback_eq_homotopyCochain_zero H, hφ.2, map_zero, zero_add, sub_self]
    exact Submodule.zero_mem _
  | succ n =>
    rw [cochainPullback_eq_homotopyCochain_succ H, hφ.2, map_zero, add_zero, add_sub_cancel_right]
    exact ⟨_, homotopyCochain_mem_vanishing H hH hφ.1, rfl⟩

end relative

end SingularCochain

namespace relativeSingularCohomology

open SingularCochain

variable (R : Type u) [CommRing R] {Y' Y : TopCat.{u}} {f g : Y' ⟶ Y} {A' : Set Y'} {A : Set Y}

/-- Homotopy invariance of the singular cohomology of pairs: continuous maps `f g : Y' → Y`
joined by a homotopy carrying `A' × [0, 1]` into `A` induce the same map
`H^j(Y, A; R) → H^j(Y', A'; R)`. -/
theorem map_eq_of_homotopy (H : TopCat.Homotopy f g) (hH : ∀ y ∈ A', ∀ t, H (t, y) ∈ A)
    (hf : A' ⊆ f ⁻¹' A) (hg : A' ⊆ g ⁻¹' A) (j : ℤ) :
    map R (ModuleCat.of R R) f hf j = map R (ModuleCat.of R R) g hg j := by
  rcases le_or_gt 0 j with h | h
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = n := ⟨j.toNat, (Int.toNat_of_nonneg h).symm⟩
    ext x
    apply (relativeSingularCohomologyEquiv R A' n).injective
    rw [relativeSingularCohomologyEquiv_map, relativeSingularCohomologyEquiv_map,
      relCohomologyMap_eq_of_homotopy H hH hf hg]
  · exact (((relativeSingularCochainComplex R (ModuleCat.of R R) Y A).extend_exactAt
      ComplexShape.embeddingUpNat j (fun n hn ↦ by simp at hn; lia)).isZero_homology).eq_of_src _ _

end relativeSingularCohomology

end MMP
