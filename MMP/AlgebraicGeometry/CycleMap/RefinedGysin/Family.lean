module

public import MMP.AlgebraicTopology.RefinedGysin.CapSwap
public import MMP.AlgebraicTopology.OrientationClass.CapProductPointClass
/-!
# Cap products along a family over a curve (Fulton, proof of Theorem 19.2)

Let `ρ : Y → T` be a map of spaces and `A ⊆ Y` a closed subset with a homeomorphism
`φ : X × T ≃ A` over `T` (`ρ (φ (x, s)) = s`). For `w ∈ H^i(Y, Y - A)` with `i` even, a class
`p_t ∈ H^n(T, T - t)` and `a ∈ H_k Y`, write `Y_t = ρ⁻¹ t`. Then the class
`w|_{Y_t} ∩ (ρ^* p_t ∩ a) ∈ H_{k-n-i}(A ∩ Y_t)`, read in `H_*(X)` through `A ∩ Y_t ≅ X × {t} ≅ X`,
is `pr^* p_t ∩ b ∈ H_{k-i-n}(X × {t}) = H_*(X)` for `b = φ^{-1}_*(w ∩ a) ∈ H_{k-i}(X × T)`
(`pushforward_interFibre_capProductSupportPullback_eq`). When `T` is a connected oriented
manifold and `p_t` is the local orientation class at `t`, the latter does not depend on `t`
(`pushforward_fibreProj_capProductSupportPullback_eq_of_isLocalOrientationClass`, Fulton's
Lemma 19.2(c)), hence neither does the former
(`pushforward_interFibre_capProductSupportPullback_eq_of_isLocalOrientationClass`).

In the proof of Fulton's Theorem 19.2 this is the chain
`g^*u_f ∩ cl(V) = (G^*u_F)|_V ∩ (ρ'^*u_0 ∩ a) = u_{i'_0} ∩ b = u_{i'_∞} ∩ b
  = (G^*u_F)|_{C'} ∩ (ρ'^*u_∞ ∩ a) = ĝ^*u_s ∩ cl(C')`
for `Y = M'(ℂ)`, `T = ℙ¹(ℂ)`, `A = (X' × ℙ¹)(ℂ)`, `w = G^*u_F` and `a = cl(M')`, once
`cl(V) = ρ'^*u_0 ∩ a` and `cl(C') = ρ'^*u_∞ ∩ a` (Fulton's Lemma 19.2(e)).

## Main definitions

* `interFibreHomeomorph`: the homeomorphism `A ∩ ρ⁻¹ t ≃ X`.
* `interFibreProj`: the homeomorphism `A ∩ ρ⁻¹ t ≃ X` as a morphism of `TopCat`.
* `fibreProjOf`: the projection `F⁻¹ t → X` for a map `F : X × T → T`.

## Main results

* `pushforward_interFibre_capProductSupportPullback_eq`: `w|_{Y_t} ∩ (ρ^* p_t ∩ a)`, read in
  `H_*(X)`, is `pr^* p_t ∩ φ^{-1}_*(w ∩ a)`.
* `pushforward_interFibre_capProductSupportPullback_eq_of_isLocalOrientationClass`: for local
  orientation classes `p_t` of a connected oriented manifold `T`, the class
  `w|_{Y_t} ∩ (ρ^* p_t ∩ a)` in `H_*(X)` does not depend on `t`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.2, proof of Theorem 19.2.
-/

@[expose] public noncomputable section

open CategoryTheory Set Topology

universe u

namespace MMP

namespace borelMooreHomology

open BorelMooreCross

variable {X T Y : TopCat.{u}} {ρ : Y ⟶ T} {A : Set Y} (φ : (X × T) ≃ₜ A)

/-- The identification `A ∩ ρ⁻¹ t ≅ X × {t} ≅ X` for a homeomorphism `φ : X × T ≃ A` over `T`. -/
def interFibreHomeomorph (hφ : ∀ p, ρ (φ p : Y) = p.2) (t : T) :
    (A ∩ ρ ⁻¹' {t} : Set Y) ≃ₜ X where
  toFun z := (φ.symm ⟨z.1, z.2.1⟩).1
  invFun x := ⟨φ (x, t), (φ (x, t)).2, by simp [hφ]⟩
  left_inv z := by
    apply Subtype.ext
    have h2 : (φ.symm ⟨z.1, z.2.1⟩).2 = t := by
      rw [← hφ, φ.apply_symm_apply]
      exact z.2.2
    have : ((φ.symm ⟨z.1, z.2.1⟩).1, t) = φ.symm ⟨z.1, z.2.1⟩ := Prod.ext rfl h2.symm
    simp only
    rw [this, φ.apply_symm_apply]
  right_inv x := by simp
  continuous_toFun := continuous_fst.comp (φ.symm.continuous.comp
    (continuous_subtype_val.subtype_mk _))
  continuous_invFun := ((continuous_subtype_val.comp (φ.continuous.comp
    (continuous_id.prodMk continuous_const))).subtype_mk _)

/-- `A ∩ ρ⁻¹ t → X`, as a morphism of `TopCat`. -/
def interFibreProj (hφ : ∀ p, ρ (φ p : Y) = p.2) (t : T) :
    TopCat.of (A ∩ ρ ⁻¹' {t} : Set Y) ⟶ X :=
  TopCat.ofHom ⟨interFibreHomeomorph φ hφ t, (interFibreHomeomorph φ hφ t).continuous⟩

/-- The map `A ∩ ρ⁻¹ t → X` of `interFibreProj` is proper. -/
lemma isProperMap_interFibreProj (hφ : ∀ p, ρ (φ p : Y) = p.2) (t : T) :
    IsProperMap (interFibreProj φ hφ t) :=
  show IsProperMap (interFibreHomeomorph φ hφ t) from (interFibreHomeomorph φ hφ t).isProperMap

/-- `φ : X × T → A`, as a morphism of `TopCat`. -/
def homeomorphHom : TopCat.of (X × T) ⟶ TopCat.of A :=
  TopCat.ofHom ⟨φ, φ.continuous⟩

/-- `φ⁻¹ : A → X × T`, as a morphism of `TopCat`. -/
def homeomorphInvHom : TopCat.of A ⟶ TopCat.of (X × T) :=
  TopCat.ofHom ⟨φ.symm, φ.symm.continuous⟩

/-- The map `φ : X × T → A` is proper. -/
lemma isProperMap_homeomorphHom : IsProperMap (homeomorphHom φ) :=
  show IsProperMap φ from φ.isProperMap

/-- The map `φ⁻¹ : A → X × T` is proper. -/
lemma isProperMap_homeomorphInvHom : IsProperMap (homeomorphInvHom φ) :=
  show IsProperMap φ.symm from φ.symm.isProperMap

variable (R : Type u) [CommRing R]

/-- The projection `F⁻¹ t → X` for a map `F : X × T → T`. -/
def fibreProjOf (F : TopCat.of (X × T) ⟶ T) (t : T) : TopCat.of (F ⁻¹' {t}) ⟶ X :=
  TopCat.ofHom ⟨fun p ↦ p.1.1, continuous_fst.comp continuous_subtype_val⟩

/-- Changing `F` to the projection `pr : X × T → T` in `p_t ∩ b` over `F⁻¹ t`. -/
lemma pushforward_fibreProjOf_capProductSupport_eq [T1Space T] (F : TopCat.of (X × T) ⟶ T)
    (hF : F = prodSnd X T) (t : T) (hFp : IsProperMap (fibreProjOf F t))
    (hdF : HasProperNeighbourhoodDeformations (F ⁻¹' {t}))
    (hd : HasProperNeighbourhoodDeformations (prodSnd X T ⁻¹' {t})) (n l : ℤ)
    (p : cohomologyWithSupports R (ModuleCat.of R R) T {t} n)
    (b : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (X × T)) l) :
    (pushforward R (ModuleCat.of R R) (fibreProjOf F t) hFp (l - n)).hom
        (capProductSupport R _ (isClosed_singleton.preimage F.hom.continuous) hdF n l
          ((cohomologyWithSupports.pullback R (ModuleCat.of R R) F {t} n).hom p) b) =
      (pushforward R (ModuleCat.of R R) (fibreProj X t) (isProperMap_fibreProj X t) (l - n)).hom
        (capProductSupportPullback R (prodSnd X T) isClosed_singleton hd n l p b) := by
  subst hF
  rfl

/-- `φ⁻¹(A ∩ ρ⁻¹ t) = pr⁻¹ t`. -/
lemma homeomorphHom_preimage_eq (hφ : ∀ p, ρ (φ p : Y) = p.2) (t : T) :
    homeomorphHom φ ⁻¹' (subsetInclusion A ⁻¹' (ρ ⁻¹' {t})) = prodSnd X T ⁻¹' {t} := by
  ext q
  exact iff_of_eq (congrArg (· = t) (hφ q))

/-- `ρ ∘ φ = pr`. -/
lemma homeomorphHom_comp_eq (hφ : ∀ p, ρ (φ p : Y) = p.2) :
    homeomorphHom φ ≫ subsetInclusion A ≫ ρ = prodSnd X T :=
  ConcreteCategory.hom_ext _ _ hφ

/-- **Cap products along a family** (Fulton, proof of Theorem 19.2). Let `ρ : Y → T`, `A ⊆ Y`
closed with a homeomorphism `φ : X × T ≃ A` over `T`, `w ∈ H^i(Y, Y - A)` with `i` even,
`p ∈ H^n(T, T - t)` and `a ∈ H_k Y`. Then `w|_{ρ⁻¹ t} ∩ (ρ^* p ∩ a)`, carried to `X` along
`A ∩ ρ⁻¹ t ≅ X`, is `pr^* p ∩ φ^{-1}_*(w ∩ a)` carried to `X` along `X × {t} ≅ X`. -/
theorem pushforward_interFibre_capProductSupportPullback_eq [T1Space T]
    (hφ : ∀ p, ρ (φ p : Y) = p.2) (hA : IsClosed A) (hAd : HasProperNeighbourhoodDeformations A)
    (t : T) (hZd : HasProperNeighbourhoodDeformations (ρ ⁻¹' {t}))
    (hAZd : HasProperNeighbourhoodDeformations (A ∩ ρ ⁻¹' {t}))
    (hd₁ : HasProperNeighbourhoodDeformations (subsetInclusion (ρ ⁻¹' {t}) ⁻¹' A))
    (hd₂ : HasProperNeighbourhoodDeformations (subsetInclusion A ⁻¹' (ρ ⁻¹' {t})))
    (hd₃ : HasProperNeighbourhoodDeformations (prodSnd X T ⁻¹' {t}))
    {i : ℤ} (hi : Even i) (n k : ℤ)
    (w : cohomologyWithSupports R (ModuleCat.of R R) Y A i)
    (p : cohomologyWithSupports R (ModuleCat.of R R) T {t} n)
    (a : borelMooreHomology R (ModuleCat.of R R) Y k) :
    (pushforward R (ModuleCat.of R R)
        ((preimageInterHom (ρ ⁻¹' {t}) A ≫ subsetInclusionOfSubset (inter_comm _ A).le) ≫
          interFibreProj φ hφ t)
        ((isProperMap_interFibreProj φ hφ t).comp
          ((isProperMap_subsetInclusionOfSubset
            ((isClosed_singleton.preimage ρ.hom.continuous).inter hA) (inter_comm _ A).le).comp
            (isProperMap_preimageInterHom (isClosed_singleton.preimage ρ.hom.continuous) hA)))
        (k - n - i)).hom
      (capProductSupportPullback R (subsetInclusion (ρ ⁻¹' {t})) hA hd₁ i (k - n) w
        (capProductSupportPullback R ρ isClosed_singleton hZd n k p a)) =
      congrDegree R X (by ring)
        ((pushforward R (ModuleCat.of R R) (fibreProj X t) (isProperMap_fibreProj X t)
            (k - i - n)).hom
          (capProductSupportPullback R (prodSnd X T) isClosed_singleton hd₃ n (k - i) p
            ((pushforward R (ModuleCat.of R R) (homeomorphInvHom φ) (isProperMap_homeomorphInvHom φ)
              (k - i)).hom (capProductSupport R Y hA hAd i k w a)))) := by
  have hZ : IsClosed (ρ ⁻¹' {t}) := isClosed_singleton.preimage ρ.hom.continuous
  have hp₁ : IsProperMap (preimageInterHom (ρ ⁻¹' {t}) A ≫
      subsetInclusionOfSubset (inter_comm (ρ ⁻¹' {t}) A).le) :=
    (isProperMap_subsetInclusionOfSubset (hZ.inter hA) (inter_comm _ A).le).comp
      (isProperMap_preimageInterHom hZ hA)
  rw [pushforward_comp_apply' R (preimageInterHom (ρ ⁻¹' {t}) A ≫
      subsetInclusionOfSubset (inter_comm (ρ ⁻¹' {t}) A).le) (interFibreProj φ hφ t) hp₁
      (isProperMap_interFibreProj φ hφ t),
    capProductSupportPullback_apply R ρ isClosed_singleton hZd n k p a,
    pushforward_capProductSupportPullback_swap_of_even R Y hA hZ hAd hZd hAZd hd₁ hd₂ hi n k w
      ((cohomologyWithSupports.pullback R (ModuleCat.of R R) ρ {t} n).hom p) a,
    pushforward_congrDegree_comm]
  have hS : IsClosed (subsetInclusion A ⁻¹' (ρ ⁻¹' {t})) :=
    hZ.preimage (subsetInclusion A).hom.continuous
  have hdS : HasProperNeighbourhoodDeformations
      (homeomorphHom φ ⁻¹' (subsetInclusion A ⁻¹' (ρ ⁻¹' {t}))) := by
    rw [homeomorphHom_preimage_eq φ hφ t]
    exact hd₃
  set b := capProductSupport R Y hA hAd i k w a
  have hb : b = (pushforward R (ModuleCat.of R R) (homeomorphHom φ) (isProperMap_homeomorphHom φ)
      (k - i)).hom ((pushforward R (ModuleCat.of R R) (homeomorphInvHom φ)
        (isProperMap_homeomorphInvHom φ) (k - i)).hom b) :=
    (pushforward_symm_pushforward_homeomorph R _ φ.symm (k - i) b).symm
  set b' := (pushforward R (ModuleCat.of R R) (homeomorphInvHom φ)
    (isProperMap_homeomorphInvHom φ) (k - i)).hom b
  rw [← pushforward_comp_apply' R (preimageInterHom A (ρ ⁻¹' {t})) (interFibreProj φ hφ t)
      (isProperMap_preimageInterHom hA hZ) (isProperMap_interFibreProj φ hφ t),
    capProductSupportPullback_apply R (subsetInclusion A) hZ hd₂ n (k - i), hb,
    ← pushforward_restrictPreimage_capProductSupportPullback R (homeomorphHom φ)
      (isProperMap_homeomorphHom φ) hS hd₂ hdS n (k - i),
    ← pushforward_comp_apply' R
      (TopCat.ofHom ((homeomorphHom φ).hom.restrictPreimage (subsetInclusion A ⁻¹' (ρ ⁻¹' {t}))))
      (preimageInterHom A (ρ ⁻¹' {t}) ≫ interFibreProj φ hφ t)
      ((isProperMap_homeomorphHom φ).restrictPreimage _)
      ((isProperMap_interFibreProj φ hφ t).comp (isProperMap_preimageInterHom hA hZ))]
  have hcomp : TopCat.ofHom ((homeomorphHom φ).hom.restrictPreimage
        (subsetInclusion A ⁻¹' (ρ ⁻¹' {t}))) ≫
        (preimageInterHom A (ρ ⁻¹' {t}) ≫ interFibreProj φ hφ t) =
      fibreProjOf (homeomorphHom φ ≫ subsetInclusion A ≫ ρ) t :=
    ConcreteCategory.hom_ext _ _ fun q ↦ congrArg Prod.fst (φ.symm_apply_apply q.1)
  have hFp : IsProperMap (fibreProjOf (homeomorphHom φ ≫ subsetInclusion A ≫ ρ) t) := by
    rw [← hcomp]
    exact ((isProperMap_interFibreProj φ hφ t).comp (isProperMap_preimageInterHom hA hZ)).comp
      ((isProperMap_homeomorphHom φ).restrictPreimage _)
  have hc : (cohomologyWithSupports.pullback R (ModuleCat.of R R) (homeomorphHom φ)
        (subsetInclusion A ⁻¹' (ρ ⁻¹' {t})) n).hom
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (subsetInclusion A)
          (ρ ⁻¹' {t}) n).hom
          ((cohomologyWithSupports.pullback R (ModuleCat.of R R) ρ {t} n).hom p)) =
      (cohomologyWithSupports.pullback R (ModuleCat.of R R)
        (homeomorphHom φ ≫ subsetInclusion A ≫ ρ) {t} n).hom p := by
    rw [cohomologyWithSupports.pullback_comp, cohomologyWithSupports.pullback_comp]
    rfl
  rw [pushforward_congr_eq R hcomp _ hFp, capProductSupportPullback_apply, hc,
    pushforward_fibreProjOf_capProductSupport_eq R _ (homeomorphHom_comp_eq φ hφ) t hFp hdS hd₃]

section orientation

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  [ChartedSpace H T]

/-- **Cap products along a family over a manifold** (Fulton, proof of Theorem 19.2). Let
`ρ : Y → T` with `T` a connected Hausdorff space with an oriented atlas, `A ⊆ Y` closed with a
homeomorphism `φ : X × T ≃ A` over `T`, `w ∈ H^i(Y, Y - A)` with `i` even and `a ∈ H_k Y`. For
the local orientation classes `u_t`, `u_{t'}` of `T` at `t`, `t'`, the classes
`w|_{ρ⁻¹ t} ∩ (ρ^* u_t ∩ a)` and `w|_{ρ⁻¹ t'} ∩ (ρ^* u_{t'} ∩ a)`, carried to `X` along
`A ∩ ρ⁻¹ t ≅ X` and `A ∩ ρ⁻¹ t' ≅ X`, agree. In Fulton's proof:
`(G^*u_F)|_V ∩ (ρ'^*u_0 ∩ a) = (G^*u_F)|_{C'} ∩ (ρ'^*u_∞ ∩ a)` in `H_*(X')`. -/
theorem pushforward_interFibre_capProductSupportPullback_eq_of_isLocalOrientationClass
    [T2Space T] [ConnectedSpace T] (hT : IsOrientedAtlas H T) {n : ℕ} (hn : 0 < n)
    (β : Module.Basis (Fin n) ℝ H) (hφ : ∀ p, ρ (φ p : Y) = p.2) (hA : IsClosed A)
    (hAd : HasProperNeighbourhoodDeformations A)
    (hZd : ∀ s : T, HasProperNeighbourhoodDeformations (ρ ⁻¹' {s}))
    (hAZd : ∀ s : T, HasProperNeighbourhoodDeformations (A ∩ ρ ⁻¹' {s}))
    (hd₁ : ∀ s : T, HasProperNeighbourhoodDeformations (subsetInclusion (ρ ⁻¹' {s}) ⁻¹' A))
    (hd₂ : ∀ s : T, HasProperNeighbourhoodDeformations (subsetInclusion A ⁻¹' (ρ ⁻¹' {s})))
    (hd₃ : ∀ s : T, HasProperNeighbourhoodDeformations (prodSnd X T ⁻¹' {s}))
    {i : ℤ} (hi : Even i) (k : ℤ)
    (w : cohomologyWithSupports R (ModuleCat.of R R) Y A i)
    (a : borelMooreHomology R (ModuleCat.of R R) Y k) {t t' : T}
    {u : cohomologyWithSupports R (ModuleCat.of R R) T {t} n}
    {u' : cohomologyWithSupports R (ModuleCat.of R R) T {t'} n}
    (hu : IsLocalOrientationClass R β t u) (hu' : IsLocalOrientationClass R β t' u') :
    (pushforward R (ModuleCat.of R R)
        ((preimageInterHom (ρ ⁻¹' {t}) A ≫ subsetInclusionOfSubset (inter_comm _ A).le) ≫
          interFibreProj φ hφ t)
        ((isProperMap_interFibreProj φ hφ t).comp
          ((isProperMap_subsetInclusionOfSubset
            ((isClosed_singleton.preimage ρ.hom.continuous).inter hA) (inter_comm _ A).le).comp
            (isProperMap_preimageInterHom (isClosed_singleton.preimage ρ.hom.continuous) hA)))
        (k - n - i)).hom
      (capProductSupportPullback R (subsetInclusion (ρ ⁻¹' {t})) hA (hd₁ t) i (k - n) w
        (capProductSupportPullback R ρ isClosed_singleton (hZd t) n k u a)) =
    (pushforward R (ModuleCat.of R R)
        ((preimageInterHom (ρ ⁻¹' {t'}) A ≫ subsetInclusionOfSubset (inter_comm _ A).le) ≫
          interFibreProj φ hφ t')
        ((isProperMap_interFibreProj φ hφ t').comp
          ((isProperMap_subsetInclusionOfSubset
            ((isClosed_singleton.preimage ρ.hom.continuous).inter hA) (inter_comm _ A).le).comp
            (isProperMap_preimageInterHom (isClosed_singleton.preimage ρ.hom.continuous) hA)))
        (k - n - i)).hom
      (capProductSupportPullback R (subsetInclusion (ρ ⁻¹' {t'})) hA (hd₁ t') i (k - n) w
        (capProductSupportPullback R ρ isClosed_singleton (hZd t') n k u' a)) := by
  rw [pushforward_interFibre_capProductSupportPullback_eq φ R hφ hA hAd t (hZd t) (hAZd t)
      (hd₁ t) (hd₂ t) (hd₃ t) hi n k w u a,
    pushforward_interFibre_capProductSupportPullback_eq φ R hφ hA hAd t' (hZd t') (hAZd t')
      (hd₁ t') (hd₂ t') (hd₃ t') hi n k w u' a,
    pushforward_fibreProj_capProductSupportPullback_eq_of_isLocalOrientationClass R hT hn β hd₃
      (k - i) _ hu hu']

end orientation

end borelMooreHomology

end MMP
