module

public import MMP.AlgebraicTopology.BorelMoore.Suspension
public import MMP.AlgebraicTopology.PoincareDuality.Alexander
public import MMP.AlgebraicTopology.OrientationClass.CapDeformation

/-!
# The duality map of an imbedded space

For a closed `A ⊆ M`, a homeomorphism `ψ : X ≅ A` and `μ ∈ H_n M`, the *imbedded duality map*
`c ↦ ψ⁻¹_*(c ∩ μ)`, `H^j(M, M - A) → H_k X` (`j + k = n`), is compatible with

* equal supports (`embeddedDualityMap_forget`),
* homeomorphisms of the ambient space (`embeddedDualityMap_pullback_symm`),
* the euclidean suspension `H^j(ℝ^m, ℝ^m - A) → H^{j+1}(ℝ^{m+1}, ℝ^{m+1} - A × 0)`
  (`embeddedDualityMap_euclideanSuspension`).

Local contractibility is invariant under homeomorphisms and holds in real normed spaces and
one-point spaces, and closed locally contractible subsets of finite-dimensional real normed spaces
have proper neighbourhood deformations.

## Main definitions

* `MMP.borelMooreHomology.embeddedDualityMap`: The imbedded duality map `c ↦ ψ⁻¹_*(c ∩ μ)`.

## Main results

* `MMP.borelMooreHomology.embeddedDualityMap_forget`: Compatibility with equal supports.
* `MMP.borelMooreHomology.embeddedDualityMap_pullback_symm`: Compatibility with homeomorphisms
  of the ambient space.
* `MMP.borelMooreHomology.embeddedDualityMap_euclideanSuspension`: Compatibility with the
  euclidean suspension.
-/

@[expose] public noncomputable section

open CategoryTheory Set Topology MMP.BorelMooreCross MMP.BorelMooreCap

universe u

namespace MMP

section contractible

/-- Local contractibility (a basis of open contractible neighbourhoods) is invariant under
homeomorphisms. -/
theorem hasBasis_contractible_of_homeomorph {Y Z : Type*} [TopologicalSpace Y]
    [TopologicalSpace Z] (φ : Y ≃ₜ Z)
    (hY : ∀ y : Y, (𝓝 y).HasBasis (fun V : Set Y ↦ IsOpen V ∧ y ∈ V ∧ ContractibleSpace V) id)
    (z : Z) : (𝓝 z).HasBasis (fun V : Set Z ↦ IsOpen V ∧ z ∈ V ∧ ContractibleSpace V) id := by
  have h := (hY (φ.symm z)).map φ
  rw [Homeomorph.map_nhds_eq, φ.apply_symm_apply] at h
  refine h.to_hasBasis (fun V ⟨hV, hzV, hVc⟩ ↦ ⟨φ '' V, ⟨φ.isOpenMap V hV, ⟨_, hzV, by simp⟩,
    ?_⟩, subset_rfl⟩) (fun W ⟨hW, hzW, hWc⟩ ↦ ⟨φ ⁻¹' W, ⟨hW.preimage φ.continuous,
      by simpa using hzW, ?_⟩, by simp [image_preimage_eq _ φ.surjective]⟩)
  · exact (φ.image V).symm.contractibleSpace
  · exact (preimageHomeomorph φ W).contractibleSpace

/-- A real normed space is locally contractible: every point has a basis of open contractible
neighbourhoods. -/
theorem hasBasis_contractible_normedSpace {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (x : V) : (𝓝 x).HasBasis (fun W : Set V ↦ IsOpen W ∧ x ∈ W ∧ ContractibleSpace W) id :=
  Metric.nhds_basis_ball.to_hasBasis
    (fun r hr ↦ ⟨Metric.ball x r, ⟨Metric.isOpen_ball, Metric.mem_ball_self hr,
      (convex_ball x r).contractibleSpace ⟨x, Metric.mem_ball_self hr⟩⟩, subset_rfl⟩)
    (fun _ ⟨hW, hxW, _⟩ ↦ Metric.isOpen_iff.1 hW x hxW)

/-- A one-point space is locally contractible. -/
theorem hasBasis_contractible_of_subsingleton {Y : Type*} [TopologicalSpace Y] [Subsingleton Y]
    (y : Y) : (𝓝 y).HasBasis (fun V : Set Y ↦ IsOpen V ∧ y ∈ V ∧ ContractibleSpace V) id := by
  have : Unique Y := uniqueOfSubsingleton y
  refine ⟨fun s ↦ ⟨fun hs ↦ ⟨univ, ⟨isOpen_univ, mem_univ _, ?_⟩, fun z _ ↦ ?_⟩,
    fun ⟨V, ⟨hV, hyV, _⟩, hVs⟩ ↦ Filter.mem_of_superset (hV.mem_nhds hyV) hVs⟩⟩
  · exact (Homeomorph.Set.univ Y).contractibleSpace
  · rw [Subsingleton.elim z y]; exact mem_of_mem_nhds hs

/-- **Proper neighbourhood deformations in a finite-dimensional real normed space**: every closed,
locally contractible subset has them. -/
theorem hasProperNeighbourhoodDeformations_of_finiteDimensional {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {X : Set V} (hX : IsClosed X)
    (hXc : ∀ x : X, (𝓝 x).HasBasis (fun W : Set X ↦ IsOpen W ∧ x ∈ W ∧ ContractibleSpace W) id) :
    HasProperNeighbourhoodDeformations X := by
  let b := Module.finBasis ℝ V
  let e : V ≃ₜ EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) :=
    (b.equivFun.trans (EuclideanSpace.equiv (Fin _) ℝ).symm.toLinearEquiv).toContinuousLinearEquiv
      |>.toHomeomorph
  let : ChartedSpace (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) V :=
    e.toOpenPartialHomeomorph.singletonChartedSpace e.toOpenPartialHomeomorph_source
  exact hasProperNeighbourhoodDeformations_of_chartedSpace (n := Module.finrank ℝ V) hX hXc

end contractible

namespace borelMooreHomology

variable (R : Type u) [CommRing R]

/-- The *imbedded duality map* `c ↦ ψ⁻¹_*(c ∩ μ)`, `H^j(M, M - A) → H_k X` for `j + k = n`, of a
closed `A ⊆ M` with a homeomorphism `ψ : X ≅ A` and `μ ∈ H_n M`. -/
def embeddedDualityMap {M : TopCat.{u}} {A : Set M} (hA : IsClosed A)
    (hAd : HasProperNeighbourhoodDeformations A) {X : TopCat.{u}} (ψ : X ≃ₜ A) {n : ℕ}
    (μ : borelMooreHomology R (ModuleCat.of R R) M n) (j k : ℤ) (h : j + k = n) :
    cohomologyWithSupports R (ModuleCat.of R R) M A j →ₗ[R]
      borelMooreHomology R (ModuleCat.of R R) X k :=
  (pushforward R (ModuleCat.of R R) (TopCat.ofHom (ψ.symm : C(A, X))) ψ.symm.isProperMap k).hom ∘ₗ
    (congrDegree R (TopCat.of A) (by omega : (n : ℤ) - j = k)).toLinearMap ∘ₗ
    (capProductSupport R M hA hAd j n).flip μ

/-- The imbedded duality map sends `c` to `ψ⁻¹_*` of the cap product `c ∩ μ`, reindexed to
degree `k`. -/
lemma embeddedDualityMap_apply {M : TopCat.{u}} {A : Set M} (hA : IsClosed A)
    (hAd : HasProperNeighbourhoodDeformations A) {X : TopCat.{u}} (ψ : X ≃ₜ A) {n : ℕ}
    (μ : borelMooreHomology R (ModuleCat.of R R) M n) (j k : ℤ) (h : j + k = n)
    (c : cohomologyWithSupports R (ModuleCat.of R R) M A j) :
    embeddedDualityMap R hA hAd ψ μ j k h c =
      (pushforward R (ModuleCat.of R R) (TopCat.ofHom (ψ.symm : C(A, X))) ψ.symm.isProperMap k).hom
        (congrDegree R (TopCat.of A) (by omega) (capProductSupport R M hA hAd j n c μ)) :=
  rfl

/-- The imbedded duality map in degree `n - k` is `ψ⁻¹_*` of the duality map. -/
lemma embeddedDualityMap_eq_dualityMap {M : TopCat.{u}} {A : Set M} (hA : IsClosed A)
    (hAd : HasProperNeighbourhoodDeformations A) {X : TopCat.{u}} (ψ : X ≃ₜ A) {n : ℕ}
    (μ : borelMooreHomology R (ModuleCat.of R R) M n) (k : ℤ)
    (c : cohomologyWithSupports R (ModuleCat.of R R) M A (n - k)) :
    embeddedDualityMap R hA hAd ψ μ (n - k) k (sub_add_cancel _ _) c =
      (pushforward R (ModuleCat.of R R) (TopCat.ofHom (ψ.symm : C(A, X))) ψ.symm.isProperMap k).hom
        (dualityMap R hA hAd μ k c) :=
  rfl

/-- **Equal supports.** For `A = B` and homeomorphisms `ψ : X ≅ A`, `ψ' : X ≅ B` with the same
values, the imbedded duality maps agree through the identification
`H^j(M, M - A) = H^j(M, M - B)`. -/
theorem embeddedDualityMap_forget {M : TopCat.{u}} {A B : Set M} (hAB : A = B) (hA : IsClosed A)
    (hAd : HasProperNeighbourhoodDeformations A) (hB : IsClosed B)
    (hBd : HasProperNeighbourhoodDeformations B) {X : TopCat.{u}} (ψ : X ≃ₜ A) (ψ' : X ≃ₜ B)
    (hψ : ∀ x, (ψ' x : M) = ψ x) {n : ℕ} (μ : borelMooreHomology R (ModuleCat.of R R) M n)
    (j k : ℤ) (h : j + k = n) (c : cohomologyWithSupports R (ModuleCat.of R R) M A j) :
    embeddedDualityMap R hB hBd ψ' μ j k h
        ((cohomologyWithSupports.forget R (ModuleCat.of R R) M hAB.le j).hom c) =
      embeddedDualityMap R hA hAd ψ μ j k h c := by
  subst hAB
  obtain rfl : ψ' = ψ := Homeomorph.ext fun x ↦ Subtype.ext (hψ x)
  rw [cohomologyWithSupports.forget_refl]
  rfl

/-- **Homeomorphisms of the ambient space.** For `φ : M ≅ M'`, the imbedded duality map of
`φ⁻¹⁻¹(A) = φ(A)` (with `X ≅ A ≅ φ(A)`) for `φ_* μ` takes `(φ⁻¹)^* c` to the imbedded duality
map of `A` for `μ` at `c`. -/
theorem embeddedDualityMap_pullback_symm {M M' : TopCat.{u}} (φ : M ≃ₜ M') {A : Set M}
    (hA : IsClosed A) (hAd : HasProperNeighbourhoodDeformations A)
    (hA'd : HasProperNeighbourhoodDeformations (φ.symm ⁻¹' A)) {X : TopCat.{u}} (ψ : X ≃ₜ A)
    {n : ℕ} (μ : borelMooreHomology R (ModuleCat.of R R) M n) (j k : ℤ) (h : j + k = n)
    (c : cohomologyWithSupports R (ModuleCat.of R R) M A j) :
    embeddedDualityMap R (hA.preimage φ.symm.continuous) hA'd
        (ψ.trans (preimageHomeomorph φ.symm A).symm)
        ((pushforward R (ModuleCat.of R R) (TopCat.ofHom (φ : C(M, M'))) φ.isProperMap n).hom μ)
        j k h
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
          (TopCat.ofHom (φ.symm : C(M', M))) A j).hom c) =
      embeddedDualityMap R hA hAd ψ μ j k h c := by
  obtain rfl : j = n - k := by omega
  rw [embeddedDualityMap_eq_dualityMap, embeddedDualityMap_eq_dualityMap]
  rw [← pushforward_dualityMap_pullback_symm R φ hA hAd hA'd μ k c]
  refine (pushforward_pushforward_apply_of_comp_eq R
    (TopCat.ofHom ((φ.symm : C(M', M)).restrictPreimage A)) (TopCat.ofHom (ψ.symm : C(A, X)))
    (TopCat.ofHom ((ψ.trans (preimageHomeomorph φ.symm A).symm).symm : C(φ.symm ⁻¹' A, X)))
    (φ.symm.isProperMap.restrictPreimage A) ψ.symm.isProperMap
    (ψ.trans (preimageHomeomorph φ.symm A).symm).symm.isProperMap ?_ k _).symm
  ext x
  rfl

/-- Pushforward along a proper map commutes with reindexing degrees: if `z` reindexes to `y`, the
pushforwards of `z` and `y` reindex to the same class in degree `k`. -/
lemma congrDegree_pushforward_eq_of_congrDegree_eq {X X' : TopCat.{u}} (g : X ⟶ X')
    (hg : IsProperMap g) {d₁ d₂ k : ℤ} (h₁ : d₁ = k) (h₂ : d₂ = k)
    (z : borelMooreHomology R (ModuleCat.of R R) X d₁)
    (y : borelMooreHomology R (ModuleCat.of R R) X d₂)
    (hz : congrDegree R X (h₁.trans h₂.symm) z = y) :
    congrDegree R X' h₁ ((pushforward R (ModuleCat.of R R) g hg d₁).hom z) =
      congrDegree R X' h₂ ((pushforward R (ModuleCat.of R R) g hg d₂).hom y) := by
  subst h₂ hz h₁
  rfl

section suspension

open FundamentalClass

/-- The point `0` of the real line has arbitrarily small proper neighbourhood deformations. -/
theorem hasProperNeighbourhoodDeformations_singleton_zero :
    HasProperNeighbourhoodDeformations ({0} : Set (TopCat.of (ULift.{u} ℝ))) :=
  hasProperNeighbourhoodDeformations_of_finiteDimensional (V := ULift.{u} ℝ) isClosed_singleton
    fun x ↦ haveI : Subsingleton ({0} : Set (ULift.{u} ℝ)) :=
      Set.subsingleton_singleton.coe_sort
      hasBasis_contractible_of_subsingleton x

/-- A class `u ∈ H^1(ℝ, ℝ - 0)` with `u ∩ μ_ℝ = [0]`. -/
def pointDual : cohomologyWithSupports R (ModuleCat.of R R)
    (TopCat.of (ULift.{u} ℝ)) {0} (1 : ℕ) :=
  Classical.choose
    (exists_capProductSupport_liftLineClass_eq R hasProperNeighbourhoodDeformations_singleton_zero)

/-- The cap product of `pointDual` with the fundamental class `μ_ℝ` of the real line is the class
`[0]` of the point `0`, in degree `0`. -/
lemma capProductSupport_pointDual :
    congrDegree R _ (by simp)
        (capProductSupport R (TopCat.of (ULift.{u} ℝ)) isClosed_singleton
          hasProperNeighbourhoodDeformations_singleton_zero (1 : ℕ) (1 : ℕ) (pointDual R)
          (liftLineClass R)) =
      (homologyEquiv R (TopCat.of ({0} : Set (ULift.{u} ℝ))) 0).symm
        (Submodule.Quotient.mk (singletonCycle R (0 : TopCat.of (ULift.{u} ℝ)))) :=
  Classical.choose_spec
    (exists_capProductSupport_liftLineClass_eq R hasProperNeighbourhoodDeformations_singleton_zero)

/-- The homeomorphism `X ≅ A ≅ A × 0 ≅ suspensionSet A` induced by `ψ : X ≅ A`. -/
def suspensionHomeomorph {m : ℕ} {A : Set (Fin m → ULift.{u} ℝ)} {X : TopCat.{u}} (ψ : X ≃ₜ A) :
    X ≃ₜ suspensionSet A :=
  ψ.trans ((sliceInterHomeomorph (TopCat.of (Fin m → ULift.{u} ℝ)) (TopCat.of (ULift.{u} ℝ)) A
    (0 : ULift.{u} ℝ)).trans (preimageHomeomorph (snocHomeomorph m).symm _).symm)

/-- `suspensionHomeomorph ψ` sends `x` to the point `(ψ x, 0)` of `ℝ^{m+1}`. -/
@[simp]
lemma coe_suspensionHomeomorph_apply {m : ℕ} {A : Set (Fin m → ULift.{u} ℝ)} {X : TopCat.{u}}
    (ψ : X ≃ₜ A) (x : X) :
    (suspensionHomeomorph ψ x : Fin (m + 1) → ULift.{u} ℝ) =
      Fin.snoc (α := fun _ ↦ ULift.{u} ℝ) (ψ x : Fin m → ULift.{u} ℝ) 0 :=
  rfl

/-- **The imbedded duality map of a euclidean suspension.** For closed, locally contractible
`A ⊆ ℝ^m`, `ψ : X ≅ A` and `c ∈ H^j(ℝ^m, ℝ^m - A)`, the imbedded duality map of `A × 0 ⊆ ℝ^{m+1}`
(for `μ_{m+1}`) at the suspension `σ c` is that of `A` (for `μ_m`) at `c`. -/
theorem embeddedDualityMap_euclideanSuspension (m : ℕ) {A : Set (Fin m → ULift.{u} ℝ)}
    (hA : IsClosed A)
    (hAc : ∀ x : A, (𝓝 x).HasBasis (fun V : Set A ↦ IsOpen V ∧ x ∈ V ∧ ContractibleSpace V) id)
    (hAd : HasProperNeighbourhoodDeformations A)
    (hA' : IsClosed (suspensionSet A)) (hA'd : HasProperNeighbourhoodDeformations (suspensionSet A))
    {X : TopCat.{u}} (ψ : X ≃ₜ A) (j k : ℤ) (h : j + k = m) (h' : j + (1 : ℕ) + k = (m + 1 : ℕ))
    (c : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (Fin m → ULift.{u} ℝ)) A j) :
    embeddedDualityMap R hA' hA'd (suspensionHomeomorph ψ) (euclideanClass R (m + 1))
        (j + (1 : ℕ)) k h' (euclideanSuspension R hA (pointDual R) j c) =
      embeddedDualityMap R hA hAd ψ (euclideanClass R m) j k h c := by
  set Y := TopCat.of (Fin m → ULift.{u} ℝ)
  set Z := TopCat.of (ULift.{u} ℝ)
  have hWc : ∀ x : (prSnd Y Z ⁻¹' ({0} : Set (ULift.{u} ℝ)) : Set (TopCat.of (Y × Z))),
      (𝓝 x).HasBasis (fun V ↦ IsOpen V ∧ x ∈ V ∧ ContractibleSpace V) id :=
    hasBasis_contractible_of_homeomorph (sliceHomeomorph Y Z (0 : ULift.{u} ℝ))
      (hasBasis_contractible_normedSpace (V := Fin m → ULift.{u} ℝ))
  have hWd : HasProperNeighbourhoodDeformations
      (prSnd Y Z ⁻¹' ({0} : Set (ULift.{u} ℝ)) : Set (TopCat.of (Y × Z))) :=
    hasProperNeighbourhoodDeformations_of_finiteDimensional
      (V := (Fin m → ULift.{u} ℝ) × ULift.{u} ℝ)
      (isClosed_singleton.preimage (prSnd Y Z).hom.continuous) hWc
  have hXWd : HasProperNeighbourhoodDeformations
      (prFst Y Z ⁻¹' A ∩ prSnd Y Z ⁻¹' ({0} : Set (ULift.{u} ℝ)) : Set (TopCat.of (Y × Z))) :=
    hasProperNeighbourhoodDeformations_of_finiteDimensional
      (V := (Fin m → ULift.{u} ℝ) × ULift.{u} ℝ)
      ((hA.preimage (prFst Y Z).hom.continuous).inter
        (isClosed_singleton.preimage (prSnd Y Z).hom.continuous))
      (hasBasis_contractible_of_homeomorph (sliceInterHomeomorph Y Z A (0 : ULift.{u} ℝ)) hAc)
  have hXd : HasProperNeighbourhoodDeformations
      (subsetInclusion (prSnd Y Z ⁻¹' ({0} : Set (ULift.{u} ℝ)))
        ⁻¹' (prFst Y Z ⁻¹' A)) :=
    hAd.preimage_homeomorph (sliceHomeomorph Y Z (0 : ULift.{u} ℝ)).symm
  have key := capProductSupport_euclideanSuspension R m hA hAd
    hasProperNeighbourhoodDeformations_singleton_zero hWd hXWd hXd hA'd (singletonSimplex (0 : Z))
    (singletonCycle R (0 : Z)) (coeff_singletonCycle_self R _)
    (fun _ hτ ↦ coeff_singletonCycle_of_ne R _ hτ) (pointDual R)
    (capProductSupport_pointDual R) j c
  rw [embeddedDualityMap_apply, embeddedDualityMap_apply, pushforward_congrDegree,
    pushforward_congrDegree]
  set g : TopCat.of (prFst Y Z ⁻¹' A ∩ prSnd Y Z ⁻¹' ({0} : Set (ULift.{u} ℝ)) :
      Set (TopCat.of (Y × Z))) ⟶ X :=
    TopCat.ofHom (((sliceInterHomeomorph Y Z A (0 : ULift.{u} ℝ)).symm.trans ψ.symm :
      C(_, X)))
  have hg : IsProperMap g := ((sliceInterHomeomorph Y Z A (0 : ULift.{u} ℝ)).symm.trans
    ψ.symm).isProperMap
  rw [← pushforward_pushforward_apply_of_comp_eq R
      (TopCat.ofHom (((snocHomeomorph m).symm :
        C(Fin (m + 1) → ULift.{u} ℝ, (Fin m → ULift.{u} ℝ) × ULift.{u} ℝ)).restrictPreimage
        (prFst Y Z ⁻¹' A ∩ prSnd Y Z ⁻¹' ({0} : Set (ULift.{u} ℝ))))) g _
      ((snocHomeomorph m).symm.isProperMap.restrictPreimage _) hg _ (by ext; rfl),
    ← pushforward_pushforward_apply_of_comp_eq R (sliceInter Y Z A (0 : ULift.{u} ℝ)) g
      (TopCat.ofHom (ψ.symm : C(A, X)))
      (sliceInterHomeomorph Y Z A (0 : ULift.{u} ℝ)).isProperMap hg ψ.symm.isProperMap
      (by ext x; exact congrArg ψ.symm (Subtype.ext rfl))]
  exact congrDegree_pushforward_eq_of_congrDegree_eq R g hg _ _ _ _ key

end suspension

end borelMooreHomology

end MMP
