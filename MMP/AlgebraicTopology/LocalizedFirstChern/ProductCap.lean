module

public import MMP.AlgebraicTopology.OrientationClass.CapProduct
public import MMP.AlgebraicTopology.CapProduct.SupportLemmas
public import MMP.AlgebraicTopology.OrientationClass.CapDeformation
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.FundamentalClassVarietyUnique
public import MMP.AlgebraicTopology.FundamentalClass.Homeomorphism
public import MMP.AlgebraicTopology.FundamentalClass.Euclidean

/-!
# The cap product with a local orientation class in a product chart (Fulton, §19.1)

Let `P` be an oriented real `(n + m)`-manifold with fundamental class `μ_P`, and
`Θ : P ≅ X × F` an orientation-preserving homeomorphism onto the product of a connected oriented
`n`-manifold `X` and an oriented real vector space `F` of even dimension `m`. Put
`g = pr₂ ∘ Θ : P → F` and `Y = g⁻¹(0)`, so that `y ↦ (Θ y).1` is a homeomorphism `Y ≅ X`. For the
local orientation class `u₀ ∈ H^m(F, F - 0)` of `F` at `0`, the cap product
`g^* u₀ ∩ μ_P ∈ H_n Y` is carried to the fundamental class `μ_X` of `X`.

Indeed `Θ_* μ_P` is a fundamental class of the connected manifold `X × F`
(`IsFundamentalClass.pushforward_homeomorph`), hence equals `μ_X × μ_F`
(`IsFundamentalClass.exteriorProduct` and uniqueness); by the projection formula the push-forward
of `g^* u₀ ∩ μ_P = Θ^*(pr^* u₀) ∩ μ_P` to `X × {0}` is `pr^* u₀ ∩ (μ_X × μ_F)`, which the
projection `X × {0} ≅ X` carries to a fundamental class of `X` (the local model), that is, to
`μ_X`.

This is the computation of `s^* u_L ∩ μ_X` near a general point of a component of the zero
scheme of a section `s` of a line bundle (Fulton, proof of Lemma 19.1.3), in a holomorphic chart
`U' ≅ B_ε × B'` in which the local equation of the component is the first coordinate, composed
with a radial homeomorphism `B_ε ≅ ℂ`: there `F = ℂ` with the basis `1, i`.

## Main definitions

* `MMP.zeroFibreHomeomorph`: the homeomorphism `g⁻¹(0) ≅ X`, `y ↦ (Θ y).1`.

## Main results

* `MMP.IsFundamentalClass.pushforward_capProductSupportPullback_prSnd_of_even`:
  the local model `pr^* u₀ ∩ (μ_X × μ_F) = μ_X` for any orientation of `F` of even dimension.
* `MMP.IsFundamentalClass.pushforward_eq_exteriorProduct`:
  `Θ_* μ_P = μ_X × μ_F`.
* `MMP.IsFundamentalClass.pushforward_zeroFibreHomeomorph_capProductSupportPullback`:
  `g^* u₀ ∩ μ_P` is carried to `μ_X`.
* `MMP.IsFundamentalClass.pushforward_zeroFibreHomeomorph_capProductSupportPullback_complex`:
  the case `F = ℂ`, oriented by `1, i`, with `u₀` in degree `2`.

## Implementation notes

The orientation of `F` is an arbitrary basis `b_F` of even length `m` (the product formula for
cap products is stated for classes of even degree), rather than the complex orientation of a
complex vector space: for `F = ℂ` this lets the basis `1, i` and the degree `2` be used as they
are, without a transport to the basis `complexOrientationBasisOf ℂ` of length
`2 * Module.finrank ℂ ℂ`. The local model is therefore proved again for such `b_F`, by the
argument of `IsFundamentalClass.pushforward_capProductSupportPullback_prSnd`.

The identification `Θ_* μ_P = μ_X × μ_F` uses the uniqueness of fundamental classes of connected
manifolds, hence `X` is assumed connected and second countable (and metrizable, for the proper
neighbourhood deformations of `X × {0}`).

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, proof of Lemma 19.1.3.
-/

@[expose] public noncomputable section

open Set CategoryTheory Topology

universe u

namespace MMP

open FundamentalClass borelMooreHomology BorelMooreCross BorelMooreCap ThomClass TensorProduct

section LocalModel

variable (R : Type u) [CommRing R]
  {H : Type*} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [ContinuousAdd H]
  [ContinuousSMul ℝ H] {X : Type u} [TopologicalSpace X] [T2Space X] [ChartedSpace H X]
  {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **The local model of `u_{M,P} ∩ μ_P = μ_M`, for an orientation of the fibre of even
dimension.** In `X × F`, with `μ_X` a fundamental class of `X`, `F` oriented by a basis `b_F`
of even length `m`, `μ_F` its fundamental class and `u₀ ∈ H^m(F, F - 0)` the local orientation
class at `0`, the cap product `pr^* u₀ ∩ (μ_X × μ_F) ∈ H_n(X × {0})` is carried to a
fundamental class of `X` by the projection `X × {0} ≅ X`. -/
theorem IsFundamentalClass.pushforward_capProductSupportPullback_prSnd_of_even {n m : ℕ}
    (hm : Even m) {b : Module.Basis (Fin n) ℝ H} {bF : Module.Basis (Fin m) ℝ F}
    {μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of X) n} (hμ : IsFundamentalClass R b μ)
    {μF : borelMooreHomology R (ModuleCat.of R R) (TopCat.of F) m}
    (hμF : IsFundamentalClass R bF μF)
    {u₀ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of F) {0} m}
    (hu₀ : IsLocalOrientationClass R bF (0 : TopCat.of F) u₀)
    (h0d : HasProperNeighbourhoodDeformations ({0} : Set (TopCat.of F)))
    (hXd : HasProperNeighbourhoodDeformations
      (prSnd (TopCat.of X) (TopCat.of F) ⁻¹' ({0} : Set (TopCat.of F))))
    (hdeg : (n : ℤ) + (m : ℕ) - (m : ℕ) = (n : ℕ)) :
    IsFundamentalClass R b
      ((pushforward R (ModuleCat.of R R) (prPreFst (TopCat.of X) ({0} : Set (TopCat.of F)))
        (isProperMap_prPreFst _ _) n).hom
        (congrDegree R _ hdeg
          (capProductSupportPullback R (prSnd (TopCat.of X) (TopCat.of F)) isClosed_singleton hXd
            (m : ℕ) ((n : ℤ) + (m : ℕ)) u₀
            (borelMooreHomology.exteriorProduct R (TopCat.of X) (TopCat.of F) n m
              (μ ⊗ₜ μF))))) := by
  have h0 : ((m : ℕ) : ℤ) - ((m : ℕ) : ℤ) = ((0 : ℕ) : ℤ) := by simp
  obtain ⟨c, hcdef⟩ : ∃ c, c = congrDegree R _ h0 (capProductSupport R (TopCat.of F)
      isClosed_singleton h0d _ _ u₀ μF) := ⟨_, rfl⟩
  have hc : IsLocallyClassOf R c (default : ({0} : Set (TopCat.of F)))
      (ContinuousMap.const _ default) := by
    rw [hcdef]
    exact isLocallyClassOf_capProductSupport_of_isLocalOrientationClass (M := F)
      bF h0d hμF hu₀ h0 _ _
  have hfund := hμ.pushforward_fst_exteriorProduct R ({0} : Set (TopCat.of F)) hc
  have hcap : capProductSupport R (TopCat.of F) isClosed_singleton h0d _ _ u₀ μF =
      congrDegree R _ h0.symm c := by
    rw [hcdef, congrDegree_congrDegree_apply]
    rfl
  have hext := pushforward_prodPreimage_exteriorProduct_capProductSupport R (TopCat.of X)
    (TopCat.of F) isClosed_singleton h0d hXd n _ _ (by exact_mod_cast hm) u₀ μ μF
  rw [hcap, exteriorProduct_congrDegree_right] at hext
  have h' : (n : ℤ) + (((m : ℕ) : ℤ) - ((m : ℕ) : ℤ)) = n := by omega
  have key := congrArg (congrDegree R _ h') hext
  rw [congrDegree_congrDegree_apply] at key
  rw [← key, pushforward_congrDegree_apply, ← ModuleCat.comp_apply, ← pushforward_comp,
    pushforward_congr_hom R (prodPreimage_comp_prPreFst (TopCat.of X) ({0} : Set (TopCat.of F)))
      _ isProperMap_fst_of_compactSpace]
  convert hfund using 1
  exact congrDegree_pushforward_congrDegree_of_eq R _ _ _ _ _ _

end LocalModel

section ZeroFibre

variable {P X F : Type u} [TopologicalSpace P] [TopologicalSpace X] [TopologicalSpace F]
  [Zero F]

/-- For `g = pr₂ ∘ Θ`, the points `Θ⁻¹(x, 0)` lie in `g⁻¹(0)`. -/
lemma mem_preimage_zero_of_eq_snd (Θ : P ≃ₜ X × F) (g : TopCat.of P ⟶ TopCat.of F)
    (hg : ∀ p, g p = (Θ p).2) (x : X) :
    Θ.symm (x, 0) ∈ (g ⁻¹' {0} : Set (TopCat.of P)) := by
  change g (Θ.symm (x, 0)) = 0
  rw [hg, Θ.apply_symm_apply]

/-- The homeomorphism `g⁻¹(0) ≅ X`, `y ↦ (Θ y).1`, for a homeomorphism `Θ : P ≅ X × F` and
`g = pr₂ ∘ Θ`. -/
def zeroFibreHomeomorph (Θ : P ≃ₜ X × F) (g : TopCat.of P ⟶ TopCat.of F)
    (hg : ∀ p, g p = (Θ p).2) : (g ⁻¹' {0} : Set (TopCat.of P)) ≃ₜ X where
  toFun y := (Θ y).1
  invFun x := ⟨Θ.symm (x, 0), mem_preimage_zero_of_eq_snd Θ g hg x⟩
  left_inv y := Subtype.ext <| by
    have hy : (Θ y).2 = 0 := (hg y).symm.trans y.2
    have h : ((Θ y).1, (0 : F)) = Θ y := Prod.ext rfl hy.symm
    exact (congrArg Θ.symm h).trans (Θ.symm_apply_apply _)
  right_inv x := congrArg Prod.fst (Θ.apply_symm_apply (x, 0))
  continuous_toFun := continuous_fst.comp (Θ.continuous.comp continuous_subtype_val)
  continuous_invFun := (Θ.symm.continuous.comp (continuous_id.prodMk continuous_const)).subtype_mk _

/-- `zeroFibreHomeomorph Θ g hg` sends `y` to `(Θ y).1`. -/
@[simp]
lemma zeroFibreHomeomorph_apply (Θ : P ≃ₜ X × F) (g : TopCat.of P ⟶ TopCat.of F)
    (hg : ∀ p, g p = (Θ p).2) (y : (g ⁻¹' {0} : Set (TopCat.of P))) :
    zeroFibreHomeomorph Θ g hg y = (Θ y).1 :=
  rfl

/-- `(zeroFibreHomeomorph Θ g hg).symm` sends `x` to `Θ.symm (x, 0)`. -/
@[simp]
lemma coe_zeroFibreHomeomorph_symm_apply (Θ : P ≃ₜ X × F) (g : TopCat.of P ⟶ TopCat.of F)
    (hg : ∀ p, g p = (Θ p).2) (x : X) :
    ((zeroFibreHomeomorph Θ g hg).symm x : P) = Θ.symm (x, 0) :=
  rfl

end ZeroFibre

section ProductChart

variable (R : Type u) [CommRing R]
  {H : Type*} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [ContinuousAdd H]
  [ContinuousSMul ℝ H]
  {H' : Type*} [AddCommGroup H'] [Module ℝ H'] [TopologicalSpace H'] [ContinuousAdd H']
  [ContinuousSMul ℝ H'] [T2Space H']
  {P : Type u} [TopologicalSpace P] [T2Space P] [ChartedSpace H P]
  {X : Type u} [TopologicalSpace X] [T2Space X] [ChartedSpace H' X]
  {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Transport of the homology class along an equality of degrees commutes with the cap
product `f^* c ∩ -`. -/
lemma capProductSupportPullback_congrDegree {Y' Y : TopCat.{u}} (f : Y' ⟶ Y) {Z : Set Y}
    (hZ : IsClosed Z) (hZd : HasProperNeighbourhoodDeformations (f ⁻¹' Z)) (j : ℤ) {k k' : ℤ}
    (h : k = k') {t : ℤ} (hn : k - j = t) (hn' : k' - j = t)
    (c : cohomologyWithSupports R (ModuleCat.of R R) Y Z j)
    (a : borelMooreHomology R (ModuleCat.of R R) Y' k) :
    congrDegree R _ hn' (capProductSupportPullback R f hZ hZd j k' c (congrDegree R _ h a)) =
      congrDegree R _ hn (capProductSupportPullback R f hZ hZd j k c a) := by
  subst h
  rfl

omit [T2Space P] [T2Space X] in
/-- For `g = pr₂ ∘ Θ` with `X` metrizable and `F` a finite-dimensional real space, the fibre
`g⁻¹(0)` has arbitrarily small proper neighbourhood deformations in `P`. -/
theorem hasProperNeighbourhoodDeformations_preimage_zero_of_eq_snd
    [TopologicalSpace.MetrizableSpace X] (Θ : P ≃ₜ X × F) (g : TopCat.of P ⟶ TopCat.of F)
    (hg : ∀ p, g p = (Θ p).2) : HasProperNeighbourhoodDeformations (g ⁻¹' {0}) := by
  have he : (Θ ⁻¹' (prodSnd (TopCat.of X) (TopCat.of F) ⁻¹' {(0 : TopCat.of F)}) : Set P) =
      g ⁻¹' {0} := by
    ext p
    change (Θ p).2 = 0 ↔ g p = 0
    rw [hg]
  exact he ▸ (hasProperNeighbourhoodDeformations_prodSnd_preimage_singleton (TopCat.of X) F
    (0 : TopCat.of F)).preimage_homeomorph Θ

/-- **`Θ_* μ_P = μ_X × μ_F`.** For an orientation-preserving homeomorphism `Θ : P ≅ X × F` onto
the product of a connected second countable oriented manifold `X` and an oriented real vector
space `F` (product orientation), the push-forward of a fundamental class of `P` is the exterior
product of fundamental classes of `X` and `F`. -/
theorem IsFundamentalClass.pushforward_eq_exteriorProduct [ConnectedSpace X]
    [SecondCountableTopology X] {n m : ℕ} {b : Module.Basis (Fin (n + m)) ℝ H}
    {b' : Module.Basis (Fin n) ℝ H'} {bF : Module.Basis (Fin m) ℝ F}
    {μP : borelMooreHomology R (ModuleCat.of R R) (TopCat.of P) (n + m : ℕ)}
    (hμP : IsFundamentalClass R b μP)
    {μX : borelMooreHomology R (ModuleCat.of R R) (TopCat.of X) n}
    (hμX : IsFundamentalClass R b' μX)
    {μF : borelMooreHomology R (ModuleCat.of R R) (TopCat.of F) m}
    (hμF : IsFundamentalClass R bF μF) (Θ : P ≃ₜ X × F)
    (hΘ : IsOrientationPreserving (H' := ModelProd H' F) b
      ((b'.prod bF).reindex finSumFinEquiv) Θ) :
    pushforward R (ModuleCat.of R R) (TopCat.ofHom (Θ : C(P, X × F))) Θ.isProperMap (n + m : ℕ) μP =
      congrDegree R _ (Nat.cast_add n m).symm
        (borelMooreHomology.exteriorProduct R (TopCat.of X) (TopCat.of F) n m (μX ⊗ₜ μF)) := by
  have : T2Space (ModelProd H' F) := inferInstanceAs (T2Space (H' × F))
  exact (hμX.exteriorProduct R hμF).eq_of_connectedSpace' (hμP.pushforward_homeomorph R Θ hΘ)

/-- **`g^* u₀ ∩ μ_P = μ_X` in a product chart.** Let `P` be an oriented `(n + m)`-manifold with
fundamental class `μ_P`, and `Θ : P ≅ X × F` an orientation-preserving homeomorphism onto the
product of a connected, second countable, metrizable oriented `n`-manifold `X` (fundamental class
`μ_X`) and a real vector space `F` oriented by a basis `b_F` of even length `m` (product
orientation). Let `g : P → F` be `pr₂ ∘ Θ`, and `u₀ ∈ H^m(F, F - 0)` the local orientation class
of `F` at `0`. Then the homeomorphism `g⁻¹(0) ≅ X`, `y ↦ (Θ y).1`, carries
`g^* u₀ ∩ μ_P ∈ H_n(g⁻¹ 0)` to `μ_X`. -/
theorem IsFundamentalClass.pushforward_zeroFibreHomeomorph_capProductSupportPullback
    [ConnectedSpace X] [SecondCountableTopology X] [TopologicalSpace.MetrizableSpace X]
    {n m : ℕ} (hm : Even m) {b : Module.Basis (Fin (n + m)) ℝ H}
    {b' : Module.Basis (Fin n) ℝ H'} {bF : Module.Basis (Fin m) ℝ F}
    {μP : borelMooreHomology R (ModuleCat.of R R) (TopCat.of P) (n + m : ℕ)}
    (hμP : IsFundamentalClass R b μP)
    {μX : borelMooreHomology R (ModuleCat.of R R) (TopCat.of X) n}
    (hμX : IsFundamentalClass R b' μX) (Θ : P ≃ₜ X × F)
    (hΘ : IsOrientationPreserving (H' := ModelProd H' F) b
      ((b'.prod bF).reindex finSumFinEquiv) Θ)
    (g : TopCat.of P ⟶ TopCat.of F) (hg : ∀ p, g p = (Θ p).2)
    {u₀ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of F) {0} m}
    (hu₀ : IsLocalOrientationClass R bF (0 : TopCat.of F) u₀)
    (hYd : HasProperNeighbourhoodDeformations (g ⁻¹' {0}))
    (hdeg : ((n + m : ℕ) : ℤ) - (m : ℕ) = (n : ℕ)) :
    (pushforward R (ModuleCat.of R R)
        (TopCat.ofHom (zeroFibreHomeomorph Θ g hg : C(g ⁻¹' {0}, X)))
        (zeroFibreHomeomorph Θ g hg).isProperMap n).hom
      (congrDegree R _ hdeg
        (capProductSupportPullback R g isClosed_singleton hYd (m : ℕ) (n + m : ℕ) u₀ μP)) = μX := by
  obtain ⟨μF, hμF⟩ := exists_isFundamentalClass_of_basis R bF
  set Θ' : TopCat.of P ⟶ TopCat.of (TopCat.of X × TopCat.of F) :=
    TopCat.ofHom (Θ : C(P, X × F)) with hΘ'
  have hgΘ : g = Θ' ≫ prSnd (TopCat.of X) (TopCat.of F) := by
    ext p
    exact hg p
  subst hgΘ
  have hΘp : IsProperMap Θ' := Θ.isProperMap
  have h0d : HasProperNeighbourhoodDeformations ({0} : Set (TopCat.of F)) :=
    (hasProperNeighbourhoodDeformations_prodSnd_preimage_singleton (TopCat.of PUnit.{u + 1})
      (T := TopCat.of F) F 0).preimage_homeomorph (Homeomorph.punitProd F).symm
  have hXd : HasProperNeighbourhoodDeformations
      (prSnd (TopCat.of X) (TopCat.of F) ⁻¹' ({0} : Set (TopCat.of F))) :=
    hasProperNeighbourhoodDeformations_prodSnd_preimage_singleton (TopCat.of X) F
      (0 : TopCat.of F)
  have hZ : IsClosed (prSnd (TopCat.of X) (TopCat.of F) ⁻¹' ({0} : Set (TopCat.of F))) :=
    isClosed_singleton.preimage (prSnd (TopCat.of X) (TopCat.of F)).hom.continuous
  have hrP : IsProperMap (TopCat.ofHom (Θ'.hom.restrictPreimage
      (prSnd (TopCat.of X) (TopCat.of F) ⁻¹' ({0} : Set (TopCat.of F))))) :=
    hΘp.restrictPreimage _
  have hcap : capProductSupportPullback R (Θ' ≫ prSnd (TopCat.of X) (TopCat.of F))
      isClosed_singleton hYd (m : ℕ) (n + m : ℕ) u₀ μP =
      capProductSupportPullback R Θ' hZ hYd (m : ℕ) (n + m : ℕ)
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
          (prSnd (TopCat.of X) (TopCat.of F)) {0} (m : ℕ)).hom u₀) μP := by
    rw [capProductSupportPullback_apply, capProductSupportPullback_apply,
      cohomologyWithSupports.pullback_comp]
    rfl
  have hproj := pushforward_restrictPreimage_capProductSupportPullback R Θ' hΘp hZ hXd
    hYd (m : ℕ) (n + m : ℕ) ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
      (prSnd (TopCat.of X) (TopCat.of F)) {0} (m : ℕ)).hom u₀) μP
  rw [hμP.pushforward_eq_exteriorProduct R hμX hμF Θ hΘ] at hproj
  have hfac : TopCat.ofHom (zeroFibreHomeomorph Θ (Θ' ≫ prSnd (TopCat.of X) (TopCat.of F)) hg :
      C((Θ' ≫ prSnd (TopCat.of X) (TopCat.of F)) ⁻¹' {0}, X)) =
      TopCat.ofHom (Θ'.hom.restrictPreimage
        (prSnd (TopCat.of X) (TopCat.of F) ⁻¹' ({0} : Set (TopCat.of F)))) ≫
        prPreFst (TopCat.of X) ({0} : Set (TopCat.of F)) := rfl
  have hdeg' : (n : ℤ) + (m : ℕ) - (m : ℕ) = (n : ℕ) := by omega
  have hloc := hμX.pushforward_capProductSupportPullback_prSnd_of_even R hm hμF hu₀ h0d hXd hdeg'
  rw [pushforward_congr_hom R hfac _ ((isProperMap_prPreFst _ _).comp
      (by exact hrP)),
    pushforward_comp R (ModuleCat.of R R) _ _ (by exact hrP)
      (isProperMap_prPreFst _ _), ModuleCat.comp_apply,
    pushforward_congrDegree_apply, hcap, hproj]
  have key : congrDegree R _ hdeg (capProductSupport R _ hZ hXd (m : ℕ) (n + m : ℕ)
      ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
        (prSnd (TopCat.of X) (TopCat.of F)) {0} (m : ℕ)).hom u₀)
      (congrDegree R _ (Nat.cast_add n m).symm
        (borelMooreHomology.exteriorProduct R (TopCat.of X) (TopCat.of F) n m (μX ⊗ₜ μF)))) =
      congrDegree R _ hdeg' (capProductSupportPullback R (prSnd (TopCat.of X) (TopCat.of F))
        isClosed_singleton hXd (m : ℕ) ((n : ℤ) + (m : ℕ)) u₀
        (borelMooreHomology.exteriorProduct R (TopCat.of X) (TopCat.of F) n m (μX ⊗ₜ μF))) :=
    capProductSupportPullback_congrDegree R _ isClosed_singleton hXd _ _ hdeg' hdeg _ _
  rw [key]
  exact hμX.eq_of_connectedSpace' hloc

end ProductChart

section Complex

variable (R : Type) [CommRing R]
  {H : Type*} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [ContinuousAdd H]
  [ContinuousSMul ℝ H]
  {H' : Type*} [AddCommGroup H'] [Module ℝ H'] [TopologicalSpace H'] [ContinuousAdd H']
  [ContinuousSMul ℝ H'] [T2Space H']
  {P : Type} [TopologicalSpace P] [T2Space P] [ChartedSpace H P]
  {X : Type} [TopologicalSpace X] [T2Space X] [ChartedSpace H' X]

/-- **`g^* u₀ ∩ μ_P = μ_X` in a product chart with a complex line.** Let `P` be an oriented
`(n + 2)`-manifold with fundamental class `μ_P`, and `Θ : P ≅ X × ℂ` a homeomorphism onto the
product of a connected, second countable, metrizable oriented `n`-manifold `X` (fundamental class
`μ_X`) and `ℂ`, orientation preserving for the product of the orientation of `X` and the
orientation `1, i` of `ℂ`. Let `g = pr₂ ∘ Θ : P → ℂ` and `u₀ ∈ H²(ℂ, ℂ - 0)` the local orientation
class of `ℂ` at `0` for the orientation `1, i`. Then the homeomorphism `g⁻¹(0) ≅ X`,
`y ↦ (Θ y).1`, carries `g^* u₀ ∩ μ_P ∈ H_n(g⁻¹ 0)` to `μ_X`.

For a holomorphic chart `ψ ∘ e : U' ≅ B_ε × B'` followed by a homeomorphism `B_ε ≅ ℂ` which is a
diffeomorphism with positive Jacobian, the hypothesis `hΘ` follows from
`isOrientationPreserving_of_hasFDerivAt` (complex linear derivatives have positive real
determinant). -/
theorem IsFundamentalClass.pushforward_zeroFibreHomeomorph_capProductSupportPullback_complex
    [ConnectedSpace X] [SecondCountableTopology X] [TopologicalSpace.MetrizableSpace X]
    {n : ℕ} {b : Module.Basis (Fin (n + 2)) ℝ H} {b' : Module.Basis (Fin n) ℝ H'}
    {μP : borelMooreHomology R (ModuleCat.of R R) (TopCat.of P) (n + 2 : ℕ)}
    (hμP : IsFundamentalClass R b μP)
    {μX : borelMooreHomology R (ModuleCat.of R R) (TopCat.of X) n}
    (hμX : IsFundamentalClass R b' μX) (Θ : P ≃ₜ X × ℂ)
    (hΘ : IsOrientationPreserving (H' := ModelProd H' ℂ) b
      ((b'.prod Complex.basisOneI).reindex finSumFinEquiv) Θ)
    (g : TopCat.of P ⟶ TopCat.of ℂ) (hg : ∀ p, g p = (Θ p).2)
    {u₀ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of ℂ) {0} (2 : ℕ)}
    (hu₀ : IsLocalOrientationClass R Complex.basisOneI (0 : TopCat.of ℂ) u₀)
    (hYd : HasProperNeighbourhoodDeformations (g ⁻¹' {0}))
    (hdeg : ((n + 2 : ℕ) : ℤ) - (2 : ℕ) = (n : ℕ)) :
    (pushforward R (ModuleCat.of R R)
        (TopCat.ofHom (zeroFibreHomeomorph Θ g hg : C(g ⁻¹' {0}, X)))
        (zeroFibreHomeomorph Θ g hg).isProperMap n).hom
      (congrDegree R _ hdeg
        (capProductSupportPullback R g isClosed_singleton hYd (2 : ℕ) (n + 2 : ℕ) u₀ μP)) = μX :=
  hμP.pushforward_zeroFibreHomeomorph_capProductSupportPullback R even_two hμX Θ hΘ g hg hu₀
    hYd hdeg

end Complex

end MMP
