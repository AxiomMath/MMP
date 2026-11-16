module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.ZeroSectionCycle.StacksAssemblyThom
public import MMP.AlgebraicTopology.CapProduct.SupportLemmas

/-!
# Fulton's Lemma 19.2(d): the cap product `ι^* u_ℰ ∩ c` over a ball of `V_reg` (Stacks bundles)

Let `ℰ` be a quasi-coherent `𝒪_X`-module, finite locally free of rank `r`, on a complex scheme
`X`, with vector bundle `π : 𝐕(ℰ) ⟶ X`, `V` a subvariety of `X`, `ι : E|_V → 𝐕(ℰ)` the inclusion
of `E|_V = π⁻¹(V)`, `h : ι⁻¹(0(X(ℂ))) ≅ V(ℂ)` the identification of the zero section of `E|_V`
with `V` (`MMP.Modules.zeroSectionPreimageHomeomorph`), and `c ∈ H_{2(m+r)}(E|_V)`. Over an open
set `B₀ ⊆ V_reg(ℂ)` lying over the domain of a chart of `ℰ`, let `Θ : P₀ ≅ B₀ × ℂʳ` be the bundle
chart (`MMP.Modules.bundleChartHomeomorph`) with second component `g`, and `μ_P = c|_{P₀}`. Then
`(h_*(ι^* u_ℰ ∩ c))|_{B₀} = ζ_*(g^* u₀ ∩ μ_P)`, read in `B₀`, for `ζ : g⁻¹(0) ≅ B₀` the zero
fibre of `Θ` and `u₀` the local orientation class of `ℂʳ` at `0`.

## Main results

* `MMP.Modules.restrict_pushforward_zeroSectionPreimageHomeomorphHom_capProductSupportPullback`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.2, proof of Lemma 19.2(d).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set Topology TopologicalSpace
open MMP.UnderlyingSpace

namespace MMP.Modules

open MMP.Intersection.Scheme
open borelMooreHomology BorelMooreCross FundamentalClass ThomClass

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X] {E : X.Modules}
  [E.IsQuasicoherent] {r : ℕ} [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E r]
  [IsComplexScheme (totalSpace E)] {V : Subvariety X} {ch : Chart E r}
  {B₀ : Opens (UnderlyingSpace ℂ V.toScheme)}
  (hB₀ : ∀ q ∈ B₀, q ∈ regularPart ℂ V.toScheme ∧ mapFun V.ι q ∈ chartBase ch)

include hB₀ in
/-- An open set `B₀` all of whose points lie in `V_reg(ℂ)` is contained in `V_reg(ℂ)`. -/
lemma subset_regularPart_of_forall_mem :
    (B₀ : Set (UnderlyingSpace ℂ V.toScheme)) ⊆ regularPart ℂ V.toScheme :=
  fun q hq ↦ (hB₀ q hq).1

variable (R : Type) [CommRing R]

set_option quotPrecheck false in
local notation "ιt" => TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (preimageSubvariety E r V).ι)

/- The inclusion `π_V⁻¹(B₀) → E|_V(ℂ)`. -/
set_option quotPrecheck false in
local notation "incP" => inclHom (Z := TopCat.of (UnderlyingSpace ℂ (preimageSubvariety E r V).toScheme))
  (preimageProjOpens E r V B₀)

/- The identification `P₀ ≅ π_V⁻¹(B₀)`. -/
set_option quotPrecheck false in
local notation "jP" => regularOpensInterHom (preimageProjOpens E r V B₀)
  (preimageProjOpens_subset_regularPart hB₀)

/-- **The cap product `ι^* u_E ∩ c` over a ball of `V_reg`** (Fulton, proof of Lemma 19.2(d)).
The restriction to `B₀` of `h_*(ι^* u_E ∩ c)` is `ζ_*(g^* u₀ ∩ c|_{P₀})`, read in `B₀`. -/
theorem restrict_pushforward_zeroSectionPreimageHomeomorphHom_capProductSupportPullback
    {u₀ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (Fin r → ℂ)) {0} (2 * r : ℕ)}
    (hu₀ : IsLocalOrientationClass R (complexOrientationBasis r) (0 : TopCat.of (Fin r → ℂ)) u₀)
    (k : ℤ)
    (c : borelMooreHomology R (ModuleCat.of R R)
      (TopCat.of (UnderlyingSpace ℂ (preimageSubvariety E r V).toScheme)) k) :
    (borelMooreHomology.restrict R (ModuleCat.of R R) (Y := TopCat.of (UnderlyingSpace ℂ V.toScheme)) B₀
        (k - (2 * r : ℕ))).hom
      ((borelMooreHomology.pushforward R (ModuleCat.of R R) (zeroSectionPreimageHomeomorphHom E r V)
        (zeroSectionPreimageHomeomorph E r V).isProperMap (k - (2 * r : ℕ))).hom
        (capProductSupportPullback R
          (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (preimageSubvariety E r V).ι))
          isClosed_range_zeroSection
          (hasProperNeighbourhoodDeformations_preimage_range_zeroSection E _) (2 * r : ℕ) k
          (thomClass R E r) c)) =
      (borelMooreHomology.pushforward R (ModuleCat.of R R)
          (regularOpensInterHom B₀ (subset_regularPart_of_forall_mem hB₀))
          (isProperMap_regularOpensInterHom _ _) (k - (2 * r : ℕ))).hom
        ((borelMooreHomology.pushforward R (ModuleCat.of R R)
          (TopCat.ofHom (zeroFibreHomeomorph (bundleChartHomeomorph hB₀) (bundleChartCoordHom hB₀)
            (fun _ ↦ rfl) : C(_, BundleChartBase V B₀)))
          (zeroFibreHomeomorph _ _ _).isProperMap (k - (2 * r : ℕ))).hom
          (capProductSupportPullback R (bundleChartCoordHom hB₀) isClosed_singleton
            (hasProperNeighbourhoodDeformations_preimage_zero_of_eq_snd
              (bundleChartHomeomorph hB₀) (bundleChartCoordHom hB₀) fun _ ↦ rfl) (2 * r : ℕ) k
            u₀
            ((borelMooreHomology.restrict R (ModuleCat.of R R) (Y := TopCat.of (regularOpens ℂ _))
              (regularOpensInter (𝕜 := ℂ) (preimageProjOpens E r V B₀)) k).hom
              ((borelMooreHomology.restrict R (ModuleCat.of R R)
                (Y := TopCat.of (UnderlyingSpace ℂ (preimageSubvariety E r V).toScheme))
                (regularOpens ℂ (preimageSubvariety E r V).toScheme :
                  Opens (TopCat.of (UnderlyingSpace ℂ (preimageSubvariety E r V).toScheme))) k).hom
                c)))) := by
  have hP₀ := preimageProjOpens_subset_regularPart hB₀
  have hS : IsClosed (range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) :=
    isClosed_range_zeroSection
  have hZc : IsClosed (ιt ⁻¹' range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) :=
    hS.preimage (continuous_mapFun _)
  have hZd := hasProperNeighbourhoodDeformations_preimage_range_zeroSection E
    (preimageSubvariety E r V).ι
  have hTc : IsClosed (incP ⁻¹' (ιt ⁻¹' range (UnderlyingSpace.map (K := ℂ) (zeroSection E)))) :=
    hZc.preimage continuous_subtype_val
  have hTd := hasProperNeighbourhoodDeformations_preimage_inclHom hB₀
  have hA := preimage_regularOpensInterHom_eq_preimage_zero hB₀
  have hd := hasProperNeighbourhoodDeformations_preimage_zero_of_eq_snd
    (bundleChartHomeomorph hB₀) (bundleChartCoordHom hB₀) fun _ ↦ rfl
  have hAd : HasProperNeighbourhoodDeformations
      (jP ⁻¹' (incP ⁻¹' (ιt ⁻¹' range (UnderlyingSpace.map (K := ℂ) (zeroSection E))))) :=
    hA ▸ hd
  have hg : (jP ⁻¹' (incP ⁻¹' (ιt ⁻¹' range (UnderlyingSpace.map (K := ℂ) (zeroSection E)))))ᶜ ⊆
      bundleChartCoordHom hB₀ ⁻¹' ({0}ᶜ : Set (TopCat.of (Fin r → ℂ))) := by
    rw [hA]; exact fun _ h ↦ h
  have hO : SetLike.coe (opensInter (preimageProjOpens E r V B₀)
      (ιt ⁻¹' range (UnderlyingSpace.map (K := ℂ) (zeroSection E)))) =
      SetLike.coe (Opens.comap (zeroSectionPreimageHomeomorphHom E r V).hom B₀) := by
    ext z
    change mapFun (preimageSubvarietyProj E r V) z.1 ∈ B₀ ↔ zeroSectionPreimageHomeomorph E r V z ∈ B₀
    rw [zeroSectionPreimageHomeomorph_apply]
  refine (restrict_pushforward_apply R (ModuleCat.of R R) (zeroSectionPreimageHomeomorphHom E r V)
    (show IsProperMap (zeroSectionPreimageHomeomorphHom E r V) from
      (zeroSectionPreimageHomeomorph E r V).isProperMap) B₀ _ _).trans ?_
  show (borelMooreHomology.pushforward R (ModuleCat.of R R) _ _ _).hom ((borelMooreHomology.restrict R (ModuleCat.of R R) _ _).hom _) = _
  have e2 := restrict_eq_pushforward_setCongr R hO (k - (2 * r : ℕ))
    (capProductSupportPullback R ιt hS hZd (2 * r : ℕ) k (thomClass R E r) c)
  have e3 := eq_pushforward_of_pushforward_eq R (opensInterMap _ _)
    (opensInterInv (preimageProjOpens E r V B₀)
      (ιt ⁻¹' range (UnderlyingSpace.map (K := ℂ) (zeroSection E)))) (isProperMap_opensInterMap _ _)
    (isProperMap_opensInterInv _ _) (opensInterMap_opensInterInv _ _) _
    (b := (borelMooreHomology.restrict R (ModuleCat.of R R) (opensInter (preimageProjOpens E r V B₀)
      (ιt ⁻¹' range (UnderlyingSpace.map (K := ℂ) (zeroSection E)))) (k - (2 * r : ℕ))).hom
      (capProductSupportPullback R ιt hS hZd (2 * r : ℕ) k (thomClass R E r) c)) rfl
  have e4 : (borelMooreHomology.pushforward R (ModuleCat.of R R) (opensInterMap (preimageProjOpens E r V B₀)
      (ιt ⁻¹' range (UnderlyingSpace.map (K := ℂ) (zeroSection E))))
        (isProperMap_opensInterMap _ _) (k - (2 * r : ℕ))).hom
      ((borelMooreHomology.restrict R (ModuleCat.of R R) (opensInter (preimageProjOpens E r V B₀)
        (ιt ⁻¹' range (UnderlyingSpace.map (K := ℂ) (zeroSection E)))) (k - (2 * r : ℕ))).hom
        (capProductSupportPullback R ιt hS hZd (2 * r : ℕ) k (thomClass R E r) c)) =
      capProductSupportPullback R incP hZc hTd (2 * r : ℕ) k
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R) ιt _ (2 * r : ℕ)).hom
          (thomClass R E r))
        ((borelMooreHomology.restrict R (ModuleCat.of R R) (Y := TopCat.of (UnderlyingSpace ℂ
          (preimageSubvariety E r V).toScheme)) (preimageProjOpens E r V B₀) k).hom c) :=
    pushforward_opensInterMap_restrict_capProductSupport R
      (TopCat.of (UnderlyingSpace ℂ (preimageSubvariety E r V).toScheme)) (preimageProjOpens E r V B₀)
      hZc hZd hTd _ k _ c
  have e5 := restrict_eq_pushforward_regularOpensInterHom R _ hP₀ k c
  have e6 := (pushforward_restrictPreimage_capProductSupportPullback R jP
    (isProperMap_regularOpensInterHom _ hP₀) hTc hTd hAd (2 * r : ℕ) k
    ((cohomologyWithSupports.pullback R (ModuleCat.of R R) incP _ (2 * r : ℕ)).hom
      ((cohomologyWithSupports.pullback R (ModuleCat.of R R) ιt _ (2 * r : ℕ)).hom
        (thomClass R E r)))
    ((borelMooreHomology.restrict R (ModuleCat.of R R) (Y := TopCat.of (regularOpens ℂ _))
      (regularOpensInter (𝕜 := ℂ) (preimageProjOpens E r V B₀)) k).hom
      ((borelMooreHomology.restrict R (ModuleCat.of R R)
        (Y := TopCat.of (UnderlyingSpace ℂ (preimageSubvariety E r V).toScheme))
        (regularOpens ℂ (preimageSubvariety E r V).toScheme :
          Opens (TopCat.of (UnderlyingSpace ℂ (preimageSubvariety E r V).toScheme))) k).hom c))).symm
  have e7 := pullback_regularOpensInterHom_pullback_thomClass hB₀ R hu₀ hg
  have e9 := pushforward_setCongr_capProductSupport_relMap R (bundleChartCoordHom hB₀)
    isClosed_singleton hA (hTc.preimage (TopCat.Hom.hom jP).continuous) hAd hg hd (2 * r : ℕ) k u₀
    ((borelMooreHomology.restrict R (ModuleCat.of R R) (Y := TopCat.of (regularOpens ℂ _))
      (regularOpensInter (𝕜 := ℂ) (preimageProjOpens E r V B₀)) k).hom
      ((borelMooreHomology.restrict R (ModuleCat.of R R)
        (Y := TopCat.of (UnderlyingSpace ℂ (preimageSubvariety E r V).toScheme))
        (regularOpens ℂ (preimageSubvariety E r V).toScheme :
          Opens (TopCat.of (UnderlyingSpace ℂ (preimageSubvariety E r V).toScheme))) k).hom c))
  have e8 := eq_pushforward_of_pushforward_eq R _
    (TopCat.ofHom ⟨(Homeomorph.setCongr hA).symm, (Homeomorph.setCongr hA).symm.continuous⟩) _
    (Homeomorph.setCongr hA).symm.isProperMap (by ext; rfl) _ e9
  conv_lhs => arg 2; rw [e2]
  conv_lhs => arg 2; arg 2; rw [e3]
  conv_lhs => arg 2; arg 2; arg 2; rw [e4]
  conv_lhs => arg 2; arg 2; arg 2; arg 2; rw [e5]
  conv_lhs => arg 2; arg 2; arg 2; erw [e6]
  conv_lhs => arg 2; arg 2; arg 2; arg 2; rw [capProductSupportPullback_apply]; arg 1; arg 2; rw [e7]
  conv_lhs => arg 2; arg 2; arg 2; arg 2; rw [e8]
  refine pushforward_chain_eq R _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun a ↦ Subtype.ext ?_) _ _
  exact zeroSectionPreimageHomeomorph_apply E r V _

end MMP.Modules
