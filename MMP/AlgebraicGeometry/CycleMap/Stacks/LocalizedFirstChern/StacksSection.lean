module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.StacksThomClass
public import MMP.AlgebraicTopology.CapProduct.SupportRetraction
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleZeroSection
public import MMP.AlgebraicGeometry.SubschemeOver
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.PointsOver

/-!
# The localized top Chern class of a section of a Stacks vector bundle (Fulton, §19.1)

Let `ℰ` be a quasi-coherent `𝒪_X`-module, finite locally free of rank `r`, on a complex scheme
`X`, with vector bundle `π : 𝐕(ℰ) ⟶ X` and zero section `0 : X ⟶ 𝐕(ℰ)`, and let
`σ : X ⟶ 𝐕(ℰ)` be a morphism over `ℂ` (a section when `σ ≫ π = 𝟙`). Its zero scheme
`Z(σ) = σ⁻¹(0(X))` is the scheme-theoretic preimage of the zero section
(`MMP.Modules.zeroLocus`), and `σ` is a map of pairs
`(X(ℂ), X(ℂ) - Z(σ)(ℂ)) → (𝐕(ℰ)(ℂ), 𝐕(ℰ)(ℂ) - 0(X(ℂ)))`. The pull-back `σ^*(u_ℰ)` of the Thom
class capped with `a ∈ H_k X` lies in `H_{k-2r}(σ⁻¹(0(X(ℂ))))`
(`MMP.Modules.localizedTopChernCap`).

## Main definitions

* `MMP.Modules.zeroLocus`: the zero scheme `σ⁻¹(0(X))`, an ideal sheaf on `X`.
* `MMP.Modules.zeroLocusHomeomorph`: the homeomorphism `Z(σ)(ℂ) ≃ₜ σ⁻¹(0(X(ℂ)))`.
* `MMP.Modules.zeroLocusHom`: the same map as a morphism in `TopCat`.
* `MMP.Modules.localizedTopChernCap`: `a ↦ σ^*(u_ℰ) ∩ a`.

## Main results

* `MMP.Modules.preimage_mapFun_range_zeroSection`: `σ⁻¹(0(X(ℂ))) = Z(σ)(ℂ)` as subsets of `X(ℂ)`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1 and Appendix B.3.2.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set
open scoped MMP.SubschemeOver

namespace MMP.Modules

open UnderlyingSpace

variable {X : Scheme.{0}} (E : X.Modules) [E.IsQuasicoherent]

/-- The zero section `0 : X ⟶ 𝐕(ℰ)` is a closed immersion. -/
instance isClosedImmersion_zeroSection : IsClosedImmersion (zeroSection E) :=
  Scheme.Modules.isClosedImmersion_vectorBundleZeroSection X E

/-- **The zero scheme of `σ : X ⟶ 𝐕(ℰ)`**: the scheme-theoretic preimage `σ⁻¹(0(X))` of the zero
section, as an ideal sheaf on `X` (Fulton, Appendix B.3.2). -/
def zeroLocus (σ : X ⟶ totalSpace E) : X.IdealSheafData :=
  (zeroSection E).ker.comap σ

/-- The support of the zero scheme of `σ` is the preimage under `σ` of the image of the zero
section. -/
lemma support_zeroLocus (σ : X ⟶ totalSpace E) :
    ((zeroLocus E σ).support : Set X) = σ.base ⁻¹' range (zeroSection E).base := by
  rw [zeroLocus, Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
    Scheme.Hom.support_ker, (zeroSection E).isClosedEmbedding.isClosed_range.closure_eq]

variable [X.Over (Spec (.of ℂ))] {E} (σ : X ⟶ totalSpace E) [σ.IsOver (Spec (.of ℂ))]

/-- **`σ⁻¹(0(X(ℂ))) = Z(σ)(ℂ)`**: the complex points that `σ` sends into the zero section are
those over the zero scheme. -/
theorem preimage_mapFun_range_zeroSection :
    mapFun σ ⁻¹' range (UnderlyingSpace.map (K := ℂ) (zeroSection E)) =
      pointsOver (K := ℂ) ((zeroLocus E σ).support : Set X) := by
  rw [range_map_of_isClosedImmersion, support_zeroLocus]
  ext p
  simp only [mem_preimage, mem_pointsOver, toHom_mapFun]
  rfl

/-- `σ⁻¹(0(X(ℂ)))` is the image of the complex points of the zero scheme. -/
theorem preimage_mapFun_range_zeroSection_eq_range :
    mapFun σ ⁻¹' range (UnderlyingSpace.map (K := ℂ) (zeroSection E)) =
      range (UnderlyingSpace.map (K := ℂ) (zeroLocus E σ).subschemeι) := by
  rw [preimage_mapFun_range_zeroSection, range_map_of_isClosedImmersion,
    Scheme.IdealSheafData.range_subschemeι]

/-- The homeomorphism `Z(σ)(ℂ) ≅ σ⁻¹(0(X(ℂ)))`. -/
def zeroLocusHomeomorph :
    UnderlyingSpace ℂ (zeroLocus E σ).subscheme ≃ₜ
      (mapFun σ ⁻¹' range (UnderlyingSpace.map (K := ℂ) (zeroSection E)) :
        Set (UnderlyingSpace ℂ X)) :=
  (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ)
    (zeroLocus E σ).subschemeι).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (preimage_mapFun_range_zeroSection_eq_range σ).symm)

/-- The homeomorphism `zeroLocusHomeomorph σ` sends a complex point of `Z(σ)` to its image in
`X(ℂ)` under the closed immersion `Z(σ) ⟶ X`. -/
@[simp]
lemma coe_zeroLocusHomeomorph_apply (p : UnderlyingSpace ℂ (zeroLocus E σ).subscheme) :
    (zeroLocusHomeomorph σ p : UnderlyingSpace ℂ X) =
      UnderlyingSpace.map (K := ℂ) (zeroLocus E σ).subschemeι p :=
  rfl

/-- The homeomorphism `Z(σ)(ℂ) → σ⁻¹(0(X(ℂ)))`, as a morphism of `TopCat`. -/
def zeroLocusHom : TopCat.of (UnderlyingSpace ℂ (zeroLocus E σ).subscheme) ⟶
    TopCat.of ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹'
      range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) :=
  TopCat.ofHom ⟨zeroLocusHomeomorph σ, (zeroLocusHomeomorph σ).continuous⟩

/-- The map `zeroLocusHom σ : Z(σ)(ℂ) → σ⁻¹(0(X(ℂ)))` is proper. -/
lemma isProperMap_zeroLocusHom : IsProperMap (zeroLocusHom σ) :=
  (zeroLocusHomeomorph σ).isProperMap

/-- The zero section `0(X(ℂ))` is closed in `𝐕(ℰ)(ℂ)`. -/
lemma isClosed_range_zeroSection :
    IsClosed (range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) :=
  (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) (zeroSection E)).isClosed_range

variable [IsComplexScheme X]

/-- `σ⁻¹(0(X(ℂ)))` has arbitrarily small proper neighbourhood deformations in `X(ℂ)`. -/
theorem hasProperNeighbourhoodDeformations_preimage :
    HasProperNeighbourhoodDeformations
      ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) := by
  change HasProperNeighbourhoodDeformations
    (mapFun σ ⁻¹' range (UnderlyingSpace.map (K := ℂ) (zeroSection E)))
  rw [preimage_mapFun_range_zeroSection]
  exact hasProperNeighbourhoodDeformations_pointsOver X (zeroLocus E σ).support

variable (R : Type) [CommRing R] {r : ℕ}
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E r]

variable (r) in
/-- **The localized top Chern class capped with a class** (Fulton, §19.1):
`a ↦ σ^*(u_ℰ) ∩ a : H_k X → H_{k-2r}(σ⁻¹(0(X(ℂ))))`, with `u_ℰ` the Thom class of `𝐕(ℰ)`. -/
def localizedTopChernCap (k : ℤ) :
    borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X)) k →ₗ[R]
      borelMooreHomology R (ModuleCat.of R R)
        (TopCat.of ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹'
          range (UnderlyingSpace.map (K := ℂ) (zeroSection E)))) (k - (2 * r : ℕ)) :=
  borelMooreHomology.capProductSupportPullback R
    (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)) isClosed_range_zeroSection
    (hasProperNeighbourhoodDeformations_preimage σ) _ k (thomClass R E r)

end MMP.Modules
