module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.ZeroSectionCycle.StacksTransport

/-!
# Fulton's Lemma 19.2(d) for a Stacks vector bundle: the zero section of `E|_V` is `V`

Let `ℰ` be a quasi-coherent `𝒪_X`-module, finite locally free of rank `r`, on a complex scheme
`X`, with vector bundle `π : 𝐕(ℰ) ⟶ X`, `V` a subvariety of `X` and
`ι : E|_V = π⁻¹(V) → 𝐕(ℰ)` the inclusion (`MMP.Modules.preimageSubvariety`). The map
`f' : ι⁻¹(0(X(ℂ))) → 0(X(ℂ)) ≅ X(ℂ)` (`MMP.Modules.zeroSectionPreimageHom`) is a closed
embedding onto `V(ℂ) ⊆ X(ℂ)`; it is therefore `V.ι ∘ h` for a homeomorphism
`h : ι⁻¹(0(X(ℂ))) ≅ V(ℂ)`, and `MMP.Modules.ZeroSectionCapFormula` follows from:
`h_*(ι^* u_ℰ ∩ c)` is a fundamental class of `V`.

## Main definitions

* `MMP.Modules.zeroSectionPreimageHomeomorph`: `h : ι⁻¹(0(X(ℂ))) ≅ V(ℂ)`.

## Main results

* `MMP.Modules.range_zeroSectionPreimageHom`: `f'(ι⁻¹(0(X(ℂ)))) = V(ℂ)`.
* `MMP.Modules.zeroSectionCapFormula_of_isVarietyFundamentalClass`: `ZeroSectionCapFormula`
  from the fundamental class statement on `V`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set Topology
open MMP.UnderlyingSpace

namespace MMP.Modules

open MMP.Intersection.Scheme

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X] (E : X.Modules)
  [E.IsQuasicoherent] (r : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E r]
  (V : Subvariety X)

/-- `f'(p)` is the image under `zeroSectionHomeomorph` of the point `f(p)` of `0(X(ℂ))`. -/
lemma coe_zeroSectionPreimageHom_apply {Y : Scheme.{0}} [Y.Over (Spec (.of ℂ))]
    (f : Y ⟶ totalSpace E) [f.IsOver (Spec (.of ℂ))] (p) :
    zeroSectionPreimageHom E f p = zeroSectionHomeomorph E ⟨mapFun f p.1, p.2⟩ :=
  rfl

/-- `f' : ι⁻¹(0(X(ℂ))) → X(ℂ)` is an embedding. -/
theorem isEmbedding_zeroSectionPreimageHom {Y : Scheme.{0}} [Y.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))] (f : Y ⟶ totalSpace E) [f.IsOver (Spec (.of ℂ))]
    [IsClosedImmersion f] : IsEmbedding (zeroSectionPreimageHom E f) :=
  (zeroSectionHomeomorph E).isEmbedding.comp
    ((isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) f).isEmbedding.restrictPreimage _)

/-- **The zero section of `E|_V` is `V`**: the image of `f' : ι⁻¹(0(X(ℂ))) → X(ℂ)` is `V(ℂ)`,
for `ι` the inclusion of `π⁻¹(V)`. -/
theorem range_zeroSectionPreimageHom :
    range (zeroSectionPreimageHom E (preimageSubvariety E r V).ι) =
      range (mapFun (K := ℂ) V.ι) := by
  have hW : range (mapFun (K := ℂ) (preimageSubvariety E r V).ι) =
      pointsOver (K := ℂ) ((proj E).base ⁻¹' (V.support : Set X)) := by
    rw [range_mapFun_of_isClosedImmersion, Subvariety.ι,
      Scheme.IdealSheafData.range_subschemeι, ← coe_support_preimageSubvariety E r V]
    rfl
  have hV : range (mapFun (K := ℂ) V.ι) = pointsOver (K := ℂ) (V.support : Set X) := by
    rw [range_mapFun_of_isClosedImmersion, Subvariety.ι, Scheme.IdealSheafData.range_subschemeι]
    rfl
  have e (y : UnderlyingSpace ℂ X) : (y.toHom ≫ zeroSection E) ≫ proj E = y.toHom := by
    rw [Category.assoc, zeroSection_proj, Category.comp_id]
  rw [hV]
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    set y := zeroSectionHomeomorph E ⟨mapFun (preimageSubvariety E r V).ι p.1, p.2⟩ with hy
    have h0 : mapFun (zeroSection E) y = mapFun (preimageSubvariety E r V).ι p.1 :=
      map_zeroSection_zeroSectionHomeomorph E _
    have hp : mapFun (preimageSubvariety E r V).ι p.1 ∈
        pointsOver (K := ℂ) ((proj E).base ⁻¹' (V.support : Set X)) := hW ▸ mem_range_self _
    rw [← h0, mem_pointsOver, toHom_mapFun] at hp
    rw [coe_zeroSectionPreimageHom_apply, ← hy, mem_pointsOver]
    have hp' : ((y.toHom ≫ zeroSection E) ≫ proj E) (IsLocalRing.closedPoint ℂ) ∈
        (V.support : Set X) := hp
    rwa [e] at hp'
  · intro hx
    have hx' : mapFun (zeroSection E) x ∈
        range (mapFun (K := ℂ) (preimageSubvariety E r V).ι) := by
      rw [hW, mem_pointsOver, toHom_mapFun]
      change ((x.toHom ≫ zeroSection E) ≫ proj E) (IsLocalRing.closedPoint ℂ) ∈
        (V.support : Set X)
      rwa [e]
    obtain ⟨p, hp⟩ := hx'
    exact ⟨⟨p, ⟨x, hp.symm⟩⟩,
      (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) (zeroSection E)).injective
        ((map_zeroSection_zeroSectionHomeomorph E _).trans hp)⟩

variable [IsComplexScheme (totalSpace E)]

/-- The homeomorphism `h : ι⁻¹(0(X(ℂ))) ≅ V(ℂ)` with `V.ι ∘ h = f'`, for `ι` the inclusion of
`π⁻¹(V)` and `f' = zeroSectionPreimageHom ι`. -/
def zeroSectionPreimageHomeomorph :
    (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (preimageSubvariety E r V).ι)).hom ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) (zeroSection E)) ≃ₜ UnderlyingSpace ℂ V.toScheme :=
  homeomorphOfRangeEq (isEmbedding_zeroSectionPreimageHom E _)
    (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) V.ι).isEmbedding
    (range_zeroSectionPreimageHom E r V)

/-- `h : ι⁻¹(0(X(ℂ))) ≅ V(ℂ)` as a morphism of spaces. -/
def zeroSectionPreimageHomeomorphHom :
    TopCat.of ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (preimageSubvariety E r V).ι)).hom ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) ⟶
      TopCat.of (UnderlyingSpace ℂ V.toScheme) :=
  TopCat.ofHom ⟨zeroSectionPreimageHomeomorph E r V,
    (zeroSectionPreimageHomeomorph E r V).continuous⟩

/-- `V.ι ∘ h = f'`, for `f' = zeroSectionPreimageHom ι`. -/
lemma zeroSectionPreimageHomeomorphHom_comp :
    zeroSectionPreimageHomeomorphHom E r V ≫ TopCat.ofHom (UnderlyingSpace.map (K := ℂ) V.ι) =
      zeroSectionPreimageHom E (preimageSubvariety E r V).ι :=
  ConcreteCategory.hom_ext _ _ fun p ↦
    apply_homeomorphOfRangeEq (isEmbedding_zeroSectionPreimageHom E _)
      (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) V.ι).isEmbedding
      (range_zeroSectionPreimageHom E r V) p

variable (R : Type) [CommRing R]

/-- **`ZeroSectionCapFormula` from the fundamental class statement on `V`.** If for every
fundamental class `c` of `E|_V`, the class `h_*(ι^* u_ℰ ∩ c) ∈ H_{2m} V` is a fundamental class
of `V` (`h : ι⁻¹(0(X(ℂ))) ≅ V(ℂ)`), then `f'_*(ι^* u_ℰ ∩ c)` is the cycle class of `V`. -/
theorem zeroSectionCapFormula_of_isVarietyFundamentalClass {m : ℕ}
    {hV : (m : WithBot ℕ∞) = dimension V.toScheme}
    {hW : ((m + r : ℕ) : WithBot ℕ∞) = dimension (preimageSubvariety E r V).toScheme}
    (h : ∀ c, IsVarietyFundamentalClass R hW c →
      IsVarietyFundamentalClass R hV
        (BorelMooreCross.congrDegree R _ (two_mul_add_sub_two_mul m r)
          (borelMooreHomology.pushforward R (ModuleCat.of R R)
            (zeroSectionPreimageHomeomorphHom E r V)
            (zeroSectionPreimageHomeomorph E r V).isProperMap _
            (borelMooreHomology.capProductSupportPullback R
              (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (preimageSubvariety E r V).ι))
              isClosed_range_zeroSection
              (hasProperNeighbourhoodDeformations_preimage_range_zeroSection E _)
              ((2 * r : ℕ) : ℤ) ((2 * (m + r) : ℕ) : ℤ) (thomClass R E r) c)))) :
    ZeroSectionCapFormula E R r V hV hW := fun c hc ↦
  ⟨_, h c hc, pushforward_congrDegree_pushforward R _ _ _
    (zeroSectionPreimageHomeomorphHom_comp E r V) _ _ _ _ _⟩

end MMP.Modules
