module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.ZeroSectionCycle.StacksPreimageSubvariety
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.RegularPartComplement
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.PointsOver
public import MMP.AlgebraicTopology.ThomClass.OfRank
public import MMP.AlgebraicTopology.CapProduct.SupportLemmas
public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.ZeroSectionCycle.ChartAlgebra
public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksSection
public import MMP.AlgebraicGeometry.Chow.CycleClass

/-!
# Fulton's Lemma 19.2(d) for a Stacks vector bundle: the transport by the projection formula

Let `ℰ` be a quasi-coherent `𝒪_X`-module, finite locally free of rank `r`, on a complex scheme
`X`, with vector bundle `π : 𝐕(ℰ) ⟶ X` (`MMP.Modules.totalSpace`, `MMP.Modules.proj`), zero
section `0 : X ⟶ 𝐕(ℰ)` and Thom class `u_ℰ ∈ H^{2r}(𝐕(ℰ)(ℂ), 𝐕(ℰ)(ℂ) - 0(X(ℂ)))`
(`MMP.Modules.thomClass`). The zero section identifies `0(X(ℂ)) ⊆ 𝐕(ℰ)(ℂ)` with `X(ℂ)`, so the
cap product `u_ℰ ∩ a` of `a ∈ H_k 𝐕(ℰ)` is a class of `H_{k-2r} X`.

For a proper morphism `f : Y → 𝐕(ℰ)` and `c ∈ H_k Y`, the projection formula gives
`u_ℰ ∩ f_* c = f'_*(f^* u_ℰ ∩ c)`, with `f' : f⁻¹(0(X(ℂ))) → 0(X(ℂ)) ≅ X(ℂ)`. Applied to the
inclusion of `E|_V = π⁻¹(V)` (`MMP.Modules.preimageSubvariety`) for a subvariety `V ⊆ X`, this
reduces `u_ℰ ∩ cl(E|_V) = cl_X(V)` to the statement on `E|_V` itself.

## Main definitions

* `MMP.Modules.zeroSectionHomeomorph`: the homeomorphism `0(X(ℂ)) ≅ X(ℂ)`.
* `MMP.Modules.zeroSectionInvHom`: it, as a morphism of spaces.
* `MMP.Modules.zeroSectionPreimageHom`: `f⁻¹(0(X(ℂ))) → X(ℂ)` for a morphism `f : Y → 𝐕(ℰ)`.
* `MMP.Modules.ZeroSectionCapFormula`: the statement `f'_*(f^* u_ℰ ∩ cl(E|_V)) = cl_X(V)` on
  `E|_V = π⁻¹(V)`, for a subvariety `V` of `X`.

## Main results

* `MMP.Modules.hasProperNeighbourhoodDeformations_range_zeroSection`.
* `MMP.Modules.pushforward_zeroSectionInvHom_capProductSupport_pushforward`:
  `u ∩ f_* c = f'_*(f^* u ∩ c)` in `H_* X`.
* `MMP.Modules.isCycleClass_pushforward_capProductSupport_of_zeroSectionCapFormula`:
  `u_ℰ ∩ cl(E|_V) = cl_X(V)`, from the statement on `E|_V`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.2, Lemma 19.2(d).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set
open MMP.UnderlyingSpace

namespace MMP.Modules

open MMP.Intersection.Scheme

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] (E : X.Modules) [E.IsQuasicoherent]

/-- The zero section `0(X(ℂ))` of `𝐕(ℰ)(ℂ)` has arbitrarily small proper neighbourhood
deformations. -/
theorem hasProperNeighbourhoodDeformations_range_zeroSection [IsComplexScheme (totalSpace E)] :
    HasProperNeighbourhoodDeformations (range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) := by
  rw [range_map_of_isClosedImmersion]
  exact hasProperNeighbourhoodDeformations_pointsOver (totalSpace E)
    ⟨range (zeroSection E).base, (zeroSection E).isClosedEmbedding.isClosed_range⟩

/-- For a morphism `f : Y → 𝐕(ℰ)` over `ℂ` from a complex scheme, `f⁻¹(0(X(ℂ)))` has arbitrarily
small proper neighbourhood deformations in `Y(ℂ)`. -/
theorem hasProperNeighbourhoodDeformations_preimage_range_zeroSection {Y : Scheme.{0}}
    [Y.Over (Spec (.of ℂ))] [IsComplexScheme Y] (f : Y ⟶ totalSpace E)
    [f.IsOver (Spec (.of ℂ))] :
    HasProperNeighbourhoodDeformations
      ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) f)).hom ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) := by
  have h : (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) f)).hom ⁻¹'
      range (UnderlyingSpace.map (K := ℂ) (zeroSection E)) =
      pointsOver (K := ℂ) (f.base ⁻¹' range (zeroSection E).base) := by
    rw [range_map_of_isClosedImmersion]
    rfl
  rw [h]
  exact hasProperNeighbourhoodDeformations_pointsOver Y
    ⟨_, (zeroSection E).isClosedEmbedding.isClosed_range.preimage f.base.hom.continuous⟩

variable [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]

/-- The homeomorphism `0(X(ℂ)) ≅ X(ℂ)`, inverse to the zero section. -/
def zeroSectionHomeomorph :
    range (UnderlyingSpace.map (K := ℂ) (zeroSection E)) ≃ₜ UnderlyingSpace ℂ X :=
  (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ)
    (zeroSection E)).isEmbedding.toHomeomorph.symm

/-- The zero section sends `zeroSectionHomeomorph E p` back to `p`. -/
lemma map_zeroSection_zeroSectionHomeomorph
    (p : range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) :
    UnderlyingSpace.map (K := ℂ) (zeroSection E) (zeroSectionHomeomorph E p) = p := by
  have := (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ)
    (zeroSection E)).isEmbedding.toHomeomorph.apply_symm_apply p
  exact congrArg Subtype.val this

/-- The homeomorphism `0(X(ℂ)) ≅ X(ℂ)`, as a morphism of spaces. -/
def zeroSectionInvHom :
    TopCat.of (range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) ⟶
      TopCat.of (UnderlyingSpace ℂ X) :=
  TopCat.ofHom ⟨zeroSectionHomeomorph E, (zeroSectionHomeomorph E).continuous⟩

/-- The map `zeroSectionInvHom E : 0(X(ℂ)) → X(ℂ)` is proper. -/
lemma isProperMap_zeroSectionInvHom : IsProperMap (zeroSectionInvHom E) :=
  (zeroSectionHomeomorph E).isProperMap

/-- The map `f⁻¹(0(X(ℂ))) → 0(X(ℂ)) ≅ X(ℂ)` induced by a morphism `f : Y → 𝐕(ℰ)`. -/
def zeroSectionPreimageHom {Y : Scheme.{0}} [Y.Over (Spec (.of ℂ))] (f : Y ⟶ totalSpace E)
    [f.IsOver (Spec (.of ℂ))] :
    TopCat.of ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) f)).hom ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) ⟶
      TopCat.of (UnderlyingSpace ℂ X) :=
  TopCat.ofHom ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) f)).hom.restrictPreimage
    (range (UnderlyingSpace.map (K := ℂ) (zeroSection E)))) ≫ zeroSectionInvHom E

/-- For a proper morphism `f : Y → 𝐕(ℰ)`, the map `f⁻¹(0(X(ℂ))) → X(ℂ)` is proper. -/
lemma isProperMap_zeroSectionPreimageHom [LocallyOfFiniteType (totalSpace E ↘ Spec (.of ℂ))]
    {Y : Scheme.{0}} [Y.Over (Spec (.of ℂ))] [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
    (f : Y ⟶ totalSpace E) [f.IsOver (Spec (.of ℂ))] [IsProper f] :
    IsProperMap (zeroSectionPreimageHom E f) :=
  (isProperMap_zeroSectionInvHom E).comp ((isProperMap_map (K := ℂ) f).restrictPreimage _)

/-- **The transport by the projection formula** (Fulton, proof of Lemma 19.2(d)). For a proper
morphism `f : Y → 𝐕(ℰ)` over `ℂ` from a complex scheme, `c ∈ H^j(𝐕(ℰ)(ℂ), 𝐕(ℰ)(ℂ) - 0(X(ℂ)))`
and `a ∈ H_k Y`, the cap product `c ∩ f_* a ∈ H_{k-j}(0(X(ℂ)))`, read in `H_{k-j} X`, is
`f'_*(f^* c ∩ a)`, where `f' : f⁻¹(0(X(ℂ))) → X(ℂ)` (`zeroSectionPreimageHom`). -/
theorem pushforward_zeroSectionInvHom_capProductSupport_pushforward (R : Type) [CommRing R]
    [IsComplexScheme (totalSpace E)] {Y : Scheme.{0}} [Y.Over (Spec (.of ℂ))]
    [IsComplexScheme Y] (f : Y ⟶ totalSpace E) [f.IsOver (Spec (.of ℂ))] [IsProper f]
    (j k : ℤ)
    (c : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ (totalSpace E)))
      (range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) j)
    (a : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ Y)) k) :
    borelMooreHomology.pushforward R (ModuleCat.of R R) (zeroSectionInvHom E)
        (isProperMap_zeroSectionInvHom E) (k - j)
        (borelMooreHomology.capProductSupport R _ isClosed_range_zeroSection
          (hasProperNeighbourhoodDeformations_range_zeroSection E) j k c
          (borelMooreHomology.pushforward R (ModuleCat.of R R)
            (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) f)) (isProperMap_map (K := ℂ) f) k a)) =
      borelMooreHomology.pushforward R (ModuleCat.of R R) (zeroSectionPreimageHom E f)
        (isProperMap_zeroSectionPreimageHom E f) (k - j)
        (borelMooreHomology.capProductSupportPullback R
          (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) f)) isClosed_range_zeroSection
          (hasProperNeighbourhoodDeformations_preimage_range_zeroSection E f) j k c a) := by
  rw [← borelMooreHomology.pushforward_restrictPreimage_capProductSupportPullback R
    (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) f)) (isProperMap_map (K := ℂ) f)
    isClosed_range_zeroSection (hasProperNeighbourhoodDeformations_range_zeroSection E)
    (hasProperNeighbourhoodDeformations_preimage_range_zeroSection E f) j k c a]
  exact borelMooreHomology.pushforward_comp_apply R _ _
    ((isProperMap_map (K := ℂ) f).restrictPreimage _) (isProperMap_zeroSectionInvHom E)
    (isProperMap_zeroSectionPreimageHom E f) _ _

/-! ### The cycle class of `V`, from the statement on `E|_V` -/

section CycleForm

variable (R : Type) [CommRing R] (r : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E r]
  [IsComplexScheme X] [IsComplexScheme (totalSpace E)]

/-- The statement `f'_*(f^* u_ℰ ∩ cl(E|_V)) = cl_X(V)` on `E|_V = π⁻¹(V)` (Fulton, proof of
Lemma 19.2(d): "it suffices to show `u_{N|_V} ∩ cl(N|_V) = cl(V)` in `H_{2v} V`"). Let `V` be an
`m`-dimensional subvariety of `X`, `ι : E|_V → 𝐕(ℰ)` the inclusion of the `(m + r)`-dimensional
subvariety `π⁻¹(V)`, and `f' : ι⁻¹(0(X(ℂ))) → X(ℂ)` (`zeroSectionPreimageHom`); the formula
says that for every fundamental class `c` of `E|_V`, the class `f'_*(ι^* u_ℰ ∩ c) ∈ H_{2m} X` is
the cycle class of `V`. -/
def ZeroSectionCapFormula (V : Subvariety X) {m : ℕ}
    (hV : (m : WithBot ℕ∞) = dimension V.toScheme)
    (hW : ((m + r : ℕ) : WithBot ℕ∞) = dimension (preimageSubvariety E r V).toScheme) : Prop :=
  ∀ c, IsVarietyFundamentalClass R hW c →
    IsCycleClassOf R V.ι hV
      (BorelMooreCross.congrDegree R _ (two_mul_add_sub_two_mul m r)
        (borelMooreHomology.pushforward R (ModuleCat.of R R)
          (zeroSectionPreimageHom E (preimageSubvariety E r V).ι)
          (isProperMap_zeroSectionPreimageHom E _) _
          (borelMooreHomology.capProductSupportPullback R
            (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (preimageSubvariety E r V).ι))
            isClosed_range_zeroSection
            (hasProperNeighbourhoodDeformations_preimage_range_zeroSection E _)
            ((2 * r : ℕ) : ℤ) ((2 * (m + r) : ℕ) : ℤ) (thomClass R E r) c)))

/-- **`u_ℰ ∩ cl(E|_V) = cl_X(V)`, from the statement on `E|_V`** (Fulton, proof of
Lemma 19.2(d)). If `ZeroSectionCapFormula` holds for the `m`-dimensional subvariety `V` of `X`,
then for every cycle class `a = cl(π⁻¹(V)) ∈ H_{2(m+r)} 𝐕(ℰ)` of `π⁻¹(V) = E|_V`, the cap
product `u_ℰ ∩ a ∈ H_{2m}(0(X(ℂ)))`, read in `H_{2m} X`, is the cycle class of `V`. -/
theorem isCycleClass_pushforward_capProductSupport_of_zeroSectionCapFormula (V : Subvariety X)
    {m : ℕ} {hV : (m : WithBot ℕ∞) = dimension V.toScheme}
    {hW : ((m + r : ℕ) : WithBot ℕ∞) = dimension (preimageSubvariety E r V).toScheme}
    (h : ZeroSectionCapFormula E R r V hV hW)
    {a : borelMooreHomology R (ModuleCat.of R R)
      (TopCat.of (UnderlyingSpace ℂ (totalSpace E))) (2 * (m + r) : ℕ)}
    (ha : IsCycleClassOf R (preimageSubvariety E r V).ι hW a) :
    IsCycleClassOf R V.ι hV
      (BorelMooreCross.congrDegree R _ (two_mul_add_sub_two_mul m r)
        (borelMooreHomology.pushforward R (ModuleCat.of R R) (zeroSectionInvHom E)
          (isProperMap_zeroSectionInvHom E) _
          (borelMooreHomology.capProductSupport R _ isClosed_range_zeroSection
            (hasProperNeighbourhoodDeformations_range_zeroSection E)
            ((2 * r : ℕ) : ℤ) ((2 * (m + r) : ℕ) : ℤ) (thomClass R E r) a))) := by
  obtain ⟨c, hc, rfl⟩ := ha
  rw [pushforward_zeroSectionInvHom_capProductSupport_pushforward E R]
  exact h c hc

end CycleForm

end MMP.Modules
