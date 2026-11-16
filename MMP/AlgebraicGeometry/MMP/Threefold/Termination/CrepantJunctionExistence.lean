module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldStabilizedTail
import MMP.AlgebraicGeometry.MMP.Threefold.Flip.FloorProgramInputs
import MMP.AlgebraicGeometry.MMP.MinimalModel.SpecifiedExtraction
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv

/-!
# Existence of crepant junctions

For an effective rational klt pair `(X, B)` on a normal projective complex threefold and a finite
set `I` of valuations in the low-discrepancy set, a crepant junction of `(X, B)` extracting `I`
exists.

## Main results

* `MMP.Fourfold.CrepantJunction.nonempty`: a crepant junction of `(X, B)` extracting `I` exists.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Fourfold MMP.Mori

namespace MMP.Fold06.LemMmpIndexcJunctionExists

/-- In a klt pair every valuation with a log discrepancy has positive log discrepancy. -/
private lemma IsKltPair.pos_of_isValuationLogDiscrepancy {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X}
    (hklt : IsKltPair sX B) {ξ : Valuation X.functionField (WithZero (Multiplicative ℤ))} {a : ℝ}
    (ha : IsValuationLogDiscrepancy sX B ξ a) : 0 < a :=
  let ⟨n, D, _, _, hD⟩ := ha
  hklt.2 n D a hD

private theorem solution : ∀ {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X}
    {I : Finset (Valuation X.functionField (WithZero (Multiplicative ℤ)))}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hdim : topologicalKrullDim X = 3)
    (hB : 0 ≤ B) (hklt : IsKltPair sX B) (hI : (I : Set _) ⊆ lowDiscrepancySet sX B),
    Nonempty (CrepantJunction sX B I) := by
  intro X _ _ _ sX B I hX hdim hB hklt hI
  obtain ⟨Y, _, _, _, p, hp, hV, E, ΔV, hpproj, hval, hinj, hexc, -, -, hdisc⟩ :=
    projectiveFloorProgramInputs_three.exists_crepant_extraction sX hX (by rw [hdim]; rfl) hklt I
      fun s hs ↦ let ⟨hex, a, ha, ha1⟩ := hI hs
        ⟨hex, a, ha, IsKltPair.pos_of_isValuationLogDiscrepancy hklt ha, ha1⟩
  haveI : AlgebraicGeometry.IsVariety ℂ (p ≫ sX) := hV.1.1
  haveI : AlgebraicGeometry.IsVariety ℂ sX := hX.toIsVariety
  exact ⟨{
    Y := Y
    p := p
    E := E
    Θ := inverseTransformDivisor p B + ∑ s : I, Finsupp.single (E s) (1 - (1 - ΔV.coeff (E s)))
    isProjectiveVariety_base := hX
    dim_base := hdim
    isKltPair := hklt
    subset_lowDiscrepancySet := hI
    isProjectiveVariety := ⟨hpproj.comp hX.isProjective⟩
    isQFactorial := hV
    dim_eq := by
      rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (p ≫ sX) hp, hdim]
    isProjectiveMorphism := hpproj
    isBirationalMorphism := hp
    valuation_eq := hval
    injective := hinj
    isExceptional_iff := hexc
    Θ_eq := ⟨fun s ↦ 1 - ΔV.coeff (E s), fun s ↦ by push_cast; exact hdisc s, rfl⟩ }⟩

end MMP.Fold06.LemMmpIndexcJunctionExists

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

/-- **Crepant junctions exist.** Let `(X, B)` be an effective rational klt pair on a normal
projective complex threefold and `I` a finite subset of the low-discrepancy set
`MMP.Fourfold.lowDiscrepancySet sX B`. Then a crepant junction of `(X, B)` extracting `I`
exists. -/
@[mmp "lem_mmp_indexc_junction_exists"]
public theorem CrepantJunction.nonempty {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X}
    {I : Finset (Valuation X.functionField (WithZero (Multiplicative ℤ)))}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hdim : topologicalKrullDim X = 3)
    (hB : 0 ≤ B) (hklt : IsKltPair sX B) (hI : (I : Set _) ⊆ lowDiscrepancySet sX B) :
    Nonempty (CrepantJunction sX B I) :=
  MMP.Fold06.LemMmpIndexcJunctionExists.solution hX hdim hB hklt hI
