module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.ZeroSectionCycle.StacksAssemblyChart
public import MMP.AlgebraicTopology.OrientationClass.CapDeformation

/-!
# Fulton's Lemma 19.2(d): the Thom class on the bundle chart of `E|_V` (Stacks bundles)

Let `ℰ` be a quasi-coherent `𝒪_X`-module, finite locally free of rank `r`, on a complex scheme
`X`, with vector bundle `π : 𝐕(ℰ) ⟶ X`, `V` a subvariety of `X`, `ι : E|_V → 𝐕(ℰ)` the inclusion
of `E|_V = π⁻¹(V)`, and `Θ : P₀ ≅ B₀ × ℂʳ` the bundle chart of `E|_V` over an open set
`B₀ ⊆ V_reg(ℂ)` lying over the domain of a chart `c` of `ℰ` (`MMP.Modules.bundleChartHomeomorph`),
with second component `g = x^c ∘ ι : P₀ → ℂʳ`. On `P₀` the zero section `ι⁻¹(0(X(ℂ)))` is the
zero locus `g⁻¹(0)`, and the pull-back of the Thom class `u_ℰ` to `P₀` is the pull-back `g^* u₀`
of the local orientation class `u₀` of `ℂʳ` at `0` (`MMP.Modules.pullback_inclHom_thomClass`).

## Main definitions

* `MMP.Modules.bundleChartCoordHom`: `g = pr₂ ∘ Θ : P₀ → ℂʳ`.

## Main results

* `MMP.Modules.preimage_regularOpensInterHom_eq_preimage_zero`: the zero section of `E|_V` on
  `P₀` is `g⁻¹(0)`.
* `MMP.Modules.hasProperNeighbourhoodDeformations_preimage_inclHom`: the zero section of `E|_V`
  in the open set `π_V⁻¹(B₀)` has proper neighbourhood deformations.
* `MMP.Modules.pullback_regularOpensInterHom_pullback_thomClass`: `u_ℰ` pulled back to `P₀` is
  `g^* u₀`.

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
  [E.IsQuasicoherent] {r : ℕ}
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E r]
  [IsComplexScheme (totalSpace E)] {V : Subvariety X} {c : Chart E r}
  {B₀ : Opens (UnderlyingSpace ℂ V.toScheme)}
  (hB₀ : ∀ q ∈ B₀, q ∈ regularPart ℂ V.toScheme ∧ mapFun V.ι q ∈ chartBase c)

/-- The second component `g = x^c ∘ ι : P₀ → ℂʳ` of the bundle chart. -/
def bundleChartCoordHom :
    TopCat.of (BundleChartSource E r V B₀) ⟶ TopCat.of (Fin r → ℂ) :=
  TopCat.ofHom ⟨fun p ↦ (bundleChartHomeomorph hB₀ p).2,
    continuous_snd.comp (bundleChartHomeomorph hB₀).continuous⟩

/-- The value of `g` at `p` is the second component of `Θ p`. -/
@[simp]
lemma bundleChartCoordHom_apply (p : BundleChartSource E r V B₀) :
    bundleChartCoordHom hB₀ p = (bundleChartHomeomorph hB₀ p).2 :=
  rfl

include hB₀ in
/-- The open set `π_V⁻¹(B₀)` of `E|_V` lies in the regular part of `E|_V`. -/
lemma preimageProjOpens_subset_regularPart :
    (preimageProjOpens E r V B₀ : Set (UnderlyingSpace ℂ (preimageSubvariety E r V).toScheme)) ⊆
      regularPart ℂ (preimageSubvariety E r V).toScheme :=
  preimageProjOpens_le_regularOpens fun q hq ↦ (hB₀ q hq).1

include hB₀ in
/-- On `π_V⁻¹(B₀)`, a point lies on the zero section iff its chart coordinates vanish. -/
lemma mem_range_zeroSection_iff_coord_eq_zero_of_mem
    {p : UnderlyingSpace ℂ (preimageSubvariety E r V).toScheme}
    (hp : p ∈ preimageProjOpens E r V B₀) :
    mapFun (preimageSubvariety E r V).ι p ∈ range (UnderlyingSpace.map (K := ℂ) (zeroSection E)) ↔
      coord c (mapFun (preimageSubvariety E r V).ι p) = 0 :=
  mem_range_zeroSection_iff_coord_eq_zero c _
    (mem_chartTotalOpens_of_mem_preimageProjOpens hB₀ hp)

/-- **The zero section of `E|_V` on `P₀` is `g⁻¹(0)`.** -/
lemma preimage_regularOpensInterHom_eq_preimage_zero :
    (regularOpensInterHom _ (preimageProjOpens_subset_regularPart hB₀)).hom ⁻¹'
      ((inclHom (Z := TopCat.of (UnderlyingSpace ℂ (preimageSubvariety E r V).toScheme))
        (preimageProjOpens E r V B₀)).hom ⁻¹'
        ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (preimageSubvariety E r V).ι)).hom ⁻¹'
          range (UnderlyingSpace.map (K := ℂ) (zeroSection E)))) =
      bundleChartCoordHom hB₀ ⁻¹' {0} := by
  ext p
  exact mem_range_zeroSection_iff_coord_eq_zero_of_mem hB₀ p.2

include hB₀ in
/-- The zero section of `E|_V` in the open set `π_V⁻¹(B₀)` has arbitrarily small proper
neighbourhood deformations: it is the zero locus of the second component of the bundle chart. -/
theorem hasProperNeighbourhoodDeformations_preimage_inclHom :
    HasProperNeighbourhoodDeformations
      ((inclHom (Z := TopCat.of (UnderlyingSpace ℂ (preimageSubvariety E r V).toScheme))
        (preimageProjOpens E r V B₀)).hom ⁻¹'
        ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (preimageSubvariety E r V).ι)).hom ⁻¹'
          range (UnderlyingSpace.map (K := ℂ) (zeroSection E)))) := by
  have h := (hasProperNeighbourhoodDeformations_preimage_zero_of_eq_snd
    (bundleChartHomeomorph hB₀) (bundleChartCoordHom hB₀) fun _ ↦ rfl).preimage_homeomorph
      (regularOpensInterHomeomorph _ (preimageProjOpens_subset_regularPart hB₀)).symm
  convert h using 1
  ext p
  exact mem_range_zeroSection_iff_coord_eq_zero_of_mem hB₀ p.2

variable (R : Type) [CommRing R]

/-- **The Thom class on the bundle chart.** The pull-back of the Thom class `u_ℰ` to
`P₀ ⊆ E|_V(ℂ)`, along `P₀ → π_V⁻¹(B₀) → E|_V(ℂ) → 𝐕(ℰ)(ℂ)`, is the pull-back `g^* u₀` of the local
orientation class `u₀ ∈ H^{2r}(ℂʳ, ℂʳ - 0)` along the second component `g` of the bundle chart. -/
theorem pullback_regularOpensInterHom_pullback_thomClass
    {u₀ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (Fin r → ℂ)) {0} (2 * r : ℕ)}
    (hu₀ : IsLocalOrientationClass R (complexOrientationBasis r) (0 : TopCat.of (Fin r → ℂ)) u₀)
    (hg : ((regularOpensInterHom _ (preimageProjOpens_subset_regularPart hB₀)).hom ⁻¹'
      ((inclHom (Z := TopCat.of (UnderlyingSpace ℂ (preimageSubvariety E r V).toScheme))
        (preimageProjOpens E r V B₀)).hom ⁻¹'
        ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (preimageSubvariety E r V).ι)).hom ⁻¹'
          range (UnderlyingSpace.map (K := ℂ) (zeroSection E)))))ᶜ ⊆
      bundleChartCoordHom hB₀ ⁻¹' ({0}ᶜ : Set (TopCat.of (Fin r → ℂ)))) :
    (cohomologyWithSupports.pullback R (ModuleCat.of R R)
        (regularOpensInterHom _ (preimageProjOpens_subset_regularPart hB₀)) _ (2 * r : ℕ)).hom
      ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
        (inclHom (Z := TopCat.of (UnderlyingSpace ℂ (preimageSubvariety E r V).toScheme))
          (preimageProjOpens E r V B₀)) _ (2 * r : ℕ)).hom
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
          (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (preimageSubvariety E r V).ι))
          (range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) (2 * r : ℕ)).hom
          (thomClass R E r))) =
      (relativeSingularCohomology.map R (ModuleCat.of R R) (bundleChartCoordHom hB₀) hg
        (2 * r : ℕ)).hom u₀ := by
  let jP := regularOpensInterHom _ (preimageProjOpens_subset_regularPart hB₀)
  let inc := inclHom (Z := TopCat.of (UnderlyingSpace ℂ (preimageSubvariety E r V).toScheme))
    (preimageProjOpens E r V B₀)
  let ιt := TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (preimageSubvariety E r V).ι)
  let kP : TopCat.of (BundleChartSource E r V B₀) ⟶ TopCat.of (chartTotalOpens c) :=
    TopCat.ofHom ⟨fun p ↦ ⟨mapFun (preimageSubvariety E r V).ι p.1.1,
      mem_chartTotalOpens_of_mem_preimageProjOpens hB₀ p.2⟩,
      ((continuous_mapFun _).comp
        (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _⟩
  have hfac : jP ≫ inc ≫ ιt = kP ≫ inclHom (chartTotalOpens c) :=
    ConcreteCategory.hom_ext _ _ fun _ ↦ rfl
  have hk : kP ≫ chartCoordHom c = bundleChartCoordHom hB₀ :=
    ConcreteCategory.hom_ext _ _ fun _ ↦ rfl
  have h1 : (cohomologyWithSupports.pullback R (ModuleCat.of R R) jP _ (2 * r : ℕ)).hom
      ((cohomologyWithSupports.pullback R (ModuleCat.of R R) inc _ (2 * r : ℕ)).hom
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R) ιt
          (range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) (2 * r : ℕ)).hom
          (thomClass R E r))) =
      (cohomologyWithSupports.pullback R (ModuleCat.of R R) (jP ≫ inc ≫ ιt)
        (range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) (2 * r : ℕ)).hom
        (thomClass R E r) := by
    rw [cohomologyWithSupports.pullback_comp, cohomologyWithSupports.pullback_comp]
    rfl
  have h2 := congrArg (fun φ ↦ ModuleCat.Hom.hom φ (thomClass R E r))
    (relativeSingularCohomology.map_eq_map_of_hom_eq R hfac
      (A' := ((jP ≫ inc ≫ ιt) ⁻¹' range (UnderlyingSpace.map (K := ℂ) (zeroSection E)))ᶜ)
      (A := (range (UnderlyingSpace.map (K := ℂ) (zeroSection E)))ᶜ)
      (fun ⦃_⦄ hx ↦ hx) (fun ⦃_⦄ hx ↦ hx) (2 * r : ℕ))
  have h3 := relativeSingularCohomology.map_hom_comp_apply R kP (inclHom (chartTotalOpens c))
    (A'' := ((jP ≫ inc ≫ ιt) ⁻¹' range (UnderlyingSpace.map (K := ℂ) (zeroSection E)))ᶜ)
    (A' := ((inclHom (chartTotalOpens c)).hom ⁻¹'
      range (UnderlyingSpace.map (K := ℂ) (zeroSection E)))ᶜ)
    (A := (range (UnderlyingSpace.map (K := ℂ) (zeroSection E)))ᶜ)
    (fun ⦃_⦄ hx ↦ hx) (fun ⦃_⦄ hx ↦ hx) (fun ⦃_⦄ hx ↦ hx) (2 * r : ℕ) (thomClass R E r)
  have h4 := pullback_inclHom_thomClass R c hu₀
  have h5 := relativeSingularCohomology.map_hom_comp_apply R kP (chartCoordHom c)
    (A'' := ((jP ≫ inc ≫ ιt) ⁻¹' range (UnderlyingSpace.map (K := ℂ) (zeroSection E)))ᶜ)
    (A' := ((inclHom (chartTotalOpens c)).hom ⁻¹'
      range (UnderlyingSpace.map (K := ℂ) (zeroSection E)))ᶜ)
    (fun ⦃_⦄ hx ↦ hx) (compl_preimage_inclHom_subset_chartCoordHom c)
    (fun ⦃_⦄ hx ↦ compl_preimage_inclHom_subset_chartCoordHom c hx) (2 * r : ℕ) u₀
  have h6 := congrArg (fun φ ↦ ModuleCat.Hom.hom φ u₀)
    (relativeSingularCohomology.map_eq_map_of_hom_eq R hk
      (fun ⦃_⦄ hx ↦ compl_preimage_inclHom_subset_chartCoordHom c hx) hg (2 * r : ℕ))
  exact h1.trans (h2.trans (h3.trans ((congrArg _ h4).trans (h5.symm.trans h6))))

end MMP.Modules
