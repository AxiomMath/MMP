module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksNormalization
public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksLineSectionZero
public import MMP.AlgebraicGeometry.Chow.CycleClassPushforward
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.StacksEulerClass
public import MMP.AlgebraicTopology.PoincareDuality.AlexanderFiveLemma
public import MMP.AlgebraicTopology.SingularCohomology.Relative.Homotopy
public import StacksFrontier.AlgebraicGeometry.Chow.ChernComponent.ClassRule
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.InvertibleDual.SectionIdeal
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCap42.DivisorOfSectionCycle
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.CurveDeltaDimension
public import MMP.AlgebraicGeometry.SubschemeOver
public import MMP.AlgebraicGeometry.Chow.CycleClassFirstChernGeneric

/-!
# The cycle class of `c₁(L) ∩ α` (Fulton, Proposition 19.2, for line bundles)

Let `X` be a complex scheme. For a quasi-coherent `𝒪_X`-module `ℰ`, finite locally free of rank
one, the *topological first Chern class* of the line bundle `𝐕(ℰ)` is the pull-back
`c₁ᵗᵒᵖ(ℰ) = 0^* u_ℰ ∈ H²(X(ℂ); R)` of the Thom class `u_ℰ` along the zero section
(`MMP.Modules.topFirstChernClass`, defined in
`MMP.AlgebraicGeometry.Chow.CycleClassFirstChernGeneric`);
by `MMP.Modules.cast_eulerClass_eq_map_thomClass` it is the Euler class, i.e. the first Chern
class, of the complex line bundle `𝐕(ℰ)(ℂ) → X(ℂ)`. For an
invertible module `L` the line bundle is `𝐕(L^∨)`, whose sections are the sections of `L`
(`MMP.Modules.globalSectionMap`), and `c₁ᵗᵒᵖ(L) := c₁ᵗᵒᵖ(L^∨)` (`MMP.Chow.firstChernClassTop`).

Fulton's Proposition 19.2 for line bundles states `cl(c₁(L) ∩ α) = c₁ᵗᵒᵖ(L) ∩ cl(α)` in
`H_{2k}(X(ℂ))` for `α ∈ Z_{k+1}(X)`, with Stacks' cap product `c₁(L) ∩ α ∈ A_k(X)` (Tag 02SO,
`Stacks.Chow.firstChernClassCapOfInvertible`) and the cycle class map `MMP.Chow.cycleClass` on
Stacks' cycles (`MMP.Chow.CycleClassFirstChernFormula`).

## Main definitions

* `MMP.Chow.firstChernClassTop`, `MMP.Chow.firstChernClassTopCap`: `c₁ᵗᵒᵖ(L)` and
  `a ↦ c₁ᵗᵒᵖ(L) ∩ a : H_{2k+2}(X(ℂ)) → H_{2k}(X(ℂ))`.
* `MMP.Chow.CycleClassFirstChernFormula`: the statement of Fulton's Proposition 19.2 for `L`.

## Main results

* `MMP.Modules.toCohomology_pullback_thomClass`: for a section `σ` of `𝐕(ℰ)`, the localized
  class `σ^* u_ℰ`, with its supports forgotten, is `c₁ᵗᵒᵖ(ℰ)` (`σ` is homotopic to `0`).
* `MMP.Modules.pushforward_cycleClass_zeroLocus_of_formula`: Fulton 19.1.3 read in `X(ℂ)`: for
  a complex variety `X` of dimension `k + 1` and a section `σ` of `𝐕(ℰ)` satisfying 19.1.3,
  `ι_* cl([Z(σ)]_k) = c₁ᵗᵒᵖ(ℰ) ∩ cl(X)`; `MMP.Modules.pushforward_cycleClass_zeroLocus` for
  normal `X` and `σ ≠ 0`.
* `MMP.Chow.cycleClass_zeroScheme_eq_firstChernClassTopCap`: for a non-zero global section `t`
  of an invertible module `L` on a complex variety `X` of dimension `k + 1`,
  `cl_X([Z(t)]_k) = c₁ᵗᵒᵖ(L) ∩ cl(X)`, with Stacks' zero scheme `Z(t)` (Tag 02OQ).

## What is not proved here

`MMP.Chow.CycleClassFirstChernFormula` is stated here and proved in
`MMP.AlgebraicGeometry.Chow.FirstChernClassTopAdditive`
(`MMP.Chow.cycleClassFirstChernFormula_of_isAmple`), from the vanishing of the cycle class on
rationally trivial cycles (`MMP.AlgebraicGeometry.Chow.CycleClassDescent`), the naturality of
`c₁ᵗᵒᵖ` (`MMP.AlgebraicGeometry.Chow.FirstChernClassTopNatural`) and its additivity.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, Lemma 19.1.3, Proposition 19.2.
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set Bundle Stacks.Chow
open MMP.UnderlyingSpace

namespace MMP.Modules

variable (R : Type) [CommRing R] {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] (E : X.Modules)
  [E.IsQuasicoherent] [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E 1]

/-! ### A section is homotopic to the zero section -/

section Homotopy

variable {E} {σ : X ⟶ totalSpace E} [σ.IsOver (Spec (.of ℂ))]

/-- The vector `σ(x)` of the fibre over `x`, for a section `σ` of `𝐕(ℰ)`. -/
def sectionFibre (hσ : σ ≫ proj E = 𝟙 X) (x : UnderlyingSpace ℂ X) : Fibre E 1 x :=
  ⟨mapFun σ x, UnderlyingSpace.ext (by
    simp only [toHom_mapFun, Category.assoc, hσ, Category.comp_id])⟩

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E 1] in
/-- The section `x ↦ σ(x)` of `𝐕(ℰ)(ℂ)` given by a section `σ` of `𝐕(ℰ)` is continuous. -/
theorem continuous_sectionFibre (hσ : σ ≫ proj E = 𝟙 X) :
    Continuous fun x : UnderlyingSpace ℂ X ↦
      (⟨x, sectionFibre hσ x⟩ : TotalSpace (Fin 1 → ℂ) (Fibre E 1)) :=
  (isInducing_totalSpaceEquiv E 1).continuous_iff.2 (continuous_mapFun σ)

/-- Multiplying a continuous section of `𝐕(ℰ)(ℂ)` by a continuous function is continuous. -/
theorem continuous_totalSpaceMk_smul {T : Type*} [TopologicalSpace T] {c : T → ℂ}
    (hc : Continuous c) {s : T → UnderlyingSpace ℂ X} (hs : Continuous s)
    {v : ∀ t, Fibre E 1 (s t)}
    (hv : Continuous fun t ↦ (⟨s t, v t⟩ : TotalSpace (Fin 1 → ℂ) (Fibre E 1))) :
    Continuous fun t ↦ (⟨s t, c t • v t⟩ : TotalSpace (Fin 1 → ℂ) (Fibre E 1)) := by
  refine continuous_iff_continuousAt.2 fun t₀ ↦ ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨hs.continuousAt, ?_⟩
  set e := trivializationAt (Fin 1 → ℂ) (Fibre E 1) (s t₀)
  have hmem : ∀ᶠ t in nhds t₀, s t ∈ e.baseSet :=
    hs.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' (s t₀)))
  have heq : (fun t ↦ c t • (e ⟨s t, v t⟩).2) =ᶠ[nhds t₀]
      fun t ↦ (e ⟨s t, c t • v t⟩).2 :=
    hmem.mono fun t ht ↦ ((e.linear ℂ ht).map_smul (c t) (v t)).symm
  refine ContinuousAt.congr ?_ heq
  refine hc.continuousAt.smul ?_
  have h1 : ContinuousAt (fun t ↦ e ⟨s t, v t⟩) t₀ :=
    (e.continuousOn.continuousAt (e.open_source.mem_nhds
      ((e.mem_source).2 (FiberBundle.mem_baseSet_trivializationAt' (s t₀))))).comp
      hv.continuousAt
  exact continuous_snd.continuousAt.comp h1

/-- The homotopy `(t, x) ↦ (1 - t) σ(x)` from a section `σ` of `𝐕(ℰ)` to the zero section. -/
def sectionHomotopy (hσ : σ ≫ proj E = 𝟙 X) :
    TopCat.Homotopy (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)) (zeroSectionHom E) where
  toFun p := totalSpaceHomeomorph E 1 ⟨p.2, (((1 : ℝ) - p.1 : ℝ) : ℂ) • sectionFibre hσ p.2⟩
  continuous_toFun := (totalSpaceHomeomorph E 1).continuous.comp
    (continuous_totalSpaceMk_smul (Complex.continuous_ofReal.comp
      (continuous_const.sub (continuous_subtype_val.comp continuous_fst))) continuous_snd
      ((continuous_sectionFibre hσ).comp continuous_snd))
  map_zero_left x := by
    change (((((1 : ℝ) - 0 : ℝ) : ℂ) • sectionFibre hσ x : Fibre E 1 x).1) = mapFun σ x
    rw [sub_zero, Complex.ofReal_one, one_smul]
    rfl
  map_one_left x := by
    change (((((1 : ℝ) - 1 : ℝ) : ℂ) • sectionFibre hσ x : Fibre E 1 x).1) =
      mapFun (zeroSection E) x
    rw [sub_self, Complex.ofReal_zero, zero_smul]
    exact zero_fibre_val E x

/-- A section and the zero section induce the same map `H^j(𝐕(ℰ)(ℂ)) → H^j(X(ℂ))`. -/
theorem map_section_eq_map_zeroSection (hσ : σ ≫ proj E = 𝟙 X) (j : ℤ) :
    relativeSingularCohomology.map R (ModuleCat.of R R)
        (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ))
        (A' := (univᶜ : Set (TopCat.of (UnderlyingSpace ℂ X))))
        (A := (univᶜ : Set (TopCat.of (UnderlyingSpace ℂ (totalSpace E)))))
        (fun x hx ↦ (hx (mem_univ x)).elim) j =
      relativeSingularCohomology.map R (ModuleCat.of R R) (zeroSectionHom E)
        (fun x hx ↦ (hx (mem_univ x)).elim) j :=
  relativeSingularCohomology.map_eq_of_homotopy R (sectionHomotopy hσ)
    (fun y hy ↦ (hy (mem_univ y)).elim) _ _ j

/-- **The localized class of a section is the first Chern class**: for a section `σ` of
`𝐕(ℰ)`, the image in `H²(X(ℂ))` of `σ^* u_ℰ ∈ H²(X(ℂ), X(ℂ) - Z(σ)(ℂ))` is `c₁ᵗᵒᵖ(ℰ)`. -/
theorem toCohomology_pullback_thomClass (hσ : σ ≫ proj E = 𝟙 X) :
    (cohomologyWithSupports.toCohomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X))
        ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹'
          range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) ((2 * 1 : ℕ) : ℤ)).hom
      ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
        (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ))
        (range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) ((2 * 1 : ℕ) : ℤ)).hom
        (thomClass R E 1)) = topFirstChernClass R E := by
  let σH := TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)
  let V := TopCat.of (UnderlyingSpace ℂ (totalSpace E))
  let u := thomClass R E 1
  have hu : (univᶜ : Set V) ⊆ (𝟙 V) ⁻¹' (range (UnderlyingSpace.map (K := ℂ)
      (zeroSection E)))ᶜ := fun x hx ↦ (hx (mem_univ x)).elim
  calc _ = (relativeSingularCohomology.map R (ModuleCat.of R R) (𝟙 _ ≫ σH)
          (fun x hx ↦ (hx (mem_univ x)).elim) ((2 * 1 : ℕ) : ℤ)).hom u :=
        (relativeSingularCohomology.map_hom_comp_apply R (𝟙 _) σH _ _ _ _ u).symm
    _ = (relativeSingularCohomology.map R (ModuleCat.of R R) (σH ≫ 𝟙 V)
          (fun x hx ↦ (hx (mem_univ x)).elim) ((2 * 1 : ℕ) : ℤ)).hom u :=
        congrArg (fun φ ↦ ModuleCat.Hom.hom φ u)
          (relativeSingularCohomology.map_eq_map_of_hom_eq R
            ((Category.id_comp σH).trans (Category.comp_id σH).symm) _ _ _)
    _ = (relativeSingularCohomology.map R (ModuleCat.of R R) σH
          (A' := (univᶜ : Set (TopCat.of (UnderlyingSpace ℂ X)))) (A := (univᶜ : Set V))
          (fun x hx ↦ (hx (mem_univ x)).elim) ((2 * 1 : ℕ) : ℤ)).hom
          ((relativeSingularCohomology.map R (ModuleCat.of R R) (𝟙 V) hu
            ((2 * 1 : ℕ) : ℤ)).hom u) :=
        relativeSingularCohomology.map_hom_comp_apply R σH (𝟙 V) _ hu _ _ u
    _ = (relativeSingularCohomology.map R (ModuleCat.of R R) (zeroSectionHom E)
          (A' := (univᶜ : Set (TopCat.of (UnderlyingSpace ℂ X)))) (A := (univᶜ : Set V))
          (fun x hx ↦ (hx (mem_univ x)).elim) ((2 * 1 : ℕ) : ℤ)).hom
          ((relativeSingularCohomology.map R (ModuleCat.of R R) (𝟙 V) hu
            ((2 * 1 : ℕ) : ℤ)).hom u) := by
        rw [map_section_eq_map_zeroSection R hσ]
    _ = (relativeSingularCohomology.map R (ModuleCat.of R R) (zeroSectionHom E ≫ 𝟙 V)
          (A' := (univᶜ : Set (TopCat.of (UnderlyingSpace ℂ X))))
          (fun x hx ↦ (hx (mem_univ x)).elim) ((2 * 1 : ℕ) : ℤ)).hom u :=
        (relativeSingularCohomology.map_hom_comp_apply R (zeroSectionHom E) (𝟙 V) _ hu _ _ u).symm
    _ = topFirstChernClass R E :=
        congrArg (fun φ ↦ ModuleCat.Hom.hom φ u)
          (relativeSingularCohomology.map_eq_map_of_hom_eq R (Category.comp_id _) _ _ _)

end Homotopy

/-! ### Lemma 19.1.3 read in `X(ℂ)` -/

section Variety

variable {E} {σ : X ⟶ totalSpace E} [σ.IsOver (Spec (.of ℂ))]

/-- The localized cap `σ^*(u_ℰ) ∩ a`, read in `X(ℂ)`, is `c₁ᵗᵒᵖ(ℰ) ∩ a`. -/
theorem pushforward_subsetInclusion_localizedTopChernCap [IsComplexScheme X]
    (hσ : σ ≫ proj E = 𝟙 X) {m : ℕ}
    (a : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X)) m) :
    (borelMooreHomology.pushforward R (ModuleCat.of R R)
        (borelMooreHomology.subsetInclusion ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹'
          range (UnderlyingSpace.map (K := ℂ) (zeroSection E))))
        (borelMooreHomology.isProperMap_subsetInclusion
          (isClosed_range_zeroSection.preimage (continuous_mapFun σ))) (m - (2 * 1 : ℕ))).hom
        (localizedTopChernCap σ R 1 m a) =
      borelMooreHomology.capProduct R _ univ ((2 * 1 : ℕ) : ℤ) m (topFirstChernClass R E) a := by
  rw [localizedTopChernCap, borelMooreHomology.capProductSupportPullback_apply,
    borelMooreHomology.pushforward_subsetInclusion_capProductSupport,
    ← borelMooreHomology.capProduct_toCohomology, toCohomology_pullback_thomClass R hσ]

open scoped MMP.SubschemeOver in
/-- **Fulton's Lemma 19.1.3, read in `X(ℂ)`.** Let `X` be a complex variety of dimension `k + 1`,
`ℰ` a quasi-coherent `𝒪_X`-module, locally free of rank one, and `σ` a section of `𝐕(ℰ) ⟶ X`
with zero scheme `ι : D = Z(σ) ⟶ X`, for which Lemma 19.1.3 holds
(`MMP.Modules.LocalizedFirstChernFormula`). Then `ι_* cl_D([D]_k) = c₁ᵗᵒᵖ(ℰ) ∩ cl(X)` in
`H_{2k}(X(ℂ))`, for every fundamental class `cl(X)`. -/
theorem pushforward_cycleClass_zeroLocus_of_formula [IsComplexScheme X] [IsIntegral X]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] [QuasiCompact (X ↘ Spec (.of ℂ))]
    {k : ℕ} {hn : ((k + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim X} (hσ : σ ≫ proj E = 𝟙 X)
    (hF : LocalizedFirstChernFormula R hn E σ) {μ : borelMooreHomology R (ModuleCat.of R R)
      (TopCat.of (UnderlyingSpace ℂ X)) (2 * (k + 1) : ℕ)}
    (hμ : IsVarietyFundamentalClass R hn μ) :
    borelMooreHomology.pushforward R (ModuleCat.of R R)
        (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (zeroLocus E σ).subschemeι))
        (isProperMap_map (K := ℂ) _) (2 * k : ℕ)
        (Chow.cycleClass R k (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
          ((zeroLocus E σ).subscheme ↘ Spec (.of ℂ)) (𝟙 _) k)) =
      BorelMooreCross.congrDegree R _ (by push_cast; ring)
        (borelMooreHomology.capProduct R _ univ ((2 * 1 : ℕ) : ℤ) (2 * (k + 1) : ℕ)
          (topFirstChernClass R E) μ) := by
  have key := congrArg (borelMooreHomology.pushforward R (ModuleCat.of R R)
      (borelMooreHomology.subsetInclusion ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) (zeroSection E))))
      (borelMooreHomology.isProperMap_subsetInclusion
        (isClosed_range_zeroSection.preimage (continuous_mapFun σ))) (2 * k : ℕ)).hom
    (hF μ hμ)
  rw [borelMooreHomology.pushforward_congrDegree,
    pushforward_subsetInclusion_localizedTopChernCap R hσ,
    ← ModuleCat.comp_apply, ← borelMooreHomology.pushforward_comp] at key
  refine Eq.trans ?_ key
  exact congrArg (fun φ ↦ ModuleCat.Hom.hom φ _)
    (borelMooreHomology.pushforward_congr_hom R (ConcreteCategory.hom_ext _ _ fun p ↦ rfl) _ _ _)

open scoped MMP.SubschemeOver in
/-- **Fulton's Lemma 19.1.3, read in `X(ℂ)`, for a normal variety.** Let `X` be a normal complex
variety of dimension `k + 1`, `ℰ` a quasi-coherent `𝒪_X`-module, locally free of rank one, and `σ`
a section of `𝐕(ℰ) ⟶ X` other than the zero section, with zero scheme `ι : D = Z(σ) ⟶ X`. Then
`ι_* cl_D([D]_k) = c₁ᵗᵒᵖ(ℰ) ∩ cl(X)` in `H_{2k}(X(ℂ))`, for every fundamental class `cl(X)`. -/
theorem pushforward_cycleClass_zeroLocus [IsComplexScheme X] [IsIntegral X]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] [QuasiCompact (X ↘ Spec (.of ℂ))] [IsNormal X]
    {k : ℕ} (hn : ((k + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim X) (hσ : σ ≫ proj E = 𝟙 X)
    (h0 : σ ≠ zeroSection E) {μ : borelMooreHomology R (ModuleCat.of R R)
      (TopCat.of (UnderlyingSpace ℂ X)) (2 * (k + 1) : ℕ)}
    (hμ : IsVarietyFundamentalClass R hn μ) :
    borelMooreHomology.pushforward R (ModuleCat.of R R)
        (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (zeroLocus E σ).subschemeι))
        (isProperMap_map (K := ℂ) _) (2 * k : ℕ)
        (Chow.cycleClass R k (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
          ((zeroLocus E σ).subscheme ↘ Spec (.of ℂ)) (𝟙 _) k)) =
      BorelMooreCross.congrDegree R _ (by push_cast; ring)
        (borelMooreHomology.capProduct R _ univ ((2 * 1 : ℕ) : ℤ) (2 * (k + 1) : ℕ)
          (topFirstChernClass R E) μ) :=
  pushforward_cycleClass_zeroLocus_of_formula R hσ
    (LocalizedFirstChernFormula.of_isNormal R hn hσ h0) hμ

end Variety

end MMP.Modules

/-! ### Line bundles of invertible modules -/

namespace MMP.Chow

open MMP.Modules

variable (R : Type) [CommRing R] {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X]
  (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- **The topological first Chern class** `c₁ᵗᵒᵖ(L) ∈ H²(X(ℂ); R)` of an invertible module `L`
on a complex scheme: that of its line bundle `𝐕(L^∨)`, whose sections are the sections of `L`
(`MMP.Modules.globalSectionMap`). -/
def firstChernClassTop :
    cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X)) univ
      ((2 * 1 : ℕ) : ℤ) :=
  topFirstChernClass R (Scheme.Modules.dual L)

/-- `c₁ᵗᵒᵖ(L)` is the topological first Chern class of the line bundle `𝐕(L^∨)`. -/
theorem firstChernClassTop_def :
    firstChernClassTop R L = topFirstChernClass R (Scheme.Modules.dual L) := rfl

/-- The cap product `a ↦ c₁ᵗᵒᵖ(L) ∩ a : H_{2k+2}(X(ℂ)) → H_{2k}(X(ℂ))`. -/
def firstChernClassTopCap (k : ℕ) : BMHomology R X (2 * (k + 1)) →ₗ[R] BMHomology R X (2 * k) :=
  (BorelMooreCross.congrDegree R _ (by push_cast; ring)).toLinearMap ∘ₗ
    borelMooreHomology.capProduct R _ univ ((2 * 1 : ℕ) : ℤ) (2 * (k + 1) : ℕ)
      (firstChernClassTop R L)

/-- `firstChernClassTopCap R L k a` is the cap product `c₁ᵗᵒᵖ(L) ∩ a`, recast to degree `2 * k`. -/
theorem firstChernClassTopCap_apply (k : ℕ) (a : BMHomology R X (2 * (k + 1))) :
    firstChernClassTopCap R L k a =
      BorelMooreCross.congrDegree R _ (by push_cast; ring)
        (borelMooreHomology.capProduct R _ univ ((2 * 1 : ℕ) : ℤ) (2 * (k + 1) : ℕ)
          (firstChernClassTop R L) a) := rfl

/-- **The statement of Fulton's Proposition 19.2 for a line bundle, on Stacks cycles.** For every
`(k+1)`-cycle `α` on `X` and every `k`-cycle `β` representing Stacks' cap product
`c₁(L) ∩ α ∈ A_k(X)` (Tag 02SO, `Stacks.Chow.firstChernClassCapOfInvertible`),
`cl(β) = c₁ᵗᵒᵖ(L) ∩ cl(α)` in `H_{2k}(X(ℂ); R)`. -/
def CycleClassFirstChernFormula (k : ℕ) : Prop :=
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
    ‹Stacks.Ample.IsInvertibleModule X L›
  ∀ (α : CycleGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) ((k + 1 : ℕ) : ℤ))
    (β : CycleGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k),
    (QuotientAddGroup.mk β : chowGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k) =
        firstChernClassCapOfInvertible (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k L α →
      cycleClass R k β = firstChernClassTopCap R L k (cycleClass R (k + 1) α)

open scoped MMP.SubschemeOver in
/-- **The cycle class of the zero scheme of a section of a line bundle** (Fulton, Lemma 19.1.3
and Proposition 19.2, for `α = [X]` and `L` with a section). Let `X` be a complex variety
of dimension `k + 1`, `L` an invertible `𝒪_X`-module and `t ≠ 0` a global section of `L`, with
Stacks' zero scheme `Z(t)` (Tag 02OQ). Then `cl_X([Z(t)]_k) = c₁ᵗᵒᵖ(L) ∩ cl(X)` in
`H_{2k}(X(ℂ); R)`, for every fundamental class `cl(X)`. -/
theorem cycleClass_zeroScheme_eq_firstChernClassTopCap [IsIntegral X]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] [QuasiCompact (X ↘ Spec (.of ℂ))] {k : ℕ}
    (hn : ((k + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim X) (t : Γ(L, ⊤)) (ht : t ≠ 0)
    {μ : BMHomology R X (2 * (k + 1))} (hμ : IsVarietyFundamentalClass R hn μ) :
    have : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
      ‹Stacks.Ample.IsInvertibleModule X L›
    cycleClass R k (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
        (Stacks.Divisors.zeroScheme X L t).subschemeι k) =
      firstChernClassTopCap R L k μ := by
  intro _
  have hσ : globalSectionMap L t ≫ proj (Scheme.Modules.dual L) = 𝟙 X := globalSectionMap_proj L t
  have : (globalSectionMap L t).IsOver (Spec (.of ℂ)) :=
    ⟨by
      change globalSectionMap L t ≫ proj (Scheme.Modules.dual L) ≫ X ↘ Spec (.of ℂ) = _
      rw [← Category.assoc, hσ, Category.id_comp]⟩
  have key := pushforward_cycleClass_zeroLocus_of_formula R hσ
    (localizedFirstChernFormula R hn L t ht) hμ
  rw [← zeroLocus_globalSectionMap L t]
  set D := zeroLocus (Scheme.Modules.dual L) (globalSectionMap L t)
  have e := properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp
    (fieldChowSituation ℂ) (D.subscheme ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ)) D.subschemeι
    (comp_over _ _) (𝟙 _) k
  rw [cycleAssociatedToClosedSubscheme_congr (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) _ _
    (Category.id_comp D.subschemeι)] at e
  rw [← e, cycleClass_properPushforward]
  exact key

end MMP.Chow
