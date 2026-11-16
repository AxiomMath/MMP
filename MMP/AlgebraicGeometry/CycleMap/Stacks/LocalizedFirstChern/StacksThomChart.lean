module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksSection
public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.ThomChartGeneric

/-!
# The Thom class of a Stacks vector bundle in a chart (Fulton, §19.1)

Let `ℰ` be a quasi-coherent `𝒪_X`-module, finite locally free of rank `r`, on a scheme `X` over
`ℂ`, with vector bundle `π : 𝐕(ℰ) ⟶ X`, and let `c = (V, b)` be a chart of `ℰ`
(`MMP.Modules.Chart`), with coordinates `x^c : π⁻¹V(ℂ) → ℂʳ` (`MMP.Modules.coord`). The map
`(π, x^c) : π⁻¹V(ℂ) → V(ℂ) × ℂʳ` is a homeomorphism onto the trivial bundle
(`MMP.Modules.chartHomeomorph`), carrying the zero section to `V(ℂ) × 0` and the complex frames of
`𝐕(ℰ)` to those of the trivial bundle. Both the restriction of the Thom class `u_ℰ` and the
pull-back `(x^c)^* u₀` of the local orientation class `u₀ ∈ H^{2r}(ℂʳ, ℂʳ - 0)` are therefore Thom
classes of the trivial bundle, and they agree by Thom's theorem: `u_ℰ|_{π⁻¹V(ℂ)} = (x^c)^* u₀`.

For `r = 1` and a section `σ : X ⟶ 𝐕(ℰ)` (`σ ≫ π = 𝟙`), with local coordinate
`h = x^c ∘ σ` on an open `O ⊆ V(ℂ)`, this gives `σ^*(u_ℰ)|_O = h^* u₀` in `H²(O, O - h⁻¹(0))` for
the local orientation class `u₀ ∈ H²(ℂ, ℂ - 0)`; if `h = g^m`, then `h^* u₀ = m · g^* u₀`, since
`z ↦ z^m` has degree `m`. These are steps of the proof of Fulton's Lemma 19.1.3.

## Main definitions

* `MMP.Modules.chartTotalOpens c`: the open set `π⁻¹V(ℂ)` of `𝐕(ℰ)(ℂ)`.
* `MMP.Modules.chartCoordHom c`: the chart coordinates `x^c : π⁻¹V(ℂ) → ℂʳ`;
  `MMP.Modules.lineChartCoordHom c`: the chart coordinate `π⁻¹V(ℂ) → ℂ` for `r = 1`.
* `MMP.Modules.chartPointHom c`, `MMP.Modules.chartTrivialHom c`: the chart
  `π⁻¹V(ℂ) ≅ V(ℂ) × ℂʳ` and its inverse.
* `MMP.Modules.chartRestrictHom`: a section restricted to an open `O ⊆ V(ℂ)`, as a map
  `O → π⁻¹V(ℂ)`.

## Main results

* `MMP.Modules.pullback_inclHom_thomClass`: `u_ℰ|_{π⁻¹V(ℂ)} = (x^c)^* u₀`.
* `MMP.Modules.pullback_inclHom_thomClass_eq_lineChartCoordHom`: the same for `r = 1`, with
  `u₀ ∈ H²(ℂ, ℂ - 0)`.
* `MMP.Modules.preimage_inclHom_preimage_range_zeroSection`: `O ∩ σ⁻¹(0(X(ℂ))) = h⁻¹(0)`.
* `MMP.Modules.pullback_inclHom_pullback_thomClass`: `σ^*(u_ℰ)|_O = h^* u₀`.
* `MMP.Modules.pullback_inclHom_pullback_thomClass_eq_smul`: `σ^*(u_ℰ)|_O = m · g^* u₀` when
  `h = g^m`.

## Implementation notes

The local coordinate of a section `σ` on `O ⊆ V(ℂ)` is the function `p ↦ (x^c(σ(p)))₀`; the
results take a map `h : O → ℂ` with `h p = coord c (mapFun σ p) 0` for all `p`.

The bundle-agnostic lemmas (`MMP.relativeSingularCohomology.map_eq_smul_of_eq_pow`,
`MMP.IsLocalOrientationClass.map_linearEquiv`, …) are those of
`MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.ThomChartGeneric`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, proof of Lemma 19.1.3.
* [J. Milnor, J. Stasheff, *Characteristic classes*][milnorstasheff1974], Thm. 10.4.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set Finsupp

namespace MMP.Modules

open UnderlyingSpace ThomClass SingularChain SingularCochain FundamentalClass

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] {E : X.Modules} [E.IsQuasicoherent] {r : ℕ}

/-! ### The chart `π⁻¹V(ℂ) ≅ V(ℂ) × ℂʳ` -/

/-- The open set `π⁻¹V(ℂ)` of `𝐕(ℰ)(ℂ)`: the points lying over the domain `V` of a chart. -/
def chartTotalOpens (c : Chart E r) :
    TopologicalSpace.Opens (TopCat.of (UnderlyingSpace ℂ (totalSpace E))) :=
  ⟨mapFun (proj E) ⁻¹' chartBase c, (isOpen_chartBase c).preimage (continuous_mapFun _)⟩

/-- A point `p` lies in `π⁻¹V(ℂ)` iff `p` factors through `π⁻¹(V)`. -/
lemma mem_chartTotalOpens_iff (c : Chart E r) (p : UnderlyingSpace ℂ (totalSpace E)) :
    p ∈ chartTotalOpens c ↔ ⊤ ≤ p.toHom ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1) :=
  Iff.rfl

/-- The chart coordinates `x^c : π⁻¹V(ℂ) → ℂʳ`, as a morphism of spaces. -/
def chartCoordHom (c : Chart E r) :
    TopCat.of (chartTotalOpens c) ⟶ TopCat.of (Fin r → ℂ) :=
  TopCat.ofHom ⟨fun p ↦ coord c p.1,
    (continuousOn_coord c).comp_continuous continuous_subtype_val fun p ↦ p.2⟩

/-- `chartCoordHom c` sends `p` to its chart coordinates `coord c p`. -/
lemma chartCoordHom_apply (c : Chart E r) (p : chartTotalOpens c) :
    chartCoordHom c p = coord c p.1 :=
  rfl

/-- A point of `π⁻¹V(ℂ)` lies on the zero section iff its chart coordinates vanish. -/
lemma mem_range_zeroSection_iff_coord_eq_zero (c : Chart E r)
    (p : UnderlyingSpace ℂ (totalSpace E)) (hp : p ∈ chartTotalOpens c) :
    p ∈ range (UnderlyingSpace.map (K := ℂ) (zeroSection E)) ↔ coord c p = 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    exact coord_mapFun_zeroSection E c y
  · intro h
    refine ⟨mapFun (proj E) p, ?_⟩
    change mapFun (zeroSection E) (mapFun (proj E) p) = p
    have hz : mapFun (zeroSection E) (mapFun (proj E) p) ∈ chartTotalOpens c := by
      change mapFun (proj E) (mapFun (zeroSection E) (mapFun (proj E) p)) ∈ chartBase c
      rw [mapFun_proj_mapFun_zeroSection]
      exact hp
    exact congrArg Subtype.val <| (chartHomeomorph c).injective (a₁ := ⟨_, hz⟩) (a₂ := ⟨p, hp⟩)
      (Prod.ext (Subtype.ext (mapFun_proj_mapFun_zeroSection E _))
        ((coord_mapFun_zeroSection E c _).trans h.symm))

/-- The zero section of `𝐕(ℰ)(ℂ)` meets `π⁻¹V(ℂ)` in the zero locus of the chart coordinates. -/
lemma preimage_inclHom_range_zeroSection (c : Chart E r) :
    (borelMooreHomology.inclHom (chartTotalOpens c)).hom ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) (zeroSection E)) =
      chartCoordHom c ⁻¹' {0} := by
  ext p
  exact mem_range_zeroSection_iff_coord_eq_zero c p.1 p.2

/-- The complement of the zero section in `π⁻¹V(ℂ)` is carried by the chart coordinates into
`ℂʳ - 0`. -/
lemma compl_preimage_inclHom_subset_chartCoordHom (c : Chart E r) :
    ((borelMooreHomology.inclHom (chartTotalOpens c)).hom ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) (zeroSection E)))ᶜ ⊆
      chartCoordHom c ⁻¹' ({0}ᶜ : Set (TopCat.of (Fin r → ℂ))) := by
  rw [preimage_inclHom_range_zeroSection]
  exact fun _ h ↦ h

/-- The trivial bundle `V(ℂ) × ℂʳ` over the domain of a chart. -/
abbrev ChartTrivialTotal (c : Chart E r) : Type :=
  Bundle.TotalSpace (Fin r → ℂ) (Bundle.Trivial (chartBase c) (Fin r → ℂ))

/-- The inverse `(x, w) ↦ chartInv c x w` of the chart, from the trivial bundle `V(ℂ) × ℂʳ` to
`π⁻¹V(ℂ)`. -/
def chartPointHom (c : Chart E r) :
    TopCat.of (ChartTrivialTotal c) ⟶ TopCat.of (chartTotalOpens c) :=
  TopCat.ofHom ⟨fun z ↦ ⟨chartInv c z.proj.1 z.proj.2 z.2, chartInv_mem c z.proj.1 z.proj.2 z.2⟩,
    ((continuous_chartInv c).comp
      (Bundle.Trivial.homeomorphProd (chartBase c) (Fin r → ℂ)).continuous).subtype_mk _⟩

/-- The point `chartPointHom c z` of `𝐕(ℰ)(ℂ)` is `chartInv c x w` for `z = (x, w)`. -/
lemma coe_chartPointHom_apply (c : Chart E r) (z : ChartTrivialTotal c) :
    ((chartPointHom c z : chartTotalOpens c) : UnderlyingSpace ℂ (totalSpace E)) =
      chartInv c z.proj.1 z.proj.2 z.2 :=
  rfl

/-- The chart `p ↦ (π p, x^c(p))`, from `π⁻¹V(ℂ)` to the trivial bundle `V(ℂ) × ℂʳ`. -/
def chartTrivialHom (c : Chart E r) :
    TopCat.of (chartTotalOpens c) ⟶ TopCat.of (ChartTrivialTotal c) :=
  TopCat.ofHom ⟨fun p ↦ Bundle.TotalSpace.mk' (Fin r → ℂ)
      (⟨mapFun (proj E) p.1, p.2⟩ : chartBase c) (coord c p.1),
    (Bundle.Trivial.homeomorphProd (chartBase c) (Fin r → ℂ)).symm.continuous.comp
      ((((continuous_mapFun (proj E)).comp continuous_subtype_val).subtype_mk _).prodMk
        (chartCoordHom c).hom.continuous)⟩

/-- `chartPointHom c` is a left inverse of `chartTrivialHom c`. -/
lemma chartTrivialHom_chartPointHom (c : Chart E r) :
    chartTrivialHom c ≫ chartPointHom c = 𝟙 _ := by
  refine ConcreteCategory.hom_ext _ _ fun p ↦ Subtype.ext ?_
  exact chartInv_mapFun_proj_coord c p.1 p.2

/-- `chartPointHom c` carries the complement of the zero section of `V(ℂ) × ℂʳ` into the
complement of the zero section in `π⁻¹V(ℂ)`. -/
lemma compl_range_zeroSection_subset_chartPointHom (c : Chart E r) :
    (range (Bundle.zeroSection (Fin r → ℂ) (Bundle.Trivial (chartBase c) (Fin r → ℂ))))ᶜ ⊆
      chartPointHom c ⁻¹' ((borelMooreHomology.inclHom (chartTotalOpens c)).hom ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) (zeroSection E)))ᶜ := by
  intro z hz h
  rw [preimage_inclHom_range_zeroSection] at h
  have h0 : z.2 = 0 := (coord_chartInv c z.proj.1 z.proj.2 z.2).symm.trans h
  exact hz ⟨z.proj, by rw [Bundle.zeroSection, ← h0]⟩

/-- `chartTrivialHom c` carries the complement of the zero section in `π⁻¹V(ℂ)` into the
complement of the zero section of `V(ℂ) × ℂʳ`. -/
lemma compl_preimage_inclHom_subset_chartTrivialHom (c : Chart E r) :
    ((borelMooreHomology.inclHom (chartTotalOpens c)).hom ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) (zeroSection E)))ᶜ ⊆
      chartTrivialHom c ⁻¹'
        (range (Bundle.zeroSection (Fin r → ℂ) (Bundle.Trivial (chartBase c) (Fin r → ℂ))))ᶜ := by
  rintro p hp ⟨x, hx⟩
  apply hp
  rw [preimage_inclHom_range_zeroSection]
  exact (congrArg Bundle.TotalSpace.snd hx).symm

/-! ### The Thom class in a chart -/

variable (R : Type) [CommRing R]

/-- The restriction of the Thom class `u_ℰ` to `π⁻¹V(ℂ)`, transported along the chart to the
trivial bundle `V(ℂ) × ℂʳ`, is a Thom class of the trivial bundle. -/
lemma isThomClassOfRank_map_chartPointHom_thomClass
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E r] (c : Chart E r) :
    IsThomClassOfRank (Fin r → ℂ) (Bundle.Trivial (chartBase c) (Fin r → ℂ)) r
      ((relativeSingularCohomology.map R (ModuleCat.of R R) (chartPointHom c)
        (compl_range_zeroSection_subset_chartPointHom c) (2 * r : ℕ)).hom
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
          (borelMooreHomology.inclHom (chartTotalOpens c))
          (range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) (2 * r : ℕ)).hom
          (Modules.thomClass R E r))) := by
  set F := Fin r → ℂ
  intro x ψ v hv
  let ψ' : (Fin r → ℂ) ≃L[ℂ] (Fin r → ℂ) := ψ
  let L : (Fin r → ℂ) ≃ₗ[ℂ] (Fin r → ℂ) := ψ'.toLinearEquiv
  let A : Matrix.GeneralLinearGroup (Fin r) ℂ :=
    ⟨LinearMap.toMatrix' L.toLinearMap, LinearMap.toMatrix' L.symm.toLinearMap,
      by rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_symm, LinearMap.toMatrix'_id],
      by rw [← LinearMap.toMatrix'_comp, LinearEquiv.symm_comp, LinearMap.toMatrix'_id]⟩
  have hcont : Continuous fun w : Fin r → ℂ ↦ chartInv c x.1 x.2 (ψ' w) :=
    (continuous_chartInv c).comp (f := fun w : Fin r → ℂ ↦
      ((⟨x.1, x.2⟩ : {x : UnderlyingSpace ℂ X // ⊤ ≤ x.toHom ⁻¹ᵁ c.1.1}), ψ' w))
      (continuous_const.prodMk ψ'.continuous)
  let f : C(Fin r → ℂ, UnderlyingSpace ℂ (totalSpace E)) :=
    ⟨fun w ↦ chartInv c x.1 x.2 (ψ' w), hcont⟩
  have hf : IsComplexFrame E r f := ⟨x.1, c, A, x.2, fun w ↦ ⟨mapFun_proj_chartInv _ _ _ _, by
    change coord c (chartInv c x.1 x.2 (ψ' w)) = _
    refine (coord_chartInv c x.1 x.2 _).trans ?_
    rw [LinearMap.toMatrix'_mulVec]
    rfl⟩⟩
  have hσ : (borelMooreHomology.inclHom (chartTotalOpens c)).hom.comp
      ((chartPointHom c).hom.comp (fibreSimplex F x ψ v)) = f.comp (affineSimplex v) :=
    ContinuousMap.ext fun _ ↦ rfl
  have hbd : ∀ t : stdSimplex ℝ (Fin (2 * r + 1)), (∃ k, t k = 0) →
      f (affineSimplex v t) ∈ (range (UnderlyingSpace.map (K := ℂ) (zeroSection E)))ᶜ :=
    fun t ht ↦ hf.notMem_range_zeroSection (hv.affineSimplex_ne_zero t ht)
  have hbd' : ∀ t : stdSimplex ℝ (Fin (2 * r + 1)), (∃ k, t k = 0) →
      (chartPointHom c).hom.comp (fibreSimplex F x ψ v) t ∈
        ((borelMooreHomology.inclHom (chartTotalOpens c)).hom ⁻¹'
          range (UnderlyingSpace.map (K := ℂ) (zeroSection E)))ᶜ := fun t ht h ↦
    hbd t ht (DFunLike.congr_fun hσ t ▸ h)
  rw [relEval_single_map (chartPointHom c) _ _ _
    (eval_single_eq_zero_of_mem_relCoboundaries _ hbd')]
  refine Eq.trans (relEval_single_map (R := R)
    (borelMooreHomology.inclHom (chartTotalOpens c)) (fun _ hx ↦ hx) _ _
    (by rw [hσ]; exact eval_single_eq_zero_of_mem_relCoboundaries _ fun t ht ↦ hbd t ht)
    (Modules.thomClass R E r)) ?_
  refine (LinearMap.congr_fun (relEval_congr (by rw [hσ]) _
    (eval_single_eq_zero_of_mem_relCoboundaries _ fun t ht ↦ hbd t ht)) _).trans ?_
  exact Modules.isThomClass_thomClass R E r f hf v hv

/-- The pull-back `(x^c)^* u₀` of a local orientation class, transported along the chart to the
trivial bundle `V(ℂ) × ℂʳ`, is a Thom class of the trivial bundle. -/
lemma isThomClassOfRank_map_chartPointHom_map_chartCoordHom (c : Chart E r)
    {u₀ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (Fin r → ℂ)) {0} (2 * r : ℕ)}
    (hu₀ : IsLocalOrientationClass R (complexOrientationBasis r) (0 : TopCat.of (Fin r → ℂ))
      u₀) :
    IsThomClassOfRank (Fin r → ℂ) (Bundle.Trivial (chartBase c) (Fin r → ℂ)) r
      ((relativeSingularCohomology.map R (ModuleCat.of R R) (chartPointHom c)
        (compl_range_zeroSection_subset_chartPointHom c) (2 * r : ℕ)).hom
        ((relativeSingularCohomology.map R (ModuleCat.of R R) (chartCoordHom c)
          (compl_preimage_inclHom_subset_chartCoordHom c) (2 * r : ℕ)).hom u₀)) := by
  set F := Fin r → ℂ
  intro x ψ v hv
  obtain ⟨α, hα, hc, hrep⟩ := hu₀
  have hα1 : ∀ w : Fin (2 * r + 1) → (Fin r → ℂ),
      IsOrientedSimplexAroundZero (complexOrientationBasis r) w →
        SingularCochain.eval α (single (affineSimplex w) 1) = 1 := fun w hw ↦ by
    have h := hc.2 (_root_.chartAt (Fin r → ℂ) (0 : TopCat.of (Fin r → ℂ)))
      (chart_mem_atlas _ _) (mem_chart_source _ _) w (by simpa [chartAt_self_eq] using hw)
      (by simp [chartAt_self_eq])
    convert h using 3
    ext1 t
    simp [chartSimplexOf_apply, chartAt_self_eq]
  let ψ' : (Fin r → ℂ) ≃L[ℂ] (Fin r → ℂ) := ψ
  have hσ : (chartCoordHom c).hom.comp ((chartPointHom c).hom.comp (fibreSimplex F x ψ v)) =
      (ψ' : C(Fin r → ℂ, Fin r → ℂ)).comp (affineSimplex v) :=
    ContinuousMap.ext fun _ ↦ coord_chartInv c _ _ _
  have hbd : ∀ t : stdSimplex ℝ (Fin (2 * r + 1)), (∃ k, t k = 0) →
      (ψ' : C(Fin r → ℂ, Fin r → ℂ)).comp (affineSimplex v) t ∈
        ({0}ᶜ : Set (TopCat.of (Fin r → ℂ))) :=
    fun t ht h ↦ hv.affineSimplex_ne_zero t ht (ψ'.map_eq_zero_iff.1 h)
  have hbd' : ∀ t : stdSimplex ℝ (Fin (2 * r + 1)), (∃ k, t k = 0) →
      (chartPointHom c).hom.comp (fibreSimplex F x ψ v) t ∈
        ((borelMooreHomology.inclHom (chartTotalOpens c)).hom ⁻¹'
          range (UnderlyingSpace.map (K := ℂ) (zeroSection E)))ᶜ := fun t ht h ↦ by
    rw [preimage_inclHom_range_zeroSection] at h
    refine hbd t ht ?_
    rw [← hσ]
    exact h
  rw [relEval_single_map (chartPointHom c) _ _ _
    (eval_single_eq_zero_of_mem_relCoboundaries _ hbd'), relEval_single_map _ _ _ _
    (by rw [hσ]; exact eval_single_eq_zero_of_mem_relCoboundaries _ hbd)]
  refine (LinearMap.congr_fun (relEval_congr (by rw [hσ]) _
    (eval_single_eq_zero_of_mem_relCoboundaries _ hbd)) _).trans ?_
  rw [hrep, relEval_mk]
  exact eval_comp_affineSimplex_eq_one hα1 ψ' hv

/-- **The Thom class in a chart**: the restriction of the Thom class `u_ℰ` to `π⁻¹V(ℂ)` is the
pull-back `(x^c)^* u₀` of the local orientation class `u₀ ∈ H^{2r}(ℂʳ, ℂʳ - 0)` along the chart
coordinates, as classes in `H^{2r}(π⁻¹V(ℂ), π⁻¹V(ℂ) - 0(X(ℂ)))` (the zero section is the zero
locus of `x^c` there, `MMP.Modules.preimage_inclHom_range_zeroSection`). -/
theorem pullback_inclHom_thomClass
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E r] (c : Chart E r)
    {u₀ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (Fin r → ℂ)) {0} (2 * r : ℕ)}
    (hu₀ : IsLocalOrientationClass R (complexOrientationBasis r) (0 : TopCat.of (Fin r → ℂ))
      u₀) :
    (cohomologyWithSupports.pullback R (ModuleCat.of R R)
        (borelMooreHomology.inclHom (chartTotalOpens c))
        (range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) (2 * r : ℕ)).hom
        (Modules.thomClass R E r) =
      (relativeSingularCohomology.map R (ModuleCat.of R R) (chartCoordHom c)
        (compl_preimage_inclHom_subset_chartCoordHom c) (2 * r : ℕ)).hom u₀ := by
  set Φ := relativeSingularCohomology.map R (ModuleCat.of R R) (chartPointHom c)
    (compl_range_zeroSection_subset_chartPointHom c) (2 * r : ℕ)
  suffices h : Φ.hom ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
      (borelMooreHomology.inclHom (chartTotalOpens c))
        (range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) (2 * r : ℕ)).hom
          (Modules.thomClass R E r)) =
      Φ.hom ((relativeSingularCohomology.map R (ModuleCat.of R R) (chartCoordHom c)
        (compl_preimage_inclHom_subset_chartCoordHom c) (2 * r : ℕ)).hom u₀) by
    rw [← relativeSingularCohomology.map_map_of_comp_eq_id R _ _
        (chartTrivialHom_chartPointHom c) (compl_preimage_inclHom_subset_chartTrivialHom c)
        (compl_range_zeroSection_subset_chartPointHom c) _ (cohomologyWithSupports.pullback R
          (ModuleCat.of R R) (borelMooreHomology.inclHom (chartTotalOpens c)) _ (2 * r : ℕ)
            |>.hom (Modules.thomClass R E r)),
      h, relativeSingularCohomology.map_map_of_comp_eq_id]
    exact chartTrivialHom_chartPointHom c
  refine (existsUnique_isThomClassOfRank (R := R) (Fin r → ℂ)
    (Bundle.Trivial (chartBase c) (Fin r → ℂ)) (Module.finrank_fin_fun ℂ)).unique
      (isThomClassOfRank_map_chartPointHom_thomClass R c)
      (isThomClassOfRank_map_chartPointHom_map_chartCoordHom R c hu₀)

/-! ### Rank one -/

section line

/-- The chart coordinate `p ↦ (x^c(p))₀` of a rank-one bundle, `π⁻¹V(ℂ) → ℂ`. -/
def lineChartCoordHom (c : Chart E 1) : TopCat.of (chartTotalOpens c) ⟶ TopCat.of ℂ :=
  chartCoordHom c ≫
    TopCat.ofHom (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℂ : C(Fin 1 → ℂ, ℂ))

/-- `lineChartCoordHom c` sends `p` to the coordinate `coord c p 0`. -/
lemma lineChartCoordHom_apply (c : Chart E 1) (p : chartTotalOpens c) :
    lineChartCoordHom c p = coord c p.1 0 :=
  rfl

/-- The zero section of a rank-one bundle meets `π⁻¹V(ℂ)` in the zero locus of the chart
coordinate. -/
lemma preimage_inclHom_range_zeroSection_eq_lineChartCoordHom (c : Chart E 1) :
    (borelMooreHomology.inclHom (chartTotalOpens c)).hom ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) (zeroSection E)) =
      lineChartCoordHom c ⁻¹' {0} := by
  rw [preimage_inclHom_range_zeroSection]
  ext p
  change coord c p.1 = 0 ↔ coord c p.1 0 = 0
  exact ⟨fun h ↦ by rw [h]; rfl, fun h ↦ funext fun a ↦ by rw [Subsingleton.elim a 0]; exact h⟩

/-- For a rank-one bundle, the complement of the zero section in `π⁻¹V(ℂ)` is carried by the
chart coordinate into `ℂ - 0`. -/
lemma compl_preimage_inclHom_subset_lineChartCoordHom (c : Chart E 1) :
    ((borelMooreHomology.inclHom (chartTotalOpens c)).hom ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) (zeroSection E)))ᶜ ⊆
      lineChartCoordHom c ⁻¹' ({0}ᶜ : Set (TopCat.of ℂ)) := by
  rw [preimage_inclHom_range_zeroSection_eq_lineChartCoordHom]
  exact fun _ h ↦ h

/-- **The Thom class of a rank-one bundle in a chart**: the restriction of `u_ℰ` to `π⁻¹V(ℂ)` is
the pull-back of the local orientation class `u₀ ∈ H²(ℂ, ℂ - 0)` (for the orientation `1, i`)
along the chart coordinate `p ↦ (x^c(p))₀`. -/
theorem pullback_inclHom_thomClass_eq_lineChartCoordHom
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E 1] (c : Chart E 1)
    {u₀ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of ℂ) {0} (2 : ℕ)}
    (hu₀ : IsLocalOrientationClass R Complex.basisOneI (0 : TopCat.of ℂ) u₀) :
    (cohomologyWithSupports.pullback R (ModuleCat.of R R)
        (borelMooreHomology.inclHom (chartTotalOpens c))
        (range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) (2 * 1 : ℕ)).hom
        (Modules.thomClass R E 1) =
      (relativeSingularCohomology.map R (ModuleCat.of R R) (lineChartCoordHom c)
        (compl_preimage_inclHom_subset_lineChartCoordHom c) (2 : ℕ)).hom u₀ := by
  set e : (Fin 1 → ℂ) ≃L[ℝ] ℂ := ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℂ
  have he : 0 < Complex.basisOneI.det ((e : (Fin 1 → ℂ) →ₗ[ℝ] ℂ) ∘ complexOrientationBasis 1) := by
    have : ((e : (Fin 1 → ℂ) →ₗ[ℝ] ℂ) ∘ complexOrientationBasis 1) = ⇑Complex.basisOneI := by
      rw [← complexOrientationBasis_one_map]
      funext k
      rfl
    rw [this, Module.Basis.det_self]
    exact one_pos
  have hu₁ := IsLocalOrientationClass.map_linearEquiv (bE := complexOrientationBasis 1) e he hu₀
  refine (pullback_inclHom_thomClass R c hu₁).trans ?_
  exact (relativeSingularCohomology.map_hom_comp_apply R (chartCoordHom c) _
    (compl_preimage_inclHom_subset_chartCoordHom c)
    (compl_zero_subset_preimage_ofHom_linearEquiv e) _ _ u₀).symm

end line

/-! ### Sections of rank-one bundles -/

section Section

variable (σ : X ⟶ totalSpace E) [σ.IsOver (Spec (.of ℂ))]

/-- The projection of the point `σ(x)` of a section is `x`. -/
lemma mapFun_proj_mapFun_of_comp_eq_id (hσ : σ ≫ proj E = 𝟙 X) (x : UnderlyingSpace ℂ X) :
    mapFun (proj E) (mapFun σ x) = x :=
  UnderlyingSpace.ext (by simp only [toHom_mapFun, Category.assoc, hσ, Category.comp_id])

/-- A section maps `V(ℂ)` into `π⁻¹V(ℂ)`: the restriction of `σ` to an open `O ⊆ V(ℂ)`. -/
def chartRestrictHom (hσ : σ ≫ proj E = 𝟙 X) (c : Chart E r)
    (O : TopologicalSpace.Opens (TopCat.of (UnderlyingSpace ℂ X)))
    (hO : (O : Set _) ⊆ chartBase c) :
    TopCat.of O ⟶ TopCat.of (chartTotalOpens c) :=
  TopCat.ofHom ⟨fun p ↦ ⟨mapFun σ p.1,
      Eq.mpr (congrArg (· ∈ chartBase c) (mapFun_proj_mapFun_of_comp_eq_id σ hσ p.1)) (hO p.2)⟩,
    (((continuous_mapFun σ).comp continuous_subtype_val).subtype_mk _)⟩

/-- Composing `chartRestrictHom σ hσ c O hO` with the inclusion of `π⁻¹V(ℂ)` gives the
restriction of `σ` to `O`. -/
lemma chartRestrictHom_comp_inclHom (hσ : σ ≫ proj E = 𝟙 X) (c : Chart E r)
    (O : TopologicalSpace.Opens (TopCat.of (UnderlyingSpace ℂ X)))
    (hO : (O : Set _) ⊆ chartBase c) :
    chartRestrictHom σ hσ c O hO ≫ borelMooreHomology.inclHom (chartTotalOpens c) =
      borelMooreHomology.inclHom O ≫ TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ) :=
  rfl

/-- The chart coordinate of the restriction of `σ` to `O` is the local coordinate `h` of `σ`. -/
lemma chartRestrictHom_comp_lineChartCoordHom (hσ : σ ≫ proj E = 𝟙 X) (c : Chart E 1)
    (O : TopologicalSpace.Opens (TopCat.of (UnderlyingSpace ℂ X)))
    (hO : (O : Set _) ⊆ chartBase c) (h : TopCat.of O ⟶ TopCat.of ℂ)
    (hh : ∀ p : O, h p = coord c (mapFun σ p.1) 0) :
    chartRestrictHom σ hσ c O hO ≫ lineChartCoordHom c = h := by
  refine ConcreteCategory.hom_ext _ _ fun p ↦ ?_
  rw [hh]
  rfl

/-- On an open `O ⊆ V(ℂ)`, `σ⁻¹(0(X(ℂ)))` is the zero locus of the local coordinate
`h = (x^c ∘ σ)₀` of the section. -/
lemma preimage_inclHom_preimage_range_zeroSection (hσ : σ ≫ proj E = 𝟙 X) (c : Chart E 1)
    (O : TopologicalSpace.Opens (TopCat.of (UnderlyingSpace ℂ X)))
    (hO : (O : Set _) ⊆ chartBase c) (h : TopCat.of O ⟶ TopCat.of ℂ)
    (hh : ∀ p : O, h p = coord c (mapFun σ p.1) 0) :
    (borelMooreHomology.inclHom O).hom ⁻¹'
        ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹'
          range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) = h ⁻¹' {0} := by
  rw [← chartRestrictHom_comp_lineChartCoordHom σ hσ c O hO h hh]
  ext p
  exact Iff.of_eq (congrArg (fun S ↦ (chartRestrictHom σ hσ c O hO).hom p ∈ S)
    (preimage_inclHom_range_zeroSection_eq_lineChartCoordHom c))

/-- On an open `O ⊆ V(ℂ)`, the local coordinate `h` of `σ` carries `O - σ⁻¹(0(X(ℂ)))` into
`ℂ - 0`. -/
lemma compl_preimage_inclHom_preimage_subset (hσ : σ ≫ proj E = 𝟙 X) (c : Chart E 1)
    (O : TopologicalSpace.Opens (TopCat.of (UnderlyingSpace ℂ X)))
    (hO : (O : Set _) ⊆ chartBase c) (h : TopCat.of O ⟶ TopCat.of ℂ)
    (hh : ∀ p : O, h p = coord c (mapFun σ p.1) 0) :
    ((borelMooreHomology.inclHom O).hom ⁻¹'
        ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹'
          range (UnderlyingSpace.map (K := ℂ) (zeroSection E))))ᶜ ⊆
      h ⁻¹' ({0}ᶜ : Set (TopCat.of ℂ)) := by
  rw [preimage_inclHom_preimage_range_zeroSection σ hσ c O hO h hh]
  exact fun _ h ↦ h

variable [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E 1]

/-- **The localized first Chern class in a chart**: for a section `σ` of a rank-one bundle `𝐕(ℰ)`
and an open `O ⊆ V(ℂ)` on which the local coordinate of `σ` is `h = (x^c ∘ σ)₀`, the restriction
to `O` of `σ^*(u_ℰ)` is `h^* u₀` in `H²(O, O - h⁻¹(0))`, for the local orientation class
`u₀ ∈ H²(ℂ, ℂ - 0)`. -/
theorem pullback_inclHom_pullback_thomClass (hσ : σ ≫ proj E = 𝟙 X) (c : Chart E 1)
    (O : TopologicalSpace.Opens (TopCat.of (UnderlyingSpace ℂ X)))
    (hO : (O : Set _) ⊆ chartBase c) (h : TopCat.of O ⟶ TopCat.of ℂ)
    (hh : ∀ p : O, h p = coord c (mapFun σ p.1) 0)
    {u₀ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of ℂ) {0} (2 : ℕ)}
    (hu₀ : IsLocalOrientationClass R Complex.basisOneI (0 : TopCat.of ℂ) u₀) :
    (cohomologyWithSupports.pullback R (ModuleCat.of R R) (borelMooreHomology.inclHom O)
        ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹'
          range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) (2 * 1 : ℕ)).hom
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
          (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ))
          (range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) (2 * 1 : ℕ)).hom
            (Modules.thomClass R E 1)) =
      (relativeSingularCohomology.map R (ModuleCat.of R R) h
        (compl_preimage_inclHom_preimage_subset σ hσ c O hO h hh) (2 : ℕ)).hom u₀ := by
  let g := chartRestrictHom σ hσ c O hO
  let ιW := borelMooreHomology.inclHom (chartTotalOpens c)
  let Z := range (UnderlyingSpace.map (K := ℂ) (zeroSection E))
  let S := (borelMooreHomology.inclHom O).hom ⁻¹'
    ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹' Z)
  have hgι : Sᶜ ⊆ (borelMooreHomology.inclHom O ≫
      TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)) ⁻¹' Zᶜ :=
    fun (p : TopCat.of O) (hp : p ∈ Sᶜ) ↦ hp
  have hgι' : Sᶜ ⊆ (g ≫ ιW) ⁻¹' Zᶜ := fun (p : TopCat.of O) (hp : p ∈ Sᶜ) ↦ hp
  have hg : Sᶜ ⊆ g ⁻¹' (ιW.hom ⁻¹' Z)ᶜ := fun (p : TopCat.of O) (hp : p ∈ Sᶜ) ↦ hp
  have hι : (ιW.hom ⁻¹' Z)ᶜ ⊆ ιW ⁻¹' Zᶜ := fun _ hp ↦ hp
  have hs : (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹' Zᶜ ⊆
      (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹' Zᶜ := fun _ hp ↦ hp
  have hO' : Sᶜ ⊆ (borelMooreHomology.inclHom O).hom ⁻¹'
      ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹' Z)ᶜ := fun _ hp ↦ hp
  have hc := compl_preimage_inclHom_subset_lineChartCoordHom c
  have hgc : Sᶜ ⊆ (g ≫ lineChartCoordHom c) ⁻¹' ({0}ᶜ : Set (TopCat.of ℂ)) :=
    fun (p : TopCat.of O) (hp : p ∈ Sᶜ) ↦ hc (hg hp)
  calc _ = (relativeSingularCohomology.map R (ModuleCat.of R R)
        (borelMooreHomology.inclHom O ≫ TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)) hgι
          (2 * 1 : ℕ)).hom (Modules.thomClass R E 1) :=
        (relativeSingularCohomology.map_hom_comp_apply R _ _ hO' hs hgι _ _).symm
    _ = (relativeSingularCohomology.map R (ModuleCat.of R R) (g ≫ ιW) hgι' (2 * 1 : ℕ)).hom
          (Modules.thomClass R E 1) := rfl
    _ = (relativeSingularCohomology.map R (ModuleCat.of R R) g hg (2 * 1 : ℕ)).hom
          ((relativeSingularCohomology.map R (ModuleCat.of R R) ιW hι (2 * 1 : ℕ)).hom
            (Modules.thomClass R E 1)) :=
        relativeSingularCohomology.map_hom_comp_apply R _ _ hg hι hgι' _ _
    _ = (relativeSingularCohomology.map R (ModuleCat.of R R) g hg (2 * 1 : ℕ)).hom
          ((relativeSingularCohomology.map R (ModuleCat.of R R) (lineChartCoordHom c) hc
            (2 : ℕ)).hom u₀) :=
        congrArg _ (pullback_inclHom_thomClass_eq_lineChartCoordHom R c hu₀)
    _ = (relativeSingularCohomology.map R (ModuleCat.of R R) (g ≫ lineChartCoordHom c) hgc
          (2 : ℕ)).hom u₀ :=
        (relativeSingularCohomology.map_hom_comp_apply R _ _ hg hc hgc _ _).symm
    _ = _ := congrArg (fun φ ↦ ModuleCat.Hom.hom φ u₀)
        (relativeSingularCohomology.map_eq_map_of_hom_eq R
          (chartRestrictHom_comp_lineChartCoordHom σ hσ c O hO h hh) _ _ _)

/-- For a section `σ` of a rank-one bundle with local coordinate `h = (x^c ∘ σ)₀` on an open
`O ⊆ V(ℂ)`, if `h = g ^ m` on `O`, then the restriction to `O` of `σ^*(u_ℰ)` is `m · g^* u₀`. -/
theorem pullback_inclHom_pullback_thomClass_eq_smul (hσ : σ ≫ proj E = 𝟙 X) (c : Chart E 1)
    (O : TopologicalSpace.Opens (TopCat.of (UnderlyingSpace ℂ X)))
    (hO : (O : Set _) ⊆ chartBase c) (h : TopCat.of O ⟶ TopCat.of ℂ)
    (hh : ∀ p : O, h p = coord c (mapFun σ p.1) 0)
    (g : TopCat.of O ⟶ TopCat.of ℂ) (m : ℕ) (hgh : ∀ p, h p = g p ^ m)
    (hg : ((borelMooreHomology.inclHom O).hom ⁻¹'
        ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹'
          range (UnderlyingSpace.map (K := ℂ) (zeroSection E))))ᶜ ⊆
      g ⁻¹' ({0}ᶜ : Set (TopCat.of ℂ)))
    {u₀ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of ℂ) {0} (2 : ℕ)}
    (hu₀ : IsLocalOrientationClass R Complex.basisOneI (0 : TopCat.of ℂ) u₀) :
    (cohomologyWithSupports.pullback R (ModuleCat.of R R) (borelMooreHomology.inclHom O)
        ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹'
          range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) (2 * 1 : ℕ)).hom
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
          (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ))
          (range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) (2 * 1 : ℕ)).hom
            (Modules.thomClass R E 1)) =
      (m : R) • (relativeSingularCohomology.map R (ModuleCat.of R R) g hg (2 : ℕ)).hom u₀ :=
  (pullback_inclHom_pullback_thomClass R σ hσ c O hO h hh hu₀).trans
    (relativeSingularCohomology.map_eq_smul_of_eq_pow R g h m hgh hg _ u₀)

end Section

end MMP.Modules
