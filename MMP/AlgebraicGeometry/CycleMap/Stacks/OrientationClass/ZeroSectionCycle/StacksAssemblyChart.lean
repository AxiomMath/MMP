module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.ZeroSectionCycle.StacksRegular
public import MMP.AlgebraicTopology.OrientationClass.ZeroSectionProductCap
public import MMP.AlgebraicTopology.CapProduct.Restriction
public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksThomChart

/-!
# Fulton's Lemma 19.2(d): the bundle chart of `E|_V` over a ball of `V_reg` (Stacks bundles)

Let `ℰ` be a quasi-coherent `𝒪_X`-module, finite locally free of rank `r`, on a complex scheme
`X`, with vector bundle `π : 𝐕(ℰ) ⟶ X`, `V` a subvariety of `X`, and `E|_V = π⁻¹(V)` with
inclusion `ι : E|_V → 𝐕(ℰ)` and projection `π_V : E|_V → V`. For a chart `c = (U, b)` of `ℰ`
(`MMP.Modules.Chart`) and an open set `B₀ ⊆ V(ℂ)` inside the regular part `V_reg(ℂ)` and over
`U`, the open set `P₀ = π_V⁻¹(B₀)` of `E|_V(ℂ)` lies in the regular part of `E|_V`, and the
bundle chart `p ↦ (π_V p, x^c(ι p))` is a homeomorphism `Θ : P₀ ≅ B₀ × ℂʳ`.

## Main definitions

* `MMP.BundleChartBase`: an open set `B₀ ⊆ V_reg(ℂ)` as an open subset of the manifold `V_reg(ℂ)`.
* `MMP.Modules.preimageProjOpens`: the open set `π_V⁻¹(B₀)` of `E|_V(ℂ)`.
* `MMP.Modules.BundleChartSource`: `P₀`, as an open subset of `(E|_V)_reg(ℂ)`.
* `MMP.Modules.bundleChartFun`: the bundle chart `p ↦ (π_V p, x^c(ι p))`.
* `MMP.Modules.bundleChartHomeomorph`: the homeomorphism `Θ : P₀ ≅ B₀ × ℂʳ`.

## Main results

* `MMP.Modules.zeroSectionPreimageHomeomorph_apply`: the homeomorphism
  `ι⁻¹(0(X(ℂ))) ≅ V(ℂ)` is the projection `π_V`.
* `MMP.Modules.preimageProjOpens_le_regularOpens`: `P₀` lies in the regular part of `E|_V`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.2, proof of Lemma 19.2(d).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set Topology TopologicalSpace
open MMP.UnderlyingSpace

namespace MMP

section BundleChartBase

open MMP.Intersection.Scheme

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X]

/-- The open set `B₀`, as an open subset of the complex manifold `V_reg(ℂ)`. -/
abbrev BundleChartBase (V : Subvariety X) (B₀ : Opens (UnderlyingSpace ℂ V.toScheme)) : Type :=
  regularOpensInter (𝕜 := ℂ) B₀

end BundleChartBase

end MMP

namespace MMP.Modules

open MMP.Intersection.Scheme

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X] (E : X.Modules)
  [E.IsQuasicoherent] (r : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E r]
  [IsComplexScheme (totalSpace E)] (V : Subvariety X)

/-- A point of `𝐕(ℰ)(ℂ)` lies in `E|_V(ℂ)` iff it lies over `V(ℂ)`. -/
lemma mem_range_mapFun_preimageSubvariety_ι_iff (y : UnderlyingSpace ℂ (totalSpace E)) :
    y ∈ range (mapFun (K := ℂ) (preimageSubvariety E r V).ι) ↔
      mapFun (proj E) y ∈ range (mapFun (K := ℂ) V.ι) := by
  have hW : range (mapFun (K := ℂ) (preimageSubvariety E r V).ι) =
      pointsOver (K := ℂ) ((proj E).base ⁻¹' (V.support : Set X)) := by
    rw [range_mapFun_of_isClosedImmersion, Subvariety.ι,
      Scheme.IdealSheafData.range_subschemeι, ← coe_support_preimageSubvariety E r V]
    rfl
  have hV : range (mapFun (K := ℂ) V.ι) = pointsOver (K := ℂ) (V.support : Set X) := by
    rw [range_mapFun_of_isClosedImmersion, Subvariety.ι, Scheme.IdealSheafData.range_subschemeι]
    rfl
  rw [hW, hV, mem_pointsOver, mem_pointsOver, toHom_mapFun]
  rfl

/-- **The zero section of `E|_V` read in `V`**: the homeomorphism `h : ι⁻¹(0(X(ℂ))) ≅ V(ℂ)` is
the projection `π_V`. -/
lemma zeroSectionPreimageHomeomorph_apply
    (z : (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (preimageSubvariety E r V).ι)).hom ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) :
    zeroSectionPreimageHomeomorph E r V z = mapFun (preimageSubvarietyProj E r V) z.1 := by
  apply (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) V.ι).injective
  change mapFun V.ι (zeroSectionPreimageHomeomorph E r V z) = mapFun V.ι _
  refine (apply_homeomorphOfRangeEq (isEmbedding_zeroSectionPreimageHom E _)
    (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) V.ι).isEmbedding
    (range_zeroSectionPreimageHom E r V) z).trans ?_
  rw [coe_zeroSectionPreimageHom_apply, mapFun_preimageSubvarietyProj]
  set y := zeroSectionHomeomorph E ⟨mapFun (preimageSubvariety E r V).ι z.1, z.2⟩
  have h0 : mapFun (zeroSection E) y = mapFun (preimageSubvariety E r V).ι z.1 :=
    map_zeroSection_zeroSectionHomeomorph E _
  rw [← h0, mapFun_proj_mapFun_zeroSection]

variable {E r} in
omit [IsComplexScheme X] [IsComplexScheme (totalSpace E)] in
/-- The inverse chart `chartInv c x hx w` depends only on the point `x`, not on the proof `hx`. -/
lemma chartInv_congr {c : Chart E r} {x x' : UnderlyingSpace ℂ X} (h : x = x')
    (hx : ⊤ ≤ x.toHom ⁻¹ᵁ c.1.1) (hx' : ⊤ ≤ x'.toHom ⁻¹ᵁ c.1.1) (w : Fin r → ℂ) :
    chartInv c x hx w = chartInv c x' hx' w := by
  subst h
  rfl

/-! ### The bundle chart over a ball of `V_reg` -/

/-- The open set `π_V⁻¹(B₀)` of `E|_V(ℂ)`, for an open set `B₀` of `V(ℂ)`. -/
def preimageProjOpens (B₀ : Opens (UnderlyingSpace ℂ V.toScheme)) :
    Opens (UnderlyingSpace ℂ (preimageSubvariety E r V).toScheme) :=
  Opens.comap (UnderlyingSpace.map (K := ℂ) (preimageSubvarietyProj E r V)) B₀

variable {E r V} {c : Chart E r} {B₀ : Opens (UnderlyingSpace ℂ V.toScheme)}

/-- A point `p` of `E|_V(ℂ)` lies in `π_V⁻¹(B₀)` iff `π_V p ∈ B₀`. -/
@[simp]
lemma mem_preimageProjOpens {p : UnderlyingSpace ℂ (preimageSubvariety E r V).toScheme} :
    p ∈ preimageProjOpens E r V B₀ ↔ mapFun (preimageSubvarietyProj E r V) p ∈ B₀ :=
  Iff.rfl

/-- If `B₀` lies over the chart base of `c`, then `ι` maps `π_V⁻¹(B₀)` into the chart domain of
`c` in `𝐕(ℰ)(ℂ)`. -/
lemma mem_chartTotalOpens_of_mem_preimageProjOpens
    (hB₀ : ∀ q ∈ B₀, q ∈ regularPart ℂ V.toScheme ∧ mapFun V.ι q ∈ chartBase c)
    {p : UnderlyingSpace ℂ (preimageSubvariety E r V).toScheme}
    (hp : p ∈ preimageProjOpens E r V B₀) :
    mapFun (preimageSubvariety E r V).ι p ∈ chartTotalOpens c := by
  change mapFun (proj E) (mapFun (preimageSubvariety E r V).ι p) ∈ chartBase c
  rw [← mapFun_preimageSubvarietyProj]
  exact (hB₀ _ hp).2

/-- If `B₀` lies in `V_reg(ℂ)`, then `π_V⁻¹(B₀)` lies in the regular part of `E|_V(ℂ)`. -/
lemma preimageProjOpens_le_regularOpens (hB₀ : ∀ q ∈ B₀, q ∈ regularPart ℂ V.toScheme) :
    preimageProjOpens E r V B₀ ≤
      (regularOpens ℂ (preimageSubvariety E r V).toScheme :
        Opens (TopCat.of (UnderlyingSpace ℂ (preimageSubvariety E r V).toScheme))) := fun p hp ↦
  mem_regularPart_preimageSubvariety E r V p _ (hB₀ _ hp)
    (mapFun_preimageSubvarietyProj E r V p).symm

variable (E r V) in
/-- The open set `P₀ = π_V⁻¹(B₀)`, as an open subset of the complex manifold `(E|_V)_reg(ℂ)`. -/
abbrev BundleChartSource (B₀ : Opens (UnderlyingSpace ℂ V.toScheme)) : Type :=
  regularOpensInter (𝕜 := ℂ) (preimageProjOpens E r V B₀)

/-- The bundle chart `p ↦ (π_V p, x^c(ι p))`, from `P₀` to `B₀ × ℂʳ`. -/
def bundleChartFun (hB₀ : ∀ q ∈ B₀, q ∈ regularPart ℂ V.toScheme ∧ mapFun V.ι q ∈ chartBase c)
    (p : BundleChartSource E r V B₀) : BundleChartBase V B₀ × (Fin r → ℂ) :=
  (⟨⟨mapFun (preimageSubvarietyProj E r V) p.1.1, (hB₀ _ p.2).1⟩, p.2⟩,
    coord c (mapFun (preimageSubvariety E r V).ι p.1.1))

variable (hB₀ : ∀ q ∈ B₀, q ∈ regularPart ℂ V.toScheme ∧ mapFun V.ι q ∈ chartBase c)

/-- The bundle chart `p ↦ (π_V p, x^c(ι p))` is continuous. -/
lemma continuous_bundleChartFun : Continuous (bundleChartFun hB₀) := by
  refine Continuous.prodMk ((((continuous_mapFun _).comp
    (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _).subtype_mk _) ?_
  exact (continuousOn_coord c).comp_continuous ((continuous_mapFun _).comp
    (continuous_subtype_val.comp continuous_subtype_val))
    fun p ↦ mem_chartTotalOpens_of_mem_preimageProjOpens hB₀ p.2

/-- The bundle chart `p ↦ (π_V p, x^c(ι p))` is a bijection `P₀ → B₀ × ℂʳ`. -/
lemma bijective_bundleChartFun : Function.Bijective (bundleChartFun hB₀) := by
  refine ⟨fun p p' h ↦ ?_, fun bw ↦ ?_⟩
  · have h1 : mapFun (preimageSubvarietyProj E r V) p.1.1 =
        mapFun (preimageSubvarietyProj E r V) p'.1.1 := congrArg (fun z ↦ z.1.1.1) h
    have h2 : coord c (mapFun (preimageSubvariety E r V).ι p.1.1) =
        coord c (mapFun (preimageSubvariety E r V).ι p'.1.1) := congrArg Prod.snd h
    have hπ : mapFun (proj E) (mapFun (preimageSubvariety E r V).ι p.1.1) =
        mapFun (proj E) (mapFun (preimageSubvariety E r V).ι p'.1.1) := by
      rw [← mapFun_preimageSubvarietyProj, ← mapFun_preimageSubvarietyProj, h1]
    have h3 := (chartHomeomorph c).injective
      (a₁ := ⟨_, mem_chartTotalOpens_of_mem_preimageProjOpens hB₀ p.2⟩)
      (a₂ := ⟨_, mem_chartTotalOpens_of_mem_preimageProjOpens hB₀ p'.2⟩)
      (Prod.ext (Subtype.ext hπ) h2)
    exact Subtype.ext (Subtype.ext ((isClosedEmbedding_map_of_isClosedImmersion (K := ℂ)
      (preimageSubvariety E r V).ι).injective (congrArg Subtype.val h3)))
  · obtain ⟨b, w⟩ := bw
    have hx : mapFun V.ι b.1.1 ∈ chartBase c := (hB₀ _ b.2).2
    set y := chartInv c (mapFun V.ι b.1.1) hx w
    have hy : mapFun (proj E) y = mapFun V.ι b.1.1 := mapFun_proj_chartInv c _ hx w
    obtain ⟨p, hp⟩ : y ∈ range (mapFun (K := ℂ) (preimageSubvariety E r V).ι) :=
      (mem_range_mapFun_preimageSubvariety_ι_iff E r V y).2 (hy ▸ mem_range_self _)
    have hpb : mapFun (preimageSubvarietyProj E r V) p = b.1.1 := by
      apply (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) V.ι).injective
      change mapFun V.ι _ = mapFun V.ι _
      rw [mapFun_preimageSubvarietyProj, hp, hy]
    have hpP : p ∈ preimageProjOpens E r V B₀ := mem_preimageProjOpens.2 (hpb ▸ b.2)
    refine ⟨⟨⟨p, preimageProjOpens_le_regularOpens (fun q hq ↦ (hB₀ q hq).1) hpP⟩, hpP⟩, ?_⟩
    refine Prod.ext (Subtype.ext (Subtype.ext hpb)) ?_
    change coord c (mapFun (preimageSubvariety E r V).ι p) = w
    rw [hp]
    exact coord_chartInv c _ hx w

/-- The bundle chart `p ↦ (π_V p, x^c(ι p))` is inducing. -/
lemma isInducing_bundleChartFun : IsInducing (bundleChartFun hB₀) := by
  let G₀ : BundleChartBase V B₀ × (Fin r → ℂ) →
      {x : UnderlyingSpace ℂ X // ⊤ ≤ x.toHom ⁻¹ᵁ c.1.1} × (Fin r → ℂ) :=
    fun z ↦ (⟨mapFun V.ι z.1.1.1, (hB₀ _ z.1.2).2⟩, z.2)
  have hG₀ : Continuous G₀ :=
    (((continuous_mapFun V.ι).comp (continuous_subtype_val.comp
      (continuous_subtype_val.comp continuous_fst))).subtype_mk _).prodMk continuous_snd
  let G : BundleChartBase V B₀ × (Fin r → ℂ) → UnderlyingSpace ℂ (totalSpace E) :=
    fun z ↦ chartInv c (G₀ z).1.1 (G₀ z).1.2 (G₀ z).2
  have hG : Continuous G := (continuous_chartInv c).comp hG₀
  have hGΘ : G ∘ bundleChartFun hB₀ = fun p ↦ mapFun (preimageSubvariety E r V).ι p.1.1 := by
    funext p
    have hp := mem_chartTotalOpens_of_mem_preimageProjOpens hB₀ p.2
    exact (chartInv_congr (c := c) (mapFun_preimageSubvarietyProj E r V p.1.1) _ hp _).trans
      (chartInv_mapFun_proj_coord c _ hp)
  refine IsInducing.of_comp (continuous_bundleChartFun hB₀) hG ?_
  rw [hGΘ]
  exact (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ)
    (preimageSubvariety E r V).ι).isInducing.comp (IsInducing.subtypeVal.comp IsInducing.subtypeVal)

/-- **The bundle chart of `E|_V` over `B₀`**: the homeomorphism `Θ : P₀ ≅ B₀ × ℂʳ`,
`p ↦ (π_V p, x^c(ι p))`, between the open subsets `P₀ = π_V⁻¹(B₀)` of `(E|_V)_reg(ℂ)` and `B₀`
of `V_reg(ℂ)`. -/
def bundleChartHomeomorph : BundleChartSource E r V B₀ ≃ₜ BundleChartBase V B₀ × (Fin r → ℂ) :=
  (Equiv.ofBijective _ (bijective_bundleChartFun hB₀)).toHomeomorphOfIsInducing
    (isInducing_bundleChartFun hB₀)

/-- The homeomorphism `Θ` is the bundle chart `p ↦ (π_V p, x^c(ι p))`. -/
lemma bundleChartHomeomorph_apply (p : BundleChartSource E r V B₀) :
    bundleChartHomeomorph hB₀ p = bundleChartFun hB₀ p :=
  rfl

/-- The first component of `Θ p`, as a point of `V(ℂ)`, is `π_V p`. -/
lemma coe_fst_bundleChartHomeomorph_apply (p : BundleChartSource E r V B₀) :
    ((bundleChartHomeomorph hB₀ p).1.1.1 : UnderlyingSpace ℂ V.toScheme) =
      mapFun (preimageSubvarietyProj E r V) p.1.1 :=
  rfl

/-- The second component of `Θ p` is the chart coordinate `x^c(ι p)`. -/
lemma snd_bundleChartHomeomorph_apply (p : BundleChartSource E r V B₀) :
    (bundleChartHomeomorph hB₀ p).2 = coord c (mapFun (preimageSubvariety E r V).ι p.1.1) :=
  rfl

end MMP.Modules
