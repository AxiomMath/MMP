module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.ZeroSectionCycle.StacksPreimageSubvariety
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.AlgebraicChartHolomorphic
public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksThomChart

/-!
# The bundle chart of `E|_V` is holomorphic (Stacks vector bundles)

Let `ℰ` be a quasi-coherent `𝒪_X`-module, finite locally free of rank `r`, on a complex scheme
`X`, with vector bundle `π : 𝐕(ℰ) ⟶ X`, `V` a subvariety of `X` and `E|_V = π⁻¹(V)`
(`MMP.Modules.preimageSubvariety`), with inclusion `ι : E|_V → 𝐕(ℰ)` and projection
`π_V : E|_V → V`. Over the domain `π⁻¹(U)` of a chart `(U, b)` of `ℰ` (`MMP.Modules.Chart`), the
bundle chart of `E|_V` is `p ↦ (π_V p, x^c(ι p))`. Read in algebraic charts of `E|_V(ℂ)` and
`V(ℂ)`, it is `C^ω`: `π_V` is a morphism, and the chart coordinates `bᵢ` are regular functions.

## Main results

* `MMP.Modules.contDiffAt_coord_comp_mapFun`: the chart coordinates of `ι` are `C^ω` in an
  algebraic chart of `E|_V(ℂ)`.
* `MMP.Modules.contDiffAt_bundleChart`: the bundle chart `(π_V, x^c ∘ ι)` is `C^ω` in algebraic
  charts.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set Topology
open scoped ContDiff
open MMP.UnderlyingSpace

namespace MMP.Modules

open MMP.Intersection.Scheme

variable {X : Scheme.{0}} (E : X.Modules) [E.IsQuasicoherent] (r : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E r]
  [X.Over (Spec (.of ℂ))] (V : Subvariety X)
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {c : OpenPartialHomeomorph (UnderlyingSpace ℂ (preimageSubvariety E r V).toScheme) F}
  {p : UnderlyingSpace ℂ (preimageSubvariety E r V).toScheme}

/-- **The chart coordinates of `E|_V` are `C^ω`.** For an algebraic chart `c` of `E|_V(ℂ)` and a
point `p` of its source lying over the domain `π⁻¹(U)` of a chart `c' = (U, b)` of `ℰ`, the
coordinates `x^{c'} ∘ ι ∘ c⁻¹` are `C^ω` at `c(p)`. -/
theorem contDiffAt_coord_comp_mapFun (hc : IsAlgebraicChart c) (hp : p ∈ c.source)
    (c' : Chart E r) (hpi : mapFun (preimageSubvariety E r V).ι p ∈ chartTotalOpens c') :
    ContDiffAt ℂ ω (fun y ↦ coord c' (mapFun (preimageSubvariety E r V).ι (c.symm y)))
      (c p) := by
  set ι := (preimageSubvariety E r V).ι
  set U : (preimageSubvariety E r V).toScheme.Opens := ι ⁻¹ᵁ (proj E ⁻¹ᵁ c'.1.1)
  have hpU : ⊤ ≤ p.toHom ⁻¹ᵁ U :=
    (top_le_toHom_preimage_preimage_iff ι _).2 ((mem_chartTotalOpens_iff c' _).1 hpi)
  set S := c.target ∩ c.symm ⁻¹' {q : UnderlyingSpace ℂ (preimageSubvariety E r V).toScheme |
    ⊤ ≤ q.toHom ⁻¹ᵁ U}
  have hSo : IsOpen S := c.isOpen_inter_preimage_symm (isOpen_setOf_le_preimage _)
  have hmem : S ∈ 𝓝 (c p) := hSo.mem_nhds ⟨c.map_source hp, by
    simpa [c.left_inv hp] using hpU⟩
  have hF : ContDiffOn ℂ ω
      (fun y a ↦ evalExt U (ι.app _ (chartCoordSection c' a)) (c.symm y)) S :=
    contDiffOn_pi.2 fun a ↦ hc.contDiffOn_evalExt _ _
  refine (hF.contDiffAt hmem).congr_of_eventuallyEq ?_
  filter_upwards with y
  funext a
  change evalExt _ _ (mapFun ι (c.symm y)) = _
  rw [evalExt_mapFun]

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
  {e : OpenPartialHomeomorph (UnderlyingSpace ℂ V.toScheme) G}

/-- **The bundle chart of `E|_V` is `C^ω` in algebraic charts.** For algebraic charts `c` of
`E|_V(ℂ)` and `e` of `V(ℂ)`, and a point `p` of the source of `c` with `π_V(p)` in the source of
`e` and lying over the domain `π⁻¹(U)` of a chart `c' = (U, b)` of `ℰ`, the chart expression
`y ↦ (e(π_V(c⁻¹ y)), x^{c'}(ι(c⁻¹ y)))` of the bundle chart is `C^ω` at `c(p)`. -/
theorem contDiffAt_bundleChart (hc : IsAlgebraicChart c) (he : IsAlgebraicChart e)
    (hp : p ∈ c.source) (hpe : mapFun (preimageSubvarietyProj E r V) p ∈ e.source)
    (c' : Chart E r) (hpi : mapFun (preimageSubvariety E r V).ι p ∈ chartTotalOpens c') :
    ContDiffAt ℂ ω (fun y ↦ (e (mapFun (preimageSubvarietyProj E r V) (c.symm y)),
      coord c' (mapFun (preimageSubvariety E r V).ι (c.symm y)))) (c p) :=
  (hc.contDiffAt_comp_mapFun _ he hp hpe).prodMk
    (contDiffAt_coord_comp_mapFun E r V hc hp c' hpi)

end MMP.Modules
