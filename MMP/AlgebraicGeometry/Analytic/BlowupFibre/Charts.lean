module

public import MMP.AlgebraicGeometry.Analytic.BlowupFibre.Basic
public import MMP.AlgebraicGeometry.Resolution.Blowup.Charts
public import MMP.AlgebraicGeometry.Morphisms.Smooth.SmoothFlagParameters
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.UnderlyingSpaceProperMap
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import StacksFrontier.AlgebraicGeometry.Blowup.SecondCentreChartCover
public import MMP.AlgebraicGeometry.Morphisms.Smooth.SmoothFlagCoordinates
public import MMP.AlgebraicGeometry.Resolution.Basic
public import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothFibreTwist
public import StacksFrontier.RingTheory.CohenMacaulay.Dimension
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.RegularStalk
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.FlatAtDivisor
public import StacksFrontier.AlgebraicGeometry.Smooth.InfinitesimalLifting

/-!
# The fibres of a smooth blowup, on charts

Let `b : V' ⟶ V` be the blowup of a smooth complex scheme `V` along a smooth closed subscheme
`T = V(I)`, and `t ∈ V(ℂ)` a point of `T` at which `T` has codimension `c`. Near `t` there are
local coordinates `x_1, …, x_N` on an affine open `U` whose first `c` generate `I` on `U`
(`MMP.Resolution.Bridges.exists_isLocalCoordinates_isCutOutByFirst_of_stalk`). The blowup is
covered over `U` by the charts `U_k = D₊(x_k)`, on which the exceptional divisor has the local
equation `x_k` and the sections `x_j / x_k` are defined: `π^*x_j = (x_j / x_k) π^*x_k`.

The fibre `F = (b^an)⁻¹(t)` is identified with `ℙ^{c-1}(ℂ)`, realized as the space of rank-one
orthogonal projections of `ℂ^c`, by sending a point `p ∈ U_k` to the projection onto the line
spanned by its coordinate ratios `((x_j / x_k)(p))_j`. Everything is read off the charts.

* *The line does not depend on the chart.* At a point of `U_k ∩ U_l`,
  `(π^*x_k) · ((x_j / x_k) - (x_l / x_k)(x_j / x_l)) = 0` in the stalk, and the germ of `π^*x_k`
  is a nonzerodivisor (the exceptional divisor is Cartier), so the two vectors of ratios are
  proportional.
* *The charts are determined by the ratios.* A point of `U_l` at which `x_k / x_l` does not vanish
  lies in `U_k`: there the germ of `π^*x_k` generates the exceptional ideal, which characterizes
  `D₊(x_k)` (`AlgebraicGeometry.mem_blowUpChartOpen_iff`).
* *Injectivity.* The ring of `U_k` is generated over `𝒪_X(U)` by the `x_j / x_k`
  (`MMP.Flips.ResolutionInputs.chartPresentation_surjective_and_ker`), so two points of `U_k` over
  `t` with the same ratios agree.
* *Surjectivity.* By the same result, the ring of `U_k` is
  `𝒪_X(U)[T_j : j ≠ k] / (x_j - T_j x_k)`; since the `x_j` vanish at `t`, every vector `w` with
  `w_k = 1` defines a homomorphism to `ℂ` over `t`, that is, a point of `U_k` over `t` with ratios
  `w`.
* *Continuity.* On `U_k(ℂ)` the map is `v ↦ v v^* / (v^* v)` composed with the continuous
  evaluations of the `x_j / x_k`; `F` is compact since `b` is proper, and `ℙ^{c-1}(ℂ)` is
  Hausdorff.

## Main definitions

* `MMP.Topology.chartRatios`: the vector `((x_j / x_k)(p))_j` of a point of `U_k(ℂ)`.
* `MMP.Topology.chartLine`: the projection onto the line of coordinate ratios.
* `MMP.Topology.fibreHomeomorphLines`: the homeomorphism of a fibre with the space of lines, for a
  chart datum.

## Main results

* `MMP.Topology.eval_chartFraction_eq_mul`: `x_j / x_k = (x_l / x_k)(x_j / x_l)` on `U_k ∩ U_l`.
* `MMP.Topology.top_le_preimage_chart_of_eval_ne_zero`: a point of `U_l` with `(x_k / x_l)(p) ≠ 0`
  lies in `U_k`.
* `MMP.Topology.eq_of_eval_chartFraction_eq`, `MMP.Topology.exists_eval_chartFraction_eq`: the
  points of `U_k` over `t` correspond to the vectors `w` with `w_k = 1`.
* `MMP.Topology.chartLine_apply_self_ne_zero`, `MMP.Topology.chartLine_div`: a point of `U_k`
  goes to a projection `P` with `P k k ≠ 0` and `P j k / P k k = (x_j / x_k)(p)`.
* `MMP.Topology.formallySmooth_quotient_idealSheafDataStalk`: `𝒪_{X,d} / I_d` is formally smooth
  for a smooth closed subscheme.
* `MMP.Topology.ringKrullDim_stalk_eq_quotient_add_height`: `dim 𝒪_{V,z} = dim 𝒪_{T,z} + ht I_z`.
* `MMP.Topology.exists_homeomorph_preimage_analyticMap_blowUpToBase_charts`: the fibre of a smooth
  blowup over a point where the ideal of the centre has height `n + 1` is `ℙⁿ(ℂ)`, explicitly on
  charts.
* `MMP.Topology.exists_homeomorph_preimage_analyticMap_blowUpToBase_charts_of_isIrreducible`,
  `MMP.Topology.exists_homeomorph_preimage_analyticMap_blowUpToBase_charts_of_codimension`: the
  same for an irreducible centre of codimension `c`, and for a centre of pure codimension `c`,
  with `n = c - 1`.

## Implementation notes

Points are `ℂ`-points with the classical topology, `MMP.UnderlyingSpace ℂ`, which is
homeomorphic to the complex realization (`MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace`);
the charts are `MMP.Resolution.BlowupChartData.chart` and the ratios
`MMP.Flips.ResolutionInputs.chartFraction`. The line of a point outside every chart is set to `0`;
on the fibres of interest every point lies in a chart.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.60]
* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology Opposite
open MMP MMP.UnderlyingSpace

namespace MMP.Topology

section Points

variable {K : Type} [Field K] {X : Scheme.{0}} [X.Over (Spec (.of K))]

/-- The value at a `K`-point `p` of a section depends only on its germ at the image of `p`. -/
lemma eval_eq_of_germ_eq {U U' : X.Opens} (p : UnderlyingSpace K X) (hp : ⊤ ≤ p.toHom ⁻¹ᵁ U)
    (hp' : ⊤ ≤ p.toHom ⁻¹ᵁ U') (s : Γ(X, U)) (s' : Γ(X, U'))
    (h : X.presheaf.germ U _ ((top_le_preimage_iff p U).1 hp) s =
      X.presheaf.germ U' _ ((top_le_preimage_iff p U').1 hp') s') :
    eval p hp s = eval p hp' s' := by
  obtain ⟨W, hxW, iU, iV, he⟩ := TopCat.Presheaf.germ_eq _ _ _ _ _ _ h
  have hpW : ⊤ ≤ p.toHom ⁻¹ᵁ W := (top_le_preimage_iff p W).2 hxW
  have e1 : eval p hpW (X.presheaf.map iU.op s) = eval p hp s :=
    eval_restrict (leOfHom iU) p hpW s
  have e2 : eval p hpW (X.presheaf.map iV.op s') = eval p hp' s' :=
    eval_restrict (leOfHom iV) p hpW s'
  rw [← e1, ← e2, he]

/-- The value at `p` of a section whose germ is a product of germs is the product of values. -/
lemma eval_eq_mul_of_germ_eq {U U' U'' : X.Opens} (p : UnderlyingSpace K X)
    (hp : ⊤ ≤ p.toHom ⁻¹ᵁ U) (hp' : ⊤ ≤ p.toHom ⁻¹ᵁ U') (hp'' : ⊤ ≤ p.toHom ⁻¹ᵁ U'')
    (s : Γ(X, U)) (s' : Γ(X, U')) (s'' : Γ(X, U''))
    (h : X.presheaf.germ U _ ((top_le_preimage_iff p U).1 hp) s =
      X.presheaf.germ U' _ ((top_le_preimage_iff p U').1 hp') s' *
        X.presheaf.germ U'' _ ((top_le_preimage_iff p U'').1 hp'') s'') :
    eval p hp s = eval p hp' s' * eval p hp'' s'' := by
  have hW : ⊤ ≤ p.toHom ⁻¹ᵁ (U' ⊓ U'') := le_inf hp' hp''
  have e := eval_eq_of_germ_eq p hp hW s
    (X.presheaf.map (homOfLE inf_le_left).op s' * X.presheaf.map (homOfLE inf_le_right).op s'')
    (by rw [h, map_mul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply])
  rw [e, ← evalRingHom_apply, map_mul, evalRingHom_apply, evalRingHom_apply, eval_restrict,
    eval_restrict]

/-- Two `K`-points of an affine open `W` at which all sections of `W` take the same values are
equal. -/
lemma eq_of_evalRingHom_eq {W : X.Opens} (hW : IsAffineOpen W) {p q : UnderlyingSpace K X}
    (hp : ⊤ ≤ p.toHom ⁻¹ᵁ W) (hq : ⊤ ≤ q.toHom ⁻¹ᵁ W)
    (h : evalRingHom p hp = evalRingHom q hq) : p = q := by
  have : IsAffine W.toScheme := hW
  obtain ⟨p', rfl⟩ : p ∈ Set.range (mapFun (K := K) W.ι) := by
    rwa [range_mapFun_of_isOpenImmersion, Scheme.Opens.opensRange_ι]
  obtain ⟨q', rfl⟩ : q ∈ Set.range (mapFun (K := K) W.ι) := by
    rwa [range_mapFun_of_isOpenImmersion, Scheme.Opens.opensRange_ι]
  congr 1
  refine UnderlyingSpace.ext (ext_of_isAffine ?_)
  ext a
  obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (W.ι.appLE W ⊤ W.ι_preimage_self.ge)).2 a
  have hb := congrArg (fun φ ↦ φ b) h
  simp only [evalRingHom_apply] at hb
  rw [eval_mapFun_ι, eval_mapFun_ι, evalTop_eq, evalTop_eq] at hb
  exact (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.injective hb

/-- A ring homomorphism `Γ(X, W) →+* K` over `K` on an affine open `W` is evaluation at a
`K`-point of `W`. -/
lemma exists_eval_eq_of_ringHom {W : X.Opens} (hW : IsAffineOpen W) (φ : Γ(X, W) →+* K)
    (hφ : ∀ a, φ (structureRingHomOpens W a) = a) :
    ∃ (p : UnderlyingSpace K X) (hp : ⊤ ≤ p.toHom ⁻¹ᵁ W), ∀ g, eval p hp g = φ g := by
  have : IsAffine W.toScheme := hW
  let θ := W.ι.appLE W ⊤ W.ι_preimage_self.ge
  let e := RingEquiv.ofBijective θ.hom (ConcreteCategory.bijective_of_isIso θ)
  let ρ : Γ(W.toScheme, ⊤) →+* K := φ.comp e.symm.toRingHom
  have hρθ : ∀ g, ρ (θ g) = φ g := fun g ↦ by
    simp only [ρ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    exact congrArg φ (e.symm_apply_apply g)
  have hρ : ∀ a, ρ (structureRingHom K W.toScheme a) = a := by
    intro a
    rw [structureRingHom_opens, RingHom.comp_apply]
    change ρ (θ _) = a
    rw [hρθ, hφ]
  let q := ofRingHom ρ hρ
  have hp : ⊤ ≤ (mapFun W.ι q).toHom ⁻¹ᵁ W := by
    have : mapFun (K := K) W.ι q ∈ Set.range (mapFun (K := K) W.ι) := ⟨q, rfl⟩
    rwa [range_mapFun_of_isOpenImmersion, Scheme.Opens.opensRange_ι] at this
  refine ⟨mapFun W.ι q, hp, fun g ↦ ?_⟩
  rw [eval_mapFun_ι, evalTop_ofRingHom]
  exact hρθ g

end Points

/-- The germ at `y` of the pull-back `g^♯ c` of a section `c` is the image of the germ of `c` at
`g y` under the stalk map. -/
private theorem germ_appLE {Y Z : Scheme.{0}} (g : Y ⟶ Z) {U : Z.Opens} {V : Y.Opens}
    (e : V ≤ g ⁻¹ᵁ U) {y : Y} (hy : y ∈ V) (c : Γ(Z, U)) :
    Y.presheaf.germ V y hy (g.appLE U V e c) =
      g.stalkMap y (Z.presheaf.germ U (g y) (show g y ∈ U from e hy) c) := by
  rw [Scheme.Hom.germ_stalkMap_apply, ← TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE e) y hy]
  rfl

section Charts

open MMP.Resolution MMP.Flips.ResolutionInputs

variable {X : Scheme.{0}} {I : X.IdealSheafData} (c : BlowupChartData I)

/-- `x_ℓ / x_ℓ = 1`. -/
@[simp]
lemma chartFraction_self (ℓ : Fin c.r) : chartFraction c ℓ ℓ = 1 :=
  (c.existsUnique_chartFraction ℓ ℓ).unique (chartPullback_eq_chartFraction_mul c ℓ ℓ)
    (one_mul _).symm

/-- A point of a chart lies over `U`. -/
lemma blowUpToBase_mem_of_mem_chart {ℓ : Fin c.r} {y : blowUp I} (hy : y ∈ c.chart ℓ) :
    blowUpToBase I y ∈ c.U :=
  c.chart_le ℓ hy

/-- The germ of `π^*f` on a chart is the image of the germ of `f`. -/
lemma germ_chartPullback (ℓ : Fin c.r) (f : Γ(X, c.U)) (y : blowUp I) (hy : y ∈ c.chart ℓ) :
    (blowUp I).presheaf.germ (c.chart ℓ) y hy (c.chartPullback ℓ f) =
      (blowUpToBase I).stalkMap y
        (X.presheaf.germ c.U _ (blowUpToBase_mem_of_mem_chart c hy) f) :=
  germ_appLE _ _ hy f

/-- The germ of `π^*x_ℓ` at a point of the chart `U_ℓ` is a nonzerodivisor. -/
lemma stalkMap_germ_mem_nonZeroDivisors (hU : IsAffineOpen c.U) (ℓ : Fin c.r) (y : blowUp I)
    (hy : y ∈ c.chart ℓ) :
    (blowUpToBase I).stalkMap y
        (X.presheaf.germ c.U _ (blowUpToBase_mem_of_mem_chart c hy) (c.x ℓ)) ∈
      nonZeroDivisors ((blowUp I).presheaf.stalk y) := by
  set a : I.ideal ⟨c.U, hU⟩ := ⟨_, c.restrict_mem_ideal ⟨c.U, hU⟩ le_rfl ℓ⟩
  have hy' : y ∈ (blowUpChartOpen I ⟨c.U, hU⟩ a).1 := chart_eq_blowUpChartOpen c hU ℓ ▸ hy
  have h1 := Stacks.Divisors.germ_mem_nonZeroDivisors (blowUpChartOpen I ⟨c.U, hU⟩ a).2
    (isRegular_iff_mem_nonZeroDivisors.2 (blowUpChartMap_self_mem_nonZeroDivisors I ⟨c.U, hU⟩ a))
    y hy'
  rwa [blowUpChartMap, germ_appLE, TopCat.Presheaf.germ_res_apply] at h1

/-- `π^*x_i = (x_i / x_ℓ) π^*x_ℓ`, read in the stalk at a point of `U_ℓ`. -/
lemma germ_chartFraction_mul (ℓ i : Fin c.r) (y : blowUp I) (hy : y ∈ c.chart ℓ) :
    (blowUp I).presheaf.germ (c.chart ℓ) y hy (chartFraction c ℓ i) *
        (blowUpToBase I).stalkMap y
          (X.presheaf.germ c.U _ (blowUpToBase_mem_of_mem_chart c hy) (c.x ℓ)) =
      (blowUpToBase I).stalkMap y
        (X.presheaf.germ c.U _ (blowUpToBase_mem_of_mem_chart c hy) (c.x i)) := by
  rw [← germ_chartPullback c ℓ (c.x ℓ) y hy, ← germ_chartPullback c ℓ (c.x i) y hy, ← map_mul,
    ← chartPullback_eq_chartFraction_mul]

/-- **The charts overlap where the coordinate ratios are units.** A point of `U_m` at which
`x_ℓ / x_m` is a unit lies in `U_ℓ`. -/
lemma mem_chart_of_isUnit (hU : IsAffineOpen c.U) {ℓ m : Fin c.r} {y : blowUp I}
    (hy : y ∈ c.chart m)
    (hu : IsUnit ((blowUp I).presheaf.germ (c.chart m) y hy (chartFraction c m ℓ))) :
    y ∈ c.chart ℓ := by
  have hyU : blowUpToBase I y ∈ c.U := c.chart_le m hy
  have hy2 := hy
  rw [chart_eq_blowUpChartOpen c hU m, mem_blowUpChartOpen_iff I _ _ y hyU] at hy2
  rw [chart_eq_blowUpChartOpen c hU ℓ, mem_blowUpChartOpen_iff I _ _ y hyU, hy2]
  have e : ∀ j, X.presheaf.germ c.U (blowUpToBase I y) hyU
      ((X.presheaf.map (homOfLE (le_refl c.U)).op).hom (c.x j)) =
      X.presheaf.germ c.U (blowUpToBase I y) hyU (c.x j) :=
    fun j ↦ TopCat.Presheaf.germ_res_apply _ _ _ _ _
  change Ideal.span {(blowUpToBase I).stalkMap y (X.presheaf.germ c.U (blowUpToBase I y) hyU
      ((X.presheaf.map (homOfLE (le_refl c.U)).op).hom (c.x m)))} =
    Ideal.span {(blowUpToBase I).stalkMap y (X.presheaf.germ c.U (blowUpToBase I y) hyU
      ((X.presheaf.map (homOfLE (le_refl c.U)).op).hom (c.x ℓ)))}
  rw [e, e, ← germ_chartFraction_mul c m ℓ y hy, Ideal.span_singleton_mul_left_unit hu]

variable {K : Type} [Field K] [(blowUp I).Over (Spec (.of K))]

/-- `x_ℓ / x_ℓ` takes the value `1`. -/
lemma eval_chartFraction_self (ℓ : Fin c.r) (p : UnderlyingSpace K (blowUp I))
    (hp : ⊤ ≤ p.toHom ⁻¹ᵁ c.chart ℓ) : eval p hp (chartFraction c ℓ ℓ) = 1 := by
  rw [chartFraction_self, ← evalRingHom_apply, map_one]

/-- **The coordinate ratios on overlapping charts.** At a point of `U_ℓ ∩ U_m`,
`x_i / x_ℓ = (x_m / x_ℓ)(x_i / x_m)`. -/
lemma eval_chartFraction_eq_mul (hU : IsAffineOpen c.U) {ℓ m : Fin c.r}
    (p : UnderlyingSpace K (blowUp I)) (hpℓ : ⊤ ≤ p.toHom ⁻¹ᵁ c.chart ℓ)
    (hpm : ⊤ ≤ p.toHom ⁻¹ᵁ c.chart m) (i : Fin c.r) :
    eval p hpℓ (chartFraction c ℓ i) =
      eval p hpℓ (chartFraction c ℓ m) * eval p hpm (chartFraction c m i) := by
  refine eval_eq_mul_of_germ_eq p hpℓ hpℓ hpm _ _ _ ?_
  set y := p.toHom (IsLocalRing.closedPoint K)
  have hyℓ : y ∈ c.chart ℓ := (top_le_preimage_iff p _).1 hpℓ
  have hym : y ∈ c.chart m := (top_le_preimage_iff p _).1 hpm
  refine (mul_cancel_right_mem_nonZeroDivisors
    (stalkMap_germ_mem_nonZeroDivisors c hU ℓ y hyℓ)).1 ?_
  rw [germ_chartFraction_mul c ℓ i y hyℓ, mul_right_comm, germ_chartFraction_mul c ℓ m y hyℓ,
    mul_comm, germ_chartFraction_mul c m i y hym]

/-- A point of `U_m` at which `x_ℓ / x_m` does not vanish lies in `U_ℓ`. -/
lemma top_le_preimage_chart_of_eval_ne_zero (hU : IsAffineOpen c.U) {ℓ m : Fin c.r}
    (p : UnderlyingSpace K (blowUp I)) (hpm : ⊤ ≤ p.toHom ⁻¹ᵁ c.chart m)
    (h : eval p hpm (chartFraction c m ℓ) ≠ 0) : ⊤ ≤ p.toHom ⁻¹ᵁ c.chart ℓ := by
  have hb := (top_le_preimage_basicOpen_iff p hpm _).2 h
  rw [top_le_preimage_iff] at hb ⊢
  have hb' : p.toHom (IsLocalRing.closedPoint K) ∈ c.chart m := Scheme.basicOpen_le _ _ hb
  exact mem_chart_of_isUnit c hU hb'
    (((blowUp I).mem_basicOpen _ _ hb').1 hb)

variable [X.Over (Spec (.of K))] [(blowUpToBase I).IsOver (Spec (.of K))]

/-- If a `K`-point `p` of the chart `U_ℓ` maps to `t`, then `t` is a `K`-point of `U`. -/
lemma top_le_preimage_of_mapFun_eq {ℓ : Fin c.r} {p : UnderlyingSpace K (blowUp I)}
    (hp : ⊤ ≤ p.toHom ⁻¹ᵁ c.chart ℓ) {t : UnderlyingSpace K X}
    (hpt : mapFun (blowUpToBase I) p = t) : ⊤ ≤ t.toHom ⁻¹ᵁ c.U := by
  subst hpt
  rw [top_le_preimage_iff] at hp ⊢
  exact c.chart_le ℓ hp

/-- At a point `p` over `t`, the pull-back `π^*f` takes the value `f(t)`. -/
lemma eval_chartPullback {ℓ : Fin c.r} {p : UnderlyingSpace K (blowUp I)}
    (hp : ⊤ ≤ p.toHom ⁻¹ᵁ c.chart ℓ) {t : UnderlyingSpace K X}
    (hpt : mapFun (blowUpToBase I) p = t) (ht : ⊤ ≤ t.toHom ⁻¹ᵁ c.U) (f : Γ(X, c.U)) :
    eval p hp (c.chartPullback ℓ f) = eval t ht f := by
  subst hpt
  exact eval_appLE _ (c.chart_le ℓ) p hp f

/-- At a point `p` of `U_ℓ` over `t`, the value of a section `P(x_i / x_ℓ)` of the chart is
`P(t)` evaluated at the coordinate ratios of `p`. -/
lemma eval_chartPresentation {ℓ : Fin c.r} {p : UnderlyingSpace K (blowUp I)}
    (hp : ⊤ ≤ p.toHom ⁻¹ᵁ c.chart ℓ) {t : UnderlyingSpace K X}
    (hpt : mapFun (blowUpToBase I) p = t) (ht : ⊤ ≤ t.toHom ⁻¹ᵁ c.U)
    (P : MvPolynomial {i : Fin c.r // i ≠ ℓ} Γ(X, c.U)) :
    eval p hp (chartPresentation c ℓ P) =
      MvPolynomial.eval₂ (evalRingHom t ht) (fun i ↦ eval p hp (chartFraction c ℓ i.1)) P := by
  rw [← evalRingHom_apply, ← RingHom.comp_apply, ← MvPolynomial.coe_eval₂Hom]
  congr 1
  refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_)
  · simp only [RingHom.comp_apply, chartPresentation, MvPolynomial.eval₂Hom_C, evalRingHom_apply]
    exact eval_chartPullback c hp hpt ht a
  · simp only [RingHom.comp_apply, chartPresentation, MvPolynomial.eval₂Hom_X', evalRingHom_apply]

/-- **A point of a chart over `t` is determined by its coordinate ratios.** -/
theorem eq_of_eval_chartFraction_eq (hU : IsAffineOpen c.U) {ℓ : Fin c.r}
    (hsurj : Function.Surjective (chartPresentation c ℓ)) {p q : UnderlyingSpace K (blowUp I)}
    (hp : ⊤ ≤ p.toHom ⁻¹ᵁ c.chart ℓ) (hq : ⊤ ≤ q.toHom ⁻¹ᵁ c.chart ℓ)
    (hpq : mapFun (blowUpToBase I) p = mapFun (blowUpToBase I) q)
    (h : ∀ i, eval p hp (chartFraction c ℓ i) = eval q hq (chartFraction c ℓ i)) : p = q := by
  have ht := top_le_preimage_of_mapFun_eq c hq rfl
  refine eq_of_evalRingHom_eq (isAffineOpen_chart c hU ℓ) hp hq (RingHom.ext fun s ↦ ?_)
  obtain ⟨P, rfl⟩ := hsurj s
  rw [evalRingHom_apply, evalRingHom_apply, eval_chartPresentation c hp hpq ht,
    eval_chartPresentation c hq rfl ht]
  simp only [h]

/-- The chart presentation sends a constant `f` to its pull-back to the chart `U_ℓ`. -/
@[simp]
lemma chartPresentation_C (ℓ : Fin c.r) (f : Γ(X, c.U)) :
    chartPresentation c ℓ (MvPolynomial.C f) = c.chartPullback ℓ f :=
  MvPolynomial.eval₂Hom_C _ _ f

/-- The chart presentation sends the variable `T_i` to the ratio `x_i / x_ℓ`. -/
@[simp]
lemma chartPresentation_X (ℓ : Fin c.r) (i : {i : Fin c.r // i ≠ ℓ}) :
    chartPresentation c ℓ (MvPolynomial.X i) = chartFraction c ℓ i.1 :=
  MvPolynomial.eval₂Hom_X' _ _ i

/-- On a chart, the structure map of the blowup over `K` is the pull-back of that of `X`. -/
lemma structureRingHomOpens_chart (ℓ : Fin c.r) (a : K) :
    structureRingHomOpens (X := blowUp I) (c.chart ℓ) a =
      c.chartPullback ℓ (structureRingHomOpens c.U a) := by
  have key : ∀ (g : blowUp I ⟶ Spec (.of K)) (_ : g = blowUpToBase I ≫ X ↘ Spec (.of K))
      (e : c.chart ℓ ≤ g ⁻¹ᵁ ⊤), g.appLE ⊤ (c.chart ℓ) e =
        (X ↘ Spec (.of K)).appLE ⊤ c.U (le_top.trans (Scheme.Hom.preimage_top _).ge) ≫
          (blowUpToBase I).appLE c.U (c.chart ℓ) (c.chart_le ℓ) := by
    rintro _ rfl e
    rw [Scheme.Hom.appLE_comp_appLE]
  simp only [structureRingHomOpens, BlowupChartData.chartPullback]
  rw [key _ (comp_over (blowUpToBase I) (Spec (.of K))).symm]
  rfl

/-- **Every vector of coordinate ratios occurs over a point of the centre.** Let the chart
presentation `𝒪_X(U)[T_i : i ≠ ℓ] → 𝒪(U_ℓ)`, `T_i ↦ x_i / x_ℓ`, be surjective with kernel inside
`(x_i - T_i x_ℓ)`, and let `t ∈ U(K)` be a point at which all the `x_i` vanish. Then every
`w ∈ K^r` with `w_ℓ = 1` is the vector of coordinate ratios `(x_i / x_ℓ)(p)` of a point `p` of
`U_ℓ(K)` over `t`. -/
theorem exists_eval_chartFraction_eq (hU : IsAffineOpen c.U) (ℓ : Fin c.r)
    (hsurj : Function.Surjective (chartPresentation c ℓ))
    (hker : RingHom.ker (chartPresentation c ℓ) ≤
      Ideal.span (Set.range fun i : {i : Fin c.r // i ≠ ℓ} ↦
        MvPolynomial.C (c.x i.1) - MvPolynomial.X i * MvPolynomial.C (c.x ℓ)))
    (t : UnderlyingSpace K X) (ht : ⊤ ≤ t.toHom ⁻¹ᵁ c.U) (ht0 : ∀ i, eval t ht (c.x i) = 0)
    {w : Fin c.r → K} (hw : w ℓ = 1) :
    ∃ (p : UnderlyingSpace K (blowUp I)) (hp : ⊤ ≤ p.toHom ⁻¹ᵁ c.chart ℓ),
      mapFun (blowUpToBase I) p = t ∧ ∀ i, eval p hp (chartFraction c ℓ i) = w i := by
  classical
  let ψ : MvPolynomial {i : Fin c.r // i ≠ ℓ} Γ(X, c.U) →+* K :=
    MvPolynomial.eval₂Hom (evalRingHom t ht) fun i ↦ w i.1
  have hψ : RingHom.ker (chartPresentation c ℓ) ≤ RingHom.ker ψ := by
    refine hker.trans (Ideal.span_le.2 ?_)
    rintro _ ⟨i, rfl⟩
    simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_mul, ψ, MvPolynomial.eval₂Hom_C,
      MvPolynomial.eval₂Hom_X', evalRingHom_apply, ht0, mul_zero, sub_zero]
  let φ₀ : Γ(blowUp I, c.chart ℓ) →+* K := (chartPresentation c ℓ).liftOfSurjective hsurj ⟨ψ, hψ⟩
  have hφ₀ : ∀ P, φ₀ (chartPresentation c ℓ P) = ψ P := fun P ↦
    RingHom.liftOfSurjective_comp_apply _ hsurj _ P
  obtain ⟨p, hp, hev⟩ := exists_eval_eq_of_ringHom (isAffineOpen_chart c hU ℓ) φ₀ fun a ↦ by
    rw [structureRingHomOpens_chart, ← chartPresentation_C, hφ₀]
    simp only [ψ, MvPolynomial.eval₂Hom_C, evalRingHom_apply, eval_structureRingHomOpens]
  refine ⟨p, hp, ?_, fun i ↦ ?_⟩
  · refine eq_of_evalRingHom_eq hU (top_le_preimage_of_mapFun_eq c hp rfl) ht
      (RingHom.ext fun f ↦ ?_)
    rw [evalRingHom_apply, evalRingHom_apply, ← eval_chartPullback c hp rfl, hev,
      ← chartPresentation_C, hφ₀]
    simp only [ψ, MvPolynomial.eval₂Hom_C, evalRingHom_apply]
  · rcases eq_or_ne i ℓ with rfl | hi
    · rw [eval_chartFraction_self, hw]
    · rw [hev, ← chartPresentation_X c ℓ ⟨i, hi⟩, hφ₀]
      simp only [ψ, MvPolynomial.eval₂Hom_X']

end Charts

section Fibre

open MMP.Resolution MMP.Flips.ResolutionInputs

variable {X : Scheme.{0}} {I : X.IdealSheafData} [(blowUp I).Over (Spec (.of ℂ))]
  (c : BlowupChartData I)

/-- The vector `((x_i / x_ℓ)(p))_i` of coordinate ratios of a point `p` of the chart `U_ℓ(ℂ)`. -/
def chartRatios (ℓ : Fin c.r) (p : UnderlyingSpace ℂ (blowUp I))
    (hp : ⊤ ≤ p.toHom ⁻¹ᵁ c.chart ℓ) : Fin c.r → ℂ :=
  fun i ↦ eval p hp (chartFraction c ℓ i)

/-- The `i`-th coordinate ratio of `p` on the chart `U_ℓ` is the value of `x_i / x_ℓ` at `p`. -/
lemma chartRatios_apply (ℓ : Fin c.r) (p : UnderlyingSpace ℂ (blowUp I))
    (hp : ⊤ ≤ p.toHom ⁻¹ᵁ c.chart ℓ) (i : Fin c.r) :
    chartRatios c ℓ p hp i = eval p hp (chartFraction c ℓ i) :=
  rfl

/-- The `ℓ`-th coordinate ratio on the chart `U_ℓ` is `1`. -/
@[simp]
lemma chartRatios_self (ℓ : Fin c.r) (p : UnderlyingSpace ℂ (blowUp I))
    (hp : ⊤ ≤ p.toHom ⁻¹ᵁ c.chart ℓ) : chartRatios c ℓ p hp ℓ = 1 :=
  eval_chartFraction_self c ℓ p hp

/-- The vector of coordinate ratios of a point of a chart is nonzero. -/
lemma chartRatios_ne_zero (ℓ : Fin c.r) (p : UnderlyingSpace ℂ (blowUp I))
    (hp : ⊤ ≤ p.toHom ⁻¹ᵁ c.chart ℓ) : chartRatios c ℓ p hp ≠ 0 :=
  Function.ne_iff.2 ⟨ℓ, by simp⟩

/-- On `U_ℓ ∩ U_m` the two vectors of coordinate ratios are proportional. -/
lemma chartRatios_eq_smul (hU : IsAffineOpen c.U) {ℓ m : Fin c.r}
    (p : UnderlyingSpace ℂ (blowUp I)) (hpℓ : ⊤ ≤ p.toHom ⁻¹ᵁ c.chart ℓ)
    (hpm : ⊤ ≤ p.toHom ⁻¹ᵁ c.chart m) :
    chartRatios c m p hpm = chartRatios c m p hpm ℓ • chartRatios c ℓ p hpℓ :=
  funext fun i ↦ eval_chartFraction_eq_mul c hU p hpm hpℓ i

/-- For `p ∈ U_ℓ ∩ U_m`, the `ℓ`-th coordinate ratio of `p` on the chart `U_m` is nonzero. -/
lemma chartRatios_apply_ne_zero (hU : IsAffineOpen c.U) {ℓ m : Fin c.r}
    (p : UnderlyingSpace ℂ (blowUp I)) (hpℓ : ⊤ ≤ p.toHom ⁻¹ᵁ c.chart ℓ)
    (hpm : ⊤ ≤ p.toHom ⁻¹ᵁ c.chart m) : chartRatios c m p hpm ℓ ≠ 0 := by
  intro h
  have := congrFun (chartRatios_eq_smul c hU p hpℓ hpm) m
  rw [chartRatios_self, Pi.smul_apply, h, zero_smul] at this
  exact one_ne_zero this

/-- **The line of a point of the blowup over `U`.** For `p` in a chart `U_ℓ`, the orthogonal
projection of `ℂ^r` onto the line spanned by the coordinate ratios `((x_i / x_ℓ)(p))_i`; it does
not depend on the chart (`MMP.Topology.chartLine_eq`). If `p` lies in no chart, the value is
`0`. -/
def chartLine (p : UnderlyingSpace ℂ (blowUp I)) : Fin c.r → Fin c.r → ℂ :=
  open Classical in
  if h : ∃ ℓ, ⊤ ≤ p.toHom ⁻¹ᵁ c.chart ℓ then lineProjection (chartRatios c h.choose p h.choose_spec)
  else 0

/-- In any chart `U_ℓ` containing `p`, the line of `p` is spanned by its coordinate ratios
`x_i / x_ℓ`. -/
lemma chartLine_eq (hU : IsAffineOpen c.U) {ℓ : Fin c.r} {p : UnderlyingSpace ℂ (blowUp I)}
    (hp : ⊤ ≤ p.toHom ⁻¹ᵁ c.chart ℓ) : chartLine c p = lineProjection (chartRatios c ℓ p hp) := by
  have h : ∃ ℓ, ⊤ ≤ p.toHom ⁻¹ᵁ c.chart ℓ := ⟨ℓ, hp⟩
  rw [chartLine, dite_eq_left h, chartRatios_eq_smul c hU p hp h.choose_spec,
    lineProjection_smul (chartRatios_ne_zero c ℓ p hp)
      (chartRatios_apply_ne_zero c hU p hp h.choose_spec)]

/-- A point of the chart `U_ℓ` goes to a projection `P` with `P ℓ ℓ ≠ 0`. -/
lemma chartLine_apply_self_ne_zero (hU : IsAffineOpen c.U) {ℓ : Fin c.r}
    {p : UnderlyingSpace ℂ (blowUp I)} (hp : ⊤ ≤ p.toHom ⁻¹ᵁ c.chart ℓ) :
    chartLine c p ℓ ℓ ≠ 0 := by
  rw [chartLine_eq c hU hp, lineProjection_apply_self_ne_zero_iff (chartRatios_ne_zero c ℓ p hp),
    chartRatios_self]
  exact one_ne_zero

/-- **The chart behaviour of the line of a point.** For `p` in the chart `U_ℓ`, the ratios
`P j ℓ / P ℓ ℓ` of its projection `P` are the values `(x_j / x_ℓ)(p)`. -/
lemma chartLine_div (hU : IsAffineOpen c.U) {ℓ : Fin c.r} {p : UnderlyingSpace ℂ (blowUp I)}
    (hp : ⊤ ≤ p.toHom ⁻¹ᵁ c.chart ℓ) (j : Fin c.r) :
    chartLine c p j ℓ / chartLine c p ℓ ℓ = eval p hp (chartFraction c ℓ j) := by
  rw [chartLine_eq c hU hp, lineProjection_div_apply (chartRatios_ne_zero c ℓ p hp)
    (by simp), chartRatios_self, div_one, chartRatios_apply]

/-- The line of a point of a chart is the projection onto the line spanned by a nonzero vector. -/
lemma chartLine_mem (hU : IsAffineOpen c.U) {ℓ : Fin c.r} {p : UnderlyingSpace ℂ (blowUp I)}
    (hp : ⊤ ≤ p.toHom ⁻¹ᵁ c.chart ℓ) :
    chartLine c p ∈ {P : Fin c.r → Fin c.r → ℂ | ∃ v, v ≠ 0 ∧ lineProjection v = P} :=
  ⟨_, chartRatios_ne_zero c ℓ p hp, (chartLine_eq c hU hp).symm⟩

/-- The line of a point is continuous on each chart `U_ℓ`. -/
lemma continuousOn_chartLine (hU : IsAffineOpen c.U) (ℓ : Fin c.r) :
    ContinuousOn (chartLine c) {p : UnderlyingSpace ℂ (blowUp I) | ⊤ ≤ p.toHom ⁻¹ᵁ c.chart ℓ} := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact (continuous_lineProjection_comp
    (continuous_pi fun j ↦ continuous_eval _ (chartFraction c ℓ j))
    fun q ↦ chartRatios_ne_zero c ℓ q.1 q.2).congr fun q ↦ (chartLine_eq c hU q.2).symm

variable [X.Over (Spec (.of ℂ))] [(blowUpToBase I).IsOver (Spec (.of ℂ))]

/-- A point over a point of `U` lies in one of the charts. -/
lemma exists_top_le_preimage_chart {t : UnderlyingSpace ℂ X} (ht : ⊤ ≤ t.toHom ⁻¹ᵁ c.U)
    {p : UnderlyingSpace ℂ (blowUp I)} (hpt : mapFun (blowUpToBase I) p = t) :
    ∃ ℓ, ⊤ ≤ p.toHom ⁻¹ᵁ c.chart ℓ := by
  subst hpt
  have hx : p.toHom (IsLocalRing.closedPoint ℂ) ∈ blowUpToBase I ⁻¹ᵁ c.U :=
    (top_le_preimage_iff _ _).1 ht
  rw [← iSup_chart_eq_preimage c] at hx
  obtain ⟨ℓ, hℓ⟩ := Opens.mem_iSup.1 hx
  exact ⟨ℓ, (top_le_preimage_iff _ _).2 hℓ⟩

/-- The line of a point is continuous on the fibre over a point of `U`. -/
lemma continuousOn_chartLine_fibre (hU : IsAffineOpen c.U) {t : UnderlyingSpace ℂ X}
    (ht : ⊤ ≤ t.toHom ⁻¹ᵁ c.U) :
    ContinuousOn (chartLine c) (mapFun (blowUpToBase I) ⁻¹' {t}) := by
  intro p hp
  obtain ⟨ℓ, hℓ⟩ := exists_top_le_preimage_chart c ht hp
  exact ((continuousOn_chartLine c hU ℓ).continuousAt
    ((isOpen_setOf_le_preimage _).mem_nhds hℓ)).continuousWithinAt

/-- The line of a point is injective on a fibre over a point of `U`. -/
theorem injOn_chartLine (hU : IsAffineOpen c.U)
    (hsurj : ∀ ℓ, Function.Surjective (chartPresentation c ℓ)) {t : UnderlyingSpace ℂ X}
    (ht : ⊤ ≤ t.toHom ⁻¹ᵁ c.U) : Set.InjOn (chartLine c) (mapFun (blowUpToBase I) ⁻¹' {t}) := by
  intro p hp q hq h
  obtain ⟨ℓ, hpℓ⟩ := exists_top_le_preimage_chart c ht hp
  obtain ⟨m, hqm⟩ := exists_top_le_preimage_chart c ht hq
  have h1 : chartLine c q ℓ ℓ ≠ 0 := h ▸ chartLine_apply_self_ne_zero c hU hpℓ
  rw [chartLine_eq c hU hqm, lineProjection_apply_self_ne_zero_iff
    (chartRatios_ne_zero c m q hqm)] at h1
  have hqℓ := top_le_preimage_chart_of_eval_ne_zero c hU q hqm h1
  have hpq : mapFun (blowUpToBase I) p = mapFun (blowUpToBase I) q :=
    (Set.mem_singleton_iff.1 hp).trans (Set.mem_singleton_iff.1 hq).symm
  refine eq_of_eval_chartFraction_eq c hU (hsurj ℓ) hpℓ hqℓ hpq fun j ↦ ?_
  rw [← chartLine_div c hU hpℓ j, ← chartLine_div c hU hqℓ j, h]

/-- The lines of the points of a fibre over a point `t` of `U` at which the `x_i` vanish are all
the lines of `ℂ^r`. -/
theorem image_chartLine (hU : IsAffineOpen c.U)
    (hsurj : ∀ ℓ, Function.Surjective (chartPresentation c ℓ))
    (hker : ∀ ℓ, RingHom.ker (chartPresentation c ℓ) ≤
      Ideal.span (Set.range fun i : {i : Fin c.r // i ≠ ℓ} ↦
        MvPolynomial.C (c.x i.1) - MvPolynomial.X i * MvPolynomial.C (c.x ℓ)))
    {t : UnderlyingSpace ℂ X} (ht : ⊤ ≤ t.toHom ⁻¹ᵁ c.U) (ht0 : ∀ i, eval t ht (c.x i) = 0) :
    chartLine c '' (mapFun (blowUpToBase I) ⁻¹' {t}) =
      {P : Fin c.r → Fin c.r → ℂ | ∃ v, v ≠ 0 ∧ lineProjection v = P} := by
  refine subset_antisymm ?_ ?_
  · rintro _ ⟨p, hp, rfl⟩
    obtain ⟨ℓ, hℓ⟩ := exists_top_le_preimage_chart c ht hp
    exact chartLine_mem c hU hℓ
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨ℓ, hℓ⟩ := Function.ne_iff.1 hv
    replace hℓ : v ℓ ≠ 0 := hℓ
    obtain ⟨p, hp, hpt, hpv⟩ := exists_eval_chartFraction_eq c hU ℓ (hsurj ℓ) (hker ℓ) t ht ht0
      (w := (v ℓ)⁻¹ • v) (by simp [hℓ])
    refine ⟨p, hpt, ?_⟩
    rw [chartLine_eq c hU hp, show chartRatios c ℓ p hp = (v ℓ)⁻¹ • v from funext hpv,
      lineProjection_smul hv (inv_ne_zero hℓ)]

/-- **The fibre of the blowup over a point of the centre, on charts.** Let `x_1, …, x_r`
generate the ideal of the centre on an affine open `U`, with chart presentations
`𝒪_X(U)[T_i : i ≠ ℓ] → 𝒪(U_ℓ)`, `T_i ↦ x_i / x_ℓ`, surjective with kernel inside
`(x_i - T_i x_ℓ)`, and let `t ∈ U(ℂ)` be a point at which all the `x_i` vanish, with compact
fibre `F = π⁻¹(t)`. Then `p ↦ [(x_i / x_ℓ)(p)]_i`, for `p ∈ U_ℓ`, is a homeomorphism of `F` onto
the space of lines of `ℂ^r`. -/
def fibreHomeomorphLines (hU : IsAffineOpen c.U)
    (hsurj : ∀ ℓ, Function.Surjective (chartPresentation c ℓ))
    (hker : ∀ ℓ, RingHom.ker (chartPresentation c ℓ) ≤
      Ideal.span (Set.range fun i : {i : Fin c.r // i ≠ ℓ} ↦
        MvPolynomial.C (c.x i.1) - MvPolynomial.X i * MvPolynomial.C (c.x ℓ)))
    {t : UnderlyingSpace ℂ X} (ht : ⊤ ≤ t.toHom ⁻¹ᵁ c.U) (ht0 : ∀ i, eval t ht (c.x i) = 0)
    (hF : IsCompact (mapFun (blowUpToBase I) ⁻¹' {t})) :
    ↥(mapFun (blowUpToBase I) ⁻¹' {t}) ≃ₜ
      ↥{P : Fin c.r → Fin c.r → ℂ | ∃ v, v ≠ 0 ∧ lineProjection v = P} :=
  haveI := isCompact_iff_compactSpace.1 hF
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective
      (fun p ↦ ⟨chartLine c p.1, image_chartLine c hU hsurj hker ht ht0 ▸ ⟨p.1, p.2, rfl⟩⟩)
      ⟨fun p q h ↦ Subtype.ext (injOn_chartLine c hU hsurj ht p.2 q.2
          (congrArg Subtype.val h)), by
        rintro ⟨P, hP⟩
        rw [← image_chartLine c hU hsurj hker ht ht0] at hP
        obtain ⟨p, hp, rfl⟩ := hP
        exact ⟨⟨p, hp⟩, rfl⟩⟩)
    ((continuousOn_iff_continuous_domRestrict.1
      (continuousOn_chartLine_fibre c hU ht)).subtype_mk _)

/-- The homeomorphism `MMP.Topology.fibreHomeomorphLines` sends a point to its line. -/
@[simp]
lemma coe_fibreHomeomorphLines_apply (hU : IsAffineOpen c.U)
    (hsurj : ∀ ℓ, Function.Surjective (chartPresentation c ℓ))
    (hker : ∀ ℓ, RingHom.ker (chartPresentation c ℓ) ≤
      Ideal.span (Set.range fun i : {i : Fin c.r // i ≠ ℓ} ↦
        MvPolynomial.C (c.x i.1) - MvPolynomial.X i * MvPolynomial.C (c.x ℓ)))
    {t : UnderlyingSpace ℂ X} (ht : ⊤ ≤ t.toHom ⁻¹ᵁ c.U) (ht0 : ∀ i, eval t ht (c.x i) = 0)
    (hF : IsCompact (mapFun (blowUpToBase I) ⁻¹' {t}))
    (p : ↥(mapFun (blowUpToBase I) ⁻¹' {t})) :
    (fibreHomeomorphLines c hU hsurj hker ht ht0 hF p).1 = chartLine c p.1 :=
  rfl

end Fibre

section SmoothBlowup

open MMP.Resolution MMP.Flips.ResolutionInputs MMP.Analytic MMP.Analytic.ComplexPoints

/-- The sections of an ideal sheaf vanish at the `K`-points of its support. -/
lemma eval_eq_zero_of_mem_ideal {K : Type} [Field K] {Y : Scheme.{0}} [Y.Over (Spec (.of K))]
    (J : Y.IdealSheafData) (W : Y.affineOpens) (p : UnderlyingSpace K Y)
    (hp : ⊤ ≤ p.toHom ⁻¹ᵁ W.1) (hpJ : p.toHom (IsLocalRing.closedPoint K) ∈ J.support)
    {s : Γ(Y, W.1)} (hs : s ∈ J.ideal W) : eval p hp s = 0 := by
  by_contra h
  have hb := (top_le_preimage_iff p _).1 ((top_le_preimage_basicOpen_iff p hp s).2 h)
  exact (Scheme.mem_zeroLocus_iff _ _ _).1 (Scheme.IdealSheafData.mem_support_iff.1 hpJ W) s hs hb

/-- The coordinates of a chart datum vanish at the `K`-points of the support of its ideal. -/
lemma eval_x_eq_zero_of_mem_support {K : Type} [Field K] {Y : Scheme.{0}}
    [Y.Over (Spec (.of K))] {J : Y.IdealSheafData} (c : BlowupChartData J)
    (hU : IsAffineOpen c.U) (p : UnderlyingSpace K Y) (hp : ⊤ ≤ p.toHom ⁻¹ᵁ c.U)
    (hpJ : p.toHom (IsLocalRing.closedPoint K) ∈ J.support) (i : Fin c.r) :
    eval p hp (c.x i) = 0 := by
  have hi := c.restrict_mem_ideal ⟨c.U, hU⟩ le_rfl i
  rw [show (homOfLE (le_refl c.U)).op = 𝟙 _ from rfl, CategoryTheory.Functor.map_id] at hi
  exact eval_eq_zero_of_mem_ideal J ⟨c.U, hU⟩ p hp hpJ hi

/-- An ideal sheaf cut out by the first `r` coordinates is, on each affine open, the span of the
range of those coordinates indexed by `Fin r`. -/
lemma ideal_eq_span_range_of_isCutOutByFirst {Y : Scheme.{0}} {J : Y.IdealSheafData}
    {U : Y.Opens} {N r : ℕ} {x : Fin N → Γ(Y, U)} (hrN : r ≤ N)
    (hcut : Bridges.IsCutOutByFirst J U x r) (W : Y.affineOpens) (h : W.1 ≤ U) :
    J.ideal W = Ideal.span
      (Set.range fun i : Fin r ↦ (Y.presheaf.map (homOfLE h).op).hom (x (Fin.castLE hrN i))) := by
  rw [hcut W h]
  congr 1
  ext s
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨Fin.castLE hrN j, j.2, rfl⟩

/-- **The local ring of a smooth closed subscheme is formally smooth.** For a closed subscheme
`D ⊆ X` smooth over a field `k` and `d ∈ D`, the quotient `𝒪_{X,d} / I_d ≅ 𝒪_{D,d}` is formally
smooth over the stalk of `Spec k`. -/
theorem formallySmooth_quotient_idealSheafDataStalk {k : Type} [Field k] {X : Scheme.{0}}
    (f : X ⟶ Spec (.of k)) (D : X.IdealSheafData) [Smooth (D.subschemeι ≫ f)]
    (d : D.subscheme) :
    letI := (f.stalkMap (D.subschemeι d)).hom.toAlgebra
    Algebra.FormallySmooth ((Spec (.of k)).presheaf.stalk (f (D.subschemeι d)))
      (X.presheaf.stalk (D.subschemeι d) ⧸ IdealSheafData.stalk D (D.subschemeι d)) := by
  let _ := (f.stalkMap (D.subschemeι d)).hom.toAlgebra
  let _ : Algebra ((Spec (.of k)).presheaf.stalk (f (D.subschemeι d)))
    (D.subscheme.presheaf.stalk d) := ((D.subschemeι ≫ f).stalkMap d).hom.toAlgebra
  have hfs : Algebra.FormallySmooth ((Spec (.of k)).presheaf.stalk (f (D.subschemeι d)))
      (D.subscheme.presheaf.stalk d) :=
    InfinitesimalLifting.SmoothAt.formallySmooth_stalkMap (D.subschemeι ≫ f) d
      (InfinitesimalLifting.smoothAt_of_smooth _ d)
  let e : (X.presheaf.stalk (D.subschemeι d) ⧸ IdealSheafData.stalk D (D.subschemeι d)) ≃ₐ[
        (Spec (.of k)).presheaf.stalk (f (D.subschemeι d))] D.subscheme.presheaf.stalk d :=
    AlgEquiv.ofRingEquiv (f := stalkQuotientEquiv D d) (fun a => by
      change (D.subschemeι.stalkMap d).hom ((f.stalkMap (D.subschemeι d)).hom a) =
        ((D.subschemeι ≫ f).stalkMap d).hom a
      rw [Scheme.Hom.stalkMap_comp]; rfl)
  exact Algebra.FormallySmooth.of_equiv e.symm

/-- **The dimension formula at a point of a smooth centre.** Let `T = V(I)` be a smooth closed
subscheme of a smooth complex scheme `V` and `z ∈ T`. Then
`dim 𝒪_{V,z} = dim 𝒪_{V,z}/I_z + ht I_z`, where `I_z` is the kernel of the stalk map
`𝒪_{V,z} → 𝒪_{T,z}`. -/
theorem ringKrullDim_stalk_eq_quotient_add_height {V : Scheme.{0}} (sV : V ⟶ Spec (.of ℂ))
    (I : V.IdealSheafData) (hI : IsSmoothBlowup sV I) (z : I.subscheme) :
    ringKrullDim (V.presheaf.stalk (I.subschemeι z)) =
      ringKrullDim (V.presheaf.stalk (I.subschemeι z) ⧸
        IdealSheafData.stalk I (I.subschemeι z)) +
        ((RingHom.ker (I.subschemeι.stalkMap z).hom).height : WithBot ℕ∞) := by
  have : Smooth sV := hI.1.smooth
  have : Smooth (I.subschemeι ≫ sV) := hI.2.smooth
  have hA := isRegularLocalRing_stalk_of_smooth_over_field sV (I.subschemeι z)
  have : IsNoetherianRing (V.presheaf.stalk (I.subschemeι z)) := hA.toIsNoetherian
  have hT := isRegularLocalRing_stalk_of_smooth_over_field (I.subschemeι ≫ sV) z
  have : IsDomain (I.subscheme.presheaf.stalk z) := IsRegularLocalRing.isDomain _
  have hP : (IdealSheafData.stalk I (I.subschemeι z)).IsPrime := by
    rw [← IdealSheafData.ker_stalkMap_subschemeι_eq_stalk]
    exact RingHom.ker_isPrime _
  rw [(IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay
      _).2.ringKrullDim_eq_height_add_ringKrullDim_quotient_of_support_eq_univ
      (Module.support_self _) (IdealSheafData.stalk I (I.subschemeι z)), add_comm,
    ← IdealSheafData.ker_stalkMap_subschemeι_eq_stalk]

/-- **The fibre of a smooth blowup over a point of the centre, explicitly on charts.** Let
`b : V' ⟶ V` be the blowup of a smooth complex scheme `V` along a smooth closed subscheme
`T = V(I)`, `t ∈ V(ℂ)` a point lying on `T`, with image `z ∈ T`, and suppose that the ideal of
`T` in `𝒪_{V,z}` has height `n + 1`. Then there are local
coordinates `x_1, …, x_N` on an affine open `U ∋ t` whose first `n + 1` generate `I` on `U`, and
a homeomorphism `h : (b^an)⁻¹(t) ≃ₜ ℙⁿ(ℂ)` such that, on the chart `U_k = D₊(x_k)` of the
blowup, `h(p)` is the line spanned by `((x_j / x_k)(p))_j`: its projection `P = h(p)` has
`P k k ≠ 0` and `P j k / P k k = (x_j / x_k)(p)`. -/
theorem exists_homeomorph_preimage_analyticMap_blowUpToBase_charts {V : Scheme.{0}}
    (sV : V ⟶ Spec (.of ℂ)) (I : V.IdealSheafData) (hI : IsSmoothBlowup sV I)
    (t : ComplexPoints sV) (z : I.subscheme) (hz : I.subschemeι z = t.toScheme) (n : ℕ)
    (hn : ((n + 1 : ℕ) : ℕ∞) = (RingHom.ker (I.subschemeι.stalkMap z).hom).height) :
    ∃ (U : V.Opens) (_ : IsAffineOpen U) (_ : t.toScheme ∈ U) (N : ℕ) (x : Fin N → Γ(V, U))
      (_ : IsLocalCoordinates sV U x) (hnN : n + 1 ≤ N)
      (hf : ∀ (W : V.affineOpens) (h : W.1 ≤ U), I.ideal W = Ideal.span
        (Set.range fun i : Fin (n + 1) ↦
          (V.presheaf.map (homOfLE h).op).hom (x (Fin.castLE hnN i))))
      (h : (analyticMap (blowUpToBase I) rfl ⁻¹' {t} : Set (analyticSpace (blowUpToBase I ≫ sV)))
        ≃ₜ complexProjectiveSpace n),
      ∀ (p : (analyticMap (blowUpToBase I) rfl ⁻¹' {t} :
          Set (analyticSpace (blowUpToBase I ≫ sV)))) (k : Fin (n + 1))
        (hp : (p.1 : ComplexPoints (blowUpToBase I ≫ sV)) ∈ ComplexPoints.chart
          ((⟨U, n + 1, fun i ↦ x (Fin.castLE hnN i), hf⟩ : BlowupChartData I).chart k)),
        (h p).1 k k ≠ 0 ∧ ∀ j, (h p).1 j k / (h p).1 k k =
          ComplexPoints.eval _ (chartFraction
            (⟨U, n + 1, fun i ↦ x (Fin.castLE hnN i), hf⟩ : BlowupChartData I) k j) ⟨p.1, hp⟩ := by
  have : Smooth sV := hI.1.smooth
  have : Smooth (I.subschemeι ≫ sV) := hI.2.smooth
  have hT := isRegularLocalRing_stalk_of_smooth_over_field (I.subschemeι ≫ sV) z
  have hreg := IsRegularLocalRing.of_ringEquiv (stalkQuotientEquiv I z).symm
  have hfs := formallySmooth_quotient_idealSheafDataStalk sV I z
  have hdim := ringKrullDim_stalk_eq_quotient_add_height sV I hI z
  rw [← hn] at hdim
  obtain ⟨hnN, U, hU, hzU, x, hx, -, hcut⟩ :=
    Bridges.exists_isLocalCoordinates_isCutOutByFirst_of_stalk sV I I le_rfl (I.subschemeι z) hreg
      hreg hfs hdim hdim
  have htU : t.toScheme ∈ U := hz ▸ hzU
  have hf := ideal_eq_span_range_of_isCutOutByFirst hnN hcut
  refine ⟨U, hU, htU, _, x, hx, hnN, hf, ?_⟩
  set c : BlowupChartData I := ⟨U, n + 1, fun i ↦ x (Fin.castLE hnN i), hf⟩
  have hcU : IsAffineOpen c.U := hU
  have hsk := fun ℓ ↦ chartPresentation_surjective_and_ker c sV hcU x hx hnN (fun _ ↦ rfl) ℓ
  let : V.Over (Spec (.of ℂ)) := ⟨sV⟩
  let : (blowUp I).Over (Spec (.of ℂ)) := ⟨blowUpToBase I ≫ sV⟩
  have : (blowUpToBase I).IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
  have : IsProper (blowUpToBase I) := isProper_blowUpToBase I
  have : LocallyOfFiniteType (V ↘ Spec (.of ℂ)) := inferInstanceAs (LocallyOfFiniteType sV)
  let t' : UnderlyingSpace ℂ V := homeomorphUnderlyingSpace t
  have htx : t'.toHom (IsLocalRing.closedPoint ℂ) = t.toScheme :=
    congrArg t.hom (Subsingleton.elim _ _)
  have ht : ⊤ ≤ t'.toHom ⁻¹ᵁ c.U := (top_le_preimage_iff _ _).2 (htx ▸ htU)
  have htI : t'.toHom (IsLocalRing.closedPoint ℂ) ∈ I.support := by
    rw [htx, ← hz]
    change I.subschemeι z ∈ (I.support : Set V)
    rw [← I.range_subschemeι]
    exact ⟨z, rfl⟩
  have ht0 := eval_x_eq_zero_of_mem_support c hcU t' ht htI
  have hF : IsCompact (mapFun (blowUpToBase I) ⁻¹' {t'}) :=
    (isProperMap_map (K := ℂ) (blowUpToBase I)).isCompact_preimage isCompact_singleton
  let Φ := fibreHomeomorphLines c hcU (fun ℓ ↦ (hsk ℓ).1) (fun ℓ ↦ (hsk ℓ).2.le) ht ht0 hF
  let h0 : ComplexPoints (blowUpToBase I ≫ sV) ≃ₜ UnderlyingSpace ℂ (blowUp I) :=
    homeomorphUnderlyingSpace
  have hS : h0 '' (analyticMap (blowUpToBase I) rfl ⁻¹' {t}) =
      mapFun (blowUpToBase I) ⁻¹' {t'} := by
    rw [Homeomorph.image_eq_preimage_symm]
    ext a
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h ↦ UnderlyingSpace.ext (congrArg ComplexPoints.hom h),
      fun h ↦ ComplexPoints.ext (congrArg UnderlyingSpace.toHom h)⟩
  refine ⟨(h0.image _).trans ((Homeomorph.setCongr hS).trans Φ), fun p k hp ↦ ?_⟩
  have hp' : ⊤ ≤ (h0 p.1).toHom ⁻¹ᵁ c.chart k := hp.ge
  exact ⟨chartLine_apply_self_ne_zero c hcU hp', fun j ↦ chartLine_div c hcU hp' j⟩

/-- **The fibre of a smooth blowup along an irreducible centre, explicitly on charts.** Let
`b : V' ⟶ V` be the blowup of a smooth complex scheme `V` along a smooth irreducible closed
subscheme `T = V(I)` of codimension `c ≥ 1`, and `t ∈ V(ℂ)` a point of `T`. Then there are local
coordinates `x_1, …, x_N` on an affine open `U ∋ t` whose first `c` generate `I` on `U`, and a
homeomorphism `h : (b^an)⁻¹(t) ≃ₜ ℙ^{c-1}(ℂ)` such that on the chart `U_k = D₊(x_k)` the
projection `P = h(p)` has `P k k ≠ 0` and `P j k / P k k = (x_j / x_k)(p)`. -/
theorem exists_homeomorph_preimage_analyticMap_blowUpToBase_charts_of_isIrreducible
    {V : Scheme.{0}} (sV : V ⟶ Spec (.of ℂ)) (I : V.IdealSheafData) (hI : IsSmoothBlowup sV I)
    (hirr : IsIrreducible (I.support : Set V)) (c : ℕ) (hc : 1 ≤ c)
    (hcodim : codimension
      (⟨I.support, hirr, I.support.isClosed⟩ : TopologicalSpace.IrreducibleCloseds V) = c)
    (t : ComplexPoints sV) (ht : t.toScheme ∈ I.support) :
    ∃ (U : V.Opens) (_ : IsAffineOpen U) (_ : t.toScheme ∈ U) (N : ℕ) (x : Fin N → Γ(V, U))
      (_ : IsLocalCoordinates sV U x) (hnN : c - 1 + 1 ≤ N)
      (hf : ∀ (W : V.affineOpens) (h : W.1 ≤ U), I.ideal W = Ideal.span
        (Set.range fun i : Fin (c - 1 + 1) ↦
          (V.presheaf.map (homOfLE h).op).hom (x (Fin.castLE hnN i))))
      (h : (analyticMap (blowUpToBase I) rfl ⁻¹' {t} : Set (analyticSpace (blowUpToBase I ≫ sV)))
        ≃ₜ complexProjectiveSpace (c - 1)),
      ∀ (p : (analyticMap (blowUpToBase I) rfl ⁻¹' {t} :
          Set (analyticSpace (blowUpToBase I ≫ sV)))) (k : Fin (c - 1 + 1))
        (hp : (p.1 : ComplexPoints (blowUpToBase I ≫ sV)) ∈ ComplexPoints.chart
          ((⟨U, c - 1 + 1, fun i ↦ x (Fin.castLE hnN i), hf⟩ : BlowupChartData I).chart k)),
        (h p).1 k k ≠ 0 ∧ ∀ j, (h p).1 j k / (h p).1 k k =
          ComplexPoints.eval _ (chartFraction
            (⟨U, c - 1 + 1, fun i ↦ x (Fin.castLE hnN i), hf⟩ : BlowupChartData I) k j)
            ⟨p.1, hp⟩ := by
  obtain ⟨z, hz⟩ : t.toScheme ∈ Set.range I.subschemeι := by
    rwa [I.range_subschemeι]
  have := MMP.Resolution.isIntegral_subscheme_of_isIrreducible sV I hI.2 hirr
  refine exists_homeomorph_preimage_analyticMap_blowUpToBase_charts sV I hI t z hz (c - 1) ?_
  rw [Nat.sub_add_cancel hc,
    MMP.Threefold.Resolution.height_ker_stalkMap_subschemeι_eq_codimension I hirr z, hcodim]

/-- **The fibre of a smooth blowup along a centre of pure codimension `c`, explicitly on
charts.** Let `b : V' ⟶ V` be the blowup of a smooth complex scheme `V` along a smooth closed
subscheme `T = V(I)`, not necessarily connected, every maximal irreducible closed subset of which
has codimension `c ≥ 1`, and `t ∈ V(ℂ)` a point of `T`. Then there are local coordinates
`x_1, …, x_N` on an affine open `U ∋ t` whose first `c` generate `I` on `U`, and a homeomorphism
`h : (b^an)⁻¹(t) ≃ₜ ℙ^{c-1}(ℂ)` such that on the chart `U_k = D₊(x_k)` the projection `P = h(p)`
has `P k k ≠ 0` and `P j k / P k k = (x_j / x_k)(p)`. -/
theorem exists_homeomorph_preimage_analyticMap_blowUpToBase_charts_of_codimension
    {V : Scheme.{0}} (sV : V ⟶ Spec (.of ℂ)) (I : V.IdealSheafData) (hI : IsSmoothBlowup sV I)
    (c : ℕ) (hc : 1 ≤ c)
    (hcodim : ∀ Z : TopologicalSpace.IrreducibleCloseds V,
      Maximal (fun W : TopologicalSpace.IrreducibleCloseds V ↦ (W : Set V) ⊆ I.support) Z →
        codimension Z = c)
    (t : ComplexPoints sV) (ht : t.toScheme ∈ I.support) :
    ∃ (U : V.Opens) (_ : IsAffineOpen U) (_ : t.toScheme ∈ U) (N : ℕ) (x : Fin N → Γ(V, U))
      (_ : IsLocalCoordinates sV U x) (hnN : c - 1 + 1 ≤ N)
      (hf : ∀ (W : V.affineOpens) (h : W.1 ≤ U), I.ideal W = Ideal.span
        (Set.range fun i : Fin (c - 1 + 1) ↦
          (V.presheaf.map (homOfLE h).op).hom (x (Fin.castLE hnN i))))
      (h : (analyticMap (blowUpToBase I) rfl ⁻¹' {t} : Set (analyticSpace (blowUpToBase I ≫ sV)))
        ≃ₜ complexProjectiveSpace (c - 1)),
      ∀ (p : (analyticMap (blowUpToBase I) rfl ⁻¹' {t} :
          Set (analyticSpace (blowUpToBase I ≫ sV)))) (k : Fin (c - 1 + 1))
        (hp : (p.1 : ComplexPoints (blowUpToBase I ≫ sV)) ∈ ComplexPoints.chart
          ((⟨U, c - 1 + 1, fun i ↦ x (Fin.castLE hnN i), hf⟩ : BlowupChartData I).chart k)),
        (h p).1 k k ≠ 0 ∧ ∀ j, (h p).1 j k / (h p).1 k k =
          ComplexPoints.eval _ (chartFraction
            (⟨U, c - 1 + 1, fun i ↦ x (Fin.castLE hnN i), hf⟩ : BlowupChartData I) k j)
            ⟨p.1, hp⟩ := by
  obtain ⟨z, hz⟩ : t.toScheme ∈ Set.range I.subschemeι := by
    rwa [I.range_subschemeι]
  obtain ⟨C, hC, hzC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {z}
    isIrreducible_singleton
  have hgen := hC.1.isGenericPoint_genericPoint_closure
  rw [isGenericPoint_def, (isClosed_of_mem_irreducibleComponents C hC).closure_eq] at hgen
  have hwz : hC.1.genericPoint ⤳ z := by
    rw [specializes_iff_mem_closure, hgen]
    exact hzC rfl
  refine exists_homeomorph_preimage_analyticMap_blowUpToBase_charts sV I hI t z hz (c - 1) ?_
  rw [Nat.sub_add_cancel hc,
    height_ker_stalkMap_subschemeι_eq_codimension_closureSingleton sV I hI.2 (by rwa [hgen]) hwz,
    hcodim _ (maximal_closureSingleton_subschemeι I (by rwa [hgen]))]

end SmoothBlowup

end MMP.Topology
