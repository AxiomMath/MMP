module

public import MMP.AlgebraicTopology.ComplexProjectiveSpace.TautologicalBundle
public import MMP.AlgebraicGeometry.Analytic.DivisorOrientationDatum
public import MMP.AlgebraicGeometry.Analytic.BlowupFibre.Charts
public import MMP.AlgebraicTopology.ThomClass.Natural
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.ThomClassPullback
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.FibreCoordinateChart

/-!
# The Euler class of the exceptional divisor on the fibres of a smooth blowup

Let `b : V' = Bl_T V ⟶ V` be the blowup of a smooth complex scheme along a smooth centre
`T = V(I)` of pure codimension `c ≥ 2`, `E ⊂ V'` its exceptional divisor, an effective Cartier
divisor, `𝐕(𝒪(E)^∨)` its line bundle, and `(𝒪(E)^∨, σ_E, W, Q)` the orientation datum of
`E ⊂ V'` built from the canonical section `σ_E` of `𝐕(𝒪(E)^∨)`
(`MMP.Topology.divisorOrientationDatum`), with `Q = 𝐕(𝒪(E)^∨)(ℂ)|_W` on a neighbourhood `W` of
`E(ℂ)`. We show that the Euler class `e(Q) = 0_Q^* u_Q`
(`MMP.Topology.eulerClass`), and so `ξ = -e(Q)`, restricts to a nonzero class on every fibre
`F = b⁻¹(t) ≅ ℙ^{c-1}(ℂ)`, `t ∈ T(ℂ)`.
The restriction of the line bundle `𝐕(𝒪(E)^∨)` to a fibre is the tautological line bundle
`O(-1)` of `ℙ^{c-1}`. Let `x_0, …, x_{c-1}` generate `I` on an affine open `U ∋ t`. On the chart
`U_k = D₊(x_k)` the exceptional divisor has the local equation `π^*x_k`, the line of a point
`p ∈ U_k ∩ F` is spanned by `((x_j / x_k)(p))_j`, and a vector `λ_k ((x_j / x_k)(p))_j` of it
goes to `λ_k / π^*x_k` in the fibre of `𝐕(𝒪(E)^∨)`. In a chart `c_j = (U_j, μ_j)` of `𝒪(E)^∨`,
where the canonical section has the coordinate `b_j = μ_j(1_E)`, a local equation of `E`
(`MMP.Topology.canonicalCoord`), this is the point with coordinate `λ_k s(p)` for the unit
`s = b_j / π^*x_k` (`MMP.Topology.IsFrameRatio`). On overlaps the coordinates of the tautological
bundle change by `(x_k' / x_k)(p)` and those of `𝐕(𝒪(E)^∨)` by the transition functions, and
`s = g_{jj'} (x_k' / x_k) s'`, so the point does not depend on the charts. This is a continuous
map `O(-1) → Q` over `F ⊆ W`, a linear isomorphism on the fibres; it pulls the Thom class of `Q`
back to that of `O(-1)` (`MMP.ThomClass.IsThomClassOfRank.map`), so
`e(Q)|_F = e(O(-1)) ≠ 0` (`MMP.Topology.eulerClass_tautologicalBundle_ne_zero`).

## Main definitions

* `MMP.Topology.IsFrameRatio`: the ratio `b_j / π^*x_k` of a local equation of `E` given by the
  canonical section to the one given by the blowup chart.
* `MMP.Topology.tautologicalFibreEquiv`, `MMP.Topology.tautologicalToLineBundle`: the map of the
  tautological bundle of `ℙⁿ(ℂ)` to `𝐕(𝒪(E)^∨)(ℂ)` over a map `g : ℙⁿ(ℂ) → Bl(ℂ)` compatible
  with the charts.
* `MMP.Topology.tautologicalToDatum`: the same map into the bundle `Q` of the orientation datum.
* `MMP.Topology.fibreContinuousLinearEquiv`: a linear isomorphism of fibres of vector bundles
  with finite-dimensional model fibres, as a continuous linear isomorphism.

## Main results

* `MMP.Topology.cast_eulerClass_eq_map`, `MMP.Topology.map_eulerClass_ne_zero`: Euler classes
  pull back along fibrewise isomorphisms of complex vector bundles.
* `MMP.Topology.exists_isFrameRatio`, `MMP.Topology.eval_eq_transition_mul_of_isFrameRatio`:
  frame ratios exist locally and satisfy the cocycle relation.
* `MMP.Topology.continuous_tautologicalToLineBundle`: the map `O(-1) → 𝐕(𝒪(E)^∨)(ℂ)` is
  continuous.
* `MMP.Topology.map_tautologicalToDatumBase_eulerClass_ne_zero`: `g^* e(Q) ≠ 0`.
* `MMP.Topology.map_eulerClass_divisorOrientationDatum_ne_zero_of_chartData`: `e(Q)|_F ≠ 0`, on
  charts.
* `MMP.Topology.map_eulerClass_divisorOrientationDatum_ne_zero`,
  `MMP.Topology.map_neg_eulerClass_divisorOrientationDatum_ne_zero`: `e(Q)|_F ≠ 0` and
  `ξ|_F ≠ 0`, `ξ = -e(Q)`, for a smooth blowup along a centre of pure codimension `c ≥ 2`.

## Implementation notes

Points are `ℂ`-points with the classical topology, `MMP.UnderlyingSpace ℂ`, on
which the orientation datum lives; `Bl(ℂ)` is homeomorphic to the complex realization
(`MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace`). The fibre `F` is
`mapFun (blowUpToBase I) ⁻¹' {t}`, and its inclusion into `W` is any continuous map
`ι : F → W` with `(ι p).1 = p.1`
(`MMP.Topology.preimage_singleton_subset_nbhd_divisorOrientationDatum` says one exists). The
charts of `𝒪(E)^∨` are arbitrary, so the map is written through the units `b_j / π^*x_k` relating
them to the local equations of the blowup charts.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.2, Appendix B.4.
* [J. Milnor, J. Stasheff, *Characteristic classes*][milnorstasheff1974], §§9–12.
-/

@[expose] public noncomputable section

namespace MMP.Topology

open MMP.Modules (totalSpace proj)

section EulerMap

open CategoryTheory Bundle Set MMP MMP.ThomClass

universe u

variable {R : Type u} [CommRing R]

/-- Moving a class of relative cohomology to an equal degree commutes with the map of a map of
pairs. -/
lemma cast_map_relativeSingularCohomology {Y' Y : TopCat.{u}} (f : Y' ⟶ Y) {A' : Set Y'}
    {A : Set Y} (h : A' ⊆ f ⁻¹' A) {n m : ℕ} (hnm : n = m)
    (x : relativeSingularCohomology R (ModuleCat.of R R) Y A (n : ℤ)) :
    cast (congrArg (fun k : ℕ ↦ (relativeSingularCohomology R (ModuleCat.of R R) Y' A' (k : ℤ) :
        Type u)) hnm) ((relativeSingularCohomology.map R (ModuleCat.of R R) f h n).hom x) =
      (relativeSingularCohomology.map R (ModuleCat.of R R) f h m).hom
        (cast (congrArg (fun k : ℕ ↦ (relativeSingularCohomology R (ModuleCat.of R R) Y A (k : ℤ) :
          Type u)) hnm) x) := by
  subst hnm
  rfl

/-- Moving a class of relative cohomology to an equal degree preserves being zero. -/
lemma cast_relativeSingularCohomology_eq_zero_iff {Y : TopCat.{u}} {A : Set Y} {n m : ℕ}
    (hnm : n = m) (x : relativeSingularCohomology R (ModuleCat.of R R) Y A (n : ℤ)) :
    cast (congrArg (fun k : ℕ ↦ (relativeSingularCohomology R (ModuleCat.of R R) Y A (k : ℤ) :
        Type u)) hnm) x = 0 ↔ x = 0 := by
  subst hnm
  rfl

variable {B : Type u} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  {E : B → Type u} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [_root_.VectorBundle ℂ F E]
  {B' : Type u} [TopologicalSpace B'] {F' : Type*} [NormedAddCommGroup F']
  [NormedSpace ℂ F'] [FiniteDimensional ℂ F'] {E' : B' → Type u} [∀ x, AddCommGroup (E' x)]
  [∀ x, Module ℂ (E' x)] [∀ x, TopologicalSpace (E' x)] [TopologicalSpace (TotalSpace F' E')]
  [FiberBundle F' E'] [_root_.VectorBundle ℂ F' E']

/-- **Euler classes pull back along fibrewise isomorphisms.** If `Φ : E' → E` covers `g : B' → B`
and is a complex linear isomorphism `E'_x ≅ E_{g x}` on each fibre, then `g^* e(E) = e(E')`, the
latter moved to the degree `2 dim F` of `e(E)`. -/
theorem cast_eulerClass_eq_map {Φ : TopCat.of (TotalSpace F' E') ⟶ TopCat.of (TotalSpace F E)}
    {g : C(B', B)} {φ : ∀ x, E' x ≃L[ℂ] E (g x)} (hΦ : ∀ x v, Φ ⟨x, v⟩ = ⟨g x, φ x v⟩)
    (hF : Module.finrank ℂ F' = Module.finrank ℂ F) :
    cast (congrArg (fun k : ℕ ↦ (relativeSingularCohomology R (ModuleCat.of R R) (TopCat.of B')
        (univᶜ) (k : ℤ) : Type u)) (congrArg (2 * ·) hF)) (eulerClass R F' E') =
      (relativeSingularCohomology.map R (ModuleCat.of R R) (TopCat.ofHom g) (A' := univᶜ)
        (A := univᶜ) (fun x hx ↦ (hx (mem_univ x)).elim) _).hom (eulerClass R F E) := by
  have hu : IsThomClassOfRank F E (Module.finrank ℂ F) (thomClass R F E) :=
    isThomClass_thomClass F E
  have hmap := IsThomClassOfRank.map hΦ hu
  have hu' := (isThomClassOfRank_cast_iff hF (thomClass R F' E')).2 (isThomClass_thomClass F' E')
  have huniq := (existsUnique_isThomClassOfRank (R := R) (F := F') (E := E') hF).unique hmap hu'
  have hzero : bundleZeroSection F' E' ≫ Φ = TopCat.ofHom g ≫ bundleZeroSection F E := by
    refine TopCat.hom_ext (ContinuousMap.ext fun x ↦ ?_)
    change Φ ⟨x, 0⟩ = ⟨g x, 0⟩
    rw [hΦ, map_zero]
  have hc : cast (congrArg (fun k : ℕ ↦ (relativeSingularCohomology R (ModuleCat.of R R)
      (TopCat.of (TotalSpace F' E')) (range (zeroSection F' E'))ᶜ (k : ℤ) : Type u))
      (congrArg (2 * ·) hF)) (thomClass R F' E') =
      (relativeSingularCohomology.map R (ModuleCat.of R R) Φ
        (compl_zeroSection_subset_preimage hΦ) _).hom (thomClass R F E) := huniq.symm
  have he : ∀ {Z : Type u} (S : Set Z), (univ : Set Z)ᶜ ⊆ S := fun _ x hx ↦ (hx (mem_univ x)).elim
  refine (cast_map_relativeSingularCohomology _ _ (congrArg (2 * ·) hF) _).trans ?_
  refine (congrArg _ hc).trans ?_
  refine ((relativeSingularCohomology.map_comp_apply' R (g := bundleZeroSection F' E') (f := Φ)
    (he _) (compl_zeroSection_subset_preimage hΦ) (he _) _ _).symm).trans ?_
  refine (relativeSingularCohomology.map_congr_apply R hzero _ (he _) _ _).trans ?_
  exact relativeSingularCohomology.map_comp_apply' R (he _) (he _) (he _) _ _

/-- If `Φ : E' → E` covers `g : B' → B` and is a complex linear isomorphism on the fibres, and
`e(E') ≠ 0`, then `g^* e(E) ≠ 0`. -/
theorem map_eulerClass_ne_zero {Φ : TopCat.of (TotalSpace F' E') ⟶ TopCat.of (TotalSpace F E)}
    {g : C(B', B)} {φ : ∀ x, E' x ≃L[ℂ] E (g x)} (hΦ : ∀ x v, Φ ⟨x, v⟩ = ⟨g x, φ x v⟩)
    (hF : Module.finrank ℂ F' = Module.finrank ℂ F) (he : eulerClass R F' E' ≠ 0) :
    (relativeSingularCohomology.map R (ModuleCat.of R R) (TopCat.ofHom g) (A' := univᶜ)
      (A := univᶜ) (fun x hx ↦ (hx (mem_univ x)).elim) _).hom (eulerClass R F E) ≠ 0 :=
  fun h ↦ he ((cast_relativeSingularCohomology_eq_zero_iff (congrArg (2 * ·) hF) _).1
    ((cast_eulerClass_eq_map (R := R) hΦ hF).trans h))

omit [FiniteDimensional ℂ F] in
variable (F F' E E') in
/-- A linear isomorphism between fibres of complex vector bundles with finite-dimensional model
fibres, as a continuous linear isomorphism. -/
def fibreContinuousLinearEquiv (x : B') (y : B) (L : E' x ≃ₗ[ℂ] E y) : E' x ≃L[ℂ] E y :=
  let ψ' := (trivializationAt F' E' x).continuousLinearEquivAt ℂ x
    (mem_baseSet_trivializationAt F' E' x)
  let ψ := (trivializationAt F E y).continuousLinearEquivAt ℂ y
    (mem_baseSet_trivializationAt F E y)
  ψ'.trans ((ψ'.symm.toLinearEquiv.trans (L.trans ψ.toLinearEquiv)).toContinuousLinearEquiv.trans
    ψ.symm)

omit [FiniteDimensional ℂ F] in
/-- `fibreContinuousLinearEquiv` agrees with the linear isomorphism it is built from. -/
@[simp]
lemma fibreContinuousLinearEquiv_apply (x : B') (y : B) (L : E' x ≃ₗ[ℂ] E y) (v : E' x) :
    fibreContinuousLinearEquiv F E F' E' x y L v = L v := by
  simp [fibreContinuousLinearEquiv, Trivialization.symm_apply_apply_mk,
    mem_baseSet_trivializationAt]

end EulerMap

section FrameRatio

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open MMP MMP.UnderlyingSpace
open MMP.Resolution MMP.Flips.ResolutionInputs

variable {X : Scheme.{0}} {I : X.IdealSheafData} (c : BlowupChartData I)
  (D : (blowUp I).IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]

/-- At a point of the chart `Uⱼ` of `𝒪(D)^∨`, the ideal of `D` is generated by the germ of the
coordinate `bⱼ` of the canonical section. -/
lemma stalk_eq_span_germ_canonicalCoord (j : MMP.Modules.Chart (divisorDualSheaf D) 1)
    (y : blowUp I) (hy : y ∈ j.1.1) :
    IdealSheafData.stalk D y = Ideal.span
      {(blowUp I).presheaf.germ _ y hy (canonicalCoord D j)} := by
  rw [IdealSheafData.stalk_eq_map_germ _ y j.1 hy, ideal_eq_span_canonicalCoord D j j.1 le_rfl,
    Ideal.map_span, Set.image_singleton, TopCat.Presheaf.germ_res_apply]

/-- At a point of the chart `U_k = D₊(x_k)` of the blowup, the exceptional ideal is generated by
the germ of `π^*x_k`. -/
lemma stalk_exceptionalIdeal_eq_span_germ (hU : IsAffineOpen c.U) (k : Fin c.r) (y : blowUp I)
    (hy : y ∈ c.chart k) :
    IdealSheafData.stalk (exceptionalIdeal I) y = Ideal.span {((blowUpToBase I).stalkMap y
      (X.presheaf.germ c.U _ (blowUpToBase_mem_of_mem_chart c hy) (c.x k)))} := by
  have hyU := blowUpToBase_mem_of_mem_chart c hy
  have hy2 := hy
  rw [chart_eq_blowUpChartOpen c hU k, mem_blowUpChartOpen_iff I _ _ y hyU] at hy2
  rw [hy2]
  change Ideal.span {(blowUpToBase I).stalkMap y (X.presheaf.germ c.U (blowUpToBase I y) hyU
      ((X.presheaf.map (homOfLE (le_refl c.U)).op).hom (c.x k)))} = _
  rw [TopCat.Presheaf.germ_res_apply]

/-- **The coordinate of `s_D` is a unit multiple of `π^*x_k`.** At a point of `U_k ∩ Uⱼ`, when
`D` is the exceptional divisor, the germ of `bⱼ` is a unit times the germ of `π^*x_k`. -/
lemma exists_unit_germ_canonicalCoord_eq_mul (hU : IsAffineOpen c.U)
    (hDE : D = exceptionalIdeal I) (k : Fin c.r) (j : MMP.Modules.Chart (divisorDualSheaf D) 1)
    (y : blowUp I)
    (hyk : y ∈ c.chart k) (hyj : y ∈ j.1.1) :
    ∃ u : ((blowUp I).presheaf.stalk y)ˣ,
      (blowUp I).presheaf.germ _ y hyj (canonicalCoord D j) =
        u * (blowUp I).presheaf.germ _ y hyk (c.chartPullback k (c.x k)) := by
  rw [germ_chartPullback]
  refine Stacks.LineBundle.exists_unit_of_span_eq _ _ (fun t ht ↦
    (isRegular_iff_mem_nonZeroDivisors.2 (stalkMap_germ_mem_nonZeroDivisors c hU k y hyk)).left
      (show _ * t = _ * 0 by rw [ht, mul_zero])) ?_
  rw [← stalk_eq_span_germ_canonicalCoord D j y hyj, hDE,
    stalk_exceptionalIdeal_eq_span_germ c hU k y hyk]

/-- `s ∈ 𝒪(W)` is the ratio `bⱼ / π^*x_k` on `W ⊆ U_k ∩ Uⱼ` of the coordinate `bⱼ` of the
canonical section `s_D` in the chart `Uⱼ` of `𝒪(D)^∨` to the local equation `π^*x_k` of the
exceptional divisor on the chart `U_k` of the blowup, and is a unit. -/
def IsFrameRatio (k : Fin c.r) (j : MMP.Modules.Chart (divisorDualSheaf D) 1) (W : (blowUp I).Opens)
    (s : Γ(blowUp I, W)) : Prop :=
  ∃ (hk : W ≤ c.chart k) (hj : W ≤ j.1.1), IsUnit s ∧
    (blowUp I).presheaf.map (homOfLE hj).op (canonicalCoord D j) =
      s * (blowUp I).presheaf.map (homOfLE hk).op (c.chartPullback k (c.x k))

/-- Frame ratios exist near every point of `U_k ∩ Uⱼ`, when `D` is the exceptional divisor. -/
lemma exists_isFrameRatio (hU : IsAffineOpen c.U) (hDE : D = exceptionalIdeal I)
    (k : Fin c.r) (j : MMP.Modules.Chart (divisorDualSheaf D) 1) (y : blowUp I)
    (hyk : y ∈ c.chart k)
    (hyj : y ∈ j.1.1) :
    ∃ (W : (blowUp I).Opens) (s : Γ(blowUp I, W)), y ∈ W ∧ IsFrameRatio c D k j W s := by
  obtain ⟨u, hu⟩ := exists_unit_germ_canonicalCoord_eq_mul c D hU hDE k j y hyk hyj
  obtain ⟨W₁, hW₁, hyW₁, s₁, hs₁⟩ := TopCat.Presheaf.exists_le_germ_eq (blowUp I).presheaf u.1
    (show y ∈ c.chart k ⊓ j.1.1 from ⟨hyk, hyj⟩)
  obtain ⟨W₂, hW₂, hyW₂, s₂, hs₂⟩ :=
    TopCat.Presheaf.exists_le_germ_eq (blowUp I).presheaf u⁻¹.1 hyW₁
  have hk : W₂ ≤ c.chart k := hW₂.trans (hW₁.trans inf_le_left)
  have hj : W₂ ≤ j.1.1 := hW₂.trans (hW₁.trans inf_le_right)
  obtain ⟨W₃, hyW₃, i₃, i₃', h₃⟩ := TopCat.Presheaf.germ_eq _ y hyW₂ hyW₂
    ((blowUp I).presheaf.map (homOfLE hj).op (canonicalCoord D j))
    ((blowUp I).presheaf.map (homOfLE hW₂).op s₁ *
      (blowUp I).presheaf.map (homOfLE hk).op (c.chartPullback k (c.x k))) (by
        simpa only [map_mul, TopCat.Presheaf.germ_res_apply, hs₁] using hu)
  obtain ⟨W₄, hyW₄, i₄, i₄', h₄⟩ := TopCat.Presheaf.germ_eq _ y hyW₂ hyW₂
    ((blowUp I).presheaf.map (homOfLE hW₂).op s₁ * s₂) 1 (by
      simp only [map_mul, map_one, TopCat.Presheaf.germ_res_apply, hs₁, hs₂, Units.mul_inv])
  set W := W₃ ⊓ W₄
  have hW₃ : W ≤ W₂ := inf_le_left.trans (leOfHom i₃)
  refine ⟨W, (blowUp I).presheaf.map (homOfLE (hW₃.trans hW₂)).op s₁, ⟨hyW₃, hyW₄⟩,
    hW₃.trans hk, hW₃.trans hj, ?_, ?_⟩
  · refine IsUnit.of_mul_eq_one ((blowUp I).presheaf.map (homOfLE hW₃).op s₂) ?_
    refine TopCat.Presheaf.section_ext (blowUp I).sheaf _ _ _ fun z hz ↦ ?_
    change (blowUp I).presheaf.germ W z hz _ = (blowUp I).presheaf.germ W z hz _
    simpa only [map_mul, map_one, TopCat.Presheaf.germ_res_apply] using
      congrArg ((blowUp I).presheaf.germ W₄ z hz.2) h₄
  · refine TopCat.Presheaf.section_ext (blowUp I).sheaf _ _ _ fun z hz ↦ ?_
    change (blowUp I).presheaf.germ W z hz _ = (blowUp I).presheaf.germ W z hz _
    simpa only [map_mul, TopCat.Presheaf.germ_res_apply] using
      congrArg ((blowUp I).presheaf.germ W₃ z hz.1) h₃

end FrameRatio

section FrameRatioEval

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open MMP MMP.UnderlyingSpace
open MMP.Resolution MMP.Flips.ResolutionInputs

variable {X : Scheme.{0}} {I : X.IdealSheafData} (c : BlowupChartData I)
  (D : (blowUp I).IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
  [(blowUp I).Over (Spec (.of ℂ))]

omit [(blowUp I).Over (Spec (.of ℂ))] in
/-- The germ at a point of `W` of the frame-ratio relation `bⱼ = s · π^*x_k`. -/
lemma germ_canonicalCoord_eq_mul_of_isFrameRatio {k : Fin c.r}
    {j : MMP.Modules.Chart (divisorDualSheaf D) 1}
    {W : (blowUp I).Opens} {s : Γ(blowUp I, W)} (h : IsFrameRatio c D k j W s) (y : blowUp I)
    (hy : y ∈ W) :
    (blowUp I).presheaf.germ _ y (h.2.1 hy) (canonicalCoord D j) =
      (blowUp I).presheaf.germ _ y hy s *
        (blowUp I).presheaf.germ _ y (h.1 hy) (c.chartPullback k (c.x k)) := by
  obtain ⟨hk, hj, -, he⟩ := h
  simpa only [map_mul, TopCat.Presheaf.germ_res_apply] using
    congrArg ((blowUp I).presheaf.germ W y hy) he

/-- The value at a point of `W` of a frame ratio is nonzero. -/
lemma eval_ne_zero_of_isFrameRatio {k : Fin c.r} {j : MMP.Modules.Chart (divisorDualSheaf D) 1}
    {W : (blowUp I).Opens} {s : Γ(blowUp I, W)} (h : IsFrameRatio c D k j W s)
    (q : UnderlyingSpace ℂ (blowUp I)) (hq : ⊤ ≤ q.toHom ⁻¹ᵁ W) : eval q hq s ≠ 0 := by
  rw [← evalRingHom_apply]
  exact (h.2.2.1.map (evalRingHom q hq)).ne_zero

/-- **Frame ratios on overlaps.** At a point `q` of `W ∩ W'`, for frame ratios `s = bⱼ / π^*x_k`
on `W` and `s' = bⱼ' / π^*x_k'` on `W'`, `s(q) = gⱼⱼ'(q) · (x_k' / x_k)(q) · s'(q)`, with `gⱼⱼ'`
the transition function of `𝒪(D)^∨`. -/
lemma eval_eq_transition_mul_of_isFrameRatio (hU : IsAffineOpen c.U) {k k' : Fin c.r}
    {j j' : MMP.Modules.Chart (divisorDualSheaf D) 1} {W W' : (blowUp I).Opens} {s : Γ(blowUp I, W)}
    {s' : Γ(blowUp I, W')} (h : IsFrameRatio c D k j W s) (h' : IsFrameRatio c D k' j' W' s')
    (q : UnderlyingSpace ℂ (blowUp I)) (hq : ⊤ ≤ q.toHom ⁻¹ᵁ W) (hq' : ⊤ ≤ q.toHom ⁻¹ᵁ W') :
    MMP.Modules.transition j' j q 0 0 *
        eval q (hq.trans (Scheme.Hom.preimage_mono _ h.1)) (chartFraction c k k') *
        eval q hq' s' = eval q hq s := by
  set y := q.toHom (IsLocalRing.closedPoint ℂ)
  have hyW : y ∈ W := (top_le_preimage_iff q W).1 hq
  have hyW' : y ∈ W' := (top_le_preimage_iff q W').1 hq'
  have hyk : y ∈ c.chart k := h.1 hyW
  have hyj : y ∈ j.1.1 := h.2.1 hyW
  have hyj' : y ∈ j'.1.1 := h'.2.1 hyW'
  -- a basic open `D(a) ∋ y` of the chart `j'` inside the chart `j`
  obtain ⟨a, ha, hya⟩ := j'.1.2.exists_basicOpen_le ⟨_, hyj⟩ hyj'
  have hyjj : y ∈ (blowUp I).basicOpen a := hya
  set T := MMP.Modules.transitionSection j' j a ha 0 0
  -- the transition relation `bⱼ = gⱼⱼ' bⱼ'`, in the stalk
  have htr : (blowUp I).presheaf.germ _ y hyj (canonicalCoord D j) =
      (blowUp I).presheaf.germ _ y hyjj T *
        (blowUp I).presheaf.germ _ y hyj' (canonicalCoord D j') := by
    simpa only [map_mul, TopCat.Presheaf.germ_res_apply] using
      congrArg ((blowUp I).presheaf.germ _ y hyjj) (map_canonicalCoord_eq_mul D j j' a ha)
  -- the stalk relation `s = gⱼⱼ' · (x_k' / x_k) · s'`
  have hstalk : (blowUp I).presheaf.germ _ y hyW s =
      (blowUp I).presheaf.germ _ y hyjj T *
        (blowUp I).presheaf.germ _ y hyk (chartFraction c k k') *
          (blowUp I).presheaf.germ _ y hyW' s' := by
    refine (mul_cancel_right_mem_nonZeroDivisors
      (stalkMap_germ_mem_nonZeroDivisors c hU k y hyk)).1 ?_
    have e1 := germ_canonicalCoord_eq_mul_of_isFrameRatio c D h y hyW
    have e2 := germ_canonicalCoord_eq_mul_of_isFrameRatio c D h' y hyW'
    rw [germ_chartPullback] at e1 e2
    rw [← e1, htr, e2, ← germ_chartFraction_mul c k k' y hyk]
    ring
  have hqa : ⊤ ≤ q.toHom ⁻¹ᵁ (blowUp I).basicOpen a := (top_le_preimage_iff q _).2 hya
  have hW'' : ⊤ ≤ q.toHom ⁻¹ᵁ ((blowUp I).basicOpen a ⊓ c.chart k ⊓ W') :=
    le_inf (le_inf hqa (hq.trans (Scheme.Hom.preimage_mono _ h.1))) hq'
  have hev := eval_eq_of_germ_eq q hq hW'' s
    ((blowUp I).presheaf.map (homOfLE (inf_le_left.trans inf_le_left)).op T *
      (blowUp I).presheaf.map (homOfLE (inf_le_left.trans inf_le_right)).op
        (chartFraction c k k') *
      (blowUp I).presheaf.map (homOfLE inf_le_right).op s') (by
        simpa only [map_mul, TopCat.Presheaf.germ_res_apply] using hstalk)
  rw [hev, ← evalRingHom_apply q hW'', map_mul, map_mul, evalRingHom_apply, evalRingHom_apply,
    evalRingHom_apply, eval_restrict, eval_restrict, eval_restrict,
    MMP.Modules.transition_eq_of_basicOpen j' j a ha q hqa]
  rfl

end FrameRatioEval

section TautologicalToLineBundle

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Bundle
open MMP MMP.UnderlyingSpace
open MMP.Resolution MMP.Flips.ResolutionInputs

variable {X : Scheme.{0}} {I : X.IdealSheafData} [(blowUp I).Over (Spec (.of ℂ))] {n : ℕ}
  {U : X.Opens} {x : Fin (n + 1) → Γ(X, U)}
  {hf : ∀ (W : X.affineOpens) (h : W.1 ≤ U), I.ideal W = Ideal.span
    (Set.range fun i ↦ (X.presheaf.map (homOfLE h).op).hom (x i))}
  (D : (blowUp I).IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]

variable (hf) in
/-- The chart datum of generators `x_0, …, x_n` of the centre on `U`. -/
abbrev chartDatum : BlowupChartData I := ⟨U, n + 1, x, hf⟩

variable (hU : IsAffineOpen U) (hDE : D = exceptionalIdeal I)
  (g : C(lineProjections n, UnderlyingSpace ℂ (blowUp I)))
  (hg : ∀ (P : lineProjections n) (k : Fin (n + 1))
    (hk : ⊤ ≤ (g P).toHom ⁻¹ᵁ (chartDatum hf).chart k),
    P.1 k k ≠ 0 ∧ ∀ j, P.1 j k / P.1 k k = eval (g P) hk (chartFraction (chartDatum hf) k j))
  (hg' : ∀ P : lineProjections n, ∃ k : Fin (n + 1), ⊤ ≤ (g P).toHom ⁻¹ᵁ (chartDatum hf).chart k)

include hU hDE hg' in
/-- At every point `g P` there is a frame ratio: a chart `U_k` of the blowup, a chart `Uⱼ` of
`𝒪(D)` and a unit `s = bⱼ / π^*x_k` on a neighbourhood `W` of `g P`. -/
lemma exists_isFrameRatio_apply (P : lineProjections n) :
    ∃ (k : Fin (n + 1)) (j : MMP.Modules.Chart (divisorDualSheaf D) 1) (W : (blowUp I).Opens)
      (s : Γ(blowUp I, W)),
      ⊤ ≤ (g P).toHom ⁻¹ᵁ W ∧ IsFrameRatio (chartDatum hf) D k j W s := by
  obtain ⟨k, hk⟩ := hg' P
  set j := MMP.Modules.chartAt (divisorDualSheaf D) 1 (g P)
  obtain ⟨W, s, hyW, hs⟩ := exists_isFrameRatio (chartDatum hf) D hU hDE k j _
    ((top_le_preimage_iff _ _).1 hk) ((top_le_preimage_iff _ _).1
      (MMP.Modules.mem_chartBase_chartAt (divisorDualSheaf D) 1 (g P)))
  exact ⟨k, j, W, s, (top_le_preimage_iff _ _).2 hyW, hs⟩

/-- The chart of the blowup of the chosen frame ratio at `g P`. -/
def frameChart (P : lineProjections n) : Fin (n + 1) :=
  (exists_isFrameRatio_apply D hU hDE g hg' P).choose

/-- The chart of `𝒪(D)^∨` of the chosen frame ratio at `g P`. -/
def frameIndex (P : lineProjections n) : MMP.Modules.Chart (divisorDualSheaf D) 1 :=
  (exists_isFrameRatio_apply D hU hDE g hg' P).choose_spec.choose

/-- The open of the chosen frame ratio at `g P`. -/
def frameOpen (P : lineProjections n) : (blowUp I).Opens :=
  (exists_isFrameRatio_apply D hU hDE g hg' P).choose_spec.choose_spec.choose

/-- The chosen frame ratio at `g P`. -/
def frameSection (P : lineProjections n) : Γ(blowUp I, frameOpen D hU hDE g hg' P) :=
  (exists_isFrameRatio_apply D hU hDE g hg' P).choose_spec.choose_spec.choose_spec.choose

/-- The point `g P` lies in the open of the chosen frame ratio at `g P`. -/
lemma top_le_preimage_frameOpen (P : lineProjections n) :
    ⊤ ≤ (g P).toHom ⁻¹ᵁ frameOpen D hU hDE g hg' P :=
  (exists_isFrameRatio_apply D hU hDE g hg' P).choose_spec.choose_spec.choose_spec.choose_spec.1

/-- The chosen section at `g P` is a frame ratio for the chosen charts on the chosen open. -/
lemma isFrameRatio_frameSection (P : lineProjections n) :
    IsFrameRatio (chartDatum hf) D (frameChart D hU hDE g hg' P) (frameIndex D hU hDE g hg' P)
      (frameOpen D hU hDE g hg' P) (frameSection D hU hDE g hg' P) :=
  (exists_isFrameRatio_apply D hU hDE g hg' P).choose_spec.choose_spec.choose_spec.choose_spec.2

/-- The point `g P` lies in the base of the chosen chart of `𝒪(D)^∨`. -/
lemma mem_chartBase_frameIndex (P : lineProjections n) :
    g P ∈ MMP.Modules.chartBase (frameIndex D hU hDE g hg' P) :=
  (top_le_preimage_frameOpen D hU hDE g hg' P).trans
    (Scheme.Hom.preimage_mono _ (isFrameRatio_frameSection D hU hDE g hg' P).2.1)

/-- The point `g P` lies in the chosen chart of the blowup. -/
lemma top_le_preimage_frameChart (P : lineProjections n) :
    ⊤ ≤ (g P).toHom ⁻¹ᵁ (chartDatum hf).chart (frameChart D hU hDE g hg' P) :=
  (top_le_preimage_frameOpen D hU hDE g hg' P).trans
    (Scheme.Hom.preimage_mono _ (isFrameRatio_frameSection D hU hDE g hg' P).1)

include hg in
/-- The coefficient `λ_k(v) s(g P)` of the map of the tautological line at `P` to `𝒪(D)` at
`g P`, in the chosen charts, is nonzero. -/
lemma frameCoefficient_ne_zero (P : lineProjections n) :
    P.1 (frameChart D hU hDE g hg' P) (chartIndex P) / P.1 (chartIndex P) (chartIndex P) *
      eval (g P) (top_le_preimage_frameOpen D hU hDE g hg' P)
        (frameSection D hU hDE g hg' P) ≠ 0 := by
  set k := frameChart D hU hDE g hg' P
  set i := chartIndex P
  have hk := (hg P k (top_le_preimage_frameChart D hU hDE g hg' P)).1
  have hi := chartIndex_diag_ne_zero P
  have hki : P.1 k i ≠ 0 := by
    intro h0
    have := lineProjections_mul_mul_eq P.2 k i i k
    rw [h0, zero_mul] at this
    exact mul_ne_zero hk hi this.symm
  exact mul_ne_zero (div_ne_zero hki hi)
    (eval_ne_zero_of_isFrameRatio (chartDatum hf) D
      (isFrameRatio_frameSection D hU hDE g hg' P) _ _)

/-- The fibre of the tautological bundle at `P` is `ℂ`, through the coordinate of its
trivializations. -/
def tautologicalFibreLinearEquiv (P : lineProjections n) : TautologicalBundle n P ≃ₗ[ℂ] ℂ where
  toFun v := v
  invFun v := v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The map of the tautological line at `P` to the fibre of `𝒪(D)(ℂ)` at `g P`, as a linear
isomorphism: in the chosen charts `U_k` of `ℙⁿ` and `Uⱼ` of `𝒪(D)^∨`, `v ↦ λ_k(v) s(g P)`. -/
def tautologicalFibreEquiv (P : lineProjections n) :
    TautologicalBundle n P ≃ₗ[ℂ] MMP.Modules.Fibre (divisorDualSheaf D) 1 (g P) :=
  have hb : Function.Bijective (MMP.Modules.fibreCoord (frameIndex D hU hDE g hg' P) (g P)) := by
    rw [show ⇑(MMP.Modules.fibreCoord (frameIndex D hU hDE g hg' P) (g P)) =
      MMP.Modules.fibreEquiv _ (g P) (mem_chartBase_frameIndex D hU hDE g hg' P) from
      funext fun p ↦ MMP.Modules.fibreCoord_apply _ (g P)
        (mem_chartBase_frameIndex D hU hDE g hg' P) p]
    exact (MMP.Modules.fibreEquiv _ _ _).bijective
  (((tautologicalFibreLinearEquiv P).trans
    (LinearEquiv.smulOfNeZero ℂ ℂ _ (frameCoefficient_ne_zero D hU hDE g hg hg' P))).trans
    (LinearEquiv.funUnique (Fin 1) ℂ ℂ).symm).trans (LinearEquiv.ofBijective _ hb).symm

end TautologicalToLineBundle

section TautologicalToLineBundleTotal

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Bundle
open MMP MMP.UnderlyingSpace
open MMP.Resolution MMP.Flips.ResolutionInputs

variable {X : Scheme.{0}} {I : X.IdealSheafData} [(blowUp I).Over (Spec (.of ℂ))] {n : ℕ}
  {U : X.Opens} {x : Fin (n + 1) → Γ(X, U)}
  {hf : ∀ (W : X.affineOpens) (h : W.1 ≤ U), I.ideal W = Ideal.span
    (Set.range fun i ↦ (X.presheaf.map (homOfLE h).op).hom (x i))}
  (D : (blowUp I).IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
  (hU : IsAffineOpen U) (hDE : D = exceptionalIdeal I)
  (g : C(lineProjections n, UnderlyingSpace ℂ (blowUp I)))
  (hg : ∀ (P : lineProjections n) (k : Fin (n + 1))
    (hk : ⊤ ≤ (g P).toHom ⁻¹ᵁ (chartDatum hf).chart k),
    P.1 k k ≠ 0 ∧ ∀ j, P.1 j k / P.1 k k = eval (g P) hk (chartFraction (chartDatum hf) k j))
  (hg' : ∀ P : lineProjections n, ∃ k : Fin (n + 1), ⊤ ≤ (g P).toHom ⁻¹ᵁ (chartDatum hf).chart k)

/-- In the chart `frameIndex` of `𝒪(D)^∨`, the image of `v` under `tautologicalFibreEquiv` has
coordinate `P_{k,i} / P_{i,i} · s(g P) · λ(v)`, where `k` is `frameChart P`, `i` is
`chartIndex P`, `s` is `frameSection P` and `λ(v)` is the `fibreCoord` of `v`. -/
lemma fibreCoord_tautologicalFibreEquiv (P : lineProjections n) (v : TautologicalBundle n P) :
    MMP.Modules.fibreCoord (frameIndex D hU hDE g hg' P) (g P)
        (tautologicalFibreEquiv D hU hDE g hg hg' P v) =
      fun _ ↦ P.1 (frameChart D hU hDE g hg' P) (chartIndex P) /
        P.1 (chartIndex P) (chartIndex P) *
        eval (g P) (top_le_preimage_frameOpen D hU hDE g hg' P)
          (frameSection D hU hDE g hg' P) *
            fibreCoord (⟨P, v⟩ : TotalSpace ℂ (TautologicalBundle n)) := by
  have key : ∀ (f : MMP.Modules.Fibre (divisorDualSheaf D) 1 (g P) →ₗ[ℂ] (Fin 1 → ℂ))
      (hb : Function.Bijective f) w,
      f ((LinearEquiv.ofBijective f hb).symm w) = w :=
    fun f hb w ↦ (LinearEquiv.ofBijective f hb).apply_symm_apply w
  simp only [tautologicalFibreEquiv, LinearEquiv.trans_apply]
  rw [key]
  rfl

/-- A point of `E(ℂ)` over `y ∈ Uᵢ(ℂ)` is `φᵢ⁻¹(y, x⁽ⁱ⁾(p))`. -/
lemma eq_chartInv_of_mapFun_eq {E : (blowUp I).Modules} [E.IsQuasicoherent] {r : ℕ}
    (i : MMP.Modules.Chart E r) {p : UnderlyingSpace ℂ (totalSpace E)}
    {y : UnderlyingSpace ℂ (blowUp I)} (hp : mapFun (proj E) p = y)
    (hy : ⊤ ≤ y.toHom ⁻¹ᵁ i.1.1) : p = MMP.Modules.chartInv i y hy (MMP.Modules.coord i p) := by
  subst hp
  exact (MMP.Modules.chartInv_mapFun_proj_coord i p hy).symm

/-- **The map of the tautological bundle to `𝒪(D)(ℂ)`, in any chart.** For a frame ratio
`s' = bⱼ' / π^*x_k'` at `g P`, the image of `⟨P, v⟩` has coordinate `λ_k'(v) s'(g P)` in the
chart `Uⱼ'` of `𝒪(D)^∨`, `λ_k'` the coordinate of the chart `U_k'` of `ℙⁿ`. -/
lemma coord_tautologicalFibreEquiv {P : lineProjections n} (v : TautologicalBundle n P)
    {k' : Fin (n + 1)} {j' : MMP.Modules.Chart (divisorDualSheaf D) 1} {W' : (blowUp I).Opens}
    {s' : Γ(blowUp I, W')}
    (h' : IsFrameRatio (chartDatum hf) D k' j' W' s') (hq' : ⊤ ≤ (g P).toHom ⁻¹ᵁ W') :
    MMP.Modules.coord j' (tautologicalFibreEquiv D hU hDE g hg hg' P v).1 =
      fun _ ↦ ((tautologicalCore n).localTriv k' ⟨P, v⟩).2 * eval (g P) hq' s' := by
  set q := (tautologicalFibreEquiv D hU hDE g hg hg' P v)
  set k := frameChart D hU hDE g hg' P
  set j := frameIndex D hU hDE g hg' P
  set i := chartIndex P
  have hqπ : mapFun (proj (divisorDualSheaf D)) q.1 = g P := q.2
  have hj := mem_chartBase_frameIndex D hU hDE g hg' P
  have hj' : g P ∈ MMP.Modules.chartBase j' := hq'.trans (Scheme.Hom.preimage_mono _ h'.2.1)
  have hk' : ⊤ ≤ (g P).toHom ⁻¹ᵁ (chartDatum hf).chart k' :=
    hq'.trans (Scheme.Hom.preimage_mono _ h'.1)
  have hc := MMP.Modules.coord_eq_transition_mulVec j j' q.1
    (MMP.Modules.top_le_preimage_proj_inf ⟨by rwa [hqπ], by rwa [hqπ]⟩)
  have hcj : MMP.Modules.coord j q.1 = _ :=
    (MMP.Modules.fibreCoord_apply j (g P) hj q).symm.trans
      (fibreCoord_tautologicalFibreEquiv D hU hDE g hg hg' P v)
  rw [hcj, hqπ] at hc
  rw [hc]
  funext a
  have E1 := eval_eq_transition_mul_of_isFrameRatio (chartDatum hf) D hU h'
    (isFrameRatio_frameSection D hU hDE g hg' P) (g P) hq'
    (top_le_preimage_frameOpen D hU hDE g hg' P)
  have E2 := (hg P k' hk').2 k
  have E3 := rankOne_ratio_mul (chartIndex_diag_ne_zero P) (hg P k' hk').1
    (fibreCoord (⟨P, v⟩ : TotalSpace ℂ (TautologicalBundle n))) k
  rw [← E2] at E1
  rw [localTriv_snd_tautological, ← E1]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, Fin.fin_one_eq_zero a]
  linear_combination (MMP.Modules.transition j j' (g P) 0 0 *
    eval (g P) (top_le_preimage_frameOpen D hU hDE g hg' P) (frameSection D hU hDE g hg' P)) * E3

/-- The map `O(-1) → 𝒪(D)(ℂ)` of total spaces over `g`, fibrewise
`MMP.Topology.tautologicalFibreEquiv`. -/
def tautologicalToLineBundle (z : TotalSpace ℂ (TautologicalBundle n)) :
    UnderlyingSpace ℂ (totalSpace (divisorDualSheaf D)) :=
  (tautologicalFibreEquiv D hU hDE g hg hg' z.proj z.2).1

/-- `tautologicalToLineBundle` lies over `g`: it sends the fibre over `P` to the fibre over
`g P`. -/
lemma mapFun_proj_tautologicalToLineBundle (z : TotalSpace ℂ (TautologicalBundle n)) :
    mapFun (proj (divisorDualSheaf D)) (tautologicalToLineBundle D hU hDE g hg hg' z) = g z.proj :=
  (tautologicalFibreEquiv D hU hDE g hg hg' z.proj z.2).2

/-- **The map `O(-1) → 𝒪(D)(ℂ)` is continuous**: near a point, in the charts `U_k` of `ℙⁿ` and
`Uⱼ` of `𝒪(D)^∨` of a frame ratio `s`, it is `(P, v) ↦ φⱼ⁻¹(g P, λ_k(v) s(g P))`. -/
theorem continuous_tautologicalToLineBundle :
    Continuous (tautologicalToLineBundle D hU hDE g hg hg') := by
  refine continuous_iff_continuousAt.2 fun z₀ ↦ ?_
  obtain ⟨k, j, W, s, hs, hW₀⟩ : ∃ (k : Fin (n + 1)) (j : MMP.Modules.Chart (divisorDualSheaf D) 1)
      (W : (blowUp I).Opens) (s : Γ(blowUp I, W)), IsFrameRatio (chartDatum hf) D k j W s ∧
        ⊤ ≤ (g z₀.proj).toHom ⁻¹ᵁ W :=
    ⟨_, _, _, _, isFrameRatio_frameSection D hU hDE g hg' z₀.proj,
      top_le_preimage_frameOpen D hU hDE g hg' z₀.proj⟩
  have hgp : Continuous fun z : TotalSpace ℂ (TautologicalBundle n) ↦ g z.proj :=
    g.continuous.comp (FiberBundle.continuous_proj ℂ _)
  set N : Set (TotalSpace ℂ (TautologicalBundle n)) := {z | ⊤ ≤ (g z.proj).toHom ⁻¹ᵁ W}
  have hN : IsOpen N := (isOpen_setOf_le_preimage W).preimage hgp
  have hNj : ∀ z : N, ⊤ ≤ (g z.1.proj).toHom ⁻¹ᵁ j.1.1 :=
    fun z ↦ z.2.trans (Scheme.Hom.preimage_mono _ hs.2.1)
  have hNk : ∀ z : N, z.1 ∈ ((tautologicalCore n).localTriv k).source := fun z ↦
    ((tautologicalCore n).mem_localTriv_source k z.1).2
      (hg z.1.proj k (z.2.trans (Scheme.Hom.preimage_mono _ hs.1))).1
  have hcont : Continuous fun z : N ↦ MMP.Modules.chartInv j (g z.1.proj) (hNj z)
      (fun _ ↦ ((tautologicalCore n).localTriv k z.1).2 * eval (g z.1.proj) z.2 s) := by
    have hlam : Continuous fun z : N ↦ ((tautologicalCore n).localTriv k z.1).2 :=
      continuous_snd.comp (((tautologicalCore n).localTriv k).continuousOn.comp_continuous
        continuous_subtype_val hNk)
    have hev : Continuous fun z : N ↦ eval (g z.1.proj) z.2 s := by
      have h1 : Continuous fun z : N ↦ (⟨g z.1.proj, z.2⟩ :
          {p : UnderlyingSpace ℂ (blowUp I) // ⊤ ≤ p.toHom ⁻¹ᵁ W}) :=
        (hgp.comp continuous_subtype_val).subtype_mk _
      have h2 := (continuous_eval W s).comp h1
      exact h2
    have hb : Continuous fun z : N ↦
        (⟨g z.1.proj, hNj z⟩ : {y : UnderlyingSpace ℂ (blowUp I) //
          ⊤ ≤ y.toHom ⁻¹ᵁ j.1.1}) :=
      (hgp.comp continuous_subtype_val).subtype_mk _
    have hψ : Continuous fun z : N ↦
        ((⟨g z.1.proj, hNj z⟩ : {y : UnderlyingSpace ℂ (blowUp I) //
          ⊤ ≤ y.toHom ⁻¹ᵁ j.1.1}),
          (fun _ ↦ ((tautologicalCore n).localTriv k z.1).2 * eval (g z.1.proj) z.2 s :
            Fin 1 → ℂ)) :=
      hb.prodMk (continuous_pi fun _ ↦ hlam.mul hev)
    have h3 := (MMP.Modules.continuous_chartInv j).comp hψ
    exact h3
  have heq : ∀ z : N, tautologicalToLineBundle D hU hDE g hg hg' z.1 =
      MMP.Modules.chartInv j (g z.1.proj) (hNj z)
        (fun _ ↦ ((tautologicalCore n).localTriv k z.1).2 * eval (g z.1.proj) z.2 s) := fun z ↦
    (eq_chartInv_of_mapFun_eq j (mapFun_proj_tautologicalToLineBundle D hU hDE g hg hg' z.1)
      (hNj z)).trans (congrArg (MMP.Modules.chartInv j (g z.1.proj) (hNj z))
        (coord_tautologicalFibreEquiv D hU hDE g hg hg' z.1.2 hs z.2))
  have hon : ContinuousOn (tautologicalToLineBundle D hU hDE g hg hg') N :=
    continuousOn_iff_continuous_domRestrict.2 ((continuous_congr fun z ↦ (heq z).symm).1 hcont)
  exact hon.continuousAt (hN.mem_nhds hW₀)

end TautologicalToLineBundleTotal

section TautologicalToDatum

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Bundle Set
open MMP MMP.UnderlyingSpace
open MMP.Resolution MMP.Flips.ResolutionInputs

variable {X : Scheme.{0}} {I : X.IdealSheafData} [(blowUp I).Over (Spec (.of ℂ))] {n : ℕ}
  {U : X.Opens} {x : Fin (n + 1) → Γ(X, U)}
  {hf : ∀ (W : X.affineOpens) (h : W.1 ≤ U), I.ideal W = Ideal.span
    (Set.range fun i ↦ (X.presheaf.map (homOfLE h).op).hom (x i))}
  (D : (blowUp I).IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
  [D.subscheme.Over (Spec (.of ℂ))]
  [D.subschemeι.IsOver (Spec (.of ℂ))]

variable (hU : IsAffineOpen U) (hDE : D = exceptionalIdeal I)
  (g : C(lineProjections n, UnderlyingSpace ℂ (blowUp I)))
  (hg : ∀ (P : lineProjections n) (k : Fin (n + 1))
    (hk : ⊤ ≤ (g P).toHom ⁻¹ᵁ (chartDatum hf).chart k),
    P.1 k k ≠ 0 ∧ ∀ j, P.1 j k / P.1 k k = eval (g P) hk (chartFraction (chartDatum hf) k j))
  (hg' : ∀ P : lineProjections n, ∃ k : Fin (n + 1), ⊤ ≤ (g P).toHom ⁻¹ᵁ (chartDatum hf).chart k)
  (hgE : ∀ P, g P ∈ (divisorOrientationDatum D).nbhd)

include hgE in
/-- `tautologicalToLineBundle` takes values over the neighbourhood of the orientation datum of
`D`. -/
lemma mapFun_proj_tautologicalToLineBundle_mem_nbhd (z : TotalSpace ℂ (TautologicalBundle n)) :
    mapFun (proj (divisorDualSheaf D)) (tautologicalToLineBundle D hU hDE g hg hg' z) ∈
      (divisorOrientationDatum D).nbhd :=
  (congrArg (· ∈ (divisorOrientationDatum D).nbhd)
    (mapFun_proj_tautologicalToLineBundle D hU hDE g hg hg' z)).mpr (hgE z.proj)

/-- The map `ℙⁿ(ℂ) → V`, `P ↦ g P`, to the neighbourhood `V` of the orientation datum of `D`. -/
def tautologicalToDatumBase : C(lineProjections n, (divisorOrientationDatum D).nbhd) :=
  ⟨fun P ↦ ⟨g P, hgE P⟩, g.continuous.subtype_mk _⟩

/-- The map of the tautological line at `P` to the fibre at `g P` of the bundle `Q = 𝒪(D)(ℂ)|_V`
of the orientation datum of `D`, as a continuous linear isomorphism. -/
def tautologicalToDatumFibre (P : lineProjections n) :
    TautologicalBundle n P ≃L[ℂ]
      (divisorOrientationDatum D).Q (tautologicalToDatumBase D g hgE P) :=
  fibreContinuousLinearEquiv (divisorOrientationDatum D).F (divisorOrientationDatum D).Q ℂ
    (TautologicalBundle n) P (tautologicalToDatumBase D g hgE P)
    (tautologicalFibreEquiv D hU hDE g hg hg' P)

/-- **The bundle map `O(-1) → Q` over `ℙⁿ(ℂ) → V`**, `Q = 𝒪(D)(ℂ)|_V` the bundle of the
orientation datum of `D`: on the fibres it is `MMP.Topology.tautologicalFibreEquiv`. -/
def tautologicalToDatum : TopCat.of (TotalSpace ℂ (TautologicalBundle n)) ⟶
    TopCat.of (TotalSpace (divisorOrientationDatum D).F (divisorOrientationDatum D).Q) :=
  TopCat.ofHom ⟨fun z ↦ ⟨tautologicalToDatumBase D g hgE z.proj,
      tautologicalToDatumFibre D hU hDE g hg hg' hgE z.proj z.2⟩, by
    have hq : ∀ z : TotalSpace ℂ (TautologicalBundle n),
        (divisorOrientationDatum D).quot ⟨tautologicalToLineBundle D hU hDE g hg hg' z,
          mapFun_proj_tautologicalToLineBundle_mem_nbhd D hU hDE g hg hg' hgE z⟩ =
        ⟨tautologicalToDatumBase D g hgE z.proj,
          tautologicalToDatumFibre D hU hDE g hg hg' hgE z.proj z.2⟩ := fun z ↦ by
      have e := fibreContinuousLinearEquiv_apply (F := (divisorOrientationDatum D).F)
        (E := (divisorOrientationDatum D).Q) (F' := ℂ) (E' := TautologicalBundle n) z.proj
        (tautologicalToDatumBase D g hgE z.proj)
        (tautologicalFibreEquiv D hU hDE g hg hg' z.proj) z.2
      refine (divisorOrientationDatum_quot_mk D (tautologicalToDatumBase D g hgE z.proj)
        (tautologicalFibreEquiv D hU hDE g hg hg' z.proj z.2) _).trans ?_
      unfold tautologicalToDatumFibre
      rw [e]
      rfl
    have hc := (divisorOrientationDatum D).continuous_quot.comp
      ((continuous_tautologicalToLineBundle D hU hDE g hg hg').subtype_mk
        (mapFun_proj_tautologicalToLineBundle_mem_nbhd D hU hDE g hg hg' hgE))
    exact (continuous_congr hq).1 hc⟩

include hU hDE hg hg' in
/-- **The Euler class of the orientation datum of the exceptional divisor restricted to
`ℙⁿ(ℂ)`.** For `n ≥ 1`, the pull-back along `g : ℙⁿ(ℂ) → V` of the Euler class of the bundle
`Q = 𝒪(D)(ℂ)|_V` of the orientation datum of `D` is nonzero. -/
theorem map_tautologicalToDatumBase_eulerClass_ne_zero (hn : 1 ≤ n) :
    (relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom (tautologicalToDatumBase D g hgE)) (A' := univᶜ) (A := univᶜ)
      (fun x hx ↦ (hx (mem_univ x)).elim) _).hom
      (eulerClass ℚ (divisorOrientationDatum D).F (divisorOrientationDatum D).Q) ≠ 0 :=
  map_eulerClass_ne_zero (Φ := tautologicalToDatum D hU hDE g hg hg' hgE)
    (fun _ _ ↦ rfl) (by rw [Module.finrank_self, (divisorOrientationDatum D).finrank_F])
    (eulerClass_tautologicalBundle_ne_zero hn)

end TautologicalToDatum

section FibreEuler

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Bundle Set
open MMP MMP.UnderlyingSpace
open MMP.Resolution MMP.Flips.ResolutionInputs

variable {X : Scheme.{0}} {I : X.IdealSheafData} [X.Over (Spec (.of ℂ))]
  [(blowUp I).Over (Spec (.of ℂ))] [(blowUpToBase I).IsOver (Spec (.of ℂ))]
  (D : (blowUp I).IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]

/-- **The fibres of the blowup over the centre lie in the exceptional divisor**: a point of
`Bl_I X(ℂ)` over a point `t` of the centre lies in `D(ℂ)`, for `D` the exceptional divisor. -/
lemma mem_range_map_subschemeι_of_mapFun_eq (hDE : D = exceptionalIdeal I)
    [D.subscheme.Over (Spec (.of ℂ))]
    [D.subschemeι.IsOver (Spec (.of ℂ))] {t : UnderlyingSpace ℂ X}
    (htI : t.toHom (IsLocalRing.closedPoint ℂ) ∈ I.support) {p : UnderlyingSpace ℂ (blowUp I)}
    (hp : mapFun (blowUpToBase I) p = t) :
    p ∈ range (UnderlyingSpace.map (K := ℂ) D.subschemeι) := by
  change p ∈ range (mapFun (K := ℂ) D.subschemeι)
  rw [range_mapFun_of_isClosedImmersion]
  change p.toHom (IsLocalRing.closedPoint ℂ) ∈ range D.subschemeι
  rw [Scheme.IdealSheafData.range_subschemeι, hDE, exceptionalIdeal,
    Scheme.IdealSheafData.support_comap]
  have e : p.toHom ≫ blowUpToBase I = t.toHom :=
    (toHom_mapFun _ p).symm.trans (congrArg UnderlyingSpace.toHom hp)
  rwa [← e] at htI

variable [D.subscheme.Over (Spec (.of ℂ))]
  [D.subschemeι.IsOver (Spec (.of ℂ))]

/-- **The Euler class of the exceptional divisor on a blowup fibre, on charts.** Let `x_0, …, x_n`
generate the centre `I` of the blowup on an affine open `U`, with chart presentations
`𝒪_X(U)[T_i : i ≠ ℓ] → 𝒪(U_ℓ)` surjective with kernel inside `(x_i - T_i x_ℓ)`, and let
`t ∈ U(ℂ)` be a point of the centre, with compact fibre `F = π⁻¹(t) ≅ ℙⁿ(ℂ)`, `n ≥ 1`. Let `D` be
the exceptional divisor, and `Q = 𝒪(D)(ℂ)|_V` the bundle of its orientation datum
`MMP.Topology.divisorOrientationDatum`. Then the pull-back of the Euler class `e(Q)` along the
inclusion `F ⊆ V` is nonzero in `H²(F; ℚ)`. -/
theorem map_eulerClass_divisorOrientationDatum_ne_zero_of_chartData {n : ℕ} (hn : 1 ≤ n)
    {U : X.Opens} {x : Fin (n + 1) → Γ(X, U)}
    {hf : ∀ (W : X.affineOpens) (h : W.1 ≤ U), I.ideal W = Ideal.span
      (Set.range fun i ↦ (X.presheaf.map (homOfLE h).op).hom (x i))}
    (hU : IsAffineOpen U) (hDE : D = exceptionalIdeal I)
    (hsurj : ∀ ℓ, Function.Surjective (chartPresentation (chartDatum hf) ℓ))
    (hker : ∀ ℓ, RingHom.ker (chartPresentation (chartDatum hf) ℓ) ≤
      Ideal.span (Set.range fun i : {i : Fin (n + 1) // i ≠ ℓ} ↦
        MvPolynomial.C ((chartDatum hf).x i.1) - MvPolynomial.X i *
          MvPolynomial.C ((chartDatum hf).x ℓ)))
    {t : UnderlyingSpace ℂ X} (ht : ⊤ ≤ t.toHom ⁻¹ᵁ U)
    (ht0 : ∀ i, eval t ht ((chartDatum hf).x i) = 0)
    (htI : t.toHom (IsLocalRing.closedPoint ℂ) ∈ I.support)
    (hF : IsCompact (mapFun (blowUpToBase I) ⁻¹' {t}))
    (ι : C(↥(mapFun (blowUpToBase I) ⁻¹' {t}), (divisorOrientationDatum D).nbhd))
    (hι : ∀ p, (ι p).1 = p.1) :
    (relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom ι) (A' := univᶜ)
      (A := univᶜ) (fun x hx ↦ (hx (mem_univ x)).elim) _).hom
      (eulerClass ℚ (divisorOrientationDatum D).F (divisorOrientationDatum D).Q) ≠ 0 := by
  set c := chartDatum hf
  let H := fibreHomeomorphLines c hU hsurj hker ht ht0 hF
  let Hs : C(lineProjections n, ↥(mapFun (blowUpToBase I) ⁻¹' {t})) :=
    ⟨fun P ↦ H.symm P, H.symm.continuous⟩
  let g : C(lineProjections n, UnderlyingSpace ℂ (blowUp I)) :=
    ⟨fun P ↦ (Hs P).1, continuous_subtype_val.comp Hs.continuous⟩
  have hgt : ∀ P, mapFun (blowUpToBase I) (g P) = t := fun P ↦ (Hs P).2
  have hline : ∀ P : lineProjections n, chartLine c (g P) = P.1 := fun P ↦
    (coe_fibreHomeomorphLines_apply c hU hsurj hker ht ht0 hF (H.symm P)).symm.trans
      (congrArg Subtype.val (H.apply_symm_apply P))
  have hg : ∀ (P : lineProjections n) (k : Fin (n + 1))
      (hk : ⊤ ≤ (g P).toHom ⁻¹ᵁ (chartDatum hf).chart k),
      P.1 k k ≠ 0 ∧ ∀ j, P.1 j k / P.1 k k = eval (g P) hk (chartFraction (chartDatum hf) k j) :=
    fun P k hk ↦ ⟨hline P ▸ chartLine_apply_self_ne_zero c hU hk,
      fun j ↦ hline P ▸ chartLine_div c hU hk j⟩
  have hg' : ∀ P : lineProjections n, ∃ k : Fin (n + 1),
      ⊤ ≤ (g P).toHom ⁻¹ᵁ (chartDatum hf).chart k :=
    fun P ↦ exists_top_le_preimage_chart c ht (hgt P)
  have hgE : ∀ P, g P ∈ (divisorOrientationDatum D).nbhd := fun P ↦
    (divisorOrientationDatum D).range_subset_nbhd
      (mem_range_map_subschemeι_of_mapFun_eq D hDE htI (hgt P))
  have hne := map_tautologicalToDatumBase_eulerClass_ne_zero D hU hDE g hg hg' hgE hn
  have hcomp : TopCat.ofHom (tautologicalToDatumBase D g hgE) =
      TopCat.ofHom Hs ≫ TopCat.ofHom ι :=
    TopCat.hom_ext (ContinuousMap.ext fun P ↦ Subtype.ext (hι (Hs P)).symm)
  have he : ∀ {Z : Type} (S : Set Z), (univ : Set Z)ᶜ ⊆ S := fun _ x hx ↦ (hx (mem_univ x)).elim
  exact fun h0 ↦ hne (((relativeSingularCohomology.map_congr_apply ℚ hcomp (he _) (he _) _ _).trans
    (relativeSingularCohomology.map_comp_apply' ℚ (he _) (he _) (he _) _ _)).trans
    ((congrArg _ h0).trans (map_zero _)))

end FibreEuler

section SmoothBlowupFibreEuler

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Bundle Set
open MMP MMP.UnderlyingSpace
open MMP.Resolution MMP.Flips.ResolutionInputs MMP.Analytic

variable {V : Scheme.{0}} [V.Over (Spec (.of ℂ))] {I : V.IdealSheafData}
  [(blowUp I).Over (Spec (.of ℂ))] [(blowUpToBase I).IsOver (Spec (.of ℂ))]
  (D : (blowUp I).IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
  [D.subscheme.Over (Spec (.of ℂ))]
  [D.subschemeι.IsOver (Spec (.of ℂ))]

omit [(blowUp I).Over (Spec (.of ℂ))] [(blowUpToBase I).IsOver (Spec (.of ℂ))] in
/-- At every point of the centre of a smooth blowup of pure codimension `c`, the ideal of the
centre in the stalk has height `c`. -/
theorem height_ker_stalkMap_subschemeι_eq_of_codimension
    (hI : IsSmoothBlowup (V ↘ Spec (.of ℂ)) I) {c : ℕ}
    (hcodim : ∀ Z : TopologicalSpace.IrreducibleCloseds V,
      Maximal (fun W : TopologicalSpace.IrreducibleCloseds V ↦ (W : Set V) ⊆ I.support) Z →
        codimension Z = c)
    (z : I.subscheme) : (RingHom.ker (I.subschemeι.stalkMap z).hom).height = c := by
  obtain ⟨C, hC, hzC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {z}
    isIrreducible_singleton
  have hgen := hC.1.isGenericPoint_genericPoint_closure
  rw [isGenericPoint_def, (isClosed_of_mem_irreducibleComponents C hC).closure_eq] at hgen
  have hwz : hC.1.genericPoint ⤳ z := by
    rw [specializes_iff_mem_closure, hgen]
    exact hzC rfl
  rw [height_ker_stalkMap_subschemeι_eq_codimension_closureSingleton _ I hI.2 (by rwa [hgen]) hwz,
    hcodim _ (maximal_closureSingleton_subschemeι I (by rwa [hgen]))]

/-- **The Euler class of the exceptional divisor is nonzero on the blowup fibres.** Let
`b : V' = Bl_T V ⟶ V` be the blowup of a smooth complex scheme `V` along a smooth closed
subscheme `T = V(I)` of pure codimension `c ≥ 2`, `D` the exceptional divisor, as an effective
Cartier divisor, and `Q = 𝒪(D)(ℂ)|_W` the bundle of its orientation datum
`MMP.Topology.divisorOrientationDatum`, on a neighbourhood `W` of `D(ℂ)`. For every point `t` of
`T(ℂ)`, the fibre `F = b⁻¹(t) ≅ ℙ^{c-1}(ℂ)` lies in `W`, and the pull-back of `e(Q)` along the
inclusion `F ⊆ W` is nonzero in `H²(F; ℚ)`. -/
theorem map_eulerClass_divisorOrientationDatum_ne_zero
    (hI : IsSmoothBlowup (V ↘ Spec (.of ℂ)) I) (c : ℕ) (hc : 2 ≤ c)
    (hcodim : ∀ Z : TopologicalSpace.IrreducibleCloseds V,
      Maximal (fun W : TopologicalSpace.IrreducibleCloseds V ↦ (W : Set V) ⊆ I.support) Z →
        codimension Z = c)
    (hDE : D = exceptionalIdeal I) (t : UnderlyingSpace ℂ V)
    (htI : t.toHom (IsLocalRing.closedPoint ℂ) ∈ I.support)
    (ι : C(↥(mapFun (blowUpToBase I) ⁻¹' {t}), (divisorOrientationDatum D).nbhd))
    (hι : ∀ p, (ι p).1 = p.1) :
    (relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom ι) (A' := univᶜ)
      (A := univᶜ) (fun x hx ↦ (hx (mem_univ x)).elim) _).hom
      (eulerClass ℚ (divisorOrientationDatum D).F (divisorOrientationDatum D).Q) ≠ 0 := by
  set sV := V ↘ Spec (.of ℂ)
  have : Smooth sV := hI.1.smooth
  have : Smooth (I.subschemeι ≫ sV) := hI.2.smooth
  obtain ⟨z, hz⟩ : t.toHom (IsLocalRing.closedPoint ℂ) ∈ Set.range I.subschemeι := by
    rwa [I.range_subschemeι]
  have hn : ((c - 1 + 1 : ℕ) : ℕ∞) = (RingHom.ker (I.subschemeι.stalkMap z).hom).height := by
    rw [Nat.sub_add_cancel (by omega), height_ker_stalkMap_subschemeι_eq_of_codimension hI hcodim]
  -- adapted local coordinates at `t`
  have hT := isRegularLocalRing_stalk_of_smooth_over_field (I.subschemeι ≫ sV) z
  have hreg := IsRegularLocalRing.of_ringEquiv (stalkQuotientEquiv I z).symm
  have hfs := formallySmooth_quotient_idealSheafDataStalk sV I z
  have hdim := ringKrullDim_stalk_eq_quotient_add_height sV I hI z
  rw [← hn] at hdim
  obtain ⟨hnN, U, hU, hzU, x, hx, -, hcut⟩ :=
    Bridges.exists_isLocalCoordinates_isCutOutByFirst_of_stalk sV I I le_rfl (I.subschemeι z) hreg
      hreg hfs hdim hdim
  have hf : ∀ (W : V.affineOpens) (h : W.1 ≤ U), I.ideal W = Ideal.span
      (Set.range fun i : Fin (c - 1 + 1) ↦ (V.presheaf.map (homOfLE h).op).hom
        (x (Fin.castLE hnN i))) := by
    intro W hW
    rw [hcut W hW]
    congr 1
    ext s
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨Fin.castLE hnN j, j.2, rfl⟩
  have hsk := fun ℓ ↦ chartPresentation_surjective_and_ker (chartDatum hf) sV hU x hx hnN
    (fun _ ↦ rfl) ℓ
  -- the fibre over `t`
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
  have : IsProper (blowUpToBase I) := isProper_blowUpToBase I
  have ht : ⊤ ≤ t.toHom ⁻¹ᵁ U := (top_le_preimage_iff _ _).2 (hz ▸ hzU)
  have hres : ∀ s : Γ(V, U), (V.presheaf.map (homOfLE (le_refl U)).op).hom s = s := fun s ↦ by
    rw [show (homOfLE (le_refl U)).op = 𝟙 _ from rfl, CategoryTheory.Functor.map_id]; rfl
  have ht0 : ∀ i, eval t ht ((chartDatum hf).x i) = 0 := fun i ↦ by
    have hi := (chartDatum hf).restrict_mem_ideal ⟨U, hU⟩ le_rfl i
    rw [hres] at hi
    exact eval_eq_zero_of_mem_ideal I ⟨U, hU⟩ t ht htI hi
  have hF : IsCompact (mapFun (blowUpToBase I) ⁻¹' {t}) :=
    (isProperMap_map (K := ℂ) (blowUpToBase I)).isCompact_preimage isCompact_singleton
  exact map_eulerClass_divisorOrientationDatum_ne_zero_of_chartData D (n := c - 1) (by omega) hU
    hDE (fun ℓ ↦ (hsk ℓ).1) (fun ℓ ↦ (hsk ℓ).2.le) ht ht0 htI hF ι hι

/-- **`ξ = -e(Q)` is nonzero on the blowup fibres**. -/
theorem map_neg_eulerClass_divisorOrientationDatum_ne_zero
    (hI : IsSmoothBlowup (V ↘ Spec (.of ℂ)) I) (c : ℕ) (hc : 2 ≤ c)
    (hcodim : ∀ Z : TopologicalSpace.IrreducibleCloseds V,
      Maximal (fun W : TopologicalSpace.IrreducibleCloseds V ↦ (W : Set V) ⊆ I.support) Z →
        codimension Z = c)
    (hDE : D = exceptionalIdeal I) (t : UnderlyingSpace ℂ V)
    (htI : t.toHom (IsLocalRing.closedPoint ℂ) ∈ I.support)
    (ι : C(↥(mapFun (blowUpToBase I) ⁻¹' {t}), (divisorOrientationDatum D).nbhd))
    (hι : ∀ p, (ι p).1 = p.1) :
    (relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom ι) (A' := univᶜ)
      (A := univᶜ) (fun x hx ↦ (hx (mem_univ x)).elim) _).hom
      (-eulerClass ℚ (divisorOrientationDatum D).F (divisorOrientationDatum D).Q) ≠ 0 := by
  rw [map_neg, neg_ne_zero]
  exact map_eulerClass_divisorOrientationDatum_ne_zero D hI c hc hcodim hDE t htI ι hι

/-- The fibres of the blowup over the points of the centre lie in the neighbourhood of the
orientation datum of the exceptional divisor. -/
lemma preimage_singleton_subset_nbhd_divisorOrientationDatum
    (hDE : D = exceptionalIdeal I) {t : UnderlyingSpace ℂ V}
    (htI : t.toHom (IsLocalRing.closedPoint ℂ) ∈ I.support) :
    mapFun (blowUpToBase I) ⁻¹' {t} ⊆ (divisorOrientationDatum D).nbhd := fun _ hp ↦
  (divisorOrientationDatum D).range_subset_nbhd
    (mem_range_map_subschemeι_of_mapFun_eq D hDE htI hp)

end SmoothBlowupFibreEuler

end MMP.Topology

end
