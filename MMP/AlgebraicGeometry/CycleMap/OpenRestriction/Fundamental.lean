module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.FundamentalClassVarietyUnique
public import MMP.AlgebraicTopology.OrientationClass.CapLocalDegree
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.GenericCovering
public import MMP.AlgebraicTopology.BorelMoore.RestrictionPushforward
public import MMP.AlgebraicGeometry.Properties.RegularLocus
public import MMP.AlgebraicGeometry.Pullbacks.Over
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.OpenImmersionRange
/-!
# Fundamental classes along open immersions of complex varieties (Fulton, §19.1)

Let `g : W → V` be an open immersion of complex varieties of dimension `n`. Then `g` induces an
open embedding `W(ℂ) → V(ℂ)`, a homeomorphism `ψ` of `W(ℂ)` onto the open subset `g(W(ℂ))`, and
it carries `W_reg(ℂ)` onto `V_reg(ℂ) ∩ g(W(ℂ))`. The algebraic charts of `V(ℂ)` restrict to
algebraic charts of `W(ℂ)` (`IsAlgebraicChart.restrict_openEmbedding`), so `ψ` is orientation
preserving on the regular parts for the complex orientations, and the restriction of the
fundamental class of `V` to `g(W(ℂ))`, read on `W(ℂ)` through `ψ`, is the fundamental class of
`W`. This is the step "`cl(V)|_{V ∩ U}` is the fundamental class of `V ∩ U`" of Fulton's
compatibility of the cycle map with restriction to open subschemes
(`lem_c19_cycle_map_open_restriction`).

## Main definitions

* `MMP.UnderlyingSpace.regularHomeomorph`: `V_reg(ℂ) ∩ g(W(ℂ)) ≃ₜ W_reg(ℂ)`.

## Main results

* `MMP.FundamentalClass.isOrientationPreserving_of_forall_mem_atlas`: a
  homeomorphism into a manifold with an oriented atlas, under which every chart of the source is
  read as a chart of the target, is orientation preserving.
* `MMP.IsVarietyFundamentalClass.pushforward_restrict_opensRangeMap`: the
  fundamental class of `V` restricted to `g(W(ℂ))` is the fundamental class of `W`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Set Manifold
open MMP.UnderlyingSpace MMP.FundamentalClass

universe u

namespace MMP

open MMP.Intersection.Scheme (dimension)
open MMP

namespace FundamentalClass

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  {M M' : Type u} [TopologicalSpace M] [TopologicalSpace M'] [ChartedSpace H M]
  [ChartedSpace H M']

/-- **Homeomorphisms reading charts as charts are orientation preserving.** Let `φ : M ≃ₜ M'` be
a homeomorphism of `n`-manifolds modelled on `H`, `M'` with an oriented atlas. If every chart `e`
of `M` is read through `φ⁻¹` as a chart `ê = e ∘ φ⁻¹` of `M'`, then `φ` is orientation preserving
for the orientation `b` in both: its chart expressions are transition maps of `M'`. -/
theorem isOrientationPreserving_of_forall_mem_atlas (hM' : IsOrientedAtlas H M') {n : ℕ}
    (b : Module.Basis (Fin n) ℝ H) (φ : M ≃ₜ M')
    (h : ∀ e ∈ atlas H M, ∃ ê ∈ atlas H M', ∀ z : M', ê z = e (φ.symm z) ∧
      (z ∈ ê.source ↔ φ.symm z ∈ e.source)) :
    IsOrientationPreserving b b φ := by
  refine isOrientationPreserving_of_hasFDerivAt b b φ fun e he e' he' x hx hx' ↦ ?_
  obtain ⟨ê, hê, hêe⟩ := h e he
  have hφx : φ x ∈ ê.source := (hêe (φ x)).2.2 (by simpa using hx)
  have hêx : ê (φ x) = e x := by simpa using (hêe (φ x)).1
  have hpt : e x ∈ (ê.symm ≫ₕ e').source := by
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      mem_inter_iff, mem_preimage]
    refine ⟨hêx ▸ ê.map_source hφx, ?_⟩
    rw [← hêx, ê.left_inv hφx]
    exact hx'
  obtain ⟨hd, hdet⟩ := hM' ê hê e' he' (e x) hpt
  refine ⟨fderiv ℝ (ê.symm ≫ₕ e') (e x), ?_, ?_⟩
  · refine hd.hasFDerivAt.congr_of_eventuallyEq ?_
    filter_upwards [e.open_target.mem_nhds (e.map_source hx)] with y hy
    have hz : φ (e.symm y) ∈ ê.source := (hêe _).2.2 (by simpa using e.map_target hy)
    have hêz : ê (φ (e.symm y)) = y := by
      rw [(hêe _).1, φ.symm_apply_apply, e.right_inv hy]
    have hsy : ê.symm y = φ (e.symm y) := by
      conv_lhs => rw [← hêz]
      exact ê.left_inv hz
    simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hsy]
  · rw [show ((fderiv ℝ (ê.symm ≫ₕ e') (e x) : H → H) ∘ b) =
      ((fderiv ℝ (ê.symm ≫ₕ e') (e x) : H →ₗ[ℝ] H) : H → H) ∘ b from rfl, basis_det_comp_self]
    exact hdet

end FundamentalClass

namespace UnderlyingSpace

section OpenImmersion

variable {W V : Scheme.{0}} [W.Over (Spec (.of ℂ))] [V.Over (Spec (.of ℂ))]
  (g : W ⟶ V) [IsOpenImmersion g] [g.IsOver (Spec (.of ℂ))]

variable [LocallyOfFiniteType (W ↘ Spec (.of ℂ))] [QuasiCompact (W ↘ Spec (.of ℂ))]
  [LocallyOfFiniteType (V ↘ Spec (.of ℂ))] [QuasiCompact (V ↘ Spec (.of ℂ))]

/-- An open immersion preserves and reflects regular points. -/
lemma mapFun_mem_regularPart_iff (z : UnderlyingSpace ℂ W) :
    mapFun g z ∈ regularPart ℂ V ↔ z ∈ regularPart ℂ W := by
  rw [mem_regularPart_iff, mem_regularPart_iff, toHom_mapFun]
  exact MMP.mem_regularLocus_iff_of_isOpenImmersion g (z.toHom (IsLocalRing.closedPoint ℂ))

/-- An open immersion `g : W → V` over `ℂ` identifies `V_reg(ℂ) ∩ g(W(ℂ))` with `W_reg(ℂ)`. -/
def regularHomeomorph :
    regularOpensInter (opensRangeMap g) ≃ₜ regularOpens ℂ W where
  toFun x := ⟨(homeomorphOpensRangeMap g).symm ⟨x.1.1, x.2⟩, by
    rw [mem_regularOpens, ← mapFun_mem_regularPart_iff g,
      mapFun_homeomorphOpensRangeMap_symm_apply]
    exact x.1.2⟩
  invFun z := ⟨⟨mapFun g z.1, (mapFun_mem_regularPart_iff g z.1).2 z.2⟩, ⟨z.1, rfl⟩⟩
  left_inv x := Subtype.ext (Subtype.ext (mapFun_homeomorphOpensRangeMap_symm_apply g _))
  right_inv z := Subtype.ext ((homeomorphOpensRangeMap g).symm_apply_apply z.1)
  continuous_toFun := by
    refine Continuous.subtype_mk ((homeomorphOpensRangeMap g).symm.continuous.comp ?_) _
    exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    exact (map (K := ℂ) g).continuous.comp continuous_subtype_val

/-- The inverse of `regularHomeomorph g` sends a regular point `z` of `W(ℂ)` to the point
`mapFun g z` of `V(ℂ)`. -/
@[simp]
lemma coe_coe_regularHomeomorph_symm_apply (z : regularOpens ℂ W) :
    (((regularHomeomorph g).symm z : regularOpens ℂ V) : UnderlyingSpace ℂ V) = mapFun g z.1 :=
  rfl

end OpenImmersion

end UnderlyingSpace

namespace borelMooreHomology

open MMP.borelMooreHomology

variable (R : Type u) [CommRing R]

/-- Two chains of three proper push-forwards with the same composite agree. -/
lemma pushforward_pushforward_pushforward_apply_eq {A B C D B' C' : TopCat.{u}} (f₁ : A ⟶ B)
    (f₂ : B ⟶ C) (f₃ : C ⟶ D) (g₁ : A ⟶ B') (g₂ : B' ⟶ C') (g₃ : C' ⟶ D)
    (hf₁ : IsProperMap f₁) (hf₂ : IsProperMap f₂) (hf₃ : IsProperMap f₃) (hg₁ : IsProperMap g₁)
    (hg₂ : IsProperMap g₂) (hg₃ : IsProperMap g₃) (h : f₁ ≫ f₂ ≫ f₃ = g₁ ≫ g₂ ≫ g₃) (j : ℤ)
    (a : borelMooreHomology R (ModuleCat.of R R) A j) :
    (pushforward R (ModuleCat.of R R) f₃ hf₃ j).hom
        ((pushforward R (ModuleCat.of R R) f₂ hf₂ j).hom
          ((pushforward R (ModuleCat.of R R) f₁ hf₁ j).hom a)) =
      (pushforward R (ModuleCat.of R R) g₃ hg₃ j).hom
        ((pushforward R (ModuleCat.of R R) g₂ hg₂ j).hom
          ((pushforward R (ModuleCat.of R R) g₁ hg₁ j).hom a)) := by
  rw [pushforward_comp_apply R f₁ f₂ hf₁ hf₂ (hf₂.comp hf₁),
    pushforward_comp_apply R (f₁ ≫ f₂) f₃ (hf₂.comp hf₁) hf₃ (hf₃.comp (hf₂.comp hf₁)),
    pushforward_comp_apply R g₁ g₂ hg₁ hg₂ (hg₂.comp hg₁),
    pushforward_comp_apply R (g₁ ≫ g₂) g₃ (hg₂.comp hg₁) hg₃ (hg₃.comp (hg₂.comp hg₁))]
  exact pushforward_apply_congr R (by simpa only [Category.assoc] using h) _ _ j a

end borelMooreHomology

section Variety

open UnderlyingSpace borelMooreHomology

variable {R : Type} [CommRing R] {W V : Scheme.{0}} [W.Over (Spec (.of ℂ))]
  [V.Over (Spec (.of ℂ))] [IsComplexScheme W] [IsComplexScheme V] [IsIntegral W] [IsIntegral V]
  (g : W ⟶ V) [IsOpenImmersion g] [g.IsOver (Spec (.of ℂ))]

/-- **The regular parts are identified orientation-preservingly.** For an open immersion
`g : W → V` of complex varieties of dimension `n`, the identification
`V_reg(ℂ) ∩ g(W(ℂ)) ≃ₜ W_reg(ℂ)` is orientation preserving for the complex orientations of the
algebraic charts: a chart `e` of `V_reg(ℂ)`, read on `W(ℂ)` through `g`, is an algebraic chart of
`W(ℂ)`. -/
theorem isOrientationPreserving_regularHomeomorph {n : ℕ} (hnW : (n : WithBot ℕ∞) = dimension W)
    (hnV : (n : WithBot ℕ∞) = dimension V) :
    letI := regularChartedSpace (𝕜 := ℂ) hnW
    letI := regularChartedSpace (𝕜 := ℂ) hnV
    IsOrientationPreserving (euclideanComplexOrientationBasis n)
      (euclideanComplexOrientationBasis n) (regularHomeomorph g) := by
  let := regularChartedSpace (𝕜 := ℂ) hnW
  let := regularChartedSpace (𝕜 := ℂ) hnV
  have := isManifold_regularOpens (𝕜 := ℂ) (X := W) hnW
  have : IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 1 (regularOpens ℂ W) :=
    IsManifold.of_le le_top
  refine isOrientationPreserving_of_forall_mem_atlas
    (isOrientedAtlas_of_isManifold_complex (regularOpens ℂ W)) _ _ fun e he ↦ ?_
  obtain ⟨_, ⟨x, rfl⟩, he⟩ := he
  rw [mem_singleton_iff] at he
  subst he
  set c := (exists_isAlgebraicChart_of_dimension_eq hnV x.1.1 (mem_regularOpens.1 x.1.2)).choose
  have hc : IsAlgebraicChart c :=
    (exists_isAlgebraicChart_of_dimension_eq hnV x.1.1 (mem_regularOpens.1 x.1.2)).choose_spec.2
  have : Nonempty (UnderlyingSpace ℂ W) := ⟨(regularHomeomorph g x).1⟩
  refine ⟨(restrictChart g c).subtypeRestr ⟨regularHomeomorph g x⟩,
    ⟨restrictChart g c, ⟨regularHomeomorph g x⟩, hc.restrict_openEmbedding g, rfl⟩,
    fun z ↦ ⟨rfl, ?_⟩⟩
  simp only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage,
    OpenPartialHomeomorph.trans_source, IsOpenEmbedding.toOpenPartialHomeomorph_source,
    univ_inter]
  change _ ↔ ((regularHomeomorph g).symm z).1 ∈ (c.subtypeRestr ⟨x.1⟩).source
  rw [OpenPartialHomeomorph.subtypeRestr_source, IsOpenEmbedding.toOpenPartialHomeomorph_apply]
  exact Iff.rfl

variable (R) in
/-- **The fundamental class restricts to fundamental classes along open immersions** (Fulton,
§19.1). Let `g : W → V` be an open immersion of complex varieties of dimension `n` and
`c = cl(V)`. Then the restriction of `c` to the open subset `g(W(ℂ))` of `V(ℂ)`, read on `W(ℂ)`
through the homeomorphism `W(ℂ) ≃ₜ g(W(ℂ))`, is the fundamental class of `W`. -/
theorem IsVarietyFundamentalClass.pushforward_restrict_opensRangeMap {n : ℕ}
    (hnW : (n : WithBot ℕ∞) = dimension W) (hnV : (n : WithBot ℕ∞) = dimension V)
    {c : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ V)) (2 * n : ℕ)}
    (hc : IsVarietyFundamentalClass R hnV c) :
    IsVarietyFundamentalClass R hnW
      (pushforward R (ModuleCat.of R R)
        (TopCat.ofHom ((homeomorphOpensRangeMap g).symm : C(opensRangeMap g, UnderlyingSpace ℂ W)))
        (homeomorphOpensRangeMap g).symm.isProperMap (2 * n : ℕ)
        (restrict R (ModuleCat.of R R) (Y := TopCat.of (UnderlyingSpace ℂ V)) (opensRangeMap g)
          (2 * n : ℕ) c)) := by
  let := regularChartedSpace (𝕜 := ℂ) hnW
  let := regularChartedSpace (𝕜 := ℂ) hnV
  have hVr : IsFundamentalClass R (euclideanComplexOrientationBasis n)
      (restrict R (ModuleCat.of R R) (Y := TopCat.of (UnderlyingSpace ℂ V))
        (regularOpens ℂ V : Opens (TopCat.of (UnderlyingSpace ℂ V))) (2 * n : ℕ) c) := hc
  have hθ := (hVr.restrict (regularOpensInter (opensRangeMap g))).pushforward_homeomorph R
    (regularHomeomorph g) (isOrientationPreserving_regularHomeomorph g hnW hnV)
  have hQO : opensRangeMap g ⊓ regularOpens ℂ V ≤ opensRangeMap g := inf_le_left
  have hQV : opensRangeMap g ⊓ regularOpens ℂ V ≤ regularOpens ℂ V := inf_le_right
  have hP : subOpens (Y := TopCat.of (UnderlyingSpace ℂ V)) (opensRangeMap g)
      (opensRangeMap g ⊓ regularOpens ℂ V) =
      Opens.comap (TopCat.ofHom ((homeomorphOpensRangeMap g).symm :
        C(opensRangeMap g, UnderlyingSpace ℂ W))).hom
        (regularOpens ℂ W : Opens (TopCat.of (UnderlyingSpace ℂ W))) := by
    ext y
    change y.1 ∈ opensRangeMap g ∧ y.1 ∈ regularOpens ℂ V ↔
      (homeomorphOpensRangeMap g).symm y ∈ regularPart ℂ W
    rw [← mapFun_mem_regularPart_iff g, mapFun_homeomorphOpensRangeMap_symm_apply]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨y.2, h⟩⟩
  have hO' : subOpens (Y := TopCat.of (UnderlyingSpace ℂ V)) (regularOpens ℂ V)
      (opensRangeMap g ⊓ regularOpens ℂ V) = regularOpensInter (opensRangeMap g) := by
    ext y
    change y.1 ∈ opensRangeMap g ∧ y.1 ∈ regularOpens ℂ V ↔ y.1 ∈ opensRangeMap g
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, y.2⟩⟩
  unfold IsVarietyFundamentalClass
  convert hθ using 1
  rw [restrict_pushforward_apply, restrict_eq_pushforward_opensEqMap hP,
    restrict_restrict_apply R (ModuleCat.of R R) (Y := TopCat.of (UnderlyingSpace ℂ V))
      (opensRangeMap g) hQO]
  have hR := restrict_eq_pushforward_opensEqMap hO' ((2 * n : ℕ) : ℤ)
    (restrict R (ModuleCat.of R R) (Y := TopCat.of (UnderlyingSpace ℂ V))
      (regularOpens ℂ V : Opens (TopCat.of (UnderlyingSpace ℂ V))) (2 * n : ℕ) c)
  rw [restrict_restrict_apply R (ModuleCat.of R R) (Y := TopCat.of (UnderlyingSpace ℂ V))
    (regularOpens ℂ V) hQV] at hR
  refine Eq.trans ?_ (congrArg (ConcreteCategory.hom (pushforward R (ModuleCat.of R R)
    (TopCat.ofHom (regularHomeomorph g : C(regularOpensInter (opensRangeMap g), regularOpens ℂ W)))
    (regularHomeomorph g).isProperMap (2 * n : ℕ))) hR).symm
  refine pushforward_pushforward_pushforward_apply_eq R _ _ _ _ _ _ _ _ _ _ _ _ ?_ _ _
  ext x
  rfl

end Variety

end MMP
