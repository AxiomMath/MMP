module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.ZeroSectionCycle.StacksAssemblyLocal
public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.ZeroSectionCycle.StacksDeriv
public import MMP.AlgebraicTopology.FundamentalClass.Exists
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.RegularPartComplement
public import MMP.AlgebraicGeometry.CycleMap.FundamentalClassDetectedOnOpen

/-!
# Fulton's Lemma 19.2(d) for a Stacks vector bundle: `u_{E|_V} ∩ cl(E|_V) = cl(V)`

Let `ℰ` be a quasi-coherent `𝒪_X`-module, finite locally free of rank `r`, on a complex scheme
`X`, with vector bundle `π : 𝐕(ℰ) ⟶ X` (`MMP.Modules.totalSpace`) and Thom class `u_ℰ`
(`MMP.Modules.thomClass`), and let `V` be an `m`-dimensional subvariety of `X`, with
`E|_V = π⁻¹(V)` (`MMP.Modules.preimageSubvariety`). For every fundamental class `c` of `E|_V`,
`h_*(ι^* u_ℰ ∩ c)` is a fundamental class of `V`, where `ι : E|_V → 𝐕(ℰ)` is the inclusion and
`h : ι⁻¹(0(X(ℂ))) ≅ V(ℂ)`; this is
`isVarietyFundamentalClass_pushforward_zeroSectionPreimageHomeomorphHom_capProductSupportPullback`.
It gives `MMP.Modules.ZeroSectionCapFormula`, and with it the cycle form
`u_ℰ ∩ cl(π^* β) = cl_X(β)`.

The proof: a top-degree class of `V` is a fundamental class as soon as it agrees with one on a
non-empty open subset of `V_reg(ℂ)` (`MMP.IsVarietyFundamentalClass.of_restrict_eq`). Take a
coordinate ball `B₀ ⊆ V_reg(ℂ)` over the domain of a chart of `ℰ`
(`MMP.Modules.exists_bundleChartBase`). Over `B₀` the cap product is computed in the bundle chart
`Θ : P₀ ≅ B₀ × ℂʳ`
(`MMP.Modules.restrict_pushforward_zeroSectionPreimageHomeomorphHom_capProductSupportPullback`),
which is holomorphic with injective derivative (`MMP.Modules.hasFDerivAt_bundleChartHomeomorph`),
and there `g^* u₀ ∩ μ_P` is carried to `μ_{B₀}`
(`MMP.IsFundamentalClass.pushforward_zeroFibreHomeomorph_capProductSupportPullback_complexVector`).

## Main results

* `MMP.Modules.hasFDerivAt_bundleChartHomeomorph`: the bundle chart is holomorphic with
  injective derivative in the charts of `P₀` and `B₀`.
* `MMP.Modules.exists_bundleChartBase`: a connected coordinate ball of `V_reg` over a chart of
  `ℰ`.
* `MMP.Modules.zeroSectionCapFormula`: `ZeroSectionCapFormula R E r V hV hW`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.2, proof of Lemma 19.2(d).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set Topology TopologicalSpace Metric
open MMP.UnderlyingSpace

namespace MMP.Modules

open MMP.Intersection.Scheme
open borelMooreHomology BorelMooreCross FundamentalClass ThomClass

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X] {E : X.Modules}
  [E.IsQuasicoherent] {r : ℕ}
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E r]
  [IsComplexScheme (totalSpace E)] {V : Subvariety X} {ch : Chart E r}
  {B₀ : Opens (UnderlyingSpace ℂ V.toScheme)}

/-- **The bundle chart is holomorphic with injective derivative** in the charts of the complex
manifolds `P₀ ⊆ (E|_V)_reg(ℂ)` and `B₀ ⊆ V_reg(ℂ)` (`contDiffAt_bundleChart`,
`injective_fderiv_bundleChart`). -/
theorem hasFDerivAt_bundleChartHomeomorph
    (hB₀ : ∀ q ∈ B₀, q ∈ regularPart ℂ V.toScheme ∧ mapFun V.ι q ∈ chartBase ch) {m : ℕ}
    (hV : (m : WithBot ℕ∞) = dimension V.toScheme)
    (hW : ((m + r : ℕ) : WithBot ℕ∞) = dimension (preimageSubvariety E r V).toScheme) :
    letI := regularChartedSpace (𝕜 := ℂ) hW
    letI := regularChartedSpace (𝕜 := ℂ) hV
    ∀ c ∈ _root_.atlas (EuclideanSpace ℂ (Fin (m + r))) (BundleChartSource E r V B₀),
      ∀ c' ∈ _root_.atlas (EuclideanSpace ℂ (Fin m))
          (BundleChartBase V B₀), ∀ x ∈ c.source,
        (bundleChartHomeomorph hB₀ x).1 ∈ c'.source →
        ∃ L : EuclideanSpace ℂ (Fin (m + r)) →L[ℂ] EuclideanSpace ℂ (Fin m) × (Fin r → ℂ),
          Function.Injective L ∧
          HasFDerivAt (fun y ↦ (c' (bundleChartHomeomorph hB₀ (c.symm y)).1,
            (bundleChartHomeomorph hB₀ (c.symm y)).2)) L (c x) := by
  intro c hc c' hc' x hx hx'
  obtain ⟨a, ha, hca, hcs, hct⟩ :=
    exists_isAlgebraicChart_of_mem_atlas_regularOpensInter hW (preimageProjOpens E r V B₀) hc
  obtain ⟨a', ha', hca', hcs', -⟩ :=
    exists_isAlgebraicChart_of_mem_atlas_regularOpensInter hV B₀ hc'
  have hpa : x.1.1 ∈ a.source := (hcs x).1 hx
  have hpa' : mapFun (preimageSubvarietyProj E r V) x.1.1 ∈ a'.source := (hcs' _).1 hx'
  have hpi := mem_chartTotalOpens_of_mem_preimageProjOpens hB₀ x.2
  set F := fun y ↦ (a' (mapFun (preimageSubvarietyProj E r V) (a.symm y)),
    coord ch (mapFun (preimageSubvariety E r V).ι (a.symm y)))
  have hFd : DifferentiableAt ℂ F (a x.1.1) :=
    (contDiffAt_bundleChart E r V ha ha' hpa hpa' ch hpi).differentiableAt (by simp)
  refine ⟨fderiv ℂ F (a x.1.1), injective_fderiv_bundleChart E r V ha ha' hpa hpa' ch hpi, ?_⟩
  rw [hca x]
  refine hFd.hasFDerivAt.congr_of_eventuallyEq ?_
  rw [← hca x]
  filter_upwards [c.open_target.mem_nhds (c.map_source hx)] with y hy
  simp only [hca', coe_fst_bundleChartHomeomorph_apply, snd_bundleChartHomeomorph_apply,
    hct y hy, F]

variable (E r V)

/-- **A coordinate ball of `V_reg` over a chart of `ℰ`.** There are a chart `ch` of `ℰ` and a
non-empty open set `B₀ ⊆ V(ℂ)`, inside the regular part `V_reg(ℂ)` and over the domain of `ch`,
which is connected as an open subset of `V_reg(ℂ)` (the preimage of a ball under an algebraic
chart). -/
theorem exists_bundleChartBase {m : ℕ} (hV : (m : WithBot ℕ∞) = dimension V.toScheme) :
    ∃ (ch : Chart E r) (B₀ : Opens (UnderlyingSpace ℂ V.toScheme)),
      (B₀ : Set (UnderlyingSpace ℂ V.toScheme)).Nonempty ∧
      (∀ q ∈ B₀, q ∈ regularPart ℂ V.toScheme ∧ mapFun V.ι q ∈ chartBase ch) ∧
      ConnectedSpace (BundleChartBase V B₀) := by
  obtain ⟨q₀, hq₀, -⟩ :=
    exists_mem_regularPart_notMem isClosed_empty (empty_ne_univ (α := V.toScheme))
  set ch := chartAt E r (mapFun V.ι q₀)
  obtain ⟨e, hq₀e, -⟩ := exists_isAlgebraicChart_of_dimension_eq hV q₀ hq₀
  set O := e.source ∩ regularPart ℂ V.toScheme ∩ mapFun V.ι ⁻¹' chartBase ch
  have hO : IsOpen O := (e.open_source.inter isOpen_regularPart).inter
    ((isOpen_chartBase ch).preimage (continuous_mapFun _))
  have hq₀U : e q₀ ∈ e.target ∩ e.symm ⁻¹' O := ⟨e.map_source hq₀e, by
    rw [mem_preimage, e.left_inv hq₀e]
    exact ⟨⟨hq₀e, hq₀⟩, mem_chartBase_chartAt E r _⟩⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (e.isOpen_inter_preimage_symm hO) _ hq₀U
  let B₀ : Opens (UnderlyingSpace ℂ V.toScheme) :=
    ⟨e.source ∩ e ⁻¹' ball (e q₀) ε, e.isOpen_inter_preimage isOpen_ball⟩
  have hB₀O : ∀ q ∈ B₀, q ∈ O := fun q hq ↦ by simpa [e.left_inv hq.1] using (hball hq.2).2
  refine ⟨ch, B₀, ⟨q₀, hq₀e, mem_ball_self hε⟩, fun q hq ↦ ⟨(hB₀O q hq).1.2, (hB₀O q hq).2⟩, ?_⟩
  have hsymm : ∀ y : ball (e q₀) ε, e.symm y ∈ B₀ := fun y ↦
    ⟨e.map_target (hball y.2).1, by simpa [e.right_inv (hball y.2).1] using y.2⟩
  let F : ball (e q₀) ε → BundleChartBase V B₀ :=
    fun y ↦ ⟨⟨e.symm y, (hB₀O _ (hsymm y)).1.2⟩, hsymm y⟩
  have hF : Continuous F :=
    ((e.continuousOn_symm.comp_continuous continuous_subtype_val
      fun y ↦ (hball y.2).1).subtype_mk _).subtype_mk _
  have hFs : Function.Surjective F := fun b ↦
    ⟨⟨e b.1.1, b.2.2⟩, Subtype.ext (Subtype.ext (e.left_inv b.2.1))⟩
  have : ConnectedSpace (ball (e q₀) ε) :=
    isConnected_iff_connectedSpace.1 ((convex_ball _ _).isConnected (nonempty_ball.2 hε))
  exact hFs.connectedSpace hF

variable (R : Type) [CommRing R]

/-- **`u_{E|_V} ∩ cl(E|_V) = cl(V)`** (Fulton, proof of Lemma 19.2(d)). Let `ℰ` be finite locally
free of rank `r` on a complex scheme `X`, `V` an `m`-dimensional subvariety of `X`, `ι` the
inclusion of the `(m + r)`-dimensional subvariety `E|_V = π⁻¹(V)` of `𝐕(ℰ)` and
`h : ι⁻¹(0(X(ℂ))) ≅ V(ℂ)`. For every fundamental class `c` of `E|_V`, the class
`h_*(ι^* u_ℰ ∩ c) ∈ H_{2m} V` is a fundamental class of `V`. -/
theorem isVarietyFundamentalClass_pushforward_zeroSectionPreimageHomeomorphHom_capProductSupportPullback
    {m : ℕ} {hV : (m : WithBot ℕ∞) = dimension V.toScheme}
    {hW : ((m + r : ℕ) : WithBot ℕ∞) = dimension (preimageSubvariety E r V).toScheme}
    {c : borelMooreHomology R (ModuleCat.of R R)
      (TopCat.of (UnderlyingSpace ℂ (preimageSubvariety E r V).toScheme)) (2 * (m + r) : ℕ)}
    (hc : IsVarietyFundamentalClass R hW c) :
    IsVarietyFundamentalClass R hV
      (BorelMooreCross.congrDegree R _ (two_mul_add_sub_two_mul m r)
        (borelMooreHomology.pushforward R (ModuleCat.of R R)
          (zeroSectionPreimageHomeomorphHom E r V)
          (zeroSectionPreimageHomeomorph E r V).isProperMap _
          (borelMooreHomology.capProductSupportPullback R
            (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (preimageSubvariety E r V).ι))
            isClosed_range_zeroSection
            (hasProperNeighbourhoodDeformations_preimage_range_zeroSection E _)
            ((2 * r : ℕ) : ℤ) ((2 * (m + r) : ℕ) : ℤ) (thomClass R E r) c))) := by
  obtain ⟨ch, B₀, hne, hB₀, hconn⟩ := exists_bundleChartBase E r V hV
  obtain ⟨u₀, hu₀⟩ : ∃ u₀, IsLocalOrientationClass R (complexOrientationBasis r)
      (0 : TopCat.of (Fin r → ℂ)) u₀ := by
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · exact exists_isLocalOrientationClass_of_eq_zero R (by simp) _ _
    · exact exists_isLocalOrientationClass (isOrientedAtlas_self (Fin r → ℂ)) (by omega) _ _
  obtain ⟨c', hc', -⟩ := existsUnique_isVarietyFundamentalClass R hV
  refine IsVarietyFundamentalClass.of_restrict_eq hc' B₀ (subset_regularPart_of_forall_mem hB₀)
    hne ?_
  letI := regularChartedSpace (𝕜 := ℂ) hW
  letI := regularChartedSpace (𝕜 := ℂ) hV
  have key :=
    IsFundamentalClass.pushforward_zeroFibreHomeomorph_capProductSupportPullback_complexVector
    R (hc.isFundamentalClass_restrict (preimageProjOpens E r V B₀))
    (hc'.isFundamentalClass_restrict B₀) (bundleChartHomeomorph hB₀)
    (hasFDerivAt_bundleChartHomeomorph hB₀ hV hW) (bundleChartCoordHom hB₀) (fun _ ↦ rfl) hu₀
    (two_mul_add_sub_two_mul m r)
  have loc := restrict_pushforward_zeroSectionPreimageHomeomorphHom_capProductSupportPullback
    hB₀ R hu₀ ((2 * (m + r) : ℕ) : ℤ) c
  conv_lhs => rw [congrDegree_restrict_hom]
  conv_lhs => arg 2; rw [loc]
  conv_lhs => rw [← pushforward_congrDegree_apply]
  conv_lhs => arg 2; rw [← pushforward_congrDegree_apply]
  conv_lhs => arg 2; rw [key]
  exact (restrict_eq_pushforward_regularOpensInterHom R B₀
    (subset_regularPart_of_forall_mem hB₀) (2 * m : ℕ) c').symm

/-- **`ZeroSectionCapFormula` for Stacks vector bundles** (Fulton, proof of Lemma 19.2(d)): for
every `m`-dimensional subvariety `V` of `X`, `f'_*(ι^* u_ℰ ∩ cl(E|_V)) = cl_X(V)`. -/
theorem zeroSectionCapFormula {m : ℕ} (hV : (m : WithBot ℕ∞) = dimension V.toScheme)
    (hW : ((m + r : ℕ) : WithBot ℕ∞) = dimension (preimageSubvariety E r V).toScheme) :
    ZeroSectionCapFormula E R r V hV hW :=
  zeroSectionCapFormula_of_isVarietyFundamentalClass E r V R fun _ hc ↦
    isVarietyFundamentalClass_pushforward_zeroSectionPreimageHomeomorphHom_capProductSupportPullback
      E r V R hc

end MMP.Modules
