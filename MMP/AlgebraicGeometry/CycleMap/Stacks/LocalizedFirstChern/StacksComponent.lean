module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksLocalCap
public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksSectionComponent
public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksCycleClass
public import MMP.AlgebraicGeometry.Chow.LocalEquationCoefficient
public import MMP.AlgebraicGeometry.SubschemeOver
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.BallProductChart
public import MMP.AlgebraicGeometry.CycleMap.LocalizedFirstChern.ComponentTrace

/-!
# Fulton's Lemma 19.1.3 near a general point of a component, for a Stacks line bundle

Let `ℰ` be a quasi-coherent `𝒪_X`-module, locally free of rank one, on a normal complex variety
`X` of dimension `k + 1`, and `σ : X ⟶ 𝐕(ℰ)` a section of `π : 𝐕(ℰ) ⟶ X` other than the zero
section, with zero scheme `D = Z(σ)`. Each irreducible component of `D` contains a non-empty open
`W ⊆ D(ℂ)` inside its regular part, missing the other components, on which `σ^*(u_ℰ) ∩ cl(X)`
and the cycle class `cl_D([D]_k)` of Stacks' cycle `[D]_k` of `D` (Tag 02QU) restrict to the same
class (`MMP.Modules.exists_opens_restrict_localizedTopChernCap_eq_cycleClass`).

The open `W` lies over a chart `c = (V, b)` of `ℰ` meeting the component, where `D` is cut out by
the local coordinate `h = σ^♯b` (`MMP.Modules.ideal_zeroLocus_chart`). The local normal form
`h = g^m` (`MMP.UnderlyingSpace.exists_localNormalForm`) and a ball product chart give local
holomorphic coordinates in which both sides are `m · μ_B`: the cap side by
`MMP.Modules.pushforward_restrict_zeroLocusOpens_eq_smul`, the cycle side by
`MMP.Chow.pushforward_restrict_cycleClass_eq_smul_of_chart`, the coefficient of the component in
`[D]_k` being the order of vanishing `m` of `h`
(`MMP.Chow.cycleAssociatedToClosedSubscheme_self_apply_eq_ord`).

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, proof of Lemma 19.1.3.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Set Metric Order
open MMP.UnderlyingSpace Stacks.Chow
open scoped MMP.SubschemeOver

namespace MMP

open MMP.Intersection.Scheme (Subvariety)

open borelMooreHomology BorelMooreCross FundamentalClass

/-- The integral component at the generic point of an irreducible component is the component
with its reduced structure. -/
theorem integralComponentAt_componentGenericPoint {D : Scheme.{0}} (j : irreducibleComponents D) :
    integralComponentAt (Chow.componentGenericPoint j) =
      Scheme.IdealSheafData.vanishingIdeal ⟨j.1, isClosed_of_mem_irreducibleComponents _ j.2⟩ := by
  unfold integralComponentAt
  congr 1
  exact SetLike.coe_injective (Chow.closure_componentGenericPoint j)

/-- The generic point of the subvariety of a component is its generic point. -/
theorem genericPoint_ofIrreducibleComponent {D : Scheme.{0}} (j : irreducibleComponents D) :
    (Subvariety.ofIrreducibleComponent j).genericPoint = Chow.componentGenericPoint j := by
  have h1 := (Subvariety.ofIrreducibleComponent j).isGenericPoint_genericPoint
  have h2 : IsGenericPoint (Chow.componentGenericPoint j)
      ((Subvariety.ofIrreducibleComponent j).support : Set D) := by
    change closure _ = _
    rw [Chow.closure_componentGenericPoint, Subvariety.support_ofIrreducibleComponent]
  exact h1.eq h2

/-- The component's generic point is a generic point of `D` in Stacks' sense. -/
theorem componentGenericPoint_mem_genericPoints {D : Scheme.{0}} (j : irreducibleComponents D) :
    Chow.componentGenericPoint j ∈ genericPoints D := by
  change closure {Chow.componentGenericPoint j} ∈ irreducibleComponents D
  rw [Chow.closure_componentGenericPoint]
  exact j.2

end MMP

namespace MMP.Modules

open MMP
open MMP.Intersection.Scheme (dimension Subvariety)

open borelMooreHomology BorelMooreCross FundamentalClass

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X] [IsIntegral X]
  [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] [QuasiCompact (X ↘ Spec (.of ℂ))]
  {E : X.Modules} [E.IsQuasicoherent]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E 1]
  {σ : X ⟶ totalSpace E} [σ.IsOver (Spec (.of ℂ))]

/-- The delta-dimension of the generic point of a component of the zero scheme is `k`
(the components of `Z(σ)` have dimension `dim X - 1`). -/
theorem relativeDimension_componentGenericPoint_zeroLocus {k : ℕ}
    (hn : ((k + 1 : ℕ) : WithBot ℕ∞) = dimension X) (hσ : σ ≫ proj E = 𝟙 X)
    (h0 : σ ≠ zeroSection E) (j : irreducibleComponents (zeroLocus E σ).subscheme) :
    relativeDimension (fieldChowSituation ℂ).dimensionFunction
      ((zeroLocus E σ).subscheme ↘ Spec (.of ℂ)) (Chow.componentGenericPoint j) = k := by
  obtain ⟨n, hnk, hd⟩ := hasDim_irreducibleComponent_zeroLocus ℂ hn hσ h0 j
  replace hd : dimension (Scheme.IdealSheafData.vanishingIdeal
      ⟨j.1, isClosed_of_mem_irreducibleComponents _ j.2⟩).subscheme = (n : WithBot ℕ∞) := by
    rw [← hd]
    refine (MMP.topologicalKrullDim_subscheme_eq_support _).trans ?_
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have h := Chow.dimension_integralComponentAt (Chow.componentGenericPoint j)
  rw [integralComponentAt_componentGenericPoint] at h
  have h2 : ((relativeDimension (fieldChowSituation ℂ).dimensionFunction
      ((zeroLocus E σ).subscheme ↘ Spec (.of ℂ)) (Chow.componentGenericPoint j)).toNat :
        WithBot ℕ∞) = (n : WithBot ℕ∞) := h.symm.trans hd
  have h0' := relativeDimension_fieldChowSituation_nonneg ℂ
    ((zeroLocus E σ).subscheme ↘ Spec (.of ℂ)) (Chow.componentGenericPoint j)
  have h3 : (relativeDimension (fieldChowSituation ℂ).dimensionFunction
      ((zeroLocus E σ).subscheme ↘ Spec (.of ℂ)) (Chow.componentGenericPoint j)).toNat = n := by
    exact_mod_cast h2
  omega

variable (R : Type) [CommRing R]

/-- **Fulton's Lemma 19.1.3 near a general point of each component** (normal case). Let `X` be a
normal complex variety of dimension `k + 1`, `ℰ` a line bundle on `X` and `σ ≠ 0` a section of
`𝐕(ℰ) ⟶ X`, with zero scheme `D = Z(σ)`. For every fundamental class `cl(X)` and irreducible
component `Z_j` of `D`, there is a non-empty open `W ⊆ D(ℂ)` inside the regular part of `Z_j`,
missing the other components, on which `σ^*(u_ℰ) ∩ cl(X)` and the cycle class `cl_D([D]_k)` of
Stacks' cycle of `D` restrict to the same class. -/
theorem exists_opens_restrict_localizedTopChernCap_eq_cycleClass [IsNormal X] {k : ℕ}
    (hn : ((k + 1 : ℕ) : WithBot ℕ∞) = dimension X) (hσ : σ ≫ proj E = 𝟙 X)
    (h0 : σ ≠ zeroSection E)
    {μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X))
      (2 * (k + 1) : ℕ)} (hμ : IsVarietyFundamentalClass R hn μ)
    (j : irreducibleComponents (zeroLocus E σ).subscheme) :
    ∃ W : Opens (UnderlyingSpace ℂ (zeroLocus E σ).subscheme),
      (W : Set (UnderlyingSpace ℂ (zeroLocus E σ).subscheme)).Nonempty ∧
      (W : Set (UnderlyingSpace ℂ (zeroLocus E σ).subscheme)) ⊆
        mapFun (K := ℂ) (irreducibleComponentι (zeroLocus E σ).subscheme j) ''
          regularPart ℂ (irreducibleComponentScheme (zeroLocus E σ).subscheme j) ∧
      (∀ i, i ≠ j → Disjoint (W : Set (UnderlyingSpace ℂ (zeroLocus E σ).subscheme))
        (range (mapFun (K := ℂ) (irreducibleComponentι (zeroLocus E σ).subscheme i)))) ∧
      borelMooreHomology.restrict R (ModuleCat.of R R)
          (Y := TopCat.of (UnderlyingSpace ℂ (zeroLocus E σ).subscheme)) W (2 * k : ℕ)
          (borelMooreHomology.pushforward R (ModuleCat.of R R) (zeroLocusInvHom σ)
            (isProperMap_zeroLocusInvHom σ) (2 * k : ℕ)
            (BorelMooreCross.congrDegree R _ (by push_cast; ring)
              (localizedTopChernCap σ R 1 _ μ))) =
        borelMooreHomology.restrict R (ModuleCat.of R R)
          (Y := TopCat.of (UnderlyingSpace ℂ (zeroLocus E σ).subscheme)) W (2 * k : ℕ)
          (Chow.cycleClass R k (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
            ((zeroLocus E σ).subscheme ↘ Spec (.of ℂ)) (𝟙 _) k)) := by
  classical
  obtain ⟨c, hgen⟩ := exists_chart_genericPoint_mem σ j
  have : Nonempty c.1.1 := ⟨⟨_, hgen⟩⟩
  have hh0 := chartLocalCoord_ne_zero hσ h0 c
  have hZ := maximal_support_image_ofIrreducibleComponent_zeroLocus σ hσ c j hgen
  obtain ⟨m, U, g, hm, hco, -, -, hUX₀, hUreg, -, ⟨y₀, hy₀U, hy₀0⟩, hYreg, hYoth, -, -,
      ⟨e, ψ, he, hψ, hψs, hUeq, hψg⟩, hgh, -, hhg⟩ :=
    exists_localNormalForm (n := k + 1) hn c.1.2 hh0
      ((Subvariety.ofIrreducibleComponent j).image (zeroLocus E σ).subschemeι).ideal hZ
      (r := Units.mk0 _ (germToFunctionField_chartLocalCoord_ne_zero hσ h0 c)) rfl
  set h := chartLocalCoord σ hσ c with hhdef
  have hUreg' : e.source ∩ e ⁻¹' ψ.source ⊆ regularPart ℂ X := hUeq ▸ hUreg
  have hy₀U' : y₀ ∈ e.source ∩ e ⁻¹' ψ.source := hUeq ▸ hy₀U
  have hy₀g : g y₀ = 0 := (hgh y₀ hy₀U).2 hy₀0
  obtain ⟨O, hO, ε, δ, hε, hδ, hy₀O, hOU, Φ, hΦ1, hΦ2, hΦd⟩ :=
    exists_ballProductChart (k := k) hn he hψ hψs hUreg' hy₀U' (by rw [hψg y₀ hy₀U]; exact hy₀g)
  have hOU₀ : (O : Set (UnderlyingSpace ℂ X)) ⊆ U := hUeq ▸ hOU
  have hpX₀ : ∀ p ∈ O, ⊤ ≤ p.toHom ⁻¹ᵁ c.1.1 := fun p hp ↦
    (UnderlyingSpace.top_le_preimage_iff p c.1.1).2 (hUX₀ p (hOU₀ hp))
  have hOi : (O : Set (TopCat.of (UnderlyingSpace ℂ X))) ⊆ chartBase c := fun p hp ↦ hpX₀ p hp
  have hm0 : m ≠ 0 := by
    rintro rfl
    have := hhg y₀ hy₀U
    rw [hy₀0, pow_zero] at this
    exact zero_ne_one this
  have hgP : ∀ p : O, ballChartFst Φ (regularOpensInterMap hO p) = g p.1 := fun p ↦
    (hΦ1 _).trans (hψg p.1 (hOU₀ p.2))
  have heval : ∀ p : O, coord c (mapFun σ p.1) 0 = evalExt c.1.1 h p.1 := fun p ↦ by
    rw [evalExt_of_le h (hpX₀ p.1 p.2)]
    exact (eval_sectionCoord σ c _ p.1 (hpX₀ p.1 p.2) 0).symm
  have hh : ∀ p : O, coord c (mapFun σ p.1) 0 =
      ballChartFst Φ (regularOpensInterMap hO p) ^ m := fun p ↦ by
    rw [heval, hhg p.1 (hOU₀ p.2), hgP]
  have hz : setInter (Y := TopCat.of (UnderlyingSpace ℂ X)) O (zeroLocusSet σ) =
      (regularOpensInterMap hO).hom ⁻¹' (ballChartFst Φ ⁻¹' {0}) := by
    have e1 := preimage_inclHom_preimage_range_zeroSection σ hσ c O hOi
      (TopCat.ofHom ⟨fun p ↦ ballChartFst Φ (regularOpensInterMap hO p) ^ m,
        (continuous_pow m).comp (regularOpensInterMap hO ≫ ballChartFst Φ).hom.continuous⟩)
      (fun p ↦ (hh p).symm)
    ext p
    have e2 := congrArg (p ∈ ·) e1
    simp only [eq_iff_iff] at e2
    refine e2.trans ?_
    change ballChartFst Φ (regularOpensInterMap hO p) ^ m = 0 ↔
      ballChartFst Φ (regularOpensInterMap hO p) = 0
    exact pow_eq_zero_iff hm0
  have : ConnectedSpace (⟨ball (ψ (e y₀)).2 δ, isOpen_ball⟩ : Opens (EuclideanSpace ℂ (Fin k))) :=
    isConnected_iff_connectedSpace.1 ((convex_ball _ _).isConnected (nonempty_ball.2 hδ))
  obtain ⟨μB, hμB⟩ := exists_isFundamentalClass (R := R)
    (isOrientedAtlas_of_isManifold_complex
      (⟨ball (ψ (e y₀)).2 δ, isOpen_ball⟩ : Opens (EuclideanSpace ℂ (Fin k))))
    (euclideanComplexOrientationBasis k)
  have hW : ∀ q ∈ zeroLocusOpens σ O,
      mapFun (K := ℂ) (zeroLocus E σ).subschemeι q ∈ O ∧
      mapFun (K := ℂ) (zeroLocus E σ).subschemeι q ∈ U ∧
      evalExt c.1.1 h (mapFun (K := ℂ) (zeroLocus E σ).subschemeι q) = 0 := by
    intro q hq
    have hqO : mapFun (K := ℂ) (zeroLocus E σ).subschemeι q ∈ O := hq
    have hqN : (⟨_, hqO⟩ : O) ∈ setInter (Y := TopCat.of (UnderlyingSpace ℂ X)) O
        (zeroLocusSet σ) := (zeroLocusHom σ q).2
    rw [hz] at hqN
    have hg0 : g (mapFun (K := ℂ) (zeroLocus E σ).subschemeι q) = 0 := (hgP _).symm.trans hqN
    exact ⟨hqO, hOU₀ hqO, (hgh _ (hOU₀ hqO)).1 hg0⟩
  have hreg : ((zeroLocusOpens σ O : Opens _) : Set (UnderlyingSpace ℂ (zeroLocus E σ).subscheme)) ⊆
      mapFun (K := ℂ) (irreducibleComponentι (zeroLocus E σ).subscheme j) ''
        regularPart ℂ (irreducibleComponentScheme (zeroLocus E σ).subscheme j) := fun q hq ↦
    mem_image_regularPart_of_regularLocus_image (zeroLocus E σ).subschemeι
      ⟨_, (Subvariety.ofIrreducibleComponent j).isIntegral⟩ q
      (hYreg _ ⟨(hW q hq).2.1, (hW q hq).2.2⟩)
  have hdisj : ∀ i', i' ≠ j →
      Disjoint ((zeroLocusOpens σ O : Opens _) : Set (UnderlyingSpace ℂ (zeroLocus E σ).subscheme))
        (range (mapFun (K := ℂ) (irreducibleComponentι (zeroLocus E σ).subscheme i'))) := by
    intro i' hi'
    rw [Set.disjoint_left]
    intro q hq hq'
    have hy : q.toHom (IsLocalRing.closedPoint ℂ) ∈ i'.1 := by
      rw [range_mapFun_of_isClosedImmersion] at hq'
      rw [← range_irreducibleComponentι]
      exact hq'
    obtain ⟨T, hT, hTne, hyT⟩ := exists_maximal_ne_mem_of_mem_irreducibleComponent_zeroLocus
      σ hσ c hi' hy (hUX₀ _ (hW q hq).2.1)
    exact hYoth T hT hTne _ ⟨(hW q hq).2.1, (hW q hq).2.2⟩ hyT
  have hy₀N : y₀ ∈ zeroLocusSet σ := by
    have : (⟨y₀, hy₀O⟩ : O) ∈ setInter (Y := TopCat.of (UnderlyingSpace ℂ X)) O
        (zeroLocusSet σ) := by
      rw [hz]
      exact (hgP _).trans hy₀g
    exact this
  refine ⟨zeroLocusOpens σ O, ⟨(zeroLocusHomeomorph σ).symm ⟨y₀, hy₀N⟩, ?_⟩,
    hreg, hdisj, ?_⟩
  · change (((zeroLocusHomeomorph σ)
      ((zeroLocusHomeomorph σ).symm ⟨y₀, hy₀N⟩) : _) : UnderlyingSpace ℂ X) ∈ O
    rw [Homeomorph.apply_symm_apply]
    exact hy₀O
  have hj := relativeDimension_componentGenericPoint_zeroLocus hn hσ h0 j
  have hreg' : ((zeroLocusOpens σ O : Opens _) :
      Set (UnderlyingSpace ℂ (zeroLocus E σ).subscheme)) ⊆
      mapFun (K := ℂ) (integralComponentAt (Chow.componentGenericPoint j)).subschemeι ''
        regularPart ℂ (integralComponentAt (Chow.componentGenericPoint j)).subscheme := by
    have hV : (⟨integralComponentAt (Chow.componentGenericPoint j),
        isIntegral_integralComponentAt _⟩ : Subvariety (zeroLocus E σ).subscheme) =
        Subvariety.ofIrreducibleComponent j :=
      Subvariety.ext (integralComponentAt_componentGenericPoint j)
    intro q hq
    have hYq := hYreg _ ⟨(hW q hq).2.1, (hW q hq).2.2⟩
    rw [← hV] at hYq
    exact mem_image_regularPart_of_regularLocus_image (zeroLocus E σ).subschemeι
      ⟨integralComponentAt (Chow.componentGenericPoint j), isIntegral_integralComponentAt _⟩ q hYq
  have hWX : ∀ p : zeroLocusOpens σ O, mapFun (K := ℂ) (zeroLocus E σ).subschemeι p.1 ∈ e.source :=
    fun p ↦ (hOU (hW p.1 p.2).1).1
  have hWψ : ∀ p : zeroLocusOpens σ O,
      e (mapFun (K := ℂ) (zeroLocus E σ).subschemeι p.1) ∈ ψ.source :=
    fun p ↦ (hOU (hW p.1 p.2).1).2
  have hψd : ∀ p : zeroLocusOpens σ O,
      DifferentiableAt ℂ ψ (e (mapFun (K := ℂ) (zeroLocus E σ).subschemeι p.1)) := fun p ↦
    (hψ.differentiableOn (by simp)).differentiableAt (ψ.open_source.mem_nhds (hWψ p))
  have hψsd : ∀ p : zeroLocusOpens σ O,
      DifferentiableAt ℂ ψ.symm (ψ (e (mapFun (K := ℂ) (zeroLocus E σ).subschemeι p.1))) := fun p ↦
    (hψs.differentiableOn (by simp)).differentiableAt
      (ψ.open_target.mem_nhds (ψ.map_source (hWψ p)))
  have hρ : ∀ p : zeroLocusOpens σ O,
      (ψ (e (mapFun (K := ℂ) (zeroLocus E σ).subschemeι p.1))).1 = 0 := fun p ↦ by
    rw [hψg _ (hW p.1 p.2).2.1]
    exact (hgh _ (hW p.1 p.2).2.1).2 (hW p.1 p.2).2.2
  apply eq_of_pushforward_homeomorph_eq R
    ((zeroLocusOpensHomeomorph σ O).trans (localZeroHomeomorph σ hO hε Φ hz)) (2 * k : ℕ)
  rw [pushforward_restrict_zeroLocusOpens_eq_smul R hn σ hσ c hOi hO hε Φ hΦd m hh hz hμ hμB,
    Chow.pushforward_restrict_cycleClass_eq_smul_of_chart R (zeroLocus E σ).subschemeι j hj
      (zeroLocusOpens σ O) hreg' hdisj he hWX hμB
      ((zeroLocusOpensHomeomorph σ O).trans (localZeroHomeomorph σ hO hε Φ hz))
      (fun z ↦ (ψ z).1) hρ (fun p ↦ (hψd p).fst) ?_]
  · -- the coefficient of the component in `[D]_k` is the exponent `m` of the local normal form
    haveI := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of ℂ))
    have hgξ : ((Subvariety.ofIrreducibleComponent j).image
        (zeroLocus E σ).subschemeι).genericPoint =
        (zeroLocus E σ).subschemeι (Chow.componentGenericPoint j) := by
      rw [Subvariety.genericPoint_image, genericPoint_ofIrreducibleComponent]
    have hco : coheight ((Subvariety.ofIrreducibleComponent j).image
        (zeroLocus E σ).subschemeι).genericPoint = 1 := hco
    have hm : (m : ℤ) = X.ord (Units.mk0 _ (germToFunctionField_chartLocalCoord_ne_zero hσ h0 c) :
        X.functionField) ((Subvariety.ofIrreducibleComponent j).image
          (zeroLocus E σ).subschemeι).genericPoint := hm
    have hξX₀ : (zeroLocus E σ).subschemeι (Chow.componentGenericPoint j) ∈ c.1.1 := hgξ ▸ hgen
    have hcoeff := Chow.cycleAssociatedToClosedSubscheme_self_apply_eq_ord ℂ (X ↘ Spec (.of ℂ))
      (zeroLocus E σ) ⟨_, componentGenericPoint_mem_genericPoints j⟩ hj (hgξ ▸ hco) hξX₀ h hh0
      (stalk_zeroLocus_eq_span_germ σ hσ c hξX₀)
    have e : X.ord (X.germToFunctionField c.1.1 h)
        ((zeroLocus E σ).subschemeι (Chow.componentGenericPoint j)) = (m : ℤ) := by
      rw [hm, Units.val_mk0, hgξ]
    have hc' : (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
        ((zeroLocus E σ).subscheme ↘ Spec (.of ℂ)) (𝟙 _) k).1 (Chow.componentGenericPoint j) =
          (m : ℤ) := hcoeff.trans e
    rw [hc', natCast_zsmul, Nat.cast_smul_eq_nsmul]
  · intro e' he' p _
    refine ⟨fun z ↦ (ψ z).2, Filter.Eventually.of_forall fun p' ↦ ?_, (hψd p).snd, ?_⟩
    · rw [opens_atlas_apply _ he']
      exact hΦ2 _
    · exact OpenPartialHomeomorph.injective_fderiv_of_differentiableAt ψ (hWψ p) (hψd p) (hψsd p)

end MMP.Modules
