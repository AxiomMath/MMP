module

public import MMP.AlgebraicGeometry.MMP.Fourfold.ElementaryStepPreserved

/-!
# Elementary dlt steps of fourfolds are step diagrams

Let `(U, Δ)` be a projective `ℚ`-factorial dlt fourfold pair over `ℂ` with rational boundary and
canonical divisor `K`, let `R` be a `(K + Δ)`-negative extremal ray of `NE̅(U)` and `f : U ⟶ V` a
birational contraction of `R` onto a normal projective variety with `ρ(U/V) = 1` and `-(K + Δ)`
`f`-ample. If `(U⁺, Δ⁺)` is an output of the elementary step of `R`, written
`U ⟶ V ⟵ U⁺` with `f⁺` the flip of `f` when `f` is small and an isomorphism otherwise, then
`(U, Δ) → V ← (U⁺, Δ⁺)` is a step diagram with `D⁻ = K + Δ` and `D⁺ = K⁺ + Δ⁺`, where
`K⁺ = (f⁺)⁻¹_* f_* K`.

## Main results

* `MMP.Fourfold.IsProjectiveElementaryDltStep.isFourfoldStepDiagram`: the statement above.

## Implementation notes

* The elementary step is `MMP.Fourfold.IsProjectiveElementaryDltStep`, which records the pair,
  the negativity of `R`, that `f` is a contraction of `R` (`MMP.Fourfold.IsContractionOfRay`,
  including normality of `V`), birationality of `f` and `Δ⁺ = (f⁺)⁻¹_* f_* Δ`. In the divisorial
  case `f⁺` is an isomorphism rather than the identity of `V`, so `U⁺` is `V` up to isomorphism.
* The boundary of the positive side of `MMP.Fourfold.IsFourfoldStepDiagram` is by definition
  `(f⁺)⁻¹_* f_* Δ`, which is `Δ⁺` by `MMP.Fourfold.IsProjectiveElementaryDltStep.eq_flipTransform`;
  its canonical divisor is `(f⁺)⁻¹_* f_* K`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], §3.7
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori MMP.Fourfold

namespace MMP.FourfoldProofs.Oai4C3ElementaryStepIsStepDiagramProof

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- Every Cartier divisor is ample relative to an isomorphism. -/
private theorem isRelativelyAmple_of_isIso {X Y : Scheme.{0}} [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] (e : X ⟶ Y) [IsIso e] {L : Divisor X}
    (hL : L.IsCartier) : L.IsRelativelyAmple e hL := by
  haveI := hL.isInvertibleModule_divisorialSheaf
  intro y
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ y)
  refine ⟨V, hV, hyV, ?_⟩
  haveI : IsAffine (e ⁻¹ᵁ V) := hV.preimage e
  have hinv : Stacks.Ample.IsInvertibleModule (e ⁻¹ᵁ V).toScheme
      ((RingedSpaceModuleAdjunction.modulePullback (e ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj
        L.divisorialSheaf) := inferInstance
  exact (Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mpr
    (@AlgebraicGeometry.Scheme.Modules.isAmple_of_isAffine_of_isInvertible _ _ _ _ hinv)

/-- A `ℚ`-Cartier `ℚ`-divisor is ample relative to an isomorphism. -/
private theorem hasRelativelyAmpleMultiple_of_isIso {X Y : Scheme.{0}} [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] (e : X ⟶ Y) [IsIso e] {D : QDivisor X}
    (hD : D.IsQCartier) : D.HasRelativelyAmpleMultiple e := by
  obtain ⟨m, hm, L, hL, hLC⟩ := hD.exists_pos
  exact ⟨m, hm, L, hLC, hL, isRelativelyAmple_of_isIso e hLC⟩

/-- An isomorphism of normal varieties over `k` is a small morphism. -/
private theorem isSmallMorphism_of_isIso {k : Type} [Field k] {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    (hY : IsNormalVariety k sY) (e : X ⟶ Y) [IsIso e] (he : e ≫ sY = sX) :
    IsSmallMorphism sX sY e where
  isNormalVariety_source := hX
  isNormalVariety_target := hY
  comp_eq := he
  isProper := inferInstance
  isBirationalMorphism := isBirationalMorphism_of_isIso e
  two_le_codimension := by
    rw [(exceptionalSet_eq_bot_iff e).2 inferInstance]
    refine le_closedsCodimension_iff.2 fun W hW => ?_
    exact absurd (Set.subset_empty_iff.1 (by simpa using hW)) W.isIrreducible.nonempty.ne_empty

/-- An isomorphism is a projective morphism: followed by `S ≅ ℙ⁰_S` it is a closed immersion into
`ℙ⁰` over its target. -/
private theorem isProjectiveMorphism_of_isIso {X Y : Scheme.{0}} (e : X ⟶ Y) [IsIso e] :
    IsProjectiveMorphism e :=
  ⟨0, e ≫ (projectiveSpaceOver.zeroIsoBase Y).inv, inferInstance, by
    rw [Category.assoc, projectiveSpaceOver.zeroIsoBase_inv_comp_over, Category.comp_id]⟩

/-- A `ℚ`-divisor with a relatively ample Cartier multiple is `ℚ`-Cartier. -/
private theorem isQCartier_of_hasRelativelyAmpleMultiple {X Y : Scheme.{0}} [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {D : QDivisor X} {f : X ⟶ Y}
    (h : D.HasRelativelyAmpleMultiple f) : D.IsQCartier := by
  obtain ⟨m, hm, L, hL, hLD, -⟩ := h
  exact ⟨m, by exact_mod_cast hm.ne', L, hLD, hL⟩

/-- If `-D` is `ℚ`-Cartier then so is `D`. -/
private theorem isQCartier_of_neg {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    {D : QDivisor X} (h : (-D).IsQCartier) : D.IsQCartier := by
  obtain ⟨m, hm, hC⟩ := h
  exact ⟨-m, neg_ne_zero.mpr hm, by rwa [neg_smul, ← smul_neg]⟩

end MMP.FourfoldProofs.Oai4C3ElementaryStepIsStepDiagramProof

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori
  MMP.FourfoldProofs.Oai4C3ElementaryStepIsStepDiagramProof

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

/-- **The elementary step is a step diagram.** Let `(X, Δ)` be a projective `ℚ`-factorial dlt
fourfold pair over `ℂ` with canonical divisor `K`, and let `(X', Δ')` be the output of the
elementary step of a `(K + Δ)`-negative extremal ray `R` whose contraction `f : X ⟶ V` is
birational, with `V` projective, `ρ(X/V) = 1` and `-(K + Δ)` `f`-ample. Then
`X ⟶ V ⟵ X'` is a step diagram with `D⁻ = K + Δ` and `D⁺ = (f⁺)⁻¹_* f_* K + Δ'`. -/
@[mmp "lem_oai4_c3_elementary_step_is_step_diagram"]
public theorem IsProjectiveElementaryDltStep.isFourfoldStepDiagram {X V X' : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sV : V ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {K : Divisor X} {Δ : QDivisor X}
    {R : Set (NumericalCurveClasses sX)} {f : X ⟶ V} {fp : X' ⟶ V} {Δ' : QDivisor X'}
    (h : IsProjectiveElementaryDltStep sX sV sX' K Δ R f fp Δ')
    (hdim : topologicalKrullDim X = 4)
    (hV : MMP.Mori.IsProjectiveVariety ℂ sV) (hρ : relativePicardNumberN1 sX f = 1)
    (hamp : (-(Divisor.toQDivisor K + Δ)).HasRelativelyAmpleMultiple f) :
    IsFourfoldStepDiagram sX sV sX' K Δ f fp := by
  have hc := h.isContractionOfRay.toIsContraction
  have hX' := h.isProjectiveQFactorialDltPair_flipTransform hV hρ hamp
  have hX'n : IsNormalVariety ℂ sX' := hX'.isQFactorial.1
  have hDp : (Divisor.toQDivisor (flipTransform f fp K) + flipTransform f fp Δ).IsQCartier :=
    isQCartier_of_isQFactorial sX' hX'.isQFactorial _
  have hp : IsSmallMorphism sX' sV fp ∧ IsProjectiveMorphism fp ∧
      (Divisor.toQDivisor (flipTransform f fp K) + flipTransform f fp Δ).HasRelativelyAmpleMultiple
        fp := by
    rcases h.flip_or_divisorial with ⟨-, hfl⟩ | ⟨-, hiso⟩
    · refine ⟨hfl.isSmallMorphism_flip, hfl.isProjectiveMorphism_flip, ?_⟩
      have := hfl.hasRelativelyAmpleMultiple_flip
      rwa [map_add, MMP.Mori.flipTransform_toQDivisor] at this
    · exact ⟨isSmallMorphism_of_isIso hX'n hc.isNormalVariety_target fp h.comp_eq,
        isProjectiveMorphism_of_isIso fp, hasRelativelyAmpleMultiple_of_isIso fp hDp⟩
  obtain ⟨hs, hpp, hpa⟩ := hp
  have : MMP.Mori.IsVariety ℂ sX := hc.isNormalVariety_source.1
  have : MMP.Mori.IsVariety ℂ sV := hc.isNormalVariety_target.1
  have : MMP.Mori.IsVariety ℂ sX' := hX'n.1
  have : IsProper fp := hs.isProper
  exact
  { isProjectiveVariety_minus := h.isProjectiveQFactorialDltPair.isProjectiveVariety
    isNormalVariety_minus := hc.isNormalVariety_source
    dim_minus := hdim
    isProjectiveVariety_plus := hX'.isProjectiveVariety
    isNormalVariety_plus := hX'n
    dim_plus := by
      rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sV sX'
        hs.isBirationalMorphism, MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism
        sV sX h.isBirationalMorphism, hdim]
    isProjectiveVariety_target := hV
    isNormalVariety_target := hc.isNormalVariety_target
    comp_eq_minus := hc.comp_eq
    comp_eq_plus := h.comp_eq
    isProjectiveMorphism_minus := hc.isProjectiveMorphism
    isProjectiveMorphism_plus := hpp
    isBirationalMorphism_minus := h.isBirationalMorphism
    isIso_app_minus := hc.isIso_app
    isIso_app_plus := (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism
      sX' sV hX'n.1 hc.isNormalVariety_target fp hs.isBirationalMorphism).1
    isSmallMorphism_plus := hs
    isCanonicalDivisor := h.isProjectiveQFactorialDltPair.isCanonicalDivisor
    nonneg := h.isProjectiveQFactorialDltPair.isDltPair.1.2.1
    isQCartier_minus := isQCartier_of_neg (isQCartier_of_hasRelativelyAmpleMultiple hamp)
    isQCartier_plus := hDp
    hasRelativelyAmpleMultiple_minus := hamp
    hasRelativelyAmpleMultiple_plus := hpa }

end MMP.Fourfold

end
