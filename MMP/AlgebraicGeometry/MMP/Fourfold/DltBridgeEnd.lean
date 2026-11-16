module

public import MMP.AlgebraicGeometry.MMP.Fourfold.ElementaryDlt
public import MMP.AlgebraicGeometry.MMP.Fourfold.GraphDivisor
public import MMP.Attr
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagramBranches
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram.GraphDivisorSupport
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram.ChainComparison
import MMP.AlgebraicGeometry.MMP.Contraction.VerticalFactorization
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.MMP.Fourfold.ElementaryStepDiagram
import MMP.AlgebraicGeometry.MMP.Contraction.DltRayContraction

/-!
# The nef end of a dlt bridge lies over the positive model of a permitted step

Let `(X, B) → Z ← (X⁺, B⁺)` be a permitted step of projective lc complex fourfold pairs with
rational boundary, with contraction `f : X ⟶ Z` and `f⁺ : X⁺ ⟶ Z`, and put
`D⁺ = K_{X⁺} + B⁺`. Let `p : (U, Δ) ⟶ (X, B)` be a crepant dlt lift and let
`(U_j, Δ_j)_{0 ≤ j ≤ m}` be an elementary dlt program over `Z` from `(U, Δ)`, with
`h₀ = f ∘ p`, whose end `K_{U_m} + Δ_m` is nef over `Z`. Then there is a projective birational
morphism `p' : U_m ⟶ X⁺` over `Z` with `K_{U_m} + Δ_m = p'^* D⁺`; that is, `Δ_m` is the
crepant boundary of `(X⁺, B⁺)` on `U_m`.

The proof compares both `U_m` and `X⁺` with `(X, B)` on a common resolution: the pull-back of
`K_X + B` is the pull-back of the end divisor plus an effective exceptional divisor on both
sides, and since `K_{U_m} + Δ_m` is nef and `D⁺` is ample over `Z`, the birational map
`U_m ⇢ X⁺` is a morphism along which `D⁺` pulls back to `K_{U_m} + Δ_m`.

## Main results

* `MMP.Fourfold.IsPermittedStep.exists_isCrepantBoundary_of_isRelativelyNef`.

## Implementation notes

The equality `K_{U_m} + Δ_m = p'^*(K_{X⁺} + B⁺)` is stated through discrepancies, as the
crepancy of `MMP.Fourfold.IsCrepantDltLift`: `Δ_m` is the crepant boundary
(`MMP.Mori.IsCrepantBoundary`) of `(X⁺, B⁺)` on `U_m` along `p'`, where
`K_{X⁺} = (f⁺)⁻¹_* f_* K_X` and `B⁺ = (f⁺)⁻¹_* f_* B` as in `MMP.Fourfold.IsPermittedStep`. This
is independent of the canonical divisors chosen on the models of the program, which are only
determined up to linear equivalence. The morphism `p'` is moreover over `ℂ` and over `Z`.

## References

* [OAI4], Termination for projective lc fourfolds.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.OAI4C3DltBridgeEndIdentified

open MMP.Mori MMP.Fourfold MMP.Fourfold.Oai4C1

/-! ### Isomorphisms of targets -/

section Iso

universe u

/-- Precomposition with an isomorphism preserves projectivity. -/
private theorem isProjectiveMorphism_isIso_comp {A B S : Scheme.{u}} (e : A ⟶ B) [IsIso e]
    {g : B ⟶ S} (hg : IsProjectiveMorphism g) : IsProjectiveMorphism (e ≫ g) := by
  obtain ⟨n, i, hi, hig⟩ := hg
  exact ⟨n, e ≫ i, inferInstance, by rw [Category.assoc, hig]⟩

/-- Composing with an isomorphism of targets does not change `f^* N¹(Z)_ℝ`. -/
private theorem pullbackNumericalClasses_comp_isIso {k : Type u} [Field k] {X Z Z' : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (f : X ⟶ Z) (e : Z ⟶ Z') [IsIso e] :
    pullbackNumericalClasses sX (f ≫ e) = pullbackNumericalClasses sX f := by
  unfold pullbackNumericalClasses
  congr 1
  ext d
  constructor
  · rintro ⟨E, M, hM, ⟨i⟩, rfl⟩
    exact ⟨E, (Scheme.Modules.pullback e).obj M, inferInstance,
      ⟨i ≪≫ ((Scheme.Modules.pullbackComp f e).app M).symm⟩, rfl⟩
  · rintro ⟨E, M, hM, ⟨i⟩, rfl⟩
    refine ⟨E, (Scheme.Modules.pullback (inv e)).obj M, inferInstance, ⟨?_⟩, rfl⟩
    have φ : (Scheme.Modules.pullback e).obj ((Scheme.Modules.pullback (inv e)).obj M) ≅ M :=
      (Scheme.Modules.pullbackComp e (inv e)).app M ≪≫
        (Scheme.Modules.pullbackCongr (IsIso.hom_inv_id e)).app M ≪≫
        (Scheme.Modules.pullbackId Z).app M
    exact i ≪≫ (Scheme.Modules.pullback f).mapIso φ.symm ≪≫
      (Scheme.Modules.pullbackComp f e).app _

/-- Composing with an isomorphism of targets does not change the relative Picard number. -/
private theorem relativePicardNumberN1_comp_isIso {k : Type u} [Field k] {X Z Z' : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (f : X ⟶ Z) (e : Z ⟶ Z') [IsIso e] :
    relativePicardNumberN1 sX (f ≫ e) = relativePicardNumberN1 sX f := by
  rw [relativePicardNumberN1, relativePicardNumberN1, pullbackNumericalClasses_comp_isIso]

/-- Relative ampleness over `Z'` passes to `Z` along an isomorphism `Z ≅ Z'`. -/
private theorem hasRelativelyAmpleMultiple_of_comp_isIso {X Y Y' : Scheme.{u}} [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {D : QDivisor X} {f : X ⟶ Y} (e : Y ⟶ Y') [IsIso e]
    (h : D.HasRelativelyAmpleMultiple (f ≫ e)) : D.HasRelativelyAmpleMultiple f := by
  obtain ⟨m, hm, L, hL, hLD, hamp⟩ := h
  refine ⟨m, hm, L, hL, hLD, fun y => ?_⟩
  obtain ⟨V, hV, hyV, hA⟩ := hamp (e y)
  exact ⟨e ⁻¹ᵁ V, hV.preimage_of_isIso e, hyV, hA⟩

end Iso

/-! ### Elementary steps are step diagrams -/

/-- An elementary dlt step of a fourfold is a step diagram: the contraction of the ray is
identified, by rigidity, with the contraction given by
`MMP.Fourfold.IsProjectiveQFactorialDltPair.exists_isContractionOfRay`, whose target is projective,
with relative Picard number one and `-(K + Δ)` relatively ample. -/
private theorem isFourfoldStepDiagram_of_isProjectiveElementaryDltStep {X V X' : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sV : V ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {K : Divisor X} {Δ : QDivisor X}
    {R : Set (NumericalCurveClasses sX)} {f : X ⟶ V} {fp : X' ⟶ V} {Δ' : QDivisor X'}
    (h : IsProjectiveElementaryDltStep sX sV sX' K Δ R f fp Δ')
    (hdim : topologicalKrullDim X = 4) :
    IsFourfoldStepDiagram sX sV sX' K Δ f fp := by
  have hpair := h.isProjectiveQFactorialDltPair
  have hU := hpair.isProjectiveVariety
  obtain ⟨V', sV', g, hg, hV'p, hρ, hamp⟩ :=
    hpair.exists_isContractionOfRay h.isNegativeExtremalRayOf
  obtain ⟨-, hext, -⟩ := h.isNegativeExtremalRayOf
  have hf := h.isContractionOfRay
  obtain ⟨e, he, -⟩ := existsUnique_comp_eq_of_isContractionOfRay hU hg.isProjectiveMorphism
    hg.comp_eq hext (fun C hC => (hg.isContractedBy_iff C).mpr hC) hf
  obtain ⟨e', he', -⟩ := existsUnique_comp_eq_of_isContractionOfRay hU hf.isProjectiveMorphism
    hf.comp_eq hext (fun C hC => (hf.isContractedBy_iff C).mpr hC) hg
  obtain ⟨_, _, huf⟩ := existsUnique_comp_eq_of_isContractionOfRay hU hf.isProjectiveMorphism
    hf.comp_eq hext (fun C hC => (hf.isContractedBy_iff C).mpr hC) hf
  obtain ⟨_, _, hug⟩ := existsUnique_comp_eq_of_isContractionOfRay hU hg.isProjectiveMorphism
    hg.comp_eq hext (fun C hC => (hg.isContractedBy_iff C).mpr hC) hg
  have h1 : e ≫ e' = 𝟙 V :=
    (huf _ (show f ≫ e ≫ e' = f by rw [← Category.assoc, he, he'])).trans
      (huf _ (Category.comp_id f)).symm
  have h2 : e' ≫ e = 𝟙 V' :=
    (hug _ (show g ≫ e' ≫ e = g by rw [← Category.assoc, he', he])).trans
      (hug _ (Category.comp_id g)).symm
  haveI : IsIso e := ⟨⟨e', h1, h2⟩⟩
  subst he
  have hes : e ≫ sV' = sV := by
    have : IsProper f := isProper_of_isProjectiveMorphism _ hf.isProjectiveMorphism
    have : IsIso f.c := @NatIso.isIso_of_isIso_app _ _ _ _ _ _ f.c fun U => hf.isIso_app U.unop
    obtain ⟨_, _, hu⟩ := MMP.existsUnique_comp_eq_of_isIso_c f (f ≫ sV) fun x x' hxx => by
      simp only [Scheme.Hom.comp_apply, hxx]
    exact (hu _ (show f ≫ e ≫ sV' = f ≫ sV by rw [← Category.assoc, hg.comp_eq, hf.comp_eq])).trans
      (hu sV rfl).symm
  have hVp : MMP.Mori.IsProjectiveVariety ℂ sV := by
    haveI : AlgebraicGeometry.IsVariety ℂ sV := hf.isNormalVariety_target.1
    exact ⟨hes ▸ isProjectiveMorphism_isIso_comp e hV'p.isProjective⟩
  exact h.isFourfoldStepDiagram hdim hVp
    (by rwa [← relativePicardNumberN1_comp_isIso sX f e])
    (hasRelativelyAmpleMultiple_of_comp_isIso e hamp)

/-! ### Canonical divisors along steps -/

/-- **The strict transform of a canonical divisor along a step is canonical.** For a proper
birational morphism `f : X ⟶ V` and a small morphism `f⁺ : X⁺ ⟶ V` of normal complex varieties,
the divisor `(f⁺)⁻¹_* f_* K` of a canonical divisor `K` of `X` is a canonical divisor of `X⁺`,
provided `X⁺` has some canonical divisor of the same index. -/
private theorem isCanonicalDivisor_flipTransform {X V X' : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral X'] [IsLocallyNoetherian X']
    [IsNormal X'] [CompactSpace X'] {sX : X ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)}
    {sX' : X' ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX) (hV : IsNormalVariety ℂ sV)
    {f : X ⟶ V} [IsProper f] (hf : IsBirationalMorphism f) (hfs : f ≫ sV = sX) {fp : X' ⟶ V}
    (hfp : IsSmallMorphism sX' sV fp) {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    {K' : Divisor X'} (hK' : K'.IsCanonicalDivisor sX' n) :
    Divisor.IsCanonicalDivisor sX' n (flipTransform f fp K) := by
  haveI : IsIntegral V := hV.1.toIsIntegral
  haveI : IsNormal V := hV.2
  haveI : LocallyOfFiniteType sV := hV.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
  haveI : QuasiCompact sV := hV.1.toQuasiCompact
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  haveI : MMP.Mori.IsVariety ℂ sX := hX.1
  haveI : MMP.Mori.IsVariety ℂ sV := hV.1
  have hXV : IsNormalVariety ℂ (f ≫ sV) := by rwa [hfs]
  haveI : LocallyOfFiniteType (f ≫ sV) := hXV.1.toLocallyOfFiniteType
  haveI := hf.isDominant
  have hdimV : topologicalKrullDim V = n := by
    rw [← hK.topologicalKrullDim_eq]
    exact MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sV sX hf
  obtain ⟨ω, hω0, hω⟩ := Main.exists_divisorOfForm_eq_transformDivisor hV hXV hf hdimV
    (by rwa [hfs])
  have hfpb := hfp.isBirationalMorphism
  haveI := hfpb.isDominant
  have hX'n := hfp.isNormalVariety_source
  obtain rfl : fp ≫ sV = sX' := hfp.comp_eq
  haveI : LocallyOfFiniteType (fp ≫ sV) := hX'n.1.toLocallyOfFiniteType
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sV) hdimV
  have hτ0 := Main.pullbackRationalPluriForms_ne_zero fp hfpb.functionFieldMap_bijective hd hω0
  have hlin := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hX'n hK' hτ0
  rw [one_zsmul] at hlin
  suffices e : flipTransform f fp K = divisorOfForm (pullbackRationalPluriForms sV fp ω) by
    rw [e]; exact hK'.of_linearlyEquivalent hlin
  refine Finsupp.ext fun P => ?_
  have hco : Order.coheight (fp P.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus _
      (map_genericPoint_mem_biregularLocus hfp.two_le_codimension P), P.coheight_genericPoint]
  have hQ : fp P.genericPoint = (PrimeDivisor.ofCoheightOne _ hco).genericPoint :=
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm
  haveI := MMP.Fourfold.isIso_stalkMap_of_map_eq_genericPoint hfpb hQ
  have h1 := inverseTransformDivisor_apply_of_map_genericPoint hQ
    (by have := map_genericPoint_mem_biregularLocus hfp.two_le_codimension P; rwa [hQ] at this)
    (RationalMap.transformDivisor (X := X) f.toRationalMap K)
  rw [flipTransform, AddMonoidHom.comp_apply, h1, ← hω]
  change (divisorOfForm ω).coeff _ = (divisorOfForm _).coeff P
  rw [coeff_divisorOfForm, coeff_divisorOfForm,
    MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso fp hfpb.functionFieldMap_bijective
      hd P _ hQ ω]

/-- Transported canonical divisors along an elementary dlt program: `K₀` on `X₀ = X`, and
`K_{j+1} = (f_j⁺)⁻¹_* (f_j)_* K_j`. -/
private noncomputable def transportedDivisor {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {K : Divisor X}
    {Δ : QDivisor X} (P : ElementaryDltProgram sX K Δ) (K₀ : Divisor X) :
    ∀ j, Divisor (modelSeq X P.Y j)
  | 0 => K₀
  | j + 1 => flipTransform (P.f j) (P.fp j) (transportedDivisor P K₀ j)

/-! ### Linear equivalence -/

section LinearEquivalence

variable {X : Scheme.{0}} [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]

/-- Intersection numbers of `K + Δ` with a curve depend on `K` only up to linear
equivalence. -/
private theorem intersectionNumber_add_eq_of_linearlyEquivalent {sX : X ⟶ Spec (.of ℂ)}
    [QuasiCompact sX] {C : Scheme.{0}} (i : C ⟶ X) [IsProper (i ≫ sX)]
    (hdim : topologicalKrullDim C ≤ 1) {K₁ K₂ : Divisor X} (h : K₁.LinearlyEquivalent K₂)
    (Δ : QDivisor X) (h₁ : (Divisor.toQDivisor K₁ + Δ).IsQCartier)
    (h₂ : (Divisor.toQDivisor K₂ + Δ).IsQCartier) :
    (Divisor.toQDivisor K₁ + Δ).intersectionNumber ℂ sX i hdim h₁ =
      (Divisor.toQDivisor K₂ + Δ).intersectionNumber ℂ sX i hdim h₂ := by
  obtain ⟨D', hD', hD'c⟩ := QDivisor.isCartierDivisor_cartierIndex_smul h₂
  set m := (Divisor.toQDivisor K₂ + Δ).cartierIndex h₂
  have hm := QDivisor.cartierIndex_pos h₂
  obtain ⟨φ, hφ⟩ := h
  set a : Additive (RationalFunctions X)ˣ := (m : ℤ) • Additive.ofMul φ with ha
  set G := D' + principalDivisorHom a with hG_def
  have hGc : G.IsCartier := hD'c.add (Divisor.isCartier_principalDivisor _)
  have hG : Divisor.toQDivisor G = (m : ℤ) • (Divisor.toQDivisor K₁ + Δ) := by
    have e : principalDivisorHom a = (m : ℤ) • (K₁ - K₂) := by
      rw [ha, map_zsmul, principalDivisorHom_apply, toMul_ofMul, hφ]
    rw [hG_def, e, map_add, hD', map_zsmul, map_sub, ← smul_add]
    congr 1
    abel
  have hGD : G.LinearlyEquivalent D' := ⟨a.toMul, by
    rw [hG_def, add_sub_cancel_left, principalDivisorHom_apply]⟩
  rw [QDivisor.intersectionNumber_eq_of_smul ℂ sX i hdim _ h₁ hm G hGc hG,
    QDivisor.intersectionNumber_eq_of_smul ℂ sX i hdim _ h₂ hm D' hD'c hD']
  congr 2
  haveI := hGc.isInvertibleModule_divisorialSheaf
  haveI := hD'c.isInvertibleModule_divisorialSheaf
  exact degreeOn_eq_of_iso ℂ sX i hdim hGD.divisorialSheafIso

/-- Relative nefness of `K + Δ` depends on `K` only up to linear equivalence. -/
private theorem isRelativelyNef_add_of_linearlyEquivalent {Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX] {f : X ⟶ Y} {K K' : Divisor X} {Δ : QDivisor X}
    (h : (Divisor.toQDivisor K + Δ).IsRelativelyNef sX f) (hK : K.LinearlyEquivalent K') :
    (Divisor.toQDivisor K' + Δ).IsRelativelyNef sX f := by
  have hD := h.1
  have hD' := hD.add_of_linearlyEquivalent hK
  refine QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sX hD' fun C hC => ?_
  rw [← intersectionNumber_add_eq_of_linearlyEquivalent C.ι C.dim_le hK Δ hD hD']
  exact MMP.Fourfold.QDivisor.IsRelativelyNef.intersectionNumber_nonneg sX h hD C hC

end LinearEquivalence

/-- A step diagram stays a step diagram when the canonical divisor `K⁻` is replaced by a
canonical divisor `K'` with `K⁻ ∼ K'` and `(f⁺)⁻¹_* f_* K⁻ ∼ (f⁺)⁻¹_* f_* K'`. -/
private theorem isFourfoldStepDiagram_of_linearlyEquivalent {Xm Xp Z : Scheme.{0}} [IsIntegral Xm]
    [CompactSpace Xm] [IsLocallyNoetherian Xm] [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp]
    [IsLocallyNoetherian Xp] [IsNormal Xp] {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    {sXp : Xp ⟶ Spec (.of ℂ)} {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) {K' : Divisor Xm}
    (hK' : ∃ m : ℕ, K'.IsCanonicalDivisor sXm m) (hKK' : K.LinearlyEquivalent K')
    (hpl : Divisor.LinearlyEquivalent (flipTransform fm fp K) (flipTransform fm fp K')) :
    IsFourfoldStepDiagram sXm sZ sXp K' B fm fp := by
  have e : ∀ L : Divisor Xm, -(Divisor.toQDivisor L + B) = Divisor.toQDivisor (-L) + -B := by
    intro L; rw [map_neg]; abel
  exact
  { h with
    isCanonicalDivisor := hK'
    isQCartier_minus := h.isQCartier_minus.add_of_linearlyEquivalent hKK'
    isQCartier_plus := h.isQCartier_plus.add_of_linearlyEquivalent hpl
    hasRelativelyAmpleMultiple_minus := by
      rw [e]
      refine Main.hasRelativelyAmpleMultiple_add_of_linearlyEquivalent ?_
        hKK'.neg
      rw [← e]
      exact h.hasRelativelyAmpleMultiple_minus
    hasRelativelyAmpleMultiple_plus :=
      Main.hasRelativelyAmpleMultiple_add_of_linearlyEquivalent h.hasRelativelyAmpleMultiple_plus
        hpl }

/-- A pull-back along `f` is one along any morphism equal to `f`. -/
private theorem isPullback_of_eq {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] {f g : X ⟶ Y} (e : f = g) {D : QDivisor Y}
    {hf : ∀ T : irreducibleComponents X, f (componentGenericPoint X T) ∉ D.supp}
    {hg : ∀ T : irreducibleComponents X, g (componentGenericPoint X T) ∉ D.supp} {D' : QDivisor X}
    (h : D.IsPullback f hf D') : D.IsPullback g hg D' := by
  subst e; exact h

/-- An integral scheme of finite type over `ℂ` of dimension `r + 1` has a point of
coheight one. -/
private theorem exists_coheight_eq_one {V : Scheme.{0}} [IsIntegral V] [CompactSpace V]
    (sV : V ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sV] {r : ℕ}
    (hdim : topologicalKrullDim V = (r + 1 : ℕ)) : ∃ y : V, Order.coheight y = 1 := by
  obtain ⟨x, -, hx⟩ := (isClosed_univ (X := V)).exists_closed_singleton Set.univ_nonempty
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sV x
  rw [hx.closure_eq, hdim] at h
  have : Nonempty (TopologicalSpace.IrreducibleCloseds ({x} : Set V)) :=
    ⟨⟨{⟨x, rfl⟩}, isIrreducible_singleton, isClosed_discrete _⟩⟩
  rw [le_antisymm (topologicalKrullDim_zero_of_discreteTopology _) Order.krullDim_nonneg,
    zero_add] at h
  have hc : Order.coheight x = (r + 1 : ℕ) := by exact_mod_cast h
  rcases r.eq_zero_or_pos with rfl | hr
  · exact ⟨x, by simpa using hc⟩
  obtain ⟨y, -, hy⟩ := (Order.coe_lt_coheight_iff (n := 1) (by rw [hc]; exact ENat.coe_lt_top _)).mp
    (by rw [hc]; exact_mod_cast Nat.succ_lt_succ hr)
  exact ⟨y, by exact_mod_cast hy⟩

/-- The index of a canonical divisor is the dimension. -/
private theorem index_eq_of_isCanonicalDivisor {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] {s : X ⟶ Spec (.of ℂ)} {n d : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor s n)
    (hd : topologicalKrullDim X = d) : n = d := by
  have h := hK.topologicalKrullDim_eq
  rw [hd] at h
  exact_mod_cast h.symm

/-- **The comparison divisor of one step diagram.** For a fourfold step diagram
`(X, B) → Z ← (X⁺, B⁺)` with `K⁺ = (f⁺)⁻¹_* f_* K`, `B⁺ = (f⁺)⁻¹_* f_* B`, and birational
morphisms `q : W ⟶ X`, `q⁺ : W ⟶ X⁺` over `ℂ` from a normal projective variety with
`q ≫ f = q⁺ ≫ f⁺`, the divisor `q^*(K + B) - q⁺^*(K⁺ + B⁺)` is effective and `q⁺`-exceptional. -/
private theorem pullback_sub_pullback_of_isFourfoldStepDiagram {X Z X' W : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsIntegral W] [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
    {K : Divisor X} {B : QDivisor X} {f : X ⟶ Z} {fp : X' ⟶ Z}
    (hS : IsFourfoldStepDiagram sX sZ sX' K B f fp) {sW : W ⟶ Spec (.of ℂ)}
    (hW : MMP.Mori.IsProjectiveVariety ℂ sW) (hWn : IsNormalVariety ℂ sW) {q : W ⟶ X}
    {q' : W ⟶ X'} (hqs : q ≫ sX = sW) (hq's : q' ≫ sX' = sW) (hq : IsBirationalMorphism q)
    (hq' : IsBirationalMorphism q') (hcomp : q ≫ f = q' ≫ fp)
    (h₁ : ∀ T : irreducibleComponents W,
      q (componentGenericPoint W T) ∉ (Divisor.toQDivisor K + B).supp)
    (h₂ : ∀ T : irreducibleComponents W, q' (componentGenericPoint W T) ∉
      (Divisor.toQDivisor (flipTransform f fp K) + flipTransform f fp B).supp) :
    0 ≤ (Divisor.toQDivisor K + B).pullback hS.isQCartier_minus h₁ -
        (Divisor.toQDivisor (flipTransform f fp K) + flipTransform f fp B).pullback
          hS.isQCartier_plus h₂ ∧
      RationalMap.transformDivisor (X := W) q'.toRationalMap
        ((Divisor.toQDivisor K + B).pullback hS.isQCartier_minus h₁ -
          (Divisor.toQDivisor (flipTransform f fp K) + flipTransform f fp B).pullback
            hS.isQCartier_plus h₂) = 0 := by
  let V : ℕ → Scheme.{0} := fun j => match j with
    | 0 => X
    | _ + 1 => X'
  haveI : ∀ j, IsIntegral (V j) := fun j => match j with
    | 0 => inferInstanceAs (IsIntegral X)
    | _ + 1 => inferInstanceAs (IsIntegral X')
  haveI : ∀ j, CompactSpace (V j) := fun j => match j with
    | 0 => inferInstanceAs (CompactSpace X)
    | _ + 1 => inferInstanceAs (CompactSpace X')
  haveI : ∀ j, IsLocallyNoetherian (V j) := fun j => match j with
    | 0 => inferInstanceAs (IsLocallyNoetherian X)
    | _ + 1 => inferInstanceAs (IsLocallyNoetherian X')
  haveI : ∀ j, IsNormal (V j) := fun j => match j with
    | 0 => inferInstanceAs (IsNormal X)
    | _ + 1 => inferInstanceAs (IsNormal X')
  let sV : ∀ j, V j ⟶ Spec (.of ℂ) := fun j => match j with
    | 0 => sX
    | _ + 1 => sX'
  let KV : ∀ j, Divisor (V j) := fun j => match j with
    | 0 => K
    | _ + 1 => flipTransform f fp K
  let ΘV : ∀ j, QDivisor (V j) := fun j => match j with
    | 0 => B
    | _ + 1 => flipTransform f fp B
  let g : ∀ j, V j ⟶ Z := fun j => match j with
    | 0 => f
    | _ + 1 => fp
  let qV : ∀ j, W ⟶ V j := fun j => match j with
    | 0 => q
    | _ + 1 => q'
  have hSV : ∀ k < 1, IsFourfoldStepDiagram (sV k) sZ (sV (k + 1)) (KV k) (ΘV k) (g k) fp :=
    fun k hk => by obtain rfl := Nat.lt_one_iff.mp hk; exact hS
  have hKV : ∀ k < 1, KV (k + 1) = flipTransform (g k) fp (KV k) := fun k hk => by
    obtain rfl := Nat.lt_one_iff.mp hk; rfl
  have hΘV : ∀ k < 1, ΘV (k + 1) = flipTransform (g k) fp (ΘV k) := fun k hk => by
    obtain rfl := Nat.lt_one_iff.mp hk; rfl
  have hqb : ∀ k ≤ 1, IsBirationalMorphism (qV k) := fun k hk => by
    rcases k with _ | _ | k
    · exact hq
    · exact hq'
    · omega
  have hcV : ∀ k < 1, qV k ≫ g k = qV (k + 1) ≫ fp := fun k hk => by
    obtain rfl := Nat.lt_one_iff.mp hk; exact hcomp
  exact ⟨ProgramComparison.pullback_sub_pullback_succ_nonneg sV KV ΘV (fun _ => sZ) g
      (fun _ => fp) 0 hS rfl rfl sW hW hWn q q' hqs hq's hq hq' hcomp hS.isQCartier_minus
      hS.isQCartier_plus h₁ h₂,
    MMP.Fourfold.transformDivisor_pullback_sub_pullback_eq_zero 1 sV KV ΘV (fun _ => sZ) g
      (fun _ => fp) hSV hKV hΘV qV hqb hcV hS.isQCartier_minus hS.isQCartier_plus h₁ h₂⟩

end MMP.OAI4C3DltBridgeEndIdentified

namespace MMP.Fourfold

open MMP.Mori MMP.Fourfold.Oai4C1 MMP.OAI4C3DltBridgeEndIdentified

/-- **The nef end of a dlt bridge lies over the positive model.** Let `(X, B) → Z ← (X⁺, B⁺)`
be a permitted step of projective lc complex fourfold pairs, `p : (U, Δ) ⟶ (X, B)` a crepant
dlt lift, and `P` an elementary dlt program over `Z` from `(U, Δ)` with `h₀ = p ≫ f` whose end
`K_{U_m} + Δ_m` is nef over `Z`. Then there is a projective birational morphism
`p' : U_m ⟶ X⁺` over `ℂ` and over `Z` such that `Δ_m` is the crepant boundary of `(X⁺, B⁺)` on
`U_m`, i.e. `K_{U_m} + Δ_m = p'^*(K_{X⁺} + B⁺)`. -/
@[mmp "lem_oai4_c3_dlt_bridge_end_identified"]
public theorem IsPermittedStep.exists_isCrepantBoundary_of_isRelativelyNef
    {X Z X' U : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsIntegral U] [CompactSpace U] [IsLocallyNoetherian U] [IsNormal U]
    (hdim : topologicalKrullDim X = 4)
    {K : Divisor X} {B : QDivisor X} {R : Set (NumericalCurveClasses sX)}
    {f : X ⟶ Z} {fp : X' ⟶ Z} (hstep : IsPermittedStep sX sZ sX' K B R f fp)
    {p : U ⟶ X} {Δ : QDivisor U} (hlift : IsCrepantDltLift sX K B p Δ)
    {KU : Divisor U} (P : RelativeElementaryDltProgram (p ≫ sX) KU Δ (p ≫ f))
    (hnef : (Divisor.toQDivisor (divisorSeq KU P.KY P.n.toNat) +
        divisorSeq Δ P.ΔY P.n.toNat).IsRelativelyNef (modelStr (p ≫ sX) P.sY P.n.toNat)
        (modelMap (p ≫ f) P.hY P.n.toNat)) :
    ∃ p' : modelSeq U P.Y P.n.toNat ⟶ X',
      p' ≫ sX' = modelStr (p ≫ sX) P.sY P.n.toNat ∧
      p' ≫ fp = modelMap (p ≫ f) P.hY P.n.toNat ∧
      IsProjectiveMorphism p' ∧
      ∃ (hY : IsNormalVariety ℂ (p' ≫ sX')) (hp' : IsBirationalMorphism p') (n : ℕ),
        IsCrepantBoundary sX' n (flipTransform f fp K) (flipTransform f fp B) p' hY hp'
          (divisorSeq Δ P.ΔY P.n.toNat) := by
  set m := P.n.toNat
  have hPn : P.n = (m : ℕ∞) := (ENat.coe_toNat P.n_ne_top).symm
  have hlt : ∀ k : ℕ, k < m → (k : ℕ∞) < P.n := fun k hk => by rw [hPn]; exact_mod_cast hk
  have hle : ∀ k : ℕ, k ≤ m → (k : ℕ∞) ≤ P.n := fun k hk => by rw [hPn]; exact_mod_cast hk
  -- the permitted step `X → Z ← X⁺`
  have hSB := hstep.isFourfoldStepDiagram hdim
  have hZn := hSB.isNormalVariety_target
  have hZp := hSB.isProjectiveVariety_target
  have hXn := hSB.isNormalVariety_minus
  have hX'n := hSB.isNormalVariety_plus
  haveI : IsIntegral Z := hZn.1.toIsIntegral
  haveI : IsNormal Z := hZn.2
  haveI : LocallyOfFiniteType sZ := hZn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsSeparated sZ := hZn.1.toIsSeparated
  haveI : IsSeparated sX := hXn.1.toIsSeparated
  haveI : IsSeparated sX' := hX'n.1.toIsSeparated
  haveI : LocallyOfFiniteType sX := hXn.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sX' := hX'n.1.toLocallyOfFiniteType
  haveI : IsProper f := isProper_of_isProjectiveMorphism _ hSB.isProjectiveMorphism_minus
  haveI : IsProper fp := hSB.isProper_plus
  haveI : IsProper p := isProper_of_isProjectiveMorphism _ hlift.isProjectiveMorphism
  have hpb := hlift.isBirationalMorphism
  have hfb := hSB.isBirationalMorphism_minus
  have hfpb := hSB.isBirationalMorphism_plus
  -- the models of the program
  have hpair : ∀ k ≤ m, IsProjectiveQFactorialDltPair (modelStr (p ≫ sX) P.sY k)
      (divisorSeq KU P.KY k) (divisorSeq Δ P.ΔY k) := fun k hk =>
    P.isProjectiveQFactorialDltPair k (hle k hk)
  have hst : ∀ k (hk : k < m), IsProjectiveElementaryDltStep (modelStr (p ≫ sX) P.sY k)
      (P.sV k) (P.sY k) (divisorSeq KU P.KY k) (divisorSeq Δ P.ΔY k) (P.R k) (P.f k) (P.fp k)
      (P.ΔY k) := fun k hk => P.isProjectiveElementaryDltStep k (hlt k hk)
  have hMn : ∀ k ≤ m, IsNormalVariety ℂ (modelStr (p ≫ sX) P.sY k) := fun k hk =>
    (hpair k hk).isQFactorial.1
  have hUn : IsNormalVariety ℂ (p ≫ sX) := hMn 0 m.zero_le
  -- the maps `h_k' : V_k ⟶ Z` of the steps
  have hVgen : ∀ k (hk : k < m), modelMap (p ≫ f) P.hY k ≫ sZ = modelStr (p ≫ sX) P.sY k →
      IsBirationalMorphism (modelMap (p ≫ f) P.hY k) →
      topologicalKrullDim (modelSeq U P.Y k) = 4 →
      P.hV k ≫ sZ = P.sV k ∧ IsBirationalMorphism (P.hV k) ∧ IsProper (P.hV k) := by
    intro k hk ihs ihb ihd
    have hSk := isFourfoldStepDiagram_of_isProjectiveElementaryDltStep (hst k hk) ihd
    have hfk := (hst k hk).isContractionOfRay
    have hcV := P.comp_hV k (hlt k hk)
    haveI : IsProper (P.f k) := isProper_of_isProjectiveMorphism _ hfk.isProjectiveMorphism
    haveI : IsIso (P.f k).c :=
      @NatIso.isIso_of_isIso_app _ _ _ _ _ _ (P.f k).c fun U => hfk.isIso_app U.unop
    have hVs : P.hV k ≫ sZ = P.sV k := by
      obtain ⟨_, _, hu⟩ := MMP.existsUnique_comp_eq_of_isIso_c (P.f k)
        (modelStr (p ≫ sX) P.sY k) fun x x' hxx => by
          rw [← hfk.comp_eq]; simp only [Scheme.Hom.comp_apply, hxx]
      exact (hu _ (show P.f k ≫ P.hV k ≫ sZ = _ by rw [← Category.assoc, hcV, ihs])).trans
        (hu _ hfk.comp_eq).symm
    haveI : IsIntegral (P.V k) := hSk.isNormalVariety_target.1.toIsIntegral
    haveI : LocallyOfFiniteType (P.sV k) := hSk.isNormalVariety_target.1.toLocallyOfFiniteType
    haveI : LocallyOfFiniteType (P.hV k ≫ sZ) := by rw [hVs]; infer_instance
    haveI : LocallyOfFiniteType (P.hV k) := locallyOfFiniteType_of_comp (P.hV k) sZ
    haveI : IsProper (P.sV k) :=
      isProper_of_isProjectiveMorphism _ hSk.isProjectiveVariety_target.isProjective
    refine ⟨hVs, Main.isBirationalMorphism_of_comp_left (P.f k) (P.hV k)
      (hst k hk).isBirationalMorphism (by rwa [hcV]),
      ProgramComparison.isProper_of_comp_eq _ hVs⟩
  -- `h_k ≫ s_Z = s_{U_k}`, `h_k` birational and `dim U_k = 4`
  have key : ∀ k ≤ m, modelMap (p ≫ f) P.hY k ≫ sZ = modelStr (p ≫ sX) P.sY k ∧
      IsBirationalMorphism (modelMap (p ≫ f) P.hY k) ∧
      topologicalKrullDim (modelSeq U P.Y k) = 4 := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨?_, CommonModel.isBirationalMorphism_comp hpb hfb, ?_⟩
      · change (p ≫ f) ≫ sZ = p ≫ sX
        rw [Category.assoc, hSB.comp_eq_minus]
      · haveI : MMP.Mori.IsVariety ℂ sX := hXn.1
        haveI : MMP.Mori.IsVariety ℂ (p ≫ sX) := hUn.1
        change topologicalKrullDim U = 4
        rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (p ≫ sX) hpb,
          hdim]
    | succ k ih =>
      intro hk
      obtain ⟨ihs, ihb, ihd⟩ := ih (by omega)
      have hSk := isFourfoldStepDiagram_of_isProjectiveElementaryDltStep (hst k hk) ihd
      obtain ⟨hVs, hVb, -⟩ := hVgen k hk ihs ihb ihd
      refine ⟨?_, ?_, hSk.dim_plus⟩
      · change P.hY k ≫ sZ = P.sY k
        rw [P.hY_eq k (hlt k hk), Category.assoc, hVs, (hst k hk).comp_eq]
      · change IsBirationalMorphism (P.hY k)
        rw [P.hY_eq k (hlt k hk)]
        exact CommonModel.isBirationalMorphism_comp hSk.isBirationalMorphism_plus hVb
  have hSD : ∀ k (hk : k < m), IsFourfoldStepDiagram (modelStr (p ≫ sX) P.sY k) (P.sV k)
      (P.sY k) (divisorSeq KU P.KY k) (divisorSeq Δ P.ΔY k) (P.f k) (P.fp k) := fun k hk =>
    isFourfoldStepDiagram_of_isProjectiveElementaryDltStep (hst k hk) (key k hk.le).2.2
  have hVf : ∀ k (hk : k < m), P.hV k ≫ sZ = P.sV k ∧ IsBirationalMorphism (P.hV k) ∧
      IsProper (P.hV k) := fun k hk =>
    hVgen k hk (key k hk.le).1 (key k hk.le).2.1 (key k hk.le).2.2
  -- canonical divisors: `K₀` on `U` with `p_* K₀ = K`, transported along the program
  have hK4 : K.IsCanonicalDivisor sX 4 := by
    obtain ⟨n, hn⟩ := hstep.isCanonicalDivisor
    obtain rfl := index_eq_of_isCanonicalDivisor hn hdim
    exact hn
  have hKP4 : ∀ k ≤ m,
      Divisor.IsCanonicalDivisor (modelStr (p ≫ sX) P.sY k) 4 (divisorSeq KU P.KY k) := by
    intro k hk
    obtain ⟨n, hn⟩ := (hpair k hk).isCanonicalDivisor
    obtain rfl := index_eq_of_isCanonicalDivisor hn (key k hk).2.2
    exact hn
  haveI : LocallyOfFiniteType (p ≫ sX) := hUn.1.toLocallyOfFiniteType
  haveI := hpb.isDominant
  obtain ⟨K₀, hK₀c, hK₀p⟩ := Main.exists_isCanonicalDivisor_transformDivisor_eq hXn hUn hpb hK4
    (hKP4 0 m.zero_le)
  set KA := transportedDivisor P.toElementaryDltProgram K₀
  have hVn : ∀ k (hk : k < m), IsNormalVariety ℂ (P.sV k) := fun k hk =>
    (hSD k hk).isNormalVariety_target
  have hfkp : ∀ k (hk : k < m), IsProper (P.f k) := fun k hk =>
    isProper_of_isProjectiveMorphism _ (hSD k hk).isProjectiveMorphism_minus
  have hflipc : ∀ k (hk : k < m) {L : Divisor (modelSeq U P.Y k)},
      L.IsCanonicalDivisor (modelStr (p ≫ sX) P.sY k) 4 →
      Divisor.IsCanonicalDivisor (P.sY k) 4 (flipTransform (P.f k) (P.fp k) L) := by
    intro k hk L hL
    haveI := hfkp k hk
    exact isCanonicalDivisor_flipTransform (hMn k hk.le) (hVn k hk)
      (hSD k hk).isBirationalMorphism_minus (hSD k hk).comp_eq_minus
      (hSD k hk).isSmallMorphism_plus hL (hKP4 (k + 1) hk)
  have hKAc : ∀ k ≤ m, Divisor.IsCanonicalDivisor (modelStr (p ≫ sX) P.sY k) 4 (KA k) := by
    intro k
    induction k with
    | zero => intro _; exact hK₀c
    | succ k ih => intro hk; exact hflipc k hk (ih (by omega))
  have hlinA : ∀ k ≤ m, Divisor.LinearlyEquivalent (divisorSeq KU P.KY k) (KA k) := fun k hk =>
    MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor _ (hMn k hk) (hKP4 k hk)
      (hKAc k hk)
  have hSDA : ∀ k (hk : k < m), IsFourfoldStepDiagram (modelStr (p ≫ sX) P.sY k) (P.sV k)
      (P.sY k) (KA k) (divisorSeq Δ P.ΔY k) (P.f k) (P.fp k) := fun k hk =>
    isFourfoldStepDiagram_of_linearlyEquivalent (hSD k hk) ⟨4, hKAc k hk.le⟩ (hlinA k hk.le)
      (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor _ (hMn (k + 1) hk)
        (hflipc k hk (hKP4 k hk.le)) (hKAc (k + 1) hk))
  -- a smooth projective `W` dominating every `U_k`, `X` and `X⁺`
  let Xs : Option (Option (Fin (m + 1))) → Scheme.{0} := fun o =>
    o.elim X' fun o' => o'.elim X fun k => modelSeq U P.Y k
  let fs : ∀ o, Xs o ⟶ Z := fun o => match o with
    | none => fp
    | some none => f
    | some (some k) => modelMap (p ≫ f) P.hY k
  have hMp : ∀ k ≤ m, IsProper (modelMap (p ≫ f) P.hY k) := fun k hk =>
    isProper_of_isProjectiveMorphism _ (P.isProjectiveMorphism k (hle k hk))
  haveI : ∀ o, IsProper (fs o) := fun o => match o with
    | none => (inferInstance : IsProper fp)
    | some none => (inferInstance : IsProper f)
    | some (some k) => hMp k (Nat.lt_succ_iff.mp k.2)
  haveI : AlgebraicGeometry.IsVariety ℂ sZ := hZn.1
  obtain ⟨W, w, hWn, hwb, gW, hWs, -, hgW, -, hWp⟩ :=
    CommonModel.exists_smooth_projective_model (k := ℂ) sZ fs
      (fun o => match o with
        | none => hfpb
        | some none => hfb
        | some (some k) => (key k (Nat.lt_succ_iff.mp k.2)).2.1)
      (fun o => match o with
        | none => by
          change IsNormalVariety ℂ (fp ≫ sZ); rwa [hSB.comp_eq_plus]
        | some none => by
          change IsNormalVariety ℂ (f ≫ sZ); rwa [hSB.comp_eq_minus]
        | some (some k) => by
          change IsNormalVariety ℂ (modelMap (p ≫ f) P.hY k ≫ sZ)
          rw [(key k (Nat.lt_succ_iff.mp k.2)).1]
          exact hMn k (Nat.lt_succ_iff.mp k.2))
      (κ := Empty) (fun j => j.elim) (fun j => j.elim)
  haveI : IsIntegral W := hWn.1.toIsIntegral
  haveI : IsNormal W := hWn.2
  haveI : LocallyOfFiniteType (w ≫ sZ) := hWn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (w ≫ sZ)
  haveI : QuasiCompact (w ≫ sZ) := hWn.1.toQuasiCompact
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (w ≫ sZ)
  have hWp' : MMP.Mori.IsProjectiveVariety ℂ (w ≫ sZ) := hWp hZp
  haveI := hwb.isDominant
  let q : ∀ k, k ≤ m → (W ⟶ modelSeq U P.Y k) := fun k hk =>
    gW (some (some ⟨k, Nat.lt_succ_of_le hk⟩))
  let qX : W ⟶ X := gW (some none)
  let qX' : W ⟶ X' := gW none
  have hq : ∀ k (hk : k ≤ m), q k hk ≫ modelMap (p ≫ f) P.hY k = w := fun k hk =>
    (hgW (some (some ⟨k, Nat.lt_succ_of_le hk⟩))).1
  have hqb : ∀ k (hk : k ≤ m), IsBirationalMorphism (q k hk) := fun k hk =>
    (hgW (some (some ⟨k, Nat.lt_succ_of_le hk⟩))).2.2
  have hqX : qX ≫ f = w := (hgW (some none)).1
  have hqXb : IsBirationalMorphism qX := (hgW (some none)).2.2
  have hqX' : qX' ≫ fp = w := (hgW none).1
  have hqX'b : IsBirationalMorphism qX' := (hgW none).2.2
  have hqs : ∀ k (hk : k ≤ m), q k hk ≫ modelStr (p ≫ sX) P.sY k = w ≫ sZ := fun k hk => by
    rw [← (key k hk).1, ← Category.assoc, hq k hk]
  have hqXs : qX ≫ sX = w ≫ sZ := by rw [← hSB.comp_eq_minus, ← Category.assoc, hqX]
  have hqX's : qX' ≫ sX' = w ≫ sZ := by rw [← hSB.comp_eq_plus, ← Category.assoc, hqX']
  -- compatibility of the morphisms out of `W`
  have hcomp : ∀ k (hk : k < m), q k hk.le ≫ P.f k = q (k + 1) hk ≫ P.fp k := by
    intro k hk
    obtain ⟨-, hVb, hVp⟩ := hVf k hk
    haveI := hVp
    haveI : IsIntegral (P.V k) := (hVn k hk).1.toIsIntegral
    have e1 : (q k hk.le ≫ P.f k) ≫ P.hV k = w := by
      rw [Category.assoc, P.comp_hV k (hlt k hk)]; exact hq k hk.le
    have e2 : (q (k + 1) hk ≫ P.fp k) ≫ P.hV k = w := (Category.assoc _ _ _).trans
      ((congrArg (q (k + 1) hk ≫ ·) (P.hY_eq k (hlt k hk)).symm).trans (hq (k + 1) hk))
    haveI : IsDominant ((q k hk.le ≫ P.f k) ≫ P.hV k) := by rw [e1]; infer_instance
    exact Main.eq_of_comp_eq hVb (e1.trans e2.symm)
  have hcompX : q 0 m.zero_le ≫ p = qX := by
    have e1 : (q 0 m.zero_le ≫ p) ≫ f = w := (Category.assoc _ _ _).trans (hq 0 m.zero_le)
    haveI : IsDominant ((q 0 m.zero_le ≫ p) ≫ f) := by rw [e1]; infer_instance
    exact Main.eq_of_comp_eq hfb (e1.trans hqX.symm)
  -- the comparison along the program: `A = q_0^*(K_0 + Δ) ≥ q_m^*(K_m + Δ_m)`
  have hQM : ∀ k ≤ m, ∀ D : QDivisor (modelSeq U P.Y k), D.IsQCartier := fun k hk D =>
    isQCartier_of_isQFactorial _ (hpair k hk).isQFactorial D
  have hgen : ∀ k (hk : k ≤ m), ∀ T : irreducibleComponents W, q k hk (componentGenericPoint W T) ∉
      (Divisor.toQDivisor (KA k) + divisorSeq Δ P.ΔY k).supp := fun k hk => by
    haveI := (hqb k hk).isDominant
    exact MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' _ _
  have hΘ : ∀ k < m, divisorSeq Δ P.ΔY (k + 1) =
      flipTransform (P.f k) (P.fp k) (divisorSeq Δ P.ΔY k) := fun k hk =>
    (hst k hk).eq_flipTransform
  have hKAe : ∀ k < m, KA (k + 1) = flipTransform (P.f k) (P.fp k) (KA k) := fun k _ => rfl
  have hF₁ : ∀ j (hj : j ≤ m), 0 ≤
      (Divisor.toQDivisor (KA 0) + divisorSeq Δ P.ΔY 0).pullback (hQM 0 m.zero_le _)
        (hgen 0 m.zero_le) -
      (Divisor.toQDivisor (KA j) + divisorSeq Δ P.ΔY j).pullback (hQM j hj _) (hgen j hj) := by
    intro j
    induction j with
    | zero => intro _; exact (sub_self _).symm.le
    | succ j ih =>
      intro hj
      have h := add_nonneg (ih (by omega)) (ProgramComparison.pullback_sub_pullback_succ_nonneg
        (modelStr (p ≫ sX) P.sY) KA (divisorSeq Δ P.ΔY) P.sV P.f P.fp j (hSDA j hj) rfl
        (hΘ j hj) (w ≫ sZ) hWp' hWn (q j (Nat.le_of_succ_le hj)) (q (j + 1) hj)
        (hqs j (Nat.le_of_succ_le hj)) (hqs (j + 1) hj) (hqb j (Nat.le_of_succ_le hj))
        (hqb (j + 1) hj) (hcomp j hj) (hQM j (Nat.le_of_succ_le hj) _) (hQM (j + 1) hj _)
        (hgen j (Nat.le_of_succ_le hj)) (hgen (j + 1) hj))
      rwa [sub_add_sub_cancel] at h
  have hF₁₀ := StepChain.transformDivisor_pullback_sub_pullback_eq_zero m (modelStr (p ≫ sX) P.sY)
    KA (divisorSeq Δ P.ΔY) P.sV P.f P.fp hSDA hKAe hΘ q hqb hcomp (hQM 0 m.zero_le _)
    (hQM m le_rfl _) (hgen 0 m.zero_le) (hgen m le_rfl)
  -- the comparison along the permitted step: `q_X^*(K + B) ≥ q_{X⁺}^*(K⁺ + B⁺)`
  have hQKB : (Divisor.toQDivisor K + B).IsQCartier := hSB.isQCartier_minus
  have hX0 : ∀ T : irreducibleComponents W, qX (componentGenericPoint W T) ∉
      (Divisor.toQDivisor K + B).supp := by
    haveI := hqXb.isDominant
    exact MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' _ _
  have hX1 : ∀ T : irreducibleComponents W, qX' (componentGenericPoint W T) ∉
      (Divisor.toQDivisor (flipTransform f fp K) + flipTransform f fp B).supp := by
    haveI := hqX'b.isDominant
    exact MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' _ _
  obtain ⟨hF₂, hF₂₀⟩ := pullback_sub_pullback_of_isFourfoldStepDiagram hSB hWp' hWn hqXs hqX's
    hqXb hqX'b (hqX.trans hqX'.symm) hX0 hX1
  -- crepancy of `p`: `K₀ + Δ = p^*(K + B)`, so `q_0^*(K₀ + Δ) = q_X^*(K + B)`
  obtain ⟨n₀, hcb⟩ := hlift.isCrepantBoundary
  have hn₀ : n₀ = 4 := by
    obtain ⟨y, hy⟩ := exists_coheight_eq_one (p ≫ sX) (r := 3)
      (by rw [show topologicalKrullDim U = 4 from (key 0 m.zero_le).2.2]; rfl)
    obtain ⟨-, hKn, -⟩ := hcb (PrimeDivisor.ofCoheightOne y hy)
    exact index_eq_of_isCanonicalDivisor hKn hdim
  subst hn₀
  obtain ⟨-, -, hB0, hpullU⟩ := hlift.isLogCanonicalPair.1.isPullback_of_isCrepantBoundary p hUn
    hpb hK4 hK₀c (Or.inr ⟨inferInstance, hK₀p⟩) hcb
  set A := (Divisor.toQDivisor (KA 0) + divisorSeq Δ P.ΔY 0).pullback (hQM 0 m.zero_le _)
    (hgen 0 m.zero_le)
  have hApb := QDivisor.isPullback_pullback (hQM 0 m.zero_le _) (hgen 0 m.zero_le)
  let q0 : W ⟶ U := q 0 m.zero_le
  have hq0X : q0 ≫ p = qX := hcompX
  haveI : IsDominant (q0 ≫ p) := by rw [hq0X]; exact hqXb.isDominant
  obtain ⟨hM', hcompPB⟩ := TwoEnds.qDivisor_isPullback_comp p q0 hpullU hApb
  have hAeq : A = (Divisor.toQDivisor K + B).pullback hQKB hX0 :=
    (hQKB.existsUnique_isPullback hX0).unique (isPullback_of_eq hq0X hcompPB)
      (QDivisor.isPullback_pullback hQKB hX0)
  -- the two ends
  haveI : QuasiCompact (modelStr (p ≫ sX) P.sY m) := (hMn m le_rfl).1.toQuasiCompact
  have hDm := hQM m le_rfl (Divisor.toQDivisor (KA m) + divisorSeq Δ P.ΔY m)
  have hnef' := isRelativelyNef_add_of_linearlyEquivalent hnef (hlinA m le_rfl)
  have hπmp : IsProjectiveMorphism (modelMap (p ≫ f) P.hY m) :=
    P.isProjectiveMorphism m (hle m le_rfl)
  have hA₁ := QDivisor.isPullback_pullback hDm (hgen m le_rfl)
  have hA₂ := QDivisor.isPullback_pullback hSB.isQCartier_plus hX1
  obtain ⟨h, hqh, hhπ, hD, hpull⟩ :=
    exists_comp_eq_and_isPullback_of_add_eq_add_of_hasRelativelyAmpleMultiple ℂ sZ
      (modelStr (p ≫ sX) P.sY m) sX' hZn hZp (hMn m le_rfl) (hpair m le_rfl).isProjectiveVariety
      hX'n hSB.isProjectiveVariety_plus (modelMap (p ≫ f) P.hY m) fp hπmp
      hSB.isProjectiveMorphism_plus (key m le_rfl).1 hSB.comp_eq_plus hDm hSB.isQCartier_plus
      hnef' hSB.hasRelativelyAmpleMultiple_plus (q m le_rfl) qX'
      (by rwa [hqs m le_rfl]) (by rwa [hqs m le_rfl]) (hqb m le_rfl) hqX'b
      ((hqs m le_rfl).trans hqX's.symm) ((hq m le_rfl).trans hqX'.symm) (hgen m le_rfl) hX1
      hA₁ hA₂ (hF₁ m le_rfl) hF₂ hF₁₀ hF₂₀ (by rw [hAeq]; abel)
  -- `p' = h`
  haveI : IsSeparated (modelStr (p ≫ sX) P.sY m) := (hMn m le_rfl).1.toIsSeparated
  have hhs : h ≫ sX' = modelStr (p ≫ sX) P.sY m := by
    rw [← hSB.comp_eq_plus, ← Category.assoc, hhπ, (key m le_rfl).1]
  haveI : LocallyOfFiniteType (modelStr (p ≫ sX) P.sY m) := (hMn m le_rfl).1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (h ≫ sX') := by rw [hhs]; infer_instance
  haveI : LocallyOfFiniteType h := locallyOfFiniteType_of_comp h sX'
  haveI : IsSeparated (h ≫ sX') := by rw [hhs]; infer_instance
  haveI : IsSeparated h := IsSeparated.of_comp h sX'
  have hhb : IsBirationalMorphism h :=
    Main.isBirationalMorphism_of_comp_left (q m le_rfl) h (hqb m le_rfl) (hqh ▸ hqX'b)
  have hhproj : IsProjectiveMorphism h := IsProjectiveMorphism.of_comp h sX'
    (by rw [hhs]; exact (hpair m le_rfl).isProjectiveVariety.isProjective)
  haveI : IsProper h := isProper_of_isProjectiveMorphism _ hhproj
  have hY' : IsNormalVariety ℂ (h ≫ sX') := by rw [hhs]; exact hMn m le_rfl
  -- `p'_* K_m = K⁺`: both sides are read off one prime divisor of `W`
  have hKh : RationalMap.transformDivisor h.toRationalMap (KA m) = flipTransform f fp K := by
    haveI := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hX'n
    haveI := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hXn
    have hWnr : IsNormalVariety ℂ (qX' ≫ sX') := by rwa [hqX's]
    haveI : IsProper (w ≫ sZ) := isProper_of_isProjectiveMorphism _ hWp'.isProjective
    haveI : IsProper qX' := ProgramComparison.isProper_of_comp_eq qX' hqX's
    refine Finsupp.ext fun Q => ?_
    obtain ⟨E, hE, -, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hX'n hWnr hqX'b Q
    have hx : h (q m le_rfl E.genericPoint) = Q.genericPoint := by
      rw [← Scheme.Hom.comp_apply, hqh, hE]
    obtain ⟨Pm, hPm, -⟩ := BridgeComparison.exists_primeDivisor_of_map_eq_genericPoint hhb hx
    rw [transformDivisor_apply_of_map_genericPoint hhb
      (show h Pm.genericPoint = Q.genericPoint by rwa [hPm])]
    obtain ⟨P₀, hP₀, hBA⟩ := StepChain.exists_primeDivisor_zero_forall_coeff_eq hSDA hcomp
      E.genericPoint m le_rfl Pm hPm.symm
    obtain ⟨P₀', hP₀', hBB⟩ := StepChain.exists_eq_genericPoint_flipTransform_apply hSB Q
      (qX E.genericPoint) (by rw [← Scheme.Hom.comp_apply, hqX, ← hqX', Scheme.Hom.comp_apply, hE])
    have h0 : (q0 ≫ p) E.genericPoint = P₀'.genericPoint := by rwa [hq0X]
    have hpP : p P₀.genericPoint = P₀'.genericPoint :=
      (congrArg p hP₀).symm.trans ((Scheme.Hom.comp_apply q0 p E.genericPoint).symm.trans h0)
    have e3 := transformDivisor_apply_of_map_genericPoint hpb hpP K₀
    rw [hK₀p] at e3
    rw [hBA KA hKAe]
    exact e3.symm.trans (hBB K).symm
  -- `K⁺` is a canonical divisor of `X⁺`
  have hK'4 : Divisor.IsCanonicalDivisor sX' 4 (flipTransform f fp K) := by
    obtain ⟨-, n', K'', hK'', -⟩ := hstep.isLogCanonicalPair_step.1
    obtain rfl := index_eq_of_isCanonicalDivisor hK'' hSB.dim_plus
    exact isCanonicalDivisor_flipTransform hXn hZn hfb hSB.comp_eq_minus hSB.isSmallMorphism_plus
      hK4 hK''
  refine ⟨h, hhs, hhπ, hhproj, hY', hhb, 4, ?_⟩
  exact MMP.Threefold.Mori.isCrepantBoundary_of_add_eq_pullback ⟨hX'n, hK'4, hSB.isQCartier_plus⟩
    h hY' hhb (by rw [hhs]; exact hKAc m le_rfl) hKh ⟨hD, hpull⟩

end MMP.Fourfold
