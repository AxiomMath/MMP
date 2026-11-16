module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksFormula
public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksNormalizationThom
public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksSectionPullback
public import MMP.AlgebraicGeometry.Chow.CycleClassPushforward
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardUncontained
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward.ComponentDegree
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.CurveDeltaDimension
public import MMP.AlgebraicGeometry.SubschemeOver
public import StacksFrontier.AlgebraicGeometry.NormalizationBirational.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import MMP.AlgebraicGeometry.Morphisms.Birational.ResidueDegree
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.Finite
public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksNormalizationGeneric

/-!
# Fulton's Lemma 19.1.3 on Stacks cycles: reduction to the normal case

Let `X` be a complex variety of dimension `k + 1`, `ℒ` an invertible `𝒪_X`-module and
`s ∈ Γ(X, ℒ)` a non-zero global section, with section `σ_s : X ⟶ 𝐕(ℒ^∨)` and zero scheme
`D = Z(s)`. Fulton's Lemma 19.1.3 states `σ_s^*(u) ∩ cl(X) = cl_D([D]_k)` in `H_{2k} D`
(`MMP.Modules.LocalizedFirstChernFormula`). For `X` normal this is
`MMP.Modules.LocalizedFirstChernFormula.of_isNormal`; here it is proved for every `X` by passing to
the normalization `ν : X̃ → X` (Fulton, §19.1, proof of Lemma 19.1.3).

For a proper surjective `ν : X' → X` of degree one and a section `σ` of `𝐕(ℰ)`, let
`σ' = ν^*σ` be the pulled-back section of `𝐕(ν^*ℰ)`, `D' = Z(σ') = ν⁻¹(D)` and `ν_D : D' → D`
the restriction of `ν`. The bundle map `𝐕(ν^*ℰ) ⟶ 𝐕(ℰ)` is a linear isomorphism on fibres, so
the localized top Chern class is natural (`MMP.Modules.pushforward_localizedTopChernCap_of_comp`):
`ν_{D*}(σ'^* u ∩ cl(X')) = σ^* u ∩ ν_* cl(X') = σ^* u ∩ cl(X)`. On the other side,
`ν_{D*} cl_{D'}([D']_k) = cl_D(ν_{D*}[D']_k)`, and `ν_{D*}[D']_k = [D]_k` for zero schemes of
sections of invertible modules (Stacks Tag 02ST). So the formula on `X'` gives it on `X`.

## Main definitions and results

* `MMP.Modules.isFibrewiseIso_baseChangeMap`: `𝐕(f^*ℰ) ⟶ 𝐕(ℰ)` is a fibrewise isomorphism.
* `MMP.Modules.zeroLocusSubschemeMap`: the restriction `Z(f^*σ) ⟶ Z(σ)` of `f`.
* `MMP.Modules.properPushforward_zeroLocusSubschemeMap_globalSectionMap`: `ν_{D*}[D']_k = [D]_k`.
* `MMP.Modules.LocalizedFirstChernFormula.of_proper_birational`: descent of the formula.
* `MMP.Modules.localizedFirstChernFormula`: **Fulton's Lemma 19.1.3** for `dim X = k + 1`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, proof of Lemma 19.1.3.
* [Stacks Project, Tag 02ST](https://stacks.math.columbia.edu/tag/02ST)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set Stacks.Chow
open MMP.UnderlyingSpace
open scoped MMP.SubschemeOver

attribute [local instance] AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback

namespace MMP.Modules

open MMP AlgebraicGeometry.SheafOfModules

section ZeroScheme

variable {X X' : Scheme.{0}} (f : X' ⟶ X) {E : X.Modules} [E.IsQuasicoherent]
  {σ : X ⟶ totalSpace E} (hσ : σ ≫ proj E = 𝟙 X)

/-- The zero scheme `Z(σ)` is contained in the image under `f` of the zero scheme `Z(f^*σ)`. -/
lemma le_map_zeroLocus_pullbackSectionMap :
    zeroLocus E σ ≤ (zeroLocus _ (pullbackSectionMap f hσ)).map f := by
  rw [zeroLocus_pullbackSectionMap]
  exact Scheme.IdealSheafData.le_map_comap _ _

/-- **The restriction `f_D : Z(f^*σ) ⟶ Z(σ)` of `f` to the zero schemes.** -/
def zeroLocusSubschemeMap :
    (zeroLocus _ (pullbackSectionMap f hσ)).subscheme ⟶ (zeroLocus E σ).subscheme :=
  Scheme.IdealSheafData.subschemeMap _ _ f (le_map_zeroLocus_pullbackSectionMap f hσ)

/-- The restriction `f_D` followed by `Z(σ) ⟶ X` is `Z(f^*σ) ⟶ X'` followed by `f`. -/
@[reassoc (attr := simp)]
lemma zeroLocusSubschemeMap_subschemeι :
    zeroLocusSubschemeMap f hσ ≫ (zeroLocus E σ).subschemeι =
      (zeroLocus _ (pullbackSectionMap f hσ)).subschemeι ≫ f :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- If `f` is proper, so is its restriction `f_D : Z(f^*σ) ⟶ Z(σ)`. -/
instance isProper_zeroLocusSubschemeMap [IsProper f] : IsProper (zeroLocusSubschemeMap f hσ) := by
  have : IsProper (zeroLocusSubschemeMap f hσ ≫ (zeroLocus E σ).subschemeι) := by
    rw [zeroLocusSubschemeMap_subschemeι]
    infer_instance
  exact IsProper.of_comp _ (zeroLocus E σ).subschemeι

/-- If `f` is a morphism over `S`, so is its restriction `f_D : Z(f^*σ) ⟶ Z(σ)`. -/
instance isOver_zeroLocusSubschemeMap {S : Scheme.{0}} [X.Over S] [X'.Over S] [f.IsOver S] :
    (zeroLocusSubschemeMap f hσ).IsOver S :=
  ⟨by
    change zeroLocusSubschemeMap f hσ ≫ (zeroLocus E σ).subschemeι ≫ X ↘ S =
      (zeroLocus _ (pullbackSectionMap f hσ)).subschemeι ≫ X' ↘ S
    rw [zeroLocusSubschemeMap_subschemeι_assoc, comp_over]⟩

variable [X.Over (Spec (.of ℂ))] [X'.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))]
  [σ.IsOver (Spec (.of ℂ))] {r : ℕ} [IsFiniteLocallyFreeOfRank.{0, 0, 0} E r]

/-- On complex points, `f_D` followed by `Z(σ)(ℂ) ≅ σ⁻¹(0(X(ℂ)))` is
`Z(f^*σ)(ℂ) ≅ (f^*σ)⁻¹(0(X'(ℂ)))` followed by the restriction of `f`. -/
theorem map_zeroLocusSubschemeMap_comp_zeroLocusHom :
    TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (zeroLocusSubschemeMap f hσ)) ≫ zeroLocusHom σ =
      zeroLocusHom (pullbackSectionMap f hσ) ≫
        zeroLocusMap σ (pullbackSectionMap f hσ) (baseChangeMap_proj f E)
          (isFibrewiseIso_baseChangeMap f E r) (pullbackSectionMap_baseChangeMap f hσ) := by
  refine ConcreteCategory.hom_ext _ _ fun p ↦ Subtype.ext ?_
  change UnderlyingSpace.map (K := ℂ) (zeroLocus E σ).subschemeι
      (UnderlyingSpace.map (K := ℂ) (zeroLocusSubschemeMap f hσ) p) =
    mapFun f (UnderlyingSpace.map (K := ℂ) (zeroLocus _ (pullbackSectionMap f hσ)).subschemeι p)
  refine UnderlyingSpace.ext ?_
  simp only [toHom_map, toHom_mapFun, Category.assoc, zeroLocusSubschemeMap_subschemeι]

end ZeroScheme

/-- The section `σ_s : X ⟶ 𝐕(ℒ^∨)` of a global section is a morphism over `ℂ`. -/
instance isOver_globalSectionMap {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] (L : X.Modules)
    [(Scheme.Modules.dual L).IsQuasicoherent] (s : Γ(L, ⊤)) :
    (globalSectionMap L s).IsOver (Spec (.of ℂ)) :=
  ⟨by
    change globalSectionMap L s ≫ proj (Scheme.Modules.dual L) ≫ X ↘ Spec (.of ℂ) =
      X ↘ Spec (.of ℂ)
    rw [globalSectionMap_proj_assoc]⟩

section Cycle

/-- Proper push-forward of cycles depends only on the morphism. -/
private lemma properPushforward_congr_hom (C : ChowSituation.{0}) {A B : Scheme.{0}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    {f f' : A ⟶ B} [IsProper f] [IsProper f'] (h : f = f') (hf : f ≫ sB = sA) (k : ℤ)
    (c : CycleGroup C sA k) :
    properPushforward C sA sB f hf k c = properPushforward C sA sB f' (h ▸ hf) k c := by
  subst h
  rfl

/-- Push-forward along a closed immersion `i : Z ⟶ Y` sends the cycle `[Z]_k` of `Z` to the cycle
`[Z ⊆ Y]_k`. -/
lemma properPushforward_cycleAssociatedToClosedSubscheme_id {Z Y : Scheme.{0}}
    (C : ChowSituation.{0}) (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (i : Z ⟶ Y) [IsClosedImmersion i] (hi : i ≫ sY = sZ) (k : ℤ) :
    properPushforward C sZ sY i hi k (cycleAssociatedToClosedSubscheme C sZ (𝟙 Z) k) =
      cycleAssociatedToClosedSubscheme C sY i k := by
  have h := properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp C sZ sY
    i hi (𝟙 Z) k
  simpa only [Category.id_comp] using h

variable {X X' : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X] [IsIntegral X]
  [X'.Over (Spec (.of ℂ))] [IsComplexScheme X'] [IsIntegral X']
  (ν : X' ⟶ X) [ν.IsOver (Spec (.of ℂ))] [IsProper ν]

/-- **`ν_{D*}[D']_k = [D]_k`** (Stacks Tag 02ST, for degree one). Let `ν : X' → X` be a proper
surjective morphism of complex varieties of dimension `k + 1` with residue degree one at the
generic point, `ℒ` invertible on `X` and `s ≠ 0` a global section. With `D = Z(σ_s)` and
`D' = Z(ν^*σ_s) = ν⁻¹(D)`, the restriction `ν_D : D' → D` pushes `[D']_k` to `[D]_k`. -/
theorem properPushforward_zeroLocusSubschemeMap_globalSectionMap {k : ℕ}
    (hn : ((k + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim X)
    (hn' : ((k + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim X') (hν : Function.Surjective ν)
    (hdeg : ν.residueDegree (genericPoint X') = 1) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] [IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (hs : s ≠ 0) :
    properPushforward (fieldChowSituation ℂ) (_ ↘ Spec (.of ℂ)) (_ ↘ Spec (.of ℂ))
        (zeroLocusSubschemeMap ν (globalSectionMap_proj L s)) (comp_over _ _) k
        (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ) (_ ↘ Spec (.of ℂ)) (𝟙 _) k) =
      cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
        ((zeroLocus _ (globalSectionMap L s)).subscheme ↘ Spec (.of ℂ)) (𝟙 _) k := by
  have : IsDominant ν := ⟨hν.denseRange⟩
  have hσ := globalSectionMap_proj L s
  have hD : zeroLocus _ (globalSectionMap L s) = Stacks.Divisors.zeroScheme X L s :=
    zeroLocus_globalSectionMap L s
  have hD' : zeroLocus _ (pullbackSectionMap ν hσ) =
      Stacks.Divisors.zeroScheme X' ((Scheme.Modules.pullback ν).obj L)
        (pullbackGlobalSections ν L s) := by
    rw [zeroLocus_pullbackSectionMap, hD, Stacks.Divisors.zeroScheme_pullback]
  have hX := schemeDeltaDimension_fieldChowSituation_eq_of_topologicalKrullDim_eq
    (X ↘ Spec (.of ℂ)) hn.symm
  have hX' := schemeDeltaDimension_fieldChowSituation_eq_of_topologicalKrullDim_eq
    (X' ↘ Spec (.of ℂ)) hn'.symm
  have key := properPushforward_cycleAssociatedToZeroScheme (fieldChowSituation ℂ) _ _ hX hX' ν
    (comp_over ν _) L s hs
  rw [finrank_functionField_eq_residueDegree ν, hdeg, Nat.cast_one, one_smul,
    show ((k + 1 : ℕ) : ℤ) - 1 = k by push_cast; ring] at key
  apply properPushforward_injective_of_isClosedImmersion (fieldChowSituation ℂ) _
    (X ↘ Spec (.of ℂ)) (zeroLocus _ (globalSectionMap L s)).subschemeι (comp_over _ _) k
  rw [properPushforward_properPushforward,
    properPushforward_congr_hom _ _ _ (zeroLocusSubschemeMap_subschemeι ν hσ),
    ← properPushforward_properPushforward _ _ (X' ↘ Spec (.of ℂ)) _ _ ν (comp_over _ _)
      (comp_over _ _),
    properPushforward_cycleAssociatedToClosedSubscheme_id,
    properPushforward_cycleAssociatedToClosedSubscheme_id, hD, hD']
  exact key

end Cycle

/-- `j = j'` transports commute with push-forward. -/
private lemma pushforward_congrDegree (R : Type) [CommRing R] {Y Z : TopCat.{0}} (g : Y ⟶ Z)
    (hg : IsProperMap g) {j j' : ℤ} (h : j = j')
    (x : borelMooreHomology R (ModuleCat.of R R) Y j) :
    (borelMooreHomology.pushforward R (ModuleCat.of R R) g hg j').hom
        (BorelMooreCross.congrDegree R Y h x) =
      BorelMooreCross.congrDegree R Z h
        ((borelMooreHomology.pushforward R (ModuleCat.of R R) g hg j).hom x) := by
  subst h
  rfl

variable (R : Type) [CommRing R] {X X' : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X]
  [X'.Over (Spec (.of ℂ))] [IsComplexScheme X']

/-- **Reduction of Fulton's Lemma 19.1.3 along a proper morphism of degree one** (Fulton, §19.1,
proof of Lemma 19.1.3). Let `ν : X' → X` be a proper surjective morphism of complex varieties of
dimension `k + 1` with residue degree one at the generic point, `ℰ` locally free of rank one on
`X` and `σ` a section of `𝐕(ℰ)`, with zero schemes `D = Z(σ)`, `D' = Z(ν^*σ)`. If
`ν_{D*}[D']_k = [D]_k`, the formula for `ν^*σ` on `X'` implies the formula for `σ` on `X`. -/
theorem LocalizedFirstChernFormula.of_proper_birational [IsIntegral X] [IsIntegral X'] {k : ℕ}
    {hn : ((k + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim X}
    (hn' : ((k + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim X')
    {E : X.Modules} [E.IsQuasicoherent] [IsFiniteLocallyFreeOfRank.{0, 0, 0} E 1]
    {σ : X ⟶ totalSpace E} [σ.IsOver (Spec (.of ℂ))] (hσ : σ ≫ proj E = 𝟙 X)
    (ν : X' ⟶ X) [ν.IsOver (Spec (.of ℂ))] [IsProper ν] (hν : Function.Surjective ν)
    (hdeg : ν.residueDegree (genericPoint X') = 1)
    (hcyc : properPushforward (fieldChowSituation ℂ) (_ ↘ Spec (.of ℂ)) (_ ↘ Spec (.of ℂ))
        (zeroLocusSubschemeMap ν hσ) (comp_over _ _) k
        (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ) (_ ↘ Spec (.of ℂ)) (𝟙 _) k) =
      cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
        ((zeroLocus E σ).subscheme ↘ Spec (.of ℂ)) (𝟙 _) k)
    (h : LocalizedFirstChernFormula R hn' ((Scheme.Modules.pullback ν).obj E)
      (pullbackSectionMap ν hσ)) :
    LocalizedFirstChernFormula R hn E σ := by
  intro μ hμ
  obtain ⟨μ', hμ', -, -⟩ := existsUnique_isVarietyFundamentalClass R hn'
  have h' := h μ' hμ'
  have hpush : (borelMooreHomology.pushforward R (ModuleCat.of R R)
      (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) ν)) (isProperMap_map (K := ℂ) ν)
      (2 * (k + 1) : ℕ)).hom μ' = μ := by
    have := IsVarietyFundamentalClass.pushforward_eq_residueDegree_smul ν hν hn hμ' hμ
    rw [hdeg, Nat.cast_one, one_smul] at this
    exact this
  have hF := isFibrewiseIso_baseChangeMap ν E 1
  have hπ := baseChangeMap_proj ν E
  have hσσ := pullbackSectionMap_baseChangeMap ν hσ
  rw [← hcyc, Chow.cycleClass_properPushforward, borelMooreHomology.pushforward_pushforward_eq_comp,
    borelMooreHomology.pushforward_apply_eq_of_hom_eq R (ModuleCat.of R R)
      (map_zeroLocusSubschemeMap_comp_zeroLocusHom ν hσ (r := 1)) _
      ((isProperMap_zeroLocusMap σ _ hπ hF hσσ).comp (isProperMap_zeroLocusHom _)),
    ← borelMooreHomology.pushforward_pushforward_eq_comp R (ModuleCat.of R R) _ _
      (isProperMap_zeroLocusHom _) (isProperMap_zeroLocusMap σ _ hπ hF hσσ)]
  erw [h']
  rw [pushforward_congrDegree, ← hpush]
  erw [pushforward_localizedTopChernCap_of_comp R σ (pullbackSectionMap ν hσ) hπ hF hσσ]

/-- **Fulton's Lemma 19.1.3, on Stacks bundles and cycles** (Fulton, §19.1). Let `X` be a complex
variety of dimension `k + 1`, `ℒ` an invertible `𝒪_X`-module and `s ∈ Γ(X, ℒ)` non-zero, with
section `σ_s : X ⟶ 𝐕(ℒ^∨)` and zero scheme `D = Z(s)`. Then `σ_s^*(u) ∩ cl(X) = cl_D([D]_k)` in
`H_{2k} D` for every fundamental class `cl(X)`. -/
theorem localizedFirstChernFormula [IsIntegral X] {k : ℕ}
    (hn : ((k + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim X) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (hs : s ≠ 0) :
    LocalizedFirstChernFormula R hn (Scheme.Modules.dual L) (globalSectionMap L s) := by
  have hX := MMP.finite_irreducibleComponents_of_isIntegral X
  have : IsFinite (X.normalization hX) :=
    normalization_isFinite X (isJapaneseScheme_of_isNagataScheme X
      (isNagataScheme_of_locallyOfFiniteType_over_field ℂ (X ↘ Spec (.of ℂ))))
  have hn' : ((k + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim (X.normalizationScheme hX) :=
    (topologicalKrullDim_normalizationSchemeOverField (X ↘ Spec (.of ℂ)) hn.symm).symm
  have := Scheme.isNormal_normalizationScheme X hX
  have hsurj := (X.normalization hX).surjective
  have hdeg := residueDegree_genericPoint_eq_one_of_isBirational (X.normalization hX)
    (Scheme.isBirational_normalization X hX)
  have hσ := globalSectionMap_proj L s
  have h0 : globalSectionMap L s ≠ zeroSection (Scheme.Modules.dual L) := fun h ↦
    hs (eq_zero_of_globalSectionMap_eq_zeroSection L s h)
  exact LocalizedFirstChernFormula.of_proper_birational R hn' hσ _ hsurj hdeg
    (properPushforward_zeroLocusSubschemeMap_globalSectionMap _ hn hn' hsurj hdeg L s hs)
    (LocalizedFirstChernFormula.of_isNormal R hn' (pullbackSectionMap_proj _ hσ)
      (pullbackSectionMap_ne_zeroSection _ hσ h0 hsurj))

end MMP.Modules
