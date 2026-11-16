module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.Statement
public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.StacksChainBaseChange
public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksNormalization
public import MMP.AlgebraicTopology.BorelMoore.PushforwardSheets
public import MMP.AlgebraicGeometry.Chow.CycleClassFundamental
public import MMP.AlgebraicGeometry.Chow.CycleClassGenericPoint
public import MMP.AlgebraicGeometry.Chow.CycleClassPushforward
public import MMP.AlgebraicTopology.CapProduct.SupportLemmas
public import MMP.AlgebraicTopology.CapProduct.ExteriorProduct
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessIntersectionFormula
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinFundamentalClass
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.GysinZeroSectionDischarge
public import StacksFrontier.AlgebraicGeometry.Chow.DivisorTransport
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.DivisorOrientation

/-!
# Fulton's Theorem 19.2 for `[V]` meeting a divisor properly

Let `f : X ⟶ Y` be a regular closed immersion of codimension one of complex schemes, with
orientation class `u ∈ H²(Y, Y - X)`, `V` a complex variety of dimension `m + 1` and
`j : V ⟶ Y` such that the base change `X_V = X ×_Y V ⟶ V` is again a regular closed immersion of
codimension one (`V ⊄ X`). This file proves Fulton's Theorem 19.2 for `α = [V]`
(`MMP.Chow.ChowCycleMapRefinedGysinFormulaAt`), following Fulton's proof through Lemma 19.1.3.

* On the Chow side, Stacks 0FBM at vanishing excess gives `f^![V]_{m+1} = [X_V]_m`.
* On the topological side, `j^*u` is an orientation class of `X_V ⟶ V`
  (`MMP.Modules.IsRegularImbeddingOrientationClass.pullback_of_isPullback`); writing
  `X_V = Z(σ)` for a section `σ` of a line bundle on `V`, it is `σ^*u_ℰ`, so
  `j^*u ∩ cl(V)` is the localized top Chern class `σ^*u_ℰ ∩ cl(V)`, which is `cl([Z(σ)]_m)` by
  Fulton's Lemma 19.1.3 (`MMP.Modules.localizedFirstChernFormula`).
* The two sides are compared along the isomorphism `X_V ≅ Z(σ)` over `V`.

## Main results

* `MMP.Chow.chowCycleMapRefinedGysinFormulaAt_fundamentalChowClass_of_isRegular`: **Fulton's
  Theorem 19.2 for `[V]`** when `X_V ⟶ V` is regular of codimension one.
* `MMP.Chow.regularNormalGysinClass_cap_fundamentalChowClass_of_isRegular`: `f^![V] = [X_V]`.
* `MMP.Chow.capProductSupportPullback_eq_pushforward_localizedTopChernCap`: `j^*u ∩ a` as a
  localized top Chern class.
* `MMP.Chow.ne_zero_of_zeroLocus_globalSectionMap_eq_ker`: the section cutting out `X_V` is
  non-zero.
* `MMP.Chow.cycleClass_fundamentalCycle_of_isVarietyFundamentalClass`: `cl([V]) = μ` for every
  fundamental class `μ` of a complex variety `V`.
* `MMP.Chow.chowCycleMapRefinedGysinFormulaAt_fundamentalChowClass_of_section`: the formula for
  `[V]`, given a section `σ` of a line bundle on `V` with zero scheme `X_V` and whose pulled-back
  Thom class is every orientation class of `X_V ⟶ V`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1–19.2, Lemma 19.1.3, Theorem 19.2.
* [Stacks Project, Tag 0FBM](https://stacks.math.columbia.edu/tag/0FBM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set Stacks.Chow MMP.UnderlyingSpace
open Stacks.AlgebraicGeometry.RegularIdealSheaf MMP.Modules
open scoped MMP.SubschemeOver

namespace MMP.Chow

attribute [local instance] fibreProductOver isOver_fibreProduct_fst isOver_fibreProduct_snd
  isComplexScheme_fibreProduct

/-! ### Generalities -/

/-- Transport along an equality of degrees sends a fundamental class to the fundamental
class. -/
theorem chowGroupCongrDegree_fundamentalChowClass (C : ChowSituation.{0}) {T : Scheme.{0}}
    (sT : T ⟶ C.S) [LocallyOfFiniteType sT] {k k' : ℤ} (h : k = k') :
    chowGroupCongrDegree C sT h (fundamentalChowClass C sT k) = fundamentalChowClass C sT k' := by
  subst h
  rfl

/-- The cycle class of a fundamental class is that of the fundamental cycle. -/
theorem chowCycleClass_fundamentalChowClass (R : Type) [CommRing R] {T : Scheme.{0}}
    [T.Over (Spec (.of ℂ))] [IsComplexScheme T] (k : ℕ) :
    chowCycleClass R k (fundamentalChowClass (fieldChowSituation ℂ) (T ↘ Spec (.of ℂ)) k) =
      cycleClass R k (fundamentalCycle (fieldChowSituation ℂ) (T ↘ Spec (.of ℂ)) k) :=
  rfl

/-- The forgetful map `H^j(Y, Y - A) → H^j(Y, Y - B)` is injective when `A = B`. -/
lemma forget_injective_of_subset {R : Type} [CommRing R] {Y : TopCat.{0}} {A B : Set Y}
    (h : A ⊆ B) (h' : B ⊆ A) (j : ℤ) :
    Function.Injective (cohomologyWithSupports.forget R (ModuleCat.of R R) Y h j).hom := by
  intro a b hab
  have e := congrArg (cohomologyWithSupports.forget R (ModuleCat.of R R) Y h' j).hom hab
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
    ← cohomologyWithSupports.forget_trans] at e
  simpa [cohomologyWithSupports.forget_refl] using e

/-- The cycle class of the fundamental cycle `[V]_k` of a complex variety `V` of dimension `k`
is its fundamental class. -/
theorem cycleClass_fundamentalCycle_of_isVarietyFundamentalClass (R : Type) [CommRing R]
    {V : Scheme.{0}} [V.Over (Spec (.of ℂ))] [IsComplexScheme V] [IsIntegral V] {k : ℕ}
    (hk : (k : WithBot ℕ∞) = topologicalKrullDim V)
    {μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ V)) (2 * k : ℕ)}
    (hμ : IsVarietyFundamentalClass R hk μ) :
    cycleClass R k (fundamentalCycle (fieldChowSituation ℂ) (V ↘ Spec (.of ℂ)) k) = μ := by
  have hη : relativeDimension (fieldChowSituation ℂ).dimensionFunction
      (V ↘ Spec (.of ℂ)) (_root_.genericPoint V) = (k : ℤ) :=
    relativeDimension_fieldChowSituation_genericPoint (V ↘ Spec (.of ℂ)) hk.symm
  have hcyc : fundamentalCycle (fieldChowSituation ℂ) (V ↘ Spec (.of ℂ)) k =
      pointCycle (fieldChowSituation ℂ) (V ↘ Spec (.of ℂ)) k (_root_.genericPoint V) hη := by
    refine Subtype.ext ?_
    ext y
    rw [pointCycle_apply]
    by_cases hy : y = _root_.genericPoint V
    · subst hy
      simp only [↓reduceIte]
      exact cycleAssociatedToClosedSubscheme_isIntegral_apply_genericPoint _ _ (𝟙 V) k hη
    · simp only [hy, ↓reduceIte]
      exact cycleAssociatedToClosedSubscheme_isIntegral_apply_of_ne _ _ (𝟙 V) k hy
  rw [hcyc, cycleClass_pointCycle]
  exact pointCycleClass_eq_of_closure_eq_univ _ hη (genericPoint_spec V).def hk hμ

/-! ### The identification `X_V ≅ Z(σ)` -/

section Iso

variable {P V : Scheme.{0}} (i : P ⟶ V) [IsClosedImmersion i] (I : V.IdealSheafData)
  (h : I = i.ker)

/-- A closed immersion `i : P ⟶ V` whose ideal is `I` identifies `P` with the closed subscheme
of `I`. -/
def toSubschemeOfEqKer : P ⟶ I.subscheme :=
  i.toImage ≫ Scheme.IdealSheafData.inclusion h.le

omit [IsClosedImmersion i] in
/-- The morphism `toSubschemeOfEqKer i I h` followed by the inclusion of the closed subscheme of
`I` is `i`. -/
@[reassoc (attr := simp)]
lemma toSubschemeOfEqKer_subschemeι : toSubschemeOfEqKer i I h ≫ I.subschemeι = i := by
  simp [toSubschemeOfEqKer]

/-- The morphism `toSubschemeOfEqKer i I h` is an isomorphism. -/
instance isIso_toSubschemeOfEqKer : IsIso (toSubschemeOfEqKer i I h) := by
  have : IsIso (Scheme.IdealSheafData.inclusion h.le) :=
    ⟨Scheme.IdealSheafData.inclusion h.ge, by simp, by simp⟩
  unfold toSubschemeOfEqKer
  infer_instance

end Iso

/-! ### Theorem 19.2 for `[V]` -/

variable {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of ℂ))]
  (R : Type) [CommRing R] [IsComplexScheme X] [IsComplexScheme Y]
  [IsClosedImmersion f]
  {V : Scheme.{0}} [V.Over (Spec (.of ℂ))] [IsComplexScheme V] [IsIntegral V]
  (j : V ⟶ Y) [j.IsOver (Spec (.of ℂ))] [LocallyOfFiniteType j]

/-- **The Chow side: Stacks 0FBM at vanishing excess.** If `X_V ⟶ V` is regular of codimension
one, `f^![V]_{m+1} = [X_V]_m`. -/
theorem regularNormalGysinClass_cap_fundamentalChowClass_of_isRegular
    (hf : IsRegularClosedImmersionOfCodim f 1) {m : ℕ}
    (hV : ((m + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim V)
    (hj : IsRegularClosedImmersionOfCodim (pullback.snd f j) 1) :
    chowGroupCongrDegree (fieldChowSituation ℂ) (pullback.fst f j ≫ X ↘ Spec (.of ℂ))
        (natCast_add_sub_natCast m 1)
        ((regularNormalGysinClass (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
            (Y ↘ Spec (.of ℂ)) f (comp_over f _) hf).cap j ((m + 1 : ℕ) : ℤ)
          (chowGroupCongr (fieldChowSituation ℂ) (q := V ↘ Spec (.of ℂ))
            (q' := j ≫ Y ↘ Spec (.of ℂ)) (comp_over j _).symm ((m + 1 : ℕ) : ℤ)
            (fundamentalChowClass (fieldChowSituation ℂ) (V ↘ Spec (.of ℂ)) (m + 1 : ℕ)))) =
      fundamentalChowClass (fieldChowSituation ℂ) (pullback.fst f j ≫ X ↘ Spec (.of ℂ)) m := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of ℂ))
  have := hf.isFiniteLocallyFreeOfRank_conormalModule
  have := hj.isFiniteLocallyFreeOfRank_conormalModule
  have hY : schemeDeltaDimension (fieldChowSituation ℂ) (j ≫ Y ↘ Spec (.of ℂ)) ≤
      (((m + 1 : ℕ) : ℤ) : EInt) :=
    (schemeDeltaDimension_fieldChowSituation_eq_of_topologicalKrullDim_eq
      (j ≫ Y ↘ Spec (.of ℂ)) hV.symm).le
  rw [chowGroupCongr_fundamentalChowClass]
  unfold regularNormalGysinClass
  rw [virtualNormalBundleClass_cap_fundamentalChowClass (fieldChowSituation ℂ)
    (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) f (comp_over f _)
    (VirtualNormalBundle.ofIsRegularImmersion f hf.isRegularImmersion) 1
    (isVirtualNormalBundleClass_virtualNormalBundleClass (fieldChowSituation ℂ) _ _ f _ _ 1) j
    (pullback.snd f j) (pullback.fst f j) (IsPullback.of_hasPullback f j).flip
    (pullback.snd f j ≫ j ≫ Y ↘ Spec (.of ℂ)) rfl hj.isRegularImmersion _ hY]
  exact chowGroupCongrDegree_fundamentalChowClass _ _ _

omit [IsComplexScheme X] [IsIntegral V] [LocallyOfFiniteType j] in
variable {f j} in
/-- **The topological side.** If `j^*u = σ^*u_ℰ` as classes supported on `j⁻¹(X(ℂ))`, then
`j^*u ∩ a` is the localized top Chern class `σ^*u_ℰ ∩ a`, pushed forward to `j⁻¹(X(ℂ))`. -/
theorem capProductSupportPullback_eq_pushforward_localizedTopChernCap
    {E : V.Modules} [E.IsQuasicoherent]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E 1]
    (σ : V ⟶ totalSpace E) [σ.IsOver (Spec (.of ℂ))]
    (hBA : (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) (zeroSection E)) ⊆
      (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) j)).hom ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) f))
    (u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ Y))
      (range (UnderlyingSpace.map (K := ℂ) f)) (2 * 1 : ℕ))
    (hpb : (cohomologyWithSupports.pullback R (ModuleCat.of R R)
        (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) j)) _ _).hom u =
      (cohomologyWithSupports.forget R (ModuleCat.of R R) _ hBA _).hom
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
          (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)) _ _).hom (thomClass R E 1)))
    (k : ℤ) (a : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ V)) k) :
    borelMooreHomology.capProductSupportPullback R
        (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) j))
        (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) f).isClosed_range
        (hasProperNeighbourhoodDeformations_preimage_range_map f j)
        ((2 * 1 : ℕ) : ℤ) k u a =
      (borelMooreHomology.pushforward R (ModuleCat.of R R)
        (borelMooreHomology.subsetInclusionOfSubset hBA)
        (borelMooreHomology.isProperMap_subsetInclusionOfSubset
          (isClosed_range_zeroSection.preimage (continuous_mapFun σ)) hBA) _).hom
        (localizedTopChernCap σ R 1 k a) := by
  rw [borelMooreHomology.capProductSupportPullback_apply, hpb, localizedTopChernCap,
    borelMooreHomology.capProductSupportPullback_apply,
    borelMooreHomology.pushforward_subsetInclusionOfSubset_capProductSupport]

/-- **Fulton's Theorem 19.2 for `[V]`, `V ⊄ X`, given the divisor as a zero scheme.** Let
`f : X ⟶ Y` be a regular closed immersion of codimension one with orientation class `u`, `V` a
complex variety of dimension `m + 1` and `j : V ⟶ Y` with `X_V ⟶ V` regular of codimension one.
Let `s ≠ 0` be a global section of an invertible module `L` on `V` whose zero scheme is `X_V`,
with section `σ` of `𝐕(L^∨)`, such that `X_V` is the fibre product of `σ` and the zero section
and every orientation class of `X_V ⟶ V` is `σ^*u_{L^∨}`. Then
`cl_{X_V}(f^![V]) = j^*u ∩ cl(V)`. -/
theorem chowCycleMapRefinedGysinFormulaAt_fundamentalChowClass_of_section
    (hf : IsRegularClosedImmersionOfCodim f 1)
    {u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ Y))
      (range (UnderlyingSpace.map (K := ℂ) f)) (2 * 1 : ℕ)}
    (hu : MMP.Modules.IsRegularImbeddingOrientationClass R f 1 u) {m : ℕ}
    (hV : ((m + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim V)
    (hj : IsRegularClosedImmersionOfCodim (pullback.snd f j) 1)
    (L : V.Modules) [Stacks.Ample.IsInvertibleModule V L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj V.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (hs : s ≠ 0)
    (hz : zeroLocus (Scheme.Modules.dual L) (globalSectionMap L s) = (pullback.snd f j).ker)
    (hsq : IsPullback (pullback.snd f j) (pullback.snd f j) (globalSectionMap L s)
      (zeroSection (Scheme.Modules.dual L)))
    (hthom : ∀ u' : cohomologyWithSupports R (ModuleCat.of R R)
        (TopCat.of (UnderlyingSpace ℂ V))
        (range (UnderlyingSpace.map (K := ℂ) (pullback.snd f j))) (2 * 1 : ℕ),
      MMP.Modules.IsRegularImbeddingOrientationClass R (pullback.snd f j) 1 u' →
      u' = (cohomologyWithSupports.forget R (ModuleCat.of R R) _
        (range_map_eq_preimage_of_isPullback hsq).ge _).hom
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
          (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (globalSectionMap L s))) _ _).hom
            (thomClass R (Scheme.Modules.dual L) 1))) :
    ChowCycleMapRefinedGysinFormulaAt f j R hf u m
      (fundamentalChowClass (fieldChowSituation ℂ) (V ↘ Spec (.of ℂ)) (m + 1 : ℕ)) := by
  have sq := (IsPullback.of_hasPullback f j).flip
  have hAR := range_map_eq_preimage_of_isPullback sq
  have hBA : (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (globalSectionMap L s))).hom ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) (zeroSection (Scheme.Modules.dual L))) ⊆
      (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) j)).hom ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) f) :=
    (range_map_eq_preimage_of_isPullback hsq).symm.le.trans hAR.le
  -- `j^*u = σ^*u_{L^∨}` as classes supported on `j⁻¹(X(ℂ))`
  have hpb : (cohomologyWithSupports.pullback R (ModuleCat.of R R)
        (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) j)) _ _).hom u =
      (cohomologyWithSupports.forget R (ModuleCat.of R R) _ hBA _).hom
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
          (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (globalSectionMap L s))) _ _).hom
            (thomClass R (Scheme.Modules.dual L) 1)) := by
    apply forget_injective_of_subset (R := R) hAR.ge hAR.le
    refine (hthom _ (MMP.Modules.IsRegularImbeddingOrientationClass.pullback_of_isPullback R hf hj
      sq hu)).trans ?_
    exact congrArg (fun φ ↦ ModuleCat.Hom.hom φ _)
      (cohomologyWithSupports.forget_trans R (ModuleCat.of R R) _ hBA hAR.ge ((2 * 1 : ℕ) : ℤ))
  -- the fundamental class of `V`
  obtain ⟨μ, hμ, -⟩ := existsUnique_isVarietyFundamentalClass R hV
  -- the identification `X_V ≅ Z(σ)` over `ℂ`
  set e := toSubschemeOfEqKer (pullback.snd f j) _ hz
  have he : e ≫ ((zeroLocus (Scheme.Modules.dual L) (globalSectionMap L s)).subscheme ↘
      Spec (.of ℂ)) = pullback.fst f j ≫ X ↘ Spec (.of ℂ) := by
    change e ≫ (zeroLocus (Scheme.Modules.dual L) (globalSectionMap L s)).subschemeι ≫
      V ↘ Spec (.of ℂ) = _
    rw [toSubschemeOfEqKer_subschemeι_assoc]
    exact comp_over (pullback.snd f j) (Spec (.of ℂ))
  have : e.IsOver (Spec (.of ℂ)) := ⟨he⟩
  have hcyc : cycleClass R m (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
        ((zeroLocus (Scheme.Modules.dual L) (globalSectionMap L s)).subscheme ↘ Spec (.of ℂ))
        (𝟙 _) m) =
      borelMooreHomology.pushforward R (ModuleCat.of R R)
        (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) e)) (isProperMap_map (K := ℂ) e) (2 * m : ℕ)
        (cycleClass (X := pullback f j) R m
          (fundamentalCycle (fieldChowSituation ℂ) (pullback f j ↘ Spec (.of ℂ)) m)) := by
    rw [← cycleClass_properPushforward]
    exact congrArg (cycleClass R m) (properPushforward_fundamentalCycle_of_isIso
      (fieldChowSituation ℂ) _ _ e he m).symm
  have hF := localizedFirstChernFormula R hV L s hs μ hμ
  rw [hcyc] at hF
  unfold ChowCycleMapRefinedGysinFormulaAt
  rw [regularNormalGysinClass_cap_fundamentalChowClass_of_isRegular f j hf hV hj,
    capProductSupportPullback_eq_pushforward_localizedTopChernCap R (globalSectionMap L s) hBA u
      hpb]
  have hP : chowCycleClass (X := pullback f j) R m (fundamentalChowClass (fieldChowSituation ℂ)
      (pullback.fst f j ≫ X ↘ Spec (.of ℂ)) m) = cycleClass (X := pullback f j) R m
        (fundamentalCycle (fieldChowSituation ℂ) (pullback f j ↘ Spec (.of ℂ)) m) := rfl
  rw [chowCycleClass_fundamentalChowClass, hP,
    cycleClass_fundamentalCycle_of_isVarietyFundamentalClass R hV hμ,
    ← borelMooreHomology.pushforward_congrDegree, ← hF,
    borelMooreHomology.pushforward_pushforward_eq_comp,
    borelMooreHomology.pushforward_pushforward_eq_comp]
  refine congrArg (fun φ ↦ ModuleCat.Hom.hom φ _)
    (borelMooreHomology.pushforward_congr_hom R (ConcreteCategory.hom_ext _ _ fun p ↦ ?_) _ _ _)
  refine Subtype.ext (UnderlyingSpace.ext ?_)
  change p.toHom ≫ pullback.snd f j = (p.toHom ≫ e) ≫
    (zeroLocus (Scheme.Modules.dual L) (globalSectionMap L s)).subschemeι
  rw [Category.assoc, toSubschemeOfEqKer_subschemeι]

omit [IsComplexScheme Y] in
variable {f j} in
/-- `X_V ⟶ V` regular of codimension one is not an isomorphism: the zero scheme of the section
`s` cutting it out is a proper closed subscheme, so `s ≠ 0`. -/
theorem ne_zero_of_zeroLocus_globalSectionMap_eq_ker {m : ℕ}
    (hV : ((m + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim V)
    (hj : IsRegularClosedImmersionOfCodim (pullback.snd f j) 1)
    (L : V.Modules) [Stacks.Ample.IsInvertibleModule V L] (s : Γ(L, ⊤))
    (hz : zeroLocus (Scheme.Modules.dual L) (globalSectionMap L s) = (pullback.snd f j).ker) :
    s ≠ 0 := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj V.ringCatSheaf.property L :=
    ‹Stacks.Ample.IsInvertibleModule V L›
  rintro rfl
  have hbot : (pullback.snd f j).ker = ⊥ := by
    rw [← hz, zeroLocus_globalSectionMap, Stacks.Divisors.zeroScheme_zero_eq_bot]
  have : IsIso (pullback.snd f j) := IsClosedImmersion.isIso_iff_ker_eq_bot.2 hbot
  have : IrreducibleSpace ↥(Limits.pullback f j : Scheme.{0}) :=
    (Scheme.homeoOfIso (asIso (pullback.snd f j))).symm.surjective.irreducibleSpace
      (Scheme.homeoOfIso (asIso (pullback.snd f j))).symm.continuous
  have : IsLocallyNoetherian (pullback f j) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f j ≫ X ↘ Spec (.of ℂ))
  have := hj.isFiniteLocallyFreeOfRank_conormalModule
  have hVd := schemeDeltaDimension_fieldChowSituation_eq_of_topologicalKrullDim_eq
    (V ↘ Spec (.of ℂ)) hV.symm
  have h1 := schemeDeltaDimension_le_sub_of_isRegularImmersion (fieldChowSituation ℂ)
    (pullback.fst f j ≫ X ↘ Spec (.of ℂ)) (V ↘ Spec (.of ℂ)) (pullback.snd f j)
    (comp_over (pullback.snd f j) _) hj.isRegularImmersion 1 ((m + 1 : ℕ) : ℤ) hVd.le
  rw [← schemeDeltaDimension_of_iso (fieldChowSituation ℂ)
    (pullback.fst f j ≫ X ↘ Spec (.of ℂ)) (V ↘ Spec (.of ℂ))
    (asIso (pullback.snd f j)) (comp_over (pullback.snd f j) _), hVd] at h1
  have := WithBotTop.coe_le_coe.mp h1
  omega

/-- **Fulton's Theorem 19.2 for `[V]` when `V ×_Y X ⟶ V` is a divisor** (Fulton, §19.2, via
Lemma 19.1.3). Let `f : X ⟶ Y` be a regular closed immersion of codimension one with orientation
class `u`, `V` a complex variety of dimension `m + 1` and `j : V ⟶ Y` such that
`X_V = X ×_Y V ⟶ V` is a regular closed immersion of codimension one. Then
`cl_{X_V}(f^![V]_{m+1}) = j^*u ∩ cl(V)` in `H_{2m}(j⁻¹(X(ℂ)))`. -/
theorem chowCycleMapRefinedGysinFormulaAt_fundamentalChowClass_of_isRegular
    (hf : IsRegularClosedImmersionOfCodim f 1)
    {u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ Y))
      (range (UnderlyingSpace.map (K := ℂ) f)) (2 * 1 : ℕ)}
    (hu : MMP.Modules.IsRegularImbeddingOrientationClass R f 1 u) {m : ℕ}
    (hV : ((m + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim V)
    (hj : IsRegularClosedImmersionOfCodim (pullback.snd f j) 1) :
    ChowCycleMapRefinedGysinFormulaAt f j R hf u m
      (fundamentalChowClass (fieldChowSituation ℂ) (V ↘ Spec (.of ℂ)) (m + 1 : ℕ)) := by
  obtain ⟨L, hL, s, hz⟩ := exists_zeroLocus_globalSectionMap_eq_ker (pullback.snd f j) hj
  have : AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj V.ringCatSheaf.property L := hL
  have hσ := globalSectionMap_proj L s
  exact chowCycleMapRefinedGysinFormulaAt_fundamentalChowClass_of_section f R j hf hu hV hj L s
    (ne_zero_of_zeroLocus_globalSectionMap_eq_ker hV hj L s hz) hz
    (isPullback_zeroLocus_zeroSection (pullback.snd f j) _ hσ hz)
    (fun u' hu' ↦ eq_forget_pullback_thomClass (pullback.snd f j) R hj _ hσ hz hu')

end MMP.Chow
