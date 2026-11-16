module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.Statement
public import MMP.AlgebraicGeometry.CycleMap.Stacks.Pushforward
public import MMP.AlgebraicGeometry.Chow.FirstChernClassTopAdditive
public import MMP.AlgebraicGeometry.Chow.CycleClassFirstChern
public import MMP.AlgebraicGeometry.Chow.CycleClassGenericPoint
public import MMP.AlgebraicGeometry.Analytic.DivisorOrientationDatum
public import MMP.AlgebraicGeometry.RegularImmersion.CodimOne
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessIntersectionFormula
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.RegularImmersionSelfIntersection
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleRankOne
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.TautologicalKernelTopChern
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ZeroSchemeVirtualNormalBundle
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeRegular
public import StacksFrontier.AlgebraicGeometry.Conormal.SquareFlatIso
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.DivisorOrientation

/-!
# Fulton's Theorem 19.2 for a divisor containing the test variety

Let `f : X ⟶ Y` be a regular closed immersion of codimension one of complex schemes (an effective
Cartier divisor `D = ker f`), with orientation class `u`, and let `j : V ⟶ Y` be a complex variety
of dimension `m + 1` lying in the divisor (`V ×_Y X ⟶ V` an isomorphism), so that `j = π ≫ f`.
This file proves Fulton's Theorem 19.2 for `α = [V]` in this case of full excess:

* on the Chow side, Stacks 0FBM at full excess
  (`Stacks.Chow.virtualNormalBundleClass_cap_fundamentalChowClass_excess`, with `i' = 𝟙 V`) gives
  `f^![V] = c₁(π^*𝒩) ∩ [V]`, `𝒩 = 𝒞_{X/Y}^∨`, whose cycle class is `c₁ᵗᵒᵖ(π^*𝒩) ∩ cl(V)`
  (`MMP.Chow.chowCycleClass_firstChernClassCap`);
* on the topological side, the image of `j^* u` in `H²(V(ℂ))` is `c₁ᵗᵒᵖ(j^*𝒪_Y(D)^∨)`
  (`MMP.Chow.forget_pullback_eq_topFirstChernClass`), and the conormal sheaf of the divisor is
  `𝒞_{X/Y} ≅ f^*𝒪_Y(D)^∨` (`MMP.Chow.conormalModuleIsoPullbackDivisorDualSheaf`, from Stacks 0FBN:
  the canonical surjection `(i^*𝒪_Y(D))^∨ ⟶ 𝒞` is an isomorphism for the regular section `1_D`).

## Main results

* `MMP.Chow.chowCycleMapRefinedGysinFormulaAt_fundamentalChowClass_of_isIso`: Theorem 19.2 for
  `[V]` when `V` lies in the divisor.
* `MMP.Chow.conormalModuleCanonicalZeroSchemeIso`: `𝒞_{Z(1_D)/Y} ≅ (i^*𝒪_Y(D))^∨`.
* `MMP.Chow.conormalModuleIsoPullbackDivisorDualSheaf`: `𝒞_{X/Y} ≅ f^*𝒪_Y(D)^∨`.
* `MMP.Chow.toCohomology_pullback_comp`: forgetting supports commutes with pull-back.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], Theorem 19.2.
* [Stacks Project, Tag 0FBM](https://stacks.math.columbia.edu/tag/0FBM)
* [Stacks Project, Tag 0FBN](https://stacks.math.columbia.edu/tag/0FBN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set Stacks.Chow MMP.UnderlyingSpace
open Stacks.AlgebraicGeometry.RegularIdealSheaf Stacks.AlgebraicGeometry.ReflexiveModules
open MMP.Modules

namespace MMP.Chow

/-! ### The conormal sheaf of an effective Cartier divisor -/

section Conormal

variable {Y : Scheme.{0}} (D : Y.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]

/-- The zero scheme of the canonical section `1_D` of `𝒪_Y(D)`. -/
abbrev canonicalZeroScheme : Y.IdealSheafData :=
  zeroScheme Y (Stacks.Divisors.divisorSheaf D) (Stacks.Divisors.divisorSheafGlobalSection D)

/-- The zero scheme of the canonical section `1_D` of `𝒪_Y(D)` is `D`. -/
theorem canonicalZeroScheme_eq : canonicalZeroScheme D = D :=
  Stacks.Divisors.zeroScheme_canonicalSection D

/-- The canonical section `1_D` is a regular section. -/
theorem injective_smul_divisorSheafGlobalSection (U : Y.Opens) :
    Function.Injective fun r : Γ(Y, U) =>
      r • (Stacks.Divisors.divisorSheaf D).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
        (Stacks.Divisors.divisorSheafGlobalSection D) :=
  injective_smul_res_of_isRegularSection (Stacks.Divisors.divisorSheaf D)
    (Stacks.Divisors.canonicalSection' D)
    ((isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection Y _ _).mp (by
      have h := canonicalZeroScheme_eq D
      unfold canonicalZeroScheme Stacks.Divisors.divisorSheafGlobalSection at h
      rw [h]
      infer_instance)) U

/-- **The conormal sheaf of the zero scheme of `1_D`** is `(i^*𝒪_Y(D))^∨`: the canonical
surjection `(i^*𝒪_Y(D))^∨ ⟶ 𝒞` of Stacks 0FBN is an isomorphism for a regular section. -/
def conormalModuleCanonicalZeroSchemeIso :
    conormalModule (canonicalZeroScheme D).subschemeι ≅
      dualSheaf ((Scheme.Modules.pullback (canonicalZeroScheme D).subschemeι).obj
        (Stacks.Divisors.divisorSheaf D)) :=
  have := isIso_zeroSchemeIdealModuleHom (Stacks.Divisors.divisorSheaf D)
    (Stacks.Divisors.divisorSheafGlobalSection D) (injective_smul_divisorSheafGlobalSection D)
  ((Stacks.FundamentalGroup.pullbackDualSheafIso (canonicalZeroScheme D).subschemeι
      (Stacks.Divisors.divisorSheaf D)
      (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1
        (hM := Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_one_of_isInvertible _
          (Stacks.Divisors.isInvertible_divisorSheaf D)))).symm ≪≫
    (Scheme.Modules.pullback (canonicalZeroScheme D).subschemeι).mapIso
      (asIso (zeroSchemeIdealModuleHom (Stacks.Divisors.divisorSheaf D)
        (Stacks.Divisors.divisorSheafGlobalSection D))) ≪≫
    (Stacks.Divisors.conormalSheafIsoNegativeTwist (canonicalZeroScheme D)).symm).symm

end Conormal

/-! ### The conormal sheaf of a divisor `f : X ⟶ Y` -/

section DivisorConormal

variable {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f]
  [Stacks.Divisors.IsEffectiveCartierDivisor f.ker]

/-- The identification of `X` with the zero scheme of the canonical section of `𝒪_Y(ker f)`. -/
def toCanonicalZeroScheme : X ⟶ (canonicalZeroScheme f.ker).subscheme :=
  IsClosedImmersion.lift (canonicalZeroScheme f.ker).subschemeι f
    (by rw [Scheme.IdealSheafData.ker_subschemeι, canonicalZeroScheme_eq])

omit [IsClosedImmersion f] in
/-- The composite of `toCanonicalZeroScheme f` with the inclusion of the zero scheme of `1_D` is
`f`. -/
@[reassoc (attr := simp)]
theorem toCanonicalZeroScheme_subschemeι :
    toCanonicalZeroScheme f ≫ (canonicalZeroScheme f.ker).subschemeι = f :=
  IsClosedImmersion.lift_fac _ _ _

/-- The morphism `toCanonicalZeroScheme f` is an isomorphism. -/
instance isIso_toCanonicalZeroScheme : IsIso (toCanonicalZeroScheme f) := by
  let g := IsClosedImmersion.lift f (canonicalZeroScheme f.ker).subschemeι
    (by rw [Scheme.IdealSheafData.ker_subschemeι, canonicalZeroScheme_eq])
  refine ⟨g, ?_, ?_⟩
  · rw [← cancel_mono f, Category.assoc, IsClosedImmersion.lift_fac,
      toCanonicalZeroScheme_subschemeι, Category.id_comp]
  · rw [← cancel_mono (canonicalZeroScheme f.ker).subschemeι, Category.assoc,
      toCanonicalZeroScheme_subschemeι, IsClosedImmersion.lift_fac, Category.id_comp]

/-- The square with sides `f`, `toCanonicalZeroScheme f`, `𝟙 Y` and the inclusion of the zero
scheme of `1_D` is a pullback square. -/
theorem isPullback_toCanonicalZeroScheme :
    IsPullback f (toCanonicalZeroScheme f) (𝟙 Y) (canonicalZeroScheme f.ker).subschemeι :=
  IsPullback.of_vert_isIso ⟨by simp⟩

/-- **The conormal sheaf of a divisor** `f : X ⟶ Y` is `f^* 𝒪_Y(D)^∨`, `D = ker f`. -/
def conormalModuleIsoPullbackDivisorDualSheaf :
    conormalModule f ≅ (Scheme.Modules.pullback f).obj
      (Scheme.Modules.dual (Stacks.Divisors.divisorSheaf f.ker)) :=
  have hL : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{0, 0, 0}
      (Stacks.Divisors.divisorSheaf f.ker) :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1
      (hM := Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_one_of_isInvertible _
        (Stacks.Divisors.isInvertible_divisorSheaf f.ker))
  (@asIso _ _ _ _ (Stacks.Immersion.immersionConormalSheafMap f
      (canonicalZeroScheme f.ker).subschemeι (toCanonicalZeroScheme f) (𝟙 Y)
      (Stacks.Immersion.toShHom_square (isPullback_toCanonicalZeroScheme f).w))
    (Stacks.Immersion.isIso_immersionConormalSheafMap_of_flat f _ _ _
      (isPullback_toCanonicalZeroScheme f))).symm ≪≫
    (Scheme.Modules.pullback (toCanonicalZeroScheme f)).mapIso
      (conormalModuleCanonicalZeroSchemeIso f.ker ≪≫
        (Stacks.FundamentalGroup.pullbackDualSheafIso (canonicalZeroScheme f.ker).subschemeι
          (Stacks.Divisors.divisorSheaf f.ker) hL).symm) ≪≫
    (Scheme.Modules.pullbackComp (toCanonicalZeroScheme f)
      (canonicalZeroScheme f.ker).subschemeι).app _ ≪≫
    (Scheme.Modules.pullbackCongr (toCanonicalZeroScheme_subschemeι f)).app _

end DivisorConormal

/-! ### Forgetting supports commutes with pull-back -/

/-- For `g ≫ f = k`, the image in absolute cohomology of the pull-back along `k` of a class with
supports in `S` equals the pull-back along `g` of the image in absolute cohomology of its
pull-back along `f`. -/
theorem toCohomology_pullback_comp (R : Type) [CommRing R] {A B C : TopCat.{0}} (g : A ⟶ B)
    (f : B ⟶ C) (k : A ⟶ C) (hk : g ≫ f = k) (S : Set C) (n : ℤ)
    (x : cohomologyWithSupports R (ModuleCat.of R R) C S n) :
    (cohomologyWithSupports.toCohomology R _ A (k ⁻¹' S) n).hom
        ((cohomologyWithSupports.pullback R _ k S n).hom x) =
      (cohomologyWithSupports.pullback R _ g univ n).hom
        ((cohomologyWithSupports.forget R _ B (subset_univ _) n).hom
          ((cohomologyWithSupports.pullback R _ f S n).hom x)) := by
  subst hk
  simp only [cohomologyWithSupports.toCohomology, cohomologyWithSupports.forget,
    cohomologyWithSupports.pullback, ← ModuleCat.comp_apply]
  refine congrArg (fun φ => ModuleCat.Hom.hom φ x) ?_
  refine ((relativeSingularCohomology.map_comp R _ (𝟙 A) (g ≫ f) _ _ n).symm.trans ?_).trans
    ((relativeSingularCohomology.map_comp R _ g (𝟙 B ≫ f) _ _ n).trans
      (eq_whisker (relativeSingularCohomology.map_comp R _ (𝟙 B) f _ _ n) _))
  exact relativeSingularCohomology.map_congr_hom R _ _ _ (by simp) n

/-! ### Theorem 19.2 for `[V]` when `V` lies in the divisor -/

section Excess

attribute [local instance] fibreProductOver isOver_fibreProduct_fst isOver_fibreProduct_snd
  isComplexScheme_fibreProduct AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback

/-- Transporting a Chow class along an equality of degrees `a = b` gives a heterogeneously equal
class. -/
theorem chowGroupCongrDegree_heq' {Z : Scheme.{0}} (s : Z ⟶ (fieldChowSituation ℂ).S)
    [LocallyOfFiniteType s] {a b : ℤ} (h : a = b)
    (x : chowGroup (fieldChowSituation ℂ) s a) :
    chowGroupCongrDegree (fieldChowSituation ℂ) s h x ≍ x := by
  subst h
  rfl

/-- The fundamental Chow classes in degrees `a` and `b` are heterogeneously equal when `a = b`. -/
theorem fundamentalChowClass_heq_of_degree_eq {Z : Scheme.{0}}
    (s : Z ⟶ (fieldChowSituation ℂ).S) [LocallyOfFiniteType s] {a b : ℤ} (h : a = b) :
    fundamentalChowClass (fieldChowSituation ℂ) s a ≍
      fundamentalChowClass (fieldChowSituation ℂ) s b := by
  subst h
  rfl

/-- Casting a Chow class along an equality of degrees `a = b` gives a heterogeneously equal
class. -/
theorem chowGroupCast_heq' {Z : Scheme.{0}} (s : Z ⟶ (fieldChowSituation ℂ).S)
    [LocallyOfFiniteType s] {a b : ℤ} (h : a = b) (x : chowGroup (fieldChowSituation ℂ) s a) :
    chowGroupCast (fieldChowSituation ℂ) s h x ≍ x := by
  subst h
  rfl

variable {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of ℂ))]
  (R : Type) [CommRing R] [IsComplexScheme X] [IsComplexScheme Y] [IsClosedImmersion f]

variable {V : Scheme.{0}} [V.Over (Spec (.of ℂ))] [IsComplexScheme V] [IsIntegral V]
  (j : V ⟶ Y) [j.IsOver (Spec (.of ℂ))] [LocallyOfFiniteType j]

/-- **Fulton's Theorem 19.2 for `[V]` when `V` lies in the divisor.** Let `f : X ⟶ Y` be a
regular closed immersion of codimension one with orientation class `u`, and `j : V ⟶ Y` a complex
variety of dimension `m + 1`, carrying an ample invertible module, with `V ×_Y X ⟶ V` an
isomorphism. Then `cl(f^![V]) = j^* u ∩ cl(V)` in `H_{2m}(j⁻¹(X(ℂ)))`. -/
theorem chowCycleMapRefinedGysinFormulaAt_fundamentalChowClass_of_isIso
    (hf : IsRegularClosedImmersionOfCodim f 1)
    {u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ Y))
      (range (UnderlyingSpace.map (K := ℂ) f)) (2 * 1 : ℕ)}
    (hu : MMP.Modules.IsRegularImbeddingOrientationClass R f 1 u) {m : ℕ}
    (hV : ((m + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim V)
    (A : V.Modules) [Stacks.Ample.IsInvertibleModule V A] (hA : Stacks.Ample.IsAmple V A)
    [IsIso (pullback.snd f j)] :
    ChowCycleMapRefinedGysinFormulaAt f j R hf u m
      (fundamentalChowClass (fieldChowSituation ℂ) (V ↘ Spec (.of ℂ)) (m + 1 : ℕ)) := by
  have hD := isEffectiveCartierDivisor_ker_of_isRegularClosedImmersionOfCodim_one f hf
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of ℂ))
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian (V ↘ Spec (.of ℂ))
  have := hf.isFiniteLocallyFreeOfRank_conormalModule
  let π : V ⟶ X := inv (pullback.snd f j) ≫ pullback.fst f j
  have hπ : π ≫ f = j := by
    simp only [π, Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]
  have : π.IsOver (Spec (.of ℂ)) := ⟨by
    change inv (pullback.snd f j) ≫ (pullback f j ↘ Spec (.of ℂ)) = _
    rw [← comp_over (pullback.snd f j) (Spec (.of ℂ)), IsIso.inv_hom_id_assoc]⟩
  have sq : IsPullback (𝟙 V) π j f :=
    (IsPullback.of_iso_pullback (show CommSq π (𝟙 V) f j from ⟨by rw [hπ, Category.id_comp]⟩)
      (asIso (inv (pullback.snd f j))) rfl (by simp)).flip
  let e : V ⟶ pullback f j := sq.flip.isoPullback.hom
  have he₂ : e ≫ pullback.snd f j = 𝟙 V := by simp [e]
  have heS : e ≫ (pullback.fst f j ≫ X ↘ Spec (.of ℂ)) = V ↘ Spec (.of ℂ) :=
    isoPullback_hom_comp_structureMorphism (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
      (Y ↘ Spec (.of ℂ)) sq (comp_over f _) (V ↘ Spec (.of ℂ))
      (by rw [Category.id_comp, comp_over])
  have : e.IsOver (Spec (.of ℂ)) := ⟨heS⟩
  have hNX : Stacks.Ample.IsInvertibleModule X (dualSheaf (conormalModule f)) :=
    GenuineChern.isInvertible_of_rank_one _
  let N : V.Modules := (Scheme.Modules.pullback π).obj (dualSheaf (conormalModule f))
  have hdim : schemeDeltaDimension (fieldChowSituation ℂ) (j ≫ Y ↘ Spec (.of ℂ)) ≤
      (((m + 1 : ℕ) : ℤ) : EInt) := by
    rw [schemeDeltaDimension_eq_genericPoint, relativeDimension_genericPoint_eq ℂ _ hV.symm]
  set 𝒩 := VirtualNormalBundle.ofIsRegularImmersion f hf.isRegularImmersion with h𝒩
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} 𝒩.bundle (0 + 1) :=
    (inferInstance : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0}
      𝒩.bundle 1)
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0}
      (conormalModule (𝟙 V)) 0 :=
    Stacks.Chow.isFiniteLocallyFreeOfRank_zero_of_isZero
      _ (Stacks.Conormal.isZero_immersionConormalSheaf_of_isIso (𝟙 V))
  have hreg' : IsRegularImmersion (𝟙 V) :=
    Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_of_smooth (𝟙 V) (𝟙 V)
  have hcap := virtualNormalBundleClass_cap_fundamentalChowClass_excess (fieldChowSituation ℂ)
    (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) f (comp_over f _) 𝒩 0 1
    (c := regularNormalGysinClass (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ))
      f (comp_over f _) hf)
    (isVirtualNormalBundleClass_virtualNormalBundleClass (fieldChowSituation ℂ) _ _ f _ 𝒩 (0 + 1))
    j (𝟙 V) π sq (V ↘ Spec (.of ℂ)) (by rw [Category.id_comp, comp_over]) hreg' _ hdim
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0}
      (𝒩.baseChange f (𝟙 V) π j sq).bundle (0 + 1) :=
    isFiniteLocallyFreeOfRank_modulePullback π 𝒩.bundle (0 + 1) inferInstance
  have := (𝒩.baseChange f (𝟙 V) π j sq).isFiniteLocallyFreeOfRank_excessNormalSheaf_of_add 0 1
  have hchow : chowGroupCongrDegree (fieldChowSituation ℂ) (pullback.fst f j ≫ X ↘ Spec (.of ℂ))
      (natCast_add_sub_natCast m 1)
      ((regularNormalGysinClass (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) f
          (comp_over f _) hf).cap j ((m + 1 : ℕ) : ℤ)
        (chowGroupCongr (fieldChowSituation ℂ) (q := V ↘ Spec (.of ℂ))
          (q' := j ≫ Y ↘ Spec (.of ℂ)) (comp_over j _).symm ((m + 1 : ℕ) : ℤ)
          (fundamentalChowClass (fieldChowSituation ℂ) (V ↘ Spec (.of ℂ)) (m + 1 : ℕ)))) =
      chowPushforwardOfIso (fieldChowSituation ℂ) (V ↘ Spec (.of ℂ))
        (pullback.fst f j ≫ X ↘ Spec (.of ℂ)) e heS (m : ℤ)
        (firstChernClassCapChow (fieldChowSituation ℂ) (m : ℤ) (V ↘ Spec (.of ℂ)) N
          (fundamentalChowClass (fieldChowSituation ℂ) (V ↘ Spec (.of ℂ)) (m + 1 : ℕ))) := by
    rw [chowGroupCongr_fundamentalChowClass, hcap,
      GenuineChern.chernCap_congr (fieldChowSituation ℂ) (V ↘ Spec (.of ℂ)) 1
        (excessNormalSheafIsoOfIdentity f hf.isRegularImmersion π j sq)]
    refine eq_of_heq ((chowGroupCongrDegree_heq' _ _ _).trans
      (chowPushforwardOfIso_heq_congr_base (fieldChowSituation ℂ) _ _ rfl _ _ rfl rfl
        (by push_cast; ring) _ _ ?_))
    refine (chowGroupDegreeEquiv_heq (fieldChowSituation ℂ) _ _ _).trans ?_
    rw [show (Fin.last 1 : Fin (1 + 1)) = 1 from rfl, GenuineChern.chernCap_one_eq_invCap,
      ← GenuineChern.firstChernClassCapChow_eq_invCap]
    have hNinv : AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj
        V.ringCatSheaf.property N := GenuineChern.isInvertible_of_rank_one _
    refine GenuineChern.firstChernClassCapChow_heq (C := fieldChowSituation ℂ)
      (V ↘ Spec (.of ℂ)) N (d₁ := ((m + 1 : ℕ) : ℤ) - ((0 : ℕ) : ℤ) - 1) (d₂ := (m : ℤ)) ?_ ?_
    · push_cast; ring
    · exact (chowGroupCast_heq' _ _ _).trans
        (fundamentalChowClass_heq_of_degree_eq _ (by push_cast; ring))
  have hcl : chowCycleClass R m (firstChernClassCapChow (fieldChowSituation ℂ) (m : ℤ)
        (V ↘ Spec (.of ℂ)) N
        (fundamentalChowClass (fieldChowSituation ℂ) (V ↘ Spec (.of ℂ)) (m + 1 : ℕ))) =
      firstChernClassTopCap R N m (chowCycleClass R (m + 1)
        (fundamentalChowClass (fieldChowSituation ℂ) (V ↘ Spec (.of ℂ)) (m + 1 : ℕ))) :=
    chowCycleClass_firstChernClassCap R N m A hA _
  have hfreeC : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{0, 0, 0}
      (conormalModule f) :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1
  have hfreeD : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{0, 0, 0}
      (dualSheaf (conormalModule f)) :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1
  have := isIso_toDoubleDual_of_isFiniteLocallyFree (conormalModule f) hfreeC
  have hjπ : TopCat.ofHom (UnderlyingSpace.map (K := ℂ) π) ≫
      TopCat.ofHom (UnderlyingSpace.map (K := ℂ) f) =
        TopCat.ofHom (UnderlyingSpace.map (K := ℂ) j) :=
    ConcreteCategory.hom_ext _ _ fun p ↦ UnderlyingSpace.ext (by
      change (p.toHom ≫ π) ≫ f = p.toHom ≫ j
      rw [Category.assoc, hπ])
  have htop : (cohomologyWithSupports.toCohomology R (ModuleCat.of R R)
        (TopCat.of (UnderlyingSpace ℂ V))
        ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) j)).hom ⁻¹'
          range (UnderlyingSpace.map (K := ℂ) f)) ((2 * 1 : ℕ) : ℤ)).hom
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
          (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) j)) _ _).hom u) =
      firstChernClassTop R N := by
    rw [toCohomology_pullback_comp R _ _ _ hjπ, forget_pullback_eq_topFirstChernClass f R hf hu,
      pullback_topFirstChernClass, firstChernClassTop]
    exact topFirstChernClass_congr R
      ((Scheme.Modules.pullback π).mapIso
        ((conormalModuleIsoPullbackDivisorDualSheaf f).symm ≪≫
          asIso (toDoubleDual (conormalModule f))) ≪≫
        Stacks.FundamentalGroup.pullbackDualSheafIso π (dualSheaf (conormalModule f)) hfreeD)
  set S := (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) j)).hom ⁻¹'
    range (UnderlyingSpace.map (K := ℂ) f) with hSdef
  have hS : IsClosed S :=
    (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) f).isClosed_range.preimage
      (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) j)).hom.continuous
  have hι := borelMooreHomology.isProperMap_subsetInclusion hS
  have hh : IsProperMap (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) e) ≫
      fibreSquarePointsHom (IsPullback.of_hasPullback f j).flip) :=
    (isProperMap_fibreSquarePointsHom (IsPullback.of_hasPullback f j).flip).comp
      (isProperMap_map (K := ℂ) e)
  have hid₁ : borelMooreHomology.subsetInclusion S ≫
      (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) e) ≫
        fibreSquarePointsHom (IsPullback.of_hasPullback f j).flip) = 𝟙 _ :=
    ConcreteCategory.hom_ext _ _ fun q ↦ Subtype.ext (UnderlyingSpace.ext (by
      change (q.1.toHom ≫ e) ≫ pullback.snd f j = q.1.toHom
      rw [Category.assoc, he₂, Category.comp_id]))
  have hid₂ : TopCat.ofHom (UnderlyingSpace.map (K := ℂ) e) ≫
      fibreSquarePointsHom (IsPullback.of_hasPullback f j).flip ≫
        borelMooreHomology.subsetInclusion S = 𝟙 _ :=
    ConcreteCategory.hom_ext _ _ fun p ↦ UnderlyingSpace.ext (by
      change (p.toHom ≫ e) ≫ pullback.snd f j = p.toHom
      rw [Category.assoc, he₂, Category.comp_id])
  have hinj : Function.Injective (borelMooreHomology.pushforward R (ModuleCat.of R R)
      (borelMooreHomology.subsetInclusion S) hι (2 * m : ℕ)).hom := by
    intro a b hab
    have key : ∀ c, (borelMooreHomology.pushforward R (ModuleCat.of R R) _ hh (2 * m : ℕ)).hom
        ((borelMooreHomology.pushforward R (ModuleCat.of R R) _ hι (2 * m : ℕ)).hom c) = c := by
      intro c
      rw [← ModuleCat.comp_apply, ← borelMooreHomology.pushforward_comp,
        borelMooreHomology.pushforward_congr_hom R hid₁ _ (by simp),
        borelMooreHomology.pushforward_id]
      rfl
    rw [← key a, ← key b, hab]
  unfold ChowCycleMapRefinedGysinFormulaAt
  rw [hchow, chowPushforwardOfIso]
  erw [chowCycleClass_properChowPushforward R e]
  rw [hcl]
  apply hinj
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← borelMooreHomology.pushforward_comp,
    ← borelMooreHomology.pushforward_comp,
    borelMooreHomology.pushforward_congr_hom R hid₂ _ (by simp),
    borelMooreHomology.pushforward_id, borelMooreHomology.pushforward_congrDegree,
    borelMooreHomology.capProductSupportPullback_apply,
    borelMooreHomology.pushforward_subsetInclusion_capProductSupport,
    ← borelMooreHomology.capProduct_toCohomology, htop]
  rfl

end Excess

end MMP.Chow
