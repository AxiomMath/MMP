module
public import MMP.AlgebraicGeometry.Intersection.PairingSeparation
public import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
public import MMP.AlgebraicGeometry.ChowForm.FibreDegreeRank
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.LimitDescent
public import StacksFrontier.AlgebraicGeometry.FieldExtensionDescent.InvertibleDescent
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.FieldExtension
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafMul
/-!
# Numerical divisor classes are unchanged by algebraically closed base extension

Let `k₀ ⊆ K` be algebraically closed fields and `X₀` a projective variety over `k₀`, with base
change `X = X₀ ×_{k₀} K` and projection `π : X ⟶ X₀`. Pulling Cartier divisors back along the
flat morphism `π` descends to numerical classes and gives an isomorphism of real vector spaces
`N¹(X₀)_ℝ ≅ N¹(X)_ℝ`, `[D₀] ↦ [π^* D₀]`.

## Main results

* `MMP.Fourfold.numericalDivisorClassesBaseChange`: the base-change isomorphism
  `N¹(X₀)_ℝ ≃ₗ[ℝ] N¹(X)_ℝ`.
* `MMP.Fourfold.numericalDivisorClassesBaseChange_eq_of_isPullback`: it sends the class of every
  Cartier divisor on `X₀` to the class of its pull-back.

## Implementation notes

The base change is any pullback square `X ⟶ X₀`, `X ⟶ Spec K` over `Spec K ⟶ Spec k₀`, rather
than the chosen fibre product. The isomorphism is characterised by sending the class of each
Cartier divisor `D₀` on `X₀` to the class of its pull-back `D` (`MMP.Intersection.IsPullback`);
since the classes of Cartier divisors span `N¹(X₀)_ℝ` and every Cartier divisor on `X₀` has a
pull-back along the flat `π`, this determines it.

## References

* [KM98] Kollár, Mori, *Birational Geometry of Algebraic Varieties*.
-/

namespace MMP.Fourfold

open CategoryTheory AlgebraicGeometry MMP.Mori

universe u

section CurveLemmas

variable {k : Type u} [Field k] {X C : Scheme.{u}}

/-- The intersection number of a proper curve with a Cartier divisor is the degree of its sheaf. -/
private theorem intersectionNumber_cycle_ofCartier {sX : X ⟶ Spec (.of k)} (C : ProperCurve sX)
    (E : X.CartierDivisor) :
    (C.cycle ℝ).intersectionNumber (KCartierDivisor.ofCartier ℝ E) =
      (degreeOn k sX C.ι C.dim_le (MMP.CartierDivisor.sheaf E) : ℝ) := by
  rw [OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree, OneCycle.degree_cycle]
  rfl

/-- The kernel of a closed immersion from a reduced scheme is the vanishing ideal of its range. -/
private theorem ker_eq_vanishingIdeal_of_isReduced {Y X : Scheme.{u}} (ι : Y ⟶ X)
    [IsClosedImmersion ι] [IsReduced Y] (Z : TopologicalSpace.Closeds X)
    (hZ : (Z : Set X) = Set.range ι) :
    ι.ker = Scheme.IdealSheafData.vanishingIdeal Z := by
  have hrad : ι.ker.radical = ι.ker := by
    refine Scheme.IdealSheafData.ext (funext fun U => ?_)
    simp only [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
    refine le_antisymm (fun x ⟨n, hn⟩ => ?_) Ideal.le_radical
    rw [RingHom.mem_ker, map_pow] at hn
    rw [RingHom.mem_ker]
    exact IsReduced.eq_zero _ ⟨n, hn⟩
  have : ι.ker.support = Z := TopologicalSpace.Closeds.ext <| by
    rw [Scheme.Hom.support_ker, ι.isClosedEmbedding.isClosed_range.closure_eq, hZ]
  rw [← this, Scheme.IdealSheafData.vanishingIdeal_support, hrad]

/-- A closed immersion from an integral scheme is the closed immersion of the closure of the image
of the generic point, up to isomorphism. -/
private theorem exists_iso_curveSubschemeAt {Y X : Scheme.{u}} [IsIntegral Y] (ι : Y ⟶ X)
    [IsClosedImmersion ι] :
    ∃ e : Y ≅ curveSubschemeAt (ι (genericPoint Y)), e.hom ≫ curveSubschemeAtι _ = ι := by
  have hrange : Set.range ι = closure {ι (genericPoint Y)} := by
    rw [← Set.image_singleton, ι.isClosedEmbedding.closure_image_eq,
      (genericPoint_spec Y).def]
    simp
  have hker : ι.ker = (curveSubschemeAtι (ι (genericPoint Y))).ker := by
    rw [ker_eq_vanishingIdeal_of_isReduced ι (TopologicalSpace.Closeds.closure
      {ι (genericPoint Y)}) hrange.symm]
    unfold curveSubschemeAtι
    rw [Scheme.IdealSheafData.ker_subschemeι]
  have hf : IsIso (IsClosedImmersion.lift (curveSubschemeAtι (ι (genericPoint Y))) ι hker.ge) :=
    IsClosedImmersion.isIso_of_ker_eq ι (curveSubschemeAtι _) _
      (IsClosedImmersion.lift_fac _ _ _) hker
  exact ⟨asIso (IsClosedImmersion.lift (curveSubschemeAtι (ι (genericPoint Y))) ι hker.ge),
    IsClosedImmersion.lift_fac _ _ _⟩

end CurveLemmas

section EulerAcrossPoints

open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic CategoryTheory.Limits

/-- An invertible module on a scheme flat over `S` is flat over `S`. -/
private theorem isFlatOver_of_isInvertibleModule' {X S : Scheme.{u}} (π : X ⟶ S) [Flat π]
    (F : X.Modules) [Stacks.Ample.IsInvertibleModule X F] :
    IsFlatOver π.toLRSHom.toShHom F := by
  have h0 : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 F :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      X.presheaf _ _).mp ‹_›
  have : F.IsQuasicoherent := Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule F
  have hflf : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F :=
    (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry F).mp
      (@Stacks.Divisors.isFiniteLocallyFree_of_isInvertible _ F h0)
  obtain ⟨-, hfree⟩ :=
    ((Stacks.FiniteLocallyFree.ModuleTFAE.finiteLocallyFree_tfae F).out 4 2).mp hflf
  intro x
  letI := (π.stalkMap x).hom.toAlgebra
  have : Module.Flat (S.presheaf.stalk (π x)) (X.presheaf.stalk x) := Flat.stalkMap π x
  have := hfree x
  letI : Module (S.presheaf.stalk (π x)) (F.presheaf.stalk x) :=
    Module.compHom _ (π.stalkMap x).hom
  have : IsScalarTower (S.presheaf.stalk (π x)) (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Flat (X.presheaf.stalk x) (F.presheaf.stalk x) := Module.Flat.of_free
  exact Module.Flat.trans (S.presheaf.stalk (π x)) (X.presheaf.stalk x) (F.presheaf.stalk x)

/-- The fibre Euler characteristic of an invertible module in a flat proper family of finite
presentation over a connected base is independent of the point. -/
private theorem fibreEulerCharacteristic_eq_of_connected {W S : Scheme.{u}} (f : W ⟶ S) [Flat f]
    [IsProper f] [LocallyOfFinitePresentation f] [ConnectedSpace S]
    (F : W.Modules) [Stacks.Ample.IsInvertibleModule W F] (s s' : S) :
    fibreEulerCharacteristic f F s = fibreEulerCharacteristic f F s' := by
  have h := (MMP.fibreEulerCharacteristic_tensorPowModule_eq f F).1 1 s s'
  have e : ∀ t, fibreEulerCharacteristic f (Stacks.Ample.tensorPowModule W F 1) t =
      fibreEulerCharacteristic f F t := fun t =>
    eulerSum_congr _ _ ((Scheme.Modules.pullback (f.fiberι t)).mapIso
      (Stacks.Ample.tensorPowModuleOneIso W F))
  rwa [e, e] at h

/-- **Euler characteristics at two field-valued points of a connected base agree.** Let
`f : W ⟶ S` be flat, proper and of finite presentation over a connected `S` and `F` an invertible
module on `W`. For two field-valued points `p_i : Spec k_i ⟶ S` with base changes
`q_i : Y_i ⟶ W`, `χ(Y_1, q_1^* F) = χ(Y_2, q_2^* F)`. -/
private theorem eulerSum_eq_of_isPullback {W S : Scheme.{u}} (f : W ⟶ S) [Flat f] [IsProper f]
    [LocallyOfFinitePresentation f] [ConnectedSpace S]
    (F : W.Modules) [Stacks.Ample.IsInvertibleModule W F]
    {k₁ k₂ : Type u} [Field k₁] [Field k₂] (p₁ : Spec (.of k₁) ⟶ S) (p₂ : Spec (.of k₂) ⟶ S)
    {Y₁ Y₂ : Scheme.{u}} (q₁ : Y₁ ⟶ W) (g₁ : Y₁ ⟶ Spec (.of k₁)) (q₂ : Y₂ ⟶ W)
    (g₂ : Y₂ ⟶ Spec (.of k₂)) (h₁ : IsPullback q₁ g₁ f p₁) (h₂ : IsPullback q₂ g₂ f p₂) :
    eulerSum k₁ g₁ ((Scheme.Modules.pullback q₁).obj F) =
      eulerSum k₂ g₂ ((Scheme.Modules.pullback q₂).obj F) := by
  have hfp : FinitePresentation f :=
    ⟨inferInstance, inferInstanceAs (QuasiCompact f),
      @IsSeparated.instQuasiSeparated _ _ f IsProper.toIsSeparated⟩
  have hF : SheafOfModules.IsFinitePresentation F :=
    @Stacks.Divisors.isFinitePresentation_of_isInvertible _ F
      ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
        W.presheaf _ _).mp ‹_›)
  have hflat := isFlatOver_of_isInvertibleModule' f F
  have key : ∀ {k : Type u} [Field k] (p : Spec (.of k) ⟶ S) {Y : Scheme.{u}} (q : Y ⟶ W)
      (g : Y ⟶ Spec (.of k)) (h : IsPullback q g f p) (pt : Spec (.of k)),
      eulerSum k g ((Scheme.Modules.pullback q).obj F) = fibreEulerCharacteristic f F (p pt) := by
    intro k _ p Y q g h pt
    rw [← chiDerivedFibre_eq_eulerSum f hfp F hF hflat k p q g h pt,
      congrFun (fibreEulerCharacteristic_eq_chiDerivedFibre f hfp F hF hflat) (p pt)]
  rw [key p₁ q₁ g₁ h₁ (IsLocalRing.closedPoint k₁), key p₂ q₂ g₂ h₂ (IsLocalRing.closedPoint k₂)]
  exact fibreEulerCharacteristic_eq_of_connected f F _ _

/-- **Degrees at two field-valued points of a connected base agree.** In the situation of
`eulerSum_eq_of_isPullback`, if both base changes have dimension at most one, the degrees of
`q_i^* F` on them agree. -/
private theorem invertibleCurveDegree_eq_of_isPullback {W S : Scheme.{u}} (f : W ⟶ S) [Flat f]
    [IsProper f] [LocallyOfFinitePresentation f] [ConnectedSpace S]
    (F : W.Modules) [Stacks.Ample.IsInvertibleModule W F]
    {k₁ k₂ : Type u} [Field k₁] [Field k₂] (p₁ : Spec (.of k₁) ⟶ S) (p₂ : Spec (.of k₂) ⟶ S)
    {Y₁ Y₂ : Scheme.{u}} (q₁ : Y₁ ⟶ W) (g₁ : Y₁ ⟶ Spec (.of k₁)) (q₂ : Y₂ ⟶ W)
    (g₂ : Y₂ ⟶ Spec (.of k₂)) (h₁ : IsPullback q₁ g₁ f p₁) (h₂ : IsPullback q₂ g₂ f p₂)
    [IsProper g₁] [IsProper g₂] (hdim₁ : topologicalKrullDim Y₁ ≤ 1)
    (hdim₂ : topologicalKrullDim Y₂ ≤ 1)
    [SheafOfModules.IsInvertible Y₁.presheaf Y₁.ringCatSheaf.2
      ((Scheme.Modules.pullback q₁).obj F)]
    [SheafOfModules.IsInvertible Y₂.presheaf Y₂.ringCatSheaf.2
      ((Scheme.Modules.pullback q₂).obj F)] :
    invertibleCurveDegree k₁ g₁ hdim₁ ((Scheme.Modules.pullback q₁).obj F) =
      invertibleCurveDegree k₂ g₂ hdim₂ ((Scheme.Modules.pullback q₂).obj F) := by
  have e₁ := eulerSum_eq_of_isPullback f F p₁ p₂ q₁ g₁ q₂ g₂ h₁ h₂
  have e₂ := eulerSum_eq_of_isPullback f (SheafOfModules.unit W.ringCatSheaf) p₁ p₂ q₁ g₁ q₂ g₂
    h₁ h₂
  have u₁ : eulerSum k₁ g₁ ((Scheme.Modules.pullback q₁).obj (SheafOfModules.unit W.ringCatSheaf)) =
      eulerSum k₁ g₁ (SheafOfModules.unit Y₁.ringCatSheaf) :=
    eulerSum_congr k₁ g₁ (Scheme.Modules.pullbackUnitIso q₁)
  have u₂ : eulerSum k₂ g₂ ((Scheme.Modules.pullback q₂).obj (SheafOfModules.unit W.ringCatSheaf)) =
      eulerSum k₂ g₂ (SheafOfModules.unit Y₂.ringCatSheaf) :=
    eulerSum_congr k₂ g₂ (Scheme.Modules.pullbackUnitIso q₂)
  rw [u₁, u₂] at e₂
  change eulerSum k₁ g₁ _ - eulerSum k₁ g₁ _ = eulerSum k₂ g₂ _ - eulerSum k₂ g₂ _
  rw [e₁, e₂]

/-- **A constant family has constant Euler characteristic.** Let `S` be a connected scheme over
`k₀`, `M` an invertible module on `X₀ ×_{k₀} S`, and `Y` a proper `k₀`-scheme with a morphism
`y : Y ⟶ X₀`. For two `k₀`-points `τ, τ'` of `S`, the Euler characteristics of the pull-backs of
`M` along `(y, τ)` and `(y, τ')` agree. -/
private theorem eulerSum_constantFamily {k₀ : Type u} [Field k₀] {S X₀ Y : Scheme.{u}}
    (gS : S ⟶ Spec (.of k₀)) (s₀ : X₀ ⟶ Spec (.of k₀)) [ConnectedSpace S]
    (M : (pullback gS s₀).Modules)
    [SheafOfModules.IsInvertible (pullback gS s₀).presheaf (pullback gS s₀).ringCatSheaf.2 M]
    (gY : Y ⟶ Spec (.of k₀)) [IsProper gY] (y : Y ⟶ X₀) (hy : y ≫ s₀ = gY)
    (τ τ' : Spec (.of k₀) ⟶ S) (hτ : τ ≫ gS = 𝟙 _) (hτ' : τ' ≫ gS = 𝟙 _) :
    eulerSum k₀ gY ((Scheme.Modules.pullback (pullback.lift (gY ≫ τ) y (by
        rw [Category.assoc, hτ, Category.comp_id, hy]))).obj M) =
      eulerSum k₀ gY ((Scheme.Modules.pullback (pullback.lift (gY ≫ τ') y (by
        rw [Category.assoc, hτ', Category.comp_id, hy]))).obj M) := by
  classical
  have hflat : Flat gY := inferInstance
  have hlf : LocallyOfFinitePresentation gY :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr
      (inferInstance : IsProper gY).toLocallyOfFiniteType
  let fS : pullback gY gS ⟶ S := pullback.snd gY gS
  have hP : IsPullback (pullback.fst gY gS) fS gY gS := IsPullback.of_hasPullback gY gS
  have hfl : Flat fS := MorphismProperty.of_isPullback (P := @Flat) hP hflat
  have hpr : IsProper fS := MorphismProperty.of_isPullback (P := @IsProper) hP ‹IsProper gY›
  let w : pullback gY gS ⟶ pullback gS s₀ :=
    pullback.lift fS (pullback.fst gY gS ≫ y) (by rw [Category.assoc, hy, ← pullback.condition])
  let F : (pullback gY gS).Modules := (Scheme.Modules.pullback w).obj M
  have hFi : SheafOfModules.IsInvertible (pullback gY gS).presheaf
      (pullback gY gS).ringCatSheaf.2 F :=
    inferInstance
  haveI : Stacks.Ample.IsInvertibleModule (pullback gY gS) F :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      (pullback gY gS).presheaf _ _).mpr hFi
  have key : ∀ (τ : Spec (.of k₀) ⟶ S) (hτ : τ ≫ gS = 𝟙 _),
      ∃ q : Y ⟶ pullback gY gS, IsPullback q gY fS τ ∧ q ≫ w = pullback.lift (gY ≫ τ) y (by
        rw [Category.assoc, hτ, Category.comp_id, hy]) := by
    intro τ hτ
    let q : Y ⟶ pullback gY gS := pullback.lift (𝟙 Y) (gY ≫ τ) (by
      rw [Category.assoc, hτ, Category.comp_id, Category.id_comp])
    have hq1 : q ≫ pullback.fst gY gS = 𝟙 Y := pullback.lift_fst _ _ _
    have hq2 : q ≫ fS = gY ≫ τ := pullback.lift_snd _ _ _
    have hw1 : w ≫ pullback.fst gS s₀ = fS := pullback.lift_fst _ _ _
    have hw2 : w ≫ pullback.snd gS s₀ = pullback.fst gY gS ≫ y := pullback.lift_snd _ _ _
    refine ⟨q, ?_, ?_⟩
    · refine IsPullback.of_right (h₁₁ := q) (h₁₂ := pullback.fst gY gS) (v₁₁ := gY)
        (v₁₂ := fS) (v₁₃ := gY) (h₂₁ := τ) (h₂₂ := gS) ?_ hq2 hP
      rw [hq1, hτ]
      exact IsPullback.of_horiz_isIso ⟨by simp⟩
    · apply pullback.hom_ext
      · rw [Category.assoc, hw1, hq2, pullback.lift_fst]
      · rw [Category.assoc, hw2, ← Category.assoc, hq1, Category.id_comp, pullback.lift_snd]
  obtain ⟨q, hq, hqw⟩ := key τ hτ
  obtain ⟨q', hq', hqw'⟩ := key τ' hτ'
  have e := eulerSum_eq_of_isPullback fS F τ τ' q gY q' gY hq hq'
  have e1 := eulerSum_congr k₀ gY
    ((Scheme.Modules.pullbackComp q w).app M ≪≫ (Scheme.Modules.pullbackCongr hqw).app M)
  have e2 := eulerSum_congr k₀ gY
    ((Scheme.Modules.pullbackComp q' w).app M ≪≫ (Scheme.Modules.pullbackCongr hqw').app M)
  exact e1.symm.trans (e.trans e2)

/-- **Euler characteristics along a spread-out family.** Let `f : W ⟶ S` be a flat proper family
of finite presentation over a connected `S` over `k₀`, with a morphism `u : W ⟶ X₀` over `k₀`, and
let `M` be an invertible module on `X₀ ×_{k₀} S₁` for a connected `S₁` under `S`, with two
`k₀`-points `τ` of `S` and `τ₀` of `S₁`. For `v = (f, u) : W ⟶ X₀ ×_{k₀} S₁` and
`σ₀ = (τ₀, 𝟙) : X₀ ⟶ X₀ ×_{k₀} S₁`
the pull-backs of `M` along `v` and `u ≫ σ₀` have the same Euler characteristic on every fibre of
`f` over a field-valued point of `S`. -/
private theorem eulerSum_spread_eq {k₀ : Type u} [Field k₀] {X₀ S S₁ W C' : Scheme.{u}}
    (s₀ : X₀ ⟶ Spec (.of k₀)) (g₁ : S₁ ⟶ Spec (.of k₀)) (g : S ⟶ Spec (.of k₀)) (r : S ⟶ S₁)
    (hr : r ≫ g₁ = g) [ConnectedSpace S] [ConnectedSpace S₁]
    (M : (pullback g₁ s₀).Modules)
    [SheafOfModules.IsInvertible (pullback g₁ s₀).presheaf (pullback g₁ s₀).ringCatSheaf.2 M]
    (τ : Spec (.of k₀) ⟶ S) (hτ : τ ≫ g = 𝟙 _) (τ₀ : Spec (.of k₀) ⟶ S₁) (hτ₀ : τ₀ ≫ g₁ = 𝟙 _)
    (f : W ⟶ S) [Flat f] [IsProper f] [LocallyOfFinitePresentation f] (u : W ⟶ X₀)
    (hu : u ≫ s₀ = f ≫ g)
    (v : W ⟶ pullback g₁ s₀) (hv₁ : v ≫ pullback.fst g₁ s₀ = f ≫ r)
    (hv₂ : v ≫ pullback.snd g₁ s₀ = u)
    (σ₀ : X₀ ⟶ pullback g₁ s₀) (hσ₁ : σ₀ ≫ pullback.fst g₁ s₀ = s₀ ≫ τ₀)
    (hσ₂ : σ₀ ≫ pullback.snd g₁ s₀ = 𝟙 _)
    {k : Type u} [Field k] (p : Spec (.of k) ⟶ S) (j : C' ⟶ W) (φ : C' ⟶ Spec (.of k))
    (hpb : IsPullback j φ f p) :
    eulerSum k φ ((Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback v).obj M)) =
      eulerSum k φ ((Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback u).obj
        ((Scheme.Modules.pullback σ₀).obj M))) := by
  classical
  let F₁ : W.Modules := (Scheme.Modules.pullback v).obj M
  let F₂ : W.Modules := (Scheme.Modules.pullback u).obj ((Scheme.Modules.pullback σ₀).obj M)
  have hF₁ : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 F₁ := inferInstance
  have hF₂ : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 F₂ := inferInstance
  haveI : Stacks.Ample.IsInvertibleModule W F₁ :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      W.presheaf _ _).mpr hF₁
  haveI : Stacks.Ample.IsInvertibleModule W F₂ :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      W.presheaf _ _).mpr hF₂
  let Y : Scheme.{u} := pullback f τ
  let qY : Y ⟶ W := pullback.fst f τ
  let gY : Y ⟶ Spec (.of k₀) := pullback.snd f τ
  have hY : IsPullback qY gY f τ := IsPullback.of_hasPullback f τ
  have hqf : qY ≫ f = gY ≫ τ := hY.w
  have hy : (qY ≫ u) ≫ s₀ = gY := by
    rw [Category.assoc, hu, ← Category.assoc, hqf, Category.assoc, hτ, Category.comp_id]
  have e₁ := eulerSum_eq_of_isPullback f F₁ p τ j φ qY gY hpb hY
  have e₂ := eulerSum_eq_of_isPullback f F₂ p τ j φ qY gY hpb hY
  have hτ₁ : (τ ≫ r) ≫ g₁ = 𝟙 _ := by rw [Category.assoc, hr, hτ]
  have hm₁ : qY ≫ v = pullback.lift (gY ≫ (τ ≫ r)) (qY ≫ u) (by
      rw [Category.assoc, hτ₁, Category.comp_id, hy]) := by
    apply pullback.hom_ext
    · rw [Category.assoc, hv₁, ← Category.assoc, hqf, Category.assoc, pullback.lift_fst]
    · rw [Category.assoc, hv₂, pullback.lift_snd]
  have hm₂ : qY ≫ u ≫ σ₀ = pullback.lift (gY ≫ τ₀) (qY ≫ u) (by
      rw [Category.assoc, hτ₀, Category.comp_id, hy]) := by
    apply pullback.hom_ext
    · have hy' : qY ≫ u ≫ s₀ = gY := by rw [← Category.assoc, hy]
      rw [Category.assoc, Category.assoc, hσ₁, pullback.lift_fst, ← hy']
      simp only [Category.assoc]
    · rw [Category.assoc, Category.assoc, hσ₂, Category.comp_id, pullback.lift_snd]
  have e₃ := eulerSum_constantFamily g₁ s₀ M gY (qY ≫ u) hy (τ ≫ r) τ₀ hτ₁ hτ₀
  have c₁ := eulerSum_congr k₀ gY
    ((Scheme.Modules.pullbackComp qY v).app M ≪≫ (Scheme.Modules.pullbackCongr hm₁).app M)
  have c₂ := eulerSum_congr k₀ gY
    (((Scheme.Modules.pullbackComp qY u).app ((Scheme.Modules.pullback σ₀).obj M)) ≪≫
      (Scheme.Modules.pullbackComp (qY ≫ u) σ₀).app M ≪≫
      (Scheme.Modules.pullbackCongr (by rw [Category.assoc, hm₂])).app M)
  exact e₁.trans (c₁.trans (e₃.trans (c₂.symm.trans e₂.symm)))

end EulerAcrossPoints

section SheafPullback

open MMP.Intersection
open MMP.CartierDivisorSheaf Opposite
  TopologicalSpace

section KModel

variable {X : Scheme.{u}} [IsIntegral X]

private noncomputable def ιK (U : X.Opens) :
    X.functionField →+* X.totalQuotientSheaf.obj.obj (op U) :=
  ((functionFieldToTotalQuotientSheaf X).app (op U)).hom

private theorem genericPoint_mem {U : X.Opens} (hU : (U : Set X).Nonempty) :
    genericPoint X ∈ U := by
  obtain ⟨x, hx⟩ := hU
  exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨x, Set.mem_univ _, hx⟩

private theorem ιK_germ (U : X.Opens) (h : genericPoint X ∈ U) (a : Γ(X, U)) :
    ιK U (X.presheaf.germ U (genericPoint X) h a) = toK U a :=
  functionFieldToTotalQuotientSheaf_germ X U a h

private theorem ιK_res {U V : X.Opens} (h : V ≤ U) (c : X.functionField) :
    resK h (ιK U c) = ιK V c :=
  (congrArg (fun φ => φ.hom c)
    ((functionFieldToTotalQuotientSheaf X).naturality (homOfLE h).op)).symm

private theorem ιK_injective (U : X.Opens) (hU : (U : Set X).Nonempty) :
    Function.Injective (ιK U) :=
  functionFieldToTotalQuotientSheaf_app_injective X U hU

private theorem ιK_surjective (U : X.Opens) (hU : (U : Set X).Nonempty) :
    Function.Surjective (ιK U) := by
  intro s
  have : Nonempty U := hU.to_subtype
  obtain ⟨a, ha⟩ := exists_eq_constantSheafOnSpace_section X X.functionField U inferInstance
    (((totalQuotientSheafIsoConstant X).val.hom.hom.app (op U)) s)
  refine ⟨a, ?_⟩
  change ((totalQuotientSheafIsoConstant X).val.inv.hom.app (op U))
    (((toSheafify (Opens.grothendieckTopology X)
      ((Functor.const (Opens X)ᵒᵖ).obj X.functionField)).app (op U)) a) = s
  rw [← ha]
  exact ConcreteCategory.congr_hom
    (congrArg (fun φ => φ.hom.app (op U)) (totalQuotientSheafIsoConstant X).val.hom_inv_id) s

end KModel

section Dominant

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (g : Y ⟶ X) [IsDominant g]

private theorem functionFieldMap_germ (U : X.Opens) (hU : genericPoint X ∈ U) (a : Γ(X, U))
    (hY : genericPoint Y ∈ g ⁻¹ᵁ U) :
    functionFieldMap g (X.presheaf.germ U (genericPoint X) hU a) =
      Y.presheaf.germ (g ⁻¹ᵁ U) (genericPoint Y) hY (g.app U a) := by
  have hx : g (genericPoint Y) ∈ U := hY
  have h1 := MMP.Mori.functionFieldMap_algebraMap_stalk g (genericPoint Y)
    (X.presheaf.germ U (g (genericPoint Y)) hx a)
  have hn : Nonempty U := ⟨⟨genericPoint X, hU⟩⟩
  have hn' : Nonempty (g ⁻¹ᵁ U) := ⟨⟨genericPoint Y, hY⟩⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (U := U) hx a] at h1
  erw [Scheme.Hom.germ_stalkMap_apply g U (genericPoint Y) hx a] at h1
  rw [Scheme.algebraMap_germ_eq_germToFunctionField (X := Y) (U := g ⁻¹ᵁ U) hY _] at h1
  exact h1

end Dominant

section LocalFraction

variable {Z : Scheme.{u}}

private theorem exists_local_fraction {D : Z.CartierDivisor} {x : Z} {U : Z.Opens} (hxU : x ∈ U)
    (A B : Γ(Z, U)) {e : Z.totalQuotientSheaf.presheaf.stalk x} (he : IsLocalEquationAt D x e)
    (hf : IsFraction e (Z.presheaf.germ U x hxU A) (Z.presheaf.germ U x hxU B)) :
    ∃ (U₀ : Z.Opens) (h₀ : U₀ ≤ U) (_ : x ∈ U₀) (f : (Z.totalQuotientSheaf.obj.obj (op U₀))ˣ),
      IsLocalEquationOn D U₀ f ∧
      toK U₀ (Z.presheaf.map (homOfLE h₀).op B) * (f : Z.totalQuotientSheaf.obj.obj (op U₀)) =
        toK U₀ (Z.presheaf.map (homOfLE h₀).op A) := by
  obtain ⟨U₁, hx₁, f₁, hf₁, rfl⟩ := he
  have h2 := hf.2
  rw [← germ_toTotalQuotient, ← germ_toTotalQuotient] at h2
  have hxW : x ∈ U ⊓ U₁ := ⟨hxU, hx₁⟩
  have e : Z.totalQuotientSheaf.presheaf.germ (U ⊓ U₁) x hxW
      (toK (U ⊓ U₁) (Z.presheaf.map (homOfLE inf_le_left).op B) * resK inf_le_right (f₁ : _)) =
      Z.totalQuotientSheaf.presheaf.germ (U ⊓ U₁) x hxW
        (toK (U ⊓ U₁) (Z.presheaf.map (homOfLE inf_le_left).op A)) := by
    rw [map_mul, ← resK_toK inf_le_left B, ← resK_toK inf_le_left A]
    erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply,
      TopCat.Presheaf.germ_res_apply]
    exact h2
  obtain ⟨U₀, hx₀, i, j, hij⟩ := Z.totalQuotientSheaf.presheaf.germ_eq x hxW hxW _ _ e
  have hij' : i = j := Subsingleton.elim _ _
  subst hij'
  refine ⟨U₀, i.le.trans inf_le_left, hx₀, MMP.Intersection.resUnit (i ≫ homOfLE inf_le_right) f₁,
    isLocalEquationOn_resUnit _ hf₁, ?_⟩
  have h3 : resK i.le (toK (U ⊓ U₁) (Z.presheaf.map (homOfLE inf_le_left).op B) *
      resK inf_le_right (f₁ : _)) =
        resK i.le (toK (U ⊓ U₁) (Z.presheaf.map (homOfLE inf_le_left).op A)) := hij
  rw [map_mul, ← resK_toK inf_le_left B, ← resK_toK inf_le_left A, resK_resK, resK_resK,
    resK_resK] at h3
  rw [← resK_toK _ B, ← resK_toK _ A]
  convert h3 using 2
  rfl

end LocalFraction

section Rho

private theorem subsingleton_totalQuotient_of_not_nonempty {Z : Scheme.{u}} {U : Z.Opens}
    (h : ¬ (U : Set Z).Nonempty) : Subsingleton (Z.totalQuotientSheaf.obj.obj (op U)) := by
  have : U = ⊥ := TopologicalSpace.Opens.coe_eq_empty.mp (Set.not_nonempty_iff_eq_empty.mp h)
  subst this
  exact CommRingCat.subsingleton_of_isTerminal
    (TopCat.Sheaf.isTerminalOfEmpty Z.totalQuotientSheaf)

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (g : Y ⟶ X) [IsDominant g]

omit [IsIntegral X] [IsIntegral Y] [IsDominant g] in
private theorem not_nonempty_preimage {U : X.Opens} (h : ¬ (U : Set X).Nonempty) :
    ¬ ((g ⁻¹ᵁ U : Y.Opens) : Set Y).Nonempty := by
  rintro ⟨y, hy⟩
  exact h ⟨g y, hy⟩

open Classical in
/-- The ring map `𝓜_X(U) → 𝓜_Y(g⁻¹U)` induced by the extension of function fields. -/
private noncomputable def rho (U : X.Opens) :
    X.totalQuotientSheaf.obj.obj (op U) →+* Y.totalQuotientSheaf.obj.obj (op (g ⁻¹ᵁ U)) :=
  if hU : (U : Set X).Nonempty then
    (ιK (g ⁻¹ᵁ U)).comp ((functionFieldMap g).comp
      (RingEquiv.ofBijective (ιK U) ⟨ιK_injective U hU, ιK_surjective U hU⟩).symm.toRingHom)
  else
    haveI := subsingleton_totalQuotient_of_not_nonempty (not_nonempty_preimage g hU)
    (default : _ →ₐ[ℤ] _).toRingHom

private theorem rho_ιK {U : X.Opens} (hU : (U : Set X).Nonempty) (κ : X.functionField) :
    rho g U (ιK U κ) = ιK (g ⁻¹ᵁ U) (functionFieldMap g κ) := by
  unfold rho
  simp only [hU, ↓reduceDIte, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom]
  have : (RingEquiv.ofBijective (ιK U) ⟨ιK_injective U hU, ιK_surjective U hU⟩).symm (ιK U κ) =
      κ :=
    (RingEquiv.ofBijective (ιK U) ⟨ιK_injective U hU, ιK_surjective U hU⟩).symm_apply_apply κ
  rw [this]

private theorem rho_res {U V : X.Opens} (h : V ≤ U) (σ : X.totalQuotientSheaf.obj.obj (op U)) :
    resK (g.preimage_mono h) (rho g U σ) = rho g V (resK h σ) := by
  by_cases hV : (V : Set X).Nonempty
  · have hU : (U : Set X).Nonempty := hV.mono h
    obtain ⟨κ, rfl⟩ := ιK_surjective U hU σ
    rw [rho_ιK g hU, ιK_res h, ιK_res (g.preimage_mono h), rho_ιK g hV]
  · have := subsingleton_totalQuotient_of_not_nonempty (not_nonempty_preimage g hV)
    exact Subsingleton.elim _ _

private theorem rho_toK (U : X.Opens) (a : Γ(X, U)) :
    rho g U (toK U a) = toK (g ⁻¹ᵁ U) (g.app U a) := by
  by_cases hU : (U : Set X).Nonempty
  · have hη : genericPoint X ∈ U := genericPoint_mem hU
    have hY : genericPoint Y ∈ g ⁻¹ᵁ U := genericPoint_mem (g.denseRange.exists_mem_open U.isOpen hU)
    rw [← ιK_germ U hη a, rho_ιK g hU, functionFieldMap_germ g U hη a hY, ιK_germ _ hY]
  · have := subsingleton_totalQuotient_of_not_nonempty (not_nonempty_preimage g hU)
    exact Subsingleton.elim _ _

end Rho

section Key

private theorem exists_common_rep_le {Z : Scheme.{u}} (x : Z) (W : Z.Opens) (hxW : x ∈ W)
    (a b : Z.presheaf.stalk x) :
    ∃ (U : Z.Opens) (_ : U ≤ W) (hx : x ∈ U) (A B : Γ(Z, U)),
      Z.presheaf.germ U x hx A = a ∧ Z.presheaf.germ U x hx B = b := by
  obtain ⟨U₁, hx₁, A₁, rfl⟩ := Z.presheaf.exists_germ_eq a
  obtain ⟨U₂, hx₂, B₂, rfl⟩ := Z.presheaf.exists_germ_eq b
  exact ⟨U₁ ⊓ U₂ ⊓ W, inf_le_right, ⟨⟨hx₁, hx₂⟩, hxW⟩,
    Z.presheaf.map (homOfLE (inf_le_left.trans inf_le_left)).op A₁,
    Z.presheaf.map (homOfLE (inf_le_left.trans inf_le_right)).op B₂,
    TopCat.Presheaf.germ_res_apply _ _ _ _ _, TopCat.Presheaf.germ_res_apply _ _ _ _ _⟩

private theorem mul_left_cancel_totalQuotient {Z : Scheme.{u}} [IsIntegral Z] {V : Z.Opens}
    (hV : (V : Set Z).Nonempty) {B x y : Z.totalQuotientSheaf.obj.obj (op V)} (hB : B ≠ 0)
    (h : B * x = B * y) : x = y := by
  obtain ⟨x', rfl⟩ := ιK_surjective V hV x
  obtain ⟨y', rfl⟩ := ιK_surjective V hV y
  obtain ⟨B', rfl⟩ := ιK_surjective V hV B
  have hB' : B' ≠ 0 := fun h0 => hB (by rw [h0, map_zero])
  have h' : B' * x' = B' * y' := ιK_injective V hV (by simpa only [map_mul] using h)
  rw [mul_left_cancel₀ hB' h']

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (g : Y ⟶ X) [IsDominant g]

/-- Local equations of a pull-back are the pulled-back local equations. -/
private theorem exists_local_pullback_equation {E : X.CartierDivisor} {E' : Y.CartierDivisor}
    (h : IsPullback g E E') (y : Y) (W : X.Opens) (hW : g y ∈ W) :
    ∃ (U₀ : X.Opens) (_ : U₀ ≤ W) (V : Y.Opens) (hV : V ≤ g ⁻¹ᵁ U₀) (_ : y ∈ V)
      (f₀ : (X.totalQuotientSheaf.obj.obj (op U₀))ˣ) (f' : (Y.totalQuotientSheaf.obj.obj (op V))ˣ),
      IsLocalEquationOn E U₀ f₀ ∧ IsLocalEquationOn E' V f' ∧
        resK hV (rho g U₀ (f₀ : X.totalQuotientSheaf.obj.obj (op U₀))) =
          (f' : Y.totalQuotientSheaf.obj.obj (op V)) := by
  obtain ⟨a, b, ⟨e, he, hf⟩, -, hb, e', he', hf'⟩ := h.2 y
  obtain ⟨U, hUW, hxU, A, B, rfl, rfl⟩ := exists_common_rep_le (g y) W hW a b
  obtain ⟨U₀, h₀, hx₀, f₀, hf₀, hAB⟩ := exists_local_fraction hxU A B he hf
  have hyU₀ : y ∈ g ⁻¹ᵁ U₀ := hx₀
  set A₀ := X.presheaf.map (homOfLE h₀).op A
  set B₀ := X.presheaf.map (homOfLE h₀).op B
  have hgA : X.presheaf.germ U₀ (g y) hx₀ A₀ = X.presheaf.germ U (g y) hxU A :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have hgB : X.presheaf.germ U₀ (g y) hx₀ B₀ = X.presheaf.germ U (g y) hxU B :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have hfr : IsFraction e' (Y.presheaf.germ (g ⁻¹ᵁ U₀) y hyU₀ (g.app U₀ A₀))
      (Y.presheaf.germ (g ⁻¹ᵁ U₀) y hyU₀ (g.app U₀ B₀)) := by
    rw [← Scheme.Hom.germ_stalkMap_apply g U₀ y hx₀, ← Scheme.Hom.germ_stalkMap_apply g U₀ y hx₀,
      hgA, hgB]
    exact hf'
  obtain ⟨V, h₁, hy₁, f', hf'', hAB'⟩ := exists_local_fraction hyU₀ _ _ he' hfr
  refine ⟨U₀, h₀.trans hUW, V, h₁, hy₁, f₀, f', hf₀, hf'', ?_⟩
  have hne : toK V (Y.presheaf.map (homOfLE h₁).op (g.app U₀ B₀)) ≠ 0 := by
    intro h0
    have h1 : Y.presheaf.map (homOfLE h₁).op (g.app U₀ B₀) = 0 :=
      MMP.Intersection.injective_toTotalQuotient V (by rw [h0, map_zero])
    have h2 : Y.presheaf.germ V y hy₁ (Y.presheaf.map (homOfLE h₁).op (g.app U₀ B₀)) =
        (g.stalkMap y).hom (X.presheaf.germ U (g y) hxU B) := by
      erw [TopCat.Presheaf.germ_res_apply]
      rw [← hgB]
      exact (Scheme.Hom.germ_stalkMap_apply g U₀ y hx₀ B₀).symm
    rw [h1, map_zero] at h2
    rw [← h2] at hb
    exact zero_notMem_nonZeroDivisors hb
  have e1 := congrArg (fun t => resK h₁ (rho g U₀ t)) hAB
  simp only [map_mul] at e1
  rw [rho_toK, rho_toK, resK_toK, resK_toK] at e1
  exact mul_left_cancel_totalQuotient ⟨y, hy₁⟩ hne (e1.trans hAB'.symm)

private theorem resK_rho_inv {U₀ : X.Opens} {V : Y.Opens} (hV : V ≤ g ⁻¹ᵁ U₀)
    {f₀ : (X.totalQuotientSheaf.obj.obj (op U₀))ˣ} {f' : (Y.totalQuotientSheaf.obj.obj (op V))ˣ}
    (hff : resK hV (rho g U₀ (f₀ : X.totalQuotientSheaf.obj.obj (op U₀))) =
      (f' : Y.totalQuotientSheaf.obj.obj (op V))) :
    resK hV (rho g U₀ (↑f₀⁻¹ : X.totalQuotientSheaf.obj.obj (op U₀))) =
      (↑f'⁻¹ : Y.totalQuotientSheaf.obj.obj (op V)) := by
  have hinv : resK hV (rho g U₀ (↑f₀⁻¹ : X.totalQuotientSheaf.obj.obj (op U₀))) *
      (f' : Y.totalQuotientSheaf.obj.obj (op V)) = 1 := by
    rw [← hff, ← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
  exact Units.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hinv)

/-- The pull-back of a section of `𝒪_X(E)` over `W` is a section of `𝒪_Y(E')` over `g⁻¹W`. -/
private theorem mem_rho {E : X.CartierDivisor} {E' : Y.CartierDivisor} (h : IsPullback g E E')
    (W : X.Opens) (s : X.totalQuotientSheaf.obj.obj (op W)) (hs : Mem E W s) :
    Mem E' (g ⁻¹ᵁ W) (rho g W s) := by
  refine Mem.of_locally fun y hy => ?_
  obtain ⟨U₀, hU₀, V, hV, hyV, f₀, f', hf₀, hf', hff⟩ := exists_local_pullback_equation g h y W hy
  refine ⟨V, hV.trans (g.preimage_mono hU₀), hyV, ?_⟩
  refine (mem_iff (U := V) (V := V) hf' le_rfl _).2 ?_
  obtain ⟨C, hC⟩ := (mem_iff (U := U₀) (V := U₀) hf₀ le_rfl _).1 (hs.res hU₀)
  refine ⟨Y.presheaf.map (homOfLE hV).op (g.app U₀ C), ?_⟩
  have e1 : resK (hV.trans (g.preimage_mono hU₀)) (rho g W s) =
      resK hV (rho g U₀ (resK hU₀ s)) := by
    rw [← rho_res g hU₀ s, resK_resK]
  rw [e1, ← hC, map_mul, map_mul, rho_toK, resK_toK]
  simp only [resK_id]
  rw [resK_rho_inv g hV hff]

private theorem epi_of_surjective_on_covering {Z : Scheme.{u}} (B : Z.Opens → Prop)
    (hB : ∀ (U : Z.Opens) (T : CategoryTheory.Sieve U),
      (∀ ⦃V : Z.Opens⦄ (f : V ⟶ U), B V → T f) → T ∈ Opens.grothendieckTopology Z U)
    {M N : Z.Modules} (φ : M ⟶ N)
    (hφ : ∀ V : Z.Opens, B V → Function.Surjective (φ.val.app (op V))) : Epi φ := by
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology Z)
      ((SheafOfModules.toSheaf Z.ringCatSheaf).map φ).hom :=
    ⟨fun s => hB _ _ fun V f hV => hφ V hV (N.val.map f.op s)⟩
  exact (SheafOfModules.toSheaf Z.ringCatSheaf).epi_of_epi_map (Sheaf.epi_of_isLocallySurjective _)

/-- The map `𝒪_X(E) ⟶ g_* 𝒪_Y(E')`, `s ↦ g^*s`. -/
private noncomputable def lambdaPre {E : X.CartierDivisor} {E' : Y.CartierDivisor}
    (h : IsPullback g E E') :
    (MMP.CartierDivisor.sheaf E).val ⟶
      ((Scheme.Modules.pushforward g).obj (MMP.CartierDivisor.sheaf E')).val :=
    (PresheafOfModules.homMk
      { app := fun U => AddCommGrpCat.ofHom
          { toFun := fun s => (⟨rho g U.unop (MMP.CartierDivisorSheaf.sectionVal s),
              mem_rho g h U.unop _ (show ↥((MMP.CartierDivisor.sheafSubmodule E).obj U) from s).2⟩ :
                ↥((MMP.CartierDivisor.sheafSubmodule E').obj (op (g ⁻¹ᵁ U.unop))))
            map_zero' := Subtype.ext (by change rho g U.unop 0 = 0; exact map_zero _)
            map_add' := fun s t => Subtype.ext (by
              exact map_add (rho g U.unop) _ _) }
        naturality := fun {U V} i => by
          ext s
          exact Subtype.ext (rho_res g i.unop.le _).symm }
      (fun U r s => Subtype.ext (by
        change rho g U.unop (toK U.unop r * MMP.CartierDivisorSheaf.sectionVal s) =
          toK (g ⁻¹ᵁ U.unop) (g.app U.unop r) *
            rho g U.unop (MMP.CartierDivisorSheaf.sectionVal s)
        rw [map_mul]
        exact congrArg (· * rho g U.unop (MMP.CartierDivisorSheaf.sectionVal s))
          (rho_toK g U.unop r))))

private noncomputable def lambdaHom {E : X.CartierDivisor} {E' : Y.CartierDivisor}
    (h : IsPullback g E E') :
    MMP.CartierDivisor.sheaf E ⟶ (Scheme.Modules.pushforward g).obj (MMP.CartierDivisor.sheaf E') :=
  (SheafOfModules.fullyFaithfulForget _).preimage (lambdaPre g h)

private theorem lambdaHom_val {E : X.CartierDivisor} {E' : Y.CartierDivisor}
    (h : IsPullback g E E') : (lambdaHom g h).val = lambdaPre g h :=
  (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).map_preimage
    (show (SheafOfModules.forget X.ringCatSheaf).obj (MMP.CartierDivisor.sheaf E) ⟶
      (SheafOfModules.forget X.ringCatSheaf).obj
        ((Scheme.Modules.pushforward g).obj (MMP.CartierDivisor.sheaf E')) from lambdaPre g h)

private theorem sectionVal_lambdaHom_app {E : X.CartierDivisor} {E' : Y.CartierDivisor}
    (h : IsPullback g E E') (U : X.Opens) (s : Γ(MMP.CartierDivisor.sheaf E, U)) :
    MMP.CartierDivisorSheaf.sectionVal ((lambdaHom g h).app U s) =
      rho g U (MMP.CartierDivisorSheaf.sectionVal s) := by
  have := congrArg (fun φ => φ.app (op U) s) (lambdaHom_val g h)
  exact congrArg MMP.CartierDivisorSheaf.sectionVal this

end Key

/-- The pull-back of `𝒪_X(D)` along a dominant morphism of integral schemes is `𝒪_Y(D')` for
`D'` a pull-back of `D`. -/
private theorem nonempty_pullback_sheaf_iso {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (g : Y ⟶ X) [IsDominant g]
    {D : X.CartierDivisor} {D' : Y.CartierDivisor} (hD' : MMP.Intersection.IsPullback g D D') :
    Nonempty ((Scheme.Modules.pullback g).obj (MMP.CartierDivisor.sheaf D) ≅
      MMP.CartierDivisor.sheaf D') := by
  have : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (MMP.CartierDivisor.sheaf D) := inferInstance
  have : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (MMP.CartierDivisor.sheaf D') := inferInstance
  have hinvpb : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      ((Scheme.Modules.pullback g).obj (MMP.CartierDivisor.sheaf D)) :=
    SheafOfModules.isInvertible_pullback g _
  let ℓ := lambdaHom g hD'
  let adj := Scheme.Modules.pullbackPushforwardAdjunction g
  let ψ : (Scheme.Modules.pullback g).obj (MMP.CartierDivisor.sheaf D) ⟶
      MMP.CartierDivisor.sheaf D' := (adj.homEquiv _ _).symm ℓ
  have hψ : ∀ (U : X.Opens) (s : Γ(MMP.CartierDivisor.sheaf D, U)),
      ψ.app (g ⁻¹ᵁ U) ((adj.unit.app (MMP.CartierDivisor.sheaf D)).app U s) =
        ℓ.app U s := by
    have h1 : ℓ = adj.unit.app (MMP.CartierDivisor.sheaf D) ≫
        (Scheme.Modules.pushforward g).map ψ := by
      have := (adj.homEquiv _ _).apply_symm_apply ℓ
      rw [Adjunction.homEquiv_unit] at this
      exact this.symm
    intro U s
    exact (congrArg (fun φ => φ.app U s) h1).symm
  have hepi : Epi ψ := by
    refine epi_of_surjective_on_covering
      (fun V : Y.Opens => Function.Surjective (ψ.app V)) ?_ ψ (fun V hV => hV)
    intro U T hT
    rw [Opens.mem_grothendieckTopology]
    intro y hy
    obtain ⟨U₀, -, V₀, hV₀, hyV₀, f₀, f', hf₀, hf', hff⟩ :=
      exists_local_pullback_equation g hD' y ⊤ trivial
    refine ⟨V₀ ⊓ U, homOfLE inf_le_right, hT (homOfLE inf_le_right) ?_, ⟨hyV₀, hy⟩⟩
    have hVV₀ : V₀ ⊓ U ≤ V₀ := inf_le_left
    intro t
    have hmem : Mem D' (V₀ ⊓ U) (MMP.CartierDivisorSheaf.sectionVal t) :=
      (show ↥((MMP.CartierDivisor.sheafSubmodule D').obj (op (V₀ ⊓ U))) from t).2
    obtain ⟨a, ha⟩ := (mem_iff (U := V₀) (V := V₀ ⊓ U) hf' hVV₀ _).1 hmem
    let e₀ : Γ(MMP.CartierDivisor.sheaf D, U₀) :=
      (⟨(↑f₀⁻¹ : X.totalQuotientSheaf.obj.obj (op U₀)), mem_inv hf₀⟩ :
        ↥((MMP.CartierDivisor.sheafSubmodule D).obj (op U₀)))
    let ε := (adj.unit.app (MMP.CartierDivisor.sheaf D)).app U₀ e₀
    refine ⟨a • ((Scheme.Modules.pullback g).obj
      (MMP.CartierDivisor.sheaf D)).presheaf.map
        (homOfLE (hVV₀.trans hV₀)).op ε, ?_⟩
    apply MMP.CartierDivisorSheaf.sectionVal_injective
    rw [Scheme.Modules.Hom.app_smul]
    have nat := PresheafOfModules.naturality_apply ψ.val (homOfLE (hVV₀.trans hV₀)).op ε
    have h4 := nat.trans (congrArg
      ((MMP.CartierDivisor.sheaf D').val.map (homOfLE (hVV₀.trans hV₀)).op)
      (hψ U₀ e₀))
    have h3 : MMP.CartierDivisorSheaf.sectionVal
        (ψ.app (V₀ ⊓ U) (((Scheme.Modules.pullback g).obj
          (MMP.CartierDivisor.sheaf D)).presheaf.map
            (homOfLE (hVV₀.trans hV₀)).op ε)) =
        resK (hVV₀.trans hV₀) (rho g U₀ (↑f₀⁻¹ : X.totalQuotientSheaf.obj.obj (op U₀))) := by
      have h5 := congrArg MMP.CartierDivisorSheaf.sectionVal h4
      refine h5.trans ?_
      exact congrArg (resK (hVV₀.trans hV₀)) (sectionVal_lambdaHom_app g hD' U₀ e₀)
    change toK (V₀ ⊓ U) a * MMP.CartierDivisorSheaf.sectionVal
      (ψ.app (V₀ ⊓ U) (((Scheme.Modules.pullback g).obj
          (MMP.CartierDivisor.sheaf D)).presheaf.map
            (homOfLE (hVV₀.trans hV₀)).op ε)) = _
    rw [h3, ← ha, ← resK_resK hVV₀ hV₀, resK_rho_inv g hV₀ hff]
  exact ⟨@asIso _ _ _ _ ψ (Stacks.Chow.GenuineChern.isIso_of_epi_of_isInvertible ψ hinvpb
    inferInstance)⟩

end SheafPullback

section BaseChange

variable {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K] [IsAlgClosed k₀] [IsAlgClosed K]
    {X₀ X : Scheme.{u}} (s₀ : X₀ ⟶ Spec (.of k₀)) (s : X ⟶ Spec (.of K)) (π : X ⟶ X₀)

/-- For `q : Y ⟶ X` flat with `X` integral and `Y` locally Noetherian, every associated point of
`Y` lies over the generic point of `X`. -/
private theorem map_eq_genericPoint_of_mem_schemeAssociatedPoints {Y X : Scheme.{u}} (q : Y ⟶ X)
    [Flat q] [IsIntegral X] [IsLocallyNoetherian Y] (y : Y)
    (hy : y ∈ Stacks.Divisors.schemeAssociatedPoints Y) :
    q y = genericPoint X := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (q y)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hx (q ⁻¹ᵁ U).isOpen
  change IsAffineOpen U at hU
  change IsAffineOpen V at hV
  have : Nonempty U := ⟨⟨q y, hx⟩⟩
  let φ := (q.appLE U V hVU).hom
  let _ : Algebra Γ(X, U) Γ(Y, V) := φ.toAlgebra
  have : Module.Flat Γ(X, U) Γ(Y, V) := q.flat_appLE hU hV hVU
  have : (SheafOfModules.unit Y.ringCatSheaf).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit Y
  have hp :=
    (AlgebraicGeometry.isAssociatedPrime_sections_iff_isAssociatedPoint_of_isLocallyNoetherian
      (SheafOfModules.unit Y.ringCatSheaf) V hV hyV).mpr hy
  change IsAssociatedPrimeStacks Γ(Y, V) Γ(Y, V) (hV.primeIdealOf ⟨y, hyV⟩).asIdeal at hp
  obtain ⟨hprime, b, hb⟩ := hp
  have hb0 : b ≠ 0 := by
    intro hh
    apply hprime.one_notMem
    rw [← hb, Submodule.mem_colon_span_singleton, Submodule.mem_bot]
    simp [hh]
  have hpbot : (hU.primeIdealOf ⟨q y, hx⟩).asIdeal = ⊥ := by
    apply le_antisymm _ bot_le
    intro a ha
    change a = 0
    have ha' : φ a ∈ (hV.primeIdealOf ⟨y, hyV⟩).asIdeal := by
      have hnat := IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hyV
      rw [← hnat] at ha
      exact ha
    rw [← hb, Submodule.mem_colon_span_singleton, Submodule.mem_bot] at ha'
    change φ a * b = 0 at ha'
    have hz : a • (b : Γ(Y, V)) = 0 := ha'
    exact (smul_eq_zero.mp hz).resolve_right hb0
  have hη : genericPoint X ∈ U :=
    (genericPoint_spec X).mem_open_set_iff U.isOpen |>.mpr (by simpa using ‹Nonempty U›)
  have heq : hU.primeIdealOf ⟨q y, hx⟩ = hU.primeIdealOf ⟨genericPoint X, hη⟩ := by
    apply PrimeSpectrum.ext
    rw [hpbot, hU.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]
    rfl
  simpa only [hU.fromSpec_primeIdealOf] using congrArg hU.fromSpec heq

/-- Every Cartier divisor on `X₀` has a pull-back along the flat base change `π`. -/
private theorem exists_isPullback
    (h : CategoryTheory.IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀)
    (D₀ : X₀.CartierDivisor) : ∃ D : X.CartierDivisor, MMP.Intersection.IsPullback π D₀ D := by
  have hv : AlgebraicGeometry.IsVariety k₀ s₀ := hX₀.toIsVariety
  have : IsIntegral X₀ := hv.toIsIntegral
  have hft : LocallyOfFiniteType s₀ := inferInstance
  have hg : Flat (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have : Flat π := MorphismProperty.of_isPullback h.flip hg
  have hfts : LocallyOfFiniteType s := MorphismProperty.of_isPullback h hft
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  have : IsLocallyNoetherian X₀ := LocallyOfFiniteType.isLocallyNoetherian s₀
  refine MMP.Intersection.exists_isPullback fun η hη => ?_
  rw [map_eq_genericPoint_of_mem_schemeAssociatedPoints π η hη]
  have : IsArtinianRing (X₀.presheaf.stalk (genericPoint X₀)) :=
    (inferInstance : IsArtinianRing X₀.functionField)
  exact MMP.Intersection.notMem_cartierSupport_of_isArtinianRing D₀ _

omit [IsAlgClosed k₀] [IsAlgClosed K] in
/-- The degree of a pulled-back invertible sheaf on a base change of a curve: if `Y → C₀` is the
base change of the curve `C₀` along `k₀ → K` and `Y → X` is the induced morphism, then the degree
of `π^* L` on `Y` equals the degree of `L` on `C₀`. -/
private theorem degreeOn_baseChange {C₀ Y : Scheme.{u}} (ι₀ : C₀ ⟶ X₀) (ι : Y ⟶ X)
    (j : Y ⟶ C₀) [IsProper (ι₀ ≫ s₀)]
    (hc : ι ≫ π = j ≫ ι₀)
    (h : IsPullback j (ι ≫ s) (ι₀ ≫ s₀) (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hdim : topologicalKrullDim C₀ ≤ 1) (hdim' : topologicalKrullDim Y ≤ 1)
    (L : X₀.Modules) [SheafOfModules.IsInvertible X₀.presheaf X₀.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 ((Scheme.Modules.pullback π).obj L)]
    [IsProper (ι ≫ s)] :
    degreeOn K s ι hdim' ((Scheme.Modules.pullback π).obj L) = degreeOn k₀ s₀ ι₀ hdim L := by
  have e : (Scheme.Modules.pullback ι).obj ((Scheme.Modules.pullback π).obj L) ≅
      (Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback ι₀).obj L) :=
    (Scheme.Modules.pullbackComp ι π).app L ≪≫ (Scheme.Modules.pullbackCongr hc).app L ≪≫
      ((Scheme.Modules.pullbackComp j ι₀).app L).symm
  unfold degreeOn invertibleCurveDegree
  congr 1
  · refine finsum_congr fun n => ?_
    rw [finrank_cohomologyOverField_eq_of_iso K (ι ≫ s) e n,
      finrank_cohomologyOverField_baseChange_field k₀ K j (ι ≫ s) (ι₀ ≫ s₀) h _ n]
  · refine finsum_congr fun n => ?_
    have eu : SheafOfModules.unit Y.ringCatSheaf ≅
        (Scheme.Modules.pullback j).obj (SheafOfModules.unit C₀.ringCatSheaf) :=
      (Scheme.Modules.pullbackUnitIso j).symm
    have : (SheafOfModules.unit C₀.ringCatSheaf).IsQuasicoherent := inferInstance
    rw [finrank_cohomologyOverField_eq_of_iso K (ι ≫ s) eu n,
      finrank_cohomologyOverField_baseChange_field k₀ K j (ι ≫ s) (ι₀ ≫ s₀) h
        (SheafOfModules.unit C₀.ringCatSheaf) n]

omit [IsAlgClosed K] in
/-- The base change of a projective variety over an algebraically closed field is integral, and
the projection to the original is surjective, hence dominant. -/
private theorem isIntegral_and_isDominant_of_isPullback
    (h : CategoryTheory.IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) : IsIntegral X ∧ IsDominant π := by
  have hv : AlgebraicGeometry.IsVariety k₀ s₀ := hX₀.toIsVariety
  haveI : IsIntegral X₀ := hv.toIsIntegral
  haveI : IrreducibleSpace X₀ := inferInstance
  haveI : IsReduced X₀ := inferInstance
  haveI : GeometricallyIrreducible s₀ :=
    geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k₀ X₀ s₀
  haveI : GeometricallyReduced s₀ := geometricallyReduced_of_isReduced s₀
  haveI : GeometricallyIntegral s₀ :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible s₀
  haveI : GeometricallyIntegral s := MorphismProperty.of_isPullback h inferInstance
  have hsurj : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) := by
    have : (algebraMap k₀ K).FaithfullyFlat := by
      rw [RingHom.faithfullyFlat_algebraMap_iff]
      infer_instance
    exact ((flat_and_surjective_SpecMap_iff _).2 this).2
  haveI : Surjective π := MorphismProperty.of_isPullback h.flip hsurj
  exact ⟨GeometricallyIntegral.isIntegral_of_subsingleton s, inferInstance⟩

omit [IsAlgClosed K] in
open CategoryTheory.Limits in
/-- The base change of a proper curve `C₀ ⊆ X₀` is a proper curve `C ⊆ X`, with a map `C ⟶ C₀`
making the square with `π` commute and `C = C₀ ×_{k₀} K`. -/
private theorem exists_properCurve_baseChange
    (h : CategoryTheory.IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) (C₀ : ProperCurve s₀) :
    ∃ (C : ProperCurve s) (j : C.scheme ⟶ C₀.scheme), C.ι ≫ π = j ≫ C₀.ι ∧
      CategoryTheory.IsPullback j (C.ι ≫ s) (C₀.ι ≫ s₀)
        (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) := by
  set g := Spec.map (CommRingCat.ofHom (algebraMap k₀ K)) with hg
  set t₀ : C₀.scheme ⟶ Spec (.of k₀) := C₀.ι ≫ s₀ with ht₀
  have hpb : CategoryTheory.IsPullback (pullback.snd t₀ g) (pullback.fst t₀ g) g t₀ :=
    (CategoryTheory.IsPullback.of_hasPullback t₀ g).flip
  obtain ⟨Y, j, t, hpb⟩ : ∃ (Y : Scheme.{u}) (j : Y ⟶ C₀.scheme) (t : Y ⟶ Spec (.of K)),
      CategoryTheory.IsPullback t j g t₀ := ⟨_, _, _, hpb⟩
  have hcomm : (j ≫ C₀.ι) ≫ s₀ = t ≫ g := by
    simpa only [Category.assoc, ← ht₀] using hpb.w.symm
  set ι' : Y ⟶ X := h.lift (j ≫ C₀.ι) t hcomm with hι'
  have hι'π : ι' ≫ π = j ≫ C₀.ι := h.lift_fst _ _ _
  have hι's : ι' ≫ s = t := h.lift_snd _ _ _
  have hsq : CategoryTheory.IsPullback j ι' C₀.ι π := by
    refine (CategoryTheory.IsPullback.of_right (h₁₁ := ι') (h₁₂ := s) (h₂₁ := C₀.ι) (h₂₂ := s₀)
      (v₁₁ := j) (v₁₂ := π) (v₁₃ := g) ?_ hι'π h.flip).flip
    rwa [hι's]
  haveI : IsClosedImmersion C₀.ι := inferInstance
  haveI : IsClosedImmersion ι' := MorphismProperty.of_isPullback hsq inferInstance
  have hproper : IsProper t₀ := C₀.isProperCurve.isProper
  haveI : IsProper t := MorphismProperty.of_isPullback hpb.flip hproper
  -- integrality of `Y`
  haveI : IsReduced C₀.scheme := inferInstance
  haveI : GeometricallyIrreducible t₀ :=
    geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k₀ C₀.scheme t₀
  haveI : GeometricallyReduced t₀ := geometricallyReduced_of_isReduced t₀
  haveI : GeometricallyIntegral t₀ :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible t₀
  haveI : GeometricallyIntegral t := MorphismProperty.of_isPullback hpb.flip inferInstance
  haveI : IsIntegral Y := GeometricallyIntegral.isIntegral_of_subsingleton t
  obtain ⟨e, he⟩ := exists_iso_curveSubschemeAt ι'
  -- the curve
  have key : e.inv ≫ ι' = curveSubschemeAtι (ι' (genericPoint Y)) :=
    e.inv_comp_eq.2 he.symm
  haveI : LocallyOfFiniteType t₀ := inferInstance
  have hdimY : topologicalKrullDim Y = topologicalKrullDim C₀.scheme :=
    topologicalKrullDim_baseChange k₀ K j t t₀ hpb.flip
  have hdimC : topologicalKrullDim (curveSubschemeAt (ι' (genericPoint Y))) = 1 := by
    rw [← IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph, hdimY]
    exact C₀.dim_eq
  have hpropC : IsProper (curveSubschemeAtι (ι' (genericPoint Y)) ≫ s) := by
    have : curveSubschemeAtι (ι' (genericPoint Y)) ≫ s = e.inv ≫ t := by
      rw [← key, Category.assoc, hι's]
    rw [this]
    infer_instance
  refine ⟨⟨ι' (genericPoint Y), ⟨hdimC, hpropC⟩⟩, e.inv ≫ j, ?_, ?_⟩
  · change curveSubschemeAtι (ι' (genericPoint Y)) ≫ π = _
    rw [← key]
    simp [hι'π]
  · refine hpb.flip.of_iso' e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) ?_ (by simp)
      (by simp)
    change e.inv ≫ t = curveSubschemeAtι (ι' (genericPoint Y)) ≫ s
    rw [← key, Category.assoc, hι's]

/-- Base change of curves: every proper curve `C₀ ⊆ X₀` has a proper curve `C ⊆ X` (the base
change `C₀ ×_{k₀} K`, integral as `k₀` is algebraically closed) on which the pull-back of every
Cartier divisor has the same degree. -/
private theorem exists_properCurve_degree_eq_of_curve
    (h : CategoryTheory.IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) (C₀ : ProperCurve s₀) :
    ∃ C : ProperCurve s, ∀ (E₀ : X₀.CartierDivisor) (E : X.CartierDivisor),
      MMP.Intersection.IsPullback π E₀ E →
        (C.cycle ℝ).intersectionNumber (KCartierDivisor.ofCartier ℝ E) =
          (C₀.cycle ℝ).intersectionNumber (KCartierDivisor.ofCartier ℝ E₀) := by
  obtain ⟨hXint, hdom⟩ := isIntegral_and_isDominant_of_isPullback s₀ s π h hX₀
  haveI : IsIntegral X₀ := hX₀.toIsVariety.toIsIntegral
  obtain ⟨C, j, hc, hsq⟩ := exists_properCurve_baseChange s₀ s π h hX₀ C₀
  refine ⟨C, fun E₀ E hE => ?_⟩
  have e : (Scheme.Modules.pullback π).obj (MMP.CartierDivisor.sheaf E₀) ≅
      MMP.CartierDivisor.sheaf E := (nonempty_pullback_sheaf_iso π hE).some
  rw [OneCycle.intersectionNumber_ofCartier, OneCycle.intersectionNumber_ofCartier,
    OneCycle.cartierDegree, OneCycle.cartierDegree, OneCycle.degree_cycle, OneCycle.degree_cycle]
  norm_cast
  unfold ProperCurve.degree
  rw [← degreeOn_eq_of_iso K s C.ι C.dim_le e]
  exact degreeOn_baseChange s₀ s π C₀.ι C.ι j hc hsq C₀.dim_le C.dim_le _

section Descent

open AlgebraicGeometry.FieldExtensionDescent CategoryTheory.Limits

omit [IsAlgClosed K] in
/-- **Descent of an invertible module to a finitely generated stage.** An invertible module `L`
on the base change `X` of the `k₀`-scheme `X₀` is, for some finitely generated `k₀`-subalgebra
`A ⊆ K`, the pull-back of an invertible module `M` on `X₀ ×_{k₀} Spec A` along the canonical
morphism `ρ : X ⟶ X₀ ×_{k₀} Spec A`. -/
private theorem exists_descent
    (h : CategoryTheory.IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    ∃ (A : FGSubalgebra k₀ K)
      (M : (pullback (Spec.map (CommRingCat.ofHom (algebraMap k₀ (A : Subalgebra k₀ K))))
        s₀).Modules)
      (_ : SheafOfModules.IsInvertible
        (pullback (Spec.map (CommRingCat.ofHom (algebraMap k₀ (A : Subalgebra k₀ K)))) s₀).presheaf
        (pullback (Spec.map (CommRingCat.ofHom (algebraMap k₀ (A : Subalgebra k₀ K))))
          s₀).ringCatSheaf.2 M)
      (ρ : X ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap k₀ (A : Subalgebra k₀ K)))) s₀),
      ρ ≫ pullback.fst _ _ =
          s ≫ Spec.map (CommRingCat.ofHom (algebraMap (A : Subalgebra k₀ K) K)) ∧
        ρ ≫ pullback.snd _ _ = π ∧ Nonempty (L ≅ (Scheme.Modules.pullback ρ).obj M) := by
  have : QuasiCompact s₀ := inferInstance
  have : QuasiSeparated s₀ := inferInstance
  have : CompactSpace X₀ := QuasiCompact.compactSpace_of_compactSpace s₀
  have : QuasiSeparatedSpace X₀ := quasiSeparatedSpace_of_quasiSeparated s₀
  let ε : X ≅ pullback (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) s₀ := h.flip.isoPullback
  let LK : (pullback (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) s₀).Modules :=
    (Scheme.Modules.pullback ε.inv).obj L
  have hLK : SheafOfModules.IsInvertible
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) s₀).presheaf
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) s₀).ringCatSheaf.2 LK :=
    inferInstance
  obtain ⟨i, Li, hLi, ⟨e⟩⟩ := exists_isInvertible_baseChangeDiagram_pullback_iso k₀ K s₀ LK hLK
  let cA : pullback (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) s₀ ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap k₀ (i.unop : Subalgebra k₀ K)))) s₀ :=
    (baseChangeLimitCone k₀ K s₀).cone.π.app i
  refine ⟨i.unop, Li, hLi, ε.hom ≫ cA, ?_, ?_, ?_⟩
  · have h1 : cA ≫ pullback.fst _ _ =
        pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap (i.unop : Subalgebra k₀ K) K)) :=
      pullback.lift_fst _ _ _
    have h2 : ε.hom ≫ pullback.fst _ _ = s := h.flip.isoPullback_hom_fst
    rw [Category.assoc, h1, ← Category.assoc, h2]
  · have h1 : cA ≫ pullback.snd _ _ = pullback.snd _ _ :=
      pullback.lift_snd _ _ _
    have h2 : ε.hom ≫ pullback.snd _ _ = π := h.flip.isoPullback_hom_snd
    rw [Category.assoc, h1, h2]
  · exact ⟨((Scheme.Modules.pullbackId X).app L).symm ≪≫
      (Scheme.Modules.pullbackCongr ε.hom_inv_id.symm).app L ≪≫
      ((Scheme.Modules.pullbackComp ε.hom ε.inv).app L).symm ≪≫
      (Scheme.Modules.pullback ε.hom).mapIso e ≪≫ (Scheme.Modules.pullbackComp ε.hom cA).app Li⟩

end Descent

section Spreading

open AlgebraicGeometry.FieldExtensionDescent CategoryTheory.Limits Opposite

/-- Spreading out a morphism to a scheme of finite presentation over the base. -/
private theorem exists_spread_morphism
    {I : Type u} [Category.{u} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    {T X₀ : Scheme.{u}} (s₀ : X₀ ⟶ T) [LocallyOfFinitePresentation s₀] [QuasiCompact s₀]
    [QuasiSeparated s₀] (t : ∀ i, D.obj i ⟶ T) (ht : ∀ {i j : I} (e : j ⟶ i), D.map e ≫ t i = t j)
    (tc : c.pt ⟶ T) (htc : ∀ i, c.π.app i ≫ t i = tc)
    (i : I) {W C : Scheme.{u}} (p : W ⟶ D.obj i) (hp : FinitePresentation p)
    (a : C ⟶ W) (φ : C ⟶ c.pt) (hpb : IsPullback a φ p (c.π.app i))
    (ψ : C ⟶ X₀) (hψ : ψ ≫ s₀ = φ ≫ tc) :
    ∃ (j : I) (e : j ⟶ i) (v : pullback p (D.map e) ⟶ X₀),
      pullback.lift a (φ ≫ c.π.app j) (by rw [hpb.w, Category.assoc, c.w e]) ≫ v = ψ ∧
      v ≫ s₀ = pullback.snd p (D.map e) ≫ t j := by
  let Z : Over (D.obj i) := Over.mk p
  let Y : Over (D.obj i) := (Over.pullback (t i)).obj (Over.mk s₀)
  have hY : FinitePresentation Y.hom :=
    ⟨inferInstanceAs (LocallyOfFinitePresentation (pullback.snd s₀ (t i))),
    inferInstanceAs (QuasiCompact (pullback.snd s₀ (t i))),
    inferInstanceAs (QuasiSeparated (pullback.snd s₀ (t i)))⟩
  let ιP := hpb.isoPullback
  have h1 : (ιP.inv ≫ ψ) ≫ s₀ = (pullback.fst p (c.π.app i) ≫ p) ≫ t i := by
    have : ιP.inv ≫ φ = pullback.snd p (c.π.app i) := hpb.isoPullback_inv_snd
    have e1 : (ιP.inv ≫ ψ) ≫ s₀ = pullback.snd p (c.π.app i) ≫ tc := by
      rw [Category.assoc, hψ, ← Category.assoc, this]
    have e2 : (pullback.fst p (c.π.app i) ≫ p) ≫ t i = pullback.snd p (c.π.app i) ≫ tc := by
      rw [pullback.condition, Category.assoc, htc]
    exact e1.trans e2.symm
  let F : pullback p (c.π.app i) ⟶ pullback Y.hom (c.π.app i) :=
    pullback.lift (pullback.lift (ιP.inv ≫ ψ) (pullback.fst p (c.π.app i) ≫ p) h1)
      (pullback.snd p (c.π.app i)) (by
        change _ ≫ pullback.snd s₀ (t i) = _
        exact (pullback.lift_snd _ _ _).trans pullback.condition)
  let f : (Over.pullback (c.π.app i)).obj Z ⟶ (Over.pullback (c.π.app i)).obj Y :=
    Over.homMk F (pullback.lift_snd _ _ _)
  obtain ⟨j, e, g, α, β, hα, hβ, hcomm⟩ :=
    exists_morphism_after_baseChange D c hc i Z Y hp hY f
  let J : C ⟶ pullback p (D.map e) :=
    pullback.lift a (φ ≫ c.π.app j) (by rw [hpb.w, Category.assoc, c.w e])
  have hJs : J ≫ pullback.snd p (D.map e) = φ ≫ c.π.app j := pullback.lift_snd _ _ _
  have hJf : J ≫ pullback.fst p (D.map e) = a := pullback.lift_fst _ _ _
  let θ : C ⟶ pullback (pullback.snd p (D.map e)) (c.π.app j) := pullback.lift J φ hJs
  have hαw := Over.w α.hom
  have hθf : θ ≫ pullback.fst ((Over.pullback (D.map e)).obj Z).hom (c.π.app j) = J :=
    pullback.lift_fst _ _ _
  have hθs : θ ≫ pullback.snd ((Over.pullback (D.map e)).obj Z).hom (c.π.app j) = φ :=
    pullback.lift_snd _ _ _
  have hθ : θ ≫ α.hom.left = ιP.hom := by
    apply pullback.hom_ext
    · rw [Category.assoc, hα, ← Category.assoc, hθf]
      exact hJf.trans hpb.isoPullback_hom_fst.symm
    · rw [Category.assoc]
      refine Eq.trans ?_ hpb.isoPullback_hom_snd.symm
      exact (congrArg (fun q => θ ≫ q) hαw).trans hθs
  refine ⟨j, e, g.left ≫ pullback.fst Y.hom (D.map e) ≫ pullback.fst s₀ (t i), ?_, ?_⟩
  · have hmf := overPullback_map_left_fst (c.π.app j) g
    have hleft : α.hom.left ≫ F = ((Over.pullback (c.π.app j)).map g).left ≫ β.hom.left :=
      congrArg Over.Hom.left hcomm
    have hFf : F ≫ pullback.fst Y.hom (c.π.app i) =
        pullback.lift (ιP.inv ≫ ψ) (pullback.fst p (c.π.app i) ≫ p) h1 := pullback.lift_fst _ _ _
    have hff : pullback.lift (ιP.inv ≫ ψ) (pullback.fst p (c.π.app i) ≫ p) h1 ≫
        pullback.fst s₀ (t i) = ιP.inv ≫ ψ := pullback.lift_fst _ _ _
    have hk : (((Over.pullback (c.π.app j)).map g).left ≫
          pullback.fst ((Over.pullback (D.map e)).obj Y).hom (c.π.app j)) ≫
          pullback.fst Y.hom (D.map e) =
        (((Over.pullback (c.π.app j)).map g).left ≫ β.hom.left) ≫
          pullback.fst Y.hom (c.π.app i) := by
      rw [Category.assoc, Category.assoc, hβ]
    calc J ≫ g.left ≫ pullback.fst Y.hom (D.map e) ≫ pullback.fst s₀ (t i)
        = θ ≫ (pullback.fst ((Over.pullback (D.map e)).obj Z).hom (c.π.app j) ≫ g.left) ≫
            pullback.fst Y.hom (D.map e) ≫ pullback.fst s₀ (t i) := by
          rw [← hθf]
          simp only [Category.assoc]
      _ = θ ≫ ((((Over.pullback (c.π.app j)).map g).left ≫
          pullback.fst ((Over.pullback (D.map e)).obj Y).hom (c.π.app j)) ≫
            pullback.fst Y.hom (D.map e)) ≫ pullback.fst s₀ (t i) := by
          rw [hmf]
          simp only [Category.assoc]
      _ = θ ≫ ((((Over.pullback (c.π.app j)).map g).left ≫ β.hom.left) ≫
            pullback.fst Y.hom (c.π.app i)) ≫ pullback.fst s₀ (t i) := by rw [hk]
      _ = θ ≫ (α.hom.left ≫ F ≫ pullback.fst Y.hom (c.π.app i)) ≫ pullback.fst s₀ (t i) := by
          rw [← hleft]
          simp only [Category.assoc]
      _ = (θ ≫ α.hom.left) ≫ (F ≫ pullback.fst Y.hom (c.π.app i)) ≫ pullback.fst s₀ (t i) := by
          simp only [Category.assoc]
      _ = ψ := by
          rw [hθ, hFf, hff]
          simp
  · have hgw := Over.w g
    calc (g.left ≫ pullback.fst Y.hom (D.map e) ≫ pullback.fst s₀ (t i)) ≫ s₀
        = g.left ≫ pullback.fst Y.hom (D.map e) ≫ pullback.snd s₀ (t i) ≫ t i := by
          rw [Category.assoc, Category.assoc, ← pullback.condition (f := s₀) (g := t i)]
      _ = g.left ≫ pullback.snd Y.hom (D.map e) ≫ D.map e ≫ t i := by
          have hc2 : pullback.fst Y.hom (D.map e) ≫ pullback.snd s₀ (t i) =
              pullback.snd Y.hom (D.map e) ≫ D.map e := pullback.condition
          rw [← Category.assoc (pullback.fst Y.hom (D.map e)), hc2]
          simp only [Category.assoc]
      _ = pullback.snd p (D.map e) ≫ t j := by
          rw [ht e, ← Category.assoc]
          exact congrArg (· ≫ t j) hgw

/-- A flat proper model at some stage. -/
private theorem exists_flat_proper_model
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    [∀ i, AlgebraicGeometry.IsNoetherian (D.obj i)]
    {S' : Scheme.{u}} (φ : S' ⟶ c.pt) [Flat φ] [IsProper φ] [LocallyOfFinitePresentation φ] :
    ∃ (j : I) (W : Scheme.{u}) (p : W ⟶ D.obj j) (a : S' ⟶ W), IsPullback a φ p (c.π.app j) ∧
      Flat p ∧ IsProper p ∧ LocallyOfFinitePresentation p := by
  have hφfp : FinitePresentation φ :=
    ⟨‹_›, instQuasiCompactOfUniversallyClosed φ, IsSeparated.instQuasiSeparated φ⟩
  obtain ⟨i, Z, hZfp, hZflat, ⟨e⟩⟩ := exists_flat_model_of_small_limit D c hc φ hφfp
  have hpbC : IsPullback (e.hom.left ≫ pullback.fst Z.hom (c.π.app i)) φ Z.hom (c.π.app i) := by
    have hw : e.hom.left ≫ pullback.snd Z.hom (c.π.app i) = φ := Over.w e.hom
    refine IsPullback.of_iso_pullback ⟨?_⟩ ((Over.forget _).mapIso e) rfl hw
    rw [Category.assoc, pullback.condition, ← Category.assoc, hw]
  have hZp : IsProper (pullback.snd Z.hom (c.π.app i)) := by
    rw [← hpbC.isoPullback_inv_snd]
    infer_instance
  have : LocallyOfFinitePresentation Z.hom := hZfp.1
  have : QuasiCompact Z.hom := hZfp.2.1
  have : QuasiSeparated Z.hom := hZfp.2.2
  have : Flat Z.hom := hZflat
  have : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  have : QuasiSeparatedSpace Z.left := quasiSeparatedSpace_of_quasiSeparated Z.hom
  have : CompactSpace (Over.mk (𝟙 (D.obj i))).left := inferInstanceAs (CompactSpace (D.obj i))
  have : QuasiSeparatedSpace (Over.mk (𝟙 (D.obj i))).left :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj i))
  let f₀ : Z ⟶ Over.mk (𝟙 (D.obj i)) := Over.homMk Z.hom (by simp)
  have : LocallyOfFiniteType f₀.left := inferInstanceAs (LocallyOfFiniteType Z.hom)
  have : IsProper ((Over.pullback (c.π.app i)).map f₀).left :=
    (overPullback_map_homMk_left_iff @IsProper Z.hom (c.π.app i)).mpr hZp
  obtain ⟨j, w, hprop⟩ := exists_isProper_baseChange_of_isLimit D c i hc Z _ f₀
  have hprop' : IsProper (pullback.snd Z.hom (D.map w)) :=
    (overPullback_map_homMk_left_iff @IsProper Z.hom (D.map w)).mp hprop
  exact ⟨j, _, pullback.snd Z.hom (D.map w), _, IsPullback.pullbackSnd_of_isLimit c w hpbC,
    inferInstance, hprop', inferInstance⟩

omit [IsAlgClosed K] in
/-- **Spreading out a proper curve.** Every proper curve `C ⊆ X` over `K` is the base change
`𝒲 ×_{Spec A} Spec K` of a flat proper family `𝒲 ⟶ Spec A` of finite presentation over a finitely
generated `k₀`-subalgebra `A ⊆ K` containing any prescribed `A₀`, together with a morphism
`u : 𝒲 ⟶ X₀` over `k₀` compatible with `π` on `C`. -/
private theorem exists_spreading
    (h : CategoryTheory.IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) (A₀ : FGSubalgebra k₀ K) (C : ProperCurve s) :
    ∃ (A : FGSubalgebra k₀ K) (_ : A₀ ≤ A) (W : Scheme.{u})
      (f : W ⟶ Spec (.of (A : Subalgebra k₀ K))) (u : W ⟶ X₀)
      (j : C.scheme ⟶ W) (_ : Flat f) (_ : IsProper f) (_ : LocallyOfFinitePresentation f),
      u ≫ s₀ = f ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ (A : Subalgebra k₀ K))) ∧
      CategoryTheory.IsPullback j (C.ι ≫ s) f
        (Spec.map (CommRingCat.ofHom (algebraMap (A : Subalgebra k₀ K) K))) ∧
      j ≫ u = C.ι ≫ π := by
  classical
  have : LocallyOfFiniteType s₀ := inferInstance
  have : QuasiCompact s₀ := inferInstance
  have : QuasiSeparated s₀ := inferInstance
  have : LocallyOfFinitePresentation s₀ := inferInstance
  let D : (FGSubalgebra k₀ K)ᵒᵖ ⥤ Scheme.{u} := specDiagram k₀ K ⋙ Over.forget _
  let c : Cone D := (Over.forget _).mapCone (specLimitCone k₀ K).cone
  have hc : IsLimit c := isLimitOfPreserves _ (specLimitCone k₀ K).isLimit
  have : ∀ {i j : (FGSubalgebra k₀ K)ᵒᵖ} (e : i ⟶ j), IsAffineHom (D.map e) := by
    intro i j e
    change IsAffineHom (Spec.map _)
    infer_instance
  have : ∀ i, CompactSpace (D.obj i) := fun i => by
    change CompactSpace (Spec _)
    infer_instance
  have : ∀ i, QuasiSeparatedSpace (D.obj i) := fun i => by
    change QuasiSeparatedSpace (Spec _)
    infer_instance
  have : ∀ i, IsNoetherian (D.obj i) := fun i => by
    have : Algebra.FiniteType k₀ (i.unop : Subalgebra k₀ K) := finiteType_coe k₀ K i.unop
    have : IsNoetherianRing (i.unop : Subalgebra k₀ K) := Algebra.FiniteType.isNoetherianRing k₀ _
    change IsNoetherian (Spec (CommRingCat.of (i.unop : Subalgebra k₀ K)))
    infer_instance
  have hφp : IsProper (C.ι ≫ s) := inferInstance
  have hFl : Flat (C.ι ≫ s) := inferInstance
  have : IsLocallyNoetherian (Spec (.of K)) := inferInstance
  have hLf : LocallyOfFinitePresentation (C.ι ≫ s) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr hφp.toLocallyOfFiniteType
  obtain ⟨j₁, W₁, p₁, a₁, hpb₁, hfl₁, hpr₁, hlf₁⟩ :=
    @exists_flat_proper_model _ _ _ D c hc _ _ _ _ _ (C.ι ≫ s) hFl hφp hLf
  let k₀' := IsCofiltered.min j₁ (op A₀)
  let m := IsCofiltered.minToLeft j₁ (op A₀)
  have hpb₂ := IsPullback.pullbackSnd_of_isLimit c m hpb₁
  have hfl₂ : Flat (pullback.snd p₁ (D.map m)) := inferInstance
  have hpr₂ : IsProper (pullback.snd p₁ (D.map m)) := inferInstance
  have hlf₂ : LocallyOfFinitePresentation (pullback.snd p₁ (D.map m)) := inferInstance
  have hfp₂ : FinitePresentation (pullback.snd p₁ (D.map m)) :=
    ⟨hlf₂, instQuasiCompactOfUniversallyClosed _, IsSeparated.instQuasiSeparated _⟩
  have hψ : (C.ι ≫ π) ≫ s₀ = (C.ι ≫ s) ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ K)) := by
    rw [Category.assoc, h.w, Category.assoc]
  obtain ⟨j, e₂, v, hv₁, hv₂⟩ := exists_spread_morphism D c hc s₀
    (fun i => ((specDiagram k₀ K).obj i).hom)
    (fun e => Over.w ((specDiagram k₀ K).map e))
    (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))
    (fun i => Over.w ((specLimitCone k₀ K).cone.π.app i)) k₀' _ hfp₂ _ (C.ι ≫ s) hpb₂ (C.ι ≫ π) hψ
  have hpb₃ := IsPullback.pullbackSnd_of_isLimit c e₂ hpb₂
  have hle : A₀ ≤ j.unop :=
    (leOfHom (IsCofiltered.minToRight j₁ (op A₀)).unop).trans (leOfHom e₂.unop)
  have hfl₃ : Flat (pullback.snd (pullback.snd p₁ (D.map m)) (D.map e₂)) :=
    MorphismProperty.of_isPullback (P := @Flat)
      (IsPullback.of_hasPullback (pullback.snd p₁ (D.map m)) (D.map e₂)) hfl₂
  have hpr₃ : IsProper (pullback.snd (pullback.snd p₁ (D.map m)) (D.map e₂)) :=
    MorphismProperty.of_isPullback (P := @IsProper)
      (IsPullback.of_hasPullback (pullback.snd p₁ (D.map m)) (D.map e₂)) hpr₂
  have hlf₃ : LocallyOfFinitePresentation (pullback.snd (pullback.snd p₁ (D.map m)) (D.map e₂)) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
      (IsPullback.of_hasPullback (pullback.snd p₁ (D.map m)) (D.map e₂)) hlf₂
  exact ⟨j.unop, hle, _, pullback.snd _ (D.map e₂), v, _, hfl₃, hpr₃, hlf₃, hv₂, hpb₃, hv₁⟩

end Spreading

/-- A finitely generated subalgebra of an extension of an algebraically closed field `k₀` has a
`k₀`-point. -/
private theorem nonempty_algHom_fgSubalgebra' (k₀ K : Type u) [Field k₀] [IsAlgClosed k₀]
    [Field K] [Algebra k₀ K] (i : AlgebraicGeometry.FieldExtensionDescent.FGSubalgebra k₀ K) :
    Nonempty ((i : Subalgebra k₀ K) →ₐ[k₀] k₀) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (i : Subalgebra k₀ K)
  letI : Field ((i : Subalgebra k₀ K) ⧸ m) := Ideal.Quotient.field m
  have : Algebra.FiniteType k₀ ((i : Subalgebra k₀ K) ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k₀ m) Ideal.Quotient.mk_surjective
  have : Module.Finite k₀ ((i : Subalgebra k₀ K) ⧸ m) :=
    finite_of_finite_type_of_isJacobsonRing k₀ ((i : Subalgebra k₀ K) ⧸ m)
  have : Algebra.IsIntegral k₀ ((i : Subalgebra k₀ K) ⧸ m) := Algebra.IsIntegral.of_finite _ _
  have hbij : Function.Bijective (algebraMap k₀ ((i : Subalgebra k₀ K) ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  exact ⟨(AlgEquiv.ofBijective (Algebra.ofId k₀ ((i : Subalgebra k₀ K) ⧸ m)) hbij).symm.toAlgHom
    |>.comp (Ideal.Quotient.mkₐ k₀ m)⟩

/-- A `k₀`-point of a `k₀`-algebra `A` gives a section of `Spec A ⟶ Spec k₀`. -/
private theorem specMap_algHom_comp_algebraMap {k₀ A : Type u} [CommRing k₀] [CommRing A]
    [Algebra k₀ A] (t : A →ₐ[k₀] k₀) :
    Spec.map (CommRingCat.ofHom t.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ A)) =
      𝟙 (Spec (.of k₀)) := by
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext a
  simp

section SpreadCycle

open CategoryTheory.Limits

open AlgebraicGeometry.FieldExtensionDescent Stacks.AlgebraicGeometry.ProperFibreDimension in
/-- The dimension of the generic-type fibre is bounded. -/
private theorem dim_fiber_le_of_isPullback {W C S : Scheme.{u}} {k : Type u} [Field k]
    (f : W ⟶ S) [LocallyOfFiniteType f] (j : C ⟶ W) (φ : C ⟶ Spec (.of k)) (p : Spec (.of k) ⟶ S)
    (hpb : IsPullback j φ f p) (hC : topologicalKrullDim C ≤ 1) (y : S)
    (hy : y = p (IsLocalRing.closedPoint k)) :
    topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞) := by
  refine topologicalKrullDim_fiber_le_of_forall f y 1 fun x hx => ?_
  obtain ⟨x', rfl, -⟩ : ∃ x' : C, j x' = x ∧ φ x' = IsLocalRing.closedPoint k := by
    have hxp : f x = p (IsLocalRing.closedPoint k) := hx.trans hy
    obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := p) x
      (IsLocalRing.closedPoint k) hxp
    refine ⟨hpb.isoPullback.inv z, ?_, ?_⟩
    · rw [← hz1, ← Scheme.Hom.comp_apply, hpb.isoPullback_inv_fst]
    · rw [← hz2, ← Scheme.Hom.comp_apply, hpb.isoPullback_inv_snd]
  rw [← topologicalKrullDimAt_fiber_eq_of_isPullback hpb x']
  refine le_trans (topologicalKrullDimAt_le_topologicalKrullDim _) ?_
  exact ((φ.fiberι (φ x')).isEmbedding.isInducing.topologicalKrullDim_le).trans hC

open Stacks.AlgebraicGeometry.ProperFibreDimension in
/-- A base change to a `k`-point of a family with bounded fibre dimension has bounded dimension. -/
private theorem dim_le_of_isPullback_fiber {W Y S : Scheme.{u}} {k : Type u} [Field k]
    (f : W ⟶ S) [LocallyOfFiniteType f] (qY : Y ⟶ W) (gY : Y ⟶ Spec (.of k))
    (τ : Spec (.of k) ⟶ S) (hY : IsPullback qY gY f τ) (y₀ : S)
    (hy₀ : y₀ = τ (IsLocalRing.closedPoint k))
    (hdim : topologicalKrullDim (f.fiber y₀) ≤ ((1 : ℕ) : WithBot ℕ∞)) :
    topologicalKrullDim Y ≤ 1 := by
  have h1 : topologicalKrullDim (gY.fiber (IsLocalRing.closedPoint k)) ≤
      ((1 : ℕ) : WithBot ℕ∞) := by
    refine topologicalKrullDim_fiber_le_of_forall gY _ 1 fun y hy => ?_
    rw [topologicalKrullDimAt_fiber_eq_of_isPullback hY y]
    refine topologicalKrullDimAt_asFiber_le f (y := y₀) ?_ 1 hdim
    have hw : f (qY y) = τ (gY y) := by
      simpa only [← Scheme.Hom.comp_apply] using congrArg (fun r : Y ⟶ S => r y) hY.w
    rw [hw, hy₀]
    exact congrArg τ (Subsingleton.elim _ _)
  have hemb : Topology.IsEmbedding (gY.fiberι (IsLocalRing.closedPoint k)) :=
    (gY.fiberι _).isEmbedding
  have hsurj : Function.Surjective (gY.fiberι (IsLocalRing.closedPoint k)) := by
    intro y
    refine (Set.ext_iff.mp (gY.range_fiberι (IsLocalRing.closedPoint k)) y).mpr ?_
    exact Subsingleton.elim _ _
  have hh : IsHomeomorph (gY.fiberι (IsLocalRing.closedPoint k)) :=
    isHomeomorph_iff_isEmbedding_surjective.mpr ⟨hemb, hsurj⟩
  rwa [← IsHomeomorph.topologicalKrullDim_eq _ hh]

open Stacks.AlgebraicGeometry.ProperFibreDimension AlgebraicGeometry.FieldExtensionDescent in
/-- Specialising a spread-out curve at a suitable `k₀`-point gives a one-dimensional fibre. -/
private theorem exists_algHom_dim_le {k₀ K : Type u} [Field k₀] [IsAlgClosed k₀] [Field K]
    [Algebra k₀ K]
    (A : FGSubalgebra k₀ K) {W C : Scheme.{u}} (f : W ⟶ Spec (.of (A : Subalgebra k₀ K)))
    [IsProper f] (j : C ⟶ W) (φ : C ⟶ Spec (.of K))
    (hpb : IsPullback j φ f (Spec.map (CommRingCat.ofHom (algebraMap (A : Subalgebra k₀ K) K))))
    (hC : topologicalKrullDim C ≤ 1) :
    ∃ (t : (A : Subalgebra k₀ K) →ₐ[k₀] k₀) (Y : Scheme.{u}) (qY : Y ⟶ W) (gY : Y ⟶ Spec (.of k₀)),
      IsPullback qY gY f (Spec.map (CommRingCat.ofHom t.toRingHom)) ∧
        topologicalKrullDim Y ≤ 1 := by
  let p : Spec (.of K) ⟶ Spec (.of (A : Subalgebra k₀ K)) :=
    Spec.map (CommRingCat.ofHom (algebraMap (A : Subalgebra k₀ K) K))
  have h1 := dim_fiber_le_of_isPullback f j φ p hpb hC (p (IsLocalRing.closedPoint K)) rfl
  obtain ⟨V, hyV, -, -, -, -, -, hV⟩ :=
    exists_affineOpen_fiberDimension_le f (p (IsLocalRing.closedPoint K)) 1 h1
  have hyK : (p (IsLocalRing.closedPoint K)).asIdeal = ⊥ := by
    change Ideal.comap (algebraMap (A : Subalgebra k₀ K) K) (IsLocalRing.closedPoint K).asIdeal = ⊥
    rw [show (IsLocalRing.closedPoint K).asIdeal = ⊥ from IsLocalRing.maximalIdeal_eq_bot]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  obtain ⟨_, ⟨b, rfl⟩, hyb, hbV⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := p (IsLocalRing.closedPoint K)) hyV V.isOpen
  have hb0 : b ≠ 0 := by
    intro hb
    apply hyb
    change b ∈ (p (IsLocalRing.closedPoint K)).asIdeal
    rw [hyK, hb]
    exact Ideal.zero_mem _
  have hbK : (b : K) ≠ 0 := fun h => hb0 (Subtype.ext h)
  let A' : FGSubalgebra k₀ K := ⟨(A : Subalgebra k₀ K) ⊔ Algebra.adjoin k₀ {((b : K))⁻¹},
    A.2.sup ⟨{((b : K))⁻¹}, by simp⟩⟩
  have hbA : (b : K) ∈ (A' : Subalgebra k₀ K) := (le_sup_left : (A : Subalgebra k₀ K) ≤ _) b.2
  have hbi : ((b : K))⁻¹ ∈ (A' : Subalgebra k₀ K) :=
    (le_sup_right : Algebra.adjoin k₀ {((b : K))⁻¹} ≤ (A' : Subalgebra k₀ K))
      (Algebra.subset_adjoin rfl)
  obtain ⟨t'⟩ := nonempty_algHom_fgSubalgebra' k₀ K A'
  let t : (A : Subalgebra k₀ K) →ₐ[k₀] k₀ :=
    t'.comp (Subalgebra.inclusion (le_sup_left : (A : Subalgebra k₀ K) ≤ _))
  have htb : t b ≠ 0 := by
    intro h0
    have hmul : (⟨(b : K), hbA⟩ : (A' : Subalgebra k₀ K)) * ⟨((b : K))⁻¹, hbi⟩ = 1 :=
      Subtype.ext (mul_inv_cancel₀ hbK)
    have := congrArg t' hmul
    have h00 : t' ⟨(b : K), hbA⟩ = 0 := h0
    rw [map_mul, map_one, h00, zero_mul] at this
    exact zero_ne_one this
  let τ : Spec (.of k₀) ⟶ Spec (.of (A : Subalgebra k₀ K)) :=
    Spec.map (CommRingCat.ofHom t.toRingHom)
  have hτV : τ (IsLocalRing.closedPoint k₀) ∈ V := by
    apply hbV
    change b ∉ Ideal.comap t.toRingHom (IsLocalRing.closedPoint k₀).asIdeal
    rw [show (IsLocalRing.closedPoint k₀).asIdeal = ⊥ from IsLocalRing.maximalIdeal_eq_bot,
      Ideal.mem_comap, Ideal.mem_bot]
    exact htb
  have hY : IsPullback (pullback.fst f τ) (pullback.snd f τ) f τ := IsPullback.of_hasPullback f τ
  exact ⟨t, _, _, _, hY, dim_le_of_isPullback_fiber f _ _ τ hY _ rfl (hV _ hτV)⟩

open ProperFlatFibreEulerCharacteristic in
/-- The degree of an invertible module on the push-forward of the fundamental cycle. -/
private theorem exists_oneCycle_degree_eq_eulerSum_sub {k : Type u} [Field k] {Y X₀ : Scheme.{u}}
    (gY : Y ⟶ Spec (.of k)) [IsProper gY] (hY : topologicalKrullDim Y ≤ 1)
    (s₀ : X₀ ⟶ Spec (.of k)) [IsSeparated s₀] [LocallyOfFiniteType s₀] (y : Y ⟶ X₀)
    (hy : y ≫ s₀ = gY) :
    ∃ Z : OneCycle ℝ s₀, ∀ (L : X₀.Modules)
      [SheafOfModules.IsInvertible X₀.presheaf X₀.ringCatSheaf.2 L],
      OneCycle.degree ℝ s₀ L Z =
        ((eulerSum k gY ((Scheme.Modules.pullback y).obj L) -
          eulerSum k gY (SheafOfModules.unit Y.ringCatSheaf) : ℤ) : ℝ) := by
  classical
  let ZY : OneCycle ℤ s₀ :=
    ∑ᶠ C : {C : ProperCurve gY // closure ({C.point} : Set Y) ∈ irreducibleComponents Y},
      ((Module.length (Y.presheaf.stalk C.1.point) (Y.presheaf.stalk C.1.point)).toNat : ℤ) •
        cyclePushforwardOfPoint ℤ s₀ y C.1.point
  refine ⟨Finsupp.mapRange Int.cast Int.cast_zero ZY, fun L _ => ?_⟩
  have hcast : OneCycle.degree ℝ s₀ L (Finsupp.mapRange Int.cast Int.cast_zero ZY) =
      (OneCycle.degree ℤ s₀ L ZY : ℝ) := by
    rw [OneCycle.degree_apply, OneCycle.degree_apply,
      Finsupp.sum_mapRange_index (fun _ => zero_mul _)]
    simp [Finsupp.sum]
  rw [hcast]
  haveI : Stacks.Ample.IsInvertibleModule Y (SheafOfModules.unit Y.ringCatSheaf) := inferInstance
  have hpi : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      ((Scheme.Modules.pullback y).obj L) := inferInstance
  haveI : Stacks.Ample.IsInvertibleModule Y ((Scheme.Modules.pullback y).obj L) :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      Y.presheaf _ _).mpr hpi
  have hcoh : ∀ (H : Y.Modules) [Stacks.Ample.IsInvertibleModule Y H], H.IsCoherent := by
    intro H _
    haveI : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} H 1 :=
      Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme Y H
    exact AlgebraicGeometry.SheafOfModules.isCoherent_of_isInvertible k gY H
  have hu : (SheafOfModules.unit Y.ringCatSheaf).IsCoherent := hcoh _
  haveI : Stacks.Ample.IsInvertibleModule Y (Stacks.RelativeVeryAmple.tensorModules Y
      (SheafOfModules.unit Y.ringCatSheaf) ((Scheme.Modules.pullback y).obj L)) :=
    Stacks.AmplePullbackPart1.isInvertibleModule_tensorModules Y _ _
  have hT : (Stacks.RelativeVeryAmple.tensorModules Y (SheafOfModules.unit Y.ringCatSheaf)
      ((Scheme.Modules.pullback y).obj L)).IsCoherent := hcoh _
  have key := MMP.Chow.eulerCharacteristic_tensorModules_sub_eq_degree_fundamentalCycle hY y hy L
    (SheafOfModules.unit Y.ringCatSheaf)
  have key' : eulerSum k gY (Stacks.RelativeVeryAmple.tensorModules Y
        (SheafOfModules.unit Y.ringCatSheaf) ((Scheme.Modules.pullback y).obj L)) -
      eulerSum k gY (SheafOfModules.unit Y.ringCatSheaf) = OneCycle.degree ℤ s₀ L ZY := key
  have hiso := eulerSum_congr k gY (Stacks.TensorSheafSpellingIso.tensorModulesLeftUnitor Y
    ((Scheme.Modules.pullback y).obj L))
  rw [hiso] at key'
  rw [← key']

omit [IsAlgClosed K] in
/-- A real 1-cycle has intersection number zero with a real Cartier divisor which has intersection
number zero with every proper curve. -/
private theorem intersectionNumber_eq_zero_of_forall_cycle {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) (c : KCartierDivisor ℝ Y)
    (hc : ∀ C : ProperCurve sY, (C.cycle ℝ).intersectionNumber c = 0) (Z : OneCycle ℝ sY) :
    Z.intersectionNumber c = 0 := by
  induction Z using Finsupp.induction_linear with
  | zero => simp [OneCycle.intersectionNumber]
  | add a b ha hb =>
    simp only [OneCycle.intersectionNumber, map_add] at ha hb ⊢
    rw [ha, hb, add_zero]
  | single C r =>
    have h1 : (Finsupp.single C r : OneCycle ℝ sY) = r • C.cycle ℝ := by
      simp [ProperCurve.cycle]
    rw [h1]
    simp only [OneCycle.intersectionNumber, map_smul] at hc ⊢
    rw [hc C, smul_zero]

open AlgebraicGeometry.FieldExtensionDescent CategoryTheory.Limits
  ProperFlatFibreEulerCharacteristic in
omit [IsAlgClosed K] in
/-- Spreading out, cycle version: every proper curve `C ⊆ X` has the same degree against
pull-backs of Cartier divisors as some real 1-cycle on `X₀`. -/
private theorem exists_oneCycle_degree_eq_of_curve
    (h : CategoryTheory.IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) (C : ProperCurve s) :
    ∃ Z₀ : OneCycle ℝ s₀, ∀ (E₀ : X₀.CartierDivisor) (E : X.CartierDivisor),
      MMP.Intersection.IsPullback π E₀ E →
        (C.cycle ℝ).intersectionNumber (KCartierDivisor.ofCartier ℝ E) =
          Z₀.intersectionNumber (KCartierDivisor.ofCartier ℝ E₀) := by
  classical
  obtain ⟨hXint, hdom⟩ := isIntegral_and_isDominant_of_isPullback s₀ s π h hX₀
  have hv : AlgebraicGeometry.IsVariety k₀ s₀ := hX₀.toIsVariety
  haveI : IsIntegral X₀ := hv.toIsIntegral
  haveI : IsSeparated s₀ := inferInstance
  haveI : LocallyOfFiniteType s₀ := inferInstance
  obtain ⟨A, -, W, f, u, j, hfl, hpr, hlf, hu, hpb, hju⟩ :=
    exists_spreading s₀ s π h hX₀ ⟨⊥, Subalgebra.fg_bot⟩ C
  obtain ⟨t, Y, qY, gY, hY, hdimY⟩ := exists_algHom_dim_le A f j (C.ι ≫ s) hpb C.dim_le
  let gA : Spec (.of (A : Subalgebra k₀ K)) ⟶ Spec (.of k₀) :=
    Spec.map (CommRingCat.ofHom (algebraMap k₀ (A : Subalgebra k₀ K)))
  let τ : Spec (.of k₀) ⟶ Spec (.of (A : Subalgebra k₀ K)) :=
    Spec.map (CommRingCat.ofHom t.toRingHom)
  have hτ : τ ≫ gA = 𝟙 _ := specMap_algHom_comp_algebraMap t
  have hqf : qY ≫ f = gY ≫ τ := hY.w
  have hYp : IsProper gY := MorphismProperty.of_isPullback (P := @IsProper) hY hpr
  have hy : (qY ≫ u) ≫ s₀ = gY := by
    rw [Category.assoc, hu, ← Category.assoc, hqf, Category.assoc, hτ, Category.comp_id]
  obtain ⟨Z₀, hZ₀⟩ := exists_oneCycle_degree_eq_eulerSum_sub gY hdimY s₀ (qY ≫ u) hy
  refine ⟨Z₀, fun E₀ E hE => ?_⟩
  haveI : ConnectedSpace (Spec (.of (A : Subalgebra k₀ K))) := inferInstance
  rw [intersectionNumber_cycle_ofCartier, OneCycle.intersectionNumber_ofCartier]
  change _ = OneCycle.degree ℝ s₀ (MMP.CartierDivisor.sheaf E₀) Z₀
  rw [hZ₀]
  norm_cast
  let L₀ := MMP.CartierDivisor.sheaf E₀
  have e : (Scheme.Modules.pullback π).obj L₀ ≅ MMP.CartierDivisor.sheaf E :=
    (nonempty_pullback_sheaf_iso π hE).some
  rw [← degreeOn_eq_of_iso K s C.ι C.dim_le e]
  let F : W.Modules := (Scheme.Modules.pullback u).obj L₀
  have hFi : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 F := inferInstance
  haveI : Stacks.Ample.IsInvertibleModule W F :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      W.presheaf _ _).mpr hFi
  have hA : degreeOn K s C.ι C.dim_le ((Scheme.Modules.pullback π).obj L₀) =
      invertibleCurveDegree K (C.ι ≫ s) C.dim_le ((Scheme.Modules.pullback j).obj F) := by
    change eulerSum K (C.ι ≫ s) ((Scheme.Modules.pullback C.ι).obj
        ((Scheme.Modules.pullback π).obj L₀)) - eulerSum K (C.ι ≫ s) _ =
      eulerSum K (C.ι ≫ s) ((Scheme.Modules.pullback j).obj F) - eulerSum K (C.ι ≫ s) _
    exact congrArg (fun x => x - eulerSum K (C.ι ≫ s) (SheafOfModules.unit C.scheme.ringCatSheaf))
      (eulerSum_congr K (C.ι ≫ s) ((Scheme.Modules.pullbackComp C.ι π).app L₀ ≪≫
        (Scheme.Modules.pullbackCongr hju.symm).app L₀ ≪≫
        ((Scheme.Modules.pullbackComp j u).app L₀).symm))
  have hB := invertibleCurveDegree_eq_of_isPullback f F _ τ j (C.ι ≫ s) qY gY hpb hY C.dim_le
    hdimY
  have hC' : invertibleCurveDegree k₀ gY hdimY ((Scheme.Modules.pullback qY).obj F) =
      eulerSum k₀ gY ((Scheme.Modules.pullback (qY ≫ u)).obj L₀) -
        eulerSum k₀ gY (SheafOfModules.unit Y.ringCatSheaf) := by
    change eulerSum k₀ gY ((Scheme.Modules.pullback qY).obj F) - _ = _
    exact congrArg (fun x => x - eulerSum k₀ gY (SheafOfModules.unit Y.ringCatSheaf))
      (eulerSum_congr k₀ gY ((Scheme.Modules.pullbackComp qY u).app L₀))
  rw [hA, hB, hC']

/-- A real combination of Cartier divisors on `X₀` is numerically trivial if and only if the same
combination of their pull-backs is numerically trivial on the base change. -/
private theorem lmapDomain_mem_numericallyTrivialDivisors_iff
    (h : CategoryTheory.IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀)
    (p : X₀.CartierDivisor → X.CartierDivisor)
    (hp : ∀ D₀, MMP.Intersection.IsPullback π D₀ (p D₀)) (c : KCartierDivisor ℝ X₀) :
    c ∈ numericallyTrivialDivisors s₀ ↔
      Finsupp.lmapDomain ℝ ℝ p c ∈ numericallyTrivialDivisors s := by
  have key : ∀ (C : ProperCurve s) (C₀ : OneCycle ℝ s₀),
      (∀ (E₀ : X₀.CartierDivisor) (E : X.CartierDivisor), MMP.Intersection.IsPullback π E₀ E →
        (C.cycle ℝ).intersectionNumber (KCartierDivisor.ofCartier ℝ E) =
          C₀.intersectionNumber (KCartierDivisor.ofCartier ℝ E₀)) →
      (C.cycle ℝ).intersectionNumber (Finsupp.lmapDomain ℝ ℝ p c) =
        C₀.intersectionNumber c := by
    intro C C₀ hC
    have hlin : ((OneCycle.intersectionPairing (sX := s)).flip (C.cycle ℝ)).comp
        (Finsupp.lmapDomain ℝ ℝ p) = (OneCycle.intersectionPairing (sX := s₀)).flip C₀ := by
      refine Finsupp.lhom_ext fun E r => ?_
      have := hC E (p E) (hp E)
      simp only [OneCycle.intersectionNumber, OneCycle.intersectionPairing,
        KCartierDivisor.ofCartier,
        Finsupp.linearCombination_single, LinearMap.comp_apply, Finsupp.lmapDomain_apply,
        Finsupp.mapDomain_single, LinearMap.flip_apply] at this ⊢
      simp only [LinearMap.smul_apply, one_smul] at this ⊢
      rw [this]
    exact congrArg (fun F => F c) hlin
  rw [mem_numericallyTrivialDivisors, mem_numericallyTrivialDivisors]
  refine ⟨fun hc C => ?_, fun hc C₀ => ?_⟩
  · obtain ⟨Z₀, hZ₀⟩ := exists_oneCycle_degree_eq_of_curve s₀ s π h hX₀ C
    rw [key C Z₀ hZ₀]
    exact intersectionNumber_eq_zero_of_forall_cycle s₀ c hc Z₀
  · obtain ⟨C, hC⟩ := exists_properCurve_degree_eq_of_curve s₀ s π h hX₀ C₀
    rw [← key C (C₀.cycle ℝ) hC]
    exact hc C

end SpreadCycle

open AlgebraicGeometry.FieldExtensionDescent CategoryTheory.Limits in
/-- Descent of a line bundle up to numerical equivalence: every invertible sheaf `L` on the base
change is numerically equivalent to the pull-back of an invertible sheaf `L₀` on `X₀`. -/
private theorem exists_isInvertible_numerically_pullback
    (h : CategoryTheory.IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    ∃ (L₀ : X₀.Modules) (hL₀ : SheafOfModules.IsInvertible X₀.presheaf X₀.ringCatSheaf.2 L₀),
      ∀ C : ProperCurve s, degreeOn K s C.ι C.dim_le L =
        degreeOn K s C.ι C.dim_le ((Scheme.Modules.pullback π).obj L₀) := by
  classical
  obtain ⟨A₁, M, hM, ρ, hρ₁, hρ₂, ⟨eL⟩⟩ := exists_descent s₀ s π h hX₀ L
  obtain ⟨t₀⟩ := nonempty_algHom_fgSubalgebra' k₀ K A₁
  let g₁ : Spec (.of (A₁ : Subalgebra k₀ K)) ⟶ Spec (.of k₀) :=
    Spec.map (CommRingCat.ofHom (algebraMap k₀ (A₁ : Subalgebra k₀ K)))
  let τ₀ : Spec (.of k₀) ⟶ Spec (.of (A₁ : Subalgebra k₀ K)) :=
    Spec.map (CommRingCat.ofHom t₀.toRingHom)
  have hτ₀ : τ₀ ≫ g₁ = 𝟙 _ := specMap_algHom_comp_algebraMap t₀
  let σ₀ : X₀ ⟶ pullback g₁ s₀ := pullback.lift (s₀ ≫ τ₀) (𝟙 X₀) (by
    rw [Category.assoc, hτ₀, Category.comp_id, Category.id_comp])
  have hσ₁ : σ₀ ≫ pullback.fst g₁ s₀ = s₀ ≫ τ₀ := pullback.lift_fst _ _ _
  have hσ₂ : σ₀ ≫ pullback.snd g₁ s₀ = 𝟙 _ := pullback.lift_snd _ _ _
  haveI hL₀ : SheafOfModules.IsInvertible X₀.presheaf X₀.ringCatSheaf.2
      ((Scheme.Modules.pullback σ₀).obj M) := inferInstance
  refine ⟨(Scheme.Modules.pullback σ₀).obj M, hL₀, fun C => ?_⟩
  obtain ⟨A, hle, W, f, u, j, hfl, hpr, hlf, hu, hpb, hju⟩ := exists_spreading s₀ s π h hX₀ A₁ C
  obtain ⟨t₁⟩ := nonempty_algHom_fgSubalgebra' k₀ K A
  let gA : Spec (.of (A : Subalgebra k₀ K)) ⟶ Spec (.of k₀) :=
    Spec.map (CommRingCat.ofHom (algebraMap k₀ (A : Subalgebra k₀ K)))
  let τ : Spec (.of k₀) ⟶ Spec (.of (A : Subalgebra k₀ K)) :=
    Spec.map (CommRingCat.ofHom t₁.toRingHom)
  have hτ : τ ≫ gA = 𝟙 _ := specMap_algHom_comp_algebraMap t₁
  let r : Spec (.of (A : Subalgebra k₀ K)) ⟶ Spec (.of (A₁ : Subalgebra k₀ K)) :=
    Spec.map (CommRingCat.ofHom
      (Subalgebra.inclusion (show (A₁ : Subalgebra k₀ K) ≤ A from hle)).toRingHom)
  have hr : r ≫ g₁ = gA := by
    rw [← Spec.map_comp]
    congr 1
  have hr' : Spec.map (CommRingCat.ofHom (algebraMap (A : Subalgebra k₀ K) K)) ≫ r =
      Spec.map (CommRingCat.ofHom (algebraMap (A₁ : Subalgebra k₀ K) K)) := by
    rw [← Spec.map_comp]
    congr 1
  let v : W ⟶ pullback g₁ s₀ := pullback.lift (f ≫ r) u (by rw [Category.assoc, hr, hu])
  have hv₁ : v ≫ pullback.fst g₁ s₀ = f ≫ r := pullback.lift_fst _ _ _
  have hv₂ : v ≫ pullback.snd g₁ s₀ = u := pullback.lift_snd _ _ _
  have key := eulerSum_spread_eq s₀ g₁ gA r hr M τ hτ τ₀ hτ₀ f u hu v hv₁ hv₂ σ₀ hσ₁ hσ₂
    (Spec.map (CommRingCat.ofHom (algebraMap (A : Subalgebra k₀ K) K))) j (C.ι ≫ s) hpb
  have hιρ : C.ι ≫ ρ = j ≫ v := by
    apply pullback.hom_ext
    · rw [Category.assoc, hρ₁, Category.assoc, hv₁, ← Category.assoc j, hpb.w, Category.assoc,
        hr', Category.assoc]
    · rw [Category.assoc, hρ₂, Category.assoc, hv₂, hju]
  unfold degreeOn invertibleCurveDegree
  congr 1
  have c₁ := ProperFlatFibreEulerCharacteristic.eulerSum_congr K (C.ι ≫ s)
    ((Scheme.Modules.pullback C.ι).mapIso eL ≪≫ (Scheme.Modules.pullbackComp C.ι ρ).app M ≪≫
      (Scheme.Modules.pullbackCongr hιρ).app M ≪≫ ((Scheme.Modules.pullbackComp j v).app M).symm)
  have c₂ := ProperFlatFibreEulerCharacteristic.eulerSum_congr K (C.ι ≫ s)
    ((Scheme.Modules.pullbackComp C.ι π).app ((Scheme.Modules.pullback σ₀).obj M) ≪≫
      (Scheme.Modules.pullbackCongr hju.symm).app _ ≪≫
      ((Scheme.Modules.pullbackComp j u).app ((Scheme.Modules.pullback σ₀).obj M)).symm)
  exact c₁.trans (key.trans c₂.symm)

/-- Every Cartier divisor on the base change is numerically equivalent to a real combination of
pull-backs of Cartier divisors on `X₀`. -/
private theorem exists_sub_mem_numericallyTrivialDivisors
    (h : CategoryTheory.IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀)
    (p : X₀.CartierDivisor → X.CartierDivisor)
    (hp : ∀ D₀, MMP.Intersection.IsPullback π D₀ (p D₀)) (D : X.CartierDivisor) :
    ∃ c : KCartierDivisor ℝ X₀, Finsupp.lmapDomain ℝ ℝ p c - KCartierDivisor.ofCartier ℝ D ∈
      numericallyTrivialDivisors s := by
  obtain ⟨hXint, hdom⟩ := isIntegral_and_isDominant_of_isPullback s₀ s π h hX₀
  haveI : IsIntegral X₀ := hX₀.toIsVariety.toIsIntegral
  obtain ⟨L₀, hL₀, hdeg⟩ :=
    exists_isInvertible_numerically_pullback s₀ s π h hX₀
      (MMP.CartierDivisor.sheaf D)
  obtain ⟨D₀, ⟨e₀'⟩⟩ := exists_nonempty_iso_cartierDivisor_sheaf L₀
  let e₀ := e₀'.symm
  refine ⟨KCartierDivisor.ofCartier ℝ D₀, mem_numericallyTrivialDivisors.mpr fun C => ?_⟩
  have e : (Scheme.Modules.pullback π).obj L₀ ≅ MMP.CartierDivisor.sheaf (p D₀) :=
    ((Scheme.Modules.pullback π).mapIso e₀).symm ≪≫ (nonempty_pullback_sheaf_iso π (hp D₀)).some
  have hmap : Finsupp.lmapDomain ℝ ℝ p (KCartierDivisor.ofCartier ℝ D₀) =
      KCartierDivisor.ofCartier ℝ (p D₀) := by
    simp [KCartierDivisor.ofCartier]
  rw [hmap]
  simp only [OneCycle.intersectionNumber, map_sub, LinearMap.sub_apply, sub_eq_zero]
  change (C.cycle ℝ).intersectionNumber _ = (C.cycle ℝ).intersectionNumber _
  rw [intersectionNumber_cycle_ofCartier, intersectionNumber_cycle_ofCartier]
  congr 1
  norm_cast
  rw [← degreeOn_eq_of_iso K s C.ι C.dim_le e, ← hdeg C]

/-- A chosen pull-back along the base change `π` of each Cartier divisor on `X₀`. -/
private noncomputable def pullbackCartierDivisor
    (h : CategoryTheory.IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) (D₀ : X₀.CartierDivisor) : X.CartierDivisor :=
  (exists_isPullback s₀ s π h hX₀ D₀).choose

private theorem isPullback_pullbackCartierDivisor
    (h : CategoryTheory.IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) (D₀ : X₀.CartierDivisor) :
    MMP.Intersection.IsPullback π D₀ (pullbackCartierDivisor s₀ s π h hX₀ D₀) :=
  (exists_isPullback s₀ s π h hX₀ D₀).choose_spec

/-- The linear map `N¹(X₀)_ℝ → N¹(X)_ℝ` induced by pulling Cartier divisors back along `π`. -/
private noncomputable def numericalDivisorClassesBaseChangeMap
    (h : CategoryTheory.IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) :
    NumericalDivisorClasses s₀ →ₗ[ℝ] NumericalDivisorClasses s :=
  (numericallyTrivialDivisors s₀).mapQ (numericallyTrivialDivisors s)
    (Finsupp.lmapDomain ℝ ℝ (pullbackCartierDivisor s₀ s π h hX₀)) fun c hc =>
      (lmapDomain_mem_numericallyTrivialDivisors_iff s₀ s π h hX₀ _
        (isPullback_pullbackCartierDivisor s₀ s π h hX₀) c).1 hc

private theorem numericalDivisorClassesBaseChangeMap_mk
    (h : CategoryTheory.IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) (c : KCartierDivisor ℝ X₀) :
    numericalDivisorClassesBaseChangeMap s₀ s π h hX₀ (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (Finsupp.lmapDomain ℝ ℝ (pullbackCartierDivisor s₀ s π h hX₀) c) :=
  Submodule.mapQ_apply _ _ _ _

private theorem bijective_numericalDivisorClassesBaseChangeMap
    (h : CategoryTheory.IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) :
    Function.Bijective (numericalDivisorClassesBaseChangeMap s₀ s π h hX₀) := by
  set p := pullbackCartierDivisor s₀ s π h hX₀
  have hp := isPullback_pullbackCartierDivisor s₀ s π h hX₀
  have hiff := lmapDomain_mem_numericallyTrivialDivisors_iff s₀ s π h hX₀ p hp
  set f := numericalDivisorClassesBaseChangeMap s₀ s π h hX₀
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.mem_ker, numericalDivisorClassesBaseChangeMap_mk,
      Submodule.Quotient.mk_eq_zero] at hx
    exact (Submodule.Quotient.mk_eq_zero _).2 ((hiff c).2 hx)
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    suffices Submodule.Quotient.mk c ∈ LinearMap.range f from this
    induction c using Finsupp.induction_linear with
    | zero => exact Submodule.zero_mem _
    | add a b ha hb =>
      rw [Submodule.Quotient.mk_add]
      exact Submodule.add_mem _ ha hb
    | single D r =>
      obtain ⟨c, hc⟩ := exists_sub_mem_numericallyTrivialDivisors s₀ s π h hX₀ p hp D
      have : Finsupp.single D r = r • KCartierDivisor.ofCartier ℝ D := by
        simp [KCartierDivisor.ofCartier]
      rw [this, Submodule.Quotient.mk_smul]
      refine Submodule.smul_mem _ r ⟨Submodule.Quotient.mk c, ?_⟩
      rw [numericalDivisorClassesBaseChangeMap_mk]
      exact (Submodule.Quotient.eq _).2 hc
  exact ⟨hinj, hsurj⟩

/-- The base-change isomorphism `N¹(X₀)_ℝ ≃ₗ[ℝ] N¹(X)_ℝ` of numerical divisor classes along an
algebraically closed base extension `X = X₀ ×_{k₀} K`, induced by pulling Cartier divisors back
along the projection `π`. -/
public noncomputable def numericalDivisorClassesBaseChange
    (h : CategoryTheory.IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) :
    NumericalDivisorClasses s₀ ≃ₗ[ℝ] NumericalDivisorClasses s :=
  LinearEquiv.ofBijective (numericalDivisorClassesBaseChangeMap s₀ s π h hX₀)
    (bijective_numericalDivisorClassesBaseChangeMap s₀ s π h hX₀)

end BaseChange

/-- **Numerical divisor classes are unchanged by algebraically closed base extension.** For
algebraically closed fields `k₀ → K`, a projective variety `X₀` over `k₀` and a base change
`X = X₀ ×_{k₀} K` with projection `π`, the `ℝ`-linear isomorphism
`numericalDivisorClassesBaseChange : N¹(X₀)_ℝ ≃ N¹(X)_ℝ` sends the class of every Cartier divisor
`D₀` on `X₀` to the class of its pull-back along `π`. -/
@[mmp "lem_oai4_numerical_extension"]
public theorem numericalDivisorClassesBaseChange_eq_of_isPullback
    {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K] [IsAlgClosed k₀] [IsAlgClosed K]
    {X₀ X : Scheme.{u}} (s₀ : X₀ ⟶ Spec (.of k₀)) (s : X ⟶ Spec (.of K)) (π : X ⟶ X₀)
    (h : CategoryTheory.IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) :
    ∀ (D₀ : X₀.CartierDivisor) (D : X.CartierDivisor), MMP.Intersection.IsPullback π D₀ D →
      numericalDivisorClassesBaseChange s₀ s π h hX₀
          (numericalDivisorClass s₀ (KCartierDivisor.ofCartier ℝ D₀)) =
        numericalDivisorClass s (KCartierDivisor.ofCartier ℝ D) := by
  intro D₀ D hD
  rw [hD.unique (isPullback_pullbackCartierDivisor s₀ s π h hX₀ D₀)]
  change numericalDivisorClassesBaseChangeMap s₀ s π h hX₀ (Submodule.Quotient.mk _) =
    Submodule.Quotient.mk _
  rw [numericalDivisorClassesBaseChangeMap_mk]
  simp [KCartierDivisor.ofCartier]

end MMP.Fourfold
