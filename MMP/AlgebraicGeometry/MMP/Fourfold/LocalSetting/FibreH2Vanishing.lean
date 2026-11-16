module
public import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting.ResolutionVanishing
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.CompletionStalkLimit

/-!
# Vanishing of `H²` of the structure sheaf of a fibre in the local setting

In a local setting `(Y, Θ, T, π)`, if the fibre of `π` over `y` has dimension at most two,
then `H²(F_y, 𝒪_{F_y}) = 0`.

Chain fold of: `lem_oai4_local_scheme_fibre_vanishing`.
-/

/-! ### `lem_oai4_local_scheme_fibre_vanishing` -/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits

namespace MMP.Fold06.LemOai4LocalSchemeFibreVanishing

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Fourfold MMP.Mori Stacks.FormalFunctions Stacks.Algebraization
  Stacks.IntertwinedFiltration Stacks.Cohomology.FormalFunctions

section Helpers

variable {X Y : Scheme.{0}} (f : X ⟶ Y) (y : Y)

/-- The closed immersion of the fibre `X_y` into `X' = X ×_Y Spec 𝒪_{Y,y}`: the identification
`X_y ≅ X_1` followed by the inclusion of the first infinitesimal neighbourhood. -/
private noncomputable abbrev fibreι : f.fiber y ⟶ stalkBaseChange f y :=
  (fiberIsoInfinitesimalNeighbourhoodOne f y).hom ≫ infinitesimalιBaseChange f y 1

/-- The fibre is cut out of `X'` by `𝓘 = 𝔪_y 𝒪_{X'}`. -/
private theorem ker_fibreι : (fibreι f y).ker = infinitesimalBaseIdealSheaf f y ^ 1 := by
  rw [Scheme.Hom.ker_comp_of_isIso, ker_infinitesimalιBaseChange]

/-- If the fibre is a Noetherian space of dimension at most two, `H³(X', 𝓘ⁿℱ'/𝓘ⁿ⁺¹ℱ') = 0`:
the layer is a direct image from the fibre, where Grothendieck vanishing applies. -/
private theorem isZero_rightDerived_three_kernel (F : X.Modules) [F.IsQuasicoherent]
    [NoetherianSpace (f.fiber y)] (hdim : topologicalKrullDim (f.fiber y) ≤ 2) (n : ℕ) :
    IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections
      (stalkBaseChange f y)).rightDerived 3).obj
      (kernel (idealPowerQuotientDrop (infinitesimalBaseIdealSheaf f y) (Nat.le_succ n)
        (stalkBaseChangeModule f F y)))) := by
  refine IsZero.of_iso ?_ (Functor.mapIso _
    (idealPowerLayerPushforwardIso _ _ n (fibreι f y) (ker_fibreι f y)))
  rw [isZero_rightDerived_pushforward_iff_isZero_hgroup,
    Stacks.Cohomology.ModuleComparison.isZero_schemeHgroupTop_iff_subsingleton_sheafH]
  exact Stacks.CohomologyVanishing.subsingleton_sheafCohomology_of_noetherianSpace_of_dim_le
    (d := 2) (by exact_mod_cast hdim) (by norm_num) _

/-- Under the same hypotheses `H²(X', ℱ'/𝓘ⁿ⁺¹ℱ') → H²(X', ℱ'/𝓘ⁿℱ')` is surjective, by the
long exact sequence of `0 → 𝓘ⁿℱ'/𝓘ⁿ⁺¹ℱ' → ℱ'/𝓘ⁿ⁺¹ℱ' → ℱ'/𝓘ⁿℱ' → 0`. -/
private theorem surjective_rightDerived_two_map_idealPowerQuotientDrop (F : X.Modules)
    [F.IsQuasicoherent] [NoetherianSpace (f.fiber y)]
    (hdim : topologicalKrullDim (f.fiber y) ≤ 2) (n : ℕ) :
    Function.Surjective (((Stacks.Cohomology.AffineBase.moduleGlobalSections
      (stalkBaseChange f y)).rightDerived 2).map
      (idealPowerQuotientDrop (infinitesimalBaseIdealSheaf f y) (Nat.le_succ n)
        (stalkBaseChangeModule f F y))).hom := by
  have := epi_idealPowerQuotientDrop (infinitesimalBaseIdealSheaf f y) (Nat.le_succ n)
    (stalkBaseChangeModule f F y)
  set φ := idealPowerQuotientDrop (infinitesimalBaseIdealSheaf f y) (Nat.le_succ n)
    (stalkBaseChangeModule f F y)
  have hS : (ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ)).ShortExact :=
    { exact := ShortComplex.exact_kernel φ }
  obtain ⟨δ, -, hex⟩ := Stacks.Cohomology.RightDerivedDelta.exists_delta_exact_composableArrows₅
    hS (Stacks.Cohomology.AffineBase.moduleGlobalSections (stalkBaseChange f y))
  have he : Epi (((Stacks.Cohomology.AffineBase.moduleGlobalSections
      (stalkBaseChange f y)).rightDerived 2).map φ) :=
    ((hex 2).exact 1).epi_f ((isZero_rightDerived_three_kernel f y F hdim n).eq_of_tgt _ _)
  exact (ModuleCat.epi_iff_surjective _).mp he

/-- The tower `n ↦ Hᵖ(X', ℱ'/𝓘ⁿℱ')` of `𝒪_{Y,y}`-modules. -/
private noncomputable abbrev fibreTower (F : X.Modules) (p n : ℕ) : Type :=
  cohomologyOverBase (Y.presheaf.stalk y) (stalkBaseChangeStructure f y) p
    (idealPowerQuotient (infinitesimalBaseIdealSheaf f y) n (stalkBaseChangeModule f F y))

/-- The transition `Hᵖ(X', ℱ'/𝓘ⁿℱ') → Hᵖ(X', ℱ'/𝓘ᵐℱ')` of `fibreTower` for `m ≤ n`. -/
private noncomputable abbrev fibreTowerMap (F : X.Modules) (p : ℕ) {m n : ℕ} (h : m ≤ n) :
    fibreTower f y F p n →ₗ[Y.presheaf.stalk y] fibreTower f y F p m :=
  (cohomologyOverBaseMap (Y.presheaf.stalk y) (stalkBaseChangeStructure f y) p
    (idealPowerQuotientDrop (infinitesimalBaseIdealSheaf f y) h
      (stalkBaseChangeModule f F y))).hom

/-- Lowering the exponent from `n` to `n` is the identity. -/
private theorem idealPowerQuotientDrop_refl {Z : Scheme} (J : Z.IdealSheafData) (M : Z.Modules)
    (n : ℕ) :
    idealPowerQuotientDrop J (le_refl n) M = 𝟙 _ :=
  (cancel_epi (cokernel.π (C := Z.Modules) (idealPowerMultiple J n M).ι)).1 <| by
    rw [idealPowerQuotientDrop_π, Category.comp_id]

/-- The transition of `fibreTower` from `n` to `n` is the identity. -/
private theorem fibreTowerMap_refl (F : X.Modules) (p n : ℕ) (x : fibreTower f y F p n) :
    fibreTowerMap f y F p (le_refl n) x = x :=
  congrArg (fun φ => φ.hom x) (show cohomologyOverBaseMap (Y.presheaf.stalk y)
      (stalkBaseChangeStructure f y) p (idealPowerQuotientDrop (infinitesimalBaseIdealSheaf f y)
        (le_refl n) (stalkBaseChangeModule f F y)) = 𝟙 _ by
    rw [idealPowerQuotientDrop_refl]
    simp only [cohomologyOverBaseMap, CategoryTheory.Functor.map_id])

/-- The transitions of `fibreTower` compose. -/
private theorem fibreTowerMap_comp (F : X.Modules) (p : ℕ) {m k n : ℕ} (hmk : m ≤ k)
    (hkn : k ≤ n) (x : fibreTower f y F p n) :
    fibreTowerMap f y F p hmk (fibreTowerMap f y F p hkn x) =
      fibreTowerMap f y F p (hmk.trans hkn) x :=
  congrArg (fun φ => φ.hom x) (show cohomologyOverBaseMap (Y.presheaf.stalk y)
      (stalkBaseChangeStructure f y) p (idealPowerQuotientDrop (infinitesimalBaseIdealSheaf f y)
        hkn (stalkBaseChangeModule f F y)) ≫ cohomologyOverBaseMap (Y.presheaf.stalk y)
      (stalkBaseChangeStructure f y) p (idealPowerQuotientDrop (infinitesimalBaseIdealSheaf f y)
        hmk (stalkBaseChangeModule f F y)) = _ by
    simp only [cohomologyOverBaseMap, ← CategoryTheory.Functor.map_comp,
      idealPowerQuotientDrop_comp])

/-- **The theorem on formal functions, at a vanishing higher direct image.** If `Rᵖf_*ℱ = 0`
then `lim_n Hᵖ(X', ℱ'/𝓘ⁿℱ') = 0`. -/
private theorem subsingleton_towerLimit [IsLocallyNoetherian Y] [IsProper f] (F : X.Modules)
    [F.IsCoherent] (p : ℕ)
    (hR : IsZero (((Scheme.Modules.pushforward f).rightDerived p).obj F)) :
    Subsingleton (towerLimit (fibreTower f y F p) fun _ _ h => fibreTowerMap f y F p h) := by
  have : Subsingleton (higherDirectImageStalk f F y p) :=
    AddCommGrpCat.subsingleton_of_isZero (Functor.map_isZero
      (Scheme.Modules.toPresheaf Y ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat y) hR)
  have : Subsingleton (AdicCompletion (stalkMaximalIdeal y) (higherDirectImageStalk f F y p)) :=
    ⟨fun _ _ => AdicCompletion.ext fun _ => Subsingleton.elim _ _⟩
  obtain ⟨E⟩ := nonempty_adicCompletionHigherDirectImageStalkEquiv f F y p
  have := E.symm.toEquiv.subsingleton
  exact (Stacks.AdicTowerComparison.towerLimitCongr _ (infinitesimalCohomology f F y p) _
    (fun m n h => (infinitesimalCohomologyMap f F y p m n h).restrictScalars
      (Y.presheaf.stalk y))
    (infinitesimalCohomologyEquiv f F y p)
    (fun m n h x => (infinitesimalCohomologyEquiv_naturality f F y p m n h x).symm) ≪≫ₗ
    towerLimitRestrictScalars (Y.presheaf.stalk y)
      (AdicCompletion (stalkMaximalIdeal y) (Y.presheaf.stalk y))
      (infinitesimalCohomology f F y p) (infinitesimalCohomologyMap f F y p)).toEquiv.subsingleton

/-- In a tower of modules indexed by `ℕ` with functorial transitions, if each consecutive
transition `P (n + 1) → P n` is surjective then so is each projection out of the limit. -/
private theorem surjective_towerLimit_apply {A : Type*} [CommRing A] {P : ℕ → Type*}
    [∀ n, AddCommGroup (P n)] [∀ n, Module A (P n)] (T : (m n : ℕ) → m ≤ n → P n →ₗ[A] P m)
    (hid : ∀ n x, T n n le_rfl x = x)
    (hcomp : ∀ m k n (hmk : m ≤ k) (hkn : k ≤ n) x,
      T m k hmk (T k n hkn x) = T m n (hmk.trans hkn) x)
    (hs : ∀ n, Function.Surjective (T n (n + 1) (Nat.le_succ n))) (k : ℕ) :
    Function.Surjective (fun x : towerLimit P T => x.1 k) := by
  intro z
  let G : (i : ℕ) → P (k + i) := fun i => Nat.rec (motive := fun i => P (k + i)) z
    (fun i g => (hs (k + i) g).choose) i
  have hG : ∀ i, T (k + i) (k + (i + 1)) (by omega) (G (i + 1)) = G i := fun i =>
    (hs (k + i) (G i)).choose_spec
  have hGle : ∀ i j (hij : i ≤ j), T (k + i) (k + j) (by omega) (G j) = G i := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact hid _ _
    | succ j hij ih =>
      rw [← hcomp (k + i) (k + j) (k + (j + 1)) (by omega) (by omega), hG, ih]
  refine ⟨⟨fun n => T n (k + n) (by omega) (G n), fun m n h => ?_⟩, ?_⟩
  · show T m n h (T n (k + n) _ (G n)) = T m (k + m) _ (G m)
    rw [hcomp, ← hGle m n h, hcomp]
  · change T k (k + k) _ (G k) = z
    rw [← hcomp k (k + 0) (k + k) le_rfl (by omega), hGle 0 k (by omega)]
    exact hid _ _

/-- If `R²f_*ℱ = 0` and the fibre over `y` is a Noetherian space of dimension at most two, then
`H²(X', ι_* ι^*ℱ') = 0` for the closed immersion `ι` of the fibre into `X'`. -/
private theorem isZero_rightDerived_pushforward_fibre [IsLocallyNoetherian Y] [IsProper f]
    (F : X.Modules) [F.IsCoherent] [NoetherianSpace (f.fiber y)]
    (hdim : topologicalKrullDim (f.fiber y) ≤ 2)
    (hR : IsZero (((Scheme.Modules.pushforward f).rightDerived 2).obj F)) :
    IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections
      (stalkBaseChange f y)).rightDerived 2).obj
      ((Scheme.Modules.pushforward (fibreι f y)).obj
        ((Scheme.Modules.pullback (fibreι f y)).obj (stalkBaseChangeModule f F y)))) := by
  have := subsingleton_towerLimit f y F 2 hR
  have := (surjective_towerLimit_apply _ (fibreTowerMap_refl f y F 2)
    (fun _ _ _ => fibreTowerMap_comp f y F 2)
    (surjective_rightDerived_two_map_idealPowerQuotientDrop f y F hdim) 1).subsingleton
  refine IsZero.of_iso ?_
    (Functor.mapIso _ (idealQuotientPushforwardIso _ 1 _ (fibreι f y) (ker_fibreι f y))).symm
  exact @ModuleCat.isZero_of_subsingleton _ _ _ this

end Helpers

end MMP.Fold06.LemOai4LocalSchemeFibreVanishing

end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

variable {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
  {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}

open MMP.Fold06.LemOai4LocalSchemeFibreVanishing Stacks.FormalFunctions Stacks.Algebraization
  Stacks.IntertwinedFiltration Stacks.Cohomology.FormalFunctions in
/-- In a local setting `(Y, Θ, T, π)`, if the scheme fibre `F_y = Ỹ ×_Y Spec κ(y)` over a point
`y ∈ Y` (closed or not) has dimension at most two, then `H²(F_y, 𝒪_{F_y}) = 0`. -/
@[mmp "lem_oai4_local_scheme_fibre_vanishing"]
public theorem IsLocalSetting.subsingleton_H_two_pointSettingFibre
    (h : IsLocalSetting sY Θ T π) {y : Y}
    (hy : topologicalKrullDim (pointSettingFibre π y) ≤ 2) :
    Subsingleton (Sheaf.H
      ((SheafOfModules.toSheaf (pointSettingFibre π y).ringCatSheaf).obj
        (SheafOfModules.unit (pointSettingFibre π y).ringCatSheaf)) 2) := by
  haveI : IsProper π := isProper_of_isProjectiveMorphism _ h.isResolution.2.2.2.1
  haveI : IsLocallyNoetherian Yt := LocallyOfFiniteType.isLocallyNoetherian π
  haveI : IsNoetherian (pointSettingFibre π y) := ⟨⟩
  haveI : NoetherianSpace (π.fiber y) :=
    (inferInstance : NoetherianSpace (pointSettingFibre π y))
  haveI := Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit (X := Yt)
  let e : (Scheme.Modules.pullback (fibreι π y)).obj
      (stalkBaseChangeModule π (SheafOfModules.unit Yt.ringCatSheaf) y) ≅
      SheafOfModules.unit (π.fiber y).ringCatSheaf :=
    (Scheme.Modules.pullbackComp _ _).app _ ≪≫
      @asIso _ _ _ _ _ (SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal.{0}
        (fibreι π y ≫ stalkBaseChangeι π y).toRingCatSheafHom)
  refine (Stacks.Cohomology.ModuleComparison.isZero_schemeHgroupTop_iff_subsingleton_sheafH
    (π.fiber y) 2 _).1 <| (isZero_rightDerived_pushforward_iff_isZero_hgroup (fibreι π y) _ 2).1 ?_
  exact (isZero_rightDerived_pushforward_fibre π y _ hy
    (h.isIso_unitToPushforwardObjUnit_and_isZero_rightDerived.2 2 (by norm_num))).of_iso
    (Functor.mapIso _ ((Scheme.Modules.pushforward _).mapIso e.symm))

end MMP.Fourfold
