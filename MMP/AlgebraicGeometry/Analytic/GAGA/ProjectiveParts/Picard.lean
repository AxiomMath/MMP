module

public import MMP.AlgebraicGeometry.Analytic.GAGA.Projective
public import MMP.AlgebraicGeometry.Analytic.GAGA.ProjectiveCohomology
public import MMP.AlgebraicGeometry.Analytic.GAGA.Stalks

/-!
# GAGA for line bundles on a projective scheme over `ℂ`

Part (3) of `MMP.Analytic.analytification_gaga_projective`, stated over named pieces. Let `X` be a
projective scheme over `ℂ` with analytification `X^an` and `L ↦ L^an` the analytification of
`𝒪_X`-modules (`MMP.Analytic.analytifyModule`).

## Main definitions

* `MMP.Analytic.IsLocallyTrivial`: a sheaf of modules on a space is locally isomorphic to the
  structure sheaf.
* `MMP.Analytic.analytifyTensorIso`: `(L ⊗ L')^an ≅ L^an ⊗ L'^an`.
* `MMP.Analytic.picardEquiv`: the group isomorphism `Pic X ≃* Pic X^an`, `[L] ↦ [L^an]`.
* `MMP.Analytic.algebraicLineBundle`, `MMP.Analytic.analytifyAlgebraicLineBundleIso`: an
  algebraic line bundle whose analytification is a given analytic line bundle.
* `MMP.Analytic.isoOfAnalytifyIso`: an isomorphism `L ≅ L'` of algebraic line bundles from one
  `L^an ≅ L'^an`.
* `MMP.Analytic.globalSectionsComparisonIso`: `H^0(X, 𝒪_X) ≅ H^0(X^an, 𝒪_X^an)`, the comparison
  map in degree `0` on the structure sheaf.

## Main statements

* `MMP.Analytic.isLocallyTrivial_analytify`: analytification preserves local triviality.
* `MMP.Analytic.picardEquiv_schemeClassOf`: `picardEquiv [L] = [L^an]`.
* `MMP.Analytic.exists_analytify_iso_of_isLocallyTrivial`: every analytic line bundle is the
  analytification of an algebraic one.
* `MMP.Analytic.nonempty_iso_of_nonempty_analytify_iso`: line bundles with isomorphic
  analytifications are isomorphic.
* `MMP.Analytic.isIso_comparisonMap_unit_zero`: the comparison map is an isomorphism on global
  sections of the structure sheaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open MMP.Analytic.Analytification

namespace MMP.Analytic

/-- A sheaf of modules `M` on a topological space is *locally trivial* if every point has an open
neighbourhood `U` with `M|_U ≅ 𝒪|_U`. -/
def IsLocallyTrivial {T : TopCat.{0}} {R : Sheaf (Opens.grothendieckTopology T) RingCat.{0}}
    (M : SheafOfModules.{0} R) : Prop :=
  ∀ x : T, ∃ U : Opens T, x ∈ U ∧ Nonempty (M.over U ≅ SheafOfModules.unit _)

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))

/-- **Analytification commutes with tensor products**: the comparison
`(L ⊗ L')^an ≅ L^an ⊗ L'^an` of the pullback along `X^an → X`. -/
noncomputable def analytifyTensorIso (L L' : X.Modules) :
    (analytifyModule sX).obj (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj L).obj L') ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor (structureSheaf sX)).obj
        ((analytifyModule sX).obj L)).obj ((analytifyModule sX).obj L') :=
  @asIso _ _ _ _ (Stacks.RingedSpace.comparison (analytificationHom sX) L L')
    (Stacks.PullbackTensorIso.isIso_comparison (analytificationHom sX) L L')

/-- The forward map of `MMP.Analytic.analytifyTensorIso` is the pullback–tensor comparison map. -/
@[simp]
theorem analytifyTensorIso_hom (L L' : X.Modules) :
    (analytifyTensorIso sX L L').hom =
      Stacks.RingedSpace.comparison (analytificationHom sX) L L' :=
  rfl

/-- **Analytification preserves local triviality**: if `L` is locally trivial on `X`, then so is
`L^an` on `X^an`. -/
theorem isLocallyTrivial_analytify [LocallyOfFiniteType sX] [QuasiCompact sX] (L : X.Modules)
    (hL : IsLocallyTrivial L) : IsLocallyTrivial ((analytifyModule sX).obj L) :=
  (analytification_stalks sX).2.2.2.2.2.2.1 L hL

/-- A locally trivial sheaf of modules on a ringed space is invertible. -/
private theorem isInvertible_of_isLocallyTrivial (Y : RingedSpace.{0})
    (L : _root_.SheafOfModules.{0} (structureSheaf Y.sheaf)) (h : IsLocallyTrivial L) :
    Stacks.SheafOfModules.IsInvertible Y.sheaf.obj (structureSheaf Y.sheaf).property L := by
  choose U hU e using h
  haveI : Stacks.SheafOfModules.Invertible.IsLocallyTrivial L :=
    ⟨Y, U, (Opens.coversTop_iff _ U).2 (TopologicalSpace.IsOpenCover.mk (eq_top_iff.mpr
      fun y _ => Opens.mem_iSup.mpr ⟨y, hU y⟩)), e⟩
  haveI : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank L 1 :=
    ⟨(Stacks.SheafOfModules.Invertible.isFiniteLocallyFreeOfRank_one_of_isLocallyTrivial
      L).exists_isFiniteLocallyFreeOfRankData⟩
  exact Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one Y L

/-- An invertible module on a scheme is locally trivial. -/
private theorem isLocallyTrivial_of_isInvertibleModule (L : X.Modules)
    [hL : Stacks.Ample.IsInvertibleModule X L] : IsLocallyTrivial L := by
  intro x
  haveI : ∀ x : X.toRingedSpace.carrier,
      IsLocalRing (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X.toRingedSpace x) :=
    X.isLocalRing
  haveI : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L := hL
  obtain ⟨I, Xs, hXs, hiso⟩ := (Stacks.SheafOfModules.Invertible.isLocallyTrivial_of_isInvertible
    (X := X.toRingedSpace) L).exists_trivializing_cover
  obtain ⟨i, hi⟩ := ((Opens.coversTop_iff (U := Xs)).1 hXs).exists_mem x
  exact ⟨Xs i, hi, hiso i⟩

/-- **Analytification preserves invertibility.** -/
theorem isInvertible_analytifyModule (L : X.Modules) (hL : Stacks.Ample.IsInvertibleModule X L) :
    SheafOfModules.IsInvertible (J := Opens.grothendieckTopology (space sX))
      (structureSheaf sX).obj (ringCatSheaf sX).2 ((analytifyModule sX).obj L) := by
  have h1 := (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).2 hL
  obtain ⟨N, ⟨e⟩⟩ := (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit L).1 h1
  refine (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).1 ?_
  exact (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit _).2
    ⟨(analytifyModule sX).obj N, ⟨(analytifyTensorIso sX L N).symm ≪≫
      (analytifyModule sX).mapIso e ≪≫ analytifyUnitIso sX⟩⟩

/-- **GAGA for Picard groups**: the group isomorphism `Pic X ≃* Pic X^an` of
`MMP.Analytic.exists_mulEquiv_picardGroup_analytification_of_isProjective`; it sends `[L]` to
`[L^an]` (`MMP.Analytic.picardEquiv_schemeClassOf`). -/
noncomputable def picardEquiv (hX : IsProjective sX) :
    Stacks.SheafPicardGroup.schemePicardGroup X ≃*
      Stacks.SheafPicardGroup.PicardGroup (J := Opens.grothendieckTopology (space sX))
      (structureSheaf sX).obj (ringCatSheaf sX).2 :=
  (exists_mulEquiv_picardGroup_analytification_of_isProjective sX hX).choose_spec.choose

/-- `MMP.Analytic.picardEquiv` sends the class of an invertible `L` to the class of `L^an`. -/
theorem picardEquiv_schemeClassOf (hX : IsProjective sX) (L : X.Modules)
    [hL : Stacks.Ample.IsInvertibleModule X L] :
    picardEquiv sX hX (Stacks.SheafPicardGroup.schemeClassOf X L) =
      @Stacks.SheafPicardGroup.classOf _ _ (Opens.grothendieckTopology (space sX))
        (structureSheaf sX).obj (ringCatSheaf sX).2 _ _ ((analytifyModule sX).obj L)
        (isInvertible_analytifyModule sX L hL) :=
  (exists_mulEquiv_picardGroup_analytification_of_isProjective sX hX).choose_spec.choose_spec.1 L

/-- **Essential surjectivity on line bundles.** Every locally trivial module on `X^an` is the
analytification of a locally trivial module on `X`. -/
theorem exists_analytify_iso_of_isLocallyTrivial (hX : IsProjective sX)
    (M : SheafOfModules.{0} (ringCatSheaf sX)) (hM : IsLocallyTrivial M) :
    ∃ L : X.Modules, IsLocallyTrivial L ∧ Nonempty ((analytifyModule sX).obj L ≅ M) := by
  haveI : AlgebraicGeometry.SheafOfModules.IsInvertible
      (J := Opens.grothendieckTopology (space sX)) (structureSheaf sX).obj (ringCatSheaf sX).2 M :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ M).1
      (isInvertible_of_isLocallyTrivial (analytification sX) M hM)
  obtain ⟨L, hL, hLe⟩ := Stacks.SheafPicardGroup.exists_classOf _ _
    ((picardEquiv sX hX).symm (Stacks.SheafPicardGroup.classOf
      (J := Opens.grothendieckTopology (space sX)) (structureSheaf sX).obj (ringCatSheaf sX).2 M))
  haveI : Stacks.Ample.IsInvertibleModule X L := hL
  haveI := isInvertible_analytifyModule sX L hL
  refine ⟨L, isLocallyTrivial_of_isInvertibleModule L,
    (Stacks.SheafPicardGroup.classOf_eq_classOf_iff
      (J := Opens.grothendieckTopology (space sX)) (structureSheaf sX).obj (ringCatSheaf sX).2
      ((analytifyModule sX).obj L) M).1 ?_⟩
  rw [← picardEquiv_schemeClassOf sX hX L,
    show Stacks.SheafPicardGroup.schemeClassOf X L = _ from hLe, MulEquiv.apply_symm_apply]

/-- A locally trivial module on `X` whose analytification is the locally trivial module `M` on
`X^an` (chosen by `MMP.Analytic.exists_analytify_iso_of_isLocallyTrivial`). -/
noncomputable def algebraicLineBundle (hX : IsProjective sX)
    (M : SheafOfModules.{0} (ringCatSheaf sX)) (hM : IsLocallyTrivial M) : X.Modules :=
  (exists_analytify_iso_of_isLocallyTrivial sX hX M hM).choose

/-- `MMP.Analytic.algebraicLineBundle` is locally trivial. -/
theorem isLocallyTrivial_algebraicLineBundle (hX : IsProjective sX)
    (M : SheafOfModules.{0} (ringCatSheaf sX)) (hM : IsLocallyTrivial M) :
    IsLocallyTrivial (algebraicLineBundle sX hX M hM) :=
  (exists_analytify_iso_of_isLocallyTrivial sX hX M hM).choose_spec.1

/-- The isomorphism `(algebraicLineBundle M)^an ≅ M`. -/
noncomputable def analytifyAlgebraicLineBundleIso (hX : IsProjective sX)
    (M : SheafOfModules.{0} (ringCatSheaf sX)) (hM : IsLocallyTrivial M) :
    (analytifyModule sX).obj (algebraicLineBundle sX hX M hM) ≅ M :=
  (exists_analytify_iso_of_isLocallyTrivial sX hX M hM).choose_spec.2.some

/-- **Analytification reflects isomorphism of line bundles.** Two locally trivial modules on `X`
with isomorphic analytifications are isomorphic. -/
theorem nonempty_iso_of_nonempty_analytify_iso (hX : IsProjective sX) (L L' : X.Modules)
    (hL : IsLocallyTrivial L) (hL' : IsLocallyTrivial L')
    (h : Nonempty ((analytifyModule sX).obj L ≅ (analytifyModule sX).obj L')) :
    Nonempty (L ≅ L') := by
  haveI : Stacks.Ample.IsInvertibleModule X L :=
    isInvertible_of_isLocallyTrivial X.toRingedSpace L hL
  haveI : Stacks.Ample.IsInvertibleModule X L' :=
    isInvertible_of_isLocallyTrivial X.toRingedSpace L' hL'
  haveI := isInvertible_analytifyModule sX L ‹_›
  haveI := isInvertible_analytifyModule sX L' ‹_›
  replace h := (Stacks.SheafPicardGroup.classOf_eq_classOf_iff
    (J := Opens.grothendieckTopology (space sX)) (structureSheaf sX).obj (ringCatSheaf sX).2
    ((analytifyModule sX).obj L) ((analytifyModule sX).obj L')).2 h
  rw [← picardEquiv_schemeClassOf sX hX L, ← picardEquiv_schemeClassOf sX hX L'] at h
  exact (Stacks.SheafPicardGroup.schemeClassOf_eq_schemeClassOf_iff X L L').1
    ((picardEquiv sX hX).injective h)

/-- An isomorphism `L ≅ L'` of locally trivial modules on `X` with isomorphic analytifications
(chosen by `MMP.Analytic.nonempty_iso_of_nonempty_analytify_iso`). -/
noncomputable def isoOfAnalytifyIso (hX : IsProjective sX) (L L' : X.Modules)
    (hL : IsLocallyTrivial L) (hL' : IsLocallyTrivial L')
    (t : (analytifyModule sX).obj L ≅ (analytifyModule sX).obj L') :
    L ≅ L' :=
  (nonempty_iso_of_nonempty_analytify_iso sX hX L L' hL hL' ⟨t⟩).some

/-- The comparison map `H^0(X, 𝒪_X) → H^0(X^an, 𝒪_X^an)` is an isomorphism. -/
theorem isIso_comparisonMap_unit_zero (hX : IsProjective sX) :
    IsIso (comparisonMap sX (SheafOfModules.unit _) 0) := by
  haveI : IsProper sX := hX.isProper
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  exact isIso_comparisonMap_of_isProjective sX hX _
    (AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent
      (Stacks.AlgebraicGeometry.CoherentKernel.structureSheaf_isCoherent X)) 0

/-- **GAGA for global functions**: the comparison isomorphism `H^0(X, 𝒪_X) ≅ H^0(X^an, 𝒪_X^an)`,
whose forward map is `comparisonMap sX 𝒪_X 0`. -/
noncomputable def globalSectionsComparisonIso (hX : IsProjective sX) :
    (sheafCohomology _ 0).obj
        ((SheafOfModules.toSheaf _).obj (SheafOfModules.unit X.ringCatSheaf)) ≅
      (sheafCohomology (space sX) 0).obj ((SheafOfModules.toSheaf _).obj
        ((analytifyModule sX).obj (SheafOfModules.unit X.ringCatSheaf))) :=
  @asIso _ _ _ _ (comparisonMap sX (SheafOfModules.unit _) 0) (isIso_comparisonMap_unit_zero sX hX)

/-- The forward map of `MMP.Analytic.globalSectionsComparisonIso` is the comparison map. -/
@[simp]
theorem globalSectionsComparisonIso_hom (hX : IsProjective sX) :
    (globalSectionsComparisonIso sX hX).hom = comparisonMap sX (SheafOfModules.unit _) 0 :=
  rfl

end MMP.Analytic

end
