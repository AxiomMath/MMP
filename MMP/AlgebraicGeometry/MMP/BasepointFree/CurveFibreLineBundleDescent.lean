module

public import MMP.AlgebraicGeometry.Intersection.NumTrivialLineBundleCurve
public import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.SurfaceMatrix
public import StacksFrontier.AlgebraicGeometry.Chow.NormalConeZeroSectionGysin
public import StacksFrontier.AlgebraicGeometry.Descent.CounitFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.PicardFibreTrivial.FibreNeighbourhood
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.FibreFirstCohomology

/-!
# Descent of a numerically trivial invertible sheaf along a morphism with curve fibres

Let `f : Y ⟶ X` be a projective morphism of normal quasi-projective complex varieties such that
the canonical map `𝒪_X ⟶ f_* 𝒪_Y` is an isomorphism, `R¹ f_* 𝒪_Y = 0`, and every fibre of `f`
has dimension at most one. If an invertible sheaf `L` on `Y` has degree zero on every proper curve
contracted by `f`, then `f_* L` is invertible and the counit `f^* f_* L ⟶ L` is an isomorphism;
in particular `L` is the pull-back of an invertible sheaf on `X`.

At a closed point `x` of `X` the fibre `Y_x` is connected, proper over `κ(x) = ℂ`, of dimension
at most one, and has `H¹(Y_x, 𝒪) = 0` ([Stacks, Tag 0E7F]); `L` has degree zero on its integral
curves, which are proper curves of `Y` contracted by `f`, so `L|_{Y_x}` is trivial. By the theorem
on formal functions the trivialization extends over `f⁻¹ V` for an open neighbourhood `V` of `x`
([Stacks, Tag 0E24]). Over such a `V` the restriction of `f_* L` is `(f ∣_ V)_* 𝒪 = 𝒪_V`, and the
counit is an isomorphism on the stalks at every point of `f⁻¹ V`: over `V` it is the counit of
`f ∣_ V` at the trivial module, carried back along the open immersion by degree-zero flat base
change ([Stacks, Tag 02KH]). Every point of `X` specializes to a closed point, so these
neighbourhoods cover `X`.

## Main results

* `MMP.Mori.isInvertible_pushforward_and_isIso_counit_of_forall_degree_eq_zero`.

## Implementation notes

The map `𝒪_X ⟶ f_* 𝒪_Y` is `SheafOfModules.unitToPushforwardObjUnit`, induced by `f^♯`;
`R¹ f_*` is the first right derived functor of `AlgebraicGeometry.Scheme.Modules.pushforward f`;
the evaluation `f^* f_* L ⟶ L` is the counit of
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f`. A curve is contracted when
`f` is constant on it (`MMP.Mori.ProperCurve.IsContractedBy`), and the fibre over `x` is the
scheme `AlgebraicGeometry.Scheme.Hom.fiber f x`, of topological Krull dimension at most one.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
* [Stacks Project, Tag 0E24](https://stacks.math.columbia.edu/tag/0E24)
* [Stacks Project, Tag 0E7F](https://stacks.math.columbia.edu/tag/0E7F)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

attribute [local instance 2000] HasDerivedCategory.standard

namespace MMP.Mori

section

variable {X Y : Scheme.{0}}

/-- `𝒪_X ≅ f_* 𝒪_Y` makes every `f.app W` an isomorphism. -/
private theorem isIso_app_of_isIso_unitToPushforwardObjUnit (f : Y ⟶ X)
    (hunit : IsIso (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) (W : X.Opens) :
    IsIso (f.app W) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ConcreteCategory.bijective_of_isIso
    ((PresheafOfModules.evaluation _ (Opposite.op W)).map
      ((SheafOfModules.forget _).map (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)))

/-- `𝒪_X ≅ f_* 𝒪_Y` makes the comorphism `f.c` an isomorphism. -/
private theorem isIso_c_of_isIso_unitToPushforwardObjUnit (f : Y ⟶ X)
    (hunit : IsIso (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) :
    IsIso f.c := by
  have : ∀ W, IsIso (f.c.app W) := fun W =>
    isIso_app_of_isIso_unitToPushforwardObjUnit f hunit W.unop
  exact NatIso.isIso_of_isIso_app _

/-- A proper morphism `f` such that every `f.app W` is an isomorphism is surjective. -/
private theorem surjective_of_forall_isIso_app (f : Y ⟶ X) [IsProper f]
    (h : ∀ W : X.Opens, IsIso (f.app W)) : Function.Surjective f := by
  intro x
  by_contra hx
  push Not at hx
  let W : X.Opens := ⟨(Set.range f)ᶜ, f.isClosedMap.isClosed_range.isOpen_compl⟩
  have hxW : x ∈ W := fun ⟨y, hy⟩ => hx y hy
  haveI : Nonempty W := ⟨⟨x, hxW⟩⟩
  have hbot : f ⁻¹ᵁ W = ⊥ := by
    ext y
    exact iff_of_false (fun h => h ⟨y, rfl⟩) (fun h => h)
  have hsub : Subsingleton Γ(Y, f ⁻¹ᵁ W) := by
    rw [hbot]
    infer_instance
  obtain ⟨_, _, hab⟩ := Scheme.component_nontrivial X W
  exact hab ((ConcreteCategory.bijective_of_isIso (f.app W)).1 (Subsingleton.elim _ _))

/-- The fibre of a projective `f` over a closed point of a variety over `ℂ` is projective over
`ℂ`: it is the base change of `f` along the `ℂ`-point `Spec ℂ ≅ Spec κ(x) ⟶ X`. -/
private theorem isProjective_fiberι_comp {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] (f : Y ⟶ X) (hf : f ≫ sX = sY) (hproj : IsProjectiveMorphism f)
    (x : X) (hx : IsClosed ({x} : Set X)) :
    IsProjective (f.fiberι x ≫ sY) := by
  let e : Spec (X.residueField x) ≅ Spec (.of ℂ) :=
    Scheme.Spec.mapIso (residueFieldIsoBase sX x hx).op.symm
  have sq : IsPullback (f.fiberToSpecResidueField x ≫ e.hom) (f.fiberι x)
      (e.inv ≫ X.fromSpecResidueField x) f :=
    IsPullback.of_iso (IsPullback.of_hasPullback f (X.fromSpecResidueField x)).flip
      (Iso.refl _) e (Iso.refl _) (Iso.refl _) (Category.id_comp _).symm
      ((Category.comp_id _).trans (Category.id_comp _).symm) (by simp) (by simp)
  have heq : f.fiberι x ≫ sY = f.fiberToSpecResidueField x ≫ e.hom := by
    have h1 : f.fiberι x ≫ f = f.fiberToSpecResidueField x ≫ X.fromSpecResidueField x :=
      pullback.condition
    have h2 : e.hom = X.fromSpecResidueField x ≫ sX := by
      rw [← SpecMap_residueFieldIsoBase_inv sX x hx]
      rfl
    rw [← hf, h2, ← Category.assoc, h1, Category.assoc]
  rw [heq]
  exact IsProjective.of_isPullback sq hproj.isProjective

/-- A dimension at most one and not at most zero is one. -/
private theorem eq_one_of_le_one_of_not_le_zero {d : WithBot ℕ∞} (h1 : d ≤ 1) (h0 : ¬ d ≤ 0) :
    d = 1 := by
  induction d using WithBot.recBotCoe with
  | bot => exact absurd bot_le h0
  | coe n =>
    induction n using ENat.recTopCoe with
    | top => exact absurd h1 (by decide)
    | coe m =>
      norm_cast at h0 h1 ⊢
      omega

open Stacks.AlgebraicGeometry in
/-- An integral closed subscheme `C ⊆ Y` lying in the fibre over `x` and proper over `ℂ`, of
dimension at most one, carries degree zero: if `C` is a point the degree vanishes on its discrete
space, and otherwise `C` is the proper curve `{p}⁻` of its generic point `p`, contracted by `f`. -/
private theorem degreeOn_eq_zero_of_isClosedImmersion {sY : Y ⟶ Spec (.of ℂ)} (f : Y ⟶ X)
    (L : Y.Modules) [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    (hdeg : ∀ C : ProperCurve sY, C.IsContractedBy f → C.degree ℂ L = 0) (x : X)
    {C : Scheme.{0}} (j : C ⟶ Y) [IsClosedImmersion j] [IsIntegral C] [IsProper (j ≫ sY)]
    (hC : topologicalKrullDim C ≤ 1) (hj : ∀ c : C, f (j c) = x) :
    degreeOn ℂ sY j hC L = 0 := by
  by_cases h0 : topologicalKrullDim C ≤ 0
  · haveI := ComponentDegrees.discreteTopology_of_isProper_of_topologicalKrullDim_le_zero ℂ
      (j ≫ sY) h0
    exact invertibleCurveDegree_eq_zero_of_discreteTopology ℂ (j ≫ sY) hC _
  have h1 : topologicalKrullDim C = 1 := eq_one_of_le_one_of_not_le_zero hC h0
  set p : Y := j (genericPoint C) with hp
  have hrange : Set.range j = closure {p} := by
    refine subset_antisymm (Set.range_subset_iff.2 fun c => ?_)
      (closure_minimal (Set.singleton_subset_iff.2 ⟨_, rfl⟩) j.isClosedEmbedding.isClosed_range)
    exact specializes_iff_mem_closure.1 ((genericPoint_specializes c).map j.continuous)
  have hker : j.ker = Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure ({p} : Set Y)) := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range, hrange]
    congr 1
    ext1
    exact closure_closure
  haveI : IsIso j.toImage := Stacks.Chow.isIso_toImage_of_isClosedImmersion j
  have hι : j.imageι = inv j.toImage ≫ j := by
    rw [IsIso.eq_inv_comp, Scheme.Hom.toImage_imageι]
  haveI : IsProper (j.imageι ≫ sY) := by
    rw [hι, Category.assoc]
    infer_instance
  have hdimI : topologicalKrullDim j.image = 1 :=
    ((Scheme.homeoOfIso (asIso j.toImage)).isHomeomorph.topologicalKrullDim_eq).symm.trans h1
  have hcurve : IsProperCurve sY p := by
    refine ⟨?_, ?_⟩
    · change topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal _).subscheme = 1
      rw [← hker]
      exact hdimI
    · change IsProper ((Scheme.IdealSheafData.vanishingIdeal _).subschemeι ≫ sY)
      rw [← hker]
      infer_instance
  haveI : IsProper ((Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure ({p} : Set Y))).subschemeι ≫ sY) := hcurve.isProper
  let C' : ProperCurve sY := ⟨p, hcurve⟩
  have hcontr : C'.IsContractedBy f := by
    intro z hz
    change z ∈ closure {p} at hz
    rw [← hrange] at hz
    obtain ⟨c, rfl⟩ := hz
    exact (hj c).trans (hj _).symm
  rw [← hdeg C' hcontr]
  exact (MMP.Threefold.Resolution.degreeOn_eq_of_iso_comp ℂ sY j j.imageι hC hdimI.le
    (asIso j.toImage) (Scheme.Hom.toImage_imageι j) L).trans
    (degreeOn_subschemeι_congr hker _ _ L)

/-- **`L` is trivial on a closed fibre.** The fibre is connected, projective over `ℂ`, of
dimension at most one with `H¹(𝒪) = 0`, and `L` has degree zero on each of its integral curves,
which are proper curves of `Y` contracted by `f`. -/
private theorem nonempty_pullback_fiberι_iso_unit {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)}
    [IsQuasiProjectiveVariety ℂ sX] [IsQuasiProjectiveVariety ℂ sY]
    (f : Y ⟶ X) (hf : f ≫ sX = sY) (hproj : IsProjectiveMorphism f)
    (hunit : IsIso (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom))
    (hfib : ∀ x : X, topologicalKrullDim (f.fiber x) ≤ 1)
    (L : Y.Modules) [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    (hdeg : ∀ C : ProperCurve sY, C.IsContractedBy f → C.degree ℂ L = 0)
    (x : X) (hx : IsClosed ({x} : Set X))
    (hH1 : IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections (f.fiber x)).rightDerived
      1).obj (SheafOfModules.unit (f.fiber x).ringCatSheaf))) :
    Nonempty ((Scheme.Modules.pullback (f.fiberι x)).obj L ≅
      SheafOfModules.unit (f.fiber x).ringCatSheaf) := by
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hproj
  have happ := isIso_app_of_isIso_unitToPushforwardObjUnit f hunit
  obtain ⟨y, hy⟩ := surjective_of_forall_isIso_app f happ x
  haveI : Nonempty (f.fiber x) :=
    ⟨((f.range_fiberι x).symm ▸ hy : y ∈ Set.range (f.fiberι x)).choose⟩
  haveI : ConnectedSpace (f.fiber x) :=
    Stacks.AlgebraicGeometry.connectedSpace_fiber_of_extendsOverNeighbourhood f x
      (isIso_c_of_isIso_unitToPushforwardObjUnit f hunit)
      (fun e he => Stacks.AlgebraicGeometry.Fibres.extendsOverNeighbourhood_of_isProper f x e he)
  refine nonempty_iso_unit_of_degreeOn_eq_zero ℂ (f.fiberι x ≫ sY)
    (isProjective_fiberι_comp f hf hproj x hx) (hfib x)
    (ModuleCat.subsingleton_of_isZero hH1 :)
    _ ?_
  intro C i _ _ _ hC
  haveI : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.1 hx
  haveI : IsClosedImmersion (f.fiberι x) :=
    inferInstanceAs (IsClosedImmersion (pullback.fst f (X.fromSpecResidueField x)))
  haveI : IsProper ((i ≫ f.fiberι x) ≫ sY) := by
    rw [Category.assoc]
    infer_instance
  rw [← MMP.Threefold.Resolution.degreeOn_comp ℂ sY (f.fiberι x) i hC L]
  exact degreeOn_eq_zero_of_isClosedImmersion f L hdeg x (i ≫ f.fiberι x) hC fun c =>
    (f.range_fiberι x ▸ Set.mem_range_self (i c) : f.fiberι x (i c) ∈ f ⁻¹' {x})

/-- In a compact T0 space every point specializes to a closed point. -/
private theorem exists_isClosed_specializes {T : Type*} [TopologicalSpace T] [T0Space T]
    [CompactSpace T] (x' : T) : ∃ x : T, IsClosed ({x} : Set T) ∧ x' ⤳ x := by
  obtain ⟨x, hx, hcl⟩ := IsClosed.exists_closed_singleton isClosed_closure
    (closure_nonempty_iff.2 (Set.singleton_nonempty x'))
  exact ⟨x, hcl, specializes_iff_mem_closure.2 hx⟩

open Stacks.AlgebraicGeometry in
/-- **Local triviality near a closed fibre.** For a closed point `x`, there is an open
neighbourhood `V` of `x` over which `L` restricted to `f⁻¹ V` is trivial. -/
private theorem exists_restrict_iso_unit_of_isClosed {sX : X ⟶ Spec (.of ℂ)}
    {sY : Y ⟶ Spec (.of ℂ)} [IsQuasiProjectiveVariety ℂ sX] [IsQuasiProjectiveVariety ℂ sY]
    (f : Y ⟶ X) (hf : f ≫ sX = sY) (hproj : IsProjectiveMorphism f)
    (hunit : IsIso (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom))
    (hR1 : IsZero (((Scheme.Modules.pushforward f).rightDerived 1).obj
      (SheafOfModules.unit Y.ringCatSheaf)))
    (hfib : ∀ x : X, topologicalKrullDim (f.fiber x) ≤ 1)
    (L : Y.Modules) [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    (hdeg : ∀ C : ProperCurve sY, C.IsContractedBy f → C.degree ℂ L = 0)
    (x : X) (hx : IsClosed ({x} : Set X)) :
    ∃ V : X.Opens, x ∈ V ∧ Nonempty (L.restrict (f ⁻¹ᵁ V).ι ≅
      SheafOfModules.unit (f ⁻¹ᵁ V).toScheme.ringCatSheaf) := by
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hproj
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  -- `H¹(Y_x, 𝒪) = 0`, [Stacks, Tag 0E7F].
  have hH1 : IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections (f.fiber x)).rightDerived
      1).obj (SheafOfModules.unit (f.fiber x).ringCatSheaf)) := by
    have hR : IsZero (TopDegreeBaseChange.firstDirectImageStructureSheaf f) :=
      (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff _ (n := 1) rfl _).2 hR1
    exact (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff _ (n := 1) rfl _).1
      (TopDegreeBaseChange.isZero_firstCohomologyStructureSheaf_fiber_of_isZero_firstDirectImage
        f x (hfib x) hR)
  obtain ⟨e⟩ := nonempty_pullback_fiberι_iso_unit f hf hproj hunit hfib L hdeg x hx hH1
  exact Stacks.PicardFibreTrivial.exists_restrict_iso_unit_of_fiber f x hx (hfib x) hH1 L e

/-- Over an open `V` above which `L` is trivial, `f_* L` is trivial. -/
private theorem nonempty_restrict_pushforward_iso_unit (f : Y ⟶ X)
    (hunit : IsIso (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom))
    (L : Y.Modules) (V : X.Opens)
    (e : L.restrict (f ⁻¹ᵁ V).ι ≅ SheafOfModules.unit (f ⁻¹ᵁ V).toScheme.ringCatSheaf) :
    Nonempty (((Scheme.Modules.pushforward f).obj L).restrict V.ι ≅
      SheafOfModules.unit V.toScheme.ringCatSheaf) := by
  let r := Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso f V
  let eO : (Scheme.Modules.pushforward (f ∣_ V)).obj
      (SheafOfModules.unit (f ⁻¹ᵁ V).toScheme.ringCatSheaf) ≅
      SheafOfModules.unit V.toScheme.ringCatSheaf :=
    (Scheme.Modules.pushforward (f ∣_ V)).mapIso (Scheme.Modules.restrictUnitIso _).symm ≪≫
      (r.app (SheafOfModules.unit Y.ringCatSheaf)).symm ≪≫
      (Scheme.Modules.restrictFunctor V.ι).mapIso
        (asIso (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)).symm ≪≫
      Scheme.Modules.restrictUnitIso _
  exact ⟨r.app L ≪≫ (Scheme.Modules.pushforward (f ∣_ V)).mapIso e ≪≫ eO⟩

/-- The counit is an isomorphism on the stalks at the points of `f⁻¹ V`, for an open `V` above
which `L` is trivial. -/
private theorem isIso_stalk_counit_of_restrict_iso_unit (f : Y ⟶ X) [IsProper f]
    (hunit : IsIso (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom))
    (L : Y.Modules) [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L] (V : X.Opens)
    (e : L.restrict (f ⁻¹ᵁ V).ι ≅ SheafOfModules.unit (f ⁻¹ᵁ V).toScheme.ringCatSheaf)
    (y : Y) (hy : f y ∈ V) :
    IsIso ((TopCat.Presheaf.stalkFunctor Ab y).map
      (Scheme.Modules.Hom.mapPresheaf
        ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app L))) := by
  have H : IsPullback (f ⁻¹ᵁ V).ι (f ∣_ V) f V.ι := (isPullback_morphismRestrict f V).flip
  haveI : L.IsQuasicoherent := Stacks.Divisors.isQuasicoherent_of_isInvertible L
  have hu := VectorBundleCodimensionOne.isIso_unit_app_unit_of_isPullback H
    (VectorBundleCodimensionOne.isIso_unit_app_unit_of_isIso_c f
      (isIso_c_of_isIso_unitToPushforwardObjUnit f hunit))
  let eU : (Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj L ≅
      SheafOfModules.unit (f ⁻¹ᵁ V).toScheme.ringCatSheaf :=
    ((Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).app L).symm ≪≫ e
  have h1 := VectorBundleCodimensionOne.isIso_counit_app_of_iso_free (f ∣_ V) hu
    ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj L) PUnit
    (eU ≪≫ (coproductUniqueIso (fun _ : PUnit => SheafOfModules.unit _)).symm)
  have h2 := VectorBundleCodimensionOne.isIso_pullback_map_counit_of_isPullback H L h1
  exact VectorBundleCodimensionOne.isIso_stalk_of_isIso_pullback_map (f ⁻¹ᵁ V).ι _ h2 ⟨y, hy⟩

end

open Stacks.AlgebraicGeometry in
/-- Let `f : Y ⟶ X` be a projective morphism of normal quasi-projective complex varieties with
`𝒪_X ≅ f_* 𝒪_Y` (via the canonical map), `R¹ f_* 𝒪_Y = 0` and all fibres of dimension at most one.
If an invertible sheaf `L` on `Y` has degree zero on every proper curve contracted by `f`, then
`f_* L` is invertible and the counit `f^* f_* L ⟶ L` is an isomorphism. -/
@[mmp "thm_mmp_lc_bpf_curve_fibre_cartier_descent"]
public theorem isInvertible_pushforward_and_isIso_counit_of_forall_degree_eq_zero
    {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)}
    [IsQuasiProjectiveVariety ℂ sX] [IsQuasiProjectiveVariety ℂ sY] [IsNormal X] [IsNormal Y]
    (f : Y ⟶ X) (hf : f ≫ sX = sY) (hproj : IsProjectiveMorphism f)
    (hunit : IsIso (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom))
    (hR1 : IsZero (((Scheme.Modules.pushforward f).rightDerived 1).obj
      (SheafOfModules.unit Y.ringCatSheaf)))
    (hfib : ∀ x : X, topologicalKrullDim (f.fiber x) ≤ 1)
    (L : Y.Modules) [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    (hdeg : ∀ C : ProperCurve sY, C.IsContractedBy f → C.degree ℂ L = 0) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
        ((Scheme.Modules.pushforward f).obj L) ∧
      IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app L) := by
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hproj
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have hloc := exists_restrict_iso_unit_of_isClosed f hf hproj hunit hR1 hfib L hdeg
  refine ⟨?_, ?_⟩
  · refine TwistMapsInvertible.isInvertibleModule_of_forall_exists_restrict_isoUnit _ fun x' => ?_
    obtain ⟨x, hx, hsp⟩ := exists_isClosed_specializes x'
    obtain ⟨V, hxV, ⟨e⟩⟩ := hloc x hx
    exact ⟨V, hsp.mem_open V.isOpen hxV, nonempty_restrict_pushforward_iso_unit f hunit L V e⟩
  · refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_stalk _ fun y => ?_
    obtain ⟨x, hx, hsp⟩ := exists_isClosed_specializes (f y)
    obtain ⟨V, hxV, ⟨e⟩⟩ := hloc x hx
    exact isIso_stalk_counit_of_restrict_iso_unit f hunit L V e y (hsp.mem_open V.isOpen hxV)

end MMP.Mori

end
