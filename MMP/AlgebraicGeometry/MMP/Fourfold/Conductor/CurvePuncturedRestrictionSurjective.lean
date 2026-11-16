module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.PuncturedH2Surjective
import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting.GenericRelativeSNCResolution
import MMP.AlgebraicGeometry.Analytic.SmoothCentreSlices
import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.VeryGeneralFibreLineBundles
import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting.EtaleIndependence
import MMP.Topology.Sheaves.LocalSystem.ParallelTransport
import MMP.AlgebraicGeometry.Morphisms.GenericSmoothness
import MMP.AlgebraicGeometry.Analytic.AnalyticMapOpenSubscheme
import MMP.AlgebraicGeometry.Analytic.GAGA.Stalks
import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCanonical
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Divisor.DivisorialSheaf
import MMP.AlgebraicGeometry.Morphisms.Smooth.IrreducibleComponents
import MMP.AlgebraicGeometry.Singularities.Slc.NodeResidueForm
import MMP.AlgebraicGeometry.Singularities.Semismooth.Normalization
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.Morphisms.SmoothHypersurfaceFlag
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.ExceptionalFibreGeneric
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# Surjectivity of the punctured restriction along a curve of singularities

In a local setting `(Y, Θ, T, π)` and for a `π`-adapted open `T° ⊆ T`, the restriction map
`r : (R²π_* ℚ)|_{T°} ⟶ (R²j_* ℚ_{Y_reg})|_{T°}` is surjective on every fibre. Surjectivity is
first shown at one point of `T°`, by slicing transversally to `T`, and then propagated along
the connected curve `T°` by parallel transport of local systems.

## Main results

* `MMP.Fourfold.surjective_localSystemRestrictionFibre`
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace MMP.Fold06.LemMmpConductorCurvePuncturedRestrictionSurjective

open MMP.Fourfold MMP.Mori MMP.Analytic MMP.Analytic.ComplexPoints

section Sheaves

variable {X M : TopCat.{0}}

private theorem stalkToPullbackStalk_map_apply (f : X ⟶ M) {F G : TopCat.Sheaf (ModuleCat.{0} ℚ) M}
    (φ : F ⟶ G) (x : X) (v : ((TopCat.Sheaf.forget _ M).obj F).stalk (f x)) :
    ((TopCat.Presheaf.stalkFunctor _ x).map
        ((TopCat.Sheaf.forget _ X).map ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).map φ))).hom
        ((stalkToPullbackStalk f F x).hom v) =
      (stalkToPullbackStalk f G x).hom
        (((TopCat.Presheaf.stalkFunctor _ (f x)).map ((TopCat.Sheaf.forget _ M).map φ)).hom v) :=
  ConcreteCategory.congr_hom (MMP.Fourfold.stalkToPullbackStalk_naturality f φ x) v

/-- On a connected space, the germ map from global sections of a constant sheaf to a stalk is
bijective. -/
private theorem bijective_germ_top_constantSheaf [ConnectedSpace X] (E : ModuleCat.{0} ℚ) (z : X) :
    Function.Bijective (((TopCat.Sheaf.forget _ X).obj
      ((constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ)).obj E)).germ ⊤ z
        (Opens.mem_top z)).hom := by
  set J := Opens.grothendieckTopology X
  set P : TopCat.Presheaf (ModuleCat.{0} ℚ) X := (Functor.const _).obj E
  set C := (TopCat.Sheaf.forget _ X).obj ((constantSheaf J (ModuleCat.{0} ℚ)).obj E)
  set η : P ⟶ C := toSheafify J P
  have hiso : ∀ y : X, Function.Bijective ((TopCat.Presheaf.stalkFunctor _ y).map η).hom :=
    fun y ↦ (ConcreteCategory.isIso_iff_bijective _).1
      (TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso y _ P)
  have hgerm : ∀ (U : Opens X) (y : X) (hy : y ∈ U) (e : E),
      (C.germ U y hy).hom ((η.app (op U)).hom e) =
        ((TopCat.Presheaf.stalkFunctor _ y).map η).hom ((P.germ U y hy).hom e) :=
    fun U y hy e ↦ (TopCat.Presheaf.stalkFunctor_map_germ_apply U y hy η e).symm
  have hres : ∀ (U : Opens X) (e : E),
      (C.map (homOfLE le_top : U ⟶ ⊤).op).hom ((η.app (op ⊤)).hom e) = (η.app (op U)).hom e :=
    fun U e ↦ (ConcreteCategory.congr_hom (η.naturality (homOfLE (le_top : U ≤ ⊤)).op) e).symm
  have hPinj : ∀ (U : Opens X) (y : X) (hy : y ∈ U) (e : E), (P.germ U y hy).hom e = 0 → e = 0 := by
    intro U y hy e he
    obtain ⟨_, -, _, _, hW⟩ := P.germ_eq y hy hy e 0 (by rw [he, map_zero])
    exact hW
  -- every germ of `C` at `y` is the germ of a constant
  have hloc : ∀ (y : X) (w : C.stalk y), ∃ e : E,
      (C.germ ⊤ y (Opens.mem_top y)).hom ((η.app (op ⊤)).hom e) = w := by
    intro y w
    obtain ⟨p, rfl⟩ := (hiso y).2 w
    obtain ⟨U, hyU, e, rfl⟩ := P.exists_germ_eq p
    refine ⟨e, ?_⟩
    rw [← hgerm, ← hres U e]
    exact (TopCat.Presheaf.germ_res_apply C (homOfLE le_top) y hyU _).symm
  refine ⟨?_, fun w ↦ ?_⟩
  · rw [← LinearMap.ker_eq_bot (f := (C.germ ⊤ z (Opens.mem_top z)).hom), LinearMap.ker_eq_bot']
    intro s hs
    -- the zero locus of the germs of `s` is clopen
    let Z : Set X := {y | (C.germ ⊤ y (Opens.mem_top y)).hom s = 0}
    have hopen : ∀ y : X, ∃ U : Opens X, y ∈ U ∧ ∀ y' ∈ U,
        ((C.germ ⊤ y' (Opens.mem_top y')).hom s = 0 ↔
          (C.germ ⊤ y (Opens.mem_top y)).hom s = 0) := by
      intro y
      obtain ⟨e, he⟩ := hloc y ((C.germ ⊤ y (Opens.mem_top y)).hom s)
      obtain ⟨W, hyW, iU, iV, hW⟩ := C.germ_eq y (Opens.mem_top y) (Opens.mem_top y) _ _ he
      refine ⟨W, hyW, fun y' hy' ↦ ?_⟩
      have hiUV : iU = iV := Subsingleton.elim _ _
      subst hiUV
      have hW' : (C.map iU.op).hom ((η.app (op ⊤)).hom e) = (C.map iU.op).hom s := hW
      have key : ∀ y'' (hy'' : y'' ∈ W), (C.germ ⊤ y'' (Opens.mem_top y'')).hom s =
          ((TopCat.Presheaf.stalkFunctor _ y'').map η).hom ((P.germ W y'' hy'').hom e) := by
        intro y'' hy''
        rw [← hgerm, ← hres W e, show (homOfLE le_top : W ⟶ ⊤) = iU from Subsingleton.elim _ _,
          hW']
        exact (TopCat.Presheaf.germ_res_apply C iU y'' hy'' s).symm
      rw [key y' hy', key y hyW]
      constructor
      · intro h
        have := hPinj W y' hy' e ((LinearMap.ker_eq_bot'.1
          (LinearMap.ker_eq_bot.2 (hiso y').1)) _ h)
        rw [this, map_zero]
        exact map_zero _
      · intro h
        have := hPinj W y hyW e ((LinearMap.ker_eq_bot'.1
          (LinearMap.ker_eq_bot.2 (hiso y).1)) _ h)
        rw [this, map_zero]
        exact map_zero _
    have hZo : IsOpen Z := by
      rw [isOpen_iff_forall_mem_open]
      intro y hy
      obtain ⟨U, hyU, hU⟩ := hopen y
      exact ⟨U, fun y' hy' ↦ (hU y' hy').2 hy, U.isOpen, hyU⟩
    have hZc : IsOpen Zᶜ := by
      rw [isOpen_iff_forall_mem_open]
      intro y hy
      obtain ⟨U, hyU, hU⟩ := hopen y
      exact ⟨U, fun y' hy' h ↦ hy ((hU y' hy').1 h), U.isOpen, hyU⟩
    have hZ : Z = Set.univ :=
      (isClopen_iff.1 ⟨⟨hZc⟩, hZo⟩).resolve_left (Set.nonempty_iff_ne_empty.1 ⟨z, hs⟩)
    refine TopCat.Presheaf.section_ext ((constantSheaf J (ModuleCat.{0} ℚ)).obj E) ⊤ s 0
      fun y _ ↦ ?_
    have : y ∈ Z := hZ ▸ Set.mem_univ y
    exact this.trans (map_zero _).symm
  · exact ⟨_, (hloc z w).choose_spec⟩

/-- On a connected space, the germ map from global sections of a sheaf isomorphic to a constant
sheaf to a stalk is bijective. -/
private theorem bijective_germ_top_of_iso [ConnectedSpace X] {A : TopCat.Sheaf (ModuleCat.{0} ℚ) X}
    {E : ModuleCat.{0} ℚ}
    (e : A ≅ (constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ)).obj E) (z : X) :
    Function.Bijective (((TopCat.Sheaf.forget _ X).obj A).germ ⊤ z (Opens.mem_top z)).hom := by
  set e' := (TopCat.Sheaf.forget _ X).mapIso e
  have h1 : Function.Bijective (e'.hom.app (op ⊤)).hom :=
    (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  have h2 : Function.Bijective ((TopCat.Presheaf.stalkFunctor _ z).map e'.hom).hom :=
    (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  have h3 := bijective_germ_top_constantSheaf E z
  have hc : ∀ s, ((TopCat.Presheaf.stalkFunctor _ z).map e'.hom).hom
      ((((TopCat.Sheaf.forget _ X).obj A).germ ⊤ z (Opens.mem_top z)).hom s) =
      (((TopCat.Sheaf.forget _ X).obj
        ((constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ)).obj E)).germ ⊤ z
          (Opens.mem_top z)).hom ((e'.hom.app (op ⊤)).hom s) :=
    fun s ↦ TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ z (Opens.mem_top z) e'.hom s
  have : Function.Bijective (((TopCat.Presheaf.stalkFunctor _ z).map e'.hom).hom ∘
      (((TopCat.Sheaf.forget _ X).obj A).germ ⊤ z (Opens.mem_top z)).hom) := by
    have heq : (((TopCat.Presheaf.stalkFunctor _ z).map e'.hom).hom ∘
        (((TopCat.Sheaf.forget _ X).obj A).germ ⊤ z (Opens.mem_top z)).hom) =
        (((TopCat.Sheaf.forget _ X).obj
          ((constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ)).obj E)).germ ⊤ z
            (Opens.mem_top z)).hom ∘ (e'.hom.app (op ⊤)).hom := funext hc
    rw [heq]
    exact h3.comp h1
  exact (Function.Bijective.of_comp_iff' h2 _).1 this

/-- Surjectivity of a morphism of sheaves at a stalk spreads along a map from the interval along
which both sheaves become constant. -/
private theorem surjective_stalk_of_interval {F G : TopCat.Sheaf (ModuleCat.{0} ℚ) M} (φ : F ⟶ G)
    (g : TopCat.of unitInterval ⟶ M) {EF EG : ModuleCat.{0} ℚ}
    (eF : (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) g).obj F ≅
      (constantSheaf (Opens.grothendieckTopology (TopCat.of unitInterval))
        (ModuleCat.{0} ℚ)).obj EF)
    (eG : (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) g).obj G ≅
      (constantSheaf (Opens.grothendieckTopology (TopCat.of unitInterval))
        (ModuleCat.{0} ℚ)).obj EG)
    (h0 : Function.Surjective
      ((TopCat.Presheaf.stalkFunctor _ (g 0)).map ((TopCat.Sheaf.forget _ M).map φ)).hom) :
    Function.Surjective
      ((TopCat.Presheaf.stalkFunctor _ (g 1)).map ((TopCat.Sheaf.forget _ M).map φ)).hom := by
  set F' := (TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) g).obj F)
  set G' := (TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) g).obj G)
  set φ' := (TopCat.Sheaf.forget _ _).map ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) g).map φ)
  have bF := bijective_germ_top_of_iso eF
  have bG := bijective_germ_top_of_iso eG
  have sF := MMP.Fourfold.bijective_stalkToPullbackStalk g F
  have sG := MMP.Fourfold.bijective_stalkToPullbackStalk g G
  intro w
  obtain ⟨σG, hσG⟩ := (bG 1).2 ((stalkToPullbackStalk g G 1).hom w)
  obtain ⟨w₀, hw₀⟩ := (sG 0).2 ((G'.germ ⊤ 0 (Opens.mem_top _)).hom σG)
  obtain ⟨v₀, rfl⟩ := h0 w₀
  obtain ⟨σF, hσF⟩ := (bF 0).2 ((stalkToPullbackStalk g F 0).hom v₀)
  have heq : (φ'.app (op ⊤)).hom σF = σG := by
    apply (bG 0).1
    refine (TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ 0 (Opens.mem_top _) φ' σF).symm.trans ?_
    refine (congrArg _ hσF).trans ?_
    exact (stalkToPullbackStalk_map_apply g φ 0 v₀).trans hw₀
  obtain ⟨v₁, hv₁⟩ := (sF 1).2 ((F'.germ ⊤ 1 (Opens.mem_top _)).hom σF)
  refine ⟨v₁, (sG 1).1 ?_⟩
  refine (stalkToPullbackStalk_map_apply g φ 1 v₁).symm.trans ?_
  refine (congrArg _ hv₁).trans ?_
  refine (TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ 1 (Opens.mem_top _) φ' σF).trans ?_
  rw [heq]
  exact hσG

/-- On a path connected, locally path connected space, a morphism of local systems which is
surjective on one stalk is surjective on every stalk. -/
private theorem surjective_stalk_of_isLocalSystem [LocallyPathConnectedSpace M]
    [PathConnectedSpace M]
    {F G : TopCat.Sheaf (ModuleCat.{0} ℚ) M} (hF : IsLocalSystem F) (hG : IsLocalSystem G)
    (φ : F ⟶ G) (x y : M)
    (hx : Function.Surjective
      ((TopCat.Presheaf.stalkFunctor _ x).map ((TopCat.Sheaf.forget _ M).map φ)).hom) :
    Function.Surjective
      ((TopCat.Presheaf.stalkFunctor _ y).map ((TopCat.Sheaf.forget _ M).map φ)).hom := by
  let γ := PathConnectedSpace.somePath x y
  obtain ⟨eF⟩ := hF.nonempty_pullback_path_iso_constantSheaf γ
  obtain ⟨eG⟩ := hG.nonempty_pullback_path_iso_constantSheaf γ
  have key := surjective_stalk_of_interval φ (TopCat.ofHom (γ : C(unitInterval, M))) eF eG
  have h0 : (TopCat.ofHom (γ : C(unitInterval, M))) 0 = x := γ.source
  have h1 : (TopCat.ofHom (γ : C(unitInterval, M))) 1 = y := γ.target
  revert key
  generalize (TopCat.ofHom (γ : C(unitInterval, M))) 0 = p at h0
  generalize (TopCat.ofHom (γ : C(unitInterval, M))) 1 = q at h1
  subst h0 h1
  exact fun key ↦ key hx

end Sheaves

section Germs

variable {A U M : TopCat.{0}}

/-- Every element of a stalk of `R^q p_* ℚ` is the germ of a class. -/
private theorem exists_higherDirectImageGerm_eq (p : A ⟶ M) (q : ℕ) (m : M)
    (w : ((TopCat.Sheaf.forget _ M).obj (higherDirectImage p q)).stalk m) :
    ∃ (V : Opens M) (hV : m ∈ V) (α : rationalCohomology (preimageSpace p V) q),
      (higherDirectImageGerm p q m hV).hom α = w := by
  have hiso := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso (C := ModuleCat.{0} ℚ)
    (𝓕 := directImagePresheaf p q) (p₀ := m)
  obtain ⟨w', rfl⟩ := ((ConcreteCategory.isIso_iff_bijective _).1 hiso).2 w
  obtain ⟨V, hV, α, rfl⟩ := (directImagePresheaf p q).exists_germ_eq w'
  exact ⟨V, hV, α, rfl⟩

/-- If the stalk at `m` of the restriction `R^q p_* ℚ ⟶ R^q j_* ℚ` is surjective, every class on
a punctured neighbourhood `j⁻¹(O)` of `m` is, near `m`, the restriction of a class on `p⁻¹`. -/
private theorem exists_restrict_eq_of_surjective_stalk (p : A ⟶ M) (g : U ⟶ A) {j : U ⟶ M}
    (h : g ≫ p = j) (q : ℕ) (m : M)
    (hs : Function.Surjective ((TopCat.Presheaf.stalkFunctor _ m).map
      ((TopCat.Sheaf.forget _ M).map (higherDirectImageRestriction p g h q))).hom)
    (O : Opens M) (hm : m ∈ O) (γ : rationalCohomology (preimageSpace j O) q) :
    ∃ (W : Opens M) (hWO : W ≤ O) (_ : m ∈ W) (α : rationalCohomology (preimageSpace p W) q),
      (rationalCohomologyMap (preimageRestrict p g h W) q).hom α =
        (rationalCohomologyMap (preimageInclusion j hWO) q).hom γ := by
  obtain ⟨w, hw⟩ := hs ((higherDirectImageGerm j q m hm).hom γ)
  obtain ⟨V, hV, α, rfl⟩ := exists_higherDirectImageGerm_eq p q m w
  have key := stalkFunctor_map_presheafToSheaf_germ p j q (directImageRestriction p g h q) m hV α
  have hw'' : ((TopCat.Presheaf.stalkFunctor _ m).map
      (toSheafify (Opens.grothendieckTopology M) (directImagePresheaf j q))).hom
        (((directImagePresheaf j q).germ V m hV).hom
          (((directImageRestriction p g h q).app (op V)).hom α)) =
      ((TopCat.Presheaf.stalkFunctor _ m).map
        (toSheafify (Opens.grothendieckTopology M) (directImagePresheaf j q))).hom
          (((directImagePresheaf j q).germ O m hm).hom γ) := key.symm.trans hw
  have hiso := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso (C := ModuleCat.{0} ℚ)
    (𝓕 := directImagePresheaf j q) (p₀ := m)
  have hinj := ((ConcreteCategory.isIso_iff_bijective _).1 hiso).1
  obtain ⟨W, hmW, iV, iO, e⟩ := (directImagePresheaf j q).germ_eq m hV hm _ _ (hinj hw'')
  refine ⟨W, iO.le, hmW, (rationalCohomologyMap (preimageInclusion p iV.le) q).hom α, ?_⟩
  have hnat : ((directImageRestriction p g h q).app (op W)).hom
      (((directImagePresheaf p q).map iV.op).hom α) =
      ((directImagePresheaf j q).map iV.op).hom
        (((directImageRestriction p g h q).app (op V)).hom α) :=
    ConcreteCategory.congr_hom ((directImageRestriction p g h q).naturality iV.op) α
  exact hnat.trans e

end Germs

/-- If, at the image `x` of `t ∈ T°(ℂ)`, every class on a punctured neighbourhood `j⁻¹(O)` is
near `x` the restriction of a class on `π⁻¹`, then `r_t` is surjective. -/
private theorem surjective_localSystemRestrictionFibre_of_forall {Y Yt : Scheme.{0}}
    (sY : Y ⟶ Spec (.of ℂ)) {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
    (hπ : IsBiregular π (smoothLocus sY)) (To : (curveScheme T).Opens)
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY))
    (h : ∀ (O : Opens (analyticSpace sY)) (_ : curveOpenInclusion sY To t ∈ O)
      (γ : rationalCohomology (preimageSpace (regularInclusion sY) O) 2),
      ∃ (W : Opens (analyticSpace sY)) (hWO : W ≤ O) (hW : curveOpenInclusion sY To t ∈ W)
        (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY π) W) 2),
        (rationalCohomologyMap (preimageRestrict (resolutionAnalyticMap sY π)
            (analyticMap (regularSection sY hπ) (by rw [← Category.assoc, regularSection_comp]))
            (regularSection_analyticMap_comp sY hπ) W) 2).hom α =
          (rationalCohomologyMap (preimageInclusion (regularInclusion sY) hWO) 2).hom γ) :
    Function.Surjective (localSystemRestrictionFibre sY hπ To t).hom := by
  intro v
  obtain ⟨w, rfl⟩ := (bijective_stalkToPullbackStalk (curveOpenInclusion sY To)
    (regularHigherDirectImage sY 2) t).2 v
  obtain ⟨O, hO, γ, rfl⟩ := exists_higherDirectImageGerm_eq (regularInclusion sY) 2 _ w
  obtain ⟨W, hWO, hW, α, hα⟩ := h O hO γ
  refine ⟨(stalkToPullbackStalk _ _ t).hom
    ((higherDirectImageGerm (resolutionAnalyticMap sY π) 2 _ hW).hom α), ?_⟩
  rw [localSystemRestrictionFibre_germ, hα, higherDirectImageGerm_res]

/-! ### Cohomology along continuous maps -/

section CohomologyMaps

/-- Pullback of classes along a composite, applied to a class. -/
private theorem rationalCohomologyMap_comp_apply {A B C : TopCat.{0}} (f : A ⟶ B) (g : B ⟶ C)
    (q : ℕ) (c : rationalCohomology C q) :
    (rationalCohomologyMap (f ≫ g) q).hom c =
      (rationalCohomologyMap f q).hom ((rationalCohomologyMap g q).hom c) := by
  rw [rationalCohomologyMap_comp]
  rfl

/-- Pullback of classes along a triple composite, applied to a class. -/
private theorem rationalCohomologyMap_comp₃_apply {A B C D : TopCat.{0}} (f : A ⟶ B) (g : B ⟶ C)
    (h : C ⟶ D) (q : ℕ) (c : rationalCohomology D q) :
    (rationalCohomologyMap (f ≫ g ≫ h) q).hom c =
      (rationalCohomologyMap f q).hom ((rationalCohomologyMap g q).hom
        ((rationalCohomologyMap h q).hom c)) := by
  rw [rationalCohomologyMap_comp, rationalCohomologyMap_comp]
  rfl

/-- Pullback of classes along a quadruple composite, applied to a class. -/
private theorem rationalCohomologyMap_comp₄_apply {A B C D E : TopCat.{0}} (f : A ⟶ B)
    (g : B ⟶ C) (h : C ⟶ D) (k : D ⟶ E) (q : ℕ) (c : rationalCohomology E q) :
    (rationalCohomologyMap (f ≫ g ≫ h ≫ k) q).hom c =
      (rationalCohomologyMap f q).hom ((rationalCohomologyMap g q).hom
        ((rationalCohomologyMap h q).hom ((rationalCohomologyMap k q).hom c))) := by
  rw [rationalCohomologyMap_comp, rationalCohomologyMap_comp, rationalCohomologyMap_comp]
  rfl

/-- Pullback of classes along a bijective embedding is injective. -/
private theorem injective_rationalCohomologyMap_of_isEmbedding {A B : TopCat.{0}} (m : A ⟶ B)
    (hm : Topology.IsEmbedding m) (hs : Function.Surjective m) (q : ℕ) :
    Function.Injective (rationalCohomologyMap m q).hom := by
  let e : A ≃ₜ B := hm.toHomeomorphOfSurjective hs
  let n : B ⟶ A := TopCat.ofHom ⟨e.symm, e.symm.continuous⟩
  have hn : n ≫ m = 𝟙 B := TopCat.ext fun y ↦ e.apply_symm_apply y
  intro a a' h
  have h' := congrArg (rationalCohomologyMap n q).hom h
  rwa [← rationalCohomologyMap_comp_apply, ← rationalCohomologyMap_comp_apply, hn,
    rationalCohomologyMap_id] at h'

end CohomologyMaps

/-! ### Lifting `ℂ`-points to open subschemes -/

section LiftPoint

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}

/-- A `ℂ`-point of `X` lying in an open `W` as a `ℂ`-point of `W`. -/
private noncomputable def liftPt (W : X.Opens) (y : ComplexPoints sX) (hy : y.toScheme ∈ W) :
    ComplexPoints (W.ι ≫ sX) :=
  have H : Set.range y.hom.base ⊆ Set.range W.ι.base := by
    rintro _ ⟨p, rfl⟩
    rw [Subsingleton.elim p default, Scheme.Opens.range_ι]
    exact hy
  ⟨IsOpenImmersion.lift W.ι y.hom H,
    by rw [← Category.assoc, IsOpenImmersion.lift_fac, y.hom_comp_structure]⟩

private theorem liftPt_hom (W : X.Opens) (y : ComplexPoints sX) (hy : y.toScheme ∈ W) :
    (liftPt W y hy).hom ≫ W.ι = y.hom :=
  IsOpenImmersion.lift_fac _ _ _

private theorem realize_liftPt (W : X.Opens) (y : ComplexPoints sX) (hy : y.toScheme ∈ W) :
    realize W.ι rfl (liftPt W y hy) = y :=
  ComplexPoints.ext (liftPt_hom W y hy)

/-- A `ℂ`-point of an open `W` is determined by its image in `X`. -/
private theorem eq_of_realize_ι_eq (W : X.Opens) {u v : ComplexPoints (W.ι ≫ sX)}
    (h : realize W.ι rfl u = realize W.ι rfl v) : u = v :=
  (isOpenEmbedding_realize_ι W).injective h

end LiftPoint

/-! ### Scheme-theoretic inputs -/

section SchemeInputs

/-- The affine line is smooth of relative dimension one. -/
private theorem smoothOfRelativeDimension_affineLine (S : Scheme.{0}) :
    SmoothOfRelativeDimension 1 (𝔸(Unit; S) ↘ S) := by
  haveI := Stacks.Chow.smoothOfRelativeDimension_affineSpaceOver S 1
  have hij : AffineSpace.reindex (fun _ : ULift.{0} (Fin 1) ↦ ()) S ≫
      AffineSpace.reindex (fun _ : Unit ↦ (⟨0⟩ : ULift.{0} (Fin 1))) S = 𝟙 _ := by
    apply AffineSpace.hom_ext
    · simp
    · intro k
      cases k
      simp only [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop]
      erw [ConcreteCategory.comp_apply, AffineSpace.reindex_appTop_coord,
        AffineSpace.reindex_appTop_coord]
      rfl
  have hji : AffineSpace.reindex (fun _ : Unit ↦ (⟨0⟩ : ULift.{0} (Fin 1))) S ≫
      AffineSpace.reindex (fun _ : ULift.{0} (Fin 1) ↦ ()) S = 𝟙 _ := by
    apply AffineSpace.hom_ext
    · simp
    · intro k
      rw [show k = ⟨0⟩ from Subsingleton.elim _ _]
      simp only [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop]
      erw [ConcreteCategory.comp_apply, AffineSpace.reindex_appTop_coord,
        AffineSpace.reindex_appTop_coord]
      rfl
  haveI : IsIso (AffineSpace.reindex (fun _ : ULift.{0} (Fin 1) ↦ ()) S) := ⟨⟨_, hij, hji⟩⟩
  have h : AffineSpace.reindex (fun _ : ULift.{0} (Fin 1) ↦ ()) S ≫
      (𝔸(ULift.{0} (Fin 1); S) ↘ S) = 𝔸(Unit; S) ↘ S := AffineSpace.reindex_over _ S
  rw [← h]
  exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)

/-- If `f` is an isomorphism over an open `U` of its target and `f ≫ g` is smooth, then `g` is
smooth on `U`. -/
private theorem smooth_ι_comp_of_isIso_morphismRestrict {X Y S : Scheme.{0}} (f : X ⟶ Y)
    (g : Y ⟶ S) (U : Y.Opens) [IsIso (f ∣_ U)] [Smooth (f ≫ g)] : Smooth (U.ι ≫ g) := by
  rw [← IsIso.inv_hom_id_assoc (f ∣_ U) (U.ι ≫ g), ← Category.assoc (f ∣_ U),
    morphismRestrict_ι, Category.assoc]
  infer_instance

/-- The image of an open subscheme that is smooth over `ℂ` lies in the smooth locus. -/
private theorem image_le_smoothLocus {Y X : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) (j : X ⟶ Y)
    [IsOpenImmersion j] (U : X.Opens) (hU : Smooth (U.ι ≫ j ≫ sY)) :
    j ''ᵁ U ≤ smoothLocus sY := by
  apply le_smoothLocus
  haveI := hU
  rw [← j.isoImage_inv_ι_assoc U]
  infer_instance

/-- A `ℂ`-point of `X` lying in a closed subset `Z` factors through the reduced closed
subscheme on `Z`. -/
private theorem mem_range_realize_vanishingIdeal {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    (Z : TopologicalSpace.Closeds X) (y : ComplexPoints sX) (hy : y.toScheme ∈ Z) :
    y ∈ Set.range (realize (sX := (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ sX)
      (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι rfl) := by
  have hker : (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι.ker ≤ y.hom.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    refine Scheme.IdealSheafData.vanishingIdeal_antimono (closure_minimal ?_ Z.isClosed)
    rintro _ ⟨q, rfl⟩
    rw [Subsingleton.elim q default]
    exact hy
  let z : Spec (.of ℂ) ⟶ (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
    IsClosedImmersion.lift _ y.hom hker
  have hz : z ≫ (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι = y.hom :=
    IsClosedImmersion.lift_fac _ _ _
  refine ⟨⟨z, by rw [← Category.assoc, hz, y.hom_comp_structure]⟩, ComplexPoints.ext hz⟩

/-- A nonempty open of a scheme locally of finite type over `ℂ` contains a `ℂ`-point. -/
private theorem exists_complexPoints_mem {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType sX] (U : X.Opens) (hU : (U : Set X).Nonempty) :
    ∃ x : ComplexPoints sX, x.toScheme ∈ U := by
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  obtain ⟨p, hpU, hp⟩ := nonempty_inter_closedPoints hU U.isOpen.isLocallyClosed
  obtain ⟨x, rfl⟩ : p ∈ Set.range (toScheme (sX := sX)) := by
    rw [range_toScheme]
    exact hp
  exact ⟨x, hpU⟩

end SchemeInputs

section Dimension

/-- The local dimension of a space at a point is at most the dimension of the space. -/
private theorem topologicalKrullDimAt_le_topologicalKrullDim {X : Type*} [TopologicalSpace X]
    (x : X) : topologicalKrullDimAt X x ≤ topologicalKrullDim X :=
  ((topologicalKrullDimAt_isLeast X x).2 ⟨Set.univ, trivial, isOpen_univ, rfl⟩).trans
    (Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq.le

/-- On a scheme locally of finite type over `ℂ` all of whose irreducible components have
dimension `d`, the local dimension at every point is `d`. -/
private theorem topologicalKrullDimAt_eq_of_forall_irreducibleComponents {X : Scheme.{0}}
    (f : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType f] {d : WithBot ℕ∞}
    (hd : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d) (x : X) :
    topologicalKrullDimAt X x = d := by
  rw [topologicalKrullDimAt_eq_iSup_irreducibleComponents ℂ X f x]
  apply le_antisymm
  · exact iSup₂_le fun Z hZ ↦ (hd Z hZ.1).le
  · exact le_iSup₂_of_le (f := fun (Z : Set X) _ ↦ topologicalKrullDim Z) (irreducibleComponent x)
      ⟨irreducibleComponent_mem_irreducibleComponents x, mem_irreducibleComponent⟩
      (hd _ (irreducibleComponent_mem_irreducibleComponents x)).ge

/-- The affine line over `ℂ` has dimension one. -/
private theorem topologicalKrullDim_affineLine :
    topologicalKrullDim (𝔸(Unit; Spec (.of ℂ))) = 1 := by
  rw [(Scheme.homeoOfIso (AffineSpace.SpecIso Unit (.of ℂ))).isHomeomorph.topologicalKrullDim_eq]
  exact ((PrimeSpectrum.homeomorphOfRingEquiv
    (MvPolynomial.pUnitAlgEquiv ℂ).toRingEquiv).isHomeomorph.topologicalKrullDim_eq).trans
      (MMP.Flips.topologicalKrullDim_line ℂ)

/-- If `d + 1 = 4` in `WithBot ℕ∞`, then `d = 3`. -/
private theorem eq_three_of_add_one_eq_four {d : WithBot ℕ∞} (hd : d + 1 = 4) : d = 3 := by
  induction d using WithBot.recBotCoe with
  | bot => exact absurd hd (by rw [WithBot.bot_add]; exact WithBot.bot_ne_coe)
  | coe e =>
    have h2 : e + 1 = 4 := WithBot.coe_injective (by rw [WithBot.coe_add]; exact hd)
    induction e using ENat.recTopCoe with
    | top =>
      rw [top_add] at h2
      exact absurd h2 (by simp)
    | coe n =>
      have h3 : n + 1 = 4 := by exact_mod_cast h2
      have : n = 3 := by omega
      rw [this]
      simp

end Dimension

/-! ### The analytic glueing at a slice point -/

section Glue

open _root_.Topology

/-- **The germ lifting at a general point of `T`, from the slice.** Let `t : X ⟶ B` be a family
over a smooth curve near a point `x` of `T`, with the product structure of
`MMP.Fourfold.exists_homeomorph_prod_and_stalk_iso_of_relativeSNC`, let `S ⊆ X_b` be an open of
the slice through `x`, `f₀ : W₀ ⟶ S` the slice of `π` over `S` (a pullback of `π`), with a
section `s` over `S ∖ {x}`, and suppose that the stalk at `x` of the degree-two punctured
restriction of `f₀` is surjective. Then every class on a punctured neighbourhood of `x` in `Y`
is, near `x`, the restriction of a class on `π⁻¹`. -/
private theorem exists_restrict_eq_of_slice {Y Yt : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    {π : Yt ⟶ Y}
    [IsProper π] [LocallyOfFiniteType sY] [IsSeparated sY]
    (hπ : IsBiregular π (smoothLocus sY))
    {X : Y.Opens} {B : Scheme.{0}} {sB : B ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sB] [IsSeparated sB] [QuasiCompact sB]
    [Smooth sB] [SmoothOfRelativeDimension 1 sB]
    (t : (X : Scheme.{0}) ⟶ B) (hX : X.ι ≫ sY = t ≫ sB)
    [LocallyOfFiniteType (t ≫ sB)] [IsSeparated (t ≫ sB)] [QuasiCompact (t ≫ sB)]
    {Z Tc : Scheme.{0}} (f : Z ⟶ X) [IsProper f] [Surjective f]
    [IsSeparated (f ≫ t ≫ sB)] [QuasiCompact (f ≫ t ≫ sB)]
    (iT : Tc ⟶ X) [IsClosedImmersion iT] [Smooth (iT ≫ t ≫ sB)]
    (UX : (X : Scheme.{0}).Opens) (hUX : (UX : Set X) = (Set.range iT.base)ᶜ)
    [IsIso (f ∣_ UX)] [IsFinite (iT ≫ t)] [Etale (iT ≫ t)]
    (hZB : Smooth (f ≫ t)) (sP : Finset (MMP.Mori.PrimeDivisor Z))
    (hsP : (⋃ E ∈ sP, (E.support : Set Z)) = f.base ⁻¹' Set.range iT.base)
    (hsnc : MMP.Mori.DivisorWithCoeffs.IsSNC (f ≫ t ≫ sB)
      (∑ E ∈ sP, Finsupp.single E (1 : ℤ)))
    (hstr : ∀ J ⊆ sP, J.Nonempty → Smooth ((⨆ E ∈ J, E.idealSheaf).subschemeι ≫ f ≫ t))
    (hreg : ∀ y : (X : Scheme.{0}), y ∉ Set.range iT.base → X.ι.base y ∈ smoothLocus sY)
    (hsing : ∀ y : (X : Scheme.{0}), y ∈ Set.range iT.base → X.ι.base y ∉ smoothLocus sY)
    (hτ : ∀ y : ComplexPoints (t ≫ sB), y.toScheme ∈ Set.range iT.base →
      y ∈ Set.range (realize (sX := iT ≫ t ≫ sB) iT rfl))
    (b : ComplexPoints sB) (xX : ComplexPoints (t ≫ sB))
    (hxT : xX ∈ Set.range (realize (sX := iT ≫ t ≫ sB) iT rfl)) (hxb : realize t rfl xX = b)
    {Xb : Scheme.{0}} (ib : Xb ⟶ X) (sXb : Xb ⟶ Spec (.of ℂ)) (H : IsPullback ib sXb t b.hom)
    (S : Xb.Opens) [LocallyOfFiniteType (S.ι ≫ sXb)] [IsSeparated (S.ι ≫ sXb)]
    (xS : ComplexPoints (S.ι ≫ sXb)) (hxS : xS.hom ≫ S.ι ≫ ib = xX.hom)
    (V : (S : Scheme.{0}).Opens) (hV : (V : Set S) = {xS.toScheme}ᶜ)
    (hVT : ∀ v : (V : Scheme.{0}), (V.ι ≫ S.ι ≫ ib).base v ∉ Set.range iT.base)
    {W₀ : Scheme.{0}} (f₀ : W₀ ⟶ S) [IsProper f₀] (s : (V : Scheme.{0}) ⟶ W₀)
    (hs : s ≫ f₀ = V.ι) (κ : W₀ ⟶ Yt) (hκ : IsPullback κ f₀ π (S.ι ≫ ib ≫ X.ι))
    (hsurj : Function.Surjective ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) xS).map
        ((TopCat.Sheaf.forget _ _).map
          (higherDirectImageRestriction (j := analyticMap (sY := S.ι ≫ sXb) V.ι rfl)
            (analyticMap f₀ rfl) (analyticMap s (by rw [← Category.assoc, hs]))
            (by
              ext y
              change (y.hom ≫ s) ≫ f₀ = y.hom ≫ V.ι
              rw [Category.assoc, hs]) 2))).hom)
    (O : Opens (analyticSpace sY)) (hO : realize X.ι hX xX ∈ O)
    (γ : rationalCohomology (preimageSpace (regularInclusion sY) O) 2) :
    ∃ (W : Opens (analyticSpace sY)) (hWO : W ≤ O) (_ : realize X.ι hX xX ∈ W)
      (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY π) W) 2),
      (rationalCohomologyMap (preimageRestrict (resolutionAnalyticMap sY π)
          (analyticMap (regularSection sY hπ) (by rw [← Category.assoc, regularSection_comp]))
          (regularSection_analyticMap_comp sY hπ) W) 2).hom α =
        (rationalCohomologyMap (preimageInclusion (regularInclusion sY) hWO) 2).hom γ := by
  classical
  set x : analyticSpace sY := realize X.ι hX xX with hx
  -- compatibilities of the structure morphisms
  have hSX : (S.ι ≫ ib) ≫ t ≫ sB = S.ι ≫ sXb := by
    rw [Category.assoc, ← Category.assoc ib t sB, H.w, Category.assoc, b.hom_comp_structure,
      Category.comp_id]
  have hSY : (S.ι ≫ ib ≫ X.ι) ≫ sY = S.ι ≫ sXb := by
    rw [Category.assoc, Category.assoc, hX, ← Category.assoc ib t sB, H.w, Category.assoc,
      b.hom_comp_structure, Category.comp_id]
  have hκY : κ ≫ π ≫ sY = f₀ ≫ S.ι ≫ sXb := by
    rw [← Category.assoc, hκ.w, Category.assoc, hSY]
  have hxSY : xS.hom ≫ S.ι ≫ ib ≫ X.ι = x.hom := by
    change _ = xX.hom ≫ X.ι
    rw [← hxS]
    simp only [Category.assoc]
  -- the analytic maps
  let ιA : analyticSpace (t ≫ sB) ⟶ analyticSpace sY := analyticMap X.ι hX
  have hιA : IsOpenEmbedding ιA := isOpenEmbedding_realize_of_isOpenImmersion X.ι hX
  let κS : analyticSpace (S.ι ≫ sXb) ⟶ analyticSpace (t ≫ sB) := analyticMap (S.ι ≫ ib) hSX
  let κY : analyticSpace (S.ι ≫ sXb) ⟶ analyticSpace sY := analyticMap (S.ι ≫ ib ≫ X.ι) hSY
  have hκYS : ∀ w, κY w = ιA (κS w) := fun w ↦ ComplexPoints.ext (by
    change w.hom ≫ S.ι ≫ ib ≫ X.ι = (w.hom ≫ S.ι ≫ ib) ≫ X.ι
    simp only [Category.assoc])
  have hκSx : κS xS = xX := ComplexPoints.ext hxS
  have hκYx : κY xS = x := (hκYS xS).trans ((congrArg ιA hκSx).trans hx.symm)
  let jS : analyticSpace (V.ι ≫ S.ι ≫ sXb) ⟶ analyticSpace (S.ι ≫ sXb) :=
    analyticMap (sY := S.ι ≫ sXb) V.ι rfl
  let f₀A : analyticSpace (f₀ ≫ S.ι ≫ sXb) ⟶ analyticSpace (S.ι ≫ sXb) := analyticMap f₀ rfl
  have hsA : s ≫ f₀ ≫ S.ι ≫ sXb = V.ι ≫ S.ι ≫ sXb := by rw [← Category.assoc, hs]
  let sA : analyticSpace (V.ι ≫ S.ι ≫ sXb) ⟶ analyticSpace (f₀ ≫ S.ι ≫ sXb) := analyticMap s hsA
  have hsAj : sA ≫ f₀A = jS := by
    ext y
    change (y.hom ≫ s) ≫ f₀ = y.hom ≫ V.ι
    rw [Category.assoc, hs]
  let κW : analyticSpace (f₀ ≫ S.ι ≫ sXb) ⟶ analyticSpace (π ≫ sY) := analyticMap κ hκY
  let πA := resolutionAnalyticMap sY π
  let jA := regularInclusion sY
  let gR : analyticSpace ((smoothLocus sY).ι ≫ sY) ⟶ analyticSpace (π ≫ sY) :=
    analyticMap (regularSection sY hπ) (by rw [← Category.assoc, regularSection_comp])
  have hgR : gR ≫ πA = jA := regularSection_analyticMap_comp sY hπ
  -- the lift `λ : V ⟶ Y_reg`
  have hVreg : Set.range (V.ι ≫ S.ι ≫ ib ≫ X.ι).base ⊆ Set.range (smoothLocus sY).ι.base := by
    rintro _ ⟨v, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hreg _ (hVT v)
  let lam : (V : Scheme.{0}) ⟶ (smoothLocus sY : Scheme.{0}) :=
    IsOpenImmersion.lift (smoothLocus sY).ι (V.ι ≫ S.ι ≫ ib ≫ X.ι) hVreg
  have hlam : lam ≫ (smoothLocus sY).ι = V.ι ≫ S.ι ≫ ib ≫ X.ι := IsOpenImmersion.lift_fac _ _ _
  have hlamS : lam ≫ (smoothLocus sY).ι ≫ sY = V.ι ≫ S.ι ≫ sXb := by
    rw [← Category.assoc, hlam, ← hSY]
    simp only [Category.assoc]
  let lamA : analyticSpace (V.ι ≫ S.ι ≫ sXb) ⟶ analyticSpace ((smoothLocus sY).ι ≫ sY) :=
    analyticMap lam hlamS
  have hjlam : ∀ v, jA (lamA v) = κY (jS v) := fun v ↦ ComplexPoints.ext (by
    change (v.hom ≫ lam) ≫ (smoothLocus sY).ι = (v.hom ≫ V.ι) ≫ S.ι ≫ ib ≫ X.ι
    rw [Category.assoc, hlam, Category.assoc])
  -- the section of `π` over `Y_reg` and the section `s` agree on `V`
  have hsec : lam ≫ regularSection sY hπ = s ≫ κ := by
    have hr : Set.range (s ≫ κ).base ⊆ Set.range (π ⁻¹ᵁ smoothLocus sY).ι.base := by
      rintro _ ⟨v, rfl⟩
      rw [Scheme.Opens.range_ι]
      change (s ≫ κ ≫ π).base v ∈ smoothLocus sY
      rw [hκ.w, ← Category.assoc, hs, ← hlam]
      exact (lam.base v).2
    let l := IsOpenImmersion.lift (π ⁻¹ᵁ smoothLocus sY).ι (s ≫ κ) hr
    have hl : l ≫ (π ⁻¹ᵁ smoothLocus sY).ι = s ≫ κ := IsOpenImmersion.lift_fac _ _ _
    have hl2 : l ≫ (π ∣_ smoothLocus sY) = lam := by
      rw [← cancel_mono (smoothLocus sY).ι, Category.assoc, morphismRestrict_ι,
        ← Category.assoc, hl, Category.assoc, hκ.w, ← Category.assoc, hs, hlam]
    have : IsIso (π ∣_ smoothLocus sY) := hπ
    unfold regularSection
    rw [← hl2, Category.assoc,
      @IsIso.hom_inv_id_assoc _ _ _ _ (π ∣_ smoothLocus sY) hπ, hl]
  -- the restriction of a class of `Y_reg` to the punctured slice neighbourhoods
  have hρmem : ∀ (O'' : Opens (analyticSpace sY)) (v : analyticSpace (V.ι ≫ S.ι ≫ sXb)),
      κY (jS v) ∈ O'' → jA (lamA v) ∈ O'' := fun O'' v hv ↦ by rwa [hjlam]
  let ρ : ∀ (N' : Opens (analyticSpace (S.ι ≫ sXb))) (O'' : Opens (analyticSpace sY)),
      N' ≤ (Opens.map κY).obj O'' → (preimageSpace jS N' ⟶ preimageSpace jA O'') :=
    fun N' O'' h ↦ TopCat.ofHom ⟨fun v ↦ ⟨lamA v.1, hρmem O'' v.1 (h v.2)⟩,
      (lamA.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩
  -- Step 1: the slice resolution lifts the restricted class near `x`
  let OS : Opens (analyticSpace (S.ι ≫ sXb)) := (Opens.map κY).obj O
  have hxOS : xS ∈ OS := by
    change κY xS ∈ O
    rw [hκYx]
    exact hO
  obtain ⟨N, hNO, hxN, β, hβ⟩ := exists_restrict_eq_of_surjective_stalk f₀A sA hsAj 2 xS hsurj
    OS hxOS ((rationalCohomologyMap (ρ OS O le_rfl) 2).hom γ)
  -- Step 2: extend the restriction of `β` to the fibre `π⁻¹(x)` to a tube in `Ỹ`
  have HPπ := IsPullback.of_hasPullback π x.hom
  have hcπ := fibre_comparison π sY x (pullback.fst π x.hom) (pullback.snd π x.hom) HPπ 2
  let iP : pullback π x.hom ⟶ W₀ := hκ.lift (pullback.fst π x.hom)
    (pullback.snd π x.hom ≫ xS.hom) (by rw [pullback.condition, Category.assoc, hxSY])
  have hiPκ : iP ≫ κ = pullback.fst π x.hom := hκ.lift_fst _ _ _
  have hiPf : iP ≫ f₀ = pullback.snd π x.hom ≫ xS.hom := hκ.lift_snd _ _ _
  have HPf : IsPullback iP (pullback.snd π x.hom) f₀ xS.hom := by
    refine IsPullback.of_right ?_ hiPf hκ
    rw [hiPκ, hxSY]
    exact HPπ
  have hcf := fibre_comparison f₀ (S.ι ≫ sXb) xS iP (pullback.snd π x.hom) HPf 2
  obtain ⟨O1, hxO1, α, hα⟩ :=
    hcπ.1 ((rationalCohomologyMap (fibreIncl f₀ (S.ι ≫ sXb) xS iP _ HPf.w hxN) 2).hom β)
  -- Step 3: compare on a smaller tube of the slice
  let N2 : Opens (analyticSpace (S.ι ≫ sXb)) := N ⊓ (Opens.map κY).obj O1
  have hN2N : N2 ≤ N := inf_le_left
  have hxN2 : xS ∈ N2 := ⟨hxN, by
    change κY xS ∈ O1
    rw [hκYx]
    exact hxO1⟩
  have hτmem : ∀ w : analyticSpace (f₀ ≫ S.ι ≫ sXb), f₀A w ∈ N2 → πA (κW w) ∈ O1 := by
    intro w hw
    have he : πA (κW w) = κY (f₀A w) := ComplexPoints.ext (by
      change (w.hom ≫ κ) ≫ π = (w.hom ≫ f₀) ≫ S.ι ≫ ib ≫ X.ι
      rw [Category.assoc, hκ.w, Category.assoc])
    rw [he]
    exact hw.2
  let τm : preimageSpace f₀A N2 ⟶ preimageSpace πA O1 :=
    TopCat.ofHom ⟨fun w ↦ ⟨κW w.1, hτmem w.1 w.2⟩,
      (κW.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩
  have hfib1 : fibreIncl f₀ (S.ι ≫ sXb) xS iP _ HPf.w hxN2 ≫ τm =
      fibreIncl π sY x (pullback.fst π x.hom) _ HPπ.w hxO1 := by
    refine TopCat.ext fun p ↦ Subtype.ext (ComplexPoints.ext ?_)
    change (p.hom ≫ iP) ≫ κ = p.hom ≫ pullback.fst π x.hom
    rw [Category.assoc, hiPκ]
  have hfib2 : fibreIncl f₀ (S.ι ≫ sXb) xS iP _ HPf.w hxN2 ≫ preimageInclusion f₀A hN2N =
      fibreIncl f₀ (S.ι ≫ sXb) xS iP _ HPf.w hxN := TopCat.ext fun _ ↦ rfl
  have hdiff : (rationalCohomologyMap (fibreIncl f₀ (S.ι ≫ sXb) xS iP _ HPf.w hxN2) 2).hom
      ((rationalCohomologyMap τm 2).hom α -
        (rationalCohomologyMap (preimageInclusion f₀A hN2N) 2).hom β) = 0 := by
    have e1 : (rationalCohomologyMap (fibreIncl f₀ (S.ι ≫ sXb) xS iP _ HPf.w hxN2) 2).hom
        ((rationalCohomologyMap τm 2).hom α) =
        (rationalCohomologyMap (fibreIncl π sY x (pullback.fst π x.hom) _ HPπ.w hxO1) 2).hom
          α := by
      rw [← hfib1]
      exact (rationalCohomologyMap_comp_apply _ _ _ _).symm
    have e2 : (rationalCohomologyMap (fibreIncl f₀ (S.ι ≫ sXb) xS iP _ HPf.w hxN2) 2).hom
        ((rationalCohomologyMap (preimageInclusion f₀A hN2N) 2).hom β) =
        (rationalCohomologyMap (fibreIncl f₀ (S.ι ≫ sXb) xS iP _ HPf.w hxN) 2).hom β := by
      rw [← hfib2]
      exact (rationalCohomologyMap_comp_apply _ _ _ _).symm
    rw [map_sub]
    exact sub_eq_zero.2 (e1.trans (hα.trans e2.symm))
  obtain ⟨N3, hN3N2, hxN3, hN3⟩ := hcf.2 N2 hxN2 _ hdiff
  -- Step 4: the difference class on `Y_reg` vanishes on the punctured slice near `x`
  let O' : Opens (analyticSpace sY) := O ⊓ O1
  have hO'O : O' ≤ O := inf_le_left
  have hO'O1 : O' ≤ O1 := inf_le_right
  have hxO' : x ∈ O' := ⟨hO, hxO1⟩
  suffices hW : ∃ (W : Opens (analyticSpace sY)) (hWO' : W ≤ O') (_ : x ∈ W),
      (rationalCohomologyMap (preimageInclusion jA hWO') 2).hom
        ((rationalCohomologyMap (preimageRestrict πA gR hgR O') 2).hom
          ((rationalCohomologyMap (preimageInclusion πA hO'O1) 2).hom α) -
        (rationalCohomologyMap (preimageInclusion jA hO'O) 2).hom γ) = 0 by
    obtain ⟨W, hWO', hxW, hεW⟩ := hW
    refine ⟨W, hWO'.trans hO'O, hxW,
      (rationalCohomologyMap (preimageInclusion πA (hWO'.trans hO'O1)) 2).hom α, ?_⟩
    rw [map_sub, sub_eq_zero] at hεW
    have e1 : preimageInclusion jA hWO' ≫ preimageRestrict πA gR hgR O' ≫
        preimageInclusion πA hO'O1 =
        preimageRestrict πA gR hgR W ≫ preimageInclusion πA (hWO'.trans hO'O1) :=
      TopCat.ext fun _ ↦ rfl
    have e2 : preimageInclusion jA hWO' ≫ preimageInclusion jA hO'O =
        preimageInclusion jA (hWO'.trans hO'O) := TopCat.ext fun _ ↦ rfl
    calc (rationalCohomologyMap (preimageRestrict πA gR hgR W) 2).hom
          ((rationalCohomologyMap (preimageInclusion πA (hWO'.trans hO'O1)) 2).hom α)
        = (rationalCohomologyMap (preimageRestrict πA gR hgR W ≫
            preimageInclusion πA (hWO'.trans hO'O1)) 2).hom α :=
          (rationalCohomologyMap_comp_apply _ _ _ _).symm
      _ = (rationalCohomologyMap (preimageInclusion jA hWO' ≫ preimageRestrict πA gR hgR O' ≫
            preimageInclusion πA hO'O1) 2).hom α := by rw [e1]
      _ = (rationalCohomologyMap (preimageInclusion jA hWO') 2).hom
            ((rationalCohomologyMap (preimageRestrict πA gR hgR O') 2).hom
              ((rationalCohomologyMap (preimageInclusion πA hO'O1) 2).hom α)) :=
          rationalCohomologyMap_comp₃_apply _ _ _ _ _
      _ = (rationalCohomologyMap (preimageInclusion jA hWO') 2).hom
            ((rationalCohomologyMap (preimageInclusion jA hO'O) 2).hom γ) := hεW
      _ = (rationalCohomologyMap (preimageInclusion jA (hWO'.trans hO'O)) 2).hom γ :=
          (rationalCohomologyMap_comp_apply _ _ _ _).symm.trans (by rw [e2])
  have hN3O' : N3 ≤ (Opens.map κY).obj O' := fun v hv ↦
    ⟨hNO (hN2N (hN3N2 hv)), (hN3N2 hv).2⟩
  have hZ1 : (rationalCohomologyMap (ρ N3 O' hN3O') 2).hom
      ((rationalCohomologyMap (preimageRestrict πA gR hgR O') 2).hom
          ((rationalCohomologyMap (preimageInclusion πA hO'O1) 2).hom α) -
        (rationalCohomologyMap (preimageInclusion jA hO'O) 2).hom γ) = 0 := by
    have mA : ρ N3 O' hN3O' ≫ preimageRestrict πA gR hgR O' ≫ preimageInclusion πA hO'O1 =
        preimageRestrict f₀A sA hsAj N3 ≫ preimageInclusion f₀A hN3N2 ≫ τm := by
      refine TopCat.ext fun v ↦ Subtype.ext (ComplexPoints.ext ?_)
      change (v.1.hom ≫ lam) ≫ regularSection sY hπ = (v.1.hom ≫ s) ≫ κ
      rw [Category.assoc, Category.assoc, hsec]
    have m1 : preimageRestrict f₀A sA hsAj N3 ≫ preimageInclusion f₀A hN3N2 ≫
        preimageInclusion f₀A hN2N =
        preimageInclusion jS (hN3N2.trans hN2N) ≫ preimageRestrict f₀A sA hsAj N :=
      TopCat.ext fun _ ↦ rfl
    have m2 : preimageInclusion jS (hN3N2.trans hN2N) ≫ preimageInclusion jS hNO ≫
        ρ OS O le_rfl = ρ N3 O' hN3O' ≫ preimageInclusion jA hO'O :=
      TopCat.ext fun _ ↦ rfl
    have hA : (rationalCohomologyMap (ρ N3 O' hN3O') 2).hom
        ((rationalCohomologyMap (preimageRestrict πA gR hgR O') 2).hom
          ((rationalCohomologyMap (preimageInclusion πA hO'O1) 2).hom α)) =
        (rationalCohomologyMap (preimageRestrict f₀A sA hsAj N3) 2).hom
          ((rationalCohomologyMap (preimageInclusion f₀A hN3N2) 2).hom
            ((rationalCohomologyMap τm 2).hom α)) := by
      calc _ = (rationalCohomologyMap (ρ N3 O' hN3O' ≫ preimageRestrict πA gR hgR O' ≫
            preimageInclusion πA hO'O1) 2).hom α :=
            (rationalCohomologyMap_comp₃_apply _ _ _ _ _).symm
        _ = (rationalCohomologyMap (preimageRestrict f₀A sA hsAj N3 ≫
            preimageInclusion f₀A hN3N2 ≫ τm) 2).hom α := by rw [mA]
        _ = _ := rationalCohomologyMap_comp₃_apply _ _ _ _ _
    have hB : (rationalCohomologyMap (ρ N3 O' hN3O') 2).hom
        ((rationalCohomologyMap (preimageInclusion jA hO'O) 2).hom γ) =
        (rationalCohomologyMap (preimageRestrict f₀A sA hsAj N3) 2).hom
          ((rationalCohomologyMap (preimageInclusion f₀A hN3N2) 2).hom
            ((rationalCohomologyMap (preimageInclusion f₀A hN2N) 2).hom β)) := by
      calc _ = (rationalCohomologyMap (ρ N3 O' hN3O' ≫ preimageInclusion jA hO'O) 2).hom γ :=
            (rationalCohomologyMap_comp_apply _ _ _ _).symm
        _ = (rationalCohomologyMap (preimageInclusion jS (hN3N2.trans hN2N) ≫
            preimageInclusion jS hNO ≫ ρ OS O le_rfl) 2).hom γ := by rw [m2]
        _ = (rationalCohomologyMap (preimageInclusion jS (hN3N2.trans hN2N)) 2).hom
            ((rationalCohomologyMap (preimageInclusion jS hNO) 2).hom
              ((rationalCohomologyMap (ρ OS O le_rfl) 2).hom γ)) :=
            rationalCohomologyMap_comp₃_apply _ _ _ _ _
        _ = (rationalCohomologyMap (preimageInclusion jS (hN3N2.trans hN2N)) 2).hom
            ((rationalCohomologyMap (preimageRestrict f₀A sA hsAj N) 2).hom β) := by rw [hβ]
        _ = (rationalCohomologyMap (preimageInclusion jS (hN3N2.trans hN2N) ≫
            preimageRestrict f₀A sA hsAj N) 2).hom β :=
            (rationalCohomologyMap_comp_apply _ _ _ _).symm
        _ = (rationalCohomologyMap (preimageRestrict f₀A sA hsAj N3 ≫
            preimageInclusion f₀A hN3N2 ≫ preimageInclusion f₀A hN2N) 2).hom β := by rw [m1]
        _ = _ := rationalCohomologyMap_comp₃_apply _ _ _ _ _
    rw [map_sub, hA, hB, ← map_sub, ← map_sub]
    exact (congrArg _ hN3).trans (map_zero _)
  -- Step 5: transport to `X` and to the slice `X_b`
  obtain ⟨εY, hεY⟩ : ∃ c, c = (rationalCohomologyMap (preimageRestrict πA gR hgR O') 2).hom
      ((rationalCohomologyMap (preimageInclusion πA hO'O1) 2).hom α) -
        (rationalCohomologyMap (preimageInclusion jA hO'O) 2).hom γ := ⟨_, rfl⟩
  rw [← hεY] at hZ1
  rw [← hεY]
  obtain ⟨-, hstalk⟩ :=
    exists_homeomorph_prod_and_stalk_iso_of_isSNC f iT UX hUX t rfl hZB sP hsP hsnc hstr b xX
      hxT hxb
  obtain ⟨e, he⟩ := hstalk 2
  let τ : Set (ComplexPoints (t ≫ sB)) := Set.range (realize (sX := iT ≫ t ≫ sB) iT rfl)
  let Fb : Set (ComplexPoints (t ≫ sB)) := realize t rfl ⁻¹' {b}
  let jX : TopCat.of ↥τᶜ ⟶ analyticSpace (t ≫ sB) :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let jb : TopCat.of ↥((Subtype.val : Fb → ComplexPoints (t ≫ sB)) ⁻¹' τ)ᶜ ⟶ TopCat.of Fb :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let slice : Opens (analyticSpace (t ≫ sB)) → Opens (TopCat.of Fb) := fun V ↦
    ⟨Subtype.val ⁻¹' (V : Set (ComplexPoints (t ≫ sB))), V.isOpen.preimage continuous_subtype_val⟩
  let r : ∀ V, preimageSpace jb (slice V) ⟶ preimageSpace jX V := fun V ↦
    TopCat.ofHom ⟨fun y ↦ ⟨⟨y.1.1.1, y.1.2⟩, y.2⟩,
      ((continuous_subtype_val.comp (continuous_subtype_val.comp
        continuous_subtype_val)).subtype_mk _).subtype_mk _⟩
  -- the comparison `X(ℂ) ∖ T(ℂ) ≅ Y_reg(ℂ) ∩ X(ℂ)`
  have hmXmem : ∀ y : ComplexPoints (t ≫ sB), y ∉ τ → (ιA y).toScheme ∈ smoothLocus sY :=
    fun y hy ↦ hreg _ (fun h ↦ hy (hτ y h))
  let mXf : ∀ W : Opens (analyticSpace sY), preimageSpace jX ((Opens.map ιA).obj W) →
      analyticSpace ((smoothLocus sY).ι ≫ sY) := fun W y ↦
    liftPt (smoothLocus sY) (ιA y.1.1) (hmXmem y.1.1 y.1.2)
  have hmXf : ∀ W y, jA (mXf W y) = ιA y.1.1 := fun W y ↦ realize_liftPt _ _ _
  have hind : IsInducing (realize (sX := (smoothLocus sY).ι ≫ sY) (smoothLocus sY).ι rfl) :=
    (isOpenEmbedding_realize_ι (sX := sY) (smoothLocus sY)).isEmbedding.isInducing
  have hmXc : ∀ W, Continuous (mXf W) := fun W ↦
    hind.continuous_iff.2 (by
      have : realize (sX := (smoothLocus sY).ι ≫ sY) (smoothLocus sY).ι rfl ∘ mXf W =
          fun y ↦ ιA y.1.1 := funext (hmXf W)
      rw [this]
      exact ιA.hom.continuous.comp (continuous_subtype_val.comp continuous_subtype_val))
  have hmXW : ∀ (W : Opens (analyticSpace sY)) (y : preimageSpace jX ((Opens.map ιA).obj W)),
      jA (mXf W y) ∈ W := fun W y ↦ by
    rw [hmXf]
    exact y.2
  let mX : ∀ W, preimageSpace jX ((Opens.map ιA).obj W) ⟶ preimageSpace jA W := fun W ↦
    TopCat.ofHom ⟨fun y ↦ ⟨mXf W y, hmXW W y⟩, (hmXc W).subtype_mk (hmXW W)⟩
  have hmXemb : ∀ W, IsEmbedding (mX W) := fun W ↦ by
    have hg : IsEmbedding (fun p : preimageSpace jA W ↦ jA p.1) :=
      (isOpenEmbedding_realize_ι (sX := sY) (smoothLocus sY)).isEmbedding.comp
        IsEmbedding.subtypeVal
    rw [← hg.of_comp_iff]
    have : (fun p : preimageSpace jA W ↦ jA p.1) ∘ (mX W) =
        ιA ∘ (Subtype.val ∘ Subtype.val) := funext fun y ↦ hmXf W y
    rw [this]
    exact hιA.isEmbedding.comp (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal)
  have hmXsurj : ∀ W : Opens (analyticSpace sY), (W : Set (analyticSpace sY)) ⊆ Set.range ιA →
      Function.Surjective (mX W) := by
    intro W hW p
    obtain ⟨y, hy⟩ := hW p.2
    have hyτ : y ∉ τ := by
      rintro ⟨z, rfl⟩
      apply hsing (iT.base z.toScheme) ⟨_, rfl⟩
      have h1 : (ιA (realize iT rfl z)).toScheme = (jA p.1).toScheme := congrArg _ hy
      change X.ι.base (iT.base z.toScheme) ∈ smoothLocus sY
      rw [show X.ι.base (iT.base z.toScheme) = (jA p.1).toScheme from h1]
      exact (p.1.toScheme).2
    refine ⟨⟨⟨y, hyτ⟩, by
      change ιA y ∈ W
      rw [hy]
      exact p.2⟩, ?_⟩
    exact Subtype.ext (eq_of_realize_ι_eq (smoothLocus sY) ((hmXf W _).trans hy))
  let OX' : Opens (analyticSpace (t ≫ sB)) := (Opens.map ιA).obj O'
  have hxOX' : xX ∈ OX' := hxO'
  obtain ⟨εX, hεX⟩ : ∃ c, c = (rationalCohomologyMap (mX O') 2).hom εY := ⟨_, rfl⟩
  -- the slice `X_b(ℂ)` as an open of the fibre `F_b`
  obtain ⟨hibemb, hibrange⟩ := isEmbedding_analyticMap_fibre t sB b ib sXb H
  let ibA := analyticMap ib (fibreIncl_w t sB b ib sXb H.w)
  let SιA : analyticSpace (S.ι ≫ sXb) ⟶ analyticSpace sXb := analyticMap (sY := sXb) S.ι rfl
  have hκS' : ∀ w, κS w = ibA (SιA w) := fun w ↦ ComplexPoints.ext (by
    change w.hom ≫ S.ι ≫ ib = (w.hom ≫ S.ι) ≫ ib
    rw [Category.assoc])
  have hκSemb : IsEmbedding κS := by
    have : (κS : analyticSpace (S.ι ≫ sXb) → analyticSpace (t ≫ sB)) = ibA ∘ SιA :=
      funext hκS'
    rw [this]
    exact hibemb.comp (isOpenEmbedding_realize_ι (sX := sXb) S).isEmbedding
  obtain ⟨O5, hO5o, hO5⟩ := hκSemb.isInducing.isOpen_iff.1 N3.isOpen
  obtain ⟨O6, hO6o, hO6⟩ := hibemb.isInducing.isOpen_iff.1
    (isOpen_setOf_toScheme_mem (sY := sXb) S.isOpen)
  let O4 : Opens (analyticSpace (t ≫ sB)) := ⟨O5, hO5o⟩ ⊓ ⟨O6, hO6o⟩ ⊓ OX'
  have hxO4 : xX ∈ O4 := by
    refine ⟨⟨?_, ?_⟩, hxOX'⟩
    · have : xS ∈ κS ⁻¹' O5 := by rw [hO5]; exact hxN3
      rw [← hκSx]
      exact this
    · have : SιA xS ∈ ibA ⁻¹' O6 := by
        rw [hO6]
        exact (xS.toScheme).2
      rw [← hκSx, hκS']
      exact this
  let N4 : Opens (analyticSpace (S.ι ≫ sXb)) := (Opens.map κS).obj O4
  have hN4N3 : N4 ≤ N3 := fun v hv ↦ by
    have : v ∈ κS ⁻¹' O5 := hv.1.1
    rwa [hO5] at this
  have hN4O' : N4 ≤ (Opens.map κY).obj O' := hN4N3.trans hN3O'
  have hZ4 : (rationalCohomologyMap (ρ N4 O' hN4O') 2).hom εY = 0 := by
    have : ρ N4 O' hN4O' = preimageInclusion jS hN4N3 ≫ ρ N3 O' hN3O' := TopCat.ext fun _ ↦ rfl
    rw [this]
    exact (rationalCohomologyMap_comp_apply _ _ _ _).trans ((congrArg _ hZ1).trans (map_zero _))
  -- the punctured slice `V(ℂ) ∩ N₄ ≅ (F_b ∖ T) ∩ O₄`
  have hFb : ∀ v : analyticSpace (V.ι ≫ S.ι ≫ sXb), κS (jS v) ∈ Fb := fun v ↦ ComplexPoints.ext (by
    change (v.hom ≫ V.ι ≫ S.ι ≫ ib) ≫ t = b.hom
    have h := v.hom_comp_structure
    rw [← Category.assoc, ← Category.assoc] at h
    simp only [Category.assoc, H.w]
    simp only [← Category.assoc]
    rw [h, Category.id_comp])
  have hFτ : ∀ v : analyticSpace (V.ι ≫ S.ι ≫ sXb), κS (jS v) ∉ τ := by
    rintro v ⟨z, hz⟩
    exact hVT v.toScheme ⟨z.toScheme, congrArg ComplexPoints.toScheme hz⟩
  let mSb : preimageSpace jS N4 ⟶ preimageSpace jb (slice O4) :=
    TopCat.ofHom ⟨fun v ↦ ⟨⟨⟨κS (jS v.1), hFb v.1⟩, hFτ v.1⟩, v.2⟩,
      (((κS.hom.continuous.comp (jS.hom.continuous.comp continuous_subtype_val)).subtype_mk
        _).subtype_mk _).subtype_mk _⟩
  have hmSbemb : IsEmbedding mSb := by
    have hg : IsEmbedding (fun p : preimageSpace jb (slice O4) ↦ p.1.1.1) :=
      IsEmbedding.subtypeVal.comp (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal)
    rw [← hg.of_comp_iff]
    have : (fun p : preimageSpace jb (slice O4) ↦ p.1.1.1) ∘ mSb = κS ∘ jS ∘ Subtype.val := rfl
    rw [this]
    exact hκSemb.comp ((isOpenEmbedding_realize_ι (sX := S.ι ≫ sXb) V).isEmbedding.comp
      IsEmbedding.subtypeVal)
  have hmSbsurj : Function.Surjective mSb := by
    rintro ⟨⟨⟨q, hqF⟩, hqτ⟩, hqO⟩
    have hqτ' : q ∉ τ := hqτ
    obtain ⟨z, rfl⟩ : q ∈ Set.range ibA := by rwa [hibrange]
    have hzS : z ∈ ibA ⁻¹' O6 := hqO.1.2
    rw [hO6] at hzS
    have hrS : Set.range SιA = {y : ComplexPoints sXb | y.toScheme ∈ S} :=
      range_realize_ι (sX := sXb) S
    obtain ⟨w, rfl⟩ : z ∈ Set.range SιA := by
      rw [hrS]
      exact hzS
    have hwV' : ComplexPoints.toScheme (sX := S.ι ≫ sXb) w ∈ (V : Set (S : Scheme.{0})) := by
      rw [hV]
      intro hw
      have hwx := Set.mem_singleton_iff.1 hw
      have h1 : ibA (SιA w) = xX := by
        apply toScheme_injective (sX := t ≫ sB)
        rw [← hκSx, hκS']
        exact congrArg (fun p ↦ ib.base (S.ι.base p)) hwx
      exact hqτ' (h1 ▸ hxT)
    have hwV : ComplexPoints.toScheme (sX := S.ι ≫ sXb) w ∈ V := hwV'
    have hrV : Set.range jS = {y : ComplexPoints (S.ι ≫ sXb) | y.toScheme ∈ V} :=
      range_realize_ι (sX := S.ι ≫ sXb) V
    obtain ⟨v, rfl⟩ : w ∈ Set.range jS := by
      rw [hrV]
      exact hwV
    refine ⟨⟨v, ?_⟩, ?_⟩
    · change κS (jS v) ∈ O4
      rw [hκS']
      exact hqO
    · exact Subtype.ext (Subtype.ext (Subtype.ext (hκS' (jS v))))
  -- the class vanishes on the punctured slice
  have hsl : slice O4 ≤ slice OX' := fun y hy ↦ hy.2
  have hcomp : mSb ≫ preimageInclusion jb hsl ≫ r OX' ≫ mX O' = ρ N4 O' hN4O' := by
    refine TopCat.ext fun v ↦ Subtype.ext ?_
    apply eq_of_realize_ι_eq (smoothLocus sY)
    change jA (mXf O' _) = jA (lamA v.1)
    exact (hmXf O' _).trans ((hκYS (jS v.1)).symm.trans (hjlam v.1).symm)
  have hslice0 : (rationalCohomologyMap (preimageInclusion jb hsl) 2).hom
      ((rationalCohomologyMap (r OX') 2).hom εX) = 0 := by
    apply injective_rationalCohomologyMap_of_isEmbedding mSb hmSbemb hmSbsurj 2
    rw [map_zero, hεX]
    calc _ = (rationalCohomologyMap (mSb ≫ preimageInclusion jb hsl ≫ r OX' ≫ mX O') 2).hom
          εY :=
          (rationalCohomologyMap_comp₄_apply _ _ _ _ _ _).symm
      _ = 0 := by rw [hcomp]; exact hZ4
  have hgerm0 : (higherDirectImageGerm jX 2 xX hxOX').hom εX = 0 := by
    have h2 : (higherDirectImageGerm jb 2 (V := slice OX') ⟨xX, hxb⟩ hxOX').hom
        ((rationalCohomologyMap (r OX') 2).hom εX) = 0 := by
      rw [← higherDirectImageGerm_res jb 2 hsl ⟨xX, hxb⟩ hxO4, hslice0, map_zero]
    apply e.toLinearEquiv.injective
    rw [map_zero]
    exact (he OX' hxOX' εX).trans h2
  -- Step 6: back to `Y`
  obtain ⟨O7, hxO7, hO7, hεX7⟩ := exists_res_eq_zero_of_germ_eq_zero jX 2 xX hxOX' εX hgerm0
  let W : Opens (analyticSpace sY) := ⟨ιA '' (O7 : Set (analyticSpace (t ≫ sB))),
    hιA.isOpenMap _ O7.isOpen⟩
  have hWO' : W ≤ O' := by
    rintro _ ⟨y, hy, rfl⟩
    exact hO7 hy
  have hxW : x ∈ W := ⟨xX, hxO7, rfl⟩
  have hWr : (W : Set (analyticSpace sY)) ⊆ Set.range ιA := by
    rintro _ ⟨y, -, rfl⟩
    exact ⟨y, rfl⟩
  have hWX : (Opens.map ιA).obj W ≤ O7 := fun y hy ↦ by
    have hy2 : ιA y ∈ ιA '' (O7 : Set (analyticSpace (t ≫ sB))) := hy
    obtain ⟨y', hy', hyy⟩ := hy2
    rwa [hιA.injective hyy] at hy'
  have hm : mX W ≫ preimageInclusion jA hWO' =
      preimageInclusion jX hWX ≫ preimageInclusion jX hO7 ≫ mX O' := TopCat.ext fun _ ↦ rfl
  refine ⟨W, hWO', hxW, injective_rationalCohomologyMap_of_isEmbedding (mX W) (hmXemb W)
    (hmXsurj W hWr) 2 ?_⟩
  rw [map_zero]
  refine (rationalCohomologyMap_comp_apply (mX W) (preimageInclusion jA hWO') 2 εY).symm.trans
    ((congrArg (fun φ ↦ (rationalCohomologyMap φ 2).hom εY) hm).trans
    ((rationalCohomologyMap_comp₃_apply (preimageInclusion jX hWX) (preimageInclusion jX hO7)
      (mX O') 2 εY).trans ?_))
  rw [← hεX, hεX7, map_zero]

end Glue

/-- **Surjectivity at one point.** Some fibre of `r` is surjective. -/
private theorem exists_surjective_localSystemRestrictionFibre {Y Yt : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
    (hLS : IsLocalSetting sY Θ T π) {To : (curveScheme T).Opens} (hTo : IsAdaptedOpen sY π To) :
    ∃ t₀ : analyticSpace (To.ι ≫ curveι T ≫ sY),
      Function.Surjective (localSystemRestrictionFibre sY hLS.isBiregular To t₀).hom := by
  classical
  haveI : AlgebraicGeometry.IsVariety ℂ sY := hLS.isProjectiveVariety.toIsVariety
  haveI : IsProper π := isProper_of_isProjectiveMorphism π hLS.isResolution.2.2.2.1
  haveI : IsDominant π := hLS.isResolution.2.2.2.2.isDominant
  haveI : Surjective π := Surjective.of_universallyClosed_of_isDominant π
  haveI hYtv : AlgebraicGeometry.IsVariety ℂ (π ≫ sY) := hLS.isResolution.2.1
  haveI : IsIntegral Yt := hYtv.toIsIntegral
  haveI : IsLocallyNoetherian Yt := LocallyOfFiniteType.isLocallyNoetherian (π ≫ sY)
  haveI : Smooth (π ≫ sY) :=
    MMP.Threefold.Resolution.smooth_of_isSmoothScheme hLS.isResolution.2.2.1
  -- the relative snc data
  obtain ⟨X, B, t, hXT, ht, hfin, het, hfib, β, -, hfproj, hfres, hfiso, hfsm, sP, hsP, hsnc,
    hstr, -⟩ := hLS.exists_relativeSNC_resolution
  set TX : Closeds (X : Scheme.{0}) :=
    ⟨X.ι ⁻¹' (T : Set Y), T.isClosed.preimage X.ι.continuous⟩ with hTX
  set iT := (Scheme.IdealSheafData.vanishingIdeal TX).subschemeι with hiT
  set f : β.target ⟶ (X : Scheme.{0}) := β.toBase ≫ (π ∣_ X) with hf
  -- the base curve
  haveI : IsLocallyNoetherian (𝔸(Unit; Spec (.of ℂ))) :=
    LocallyOfFiniteType.isLocallyNoetherian (𝔸(Unit; Spec (.of ℂ)) ↘ Spec (.of ℂ))
  set sB : (B : Scheme.{0}) ⟶ Spec (.of ℂ) := B.ι ≫ (𝔸(Unit; Spec (.of ℂ)) ↘ Spec (.of ℂ))
    with hsB
  have hX : X.ι ≫ sY = t ≫ sB := ht.symm
  haveI : LocallyOfFiniteType sB := by rw [hsB]; infer_instance
  haveI : IsSeparated sB := by rw [hsB]; infer_instance
  haveI : QuasiCompact sB := by rw [hsB]; infer_instance
  haveI : SmoothOfRelativeDimension 1 sB := by
    rw [hsB]
    haveI := smoothOfRelativeDimension_affineLine (Spec (.of ℂ))
    exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)
  haveI : Smooth sB := SmoothOfRelativeDimension.smooth 1 sB
  haveI : LocallyOfFiniteType (t ≫ sB) := hX ▸ inferInstance
  haveI : IsSeparated (t ≫ sB) := hX ▸ inferInstance
  haveI : QuasiCompact (t ≫ sB) := hX ▸ inferInstance
  -- the higher resolution
  haveI : IsProper f := hfres.isProper
  haveI : IsDominant f := hfres.isBirationalMorphism.isDominant
  haveI : Surjective f := Surjective.of_universallyClosed_of_isDominant f
  haveI : IsSeparated (f ≫ t ≫ sB) := by rw [← hX]; infer_instance
  haveI : QuasiCompact (f ≫ t ≫ sB) := by rw [← hX]; infer_instance
  haveI : IsFinite (iT ≫ t) := hfin
  haveI : Etale (iT ≫ t) := het
  haveI : Smooth (iT ≫ t ≫ sB) := by rw [← Category.assoc]; infer_instance
  have hrange : Set.range iT.base = (TX : Set (X : Scheme.{0})) := by
    rw [hiT, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
  let UX : (X : Scheme.{0}).Opens := ⟨(TX : Set (X : Scheme.{0}))ᶜ, TX.isClosed.isOpen_compl⟩
  have hUX : (UX : Set (X : Scheme.{0})) = (Set.range iT.base)ᶜ := by rw [hrange]; rfl
  haveI : IsIso (f ∣_ UX) := hfiso UX rfl
  have hsP' : (⋃ E ∈ sP, (E.support : Set β.target)) = f.base ⁻¹' Set.range iT.base := by
    rwa [hrange]
  have hsnc' : MMP.Mori.DivisorWithCoeffs.IsSNC (f ≫ t ≫ sB)
      (∑ E ∈ sP, Finsupp.single E (1 : ℤ)) := by
    rwa [← hX]
  -- `X ∖ T` is smooth and `T` is singular
  haveI : Smooth (f ≫ X.ι ≫ sY) :=
    MMP.Threefold.Resolution.smooth_of_isSmoothScheme hfres.isSmoothScheme
  have hreg : ∀ y : (X : Scheme.{0}), y ∉ Set.range iT.base → X.ι.base y ∈ smoothLocus sY := by
    intro y hy
    apply image_le_smoothLocus sY X.ι UX (smooth_ι_comp_of_isIso_morphismRestrict f _ UX)
    rw [hrange] at hy
    exact ⟨y, hy, rfl⟩
  have hsing : ∀ y : (X : Scheme.{0}), y ∈ Set.range iT.base → X.ι.base y ∉ smoothLocus sY := by
    intro y hy
    rw [hrange] at hy
    exact mem_singularLocus_iff.1 (hLS.subset_singularLocus hy)
  have hτ : ∀ y : ComplexPoints (t ≫ sB), y.toScheme ∈ Set.range iT.base →
      y ∈ Set.range (realize (sX := iT ≫ t ≫ sB) iT rfl) := fun y hy ↦ by
    rw [hrange] at hy
    exact mem_range_realize_vanishingIdeal TX y hy
  -- generic smoothness of the slices of `π`
  let p : (π ⁻¹ᵁ X : Scheme.{0}) ⟶ B := (π ∣_ X) ≫ t
  letI : (π ⁻¹ᵁ X : Scheme.{0}).Over (Spec (.of ℂ)) := ⟨(π ⁻¹ᵁ X).ι ≫ π ≫ sY⟩
  letI : (B : Scheme.{0}).Over (Spec (.of ℂ)) := ⟨sB⟩
  have hpover : p ≫ sB = (π ⁻¹ᵁ X).ι ≫ π ≫ sY := by
    change ((π ∣_ X) ≫ t) ≫ sB = _
    rw [Category.assoc, ← hX, ← Category.assoc, morphismRestrict_ι, Category.assoc]
  haveI : p.IsOver (Spec (.of ℂ)) := ⟨hpover⟩
  obtain ⟨x0, hx0X, hx0T⟩ := hXT
  haveI : Nonempty (π ⁻¹ᵁ X : Scheme.{0}) := by
    obtain ⟨y, hy⟩ := π.surjective x0
    exact ⟨⟨y, by change π y ∈ X; rw [hy]; exact hx0X⟩⟩
  haveI : Nonempty (B : Scheme.{0}) := ⟨t ⟨x0, hx0X⟩⟩
  haveI : LocallyOfFiniteType ((π ⁻¹ᵁ X : Scheme.{0}) ↘ Spec (.of ℂ)) :=
    inferInstanceAs (LocallyOfFiniteType ((π ⁻¹ᵁ X).ι ≫ π ≫ sY))
  haveI : QuasiCompact ((π ⁻¹ᵁ X : Scheme.{0}) ↘ Spec (.of ℂ)) :=
    inferInstanceAs (QuasiCompact ((π ⁻¹ᵁ X).ι ≫ π ≫ sY))
  haveI : Smooth ((π ⁻¹ᵁ X : Scheme.{0}) ↘ Spec (.of ℂ)) :=
    inferInstanceAs (Smooth ((π ⁻¹ᵁ X).ι ≫ π ≫ sY))
  haveI : LocallyOfFiniteType ((B : Scheme.{0}) ↘ Spec (.of ℂ)) :=
    inferInstanceAs (LocallyOfFiniteType sB)
  haveI : QuasiCompact ((B : Scheme.{0}) ↘ Spec (.of ℂ)) := inferInstanceAs (QuasiCompact sB)
  obtain ⟨B0, hB0, -, -, hgs⟩ := MMP.exists_dense_smooth_restrict_of_smooth (K := ℂ) p
  -- a point of `T ∩ X` over `B₀`
  haveI : Smooth (iT ≫ t) := inferInstance
  haveI : Flat (iT ≫ t) := inferInstance
  haveI : LocallyOfFinitePresentation (iT ≫ t) := inferInstance
  haveI : UniversallyOpen (iT ≫ t) := UniversallyOpen.of_flat (iT ≫ t)
  have hopen : IsOpen (Set.range (iT ≫ t).base) := (iT ≫ t).isOpenMap.isOpen_range
  obtain ⟨z0, hz0⟩ : ∃ z : (Scheme.IdealSheafData.vanishingIdeal TX).subscheme,
      (iT ≫ t).base z ∈ B0 := by
    obtain ⟨z, hz⟩ : (⟨x0, hx0X⟩ : (X : Scheme.{0})) ∈ Set.range iT.base := by
      rw [hrange]
      exact hx0T
    obtain ⟨_, ⟨w, rfl⟩, hw⟩ := hB0.inter_open_nonempty _ hopen ⟨_, ⟨z, rfl⟩⟩
    exact ⟨w, hw⟩
  have hdom : IsDominant p := by
    haveI : Surjective (π ∣_ X) := IsZariskiLocalAtTarget.restrict (P := @Surjective) ‹_› X
    refine ⟨?_⟩
    have h1 : Set.range (iT ≫ t).base ⊆ Set.range p.base := by
      rintro _ ⟨z, rfl⟩
      obtain ⟨w, hw⟩ := (π ∣_ X).surjective (iT z)
      exact ⟨w, by
        change t ((π ∣_ X) w) = t (iT z)
        rw [hw]⟩
    exact (hopen.dense ⟨_, ⟨z0, rfl⟩⟩).mono h1
  -- the dimensions of the base and of the resolution
  have hdimB : topologicalKrullDim (B : Scheme.{0}) = 1 := by
    have hBne : ((B : Set (𝔸(Unit; Spec (.of ℂ))))).Nonempty := ⟨_, (t ⟨x0, hx0X⟩).2⟩
    rw [← topologicalKrullDim_affineLine]
    exact (AlgebraicGeometry.topologicalKrullDim_eq_of_isOpen ℂ _
      (𝔸(Unit; Spec (.of ℂ)) ↘ Spec (.of ℂ)) B B.isOpen hBne).symm
  have hdimV : topologicalKrullDim (π ⁻¹ᵁ X : Scheme.{0}) = 4 := by
    have hne : ((π ⁻¹ᵁ X : Yt.Opens) : Set Yt).Nonempty := by
      obtain ⟨y⟩ := ‹Nonempty (π ⁻¹ᵁ X : Scheme.{0})›
      exact ⟨y.1, y.2⟩
    rw [← hLS.topologicalKrullDim_eq,
      MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (π ≫ sY)
        hLS.isResolution.2.2.2.2]
    exact (AlgebraicGeometry.topologicalKrullDim_eq_of_isOpen ℂ Yt (π ≫ sY) _
      (π ⁻¹ᵁ X).isOpen hne).symm
  -- a `ℂ`-point of `T°` over `B₀`
  let OY : Y.Opens := X.ι ''ᵁ (t ⁻¹ᵁ B0)
  let O : (curveScheme T).Opens := To ⊓ (curveι T) ⁻¹ᵁ OY
  have hOne : (O : Set (curveScheme T)).Nonempty := by
    have h1 : (((curveι T) ⁻¹ᵁ OY : (curveScheme T).Opens) : Set (curveScheme T)).Nonempty := by
      have hmem : X.ι (iT z0) ∈ (T : Set Y) := by
        have : iT z0 ∈ (TX : Set (X : Scheme.{0})) := hrange ▸ ⟨z0, rfl⟩
        exact this
      obtain ⟨w, hw⟩ : X.ι (iT z0) ∈ Set.range (curveι T).base := by
        rw [Scheme.IdealSheafData.range_subschemeι,
          Scheme.IdealSheafData.coe_support_vanishingIdeal]
        exact hmem
      exact ⟨w, by
        change curveι T w ∈ OY
        rw [hw]
        exact ⟨iT z0, hz0, rfl⟩⟩
    obtain ⟨w, hw1, hw2⟩ := hTo.dense.inter_open_nonempty _ ((curveι T) ⁻¹ᵁ OY).isOpen h1
    exact ⟨w, hw2, hw1⟩
  haveI : AlgebraicGeometry.IsVariety ℂ sY := hLS.isProjectiveVariety.toIsVariety
  obtain ⟨w0, hw0⟩ := exists_complexPoints_mem (curveι T ≫ sY) O hOne
  set t₀ : ComplexPoints (To.ι ≫ curveι T ≫ sY) := liftPt To w0 hw0.1 with ht₀
  have hxXmem : (curveOpenInclusion sY To t₀).toScheme ∈ X := by
    obtain ⟨y, -, hy⟩ := hw0.2
    change (curveι T) (To.ι (t₀.toScheme)) ∈ X
    rw [show To.ι t₀.toScheme = w0.toScheme from congrArg ComplexPoints.toScheme
      (realize_liftPt To w0 hw0.1), ← hy]
    exact y.2
  let xX0 := liftPt X (curveOpenInclusion sY To t₀) hxXmem
  let xX : ComplexPoints (t ≫ sB) := ⟨xX0.hom, by rw [← hX]; exact xX0.2⟩
  have hxX : realize X.ι hX xX = curveOpenInclusion sY To t₀ :=
    ComplexPoints.ext (liftPt_hom X (curveOpenInclusion sY To t₀) hxXmem)
  have hxXι : X.ι xX.toScheme = (curveOpenInclusion sY To t₀).toScheme :=
    congrArg ComplexPoints.toScheme hxX
  have hxTX : xX.toScheme ∈ Set.range iT.base := by
    rw [hrange]
    change X.ι xX.toScheme ∈ (T : Set Y)
    rw [hxXι]
    change (curveι T) (To.ι (t₀.toScheme)) ∈ (T : Set Y)
    have : (curveι T) (To.ι (t₀.toScheme)) ∈ Set.range (curveι T).base := ⟨_, rfl⟩
    rwa [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
  have hxB0 : t xX.toScheme ∈ B0 := by
    obtain ⟨y, hy, hyx⟩ := hw0.2
    have : X.ι y = X.ι xX.toScheme := by
      refine hyx.trans ?_
      rw [hxXι]
      change (curveι T) w0.toScheme = (curveι T) (To.ι t₀.toScheme)
      rw [show To.ι t₀.toScheme = w0.toScheme from congrArg ComplexPoints.toScheme
        (realize_liftPt To w0 hw0.1)]
    rw [← X.ι.isOpenEmbedding.injective this]
    exact hy
  have hxT : xX ∈ Set.range (realize (sX := iT ≫ t ≫ sB) iT rfl) := hτ xX hxTX
  set b : ComplexPoints sB := realize t rfl xX with hb
  -- the slice
  -- the residue field at `b` is `ℂ`
  set b' : (B : Scheme.{0}) := b.toScheme with hb'
  have hb'cl : IsClosed ({b'} : Set (B : Scheme.{0})) := isClosed_singleton_toScheme b
  set φ := (B : Scheme.{0}).fromSpecResidueField b' ≫ sB with hφdef
  haveI hφ : IsIso φ := isIso_fromSpecResidueField_comp sB b' hb'cl
  have hbφ : b.hom = inv φ ≫ (B : Scheme.{0}).fromSpecResidueField b' :=
    hom_eq_inv_comp_fromSpecResidueField b b' rfl
  -- the slice `X_b = t⁻¹(b)`
  let sXb : t.fiber b' ⟶ Spec (.of ℂ) := t.fiberToSpecResidueField b' ≫ φ
  have H : IsPullback (t.fiberι b') sXb t b.hom := by
    refine (IsPullback.of_hasPullback t ((B : Scheme.{0}).fromSpecResidueField b')).of_iso
      (Iso.refl _) (Iso.refl _) (asIso φ) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl
    · simp only [Iso.refl_hom, Category.id_comp, asIso_hom]
      rfl
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    · simp only [Iso.refl_hom, Category.comp_id, asIso_hom]
      rw [hbφ, IsIso.hom_inv_id_assoc]
  haveI : IsNormal (t.fiber b') := (hfib b' hb'cl).1
  haveI : LocallyOfFiniteType t := locallyOfFiniteType_of_comp t sB
  haveI : IsSeparated t := IsSeparated.of_comp t sB
  haveI : LocallyOfFiniteType (t.fiberToSpecResidueField b') :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback t _)
      (inferInstance : LocallyOfFiniteType t)
  haveI : IsSeparated (t.fiberToSpecResidueField b') :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback t _)
      (inferInstance : IsSeparated t)
  haveI : LocallyOfFiniteType sXb := by
    change LocallyOfFiniteType (t.fiberToSpecResidueField b' ≫ φ)
    infer_instance
  haveI : IsSeparated sXb := by
    change IsSeparated (t.fiberToSpecResidueField b' ≫ φ)
    infer_instance
  haveI : IsLocallyNoetherian (t.fiber b') := LocallyOfFiniteType.isLocallyNoetherian sXb
  -- the point `x_b` of the slice over `x`
  have hxtb : xX.hom ≫ t = 𝟙 _ ≫ b.hom := by rw [Category.id_comp]; rfl
  let xb : ComplexPoints sXb := ⟨H.lift xX.hom (𝟙 _) hxtb, H.lift_snd _ _ _⟩
  have hxbι : xb.hom ≫ t.fiberι b' = xX.hom := H.lift_fst _ _ _
  have hxbX : (t.fiberι b') xb.toScheme = xX.toScheme := by
    change (xb.hom ≫ t.fiberι b').base default = xX.hom.base default
    rw [hxbι]
  have hfibpt : ∀ q : t.fiber b', t ((t.fiberι b') q) = b' := fun q ↦ by
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.fiber_fac, Scheme.Hom.comp_apply,
      Scheme.fromSpecResidueField_apply]
  -- `x` is isolated in `T ∩ t⁻¹(b)`
  obtain ⟨zx, hzx⟩ := hxTX
  have hzxb : zx ∈ (iT ≫ t).base ⁻¹' {b'} := by
    change t (iT zx) = b'
    rw [hzx]
    rfl
  have hD : _root_.IsDiscrete (iT.base '' ((iT ≫ t).base ⁻¹' {b'})) :=
    ((iT ≫ t).isDiscrete_preimage_singleton b').image iT.isClosedEmbedding.isInducing
  obtain ⟨O, hOo, hO⟩ := isDiscrete_iff_forall_mem_exists_isOpen.1 hD xX.toScheme
    ⟨zx, hzxb, hzx⟩
  have hxO : xX.toScheme ∈ O := by
    have : xX.toScheme ∈ O ∩ iT.base '' ((iT ≫ t).base ⁻¹' {b'}) := hO.symm ▸ rfl
    exact this.1
  let Oop : (X : Scheme.{0}).Opens := ⟨O, hOo⟩
  have hxbO : xb.toScheme ∈ (t.fiberι b') ⁻¹ᵁ Oop := by
    change (t.fiberι b') xb.toScheme ∈ O
    rw [hxbX]
    exact hxO
  -- an affine irreducible neighbourhood `S` of `x_b` meeting `T_b` only in `x_b`
  obtain ⟨V1, hxV1, hV1⟩ := MMP.Mori.exists_mem_opens_forall_irreducibleComponents_eq
    (X := t.fiber b') (Z := ⟨irreducibleComponent xb.toScheme,
      irreducibleComponent_mem_irreducibleComponents _⟩) mem_irreducibleComponent
  obtain ⟨_, ⟨S0, hSaff, rfl⟩, hxS0, hSsub⟩ :=
    (t.fiber b').isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_inter hxV1 hxbO)
      (V1.isOpen.inter ((t.fiberι b') ⁻¹ᵁ Oop).isOpen)
  let S : (t.fiber b').Opens := S0
  have hSZ : (S : Set (t.fiber b')) ⊆ irreducibleComponent xb.toScheme := by
    intro s hs
    have := hV1 ⟨irreducibleComponent s, irreducibleComponent_mem_irreducibleComponents _⟩
      ⟨s, mem_irreducibleComponent, (hSsub hs).1⟩
    have h2 : s ∈ irreducibleComponent s := mem_irreducibleComponent
    rw [show irreducibleComponent s = irreducibleComponent xb.toScheme from
      congrArg Subtype.val this] at h2
    exact h2
  haveI : IrreducibleSpace (S : Scheme.{0}) := by
    have hirr : IsIrreducible (S : Set (t.fiber b')) :=
      ⟨⟨_, hxS0⟩, (isIrreducible_irreducibleComponent.isPreirreducible).open_subset S.isOpen
        hSZ⟩
    exact Subtype.irreducibleSpace hirr
  haveI : IsIntegral (S : Scheme.{0}) := isIntegral_of_irreducibleSpace_of_isReduced _
  haveI : IsAffine (S : Scheme.{0}) := hSaff
  -- the point `x_S` and the punctured neighbourhood `V = S ∖ {x}`
  let xS : ComplexPoints (S.ι ≫ sXb) := liftPt S xb hxS0
  have hxS : xS.hom ≫ S.ι ≫ t.fiberι b' = xX.hom := by
    rw [← Category.assoc, liftPt_hom, hxbι]
  let V : (S : Scheme.{0}).Opens :=
    ⟨{xS.toScheme}ᶜ, (isClosed_singleton_toScheme xS).isOpen_compl⟩
  have hVT : ∀ v : (V : Scheme.{0}), (V.ι ≫ S.ι ≫ t.fiberι b').base v ∉ Set.range iT.base := by
    intro v hv
    apply v.2
    obtain ⟨z, hz⟩ := hv
    have hyO : (t.fiberι b') (S.ι v.1) ∈ O := (hSsub (v.1).2).2
    have hyD : (t.fiberι b') (S.ι v.1) ∈ iT.base '' ((iT ≫ t).base ⁻¹' {b'}) := by
      refine ⟨z, ?_, hz⟩
      change t (iT z) = b'
      rw [show iT z = (t.fiberι b') (S.ι v.1) from hz]
      exact hfibpt _
    have h1 : (t.fiberι b') (S.ι v.1) = xX.toScheme := by
      have : (t.fiberι b') (S.ι v.1) ∈ O ∩ iT.base '' ((iT ≫ t).base ⁻¹' {b'}) := ⟨hyO, hyD⟩
      rw [hO] at this
      exact this
    have h2 : (t.fiberι b') (S.ι v.1) = (t.fiberι b') (S.ι xS.toScheme) := by
      rw [h1, ← hxbX]
      exact congrArg _ (congrArg ComplexPoints.toScheme (realize_liftPt S xb hxS0)).symm
    exact S.ι.isOpenEmbedding.injective ((t.fiberι b').isEmbedding.injective h2)
  -- the slice `Ỹ_b` of the resolution, and its part `W₀` over `S`
  let πb : pullback (π ∣_ X) (t.fiberι b') ⟶ t.fiber b' := pullback.snd _ _
  let W₀ : Scheme.{0} := (πb ⁻¹ᵁ S : (pullback (π ∣_ X) (t.fiberι b')).Opens)
  let f₀ : W₀ ⟶ S := πb ∣_ S
  let κ : W₀ ⟶ Yt := (πb ⁻¹ᵁ S).ι ≫ pullback.fst (π ∣_ X) (t.fiberι b') ≫ (π ⁻¹ᵁ X).ι
  have hκ : IsPullback κ f₀ π (S.ι ≫ t.fiberι b' ≫ X.ι) := by
    have h1 := (isPullback_morphismRestrict πb S).flip
    have h2 := IsPullback.of_hasPullback (π ∣_ X) (t.fiberι b')
    have h3 := (isPullback_morphismRestrict π X).flip
    simpa only [Category.assoc] using (h1.paste_horiz h2).paste_horiz h3
  haveI : IsProper f₀ := MorphismProperty.of_isPullback hκ (inferInstance : IsProper π)
  -- `f₀` is an isomorphism over `V`
  have hVreg : Set.range (V.ι ≫ S.ι ≫ t.fiberι b' ≫ X.ι).base ⊆
      Set.range (smoothLocus sY).ι.base := by
    rintro _ ⟨v, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hreg _ (hVT v)
  let lam : (V : Scheme.{0}) ⟶ (smoothLocus sY : Scheme.{0}) :=
    IsOpenImmersion.lift (smoothLocus sY).ι (V.ι ≫ S.ι ≫ t.fiberι b' ≫ X.ι) hVreg
  have hlam : lam ≫ (smoothLocus sY).ι = V.ι ≫ S.ι ≫ t.fiberι b' ≫ X.ι :=
    IsOpenImmersion.lift_fac _ _ _
  have hV1 : IsPullback ((f₀ ⁻¹ᵁ V).ι ≫ κ) (f₀ ∣_ V) π (V.ι ≫ S.ι ≫ t.fiberι b' ≫ X.ι) :=
    (isPullback_morphismRestrict f₀ V).flip.paste_horiz hκ
  have hSm := (isPullback_morphismRestrict π (smoothLocus sY)).flip
  have hV2 : IsPullback (hSm.lift ((f₀ ⁻¹ᵁ V).ι ≫ κ) ((f₀ ∣_ V) ≫ lam)
      (by rw [hV1.w, Category.assoc, hlam])) (f₀ ∣_ V) (π ∣_ smoothLocus sY) lam := by
    refine IsPullback.of_right ?_ (hSm.lift_snd _ _ _) hSm
    rw [hSm.lift_fst, hlam]
    exact hV1
  haveI : IsIso (π ∣_ smoothLocus sY) := hLS.isBiregular
  haveI hbir : IsIso (f₀ ∣_ V) := hV2.isIso_snd_of_isIso
  let s₀ : (V : Scheme.{0}) ⟶ W₀ := inv (f₀ ∣_ V) ≫ (f₀ ⁻¹ᵁ V).ι
  have hs₀ : s₀ ≫ f₀ = V.ι := by
    rw [Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  -- the slice of the resolution is smooth
  haveI hYbsm : Smooth (πb ≫ sXb) := by
    haveI hfs : Smooth (Scheme.Hom.fiberToSpecResidueField ((π ∣_ X) ≫ t) b') :=
      (hgs hdom b' hxB0).1
    have he : πb ≫ t.fiberToSpecResidueField b' =
        (pullbackRightPullbackFstIso t ((B : Scheme.{0}).fromSpecResidueField b') (π ∣_ X)).hom ≫
          p.fiberToSpecResidueField b' :=
      (pullbackRightPullbackFstIso_hom_snd _ _ _).symm
    change Smooth (πb ≫ t.fiberToSpecResidueField b' ≫ φ)
    rw [← Category.assoc, he]
    haveI h1 : Smooth (pullbackRightPullbackFstIso t ((B : Scheme.{0}).fromSpecResidueField b')
        (π ∣_ X)).hom := inferInstance
    haveI h2 : Smooth φ := inferInstance
    exact MorphismProperty.comp_mem @Smooth _ _ (MorphismProperty.comp_mem @Smooth _ _ h1 hfs) h2
  -- the local dimensions of the slice `Ỹ_b` are `3`
  have hdimfib : ∀ Z ∈ irreducibleComponents (p.fiber b'), topologicalKrullDim Z = 3 :=
    fun Z hZ ↦ by
      have := (hgs hdom b' hxB0).2 Z hZ
      rw [hdimB, hdimV] at this
      exact eq_three_of_add_one_eq_four this
  haveI : LocallyOfFiniteType (π ∣_ X) := inferInstance
  haveI : LocallyOfFiniteType p := inferInstance
  haveI : LocallyOfFiniteType (p.fiberToSpecResidueField b') :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback p _)
      (inferInstance : LocallyOfFiniteType p)
  have hdimAtfib : ∀ y : p.fiber b', topologicalKrullDimAt (p.fiber b') y = 3 :=
    topologicalKrullDimAt_eq_of_forall_irreducibleComponents
      (p.fiberToSpecResidueField b' ≫ φ) hdimfib
  have hdimAtYb : ∀ y : Limits.pullback (C := Scheme.{0}) (π ∣_ X) (t.fiberι b'),
      topologicalKrullDimAt (Limits.pullback (C := Scheme.{0}) (π ∣_ X) (t.fiberι b')) y = 3 :=
    fun y ↦ by
    have h := topologicalKrullDimAt_eq_of_homeomorph (Scheme.homeoOfIso
      (pullbackRightPullbackFstIso t ((B : Scheme.{0}).fromSpecResidueField b') (π ∣_ X))) y
    exact h.trans (hdimAtfib _)
  have hdimAtW : ∀ w : W₀, topologicalKrullDimAt W₀ w = 3 := fun w ↦
    ((πb ⁻¹ᵁ S).isOpen.isOpenEmbedding_subtypeVal.topologicalKrullDimAt_eq w).symm.trans
      (hdimAtYb w.1)
  have hdimO : ∀ O : Set W₀, IsOpen O → ∀ w ∈ O, (3 : WithBot ℕ∞) ≤ topologicalKrullDim O :=
    fun O hO w hw ↦ by
      rw [← hdimAtW w, hO.isOpenEmbedding_subtypeVal.topologicalKrullDimAt_eq ⟨w, hw⟩]
      exact topologicalKrullDimAt_le_topologicalKrullDim _
  -- the fibre `P = f₀⁻¹(x)` has dimension at most two
  have hdimP : topologicalKrullDim (f₀ ⁻¹' {xS.toScheme} : Set W₀) ≤ 2 := by
    set y : Y := (S.ι ≫ t.fiberι b' ≫ X.ι) xS.toScheme with hydef
    have hy : (curveι T).base w0.toScheme = y := by
      have h1 : (S.ι ≫ t.fiberι b') xS.toScheme = xX.toScheme := by
        change (xS.hom ≫ S.ι ≫ t.fiberι b').base default = xX.hom.base default
        rw [hxS]
      have h2 : y = X.ι xX.toScheme := by
        rw [← h1, hydef]
        try rfl
      rw [h2, hxXι]
      change (curveι T) w0.toScheme = (curveι T) (To.ι t₀.toScheme)
      rw [show To.ι t₀.toScheme = w0.toScheme from congrArg ComplexPoints.toScheme
        (realize_liftPt To w0 hw0.1)]
    have hfibd := hTo.topologicalKrullDim_fibre_le ⟨w0.toScheme, hw0.1⟩
    change topologicalKrullDim (pointSettingFibre π ((curveι T).base w0.toScheme)) ≤ 2 at hfibd
    rw [hy] at hfibd
    have h1 : topologicalKrullDim (π.fiber y) = topologicalKrullDim (π ⁻¹' {y} : Set Yt) :=
      (π.fiberHomeo y).isHomeomorph.topologicalKrullDim_eq
    have hmaps : Set.MapsTo κ (f₀ ⁻¹' {xS.toScheme}) (π ⁻¹' {y}) := fun w hw ↦ by
      change π (κ w) = y
      rw [← Scheme.Hom.comp_apply, hκ.w, Scheme.Hom.comp_apply,
        show f₀ w = xS.toScheme from hw]
    refine (Topology.IsInducing.topologicalKrullDim_le
      (f := hmaps.restrict κ _ _) (κ.isEmbedding.isInducing.restrict hmaps)).trans ?_
    rw [← h1]
    exact hfibd
  have not_three_le_two : ¬ ((3 : WithBot ℕ∞) ≤ 2) := fun h ↦
    absurd (show (3 : ℕ) ≤ 2 by exact_mod_cast h) (by omega)
  -- `V` is nonempty
  haveI : Surjective f₀ := MorphismProperty.of_isPullback hκ (inferInstance : Surjective π)
  obtain ⟨w₁, -, hw₁⟩ := Set.not_subset.1 (show ¬ (Set.univ : Set W₀) ⊆
      f₀ ⁻¹' {xS.toScheme} by
    intro h
    obtain ⟨w, -⟩ := f₀.surjective xS.toScheme
    exact not_three_le_two ((hdimO Set.univ isOpen_univ w trivial).trans
      (((Topology.IsEmbedding.inclusion h).isInducing.topologicalKrullDim_le).trans hdimP)))
  have hVne : ((V : Set (S : Scheme.{0}))).Nonempty := ⟨f₀ w₁, hw₁⟩
  -- `W₀` is irreducible
  haveI : Smooth (f₀ ≫ S.ι ≫ sXb) := by
    change Smooth ((πb ∣_ S) ≫ S.ι ≫ sXb)
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    infer_instance
  have hrange_s₀ : Set.range s₀.base = (f₀ ⁻¹ᵁ V : Set W₀) := by
    ext w
    constructor
    · rintro ⟨v, rfl⟩
      exact ((inv (f₀ ∣_ V)).base v).2
    · intro hw
      refine ⟨(f₀ ∣_ V).base ⟨w, hw⟩, ?_⟩
      change ((f₀ ∣_ V ≫ inv (f₀ ∣_ V)) ≫ (f₀ ⁻¹ᵁ V).ι).base ⟨w, hw⟩ = w
      rw [IsIso.hom_inv_id, Category.id_comp]
      rfl
  haveI : IrreducibleSpace (V : Scheme.{0}) := by
    have hirr : IsIrreducible (V : Set (S : Scheme.{0})) :=
      ⟨hVne, (IrreducibleSpace.isIrreducible_univ (S : Scheme.{0})).isPreirreducible.open_subset
        V.isOpen (Set.subset_univ _)⟩
    exact Subtype.irreducibleSpace hirr
  have hs₀irr : IsIrreducible (Set.range s₀.base) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ s₀.continuous.continuousOn
  obtain ⟨C₀, hC₀, hsC₀⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hs₀irr
  have hcomp : ∀ C ∈ irreducibleComponents W₀, C = C₀ := by
    intro C hC
    by_contra hne
    have hdisj := MMP.Flips.ResolutionInputs.disjoint_of_mem_irreducibleComponents_of_smooth
      (f₀ ≫ S.ι ≫ sXb) hC hC₀ hne
    have hCP : C ⊆ f₀ ⁻¹' {xS.toScheme} := by
      intro w hw
      by_contra hwP
      have : w ∈ Set.range s₀.base := by
        rw [hrange_s₀]
        exact hwP
      exact Set.disjoint_left.1 hdisj hw (hsC₀ this)
    obtain ⟨w, hw⟩ := hC.1.nonempty
    exact not_three_le_two ((hdimO C
      (MMP.Flips.ResolutionInputs.isOpen_of_mem_irreducibleComponents_of_smooth
        (f₀ ≫ S.ι ≫ sXb) hC) w hw).trans
      (((Topology.IsEmbedding.inclusion hCP).isInducing.topologicalKrullDim_le).trans hdimP))
  haveI : IrreducibleSpace W₀ := by
    rw [irreducibleSpace_def]
    show IsIrreducible (Set.univ : Set W₀)
    have huniv : (Set.univ : Set W₀) = C₀ := by
      refine Set.eq_of_subset_of_subset (fun w _ ↦ ?_) (Set.subset_univ _)
      rw [← hcomp _ (irreducibleComponent_mem_irreducibleComponents w)]
      exact mem_irreducibleComponent
    rw [huniv]
    exact hC₀.1
  haveI : IsNormal W₀ := isNormal_of_smooth_over_field (f₀ ≫ S.ι ≫ sXb)
  haveI : IsReduced W₀ := isReduced_of_isNormal W₀
  haveI hW₀int : IsIntegral W₀ := isIntegral_of_irreducibleSpace_of_isReduced _
  -- `S` is a threefold
  have hSdim : topologicalKrullDim (S : Scheme.{0}) = 3 := by
    have hne' : ((f₀ ⁻¹ᵁ V : W₀.Opens) : Set W₀).Nonempty := ⟨w₁, hw₁⟩
    rw [AlgebraicGeometry.topologicalKrullDim_eq_of_isOpen ℂ _ (S.ι ≫ sXb) V V.isOpen hVne]
    refine ((Scheme.homeoOfIso (asIso (f₀ ∣_ V))).isHomeomorph.topologicalKrullDim_eq).symm.trans
      ?_
    change topologicalKrullDim ((f₀ ⁻¹ᵁ V : W₀.Opens) : Set W₀) = 3
    rw [← AlgebraicGeometry.topologicalKrullDim_eq_of_isOpen ℂ W₀ (f₀ ≫ S.ι ≫ sXb) _
      (f₀ ⁻¹ᵁ V).isOpen hne',
      AlgebraicGeometry.topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible ℂ W₀
        (f₀ ≫ S.ι ≫ sXb) w₁]
    exact hdimAtW w₁
  -- the resolution `f₀` of `S`
  haveI : LocallyOfFiniteType (S.ι ≫ sXb) := inferInstance
  haveI : IsSeparated (S.ι ≫ sXb) := inferInstance
  haveI : QuasiCompact (S.ι ≫ sXb) := inferInstance
  have hSqp : Stacks.HProjective.IsQuasiProjective (S.ι ≫ sXb) :=
    Stacks.HProjective.isQuasiProjective_of_isQuasiAffineHom _ inferInstance
  have hf₀proj : IsProjectiveMorphism f₀ := by
    obtain ⟨n, i, hi, hcomp⟩ := hLS.isResolution.2.2.2.1.baseChange (S.ι ≫ t.fiberι b' ≫ X.ι)
    refine ⟨n, hκ.isoPullback.hom ≫ i, ?_, ?_⟩
    · haveI := hi
      infer_instance
    · rw [Category.assoc, hcomp, IsPullback.isoPullback_hom_snd]
  have hres : MMP.Resolution.IsResolutionOfVariety (S.ι ≫ sXb) f₀ :=
    { isVariety := { toIsIntegral := inferInstance }
      isVariety_source := { toIsIntegral := hW₀int }
      isProjective := hf₀proj.isProjective
      isBirationalMorphism := by
        haveI : IrreducibleSpace W₀ := inferInstance
        refine MMP.Flips.isBirationalMorphism_of_isIso_resLE f₀ (f₀ ⁻¹ᵁ V) V ?_ hVne le_rfl
          ?_
        · obtain ⟨v, hv⟩ := hVne
          obtain ⟨w, hw⟩ := (f₀ ∣_ V).surjective ⟨v, hv⟩
          exact ⟨_, w.2⟩
        · rw [Scheme.Hom.resLE_eq_morphismRestrict]
          exact hbir
      isSmoothScheme := by
        rw [MMP.Mori.IsSmoothScheme, eq_top_iff]
        apply le_smoothLocus
        infer_instance }
  have hsm : V ≤ smoothLocus (S.ι ≫ sXb) :=
    le_smoothLocus _ (smooth_ι_comp_of_isIso_morphismRestrict f₀ _ V)
  have hsurj := surjective_stalk_higherDirectImageRestriction_two (S.ι ≫ sXb) hSdim hSqp f₀
    hres xS ⊤ trivial V (by ext v; simp [V]) hsm hbir s₀ hs₀
  refine ⟨t₀, surjective_localSystemRestrictionFibre_of_forall sY hLS.isBiregular To t₀
    fun O hO γ ↦ ?_⟩
  rw [← hxX] at hO ⊢
  exact exists_restrict_eq_of_slice hLS.isBiregular t hX f iT UX hUX hfsm sP hsP' hsnc' hstr hreg
    hsing hτ b xX hxT rfl (t.fiberι b') sXb H S xS hxS V rfl hVT f₀ s₀ hs₀ κ hκ hsurj O hO γ

end MMP.Fold06.LemMmpConductorCurvePuncturedRestrictionSurjective

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori MMP.Analytic MMP.Analytic.ComplexPoints

/-- In a local setting `(Y, Θ, T, π)`, for every `π`-adapted open `T° ⊆ T`, the restriction map
`r : (R²π_* ℚ_Ỹ)|_{T°} ⟶ (R²j_* ℚ_{Y_reg})|_{T°}` is surjective on every fibre. -/
@[mmp "lem_mmp_conductor_curve_punctured_restriction_surjective"]
public theorem surjective_localSystemRestrictionFibre {Y Yt : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
    (hLS : IsLocalSetting sY Θ T π) {To : (curveScheme T).Opens} (hTo : IsAdaptedOpen sY π To)
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) :
    Function.Surjective (localSystemRestrictionFibre sY hLS.isBiregular To t).hom := by
  haveI : AlgebraicGeometry.IsVariety ℂ sY := hLS.isProjectiveVariety.toIsVariety
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI : IsLocallyNoetherian (curveScheme T) :=
    LocallyOfFiniteType.isLocallyNoetherian (curveι T ≫ sY)
  haveI : CompactSpace (curveScheme T) :=
    QuasiCompact.compactSpace_of_compactSpace (curveι T ≫ sY)
  haveI : IsNoetherian (curveScheme T) := ⟨⟩
  haveI : Smooth (To.ι ≫ curveι T ≫ sY) := hTo.smooth
  haveI : ConnectedSpace To := hTo.connectedSpace
  haveI : IsIntegral (To : Scheme.{0}) :=
    Stacks.Chow.isIntegral_of_connectedSpace_of_smooth (To.ι ≫ curveι T ≫ sY)
  haveI : ConnectedSpace (analyticSpace (To.ι ≫ curveι T ≫ sY)) :=
    connectedSpace_analyticSpace _
  haveI : LocallyPathConnectedSpace (analyticSpace (To.ι ≫ curveι T ≫ sY)) :=
    locallyPathConnectedSpace_analyticSpace _
  haveI := PathConnectedSpace.of_locallyPathConnectedSpace
    (X := analyticSpace (To.ι ≫ curveι T ≫ sY))
  open MMP.Fold06.LemMmpConductorCurvePuncturedRestrictionSurjective in
  obtain ⟨t₀, ht₀⟩ := exists_surjective_localSystemRestrictionFibre hLS hTo
  open MMP.Fold06.LemMmpConductorCurvePuncturedRestrictionSurjective in
  exact surjective_stalk_of_isLocalSystem hTo.isLocalSystem_resolution hTo.isLocalSystem
    (localSystemRestriction sY hLS.isBiregular To) t₀ t ht₀

end MMP.Fourfold
