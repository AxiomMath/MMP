module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
import StacksFrontier.AlgebraicGeometry.GenericFlatness.NoetherianFlatStratification
import MMP.AlgebraicGeometry.SpreadingOut.GenericFibreDimension
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting.GenericLocalSystems

/-!
# Adapted opens exist

Let `(Y, Θ, T, π)` be a local setting (`MMP.Fourfold.IsLocalSetting`). Then the curve `T` has a
`π`-adapted open (`MMP.Fourfold.IsAdaptedOpen`), and the class of `π`-adapted opens is stable
under shrinking: every connected dense Zariski-open subset of a `π`-adapted open is again
`π`-adapted.

## Main results

* `MMP.Fourfold.IsLocalSetting.exists_isAdaptedOpen_and_isAdaptedOpen_of_le`

## Implementation notes

* Zariski-opens of `T` are opens of the reduced curve `MMP.Fourfold.curveScheme T`, and a
  subset `U ⊆ T°` is an inequality `U ≤ T°` of such opens. Density is density in `T`; for an
  open `U ⊆ T°` with `T°` dense in the irreducible `T` this is the same as density in `T°`.
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MMP.Mori MMP.Analytic
  MMP.Analytic.ComplexPoints MMP.Fourfold

namespace Proof_lem_oai4_c2_adapted_open_exists

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

noncomputable section

variable {X Y Z : TopCat.{0}}

/-- Global sections of a pushforward are global sections. -/
private def pushforwardTopIso (f : X ⟶ Y) :
    TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f ⋙
        (sheafSections (Opens.grothendieckTopology Y) (ModuleCat.{0} ℚ)).obj (Opposite.op ⊤) ≅
      (sheafSections (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ)).obj (Opposite.op ⊤) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- The inverse image of a constant sheaf is constant. -/
private def pullbackConstIso (f : X ⟶ Y) :
    constantSheaf (Opens.grothendieckTopology Y) (ModuleCat.{0} ℚ) ⋙
        TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f ≅
      constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ) :=
  (((constantSheafAdj _ (ModuleCat.{0} ℚ) isTerminalTop).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f)).ofNatIsoRight
      (pushforwardTopIso f)).leftAdjointUniq (constantSheafAdj _ (ModuleCat.{0} ℚ) isTerminalTop)

/-- Pushforwards compose. -/
private def pushforwardCompIso (g : X ⟶ Y) (f : Y ⟶ Z) :
    TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) g ⋙ TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f ≅
      TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (g ≫ f) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- Inverse images compose. -/
private def pullbackCompIso (g : X ⟶ Y) (f : Y ⟶ Z) :
    TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f ⋙ TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) g ≅
      TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) (g ≫ f) :=
  (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) g)).ofNatIsoRight
      (pushforwardCompIso g f)).leftAdjointUniq
        (TopCat.Sheaf.pullbackPushforwardAdjunction _ (g ≫ f))

/-- The inverse image of a local system along a continuous map is a local system. -/
private theorem isLocalSystem_pullback (f : X ⟶ Y) {F : TopCat.Sheaf (ModuleCat.{0} ℚ) Y}
    (hF : IsLocalSystem F) : IsLocalSystem ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj F) := by
  intro x
  obtain ⟨V, hx, E, hE, ⟨e⟩⟩ := hF (f x)
  let V' : Opens X := (Opens.map f).obj V
  let f' : TopCat.of V' ⟶ TopCat.of V :=
    TopCat.ofHom
      ⟨fun y => ⟨f y.1, y.2⟩, (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩
  have comm : V'.inclusion' ≫ f = f' ≫ V.inclusion' := rfl
  exact ⟨V', hx, E, hE, ⟨(pullbackCompIso V'.inclusion' f).app F ≪≫
    eqToIso (by rw [comm]; rfl) ≪≫ (pullbackCompIso f' V.inclusion').symm.app F ≪≫
    (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f').mapIso e ≪≫ (pullbackConstIso f').app E⟩⟩

private theorem isLocalSystem_of_iso {F G : TopCat.Sheaf (ModuleCat.{0} ℚ) X} (i : F ≅ G)
    (hF : IsLocalSystem F) : IsLocalSystem G := by
  intro x
  obtain ⟨V, hx, E, hE, ⟨e⟩⟩ := hF x
  exact ⟨V, hx, E, hE, ⟨(TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) V.inclusion').mapIso i.symm ≪≫ e⟩⟩

end

variable {Y Yt : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}

/-- `U^an ⟶ Y^an` factors through `T°^an` for `U ⊆ T°`. -/
private theorem curveOpenInclusion_eq {To U : (curveScheme T).Opens} (hUT : U ≤ To) :
    curveOpenInclusion sY U =
      analyticMap ((curveScheme T).homOfLE hUT)
        (by rw [Scheme.homOfLE_ι_assoc]) ≫ curveOpenInclusion sY To := by
  unfold curveOpenInclusion
  rw [analyticMap_comp]
  congr 1
  rw [Scheme.homOfLE_ι_assoc]

/-- A sheaf on `Y^an` whose inverse image to `T°^an` is a local system has a local system as
inverse image to `U^an` for every Zariski-open `U ⊆ T°`. -/
private theorem isLocalSystem_pullback_curveOpenInclusion_of_le {To U : (curveScheme T).Opens}
    (hUT : U ≤ To) {F : TopCat.Sheaf (ModuleCat.{0} ℚ) (analyticSpace sY)}
    (hF : IsLocalSystem
      ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) (curveOpenInclusion sY To)).obj F)) :
    IsLocalSystem ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) (curveOpenInclusion sY U)).obj F) :=
  isLocalSystem_of_iso
    ((pullbackCompIso _ _).app _ ≪≫ eqToIso (by rw [← curveOpenInclusion_eq hUT]))
    (isLocalSystem_pullback _ hF)

/-- For `U ⊆ T°`, the family `Ỹ ×_Y U ⟶ U` is the base change of `Ỹ ×_Y T° ⟶ T°` along
`U ⟶ T°`. -/
private theorem pullback_snd_eq_of_le {To U : (curveScheme T).Opens} (hUT : U ≤ To) :
    pullback.snd π (U.ι ≫ curveι T) =
      (pullback.congrHom rfl (Scheme.homOfLE_ι_assoc _ hUT _).symm ≪≫
        (pullbackLeftPullbackSndIso π (To.ι ≫ curveι T) ((curveScheme T).homOfLE hUT)).symm).hom ≫
        pullback.snd (pullback.snd π (To.ι ≫ curveι T)) ((curveScheme T).homOfLE hUT) := by
  simp

private theorem isProjectiveMorphism_iso_comp {A B S : Scheme.{0}} (e : A ≅ B) {f : B ⟶ S}
    (hf : IsProjectiveMorphism f) : IsProjectiveMorphism (e.hom ≫ f) := by
  obtain ⟨n, i, hi, rfl⟩ := hf
  exact ⟨n, e.hom ≫ i, inferInstance, by simp⟩

/-- Flatness of `Ỹ ×_Y T° ⟶ T°` is inherited by Zariski-opens `U ⊆ T°`. -/
private theorem flat_pullback_snd_of_le {To U : (curveScheme T).Opens} (hUT : U ≤ To)
    (hfl : Flat (pullback.snd π (To.ι ≫ curveι T))) : Flat (pullback.snd π (U.ι ≫ curveι T)) := by
  rw [pullback_snd_eq_of_le hUT]
  infer_instance

/-- Connected dense opens of a `π`-adapted open are `π`-adapted. -/
private theorem isAdaptedOpen_of_le {To U : (curveScheme T).Opens} (hTo : IsAdaptedOpen sY π To)
    (hUT : U ≤ To) (hconn : ConnectedSpace U) (hdense : Dense (U : Set (curveScheme T))) :
    IsAdaptedOpen sY π U where
  connectedSpace := hconn
  smooth := by
    have := hTo.smooth
    rw [← Scheme.homOfLE_ι_assoc _ hUT]
    infer_instance
  dense := hdense
  isLocalSystem := isLocalSystem_pullback_curveOpenInclusion_of_le hUT hTo.isLocalSystem
  isLocalSystem_resolution :=
    isLocalSystem_pullback_curveOpenInclusion_of_le hUT hTo.isLocalSystem_resolution
  topologicalKrullDim_fibre_le t := hTo.topologicalKrullDim_fibre_le ⟨t.1, hUT t.2⟩
  flat := flat_pullback_snd_of_le hUT hTo.flat
  isProjectiveMorphism := by
    rw [pullback_snd_eq_of_le hUT]
    exact isProjectiveMorphism_iso_comp _ (hTo.isProjectiveMorphism.baseChange _)

/-- Smoothness over `ℂ` of an open of the curve contained in its smooth locus. -/
private theorem smooth_of_le_smoothLocus [LocallyOfFinitePresentation (curveι T ≫ sY)]
    {To : (curveScheme T).Opens} (hle : To ≤ (curveι T ≫ sY).smoothLocus) :
    Smooth (To.ι ≫ curveι T ≫ sY) := by
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
  exact top_le_iff.mp fun x _ => hle x.2

section Topology

open Topology

/-- Let `f : X → Z` be a continuous closed map out of an irreducible space with
`dim X ≤ n + 2`, and `y ∈ Z` a point having a specialization `t` that does not generalize back
to `y`, and such that some point of `X` maps outside `closure {y}`. Then the fibre `f⁻¹(y)` has
dimension at most `n`. -/
private theorem topologicalKrullDim_preimage_singleton_le {X Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Z] [IrreducibleSpace X] {f : X → Z} (hf : Continuous f)
    (hcl : IsClosedMap f) {y t : Z} (ht : t ∈ closure {y}) (hyt : y ∉ closure {t}) {x₀ : X}
    (hx₀ : f x₀ ∉ closure {y}) {n : ℕ}
    (hX : topologicalKrullDim X ≤ ((n + 2 : ℕ) : WithBot ℕ∞)) :
    topologicalKrullDim (f ⁻¹' {y}) ≤ (n : WithBot ℕ∞) := by
  unfold topologicalKrullDim at *
  let m := IrreducibleCloseds.map ((↑) : f ⁻¹' {y} → X) continuous_subtype_val
  have hm : StrictMono m := IrreducibleCloseds.map_strictMono_of_isInducing IsInducing.subtypeVal
  refine iSup_le fun p => ?_
  obtain ⟨z, hz⟩ := p.head.isIrreducible.nonempty
  have hzm : z.1 ∈ (m p.head : Set X) := subset_closure ⟨z, hz, rfl⟩
  have hfz : f z.1 = y := z.2
  have hyimg : y ∈ f '' (m p.head : Set X) := ⟨z.1, hzm, hfz⟩
  obtain ⟨x', hx'm, hx't⟩ : t ∈ f '' (m p.head : Set X) :=
    closure_minimal (Set.singleton_subset_iff.mpr hyimg) (hcl _ (m p.head).isClosed) ht
  let b : IrreducibleCloseds X := ⟨closure {x'}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hb : b < m p.head := by
    refine lt_of_le_of_ne
      (show (b : Set X) ⊆ m p.head from
        closure_minimal (Set.singleton_subset_iff.mpr hx'm) (m p.head).isClosed) ?_
    intro heq
    have hzb : z.1 ∈ (b : Set X) := by rwa [heq]
    have h2 : f z.1 ∈ closure {t} := by
      rw [← hx't, ← Set.image_singleton]
      exact image_closure_subset_closure_image hf ⟨z.1, hzb, rfl⟩
    exact hyt (hfz ▸ h2)
  let tp : IrreducibleCloseds X := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have htp : m p.last < tp := by
    refine lt_of_le_of_ne (show (m p.last : Set X) ⊆ tp from Set.subset_univ _) ?_
    intro heq
    have hx : x₀ ∈ (m p.last : Set X) := by rw [heq]; exact Set.mem_univ x₀
    apply hx₀
    have h1 := image_closure_subset_closure_image hf ⟨x₀, hx, rfl⟩
    refine closure_minimal ?_ isClosed_closure h1
    rintro _ ⟨_, ⟨w, -, rfl⟩, rfl⟩
    exact subset_closure w.2
  let q : LTSeries (IrreducibleCloseds X) :=
    ((p.map m hm).cons b (by simpa using hb)).snoc tp (by simpa using htp)
  have hq := (Order.LTSeries.length_le_krullDim q).trans hX
  rw [show q.length = p.length + 2 by simp [q]] at hq
  have : p.length + 2 ≤ n + 2 := by exact_mod_cast hq
  exact_mod_cast (by omega : p.length ≤ n)

end Topology

section Existence

/-- The closed immersion `T ⟶ Y` has image `T`. -/
private theorem range_curveι (T : IrreducibleCloseds Y) :
    Set.range (curveι T) = (T : Set Y) := by
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

/-- The reduced curve `T` is irreducible. -/
private theorem irreducibleSpace_curveScheme (T : IrreducibleCloseds Y) :
    IrreducibleSpace (curveScheme T) := by
  have : IrreducibleSpace (Set.range (curveι T)) :=
    Subtype.irreducibleSpace (by rw [range_curveι]; exact T.isIrreducible)
  let e := (curveι T).isClosedEmbedding.toIsEmbedding.toHomeomorph
  exact Function.Surjective.irreducibleSpace e.symm.continuous e.symm.surjective

/-- The closed immersion `T ⟶ Y` sends the generic point of the curve to `η_T`. -/
private theorem curveι_genericPoint (T : IrreducibleCloseds Y) [IrreducibleSpace (curveScheme T)] :
    curveι T (genericPoint (curveScheme T)) = localSettingGenericPoint T := by
  have h := (genericPoint_spec (curveScheme T)).image (curveι T).continuous
  rw [Set.image_univ, range_curveι, T.isClosed.closure_eq] at h
  exact h.eq (isGenericPoint_localSettingGenericPoint T)

/-- In a local setting, the scheme fibre `F_{η_T}` of `π` over the generic point of `T` has
dimension at most two. -/
private theorem fiberDimension_localSettingGenericPoint_le [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {Θ : QDivisor Y} (h : IsLocalSetting sY Θ T π) :
    π.fiberDimension (localSettingGenericPoint T) ≤ ((2 : ℕ) : WithBot ℕ∞) := by
  obtain ⟨hvar, hvar', -, hproj, hbir⟩ := h.isResolution
  have : IsProper π := isProper_of_isProjectiveMorphism π hproj
  have : IsIntegral Yt := hvar'.toIsIntegral
  have hdim : topologicalKrullDim Yt = 4 := by
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (π ≫ sY) hbir]
    exact h.topologicalKrullDim_eq
  set η := localSettingGenericPoint T
  have hη : IsGenericPoint η (T : Set Y) := isGenericPoint_localSettingGenericPoint T
  have hTne : (T : Set Y) ≠ Set.univ := by
    intro hT
    have h1 := h.topologicalKrullDim_curve
    rw [hT, IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ Y).isHomeomorph,
      h.topologicalKrullDim_eq] at h1
    exact absurd h1 (by decide)
  obtain ⟨t, htT, htη⟩ : ∃ t ∈ (T : Set Y), t ≠ η := by
    by_contra hcon
    push Not at hcon
    have : Subsingleton (T : Set Y) :=
      ⟨fun a b => Subtype.ext ((hcon a.1 a.2).trans (hcon b.1 b.2).symm)⟩
    have : Nonempty (T : Set Y) := ⟨⟨η, hη.mem⟩⟩
    have h1 := h.topologicalKrullDim_curve
    have h0 := topologicalKrullDim_zero_of_discreteTopology (T : Set Y)
    rw [h1] at h0
    exact absurd h0 (by decide)
  have ht : t ∈ closure {η} := by rw [hη.def]; exact htT
  have hyt : η ∉ closure {t} := fun hηt =>
    htη ((specializes_iff_mem_closure.2 hηt).antisymm (specializes_iff_mem_closure.2 ht)).eq
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : Yt, π x₀ ∉ (T : Set Y) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨W, ⟨w, hw⟩, hWi⟩ := hbir.exists_isOpenImmersion
    have hO : IsOpen (Set.range (W.ι ≫ π)) := (W.ι ≫ π).isOpenEmbedding.isOpen_range
    have hsub : Set.range (W.ι ≫ π) ⊆ (T : Set Y) := by
      rintro _ ⟨v, rfl⟩
      simpa using hcon (W.ι v)
    have hne : (Set.range (W.ι ≫ π)).Nonempty := ⟨_, ⟨⟨w, hw⟩, rfl⟩⟩
    apply hTne
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (hO.dense hne).closure_eq, ← T.isClosed.closure_eq]
    exact closure_mono hsub
  have hle := topologicalKrullDim_preimage_singleton_le (f := π) π.continuous π.isClosedMap ht hyt
    (x₀ := x₀) (by rwa [hη.def]) (n := 2) (by rw [hdim]; rfl)
  unfold Scheme.Hom.fiberDimension
  rwa [(π.fiberHomeo η).isHomeomorph.topologicalKrullDim_eq]

/-- In a local setting, the scheme fibres of `π` over the points of a nonempty Zariski-open of
`T` have dimension at most two. -/
private theorem exists_nonempty_forall_topologicalKrullDim_fibre_le [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {Θ : QDivisor Y} (h : IsLocalSetting sY Θ T π) :
    ∃ V : (curveScheme T).Opens, (V : Set (curveScheme T)).Nonempty ∧
      ∀ t ∈ V, topologicalKrullDim (pointSettingFibre π ((curveι T).base t)) ≤ 2 := by
  obtain ⟨-, -, -, hproj, -⟩ := h.isResolution
  have : IsProper π := isProper_of_isProjectiveMorphism π hproj
  have := irreducibleSpace_curveScheme T
  have hgen := fiberDimension_localSettingGenericPoint_le h
  rw [← curveι_genericPoint T] at hgen
  obtain ⟨V, hVne, hV⟩ := exists_nonempty_open_fiberDimension_le (pullback.snd π (curveι T)) 2
    (genericPoint (curveScheme T)) (genericPoint_spec (curveScheme T))
    (by rwa [Scheme.Hom.fiberDimension_pullback_snd])
  refine ⟨V, hVne, fun t ht => ?_⟩
  have := hV t ht
  rw [Scheme.Hom.fiberDimension_pullback_snd] at this
  exact_mod_cast this

/-- In a local setting, the curve `T` has a `π`-adapted open. -/
private theorem exists_isAdaptedOpen [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {Θ : QDivisor Y} (h : IsLocalSetting sY Θ T π) :
    ∃ To : (curveScheme T).Opens, IsAdaptedOpen sY π To := by
  obtain ⟨hvar, -, -, hproj, -⟩ := h.isResolution
  have : IsProper π := isProper_of_isProjectiveMorphism π hproj
  have : LocallyOfFiniteType sY := hvar.toLocallyOfFiniteType
  have : QuasiCompact sY := hvar.toQuasiCompact
  have := irreducibleSpace_curveScheme T
  have : IsReduced (curveScheme T) :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  obtain ⟨Us, hUsne, hUss, hloc⟩ := h.exists_isLocalSystem_higherDirectImage
  have hUs : Dense (Us : Set (curveScheme T)) := Us.isOpen.dense hUsne
  obtain ⟨Uf, hUf, hflat⟩ :=
    exists_dense_open_flat_pullback_vanishingIdeal π ⟨(T : Set Y), T.isClosed⟩
  obtain ⟨Vd, hVd, hdim⟩ := exists_nonempty_forall_topologicalKrullDim_fibre_le h
  let To : (curveScheme T).Opens := Us ⊓ Uf ⊓ Vd
  have hdense : Dense (To : Set (curveScheme T)) := by
    simp only [To, Opens.coe_inf]
    exact (hUs.inter_of_isOpen_left hUf Us.isOpen).inter_of_isOpen_left (Vd.isOpen.dense hVd)
      (Us.isOpen.inter Uf.isOpen)
  have hTs : To ≤ Us := le_trans inf_le_left inf_le_left
  have hTf : To ≤ Uf := le_trans inf_le_left inf_le_right
  have hTd : To ≤ Vd := inf_le_right
  obtain ⟨⟨hπ, -⟩, hj⟩ := hloc To hTs 2
  have : Nonempty To := hdense.nonempty.to_subtype
  have : IrreducibleSpace To :=
    To.isOpen.isOpenEmbedding_subtypeVal.irreducibleSpace (f := ((↑) : To → curveScheme T))
  exact ⟨To,
    { connectedSpace := inferInstance
      smooth := smooth_of_le_smoothLocus
        (hTs.trans (hUss.trans (smoothLocus_eq_smoothLocus _).le))
      dense := hdense
      isLocalSystem := hj
      isLocalSystem_resolution := hπ
      topologicalKrullDim_fibre_le := fun t => hdim t.1 (hTd t.2)
      flat := flat_pullback_snd_of_le hTf hflat
      isProjectiveMorphism := hproj.baseChange _ }⟩

end Existence

end Proof_lem_oai4_c2_adapted_open_exists

end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MMP.Mori

namespace MMP.Fourfold.IsLocalSetting

/-- In a local setting `(Y, Θ, T, π)`, the curve `T` has a `π`-adapted open, and every
connected dense Zariski-open subset of a `π`-adapted open is `π`-adapted. -/
@[mmp "lem_oai4_c2_adapted_open_exists"]
public theorem exists_isAdaptedOpen_and_isAdaptedOpen_of_le
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
    (h : IsLocalSetting sY Θ T π) :
    (∃ To : (curveScheme T).Opens, IsAdaptedOpen sY π To) ∧
      ∀ To U : (curveScheme T).Opens, IsAdaptedOpen sY π To → U ≤ To → ConnectedSpace U →
        Dense (U : Set (curveScheme T)) → IsAdaptedOpen sY π U :=
  ⟨Proof_lem_oai4_c2_adapted_open_exists.exists_isAdaptedOpen h,
    fun _ _ => Proof_lem_oai4_c2_adapted_open_exists.isAdaptedOpen_of_le⟩

end MMP.Fourfold.IsLocalSetting
