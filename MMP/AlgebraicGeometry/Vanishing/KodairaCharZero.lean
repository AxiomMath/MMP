module

public import MMP.AlgebraicGeometry.Vanishing.KodairaComplex
public import MMP.AlgebraicTopology.PoincareDualityGoodCover
public import MMP.Analysis.Convex.FiniteDimensional

/-!
# Kodaira vanishing over an algebraically closed field of characteristic zero

Let `X` be a smooth projective variety of dimension `n` over an algebraically closed field `k`
of characteristic zero, and let `L` be an ample line bundle on `X`. Then
`H^i(X, L^{-1}) = 0` for every `i < n`.

Kollár and Mori prove this over `ℂ` by Hodge theory. Over a general `k` one descends `X` and `L`
to a finitely generated subfield `k₀ ⊆ k`, embeds `k₀` into `ℂ`, and compares dimensions of
cohomology by flat base change.

## Main results

* `MMP.Mori.subsingleton_derivedCohomologyOverField_dualSheaf_of_isAmple`: Kodaira vanishing
  `H^i(X, L^{-1}) = 0` for `i < dim X`.
* `MMP.Intersection.isAmple_of_stacksIsAmple`, `MMP.Intersection.IsAmple.stacksIsAmple`: on a
  proper scheme over a field, Stacks ampleness agrees with having a very ample power.

## Implementation notes

* `H^i(X, ℱ)` for `i : ℤ` is `Stacks.Duality.derivedCohomologyOverField f` of `ℱ` placed in
  degree zero, as in `MMP.Mori.subsingleton_dual_iff_subsingleton_exteriorPower_tensor`. It
  agrees with sheaf cohomology for `i ≥ 0` and vanishes for `i < 0`, so the statement for every
  integer `i < n` contains the one for `0 ≤ i < n`.
* `L^{-1}` is the dual `Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf L`, and ampleness
  is `Stacks.Ample.IsAmple` (Stacks Tag 01PS).
* A smooth projective variety of dimension `n` is a projective variety
  (`MMP.Mori.IsProjectiveVariety`) whose smooth locus is everything (`MMP.Mori.IsSmoothScheme`)
  with `topologicalKrullDim X = n`.

## References

* [J. Kollár and S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998],
  Theorem 2.47
-/

@[expose] public section

section

/-!
## Proof: Kodaira vanishing over an algebraically closed field of characteristic zero

Let `X` be a smooth projective variety of dimension `n` over an algebraically closed field `k` of
characteristic zero and `L` an ample invertible sheaf on `X`. Then `H^i(X, L^{-1}) = 0` for
`i < n`.

The proof reduces to the complex case. The polarized variety `(X, L)` is the base change of a
smooth projective geometrically integral polarized variety `(X₀, L₀)` over a subfield `k₀ ⊆ k`
finitely generated over `ℚ`. Such a field is countable, so it embeds into `ℂ`, and the base change
`(X_ℂ, L_ℂ)` is a smooth projective polarized complex variety of dimension `n`. By flat base change
along `Spec k ⟶ Spec k₀` and `Spec ℂ ⟶ Spec k₀`,
`dim_k H^i(X, L^{-1}) = dim_{k₀} H^i(X₀, L₀^{-1}) = dim_ℂ H^i(X_ℂ, L_ℂ^{-1})`, and the last
dimension is zero by Kodaira vanishing over `ℂ`.

## References

* [J. Kollár and S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998],
  Theorem 2.47
* [R. Hartshorne, *Algebraic geometry*][Hartshorne1977], III.9.3
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Stacks.SmallDerivedModel

universe u

noncomputable section

namespace MMP.Intersection

variable (F : Type u) [Field F] {X : Scheme.{u}} [X.Over (Spec (.of F))]

/-- On a proper scheme over a field a Stacks-ample invertible sheaf is ample in the sense of
`MMP.Intersection.IsAmple`: some power of it is very ample. -/
theorem isAmple_of_stacksIsAmple [IsProper (X ↘ Spec (.of F))]
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : Stacks.Ample.IsAmple X L) : IsAmple F L := by
  have : Stacks.Ample.IsInvertibleModule X L := ‹_›
  obtain ⟨d₀, hd₀, himm⟩ :=
    ((Stacks.AmpleRelativeFiniteType.tfae_six (X ↘ Spec (.of F)) L).out 1 6).1 hL
  obtain ⟨eP⟩ := MMP.Resolution.Bridges.nonempty_tensorPow_iso_tensorPowModule X L d₀
  exact ⟨d₀, hd₀, MMP.Resolution.Bridges.isVeryAmple_of_hasImmersionTwistOver F _ _ eP
    (himm d₀ le_rfl)⟩

variable {F} in
/-- Conversely, an invertible sheaf with a very ample power is Stacks-ample. -/
theorem IsAmple.stacksIsAmple [LocallyOfFiniteType (X ↘ Spec (.of F))]
    [QuasiCompact (X ↘ Spec (.of F))] {L : X.Modules}
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : IsAmple F L) : Stacks.Ample.IsAmple X L := by
  have : Stacks.Ample.IsInvertibleModule X L := ‹_›
  obtain ⟨m, hm, hva⟩ := hL
  obtain ⟨eP⟩ := MMP.Resolution.Bridges.nonempty_tensorPow_iso_tensorPowModule X L m
  have h5 : ∃ d : ℕ, 1 ≤ d ∧ Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver
      (X ↘ Spec (.of F)) (Stacks.Ample.tensorPowModule X L (d : ℤ)) :=
    ⟨m, hm, MMP.Resolution.Bridges.hasImmersionTwistOver_of_isVeryAmple F _ _ hva eP.symm⟩
  exact ((Stacks.AmpleRelativeFiniteType.tfae_six (X ↘ Spec (.of F)) L).out 5 1).1 h5

end MMP.Intersection

namespace MMP.FourfoldProofs.Km2cKodairaVanishingCharZeroProof

/-- `H^j(X, G)`, the cohomology over the base field of a module placed in degree zero. -/
private abbrev H {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (G : X.Modules)
    (j : ℤ) : ModuleCat.{u} k :=
  Stacks.Duality.derivedCohomologyOverField f ((DerivedCategory.singleFunctor X.Modules 0).obj G) j

/-- The cohomology of a module vanishes in negative degrees. -/
private theorem subsingleton_H_of_neg {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (G : X.Modules) {j : ℤ} (hj : j < 0) : Subsingleton (H f G j) := by
  letI : Linear k X.Modules := Scheme.Modules.linearOverBase f
  letI : Functor.Linear k (globalSectionsOver f) := globalSectionsOver_linear_linearOverBase f
  haveI := DerivedCategory.TStructure.t.isGE_shift
    ((DerivedCategory.singleFunctor X.Modules 0).obj G) 0 j (-j) (by omega)
  haveI : Subsingleton (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor X.Modules 0).obj (Stacks.Ample.unitModule X))
      ((DerivedCategory.singleFunctor X.Modules 0).obj G) j) :=
    ⟨fun a b => by
      rw [DerivedCategory.TStructure.t.zero a 0 (-j) (by omega),
        DerivedCategory.TStructure.t.zero b 0 (-j) (by omega)]⟩
  exact (Stacks.Duality.nonempty_derivedCohomologyOverFieldLinearEquivExtUnit f
    ((DerivedCategory.singleFunctor X.Modules 0).obj G) j).some.toEquiv.subsingleton

/-- A vanishing cohomology group in degree `m ≥ 0` has dimension zero. -/
private theorem finrank_cohomologyOverField_eq_zero_of_subsingleton {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (G : X.Modules) (m : ℕ)
    (h : Subsingleton (H f G m)) : Module.finrank k (cohomologyOverField k f G m) = 0 :=
  haveI : Subsingleton (cohomologyOverField k f G m) :=
    (Stacks.Duality.cohomologyOverFieldLinearEquivDerivedCohomologyOverField k f G m).toEquiv
      |>.subsingleton
  Module.finrank_zero_of_subsingleton

/-- The dual of an invertible module is invertible. -/
private theorem isInvertible_dualSheaf {X : Scheme.{u}} (N : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N] :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf N) :=
  Stacks.SheafOfModules.Invertible.isInvertible_dualSheaf X.presheaf _ N

/-- The dual of an invertible module on a scheme is coherent, provided the scheme is locally
noetherian. -/
private theorem isCoherent_dualSheaf {X : Scheme.{u}} [IsLocallyNoetherian X] (N : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N] :
    SheafOfModules.IsCoherent (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf N) := by
  haveI := isInvertible_dualSheaf N
  exact (Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_iff_isFinitePresentation _).2
    (Stacks.Chow.isFinitePresentation_of_isFiniteLocallyFree _
      (SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1))

/-- The dual of an invertible module is quasi-coherent. -/
private theorem isQuasicoherent_dualSheaf {X : Scheme.{u}} (N : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N] :
    SheafOfModules.IsQuasicoherent (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf N) := by
  haveI := isInvertible_dualSheaf N
  haveI := Stacks.Chow.isFinitePresentation_of_isFiniteLocallyFree _
    (SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
      (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf N) 1)
  infer_instance

section Picard

variable {X : Scheme.{u}}

/-- The Picard class of an invertible `𝒪_X`-module. -/
private abbrev pic (L : X.Modules) (h : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L) :
    Stacks.Picard.ofScheme X :=
  Stacks.SheafOfModules.picardClass X.presheaf X.ringCatSheaf.2 L h

private theorem pic_eq_iff (L L' : X.Modules)
    (h : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L)
    (h' : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L') :
    pic L h = pic L' h' ↔ Nonempty (L ≅ L') :=
  Stacks.SheafOfModules.picardClass_eq_iff X.presheaf X.ringCatSheaf.2 L L' h h'

/-- `[L^∨] = -[L]`. -/
private theorem pic_dualSheaf (L : X.Modules)
    [h : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    pic (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf L) (isInvertible_dualSheaf L) =
      -pic L h := by
  haveI := isInvertible_dualSheaf L
  obtain ⟨N, ⟨e⟩⟩ := (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit L).mp h
  let e' : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj L).obj
      (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf L) ≅
      _root_.SheafOfModules.unit _ :=
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj L).mapIso
      (Stacks.SheafOfModules.Invertible.tensorInverseIsoDualSheaf X.presheaf
        X.ringCatSheaf.2 L N e)).symm ≪≫ e
  have hLD : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj L).obj
        (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf L)) :=
    Stacks.SheafOfModules.isInvertible_tensorSheaf X.presheaf X.ringCatSheaf.2 _ _
  have hsum : pic L h + pic _ (isInvertible_dualSheaf L) = pic _ hLD :=
    Stacks.SheafOfModules.picardClass_tensorSheaf X.presheaf X.ringCatSheaf.2 L
      (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf L) h (isInvertible_dualSheaf L) hLD
  have hzero : pic _ hLD = 0 :=
    ((Stacks.SheafOfModules.picardClass_eq_iff X.presheaf X.ringCatSheaf.2 _ _ hLD _).2 ⟨e'⟩).trans
      (Stacks.SheafOfModules.picardClass_zero X.presheaf X.ringCatSheaf.2)
  exact eq_neg_of_add_eq_zero_right (hsum.trans hzero)

/-- **The dual commutes with pull-back of invertible modules.** If `L ≅ φ^* M` for an invertible
`M`, then `L^{-1} ≅ φ^* (M^{-1})`. -/
private theorem nonempty_dualSheaf_iso_pullback {Y : Scheme.{u}} (φ : X ⟶ Y) (L : X.Modules)
    (M : Y.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [hM : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M]
    (e : L ≅ (Scheme.Modules.pullback φ).obj M) :
    Nonempty (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf L ≅
      (Scheme.Modules.pullback φ).obj (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf M)) := by
  haveI := isInvertible_dualSheaf M
  haveI hφM := Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback φ M
  haveI hφD := Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback φ
    (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf M)
  refine (pic_eq_iff _ _ (isInvertible_dualSheaf L) hφD).1 ?_
  have h₁ : pic ((Scheme.Modules.pullback φ).obj
      (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf M)) hφD =
      Stacks.Picard.schemePullbackClass φ (pic _ (isInvertible_dualSheaf M)) :=
    (Stacks.Picard.pullbackClass_classOf φ.toLRSHom.toShHom
      (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf M) (isInvertible_dualSheaf M)).symm
  have h₂ : pic ((Scheme.Modules.pullback φ).obj M) hφM =
      Stacks.Picard.schemePullbackClass φ (pic M hM) :=
    (Stacks.Picard.pullbackClass_classOf φ.toLRSHom.toShHom M hM).symm
  rw [h₁, pic_dualSheaf, pic_dualSheaf, (pic_eq_iff _ _ _ hφM).2 ⟨e⟩, h₂]
  exact (map_neg (Stacks.Picard.pullbackClassHom φ.toLRSHom.toShHom) _).symm

end Picard

/-- A subfield of a field that is finitely generated over `ℚ` is countable. -/
private theorem countable_of_fg {k : Type u} [Field k] [CharZero k] {F : IntermediateField ℚ k}
    (hF : F.FG) : Countable F := by
  obtain ⟨S, rfl⟩ := hF
  have h := IntermediateField.lift_cardinalMk_adjoin_le ℚ (S : Set k)
  refine Cardinal.mk_le_aleph0_iff.1 (Cardinal.lift_le_aleph0.1 (h.trans ?_))
  exact max_le (max_le (Cardinal.lift_le_aleph0.2 Cardinal.mk_le_aleph0)
    (Cardinal.lift_le_aleph0.2 (Set.Finite.countable S.finite_toSet).le_aleph0)) le_rfl

/-- **Flat base change for `H^m(L^{-1})`.** Let `X' = X ×_F K` for a field extension `K / F`, with
`X` proper over `F`, and let `M` be invertible on `X`. If `N ≅ p^* M` on `X'`, then
`dim_K H^m(X', N^{-1}) = dim_F H^m(X, M^{-1})`. -/
private theorem finrank_cohomologyOverField_dualSheaf_baseChange (F K : Type u) [Field F]
    [Field K] [Algebra F K] {X' X : Scheme.{u}} (p : X' ⟶ X) (f' : X' ⟶ Spec (.of K))
    (f : X ⟶ Spec (.of F)) (h : IsPullback p f' f (Spec.map (CommRingCat.ofHom (algebraMap F K))))
    [IsProper f] (M : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    (N : X'.Modules) [SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2 N]
    (e : N ≅ (Scheme.Modules.pullback p).obj M) (m : ℕ) :
    Module.finrank K (cohomologyOverField K f'
        (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf N) m) =
      Module.finrank F (cohomologyOverField F f
        (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf M) m) := by
  haveI := isQuasicoherent_dualSheaf M
  obtain ⟨eD⟩ := nonempty_dualSheaf_iso_pullback p N M e
  rw [finrank_cohomologyOverField_eq_of_iso K f' eD m]
  exact finrank_cohomologyOverField_baseChange_field F K p f' f h _ m

/-- **Kodaira vanishing in characteristic zero, from the complex case.** -/
private theorem subsingleton_H_dualSheaf
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}}
    (f : X ⟶ Spec (.of k)) [hXv : MMP.Mori.IsProjectiveVariety k f]
    (hsm : MMP.Mori.IsSmoothScheme f) (n : ℕ) (hn : topologicalKrullDim X = n) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (hL : Stacks.Ample.IsAmple X L)
    (i : ℤ) (hi : i < n) :
    Subsingleton (H f (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf L) i) := by
  rcases lt_or_ge i 0 with hi0 | hi0
  · exact subsingleton_H_of_neg f _ hi0
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hi0
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hXv.isProjective
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  letI : X.Over (Spec (.of k)) := ⟨f⟩
  haveI : Smooth (X ↘ Spec (.of k)) := (MMP.Mori.isSmoothScheme_iff f).1 hsm
  haveI : IsProper (X ↘ Spec (.of k)) := ‹IsProper f›
  -- step 1: descent to a finitely generated field `F`
  obtain ⟨F, hF, XF, _, hsmF, hprojF, hgiF, LF, _, hLF, e, he, ⟨eL⟩⟩ :=
    MMP.Descent.exists_fg_intermediateField_isoBaseChange_of_isAmple k X hXv.isProjective L
      (MMP.Intersection.isAmple_of_stacksIsAmple k L hL)
  haveI : IsProper (XF ↘ Spec (.of F)) := isProper_of_isProjectiveMorphism _ hprojF
  -- step 2: an embedding `F → ℂ`
  haveI := countable_of_fg hF
  obtain ⟨σ⟩ := MMP.Resolution.Bridges.nonempty_ringHom_complex_and_countable_algebraicClosure.1 F
  letI : Algebra F ℂ := σ.toAlgebra
  -- step 3: the base change to `ℂ` is a smooth projective variety of dimension `n`
  have hC₀ := IsPullback.of_hasPullback (XF ↘ Spec (.of F))
    (Spec.map (CommRingCat.ofHom (algebraMap F ℂ)))
  have hX₀ : IsPullback (e.hom ≫ pullback.fst _ _) f (XF ↘ Spec (.of F))
      (Spec.map (CommRingCat.ofHom (algebraMap F k))) := by
    have h₁ : IsPullback e.hom f (pullback.snd _ _) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact he⟩
    have := h₁.paste_horiz (IsPullback.of_hasPullback (XF ↘ Spec (.of F))
      (Spec.map (CommRingCat.ofHom (algebraMap F k))))
    rwa [Category.id_comp] at this
  haveI : AlgebraicGeometry.IsIntegral (pullback (XF ↘ Spec (.of F))
      (Spec.map (CommRingCat.ofHom (algebraMap F ℂ)))) :=
    pullback_of_geometrically (GeometricallyIntegral.eq_geometrically ▸ hgiF) ℂ _
  haveI : Smooth (pullback.snd (XF ↘ Spec (.of F))
      (Spec.map (CommRingCat.ofHom (algebraMap F ℂ)))) :=
    MorphismProperty.of_isPullback (P := @Smooth) hC₀ hsmF
  haveI hXCv : MMP.Mori.IsProjectiveVariety ℂ (pullback.snd (XF ↘ Spec (.of F))
      (Spec.map (CommRingCat.ofHom (algebraMap F ℂ)))) :=
    { toIsIntegral := inferInstance, toIsSeparated := inferInstance,
      toLocallyOfFiniteType := inferInstance, toQuasiCompact := inferInstance,
      isProjective := hprojF.baseChange _ }
  have hnC : topologicalKrullDim ↥(pullback (C := Scheme.{0}) (XF ↘ Spec (.of F))
      (Spec.map (CommRingCat.ofHom (algebraMap F ℂ)))) = n := by
    rw [topologicalKrullDim_baseChange F ℂ _ _ _ hC₀, ← hn,
      topologicalKrullDim_baseChange F k _ f _ hX₀]
  -- the pulled-back polarization is ample
  haveI := Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback
    (pullback.fst (XF ↘ Spec (.of F)) (Spec.map (CommRingCat.ofHom (algebraMap F ℂ)))) LF
  have hLC : Stacks.Ample.IsAmple _ ((Scheme.Modules.pullback (pullback.fst (XF ↘ Spec (.of F))
      (Spec.map (CommRingCat.ofHom (algebraMap F ℂ))))).obj LF) := by
    haveI : IsAffineHom (pullback.fst (XF ↘ Spec (.of F))
        (Spec.map (CommRingCat.ofHom (algebraMap F ℂ)))) :=
      MorphismProperty.of_isPullback (P := @IsAffineHom) hC₀.flip inferInstance
    haveI : CompactSpace ↥(pullback (C := Scheme.{0}) (XF ↘ Spec (.of F))
        (Spec.map (CommRingCat.ofHom (algebraMap F ℂ)))) :=
      QuasiCompact.compactSpace_of_compactSpace (pullback.snd _ _)
    rw [Stacks.AmpleBridge.isAmple_iff_isAmple]
    exact Scheme.Modules.isAmple_pullback_of_isAffineHom _ LF
      ((Stacks.AmpleBridge.isAmple_iff_isAmple XF LF).1 hLF.stacksIsAmple)
  -- step 4: Kodaira vanishing over `ℂ`
  have hvan := MMP.Mori.subsingleton_derivedCohomologyOverField_dualSheaf_of_isAmple_complex
    (pullback.snd (XF ↘ Spec (.of F))
      (Spec.map (CommRingCat.ofHom (algebraMap F ℂ))))
    ((MMP.Mori.isSmoothScheme_iff _).2 inferInstance) n hnC _ hLC m
    (by exact_mod_cast hi)
  -- step 5: comparison of dimensions by flat base change
  have hk0 : Module.finrank k (cohomologyOverField k f
      (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf L) m) = 0 := by
    rw [finrank_cohomologyOverField_dualSheaf_baseChange F k _ f _ hX₀ LF L eL m,
      ← finrank_cohomologyOverField_dualSheaf_baseChange F ℂ _ _ _ hC₀ LF _ (Iso.refl _) m]
    exact finrank_cohomologyOverField_eq_zero_of_subsingleton _ _ m hvan
  haveI := isCoherent_dualSheaf L
  haveI := finiteDimensional_cohomologyOverField_of_isProper k f
    (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf L) m
  haveI := Module.finrank_zero_iff.mp hk0
  exact (Stacks.Duality.cohomologyOverFieldLinearEquivDerivedCohomologyOverField k f _
    m).toEquiv.symm.subsingleton

end MMP.FourfoldProofs.Km2cKodairaVanishingCharZeroProof

namespace MMP.Mori

/-- **Kodaira vanishing** (Kollár--Mori, Theorem 2.47) over an algebraically closed field of
characteristic zero. Let `X` be a smooth projective variety of dimension `n` over `k` and `L` an
ample line bundle on `X`. Then `H^i(X, L^{-1}) = 0` for every `i < n`. -/
@[mmp "thm_km2c_kodaira_vanishing_char_zero"]
public theorem subsingleton_derivedCohomologyOverField_dualSheaf_of_isAmple
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}}
    (f : X ⟶ Spec (.of k)) [IsProjectiveVariety k f] (hsm : IsSmoothScheme f)
    (n : ℕ) (hn : topologicalKrullDim X = n) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (hL : Stacks.Ample.IsAmple X L)
    (i : ℤ) (hi : i < n) :
    Subsingleton (Stacks.Duality.derivedCohomologyOverField f
      ((DerivedCategory.singleFunctor X.Modules 0).obj
        (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf L)) i) :=
  MMP.FourfoldProofs.Km2cKodairaVanishingCharZeroProof.subsingleton_H_dualSheaf f hsm n hn L hL i hi

end MMP.Mori

end

end
