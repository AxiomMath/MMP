module

public import MMP.AlgebraicGeometry.Resolution.Basic
public import MMP.AlgebraicGeometry.Resolution.Principalization
public import MMP.AlgebraicGeometry.Resolution.Blowup.VarietyProjective
public import MMP.AlgebraicGeometry.MMP.Abundance.Basic

/-!
# Blow-ups, restriction and push-forward of blow-up sequences

Three facts from Kollár's treatment of principalization and embedded resolution.

* Let `X` be a smooth variety over a field `k` and `0 ≠ I ⊆ 𝒪_X` an ideal sheaf. If
  `π : B_I X → X` is the blow-up of `I` and `h : X' → B_I X` is a resolution of `B_I X`, then
  `π ∘ h` is a principalization of `I`: `X'` is a smooth variety, `π ∘ h` is birational as a
  composite of birational morphisms, and `(π ∘ h)^* I = h^*(π^* I)` is locally principal since
  `π^* I` is invertible on `B_I X`.
* Restriction of blow-up sequences is transitive: for closed subschemes `S ⊆ Y ⊆ X` and a
  blow-up sequence `𝐁` starting with `X`, `(𝐁|_Y)|_S` is the pull-back of `𝐁` along `S ↪ X`,
  compatibly with the morphisms `S_r → Y_r → X_r`. This is functoriality of pull-back,
  `g^*(f^*𝐁) = (f ∘ g)^*𝐁`, which holds because canonical lifts compose, by the uniqueness in the
  universal property of the blow-up.
* The induced blow-up sequence commutes with push-forward: for a closed embedding `j : S ↪ A` of
  schemes of finite type over `k`, a closed subscheme `X ⊆ S` which is a disjoint union of
  varieties and a push-forward `𝐁^A = j_*𝐁(S)`, `𝓑𝓡_{𝐁^A}(X ⊆ A) = 𝓑𝓡_{𝐁(S)}(X ⊆ S)`. Entry
  indices are preserved, since the support of `j_* Z` is `j(Supp Z)`, and each step of the
  recursion agrees, since the blow-up lift through `j` factors through the canonical lift of `j`.

## Main results

* `MMP.Resolution.isPrincipalization_comp_blowUpToBase`: if `h` is a resolution of
  `Stacks.Blowup.blowUp I`, then `h ≫ Stacks.Blowup.blowUpToBase I` is a principalization of `I`.
* `MMP.Resolution.ClosedBlowupSequence.restrict_restrict`: `(𝐁|_Y)|_S = 𝐁|_S`, compatibly with
  the morphisms `S_r → Y_r → X_r` and `S_r → X_r`.
* `MMP.Resolution.Kollar.embeddedResolutionSequence_comp_eq_of_isPushforward`:
  `𝓑𝓡_{𝐁^A}(X ⊆ A) = 𝓑𝓡_{𝐁(S)}(X ⊆ S)` whenever `𝐁^A` is a push-forward of `𝐁(S)` along `j`.

## Implementation notes

Ideal sheaves are `Scheme.IdealSheafData`; on a noetherian scheme they are coherent, so coherence
is not a separate hypothesis. The variety `B_I X` is over `k` through `π ≫ s_X`, which is how
`MMP.Resolution.IsResolutionOfVariety` is applied to `h`.

A closed subscheme `S` of `Y` is a `Scheme.IdealSheafData` on `Y.subscheme`, and `𝐁|_S` is the
pull-back `ClosedBlowupSequence.pullback` of `𝐁` along `S.subschemeι ≫ Y.subschemeι`. The two
sequences start with the same scheme, so their equality is equality of centres; the morphisms to
`X_r` are then compared through `eqToHom`.

The push-forward `j_*𝐁(S)` is a property of a pair of sequences
(`MMP.Resolution.ClosedBlowupSequence.IsPushforward`), not a construction, so the last statement
quantifies over every push-forward `𝐁^A` of `𝐁(S)` along `j`. The embedding `X ⊆ A` is `i ≫ j`.

## References

* [J. Kollár, *Lectures on resolution of singularities*][kollar2007], §3.3, 3.30.2, the proof of
  3.36, and p. 146.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace MMP.Resolution

section Principalization

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Flips
open MMP.Mori (IsBirationalMorphism isBirationalMorphism_of_isIso)

/-- A morphism of integral schemes, locally of finite type and birational in the sense of
`AlgebraicGeometry.IsBirational`, is a birational morphism. -/
private theorem isBirationalMorphism_of_isBirational {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : IsBirational f) :
    IsBirationalMorphism f := by
  haveI : Finite (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]
    exact Set.finite_singleton _
  haveI : Finite (irreducibleComponents Y) := by
    rw [irreducibleComponents_eq_singleton]
    exact Set.finite_singleton _
  obtain ⟨U, V, hUV, hU, hV, hiso⟩ :=
    exists_dense_opens_isIso_resLE_of_isBirational f hf (Or.inl ⟨inferInstance, inferInstance⟩)
  exact isBirationalMorphism_of_isIso_resLE f U V hU.nonempty hV.nonempty hUV hiso

/-- A dominant morphism which is an open immersion on a dense open is birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsDominant f] (U : X.Opens) (hU : Dense (U : Set X)) [IsOpenImmersion (U.ι ≫ f)] :
    IsBirationalMorphism f := by
  have hd : Dense ((U.ι ≫ f).opensRange : Set Y) := by
    rw [Scheme.Hom.coe_opensRange, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι]
    exact f.denseRange.dense_image f.continuous hU
  let e : X.PartialIso Y :=
    { source := U
      dense_source := hU
      target := (U.ι ≫ f).opensRange
      dense_target := hd
      iso := (U.ι ≫ f).isoOpensRange }
  refine ⟨e, ?_⟩
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨U, hU, le_rfl, le_top, ?_⟩
  simp only [Scheme.PartialMap.restrict, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom, e, Scheme.Hom.isoOpensRange_hom_ι]
  exact (Scheme.homOfLE_ι_assoc _ _ _).trans
    (by rw [Scheme.topIso_hom]; exact (Scheme.homOfLE_ι_assoc _ _ _).symm)

/-- A birational morphism is an open immersion on a dense open. -/
private theorem exists_isOpenImmersion_of_isBirationalMorphism {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : IsBirationalMorphism f) :
    ∃ U : X.Opens, Dense (U : Set X) ∧ IsOpenImmersion (U.ι ≫ f) := by
  obtain ⟨e, he⟩ := hf
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff] at he
  obtain ⟨W, hW, hWe, hWf, h⟩ := he
  simp only [Scheme.PartialMap.restrict_hom] at h
  have : IsOpenImmersion e.toPartialMap.hom := by
    change IsOpenImmersion (e.iso.hom ≫ e.target.ι)
    infer_instance
  refine ⟨W, hW, ?_⟩
  have : W.ι ≫ f = X.homOfLE hWf ≫ f.toPartialMap.hom := by
    change W.ι ≫ f = (X.homOfLE (le_top : W ≤ ⊤) ≫ X.topIso.hom) ≫ f
    simp only [Scheme.topIso_hom, Scheme.homOfLE_ι]
  rw [this, ← h]
  infer_instance

/-- A composite of birational morphisms out of an irreducible scheme is birational. -/
private theorem isBirationalMorphism_comp {X Y Z : Scheme.{u}} [IrreducibleSpace X]
    {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsBirationalMorphism f) (hg : IsBirationalMorphism g) :
    IsBirationalMorphism (f ≫ g) := by
  haveI := hf.isDominant
  haveI := hg.isDominant
  obtain ⟨U₁, hU₁, h₁⟩ := exists_isOpenImmersion_of_isBirationalMorphism hf
  obtain ⟨U₂, hU₂, h₂⟩ := exists_isOpenImmersion_of_isBirationalMorphism hg
  let U : X.Opens := U₁ ⊓ f ⁻¹ᵁ U₂
  have hne : (U : Set X).Nonempty := by
    obtain ⟨x₀⟩ := (IrreducibleSpace.isIrreducible_univ X).nonempty
    haveI : Nonempty Y := ⟨f x₀⟩
    have hd : Dense (f '' U₁) := f.denseRange.dense_image f.continuous hU₁
    obtain ⟨y, hy₂, x, hx₁, rfl⟩ := (hU₂.inter_of_isOpen_left hd U₂.2).nonempty
    exact ⟨x, hx₁, hy₂⟩
  have hle : U ≤ f ⁻¹ᵁ U₂ := inf_le_right
  have : IsOpenImmersion (f.resLE U₂ U hle ≫ U₂.ι) := by
    rw [Scheme.Hom.resLE_comp_ι, ← Scheme.homOfLE_ι X (inf_le_left : U ≤ U₁), Category.assoc]
    infer_instance
  have := IsOpenImmersion.of_comp (f.resLE U₂ U hle) U₂.ι
  haveI : IsOpenImmersion (U.ι ≫ f ≫ g) := by
    rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι f hle, Category.assoc]
    infer_instance
  exact isBirationalMorphism_of_isOpenImmersion (f ≫ g) U (U.2.dense hne)

/-- If `X` is a smooth variety over `k`, `I ≠ ⊥` an ideal sheaf on `X`, and `h : X' ⟶ B_I X` a
resolution of the blow-up `B_I X` of `I`, then `h ≫ π` (with `π : B_I X ⟶ X` the blow-up
morphism) is a principalization of `I`. -/
@[mmp "lem_kr3b_resolution_implies_principalization"]
public theorem isPrincipalization_comp_blowUpToBase {k : Type u} [Field k] {X X' : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : IsVariety k sX) (hXs : MMP.Mori.IsSmoothScheme sX)
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (h : X' ⟶ Stacks.Blowup.blowUp I)
    (hh : IsResolutionOfVariety (Stacks.Blowup.blowUpToBase I ≫ sX) h) :
    IsPrincipalization sX I (h ≫ Stacks.Blowup.blowUpToBase I) := by
  have hV : IsVariety k (h ≫ Stacks.Blowup.blowUpToBase I ≫ sX) := hh.isVariety_source
  refine ⟨by simpa only [Category.assoc] using hV,
    by simpa only [Category.assoc] using hh.isSmoothScheme, ?_, ?_⟩
  · obtain ⟨hB, hproj, hbir⟩ :=
      ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational sX I hI
    haveI := hX.toIsIntegral
    haveI := hB.toIsIntegral
    haveI := hV.toIsIntegral
    haveI := hproj.isProper
    rw [(Iso.eq_inv_comp _).2 (blowUpIso_hom_blowUpToBase I), ← Category.assoc]
    exact isBirationalMorphism_comp
      (isBirationalMorphism_comp hh.isBirationalMorphism (isBirationalMorphism_of_isIso _))
      (isBirationalMorphism_of_isBirational _ hbir)
  · rw [Scheme.IdealSheafData.comap_comp]
    exact Stacks.Divisors.isLocallyPrincipal_comap _ _
      (Stacks.Blowup.isLocallyPrincipal_exceptionalIdeal I)

end Principalization

namespace ClosedBlowupSequence

/-- Transport of the blow-up of `X` with centre `A` along an equality `A = A'` lies over `X`. -/
private lemma eqToHom_comp_blowUpToBase {X : Scheme.{u}} {A A' : X.IdealSheafData}
    (e : A = A') : eqToHom (congrArg blowUp e) ≫ blowUpToBase A' = blowUpToBase A := by
  subst e
  simp

/-- The canonical lifts compose: `g̃ ∘ f̃` is the canonical lift of `f ∘ g`, up to the
identification `g⁻¹(f⁻¹Z) = (f ∘ g)⁻¹Z`. -/
private lemma canonicalLift_comp_canonicalLift {X Y W : Scheme.{u}} (f : Y ⟶ X) (g : W ⟶ Y)
    (Z : X.IdealSheafData) :
    canonicalLift g (Z.comap f) ≫ canonicalLift f Z =
      eqToHom (congrArg blowUp (Scheme.IdealSheafData.comap_comp Z g f).symm) ≫
        canonicalLift (g ≫ f) Z := by
  have hc : Stacks.Blowup.IsCartierOver Z
      (Over.mk (blowUpToBase ((Z.comap f).comap g) ≫ g ≫ f)) := by
    change Stacks.Divisors.IsEffectiveCartierDivisor
      (Z.comap (blowUpToBase ((Z.comap f).comap g) ≫ g ≫ f))
    rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp]
    exact Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal _
  refine (blowUpLift_unique Z _ hc _ ?_).trans (blowUpLift_unique Z _ hc _ ?_).symm
  · rw [Category.assoc, canonicalLift_comp_blowUpToBase, ← Category.assoc,
      canonicalLift_comp_blowUpToBase, Category.assoc]
  · rw [Category.assoc, canonicalLift_comp_blowUpToBase, ← Category.assoc,
      eqToHom_comp_blowUpToBase (Scheme.IdealSheafData.comap_comp Z g f).symm]

/-- Two pulled-back sequences with equal first centres and compatible lifts agree. -/
private lemma cons_pullback_congr {W T : Scheme.{u}} {A A' : W.IdealSheafData} (e : A = A')
    (B : ClosedBlowupSequence T) (φ : blowUp A ⟶ T) (φ' : blowUp A' ⟶ T)
    (hφ : φ = eqToHom (congrArg blowUp e) ≫ φ') :
    ∃ h : cons A (B.pullback φ) = cons A' (B.pullback φ'),
      B.pullbackHom φ = eqToHom (congrArg target h) ≫ B.pullbackHom φ' := by
  subst e
  simp only [eqToHom_refl, Category.id_comp] at hφ
  subst hφ
  exact ⟨rfl, (Category.id_comp _).symm⟩

/-- Pull-back of blow-up sequences is functorial: `g^*(f^*𝐁) = (f ∘ g)^*𝐁`, and
`f_r ∘ g_r = (f ∘ g)_r`. -/
private lemma pullback_pullback {X : Scheme.{u}} (B : ClosedBlowupSequence X) :
    ∀ {Y W : Scheme.{u}} (f : Y ⟶ X) (g : W ⟶ Y),
    ∃ h : (B.pullback f).pullback g = B.pullback (g ≫ f),
      (B.pullback f).pullbackHom g ≫ B.pullbackHom f =
        eqToHom (congrArg target h) ≫ B.pullbackHom (g ≫ f) := by
  induction B with
  | nil X =>
    intro Y W f g
    exact ⟨rfl, (Category.id_comp _).symm⟩
  | cons Z B ih =>
    intro Y W f g
    obtain ⟨h₁, hh₁⟩ := ih (canonicalLift f Z) (canonicalLift g (Z.comap f))
    obtain ⟨h₂, hh₂⟩ := cons_pullback_congr (Scheme.IdealSheafData.comap_comp Z g f).symm B _ _
      (canonicalLift_comp_canonicalLift f g Z)
    refine ⟨(congrArg (cons _) h₁).trans h₂, ?_⟩
    change (B.pullback (canonicalLift f Z)).pullbackHom (canonicalLift g (Z.comap f)) ≫
        B.pullbackHom (canonicalLift f Z) = _ ≫ B.pullbackHom (canonicalLift (g ≫ f) Z)
    rw [hh₁, hh₂]
    exact eqToHom_trans_assoc _ _ _

/-- Restriction of blow-up sequences is transitive: for closed subschemes `S ⊆ Y ⊆ X`,
`(𝐁|_Y)|_S` is the pull-back of `𝐁` along `S ↪ Y ↪ X`, and the composite
`S_r → Y_r → X_r` of the restriction morphisms is the morphism `S_r → X_r` of that pull-back. -/
@[mmp "lem_kr3b_restriction_transitive"]
public theorem restrict_restrict {X : Scheme.{u}} [IsLocallyNoetherian X]
    (B : ClosedBlowupSequence X) (Y : X.IdealSheafData) (S : Y.subscheme.IdealSheafData) :
    ∃ h : (B.restrict Y).restrict S = B.pullback (S.subschemeι ≫ Y.subschemeι),
      (B.restrict Y).restrictHom S ≫ B.restrictHom Y =
        eqToHom (congrArg target h) ≫ B.pullbackHom (S.subschemeι ≫ Y.subschemeι) :=
  pullback_pullback B Y.subschemeι S.subschemeι

end ClosedBlowupSequence

namespace Kollar

/-- The canonical lift of a closed immersion is a closed immersion. -/
private theorem isClosedImmersion_canonicalLift {Y X : Scheme.{u}} (f : Y ⟶ X)
    [IsClosedImmersion f] (Z : X.IdealSheafData) : IsClosedImmersion (canonicalLift f Z) := by
  obtain ⟨g, hg, -, hfst⟩ := exists_isClosedImmersion_canonicalLift_factor f Z
  rw [← hfst]
  infer_instance

/-- The support of the push-forward of an ideal sheaf along a closed immersion is the image of
its support. -/
private theorem coe_support_map_of_isClosedImmersion {S A : Scheme.{u}} (j : S ⟶ A)
    [IsClosedImmersion j] (W : S.IdealSheafData) :
    ((W.map j).support : Set A) = j.base '' W.support := by
  rw [Scheme.IdealSheafData.support_map, TopologicalSpace.Closeds.coe_closure,
    (j.isClosedEmbedding.isClosedMap _ W.support.isClosed).closure_eq]

/-- Entry indices of sets are preserved by push-forward along a closed immersion. -/
private theorem entryIndexOfSet_eq_of_isPushforward {S A : Scheme.{u}}
    (BS : ClosedBlowupSequence S) :
    ∀ (BA : ClosedBlowupSequence A) (j : S ⟶ A) [IsClosedImmersion j],
      ClosedBlowupSequence.IsPushforward j BS BA → ∀ T : Set A,
      BA.entryIndexOfSet T = BS.entryIndexOfSet (j.base ⁻¹' T) := by
  induction BS generalizing A with
  | nil S =>
    intro BA j _ hP T
    cases BA with
    | nil => rfl
    | cons => exact hP.elim
  | cons ZS BS ih =>
    intro BA j _ hP T
    cases BA with
    | nil => exact hP.elim
    | cons ZX BX =>
      obtain ⟨h0, h1, hP'⟩ := hP
      subst h0
      have := isClosedImmersion_canonicalLift j ZX
      simp only [eqToHom_refl, Category.id_comp] at hP'
      have hsupp : ((ZX.support : Set A) ∩ T).Nonempty ↔
          (((ZX.comap j).support : Set _) ∩ j.base ⁻¹' T).Nonempty := by
        rw [h1, coe_support_map_of_isClosedImmersion, Set.image_inter_nonempty_iff, ← h1]
      simp only [ClosedBlowupSequence.entryIndexOfSet]
      have hpre : (canonicalLift j ZX).base ⁻¹' ((blowUpToBase ZX).base ⁻¹' T) =
          (blowUpToBase (ZX.comap j)).base ⁻¹' (j.base ⁻¹' T) := by
        ext y
        simp only [Set.mem_preimage, ← Scheme.Hom.comp_apply, canonicalLift_comp_blowUpToBase]
      rw [ih BX (canonicalLift j ZX) hP', hpre]
      by_cases hc : ((ZX.support : Set A) ∩ T).Nonempty
      · rw [if_pos hc, if_pos (hsupp.1 hc)]
      · rw [if_neg hc, if_neg (mt hsupp.2 hc)]

/-- Entry indices of points are preserved by push-forward along a closed immersion. -/
private theorem entryIndex_eq_of_isPushforward {S A : Scheme.{u}} (BS : ClosedBlowupSequence S)
    (BA : ClosedBlowupSequence A) (j : S ⟶ A) [IsClosedImmersion j]
    (hP : ClosedBlowupSequence.IsPushforward j BS BA) (x : S) :
    BA.entryIndex (j.base x) = BS.entryIndex x := by
  rw [ClosedBlowupSequence.entryIndex, ClosedBlowupSequence.entryIndex,
    entryIndexOfSet_eq_of_isPushforward BS BA j hP, ← Set.image_singleton,
    Set.preimage_image_eq _ j.isClosedEmbedding.injective]

open Classical ClosedBlowupSequence in
/-- The step of `embeddedAux` on `cons Z C`, with its centre `W` named. -/
private theorem embeddedAux_cons_eq {X : Scheme.{u}} (act : ℕ → X.Opens) {A : Scheme.{u}}
    (Z : A.IdealSheafData) (C : ClosedBlowupSequence (blowUp Z)) (n : ℕ) (Y : Scheme.{u})
    (p : Y ⟶ X) (U : Y.Opens) (h : U.toScheme ⟶ A) (W : Y.IdealSheafData)
    (hW : (Z.comap h).map U.ι = W) :
    embeddedAux act (.cons Z C) n Y p U h =
      if hc : Stacks.Blowup.IsCartierOver Z (Over.mk ((blowUpToBase W).resLE U
          (blowUpToBase W ⁻¹ᵁ U ⊓ (blowUpToBase W ≫ p) ⁻¹ᵁ act (n + 1)) inf_le_left ≫ h)) then
        cons W (embeddedAux act C (n + 1) _ (blowUpToBase W ≫ p)
          (blowUpToBase W ⁻¹ᵁ U ⊓ (blowUpToBase W ≫ p) ⁻¹ᵁ act (n + 1))
          (blowUpLift Z ((blowUpToBase W).resLE U
            (blowUpToBase W ⁻¹ᵁ U ⊓ (blowUpToBase W ≫ p) ⁻¹ᵁ act (n + 1)) inf_le_left ≫ h) hc))
      else cons W (nil _) := by
  subst hW
  rw [embeddedAux.eq_2]

/-- The recursion `embeddedAux` run with a push-forward `𝐁^A` of `𝐁(S)` along `j`, on the
composite `h ≫ j`, agrees with the recursion run with `𝐁(S)` on `h`. -/
private theorem embeddedAux_comp_eq_of_isPushforward {X : Scheme.{u}} (act : ℕ → X.Opens)
    {S : Scheme.{u}} (BS : ClosedBlowupSequence S) :
    ∀ {A : Scheme.{u}} (BA : ClosedBlowupSequence A) (j : S ⟶ A),
      ClosedBlowupSequence.IsPushforward j BS BA → ∀ (n : ℕ) (Y : Scheme.{u}) (p : Y ⟶ X)
      (U : Y.Opens) (h : U.toScheme ⟶ S),
      ClosedBlowupSequence.embeddedAux act BA n Y p U (h ≫ j) =
        ClosedBlowupSequence.embeddedAux act BS n Y p U h := by
  induction BS with
  | nil S =>
    intro A BA j hP n Y p U h
    cases BA with
    | nil => rfl
    | cons => exact hP.elim
  | cons ZS BS ih =>
    intro A BA j hP n Y p U h
    cases BA with
    | nil => exact hP.elim
    | cons ZX BX =>
      obtain ⟨h0, -, hP'⟩ := hP
      subst h0
      simp only [eqToHom_refl, Category.id_comp] at hP'
      rw [embeddedAux_cons_eq act ZX BX n Y p U (h ≫ j) (((ZX.comap j).comap h).map U.ι)
          (by rw [Scheme.IdealSheafData.comap_comp]),
        embeddedAux_cons_eq act (ZX.comap j) BS n Y p U h _ rfl]
      set W := ((ZX.comap j).comap h).map U.ι
      set g := (blowUpToBase W).resLE U
        (blowUpToBase W ⁻¹ᵁ U ⊓ (blowUpToBase W ≫ p) ⁻¹ᵁ act (n + 1)) inf_le_left
      have hiff : Stacks.Blowup.IsCartierOver ZX (Over.mk (g ≫ h ≫ j)) ↔
          Stacks.Blowup.IsCartierOver (ZX.comap j) (Over.mk (g ≫ h)) := by
        change Stacks.Divisors.IsEffectiveCartierDivisor (ZX.comap (g ≫ h ≫ j)) ↔
          Stacks.Divisors.IsEffectiveCartierDivisor ((ZX.comap j).comap (g ≫ h))
        rw [← Category.assoc, Scheme.IdealSheafData.comap_comp]
      by_cases hc : Stacks.Blowup.IsCartierOver (ZX.comap j) (Over.mk (g ≫ h))
      · rw [dif_pos (hiff.2 hc), dif_pos hc]
        have hlift : blowUpLift ZX (g ≫ h ≫ j) (hiff.2 hc) =
            blowUpLift (ZX.comap j) (g ≫ h) hc ≫ canonicalLift j ZX := by
          symm
          apply blowUpLift_unique
          rw [Category.assoc, canonicalLift_comp_blowUpToBase, ← Category.assoc, blowUpLift_comp,
            Category.assoc]
        rw [hlift, ih BX _ hP']
      · rw [dif_neg (mt hiff.1 hc), dif_neg hc]

/-- **The induced sequence commutes with push-forward** (Kollár p. 146): for a closed embedding
`j : S ⟶ A` of schemes of finite type over a field, a closed subscheme `i : X ⟶ S` which is a
disjoint union of varieties, a blow-up sequence `BS` of `S` and a push-forward `BA` of `BS` along
`j`, the blow-up sequences of `X` induced by `BA` (for `X ⊆ A`) and by `BS` (for `X ⊆ S`) agree. -/
@[mmp "lem_kr3f_br_pushforward"]
public theorem embeddedResolutionSequence_comp_eq_of_isPushforward {k : Type u} [Field k]
    {X S A : Scheme.{u}} (sA : A ⟶ Spec (.of k)) [LocallyOfFiniteType sA] [QuasiCompact sA]
    (j : S ⟶ A) [IsClosedImmersion j] (i : X ⟶ S) [IsClosedImmersion i]
    (hX : IsDisjointUnionOfVarieties (i ≫ j ≫ sA))
    (BS : ClosedBlowupSequence S) (BA : ClosedBlowupSequence A)
    (hP : ClosedBlowupSequence.IsPushforward j BS BA) :
    embeddedResolutionSequence BA (i ≫ j) = embeddedResolutionSequence BS i := by
  have hentry (x : X) := entryIndex_eq_of_isPushforward BS BA j hP (i.base x)
  have hcomp : componentEntryIndex BA (i ≫ j) = componentEntryIndex BS i := by
    funext x
    simp only [componentEntryIndex, Scheme.Hom.comp_apply, hentry]
  have hlen : embeddedResolutionLength BA (i ≫ j) = embeddedResolutionLength BS i := by
    simp only [embeddedResolutionLength, Scheme.Hom.comp_apply, hentry]
  have hact : activeLocus BA (i ≫ j) = activeLocus BS i := by
    funext n
    rw [activeLocus, activeLocus, hcomp]
  rw [embeddedResolutionSequence, embeddedResolutionSequence, hact, hlen, ← Category.assoc,
    embeddedAux_comp_eq_of_isPushforward _ BS BA j hP]

end Kollar

end MMP.Resolution
