module
public import MMP.AlgebraicGeometry.Resolution.StrongResolutionCharZero

/-!
# Varieties in characteristic zero are dominated by opens of smooth projective varieties

Let `k` be a field of characteristic zero and `X` a variety over `k`. Then there are a smooth
projective variety `T` over `k`, a nonempty open `V ⊆ T`, and a `k`-morphism `τ : V ⟶ X` that is
proper, surjective and birational. No properness of `X` is assumed: one takes a Chow modification
of `X` that is quasi-projective, resolves its singularities, and then resolves a projective
closure of the result while keeping the smooth open part fixed.

## Main results

* `MMP.Mori.exists_smooth_projective_open_proper_birational`

## Implementation notes

Both resolutions are strong resolutions, `MMP.Resolution.exists_isStrongResolution`. A strong
resolution is an isomorphism over the whole smooth locus, so it is one over any smooth open, and
no resolution with simple normal crossing complement is needed. Quasi-projectivity is carried
through Stacks Tags 0B43 and 087S: the strong resolution of a quasi-projective variety is
projective over it, hence quasi-projective over `k`, hence immersed in some `ℙᴺ_k`.

## References

* [KM98] J. Kollár, S. Mori, *Birational geometry of algebraic varieties*.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Mori

/-- A scheme of finite type over a Noetherian scheme is Noetherian. -/
private theorem isNoetherian_of_locallyOfFiniteType {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hY : AlgebraicGeometry.IsNoetherian Y] [LocallyOfFiniteType f] [QuasiCompact f] :
    AlgebraicGeometry.IsNoetherian X where
  toIsLocallyNoetherian :=
    @LocallyOfFiniteType.isLocallyNoetherian _ _ f _ hY.toIsLocallyNoetherian
  toCompactSpace := @QuasiCompact.compactSpace_of_compactSpace _ _ f _ hY.toCompactSpace

/-- Strong resolution of a quasi-projective variety in characteristic zero: it is smooth over `k`,
immersed in a projective space over `k`, projective over the variety, and an isomorphism over
the smooth locus. -/
private theorem exists_smooth_isHQuasiProjective_resolution {k : Type u} [Field k] [CharZero k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [hY : MMP.Mori.IsVariety k sY]
    (hYq : IsQuasiProjective sY) :
    ∃ (T : Scheme.{u}) (g : T ⟶ Y), MMP.Mori.IsVariety k (g ≫ sY) ∧ Smooth (g ≫ sY) ∧
      IsHQuasiProjective (g ≫ sY) ∧ IsProper g ∧ IsBirationalMorphism g ∧
      IsIso (g ∣_ MMP.Mori.smoothLocus sY) := by
  obtain ⟨T, g, hTv, hgp, hgb, hTs, hiso, -⟩ := MMP.Resolution.exists_isStrongResolution sY hY
  have : LocallyOfFinitePresentation (g ≫ sY) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 hTv.toLocallyOfFiniteType
  obtain ⟨M, _, hM⟩ := Stacks.HProjective.exists_isAmple_of_isAffine (Spec (.of k))
  exact ⟨T, g, hTv, (MMP.Mori.isSmoothScheme_iff _).1 hTs,
    isHQuasiProjective_of_isQuasiProjective (g ≫ sY) M hM
      (IsQuasiProjective.comp g sY hgp.isQuasiProjective hYq), hgp.isProper, hgb, hiso⟩

/-- Strong resolution of a quasi-projective variety in characteristic zero: a variety `W`
immersed in a projective space over `k` receives a proper surjective birational `k`-morphism from
a smooth variety `V` which is again immersed in a projective space over `k`. -/
private theorem exists_smooth_immersed_resolution {k : Type u} [Field k] [CharZero k] {n : ℕ}
    {W : Scheme.{u}} (sW : W ⟶ Spec (.of k)) [hW : MMP.Mori.IsVariety k sW]
    (i : W ⟶ ProjectiveSpace n (Spec (.of k))) (hi : IsImmersion i)
    (hiW : i ≫ (ProjectiveSpace n (Spec (.of k)) ↘ Spec (.of k)) = sW) :
    ∃ (N : ℕ) (V : Scheme.{u}) (sV : V ⟶ Spec (.of k)) (_ : MMP.Mori.IsVariety k sV)
      (_ : Smooth sV) (j : V ⟶ ProjectiveSpace N (Spec (.of k))) (g : V ⟶ W),
      IsImmersion j ∧ j ≫ (ProjectiveSpace N (Spec (.of k)) ↘ Spec (.of k)) = sV ∧
      IsProper g ∧ Surjective g ∧ IsBirationalMorphism g ∧ g ≫ sW = sV := by
  have := hW.toLocallyOfFiniteType
  have := hW.toQuasiCompact
  have := isNoetherian_of_locallyOfFiniteType sW
  obtain ⟨V, g, hVv, hVs, ⟨N, j, hj, -, hjV⟩, hgp, hgb, -⟩ :=
    exists_smooth_isHQuasiProjective_resolution sW
      (isQuasiProjective_of_isHQuasiProjective sW
        ⟨n, i, hi, quasiCompact_of_noetherianSpace_source _, hiW⟩)
  have := hgb.isDominant
  exact ⟨N, V, g ≫ sW, hVv, hVs, j, g, hj, hjV, hgp, inferInstance, hgb, rfl⟩

/-- Resolution of a projective variety in characteristic zero which is an isomorphism over a
given smooth open subscheme. -/
private theorem exists_smooth_projective_isIso_morphismRestrict {k : Type u} [Field k]
    [CharZero k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sY]
    (O : Y.Opens) [Smooth (O.ι ≫ sY)] :
    ∃ (T : Scheme.{u}) (sT : T ⟶ Spec (.of k)) (_ : MMP.Mori.IsProjectiveVariety k sT)
      (_ : Smooth sT) (f : T ⟶ Y), f ≫ sY = sT ∧ IsIso (f ∣_ O) := by
  obtain ⟨hYv, hYp⟩ := (MMP.Mori.isProjectiveVariety_iff k sY).1 ‹_›
  obtain ⟨T, g, hTv, hTs, hTq, hgp, -, hiso⟩ := exists_smooth_isHQuasiProjective_resolution sY
    (isQuasiProjective_of_isHQuasiProjective sY hYp.isHQuasiProjective)
  have := isProper_of_isProjectiveMorphism sY hYp
  exact ⟨T, g ≫ sY, (MMP.Mori.isProjectiveVariety_iff k _).2
    ⟨hTv, isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.2 ⟨hTq, inferInstance⟩⟩, hTs,
    g, rfl, MMP.Resolution.Kollar.isIso_morphismRestrict_of_le g (MMP.Mori.le_smoothLocus sY ‹_›)⟩

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
  have he' : IsOpenImmersion e.toPartialMap.hom := by
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
  have hres : IsOpenImmersion (f.resLE U₂ U hle) := by
    have : f.resLE U₂ U hle ≫ U₂.ι = X.homOfLE (inf_le_left : U ≤ U₁) ≫ (U₁.ι ≫ f) := by
      rw [Scheme.Hom.resLE_comp_ι, ← Category.assoc, Scheme.homOfLE_ι]
    have : IsOpenImmersion (f.resLE U₂ U hle ≫ U₂.ι) := by rw [this]; infer_instance
    exact IsOpenImmersion.of_comp _ U₂.ι
  haveI : IsOpenImmersion (U.ι ≫ f ≫ g) := by
    rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι f hle, Category.assoc]
    infer_instance
  exact isBirationalMorphism_of_isOpenImmersion (f ≫ g) U (U.2.dense hne)

/-- Chow's lemma in variety form: a `k`-variety `X` receives a proper surjective birational
`k`-morphism from a variety immersed in a projective space over `k`. -/
private theorem exists_immersed_chow_model {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [MMP.Mori.IsVariety k sX] :
    ∃ (n : ℕ) (W : Scheme.{u}) (sW : W ⟶ Spec (.of k)) (_ : MMP.Mori.IsVariety k sW)
      (i : W ⟶ ProjectiveSpace n (Spec (.of k))) (π : W ⟶ X),
      IsImmersion i ∧ i ≫ (ProjectiveSpace n (Spec (.of k)) ↘ Spec (.of k)) = sW ∧
      IsProper π ∧ Surjective π ∧ IsBirationalMorphism π ∧ π ≫ sX = sW := by
  have hXv : AlgebraicGeometry.IsVariety k sX := ‹_›
  have := hXv.toIsSeparated
  have := hXv.toLocallyOfFiniteType
  have := hXv.toQuasiCompact
  have := hXv.toIsIntegral
  have := isNoetherian_of_locallyOfFiniteType sX
  obtain ⟨n, X', π, i, U, hπ, hsurj, hi, hcomm, hdense, hiso⟩ := hasDenseChowModification sX
  have := isNoetherian_of_locallyOfFiniteType (π ≫ sX)
  have hUne : Nonempty U := hdense.nonempty.to_subtype
  have hVne : Nonempty (π ⁻¹ᵁ U) := ⟨(inv (π ∣_ U)).base hUne.some⟩
  have : IsIntegral (π ⁻¹ᵁ U) := isIntegral_of_isOpenImmersion (π ∣_ U)
  have : NoetherianSpace (π ⁻¹ᵁ U).toScheme := NoetherianSpace.set _
  have : QuasiCompact (π ⁻¹ᵁ U).ι := quasiCompact_of_noetherianSpace_source _
  have hi1 : IsIso ((π ⁻¹ᵁ U).ι.imageι ∣_ (π ⁻¹ᵁ U)) :=
    Stacks.SchemeTheoreticImage.isIso_imageι_restrict _
  have hvar : AlgebraicGeometry.IsVariety k (((π ⁻¹ᵁ U).ι.imageι ≫ π) ≫ sX) := by
    rw [Category.assoc]
    exact AlgebraicGeometry.Scheme.Hom.isVariety_image k (π ⁻¹ᵁ U).ι (π ≫ sX)
  let ψ := (π ⁻¹ᵁ U).ι.imageι ≫ π
  -- the dense open of `W` over which `ψ` is an isomorphism onto `U`
  let O : (π ⁻¹ᵁ U).ι.image.Opens := (π ⁻¹ᵁ U).ι.imageι ⁻¹ᵁ (π ⁻¹ᵁ U)
  have hO : O.ι ≫ ψ = ((π ⁻¹ᵁ U).ι.imageι ∣_ (π ⁻¹ᵁ U)) ≫ (π ∣_ U) ≫ U.ι := by
    simp only [ψ, O, morphismRestrict_ι, morphismRestrict_ι_assoc]
  have hOne : (O : Set (π ⁻¹ᵁ U).ι.image).Nonempty := by
    obtain ⟨x⟩ := hVne
    exact ⟨_, ((inv ((π ⁻¹ᵁ U).ι.imageι ∣_ (π ⁻¹ᵁ U))).base x).2⟩
  have hOι : IsOpenImmersion (O.ι ≫ ψ) := by rw [hO]; infer_instance
  have hsub : (U : Set X) ⊆ Set.range ψ := by
    intro u hu
    obtain ⟨x, rfl⟩ := hsurj.surj u
    refine ⟨(π ⁻¹ᵁ U).ι.toImage ⟨x, hu⟩, ?_⟩
    change ((π ⁻¹ᵁ U).ι.toImage ≫ (π ⁻¹ᵁ U).ι.imageι ≫ π) ⟨x, hu⟩ = π x
    rw [Scheme.Hom.toImage_imageι_assoc]
    rfl
  have : IsDominant ψ := ⟨hdense.mono hsub⟩
  refine ⟨n, (π ⁻¹ᵁ U).ι.image, ψ ≫ sX, hvar, (π ⁻¹ᵁ U).ι.imageι ≫ i, ψ, inferInstance, ?_,
    inferInstance, inferInstance, isBirationalMorphism_of_isOpenImmersion ψ O (O.2.dense hOne),
    rfl⟩
  simp only [ψ, Category.assoc, hcomm]

/-- A quasi-projective variety in characteristic zero receives a proper surjective birational
`k`-morphism from a nonempty open of a smooth projective `k`-variety. -/
private theorem exists_smooth_projective_open_model_of_isImmersion {k : Type u} [Field k]
    [CharZero k] {n : ℕ} {W : Scheme.{u}} (sW : W ⟶ Spec (.of k)) [MMP.Mori.IsVariety k sW]
    (i : W ⟶ ProjectiveSpace n (Spec (.of k))) (hi : IsImmersion i)
    (hiW : i ≫ (ProjectiveSpace n (Spec (.of k)) ↘ Spec (.of k)) = sW) :
    ∃ (T : Scheme.{u}) (sT : T ⟶ Spec (.of k)) (_ : MMP.Mori.IsProjectiveVariety k sT)
      (_ : Smooth sT) (V : T.Opens) (_ : Nonempty V) (τ : V.toScheme ⟶ W),
      IsProper τ ∧ Surjective τ ∧ IsBirationalMorphism τ ∧ τ ≫ sW = V.ι ≫ sT := by
  obtain ⟨N, V, sV, hV, hVs, j, g, hj, hjV, hgp, hgs, hgb, hg⟩ :=
    exists_smooth_immersed_resolution sW i hi hiW
  have hVv : AlgebraicGeometry.IsVariety k sV := hV
  have := hVv.toIsIntegral
  have := hVv.toLocallyOfFiniteType
  have := hVv.toQuasiCompact
  have := hj
  have := isNoetherian_of_locallyOfFiniteType sV
  have : QuasiCompact j := quasiCompact_of_noetherianSpace_source _
  let p := ProjectiveSpace N (Spec (.of k)) ↘ Spec (.of k)
  let sY := j.imageι ≫ p
  have hYv : AlgebraicGeometry.IsVariety k sY := AlgebraicGeometry.Scheme.Hom.isVariety_image k j p
  have hY : MMP.Mori.IsProjectiveVariety k sY :=
    (MMP.Mori.isProjectiveVariety_iff k sY).2
      ⟨hYv, ⟨N, j.imageι, (inferInstance : IsClosedImmersion j.ker.subschemeι), rfl⟩⟩
  let O : j.image.Opens := j.toImage.opensRange
  let e : V ≅ O := j.toImage.isoOpensRange
  have he : e.hom ≫ O.ι = j.toImage := Scheme.Hom.isoOpensRange_hom_ι _
  have hOs : O.ι ≫ sY = e.inv ≫ sV := by
    rw [Iso.eq_inv_comp, ← Category.assoc, he, ← hjV]
    exact (Scheme.Hom.toImage_imageι_assoc j p)
  have : Nonempty O := ⟨e.hom (Nonempty.some inferInstance)⟩
  have : Smooth (O.ι ≫ sY) := by rw [hOs]; infer_instance
  obtain ⟨T, sT, hT, hTs, f, hf, hiso⟩ := exists_smooth_projective_isIso_morphismRestrict sY O
  have : IsIntegral T := ((MMP.Mori.isProjectiveVariety_iff k sT).1 hT).1.toIsIntegral
  have hne : Nonempty (f ⁻¹ᵁ O) := ⟨(inv (f ∣_ O)) (Nonempty.some inferInstance)⟩
  refine ⟨T, sT, hT, hTs, f ⁻¹ᵁ O, hne, (f ∣_ O) ≫ e.inv ≫ g, inferInstance, inferInstance,
    isBirationalMorphism_comp (isBirationalMorphism_of_isIso _)
      (isBirationalMorphism_comp (isBirationalMorphism_of_isIso _) hgb), ?_⟩
  rw [Category.assoc, Category.assoc, hg, ← hOs, morphismRestrict_ι_assoc, hf]

/-- Over a field of characteristic zero, every variety `X` admits a proper surjective birational
`k`-morphism `τ : V ⟶ X` from a nonempty open `V` of a smooth projective `k`-variety `T`. -/
@[mmp "lem_mmp_foundation_char_zero_variety_projective_smooth_open_model"]
public theorem exists_smooth_projective_open_proper_birational {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsVariety k sX] :
    ∃ (T : Scheme.{u}) (sT : T ⟶ Spec (.of k)) (_ : IsProjectiveVariety k sT) (_ : Smooth sT)
      (V : T.Opens) (_ : Nonempty V) (τ : V.toScheme ⟶ X),
      IsProper τ ∧ Surjective τ ∧ IsBirationalMorphism τ ∧ τ ≫ sX = V.ι ≫ sT := by
  obtain ⟨n, W, sW, hW, i, π, hi, hiW, _, _, hπb, hπ⟩ := exists_immersed_chow_model sX
  obtain ⟨T, sT, hT, hTs, V, hV, τ, _, _, hτb, hτ⟩ :=
    exists_smooth_projective_open_model_of_isImmersion sW i hi hiW
  have : IsIntegral T := ((isProjectiveVariety_iff k sT).1 hT).1.toIsIntegral
  refine ⟨T, sT, hT, hTs, V, hV, τ ≫ π, inferInstance, inferInstance,
    isBirationalMorphism_comp hτb hπb, ?_⟩
  rw [Category.assoc, hπ, hτ]

end MMP.Mori

end
