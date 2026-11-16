module

public import MMP.AlgebraicGeometry.MMP.Abundance.Basic

/-!
# Étale base change of a resolution

Let `q : Y_e ⟶ Y₀` be an étale morphism of normal varieties over a field `k`, and
`μ : W ⟶ Y₀` a projective morphism from a smooth variety `W` which is an isomorphism over a
dense open `U ⊆ Y₀`. Then the base change `W_e = W ×_{Y₀} Y_e` is a smooth variety, and the
projection `μ_e : W_e ⟶ Y_e` is projective, birational and an isomorphism over `q⁻¹(U)`; at the
generic point of `W_e` it induces an isomorphism of function fields `k(Y_e) ≅ k(W_e)`.

## Main results

* `MMP.Fourfold.isVariety_pullback_snd_of_etale`.

## Implementation notes

* "Projective" is H-projectivity, `AlgebraicGeometry.IsProjectiveMorphism`; "an isomorphism
  over `U`" is that the restriction `μ ∣_ U : μ⁻¹(U) ⟶ U` is an isomorphism.
* The identification of the function field of `W_e` with `k(Y_e)` is the canonical one: `μ_e`
  sends every generic point `w` of `W_e` to the generic point of `Y_e`, and the stalk map
  `𝒪_{Y_e, μ_e(w)} ⟶ 𝒪_{W_e, w}` is an isomorphism.
* The source works over `ℂ`; the statement is made over an arbitrary field `k`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace MMP.Fourfold

/-- If `μ` is an isomorphism over `U`, then its base change `pullback.snd μ q` is an
isomorphism over `q⁻¹(U)`. -/
theorem isIso_pullback_snd_morphismRestrict {X Y Z : Scheme.{u}} (μ : X ⟶ Y) (q : Z ⟶ Y)
    (U : Y.Opens) (hμU : IsIso (μ ∣_ U)) : IsIso (pullback.snd μ q ∣_ (q ⁻¹ᵁ U)) := by
  have AB := (isPullback_morphismRestrict (pullback.snd μ q) (q ⁻¹ᵁ U)).paste_vert
    (IsPullback.of_hasPullback μ q).flip
  have C := isPullback_morphismRestrict μ U
  have hw : (pullback.snd μ q ∣_ (q ⁻¹ᵁ U) ≫ q ∣_ U) ≫ U.ι =
      ((pullback.snd μ q ⁻¹ᵁ (q ⁻¹ᵁ U)).ι ≫ pullback.fst μ q) ≫ μ := by
    simp only [Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc, pullback.condition]
  have h1 : C.lift _ _ hw ≫ (μ ⁻¹ᵁ U).ι =
      (pullback.snd μ q ⁻¹ᵁ (q ⁻¹ᵁ U)).ι ≫ pullback.fst μ q := C.lift_snd _ _ hw
  have h2 : pullback.snd μ q ∣_ (q ⁻¹ᵁ U) ≫ q ∣_ U = C.lift _ _ hw ≫ μ ∣_ U :=
    (C.lift_fst _ _ hw).symm
  rw [← h1, show (q ⁻¹ᵁ U).ι ≫ q = q ∣_ U ≫ U.ι from (morphismRestrict_ι q U).symm] at AB
  exact MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms Scheme)
    (IsPullback.of_bot AB h2 C).flip hμU

/-- **Étale base change of a resolution.** Let `q : Y_e ⟶ Y₀` be an étale morphism of normal
varieties over `k`, and `μ : W ⟶ Y₀` a projective morphism over `k` from a smooth variety `W`
which is an isomorphism over a dense open `U ⊆ Y₀`. Then `W_e = W ×_{Y₀} Y_e` is a smooth
variety over `k`, the projection `μ_e : W_e ⟶ Y_e` is projective, an isomorphism over
`q⁻¹(U)`, and birational, and at every generic point `w` of `W_e` it maps `w` to the generic
point of `Y_e` and induces an isomorphism of local rings, i.e. `k(W_e) ≅ k(Y_e)`. -/
@[mmp "lem_oai4_c2_etale_base_change_integral"]
theorem isVariety_pullback_snd_of_etale {k : Type*} [Field k]
    {Y₀ Yₑ W : Scheme.{_}} {s₀ : Y₀ ⟶ Spec (.of k)} {sₑ : Yₑ ⟶ Spec (.of k)}
    {sW : W ⟶ Spec (.of k)}
    [IsVariety k s₀] [IsVariety k sₑ] [IsNormal Y₀] [IsNormal Yₑ]
    (q : Yₑ ⟶ Y₀) [Etale q] (hq : q ≫ s₀ = sₑ)
    [IsVariety k sW] [Smooth sW]
    (μ : W ⟶ Y₀) (hμ : μ ≫ s₀ = sW) (hμp : IsProjectiveMorphism μ)
    (U : Y₀.Opens) (hU : Dense (U : Set Y₀)) (hμU : IsIso (μ ∣_ U)) :
    IsVariety k (pullback.snd μ q ≫ sₑ) ∧ Smooth (pullback.snd μ q ≫ sₑ) ∧
      IsProjectiveMorphism (pullback.snd μ q) ∧
      IsIso (pullback.snd μ q ∣_ (q ⁻¹ᵁ U)) ∧
      MMP.Mori.RationalMap.IsBirational (pullback.snd μ q).toRationalMap ∧
      ∀ w : (pullback μ q : Scheme), closure {w} = Set.univ →
        (pullback.snd μ q).base w = genericPoint Yₑ ∧
          IsIso ((pullback.snd μ q).stalkMap w) := by
  set f := pullback.snd μ q
  set g := pullback.fst μ q
  set V : Yₑ.Opens := q ⁻¹ᵁ U
  have hcomp : f ≫ sₑ = g ≫ sW := by
    simp only [f, g, ← hq, ← hμ, pullback.condition_assoc]
  have hfp : IsProjectiveMorphism f := hμp.baseChange q
  have : IsProper f := isProper_of_isProjectiveMorphism f hfp
  have : Etale g := MorphismProperty.of_isPullback (IsPullback.of_hasPullback μ q).flip ‹Etale q›
  have hfV : IsIso (f ∣_ V) := isIso_pullback_snd_morphismRestrict μ q U hμU
  have : UniversallyOpen q := UniversallyOpen.of_flat q
  have : UniversallyOpen g := UniversallyOpen.of_flat g
  obtain ⟨y₀⟩ : Nonempty Yₑ := inferInstance
  obtain ⟨_, ⟨v, rfl⟩, hyU⟩ := hU.inter_open_nonempty (Set.range q.base) q.isOpenMap.isOpen_range
    ⟨q.base y₀, Set.mem_range_self _⟩
  have hv : v ∈ V := hyU
  have hne : Nonempty (f ⁻¹ᵁ V).toScheme := ⟨(inv (f ∣_ V)).base ⟨v, hv⟩⟩
  obtain ⟨x⟩ := id hne
  have hset : SetLike.coe (f ⁻¹ᵁ V) = g.base ⁻¹' SetLike.coe (μ ⁻¹ᵁ U) := by
    ext z
    have := congrArg (fun h => h.base z) (pullback.condition (f := μ) (g := q))
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
    simp [V, f, g, this]
  have hWU : Dense (SetLike.coe (μ ⁻¹ᵁ U)) :=
    (μ ⁻¹ᵁ U).isOpen.dense ⟨g.base x.1, by
      simpa [hset] using (show x.1 ∈ SetLike.coe (f ⁻¹ᵁ V) from x.2)⟩
  have hdense : Dense (SetLike.coe (f ⁻¹ᵁ V)) := hset ▸ hWU.preimage g.isOpenMap
  have hfVo : IsOpenImmersion (f ∣_ V) := .of_isIso _
  have : IsIntegral (f ⁻¹ᵁ V).toScheme := isIntegral_of_isOpenImmersion (f ∣_ V ≫ V.ι)
  have hirr : IsIrreducible (SetLike.coe (f ⁻¹ᵁ V)) := by
    rw [← Scheme.Opens.range_ι, ← Set.image_univ]
    exact (irreducibleSpace_def _).mp inferInstance |>.image _ (f ⁻¹ᵁ V).ι.continuous.continuousOn
  have : IrreducibleSpace (pullback μ q : Scheme) :=
    (irreducibleSpace_def _).mpr (by
      change IsIrreducible Set.univ
      rw [← hdense.closure_eq]
      exact hirr.closure)
  have : IsIntegral W := IsVariety.toIsIntegral (k := k) (f := sW)
  have : IsReduced W := isReduced_of_isIntegral W
  have : IsReduced (pullback μ q : Scheme) := isReduced_of_etale g
  have : IsIntegral (pullback μ q : Scheme) := isIntegral_of_irreducibleSpace_of_isReduced _
  have hVd : Dense (SetLike.coe V) := V.isOpen.dense ⟨v, hv⟩
  refine ⟨?_, ?_, hfp, hfV, ?_, ?_⟩
  · exact @IsVariety.mk k _ _ _ ‹_›
      (MorphismProperty.comp_mem @IsSeparated f sₑ IsProper.toIsSeparated
        (IsVariety.toIsSeparated (k := k)))
      (MorphismProperty.comp_mem @LocallyOfFiniteType f sₑ IsProper.toLocallyOfFiniteType
        (IsVariety.toLocallyOfFiniteType (k := k)))
      (MorphismProperty.comp_mem @QuasiCompact f sₑ
        (@instQuasiCompactOfUniversallyClosed _ _ f IsProper.toUniversallyClosed)
        (IsVariety.toQuasiCompact (k := k)))
  · rw [hcomp]
    infer_instance
  · exact MMP.Flips.isBirationalMorphism_of_isIso_resLE f (f ⁻¹ᵁ V) V ⟨x.1, x.2⟩ ⟨v, hv⟩ le_rfl
      (by rwa [Scheme.Hom.resLE_eq_morphismRestrict])
  · intro w hw
    have hwV : w ∈ SetLike.coe (f ⁻¹ᵁ V) := by
      by_contra h
      have : closure {w} ⊆ (SetLike.coe (f ⁻¹ᵁ V))ᶜ :=
        closure_minimal (by simpa using h) (f ⁻¹ᵁ V).isOpen.isClosed_compl
      rw [hw] at this
      exact this (Set.mem_univ x.1) x.2
    have hsurj : ∀ y ∈ V, ∃ z, f.base z = y := fun y hy => by
      obtain ⟨z, hz⟩ := (f ∣_ V).homeomorph.surjective ⟨y, hy⟩
      exact ⟨z.1, by rw [← morphismRestrict_base_coe]; exact congrArg Subtype.val hz⟩
    have hclos : closure (f.base '' Set.univ) = Set.univ := by
      refine Dense.closure_eq (hVd.mono fun y hy => ?_)
      obtain ⟨z, hz⟩ := hsurj y hy
      exact ⟨z, trivial, hz⟩
    have h2 := (show IsGenericPoint w Set.univ from hw).image f.continuous
    rw [hclos] at h2
    refine ⟨h2.eq (genericPoint_spec Yₑ), ?_⟩
    exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
      (morphismRestrictStalkMap f V ⟨w, hwV⟩)).mp
      (@IsOpenImmersion.instIsIsoCommRingCatStalkMap _ _ (f ∣_ V) hfVo ⟨w, hwV⟩)

end MMP.Fourfold

end
