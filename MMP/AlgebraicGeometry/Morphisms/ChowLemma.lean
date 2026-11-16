module

public import MMP.Attr
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.DevissageChow
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Basic
public import StacksFrontier.AlgebraicGeometry.F6Rank136.ExceptionalCurveContractionBirational
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Variety
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.DenseOpen

/-!
# Chow's lemma for a proper morphism of varieties

Let `h : Z ⟶ Y` be a proper morphism of varieties over a field `k`. Then there are a variety `Z''`
and a projective surjective birational morphism `p : Z'' ⟶ Z` with `h ∘ p` projective. In
particular a proper variety is dominated by a projective variety through a surjective birational
morphism.

## Main results

* `MMP.Resolution.Bridges.exists_isProjectiveMorphism_isBirational_chowModification`: the
  relative statement and its absolute corollary.

## Implementation notes

* A variety is `AlgebraicGeometry.IsVariety k s` for the structure morphism `s`; projectivity is
  H-projectivity `AlgebraicGeometry.IsProjectiveMorphism` (Stacks 01W8: a closed immersion into
  some `ℙⁿ` over the base), and a projective variety is a variety whose structure morphism is
  H-projective. Birationality is `AlgebraicGeometry.IsBirational` (Stacks 01RO).
* The library result is `AlgebraicGeometry.exists_isProjectiveMorphism_denseChowModification`:
  a proper surjective `π : X' ⟶ Z`, an isomorphism over a dense open `U`, with `π ≫ h`
  H-projective. The variety `Z''` is the reduced closure of `π⁻¹(U)` in `X'`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace MMP.Resolution.Bridges

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

private theorem isNoetherian_of_isVariety (k : Type u) [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] [QuasiCompact sY] : IsNoetherian Y := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  exact { toIsLocallyNoetherian := ‹_›, toCompactSpace := ‹_› }

private theorem chow_aux (k : Type u) [Field k] {Z Y : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)}
    {sY : Y ⟶ Spec (.of k)} (hZ : IsVariety k sZ) (hY : IsVariety k sY) (h : Z ⟶ Y)
    (_hh : h ≫ sY = sZ) (hp : IsProper h) :
    ∃ (Z'' : Scheme.{u}) (p : Z'' ⟶ Z), IsVariety k (p ≫ sZ) ∧ IsProjectiveMorphism p ∧
      Surjective p ∧ IsBirational p ∧ IsProjectiveMorphism (p ≫ h) := by
  have : IsNoetherian Y := isNoetherian_of_isVariety k sY
  obtain ⟨X', π, U, hπ, hsurj, ⟨n, i, hi, hcomm⟩, hdense, hiso⟩ :=
    exists_isProjectiveMorphism_denseChowModification h
  have := hπ
  have := hsurj
  have := hiso
  have := hi
  have : IsIntegral Z := hZ.toIsIntegral
  have : IsSeparated h := inferInstance
  have := hZ.toIsSeparated
  have := hZ.toLocallyOfFiniteType
  have := hZ.toQuasiCompact
  have : IsSeparated (π ≫ sZ) := inferInstance
  have : LocallyOfFiniteType (π ≫ sZ) := inferInstance
  have : QuasiCompact (π ≫ sZ) := inferInstance
  have hX' : IsNoetherian X' := isNoetherian_of_isVariety k (π ≫ sZ)
  have hUne : Nonempty U := hdense.nonempty.to_subtype
  have hVne : Nonempty (π ⁻¹ᵁ U) := ⟨(inv (π ∣_ U)).base hUne.some⟩
  have : IsIntegral (π ⁻¹ᵁ U) := isIntegral_of_isOpenImmersion (π ∣_ U)
  have : QuasiCompact (π ⁻¹ᵁ U).ι := inferInstance
  have hi1 : IsIso ((π ⁻¹ᵁ U).ι.imageι ∣_ (π ⁻¹ᵁ U)) :=
    Stacks.SchemeTheoreticImage.isIso_imageι_restrict _
  have : IsClosedImmersion (π ⁻¹ᵁ U).ι.imageι := inferInstance
  have : IsProper ((π ⁻¹ᵁ U).ι.imageι ≫ π) := inferInstance
  refine ⟨(π ⁻¹ᵁ U).ι.image, (π ⁻¹ᵁ U).ι.imageι ≫ π, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc]
    exact Scheme.Hom.isVariety_image k _ (π ≫ sZ)
  · have hproj : IsProjectiveMorphism (((π ⁻¹ᵁ U).ι.imageι ≫ π) ≫ h) :=
      ⟨n, (π ⁻¹ᵁ U).ι.imageι ≫ i, inferInstance, by rw [Category.assoc, hcomm, Category.assoc]⟩
    exact IsProjectiveMorphism.of_comp _ h hproj
  · refine ⟨?_⟩
    have hcl : IsClosed (Set.range ((π ⁻¹ᵁ U).ι.imageι ≫ π)) :=
      ((π ⁻¹ᵁ U).ι.imageι ≫ π).isClosedMap.isClosed_range
    have hsub : (U : Set Z) ⊆ Set.range ((π ⁻¹ᵁ U).ι.imageι ≫ π) := by
      intro u hu
      obtain ⟨x, rfl⟩ := hsurj.surj u
      refine ⟨(π ⁻¹ᵁ U).ι.toImage ⟨x, hu⟩, ?_⟩
      have := (π ⁻¹ᵁ U).ι.toImage_imageι
      change ((π ⁻¹ᵁ U).ι.toImage ≫ (π ⁻¹ᵁ U).ι.imageι ≫ π) ⟨x, hu⟩ = π x
      rw [← Category.assoc, this]
      rfl
    have hd : Dense (Set.range ((π ⁻¹ᵁ U).ι.imageι ≫ π)) := hdense.mono hsub
    intro z
    have := hd.closure_eq
    rw [hcl.closure_eq] at this
    exact (Set.eq_univ_iff_forall.mp this) z
  · refine isBirational_of_isIso_morphismRestrict_of_genericPoint_mem _ U ?_ ?_
    · rw [morphismRestrict_comp]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ hi1 hiso
    · exact ((genericPoint_spec Z).mem_open_set_iff U.isOpen).2 (by
        rw [Set.univ_inter]; exact hdense.nonempty)
  · exact ⟨n, (π ⁻¹ᵁ U).ι.imageι ≫ i, inferInstance, by rw [Category.assoc, hcomm, Category.assoc]⟩

/-- **Relative Chow modification of a proper morphism of varieties.** Let `h : Z ⟶ Y` be a
proper morphism of varieties over `k`. Then there are a variety `Z''` and a projective surjective
birational morphism `p : Z'' ⟶ Z` such that `p ≫ h` is projective. In particular, for a proper
variety `Z` there are a projective variety `Z'` and a surjective birational morphism
`π : Z' ⟶ Z`. -/
@[mmp "lem_mmp_foundation_general_relative_chow_varieties"]
theorem exists_isProjectiveMorphism_isBirational_chowModification (k : Type u) [Field k] :
    (∀ {Z Y : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)},
      IsVariety k sZ → IsVariety k sY → ∀ (h : Z ⟶ Y), h ≫ sY = sZ → IsProper h →
        ∃ (Z'' : Scheme.{u}) (p : Z'' ⟶ Z), IsVariety k (p ≫ sZ) ∧ IsProjectiveMorphism p ∧
          Surjective p ∧ IsBirational p ∧ IsProjectiveMorphism (p ≫ h)) ∧
    (∀ {Z : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)}, IsVariety k sZ → IsProper sZ →
        ∃ (Z' : Scheme.{u}) (π : Z' ⟶ Z), IsVariety k (π ≫ sZ) ∧
          IsProjectiveMorphism (π ≫ sZ) ∧ Surjective π ∧ IsBirational π) := by
  refine ⟨fun {Z Y} {sZ} {sY} hZ hY h hh hp => chow_aux k hZ hY h hh hp, ?_⟩
  intro Z sZ hZ hp
  have hY : IsVariety k (𝟙 (Spec (.of k))) := IsVariety.mk
  obtain ⟨Z', p, h1, h2, h3, h4, h5⟩ := chow_aux k hZ hY sZ (Category.comp_id _) hp
  exact ⟨Z', p, h1, h5, h3, h4⟩

end MMP.Resolution.Bridges
