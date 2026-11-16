module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.Basic
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence
public import MMP.AlgebraicGeometry.Singularities.LogResolution.Basic
public import MMP.AlgebraicGeometry.Resolution.StrongResolutionCharZero

/-!
# Resolutions with snc complement and common resolutions of modifications

Over a field `k` of characteristic zero:

* a variety `X` with a nonempty smooth open `U ⊆ X` has a projective birational morphism
  `g : Y ⟶ X` from a smooth variety which is an isomorphism over `U` and such that `Y ∖ g⁻¹(U)`
  is empty or the support of an snc divisor. One composes a strong resolution `r : Z ⟶ X`, an
  isomorphism over the smooth locus, with the canonical principalization of the ideal
  `I_{X ∖ U} 𝒪_Z`; the principalized ideal is monomial, so its support is an snc closed subset;
* a proper birational `μ₁ : X₁ ⟶ X` and a projective birational `μ₂ : X₂ ⟶ X` from non-singular
  varieties have a common resolution `g₁ : V ⟶ X₁`, `g₂ : V ⟶ X₂` with `g₁ ≫ μ₁ = g₂ ≫ μ₂`:
  a resolution of a quasi-projective Chow modification of the graph `Γ ⊆ X₁ ×_X X₂` of the
  birational identification of `X₁` and `X₂`.

## Main results

* `MMP.Resolution.exists_isResolutionOfVariety_isIso_restrict_isSNCClosedSubset_compl`: a
  resolution which is an isomorphism over `U` and has snc complement.
* `MMP.Intersection.exists_isResolution_comp_eq_comp`: the common resolution of two
  modifications.

## Implementation notes

"Empty or the support of an snc divisor" is `MMP.Resolution.IsSNCClosedSubset`, which admits the
empty set; "projective birational with `Y` smooth" is `MMP.Resolution.IsResolutionOfVariety`.
Projectivity of `g₁` in the common resolution is H-projectivity
(`AlgebraicGeometry.IsProjectiveMorphism`): the graph is first replaced by a Chow modification
which is H-quasi-projective over `k`, so that the proper morphism `V ⟶ X₁` is H-projective. The
auxiliary lemmas of each proof live in the namespace `Proof_<tag>` named after its label.

## References

* [J. Kollár, *Lectures on resolution of singularities*, Thm. 3.36, 3.72]
* [R. Lazarsfeld, *Positivity in algebraic geometry II*, proof of Thm. 9.2.18]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace Proof_thm_mmp_resolution_with_snc_complement

open TopologicalSpace MMP.Resolution

/-- The components of the support of the empty ordered divisor are pairwise disjoint. -/
private theorem pairwise_disjoint_componentsOf_empty {X : Scheme.{u}} :
    (componentsOf (OrderedDivisor.empty X).support).Pairwise Disjoint := by
  intro C hC
  obtain ⟨x, hx⟩ := hC.1.1.nonempty
  obtain ⟨i, -⟩ := Set.mem_iUnion.1 (hC.1.2 hx)
  exact i.elim0

/-- Truncating a blow-up sequence at its length does nothing. -/
private theorem truncate_length {X : Scheme.{u}} (B : ClosedBlowupSequence X) :
    B.truncate B.length = B := by
  induction B with
  | nil _ => rfl
  | cons Z B ih => exact congrArg (ClosedBlowupSequence.cons Z) ih

/-- A morphism of irreducible schemes which is an isomorphism over a nonempty open is
birational. -/
private theorem isBirationalMorphism_of_isIso_restrict {X Y : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (g : Y ⟶ X) (V : X.Opens) [IsIso (g ∣_ V)]
    (hV : (V : Set X).Nonempty) : MMP.Mori.IsBirationalMorphism g := by
  obtain ⟨x, hx⟩ := hV
  obtain ⟨y, -⟩ := (g ∣_ V).surjective ⟨x, hx⟩
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE g _ _ ⟨y.1, y.2⟩ ⟨x, hx⟩ le_rfl ?_
  rwa [Scheme.Hom.resLE_eq_morphismRestrict]

/-- The pullback along `f` of the reduced ideal of `X ∖ U` is supported on `Y ∖ f⁻¹(U)`. -/
private theorem coe_support_comap_vanishingIdeal_compl {X Y : Scheme.{u}} (f : Y ⟶ X)
    (U : X.Opens) :
    (((Scheme.IdealSheafData.vanishingIdeal ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩).comap
      f).support : Set Y) = (f ⁻¹' (U : Set X))ᶜ := by
  rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

/-- The support of a finite product of ideal sheaves is the union of their supports. -/
private theorem coe_support_prod {X : Scheme.{u}} {ι : Type*} (s : Finset ι)
    (F : ι → X.IdealSheafData) :
    ((∏ i ∈ s, F i).support : Set X) = ⋃ i ∈ s, ((F i).support : Set X) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Scheme.IdealSheafData.support_mul, Closeds.coe_sup, ih,
      Finset.set_biUnion_insert]

/-- On a smooth scheme of finite type over a perfect field, the support of a monomial ideal is
an snc closed subset: it is the union of the components of an snc divisor. -/
private theorem isSNCClosedSubset_support_of_isMonomialIdeal {k : Type u} [Field k]
    [PerfectField k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY]
    [QuasiCompact sY] (hY : MMP.Mori.IsSmoothScheme sY) {I : Y.IdealSheafData}
    (hI : IsMonomialIdeal I) : IsSNCClosedSubset sY (I.support : Set Y) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  obtain ⟨D, hD, -, rfl⟩ := exists_divisorWithCoeffs_of_isMonomialIdeal sY hY I hI
  convert hD.isSNCClosedSubset_iUnion using 1
  rw [coe_support_prod, Set.iUnion_subtype]
  refine Set.iUnion₂_congr fun E hE => ?_
  rw [Scheme.IdealSheafData.support_pow _ _ (Finsupp.mem_support_iff.1 hE)]

end Proof_thm_mmp_resolution_with_snc_complement

namespace MMP.Resolution

open TopologicalSpace
open Proof_thm_mmp_resolution_with_snc_complement

/-- **Resolution preserving a smooth open, with snc complement.** Let `X` be a variety over a
field `k` of characteristic zero and `U ⊆ X` a nonempty open smooth over `k`. There is a
projective birational morphism `g : Y ⟶ X` from a smooth variety `Y` which is an isomorphism over
`U` and such that `Y ∖ g⁻¹(U)` is empty or the support of a divisor with simple normal
crossings. -/
@[mmp "thm_mmp_resolution_with_snc_complement"]
public theorem exists_isResolutionOfVariety_isIso_restrict_isSNCClosedSubset_compl
    {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (hX : IsVariety k sX) (U : X.Opens) (hU : (U : Set X).Nonempty)
    (hUs : MMP.Mori.IsSmoothScheme (U.ι ≫ sX)) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ X),
      IsResolutionOfVariety sX g ∧ IsIso (g ∣_ U) ∧
      IsSNCClosedSubset (g ≫ sX) (g ⁻¹' (U : Set X))ᶜ := by
  have : IsIntegral X := hX.toIsIntegral
  -- a strong resolution `r : Z ⟶ X`, an isomorphism over `U`
  obtain ⟨Z, r, hZv, hrproj, -, hZsm, hriso, -⟩ := exists_isStrongResolution sX hX
  have hrU : IsIso (r ∣_ U) := MMP.Mori.isBiregular_iff_le_biregularLocus.2
    ((MMP.Mori.le_smoothLocus sX (Aux.smooth_of_isSmoothScheme' _ hUs)).trans
      (MMP.Mori.le_biregularLocus hriso))
  -- the ideal `J = I_{X ∖ U} 𝒪_Z`, with support `Z ∖ r⁻¹(U)`, nonzero since `r⁻¹(U) ≠ ∅`
  set I := Scheme.IdealSheafData.vanishingIdeal ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩
  have hJ : I.comap r ≠ ⊥ := by
    obtain ⟨x, hx⟩ := hU
    obtain ⟨z, -⟩ := (r ∣_ U).surjective ⟨x, hx⟩
    intro h
    have hz : z.1 ∈ ((I.comap r).support : Set Z) := by
      rw [h]
      trivial
    exact (coe_support_comap_vanishingIdeal_compl r U ▸ hz) z.2
  -- the canonical principalization `s : Y ⟶ Z` of `(Z, J, ∅)`
  obtain ⟨ht, hvar⟩ :=
    isVariety_and_isProjective_toBase_truncate_canonicalPrincipalization (r ≫ sX) hZv hZsm _ hJ
  obtain ⟨-, hmono, hiso, -⟩ := canonicalPrincipalization_properties.{u, u, u}
  set B := canonicalPrincipalization _ (triples_subset_sncTriples ht)
  obtain ⟨hYv, hsproj, -, hYsm⟩ := hvar B.length
  rw [truncate_length] at hYv hsproj hYsm
  have hsJ : IsIso (B.toBase ∣_ (I.comap r).support.compl) :=
    (hiso _ ht pairwise_disjoint_componentsOf_empty).2
  have hsU : IsIso (B.toBase ∣_ r ⁻¹ᵁ U) := by
    refine MMP.Mori.isBiregular_iff_le_biregularLocus.2
      (le_trans ?_ (MMP.Mori.le_biregularLocus hsJ))
    intro z hz
    change z ∉ ((I.comap r).support : Set Z)
    rw [coe_support_comap_vanishingIdeal_compl]
    exact not_not_intro hz
  have hgiso : IsIso ((B.toBase ≫ r) ∣_ U) := by
    rw [morphismRestrict_comp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hsU hrU
  have : IsIntegral B.target := hYv.toIsIntegral
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated sX
  have : LocallyOfFiniteType (B.toBase ≫ r ≫ sX) := hYv.toLocallyOfFiniteType
  have : QuasiCompact (B.toBase ≫ r ≫ sX) := hYv.toQuasiCompact
  refine ⟨B.target, B.toBase ≫ r, ⟨hX, by rwa [Category.assoc], hsproj.comp hrproj,
    isBirationalMorphism_of_isIso_restrict _ U hU, by rwa [Category.assoc]⟩, hgiso, ?_⟩
  -- the complement of `(r ∘ s)⁻¹(U)` is the support of the monomial ideal `J 𝒪_Y`
  rw [Category.assoc, ← coe_support_comap_vanishingIdeal_compl,
    Scheme.IdealSheafData.comap_comp]
  exact isSNCClosedSubset_support_of_isMonomialIdeal _ hYsm (hmono _ ht)

end MMP.Resolution

namespace Proof_lem_p09a_common_resolution

open CategoryTheory.Limits

/-- A morphism `f : Γ ⟶ Y` of irreducible schemes is birational when its composite with an open
immersion from a nonempty scheme is an open immersion. -/
private theorem isBirationalMorphism_of_isOpenImmersion_comp {O Γ Y : Scheme.{u}}
    [IrreducibleSpace Γ] [IrreducibleSpace Y] [Nonempty O] (j : O ⟶ Γ) [IsOpenImmersion j]
    (f : Γ ⟶ Y) [IsOpenImmersion (j ≫ f)] : MMP.Mori.IsBirationalMorphism f := by
  have hle : j.opensRange ≤ f ⁻¹ᵁ (j ≫ f).opensRange := by
    rintro _ ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  obtain ⟨o⟩ := ‹Nonempty O›
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE f j.opensRange (j ≫ f).opensRange
    ⟨j o, o, rfl⟩ ⟨(j ≫ f) o, o, rfl⟩ hle ?_
  have e : (Scheme.Hom.isoOpensRange j).hom ≫ f.resLE _ _ hle =
      (Scheme.Hom.isoOpensRange (j ≫ f)).hom := by
    rw [← cancel_mono (j ≫ f).opensRange.ι, Category.assoc, Scheme.Hom.resLE_comp_ι,
      Scheme.Hom.isoOpensRange_hom_ι_assoc, Scheme.Hom.isoOpensRange_hom_ι]
  rw [← (Iso.inv_comp_eq _).2 e.symm]
  infer_instance

/-- A composite of birational morphisms of irreducible schemes is birational. -/
private theorem isBirationalMorphism_comp {X Y Z : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace Y] [IrreducibleSpace Z] {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : MMP.Mori.IsBirationalMorphism f) (hg : MMP.Mori.IsBirationalMorphism g) :
    MMP.Mori.IsBirationalMorphism (f ≫ g) := by
  have : Nonempty X := IrreducibleSpace.toNonempty
  have : Nonempty Y := IrreducibleSpace.toNonempty
  obtain ⟨W₁, ⟨w, hw⟩, h₁⟩ := hf.exists_isOpenImmersion
  obtain ⟨W₂, hW₂, h₂⟩ := hg.exists_isOpenImmersion
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := nonempty_preirreducible_inter (W₁.ι ≫ f).opensRange.isOpen
    W₂.isOpen ⟨(W₁.ι ≫ f) ⟨w, hw⟩, ⟨w, hw⟩, rfl⟩ hW₂
  let U : X.Opens := W₁ ⊓ f ⁻¹ᵁ W₂
  have : Nonempty U := ⟨⟨x.1, x.2, hx⟩⟩
  have hle : U ≤ f ⁻¹ᵁ W₂ := inf_le_right
  have : IsOpenImmersion (f.resLE W₂ U hle ≫ W₂.ι) := by
    rw [Scheme.Hom.resLE_comp_ι, ← Scheme.homOfLE_ι X (inf_le_left : U ≤ W₁), Category.assoc]
    infer_instance
  have := IsOpenImmersion.of_comp (f.resLE W₂ U hle) W₂.ι
  have : IsOpenImmersion (U.ι ≫ f ≫ g) := by
    rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι f hle, Category.assoc]
    infer_instance
  exact isBirationalMorphism_of_isOpenImmersion_comp U.ι (f ≫ g)

/-- A proper morphism `f : W ⟶ Y` over `S` from an `S`-scheme `W` which is H-quasi-projective
over `S` is H-projective. -/
private theorem isProjectiveMorphism_of_isHQuasiProjective_comp {W Y S : Scheme.{u}}
    {sW : W ⟶ S} (sY : Y ⟶ S) (hW : IsHQuasiProjective sW) (f : W ⟶ Y) (hf : f ≫ sY = sW)
    [IsProper f] : IsProjectiveMorphism f := by
  obtain ⟨n, i, hi, -, hif⟩ := hW
  let j : W ⟶ pullback (projectiveSpaceOver n S ↘ S) sY := pullback.lift i f (by rw [hif, hf])
  have : IsImmersion j := by
    have : IsImmersion (j ≫ pullback.fst _ _) := by rwa [pullback.lift_fst]
    exact IsImmersion.of_comp j (pullback.fst _ _)
  let c := j ≫ (projectiveSpaceOverBaseChangeIso n sY).hom
  have hc : c ≫ (projectiveSpaceOver n Y ↘ Y) = f := by
    simp only [c, Category.assoc, projectiveSpaceOverBaseChangeIso_hom_over, j, pullback.lift_snd]
  have := isProper_projectiveSpaceOver n Y
  have : IsProper (c ≫ (projectiveSpaceOver n Y ↘ Y)) := by
    rw [hc]
    infer_instance
  have : IsProper c := IsProper.of_comp c (projectiveSpaceOver n Y ↘ Y)
  exact ⟨n, c, IsClosedImmersion.of_isPreimmersion c c.isClosedMap.isClosed_range, hc⟩

/-- An open `U ⊆ X` inside the image of an open immersion `W ⟶ X` through `μ : Y ⟶ X` carries a
section `U ⟶ Y` of `μ` which is an open immersion. -/
private theorem exists_isOpenImmersion_section {X Y : Scheme.{u}} {W : Y.Opens} (μ : Y ⟶ X)
    [IsOpenImmersion (W.ι ≫ μ)] {U : X.Opens} (hU : U ≤ (W.ι ≫ μ).opensRange) :
    ∃ s : U.toScheme ⟶ Y, IsOpenImmersion s ∧ s ≫ μ = U.ι := by
  have h : Set.range U.ι ⊆ Set.range (W.ι ≫ μ) := by
    rw [Scheme.Opens.range_ι]
    exact hU
  let l := IsOpenImmersion.lift (W.ι ≫ μ) U.ι h
  have : IsOpenImmersion (l ≫ W.ι ≫ μ) := by
    rw [IsOpenImmersion.lift_fac]
    infer_instance
  have := IsOpenImmersion.of_comp l (W.ι ≫ μ)
  exact ⟨l ≫ W.ι, inferInstance, by simp [l]⟩

/-- Let `φ : O ⟶ Y` be a quasi-compact immersion from a nonempty scheme. If `φ ≫ f` is an open
immersion, then `f` restricted to the scheme-theoretic image of `φ` is birational. -/
private theorem isBirationalMorphism_imageι_comp {O Y Z : Scheme.{u}} [Nonempty O]
    (φ : O ⟶ Y) [IsImmersion φ] [QuasiCompact φ] [IrreducibleSpace φ.image] [IrreducibleSpace Z]
    (f : Y ⟶ Z) {s : O ⟶ Z} [IsOpenImmersion s] (h : φ ≫ f = s) :
    MMP.Mori.IsBirationalMorphism (φ.imageι ≫ f) := by
  have := isOpenImmersion_toImage φ (.inl inferInstance)
  have : IsOpenImmersion (φ.toImage ≫ φ.imageι ≫ f) := by
    rwa [← Category.assoc, Scheme.Hom.toImage_imageι, h]
  exact isBirationalMorphism_of_isOpenImmersion_comp φ.toImage _

/-- **Chow's lemma, quasi-projective form.** A variety `Γ` over `k` admits a proper birational
morphism `q : Γ' ⟶ Γ` from a variety `Γ'` which is H-quasi-projective over `k`. -/
private theorem exists_isHQuasiProjective_modification {k : Type u} [Field k] {Γ : Scheme.{u}}
    (sΓ : Γ ⟶ Spec (.of k)) [IsVariety k sΓ] :
    ∃ (Γ' : Scheme.{u}) (q : Γ' ⟶ Γ), IsVariety k (q ≫ sΓ) ∧ IsHQuasiProjective (q ≫ sΓ) ∧
      IsProper q ∧ MMP.Mori.IsBirationalMorphism q := by
  have : IsIntegral Γ := IsVariety.toIsIntegral (k := k) (f := sΓ)
  have : IsNoetherian Γ := isNoetherian_of_locallyOfFiniteType sΓ
  obtain ⟨n, Y, π, i, U, hπ, -, hi, hcomm, hU, hiso⟩ :=
    hasChowModificationIsoOnDenseOpen_of_isAffine sΓ
  have : IsProper π := hπ
  have : IsImmersion i := hi
  have : IsIso (π ∣_ U) := hiso
  have : Nonempty U := hU.nonempty.to_subtype
  let σ : U.toScheme ⟶ Y := inv (π ∣_ U) ≫ (π ⁻¹ᵁ U).ι
  have hσ : σ ≫ π = U.ι := by
    rw [Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  have : IsImmersion σ := by
    have : IsImmersion (σ ≫ π) := by
      rw [hσ]
      infer_instance
    exact IsImmersion.of_comp σ π
  have : TopologicalSpace.NoetherianSpace U := TopologicalSpace.NoetherianSpace.set (U : Set Γ)
  have : QuasiCompact σ := quasiCompact_of_noetherianSpace_source σ
  have hv := Scheme.Hom.isVariety_image k σ (π ≫ sΓ)
  have : IsIntegral σ.image := hv.toIsIntegral
  have : IsNoetherian σ.image := isNoetherian_of_locallyOfFiniteType (σ.imageι ≫ π ≫ sΓ)
  have : QuasiCompact (σ.imageι ≫ i) := quasiCompact_of_noetherianSpace_source _
  refine ⟨σ.image, σ.imageι ≫ π, by simpa only [Category.assoc] using hv,
    ⟨n, σ.imageι ≫ i, inferInstance, inferInstance, ?_⟩, inferInstance,
    isBirationalMorphism_imageι_comp σ π hσ⟩
  rw [Category.assoc, ← hcomm, Category.assoc]

end Proof_lem_p09a_common_resolution

namespace MMP.Intersection

open CategoryTheory.Limits
open Proof_lem_p09a_common_resolution

/-- **Common resolution of two modifications.** Given a proper birational morphism
`μ₁ : X₁ ⟶ X` and a projective birational morphism `μ₂ : X₂ ⟶ X` from non-singular varieties to
a variety `X` over a field of characteristic zero, there are a non-singular variety `V`, a
projective birational morphism `g₁ : V ⟶ X₁` and a proper birational morphism `g₂ : V ⟶ X₂`
with `g₁ ≫ μ₁ = g₂ ≫ μ₂`. -/
@[mmp "lem_p09a_common_resolution"]
public theorem exists_isResolution_comp_eq_comp {k : Type u} [Field k] [CharZero k]
    {X X₁ X₂ : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsVariety k sX]
    (μ₁ : X₁ ⟶ X) (μ₂ : X₂ ⟶ X)
    [IsVariety k (μ₁ ≫ sX)] [IsVariety k (μ₂ ≫ sX)]
    (hX₁ : MMP.Mori.IsSmoothScheme (μ₁ ≫ sX)) (hX₂ : MMP.Mori.IsSmoothScheme (μ₂ ≫ sX))
    [IsProper μ₁] (hμ₂ : IsProjectiveMorphism μ₂)
    (hb₁ : MMP.Mori.IsBirationalMorphism μ₁) (hb₂ : MMP.Mori.IsBirationalMorphism μ₂) :
    ∃ (V : Scheme.{u}) (g₁ : V ⟶ X₁) (g₂ : V ⟶ X₂),
      IsResolution (μ₁ ≫ sX) g₁ ∧ IsProper g₂ ∧ MMP.Mori.IsBirationalMorphism g₂ ∧
        g₁ ≫ μ₁ = g₂ ≫ μ₂ := by
  have : IsProper μ₂ := isProper_of_isProjectiveMorphism μ₂ hμ₂
  have : IsIntegral X := IsVariety.toIsIntegral (k := k) (f := sX)
  have : IsIntegral X₁ := IsVariety.toIsIntegral (k := k) (f := μ₁ ≫ sX)
  have : IsIntegral X₂ := IsVariety.toIsIntegral (k := k) (f := μ₂ ≫ sX)
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType sX
  /- Step 1: a dense open `O ⊆ X` with sections `sᵢ : O ⟶ Xᵢ` of `μᵢ`. -/
  obtain ⟨W₁, ⟨w₁, hw₁⟩, h₁⟩ := hb₁.exists_isOpenImmersion
  obtain ⟨W₂, ⟨w₂, hw₂⟩, h₂⟩ := hb₂.exists_isOpenImmersion
  let O : X.Opens := (W₁.ι ≫ μ₁).opensRange ⊓ (W₂.ι ≫ μ₂).opensRange
  have : Nonempty O := (nonempty_preirreducible_inter (W₁.ι ≫ μ₁).opensRange.isOpen
    (W₂.ι ≫ μ₂).opensRange.isOpen ⟨_, ⟨w₁, hw₁⟩, rfl⟩ ⟨_, ⟨w₂, hw₂⟩, rfl⟩).to_subtype
  obtain ⟨s₁, _, hs₁⟩ := exists_isOpenImmersion_section μ₁ (inf_le_left : O ≤ _)
  obtain ⟨s₂, _, hs₂⟩ := exists_isOpenImmersion_section μ₂ (inf_le_right : O ≤ _)
  /- Step 2: the graph `Γ ⊆ X₁ ×_X X₂`, the scheme-theoretic image of `(s₁, s₂)`. -/
  let φ : O.toScheme ⟶ pullback μ₁ μ₂ := pullback.lift s₁ s₂ (by rw [hs₁, hs₂])
  have : IsImmersion φ := by
    have : IsImmersion (φ ≫ pullback.fst μ₁ μ₂) := by
      rw [pullback.lift_fst]
      infer_instance
    exact IsImmersion.of_comp φ (pullback.fst _ _)
  have : TopologicalSpace.NoetherianSpace O := TopologicalSpace.NoetherianSpace.set (O : Set X)
  have : QuasiCompact φ := quasiCompact_of_noetherianSpace_source φ
  let sΓ : φ.image ⟶ Spec (.of k) := φ.imageι ≫ pullback.fst μ₁ μ₂ ≫ μ₁ ≫ sX
  have hΓ : IsVariety k sΓ := Scheme.Hom.isVariety_image k φ _
  have : IsIntegral φ.image := hΓ.toIsIntegral
  /- Step 3: a Chow modification `q : Γ' ⟶ Γ` with `Γ'` quasi-projective over `k`. -/
  obtain ⟨Γ', q, hΓ', hΓ'qp, hq, hbq⟩ := exists_isHQuasiProjective_modification sΓ
  /- Step 4: a resolution `r : V ⟶ Γ'`. -/
  obtain ⟨V, r, hV, hr, hbr, hsm, -, -⟩ := MMP.Resolution.exists_isStrongResolution _ hΓ'
  have : IsProper r := hr.isProper
  have hVqp : IsHQuasiProjective (r ≫ q ≫ sΓ) :=
    isHQuasiProjective_of_isQuasiProjective _ (Stacks.Ample.unitModule _)
      (Stacks.Ample.isAmple_unitModule_of_isAffine _)
      (isQuasiProjective_comp_of_exists_isAmple r (q ≫ sΓ)
        ⟨_, inferInstance, Stacks.Ample.isAmple_unitModule_of_isAffine _⟩ hr.isQuasiProjective
        (isQuasiProjective_of_isHQuasiProjective _ hΓ'qp))
  /- Step 5: the common resolution `gᵢ = r ≫ q ≫ pᵢ`, `pᵢ` the projections of `Γ`. -/
  have hassoc : (r ≫ q ≫ φ.imageι ≫ pullback.fst μ₁ μ₂) ≫ μ₁ ≫ sX = r ≫ q ≫ sΓ := by
    simp only [sΓ, Category.assoc]
  have : IsIntegral V := hV.toIsIntegral
  have : IsIntegral Γ' := hΓ'.toIsIntegral
  refine ⟨V, r ≫ q ≫ φ.imageι ≫ pullback.fst μ₁ μ₂, r ≫ q ≫ φ.imageι ≫ pullback.snd μ₁ μ₂,
    ⟨inferInstance, hassoc ▸ hV, hassoc ▸ hsm,
      isProjectiveMorphism_of_isHQuasiProjective_comp (μ₁ ≫ sX) hVqp _ hassoc, ?_⟩,
    inferInstance, ?_, by simp only [Category.assoc, pullback.condition]⟩ <;>
  refine isBirationalMorphism_comp hbr (isBirationalMorphism_comp hbq ?_)
  · exact isBirationalMorphism_imageι_comp φ _ (pullback.lift_fst _ _ _)
  · exact isBirationalMorphism_imageι_comp φ _ (pullback.lift_snd _ _ _)

end MMP.Intersection
