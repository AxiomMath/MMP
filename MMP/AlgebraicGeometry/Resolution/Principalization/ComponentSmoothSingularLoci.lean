module
public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.Principalization.CanonicalFunctor
public import MMP.AlgebraicGeometry.Resolution.Principalization.ComponentRestriction
public import MMP.AlgebraicGeometry.Resolution.Principalization
public import MMP.AlgebraicGeometry.Resolution.SNCRestriction
public import MMP.AlgebraicGeometry.Resolution.OneBlowupTotalTransform
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence.PushforwardSmooth
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
public import MMP.AlgebraicGeometry.Resolution.ExceptionalDivisorPrime
public import MMP.AlgebraicGeometry.Intersection.CartierRestriction
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence.FlatPullback
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence.Restriction
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence.EntryIndex

/-!
# The canonical principalization restricted to a component: smooth and singular loci

Let `P` be a smooth equidimensional scheme of finite type over a field `k` of characteristic `0`
and `X = I.subscheme ⊆ P` a reduced closed subscheme all of whose irreducible components have
codimension `≥ 2`. Let `𝐁 = 𝓑𝓟^can(P, I, ∅)`, let `C` be an irreducible component of `X` with
generic point `η`, `j = 𝐁.entryIndex η`, and `g : C_j → C` the composite of the restriction
`(𝐁.truncate j).restrict C` of the first `j` blow-ups of `𝐁` to `C`, with `C_j ⊆ P_j` embedded by
`restrictHom`. Near a point `x` of `C` at which `X` is smooth, the centres of the first `j`
blow-ups miss a neighbourhood of `x`; so `g` is an isomorphism over a neighbourhood `V` of `x`,
and `g⁻¹(V)` misses the total exceptional set `Ex_tot(Π_j)`. The trace `C_j ∩ Ex_tot(Π_j)` is a
divisor with simple normal crossings on `C_j`, and when `C` meets no other irreducible component
of `X` it is the preimage `g⁻¹(Sing C)` of the singular locus of `C` (Kollár, p. 139-140).

## Main results

* `exists_isIso_morphismRestrict_toBase_restrict_canonicalPrincipalization`:
  `g` is an isomorphism over a neighbourhood of a smooth point of `X` on `C`.
* `exists_disjoint_preimage_totalExceptionalSet_truncate_canonicalPrincipalization`:
  over such a neighbourhood, `C_j` misses `Ex_tot(Π_j)`.
* `isSNCClosedSubset_restrictHom_preimage_totalExceptionalSet_canonicalPrincipalization`:
  `C_j ∩ Ex_tot(Π_j)` is an snc divisor on `C_j`.
* `preimage_singularLocus_toBase_restrict_canonicalPrincipalization`:
  `g⁻¹(Sing C) = C_j ∩ Ex_tot(Π_j)` when `C` is a connected component of `X`.

## Implementation notes

The component `C` is the closed subscheme `vanishingIdeal (closure {η})` of `P`, the reduced
induced structure on the closure of `η`; the restricted sequence is `(𝐁.truncate j).restrict C`
and `g` its `toBase`. `C_j ∩ Ex_tot(Π_j)` is the preimage of `(𝐁.truncate j).totalExceptionalSet`
under the closed immersion `(𝐁.truncate j).restrictHom C : C_j → P_j`. Each statement asserts
that `(P, I, ∅)` lies in `MMP.Resolution.triples`, the domain of
`MMP.Resolution.canonicalPrincipalization`. The auxiliary lemmas of each proof live in the
namespace `Proof_<tag>` named after its label.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.72 and p. 139-140]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace Proof_lem_kr3f_strong_resolution_iso_over_smooth_locus

open MMP.Resolution

/-- If the images of the centres of `𝐁` lie in `S`, so do those of the pull-back `h^*𝐁`. -/
private theorem centersLieOver_pullback {X X₀ Y : Scheme.{u}} (B : ClosedBlowupSequence X)
    (f : X ⟶ X₀) (S : Set X₀) (hB : B.CentersLieOver f S) (h : Y ⟶ X) :
    (B.pullback h).CentersLieOver (h ≫ f) S := by
  induction B generalizing Y X₀ with
  | nil X => trivial
  | cons Z B ih =>
    refine ⟨?_, ?_⟩
    · rintro _ ⟨p, hp, rfl⟩
      rw [Scheme.IdealSheafData.support_comap] at hp
      exact hB.1 ⟨h p, hp, rfl⟩
    · have := ih (blowUpToBase Z ≫ f) S hB.2 (canonicalLift h Z)
      rwa [← Category.assoc, canonicalLift_comp_blowUpToBase, Category.assoc] at this

/-- If the images of the centres of `𝐁` miss the open `V`, then `Π : X_r → X` is an isomorphism
over the inverse image of `V`. -/
private theorem isIso_toBase_restrict_of_centersLieOver {X X₀ : Scheme.{u}}
    (B : ClosedBlowupSequence X) (f : X ⟶ X₀) (V : X₀.Opens)
    (hB : B.CentersLieOver f (V : Set X₀)ᶜ) : IsIso (B.toBase ∣_ (f ⁻¹ᵁ V)) := by
  induction B generalizing X₀ with
  | nil X =>
    change IsIso (𝟙 X ∣_ (f ⁻¹ᵁ V))
    infer_instance
  | @cons X Z B ih =>
    have := isIso_blowUp_restrict_compl_support Z
    have h : IsIso (blowUpToBase Z ∣_ (f ⁻¹ᵁ V)) :=
      Kollar.isIso_morphismRestrict_of_le (W := ⟨_, Z.support.isClosed.isOpen_compl⟩) _
        fun p hp hpZ ↦ hB.1 ⟨p, hpZ, rfl⟩ hp
    change IsIso ((B.toBase ≫ blowUpToBase Z) ∣_ (f ⁻¹ᵁ V))
    rw [morphismRestrict_comp]
    exact IsIso.comp_isIso' (ih (blowUpToBase Z ≫ f) V hB.2) h

end Proof_lem_kr3f_strong_resolution_iso_over_smooth_locus

namespace MMP.Resolution

open Proof_lem_kr3f_strong_resolution_iso_over_smooth_locus

/-- **Kollár, p. 139.** Let `P` be a smooth equidimensional scheme of finite type over a field
`k` of characteristic `0`, and `X = I.subscheme ⊆ P` a closed subscheme all of whose
irreducible components have codimension `≥ 2`. Let `𝐁 = 𝓑𝓟^can(P, I, ∅)`
(`MMP.Resolution.canonicalPrincipalization`), let `η` be the generic point of an irreducible
component `C` of `X`, `j = 𝐁.entryIndex η`, and `g : C_j → C` the composite of the restriction
`(𝐁.truncate j).restrict C`. If `x` is a point of `C` at which `X` is smooth, then there is an
open neighbourhood `V` of `x` in `C` such that `g ∣_ V : g⁻¹(V) → V` is an isomorphism. -/
@[mmp "lem_kr3f_strong_resolution_iso_over_smooth_locus"]
public theorem exists_isIso_morphismRestrict_toBase_restrict_canonicalPrincipalization
    {k : Type u} [Field k] [CharZero k] {P : Scheme.{u}} (sP : P ⟶ Spec (.of k))
    (hsm : IsSmoothScheme sP) [QuasiCompact sP] (heq : Equidimensional P)
    (I : P.IdealSheafData)
    (hcodim : 2 ≤ closedsCodimension I.support)
    (η : P) (hη : closure {η} ∈ componentsOf (I.support : Set P))
    (x : I.subscheme) (hx : x ∈ smoothLocus (I.subschemeι ≫ sP))
    (hxC : I.subschemeι.base x ∈ closure {η}) :
    ∃ ht : (⟨⟨P, I, OrderedDivisor.empty P⟩, k, sP⟩ : FieldBlowupTriple.{u}) ∈ triples,
      let B := canonicalPrincipalization _ (triples_subset_sncTriples ht)
      let C : P.IdealSheafData :=
        Scheme.IdealSheafData.vanishingIdeal ⟨closure {η}, isClosed_closure⟩
      let g := ((B.truncate (B.entryIndex η)).restrict C).toBase
      ∃ (V : C.subscheme.Opens) (y : C.subscheme),
        C.subschemeι.base y = I.subschemeι.base x ∧ y ∈ V ∧ IsIso (g ∣_ V) := by
  obtain ⟨ht, U, hxU, hU, -⟩ :=
    exists_centersLieOver_compl_and_comap_eq_canonicalPrincipalization sP hsm heq I hcodim
      η hη x hx hxC
  refine ⟨ht, ?_⟩
  intro B C g
  obtain ⟨y, hy⟩ : I.subschemeι.base x ∈ Set.range C.subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    simpa [C] using hxC
  refine ⟨(C.subschemeι ≫ 𝟙 P) ⁻¹ᵁ U, y, hy, by simpa [hy] using hxU,
    isIso_toBase_restrict_of_centersLieOver _ _ U (centersLieOver_pullback _ _ _ hU _)⟩

end MMP.Resolution

namespace Proof_lem_kr3f_smooth_locus_off_exceptional

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori MMP.Resolution

/-- If the images in `X₀` (via `f`) of all centres of `B` lie in `S`, then so does the image of
the total exceptional set of `B`. -/
private theorem image_totalExceptionalSet_subset_of_centersLieOver :
    ∀ {X X₀ : Scheme.{u}} (B : ClosedBlowupSequence X) (f : X ⟶ X₀) (S : Set X₀),
      B.CentersLieOver f S → (B.toBase ≫ f).base '' B.totalExceptionalSet ⊆ S
  | _, _, .nil _, _, _, _ => by simp [ClosedBlowupSequence.totalExceptionalSet]
  | _, _, .cons Z B, f, S, h => by
    obtain ⟨hZ, hB⟩ := h
    rintro _ ⟨z, hz | hz, rfl⟩
    · exact hZ ⟨_, hz, rfl⟩
    · exact image_totalExceptionalSet_subset_of_centersLieOver B _ S hB ⟨z, hz, rfl⟩

end Proof_lem_kr3f_smooth_locus_off_exceptional

namespace MMP.Resolution

open Proof_lem_kr3f_smooth_locus_off_exceptional

/-- **Kollár, p. 140.** Let `P` be a smooth equidimensional scheme of finite type over a field
`k` of characteristic `0`, and `X = I.subscheme ⊆ P` a closed subscheme all of whose
irreducible components have codimension `≥ 2`. Let `𝐁 = 𝓑𝓟^can(P, I, ∅)`
(`MMP.Resolution.canonicalPrincipalization`), let `η` be the generic point of an irreducible
component `C` of `X`, `j = 𝐁.entryIndex η`, and `g : C_j → C` the composite of the restriction
`(𝐁.truncate j).restrict C`. If `x` is a point of `C` at which `X` is smooth, then there is an
open neighbourhood `V` of `x` in `C` such that `g⁻¹(V) ⊆ C_j ⊆ P_j` does not meet the total
exceptional set `(𝐁.truncate j).totalExceptionalSet`. -/
@[mmp "lem_kr3f_smooth_locus_off_exceptional"]
public theorem exists_disjoint_preimage_totalExceptionalSet_truncate_canonicalPrincipalization
    {k : Type u} [Field k] [CharZero k] {P : Scheme.{u}} (sP : P ⟶ Spec (.of k))
    (hsm : IsSmoothScheme sP) [QuasiCompact sP] (heq : Equidimensional P)
    (I : P.IdealSheafData)
    (hcodim : 2 ≤ closedsCodimension I.support)
    (η : P) (hη : closure {η} ∈ componentsOf (I.support : Set P))
    (x : I.subscheme) (hx : x ∈ smoothLocus (I.subschemeι ≫ sP))
    (hxC : I.subschemeι.base x ∈ closure {η}) :
    ∃ ht : (⟨⟨P, I, OrderedDivisor.empty P⟩, k, sP⟩ : FieldBlowupTriple.{u}) ∈ triples,
      let B := canonicalPrincipalization _ (triples_subset_sncTriples ht)
      let C : P.IdealSheafData :=
        Scheme.IdealSheafData.vanishingIdeal ⟨closure {η}, isClosed_closure⟩
      let Bj := B.truncate (B.entryIndex η)
      ∃ (V : C.subscheme.Opens) (y : C.subscheme),
        C.subschemeι.base y = I.subschemeι.base x ∧ y ∈ V ∧
          Disjoint ((Bj.restrict C).toBase.base ⁻¹' (V : Set C.subscheme))
            ((Bj.restrictHom C).base ⁻¹' Bj.totalExceptionalSet) := by
  obtain ⟨ht, U, hxU, hlie, -⟩ :=
    exists_centersLieOver_compl_and_comap_eq_canonicalPrincipalization sP hsm heq I hcodim
      η hη x hx hxC
  refine ⟨ht, ?_⟩
  intro B C Bj
  obtain ⟨y, hy⟩ : I.subschemeι.base x ∈ Set.range C.subschemeι.base := by
    simpa [C, Scheme.IdealSheafData.range_subschemeι] using hxC
  refine ⟨C.subschemeι ⁻¹ᵁ U, y, hy, by simpa [hy] using hxU,
    Set.disjoint_left.2 fun z hzV hzE => ?_⟩
  refine image_totalExceptionalSet_subset_of_centersLieOver Bj (𝟙 P) _ hlie ⟨_, hzE, ?_⟩ hzV
  rw [Category.comp_id]
  exact congrArg (fun g => g.base z) (Kollar.pullbackHom_toBase_comm Bj C.subschemeι)

end MMP.Resolution

namespace Proof_lem_kr3f_sing_preimage_snc

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori MMP.Resolution
  MMP.Resolution.ClosedBlowupSequence

/-! ### Blow-up sequences -/

/-- If `D.append C` is smooth over `k`, so is `C`, over `D.toBase ≫ s`. -/
private theorem isSmooth_of_isSmooth_append {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) (D : ClosedBlowupSequence X) (C : ClosedBlowupSequence D.target)
    (h : (D.append C).IsSmooth s) : C.IsSmooth (D.toBase ≫ s) := by
  induction D with
  | nil X =>
    change C.IsSmooth (𝟙 X ≫ s)
    rwa [Category.id_comp]
  | cons Z D ih =>
    change C.IsSmooth ((D.toBase ≫ blowUpToBase Z) ≫ s)
    rw [Category.assoc]
    exact ih _ C h.2.2

/-- If the centres of `D.append C` have snc with `E`, those of `C` have snc with the total
transform `D⁻¹_tot(E)`. -/
private theorem centersHaveSNCWith_of_append {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) (D : ClosedBlowupSequence X) (C : ClosedBlowupSequence D.target)
    (E : Set X) (h : (D.append C).CentersHaveSNCWith s E) :
    C.CentersHaveSNCWith (D.toBase ≫ s) (D.totalTransform E) := by
  induction D with
  | nil X =>
    change C.CentersHaveSNCWith (𝟙 X ≫ s) E
    rwa [Category.id_comp]
  | cons Z D ih =>
    change C.CentersHaveSNCWith ((D.toBase ≫ blowUpToBase Z) ≫ s)
      (D.totalTransform (totalTransformStep Z E))
    rw [Category.assoc]
    exact ih _ C _ h.2.2

/-- One step of the total transform of a closed set `E` is `π⁻¹(E) ∪ π⁻¹(Z)`. -/
private theorem totalTransformStep_eq {X : Scheme.{u}} (Z : X.IdealSheafData) {E : Set X}
    (hE : IsClosed E) :
    totalTransformStep Z E = blowUpToBase Z ⁻¹' E ∪ blowUpToBase Z ⁻¹' (Z.support : Set X) := by
  unfold totalTransformStep
  apply subset_antisymm
  · refine Set.union_subset_union_left _ ?_
    exact closure_minimal (Set.preimage_mono Set.sdiff_subset)
      (hE.preimage (blowUpToBase Z).continuous)
  · refine Set.union_subset (fun p hp => ?_) Set.subset_union_right
    by_cases hpZ : blowUpToBase Z p ∈ (Z.support : Set X)
    · exact Or.inr hpZ
    · exact Or.inl (subset_closure ⟨hp, hpZ⟩)

/-- The total transform of a closed set `E` is `Π⁻¹(E) ∪ Ex_tot(Π)`. -/
private theorem totalTransform_eq_union {X : Scheme.{u}} (B : ClosedBlowupSequence X) {E : Set X}
    (hE : IsClosed E) : B.totalTransform E = B.toBase ⁻¹' E ∪ B.totalExceptionalSet := by
  induction B with
  | nil X =>
    change E = (𝟙 X : X ⟶ X) ⁻¹' E ∪ ∅
    simp
  | cons Z B ih =>
    change B.totalTransform (totalTransformStep Z E) =
      (B.toBase ≫ blowUpToBase Z) ⁻¹' E ∪
        (B.toBase ⁻¹' (blowUpToBase Z ⁻¹' (Z.support : Set _)) ∪ B.totalExceptionalSet)
    have hcl : IsClosed (totalTransformStep Z E) := by
      rw [totalTransformStep_eq Z hE]
      exact (hE.preimage (blowUpToBase Z).continuous).union
        (Z.support.isClosed.preimage (blowUpToBase Z).continuous)
    rw [ih hcl, totalTransformStep_eq Z hE, Set.preimage_union, Set.union_assoc]
    rfl

/-- The composite of a blow-up sequence of a locally noetherian scheme is proper. -/
private theorem isProper_toBase :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X] (B : ClosedBlowupSequence X), IsProper B.toBase
  | X, _, .nil _ => by
    change IsProper (𝟙 X)
    infer_instance
  | _, _, .cons Z B => by
    have := isProper_blowUpToBase Z
    have : IsLocallyNoetherian (blowUp Z) :=
      LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase Z)
    have := isProper_toBase B
    change IsProper (B.toBase ≫ blowUpToBase Z)
    infer_instance

/-! ### Simple normal crossings at a point -/

/-- Being snc at a point is carried back along a morphism which is an isomorphism on the stalk. -/
private theorem isSNCAt_preimage {Y Y' : Scheme.{u}} (f : Y' ⟶ Y) (y : Y')
    [IsIso (f.stalkMap y)] {T : Set Y} (h : IsSNCAt T (f y)) : IsSNCAt (f ⁻¹' T) y := by
  obtain ⟨n, w, C, hw, hT⟩ := h
  let e : Y.presheaf.stalk (f y) ≃+* Y'.presheaf.stalk y :=
    (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv
  refine ⟨n, fun i => e (w i), C, hw.map_ringEquiv e, ?_⟩
  ext p
  have hp : Y.fromSpecStalk (f y) (Spec.map (f.stalkMap y) p) = f (Y'.fromSpecStalk y p) := by
    rw [← Scheme.Hom.comp_apply, Scheme.SpecMap_stalkMap_fromSpecStalk, Scheme.Hom.comp_apply]
  change f (Y'.fromSpecStalk y p) ∈ T ↔ _
  rw [← hp, ← Set.mem_preimage (f := Y.fromSpecStalk (f y)), hT]
  change p ∈ PrimeSpectrum.comap (f.stalkMap y).hom ⁻¹' (⋃ c ∈ C, PrimeSpectrum.zeroLocus {w c}) ↔
    p ∈ ⋃ c ∈ C, PrimeSpectrum.zeroLocus {e (w c)}
  simp only [Set.preimage_iUnion₂, PrimeSpectrum.preimage_comap_zeroLocus, Set.image_singleton]
  rfl

/-- If at `y` the members of a family of ideal sheaves through `y` are cut out by distinct
members of a regular system of parameters, the union of their supports is snc at `y`. -/
private theorem isSNCAt_iUnion_support {Y : Scheme.{u}} {Λ : Type*}
    (F : Λ → Y.IdealSheafData) (y : Y) {n : ℕ} (w : Fin n → Y.presheaf.stalk y)
    (c : {i // y ∈ (F i).support} → Fin n) (hw : IsRegularSystemOfParameters w)
    (hc : ∀ i, IdealSheafData.stalk (F i.1) y = Ideal.span {w (c i)}) :
    IsSNCAt (⋃ i, ((F i).support : Set Y)) y := by
  classical
  refine ⟨n, w, Finset.univ.filter (fun j => ∃ i, c i = j), hw, ?_⟩
  have hmem : ∀ (i : {i // y ∈ (F i).support}) (p : PrimeSpectrum (Y.presheaf.stalk y)),
      Y.fromSpecStalk y p ∈ ((F i.1).support : Set Y) ↔ p ∈ PrimeSpectrum.zeroLocus {w (c i)} := by
    intro i p
    change p ∈ Y.fromSpecStalk y ⁻¹' ((F i.1).support : Set Y) ↔ _
    rw [preimage_fromSpecStalk_support, hc i, PrimeSpectrum.zeroLocus_span]
    exact Iff.rfl
  ext p
  constructor
  · intro hp
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hp
    have hsp : Y.fromSpecStalk y p ⤳ y := by
      have : Y.fromSpecStalk y p ∈ Set.range (Y.fromSpecStalk y) := ⟨p, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    have hyi : y ∈ (F i).support := hsp.mem_closed (F i).support.isClosed hi
    exact Set.mem_iUnion₂.2
      ⟨c ⟨i, hyi⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, _, rfl⟩, (hmem ⟨i, hyi⟩ p).1 hi⟩
  · intro hp
    obtain ⟨j, hj, hpj⟩ := Set.mem_iUnion₂.1 hp
    obtain ⟨i, rfl⟩ := (Finset.mem_filter.1 hj).2
    exact Set.mem_iUnion.2 ⟨i.1, (hmem i p).2 hpj⟩

/-- **Restriction of an snc divisor along a closed immersion having snc with it.** Let `X` be
smooth and locally of finite type over a perfect field, `E = ∑ᵢ Eⁱ` a simple normal crossing
divisor on `X` with support `T`, and `ι : Y → X` a closed immersion from a quasi-compact scheme
whose image has simple normal crossings with `E`, no `Eⁱ` containing an irreducible component of
the image. Then `ι⁻¹(T)` is a divisor with simple normal crossings on `Y`. -/
private theorem isSNCClosedSubset_preimage_of_hasSNCWith_ker {k : Type u} [Field k]
    [PerfectField k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    (hX : IsSmoothScheme sX) {Λ : Type*} {E : Λ → X.IdealSheafData} (hE : IsSNCFamily sX E)
    {T : Set X} (hT : IsClosed T) (hTE : T = ⋃ i, ((E i).support : Set X))
    (ι : Y ⟶ X) [IsClosedImmersion ι] [CompactSpace Y] (hZ : HasSNCWith E ι.ker)
    (hcomp : ∀ i, ∀ W ∈ componentsOf (ι.ker.support : Set X), ¬ W ⊆ (E i).support)
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] :
    IsSNCClosedSubset sY (ι ⁻¹' T) := by
  obtain ⟨-, hfam⟩ := isSmoothScheme_and_isSNCFamily_comap_subschemeι sX hX hE hZ hcomp
  refine isSNCClosedSubset_of_forall_isSNCAt sY (hT.preimage ι.continuous) fun y => ?_
  obtain ⟨n, w, c, hw, hc, -⟩ := hfam.2 (ι.toImage y)
  have h1 := isSNCAt_iUnion_support (fun i => (E i).comap ι.ker.subschemeι) _ w c hw hc
  have h2 : ι ⁻¹' T = ι.toImage ⁻¹' (⋃ i, (((E i).comap ι.ker.subschemeι).support : Set _)) := by
    conv_lhs => rw [← ι.toImage_imageι]
    simp only [hTE, Scheme.IdealSheafData.support_comap, Set.preimage_iUnion]
    rfl
  rw [h2]
  exact isSNCAt_preimage ι.toImage y h1

/-- Membership in `componentsOf D` is maximality among irreducible subsets of `D`. -/
private theorem maximal_of_mem_componentsOf {T : Type*} [TopologicalSpace T] {D W : Set T}
    (h : W ∈ componentsOf D) : Maximal (fun W' : Set T => IsIrreducible W' ∧ W' ⊆ D) W :=
  h

/-- The ideal of an irreducible component of a closed set `D` cuts out that component. -/
private theorem coe_support_componentsFamily {X : Scheme.{u}} {D : Set X} (hD : IsClosed D)
    (i : componentsOf D) : ((componentsFamily D i).support : Set X) = i.1 := by
  unfold componentsFamily
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure,
    (Aux.isClosed_of_mem_componentsOf hD i.2).closure_eq]

/-- A closed set is the union of its irreducible components, each with its reduced structure. -/
private theorem eq_iUnion_support_componentsFamily {X : Scheme.{u}} {D : Set X}
    (hD : IsClosed D) : D = ⋃ i, ((componentsFamily D i).support : Set X) := by
  ext z
  simp only [Set.mem_iUnion, coe_support_componentsFamily hD]
  refine ⟨fun hz => ?_, fun ⟨i, hi⟩ => (maximal_of_mem_componentsOf i.2).prop.2 hi⟩
  obtain ⟨W, hW, hzW⟩ := exists_mem_componentsOf hz
  exact ⟨⟨W, hW⟩, hzW⟩

/-- If `K` and `Z` agree on an open `U`, their stalks agree at the points of `U`. -/
private theorem stalk_eq_of_comap_eq {X : Scheme.{u}} {K Z : X.IdealSheafData} (U : X.Opens)
    (h : K.comap U.ι = Z.comap U.ι) (x : U.toScheme) :
    IdealSheafData.stalk K (U.ι x) = IdealSheafData.stalk Z (U.ι x) := by
  have h' := congrArg (fun J => IdealSheafData.stalk J x) h
  simp only [IdealSheafData.stalk_comap] at h'
  have hbij : Function.Bijective (U.ι.stalkMap x).hom := ConcreteCategory.bijective_of_isIso _
  rw [← Ideal.comap_map_of_bijective _ hbij (I := IdealSheafData.stalk K _), h',
    Ideal.comap_map_of_bijective _ hbij]

/-- A connected component of a closed subscheme that is normal and noetherian is irreducible. -/
private theorem isIrreducible_connectedComponentIn_support {Y : Scheme.{u}}
    (Z : Y.IdealSheafData) [IsLocallyNoetherian Z.subscheme] [NoetherianSpace Z.subscheme]
    [IsNormal Z.subscheme] {x : Y} (hx : x ∈ (Z.support : Set Y)) :
    IsIrreducible (connectedComponentIn (Z.support : Set Y) x) := by
  have hrange : Set.range Z.subschemeι = (Z.support : Set Y) := by
    rw [Scheme.IdealSheafData.range_subschemeι]
  obtain ⟨z, rfl⟩ : x ∈ Set.range Z.subschemeι := hrange ▸ hx
  have heq : connectedComponentIn (Z.support : Set Y) (Z.subschemeι z) =
      Z.subschemeι '' connectedComponent z := by
    rw [← connectedComponentIn_univ, MMP.Mori.image_connectedComponentIn_of_isEmbedding
      Z.subschemeι.isClosedEmbedding.isEmbedding (Set.mem_univ z), Set.image_univ, hrange]
  rw [heq]
  exact (isIrreducible_connectedComponent_of_isNormal _ z).image _
    Z.subschemeι.continuous.continuousOn

/-- Codimension `≥ 2` of a closed set `S` containing `closure {η}` gives a chain
`closure {η} ⊂ Y₁ ⊂ Y₂` of irreducible closed subsets. -/
private theorem exists_ssubset_ssubset_of_two_le_closedsCodimension {T : Type*}
    [TopologicalSpace T] {S : Closeds T} (hS : 2 ≤ closedsCodimension S) {η : T}
    (hη : closure {η} ⊆ (S : Set T)) :
    ∃ Y₁ Y₂ : IrreducibleCloseds T, closure {η} ⊂ (Y₁ : Set T) ∧ (Y₁ : Set T) ⊂ Y₂ := by
  let Y : IrreducibleCloseds T := ⟨closure {η}, isIrreducible_singleton.closure, isClosed_closure⟩
  obtain ⟨p, hhead, hlen⟩ := (codimension_iff_exists_chain Y 2).1
    (by simpa using le_closedsCodimension_iff.mp hS Y hη)
  refine ⟨p ⟨1, by omega⟩, p ⟨2, by omega⟩, ?_, p.strictMono (by simp [Fin.lt_def])⟩
  change Y < p ⟨1, by omega⟩
  rw [← hhead]
  exact p.strictMono (by simp [Fin.lt_def])

/-- The centres of `𝓑𝓟^can(P, I, ∅)` lie over the support of `I`. -/
private theorem centersLieOver_support_canonicalPrincipalization {k : Type u} [Field k]
    {P : Scheme.{u}} (sP : P ⟶ Spec (.of k)) (I : P.IdealSheafData)
    (ht : (⟨⟨P, I, OrderedDivisor.empty P⟩, k, sP⟩ : FieldBlowupTriple.{u}) ∈ triples) :
    (canonicalPrincipalization _ (triples_subset_sncTriples ht)).CentersLieOver (𝟙 P)
      (I.support : Set P) := by
  obtain ⟨-, -, h3, -⟩ := canonicalPrincipalization_properties.{u, u, u}
  refine (h3 _ ht fun W hW => ?_).1
  obtain ⟨x, hx⟩ := hW.1.1.nonempty
  obtain ⟨i, -⟩ := Set.mem_iUnion.1 (hW.1.2 hx)
  exact i.elim0

/-- The pull-back of `I` along `𝓑𝓟^can(P, I, ∅)` is locally principal. -/
private theorem isLocallyPrincipal_comap_toBase_canonicalPrincipalization {k : Type u}
    [Field k] {P : Scheme.{u}} (sP : P ⟶ Spec (.of k)) (I : P.IdealSheafData)
    (ht : (⟨⟨P, I, OrderedDivisor.empty P⟩, k, sP⟩ : FieldBlowupTriple.{u}) ∈ triples)
    [IsLocallyNoetherian (canonicalPrincipalization _ (triples_subset_sncTriples ht)).target] :
    Stacks.Divisors.IsLocallyPrincipal
      (I.comap (canonicalPrincipalization _ (triples_subset_sncTriples ht)).toBase) := by
  obtain ⟨-, h2, -, -⟩ := canonicalPrincipalization_properties.{u, u, u}
  refine Stacks.Divisors.isLocallyPrincipal_of_stalk_isPrincipal _ fun x _ => ?_
  obtain ⟨n, z, c, -, hx⟩ := h2 _ ht x
  rw [hx]
  exact ⟨_, rfl⟩

/-- A morphism from a nonempty scheme onto a connected component of a closed subscheme smooth
over a field, in a noetherian space, has irreducible image. -/
private theorem isIrreducible_range_of_eq_connectedComponentIn {k : Type u} [Field k]
    {Y W : Scheme.{u}} [NoetherianSpace Y] (t : Y ⟶ Spec (.of k)) (Z : Y.IdealSheafData)
    (hZ : IsSmoothScheme (Z.subschemeι ≫ t)) (ι : W ⟶ Y) {x₀ : Y}
    (hrange : Set.range ι = connectedComponentIn (Z.support : Set Y) x₀) (w : W) :
    IsIrreducible (Set.range ι) := by
  have : Smooth (Z.subschemeι ≫ t) := IsSmoothScheme.smooth hZ
  have : IsLocallyNoetherian Z.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (Z.subschemeι ≫ t)
  have : NoetherianSpace Z.subscheme :=
    Z.subschemeι.isClosedEmbedding.isEmbedding.noetherianSpace
  have : IsNormal Z.subscheme := isNormal_of_smooth_over_field (Z.subschemeι ≫ t)
  have hx₀ : x₀ ∈ (Z.support : Set Y) := by
    by_contra h
    have h' : ι w ∈ connectedComponentIn (Z.support : Set Y) x₀ := hrange ▸ ⟨w, rfl⟩
    rw [connectedComponentIn_eq_empty h] at h'
    exact h'
  exact hrange ▸ isIrreducible_connectedComponentIn_support Z hx₀

/-- Let `T` be a blow-up sequence of `P` whose target is smooth over `k`, with `Ex_tot(Π)` an snc
divisor having snc with a smooth centre `Z`. If the closed immersion `T.restrictHom C` maps onto
a connected component of `Z`, agreeing with `Z` near its image, and some point of `C_T` maps off
`Ex_tot(Π)`, then the trace of `Ex_tot(Π)` on `C_T` is an snc divisor. -/
private theorem isSNCClosedSubset_restrictHom_preimage_of_eq_connectedComponentIn
    {k : Type u} [Field k] [CharZero k] {P : Scheme.{u}} (sP : P ⟶ Spec (.of k))
    [QuasiCompact sP] [IsLocallyNoetherian P] (T : ClosedBlowupSequence P)
    (C : P.IdealSheafData) [IsClosedImmersion (T.restrictHom C)] (Z : T.target.IdealSheafData)
    (hsmT : IsSmoothScheme (T.toBase ≫ sP))
    (hsmZ : IsSmoothScheme (Z.subschemeι ≫ T.toBase ≫ sP))
    (hDsnc : IsSNCClosedSubset (T.toBase ≫ sP) T.totalExceptionalSet)
    (hZsnc : HasSNCWith (componentsFamily T.totalExceptionalSet) Z) {x₀ : T.target}
    (hrange : Set.range (T.restrictHom C) = connectedComponentIn (Z.support : Set _) x₀)
    (U : T.target.Opens) (hιU : Set.range (T.restrictHom C) ⊆ U)
    (hker : (T.restrictHom C).ker.comap U.ι = Z.comap U.ι) (q : (T.restrict C).target)
    (hq : T.restrictHom C q ∉ T.totalExceptionalSet) :
    IsSNCClosedSubset ((T.restrict C).toBase ≫ C.subschemeι ≫ sP)
      (T.restrictHom C ⁻¹' T.totalExceptionalSet) := by
  set ι := T.restrictHom C
  have : Smooth (T.toBase ≫ sP) := IsSmoothScheme.smooth hsmT
  have : IsLocallyNoetherian T.target := LocallyOfFiniteType.isLocallyNoetherian (T.toBase ≫ sP)
  have : IsProper T.toBase := isProper_toBase T
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace sP
  have : CompactSpace T.target := QuasiCompact.compactSpace_of_compactSpace T.toBase
  have : CompactSpace (T.restrict C).target := QuasiCompact.compactSpace_of_compactSpace ι
  have : IsNoetherian T.target := {}
  have hirr := isIrreducible_range_of_eq_connectedComponentIn (T.toBase ≫ sP) Z hsmZ ι hrange q
  have hsuppK : (ι.ker.support : Set _) = Set.range ι := by
    rw [Scheme.Hom.support_ker, ι.isClosedEmbedding.isClosed_range.closure_eq]
  have hKsnc : HasSNCWith (componentsFamily T.totalExceptionalSet) ι.ker := fun z hz => by
    rw [hsuppK] at hz
    have hzZ : z ∈ (Z.support : Set _) := connectedComponentIn_subset _ _ (hrange ▸ hz)
    obtain ⟨n, w, c, J, hw, hc, hinj, hZz⟩ := hZsnc z hzZ
    exact ⟨n, w, c, J, hw, hc, hinj, (stalk_eq_of_comap_eq U hker ⟨z, hιU hz⟩).trans hZz⟩
  have hcomp : ∀ i, ∀ W ∈ componentsOf (ι.ker.support : Set _),
      ¬ W ⊆ ((componentsFamily T.totalExceptionalSet i).support : Set T.target) := by
    intro i W hW hWi
    rw [hsuppK] at hW
    have hW' := maximal_of_mem_componentsOf hW
    have hWr : Set.range ι ⊆ W := hW'.2 ⟨hirr, subset_rfl⟩ hW'.prop.2
    have h := hWi (hWr ⟨q, rfl⟩)
    rw [coe_support_componentsFamily (isClosed_totalExceptionalSet _)] at h
    exact hq ((maximal_of_mem_componentsOf i.2).prop.2 h)
  rcases hDsnc with ⟨-, hD0 | ⟨-, -, hDfam⟩⟩
  · rw [hD0, Set.preimage_empty]
    exact ⟨isClosed_empty, Or.inl rfl⟩
  · have hc : (T.restrict C).toBase ≫ C.subschemeι = ι ≫ T.toBase :=
      (Kollar.pullbackHom_toBase_comm _ _).symm
    have : LocallyOfFiniteType ((T.restrict C).toBase ≫ C.subschemeι ≫ sP) := by
      rw [← Category.assoc, hc, Category.assoc]
      infer_instance
    exact isSNCClosedSubset_preimage_of_hasSNCWith_ker (T.toBase ≫ sP) hsmT hDfam
      (isClosed_totalExceptionalSet _)
      (eq_iUnion_support_componentsFamily (isClosed_totalExceptionalSet _)) ι hKsnc hcomp _

end Proof_lem_kr3f_sing_preimage_snc

namespace MMP.Resolution

open Proof_lem_kr3f_sing_preimage_snc
open ClosedBlowupSequence

/-- **Kollár, p. 140.** Let `P` be a smooth equidimensional scheme of finite type over a field
`k` of characteristic `0`, and `X = I.subscheme ⊆ P` a closed subscheme all of whose
irreducible components have codimension `≥ 2`. Let `𝐁 = 𝓑𝓟^can(P, I, ∅)`
(`MMP.Resolution.canonicalPrincipalization`), let `η` be the generic point of an irreducible
component `C` of `X`, `j = 𝐁.entryIndex η`, and `C_j` the last scheme of the restriction
`(𝐁.truncate j).restrict C`, with structure map `C_j → C → P → Spec k`. Suppose `x` is a point of
`C` at which `X` is smooth. Then `C_j ∩ Ex_tot(Π_j)`, the preimage of
`(𝐁.truncate j).totalExceptionalSet` under `(𝐁.truncate j).restrictHom C`, is a divisor
with simple normal crossings on `C_j`. -/
@[mmp "lem_kr3f_sing_preimage_snc"]
public theorem isSNCClosedSubset_restrictHom_preimage_totalExceptionalSet_canonicalPrincipalization
    {k : Type u} [Field k] [CharZero k] {P : Scheme.{u}} (sP : P ⟶ Spec (.of k))
    (hsm : IsSmoothScheme sP) [QuasiCompact sP] (heq : Equidimensional P)
    (I : P.IdealSheafData)
    (hcodim : 2 ≤ closedsCodimension I.support)
    (η : P) (hη : closure {η} ∈ componentsOf (I.support : Set P))
    (x : I.subscheme) (hx : x ∈ smoothLocus (I.subschemeι ≫ sP))
    (hxC : I.subschemeι.base x ∈ closure {η}) :
    ∃ ht : (⟨⟨P, I, OrderedDivisor.empty P⟩, k, sP⟩ : FieldBlowupTriple.{u}) ∈ triples,
      let B := canonicalPrincipalization _ (triples_subset_sncTriples ht)
      let C : P.IdealSheafData :=
        Scheme.IdealSheafData.vanishingIdeal ⟨closure {η}, isClosed_closure⟩
      let Bj := B.truncate (B.entryIndex η)
      IsSNCClosedSubset ((Bj.restrict C).toBase ≫ C.subschemeι ≫ sP)
        (Bj.restrictHom C ⁻¹' Bj.totalExceptionalSet) := by
  obtain ⟨ht, V, y, hy, hyV, hiso⟩ :=
    exists_isIso_morphismRestrict_toBase_restrict_canonicalPrincipalization sP hsm heq I
      hcodim η hη x hx hxC
  obtain ⟨ht', V', y', hy', hyV', hdisj⟩ :=
    exists_disjoint_preimage_totalExceptionalSet_truncate_canonicalPrincipalization sP hsm heq I
      hcodim η hη x hx hxC
  have hη' := maximal_of_mem_componentsOf hη
  refine ⟨ht, ?_⟩
  intro B C Bj
  have : Smooth sP := IsSmoothScheme.smooth hsm
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian sP
  obtain ⟨h1, -, -, -⟩ := canonicalPrincipalization_properties.{u, u, u}
  obtain ⟨hBsm, hBsnc⟩ := h1 _ ht
  have hE0 : (OrderedDivisor.empty P).support = ∅ := by
    simp [OrderedDivisor.support, OrderedDivisor.empty]
  have : IsProper B.toBase := isProper_toBase B
  have : IsLocallyNoetherian B.target := LocallyOfFiniteType.isLocallyNoetherian B.toBase
  obtain ⟨-, Z, B', hsplit, ⟨x₀, hrange⟩, U, hιU, hker⟩ :=
    restrict_truncate_entryIndex_isConnectedComponent sP hsm I hη'
      (exists_ssubset_ssubset_of_two_le_closedsCodimension hcodim hη'.prop.2) B hBsm
      (isLocallyPrincipal_comap_toBase_canonicalPrincipalization sP I ht)
      (centersLieOver_support_canonicalPrincipalization sP I ht)
  have hBsm2 : ((B.truncate (B.entryIndex η)).append (cons Z B')).IsSmooth sP := hsplit ▸ hBsm
  have hBsnc2 : ((B.truncate (B.entryIndex η)).append (cons Z B')).CentersHaveSNCWith sP
      (OrderedDivisor.empty P).support := hsplit ▸ hBsnc
  obtain ⟨hsmj, hsmZ, -⟩ := isSmooth_of_isSmooth_append sP _ _ hBsm2
  obtain ⟨hDsnc, hZsnc, -⟩ := centersHaveSNCWith_of_append sP _ _ _ hBsnc2
  have hD : Bj.totalTransform (OrderedDivisor.empty P).support = Bj.totalExceptionalSet := by
    rw [hE0, totalTransform_eq_union _ isClosed_empty, Set.preimage_empty, Set.empty_union]
  change IsSNCClosedSubset (Bj.toBase ≫ sP) (Bj.totalTransform _) at hDsnc
  change HasSNCWith (componentsFamily (Bj.totalTransform _)) Z at hZsnc
  rw [hD] at hDsnc hZsnc
  have : IsClosedImmersion (Bj.restrictHom C) := Kollar.isClosedImmersion_restrictHom_truncate B C _
  set g := (Bj.restrict C).toBase
  have hyy' : y' = y := C.subschemeι.isClosedEmbedding.injective (hy'.trans hy.symm)
  obtain ⟨q, hq⟩ := (g ∣_ V).homeomorph.surjective ⟨y, hyV⟩
  have hgq : g q.1 = y := by
    rw [← morphismRestrict_base_coe]
    exact congrArg Subtype.val hq
  refine isSNCClosedSubset_restrictHom_preimage_of_eq_connectedComponentIn sP Bj C Z hsmj hsmZ
    hDsnc hZsnc hrange U hιU hker q.1 fun h => ?_
  refine Set.disjoint_left.1 hdisj (show g q.1 ∈ (V' : Set C.subscheme) from ?_) h
  rw [hgq, ← hyy']
  exact hyV'

end MMP.Resolution

namespace Proof_lem_kr3f_strong_resolution_sing_preimage

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori MMP.Resolution

/-- Smoothness at a point is preserved and reflected by an open immersion. -/
private theorem mem_smoothLocus_comp_iff {A B S : Scheme.{u}} (e : A ⟶ B) [IsOpenImmersion e]
    (s : B ⟶ S) (a : A) : a ∈ smoothLocus (e ≫ s) ↔ e a ∈ smoothLocus s := by
  simp only [mem_smoothLocus_iff]
  constructor
  · rintro ⟨U, haU, hU⟩
    refine ⟨e ''ᵁ U, ⟨a, haU, rfl⟩, ?_⟩
    have h : (e ''ᵁ U).ι = inv (e.isoImage U).hom ≫ U.ι ≫ e := by
      rw [← Scheme.Hom.isoImage_hom_ι, IsIso.inv_hom_id_assoc]
    rw [h, Category.assoc, Category.assoc]
    infer_instance
  · rintro ⟨V, haV, hV⟩
    refine ⟨e ⁻¹ᵁ V, haV, ?_⟩
    rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    infer_instance

/-- If `t` is an open immersion near `q` and `b` is an isomorphism over an open `V` containing
the image of `q`, then `t ≫ b` is an open immersion near `q`. -/
private theorem exists_isOpenImmersion_comp {M N L : Scheme.{u}} (t : M ⟶ N) (b : N ⟶ L)
    (V : L.Opens) [IsIso (b ∣_ V)] (q : M) (W' : M.Opens) (hqW' : q ∈ W')
    [IsOpenImmersion (W'.ι ≫ t)] (hqV : b (t q) ∈ V) :
    ∃ W : M.Opens, q ∈ W ∧ IsOpenImmersion (W.ι ≫ t ≫ b) := by
  let W : M.Opens := W' ⊓ t ⁻¹ᵁ (b ⁻¹ᵁ V)
  refine ⟨W, ⟨hqW', hqV⟩, ?_⟩
  have hle : W ≤ W' := inf_le_left
  have hWW : IsOpenImmersion (W.ι ≫ t) := by
    rw [← Scheme.homOfLE_ι _ hle, Category.assoc]
    infer_instance
  have hr : Set.range (W.ι ≫ t) ⊆ Set.range (b ⁻¹ᵁ V).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact w.2.2
  have hψ : IsOpenImmersion (IsOpenImmersion.lift (b ⁻¹ᵁ V).ι (W.ι ≫ t) hr) := by
    have : IsOpenImmersion (IsOpenImmersion.lift (b ⁻¹ᵁ V).ι (W.ι ≫ t) hr ≫ (b ⁻¹ᵁ V).ι) := by
      rwa [IsOpenImmersion.lift_fac]
    exact IsOpenImmersion.of_comp _ (b ⁻¹ᵁ V).ι
  rw [← Category.assoc, ← IsOpenImmersion.lift_fac (b ⁻¹ᵁ V).ι (W.ι ≫ t) hr, Category.assoc,
    ← morphismRestrict_ι]
  infer_instance

/-- Off the total exceptional set of `𝐁`, the composite of a pull-back `h^*𝐁` is an open
immersion near the point. -/
private theorem exists_isOpenImmersion_of_notMem_totalExceptionalSet {X : Scheme.{u}} :
    ∀ (B : ClosedBlowupSequence X) {Y : Scheme.{u}} (h : Y ⟶ X) (q : (B.pullback h).target),
      (B.pullbackHom h) q ∉ B.totalExceptionalSet →
        ∃ W : (B.pullback h).target.Opens, q ∈ W ∧
          IsOpenImmersion (W.ι ≫ (B.pullback h).toBase) := by
  intro B
  induction B with
  | nil X =>
    intro Y h q _
    refine ⟨⊤, trivial, ?_⟩
    change IsOpenImmersion ((⊤ : Y.Opens).ι ≫ 𝟙 Y)
    infer_instance
  | @cons X Z B ih =>
    intro Y h
    change ∀ q : (B.pullback (canonicalLift h Z)).target,
      B.pullbackHom (canonicalLift h Z) q ∉
        B.toBase ⁻¹' (blowUpToBase Z ⁻¹' (Z.support : Set _)) ∪ B.totalExceptionalSet →
      ∃ W : (B.pullback (canonicalLift h Z)).target.Opens, q ∈ W ∧
        IsOpenImmersion (W.ι ≫ (B.pullback (canonicalLift h Z)).toBase ≫
          blowUpToBase (Z.comap h))
    intro q hq
    rw [Set.mem_union, not_or] at hq
    obtain ⟨W', hqW', hW'⟩ := ih (canonicalLift h Z) q hq.2
    have := isIso_blowUp_restrict_compl_support (Z.comap h)
    refine exists_isOpenImmersion_comp _ _ ⟨_, (Z.comap h).support.isClosed.isOpen_compl⟩ q W'
      hqW' ?_
    change blowUpToBase (Z.comap h) ((B.pullback (canonicalLift h Z)).toBase q) ∉
      ((Z.comap h).support : Set _)
    rw [Scheme.IdealSheafData.support_comap]
    have e1 : blowUpToBase Z (canonicalLift h Z ((B.pullback (canonicalLift h Z)).toBase q)) =
        h (blowUpToBase (Z.comap h) ((B.pullback (canonicalLift h Z)).toBase q)) := by
      rw [← Scheme.Hom.comp_apply, canonicalLift_comp_blowUpToBase, Scheme.Hom.comp_apply]
    have e2 : B.toBase (B.pullbackHom (canonicalLift h Z) q) =
        canonicalLift h Z ((B.pullback (canonicalLift h Z)).toBase q) := by
      rw [← Scheme.Hom.comp_apply, Kollar.pullbackHom_toBase_comm, Scheme.Hom.comp_apply]
    change h _ ∉ (Z.support : Set _)
    rw [← e1, ← e2]
    exact hq.1

/-- A closed subscheme `W` whose ideal agrees, on an open `U` containing its support, with the
ideal of a closed subscheme `Z` smooth over `T`, is itself smooth over `T`. -/
private theorem smooth_subschemeι_of_comap_eq {Y T : Scheme.{u}} (t : Y ⟶ T)
    (W Z : Y.IdealSheafData) (U : Y.Opens) (hWU : (W.support : Set Y) ⊆ U)
    (h : W.comap U.ι = Z.comap U.ι) (hZ : Smooth (Z.subschemeι ≫ t)) :
    Smooth (W.subschemeι ≫ t) := by
  have key : ∀ V : U.toScheme.IdealSheafData, V = Z.comap U.ι →
      Smooth (V.subschemeι ≫ U.ι ≫ t) := by
    rintro _ rfl
    have e : (Z.comap U.ι).subschemeι ≫ U.ι ≫ t =
        ((Z.comapIso U.ι).hom ≫ Limits.pullback.snd U.ι Z.subschemeι) ≫ Z.subschemeι ≫ t := by
      rw [← Z.comapIso_hom_fst U.ι, Category.assoc, Category.assoc, ← Category.assoc _ U.ι,
        Limits.pullback.condition, Category.assoc]
    rw [e]
    infer_instance
  have hW := key _ h
  have hsnd : IsIso (Limits.pullback.snd U.ι W.subschemeι) := by
    refine (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, ⟨fun x => ?_⟩⟩
    have hx : W.subschemeι x ∈ U := hWU (by
      rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨x, rfl⟩)
    change x ∈ Set.range (Limits.pullback.snd U.ι W.subschemeι)
    rw [IsOpenImmersion.range_pullbackSnd]
    simpa using hx
  have e : W.subschemeι ≫ t = inv (Limits.pullback.snd U.ι W.subschemeι) ≫
      ((W.comapIso U.ι).inv ≫ (W.comap U.ι).subschemeι ≫ U.ι ≫ t) := by
    rw [← W.comapIso_hom_fst U.ι]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [Limits.pullback.condition_assoc, IsIso.inv_hom_id_assoc]
  rw [e]
  infer_instance

/-- If the closed subscheme `T.restrictHom C` of `T.target` agrees, on an open `U` containing
it, with a closed subscheme `Z` smooth over `T.toBase ≫ t`, then the restricted composite is
smooth over `t`. -/
private theorem smooth_restrict_toBase_comp {X S : Scheme.{u}} (t : X ⟶ S)
    (T : ClosedBlowupSequence X) (C : X.IdealSheafData) [IsClosedImmersion (T.restrictHom C)]
    (Z : T.target.IdealSheafData) (U : T.target.Opens)
    (hιU : Set.range (T.restrictHom C) ⊆ U)
    (hker : (T.restrictHom C).ker.comap U.ι = Z.comap U.ι)
    (hZ : Smooth (Z.subschemeι ≫ T.toBase ≫ t)) :
    Smooth ((T.restrict C).toBase ≫ C.subschemeι ≫ t) := by
  have hW := smooth_subschemeι_of_comap_eq _ _ Z U (by
    rwa [Scheme.Hom.support_ker, (T.restrictHom C).isClosedEmbedding.isClosed_range.closure_eq])
    hker hZ
  have hc : (T.restrict C).toBase ≫ C.subschemeι = T.restrictHom C ≫ T.toBase :=
    (Kollar.pullbackHom_toBase_comm _ _).symm
  rw [← Category.assoc, hc, ← Scheme.Hom.toImage_imageι (T.restrictHom C)]
  simp only [Category.assoc]
  infer_instance

/-- An empty family on a smooth scheme over a field is a simple normal crossing family. -/
private theorem isSNCFamily_of_isEmpty {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) [Smooth f] {Λ : Type*} [IsEmpty Λ] (E : Λ → Y.IdealSheafData) :
    IsSNCFamily f E := by
  refine ⟨isEmptyElim, fun x => ?_⟩
  have := isRegularLocalRing_stalk_of_smooth_over_field f x
  obtain ⟨n, z, hz⟩ := MMP.Mori.exists_isRegularSystemOfParameters (Y.presheaf.stalk x)
  exact ⟨n, z, fun i => isEmptyElim i.1, hz, fun i => isEmptyElim i.1, fun i => isEmptyElim i.1⟩

/-- An irreducible component of `T` does not lie in a closed set all of whose irreducible closed
subsets have codimension `≥ 1`. -/
private theorem notMem_of_mem_irreducibleComponents {T : Type*} [TopologicalSpace T]
    {S : Closeds T} (hS : 1 ≤ closedsCodimension S) {ξ : T}
    (hξ : closure {ξ} ∈ irreducibleComponents T) : ξ ∉ (S : Set T) := by
  intro hξS
  let Y : IrreducibleCloseds T := ⟨closure {ξ}, hξ.1, isClosed_closure⟩
  have hYS : (Y : Set T) ⊆ S := closure_minimal (Set.singleton_subset_iff.2 hξS) S.isClosed
  obtain ⟨p, hhead, hlen⟩ := (codimension_iff_exists_chain Y 1).1
    (by simpa using le_closedsCodimension_iff.mp hS Y hYS)
  have hlt : Y < p.last := by
    rw [← hhead]
    exact p.strictMono (by rw [Fin.lt_def]; simp [hlen])
  have hle : closure {ξ} ⊆ (p.last : Set T) := hlt.le
  exact hlt.not_ge (hξ.2 p.last.isIrreducible hle)

/-- In a noetherian space, a set `K` disjoint from every irreducible component of a closed set `D`
other than itself has an open neighbourhood `U` with `D ∩ U ⊆ K`. -/
private theorem exists_isOpen_inter_subset_of_disjoint {T : Type*} [TopologicalSpace T]
    [NoetherianSpace T] {D K : Set T} (hD : IsClosed D)
    (hconn : ∀ Z ∈ componentsOf D, Z ≠ K → Disjoint Z K) :
    ∃ U : Set T, IsOpen U ∧ K ⊆ U ∧ D ∩ U ⊆ K := by
  have hS : componentsOf D \ {K} ⊆ componentsOf D := Set.sdiff_subset
  refine ⟨(⋃₀ (componentsOf D \ {K}))ᶜ, (((Aux.finite_and_cover_componentsOf hD).1.subset
    hS).isClosed_sUnion fun W hW => Aux.isClosed_of_mem_componentsOf hD (hS hW)).isOpen_compl,
    ?_, ?_⟩
  · rintro p hp ⟨W, ⟨hW, hWK⟩, hpW⟩
    exact Set.disjoint_left.1 (hconn W hW hWK) hpW hp
  · rintro z ⟨hz, hzU⟩
    obtain ⟨W, hW, hzW⟩ := Set.mem_sUnion.1 ((Aux.finite_and_cover_componentsOf hD).2 hz)
    by_contra hzK
    exact hzU ⟨W, ⟨hW, fun h => hzK (h ▸ hzW)⟩, hzW⟩

/-- Let `I ≤ C` be ideal sheaves with `I.subscheme` reduced, and `U` an open containing the
support of `C` on which the support of `I` lies in that of `C`. Then the inclusion
`C.subscheme ⟶ I.subscheme` maps smooth points over `s` to smooth points over `s`. -/
private theorem inclusion_mem_smoothLocus {Y S : Scheme.{u}} (s : Y ⟶ S)
    {I C : Y.IdealSheafData} (hle : I ≤ C) [IsReduced I.subscheme] (U : Y.Opens)
    (hCU : (C.support : Set Y) ⊆ U) (hIU : (I.support : Set Y) ∩ U ⊆ C.support)
    {c : C.subscheme} (hc : c ∈ smoothLocus (C.subschemeι ≫ s)) :
    Scheme.IdealSheafData.inclusion hle c ∈ smoothLocus (I.subschemeι ≫ s) := by
  let incl := Scheme.IdealSheafData.inclusion hle
  have hincl : incl ≫ I.subschemeι = C.subschemeι :=
    Scheme.IdealSheafData.inclusion_subschemeι hle
  have hmemC : ∀ c : C.subscheme, C.subschemeι c ∈ (C.support : Set Y) := fun c => by
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨c, rfl⟩
  let O : I.subscheme.Opens := I.subschemeι ⁻¹ᵁ U
  have : IsReduced O.toScheme := isReduced_of_isOpenImmersion O.ι
  have : Surjective (incl ∣_ O) := by
    refine ⟨fun y => ?_⟩
    have hyI : I.subschemeι y.1 ∈ (I.support : Set Y) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨y.1, rfl⟩
    obtain ⟨c, hc⟩ : I.subschemeι y.1 ∈ Set.range C.subschemeι := by
      rw [Scheme.IdealSheafData.range_subschemeι]
      exact hIU ⟨hyI, y.2⟩
    have hcy : incl c = y.1 := by
      apply I.subschemeι.isClosedEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hincl, hc]
    exact ⟨⟨c, show incl c ∈ O from hcy ▸ y.2⟩,
      Subtype.ext ((morphismRestrict_base_coe incl O _).trans hcy)⟩
  have : IsIso (incl ∣_ O) := isIso_of_isClosedImmersion_of_surjective _
  have hcO : c ∈ incl ⁻¹ᵁ O := by
    change I.subschemeι (incl c) ∈ U
    rw [← Scheme.Hom.comp_apply, hincl]
    exact hCU (hmemC c)
  let c₀ : (incl ⁻¹ᵁ O).toScheme := ⟨c, hcO⟩
  have h1 := (mem_smoothLocus_comp_iff (incl ⁻¹ᵁ O).ι (C.subschemeι ≫ s) c₀).2 hc
  have : IsOpenImmersion ((incl ⁻¹ᵁ O).ι ≫ incl) := by
    rw [← morphismRestrict_ι]; infer_instance
  rwa [show (incl ⁻¹ᵁ O).ι ≫ C.subschemeι ≫ s = ((incl ⁻¹ᵁ O).ι ≫ incl) ≫ I.subschemeι ≫ s by
    rw [← hincl]; simp only [Category.assoc], mem_smoothLocus_comp_iff] at h1

/-- `(P, I, ∅)` is a triple when `P` is smooth equidimensional of finite type over a field of
characteristic `0` and `I` has codimension `≥ 2`. -/
private theorem mem_triples_of_two_le_closedsCodimension {k : Type u} [Field k] [CharZero k]
    {P : Scheme.{u}} (sP : P ⟶ Spec (.of k)) (hsm : IsSmoothScheme sP) [QuasiCompact sP]
    (heq : Equidimensional P) (I : P.IdealSheafData) (hcodim : 2 ≤ closedsCodimension I.support) :
    (⟨⟨P, I, OrderedDivisor.empty P⟩, k, sP⟩ : FieldBlowupTriple.{u}) ∈ triples := by
  have : Smooth sP := IsSmoothScheme.smooth hsm
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian sP
  refine ⟨‹CharZero k›, hsm, inferInstance, inferInstance, heq, fun ξ hξ hst => ?_,
    ⟨fun i => i.elim0, @isSNCFamily_of_isEmpty _ _ _ sP _ (Fin 0) inferInstance _⟩⟩
  refine notMem_of_mem_irreducibleComponents (le_trans (by norm_num) hcodim) hξ ?_
  by_contra hξI
  have htop := (IdealSheafData.stalk_eq_top_iff_notMem_support I ξ).2 hξI
  rw [hst] at htop
  exact bot_ne_top htop

end Proof_lem_kr3f_strong_resolution_sing_preimage

namespace MMP.Resolution

open Proof_lem_kr3f_sing_preimage_snc Proof_lem_kr3f_strong_resolution_sing_preimage

/-- **Kollár, p. 140.** Let `P` be a smooth equidimensional scheme of finite type over a field
`k` of characteristic `0`, and `X = I.subscheme ⊆ P` a reduced closed subscheme all of whose
irreducible components have codimension `≥ 2`. Let `𝐁 = 𝓑𝓟^can(P, I, ∅)`
(`MMP.Resolution.canonicalPrincipalization`), let `η` be the generic point of an irreducible
component `C` of `X` meeting no other irreducible component of `X`, `j = 𝐁.entryIndex η`, and
`g : C_j → C` the composite of the restriction `(𝐁.truncate j).restrict C`. Then
`g⁻¹(Sing C) = C_j ∩ Ex_tot(Π_j)`: a point of `C_j` lies over the singular locus of `C` exactly
when its image in `P_j` lies in the total exceptional set of the first `j` blow-ups. -/
@[mmp "lem_kr3f_strong_resolution_sing_preimage"]
public theorem preimage_singularLocus_toBase_restrict_canonicalPrincipalization
    {k : Type u} [Field k] [CharZero k] {P : Scheme.{u}} (sP : P ⟶ Spec (.of k))
    (hsm : IsSmoothScheme sP) [QuasiCompact sP] (heq : Equidimensional P)
    (I : P.IdealSheafData) (hred : IsReduced I.subscheme)
    (hcodim : 2 ≤ closedsCodimension I.support)
    (η : P) (hη : closure {η} ∈ componentsOf (I.support : Set P))
    (hconn : ∀ Z ∈ componentsOf (I.support : Set P), Z ≠ closure {η} →
      Disjoint Z (closure {η})) :
    ∃ ht : (⟨⟨P, I, OrderedDivisor.empty P⟩, k, sP⟩ : FieldBlowupTriple.{u}) ∈ triples,
      let B := canonicalPrincipalization _ (triples_subset_sncTriples ht)
      let C : P.IdealSheafData :=
        Scheme.IdealSheafData.vanishingIdeal ⟨closure {η}, isClosed_closure⟩
      let Bj := B.truncate (B.entryIndex η)
      (Bj.restrict C).toBase.base ⁻¹' (singularLocus (C.subschemeι ≫ sP) : Set C.subscheme) =
        (Bj.restrictHom C).base ⁻¹' Bj.totalExceptionalSet := by
  have : Smooth sP := IsSmoothScheme.smooth hsm
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian sP
  have hηmax := maximal_of_mem_componentsOf hη
  have ht := mem_triples_of_two_le_closedsCodimension sP hsm heq I hcodim
  refine ⟨ht, ?_⟩
  intro B C Bj
  have hBsm : B.IsSmooth sP := (canonicalPrincipalization_properties.{u, u, u}.1 _ ht).1
  have : IsProper B.toBase := isProper_toBase B
  have : IsLocallyNoetherian B.target := LocallyOfFiniteType.isLocallyNoetherian B.toBase
  obtain ⟨-, Z, B', hBeq, -, U, hιU, hker⟩ :=
    ClosedBlowupSequence.restrict_truncate_entryIndex_isConnectedComponent sP hsm I hηmax
      (exists_ssubset_ssubset_of_two_le_closedsCodimension hcodim hηmax.prop.2) B hBsm
      (isLocallyPrincipal_comap_toBase_canonicalPrincipalization sP I ht)
      (centersLieOver_support_canonicalPrincipalization sP I ht)
  have hCj : Smooth ((Bj.restrict C).toBase ≫ C.subschemeι ≫ sP) := by
    have hB' : (Bj.append (.cons Z B')).IsSmooth sP := hBeq ▸ hBsm
    have := Kollar.isClosedImmersion_restrictHom_truncate B C (B.entryIndex η)
    exact smooth_restrict_toBase_comp sP _ C Z U hιU hker
      (IsSmoothScheme.smooth (isSmooth_of_isSmooth_append sP _ _ hB').2.1)
  have hCsupp : (C.support : Set P) = closure {η} := by
    simp [C, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hle : I ≤ C := Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp hηmax.prop.2
  have hincl := Scheme.IdealSheafData.inclusion_subschemeι hle
  ext q
  constructor
  · intro hq
    by_contra hE
    obtain ⟨W, hqW, hW⟩ : ∃ W : (Bj.restrict C).target.Opens, q ∈ W ∧
        IsOpenImmersion (W.ι ≫ (Bj.restrict C).toBase) :=
      exists_isOpenImmersion_of_notMem_totalExceptionalSet Bj C.subschemeι q hE
    refine hq ((mem_smoothLocus_comp_iff (W.ι ≫ (Bj.restrict C).toBase) (C.subschemeι ≫ sP)
      ⟨q, hqW⟩).1 (mem_smoothLocus_iff.2 ⟨⊤, trivial, ?_⟩))
    simp only [Category.assoc]
    infer_instance
  · intro hE hsmC
    have := Aux.noetherianSpace_of_finiteType sP
    obtain ⟨U₀, hU₀, hηU₀, hIU₀⟩ := exists_isOpen_inter_subset_of_disjoint I.support.isClosed hconn
    obtain ⟨V, y, hy, hyV, hdisj⟩ :=
      (exists_disjoint_preimage_totalExceptionalSet_truncate_canonicalPrincipalization sP hsm heq
        I hcodim η hη _ (inclusion_mem_smoothLocus sP hle ⟨U₀, hU₀⟩ (hCsupp ▸ hηU₀)
          (hCsupp ▸ hIU₀) hsmC) (by
          rw [← Scheme.Hom.comp_apply, hincl, ← hCsupp, ← Scheme.IdealSheafData.range_subschemeι]
          exact ⟨_, rfl⟩)).2
    have hyq : y = (Bj.restrict C).toBase q := by
      apply C.subschemeι.isClosedEmbedding.injective
      rw [hy, ← Scheme.Hom.comp_apply, hincl]
    exact Set.disjoint_left.1 hdisj
      (show (Bj.restrict C).toBase q ∈ (V : Set C.subscheme) from hyq ▸ hyV) hE

end MMP.Resolution

end
