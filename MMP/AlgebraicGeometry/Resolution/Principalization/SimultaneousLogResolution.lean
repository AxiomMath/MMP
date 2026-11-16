module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs
import MMP.AlgebraicGeometry.Resolution.Principalization.ResolutionPrincipalization
import MMP.AlgebraicGeometry.Morphisms.ChowLemma
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.MMP.Models
import MMP.AlgebraicGeometry.Divisor.SNC
import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlops
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Singularities.Snc.Basic
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Divisor.EffectiveCartierCoheight

/-!
# Simultaneous principalization and projective log resolutions

Let `X` be a normal variety over a field `k` of characteristic zero and `Δ` a boundary on `X`.
This file proves that finitely many nonzero ideal sheaves `I_j` on `X` are principalized by one
projective log resolution `g : Y ⟶ X` of `(X, Δ)`, with the exceptional divisors, the strict
transform of `Δ` and the supports of the `I_j 𝒪_Y` forming one snc divisor (Kollár 3.26, 3.36;
*Flips and abundance* 2.9). For the empty family this is the existence of projective log
resolutions of log varieties.

## Main results

* `MMP.Flips.exists_isLogResolution_isEffectiveCartierDivisor_comap`: simultaneous
  principalization of finitely many nonzero ideals by a projective log resolution.
* `MMP.Flips.exists_isLogResolution_isProjectiveMorphism`: projective log resolutions of log
  varieties exist in characteristic zero.

## Implementation notes

The auxiliary lemmas live in the namespace `Proof_lem_mmp_simultaneous_ideal_log_resolution`,
opened only for that result.

The simultaneous principalization is applied to a Chow modification `r : X₁ ⟶ X`: Chow's lemma
gives `X₁` quasi-projective over `k`, and principalizing on `X₁` the inverse image of
`I_W · I_Δ · ∏ I_j` (`W` the complement of the biregular locus of `r`, `I_Δ` the ideal of
`Supp Δ`) gives a resolution `f : Y ⟶ X₁` with `g = f ≫ r` projective in the sense of a closed
immersion into some `ℙⁿ_X`. Every factor of the invertible product `(I_W · I_Δ · ∏ I_j) 𝒪_Y` is
invertible (Stacks 07ZV), and a reduced divisor whose components are components of an snc divisor
is snc. The inverse image ideal `I_j 𝒪_Y` is `(I j).comap g`; projectivity is
`AlgebraicGeometry.IsProjectiveMorphism`.

The sources work over `ℂ`; the statements are over any field of characteristic zero.

## References

* [J. Kollár, *Lectures on resolution of singularities*], 3.26, 3.36
* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.9
* [H. Hironaka, *Resolution of singularities of an algebraic variety over a field of
  characteristic zero*][Hir64]
* [Stacks Project, Tag 0200] (Chow's lemma)
-/

@[expose] public section

universe u

namespace Proof_lem_mmp_simultaneous_ideal_log_resolution

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP MMP.Mori MMP.Flips

/-! ### Prime divisors and generic points -/

private theorem genericPoint_mem_support {X : Scheme.{u}} (P : Mori.PrimeDivisor X) :
    P.genericPoint ∈ (P.support : Set X) := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact subset_closure rfl

/-- A prime divisor is determined by its support. -/
private theorem primeDivisor_eq_of_support_eq {X : Scheme.{u}} {P Q : Mori.PrimeDivisor X}
    (h : (P.support : Set X) = Q.support) : P = Q := by
  refine AlgebraicGeometry.PrimeDivisor.genericPoint_injective ?_
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h
  exact (inseparable_iff_closure_eq.2 h).eq

/-- The support of a finite product of ideal sheaves is the union of the supports. -/
private theorem coe_support_prod {X : Scheme.{u}} {ι : Type*} (s : Finset ι)
    (I : ι → X.IdealSheafData) :
    ((∏ j ∈ s, I j).support : Set X) = ⋃ j ∈ s, ((I j).support : Set X) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Scheme.IdealSheafData.support_mul, Closeds.coe_sup, ih,
      Finset.set_biUnion_insert]

/-! ### Chow's lemma -/

/-- **Chow's lemma for a variety.** A variety `X` over `k` is the target of a proper morphism
`r : X₁ ⟶ X` from a variety `X₁` which is H-quasi-projective over `k` and an isomorphism over a
nonempty open subset of `X`. -/
private theorem exists_isHQuasiProjective_isIso_morphismRestrict {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : Mori.IsVariety k sX) :
    ∃ (X₁ : Scheme.{u}) (r : X₁ ⟶ X) (U : X.Opens), Mori.IsVariety k (r ≫ sX) ∧ IsProper r ∧
      (U : Set X).Nonempty ∧ IsIso (r ∣_ U) ∧ IsHQuasiProjective (r ≫ sX) := by
  haveI : IsIntegral X := hX.toIsIntegral
  haveI : IsSeparated sX := hX.toIsSeparated
  haveI : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hX.toQuasiCompact
  obtain ⟨n, X', π, i, U, hπ, -, hi, hcomm, hdense, hiso⟩ := hasDenseChowModification sX
  have hUne : Nonempty U := hdense.nonempty.to_subtype
  have hVne : Nonempty (π ⁻¹ᵁ U) := ⟨(inv (π ∣_ U)).base hUne.some⟩
  haveI : IsIntegral (π ⁻¹ᵁ U) := isIntegral_of_isOpenImmersion (π ∣_ U)
  haveI : IsSeparated (π ≫ sX) := by
    rw [hcomm]
    infer_instance
  haveI : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (π ≫ sX)
  haveI : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace (π ≫ sX)
  haveI : IsNoetherian X' := ⟨⟩
  have hi1 : IsIso ((π ⁻¹ᵁ U).ι.imageι ∣_ (π ⁻¹ᵁ U)) :=
    Stacks.SchemeTheoreticImage.isIso_imageι_restrict _
  refine ⟨(π ⁻¹ᵁ U).ι.image, (π ⁻¹ᵁ U).ι.imageι ≫ π, U, ?_, inferInstance, hdense.nonempty,
    ?_, ?_⟩
  · rw [Category.assoc]
    exact Scheme.Hom.isVariety_image k _ (π ≫ sX)
  · rw [morphismRestrict_comp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hi1 hiso
  · have heq : ((π ⁻¹ᵁ U).ι.imageι ≫ i) ≫ (ProjectiveSpace n (Spec (.of k)) ↘ Spec (.of k)) =
        ((π ⁻¹ᵁ U).ι.imageι ≫ π) ≫ sX := by
      rw [Category.assoc, Category.assoc, hcomm]
    have : QuasiCompact (((π ⁻¹ᵁ U).ι.imageι ≫ i) ≫
        (ProjectiveSpace n (Spec (.of k)) ↘ Spec (.of k))) := by
      rw [heq]
      infer_instance
    have hqs : QuasiSeparated (ProjectiveSpace n (Spec (.of k)) ↘ Spec (.of k)) :=
      @IsSeparated.instQuasiSeparated _ _ _ (Stacks.HProjective.isSeparated_over n _)
    have him : IsImmersion ((π ⁻¹ᵁ U).ι.imageι ≫ i) := inferInstance
    exact ⟨n, (π ⁻¹ᵁ U).ι.imageι ≫ i, him, @QuasiCompact.of_comp _ _ _ _
      (ProjectiveSpace n (Spec (.of k)) ↘ Spec (.of k)) this hqs, heq⟩

/-- A proper morphism `g` whose composite with a morphism `s` is H-quasi-projective is a
projective morphism. -/
private theorem isProjectiveMorphism_of_isHQuasiProjective_comp {Y X S : Scheme.{u}}
    (g : Y ⟶ X) (s : X ⟶ S) [IsProper g] (h : IsHQuasiProjective (g ≫ s)) :
    IsProjectiveMorphism g := by
  obtain ⟨n, i, hi, -, hif⟩ := h
  haveI := hi
  rw [isProjectiveMorphism_iff_isHQuasiProjective_and_isProper]
  refine ⟨?_, inferInstance⟩
  let l : Y ⟶ Limits.pullback (projectiveSpaceOver n S ↘ S) s := Limits.pullback.lift i g hif
  have hl : IsImmersion l := by
    have : IsImmersion (l ≫ Limits.pullback.fst _ _) := by
      rwa [Limits.pullback.lift_fst]
    exact IsImmersion.of_comp l (Limits.pullback.fst _ _)
  have heq : (l ≫ (projectiveSpaceOverBaseChangeIso n s).hom) ≫
      (projectiveSpaceOver n X ↘ X) = g := by
    rw [Category.assoc, projectiveSpaceOverBaseChangeIso_hom_over, Limits.pullback.lift_snd]
  haveI : QuasiSeparated (projectiveSpaceOver n X ↘ X) :=
    @IsSeparated.instQuasiSeparated _ _ _ (Stacks.HProjective.isSeparated_over n X)
  have : QuasiCompact ((l ≫ (projectiveSpaceOverBaseChangeIso n s).hom) ≫
      (projectiveSpaceOver n X ↘ X)) := by
    rw [heq]
    infer_instance
  exact ⟨n, l ≫ (projectiveSpaceOverBaseChangeIso n s).hom, inferInstance,
    QuasiCompact.of_comp _ (projectiveSpaceOver n X ↘ X), heq⟩

/-- If `r` is an isomorphism over an open `U` and an ideal sheaf `J` does not vanish at a point
of `U`, then `r⁻¹ J` is nonzero. -/
private theorem comap_ne_bot_of_isIso_morphismRestrict {X₁ X : Scheme.{u}} (r : X₁ ⟶ X)
    {U : X.Opens} [IsIso (r ∣_ U)] {J : X.IdealSheafData} {x : X} (hxU : x ∈ U)
    (hx : x ∉ (J.support : Set X)) : J.comap r ≠ ⊥ := by
  intro h
  set a := (asIso (r ∣_ U)).inv ⟨x, hxU⟩
  have hra : r a.1 = x := by
    rw [← morphismRestrict_base_coe]
    exact congrArg Subtype.val (Scheme.inv_hom_apply (asIso (r ∣_ U)) ⟨x, hxU⟩)
  have : a.1 ∈ ((J.comap r).support : Set X₁) := by
    rw [h, Scheme.IdealSheafData.support_bot]
    trivial
  rw [Scheme.IdealSheafData.support_comap] at this
  exact hx (hra ▸ this)

/-- A morphism of irreducible schemes which is an isomorphism over a nonempty open subset of the
target is birational. -/
private theorem isBirationalMorphism_of_isIso_morphismRestrict {X Y : Scheme.{u}}
    [IrreducibleSpace X] [IrreducibleSpace Y] (f : X ⟶ Y) (U : Y.Opens)
    (hU : (U : Set Y).Nonempty) [IsIso (f ∣_ U)] : IsBirationalMorphism f := by
  obtain ⟨y, hy⟩ := hU
  have hV : ((f ⁻¹ᵁ U : X.Opens) : Set X).Nonempty := ⟨_, ((inv (f ∣_ U)) ⟨y, hy⟩).2⟩
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE f (f ⁻¹ᵁ U) U hV ⟨y, hy⟩ le_rfl ?_
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  infer_instance

/-- A composite of birational morphisms of irreducible schemes is birational. -/
private theorem isBirationalMorphism_comp {V X' X : Scheme.{u}} [IrreducibleSpace V]
    [IrreducibleSpace X'] [IrreducibleSpace X] {g : V ⟶ X'} {μ : X' ⟶ X}
    (hg : IsBirationalMorphism g) (hμ : IsBirationalMorphism μ) :
    IsBirationalMorphism (g ≫ μ) := by
  have : Nonempty V := (IrreducibleSpace.isIrreducible_univ V).nonempty.to_subtype.map Subtype.val
  have : Nonempty X' :=
    (IrreducibleSpace.isIrreducible_univ X').nonempty.to_subtype.map Subtype.val
  obtain ⟨Wg, hWgne, hWg⟩ := MMP.Mori.IsBirationalMorphism.exists_isOpenImmersion hg
  obtain ⟨Wμ, hWμne, hWμ⟩ := MMP.Mori.IsBirationalMorphism.exists_isOpenImmersion hμ
  obtain ⟨x₀, hx₀⟩ := hWgne
  obtain ⟨y, ⟨w, rfl⟩, hy⟩ := nonempty_preirreducible_inter
    (Wg.ι ≫ g).isOpenEmbedding.isOpen_range Wμ.isOpen ⟨_, (⟨x₀, hx₀⟩ : Wg.toScheme), rfl⟩ hWμne
  let U : V.Opens := Wg ⊓ g ⁻¹ᵁ Wμ
  have hwU : w.1 ∈ U := ⟨w.2, hy⟩
  have h1 : IsOpenImmersion (U.ι ≫ g) := by
    rw [← Scheme.homOfLE_ι V (inf_le_left : U ≤ Wg), Category.assoc]
    infer_instance
  have hrange : Set.range (U.ι ≫ g) ⊆ Set.range Wμ.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact z.2.2
  have hfac := IsOpenImmersion.lift_fac Wμ.ι (U.ι ≫ g) hrange
  have : IsOpenImmersion (IsOpenImmersion.lift Wμ.ι (U.ι ≫ g) hrange ≫ Wμ.ι) := by
    rwa [hfac]
  have : IsOpenImmersion (IsOpenImmersion.lift Wμ.ι (U.ι ≫ g) hrange) :=
    IsOpenImmersion.of_comp _ Wμ.ι
  have hU : IsOpenImmersion (U.ι ≫ g ≫ μ) := by
    rw [← Category.assoc, ← hfac, Category.assoc]
    infer_instance
  let V' : X.Opens := (U.ι ≫ g ≫ μ).opensRange
  have hle : U ≤ (g ≫ μ) ⁻¹ᵁ V' := fun x hx => ⟨⟨x, hx⟩, rfl⟩
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE (g ≫ μ) U V' ⟨_, hwU⟩
    ⟨_, ⟨⟨w.1, hwU⟩, rfl⟩⟩ hle ?_
  have e : (g ≫ μ).resLE V' U hle = (U.ι ≫ g ≫ μ).isoOpensRange.hom := by
    rw [← cancel_mono V'.ι, Scheme.Hom.resLE_comp_ι, Scheme.Hom.isoOpensRange_hom_ι]
  rw [e]
  infer_instance

/-! ### Components of snc divisors -/

/-- The support of a prime divisor, as an irreducible closed subset. -/
private noncomputable def primeIrr {X : Scheme.{u}} (E : AlgebraicGeometry.PrimeDivisor X) :
    IrreducibleCloseds X :=
  IrreducibleCloseds.closureSingleton E.genericPoint

private theorem coe_primeIrr {X : Scheme.{u}} (E : AlgebraicGeometry.PrimeDivisor X) :
    (primeIrr E : Set X) = E.support := by
  rw [E.support_eq_closure]
  rfl

/-- An irreducible closed subset of codimension one contained in the union of the supports of
finitely many prime divisors is the support of one of them. -/
private theorem exists_mem_support_eq {X : Scheme.{u}}
    {s : Finset (AlgebraicGeometry.PrimeDivisor X)} (W : IrreducibleCloseds X)
    (hW : (W : Set X) ⊆ ⋃ E ∈ s, E.support) (hW1 : codimension W = 1) :
    ∃ E ∈ s, (E.support : Set X) = W := by
  classical
  obtain ⟨z, hz, hWz⟩ := (isIrreducible_iff_sUnion_isClosed.mp W.isIrreducible)
    (s.image AlgebraicGeometry.PrimeDivisor.support)
    (by
      intro z hz
      obtain ⟨E, -, rfl⟩ := Finset.mem_image.mp hz
      rw [← coe_primeIrr]
      exact (primeIrr E).isClosed)
    (by
      intro x hx
      obtain ⟨E, hE, hxE⟩ := Set.mem_iUnion₂.mp (hW hx)
      exact ⟨E.support, Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hE), hxE⟩)
  obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hz
  have hWE : W ≤ primeIrr E := fun x hx ↦ (coe_primeIrr E).superset (hWz hx)
  have hWE' : W = primeIrr E := by
    by_contra hne
    have hlt : W < primeIrr E := lt_of_le_of_ne hWE hne
    have := Order.coheight_add_one_le hlt
    rw [← codimension_eq_coheight, ← codimension_eq_coheight,
      show codimension (primeIrr E) = 1 from E.codimension_one, hW1] at this
    exact absurd this (by decide)
  exact ⟨E, hE, by rw [← coe_primeIrr, ← hWE']⟩

/-- The preimage in a subspace `C` of a preirreducible subset of `C` is preirreducible. -/
private theorem isPreirreducible_preimage_val {Y : Type*} [TopologicalSpace Y] {C W : Set Y}
    (hW : IsPreirreducible W) (hWC : W ⊆ C) : IsPreirreducible (Subtype.val ⁻¹' W : Set C) := by
  rintro u v hu hv ⟨a, ha, hau⟩ ⟨b, hb, hbv⟩
  obtain ⟨u', hu', rfl⟩ := isOpen_induced_iff.mp hu
  obtain ⟨v', hv', rfl⟩ := isOpen_induced_iff.mp hv
  obtain ⟨y, hyW, hyu, hyv⟩ := hW u' v' hu' hv' ⟨a, ha, hau⟩ ⟨b, hb, hbv⟩
  exact ⟨⟨y, hWC hyW⟩, hyW, hyu, hyv⟩

/-- An irreducible closed set contained in a closed set lies in an irreducible closed subset
maximal in it. -/
private theorem exists_maximal_ge {Y : Type*} [TopologicalSpace Y] {C : Set Y} (hC : IsClosed C)
    (Z : IrreducibleCloseds Y) (hZ : (Z : Set Y) ⊆ C) :
    ∃ W : IrreducibleCloseds Y, Maximal (fun W' : IrreducibleCloseds Y ↦ (W' : Set Y) ⊆ C) W ∧
      Z ≤ W := by
  obtain ⟨t, ht, hxt, hmax⟩ := exists_preirreducible (Subtype.val ⁻¹' (Z : Set Y) : Set C)
    (isPreirreducible_preimage_val Z.isIrreducible.isPreirreducible hZ)
  obtain ⟨z, hz⟩ := Z.isIrreducible.nonempty
  let W : IrreducibleCloseds Y := ⟨closure (Subtype.val '' t),
    (IsIrreducible.closure ⟨⟨z, ⟨z, hZ hz⟩, hxt hz, rfl⟩,
      ht.image _ continuous_subtype_val.continuousOn⟩), isClosed_closure⟩
  have hWC : (W : Set Y) ⊆ C := closure_minimal (Subtype.coe_image_subset _ _) hC
  refine ⟨W, ⟨hWC, fun W' hW'C hWW' y hy ↦ ?_⟩, fun y hy ↦ subset_closure ⟨⟨y, hZ hy⟩, hxt hy, rfl⟩⟩
  have := hmax _ (isPreirreducible_preimage_val W'.isIrreducible.isPreirreducible hW'C)
    fun y hy ↦ hWW' (subset_closure ⟨y, hy, rfl⟩)
  have : (⟨y, hW'C hy⟩ : C) ∈ t := by rwa [← this]
  exact subset_closure ⟨_, this, rfl⟩

/-- The support of an effective Cartier divisor on a scheme locally of finite type over a field
is of pure codimension one. -/
private theorem isPureCodimOne_support_of_isEffectiveCartierDivisor {k : Type u} [Field k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] {D : Y.IdealSheafData}
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) : IsPureCodimOne D.support := by
  letI : Y.Over (Spec (.of k)) := ⟨sY⟩
  haveI : LocallyOfFiniteType (Y ↘ Spec (.of k)) := ‹LocallyOfFiniteType sY›
  intro W hW
  set e := irreducibleSetEquivPoints (α := Y)
  have hWη : (W : Set Y) = closure {e W} := by
    conv_lhs => rw [← e.symm_apply_apply W]
    rfl
  have hηW : e W ∈ (W : Set Y) := by
    rw [hWη]
    exact subset_closure rfl
  have h1 : codimension W = Order.coheight (e W) := by
    change Order.coheight W = _
    rw [← Order.coheight_orderIso e W]
  rw [h1]
  refine MMP.coheight_eq_one_of_isEffectiveCartierDivisor k hD (hW.1 hηW)
    fun y hy hyη => ?_
  have hle : W ≤ e.symm y := by
    rw [← e.le_iff_le, e.apply_symm_apply, Scheme.le_iff_specializes]
    exact hyη
  have hsub : ((e.symm y : IrreducibleCloseds Y) : Set Y) ⊆ D.support := by
    change closure {y} ⊆ _
    exact closure_minimal (Set.singleton_subset_iff.mpr hy) D.support.isClosed
  have heq : e.symm y = W := le_antisymm (hW.2 hsub hle) hle
  rw [← heq, e.apply_symm_apply]

/-- **Points of an effective Cartier divisor inside an snc subset lie on its components.** If the
support of an effective Cartier divisor `D` on a scheme locally of finite type over `k` lies in an
snc subset, then every point of `Supp D` lies on a prime divisor contained in `Supp D`. -/
private theorem exists_primeDivisor_subset_support_mem {k : Type u} [Field k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [LocallyOfFiniteType sY] {S : Closeds Y} (hS : IsSNCSubset sY S)
    {D : Y.IdealSheafData} (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (hDS : (D.support : Set Y) ⊆ S) {y : Y} (hy : y ∈ (D.support : Set Y)) :
    ∃ P : Mori.PrimeDivisor Y, (P.support : Set Y) ⊆ D.support ∧ y ∈ P.support := by
  obtain ⟨W, hWmax, hyW⟩ := exists_maximal_ge D.support.isClosed
    (IrreducibleCloseds.closureSingleton y)
    (closure_minimal (Set.singleton_subset_iff.mpr hy) D.support.isClosed)
  have hyW' : y ∈ (W : Set Y) := hyW (subset_closure rfl)
  rcases hS with rfl | ⟨s, hs, -⟩
  · exact absurd (hDS (hWmax.1 hyW')) (by simp)
  · obtain ⟨E, -, hEW⟩ := exists_mem_support_eq W (hs ▸ hWmax.1.trans hDS)
      (isPureCodimOne_support_of_isEffectiveCartierDivisor sY hD W hWmax)
    exact ⟨E, hEW ▸ hWmax.1, hEW ▸ hyW'⟩

private theorem coeff_sum_single {X : Scheme.{u}} (s : Finset (Mori.PrimeDivisor X))
    (P : Mori.PrimeDivisor X) [Decidable (P ∈ s)] :
    (∑ E ∈ s, Finsupp.single E (1 : ℤ) : Divisor X).coeff P = if P ∈ s then 1 else 0 := by
  classical
  simp [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply, Finsupp.single_apply]

/-- The reduced divisor with components `s` has coefficients `0` and `1`. -/
private theorem coeff_sum_single_eq_zero_or_eq_one {X : Scheme.{u}}
    (s : Finset (Mori.PrimeDivisor X)) (P : Mori.PrimeDivisor X) :
    (∑ E ∈ s, Finsupp.single E (1 : ℤ) : Divisor X).coeff P = 0 ∨
      (∑ E ∈ s, Finsupp.single E (1 : ℤ) : Divisor X).coeff P = 1 := by
  classical
  rw [coeff_sum_single]
  split_ifs <;> simp

/-- An snc reduced divisor in the sense of `DivisorWithCoeffs.IsSNC` is an snc divisor in the
sense of *Flips and abundance*. -/
private theorem isSNCDivisor_sum_single {k : Type u} [Field k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} (s : Finset (Mori.PrimeDivisor Y))
    (h : (∑ P ∈ s, Finsupp.single P (1 : ℤ) : Divisor Y).IsSNC sY) :
    MMP.Flips.IsSNCDivisor sY (∑ P ∈ s, Finsupp.single P (1 : ℤ)) :=
  ⟨coeff_sum_single_eq_zero_or_eq_one s, h.1, fun p _ => h.2 p⟩

/-- **A reduced divisor whose components lie in an snc divisor is snc.** Let `S` be an snc
closed subset of a smooth `k`-scheme `Y` and `Q` a property of prime divisors whose prime divisors lie
in `S`. Then the reduced divisor with components the prime divisors with `Q` is an snc
divisor. -/
private theorem exists_isSNCDivisor_of_isSNCSubset {k : Type u} [Field k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [LocallyOfFinitePresentation sY] (hsm : IsSmoothScheme sY)
    {S : Closeds Y} (hS : IsSNCSubset sY S)
    (Q : Mori.PrimeDivisor Y → Prop) (hQ : ∀ P, Q P → (P.support : Set Y) ⊆ S) :
    ∃ G : Divisor Y, (∀ P, G.coeff P = 0 ∨ G.coeff P = 1) ∧ (∀ P, G.coeff P = 1 ↔ Q P) ∧
      IsSNCDivisor sY G := by
  classical
  rcases hS with rfl | ⟨s, hs, hsnc⟩
  · have hQ0 : ∀ P, ¬ Q P := fun P hP => hQ P hP (genericPoint_mem_support P)
    refine ⟨∑ P ∈ (∅ : Finset (Mori.PrimeDivisor Y)), Finsupp.single P (1 : ℤ),
      coeff_sum_single_eq_zero_or_eq_one _, fun P => ?_, isSNCDivisor_sum_single _ ?_⟩
    · rw [coeff_sum_single]
      simp [hQ0 P]
    · rw [Finset.sum_empty]
      exact DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme sY hsm
  · have hmem : ∀ P, Q P → P ∈ s := fun P hP => by
      obtain ⟨E, hE, hEP⟩ := exists_mem_support_eq (s := s) (primeIrr P)
        (by rw [coe_primeIrr, hs]; exact hQ P hP) P.codimension_one
      rw [coe_primeIrr] at hEP
      rwa [← primeDivisor_eq_of_support_eq hEP]
    refine ⟨∑ P ∈ s.filter Q, Finsupp.single P (1 : ℤ),
      coeff_sum_single_eq_zero_or_eq_one _, fun P => ?_, isSNCDivisor_sum_single _ ?_⟩
    · rw [coeff_sum_single]
      by_cases hP : Q P
      · simp [hP, hmem P hP]
      · simp [hP]
    · refine hsnc.of_support_subset ?_
      intro E hE
      rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply] at hE ⊢
      simp only [Finsupp.single_apply] at hE ⊢
      rw [Finset.sum_ite_eq'] at hE ⊢
      split_ifs at hE with h1
      · rw [if_pos (Finset.mem_filter.mp h1).1]
        exact one_ne_zero
      · exact absurd rfl hE

/-! ### Strict transforms and exceptional divisors -/

/-- A coefficient of the linear extension of a partial map `φ` on prime divisors is nonzero only
at the image of a prime divisor with nonzero coefficient. -/
private theorem exists_apply_ne_zero_of_mapPrimeDivisors_apply_ne_zero {X Y : Scheme.{u}}
    {R : Type*} [AddCommMonoid R] {φ : Mori.PrimeDivisor X → Option (Mori.PrimeDivisor Y)}
    {D : DivisorWithCoeffs R X} {P : Mori.PrimeDivisor Y}
    (h : DivisorWithCoeffs.mapPrimeDivisors φ D P ≠ 0) : ∃ Q, D Q ≠ 0 ∧ φ Q = some P := by
  classical
  by_contra hne
  push Not at hne
  refine h ?_
  conv_lhs => rw [← Finsupp.sum_single D]
  rw [Finsupp.sum, map_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_eq_zero fun Q hQ => ?_
  rw [DivisorWithCoeffs.mapPrimeDivisors_single]
  rcases hφ : φ Q with _ | E
  · rfl
  · have hne' : E ≠ P := fun he => hne Q (Finsupp.mem_support_iff.mp hQ) (by rw [hφ, he])
    exact Finsupp.single_eq_of_ne' hne'

private theorem source_ι_comp_eq_of_toRationalMap_eq {X Y : Scheme.{u}} [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) : e.source.ι ≫ f = e.iso.hom ≫ e.target.ι :=
  ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp he)).symm

/-- If `e` is a partial isomorphism representing `f : Y ⟶ X` and `g'` a partial map representing
`e⁻¹`, then `f ∘ g'` is the identity where `g'` is defined. -/
private theorem apply_hom_eq_of_isInverse {X Y : Scheme.{u}} [IsReduced Y] [IsReduced X]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = e.symm.toRationalMap) {x : X} (hx : x ∈ g'.domain) :
    f (g'.hom ⟨x, hx⟩) = x := by
  have h1 : (g'.compHom f).toRationalMap = (Scheme.PartialMap.id X).toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg', ← Scheme.RationalMap.compHom_toRationalMap,
      Scheme.PartialMap.toRationalMap_eq_iff,
      Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
    change e.iso.inv ≫ e.source.ι ≫ f = e.target.ι ≫ 𝟙 X
    rw [source_ι_comp_eq_of_toRationalMap_eq f e he, Iso.inv_hom_id_assoc, Category.comp_id]
  have h2 := MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq
    (g := g'.compHom f) (g' := Scheme.PartialMap.id X) h1 hx trivial
  change (g'.hom ≫ f) ⟨x, hx⟩ = (X.topIso.hom ≫ 𝟙 X) ⟨x, trivial⟩ at h2
  refine (Scheme.Hom.comp_apply _ _ _).symm.trans (h2.trans ?_)
  rw [Category.comp_id, Scheme.topIso_hom]
  rfl

private theorem coe_transform_eq_closure_singleton {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = φ) (P : Mori.PrimeDivisor X) (hP : P.genericPoint ∈ g'.domain) :
    (Mori.RationalMap.transform φ P.idealSheaf.support : Set Y) =
      closure {g'.hom ⟨P.genericPoint, hP⟩} := by
  have hZ : closure ((P.idealSheaf.support : Set X) ∩ g'.domain) = P.idealSheaf.support := by
    refine le_antisymm ?_ ?_
    · exact closure_minimal Set.inter_subset_left P.idealSheaf.support.isClosed
    · change P.support ⊆ _
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact closure_mono (Set.singleton_subset_iff.mpr ⟨genericPoint_mem_support P, hP⟩)
  rw [← MMP.Positivity.closure_image_eq_transform g' hg' _ hZ, Closeds.coe_closure]
  refine le_antisymm (closure_minimal ?_ isClosed_closure) (closure_mono ?_)
  · rintro _ ⟨q, hq, rfl⟩
    have hq' : P.genericPoint ⤳ g'.domain.ι q := by
      have : g'.domain.ι q ∈ P.support := hq
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
      exact specializes_iff_mem_closure.mpr this
    have h1 := (g'.domain.ι.isOpenEmbedding.isInducing.specializes_iff (y := q)
      (x := ⟨P.genericPoint, hP⟩)).mp (by rwa [Scheme.Opens.ι_apply])
    exact specializes_iff_mem_closure.mp (h1.map g'.hom.continuous)
  · rw [Set.singleton_subset_iff]
    exact ⟨⟨P.genericPoint, hP⟩, genericPoint_mem_support P, rfl⟩

private theorem genericPoint_eq_of_transformPrimeDivisor_eq_some {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : Mori.PrimeDivisor X}
    {E : Mori.PrimeDivisor Y} (h : Mori.RationalMap.transformPrimeDivisor φ P = some E)
    (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ) (hP : P.genericPoint ∈ g'.domain) :
    E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩ := by
  have h1 := Mori.RationalMap.support_transformPrimeDivisor h
  rw [coe_transform_eq_closure_singleton g' hg' P hP,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h1
  exact (inseparable_iff_closure_eq.2 h1).eq

/-- If the strict transform of a prime divisor `P` of `X` under the inverse of a birational
morphism `f : Y ⟶ X` is `E`, then `f` sends the generic point of `E` to that of `P`. -/
private theorem genericPoint_eq_of_transformPrimeDivisor_inverse_eq_some {X Y : Scheme.{u}}
    [IsReduced X] [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] [IsSeparated (Y ↘ ⊤_ Scheme)] {f : Y ⟶ X}
    (hf : IsBirationalMorphism f) {P : Mori.PrimeDivisor X} {E : Mori.PrimeDivisor Y}
    (h : Mori.RationalMap.transformPrimeDivisor (Mori.RationalMap.IsBirational.inverse hf) P =
      some E) :
    f E.genericPoint = P.genericPoint := by
  obtain ⟨e, he, he'⟩ := hf.isInverse_inverse
  obtain ⟨g', hP, hg'⟩ :=
    Mori.RationalMap.definedAt_iff.mp (Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp h).1
  rw [genericPoint_eq_of_transformPrimeDivisor_eq_some h g' hg' hP]
  exact apply_hom_eq_of_isInverse f e he g' (hg'.trans he'.symm) hP

private theorem isSeparated_toTerminal_of_isSeparated {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsSeparated sX] : IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

/-- A component `P` of the strict transform `g⁻¹_* D` under a birational morphism of varieties
lies over a component `Q` of `D`: `g(η_P) = η_Q`. -/
private theorem exists_map_genericPoint_eq_of_birationalInverseTransform_ne_zero
    {k : Type u} [Field k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    (hX : Mori.IsVariety k sX) {g : Y ⟶ X} (hY : Mori.IsVariety k (g ≫ sX))
    (hg : IsBirationalMorphism g) {R : Type*} [AddCommMonoid R] {D : DivisorWithCoeffs R X}
    {P : Mori.PrimeDivisor Y} (h : MMP.Flips.birationalInverseTransform g hg D P ≠ 0) :
    ∃ Q, D Q ≠ 0 ∧ g P.genericPoint = Q.genericPoint := by
  have : IsIntegral X := hX.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  have : IsSeparated sX := hX.toIsSeparated
  have : IsSeparated (g ≫ sX) := hY.toIsSeparated
  have := isSeparated_toTerminal_of_isSeparated sX
  have := isSeparated_toTerminal_of_isSeparated (g ≫ sX)
  obtain ⟨Q, hQ, hQP⟩ := exists_apply_ne_zero_of_mapPrimeDivisors_apply_ne_zero
    (φ := Mori.RationalMap.transformPrimeDivisor (Mori.RationalMap.IsBirational.inverse hg)) h
  exact ⟨Q, hQ, genericPoint_eq_of_transformPrimeDivisor_inverse_eq_some hg hQP⟩

private theorem withBot_add_two_le_iff {d : WithBot ℕ∞} {c : ℕ∞} {n : ℕ} (h : d + c = n) :
    d + 2 ≤ n ↔ 2 ≤ c := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe d =>
    induction d using ENat.recTopCoe with
    | top => exact absurd (WithBot.coe_injective h) (by simp)
    | coe d =>
      induction c using ENat.recTopCoe with
      | top => exact absurd (WithBot.coe_injective h) (by simp)
      | coe c =>
        have h' : d + c = n := by exact_mod_cast h
        rw [show ((d : ℕ∞) : WithBot ℕ∞) + 2 = ((d + 2 : ℕ) : WithBot ℕ∞) by norm_cast]
        norm_cast
        omega

/-- A variety has finite dimension. -/
private theorem exists_topologicalKrullDim_eq {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : Mori.IsVariety k sX) : ∃ n : ℕ, topologicalKrullDim X = n := by
  have : IsIntegral X := hX.toIsIntegral
  have : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  have : QuasiCompact sX := hX.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have h1 := topologicalKrullDim_ne_top_of_locallyOfFiniteType k sX
  have h2 : topologicalKrullDim X ≠ ⊥ := by
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    have : Nonempty (IrreducibleCloseds X) := ⟨IrreducibleCloseds.closureSingleton x⟩
    unfold topologicalKrullDim
    rw [Ne, Order.krullDim_eq_bot_iff]
    exact not_isEmpty_of_nonempty _
  generalize topologicalKrullDim X = d at h1 h2
  induction d using WithBot.recBotCoe with
  | bot => exact absurd rfl h2
  | coe d =>
    induction d using ENat.recTopCoe with
    | top => exact absurd rfl h1
    | coe n => exact ⟨n, rfl⟩

/-- The generic point of a prime divisor `P` of `Y` exceptional over `X` lies in `Ex(f)`. -/
private theorem genericPoint_mem_exceptionalSet {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX] {n : ℕ}
    (hn : topologicalKrullDim X = n) {Y : Scheme.{u}} {f : Y ⟶ X} {P : Mori.PrimeDivisor Y}
    (h : MMP.Flips.IsExceptionalPrimeDivisor sX f P) :
    P.genericPoint ∈ (Mori.exceptionalSet f : Set Y) := by
  obtain ⟨hY, hf, hp, hexc⟩ := h
  set D := MMP.Flips.ProperDivisorOver.mk ⟨Y, f, hY, hf, P⟩ hp
  have h2 : 2 ≤ Order.coheight (f P.genericPoint) := by
    unfold MMP.Flips.ProperDivisorOver.IsExceptional at hexc
    rw [D.center_eq_toDivisorOver_center, D.toDivisorOver.center_eq_closure_genericPoint,
      hn] at hexc
    have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX (f P.genericPoint)
    rw [hn] at h
    exact (withBot_add_two_le_iff h).mp hexc
  by_contra hmem
  have hV : f P.genericPoint ∈ biregularLocus f := by
    by_contra hV
    exact hmem (mem_exceptionalSet.mpr hV)
  rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f hV, P.coheight_genericPoint] at h2
  exact absurd h2 (by decide)

/-! ### Exceptional sets of composites -/

/-- The exceptional set of a composite `π ≫ g`, with `π` an isomorphism off a closed set `Z ⊆ B`
and `B` containing the exceptional set of `g`, lies in `π⁻¹ B`. -/
private theorem exceptionalSet_comp_subset {X Y Y' : Scheme.{u}} (g : Y ⟶ X) [IsProper g]
    (π : Y' ⟶ Y) (Z : Closeds Y) (hπ : IsIso (π ∣_ ⟨(Z : Set Y)ᶜ, Z.isClosed.isOpen_compl⟩))
    {B : Set Y} (hB : (Mori.exceptionalSet g : Set Y) ⊆ B) (hZ : (Z : Set Y) ⊆ B) :
    (Mori.exceptionalSet (π ≫ g) : Set Y') ⊆ π ⁻¹' B := by
  intro y' hy'
  by_contra hyB
  apply hy'
  set V0 : X.Opens := biregularLocus g ⊓
    ⟨(g '' (Z : Set Y))ᶜ, (g.isClosedMap _ Z.isClosed).isOpen_compl⟩
  have hgV : IsBiregular g V0 := isBiregular_iff_le_biregularLocus.mpr inf_le_left
  have hπV : IsBiregular π (g ⁻¹ᵁ V0) := by
    refine isBiregular_iff_le_biregularLocus.mpr (le_trans ?_ (le_biregularLocus hπ))
    intro y hy hyZ
    exact hy.2 ⟨y, hyZ, rfl⟩
  have hV : IsBiregular (π ≫ g) V0 := by
    change IsIso ((π ≫ g) ∣_ V0)
    rw [morphismRestrict_comp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hπV hgV
  have hπy : π y' ∉ (Mori.exceptionalSet g : Set Y) := fun h => hyB (hB h)
  refine le_biregularLocus hV ⟨not_not.mp hπy, ?_⟩
  rintro ⟨c, hcZ, hc⟩
  rw [Scheme.Hom.comp_apply] at hc
  have hcB : g c ∈ biregularLocus g := by
    rw [hc]
    exact not_not.mp hπy
  have hinj : c = π y' := by
    have hb' : g (π y') ∈ biregularLocus g := hc ▸ hcB
    exact ((MMP.Threefold.Resolution.specializes_of_mem_biregularLocus g hcB hb'
      (hc ▸ specializes_rfl)).antisymm
      (MMP.Threefold.Resolution.specializes_of_mem_biregularLocus g hb' hcB
        (hc ▸ specializes_rfl))).eq
  exact hyB (by rw [Set.mem_preimage, ← hinj]; exact hZ hcZ)

/-- The exceptional set of a composite `f ≫ r` lies in `Ex(f) ∪ f⁻¹ Ex(r)`. -/
private theorem exceptionalSet_comp_subset_union {X X₁ Y : Scheme.{u}} (f : Y ⟶ X₁)
    (r : X₁ ⟶ X) [IsProper r] :
    (Mori.exceptionalSet (f ≫ r) : Set Y) ⊆
      (Mori.exceptionalSet f : Set Y) ∪ f ⁻¹' (Mori.exceptionalSet r : Set X₁) := by
  set Z : Closeds X₁ := (biregularLocus f).compl
  have hZo : (⟨(Z : Set X₁)ᶜ, Z.isClosed.isOpen_compl⟩ : X₁.Opens) = biregularLocus f :=
    TopologicalSpace.Opens.ext (compl_compl _)
  have hπ : IsIso (f ∣_ ⟨(Z : Set X₁)ᶜ, Z.isClosed.isOpen_compl⟩) := by
    rw [hZo]
    exact isBiregular_biregularLocus f
  exact exceptionalSet_comp_subset r f Z hπ (B := (Z : Set X₁) ∪ (Mori.exceptionalSet r : Set X₁))
    Set.subset_union_right Set.subset_union_left

/-! ### Principalization on a Chow modification -/

/-- The support of `I(Z) · I(W) · ∏ I_j` is `Z ∪ W ∪ ⋃ Supp I_j`. -/
private theorem coe_support_vanishingIdeal_mul_prod {X : Scheme.{u}} {ι : Type*} [Fintype ι]
    (Z W : Closeds X) (I : ι → X.IdealSheafData) :
    ((Scheme.IdealSheafData.vanishingIdeal Z * Scheme.IdealSheafData.vanishingIdeal W *
      ∏ j, I j).support : Set X) =
      ((Z : Set X) ∪ W) ∪ ⋃ j ∈ Finset.univ, ((I j).support : Set X) := by
  rw [Scheme.IdealSheafData.support_mul, Scheme.IdealSheafData.support_mul, Closeds.coe_sup,
    Closeds.coe_sup, coe_support_prod, Scheme.IdealSheafData.coe_support_vanishingIdeal,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]

/-- The generic point of an integral scheme off `Z` and `W` is off the support of
`I(Z) · I(W) · ∏ I_j` for nonzero `I_j`. -/
private theorem genericPoint_notMem_support_vanishingIdeal_mul_prod {X : Scheme.{u}}
    [IsIntegral X] {ι : Type*} [Fintype ι] {Z W : Closeds X} {I : ι → X.IdealSheafData}
    (hZ : genericPoint X ∉ (Z : Set X)) (hW : genericPoint X ∉ (W : Set X)) (hI : ∀ j, I j ≠ ⊥) :
    genericPoint X ∉ ((Scheme.IdealSheafData.vanishingIdeal Z *
      Scheme.IdealSheafData.vanishingIdeal W * ∏ j, I j).support : Set X) := by
  rw [coe_support_vanishingIdeal_mul_prod]
  rintro ((h | h) | h)
  · exact hZ h
  · exact hW h
  · obtain ⟨j, -, hj⟩ := Set.mem_iUnion₂.mp h
    exact Stacks.Chow.notMem_support_genericPoint_of_ne_bot (hI j) hj

/-- If the inverse image of `A · ∏ I_j` is effective Cartier, so is the inverse image of each
`I_j`. -/
private theorem isEffectiveCartierDivisor_comap_of_mul_prod {X Y : Scheme.{u}} (g : Y ⟶ X)
    {ι : Type*} [Fintype ι] (A : X.IdealSheafData) (I : ι → X.IdealSheafData)
    (h : Stacks.Divisors.IsEffectiveCartierDivisor ((A * ∏ j, I j).comap g)) (j : ι) :
    Stacks.Divisors.IsEffectiveCartierDivisor ((I j).comap g) := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ I (Finset.mem_univ j), mul_left_comm, comap_mul] at h
  exact isEffectiveCartierDivisor_left_of_mul _ _ h

/-- **Simultaneous principalization on a variety.** For nonzero ideal sheaves `I_j` on a variety
`X` over a field of characteristic zero and an `ℝ`-divisor `Δ` on `X`, there is a projective
birational morphism `g : Y ⟶ X` from a smooth variety with every `I_j 𝒪_Y` effective Cartier, and
an snc subset `S` of `Y` containing `Ex(g)`, `g⁻¹ Supp Δ` and every `Supp I_j 𝒪_Y`. -/
private theorem exists_isProjectiveMorphism_isSNCSubset {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hXv : Mori.IsVariety k sX) (Δ : RDivisor X)
    {ι : Type*} [Fintype ι] (I : ι → X.IdealSheafData) (hI : ∀ j, I j ≠ ⊥) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ X) (S : Closeds Y), Mori.IsVariety k (g ≫ sX) ∧
      IsSmoothScheme (g ≫ sX) ∧ IsProjectiveMorphism g ∧ IsBirationalMorphism g ∧
      (∀ j, Stacks.Divisors.IsEffectiveCartierDivisor ((I j).comap g)) ∧
      IsSNCSubset (g ≫ sX) S ∧ (Mori.exceptionalSet g : Set Y) ⊆ S ∧
      (∀ y, g y ∈ (Δ.supp : Set X) → y ∈ (S : Set Y)) ∧
      ∀ j, (((I j).comap g).support : Set Y) ⊆ S := by
  classical
  haveI : IsIntegral X := hXv.toIsIntegral
  haveI : LocallyOfFiniteType sX := hXv.toLocallyOfFiniteType
  obtain ⟨X₁, r, U, hX₁, hrp, hUne, hrU, hrq⟩ :=
    exists_isHQuasiProjective_isIso_morphismRestrict sX hXv
  haveI : IsIntegral X₁ := hX₁.toIsIntegral
  haveI := Stacks.Ample.isInvertibleModule_unit (Spec (.of k))
  obtain ⟨L, hL, hLa⟩ := exists_isAmple_of_isQuasiProjective (r ≫ sX) _
    (Stacks.Ample.isAmple_unitModule_of_isAffine _) (isQuasiProjective_of_isHQuasiProjective _ hrq)
  set IW : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal (biregularLocus r).compl
  set IΔ : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal Δ.supp
  set Itot : X.IdealSheafData := IW * IΔ * ∏ j, I j
  have hItot_supp : (Itot.support : Set X) = ((biregularLocus r : Set X)ᶜ ∪ (Δ.supp : Set X)) ∪
      ⋃ j ∈ Finset.univ, ((I j).support : Set X) :=
    coe_support_vanishingIdeal_mul_prod (biregularLocus r).compl Δ.supp I
  have hηU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by rwa [Set.univ_inter])
  have hItot_ne : genericPoint X ∉ (Itot.support : Set X) :=
    genericPoint_notMem_support_vanishingIdeal_mul_prod
      (fun h => h (isBiregular_iff_le_biregularLocus.mp hrU hηU))
      (MMP.Fourfold.genericPoint_notMem_supp Δ) hI
  set J : X₁.IdealSheafData := Itot.comap r
  obtain ⟨Y, f, hYv, hfproj, hfbir, hfsm, -, hfcart, hfsnc, -⟩ :=
    MMP.Resolution.exists_isResolutionOfVariety_isEffectiveCartierDivisor_comap (r ≫ sX) hX₁ J
      (comap_ne_bot_of_isIso_morphismRestrict r hηU hItot_ne)
  set g : Y ⟶ X := f ≫ r
  have hgsX : g ≫ sX = f ≫ r ≫ sX := Category.assoc _ _ _
  have hJg : J.comap f = Itot.comap g := (Scheme.IdealSheafData.comap_comp Itot f r).symm
  rw [hJg] at hfcart
  set S : Closeds Y := Mori.exceptionalSet f ⊔ (Itot.comap g).support with hSdef
  have hpre : ∀ y : Y, g y ∈ (Itot.support : Set X) → y ∈ (S : Set Y) := fun y hy =>
    Or.inr (by rwa [Scheme.IdealSheafData.support_comap])
  refine ⟨Y, g, S, by rwa [hgsX], by rwa [hgsX],
    (isProjectiveMorphism_of_isProjective f L hLa hfproj).comp
      (isProjectiveMorphism_of_isHQuasiProjective_comp r sX hrq),
    isBirationalMorphism_comp hfbir (isBirationalMorphism_of_isIso_morphismRestrict r U hUne),
    isEffectiveCartierDivisor_comap_of_mul_prod g (IW * IΔ) I hfcart,
    by rwa [hgsX, hSdef, ← hJg],
    fun y hy => (exceptionalSet_comp_subset_union f r hy).elim Or.inl fun h =>
      hpre y (hItot_supp ▸ Or.inl (Or.inl h)),
    fun y hy => hpre y (hItot_supp ▸ Or.inl (Or.inr hy)), fun j y hy => hpre y ?_⟩
  rw [Scheme.IdealSheafData.support_comap] at hy
  exact hItot_supp ▸ Or.inr (Set.mem_iUnion₂.mpr ⟨j, Finset.mem_univ j, hy⟩)

end Proof_lem_mmp_simultaneous_ideal_log_resolution

namespace MMP.Flips

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP MMP.Mori MMP.Flips
open Proof_lem_mmp_simultaneous_ideal_log_resolution

/-- **Simultaneous principalization and log resolution.** Let `X` be a normal variety over a
field `k` of characteristic zero, `Δ` a boundary on `X` and `I_j` (`j ∈ ι`, `ι` finite) nonzero
ideal sheaves on `X`. There is a projective log resolution `g : Y ⟶ X` of `(X, Δ)` such that
every `I_j 𝒪_Y` is the ideal of an effective Cartier divisor `G_j`, and a reduced snc divisor `G`
on `Y` whose components are the components of `g⁻¹_* Δ`, the prime divisors exceptional over `X`
and the prime divisors contained in some `Supp G_j`, and whose support contains every
`Supp G_j`. -/
@[mmp "lem_mmp_simultaneous_ideal_log_resolution"]
public theorem exists_isLogResolution_isEffectiveCartierDivisor_comap {k : Type u} [Field k]
    [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : IsNormalVariety k sX)
    (Δ : RDivisor X) (hΔ : IsBoundary Δ) {ι : Type*} [Finite ι] (I : ι → X.IdealSheafData)
    (hI : ∀ j, I j ≠ ⊥) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ X), IsLogResolution sX Δ g ∧ IsProjectiveMorphism g ∧
      (∀ j, Stacks.Divisors.IsEffectiveCartierDivisor ((I j).comap g)) ∧
      ∃ (hg : IsBirationalMorphism g) (G : Divisor Y),
        (∀ P, G.coeff P = 0 ∨ G.coeff P = 1) ∧
        (∀ P, G.coeff P = 1 ↔
          (birationalInverseTransform g hg Δ).coeff P ≠ 0 ∨ IsExceptionalPrimeDivisor sX g P ∨
            ∃ j, (P.support : Set Y) ⊆ ((I j).comap g).support) ∧
        (∀ j, ∀ y ∈ (((I j).comap g).support : Set Y), ∃ P, G.coeff P = 1 ∧ y ∈ P.support) ∧
        IsSNCDivisor (g ≫ sX) G := by
  classical
  have hXv : Mori.IsVariety k sX := hX.1
  haveI : IsIntegral X := hXv.toIsIntegral
  haveI : LocallyOfFiniteType sX := hXv.toLocallyOfFiniteType
  haveI : Fintype ι := Fintype.ofFinite ι
  obtain ⟨Y, g, S, hYv', hgsm, hgproj, hgbir, hcart, hSsnc, hExc, hΔS, hIjS⟩ :=
    exists_isProjectiveMorphism_isSNCSubset sX hXv Δ I hI
  haveI : IsIntegral Y := hYv'.toIsIntegral
  haveI : LocallyOfFiniteType (g ≫ sX) := hYv'.toLocallyOfFiniteType
  haveI : IsProper g := isProper_of_isProjectiveMorphism g hgproj
  obtain ⟨n₀, hn₀⟩ := exists_topologicalKrullDim_eq sX hXv
  have hsupp_sub : ∀ P : Mori.PrimeDivisor Y, P.genericPoint ∈ (S : Set Y) →
      (P.support : Set Y) ⊆ S := fun P hP => by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact closure_minimal (Set.singleton_subset_iff.mpr hP) S.isClosed
  have hQ : ∀ P : Mori.PrimeDivisor Y,
      ((birationalInverseTransform g hgbir Δ).coeff P ≠ 0 ∨ IsExceptionalPrimeDivisor sX g P ∨
        ∃ j, (P.support : Set Y) ⊆ ((I j).comap g).support) → (P.support : Set Y) ⊆ S := by
    rintro P (h | h | ⟨j, h⟩)
    · obtain ⟨Q, hQ, hgQ⟩ :=
        exists_map_genericPoint_eq_of_birationalInverseTransform_ne_zero hXv hYv' hgbir h
      refine hsupp_sub P (hΔS _ ?_)
      rw [hgQ]
      exact DivisorWithCoeffs.support_subset_supp hQ (genericPoint_mem_support Q)
    · exact hsupp_sub P (hExc (genericPoint_mem_exceptionalSet hn₀ h))
    · exact h.trans (hIjS j)
  obtain ⟨G, hG01, hGiff, hGsnc⟩ := exists_isSNCDivisor_of_isSNCSubset hgsm hSsnc _ hQ
  obtain ⟨G', hG'01, hG'iff, hG'snc⟩ := exists_isSNCDivisor_of_isSNCSubset hgsm hSsnc
    (fun P => (birationalInverseTransform g hgbir Δ).coeff P ≠ 0 ∨
      IsExceptionalPrimeDivisor sX g P)
    (fun P hP => hQ P (hP.elim Or.inl fun h => Or.inr (Or.inl h)))
  have hcover : ∀ j, ∀ y ∈ (((I j).comap g).support : Set Y),
      ∃ P, G.coeff P = 1 ∧ y ∈ P.support := fun j y hy => by
    obtain ⟨P, hPj, hyP⟩ := exists_primeDivisor_subset_support_mem hSsnc (hcart j) (hIjS j) hy
    exact ⟨P, (hGiff P).mpr (Or.inr (Or.inr ⟨j, hPj⟩)), hyP⟩
  exact ⟨Y, g, ⟨⟨hX, hΔ⟩, hYv', hgsm, inferInstance, hgbir, G', hG'01, hG'iff, hG'snc⟩, hgproj,
    hcart, hgbir, G, hG01, hGiff, hcover, hGsnc⟩

/-- Let `X` be a normal variety over a field `k` of characteristic zero and `B` a boundary on `X`.
Then the log variety `(X, B)` has a log resolution `f : Y ⟶ X` with `f` a projective morphism. -/
@[mmp "lem_mmp_fa_log_resolution"]
public theorem exists_isLogResolution_isProjectiveMorphism {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : Mori.IsNormalVariety k sX) (B : Mori.RDivisor X)
    (hB : IsBoundary B) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsLogResolution sX B f ∧ IsProjectiveMorphism f :=
  have ⟨Y, g, hg, hgp, _⟩ := exists_isLogResolution_isEffectiveCartierDivisor_comap sX hX B hB
    (ι := PEmpty.{1}) PEmpty.elim PEmpty.rec
  ⟨Y, g, hg, hgp⟩

end MMP.Flips

end
