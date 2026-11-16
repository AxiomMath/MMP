module

import StacksFrontier.AlgebraicGeometry.Limits.ChowLemmaAffineBase
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Intersection.Nef
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.Divisor.Pullback
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.Monomial
import MMP.AlgebraicGeometry.Positivity.AmpleNumerical
import MMP.AlgebraicGeometry.Resolution.Principalization.ResolutionPrincipalization
import MMP.AlgebraicGeometry.Resolution.ProjectiveLogResolution
import MMP.AlgebraicGeometry.Resolution.DivisorTuple.TransformationSequence
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothGeometry
import MMP.AlgebraicGeometry.Morphisms.ChowLemma
import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
import MMP.AlgebraicGeometry.Resolution.OrderReduction.MonomialSmoothPullback
import MMP.AlgebraicGeometry.Intersection.KleimanTransversality
import MMP.AlgebraicGeometry.MMP.BasepointFree.RelativelyFreeTwist
import MMP.AlgebraicGeometry.Divisor.SmoothWeilCartier
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalAntiampleDivisor
import MMP.AlgebraicGeometry.Morphisms.ValuativeCentre
import MMP.AlgebraicGeometry.Positivity.BigAmplePlusEffective
import MMP.AlgebraicGeometry.Resolution.OrderUpperSemicontinuous
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
import MMP.AlgebraicGeometry.Divisor.SNC
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.Resolution.SNCWeight.StratumBlowup
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafSections

/-!
# Projective log resolutions adapted to an ideal, with an ample boundary subtraction

Let `X` be a proper normal variety over an algebraically closed field `k` of characteristic
zero, `Δ` a `ℚ`-divisor on `X`, `I ⊆ 𝒪_X` a nonzero ideal sheaf and `B` a nef and big
`ℚ`-Cartier `ℚ`-divisor on `X`. Then there are a log resolution `f : Y ⟶ X` of `(X, Δ)` with `Y`
projective over `k` and an effective Cartier divisor `D_I` on `Y` with `f⁻¹I · 𝒪_Y = 𝒪_Y(-D_I)`,
distinct prime divisors `F₁, …, F_s` on `Y` with `F₁ + ⋯ + F_s` snc and whose union contains
`Ex(f) ∪ f⁻¹(Supp Δ) ∪ Supp D_I`, and rationals `p₁, …, p_s > 0` such that `f^*B - ∑ⱼ pⱼ Fⱼ` is
ample.

## Main results

* `MMP.Mori.exists_isLogResolution_isAmple_pullback_sub_sum`: the statement above.

## Implementation notes

* `X` carries its structure morphism `sX : X ⟶ Spec k`, and `Y` the composite `f ≫ sX`.
* The ideal sheaf `f⁻¹I · 𝒪_Y` is `Scheme.IdealSheafData.comap I f`, and `𝒪_Y(-D_I)` for the
  effective divisor `D_I = ∑_E d_E E` is `MMP.Resolution.divisorIdeal`, the product
  `∏_E I_E^{d_E}` of the powers of the ideal sheaves of its components; on the smooth `Y` this is
  the invertible sheaf `𝒪_Y(-D_I)`.
* The prime divisors `F₁, …, F_s` are a finite set `F` of prime divisors of `Y`, and the
  rationals `pⱼ` a function `p` on prime divisors, positive on `F`.
* The pull-back `f^*B` is a `ℚ`-divisor `fB` with `MMP.Mori.QDivisor.IsPullback`; the pull-back
  of a `ℚ`-Cartier `ℚ`-divisor along a birational morphism exists and is unique
  (`MMP.Mori.QDivisor.IsQCartier.existsUnique_isPullback`).
* The instances `IsLocallyNoetherian Y`, `IsNormal Y` and `CompactSpace Y`, under which divisors
  and ampleness on `Y` are stated, are part of the conclusion; they follow from `Y` smooth and
  projective over `k`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proofs of 3.4
  and 3.5
-/

public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Resolution

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Mori

/-! ### Topology -/

/-- On an irreducible space, the generic point lies in every nonempty open. -/
private theorem genericPoint_mem_of_nonempty {X : Scheme.{u}} [IrreducibleSpace X] (V : X.Opens)
    (hV : (V : Set X).Nonempty) : genericPoint X ∈ V :=
  ((genericPoint_spec X).mem_open_set_iff V.isOpen).2 (by simpa using hV)

/-- A union of two closed sets of pure codimension one is of pure codimension one. -/
private theorem isPureCodimOne_sup {T : Type*} [TopologicalSpace T] {S S' : Closeds T}
    (hS : IsPureCodimOne S) (hS' : IsPureCodimOne S') : IsPureCodimOne (S ⊔ S') := by
  intro W hW
  have hsub : (W : Set T) ⊆ (S : Set T) ∪ S' := by simpa using hW.prop
  rcases (isPreirreducible_iff_isClosed_union_isClosed.1 W.isIrreducible.isPreirreducible)
    _ _ S.isClosed S'.isClosed hsub with h | h
  · exact hS W ⟨h, fun W' hW' hle => hW.2 (hW'.trans (by simp)) hle⟩
  · exact hS' W ⟨h, fun W' hW' hle => hW.2 (hW'.trans (by simp)) hle⟩

private lemma isPreirreducible_preimage_val {Y : Type*} [TopologicalSpace Y] {C W : Set Y}
    (hW : IsPreirreducible W) (hWC : W ⊆ C) : IsPreirreducible (Subtype.val ⁻¹' W : Set C) := by
  rintro u v hu hv ⟨a, ha, hau⟩ ⟨b, hb, hbv⟩
  obtain ⟨u', hu', rfl⟩ := isOpen_induced_iff.mp hu
  obtain ⟨v', hv', rfl⟩ := isOpen_induced_iff.mp hv
  obtain ⟨y, hyW, hyu, hyv⟩ := hW u' v' hu' hv' ⟨a, ha, hau⟩ ⟨b, hb, hbv⟩
  exact ⟨⟨y, hWC hyW⟩, hyW, hyu, hyv⟩

/-- An irreducible closed set contained in a closed set lies in an irreducible closed subset
maximal in it. -/
private lemma exists_maximal_ge {Y : Type*} [TopologicalSpace Y] {C : Set Y} (hC : IsClosed C)
    (Z : IrreducibleCloseds Y) (hZ : (Z : Set Y) ⊆ C) :
    ∃ W : IrreducibleCloseds Y, Maximal (fun W' : IrreducibleCloseds Y ↦ (W' : Set Y) ⊆ C) W ∧
      Z ≤ W := by
  obtain ⟨t, ht, hxt, hmax⟩ := exists_preirreducible (Subtype.val ⁻¹' (Z : Set Y) : Set C)
    (isPreirreducible_preimage_val Z.isIrreducible.isPreirreducible hZ)
  obtain ⟨z, hz⟩ := Z.isIrreducible.nonempty
  let W : IrreducibleCloseds Y := ⟨closure (Subtype.val '' t),
    (IsIrreducible.closure ⟨⟨z, ⟨z, hZ hz⟩, hxt hz, rfl⟩,
      ht.image _ continuous_subtype_val.continuousOn⟩), isClosed_closure⟩
  have hWC : (W : Set Y) ⊆ C := closure_minimal (by rintro _ ⟨y, -, rfl⟩; exact y.2) hC
  refine ⟨W, ⟨hWC, fun W' hW'C hWW' y hy ↦ ?_⟩, fun y hy ↦ subset_closure ⟨⟨y, hZ hy⟩, hxt hy, rfl⟩⟩
  have := hmax _ (isPreirreducible_preimage_val W'.isIrreducible.isPreirreducible hW'C)
    fun y hy ↦ hWW' (subset_closure ⟨y, hy, rfl⟩)
  have : (⟨y, hW'C hy⟩ : C) ∈ t := by rw [← this]; exact hy
  exact subset_closure ⟨_, this, rfl⟩

/-! ### Snc subsets -/

section SNC

/-- The support of a prime divisor, as an irreducible closed subset. -/
private noncomputable def primeIrr {X : Scheme.{u}} (E : AlgebraicGeometry.PrimeDivisor X) :
    IrreducibleCloseds X :=
  IrreducibleCloseds.closureSingleton E.genericPoint

private lemma coe_primeIrr {X : Scheme.{u}} (E : AlgebraicGeometry.PrimeDivisor X) :
    (primeIrr E : Set X) = E.support := by
  rw [E.support_eq_closure]
  rfl

private lemma codimension_primeIrr {X : Scheme.{u}} (E : AlgebraicGeometry.PrimeDivisor X) :
    codimension (primeIrr E) = 1 := E.codimension_one

private lemma exists_mem_of_subset_iUnion {X : Scheme.{u}}
    {s : Finset (AlgebraicGeometry.PrimeDivisor X)}
    (W : IrreducibleCloseds X) (hW : (W : Set X) ⊆ ⋃ E ∈ s, E.support) :
    ∃ E ∈ s, W ≤ primeIrr E := by
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
  exact ⟨E, hE, fun x hx ↦ by
    change x ∈ (primeIrr E : Set X); rw [coe_primeIrr]; exact hWz hx⟩

/-- A prime divisor contained in a finite union of prime divisors is one of them. -/
private lemma mem_of_support_subset_iUnion {X : Scheme.{u}}
    {s : Finset (AlgebraicGeometry.PrimeDivisor X)} {E : AlgebraicGeometry.PrimeDivisor X}
    (h : (E.support : Set X) ⊆ ⋃ F ∈ s, F.support) : E ∈ s := by
  obtain ⟨F, hF, hEF⟩ := exists_mem_of_subset_iUnion (primeIrr E) (by rwa [coe_primeIrr])
  have : E = F := MMP.Fourfold.SNCWeight.PrimeDivisorUnion.eq_of_support_subset (by
    rw [← coe_primeIrr, ← coe_primeIrr]
    exact hEF)
  exact this ▸ hF

variable {k : Type u} [Field k]

/-- A closed subset of pure codimension one of an snc divisor is an snc divisor. -/
private lemma isSNCSubset_of_le {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {S C : Closeds X}
    (hS : IsSNCSubset sX S) (hC : IsPureCodimOne C) (hCS : C ≤ S) : IsSNCSubset sX C := by
  classical
  rcases hS with rfl | ⟨s, hs, hsnc⟩
  · exact Or.inl (le_bot_iff.mp hCS)
  right
  refine ⟨s.filter (fun E ↦ E.support ⊆ C), ?_, ?_⟩
  · refine subset_antisymm (fun x hx ↦ ?_) fun x hx ↦ ?_
    · obtain ⟨E, hE, hxE⟩ := Set.mem_iUnion₂.mp hx
      exact (Finset.mem_filter.mp hE).2 hxE
    · obtain ⟨W, hW, hxW⟩ := exists_maximal_ge C.isClosed
        (IrreducibleCloseds.closureSingleton x) (by
          change closure {x} ⊆ (C : Set X)
          exact closure_minimal (by simpa using hx) C.isClosed)
      have hxW' : x ∈ (W : Set X) := hxW (subset_closure rfl)
      obtain ⟨E, hE, hWE⟩ := exists_mem_of_subset_iUnion W (hs ▸ hW.1.trans hCS)
      have hWE' : W = primeIrr E := by
        by_contra hne
        have hlt : W < primeIrr E := lt_of_le_of_ne hWE hne
        have := Order.coheight_add_one_le hlt
        rw [← codimension_eq_coheight, ← codimension_eq_coheight, codimension_primeIrr,
          hC W hW] at this
        exact absurd this (by decide)
      refine Set.mem_iUnion₂.mpr ⟨E, Finset.mem_filter.mpr ⟨hE, ?_⟩, ?_⟩
      · rw [← coe_primeIrr, ← hWE']
        exact hW.1
      · rw [← coe_primeIrr, ← hWE']
        exact hxW'
  · refine hsnc.of_support_subset ?_
    intro E hE
    rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply] at hE ⊢
    simp only [Finsupp.single_apply] at hE ⊢
    rw [Finset.sum_ite_eq'] at hE ⊢
    split_ifs at hE with h1
    · rw [if_pos (Finset.mem_filter.mp h1).1]
      exact one_ne_zero
    · exact absurd rfl hE

end SNC

/-! ### Isomorphisms over opens and biregular loci -/

/-- A morphism which is an isomorphism over a nonempty open has points over it. -/
private theorem nonempty_preimage_of_isIso_restrict {X Y : Scheme.{u}} (g : Y ⟶ X) (V : X.Opens)
    [IsIso (g ∣_ V)] (hV : (V : Set X).Nonempty) : ((g ⁻¹ᵁ V : Y.Opens) : Set Y).Nonempty := by
  obtain ⟨x, hx⟩ := hV
  exact ⟨((inv (g ∣_ V)) ⟨x, hx⟩).1, ((inv (g ∣_ V)) ⟨x, hx⟩).2⟩

/-- On an irreducible scheme, the generic point lies over every nonempty open over which a
morphism is an isomorphism. -/
private theorem genericPoint_mem_preimage {X Y : Scheme.{u}} [IrreducibleSpace Y] (g : Y ⟶ X)
    (V : X.Opens) [IsIso (g ∣_ V)] (hV : (V : Set X).Nonempty) :
    genericPoint Y ∈ g ⁻¹ᵁ V :=
  genericPoint_mem_of_nonempty _ (nonempty_preimage_of_isIso_restrict g V hV)

/-- A morphism of irreducible schemes which is an isomorphism over a nonempty open is
birational. -/
private theorem isBirationalMorphism_of_isIso_restrict {X Y : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (g : Y ⟶ X) (V : X.Opens) [IsIso (g ∣_ V)]
    (hV : (V : Set X).Nonempty) : IsBirationalMorphism g := by
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE g _ _
    (nonempty_preimage_of_isIso_restrict g V hV) hV le_rfl ?_
  rwa [Scheme.Hom.resLE_eq_morphismRestrict]

/-- A composite of isomorphisms over `V` and over its inverse image is an isomorphism over `V`. -/
private theorem isIso_restrict_comp {X Y W : Scheme.{u}} (h : W ⟶ Y) (g : Y ⟶ X) (V : X.Opens)
    [IsIso (g ∣_ V)] [IsIso (h ∣_ g ⁻¹ᵁ V)] : IsIso ((h ≫ g) ∣_ V) := by
  rw [morphismRestrict_comp]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ ‹_› ‹_›

/-- The biregular locus of a morphism from a smooth scheme lies in the smooth locus. -/
private theorem biregularLocus_le_smoothLocus {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (f : Y ⟶ X) [LocallyOfFiniteType (f ≫ sX)]
    (hY : IsSmoothScheme (f ≫ sX)) : biregularLocus f ≤ smoothLocus sX := by
  set V := biregularLocus f
  haveI : IsIso (f ∣_ V) := isBiregular_biregularLocus f
  have : LocallyOfFinitePresentation (f ≫ sX) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := f ≫ sX)).mpr inferInstance
  haveI : Smooth (f ≫ sX) := (isSmoothScheme_iff _).1 hY
  haveI h : Smooth ((f ∣_ V) ≫ V.ι ≫ sX) := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    infer_instance
  have e : V.ι ≫ sX = inv (f ∣_ V) ≫ ((f ∣_ V) ≫ V.ι ≫ sX) := by simp
  refine le_smoothLocus _ ?_
  rw [e]
  infer_instance

/-- The inverse image of the smooth locus under a morphism which is an isomorphism over an open
`V ⊆ X_sm` contains the inverse image of `V`. -/
private theorem preimage_le_smoothLocus {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (q : Y ⟶ X) (V : X.Opens) [IsIso (q ∣_ V)]
    (hV : V ≤ smoothLocus sX) : q ⁻¹ᵁ V ≤ smoothLocus (q ≫ sX) := by
  have : LocallyOfFinitePresentation sX :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := sX)).mpr inferInstance
  haveI : Smooth (V.ι ≫ sX) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq,
      ← smoothLocus_eq_smoothLocus]
    exact top_le_iff.1 fun x _ => hV x.2
  refine le_smoothLocus _ ?_
  rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  infer_instance

/-! ### Exceptional sets of composites -/

section Exceptional

/-- If `a ≫ b` is an isomorphism, `a` is dominant, the source of `b` is reduced and `b` is
separated, then `b` is an isomorphism. -/
private lemma isIso_of_isIso_comp {A B V : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ V) [IsIso (a ≫ b)]
    [IsDominant a] [IsReduced B] [IsSeparated b] : IsIso b := by
  refine ⟨⟨inv (a ≫ b) ≫ a, ?_, by simp⟩⟩
  refine ext_of_isDominant_of_isSeparated b ?_ a ?_
  · simp
  · rw [← Category.assoc, IsIso.hom_inv_id_assoc, Category.comp_id]

/-- If `h ≫ g` is an isomorphism over `V`, with `h` dominant, `X'` reduced and `g` separated,
then `g` is an isomorphism over `V` and `h` over `g⁻¹(V)`. -/
private lemma isBiregular_of_isBiregular_comp {Y X' X : Scheme.{u}} (h : Y ⟶ X') (g : X' ⟶ X)
    [IsDominant h] [IsReduced X'] [IsSeparated g] {V : X.Opens}
    (hV : IsBiregular (h ≫ g) V) : IsBiregular g V ∧ IsBiregular h (g ⁻¹ᵁ V) := by
  unfold IsBiregular at hV ⊢
  rw [morphismRestrict_comp] at hV
  have : IsDominant (h ∣_ g ⁻¹ᵁ V) := IsZariskiLocalAtTarget.restrict ‹IsDominant h› _
  have : IsSeparated (g ∣_ V) := IsZariskiLocalAtTarget.restrict ‹IsSeparated g› _
  have := @isIso_of_isIso_comp _ _ _ (h ∣_ g ⁻¹ᵁ V) (g ∣_ V) hV _ _ _
  exact ⟨this, @IsIso.of_isIso_comp_right _ _ _ _ _ _ (g ∣_ V) this hV⟩

/-- The exceptional set of a composite: `Ex(g ∘ h) = Ex(h) ∪ h⁻¹(Ex(g))`. -/
private lemma exceptionalSet_comp {Y X' X : Scheme.{u}} (h : Y ⟶ X') (g : X' ⟶ X)
    [IsDominant h] [IsReduced X'] [IsSeparated g] [UniversallyClosed g] :
    exceptionalSet (h ≫ g) = exceptionalSet h ⊔ (exceptionalSet g).preimage h.continuous := by
  apply SetLike.coe_injective
  ext y
  change y ∈ exceptionalSet (h ≫ g) ↔ y ∈ exceptionalSet h ∨ h y ∈ exceptionalSet g
  simp only [mem_exceptionalSet]
  constructor
  · intro hy
    by_contra hne
    push Not at hne
    obtain ⟨hyh, hyg⟩ := hne
    apply hy
    have hcl : IsClosed (g '' (biregularLocus h : Set X')ᶜ) :=
      g.isClosedMap _ (biregularLocus h).isOpen.isClosed_compl
    let W : X.Opens := biregularLocus g ⊓ ⟨_, hcl.isOpen_compl⟩
    have hWg : IsBiregular g W := isBiregular_iff_le_biregularLocus.mpr inf_le_left
    have hWh : IsBiregular h (g ⁻¹ᵁ W) := by
      refine isBiregular_iff_le_biregularLocus.mpr ?_
      intro x hx
      by_contra hxU
      exact hx.2 ⟨x, hxU, rfl⟩
    have hiso : IsBiregular (h ≫ g) W := by
      unfold IsBiregular at *
      rw [morphismRestrict_comp]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ hWh hWg
    refine le_biregularLocus hiso ⟨hyg, ?_⟩
    rintro ⟨x, hx, hxy⟩
    have : IsIso (g ∣_ biregularLocus g) := isBiregular_biregularLocus g
    have hxy' : g x = g (h y) := hxy.trans (Scheme.Hom.comp_apply h g y)
    have hx' : g x ∈ biregularLocus g := hxy' ▸ hyg
    have hinj := (g ∣_ biregularLocus g).isOpenEmbedding.injective
      (a₁ := (⟨x, hx'⟩ : g ⁻¹ᵁ biregularLocus g)) (a₂ := ⟨h y, hyg⟩)
    have : x = h y := congrArg Subtype.val (hinj (Subtype.ext
      ((morphismRestrict_base_coe g _ _).trans (hxy'.trans
        (morphismRestrict_base_coe g (biregularLocus g) ⟨h y, hyg⟩).symm))))
    exact hx (this ▸ hyh)
  · intro hy hmem
    have hb := isBiregular_of_isBiregular_comp h g (isBiregular_biregularLocus (h ≫ g))
    rcases hy with hy | hy
    · exact hy (le_biregularLocus hb.2 hmem)
    · exact hy (le_biregularLocus hb.1 hmem)

end Exceptional

/-- If `q` is an isomorphism over `V` and the biregular locus of `g ≫ q` lies in `V`, then `g` is
an isomorphism over the inverse image of the biregular locus of `g ≫ q`. -/
private theorem preimage_biregularLocus_comp_le {W Y X : Scheme.{u}} (g : W ⟶ Y) (q : Y ⟶ X)
    (V : X.Opens) [IsIso (q ∣_ V)] (hV : biregularLocus (g ≫ q) ≤ V) :
    q ⁻¹ᵁ biregularLocus (g ≫ q) ≤ biregularLocus g := by
  set B := biregularLocus (g ≫ q)
  have h : IsIso ((g ≫ q) ∣_ B) := isBiregular_biregularLocus (g ≫ q)
  rw [morphismRestrict_comp] at h
  haveI : IsIso (q ∣_ B) := MMP.Resolution.TupleResolutionAux.isIso_restrict_of_le q hV
  haveI : IsIso (g ∣_ q ⁻¹ᵁ B) := @IsIso.of_isIso_comp_right _ _ _ _ _ _ (q ∣_ B) _ h
  exact le_biregularLocus this

/-- If `q` is an isomorphism over `V`, a point of `W` over `V` at which `g` is biregular lies over
the biregular locus of `g ≫ q`. -/
private theorem mem_biregularLocus_comp {W Y X : Scheme.{u}} (g : W ⟶ Y) (q : Y ⟶ X)
    (V : X.Opens) [IsIso (q ∣_ V)] (y : Y) (hyV : q y ∈ V) (hy : y ∈ biregularLocus g) :
    q y ∈ biregularLocus (g ≫ q) := by
  set N := q ⁻¹ᵁ V
  set j : N.toScheme ⟶ X := (q ∣_ V) ≫ V.ι with hj
  have hjapp : ∀ z : N.toScheme, j z = q z.1 := fun z => by
    rw [hj, morphismRestrict_ι, Scheme.Hom.comp_apply]
    rfl
  set O : X.Opens := j ''ᵁ (N.ι ⁻¹ᵁ biregularLocus g) with hO
  have hOV : O ≤ V := by
    rintro _ ⟨z, -, rfl⟩
    exact Eq.mpr (congrArg (· ∈ V) (hjapp z)) z.2
  have hqO : q ⁻¹ᵁ O ≤ biregularLocus g := by
    intro y' hy'
    obtain ⟨z, hz, hzy⟩ := hy'
    have hzq : q z.1 = q y' := (hjapp z).symm.trans hzy
    have hy'N : y' ∈ N := by
      show q y' ∈ V
      rw [← hzq]
      exact z.2
    have : z = (⟨y', hy'N⟩ : N.toScheme) :=
      j.isOpenEmbedding.injective (hzy.trans (hjapp ⟨y', hy'N⟩).symm)
    rwa [this] at hz
  haveI : IsIso (q ∣_ O) := MMP.Resolution.TupleResolutionAux.isIso_restrict_of_le q hOV
  haveI : IsIso (g ∣_ biregularLocus g) := isBiregular_biregularLocus g
  haveI : IsIso (g ∣_ q ⁻¹ᵁ O) := MMP.Resolution.TupleResolutionAux.isIso_restrict_of_le g hqO
  haveI := isIso_restrict_comp g q O
  exact le_biregularLocus this ⟨⟨y, hyV⟩, hy, hjapp _⟩

/-- **The exceptional set of a composite.** If `q` is an isomorphism over `V` and `g ≫ q` is
biregular only over `V`, then the exceptional set of `g ≫ q` is the inverse image of `X ∖ V`
together with the exceptional set of `g`. -/
private theorem coe_exceptionalSet_comp {W Y X : Scheme.{u}} (g : W ⟶ Y) (q : Y ⟶ X)
    (V : X.Opens) [IsIso (q ∣_ V)] (hV : biregularLocus (g ≫ q) ≤ V) :
    (exceptionalSet (g ≫ q) : Set W) = (g ≫ q) ⁻¹' (V.compl : Set X) ∪ exceptionalSet g := by
  ext y
  change q (g y) ∉ biregularLocus (g ≫ q) ↔ q (g y) ∉ V ∨ g y ∉ biregularLocus g
  refine ⟨fun hy => ?_, ?_⟩
  · by_contra hc
    push Not at hc
    exact hy (mem_biregularLocus_comp g q V (g y) hc.1 hc.2)
  · rintro (hy | hy) hy'
    · exact hy (hV hy')
    · exact hy (preimage_biregularLocus_comp_le g q V hV hy')

/-- The support of the pulled-back ideal of a closed subset is its inverse image. -/
private theorem coe_support_comap_vanishingIdeal {X Y : Scheme.{u}} (q : Y ⟶ X) (Z : Closeds X) :
    (((Scheme.IdealSheafData.vanishingIdeal Z).comap q).support : Set Y) = q ⁻¹' Z := by
  rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]

/-! ### Invertible ideals -/

/-- In a local domain, a factor of a nonzero principal ideal is a nonzero principal ideal. -/
private theorem exists_eq_span_of_mul_eq_span {R : Type*} [CommRing R] [IsDomain R]
    [IsLocalRing R] {I J : Ideal R} {t : R} (ht : t ≠ 0) (h : I * J = Ideal.span {t}) :
    ∃ a : R, a ≠ 0 ∧ I = Ideal.span {a} := by
  have hmem : ∀ a ∈ I, ∀ b ∈ J, ∃ c, a * b = t * c := fun a ha b hb => by
    have : a * b ∈ Ideal.span {t} := h ▸ Ideal.mul_mem_mul ha hb
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 this
    exact ⟨c, by rw [← hc, mul_comm]⟩
  have hex : ∃ a ∈ I, ∃ b ∈ J, ∃ u : R, IsUnit u ∧ a * b = t * u := by
    by_contra hne
    push Not at hne
    have hle : I * J ≤ Ideal.span {t} * IsLocalRing.maximalIdeal R := by
      refine Ideal.mul_le.2 fun a ha b hb => ?_
      obtain ⟨c, hc⟩ := hmem a ha b hb
      have hcu : ¬ IsUnit c := fun hu => hne a ha b hb c hu hc
      rw [hc]
      exact Ideal.mem_span_singleton_mul.2 ⟨c, (IsLocalRing.mem_maximalIdeal c).2 hcu, rfl⟩
    rw [h] at hle
    obtain ⟨z, hz, htz⟩ := Ideal.mem_span_singleton_mul.1 (hle (Ideal.mem_span_singleton_self t))
    have hz1 : z = 1 := by
      have : t * (z - 1) = 0 := by rw [mul_sub, htz, mul_one, sub_self]
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left ht)
    exact (IsLocalRing.mem_maximalIdeal z).1 hz (hz1 ▸ isUnit_one)
  obtain ⟨a₀, ha₀, b₀, hb₀, u, hu, hab⟩ := hex
  refine ⟨a₀, fun h0 => ?_, le_antisymm (fun a ha => ?_) (Ideal.span_le.2 (by simpa using ha₀))⟩
  · rw [h0, zero_mul] at hab
    exact (mul_ne_zero ht hu.ne_zero) hab.symm
  · obtain ⟨s, hs⟩ := hmem a ha b₀ hb₀
    have h2 : a * u = a₀ * s := mul_left_cancel₀ ht (by linear_combination a₀ * hs - a * hab)
    rw [Ideal.mem_span_singleton']
    refine ⟨s * ↑hu.unit⁻¹, ?_⟩
    calc s * ↑hu.unit⁻¹ * a₀ = (a₀ * s) * ↑hu.unit⁻¹ := by ring
      _ = (a * u) * ↑hu.unit⁻¹ := by rw [h2]
      _ = a := by rw [mul_assoc, IsUnit.mul_val_inv, mul_one]

/-- **Krull's height theorem, geometric form.** On a locally noetherian scheme, if
`closure {η}` is an irreducible component of the support of `I`, then the coheight of `η` is at
most the number of generators of `I` on any affine open containing `η`. -/
private theorem coheight_le_spanRank_ideal {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) {η : X}
    (hη : Maximal (fun s : Set X => IsIrreducible s ∧ s ⊆ (I.support : Set X)) (closure {η}))
    (W : X.affineOpens) (hηW : η ∈ W.1) :
    Order.coheight η ≤ Cardinal.toENat (Submodule.spanRank (I.ideal W)) := by
  have hW : IsAffineOpen W.1 := W.2
  have : IsNoetherianRing Γ(X, W.1) := IsLocallyNoetherian.component_noetherian W
  set x := hW.primeIdealOf ⟨η, hηW⟩ with hx_def
  have hx : hW.fromSpec x = η := hW.fromSpec_primeIdealOf ⟨η, hηW⟩
  have hsupp : ∀ y : Spec Γ(X, W.1),
      hW.fromSpec y ∈ (I.support : Set X) ↔ (I.ideal W : Set Γ(X, W.1)) ⊆ y.asIdeal := by
    intro y
    have hyW : hW.fromSpec y ∈ W.1 := by
      rw [← SetLike.mem_coe, ← hW.range_fromSpec]
      exact ⟨y, rfl⟩
    rw [SetLike.mem_coe, Scheme.IdealSheafData.mem_support_iff_of_mem hyW, ← Set.mem_preimage, hW.fromSpec_preimage_zeroLocus]
    rfl
  have hηsupp : η ∈ (I.support : Set X) := hη.prop.2 (subset_closure rfl)
  have hmin : x.asIdeal ∈ (I.ideal W).minimalPrimes := by
    refine ⟨⟨x.isPrime, (hsupp x).mp (hx ▸ hηsupp)⟩, ?_⟩
    rintro q ⟨hq, hJq⟩ hqx
    let y : Spec Γ(X, W.1) := ⟨q, hq⟩
    have hyx : y ⤳ x := (PrimeSpectrum.le_iff_specializes y x).mp hqx
    have hyη : hW.fromSpec y ⤳ η := hx ▸ hyx.map (hW.fromSpec).continuous
    have hysupp : hW.fromSpec y ∈ (I.support : Set X) := (hsupp y).mpr hJq
    have hcl : closure {hW.fromSpec y} ⊆ closure {η} := by
      refine hη.2 ⟨isIrreducible_singleton.closure, ?_⟩
        (specializes_iff_closure_subset.mp hyη)
      exact (I.support.isClosed.closure_subset_iff).mpr (Set.singleton_subset_iff.mpr hysupp)
    have hηy : η ⤳ hW.fromSpec y := specializes_iff_closure_subset.mpr hcl
    rw [← hx] at hηy
    have hxy : x ⤳ y := hW.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp hηy
    exact (PrimeSpectrum.le_iff_specializes x y).mpr hxy
  have hle := Ideal.height_le_spanRank_toENat_of_mem_minimal_primes _ _ hmin
  rwa [idealHeight_eq_coheight _ x,
    show Order.coheight (α := Spec Γ(X, W.1)) x = Order.coheight η from
      (coheight_eq_of_isOpenImmersion (x := x) hW.fromSpec).symm.trans (congrArg _ hx)] at hle

/-- **The support of an effective Cartier divisor is of pure codimension one** (Krull's principal
ideal theorem), on an integral locally noetherian scheme, when it misses the generic point. -/
private theorem isPureCodimOne_support_of_isEffectiveCartierDivisor {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) (hgen : genericPoint X ∉ I.support) :
    IsPureCodimOne I.support := by
  intro W hW
  set η := W.isIrreducible.genericPoint with hη
  have hηW : closure {η} = (W : Set X) := by
    have := W.isIrreducible.isGenericPoint_genericPoint_closure
    rwa [W.isClosed.closure_eq] at this
  have hWeq : W = IrreducibleCloseds.closureSingleton η :=
    IrreducibleCloseds.ext (by rw [IrreducibleCloseds.coe_closureSingleton, hηW])
  have hmax : Maximal (fun s : Set X => IsIrreducible s ∧ s ⊆ (I.support : Set X))
      (closure {η}) := by
    rw [hηW]
    refine ⟨⟨W.isIrreducible, hW.prop⟩, fun s ⟨hs, hsI⟩ hWs => ?_⟩
    have hle := hW.2 (y := ⟨closure s, hs.closure, isClosed_closure⟩)
      (closure_minimal hsI I.support.isClosed) (hWs.trans subset_closure)
    exact subset_closure.trans hle
  have hηI : η ∈ (I.support : Set X) := hmax.prop.2 (subset_closure rfl)
  rw [hWeq, Stacks.AlgebraicGeometry.CodimensionOneDivisor.codimension_closureSingleton_eq_coheight]
  obtain ⟨U, hU, hηU, f, -, hf⟩ :=
    Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor I hI η
  have h1 := coheight_le_spanRank_ideal I hmax ⟨U, hU⟩ hηU
  have hrank : Cardinal.toENat (Submodule.spanRank (I.ideal ⟨U, hU⟩)) ≤ 1 := by
    rw [hf]
    have := Submodule.spanRank_span_le_card (R := Γ(X, U)) ({f} : Set Γ(X, U))
    rw [Cardinal.mk_singleton] at this
    exact (Cardinal.toENat.monotone' this).trans (by simp)
  have h0 : Order.coheight η ≠ 0 := by
    intro h0
    rw [Order.coheight_eq_zero] at h0
    have hle : η ≤ genericPoint X := by
      rw [Scheme.le_iff_specializes]
      exact genericPoint_specializes η
    have h2 := h0 hle
    rw [Scheme.le_iff_specializes] at h2
    exact hgen (h2.mem_closed I.support.isClosed hηI)
  exact le_antisymm (h1.trans hrank) (Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 h0))

/-- On an integral locally noetherian scheme, if `P * Q = R` stalkwise with `R` an effective
Cartier divisor, then `P` is an effective Cartier divisor. -/
private theorem isEffectiveCartierDivisor_of_stalk_mul {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (P Q R : X.IdealSheafData)
    (hR : Stacks.Divisors.IsEffectiveCartierDivisor R)
    (h : ∀ x, IdealSheafData.stalk P x * IdealSheafData.stalk Q x = IdealSheafData.stalk R x) :
    Stacks.Divisors.IsEffectiveCartierDivisor P := by
  refine isEffectiveCartierDivisor_of_stalk_regular_principal P fun x _ => ?_
  obtain ⟨U, hU, hxU, t, ht, hRt⟩ :=
    Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor R hR x
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  have hstalk : IdealSheafData.stalk R x = Ideal.span {(X.presheaf.germ U x hxU).hom t} := by
    rw [IdealSheafData.stalk_eq_map_germ _ x ⟨U, hU⟩ hxU, hRt, Ideal.map_span,
      Set.image_singleton]
  have ht0 : (X.presheaf.germ U x hxU).hom t ≠ 0 := by
    intro h0
    refine ht.ne_zero (germ_injective_of_isIntegral X x hxU ?_)
    rw [h0, map_zero]
  obtain ⟨a, ha, hPa⟩ := exists_eq_span_of_mul_eq_span ht0 ((h x).trans hstalk)
  exact ⟨a, IsRegular.of_ne_zero ha, hPa⟩

/-! ### Projectivity -/

/-- A proper morphism from a scheme which immerses into some `ℙⁿ_k` over `k` is H-projective. -/
private theorem isProjectiveMorphism_of_isHQuasiProjective_comp {k : Type u} [Field k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (f : Y ⟶ X) [IsProper f]
    (h : IsHQuasiProjective (f ≫ sX)) : IsProjectiveMorphism f := by
  obtain ⟨n, i, hi, -, hcomm⟩ := h
  have hfst : IsImmersion (Limits.pullback.lift i f hcomm ≫
      Limits.pullback.fst (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) sX) := by
    rw [Limits.pullback.lift_fst]; exact hi
  have hmid : IsImmersion (Limits.pullback.lift i f hcomm) :=
    IsImmersion.of_comp _ (Limits.pullback.fst _ _)
  have hover : (Limits.pullback.lift i f hcomm ≫ (projectiveSpaceOverBaseChangeIso n sX).hom) ≫
      (projectiveSpaceOver n X ↘ X) = f := by
    rw [Category.assoc, projectiveSpaceOverBaseChangeIso_hom_over, Limits.pullback.lift_snd]
  exact isProjectiveMorphism_of_isImmersion_projectiveSpaceOver _ hover

/-! ### Chow's lemma -/

/-- **Chow's lemma for a variety.** A variety `X` over `k` admits a proper morphism `q : X₂ ⟶ X`
from a variety quasi-projective over `k` which is an isomorphism over a nonempty open. -/
private theorem exists_isQuasiProjective_isIso_restrict {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : AlgebraicGeometry.IsVariety k sX) :
    ∃ (X₂ : Scheme.{u}) (q : X₂ ⟶ X) (U : X.Opens), AlgebraicGeometry.IsVariety k (q ≫ sX) ∧
      IsProper q ∧ (U : Set X).Nonempty ∧ IsIso (q ∣_ U) ∧ IsQuasiProjective (q ≫ sX) := by
  haveI : IsIntegral X := hX.toIsIntegral
  haveI := hX.toIsSeparated
  haveI := hX.toLocallyOfFiniteType
  haveI := hX.toQuasiCompact
  obtain ⟨n, X₁, p₁, i, U, hp₁, -, hi, hcomm, hdense, hiso⟩ :=
    AlgebraicGeometry.hasChowModificationIsoOnDenseOpen_of_isAffine sX
  haveI := hiso
  haveI : IsProper p₁ := hp₁
  haveI : IsImmersion i := hi
  haveI : IsLocallyNoetherian X₁ := LocallyOfFiniteType.isLocallyNoetherian (p₁ ≫ sX)
  haveI : CompactSpace X₁ := QuasiCompact.compactSpace_of_compactSpace (p₁ ≫ sX)
  haveI : AlgebraicGeometry.IsNoetherian X₁ := {}
  haveI : Nonempty U := hdense.nonempty.to_subtype
  haveI : Nonempty (p₁ ⁻¹ᵁ U) := ⟨(inv (p₁ ∣_ U)) (Classical.arbitrary U)⟩
  haveI : IsIntegral (p₁ ⁻¹ᵁ U) := isIntegral_of_isOpenImmersion (p₁ ∣_ U)
  have hi1 : IsIso ((p₁ ⁻¹ᵁ U).ι.imageι ∣_ (p₁ ⁻¹ᵁ U)) :=
    Stacks.SchemeTheoreticImage.isIso_imageι_restrict _
  refine ⟨(p₁ ⁻¹ᵁ U).ι.image, (p₁ ⁻¹ᵁ U).ι.imageι ≫ p₁, U, ?_, inferInstance,
    hdense.nonempty, ?_, ?_⟩
  · rw [Category.assoc]
    exact Scheme.Hom.isVariety_image k _ (p₁ ≫ sX)
  · rw [morphismRestrict_comp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hi1 hiso
  · refine Stacks.HProjective.isQuasiProjective_of_isHQuasiProjective _
      ⟨n, (p₁ ⁻¹ᵁ U).ι.imageι ≫ i, inferInstance, inferInstance, ?_⟩
    rw [Category.assoc, ← hcomm, Category.assoc]

/-! ### Invertible ideals on smooth schemes -/

section DivisorialIdeals

open IsLocalRing

/-- The order of `𝔪^a` is `a` in a Noetherian local domain which is not a field. -/
private theorem idealOrder_maximalIdeal_pow {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsDomain R] (h : IsLocalRing.maximalIdeal R ≠ ⊥) (a : ℕ) :
    idealOrder (IsLocalRing.maximalIdeal R ^ a) = a := by
  refine le_antisymm (iSup₂_le fun j hj => ?_) (le_iSup₂_of_le
    (f := fun (j : ℕ) (_ : IsLocalRing.maximalIdeal R ^ a ≤ IsLocalRing.maximalIdeal R ^ j) =>
      (j : ℕ∞)) a le_rfl le_rfl)
  by_contra hlt
  have hlt' : a + 1 ≤ j := by exact_mod_cast Order.add_one_le_of_lt (not_le.1 hlt)
  have heq : IsLocalRing.maximalIdeal R ^ a = IsLocalRing.maximalIdeal R ^ (a + 1) :=
    le_antisymm (hj.trans (Ideal.pow_le_pow_right hlt')) (Ideal.pow_le_pow_right (by omega))
  have := MMP.Resolution.maximalIdeal_pow_injective h heq
  omega

/-- A point at which an ideal sheaf has nonzero order lies in its support. -/
private theorem mem_support_of_multAt_ne_zero {Y : Scheme.{u}} (J : Y.IdealSheafData) (y : Y)
    (h : multAt J y ≠ 0) : y ∈ (J.support : Set Y) := by
  by_contra hy
  apply h
  rw [multAt, (IdealSheafData.stalk_eq_top_iff_notMem_support J y).2 hy,
    MMP.Threefold.Resolution.idealOrder_top]

/-- In a discrete valuation ring the order of `(x)` is the valuation of `x`. -/
private theorem idealOrder_span_eq_addVal {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {x : R} (hx : x ≠ 0) :
    idealOrder (Ideal.span {x}) = IsDiscreteValuationRing.addVal R x := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  rw [IsDiscreteValuationRing.addVal_def _ u hϖ n rfl]
  have hm : maximalIdeal R = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have key : ∀ j : ℕ, Ideal.span {(u : R) * ϖ ^ n} ≤ maximalIdeal R ^ j ↔ j ≤ n := by
    intro j
    rw [hm, Ideal.span_singleton_pow, Ideal.span_singleton_le_span_singleton,
      Units.dvd_mul_left]
    exact _root_.pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit
  refine le_antisymm (iSup₂_le fun j hj => by exact_mod_cast (key j).1 hj) ?_
  exact le_iSup₂_of_le (f := fun (j : ℕ) (_ : Ideal.span {(u : R) * ϖ ^ n} ≤
    maximalIdeal R ^ j) => (j : ℕ∞)) n ((key n).2 le_rfl) le_rfl

/-- A regular local ring of dimension one is a discrete valuation ring. -/
private theorem isDiscreteValuationRing_of_ringKrullDim_eq_one {R : Type*} [CommRing R]
    [IsRegularLocalRing R] [IsDomain R] (h : ringKrullDim R = 1) : IsDiscreteValuationRing R := by
  haveI := IsRegularLocalRing.uniqueFactorizationMonoid R
  have hnf : ¬ IsField R := fun hf => by
    have := ringKrullDim_eq_zero_of_isField hf
    rw [h] at this
    exact absurd this (by decide)
  have e := (IsDiscreteValuationRing.TFAE R hnf).out 1 4
  refine e.2 ⟨inferInstance, maximalIdeal R,
    ⟨fun h0 => hnf ((isField_iff_maximalIdeal_eq).2 h0), inferInstance⟩, fun P hP => ?_⟩
  haveI := hP.2
  haveI : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.2 (h ▸ le_rfl)
  exact IsLocalRing.eq_maximalIdeal
    ((Ring.krullDimLE_one_iff_of_isPrime_bot.1 inferInstance) P hP.1 inferInstance)

private theorem maximalIdeal_eq_span_of_isLocalization {R S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [IsLocalRing S] [Algebra R S] {p : R} (hp : Prime p)
    [(Ideal.span {p}).IsPrime] [IsLocalization.AtPrime S (Ideal.span {p})] :
    maximalIdeal S = Ideal.span {algebraMap R S p} ∧ maximalIdeal S ≠ ⊥ := by
  have hm : maximalIdeal S = Ideal.span {algebraMap R S p} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {p}) S, Ideal.map_span,
      Set.image_singleton]
  refine ⟨hm, ?_⟩
  rw [hm, Ne, Ideal.span_singleton_eq_bot]
  intro h0
  obtain ⟨⟨c, hc⟩, hc0⟩ := (IsLocalization.map_eq_zero_iff (Ideal.span {p}).primeCompl S p).1 h0
  have : c = 0 := (mul_eq_zero.1 hc0).resolve_right hp.ne_zero
  exact hc (by rw [this]; exact Ideal.zero_mem _)

private theorem idealOrder_span_algebraMap_eq_emultiplicity {R S : Type*} [CommRing R]
    [IsDomain R] [UniqueFactorizationMonoid R] [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    [IsDomain S] [Algebra R S] {p : R} (hp : Prime p) [(Ideal.span {p}).IsPrime]
    [IsLocalization.AtPrime S (Ideal.span {p})] {f : R} (hf : f ≠ 0) :
    idealOrder (Ideal.span {algebraMap R S f}) = emultiplicity p f := by
  have hfin := FiniteMultiplicity.of_prime_left hp hf
  obtain ⟨h, hfh, hndvd⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  rw [hfin.emultiplicity_eq_multiplicity]
  generalize multiplicity p f = e at hfh ⊢
  have hunit : IsUnit (algebraMap R S h) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff S _ h).2 (by
      change h ∉ Ideal.span {p}
      rwa [Ideal.mem_span_singleton])
  obtain ⟨hm, hm0⟩ := maximalIdeal_eq_span_of_isLocalization (S := S) hp
  have hspan : Ideal.span {algebraMap R S f} = maximalIdeal S ^ e := by
    rw [hfh, map_mul, map_pow, ← Ideal.span_singleton_mul_span_singleton,
      Ideal.span_singleton_eq_top.2 hunit, Ideal.mul_top, ← Ideal.span_singleton_pow, ← hm]
  rw [hspan]
  exact idealOrder_maximalIdeal_pow hm0 _

private theorem coheight_and_multAt_fromSpecStalk {Y : Scheme.{u}}
    (hreg : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) (x : Y)
    {p : Y.presheaf.stalk x} (hp : Prime p) (q : PrimeSpectrum (Y.presheaf.stalk x))
    (hq : q.asIdeal = Ideal.span {p}) :
    Order.coheight (Y.fromSpecStalk x q) = 1 ∧
      ∀ (J : Y.IdealSheafData) (f : Y.presheaf.stalk x), IdealSheafData.stalk J x =
        Ideal.span {f} → f ≠ 0 → multAt J (Y.fromSpecStalk x q) = emultiplicity p f := by
  obtain ⟨I, hI⟩ := q
  simp only at hq
  subst hq
  have hyx := fromSpecStalk_specializes_self x ⟨Ideal.span {p}, hI⟩
  letI : Algebra (Y.presheaf.stalk x) (Y.presheaf.stalk (Y.fromSpecStalk x ⟨_, hI⟩)) :=
    (Y.presheaf.stalkSpecializes hyx).hom.toAlgebra
  haveI hloc := Stacks.Chow.isLocalization_stalk_of_specializes hyx ⟨Ideal.span {p}, hI⟩ rfl
  haveI := hreg x
  haveI := hreg (Y.fromSpecStalk x ⟨_, hI⟩)
  haveI := IsRegularLocalRing.isDomain (Y.presheaf.stalk x)
  haveI := IsRegularLocalRing.isDomain (Y.presheaf.stalk (Y.fromSpecStalk x ⟨_, hI⟩))
  haveI := IsRegularLocalRing.uniqueFactorizationMonoid (Y.presheaf.stalk x)
  haveI : IsLocalization.AtPrime (Y.presheaf.stalk (Y.fromSpecStalk x ⟨_, hI⟩))
      (Ideal.span {p}) := hloc
  obtain ⟨hm, hm0⟩ := maximalIdeal_eq_span_of_isLocalization
    (S := Y.presheaf.stalk (Y.fromSpecStalk x ⟨_, hI⟩)) hp
  have hnf : ¬ IsField (Y.presheaf.stalk (Y.fromSpecStalk x ⟨_, hI⟩)) :=
    fun hf => hm0 ((isField_iff_maximalIdeal_eq).1 hf)
  have hdvr : IsDiscreteValuationRing (Y.presheaf.stalk (Y.fromSpecStalk x ⟨_, hI⟩)) :=
    ((IsDiscreteValuationRing.TFAE _ hnf).out 1 5).2 (show (maximalIdeal _).IsPrincipal from
      ⟨⟨_, hm⟩⟩)
  refine ⟨?_, fun J f hJ hf => ?_⟩
  · have h1 := ringKrullDim_stalk_eq_coheight (Y.fromSpecStalk x ⟨_, hI⟩)
    rw [IsDiscreteValuationRing.ringKrullDim_eq_one] at h1
    exact_mod_cast h1.symm
  · rw [multAt, Aux.stalk_eq_map_stalkSpecializes J hyx, hJ, Ideal.map_span, Set.image_singleton]
    exact idealOrder_span_algebraMap_eq_emultiplicity hp hf

/-- Invertible ideals on a scheme with regular local rings are determined by their orders along
prime divisors. -/
private theorem eq_of_forall_multAt_genericPoint_eq {Y : Scheme.{u}}
    (hreg : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) (J₁ J₂ : Y.IdealSheafData)
    (h₁ : Stacks.Divisors.IsEffectiveCartierDivisor J₁)
    (h₂ : Stacks.Divisors.IsEffectiveCartierDivisor J₂)
    (h : ∀ D : AlgebraicGeometry.PrimeDivisor Y,
      multAt J₁ D.genericPoint = multAt J₂ D.genericPoint) : J₁ = J₂ := by
  refine AlgebraicGeometry.IdealSheafData.eq_of_stalk_eq _ _ fun x => ?_
  haveI := hreg x
  haveI := IsRegularLocalRing.isDomain (Y.presheaf.stalk x)
  haveI := IsRegularLocalRing.uniqueFactorizationMonoid (Y.presheaf.stalk x)
  obtain ⟨f, hf, hJf⟩ := exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor _ h₁ x
  obtain ⟨g, hg, hJg⟩ := exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor _ h₂ x
  have key : ∀ p, Prime p → emultiplicity p f = emultiplicity p g := fun p hp => by
    obtain ⟨hcoh, hmult⟩ := coheight_and_multAt_fromSpecStalk hreg x hp
      ⟨Ideal.span {p}, (Ideal.span_singleton_prime hp.ne_zero).2 hp⟩ rfl
    have := h (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh)
    rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne] at this
    rw [← hmult J₁ f hJf hf.ne_zero, ← hmult J₂ g hJg hg.ne_zero, this]
  rw [hJf, hJg, Ideal.span_singleton_eq_span_singleton]
  exact associated_of_dvd_dvd
    ((UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hf.ne_zero).2 fun p hp => (key p hp).le)
    ((UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hg.ne_zero).2 fun p hp => (key p hp).ge)

/-- An effective Cartier divisor has finite order along a prime divisor of a scheme with regular
local rings. -/
private theorem multAt_ne_top_of_isEffectiveCartierDivisor {Y : Scheme.{u}}
    (hreg : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) (J : Y.IdealSheafData)
    (hJ : Stacks.Divisors.IsEffectiveCartierDivisor J) (D : AlgebraicGeometry.PrimeDivisor Y) :
    multAt J D.genericPoint ≠ ⊤ := by
  haveI := hreg D.genericPoint
  haveI := IsRegularLocalRing.isDomain (Y.presheaf.stalk D.genericPoint)
  haveI := isDiscreteValuationRing_of_ringKrullDim_eq_one D.ringKrullDim_stalk_genericPoint_eq_one
  obtain ⟨g, hg, hJg⟩ := exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor _ hJ
    D.genericPoint
  rw [multAt, hJg, idealOrder_span_eq_addVal hg.ne_zero, Ne,
    IsDiscreteValuationRing.addVal_eq_top_iff]
  exact hg.ne_zero

/-- The stalk of `𝒪_X(-A)` at the generic point of a prime divisor `D` is `𝔪^{a_D}`. -/
private theorem stalk_divisorIdeal_genericPoint {X : Scheme.{u}}
    (A : AlgebraicGeometry.PrimeDivisor X → ℕ) (hfin : (Function.support A).Finite)
    (D : AlgebraicGeometry.PrimeDivisor X) :
    IdealSheafData.stalk (divisorIdeal A) D.genericPoint =
      IsLocalRing.maximalIdeal (X.presheaf.stalk D.genericPoint) ^ A D := by
  classical
  unfold divisorIdeal
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := hfin.toFinset) fun D' hD' => by
      simpa using fun h0 => hD' (by simp [h0]), Aux.stalk_prod,
    Finset.prod_eq_single D (fun b _ hb => ?_) (fun hD => ?_), Aux.stalk_pow,
    Aux.stalk_idealSheaf_genericPoint]
  · rw [Aux.stalk_pow, (IdealSheafData.stalk_eq_top_iff_notMem_support _ _).2, Ideal.top_pow,
      Ideal.one_eq_top]
    intro hmem
    refine hb (MMP.Fourfold.SNCWeight.PrimeDivisorUnion.eq_of_support_subset ?_).symm
    rw [Aux.support_eq_closure_genericPoint D]
    exact closure_minimal (Set.singleton_subset_iff.2 hmem) b.idealSheaf.support.isClosed
  · have : A D = 0 := by simpa using hD
    rw [this, pow_zero, show (1 : X.IdealSheafData) = ⊤ from rfl, Aux.stalk_top,
      Ideal.one_eq_top]

/-- The order of `𝒪_X(-A)` along a prime divisor `D` is its coefficient `a_D`. -/
private theorem multAt_divisorIdeal_genericPoint {X : Scheme.{u}} [IsLocallyNoetherian X]
    (hreg : ∀ y : X, IsRegularLocalRing (X.presheaf.stalk y))
    (A : AlgebraicGeometry.PrimeDivisor X → ℕ) (hfin : (Function.support A).Finite)
    (D : AlgebraicGeometry.PrimeDivisor X) :
    multAt (divisorIdeal A) D.genericPoint = A D := by
  haveI := hreg D.genericPoint
  haveI := IsRegularLocalRing.isDomain (X.presheaf.stalk D.genericPoint)
  rw [multAt, stalk_divisorIdeal_genericPoint A hfin]
  exact idealOrder_maximalIdeal_pow (maximalIdeal_stalk_genericPoint_ne_bot D) _

/-- The ideal sheaf `𝒪_Y(-A)` of an effective divisor on a smooth scheme is invertible. -/
private theorem isEffectiveCartierDivisor_divisorIdeal {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (hY : MMP.Mori.IsSmoothScheme sY)
    (A : AlgebraicGeometry.PrimeDivisor Y → ℕ) (hA : (Function.support A).Finite) :
    Stacks.Divisors.IsEffectiveCartierDivisor (divisorIdeal A) := by
  classical
  have hM : divisorIdeal A = ∏ D ∈ hA.toFinset, D.idealSheaf ^ A D := by
    unfold divisorIdeal
    refine finprod_eq_prod_of_mulSupport_subset _ fun D hD => ?_
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    intro h0
    exact hD (by show D.idealSheaf ^ A D = 1; rw [h0, pow_zero])
  rw [hM]
  exact Stacks.Divisors.isEffectiveCartierDivisor_prod _ _ _
    fun D _ => Aux.isEffectiveCartierDivisor_idealSheaf sY hY D

/-- **An invertible ideal on a smooth scheme is `𝒪_Y(-D)`.** If `J` is an invertible ideal sheaf
on a smooth scheme `Y` over a field whose support lies in finitely many prime divisors, then
`J = 𝒪_Y(-D) = ∏_E I_E^{d_E}` for an effective divisor `D = ∑_E d_E E` supported in `Supp J`;
`d_E` is the order of `J` along `E`. -/
private theorem exists_divisor_eq_divisorIdeal {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (hY : MMP.Mori.IsSmoothScheme sY)
    (J : Y.IdealSheafData) (hJ : Stacks.Divisors.IsEffectiveCartierDivisor J)
    (s : Finset (AlgebraicGeometry.PrimeDivisor Y))
    (hs : (J.support : Set Y) ⊆ ⋃ E ∈ s, E.support) :
    ∃ D : Divisor Y, 0 ≤ D ∧ J = divisorIdeal (fun E => (D E).toNat) ∧
      (D.supp : Set Y) ⊆ J.support := by
  classical
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  haveI := Aux.smooth_of_isSmoothScheme' sY hY
  have hreg : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y) := fun y =>
    isRegularLocalRing_stalk_of_smooth_over_field sY y
  set D : Divisor Y := ∑ E ∈ s, Finsupp.single E ((multAt J E.genericPoint).toNat : ℤ) with hD
  have hDE : ∀ E, D E = if E ∈ s then ((multAt J E.genericPoint).toNat : ℤ) else 0 := by
    intro E
    rw [hD, Finsupp.finset_sum_apply]
    simp only [Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
  have hsupp : ∀ E : AlgebraicGeometry.PrimeDivisor Y, multAt J E.genericPoint ≠ 0 →
      (E.support : Set Y) ⊆ J.support := fun E hE => by
    rw [Aux.support_eq_closure_genericPoint E]
    exact closure_minimal (Set.singleton_subset_iff.2 (mem_support_of_multAt_ne_zero J _ hE))
      J.support.isClosed
  have hfin : (Function.support fun E => (D E).toNat).Finite := by
    refine s.finite_toSet.subset fun E hE => ?_
    by_contra hEs
    have hEs' : E ∉ s := hEs
    exact hE (by simp [hDE, hEs'])
  refine ⟨D, fun E => ?_, ?_, ?_⟩
  · simp only [Finsupp.coe_zero, Pi.zero_apply, hDE]
    split_ifs <;> simp
  · refine (eq_of_forall_multAt_genericPoint_eq hreg _ _ hJ
      (isEffectiveCartierDivisor_divisorIdeal sY hY _ hfin) fun E => ?_)
    rw [multAt_divisorIdeal_genericPoint hreg _ hfin, hDE]
    split_ifs with hEs
    · simp only [Int.toNat_natCast]
      exact (ENat.coe_toNat (multAt_ne_top_of_isEffectiveCartierDivisor hreg J hJ E)).symm
    · by_contra hne
      exact hEs (mem_of_support_subset_iUnion ((hsupp E (by simpa using hne)).trans hs))
  · intro x hx
    obtain ⟨E, hE, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hx
    rw [DivisorWithCoeffs.coeff_apply, hDE] at hE
    split_ifs at hE with hEs
    · refine hsupp E (fun h0 => hE ?_) hxE
      rw [h0]; rfl
    · exact absurd rfl hE

/-- **Effective Cartier divisors pull back along a surjection of integral schemes.** -/
private theorem isEffectiveCartierDivisor_comap_of_surjective {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (g : Y ⟶ X) [Surjective g] (F : X.IdealSheafData)
    (hF : Stacks.Divisors.IsEffectiveCartierDivisor F) :
    Stacks.Divisors.IsEffectiveCartierDivisor (F.comap g) := by
  refine Stacks.Divisors.isEffectiveCartierDivisor_of_forall_exists_affineOpen _ fun y => ?_
  obtain ⟨W, hyW, -, t, ht, hgen⟩ :=
    Stacks.Blowup.exists_affineOpens_ideal_eq_span_le F hF (g y) ⊤ trivial
  obtain ⟨-, ⟨V, hV, rfl⟩, hyV, hVsub⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (show y ∈ g ⁻¹ᵁ (W : X.Opens) from hyW) (g ⁻¹ᵁ (W : X.Opens)).isOpen
  have hVW : (V : Y.Opens) ≤ g ⁻¹ᵁ (W : X.Opens) := hVsub
  refine ⟨V, hV, hyV, (g.appLE W.1 V hVW).hom t,
    ?_, Stacks.IdealSheaf.ideal_comap_eq_span F g W ⟨V, hV⟩ hVW hgen⟩
  haveI : Nonempty (V : Y.Opens) := ⟨⟨y, hyV⟩⟩
  refine IsRegular.of_ne_zero' fun h0 => ?_
  have hb := Scheme.basicOpen_appLE g V W.1 hVW t
  rw [h0, Scheme.basicOpen_zero] at hb
  haveI : Nonempty (W.1 : X.Opens) := ⟨⟨g y, hyW⟩⟩
  have hne : (X.basicOpen t : Set X).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr fun hc => ht.ne_zero <| by
      rw [← AlgebraicGeometry.basicOpen_eq_bot_iff]
      exact TopologicalSpace.Opens.coe_eq_empty.mp hc
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y', rfl⟩ := g.surjective x
  have hne' : ((V : Y.Opens) ⊓ g ⁻¹ᵁ (X.basicOpen t) : Set Y).Nonempty :=
    (IrreducibleSpace.isIrreducible_univ Y).2 _ _ V.isOpen (g ⁻¹ᵁ (X.basicOpen t)).isOpen
      ⟨y, trivial, hyV⟩ ⟨y', trivial, hx⟩ |>.mono fun _ h => h.2
  obtain ⟨z, hz⟩ := hne'
  have : z ∈ ((V ⊓ g ⁻¹ᵁ X.basicOpen t : Y.Opens) : Set Y) := hz
  rw [← hb] at this
  exact this

end DivisorialIdeals

/-! ### Step 1: a resolution projective over `k` principalizing `I` -/

/-- **A resolution projective over `k`, adapted to `Δ` and to an ideal.** Let `X` be a proper
variety over an algebraically closed field of characteristic zero, `Δ` an `ℝ`-divisor and `I`
a nonzero ideal sheaf on `X`. There is a log resolution `f : T ⟶ X` of `(X, Δ)` with `T`
projective over `k`, `I 𝒪_T` invertible, and an snc divisor `S` on `T` containing
`Ex(f) ∪ f⁻¹(Supp Δ) ∪ Supp(I 𝒪_T)`. -/
private theorem exists_isLogResolution_isProjectiveVariety_comap {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (hXv : AlgebraicGeometry.IsVariety k sX) [IsProper sX] (Δ : RDivisor X)
    (I : X.IdealSheafData) (hI : I ≠ ⊥) :
    ∃ (T : Scheme.{u}) (f : T ⟶ X), IsLogResolution sX Δ f ∧
      AlgebraicGeometry.IsProjectiveVariety k (f ≫ sX) ∧
      Stacks.Divisors.IsEffectiveCartierDivisor (I.comap f) ∧
      ∃ S : Closeds T, IsSNCSubset (f ≫ sX) S ∧
        exceptionalSet f ⊔ Δ.supp.preimage f.continuous ≤ S ∧ (I.comap f).support ≤ S := by
  haveI := hXv
  haveI : IsIntegral X := hXv.toIsIntegral
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  /- Chow: a quasi-projective model `q : X₂ ⟶ X`. -/
  obtain ⟨X₂, q, U, hX₂, hq, hUne, hqU, hqp⟩ := exists_isQuasiProjective_isIso_restrict sX hXv
  haveI := hX₂
  haveI := hq
  haveI := hqU
  haveI : IsIntegral X₂ := hX₂.toIsIntegral
  haveI : IsLocallyNoetherian X₂ := LocallyOfFiniteType.isLocallyNoetherian (q ≫ sX)
  haveI : CompactSpace X₂ := QuasiCompact.compactSpace_of_compactSpace (q ≫ sX)
  haveI : IsIso (q ∣_ biregularLocus q) := isBiregular_biregularLocus q
  set V : X.Opens := biregularLocus q ⊓ smoothLocus sX with hV
  haveI : IsIso (q ∣_ V) := MMP.Resolution.TupleResolutionAux.isIso_restrict_of_le q inf_le_left
  set O : X.Opens := V ⊓ Δ.supp.compl ⊓ I.support.compl with hO
  haveI : IsIso (q ∣_ O) := MMP.Resolution.TupleResolutionAux.isIso_restrict_of_le q
    (inf_le_left.trans (inf_le_left.trans inf_le_left))
  have : LocallyOfFinitePresentation sX :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := sX)).mpr inferInstance
  have hgenI : genericPoint X ∉ (I.support : Set X) := by
    intro h
    refine hI (Scheme.IdealSheafData.support_eq_top_iff.mp (eq_top_iff.mpr fun x _ => ?_))
    exact ((genericPoint_spec X).mem_closed_set_iff I.support.isClosed).mp h (Set.mem_univ x)
  have hgenO : genericPoint X ∈ O := by
    refine ⟨⟨⟨genericPoint_mem_of_nonempty _ (hUne.mono (le_biregularLocus hqU)), ?_⟩, ?_⟩,
      hgenI⟩
    · rw [smoothLocus_eq_smoothLocus]
      exact Scheme.Hom.genericPoint_mem_smoothLocus_of_perfectField sX
    · exact MMP.Fourfold.genericPoint_notMem_supp Δ
  have hOne : (O : Set X).Nonempty := ⟨_, hgenO⟩
  /- Principalization of `A · B · C` on `X₂`. -/
  set A : X₂.IdealSheafData := (Scheme.IdealSheafData.vanishingIdeal V.compl).comap q with hA
  set B : X₂.IdealSheafData := (Scheme.IdealSheafData.vanishingIdeal Δ.supp).comap q with hB
  set C : X₂.IdealSheafData := I.comap q with hC
  have hAsupp : (A.support : Set X₂) = q ⁻¹' (V.compl : Set X) :=
    coe_support_comap_vanishingIdeal q _
  have hBsupp : (B.support : Set X₂) = q ⁻¹' (Δ.supp : Set X) :=
    coe_support_comap_vanishingIdeal q _
  have hCsupp : (C.support : Set X₂) = q ⁻¹' (I.support : Set X) := by
    rw [hC, Scheme.IdealSheafData.support_comap, Closeds.coe_preimage]
  have hABsupp : ((A * B).support : Set X₂) =
      q ⁻¹' (V.compl : Set X) ∪ q ⁻¹' (Δ.supp : Set X) := by
    rw [Scheme.IdealSheafData.support_mul, Closeds.coe_sup, hAsupp, hBsupp]
  have hKsupp : ((A * B * C).support : Set X₂) =
      q ⁻¹' (V.compl : Set X) ∪ q ⁻¹' (Δ.supp : Set X) ∪ q ⁻¹' (I.support : Set X) := by
    rw [Scheme.IdealSheafData.support_mul, Closeds.coe_sup, hABsupp, hCsupp]
  have hgen₂ : q (genericPoint X₂) ∈ O := genericPoint_mem_preimage q O hOne
  have hK : A * B * C ≠ ⊥ := by
    intro h0
    have h1 : genericPoint X₂ ∈ ((A * B * C).support : Set X₂) := by rw [h0]; simp
    rw [hKsupp] at h1
    rcases h1 with (h1 | h1) | h1
    · exact h1 hgen₂.1.1
    · exact hgen₂.1.2 h1
    · exact hgen₂.2 h1
  obtain ⟨Y, g, hYv, hgP, -, hgS, hgiso, hcart, hsnc, hpure⟩ :=
    MMP.Resolution.exists_isResolutionOfVariety_isEffectiveCartierDivisor_comap (q ≫ sX) hX₂
      (A * B * C) hK
  set f : Y ⟶ X := g ≫ q with hf
  haveI := hYv
  haveI : IsIntegral Y := hYv.toIsIntegral
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (g ≫ q ≫ sX)
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (g ≫ q ≫ sX)
  have hfs : f ≫ sX = g ≫ q ≫ sX := Category.assoc _ _ _
  haveI : IsProper g := hgP.isProper
  /- `f` is an isomorphism over `O`, and `O ⊆ V_f ⊆ V`. -/
  have hqOsm : q ⁻¹ᵁ O ≤ smoothLocus (q ≫ sX) ⊓ (A * B * C).support.compl := by
    refine le_inf (fun y hy => preimage_le_smoothLocus sX q V inf_le_right hy.1.1) ?_
    intro y hy h
    have h' : y ∈ ((A * B * C).support : Set X₂) := h
    rw [hKsupp] at h'
    rcases h' with (h' | h') | h'
    · exact h' hy.1.1
    · exact hy.1.2 h'
    · exact hy.2 h'
  haveI := hgiso
  haveI : IsIso (g ∣_ q ⁻¹ᵁ O) := MMP.Resolution.TupleResolutionAux.isIso_restrict_of_le g hqOsm
  haveI hfO : IsIso (f ∣_ O) := isIso_restrict_comp g q O
  have hsm : IsSmoothScheme (f ≫ sX) := hfs ▸ hgS
  haveI : LocallyOfFiniteType (f ≫ sX) := by rw [hfs]; infer_instance
  haveI : IsDominant g :=
    (isBirationalMorphism_of_isIso_restrict g (q ⁻¹ᵁ O) ⟨_, hgen₂⟩).isDominant
  have hfV : biregularLocus f ≤ V := le_inf
    (le_biregularLocus (isBiregular_of_isBiregular_comp g q (isBiregular_biregularLocus f)).1)
    (biregularLocus_le_smoothLocus sX f hsm)
  /- `Ex(f) = f⁻¹(X ∖ V) ∪ Ex(g)`. -/
  have hEx : (exceptionalSet f : Set Y) = f ⁻¹' (V.compl : Set X) ∪ exceptionalSet g :=
    coe_exceptionalSet_comp g q V hfV
  have hstalk : ∀ (P Q : X₂.IdealSheafData) (y : Y),
      IdealSheafData.stalk (P.comap g) y * IdealSheafData.stalk (Q.comap g) y =
        IdealSheafData.stalk ((P * Q).comap g) y := fun P Q y => by
    rw [IdealSheafData.stalk_comap (P * Q) g, Aux.stalk_mul, Ideal.map_mul,
      IdealSheafData.stalk_comap P g, IdealSheafData.stalk_comap Q g]
  have hcartAB : Stacks.Divisors.IsEffectiveCartierDivisor ((A * B).comap g) :=
    isEffectiveCartierDivisor_of_stalk_mul _ (C.comap g) _ hcart (hstalk _ _)
  have hcartA : Stacks.Divisors.IsEffectiveCartierDivisor (A.comap g) :=
    isEffectiveCartierDivisor_of_stalk_mul _ (B.comap g) _ hcartAB (hstalk _ _)
  have hcartC : Stacks.Divisors.IsEffectiveCartierDivisor (C.comap g) :=
    isEffectiveCartierDivisor_of_stalk_mul _ ((A * B).comap g) _ hcart fun y => by
      rw [mul_comm, hstalk]
  have hgenY : f (genericPoint Y) ∈ O := genericPoint_mem_preimage f O hOne
  have hcoe_comap : ∀ P : X₂.IdealSheafData,
      ((P.comap g).support : Set Y) = g ⁻¹' (P.support : Set X₂) := fun P => by
    rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage]
  have hgenA : genericPoint Y ∉ (A.comap g).support := by
    intro h
    have h' : genericPoint Y ∈ ((A.comap g).support : Set Y) := h
    rw [hcoe_comap, Set.mem_preimage, hAsupp] at h'
    exact h' hgenY.1.1
  have hgenAB : genericPoint Y ∉ ((A * B).comap g).support := by
    intro h
    have h' : genericPoint Y ∈ (((A * B).comap g).support : Set Y) := h
    rw [hcoe_comap, Set.mem_preimage, hABsupp] at h'
    rcases h' with h' | h'
    · exact h' hgenY.1.1
    · exact hgenY.1.2 h'
  have hExeq : exceptionalSet f = (A.comap g).support ⊔ exceptionalSet g :=
    Closeds.ext (by rw [Closeds.coe_sup, hEx, hcoe_comap, hAsupp]; rfl)
  have hS : exceptionalSet f ⊔ Δ.supp.preimage f.continuous =
      exceptionalSet g ⊔ ((A * B).comap g).support := by
    refine Closeds.ext ?_
    rw [Closeds.coe_sup, Closeds.coe_sup, hEx, hcoe_comap, hABsupp]
    simp only [Closeds.coe_preimage]
    ext y
    simp only [Set.mem_union, Set.mem_preimage, hf, Scheme.Hom.comp_apply]
    tauto
  have hle : exceptionalSet g ⊔ ((A * B).comap g).support ≤
      exceptionalSet g ⊔ ((A * B * C).comap g).support := by
    refine sup_le_sup_left (fun y hy => ?_) _
    have h' : y ∈ (((A * B).comap g).support : Set Y) := hy
    change y ∈ (((A * B * C).comap g).support : Set Y)
    rw [hcoe_comap] at h' ⊢
    rw [Set.mem_preimage, Scheme.IdealSheafData.support_mul] at h' ⊢
    exact Or.inl h'
  /- Projectivity. -/
  have h1 : IsQuasiProjective g := isQuasiProjective_of_isProjective hgP
  have h2 : IsQuasiProjective (f ≫ sX) := by
    rw [hfs]
    exact IsQuasiProjective.comp g (q ≫ sX) h1 hqp
  have h3 := Stacks.HProjective.isHQuasiProjective_of_isQuasiProjective_of_exists_isAmple (f ≫ sX)
    (Stacks.HProjective.exists_isAmple_of_isAffine _) h2
  have hfP : IsProjectiveMorphism f := isProjectiveMorphism_of_isHQuasiProjective_comp sX f h3
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hfP
  have hYP : IsProjectiveMorphism (f ≫ sX) :=
    isProjectiveMorphism_of_isHQuasiProjective_comp (𝟙 (Spec (.of k))) (f ≫ sX)
      (by rw [Category.comp_id]; exact h3)
  have hYv' : AlgebraicGeometry.IsVariety k (f ≫ sX) := by rw [hfs]; exact hYv
  refine ⟨Y, f, ⟨⟨inferInstance, isBirationalMorphism_of_isIso_restrict f O hOne, hsm⟩, ?_, ?_⟩,
    (AlgebraicGeometry.isProjectiveVariety_iff k _).mpr ⟨hYv', hYP⟩, ?_,
    exceptionalSet g ⊔ ((A * B * C).comap g).support, hfs ▸ hsnc, ?_, ?_⟩
  · rw [hExeq]
    exact isPureCodimOne_sup (isPureCodimOne_support_of_isEffectiveCartierDivisor _ hcartA hgenA)
      hpure
  · rw [hS, hfs]
    refine isSNCSubset_of_le hsnc (isPureCodimOne_sup hpure
      (isPureCodimOne_support_of_isEffectiveCartierDivisor _ hcartAB hgenAB)) hle
  · rw [hf, Scheme.IdealSheafData.comap_comp]
    exact hcartC
  · rw [hS]; exact hle
  · intro y hy
    have h' : y ∈ ((I.comap f).support : Set Y) := hy
    rw [hf, Scheme.IdealSheafData.comap_comp, hcoe_comap, Set.mem_preimage] at h'
    refine Or.inr ?_
    change y ∈ (((A * B * C).comap g).support : Set Y)
    rw [hcoe_comap, Set.mem_preimage, Scheme.IdealSheafData.support_mul]
    exact Or.inr h'

section KM2c

variable {k : Type} [Field k]

/-! ### Varieties -/

/-- The Weil divisor `[τ]` of a Cartier divisor `τ`, as an additive map. -/
private noncomputable def weilOfCartier (X : Scheme.{0}) [IsNoetherian X] [IsIntegral X] :
    X.CartierDivisor →+ Divisor X where
  toFun τ := weilDivisorEquivFinsupp (cartierWeilDivisor τ)
  map_zero' := Finsupp.ext fun Z => by
    have h : cartierMultiplicity ((0 : X.CartierDivisor) + 0) Z.genericPoint =
        cartierMultiplicity (0 : X.CartierDivisor) Z.genericPoint +
          cartierMultiplicity (0 : X.CartierDivisor) Z.genericPoint := by
      unfold cartierMultiplicity
      rw [map_add, map_add]
      rfl
    rw [add_zero] at h
    change cartierMultiplicity (0 : X.CartierDivisor) Z.genericPoint = 0
    omega
  map_add' a b := Finsupp.ext fun Z => by
    change cartierMultiplicity (a + b) Z.genericPoint =
      cartierMultiplicity a Z.genericPoint + cartierMultiplicity b Z.genericPoint
    unfold cartierMultiplicity
    rw [map_add, map_add]
    rfl

/-- The source of a projective smooth resolution of a normal projective variety is a projective
variety. -/
private theorem isProjectiveVariety_comp {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) (hXp : MMP.Mori.IsProjectiveVariety k sX) {f : Y ⟶ X}
    (hf : IsSmoothResolution sX f) (hfp : IsProjectiveMorphism f) :
    MMP.Mori.IsProjectiveVariety k (f ≫ sX) := by
  rw [MMP.Mori.isProjectiveVariety_iff] at hXp ⊢
  exact ⟨(hf.isNormalVariety hX).1.1, hfp.comp hXp.2⟩

/-- The source of a smooth resolution of a normal variety is a smooth variety. -/
private theorem isSmoothVariety_of_isSmoothResolution {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) {f : Y ⟶ X} (hf : IsSmoothResolution sX f) :
    IsSmoothVariety k (f ≫ sX) := by
  have hv := (hf.isNormalVariety hX).1.1
  haveI : LocallyOfFiniteType (f ≫ sX) := hv.toLocallyOfFiniteType
  haveI : LocallyOfFinitePresentation (f ≫ sX) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  exact (isSmoothVariety_iff k _).mpr ⟨hv, (isSmoothScheme_iff _).mp hf.isSmoothScheme⟩

/-! ### Degrees along curves -/

/-- The degree along a curve of a divisor depends only on the isomorphism class of its sheaf. -/
private theorem degreeOn_eq_of_divisorialSheaf_iso {X C : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] (φ : C ⟶ X) [IsProper (φ ≫ sX)]
    (hdim : topologicalKrullDim C ≤ 1) {D D' : Divisor X} (hD : D.IsCartier) (hD' : D'.IsCartier)
    (e : (haveI := QuasiCompact.compactSpace_of_compactSpace sX; D.divisorialSheaf) ≅
      (haveI := QuasiCompact.compactSpace_of_compactSpace sX; D'.divisorialSheaf)) :
    D.degreeOn k sX φ hdim hD = D'.degreeOn k sX φ hdim hD' := by
  haveI := QuasiCompact.compactSpace_of_compactSpace sX
  haveI := hD.isInvertibleModule_divisorialSheaf
  haveI := hD'.isInvertibleModule_divisorialSheaf
  exact degreeOn_eq_of_iso k sX φ hdim e

/-- The degree along a curve depends only on the morphism. -/
private theorem degreeOn_congr_hom {X C : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
    [IsLocallyNoetherian X] [IsNormal X] {φ φ' : C ⟶ X} (h : φ = φ') [IsProper (φ ≫ sX)]
    [IsProper (φ' ≫ sX)] (hdim : topologicalKrullDim C ≤ 1) (D : Divisor X) (hD : D.IsCartier) :
    D.degreeOn k sX φ hdim hD = D.degreeOn k sX φ' hdim hD := by
  subst h; rfl

/-- `deg_C 𝒪_V(u^*B) = deg_{u ∘ C} 𝒪_W(B)` for the pull-back of a Cartier divisor. -/
private theorem degreeOn_eq_of_isPullback {V W C : Scheme.{0}} {sV : V ⟶ Spec (.of k)}
    {sW : W ⟶ Spec (.of k)} [QuasiCompact sV] [QuasiCompact sW] [IsLocallyNoetherian V]
    [IsNormal V] [IsIntegral V] [IsLocallyNoetherian W] [IsNormal W] (u : V ⟶ W)
    (hu : u ≫ sW = sV) {B : Divisor W} (hBc : B.IsCartier)
    {hB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ B.supp}
    {B' : Divisor V} (h : B.IsPullback u hB B') (hB'c : B'.IsCartier) (φ : C ⟶ V)
    [IsProper (φ ≫ sV)] [IsProper ((φ ≫ u) ≫ sW)] (hdim : topologicalKrullDim C ≤ 1) :
    B'.degreeOn k sV φ hdim hB'c = B.degreeOn k sW (φ ≫ u) hdim hBc := by
  haveI := QuasiCompact.compactSpace_of_compactSpace sV
  haveI := QuasiCompact.compactSpace_of_compactSpace sW
  haveI := hBc.isInvertibleModule_divisorialSheaf
  haveI := hB'c.isInvertibleModule_divisorialSheaf
  change MMP.Mori.degreeOn k sV φ hdim B'.divisorialSheaf = MMP.Mori.degreeOn k sW (φ ≫ u) hdim
    B.divisorialSheaf
  rw [degreeOn_eq_of_iso k sV φ hdim (h.divisorialSheafIso (hBc := hBc))]
  exact degreeOn_pullback_eq_degreeOn_comp sV sW u φ hu hdim _

/-- **The degree identity on `Y`.** Let `g : X' ⟶ X`, `h : Y ⟶ X'`, `D₁ = g^*D`, and suppose
`𝒪_{X'}(m D₁) ≅ 𝒪_{X'}(a + e)`. Then along every curve on `Y`,
`deg h^*a + deg h^*e = m · deg (g ∘ h)^*D`. -/
private theorem degreeOn_add_eq_mul_degreeOn_of_iso {X X' Y C : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX']
    [IsLocallyNoetherian X'] [IsNormal X'] [IsIntegral X'] [CompactSpace X'] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y]
    (g : X' ⟶ X) (hg : g ≫ sX = sX') (h : Y ⟶ X') (hh : h ≫ sX' = sY)
    {D : Divisor X} (hDc : D.IsCartier)
    {hB₁ : ∀ Z : irreducibleComponents X', g (componentGenericPoint X' Z) ∉ D.supp}
    {D₁ : Divisor X'} (hD₁ : D.IsPullback g hB₁ D₁) (hD₁c : D₁.IsCartier)
    {hBf : ∀ Z : irreducibleComponents Y, (h ≫ g) (componentGenericPoint Y Z) ∉ D.supp}
    {fD : Divisor Y} (hfD : D.IsPullback (h ≫ g) hBf fD) (hfDc : fD.IsCartier)
    {a e : Divisor X'} (hac : a.IsCartier) (hec : e.IsCartier) {m : ℕ}
    (eae : (m • D₁).divisorialSheaf ≅ (a + e).divisorialSheaf)
    {hBa : ∀ Z : irreducibleComponents Y, h (componentGenericPoint Y Z) ∉ a.supp}
    {b : Divisor Y} (hb : a.IsPullback h hBa b) (hbc : b.IsCartier)
    {hBe : ∀ Z : irreducibleComponents Y, h (componentGenericPoint Y Z) ∉ e.supp}
    {be : Divisor Y} (hbe : e.IsPullback h hBe be) (hbec : be.IsCartier)
    (i : C ⟶ Y) [IsProper (i ≫ sY)] (hdim : topologicalKrullDim C ≤ 1) :
    b.degreeOn k sY i hdim hbc + be.degreeOn k sY i hdim hbec =
      m * fD.degreeOn k sY i hdim hfDc := by
  haveI : IsProper ((i ≫ h) ≫ sX') := by simp only [Category.assoc, hh]; infer_instance
  haveI : IsProper ((i ≫ h ≫ g) ≫ sX) := by simp only [Category.assoc, hg, hh]; infer_instance
  haveI : IsProper (((i ≫ h) ≫ g) ≫ sX) := by simp only [Category.assoc, hg, hh]; infer_instance
  have hmae := degreeOn_eq_of_divisorialSheaf_iso (sX := sX') (i ≫ h) hdim (hD₁c.nsmul m)
    (hac.add hec) eae
  rw [Divisor.degreeOn_nsmul' k sX' (i ≫ h) hdim D₁ hD₁c m,
    Divisor.degreeOn_add k sX' (i ≫ h) hdim a e hac hec] at hmae
  rw [degreeOn_eq_of_isPullback h hh hac hb hbc i hdim,
    degreeOn_eq_of_isPullback h hh hec hbe hbec i hdim, ← hmae,
    degreeOn_eq_of_isPullback g hg hDc hD₁ hD₁c (i ≫ h) hdim,
    degreeOn_eq_of_isPullback (h ≫ g) (by rw [Category.assoc, hg, hh]) hDc hfD hfDc i hdim,
    degreeOn_congr_hom (Category.assoc i h g) hdim D hDc]

/-- If `D = e • F` as `ℚ`-divisors, then each coefficient satisfies `D P = e * F P`. -/
private theorem coeff_eq_mul_of_toQDivisor_eq_smul {Y : Scheme.{0}} {D : Divisor Y}
    {F : QDivisor Y} {e : ℕ} (h : Divisor.toQDivisor D = (e : ℚ) • F)
    (P : MMP.Mori.PrimeDivisor Y) : (D P : ℚ) = e * F P :=
  (by simpa using congrArg (· P) h : Divisor.toQDivisor D P = e * F P)

/-! ### Bigness -/

/-- Restricting a section of a module twice is restricting it once. -/
private theorem map_map_homOfLE {X : Scheme.{0}} (L : X.Modules) {P Q R : X.Opens} (h₁ : Q ≤ P)
    (h₂ : P ≤ R) (σ : Γ(L, R)) :
    L.presheaf.map (homOfLE h₁).op (L.presheaf.map (homOfLE h₂).op σ) =
      L.presheaf.map (homOfLE (h₁.trans h₂)).op σ := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Restricting a section of a module to its own open does nothing. -/
private theorem map_homOfLE_refl {X : Scheme.{0}} (L : X.Modules) {W : X.Opens} (σ : Γ(L, W)) :
    L.presheaf.map (homOfLE (le_refl W)).op σ = σ := by
  rw [show homOfLE (le_refl W) = 𝟙 W from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- A generator of an invertible module over every open inside `K` pulls back, along the unit of
`b^* ⊣ b_*`, to a generator over every open inside `b⁻¹ K`. -/
private theorem bijective_smul_unit_app {X Y : Scheme.{0}} (b : X ⟶ Y) (A : Y.Modules)
    [Stacks.Ample.IsInvertibleModule Y A] {K : Y.Opens} (a : Γ(A, K))
    (ha : ∀ (W : Y.Opens) (hW : W ≤ K),
      Function.Bijective (fun c : Γ(Y, W) => c • A.presheaf.map (homOfLE hW).op a))
    (W : X.Opens) (hW : W ≤ b ⁻¹ᵁ K) :
    Function.Bijective (fun c : Γ(X, W) =>
      c • ((Scheme.Modules.pullback b).obj A).presheaf.map (homOfLE hW).op
        (((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app A).app K a)) := by
  have hpb : Stacks.Ample.IsInvertibleModule X
      ((RingedSpaceModuleAdjunction.modulePullback b.toLRSHom.toShHom).obj A) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback b A
  have hpb' : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property
      ((RingedSpaceModuleAdjunction.modulePullback b.toLRSHom.toShHom).obj A) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr hpb
  refine Stacks.SheafOfModules.bijective_smul_of_forall_germ_notMem_maximalIdeal_smul_top
    (X := X.toRingedSpace) _
    (Stacks.RingedSpace.pullbackUnit b.toLRSHom.toShHom A (Opposite.op K) a)
    _ hW fun x hx => ?_
  have h1 := Scheme.Modules.germ_notMem_maximalSmul_of_bijective_smul A a ha (b.base x) (hW hx)
  rw [← Stacks.NonvanishingLocusRestrict.mem_maximalSmul_germ_pullbackUnit_iff b A a x
    (hW hx)] at h1
  rwa [Stacks.NonvanishingPullback.mem_maximalSmul_iff] at h1

/-- A global section of an invertible module on an integral scheme vanishing on a nonempty open
vanishes. -/
private theorem eq_zero_of_map_eq_zero {X : Scheme.{0}} [IsIntegral X] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] {V : X.Opens} (hV : (V : Set X).Nonempty)
    (s : Γ(L, ⊤)) (hs : L.presheaf.map (homOfLE le_top : V ⟶ ⊤).op s = 0) : s = 0 := by
  have hL : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).mpr ‹_›
  have key : ∀ x : X, ∃ (K : X.Opens) (_ : x ∈ K),
      L.presheaf.map (homOfLE le_top : K ⟶ ⊤).op s = 0 := by
    intro x
    obtain ⟨K, hx, a, ha⟩ : ∃ (K : X.Opens) (_ : x ∈ K) (a : Γ(L, K)), ∀ (W : X.Opens)
        (hW : W ≤ K), Function.Bijective
          (fun c : Γ(X, W) => c • L.presheaf.map (homOfLE hW).op a) :=
      @Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible X.toRingedSpace _ L hL x
    refine ⟨K, hx, ?_⟩
    obtain ⟨g, hg⟩ := (ha K le_rfl).2 (L.presheaf.map (homOfLE le_top : K ⟶ ⊤).op s)
    simp only [map_homOfLE_refl] at hg
    obtain ⟨z, hz⟩ := nonempty_preirreducible_inter K.2 V.2 ⟨x, hx⟩ hV
    have : Nonempty (K ⊓ V : X.Opens) := ⟨⟨z, hz⟩⟩
    have hg0 : g = 0 := by
      refine map_injective_of_isIntegral X (homOfLE inf_le_left : K ⊓ V ⟶ K) ?_
      rw [map_zero]
      refine (ha (K ⊓ V) inf_le_left).1 ?_
      dsimp only
      rw [zero_smul, ← Scheme.Modules.map_smul, hg, map_map_homOfLE,
        ← map_map_homOfLE L (inf_le_right : K ⊓ V ≤ V) (le_top : V ≤ ⊤), hs, map_zero]
    rw [← hg, hg0, zero_smul]
  choose K hxK hK using key
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨L.presheaf, L.isSheaf⟩ K ⊤
    (fun x => homOfLE le_top) (fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxK x⟩) s 0
    fun x => ?_
  change L.presheaf.map (homOfLE le_top : K x ⟶ ⊤).op s =
    L.presheaf.map (homOfLE le_top : K x ⟶ ⊤).op 0
  rw [hK x, map_zero]

/-- Pull-back of sections of an invertible sheaf along a dominant quasi-compact morphism of
integral schemes is injective on global sections. -/
private theorem unit_app_top_injective {Y T : Scheme.{0}} [IsIntegral Y] [IsIntegral T]
    (g : Y ⟶ T) [IsDominant g] [QuasiCompact g] (M : T.Modules)
    [Stacks.Ample.IsInvertibleModule T M] :
    Function.Injective (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app ⊤) := by
  have hMinv : Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf
      (structureSheafRing T.toRingedSpace).property M :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ M).mpr ‹_›
  set L := (Scheme.Modules.pullback g).obj M
  set η := (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M
  rw [injective_iff_map_eq_zero]
  intro s hs
  obtain ⟨y0⟩ : Nonempty Y := inferInstance
  obtain ⟨K, hyK, a, ha⟩ : ∃ (K : T.Opens) (_ : g y0 ∈ K) (a : Γ(M, K)), ∀ (W : T.Opens)
      (hW : W ≤ K), Function.Bijective
        (fun c : Γ(T, W) => c • M.presheaf.map (homOfLE hW).op a) :=
    @Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible T.toRingedSpace _ M hMinv (g y0)
  obtain ⟨U, hUaff, hyU, hUK⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens hyK
  set e : Γ(L, g ⁻¹ᵁ U) := η.app U (M.presheaf.map (homOfLE hUK).op a)
  have hgen := bijective_smul_unit_app g M (M.presheaf.map (homOfLE hUK).op a)
    (fun W hW => by simpa only [map_map_homOfLE] using ha W (hW.trans hUK)) (g ⁻¹ᵁ U) le_rfl
  set t := M.presheaf.map (homOfLE le_top : U ⟶ ⊤).op s
  obtain ⟨f, hf⟩ := (ha U hUK).2 t
  have hηt : η.app U t = 0 := by
    refine (PresheafOfModules.naturality_apply η.val (homOfLE le_top : U ⟶ ⊤).op s).trans ?_
    change _ = (0 : _)
    erw [hs, map_zero]
    rfl
  have hgf : g.app U f = 0 := by
    refine hgen.1 ?_
    change g.app U f • L.presheaf.map (homOfLE (le_refl (g ⁻¹ᵁ U))).op e =
      (0 : Γ(Y, g ⁻¹ᵁ U)) • L.presheaf.map (homOfLE (le_refl (g ⁻¹ᵁ U))).op e
    rw [map_homOfLE_refl, zero_smul]
    refine Eq.trans ?_ hηt
    rw [← hf, Scheme.Modules.Hom.app_smul]
    rfl
  have : IsSchemeTheoreticallyDominant g := .of_isDominant _
  have hf0 : f = 0 := g.app_injective U (by rw [hgf, map_zero])
  have ht0 : t = 0 := by rw [← hf, hf0]; exact zero_smul _ _
  exact eq_zero_of_map_eq_zero M ⟨g y0, hyU⟩ s ht0

/-- `scalarsToGlobalSections k sX` is the composite of `(ΓSpecIso k).inv` with `sX.appLE ⊤ ⊤`. -/
private theorem scalarsToGlobalSections_eq_appLE {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) :
    scalarsToGlobalSections k sX =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appLE ⊤ ⊤ (by simp)).hom := by
  have : sX.appLE ⊤ ⊤ (by simp) = sX.appTop := by
    simp [Scheme.Hom.appLE]
    exact Category.comp_id _
  rw [this]; rfl

/-- The global sections of `𝒪_Y(D)`, `D` Cartier on a proper `k`-scheme, are finite over `k`. -/
private theorem finite_divisorialSubmodule_top {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k))
    [IsProper sY] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {D : Divisor Y}
    (hD : D.IsCartier) :
    letI := Module.compHom (D.divisorialSubmodule ⊤) (scalarsToGlobalSections k sY);
    Module.Finite k (D.divisorialSubmodule ⊤) := by
  have := hD.isInvertibleModule_divisorialSheaf
  have := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k sY
    D.divisorialSheaf 1
  have := finiteDimensional_cohomologyOverField_of_isProper k sY D.divisorialSheaf 0
  have e := (cohomologyOverFieldZeroLinearIso k sY D.divisorialSheaf).toLinearEquiv
  have key : ∀ ψ : k →+* Γ(Y, ⊤),
      ψ = ((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appLE ⊤ ⊤ (by simp)).hom →
        (letI := Module.compHom (D.divisorialSubmodule ⊤) ψ;
          Module.Finite k (D.divisorialSubmodule ⊤)) := by
    rintro ψ rfl
    have := Module.Finite.equiv e
    exact this
  exact key _ (scalarsToGlobalSections_eq_appLE sY)

/-- Pull-back of sections along a dominant morphism of proper varieties: `h⁰(X, 𝒪_X(D)) ≤
h⁰(V, 𝒪_V(D'))` when `𝒪_V(D') ≅ u^* 𝒪_X(D)`. -/
private theorem h0_le_of_iso_pullback {X V : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    {sV : V ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral V] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V] [IsProper sV]
    (u : V ⟶ X) (hu : u ≫ sX = sV) [IsDominant u] [QuasiCompact u] {D : Divisor X}
    (hDc : D.IsCartier) {D' : Divisor V} (hD'c : D'.IsCartier)
    (E : D'.divisorialSheaf ≅ (Scheme.Modules.pullback u).obj D.divisorialSheaf) :
    Divisor.h0 k sX D ≤ Divisor.h0 k sV D' := by
  have hsc : ∀ c, u.appTop (scalarsToGlobalSections k sX c) = scalarsToGlobalSections k sV c := by
    intro c
    subst hu
    simp only [scalarsToGlobalSections, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
      RingHom.comp_apply]
  haveI := hDc.isInvertibleModule_divisorialSheaf
  set M := D.divisorialSheaf with hM
  let η := (Scheme.Modules.pullbackPushforwardAdjunction u).unit.app M
  letI := Module.compHom Γ(M, ⊤) (scalarsToGlobalSections k sX)
  letI := Module.compHom (D'.divisorialSubmodule ⊤) (scalarsToGlobalSections k sV)
  have : Module.Finite k (D'.divisorialSubmodule ⊤) := finite_divisorialSubmodule_top sV hD'c
  let φ : Γ(M, ⊤) →ₗ[k] D'.divisorialSubmodule ⊤ :=
    { toFun s := E.inv.app ⊤ (η.app ⊤ s)
      map_add' s t := by
        rw [map_add]
        exact map_add _ _ _
      map_smul' c s := by
        change E.inv.app ⊤ (η.app ⊤ (scalarsToGlobalSections k sX c • s)) =
          (scalarsToGlobalSections k sV c • (E.inv.app ⊤ (η.app ⊤ s) : D'.divisorialSubmodule ⊤))
        rw [Scheme.Modules.Hom.app_smul, ← hsc c]
        exact Scheme.Modules.Hom.app_smul E.inv _ _ }
  have h2 : ∀ x, E.hom.app ⊤ (E.inv.app ⊤ x) = x := fun x => by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, E.inv_hom_id]
    rfl
  have hφ : Function.Injective φ := fun s t hst => by
    refine unit_app_top_injective u M ?_
    have := congrArg (E.hom.app ⊤) hst
    change E.hom.app ⊤ (E.inv.app ⊤ (η.app ⊤ s)) = E.hom.app ⊤ (E.inv.app ⊤ (η.app ⊤ t)) at this
    exact (h2 _).symm.trans (this.trans (h2 _))
  change Module.finrank k Γ(M, ⊤) ≤ Module.finrank k (D'.divisorialSubmodule ⊤)
  exact LinearMap.finrank_le_finrank_of_injective hφ

/-- The pull-back of a big Cartier divisor along a birational morphism of proper normal
varieties is big. -/
private theorem isBig_of_isPullback {X V : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    {sV : V ⟶ Spec (.of k)} (hXp : MMP.Mori.IsProperVariety k sX)
    (hVp : MMP.Mori.IsProperVariety k sV) [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian V] [IsNormal V] (u : V ⟶ X) (hu : u ≫ sX = sV)
    (hub : IsBirationalMorphism u) {D : Divisor X} (hDc : D.IsCartier) (hD : D.IsBig k sX)
    {hB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ D.supp}
    {D' : Divisor V} (h : D.IsPullback u hB D') : D'.IsBig k sV := by
  have hXv := ((MMP.Mori.isProperVariety_iff k sX).mp hXp).1
  have hVv := ((MMP.Mori.isProperVariety_iff k sV).mp hVp).1
  haveI : IsIntegral X := hXv.toIsIntegral
  haveI : IsIntegral V := hVv.toIsIntegral
  haveI : QuasiCompact sX := hXv.toQuasiCompact
  haveI : QuasiCompact sV := hVv.toQuasiCompact
  haveI : IsSeparated sX := hXv.toIsSeparated
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  haveI : IsProper sV := ((MMP.Mori.isProperVariety_iff k sV).mp hVp).2
  haveI : IsDominant u := hub.isDominant
  haveI : QuasiCompact (u ≫ sX) := hu ▸ inferInstance
  haveI : QuasiCompact u := QuasiCompact.of_comp u sX
  haveI := hXv
  haveI := hVv
  have hdim : topologicalKrullDim X = topologicalKrullDim V :=
    MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX sV hub
  obtain ⟨n, hn, c, hc, k₀, hk⟩ := hD
  refine ⟨n, hdim ▸ hn, c, hc, k₀, fun j hj => (hk j hj).trans_le ?_⟩
  have hBj : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ (j • D).supp :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' u _
  have hpj := h.zsmul hDc j hBj
  exact_mod_cast h0_le_of_iso_pullback u hu (hDc.zsmul j) (hpj.isCartier (hDc.zsmul j))
    (hpj.divisorialSheafIso (hBc := hDc.zsmul j))

/-! ### Ample plus effective on a smooth projective variety -/

/-- An `R`-linear equivalence between `R`-modules that are `k`-vector spaces through a ring map
`φ : k →+* R` preserves the `k`-dimension. -/
private theorem finrank_compHom_eq {R : Type} [CommRing R] (φ : k →+* R) {M N : Type}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (g : M ≃ₗ[R] N) :
    (letI := Module.compHom M φ; Module.finrank k M) =
      (letI := Module.compHom N φ; Module.finrank k N) := by
  letI := Module.compHom M φ
  letI := Module.compHom N φ
  let g' : M ≃ₗ[k] N :=
    { g.toEquiv with map_add' := g.map_add, map_smul' := fun c x => g.map_smul (φ c) x }
  exact g'.finrank_eq

/-- `h⁰` of a Cartier divisor `A` equals `h⁰` of a divisor `D` with `𝒪_X(A) ≅ 𝒪_X(D)`. -/
private theorem cartierH0_eq_h0 {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [IsLocallyNoetherian X]
    [IsNormal X] (A : X.CartierDivisor) (D : Divisor X)
    (e : MMP.CartierDivisor.sheaf A ≅ D.divisorialSheaf) :
    cartierH0 k sX A = D.h0 k sX :=
  finrank_compHom_eq (scalarsToGlobalSections k sX) (Scheme.Modules.sectionsLinearEquiv e ⊤)

/-- The Weil divisor `[D]` of a Cartier divisor. -/
private lemma isWeilDivisorOfCartier_cartierWeilDivisor {S : Scheme.{0}} [IsIntegral S]
    [IsNoetherian S] (D : S.CartierDivisor) :
    MMP.Intersection.IsWeilDivisorOfCartier D (weilDivisorEquivFinsupp (cartierWeilDivisor D)) := by
  intro P
  have hcoh : Order.coheight (MMP.Mori.PrimeDivisor.genericPoint P) = 1 :=
    AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P
  haveI : Ring.KrullDimLE 1
      (S.presheaf.stalk (MMP.Intersection.primeDivisorSubvariety P).genericPoint) :=
    krullDimLE_of_coheight_le hcoh.le
  obtain ⟨N, hN⟩ :=
    MMP.Intersection.exists_isOrderAlong D (MMP.Intersection.primeDivisorSubvariety P)
  convert hN using 1
  have hN' := hN
  unfold MMP.Intersection.IsOrderAlong at hN'
  dsimp only [MMP.Intersection.primeDivisorSubvariety_genericPoint] at hN'
  obtain ⟨a, b, ha, hb, ⟨g, hg, hgab⟩, la, lb, hla, hlb, rfl⟩ := hN'
  change cartierMultiplicity D (MMP.Mori.PrimeDivisor.genericPoint P) = _
  rw [MMP.Intersection.cartierMultiplicity_eq_ord_of_isLocalEquationAt hg]
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap (S.presheaf.stalk _) S.functionField b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have key : totalQuotientStalkToFunctionField _ g *
      algebraMap (S.presheaf.stalk _) S.functionField b =
      algebraMap (S.presheaf.stalk _) S.functionField a := by
    have := congrArg (totalQuotientStalkToFunctionField _) hgab.2
    rw [map_mul, MMP.Intersection.totalQuotientStalkToFunctionField_stalkToTotalQuotient,
      MMP.Intersection.totalQuotientStalkToFunctionField_stalkToTotalQuotient] at this
    rw [mul_comm]
    exact this
  have hTg := MMP.Intersection.totalQuotientStalkToFunctionField_ne_zero_of_isLocalEquationAt hg
  have hord := S.ord_mul (x := MMP.Mori.PrimeDivisor.genericPoint P) hTg hbK
  rw [key, ord_algebraMap_stalk _ hcoh a ha0, ord_algebraMap_stalk _ hcoh b hb0] at hord
  erw [hla, hlb, ENat.toNat_coe, ENat.toNat_coe] at hord
  omega

/-- **Kodaira's lemma** on a smooth projective variety: a big divisor `D` has a multiple `mD`
with `𝒪(mD) ≅ 𝒪(a + e)`, `a` ample and `e` effective. -/
private theorem exists_isAmple_add_nonneg {X : Scheme.{0}} (sX : X ⟶ Spec (.of k))
    [IsSmoothVariety k sX] (hXp : MMP.Mori.IsProjectiveVariety k sX) [IsLocallyNoetherian X]
    [CompactSpace X] [IsNormal X] (D : Divisor X) (hD : D.IsBig k sX) :
    ∃ m : ℕ, 0 < m ∧ ∃ (a e : Divisor X) (ha : a.IsCartier), a.IsAmple ha ∧ 0 ≤ e ∧
      Nonempty ((m • D).divisorialSheaf ≅ (a + e).divisorialSheaf) := by
  have hXv := (isSmoothVariety_iff k sX).mp ‹_›
  haveI : IsIntegral X := hXv.1.toIsIntegral
  haveI : IsNoetherian X := ⟨⟩
  obtain ⟨hcart, -, hbij, hiso, -, -⟩ := Divisor.cartier_weil_dictionary_of_isSmoothVariety k sX
  have hiso' : ∀ τ : X.CartierDivisor,
      Nonempty ((weilOfCartier X τ).divisorialSheaf ≅ MMP.CartierDivisor.sheaf τ) := hiso
  obtain ⟨τ, hτ⟩ := hbij.2 D
  change weilOfCartier X τ = D at hτ
  obtain ⟨n, hn, c, hc, k₀, hk⟩ := hD
  have hh0 : ∀ j : ℕ, cartierH0 k sX (j • τ) = Divisor.h0 k sX ((j : ℤ) • D) := by
    intro j
    obtain ⟨e⟩ := hiso' (j • τ)
    rw [map_nsmul, hτ, ← natCast_zsmul] at e
    exact cartierH0_eq_h0 sX _ _ (e.symm)
  have hinf : {m : ℕ | c * (m : ℝ) ^ n < (cartierH0 k sX (m • τ) : ℝ)}.Infinite := by
    refine Set.infinite_of_forall_exists_gt fun a => ⟨max (a + 1) k₀.toNat, ?_,
      lt_of_lt_of_le (Nat.lt_succ_self a) (le_max_left _ _)⟩
    simp only [Set.mem_setOf_eq]
    rw [hh0]
    have hle : k₀ ≤ ((max (a + 1) k₀.toNat : ℕ) : ℤ) :=
      (Int.self_le_toNat k₀).trans (by exact_mod_cast le_max_right _ _)
    have := hk _ hle
    push_cast at this ⊢
    exact this
  obtain ⟨m, hm, A, E, -, hAamp, hE, hlin⟩ :=
    exists_linearlyEquivalent_ample_add_effective sX hXp hn τ ⟨c, hc, hinf⟩
  refine ⟨m, hm, weilOfCartier X A, weilOfCartier X E, hcart _, ?_, ?_, ?_⟩
  · obtain ⟨eA⟩ := hiso' A
    haveI := (hcart (weilOfCartier X A)).isInvertibleModule_divisorialSheaf
    exact (Stacks.RelativeVeryAmple.isAmple_congr _ _ eA).mpr hAamp
  · intro P
    change (0 : ℤ) ≤
      DivisorWithCoeffs.coeff (weilDivisorEquivFinsupp (cartierWeilDivisor E) : Divisor X) P
    exact (isWeilDivisorOfCartier_cartierWeilDivisor E P).nonneg_of_isEffective hE
  · obtain ⟨φ, hφ⟩ := MMP.Intersection.mem_principalSubgroup_iff.mp hlin
    have e1 : MMP.CartierDivisor.sheaf (A + E) ≅ MMP.CartierDivisor.sheaf (m • τ) :=
      MMP.CartierDivisor.sheafAddPrincipalIso (A + E) φ ≪≫
        eqToIso (by rw [hφ, add_sub_cancel])
    obtain ⟨eτ⟩ := hiso' (m • τ)
    obtain ⟨eAE⟩ := hiso' (A + E)
    rw [map_nsmul, hτ] at eτ
    rw [map_add] at eAE
    exact ⟨eτ ≪≫ e1.symm ≪≫ eAE.symm⟩

/-! ### Relatively ample plus a pull-back of an ample divisor -/

/-- Relative ampleness of an invertible sheaf is invariant under isomorphism. -/
private theorem isRelativelyAmple_of_iso {X Y : Scheme.{0}} {f : X ⟶ Y} {L L' : X.Modules}
    [Stacks.Ample.IsInvertibleModule X L] [Stacks.Ample.IsInvertibleModule X L'] (e : L ≅ L')
    (h : IsRelativelyAmple f L) : IsRelativelyAmple f L' := by
  intro y
  obtain ⟨V, hV, hyV, hamp⟩ := h y
  refine ⟨V, hV, hyV, ?_⟩
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _
    ((RingedSpaceModuleAdjunction.modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).mapIso e)).1 hamp

/-- For `h : Y ⟶ X` a morphism of smooth projective varieties, `L` an `h`-ample divisor on `Y`
and `a` an ample divisor on `X`, `L + ν h^*a` is ample for some `ν > 0`. -/
private theorem exists_isAmple_add_nsmul {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    {sY : Y ⟶ Spec (.of k)} [IsSmoothVariety k sX] [IsSmoothVariety k sY]
    (hXp : MMP.Mori.IsProjectiveVariety k sX) (hYp : MMP.Mori.IsProjectiveVariety k sY)
    [IsLocallyNoetherian X] [CompactSpace X] [IsNormal X] [IsLocallyNoetherian Y]
    [CompactSpace Y] [IsNormal Y] (h : Y ⟶ X) (hh : h ≫ sX = sY) {a : Divisor X}
    (ha : a.IsCartier) (hamp : a.IsAmple ha)
    {hB : ∀ Z : irreducibleComponents Y, h (componentGenericPoint Y Z) ∉ a.supp}
    {b : Divisor Y} (hb : a.IsPullback h hB b) {L : Divisor Y} (hL : L.IsCartier)
    (hLamp : L.IsRelativelyAmple h hL) :
    ∃ ν : ℕ, 0 < ν ∧ ∃ hG : (L + ν • b).IsCartier, (L + ν • b).IsAmple hG := by
  have hXv := (isSmoothVariety_iff k sX).mp ‹_›
  have hYv := (isSmoothVariety_iff k sY).mp ‹_›
  haveI : IsIntegral X := hXv.1.toIsIntegral
  haveI : IsIntegral Y := hYv.1.toIsIntegral
  haveI : IsNoetherian X := ⟨⟩
  haveI : IsNoetherian Y := ⟨⟩
  obtain ⟨-, -, hbijX, hisoX, -, -⟩ := Divisor.cartier_weil_dictionary_of_isSmoothVariety k sX
  obtain ⟨hcartY, -, hbijY, hisoY, -, -⟩ :=
    Divisor.cartier_weil_dictionary_of_isSmoothVariety k sY
  have hisoX' : ∀ τ : X.CartierDivisor,
      Nonempty ((weilOfCartier X τ).divisorialSheaf ≅ MMP.CartierDivisor.sheaf τ) := hisoX
  have hisoY' : ∀ τ : Y.CartierDivisor,
      Nonempty ((weilOfCartier Y τ).divisorialSheaf ≅ MMP.CartierDivisor.sheaf τ) := hisoY
  obtain ⟨M, hM⟩ := hbijX.2 a
  obtain ⟨Lc, hLc⟩ := hbijY.2 L
  obtain ⟨Bc, hBc⟩ := hbijY.2 b
  change weilOfCartier X M = a at hM
  change weilOfCartier Y Lc = L at hLc
  change weilOfCartier Y Bc = b at hBc
  obtain ⟨eM⟩ := hisoX' M
  obtain ⟨eL⟩ := hisoY' Lc
  obtain ⟨eB⟩ := hisoY' Bc
  rw [hM] at eM
  rw [hLc] at eL
  rw [hBc] at eB
  haveI := ha.isInvertibleModule_divisorialSheaf
  haveI := hL.isInvertibleModule_divisorialSheaf
  haveI := (hcartY b).isInvertibleModule_divisorialSheaf
  have hMamp : Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf M) :=
    (Stacks.RelativeVeryAmple.isAmple_congr _ _ eM).mp hamp
  have hLamp' : IsRelativelyAmple h (MMP.CartierDivisor.sheaf Lc) :=
    isRelativelyAmple_of_iso eL hLamp
  have hB : Nonempty (MMP.CartierDivisor.sheaf Bc ≅
      (Scheme.Modules.pullback h).obj (MMP.CartierDivisor.sheaf M)) :=
    ⟨eB.symm ≪≫ hb.divisorialSheafIso (hBc := ha) ≪≫ (Scheme.Modules.pullback h).mapIso eM⟩
  obtain ⟨ν, hν, hν1⟩ := ((MMP.Foundations.isAmple_add_zsmul_pullback k hYp hXp hh hMamp hLamp'
    hB).and (Filter.eventually_ge_atTop 1)).exists
  lift ν to ℕ using (by omega)
  refine ⟨ν, by omega, hcartY _, ?_⟩
  obtain ⟨e⟩ := hisoY' (Lc + (ν : ℤ) • Bc)
  rw [map_add, map_zsmul, hLc, hBc, natCast_zsmul] at e
  haveI := (hcartY (L + ν • b)).isInvertibleModule_divisorialSheaf
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _ e).mpr hν

/-! ### Snc divisors -/

/-- An `ℝ`-divisor whose support contains an snc divisor `S` and the support of an effective
divisor `e`. -/
private theorem exists_rDivisor_le_supp {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of k)}
    {S : TopologicalSpace.Closeds Y} (hS : IsSNCSubset sY S) (e : Divisor Y) (he : 0 ≤ e) :
    ∃ Δ' : RDivisor Y, S ≤ Δ'.supp ∧ e.supp ≤ Δ'.supp := by
  classical
  rcases hS with rfl | ⟨s, hs, -⟩
  · exact ⟨Divisor.toRDivisor e, bot_le, by rw [Divisor.supp_toRDivisor]⟩
  set R : Divisor Y := ∑ E ∈ s, Finsupp.single E (1 : ℤ) with hR
  have hR1 : ∀ E ∈ s, R E = 1 := fun E hE => by
    rw [hR, Finsupp.finset_sum_apply]
    simp [Finsupp.single_apply, hE]
  have hR0 : 0 ≤ R := fun E => by
    rw [hR, Finsupp.finset_sum_apply]
    exact Finset.sum_nonneg fun F _ => by
      rw [Finsupp.single_apply]; split_ifs <;> simp
  refine ⟨Divisor.toRDivisor (e + R), ?_, ?_⟩
  · intro x hx
    rw [Divisor.supp_toRDivisor]
    have hx' : x ∈ (S : Set Y) := hx
    rw [← hs, Set.mem_iUnion₂] at hx'
    obtain ⟨E, hE, hxE⟩ := hx'
    refine DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, ?_, hxE⟩
    rw [DivisorWithCoeffs.coeff_apply, Finsupp.add_apply, hR1 E hE]
    have := he E
    simp only [Finsupp.coe_zero, Pi.zero_apply] at this
    omega
  · intro x hx
    rw [Divisor.supp_toRDivisor]
    obtain ⟨E, hE, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hx
    refine DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, ?_, hxE⟩
    rw [DivisorWithCoeffs.coeff_apply] at hE ⊢
    rw [Finsupp.add_apply]
    have h1 := he E
    have h2 := hR0 E
    simp only [Finsupp.coe_zero, Pi.zero_apply] at h1 h2
    omega

/-! ### Degrees of integer multiples -/

/-- **The ample twist.** On a smooth projective variety `Y`, let `G` be ample, `E` effective
with support in a finite set `F` of prime divisors, and `D = n₀ fB` Cartier with
`deg_C G + deg_C E = N deg_C D` on every curve `C`. Then `fB - ∑_{P ∈ F} p_P P` is ample for some
rationals `p_P > 0`. -/
private theorem exists_isAmple_sub_sum_single {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k))
    [IsSmoothVariety k sY] [MMP.Mori.IsProjectiveVariety k sY] [IsLocallyNoetherian Y]
    [CompactSpace Y] [IsNormal Y] {G : Divisor Y} (hGc : G.IsCartier) (hGamp : G.IsAmple hGc)
    {E : Divisor Y} (hE0 : 0 ≤ E) (hEc : E.IsCartier) (F : Finset (MMP.Mori.PrimeDivisor Y))
    (hEF : ∀ P, E P ≠ 0 → P ∈ F) {n₀ : ℕ} (hn₀ : 0 < n₀) {fB : QDivisor Y} {D : Divisor Y}
    (hDc : D.IsCartier) (hD : Divisor.toQDivisor D = (n₀ : ℚ) • fB) {N : ℕ} (hN : 0 < N)
    (hdeg : ∀ (C : Scheme.{0}) (i : C ⟶ Y) [IsProper (i ≫ sY)] (hdim : topologicalKrullDim C ≤ 1),
      G.degreeOn k sY i hdim hGc + E.degreeOn k sY i hdim hEc =
        (N : ℤ) * D.degreeOn k sY i hdim hDc) :
    ∃ p : MMP.Mori.PrimeDivisor Y → ℚ, (∀ P ∈ F, 0 < p P) ∧
      (fB - ∑ P ∈ F, Finsupp.single P (p P)).IsAmple := by
  classical
  have hYv := (isSmoothVariety_iff k sY).mp ‹_›
  haveI : IsIntegral Y := hYv.1.toIsIntegral
  haveI : IsNoetherian Y := ⟨⟩
  obtain ⟨hYcart, -, hbijY, hisoY, -, hYq⟩ :=
    Divisor.cartier_weil_dictionary_of_isSmoothVariety k sY
  have hisoY' : ∀ τ : Y.CartierDivisor,
      Nonempty ((weilOfCartier Y τ).divisorialSheaf ≅ MMP.CartierDivisor.sheaf τ) := hisoY
  /- `H = M G - ∑_{P ∈ F} P` is ample for some `M ≥ 1`. -/
  set sumF : Divisor Y := ∑ P ∈ F, Finsupp.single P (1 : ℤ) with hsumF
  obtain ⟨τG, hτG⟩ := hbijY.2 G
  obtain ⟨τF, hτF⟩ := hbijY.2 (-sumF)
  change weilOfCartier Y τG = G at hτG
  change weilOfCartier Y τF = -sumF at hτF
  haveI := hGc.isInvertibleModule_divisorialSheaf
  have hτGamp : Stacks.Ample.IsAmple Y (MMP.CartierDivisor.sheaf τG) := by
    obtain ⟨eG⟩ := hisoY' τG
    rw [hτG] at eG
    exact (Stacks.RelativeVeryAmple.isAmple_congr _ _ eG).mp hGamp
  obtain ⟨M, hMamp, hM1⟩ := ((MMP.Mori.eventually_isAmple_cartierSheaf_nsmul_add τG τF
    hτGamp).and (Filter.eventually_ge_atTop 1)).exists
  set H : Divisor Y := (M : ℤ) • G - sumF with hH
  have hHc : H.IsCartier := hYcart H
  have hHamp : H.IsAmple hHc := by
    obtain ⟨eH⟩ := hisoY' (M • τG + τF)
    rw [map_add, map_nsmul, hτG, hτF, ← natCast_zsmul, ← sub_eq_add_neg] at eH
    haveI := hHc.isInvertibleModule_divisorialSheaf
    exact (Stacks.RelativeVeryAmple.isAmple_congr _ _ eH).mpr hMamp
  /- `Dfin = M (N D - E) - ∑ P = mt (fB - ∑ p_P P)` has the degrees of `H`. -/
  set mt : ℕ := n₀ * N * M with hmt
  have hmtpos : 0 < mt := Nat.mul_pos (Nat.mul_pos hn₀ hN) (by omega)
  have hmtq : (mt : ℚ) ≠ 0 := by exact_mod_cast hmtpos.ne'
  set Dfin : Divisor Y := (M : ℤ) • ((N : ℤ) • D - E) - sumF with hDfin
  set p : MMP.Mori.PrimeDivisor Y → ℚ := fun P => ((M * E P + 1 : ℤ) : ℚ) / mt with hp
  have hQeq : Divisor.toQDivisor Dfin =
      (mt : ℚ) • (fB - ∑ P ∈ F, Finsupp.single P (p P)) := by
    ext P
    have hDP : (Divisor.toQDivisor D) P = (n₀ : ℚ) * fB P := by simpa using congrArg (· P) hD
    have hsumP : sumF P = if P ∈ F then 1 else 0 := by simp [hsumF, Finsupp.single_apply]
    have hpP : (∑ P' ∈ F, Finsupp.single P' (p P')) P = if P ∈ F then p P else 0 := by
      simp [Finsupp.single_apply]
    simp [hDfin]
    simp only [DivisorWithCoeffs.coeff_apply, hsumP, hpP, show (D P : ℚ) = _ from hDP]
    split_ifs with hPF
    · simp only [hp]
      field_simp
      rw [hmt]; push_cast; ring
    · have h0 : E P = 0 := by by_contra h0; exact hPF (hEF P h0)
      rw [h0, hmt]; push_cast; ring
  have hDH : Dfin = H + (M : ℤ) • ((N : ℤ) • D + (-1 : ℤ) • (G + E)) := by
    rw [hDfin, hH]; module
  have hDfindeg : ∀ (C : Scheme.{0}) (i : C ⟶ Y) [IsProper (i ≫ sY)]
      (hdim : topologicalKrullDim C ≤ 1),
      Dfin.degreeOn k sY i hdim (hYcart _) = H.degreeOn k sY i hdim hHc := by
    intro C i _ hdim
    rw [Divisor.degreeOn_congr hDH (hYcart _) (hYcart _),
      Divisor.degreeOn_add k _ i hdim _ _ hHc (hYcart _),
      Fourfold.degreeOn_zsmul _ i hdim _ (hYcart _),
      Divisor.degreeOn_add k _ i hdim _ _ (hYcart _) (hYcart _),
      Fourfold.degreeOn_zsmul _ i hdim _ hDc, Fourfold.degreeOn_zsmul _ i hdim _ (hYcart _),
      Divisor.degreeOn_add k _ i hdim _ _ hGc hEc, hdeg C i hdim]
    ring
  /- Numerical invariance of ampleness. -/
  refine ⟨p, fun P _ => div_pos (by have := hE0 P; simp at this; positivity)
    (by exact_mod_cast hmtpos), ?_⟩
  have hA : ((mt : ℚ)⁻¹ • Divisor.toQDivisor H).IsAmple :=
    ⟨mt, hmtpos, H, by rw [smul_smul, mul_inv_cancel₀ hmtq, one_smul], hHc, hHamp⟩
  have h0nef : (0 : MMP.Mori.QDivisor Y).IsNef k sY :=
    ⟨QDivisor.isQCartier_zero, fun C i _ _ _ hC =>
      (MMP.Fourfold.intersectionNumber_zero _ i hC.le).ge⟩
  have hnum : (fB - ∑ P ∈ F, Finsupp.single P (p P)).NumericallyEquivalent k sY
      ((mt : ℚ)⁻¹ • Divisor.toQDivisor H + 0) := by
    rw [add_zero]
    refine ⟨hYq _, hYq _, fun C i _ _ _ hC => ?_⟩
    have hz1 : Divisor.toQDivisor Dfin =
        ((mt : ℕ) : ℤ) • (fB - ∑ P ∈ F, Finsupp.single P (p P)) := by
      rw [hQeq, ← Int.cast_smul_eq_zsmul ℚ]; norm_cast
    have hz2 : Divisor.toQDivisor H = ((mt : ℕ) : ℤ) • ((mt : ℚ)⁻¹ • Divisor.toQDivisor H) := by
      rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul]
      push_cast
      rw [mul_inv_cancel₀ hmtq, one_smul]
    rw [QDivisor.intersectionNumber_eq_of_smul k _ i hC.le _ _ hmtpos Dfin (hYcart _) hz1,
      QDivisor.intersectionNumber_eq_of_smul k _ i hC.le _ _ hmtpos H hHc hz2,
      hDfindeg C i hC.le]
  exact ⟨mt, hmtpos, Dfin, hQeq, hYcart _,
    QDivisor.isAmple_of_numericallyEquivalent_add_of_isNef sY hA h0nef hnum mt hmtpos Dfin hQeq
      (hYcart _)⟩

end KM2c

/-! ### Snc subsets as finite sets of prime divisors -/

/-- An snc divisor is the union of a finite set of prime divisors whose reduced sum is snc. -/
private theorem exists_finset_of_isSNCSubset {k : Type} [Field k] {Y : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} [LocallyOfFinitePresentation sY] (hsm : IsSmoothScheme sY)
    {S : Closeds Y} (hS : IsSNCSubset sY S) :
    ∃ s : Finset (MMP.Mori.PrimeDivisor Y), (⋃ E ∈ s, E.support) = (S : Set Y) ∧
      DivisorWithCoeffs.IsSNC sY (∑ E ∈ s, Finsupp.single E (1 : ℤ)) := by
  rcases hS with rfl | ⟨s, hs, hsnc⟩
  · refine ⟨∅, by simp, ?_⟩
    rw [Finset.sum_empty]
    exact DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme (R := ℤ) sY hsm
  · exact ⟨s, hs, hsnc⟩

/-- **Projective log resolutions adapted to an ideal with an ample boundary subtraction.** Let
`X` be a proper normal variety over an algebraically closed field `k` of characteristic zero,
`Δ` a `ℚ`-divisor on `X`, `I` a nonzero ideal sheaf on `X` and `B` a nef and big `ℚ`-Cartier
`ℚ`-divisor on `X`. Then there are a log resolution `f : Y ⟶ X` of `(X, Δ)` with `Y` projective
over `k`, an effective Cartier divisor `D_I` on `Y` with `f⁻¹I · 𝒪_Y = 𝒪_Y(-D_I)`, a finite set
`F` of prime divisors of `Y` with `∑_{E ∈ F} E` snc and `⋃_{E ∈ F} E ⊇ Ex(f) ∪ f⁻¹(Supp Δ) ∪
Supp D_I`, and rationals `p E > 0` for `E ∈ F` such that `f^*B - ∑_{E ∈ F} p E • E` is ample. -/
@[mmp "lem_mmp_foundation_km3a_projective_resolution_with_additional_boundary"]
public theorem exists_isLogResolution_isAmple_pullback_sub_sum {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k))
    [IsProperVariety k sX] [IsLocallyNoetherian X] [IsNormal X] (Δ : QDivisor X)
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (B : QDivisor X) (hnef : B.IsNef k sX)
    (hbig : B.IsBig k sX) :
    ∃ (Y : Scheme.{0}) (f : Y ⟶ X), IsLogResolution sX (QDivisor.toRDivisor Δ) f ∧
      IsProjectiveVariety k (f ≫ sX) ∧
      ∃ (_ : IsLocallyNoetherian Y) (_ : IsNormal Y) (_ : CompactSpace Y) (D : Divisor Y),
        0 ≤ D ∧ D.IsCartier ∧ I.comap f = MMP.Resolution.divisorIdeal (fun E => (D E).toNat) ∧
        ∃ F : Finset (PrimeDivisor Y),
          DivisorWithCoeffs.IsSNC (f ≫ sX) (∑ E ∈ F, Finsupp.single E (1 : ℤ)) ∧
          (exceptionalSet f : Set Y) ∪ f ⁻¹' (Δ.supp : Set X) ∪ (D.supp : Set Y) ⊆
            ⋃ E ∈ F, E.support ∧
          ∃ (hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ B.supp)
            (fB : QDivisor Y) (p : PrimeDivisor Y → ℚ), B.IsPullback f hB fB ∧
            (∀ E ∈ F, 0 < p E) ∧
            (fB - ∑ E ∈ F, Finsupp.single E (p E)).IsAmple := by
  have hXp : IsProperVariety k sX := inferInstance
  classical
  /- The variety `X`. -/
  have hXv : MMP.Mori.IsVariety k sX := ((MMP.Mori.isProperVariety_iff k sX).mp hXp).1
  haveI : IsProper sX := ((MMP.Mori.isProperVariety_iff k sX).mp hXp).2
  have hXN : IsNormalVariety k sX := ⟨hXv, inferInstance⟩
  haveI : IsIntegral X := hXv.toIsIntegral
  haveI : QuasiCompact sX := hXv.toQuasiCompact
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  /- The Cartier multiple `D₀ = n₀ B`, nef and big. -/
  obtain ⟨n₀, hn₀, D₀, hD₀, hD₀c, hD₀big⟩ := hbig
  have hBq : B.IsQCartier := hnef.1
  have hD₀z : Divisor.toQDivisor D₀ = ((n₀ : ℕ) : ℤ) • B := by
    rw [hD₀, ← Int.cast_smul_eq_zsmul ℚ]; norm_cast
  /- Step 1: `f₀ : T ⟶ X`. -/
  obtain ⟨T, g, hg, hTp, hIcart, S₀, hS₀, hS₀1, hS₀2⟩ :=
    exists_isLogResolution_isProjectiveVariety_comap sX hXv (QDivisor.toRDivisor Δ) I hI
  have hX'N : IsNormalVariety k (g ≫ sX) := (hg.toIsSmoothResolution.isNormalVariety hXN).1
  have hX'p : MMP.Mori.IsProjectiveVariety k (g ≫ sX) := hTp
  haveI : IsSmoothVariety k (g ≫ sX) :=
    isSmoothVariety_of_isSmoothResolution hXN hg.toIsSmoothResolution
  haveI : IsIntegral T := hX'N.1.toIsIntegral
  haveI : IsNormal T := hX'N.2
  haveI : QuasiCompact (g ≫ sX) := hX'N.1.toQuasiCompact
  haveI : LocallyOfFiniteType (g ≫ sX) := hX'N.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sX)
  haveI : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace (g ≫ sX)
  haveI : IsNoetherian T := ⟨⟩
  have hX'cart := (Divisor.cartier_weil_dictionary_of_isSmoothVariety k (g ≫ sX)).1
  have hgb := hg.isBirationalMorphism
  haveI : IsDominant g := hgb.isDominant
  haveI : IsProper g := hg.isProper
  have hX'pr : MMP.Mori.IsProperVariety k (g ≫ sX) :=
    (MMP.Mori.isProperVariety_iff k _).mpr ⟨hX'N.1, isProper_of_isProjectiveMorphism _
      ((MMP.Mori.isProjectiveVariety_iff k _).mp hX'p).2⟩
  have hBg : ∀ Z : irreducibleComponents T, g (componentGenericPoint T Z) ∉ D₀.supp :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' g D₀
  obtain ⟨D₁, hD₁⟩ := hD₀c.exists_isPullback hBg
  have hD₁big : D₁.IsBig k (g ≫ sX) := isBig_of_isPullback hXp hX'pr g rfl hgb hD₀c hD₀big hD₁
  obtain ⟨m, hm, a, e, hac, hamp, he0, ⟨eae⟩⟩ :=
    exists_isAmple_add_nonneg (g ≫ sX) hX'p D₁ hD₁big
  /- The boundary `Δ''` of the second resolution and `h : Y ⟶ T`. -/
  obtain ⟨Δ'', hΔ''1, hΔ''2⟩ := exists_rDivisor_le_supp hS₀ e he0
  obtain ⟨Y, h, hh, hhp⟩ := MMP.Mori.exists_isLogResolution_isProjectiveMorphism (g ≫ sX) hX'N Δ''
  have hf : IsLogResolution sX (QDivisor.toRDivisor Δ) (h ≫ g) := hg.comp (hS₀1.trans hΔ''1) hh
  have ht : h ≫ g ≫ sX = (h ≫ g) ≫ sX := (Category.assoc _ _ _).symm
  have hYN : IsNormalVariety k ((h ≫ g) ≫ sX) :=
    ht ▸ (hh.toIsSmoothResolution.isNormalVariety hX'N).1
  haveI hYp : MMP.Mori.IsProjectiveVariety k ((h ≫ g) ≫ sX) :=
    ht ▸ isProjectiveVariety_comp hX'N hX'p hh.toIsSmoothResolution hhp
  haveI : IsSmoothVariety k ((h ≫ g) ≫ sX) :=
    ht ▸ isSmoothVariety_of_isSmoothResolution hX'N hh.toIsSmoothResolution
  haveI : IsIntegral Y := hYN.1.toIsIntegral
  haveI : IsNormal Y := hYN.2
  haveI : QuasiCompact ((h ≫ g) ≫ sX) := hYN.1.toQuasiCompact
  haveI : LocallyOfFiniteType ((h ≫ g) ≫ sX) := hYN.1.toLocallyOfFiniteType
  haveI : IsSeparated ((h ≫ g) ≫ sX) := hYN.1.toIsSeparated
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian ((h ≫ g) ≫ sX)
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace ((h ≫ g) ≫ sX)
  haveI : IsNoetherian Y := ⟨⟩
  haveI : LocallyOfFinitePresentation ((h ≫ g) ≫ sX) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := (h ≫ g) ≫ sX)).mpr inferInstance
  obtain ⟨hYcart, -⟩ :=
    Divisor.cartier_weil_dictionary_of_isSmoothVariety k ((h ≫ g) ≫ sX)
  have hhb := hh.isBirationalMorphism
  haveI : IsDominant h := hhb.isDominant
  haveI : IsProper h := hh.isProper
  haveI : IsDominant (h ≫ g) := hf.isBirationalMorphism.isDominant
  /- Step 2: an anti-ample exceptional divisor `D_F` and the ample `G = ν h^*a - D_F`. -/
  have hQ : MMP.Fourfold.IsQFactorial (g ≫ sX) :=
    ⟨hX'N, fun B => ⟨1, one_pos, hX'cart _⟩⟩
  obtain ⟨F, e₀, he₀, hF0, hFex, DF, hDFc, hDF, hDFamp⟩ :=
    exists_isRelativelyAmple_neg_smul_of_isExceptional (g ≫ sX) ((h ≫ g) ≫ sX) hQ hYN h ht
      hhp hhb
  have hBa : ∀ Z : irreducibleComponents Y, h (componentGenericPoint Y Z) ∉ a.supp :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' h a
  have hBe : ∀ Z : irreducibleComponents Y, h (componentGenericPoint Y Z) ∉ e.supp :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' h e
  have hec : e.IsCartier := hX'cart e
  obtain ⟨b, hb⟩ := hac.exists_isPullback hBa
  obtain ⟨be, hbe⟩ := hec.exists_isPullback hBe
  obtain ⟨ν, hν, hGc, hGamp⟩ :=
    exists_isAmple_add_nsmul hX'p hYp h ht hac hamp hb hDFc.neg hDFamp
  set G : Divisor Y := -DF + ν • b with hG
  set E'' : Divisor Y := ν • be + DF with hE''
  set N₁ : ℕ := ν * m with hN₁
  have hN₁pos : 0 < N₁ := Nat.mul_pos hν hm
  /- The pull-back `f^*D₀` and the degree identity `N₁ f^*D₀ ≡ G + E''`. -/
  have hBf : ∀ Z : irreducibleComponents Y, (h ≫ g) (componentGenericPoint Y Z) ∉ D₀.supp :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' (h ≫ g) D₀
  obtain ⟨fD, hfD⟩ := hD₀c.exists_isPullback hBf
  have hfDc : fD.IsCartier := hYcart fD
  have hkey : ∀ (C : Scheme.{0}) (i : C ⟶ Y) [IsProper (i ≫ (h ≫ g) ≫ sX)]
      (hdim : topologicalKrullDim C ≤ 1),
      G.degreeOn k ((h ≫ g) ≫ sX) i hdim hGc + E''.degreeOn k ((h ≫ g) ≫ sX) i hdim (hYcart _) =
        (N₁ : ℤ) * fD.degreeOn k ((h ≫ g) ≫ sX) i hdim hfDc := by
    intro C i _ hdim
    have hGE : G + E'' = ν • (b + be) := by rw [hG, hE'', smul_add]; abel
    rw [← Divisor.degreeOn_add, Divisor.degreeOn_congr hGE _ ((hYcart _).nsmul ν),
      Divisor.degreeOn_nsmul' k _ i hdim (b + be) (hYcart _) ν,
      Divisor.degreeOn_add k _ i hdim b be (hYcart _) (hYcart _),
      degreeOn_add_eq_mul_degreeOn_of_iso g rfl h ht hD₀c hD₁ (hX'cart D₁) hfD hfDc hac hec eae
        hb (hYcart b) hbe (hYcart be) i hdim, hN₁]
    push_cast
    ring
  /- The snc boundary `F` on `Y`. -/
  set SY : Closeds Y := exceptionalSet h ⊔ Δ''.supp.preimage h.continuous
  have hSYsnc : IsSNCSubset ((h ≫ g) ≫ sX) SY := ht ▸ hh.isSNCSubset
  obtain ⟨Fs, hFs, hFsnc⟩ := exists_finset_of_isSNCSubset hf.isSmoothScheme hSYsnc
  have hpre : ∀ y : Y, h y ∈ (Δ''.supp : Set T) → y ∈ (SY : Set Y) := fun y hy => Or.inr hy
  /- `E''` is effective with support in `F`. -/
  have hbe0 : 0 ≤ be := fun P => MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn hec
    (V := ⊤) (fun Q _ => he0 Q) hbe P
    ⟨P.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support P, trivial⟩
  have hDF0 : 0 ≤ DF := fun P => by
    have : (0 : ℚ) ≤ DF P := by
      rw [coeff_eq_mul_of_toQDivisor_eq_smul hDF P]; exact mul_nonneg (by positivity) (hF0 P)
    exact_mod_cast this
  have hE0 : 0 ≤ E'' := add_nonneg (nsmul_nonneg hbe0 ν) hDF0
  have hE''sub : ∀ P : MMP.Mori.PrimeDivisor Y, E'' P ≠ 0 → (P.support : Set Y) ⊆ SY := by
    intro P hP'
    have hE''P : E'' P = ν * be P + DF P := by rw [hE'']; simp
    by_cases hbP : be P = 0
    · have hDFP : DF P ≠ 0 := by rw [hE''P, hbP, mul_zero, zero_add] at hP'; exact hP'
      have hFP : F P ≠ 0 := fun h0 => hDFP (by
        have := coeff_eq_mul_of_toQDivisor_eq_smul hDF P
        rw [h0, mul_zero] at this
        exact_mod_cast this)
      intro x hx
      exact (le_sup_left : exceptionalSet h ≤ _)
        (MMP.Positivity.support_subset_exceptionalSet P (hFex P hFP) hx)
    · intro x hx
      refine (le_sup_right : _ ≤ exceptionalSet h ⊔ _) ?_
      have hx' := MMP.Flips.supp_subset_preimage_supp_of_isPullback hec hbe
        (DivisorWithCoeffs.support_subset_supp hbP hx)
      exact hΔ''2 hx'
  have hE''F : ∀ P, E'' P ≠ 0 → P ∈ Fs := fun P hP =>
    mem_of_support_subset_iUnion (by rw [hFs]; exact hE''sub P hP)
  /- The ideal `I 𝒪_Y = 𝒪_Y(-D_I)`. -/
  have hJcomp : I.comap (h ≫ g) = (I.comap g).comap h := Scheme.IdealSheafData.comap_comp _ _ _
  have hJcart : Stacks.Divisors.IsEffectiveCartierDivisor (I.comap (h ≫ g)) := by
    rw [hJcomp]; exact isEffectiveCartierDivisor_comap_of_surjective h _ hIcart
  have hJsupp : ((I.comap (h ≫ g)).support : Set Y) ⊆ SY := by
    intro y hy
    rw [hJcomp, Scheme.IdealSheafData.support_comap] at hy
    exact hpre y (hΔ''1 (hS₀2 hy))
  obtain ⟨DI, hDI0, hDIeq, hDIsupp⟩ := exists_divisor_eq_divisorIdeal ((h ≫ g) ≫ sX)
    hf.isSmoothScheme _ hJcart Fs (by rw [hFs]; exact hJsupp)
  /- The pull-back `f^*B`. -/
  have hBB : ∀ Z : irreducibleComponents Y, (h ≫ g) (componentGenericPoint Y Z) ∉ B.supp :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' (h ≫ g) B
  set fB := B.pullback hBq hBB
  have hfBp : B.IsPullback (h ≫ g) hBB fB := QDivisor.isPullback_pullback hBq hBB
  obtain ⟨D'', hD''q, hD''p⟩ := hfBp n₀ hn₀ D₀ hD₀z hD₀c
  have hD''eq : D'' = fD := hD''p.eq hD₀c hfD
  rw [hD''eq] at hD''q
  /- Step 3: the twist. -/
  obtain ⟨p, hp0, hQamp⟩ := exists_isAmple_sub_sum_single ((h ≫ g) ≫ sX) hGc hGamp hE0
    (hYcart E'') Fs hE''F hn₀ hfDc hD''q hN₁pos hkey
  /- The conclusion. -/
  refine ⟨Y, h ≫ g, hf, hYp, inferInstance, inferInstance, inferInstance, DI, hDI0, hYcart DI,
    hDIeq, Fs, hFsnc, ?_, hBB, fB, p, hfBp, hp0, hQamp⟩
  · intro y hy
    rw [hFs]
    rcases hy with (hy | hy) | hy
    · have h' : y ∈ exceptionalSet h ⊔ (exceptionalSet g).preimage h.continuous := by
        rw [← exceptionalSet_comp]; exact hy
      rcases h' with h1 | h1
      · exact Or.inl h1
      · exact hpre y (hΔ''1 (hS₀1 (Or.inl h1)))
    · refine hpre y (hΔ''1 (hS₀1 (Or.inr ?_)))
      change g (h y) ∈ ((QDivisor.toRDivisor Δ).supp : Set X)
      rw [QDivisor.supp_toRDivisor]
      exact hy
    · exact hJsupp (hDIsupp hy)

end MMP.Mori

end
