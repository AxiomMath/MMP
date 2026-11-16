/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCentre
public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportClopen
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Codimension
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorStalkResidueCokernel
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover

/-!
# The exceptional divisor of the blow-up of an irreducible smooth centre is a prime divisor

Let `X` be smooth over a field `k` and `Z ⊆ X` an irreducible closed subscheme, smooth over `k`,
of codimension `c ≥ 1`, with blow-up `π : B_Z X → X` and exceptional divisor `F = π⁻¹(Z)`. Then
`B_Z X` is smooth over `k`, and `F` is a prime divisor of `B_Z X`: an integral closed subscheme of
codimension one, cut out by the invertible ideal `π^*I_Z`; moreover `π(F) = Z`.

The proof: `F → Z` is a `ℙ^{c-1}`-bundle, and `c ≥ 1` at every point of `Z` since `I_Z` is
nonzero in the domain `𝒪_{X,z}` (it is nonzero at the generic point of `Z`, where `𝒪_{X,η}` has
dimension `codim Z ≥ 1`). So `F → Z` is surjective with connected fibres; it is closed, since
`B_Z X → X` is proper. As `Z` is connected, so is `F`, and a connected scheme smooth over a field
is integral. Finally an integral effective Cartier divisor of a locally noetherian scheme has
codimension one by Krull's principal ideal theorem.

## Main definitions

* `MMP.Resolution.exceptionalPrimeDivisor`: the exceptional divisor as a prime divisor.

## Main results

* `MMP.Resolution.isIntegral_exceptionalDivisor`: `F` is integral.
* `MMP.Resolution.isSmoothScheme_blowUp_and_exists_primeDivisor_exceptionalIdeal`: `B_Z X` is
  smooth, `F` is a prime divisor with invertible ideal sheaf, and `π(F) = Z`.

## Implementation notes

The centre is given by its ideal sheaf `I`; irreducibility and codimension refer to the closed
set `Z = V(I)`, the codimension being `codimension` of `Z` as an irreducible closed subset.

## References

* [J. Kollár, *Lectures on resolution of singularities*, Notation 3.19]
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing

universe u

namespace MMP.Resolution

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- A morphism smooth at every point is smooth. -/
private theorem smooth_of_isSmoothScheme {Y Z : Scheme.{u}} {f : Y ⟶ Z}
    (h : MMP.Mori.IsSmoothScheme f) :
    Smooth f := by
  have : IsZariskiLocalAtSource @Smooth := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @Smooth)
    (fun U : {U : Y.Opens // Smooth (U.ι ≫ f)} => U.1) ?_ fun U => U.2
  rw [← h, MMP.Mori.smoothLocus, sSup_eq_iSup']
  rfl

/-- A smooth morphism is smooth at every point. -/
theorem isSmoothScheme_of_smooth {Y Z : Scheme.{u}} (f : Y ⟶ Z) [Smooth f] :
    MMP.Mori.IsSmoothScheme f :=
  (MMP.Mori.isSmoothScheme_iff f).2 inferInstance

/-- An irreducible closed subscheme smooth over a field is integral. -/
theorem isIntegral_subscheme_of_isIrreducible (sX : X ⟶ Spec (.of k)) (I : X.IdealSheafData)
    (hI : MMP.Mori.IsSmoothScheme (I.subschemeι ≫ sX)) (hirr : IsIrreducible (I.support : Set X)) :
    IsIntegral I.subscheme := by
  have := smooth_of_isSmoothScheme hI
  have hc : _root_.IsConnected (I.subschemeι.base ⁻¹' (I.support : Set X)) :=
    hirr.isConnected.preimage_of_isClosedMap I.subschemeι.isClosedEmbedding.injective
      I.subschemeι.isClosedEmbedding.isClosedMap (by rw [I.range_subschemeι])
  have : ConnectedSpace I.subscheme := by
    rw [connectedSpace_iff_univ]
    convert hc
    ext z
    simp only [Set.mem_univ, Set.mem_preimage, true_iff]
    rw [← I.range_subschemeι]
    exact ⟨z, rfl⟩
  exact Stacks.Chow.isIntegral_of_connectedSpace_of_smooth (I.subschemeι ≫ sX)

/-- The generic point of an integral closed subscheme `Z = V(I)`, as a point of `X`, has closure
`Z`. -/
theorem closure_subschemeι_genericPoint (I : X.IdealSheafData) [IsIntegral I.subscheme] :
    closure {I.subschemeι (genericPoint I.subscheme)} = (I.support : Set X) := by
  rw [← Set.image_singleton,
    I.subschemeι.isClosedEmbedding.isClosedMap.closure_image_eq_of_continuous
      I.subschemeι.continuous,
    genericPoint_closure, Set.image_univ, I.range_subschemeι]

/-- If `Z = V(I)` is an irreducible closed subset of codimension `≥ 1` whose subscheme is
integral, then `I` is nonzero at every point of `Z`. -/
theorem stalk_ne_bot_of_one_le_codimension (I : X.IdealSheafData) [IsIntegral I.subscheme]
    (hirr : IsIrreducible (I.support : Set X))
    (hcodim : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds X))
    {x : X} (hx : x ∈ (I.support : Set X)) : IdealSheafData.stalk I x ≠ ⊥ := by
  set ζ := I.subschemeι (genericPoint I.subscheme) with hζdef
  have hcl := closure_subschemeι_genericPoint I
  have hsp : ζ ⤳ x := by
    rwa [specializes_iff_mem_closure, hcl]
  have heq : (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds X) =
      IrreducibleCloseds.closureSingleton ζ := by
    ext1
    exact hcl.symm
  rw [heq, Stacks.Divisors.PrimeDivisor.codimension_closureSingleton] at hcodim
  have hdim : (1 : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk ζ) := by
    rw [ringKrullDim_stalk_eq_coheight]
    exact_mod_cast hcodim
  have hm : maximalIdeal (X.presheaf.stalk ζ) ≠ ⊥ := by
    intro hm
    have hfield : IsField (X.presheaf.stalk ζ) :=
      (IsLocalRing.isField_iff_maximalIdeal_eq).mpr hm
    rw [ringKrullDim_eq_zero_of_isField hfield] at hdim
    exact absurd hdim (by decide)
  intro hbot
  apply hm
  rw [← IdealSheafData.stalk_subschemeι_genericPoint_eq_maximalIdeal,
    Stacks.Chow.idealStalk_eq_map_stalkSpecializes I hsp, hbot, Ideal.map_bot]

open Stacks.AlgebraicGeometry (exceptionalSubschemeMap)

/-- The map `F → Z` of the exceptional divisor to the centre is a closed map: `F → X` is the
composite of a closed immersion with the proper blow-up morphism. -/
theorem isClosedMap_exceptionalSubschemeMap (I : X.IdealSheafData) [IsLocallyNoetherian X] :
    IsClosedMap (exceptionalSubschemeMap I) := by
  intro C hC
  have hcomp : ((exceptionalSubschemeMap I ≫ I.subschemeι) : _ → _) =
      ((exceptionalIdeal I).subschemeι ≫ blowUpToBase I : _ ⟶ _) := by
    rw [Scheme.IdealSheafData.subschemeMap_subschemeι]
  have hcl : IsClosed (((exceptionalIdeal I).subschemeι ≫ blowUpToBase I : _ ⟶ _) '' C) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp]
    exact (blowUpToBase I).isClosedMap _
      ((exceptionalIdeal I).subschemeι.isClosedEmbedding.isClosedMap _ hC)
  rw [← hcomp, Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp] at hcl
  have := hcl.preimage I.subschemeι.continuous
  rwa [Set.preimage_image_eq _ I.subschemeι.isClosedEmbedding.injective] at this

/-- Projective space `ℙⁿ_K` is connected. -/
theorem connectedSpace_projSpace (K : Type u) [Field K] (n : ℕ) :
    ConnectedSpace (MMP.Intersection.ProjSpace K (ULift.{u} (Fin (n + 1)))) := by
  have : ConnectedSpace
      (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading K n)) :=
    inferInstance
  set e := Stacks.AlgebraicGeometry.ProjPoly.projIsoULiftIndex K n
  exact e.inv.homeomorph.surjective.connectedSpace e.inv.homeomorph.continuous

/-- For a smooth blow-up along an irreducible centre `Z` of codimension `≥ 1`, every fibre of
`F → Z` is (nonempty and) connected: it is `ℙ^{c-1}` with `c ≥ 1`. -/
theorem isConnected_preimage_exceptionalSubschemeMap (sX : X ⟶ Spec (.of k))
    (I : X.IdealSheafData) (h : IsSmoothBlowup sX I) (hirr : IsIrreducible (I.support : Set X))
    (hcodim : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds X))
    (z : I.subscheme) : _root_.IsConnected ((exceptionalSubschemeMap I) ⁻¹' {z}) := by
  have := isIntegral_subscheme_of_isIrreducible sX I h.2 hirr
  have := smooth_of_isSmoothScheme h.1
  obtain ⟨-, -, -, -, hfib⟩ :=
    Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sX I h
  obtain ⟨c, hc, e, -⟩ := hfib z
  have hne : IdealSheafData.stalk I (I.subschemeι z) ≠ ⊥ :=
    stalk_ne_bot_of_one_le_codimension I hirr hcodim (I.range_subschemeι ▸ ⟨z, rfl⟩)
  have := isRegularLocalRing_stalk_of_smooth_over_field sX (I.subschemeι z)
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk (I.subschemeι z))
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hne
    rw [← Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk]
    exact Ideal.height_eq_zero_iff_eq_bot.mp (by rw [← hc]; rfl)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hc0
  have := connectedSpace_projSpace (I.subscheme.residueField z) n
  have : ConnectedSpace ((exceptionalSubschemeMap I).fiber z) :=
    e.inv.homeomorph.surjective.connectedSpace e.inv.homeomorph.continuous
  rw [← Scheme.Hom.range_fiberι]
  exact isConnected_range (Scheme.Hom.continuous _)

/-- For a smooth blow-up along an irreducible centre `Z` of codimension `≥ 1`, the map `F → Z`
is surjective. -/
theorem surjective_exceptionalSubschemeMap (sX : X ⟶ Spec (.of k))
    (I : X.IdealSheafData) (h : IsSmoothBlowup sX I) (hirr : IsIrreducible (I.support : Set X))
    (hcodim : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds X)) :
    Function.Surjective (exceptionalSubschemeMap I) := fun z =>
  (isConnected_preimage_exceptionalSubschemeMap sX I h hirr hcodim z).nonempty

/-- **The exceptional divisor is integral.** For a smooth blow-up along an irreducible centre of
codimension `≥ 1`, the exceptional divisor `F` is connected (`F → Z` is a closed surjection with
connected fibres onto the connected `Z`) and smooth over `k`, hence integral. -/
theorem isIntegral_exceptionalDivisor (sX : X ⟶ Spec (.of k))
    (I : X.IdealSheafData) (h : IsSmoothBlowup sX I) (hirr : IsIrreducible (I.support : Set X))
    (hcodim : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds X)) :
    IsIntegral (exceptionalDivisor I) := by
  have := smooth_of_isSmoothScheme h.1
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have := isIntegral_subscheme_of_isIrreducible sX I h.2 hirr
  have hq : Topology.IsQuotientMap (exceptionalSubschemeMap I) :=
    (isClosedMap_exceptionalSubschemeMap I).isQuotientMap (Scheme.Hom.continuous _)
      (surjective_exceptionalSubschemeMap sX I h hirr hcodim)
  have hconn := hq.isCoinducing.isConnected_preimage_of_isClosed
    (isConnected_preimage_exceptionalSubschemeMap sX I h hirr hcodim) isClosed_univ
    (IrreducibleSpace.isIrreducible_univ I.subscheme).isConnected
  have : ConnectedSpace (exceptionalDivisor I) := by
    rw [connectedSpace_iff_univ]
    simpa using hconn
  obtain ⟨-, h2, -⟩ := Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sX I h
  exact Stacks.Chow.isIntegral_of_connectedSpace_of_smooth
    ((exceptionalIdeal I).subschemeι ≫ blowUpToBase I ≫ sX)

/-- A scheme smooth over a field is locally noetherian. -/
theorem isLocallyNoetherian_of_smooth {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k)) [Smooth f] :
    IsLocallyNoetherian Y :=
  LocallyOfFiniteType.isLocallyNoetherian f

/-- **The exceptional divisor as a prime divisor.** For a smooth blow-up `π : B_Z X → X` along an
irreducible centre `Z` of codimension `≥ 1`, the exceptional divisor `F = π⁻¹(Z)` is an integral
closed subscheme of codimension one of `B_Z X`. -/
def exceptionalPrimeDivisor (sX : X ⟶ Spec (.of k))
    (I : X.IdealSheafData) (h : IsSmoothBlowup sX I) (hirr : IsIrreducible (I.support : Set X))
    (hcodim : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds X)) :
    AlgebraicGeometry.PrimeDivisor (blowUp I) where
  idealSheaf := exceptionalIdeal I
  integral := isIntegral_exceptionalDivisor sX I h hirr hcodim
  codimension_one := by
    have := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sX I h).1
    have : IsLocallyNoetherian (blowUp I) := isLocallyNoetherian_of_smooth (blowUpToBase I ≫ sX)
    have := isIntegral_exceptionalDivisor sX I h hirr hcodim
    rw [Stacks.Divisors.PrimeDivisor.codimension_closureSingleton]
    have := ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor (exceptionalIdeal I)
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal I)
      (genericPoint (exceptionalDivisor I))
      ⟨⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩,
        (genericPoint_spec (exceptionalDivisor I))⟩
    rw [ringKrullDim_stalk_eq_coheight] at this
    exact_mod_cast this

/-- The ideal sheaf of `exceptionalPrimeDivisor sX I h hirr hcodim` is the exceptional ideal
`exceptionalIdeal I`. -/
@[simp]
theorem exceptionalPrimeDivisor_idealSheaf (sX : X ⟶ Spec (.of k))
    (I : X.IdealSheafData) (h : IsSmoothBlowup sX I) (hirr : IsIrreducible (I.support : Set X))
    (hcodim : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds X)) :
    (exceptionalPrimeDivisor sX I h hirr hcodim).idealSheaf = exceptionalIdeal I :=
  rfl

/-- **Kollár, Notation 3.19: the exceptional divisor of the blow-up of an irreducible smooth
centre is a prime divisor.** Let `X` be smooth over `k` and `Z = V(I) ⊆ X` an irreducible closed
subscheme, smooth over `k`, of codimension `≥ 1`, with blow-up `π : B_Z X → X` and exceptional
divisor `F = π⁻¹(Z)`. Then `B_Z X` is smooth over `k`, `F` is a prime divisor of `B_Z X` (an
integral closed subscheme of codimension one) whose ideal sheaf `π^*I` is invertible (an effective
Cartier divisor), and `π(F) = Z`. -/
@[mmp "lem_kr3c_exceptional_divisor_prime"]
theorem isSmoothScheme_blowUp_and_exists_primeDivisor_exceptionalIdeal (sX : X ⟶ Spec (.of k))
    (I : X.IdealSheafData) (h : IsSmoothBlowup sX I) (hirr : IsIrreducible (I.support : Set X))
    (hcodim : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds X)) :
    MMP.Mori.IsSmoothScheme (blowUpToBase I ≫ sX) ∧
      ∃ F : AlgebraicGeometry.PrimeDivisor (blowUp I), F.idealSheaf = exceptionalIdeal I ∧
        Stacks.Divisors.IsEffectiveCartierDivisor F.idealSheaf ∧
        blowUpToBase I '' F.support = (I.support : Set X) := by
  have := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sX I h).1
  refine ⟨isSmoothScheme_of_smooth _,
    exceptionalPrimeDivisor sX I h hirr hcodim, rfl,
    Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal I, ?_⟩
  change blowUpToBase I '' ((exceptionalIdeal I).support : Set (blowUp I)) = _
  rw [← (exceptionalIdeal I).range_subschemeι, ← Set.range_comp, ← TopCat.coe_comp,
    ← Scheme.Hom.comp_base, ← Scheme.IdealSheafData.subschemeMap_subschemeι (exceptionalIdeal I) I
      (blowUpToBase I) (I.le_map_comap (blowUpToBase I)),
    Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    (surjective_exceptionalSubschemeMap sX I h hirr hcodim).range_eq, Set.image_univ,
    I.range_subschemeι]

end MMP.Resolution
