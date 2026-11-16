module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCentre
public import MMP.AlgebraicGeometry.Resolution.ExceptionalDivisorPrime
public import MMP.AlgebraicGeometry.MMP.Abundance.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.BlowUpIsProjective
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Integral
public import StacksFrontier.AlgebraicGeometry.Blowup.TwoStepTower
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Composition
public import StacksFrontier.AlgebraicGeometry.HProjective.AmpleBase
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.StalkPrimes
public import MMP.AlgebraicGeometry.Divisor.PullbackExistence

/-!
# Smooth blow-ups of smooth varieties: projectivity, birationality, exceptional divisor, fibres

Let `Y` be a smooth variety over a field `k`, `Z ⊆ Y` a smooth irreducible closed subscheme of
codimension `c ≥ 2` with ideal sheaf `I`, and `π : V = Bl_Z Y ⟶ Y` the blow-up. Then `V` is
smooth over `k`; `π` is projective, birational, and an isomorphism over `Y ∖ Z`; if `Y` carries
an ample invertible sheaf, `π` factors through a closed immersion into a fixed `ℙᴺ_Y`; if `Y` is
projective, so is `V`. The exceptional divisor `E = π⁻¹(Z)` is smooth over `k` and a prime
divisor, and the fibre of `E ⟶ Z` over `z ∈ Z` is `ℙ^{c-1}_{κ(z)}`.

## Main results

* `MMP.Threefold.Resolution.smooth_isProjective_isBirationalMorphism_blowUpToBase`: smoothness of
  `V`, projectivity, birationality, the isomorphism off `Z`, the closed immersion into `ℙᴺ_Y`
  over an ample base, and projectivity of `V` over a projective `Y`.
* `MMP.Threefold.Resolution.smooth_exceptionalDivisor_and_fiber_iso_projSpace`: `E` is smooth and
  prime, and every fibre of `E ⟶ Z` is `ℙ^{c-1}_{κ(z)}` with `c` the codimension of `Z`.
* `MMP.Threefold.Resolution.height_ker_stalkMap_subschemeι_eq_codimension`: for an integral
  closed subscheme `Z` of `Y` and `z ∈ Z`, the ideal of `Z` in `𝒪_{Y,z}` has height the
  codimension of `Z`.

## Implementation notes

* The centre is given by its ideal sheaf `I` with `MMP.Resolution.IsSmoothBlowup`; irreducibility
  and codimension refer to the closed set `Z = V(I)`. Integrality of `Y`, needed for birationality,
  is assumed only in the first main result; the second needs only smoothness.
* Projectivity is `AlgebraicGeometry.IsProjective` ([Stacks, Tag 01W8]: a closed immersion into
  `𝐏(ℰ)` with `ℰ` quasi-coherent of finite type, EGA's notion). The fixed projective space is
  `Stacks.HProjective.IsHProjective`; the ample invertible sheaf is `Stacks.Ample.IsAmple`.
* Birationality is `MMP.Mori.IsBirationalMorphism`.
* `ℙ^{c-1}_{κ(z)}` is `MMP.Intersection.ProjSpace κ(z) (ULift (Fin c))`, with `c` homogeneous
  coordinates, as a `κ(z)`-scheme; the fibre is a `κ(z)`-scheme through
  `Scheme.Hom.fiberToSpecResidueField`.

## References

* [J. Kollár, *Lectures on resolution of singularities*, Notation 3.19]
* [Stacks Project, Tags 02OS, 02NS, 0FUT, 087S, 0C4P]
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing

universe u

namespace MMP.Threefold.Resolution

/-- A morphism smooth at every point is smooth. -/
private theorem smooth_of_isSmoothScheme {X S : Scheme.{u}} {f : X ⟶ S}
    (h : MMP.Mori.IsSmoothScheme f) : Smooth f := by
  have : IsZariskiLocalAtSource @Smooth := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @Smooth)
    (fun U : {U : X.Opens // Smooth (U.ι ≫ f)} => U.1) ?_ fun U => U.2
  rw [← h, MMP.Mori.smoothLocus, sSup_eq_iSup']
  rfl

/-- **The codimension of an integral closed subscheme is its local codimension at each point.**
For a closed subscheme `Z = V(I)` of `Y` that is integral, and `z ∈ Z`, the kernel of
`𝒪_{Y,z} ⟶ 𝒪_{Z,z}` has height the codimension of `Z` in `Y`. -/
theorem height_ker_stalkMap_subschemeι_eq_codimension {X : Scheme.{u}} (I : X.IdealSheafData)
    [IsIntegral I.subscheme] (hirr : IsIrreducible (I.support : Set X)) (z : I.subscheme) :
    (RingHom.ker (I.subschemeι.stalkMap z).hom).height =
      codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds X) := by
  set ζ := I.subschemeι (genericPoint I.subscheme) with hζ
  have hcl := MMP.Resolution.closure_subschemeι_genericPoint I
  have hsp : ζ ⤳ I.subschemeι z := by
    rw [specializes_iff_mem_closure, hcl, ← I.range_subschemeι]; exact ⟨z, rfl⟩
  have heq : (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds X) =
      IrreducibleCloseds.closureSingleton ζ := by ext1; exact hcl.symm
  rw [heq, Stacks.Divisors.PrimeDivisor.codimension_closureSingleton]
  let := (X.presheaf.stalkSpecializes hsp).hom.toAlgebra
  have hloc := MMP.Intersection.isLocalization_stalkSpecializes hsp
  set Q := (maximalIdeal (X.presheaf.stalk ζ)).comap (X.presheaf.stalkSpecializes hsp).hom
    with hQdef
  have hJ := Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk I z
  have hprime : (IdealSheafData.stalk I (I.subschemeι z)).IsPrime := by
    rw [← hJ]; exact RingHom.ker_isPrime _
  have hmap : (IdealSheafData.stalk I (I.subschemeι z)).map
      (X.presheaf.stalkSpecializes hsp).hom = maximalIdeal (X.presheaf.stalk ζ) := by
    rw [← Stacks.Chow.idealStalk_eq_map_stalkSpecializes I hsp, hζ,
      IdealSheafData.stalk_subschemeι_genericPoint_eq_maximalIdeal]
  have hle : IdealSheafData.stalk I (I.subschemeι z) ≤ Q := by
    rw [hQdef, ← hmap]; exact Ideal.le_comap_map
  have hQ : Q = IdealSheafData.stalk I (I.subschemeι z) := by
    rw [hQdef, ← hmap]
    exact IsLocalization.under_map_of_isPrime_disjoint Q.primeCompl (X.presheaf.stalk ζ) hprime
      (Set.disjoint_left.mpr fun a ha hb => ha (hle hb))
  have hdim := IsLocalization.AtPrime.ringKrullDim_eq_height Q (X.presheaf.stalk ζ)
  rw [ringKrullDim_stalk_eq_coheight, hQ, ← hJ] at hdim
  exact_mod_cast hdim.symm

variable {k : Type u} [Field k] {Y : Scheme.{u}}

open MMP.Resolution in
/-- **Smooth blow-ups: smoothness, projectivity, birationality.** Let `Y` be an integral scheme
smooth over `k`, and `Z = V(I)` an irreducible closed subscheme smooth over `k` of codimension
`≥ 2`, with blow-up `π : V = Bl_Z Y ⟶ Y`. Then `V` is smooth over `k`, `π` is projective,
birational and an isomorphism over `Y ∖ Z`; if `Y` has an ample invertible sheaf, `π` is a closed
immersion into some `ℙᴺ_Y` followed by the projection; and if `Y` is projective over `k`, so is
`V`. -/
@[mmp "lem_mmp_threefold_smooth_blowup_geometry"]
theorem smooth_isProjective_isBirationalMorphism_blowUpToBase (sY : Y ⟶ Spec (.of k)) [IsIntegral Y]
    (I : Y.IdealSheafData) (h : IsSmoothBlowup sY I) (hirr : IsIrreducible (I.support : Set Y))
    (hc : 2 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y)) :
    Smooth (blowUpToBase I ≫ sY) ∧ IsProjective (blowUpToBase I) ∧
      MMP.Mori.IsBirationalMorphism (blowUpToBase I) ∧
      IsIso (blowUpToBase I ∣_ (⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩ : Y.Opens)) ∧
      ((∃ (M : Y.Modules) (_ : Stacks.Ample.IsInvertibleModule Y M), Stacks.Ample.IsAmple Y M) →
        Stacks.HProjective.IsHProjective (blowUpToBase I)) ∧
      (IsProjective sY → IsProjective (blowUpToBase I ≫ sY)) := by
  have : Smooth sY := smooth_of_isSmoothScheme h.1
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have hft := TwoStepTower.isFiniteType_of_isLocallyNoetherian I
  have : IsProper (blowUpToBase I) := TwoStepTower.isProper_blowUpToBase hft
  have hproj := Stacks.Blowup.isProjective_blowUpToBase I hft
  have hiso := isIso_blowUp_restrict_compl_support I
  -- the complement of the centre is nonempty
  have hne : (I.supportᶜ : Set Y).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at hne
    have h0 : codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y) = 0 :=
      Order.coheight_eq_zero.mpr fun b _ => fun x _ => by
        change x ∈ (I.support : Set Y); rw [hne]; trivial
    rw [h0] at hc
    exact absurd hc (by decide)
  have hIbot : I ≠ ⊥ := by
    rintro rfl
    obtain ⟨y, hy⟩ := hne
    exact hy (by simp)
  have : IsIntegral (blowUp I) := isIntegral_blowUp I hIbot
  refine ⟨(Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sY I h).1, hproj,
    ?_, hiso, ?_, hproj.comp⟩
  · set V : Y.Opens := ⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩
    obtain ⟨y, hy⟩ := hne
    obtain ⟨x, -⟩ := (asIso (blowUpToBase I ∣_ V)).hom.homeomorph.surjective ⟨y, hy⟩
    refine MMP.Flips.isBirationalMorphism_of_isIso_resLE (blowUpToBase I) (blowUpToBase I ⁻¹ᵁ V) V
      ⟨x.1, x.2⟩ ⟨y, hy⟩ le_rfl ?_
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    exact hiso
  · intro hamp
    obtain ⟨n, i, hi, -, hig⟩ :=
      Stacks.HProjective.isHQuasiProjective_of_isQuasiProjective_of_exists_isAmple
        (blowUpToBase I) hamp (Stacks.Blowup.isQuasiProjective_blowUpToBase I hft)
    have : IsProper (i ≫ (projectiveSpaceOver n Y ↘ Y)) := by rw [hig]; infer_instance
    have : IsProper i := IsProper.of_comp i (projectiveSpaceOver n Y ↘ Y)
    exact ⟨n, i, .of_isPreimmersion i i.isClosedMap.isClosed_range, hig⟩

open MMP.Resolution Stacks.AlgebraicGeometry in
/-- **Smooth blow-ups: the exceptional divisor and its fibres.** Let `Y` be smooth over `k`, and
`Z = V(I)` an irreducible closed subscheme smooth over `k` of codimension `c ≥ 2`, with blow-up
`π : V ⟶ Y` and exceptional divisor `E = π⁻¹(Z)`. Then `E` is smooth over `k` and is a prime
divisor of `V`, and for every `z ∈ Z` the fibre of `E ⟶ Z` over `z` is `ℙ^{c-1}_{κ(z)}` as a
`κ(z)`-scheme. -/
@[mmp "lem_mmp_threefold_smooth_blowup_geometry"]
theorem smooth_exceptionalDivisor_and_fiber_iso_projSpace (sY : Y ⟶ Spec (.of k))
    (I : Y.IdealSheafData) (h : IsSmoothBlowup sY I) (hirr : IsIrreducible (I.support : Set Y))
    (hc : 2 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y)) :
    Smooth ((exceptionalIdeal I).subschemeι ≫ blowUpToBase I ≫ sY) ∧
      (∃ F : AlgebraicGeometry.PrimeDivisor (blowUp I), F.idealSheaf = exceptionalIdeal I) ∧
      ∃ c : ℕ, (c : ℕ∞) =
          codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y) ∧
        ∀ z : I.subscheme,
          ∃ e : (exceptionalSubschemeMap I).fiber z ≅
              MMP.Intersection.ProjSpace (I.subscheme.residueField z) (ULift.{u} (Fin c)),
            e.hom ≫ MMP.Intersection.ProjSpace.toSpec (I.subscheme.residueField z) _ =
              (exceptionalSubschemeMap I).fiberToSpecResidueField z := by
  obtain ⟨-, hE, -, -, hfib⟩ :=
    Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sY I h
  have : IsIntegral I.subscheme := isIntegral_subscheme_of_isIrreducible sY I h.2 hirr
  have hc1 : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y) :=
    le_trans (by norm_num) hc
  refine ⟨hE, ⟨exceptionalPrimeDivisor sY I h hirr hc1, rfl⟩, ?_⟩
  obtain ⟨z₀⟩ : Nonempty I.subscheme := inferInstance
  obtain ⟨c₀, hc₀, -⟩ := hfib z₀
  refine ⟨c₀, ?_, fun z => ?_⟩
  · rw [hc₀, height_ker_stalkMap_subschemeι_eq_codimension I hirr z₀]
  · obtain ⟨c, hcz, e, he⟩ := hfib z
    have : c = c₀ := by
      have := hcz.trans ((height_ker_stalkMap_subschemeι_eq_codimension I hirr z).trans
        (height_ker_stalkMap_subschemeι_eq_codimension I hirr z₀).symm |>.trans hc₀.symm)
      exact_mod_cast this
    subst this
    exact ⟨e, he⟩

end MMP.Threefold.Resolution

end
