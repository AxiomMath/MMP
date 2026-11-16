module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.Principalization
public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.Functor
public import MMP.AlgebraicGeometry.Resolution.Basic
public import MMP.AlgebraicGeometry.Resolution.Blowup.VarietyProjective
public import MMP.AlgebraicGeometry.Morphisms.Smooth.SmoothFlagCoordinates
import MMP.AlgebraicGeometry.Morphisms.ValuativeCentre
import MMP.AlgebraicGeometry.Resolution.OrderReduction.MonomialStepTermination
import MMP.AlgebraicGeometry.Resolution.BlowupSequence.EntryIndex
import MMP.AlgebraicGeometry.Resolution.BlowupSequence.Restriction
import MMP.AlgebraicGeometry.Resolution.BlowupSequence.FlatPullback
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Resolution.Blowup
import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
import MMP.AlgebraicGeometry.Resolution.BlowupSequence.PushforwardSmooth
import MMP.AlgebraicGeometry.Resolution.Surface.SemilocalRing
import MMP.AlgebraicGeometry.Intersection.CartierRestriction
import MMP.AlgebraicGeometry.MMP.Abundance.Basic

/-!
# Principalization: the restriction of a blow-up sequence to a component

Let `P` be a scheme over a field `k` and `𝐁 = (P_i, Z_i)_{i ≤ r}` a blow-up sequence starting
with `P`, with composites `Π_i : P_i ⟶ P`. For a closed subvariety `C ⊆ P` with generic point
`η`, the *entry index* `j = j_𝐁(η)` is the first step whose centre meets the fibre over `η`, and
the restriction `𝐁|_C` is the sequence of blow-ups `C_{i+1} = B_{C_i ∩ Z_i} C_i`, with
`Π^C_i : C_i ⟶ C`.

Before the entry index each `C_i` is a variety whose generic point lies over `η`, and
`Π^C_i` is projective and birational (Kollár, Warning 3.23). When `P` is smooth, `𝐁` is a
smooth blow-up sequence principalizing the ideal `I` of a closed `X ⊆ P` with all centres over
`X`, and `C` is an irreducible component of `X` of codimension at least two, then `j < r` and
`C_j` is a connected component of the smooth centre `Z_j`; hence `Π^C_j : C_j ⟶ C` is a
resolution of `C` (Kollár, p. 137). Finally a closed subscheme `Z` of a smooth `k`-scheme, smooth
at a point of codimension `c`, is near that point the pullback of the origin of `𝔸^c_k` along a
smooth `k`-morphism (Kollár, p. 139).

## Main results

* `MMP.Resolution.ClosedBlowupSequence.isVariety_restrict_truncate_of_le_entryIndex`: before the
  entry index, `C_i` is a variety over `η` and `Π^C_i` is projective and birational.
* `MMP.Resolution.ClosedBlowupSequence.restrict_truncate_entryIndex_isConnectedComponent`:
  `j < r`, and `C_j` is a connected component of `Z_j`.
* `MMP.Resolution.ClosedBlowupSequence.isResolutionOfVariety_toBase_restrict_truncate_entryIndex`:
  `Π^C_j` is a resolution of `C`.
* `MMP.Resolution.Kollar.exists_smooth_comap_ker_origin_eq`: a smooth pair is locally the
  pullback of the origin of `𝔸^c`.

## Implementation notes

The first `i` steps of `𝐁` are `ClosedBlowupSequence.truncate`, so `C_i` is the target of
`(𝐁.truncate i).restrict C`, the embedding `C_i ⟶ P_i` is `restrictHom`, and `Π_i`, `Π^C_i` are
the respective `toBase`. The component `C` is the reduced subscheme
`vanishingIdeal (closure {η})` with `closure {η}` maximal among irreducible subsets of the
support of `I`, and codimension at least two is a strict chain `closure {η} ⊂ Y₁ ⊂ Y₂` of
irreducible closed subsets. "`C_j` is a connected component of `Z_j`" is stated for subschemes:
the image of `C_j` is a connected component of the support of `Z_j`, and on an open `U ⊇ C_j`
the ideals of `C_j` and `Z_j` agree.

For the resolution statement `P` is asked separated and quasi-projective over `k`, as in the
source's setting of quasi-projective varieties. Without separatedness and quasi-compactness `C`
need not be a variety: a line with infinitely many doubled points is irreducible and smooth but
neither separated nor quasi-compact. Quasi-projectivity is needed for the projectivity of
`Π^C_j` in the sense of a closed immersion into `ℙⁿ_C`: over a proper normal surface `Y` with
`Pic Y = 0` and a smooth point `p`, the blow-up `Bl_p Y ⟶ Y` is projective in the sense of EGA
but admits no closed immersion into any `ℙⁿ_Y`, since `H⁰(Y, 𝔪_p^m) = 0` for `m > 0`. Over a
quasi-projective base the two notions agree (Stacks, Tags 01WA, 0B45).

The affine space `𝔸^c_k` is indexed by `ULift (Fin c)` to keep the statement universe
polymorphic; the origin is the section `AffineSpace.homOfVector (𝟙 _) 0`, and `𝔪₀` its kernel.

## References

* [Kollár, *Lectures on resolution of singularities*, Warning 3.23, pp. 137, 139][kollar2007]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace MMP.Resolution.ClosedBlowupSequence

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### The restriction before the entry index -/

/-- The case of the empty blow-up sequence. -/
private theorem pullback_nil {k : Type u} [Field k] {X S : Scheme.{u}} (j : S ⟶ X)
    (s : S ⟶ Spec (.of k)) (hs : IsVariety k s) :
    IsVariety k ((nil S).toBase ≫ s) ∧
      (∀ ξ : (nil S).target, IsGenericPoint ξ Set.univ →
        ∀ ξ₀ : S, IsGenericPoint ξ₀ Set.univ → (nil X).toBase ((nil X).pullbackHom j ξ) = j ξ₀) ∧
      IsBirational (nil S).toBase := by
  refine ⟨?_, fun ξ hξ ξ₀ hξ₀ => ?_, Stacks.Chow.isBirational_id S⟩
  · change IsVariety k (𝟙 S ≫ s)
    rwa [Category.id_comp]
  · change j ξ = j ξ₀
    rw [hξ.eq hξ₀]

/-- The inductive statement: the pull-back of `𝐁.truncate i` along a closed immersion `j` of a
variety `S` whose generic point lies in `T`, for `i ≤ j_𝐁(T)`. -/
private theorem pullback_truncate_of_le_entryIndexOfSet {k : Type u} [Field k] {X : Scheme.{u}}
    (B : ClosedBlowupSequence X) :
    ∀ {S : Scheme.{u}} (j : S ⟶ X) (s : S ⟶ Spec (.of k)), IsClosedImmersion j →
      IsVariety k s → ∀ (T : Set X) (i : ℕ), i ≤ B.entryIndexOfSet T →
      (∀ ξ : S, IsGenericPoint ξ Set.univ → j ξ ∈ T) →
      IsVariety k (((B.truncate i).pullback j).toBase ≫ s) ∧
        (∀ ξ : ((B.truncate i).pullback j).target, IsGenericPoint ξ Set.univ →
          ∀ ξ₀ : S, IsGenericPoint ξ₀ Set.univ →
            (B.truncate i).toBase ((B.truncate i).pullbackHom j ξ) = j ξ₀) ∧
        IsBirational ((B.truncate i).pullback j).toBase := by
  induction B with
  | nil X =>
    intro S j s _ hs T i _ _
    exact pullback_nil j s hs
  | @cons X Z B ih =>
    intro S j s hj hs T i hi hT
    cases i with
    | zero => exact pullback_nil j s hs
    | succ i =>
      have hZT : ¬ ((Z.support : Set X) ∩ T).Nonempty := by
        intro h
        simp only [entryIndexOfSet, h, ite_true] at hi
        omega
      have hi' : i ≤ B.entryIndexOfSet (blowUpToBase Z ⁻¹' T) := by
        simp only [entryIndexOfSet, hZT, ite_false] at hi
        omega
      have : IsIntegral S := hs.toIsIntegral
      have hne : Z.comap j ≠ ⊥ := by
        intro h
        have h' := congrArg Scheme.IdealSheafData.support h
        rw [Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_bot] at h'
        have hmem : genericPoint S ∈ (⊤ : TopologicalSpace.Closeds S) := trivial
        rw [← h'] at hmem
        exact hZT ⟨_, hmem, hT _ (genericPoint_spec S)⟩
      obtain ⟨hv, -, hbir⟩ :=
        MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational s
          (Z.comap j) hne
      have : IsIntegral (blowUp (Z.comap j)) := hv.toIsIntegral
      have hsq : ∀ v, blowUpToBase Z (canonicalLift j Z v) =
          j (blowUpToBase (Z.comap j) v) := fun v => by
        rw [← Scheme.Hom.comp_apply, canonicalLift_comp_blowUpToBase, Scheme.Hom.comp_apply]
      obtain ⟨h1, h2, h3⟩ := ih (canonicalLift j Z) (blowUpToBase (Z.comap j) ≫ s)
        (Bridges.isClosedImmersion_canonicalLift j Z) hv (blowUpToBase Z ⁻¹' T) i hi'
        (fun ξ hξ => by
          change blowUpToBase Z (canonicalLift j Z ξ) ∈ T
          rw [hsq, hξ.eq (genericPoint_spec _), IsBirational.genericPoint_eq _ hbir]
          exact hT _ (genericPoint_spec S))
      refine ⟨?_, fun ξ hξ ξ₀ hξ₀ => ?_, h3.comp hbir⟩
      · change IsVariety k ((((B.truncate i).pullback (canonicalLift j Z)).toBase ≫
          blowUpToBase (Z.comap j)) ≫ s)
        rwa [Category.assoc]
      · change ((B.truncate i).toBase ≫ blowUpToBase Z)
          ((B.truncate i).pullbackHom (canonicalLift j Z) ξ) = j ξ₀
        rw [Scheme.Hom.comp_apply, h2 ξ hξ _ (genericPoint_spec _), hsq,
          IsBirational.genericPoint_eq _ hbir, (genericPoint_spec S).eq hξ₀]

/-- **The restriction of a blow-up sequence before the entry index** (Kollár, Warning 3.23).
Let `𝐁` be a blow-up sequence starting with a scheme `P` of finite type over a field `k`, let
`C ⊆ P` be a closed subvariety with generic point `η`, and let `i ≤ 𝐁.entryIndex η`. Then
`C_i`, the last scheme of `(𝐁.truncate i).restrict C`, is a variety over `k`, every generic point
of `C_i` is sent by `C_i ⟶ P_i ⟶ P` to `η`, and `Π^C_i : C_i ⟶ C` is projective and
birational. -/
@[mmp "lem_kr3f_restriction_integral_before_entry"]
public theorem isVariety_restrict_truncate_of_le_entryIndex {k : Type u} [Field k]
    {P : Scheme.{u}} (sP : P ⟶ Spec (.of k)) [LocallyOfFiniteType sP] [QuasiCompact sP]
    (B : ClosedBlowupSequence P) (C : P.IdealSheafData)
    (hC : IsVariety k (C.subschemeι ≫ sP)) {η : P}
    (hη : IsGenericPoint η (C.support : Set P)) {i : ℕ} (hi : i ≤ B.entryIndex η) :
    IsVariety k (((B.truncate i).restrict C).toBase ≫ C.subschemeι ≫ sP) ∧
      (∀ ξ : ((B.truncate i).restrict C).target, IsGenericPoint ξ Set.univ →
        (B.truncate i).toBase ((B.truncate i).restrictHom C ξ) = η) ∧
      IsProjective ((B.truncate i).restrict C).toBase ∧
      IsBirational ((B.truncate i).restrict C).toBase := by
  have : IsIntegral C.subscheme := hC.toIsIntegral
  have hgen : ∀ ξ : C.subscheme, IsGenericPoint ξ Set.univ → C.subschemeι ξ = η := by
    intro ξ hξ
    refine IsGenericPoint.eq ?_ hη
    have h := C.subschemeι.isClosedEmbedding.isClosedMap.closure_image_eq_of_continuous
      C.subschemeι.continuous {ξ}
    rwa [Set.image_singleton, hξ.def, Set.image_univ, Scheme.IdealSheafData.range_subschemeι] at h
  obtain ⟨h1, h2, h3⟩ := pullback_truncate_of_le_entryIndexOfSet B C.subschemeι
    (C.subschemeι ≫ sP) inferInstance hC {η} i hi hgen
  have : IsLocallyNoetherian C.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (C.subschemeι ≫ sP)
  have : CompactSpace C.subscheme := QuasiCompact.compactSpace_of_compactSpace (C.subschemeι ≫ sP)
  have : IsNoetherian C.subscheme := {}
  refine ⟨h1, fun ξ hξ => ?_, isProjective_toBase _, h3⟩
  rw [← hgen _ (genericPoint_spec C.subscheme)]
  exact h2 ξ hξ _ (genericPoint_spec C.subscheme)

/-! ### The first centre through the generic point of a component -/

/-- A blow-up sequence splits at the entry index `j` of a set `S`, when `j` is less than its
length: the centre `Z_j` meets the fibre over `S`, it is smooth when the sequence is, and it lies
over `S₀` when every centre does. -/
private theorem exists_split_at_entryIndexOfSet {k : Type u} [Field k] :
    ∀ {X X₀ : Scheme.{u}} (B : ClosedBlowupSequence X) (S : Set X) (s : X ⟶ Spec (.of k))
      (f : X ⟶ X₀) (S₀ : Set X₀) (j : ℕ), j = B.entryIndexOfSet S → j < B.length →
      ∃ (Z : (B.truncate j).target.IdealSheafData) (B' : ClosedBlowupSequence (blowUp Z)),
        B = (B.truncate j).append (.cons Z B') ∧
        ((Z.support : Set _) ∩ (B.truncate j).toBase ⁻¹' S).Nonempty ∧
        (B.IsSmooth s → MMP.Mori.IsSmoothScheme ((B.truncate j).toBase ≫ s) ∧
          MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ (B.truncate j).toBase ≫ s)) ∧
        (B.CentersLieOver f S₀ → ((B.truncate j).toBase ≫ f) '' (Z.support : Set _) ⊆ S₀)
  | _, _, .nil _, _, _, _, _, j, _, h => by simp [ClosedBlowupSequence.length] at h
  | _, _, .cons Z B, S, s, f, S₀, j, hj, hlen => by
    by_cases hS : ((Z.support : Set _) ∩ S).Nonempty
    · have hj0 : j = 0 := by simpa [ClosedBlowupSequence.entryIndexOfSet, hS] using hj
      subst hj0
      refine ⟨Z, B, rfl, hS, fun hB => ?_, fun hc => ?_⟩
      · change MMP.Mori.IsSmoothScheme (𝟙 _ ≫ s) ∧
          MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ 𝟙 _ ≫ s)
        simpa using ⟨hB.1, hB.2.1⟩
      · change (𝟙 _ ≫ f) '' (Z.support : Set _) ⊆ S₀
        simpa [Set.image_subset_iff] using hc.1
    · have hj' : j = B.entryIndexOfSet (blowUpToBase Z ⁻¹' S) + 1 := by
        simpa [ClosedBlowupSequence.entryIndexOfSet, hS] using hj
      subst hj'
      obtain ⟨Z', B', hB, hne, hsm, hlie⟩ := exists_split_at_entryIndexOfSet B
        (blowUpToBase Z ⁻¹' S) (blowUpToBase Z ≫ s) (blowUpToBase Z ≫ f) S₀ _ rfl (by
          simpa [ClosedBlowupSequence.length] using hlen)
      let T := B.truncate (B.entryIndexOfSet (blowUpToBase Z ⁻¹' S))
      refine ⟨Z', B', ?_, ?_, fun h => ?_, fun h => ?_⟩
      · change ClosedBlowupSequence.cons Z B = .cons Z (T.append (.cons Z' B'))
        rw [← hB]
      · change ((Z'.support : Set _) ∩ (T.toBase ≫ blowUpToBase Z) ⁻¹' S).Nonempty
        simpa [Scheme.Hom.comp_base, Set.preimage_comp] using hne
      · change MMP.Mori.IsSmoothScheme ((T.toBase ≫ blowUpToBase Z) ≫ s) ∧
          MMP.Mori.IsSmoothScheme (Z'.subschemeι ≫ (T.toBase ≫ blowUpToBase Z) ≫ s)
        simpa only [Category.assoc] using hsm h.2.2
      · change ((T.toBase ≫ blowUpToBase Z) ≫ f) '' (Z'.support : Set _) ⊆ S₀
        simpa only [Category.assoc] using hlie h.2

/-- At the entry index, the fiber of `Π_j` over `η` is one point, and it lies on `Z_j`. -/
private theorem existsUnique_fiber_point {P : Scheme.{u}} (B : ClosedBlowupSequence P) (η : P)
    (Z : (B.truncate (B.entryIndex η)).target.IdealSheafData)
    (hne : ((Z.support : Set _) ∩ (B.truncate (B.entryIndex η)).toBase ⁻¹' {η}).Nonempty) :
    ∃ ηj, (B.truncate (B.entryIndex η)).toBase ηj = η ∧ ηj ∈ (Z.support : Set _) ∧
      ∀ y, (B.truncate (B.entryIndex η)).toBase y = η → y = ηj := by
  obtain ⟨ηj, hZ, hη⟩ := hne
  refine ⟨ηj, hη, hZ, fun y hy => ?_⟩
  obtain ⟨V, hηV, hiso⟩ :=
    Kollar.exists_isIso_truncate_toBase_restrict_of_le_entryIndex B η _ le_rfl
  set p := (B.truncate (B.entryIndex η)).toBase
  have hinj : Function.Injective (p ∣_ V) :=
    ((TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (asIso (p ∣_ V)))).injective)
  have hyV : y ∈ p ⁻¹ᵁ V := by simpa [Scheme.Hom.mem_preimage, hy] using hηV
  have hη' : p ηj = η := hη
  have hηjV : ηj ∈ p ⁻¹ᵁ V := by simpa [Scheme.Hom.mem_preimage, hη'] using hηV
  exact congrArg Subtype.val (@hinj ⟨y, hyV⟩ ⟨ηj, hηjV⟩ (Subtype.ext (by
    rw [morphismRestrict_base]
    exact hy.trans hη'.symm)))

/-- The generic point of `B_{h⁻¹Z}Y` lies over the generic point of an integral `Y`, when the
generic point of `Y` lies off `h⁻¹Z`. -/
private theorem isGenericPoint_blowUpToBase {X Y : Scheme.{u}} [IsIntegral Y] (h : Y ⟶ X)
    (Z : X.IdealSheafData) (hZ : h (genericPoint Y) ∉ (Z.support : Set X))
    {ξ : blowUp (Z.comap h)} (hξ : IsGenericPoint ξ Set.univ) :
    IsGenericPoint (blowUpToBase (Z.comap h) ξ) Set.univ := by
  have hξ0 : genericPoint Y ∉ ((Z.comap h).support : Set Y) := by simpa using hZ
  obtain ⟨v, hv⟩ := exists_blowUpToBase_eq_of_notMem_support (Z.comap h) hξ0
  have hsp : blowUpToBase (Z.comap h) ξ ⤳ genericPoint Y :=
    hv ▸ (hξ.specializes (Set.mem_univ v)).map (blowUpToBase (Z.comap h)).continuous
  exact isGenericPoint_iff_specializes.mpr fun y =>
    ⟨fun _ => Set.mem_univ y, fun _ => hsp.trans ((genericPoint_spec Y).specializes trivial)⟩

/-- Pulling back the first `i ≤ j_𝐁(S)` blow-ups along a morphism `h : Y ⟶ X` from an integral
scheme whose generic point lies over `S` gives an integral scheme whose generic points lie over
`S`. -/
private theorem isIntegral_pullback_truncate_of_le_entryIndexOfSet :
    ∀ {X Y : Scheme.{u}} (B : ClosedBlowupSequence X) (h : Y ⟶ X) [IsIntegral Y] (S : Set X)
      (i : ℕ), (∀ ξ : Y, IsGenericPoint ξ Set.univ → h ξ ∈ S) → i ≤ B.entryIndexOfSet S →
      IsIntegral ((B.truncate i).pullback h).target ∧
        ∀ ξ : ((B.truncate i).pullback h).target, IsGenericPoint ξ Set.univ →
          (B.truncate i).toBase ((B.truncate i).pullbackHom h ξ) ∈ S
  | _, _, .nil _, h, inst, S, i, hS, _ => ⟨inst, fun ξ hξ => hS ξ hξ⟩
  | _, _, .cons Z B, h, inst, S, 0, hS, _ => ⟨inst, fun ξ hξ => hS ξ hξ⟩
  | _, Y, .cons Z B, h, inst, S, i + 1, hS, hle => by
    have hZS : ¬ ((Z.support : Set _) ∩ S).Nonempty := by
      intro hne
      simp [ClosedBlowupSequence.entryIndexOfSet, hne] at hle
    have hle' : i ≤ B.entryIndexOfSet (blowUpToBase Z ⁻¹' S) := by
      simpa [ClosedBlowupSequence.entryIndexOfSet, hZS] using hle
    have hgen : h (genericPoint Y) ∉ (Z.support : Set _) := fun hm =>
      hZS ⟨_, hm, hS _ (genericPoint_spec Y)⟩
    have hne : Z.comap h ≠ ⊥ := by
      intro hbot
      have : genericPoint Y ∈ ((Z.comap h).support : Set Y) := by
        rw [hbot, Scheme.IdealSheafData.support_bot]
        trivial
      exact hgen (by simpa using this)
    have : IsIntegral (blowUp (Z.comap h)) := isIntegral_blowUp (Z.comap h) hne
    obtain ⟨hint, hpt⟩ := isIntegral_pullback_truncate_of_le_entryIndexOfSet B
      (canonicalLift h Z) (blowUpToBase Z ⁻¹' S) i (fun ξ hξ => by
        change blowUpToBase Z (canonicalLift h Z ξ) ∈ S
        rw [← Scheme.Hom.comp_apply, canonicalLift_comp_blowUpToBase, Scheme.Hom.comp_apply]
        exact hS _ (isGenericPoint_blowUpToBase h Z hgen hξ)) hle'
    refine ⟨hint, fun ξ hξ => ?_⟩
    have := hpt ξ hξ
    change ((B.truncate i).toBase ≫ blowUpToBase Z)
      ((B.truncate i).pullbackHom (canonicalLift h Z) ξ) ∈ S
    rwa [Scheme.Hom.comp_apply]

/-- `C_j` is integral with generic point the point `η_j` of the fibre of `Π_j` over `η`, so the
closed subscheme `C_j ⊆ P_j` is the closure of `η_j` with its reduced structure. -/
private theorem range_and_ker_restrictHom {P : Scheme.{u}} (B : ClosedBlowupSequence P) (η : P)
    (ηj : (B.truncate (B.entryIndex η)).target)
    (huniq : ∀ y, (B.truncate (B.entryIndex η)).toBase y = η → y = ηj) :
    Set.range ((B.truncate (B.entryIndex η)).restrictHom
      (Scheme.IdealSheafData.vanishingIdeal ⟨closure {η}, isClosed_closure⟩)) = closure {ηj} ∧
    ((B.truncate (B.entryIndex η)).restrictHom
      (Scheme.IdealSheafData.vanishingIdeal ⟨closure {η}, isClosed_closure⟩)).ker =
      Scheme.IdealSheafData.vanishingIdeal ⟨closure {ηj}, isClosed_closure⟩ := by
  set C := Scheme.IdealSheafData.vanishingIdeal (X := P) ⟨closure {η}, isClosed_closure⟩
  have : IsIntegral C.subscheme :=
    StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _
      isIrreducible_singleton.closure
  have hrangeC : Set.range C.subschemeι = closure {η} := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hS : ∀ ξ : C.subscheme, IsGenericPoint ξ Set.univ → C.subschemeι ξ ∈ ({η} : Set P) := by
    intro ξ hξ
    have h1 : closure {C.subschemeι ξ} = closure {η} := by
      rw [← hrangeC, ← Set.image_singleton,
        C.subschemeι.isClosedEmbedding.closure_image_eq, hξ.def, Set.image_univ]
    exact (IsGenericPoint.eq (h1 ▸ isGenericPoint_closure) isGenericPoint_closure)
  obtain ⟨hint, hpt⟩ := isIntegral_pullback_truncate_of_le_entryIndexOfSet B C.subschemeι {η}
    (B.entryIndex η) hS le_rfl
  have : IsIntegral ((B.truncate (B.entryIndex η)).restrict C).target := hint
  set ι := (B.truncate (B.entryIndex η)).restrictHom C
  have : IsClosedImmersion ι := Kollar.isClosedImmersion_restrictHom_truncate B C (B.entryIndex η)
  set ξ := genericPoint ((B.truncate (B.entryIndex η)).restrict C).target
  have hξ : IsGenericPoint ξ Set.univ := genericPoint_spec _
  have hιξ : ι ξ = ηj := huniq _ (hpt ξ hξ)
  have hrange : Set.range ι = closure {ηj} := by
    rw [← Set.image_univ, ← hξ.def, ← hιξ, ← Set.image_singleton]
    exact (ι.isClosedEmbedding.closure_image_eq {ξ}).symm
  refine ⟨hrange, ?_⟩
  rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range ι, hrange]
  congr 1
  exact Closeds.ext (by rw [Closeds.coe_closure, closure_closure]; rfl)

/-- In a locally noetherian normal scheme every connected component is irreducible and open: the
scheme is a disjoint union of integral schemes (Stacks, Tag 033N). -/
private theorem isIrreducible_and_isOpen_connectedComponent_of_isNormal {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] (x : X) :
    IsIrreducible (connectedComponent x) ∧ IsOpen (connectedComponent x) := by
  obtain ⟨ι, Y, -, hI, ⟨e⟩⟩ :=
    (isNormal_iff_exists_iso_coproduct_integral_normal X).1 inferInstance
  let h : X ≃ₜ (Σ i, Y i) := e.hom.homeomorph.trans (sigmaMk Y).symm
  set p := h x
  set P : Set X := h ⁻¹' Set.range (@Sigma.mk ι (fun i => Y i) p.1) with hP
  have hPc : IsClopen P := isClopen_range_sigmaMk.preimage h.continuous
  have hPirr : IsIrreducible P := by
    have := hI p.1
    have hR : IsIrreducible (Set.range (@Sigma.mk ι (fun i => Y i) p.1)) := by
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ _).image _ continuous_sigmaMk.continuousOn
    rw [hP, ← Homeomorph.image_symm]
    exact hR.image _ h.symm.continuous.continuousOn
  have hxP : x ∈ P := ⟨p.2, rfl⟩
  have hS : connectedComponent x = P := subset_antisymm (hPc.connectedComponent_subset hxP)
    (hPirr.isPreirreducible.isPreconnected.subset_connectedComponent hxP)
  exact ⟨hS ▸ hPirr, hS ▸ hPc.isOpen⟩

/-- The connected components of the support of a smooth closed subscheme are irreducible and open
in the support. -/
private theorem isIrreducible_connectedComponentIn_support_of_isSmoothScheme {k : Type u} [Field k]
    {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) (Z : Y.IdealSheafData)
    (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ s)) {x : Y} (hx : x ∈ (Z.support : Set Y)) :
    IsIrreducible (connectedComponentIn (Z.support : Set Y) x) ∧
      ∃ W : Y.Opens, (W : Set Y) ∩ Z.support = connectedComponentIn (Z.support : Set Y) x := by
  have : Smooth (Z.subschemeι ≫ s) := MMP.Mori.IsSmoothScheme.smooth hZ
  have : IsLocallyNoetherian Z.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (Z.subschemeι ≫ s)
  have : IsNormal Z.subscheme := isNormal_of_smooth_over_field (Z.subschemeι ≫ s)
  have hrange : Set.range Z.subschemeι = (Z.support : Set Y) := by
    rw [Scheme.IdealSheafData.range_subschemeι]
  obtain ⟨z, rfl⟩ : x ∈ Set.range Z.subschemeι := hrange ▸ hx
  have hemb := Z.subschemeι.isClosedEmbedding.isEmbedding
  have heq : connectedComponentIn (Z.support : Set Y) (Z.subschemeι z) =
      Z.subschemeι '' connectedComponent z := by
    rw [← connectedComponentIn_univ, MMP.Mori.image_connectedComponentIn_of_isEmbedding hemb
      (Set.mem_univ z), Set.image_univ, hrange]
  obtain ⟨hirr, hopen⟩ := isIrreducible_and_isOpen_connectedComponent_of_isNormal z
  refine ⟨heq ▸ hirr.image _ Z.subschemeι.continuous.continuousOn, ?_⟩
  obtain ⟨t, ht, hts⟩ := hemb.isInducing.isOpen_iff.mp hopen
  refine ⟨⟨t, ht⟩, ?_⟩
  change t ∩ (Z.support : Set Y) = _
  rw [heq, ← hts, Set.image_preimage_eq_inter_range, hrange]

/-- The inverse image of a reduced closed subscheme along an open immersion is the reduced closed
subscheme on the inverse image of its support. -/
private theorem comap_eq_vanishingIdeal_of_isOpenImmersion {X Y : Scheme.{u}}
    (J : Y.IdealSheafData) [IsReduced J.subscheme] (f : X ⟶ Y) [IsOpenImmersion f] :
    J.comap f = Scheme.IdealSheafData.vanishingIdeal (J.support.preimage f.continuous) := by
  have : IsReduced (Limits.pullback f J.subschemeι) :=
    isReduced_of_isOpenImmersion (Limits.pullback.snd f J.subschemeι)
  rw [Scheme.IdealSheafData.comap, Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
  congr 1
  refine Closeds.ext ?_
  rw [Closeds.coe_closure, Scheme.Pullback.range_fst, Scheme.IdealSheafData.range_subschemeι]
  exact (J.support.preimage f.continuous).isClosed.closure_eq

/-- A reduced closed subscheme is determined on an open `U` by its support. -/
private theorem comap_eq_comap_vanishingIdeal_of_isReduced {Y : Scheme.{u}}
    (Z : Y.IdealSheafData) [IsReduced Z.subscheme] (U : Y.Opens) (F : Closeds Y)
    (hF : (U : Set Y) ∩ Z.support = (U : Set Y) ∩ F) :
    Z.comap U.ι = (Scheme.IdealSheafData.vanishingIdeal F).comap U.ι := by
  rw [comap_eq_vanishingIdeal_of_isOpenImmersion, comap_eq_vanishingIdeal_of_isOpenImmersion]
  congr 1
  refine Closeds.ext (Set.ext fun x => ?_)
  have hx : U.ι x ∈ (U : Set Y) := by
    rw [← Scheme.Opens.range_ι U]
    exact ⟨x, rfl⟩
  change U.ι x ∈ (Z.support : Set Y) ↔ U.ι x ∈
    ((Scheme.IdealSheafData.vanishingIdeal F).support : Set Y)
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have h := Set.ext_iff.mp hF (U.ι x)
  exact ⟨fun h' => (h.mp ⟨hx, h'⟩).2, fun h' => (h.mpr ⟨hx, h'⟩).2⟩

/-- The connected component of the smooth centre `Z_j` through `η_j` is the closure of `η_j`: its
generic point `ζ` maps into `X` and `Π_j ζ` specializes to `η`, so `Π_j ζ = η` by maximality of
`closure {η}`, hence `ζ = η_j`. Near it, `Z_j` (reduced) is the vanishing ideal of this
closure. -/
private theorem connectedComponentIn_eq_closure {k : Type u} [Field k] {P : Scheme.{u}}
    (sP : P ⟶ Spec (.of k)) (I : P.IdealSheafData) {η : P}
    (hη : Maximal (fun s : Set P => IsIrreducible s ∧ s ⊆ (I.support : Set P)) (closure {η}))
    (T : ClosedBlowupSequence P) (Z : T.target.IdealSheafData)
    (hsm : MMP.Mori.IsSmoothScheme (T.toBase ≫ sP) ∧
      MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ T.toBase ≫ sP))
    (hlie : (T.toBase ≫ 𝟙 P) '' (Z.support : Set _) ⊆ (I.support : Set P))
    (ηj : T.target) (hηj : T.toBase ηj = η) (hηjZ : ηj ∈ (Z.support : Set _))
    (huniq : ∀ y, T.toBase y = η → y = ηj) :
    connectedComponentIn (Z.support : Set _) ηj = closure {ηj} ∧
      ∃ U : T.target.Opens, closure {ηj} ⊆ (U : Set _) ∧
        Z.comap U.ι = (Scheme.IdealSheafData.vanishingIdeal
          ⟨closure {ηj}, isClosed_closure⟩).comap U.ι := by
  obtain ⟨hirr, W, hW⟩ :=
    isIrreducible_connectedComponentIn_support_of_isSmoothScheme _ Z hsm.2 hηjZ
  set K := connectedComponentIn (Z.support : Set _) ηj
  have hKZ : K ⊆ Z.support := connectedComponentIn_subset _ _
  have hηjK : ηj ∈ K := mem_connectedComponentIn hηjZ
  set ζ := hirr.genericPoint
  have hζ : IsGenericPoint ζ (closure K) := hirr.isGenericPoint_genericPoint_closure
  have hζZ : ζ ∈ (Z.support : Set _) :=
    closure_minimal hKZ Z.support.isClosed hζ.mem
  have hsp : ζ ⤳ ηj := hζ.specializes (subset_closure hηjK)
  have hpζ : T.toBase ζ = η := by
    have hI : T.toBase ζ ∈ (I.support : Set P) := hlie ⟨ζ, hζZ, rfl⟩
    have hle : closure {η} ⊆ closure {T.toBase ζ} := by
      rw [← hηj]
      exact specializes_iff_closure_subset.mp (hsp.map T.toBase.continuous)
    have hsub : closure {T.toBase ζ} ⊆ (I.support : Set P) :=
      closure_minimal (Set.singleton_subset_iff.mpr hI) I.support.isClosed
    have := hη.2 ⟨isIrreducible_singleton.closure, hsub⟩ hle
    exact (inseparable_iff_closure_eq.mpr (subset_antisymm this hle)).eq
  have hζη : ζ = ηj := huniq ζ hpζ
  have hKeq : K = closure {ηj} := by
    apply subset_antisymm
    · rw [← hζη, hζ.def]
      exact subset_closure
    · exact isIrreducible_singleton.closure.isConnected.isPreconnected
        |>.subset_connectedComponentIn (subset_closure rfl)
          (closure_minimal (Set.singleton_subset_iff.mpr hηjZ) Z.support.isClosed)
  refine ⟨hKeq, W, ?_, ?_⟩
  · rw [← hKeq, ← hW]
    exact Set.inter_subset_left
  · have : Smooth (T.toBase ≫ sP) := MMP.Mori.IsSmoothScheme.smooth hsm.1
    have : IsReduced Z.subscheme :=
      MMP.Resolution.Aux.isReduced_subscheme_of_isSmoothScheme (T.toBase ≫ sP) Z hsm.2
    apply comap_eq_comap_vanishingIdeal_of_isReduced Z
    change (W : Set _) ∩ (Z.support : Set _) = (W : Set _) ∩ closure {ηj}
    rw [hW, ← hKeq, Set.inter_eq_right.mpr (hW ▸ Set.inter_subset_left)]

/-- **Kollár, p. 137.** Let `P` be smooth over a field, `I` the ideal of a closed subscheme
`X ⊆ P`, `η` the generic point of an irreducible component `C` of `X` of codimension
`≥ 2`, and `B` a smooth blow-up sequence of `P` with `Π^*I` locally principal and all centers
mapping into `X`. Then `j = B.entryIndex η < B.length`, and the restriction `C_j` of `B` to `C`
at step `j` is a connected component of the `j`-th center `Z_j`. -/
@[mmp "lem_kr3f_first_center_through_generic_point"]
public theorem restrict_truncate_entryIndex_isConnectedComponent {k : Type u} [Field k]
    {P : Scheme.{u}} (sP : P ⟶ Spec (.of k)) (hP : MMP.Mori.IsSmoothScheme sP)
    (I : P.IdealSheafData) {η : P}
    (hη : Maximal (fun s : Set P => IsIrreducible s ∧ s ⊆ (I.support : Set P)) (closure {η}))
    (hcodim : ∃ Y₁ Y₂ : IrreducibleCloseds P,
      closure {η} ⊂ (Y₁ : Set P) ∧ (Y₁ : Set P) ⊂ Y₂)
    (B : ClosedBlowupSequence P) (hB : B.IsSmooth sP)
    (hprinc : Stacks.Divisors.IsLocallyPrincipal (I.comap B.toBase))
    (hcent : B.CentersLieOver (𝟙 P) (I.support : Set P)) :
    B.entryIndex η < B.length ∧
      ∃ (Z : (B.truncate (B.entryIndex η)).target.IdealSheafData)
        (B' : ClosedBlowupSequence (blowUp Z)),
        B = (B.truncate (B.entryIndex η)).append (cons Z B') ∧
        let C : P.IdealSheafData :=
          Scheme.IdealSheafData.vanishingIdeal ⟨closure {η}, isClosed_closure⟩
        let ι := (B.truncate (B.entryIndex η)).restrictHom C
        (∃ x, Set.range ι = connectedComponentIn (Z.support : Set _) x) ∧
        ∃ U : (B.truncate (B.entryIndex η)).target.Opens, Set.range ι ⊆ U ∧
          ι.ker.comap U.ι = Z.comap U.ι := by
  have hj := ClosedBlowupSequence.entryIndex_lt_length_of_isLocallyPrincipal sP hP I hη hcodim B
    hprinc
  obtain ⟨Z, B', hsplit, hne, hsm, hlie⟩ :=
    exists_split_at_entryIndexOfSet B {η} sP (𝟙 P) (I.support : Set P) (B.entryIndex η) rfl hj
  obtain ⟨ηj, hηj, hηjZ, huniq⟩ := existsUnique_fiber_point B η Z hne
  obtain ⟨hcc, U, hU, hZU⟩ := connectedComponentIn_eq_closure sP I hη _ Z (hsm hB) (hlie hcent)
    ηj hηj hηjZ huniq
  obtain ⟨hrange, hker⟩ := range_and_ker_restrictHom B η ηj huniq
  refine ⟨hj, Z, B', hsplit, ⟨ηj, hrange.trans hcc.symm⟩, U, hrange ▸ hU, ?_⟩
  simp only [hker, hZU]

/-! ### The restricted sequence resolves the component -/

/-- If the concatenation `D.append C` of blow-up sequences is smooth over `k`, so is `C`, over
the composite `D.toBase ≫ s`. -/
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

/-- If the closed immersion `T.restrictHom C` has ideal agreeing, on an open `U` containing its
image, with the ideal of a centre `Z` smooth over `T.toBase ≫ t`, then the restricted composite
is smooth over `t`. -/
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
    (MMP.Resolution.Kollar.pullbackHom_toBase_comm _ _).symm
  rw [← Category.assoc, hc, ← Scheme.Hom.toImage_imageι (T.restrictHom C)]
  simp only [Category.assoc]
  infer_instance

/-- **Kollár, p. 137.** Let `P` be smooth, separated and quasi-projective over a field, `I` the
ideal of a closed subscheme `X ⊆ P`, `η` the generic point of an irreducible component `C`
of `X` of codimension `≥ 2`, and `B` a smooth blow-up sequence of `P` with `Π^*I` locally principal
and all centers mapping into `X`. Then the composite `C_j ⟶ C` of the restriction to `C` of `B`
truncated at `j = B.entryIndex η` is a resolution of the variety `C`. -/
@[mmp "lem_kr3f_restricted_component_resolution"]
public theorem isResolutionOfVariety_toBase_restrict_truncate_entryIndex {k : Type u} [Field k]
    {P : Scheme.{u}} (sP : P ⟶ Spec (.of k)) (hP : MMP.Mori.IsSmoothScheme sP)
    [IsSeparated sP] (hPqp : IsQuasiProjective sP)
    (I : P.IdealSheafData) {η : P}
    (hη : Maximal (fun s : Set P => IsIrreducible s ∧ s ⊆ (I.support : Set P)) (closure {η}))
    (hcodim : ∃ Y₁ Y₂ : IrreducibleCloseds P,
      closure {η} ⊂ (Y₁ : Set P) ∧ (Y₁ : Set P) ⊂ Y₂)
    (B : ClosedBlowupSequence P) (hB : B.IsSmooth sP)
    (hprinc : Stacks.Divisors.IsLocallyPrincipal (I.comap B.toBase))
    (hcent : B.CentersLieOver (𝟙 P) (I.support : Set P)) :
    let C : P.IdealSheafData :=
      Scheme.IdealSheafData.vanishingIdeal ⟨closure {η}, isClosed_closure⟩
    IsResolutionOfVariety (C.subschemeι ≫ sP)
      ((B.truncate (B.entryIndex η)).restrict C).toBase := by
  intro C
  have hsP : Smooth sP := MMP.Mori.IsSmoothScheme.smooth hP
  have : QuasiCompact sP := hPqp.1.2
  have : IsIntegral C.subscheme :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure η
  have hCvar : IsVariety k (C.subschemeι ≫ sP) := by constructor <;> infer_instance
  have hηC : IsGenericPoint η (C.support : Set P) := by
    simp [C, IsGenericPoint]
  obtain ⟨hvar, -, hproj, hbir⟩ :=
    isVariety_restrict_truncate_of_le_entryIndex sP B C hCvar hηC le_rfl
  obtain ⟨-, Z, B', hBeq, -, U, hιU, hker⟩ :=
    restrict_truncate_entryIndex_isConnectedComponent sP hP I hη hcodim B hB hprinc hcent
  refine ⟨hCvar, hvar, hproj, ?_, ?_⟩
  · have := hvar.toIsIntegral
    have : LocallyOfFiniteType ((B.truncate (B.entryIndex η)).restrict C).toBase :=
      locallyOfFiniteType_of_comp _ (C.subschemeι ≫ sP)
    have : Finite (irreducibleComponents
        ((B.truncate (B.entryIndex η)).restrict C).target) := by
      rw [irreducibleComponents_eq_singleton]
      infer_instance
    have : Finite (irreducibleComponents C.subscheme) := by
      rw [irreducibleComponents_eq_singleton]
      infer_instance
    obtain ⟨V₁, V₂, hV, hV₁, hV₂, hiso⟩ :=
      exists_dense_opens_isIso_resLE_of_isBirational _ hbir
        (Or.inl ⟨inferInstance, inferInstance⟩)
    exact MMP.Flips.isBirationalMorphism_of_isIso_resLE _ V₁ V₂ hV₁.nonempty hV₂.nonempty hV hiso
  · have hB' : ((B.truncate (B.entryIndex η)).append (cons Z B')).IsSmooth sP := hBeq ▸ hB
    have := MMP.Resolution.Kollar.isClosedImmersion_restrictHom_truncate B C (B.entryIndex η)
    exact MMP.Mori.isSmoothScheme_of_smooth (smooth_restrict_toBase_comp sP _ C Z U hιU hker
      (MMP.Mori.IsSmoothScheme.smooth (isSmooth_of_isSmooth_append sP _ _ hB').2.1))

end MMP.Resolution.ClosedBlowupSequence

/-! ### Smooth pairs are locally pulled back from the origin -/

namespace MMP.Resolution.Kollar

open MvPolynomial

/-- The inclusion `R[m] → R[T ⊕ m]` of a polynomial ring into one with finitely many extra
variables is smooth. -/
private theorem smooth_rename_inr (R : Type u) [CommRing R] (T m : Type u) [Finite T] :
    (rename (R := R) (Sum.inr : m → T ⊕ m)).toRingHom.Smooth := by
  let A := MvPolynomial m R
  let e := sumAlgEquiv R T m
  have h : (rename (R := R) (Sum.inr : m → T ⊕ m)).toRingHom =
      e.symm.toRingEquiv.toRingHom.comp (algebraMap A (MvPolynomial T A)) := by
    refine RingHom.ext fun q ↦ ?_
    have h2 := DFunLike.congr_fun
      (congrArg AlgHom.toRingHom (sumAlgEquiv_comp_rename_inr (R := R) (S₁ := T) (S₂ := m))) q
    change e (rename Sum.inr q) = C q at h2
    change rename Sum.inr q = e.symm (C q)
    rw [← h2, AlgEquiv.symm_apply_apply]
  rw [h]
  have : Algebra.Smooth A (MvPolynomial T A) := ⟨inferInstance, inferInstance⟩
  exact RingHom.Smooth.comp (RingHom.smooth_algebraMap.mpr this)
    (RingHom.Smooth.of_bijective e.symm.bijective)

/-- Renaming the variables of `R[m]` along an injection into a finite type is a smooth ring map. -/
private theorem smooth_rename {R : Type u} [CommRing R] {m n : Type u} [Finite n] (i : m → n)
    (hi : Function.Injective i) : (rename (R := R) i).toRingHom.Smooth := by
  classical
  let E : n ≃ (↥(Set.range i)ᶜ) ⊕ m :=
    ((Equiv.sumCompl (· ∈ Set.range i)).symm.trans (Equiv.sumComm _ _)).trans
      (Equiv.sumCongr (Equiv.refl _) (Equiv.ofInjective i hi).symm)
  have hE : ∀ j, E.symm (Sum.inr j) = i j := fun j => by simp [E, Equiv.ofInjective]
  have : (rename (R := R) i).toRingHom =
      (renameEquiv R E.symm).toRingEquiv.toRingHom.comp (rename (R := R) Sum.inr).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun q ↦ ?_)
    · change rename i (C r) = renameEquiv R E.symm (rename Sum.inr (C r))
      simp
    · change rename i (X q) = renameEquiv R E.symm (rename Sum.inr (X q))
      simp [hE]
  rw [this]
  exact RingHom.Smooth.comp (smooth_rename_inr R _ m)
    (RingHom.Smooth.of_bijective (renameEquiv R E.symm).bijective)

/-- Over an affine base, the global sections of `𝔸(n; S)` are the polynomials in the
coordinates. -/
private theorem bijective_eval₂Hom_coord (n : Type u) (S : Scheme.{u}) [IsAffine S] :
    Function.Bijective
      (eval₂Hom ((𝔸(n; S) ↘ S).appTop).hom (AffineSpace.coord (n := n) S)) := by
  have : IsIso (AffineSpace.isoOfIsAffine n S).hom.appTop :=
    inferInstanceAs (IsIso ((AffineSpace.isoOfIsAffine n S).hom.app ⊤))
  have h1 := ConcreteCategory.bijective_of_isIso (AffineSpace.isoOfIsAffine n S).hom.appTop
  have h2 := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso
    (CommRingCat.of (MvPolynomial n Γ(S, ⊤)))).inv
  have := h1.comp h2
  rw [AffineSpace.isoOfIsAffine_hom_appTop] at this
  convert this using 1
  ext q
  simp only [Function.comp_apply, CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

/-- The coordinate projection `𝔸(n; S) ⟶ 𝔸(m; S)` along an injection `m → n`, `n` finite, is
smooth over an affine base. -/
private theorem smooth_reindex {m n : Type u} [Finite n] (i : m → n) (hi : Function.Injective i)
    (S : Scheme.{u}) [IsAffine S] : Smooth (AffineSpace.reindex i S) := by
  suffices H : Smooth (AffineSpace.reindex i S ≫ (AffineSpace.isoOfIsAffine m S).hom) by
    have : Smooth ((AffineSpace.reindex i S ≫ (AffineSpace.isoOfIsAffine m S).hom) ≫
      (AffineSpace.isoOfIsAffine m S).inv) := inferInstance
    simpa using this
  rw [HasRingHomProperty.iff_of_isAffine (P := @Smooth), Scheme.Hom.comp_appTop,
    AffineSpace.isoOfIsAffine_hom_appTop]
  have heq : ((AffineSpace.reindex i S).appTop.hom).comp
      (eval₂Hom ((𝔸(m; S) ↘ S).appTop).hom (AffineSpace.coord S)) =
      (eval₂Hom ((𝔸(n; S) ↘ S).appTop).hom (AffineSpace.coord S)).comp
        (rename (R := Γ(S, ⊤)) i).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun j ↦ ?_)
    · simp only [RingHom.comp_apply, eval₂Hom_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        rename_C]
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, AffineSpace.reindex_over]
    · simp
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  rw [← RingHom.comp_assoc, heq]
  exact RingHom.Smooth.comp (RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso _))
    (RingHom.Smooth.comp (smooth_rename i hi)
      (RingHom.Smooth.of_bijective (bijective_eval₂Hom_coord n S)))

/-- The functions on `𝔸(n; S)` vanishing on the zero section of an affine base `S` form the
ideal generated by the coordinates. -/
private theorem ker_appTop_homOfVector_zero (n : Type u) (S : Scheme.{u}) [IsAffine S] :
    RingHom.ker (AffineSpace.homOfVector (n := n) (𝟙 S) 0).appTop.hom =
      Ideal.span (Set.range (AffineSpace.coord S)) := by
  set φ := eval₂Hom ((𝔸(n; S) ↘ S).appTop).hom (AffineSpace.coord (n := n) S)
  have hφ := bijective_eval₂Hom_coord n S
  have hcomp : (AffineSpace.homOfVector (n := n) (𝟙 S) 0).appTop.hom.comp φ =
      eval₂Hom (RingHom.id _) 0 := by
    refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun j ↦ ?_)
    · simp only [RingHom.comp_apply, φ, eval₂Hom_C, RingHom.id_apply]
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, AffineSpace.homOfVector_over]
      rfl
    · simp [φ]
  have hker : RingHom.ker (eval₂Hom (RingHom.id Γ(S, ⊤)) (0 : n → Γ(S, ⊤))) =
      Ideal.span (Set.range X) := by
    ext p
    rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image, RingHom.mem_ker]
    have h0 : eval₂Hom (RingHom.id Γ(S, ⊤)) (0 : n → Γ(S, ⊤)) p = p.coeff 0 := by
      rw [← MvPolynomial.constantCoeff_eq, ← MvPolynomial.eval_zero]; rfl
    rw [h0]
    refine ⟨fun hp m hm => ?_, fun h => ?_⟩
    · have hm0 : m ≠ 0 := by
        rintro rfl
        exact (MvPolynomial.mem_support_iff.mp hm) hp
      obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hm0
      exact ⟨i, Set.mem_univ _, hi⟩
    · by_contra hp
      obtain ⟨i, -, hi⟩ := h 0 (MvPolynomial.mem_support_iff.mpr hp)
      exact hi rfl
  have hX : (⇑φ ∘ X) = AffineSpace.coord S := funext fun j => by simp [φ]
  rw [← Ideal.map_comap_of_surjective φ hφ.2
    (RingHom.ker (AffineSpace.homOfVector (n := n) (𝟙 S) 0).appTop.hom), RingHom.comap_ker, hcomp,
    hker, Ideal.map_span, ← Set.range_comp, hX]

open IsLocalRing in
/-- At a point `z` of a closed subscheme `Z` of a smooth `k`-scheme `P` with `𝒪_{Z,z}` regular,
`dim 𝒪_{P,z} = dim 𝒪_{Z,z} + c` when `Z` has codimension `c` in `P` at `z`. -/
private theorem ringKrullDim_stalk_eq_add_of_isRegularLocalRing {k : Type u} [Field k]
    {P : Scheme.{u}} (f : P ⟶ Spec (.of k)) [Smooth f] (Z : P.IdealSheafData) (z : Z.subscheme)
    [IsRegularLocalRing (Z.subscheme.presheaf.stalk z)] {c : ℕ}
    (hc : topologicalKrullDimAt P (Z.subschemeι z) = topologicalKrullDimAt Z.subscheme z + c) :
    ringKrullDim (P.presheaf.stalk (Z.subschemeι z)) =
      ringKrullDim (Z.subscheme.presheaf.stalk z) + c := by
  set i := Z.subschemeι
  have hX := topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k P f (i z)
  have hD := topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k Z.subscheme (i ≫ f) z
  have htr := trdeg_residueField_of_surjectiveOnStalks k f i z
  have hfin := residueField_finTrdeg k f (i z)
  have h1 := isRegularLocalRing_stalk_of_smooth_over_field f (i z)
  have d1 := IsRegularLocalRing.spanFinrank_maximalIdeal (R := P.presheaf.stalk (i z))
  have d2 := IsRegularLocalRing.spanFinrank_maximalIdeal (R := Z.subscheme.presheaf.stalk z)
  rw [← d1, ← d2]
  letI : Algebra k (P.residueField (i z)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ P.Γevaluation (i z)).hom.toAlgebra
  have hlt : Cardinal.toENat (Algebra.trdeg k (P.residueField (i z))) < ⊤ := by
    rw [Cardinal.toENat_lt_top]
    exact trdeg_lt_aleph0 k _
  rw [hX, hD, htr] at hc
  rw [htr] at hlt
  obtain ⟨t, ht⟩ := ENat.ne_top_iff_exists.mp hlt.ne
  rw [← ht, ← d1, ← d2] at hc
  have h3 : t + Submodule.spanFinrank (maximalIdeal (P.presheaf.stalk (i z))) =
      t + Submodule.spanFinrank (maximalIdeal (Z.subscheme.presheaf.stalk z)) + c := by
    exact_mod_cast hc
  exact_mod_cast (by omega : Submodule.spanFinrank (maximalIdeal (P.presheaf.stalk (i z))) =
    Submodule.spanFinrank (maximalIdeal (Z.subscheme.presheaf.stalk z)) + c)

open IsLocalRing in
/-- The stalk data at `z` of a closed subscheme `Z` of a smooth `k`-scheme `P`, smooth over `k`
near `z` and of codimension `c` at `z`: the quotient `𝒪_{P,z}/I_{Z,z}` is a regular local ring,
formally smooth over the base, and `dim 𝒪_{P,z} = dim 𝒪_{P,z}/I_{Z,z} + c`. -/
private theorem stalk_data_of_smooth_near {k : Type u} [Field k] {P : Scheme.{u}}
    (f : P ⟶ Spec (.of k)) [Smooth f] (Z : P.IdealSheafData) (z : Z.subscheme)
    (hsm : ∃ V : Z.subscheme.Opens, z ∈ V ∧ Smooth (V.ι ≫ Z.subschemeι ≫ f)) {c : ℕ}
    (hc : topologicalKrullDimAt P (Z.subschemeι z) = topologicalKrullDimAt Z.subscheme z + c) :
    IsRegularLocalRing
      (P.presheaf.stalk (Z.subschemeι z) ⧸ IdealSheafData.stalk Z (Z.subschemeι z)) ∧
    (letI := (f.stalkMap (Z.subschemeι z)).hom.toAlgebra;
      Algebra.FormallySmooth ((Spec (.of k)).presheaf.stalk (f (Z.subschemeι z)))
        (P.presheaf.stalk (Z.subschemeι z) ⧸ IdealSheafData.stalk Z (Z.subschemeι z))) ∧
    ringKrullDim (P.presheaf.stalk (Z.subschemeι z)) =
      ringKrullDim (P.presheaf.stalk (Z.subschemeι z) ⧸
        IdealSheafData.stalk Z (Z.subschemeι z)) + c := by
  obtain ⟨V, hxV, hV⟩ := hsm
  set i := Z.subschemeι
  obtain ⟨W0, hW0, hxW0, -⟩ := exists_isAffineOpen_mem_and_subset
    (show i z ∈ (⊤ : P.Opens) from trivial)
  have hk : IdealSheafData.stalk Z (i z) = RingHom.ker (i.stalkMap z).hom := by
    have := stalk_ker_eq_of_affine_target i z W0 hW0 hxW0
    rwa [Z.ker_subschemeι] at this
  let e : (P.presheaf.stalk (i z) ⧸ IdealSheafData.stalk Z (i z)) ≃+*
      Z.subscheme.presheaf.stalk z :=
    (Ideal.quotEquivOfEq hk).trans (RingHom.quotientKerEquivOfSurjective (i.stalkMap_surjective z))
  let v : V := ⟨z, hxV⟩
  have := isRegularLocalRing_stalk_of_smooth_over_field (V.ι ≫ i ≫ f) v
  have : IsIso (V.ι.stalkMap v) := IsOpenImmersion.instIsIsoCommRingCatStalkMap V.ι v
  have : IsRegularLocalRing (Z.subscheme.presheaf.stalk z) :=
    IsRegularLocalRing.of_ringEquiv (asIso (V.ι.stalkMap v)).commRingCatIsoToRingEquiv.symm
  have hsa : InfinitesimalLifting.SmoothAt (i ≫ f) z := by
    refine ⟨V, hxV, ?_⟩
    have he : (i ≫ f).resLE ⊤ V le_top = V.ι ≫ (i ≫ f) ≫ (Spec (.of k)).topIso.inv := by
      apply (cancel_mono (⊤ : (Spec (.of k)).Opens).ι).1
      simpa using Scheme.Hom.resLE_comp_ι _ le_top
    rw [he, ← Category.assoc]
    infer_instance
  refine ⟨IsRegularLocalRing.of_ringEquiv e.symm, ?_, ?_⟩
  · letI := (f.stalkMap (i z)).hom.toAlgebra
    letI : Algebra ((Spec (.of k)).presheaf.stalk (f (i z))) (Z.subscheme.presheaf.stalk z) :=
      ((i ≫ f).stalkMap z).hom.toAlgebra
    have : Algebra.FormallySmooth ((Spec (.of k)).presheaf.stalk (f (i z)))
        (Z.subscheme.presheaf.stalk z) := hsa.formallySmooth_stalkMap
    exact Algebra.FormallySmooth.of_equiv (AlgEquiv.ofRingEquiv (f := e) (fun a => by
      change (i.stalkMap z).hom ((f.stalkMap (i z)).hom a) = ((i ≫ f).stalkMap z).hom a
      rw [Scheme.Hom.stalkMap_comp]; rfl)).symm
  · rw [ringKrullDim_eq_of_ringEquiv e]
    exact ringKrullDim_stalk_eq_add_of_isRegularLocalRing f Z z hc

/-- **A smooth pair is locally pulled back from the origin of `𝔸^c`.** Let `f : P ⟶ Spec k` be
smooth, `Z` a closed subscheme of `P` and `z ∈ Z` a point near which `Z` is smooth over `k`, with
`Z` of codimension `c` in `P` at `z`. Then there are an open `U ∋ z` of `P` and a smooth
`k`-morphism `h : U ⟶ 𝔸^c_k` with `Z|_U = h^*𝔪₀`, `𝔪₀` the ideal of the origin. -/
@[mmp "lem_kr3f_smooth_pair_locally_pulled_back"]
public theorem exists_smooth_comap_ker_origin_eq {k : Type u} [Field k] {P : Scheme.{u}}
    (f : P ⟶ Spec (.of k)) [Smooth f] (Z : P.IdealSheafData) (z : Z.subscheme)
    (hsm : ∃ V : Z.subscheme.Opens, z ∈ V ∧ Smooth (V.ι ≫ Z.subschemeι ≫ f)) {c : ℕ}
    (hc : topologicalKrullDimAt P (Z.subschemeι z) = topologicalKrullDimAt Z.subscheme z + c) :
    ∃ (U : P.Opens) (_ : Z.subschemeι z ∈ U) (h : U.toScheme ⟶ 𝔸(ULift.{u} (Fin c); Spec (.of k))),
      Smooth h ∧ h ≫ 𝔸(ULift.{u} (Fin c); Spec (.of k)) ↘ Spec (.of k) = U.ι ≫ f ∧
      Z.comap U.ι = (AffineSpace.homOfVector (𝟙 (Spec (.of k))) 0).ker.comap h := by
  obtain ⟨hreg, hfs, hr⟩ := stalk_data_of_smooth_near f Z z hsm hc
  obtain ⟨hcn, U, hU, hpU, x, hloc, -, hcut⟩ :=
    MMP.Resolution.Bridges.exists_isLocalCoordinates_isCutOutByFirst_of_stalk f Z Z le_rfl
      (Z.subschemeι z) hreg hreg hfs hr hr
  have : IsAffine U.toScheme := hU
  let ι : ULift.{u} (Fin c) → ULift.{u} (Fin _) := fun i => ⟨Fin.castLE hcn i.down⟩
  have hι : Function.Injective ι := fun a b hab =>
    ULift.ext (Fin.castLE_injective hcn (congrArg ULift.down hab))
  let g := AffineSpace.homOfVector (U.ι ≫ f)
    (fun i : ULift.{u} (Fin _) => U.topIso.inv.hom (x i.down))
  have : Etale g := hloc
  have := smooth_reindex ι hι (Spec (.of k))
  refine ⟨U, hpU, g ≫ AffineSpace.reindex ι _, inferInstance, ?_, ?_⟩
  · simp [g, AffineSpace.reindex_over, AffineSpace.homOfVector_over]
  · let v : ULift.{u} (Fin c) → Γ(U.toScheme, ⊤) := fun i => U.topIso.inv.hom (x (ι i).down)
    apply Scheme.IdealSheafData.ext_of_isAffine
    have hR : ((AffineSpace.homOfVector (𝟙 (Spec (.of k))) 0).ker.comap
        (g ≫ AffineSpace.reindex ι _)).ideal ⟨⊤, isAffineOpen_top _⟩ =
          Ideal.span (Set.range v) := by
      rw [Scheme.ker_of_isAffine (AffineSpace.homOfVector (𝟙 (Spec (.of k))) 0),
        Stacks.Divisors.ideal_comap_appLE _ _ ⊤ (isAffineOpen_top _) ⊤ (isAffineOpen_top _) le_top,
        Stacks.Divisors.ideal_ofIdealTop_top, ker_appTop_homOfVector_zero, Ideal.map_span,
        ← Set.range_comp]
      have e1 : (homOfLE (le_top : (⊤ : U.toScheme.Opens) ≤ ⊤)) = 𝟙 _ := rfl
      have hv : (⇑((g ≫ AffineSpace.reindex ι _).appLE ⊤ ⊤ le_top).hom ∘
          AffineSpace.coord (Spec (.of k))) = v := by
        funext i
        change (U.toScheme.presheaf.map (homOfLE le_top).op).hom
          ((g ≫ AffineSpace.reindex ι _).appTop.hom (AffineSpace.coord _ i)) = v i
        rw [e1, op_id, CategoryTheory.Functor.map_id, CommRingCat.hom_id, RingHom.id_apply,
          Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.reindex_appTop_coord,
          AffineSpace.homOfVector_appTop_coord]
      rw [hv]
    have hL : (Z.comap U.ι).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span (Set.range v) := by
      rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, Scheme.Opens.ι_appIso]
      have hle : U.ι ''ᵁ ⊤ ≤ U := by simp
      rw [hcut ⟨U.ι ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion U.ι⟩ hle]
      have hres : ∀ a : Γ(P, U), (P.presheaf.map (homOfLE hle).op).hom a = U.topIso.inv.hom a :=
        fun a => rfl
      have hset : (fun i => (P.presheaf.map (homOfLE hle).op).hom (x i)) '' {i | (i : ℕ) < c} =
          Set.range v := by
        ext y
        constructor
        · rintro ⟨i, hi, rfl⟩
          exact ⟨⟨⟨i, hi⟩⟩, (hres _).symm⟩
        · rintro ⟨i, rfl⟩
          exact ⟨(ι i).down, i.down.2, hres _⟩
      rw [hset]
      exact Ideal.comap_id _
    exact hL.trans hR.symm

end MMP.Resolution.Kollar

end
