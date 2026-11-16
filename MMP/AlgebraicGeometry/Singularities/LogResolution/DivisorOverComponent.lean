module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldGraphDivisor
public import MMP.AlgebraicGeometry.Singularities.Snc.Basic
public import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
public import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
public import MMP.AlgebraicGeometry.Resolution.Blowup.StrictTransform
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.FirstChernClassSurjective
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjPointOfRingHom
public import StacksFrontier.AlgebraicGeometry.ProjTwistChain.Sections
public import MMP.AlgebraicGeometry.Resolution.ExceptionalDivisorPrime
public import MMP.AlgebraicGeometry.Resolution.DisjoiningSequence
public import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
public import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
public import MMP.AlgebraicGeometry.Morphisms.Birational.BiregularLocusCodimOnePoints

universe u v w

section

/-!
# Divisors over a component of the normalization of `S`, realized on a log resolution

Let `X` be a normal complex variety, `S` a reduced divisor and `B` a `ℚ`-divisor on `X`, `P` a
component of `S` with normalization `ν : P^ν ⟶ P ⊆ X`, and `F` a divisor over `P^ν`. Then `ord_F`
is the valuation of a prime divisor `C` of the strict transform `S'` of `P` on a log resolution
`f : Y ⟶ X` of `(X, (Supp S ∪ Supp B)_red)`, and `C` is an irreducible component of `E ∩ S'` for a
prime divisor `E` of `Y` exceptional over `X`.

The proof realizes `ord_F` by an ideal. Write `v` for `ord_F` read on `ℂ(P)`, and `x ∈ P` for the
centre of `v`. On an affine open `U ∋ x` of `P` there is a nonzero ideal `J ⊆ 𝔭_x` such that on the
blow-up `π_P : Bl_ℐ P ⟶ P` of any ideal sheaf `ℐ` restricting to `J` on `U`, some point `q` over
`x` has local ring the valuation ring of `v`. Take for `ℐ` the restriction to `P` of an ideal
sheaf `𝒥` of `X`, and let `π : Bl_𝒥 X ⟶ X`; the strict transform of `P` on `Bl_𝒥 X` is
`Bl_ℐ P`. Normalize `Bl_𝒥 X` and take an snc-preserving log resolution of the result, with
boundary the components of the strict transform of the boundary and the divisors exceptional
over `X`; the composite `f : Y ⟶ X` is a log resolution. The strict transform `S'` of `P` maps to
`Bl_ℐ P`, properly; a point `c ∈ S'` over `q` with the same local ring, a discrete valuation
ring, is the generic point of `C`. Finally `c` lies over `x ∈ V(𝒥)`, and `𝒥 𝒪_Y` is invertible,
so `c` lies on a prime divisor `E ⊆ f⁻¹ V(𝒥)`, which is exceptional since `V(𝒥) ⊊ P`.

## Main results

* `MMP.Flips.exists_isLogResolution_valuation_eq_of_properDivisorOver_primeDivisorNormalization`:
  the statement above.

## Implementation notes

The source first applies Chow's lemma to `F` over an affine open of `P` and realizes the
resulting projective model as a blow-up; here the blow-up is produced directly from the valuation
ring of `ord_F`, which is essentially of finite type over `ℂ`. Instead of a simultaneous
principalization of `𝒥` and of the ideal of the centre, `𝒥` is chosen inside the ideal of the
centre, and the log resolution is built on the normalization of `Bl_𝒥 X`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], proof of
  Theorem 17.2
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped WithZero

namespace MMP.FourfoldProofs.DivisorOverComponent

open MMP MMP.Mori MMP.Flips MMP.Resolution

section Helpers

/-! ### Generalities on prime divisors -/

private theorem genericPoint_mem_support {X : Scheme.{v}} (P : Mori.PrimeDivisor X) :
    P.genericPoint ∈ (P.support : Set X) := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact subset_closure rfl

/-- A prime divisor is determined by its support. -/
private theorem primeDivisor_eq_of_support_eq {X : Scheme.{v}} {P Q : Mori.PrimeDivisor X}
    (h : (P.support : Set X) = Q.support) : P = Q := by
  refine AlgebraicGeometry.PrimeDivisor.genericPoint_injective ?_
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h
  exact (inseparable_iff_closure_eq.2 h).eq

/-- The ideal sheaf of a prime divisor is the vanishing ideal of its support. -/
private theorem idealSheaf_eq_vanishingIdeal {X : Scheme.{v}} (P : Mori.PrimeDivisor X)
    {T : Closeds X} (hT : (T : Set X) = P.support) :
    P.idealSheaf = Scheme.IdealSheafData.vanishingIdeal T := by
  have := P.integral
  exact Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ (Closeds.ext hT.symm)

/-- The reduced divisor with components a finite set `s` of prime divisors has support `s`. -/
private theorem support_sum_single {X : Scheme.{v}} (s : Finset (Mori.PrimeDivisor X)) :
    (∑ E ∈ s, Finsupp.single E (1 : ℤ) : Divisor X).support = s := by
  classical
  ext E
  simp [Finsupp.finsetSum_apply, Finsupp.single_apply]

private theorem coeff_sum_single {X : Scheme.{v}} (s : Finset (Mori.PrimeDivisor X))
    (P : Mori.PrimeDivisor X) [Decidable (P ∈ s)] :
    (∑ E ∈ s, Finsupp.single E (1 : ℤ) : Divisor X).coeff P = if P ∈ s then 1 else 0 := by
  classical
  simp [DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply, Finsupp.single_apply]

/-- The reduced divisor with components `s` has coefficients `0` and `1`. -/
private theorem coeff_sum_single_eq_zero_or_eq_one {X : Scheme.{v}}
    (s : Finset (Mori.PrimeDivisor X)) (P : Mori.PrimeDivisor X) :
    (∑ E ∈ s, Finsupp.single E (1 : ℤ) : Divisor X).coeff P = 0 ∨
      (∑ E ∈ s, Finsupp.single E (1 : ℤ) : Divisor X).coeff P = 1 := by
  classical
  rw [coeff_sum_single]
  split_ifs <;> simp

/-- A coefficient of the linear extension of a partial map `φ` on prime divisors is nonzero only
at the image of a prime divisor with nonzero coefficient. -/
private theorem exists_apply_ne_zero_of_mapPrimeDivisors_apply_ne_zero {X Y : Scheme.{v}}
    {R : Type*} [AddCommMonoid R] {φ : Mori.PrimeDivisor X → Option (Mori.PrimeDivisor Y)}
    {D : DivisorWithCoeffs R X} {P : Mori.PrimeDivisor Y}
    (h : DivisorWithCoeffs.mapPrimeDivisors φ D P ≠ 0) : ∃ Q, D Q ≠ 0 ∧ φ Q = some P := by
  classical
  by_contra hne
  push Not at hne
  refine h ?_
  conv_lhs => rw [← Finsupp.sum_single D]
  rw [Finsupp.sum, map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun Q hQ => ?_
  rw [DivisorWithCoeffs.mapPrimeDivisors_single]
  rcases hφ : φ Q with _ | E
  · rfl
  · have hne' : E ≠ P := fun he => hne Q (Finsupp.mem_support_iff.mp hQ) (by rw [hφ, he])
    exact Finsupp.single_eq_of_ne' hne'

/-! ### Strict transforms under the inverse of a birational morphism -/

private theorem source_ι_comp_eq_of_toRationalMap_eq {X Y : Scheme.{v}} [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) : e.source.ι ≫ f = e.iso.hom ≫ e.target.ι :=
  ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp he)).symm

/-- If `e` is a partial isomorphism representing `f : Y ⟶ X` and `g'` a partial map representing
`e⁻¹`, then `f ∘ g'` is the identity where `g'` is defined. -/
private theorem apply_hom_eq_of_isInverse {X Y : Scheme.{v}} [IsReduced Y] [IsReduced X]
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

private theorem coe_transform_eq_closure_singleton {X Y : Scheme.{v}} [IsReduced X]
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
    refine ⟨⟨P.genericPoint, hP⟩, ?_, rfl⟩
    exact genericPoint_mem_support P

private theorem genericPoint_eq_of_transformPrimeDivisor_eq_some {X Y : Scheme.{v}} [IsReduced X]
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
private theorem genericPoint_eq_of_transformPrimeDivisor_inverse_eq_some {X Y : Scheme.{v}}
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

private theorem isSeparated_terminal_from {k : Type v} [Field k] {X : Scheme.{v}}
    (sX : X ⟶ Spec (.of k)) [IsSeparated sX] : IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

/-- A component `P` of the strict transform `g⁻¹_* D` under a birational morphism of varieties
lies over a component `Q` of `D`: `g(η_P) = η_Q`. -/
private theorem exists_map_genericPoint_eq_of_birationalInverseTransform_ne_zero
    {k : Type v} [Field k] {X Y : Scheme.{v}} {sX : X ⟶ Spec (.of k)}
    (hX : Mori.IsVariety k sX) {g : Y ⟶ X} (hY : Mori.IsVariety k (g ≫ sX))
    (hg : IsBirationalMorphism g) {R : Type*} [AddCommMonoid R] {D : DivisorWithCoeffs R X}
    {P : Mori.PrimeDivisor Y} (h : MMP.Flips.birationalInverseTransform g hg D P ≠ 0) :
    ∃ Q, D Q ≠ 0 ∧ g P.genericPoint = Q.genericPoint := by
  have : IsIntegral X := hX.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  have : IsSeparated sX := hX.toIsSeparated
  have : IsSeparated (g ≫ sX) := hY.toIsSeparated
  have := isSeparated_terminal_from sX
  have := isSeparated_terminal_from (g ≫ sX)
  obtain ⟨Q, hQ, hQP⟩ := exists_apply_ne_zero_of_mapPrimeDivisors_apply_ne_zero
    (φ := Mori.RationalMap.transformPrimeDivisor (Mori.RationalMap.IsBirational.inverse hg)) h
  exact ⟨Q, hQ, genericPoint_eq_of_transformPrimeDivisor_inverse_eq_some hg hQP⟩

/-! ### Prime divisors exceptional over `X` -/

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
private theorem exists_topologicalKrullDim_eq {k : Type v} [Field k] {X : Scheme.{v}}
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

/-! ### Simple normal crossing closed subsets and their components -/

section SNC

variable {k : Type v} [Field k] {Y : Scheme.{v}} {sY : Y ⟶ Spec (.of k)}

private theorem exists_coheight_eq_one_of_mem_componentsOf {S : Set Y} (hSc : IsClosed S)
    (hS : MMP.Mori.IsPureCodimOne (⟨S, hSc⟩ : Closeds Y)) {V : Set Y}
    (hV : V ∈ componentsOf S) : ∃ ξ : Y, V = closure {ξ} ∧ Order.coheight ξ = 1 := by
  obtain ⟨ξ, -, hξ⟩ := Aux.exists_eq_closure_of_mem_componentsOf hSc hV
  refine ⟨ξ, hξ, ?_⟩
  rw [← MMP.Flips.codimension_closureSingleton]
  apply hS
  refine ⟨?_, fun W' hW' hle => ?_⟩
  · change closure {ξ} ⊆ S
    rw [← hξ]
    exact hV.1.2
  · have : (W' : Set Y) ⊆ V := hV.2 ⟨W'.isIrreducible, hW'⟩ (by rwa [hξ])
    change (W' : Set Y) ⊆ closure {ξ}
    rw [← hξ]
    exact this

/-- The support of a prime divisor contained in an snc closed subset `S` is an irreducible
component of `S`. -/
private theorem support_mem_componentsOf [NoetherianSpace Y] {S : Set Y}
    (hS : IsSNCClosedSubset sY S) {P : Mori.PrimeDivisor Y} (hP : (P.support : Set Y) ⊆ S) :
    (P.support : Set Y) ∈ componentsOf S := by
  obtain ⟨hSc, hempty | ⟨hpure, -, -⟩⟩ := hS
  · exfalso
    have := hP (genericPoint_mem_support P)
    rw [hempty] at this
    exact this
  · obtain ⟨-, hcov⟩ := Aux.finite_and_cover_componentsOf hSc
    obtain ⟨W, hW, hηW⟩ := hcov (hP (genericPoint_mem_support P))
    obtain ⟨ξ, hWξ, hξ1⟩ := exists_coheight_eq_one_of_mem_componentsOf hSc hpure hW
    have hsp : ξ ⤳ P.genericPoint := specializes_iff_mem_closure.mpr (hWξ ▸ hηW)
    have hξη : ξ = P.genericPoint := by
      by_contra hne
      have hlt : P.genericPoint < ξ := lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hsp)
        fun hle => hne (hsp.antisymm (Scheme.le_iff_specializes.mp hle)).eq
      have := Order.coheight_strictAnti hlt
      rw [hξ1, P.coheight_genericPoint] at this
      exact lt_irrefl _ (this (by simp))
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    change closure {P.genericPoint} ∈ _
    rw [← hξη, ← hWξ]
    exact hW

/-- Only finitely many prime divisors are contained in an snc closed subset. -/
private theorem finite_setOf_support_subset [NoetherianSpace Y] {S : Set Y}
    (hS : IsSNCClosedSubset sY S) :
    {P : Mori.PrimeDivisor Y | (P.support : Set Y) ⊆ S}.Finite := by
  refine Set.Finite.of_finite_image ((Aux.finite_and_cover_componentsOf hS.1).1.subset ?_)
    fun P _ Q _ h => primeDivisor_eq_of_support_eq h
  rintro - ⟨P, hP, rfl⟩
  exact support_mem_componentsOf hS hP

/-- **A reduced divisor whose components lie in an snc closed subset is snc.** -/
private theorem isSNC_sum_single_of_support_subset [LocallyOfFiniteType sY] [NoetherianSpace Y]
    [IsLocallyNoetherian Y] (hsm : IsSmoothScheme sY) {S : Set Y} (hS : IsSNCClosedSubset sY S)
    (s : Finset (Mori.PrimeDivisor Y)) (hs : ∀ P ∈ s, (P.support : Set Y) ⊆ S) :
    (∑ P ∈ s, Finsupp.single P (1 : ℤ) : Divisor Y).IsSNC sY := by
  classical
  have hc : ∀ P ∈ s, (P.support : Set Y) ∈ componentsOf S := fun P hP =>
    support_mem_componentsOf hS (hs P hP)
  obtain ⟨hSc, hempty | ⟨-, -, hfam⟩⟩ := id hS
  · have hs0 : s = ∅ := Finset.eq_empty_of_forall_notMem fun P hP => by
      have := hs P hP (genericPoint_mem_support P)
      rw [hempty] at this
      exact this
    subst hs0
    rw [Finset.sum_empty]
    exact DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme sY hsm
  have hG := support_sum_single s
  have hideal : ∀ P (hP : P ∈ s),
      P.idealSheaf = componentsFamily S ⟨(P.support : Set Y), hc P hP⟩ := fun P hP =>
    idealSheaf_eq_vanishingIdeal P (by
      rw [Closeds.coe_closure, (Aux.isClosed_of_mem_componentsOf hSc (hc P hP)).closure_eq])
  refine ⟨fun P hP => ?_, fun x => ?_⟩
  · rw [hG] at hP
    rw [hideal P hP]
    exact (hfam.1 _).2.2
  · obtain ⟨m, z, c, hz, hcI, hcinj⟩ := hfam.2 x
    have hs' : ∀ P : {P : Mori.PrimeDivisor Y //
        P ∈ (∑ P ∈ s, Finsupp.single P (1 : ℤ) : Divisor Y).support ∧ x ∈ P.support},
        P.1 ∈ s := fun P => hG.subset P.2.1
    have hmem : ∀ P : {P : Mori.PrimeDivisor Y //
        P ∈ (∑ P ∈ s, Finsupp.single P (1 : ℤ) : Divisor Y).support ∧ x ∈ P.support},
        x ∈ (componentsFamily S ⟨(P.1.support : Set Y), hc P.1 (hs' P)⟩).support := fun P => by
      rw [← SetLike.mem_coe, coe_support_componentsFamily hSc]
      exact P.2.2
    refine ⟨m, z, fun P => c ⟨_, hmem P⟩, hz, fun P Q h => ?_, fun P => ?_⟩
    · have h1 := congrArg (fun V => (V.1.1 : Set Y)) (hcinj h)
      exact Subtype.ext (primeDivisor_eq_of_support_eq h1)
    · rw [hideal P.1 (hs' P)]
      exact hcI ⟨_, hmem P⟩

/-- An snc reduced divisor in the sense of `DivisorWithCoeffs.IsSNC` is an snc divisor in the
sense of *Flips and abundance*. -/
private theorem isSNCDivisor_sum_single (s : Finset (Mori.PrimeDivisor Y))
    (h : (∑ P ∈ s, Finsupp.single P (1 : ℤ) : Divisor Y).IsSNC sY) :
    MMP.Flips.IsSNCDivisor sY (∑ P ∈ s, Finsupp.single P (1 : ℤ)) := by
  classical
  exact ⟨coeff_sum_single_eq_zero_or_eq_one s, h.1, fun p _ => h.2 p⟩

end SNC

/-! ### From an snc closed subset to a log resolution -/

/-- **A resolution whose boundary components lie in an snc closed subset is a log resolution.**
Let `X` be a normal variety, `B` a boundary on `X` and `g : Y ⟶ X` a resolution. If the components
of `g⁻¹_* B` and the prime divisors exceptional over `X` all lie in a closed subset `S ⊆ Y` with
simple normal crossings, then `g` is a log resolution of `(X, B)`: the reduced divisor they form is
snc. -/
private theorem isLogResolution_of_forall_support_subset {k : Type v} [Field k]
    {X Y : Scheme.{v}} {sX : X ⟶ Spec (.of k)} {B : RDivisor X}
    (hB : MMP.Flips.IsLogVariety k sX B) {g : Y ⟶ X} (hres : IsResolutionOfVariety sX g)
    {S : Set Y} (hS : IsSNCClosedSubset (g ≫ sX) S)
    (hsub : ∀ P : Mori.PrimeDivisor Y,
      (MMP.Flips.birationalInverseTransform g hres.isBirationalMorphism B P ≠ 0 ∨
        MMP.Flips.IsExceptionalPrimeDivisor sX g P) → (P.support : Set Y) ⊆ S) :
    MMP.Flips.IsLogResolution sX B g := by
  classical
  have hX : IsNormalVariety k sX := hB.isNormalVariety
  have hYv : Mori.IsVariety k (g ≫ sX) := hres.isVariety_source
  have hg : IsBirationalMorphism g := hres.isBirationalMorphism
  have hsm : IsSmoothScheme (g ≫ sX) := hres.isSmoothScheme
  have : IsProper g := hres.isProjective.isProper
  have : LocallyOfFiniteType (g ≫ sX) := hYv.toLocallyOfFiniteType
  have : QuasiCompact (g ≫ sX) := hYv.toQuasiCompact
  have : IsIntegral Y := hYv.toIsIntegral
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sX)
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (g ≫ sX)
  have : IsNoetherian Y := ⟨⟩
  have hfin : {P : Mori.PrimeDivisor Y |
      MMP.Flips.birationalInverseTransform g hg B P ≠ 0 ∨
        MMP.Flips.IsExceptionalPrimeDivisor sX g P}.Finite :=
    (finite_setOf_support_subset hS).subset fun P hP => hsub P hP
  set s := hfin.toFinset with hs
  have hG := isSNC_sum_single_of_support_subset hsm hS s
    (fun P hP => hsub P (by simpa [hs] using hP))
  refine ⟨hB, hYv, hsm, inferInstance, hg, ∑ P ∈ s, Finsupp.single P (1 : ℤ),
    coeff_sum_single_eq_zero_or_eq_one s, fun P => ?_, isSNCDivisor_sum_single s hG⟩
  · rw [coeff_sum_single]
    have hmem : P ∈ s ↔ (MMP.Flips.birationalInverseTransform g hg B P ≠ 0 ∨
        MMP.Flips.IsExceptionalPrimeDivisor sX g P) := by
      rw [hs, Set.Finite.mem_toFinset]
      rfl
    split_ifs with h
    · exact ⟨fun _ => hmem.mp h, fun _ => rfl⟩
    · exact ⟨fun h' => absurd h' (by decide), fun h' => absurd (hmem.mpr h') h⟩

private theorem transformPrimeDivisor_eq_some_of_genericPoint_eq {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : Mori.PrimeDivisor X}
    {E : Mori.PrimeDivisor Y} (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ)
    (hP : P.genericPoint ∈ g'.domain) (hE : E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩) :
    Mori.RationalMap.transformPrimeDivisor φ P = some E := by
  refine Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mpr
    ⟨Mori.RationalMap.definedAt_iff.mpr ⟨g', hP, hg'⟩, ?_⟩
  have h1 : Mori.RationalMap.transform φ P.idealSheaf.support = E.idealSheaf.support := by
    apply SetLike.coe_injective
    rw [coe_transform_eq_closure_singleton g' hg' P hP, ← hE]
    exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure E).symm
  have := E.integral
  rw [Mori.RationalMap.transformIdeal, h1, MMP.Positivity.vanishingIdeal_support_of_isReduced]

/-- For a proper birational morphism `f : Y ⟶ X` of varieties with `X` normal, if `f` sends the
generic point of a prime divisor `E` of `Y` to that of a prime divisor `P` of `X`, then the
strict transform of `P` under `f⁻¹` is `E`. -/
private theorem transformPrimeDivisor_inverse_eq_some_of_genericPoint_eq {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (f : Y ⟶ X)
    (hY : Mori.IsVariety k (f ≫ sX)) [IsProper f] (hf : IsBirationalMorphism f)
    {P : Mori.PrimeDivisor X} {E : Mori.PrimeDivisor Y} (h : f E.genericPoint = P.genericPoint) :
    Mori.RationalMap.transformPrimeDivisor (Mori.RationalMap.IsBirational.inverse hf) P =
      some E := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (f ≫ sX) := hY.toIsSeparated
  have := isSeparated_terminal_from sX
  have := isSeparated_terminal_from (f ≫ sX)
  have : IsNormal X := hX.2
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsDominant f := hf.isDominant
  have hbij := hf.functionFieldMap_bijective
  obtain ⟨e, he, he'⟩ := hf.isInverse_inverse
  have hdef : Mori.RationalMap.DefinedAt (Mori.RationalMap.IsBirational.inverse hf)
      P.genericPoint := by
    by_contra hnd
    have h2 := le_closedsCodimension_iff.mp
      (MMP.Flips.RationalMap.isMorphismInCodimOne_inverse hX f hY hf)
      (IrreducibleCloseds.closureSingleton P.genericPoint)
      (closure_minimal (Set.singleton_subset_iff.mpr hnd)
        (Mori.RationalMap.dom (Mori.RationalMap.IsBirational.inverse hf)).compl.isClosed)
    rw [codimension_eq_coheight, show IrreducibleCloseds.closureSingleton P.genericPoint =
      (irreducibleSetEquivPoints (α := X)).symm P.genericPoint from rfl,
      Order.coheight_orderIso, P.coheight_genericPoint] at h2
    exact absurd h2 (by decide)
  obtain ⟨g', hP, hg'⟩ := Mori.RationalMap.definedAt_iff.mp hdef
  refine transformPrimeDivisor_eq_some_of_genericPoint_eq g' hg' hP ?_
  have hy := apply_hom_eq_of_isInverse f e he g' (hg'.trans he'.symm) hP
  have := P.isDiscreteValuationRing_localRing
  have : ValuationRing (X.presheaf.stalk (f E.genericPoint)) := by rw [h]; infer_instance
  have : ValuationRing (X.presheaf.stalk (f (g'.hom ⟨P.genericPoint, hP⟩))) := by
    rw [hy]; infer_instance
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hbij E.genericPoint
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hbij (g'.hom ⟨P.genericPoint, hP⟩)
  exact MMP.Positivity.eq_of_isIso_stalkMap f hbij (hy.trans h.symm)

/-- A local ring of an integral scheme `Y` birational to `X` which, inside the function field, is
the valuation ring of a valuation of `k(X)` is a valuation ring. -/
private theorem valuationRing_stalk_of_forall_le_one_iff {X Y : Scheme.{w}}
    [IsIntegral X] [IsIntegral Y] (β : Y ⟶ X) [IsDominant β]
    (hβ : Function.Bijective (functionFieldMap β))
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation X.functionField Γ) (q : Y)
    (hq : ∀ g : X.functionField, v g ≤ 1 ↔
        ∃ a : Y.presheaf.stalk q, algebraMap _ Y.functionField a = functionFieldMap β g) :
    ValuationRing (Y.presheaf.stalk q) := by
  let φ := RingEquiv.ofBijective (functionFieldMap β) hβ
  let w : Valuation Y.functionField Γ := v.comap φ.symm.toRingHom
  have hw : ∀ r, w r ≤ 1 ↔ ∃ a : Y.presheaf.stalk q, algebraMap _ Y.functionField a = r := by
    intro r
    have := hq (φ.symm r)
    rwa [show functionFieldMap β (φ.symm r) = φ (φ.symm r) from rfl,
      RingEquiv.apply_symm_apply] at this
  exact ValuationRing.of_integers w
    ⟨IsFractionRing.injective _ _, fun a => (hw _).2 ⟨a, rfl⟩, fun r hr => (hw r).1 hr⟩

/-- A morphism of integral schemes, locally of finite type and birational in the sense of
`AlgebraicGeometry.IsBirational`, is a birational morphism. -/
private theorem isBirationalMorphism_of_isBirational {X Y : Scheme.{w}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : IsBirational f) :
    IsBirationalMorphism f := by
  have : Finite (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]
    exact Set.finite_singleton _
  have : Finite (irreducibleComponents Y) := by
    rw [irreducibleComponents_eq_singleton]
    exact Set.finite_singleton _
  obtain ⟨U, V, hUV, hU, hV, hiso⟩ :=
    exists_dense_opens_isIso_resLE_of_isBirational f hf (Or.inl ⟨inferInstance, inferInstance⟩)
  exact isBirationalMorphism_of_isIso_resLE f U V hU.nonempty hV.nonempty hUV hiso

/-- An ideal of the sections over an affine open extends to an ideal sheaf: the kernel of the
closed subscheme `Spec (Γ(X, U) ⧸ J) ⟶ X`, i.e. the ideal sheaf of its scheme-theoretic closure. -/
private theorem exists_idealSheafData_ideal_eq {X : Scheme.{w}} [QuasiSeparatedSpace X]
    (U : X.affineOpens) (J : Ideal Γ(X, U)) : ∃ ℐ : X.IdealSheafData, ℐ.ideal U = J := by
  have hU : IsAffineOpen (U : X.Opens) := U.2
  let φ := CommRingCat.ofHom (Ideal.Quotient.mk J)
  let π : Spec (.of (Γ(X, U) ⧸ J)) ⟶ X := Spec.map φ ≫ hU.fromSpec
  refine ⟨π.ker, ?_⟩
  rw [Scheme.Hom.ker_apply]
  ext a
  rw [RingHom.mem_ker]
  have hle : (⊤ : (Spec (.of (Γ(X, U) ⧸ J))).Opens) ≤ π ⁻¹ᵁ U := by
    intro y _
    change hU.fromSpec ((Spec.map φ) y) ∈ (U : X.Opens)
    exact hU.range_fromSpec.subset ⟨_, rfl⟩
  have hres : (π.app U).hom a = 0 ↔ (π.appLE U ⊤ hle).hom a = 0 := by
    have heq : (homOfLE hle) = eqToHom (top_le_iff.mp hle).symm := Subsingleton.elim _ _
    rw [Scheme.Hom.appLE, heq, CommRingCat.comp_apply]
    exact (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
      ((Spec (.of (Γ(X, U) ⧸ J))).presheaf.map (eqToHom (top_le_iff.mp hle).symm).op)).1).symm
  have hcomp : π.appLE U ⊤ hle = (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec.map φ).appTop := by
    rw [Scheme.Hom.comp_appLE, hU.fromSpec_app_self, Category.assoc]
    congr 1
  rw [hres, hcomp, CommRingCat.comp_apply]
  have hnat := congrArg (fun g => g.hom ((Scheme.ΓSpecIso Γ(X, U)).inv.hom a))
    (Scheme.ΓSpecIso_naturality φ)
  simp only at hnat
  rw [← map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ J))).hom).1]
  erw [hnat]
  rw [CommRingCat.comp_apply]
  erw [Iso.inv_hom_id_apply]
  exact Ideal.Quotient.eq_zero_iff_mem (I := J)

/-- Let `φ : S → L` land in the valuation ring of `w`, with `S` essentially of finite type over
`R`. If a subring `C` contains the images of `R` and of the generators of `S`, every `φ s` is a
fraction `c / t` with `c, t ∈ C` and `w t = 1`. -/
private theorem exists_mul_eq_of_essFiniteType {R S L : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.EssFiniteType R S] [Field L] {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ) (φ : S →+* L)
    (hφ : ∀ s, w (φ s) ≤ 1) (C : Subring L) (hR : ∀ r, φ (algebraMap R S r) ∈ C)
    (hσ : ∀ s ∈ Algebra.EssFiniteType.finset R S, φ s ∈ C) (s : S) :
    ∃ c ∈ C, ∃ t ∈ C, w t = 1 ∧ φ s * t = c := by
  have hcond := (Algebra.essFiniteType_cond_iff R S (Algebra.EssFiniteType.finset R S)).mp
    (Algebra.EssFiniteType.isLocalization R S)
  have hadj : ∀ y ∈ Algebra.adjoin R (Algebra.EssFiniteType.finset R S : Set S), φ y ∈ C := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem x hx => exact hσ x hx
    | algebraMap r => exact hR r
    | add x y _ _ hx hy => rw [map_add]; exact C.add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact C.mul_mem hx hy
  obtain ⟨t, ht, htu, hst⟩ := hcond s
  exact ⟨φ (s * t), hadj _ hst, φ t, hadj _ ht,
    (letI := φ.toAlgebra; Valuation.Integers.one_of_isUnit' (v := w) htu hφ),
    (map_mul φ s t).symm⟩

/-- If every element of `J` has value at most that of `h`, every element of `Jⁿ` has value at
most that of `hⁿ`. -/
private theorem valuation_le_pow_of_mem_pow {A L : Type*} [CommRing A] [Field L] {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ) (ι : A →+* L)
    (hA : ∀ a, w (ι a) ≤ 1) (J : Ideal A) (h : A) (hJ : ∀ y ∈ J, w (ι y) ≤ w (ι h)) :
    ∀ n : ℕ, ∀ y ∈ J ^ n, w (ι y) ≤ w (ι h) ^ n := by
  intro n
  induction n with
  | zero => exact fun y _ => by simpa using hA y
  | succ n ih =>
    intro y hy
    rw [pow_succ] at hy
    refine Submodule.mul_induction_on hy (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · rw [map_mul, map_mul, pow_succ]
      exact mul_le_mul' (ih a ha) (hJ b hb)
    · rw [map_add]
      exact (w.map_add _ _).trans (max_le ha hb)

/-- If `x * hⁿ = y` with `h ≠ 0` and `v y ≤ v hⁿ`, then `v x ≤ 1`. -/
private theorem valuation_le_one_of_mul_pow_eq {L : Type*} [Field L] {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation L Γ) {x h y : L} {n : ℕ} (hh : h ≠ 0)
    (hxy : x * h ^ n = y) (hy : v y ≤ v h ^ n) : v x ≤ 1 := by
  rw [← hxy, map_mul, map_pow] at hy
  exact (mul_le_iff_le_one_left (pow_pos ((Valuation.pos_iff v).2 hh) n)).mp hy

/-- The local rings of a scheme locally of finite type over a field `k` are essentially of
finite type over `k`. -/
private theorem essFiniteType_stalkAlgebra {k : Type w} [Field k] {Y : Scheme.{w}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (y : Y) :
    letI := stalkAlgebra sY y
    Algebra.EssFiniteType k (Y.presheaf.stalk y) := by
  let := stalkAlgebra sY y
  have := (sY.base y).isPrime
  have h0 : (algebraMap k (Localization.AtPrime (sY.base y).asIdeal)).EssFiniteType := by
    rw [RingHom.essFiniteType_algebraMap]
    exact Algebra.EssFiniteType.of_isLocalization _ (sY.base y).asIdeal.primeCompl
  have hiso : (Spec.stalkIso (.of k) (sY.base y)).inv.hom.EssFiniteType :=
    (RingHom.FiniteType.of_surjective _
      (asIso (Spec.stalkIso (.of k) (sY.base y)).inv).commRingCatIsoToRingEquiv.surjective
      ).essFiniteType
  have h1 : ((Scheme.ΓSpecIso (.of k)).inv ≫
      (Spec (.of k)).presheaf.germ ⊤ (sY.base y) (by simp)).hom.EssFiniteType := by
    have e := congrArg CommRingCat.Hom.hom
      (Spec.algebraMap_stalkIso_inv (R := .of k) (x := sY.base y))
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at e
    rw [← e]
    exact h0.comp hiso
  have h2 := h1.comp (LocallyOfFiniteType.stalkMap sY y)
  rw [← RingHom.essFiniteType_algebraMap]
  convert h2 using 1
  change ((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appTop ≫ Y.presheaf.germ ⊤ y (by simp)).hom = _
  rw [← CommRingCat.hom_comp, Category.assoc, Scheme.Hom.germ_stalkMap]
  rfl

/-- The valuation ring of a divisor of the function field, as the image of a `k`-algebra
essentially of finite type. -/
private theorem IsDivisorOfFunctionField.exists_essFiniteType {k : Type w} [Field k]
    {X : Scheme.{w}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] {v : Valuation X.functionField ℤᵐ⁰}
    (hv : IsDivisorOfFunctionField k sX v) :
    letI := functionFieldAlgebra sX
    ∃ (S : Type w) (_ : CommRing S) (_ : Algebra k S) (_ : Algebra.EssFiniteType k S)
      (φ : S →ₐ[k] X.functionField), ∀ g, v g ≤ 1 ↔ g ∈ φ.range := by
  let := functionFieldAlgebra sX
  obtain ⟨Y, sY, hY, E, hE⟩ := hv
  have : IsIntegral Y := hY.1.toIsIntegral
  have : IsNormal Y := hY.2
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  let := functionFieldAlgebra sY
  obtain ⟨e, rfl⟩ := hE
  let := stalkAlgebra sY E.genericPoint
  have := essFiniteType_stalkAlgebra sY E.genericPoint
  have := isScalarTower_stalk_functionField sY E.genericPoint
  refine ⟨Y.presheaf.stalk E.genericPoint, inferInstance, inferInstance, inferInstance,
    (e.symm : Y.functionField →ₐ[k] X.functionField).comp
      (IsScalarTower.toAlgHom k _ Y.functionField), fun g => ?_⟩
  rw [Valuation.comap_apply, PrimeDivisor.divisorialValuation_le_one_iff]
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    change e.symm (algebraMap (Y.presheaf.stalk E.genericPoint) Y.functionField s) = g
    erw [hs]
    exact e.symm_apply_apply g
  · rintro ⟨s, rfl⟩
    refine ⟨s, ?_⟩
    change _ = e (e.symm (algebraMap (Y.presheaf.stalk E.genericPoint) Y.functionField s))
    rw [AlgEquiv.apply_symm_apply]

/-- Sections pulled back along a dominant morphism of integral schemes map to the function field
through `functionFieldMap`. -/
private theorem germToFunctionField_appLE {X Y : Scheme.{w}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) [IsDominant f] (U : X.Opens) (V : Y.Opens) [Nonempty U] [Nonempty V]
    (h : V ≤ f ⁻¹ᵁ U) (s : Γ(X, U)) :
    Y.germToFunctionField V (f.appLE U V h s) = functionFieldMap f (X.germToFunctionField U s) := by
  obtain ⟨⟨y, hy⟩⟩ := ‹Nonempty V›
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X := Y) hy,
    ← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (h hy),
    MMP.Mori.functionFieldMap_algebraMap_stalk]
  congr 1
  erw [Scheme.Hom.germ_stalkMap_apply]
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]

/-- The constants `k ⊆ k(X)` are sections over every nonempty open. -/
private theorem exists_germToFunctionField_eq_algebraMap {k : Type w} [Field k] {X : Scheme.{w}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] (U : X.Opens) [Nonempty U] (c : k) :
    letI := functionFieldAlgebra sX
    ∃ a : Γ(X, U), X.germToFunctionField U a = algebraMap k X.functionField c := by
  let := functionFieldAlgebra sX
  refine ⟨X.presheaf.map (homOfLE le_top).op (sX.appTop ((Scheme.ΓSpecIso (.of k)).inv c)), ?_⟩
  change X.presheaf.germ U _ _ _ = ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
    X.presheaf.germ ⊤ (genericPoint X) (by simp)) c
  rw [TopCat.Presheaf.germ_res_apply]
  rfl

/-- Given a valuation `v` of the fraction field `K` of `A`, at most `1` on `A`, with an element of
value `exp (-1)`, finitely many elements `φ s` of `K` are fractions `g s / h₀` with `h₀ ≠ 0` of
value `< 1`. -/
private theorem exists_ne_zero_valuation_lt_one_mul_eq {A K S : Type*} [CommRing A] [IsDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K] (v : Valuation K ℤᵐ⁰)
    (hle : ∀ a, v (algebraMap A K a) ≤ 1) {g₀ : K} (hg₀ : v g₀ = WithZero.exp (-1))
    (φ : S → K) (σ : Finset S) :
    ∃ (h₀ : A) (g : S → A), h₀ ≠ 0 ∧ v (algebraMap A K h₀) < 1 ∧
      ∀ s ∈ σ, algebraMap A K (g s) = algebraMap A K h₀ * φ s := by
  classical
  obtain ⟨⟨h₁, hh₁⟩, hden⟩ :=
    IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors A) (σ.image φ)
  have hden' : ∀ s ∈ σ, ∃ r : A, algebraMap A K r = algebraMap A K h₁ * φ s := fun s hs => by
    obtain ⟨r, hr⟩ := hden (φ s) (Finset.mem_image_of_mem _ hs)
    exact ⟨r, hr.trans (Algebra.smul_def _ _)⟩
  choose! g₁ hg₁ using hden'
  obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.mk'_surjective (nonZeroDivisors A) g₀
  have hnd' : algebraMap A K n = g₀ * algebraMap A K d := by
    change IsLocalization.mk' K n d = g₀ at hnd
    rw [← IsLocalization.mk'_spec (S := K) n d, hnd]
  have hn1 : v (algebraMap A K n) < 1 := by
    rw [hnd', map_mul, hg₀]
    calc _ ≤ WithZero.exp (-1) * 1 := mul_le_mul_right (hle _) _
      _ < 1 := by rw [mul_one, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, mul_eq_zero] at hnd'
    rcases hnd' with h | h
    · rw [h, map_zero] at hg₀
      exact WithZero.exp_ne_zero hg₀.symm
    · exact nonZeroDivisors.ne_zero d.2
        (IsFractionRing.injective A K (h.trans (map_zero _).symm))
  refine ⟨n * h₁, fun s => n * g₁ s, mul_ne_zero hn0 (nonZeroDivisors.ne_zero hh₁), ?_,
    fun s hs => by simp only [map_mul, hg₁ s hs]; ring⟩
  rw [map_mul, map_mul]
  exact (mul_le_of_le_one_right' (hle _)).trans_lt hn1

/-- If `v ∘ ι ≤ 1` and `ι (g s) = ι h₀ * φ s` with `v (φ s) ≤ 1`, every element of the ideal
generated by `h₀` and the `g s` has value at most `v (ι h₀)`. -/
private theorem valuation_le_of_mem_span_insert {A K S Γ : Type*} [CommRing A] [Field K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (ι : A →+* K)
    (hι : ∀ a, v (ι a) ≤ 1) {h₀ : A} {g : S → A} {φ : S → K} {σ : Set S}
    (hφ : ∀ s, v (φ s) ≤ 1) (hg : ∀ s ∈ σ, ι (g s) = ι h₀ * φ s) :
    ∀ y ∈ Ideal.span (insert h₀ (g '' σ)), v (ι y) ≤ v (ι h₀) := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    rcases hz with rfl | ⟨s, hs, rfl⟩
    · exact le_rfl
    · rw [hg s hs, map_mul]
      exact mul_le_of_le_one_right' (hφ s)
  | zero => rw [map_zero, map_zero]; exact zero_le
  | add y z _ _ hy hz => rw [map_add]; exact (v.map_add _ _).trans (max_le hy hz)
  | smul c y _ hy =>
    rw [smul_eq_mul, map_mul, map_mul]
    exact (mul_le_of_le_one_left' (hι c)).trans hy

/-- For a valuation `w` which is at most `1` on the image of `ψ : A →+* K`, the elements of value
`< 1` form a prime ideal of `A`. -/
private theorem exists_isPrime_mem_iff_valuation_lt_one {A K Γ : Type*} [CommRing A] [Field K]
    [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ) (ψ : A →+* K)
    (hle : ∀ t, w (ψ t) ≤ 1) : ∃ 𝔮 : Ideal A, 𝔮.IsPrime ∧ ∀ t, t ∈ 𝔮 ↔ w (ψ t) < 1 := by
  let 𝔮 : Ideal A :=
    { carrier := {t | w (ψ t) < 1}
      add_mem' := fun {y z} hy hz => by
        simp only [Set.mem_ofPred_eq, map_add] at *
        exact (w.map_add _ _).trans_lt (max_lt hy hz)
      zero_mem' := by simp
      smul_mem' := fun c y hy => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul] at *
        exact (mul_le_of_le_one_left' (hle c)).trans_lt hy }
  have h𝔮 : ∀ t, t ∈ 𝔮 ↔ w (ψ t) < 1 := fun _ => Iff.rfl
  refine ⟨𝔮, ⟨?_, fun {y z} h => ?_⟩, h𝔮⟩
  · rw [Ideal.ne_top_iff_one, h𝔮, map_one, map_one]
    exact lt_irrefl _
  · rw [h𝔮, map_mul, map_mul] at h
    rw [h𝔮, h𝔮]
    by_contra hc
    push Not at hc
    rw [le_antisymm (hle y) hc.1, le_antisymm (hle z) hc.2, one_mul] at h
    exact lt_irrefl _ h

/-- Let `S` be essentially of finite type over `R`, `φ : S → K` onto the valuation ring of `v`, and
`f : K → L` carry `v` to `w`. If the image of `ψ : A → L` lies in the valuation ring of `w` and
contains the images of `R` and of the generators of `S`, then `v g ≤ 1` iff `f g` is a fraction
`ψ c / ψ t` with `t` outside the prime `𝔮` of elements of value `< 1`. -/
private theorem valuation_le_one_iff_exists_mul_eq {R S K L A Γ : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.EssFiniteType R S] [Field K] [Field L] [CommRing A]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (w : Valuation L Γ) (f : K →+* L)
    (hw : ∀ g, w (f g) = v g) (φ : S →+* K) (hφ : ∀ g, v g ≤ 1 ↔ ∃ s, φ s = g) (ψ : A →+* L)
    (hψ : ∀ t, w (ψ t) ≤ 1) (𝔮 : Ideal A) (h𝔮 : ∀ t, t ∈ 𝔮 ↔ w (ψ t) < 1)
    (hR : ∀ r, f (φ (algebraMap R S r)) ∈ ψ.range)
    (hσ : ∀ s ∈ Algebra.EssFiniteType.finset R S, f (φ s) ∈ ψ.range) (g : K) :
    v g ≤ 1 ↔ ∃ c t, t ∉ 𝔮 ∧ f g * ψ t = ψ c := by
  refine ⟨fun hg => ?_, fun ⟨c, t, ht, hct⟩ => ?_⟩
  · obtain ⟨s, rfl⟩ := (hφ g).1 hg
    obtain ⟨_, ⟨c, rfl⟩, _, ⟨t, rfl⟩, ht, hct⟩ :=
      exists_mul_eq_of_essFiniteType w (f.comp φ)
        (fun s => (hw (φ s)).trans_le ((hφ _).2 ⟨s, rfl⟩)) ψ.range hR hσ s
    exact ⟨c, t, fun h => ((h𝔮 t).1 h).ne ht, hct⟩
  · calc v g = w (f g) * w (ψ t) := by
          rw [le_antisymm (hψ t) (not_lt.mp (mt (h𝔮 t).2 ht)), mul_one, hw]
      _ = w (ψ c) := by rw [← map_mul]; exact congrArg w hct
      _ ≤ 1 := hψ c

/-- Let `P` be a prime of the sections over an affine open `W` of an integral scheme whose point
lies in `W`. An element of the function field is the image of a germ at `P` iff it is a fraction
`c / t` of sections with `t ∉ P`. -/
private theorem exists_algebraMap_stalk_eq_iff {Y : Scheme.{w}} [IsIntegral Y] {W : Y.Opens}
    (hW : IsAffineOpen W) [Nonempty W] (P : PrimeSpectrum Γ(Y, W)) (hP : hW.fromSpec P ∈ W)
    (f : Y.functionField) :
    (∃ a : Y.presheaf.stalk (hW.fromSpec P), algebraMap _ Y.functionField a = f) ↔
      ∃ c t, t ∉ P.asIdeal ∧
        f * (Y.germToFunctionField W).hom t = (Y.germToFunctionField W).hom c := by
  let : Algebra Γ(Y, W) (Y.presheaf.stalk (hW.fromSpec P)) :=
    TopCat.Presheaf.algebra_section_stalk _ ⟨_, hP⟩
  have : IsLocalization P.asIdeal.primeCompl (Y.presheaf.stalk (hW.fromSpec P)) :=
    hW.isLocalization_stalk' P hP
  have := functionField_isScalarTower Y W ⟨_, hP⟩
  have hμ : ∀ t, algebraMap _ Y.functionField (algebraMap Γ(Y, W)
      (Y.presheaf.stalk (hW.fromSpec P)) t) = (Y.germToFunctionField W).hom t := fun t => by
    rw [← IsScalarTower.algebraMap_apply]; rfl
  have hmk : ∀ c (t : P.asIdeal.primeCompl), algebraMap _ Y.functionField
      (IsLocalization.mk' (Y.presheaf.stalk (hW.fromSpec P)) c t) *
        (Y.germToFunctionField W).hom t = (Y.germToFunctionField W).hom c :=
    fun c t => by rw [← hμ, ← hμ, ← map_mul, IsLocalization.mk'_spec]
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨⟨c, t⟩, rfl⟩ := IsLocalization.mk'_surjective P.asIdeal.primeCompl y
    exact ⟨c, t, t.2, hmk c t⟩
  · rintro ⟨c, t, ht, hf⟩
    refine ⟨IsLocalization.mk' _ c ⟨t, ht⟩,
      mul_right_cancel₀ (fun h => ht ?_) ((hmk _ _).trans hf.symm)⟩
    have h0 : t = 0 := (map_eq_zero_iff _ (Y.germToFunctionField_injective W)).1 h
    exact h0 ▸ P.asIdeal.zero_mem

/-- A morphism `f` maps the point of an affine open `W ≤ f⁻¹ U` cut out by a prime `P` of
`Γ(Y, W)` to `x ∈ U` as soon as `P` pulls back to the prime of `x`. -/
private theorem hom_fromSpec_eq_of_forall_mem_iff {X Y : Scheme.{w}} (f : Y ⟶ X) {U : X.Opens}
    (hU : IsAffineOpen U) {W : Y.Opens} (hW : IsAffineOpen W) (hWle : W ≤ f ⁻¹ᵁ U)
    (P : PrimeSpectrum Γ(Y, W)) {x : X} (hxU : x ∈ U)
    (h : ∀ s, (f.appLE U W hWle).hom s ∈ P.asIdeal ↔ s ∈ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) :
    f (hW.fromSpec P) = x := by
  have hqW : hW.fromSpec P ∈ W := hW.range_fromSpec.subset ⟨P, rfl⟩
  have h1 := IsAffineOpen.comap_primeIdealOf_appLE (f := f) U hU W hW hWle hqW
  have h2 : hU.primeIdealOf ⟨f (hW.fromSpec P), hWle hqW⟩ = hU.primeIdealOf ⟨x, hxU⟩ := by
    rw [← h1, hW.primeIdealOf_fromSpec P hqW]
    exact PrimeSpectrum.ext (Ideal.ext h)
  have := congrArg hU.fromSpec h2
  rwa [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf] at this

/-- The chart `Spec Γ(X, U)[ℐ(U)/a]` of the blow-up of `ℐ` at a nonzero `a` is nonempty. -/
private theorem nonempty_blowUpChartOpen {X : Scheme.{w}} [IsIntegral X] (ℐ : X.IdealSheafData)
    (U : X.affineOpens) [Nonempty (U : X.Opens)] (a : ℐ.ideal U) (ha : (a : Γ(X, U)) ≠ 0) :
    Nonempty (blowUpChartOpen ℐ U a).1 := by
  have hW : IsAffineOpen (blowUpChartOpen ℐ U a).1 := (blowUpChartOpen ℐ U a).2
  have : Nontrivial Γ(blowUp ℐ, (blowUpChartOpen ℐ U a).1) := by
    have : Nontrivial (Localization.Away (a : Γ(X, U))) := by
      have hinj := IsLocalization.injective (Localization.Away (a : Γ(X, U)))
        (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
      exact ⟨⟨_, _, hinj.ne zero_ne_one⟩⟩
    exact (blowUpChartRingIso ℐ U a).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  obtain ⟨p₀, hp₀⟩ := Ideal.exists_maximal Γ(blowUp ℐ, (blowUpChartOpen ℐ U a).1)
  exact ⟨⟨hW.fromSpec (show Spec _ from ⟨p₀, hp₀.isPrime⟩), hW.range_fromSpec.subset ⟨_, rfl⟩⟩⟩

/-- On the chart `Spec Γ(X, U)[J/a]` of the blow-up of `ℐ`, `J = ℐ(U)`, every section has value
at most `1` for the valuation `w` induced by `v`, if `v ≤ 1` on `Γ(X, U)` and `v ≤ v a` on `J`. -/
private theorem valuation_germToFunctionField_blowUpChart_le_one {X : Scheme.{w}} [IsIntegral X]
    (ℐ : X.IdealSheafData) [IsIntegral (blowUp ℐ)] [IsDominant (blowUpToBase ℐ)]
    (U : X.affineOpens) [Nonempty (U : X.Opens)] (a : ℐ.ideal U) (ha : (a : Γ(X, U)) ≠ 0)
    [Nonempty (blowUpChartOpen ℐ U a).1] {v : Valuation X.functionField ℤᵐ⁰}
    {w : Valuation (blowUp ℐ).functionField ℤᵐ⁰}
    (hw : ∀ g, w (functionFieldMap (blowUpToBase ℐ) g) = v g)
    (hle : ∀ s, v ((X.germToFunctionField U).hom s) ≤ 1)
    (hJ : ∀ y ∈ ℐ.ideal U,
      v ((X.germToFunctionField U).hom y) ≤ v ((X.germToFunctionField U).hom a))
    (t : Γ(blowUp ℐ, (blowUpChartOpen ℐ U a).1)) :
    w (((blowUp ℐ).germToFunctionField (blowUpChartOpen ℐ U a).1).hom t) ≤ 1 := by
  let ι := (X.germToFunctionField U).hom
  let χ := (blowUpChartMap ℐ U a).hom
  let ψ := ((blowUp ℐ).germToFunctionField (blowUpChartOpen ℐ U a).1).hom
  set fβ := functionFieldMap (blowUpToBase ℐ)
  have hψχ : ∀ s, ψ (χ s) = fβ (ι s) := fun s =>
    germToFunctionField_appLE (blowUpToBase ℐ) U _ (blowUpChartOpen_le ℐ U a) s
  obtain ⟨n, y, hy, hty⟩ := exists_mem_pow_mul_eq_blowUpChartMap ℐ U a t
  have h1 : ψ t * fβ (ι a) ^ n = fβ (ι y) := by
    have := congrArg ψ (hty : t * χ a ^ n = χ y)
    rwa [map_mul, map_pow, hψχ, hψχ] at this
  refine valuation_le_one_of_mul_pow_eq w ?_ h1 ?_
  · rw [map_ne_zero, ne_eq, ← map_zero ι]
    exact fun h => ha (X.germToFunctionField_injective U h)
  · rw [hw, hw]
    exact valuation_le_pow_of_mem_pow v ι hle _ _ hJ n y hy

/-- On the chart `Spec Γ(X, U)[ℐ(U)/a]` of the blow-up of `ℐ`, a function `z` with `a z ∈ ℐ(U)`
is a section. -/
private theorem mem_range_germToFunctionField_blowUpChart {X : Scheme.{w}} [IsIntegral X]
    (ℐ : X.IdealSheafData) [IsIntegral (blowUp ℐ)] [IsDominant (blowUpToBase ℐ)]
    (U : X.affineOpens) [Nonempty (U : X.Opens)] (a : ℐ.ideal U) (ha : (a : Γ(X, U)) ≠ 0)
    [Nonempty (blowUpChartOpen ℐ U a).1] {y : Γ(X, U)} (hy : y ∈ ℐ.ideal U) {z : X.functionField}
    (hz : (X.germToFunctionField U).hom y = (X.germToFunctionField U).hom a * z) :
    functionFieldMap (blowUpToBase ℐ) z ∈
      ((blowUp ℐ).germToFunctionField (blowUpChartOpen ℐ U a).1).hom.range := by
  let ι := (X.germToFunctionField U).hom
  let χ := (blowUpChartMap ℐ U a).hom
  let ψ := ((blowUp ℐ).germToFunctionField (blowUpChartOpen ℐ U a).1).hom
  set fβ := functionFieldMap (blowUpToBase ℐ)
  have hψχ : ∀ s, ψ (χ s) = fβ (ι s) := fun s =>
    germToFunctionField_appLE (blowUpToBase ℐ) U _ (blowUpChartOpen_le ℐ U a) s
  have hfa : fβ (ι a) ≠ 0 := by
    rw [map_ne_zero, ne_eq, ← map_zero ι]
    exact fun h => ha (X.germToFunctionField_injective U h)
  obtain ⟨t, ht⟩ := exists_mul_eq_blowUpChartMap_of_mem_pow ℐ U a (n := 1) (x := y)
    (by rwa [pow_one])
  have := congrArg ψ (ht : χ y = χ a ^ 1 * t)
  rw [pow_one, map_mul, hψχ, hψχ, hz, map_mul] at this
  exact ⟨t, (mul_left_cancel₀ hfa this).symm⟩

/-- On the blow-up of an ideal sheaf `ℐ` with `h₀ ∈ ℐ(U)`, `v ≤ v h₀` on `ℐ(U)` and
`h₀ φ(s) ∈ ℐ(U)` for the generators `s` of an algebra `S` whose image is the valuation ring of `v`,
the point of the chart `Spec Γ(X, U)[ℐ(U)/h₀]` cut out by `𝔪_v` lies over `x` and has the
valuation ring of `v` as local ring. -/
private theorem exists_blowUp_stalk_eq_integer_of_mem_ideal {k : Type w} [Field k]
    {X : Scheme.{w}} [IsIntegral X] [Algebra k X.functionField]
    {v : Valuation X.functionField ℤᵐ⁰} {S : Type w} [CommRing S] [Algebra k S]
    [Algebra.EssFiniteType k S] {φ : S →ₐ[k] X.functionField} (hφ : ∀ g, v g ≤ 1 ↔ g ∈ φ.range)
    {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] {x : X} (hxU : x ∈ U)
    (halg : ∀ r : k, ∃ c : Γ(X, U), X.germToFunctionField U c = algebraMap k X.functionField r)
    (hιle : ∀ a, v ((X.germToFunctionField U).hom a) ≤ 1)
    (hιlt : ∀ a, a ∈ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal ↔ v ((X.germToFunctionField U).hom a) < 1)
    {h₀ : Γ(X, U)} (hh₀0 : h₀ ≠ 0) {g : S → Γ(X, U)}
    (hg : ∀ s ∈ Algebra.EssFiniteType.finset k S,
      (X.germToFunctionField U).hom (g s) = (X.germToFunctionField U).hom h₀ * φ s)
    (ℐ : X.IdealSheafData) [IsIntegral (blowUp ℐ)] [IsDominant (blowUpToBase ℐ)]
    (hsurj : Function.Surjective (functionFieldMap (blowUpToBase ℐ)))
    (hh₀ : h₀ ∈ ℐ.ideal ⟨U, hU⟩)
    (hgℐ : ∀ s ∈ Algebra.EssFiniteType.finset k S, g s ∈ ℐ.ideal ⟨U, hU⟩)
    (hJ : ∀ y ∈ ℐ.ideal ⟨U, hU⟩,
      v ((X.germToFunctionField U).hom y) ≤ v ((X.germToFunctionField U).hom h₀)) :
    ∃ q : blowUp ℐ, blowUpToBase ℐ q = x ∧
      ∀ g' : X.functionField, v g' ≤ 1 ↔ ∃ a : (blowUp ℐ).presheaf.stalk q,
        algebraMap _ (blowUp ℐ).functionField a = functionFieldMap (blowUpToBase ℐ) g' := by
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  let ι : Γ(X, U) →+* X.functionField := (X.germToFunctionField U).hom
  set σ := Algebra.EssFiniteType.finset k S
  let U' : X.affineOpens := ⟨U, hU⟩
  let a : ℐ.ideal U' := ⟨h₀, hh₀⟩
  let W := blowUpChartOpen ℐ U' a
  have hW : IsAffineOpen W.1 := W.2
  have hWle : W.1 ≤ blowUpToBase ℐ ⁻¹ᵁ U := blowUpChartOpen_le ℐ U' a
  let χ : Γ(X, U) →+* Γ(blowUp ℐ, W.1) := (blowUpChartMap ℐ U' a).hom
  have : Nonempty W.1 := nonempty_blowUpChartOpen ℐ U' a hh₀0
  let ψ : Γ(blowUp ℐ, W.1) →+* (blowUp ℐ).functionField :=
    ((blowUp ℐ).germToFunctionField W.1).hom
  set fβ := functionFieldMap (blowUpToBase ℐ)
  have hψχ : ∀ s, ψ (χ s) = fβ (ι s) := fun s =>
    germToFunctionField_appLE (blowUpToBase ℐ) U W.1 hWle s
  let e := RingEquiv.ofBijective fβ ⟨fβ.injective, hsurj⟩
  let w : Valuation (blowUp ℐ).functionField ℤᵐ⁰ := v.comap e.symm.toRingHom
  have hw : ∀ g, w (fβ g) = v g := fun g => by
    simp only [w, Valuation.comap_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    exact congrArg v (e.symm_apply_apply g)
  have hTle : ∀ t, w (ψ t) ≤ 1 := valuation_germToFunctionField_blowUpChart_le_one ℐ U' a hh₀0
    hw hιle hJ
  have hR : ∀ r, (fβ.comp φ.toRingHom) (algebraMap k S r) ∈ ψ.range := by
    intro r
    obtain ⟨c, hc⟩ := halg r
    refine ⟨χ c, ?_⟩
    rw [hψχ]
    change fβ (ι c) = fβ (φ (algebraMap k S r))
    rw [φ.commutes]
    exact congrArg fβ hc
  have hσ : ∀ s ∈ σ, (fβ.comp φ.toRingHom) s ∈ ψ.range := fun s hs =>
    mem_range_germToFunctionField_blowUpChart ℐ U' a hh₀0
      (hgℐ s hs) (hg s hs)
  obtain ⟨𝔮, h𝔮p, h𝔮⟩ := exists_isPrime_mem_iff_valuation_lt_one w ψ hTle
  let P : PrimeSpectrum Γ(blowUp ℐ, W.1) := ⟨𝔮, h𝔮p⟩
  refine ⟨hW.fromSpec P, hom_fromSpec_eq_of_forall_mem_iff _ hU hW hWle P hxU fun s => ?_,
    fun g' => ?_⟩
  · rw [hιlt]
    change χ s ∈ 𝔮 ↔ _
    rw [h𝔮, hψχ, hw]
  · rw [exists_algebraMap_stalk_eq_iff hW P (hW.range_fromSpec.subset ⟨P, rfl⟩)]
    exact valuation_le_one_iff_exists_mul_eq (R := k) v w fβ hw φ.toRingHom
      (fun g => (hφ g).trans (AlgHom.mem_range φ)) ψ hTle 𝔮 h𝔮 hR hσ g'

/-- **The chart of the blow-up.** There are an affine open `U ∋ x` and a nonzero ideal
`J = (h₀, g₁, …, gₖ)` of `Γ(X, U)` such that, on the blow-up of any ideal sheaf restricting to `J`
on `U`, the point of the chart `Spec Γ(X, U)[J/h₀]` cut out by `𝔪_v` lies over `x` and has the
valuation ring of `v` as local ring. -/
private theorem exists_affineOpen_ideal_blowUp_stalk_eq_integer {k : Type w} [Field k]
    {X : Scheme.{w}} (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sX]
    {v : Valuation X.functionField ℤᵐ⁰} (hS : letI := functionFieldAlgebra sX
      ∃ (S : Type w) (_ : CommRing S) (_ : Algebra k S) (_ : Algebra.EssFiniteType k S)
        (φ : S →ₐ[k] X.functionField), ∀ g, v g ≤ 1 ↔ g ∈ φ.range) (x : X)
    (hle : ∀ a : X.presheaf.stalk x, v (algebraMap _ X.functionField a) ≤ 1)
    (hlt : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x),
      v (algebraMap _ X.functionField a) < 1)
    {g₀ : X.functionField} (hg₀ : v g₀ = WithZero.exp (-1)) :
    ∃ (U : X.affineOpens) (J : Ideal Γ(X, U)), x ∈ (U : X.Opens) ∧ J ≠ ⊥ ∧
      (∀ ℐ : X.IdealSheafData, ℐ.ideal U = J → x ∈ ℐ.support) ∧
      ∀ (ℐ : X.IdealSheafData), ℐ.ideal U = J → ∀ [IsIntegral (blowUp ℐ)]
        [IsDominant (blowUpToBase ℐ)], Function.Surjective (functionFieldMap (blowUpToBase ℐ)) →
        ∃ q : blowUp ℐ, blowUpToBase ℐ q = x ∧
          ∀ g : X.functionField, v g ≤ 1 ↔ ∃ a : (blowUp ℐ).presheaf.stalk q,
            algebraMap _ (blowUp ℐ).functionField a = functionFieldMap (blowUpToBase ℐ) g := by
  have : IsIntegral X := ‹AlgebraicGeometry.IsVariety k sX›.toIsIntegral
  let := functionFieldAlgebra sX
  obtain ⟨S, _, _, _, φ, hφ⟩ := hS
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  let ι : Γ(X, U) →+* X.functionField := (X.germToFunctionField U).hom
  have hιinj : Function.Injective ι := X.germToFunctionField_injective U
  have hιle : ∀ a, v (ι a) ≤ 1 := fun a => by
    rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) hxU]
    exact hle _
  have hιlt : ∀ a, a ∈ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal ↔ v (ι a) < 1 := by
    intro a
    rw [hU.primeIdealOf_eq_map_closedPoint]
    change X.presheaf.germ U x hxU a ∈ IsLocalRing.maximalIdeal _ ↔ _
    rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) hxU]
    exact ⟨hlt _, fun h => (IsLocalRing.mem_maximalIdeal _).2 <| mem_nonunits_iff.2 fun hu =>
      ne_of_lt h (Valuation.Integers.one_of_isUnit' (v := v) hu hle)⟩
  set σ := Algebra.EssFiniteType.finset k S
  obtain ⟨h₀, g, hh₀0, hh₀1, hg⟩ : ∃ (h₀ : Γ(X, U)) (g : S → Γ(X, U)), h₀ ≠ 0 ∧
      v (ι h₀) < 1 ∧ ∀ s ∈ σ, ι (g s) = ι h₀ * φ s :=
    exists_ne_zero_valuation_lt_one_mul_eq v hιle hg₀ φ σ
  let J : Ideal Γ(X, U) := Ideal.span (insert h₀ (g '' σ))
  have hJ : ∀ y ∈ J, v (ι y) ≤ v (ι h₀) :=
    valuation_le_of_mem_span_insert v ι hιle (σ := σ) (φ := φ)
      (fun s => (hφ (φ s)).2 ⟨s, rfl⟩) hg
  refine ⟨⟨U, hU⟩, J, hxU, ?_, ?_, ?_⟩
  · rw [ne_eq, Ideal.span_eq_bot]
    push Not
    exact ⟨h₀, Set.mem_insert _ _, hh₀0⟩
  · intro ℐ hℐ
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨U, hU⟩) hxU, hℐ,
      Scheme.mem_zeroLocus_iff]
    intro y hy hxy
    rw [Scheme.mem_basicOpen X y x hxU] at hxy
    have h1 := Valuation.Integers.one_of_isUnit' (v := v) hxy hle
    rw [Scheme.algebraMap_germ_eq_germToFunctionField] at h1
    exact (ne_of_lt ((hJ y hy).trans_lt hh₀1)) h1
  intro ℐ hℐ _ _ hsurj
  have hmemJ : ∀ y ∈ J, y ∈ ℐ.ideal ⟨U, hU⟩ := fun y hy => hℐ ▸ hy
  exact exists_blowUp_stalk_eq_integer_of_mem_ideal hφ hU hxU
    (exists_germToFunctionField_eq_algebraMap sX U) hιle hιlt hh₀0 hg ℐ hsurj
    (hmemJ _ (Ideal.subset_span (Set.mem_insert _ _)))
    (fun s hs => hmemJ _ (Ideal.subset_span (Set.mem_insert_of_mem _ ⟨s, hs, rfl⟩)))
    fun y hy => hJ y (hℐ ▸ hy)

/-- A dominant morphism which is an open immersion on a dense open is birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion {X Y : Scheme.{w}} (f : X ⟶ Y)
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
private theorem exists_isOpenImmersion_of_isBirationalMorphism {X Y : Scheme.{w}} {f : X ⟶ Y}
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
private theorem isBirationalMorphism_comp {X Y Z : Scheme.{w}} [IrreducibleSpace X]
    {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsBirationalMorphism f) (hg : IsBirationalMorphism g) :
    IsBirationalMorphism (f ≫ g) := by
  have := hf.isDominant
  have := hg.isDominant
  obtain ⟨U₁, hU₁, h₁⟩ := exists_isOpenImmersion_of_isBirationalMorphism hf
  obtain ⟨U₂, hU₂, h₂⟩ := exists_isOpenImmersion_of_isBirationalMorphism hg
  let U : X.Opens := U₁ ⊓ f ⁻¹ᵁ U₂
  have hne : (U : Set X).Nonempty := by
    obtain ⟨x₀⟩ := (IrreducibleSpace.isIrreducible_univ X).nonempty
    have : Nonempty Y := ⟨f x₀⟩
    have hd : Dense (f '' U₁) := f.denseRange.dense_image f.continuous hU₁
    obtain ⟨y, hy₂, x, hx₁, rfl⟩ := (hU₂.inter_of_isOpen_left hd U₂.2).nonempty
    exact ⟨x, hx₁, hy₂⟩
  have hU : Dense (U : Set X) := U.2.dense hne
  have hle : U ≤ f ⁻¹ᵁ U₂ := inf_le_right
  have hle₁ : U ≤ U₁ := inf_le_left
  have hres : IsOpenImmersion (f.resLE U₂ U hle) := by
    have : f.resLE U₂ U hle ≫ U₂.ι = X.homOfLE hle₁ ≫ (U₁.ι ≫ f) := by
      rw [Scheme.Hom.resLE_comp_ι, ← Category.assoc, Scheme.homOfLE_ι]
    have : IsOpenImmersion (f.resLE U₂ U hle ≫ U₂.ι) := by
      rw [this]
      infer_instance
    exact IsOpenImmersion.of_comp _ U₂.ι
  have : IsOpenImmersion (U.ι ≫ f ≫ g) := by
    rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι f hle, Category.assoc]
    infer_instance
  exact isBirationalMorphism_of_isOpenImmersion (f ≫ g) U hU

/-- Transport of "the local ring at `ν z` is a given subset of `k(X)`" along a morphism `ν`
which is an isomorphism on local rings at `z`. -/
private theorem forall_iff_exists_stalk_comp {X Y Z : Scheme.{w}} [IsIntegral X] [IsIntegral Y]
    [IsIntegral Z] (ν : Z ⟶ Y) (β : Y ⟶ X) [IsDominant ν] [IsDominant β] [IsDominant (ν ≫ β)]
    (z : Z) [IsIso (ν.stalkMap z)] (S : Set X.functionField)
    (hq : ∀ g : X.functionField, g ∈ S ↔
      ∃ a : Y.presheaf.stalk (ν z), algebraMap _ Y.functionField a = functionFieldMap β g) :
    ∀ g : X.functionField, g ∈ S ↔
      ∃ a : Z.presheaf.stalk z, algebraMap _ Z.functionField a = functionFieldMap (ν ≫ β) g := by
  intro g
  rw [hq g]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨(ν.stalkMap z).hom a, ?_⟩
    rw [← MMP.Mori.functionFieldMap_algebraMap_stalk, ha,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
  · rintro ⟨b, hb⟩
    refine ⟨(inv (ν.stalkMap z)).hom b, (functionFieldMap ν).injective ?_⟩
    rw [MMP.Mori.functionFieldMap_algebraMap_stalk,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply, ← hb]
    congr 1
    exact congrArg (fun φ => φ.hom b) (IsIso.inv_hom_id (ν.stalkMap z))

/-- Two equivalent `ℤᵐ⁰`-valued valuations of a field which both take the value `exp (-1)` are
equal. -/
private theorem eq_of_isEquiv_of_exp_neg_one {K : Type*} [Field K] {w₁ w₂ : Valuation K ℤᵐ⁰}
    (h : w₁.IsEquiv w₂) (h₁ : ∃ a, w₁ a = WithZero.exp (-1))
    (h₂ : ∃ a, w₂ a = WithZero.exp (-1)) : w₁ = w₂ := by
  obtain ⟨ϖ, hϖ⟩ := h₁
  obtain ⟨ϖ', hϖ'⟩ := h₂
  have hpow : ∀ (w : Valuation K ℤᵐ⁰) (c : ℤ), w ϖ = WithZero.exp c → ∀ n : ℤ,
      w (ϖ ^ n) = WithZero.exp (c * n) := by
    intro w c hc n
    rw [map_zpow₀, hc, ← WithZero.exp_zsmul, smul_eq_mul, mul_comm]
  have hw₂ϖ : w₂ ϖ ≠ 0 := by
    rw [ne_eq, ← h.eq_zero, hϖ]; exact WithZero.exp_ne_zero
  set a := WithZero.log (w₂ ϖ)
  have ha : w₂ ϖ = WithZero.exp a := (WithZero.exp_log hw₂ϖ).symm
  have hw₁ϖ' : w₁ ϖ' ≠ 0 := by
    rw [ne_eq, h.eq_zero, hϖ']; exact WithZero.exp_ne_zero
  set b := WithZero.log (w₁ ϖ')
  have hb : w₁ ϖ' = WithZero.exp b := (WithZero.exp_log hw₁ϖ').symm
  have hab : w₂ ϖ' = WithZero.exp (a * -b) := by
    rw [← hpow w₂ a ha]
    exact (h.eq_iff).mp (by rw [hb, hpow w₁ (-1) hϖ]; congr 1; ring)
  rw [hϖ', WithZero.exp_inj] at hab
  have ha0 : a < 0 := by
    have : w₂ ϖ < 1 := (Valuation.isEquiv_iff_val_lt_one.mp h).mp
      (by rw [hϖ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
    rwa [ha, ← WithZero.exp_zero, WithZero.exp_lt_exp] at this
  have ha1 : a = -1 := by
    have : a * b = 1 := by linarith
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' this with h | h <;> omega
  ext g
  by_cases hg : g = 0
  · simp [hg]
  have hg1 : w₁ g ≠ 0 := by simp [hg]
  set m := WithZero.log (w₁ g)
  have hm : w₁ g = WithZero.exp m := (WithZero.exp_log hg1).symm
  have : w₂ g = w₂ (ϖ ^ (-m)) :=
    (h.eq_iff).mp (by rw [hm, hpow w₁ (-1) hϖ]; congr 1; ring)
  rw [this, hpow w₂ a ha, hm, ha1]; congr 1; ring

/-- A divisor of the function field takes the value `exp (-1)`. -/
private theorem IsDivisorOfFunctionField.exists_eq_exp_neg_one {k : Type w} [Field k]
    {X : Scheme.{w}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] {v : Valuation X.functionField ℤᵐ⁰}
    (hv : IsDivisorOfFunctionField k sX v) : ∃ g, v g = WithZero.exp (-1) := by
  obtain ⟨Y, sY, hY, E, hE⟩ := hv
  have : IsIntegral Y := hY.1.toIsIntegral
  have : IsNormal Y := hY.2
  have : IsLocallyNoetherian Y :=
    haveI := hY.1.toLocallyOfFiniteType
    LocallyOfFiniteType.isLocallyNoetherian sY
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra sY
  obtain ⟨e, rfl⟩ := hE
  have := E.isDiscreteValuationRing_localRing
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible E.localRing
  refine ⟨e.symm (algebraMap E.localRing Y.functionField ϖ), ?_⟩
  rw [Valuation.comap_apply]
  simp only [RingHom.coe_coe, AlgEquiv.apply_symm_apply]
  exact E.divisorialValuation_algebraMap_of_irreducible hϖ

/-- If the local ring of `Z` at `z` is, inside `k(X)`, the valuation ring of a valuation taking
the value `exp (-1)`, it is not a field. -/
private theorem not_isField_stalk_of_forall_le_one_iff {X Z : Scheme.{w}} [IsIntegral X]
    [IsIntegral Z] (h : Z ⟶ X) [IsDominant h] (v : Valuation X.functionField ℤᵐ⁰) (z : Z)
    (hz : ∀ g : X.functionField, v g ≤ 1 ↔
      ∃ a : Z.presheaf.stalk z, algebraMap _ Z.functionField a = functionFieldMap h g)
    {g₀ : X.functionField} (hg₀ : v g₀ = WithZero.exp (-1)) :
    ¬ IsField (Z.presheaf.stalk z) := by
  intro hF
  obtain ⟨a, ha⟩ := (hz g₀).1 (by rw [hg₀, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, map_eq_zero, ← v.zero_iff, hg₀] at ha
    exact WithZero.exp_ne_zero ha
  obtain ⟨b, hb⟩ := hF.mul_inv_cancel ha0
  have hb' : v g₀⁻¹ ≤ 1 := (hz _).2 ⟨b, by
    rw [map_inv₀, ← ha]
    exact eq_inv_of_mul_eq_one_right (by rw [← map_mul, hb, map_one])⟩
  rw [map_inv₀, hg₀, ← WithZero.exp_neg, neg_neg, ← WithZero.exp_zero, WithZero.exp_le_exp] at hb'
  omega

/-- **The assembly step.** On a normal locally noetherian integral scheme `Z` dominating `X`, a
point `z` whose local ring is, inside `k(X)`, the valuation ring of a valuation `v` of `k(X)`
taking the value `exp (-1)`, is the generic point of a prime divisor `F` with `ord_F = v`. -/
private theorem exists_primeDivisor_valuationOver_eq {X : Scheme.{w}} [IsIntegral X]
    {v : Valuation X.functionField ℤᵐ⁰} {g₀ : X.functionField}
    (hg₀ : v g₀ = WithZero.exp (-1)) {Z : Scheme.{w}} [IsIntegral Z]
    [IsLocallyNoetherian Z] [IsNormal Z] (h : Z ⟶ X) [IsDominant h]
    (hh : Function.Bijective (functionFieldMap h)) (z : Z)
    (hz : ∀ g : X.functionField, v g ≤ 1 ↔
        ∃ a : Z.presheaf.stalk z, algebraMap _ Z.functionField a = functionFieldMap h g) :
    ∃ F : MMP.Mori.PrimeDivisor Z, F.genericPoint = z ∧ F.valuationOver h = v := by
  have := valuationRing_stalk_of_forall_le_one_iff h hh v z hz
  have hnf := not_isField_stalk_of_forall_le_one_iff h v z hz hg₀
  have : IsDiscreteValuationRing (Z.presheaf.stalk z) :=
    ((IsDiscreteValuationRing.TFAE (Z.presheaf.stalk z) hnf).out 1 2).mpr ‹_›
  have hcoh : Order.coheight z = 1 := by
    have h1 := ringKrullDim_stalk_eq_coheight z
    rw [IsDiscreteValuationRing.ringKrullDim_eq_one] at h1
    exact_mod_cast h1.symm
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne z hcoh,
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne z hcoh, ?_⟩
  set F : MMP.Mori.PrimeDivisor Z := AlgebraicGeometry.PrimeDivisor.ofCoheightOne z hcoh
  have hF : F.genericPoint = z := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne z hcoh
  have hrange : ∀ r : Z.functionField,
      r ∈ (algebraMap F.localRing Z.functionField).range ↔
        ∃ a : Z.presheaf.stalk z, algebraMap _ Z.functionField a = r := by
    intro r
    change (∃ a : Z.presheaf.stalk F.genericPoint, _) ↔ _
    clear_value F
    subst hF
    rfl
  apply eq_of_isEquiv_of_exp_neg_one
  · refine Valuation.isEquiv_iff_val_le_one.mpr fun {g} => ?_
    rw [PrimeDivisor.valuationOver_apply, PrimeDivisor.divisorialValuation_le_one_iff, hrange,
      hz g]
  · have := F.isDiscreteValuationRing_localRing
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible F.localRing
    obtain ⟨g, hg⟩ := hh.2 (algebraMap F.localRing Z.functionField ϖ)
    refine ⟨g, ?_⟩
    rw [PrimeDivisor.valuationOver_apply, hg]
    exact F.divisorialValuation_algebraMap_of_irreducible hϖ
  · exact ⟨g₀, hg₀⟩

/-! ### Ideal sheaves and closed immersions -/

/-- On an integral scheme, the generic point lies outside the support of a nonzero ideal
sheaf. -/
private theorem genericPoint_notMem_support {X : Scheme.{u}} [IsIntegral X]
    {I : X.IdealSheafData} (hI : I ≠ ⊥) : genericPoint X ∉ (I.support : Set X) := by
  intro h
  apply hI
  have h1 : (⊤ : Closeds X) ≤ I.support := fun y _ =>
    (genericPoint_specializes y).mem_closed I.support.isClosed h
  have h2 := Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp h1
  rw [Scheme.IdealSheafData.vanishingIdeal_top, Scheme.nilradical_eq_bot] at h2
  exact le_bot_iff.mp h2

/-- The direct image `𝒥` in `X` of a nonzero ideal sheaf `ℐ` of a prime divisor `P` is nonzero,
meets `P` exactly in the support of `ℐ`, misses the generic point of `P`, and is supported in
`P`. -/
private theorem map_subschemeι_support {X : Scheme.{u}} (P : Mori.PrimeDivisor X)
    {ℐ : P.idealSheaf.subscheme.IdealSheafData} (hℐ : ℐ ≠ ⊥) :
    ℐ.map P.idealSheaf.subschemeι ≠ ⊥ ∧
      (∀ y, P.idealSheaf.subschemeι y ∈ ((ℐ.map P.idealSheaf.subschemeι).support : Set X) ↔
        y ∈ (ℐ.support : Set _)) ∧
      P.genericPoint ∉ ((ℐ.map P.idealSheaf.subschemeι).support : Set X) ∧
      ((ℐ.map P.idealSheaf.subschemeι).support : Set X) ⊆ P.support := by
  have := P.integral
  set j := P.idealSheaf.subschemeι
  have hj : (ℐ.map j).comap j = ℐ := Scheme.IdealSheafData.comap_map_of_isClosedImmersion ℐ j
  have hmem : ∀ y, j y ∈ ((ℐ.map j).support : Set X) ↔ y ∈ (ℐ.support : Set _) := fun y => by
    conv_rhs => rw [← hj]
    rw [Scheme.IdealSheafData.support_comap]
    rfl
  refine ⟨fun h => hℐ (by rw [← hj, h, Scheme.IdealSheafData.comap_bot]), hmem, ?_, ?_⟩
  · rw [show P.genericPoint = j (genericPoint _) from rfl, hmem]
    exact genericPoint_notMem_support hℐ
  · have hPsupp : P.support = Set.range j := P.idealSheaf.range_subschemeι.symm
    rw [Scheme.IdealSheafData.support_map, Closeds.coe_closure, hPsupp]
    exact closure_minimal (Set.image_subset_range _ _) j.isClosedEmbedding.isClosed_range

/-- A morphism sending the generic point of an irreducible scheme to the generic point of an
irreducible scheme is dominant. -/
private theorem isDominant_of_map_genericPoint {X Y : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (f : X ⟶ Y) (hf : f (genericPoint X) = genericPoint Y) :
    IsDominant f := by
  refine ⟨?_⟩
  rw [DenseRange, dense_iff_closure_eq]
  apply Set.eq_univ_of_univ_subset
  rw [← (genericPoint_spec Y).def]
  exact closure_mono (Set.singleton_subset_iff.mpr ⟨_, hf⟩)

/-- For a separated dominant morphism of integral schemes inducing an isomorphism of function
fields, the generic point is the only point over the generic point. -/
private theorem eq_genericPoint_of_map_eq_genericPoint {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) [IsSeparated f] [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) {x : X} (hx : f x = genericPoint Y) :
    x = genericPoint X := by
  have h1 := MMP.Positivity.map_genericPoint_eq_of_isDominant f
  have : ValuationRing (Y.presheaf.stalk (f (genericPoint X))) := by
    rw [h1]
    exact (inferInstance : ValuationRing Y.functionField)
  have : ValuationRing (Y.presheaf.stalk (f x)) := by
    rw [hx]
    exact (inferInstance : ValuationRing Y.functionField)
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hf (genericPoint X)
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hf x
  exact (MMP.Positivity.eq_of_isIso_stalkMap f hf (hx.trans h1.symm)).symm

/-- **Birationality onto the image, read on stalks.** Let `σ : Z ⟶ W` be a dominant morphism of
integral schemes and `σ ≫ j = i ≫ f`, with `i` surjective on stalks and `f` surjective on the
stalk at the image of the generic point of `Z`. Then `σ` induces a surjection of function
fields. -/
private theorem functionFieldMap_surjective_of_comp_eq {Z W Y X : Scheme.{u}} [IsIntegral Z]
    [IsIntegral W] (σ : Z ⟶ W) [IsDominant σ] (i : Z ⟶ Y) (j : W ⟶ X) (f : Y ⟶ X)
    [SurjectiveOnStalks i] (hσ : σ ≫ j = i ≫ f)
    (hf : Function.Surjective (f.stalkMap (i (genericPoint Z)))) :
    Function.Surjective (functionFieldMap σ) := by
  have key : Function.Surjective (σ.stalkMap (genericPoint Z)) := by
    have hif : Function.Surjective ((i ≫ f).stalkMap (genericPoint Z)) := by
      rw [Scheme.Hom.stalkMap_comp]
      intro z
      obtain ⟨y, rfl⟩ := i.stalkMap_surjective _ z
      obtain ⟨w, rfl⟩ := hf y
      exact ⟨w, rfl⟩
    have hsj : Function.Surjective ((σ ≫ j).stalkMap (genericPoint Z)) := by
      rw [hσ]; exact hif
    rw [Scheme.Hom.stalkMap_comp] at hsj
    intro z
    obtain ⟨w, hw⟩ := hsj z
    exact ⟨_, hw⟩
  unfold functionFieldMap
  simp only [CommRingCat.hom_comp, RingHom.coe_comp]
  exact key.comp (ConcreteCategory.bijective_of_isIso _).2

/-! ### Effective Cartier divisors -/

/-- The inverse image of an effective Cartier divisor along a dominant morphism of integral
schemes is an effective Cartier divisor. -/
private theorem isEffectiveCartierDivisor_comap {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (g : Y ⟶ X) [IsDominant g] {I : X.IdealSheafData}
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) :
    Stacks.Divisors.IsEffectiveCartierDivisor (I.comap g) := by
  rw [Stacks.CartierAffineLocalConverse.isEffectiveCartierDivisor_iff_nonZeroDivisor] at hI ⊢
  intro y
  obtain ⟨V, hgyV, t, ht, hVt⟩ := hI (g y)
  obtain ⟨W, hW, hyW, hWV⟩ :=
    exists_isAffineOpen_mem_and_subset (show y ∈ g ⁻¹ᵁ (V : X.Opens) from hgyV)
  have hWV' : W ≤ g ⁻¹ᵁ (V : X.Opens) := hWV
  refine ⟨⟨W, hW⟩, hyW, (g.appLE V W hWV').hom t, ?_,
    Stacks.IdealSheaf.ideal_comap_eq_span I g V ⟨W, hW⟩ hWV' hVt⟩
  have : Nonempty W := ⟨⟨y, hyW⟩⟩
  have : Nonempty (V : X.Opens) := ⟨⟨g y, hgyV⟩⟩
  apply mem_nonZeroDivisors_of_ne_zero
  intro h0
  have h1 := germToFunctionField_appLE g V W hWV' t
  rw [h0, map_zero, eq_comm, map_eq_zero_iff _ (functionFieldMap g).injective] at h1
  exact nonZeroDivisors.ne_zero ht
    (X.germToFunctionField_injective V (by rw [h1, map_zero]))

/-- **Krull's principal ideal theorem for an effective Cartier divisor.** Every point of the
support of an effective Cartier divisor on a locally noetherian scheme lies on a prime divisor
contained in that support. -/
private theorem exists_primeDivisor_mem_support_subset {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    {I : Y.IdealSheafData} (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) {y : Y}
    (hy : y ∈ (I.support : Set Y)) :
    ∃ E : Mori.PrimeDivisor Y, y ∈ E.support ∧ E.support ⊆ (I.support : Set Y) := by
  have hy' : y ∈ Set.range I.subschemeι := by rw [I.range_subschemeι]; exact hy
  obtain ⟨y', rfl⟩ := hy'
  obtain ⟨Z, hZ, hyZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    ({y'} : Set I.subscheme) isIrreducible_singleton
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents Z hZ)
  have hdim := ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor I hI ξ ⟨⟨Z, hZ⟩, hξ⟩
  rw [ringKrullDim_stalk_eq_coheight] at hdim
  have hcoh : Order.coheight (I.subschemeι ξ) = 1 := by exact_mod_cast hdim
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh, ?_, ?_⟩
  · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
    have h1 : ξ ⤳ y' := by
      rw [specializes_iff_mem_closure, hξ.def]
      exact hyZ rfl
    exact specializes_iff_mem_closure.mp (h1.map I.subschemeι.continuous)
  · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
    refine closure_minimal (Set.singleton_subset_iff.mpr ?_) I.support.isClosed
    rw [← I.range_subschemeι]
    exact ⟨ξ, rfl⟩

/-! ### Prime divisors in a proper closed subset -/

/-- On an irreducible scheme, a generization of a point of coheight one is that point or the
generic point. -/
private theorem eq_or_eq_genericPoint_of_specializes {Y : Scheme.{u}} [IrreducibleSpace Y]
    {a b : Y} (hb : Order.coheight b = 1) (h : a ⤳ b) : a = b ∨ a = genericPoint Y := by
  by_cases hab : a = b
  · exact Or.inl hab
  right
  have hlt : b < a := lt_of_le_not_ge (Scheme.le_iff_specializes.mpr h) fun hle =>
    hab (h.antisymm (Scheme.le_iff_specializes.mp hle)).eq
  have h1 := Order.coheight_add_one_le hlt
  rw [hb] at h1
  have h0 : Order.coheight a = 0 := by
    have hne : Order.coheight a ≠ ⊤ := fun ht => by simp [ht] at h1
    exact Order.lt_one_iff.mp ((ENat.add_one_le_iff hne).mp h1)
  have hmax : IsMax a := Order.coheight_eq_zero.mp h0
  exact ((genericPoint_specializes a).antisymm (Scheme.le_iff_specializes.mp
    (hmax (Scheme.le_iff_specializes.mpr (genericPoint_specializes a))))).eq.symm

/-- Two points of coheight one, one specializing to the other, are equal. -/
private theorem eq_of_specializes_of_coheight_eq_one {Y : Scheme.{u}} {a b : Y}
    (ha : Order.coheight a = 1) (hb : Order.coheight b = 1) (h : a ⤳ b) : a = b := by
  by_contra hab
  have hlt : b < a := lt_of_le_not_ge (Scheme.le_iff_specializes.mpr h) fun hle =>
    hab (h.antisymm (Scheme.le_iff_specializes.mp hle)).eq
  have h1 := Order.coheight_add_one_le hlt
  rw [ha, hb] at h1
  exact absurd h1 (by norm_num)

/-- An integral noetherian scheme has only finitely many prime divisors inside a closed subset
not containing the generic point. -/
private theorem finite_setOf_support_subset_of_isClosed {Y : Scheme.{u}} [IsIntegral Y]
    [NoetherianSpace Y] {Z : Set Y} (hZ : IsClosed Z) (hne : genericPoint Y ∉ Z) :
    {Q : Mori.PrimeDivisor Y | Q.support ⊆ Z}.Finite := by
  refine Set.Finite.of_finite_image ((Aux.finite_and_cover_componentsOf hZ).1.subset ?_)
    fun P _ Q _ h => primeDivisor_eq_of_support_eq h
  rintro - ⟨Q, hQ, rfl⟩
  refine ⟨⟨?_, hQ⟩, fun W hW hle => ?_⟩
  · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isIrreducible_singleton.closure
  · obtain ⟨w, hw⟩ := QuasiSober.sober hW.1.closure isClosed_closure
    have hηW : Q.genericPoint ∈ closure W := subset_closure (hle (genericPoint_mem_support Q))
    rw [← hw.def] at hηW
    rcases eq_or_eq_genericPoint_of_specializes Q.coheight_genericPoint
      (specializes_iff_mem_closure.mpr hηW) with h | h
    · calc W ⊆ closure W := subset_closure
        _ = closure {w} := hw.def.symm
        _ = Q.support := by
          rw [h]; exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure Q).symm
    · exfalso
      apply hne
      have : w ∈ closure W := by rw [← hw.def]; exact subset_closure rfl
      rw [← h]
      exact closure_minimal hW.2 hZ this

/-- A point of a prime divisor `P` other than its generic point has coheight at least two. -/
private theorem two_le_coheight_of_mem_support {X : Scheme.{u}} {P : Mori.PrimeDivisor X} {y : X}
    (hy : y ∈ P.support) (hne : y ≠ P.genericPoint) : 2 ≤ Order.coheight y := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hy
  have hsp : P.genericPoint ⤳ y := specializes_iff_mem_closure.mpr hy
  have hlt : y < P.genericPoint :=
    lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hsp) fun hle =>
      hne (hsp.antisymm (Scheme.le_iff_specializes.mp hle)).eq.symm
  have := Order.coheight_add_one_le hlt
  rw [P.coheight_genericPoint] at this
  exact (by norm_num : (2 : ℕ∞) = 1 + 1) ▸ this

/-- A prime divisor of a prime divisor `S'` of `Y` whose generic point lies on another prime
divisor `E` of `Y` is an irreducible component of `E ∩ S'`. -/
private theorem maximal_image_support {Y : Scheme.{u}} {E S' : Mori.PrimeDivisor Y} (hES : E ≠ S')
    (C : Mori.PrimeDivisor S'.idealSheaf.subscheme)
    (hCE : S'.idealSheaf.subschemeι C.genericPoint ∈ E.support) :
    Maximal (fun W : Set Y => IsIrreducible W ∧ W ⊆ E.support ∩ S'.support)
      (S'.idealSheaf.subschemeι '' C.support) := by
  have := S'.integral
  set ι := S'.idealSheaf.subschemeι with hι
  have hrange : Set.range ι = S'.support := S'.idealSheaf.range_subschemeι
  have himg : ι '' C.support = closure {ι C.genericPoint} := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      ← ι.isClosedEmbedding.closure_image_eq, Set.image_singleton]
  have hS'cl : IsClosed S'.support := by rw [← hrange]; exact ι.isClosedEmbedding.isClosed_range
  have hEcl : IsClosed E.support := E.idealSheaf.support.isClosed
  rw [himg]
  refine ⟨⟨isIrreducible_singleton.closure, closure_minimal (Set.singleton_subset_iff.mpr
    ⟨hCE, by rw [← hrange]; exact ⟨_, rfl⟩⟩) (hEcl.inter hS'cl)⟩, fun W hW hle => ?_⟩
  obtain ⟨w, hw⟩ := QuasiSober.sober hW.1.closure isClosed_closure
  have hwW : w ∈ closure W := by rw [← hw.def]; exact subset_closure rfl
  have hWS' : closure W ⊆ S'.support :=
    closure_minimal (hW.2.trans Set.inter_subset_right) hS'cl
  have hWE : closure W ⊆ E.support := closure_minimal (hW.2.trans Set.inter_subset_left) hEcl
  obtain ⟨w', rfl⟩ : w ∈ Set.range ι := by rw [hrange]; exact hWS' hwW
  have hcW : ι C.genericPoint ∈ closure {ι w'} := by
    rw [hw.def]; exact subset_closure (hle (subset_closure rfl))
  have hsp : w' ⤳ C.genericPoint :=
    (ι.isClosedEmbedding.isInducing.specializes_iff).mp (specializes_iff_mem_closure.mpr hcW)
  rcases eq_or_eq_genericPoint_of_specializes C.coheight_genericPoint hsp with h | h
  · rw [← h, hw.def]; exact subset_closure
  · exfalso
    apply hES
    have hS'E : S'.genericPoint ∈ E.support := by
      rw [show S'.genericPoint = ι w' by rw [h]; rfl]; exact hWE hwW
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hS'E
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (eq_of_specializes_of_coheight_eq_one E.coheight_genericPoint S'.coheight_genericPoint
        (specializes_iff_mem_closure.mpr hS'E))

/-! ### Divisors over a variety and strict transforms -/

/-- The valuation of a divisor over a variety is a divisor of its function field. -/
private theorem isDivisorOfFunctionField_valuation {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] (D : DivisorOver k sX) :
    IsDivisorOfFunctionField k sX D.valuation := by
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have := D.isDominant
  refine ⟨D.Y, D.f ≫ sX, D.isNormalVariety, D.E, ?_⟩
  let := MMP.Mori.functionFieldAlgebra sX
  let := MMP.Mori.functionFieldAlgebra (D.f ≫ sX)
  exact ⟨MMP.Mori.functionFieldAlgEquiv sX D.f D.isBirationalMorphism.functionFieldMap_bijective,
    Valuation.ext fun t => rfl⟩

/-- A divisor `D` with coefficients in a canonically ordered monoid has `φ_* D ≥ D(P)` at `φ(P)`
when `P` is the only prime divisor sent to `φ(P)`. -/
private theorem mapPrimeDivisors_apply_of_forall_eq {X Y : Scheme.{u}} {R : Type*}
    [AddCommMonoid R] {φ : Mori.PrimeDivisor X → Option (Mori.PrimeDivisor Y)}
    {P : Mori.PrimeDivisor X} {E : Mori.PrimeDivisor Y} (hP : φ P = some E)
    (h : ∀ Q, φ Q = some E → Q = P) (D : DivisorWithCoeffs R X) :
    DivisorWithCoeffs.mapPrimeDivisors φ D E = D P := by
  classical
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' hD hD' => rw [map_add, Finsupp.add_apply, Finsupp.add_apply, hD, hD']
  | single Q r =>
    rw [DivisorWithCoeffs.mapPrimeDivisors_single]
    by_cases hQ : Q = P
    · subst hQ
      rw [hP]
      simp
    · rw [Finsupp.single_eq_of_ne' hQ]
      rcases hφ : φ Q with _ | E'
      · rfl
      · have hne : E' ≠ E := fun he => hQ (h Q (by rw [hφ, he]))
        exact Finsupp.single_eq_of_ne' hne

/-- **The strict transform of a prime divisor.** For a proper birational morphism `f : Y ⟶ X`
from a variety onto a normal variety, every prime divisor `P` of `X` has a strict transform
`S'` with `f(η_{S'}) = η_P`, at whose generic point `f` is an isomorphism on local rings. -/
private theorem exists_transformPrimeDivisor_inverse_eq_some {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (f : Y ⟶ X)
    (hY : Mori.IsVariety k (f ≫ sX)) [IsProper f] (hf : IsBirationalMorphism f)
    (P : Mori.PrimeDivisor X) :
    ∃ S' : Mori.PrimeDivisor Y,
      Mori.RationalMap.transformPrimeDivisor (Mori.RationalMap.IsBirational.inverse hf) P =
        some S' ∧ f S'.genericPoint = P.genericPoint ∧ IsIso (f.stalkMap S'.genericPoint) := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  have : IsNormal X := hX.2
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsDominant f := hf.isDominant
  obtain ⟨x', hx', hc, -, -⟩ := MMP.Intersection.exists_preimage_of_coheight_eq_one f
    hf.functionFieldMap_bijective P.coheight_genericPoint
  have hS'g := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x' hc
  have hfS : f (AlgebraicGeometry.PrimeDivisor.ofCoheightOne x' hc).genericPoint =
      P.genericPoint := by rw [hS'g, hx']
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne x' hc,
    transformPrimeDivisor_inverse_eq_some_of_genericPoint_eq hX f hY hf hfS, hfS, ?_⟩
  have := P.isDiscreteValuationRing_localRing
  have : ValuationRing (X.presheaf.stalk
      (f (AlgebraicGeometry.PrimeDivisor.ofCoheightOne x' hc).genericPoint)) := by
    rw [hfS]; infer_instance
  exact MMP.Positivity.isIso_stalkMap_of_valuationRing f hf.functionFieldMap_bijective _

/-- A divisor `(Y, f, E)` over a variety of dimension `n` is exceptional exactly when
`f(η_E)` has coheight at least two. -/
private theorem isExceptional_iff_two_le_coheight {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX] {n : ℕ}
    (hn : topologicalKrullDim X = n) (D : ProperDivisorOver k sX) :
    D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  unfold ProperDivisorOver.IsExceptional
  rw [D.center_eq_toDivisorOver_center, D.toDivisorOver.center_eq_closure_genericPoint, hn]
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX
    (D.f D.E.genericPoint)
  rw [hn] at h
  exact withBot_add_two_le_iff h

/-- **Exceptional divisors over a centre of codimension at least two.** Let `f : Y ⟶ X` be a
proper birational morphism from a normal variety, and `𝒥` an ideal sheaf of `X` whose support lies
in a prime divisor `P` but misses its generic point, with `𝒥 𝒪_Y` invertible. Every point of `Y`
over `V(𝒥)` lies on a prime divisor `E` of `Y` exceptional over `X`, and `f(η_E)` has coheight at
least two. -/
private theorem exists_isExceptionalPrimeDivisor_mem_support {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} (hX : Mori.IsVariety k sX) {f : Y ⟶ X}
    (hY : IsNormalVariety k (f ≫ sX)) [IsProper f] (hf : IsBirationalMorphism f)
    {𝒥 : X.IdealSheafData} (hcart : Stacks.Divisors.IsEffectiveCartierDivisor (𝒥.comap f))
    {P : Mori.PrimeDivisor X} (h𝒥P : (𝒥.support : Set X) ⊆ P.support)
    (hP𝒥 : P.genericPoint ∉ (𝒥.support : Set X)) {y : Y} (hy : f y ∈ (𝒥.support : Set X)) :
    ∃ E : Mori.PrimeDivisor Y, MMP.Flips.IsExceptionalPrimeDivisor sX f E ∧ y ∈ E.support ∧
      2 ≤ Order.coheight (f E.genericPoint) := by
  have : IsIntegral X := hX.toIsIntegral
  have : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  have : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  obtain ⟨E, hyE, hEJ⟩ := exists_primeDivisor_mem_support_subset hcart
    (y := y) (by rwa [Scheme.IdealSheafData.support_comap])
  have hE : f E.genericPoint ∈ (𝒥.support : Set X) := by
    have := hEJ (genericPoint_mem_support E)
    rw [Scheme.IdealSheafData.support_comap] at this
    exact this
  have hE2 := two_le_coheight_of_mem_support (h𝒥P hE) fun h => hP𝒥 (h ▸ hE)
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_eq sX hX
  exact ⟨E, ⟨hY, hf, inferInstance, (isExceptional_iff_two_le_coheight hd
    (ProperDivisorOver.mk ⟨Y, f, hY, hf, E⟩ inferInstance)).2 hE2⟩, hyE, hE2⟩

/-! ### Log resolutions dominating a normal model -/

/-- On a resolution `h ≫ p` of `X`, the generic point of a prime divisor of `Y` lying over
`Supp Δ` or exceptional over `X` lies in `Ex(h) ∪ h⁻¹(⋃ D)`, provided `D` contains every prime
divisor of `N` supported in `Ex(p) ∪ p⁻¹(Supp Δ)`. -/
private theorem genericPoint_mem_exceptionalSet_union {k : Type u} [Field k]
    {X N Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX]
    {Δ : RDivisor X} {p : N ⟶ X} {h : Y ⟶ N} (hres : IsResolutionOfVariety sX (h ≫ p))
    {d : ℕ} (hd : topologicalKrullDim X = d) {D : Finset (Mori.PrimeDivisor N)}
    (hD : ∀ Q : Mori.PrimeDivisor N,
      (Q.support : Set N) ⊆ (Mori.exceptionalSet p : Set N) ∪ p ⁻¹' (Δ.supp : Set X) → Q ∈ D)
    (P' : Mori.PrimeDivisor Y)
    (hP' : MMP.Flips.birationalInverseTransform (h ≫ p) hres.isBirationalMorphism Δ P' ≠ 0 ∨
      MMP.Flips.IsExceptionalPrimeDivisor sX (h ≫ p) P') :
    P'.genericPoint ∈ (Mori.exceptionalSet h : Set Y) ∪
      h ⁻¹' (D.sup fun E => (E.idealSheaf.support : Set N)) := by
  by_cases hbir : h P'.genericPoint ∈ biregularLocus h
  · right
    have hc : Order.coheight (h P'.genericPoint) = 1 := by
      rw [MMP.Positivity.coheight_map_of_mem_biregularLocus h hbir, P'.coheight_genericPoint]
    have hQg := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hc
    have hyZ : h P'.genericPoint ∈ (Mori.exceptionalSet p : Set N) ∪ p ⁻¹' (Δ.supp : Set X) := by
      rcases hP' with hP' | hP'
      · obtain ⟨Q₀, hQ₀, hQ₀g⟩ := exists_map_genericPoint_eq_of_birationalInverseTransform_ne_zero
          hres.isVariety hres.isVariety_source hres.isBirationalMorphism hP'
        right
        change p (h P'.genericPoint) ∈ (Δ.supp : Set X)
        rw [← Scheme.Hom.comp_apply, hQ₀g]
        exact DivisorWithCoeffs.support_subset_supp hQ₀ (genericPoint_mem_support Q₀)
      · left
        obtain ⟨_, _, _, hexc⟩ := hP'
        have h2 := (isExceptional_iff_two_le_coheight hd _).mp hexc
        refine Mori.mem_exceptionalSet.mpr fun hpb => ?_
        have h3 := MMP.Positivity.coheight_map_of_mem_biregularLocus p hpb
        change 2 ≤ Order.coheight ((h ≫ p) P'.genericPoint) at h2
        rw [Scheme.Hom.comp_apply, h3, hc] at h2
        exact absurd h2 (by decide)
    have hQD : AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hc ∈ D := by
      refine hD _ ?_
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, hQg]
      exact closure_minimal (Set.singleton_subset_iff.mpr hyZ)
        ((Mori.isClosed_exceptionalSet p).union (Δ.supp.isClosed.preimage p.continuous))
    change h P'.genericPoint ∈ (D.sup fun E => (E.idealSheaf.support : Set N))
    rw [Finset.sup_set_eq_biUnion]
    refine Set.mem_biUnion hQD ?_
    change h P'.genericPoint ∈ (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hc).support
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, hQg]
    exact subset_closure rfl
  · exact Or.inl (Mori.mem_exceptionalSet.mpr hbir)

/-- **A projective birational normal model of a log variety is dominated by a log resolution.**
For a log variety `(X, Δ)` in characteristic zero and a projective birational morphism `p : N ⟶ X`
from a normal variety, there is a resolution `h : Y ⟶ N` such that `h ≫ p` is a log resolution of
`(X, Δ)`; the components of the strict transform of `Δ` are smooth. -/
private theorem exists_isLogResolution_comp {k : Type u} [Field k] [CharZero k]
    {X N : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {Δ : RDivisor X}
    (hΔ : MMP.Flips.IsLogVariety k sX Δ) (p : N ⟶ X) (hN : IsNormalVariety k (p ≫ sX))
    (hpp : IsProjective p) (hp : IsBirationalMorphism p) :
    ∃ (Y : Scheme.{u}) (h : Y ⟶ N), IsResolutionOfVariety sX (h ≫ p) ∧
      MMP.Flips.IsLogResolution sX Δ (h ≫ p) ∧
      ∀ (hf : IsBirationalMorphism (h ≫ p)) (P' : Mori.PrimeDivisor Y),
        MMP.Flips.birationalInverseTransform (h ≫ p) hf Δ P' ≠ 0 →
          IsSmoothScheme (P'.idealSheaf.subschemeι ≫ (h ≫ p) ≫ sX) := by
  classical
  have hX : IsNormalVariety k sX := hΔ.isNormalVariety
  have hXv : AlgebraicGeometry.IsVariety k sX := hX.1
  have : IsIntegral X := hXv.toIsIntegral
  have : LocallyOfFiniteType sX := hXv.toLocallyOfFiniteType
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated sX
  have hNv : AlgebraicGeometry.IsVariety k (p ≫ sX) := hN.1
  have : IsIntegral N := hNv.toIsIntegral
  have : LocallyOfFiniteType (p ≫ sX) := hNv.toLocallyOfFiniteType
  have : IsLocallyNoetherian N := LocallyOfFiniteType.isLocallyNoetherian (p ≫ sX)
  have : CompactSpace N := QuasiCompact.compactSpace_of_compactSpace (p ≫ sX)
  have : IsNoetherian N := ⟨⟩
  have : IsProper p := hpp.isProper
  have : IsDominant p := hp.isDominant
  -- the closed subset `Ex(p) ∪ p⁻¹(Supp Δ)` of `N` and its prime divisors
  set Z : Set N := (Mori.exceptionalSet p : Set N) ∪ p ⁻¹' (Δ.supp : Set X) with hZ
  have hZc : IsClosed Z :=
    (Mori.isClosed_exceptionalSet p).union (Δ.supp.isClosed.preimage p.continuous)
  have hpgen := MMP.Positivity.map_genericPoint_eq_of_isDominant p
  have hgen : genericPoint N ∉ Z := by
    rintro (h | h)
    · apply Mori.mem_exceptionalSet.mp h
      rw [hpgen]
      refine MMP.Mori.mem_biregularLocus_of_ringKrullDim_stalk_le_one hX p hNv hp ?_
      rw [ringKrullDim_stalk_eq_coheight, Order.coheight_eq_zero.mpr fun b _ =>
        Scheme.le_iff_specializes.mpr (genericPoint_specializes b)]
      norm_num
    · change p (genericPoint N) ∈ (Δ.supp : Set X) at h
      rw [hpgen] at h
      exact MMP.Fourfold.genericPoint_notMem_supp Δ h
  set D := (finite_setOf_support_subset_of_isClosed hZc hgen).toFinset with hD
  -- an snc-preserving log resolution of `(N, D)`
  obtain ⟨Y, h, hres, -, hS, -⟩ :=
    MMP.Resolution.exists_isLogResolution_isIso_restrict_of_isSNCClosedSubset (p ≫ sX) hN D
  have hYv : AlgebraicGeometry.IsVariety k (h ≫ p ≫ sX) := hres.isVariety_source
  have : IsIntegral Y := hYv.toIsIntegral
  have : IsProper h := hres.isProjective.isProper
  have hres' : IsResolutionOfVariety sX (h ≫ p) :=
    { isVariety := hXv
      isVariety_source := by rw [Category.assoc]; exact hYv
      isProjective := IsProjective.comp hres.isProjective hpp
      isBirationalMorphism := isBirationalMorphism_comp hres.isBirationalMorphism hp
      isSmoothScheme := by rw [Category.assoc]; exact hres.isSmoothScheme }
  set S : Set Y := (Mori.exceptionalSet h : Set Y) ∪
    h ⁻¹' (D.sup fun E => (E.idealSheaf.support : Set N)) with hSdef
  have hS' : IsSNCClosedSubset ((h ≫ p) ≫ sX) S := by rw [Category.assoc]; exact hS
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_eq sX hXv
  have hsub : ∀ P' : Mori.PrimeDivisor Y,
      (MMP.Flips.birationalInverseTransform (h ≫ p) hres'.isBirationalMorphism Δ P' ≠ 0 ∨
        MMP.Flips.IsExceptionalPrimeDivisor sX (h ≫ p) P') → (P'.support : Set Y) ⊆ S := by
    intro P' hP'
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    refine closure_minimal (Set.singleton_subset_iff.mpr ?_) hS.1
    exact genericPoint_mem_exceptionalSet_union hres' hd
      (fun Q hQ => by rw [hD, Set.Finite.mem_toFinset]; exact hQ) P' hP'
  refine ⟨Y, h, hres', isLogResolution_of_forall_support_subset hΔ hres' hS' hsub,
    fun hf P' hP' => ?_⟩
  have : LocallyOfFiniteType ((h ≫ p) ≫ sX) := hres'.isVariety_source.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian ((h ≫ p) ≫ sX)
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace ((h ≫ p) ≫ sX)
  have : IsNoetherian Y := ⟨⟩
  have hG := isSNC_sum_single_of_support_subset hres'.isSmoothScheme hS' {P'}
    (by simpa using hsub P' (Or.inl hP'))
  exact hG.1 P' (by rw [support_sum_single]; exact Finset.mem_singleton_self P')

/-- Every point of a prime divisor `S'` maps under `e` into the closure of the image of
`η_{S'}`. -/
private theorem map_subschemeι_mem_closure {Y T : Scheme.{u}} (S' : Mori.PrimeDivisor Y)
    (e : Y ⟶ T) (y : S'.idealSheaf.subscheme) :
    e (S'.idealSheaf.subschemeι y) ∈ closure {e S'.genericPoint} := by
  have h1 : S'.idealSheaf.subschemeι y ∈ S'.support := by
    rw [show S'.support = Set.range S'.idealSheaf.subschemeι from
      S'.idealSheaf.range_subschemeι.symm]
    exact ⟨y, rfl⟩
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h1
  exact specializes_iff_mem_closure.mp ((specializes_iff_mem_closure.mpr h1).map e.continuous)

/-- If `f` sends `η_{S'}` to `η_P`, then `f|_{S'}` kills the ideal sheaf of `P`. -/
private theorem ker_subschemeι_le_ker_comp {X Y : Scheme.{u}} {P : Mori.PrimeDivisor X}
    {S' : Mori.PrimeDivisor Y} {f : Y ⟶ X} (hS'gen : f S'.genericPoint = P.genericPoint) :
    P.idealSheaf.subschemeι.ker ≤ (S'.idealSheaf.subschemeι ≫ f).ker := by
  have := S'.integral
  rw [show P.idealSheaf.subschemeι.ker = P.idealSheaf from P.idealSheaf.ker_subschemeι,
    Scheme.Hom.ker_eq_vanishingIdeal_closure_range,
    idealSheaf_eq_vanishingIdeal P (T := P.idealSheaf.support) rfl]
  refine Scheme.IdealSheafData.vanishingIdeal_antimono ?_
  change closure (Set.range (S'.idealSheaf.subschemeι ≫ f)) ⊆ (P.idealSheaf.support : Set X)
  refine closure_minimal ?_ P.idealSheaf.support.isClosed
  rintro _ ⟨y, rfl⟩
  have h1 := map_subschemeι_mem_closure S' f y
  rw [hS'gen] at h1
  change f (S'.idealSheaf.subschemeι y) ∈ P.support
  rwa [AlgebraicGeometry.PrimeDivisor.support_eq_closure]

/-- If `g ≫ π` sends `η_{S'}` to `η_P ∉ 𝒥`, then `g|_{S'}` kills the ideal sheaf of the strict
transform of `P` in the blow-up along `𝒥`. -/
private theorem ker_canonicalLift_le_ker_comp {X Y : Scheme.{u}} {P : Mori.PrimeDivisor X}
    {𝒥 : X.IdealSheafData} (hP𝒥 : P.genericPoint ∉ (𝒥.support : Set X))
    {S' : Mori.PrimeDivisor Y} {g : Y ⟶ blowUp 𝒥}
    (hS'gen : (g ≫ blowUpToBase 𝒥) S'.genericPoint = P.genericPoint) :
    (canonicalLift P.idealSheaf.subschemeι 𝒥).ker ≤ (S'.idealSheaf.subschemeι ≫ g).ker := by
  have := P.integral
  have := S'.integral
  rw [(Resolution.Bridges.range_canonicalLift_eq_closure_and_ker_eq_vanishingIdeal _ 𝒥
      fun hsub => hP𝒥 (hsub ⟨_, rfl⟩)).2,
    Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
  refine Scheme.IdealSheafData.vanishingIdeal_antimono ?_
  change closure (Set.range (S'.idealSheaf.subschemeι ≫ g)) ⊆ closure _
  refine closure_minimal ?_ isClosed_closure
  rintro _ ⟨y, rfl⟩
  refine closure_mono (Set.singleton_subset_iff.mpr ?_) (map_subschemeι_mem_closure S' g y)
  refine ⟨⟨genericPoint P.idealSheaf.subscheme, ?_⟩, ?_⟩
  · rw [← Scheme.Hom.comp_apply, hS'gen]
    rfl
  · rw [← Scheme.Hom.comp_apply, hS'gen]
    exact hP𝒥

/-- The reduced boundary `(Supp S ∪ Supp B)_red` makes a normal variety a log variety. -/
private theorem isLogVariety_reducedUnion {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    (hX : IsNormalVariety ℂ sX) (S : Divisor X) (B : QDivisor X) :
    IsLogVariety ℂ sX (Divisor.toRDivisor
      (MMP.Intersection.reducedUnion ![Divisor.toRDivisor S, QDivisor.toRDivisor B])) := by
  refine ⟨hX, fun E => ?_⟩
  rw [Divisor.coeff_toRDivisor, MMP.Intersection.coeff_reducedUnion]
  split_ifs <;> norm_num

/-- A component of `S` has nonzero coefficient in `(Supp S ∪ Supp B)_red`. -/
private theorem reducedUnion_apply_ne_zero {X : Scheme.{u}} {S : Divisor X} (B : QDivisor X)
    {P : Mori.PrimeDivisor X} (hP : S.coeff P ≠ 0) :
    Divisor.toRDivisor
      (MMP.Intersection.reducedUnion ![Divisor.toRDivisor S, QDivisor.toRDivisor B]) P ≠ 0 := by
  change (Divisor.toRDivisor
    (MMP.Intersection.reducedUnion ![Divisor.toRDivisor S, QDivisor.toRDivisor B])).coeff P ≠ 0
  rw [Divisor.coeff_toRDivisor, MMP.Intersection.coeff_reducedUnion, if_pos]
  · norm_num
  · exact ⟨0, by simpa [Divisor.coeff_toRDivisor] using hP⟩

/-- A morphism from a normal integral scheme sending generic point to generic point lifts through
the normalization to a dominant morphism. -/
private theorem exists_lift_normalization_isDominant {Z W : Scheme.{u}} [IsIntegral Z]
    [IsNormal Z] [IsIntegral W]
    (hW : ∀ U : W.Opens, IsCompact (U : Set W) → (irreducibleComponents U).Finite)
    [LocallyOfFiniteType (W.normalization hW)] [IsSeparated (W.normalization hW)] (σ : Z ⟶ W)
    (hσ : σ (genericPoint Z) = genericPoint W) :
    ∃ ψ, ψ ≫ W.normalization hW = σ ∧ IsDominant ψ := by
  obtain ⟨ψ, hψ, -⟩ := Scheme.existsUnique_lift_normalization hW σ fun η => by
    have h1 : η.1 = genericPoint _ := by
      obtain ⟨y, hy⟩ := η
      rw [genericPoints_eq_singleton] at hy
      exact hy
    rw [h1, hσ, genericPoints_eq_singleton]
    rfl
  have := Scheme.isIntegral_normalizationScheme W hW
  have hν := isBirationalMorphism_of_isBirational _ (Scheme.isBirational_normalization W hW)
  have : IsDominant (W.normalization hW) := hν.isDominant
  refine ⟨ψ, hψ, isDominant_of_map_genericPoint ψ ?_⟩
  refine eq_genericPoint_of_map_eq_genericPoint _ hν.functionFieldMap_bijective ?_
  rw [← Scheme.Hom.comp_apply, hψ, hσ]

/-- If `f` sends `η_{S'}` to `η_P` and is an isomorphism on the local ring there, then `f|_{S'}`
factors through `P` by a dominant morphism `σ : S' ⟶ P` inducing an isomorphism of function
fields. -/
private theorem exists_lift_subschemeι {X Y : Scheme.{u}} {P : Mori.PrimeDivisor X}
    {S' : Mori.PrimeDivisor Y} (f : Y ⟶ X) (hS'gen : f S'.genericPoint = P.genericPoint)
    (hS'iso : IsIso (f.stalkMap S'.genericPoint)) :
    haveI := P.integral
    haveI := S'.integral
    ∃ σ : S'.idealSheaf.subscheme ⟶ P.idealSheaf.subscheme,
      σ ≫ P.idealSheaf.subschemeι = S'.idealSheaf.subschemeι ≫ f ∧
      σ (genericPoint _) = genericPoint _ ∧
      ∃ _ : IsDominant σ, Function.Bijective (functionFieldMap σ) := by
  have := P.integral
  have := S'.integral
  set σ := IsClosedImmersion.lift P.idealSheaf.subschemeι (S'.idealSheaf.subschemeι ≫ f)
    (ker_subschemeι_le_ker_comp hS'gen)
  have hσ : σ ≫ P.idealSheaf.subschemeι = S'.idealSheaf.subschemeι ≫ f :=
    IsClosedImmersion.lift_fac _ _ _
  have hσgen : σ (genericPoint _) = genericPoint _ := by
    apply P.idealSheaf.subschemeι.isClosedEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hσ, Scheme.Hom.comp_apply]
    exact hS'gen
  have : IsDominant σ := isDominant_of_map_genericPoint σ hσgen
  exact ⟨σ, hσ, hσgen, this, (functionFieldMap σ).injective,
    functionFieldMap_surjective_of_comp_eq σ _ _ f hσ (by
      change Function.Surjective (f.stalkMap S'.genericPoint)
      exact (ConcreteCategory.bijective_of_isIso _).2)⟩

/-- If `g : Y ⟶ Bl_𝒥 X` sends `η_{S'}` to `η_P ∉ 𝒥` and `σ : S' ⟶ P` lifts `(g ≫ π)|_{S'}`,
then `g|_{S'}` lifts `σ` through the strict transform `Bl_{𝒥|_P} P ⟶ P` by a dominant,
universally closed morphism inducing an isomorphism of function fields. -/
private theorem exists_lift_blowUp_comap {X Y : Scheme.{u}} {P : Mori.PrimeDivisor X}
    {S' : Mori.PrimeDivisor Y} [IsIntegral P.idealSheaf.subscheme]
    [IsIntegral S'.idealSheaf.subscheme] {𝒥 : X.IdealSheafData}
    [IsIntegral (blowUp (𝒥.comap P.idealSheaf.subschemeι))]
    [IsProper (blowUpToBase (𝒥.comap P.idealSheaf.subschemeι))]
    (hP𝒥 : P.genericPoint ∉ (𝒥.support : Set X)) (g : Y ⟶ blowUp 𝒥) [IsProper g]
    (hS'gen : (g ≫ blowUpToBase 𝒥) S'.genericPoint = P.genericPoint)
    (hβ : IsBirationalMorphism (blowUpToBase (𝒥.comap P.idealSheaf.subschemeι)))
    {σ : S'.idealSheaf.subscheme ⟶ P.idealSheaf.subscheme} [IsDominant σ]
    (hσ : σ ≫ P.idealSheaf.subschemeι = S'.idealSheaf.subschemeι ≫ g ≫ blowUpToBase 𝒥)
    (hσgen : σ (genericPoint _) = genericPoint _)
    (hσbij : Function.Bijective (functionFieldMap σ)) :
    ∃ φ₁ : S'.idealSheaf.subscheme ⟶ blowUp (𝒥.comap P.idealSheaf.subschemeι),
      φ₁ ≫ blowUpToBase _ = σ ∧ ∃ (_ : IsDominant φ₁) (_ : UniversallyClosed φ₁),
        Function.Bijective (functionFieldMap φ₁) := by
  set j := P.idealSheaf.subschemeι
  have : IsDominant (blowUpToBase (𝒥.comap j)) := hβ.isDominant
  have := Resolution.Bridges.isClosedImmersion_canonicalLift j 𝒥
  set φ₁ := IsClosedImmersion.lift (canonicalLift j 𝒥) (S'.idealSheaf.subschemeι ≫ g)
    (ker_canonicalLift_le_ker_comp hP𝒥 hS'gen)
  have hφ₁ : φ₁ ≫ canonicalLift j 𝒥 = S'.idealSheaf.subschemeι ≫ g :=
    IsClosedImmersion.lift_fac _ _ _
  have hφ₁β : φ₁ ≫ blowUpToBase (𝒥.comap j) = σ := by
    rw [← cancel_mono j, hσ, Category.assoc, ← canonicalLift_comp_blowUpToBase,
      ← Category.assoc, hφ₁, Category.assoc]
  have : IsDominant φ₁ := isDominant_of_map_genericPoint φ₁ <|
    eq_genericPoint_of_map_eq_genericPoint (blowUpToBase (𝒥.comap j))
      hβ.functionFieldMap_bijective (by rw [← Scheme.Hom.comp_apply, hφ₁β, hσgen])
  have : IsDominant (φ₁ ≫ blowUpToBase (𝒥.comap j)) := by rw [hφ₁β]; infer_instance
  have : UniversallyClosed (φ₁ ≫ canonicalLift j 𝒥) := by rw [hφ₁]; infer_instance
  have : UniversallyClosed φ₁ := UniversallyClosed.of_comp_of_isSeparated φ₁ (canonicalLift j 𝒥)
  have hbij : Function.Bijective (functionFieldMap (φ₁ ≫ blowUpToBase (𝒥.comap j))) := by
    rw [MMP.Positivity.DivisorOver.functionFieldMap_congr hφ₁β]; exact hσbij
  refine ⟨φ₁, hφ₁β, ‹_›, ‹_›, (functionFieldMap φ₁).injective, fun t => ?_⟩
  obtain ⟨b, hb⟩ := hbij.2 t
  exact ⟨_, (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply _ _ b).trans hb⟩

end Helpers

section Main

open MMP.Fourfold

/-- Proof of
`MMP.Flips.exists_isLogResolution_valuation_eq_of_properDivisorOver_primeDivisorNormalization`. -/
theorem exists_isLogResolution_valuation_eq {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (hX : IsNormalVariety ℂ sX) (S : Divisor X) (hS : MMP.Intersection.IsReducedEffective S)
    (B : QDivisor X) (P : Mori.PrimeDivisor X) (hP : S.coeff P ≠ 0)
    (F : ProperDivisorOver ℂ (primeDivisorNormalization P ≫ sX)) :
    haveI := P.integral
    haveI : IsIntegral (primeDivisorNormalizationScheme P) :=
      Scheme.isIntegral_normalizationScheme P.idealSheaf.subscheme
        (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)
    ∃ (Y : Scheme.{0}) (f : Y ⟶ X) (hf : IsBirationalMorphism f),
      MMP.Flips.IsLogResolution sX
        (Divisor.toRDivisor
          (MMP.Intersection.reducedUnion ![Divisor.toRDivisor S, QDivisor.toRDivisor B])) f ∧
      ∃ (E S' : Mori.PrimeDivisor Y), MMP.Flips.IsExceptionalPrimeDivisor sX f E ∧
        Mori.RationalMap.transformPrimeDivisor (Mori.RationalMap.IsBirational.inverse hf) P =
          some S' ∧
        ∃ (C : Mori.PrimeDivisor S'.idealSheaf.subscheme),
          Maximal (fun W : Set Y => IsIrreducible W ∧ W ⊆ E.support ∩ S'.support)
            (S'.idealSheaf.subschemeι '' C.support) ∧
          ∃ (ψ : S'.idealSheaf.subscheme ⟶ primeDivisorNormalizationScheme P),
            ψ ≫ primeDivisorNormalization P = S'.idealSheaf.subschemeι ≫ f ∧
            ∃ (_ : IsNormal S'.idealSheaf.subscheme)
              (_ : IsLocallyNoetherian S'.idealSheaf.subscheme)
              (_ : IsDominant ψ),
              haveI := S'.integral
              F.valuation = C.divisorialValuation.comap (functionFieldMap ψ) := by
  classical
  have hXv : AlgebraicGeometry.IsVariety ℂ sX := hX.1
  have : IsIntegral X := hXv.toIsIntegral
  have : IsNormal X := hX.2
  have : LocallyOfFiniteType sX := hXv.toLocallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated sX
  have := P.integral
  have : IsIntegral (primeDivisorNormalizationScheme P) :=
    Scheme.isIntegral_normalizationScheme P.idealSheaf.subscheme
      (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)
  -- the boundary `Δ = (Supp S ∪ Supp B)_red`
  have hΔlog := isLogVariety_reducedUnion hX S B
  have hΔP := reducedUnion_apply_ne_zero B hP
  set Δ : RDivisor X := Divisor.toRDivisor
    (MMP.Intersection.reducedUnion ![Divisor.toRDivisor S, QDivisor.toRDivisor B]) with hΔ
  -- `P`, its normalization `ν'`, and the valuation `v` of `ℂ(P)` given by `F`
  set j := P.idealSheaf.subschemeι with hj
  have hPv : AlgebraicGeometry.IsVariety ℂ (j ≫ sX) := by constructor
  have : QuasiSeparatedSpace P.idealSheaf.subscheme :=
    quasiSeparatedSpace_of_quasiSeparated (j ≫ sX)
  have hPfin : ∀ U : P.idealSheaf.subscheme.Opens, IsCompact (U : Set P.idealSheaf.subscheme) →
      (irreducibleComponents U).Finite := fun U _ =>
    finite_irreducibleComponents_opens_of_irreducibleSpace U
  set ν' : primeDivisorNormalizationScheme P ⟶ P.idealSheaf.subscheme :=
    P.idealSheaf.subscheme.normalization hPfin with hν'
  have : IsFinite ν' := isFinite_normalizationOverField ℂ (j ≫ sX)
  have hν'b : IsBirationalMorphism ν' :=
    isBirationalMorphism_of_isBirational ν' (Scheme.isBirational_normalization _ hPfin)
  have : IsDominant ν' := hν'b.isDominant
  have := F.isIntegral
  have hD'nv : IsNormalVariety ℂ ((F.f ≫ ν') ≫ j ≫ sX) := by
    have := F.isNormalVariety
    simp only [Category.assoc] at this ⊢
    exact this
  let D' : DivisorOver ℂ (j ≫ sX) :=
    { Y := F.Y, f := F.f ≫ ν', isNormalVariety := hD'nv
      isBirationalMorphism := isBirationalMorphism_comp F.isBirationalMorphism hν'b
      E := F.E }
  set v := D'.valuation with hv
  have hvF : ∀ b, v b = F.valuation (functionFieldMap ν' b) := by
    intro b
    have := F.isNormal
    have := F.isLocallyNoetherian
    have := F.isDominant
    have : IsDominant (F.f ≫ ν') := D'.isDominant
    exact congrArg F.E.divisorialValuation
      (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply F.f ν' b).symm
  set x := (F.f ≫ ν') F.E.genericPoint with hx
  have hdiv := isDivisorOfFunctionField_valuation D'
  obtain ⟨g₀, hg₀⟩ := IsDivisorOfFunctionField.exists_eq_exp_neg_one (j ≫ sX) hdiv
  obtain ⟨U, J, hxU, hJ0, hxsupp, hchart⟩ := exists_affineOpen_ideal_blowUp_stalk_eq_integer
    (j ≫ sX) (IsDivisorOfFunctionField.exists_essFiniteType (j ≫ sX) hdiv) x
    (MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D' x rfl)
    (MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one D' x rfl) hg₀
  -- the ideal sheaf `𝒥` of `X`, supported in `P` and restricting to `J` near `x`
  obtain ⟨ℐ₀, hℐ₀⟩ := exists_idealSheafData_ideal_eq U J
  set 𝒥 := ℐ₀.map j with h𝒥
  have h𝒥j : 𝒥.comap j = ℐ₀ := Scheme.IdealSheafData.comap_map_of_isClosedImmersion ℐ₀ j
  have hℐ₀0 : ℐ₀ ≠ ⊥ := by
    rintro rfl
    exact hJ0 (by rw [← hℐ₀, Scheme.IdealSheafData.ideal_bot]; rfl)
  obtain ⟨h𝒥0, hmem𝒥, hP𝒥, h𝒥P⟩ := map_subschemeι_support P hℐ₀0
  have hx𝒥 : j x ∈ (𝒥.support : Set X) := (hmem𝒥 x).2 (hxsupp ℐ₀ hℐ₀)
  -- the blow-up `π₁ : X₁ ⟶ X` along `𝒥`
  obtain ⟨hX₁v, hπ₁p, hπ₁b⟩ :=
    MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational sX 𝒥 h𝒥0
  have : IsIntegral (blowUp 𝒥) := hX₁v.toIsIntegral
  have : IsProper (blowUpToBase 𝒥) := hπ₁p.isProper
  have hπ₁ : IsBirationalMorphism (blowUpToBase 𝒥) :=
    isBirationalMorphism_of_isBirational _ hπ₁b
  have : IsDominant (blowUpToBase 𝒥) := hπ₁.isDominant
  -- the strict transform `β : Bl_ℐ P ⟶ P` of `P`, and the point `q` realizing `v`
  have hℐ0 : 𝒥.comap j ≠ ⊥ := by rwa [h𝒥j]
  obtain ⟨hBv, hβp, hβb⟩ :=
    MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational (j ≫ sX)
      (𝒥.comap j) hℐ0
  have : IsIntegral (blowUp (𝒥.comap j)) := hBv.toIsIntegral
  have : IsProper (blowUpToBase (𝒥.comap j)) := hβp.isProper
  have hβ : IsBirationalMorphism (blowUpToBase (𝒥.comap j)) :=
    isBirationalMorphism_of_isBirational _ hβb
  have : IsDominant (blowUpToBase (𝒥.comap j)) := hβ.isDominant
  obtain ⟨q, hqx, hq⟩ := hchart (𝒥.comap j) (by rwa [h𝒥j])
    hβ.functionFieldMap_bijective.2
  -- the normalization `n : N ⟶ X₁` and the log resolution `h : Y ⟶ N`
  set n := normalizationOverField ℂ (blowUpToBase 𝒥 ≫ sX) with hn
  have : IsFinite n := isFinite_normalizationOverField ℂ (blowUpToBase 𝒥 ≫ sX)
  have hNv' : AlgebraicGeometry.IsVariety ℂ (n ≫ blowUpToBase 𝒥 ≫ sX) :=
    isVariety_normalizationOverField ℂ (blowUpToBase 𝒥 ≫ sX)
  have : IsIntegral (normalizationSchemeOverField ℂ (blowUpToBase 𝒥 ≫ sX)) :=
    hNv'.toIsIntegral
  have hNv : IsNormalVariety ℂ ((n ≫ blowUpToBase 𝒥) ≫ sX) :=
    ⟨by rw [Category.assoc]; exact hNv', Scheme.isNormal_normalizationScheme _ _⟩
  have hnp : IsProjective (n ≫ blowUpToBase 𝒥) :=
    IsProjective.comp (Stacks.FiniteMorphismProjective.isProjective_of_isFinite n) hπ₁p
  have hnb : IsBirationalMorphism (n ≫ blowUpToBase 𝒥) :=
    isBirationalMorphism_comp
      (isBirationalMorphism_of_isBirational n (Scheme.isBirational_normalization _ _)) hπ₁
  obtain ⟨Y, h, hres, hflog, hsm⟩ :=
    exists_isLogResolution_comp hΔlog (n ≫ blowUpToBase 𝒥) hNv hnp hnb
  set g : Y ⟶ blowUp 𝒥 := h ≫ n with hg
  set f : Y ⟶ X := h ≫ n ≫ blowUpToBase 𝒥 with hf_def
  have hgf : g ≫ blowUpToBase 𝒥 = f := by rw [hg, hf_def, Category.assoc]
  have hf : IsBirationalMorphism f := hres.isBirationalMorphism
  have hYv : Mori.IsVariety ℂ (f ≫ sX) := hres.isVariety_source
  have : IsProper f := hres.isProjective.isProper
  have : IsIntegral Y := hYv.toIsIntegral
  have : IsDominant f := hf.isDominant
  have : LocallyOfFiniteType (f ≫ sX) := hYv.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  have : Smooth (f ≫ sX) := MMP.Resolution.Aux.smooth_of_isSmoothScheme' (f ≫ sX)
    hres.isSmoothScheme
  have : IsNormal (Spec (.of ℂ)) := isNormal_spec_of_isIntegrallyClosed _
  have : IsNormal Y := AlgebraicGeometry.isNormal_of_smooth (f ≫ sX)
  have : IsDominant g := by
    refine isDominant_of_map_genericPoint g (eq_genericPoint_of_map_eq_genericPoint
      (blowUpToBase 𝒥) hπ₁.functionFieldMap_bijective ?_)
    rw [← Scheme.Hom.comp_apply, hgf]
    exact MMP.Positivity.map_genericPoint_eq_of_isDominant f
  have : IsProper (g ≫ blowUpToBase 𝒥) := by rw [hgf]; infer_instance
  have : IsProper g := IsProper.of_comp g (blowUpToBase 𝒥)
  -- the strict transform `S'` of `P`
  obtain ⟨S', hS'tr, hS'gen, hS'iso⟩ :=
    exists_transformPrimeDivisor_inverse_eq_some hX f hYv hf P
  have := S'.integral
  set ι' := S'.idealSheaf.subschemeι with hι'
  have hS'sm : IsSmoothScheme (ι' ≫ f ≫ sX) := hsm hf S' (by
    have hsep : IsSeparated (X ↘ ⊤_ Scheme) := isSeparated_terminal_from sX
    have hsepY : IsSeparated (Y ↘ ⊤_ Scheme) := isSeparated_terminal_from (f ≫ sX)
    change DivisorWithCoeffs.mapPrimeDivisors _ Δ S' ≠ 0
    rw [mapPrimeDivisors_apply_of_forall_eq hS'tr (fun Q hQ => ?_)]
    · exact hΔP
    · exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        ((genericPoint_eq_of_transformPrimeDivisor_inverse_eq_some hf hQ).symm.trans hS'gen))
  have : LocallyOfFiniteType (ι' ≫ f ≫ sX) := inferInstance
  have : IsLocallyNoetherian S'.idealSheaf.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (ι' ≫ f ≫ sX)
  have : Smooth (ι' ≫ f ≫ sX) := MMP.Resolution.Aux.smooth_of_isSmoothScheme' _ hS'sm
  have : IsNormal S'.idealSheaf.subscheme := AlgebraicGeometry.isNormal_of_smooth (ι' ≫ f ≫ sX)
  -- `f|_{S'}` lands in `P`: the morphism `σ : S' ⟶ P`
  obtain ⟨σ, hσ, hσgen, _, hσbij⟩ := exists_lift_subschemeι f hS'gen hS'iso
  -- the lift `ψ : S' ⟶ P^ν`
  have : IsFinite (P.idealSheaf.subscheme.normalization hPfin) :=
    isFinite_normalizationOverField ℂ (j ≫ sX)
  obtain ⟨ψ₀, hψ₀, hψ₀d⟩ := exists_lift_normalization_isDominant hPfin σ hσgen
  set ψ : S'.idealSheaf.subscheme ⟶ primeDivisorNormalizationScheme P := ψ₀ with hψdef
  have hψ : ψ ≫ ν' = σ := hψ₀
  have hψ' : ψ ≫ primeDivisorNormalization P = ι' ≫ f := by
    rw [← hσ, ← hψ]
    rfl
  have : IsDominant ψ := hψ₀d
  -- `f|_{S'}` lifts to the strict transform `Bl_ℐ P` of `P`: the morphism `φ₁`
  obtain ⟨φ₁, hφ₁β, _, _, hφ₁bij⟩ := exists_lift_blowUp_comap hP𝒥 g (by rw [hgf]; exact hS'gen)
    hβ (by rw [hσ, hgf]) hσgen hσbij
  have : IsDominant (φ₁ ≫ blowUpToBase (𝒥.comap j)) := by rw [hφ₁β]; infer_instance
  have hφ₁βbij : Function.Bijective (functionFieldMap (φ₁ ≫ blowUpToBase (𝒥.comap j))) := by
    rw [MMP.Positivity.DivisorOver.functionFieldMap_congr hφ₁β]; exact hσbij
  -- the point `c ∈ S'` over `q` with the same local ring, and the prime divisor `C`
  have := valuationRing_stalk_of_forall_le_one_iff (blowUpToBase (𝒥.comap j))
    hβ.functionFieldMap_bijective v q hq
  obtain ⟨c, hcq, hciso⟩ := MMP.Intersection.exists_isIso_stalkMap_of_valuationRing φ₁ hφ₁bij q
  have hz := forall_iff_exists_stalk_comp φ₁ (blowUpToBase (𝒥.comap j)) c {g | v g ≤ 1}
    (by subst hcq; exact hq)
  obtain ⟨C, hCc, hCv⟩ := exists_primeDivisor_valuationOver_eq hg₀
    (φ₁ ≫ blowUpToBase (𝒥.comap j)) hφ₁βbij c hz
  -- the prime divisor `E ∋ c` exceptional over `X`
  have hfc : f (ι' c) = j x := by
    rw [← Scheme.Hom.comp_apply, ← hσ, ← hφ₁β]
    simp only [Scheme.Hom.comp_apply]
    rw [hcq, hqx]
  have hcart : Stacks.Divisors.IsEffectiveCartierDivisor (𝒥.comap f) := by
    rw [← hgf, Scheme.IdealSheafData.comap_comp]
    exact isEffectiveCartierDivisor_comap g
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal 𝒥)
  obtain ⟨E, hEexc, hcE, hE2⟩ := exists_isExceptionalPrimeDivisor_mem_support hXv
    ⟨hYv, inferInstance⟩ hf hcart h𝒥P hP𝒥 (by rwa [hfc])
  have hES' : E ≠ S' := by
    rintro rfl
    rw [hS'gen, P.coheight_genericPoint] at hE2
    exact absurd hE2 (by decide)
  refine ⟨Y, f, hf, hflog, E, S', hEexc, hS'tr, C, ?_, ψ, hψ', ‹_›, ‹_›, ‹_›, ?_⟩
  · exact maximal_image_support hES' C (by rwa [hCc])
  · refine Valuation.ext fun b => ?_
    obtain ⟨a, rfl⟩ := hν'b.functionFieldMap_bijective.2 b
    change F.valuation _ = C.divisorialValuation (functionFieldMap ψ (functionFieldMap ν' a))
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply ψ ν' a,
      ← hvF a, show v = C.valuationOver _ from hCv.symm, PrimeDivisor.valuationOver_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_congr (hψ.trans hφ₁β.symm)]

end Main

end MMP.FourfoldProofs.DivisorOverComponent

end

section

/-!
# Divisors over a component of the normalization of `S`, realized on a log resolution

Let `X` be a normal complex variety, `S` a reduced divisor and `B` a `ℚ`-divisor on `X`, and let
`S_P` be a component of `S`, with normalization `ν : S_P^ν ⟶ S_P ⊆ X`. Every divisor `F` over
`S_P^ν` (a component of the normalization of `S`) is realized on a log resolution of `X`: there are
a log resolution `f : Y ⟶ X` of `(X, (Supp S ∪ Supp B)_red)`, a prime divisor `E` of `Y`
exceptional over `X`, and an irreducible component `C` of `E ∩ S'`, where `S' = f⁻¹_* S_P` is the
birational transform of `S_P`, such that `ord_C = ord_F` as valuations of
`ℂ(S_P^ν) = ℂ(S')`.

## Main results

* `MMP.Flips.exists_isLogResolution_valuation_eq_of_properDivisorOver_primeDivisorNormalization`

## Implementation notes

The normalization of the reduced divisor `S` is the disjoint union of the normalizations of its
components; a divisor over one of its components `S_j` is therefore a divisor
(`MMP.Flips.ProperDivisorOver`) over the normalization
`MMP.Fourfold.primeDivisorNormalizationScheme P` of a prime divisor `P` with nonzero coefficient in
`S`, and `ν(S_j) = P`.

The boundary of the log resolution is the reduced divisor on `Supp S ∪ Supp B`
(`MMP.Intersection.reducedUnion`), which contains `(Supp (S + B))_red`; since a reduced divisor
contained in an snc divisor is snc, a log resolution of `(X, (Supp S ∪ Supp B)_red)` is one of
`(X, (Supp (S + B))_red)`, and the components of `S` are never cancelled by `B`.

The identification `ℂ(S_P^ν) = ℂ(S')` is made explicit by a morphism
`ψ : S' ⟶ S_P^ν` lifting `f|_{S'} : S' ⟶ S_P` through `ν`; any two such lifts agree, since `ν` is
separated and an isomorphism over a dense open subset of `S_P`, so the conclusion pins the
identification. The valuation `ord_C` of `ℂ(S')` is that of the prime divisor `C` of the normal
variety `S'`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], proof of
  Theorem 17.2
-/

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold

namespace MMP.Flips

/-- **A divisor over a component of the normalization of `S` is realized on a log resolution.**
Let `X` be a normal complex variety, `S` a reduced divisor, `B` a `ℚ`-divisor on `X`, `P` a
component of `S` with normalization `ν : P^ν ⟶ X` (`MMP.Fourfold.primeDivisorNormalization`), and
`F` a divisor over `P^ν`. Then there are a log resolution `f : Y ⟶ X` of
`(X, (Supp S ∪ Supp B)_red)`, a prime divisor `E` of `Y` exceptional over `X`, the birational
transform `S' = f⁻¹_* P`, a prime divisor `C` of `S'` whose image in `Y` is an irreducible
component of `E ∩ S'`, and the lift `ψ : S' ⟶ P^ν` of `f|_{S'}` through `ν`, such that
`ord_F = ord_C ∘ ψ^*` on `ℂ(P^ν)`. -/
@[mmp "lem_fa17_divisor_over_s_on_log_resolution"]
public theorem exists_isLogResolution_valuation_eq_of_properDivisorOver_primeDivisorNormalization
    {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (hX : IsNormalVariety ℂ sX)
    (S : Divisor X) (hS : MMP.Intersection.IsReducedEffective S) (B : QDivisor X)
    (P : Mori.PrimeDivisor X) (hP : S.coeff P ≠ 0)
    (F : ProperDivisorOver ℂ (primeDivisorNormalization P ≫ sX)) :
    haveI := P.integral
    haveI : IsIntegral (primeDivisorNormalizationScheme P) :=
      Scheme.isIntegral_normalizationScheme P.idealSheaf.subscheme
        (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)
    ∃ (Y : Scheme.{0}) (f : Y ⟶ X) (hf : IsBirationalMorphism f),
      IsLogResolution sX
        (Divisor.toRDivisor
          (MMP.Intersection.reducedUnion ![Divisor.toRDivisor S, QDivisor.toRDivisor B])) f ∧
      ∃ (E S' : Mori.PrimeDivisor Y), IsExceptionalPrimeDivisor sX f E ∧
        Mori.RationalMap.transformPrimeDivisor (RationalMap.IsBirational.inverse hf) P =
          some S' ∧
        ∃ (C : Mori.PrimeDivisor S'.idealSheaf.subscheme),
          Maximal (fun W : Set Y => IsIrreducible W ∧ W ⊆ E.support ∩ S'.support)
            (S'.idealSheaf.subschemeι '' C.support) ∧
          ∃ (ψ : S'.idealSheaf.subscheme ⟶ primeDivisorNormalizationScheme P),
            ψ ≫ primeDivisorNormalization P = S'.idealSheaf.subschemeι ≫ f ∧
            ∃ (_ : IsNormal S'.idealSheaf.subscheme)
              (_ : IsLocallyNoetherian S'.idealSheaf.subscheme)
              (_ : IsDominant ψ),
              haveI := S'.integral
              F.valuation = C.divisorialValuation.comap (functionFieldMap ψ) :=
  MMP.FourfoldProofs.DivisorOverComponent.exists_isLogResolution_valuation_eq sX hX S hS B P hP F

end MMP.Flips

end
