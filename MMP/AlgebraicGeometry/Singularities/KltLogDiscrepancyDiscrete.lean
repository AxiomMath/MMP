module

public import MMP.AlgebraicGeometry.Singularities.SncLogDiscrepancyFormula
public import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
public import MMP.AlgebraicGeometry.Resolution.DisjoiningSequence

universe u v

section

/-!
# Log discrepancies of a klt pair lie in a discrete set

Let `(X, B)` be a Kawamata log terminal pair over an algebraically closed field of
characteristic zero. Take a log resolution `h : W ⟶ X` of `(X, B)` and write
`K_W + B_W = h^*(K_X + B)`, with `B_W = ∑ⱼ bⱼ Bⱼ` supported on the snc divisor formed by the
components of `h⁻¹_* B` and the `h`-exceptional prime divisors. Every `cⱼ = 1 - bⱼ` is the log
discrepancy of `Bⱼ`, hence positive. A divisor `F` of `k(X)` with center on `X` has a center on
`W`, its log discrepancy over `(X, B)` is its log discrepancy over `(W, B_W)`, and the latter is
`m + ∑ⱼ lⱼ cⱼ` with `m, lⱼ ∈ ℕ` by the log discrepancy formula over an snc divisor. Finally
`m + ∑ⱼ lⱼ ≥ 1` because the log discrepancy is positive.

## Main results

* `MMP.Flips.isLogResolution_of_isSNCClosedSubset`: a resolution `g` of a log variety `(X, B)`
  along which `Ex(g) ∪ g⁻¹(Supp B)` is an snc closed subset is a log resolution of `(X, B)`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 6.6
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped WithZero

namespace MMP.FourfoldProofs.Fa6KltLogDiscrepanciesDiscreteProof

open MMP MMP.Mori MMP.Flips MMP.Resolution

section Helpers

/-! ### Generalities on prime divisors -/

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
  simp [Finsupp.finset_sum_apply, Finsupp.single_apply]

private theorem coeff_sum_single {X : Scheme.{v}} (s : Finset (Mori.PrimeDivisor X))
    (P : Mori.PrimeDivisor X) [Decidable (P ∈ s)] :
    (∑ E ∈ s, Finsupp.single E (1 : ℤ) : Divisor X).coeff P = if P ∈ s then 1 else 0 := by
  classical
  simp [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply, Finsupp.single_apply]

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
  rw [Finsupp.sum, map_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_eq_zero fun Q hQ => ?_
  rw [DivisorWithCoeffs.mapPrimeDivisors_single]
  rcases hφ : φ Q with _ | E
  · rfl
  · have hne' : E ≠ P := fun he => hne Q (Finsupp.mem_support_iff.mp hQ) (by rw [hφ, he])
    exact Finsupp.single_eq_of_ne' hne'

/-! ### Strict transforms under the inverse of a birational morphism -/

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
    have he' : e.source.ι ≫ f = e.iso.hom ≫ e.target.ι :=
      ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
        (Scheme.PartialMap.toRationalMap_eq_iff.mp he)).symm
    rw [he', Iso.inv_hom_id_assoc, Category.comp_id]
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
      exact closure_mono
        (Set.singleton_subset_iff.mpr ⟨primeDivisor_genericPoint_mem_support P, hP⟩)
  rw [← MMP.Positivity.closure_image_eq_transform g' hg' _ hZ, Closeds.coe_closure]
  refine le_antisymm (closure_minimal ?_ isClosed_closure) (closure_mono ?_)
  · rintro _ ⟨q, hq, rfl⟩
    have hq' : P.genericPoint ⤳ g'.domain.ι q := by
      have : g'.domain.ι q ∈ P.support := hq
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
      exact specializes_iff_mem_closure.mpr this
    have h1 := (g'.domain.ι.isOpenEmbedding.isInducing.specializes_iff (y := q)
      (x := ⟨P.genericPoint, hP⟩)).mp (by rw [Scheme.Opens.ι_apply]; exact hq')
    exact specializes_iff_mem_closure.mp (h1.map g'.hom.continuous)
  · rw [Set.singleton_subset_iff]
    refine ⟨⟨P.genericPoint, hP⟩, ?_, rfl⟩
    exact primeDivisor_genericPoint_mem_support P

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
    {sX : X ⟶ Spec (.of k)} (hX : Mori.IsVariety k sX) : ∃ n : ℕ, topologicalKrullDim X = n := by
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

/-- A prime divisor `P` of `Y` exceptional over `X` has its generic point in `Ex(f)`. -/
private theorem genericPoint_mem_exceptionalSet {k : Type v} [Field k] {X : Scheme.{v}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX] {n : ℕ}
    (hn : topologicalKrullDim X = n) {Y : Scheme.{v}} {f : Y ⟶ X} {P : Mori.PrimeDivisor Y}
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
  · have : (W' : Set Y) ⊆ V := hV.2 ⟨W'.isIrreducible, hW'⟩ (by rw [hξ]; exact hle)
    change (W' : Set Y) ⊆ closure {ξ}
    rw [← hξ]
    exact this

/-- The support of a prime divisor contained in an snc closed subset `S` is an irreducible
component of `S`. -/
private theorem support_mem_componentsOf [NoetherianSpace Y] {S : Set Y}
    (hS : IsSNCClosedSubset sY S) {P : Mori.PrimeDivisor Y} (hP : (P.support : Set Y) ⊆ S) :
    (P.support : Set Y) ∈ componentsOf S := by
  obtain ⟨hSc, hempty | ⟨hpure, -, -⟩⟩ := hS
  · simpa [hempty] using hP (primeDivisor_genericPoint_mem_support P)
  · obtain ⟨-, hcov⟩ := Aux.finite_and_cover_componentsOf hSc
    obtain ⟨W, hW, hηW⟩ := hcov (hP (primeDivisor_genericPoint_mem_support P))
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
      simpa [hempty] using hs P hP (primeDivisor_genericPoint_mem_support P)
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

end SNC

/-! ### From an snc closed subset to a log resolution -/

/-- **A resolution with snc exceptional set and inverse image of the boundary is a log
resolution.** Let `(X, B)` be a log variety over a field `k` and `g : Y ⟶ X` a resolution such
that `Ex(g) ∪ g⁻¹(Supp B)` is a closed subset with simple normal crossings. Then `g` is a log
resolution of `(X, B)`. -/
public theorem _root_.MMP.Flips.isLogResolution_of_isSNCClosedSubset {k : Type v} [Field k]
    {X Y : Scheme.{v}} {sX : X ⟶ Spec (.of k)} {B : RDivisor X}
    (hB : MMP.Flips.IsLogVariety k sX B) {g : Y ⟶ X} (hres : IsResolutionOfVariety sX g)
    (hS : IsSNCClosedSubset (g ≫ sX) ((Mori.exceptionalSet g : Set Y) ∪ g ⁻¹' (B.supp : Set X))) :
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
  have : IsIntegral X := hX.1.toIsIntegral
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sX)
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (g ≫ sX)
  have : IsNoetherian Y := ⟨⟩
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_eq hX.1
  set S : Set Y := (Mori.exceptionalSet g : Set Y) ∪ g ⁻¹' (B.supp : Set X)
  have hsub : ∀ P : Mori.PrimeDivisor Y,
      (MMP.Flips.birationalInverseTransform g hg B P ≠ 0 ∨
        MMP.Flips.IsExceptionalPrimeDivisor sX g P) → (P.support : Set Y) ⊆ S := by
    intro P hP
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    refine closure_minimal (Set.singleton_subset_iff.mpr ?_) hS.1
    rcases hP with hP | hP
    · obtain ⟨Q, hQ, hgQ⟩ :=
        exists_map_genericPoint_eq_of_birationalInverseTransform_ne_zero hX.1 hYv hg hP
      right
      change g P.genericPoint ∈ (B.supp : Set X)
      rw [hgQ]
      exact DivisorWithCoeffs.support_subset_supp hQ (primeDivisor_genericPoint_mem_support Q)
    · left
      exact genericPoint_mem_exceptionalSet hn hP
  have hfin : {P : Mori.PrimeDivisor Y |
      MMP.Flips.birationalInverseTransform g hg B P ≠ 0 ∨
        MMP.Flips.IsExceptionalPrimeDivisor sX g P}.Finite :=
    (finite_setOf_support_subset hS).subset fun P hP => hsub P hP
  set s := hfin.toFinset with hs
  have hG := isSNC_sum_single_of_support_subset hsm hS s
    (fun P hP => hsub P (by simpa [hs] using hP))
  refine ⟨hB, hYv, hsm, inferInstance, hg, ∑ P ∈ s, Finsupp.single P (1 : ℤ),
    coeff_sum_single_eq_zero_or_eq_one s, fun P => ?_,
    ⟨coeff_sum_single_eq_zero_or_eq_one s, hG.1, fun p _ => hG.2 p⟩⟩
  · rw [coeff_sum_single]
    have hmem : P ∈ s ↔ (MMP.Flips.birationalInverseTransform g hg B P ≠ 0 ∨
        MMP.Flips.IsExceptionalPrimeDivisor sX g P) := by
      rw [hs, Set.Finite.mem_toFinset]
      rfl
    split_ifs with h
    · exact ⟨fun _ => hmem.mp h, fun _ => rfl⟩
    · exact ⟨fun h' => absurd h' (by decide), fun h' => absurd (hmem.mpr h') h⟩

/-! ### Forms, valuations and lifts of divisors -/

/-- The pull-back of a nonzero rational form along a morphism inducing an isomorphism of function
fields is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {k : Type u} [Field k] [PerfectField k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral Y]
    [LocallyOfFiniteType sX] (f : Y ⟶ X) [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d) {m : ℤ}
    {τ : RationalPluriForms sX d m} (hτ : τ ≠ 0) : pullbackRationalPluriForms sX f τ ≠ 0 := by
  let := functionFieldAlgebra sX
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX f hf hd
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := pullbackForms_eq hω m τ ▸ h0
  have h1 : algebraMap X.functionField Y.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← repr_pullbackFormsAlong hω m τ, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

/-- The valuation of a prime divisor `P` of `X`, viewed as a divisor over `X`, is `ord_P`. -/
private theorem valuation_ofPrimeDivisor {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    (P : MMP.Mori.PrimeDivisor X) :
    (DivisorOver.ofPrimeDivisor k hX P).valuation = P.divisorialValuation :=
  Valuation.ext fun φ => by
    change P.divisorialValuation (functionFieldMap (𝟙 X) φ) = _
    rw [functionFieldMap_id_apply]

/-! ### Lifting divisors over `X` to a proper birational model -/

/-- **Valuative criterion.** For a proper dominant morphism `f : Y ⟶ X` of integral schemes, a
valuation `ξ` of `k(Y)` whose restriction to `k(X)` is nonnegative on the local ring at `z`
dominates the local ring of a point of `Y`. -/
private theorem exists_stalk_dominated_of_isProper {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] (f : Y ⟶ X) [IsDominant f] [IsProper f] (ξ : Valuation Y.functionField ℤᵐ⁰)
    (z : X) (hz : ∀ b : X.presheaf.stalk z,
      ξ (functionFieldMap f (algebraMap _ X.functionField b)) ≤ 1) :
    ∃ x : Y, (∀ a : Y.presheaf.stalk x, ξ (algebraMap _ Y.functionField a) ≤ 1) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk x),
        ξ (algebraMap _ Y.functionField a) < 1 := by
  let R := ξ.valuationSubring
  let φ : X.presheaf.stalk z →+* R :=
    ((functionFieldMap f).comp (algebraMap (X.presheaf.stalk z) X.functionField)).codRestrict R
      fun b => (ξ.mem_valuationSubring_iff _).2 (hz b)
  have hgen : genericPoint X ⤳ z := (genericPoint_spec X).specializes trivial
  have hex : ValuativeCriterion.Existence f := by
    have h : @IsProper _ _ f := inferInstance
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1.existence
  let S : ValuativeCommSq f :=
    { R := R
      K := Y.functionField
      i₁ := Y.fromSpecStalk (genericPoint Y)
      i₂ := Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk z
      commSq := ⟨by
        rw [← functionFieldMap_fromSpecStalk f,
          ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgen, ← Category.assoc,
          ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
        rfl⟩ }
  obtain ⟨⟨l, hl₁, -⟩⟩ := (hex S).exists_lift
  have hl₁' : Spec.map (CommRingCat.ofHom (algebraMap R Y.functionField)) ≫ l =
      Y.fromSpecStalk (genericPoint Y) := hl₁
  set x := l (IsLocalRing.closedPoint R)
  have hx : genericPoint Y ⤳ x := (genericPoint_spec Y).specializes trivial
  let g := Scheme.stalkClosedPointTo l
  have hg : g ≫ CommRingCat.ofHom (algebraMap R Y.functionField) =
      Y.presheaf.stalkSpecializes hx := by
    apply Spec.map_injective
    apply (cancel_mono (Y.fromSpecStalk x)).mp
    rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hl₁',
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hga : ∀ a : Y.presheaf.stalk x,
      algebraMap _ Y.functionField a = ((g.hom a : R) : Y.functionField) := fun a =>
    (congrArg (fun q => q.hom a) hg).symm
  refine ⟨x, fun a => ?_, fun a ha => ?_⟩
  · rw [hga]
    exact (g.hom a).2
  · rw [hga]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp
      (fun hu => (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit g.hom a hu))

/-- For a proper birational morphism `f : Y ⟶ X` from a normal variety, every divisor `D` over
`X` has the valuation of a divisor `E` over `Y`, read on `k(X)` through `f^*`. -/
private theorem exists_properDivisorOver_comap_eq {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral Y] {f : Y ⟶ X}
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) [IsProper f]
    (D : ProperDivisorOver k sX) :
    haveI : IsDominant f := hf.isDominant
    ∃ E : ProperDivisorOver k (f ≫ sX), E.valuation.comap (functionFieldMap f) = D.valuation := by
  have : IsDominant f := hf.isDominant
  have : IsNormal Y := hY.2
  have : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  have hbW := hf.functionFieldMap_bijective
  let e : X.functionField ≃+* Y.functionField := RingEquiv.ofBijective (functionFieldMap f) hbW
  let ξ : Valuation Y.functionField ℤᵐ⁰ := D.valuation.comap (e.symm : Y.functionField →+* _)
  have hξ : ξ.comap (functionFieldMap f) = D.valuation := by
    ext t
    exact congrArg D.valuation (e.symm_apply_apply t)
  obtain ⟨x, h1, h2⟩ :=
    exists_stalk_dominated_of_isProper f ξ (D.f D.E.genericPoint) fun b =>
      (congrArg (· (algebraMap _ X.functionField b)) hξ).trans_le
        (MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D.toDivisorOver _ rfl _)
  have : AlgebraicGeometry.IsVariety k (f ≫ sX) := hY.1
  have hdiv : MMP.Flips.IsDivisorOfFunctionField k (f ≫ sX) ξ := by
    have := D.isIntegral
    have := D.isNormal
    have := D.isLocallyNoetherian
    have := D.isDominant
    refine ⟨D.Y, D.f ≫ sX, D.isNormalVariety, D.E, ?_⟩
    let := MMP.Mori.functionFieldAlgebra sX
    let := MMP.Mori.functionFieldAlgebra (f ≫ sX)
    let := MMP.Mori.functionFieldAlgebra (D.f ≫ sX)
    let eP := MMP.Mori.functionFieldAlgEquiv sX f hbW
    let eY :=
      MMP.Mori.functionFieldAlgEquiv sX D.f D.isBirationalMorphism.functionFieldMap_bijective
    refine ⟨eP.symm.trans eY, ?_⟩
    ext t
    obtain ⟨s, rfl⟩ := hbW.2 t
    have hes : eP.symm (functionFieldMap f s) = s := eP.symm_apply_apply s
    change ξ (functionFieldMap f s) = D.E.divisorialValuation (eY (eP.symm (functionFieldMap f s)))
    rw [hes]
    exact congrArg (· s) hξ
  obtain ⟨D', -, hv, -⟩ :=
    MMP.Flips.exists_properDivisorOver_isProjective_of_dominates (f ≫ sX) hdiv x h1 h2
  exact ⟨D', by rw [hv, hξ]⟩

/-! ### The log resolution and its crepant boundary -/

/-- A log variety over a field of characteristic zero has a log resolution. -/
private theorem exists_isLogResolution {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {B : RDivisor X} (hlv : IsLogVariety k sX B) :
    ∃ (W : Scheme.{u}) (f : W ⟶ X), MMP.Flips.IsLogResolution sX B f := by
  obtain ⟨W, f, hres, -, hS, -⟩ :=
    MMP.Resolution.exists_isLogResolution_isIso_restrict_of_isSNCClosedSubset sX
      hlv.isNormalVariety B.support
  have hsupp_eq : (B.supp : Set X) = B.support.sup fun E => (E.idealSheaf.support : Set X) := by
    rw [DivisorWithCoeffs.supp, Closeds.coe_finset_sup]
    rfl
  rw [← hsupp_eq] at hS
  exact ⟨W, f, isLogResolution_of_isSNCClosedSubset hlv hres hS⟩

/-- On a smooth birational model `W` of `X`, the divisor of the pull-back of a nonzero rational
top form is a canonical divisor. -/
private theorem isCanonicalDivisor_divisorOfForm_pullback {k : Type u} [Field k] [PerfectField k]
    {X W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) {f : W ⟶ X} [IsIntegral W] [IsLocallyNoetherian W]
    [IsNormal W] [CompactSpace W] [LocallyOfFiniteType (f ≫ sX)] [IsDominant f]
    (hY : IsNormalVariety k (f ≫ sX)) (hYsm : IsSmoothScheme (f ≫ sX))
    (hfb : IsBirationalMorphism f) {ω : RationalPluriForms sX n 1}
    (hσ0 : pullbackRationalPluriForms sX f ω ≠ 0) :
    (divisorOfForm (pullbackRationalPluriForms sX f ω)).IsCanonicalDivisor (f ≫ sX) n := by
  have : AlgebraicGeometry.IsVariety k sX := hX.1
  have : AlgebraicGeometry.IsVariety k (f ≫ sX) := hY.1
  have hnY : topologicalKrullDim W = n := by
    rw [← hn]
    exact (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (f ≫ sX) hfb).symm
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (f ≫ sX) hYsm hnY
  exact hK₀.of_linearlyEquivalent (by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hY hK₀ hσ0)

/-- The crepant boundary `f^*(K_X + B) - div_W(f^*ω)` of a log resolution `f : W ⟶ X` is
supported on the reduced divisor `G` formed by `f⁻¹_* B` and the exceptional prime divisors. -/
private theorem mem_support_of_coeff_crepantBoundary_ne_zero {k : Type u} [Field k]
    [PerfectField k] {X W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety k sX) {n : ℕ} (B : RDivisor X) {ω : RationalPluriForms sX n 1}
    (hω0 : ω ≠ 0) (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    (hKB : IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω) + B)) (f : W ⟶ X)
    [IsProper f] (hY : IsNormalVariety k (f ≫ sX)) (hfb : IsBirationalMorphism f) [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] [LocallyOfFiniteType (f ≫ sX)]
    [IsDominant f] {GP : RDivisor W}
    (hGP : IsRCartierPullback f (Divisor.toRDivisor (divisorOfForm ω) + B) GP) {G : Divisor W}
    (hGiff : ∀ P, G.coeff P = 1 ↔
      (birationalInverseTransform f hfb B).coeff P ≠ 0 ∨ IsExceptionalPrimeDivisor sX f P)
    (P : Mori.PrimeDivisor W)
    (hP : (GP - Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sX f ω))).coeff P ≠
      0) : P ∈ G.support := by
  classical
  obtain ⟨Ex, aE, GP', hEx, hGP', -, hform⟩ := discrepancy_formula hX B ω hω0 hK hKB f hY hfb
  have hGG : GP' = GP := IsRCartierPullback.eq f hGP' hGP
  have hG1 : G.coeff P = 1 := by
    refine (hGiff P).mpr ?_
    by_cases hex : IsExceptionalPrimeDivisor sX f P
    · exact Or.inr hex
    · left
      have hPEx : P ∉ Ex := fun h => hex ((hEx P).mp h)
      have h := DFunLike.congr_fun hform P
      simp only [Finsupp.add_apply, Finsupp.coe_finset_sum, Finset.sum_apply,
        Finsupp.single_apply, Finset.sum_ite_eq', hPEx, if_false, add_zero, hGG] at h
      rw [DivisorWithCoeffs.coeff_apply] at hP ⊢
      rw [Finsupp.sub_apply, ← h] at hP
      simpa using hP
  rw [DivisorWithCoeffs.coeff_apply] at hG1
  exact Finsupp.mem_support_iff.mpr (hG1 ▸ one_ne_zero)

/-! ### Reindexing a nonnegative integral combination -/

/-- A positive real `b = m + ∑_{P ∈ T} l_P c_P` with `m, l_P ∈ ℕ` is such a combination indexed by
`Fin #T`, with at least one nonzero coefficient. -/
private theorem exists_eq_natCast_add_sum_of_pos {ι : Type*} {T : Finset ι} {c : ι → ℝ} {b : ℝ}
    (hb : 0 < b) {m : ℕ} {l : ι → ℕ} (hbl : b = m + ∑ P ∈ T, (l P : ℝ) * c P) :
    ∃ (m' : ℕ) (l' : Fin T.card → ℕ), 1 ≤ m' + ∑ j, l' j ∧
      b = m' + ∑ j, (l' j : ℝ) * c (T.equivFin.symm j) := by
  have hsum : ∑ j, (l (T.equivFin.symm j) : ℝ) * c (T.equivFin.symm j) =
      ∑ P ∈ T, (l P : ℝ) * c P := by
    rw [← Finset.sum_coe_sort T]
    exact Equiv.sum_comp T.equivFin.symm fun P : T => (l P : ℝ) * c P
  refine ⟨m, fun j => l (T.equivFin.symm j), ?_, by rw [hbl, hsum]⟩
  by_contra! hlt
  have hl : ∀ P ∈ T, l P = 0 := fun P hP => by
    have := Finset.sum_eq_zero_iff.mp (show ∑ j, l (T.equivFin.symm j) = 0 by omega)
      (T.equivFin ⟨P, hP⟩) (Finset.mem_univ _)
    simpa using this
  rw [hbl, show m = 0 by omega, Finset.sum_eq_zero fun P hP => by simp [hl P hP]] at hb
  simp at hb

end Helpers

/-- Let `(X, B)` be a Kawamata log terminal pair. There are finitely many positive reals `cⱼ`
such that every log discrepancy of a divisor of `k(X)` with nonempty center on `X` is
`m + ∑ⱼ lⱼ cⱼ` with `m, lⱼ ∈ ℕ` and `m + ∑ⱼ lⱼ ≥ 1`. -/
theorem solution : ∀ {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    {n : ℕ} {K : Divisor X} {B : RDivisor X} (h : IsKawamataLogTerminal sX n K B),
    ∃ (s : ℕ) (c : Fin s → ℝ), (∀ j, 0 < c j) ∧
      ∀ F : Valuation X.functionField ℤᵐ⁰, HasNonemptyCenter k sX F →
        ∀ b : ℝ, IsLogDiscrepancy sX n K B F b →
          ∃ (m : ℕ) (l : Fin s → ℕ), 1 ≤ m + ∑ j, l j ∧ b = m + ∑ j, (l j : ℝ) * c j := by
  rintro k _ _ _ X sX _ _ _ _ _ n K B ⟨hlv, hK, hKB, hklt⟩
  classical
  have hX : IsNormalVariety k sX := hlv.isNormalVariety
  have hn : topologicalKrullDim X = n := hK.topologicalKrullDim_eq
  obtain ⟨ω, hω0, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain rfl : divisorOfForm ω = K := Finsupp.ext fun Γ => (coeff_divisorOfForm ω Γ).trans (hωK Γ)
  obtain ⟨W, f, -, hYvar, hYsm, hfp, hfb, G, -, hGiff, hGsnc⟩ := exists_isLogResolution hlv
  haveI : IsIntegral W := hYvar.toIsIntegral
  haveI : LocallyOfFiniteType (f ≫ sX) := hYvar.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  haveI : Smooth (f ≫ sX) := MMP.Resolution.Aux.smooth_of_isSmoothScheme' (f ≫ sX) hYsm
  haveI : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
  haveI : IsNormal W := AlgebraicGeometry.isNormal_of_smooth (f ≫ sX)
  haveI : CompactSpace W := hYvar.toQuasiCompact.compactSpace_of_compactSpace
  haveI := hfp
  haveI : IsDominant f := hfb.isDominant
  have hY : IsNormalVariety k (f ≫ sX) := ⟨hYvar, inferInstance⟩
  obtain ⟨GP, hGP, -⟩ := existsUnique_isRCartierPullback f hKB
  set σ := pullbackRationalPluriForms sX f ω
  set DY : RDivisor W := GP - Divisor.toRDivisor (divisorOfForm σ) with hDYdef
  have hDY : IsRCartierPullback f (Divisor.toRDivisor (divisorOfForm ω) + B)
      (Divisor.toRDivisor (divisorOfForm σ) + DY) := by rwa [hDYdef, add_sub_cancel]
  have hσ0 : σ ≠ 0 := pullbackRationalPluriForms_ne_zero f hfb.functionFieldMap_bijective
    (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn) hω0
  have hKY : (divisorOfForm σ).IsCanonicalDivisor (f ≫ sX) n :=
    isCanonicalDivisor_divisorOfForm_pullback hX hn hY hYsm hfb hσ0
  have hcrep := isDiscrepancy_comap_functionFieldMap_iff hX hω0 hK hKB f hY hfb hDY hKY
  have hKDY : IsCartierCombination (Divisor.toRDivisor (divisorOfForm σ) + DY) := by
    obtain ⟨m', r', L', L'', hLc, -, hpb, heq⟩ := hDY
    refine ⟨m', r', L'', fun j => (hpb j).2.isCartier (hLc j), ?_⟩
    rw [heq]
    simp only [toRDivisor_eq_mapCoeffs]
  have hpos : ∀ P, 0 < 1 - DY.coeff P := by
    intro P
    have h1 := isDiscrepancy_divisorialValuation hY σ hσ0 hKY hKDY P
    rw [← valuation_ofPrimeDivisor hY P] at h1
    have h2 :=
      (hcrep ⟨DivisorOver.ofPrimeDivisor k hY P, (inferInstance : IsProper (𝟙 W))⟩ _).mpr h1
    have := hklt _ h2.2.2.1 _ ⟨_, h2, rfl⟩
    linarith
  have hsupp : ∀ P, DY.coeff P ≠ 0 → P ∈ G.support :=
    mem_support_of_coeff_crepantBoundary_ne_zero hX B hω0 hK hKB f hY hfb hGP hGiff
  refine ⟨G.support.card, fun j => 1 - DY.coeff (G.support.equivFin.symm j), fun j => hpos _,
    fun F hF b hb => ?_⟩
  obtain ⟨a, ha, rfl⟩ := id hb
  obtain ⟨-, -, -, E₀, -, -, -, -, hE₀F, -, -⟩ := id ha
  obtain ⟨E, hE⟩ := exists_properDivisorOver_comap_eq hY hfb E₀
  obtain ⟨l, nP, hbeq, -⟩ := exists_logDiscrepancy_eq_add_sum_of_isSNCDivisor (f ≫ sX) hYvar
    hYsm hGsnc hsupp E (b := 1 + a) ⟨a, (hcrep E a).mp (by rwa [hE, hE₀F]), rfl⟩
  exact exists_eq_natCast_add_sum_of_pos (hklt F hF _ hb) hbeq

end MMP.FourfoldProofs.Fa6KltLogDiscrepanciesDiscreteProof

end

section

/-!
# Log discrepancies of a klt pair lie in a discrete set

Let `(X, B)` be a Kawamata log terminal pair. There are finitely many positive reals
`c₁, …, c_s` such that every log discrepancy `a_ℓ(F, X, B)` of a divisor `F` of `k(X)` with
nonempty center on `X` lies in
`Λ = {k + ∑ nⱼ cⱼ : k, n₁, …, n_s ∈ ℕ, k + ∑ nⱼ ≥ 1}`.
In particular the set of log discrepancies is discrete and bounded below by
`min (1, c₁, …, c_s) > 0`.

## Main results

* `MMP.Flips.IsKawamataLogTerminal.exists_logDiscrepancy_eq_add_sum`: the statement above.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 6.6
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped WithZero

namespace MMP.Flips

open MMP.Mori

/-- Let `(X, B)` be a Kawamata log terminal pair, `X` of dimension `n` with canonical divisor `K`.
There are finitely many positive reals `c₀, …, c_{s-1}` such that every log discrepancy
`a_ℓ(F, X, B)` of a divisor `F` of `k(X)` with nonempty center on `X` is `m + ∑ⱼ lⱼ cⱼ` for some
natural numbers `m, l₀, …, l_{s-1}` with `m + ∑ⱼ lⱼ ≥ 1`. -/
@[mmp "lem_fa6_klt_log_discrepancies_discrete"]
public theorem IsKawamataLogTerminal.exists_logDiscrepancy_eq_add_sum {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    {n : ℕ} {K : Divisor X} {B : RDivisor X} (h : IsKawamataLogTerminal sX n K B) :
    ∃ (s : ℕ) (c : Fin s → ℝ), (∀ j, 0 < c j) ∧
      ∀ F : Valuation X.functionField ℤᵐ⁰, HasNonemptyCenter k sX F →
        ∀ b : ℝ, IsLogDiscrepancy sX n K B F b →
          ∃ (m : ℕ) (l : Fin s → ℕ), 1 ≤ m + ∑ j, l j ∧ b = m + ∑ j, (l j : ℝ) * c j :=
  MMP.FourfoldProofs.Fa6KltLogDiscrepanciesDiscreteProof.solution sX h

end MMP.Flips

end
