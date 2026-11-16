module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.NefLogBirationalModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.FiniteGeneration
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancy
import MMP.AlgebraicGeometry.Divisor.Principal
import MMP.AlgebraicGeometry.MMP.Fourfold.Defs
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Divisor.LocalSectionDivisor
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Positivity.BaseLocusSum
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.MMP.BasepointFree.ProofData
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Resolution.BirationalTransformTriple
import MMP.AlgebraicGeometry.Positivity.SemiampleDescent
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Resolution.MaximalOrderAttained
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Bertini.FreeLinearSystem
import MMP.AlgebraicGeometry.Curves.PluricanonicalSectionsSeparatePoints
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
import MMP.AlgebraicGeometry.Singularities.BoundaryLowering
import MMP.AlgebraicGeometry.Singularities.Bertini.GeneralMemberSNC
import MMP.AlgebraicGeometry.Resolution.SNCWeight.StratumBlowup
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv

/-!
# Lowering the reduced boundary of a dlt pair using an ample component

Let `X` be a normal `ℚ`-factorial projective variety and `(X, Γ)` a dlt pair with real boundary.
Let `A ≤ Γ` be an effective ample `ℚ`-divisor none of whose components lies in the reduced
boundary `T = ⌊Γ⌋`. For every sufficiently small rational `δ > 0`, the `ℚ`-divisor `A + δT` is
ample, and removing `A` and lowering the coefficients of `T` by `δ` leaves an effective klt
boundary `Γ - A - δT`; adding back a general member `A' = H/m` of the `ℚ`-linear system of
`A + δT` keeps the pair klt. The divisor `A'` can be taken with arbitrarily small coefficients
and avoiding finitely many prescribed proper centres. Keeping one component `S` of `⌊Γ⌋` and
lowering only `T = ⌊Γ⌋ - S` instead, the same construction gives a plt boundary whose reduced
part is `S`.

## Main results

* `MMP.Fourfold.IsRealDltPair.exists_isRealKltPair_sub_add_of_isAmple`: the klt lowering.
* `MMP.Fourfold.IsRealDltPair.exists_isRealPltPair_sub_add_of_isAmple`: the plt lowering, keeping
  one reduced component.
* `MMP.Fourfold.AmpleFloorLowering.exists_section_logDiscrepancy_pos_of_isExceptional` and
  `MMP.Fourfold.AmpleFloorLowering.exists_section_isRealKltPair`: a general member of a free
  linear system supported in `Supp Γ` keeps `(X, Γ)` plt, resp. klt, after lowering.
* `MMP.Fourfold.AmpleFloorLowering.logDiscrepancy_pos_of_isSmoothResolution_of_isExceptional` and
  `MMP.Fourfold.AmpleFloorLowering.logDiscrepancy_pos_of_isSmoothResolution`: plt, resp. klt, is
  tested on one smooth model with snc boundary.

## Implementation notes

For small `δ > 0` a large multiple `M = N (A + δ T)` is a basepoint-free Cartier divisor (Serre's
theorem applied to an ample Cartier multiple of `A` and a Cartier multiple of `T`), and a general
member `(σ)₀ ∈ |M|` gives `A' = (σ)₀ / N ∼_ℚ A + δ T`.

Kltness of `Γ - (A + δ T) + A'` is checked on one log resolution `π : W ⟶ X` which is an
isomorphism over the snc locus of `(X, Γ)`. By Bertini's theorem on the smooth variety `W`, the
pull-back of `(σ)₀` is reduced and meets the snc divisor `Ex(π) ∪ π⁻¹(Supp Γ)` transversally, so
the crepant boundary on `W` is snc with coefficients at most one, and one only along the strict
transform of a kept component. Real snc boundaries with at most one coefficient equal to one have
positive log discrepancies along exceptional divisors, by comparison with a rational snc boundary
and the snc discrepancy bound; positivity descends along the crepant morphism `π`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.37, 5.17
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped WithZero

universe u

/-! ### Snc closed subsets and their components -/

namespace MMP.Resolution.AmpleFloorLowering

open MMP MMP.Mori MMP.Resolution

/-- The ideal sheaf of a prime divisor is the vanishing ideal of its support. -/
private theorem idealSheaf_eq_vanishingIdeal {X : Scheme.{u}} (P : Mori.PrimeDivisor X)
    {T : Closeds X} (hT : (T : Set X) = P.support) :
    P.idealSheaf = Scheme.IdealSheafData.vanishingIdeal T := by
  have := P.integral
  exact Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ (Closeds.ext hT.symm)

/-- The reduced divisor with components a finite set `s` of prime divisors has support `s`. -/
private theorem support_sum_single {X : Scheme.{u}} (s : Finset (Mori.PrimeDivisor X)) :
    (∑ E ∈ s, Finsupp.single E (1 : ℤ) : Divisor X).support = s := by
  classical
  ext E
  simp [Finsupp.finsetSum_apply, Finsupp.single_apply]

section SNC

variable {k : Type u} [Field k] {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}

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
    have := hP (MMP.Positivity.PrimeDivisor.genericPoint_mem_support' P)
    rw [hempty] at this
    exact this
  · obtain ⟨-, hcov⟩ := Aux.finite_and_cover_componentsOf hSc
    obtain ⟨W, hW, hηW⟩ := hcov (hP (MMP.Positivity.PrimeDivisor.genericPoint_mem_support' P))
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
    fun P _ Q _ h => Aux.PrimeDivisor.eq_of_support_eq h
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
      have := hs P hP (MMP.Positivity.PrimeDivisor.genericPoint_mem_support' P)
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
      exact Subtype.ext (Aux.PrimeDivisor.eq_of_support_eq h1)
    · rw [hideal P.1 (hs' P)]
      exact hcI ⟨_, hmem P⟩

end SNC

/-- If the restriction `Δ|_U` of a `ℚ`-divisor to an open `U` is snc, then `U ∩ Supp Δ` is a
divisor with simple normal crossings on `U`. -/
private theorem isSNCClosedSubset_preimage_of_isSNC_restrictOpen {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) {Δ : RDivisor X} {U : X.Opens}
    (hsnc : (Δ.restrictOpen U).IsSNC (U.ι ≫ sX)) :
    IsSNCClosedSubset (U.ι ≫ sX)
      (U.ι ⁻¹' (Δ.support.sup fun E => (E.idealSheaf.support : Set X))) := by
  classical
  set R := (Δ.restrictOpen U).support with hR
  have hsupp := support_sum_single R
  have hT : DivisorWithCoeffs.IsSNC (U.ι ≫ sX) (∑ E ∈ R, Finsupp.single E (1 : ℤ)) :=
    (DivisorWithCoeffs.isSNC_iff_of_support_eq hsupp).mpr hsnc
  have h := MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isSNCClosedSubset_of_isSNC _ hT
  rw [hsupp] at h
  convert h using 1
  ext x
  rw [Finset.sup_set_eq_biUnion]
  simp only [Set.mem_preimage, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨E, hE, hxE⟩
    obtain ⟨P, hP⟩ := MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support
      U.ι E x hxE
    refine ⟨P, ?_, ?_⟩
    · rw [hR, Finsupp.mem_support_iff]
      change Δ.coeff (OpenWeilRestriction.primeDivisorMap U.ι P) ≠ 0
      rw [hP]
      exact Finsupp.mem_support_iff.mp hE
    · rw [← MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff U.ι P x, hP]
      exact hxE
  · rintro ⟨P, hP, hxP⟩
    refine ⟨OpenWeilRestriction.primeDivisorMap U.ι P, ?_, ?_⟩
    · rw [hR, Finsupp.mem_support_iff] at hP
      exact Finsupp.mem_support_iff.mpr hP
    · exact (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff U.ι P x).2 hxP

end MMP.Resolution.AmpleFloorLowering

/-! ### Sections of a free linear system -/

namespace MMP.Mori.AmpleFloorLowering

open Classical in
/-- The coefficient of the reduced divisor `∑_{E ∈ S} E` at `F` is `1` or `0`. -/
private theorem coeff_sum_single {Y : Scheme.{u}} (S : Finset (PrimeDivisor Y))
    (F : PrimeDivisor Y) :
    DivisorWithCoeffs.coeff (∑ E ∈ S, Finsupp.single E (1 : ℤ) : Divisor Y) F =
      if F ∈ S then 1 else 0 := by
  classical
  change (∑ E ∈ S, Finsupp.single E (1 : ℤ)) F = _
  rw [Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply]

/-- **Avoiding a proper subspace by a polynomial condition.** If `v ∉ p` for a subspace
`p ⊆ kⁱ`, there is a nonzero polynomial `Q` (in fact a linear form) with `c ∉ p` whenever
`Q(c) ≠ 0`. -/
private theorem exists_polynomial_notMem_of_eval_ne_zero {k : Type*} [Field k] {ι : Type*}
    [Fintype ι] {p : Submodule k (ι → k)} {v : ι → k} (hv : v ∉ p) :
    ∃ Q : MvPolynomial ι k, Q ≠ 0 ∧ ∀ c, MvPolynomial.eval c Q ≠ 0 → c ∉ p := by
  classical
  obtain ⟨ℓ, hℓ, hp⟩ := Submodule.exists_le_ker_of_notMem hv
  let Q : MvPolynomial ι k :=
    ∑ i, MvPolynomial.C (ℓ (fun j => if i = j then 1 else 0)) * MvPolynomial.X i
  have heval : ∀ c, MvPolynomial.eval c Q = ℓ c := fun c => by
    rw [LinearMap.pi_apply_eq_sum_univ ℓ c]
    simp [Q, mul_comm]
  exact ⟨Q, fun h => hℓ (by rw [← heval, h, map_zero]), fun c hc hcp => hc (heval c ▸ hp hcp)⟩

/-- A general linear combination of finitely many sections, one of them nonzero, is nonzero:
the coefficient vectors `c` with `∑ cᵢ sᵢ = 0` form a proper subspace of `kⁱ`, contained in the
kernel of a linear form `ℓ` with `ℓ(e_j) ≠ 0`. -/
private theorem exists_polynomial_sum_smul_ne_zero {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {H : Divisor X} {ι : Type*} [Fintype ι] (s : ι → H.divisorialSubmodule ⊤) (j : ι)
    (hj : s j ≠ 0) :
    ∃ Q : MvPolynomial ι k, Q ≠ 0 ∧ ∀ c : ι → k, MvPolynomial.eval c Q ≠ 0 →
      (∑ i, scalarsToGlobalSections k sX (c i) • s i) ≠ 0 := by
  classical
  let p : Submodule k (ι → k) :=
    { carrier := {c | ∑ i, scalarsToGlobalSections k sX (c i) • s i = 0}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq, Pi.add_apply, map_add, add_smul,
          Finset.sum_add_distrib] at *
        rw [ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := by
        intro a c hc
        simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul] at *
        rw [← Finset.smul_sum, hc, smul_zero] }
  have hjp : (Pi.single j 1 : ι → k) ∉ p := by
    intro h
    apply hj
    have : ∑ i, scalarsToGlobalSections k sX ((Pi.single j 1 : ι → k) i) • s i = 0 := h
    rwa [Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp),
      Pi.single_eq_same, map_one, one_smul] at this
  exact exists_polynomial_notMem_of_eval_ne_zero hjp

/-! ### The zero scheme of a section of a divisorial sheaf -/

attribute [local instance] MMP.Mori.isInvertible_of_isInvertibleModule

section ZeroScheme

/-- The nonvanishing open of a nonzero section `t` of `𝒪_Y(D)` is the complement of the
support of its zero scheme. -/
private theorem mem_nonvanishingOpen_iff_notMem_supportSet {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (D : Divisor Y)
    [Stacks.Ample.IsInvertibleModule Y D.divisorialSheaf]
    {t : D.divisorialSubmodule ⊤} (ht : t ≠ 0) (y : Y) :
    y ∈ Stacks.NonvanishingOpen.nonvanishingOpen Y D.divisorialSheaf t ↔
      y ∉ (zeroScheme Y D.divisorialSheaf t).supportSet := by
  set s' := (Stacks.NonvanishingSpelling.sectionsEquiv Y D.divisorialSheaf).symm t
  have hev : PresheafOfModules.sections.eval s' (Opposite.op ⊤) = t :=
    (Stacks.NonvanishingSpelling.sectionsEquiv Y D.divisorialSheaf).apply_symm_apply t
  have h := AlgebraicGeometry.nonvanishingLocus_eq_compl_supportSet_zeroScheme
    D.divisorialSheaf s' (fun h0 => ht (hev.symm.trans h0))
  have h2 := Stacks.NonvanishingSpelling.stalkNonvanishingLocus_eq Y D.divisorialSheaf s'
  have e := (Stacks.NonvanishingSpelling.sectionsEquiv Y D.divisorialSheaf).apply_symm_apply t
  constructor
  · intro hy
    have h3 : y ∈ Stacks.SheafOfModules.nonvanishingLocus D.divisorialSheaf s' := by
      rwa [h2, e]
    rw [← hev]
    rwa [h] at h3
  · intro hyZ
    have h3 : y ∈ Stacks.SheafOfModules.nonvanishingLocus D.divisorialSheaf s' := by
      rw [h]
      exact fun hm => hyZ (hev ▸ hm)
    rw [h2] at h3
    change y ∈ Stacks.Ample.nonvanishingLocus D.divisorialSheaf t
    exact e ▸ h3

/-- On the nonvanishing open of a nonzero section `t` of `𝒪_Y(D)`, `D` Cartier, the divisor of
zeros `(t)₀` vanishes: such a point is off the zero scheme of `t`, hence so is the generic point of
every prime divisor through it. -/
private theorem notMem_supp_of_mem_nonvanishingOpen {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (D : Divisor Y) (hD : D.IsCartier)
    [Stacks.Ample.IsInvertibleModule Y D.divisorialSheaf]
    (t : D.divisorialSubmodule ⊤) (ht : t ≠ 0) (y : Y)
    (hy : y ∈ Stacks.NonvanishingOpen.nonvanishingOpen Y D.divisorialSheaf t) :
    y ∉ (D.zeroDivisor t ht).supp := by
  have hyZ := (mem_nonvanishingOpen_iff_notMem_supportSet D ht y).1 hy
  intro hmem
  obtain ⟨E, hE, hyE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
  have hEZ : E.genericPoint ∉ (zeroScheme Y D.divisorialSheaf t).supportSet := by
    intro hη
    apply hyZ
    have hcl : IsClosed (zeroScheme Y D.divisorialSheaf t).supportSet :=
      (zeroScheme Y D.divisorialSheaf t).support.isClosed
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hyE
    exact hcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hη) hyE
  exact hE (coeff_zeroDivisor_eq_zero_of_notMem D hD t ht E hEZ)

end ZeroScheme

end MMP.Mori.AmpleFloorLowering

namespace MMP.Threefold.Bridges.AmpleFloorLowering

open MMP.Mori

/-- The inverse transform of a divisor along the inclusion of an open subscheme is its
restriction. -/
private theorem inverseTransformDivisor_ι_eq_restrictOpen {X : Scheme.{u}} {R : Type*}
    [AddCommMonoid R] (U : X.Opens) (B : DivisorWithCoeffs R X) :
    inverseTransformDivisor U.ι B = B.restrictOpen U := by
  have hbir : ∀ x : U.toScheme, U.ι x ∈ biregularLocus U.ι := fun x =>
    le_biregularLocus (MMP.Mori.isIso_ι_restrict_self U)
      (by rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]; exact ⟨x, rfl⟩)
  refine Finsupp.ext fun W => ?_
  refine (MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    (E := OpenWeilRestriction.primeDivisorMap U.ι W)
    (MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint
      (OpenWeilRestriction.genericPoint_primeDivisorMap U.ι W).symm (hbir _))
    (fun E' hE' => ?_) B).trans rfl
  refine AlgebraicGeometry.PrimeDivisor.genericPoint_injective ?_
  rw [OpenWeilRestriction.genericPoint_primeDivisorMap,
    (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hE').1]

end MMP.Threefold.Bridges.AmpleFloorLowering

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold.AmpleFloorLowering

open MMP.Mori

/-! ### Real snc pairs -/

section RealSNC

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
  {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- A log discrepancy of an exceptional divisor over a pair with rational boundary and
`discrep > -1` is positive. -/
private theorem pos_of_isLogDiscrepancy_of_isExceptional {n : ℕ} {K : Divisor X}
    {Δ : QDivisor X} (hP : MMP.Mori.IsPair sX Δ) (hK : K.IsCanonicalDivisor sX n)
    (hd : -1 < discrep sX n K Δ) {n' : ℕ} {D : DivisorOver k sX} (hE : D.IsExceptional) {a : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sX n' (QDivisor.toRDivisor Δ) D a) : 0 < a := by
  obtain rfl : n' = n := by
    exact_mod_cast (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha).symm.trans
      hK.topologicalKrullDim_eq
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK D
  rw [MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy hc ha]
  have h : (-1 : ℝ) < c := by
    exact_mod_cast EReal.coe_lt_coe_iff.mp (hd.trans_le (discrep_le hE hc))
  linarith

/-- The log discrepancy of a prime divisor `P` of `X` with respect to an `ℝ`-divisor `B` with
`K + B` `ℝ`-Cartier is `1 - coeff_P B`. -/
private theorem isLogDiscrepancy_ofPrimeDivisor [CompactSpace X] (hX : IsNormalVariety k sX)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {B : RDivisor X}
    (hKB : RDivisor.IsRCartier (Divisor.toRDivisor K + B)) (P : MMP.Mori.PrimeDivisor X) :
    MMP.Intersection.IsLogDiscrepancy sX n B (DivisorOver.ofPrimeDivisor k hX P)
      (1 - B.coeff P) := by
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain ⟨m, r, C, hC, hsum⟩ := hKB
  choose C' hC' using fun i => MMP.Threefold.Bridges.exists_isPullback_of_isDominant (𝟙 X) (hC i)
  have hC'P : ∀ i, (C' i).coeff P = (C i).coeff P := fun i =>
    MMP.Positivity.coeff_eq_of_isPullback (f := 𝟙 X) P P rfl (hC i) (hC' i)
  have hord : (DivisorOver.ofPrimeDivisor k hX P).ordPullback ω = P.ordForm ω :=
    DivisorOver.ordPullback_ofPrimeDivisor hX hK.topologicalKrullDim_eq P ω
  have hsumΓ : ∀ Γ, (Γ.ordForm ω : ℝ) + B.coeff Γ = ∑ i, r i * (C i).coeff Γ := fun Γ => by
    rw [← hsum Γ, hω Γ, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor]
  refine ⟨hX, (inferInstance : IsProper (𝟙 X)), ω, hω0, ⟨K, hK, fun Γ => (hω Γ).symm⟩, m, r, C,
    C', hC, hsumΓ, fun i => ⟨_, hC' i⟩, ?_⟩
  change 1 - B.coeff P = 1 + ((DivisorOver.ofPrimeDivisor k hX P).ordPullback ω : ℝ) -
    ∑ i, r i * ((C' i).coeff P : ℝ)
  simp_rw [hC'P, hord]
  rw [← hsumΓ P]
  ring

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] in
open Classical in
/-- Sums over the prime divisors of a finite set, written through `Fin`. -/
private theorem sum_equivFin_mul_single (S : Finset (MMP.Mori.PrimeDivisor X))
    (c : MMP.Mori.PrimeDivisor X → ℝ) (Γ : MMP.Mori.PrimeDivisor X) :
    ∑ i : Fin S.card, c (S.equivFin.symm i) *
        (((Finsupp.single (S.equivFin.symm i : MMP.Mori.PrimeDivisor X) (1 : ℤ)) Γ : ℤ) : ℝ) =
      if Γ ∈ S then c Γ else 0 := by
  rw [Equiv.sum_comp S.equivFin.symm (fun x : S => c x *
    (((Finsupp.single (x : MMP.Mori.PrimeDivisor X) (1 : ℤ)) Γ : ℤ) : ℝ))]
  rw [Finset.sum_coe_sort S (fun x => c x * (((Finsupp.single x (1 : ℤ)) Γ : ℤ) : ℝ))]
  simp only [Finsupp.single_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single Γ]
    · simp
    · intro b _ hb; simp [hb]
    · exact fun h' => absurd h h'
  · refine Finset.sum_eq_zero fun b hb => ?_
    have : b ≠ Γ := fun h' => h (h' ▸ hb)
    simp [this]

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] in
open Classical in
/-- The coefficient at `Γ` of the combination `K + ∑_{E ∈ S} c_E E`, indexed via
`S.equivFin`, is `K.coeff Γ + (if Γ ∈ S then c Γ else 0)`. -/
private theorem sum_cons_mul_coeff (K : Divisor X) (S : Finset (MMP.Mori.PrimeDivisor X))
    (c : MMP.Mori.PrimeDivisor X → ℝ) (Γ : MMP.Mori.PrimeDivisor X) :
    ∑ i, (Fin.cons 1 (fun i => c (S.equivFin.symm i)) : Fin (S.card + 1) → ℝ) i *
        (((Fin.cons K (fun i => (Finsupp.single (S.equivFin.symm i : MMP.Mori.PrimeDivisor X)
          (1 : ℤ) : Divisor X)) : Fin (S.card + 1) → Divisor X) i).coeff Γ : ℝ) =
      K.coeff Γ + if Γ ∈ S then c Γ else 0 := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, one_mul, DivisorWithCoeffs.coeff_apply]
  rw [sum_equivFin_mul_single S c Γ]

/-- **Log discrepancies decrease as an snc boundary grows.** On a smooth variety, let `Δ ≤ Δ'` be
`ℝ`-divisors supported in a finite set `S` of prime divisors. If `a(D, X, Δ) = a`, then `D` has a
log discrepancy `a' ≤ a` with respect to `Δ'`: both are computed through the presentation of
`K + Δ` and `K + Δ'` by `K` and the members of `S`, whose pull-backs are effective. -/
private theorem exists_isLogDiscrepancy_le_of_coeff_le (hX : IsNormalVariety k sX)
    (hsm : IsSmoothScheme sX) {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    (S : Finset (MMP.Mori.PrimeDivisor X)) {Δ Δ' : RDivisor X}
    (hΔ : ∀ Γ, Γ ∉ S → Δ.coeff Γ = 0) (hΔ' : ∀ Γ, Γ ∉ S → Δ'.coeff Γ = 0)
    (hle : ∀ P ∈ S, Δ.coeff P ≤ Δ'.coeff P) {n' : ℕ} {D : DivisorOver k sX} {a : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sX n' Δ D a) :
    ∃ a', MMP.Intersection.IsLogDiscrepancy sX n' Δ' D a' ∧ a' ≤ a := by
  classical
  obtain rfl : n' = n := by
    exact_mod_cast (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha).symm.trans
      hK.topologicalKrullDim_eq
  let C : Fin (S.card + 1) → Divisor X :=
    Fin.cons K fun i => (Finsupp.single (S.equivFin.symm i : MMP.Mori.PrimeDivisor X) (1 : ℤ))
  have hC : ∀ i, (C i).IsCartier := fun i => MMP.Fourfold.isCartier_of_isSmoothScheme hsm _
  let r : (MMP.Mori.PrimeDivisor X → ℝ) → Fin (S.card + 1) → ℝ :=
    fun c => Fin.cons 1 fun i => c (S.equivFin.symm i)
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isDominant
  have : CompactSpace D.Y := by
    have := D.isNormalVariety.1
    exact QuasiCompact.compactSpace_of_compactSpace (D.f ≫ sX)
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  choose C' hC' using fun i => MMP.Threefold.Bridges.exists_isPullback_of_isDominant D.f (hC i)
  -- the log discrepancy of a boundary supported in `S`, through this presentation
  have hb : ∀ B : RDivisor X, (∀ Γ, Γ ∉ S → B.coeff Γ = 0) →
      MMP.Intersection.IsLogDiscrepancy sX n' B D
        (1 + (D.ordPullback ω : ℝ) - ∑ i, r B.coeff i * ((C' i).coeff D.E : ℝ)) := by
    intro B hB
    refine ⟨hX, ha.2.1, ω, hω0, ⟨K, hK, fun Γ => (hω Γ).symm⟩, S.card + 1, r B.coeff, C, C', hC,
      fun Γ => ?_, fun i => ⟨_, hC' i⟩, rfl⟩
    rw [sum_cons_mul_coeff, hω Γ]
    split_ifs with h
    · rfl
    · rw [hB Γ h]
  refine ⟨_, hb Δ' hΔ', ?_⟩
  rw [MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha (hb Δ hΔ), sub_le_sub_iff_left,
    Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [r, Fin.cons_zero, Fin.cons_succ]
  refine add_le_add_right (Finset.sum_le_sum fun i _ => ?_) _
  have hc0 : (0 : ℝ) ≤ ((C' i.succ).coeff D.E : ℝ) := by
    have hnn := MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn (hC i.succ)
      (V := ⊤) (fun P _ => ?_) (hC' i.succ) D.E ((D.E.genericPoint_mem_iff _).mp trivial)
    · exact_mod_cast hnn
    · simp only [C, Fin.cons_succ, DivisorWithCoeffs.coeff_apply, Finsupp.single_apply]
      split_ifs <;> norm_num
  exact mul_le_mul_of_nonneg_right (hle _ (S.equivFin.symm i).2) hc0

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] in
/-- There is a rational number `q < 1` above every coefficient `< 1` of `Δ` along `S`, and above
`0`. -/
private theorem exists_rat_coeff_lt (Δ : RDivisor X) (S : Finset (MMP.Mori.PrimeDivisor X)) :
    ∃ q : ℚ, 0 < q ∧ q < 1 ∧ ∀ P ∈ S, Δ.coeff P < 1 → Δ.coeff P < q := by
  classical
  obtain ⟨t, ht1, ht⟩ : ∃ t : ℝ, t < 1 ∧ ∀ P ∈ S, Δ.coeff P < 1 → Δ.coeff P ≤ t := by
    refine ⟨(insert 0 ((S.filter fun P => Δ.coeff P < 1).image Δ.coeff)).max'
      (Finset.insert_nonempty _ _), ?_, fun P hP hP1 => Finset.le_max' _ _
        (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hP, hP1⟩)))⟩
    refine (Finset.max'_lt_iff _ _).mpr fun y hy => ?_
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact one_pos
    · obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hy
      exact (Finset.mem_filter.1 hP).2
  obtain ⟨q, hq0, hq1⟩ := exists_rat_btwn (max_lt ht1 one_pos : max t 0 < 1)
  exact ⟨q, by exact_mod_cast (le_max_right _ _).trans_lt hq0, by exact_mod_cast hq1,
    fun P hP hP1 => (ht P hP hP1).trans_lt ((le_max_left _ _).trans_lt hq0)⟩

/-- **Real snc pairs are plt.** On a smooth variety `X` over an algebraically closed field of
characteristic zero, let `Δ` be an `ℝ`-divisor whose support lies in a finite set `S` of prime
divisors with `∑_{E ∈ S} E` simple normal crossing, with coefficients at most one, and such that
no two members of `S` both have coefficient one. Then every exceptional divisor over `X` has
positive log discrepancy with respect to `Δ`. The log discrepancies of `Δ` dominate those of the
rational snc boundary with coefficient `q` along the members of coefficient `< 1` and `1` along the
others, whose discrepancy exceeds `-1` by the snc discrepancy bound
(`MMP.Mori.le_discrep_of_isSNC`). -/
private theorem logDiscrepancy_pos_of_isSNC_of_isExceptional [IsAlgClosed k]
    (hX : IsNormalVariety k sX)
    (hsm : IsSmoothScheme sX) {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    {Δ : RDivisor X} (S : Finset (MMP.Mori.PrimeDivisor X)) (hS : Δ.support ⊆ S)
    (hsnc : DivisorWithCoeffs.IsSNC sX (∑ E ∈ S, Finsupp.single E (1 : ℤ)))
    (h1 : ∀ P, Δ.coeff P ≤ 1)
    (h2 : ∀ P ∈ S, ∀ Q ∈ S, P ≠ Q → Δ.coeff P < 1 ∨ Δ.coeff Q < 1) {n' : ℕ}
    {D : DivisorOver k sX} (hD : D.IsExceptional) {a : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sX n' Δ D a) : 0 < a := by
  classical
  have hΔS : ∀ Γ, Γ ∉ S → Δ.coeff Γ = 0 := fun Γ hΓ =>
    Classical.byContradiction fun h => hΓ (hS (Finsupp.mem_support_iff.mpr h))
  obtain ⟨q, hq0, hq1, hq⟩ := exists_rat_coeff_lt Δ S
  let c : MMP.Mori.PrimeDivisor X → ℚ := fun E => if Δ.coeff E < 1 then q else 1
  let Δq : QDivisor X := ∑ E ∈ S, Finsupp.single E (c E)
  have hΔq : ∀ Γ, Δq.coeff Γ = if Γ ∈ S then c Γ else 0 := fun Γ => by
    simp only [Δq, DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply, Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
  have hc1 : ∀ E, c E ≤ 1 := fun E => by
    simp only [c]
    split_ifs <;> linarith
  have hΔqS : Δq.support ⊆ S := fun E hE => by
    by_contra h
    exact (Finsupp.mem_support_iff.mp hE)
      (by rw [← DivisorWithCoeffs.coeff_apply, hΔq, ite_eq_right h])
  -- the discrepancy of the rational snc boundary exceeds `-1`
  have hb : ∀ E ∈ S, ((-q : ℚ) : ℝ) ≤ ((1 - Δq.coeff E : ℚ) : ℝ) := fun E hE => by
    rw [hΔq, ite_eq_left hE]
    exact_mod_cast (show -q ≤ 1 - c E by linarith [hc1 E])
  have hpair : ∀ E ∈ S, ∀ F ∈ S, E ≠ F →
      ((-q : ℚ) : ℝ) ≤ ((1 - Δq.coeff E - Δq.coeff F : ℚ) : ℝ) := fun E hE F hF hEF => by
    rw [hΔq, hΔq, ite_eq_left hE, ite_eq_left hF]
    have : c E = q ∨ c F = q :=
      (h2 E hE F hF hEF).imp (fun h => ite_eq_left h) (fun h => ite_eq_left h)
    exact_mod_cast (show -q ≤ 1 - c E - c F by rcases this with h | h <;> linarith [hc1 E, hc1 F])
  have hq0' : (0 : ℝ) < q := by exact_mod_cast hq0
  have hd : -1 < discrep sX n K Δq := by
    refine lt_of_lt_of_le ?_ (le_trans (le_inf (le_inf
      (le_iInf₂ fun E hE => le_iInf₂ fun F hF => le_iInf₂ fun hEF _ =>
        EReal.coe_le_coe_iff.mpr (hpair E hE F hF hEF))
      (le_iInf₂ fun E hE => EReal.coe_le_coe_iff.mpr (hb E hE)))
      (show ((((-q : ℚ) : ℝ)) : EReal) ≤ 1 from by
        exact_mod_cast (show ((-q : ℚ) : ℝ) ≤ 1 by push_cast; linarith [hq0'])))
      (MMP.Mori.le_discrep_of_isSNC hX hsm hK hΔqS hsnc fun E _ => by
        rw [hΔq]
        split_ifs
        exact hc1 E))
    have : (-1 : ℝ) < ((-q : ℚ) : ℝ) := by
      push_cast
      linarith [(by exact_mod_cast hq1 : (q : ℝ) < 1)]
    simpa using (EReal.coe_lt_coe_iff.mpr this : ((-1 : ℝ) : EReal) < _)
  obtain ⟨a', ha', hle⟩ := exists_isLogDiscrepancy_le_of_coeff_le hX hsm hK S hΔS
    (Δ' := QDivisor.toRDivisor Δq)
    (fun Γ hΓ => by rw [QDivisor.coeff_toRDivisor, hΔq, ite_eq_right hΓ, Rat.cast_zero])
    (fun P hP => by
      rw [QDivisor.coeff_toRDivisor, hΔq, ite_eq_left hP]
      simp only [c]
      split_ifs with h
      · exact (hq P hP h).le
      · simpa using h1 P) ha
  exact (pos_of_isLogDiscrepancy_of_isExceptional
    ⟨hX, n, K, hK, MMP.Fourfold.isQCartier_of_isSmoothScheme hsm _⟩ hK hd hD ha').trans_le hle

end RealSNC

/-! ### Crepant transfer of log discrepancies -/

section CrepantInputs

open MMP.Flips

private theorem exists_dominated_point {k : Type u} [Field k] {X W : Scheme.{u}} [IsIntegral X]
    [IsIntegral W] {sX : X ⟶ Spec (.of k)} (π : W ⟶ X) [IsDominant π] [IsProper π]
    (D : DivisorOver k sX) (ξ : Valuation W.functionField (WithZero (Multiplicative ℤ)))
    (h : ξ.comap (functionFieldMap π) = D.valuation) :
    ∃ x : W, (∀ a : W.presheaf.stalk x, ξ (algebraMap _ W.functionField a) ≤ 1) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (W.presheaf.stalk x),
        ξ (algebraMap _ W.functionField a) < 1 := by
  set y := D.f D.E.genericPoint
  have hw : ∀ b : X.presheaf.stalk y,
      ξ (functionFieldMap π (algebraMap _ X.functionField b)) =
        D.valuation (algebraMap _ X.functionField b) := by
    intro b
    simpa only [Valuation.comap_apply] using
      congrArg (fun v => v (algebraMap _ X.functionField b)) h
  let R := ξ.valuationSubring
  let φ : X.presheaf.stalk y →+* R :=
    ((functionFieldMap π).comp (algebraMap (X.presheaf.stalk y) X.functionField)).codRestrict R
      fun b => (ξ.mem_valuationSubring_iff _).2 (by
        rw [RingHom.comp_apply, hw]
        exact MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D y rfl _)
  have hgen : genericPoint X ⤳ y := (genericPoint_spec X).specializes trivial
  have hex : ValuativeCriterion.Existence π := by
    have h : IsProper π := inferInstance
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1.existence
  let S : ValuativeCommSq π :=
    { R := R
      K := W.functionField
      i₁ := W.fromSpecStalk (genericPoint W)
      i₂ := Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk y
      commSq := ⟨by
        rw [← functionFieldMap_fromSpecStalk π,
          ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgen, ← Category.assoc,
          ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
        rfl⟩ }
  obtain ⟨⟨l, hl₁, -⟩⟩ := (hex S).exists_lift
  have hl₁' : Spec.map (CommRingCat.ofHom (algebraMap R W.functionField)) ≫ l =
      W.fromSpecStalk (genericPoint W) := hl₁
  set x := l (IsLocalRing.closedPoint R)
  have hx : genericPoint W ⤳ x := (genericPoint_spec W).specializes trivial
  let f := Scheme.stalkClosedPointTo l
  have hf : f ≫ CommRingCat.ofHom (algebraMap R W.functionField) =
      W.presheaf.stalkSpecializes hx := by
    apply Spec.map_injective
    apply (cancel_mono (W.fromSpecStalk x)).mp
    rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hl₁',
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hfa : ∀ a : W.presheaf.stalk x,
      algebraMap _ W.functionField a = ((f.hom a : R) : W.functionField) := fun a =>
    (congrArg (fun q => q.hom a) hf).symm
  refine ⟨x, fun a => ?_, fun a ha => ?_⟩
  · rw [hfa]
    exact (f.hom a).2
  · rw [hfa]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp
      (fun hu => (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit f.hom a hu))

section Discrepancy

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]

/-- A discrepancy computed with a form whose divisor is canonical gives the log discrepancy
`1 + a`. -/
private theorem isLogDiscrepancy_of_isDiscrepancyWith {n : ℕ} {D : RDivisor X}
    {ω : RationalPluriForms sX n 1} {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X}
    {E : ProperDivisorOver k sX} {b : ℝ} (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    (h : IsDiscrepancyWith sX n D ω r L E b) :
    MMP.Intersection.IsLogDiscrepancy sX n D E.toDivisorOver (1 + b) := by
  obtain ⟨hX, hn, hω, hLc, hsum, L', hpb, rfl⟩ := h
  refine ⟨hX, E.isProper, ω, hω, ⟨divisorOfForm ω, hK, fun Γ => coeff_divisorOfForm ω Γ⟩, m, r,
    L, L', hLc, fun Γ => ?_, hpb, by ring⟩
  simpa only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, coeff_divisorOfForm,
    MMP.Flips.coeff_sum_smul_toRDivisor] using congrArg (fun D : RDivisor X => D.coeff Γ) hsum

/-- With a presentation of `div(ω) + D` by Cartier divisors, every divisor over `X` (with proper
model) has a discrepancy computed with these choices. -/
private theorem exists_isDiscrepancyWith (hX : IsNormalVariety k sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) {D : RDivisor X} {ω : RationalPluriForms sX n 1}
    (hω : ω ≠ 0) {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} (hLc : ∀ j, (L j).IsCartier)
    (hsum : Divisor.toRDivisor (divisorOfForm ω) + D = ∑ j, r j • Divisor.toRDivisor (L j))
    (E : ProperDivisorOver k sX) : ∃ b, IsDiscrepancyWith sX n D ω r L E b := by
  have := E.isIntegral
  have := E.isNormal
  have := E.isLocallyNoetherian
  have := E.isDominant
  have := E.isProper
  have : CompactSpace E.Y := QuasiCompact.compactSpace_of_compactSpace E.f
  choose L' hL' using fun j => MMP.Threefold.Bridges.exists_isPullback_of_isDominant E.f (hLc j)
  exact ⟨_, hX, hn, hω, hLc, hsum, L', fun j => ⟨_, hL' j⟩, rfl⟩

/-- The valuation of a divisor over `X` with proper model has nonempty center. -/
private theorem hasNonemptyCenter_valuation (E : ProperDivisorOver k sX) :
    HasNonemptyCenter k sX E.valuation := by
  have := E.isIntegral
  have := E.isNormal
  have := E.isLocallyNoetherian
  have := E.isDominant
  exact ⟨⟨E.Y, E.f ≫ sX, E.isNormalVariety, E.E,
    functionFieldAlgEquiv sX E.f E.isBirationalMorphism.functionFieldMap_bijective, rfl⟩, E, rfl⟩

end Discrepancy

/-! ### Lifting a divisor over `M` to a proper model `W ⟶ M` -/

section Lift

variable {k : Type u} [Field k] {M W : Scheme.{u}} [IsIntegral M] [IsIntegral W]
  {sM : M ⟶ Spec (.of k)}

variable [IsLocallyNoetherian M] [IsNormal M] [IsLocallyNoetherian W] [IsNormal W]

/-- **Lifting a divisor over `M` along a proper birational morphism.** Every divisor `D` over `M`
with proper model has the valuation `ord_E ∘ q^*` of a divisor `E` over `W`, for `q : W ⟶ M`
proper birational with `W` a variety. -/
private theorem exists_properDivisorOver_comap_eq (q : W ⟶ M) [IsProper q]
    (hq : IsBirationalMorphism q) [AlgebraicGeometry.IsVariety k (q ≫ sM)]
    (D : ProperDivisorOver k sM) :
    haveI := hq.isDominant
    ∃ E : ProperDivisorOver k (q ≫ sM),
      E.valuation.comap (functionFieldMap q) = D.valuation := by
  have := hq.isDominant
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have := D.isDominant
  have hbq := hq.functionFieldMap_bijective
  let eq := RingEquiv.ofBijective (functionFieldMap q) hbq
  let ξ : Valuation W.functionField ℤᵐ⁰ := D.valuation.comap eq.symm.toRingHom
  have hξ : ξ.comap (functionFieldMap q) = D.valuation := by
    ext a
    change D.valuation (eq.symm (functionFieldMap q a)) = D.valuation a
    rw [show functionFieldMap q a = eq a from rfl, RingEquiv.symm_apply_apply]
  obtain ⟨x, hle, hlt⟩ := exists_dominated_point q D.toDivisorOver ξ hξ
  have hdiv : IsDivisorOfFunctionField k (q ≫ sM) ξ := by
    refine ⟨D.Y, D.f ≫ sM, D.isNormalVariety, D.E, ?_⟩
    let := functionFieldAlgebra sM
    let := functionFieldAlgebra (q ≫ sM)
    let := functionFieldAlgebra (D.f ≫ sM)
    let eP := functionFieldAlgEquiv sM q hbq
    let eY := functionFieldAlgEquiv sM D.f D.isBirationalMorphism.functionFieldMap_bijective
    refine ⟨eP.symm.trans eY, ?_⟩
    ext t
    obtain ⟨s, rfl⟩ := hbq.2 t
    change D.valuation (eq.symm (functionFieldMap q s)) =
      D.E.divisorialValuation (eY (eP.symm (functionFieldMap q s)))
    have h1 : eP.symm (functionFieldMap q s) = s := eP.symm_apply_apply s
    rw [h1, show functionFieldMap q s = eq s from rfl, RingEquiv.symm_apply_apply]
    rfl
  obtain ⟨E, -, hv, -⟩ := exists_properDivisorOver_isProjective_of_dominates (q ≫ sM) hdiv x hle hlt
  exact ⟨E, by rw [hv, hξ]⟩

end Lift

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

/-- Being exceptional over a normal variety depends only on the valuation. -/
private theorem isExceptional_of_valuation_eq {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) {D D' : DivisorOver k sX} (h : D.valuation = D'.valuation)
    (hD : D.IsExceptional) : D'.IsExceptional := by
  rw [DivisorOver.isExceptional_iff_two_le_coheight hX] at hD ⊢
  rwa [← MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 h]

/-- **Positivity of log discrepancies descends along a crepant proper birational morphism.** Let
`π : W ⟶ X` be a proper birational morphism of normal varieties, `K_X = div(ω)` canonical with
`div(π^*ω)` canonical on `W`, and `K_W + D_W = π^*(K_X + D)` with `K_W = div(π^*ω)`. Let `E` be a
divisor over `X` realized by a divisor `E'` over `W`. If every log discrepancy over `(W, D_W)` of a
divisor with the valuation of `E'` is positive, so is the log discrepancy of `E` over `(X, D)`:
the two discrepancies agree. -/
private theorem logDiscrepancy_pos_of_isRCartierPullback {k : Type u} [Field k] [PerfectField k]
    {X W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] (hX : IsNormalVariety k sX)
    (π : W ⟶ X) [IsProper π] [LocallyOfFiniteType (π ≫ sX)]
    [AlgebraicGeometry.IsVariety k (π ≫ sX)] (hW : IsNormalVariety k (π ≫ sX))
    (hπ : IsBirationalMorphism π) {n : ℕ} {ω : RationalPluriForms sX n 1} (hω : ω ≠ 0)
    (hK : (divisorOfForm ω).IsCanonicalDivisor sX n) {D : RDivisor X} {DW : RDivisor W}
    (hDW : haveI : IsDominant π := hπ.isDominant
      IsRCartierPullback π (Divisor.toRDivisor (divisorOfForm ω) + D)
        (Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sX π ω)) + DW))
    (hKW : haveI : IsDominant π := hπ.isDominant
      (divisorOfForm (pullbackRationalPluriForms sX π ω)).IsCanonicalDivisor (π ≫ sX) n)
    {E : DivisorOver k sX} {E' : ProperDivisorOver k (π ≫ sX)}
    (hE' : haveI : IsDominant π := hπ.isDominant
      E'.valuation.comap (functionFieldMap π) = E.valuation)
    (hkltW : ∀ (d : ℕ) (E₀ : DivisorOver k (π ≫ sX)) (a : ℝ), E₀.valuation = E'.valuation →
      MMP.Intersection.IsLogDiscrepancy (π ≫ sX) d DW E₀ a → 0 < a)
    {d : ℕ} {a : ℝ} (ha : MMP.Intersection.IsLogDiscrepancy sX d D E a) : 0 < a := by
  have : IsDominant π := hπ.isDominant
  obtain rfl : d = n := by
    exact_mod_cast (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha).symm.trans
      hK.topologicalKrullDim_eq
  let EP : ProperDivisorOver k sX := ⟨E, ha.2.1⟩
  obtain ⟨m, r, L, L', hLc, hLsum, -, -⟩ := id hDW
  obtain ⟨b, hb⟩ := exists_isDiscrepancyWith hX hK.topologicalKrullDim_eq hω hLc hLsum EP
  rw [MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha
    (isLogDiscrepancy_of_isDiscrepancyWith hK hb)]
  have hKD : IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω) + D) :=
    ⟨m, r, L, hLc, by rw [hLsum]; simp only [toRDivisor_eq_mapCoeffs]⟩
  have h1 := (isDiscrepancy_comap_functionFieldMap_iff hX hω hK hKD π hW hπ hDW hKW E' b).mp (by
    rw [hE']
    exact ⟨hK, hKD, hasNonemptyCenter_valuation EP, EP, ω, m, r, L, rfl, rfl, hb⟩)
  obtain ⟨-, -, -, E₀, ω₀, m₀, r₀, L₀, hv₀, hdiv₀, hw₀⟩ := h1
  exact hkltW _ E₀.toDivisorOver (1 + b) hv₀
    (isLogDiscrepancy_of_isDiscrepancyWith (by rwa [hdiv₀]) hw₀)

end CrepantInputs

/-! ### Serre generation -/

section GlobalGeneration

open Stacks.Ample Stacks.RelativeVeryAmple

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]

/-- `𝒪_X(n H + F) ≅ 𝒪_X(F) ⊗ 𝒪_X(H)^{⊗ n}` for Cartier divisors `H` and `F`. -/
private theorem nonempty_divisorialSheaf_nsmul_add_iso {H F : Divisor X} (hH : H.IsCartier)
    (hF : F.IsCartier) (n : ℕ) :
    haveI := hH.isInvertibleModule_divisorialSheaf
    Nonempty ((n • H + F).divisorialSheaf ≅
      tensorModules X F.divisorialSheaf (tensorPowModule X H.divisorialSheaf (n : ℤ))) := by
  have := hH.isInvertibleModule_divisorialSheaf
  induction n with
  | zero =>
    exact ⟨eqToIso (by rw [zero_smul, zero_add]) ≪≫
      (Stacks.TensorSheafSpellingIso.tensorModulesRightUnitor X _).symm ≪≫
      tensorModulesMapIso X (Iso.refl _) (tensorPowModuleZeroIso X _).symm⟩
  | succ n ih =>
    obtain ⟨e⟩ := ih
    exact ⟨eqToIso (by rw [succ_nsmul, add_right_comm]) ≪≫
      (((hH.nsmul n).add hF).divisorialSheafTensorIso hH).symm ≪≫
      tensorModulesMapIso X e (tensorPowModuleOneIso X _).symm ≪≫
      Stacks.TensorSheafSpellingIso.tensorModulesAssociator X _ _ _ ≪≫
      tensorModulesMapIso X (Iso.refl _)
        (tensorPowModuleAddIso X _ (n : ℤ) 1 ≪≫ tensorPowModuleCongr X _ (by push_cast; ring))⟩

/-- **Serre generation for `𝒪_X(n H + F)`.** If `𝒪_X(H)` is ample and `F` is Cartier, then for
some `n` finitely many global sections `s₀, …, s_N` of `𝒪_X(n H + F)` have nonvanishing opens
covering `X`. -/
private theorem exists_forall_ge_forall_mem_nonvanishingOpen [IsIntegral X] {H F : Divisor X}
    (hH : H.IsCartier) (hF : F.IsCartier)
    (hamp : haveI := hH.isInvertibleModule_divisorialSheaf
      Stacks.Ample.IsAmple X H.divisorialSheaf) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∃ (N : ℕ) (s : Fin (N + 1) → Γ((n • H + F).divisorialSheaf, ⊤)),
      haveI := ((hH.nsmul n).add hF).isInvertibleModule_divisorialSheaf
      ∀ x : X, ∃ i, x ∈ Stacks.NonvanishingOpen.nonvanishingOpen X (n • H + F).divisorialSheaf
        (s i) := by
  have := hH.isInvertibleModule_divisorialSheaf
  have := hF.isInvertibleModule_divisorialSheaf
  have : SheafOfModules.IsFiniteType.{u, u, u} F.divisorialSheaf :=
    Stacks.AmpleEventualGeneration.isFiniteType_of_isInvertibleModule _
  obtain ⟨n₀, hn₀⟩ :=
    (Stacks.AmpleLocalGeneration.quasiSeparatedSpace_and_isEventuallyGloballyGenerated_of_isAmple
      _ hamp).2 F.divisorialSheaf inferInstance inferInstance
  refine ⟨n₀.toNat, fun n hn => ?_⟩
  obtain ⟨σ, hσ⟩ := hn₀ (n : ℤ) (by omega)
  have := ((hH.nsmul n).add hF).isInvertibleModule_divisorialSheaf
  let := Stacks.SheafInternalHom.schemeMonoidalCategory X
  let i := Stacks.TensorSheafSpellingIso.monoidalTensorIso X F.divisorialSheaf
    (tensorPowModule X H.divisorialSheaf (n : ℤ))
  obtain ⟨e⟩ := nonempty_divisorialSheaf_nsmul_add_iso hH hF n
  let p := i.hom ≫ e.inv
  have : @Epi (SheafOfModules.{u} X.ringCatSheaf) _ _ _ p :=
    @IsIso.epi_of_iso _ _ _ _ p inferInstance
  let σ' := σ.ofEpi p
  have : Finite σ'.I := hσ
  have : Fintype σ'.I := Fintype.ofFinite _
  obtain ⟨x₀⟩ : Nonempty X := inferInstance
  obtain ⟨i₀, -⟩ := Stacks.SheafOfModules.exists_generatingSection_nonvanishing _ σ' x₀
  have hcard : 0 < Fintype.card σ'.I := Fintype.card_pos_iff.mpr ⟨i₀⟩
  let eI : σ'.I ≃ Fin (Fintype.card σ'.I - 1 + 1) :=
    Fintype.equivFinOfCardEq (by omega)
  refine ⟨Fintype.card σ'.I - 1, fun j => (σ'.s (eI.symm j)).eval (Opposite.op ⊤),
    fun x => ?_⟩
  obtain ⟨j, hj⟩ := Stacks.SheafOfModules.exists_generatingSection_nonvanishing _ σ' x
  refine ⟨eI j, ?_⟩
  have hx : x ∈ (Stacks.SheafOfModules.nonvanishingOpen _ (σ'.s j) : Set X) := hj
  rw [Stacks.AmplePredicateBridge.coe_nonvanishingOpen_eval X _ (σ'.s j)] at hx
  simp only [Equiv.symm_apply_apply]
  exact hx

end GlobalGeneration

/-! ### Basepoint-free linear systems -/

section Positivity

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]

/-- A Cartier divisor whose sheaf is generated by finitely many global sections is basepoint
free. -/
private theorem isBasepointFree_of_forall_mem_nonvanishingOpen {D : Divisor X}
    (hD : D.IsCartier) {N : ℕ} (s : Fin (N + 1) → Γ(D.divisorialSheaf, ⊤))
    (hs : haveI := hD.isInvertibleModule_divisorialSheaf
      ∀ x : X, ∃ i, x ∈ Stacks.NonvanishingOpen.nonvanishingOpen X D.divisorialSheaf (s i)) :
    D.IsBasepointFree := by
  have := hD.isInvertibleModule_divisorialSheaf
  refine eq_bot_iff.mpr fun x hx => ?_
  obtain ⟨i, hi⟩ := hs x
  have hne : (s i : D.divisorialSubmodule ⊤) ≠ 0 := by
    intro h0
    have h0' : s i = 0 := h0
    rw [h0'] at hi
    change x ∈ Stacks.Ample.nonvanishingLocus D.divisorialSheaf 0 at hi
    rw [Stacks.Ample.nonvanishingLocus_zero] at hi
    exact hi
  exact (MMP.Mori.AmpleFloorLowering.notMem_supp_of_mem_nonvanishingOpen D hD _ hne x hi
    ((Divisor.mem_baseLocus_iff D x).mp hx _ hne)).elim

/-- The sum of two basepoint-free divisors is basepoint free. -/
private theorem isBasepointFree_add {M₁ M₂ : Divisor X} (h₁ : M₁.IsBasepointFree)
    (h₂ : M₂.IsBasepointFree) : (M₁ + M₂).IsBasepointFree := by
  have h := MMP.Positivity.baseLocus_add_le M₁ M₂
  rw [show M₁.baseLocus = ⊥ from h₁, show M₂.baseLocus = ⊥ from h₂, bot_sup_eq] at h
  exact eq_bot_iff.mpr h

/-- Positive multiples of a basepoint-free divisor are basepoint free. -/
private theorem isBasepointFree_nsmul {M : Divisor X} (h : M.IsBasepointFree) :
    ∀ n : ℕ, 0 < n → (n • M).IsBasepointFree
  | 0, h0 => absurd h0 (lt_irrefl 0)
  | 1, _ => by rwa [one_nsmul]
  | n + 2, _ => by
    rw [succ_nsmul]
    exact isBasepointFree_add (isBasepointFree_nsmul h (n + 1) n.succ_pos) h

/-- **Serre's theorem for divisors.** If `H` is an ample Cartier divisor and `F` is Cartier, then
`|n H + F|` is basepoint free for every sufficiently large `n`. -/
private theorem exists_forall_ge_isBasepointFree {H F : Divisor X} (hH : H.IsCartier)
    (hF : F.IsCartier) (hamp : H.IsAmple hH) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → (n • H + F).IsBasepointFree := by
  obtain ⟨n₀, hn₀⟩ := exists_forall_ge_forall_mem_nonvanishingOpen hH hF hamp
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨N, s, hs⟩ := hn₀ n hn
  exact isBasepointFree_of_forall_mem_nonvanishingOpen ((hH.nsmul n).add hF) s hs

/-- A basepoint-free linear system has finitely many members without common point. -/
private theorem exists_finset_sections_of_isBasepointFree {M : Divisor X}
    (h : M.IsBasepointFree) :
    ∃ (t : Finset X) (σ : X → M.divisorialSubmodule ⊤) (hσ : ∀ x, σ x ≠ 0),
      ∀ x : X, ∃ y ∈ t, x ∉ (M.zeroDivisor (σ y) (hσ y)).supp := by
  have hx : ∀ x : X, ∃ (σ : M.divisorialSubmodule ⊤) (hσ : σ ≠ 0),
      x ∉ (M.zeroDivisor σ hσ).supp := by
    intro x
    by_contra hcon
    push Not at hcon
    have hmem : x ∈ (M.baseLocus : Set X) := (Divisor.mem_baseLocus_iff M x).mpr hcon
    simp [show M.baseLocus = ⊥ from h] at hmem
  choose σ hσ hσx using hx
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X => ((M.zeroDivisor (σ x) (hσ x)).supp : Set X)ᶜ)
    (fun x => (M.zeroDivisor (σ x) (hσ x)).supp.isClosed.isOpen_compl)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hσx x⟩)
  refine ⟨t, σ, hσ, fun x => ?_⟩
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  exact ⟨y, hy, hxy⟩

/-- **A general member avoids a point.** If some member `s_j` of a finite family of sections of
`𝒪_X(M)` does not vanish at `x`, then for coefficient vectors `c` off the zero locus of a nonzero
linear form, the member `∑ cᵢ sᵢ` does not vanish at `x`: the vectors `c` with
`∑ cᵢ sᵢ(x) ∈ 𝔪_x 𝒪_X(M)_x` form a proper subspace. -/
private theorem exists_polynomial_mem_nonvanishingOpen {k : Type u} [Field k]
    (sX : X ⟶ Spec (.of k)) {M : Divisor X} (hM : M.IsCartier) {ι : Type*} [Fintype ι]
    (s : ι → M.divisorialSubmodule ⊤) (x : X) (j : ι)
    (hj : haveI := hM.isInvertibleModule_divisorialSheaf
      x ∈ Stacks.NonvanishingOpen.nonvanishingOpen X M.divisorialSheaf (s j)) :
    ∃ Q : MvPolynomial ι k, Q ≠ 0 ∧ ∀ c : ι → k, MvPolynomial.eval c Q ≠ 0 →
      haveI := hM.isInvertibleModule_divisorialSheaf
      x ∈ Stacks.NonvanishingOpen.nonvanishingOpen X M.divisorialSheaf
        (show M.divisorialSubmodule ⊤ from ∑ i, scalarsToGlobalSections k sX (c i) • s i) := by
  classical
  have := hM.isInvertibleModule_divisorialSheaf
  let σ : (ι → k) → Γ(M.divisorialSheaf, ⊤) := fun c =>
    (show M.divisorialSubmodule ⊤ from ∑ i, scalarsToGlobalSections k sX (c i) • s i)
  let p : Submodule k (ι → k) :=
    { carrier := {c | (M.divisorialSheaf.presheaf.Γgerm x).hom (σ c) ∈
        Stacks.ModuleStalk.maximalSmul M.divisorialSheaf x}
      add_mem' := by
        intro a b ha hb
        have h : σ (a + b) = σ a + σ b := by
          change (show M.divisorialSubmodule ⊤ from _) = _
          simp only [Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]
          rfl
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [h, map_add]
        exact Submodule.add_mem _ ha hb
      zero_mem' := by
        have h : σ 0 = 0 := by
          change (show M.divisorialSubmodule ⊤ from _) = _
          simp only [Pi.zero_apply, map_zero, zero_smul, Finset.sum_const_zero]
          rfl
        simp only [Set.mem_ofPred_eq]
        rw [h, map_zero]
        exact Submodule.zero_mem _
      smul_mem' := by
        intro a c hc
        have h : σ (a • c) = scalarsToGlobalSections k sX a • σ c := by
          change (show M.divisorialSubmodule ⊤ from _) = _
          simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, ← Finset.smul_sum]
          rfl
        simp only [Set.mem_ofPred_eq] at hc ⊢
        rw [h, Stacks.ModuleStalk.Γgerm_smul]
        exact Submodule.smul_mem _ _ hc }
  have hjp : (Pi.single j 1 : ι → k) ∉ p := by
    intro h
    have h1 : σ (Pi.single j 1) = (s j : Γ(M.divisorialSheaf, ⊤)) := by
      change (show M.divisorialSubmodule ⊤ from _) = _
      rw [Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp),
        Pi.single_eq_same, map_one, one_smul]
    have h' : (M.divisorialSheaf.presheaf.Γgerm x).hom (σ (Pi.single j 1)) ∈
        Stacks.ModuleStalk.maximalSmul M.divisorialSheaf x := h
    rw [h1] at h'
    exact hj h'
  obtain ⟨Q, hQ0, hQ⟩ :=
    MMP.Mori.AmpleFloorLowering.exists_polynomial_notMem_of_eval_ne_zero hjp
  refine ⟨Q, hQ0, fun c hc => ?_⟩
  by_contra hmem
  have hcp : (M.divisorialSheaf.presheaf.Γgerm x).hom (σ c) ∈
      Stacks.ModuleStalk.maximalSmul M.divisorialSheaf x := by
    by_contra h'
    exact hmem h'
  exact hQ c hc hcp

end Positivity

/-! ### Log discrepancies with respect to real boundaries -/

section LogDiscrepancy

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X]

/-- Every divisor over `X` with proper model has a log discrepancy with respect to `B`, once
`K_X + B` is `ℝ`-Cartier. -/
private theorem exists_isLogDiscrepancy [PerfectField k] [CompactSpace X]
    (hX : IsNormalVariety k sX) {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    {B : RDivisor X} (hKB : RDivisor.IsRCartier (Divisor.toRDivisor K + B))
    (D : DivisorOver k sX) (hD : IsProper D.f) :
    ∃ a, MMP.Intersection.IsLogDiscrepancy sX n B D a := by
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain ⟨m, r, C, hC, hsum⟩ := hKB
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isDominant
  have : CompactSpace D.Y := QuasiCompact.compactSpace_of_compactSpace D.f
  choose C' hC' using fun i => MMP.Threefold.Bridges.exists_isPullback_of_isDominant D.f (hC i)
  exact ⟨_, hX, hD, ω, hω0, ⟨K, hK, fun Γ => (hω Γ).symm⟩, m, r, C, C', hC, fun Γ => by
    rw [← hsum Γ, hω Γ, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor],
    fun i => ⟨_, hC' i⟩, rfl⟩

/-- **Log discrepancies are affine in the boundary.** Adding `t L` to the boundary, `L` Cartier,
lowers a log discrepancy by `t` times the coefficient of the pull-back of `L`. -/
private theorem isLogDiscrepancy_add_smul {n : ℕ} {B : RDivisor X} {D : DivisorOver k sX}
    {a : ℝ} (ha : MMP.Intersection.IsLogDiscrepancy sX n B D a) (t : ℝ) {L : Divisor X}
    (hL : L.IsCartier) {L' : Divisor D.Y}
    (hL' : haveI := D.isLocallyNoetherian
      haveI := D.isNormal
      ∃ hB, L.IsPullback D.f hB L') :
    MMP.Intersection.IsLogDiscrepancy sX n (B + t • Divisor.toRDivisor L) D
      (a - t * L'.coeff D.E) := by
  obtain ⟨hX, hp, ω, hω, hK, m, r, C, C', hC, hsum, hpb, rfl⟩ := ha
  refine ⟨hX, hp, ω, hω, hK, m + 1, Fin.cons t r, Fin.cons L C, Fin.cons L' C', fun i => ?_,
    fun Γ => ?_, fun i => ?_, ?_⟩
  · refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hL
    · simpa using hC j
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, DivisorWithCoeffs.coeff_add,
      DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor, smul_eq_mul]
    rw [← hsum Γ]
    ring
  · refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hL'
    · simpa using hpb j
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    ring

omit [IsIntegral X] in
/-- Adding a real multiple of a Cartier divisor keeps a divisor `ℝ`-Cartier. -/
private theorem isRCartier_add_smul {D : RDivisor X} (hD : RDivisor.IsRCartier D) (t : ℝ)
    {L : Divisor X} (hL : L.IsCartier) : RDivisor.IsRCartier (D + t • Divisor.toRDivisor L) := by
  obtain ⟨m, r, C, hC, hsum⟩ := hD
  refine ⟨m + 1, Fin.cons t r, Fin.cons L C, fun i => ?_, fun Γ => ?_⟩
  · refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hL
    · simpa using hC j
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, DivisorWithCoeffs.coeff_add,
      DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor, smul_eq_mul, hsum Γ]
    ring

end LogDiscrepancy

/-! ### Klt and plt are tested on a smooth model -/

/-- **Plt is tested on one smooth model with snc boundary.** Let `π : W ⟶ X` be a resolution of a
normal variety, `K_X + B` `ℝ`-Cartier, and `S_W` a finite set of prime divisors of `W` whose sum
is snc. Suppose every prime divisor of `W` has nonnegative log discrepancy over `(X, B)`, positive
when it is exceptional over `X`, and one when it is not in `S_W`, and that of two distinct
members of `S_W` one has positive log discrepancy. Then every exceptional divisor over `X` has
positive log discrepancy over `(X, B)`. -/
public theorem logDiscrepancy_pos_of_isSmoothResolution_of_isExceptional {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {X W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (hX : IsNormalVariety k sX) {n : ℕ}
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {B : RDivisor X}
    (hKB : RDivisor.IsRCartier (Divisor.toRDivisor K + B)) {π : W ⟶ X}
    (hπ : IsSmoothResolution sX π) (hW : IsNormalVariety k (π ≫ sX))
    (SW : Finset (MMP.Mori.PrimeDivisor W))
    (hSW : DivisorWithCoeffs.IsSNC (π ≫ sX) (∑ E ∈ SW, Finsupp.single E (1 : ℤ)))
    (hnn : ∀ (F : MMP.Mori.PrimeDivisor W) (a : ℝ), MMP.Intersection.IsLogDiscrepancy sX n B
      ⟨W, π, hW, hπ.isBirationalMorphism, F⟩ a → 0 ≤ a)
    (hpair : ∀ F ∈ SW, ∀ F' ∈ SW, F ≠ F' →
      (∀ a : ℝ, MMP.Intersection.IsLogDiscrepancy sX n B
        ⟨W, π, hW, hπ.isBirationalMorphism, F⟩ a → 0 < a) ∨
      (∀ a : ℝ, MMP.Intersection.IsLogDiscrepancy sX n B
        ⟨W, π, hW, hπ.isBirationalMorphism, F'⟩ a → 0 < a))
    (hexc : ∀ (F : MMP.Mori.PrimeDivisor W) (a : ℝ),
      (⟨W, π, hW, hπ.isBirationalMorphism, F⟩ : DivisorOver k sX).IsExceptional →
      MMP.Intersection.IsLogDiscrepancy sX n B ⟨W, π, hW, hπ.isBirationalMorphism, F⟩ a → 0 < a)
    (hone : ∀ F : MMP.Mori.PrimeDivisor W, F ∉ SW → ∀ a : ℝ,
      MMP.Intersection.IsLogDiscrepancy sX n B ⟨W, π, hW, hπ.isBirationalMorphism, F⟩ a →
        a = 1) :
    ∀ (d : ℕ) (E : DivisorOver k sX) (a : ℝ), E.IsExceptional →
      MMP.Intersection.IsLogDiscrepancy sX d B E a → 0 < a := by
  classical
  have : AlgebraicGeometry.IsVariety k sX := hX.1
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : AlgebraicGeometry.IsVariety k (π ≫ sX) := hW.1
  have : IsIntegral W := hW.1.toIsIntegral
  have : LocallyOfFiniteType (π ≫ sX) := hW.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (π ≫ sX)
  have : IsNormal W := hW.2
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (π ≫ sX)
  have : IsProper π := hπ.isProper
  have hπb := hπ.isBirationalMorphism
  have : IsDominant π := hπb.isDominant
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  have hdivω : divisorOfForm ω = K := Finsupp.ext fun P => by
    have := hω P
    rw [← DivisorWithCoeffs.coeff_apply, ← DivisorWithCoeffs.coeff_apply, coeff_divisorOfForm]
    exact this
  have hn : topologicalKrullDim X = n := hK.topologicalKrullDim_eq
  have hnW : topologicalKrullDim W = n := by
    rw [← hn]
    exact (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (π ≫ sX) hπb).symm
  have hω' : pullbackRationalPluriForms sX π ω ≠ 0 :=
    pullbackRationalPluriForms_ne_zero π hπb.functionFieldMap_bijective
      (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn) hω0
  have hKW : (divisorOfForm (pullbackRationalPluriForms sX π ω)).IsCanonicalDivisor
      (π ≫ sX) n := by
    obtain ⟨K₀, hK₀⟩ :=
      MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (π ≫ sX) hπ.isSmoothScheme hnW
    exact hK₀.of_linearlyEquivalent (by
      simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hW hK₀ hω')
  obtain ⟨m, r, C, hC, hsum⟩ := id hKB
  choose C' hC' using fun i => MMP.Threefold.Bridges.exists_isPullback_of_isDominant π (hC i)
  set DW : RDivisor W := ∑ i, r i • Divisor.toRDivisor (C' i) -
    Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sX π ω)) with hDW
  -- the log discrepancy of a prime divisor of `W` is one minus its coefficient in `B_W`
  have hF : ∀ F : MMP.Mori.PrimeDivisor W, MMP.Intersection.IsLogDiscrepancy sX n B
      ⟨W, π, hW, hπb, F⟩ (1 - DW.coeff F) := by
    intro F
    refine ⟨hX, hπ.isProper, ω, hω0, ⟨K, hK, fun Γ => (hω Γ).symm⟩, m, r, C, C', hC,
      fun Γ => ?_, fun i => ⟨_, hC' i⟩, ?_⟩
    · rw [← hsum Γ, hω Γ, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor]
    · rw [hDW, DivisorWithCoeffs.coeff_sub, MMP.Flips.coeff_sum_smul_toRDivisor,
        Divisor.coeff_toRDivisor, coeff_divisorOfForm]
      change _ = 1 + ((F.ordForm (pullbackRationalPluriForms sX π ω) : ℤ) : ℝ) - _
      ring
  have hle : ∀ F, DW.coeff F ≤ 1 := fun F => by linarith [hnn F _ (hF F)]
  have hsupp : DW.support ⊆ SW := fun F hF' => by
    by_contra hFS
    have h1 := hone F hFS _ (hF F)
    have h0 : DW.coeff F = 0 := by linarith
    rw [DivisorWithCoeffs.coeff_apply] at h0
    exact (Finsupp.mem_support_iff.mp hF') h0
  have hpairW : ∀ F ∈ SW, ∀ F' ∈ SW, F ≠ F' → DW.coeff F < 1 ∨ DW.coeff F' < 1 :=
    fun F hF₁ F' hF'₁ hne => (hpair F hF₁ F' hF'₁ hne).imp
      (fun h => by linarith [h _ (hF F)]) (fun h => by linarith [h _ (hF F')])
  have hpb : MMP.Flips.IsRCartierPullback π (Divisor.toRDivisor (divisorOfForm ω) + B)
      (Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sX π ω)) + DW) := by
    refine ⟨m, r, C, C', hC, Finsupp.ext fun Γ => ?_, fun i => ⟨_, hC' i⟩, ?_⟩
    · rw [← DivisorWithCoeffs.coeff_apply, ← DivisorWithCoeffs.coeff_apply,
        MMP.Flips.coeff_sum_smul_toRDivisor, ← hsum Γ, hdivω]
    · rw [hDW]
      abel
  intro d E a hE ha
  obtain ⟨E', hE'⟩ := exists_properDivisorOver_comap_eq π hπb ⟨E, ha.2.1⟩
  by_cases hE'x : E'.toDivisorOver.IsExceptional
  · -- `E` is exceptional over `W`, where `(W, B_W)` is plt
    refine logDiscrepancy_pos_of_isRCartierPullback hX π hW hπb hω0 (by rwa [hdivω])
      hpb hKW hE' (fun d E₀ a' hv ha' => ?_) ha
    exact logDiscrepancy_pos_of_isSNC_of_isExceptional hW hπ.isSmoothScheme hKW SW hsupp hSW hle
      hpairW (isExceptional_of_valuation_eq hW hv.symm hE'x) ha'
  · -- `E` is a prime divisor of `W`, exceptional over `X`
    obtain ⟨P, hP⟩ :=
      MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hW _ hE'x
    have hv : (⟨W, π, hW, hπb, P⟩ : DivisorOver k sX).valuation = E.valuation := by
      refine Eq.trans ?_ hE'
      ext g
      change P.divisorialValuation (functionFieldMap π g) = E'.valuation (functionFieldMap π g)
      rw [show E'.valuation = E'.toDivisorOver.valuation from rfl, hP]
      change _ = P.divisorialValuation (functionFieldMap (𝟙 W) _)
      rw [MMP.Mori.functionFieldMap_id_apply]
    obtain ⟨b, hb⟩ := exists_isLogDiscrepancy hX hK hKB ⟨W, π, hW, hπb, P⟩ hπ.isProper
    rw [MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha hb hv.symm]
    exact hexc P b (isExceptional_of_valuation_eq hX hv.symm hE) hb

/-- **Klt is tested on one smooth model with snc boundary.** Let `π : W ⟶ X` be a resolution of a
normal variety, `K_X + B` `ℝ`-Cartier, and `S_W` a finite set of prime divisors of `W` whose sum
is snc. If every prime divisor of `W` has positive log discrepancy over `(X, B)`, and log
discrepancy one when it is not in `S_W`, then every log discrepancy of `(X, B)` is positive. -/
public theorem logDiscrepancy_pos_of_isSmoothResolution {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {X W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (hX : IsNormalVariety k sX) {n : ℕ}
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {B : RDivisor X}
    (hKB : RDivisor.IsRCartier (Divisor.toRDivisor K + B)) {π : W ⟶ X}
    (hπ : IsSmoothResolution sX π) (hW : IsNormalVariety k (π ≫ sX))
    (SW : Finset (MMP.Mori.PrimeDivisor W))
    (hSW : DivisorWithCoeffs.IsSNC (π ≫ sX) (∑ E ∈ SW, Finsupp.single E (1 : ℤ)))
    (hpos : ∀ (F : MMP.Mori.PrimeDivisor W) (a : ℝ), MMP.Intersection.IsLogDiscrepancy sX n B
      ⟨W, π, hW, hπ.isBirationalMorphism, F⟩ a → 0 < a)
    (hone : ∀ F : MMP.Mori.PrimeDivisor W, F ∉ SW → ∀ a : ℝ,
      MMP.Intersection.IsLogDiscrepancy sX n B ⟨W, π, hW, hπ.isBirationalMorphism, F⟩ a →
        a = 1) :
    ∀ (d : ℕ) (E : DivisorOver k sX) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sX d B E a → 0 < a := by
  intro d E a ha
  by_cases hE : E.IsExceptional
  · exact logDiscrepancy_pos_of_isSmoothResolution_of_isExceptional hX hK hKB hπ hW SW hSW
      (fun F a ha => (hpos F a ha).le) (fun F _ _ _ _ => Or.inl (hpos F))
      (fun F a _ ha => hpos F a ha) hone d E a hE ha
  have : IsProper π := hπ.isProper
  have : LocallyOfFiniteType (π ≫ sX) := hW.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (π ≫ sX)
  have : IsNormal W := hW.2
  obtain ⟨P, hv⟩ :=
    MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hX E hE
  obtain ⟨F, hF, -⟩ := MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0}
    hX hW hπ.isBirationalMorphism P
  have hvF := MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq hX
    ⟨W, π, hW, hπ.isBirationalMorphism, F⟩ P hF
  obtain ⟨b, hb⟩ := exists_isLogDiscrepancy hX hK hKB ⟨W, π, hW, hπ.isBirationalMorphism, F⟩
    hπ.isProper
  rw [MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha hb (hv.trans hvF.symm)]
  exact hpos F b hb

/-! ### The ample multiple -/

/-- **A basepoint-free multiple of `A + δT`.** If `A` is an ample `ℚ`-divisor and `T` is
`ℚ`-Cartier, there is `δ₀ > 0` such that for every rational `0 < δ < δ₀`, arbitrarily large
multiples `N (A + δ T)` are basepoint-free Cartier divisors. With `D_A = m A` ample Cartier and
`G = q T` Cartier, `|j D_A + G|` and `|j D_A|` are free for `j ≥ j₀`, resp. `j ≥ j₁`, and
`N (A + δ T) = b (j₀ D_A + G) + c D_A` for suitable `b ≥ 1`, `c ≥ j₁` once
`δ < q / (m (j₀ + 1))`. -/
private theorem exists_isBasepointFree_eq_smul {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {A : QDivisor X} (hA : A.IsAmple)
    (T : Divisor X) (hT : ∃ q : ℕ, 0 < q ∧ ((q : ℤ) • T).IsCartier) :
    ∃ δ₀ : ℚ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∀ δ : ℚ, 0 < δ → δ < δ₀ → ∀ N₀ : ℕ,
      ∃ (N : ℕ) (M : Divisor X), N₀ < N ∧ M.IsCartier ∧ M.IsBasepointFree ∧
        Divisor.toQDivisor M = (N : ℚ) • (A + δ • Divisor.toQDivisor T) := by
  obtain ⟨q, hq, hqT⟩ := hT
  obtain ⟨m, hm, DA, hDA, hDAc, hamp⟩ := hA
  obtain ⟨j₀, hj₀⟩ := exists_forall_ge_isBasepointFree hDAc hqT hamp
  obtain ⟨j₁, hj₁⟩ := exists_forall_ge_isBasepointFree hDAc Divisor.isCartier_zero hamp
  have hδ₀ : (0 : ℚ) < (q : ℚ) / (m * (j₀ + 1)) := by positivity
  refine ⟨min 1 ((q : ℚ) / (m * (j₀ + 1))), lt_min one_pos hδ₀, min_le_left _ _,
    fun δ hδ hδlt N₀ => ?_⟩
  have hδlt' : δ < (q : ℚ) / (m * (j₀ + 1)) := hδlt.trans_le (min_le_right _ _)
  set p : ℕ := δ.num.toNat with hp_def
  set r : ℕ := δ.den with hr_def
  have hnum : (0 : ℤ) < δ.num := Rat.num_pos.mpr hδ
  have hpnum : (p : ℤ) = δ.num := Int.toNat_of_nonneg hnum.le
  have hp : 0 < p := by omega
  have hr : 0 < r := δ.den_pos
  have hδpr : δ = (p : ℚ) / r := by
    rw [← Rat.num_div_den δ]
    congr 1
    exact_mod_cast hpnum.symm
  have hlt : p * m * (j₀ + 1) < r * q := by
    have h1 : (p : ℚ) / r < (q : ℚ) / (m * (j₀ + 1)) := hδpr ▸ hδlt'
    rw [div_lt_div_iff₀ (by exact_mod_cast hr) (by positivity)] at h1
    have h2 : ((p * m * (j₀ + 1) : ℕ) : ℚ) < ((r * q : ℕ) : ℚ) := by push_cast; nlinarith [h1]
    exact_mod_cast h2
  obtain ⟨u, hu⟩ : ∃ u : ℕ, r * q = p * m * j₀ + u + 1 :=
    ⟨r * q - p * m * j₀ - 1, by
      have : p * m * j₀ + p * m ≤ r * q - 1 := by
        have := hlt
        rw [mul_add, mul_one] at this
        omega
      omega⟩
  set t : ℕ := N₀ + j₁ + 1 with ht
  set b : ℕ := p * m * t with hb_def
  set c : ℕ := t * (u + 1) with hc_def
  have hb : 0 < b := by positivity
  have hc : j₁ ≤ c := by
    rw [hc_def]
    nlinarith
  refine ⟨m * q * r * t, b • (j₀ • DA + (q : ℤ) • T) + (c • DA + 0), ?_,
    (((hDAc.nsmul j₀).add hqT).nsmul b).add ((hDAc.nsmul c).add Divisor.isCartier_zero),
    isBasepointFree_add (isBasepointFree_nsmul (hj₀ j₀ le_rfl) b hb) (hj₁ c hc), ?_⟩
  · have h1 : 1 ≤ m * q * r := by
      have := Nat.mul_pos (Nat.mul_pos hm hq) hr
      omega
    nlinarith
  · have hDAP : ∀ P, ((DA.coeff P : ℤ) : ℚ) = m * A.coeff P := fun P => by
      simpa using congrArg (fun G : QDivisor X => G.coeff P) hDA
    have hbc : ((b * j₀ + c : ℕ) : ℚ) = r * q * t := by
      have : b * j₀ + c = r * q * t := by
        rw [hb_def, hc_def, hu]
        ring
      exact_mod_cast this
    have hbc' : (b : ℚ) * j₀ + c = r * q * t := by exact_mod_cast hbc
    have hbq : (b : ℚ) = p * m * t := by rw [hb_def]; push_cast; ring
    have hNδ : (m : ℚ) * q * r * t * δ = m * q * t * p := by
      rw [hδpr]; field_simp
    refine Finsupp.ext fun P => ?_
    have h1 := Divisor.coeff_toQDivisor (b • (j₀ • DA + (q : ℤ) • T) + (c • DA + 0)) P
    have h2 := Divisor.coeff_toQDivisor T P
    have h3 := hDAP P
    rw [DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply] at h1 h2
    rw [DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply] at h3
    rw [h1]
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, nsmul_eq_mul,
      add_zero, h2]
    push_cast
    rw [h3]
    linear_combination (↑m * A P) * hbc' + (↑q * ((T P : ℤ) : ℚ)) * hbq - ((T P : ℤ) : ℚ) * hNδ

/-! ### A general member on the snc-preserving resolution -/

/-- **The strict transform is unique.** Along a birational morphism `π : W ⟶ X` of normal
varieties, two prime divisors of `W` whose generic points map to the generic point of one prime
divisor `P` of `X` are equal: both have the valuation of `P`. -/
private theorem eq_of_map_genericPoint_eq {k : Type u} [Field k] {X W : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] (hX : IsNormalVariety k sX) {π : W ⟶ X}
    (hW : IsNormalVariety k (π ≫ sX)) (hπ : IsBirationalMorphism π)
    {F F' : MMP.Mori.PrimeDivisor W} (P : MMP.Mori.PrimeDivisor X)
    (hF : π F.genericPoint = P.genericPoint) (hF' : π F'.genericPoint = P.genericPoint) :
    F = F' := by
  have : IsDominant π := hπ.isDominant
  have hv := (MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq hX
    ⟨W, π, hW, hπ, F⟩ P hF).trans
      (MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq hX
        ⟨W, π, hW, hπ, F'⟩ P hF').symm
  have hvW : (DivisorOver.ofPrimeDivisor k hW F).valuation =
      (DivisorOver.ofPrimeDivisor k hW F').valuation := by
    ext g
    obtain ⟨g, rfl⟩ := hπ.functionFieldMap_bijective.2 g
    change F.divisorialValuation (functionFieldMap (𝟙 W) (functionFieldMap π g)) =
      F'.divisorialValuation (functionFieldMap (𝟙 W) (functionFieldMap π g))
    rw [MMP.Mori.functionFieldMap_id_apply]
    exact congrArg (fun v : Valuation X.functionField ℤᵐ⁰ => v g) hv
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hW.1 hvW)

/-- A coefficient `γ - μ / N + z / N` of a lowered boundary is at most one, and less than one
unless `γ = 1` and `μ = 0`. -/
public theorem sub_div_add_div_le_one {γ μ z N : ℝ} (hγ : γ ≤ 1) (hμ : 0 ≤ μ) (hz : z ≤ 1)
    (hμγ : μ ≠ 0 → γ ≠ 0) (hγz : γ ≠ 0 → z = 0) (hN : 2 ≤ N) :
    γ - μ / N + z / N ≤ 1 ∧ ((γ = 1 → 0 < μ) → γ - μ / N + z / N < 1) := by
  have hN0 : 0 < N := by linarith
  by_cases hγ0 : γ = 0
  · have hμ0 : μ = 0 := Classical.byContradiction fun h => hμγ h hγ0
    have : z / N < 1 := (div_lt_one hN0).2 (by linarith)
    rw [hγ0, hμ0, zero_div, sub_zero, zero_add]
    exact ⟨this.le, fun _ => this⟩
  · rw [hγz hγ0, zero_div, add_zero]
    have hμN : 0 ≤ μ / N := div_nonneg hμ hN0.le
    refine ⟨by linarith, fun h1 => ?_⟩
    rcases hγ.lt_or_eq with h | h
    · linarith
    · linarith [div_pos (h1 h) hN0]

/-- **A general member of a free system keeps a dlt pair plt after lowering.** Let `(X, Γ)` be a
dlt pair with real boundary, and `M` an effective basepoint-free Cartier divisor supported in
`Supp Γ` with zero coefficient along at most one component of `Γ` of coefficient one. For
`N ≥ 2` and a finite set `S ⊆ X`, a general member `(σ)₀` of `|M|` is reduced, has no component
in `Supp Γ`, avoids `S`, and `B = Γ - M/N + (σ)₀/N` has coefficients at most one, less than one
along every prime divisor which is not a component of coefficient one of `Γ` along which `M` has
zero coefficient, with `K_X + B` `ℝ`-Cartier and every exceptional divisor over `X` of positive
log discrepancy. -/
public theorem exists_section_logDiscrepancy_pos_of_isExceptional {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {Γ : RDivisor X}
    (hΓ : IsRealDltPair sX Γ) {M : Divisor X} (hMc : M.IsCartier) (hMbpf : M.IsBasepointFree)
    (hM0 : ∀ P, 0 ≤ M.coeff P) (hMΓ : ∀ P, M.coeff P ≠ 0 → Γ.coeff P ≠ 0)
    (hM1 : ∀ P Q, Γ.coeff P = 1 → Γ.coeff Q = 1 → M.coeff P = 0 → M.coeff Q = 0 → P = Q)
    {N : ℕ} (hN : 2 ≤ N) (S : Set X) (hS : S.Finite) :
    ∃ (σ : M.divisorialSubmodule ⊤) (hσ : σ ≠ 0),
      (∀ P, (M.zeroDivisor σ hσ).coeff P ≤ 1) ∧
      (∀ P, Γ.coeff P ≠ 0 → (M.zeroDivisor σ hσ).coeff P = 0) ∧
      (∀ x ∈ S, x ∉ (M.zeroDivisor σ hσ).supp) ∧
      (∀ P, (Γ + (-(N : ℝ)⁻¹) • Divisor.toRDivisor M +
        (N : ℝ)⁻¹ • Divisor.toRDivisor (M.zeroDivisor σ hσ)).coeff P ≤ 1) ∧
      (∀ P, (Γ.coeff P = 1 → 0 < M.coeff P) → (Γ + (-(N : ℝ)⁻¹) • Divisor.toRDivisor M +
        (N : ℝ)⁻¹ • Divisor.toRDivisor (M.zeroDivisor σ hσ)).coeff P < 1) ∧
      (∃ (n : ℕ) (K : Divisor X), K.IsCanonicalDivisor sX n ∧
        RDivisor.IsRCartier (Divisor.toRDivisor K + (Γ + (-(N : ℝ)⁻¹) • Divisor.toRDivisor M +
          (N : ℝ)⁻¹ • Divisor.toRDivisor (M.zeroDivisor σ hσ)))) ∧
      ∀ (d : ℕ) (E : DivisorOver k sX) (a : ℝ), E.IsExceptional →
        MMP.Intersection.IsLogDiscrepancy sX d (Γ + (-(N : ℝ)⁻¹) • Divisor.toRDivisor M +
          (N : ℝ)⁻¹ • Divisor.toRDivisor (M.zeroDivisor σ hσ)) E a → 0 < a := by
  classical
  obtain ⟨⟨hX, hΓ0, ⟨n, K, hK, hKΓ⟩, -⟩, hΓ1, Z, hZsm, hZsnc, hZpos⟩ := hΓ
  have : AlgebraicGeometry.IsVariety k sX := hX.1
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  -- the snc-preserving resolution
  obtain ⟨W, π, hres, -, hSNC, hiso⟩ :=
    MMP.Resolution.exists_isLogResolution_isIso_restrict_of_isSNCClosedSubset sX hX Γ.support
  have hWv : AlgebraicGeometry.IsVariety k (π ≫ sX) := hres.isVariety_source
  have : IsIntegral W := hWv.toIsIntegral
  have : LocallyOfFiniteType (π ≫ sX) := hWv.toLocallyOfFiniteType
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (π ≫ sX)
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (π ≫ sX)
  have : AlgebraicGeometry.IsNoetherian W := {}
  have : IsProper π := hres.isProjective.isProper
  have hπb : IsBirationalMorphism π := hres.isBirationalMorphism
  have : IsDominant π := hπb.isDominant
  have hπs : IsSmoothResolution sX π := ⟨inferInstance, hπb, hres.isSmoothScheme⟩
  obtain ⟨hW, -, -⟩ := hπs.isNormalVariety hX
  have : IsNormal W := hW.2
  -- `π` is an isomorphism over `U = X ∖ Z`, so `Ex(π)` lies over `Z`
  set U : X.Opens := Z.compl with hU
  have hUsnc : MMP.Resolution.IsSNCClosedSubset (U.ι ≫ sX)
      (U.ι ⁻¹' (Γ.support.sup fun E => (E.idealSheaf.support : Set X))) := by
    have h := hZsnc
    rw [MMP.Threefold.Bridges.AmpleFloorLowering.inverseTransformDivisor_ι_eq_restrictOpen]
      at h
    exact MMP.Resolution.AmpleFloorLowering.isSNCClosedSubset_preimage_of_isSNC_restrictOpen
      sX h
  have hπU : IsIso (π ∣_ U) := hiso U hZsm hUsnc
  have hEx : ∀ w ∈ (exceptionalSet π : Set W), π w ∈ (Z : Set X) := fun w hw => by
    by_contra hwZ
    exact hw (le_biregularLocus hπU (show π w ∈ U from hwZ))
  -- the snc divisor `S_W` of all prime divisors in `Ex(π) ∪ π⁻¹(Supp Γ)`
  set C : Set W := (exceptionalSet π : Set W) ∪
    π ⁻¹' (Γ.support.sup fun E => (E.idealSheaf.support : Set X)) with hC
  have hfin := MMP.Resolution.AmpleFloorLowering.finite_setOf_support_subset hSNC
  set SW : Finset (MMP.Mori.PrimeDivisor W) := hfin.toFinset with hSW
  have hmemSW : ∀ F : MMP.Mori.PrimeDivisor W, F ∈ SW ↔ (F.support : Set W) ⊆ C := fun F => by
    rw [hSW, Set.Finite.mem_toFinset]
    rfl
  have hSWsnc : DivisorWithCoeffs.IsSNC (π ≫ sX) (∑ E ∈ SW, Finsupp.single E (1 : ℤ)) :=
    MMP.Resolution.AmpleFloorLowering.isSNC_sum_single_of_support_subset
      hres.isSmoothScheme hSNC SW fun P hP => (hmemSW P).1 hP
  -- finitely many members of `|M|` without common point
  obtain ⟨t₀, σ₀, hσ₀, hcov⟩ := exists_finset_sections_of_isBasepointFree hMbpf
  let s : t₀ → M.divisorialSubmodule ⊤ := fun i => σ₀ i
  have hs : ∀ x : X, ∃ (i : t₀) (hi : s i ≠ 0), x ∉ (M.zeroDivisor (s i) hi).supp := fun x => by
    obtain ⟨y, hy, hxy⟩ := hcov x
    exact ⟨⟨y, hy⟩, hσ₀ y, hxy⟩
  have := hMc.isInvertibleModule_divisorialSheaf
  -- Bertini, nonvanishing and avoidance conditions on the coefficients
  obtain ⟨Q₁, hQ₁0, hQ₁⟩ :=
    MMP.Mori.exists_polynomial_pullback_zeroDivisor_eq_sum_isSNC hX.1
      hπs s hs SW hSWsnc
  obtain ⟨x₀⟩ : Nonempty X := inferInstance
  obtain ⟨j₀, hj₀, -⟩ := hs x₀
  obtain ⟨Q₂, hQ₂0, hQ₂⟩ :=
    MMP.Mori.AmpleFloorLowering.exists_polynomial_sum_smul_ne_zero sX s j₀ hj₀
  have hav : ∀ x : X, ∃ Q : MvPolynomial t₀ k, Q ≠ 0 ∧ ∀ c : t₀ → k,
      MvPolynomial.eval c Q ≠ 0 →
        x ∈ Stacks.NonvanishingOpen.nonvanishingOpen X M.divisorialSheaf
          (show M.divisorialSubmodule ⊤ from ∑ i, scalarsToGlobalSections k sX (c i) • s i) :=
    fun x => by
      obtain ⟨j, hj, hxj⟩ := hs x
      exact exists_polynomial_mem_nonvanishingOpen sX hMc s x j
        (MMP.Mori.mem_nonvanishingOpen_of_notMem_supp M hMc (s j) hj x
          hxj)
  choose Qx hQx0 hQx using hav
  set Q : MvPolynomial t₀ k := Q₁ * Q₂ * ∏ x ∈ hS.toFinset, Qx x with hQ
  have hQ0 : Q ≠ 0 :=
    mul_ne_zero (mul_ne_zero hQ₁0 hQ₂0) (Finset.prod_ne_zero_iff.mpr fun x _ => hQx0 x)
  obtain ⟨c, hc⟩ : ∃ c : t₀ → k, MvPolynomial.eval c Q ≠ 0 := by
    by_contra h
    push Not at h
    exact hQ0 (MvPolynomial.funext fun c => by rw [h c, map_zero])
  rw [hQ, map_mul, map_mul, map_prod] at hc
  have hc₁ : MvPolynomial.eval c Q₁ ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hc)
  have hc₂ : MvPolynomial.eval c Q₂ ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hc)
  have hcx : ∀ x ∈ hS.toFinset, MvPolynomial.eval c (Qx x) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hc)
  -- the general member
  set σ : M.divisorialSubmodule ⊤ := ∑ i, scalarsToGlobalSections k sX (c i) • s i with hσdef
  have hσ : σ ≠ 0 := hQ₂ c hc₂
  set Zσ := M.zeroDivisor σ hσ with hZσ
  have hσS : ∀ x ∈ S, x ∉ Zσ.supp := fun x hx =>
    MMP.Mori.AmpleFloorLowering.notMem_supp_of_mem_nonvanishingOpen M hMc σ hσ x
      (hQx x c (hcx x (hS.mem_toFinset.mpr hx)))
  have hBσ : ∀ Z' : irreducibleComponents W, π (componentGenericPoint W Z') ∉ Zσ.supp :=
    fun Z' => MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant π _ Z'
  have hZc : Zσ.IsCartier := by
    rw [hZσ, Divisor.zeroDivisor_eq]
    exact (Divisor.isCartier_principalDivisor _).add hMc
  obtain ⟨H', hH'⟩ := hZc.exists_isPullback hBσ
  obtain ⟨T, hT, hTSW, hTsnc, -⟩ := hQ₁ c hc₁ hσ hBσ H' hH'
  have hH'c : ∀ E, H'.coeff E = if E ∈ T then 1 else 0 := fun E => by
    rw [hT]
    exact MMP.Mori.AmpleFloorLowering.coeff_sum_single T E
  -- strict transforms of the prime divisors of `X`
  have hstrict : ∀ P : MMP.Mori.PrimeDivisor X, ∃ E : MMP.Mori.PrimeDivisor W,
      π E.genericPoint = P.genericPoint ∧ Zσ.coeff P = H'.coeff E := fun P => by
    obtain ⟨E, heq, hisoE, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hX hW hπb P
    exact ⟨E, heq, (MMP.Positivity.coeff_eq_of_isPullback E P heq hZc hH').symm⟩
  have hZle : ∀ P, Zσ.coeff P ≤ 1 := fun P => by
    obtain ⟨E, -, hE⟩ := hstrict P
    rw [hE, hH'c]
    split_ifs <;> norm_num
  have hsuppΓW : ∀ (P : MMP.Mori.PrimeDivisor X) (F : MMP.Mori.PrimeDivisor W), Γ.coeff P ≠ 0 →
      π F.genericPoint = P.genericPoint → F ∈ SW := by
    intro P F hP hF
    rw [hmemSW, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    refine hSNC.1.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr (Or.inr ?_))
    change π F.genericPoint ∈ (Γ.support.sup fun E => (E.idealSheaf.support : Set X))
    rw [hF]
    have hPΓ : P ∈ Γ.support := Finsupp.mem_support_iff.mpr (by
      rwa [← DivisorWithCoeffs.coeff_apply])
    exact (Finset.le_sup (f := fun E => (E.idealSheaf.support : Set X)) hPΓ)
      (MMP.Positivity.PrimeDivisor.genericPoint_mem_support' P)
  have hZΓ : ∀ P, Γ.coeff P ≠ 0 → Zσ.coeff P = 0 := fun P hP => by
    obtain ⟨E, hE, hZE⟩ := hstrict P
    rw [hZE, hH'c, ite_eq_right]
    exact fun hET => Finset.disjoint_left.mp hTSW hET (hsuppΓW P E hP hE)
  -- the lowered boundary
  set B : RDivisor X := Γ + (-(N : ℝ)⁻¹) • Divisor.toRDivisor M +
    (N : ℝ)⁻¹ • Divisor.toRDivisor Zσ with hBdef
  have hBc : ∀ P, B.coeff P = Γ.coeff P - (M.coeff P : ℝ) / N + (Zσ.coeff P : ℝ) / N :=
    fun P => by
      simp only [hBdef, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
        Divisor.coeff_toRDivisor, smul_eq_mul]
      ring
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hB1 : ∀ P, B.coeff P ≤ 1 ∧ ((Γ.coeff P = 1 → 0 < M.coeff P) → B.coeff P < 1) :=
      fun P => by
    rw [hBc]
    have h := sub_div_add_div_le_one (hΓ1 P) (by exact_mod_cast hM0 P : (0 : ℝ) ≤ M.coeff P)
      (by exact_mod_cast hZle P : (Zσ.coeff P : ℝ) ≤ 1) (fun h => hMΓ P (by exact_mod_cast h))
      (fun h => by exact_mod_cast hZΓ P h) hN2
    exact ⟨h.1, fun h' => h.2 fun h1 => by exact_mod_cast h' h1⟩
  have hKB : RDivisor.IsRCartier (Divisor.toRDivisor K + B) := by
    have h := isRCartier_add_smul (isRCartier_add_smul hKΓ (-(N : ℝ)⁻¹) hMc) ((N : ℝ)⁻¹) hZc
    simpa only [hBdef, add_assoc] using h
  -- log discrepancies of the prime divisors of `W`
  have hlogF : ∀ (F : MMP.Mori.PrimeDivisor W) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sX n B ⟨W, π, hW, hπs.isBirationalMorphism, F⟩ a →
        0 ≤ a ∧ ((⟨W, π, hW, hπs.isBirationalMorphism, F⟩ : DivisorOver k sX).IsExceptional →
          0 < a) ∧ (F ∉ SW ∪ T → a = 1) ∧
        (a = 0 → ∃ P : MMP.Mori.PrimeDivisor X, π F.genericPoint = P.genericPoint ∧
          Γ.coeff P = 1 ∧ M.coeff P = 0) := by
    intro F a ha
    by_cases hFe : (⟨W, π, hW, hπs.isBirationalMorphism, F⟩ : DivisorOver k sX).IsExceptional
    · have hFsupp : (F.support : Set W) ⊆ (exceptionalSet π : Set W) :=
        MMP.Positivity.support_subset_exceptionalSet F hFe
      have hFSW : F ∈ SW := (hmemSW F).2 (hFsupp.trans Set.subset_union_left)
      suffices h : 0 < a from ⟨h.le, fun _ => h,
        fun h' => absurd (Finset.mem_union_left _ hFSW) h', fun h0 => absurd h0 h.ne'⟩
      obtain ⟨aΓ, haΓ⟩ := exists_isLogDiscrepancy hX hK hKΓ
        (⟨W, π, hW, hπs.isBirationalMorphism, F⟩ : DivisorOver k sX) (inferInstance : IsProper π)
      obtain ⟨M', hM'⟩ := hMc.exists_isPullback
        (fun Z' => MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant π M Z')
      have h2 := isLogDiscrepancy_add_smul (isLogDiscrepancy_add_smul haΓ (-(N : ℝ)⁻¹) hMc
        ⟨_, hM'⟩) ((N : ℝ)⁻¹) hZc ⟨_, hH'⟩
      have heq := MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha h2
      have hcenter : ((⟨W, π, hW, hπs.isBirationalMorphism, F⟩ : DivisorOver k sX).center :
          Set X) ⊆ Z := by
        rw [DivisorOver.center_eq_closure_genericPoint]
        exact Z.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr
          (hEx _ (hFsupp
            (MMP.Positivity.PrimeDivisor.genericPoint_mem_support' F))))
      have haΓpos := hZpos n _ hcenter aΓ haΓ
      have hH'F : H'.coeff F = 0 := by
        rw [hH'c, ite_eq_right]
        exact fun hFT => Finset.disjoint_left.mp hTSW hFT hFSW
      have hM'F : 0 ≤ M'.coeff F :=
        MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn hMc (V := ⊤)
          (fun P _ => hM0 P) hM' F ((F.genericPoint_mem_iff _).mp trivial)
      have hM'F' : (0 : ℝ) ≤ M'.coeff F := by exact_mod_cast hM'F
      have hinv : (0 : ℝ) ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr hNpos.le
      rw [heq]
      change 0 < aΓ - -(N : ℝ)⁻¹ * (M'.coeff F : ℝ) - (N : ℝ)⁻¹ * (H'.coeff F : ℝ)
      rw [hH'F]
      push_cast
      nlinarith
    · obtain ⟨P, hv⟩ :=
        MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hX _ hFe
      have hb := isLogDiscrepancy_ofPrimeDivisor hX hK hKB P
      rw [MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha hb hv]
      have hηF : π F.genericPoint = P.genericPoint :=
        MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hX hv
      refine ⟨by linarith [(hB1 P).1], fun h => absurd h hFe, fun hF => ?_, fun h0 => ?_⟩
      swap
      · refine ⟨P, hηF, ?_⟩
        by_contra h
        have h' : Γ.coeff P = 1 → 0 < M.coeff P := fun hP1 =>
          (hM0 P).lt_of_ne fun hM => h ⟨hP1, hM.symm⟩
        linarith [(hB1 P).2 h']
      have hΓP : Γ.coeff P = 0 :=
        Classical.byContradiction fun h => hF (Finset.mem_union_left _ (hsuppΓW P F h hηF))
      have hMP : M.coeff P = 0 := Classical.byContradiction fun h => hMΓ P h hΓP
      have hZP : Zσ.coeff P = 0 := by
        by_contra h
        apply hF
        refine Finset.mem_union_right _ ?_
        have hmem : P.genericPoint ∈ (Zσ.supp : Set X) :=
          DivisorWithCoeffs.support_subset_supp h
            (MMP.Positivity.PrimeDivisor.genericPoint_mem_support' P)
        have hsupp := MMP.Flips.supp_eq_preimage_supp_of_isPullback hZc
          (Divisor.zeroDivisor_nonneg M σ hσ) hH'
        have hmem' : F.genericPoint ∈ (H'.supp : Set W) := by
          rw [hsupp]
          change π F.genericPoint ∈ (Zσ.supp : Set X)
          rw [hηF]
          exact hmem
        obtain ⟨E, hE, hFE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem'
        have hFE' := MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hFE
        rw [hH'c] at hE
        split_ifs at hE with hET
        · rwa [← hFE']
        · exact absurd rfl hE
      rw [hBc, hΓP, hMP, hZP]
      push_cast
      ring
  -- of two distinct prime divisors of `W`, one has positive log discrepancy
  have hpair : ∀ F ∈ SW ∪ T, ∀ F' ∈ SW ∪ T, F ≠ F' →
      (∀ a : ℝ, MMP.Intersection.IsLogDiscrepancy sX n B
        ⟨W, π, hW, hπs.isBirationalMorphism, F⟩ a → 0 < a) ∨
      (∀ a : ℝ, MMP.Intersection.IsLogDiscrepancy sX n B
        ⟨W, π, hW, hπs.isBirationalMorphism, F'⟩ a → 0 < a) := by
    intro F _ F' _ hne
    by_contra h
    simp only [not_or, not_forall, not_lt] at h
    obtain ⟨⟨a, ha, ha0⟩, ⟨a', ha', ha0'⟩⟩ := h
    obtain ⟨P, hP, hP1, hP0⟩ := (hlogF F a ha).2.2.2 (le_antisymm ha0 (hlogF F a ha).1)
    obtain ⟨P', hP', hP'1, hP'0⟩ :=
      (hlogF F' a' ha').2.2.2 (le_antisymm ha0' (hlogF F' a' ha').1)
    obtain rfl := hM1 P P' hP1 hP'1 hP0 hP'0
    exact hne (eq_of_map_genericPoint_eq hX hW hπb P hP hP')
  refine ⟨σ, hσ, hZle, hZΓ, hσS, fun P => (hB1 P).1, fun P h => (hB1 P).2 h,
    ⟨n, K, hK, hKB⟩, ?_⟩
  exact logDiscrepancy_pos_of_isSmoothResolution_of_isExceptional hX hK hKB hπs hW (SW ∪ T)
    (by rwa [Finset.union_comm]) (fun F a ha => (hlogF F a ha).1) hpair
    (fun F a hF ha => (hlogF F a ha).2.1 hF) (fun F hF a ha => (hlogF F a ha).2.2.1 hF)

/-- A pair with real boundary whose coefficients are less than one, with `K_X + B` `ℝ`-Cartier and
positive log discrepancies along the exceptional divisors, is klt: a non-exceptional divisor has
the valuation of a prime divisor `P` of `X`, and log discrepancy `1 - coeff_P B`. -/
private theorem isRealKltPair_of_logDiscrepancy_pos_of_isExceptional {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] (hX : IsNormalVariety k sX) {n : ℕ}
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {B : RDivisor X}
    (hKB : RDivisor.IsRCartier (Divisor.toRDivisor K + B)) (h1 : ∀ P, B.coeff P < 1)
    (hexc : ∀ (d : ℕ) (E : DivisorOver k sX) (a : ℝ), E.IsExceptional →
      MMP.Intersection.IsLogDiscrepancy sX d B E a → 0 < a) :
    IsRealKltPair sX B := by
  refine ⟨hX, h1, ⟨n, K, hK, hKB⟩, fun d E a ha => ?_⟩
  by_cases hE : E.IsExceptional
  · exact hexc d E a hE ha
  obtain ⟨P, hv⟩ :=
    MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hX E hE
  rw [MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha
    (isLogDiscrepancy_ofPrimeDivisor hX hK hKB P) hv]
  linarith [h1 P]

/-- **A general member of a free system keeps a dlt pair klt after lowering.** Let `(X, Γ)` be a
dlt pair with real boundary, and `M` an effective basepoint-free Cartier divisor supported in
`Supp Γ` with positive coefficient along every component of `Γ` of coefficient one. For `N ≥ 2`
and a finite set `S ⊆ X`, a general member `(σ)₀` of `|M|` is reduced, has no component in
`Supp Γ`, avoids `S`, and `Γ - M/N + (σ)₀/N` is klt. -/
public theorem exists_section_isRealKltPair {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {Γ : RDivisor X} (hΓ : IsRealDltPair sX Γ)
    {M : Divisor X} (hMc : M.IsCartier) (hMbpf : M.IsBasepointFree)
    (hM0 : ∀ P, 0 ≤ M.coeff P) (hMΓ : ∀ P, M.coeff P ≠ 0 → Γ.coeff P ≠ 0)
    (hM1 : ∀ P, Γ.coeff P = 1 → 0 < M.coeff P) {N : ℕ} (hN : 2 ≤ N)
    (S : Set X) (hS : S.Finite) :
    ∃ (σ : M.divisorialSubmodule ⊤) (hσ : σ ≠ 0),
      (∀ P, (M.zeroDivisor σ hσ).coeff P ≤ 1) ∧
      (∀ P, Γ.coeff P ≠ 0 → (M.zeroDivisor σ hσ).coeff P = 0) ∧
      (∀ x ∈ S, x ∉ (M.zeroDivisor σ hσ).supp) ∧
      IsRealKltPair sX (Γ + (-(N : ℝ)⁻¹) • Divisor.toRDivisor M +
        (N : ℝ)⁻¹ • Divisor.toRDivisor (M.zeroDivisor σ hσ)) := by
  obtain ⟨σ, hσ, hZle, hZΓ, hσS, -, hlt, ⟨n, K, hK, hKB⟩, hexc⟩ :=
    exists_section_logDiscrepancy_pos_of_isExceptional hΓ hMc hMbpf hM0 hMΓ
      (fun P _ hP1 _ hP0 _ => absurd hP0 (hM1 P hP1).ne') hN S hS
  exact ⟨σ, hσ, hZle, hZΓ, hσS, isRealKltPair_of_logDiscrepancy_pos_of_isExceptional hΓ.1.1 hK
    hKB (fun P => hlt P (hM1 P)) hexc⟩

end MMP.Fourfold.AmpleFloorLowering

/-! ### The lowering -/

namespace MMP.Fourfold

open MMP.Mori AmpleFloorLowering

/-- **Lowering the reduced boundary using an ample component.** Let `X` be a normal
`ℚ`-factorial projective variety over an algebraically closed field of characteristic zero,
`(X, Γ)` a dlt pair with real boundary, and `A ≤ Γ` an effective ample `ℚ`-divisor with no
component in `T = ⌊Γ⌋`. Then there is `δ₀ > 0` such that for every rational `0 < δ < δ₀`, every
`ε > 0` and every finite set `S` of points of `X` with proper closures, there is an effective
`ℚ`-divisor `A' ∼_ℚ A + δT` with coefficients `< ε` whose support contains no point of `S`, and
such that `Γ - A - δT + A'` is effective and `(X, Γ - A - δT + A')` is klt. -/
@[mmp "lem_fourfold_ample_floor_lowering"]
public theorem IsRealDltPair.exists_isRealKltPair_sub_add_of_isAmple
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (hXq : IsQFactorial sX) (hXproj : MMP.Mori.IsProjectiveVariety k sX)
    {Γ : RDivisor X} (hΓ : IsRealDltPair sX Γ)
    {A : QDivisor X} (hA : A.IsAmple) (hA0 : ∀ P, 0 ≤ A.coeff P)
    (hAΓ : ∀ P, (A.coeff P : ℝ) ≤ Γ.coeff P)
    (hAT : ∀ P, A.coeff P ≠ 0 → (DivisorWithCoeffs.roundDown Γ).coeff P = 0) :
    ∃ δ₀ : ℚ, 0 < δ₀ ∧ ∀ δ : ℚ, 0 < δ → δ < δ₀ →
      ∀ ε : ℚ, 0 < ε → ∀ S : Set X, S.Finite → (∀ x ∈ S, closure {x} ≠ (Set.univ : Set X)) →
        ∃ A' : QDivisor X,
          (∀ P, 0 ≤ A'.coeff P) ∧ (∀ P, A'.coeff P < ε) ∧ (∀ x ∈ S, x ∉ A'.supp) ∧
          A'.QLinearlyEquivalent
            (A + δ • Divisor.toQDivisor (DivisorWithCoeffs.roundDown Γ)) ∧
          (∀ P, 0 ≤ (Γ - QDivisor.toRDivisor
              (A + δ • Divisor.toQDivisor (DivisorWithCoeffs.roundDown Γ)) +
              QDivisor.toRDivisor A').coeff P) ∧
          IsRealKltPair sX (Γ - QDivisor.toRDivisor
              (A + δ • Divisor.toQDivisor (DivisorWithCoeffs.roundDown Γ)) +
              QDivisor.toRDivisor A') := by
  classical
  have hΓ0 : ∀ P, 0 ≤ Γ.coeff P := hΓ.1.2.1
  have hΓ1 : ∀ P, Γ.coeff P ≤ 1 := hΓ.2.1
  set T : Divisor X := DivisorWithCoeffs.roundDown Γ with hTdef
  have hTc : ∀ P, T.coeff P = if Γ.coeff P = 1 then 1 else 0 := fun P => by
    rw [hTdef, DivisorWithCoeffs.coeff_roundDown]
    split_ifs with h
    · rw [h, Int.floor_one]
    · rw [Int.floor_eq_zero_iff]
      exact ⟨hΓ0 P, lt_of_le_of_ne (hΓ1 P) h⟩
  obtain ⟨δ₀, hδ₀, hδ₀1, hδfun⟩ := exists_isBasepointFree_eq_smul hA T (by
    obtain ⟨q, hq, h⟩ := hXq.2 T
    exact ⟨q, hq, h⟩)
  refine ⟨δ₀, hδ₀, fun δ hδ hδlt ε hε S hS _ => ?_⟩
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, (ε⁻¹ : ℚ) < N₀ := exists_nat_gt _
  obtain ⟨N, M, hNN₀, hMc, hMbpf, hMeq⟩ := hδfun δ hδ hδlt (N₀ + 2)
  have hNq : (0 : ℚ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hMP : ∀ P, (M.coeff P : ℚ) = N * (A.coeff P + δ * T.coeff P) := fun P => by
    have h := congrArg (fun G : QDivisor X => G.coeff P) hMeq
    simp at h
    rw [h]
    ring
  have hAT' : ∀ P, Γ.coeff P = 1 → A.coeff P = 0 := fun P h => by
    by_contra hA'
    have := hAT P hA'
    rw [hTdef] at hTc
    rw [hTc P, ite_eq_left h] at this
    exact one_ne_zero this
  have hM0 : ∀ P, 0 ≤ M.coeff P := fun P => by
    have h : (0 : ℚ) ≤ M.coeff P := by
      rw [hMP, hTc]
      have := hA0 P
      split_ifs <;> positivity
    exact_mod_cast h
  have hMΓ : ∀ P, M.coeff P ≠ 0 → Γ.coeff P ≠ 0 := fun P hM hΓP => by
    apply hM
    have hAP : A.coeff P = 0 := le_antisymm (by exact_mod_cast (hAΓ P).trans hΓP.le) (hA0 P)
    have h : (M.coeff P : ℚ) = 0 := by
      rw [hMP, hTc, ite_eq_right (by rw [hΓP]; exact zero_ne_one), hAP]
      simp
    exact_mod_cast h
  have hM1 : ∀ P, Γ.coeff P = 1 → 0 < M.coeff P := fun P h => by
    have h' : (0 : ℚ) < M.coeff P := by
      rw [hMP, hTc, ite_eq_left h, hAT' P h]
      push_cast
      positivity
    exact_mod_cast h'
  obtain ⟨σ, hσ, hZle, hZΓ, hσS, hklt⟩ :=
    exists_section_isRealKltPair hΓ hMc hMbpf hM0 hMΓ hM1 (N := N) (by omega) S hS
  set Zσ := M.zeroDivisor σ hσ with hZσ
  have hZ0 : ∀ P, 0 ≤ Zσ.coeff P := fun P => Divisor.zeroDivisor_nonneg M σ hσ P
  have hA'c : ∀ P, (((N : ℚ)⁻¹) • Divisor.toQDivisor Zσ).coeff P = (Zσ.coeff P : ℚ) / N :=
    fun P => by simp [div_eq_inv_mul]
  -- the boundary
  have hbd : Γ - QDivisor.toRDivisor (A + δ • Divisor.toQDivisor T) +
      QDivisor.toRDivisor (((N : ℚ)⁻¹) • Divisor.toQDivisor Zσ) =
      Γ + (-(N : ℝ)⁻¹) • Divisor.toRDivisor M + (N : ℝ)⁻¹ • Divisor.toRDivisor Zσ := by
    refine Finsupp.ext fun P => ?_
    rw [← DivisorWithCoeffs.coeff_apply, ← DivisorWithCoeffs.coeff_apply]
    have hMP' : (M.coeff P : ℝ) = N * ((A.coeff P : ℝ) + δ * T.coeff P) := by
      exact_mod_cast hMP P
    simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_sub,
      DivisorWithCoeffs.coeff_smul, QDivisor.coeff_toRDivisor, Divisor.coeff_toRDivisor,
      Divisor.coeff_toQDivisor, smul_eq_mul, hMP']
    push_cast
    field_simp
    ring
  refine ⟨((N : ℚ)⁻¹) • Divisor.toQDivisor Zσ, fun P => ?_, fun P => ?_, fun x hx => ?_, ?_,
    fun P => ?_, ?_⟩
  · rw [hA'c]
    exact div_nonneg (by exact_mod_cast hZ0 P) hNq.le
  · rw [hA'c]
    have hZ1 : (Zσ.coeff P : ℚ) ≤ 1 := by exact_mod_cast hZle P
    have h1 : (Zσ.coeff P : ℚ) / N ≤ 1 / N := div_le_div_of_nonneg_right hZ1 hNq.le
    have h2 : (1 : ℚ) / N < ε := by
      rw [div_lt_iff₀ hNq]
      have hN₀' : (N₀ : ℚ) < N := by exact_mod_cast (by omega : N₀ < N)
      have := (inv_lt_iff_one_lt_mul₀ hε).mp (hN₀.trans hN₀')
      linarith
    linarith
  · intro hmem
    apply hσS x hx
    obtain ⟨E, hE, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
    rw [hA'c] at hE
    have hZE : Zσ.coeff E ≠ 0 := fun h => hE (by rw [h]; simp)
    exact DivisorWithCoeffs.support_subset_supp hZE hxE
  · refine ⟨N, by omega, (Divisor.isUnit_sectionToRationalFunctions hσ).unit, ?_⟩
    refine Finsupp.ext fun P => ?_
    rw [← DivisorWithCoeffs.coeff_apply, ← DivisorWithCoeffs.coeff_apply]
    have hZP : (Zσ.coeff P : ℚ) =
        ((principalDivisor (Divisor.isUnit_sectionToRationalFunctions hσ).unit).coeff P : ℚ) +
          M.coeff P := by
      rw [hZσ, Divisor.zeroDivisor_eq, DivisorWithCoeffs.coeff_add]
      push_cast
      ring
    simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_sub,
      DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, smul_eq_mul, zsmul_eq_mul]
    have hMP2 := hMP P
    push_cast
    rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hNq.ne', one_mul]
    linear_combination hZP + hMP2
  · rw [hbd, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_add,
      DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor,
      Divisor.coeff_toRDivisor, smul_eq_mul, smul_eq_mul]
    have hMP' : (M.coeff P : ℝ) = N * ((A.coeff P : ℝ) + δ * T.coeff P) := by
      exact_mod_cast hMP P
    have hZ0' : (0 : ℝ) ≤ Zσ.coeff P := by exact_mod_cast hZ0 P
    have hinv : (0 : ℝ) ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr hNr.le
    have hcancel : (N : ℝ)⁻¹ * N = 1 := inv_mul_cancel₀ hNr.ne'
    have hT' : (T.coeff P : ℝ) = if Γ.coeff P = 1 then 1 else 0 := by
      rw [hTc]; split_ifs <;> simp
    have hδ1 : (δ : ℝ) ≤ 1 := by exact_mod_cast (hδlt.le.trans hδ₀1)
    have hδ0 : (0 : ℝ) ≤ δ := by exact_mod_cast hδ.le
    rw [hMP']
    have hkey : 0 ≤ Γ.coeff P - ((A.coeff P : ℝ) + δ * T.coeff P) := by
      rw [hT']
      split_ifs with h
      · rw [h, show (A.coeff P : ℝ) = 0 by exact_mod_cast hAT' P h]
        linarith
      · have := hAΓ P
        linarith
    have : -(N : ℝ)⁻¹ * (N * ((A.coeff P : ℝ) + δ * T.coeff P)) =
        -((A.coeff P : ℝ) + δ * T.coeff P) := by
      rw [← mul_assoc, neg_mul, hcancel, neg_one_mul]
    rw [this]
    nlinarith [mul_nonneg hinv hZ0']
  · rw [hbd]
    exact hklt

/-- **Lowering the reduced boundary but one component, using an ample component.** Let `X` be a
normal `ℚ`-factorial projective variety over an algebraically closed field of characteristic
zero, `(X, Γ)` a dlt pair with real boundary, `S` a prime divisor with coefficient one in `Γ`, and
`A ≤ Γ` an effective ample `ℚ`-divisor with no component in `⌊Γ⌋`. Put `T = ⌊Γ⌋ - S`. Then there
is `δ₀ > 0` such that for every rational `0 < δ < δ₀`, every `ε > 0` and every finite set `S'` of
points of `X` with proper closures, there is an effective `ℚ`-divisor `A' ∼_ℚ A + δT` with
coefficients `< ε`, not containing `S`, whose support contains no point of `S'`, and such that the
boundary `B' = Γ - A - δT + A'` has coefficients in `[0, 1]`, coefficient one exactly along `S`,
`K_X + B'` is `ℝ`-Cartier, and every exceptional divisor over `X` has positive log discrepancy
with respect to `B'`: `(X, B')` is plt with `⌊B'⌋ = S`. -/
public theorem IsRealDltPair.exists_isRealPltPair_sub_add_of_isAmple
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (hXq : IsQFactorial sX) (hXproj : MMP.Mori.IsProjectiveVariety k sX)
    {Γ : RDivisor X} (hΓ : IsRealDltPair sX Γ)
    {A : QDivisor X} (hA : A.IsAmple) (hA0 : ∀ P, 0 ≤ A.coeff P)
    (hAΓ : ∀ P, (A.coeff P : ℝ) ≤ Γ.coeff P)
    (hAT : ∀ P, A.coeff P ≠ 0 → (DivisorWithCoeffs.roundDown Γ).coeff P = 0)
    (S : MMP.Mori.PrimeDivisor X) (hS : Γ.coeff S = 1) :
    ∃ δ₀ : ℚ, 0 < δ₀ ∧ ∀ δ : ℚ, 0 < δ → δ < δ₀ →
      ∀ ε : ℚ, 0 < ε → ∀ S' : Set X, S'.Finite →
        (∀ x ∈ S', closure {x} ≠ (Set.univ : Set X)) →
        ∃ A' : QDivisor X,
          (∀ P, 0 ≤ A'.coeff P) ∧ (∀ P, A'.coeff P < ε) ∧ (∀ x ∈ S', x ∉ A'.supp) ∧
          A'.coeff S = 0 ∧
          A'.QLinearlyEquivalent (A + δ • Divisor.toQDivisor
            (DivisorWithCoeffs.roundDown Γ - (Finsupp.single S 1 : Divisor X))) ∧
          (∀ P, 0 ≤ (Γ - QDivisor.toRDivisor (A + δ • Divisor.toQDivisor
              (DivisorWithCoeffs.roundDown Γ - (Finsupp.single S 1 : Divisor X))) +
              QDivisor.toRDivisor A').coeff P ∧
            (Γ - QDivisor.toRDivisor (A + δ • Divisor.toQDivisor
              (DivisorWithCoeffs.roundDown Γ - (Finsupp.single S 1 : Divisor X))) +
              QDivisor.toRDivisor A').coeff P ≤ 1) ∧
          (Γ - QDivisor.toRDivisor (A + δ • Divisor.toQDivisor
              (DivisorWithCoeffs.roundDown Γ - (Finsupp.single S 1 : Divisor X))) +
              QDivisor.toRDivisor A').coeff S = 1 ∧
          (∀ P, P ≠ S → (Γ - QDivisor.toRDivisor (A + δ • Divisor.toQDivisor
              (DivisorWithCoeffs.roundDown Γ - (Finsupp.single S 1 : Divisor X))) +
              QDivisor.toRDivisor A').coeff P < 1) ∧
          (∃ (n : ℕ) (K : Divisor X), K.IsCanonicalDivisor sX n ∧
            RDivisor.IsRCartier (Divisor.toRDivisor K + (Γ - QDivisor.toRDivisor
              (A + δ • Divisor.toQDivisor
                (DivisorWithCoeffs.roundDown Γ - (Finsupp.single S 1 : Divisor X))) +
              QDivisor.toRDivisor A'))) ∧
          ∀ (n : ℕ) (E : DivisorOver k sX) (a : ℝ), E.IsExceptional →
            MMP.Intersection.IsLogDiscrepancy sX n (Γ - QDivisor.toRDivisor
              (A + δ • Divisor.toQDivisor
                (DivisorWithCoeffs.roundDown Γ - (Finsupp.single S 1 : Divisor X))) +
              QDivisor.toRDivisor A') E a → 0 < a := by
  classical
  have hΓ0 : ∀ P, 0 ≤ Γ.coeff P := hΓ.1.2.1
  have hΓ1 : ∀ P, Γ.coeff P ≤ 1 := hΓ.2.1
  have hfl : ∀ P, (DivisorWithCoeffs.roundDown Γ).coeff P = if Γ.coeff P = 1 then 1 else 0 :=
    fun P => by
      rw [DivisorWithCoeffs.coeff_roundDown]
      split_ifs with h
      · rw [h, Int.floor_one]
      · rw [Int.floor_eq_zero_iff]
        exact ⟨hΓ0 P, lt_of_le_of_ne (hΓ1 P) h⟩
  set T : Divisor X := DivisorWithCoeffs.roundDown Γ - (Finsupp.single S 1 : Divisor X)
    with hTdef
  have hTc : ∀ P, T.coeff P = if Γ.coeff P = 1 ∧ P ≠ S then 1 else 0 := fun P => by
    rw [hTdef, DivisorWithCoeffs.coeff_sub, hfl,
      show DivisorWithCoeffs.coeff (Finsupp.single S 1 : Divisor X) P = if S = P then 1 else 0
        from Finsupp.single_apply]
    by_cases hP : P = S
    · subst hP
      simp [hS]
    · simp only [Ne.symm hP, hP, ite_false, sub_zero, ne_eq, not_false_eq_true, and_true]
  obtain ⟨δ₀, hδ₀, hδ₀1, hδfun⟩ := exists_isBasepointFree_eq_smul hA T (by
    obtain ⟨q, hq, h⟩ := hXq.2 T
    exact ⟨q, hq, h⟩)
  refine ⟨δ₀, hδ₀, fun δ hδ hδlt ε hε S' hS' _ => ?_⟩
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, (ε⁻¹ : ℚ) < N₀ := exists_nat_gt _
  obtain ⟨N, M, hNN₀, hMc, hMbpf, hMeq⟩ := hδfun δ hδ hδlt (N₀ + 2)
  have hNq : (0 : ℚ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hMP : ∀ P, (M.coeff P : ℚ) = N * (A.coeff P + δ * T.coeff P) := fun P => by
    have h := congrArg (fun G : QDivisor X => G.coeff P) hMeq
    simp at h
    rw [h]
    ring
  have hAT' : ∀ P, Γ.coeff P = 1 → A.coeff P = 0 := fun P h => by
    by_contra hA'
    have := hAT P hA'
    rw [hfl P, ite_eq_left h] at this
    exact one_ne_zero this
  have hM0 : ∀ P, 0 ≤ M.coeff P := fun P => by
    have h : (0 : ℚ) ≤ M.coeff P := by
      rw [hMP, hTc]
      have := hA0 P
      split_ifs <;> positivity
    exact_mod_cast h
  have hMΓ : ∀ P, M.coeff P ≠ 0 → Γ.coeff P ≠ 0 := fun P hM hΓP => by
    apply hM
    have hAP : A.coeff P = 0 := le_antisymm (by exact_mod_cast (hAΓ P).trans hΓP.le) (hA0 P)
    have h : (M.coeff P : ℚ) = 0 := by
      rw [hMP, hTc, ite_eq_right (by rw [hΓP]; exact fun h => zero_ne_one h.1), hAP]
      simp
    exact_mod_cast h
  have hMlt : ∀ P, Γ.coeff P = 1 → P ≠ S → 0 < M.coeff P := fun P h hP => by
    have h' : (0 : ℚ) < M.coeff P := by
      rw [hMP, hTc, ite_eq_left ⟨h, hP⟩, hAT' P h]
      push_cast
      positivity
    exact_mod_cast h'
  have hMS : ∀ P, Γ.coeff P = 1 → M.coeff P = 0 → P = S := fun P h hM => by
    by_contra hP
    exact (hMlt P h hP).ne' hM
  have hMSz : M.coeff S = 0 := by
    have h : (M.coeff S : ℚ) = 0 := by
      rw [hMP, hTc, ite_eq_right (fun h => h.2 rfl), hAT' S hS]
      simp
    exact_mod_cast h
  obtain ⟨σ, hσ, hZle, hZΓ, hσS, hBle, hBlt, hKB, hexc⟩ :=
    exists_section_logDiscrepancy_pos_of_isExceptional hΓ hMc hMbpf hM0 hMΓ
      (fun P Q hP hQ hMP hMQ => (hMS P hP hMP).trans (hMS Q hQ hMQ).symm) (N := N) (by omega)
      S' hS'
  set Zσ := M.zeroDivisor σ hσ with hZσ
  have hZ0 : ∀ P, 0 ≤ Zσ.coeff P := fun P => Divisor.zeroDivisor_nonneg M σ hσ P
  have hZS : Zσ.coeff S = 0 := hZΓ S (by rw [hS]; exact one_ne_zero)
  have hA'c : ∀ P, (((N : ℚ)⁻¹) • Divisor.toQDivisor Zσ).coeff P = (Zσ.coeff P : ℚ) / N :=
    fun P => by simp [div_eq_inv_mul]
  -- the boundary
  have hbd : Γ - QDivisor.toRDivisor (A + δ • Divisor.toQDivisor T) +
      QDivisor.toRDivisor (((N : ℚ)⁻¹) • Divisor.toQDivisor Zσ) =
      Γ + (-(N : ℝ)⁻¹) • Divisor.toRDivisor M + (N : ℝ)⁻¹ • Divisor.toRDivisor Zσ := by
    refine Finsupp.ext fun P => ?_
    rw [← DivisorWithCoeffs.coeff_apply, ← DivisorWithCoeffs.coeff_apply]
    have hMP' : (M.coeff P : ℝ) = N * ((A.coeff P : ℝ) + δ * T.coeff P) := by
      exact_mod_cast hMP P
    simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_sub,
      DivisorWithCoeffs.coeff_smul, QDivisor.coeff_toRDivisor, Divisor.coeff_toRDivisor,
      Divisor.coeff_toQDivisor, smul_eq_mul, hMP']
    push_cast
    field_simp
    ring
  have hBc : ∀ P, (Γ + (-(N : ℝ)⁻¹) • Divisor.toRDivisor M +
      (N : ℝ)⁻¹ • Divisor.toRDivisor Zσ).coeff P =
        Γ.coeff P + -(N : ℝ)⁻¹ * M.coeff P + (N : ℝ)⁻¹ * Zσ.coeff P := fun P => by
    simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
      Divisor.coeff_toRDivisor, smul_eq_mul]
  refine ⟨((N : ℚ)⁻¹) • Divisor.toQDivisor Zσ, fun P => ?_, fun P => ?_, fun x hx => ?_, ?_, ?_,
    fun P => ⟨?_, ?_⟩, ?_, fun P hP => ?_, ?_, ?_⟩
  · rw [hA'c]
    exact div_nonneg (by exact_mod_cast hZ0 P) hNq.le
  · rw [hA'c]
    have hZ1 : (Zσ.coeff P : ℚ) ≤ 1 := by exact_mod_cast hZle P
    have h1 : (Zσ.coeff P : ℚ) / N ≤ 1 / N := div_le_div_of_nonneg_right hZ1 hNq.le
    have h2 : (1 : ℚ) / N < ε := by
      rw [div_lt_iff₀ hNq]
      have hN₀' : (N₀ : ℚ) < N := by exact_mod_cast (by omega : N₀ < N)
      have := (inv_lt_iff_one_lt_mul₀ hε).mp (hN₀.trans hN₀')
      linarith
    linarith
  · intro hmem
    apply hσS x hx
    obtain ⟨E, hE, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
    rw [hA'c] at hE
    have hZE : Zσ.coeff E ≠ 0 := fun h => hE (by rw [h]; simp)
    exact DivisorWithCoeffs.support_subset_supp hZE hxE
  · rw [hA'c, hZS]
    simp
  · refine ⟨N, by omega, (Divisor.isUnit_sectionToRationalFunctions hσ).unit, ?_⟩
    refine Finsupp.ext fun P => ?_
    rw [← DivisorWithCoeffs.coeff_apply, ← DivisorWithCoeffs.coeff_apply]
    have hZP : (Zσ.coeff P : ℚ) =
        ((principalDivisor (Divisor.isUnit_sectionToRationalFunctions hσ).unit).coeff P : ℚ) +
          M.coeff P := by
      rw [hZσ, Divisor.zeroDivisor_eq, DivisorWithCoeffs.coeff_add]
      push_cast
      ring
    simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_sub,
      DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, smul_eq_mul, zsmul_eq_mul]
    have hMP2 := hMP P
    push_cast
    rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hNq.ne', one_mul]
    linear_combination hZP + hMP2
  · rw [hbd, hBc]
    have hMP' : (M.coeff P : ℝ) = N * ((A.coeff P : ℝ) + δ * T.coeff P) := by
      exact_mod_cast hMP P
    have hZ0' : (0 : ℝ) ≤ Zσ.coeff P := by exact_mod_cast hZ0 P
    have hinv : (0 : ℝ) ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr hNr.le
    have hcancel : (N : ℝ)⁻¹ * N = 1 := inv_mul_cancel₀ hNr.ne'
    have hT' : (T.coeff P : ℝ) = if Γ.coeff P = 1 ∧ P ≠ S then 1 else 0 := by
      rw [hTc]; split_ifs <;> simp
    have hδ1 : (δ : ℝ) ≤ 1 := by exact_mod_cast (hδlt.le.trans hδ₀1)
    have hδ0 : (0 : ℝ) ≤ δ := by exact_mod_cast hδ.le
    rw [hMP']
    have hkey : 0 ≤ Γ.coeff P - ((A.coeff P : ℝ) + δ * T.coeff P) := by
      rw [hT']
      split_ifs with h
      · rw [h.1, show (A.coeff P : ℝ) = 0 by exact_mod_cast hAT' P h.1]
        linarith
      · have := hAΓ P
        linarith
    have : -(N : ℝ)⁻¹ * (N * ((A.coeff P : ℝ) + δ * T.coeff P)) =
        -((A.coeff P : ℝ) + δ * T.coeff P) := by
      rw [← mul_assoc, neg_mul, hcancel, neg_one_mul]
    rw [this]
    nlinarith [mul_nonneg hinv hZ0']
  · rw [hbd]
    exact hBle P
  · rw [hbd, hBc, hS, hMSz, hZS]
    simp
  · rw [hbd]
    exact hBlt P fun h => hMlt P h hP
  · rw [hbd]
    exact hKB
  · rw [hbd]
    exact hexc

end MMP.Fourfold
