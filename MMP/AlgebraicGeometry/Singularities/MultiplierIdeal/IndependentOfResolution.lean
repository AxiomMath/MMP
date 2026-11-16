module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.LogResolution.Basic
public import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.Basic
import MMP.AlgebraicGeometry.Singularities.LogResolution.ReducedUnion
import MMP.AlgebraicGeometry.Singularities.Snc.LocalEquations
import MMP.AlgebraicGeometry.Divisor.SmoothRDivisors
import MMP.AlgebraicGeometry.Divisor.PullbackExistence
import MMP.AlgebraicGeometry.Divisor.CartierLineBundle
import MMP.AlgebraicGeometry.Divisor.Arithmetic
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Valuation
import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.FiniteDominant
import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CurveInputs
import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.GlobalSections
import StacksFrontier.AlgebraicGeometry.Divisors.QuasiAffineDivisorRepresentation
import StacksFrontier.AlgebraicGeometry.Chow.CalculationMultiplicities.RestrictedDivisors
import StacksFrontier.AlgebraicGeometry.Variety.Curve.DivisorDegreeTwist
import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteOverFieldStalks
import StacksFrontier.AlgebraicGeometry.Chow.ChernClassOfSection.Induction
import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.PointClosureAssociatedPoints
import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.TowerProjective
import MMP.AlgebraicGeometry.Resolution.EmbeddedResolution.CartierDivisor
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.PushforwardComparison

/-!
# Log resolutions of `ℝ`-divisors and independence of the multiplier ideal

Let `X` be a non-singular variety over a field `k` of characteristic zero and `D` an `ℝ`-divisor
on `X`. Then `D` has a log resolution `μ : X' ⟶ X` (Hironaka): one takes an embedded resolution
of the reduced divisor `[D]_red` with the same support as `D`, which is Cartier because `X` is
non-singular. For a log resolution `μ` the multiplier ideal computed on `μ` is
`𝒥_μ(X, D) = μ_*𝒪_{X'}(K_{X'/X} - ⌊μ^*D⌋) ⊆ K(X)`, and by Esnault and Viehweg it is the same
for every log resolution: two log resolutions are dominated by a common resolution `V`, and both
push-forwards agree with the one computed on `V`. The argument nowhere uses that the
coefficients of `D` are rational.

## Main results

* `MMP.Intersection.exists_isLogResolution`: every `ℝ`-divisor on a non-singular variety over a
  field of characteristic zero has a log resolution.
* `MMP.Intersection.IsMultiplierIdealOn.unique`: if `J₁ = 𝒥_{μ₁}(X, D)` and
  `J₂ = 𝒥_{μ₂}(X, D)` for log resolutions `μ₁`, `μ₂` of `D`, then `J₁ = J₂`.

## Implementation notes

Each result's auxiliary lemmas live in a namespace `Proof_<tag>` named after its label,
opened only for that result; the helpers shared by both results (Weil divisors of `ℝ`-divisors
on Noetherian integral schemes, the pull-back condition along dominant morphisms) live in the
first namespace. Weil divisors of Cartier divisors come from
`MMP.Intersection.exists_isWeilDivisorOfCartier`.

Lazarsfeld works over `ℂ`; the statements are made over an arbitrary field of characteristic
zero, which is the generality of Hironaka's theorem. A non-singular variety over `k` is
`MMP.Mori.IsVariety k sX` together with `MMP.Mori.IsSmoothScheme sX`, and `X'` is a `k`-scheme
through `μ ≫ sX`, as in `MMP.Intersection.IsLogResolution`. The resolution lives in the same
universe as `X`.

The existence proof takes `S = [D]_red`, the reduced divisor on the support of the Weil divisor
of `D`, the Weil divisor of an effective Cartier divisor since `X` is non-singular. An embedded
resolution `μ` of `S` (`MMP.Intersection.exists_isEmbeddedResolution`) is a log resolution of
`S`, and since `Supp D = Supp S` it is one of `D`
(`MMP.Intersection.IsLogResolution.hasJointSNCSupport_snoc`).

The multiplier ideal computed on `μ` is recorded by the predicate
`MMP.Intersection.IsMultiplierIdealOn`, which includes that `μ` is a log resolution of `D`, and
by its sections over the opens of `X` as subsets of `K(X)`. On integral locally Noetherian
schemes every Cartier divisor pulls back along a dominant morphism, additively, so tensoring with
`ℝ` gives a pull-back `Div_ℝ(X) → Div_ℝ(Y)` that does not depend on a representation
`D = ∑ cᵢ Aᵢ` and is compatible with composition. The comparison of push-forwards
`MMP.Intersection.multiplierIdealSections_sub_roundDown_eq_of_weilPullback_eq` then gives
`𝒥_{μ₁}(X, D) = 𝒥_{μ₂}(X, D)`.

## References

* [R. Lazarsfeld, *Positivity in Algebraic Geometry II*][lazarsfeld2004], §9.1.B, Thm. 9.2.18
  and Rem. 9.2.20.
* [H. Hironaka, *Resolution of singularities of an algebraic variety over a field of
  characteristic zero*][hironaka1964].
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace TensorProduct MMP.Intersection

namespace Proof_lem_p09a_log_resolution_divisor_exists

open MMP.Mori (Divisor RDivisor DivisorWithCoeffs)

/-- Every `ℝ`-divisor on a Noetherian integral scheme has a Weil divisor. -/
private theorem exists_isWeilRDivisorOf {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [NoetherianSpace X] (D : RCartierDivisor X) : ∃ w, IsWeilRDivisorOf D w := by
  obtain ⟨m, c, A, hA⟩ := CartierDivisorWithCoeffs.exists_isRepresentation D
  choose wA hwA using fun i => exists_isWeilDivisorOfCartier (A i)
  exact ⟨_, m, c, A, wA, hA, hwA, rfl⟩

/-- A dominant morphism of integral locally Noetherian schemes satisfies the pull-back condition
for every Cartier divisor. -/
private theorem pullbackCondition_of_isDominant {X X' : Scheme.{u}} [IsIntegral X]
    [IsIntegral X'] [IsLocallyNoetherian X'] (μ : X' ⟶ X) [IsDominant μ]
    (A : X.CartierDivisor) : PullbackCondition μ A := by
  intro η hη hμη
  rw [AlgebraicGeometry.schemeAssociatedPoints_eq_singleton_genericPoint] at hη
  rw [Set.mem_singleton_iff.mp hη] at hμη
  have hsub : (Set.univ : Set X') ⊆ μ ⁻¹' cartierSupport A := by
    rw [← genericPoint_spec X']
    exact closure_minimal (Set.singleton_subset_iff.mpr hμη)
      ((isClosed_cartierSupport A).preimage μ.continuous)
  have hdense : closure (Set.range μ) ⊆ cartierSupport A :=
    closure_minimal (by rintro _ ⟨y, rfl⟩; exact hsub (Set.mem_univ y))
      (isClosed_cartierSupport A)
  rw [μ.denseRange.closure_range] at hdense
  have : IsArtinianRing (X.presheaf.stalk (genericPoint X)) :=
    (inferInstance : IsArtinianRing X.functionField)
  exact notMem_cartierSupport_of_isArtinianRing A (genericPoint X) (hdense (Set.mem_univ _))

/-- Along a dominant morphism of Noetherian integral schemes, every `ℝ`-divisor has the Weil
divisor of a pull-back. -/
private theorem exists_isWeilPullback {X X' : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [NoetherianSpace X'] (μ : X' ⟶ X) [IsDominant μ]
    (D : RCartierDivisor X) : ∃ F, IsWeilPullback μ D F := by
  obtain ⟨m, c, A, hA⟩ := CartierDivisorWithCoeffs.exists_isRepresentation D
  choose A' hA' using fun i => exists_isPullback (pullbackCondition_of_isDominant μ (A i))
  obtain ⟨F, hF⟩ := exists_isWeilRDivisorOf (∑ i, A' i ⊗ₜ c i)
  exact ⟨F, m, c, A, _, ⟨hA, fun i => pullbackCondition_of_isDominant μ (A i), A', rfl, hA'⟩, hF⟩

/-- The Weil divisor of `1 ⊗ A` is the Weil divisor of `A`. -/
private theorem isWeilRDivisorOf_ofDivisor {X : Scheme.{u}} {A : X.CartierDivisor}
    {w : Divisor X} (h : IsWeilDivisorOfCartier A w) :
    IsWeilRDivisorOf (CartierDivisorWithCoeffs.ofDivisor ℝ A) (MMP.Mori.Divisor.toRDivisor w) :=
  ⟨1, fun _ => 1, fun _ => A, fun _ => w,
    by simp [CartierDivisorWithCoeffs.IsRepresentation, CartierDivisorWithCoeffs.ofDivisor],
    fun _ => h, by simp⟩

/-- The support of an `ℝ`-divisor `w` is contained in that of the reduced divisor
`∑_{P ∈ Supp w} P`. -/
private theorem supp_le_supp_reducedDivisorOf_support {X : Scheme.{u}} (w : RDivisor X) :
    w.supp ≤ (MMP.Mori.Divisor.toRDivisor (reducedDivisorOf w.support)).supp := by
  intro x hx
  obtain ⟨Q, hQ, hxQ⟩ := DivisorWithCoeffs.mem_supp_iff.mp hx
  refine DivisorWithCoeffs.mem_supp_iff.mpr ⟨Q, ?_, hxQ⟩
  rw [MMP.Mori.Divisor.coeff_toRDivisor, coeff_reducedDivisorOf,
    ite_eq_left (Finsupp.mem_support_iff.mpr hQ)]
  norm_num

/-- The orders of a pull-back of an effective divisor are non-negative. -/
private theorem nonneg_of_isPullback_of_isOrderAlong {X Y : Scheme.{u}} {f : Y ⟶ X}
    {A : X.CartierDivisor} {A' : Y.CartierDivisor} (h : IsPullback f A A') (hA : IsEffective A)
    {V : Scheme.Subvariety Y} {N : ℤ} (hN : IsOrderAlong A' V N) : 0 ≤ N := by
  obtain ⟨U, hU, s, hs, hsA⟩ := hA (f V.genericPoint)
  set t := X.presheaf.germ U (f V.genericPoint) hU s
  have hg : IsLocalEquationAt A (f V.genericPoint) (stalkToTotalQuotient _ t) :=
    ⟨U, hU, hs.unit, hsA, germ_toTotalQuotient hU s⟩
  have hfr : IsFraction (stalkToTotalQuotient _ t) t 1 := ⟨by simp, by simp⟩
  have h' : IsFraction (stalkToTotalQuotient _ (f.stalkMap V.genericPoint t))
      (f.stalkMap V.genericPoint t) (f.stalkMap V.genericPoint 1) := ⟨by simp, by simp⟩
  obtain ⟨n, -, rfl⟩ := hN.eq_length (h.isLocalEquationAt hg hfr h')
  exact Int.natCast_nonneg n

/-- The reduced divisor with support `Exc(μ)` is the exceptional divisor `except(μ)`. -/
private theorem isExceptionalDivisorSum_of_isReducedDivisorWithSupport {X X' : Scheme.{u}}
    {μ : X' ⟶ X} {E : Divisor X'} (hE : IsReducedDivisorWithSupport E (exceptionalLocus μ)) :
    IsExceptionalDivisorSum μ E := by
  classical
  intro P
  have hPP : P.genericPoint ∈ P.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  rcases hE.1 P with h0 | h1
  · rw [h0, ite_eq_right]
    intro hsub
    have hmem : P.genericPoint ∈ (E.supp : Set X') := hE.2 ▸ hsub hPP
    obtain ⟨Q, hQ, hPQ⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
    rw [primeDivisor_eq_of_genericPoint_mem_support hPQ] at hQ
    exact hQ h0
  · rw [h1, ite_eq_left]
    rw [← hE.2]
    exact DivisorWithCoeffs.support_subset_supp (by rw [h1]; norm_num)

/-- An integral scheme of finite dimension has pure dimension `n` for some `n : ℕ`. -/
private theorem exists_isPureDimensional {X : Scheme.{u}} [IsIntegral X]
    (h : topologicalKrullDim X ≠ ⊤) : ∃ n : ℕ, IsPureDimensional X n := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, topologicalKrullDim X = n := by
    have h0 : topologicalKrullDim X ≠ ⊥ := (Order.krullDim_ne_bot_iff
      (α := IrreducibleCloseds X)).mpr ⟨IrreducibleCloseds.closureSingleton (genericPoint X)⟩
    obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp h0
    have hd' : d ≠ ⊤ := by rintro rfl; exact h hd.symm
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hd'
    exact ⟨m, by rw [← hd, ← hm]; rfl⟩
  refine ⟨n, fun Z hZ => ?_⟩
  rw [irreducibleComponents_eq_singleton] at hZ
  rw [Set.mem_singleton_iff.mp hZ, (Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq]
  exact hn

/-- On a non-singular variety, every reduced divisor `∑_{P ∈ s} P` is the Weil divisor of an
effective Cartier divisor. -/
private theorem exists_isEffective_isWeilDivisorOfCartier_reducedDivisorOf {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsVariety k sX)
    (hXs : MMP.Mori.IsSmoothScheme sX) (s : Finset (MMP.Mori.PrimeDivisor X)) :
    ∃ A : X.CartierDivisor, IsEffective A ∧ IsWeilDivisorOfCartier A (reducedDivisorOf s) := by
  classical
  let : X.Over (Spec (.of k)) := ⟨sX⟩
  have : MMP.Mori.IsVariety k (X ↘ Spec (.of k)) := hX
  have : LocallyOfFiniteType sX := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  have : LocallyOfFiniteType (X ↘ Spec (.of k)) := ‹LocallyOfFiniteType sX›
  have : IsIntegral X := AlgebraicGeometry.IsVariety.toIsIntegral (f := sX)
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := {}
  obtain ⟨n, hn⟩ := exists_isPureDimensional
    (topologicalKrullDim_ne_top_of_locallyOfFiniteType k sX)
  have hgp : ∀ P : MMP.Mori.PrimeDivisor X,
      (primeDivisorSubvariety P).genericPoint = P.genericPoint := fun _ => rfl
  have hV : ∀ P : MMP.Mori.PrimeDivisor X,
      subvarietyDim (primeDivisorSubvariety P) + 1 = n := fun P =>
    (subvarietyDim_add_one_eq_iff k hn _).mpr
      (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P)
  choose C hCe hC using fun P : MMP.Mori.PrimeDivisor X =>
    exists_isEffective_cycleMap_eq_single_of_isSmoothScheme (k := k) hn hXs
      ⟨primeDivisorSubvariety P, hV P⟩
  have hord : ∀ P Q, IsOrderAlong (C P) (primeDivisorSubvariety Q) (if P = Q then 1 else 0) := by
    intro P Q
    have h := isOrderAlong_orderAlong hn ⟨_, hV Q⟩ (C P)
    rw [← cycleMap_apply, hC P, Finsupp.single_apply] at h
    by_cases hPQ : P = Q
    · subst hPQ
      rw [ite_eq_left rfl] at h
      rwa [ite_eq_left rfl]
    · have hne : (⟨primeDivisorSubvariety P, hV P⟩ : Codim1Subvariety X n) ≠
          ⟨primeDivisorSubvariety Q, hV Q⟩ := by
        intro h
        have h' : (primeDivisorSubvariety P).genericPoint =
            (primeDivisorSubvariety Q).genericPoint :=
          congrArg Scheme.Subvariety.genericPoint (Subtype.mk.inj h)
        rw [hgp, hgp] at h'
        exact hPQ (AlgebraicGeometry.PrimeDivisor.genericPoint_injective h')
      rw [ite_eq_right hne] at h
      rwa [ite_eq_right hPQ]
  refine ⟨∑ P ∈ s, C P, ?_, fun Q => ?_⟩
  · exact Finset.sum_induction _ IsEffective (fun _ _ => IsEffective.add) isEffective_zero
      fun P _ => hCe P
  · rw [coeff_reducedDivisorOf]
    have : IsOrderAlong (∑ P ∈ s, C P) (primeDivisorSubvariety Q)
        (∑ P ∈ s, if P = Q then 1 else 0) := by
      induction s using Finset.induction_on with
      | empty => simpa using isOrderAlong_zero _
      | insert P s hP ih =>
        rw [Finset.sum_insert hP, Finset.sum_insert hP]; exact (hord P Q).add ih
    rwa [Finset.sum_ite_eq'] at this

/-- An embedded resolution of an effective Cartier divisor `A` is a log resolution of `A`. -/
private theorem isLogResolution_ofDivisor {k : Type u} [Field k] {X X' : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {A : X.CartierDivisor} {μ : X' ⟶ X}
    (h : IsEmbeddedResolution sX A μ) :
    IsLogResolution sX (CartierDivisorWithCoeffs.ofDivisor ℝ A) μ := by
  classical
  obtain ⟨hA, ⟨-, hvar, hsm, hproj, hbir⟩, -, A', wA', Eμ, hpb, hwA', hEμ, hsnc⟩ := h
  have : LocallyOfFiniteType (μ ≫ sX) := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (μ ≫ sX)
  refine ⟨hproj, hbir, hvar, hsm, MMP.Mori.Divisor.toRDivisor wA', Eμ,
    ⟨1, fun _ => 1, fun _ => A, A' ⊗ₜ (1 : ℝ), ⟨?_, fun _ => hpb.1, fun _ => A', ?_, fun _ => hpb⟩,
      isWeilRDivisorOf_ofDivisor hwA'⟩,
    isExceptionalDivisorSum_of_isReducedDivisorWithSupport hEμ, ?_⟩
  · simp [CartierDivisorWithCoeffs.IsRepresentation, CartierDivisorWithCoeffs.ofDivisor]
  · simp [CartierDivisorWithCoeffs.IsRepresentation]
  · refine IsSNCDivisor.of_support_subset hsnc (isReducedEffective_reducedDivisorOf _) ?_
    rw [reducedUnion, reducedDivisor, support_reducedDivisorOf, support_reducedDivisorOf]
    intro P hP
    rw [Finset.mem_biUnion] at hP
    obtain ⟨j, -, hj⟩ := hP
    rw [Finsupp.mem_support_iff] at hj ⊢
    have h0 : 0 ≤ wA'.coeff P := nonneg_of_isPullback_of_isOrderAlong hpb hA (hwA' P)
    have h1 := hEμ.1 P
    have hj' : wA'.coeff P ≠ 0 ∨ Eμ.coeff P ≠ 0 := by
      fin_cases j
      · left
        change (MMP.Mori.Divisor.toRDivisor wA').coeff P ≠ 0 at hj
        rw [MMP.Mori.Divisor.coeff_toRDivisor] at hj
        exact_mod_cast hj
      · right
        change (MMP.Mori.Divisor.toRDivisor Eμ).coeff P ≠ 0 at hj
        rw [MMP.Mori.Divisor.coeff_toRDivisor] at hj
        exact_mod_cast hj
    rw [Finsupp.add_apply]
    change wA'.coeff P + Eμ.coeff P ≠ 0
    omega

end Proof_lem_p09a_log_resolution_divisor_exists

namespace MMP.Intersection

open Proof_lem_p09a_log_resolution_divisor_exists

/-- **Existence of log resolutions** (Hironaka; Lazarsfeld §9.1.B): every `ℝ`-divisor `D` on a
non-singular variety `X` over a field of characteristic zero has a log resolution
`μ : X' ⟶ X`, in the sense of `MMP.Intersection.IsLogResolution`. -/
@[mmp "lem_p09a_log_resolution_divisor_exists"]
public theorem exists_isLogResolution {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsVariety k sX) (hXs : MMP.Mori.IsSmoothScheme sX)
    (D : RCartierDivisor X) :
    ∃ (X' : Scheme.{u}) (μ : X' ⟶ X), IsLogResolution sX D μ := by
  classical
  have := hX
  have : LocallyOfFiniteType sX := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  have : IsIntegral X := AlgebraicGeometry.IsVariety.toIsIntegral (f := sX)
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := {}
  obtain ⟨wD, hwD⟩ := exists_isWeilRDivisorOf D
  obtain ⟨A, hAe, hwA⟩ :=
    exists_isEffective_isWeilDivisorOfCartier_reducedDivisorOf sX hX hXs wD.support
  obtain ⟨X', μ, hμ⟩ := exists_isEmbeddedResolution sX hX A hAe
  have hlog := isLogResolution_ofDivisor hμ
  have ⟨hproj, hbir, hvar, hsm, _, E, _, hE, _⟩ := hlog
  have : LocallyOfFiniteType (μ ≫ sX) := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  have : IsIntegral X' := AlgebraicGeometry.IsVariety.toIsIntegral (f := μ ≫ sX)
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (μ ≫ sX)
  have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace (μ ≫ sX)
  have : IsNoetherian X' := {}
  have : IsDominant μ := hbir.isDominant
  obtain ⟨F, hF⟩ := exists_isWeilPullback μ D
  have h := hlog.hasJointSNCSupport_snoc (isWeilRDivisorOf_ofDivisor hwA)
    (G := ![D]) (wG := ![wD]) (fun _ => by simpa using hwD)
    (fun _ => by simpa using supp_le_supp_reducedDivisorOf_support wD)
    (F := ![F]) (fun _ => by simpa using hF) hE
  refine ⟨X', μ, hproj, hbir, hvar, hsm, F, E, hF, hE, ?_⟩
  convert h using 1
  ext i : 1
  fin_cases i <;> rfl

end MMP.Intersection

namespace Proof_thm_p09a_multiplier_ideal_independent_of_resolution

open MMP.Mori (RDivisor)

variable {X Y Z : Scheme.{u}}

/-- Pull-back of Cartier divisors is additive: `f^*(D₁ + D₂) = f^*D₁ + f^*D₂`. -/
private theorem isPullback_add {f : Y ⟶ X} {D₁ D₂ : X.CartierDivisor}
    {D₁' D₂' : Y.CartierDivisor} (h₁ : IsPullback f D₁ D₁') (h₂ : IsPullback f D₂ D₂')
    (hc : PullbackCondition f (D₁ + D₂)) : IsPullback f (D₁ + D₂) (D₁' + D₂') := by
  refine ⟨hc, fun y => ?_⟩
  obtain ⟨a₁, b₁, ⟨g₁, hg₁, hab₁⟩, ha₁, hb₁, g₁', hg₁', h₁'⟩ := h₁.2 y
  obtain ⟨a₂, b₂, ⟨g₂, hg₂, hab₂⟩, ha₂, hb₂, g₂', hg₂', h₂'⟩ := h₂.2 y
  refine ⟨a₁ * a₂, b₁ * b₂, ⟨g₁ * g₂, hg₁.add hg₂, hab₁.mul hab₂⟩, ?_, ?_,
    g₁' * g₂', hg₁'.add hg₂', ?_⟩
  · rw [map_mul]; exact mul_mem ha₁ ha₂
  · rw [map_mul]; exact mul_mem hb₁ hb₂
  · rw [map_mul, map_mul]; exact h₁'.mul h₂'

/-- The pull-back `f^* : Div(X) → Div(Y)` along a morphism of locally Noetherian schemes
satisfying the pull-back condition for every divisor. -/
private noncomputable def pullbackHom [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : Y ⟶ X) (hf : ∀ A : X.CartierDivisor, PullbackCondition f A) :
    X.CartierDivisor →+ Y.CartierDivisor :=
  AddMonoidHom.mk' (fun A => (exists_isPullback (hf A)).choose) fun A B =>
    (exists_isPullback (hf (A + B))).choose_spec.unique
      (isPullback_add (exists_isPullback (hf A)).choose_spec
        (exists_isPullback (hf B)).choose_spec (hf _))

private theorem isPullback_pullbackHom [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : Y ⟶ X) (hf : ∀ A : X.CartierDivisor, PullbackCondition f A) (A : X.CartierDivisor) :
    IsPullback f A (pullbackHom f hf A) :=
  (exists_isPullback (hf A)).choose_spec

/-- The pull-back `f^* : Div_ℝ(X) → Div_ℝ(Y)` of `ℝ`-divisors, `pullbackHom` tensored with `ℝ`. -/
private noncomputable def rPullback [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : Y ⟶ X) (hf : ∀ A : X.CartierDivisor, PullbackCondition f A) :
    RCartierDivisor X →ₗ[ℤ] RCartierDivisor Y :=
  LinearMap.rTensor ℝ (pullbackHom f hf).toIntLinearMap

private theorem rPullback_sum [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : Y ⟶ X) (hf : ∀ A : X.CartierDivisor, PullbackCondition f A) {m : ℕ} (c : Fin m → ℝ)
    (A : Fin m → X.CartierDivisor) :
    rPullback f hf (∑ i, A i ⊗ₜ c i) = ∑ i, pullbackHom f hf (A i) ⊗ₜ c i :=
  (map_sum _ _ _).trans (Finset.sum_congr rfl fun i _ => LinearMap.rTensor_tmul _ _ _ _)

/-- A Weil divisor of a pull-back of `D` relative to any representation is a Weil divisor of
`rPullback f hf D`. -/
private theorem isWeilRDivisorOf_rPullback [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    {f : Y ⟶ X} (hf : ∀ A : X.CartierDivisor, PullbackCondition f A) {D : RCartierDivisor X}
    {F : RDivisor Y} (h : IsWeilPullback f D F) : IsWeilRDivisorOf (rPullback f hf D) F := by
  obtain ⟨m, c, A, D', ⟨hrep, -, A', hrep', hA'⟩, hD'⟩ := h
  have : D' = rPullback f hf D := by
    unfold CartierDivisorWithCoeffs.IsRepresentation at hrep hrep'
    rw [hrep', hrep, rPullback_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [(hA' i).unique (isPullback_pullbackHom f hf (A i))]
  rwa [← this]

/-- **Pull-back of `ℝ`-divisors along a composite** (`(g ≫ μ)^*D = g^*μ^*D`): a Weil divisor of
`h^*D`, for `h = g ≫ μ`, is a Weil divisor of a pull-back of `μ^*D` along `g`. -/
private theorem isWeilPullback_rPullback [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian Z] {μ : Y ⟶ X} {g : Z ⟶ Y} {h : Z ⟶ X} (hgh : g ≫ μ = h)
    (hμ : ∀ A : X.CartierDivisor, PullbackCondition μ A)
    (hg : ∀ A : Y.CartierDivisor, PullbackCondition g A)
    (hh : ∀ A : X.CartierDivisor, PullbackCondition h A) (D : RCartierDivisor X)
    {F : RDivisor Z} (hF : IsWeilRDivisorOf (rPullback h hh D) F) :
    IsWeilPullback g (rPullback μ hμ D) F := by
  subst hgh
  obtain ⟨m, c, A, hrep⟩ := D.exists_isRepresentation
  unfold CartierDivisorWithCoeffs.IsRepresentation at hrep
  have key : ∀ i, IsPullback g (pullbackHom μ hμ (A i)) (pullbackHom (g ≫ μ) hh (A i)) :=
    fun i => by
      have h1 := isPullback_pullbackHom g hg (pullbackHom μ hμ (A i))
      rwa [(isPullback_pullbackHom μ hμ (A i)).comp_eq h1
        (isPullback_pullbackHom (g ≫ μ) hh (A i))]
  refine ⟨m, c, fun i => pullbackHom μ hμ (A i), rPullback (g ≫ μ) hh D,
    ⟨?_, fun i => hg _, fun i => pullbackHom (g ≫ μ) hh (A i), ?_, key⟩, hF⟩
  all_goals unfold CartierDivisorWithCoeffs.IsRepresentation; rw [hrep, rPullback_sum]

end Proof_thm_p09a_multiplier_ideal_independent_of_resolution

namespace MMP.Intersection

open Proof_lem_p09a_log_resolution_divisor_exists
  Proof_thm_p09a_multiplier_ideal_independent_of_resolution
open MMP.Mori (Divisor RDivisor)

/-- **Independence of the log resolution** (Esnault–Viehweg; Lazarsfeld Thm. 9.2.18 with
Rem. 9.2.20). Let `X` be a non-singular variety over a field of characteristic zero and `D` an
`ℝ`-divisor on `X`. If `J₁` is the multiplier ideal of `D` computed on a log resolution `μ₁` and
`J₂` the one computed on a log resolution `μ₂` (`MMP.Intersection.IsMultiplierIdealOn`), then
`J₁ = J₂`. -/
@[mmp "thm_p09a_multiplier_ideal_independent_of_resolution"]
public theorem IsMultiplierIdealOn.unique {k : Type u} [Field k] [CharZero k]
    {X X₁ X₂ : Scheme.{u}} [IsIntegral X] {sX : X ⟶ Spec (.of k)}
    (hX : MMP.Mori.IsVariety k sX) (hXs : MMP.Mori.IsSmoothScheme sX) {D : RCartierDivisor X}
    {μ₁ : X₁ ⟶ X} {μ₂ : X₂ ⟶ X} {J₁ J₂ : X.Opens → Set X.functionField}
    (h₁ : IsMultiplierIdealOn sX D μ₁ J₁) (h₂ : IsMultiplierIdealOn sX D μ₂ J₂) :
    J₁ = J₂ := by
  obtain ⟨⟨hp₁, hb₁, hv₁, hs₁, F₁', E₁, hF₁', -, hjoint₁⟩, -, -, -, -, K₁, wK₁, F₁, hK₁,
    hwK₁, hF₁, rfl⟩ := h₁
  obtain ⟨⟨hp₂, hb₂, hv₂, hs₂, F₂', E₂, hF₂', -, hjoint₂⟩, -, -, -, -, K₂, wK₂, F₂, hK₂,
    hwK₂, hF₂, rfl⟩ := h₂
  have : MMP.Mori.IsVariety k sX := hX
  have : MMP.Mori.IsVariety k (μ₁ ≫ sX) := hv₁
  have : MMP.Mori.IsVariety k (μ₂ ≫ sX) := hv₂
  have : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsProper μ₁ := isProper_of_isProjectiveMorphism μ₁ hp₁
  have hpc₁ := pullbackCondition_of_isDominant μ₁
  have hpc₂ := pullbackCondition_of_isDominant μ₂
  -- `μᵢ^*D` has SNC support, its support being part of that of `μᵢ^*D + except(μᵢ)`
  have hsnc : ∀ {X' : Scheme.{u}} [IsLocallyNoetherian X'] {μ : X' ⟶ X} {F F' : RDivisor X'}
      {E : Divisor X'}, F' = F → HasJointSNCSupport (μ ≫ sX) ![F', MMP.Mori.Divisor.toRDivisor E] →
      HasSNCSupport (μ ≫ sX) F := by
    classical
    rintro X' _ μ F F' E rfl hj
    refine hj.reducedDivisorOf ?_
    rw [reducedUnion, support_reducedDivisorOf]
    exact Finset.subset_biUnion_of_mem
      (fun j => (![F', MMP.Mori.Divisor.toRDivisor E] j).support) (Finset.mem_univ 0)
  refine multiplierIdealSections_sub_roundDown_eq_of_weilPullback_eq (k := k) hXs hs₁ hs₂ hb₁ hp₂
    hb₂ (isWeilRDivisorOf_rPullback hpc₁ hF₁)
    (hsnc ((isWeilRDivisorOf_rPullback hpc₁ hF₁').unique (isWeilRDivisorOf_rPullback hpc₁ hF₁))
      hjoint₁)
    (isWeilRDivisorOf_rPullback hpc₂ hF₂)
    (hsnc ((isWeilRDivisorOf_rPullback hpc₂ hF₂').unique (isWeilRDivisorOf_rPullback hpc₂ hF₂))
      hjoint₂) ?_ hK₁ hwK₁ hK₂ hwK₂
  -- on a common resolution `V`, `g₁^*μ₁^*D = (g₁ ≫ μ₁)^*D = g₂^*μ₂^*D`
  intro V g₁ g₂ hvV _ _ hbg₁ _ hbg₂ hcomm
  have : IsIntegral V := hvV.toIsIntegral
  have : LocallyOfFiniteType (g₁ ≫ μ₁ ≫ sX) := hvV.toLocallyOfFiniteType
  have : QuasiCompact (g₁ ≫ μ₁ ≫ sX) := hvV.toQuasiCompact
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian (g₁ ≫ μ₁ ≫ sX)
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace (g₁ ≫ μ₁ ≫ sX)
  have : IsNoetherian V := {}
  have := hbg₁.isDominant
  have := hbg₂.isDominant
  have hh := pullbackCondition_of_isDominant (g₁ ≫ μ₁)
  obtain ⟨F, hF⟩ := exists_isWeilRDivisorOf (rPullback (g₁ ≫ μ₁) hh D)
  exact ⟨F, isWeilPullback_rPullback rfl hpc₁ (pullbackCondition_of_isDominant g₁) hh D hF,
    isWeilPullback_rPullback hcomm.symm hpc₂ (pullbackCondition_of_isDominant g₂) hh D hF⟩

end MMP.Intersection

end
