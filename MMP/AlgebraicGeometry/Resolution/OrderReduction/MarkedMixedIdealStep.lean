module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.Sequence
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.Functor
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.Monomial
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence.FlatBaseChange
import MMP.AlgebraicGeometry.Divisor.DivisorialSheaf
import MMP.AlgebraicGeometry.Resolution.BirationalTransformIdeal
import MMP.AlgebraicGeometry.Resolution.BirationalTransformTriple
import MMP.AlgebraicGeometry.Resolution.DivisorialPart
import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.OrderOnePullback
import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
import MMP.AlgebraicGeometry.Resolution.OrderAlongExceptional
import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
import MMP.AlgebraicGeometry.Resolution.SNCRestriction
import MMP.AlgebraicGeometry.Resolution.MaximalContact.MaximalCoefficientPowers
import MMP.AlgebraicGeometry.Resolution.OrderRestriction
import StacksFrontier.AlgebraicGeometry.Curves.LinearSystemScheme.IdealGlue
import StacksFrontier.AlgebraicGeometry.FiniteTypeIdealSheafDirected.FlatCapture
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Resolution.OrderReduction.MonomialReducesOrder
import MMP.AlgebraicGeometry.Resolution.OrderReduction.IdealFunctor
import MMP.AlgebraicGeometry.Resolution.MaximalOrderAttained
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
import MMP.AlgebraicGeometry.Resolution.OrderReduction.MarkedStepOne
import MMP.AlgebraicGeometry.Resolution.OrderReduction.OrderMSequenceCosupport
import MMP.AlgebraicGeometry.Resolution.OrderReduction.MixedIdealMonomialReduction
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# Order reduction for marked ideals: Steps 2 and 3, and the first inductive step

This file proves the parts of Kollár's order-reduction induction that go from an order-reduction
family `𝓑` for ideals to the sequence `𝓑𝓜𝓞_{d,m}[𝓑]` for marked ideals, and back.

Let `(X, I, m, E)` be a marked triple, `N(I)` the nonmonomial part of `I` with respect to `E`, and
`K_s(I, m) = N(I)^m + I^s`. Along a smooth blow-up sequence of order `m·s` starting with
`(X, K_s, E)` the marked transform of `(N(I), s)` stays inside the nonmonomial part of the marked
transform of `(I, m)`. Hence one application of `𝓑_{d, m s}` with `s = maxord_{cosupp(I, m)} N(I)`
strictly lowers `s`, and the Step-2 sequence, iterating this, ends with `cosupp(I_2, m)` disjoint
from `cosupp N(I_2)`. Concatenating Step 1, Step 2 and the monomial order reduction of Step 3,
`𝓑𝓜𝓞_{d,m}[𝓑]` is a smooth blow-up sequence of order `≥ m`.

Independently, blow-ups and their marked and total transforms commute with flat pull-back; and,
as the first inductive step, a marked order-reduction family in dimensions `< n` yields, through
`𝓑𝓞`, an order-reduction family for ideals in dimensions `≤ n`.

## Main results

* `MMP.Resolution.ClosedBlowupSequence.markedTransform_nonmonomialPart_le_nonmonomialPart`:
  `N_i ⊆ N(I_i)` along a mixed-ideal sequence.
* `MMP.Resolution.maxOrderAlong_nonmonomialPart_endOf_mixedIdeal_lt`: one round of Step 2 lowers
  `s`.
* `MMP.Resolution.isOrderGeMarkedTripleSeq_bmoStepTwo`: the Step-2 sequence is of order `≥ m`
  and separates `cosupp(I_2, m)` from `cosupp N(I_2)`.
* `MMP.Resolution.bmoFunctor_isOrderGeMarkedTripleSeq`: `𝓑𝓜𝓞_{d,m}[𝓑]` is a smooth blow-up
  sequence of order `≥ m` without empty blow-ups.
* `MMP.Resolution.Kollar.transforms_comap_canonicalLift_of_flat`: blow-ups and their transforms
  commute with flat pull-back.
* `MMP.Resolution.isOrderReductionFamily_boFunctor`: the first inductive step, Kollár 3.70.1.

## Implementation notes

The file has six parts, one per result, in the order above; the first four form one argument,
the last two are independent of it and of each other.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.30, 3.60, 3.65, 3.70.1, 3.107,
  3.111][kollar2007]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Resolution

/-! ### The transform of the nonmonomial part along a mixed-ideal sequence -/

section MixedIdeal

open IsLocalRing MMP.Resolution.Aux

section DivisorIdeal

variable {X : Scheme.{u}}

private theorem genericPoint_mem_support (D : AlgebraicGeometry.PrimeDivisor X) :
    D.genericPoint ∈ D.support := by
  have : D.genericPoint ∈ closure ({D.genericPoint} : Set X) := subset_closure rfl
  rwa [← support_eq_closure_genericPoint] at this

private theorem isDiscreteValuationRing_stalk_genericPoint {k : Type u} [Field k]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (h : MMP.Mori.IsSmoothScheme sX)
    (D : AlgebraicGeometry.PrimeDivisor X) :
    ∃ _ : IsDomain (X.presheaf.stalk D.genericPoint),
      IsDiscreteValuationRing (X.presheaf.stalk D.genericPoint) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have := smooth_of_isSmoothScheme' sX h
  have := isRegularLocalRing_stalk_of_smooth_over_field sX D.genericPoint
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk D.genericPoint)
  obtain ⟨π, hπ, hπD⟩ := exists_prime_stalk_idealSheaf sX h D (genericPoint_mem_support D)
  rw [stalk_idealSheaf_genericPoint] at hπD
  refine ⟨inferInstance, ?_⟩
  have hnf : ¬ IsField (X.presheaf.stalk D.genericPoint) := by
    intro hf
    have h0 := IsLocalRing.isField_iff_maximalIdeal_eq.mp hf
    rw [h0, eq_comm, Ideal.span_singleton_eq_bot] at hπD
    exact hπ.ne_zero hπD
  exact ((IsDiscreteValuationRing.TFAE _ hnf).out 5 1).mp
    (show Submodule.IsPrincipal (IsLocalRing.maximalIdeal (X.presheaf.stalk D.genericPoint)) from
      ⟨⟨π, hπD⟩⟩)

private theorem genericPoint_notMem_support {k : Type u} [Field k]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (h : MMP.Mori.IsSmoothScheme sX)
    {D D' : AlgebraicGeometry.PrimeDivisor X} (hne : D ≠ D') :
    D.genericPoint ∉ D'.support := by
  intro hx
  obtain ⟨_, _⟩ := isDiscreteValuationRing_stalk_genericPoint sX h D
  obtain ⟨π, hπ, hπD⟩ := exists_prime_stalk_idealSheaf sX h D' hx
  have hp : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).2 hπ
  have hb : Ideal.span {π} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hπ.ne_zero
  have hm := IsLocalRing.eq_maximalIdeal (hp.isMaximal hb)
  refine hne (eq_of_stalk_idealSheaf_eq sX h D D' (genericPoint_mem_support D) hx ?_)
  rw [stalk_idealSheaf_genericPoint, hπD, hm]

private theorem divisorIdeal_eq_prod (A : AlgebraicGeometry.PrimeDivisor X → ℕ)
    (hfin : (Function.support A).Finite) :
    divisorIdeal A = ∏ D ∈ hfin.toFinset, D.idealSheaf ^ A D := by
  refine finprod_eq_prod_of_mulSupport_subset _ fun D hD => ?_
  rw [Finset.mem_coe, Set.Finite.mem_toFinset]
  intro h0
  exact hD (by show D.idealSheaf ^ A D = 1; rw [h0, pow_zero])

/-- The stalk of `𝒪_X(-A)` at the generic point of a prime divisor `D` is `𝔪^{a_D}`. -/
private theorem stalk_divisorIdeal_genericPoint {k : Type u} [Field k]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (h : MMP.Mori.IsSmoothScheme sX)
    (A : AlgebraicGeometry.PrimeDivisor X → ℕ) (hfin : (Function.support A).Finite)
    (D : AlgebraicGeometry.PrimeDivisor X) :
    IdealSheafData.stalk (divisorIdeal A) D.genericPoint =
      IsLocalRing.maximalIdeal (X.presheaf.stalk D.genericPoint) ^ A D := by
  rw [divisorIdeal_eq_prod A hfin, Aux.stalk_prod]
  simp only [Aux.stalk_pow]
  have htop : ∀ D' ∈ hfin.toFinset, D' ≠ D →
      IdealSheafData.stalk D'.idealSheaf D.genericPoint ^ A D' = 1 := by
    intro D' _ hne
    rw [(IdealSheafData.stalk_eq_top_iff_notMem_support _ _).2
      (genericPoint_notMem_support sX h (Ne.symm hne)), ← Ideal.one_eq_top, one_pow]
  by_cases hD : D ∈ hfin.toFinset
  · rw [Finset.prod_eq_single D htop (fun h' => absurd hD h'), stalk_idealSheaf_genericPoint]
  · have h0 : A D = 0 := by
      by_contra h0; exact hD (by simpa using h0)
    rw [h0, pow_zero]
    exact Finset.prod_eq_one fun D' hD' => htop D' hD' (fun e => hD (e ▸ hD'))

private theorem isEffectiveCartierDivisor_divisorIdeal {k : Type u} [Field k]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (h : MMP.Mori.IsSmoothScheme sX)
    (A : AlgebraicGeometry.PrimeDivisor X → ℕ) (hfin : (Function.support A).Finite) :
    Stacks.Divisors.IsEffectiveCartierDivisor (divisorIdeal A) := by
  rw [divisorIdeal_eq_prod A hfin]
  exact Stacks.Divisors.isEffectiveCartierDivisor_prod _ _ _
    fun D _ => isEffectiveCartierDivisor_idealSheaf sX h D

/-- A divisor ideal `𝒪_X(-A)` with `A` supported on prime divisors inside `S` is trivial off
`S`. -/
private theorem stalk_divisorIdeal_eq_top (A : AlgebraicGeometry.PrimeDivisor X → ℕ)
    (hfin : (Function.support A).Finite) {S : Set X}
    (hA : ∀ D, A D ≠ 0 → (D.support : Set X) ⊆ S) {y : X} (hy : y ∉ S) :
    IdealSheafData.stalk (divisorIdeal A) y = ⊤ := by
  rw [divisorIdeal_eq_prod A hfin, Aux.stalk_prod, ← Ideal.one_eq_top]
  refine Finset.prod_eq_one fun D _ => ?_
  rw [Aux.stalk_pow]
  by_cases h0 : A D = 0
  · rw [h0, pow_zero]
  · rw [(IdealSheafData.stalk_eq_top_iff_notMem_support _ _).2 (fun h => hy (hA D h0 h)),
      ← Ideal.one_eq_top, one_pow]

/-- An ideal sheaf whose stalks are generated by left-regular elements can be cancelled from an
inclusion: `D·A ⊆ D·B` forces `A ⊆ B`. -/
private theorem le_of_mul_le_mul_left {A B D : X.IdealSheafData}
    (hD : ∀ y, ∃ g : X.presheaf.stalk y, IsLeftRegular g ∧
      IdealSheafData.stalk D y = Ideal.span {g})
    (h : D * A ≤ D * B) : A ≤ B := by
  refine IdealSheafData.le_of_stalk_le _ _ fun y => ?_
  obtain ⟨g, hg, hgs⟩ := hD y
  have hy : IdealSheafData.stalk (D * A) y ≤ IdealSheafData.stalk (D * B) y :=
    stalk_le_stalk_of_le h y
  simp only [IdealSheafData.stalk_mul, hgs] at hy
  intro x hx
  have hxg : g * x ∈ Ideal.span {g} * IdealSheafData.stalk B y :=
    hy (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self g) hx)
  rw [Ideal.mem_span_singleton_mul] at hxg
  obtain ⟨b, hb, hbg⟩ := hxg
  rw [hg hbg] at hb
  exact hb

/-- On a smooth scheme, a prime element of a local ring is a local equation of a prime
divisor through the point. -/
private theorem exists_primeDivisor_stalk_eq_span {k : Type u} [Field k]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (h : MMP.Mori.IsSmoothScheme sX)
    {x : X} {p : X.presheaf.stalk x} (hp : Prime p) :
    ∃ D : AlgebraicGeometry.PrimeDivisor X, x ∈ D.support ∧
      IdealSheafData.stalk D.idealSheaf x = Ideal.span {p} := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have := smooth_of_isSmoothScheme' sX h
  have := isRegularLocalRing_stalk_of_smooth_over_field sX x
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk x)
  have hpp : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp
  have hht : (Ideal.span {p}).height = 1 := by
    refine le_antisymm ?_ ?_
    · exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {p})
        (Ideal.span {p}) (by rw [Ideal.minimalPrimes_eq_subsingleton_self]; rfl)
    · rw [Order.one_le_iff_pos, pos_iff_ne_zero, Ne, Ideal.height_eq_zero_iff,
        IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff,
        Ideal.span_singleton_eq_bot]
      exact hp.ne_zero
  obtain ⟨D, hsp, hloc⟩ := MMP.Mori.exists_primeDivisor_isLocalization
    (⟨Ideal.span {p}, hpp⟩ : PrimeSpectrum (X.presheaf.stalk x)) hht
  have hx : x ∈ D.support := by
    have : x ∈ closure ({D.genericPoint} : Set X) := specializes_iff_mem_closure.1 hsp
    rwa [← support_eq_closure_genericPoint] at this
  refine ⟨D, hx, ?_⟩
  rw [← primeOfSpecializes_genericPoint sX h D hx]
  letI := (X.presheaf.stalkSpecializes hsp).hom.toAlgebra
  exact IsLocalization.AtPrime.comap_maximalIdeal (X.presheaf.stalk D.genericPoint)
    (Ideal.span {p})

/-- **Inclusions into a locally principal ideal are detected in codimension one.** On a smooth
scheme, if `Q` has stalks generated by nonzero elements and `L_{ξ_D} ⊆ Q_{ξ_D}` at the generic
point of every prime divisor `D`, then `L ⊆ Q`. -/
private theorem le_of_stalk_genericPoint_le {k : Type u} [Field k]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (h : MMP.Mori.IsSmoothScheme sX)
    (L Q : X.IdealSheafData)
    (hQ : ∀ x, ∃ q : X.presheaf.stalk x, q ≠ 0 ∧ IdealSheafData.stalk Q x = Ideal.span {q})
    (hLQ : ∀ D : AlgebraicGeometry.PrimeDivisor X,
      IdealSheafData.stalk L D.genericPoint ≤ IdealSheafData.stalk Q D.genericPoint) :
    L ≤ Q := by
  have := smooth_of_isSmoothScheme' sX h
  refine IdealSheafData.le_of_stalk_le _ _ fun x f hf => ?_
  have := isRegularLocalRing_stalk_of_smooth_over_field sX x
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk x)
  have := IsRegularLocalRing.uniqueFactorizationMonoid (X.presheaf.stalk x)
  obtain ⟨q, hq0, hq⟩ := hQ x
  rw [hq, Ideal.mem_span_singleton, UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hq0]
  intro p hp
  obtain ⟨D, hxD, hD⟩ := exists_primeDivisor_stalk_eq_span sX h hp
  have hfin : FiniteMultiplicity p q := FiniteMultiplicity.of_not_isUnit hp.not_unit hq0
  rw [hfin.emultiplicity_eq_multiplicity]
  refine le_emultiplicity_of_pow_dvd ?_
  refine pow_dvd_of_stalk_genericPoint_le sX h D hxD hp hD L _ ?_ hf
  refine (hLQ D).trans ?_
  have hsp := genericPoint_specializes_of_mem_support D hxD
  rw [stalk_eq_map_stalkSpecializes Q hsp, hq, ← stalk_idealSheaf_genericPoint,
    stalk_eq_map_stalkSpecializes D.idealSheaf hsp, hD, ← Ideal.map_pow,
    Ideal.span_singleton_pow]
  refine Ideal.map_mono ?_
  rw [Ideal.span_singleton_le_span_singleton]
  exact pow_multiplicity_dvd p q

/-- On a smooth scheme with an snc divisor `F`, a prime divisor whose generic point lies on
`Supp F` is an irreducible component of a member of `F`. -/
private theorem isComponent_of_genericPoint_mem_support {k : Type u} [Field k]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (h : MMP.Mori.IsSmoothScheme sX)
    (F : OrderedDivisor X) (hF : F.IsSNC sX) (D : AlgebraicGeometry.PrimeDivisor X)
    (hD : D.genericPoint ∈ F.support) : F.IsComponent D := by
  obtain ⟨_, _⟩ := isDiscreteValuationRing_stalk_genericPoint sX h D
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hD
  refine ⟨j, ?_⟩
  obtain ⟨n, z, c, hz, hc, -⟩ := hF.2 D.genericPoint
  have := smooth_of_isSmoothScheme' sX h
  have := isRegularLocalRing_stalk_of_smooth_over_field sX D.genericPoint
  have hπ := prime_of_isRegularSystemOfParameters hz (c ⟨j, hj⟩)
  obtain ⟨W, hW, hηW⟩ := exists_mem_componentsOf hj
  have hW' : Maximal (fun W' : Set X => IsIrreducible W' ∧ W' ⊆ (F.E j).support) W := hW
  have hirr : IsIrreducible W := hW'.prop.1
  have hgen : IsGenericPoint hirr.genericPoint (closure W) :=
    hirr.isGenericPoint_genericPoint_closure
  have hsp : hirr.genericPoint ⤳ D.genericPoint := hgen.specializes (subset_closure hηW)
  have hξ : hirr.genericPoint ∈ ((F.E j).support : Set X) :=
    closure_minimal hW'.prop.2 (F.E j).support.isClosed hgen.mem
  obtain ⟨q, hq⟩ := exists_fromSpecStalk_eq_of_specializes hsp
  rw [← hq, fromSpecStalk_mem_support_iff_stalk_le, hc ⟨j, hj⟩] at hξ
  have hqne : q.asIdeal ≠ ⊥ := fun h0 => hπ.ne_zero (by
    have := hξ (Ideal.mem_span_singleton_self _)
    rw [h0] at this
    exact Ideal.mem_bot.1 this)
  have hqc : q = IsLocalRing.closedPoint _ :=
    PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (q.2.isMaximal hqne))
  rw [hqc, Scheme.fromSpecStalk_closedPoint] at hq
  have hDcl : (D.support : Set X) = closure {D.genericPoint} := support_eq_closure_genericPoint D
  have hWD : W ⊆ D.support := by
    rw [hDcl, hq]
    calc W ⊆ closure W := subset_closure
      _ = closure {hirr.genericPoint} := hgen.symm
  have hDsub : (D.support : Set X) ⊆ (F.E j).support := by
    rw [hDcl]
    exact closure_minimal (Set.singleton_subset_iff.2 hj) (F.E j).support.isClosed
  have hDirr : IsIrreducible (D.support : Set X) := by
    rw [hDcl]; exact isIrreducible_singleton.closure
  have hDW := hW'.2 ⟨hDirr, hDsub⟩ hWD
  rwa [← hWD.antisymm hDW]

/-- On a smooth scheme with an snc divisor `F`, an ideal sheaf whose support lies in `Supp F`
has no zero stalk. -/
private theorem stalk_ne_bot_of_support_subset {k : Type u} [Field k]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (h : MMP.Mori.IsSmoothScheme sX)
    (F : OrderedDivisor X) (hF : F.IsSNC sX) (K : X.IdealSheafData)
    (hK : (K.support : Set X) ⊆ F.support) (x : X) : IdealSheafData.stalk K x ≠ ⊥ := by
  have := smooth_of_isSmoothScheme' sX h
  have := isRegularLocalRing_stalk_of_smooth_over_field sX x
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk x)
  intro h0
  let p₀ : PrimeSpectrum (X.presheaf.stalk x) := ⟨⊥, Ideal.isPrime_bot⟩
  have hξ : X.fromSpecStalk x p₀ ∈ (K.support : Set X) :=
    (fromSpecStalk_mem_support_iff_stalk_le K x p₀).2 h0.le
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hK hξ)
  have hxj : x ∈ ((F.E j).support : Set X) :=
    (fromSpecStalk_specializes_self x p₀).mem_closed (F.E j).support.isClosed hj
  have hle := (fromSpecStalk_mem_support_iff_stalk_le _ x p₀).1 hj
  obtain ⟨n, z, c, hz, hc, -⟩ := hF.2 x
  rw [hc ⟨j, hxj⟩] at hle
  exact (prime_of_isRegularSystemOfParameters hz (c ⟨j, hxj⟩)).ne_zero
    (Ideal.mem_bot.1 (hle (Ideal.mem_span_singleton_self _)))

end DivisorIdeal

section DVR

/-- In a discrete valuation ring the order of `𝔪ⁿ` is `n`. -/
private theorem idealOrder_maximalIdeal_pow {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (n : ℕ) :
    idealOrder (IsLocalRing.maximalIdeal R ^ n) = n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have key : ∀ j : ℕ, IsLocalRing.maximalIdeal R ^ n ≤ IsLocalRing.maximalIdeal R ^ j ↔ j ≤ n := by
    intro j
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_pow,
      Ideal.span_singleton_le_span_singleton]
    exact pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit
  refine le_antisymm (iSup₂_le fun j hj => by exact_mod_cast (key j).1 hj) ?_
  exact le_iSup₂_of_le (f := fun (j : ℕ) (_ : IsLocalRing.maximalIdeal R ^ n ≤
    IsLocalRing.maximalIdeal R ^ j) => (j : ℕ∞)) n le_rfl le_rfl

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

private theorem idealOrder_bot {R : Type*} [CommRing R] [IsLocalRing R] :
    idealOrder (⊥ : Ideal R) = ⊤ := by
  refine ENat.eq_top_iff_forall_ge.mpr fun n => ?_
  exact le_iSup₂_of_le (f := fun (j : ℕ) (_ : (⊥ : Ideal R) ≤ maximalIdeal R ^ j) => (j : ℕ∞))
    n bot_le le_rfl

/-- In a discrete valuation ring the order is additive. -/
private theorem idealOrder_mul_of_isDiscreteValuationRing {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (I J : Ideal R) :
    idealOrder (I * J) = idealOrder I + idealOrder J := by
  obtain ⟨a, rfl⟩ := Submodule.IsPrincipal.principal I
  obtain ⟨b, rfl⟩ := Submodule.IsPrincipal.principal J
  change idealOrder (Ideal.span {a} * Ideal.span {b}) =
    idealOrder (Ideal.span {a}) + idealOrder (Ideal.span {b})
  rw [Ideal.span_singleton_mul_span_singleton]
  by_cases ha : a = 0
  · subst ha
    simp [Ideal.span_singleton_eq_bot.2 rfl, idealOrder_bot]
  by_cases hb : b = 0
  · subst hb
    simp [Ideal.span_singleton_eq_bot.2 rfl, idealOrder_bot]
  rw [idealOrder_span_eq_addVal (mul_ne_zero ha hb), idealOrder_span_eq_addVal ha,
    idealOrder_span_eq_addVal hb, IsDiscreteValuationRing.addVal_mul]

/-- In a discrete valuation ring, an ideal of order at least that of a nonzero ideal `K` lies
in `K`. -/
private theorem le_of_idealOrder_le {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {I K : Ideal R} (hK : K ≠ ⊥)
    (h : idealOrder K ≤ idealOrder I) : I ≤ K := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, rfl⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hK hϖ
  have hm : Ideal.span {ϖ ^ n} = maximalIdeal R ^ n := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  rw [hm, idealOrder_maximalIdeal_pow] at h
  rw [hm]
  exact (natCast_le_idealOrder_iff' I n).1 h

/-- In a domain, `(a)·(f)ⁿ` is generated by the nonzero element `a·fⁿ` when `a, f ≠ 0`. -/
private theorem exists_span_mul_pow_eq_span {R : Type*} [CommRing R] [IsDomain R] {a f : R}
    (ha : a ≠ 0) (hf : f ≠ 0) (n : ℕ) :
    ∃ g : R, g ≠ 0 ∧ Ideal.span {a} * Ideal.span {f} ^ n = Ideal.span {g} :=
  ⟨a * f ^ n, mul_ne_zero ha (pow_ne_zero n hf), by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton]⟩

end DVR

section MonomialPart

/-- The monomial part of a triple has finitely many nonzero coefficients. -/
private theorem finite_support_monomialPartCoeff {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (I : X.IdealSheafData) (E : OrderedDivisor X)
    (hT : IsTriple sX I E) : (Function.support (monomialPartCoeff I E)).Finite := by
  obtain ⟨-, -, hlft, hqc, -, -, -⟩ := hT
  have : LocallyOfFiniteType sX := hlft
  have : QuasiCompact sX := hqc
  refine (finite_primeDivisor_of_isComponent sX E.E).subset fun D hD => ?_
  by_contra hnc
  exact hD (by unfold monomialPartCoeff; exact if_neg hnc)

/-- The monomial part `M(I)` of a triple is an effective Cartier divisor. -/
private theorem isEffectiveCartierDivisor_monomialPart {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (I : X.IdealSheafData) (E : OrderedDivisor X)
    (hT : IsTriple sX I E) : Stacks.Divisors.IsEffectiveCartierDivisor (monomialPart I E) := by
  have hAfin := finite_support_monomialPartCoeff sX I E hT
  obtain ⟨-, hsm, hlft, -, -, -, -⟩ := hT
  have : LocallyOfFiniteType sX := hlft
  exact isEffectiveCartierDivisor_divisorIdeal sX hsm _ hAfin

/-- **Orders add in codimension one.** On a triple `(Y, J, F)`, if `P·J = Q·N` for ideal sheaves
`P, Q` with stalks generated by nonzero elements and `Supp Q ⊆ Supp F`, then `P·M(J) ⊆ Q`: at
the generic point of a component `C` of `F`, `ord_C Q ≤ ord_C P + ord_C J`. -/
private theorem mul_monomialPart_le {k : Type u} [Field k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (J N : Y.IdealSheafData) (F : OrderedDivisor Y)
    (hT : IsTriple sY J F) (P Q : Y.IdealSheafData)
    (hP : ∀ y, ∃ g : Y.presheaf.stalk y, g ≠ 0 ∧ IdealSheafData.stalk P y = Ideal.span {g})
    (hQ : ∀ y, ∃ q : Y.presheaf.stalk y, q ≠ 0 ∧ IdealSheafData.stalk Q y = Ideal.span {q})
    (hQF : (Q.support : Set Y) ⊆ F.support) (hPQ : P * J = Q * N) :
    P * monomialPart J F ≤ Q := by
  classical
  have hAfin := finite_support_monomialPartCoeff sY J F hT
  obtain ⟨-, hsm, hlft, hqc, -, hJ, hF⟩ := hT
  have : LocallyOfFiniteType sY := hlft
  have : QuasiCompact sY := hqc
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have := smooth_of_isSmoothScheme' sY hsm
  refine le_of_stalk_genericPoint_le sY hsm _ Q hQ fun D => ?_
  by_cases hDQ : D.genericPoint ∈ (Q.support : Set Y)
  swap
  · rw [(IdealSheafData.stalk_eq_top_iff_notMem_support _ _).2 hDQ]
    exact le_top
  have hc := isComponent_of_genericPoint_mem_support sY hsm F hF.2 D (hQF hDQ)
  obtain ⟨_, _⟩ := isDiscreteValuationRing_stalk_genericPoint sY hsm D
  have hne : multAt J D.genericPoint ≠ ⊤ := by
    refine Kollar.multAt_ne_top_of_stalk_genericPoint_ne_bot J (fun T hT => ?_) _
    refine hJ _ ?_
    have h := hT.1.isGenericPoint_genericPoint_closure
    rw [(isClosed_of_mem_irreducibleComponents T hT).closure_eq] at h
    rw [h.def]
    exact hT
  obtain ⟨g, hg0, hg⟩ := hP D.genericPoint
  have hPfin : idealOrder (IdealSheafData.stalk P D.genericPoint) ≠ ⊤ := by
    rw [hg, idealOrder_span_eq_addVal hg0, Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
    exact hg0
  have hst := congrArg (fun K => idealOrder (IdealSheafData.stalk K D.genericPoint)) hPQ
  simp only [IdealSheafData.stalk_mul, idealOrder_mul_of_isDiscreteValuationRing] at hst
  have hMη : IdealSheafData.stalk (monomialPart J F) D.genericPoint =
      IsLocalRing.maximalIdeal (Y.presheaf.stalk D.genericPoint) ^
        (multAt J D.genericPoint).toNat := by
    rw [show monomialPart J F = divisorIdeal (monomialPartCoeff J F) from rfl,
      stalk_divisorIdeal_genericPoint sY hsm _ hAfin]
    simp [monomialPartCoeff, hc]
  have hord : idealOrder (IdealSheafData.stalk (P * monomialPart J F) D.genericPoint) =
      idealOrder (IdealSheafData.stalk P D.genericPoint) + multAt J D.genericPoint := by
    rw [IdealSheafData.stalk_mul, idealOrder_mul_of_isDiscreteValuationRing, hMη,
      idealOrder_maximalIdeal_pow, ENat.coe_toNat hne]
  have hle : idealOrder (IdealSheafData.stalk Q D.genericPoint) ≤
      idealOrder (IdealSheafData.stalk (P * monomialPart J F) D.genericPoint) := by
    rw [hord, multAt, hst]
    exact le_self_add
  refine le_of_idealOrder_le (fun h0 => ?_) hle
  rw [h0, idealOrder_bot, hord] at hle
  exact WithTop.add_ne_top.2 ⟨hPfin, hne⟩ (top_le_iff.1 hle)

/-- On a triple `(Y, J, F)`, if `P·J = Q·N` for ideal sheaves `P, Q` with stalks generated by
nonzero elements and `Supp Q ⊆ Supp F`, then `N ⊆ N(J)`: by `mul_monomialPart_le`,
`P·M(J)·N ⊆ Q·N = P·J = P·M(J)·N(J)`, and `P`, `M(J)` cancel. -/
private theorem le_nonmonomialPart_of_mul_eq {k : Type u} [Field k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (J N : Y.IdealSheafData) (F : OrderedDivisor Y)
    (hT : IsTriple sY J F) (P Q : Y.IdealSheafData)
    (hP : ∀ y, ∃ g : Y.presheaf.stalk y, g ≠ 0 ∧ IdealSheafData.stalk P y = Ideal.span {g})
    (hQ : ∀ y, ∃ q : Y.presheaf.stalk y, q ≠ 0 ∧ IdealSheafData.stalk Q y = Ideal.span {q})
    (hQF : (Q.support : Set Y) ⊆ F.support) (hPQ : P * J = Q * N) :
    N ≤ nonmonomialPart J F := by
  have hPreg : ∀ y, ∃ g : Y.presheaf.stalk y, IsLeftRegular g ∧
      IdealSheafData.stalk P y = Ideal.span {g} := by
    obtain ⟨-, hsm, hlft, -, -, -, -⟩ := hT
    have : LocallyOfFiniteType sY := hlft
    have := smooth_of_isSmoothScheme' sY hsm
    intro y
    have := isRegularLocalRing_stalk_of_smooth_over_field sY y
    have := IsRegularLocalRing.isDomain (Y.presheaf.stalk y)
    obtain ⟨g, hg0, hg⟩ := hP y
    exact ⟨g, fun _ _ h => IsLeftCancelMulZero.mul_left_cancel_of_ne_zero hg0 h, hg⟩
  refine le_of_mul_le_mul_left (fun y =>
    (AlgebraicGeometry.exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor _
      (isEffectiveCartierDivisor_monomialPart sY J F hT) y).imp fun _ h => ⟨h.1.1, h.2⟩) ?_
  rw [monomialPart_mul_nonmonomialPart sY J F hT]
  refine le_of_mul_le_mul_left hPreg ?_
  rw [hPQ, ← mul_assoc]
  gcongr
  exact mul_monomialPart_le sY J N F hT P Q hP hQ hQF hPQ

end MonomialPart

/-- The factorization `𝒪(-P)·I_i = 𝒪(-Q)·N_i` along the sequence: with `Π` the composite and
`Ex` the exceptional ideal, `Π^*I = I_r·Ex^m`, `Π^*N(I) = N_r·Ex^s` and `I = M(I)·N(I)` give
`Ex^m·I_r = (Π^*M(I)·Ex^s)·N_r`; both factors are locally principal, nonzero, and supported
on `Supp E_r`. -/
private theorem exists_mul_eq {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (I : X.IdealSheafData) (E : OrderedDivisor X)
    (m s : ℕ) (hT : IsTriple sX I E) (B : ClosedBlowupSequence X)
    (hBI : B.IsOrderGeMarkedTripleSeq sX ⟨I, m⟩ E)
    (hBN : B.IsOrderGeMarkedTripleSeq sX ⟨nonmonomialPart I E, s⟩ E) :
    ∃ P Q : B.target.IdealSheafData,
      (∀ y, ∃ g : B.target.presheaf.stalk y, g ≠ 0 ∧
        IdealSheafData.stalk P y = Ideal.span {g}) ∧
      (∀ y, ∃ q : B.target.presheaf.stalk y, q ≠ 0 ∧
        IdealSheafData.stalk Q y = Ideal.span {q}) ∧
      (Q.support : Set B.target) ⊆ (B.orderedTotalTransform E).support ∧
      P * (B.markedTransform ⟨I, m⟩).I =
        Q * (B.markedTransform ⟨nonmonomialPart I E, s⟩).I := by
  classical
  have hMN := monomialPart_mul_nonmonomialPart sX I E hT
  have hAfin := finite_support_monomialPartCoeff sX I E hT
  have hM := isEffectiveCartierDivisor_monomialPart sX I E hT
  obtain ⟨-, -, hlft, hqc, -, -, -⟩ := hT
  have : LocallyOfFiniteType sX := hlft
  have : QuasiCompact sX := hqc
  obtain ⟨-, hsmr, hlftr, -, -, -, hFr⟩ :=
    ClosedBlowupSequence.isTriple_target_of_isOrderGeMarkedTripleSeq B sX _ E hBI
  have : LocallyOfFiniteType (B.toBase ≫ sX) := hlftr
  have := smooth_of_isSmoothScheme' _ hsmr
  have h1 := ClosedBlowupSequence.comap_toBase_eq_markedTransform_mul_exceptionalIdeal_pow
    B sX ⟨I, m⟩ E hBI
  have h2 := ClosedBlowupSequence.comap_toBase_eq_markedTransform_mul_exceptionalIdeal_pow
    B sX ⟨nonmonomialPart I E, s⟩ E hBN
  have hExs := ClosedBlowupSequence.support_exceptionalIdeal_subset B sX _ E hBI
  have hpre := ClosedBlowupSequence.preimage_support_subset_support_orderedTotalTransform
    B sX _ E hBI
  have hMtop : ∀ x : X, x ∉ E.support →
      IdealSheafData.stalk (monomialPart I E) x = ⊤ := by
    intro x hx
    refine stalk_divisorIdeal_eq_top _ hAfin (fun D hD => ?_) hx
    have hc : E.IsComponent D := by
      by_contra hnc
      exact hD (by simp [monomialPartCoeff, hnc])
    obtain ⟨i, hi⟩ := hc
    have hi' : Maximal (fun W' : Set X => IsIrreducible W' ∧ W' ⊆ (E.E i).support)
        D.support := hi
    exact fun y hy => Set.mem_iUnion.2 ⟨i, hi'.prop.2 hy⟩
  have hMs : (((monomialPart I E).comap B.toBase).support : Set B.target) ⊆
      ((B.orderedTotalTransform E).support) := by
    intro y hy
    refine hpre ?_
    by_contra hy'
    exact (IdealSheafData.stalk_eq_top_iff_notMem_support _ _).1
      (by rw [IdealSheafData.stalk_comap, hMtop _ hy', Ideal.map_top]) hy
  have hExne := stalk_ne_bot_of_support_subset _ hsmr _ hFr.2 _ hExs
  have hMne := stalk_ne_bot_of_support_subset _ hsmr _ hFr.2 _ hMs
  refine ⟨B.exceptionalIdeal ^ m, (monomialPart I E).comap B.toBase * B.exceptionalIdeal ^ s,
    fun y => ?_, fun y => ?_, fun y hy => ?_, ?_⟩
  · have := isRegularLocalRing_stalk_of_smooth_over_field (B.toBase ≫ sX) y
    have := IsRegularLocalRing.isDomain (B.target.presheaf.stalk y)
    obtain ⟨f, hf⟩ := ClosedBlowupSequence.exists_stalk_exceptionalIdeal_eq_span B y
    have hf0 : f ≠ 0 := fun h0 => hExne y (by rw [hf, h0, Ideal.span_singleton_eq_bot])
    obtain ⟨g, hg0, hg⟩ := exists_span_mul_pow_eq_span one_ne_zero hf0 m
    refine ⟨g, hg0, ?_⟩
    rw [Aux.stalk_pow, hf, ← hg, Ideal.span_singleton_one, Ideal.top_mul]
  · have := isRegularLocalRing_stalk_of_smooth_over_field (B.toBase ≫ sX) y
    have := IsRegularLocalRing.isDomain (B.target.presheaf.stalk y)
    obtain ⟨f, hf⟩ := ClosedBlowupSequence.exists_stalk_exceptionalIdeal_eq_span B y
    have hf0 : f ≠ 0 := fun h0 => hExne y (by rw [hf, h0, Ideal.span_singleton_eq_bot])
    obtain ⟨g, -, hg⟩ :=
      exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor _ hM (B.toBase y)
    have hgs : IdealSheafData.stalk ((monomialPart I E).comap B.toBase) y =
        Ideal.span {(B.toBase.stalkMap y).hom g} := by
      rw [IdealSheafData.stalk_comap, hg, Ideal.map_span, Set.image_singleton]
    have hg0 : (B.toBase.stalkMap y).hom g ≠ 0 := fun h0 =>
      hMne y (by rw [hgs, h0, Ideal.span_singleton_eq_bot])
    obtain ⟨g', hg'0, hg'⟩ := exists_span_mul_pow_eq_span hg0 hf0 s
    refine ⟨g', hg'0, ?_⟩
    rw [IdealSheafData.stalk_mul, Aux.stalk_pow, hgs, hf, hg']
  · by_contra hy'
    refine (IdealSheafData.stalk_eq_top_iff_notMem_support _ _).1 ?_ hy
    have hE1 : IdealSheafData.stalk B.exceptionalIdeal y = ⊤ :=
      (IdealSheafData.stalk_eq_top_iff_notMem_support _ _).2 fun h => hy' (hExs h)
    have hM1 : IdealSheafData.stalk ((monomialPart I E).comap B.toBase) y = ⊤ :=
      (IdealSheafData.stalk_eq_top_iff_notMem_support _ _).2 fun h => hy' (hMs h)
    rw [IdealSheafData.stalk_mul, Aux.stalk_pow, hE1, hM1, Ideal.top_pow, Ideal.top_mul]
  · have h1' : I.comap B.toBase =
        (B.markedTransform ⟨I, m⟩).I * B.exceptionalIdeal ^ m := h1
    have h2' : (nonmonomialPart I E).comap B.toBase =
        (B.markedTransform ⟨nonmonomialPart I E, s⟩).I * B.exceptionalIdeal ^ s := h2
    calc B.exceptionalIdeal ^ m * (B.markedTransform ⟨I, m⟩).I = I.comap B.toBase := by
          rw [h1', mul_comm]
      _ = (monomialPart I E).comap B.toBase * (nonmonomialPart I E).comap B.toBase := by
          conv_lhs => rw [← hMN]
          exact Stacks.IdealSheaf.comap_mul _ _ _
      _ = _ := by rw [h2', mul_comm (B.markedTransform _).I, mul_assoc]

namespace ClosedBlowupSequence

/-- **The transform of `N(I)` lies in the nonmonomial part of the transform** (Kollár 3.111,
Step 2). In the setting of
`isOrderGeMarkedTripleSeq_truncate_of_isOrderMTripleSeq_mixedIdeal`, for every `i` the marked
transform `N_i` of `(nonmonomialPart I E, s)` along `B.truncate i` is contained in
`nonmonomialPart I_i E_i`, where `I_i` is the marked transform of `(I, m)` and `E_i` the iterated
total transform of `E` along `B.truncate i`. -/
@[mmp "lem_kr3e_mixed_ideal_factorization"]
public theorem markedTransform_nonmonomialPart_le_nonmonomialPart {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (I : X.IdealSheafData) (E : OrderedDivisor X)
    (m s : ℕ) (hT : IsTriple sX I E) (hm : 1 ≤ m) (hs : 1 ≤ s)
    (hK : maxOrder (mixedIdeal I E m s) ≤ ((m * s : ℕ) : ℕ∞)) (B : ClosedBlowupSequence X)
    (hB : B.IsOrderMTripleSeq sX (mixedIdeal I E m s) E (m * s)) (i : ℕ) :
    ((B.truncate i).markedTransform ⟨nonmonomialPart I E, s⟩).I ≤
      nonmonomialPart ((B.truncate i).markedTransform ⟨I, m⟩).I
        ((B.truncate i).orderedTotalTransform E) := by
  obtain ⟨hBI, hBN, -⟩ :=
    ClosedBlowupSequence.isOrderGeMarkedTripleSeq_truncate_of_isOrderMTripleSeq_mixedIdeal
      sX I E m s hT hm hs hK B hB i
  obtain ⟨P, Q, hP, hQ, hQF, hPQ⟩ := exists_mul_eq sX I E m s hT (B.truncate i) hBI hBN
  exact le_nonmonomialPart_of_mul_eq _ _ _ _
    (ClosedBlowupSequence.isTriple_target_of_isOrderGeMarkedTripleSeq _ sX _ E hBI)
    P Q hP hQ hQF hPQ

end ClosedBlowupSequence

end MixedIdeal

/-! ### One round of Step 2 lowers `s` -/

private theorem truncate_length {X : Scheme.{u}} (B : ClosedBlowupSequence X) :
    B.truncate B.length = B := by
  induction B with
  | nil _ => rfl
  | cons Z B ih =>
    change ClosedBlowupSequence.cons Z (B.truncate B.length) = _
    rw [ih]

/-- The nonmonomial part of the ideal of a triple is nonzero at the generic points. -/
private theorem isNonzeroAtGenericPoints_nonmonomialPart {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {I : X.IdealSheafData} {E : OrderedDivisor X} (h : IsTriple s I E) :
    IsNonzeroAtGenericPoints (nonmonomialPart I E) := fun η hη hbot =>
  h.2.2.2.2.2.1 η hη (eq_bot_iff.2 (hbot ▸ stalk_le_stalk_of_le (le_idealColon _ _) η))

/-- `K_s(I, m) = N(I)^m + I^s` is nonzero at the generic points of a triple. -/
private theorem isTriple_mixedIdeal {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {I : X.IdealSheafData} {E : OrderedDivisor X} (h : IsTriple s I E)
    (m n : ℕ) : IsTriple s (mixedIdeal I E m n) E := by
  have hN := isNonzeroAtGenericPoints_nonmonomialPart h
  obtain ⟨h1, hsm, hlft, h4, h5, h6, h7⟩ := h
  refine ⟨h1, hsm, hlft, h4, h5, fun η hη h0 => ?_, h7⟩
  have : LocallyOfFiniteType s := hlft
  have : Smooth s := (MMP.Mori.isSmoothScheme_iff _).1 hsm
  have := isRegularLocalRing_stalk_of_smooth_over_field s η
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk η)
  have h1 := stalk_le_stalk_of_le
    (show nonmonomialPart I E ^ m ≤ mixedIdeal I E m n from le_self_add) η
  rw [h0, Aux.stalk_pow, le_bot_iff] at h1
  exact hN η hη (eq_zero_of_pow_eq_zero h1)

/-- The order of `I` at any point is at most its maximal order. -/
private theorem multAt_le_maxOrder {X : Scheme.{u}} (I : X.IdealSheafData) (x : X) :
    multAt I x ≤ maxOrder I :=
  le_iSup₂ (f := fun z (_ : z ∈ Set.univ) => multAt I z) x trivial

/-- If the order of `I` is `< s` at every point of `Z`, then so is its maximal order along `Z`,
for `s ≥ 1` (the bound is needed only when `Z` is empty). -/
private theorem maxOrderAlong_lt_of_forall_lt {X : Scheme.{u}} {I : X.IdealSheafData} {Z : Set X}
    {s : ℕ} (hs : 1 ≤ s) (h : ∀ x ∈ Z, multAt I x < s) : maxOrderAlong I Z < s := by
  have hle : maxOrderAlong I Z ≤ ((s - 1 : ℕ) : ℕ∞) := iSup₂_le fun x hx =>
    Order.le_of_lt_add_one <| by exact_mod_cast (Nat.sub_add_cancel hs).symm ▸ h x hx
  exact hle.trans_lt (by exact_mod_cast Nat.sub_one_lt_of_lt hs)

/-- **Kollár 3.111, Step 2: the invariant `s` drops.** Let `B` be an order-reduction family on
dimensions `a, …, b` (`IsOrderReductionFamily`), `t = (X, I, m, E)` a marked triple of dimension
`d` with `a ≤ d ≤ b` and `m ≥ 1`, and `s ≥ 1` with
`maxOrderAlong (nonmonomialPart I E) (cosupport (I, m)) = s`. Let `P = B d (m * s)` applied to
`(X, mixedIdeal I E m s, E)`, with end `t.endOf m P = (X_r, I_r, m, E_r)`. Then
`maxOrderAlong (nonmonomialPart I_r E_r) (cosupport (I_r, m)) < s`. -/
@[mmp "lem_kr3e_mixed_stage_decreases"]
public theorem maxOrderAlong_nonmonomialPart_endOf_mixedIdeal_lt {a b d s : ℕ}
    (B : UnmarkedFamily.{u}) (hB : IsOrderReductionFamily a b B)
    (t : MarkedTriple.{u}) (ht : t ∈ markedTriples)
    (hdim : topologicalKrullDim t.X = ((d : ℕ∞) : WithBot ℕ∞)) (had : a ≤ d) (hdb : d ≤ b)
    (hm : 1 ≤ t.m)
    (hs : maxOrderAlong (nonmonomialPart t.I t.E) t.markedIdeal.cosupport = s) (hs1 : 1 ≤ s) :
    let P := B d (t.m * s) ⟨⟨t.X, mixedIdeal t.I t.E t.m s, t.E⟩, t.k, t.sX⟩
    let tr := t.endOf t.m P
    maxOrderAlong (nonmonomialPart tr.I tr.E) tr.markedIdeal.cosupport < s := by
  intro P tr
  have hT : IsTriple t.sX t.I t.E := ht
  have hK := maxOrder_mixedIdeal_le t.sX t.I t.E t.m s hT hm hs hs1
  obtain ⟨F, hF, hred, -⟩ := hB (t.m * s) (Nat.one_le_iff_ne_zero.2 (by positivity))
  let T : FieldBlowupTriple.{u} := ⟨⟨t.X, mixedIdeal t.I t.E t.m s, t.E⟩, t.k, t.sX⟩
  have hTmem : T ∈ idealTriplesOfDim (Set.Icc a b) (t.m * s) :=
    ⟨isTriple_mixedIdeal hT t.m s, ⟨d, ⟨had, hdb⟩, hdim⟩, hK⟩
  have hFP : F.toFun T hTmem = P := by
    rw [hF]; congr; change ((topologicalKrullDim t.X).unbotD 0).toNat = d; rw [hdim]; rfl
  have hPseq : P.IsOrderMTripleSeq t.sX (mixedIdeal t.I t.E t.m s) t.E (t.m * s) :=
    hFP ▸ F.isOrderMTripleSeq T hTmem
  have hPred : maxOrder (P.controlledTransform (mixedIdeal t.I t.E t.m s)) < t.m * s :=
    hFP ▸ hred T hTmem
  obtain ⟨hIseq, -, hKr⟩ :=
    ClosedBlowupSequence.isOrderGeMarkedTripleSeq_truncate_of_isOrderMTripleSeq_mixedIdeal
      t.sX t.I t.E t.m s hT hm hs1 hK P hPseq P.length
  have hfac := ClosedBlowupSequence.markedTransform_nonmonomialPart_le_nonmonomialPart
      t.sX t.I t.E t.m s hT hm hs1 hK P hPseq P.length
  rw [truncate_length] at hIseq hKr hfac
  have hTr :=
    ClosedBlowupSequence.isTriple_target_of_isOrderGeMarkedTripleSeq P t.sX ⟨t.I, t.m⟩ t.E hIseq
  have : LocallyOfFiniteType (P.toBase ≫ t.sX) := hTr.2.2.1
  have : QuasiCompact (P.toBase ≫ t.sX) := hTr.2.2.2.1
  refine maxOrderAlong_lt_of_forall_lt hs1 fun x hx =>
    (Kollar.multAt_antitone hfac x).trans_lt (lt_of_not_ge fun hge => ?_)
  have hord := (le_multAt_pow_sup_pow_iff hTr.2.1 hTr.2.2.2.2.1 _ tr.I hs1 hm x).1 ⟨hge, hx⟩
  have hlt := (multAt_le_maxOrder _ x).trans_lt hPred
  rw [hKr] at hlt
  exact hlt.not_ge (by exact_mod_cast hord)

/-! ### Step 2 of `𝓑𝓜𝓞` -/

/-- The conclusion for a sequence `S`: it is of order `≥ m` starting with `(X, I, m, E)` and at
its end the marked cosupport is disjoint from the cosupport of the nonmonomial part. -/
private def StepTwoGood {k : Type u} [Field k] {X : Scheme.{u}} (s : X ⟶ Spec (.of k))
    (a : MarkedIdeal X) (E : OrderedDivisor X) (S : ClosedBlowupSequence X) : Prop :=
  S.IsOrderGeMarkedTripleSeq s a E ∧
    Disjoint (⟨(S.markedTransform a).I, a.m⟩ : MarkedIdeal S.target).cosupport
      ((nonmonomialPart (S.markedTransform a).I (S.orderedTotalTransform E)).support : Set _)

private theorem markedTransform_eq {X : Scheme.{u}} (S : ClosedBlowupSequence X)
    (a : MarkedIdeal X) : S.markedTransform a = ⟨(S.markedTransform a).I, a.m⟩ := by
  cases h : S.markedTransform a
  have := S.markedTransform_m a
  rw [h] at this
  subst this
  rfl

/-- Concatenation: `S` of order `≥ m`, followed by a good sequence starting with its end. -/
private theorem stepTwoGood_append {k : Type u} [Field k] {X : Scheme.{u}} :
    ∀ (S : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X)
      (E : OrderedDivisor X) (T : ClosedBlowupSequence S.target),
      S.IsOrderGeMarkedTripleSeq s a E →
      StepTwoGood (S.toBase ≫ s) (S.markedTransform a) (S.orderedTotalTransform E) T →
      StepTwoGood s a E (S.append T)
  | .nil X, s, a, E, T, _, hT => by
    change StepTwoGood (𝟙 X ≫ s) a E T at hT
    rw [Category.id_comp] at hT; exact hT
  | .cons Z S, s, a, E, T, hS, hT => by
    have ih := stepTwoGood_append S (blowUpToBase Z ≫ s) (a.birationalTransform Z)
      (E.totalTransform Z) T hS.2.2.2.2.2 (by
        change StepTwoGood ((S.toBase ≫ blowUpToBase Z) ≫ s) _ _ T at hT
        rw [Category.assoc] at hT; exact hT)
    exact ⟨⟨hS.1, hS.2.1, hS.2.2.1, hS.2.2.2.1, hS.2.2.2.2.1, ih.1⟩, ih.2⟩

/-- `StepTwoGood` passes into the true branch of an `if`; stated for an arbitrary `Decidable`
instance, so that it applies where the branches only typecheck up to defeq. -/
private theorem stepTwoGood_ite {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X) (E : OrderedDivisor X) {p : Prop} {_ : Decidable p}
    (x y : ClosedBlowupSequence X) (hp : p) (h : StepTwoGood s a E x) :
    StepTwoGood s a E (if p then x else y) := by
  rwa [if_pos hp]

/-! ### Dimension along a blow-up sequence -/

/-- A nonempty scheme carrying a triple has Krull dimension `dimNat X`. -/
private theorem topologicalKrullDim_eq_dimNat {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {I : X.IdealSheafData} {E : OrderedDivisor X} (h : IsTriple s I E)
    [Nonempty X] : topologicalKrullDim X = ((dimNat X : ℕ∞) : WithBot ℕ∞) := by
  obtain ⟨-, -, hlft, hqc, -⟩ := h
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  have htop := topologicalKrullDim_ne_top_of_locallyOfFiniteType k s
  have hbot : topologicalKrullDim X ≠ ⊥ := by
    unfold topologicalKrullDim
    rw [Ne, Order.krullDim_eq_bot_iff, not_isEmpty_iff]
    obtain ⟨x⟩ := ‹Nonempty X›
    exact ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  unfold dimNat
  generalize topologicalKrullDim X = e at htop hbot ⊢
  induction e using WithBot.recBotCoe with
  | bot => exact absurd rfl hbot
  | coe e =>
    induction e using WithTop.recTopCoe with
    | top => exact absurd rfl htop
    | coe n => rfl

/-- A generic point of `X` lies off a closed subscheme all of whose components have positive
codimension. -/
private theorem notMem_supportSet_of_mem_genericPoints {X : Scheme.{u}}
    {Z : X.IdealSheafData} (hZ : HasComponentsOfPositiveCodim (Z.support : Set X)) {ξ : X}
    (hξ : ξ ∈ genericPoints X) : ξ ∉ Z.supportSet := by
  intro h
  have h' : ξ ∈ (Z.support : Set X) := Scheme.IdealSheafData.mem_supportSet_iff_mem_support.1 h
  obtain ⟨W, hW, hξW⟩ := exists_mem_componentsOf h'
  have hD : closure {ξ} ∈ irreducibleComponents X := hξ
  have hDW : closure {ξ} ⊆ closure W := closure_mono (Set.singleton_subset_iff.2 hξW)
  have hcod := hZ W hW
  rw [codimension_eq_coheight] at hcod
  have hmax : IsMax (irreducibleClosure hW.1.1) := fun C hC => by
    have hC' : closure W ⊆ (C : Set X) := hC
    have : (C : Set X) ⊆ closure {ξ} := hD.2 C.isIrreducible (hDW.trans hC')
    exact this.trans hDW
  rw [Order.coheight_eq_zero.2 hmax] at hcod
  exact absurd hcod (by norm_num)

/-- The blow-up of an equidimensional scheme locally of finite type over a field along a closed
subscheme all of whose components have positive codimension has the same dimension. -/
private theorem topologicalKrullDim_blowUp {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s] (hX : TopologicalSpace.Equidimensional X)
    (Z : X.IdealSheafData) (hZ : HasComponentsOfPositiveCodim (Z.support : Set X)) :
    topologicalKrullDim (blowUp Z) = topologicalKrullDim X := by
  rw [topologicalKrullDim_eq_iSup_irreducibleComponents (blowUp Z),
    topologicalKrullDim_eq_iSup_irreducibleComponents X]
  apply le_antisymm
  · refine iSup₂_le fun C hC => ?_
    obtain ⟨D, hD, h⟩ := exists_topologicalKrullDim_eq_of_mem_irreducibleComponents_blowUp s Z hC
    rw [h]
    exact le_iSup₂ (f := fun D (_ : D ∈ irreducibleComponents X) => topologicalKrullDim D) D hD
  · refine iSup₂_le fun D hD => ?_
    have hgen := hD.1.isGenericPoint_genericPoint_closure
    rw [(isClosed_of_mem_irreducibleComponents D hD).closure_eq] at hgen
    have hξ : hD.1.genericPoint ∈ genericPoints X := by
      change closure {_} ∈ irreducibleComponents X
      rw [hgen.def]; exact hD
    obtain ⟨η, hη, -⟩ := (bijOn_genericPoints_blowUpToBase Z).2.2
      ⟨hξ, notMem_supportSet_of_mem_genericPoints hZ hξ⟩
    have hC : closure {η} ∈ irreducibleComponents (blowUp Z) := hη
    obtain ⟨D', hD', h⟩ := exists_topologicalKrullDim_eq_of_mem_irreducibleComponents_blowUp s Z hC
    rw [hX D hD D' hD', ← h]
    exact le_iSup₂ (f := fun C (_ : C ∈ irreducibleComponents (blowUp Z)) =>
      topologicalKrullDim C) _ hC

/-- A smooth blow-up sequence of order `μ` starting with a triple keeps the dimension. -/
private theorem dimNat_target {k : Type u} [Field k] {μ : ℕ} {X : Scheme.{u}} :
    ∀ (S : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k)) (I : X.IdealSheafData)
      (E : OrderedDivisor X), S.IsOrderMTripleSeq s I E μ → dimNat S.target = dimNat X
  | .nil _, _, _, _, _ => rfl
  | .cons Z S, s, I, E, hS => by
    obtain ⟨⟨-, -, hlft, -, hX, -⟩, -, hcod, -, -, hS'⟩ := hS
    have := hlft
    refine (dimNat_target S _ _ _ hS').trans ?_
    unfold dimNat
    rw [topologicalKrullDim_blowUp s hX Z hcod]

/-! ### The invariant `s` -/

/-- A point of the cosupport of an ideal sheaf has order at least one. -/
private theorem one_le_multAt_of_mem_support {X : Scheme.{u}} (I : X.IdealSheafData) {x : X}
    (hx : x ∈ (I.support : Set X)) : 1 ≤ multAt I x := by
  rw [← Nat.cast_one, multAt, natCast_le_idealOrder_iff', pow_one]
  exact IsLocalRing.le_maximalIdeal fun h =>
    (IdealSheafData.stalk_eq_top_iff_notMem_support I x |>.1 h) hx

/-- For a triple, the maximal order of `N(I)` along a set is finite. -/
private theorem maxOrderAlong_nonmonomialPart_ne_top {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {I : X.IdealSheafData} {E : OrderedDivisor X} (h : IsTriple s I E)
    (Z : Set X) : maxOrderAlong (nonmonomialPart I E) Z ≠ ⊤ := by
  rcases Z.eq_empty_or_nonempty with rfl | hZ
  · simp [maxOrderAlong]
  have hN := isNonzeroAtGenericPoints_nonmonomialPart h
  obtain ⟨-, hsm, hlft, hqc, -, -, -⟩ := h
  have : LocallyOfFiniteType s := hlft
  have : QuasiCompact s := hqc
  have : Smooth s := (MMP.Mori.isSmoothScheme_iff _).1 hsm
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x =>
    have := isRegularLocalRing_stalk_of_smooth_over_field s x
    have := IsRegularLocalRing.isDomain (X.presheaf.stalk x)
    inferInstance
  have : IsReduced X := isReduced_of_isReduced_stalk _
  refine (exists_multAt_eq_maxOrderAlong s _ ?_ hZ).1
  intro W hW hsub
  have hgen := (QuasiSober.sober hW.1 (isClosed_of_mem_irreducibleComponents W hW)).choose_spec
  set η := (QuasiSober.sober hW.1 (isClosed_of_mem_irreducibleComponents W hW)).choose
  have hη : closure ({η} : Set X) ∈ irreducibleComponents X := by
    rw [hgen.def]; exact hW
  have hF := isField_stalk_of_closure_mem_irreducibleComponents X η hη
  have hbot := hN η hη
  have htop : IdealSheafData.stalk (nonmonomialPart I E) η ≠ ⊤ := fun h =>
    (IdealSheafData.stalk_eq_top_iff_notMem_support _ η).1 h (hsub hgen.mem)
  letI := hF.toField
  exact (Ideal.eq_bot_or_top _).elim hbot htop

/-! ### The Step-2 recursion -/

private theorem maxOrderAlong_eq_bmoStepTwoOrder (m : ℕ) (t : MarkedTriple.{u})
    (ht : t ∈ markedTriples) :
    maxOrderAlong (nonmonomialPart t.I t.E) (⟨t.I, m⟩ : MarkedIdeal t.X).cosupport =
      (bmoStepTwoOrder m t : ℕ∞) :=
  (ENat.coe_toNat (maxOrderAlong_nonmonomialPart_ne_top (s := t.sX) ht _)).symm

/-- The Step-2 recursion with fuel `q` is good once the fuel exceeds the invariant
`s = maxord_{cosupp(I, m)} N(I)`: each round is of order `≥ m` and strictly lowers `s`. -/
private theorem stepTwoGood_bmoStepTwoAux {a b : ℕ} {B : UnmarkedFamily.{u}}
    (hB : IsOrderReductionFamily a b B)
    {m : ℕ} (hm : 1 ≤ m) {d : ℕ} (hd : d ∈ Set.Icc a b) :
    ∀ (q : ℕ) (t : MarkedTriple.{u}), t ∈ markedTriples → dimNat t.X = d →
      bmoStepTwoOrder m t < q →
      StepTwoGood t.sX ⟨t.I, m⟩ t.E (bmoStepTwoAux B d m q t)
  | 0, _, _, _, hq => absurd hq (Nat.not_lt_zero _)
  | q + 1, t, ht, hdt, hq => by
    have ht0 : IsTriple t.sX t.I t.E := ht
    have hσ := maxOrderAlong_eq_bmoStepTwoOrder m t ht
    rw [bmoStepTwoAux]
    split_ifs with h0
    · refine ⟨ht0, Set.disjoint_left.2 fun x hx hxN => ?_⟩
      have h1 := one_le_multAt_of_mem_support _ hxN
      have h2 : multAt (nonmonomialPart t.I t.E) x ≤ 0 := by
        rw [← Nat.cast_zero, ← h0, ← hσ]
        exact le_iSup₂ (f := fun z (_ : z ∈ (⟨t.I, m⟩ : MarkedIdeal t.X).cosupport) =>
          multAt (nonmonomialPart t.I t.E) z) x hx
      exact absurd (h1.trans h2) (by norm_num)
    · set σ := bmoStepTwoOrder m t
      have hσ1 : 1 ≤ σ := Nat.one_le_iff_ne_zero.2 h0
      have hne : Nonempty t.X := by
        by_contra hX
        rw [not_nonempty_iff] at hX
        have : maxOrderAlong (nonmonomialPart t.I t.E)
            (⟨t.I, m⟩ : MarkedIdeal t.X).cosupport = 0 := by simp [maxOrderAlong]
        rw [hσ, Nat.cast_eq_zero] at this
        exact h0 this
      have hK := maxOrder_mixedIdeal_le t.sX t.I t.E m σ ht0 hm hσ hσ1
      have hmσ : 1 ≤ m * σ := Nat.one_le_iff_ne_zero.2 (by positivity)
      obtain ⟨F, hFB, -, -⟩ := hB _ hmσ
      have ht' : (⟨⟨t.X, mixedIdeal t.I t.E m σ, t.E⟩, t.k, t.sX⟩ : FieldBlowupTriple.{u}) ∈
          idealTriplesOfDim (Set.Icc a b) (m * σ) :=
        ⟨isTriple_mixedIdeal ht0 m σ,
          ⟨d, hd, by rw [← hdt]; exact topologicalKrullDim_eq_dimNat ht0⟩, hK⟩
      have hS := F.isOrderMTripleSeq _ ht'
      rw [hFB] at hS
      simp only [show dimNat t.X = d from hdt] at hS
      have hS1 :=
        (ClosedBlowupSequence.isOrderGeMarkedTripleSeq_truncate_of_isOrderMTripleSeq_mixedIdeal
          t.sX t.I t.E m σ ht0 hm hσ1 hK _ hS
          (B d (m * σ) ⟨⟨t.X, mixedIdeal t.I t.E m σ, t.E⟩, t.k, t.sX⟩).length).1
      rw [truncate_length] at hS1
      dsimp only
      refine stepTwoGood_append _ t.sX ⟨t.I, m⟩ t.E _ hS1 ?_
      have h1' : t.endOf m (B d (m * σ)
          ⟨⟨t.X, mixedIdeal t.I t.E m σ, t.E⟩, t.k, t.sX⟩) ∈ markedTriples :=
        ClosedBlowupSequence.isTriple_target_of_isOrderGeMarkedTripleSeq _ _ _ _ hS1
      refine stepTwoGood_ite _ _ _ _ _ h1' ?_
      rw [markedTransform_eq]
      refine stepTwoGood_bmoStepTwoAux hB hm hd q _ h1' ?_ ?_
      · exact (dimNat_target _ _ _ _ hS).trans hdt
      · have hlt := maxOrderAlong_nonmonomialPart_endOf_mixedIdeal_lt (s := σ) B hB
          ⟨t.toFieldBlowupTriple, m⟩ ht (d := d)
          (by rw [← hdt]; exact topologicalKrullDim_eq_dimNat ht0) hd.1 hd.2 hm hσ hσ1
        have hlt' : (bmoStepTwoOrder m (t.endOf m (B d (m * σ)
            ⟨⟨t.X, mixedIdeal t.I t.E m σ, t.E⟩, t.k, t.sX⟩)) : ℕ∞) < σ := by
          rw [← maxOrderAlong_eq_bmoStepTwoOrder m _ h1']
          exact hlt
        have := ENat.coe_lt_coe.1 hlt'
        omega

/-- **Kollár 3.111, Step 2.** Let `B` be an order-reduction family on dimensions `a, …, b`,
`m ≥ 1`, and `t = (X, I, E)` a marked triple with `a ≤ dim X ≤ b`. Then the Step-2 sequence
`bmoStepTwo B (dimNat t.X) m t` is a smooth blow-up sequence of order `≥ m` starting with
`(X, I, m, E)`, and its end `(X_2, I_2, m, E_2)` has `cosupp(I_2, m)` disjoint from
`cosupp N(I_2)`. -/
@[mmp "lem_kr3e_bmo_step_two_result"]
public theorem isOrderGeMarkedTripleSeq_bmoStepTwo {a b : ℕ} {B : UnmarkedFamily.{u}}
    (hB : IsOrderReductionFamily a b B) {m : ℕ} (hm : 1 ≤ m) {t : MarkedTriple.{u}}
    (ht : t ∈ markedTriples) (hdim : dimNat t.X ∈ Set.Icc a b) :
    (bmoStepTwo B (dimNat t.X) m t).IsOrderGeMarkedTripleSeq t.sX ⟨t.I, m⟩ t.E ∧
      Disjoint (⟨(t.endOf m (bmoStepTwo B (dimNat t.X) m t)).I, m⟩ :
          MarkedIdeal (t.endOf m (bmoStepTwo B (dimNat t.X) m t)).X).cosupport
        ((nonmonomialPart (t.endOf m (bmoStepTwo B (dimNat t.X) m t)).I
          (t.endOf m (bmoStepTwo B (dimNat t.X) m t)).E).support : Set _) :=
  stepTwoGood_bmoStepTwoAux hB hm hdim _ t ht rfl (Nat.lt_succ_self _)

/-! ### `𝓑𝓜𝓞_{d,m}[𝓑]` is a smooth blow-up sequence of order `≥ m` -/

/-- A concatenation of smooth blow-up sequences of order `≥ m`, the second starting with the end
of the first, is a smooth blow-up sequence of order `≥ m`. -/
private theorem isOrderGeMarkedTripleSeq_append {k : Type u} [Field k] :
    ∀ {X : Scheme.{u}} (D : ClosedBlowupSequence X) (C : ClosedBlowupSequence D.target)
      (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X) (E : OrderedDivisor X),
      D.IsOrderGeMarkedTripleSeq s a E →
      C.IsOrderGeMarkedTripleSeq (D.toBase ≫ s) ⟨(D.markedTransform a).I, a.m⟩
        (D.orderedTotalTransform E) →
      (D.append C).IsOrderGeMarkedTripleSeq s a E
  | _, .nil _, C, s, a, E, _, hC => by
    change C.IsOrderGeMarkedTripleSeq (𝟙 _ ≫ s) ⟨a.I, a.m⟩ E at hC
    rwa [Category.id_comp] at hC
  | _, .cons Z D, C, s, a, E, hD, hC => by
    obtain ⟨h1, h2, h3, h4, h5, hD'⟩ := hD
    refine ⟨h1, h2, h3, h4, h5, isOrderGeMarkedTripleSeq_append D C _ _ _ hD' ?_⟩
    change C.IsOrderGeMarkedTripleSeq ((D.toBase ≫ blowUpToBase Z) ≫ s) _ _ at hC
    rwa [Category.assoc] at hC

/-- `E'` arises from `F` by deleting some entries equal to `⊤`, i.e. some empty divisors. -/
private def IsDeletionOfEmpty {Y : Scheme.{u}} (E' F : OrderedDivisor Y) : Prop :=
  ∃ f : Fin E'.s → Fin F.s, Function.Injective f ∧ (∀ i, E'.E i = F.E (f i)) ∧
    ∀ j, j ∉ Set.range f → F.E j = ⊤

private theorem isDeletionOfEmpty_refl {Y : Scheme.{u}} (E : OrderedDivisor Y) :
    IsDeletionOfEmpty E E :=
  ⟨id, Function.injective_id, fun _ => rfl, fun j hj => absurd ⟨j, rfl⟩ hj⟩

private theorem IsDeletionOfEmpty.support_eq {Y : Scheme.{u}} {E' F : OrderedDivisor Y}
    (h : IsDeletionOfEmpty E' F) : E'.support = F.support := by
  obtain ⟨f, -, hE, hF⟩ := h
  ext x
  simp only [OrderedDivisor.support, Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨f i, hE i ▸ hi⟩
  · rintro ⟨j, hj⟩
    by_cases hr : j ∈ Set.range f
    · obtain ⟨i, rfl⟩ := hr
      exact ⟨i, (hE i).symm ▸ hj⟩
    · rw [hF j hr, Scheme.IdealSheafData.support_top] at hj
      exact absurd hj (Set.notMem_empty x)

/-- A subfamily of a simple normal crossing family is one. -/
private theorem isSNCFamily_comp {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {Λ Λ' : Type*} {E : Λ → X.IdealSheafData}
    (h : IsSNCFamily sX E) {f : Λ' → Λ} (hf : Function.Injective f) :
    IsSNCFamily sX (E ∘ f) := by
  refine ⟨fun i => h.1 (f i), fun x => ?_⟩
  obtain ⟨n, z, c, hz, hE, hinj⟩ := h.2 x
  exact ⟨n, z, fun i => c ⟨f i.1, i.2⟩, hz, fun i => hE ⟨f i.1, i.2⟩,
    fun i j hij => Subtype.ext (hf (congrArg Subtype.val (hinj hij)))⟩

/-- A centre with simple normal crossings with a family has them with every subfamily. -/
private theorem hasSNCWith_comp {X : Scheme.{u}} {Λ Λ' : Type*} {E : Λ → X.IdealSheafData}
    {Z : X.IdealSheafData} (h : HasSNCWith E Z) {f : Λ' → Λ} (hf : Function.Injective f) :
    HasSNCWith (E ∘ f) Z := by
  intro x hx
  obtain ⟨n, z, c, J, hz, hE, hinj, hZ⟩ := h x hx
  exact ⟨n, z, fun i => c ⟨f i.1, i.2⟩, J, hz, fun i => hE ⟨f i.1, i.2⟩,
    fun i j hij => Subtype.ext (hf (congrArg Subtype.val (hinj hij))), hZ⟩

private theorem IsDeletionOfEmpty.hasSNCWith {X : Scheme.{u}} {E' F : OrderedDivisor X}
    (h : IsDeletionOfEmpty E' F) {Z : X.IdealSheafData} (hZ : HasSNCWith F.E Z) :
    HasSNCWith E'.E Z := by
  obtain ⟨f, hf, hE, -⟩ := h
  rw [show E'.E = F.E ∘ f from funext hE]
  exact hasSNCWith_comp hZ hf

private theorem IsDeletionOfEmpty.isTriple {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {I : X.IdealSheafData} {E' F : OrderedDivisor X}
    (h : IsDeletionOfEmpty E' F) (hF : IsTriple s I F) : IsTriple s I E' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hF
  obtain ⟨f, hf, hE, -⟩ := h
  have he : E'.E = F.E ∘ f := funext hE
  refine ⟨h1, h2, h3, h4, h5, h6, fun i => ?_, ?_⟩
  · rw [hE i]; exact h7 (f i)
  · change IsSNCFamily s E'.E
    rw [he]
    exact isSNCFamily_comp h8 hf

/-- Deleting empty entries commutes with the total transform. -/
private theorem IsDeletionOfEmpty.totalTransform {X : Scheme.{u}} {E' F : OrderedDivisor X}
    (h : IsDeletionOfEmpty E' F) (W : X.IdealSheafData) :
    IsDeletionOfEmpty (E'.totalTransform W) (F.totalTransform W) := by
  have hs := h.support_eq
  obtain ⟨f, hf, hE, hF⟩ := h
  let g : Fin (E'.s + 1) → Fin (F.s + 1) :=
    Fin.lastCases (Fin.last _) (fun i => (f i).castSucc)
  have hgl : g (Fin.last _) = Fin.last _ := Fin.lastCases_last
  have hgc : ∀ i, g i.castSucc = (f i).castSucc := fun i => Fin.lastCases_castSucc _
  refine ⟨g, ?_, ?_, ?_⟩
  · intro i j hij
    induction i using Fin.lastCases <;> induction j using Fin.lastCases
    · rfl
    · simp only [hgl, hgc] at hij; exact absurd hij.symm (Fin.castSucc_ne_last _)
    · simp only [hgl, hgc] at hij; exact absurd hij (Fin.castSucc_ne_last _)
    · rw [hgc, hgc] at hij; rw [hf (Fin.castSucc_injective _ hij)]
  · intro i
    induction i using Fin.lastCases with
    | last =>
      rw [hgl]
      simp only [OrderedDivisor.totalTransform, Fin.snoc_last, hs]
    | cast i =>
      rw [hgc]
      simp only [OrderedDivisor.totalTransform, Fin.snoc_castSucc, hE]
  · intro j hj
    induction j using Fin.lastCases with
    | last => exact absurd ⟨Fin.last _, hgl⟩ hj
    | cast j =>
      have hj' : j ∉ Set.range f := fun ⟨i, hi⟩ => hj ⟨i.castSucc, by rw [hgc, hi]⟩
      simp only [OrderedDivisor.totalTransform, Fin.snoc_castSucc, hF j hj',
        Scheme.IdealSheafData.support_top]
      convert Scheme.IdealSheafData.vanishingIdeal_bot
      ext x
      simp

private theorem comap_comap_inv_orderedDivisor {X Y : Scheme.{u}} (ψ : Y ⟶ X) [IsIso ψ]
    (E : OrderedDivisor X) : (E.comap ψ).comap (inv ψ) = E := by
  simp only [OrderedDivisor.comap, Kollar.comap_comap_inv]

private theorem range_inv {X Y : Scheme.{u}} (ψ : Y ⟶ X) [IsIso ψ] (S : Set Y) :
    S ⊆ Set.range (inv ψ) := fun y _ => ⟨ψ y, by
  rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl⟩

/-- The end of a smooth blow-up sequence of order `≥ m` starting with a marked triple has the
dimension of its start. -/
private theorem dimNat_target_of_isOrderGeMarkedTripleSeq {k : Type u} [Field k] :
    ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X)
      (E : OrderedDivisor X), B.IsOrderGeMarkedTripleSeq s a E → dimNat B.target = dimNat X
  | _, .nil _, _, _, _, _ => rfl
  | _, .cons Z B, s, a, E, hB => by
    obtain ⟨⟨-, -, hlft, -, hequi, -, -⟩, -, hc, -, -, hB'⟩ := hB
    have : LocallyOfFiniteType s := hlft
    refine (dimNat_target_of_isOrderGeMarkedTripleSeq B _ _ _ hB').trans ?_
    simp only [dimNat, topologicalKrullDim_blowUp s hequi Z hc]

/-- On an equidimensional scheme locally of finite type over a field, the local dimension at
every point is the dimension of any irreducible component. -/
private theorem topologicalKrullDimAt_eq_of_equidimensional (k : Type u) [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (hX : Equidimensional X) {C : Set X} (hC : C ∈ irreducibleComponents X)
    (x : X) : topologicalKrullDimAt X x = topologicalKrullDim C := by
  rw [topologicalKrullDimAt_eq_iSup_irreducibleComponents k X s x]
  refine le_antisymm (iSup₂_le fun D hD => (hX D hD.1 C hC).le) ?_
  exact (hX _ (irreducibleComponent_mem_irreducibleComponents x) C hC).symm.le.trans
    (le_iSup₂ (f := fun D (_ : D ∈ {D | D ∈ irreducibleComponents X ∧ x ∈ D}) =>
      topologicalKrullDim D) _ ⟨irreducibleComponent_mem_irreducibleComponents x,
        mem_irreducibleComponent⟩)

/-- The dimension of an irreducible component is the local dimension at its generic point. -/
private theorem exists_topologicalKrullDimAt_eq (k : Type u) [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s] {Z : Set X}
    (hZ : Z ∈ irreducibleComponents X) :
    ∃ η ∈ Z, topologicalKrullDimAt X η = topologicalKrullDim Z := by
  obtain ⟨η, hη⟩ := QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents Z hZ)
  refine ⟨η, hη.mem, ?_⟩
  rw [topologicalKrullDimAt_eq_iSup_irreducibleComponents k X s η]
  refine le_antisymm (iSup₂_le fun Z' hZ' => ?_)
    (le_iSup₂ (f := fun Z' (_ : Z' ∈ {Z' | Z' ∈ irreducibleComponents X ∧ η ∈ Z'}) =>
      topologicalKrullDim Z') Z ⟨hZ, hη.mem⟩)
  have hle : Z ⊆ Z' := by
    rw [← (show closure {η} = Z from hη)]
    exact (isClosed_of_mem_irreducibleComponents Z' hZ'.1).closure_subset_iff.2
      (Set.singleton_subset_iff.2 hZ'.2)
  rw [(hZ.2 hZ'.1.1 hle).antisymm hle]

/-- The restriction `(Y, j⁻¹I, j⁻¹E)` of a triple along an open immersion `j : Y → X` with
`Y → Spec k` quasi-compact is a triple. -/
private theorem isTriple_comap_of_isOpenImmersion {k : Type u} [Field k] {X Y : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) {I : X.IdealSheafData} {E : OrderedDivisor X} (h : IsTriple s I E)
    (j : Y ⟶ X) [IsOpenImmersion j] [QuasiCompact (j ≫ s)] :
    IsTriple (j ≫ s) (I.comap j) (E.comap j) := by
  let t : FieldBlowupTriple.{u} := ⟨⟨X, I, E⟩, k, s⟩
  have ht : t ∈ triples := h
  have : LocallyOfFiniteType s := h.2.2.1
  have hp : t.pullback j ∈ triples := by
    refine mem_triples_iff.2 ⟨pullback_mem_sncTriples (mem_sncTriples_of_mem_triples ht) j, ?_⟩
    intro W hW W' hW'
    obtain ⟨η, -, hη⟩ := exists_topologicalKrullDimAt_eq k (j ≫ s) hW
    obtain ⟨η', -, hη'⟩ := exists_topologicalKrullDimAt_eq k (j ≫ s) hW'
    have hC := irreducibleComponent_mem_irreducibleComponents (j η)
    refine hη.symm.trans (Eq.trans ?_ hη')
    rw [← j.isOpenEmbedding.topologicalKrullDimAt_eq η,
      ← j.isOpenEmbedding.topologicalKrullDimAt_eq η',
      topologicalKrullDimAt_eq_of_equidimensional k s h.2.2.2.2.1 hC,
      topologicalKrullDimAt_eq_of_equidimensional k s h.2.2.2.2.1 hC]
  exact hp

/-- The restriction `(U, I|_U, E|_U)` of a triple to an open `U` is a triple. -/
private theorem isTriple_comap_opens {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) {I : X.IdealSheafData} {E : OrderedDivisor X} (h : IsTriple s I E)
    (U : X.Opens) : IsTriple (U.ι ≫ s) (I.comap U.ι) (E.comap U.ι) := by
  have : LocallyOfFiniteType s := h.2.2.1
  have : QuasiCompact s := h.2.2.2.1
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  have : IsNoetherian X := {}
  have : CompactSpace U := by
    refine ⟨?_⟩
    have hc : IsCompact (Set.range U.ι) := NoetherianSpace.isCompact _
    rw [U.ι.isOpenEmbedding.isInducing.isCompact_iff, Set.image_univ]
    exact hc
  have : QuasiCompact (U.ι ≫ s) := quasiCompact_of_compactSpace _
  exact isTriple_comap_of_isOpenImmersion s h U.ι

/-- Deleting entries `⊤` from the total transform along the empty centre: on `Y ≅ B_∅X`, the
total transform of `E` is `E` (pulled back) followed by an empty entry. -/
private theorem isDeletionOfEmpty_totalTransform_top {X Y : Scheme.{u}} (ψ : Y ⟶ X) [IsIso ψ]
    (ψ₁ : Y ⟶ blowUp (⊤ : X.IdealSheafData)) [IsIso ψ₁] (hψ : ψ₁ ≫ blowUpToBase ⊤ = ψ)
    (E : OrderedDivisor X) (hred : ∀ j, IsReduced (E.E j).subscheme) (E' : OrderedDivisor Y)
    (h : IsDeletionOfEmpty E' (E.comap ψ)) :
    IsDeletionOfEmpty E' ((E.totalTransform ⊤).comap ψ₁) := by
  obtain ⟨f, hf, hE, hF⟩ := h
  have hC2 : componentsOfCodimAtLeastTwo ((⊤ : X.IdealSheafData).support : Set X) = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun x hx => ?_
    simp only [componentsOfCodimAtLeastTwo, Set.mem_iUnion] at hx
    obtain ⟨W, hW, -, hx⟩ := hx
    simpa [Scheme.IdealSheafData.support_top] using hW.1.2 hx
  have key : ∀ j, ((E.totalTransform ⊤).E j.castSucc).comap ψ₁ = (E.E j).comap ψ := by
    intro j
    simp only [OrderedDivisor.totalTransform, Fin.snoc_castSucc]
    rw [hC2, Set.diff_empty]
    have := hred j
    let T : Closeds Y := ⟨ψ ⁻¹' (E.E j).support, (E.E j).support.isClosed.preimage ψ.continuous⟩
    conv_rhs => rw [Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme (E.E j)
      (E.E j).support rfl]
    rw [IsReducedFlatBaseChange.comap_vanishingIdeal (IsReducedFlatBaseChange.of_smooth ψ₁) _ T,
      IsReducedFlatBaseChange.comap_vanishingIdeal (IsReducedFlatBaseChange.of_smooth ψ) _ T rfl]
    change ψ ⁻¹' _ = ψ₁ ⁻¹' closure _
    rw [((E.E j).support.isClosed.preimage (blowUpToBase ⊤).continuous).closure_eq, ← hψ]
    rfl
  have klast : ((E.totalTransform ⊤).E (Fin.last _)).comap ψ₁ = ⊤ := by
    simp only [OrderedDivisor.totalTransform, Fin.snoc_last]
    convert Scheme.IdealSheafData.comap_top ψ₁
    convert Scheme.IdealSheafData.vanishingIdeal_bot
    ext y
    simp only [Closeds.coe_closure, Closeds.coe_bot, Set.mem_empty_iff_false, iff_false]
    rw [show (⋃ (W : Set X) (_ : W ∈ componentsOf ((⊤ : X.IdealSheafData).support : Set X))
        (_ : W ∉ componentsOf E.support), blowUpToBase ⊤ ⁻¹' W) = ∅ from
      Set.eq_empty_of_forall_notMem fun y hy => by
        simp only [Set.mem_iUnion] at hy
        obtain ⟨W, hW, -, hy⟩ := hy
        simpa [Scheme.IdealSheafData.support_top] using hW.1.2 hy]
    simp
  refine ⟨Fin.castSucc ∘ f, (Fin.castSucc_injective _).comp hf, fun i => ?_, fun j hj => ?_⟩
  · rw [hE i]
    exact (key (f i)).symm
  · induction j using Fin.lastCases with
    | last => exact klast
    | cast j =>
      have hj' : j ∉ Set.range f := fun ⟨i, hi⟩ => hj ⟨i, congrArg (Fin.castSucc (n := E.s)) hi⟩
      exact (key j).trans (hF j hj')

/-- Deleting the empty blow-ups after pulling back along an isomorphism: if `B` is of order
`≥ m` for `(s, a, E)`, then the reduced pull-back of `B` along an isomorphism `ψ : Y → X` is of
order `≥ m` for `(ψ ≫ s, ψ⁻¹a, E')`, for any `E'` obtained from `ψ⁻¹E` by deleting empty
entries. -/
private theorem isOrderGeMarkedTripleSeq_pullbackReduced {k : Type u} [Field k]
    {X : Scheme.{u}} (B : ClosedBlowupSequence X) :
    ∀ {Y : Scheme.{u}} (ψ : Y ⟶ X) [IsIso ψ] (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X)
      (E : OrderedDivisor X) (E' : OrderedDivisor Y), B.IsOrderGeMarkedTripleSeq s a E →
      IsDeletionOfEmpty E' (E.comap ψ) →
      (B.pullbackReduced ψ).IsOrderGeMarkedTripleSeq (ψ ≫ s) ⟨a.I.comap ψ, a.m⟩ E' := by
  induction B with
  | nil X =>
    intro Y ψ _ s a E E' hB hE
    have : QuasiCompact s := hB.2.2.2.1
    exact hE.isTriple (isTriple_comap_of_isOpenImmersion s hB ψ)
  | @cons X Z B ih =>
    intro Y ψ _ s a E E' hB hE
    obtain ⟨ht, -, hcod, hsnc, hord, hB⟩ := hB
    by_cases hZ : Z.comap ψ = ⊤
    · have hZ' : Z = ⊤ := by
        rw [← Kollar.comap_comap_inv ψ Z, hZ, Scheme.IdealSheafData.comap_top]
      subst hZ'
      simp only [ClosedBlowupSequence.pullbackReduced, hZ, dite_true]
      have := ClosedBlowupSequence.isIso_blowUpToBase_top X
      set ψ₁ := blowUpLift (⊤ : X.IdealSheafData) ψ
        (ClosedBlowupSequence.isCartierOver_of_comap_eq_top ψ ⊤ hZ)
      have hψ : ψ₁ ≫ blowUpToBase ⊤ = ψ := blowUpLift_comp _ _ _
      have : IsIso ψ₁ := by
        rw [show ψ₁ = ψ ≫ inv (blowUpToBase ⊤) by rw [← hψ]; simp]
        infer_instance
      have := ih ψ₁ (blowUpToBase ⊤ ≫ s) (a.birationalTransform ⊤) (E.totalTransform ⊤) E' hB
        (isDeletionOfEmpty_totalTransform_top ψ ψ₁ hψ E (fun j => (ht.2.2.2.2.2.2.1 j).1) E' hE)
      have hI : (a.birationalTransform ⊤).I.comap ψ₁ = a.I.comap ψ := by
        have h0 : (a.birationalTransform ⊤).I = a.I.comap (blowUpToBase ⊤) := by
          change idealColon _ (_ ^ a.m) = _
          rw [Scheme.IdealSheafData.comap_top,
            show (⊤ : (blowUp (⊤ : X.IdealSheafData)).IdealSheafData) ^ a.m = ⊤ by
              exact one_pow (M := (blowUp (⊤ : X.IdealSheafData)).IdealSheafData) a.m]
          simp only [idealColon, Scheme.IdealSheafData.ideal_top, Pi.top_apply,
            Submodule.top_coe, Submodule.colon_univ, Scheme.IdealSheafData.ofIdeals_ideal]
        rw [h0, ← Scheme.IdealSheafData.comap_comp, hψ]
      rw [← Category.assoc, hψ, hI] at this
      exact this
    · simp only [ClosedBlowupSequence.pullbackReduced, hZ, dite_false]
      have hsupp : ∀ S, S ⊆ Set.range ψ := fun S x _ =>
        ⟨inv ψ x, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
      have : QuasiCompact s := ht.2.2.2.1
      have htY := isTriple_comap_of_isOpenImmersion s ht ψ
      have hsncY : HasSNCWith (E.comap ψ).E (Z.comap ψ) := by
        refine hasSNCWith_of_comap (inv ψ) _ _ (range_inv ψ _) ?_
        rwa [comap_comap_inv_orderedDivisor, Kollar.comap_comap_inv]
      have hcodY : HasComponentsOfPositiveCodim ((Z.comap ψ).support : Set Y) := by
        refine hasComponentsOfPositiveCodim_of_comap (inv ψ) _ (range_inv ψ _) ?_
        rwa [Kollar.comap_comap_inv]
      have hordY : OrderAlongGE (a.I.comap ψ) ((Z.comap ψ).support : Set Y) a.m := by
        refine orderAlongGE_of_comap (inv ψ) _ (range_inv ψ _) _ _ ?_
        rwa [Kollar.comap_comap_inv, Kollar.comap_comap_inv]
      have hsm : MMP.Mori.IsSmoothScheme ((Z.comap ψ).subschemeι ≫ ψ ≫ s) :=
        isSmoothScheme_of_hasSNCWith ⟨⟨Y, a.I.comap ψ, E.comap ψ⟩, k, ψ ≫ s⟩ htY _ hsncY
      have hZsm : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ s) :=
        isSmoothScheme_of_hasSNCWith ⟨⟨X, a.I, E⟩, k, s⟩ ht _ hsnc
      refine ⟨hE.isTriple htY, hsm, hcodY, hE.hasSNCWith hsncY, hordY, ?_⟩
      have sq := Kollar.isPullback_canonicalLift_of_flat ψ Z
      have : IsIso (canonicalLift ψ Z) :=
        MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms _) sq
          (inferInstanceAs (IsIso ψ))
      have := ih (canonicalLift ψ Z) (blowUpToBase Z ≫ s) (a.birationalTransform Z)
        (E.totalTransform Z) (E'.totalTransform (Z.comap ψ)) hB
        (by rw [← totalTransform_comap ψ E Z (hsupp _)]; exact hE.totalTransform _)
      rw [birationalTransform_comap ψ s ht.2.1 Z hZsm hcod a hord htY.2.1 hsm hcodY hordY,
        ← Category.assoc, ← canonicalLift_comp_blowUpToBase, Category.assoc]
      exact this

/-- Deleting the empty blow-ups of a smooth blow-up sequence of order `≥ m` starting with a
marked triple gives one. -/
private theorem isOrderGeMarkedTripleSeq_reduction {k : Type u} [Field k] {X : Scheme.{u}}
    (B : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X)
    (E : OrderedDivisor X) (hB : B.IsOrderGeMarkedTripleSeq s a E) :
    B.reduction.IsOrderGeMarkedTripleSeq s a E := by
  have h := isOrderGeMarkedTripleSeq_pullbackReduced B (𝟙 X) s a E E hB (by
    simpa [OrderedDivisor.comap, Scheme.IdealSheafData.comap_id] using isDeletionOfEmpty_refl E)
  rw [Category.id_comp, Scheme.IdealSheafData.comap_id] at h
  exact h

/-- On `U = X ∖ cosupp N(I)` the restriction of `I` is monomial: `N(I|_U) = 𝒪_U`. -/
private theorem nonmonomialPart_comap_eq_top {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) {I : X.IdealSheafData} {E : OrderedDivisor X} (h : IsTriple s I E)
    (U : X.Opens) (hU : U = (nonmonomialPart I E).support.compl) :
    nonmonomialPart (I.comap U.ι) (E.comap U.ι) = ⊤ := by
  have hdecX := (isMonomialDecomposition_iff s h _ _).2 ⟨rfl, rfl⟩
  have htU := isTriple_comap_opens s h U
  have : LocallyOfFiniteType (U.ι ≫ s) := htU.2.2.1
  have : QuasiCompact (U.ι ≫ s) := htU.2.2.2.1
  have hM := monomialPart_comap s h (U.ι ≫ s) htU.2.1 U.ι (IsReducedFlatBaseChange.of_smooth U.ι)
  have hNtop : (nonmonomialPart I E).comap U.ι = ⊤ := by
    rw [← Scheme.IdealSheafData.support_eq_bot_iff, eq_bot_iff]
    intro u hu
    have hu' := (mem_support_comap_iff U.ι (nonmonomialPart I E) u).1 hu
    have hmem : U.ι u ∈ (U : Set X) := by
      rw [← Scheme.Opens.range_ι]; exact ⟨u, rfl⟩
    have hc : (U : Set X) = ((nonmonomialPart I E).support : Set X)ᶜ := by rw [hU]; rfl
    have h2 : U.ι u ∈ ((nonmonomialPart I E).support : Set X)ᶜ := hc ▸ hmem
    exact absurd hu' h2
  have hIU : I.comap U.ι = monomialPart (I.comap U.ι) (E.comap U.ι) := by
    rw [hM]
    conv_lhs => rw [hdecX.eq_mul]
    rw [Stacks.IdealSheaf.comap_mul, hNtop, Scheme.IdealSheafData.mul_top]
    rfl
  have hdecU := (isMonomialDecomposition_iff _ htU _ _).2 ⟨rfl, rfl⟩
  have hdec : IsMonomialDecomposition (I.comap U.ι) (E.comap U.ι)
      (monomialPartCoeff (I.comap U.ι) (E.comap U.ι)) ⊤ :=
    ⟨hdecU.finite_support, hdecU.isComponent_of_ne_zero,
      by rw [Scheme.IdealSheafData.mul_top]; exact hIU, fun D hDc hD => by
        obtain ⟨i, hi⟩ := hDc
        obtain ⟨x, hx⟩ := hi.1.1.nonempty
        simpa using hD hx⟩
  exact ((isMonomialDecomposition_iff _ htU _ _).1 hdec).2.symm

/-- Step 3 of `𝓑𝓜𝓞`: for a marked triple `(X_2, I_2, m, E_2)` with `cosupp(I_2, m)` disjoint
from `cosupp N(I_2)`, the extension by closure of the monomial order reduction of
`(U, E_2|_U, A(I_2)|_U)`, `U = X_2 ∖ cosupp N(I_2)`, is of order `≥ m`. -/
private theorem isOrderGeMarkedTripleSeq_stepThree {m : ℕ} (hm : 1 ≤ m) (t : MarkedTriple.{u})
    (ht : t ∈ markedTriples)
    (hdisj : Disjoint (⟨t.I, m⟩ : MarkedIdeal t.X).cosupport
      ((nonmonomialPart t.I t.E).support : Set t.X)) :
    let U : t.X.Opens := (nonmonomialPart t.I t.E).support.compl
    let C : MonomialData U :=
      ⟨t.k, U.ι ≫ t.sX, t.E.comap U.ι, monomialPartCoeff (t.I.comap U.ι) (t.E.comap U.ι)⟩
    ((C.monomialOrderReduction m).extendByClosure U.ι).IsOrderGeMarkedTripleSeq t.sX ⟨t.I, m⟩
      t.E := by
  intro U C
  have ht' : IsTriple t.sX t.I t.E := ht
  have htU := isTriple_comap_opens t.sX ht' U
  have hdec := (isMonomialDecomposition_iff _ htU _ _).2 ⟨rfl, rfl⟩
  have hI : C.monomialIdeal = t.I.comap U.ι := by
    rw [hdec.eq_mul, nonmonomialPart_comap_eq_top t.sX ht' U rfl,
      Scheme.IdealSheafData.mul_top]
    rfl
  have hC : C.IsMonomialData := ⟨htU.2.1, htU.2.2.1, htU.2.2.2.1, htU.2.2.2.2.2.2,
    hdec.finite_support, hdec.isComponent_of_ne_zero⟩
  have h3 := (C.isOrderGeMarkedTripleSeq_monomialOrderReduction hC htU.1 htU.2.2.2.2.1 hm).1
  rw [hI] at h3
  exact ClosedBlowupSequence.isOrderGeMarkedTripleSeq_extendByClosure t.sX t.I m t.E ht' hm
    hdisj U rfl _ h3

/-- The three steps of `𝓑𝓜𝓞` concatenated: if `S_1` is of order `≥ m` for `(X, I, m, E)`,
`S_2` is of order `≥ m` for its end `(X_1, I_1, m, E_1)`, and the end `(X_2, I_2, m, E_2)` of
`S_2` has `cosupp(I_2, m)` disjoint from `cosupp N(I_2)`, then `S_1`, `S_2` and the extended
monomial order reduction together are of order `≥ m`. -/
private theorem isOrderGeMarkedTripleSeq_steps {m : ℕ} (hm : 1 ≤ m) (t : MarkedTriple.{u})
    (S₁ : ClosedBlowupSequence t.X)
    (h1 : S₁.IsOrderGeMarkedTripleSeq t.sX ⟨t.I, m⟩ t.E)
    (S₂ : ClosedBlowupSequence (t.endOf m S₁).X)
    (h2 : S₂.IsOrderGeMarkedTripleSeq (t.endOf m S₁).sX ⟨(t.endOf m S₁).I, m⟩ (t.endOf m S₁).E)
    (hdisj : Disjoint (⟨((t.endOf m S₁).endOf m S₂).I, m⟩ :
          MarkedIdeal ((t.endOf m S₁).endOf m S₂).X).cosupport
        ((nonmonomialPart ((t.endOf m S₁).endOf m S₂).I
          ((t.endOf m S₁).endOf m S₂).E).support : Set _)) :
    let t₂ := (t.endOf m S₁).endOf m S₂
    let U : t₂.X.Opens := (nonmonomialPart t₂.I t₂.E).support.compl
    let C : MonomialData U :=
      ⟨t₂.k, U.ι ≫ t₂.sX, t₂.E.comap U.ι, monomialPartCoeff (t₂.I.comap U.ι) (t₂.E.comap U.ι)⟩
    (S₁.append (S₂.append ((C.monomialOrderReduction m).extendByClosure U.ι)))
      |>.IsOrderGeMarkedTripleSeq t.sX ⟨t.I, m⟩ t.E := by
  intro t₂ U C
  refine isOrderGeMarkedTripleSeq_append S₁ _ _ _ _ h1 ?_
  refine isOrderGeMarkedTripleSeq_append S₂ _ _ _ _ h2 ?_
  exact isOrderGeMarkedTripleSeq_stepThree hm t₂
    (ClosedBlowupSequence.isTriple_target_of_isOrderGeMarkedTripleSeq _ _ _ _ h2) hdisj

/-- **Kollár, Thm. 3.107 (opening clause).** Let `𝓑` be an order-reduction family on dimensions
`a, …, b` (`IsOrderReductionFamily`), `m ≥ 1`, and `(X, I, m, E)` a marked triple with `dim X = d`,
`a ≤ d ≤ b` (`markedTriplesOfDim`). Then `bmoFunctor B d m (X, I, m, E)` is a smooth blow-up
sequence of order `≥ m` starting with `(X, I, m, E)`
(`ClosedBlowupSequence.IsOrderGeMarkedTripleSeq`) without empty blow-ups
(`ClosedBlowupSequence.HasNoEmptyBlowups`). -/
@[mmp "lem_kr3e_bmo_is_sequence_of_order_ge_m"]
public theorem bmoFunctor_isOrderGeMarkedTripleSeq {a b d m : ℕ} (B : UnmarkedFamily.{u})
    (hB : IsOrderReductionFamily a b B) (hm : 1 ≤ m) (hd : d ∈ Set.Icc a b)
    (t : MarkedTriple.{u}) (ht : t ∈ markedTriplesOfDim {d} m) :
    (bmoFunctor B d m t).IsOrderGeMarkedTripleSeq t.sX t.markedIdeal t.E ∧
      (bmoFunctor B d m t).HasNoEmptyBlowups := by
  obtain ⟨htT, htm, n, hn, hdim⟩ := ht
  have hdt : dimNat t.X = d := by
    rw [Set.mem_singleton_iff] at hn
    simp [dimNat, hdim, hn]
  have hmk : t.markedIdeal = ⟨t.I, m⟩ := by rw [MarkedTriple.markedIdeal, htm]
  refine ⟨?_, ClosedBlowupSequence.hasNoEmptyBlowups_reduction _⟩
  rw [hmk]
  have h1 := (isOrderGeMarkedTripleSeq_bmoStepOne hB hm htT (hdt ▸ hd)).1
  rw [hdt] at h1
  have ht₁ : t.endOf m (bmoStepOne B d m t) ∈ markedTriples :=
    ClosedBlowupSequence.isTriple_target_of_isOrderGeMarkedTripleSeq _ _ _ _ h1
  have hd₁ : dimNat (t.endOf m (bmoStepOne B d m t)).X = d :=
    (dimNat_target_of_isOrderGeMarkedTripleSeq (bmoStepOne B d m t) _ _ _ h1).trans hdt
  obtain ⟨h2, hdisj⟩ := isOrderGeMarkedTripleSeq_bmoStepTwo hB hm ht₁ (by rw [hd₁]; exact hd)
  rw [hd₁] at h2 hdisj
  refine isOrderGeMarkedTripleSeq_reduction _ _ _ _
    (isOrderGeMarkedTripleSeq_steps hm t _ ?_ _ ?_ ?_)
  · rw [if_pos htT]; exact h1
  · rw [if_pos htT, if_pos ht₁]; exact h2
  · rw [if_pos htT, if_pos ht₁]; exact hdisj

/-! ### Blow-ups and their transforms commute with flat pull-back -/

namespace Kollar

section FlatPullback

open Stacks.Divisors

section Colon

variable {X Y : Scheme.{u}}

/-- For an effective Cartier divisor `B`, `idealColon A B` is the ideal-sheaf quotient. -/
private theorem idealColon_eq_colon (A B : X.IdealSheafData)
    (hB : IsEffectiveCartierDivisor B) :
    idealColon A B = A.colon B (fg_ideal_of_isEffectiveCartierDivisor B hB) :=
  Scheme.IdealSheafData.ofIdeals_ideal (A.colon B _)

/-- Dividing a product by an effective Cartier divisor: `(D · J : D) = J`. -/
private theorem idealColon_mul_cancel_left (D J : X.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) : idealColon (D * J) D = J := by
  rw [idealColon_eq_colon _ _ hD]
  choose U hU hxU b hb hgen using
    fun x : X => exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor D hD x
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun x : X => (⟨U x, hU x⟩ : X.affineOpens))
    (top_unique fun z _ => TopologicalSpace.Opens.mem_iSup.2 ⟨z, hxU z⟩) fun x => ?_
  rw [Scheme.IdealSheafData.ideal_colon, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, hgen x]
  ext d
  rw [Ideal.colon_span, Submodule.mem_colon_singleton, smul_eq_mul, Ideal.mem_span_singleton_mul]
  exact ⟨fun ⟨z, hz, hzd⟩ => ((hb x).left (show b x * d = b x * z by rw [hzd]; ring)) ▸ hz,
    fun hd => ⟨d, hd, mul_comm _ _⟩⟩

/-- The quotient by an effective Cartier divisor `D ⊇ A` commutes with inverse images along any
morphism pulling `D` back to an effective Cartier divisor. -/
private theorem idealColon_comap_of_le (f : Y ⟶ X) {A D : X.IdealSheafData}
    (hD : IsEffectiveCartierDivisor D) (hfD : IsEffectiveCartierDivisor (D.comap f))
    (hAD : A ≤ D) : idealColon (A.comap f) (D.comap f) = (idealColon A D).comap f := by
  conv_lhs => rw [← mul_colon_eq_of_isEffectiveCartierDivisor D A hD hAD,
    Stacks.IdealSheaf.comap_mul, idealColon_mul_cancel_left _ _ hfD]
  rw [idealColon_eq_colon _ _ hD]

/-- The quotient `(A : D)` only depends on `A ⊓ D`. -/
private theorem idealColon_inf_right (A D : X.IdealSheafData) :
    idealColon (A ⊓ D) D = idealColon A D := by
  unfold idealColon
  congr 1
  funext V
  ext x
  simp only [Submodule.mem_colon, Scheme.IdealSheafData.ideal_inf, Submodule.mem_inf]
  exact ⟨fun h p hp => (h p hp).1, fun h p hp => ⟨h p hp, Ideal.mul_mem_left _ _ hp⟩⟩

/-- **The quotient by an effective Cartier divisor commutes with flat inverse images.** -/
private theorem idealColon_comap_of_flat (f : Y ⟶ X) [Flat f] (A D : X.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) (hfD : IsEffectiveCartierDivisor (D.comap f)) :
    idealColon (A.comap f) (D.comap f) = (idealColon A D).comap f := by
  rw [← idealColon_inf_right A D, ← idealColon_inf_right (A.comap f),
    ← Stacks.FiniteTypeIdealSheaf.comap_inf_of_flat]
  exact idealColon_comap_of_le f hD hfD inf_le_right

/-- The marked transform commutes with flat base change. -/
private theorem birationalTransform_comap_of_flat (h : Y ⟶ X) [Flat h] (Z : X.IdealSheafData)
    (a : MarkedIdeal X) :
    (⟨a.I.comap h, a.m⟩ : MarkedIdeal Y).birationalTransform (Z.comap h) =
      ⟨(a.birationalTransform Z).I.comap (canonicalLift h Z), a.m⟩ := by
  have := flat_canonicalLift h Z
  have hEH : IsEffectiveCartierDivisor ((Z.comap (blowUpToBase Z) ^ a.m).comap
      (canonicalLift h Z)) := by
    rw [Stacks.IdealSheaf.comap_pow, comap_canonicalLift_comap_blowUpToBase]
    exact isEffectiveCartierDivisor_pow
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal (Z.comap h)) a.m
  have e := idealColon_comap_of_flat (canonicalLift h Z) (a.I.comap (blowUpToBase Z))
    _ (isEffectiveCartierDivisor_pow
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal Z) a.m) hEH
  rw [Stacks.IdealSheaf.comap_pow, comap_canonicalLift_comap_blowUpToBase,
    comap_canonicalLift_comap_blowUpToBase] at e
  exact congrArg (MarkedIdeal.mk · a.m) e

end Colon

/-! ### Irreducible components under flat base change -/

section Components

variable {X Y : Scheme.{u}}

/-- A point `η` whose closure is a component of `h⁻¹(\overline{ξ})` has no proper generalization
in `h⁻¹(\overline{ξ})`. -/
private theorem eq_of_specializes_of_mem_componentsOf {h : Y ⟶ X} (ξ : X) {η : Y}
    (hW : closure {η} ∈ componentsOf (h ⁻¹' closure {ξ})) :
    ∀ y', y' ⤳ η → h y' ∈ closure ({ξ} : Set X) → y' = η := by
  intro y' hy' hy'Z
  have hTcl : IsClosed (h ⁻¹' closure ({ξ} : Set X)) := isClosed_closure.preimage h.continuous
  have hcl : closure {y'} ⊆ h ⁻¹' closure ({ξ} : Set X) :=
    closure_minimal (Set.singleton_subset_iff.2 hy'Z) hTcl
  have hsub := hW.2 ⟨isIrreducible_singleton.closure, hcl⟩
    (closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 hy'))
      isClosed_closure)
  have : η ⤳ y' := specializes_iff_mem_closure.2 (hsub (subset_closure rfl))
  exact (hy'.antisymm this).eq

/-- **The closed fibre at a generic point of a fibre is zero-dimensional.** If `η` has no proper
generalization in its fibre `h⁻¹(h(η))`, the maximal ideal of the closed fibre
`𝒪_{Y,η} / 𝔪_{h(η)}𝒪_{Y,η}` has height zero: a prime of `𝒪_{Y,η}` containing `𝔪_{h(η)}` is a
point of `Spec 𝒪_{Y,η}` over `h(η)`, hence a generalization of `η` in its fibre. -/
private theorem height_maximalIdeal_closedFibre_eq_zero {h : Y ⟶ X} {η : Y}
    (hmax : ∀ y', y' ⤳ η → h y' = h η → y' = η) :
    ((IsLocalRing.maximalIdeal (Y.presheaf.stalk η)).map (Ideal.Quotient.mk
      ((IsLocalRing.maximalIdeal (X.presheaf.stalk (h η))).map (h.stalkMap η).hom))).height =
      0 := by
  set mA := IsLocalRing.maximalIdeal (X.presheaf.stalk (h η))
  set mB := IsLocalRing.maximalIdeal (Y.presheaf.stalk η)
  set J := mA.map (h.stalkMap η).hom
  have hcomap : mB.comap (h.stalkMap η).hom = mA := IsLocalRing.maximalIdeal_comap _
  have hP : (mB.map (Ideal.Quotient.mk J)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact Ideal.map_le_iff_le_comap.2 hcomap.ge)
  rw [Ideal.height_eq_zero_iff]
  refine ⟨⟨hP, bot_le⟩, fun q hq _ => ?_⟩
  have := hq.1
  set q' := q.comap (Ideal.Quotient.mk J) with hq'
  have hAq : mA = q'.comap (h.stalkMap η).hom :=
    (IsLocalRing.maximalIdeal.isMaximal _).eq_of_le (Ideal.comap_isPrime _ _).ne_top
      (Ideal.map_le_iff_le_comap.1 fun x hx => by
        rw [hq', Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx]; exact q.zero_mem)
  let pt : Spec (Y.presheaf.stalk η) := (⟨q', Ideal.comap_isPrime _ _⟩ : PrimeSpectrum _)
  have hy' : Y.fromSpecStalk η pt ⤳ η := by
    simpa [Scheme.range_fromSpecStalk] using Set.mem_range_self (f := Y.fromSpecStalk η) pt
  have himg : h (Y.fromSpecStalk η pt) = h η := by
    have e := congrArg (fun f => f pt) (Scheme.SpecMap_stalkMap_fromSpecStalk h (x := η))
    simp only [Scheme.Hom.comp_apply] at e
    rw [← e, show (Spec.map (h.stalkMap η)) pt = IsLocalRing.closedPoint _ from
      PrimeSpectrum.ext hAq.symm, Scheme.fromSpecStalk_closedPoint]
  have hpt := (IsPreimmersion.isEmbedding (Y.fromSpecStalk η)).injective
    ((hmax _ hy' himg).trans Scheme.fromSpecStalk_closedPoint.symm)
  rw [← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective q, ← hq',
    show q' = mB from congrArg PrimeSpectrum.asIdeal hpt]

/-- **Flat morphisms preserve coheight at generic points of fibres.** For `h` flat between locally
noetherian schemes and `η` with no proper generalization in its fibre,
`dim 𝒪_{Y,η} = dim 𝒪_{X,h(η)}`:
by going-down, `ht 𝔪_η = ht 𝔪_{h(η)} + ht(𝔪_η / 𝔪_{h(η)}𝒪_{Y,η})`, and the last term vanishes. -/
private theorem coheight_eq_of_forall_specializes_fibre [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] {h : Y ⟶ X} [Flat h] {η : Y}
    (hmax : ∀ y', y' ⤳ η → h y' = h η → y' = η) :
    Order.coheight η = Order.coheight (h η) := by
  letI : Algebra (X.presheaf.stalk (h η)) (Y.presheaf.stalk η) := (h.stalkMap η).hom.toAlgebra
  have : Module.Flat (X.presheaf.stalk (h η)) (Y.presheaf.stalk η) := Flat.stalkMap h η
  have : IsLocalHom (algebraMap (X.presheaf.stalk (h η)) (Y.presheaf.stalk η)) :=
    inferInstanceAs (IsLocalHom (h.stalkMap η).hom)
  have : Algebra.HasGoingDown (X.presheaf.stalk (h η)) (Y.presheaf.stalk η) :=
    Algebra.HasGoingDown.of_flat
  have : (IsLocalRing.maximalIdeal (Y.presheaf.stalk η)).LiesOver
      (IsLocalRing.maximalIdeal (X.presheaf.stalk (h η))) :=
    ⟨(IsLocalRing.maximalIdeal_comap _).symm⟩
  have hht := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (IsLocalRing.maximalIdeal (X.presheaf.stalk (h η)))
    (IsLocalRing.maximalIdeal (Y.presheaf.stalk η))
  have h0 : ((IsLocalRing.maximalIdeal (Y.presheaf.stalk η)).map (Ideal.Quotient.mk
      ((IsLocalRing.maximalIdeal (X.presheaf.stalk (h η))).map
        (algebraMap (X.presheaf.stalk (h η)) (Y.presheaf.stalk η))))).height = 0 :=
    height_maximalIdeal_closedFibre_eq_zero hmax
  rw [h0, add_zero] at hht
  have hd : ringKrullDim (Y.presheaf.stalk η) = ringKrullDim (X.presheaf.stalk (h η)) := by
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
      ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hht]
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight] at hd
  exact_mod_cast hd

/-- **Generic points of the components of a flat inverse image.** For `h` flat between locally
noetherian schemes, the generic point `η` of a component of `h⁻¹(\overline{ξ})` lies over `ξ`
(by going-down) and has the same coheight. -/
private theorem map_eq_and_coheight_eq [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    {h : Y ⟶ X} [Flat h] (ξ : X) {η : Y}
    (hW : closure {η} ∈ componentsOf (h ⁻¹' closure {ξ})) :
    h η = ξ ∧ Order.coheight η = Order.coheight ξ := by
  have hmax := eq_of_specializes_of_mem_componentsOf ξ hW
  obtain ⟨y, hyη, rfl⟩ :=
    Flat.generalizingMap h (specializes_iff_mem_closure.2 (hW.1.2 (subset_closure rfl)))
  obtain rfl : y = η := hmax y hyη (subset_closure rfl)
  exact ⟨rfl, coheight_eq_of_forall_specializes_fibre fun y' hy' e =>
    hmax y' hy' (e ▸ subset_closure rfl)⟩

/-- An irreducible subset of a closed subset of a scheme lies in one of its components. -/
private theorem exists_mem_componentsOf_subset {D C : Set Y} (hD : IsClosed D)
    (hC : IsIrreducible C) (hCD : C ⊆ D) : ∃ W ∈ componentsOf D, C ⊆ W := by
  obtain ⟨c, hc⟩ := QuasiSober.sober hC.closure isClosed_closure
  have hcD : c ∈ D := (closure_minimal hCD hD) hc.mem
  obtain ⟨W, hW, hcW⟩ := exists_mem_componentsOf hcD
  refine ⟨W, hW, subset_closure.trans ?_⟩
  rw [← hc.def]
  exact closure_minimal (Set.singleton_subset_iff.2 hcW) (Aux.isClosed_of_mem_componentsOf hD hW)

/-- **The components of a flat inverse image.** For `h` flat between locally noetherian schemes
and `Z` closed, the components of `h⁻¹Z` are the components of the `h⁻¹Z_j`,
`Z_j = \overline{ξ}` the components of `Z`. -/
private theorem mem_componentsOf_preimage_iff [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    {h : Y ⟶ X} [Flat h] {Z : Set X} (hZ : IsClosed Z) {W' : Set Y} :
    W' ∈ componentsOf (h ⁻¹' Z) ↔
      ∃ ξ : X, closure {ξ} ∈ componentsOf Z ∧ W' ∈ componentsOf (h ⁻¹' closure {ξ}) := by
  have hZ' : IsClosed (h ⁻¹' Z) := hZ.preimage h.continuous
  have fwd : ∀ {W'}, W' ∈ componentsOf (h ⁻¹' Z) →
      ∃ ξ : X, closure {ξ} ∈ componentsOf Z ∧ W' ∈ componentsOf (h ⁻¹' closure {ξ}) := by
    intro W' hW'
    obtain ⟨η, hηZ, rfl⟩ := Aux.exists_eq_closure_of_mem_componentsOf hZ' hW'
    obtain ⟨W, hW, hηW⟩ := exists_mem_componentsOf (show h η ∈ Z from hηZ)
    obtain ⟨ξ, -, rfl⟩ := Aux.exists_eq_closure_of_mem_componentsOf hZ hW
    refine ⟨ξ, hW, ⟨⟨isIrreducible_singleton.closure, closure_minimal
      (Set.singleton_subset_iff.2 hηW) (isClosed_closure.preimage h.continuous)⟩, ?_⟩⟩
    intro C hC hle
    exact hW'.2 ⟨hC.1, hC.2.trans (Set.preimage_mono hW.1.2)⟩ hle
  refine ⟨fwd, ?_⟩
  rintro ⟨ξ, hξ, hW'⟩
  refine ⟨⟨hW'.1.1, hW'.1.2.trans (Set.preimage_mono hξ.1.2)⟩, ?_⟩
  intro C hC hle
  obtain ⟨W'', hW'', hCW''⟩ := exists_mem_componentsOf_subset hZ' hC.1 hC.2
  obtain ⟨ξ₂, hξ₂, hW''₂⟩ := fwd hW''
  obtain ⟨η', -, rfl⟩ := Aux.exists_eq_closure_of_mem_componentsOf
    (isClosed_closure.preimage h.continuous) hW'
  obtain ⟨η'', -, rfl⟩ := Aux.exists_eq_closure_of_mem_componentsOf
    (isClosed_closure.preimage h.continuous) hW''₂
  have e1 := (map_eq_and_coheight_eq ξ hW').1
  have e2 := (map_eq_and_coheight_eq ξ₂ hW''₂).1
  have hsp : η'' ⤳ η' := specializes_iff_mem_closure.2 (hCW'' (hle (subset_closure rfl)))
  have hsp' : ξ₂ ⤳ ξ := by rw [← e1, ← e2]; exact hsp.map h.continuous
  have hle' : closure ({ξ} : Set X) ⊆ closure {ξ₂} :=
    closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 hsp'))
      isClosed_closure
  have hge : closure ({ξ₂} : Set X) ⊆ closure {ξ} := hξ.2 hξ₂.1 hle'
  have hW''sub : closure {η''} ⊆ h ⁻¹' closure ({ξ} : Set X) :=
    hW''₂.1.2.trans (Set.preimage_mono hge)
  exact hCW''.trans (hW'.2 ⟨hW''₂.1.1, hW''sub⟩ (hle.trans hCW''))

/-- The codimension of the closure of a point is its coheight. -/
private theorem codimension_irreducibleClosure_closure (ξ : X)
    (hW : IsIrreducible (closure ({ξ} : Set X))) :
    codimension (irreducibleClosure hW) = Order.coheight ξ := by
  rw [coheight_eq_codimension_closureSingleton]
  congr 1
  ext1
  change closure (closure {ξ}) = closure {ξ}
  exact closure_closure

/-- The union of the components of a closed subset of a noetherian space is the subset. -/
private theorem sUnion_componentsOf [NoetherianSpace Y] {D : Set Y} (hD : IsClosed D) :
    ⋃₀ componentsOf D = D :=
  le_antisymm (Set.sUnion_subset fun _ hW => hW.1.2) (Aux.finite_and_cover_componentsOf hD).2

/-- Components of codimension `≥ 2` pull back along a flat morphism. -/
private theorem componentsOfCodimAtLeastTwo_preimage [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] {h : Y ⟶ X} [Flat h] {Z : Set X} (hZ : IsClosed Z) :
    componentsOfCodimAtLeastTwo (h ⁻¹' Z) = h ⁻¹' componentsOfCodimAtLeastTwo Z := by
  ext y
  simp only [componentsOfCodimAtLeastTwo, Set.mem_iUnion, Set.mem_preimage]
  constructor
  · rintro ⟨W', hW', hcod, hyW'⟩
    obtain ⟨ξ, hξ, hW'ξ⟩ := (mem_componentsOf_preimage_iff hZ).1 hW'
    obtain ⟨η, -, rfl⟩ := Aux.exists_eq_closure_of_mem_componentsOf
      (isClosed_closure.preimage h.continuous) hW'ξ
    have hc := (map_eq_and_coheight_eq ξ hW'ξ).2
    refine ⟨closure {ξ}, hξ, ?_, hW'ξ.1.2 hyW'⟩
    rw [codimension_irreducibleClosure_closure] at hcod ⊢
    rwa [← hc]
  · rintro ⟨W, hW, hcod, hyW⟩
    obtain ⟨ξ, -, rfl⟩ := Aux.exists_eq_closure_of_mem_componentsOf hZ hW
    obtain ⟨W', hW', hyW'⟩ := exists_mem_componentsOf (show y ∈ h ⁻¹' closure {ξ} from hyW)
    have hW'Z := (mem_componentsOf_preimage_iff hZ).2 ⟨ξ, hW, hW'⟩
    obtain ⟨η, -, rfl⟩ := Aux.exists_eq_closure_of_mem_componentsOf
      (isClosed_closure.preimage h.continuous) hW'
    have hc := (map_eq_and_coheight_eq ξ hW').2
    refine ⟨closure {η}, hW'Z, ?_, hyW'⟩
    rw [codimension_irreducibleClosure_closure] at hcod ⊢
    rwa [hc]

/-- A component `W'` of `h⁻¹\overline{ξ}` is a component of `h⁻¹D` exactly when
`\overline{ξ}` is a component of `D`. -/
private theorem mem_componentsOf_preimage_iff_of_mem [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] {h : Y ⟶ X} [Flat h] {D : Set X}
    (hD : IsClosed D) (ξ : X) {W' : Set Y} (hW' : W' ∈ componentsOf (h ⁻¹' closure {ξ})) :
    W' ∈ componentsOf (h ⁻¹' D) ↔ closure {ξ} ∈ componentsOf D := by
  refine ⟨fun hD' => ?_, fun hξ => (mem_componentsOf_preimage_iff hD).2 ⟨ξ, hξ, hW'⟩⟩
  obtain ⟨ξ₂, hξ₂, hW'₂⟩ := (mem_componentsOf_preimage_iff hD).1 hD'
  obtain ⟨η, -, rfl⟩ := Aux.exists_eq_closure_of_mem_componentsOf
    (isClosed_closure.preimage h.continuous) hW'
  rw [← (map_eq_and_coheight_eq ξ hW').1, (map_eq_and_coheight_eq ξ₂ hW'₂).1]
  exact hξ₂

/-- The union of the components of `Z` that are not components of `D` pulls back. -/
private theorem iUnion_componentsOf_not_preimage [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] {h : Y ⟶ X} [Flat h]
    {Z D : Set X} (hZ : IsClosed Z) (hD : IsClosed D) :
    (⋃ (W : Set Y) (_ : W ∈ componentsOf (h ⁻¹' Z)) (_ : W ∉ componentsOf (h ⁻¹' D)), W) =
      h ⁻¹' ⋃ (W : Set X) (_ : W ∈ componentsOf Z) (_ : W ∉ componentsOf D), W := by
  ext y
  simp only [Set.mem_iUnion, Set.mem_preimage]
  constructor
  · rintro ⟨W', hW', hnD, hyW'⟩
    obtain ⟨ξ, hξ, hW'ξ⟩ := (mem_componentsOf_preimage_iff hZ).1 hW'
    exact ⟨closure {ξ}, hξ, fun h' => hnD ((mem_componentsOf_preimage_iff_of_mem hD ξ
      hW'ξ).2 h'), hW'ξ.1.2 hyW'⟩
  · rintro ⟨W, hW, hnD, hyW⟩
    obtain ⟨ξ, -, rfl⟩ := Aux.exists_eq_closure_of_mem_componentsOf hZ hW
    obtain ⟨W', hW', hyW'⟩ := exists_mem_componentsOf (show y ∈ h ⁻¹' closure {ξ} from hyW)
    exact ⟨W', (mem_componentsOf_preimage_iff hZ).2 ⟨ξ, hW, hW'⟩,
      fun h' => hnD ((mem_componentsOf_preimage_iff_of_mem hD ξ hW').1 h'), hyW'⟩

end Components

/-! ### Closures under generalizing maps -/

section Closure

/-- In a noetherian sober space every point of the closure of a locally closed set `U ∩ C` is a
specialization of a point of `U ∩ C`: the generic point of a component of the closure through
it lies in `U ∩ C`. -/
private theorem exists_specializes_of_mem_closure_inter {T : Type*} [TopologicalSpace T]
    [NoetherianSpace T] [QuasiSober T] {U C : Set T} (hU : IsOpen U) (hC : IsClosed C) {x : T}
    (hx : x ∈ closure (U ∩ C)) : ∃ s ∈ U ∩ C, s ⤳ x := by
  classical
  set K := closure (U ∩ C)
  obtain ⟨hfin, hcov⟩ := Aux.finite_and_cover_componentsOf (isClosed_closure : IsClosed K)
  obtain ⟨T₀, hT₀, hxT₀⟩ := hcov hx
  have hT₀cl : IsClosed T₀ := Aux.isClosed_of_mem_componentsOf isClosed_closure hT₀
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hT₀.1.1 hT₀cl
  have hξx : ξ ⤳ x := by rw [specializes_iff_mem_closure, hξ.def]; exact hxT₀
  refine ⟨ξ, ⟨?_, closure_minimal Set.inter_subset_right hC (hT₀.1.2 hξ.mem)⟩, hξx⟩
  by_contra hξU
  have hT₀U : T₀ ⊆ Uᶜ := by
    rw [← hξ.def]
    exact closure_minimal (Set.singleton_subset_iff.2 hξU) hU.isClosed_compl
  set O := componentsOf K \ {T₀}
  have hOfin : O.Finite := hfin.subset Set.diff_subset
  have hOcl : IsClosed (⋃₀ O) :=
    hOfin.isClosed_sUnion fun W hW => Aux.isClosed_of_mem_componentsOf isClosed_closure hW.1
  have hKO : K ⊆ ⋃₀ O := by
    refine closure_minimal (fun s hs => ?_) hOcl
    obtain ⟨T', hT', hsT'⟩ := hcov (subset_closure hs)
    refine ⟨T', ⟨hT', fun hT'eq => ?_⟩, hsT'⟩
    rw [Set.mem_singleton_iff] at hT'eq
    exact hT₀U (hT'eq ▸ hsT') hs.1
  obtain ⟨T', hT', hT₀T'⟩ := isIrreducible_iff_sUnion_isClosed.mp hT₀.1.1 hOfin.toFinset
    (fun W hW => Aux.isClosed_of_mem_componentsOf isClosed_closure
      (hOfin.mem_toFinset.mp hW).1)
    (by rw [hOfin.coe_toFinset]; exact hT₀.1.2.trans hKO)
  have hT'O := hOfin.mem_toFinset.mp hT'
  exact hT'O.2 (Set.mem_singleton_iff.2
    (Set.Subset.antisymm (hT₀.2 hT'O.1.1 hT₀T') hT₀T'))

/-- **Closures pull back along generalizing maps** to a noetherian sober space, for locally
closed sets. -/
private theorem preimage_closure_inter_of_generalizingMap {S T : Type*} [TopologicalSpace S]
    [TopologicalSpace T] [NoetherianSpace T] [QuasiSober T] {f : S → T} (hf : Continuous f)
    (hg : GeneralizingMap f) {U C : Set T} (hU : IsOpen U) (hC : IsClosed C) :
    f ⁻¹' closure (U ∩ C) = closure (f ⁻¹' (U ∩ C)) := by
  refine le_antisymm (fun y hy => ?_) (hf.closure_preimage_subset _)
  obtain ⟨s, hs, hsy⟩ := exists_specializes_of_mem_closure_inter hU hC hy
  obtain ⟨y', hy'y, hy's⟩ := hg hsy
  have hy' : y' ∈ f ⁻¹' (U ∩ C) := by rw [Set.mem_preimage, hy's]; exact hs
  exact closure_mono (Set.singleton_subset_iff.2 hy') (specializes_iff_mem_closure.1 hy'y)

end Closure

/-! ### The total transform under flat base change, one blow-up -/

section TotalTransform

variable {X Y : Scheme.{u}}

private theorem preimage_canonicalLift_preimage (h : Y ⟶ X) (Z : X.IdealSheafData)
    (S : Set X) :
    canonicalLift h Z ⁻¹' (blowUpToBase Z ⁻¹' S) = blowUpToBase (Z.comap h) ⁻¹' (h ⁻¹' S) := by
  rw [← Set.preimage_comp, ← Set.preimage_comp]
  congr 1
  funext y
  have := congrArg (fun f : blowUp (Z.comap h) ⟶ X => f y)
    (canonicalLift_comp_blowUpToBase h Z)
  simpa using this

/-- The closure of `π⁻¹(U ∩ C)`, `U` open and `C` closed, pulls back along the canonical lift of
a flat morphism to the closure of `π_Y⁻¹(h⁻¹(U ∩ C))`. -/
private theorem preimage_canonicalLift_closure [AlgebraicGeometry.IsNoetherian X] (h : Y ⟶ X)
    [Flat h] (Z : X.IdealSheafData) {U C : Set X} (hU : IsOpen U) (hC : IsClosed C) :
    canonicalLift h Z ⁻¹' closure (blowUpToBase Z ⁻¹' (U ∩ C)) =
      closure (blowUpToBase (Z.comap h) ⁻¹' (h ⁻¹' (U ∩ C))) := by
  have := isNoetherian_blowUp' Z
  have := flat_canonicalLift h Z
  rw [Set.preimage_inter, preimage_closure_inter_of_generalizingMap
      (canonicalLift h Z).continuous (Flat.generalizingMap _)
      (hU.preimage (blowUpToBase Z).continuous) (hC.preimage (blowUpToBase Z).continuous),
    ← Set.preimage_inter, preimage_canonicalLift_preimage]

/-- The support of an ordered divisor is closed. -/
private theorem isClosed_support {X : Scheme.{u}} (E : OrderedDivisor X) : IsClosed E.support :=
  isClosed_iUnion_of_finite fun i => (E.E i).support.isClosed

/-- The support of an inverse image is the inverse image of the support. -/
private theorem coe_support_comap {X Y : Scheme.{u}} (I : X.IdealSheafData) (f : Y ⟶ X) :
    ((I.comap f).support : Set Y) = f ⁻¹' (I.support : Set X) := by
  rw [Scheme.IdealSheafData.support_comap]; rfl

/-- **The total transform under flat base change, on reduced structures.** -/
private theorem reduced_totalTransform_comap [AlgebraicGeometry.IsNoetherian X]
    [AlgebraicGeometry.IsNoetherian Y] (h : Y ⟶ X) [Flat h] (E : OrderedDivisor X)
    (Z : X.IdealSheafData) :
    (⟨E.s + 1, fun i => Scheme.IdealSheafData.vanishingIdeal
        (((E.totalTransform Z).E i).comap (canonicalLift h Z)).support⟩ :
        OrderedDivisor (blowUp (Z.comap h))) =
      ⟨E.s + 1, fun i => Scheme.IdealSheafData.vanishingIdeal
        (((E.comap h).totalTransform (Z.comap h)).E i).support⟩ := by
  have hsupp : ((Z.comap h).support : Set Y) = h ⁻¹' (Z.support : Set X) :=
    coe_support_comap Z h
  congr 1
  funext i
  congr 1
  ext1
  rw [coe_support_comap]
  induction i using Fin.lastCases with
  | last =>
    change _ = ((((E.comap h).totalTransform (Z.comap h)).E (Fin.last (E.comap h).s)).support :
      Set (blowUp (Z.comap h)))
    rw [totalTransform_E_last, totalTransform_E_last,
      Scheme.IdealSheafData.coe_support_vanishingIdeal,
      Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure, Closeds.coe_closure]
    simp only [← Set.preimage_iUnion]
    rw [hsupp, Kollar.support_comap,
      iUnion_componentsOf_not_preimage Z.support.isClosed (isClosed_support E),
      ← Set.univ_inter (⋃ (W : Set X) (_ : W ∈ componentsOf (Z.support : Set X))
      (_ : W ∉ componentsOf E.support), W)]
    exact preimage_canonicalLift_closure h Z isOpen_univ
      (isClosed_biUnion_componentsOf Z.support.isClosed _)
  | cast i =>
    have hr := totalTransform_E_castSucc (E.comap h) (Z.comap h) i
    change _ = ((((E.comap h).totalTransform (Z.comap h)).E
      (Fin.castSucc (n := (E.comap h).s) i)).support : Set (blowUp (Z.comap h)))
    rw [totalTransform_E_castSucc, hr,
      Scheme.IdealSheafData.coe_support_vanishingIdeal,
      Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure, Closeds.coe_closure]
    change _ = closure (blowUpToBase (Z.comap h) ⁻¹' ((((E.E i).comap h).support : Set Y) \
      componentsOfCodimAtLeastTwo ((Z.comap h).support : Set Y)))
    rw [hsupp, componentsOfCodimAtLeastTwo_preimage Z.support.isClosed, coe_support_comap,
      ← Set.preimage_sdiff, Set.diff_eq, Set.inter_comm]
    exact preimage_canonicalLift_closure h Z
      (isClosed_componentsOfCodimAtLeastTwo Z.support.isClosed).isOpen_compl
      (E.E i).support.isClosed

/-- **The total transform under flat base change with reduced base changes.** -/
private theorem totalTransform_comap [AlgebraicGeometry.IsNoetherian X]
    [AlgebraicGeometry.IsNoetherian Y] {h : Y ⟶ X} (hh : IsReducedFlatBaseChange h)
    (E : OrderedDivisor X) (Z : X.IdealSheafData) :
    (E.totalTransform Z).comap (canonicalLift h Z) = (E.comap h).totalTransform (Z.comap h) := by
  have := hh.flat
  have hsupp : ((Z.comap h).support : Set Y) = h ⁻¹' (Z.support : Set X) :=
    coe_support_comap Z h
  refine Kollar.totalTransform_comap_canonicalLift hh E Z ?_ ?_
  · rw [hsupp]; exact componentsOfCodimAtLeastTwo_preimage Z.support.isClosed
  · rw [hsupp, Kollar.support_comap]
    exact iUnion_componentsOf_not_preimage Z.support.isClosed (isClosed_support E)

end TotalTransform

/-! ### Transforms along a pulled-back blow-up sequence -/

section Sequence

/-- The ordered divisor with the same supports as `E` and reduced entries. -/
private noncomputable def reducedDivisor {X : Scheme.{u}} (E : OrderedDivisor X) :
    OrderedDivisor X :=
  ⟨E.s, fun i => Scheme.IdealSheafData.vanishingIdeal (E.E i).support⟩

private theorem support_reducedDivisor {X : Scheme.{u}} (E : OrderedDivisor X) :
    (reducedDivisor E).support = E.support := by
  simp only [OrderedDivisor.support, reducedDivisor,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]

/-- The total transform only depends on the supports of the entries. -/
private theorem totalTransform_reducedDivisor {X : Scheme.{u}} (E : OrderedDivisor X)
    (Z : X.IdealSheafData) : (reducedDivisor E).totalTransform Z = E.totalTransform Z := by
  simp only [OrderedDivisor.totalTransform, support_reducedDivisor]
  simp only [reducedDivisor, Scheme.IdealSheafData.coe_support_vanishingIdeal]

private theorem totalTransform_congr {X : Scheme.{u}} {E E' : OrderedDivisor X}
    (hE : reducedDivisor E = reducedDivisor E') (Z : X.IdealSheafData) :
    E.totalTransform Z = E'.totalTransform Z := by
  rw [← totalTransform_reducedDivisor E, hE, totalTransform_reducedDivisor]

/-- **The marked transform along a pulled-back blow-up sequence.** -/
private theorem markedTransform_pullback : ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X)
    {Y : Scheme.{u}} (h : Y ⟶ X) [Flat h] (a : MarkedIdeal X),
    (B.pullback h).markedTransform ⟨a.I.comap h, a.m⟩ =
      ⟨(B.markedTransform a).I.comap (B.pullbackHom h), a.m⟩
  | _, .nil _, _, _, _, _ => rfl
  | _, .cons Z B, Y, h, _, a => by
    have := flat_canonicalLift h Z
    change (B.pullback (canonicalLift h Z)).markedTransform
        ((⟨a.I.comap h, a.m⟩ : MarkedIdeal Y).birationalTransform (Z.comap h)) =
      ⟨(B.markedTransform (a.birationalTransform Z)).I.comap
        (B.pullbackHom (canonicalLift h Z)), a.m⟩
    rw [birationalTransform_comap_of_flat]
    exact markedTransform_pullback B (canonicalLift h Z) (a.birationalTransform Z)

/-- **The total transform along a pulled-back blow-up sequence, on reduced structures.** -/
private theorem reduced_orderedTotalTransform_pullback : ∀ {X : Scheme.{u}}
    (B : ClosedBlowupSequence X) {Y : Scheme.{u}} (h : Y ⟶ X) [Flat h]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (E : OrderedDivisor X) (E' : OrderedDivisor Y),
    reducedDivisor E' = reducedDivisor (E.comap h) →
    reducedDivisor ((B.orderedTotalTransform E).comap (B.pullbackHom h)) =
      reducedDivisor ((B.pullback h).orderedTotalTransform E')
  | _, .nil _, _, _, _, _, _, _, _, hE => hE.symm
  | _, .cons Z B, Y, h, _, _, _, E, E', hE => by
    have := flat_canonicalLift h Z
    have := isNoetherian_blowUp' Z
    have := isNoetherian_blowUp' (Z.comap h)
    change reducedDivisor ((B.orderedTotalTransform (E.totalTransform Z)).comap
        (B.pullbackHom (canonicalLift h Z))) =
      reducedDivisor ((B.pullback (canonicalLift h Z)).orderedTotalTransform
        (E'.totalTransform (Z.comap h)))
    refine reduced_orderedTotalTransform_pullback B (canonicalLift h Z) _ _ ?_
    rw [totalTransform_congr hE]
    exact (reduced_totalTransform_comap h E Z).symm

/-- **The total transform along a pulled-back blow-up sequence**, for a flat morphism with
reduced base changes. -/
private theorem orderedTotalTransform_pullback : ∀ {X : Scheme.{u}}
    (B : ClosedBlowupSequence X) {Y : Scheme.{u}} {h : Y ⟶ X} (_ : IsReducedFlatBaseChange h)
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (E : OrderedDivisor X),
    (B.orderedTotalTransform E).comap (B.pullbackHom h) =
      (B.pullback h).orderedTotalTransform (E.comap h)
  | _, .nil _, _, _, _, _, _, _ => rfl
  | _, .cons Z B, Y, h, hh, _, _, E => by
    have := isNoetherian_blowUp' Z
    have := isNoetherian_blowUp' (Z.comap h)
    change (B.orderedTotalTransform (E.totalTransform Z)).comap
        (B.pullbackHom (canonicalLift h Z)) =
      (B.pullback (canonicalLift h Z)).orderedTotalTransform
        ((E.comap h).totalTransform (Z.comap h))
    rw [← totalTransform_comap hh E Z]
    exact orderedTotalTransform_pullback B (hh.canonicalLift Z) _

end Sequence

/-- **Blow-ups and their transforms commute with flat pull-back.** Let `h : Y → X` be a flat
morphism of Noetherian schemes, `Z ⊆ X` a closed subscheme and `h' : B_{h⁻¹Z}Y → B_ZX` the
canonical lift of `h`. Then

1. `h'⁻¹` of the exceptional divisor of `B_ZX` is the exceptional divisor of `B_{h⁻¹Z}Y`;
2. for a marked ideal `a = (I, m)` with `1 ≤ m` and `Z ⊆ cosupp(I, m)`, the birational transform
   of `(h^*I, m)` along `h⁻¹Z` is `(h'^*I', m)`, `(I', m)` the birational transform of `(I, m)`;
3. for an ordered divisor `E`, the entries of `h'⁻¹(π⁻¹_tot E)` and of `π_Y⁻¹_tot(h⁻¹E)` have the
   same reduced structure, and if `h` has reduced base changes the two ordered divisors are equal;
4. the irreducible components of `h⁻¹Z` are the irreducible components of the `h⁻¹Z_j`, `Z_j`
   the components of `Z`, and those of `h⁻¹Z_j` have the codimension of `Z_j`;
5. `h⁻¹` of an irreducible component of `Supp E` is a union of irreducible components of
   `Supp h⁻¹E`;
6. along a blow-up sequence `𝐁` with last morphism `h_r : (h^*𝐁).target → 𝐁.target`: if every
   centre `Z_i` lies in the cosupport of the `i`-th marked transform of `(I, m)`, the marked
   transform of `(h^*I, m)` along `h^*𝐁` is `h_r^*` of that of `(I, m)` along `𝐁`; and the total
   transforms of `E` and of `h⁻¹E` correspond under `h_r` as in 3. -/
@[mmp "lem_mmp_foundation_transforms_flat_pullback"]
public theorem transforms_comap_canonicalLift_of_flat {X Y : Scheme.{u}} [IsNoetherian X]
    [IsNoetherian Y] (h : Y ⟶ X) [Flat h] (Z : X.IdealSheafData) :
    -- 1. the exceptional divisor
    (AlgebraicGeometry.exceptionalIdeal Z).comap (canonicalLift h Z) =
        AlgebraicGeometry.exceptionalIdeal (Z.comap h) ∧
    -- 2. the marked transform
    (∀ a : MarkedIdeal X, 1 ≤ a.m → (Z.support : Set X) ⊆ a.cosupport →
        (⟨a.I.comap h, a.m⟩ : MarkedIdeal Y).birationalTransform (Z.comap h) =
          ⟨(a.birationalTransform Z).I.comap (canonicalLift h Z), a.m⟩) ∧
    -- 3. the total transform, entry by entry
    (∀ E : OrderedDivisor X,
        (⟨E.s + 1, fun i => Scheme.IdealSheafData.vanishingIdeal
            (((E.totalTransform Z).E i).comap (canonicalLift h Z)).support⟩ :
            OrderedDivisor (blowUp (Z.comap h))) =
          ⟨E.s + 1, fun i => Scheme.IdealSheafData.vanishingIdeal
            (((E.comap h).totalTransform (Z.comap h)).E i).support⟩ ∧
        (IsReducedFlatBaseChange h →
          (E.totalTransform Z).comap (canonicalLift h Z) =
            (E.comap h).totalTransform (Z.comap h))) ∧
    -- 4. components of the centre and their codimension
    componentsOf ((Z.comap h).support : Set Y) =
        ⋃ W ∈ componentsOf (Z.support : Set X), componentsOf (h ⁻¹' W) ∧
    (∀ W (hW : W ∈ componentsOf (Z.support : Set X)) W' (hW' : W' ∈ componentsOf (h ⁻¹' W)),
        codimension (irreducibleClosure hW'.1.1) = codimension (irreducibleClosure hW.1.1)) ∧
    -- 5. components of the support of a divisor
    (∀ E : OrderedDivisor X, ∀ D ∈ componentsOf E.support,
        ∃ S ⊆ componentsOf (E.comap h).support, h ⁻¹' D = ⋃₀ S) ∧
    -- 6. along a blow-up sequence, step by step
    (∀ (B : ClosedBlowupSequence X) (a : MarkedIdeal X), 1 ≤ a.m →
        ClosedBlowupSequence.rec (motive := fun X _ => MarkedIdeal X → Prop)
          (fun _ _ => True)
          (fun Z _ ih b => (Z.support : Set _) ⊆ b.cosupport ∧ ih (b.birationalTransform Z))
          B a →
        (B.pullback h).markedTransform ⟨a.I.comap h, a.m⟩ =
          ⟨(B.markedTransform a).I.comap (B.pullbackHom h), a.m⟩) ∧
    (∀ (B : ClosedBlowupSequence X) (E : OrderedDivisor X),
        (⟨((B.orderedTotalTransform E).comap (B.pullbackHom h)).s, fun i =>
            Scheme.IdealSheafData.vanishingIdeal
              (((B.orderedTotalTransform E).comap (B.pullbackHom h)).E i).support⟩ :
            OrderedDivisor (B.pullback h).target) =
          ⟨((B.pullback h).orderedTotalTransform (E.comap h)).s, fun i =>
            Scheme.IdealSheafData.vanishingIdeal
              (((B.pullback h).orderedTotalTransform (E.comap h)).E i).support⟩ ∧
        (IsReducedFlatBaseChange h →
          (B.orderedTotalTransform E).comap (B.pullbackHom h) =
            (B.pullback h).orderedTotalTransform (E.comap h))) := by
  refine ⟨comap_canonicalLift_comap_blowUpToBase h Z Z,
    fun a _ _ => birationalTransform_comap_of_flat h Z a,
    fun E => ⟨reduced_totalTransform_comap h E Z, fun hh => totalTransform_comap hh E Z⟩,
    ?_, ?_, ?_, fun B a _ _ => markedTransform_pullback B h a,
    fun B E => ⟨reduced_orderedTotalTransform_pullback B h E (E.comap h) rfl,
      fun hh => orderedTotalTransform_pullback B hh E⟩⟩
  · rw [coe_support_comap]
    ext W'
    simp only [Set.mem_iUnion]
    rw [mem_componentsOf_preimage_iff Z.support.isClosed]
    constructor
    · rintro ⟨ξ, hξ, hW'⟩
      exact ⟨_, hξ, hW'⟩
    · rintro ⟨W, hW, hW'⟩
      obtain ⟨ξ, -, rfl⟩ := Aux.exists_eq_closure_of_mem_componentsOf Z.support.isClosed hW
      exact ⟨ξ, hW, hW'⟩
  · intro W hW W' hW'
    obtain ⟨ξ, -, rfl⟩ := Aux.exists_eq_closure_of_mem_componentsOf Z.support.isClosed hW
    obtain ⟨η, -, rfl⟩ := Aux.exists_eq_closure_of_mem_componentsOf
      (isClosed_closure.preimage h.continuous) hW'
    rw [codimension_irreducibleClosure_closure, codimension_irreducibleClosure_closure]
    exact (map_eq_and_coheight_eq ξ hW').2
  · intro E D hD
    have hDcl : IsClosed D := Aux.isClosed_of_mem_componentsOf (isClosed_support E) hD
    refine ⟨componentsOf (h ⁻¹' D), fun W' hW' => ?_,
      (sUnion_componentsOf (hDcl.preimage h.continuous)).symm⟩
    rw [Kollar.support_comap]
    obtain ⟨ξ, -, rfl⟩ := Aux.exists_eq_closure_of_mem_componentsOf (isClosed_support E) hD
    exact (mem_componentsOf_preimage_iff_of_mem (isClosed_support E) ξ hW').2 hD

end FlatPullback

end Kollar

/-! ### The first inductive step of order reduction -/

section InductiveStepOne

open Topology

section Topology

variable {T : Type*} [TopologicalSpace T]

/-- In a `T₀` space of dimension `≤ 0` every specialization is trivial. -/
private theorem eq_of_specializes_of_topologicalKrullDim_le_zero [T0Space T]
    (h : topologicalKrullDim T ≤ 0) {a b : T} (hab : a ⤳ b) : a = b := by
  let S : IrreducibleCloseds T := ⟨closure {b}, isIrreducible_singleton.closure, isClosed_closure⟩
  let S' : IrreducibleCloseds T := ⟨closure {a}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hmax := (Order.krullDim_nonpos_iff_forall_isMax.1 h) S
  have hle : S ≤ S' := specializes_iff_closure_subset.1 hab
  exact (inseparable_iff_closure_eq.2
    (congrArg (fun U : IrreducibleCloseds T => (U : Set T)) (le_antisymm (hmax hle) hle))).eq

/-- A quasi-sober space in which every specialization is trivial has dimension `≤ 0`. -/
private theorem topologicalKrullDim_le_zero_of_forall_specializes [QuasiSober T]
    (h : ∀ ⦃a b : T⦄, a ⤳ b → a = b) : topologicalKrullDim T ≤ 0 := by
  refine Order.krullDim_nonpos_iff_forall_isMax.2 fun S S' hle => ?_
  have hS := S.isIrreducible.isGenericPoint_genericPoint S.isClosed
  have hS' := S'.isIrreducible.isGenericPoint_genericPoint S'.isClosed
  have hsp : S'.isIrreducible.genericPoint ⤳ S.isIrreducible.genericPoint :=
    hS'.specializes (hle hS.mem)
  have := h hsp
  change (S' : Set T) ≤ S
  rw [← hS'.def, ← hS.def, this]

/-- A space whose irreducible components all have dimension `≤ 0` has dimension `≤ 0`. -/
private theorem topologicalKrullDim_le_zero_of_forall_mem_irreducibleComponents [QuasiSober T]
    [T0Space T] (h : ∀ W ∈ irreducibleComponents T, topologicalKrullDim W ≤ 0) :
    topologicalKrullDim T ≤ 0 := by
  refine topologicalKrullDim_le_zero_of_forall_specializes fun a b hab => ?_
  obtain ⟨W, hW, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure {a}) isIrreducible_singleton.closure
  have ha : a ∈ W := hsub (subset_closure rfl)
  have hb : b ∈ W := hsub (specializes_iff_mem_closure.1 hab)
  have : (⟨a, ha⟩ : W) ⤳ ⟨b, hb⟩ := (IsInducing.subtypeVal.specializes_iff).1 hab
  exact congrArg Subtype.val (eq_of_specializes_of_topologicalKrullDim_le_zero (h W hW) this)

/-- A closed point without proper generalizations is an irreducible component. -/
private theorem singleton_mem_irreducibleComponents [QuasiSober T] {x : T} (hx : IsClosed {x})
    (h : ∀ y, y ⤳ x → y = x) : {x} ∈ irreducibleComponents T := by
  refine ⟨isIrreducible_singleton, fun S hS hxS => ?_⟩
  have hη := hS.closure.isGenericPoint_genericPoint isClosed_closure
  have hxη : hS.closure.genericPoint ⤳ x := hη.specializes (subset_closure (hxS rfl))
  have h' := h _ hxη
  intro z hz
  have : z ∈ closure ({x} : Set T) := by rw [← h', hη.def]; exact subset_closure hz
  rwa [hx.closure_eq] at this

/-- An equidimensional Jacobson quasi-sober `T₀` space has dimension `≤ 0` as soon as a nonempty
open subset lies in the image of a generalizing map from a space of dimension `≤ 0`. -/
private theorem topologicalKrullDim_le_zero_of_generalizingMap {S : Type*} [TopologicalSpace S]
    [T0Space S] [QuasiSober T] [T0Space T] [JacobsonSpace T] (heq : Equidimensional T)
    {f : S → T} (hf : GeneralizingMap f) (hS : topologicalKrullDim S ≤ 0) {U : Set T}
    (hU : IsOpen U) (hUne : U.Nonempty) (hUf : U ⊆ Set.range f) :
    topologicalKrullDim T ≤ 0 := by
  obtain ⟨x, hxU, hxc⟩ := nonempty_inter_closedPoints hUne hU.isLocallyClosed
  obtain ⟨y, rfl⟩ := hUf hxU
  have hgen : ∀ z, z ⤳ f y → z = f y := fun z hz => by
    obtain ⟨y', hy', rfl⟩ := hf hz
    rw [eq_of_specializes_of_topologicalKrullDim_le_zero hS hy']
  have hcomp := singleton_mem_irreducibleComponents hxc hgen
  exact topologicalKrullDim_le_zero_of_forall_mem_irreducibleComponents fun W hW =>
    (heq W hW _ hcomp).trans_le (topologicalKrullDim_zero_of_discreteTopology _)

end Topology

/-! ### Dimensions of triples -/

private theorem nonempty_of_topologicalKrullDim_eq {X : Type*} [TopologicalSpace X] {d : ℕ}
    (h : topologicalKrullDim X = ((d : ℕ∞) : WithBot ℕ∞)) : Nonempty X := by
  by_contra hX
  rw [not_nonempty_iff] at hX
  have : IsEmpty (IrreducibleCloseds X) := ⟨fun S => hX.elim S.isIrreducible.nonempty.some⟩
  rw [topologicalKrullDim, Order.krullDim_eq_bot] at h
  exact WithBot.bot_ne_coe h

private theorem dimNat_eq_of_hasDimensionIn {X : Scheme.{u}} {N : Set ℕ}
    (h : HasDimensionIn X N) :
    dimNat X ∈ N ∧ topologicalKrullDim X = ((dimNat X : ℕ∞) : WithBot ℕ∞) := by
  obtain ⟨d, hd, hX⟩ := h
  have : dimNat X = d := by simp [dimNat, hX]
  exact ⟨this ▸ hd, this ▸ hX⟩

private theorem idealTriplesOfDim_mono {N N' : Set ℕ} (hN : N' ⊆ N) (m : ℕ) :
    idealTriplesOfDim.{u} N' m ⊆ idealTriplesOfDim N m := fun _ ht =>
  ⟨ht.1, let ⟨d, hd, e⟩ := ht.2.1; ⟨d, hN hd, e⟩, ht.2.2⟩

private theorem markedTriplesOfDim_mono {N N' : Set ℕ} (hN : N' ⊆ N) (m : ℕ) :
    markedTriplesOfDim.{u} N' m ⊆ markedTriplesOfDim N m := fun _ ht =>
  ⟨ht.1, ht.2.1, let ⟨d, hd, e⟩ := ht.2.2; ⟨d, hN hd, e⟩⟩

private theorem mem_idealTriplesOfDim_singleton {N : Set ℕ} {m : ℕ} {t : FieldBlowupTriple.{u}}
    (ht : t ∈ idealTriplesOfDim N m) : t ∈ idealTriplesOfDim {dimNat t.X} m :=
  ⟨ht.1, ⟨_, rfl, (dimNat_eq_of_hasDimensionIn ht.2.1).2⟩, ht.2.2⟩

/-- A triple of dimension `0` has the unit ideal. -/
private theorem eq_top_of_dimNat_eq_zero {N : Set ℕ} {m : ℕ} {t : FieldBlowupTriple.{u}}
    (ht : t ∈ idealTriplesOfDim N m) (h0 : dimNat t.X = 0) : t.I = ⊤ := by
  obtain ⟨hc, hsm, hft, hqc, heq, hI, -⟩ := ht.1
  have := hc; have := hft; have := hqc
  have hX := (dimNat_eq_of_hasDimensionIn ht.2.1).2
  rw [h0] at hX
  exact (eq_top_and_maxOrder_eq_zero_of_topologicalKrullDim_eq_zero t.sX hsm heq hX t.I hI).1

private theorem maxOrder_top (X : Scheme.{u}) : maxOrder (⊤ : X.IdealSheafData) = 0 :=
  le_antisymm (iSup₂_le fun x _ => by
    rw [multAt, Aux.stalk_top, MMP.Threefold.Resolution.idealOrder_top]) bot_le

/-- **Dimension cannot drop to `0`.** If a triple has positive dimension, a scheme `Y` with a
generalizing map to it whose image contains a nonempty open subset has positive dimension too:
otherwise the image of a closed point of that open would be an irreducible component of
dimension `0` of the equidimensional scheme. -/
private theorem dimNat_ne_zero_of_generalizingMap {N N' : Set ℕ} {m : ℕ}
    {t : FieldBlowupTriple.{u}} (ht : t ∈ idealTriplesOfDim N m) (hX : dimNat t.X ≠ 0)
    {Y : Scheme.{u}} (f : Y ⟶ t.X) (hf : GeneralizingMap f) (hY : HasDimensionIn Y N')
    {U : Set t.X} (hU : IsOpen U) (hUne : U.Nonempty) (hUf : U ⊆ Set.range f) :
    dimNat Y ≠ 0 := by
  intro hY0
  obtain ⟨-, -, hft, -, heq, -, -⟩ := ht.1
  have := hft
  have : JacobsonSpace t.X := LocallyOfFiniteType.jacobsonSpace t.sX
  have hYd := (dimNat_eq_of_hasDimensionIn hY).2
  rw [hY0] at hYd
  have h := topologicalKrullDim_le_zero_of_generalizingMap heq hf hYd.le hU hUne hUf
  rw [(dimNat_eq_of_hasDimensionIn ht.2.1).2] at h
  exact hX (Nat.le_zero.1 (by exact_mod_cast h))

/-- The source of a smooth morphism to a triple of positive dimension has positive dimension. -/
private theorem dimNat_ne_zero_of_smooth {N N' : Set ℕ} {m : ℕ} {t : FieldBlowupTriple.{u}}
    (ht : t ∈ idealTriplesOfDim N m) (hX : dimNat t.X ≠ 0) {Y : Scheme.{u}} (h : Y ⟶ t.X)
    (hsm : Smooth h) (hY : HasDimensionIn Y N') : dimNat Y ≠ 0 := by
  obtain ⟨y⟩ := nonempty_of_topologicalKrullDim_eq (dimNat_eq_of_hasDimensionIn hY).2
  have := hsm
  exact dimNat_ne_zero_of_generalizingMap ht hX h (Flat.generalizingMap h) hY
    h.isOpenMap.isOpen_range ⟨_, y, rfl⟩ le_rfl

/-- A change of fields of a triple of positive dimension has positive dimension. -/
private theorem dimNat_fieldChange_ne_zero {N N' : Set ℕ} {m : ℕ} {t : FieldBlowupTriple.{u}}
    (ht : t ∈ idealTriplesOfDim N m) (hX : dimNat t.X ≠ 0) {L : Type u} [Field L]
    (σ : t.k →+* L) (hL : HasDimensionIn (t.fieldChange σ).X N') :
    dimNat (t.fieldChange σ).X ≠ 0 := by
  have : Flat (Spec.map (CommRingCat.ofHom σ)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    algebraize [σ]; exact Module.Flat.of_free
  have hsurj : Surjective (t.fieldChangeProj σ) := inferInstance
  obtain ⟨x⟩ := nonempty_of_topologicalKrullDim_eq (dimNat_eq_of_hasDimensionIn ht.2.1).2
  exact dimNat_ne_zero_of_generalizingMap ht hX _ (Flat.generalizingMap (t.fieldChangeProj σ))
    hL isOpen_univ ⟨x, trivial⟩ fun x _ => hsurj.surj x

/-! ### Sequences of order `m` -/

/-- A smooth blow-up sequence of order `m` without empty blow-ups, starting with an ideal of
maximal order `< m`, is empty. -/
private theorem eq_nil_of_maxOrder_lt {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {I : X.IdealSheafData} {E : OrderedDivisor X} {m : ℕ}
    {B : ClosedBlowupSequence X} (hB : B.IsOrderMTripleSeq s I E m) (hB' : B.HasNoEmptyBlowups)
    (hI : maxOrder I < m) : B = .nil X := by
  cases B with
  | nil => rfl
  | cons Z B =>
    exfalso
    obtain ⟨-, -, -, -, hord, -⟩ := hB
    obtain ⟨hZ, -⟩ := hB'
    obtain ⟨x, hx⟩ : (Z.support : Set X).Nonempty := Set.nonempty_iff_ne_empty.2 fun h =>
      hZ ((Scheme.IdealSheafData.support_eq_bot_iff _).1 (TopologicalSpace.Closeds.ext h))
    obtain ⟨W, hW, -⟩ := exists_mem_componentsOf hx
    have h2 : orderAlong I hW.1.1 ≤ maxOrder I :=
      le_iSup₂ (f := fun z (_ : z ∈ Set.univ) => multAt I z) _ (Set.mem_univ _)
    rw [hord W hW] at h2
    exact (h2.trans_lt hI).false

/-! ### Restriction of order-reduction functors -/

/-- The restriction of a smooth blow-up sequence functor of order `m` to a smaller class. -/
private def restrictIdeals {m : ℕ} {𝒞 𝒞' : Set FieldBlowupTriple.{u}}
    (h : 𝒞' ⊆ 𝒞) (F : OrderBlowupSequenceFunctor m 𝒞) : OrderBlowupSequenceFunctor m 𝒞' :=
  ⟨fun t ht => F.toFun t (h ht), fun t ht => F.isOrderMTripleSeq t (h ht),
    fun t ht => F.hasNoEmptyBlowups t (h ht)⟩

/-- The restriction of a smooth blow-up sequence functor of order `≥ m` to a smaller class. -/
private def restrictMarked {𝒞 𝒞' : Set MarkedTriple.{u}}
    (h : 𝒞' ⊆ 𝒞) (F : OrderGeBlowupSequenceFunctor 𝒞) : OrderGeBlowupSequenceFunctor 𝒞' :=
  ⟨fun t ht => F.toFun t (h ht), fun t ht => F.isOrderGeMarkedTripleSeq t (h ht),
    fun t ht => F.hasNoEmptyBlowups t (h ht)⟩

private theorem isOrderReductionFunctorIdeals_restrict {m : ℕ} {N N' : Set ℕ} (hN : N' ⊆ N)
    {F : OrderBlowupSequenceFunctor.{u} m (idealTriplesOfDim N m)}
    (hF : IsOrderReductionFunctorIdeals m N F) :
    IsOrderReductionFunctorIdeals m N' (restrictIdeals (idealTriplesOfDim_mono hN m) F) :=
  ⟨fun t _ => hF.1 t _, ⟨fun t _ Y h h1 h2 h3 h4 _ => hF.2.1.1 t _ Y h h1 h2 h3 h4 _,
    fun t _ Y h h1 h2 h3 _ => hF.2.1.2 t _ Y h h1 h2 h3 _⟩, fun t _ L _ σ _ => hF.2.2 t _ L σ _⟩

private theorem isOrderReductionFunctorMarked_restrict {m : ℕ} {N N' : Set ℕ} (hN : N' ⊆ N)
    {F : OrderGeBlowupSequenceFunctor.{u} (markedTriplesOfDim N m)}
    (hF : IsOrderReductionFunctorMarked m N F) :
    IsOrderReductionFunctorMarked m N' (restrictMarked (markedTriplesOfDim_mono hN m) F) :=
  ⟨fun t _ => hF.1 t _, ⟨fun t _ Y h h1 h2 h3 h4 _ => hF.2.1.1 t _ Y h h1 h2 h3 h4 _,
    fun t _ Y h h1 h2 h3 _ => hF.2.1.2 t _ Y h h1 h2 h3 _⟩, fun t _ L _ σ _ => hF.2.2 t _ L σ _⟩

/-- A marked order-reduction family on dimensions `a, …, b` is one on `a, …, b'` for `b' ≤ b`. -/
private theorem isMarkedOrderReductionFamily_mono {a b b' : ℕ} (hb : b' ≤ b)
    {M : MarkedFamily.{u}} (hM : IsMarkedOrderReductionFamily a b M) :
    IsMarkedOrderReductionFamily a b' M := fun μ hμ => by
  obtain ⟨F, hF1, hF2⟩ := hM μ hμ
  have hN : Set.Icc a b' ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl hb
  exact ⟨restrictMarked (markedTriplesOfDim_mono hN μ) F, fun t ht => hF1 t _,
    isOrderReductionFunctorMarked_restrict hN hF2⟩

/-! ### The first conjunct -/

private theorem mem_idealTriplesOfDim_Icc_one {n μ : ℕ} {t : FieldBlowupTriple.{u}}
    (ht : t ∈ idealTriplesOfDim (Set.Icc 0 n) μ) (h0 : dimNat t.X ≠ 0) :
    t ∈ idealTriplesOfDim (Set.Icc 1 n) μ :=
  ⟨ht.1, ⟨_, ⟨Nat.one_le_iff_ne_zero.2 h0, (dimNat_eq_of_hasDimensionIn ht.2.1).1.2⟩,
    (dimNat_eq_of_hasDimensionIn ht.2.1).2⟩, ht.2.2⟩

/-- On a triple of positive dimension `d ≤ n`, `𝓑𝓞_{d,μ}` is a smooth blow-up sequence of order
`μ` without empty blow-ups which ends with maximal order `< μ`. -/
private theorem boFunctor_spec {n μ : ℕ} {M : MarkedFamily.{u}}
    (hM : IsMarkedOrderReductionFamily 0 (n - 1) M) (hμ : 1 ≤ μ) {t : FieldBlowupTriple.{u}}
    (ht : t ∈ idealTriplesOfDim (Set.Icc 0 n) μ) (h0 : dimNat t.X ≠ 0) :
    ((boFunctor M (dimNat t.X) μ t).IsOrderMTripleSeq t.sX t.I t.E μ ∧
      (boFunctor M (dimNat t.X) μ t).HasNoEmptyBlowups) ∧
    maxOrder (t.endOf (boFunctor M (dimNat t.X) μ t)).I < μ := by
  have h1 := Nat.one_le_iff_ne_zero.2 h0
  have hM' : IsMarkedOrderReductionFamily 0 (dimNat t.X - 1) M :=
    isMarkedOrderReductionFamily_mono
      (Nat.sub_le_sub_right (dimNat_eq_of_hasDimensionIn ht.2.1).1.2 1) hM
  have ht' := mem_idealTriplesOfDim_singleton ht
  exact ⟨boFunctor_isOrderMTripleSeq M h1 hM' hμ t ht',
    maxOrder_endOf_boFunctor_lt M h1 hM' hμ t ht'⟩

/-- The functor of the first conjunct: empty in dimension `0`, `𝓑𝓞_{d,μ}` in dimension `d ≥ 1`. -/
private noncomputable def stepFunctor {n μ : ℕ} {M : MarkedFamily.{u}}
    (hM : IsMarkedOrderReductionFamily 0 (n - 1) M) (hμ : 1 ≤ μ) :
    OrderBlowupSequenceFunctor.{u} μ (idealTriplesOfDim (Set.Icc 0 n) μ) where
  toFun t _ := if dimNat t.X = 0 then .nil t.X else boFunctor M (dimNat t.X) μ t
  isOrderMTripleSeq t ht := by
    split_ifs with h0
    exacts [ht.1, (boFunctor_spec hM hμ ht h0).1.1]
  hasNoEmptyBlowups t ht := by
    split_ifs with h0
    exacts [trivial, (boFunctor_spec hM hμ ht h0).1.2]

private theorem stepFunctor_apply_of_ne_zero {n μ : ℕ} {M : MarkedFamily.{u}}
    (hM : IsMarkedOrderReductionFamily 0 (n - 1) M) (hμ : 1 ≤ μ) {t : FieldBlowupTriple.{u}}
    (ht : t ∈ idealTriplesOfDim (Set.Icc 0 n) μ) (h0 : dimNat t.X ≠ 0) :
    (stepFunctor hM hμ).toFun t ht = boFunctor M (dimNat t.X) μ t := if_neg h0

/-- The step functor is empty on a triple with the unit ideal. -/
private theorem stepFunctor_eq_nil {n μ : ℕ} {M : MarkedFamily.{u}}
    (hM : IsMarkedOrderReductionFamily 0 (n - 1) M) (hμ : 1 ≤ μ) {t : FieldBlowupTriple.{u}}
    (ht : t ∈ idealTriplesOfDim (Set.Icc 0 n) μ) (hI : t.I = ⊤) :
    (stepFunctor hM hμ).toFun t ht = .nil t.X := by
  by_cases h0 : dimNat t.X = 0
  · exact if_pos h0
  · rw [stepFunctor_apply_of_ne_zero hM hμ ht h0]
    obtain ⟨⟨hB, hB'⟩, -⟩ := boFunctor_spec hM hμ ht h0
    exact eq_nil_of_maxOrder_lt hB hB' (by rw [hI, maxOrder_top]; exact_mod_cast hμ)

/-- Over a triple of dimension `0`, the step functor is empty both on the triple and on any
member of the class whose ideal is pulled back from it. -/
private theorem stepFunctor_eq_nil_of_dimNat_eq_zero {n μ : ℕ} {M : MarkedFamily.{u}}
    (hM : IsMarkedOrderReductionFamily 0 (n - 1) M) (hμ : 1 ≤ μ) {t t' : FieldBlowupTriple.{u}}
    (ht : t ∈ idealTriplesOfDim (Set.Icc 0 n) μ) (h0 : dimNat t.X = 0)
    (ht' : t' ∈ idealTriplesOfDim (Set.Icc 0 n) μ) (f : t'.X ⟶ t.X) (hI : t'.I = t.I.comap f) :
    (stepFunctor hM hμ).toFun t' ht' = .nil t'.X ∧ (stepFunctor hM hμ).toFun t ht = .nil t.X := by
  have htop := eq_top_of_dimNat_eq_zero ht h0
  exact ⟨stepFunctor_eq_nil hM hμ ht' (by rw [hI, htop, Scheme.IdealSheafData.comap_top]),
    stepFunctor_eq_nil hM hμ ht htop⟩

/-- The first conjunct: if `𝓜` is a marked order-reduction family on dimensions `0, …, n - 1`
ignoring empty entries, the family empty in dimension `0` and `𝓑𝓞` in dimensions `1, …, n` is an
order-reduction family on dimensions `0, …, n`. -/
private theorem isOrderReductionFamily {n : ℕ} (hn : 1 ≤ n) (M : MarkedFamily.{u})
    (hM : IsMarkedOrderReductionFamily 0 (n - 1) M)
    (hMe : ∀ d ∈ Set.Icc 0 (n - 1), ∀ μ : ℕ, 1 ≤ μ →
      IgnoresEmptyEntriesMarked (markedTriplesOfDim {d} μ) (fun t _ => M d μ t)) :
    IsOrderReductionFamily 0 n (fun d μ t => if d = 0 then .nil t.X else boFunctor M d μ t) := by
  intro μ hμ
  have hS := commutesWithSmoothOn_boFunctor M hn hM hMe hμ
  refine ⟨stepFunctor hM hμ, fun t ht => rfl, fun t ht => ?_, ⟨fun t ht Y h hsm hsurj hlft hqc hY
    => ?_, fun t ht Y h hsm hlft hqc hY => ?_⟩, fun t ht L _ σ hL => ?_⟩
  · by_cases h0 : dimNat t.X = 0
    · rw [stepFunctor_eq_nil hM hμ ht (eq_top_of_dimNat_eq_zero ht h0)]
      change maxOrder t.I < μ
      rw [eq_top_of_dimNat_eq_zero ht h0, maxOrder_top]
      exact_mod_cast hμ
    · rw [stepFunctor_apply_of_ne_zero hM hμ ht h0]
      exact (boFunctor_spec hM hμ ht h0).2
  · by_cases hX0 : dimNat t.X = 0
    · obtain ⟨h1, h2⟩ := stepFunctor_eq_nil_of_dimNat_eq_zero hM hμ ht hX0 hY h rfl
      rw [h1, h2]; rfl
    · have hY0 := dimNat_ne_zero_of_smooth ht hX0 h hsm hY.2.1
      rw [stepFunctor_apply_of_ne_zero hM hμ hY hY0, stepFunctor_apply_of_ne_zero hM hμ ht hX0]
      exact hS.1 t (mem_idealTriplesOfDim_Icc_one ht hX0) Y h hsm hsurj hlft hqc
        (mem_idealTriplesOfDim_Icc_one hY hY0)
  · by_cases hX0 : dimNat t.X = 0
    · obtain ⟨h1, h2⟩ := stepFunctor_eq_nil_of_dimNat_eq_zero hM hμ ht hX0 hY h rfl
      rw [h1, h2]; rfl
    · have hY0 := dimNat_ne_zero_of_smooth ht hX0 h hsm hY.2.1
      rw [stepFunctor_apply_of_ne_zero hM hμ hY hY0, stepFunctor_apply_of_ne_zero hM hμ ht hX0]
      exact hS.2 t (mem_idealTriplesOfDim_Icc_one ht hX0) Y h hsm hlft hqc
        (mem_idealTriplesOfDim_Icc_one hY hY0)
  · by_cases hX0 : dimNat t.X = 0
    · obtain ⟨h1, h2⟩ := stepFunctor_eq_nil_of_dimNat_eq_zero hM hμ ht hX0 hL _ rfl
      rw [h1, h2]; rfl
    · have hL0 := dimNat_fieldChange_ne_zero ht hX0 σ hL.2.1
      rw [stepFunctor_apply_of_ne_zero hM hμ hL hL0, stepFunctor_apply_of_ne_zero hM hμ ht hX0]
      exact commutesWithFieldChangeOn_boFunctor M hn hM hμ t
        (mem_idealTriplesOfDim_Icc_one ht hX0) L σ (mem_idealTriplesOfDim_Icc_one hL hL0)

/-! ### The theorem -/

/-- **Kollár 3.70.1.** Let `n ≥ 1`. If `M` is a marked order-reduction family on dimensions
`0, …, n - 1` (`IsMarkedOrderReductionFamily`), the unmarked family which is empty in dimension
`0` and `boFunctor M d μ` in dimension `d ≥ 1` is an order-reduction family on dimensions
`0, …, n` (`IsOrderReductionFamily`), provided `M` ignores empty entries
(`IgnoresEmptyEntriesMarked`, Kollár 3.72). In particular, if (3.69) holds in dimensions
`≤ n - 1` by functors ignoring empty entries, then `OrderReductionIdealsHoldsUpTo n`, and for every
`m ≥ 1` there is an order reduction functor
for ideals of order `m` on dimensions `{n}`. -/
@[mmp "thm_kr3e_main_inductive_step_one"]
public theorem isOrderReductionFamily_boFunctor {n : ℕ} (hn : 1 ≤ n) :
    (∀ M : MarkedFamily.{u}, IsMarkedOrderReductionFamily 0 (n - 1) M →
      (∀ d ∈ Set.Icc 0 (n - 1), ∀ μ : ℕ, 1 ≤ μ →
        IgnoresEmptyEntriesMarked (markedTriplesOfDim {d} μ) (fun t _ => M d μ t)) →
      IsOrderReductionFamily 0 n
        (fun d μ t => if d = 0 then .nil t.X else boFunctor M d μ t)) ∧
    ((∀ m : ℕ, 1 ≤ m →
        ∃ B : OrderGeBlowupSequenceFunctor.{u} (markedTriplesOfDim {e | e ≤ n - 1} m),
          IsOrderReductionFunctorMarked m _ B ∧ IgnoresEmptyEntriesMarked _ B.toFun) →
      OrderReductionIdealsHoldsUpTo.{u} n ∧
        ∀ m : ℕ, 1 ≤ m → ∃ B : OrderBlowupSequenceFunctor.{u} m (idealTriplesOfDim {n} m),
          IsOrderReductionFunctorIdeals m _ B) := by
  refine ⟨fun M hM hMe => isOrderReductionFamily hn M hM hMe, fun hMk => ?_⟩
  classical
  let M : MarkedFamily.{u} := fun _ μ t =>
    if h : 1 ≤ μ ∧ t ∈ markedTriplesOfDim {e | e ≤ n - 1} μ then
      (hMk μ h.1).choose.toFun t h.2 else .nil t.X
  have hN : Set.Icc 0 (n - 1) ⊆ {e | e ≤ n - 1} := fun e he => he.2
  have hMfam : IsMarkedOrderReductionFamily 0 (n - 1) M := by
    intro μ hμ
    refine ⟨restrictMarked (markedTriplesOfDim_mono hN μ) (hMk μ hμ).choose, fun t ht => ?_,
      isOrderReductionFunctorMarked_restrict hN (hMk μ hμ).choose_spec.1⟩
    change _ = dite _ _ _
    rw [dif_pos ⟨hμ, markedTriplesOfDim_mono hN μ ht⟩]
    rfl
  have hMe : ∀ d ∈ Set.Icc 0 (n - 1), ∀ μ : ℕ, 1 ≤ μ →
      IgnoresEmptyEntriesMarked (markedTriplesOfDim {d} μ) (fun t _ => M d μ t) := by
    intro d hd μ hμ t ht
    have hd' : ({d} : Set ℕ) ⊆ {e | e ≤ n - 1} := by rintro e rfl; exact hd.2
    have ht' := markedTriplesOfDim_mono hd' μ ht
    obtain ⟨hdel, hB⟩ := (hMk μ hμ).choose_spec.2 t ht'
    refine ⟨⟨hdel.1, hdel.2.1, ht.2.2⟩, ?_⟩
    exact ((dif_pos (And.intro hμ hdel)).trans hB).trans (dif_pos (And.intro hμ ht')).symm
  have hB := isOrderReductionFamily hn M hMfam hMe
  refine ⟨fun m hm => ?_, fun m hm => ?_⟩
  · obtain ⟨F, -, hF⟩ := hB m hm
    have hN : {d | d ≤ n} ⊆ Set.Icc 0 n := fun d hd => ⟨Nat.zero_le _, hd⟩
    exact ⟨_, isOrderReductionFunctorIdeals_restrict hN hF⟩
  · obtain ⟨F, -, hF⟩ := hB m hm
    have hN : ({n} : Set ℕ) ⊆ Set.Icc 0 n := by
      rintro d rfl; exact ⟨Nat.zero_le _, le_rfl⟩
    exact ⟨_, isOrderReductionFunctorIdeals_restrict hN hF⟩

end InductiveStepOne

end MMP.Resolution

end
