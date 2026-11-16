module
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldGraphDivisor
import StacksFrontier.RingTheory.OrderOfVanishing.Degree
import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UpperSemicontinuity
import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.PreimageDimension
import StacksFrontier.RingTheory.Length.FiniteModification
import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
import MMP.AlgebraicGeometry.MMP.Threefold.SurfaceLocalRings
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalenceDefs
public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation.Base
public import StacksFrontier.AlgebraicGeometry.Chow.Setup.JacobsonDimension
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# Branches and relative numerical triviality along codimension-two loci

Two local statements used in the treatment of small modifications of fourfolds over a curve
`T'` of the base.

**Branches.** Let `Y` be a scheme locally of finite type over a field, `V ⊆ Y` an irreducible
closed subset whose local ring `𝒪_{Y,η_V}` at the generic point is regular of dimension two, and
`S` a prime divisor of `Y` with multiplicity `m` along `V`. Then at most `m` prime divisors of
the normalization `S^ν` map onto `V`. Writing `f` for an equation of `S` in `𝒪 = 𝒪_{Y,η_V}` and
`R = 𝒪/(f)`, the prime divisors of `S^ν` over `V` are the maximal ideals `𝔮` of the
normalization `R̄` of `R`; for a general `t ∈ 𝔪_𝒪` one has
`m = ℓ_R(R/tR) = ℓ_R(R̄/tR̄) = ∑_𝔮 [κ(𝔮) : κ] ord_𝔮(t)`, a sum of positive integers, one for
each `𝔮`. When the residue field is finite, a general element exists after the base change
`𝒪 → 𝒪(x) = 𝒪[x]_{𝔪[x]}`.

**Relative numerical triviality.** Let `g : Y' ⟶ Y` be a proper morphism of varieties over a
field `k`, with `Y'` normal, and let `η'` be the generic point of a curve `T' ⊆ Y` such that `g`
is an isomorphism over `Y ∖ T'`. Let `D'` be a `ℚ`-Cartier `ℚ`-divisor on `Y'` with Cartier
index `m`. If `𝒪_{Y'}(m D')` has degree zero, over `κ(η')`, on every proper curve of the generic
fibre `g⁻¹(η')`, then there is an open neighbourhood `U` of `η'` such that `(D' · C) = 0` for
every proper curve `C ⊆ Y'` contracted by `g` to a point of `U`. The degree on the curves of the
fibre is spread out from the generic fibre to the fibres over a dense open of `T'`, through a
finite cover of `T'` over which the components of `Y' ×_Y T'` become flat with geometrically
irreducible fibres; away from `T'` the morphism `g` contracts no curve.

## Main results

* `MMP.Fourfold.encard_branches_le_multiplicityAlong`: the number of prime divisors of `S^ν`
  mapping onto `V` is at most `mult_V S`.
* `MMP.Fourfold.intersectionNumber_eq_zero_of_degreeOn_fiber_eq_zero`: the open neighbourhood
  `U` of `η'` over which `D'` is numerically `g`-trivial.
* `MMP.Fourfold.intersectionNumber_eq_zero_of_degreeOn_fiber_eq_zero_of_isBiregular`: the same,
  when `g` is an isomorphism only over `U₀ ∖ T'` for a neighbourhood `U₀` of `η'`.
* `MMP.Fourfold.RelativeNumericalTriviality.exists_open_fiberDegreeZero`: the degree-zero
  condition `FiberDegreeZero` spreads out from `η'` to the points of `T'` near `η'`.
* `MMP.Fourfold.RelativeNumericalTriviality.intersectionNumber_eq_zero_of_fiberDegreeZero`:
  degree zero on the fibre over a closed point `t` gives `(D' · C) = 0` for curves over `t`.

## Implementation notes

The number of branches is the cardinality `Set.encard` in `ℕ∞`, so the statement also asserts
that there are finitely many branches whenever `mult_V S` is finite; it is the branch number
`MMP.Fourfold.branchNumber S V` when finite. The multiplicity of `S` at `η_V` is
`MMP.Mori.PrimeDivisor.multiplicityAlong`. The codimension of `V` is the Krull dimension of
`𝒪_{Y,η_V}`. The hypothesis `V ⊆ S` is not needed: otherwise no prime divisor of `S^ν` maps
onto `V`.

The curves of the generic fibre are the proper curves (`MMP.Mori.ProperCurve`) of the
`κ(η')`-scheme `g.fiber η'`, and the degree of `D'` on such a curve `C` is the degree
`MMP.Mori.degreeOn` of the pull-back of `𝒪_{Y'}(m D')` to `C`; it vanishes if and only if the
degree of `D'` itself does. The curve `T'` is recorded by its generic point `η'`, with
`closure {η'}` of dimension one. The morphism is projective and birational, and the generic
fibre has dimension at most one.

## References

* [OpenAI, *Projective log canonical fourfolds*], §C.2
-/

universe u

open AlgebraicGeometry TopologicalSpace CategoryTheory

namespace MMP.Fourfold

/-! ### Branches of a prime divisor along a regular codimension-two subset -/

namespace BranchMultiplicity

/-- In a one-dimensional local Noetherian domain `A` with finite integral closure `B`, the number
of maximal ideals of `B` is at most `ord_A(a)` for every nonzero `a ∈ 𝔪_A`: each maximal ideal
`𝔫` contributes `[κ(𝔫) : κ(𝔪_A)] · ord_{B_𝔫}(a) ≥ 1` to the sum, which equals `ord_A(a)` because
`A → B` is finite and `B` has the fraction field of `A` (Stacks 02MM). -/
private lemma encard_maximal_integralClosure_le_ord (A : Type u) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsLocalRing A] (hA : ringKrullDim A = 1)
    [Module.Finite A (integralClosure A (FractionRing A))] {a : A} (ha0 : a ≠ 0)
    (ha : a ∈ IsLocalRing.maximalIdeal A) :
    {q : Ideal (integralClosure A (FractionRing A)) | q.IsMaximal}.encard ≤ Ring.ord A a := by
  haveI : Ring.KrullDimLE 1 A := by rw [Ring.krullDimLE_iff, hA]; rfl
  haveI : FaithfulSMul A (integralClosure A (FractionRing A)) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    exact fun x y hxy => IsFractionRing.injective A (FractionRing A) (congrArg Subtype.val hxy)
  haveI : IsFractionRing (integralClosure A (FractionRing A)) (FractionRing A) :=
    integralClosure.isFractionRing_of_finite_extension (FractionRing A) (FractionRing A)
  obtain ⟨hfin, hsum⟩ :=
    Ring.finite_maximalSpectrum_and_sum_inertiaDeg_mul_ord_le_and_eq_iff_finite
      (A := A) (B := integralClosure A (FractionRing A)) (K := FractionRing A)
      (L := FractionRing A)
  have heq := (hsum a ha ha0).2.mpr inferInstance
  rw [Module.finrank_self, Nat.cast_one, one_mul] at heq
  have hset : {q : Ideal (integralClosure A (FractionRing A)) | q.IsMaximal}.encard =
      ENat.card (MaximalSpectrum (integralClosure A (FractionRing A))) := by
    rw [← Set.encard_univ]
    exact (Set.encard_congr ⟨fun q => ⟨⟨q.1, q.2⟩, trivial⟩, fun q => ⟨q.1.asIdeal, q.1.isMaximal⟩,
      fun _ => rfl, fun _ => rfl⟩)
  rw [hset, ← heq]
  have := Fintype.ofFinite (MaximalSpectrum (integralClosure A (FractionRing A)))
  rw [finsum_eq_sum_of_fintype, ENat.card_eq_coe_fintype_card, ← Finset.card_univ,
    Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_le_sum fun 𝔫 _ => ?_
  have hmem : algebraMap A (integralClosure A (FractionRing A)) a ∈ 𝔫.asIdeal := by
    have hmax : (𝔫.asIdeal.comap (algebraMap A (integralClosure A (FractionRing A)))).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal 𝔫.asIdeal
    rw [← Ideal.mem_comap, IsLocalRing.eq_maximalIdeal hmax]
    exact ha
  have h1 : 1 ≤ Ring.ord (Localization.AtPrime 𝔫.asIdeal)
      (algebraMap (integralClosure A (FractionRing A)) (Localization.AtPrime 𝔫.asIdeal)
        (algebraMap A (integralClosure A (FractionRing A)) a)) := by
    rw [ENat.one_le_iff_ne_zero, Ring.ord, Ne, Module.length_eq_zero_iff,
      Ideal.Quotient.subsingleton_iff, Ideal.span_singleton_eq_top,
      IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime 𝔫.asIdeal) 𝔫.asIdeal]
    exact fun h => h hmem
  have h2 : (1 : ℕ∞) ≤ (𝔫.asIdeal.inertiaDeg A : ℕ∞) := by
    exact_mod_cast Ideal.inertiaDeg_pos (R := A) (q := 𝔫.asIdeal)
  have h3 := mul_le_mul' h2 h1
  rw [one_mul] at h3
  rw [Nat.cast_one]
  exact h3

/-- A dimension `d ≤ e` with `e + 1 ≤ 2` and `d` positive is `1`. -/
private lemma eq_one_of_le_of_add_one_le_two {d e : WithBot ℕ∞} (h1 : e + 1 ≤ 2)
    (h2 : d ≤ e) (hge : ¬ d ≤ 0) : d = 1 := by
  obtain ⟨e, rfl⟩ : ∃ n : ℕ, e = n := by
    induction e using WithBot.recBotCoe with
    | bot => exact absurd (h2.trans bot_le) hge
    | coe e =>
      induction e using ENat.recTopCoe with
      | top => exact absurd h1 (by decide)
      | coe e => exact ⟨e, rfl⟩
  obtain ⟨d, rfl⟩ : ∃ n : ℕ, d = n := by
    induction d using WithBot.recBotCoe with
    | bot => exact absurd bot_le hge
    | coe d =>
      induction d using ENat.recTopCoe with
      | top => exact absurd (WithBot.coe_le_coe.1 h2) (by simp)
      | coe d => exact ⟨d, rfl⟩
  norm_cast at *
  omega

/-- In a local domain of dimension two, the quotient by a prime that is neither zero nor maximal
has dimension one. -/
private lemma ringKrullDim_quotient_eq_one {O : Type u} [CommRing O] [IsLocalRing O] [IsDomain O]
    (hdim : ringKrullDim O = 2) {p : Ideal O} [p.IsPrime] (h0 : p ≠ ⊥) (hm : ¬ p.IsMaximal) :
    ringKrullDim (O ⧸ p) = 1 := by
  obtain ⟨r, hrp, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (R := O)
    (mem_nonZeroDivisors_of_ne_zero hr0)
  rw [hdim] at h1
  have h2 : ringKrullDim (O ⧸ p) ≤ ringKrullDim (O ⧸ Ideal.span {r}) :=
    ringKrullDim_le_of_surjective _
      (Ideal.Quotient.factor_surjective (by simpa [Ideal.span_le] using hrp))
  have hge : ¬ ringKrullDim (O ⧸ p) ≤ 0 := fun h =>
    have : Ring.KrullDimLE 0 (O ⧸ p) := Ring.krullDimLE_iff.2 (by simpa using h)
    hm ((Ideal.Quotient.maximal_ideal_iff_isField_quotient p).2
      Ring.KrullDimLE.isField_of_isDomain)
  exact eq_one_of_le_of_add_one_le_two h1 h2 hge

/-- The integral closure of a field in its fraction field has at most one maximal ideal. -/
private lemma encard_maximal_integralClosure_le_one_of_isField {F : Type u} [CommRing F]
    [IsDomain F] (hF : IsField F) :
    {q : Ideal (integralClosure F (FractionRing F)) | q.IsMaximal}.encard ≤ 1 := by
  have hB : IsField (integralClosure F (FractionRing F)) :=
    (Algebra.IsIntegral.isField_iff_isField (FaithfulSMul.algebraMap_injective F _)).1 hF
  have key : ∀ q : Ideal (integralClosure F (FractionRing F)), q.IsMaximal → q = ⊥ := fun q hq =>
    letI := hB.toField
    (Ideal.eq_bot_or_top q).resolve_right hq.ne_top
  exact Set.encard_le_one_iff.2 fun a b ha hb => (key a ha).trans (key b hb).symm

section GeneralElement

open IsLocalRing Stacks.RegularLocalRing.Domain RingTheory.Sequence

private lemma classOfPow_eq_zero_iff {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) (a : R)
    (h : a ∈ I ^ n) : AssociatedGraded.classOfPow I n ⟨a, h⟩ = 0 ↔ a ∈ I ^ (n + 1) := by
  change DirectSum.of _ n (AssociatedGraded.mk (M := R) I n ⟨a, _⟩) = 0 ↔ _
  rw [← (DirectSum.of (fun j => AssociatedGraded.piece (M := R) I j) n).map_zero,
    (DirectSum.of_injective n).eq_iff]
  refine (Submodule.Quotient.mk_eq_zero _).trans ?_
  simp only [Submodule.mem_comap, Submodule.subtype_apply, AssociatedGraded.ring_power_eq]

private lemma map_eq_zero_iff_eval_mem {R : Type u} [CommRing R] [IsLocalRing R] {x : Fin 2 → R}
    (hx : Jid x = maximalIdeal R)
    (hqr : Function.Injective (quasiRegularCanonicalMap (M := R) x)) {n : ℕ}
    {P : MvPolynomial (Fin 2) R} (hP : P.IsHomogeneous n) :
    P.map (Ideal.Quotient.mk (maximalIdeal R)) = 0 ↔
      MvPolynomial.eval x P ∈ maximalIdeal R ^ (n + 1) := by
  have hx' : ∀ i, x i ∈ maximalIdeal R := fun i => hx ▸ Ideal.subset_span ⟨i, rfl⟩
  have h := AssociatedGraded.injective_polyGradedHom (maximalIdeal R) x hx' hx hqr
  rw [← classOfPow_eq_zero_iff _ n _ (AssociatedGraded.eval_mem_pow_of_isHomogeneous _ x hx' hP),
    ← AssociatedGraded.polyGradedHom_map _ x hx' hP, ← map_zero (AssociatedGraded.polyGradedHom
      (maximalIdeal R) x hx'), h.eq_iff]

private lemma isHomogeneous_linearForm {R : Type u} [CommRing R] (a b : R) :
    (MvPolynomial.C a * MvPolynomial.X 0 - MvPolynomial.C b * MvPolynomial.X 1 :
      MvPolynomial (Fin 2) R).IsHomogeneous 1 := by
  have h0 : (MvPolynomial.C a * MvPolynomial.X 0 : MvPolynomial (Fin 2) R).IsHomogeneous 1 := by
    simpa using (MvPolynomial.isHomogeneous_C (Fin 2) a).mul
      (MvPolynomial.isHomogeneous_X R (0 : Fin 2))
  have h1 : (MvPolynomial.C b * MvPolynomial.X 1 : MvPolynomial (Fin 2) R).IsHomogeneous 1 := by
    simpa using (MvPolynomial.isHomogeneous_C (Fin 2) b).mul
      (MvPolynomial.isHomogeneous_X R (1 : Fin 2))
  exact h0.sub h1

private lemma exists_span_linearForm_eq_maximalIdeal {R : Type u} [CommRing R] [IsLocalRing R]
    {x w : Fin 2 → R} {v : Fin 2 → R ⧸ maximalIdeal R}
    (hxs : Ideal.span (Set.range x) = maximalIdeal R)
    (hw : ∀ i, Ideal.Quotient.mk (maximalIdeal R) (w i) = v i) (hv0 : v ≠ 0) :
    ∃ π : R, Ideal.span {w 1 * x 0 - w 0 * x 1, π} = maximalIdeal R := by
  have hx' : ∀ i, x i ∈ maximalIdeal R := fun i => hxs ▸ Ideal.subset_span ⟨i, rfl⟩
  set t : R := w 1 * x 0 - w 0 * x 1 with ht
  have htm : t ∈ maximalIdeal R :=
    Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (hx' 0)) (Ideal.mul_mem_left _ _ (hx' 1))
  have hunit : IsUnit (w 0) ∨ IsUnit (w 1) := by
    by_contra hcon
    push Not at hcon
    apply hv0
    have h : ∀ i, ¬ IsUnit (w i) → v i = 0 := fun i hi => by
      rw [← hw i]
      exact Ideal.Quotient.eq_zero_iff_mem.2 ((IsLocalRing.mem_maximalIdeal _).2 hi)
    ext i
    fin_cases i
    · exact h 0 hcon.1
    · exact h 1 hcon.2
  rcases hunit with ⟨u, hu⟩ | ⟨u, hu⟩
  · refine ⟨x 0, le_antisymm ?_ ?_⟩
    · exact Ideal.span_le.2 (by rintro _ (rfl | rfl) <;> [exact htm; exact hx' 0])
    · rw [← hxs, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact Ideal.subset_span (by simp)
      · have hinv : (↑u⁻¹ : R) * ↑u = 1 := by simp
        have : x 1 = (↑u⁻¹ : R) * (w 1 * x 0 - t) := by
          rw [ht, ← hu]; linear_combination (-(x 1)) * hinv
        change x 1 ∈ _
        rw [this]
        exact Ideal.mul_mem_left _ _ (Ideal.sub_mem _
          (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))) (Ideal.subset_span (by simp)))
  · refine ⟨x 1, le_antisymm ?_ ?_⟩
    · exact Ideal.span_le.2 (by rintro _ (rfl | rfl) <;> [exact htm; exact hx' 1])
    · rw [← hxs, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · have hinv : (↑u⁻¹ : R) * ↑u = 1 := by simp
        have : x 0 = (↑u⁻¹ : R) * (t + w 0 * x 1) := by
          rw [ht, ← hu]; linear_combination (-(x 0)) * hinv
        change x 0 ∈ _
        rw [this]
        exact Ideal.mul_mem_left _ _ (Ideal.add_mem _
          (Ideal.subset_span (by simp)) (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))))
      · exact Ideal.subset_span (by simp)

/-- **General element, over the associated graded ring.** In a regular local ring of dimension
two with infinite residue field and regular system of parameters `x`, for `f ∈ 𝔪^m ∖ 𝔪^(m+1)`
there is a regular system of parameters `t, π` with `f ∉ (t) + 𝔪^(m+1)`: take for `t` a linear
form in `x` not dividing the initial form of `f`. -/
private lemma exists_general_element {R : Type u} [CommRing R] [IsRegularLocalRing R]
    [Infinite (R ⧸ maximalIdeal R)] (hd : (maximalIdeal R).spanFinrank = 2) {x : Fin 2 → R}
    (hx : Jid x = maximalIdeal R)
    (hqr : Function.Injective (quasiRegularCanonicalMap (M := R) x)) {m : ℕ} (hm : 1 ≤ m)
    {f : R} (hf : f ∈ maximalIdeal R ^ m) (hf' : f ∉ maximalIdeal R ^ (m + 1)) :
    ∃ t π : R, t ∈ maximalIdeal R ∧ Ideal.span {t, π} = maximalIdeal R ∧
      f ∉ Ideal.span {t} ⊔ maximalIdeal R ^ (m + 1) := by
  classical
  have hxs : Ideal.span (Set.range x) = maximalIdeal R := hx
  obtain ⟨P, hPh, hPf⟩ := (Ideal.mem_span_pow_iff_exists_isHomogeneous x f).1 (hxs ▸ hf)
  have hF : P.map (Ideal.Quotient.mk (maximalIdeal R)) ≠ 0 := fun h =>
    hf' (hPf ▸ (map_eq_zero_iff_eval_mem hx hqr hPh).1 h)
  obtain ⟨v, hv⟩ : ∃ v : Fin 2 → R ⧸ maximalIdeal R,
      MvPolynomial.eval v (P.map (Ideal.Quotient.mk (maximalIdeal R))) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hF (MvPolynomial.funext fun w => by simp [hcon w])
  obtain ⟨w, hw⟩ : ∃ w : Fin 2 → R, ∀ i, Ideal.Quotient.mk (maximalIdeal R) (w i) = v i :=
    ⟨fun i => (Ideal.Quotient.mk_surjective (v i)).choose,
      fun i => (Ideal.Quotient.mk_surjective (v i)).choose_spec⟩
  have hx' : ∀ i, x i ∈ maximalIdeal R := fun i => hx ▸ Ideal.subset_span ⟨i, rfl⟩
  have hFh : (P.map (Ideal.Quotient.mk (maximalIdeal R))).IsHomogeneous m := hPh.map _
  have hv0 : v ≠ 0 := by
    rintro rfl
    apply hv
    rw [MvPolynomial.eval_zero]
    exact hFh.coeff_eq_zero (d := 0) (by simp; omega)
  set t : R := w 1 * x 0 - w 0 * x 1 with ht
  have htm : t ∈ maximalIdeal R :=
    Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (hx' 0)) (Ideal.mul_mem_left _ _ (hx' 1))
  let L : MvPolynomial (Fin 2) R := MvPolynomial.C (w 1) * MvPolynomial.X 0 -
      MvPolynomial.C (w 0) * MvPolynomial.X 1
  have hL : L.IsHomogeneous 1 := isHomogeneous_linearForm (w 1) (w 0)
  have hLe : MvPolynomial.eval x L = t := by simp [L, ht]
  have hLb : L.map (Ideal.Quotient.mk (maximalIdeal R)) =
      MvPolynomial.C (v 1) * MvPolynomial.X 0 - MvPolynomial.C (v 0) * MvPolynomial.X 1 := by
    simp [L, hw]
  have ht1 : t ∉ maximalIdeal R ^ 2 := by
    intro h2
    have h := (map_eq_zero_iff_eval_mem hx hqr hL).2 (hLe ▸ h2)
    rw [hLb] at h
    apply hv0
    have e0 := congrArg (MvPolynomial.eval (Pi.single 0 1 : Fin 2 → R ⧸ maximalIdeal R)) h
    have e1 := congrArg (MvPolynomial.eval (Pi.single 1 1 : Fin 2 → R ⧸ maximalIdeal R)) h
    simp at e0 e1
    ext i
    fin_cases i <;> simp [e0, e1]
  obtain ⟨π, hπ⟩ := exists_span_linearForm_eq_maximalIdeal hxs hw hv0
  refine ⟨t, π, htm, hπ, ?_⟩
  intro hmem
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hmem
  obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  have hgt : g * t ∈ maximalIdeal R ^ m := by
    rw [show g * t = f - b by rw [← hab]; ring]
    exact Ideal.sub_mem _ hf (Ideal.pow_le_pow_right (Nat.le_succ m) hb)
  have hg : g ∈ maximalIdeal R ^ (m - 1) :=
    (MMP.Mori.SurfaceAux.mul_mem_pow_iff hd (a := 1) (by simpa using htm) ht1 g m).1 hgt
  obtain ⟨Q, hQh, hQg⟩ := (Ideal.mem_span_pow_iff_exists_isHomogeneous x g).1 (hxs ▸ hg)
  have hD : (P - L * Q).IsHomogeneous m := by
    have := hL.mul hQh
    rw [show 1 + (m - 1) = m by omega] at this
    exact hPh.sub this
  have hDe : MvPolynomial.eval x (P - L * Q) ∈ maximalIdeal R ^ (m + 1) := by
    rw [map_sub, map_mul, hLe, hQg, hPf]
    rwa [show f - t * g = b by rw [← hab]; ring]
  have h0 := (map_eq_zero_iff_eval_mem hx hqr hD).2 hDe
  rw [map_sub, map_mul, sub_eq_zero] at h0
  apply hv
  rw [h0, map_mul, hLb]
  have h1 : MvPolynomial.eval v (MvPolynomial.C (v 1) * MvPolynomial.X 0 -
      MvPolynomial.C (v 0) * MvPolynomial.X 1 : MvPolynomial (Fin 2) (R ⧸ maximalIdeal R)) = 0 := by
    simp only [map_sub, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
    ring
  rw [h1, zero_mul]

private lemma length_quotient_span_pair_pow_le {R : Type u} [CommRing R] [IsLocalRing R] {t π : R}
    (hs : Ideal.span {t, π} = maximalIdeal R) (j : ℕ) :
    Module.length R (R ⧸ Ideal.span {t, π ^ j}) ≤ j := by
  induction j with
  | zero =>
    have : Ideal.span {t, π ^ 0} = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp)) isUnit_one
    rw [this]
    simp
  | succ j ih =>
    set I := Ideal.span {t, π ^ j} with hI
    set J := Ideal.span {t, π ^ (j + 1)} with hJ
    have htJ : t ∈ J := Ideal.subset_span (by simp)
    have hπJ : π ^ (j + 1) ∈ J := Ideal.subset_span (by simp)
    have hle : J ≤ I := by
      refine Ideal.span_le.2 ?_
      rintro _ (rfl | rfl)
      · exact Ideal.subset_span (by simp)
      · rw [pow_succ]
        exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
    let M := R ⧸ J
    let K : Submodule R M := Submodule.map J.mkQ (I : Submodule R R)
    have e1 : Module.length R M = Module.length R K + Module.length R (M ⧸ K) :=
      Module.length_eq_add_of_exact K.subtype K.mkQ K.subtype_injective K.mkQ_surjective
        (LinearMap.exact_subtype_mkQ K)
    have e2 : Module.length R (M ⧸ K) = Module.length R (R ⧸ I) :=
      (Submodule.quotientQuotientEquivQuotient J I hle).length_eq
    have e3 : Module.length R K ≤ 1 := by
      let e : M := J.mkQ (π ^ j)
      have he : e ∈ K := ⟨π ^ j, Ideal.subset_span (by simp), rfl⟩
      let f : R →ₗ[R] K := LinearMap.toSpanSingleton R K ⟨e, he⟩
      have hf : Function.Surjective f := by
        rintro ⟨_, r, hr, rfl⟩
        obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 hr
        refine ⟨b, Subtype.ext ?_⟩
        have : J.mkQ (a * t) = 0 := by
          rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
          exact Ideal.mul_mem_left _ _ htJ
        simp only [f, LinearMap.toSpanSingleton_apply, Submodule.coe_smul]
        rw [← hab, map_add, this, zero_add]
        simp only [e, Submodule.mkQ_apply]
        rw [← Submodule.Quotient.mk_smul]; rfl
      have hker : maximalIdeal R ≤ LinearMap.ker f := by
        rw [← hs, Ideal.span_le]
        rintro _ (rfl | rfl)
        · refine LinearMap.mem_ker.2 (Subtype.ext ?_)
          simp only [f, LinearMap.toSpanSingleton_apply, Submodule.coe_smul, e, Submodule.mkQ_apply]
          rw [← Submodule.Quotient.mk_smul]
          refine (Submodule.Quotient.mk_eq_zero J).2 ?_
          exact Ideal.mul_mem_right _ _ htJ
        · refine LinearMap.mem_ker.2 (Subtype.ext ?_)
          simp only [f, LinearMap.toSpanSingleton_apply, Submodule.coe_smul, e, Submodule.mkQ_apply]
          rw [← Submodule.Quotient.mk_smul]
          refine (Submodule.Quotient.mk_eq_zero J).2 ?_
          simpa [smul_eq_mul, ← pow_succ'] using hπJ
      let g : (R ⧸ maximalIdeal R) →ₗ[R] K := Submodule.liftQ _ f hker
      have hg : Function.Surjective g := by
        intro k
        obtain ⟨r, hr⟩ := hf k
        exact ⟨Submodule.Quotient.mk r, hr⟩
      haveI : IsSimpleModule R (R ⧸ maximalIdeal R) :=
        isSimpleModule_iff_isCoatom.2 (maximalIdeal.isMaximal R).out
      calc Module.length R K ≤ Module.length R (R ⧸ maximalIdeal R) :=
            Module.length_le_of_surjective g hg
        _ = 1 := Module.length_eq_one _ _
    show Module.length R M ≤ j + 1
    rw [e1, e2]
    calc _ ≤ 1 + (j : ℕ∞) := add_le_add e3 ih
      _ = _ := by push_cast; ring

private lemma span_pair_pow_le {R : Type u} [CommRing R] (t π : R) (j : ℕ) :
    Ideal.span {t, π} ^ j ≤ Ideal.span {t} ⊔ Ideal.span {π ^ j} := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ]
    refine (Ideal.mul_mono_left ih).trans ?_
    rw [Ideal.sup_mul]
    refine sup_le ((show Ideal.span {t} * Ideal.span {t, π} ≤ Ideal.span {t} from
      Ideal.mul_le_left).trans le_sup_left) ?_
    rw [Ideal.mul_le]
    intro r hr s hs
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    obtain ⟨c, d, rfl⟩ := Ideal.mem_span_pair.1 hs
    have : b * π ^ j * (c * t + d * π) = (b * π ^ j * c) * t + (b * d) * π ^ (j + 1) := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton'.2 ⟨_, rfl⟩))
      (Ideal.mem_sup_right (Ideal.mem_span_singleton'.2 ⟨_, rfl⟩))

private lemma length_quotient_span_pair_le {R : Type u} [CommRing R] [IsLocalRing R] {t π f : R}
    {m : ℕ} (hs : Ideal.span {t, π} = maximalIdeal R) (hf : f ∈ maximalIdeal R ^ m)
    (hf' : f ∉ Ideal.span {t} ⊔ maximalIdeal R ^ (m + 1)) :
    Module.length R (R ⧸ Ideal.span {t, f}) ≤ m := by
  classical
  have hex : ∃ n, f ∉ Ideal.span {t} ⊔ maximalIdeal R ^ (n + 1) := ⟨m, hf'⟩
  set j := Nat.find hex with hj
  have hjm : j ≤ m := Nat.find_min' hex hf'
  have hj1 : f ∉ Ideal.span {t} ⊔ maximalIdeal R ^ (j + 1) := Nat.find_spec hex
  have hj0 : f ∈ Ideal.span {t} ⊔ maximalIdeal R ^ j := by
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · rw [h0]; simp
    · have := Nat.find_min hex (show j - 1 < j by omega)
      rw [show j - 1 + 1 = j by omega] at this
      exact not_not.1 this
  have hπ : π ∈ maximalIdeal R := hs ▸ Ideal.subset_span (by simp)
  have hmem : f ∈ Ideal.span {t, π ^ j} := by
    have h1 : Ideal.span {t} ⊔ maximalIdeal R ^ j ≤ Ideal.span {t, π ^ j} := by
      refine sup_le (Ideal.span_mono (by simp)) ?_
      rw [← hs]
      refine (span_pair_pow_le t π j).trans (sup_le (Ideal.span_mono (by simp)) ?_)
      exact Ideal.span_mono (by simp)
    exact h1 hj0
  obtain ⟨c, d, hcd⟩ := Ideal.mem_span_pair.1 hmem
  have hd : IsUnit d := by
    by_contra hdn
    apply hj1
    rw [← hcd]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (Ideal.mem_span_singleton'.2 ⟨c, rfl⟩))
      (Submodule.mem_sup_right ?_)
    rw [pow_succ']
    exact Ideal.mul_mem_mul ((IsLocalRing.mem_maximalIdeal _).2 hdn) (Ideal.pow_mem_pow hπ j)
  have heq : Ideal.span {t, f} = Ideal.span {t, π ^ j} := by
    obtain ⟨u, rfl⟩ := hd
    refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.span_le.2 ?_)
    · rintro _ (rfl | rfl)
      · exact Ideal.subset_span (by simp)
      · exact hmem
    · rintro _ (rfl | rfl)
      · exact Ideal.subset_span (by simp)
      · have : π ^ j = (↑u⁻¹ : R) * (f - c * t) := by
          rw [← hcd]; simp
        rw [this]
        exact Ideal.mul_mem_left _ _ (Ideal.sub_mem _ (Ideal.subset_span (by simp))
          (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))))
  rw [heq]
  exact (length_quotient_span_pair_pow_le hs j).trans (by exact_mod_cast hjm)

/-- **General element.** Let `𝒪` be a regular local ring of dimension two with infinite residue
field, `𝔭` a prime of height one and `A = 𝒪/𝔭`. Some nonzero nonunit `t ∈ A` has
`ord_A(t) = length_A(A/tA) ≤ sup {s | 𝔭 ≤ 𝔪^s}`: take `t` whose initial form is not divisible by
the initial form of a generator of `𝔭`. -/
private lemma exists_ord_le_multiplicity_of_infinite (O : Type u) [CommRing O] [IsLocalRing O]
    [IsRegularLocalRing O] [Infinite (IsLocalRing.ResidueField O)] (hdim : ringKrullDim O = 2)
    (p : Ideal O) [p.IsPrime] (h0 : p ≠ ⊥) (hm : ¬ p.IsMaximal) :
    ∃ t : O ⧸ p, ¬ IsUnit t ∧ t ≠ 0 ∧
      Ring.ord (O ⧸ p) t ≤ ⨆ (s : ℕ) (_ : p ≤ IsLocalRing.maximalIdeal O ^ s), (s : ℕ∞) := by
  classical
  have hd := MMP.Mori.SurfaceAux.spanFinrank_eq_two_of_ringKrullDim hdim
  obtain ⟨x, hx, hqr⟩ := MMP.Mori.SurfaceAux.exists_quasiRegular_gens hd
  have hpm : p ≤ maximalIdeal O := IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)
  have hex : ∃ a : ℕ, ¬ p ≤ maximalIdeal O ^ (a + 1) := by
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    obtain ⟨a, ha, ha'⟩ := MMP.Mori.SurfaceAux.exists_order (R := O) hu0
    exact ⟨a, fun h => ha' (h hu)⟩
  set m := Nat.find hex with hmdef
  have hm1 : ¬ p ≤ maximalIdeal O ^ (m + 1) := Nat.find_spec hex
  have hpm' : p ≤ maximalIdeal O ^ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · simp [h]
    · have := Nat.find_min hex (show m - 1 < m by omega)
      rw [show m - 1 + 1 = m by omega] at this
      exact not_not.1 this
  have hm1' : 1 ≤ m := by
    by_contra h
    apply hm1
    rw [show m = 0 by omega]
    simpa using hpm
  obtain ⟨f, hfp, hf'⟩ := Set.not_subset.1 hm1
  have hf : f ∈ maximalIdeal O ^ m := hpm' hfp
  haveI : Infinite (O ⧸ maximalIdeal O) := inferInstanceAs (Infinite (IsLocalRing.ResidueField O))
  obtain ⟨t, π, htm, hts, hft⟩ := exists_general_element hd hx hqr hm1' hf hf'
  have hlen : Module.length O (O ⧸ Ideal.span {t, f}) ≤ m :=
    length_quotient_span_pair_le hts hf hft
  have hord : Ring.ord (O ⧸ p) (Ideal.Quotient.mk p t) ≤ m := by
    unfold Ring.ord
    rw [← Module.length_eq_of_surjective (S := O) (R := O ⧸ p) Ideal.Quotient.mk_surjective]
    let g : O →ₗ[O] (O ⧸ p) ⧸ Ideal.span {Ideal.Quotient.mk p t} :=
      ((Submodule.mkQ (Ideal.span {Ideal.Quotient.mk p t})).restrictScalars O).comp
        (Submodule.mkQ p)
    have hker : (Ideal.span {t, f} : Submodule O O) ≤ LinearMap.ker g := by
      refine Ideal.span_le.2 ?_
      rintro a (ha | ha)
      · rw [ha]
        refine LinearMap.mem_ker.2 ?_
        simp only [g, LinearMap.comp_apply, LinearMap.restrictScalars_apply, Submodule.mkQ_apply]
        exact (Submodule.Quotient.mk_eq_zero _).2 (Ideal.subset_span (by simp))
      · rw [Set.mem_singleton_iff.1 ha]
        refine LinearMap.mem_ker.2 ?_
        have : (Submodule.mkQ p) f = 0 := (Submodule.Quotient.mk_eq_zero _).2 hfp
        simp [g, this]
    refine (Module.length_le_of_surjective (Submodule.liftQ _ g hker) ?_).trans hlen
    intro y
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨r, rfl⟩ := Submodule.mkQ_surjective _ z
    exact ⟨Submodule.mkQ _ r, rfl⟩
  have hmle : (m : ℕ∞) ≤ ⨆ (s : ℕ) (_ : p ≤ IsLocalRing.maximalIdeal O ^ s), (s : ℕ∞) :=
    le_iSup₂_of_le (f := fun (s : ℕ) (_ : p ≤ IsLocalRing.maximalIdeal O ^ s) => (s : ℕ∞))
      m hpm' le_rfl
  refine ⟨Ideal.Quotient.mk p t, ?_, ?_, hord.trans hmle⟩
  · rintro ⟨u, hu⟩
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (↑u⁻¹ : O ⧸ p)
    have h1 : Ideal.Quotient.mk p (t * s) = 1 := by
      rw [map_mul, hs, ← hu]; simp
    have h2 : t * s - 1 ∈ p := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h1, map_one, sub_self]
    have h3 : t * s - 1 ∈ maximalIdeal O := hpm h2
    have h4 : (1 : O) ∈ maximalIdeal O := by
      have := Ideal.sub_mem _ (Ideal.mul_mem_right s _ htm) h3
      simpa using this
    exact (maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h4)
  · intro hzero
    have hfin : Module.length (O ⧸ p) ((O ⧸ p) ⧸ Ideal.span {Ideal.Quotient.mk p t}) ≠ ⊤ := by
      refine ne_top_of_le_ne_top (ENat.natCast_ne_top m) ?_
      exact hord
    rw [hzero] at hfin
    have hbot : (Ideal.span {(0 : O ⧸ p)}) = ⊥ := by simp
    have e := Submodule.quotEquivOfEqBot (Ideal.span {(0 : O ⧸ p)}) hbot
    rw [e.length_eq] at hfin
    have hart : IsArtinianRing (O ⧸ p) :=
      (isFiniteLength_iff_isNoetherian_isArtinian.1 (Module.length_ne_top_iff.1 hfin)).2
    exact hm (Ideal.Quotient.maximal_of_isField _ (IsArtinianRing.isField_of_isDomain _))

end GeneralElement

section FiniteResidueField

open Polynomial IsLocalRing
open scoped Pointwise

noncomputable section

/-- Herbrand step: for a finite extension domain `N ⊇ A` with torsion cokernel,
`ord_A(a) = length_A(N/aN)`. -/
private lemma ord_eq_length_quotient_of_finite_extension {A N : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsLocalRing A] (hA : ringKrullDim A = 1) [CommRing N] [IsDomain N]
    [Algebra A N] [Module.Finite A N] (hinj : Function.Injective (algebraMap A N))
    (htors : ∀ x : N, ∃ d : A, d ≠ 0 ∧ d • x ∈ LinearMap.range (Algebra.linearMap A N))
    {a : A} (ha : a ≠ 0) :
    IsFiniteLength A (N ⧸ a • (⊤ : Submodule A N)) ∧
      Ring.ord A a = Module.length A (N ⧸ a • (⊤ : Submodule A N)) := by
  haveI : Ring.KrullDimLE 1 A := by rw [Ring.krullDimLE_iff, hA]; rfl
  let i : A →ₗ[A] N := Algebra.linearMap A N
  have htorsQ : Module.IsTorsion A (N ⧸ LinearMap.range i) := by
    intro q
    obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ q
    obtain ⟨d, hd, hdb⟩ := htors b
    refine ⟨⟨d, mem_nonZeroDivisors_of_ne_zero hd⟩, ?_⟩
    change d • (LinearMap.range i).mkQ b = 0
    rw [← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hdb
  obtain ⟨d, hdann, hdnzd⟩ := Submodule.annihilator_top_inter_nonZeroDivisors htorsQ
  have hQ : Module.length A (N ⧸ LinearMap.range (Algebra.linearMap A N)) ≠ ⊤ :=
    Stacks.Length.length_ne_top_of_isTorsionBy_nonZeroDivisor hdnzd
      (fun x => Submodule.mem_annihilator.mp hdann x Submodule.mem_top)
  have hreg : IsSMulRegular N a := by
    intro x y hxy
    have haN : algebraMap A N a ≠ 0 := (map_ne_zero_iff _ hinj).2 ha
    exact mul_left_cancel₀ haN (by simpa [Algebra.smul_def] using hxy)
  have key := Stacks.Length.length_quotient_span_eq hinj hQ hreg
  have hset : a • (⊤ : Submodule A N) =
      (Ideal.span {algebraMap A N a} : Ideal N).restrictScalars A := by
    ext x
    rw [Submodule.mem_smul_pointwise_iff_exists, Submodule.restrictScalars_mem,
      Ideal.mem_span_singleton']
    constructor
    · rintro ⟨b, -, rfl⟩
      exact ⟨b, by rw [Algebra.smul_def, mul_comm]⟩
    · rintro ⟨b, rfl⟩
      exact ⟨b, Submodule.mem_top, by rw [Algebra.smul_def, mul_comm]⟩
  have hlen : Ring.ord A a = Module.length A (N ⧸ a • (⊤ : Submodule A N)) := by
    rwa [hset, (Submodule.Quotient.restrictScalarsEquiv A
      (Ideal.span {algebraMap A N a} : Ideal N)).length_eq]
  refine ⟨Module.length_ne_top_iff.mp ?_, hlen⟩
  rw [← hlen, Ring.ord, Module.length_ne_top_iff]
  exact isFiniteLength_quotient_span_singleton A (mem_nonZeroDivisors_of_ne_zero ha)

private lemma card_le_length_quotient {A N : Type u} [CommRing A] [IsLocalRing A] [CommRing N]
    [Algebra A N] [Module.Finite A N] {a : A} (ha : a ∈ maximalIdeal A) (F : Finset (Ideal N))
    (hF : ∀ q ∈ F, q.IsMaximal) :
    (F.card : ℕ∞) ≤ Module.length A (N ⧸ a • (⊤ : Submodule A N)) := by
  classical
  have haq : ∀ q ∈ F, algebraMap A N a ∈ q := by
    intro q hq
    haveI := hF q hq
    rw [← Ideal.mem_comap, ← Ideal.under_def]
    rwa [IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) q)]
  let g : N →ₗ[A] (∀ q : F, N ⧸ q.1) :=
    LinearMap.pi fun q => (Ideal.Quotient.mkₐ A q.1).toLinearMap
  have hg : Function.Surjective g := by
    have hcop : Pairwise (Function.onFun IsCoprime fun q : F => q.1) := by
      intro q q' hne
      haveI := hF q.1 q.2
      haveI := hF q'.1 q'.2
      exact (Ideal.isCoprime_iff_sup_eq).2 (Ideal.IsMaximal.coprime_of_ne ‹_› ‹_›
        (fun h => hne (Subtype.ext h)))
    intro y
    obtain ⟨z, hz⟩ := Ideal.quotientInfToPiQuotient_surj hcop y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨x, by rw [← hz]; rfl⟩
  have hker : a • (⊤ : Submodule A N) ≤ LinearMap.ker g := by
    rintro _ ⟨x, -, rfl⟩
    refine LinearMap.mem_ker.2 (funext fun q => ?_)
    simp only [g, LinearMap.pi_apply, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
      Pi.zero_apply]
    change Ideal.Quotient.mk q.1 (a • x) = 0
    rw [Algebra.smul_def, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (haq q.1 q.2)
  have hs : Function.Surjective (Submodule.liftQ _ g hker) := by
    intro y
    obtain ⟨x, rfl⟩ := hg y
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  refine le_trans ?_ (Module.length_le_of_surjective _ hs)
  rw [Module.length_pi_of_fintype]
  calc (F.card : ℕ∞) = ∑ _q : F, 1 := by simp
    _ ≤ _ := Finset.sum_le_sum fun q _ => by
      haveI : Nontrivial (N ⧸ q.1) := Ideal.Quotient.nontrivial_iff.2 (hF q.1 q.2).ne_top
      exact Order.one_le_iff_pos.2 Module.length_pos

private lemma encard_maximal_le_ord_of_finite_extension {A N : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsLocalRing A] (hA : ringKrullDim A = 1) [CommRing N] [IsDomain N]
    [Algebra A N] [Module.Finite A N] (hinj : Function.Injective (algebraMap A N))
    (htors : ∀ x : N, ∃ d : A, d ≠ 0 ∧ d • x ∈ LinearMap.range (Algebra.linearMap A N))
    {a : A} (ha0 : a ≠ 0) (ha : a ∈ maximalIdeal A) :
    {q : Ideal N | q.IsMaximal}.encard ≤ Ring.ord A a := by
  rw [(ord_eq_length_quotient_of_finite_extension hA hinj htors ha0).2]
  by_contra hlt
  push Not at hlt
  have hne : Module.length A (N ⧸ a • (⊤ : Submodule A N)) ≠ ⊤ := ne_top_of_lt hlt
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hne
  rw [← hn] at hlt
  have hle : ((n + 1 : ℕ) : ℕ∞) ≤ {q : Ideal N | q.IsMaximal}.encard :=
    mod_cast Order.add_one_le_of_lt hlt
  obtain ⟨t, hts, htc⟩ := Set.exists_subset_encard_eq hle
  have htf : t.Finite := Set.finite_of_encard_eq_coe htc
  have hcard := card_le_length_quotient (N := N) ha htf.toFinset
    (fun q hq => hts (htf.mem_toFinset.1 hq))
  have hc : htf.toFinset.card = n + 1 := by
    have := Set.encard_coe_eq_coe_finsetCard htf.toFinset
    rw [htf.coe_toFinset, htc] at this
    exact_mod_cast this.symm
  rw [hc, ← hn] at hcard
  exact absurd hcard (by exact_mod_cast Nat.not_succ_le_self n)

private abbrev mC (O : Type u) [CommRing O] [IsLocalRing O] : Ideal O[X] :=
  Ideal.map (C : O →+* O[X]) (maximalIdeal O)

private abbrev XLoc (O : Type u) [CommRing O] [IsLocalRing O] := Localization.AtPrime (mC O)

section ExtO

variable (O : Type u) [CommRing O] [IsLocalRing O]

private lemma comap_mC : (mC O).comap (C : O →+* O[X]) = maximalIdeal O := by
  ext x
  rw [Ideal.mem_comap, Ideal.mem_map_C_iff]
  refine ⟨fun h => by simpa using h 0, fun h n => ?_⟩
  simp only [coeff_C]
  split_ifs
  · exact h
  · exact zero_mem _

private lemma isRegularLocalRing_ext [IsRegularLocalRing O] : IsRegularLocalRing (XLoc O) :=
  Polynomial.isRegularLocalRing_localization_atPrime_of_comap_eq_maximalIdeal O (mC O)
    (comap_mC O)

private lemma ringKrullDim_ext [IsNoetherianRing O] (hdim : ringKrullDim O = 2) :
    ringKrullDim (XLoc O) = 2 := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (mC O) (XLoc O), Polynomial.height_map_C,
    maximalIdeal_height_eq_ringKrullDim, hdim]

private lemma infinite_residueField_ext : Infinite (XLoc O ⧸ maximalIdeal (XLoc O)) := by
  let θ : O[X] →+* XLoc O ⧸ maximalIdeal (XLoc O) :=
    (Ideal.Quotient.mk _).comp (algebraMap O[X] (XLoc O))
  refine Infinite.of_injective (fun n : ℕ => θ (Polynomial.X ^ n)) fun n m hnm => ?_
  by_contra hne
  have h1 : (Polynomial.X ^ n - Polynomial.X ^ m : O[X]) ∈ mC O := by
    have : (Polynomial.X ^ n - Polynomial.X ^ m : O[X]) ∈
        (maximalIdeal (XLoc O)).comap (algebraMap O[X] (XLoc O)) := by
      rw [Ideal.mem_comap, map_sub, ← Ideal.Quotient.eq_zero_iff_mem]
      change θ (Polynomial.X ^ n) - θ (Polynomial.X ^ m) = 0
      rwa [sub_eq_zero]
    rwa [show (maximalIdeal (XLoc O)).comap (algebraMap O[X] (XLoc O)) = mC O from
      IsLocalization.AtPrime.under_maximalIdeal (XLoc O) (mC O)] at this
  rw [Ideal.mem_map_C_iff] at h1
  have := h1 n
  simp only [coeff_sub, coeff_X_pow, if_true] at this
  rw [if_neg hne, sub_zero] at this
  exact (maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 this)

private instance : Module.Flat O (XLoc O) := by
  haveI : Module.Flat O O[X] := inferInstance
  haveI : Module.Flat O[X] (XLoc O) := IsLocalization.flat (XLoc O) (mC O).primeCompl
  exact Module.Flat.trans O O[X] (XLoc O)

private lemma maximalIdeal_ext_eq : maximalIdeal (XLoc O) =
    Ideal.map (algebraMap O (XLoc O)) (maximalIdeal O) := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal (I := mC O), Ideal.map_map]
  rfl

private instance : IsLocalHom (algebraMap O (XLoc O)) := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have h1 : a ∈ maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hna
  have h2 : algebraMap O (XLoc O) a ∈ maximalIdeal (XLoc O) := by
    rw [maximalIdeal_ext_eq]; exact Ideal.mem_map_of_mem _ h1
  exact (IsLocalRing.mem_maximalIdeal _).1 h2 ha

private instance : Module.FaithfullyFlat O (XLoc O) :=
  Module.FaithfullyFlat.of_flat_of_isLocalHom

private lemma comap_map_ext (I : Ideal O) :
    (I.map (algebraMap O (XLoc O))).comap (algebraMap O (XLoc O)) = I :=
  Ideal.comap_map_eq_self_of_faithfullyFlat I

private lemma isPrime_map_ext (p : Ideal O) [hp : p.IsPrime] :
    (p.map (algebraMap O (XLoc O))).IsPrime := by
  have hpm : p ≤ maximalIdeal O := IsLocalRing.le_maximalIdeal hp.ne_top
  have h1 : (p.map (C : O →+* O[X])).IsPrime := Ideal.isPrime_map_C_of_isPrime
  have h2 : p.map (algebraMap O (XLoc O)) =
      (p.map (C : O →+* O[X])).map (algebraMap O[X] (XLoc O)) := by
    rw [Ideal.map_map]; rfl
  rw [h2]
  refine IsLocalization.isPrime_of_isPrime_disjoint (mC O).primeCompl (XLoc O) _ h1 ?_
  rw [Set.disjoint_left]
  intro x hx hx'
  exact hx (Ideal.map_mono hpm hx')

private lemma map_ext_ne_bot (p : Ideal O) (h : p ≠ ⊥) : p.map (algebraMap O (XLoc O)) ≠ ⊥ := by
  intro h0
  apply h
  rw [← comap_map_ext O p, h0, Ideal.comap_bot_of_injective _
    (FaithfulSMul.algebraMap_injective O (XLoc O))]

private lemma not_isMaximal_map_ext (p : Ideal O) (h : ¬ p.IsMaximal) :
    ¬ (p.map (algebraMap O (XLoc O))).IsMaximal := by
  intro hm
  apply h
  have : p.map (algebraMap O (XLoc O)) = maximalIdeal (XLoc O) := IsLocalRing.eq_maximalIdeal hm
  rw [← comap_map_ext O p, this, maximalIdeal_ext_eq, comap_map_ext]
  exact maximalIdeal.isMaximal O

private lemma map_ext_le_pow_iff (p : Ideal O) (s : ℕ) :
    p.map (algebraMap O (XLoc O)) ≤ maximalIdeal (XLoc O) ^ s ↔ p ≤ maximalIdeal O ^ s := by
  rw [maximalIdeal_ext_eq, ← Ideal.map_pow]
  refine ⟨fun h => ?_, Ideal.map_mono⟩
  have := Ideal.comap_mono (f := algebraMap O (XLoc O)) h
  rwa [comap_map_ext, comap_map_ext] at this

end ExtO

section Rel

variable (R : Type u) [CommRing R] [IsLocalRing R] (RB : Type u) [CommRing RB] [IsDomain RB]
  [Algebra R RB] [FaithfulSMul R RB]

private abbrev phi : R[X] →+* RB[X] := Polynomial.mapRingHom (algebraMap R RB)

private abbrev Nrel := Localization (Submonoid.map (phi R RB) (mC R).primeCompl)

private abbrev lamNrel : XLoc R →+* Nrel R RB :=
  IsLocalization.map (Nrel R RB) (phi R RB) (Submonoid.le_comap_map (mC R).primeCompl)

@[instance_reducible] private def algNrel : Algebra (XLoc R) (Nrel R RB) := (lamNrel R RB).toAlgebra

attribute [local instance] algNrel

private lemma algebraMap_nrel (f : R[X]) :
    algebraMap (XLoc R) (Nrel R RB) (algebraMap R[X] (XLoc R) f) =
      algebraMap RB[X] (Nrel R RB) (phi R RB f) :=
  IsLocalization.map_eq (Submonoid.le_comap_map (mC R).primeCompl) f

private lemma phi_injective : Function.Injective (phi R RB) :=
  Polynomial.map_injective _ (FaithfulSMul.algebraMap_injective R RB)

private instance : IsDomain (Nrel R RB) := by
  refine IsLocalization.isDomain_localization (M := Submonoid.map (phi R RB) (mC R).primeCompl) ?_
  rintro _ ⟨s, hs, rfl⟩
  refine mem_nonZeroDivisors_of_ne_zero ?_
  intro h0
  have : s = 0 := (phi_injective R RB) (by simpa using h0)
  exact hs (this ▸ zero_mem _)

private lemma algebraMap_ext_nrel_injective :
    Function.Injective (algebraMap (XLoc R) (Nrel R RB)) :=
  IsLocalization.map_injective_of_injective (mC R).primeCompl (XLoc R) (Nrel R RB)
    (phi_injective R RB)

private abbrev iota : RB →+* Nrel R RB := (algebraMap RB[X] (Nrel R RB)).comp C

/-- Every element of `N` is a `(XLoc R)`-multiple of the image of a polynomial over `R̄`. -/
private lemma exists_eq_lam_mul (x : Nrel R RB) :
    ∃ (u : XLoc R) (f : RB[X]), x = algebraMap (XLoc R) (Nrel R RB) u *
      algebraMap RB[X] (Nrel R RB) f := by
  obtain ⟨⟨f, t⟩, hx⟩ :=
    IsLocalization.mk'_surjective (Submonoid.map (phi R RB) (mC R).primeCompl) x
  obtain ⟨_, ⟨s0, hs0, rfl⟩⟩ := t
  subst hx
  refine ⟨IsLocalization.mk' (XLoc R) (1 : R[X]) ⟨s0, hs0⟩, f, ?_⟩
  have hu : algebraMap (XLoc R) (Nrel R RB) (IsLocalization.mk' (XLoc R) (1 : R[X]) ⟨s0, hs0⟩) =
      IsLocalization.mk' (Nrel R RB) (1 : RB[X]) (⟨phi R RB s0, ⟨s0, hs0, rfl⟩⟩ :
        Submonoid.map (phi R RB) (mC R).primeCompl) := by
    rw [IsLocalization.eq_mk'_iff_mul_eq, ← algebraMap_nrel, ← map_mul,
      IsLocalization.mk'_spec, map_one, map_one, map_one]
  rw [hu]
  exact (IsLocalization.mk'_eq_mul_mk'_one (S := Nrel R RB) f _).trans (mul_comm _ _)

private lemma iota_algebraMap (r : R) :
    iota R RB (algebraMap R RB r) =
      algebraMap (XLoc R) (Nrel R RB) (algebraMap R[X] (XLoc R) (C r)) := by
  rw [algebraMap_nrel]
  simp [iota, phi]

private lemma algebraMap_X :
    algebraMap RB[X] (Nrel R RB) Polynomial.X =
      algebraMap (XLoc R) (Nrel R RB) (algebraMap R[X] (XLoc R) Polynomial.X) := by
  rw [algebraMap_nrel]
  simp [phi]

private lemma finite_nrel [Module.Finite R RB] : Module.Finite (XLoc R) (Nrel R RB) := by
  classical
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top (R := R) (M := RB))
  refine ⟨⟨s.image (iota R RB), ?_⟩⟩
  set T := Submodule.span (XLoc R) (↑(s.image (iota R RB)) : Set (Nrel R RB)) with hT
  have hι : ∀ c : RB, iota R RB c ∈ T := by
    intro c
    have hc : c ∈ Submodule.span R (s : Set RB) := by rw [hs]; trivial
    induction hc using Submodule.span_induction with
    | mem c hc =>
      exact Submodule.subset_span
        (Finset.mem_coe.2 (Finset.mem_image.2 ⟨c, Finset.mem_coe.1 hc, rfl⟩))
    | zero => rw [map_zero]; exact T.zero_mem
    | add a b _ _ ha hb => rw [map_add]; exact T.add_mem ha hb
    | smul r c _ hc =>
      have : iota R RB (r • c) = algebraMap (XLoc R) (Nrel R RB) (algebraMap R[X] (XLoc R) (C r)) *
          iota R RB c := by
        rw [Algebra.smul_def, map_mul, iota_algebraMap]
      rw [this]
      exact T.smul_mem (algebraMap R[X] (XLoc R) (C r)) hc
  have hf : ∀ f : RB[X], algebraMap RB[X] (Nrel R RB) f ∈ T := by
    intro f
    induction f using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add]; exact T.add_mem hp hq
    | monomial n c =>
      have : algebraMap RB[X] (Nrel R RB) (monomial n c) =
          (algebraMap (XLoc R) (Nrel R RB) (algebraMap R[X] (XLoc R) Polynomial.X)) ^ n *
            iota R RB c := by
        rw [← algebraMap_X, ← C_mul_X_pow_eq_monomial, map_mul, map_pow, mul_comm]
        rfl
      rw [this, ← map_pow, ← Algebra.smul_def, ← map_pow]
      exact T.smul_mem _ (hι c)
  rw [eq_top_iff]
  intro x _
  obtain ⟨u, f, rfl⟩ := exists_eq_lam_mul R RB x
  rw [← Algebra.smul_def]
  exact T.smul_mem u (hf f)

private lemma exists_phi_eq (D : R)
    (hD : ∀ c : RB, algebraMap R RB D * c ∈ Set.range (algebraMap R RB))
    (f : RB[X]) : ∃ g : R[X], phi R RB g = C (algebraMap R RB D) * f := by
  classical
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨g1, h1⟩ := hp
    obtain ⟨g2, h2⟩ := hq
    exact ⟨g1 + g2, by rw [map_add, h1, h2, mul_add]⟩
  | monomial n c =>
    obtain ⟨r, hr⟩ := hD c
    refine ⟨monomial n r, ?_⟩
    rw [C_mul_monomial, ← hr]
    simp [phi]

private lemma torsion_nrel [IsDomain R] (D : R) (hD0 : D ≠ 0)
    (hD : ∀ c : RB, algebraMap R RB D * c ∈ Set.range (algebraMap R RB)) (x : Nrel R RB) :
    ∃ d : XLoc R, d ≠ 0 ∧ d • x ∈ LinearMap.range (Algebra.linearMap (XLoc R) (Nrel R RB)) := by
  obtain ⟨u, f, rfl⟩ := exists_eq_lam_mul R RB x
  refine ⟨algebraMap R[X] (XLoc R) (C D), ?_, ?_⟩
  · have hinj : Function.Injective (algebraMap R[X] (XLoc R)) :=
      IsLocalization.injective (XLoc R) (M := (mC R).primeCompl)
        (Ideal.primeCompl_le_nonZeroDivisors _)
    exact fun h => (Polynomial.C_ne_zero.2 hD0) (hinj (by simpa using h))
  · obtain ⟨g, hg⟩ := exists_phi_eq R RB D hD f
    refine ⟨u * algebraMap R[X] (XLoc R) g, ?_⟩
    simp only [Algebra.linearMap_apply, Algebra.smul_def]
    rw [map_mul, algebraMap_nrel R RB g, hg, map_mul, algebraMap_nrel R RB (C D),
      show phi R RB (C D) = C (algebraMap R RB D) by simp [phi]]
    ring

private lemma exists_maximal_comap_eq [Algebra.IsIntegral R RB] (𝔫 : Ideal RB) [h𝔫 : 𝔫.IsMaximal] :
    ∃ 𝔑 : Ideal (Nrel R RB), 𝔑.IsMaximal ∧ 𝔑.comap (iota R RB) = 𝔫 := by
  classical
  have hcomap : 𝔫.comap (algebraMap R RB) = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal 𝔫)
  let F := FractionRing (RB ⧸ 𝔫)[X]
  haveI : IsDomain (RB ⧸ 𝔫)[X] := inferInstance
  haveI : Nontrivial F := inferInstance
  let g : RB[X] →+* F :=
    (algebraMap (RB ⧸ 𝔫)[X] F).comp (Polynomial.mapRingHom (Ideal.Quotient.mk 𝔫))
  have hg : ∀ y : Submonoid.map (phi R RB) (mC R).primeCompl, IsUnit (g y) := by
    rintro ⟨_, s, hs, rfl⟩
    refine IsUnit.mk0 _ ?_
    intro h0
    have h1 : Polynomial.map (Ideal.Quotient.mk 𝔫) (phi R RB s) = 0 := by
      have := (IsFractionRing.injective (RB ⧸ 𝔫)[X] F)
      refine this ?_
      simpa [g] using h0
    apply hs
    rw [SetLike.mem_coe, Ideal.mem_map_C_iff]
    intro n
    have h2 := congrArg (fun p => Polynomial.coeff p n) h1
    simp only [Polynomial.coeff_map, phi, Polynomial.coe_mapRingHom, Polynomial.coeff_zero] at h2
    rw [← hcomap, Ideal.mem_comap]
    exact Ideal.Quotient.eq_zero_iff_mem.1 h2
  let θ : Nrel R RB →+* F := IsLocalization.lift hg
  have hθ : ∀ f : RB[X], θ (algebraMap RB[X] (Nrel R RB) f) = g f :=
    fun f => IsLocalization.lift_eq hg f
  have hker : Ideal.map (iota R RB) 𝔫 ≤ RingHom.ker θ := by
    rw [Ideal.map_le_iff_le_comap]
    intro c hc
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change θ (algebraMap RB[X] (Nrel R RB) (C c)) = 0
    rw [hθ]
    simp [g, (Ideal.Quotient.eq_zero_iff_mem.2 hc)]
  have hne : RingHom.ker θ ≠ ⊤ := by
    refine (Ideal.ne_top_iff_one _).2 ?_
    rw [RingHom.mem_ker, map_one]
    exact one_ne_zero
  obtain ⟨𝔑, h𝔑, hle⟩ := Ideal.exists_le_maximal _ hne
  refine ⟨𝔑, h𝔑, ?_⟩
  have h1 : 𝔫 ≤ 𝔑.comap (iota R RB) := fun c hc =>
    Ideal.mem_comap.2 (hle (hker (Ideal.mem_map_of_mem _ hc)))
  exact (h𝔫.eq_of_le (Ideal.comap_ne_top _ h𝔑.ne_top) h1).symm

private lemma encard_maximal_le_nrel [Algebra.IsIntegral R RB] :
    {q : Ideal RB | q.IsMaximal}.encard ≤ {q : Ideal (Nrel R RB) | q.IsMaximal}.encard := by
  have hsub : {q : Ideal RB | q.IsMaximal} ⊆
      Ideal.comap (iota R RB) '' {q : Ideal (Nrel R RB) | q.IsMaximal} := by
    intro 𝔫 h𝔫
    obtain ⟨𝔑, h𝔑, h⟩ := @exists_maximal_comap_eq R _ _ RB _ _ _ _ _ 𝔫 h𝔫
    exact ⟨𝔑, h𝔑, h⟩
  exact (Set.encard_le_encard hsub).trans (Set.encard_image_le _ _)

end Rel

section Iso

variable {O : Type u} [CommRing O] [IsLocalRing O] (p : Ideal O) [hp : p.IsPrime]

private instance quotLocalRing : IsLocalRing (O ⧸ p) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective

private lemma mk_mem_maximalIdeal_iff (x : O) :
    Ideal.Quotient.mk p x ∈ maximalIdeal (O ⧸ p) ↔ x ∈ maximalIdeal O := by
  haveI : IsLocalHom (Ideal.Quotient.mk p) := .of_surjective _ Ideal.Quotient.mk_surjective
  exact map_mem_nonunits_iff _ x

private lemma map_mk_notMem (y : O[X]) (hy : y ∉ mC O) :
    Polynomial.map (Ideal.Quotient.mk p) y ∉ mC (O ⧸ p) := by
  intro h
  apply hy
  rw [Ideal.mem_map_C_iff] at h ⊢
  intro n
  exact (mk_mem_maximalIdeal_iff p _).1 (by simpa only [Polynomial.coeff_map] using h n)

private abbrev psi : XLoc O →+* XLoc (O ⧸ p) :=
  IsLocalization.lift (M := (mC O).primeCompl)
    (g := (algebraMap (O ⧸ p)[X] (XLoc (O ⧸ p))).comp (Polynomial.mapRingHom (Ideal.Quotient.mk p)))
    (fun y => IsLocalization.map_units (XLoc (O ⧸ p))
      (⟨Polynomial.map (Ideal.Quotient.mk p) y, map_mk_notMem p y y.2⟩ : (mC (O ⧸ p)).primeCompl))

private lemma psi_algebraMap (f : O[X]) :
    psi p (algebraMap O[X] (XLoc O) f) =
      algebraMap (O ⧸ p)[X] (XLoc (O ⧸ p)) (Polynomial.map (Ideal.Quotient.mk p) f) :=
  IsLocalization.lift_eq _ f

private lemma psi_surjective : Function.Surjective (psi p) := by
  intro z
  obtain ⟨⟨f, s⟩, rfl⟩ := IsLocalization.mk'_surjective (mC (O ⧸ p)).primeCompl z
  obtain ⟨f', rfl⟩ := Polynomial.map_surjective _ Ideal.Quotient.mk_surjective f
  obtain ⟨s', hs'⟩ := Polynomial.map_surjective _ Ideal.Quotient.mk_surjective (s : (O ⧸ p)[X])
  have hs'm : s' ∈ (mC O).primeCompl := by
    intro h
    apply s.2
    rw [SetLike.mem_coe, Ideal.mem_map_C_iff] at h
    rw [← hs', SetLike.mem_coe, Ideal.mem_map_C_iff]
    intro n
    rw [Polynomial.coeff_map]
    exact (mk_mem_maximalIdeal_iff p _).2 (h n)
  refine ⟨IsLocalization.mk' (XLoc O) f' ⟨s', hs'm⟩, ?_⟩
  rw [IsLocalization.eq_mk'_iff_mul_eq]
  have h2 :=
    congrArg (psi p) (IsLocalization.mk'_spec (XLoc O) f' (⟨s', hs'm⟩ : (mC O).primeCompl))
  rwa [map_mul, psi_algebraMap, psi_algebraMap, hs'] at h2

private lemma ker_psi : RingHom.ker (psi p) = Ideal.map (algebraMap O (XLoc O)) p := by
  classical
  apply le_antisymm
  · intro z hz
    obtain ⟨⟨f, s⟩, rfl⟩ := IsLocalization.mk'_surjective (mC O).primeCompl z
    have h2 := congrArg (psi p) (IsLocalization.mk'_spec (XLoc O) f s)
    rw [RingHom.mem_ker] at hz
    rw [map_mul, hz, zero_mul, psi_algebraMap] at h2
    have hinj : Function.Injective (algebraMap (O ⧸ p)[X] (XLoc (O ⧸ p))) :=
      IsLocalization.injective (XLoc (O ⧸ p)) (M := (mC (O ⧸ p)).primeCompl)
        (Ideal.primeCompl_le_nonZeroDivisors _)
    have h3 : Polynomial.map (Ideal.Quotient.mk p) f = 0 := hinj (by rw [← h2, map_zero])
    have h4 : f ∈ Ideal.map (C : O →+* O[X]) p := by
      rw [Ideal.mem_map_C_iff]
      intro n
      have := congrArg (fun q => Polynomial.coeff q n) h3
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at this
      exact Ideal.Quotient.eq_zero_iff_mem.1 this
    have h5 : algebraMap O[X] (XLoc O) f ∈ Ideal.map (algebraMap O (XLoc O)) p := by
      have : Ideal.map (algebraMap O (XLoc O)) p =
          (Ideal.map (C : O →+* O[X]) p).map (algebraMap O[X] (XLoc O)) := by
        rw [Ideal.map_map]; rfl
      rw [this]
      exact Ideal.mem_map_of_mem _ h4
    change IsLocalization.mk' (XLoc O) f s ∈ _
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ h5
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have : algebraMap O (XLoc O) a = algebraMap O[X] (XLoc O) (C a) := rfl
    rw [this, psi_algebraMap]
    simp [(Ideal.Quotient.eq_zero_iff_mem.2 ha)]

end Iso

section Final

private lemma exists_conductor_elt (R : Type u) [CommRing R] [IsDomain R]
    [Module.Finite R (integralClosure R (FractionRing R))] :
    ∃ D : R, D ≠ 0 ∧ ∀ c : integralClosure R (FractionRing R),
      algebraMap R (integralClosure R (FractionRing R)) D * c ∈
        Set.range (algebraMap R (integralClosure R (FractionRing R))) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := integralClosure R (FractionRing R))
  obtain ⟨D, hD⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors R)
    (s.image (fun b : integralClosure R (FractionRing R) => (b : FractionRing R)))
  refine ⟨D, nonZeroDivisors.ne_zero D.2, ?_⟩
  have hgen : ∀ b ∈ s, algebraMap R (integralClosure R (FractionRing R)) D * b ∈
      Set.range (algebraMap R (integralClosure R (FractionRing R))) := by
    intro b hb
    obtain ⟨r, hr⟩ := hD (b : FractionRing R) (Finset.mem_image_of_mem _ hb)
    refine ⟨r, Subtype.ext ?_⟩
    rw [Subalgebra.coe_mul]
    simpa [Algebra.smul_def] using hr
  intro c
  have hc : c ∈ Submodule.span R (s : Set (integralClosure R (FractionRing R))) := by
    rw [hs]; trivial
  induction hc using Submodule.span_induction with
  | mem b hb => exact hgen b hb
  | zero => exact ⟨0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨r, hr⟩ := ha
    obtain ⟨r', hr'⟩ := hb
    exact ⟨r + r', by rw [mul_add, ← hr, ← hr', map_add]⟩
  | smul r a _ ha =>
    obtain ⟨r', hr'⟩ := ha
    exact ⟨r * r', by rw [map_mul, hr', Algebra.smul_def]; ring⟩

end Final

end

end FiniteResidueField

/-- **Finite residue field.** The bound of `encard_maximal_integralClosure_le` when the residue
field of `𝒪` is finite, by base change to `𝒪(x) = 𝒪[x]_{𝔪[x]}`, which is regular of dimension two
with infinite residue field, preserves `sup {s | 𝔭 ≤ 𝔪^s}`, and does not decrease the number of
maximal ideals of the integral closure. -/
private lemma encard_maximal_integralClosure_le_of_finite (O : Type u) [CommRing O]
    [IsLocalRing O] [IsRegularLocalRing O] [Finite (IsLocalRing.ResidueField O)]
    (hdim : ringKrullDim O = 2) (p : Ideal O) [p.IsPrime] (h0 : p ≠ ⊥) (hm : ¬ p.IsMaximal)
    [Module.Finite (O ⧸ p) (integralClosure (O ⧸ p) (FractionRing (O ⧸ p)))] :
    {q : Ideal (integralClosure (O ⧸ p) (FractionRing (O ⧸ p))) | q.IsMaximal}.encard ≤
      ⨆ (s : ℕ) (_ : p ≤ IsLocalRing.maximalIdeal O ^ s), (s : ℕ∞) := by
  classical
  haveI := IsRegularLocalRing.isDomain O
  haveI := isRegularLocalRing_ext O
  haveI : Infinite (IsLocalRing.ResidueField (XLoc O)) := infinite_residueField_ext O
  have hdim' := ringKrullDim_ext O hdim
  haveI hpe : (Ideal.map (algebraMap O (XLoc O)) p).IsPrime := isPrime_map_ext O p
  have hne0 := map_ext_ne_bot O p h0
  have hnm := not_isMaximal_map_ext O p hm
  obtain ⟨t, htu, ht0, hord⟩ :=
    exists_ord_le_multiplicity_of_infinite (XLoc O) hdim' (Ideal.map (algebraMap O (XLoc O)) p)
      hne0 hnm
  let e : (XLoc O ⧸ Ideal.map (algebraMap O (XLoc O)) p) ≃+* XLoc (O ⧸ p) :=
    (Ideal.quotEquivOfEq (ker_psi p).symm).trans
      (RingHom.quotientKerEquivOfSurjective (psi_surjective p))
  have hA1 : ringKrullDim (XLoc (O ⧸ p)) = 1 := by
    rw [← ringKrullDim_eq_of_ringEquiv e]
    exact ringKrullDim_quotient_eq_one hdim' hne0 hnm
  have ha0 : e t ≠ 0 := fun h => ht0 (by simpa using h)
  have ha : e t ∈ IsLocalRing.maximalIdeal (XLoc (O ⧸ p)) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact htu (by simpa using hu.map e.symm)
  have hordeq : Ring.ord (XLoc (O ⧸ p)) (e t) =
      Ring.ord (XLoc O ⧸ Ideal.map (algebraMap O (XLoc O)) p) t := by
    unfold Ring.ord
    rw [Module.quotient_length_eq_of_ringEquiv e (Ideal.span {t}), Ideal.map_span,
      Set.image_singleton]
    rfl
  obtain ⟨D, hD0, hD⟩ := exists_conductor_elt (O ⧸ p)
  letI := algNrel (O ⧸ p) (integralClosure (O ⧸ p) (FractionRing (O ⧸ p)))
  haveI := finite_nrel (O ⧸ p) (integralClosure (O ⧸ p) (FractionRing (O ⧸ p)))
  have h1 := encard_maximal_le_ord_of_finite_extension (A := XLoc (O ⧸ p))
    (N := Nrel (O ⧸ p) (integralClosure (O ⧸ p) (FractionRing (O ⧸ p)))) hA1
    (algebraMap_ext_nrel_injective _ _)
    (torsion_nrel (O ⧸ p) _ D hD0 hD) ha0 ha
  have h2 := encard_maximal_le_nrel (O ⧸ p) (integralClosure (O ⧸ p) (FractionRing (O ⧸ p)))
  have h3 : (⨆ (s : ℕ) (_ : Ideal.map (algebraMap O (XLoc O)) p ≤
      IsLocalRing.maximalIdeal (XLoc O) ^ s), (s : ℕ∞)) =
      ⨆ (s : ℕ) (_ : p ≤ IsLocalRing.maximalIdeal O ^ s), (s : ℕ∞) := by
    simp only [map_ext_le_pow_iff]
  rw [← h3]
  exact h2.trans (h1.trans (hordeq ▸ hord))

/-- **Algebraic step.** In a regular local ring `𝒪` of dimension two, for a prime `𝔭` such that
the integral closure of `𝒪/𝔭` is finite, that integral closure has at most
`sup {s | 𝔭 ≤ 𝔪^s}` maximal ideals. -/
private lemma encard_maximal_integralClosure_le (O : Type u) [CommRing O] [IsLocalRing O]
    [IsRegularLocalRing O] (hdim : ringKrullDim O = 2) (p : Ideal O) [p.IsPrime]
    [Module.Finite (O ⧸ p) (integralClosure (O ⧸ p) (FractionRing (O ⧸ p)))] :
    {q : Ideal (integralClosure (O ⧸ p) (FractionRing (O ⧸ p))) | q.IsMaximal}.encard ≤
      ⨆ (s : ℕ) (_ : p ≤ IsLocalRing.maximalIdeal O ^ s), (s : ℕ∞) := by
  haveI := IsRegularLocalRing.isDomain O
  by_cases h0 : p = ⊥
  · subst h0
    refine le_top.trans (le_of_eq ?_)
    refine (ENat.eq_of_forall_natCast_le_iff fun n => ?_).symm
    simp only [le_top, iff_true]
    exact le_iSup₂_of_le (f := fun (s : ℕ) (_ : (⊥ : Ideal O) ≤ IsLocalRing.maximalIdeal O ^ s) =>
      (s : ℕ∞)) n bot_le le_rfl
  by_cases hm : p.IsMaximal
  · refine (encard_maximal_integralClosure_le_one_of_isField
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient p).1 hm)).trans ?_
    have : p ≤ IsLocalRing.maximalIdeal O ^ 1 := by
      rw [pow_one]; exact IsLocalRing.le_maximalIdeal hm.ne_top
    exact le_iSup₂_of_le (f := fun (s : ℕ) (_ : p ≤ IsLocalRing.maximalIdeal O ^ s) =>
      (s : ℕ∞)) 1 this (by simp)
  rcases finite_or_infinite (IsLocalRing.ResidueField O) with hk | hk
  · exact encard_maximal_integralClosure_le_of_finite O hdim p h0 hm
  · obtain ⟨t, htu, ht0, hle⟩ := exists_ord_le_multiplicity_of_infinite O hdim p h0 hm
    exact (encard_maximal_integralClosure_le_ord (O ⧸ p)
      (ringKrullDim_quotient_eq_one hdim h0 hm) ht0
      ((IsLocalRing.mem_maximalIdeal _).2 htu)).trans hle

/-- The structure map `C ⟶ 𝒪_{Y, y}` of a scheme `Y` locally of finite type over `Spec C` is
essentially of finite type: a localization followed by a stalk map of a morphism locally of
finite type. -/
private theorem essFiniteType_stalkStructureMap {C : Type u} [CommRing C] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of C)) [LocallyOfFiniteType f] (y : Y) :
    ((f.stalkMap y).hom.comp ((Scheme.ΓSpecIso (.of C)).inv ≫
      (Spec (.of C)).presheaf.germ ⊤ (f.base y) (by simp)).hom).EssFiniteType := by
  have := (f.base y).isPrime
  have h0 : (algebraMap C (Localization.AtPrime (f.base y).asIdeal)).EssFiniteType := by
    rw [RingHom.essFiniteType_algebraMap]
    exact Algebra.EssFiniteType.of_isLocalization _ (f.base y).asIdeal.primeCompl
  have hiso : (Spec.stalkIso (.of C) (f.base y)).inv.hom.EssFiniteType :=
    (RingHom.FiniteType.of_surjective _
      (asIso (Spec.stalkIso (.of C) (f.base y)).inv).commRingCatIsoToRingEquiv.surjective
      ).essFiniteType
  have h1 : ((Scheme.ΓSpecIso (.of C)).inv ≫
      (Spec (.of C)).presheaf.germ ⊤ (f.base y) (by simp)).hom.EssFiniteType := by
    have e := congrArg CommRingCat.Hom.hom
      (Spec.algebraMap_stalkIso_inv (R := .of C) (x := f.base y))
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at e
    rw [← e]
    exact h0.comp hiso
  exact h1.comp (LocallyOfFiniteType.stalkMap f y)

/-- **Finiteness of the normalization.** For a scheme `Y` locally of finite type over a field,
the quotient of a local ring of `Y` by a prime has finite integral closure: the local ring is
essentially of finite type over the field, hence excellent, hence Nagata. -/
private lemma finite_integralClosure_stalk_quotient {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (y : Y)
    (p : Ideal (Y.presheaf.stalk y)) [p.IsPrime] :
    Module.Finite (Y.presheaf.stalk y ⧸ p)
      (integralClosure (Y.presheaf.stalk y ⧸ p) (FractionRing (Y.presheaf.stalk y ⧸ p))) := by
  letI : Algebra k (Y.presheaf.stalk y) := RingHom.toAlgebra ((sY.stalkMap y).hom.comp
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).presheaf.germ ⊤ (sY.base y) (by simp)).hom)
  haveI : Algebra.EssFiniteType k (Y.presheaf.stalk y) :=
    RingHom.essFiniteType_algebraMap.1 (essFiniteType_stalkStructureMap sY y)
  have hN : IsNagataRing (Y.presheaf.stalk y) :=
    isNagataRing_of_isQuasiExcellent
      ((isQuasiExcellent_and_isExcellent_of_essFiniteType (R := k) (S := Y.presheaf.stalk y)).2
        (isExcellent_of_standard_classes_and_finiteType.{_, 0}.1 k)).1
  exact (hN.isJapaneseRing_quotient p).finite (FractionRing (Y.presheaf.stalk y ⧸ p))

section LocalizedIntegralClosure

open IsLocalRing

section LocInt

variable {A R K : Type u} [CommRing A] [CommRing R] [Algebra A R] (𝔮 : Ideal A) [𝔮.IsPrime]
  [IsLocalization.AtPrime R 𝔮] [Field K] [Algebra A K] [Algebra R K] [IsScalarTower A R K]

/-- The ring map `Ā → B` from the integral closure of `A` in `K` to that of its localization. -/
private def intClosureMap : integralClosure A K →+* integralClosure R K where
  toFun a := ⟨a, (a.2 : IsIntegral A (a : K)).tower_top⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

private lemma intClosureMap_injective :
    Function.Injective (intClosureMap (A := A) (R := R) (K := K)) :=
  fun a b h => Subtype.ext (congrArg (fun x : integralClosure R K => (x : K)) h)

private lemma intClosureMap_algebraMap (m : A) :
    intClosureMap (R := R) (algebraMap A (integralClosure A K) m) =
      algebraMap R (integralClosure R K) (algebraMap A R m) := by
  apply Subtype.ext
  change algebraMap A K m = algebraMap R K (algebraMap A R m)
  rw [← IsScalarTower.algebraMap_apply]

private lemma exists_mul_eq_intClosureMap (b : integralClosure R K) :
    ∃ m ∈ 𝔮.primeCompl, ∃ a : integralClosure A K,
      algebraMap R (integralClosure R K) (algebraMap A R m) * b = intClosureMap (R := R) a := by
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (R := A) 𝔮.primeCompl
    (Rₘ := R) (S := K) (b : K) b.2
  refine ⟨m, m.2, ⟨m • (b : K), hm⟩, Subtype.ext ?_⟩
  change algebraMap R K (algebraMap A R m) * (b : K) = (m : A) • (b : K)
  rw [← IsScalarTower.algebraMap_apply, Algebra.smul_def]

private lemma mem_map_intClosureMap_iff (Q : Ideal (integralClosure A K))
    (x : integralClosure R K) :
    x ∈ Q.map (intClosureMap (R := R)) ↔ ∃ m ∈ 𝔮.primeCompl, ∃ q ∈ Q,
      algebraMap R (integralClosure R K) (algebraMap A R m) * x = intClosureMap (R := R) q := by
  constructor
  · intro hx
    rw [Ideal.map] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨q, hq, rfl⟩ := hx
      exact ⟨1, 𝔮.primeCompl.one_mem, q, hq, by simp⟩
    | zero => exact ⟨1, 𝔮.primeCompl.one_mem, 0, Q.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨m1, hm1, q1, hq1, e1⟩ := hx
      obtain ⟨m2, hm2, q2, hq2, e2⟩ := hy
      refine ⟨m1 * m2, 𝔮.primeCompl.mul_mem hm1 hm2,
        algebraMap A _ m2 * q1 + algebraMap A _ m1 * q2,
        Q.add_mem (Q.mul_mem_left _ hq1) (Q.mul_mem_left _ hq2), ?_⟩
      simp only [map_add, map_mul, intClosureMap_algebraMap]
      rw [← e1, ← e2]
      ring
    | smul b x _ hx =>
      obtain ⟨m, hm, q, hq, e⟩ := hx
      obtain ⟨mb, hmb, a, eb⟩ := exists_mul_eq_intClosureMap 𝔮 b
      refine ⟨mb * m, 𝔮.primeCompl.mul_mem hmb hm, a * q, Q.mul_mem_left _ hq, ?_⟩
      simp only [map_mul, smul_eq_mul]
      rw [← e, ← eb]
      ring
  · rintro ⟨m, hm, q, hq, e⟩
    have hu : IsUnit (algebraMap R (integralClosure R K) (algebraMap A R m)) :=
      (IsLocalization.map_units R (⟨m, hm⟩ : 𝔮.primeCompl)).map _
    rw [← Ideal.unit_mul_mem_iff_mem _ hu, e]
    exact Ideal.mem_map_of_mem _ hq

private lemma comap_map_intClosureMap (Q : Ideal (integralClosure A K)) [hQ : Q.IsPrime]
    (hQ𝔮 : Q.comap (algebraMap A (integralClosure A K)) = 𝔮) :
    (Q.map (intClosureMap (R := R))).comap (intClosureMap (R := R)) = Q := by
  apply le_antisymm
  · intro a ha
    rw [Ideal.mem_comap, mem_map_intClosureMap_iff 𝔮] at ha
    obtain ⟨m, hm, q, hq, e⟩ := ha
    rw [← intClosureMap_algebraMap, ← map_mul] at e
    have e' := intClosureMap_injective e
    have hmQ : algebraMap A (integralClosure A K) m ∉ Q := fun h => hm (by rwa [← hQ𝔮])
    exact (hQ.mem_or_mem (e' ▸ hq : algebraMap A (integralClosure A K) m * a ∈ Q)).resolve_left
      hmQ
  · exact Ideal.le_comap_map

private lemma isMaximal_map_intClosureMap (Q : Ideal (integralClosure A K)) [hQ : Q.IsPrime]
    (hQ𝔮 : Q.comap (algebraMap A (integralClosure A K)) = 𝔮) :
    (Q.map (intClosureMap (R := R))).IsMaximal := by
  have hcm := comap_map_intClosureMap 𝔮 (R := R) Q hQ𝔮
  have hmQ : ∀ m ∈ 𝔮.primeCompl, algebraMap A (integralClosure A K) m ∉ Q :=
    fun m hm h => hm (by rwa [← hQ𝔮])
  have hne : Q.map (intClosureMap (R := R)) ≠ ⊤ := by
    intro h
    rw [h, Ideal.comap_top] at hcm
    exact hQ.ne_top hcm.symm
  have hprime : (Q.map (intClosureMap (R := R))).IsPrime := by
    refine ⟨hne, fun {x y} hxy => ?_⟩
    obtain ⟨m, hm, q, hq, e⟩ := (mem_map_intClosureMap_iff 𝔮 Q _).1 hxy
    obtain ⟨m1, hm1, a1, e1⟩ := exists_mul_eq_intClosureMap 𝔮 (R := R) x
    obtain ⟨m2, hm2, a2, e2⟩ := exists_mul_eq_intClosureMap 𝔮 (R := R) y
    have key : algebraMap A (integralClosure A K) m * (a1 * a2) ∈ Q := by
      have : intClosureMap (R := R) (algebraMap A (integralClosure A K) m * (a1 * a2)) =
          intClosureMap (R := R) (algebraMap A (integralClosure A K) (m1 * m2) * q) := by
        simp only [map_mul, intClosureMap_algebraMap]
        rw [← e1, ← e2, ← e]
        ring
      rw [intClosureMap_injective this]
      exact Q.mul_mem_left _ hq
    rcases hQ.mem_or_mem ((hQ.mem_or_mem key).resolve_left (hmQ m hm)) with h | h
    · exact Or.inl ((mem_map_intClosureMap_iff 𝔮 Q _).2 ⟨m1, hm1, a1, h, e1⟩)
    · exact Or.inr ((mem_map_intClosureMap_iff 𝔮 Q _).2 ⟨m2, hm2, a2, h, e2⟩)
  haveI := hprime
  haveI : IsLocalRing R := IsLocalization.AtPrime.isLocalRing R 𝔮
  refine Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) _ ?_
  have hle : maximalIdeal R ≤ (Q.map (intClosureMap (R := R))).comap
      (algebraMap R (integralClosure R K)) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal 𝔮 R, Ideal.map_le_iff_le_comap]
    intro q0 hq0
    rw [Ideal.mem_comap, Ideal.mem_comap]
    have : algebraMap R (integralClosure R K) (algebraMap A R q0) =
        intClosureMap (R := R) (algebraMap A (integralClosure A K) q0) :=
      (intClosureMap_algebraMap q0).symm
    rw [this]
    exact Ideal.mem_map_of_mem _ (by rwa [← hQ𝔮] at hq0)
  have hne' : (Q.map (intClosureMap (R := R))).comap (algebraMap R (integralClosure R K)) ≠ ⊤ :=
    Ideal.comap_ne_top _ hne
  rw [Ideal.under_def, ← (maximalIdeal.isMaximal R).eq_of_le hne' hle]
  exact maximalIdeal.isMaximal R

private lemma encard_primes_le_encard_maximal :
    {Q : Ideal (integralClosure A K) | Q.IsPrime ∧
      Q.comap (algebraMap A (integralClosure A K)) = 𝔮}.encard ≤
    {q : Ideal (integralClosure R K) | q.IsMaximal}.encard := by
  refine Set.encard_le_encard_of_injOn (f := Ideal.map (intClosureMap (R := R))) ?_ ?_
  · rintro Q ⟨hQ, hQ𝔮⟩
    exact @isMaximal_map_intClosureMap A R K _ _ _ 𝔮 _ _ _ _ _ _ Q hQ hQ𝔮
  · rintro Q1 ⟨h1, e1⟩ Q2 ⟨h2, e2⟩ h
    have c1 := @comap_map_intClosureMap A R K _ _ _ 𝔮 _ _ _ _ _ _ Q1 h1 e1
    have c2 := @comap_map_intClosureMap A R K _ _ _ 𝔮 _ _ _ _ _ _ Q2 h2 e2
    rw [← c1, ← c2, h]

end LocInt

end LocalizedIntegralClosure

section GeometricStep

open IsLocalRing

section Transport

variable {R R' K K' : Type u} [CommRing R] [CommRing R'] [Field K] [Field K'] [Algebra R K]
  [Algebra R' K'] [IsFractionRing R K] [IsFractionRing R' K']

private lemma encard_maximal_integralClosure_le_of_ringEquiv (e : R ≃+* R') :
    {q : Ideal (integralClosure R K) | q.IsMaximal}.encard ≤
      {q : Ideal (integralClosure R' K') | q.IsMaximal}.encard := by
  let φ : K ≃+* K' := IsFractionRing.ringEquivOfRingEquiv e
  have hφ : ∀ r : R, φ (algebraMap R K r) = algebraMap R' K' (e r) := fun r => by
    simp [φ]
  have hint : ∀ x : K, IsIntegral R x → IsIntegral R' (φ x) := fun x hx =>
    IsIntegral.map_of_comp_eq (e : R →+* R') (φ : K →+* K')
      (by ext r; exact (hφ r).symm) hx
  have hint' : ∀ y : K', IsIntegral R' y → IsIntegral R (φ.symm y) := fun y hy =>
    IsIntegral.map_of_comp_eq (e.symm : R' →+* R) (φ.symm : K' →+* K)
      (by ext r; apply φ.injective; simp [hφ]) hy
  let g : integralClosure R' K' →+* integralClosure R K :=
    { toFun := fun y => ⟨φ.symm y, hint' y y.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun a b => Subtype.ext (map_add _ _ _) }
  have hg : Function.Surjective g := fun x => ⟨⟨φ x, hint x x.2⟩, Subtype.ext (by simp [g])⟩
  refine Set.encard_le_encard_of_injOn (f := Ideal.comap g) ?_ ?_
  · intro q hq
    haveI : q.IsMaximal := hq
    exact Ideal.comap_isMaximal_of_surjective g hg
  · intro a _ b _ h
    exact Ideal.comap_injective_of_surjective g hg h

end Transport

open MMP.Fourfold in
private lemma generic_image_eq {Y : Scheme.{u}} (S : MMP.Mori.PrimeDivisor Y)
    (V : IrreducibleCloseds Y) (P : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S))
    (hP : primeDivisorNormalization S '' P.support = (V : Set Y)) :
    primeDivisorNormalization S P.genericPoint = V.isIrreducible.genericPoint := by
  set f := primeDivisorNormalization S with hf
  have hsupp := AlgebraicGeometry.PrimeDivisor.support_eq_closure P
  have hmem : f P.genericPoint ∈ (V : Set Y) := by
    rw [← hP]
    exact ⟨_, hsupp ▸ subset_closure rfl, rfl⟩
  have h1 : closure {f P.genericPoint} ⊆ (V : Set Y) :=
    closure_minimal (Set.singleton_subset_iff.2 hmem) V.isClosed
  have h2 : (V : Set Y) ⊆ closure {f P.genericPoint} := by
    rw [← hP, hsupp]
    have := image_closure_subset_closure_image (f := f) f.continuous (s := {P.genericPoint})
    rwa [Set.image_singleton] at this
  have h3 : IsGenericPoint (f P.genericPoint) (V : Set Y) := (h1.antisymm h2 : _)
  have h4 : IsGenericPoint V.isIrreducible.genericPoint (V : Set Y) := by
    have := V.isIrreducible.isGenericPoint_genericPoint_closure
    rwa [V.isClosed.closure_eq] at this
  exact h3.eq h4

open Stacks.AlgebraicGeometry.Normalization in
private lemma encard_fibre_le {X : Scheme.{u}} [IsIntegral X]
    (hX : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite) (z : X) :
    {ξ : normalizationScheme X hX | normalization X hX ξ = z}.encard ≤
      {q : Ideal (integralClosure (X.presheaf.stalk z) (FractionRing (X.presheaf.stalk z))) |
        q.IsMaximal}.encard := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ z) isOpen_univ
  let z' : U := ⟨z, hzU⟩
  haveI : Nonempty U := ⟨z'⟩
  let A := Γ(X, U)
  let 𝔮 : Ideal A := (hU.primeIdealOf z').asIdeal
  haveI : 𝔮.IsPrime := (hU.primeIdealOf z').isPrime
  letI : Algebra A (X.presheaf.stalk z) := (X.presheaf.germ U z hzU).hom.toAlgebra
  haveI hloc : IsLocalization.AtPrime (X.presheaf.stalk z) 𝔮 := hU.isLocalization_stalk z'
  let K := FractionRing A
  have hunit : ∀ y : 𝔮.primeCompl, IsUnit (algebraMap A K y) := by
    intro y
    refine isUnit_iff_ne_zero.2 ?_
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective A K)]
    intro h0
    exact y.2 (h0 ▸ 𝔮.zero_mem)
  letI : Algebra (X.presheaf.stalk z) K :=
    (IsLocalization.lift (M := 𝔮.primeCompl) hunit : X.presheaf.stalk z →+* K).toAlgebra
  haveI : IsScalarTower A (X.presheaf.stalk z) K :=
    IsScalarTower.of_algebraMap_eq fun a => (IsLocalization.lift_eq hunit a).symm
  haveI : IsFractionRing (X.presheaf.stalk z) K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔮.primeCompl _ _
  have hC := encard_primes_le_encard_maximal (R := X.presheaf.stalk z) (K := K) 𝔮
  have hT := encard_maximal_integralClosure_le_of_ringEquiv (R := X.presheaf.stalk z)
    (R' := X.presheaf.stalk z) (K := K) (K' := FractionRing (X.presheaf.stalk z))
    (RingEquiv.refl _)
  refine le_trans ?_ (hC.trans hT)
  let e : Spec (CommRingCat.of A) ≅ Scheme.Opens.toScheme U := hU.isoSpec.symm
  let ρ := AlgebraicGeometry.preimageNormalizationIsoSpecIntegralClosure hX U e
  have hcomp := AlgebraicGeometry.preimageNormalizationIsoSpecIntegralClosure_hom_comp hX U e
  have hpt : ∀ (ξ : normalizationScheme X hX) (hξ : normalization X hX ξ = z)
      (hmem : ξ ∈ normalization X hX ⁻¹ᵁ U),
      PrimeSpectrum.comap (algebraMap A (integralClosure A K)) (ρ.hom ⟨ξ, hmem⟩) =
        hU.primeIdealOf z' := by
    intro ξ hξ hmem
    have h1 := congrArg (fun f : Scheme.Opens.toScheme (normalization X hX ⁻¹ᵁ U) ⟶
      Spec (CommRingCat.of A) => f ⟨ξ, hmem⟩) hcomp
    have h2 : (normalization X hX ∣_ U) ⟨ξ, hmem⟩ = z' :=
      Subtype.ext ((morphismRestrict_base_coe _ U _).trans hξ)
    have h3 : Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A K)))
        (ρ.hom ⟨ξ, hmem⟩) = e.inv ((normalization X hX ∣_ U) ⟨ξ, hmem⟩) := h1
    rwa [h2] at h3
  classical
  let Φ : normalizationScheme X hX → Ideal (integralClosure A K) := fun ξ =>
    if h : ξ ∈ normalization X hX ⁻¹ᵁ U then
      (ρ.hom ⟨ξ, h⟩ : PrimeSpectrum (integralClosure A K)).asIdeal else ⊥
  have hmem : ∀ ξ : normalizationScheme X hX, normalization X hX ξ = z →
      ξ ∈ normalization X hX ⁻¹ᵁ U := by
    intro ξ hξ
    change normalization X hX ξ ∈ U
    rw [hξ]
    exact hzU
  refine Set.encard_le_encard_of_injOn (f := Φ) ?_ ?_
  · intro ξ hξ
    have hξ' : normalization X hX ξ = z := hξ
    have hm := hmem ξ hξ'
    have hΦ : Φ ξ = (ρ.hom ⟨ξ, hm⟩ : PrimeSpectrum (integralClosure A K)).asIdeal := dif_pos hm
    rw [Set.mem_setOf_eq, hΦ]
    exact ⟨(ρ.hom ⟨ξ, hm⟩ : PrimeSpectrum (integralClosure A K)).isPrime,
      congrArg PrimeSpectrum.asIdeal (hpt ξ hξ' hm)⟩
  · intro ξ1 h1 ξ2 h2 h
    have h1' : normalization X hX ξ1 = z := h1
    have h2' : normalization X hX ξ2 = z := h2
    have hm1 := hmem ξ1 h1'
    have hm2 := hmem ξ2 h2'
    have e1 : Φ ξ1 = (ρ.hom ⟨ξ1, hm1⟩ : PrimeSpectrum (integralClosure A K)).asIdeal := dif_pos hm1
    have e2 : Φ ξ2 = (ρ.hom ⟨ξ2, hm2⟩ : PrimeSpectrum (integralClosure A K)).asIdeal := dif_pos hm2
    have : ρ.hom ⟨ξ1, hm1⟩ = ρ.hom ⟨ξ2, hm2⟩ := PrimeSpectrum.ext (by rw [← e1, ← e2]; exact h)
    have := (Scheme.Hom.isOpenEmbedding ρ.hom).injective this
    exact congrArg Subtype.val this

open MMP.Fourfold in
private lemma encard_branches_le_encard_maximal {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (V : IrreducibleCloseds Y)
    (S : MMP.Mori.PrimeDivisor Y) :
    {P : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S) |
        primeDivisorNormalization S '' P.support = (V : Set Y)}.encard ≤
      {q : Ideal (integralClosure
          (Y.presheaf.stalk V.isIrreducible.genericPoint ⧸
            S.idealSheaf.stalkIdeal V.isIrreducible.genericPoint)
          (FractionRing (Y.presheaf.stalk V.isIrreducible.genericPoint ⧸
            S.idealSheaf.stalkIdeal V.isIrreducible.genericPoint))) | q.IsMaximal}.encard := by
  classical
  haveI := S.integral
  rcases Set.eq_empty_or_nonempty {P : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S) |
        primeDivisorNormalization S '' P.support = (V : Set Y)} with h | ⟨P0, hP0⟩
  · rw [h]; simp
  have hν := generic_image_eq S V P0 hP0
  have hη : V.isIrreducible.genericPoint ∈ S.support :=
    hν ▸ range_primeDivisorNormalization_subset S ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : S.idealSheaf.subscheme,
      S.idealSheaf.subschemeι z = V.isIrreducible.genericPoint := by
    have : V.isIrreducible.genericPoint ∈ Set.range S.idealSheaf.subschemeι := by
      rwa [S.idealSheaf.range_subschemeι]
    exact this
  have hX : ∀ U : S.idealSheaf.subscheme.Opens, IsCompact (U : Set S.idealSheaf.subscheme) →
      (irreducibleComponents (U : Set S.idealSheaf.subscheme)).Finite :=
    fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U
  have hfibre : ∀ P ∈ {P : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S) |
        primeDivisorNormalization S '' P.support = (V : Set Y)},
      Stacks.AlgebraicGeometry.Normalization.normalization S.idealSheaf.subscheme hX
        P.genericPoint = z := by
    intro P hP
    have h1 := generic_image_eq S V P hP
    apply S.idealSheaf.subschemeι.isClosedEmbedding.injective
    rw [hz, ← h1]
    rfl
  have hinj := Set.encard_le_encard_of_injOn
    (s := {P : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S) |
        primeDivisorNormalization S '' P.support = (V : Set Y)})
    (t := {ξ : Stacks.AlgebraicGeometry.Normalization.normalizationScheme
        S.idealSheaf.subscheme hX | Stacks.AlgebraicGeometry.Normalization.normalization
        S.idealSheaf.subscheme hX ξ = z})
    (f := fun P => P.genericPoint) (fun P hP => hfibre P hP)
    (fun P _ P' _ h => AlgebraicGeometry.PrimeDivisor.genericPoint_injective h)
  refine hinj.trans ((encard_fibre_le hX z).trans ?_)
  generalize V.isIrreducible.genericPoint = η at hz ⊢
  subst hz
  have hsurj : Function.Surjective (S.idealSheaf.subschemeι.stalkMap z).hom :=
    S.idealSheaf.subschemeι.stalkMap_surjective z
  have hker : RingHom.ker (S.idealSheaf.subschemeι.stalkMap z).hom =
      S.idealSheaf.stalkIdeal (S.idealSheaf.subschemeι z) :=
    S.idealSheaf.ker_stalkMap_subschemeι z
  let e : (Y.presheaf.stalk (S.idealSheaf.subschemeι z) ⧸
      S.idealSheaf.stalkIdeal (S.idealSheaf.subschemeι z)) ≃+*
      S.idealSheaf.subscheme.presheaf.stalk z :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  haveI : IsDomain (Y.presheaf.stalk (S.idealSheaf.subschemeι z) ⧸
      S.idealSheaf.stalkIdeal (S.idealSheaf.subschemeι z)) :=
    Function.Injective.isDomain e.toRingHom e.injective
  exact encard_maximal_integralClosure_le_of_ringEquiv e.symm

end GeometricStep

/-- The ideal of a prime divisor at a point is prime, or the unit ideal off the divisor. -/
private lemma stalkIdeal_isPrime_or_eq_top {Y : Scheme.{u}} (V : IrreducibleCloseds Y)
    (S : MMP.Mori.PrimeDivisor Y) :
    (S.idealSheaf.stalkIdeal V.isIrreducible.genericPoint).IsPrime ∨
      S.idealSheaf.stalkIdeal V.isIrreducible.genericPoint = ⊤ := by
  haveI := S.integral
  by_cases hx : V.isIrreducible.genericPoint ∈ S.idealSheaf.support
  · left
    obtain ⟨z, hz⟩ : V.isIrreducible.genericPoint ∈ Set.range S.idealSheaf.subschemeι := by
      rwa [S.idealSheaf.range_subschemeι]
    rw [← hz, ← S.idealSheaf.ker_stalkMap_subschemeι z]
    exact RingHom.ker_isPrime _
  · exact Or.inr (S.idealSheaf.stalkIdeal_eq_top_of_notMem_support hx)

/-- Over the zero ring `O/⊤` there are no maximal ideals of the integral closure. -/
private lemma encard_maximal_integralClosure_eq_zero_of_eq_top {O : Type u} [CommRing O]
    {p : Ideal O} (hp : p = ⊤) :
    {q : Ideal (integralClosure (O ⧸ p) (FractionRing (O ⧸ p))) | q.IsMaximal}.encard = 0 := by
  subst hp
  have : Subsingleton (FractionRing (O ⧸ (⊤ : Ideal O))) :=
    ⟨fun a b => by
      rw [← one_mul a, ← one_mul b, ← map_one (algebraMap (O ⧸ (⊤ : Ideal O)) _),
        Subsingleton.elim (1 : O ⧸ (⊤ : Ideal O)) 0]
      simp⟩
  rw [Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem]
  intro q hq
  exact hq.ne_top (Subsingleton.elim _ _)

end BranchMultiplicity

open BranchMultiplicity in
/-- **Branch multiplicity inequality.** Let `Y` be locally of finite type over a field `k`, `V`
an irreducible closed subset of `Y` with `𝒪_{Y,η_V}` a regular local ring of dimension two, and
`S` a prime divisor of `Y`. Then the number of prime divisors `P` of the normalization `S^ν` with
`ν(P) = V` is at most the multiplicity `mult_V S` of `S` along `V`. -/
@[mmp "lem_oai4_c2_branch_multiplicity"]
public theorem encard_branches_le_multiplicityAlong {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (V : IrreducibleCloseds Y)
    (hreg : IsRegularLocalRing (Y.presheaf.stalk V.isIrreducible.genericPoint))
    (hdim : ringKrullDim (Y.presheaf.stalk V.isIrreducible.genericPoint) = 2)
    (S : MMP.Mori.PrimeDivisor Y) :
    {P : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S) |
        primeDivisorNormalization S '' P.support = (V : Set Y)}.encard ≤
      S.multiplicityAlong V := by
  refine (encard_branches_le_encard_maximal sY V S).trans ?_
  rcases stalkIdeal_isPrime_or_eq_top V S with hp | h
  · haveI := finite_integralClosure_stalk_quotient sY _
      (S.idealSheaf.stalkIdeal V.isIrreducible.genericPoint)
    exact encard_maximal_integralClosure_le _ hdim _
  · simp [encard_maximal_integralClosure_eq_zero_of_eq_top h]

/-! ### Relative numerical triviality near the generic point of a curve -/

section NumericalTriviality

open MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

variable {k : Type u} [Field k] {Y' Y : Scheme.{u}}
  {sY' : Y' ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
  [IsLocallyNoetherian Y'] [IsNormal Y'] [QuasiCompact sY']

namespace RelativeNumericalTriviality

section tower

open Opposite

attribute [local instance] HasDerivedCategory.standard

private theorem ring_map_tower {F F' : Type u} [Field F] [Field F'] (φ : F →+* F')
    {C : Scheme.{u}} (s' : C ⟶ Spec (.of F')) :
    ((Scheme.ΓSpecIso (.of F)).inv ≫
      (s' ≫ Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ (by simp)).hom =
      (((Scheme.ΓSpecIso (.of F')).inv ≫ s'.appLE ⊤ ⊤ (by simp)).hom).comp φ := by
  have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)
  have h2 : (s' ≫ Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ (by simp) =
      (Spec.map (CommRingCat.ofHom φ)).appTop ≫ s'.appLE ⊤ ⊤ (by simp) := by
    simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
    rfl
  rw [h2, ← Category.assoc, ← this]
  rfl

private theorem finrank_cohomologyOverField_tower {F F' : Type u} [Field F] [Field F']
    [Algebra F F'] [Module.Finite F F']
    {C : Scheme.{u}} (s' : C ⟶ Spec (.of F')) (M : C.Modules) (n : ℕ) :
    Module.finrank F (cohomologyOverField F
      (s' ≫ Spec.map (CommRingCat.ofHom (algebraMap F F'))) M n) =
      Module.finrank F F' * Module.finrank F' (cohomologyOverField F' s' M n) := by
  set V := (SheafOfModules.evaluation C.ringCatSheaf (op (⊤ : C.Opens))).rightDerived n |>.obj M
  let ρ' := ((Scheme.ΓSpecIso (.of F')).inv ≫ s'.appLE ⊤ ⊤ (by simp)).hom
  let e := ModuleCat.restrictScalarsComp'App (algebraMap F F') ρ' _
    (ring_map_tower (algebraMap F F') s') V
  have h1 := LinearEquiv.finrank_eq e.toLinearEquiv
  refine h1.trans ?_
  let W := (ModuleCat.restrictScalars ρ').obj V
  letI : Module F W := Module.compHom W (algebraMap F F')
  haveI : IsScalarTower F F' W := IsScalarTower.of_algebraMap_smul fun r x => rfl
  exact (Module.finrank_mul_finrank F F' W).symm

private theorem invertibleCurveDegree_tower {F F' : Type u} [Field F] [Field F']
    [Algebra F F'] [Module.Finite F F']
    {C : Scheme.{u}} (s' : C ⟶ Spec (.of F')) [IsProper s']
    [IsProper (s' ≫ Spec.map (CommRingCat.ofHom (algebraMap F F')))]
    (hdim : topologicalKrullDim C ≤ 1) (N : C.Modules)
    [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 N] :
    invertibleCurveDegree F (s' ≫ Spec.map (CommRingCat.ofHom (algebraMap F F'))) hdim N =
      (Module.finrank F F' : ℤ) * invertibleCurveDegree F' s' hdim N := by
  have key : ∀ M : C.Modules,
      ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank F (cohomologyOverField F
        (s' ≫ Spec.map (CommRingCat.ofHom (algebraMap F F'))) M n) : ℤ) =
      (Module.finrank F F' : ℤ) * ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
        (Module.finrank F' (cohomologyOverField F' s' M n) : ℤ) := fun M => by
    rw [mul_finsum]
    refine finsum_congr fun n => ?_
    rw [finrank_cohomologyOverField_tower]
    push_cast
    ring
  unfold invertibleCurveDegree
  rw [key N, key (SheafOfModules.unit C.ringCatSheaf)]
  ring

end tower

private theorem topologicalKrullDim_curveSubschemeAt_eq {A B : Scheme.{u}} (u : A ⟶ B)
    [IsClosedImmersion u] (a : A) :
    topologicalKrullDim (curveSubschemeAt a) = topologicalKrullDim (curveSubschemeAt (u a)) := by
  let e1 : curveSubschemeAt a ⟶ B := curveSubschemeAtι a ≫ u
  have h1 : Topology.IsEmbedding e1 := by
    have : IsClosedImmersion e1 := inferInstance
    exact e1.isEmbedding
  have h2 : Topology.IsEmbedding (curveSubschemeAtι (u a)) := (curveSubschemeAtι (u a)).isEmbedding
  have hu : Topology.IsClosedEmbedding u := u.isClosedEmbedding
  have hr : Set.range e1 = Set.range (curveSubschemeAtι (u a)) := by
    rw [range_curveSubschemeAtι]
    have : Set.range e1 = u '' Set.range (curveSubschemeAtι a) := by
      rw [← Set.range_comp]; rfl
    rw [this, range_curveSubschemeAtι, ← hu.closure_image_eq, Set.image_singleton]
  let eq1 := h1.toHomeomorph
  let eq2 := h2.toHomeomorph
  let eq3 : Set.range e1 ≃ₜ Set.range (curveSubschemeAtι (u a)) := Homeomorph.setCongr hr
  exact (eq1.trans (eq3.trans eq2.symm)).isHomeomorph.topologicalKrullDim_eq _

section DegreeOnComponents

open MMP MMP.Flips

section helpers

open TopologicalSpace MMP.Mori TensorProduct

variable {k : Type*} [Field k] {X : Scheme} {sX : X ⟶ Spec (.of k)}

private theorem not_const_of_isCurveNormalization (C : Mori.ProperCurve sX) {C' : Scheme}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) :
    ¬ ∃ y : C.scheme, ∀ x : C', ν.base x = y := by
  rintro ⟨y, hy⟩
  have := hν.isFinite
  have : IsDominant ν := hν.isBirationalMorphism.isDominant
  have huniv : Set.range ν = Set.univ := by
    rw [← ν.isClosedMap.isClosed_range.closure_eq, ν.denseRange.closure_range]
  have : Subsingleton C.scheme := ⟨fun a b => by
    obtain ⟨x, rfl⟩ := huniv.ge (Set.mem_univ a)
    obtain ⟨x', rfl⟩ := huniv.ge (Set.mem_univ b)
    exact (hy x).trans (hy x').symm⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
  rw [C.dim_eq] at h0
  exact absurd h0 (by decide)

private theorem isVariety_of_isProper {Y : Scheme} [IsIntegral Y] (f : Y ⟶ Spec (.of k))
    [hp : IsProper f] : AlgebraicGeometry.IsVariety k f :=
  { toIsIntegral := ‹_›, toIsSeparated := hp.toIsSeparated,
    toLocallyOfFiniteType := hp.toLocallyOfFiniteType, toQuasiCompact := inferInstance }

private theorem isCurve_comp (C : Mori.ProperCurve sX) {C' : Scheme} {ν : C' ⟶ C.scheme}
    (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1) :
    AlgebraicGeometry.IsCurve k (ν ≫ C.ι ≫ sX) := by
  have := hν.isFinite
  have := hν.isIntegral
  have := isVariety_of_isProper (ν ≫ C.ι ≫ sX)
  refine ⟨le_antisymm hdim ?_⟩
  by_contra! h
  refine not_const_of_isCurveNormalization C hν ⟨ν.base (genericPoint C'), fun x => ?_⟩
  by_cases hx : x = genericPoint C'
  · rw [hx]
  · exact absurd (one_le_topologicalKrullDim_of_specializes_of_ne
      (genericPoint_specializes x) (Ne.symm hx)) (not_le.mpr h)

private theorem isCurve_ι (C : Mori.ProperCurve sX) :
    AlgebraicGeometry.IsCurve k (C.ι ≫ sX) := by
  have := isVariety_of_isProper (C.ι ≫ sX)
  exact ⟨C.dim_eq⟩

private theorem degreeOver_eq_one_of_isBirationalMorphism {Y Z : Scheme} [IsIntegral Y]
    [IsIntegral Z] (f : Y ⟶ Z) (hf : IsBirationalMorphism f) [IsDominant f]
    [LocallyOfFiniteType f] : degreeOver f = 1 := by
  let := (functionFieldMap f).toAlgebra
  have heq : functionFieldMap f = dominantFunctionFieldMap f :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target f (genericPoint Y) (map_genericPoint_of_isDominant f))).symm
  rw [degreeOver_eq_finrank f heq]
  let e := AlgEquiv.ofBijective (Algebra.ofId Z.functionField Y.functionField)
    (hf.functionFieldMap_bijective)
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]

private theorem degreeOn_normalization (C : Mori.ProperCurve sX) {C' : Scheme}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1)
    [IsProper ((ν ≫ C.ι) ≫ sX)] (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    Mori.degreeOn k sX (ν ≫ C.ι) hdim M = Mori.degreeOn k sX C.ι C.dim_le M := by
  have := hν.isFinite
  have := hν.isIntegral
  have : IsProper (ν ≫ C.ι ≫ sX) := by rw [← Category.assoc]; infer_instance
  have hc := isCurve_comp C hν hdim
  have hc2 := isCurve_ι C
  have : IsDominant ν := hν.isBirationalMorphism.isDominant
  have key := curveDegree_pullback_eq_degreeOver_mul k (ν ≫ C.ι ≫ sX) (C.ι ≫ sX) ν rfl
    (not_const_of_isCurveNormalization C hν) ((Scheme.Modules.pullback C.ι).obj M) 1
  rw [degreeOver_eq_one_of_isBirationalMorphism ν hν.isBirationalMorphism, Nat.cast_one,
    one_mul] at key
  let e : (Scheme.Modules.pullback (ν ≫ C.ι)).obj M ≅
      (Scheme.Modules.pullback ν).obj ((Scheme.Modules.pullback C.ι).obj M) :=
    ((Scheme.Modules.pullbackComp ν C.ι).app M).symm
  rw [Mori.degreeOn, Mori.degreeOn,
    invertibleCurveDegree_congr_structure (Category.assoc ν C.ι sX) hdim,
    invertibleCurveDegree_eq_of_iso k _ hdim e,
    invertibleCurveDegree_eq_curveDegree_one, invertibleCurveDegree_eq_curveDegree_one]
  exact key

end helpers

section dimComponents

open TopologicalSpace MMP.Mori

variable {X : Scheme.{u}}

private theorem support_eq_closure_genericPt (Z : X.IdealSheafData) [IsIntegral Z.subscheme] :
    (Z.support : Set X) = closure {Z.subschemeι (genericPoint Z.subscheme)} := by
  have h := (genericPoint_spec Z.subscheme).image Z.subschemeι.continuous
  rw [Set.image_univ, Z.subschemeι.isClosedEmbedding.isClosed_range.closure_eq,
    Scheme.IdealSheafData.range_subschemeι] at h
  exact h.symm

private theorem eq_vanishingIdeal_closure_genericPt (Z : X.IdealSheafData)
    [IsIntegral Z.subscheme] :
    Z = Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({Z.subschemeι (genericPoint Z.subscheme)} : Set X)) := by
  have hc : Closeds.closure ({Z.subschemeι (genericPoint Z.subscheme)} : Set X) = Z.support :=
    Closeds.ext (support_eq_closure_genericPt Z).symm
  rw [hc]
  exact Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme Z Z.support rfl

private theorem false_of_specializes_of_specializes {X : Scheme.{u}}
    (hX : topologicalKrullDim X ≤ 1) {a b c : X}
    (hab : a ⤳ b) (hbc : b ⤳ c) (hab' : a ≠ b) (hbc' : b ≠ c) : False := by
  have h := two_le_topologicalKrullDim_of_specializes (S := (Set.univ : Set X))
    (Set.mem_univ a) (Set.mem_univ b) (Set.mem_univ c) hab hbc hab' hbc'
  have := (h.trans (topologicalKrullDim_subspace_le X Set.univ)).trans hX
  exact absurd this (by norm_num)

private theorem exists_ne_genericPoint {Z : Scheme.{u}} [IsIntegral Z]
    (hZ : topologicalKrullDim Z = 1) : ∃ z : Z, z ≠ genericPoint Z := by
  by_contra! h
  have : Subsingleton Z := ⟨fun a b => (h a).trans (h b).symm⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology Z
  rw [hZ] at h0
  exact absurd h0 (by decide)

private theorem closure_genericPt_mem_irreducibleComponents (hX : topologicalKrullDim X ≤ 1)
    (Z : X.IdealSheafData) [IsIntegral Z.subscheme] (hZ : topologicalKrullDim Z.subscheme = 1) :
    closure {Z.subschemeι (genericPoint Z.subscheme)} ∈ irreducibleComponents X := by
  obtain ⟨z, hz⟩ := exists_ne_genericPoint hZ
  set p := Z.subschemeι (genericPoint Z.subscheme) with hp
  have hpq : p ⤳ Z.subschemeι z := ((genericPoint_specializes z).map Z.subschemeι.continuous)
  have hpq' : p ≠ Z.subschemeι z := fun h =>
    hz (Z.subschemeι.isClosedEmbedding.injective h).symm
  refine ⟨isIrreducible_singleton.closure, fun T hT hle => ?_⟩
  have hgen := hT.isGenericPoint_genericPoint_closure
  set t := hT.genericPoint
  have hpt : p ∈ closure T := subset_closure (hle (subset_closure rfl))
  have htp : t ⤳ p := by
    rwa [specializes_iff_mem_closure, hgen.def]
  by_cases h : t = p
  · rw [h] at hgen
    intro x hx
    have := subset_closure hx
    rw [← hgen.def] at this
    exact this
  · exact (false_of_specializes_of_specializes hX htp hpq h hpq').elim

private noncomputable abbrev pushforwardUnitModule (X : Scheme.{u}) : X.Modules :=
  (Scheme.Modules.pushforward (𝟙 X)).obj (Stacks.Ample.unitModule X)

private theorem supp_pushforwardUnitModule :
    SheafOfModules.supp (pushforwardUnitModule X) = Set.univ := by
  rw [pushforwardUnitModule, Stacks.Chow.supp_pushforwardStructureSheaf]
  simp

private theorem sheafMultiplicity_pushforwardUnitModule (x : X) :
    Stacks.Chow.sheafMultiplicity (pushforwardUnitModule X) x =
      ((Module.length (X.presheaf.stalk x) (X.presheaf.stalk x)).toNat : ℤ) := by
  have h := Stacks.Chow.length_stalk_pushforwardStructureSheaf (𝟙 X) x
    (Topology.IsInducing.id)
  unfold Stacks.Chow.sheafMultiplicity
  rw [Scheme.Hom.stalkMap_id] at h
  congr 2

section toW

variable {K : Type u} [Field K] (sX : X ⟶ Spec (.of K))

private noncomputable def toW (C : Mori.ProperCurve sX) :
    DimIntegralSubscheme (pushforwardUnitModule X) 1 :=
  ⟨Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({C.point} : Set X)),
    Mori.ProperCurve.isIntegral_scheme C,
    by rw [supp_pushforwardUnitModule]; exact Set.subset_univ _,
    by simpa using C.dim_eq⟩

private theorem genericPt_toW (C : Mori.ProperCurve sX) : (toW sX C).genericPt = C.point := by
  have := (toW sX C).2.1
  have h1 := support_eq_closure_genericPt (toW sX C).1
  have h2 : ((toW sX C).1.support : Set X) = closure {C.point} := by
    simp [toW]
  have h3 : closure {(toW sX C).genericPt} = closure {C.point} := by
    rw [← h2]; exact h1.symm
  exact ((inseparable_iff_closure_eq).mpr h3).eq

private theorem toW_injective : Function.Injective (toW sX) := by
  intro C C' h
  have h1 : (toW sX C).genericPt = (toW sX C').genericPt := by rw [h]
  rw [genericPt_toW, genericPt_toW] at h1
  exact Mori.ProperCurve.ext h1

private theorem exists_properCurve (hX : topologicalKrullDim X ≤ 1) [IsProper sX]
    (W : DimIntegralSubscheme (pushforwardUnitModule X) 1) :
    ∃ C : {C : Mori.ProperCurve sX // closure {C.point} ∈ irreducibleComponents X},
      toW sX C.1 = W := by
  have hint := W.2.1
  have hW : W.1 = Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({W.genericPt} : Set X)) := eq_vanishingIdeal_closure_genericPt W.1
  have hdim : topologicalKrullDim W.1.subscheme = 1 := by simpa using W.2.2.2
  have hpc : Mori.IsProperCurve sX W.genericPt := by
    refine ⟨?_, ?_⟩
    · change topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({W.genericPt} : Set X))).subscheme = 1
      rwa [← hW]
    · change IsProper ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({W.genericPt} : Set X))).subschemeι ≫ sX)
      rw [← hW]; infer_instance
  exact ⟨⟨⟨W.genericPt, hpc⟩, closure_genericPt_mem_irreducibleComponents hX W.1 hdim⟩,
    Subtype.ext hW.symm⟩

end toW

private theorem finsum_dimIntegral_eq {K : Type u} [Field K]
    (sX : X ⟶ Spec (.of K)) [IsProper sX] (hX : topologicalKrullDim X ≤ 1)
    (M : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    invertibleCurveDegree K sX hX M =
      ∑ᶠ W : DimIntegralSubscheme ((Scheme.Modules.pushforward (𝟙 X)).obj
          (Stacks.Ample.unitModule X)) 1,
        Stacks.Chow.sheafMultiplicity ((Scheme.Modules.pushforward (𝟙 X)).obj
          (Stacks.Ample.unitModule X)) W.genericPt *
        invertibleCurveDegree K (W.1.subschemeι ≫ sX) W.topologicalKrullDim_le
          ((Scheme.Modules.pullback W.1.subschemeι).obj M) := by
  have h := intersectionNumber_eq_sum_dimComponents K sX (𝟙 X) 1 hX (fun _ => M)
  rw [intersectionNumber_one_eq_invertibleCurveDegree] at h
  have e := invertibleCurveDegree_congr_structure (Category.id_comp sX) hX
    (L := (Scheme.Modules.pullback (𝟙 X)).obj M)
  rw [e] at h
  have e2 : (Scheme.Modules.pullback (𝟙 X)).obj M ≅ M := (Scheme.Modules.pullbackId X).app M
  rw [← invertibleCurveDegree_eq_of_iso K sX hX e2]
  rw [h]
  refine finsum_congr fun W => ?_
  exact congrArg _ (intersectionNumber_one_eq_invertibleCurveDegree K sX _ _ M)

end dimComponents

/-- **Degree dictionary on a proper curve.** Let `X` be proper over a field `K`, of dimension at
most one, and `M` invertible on `X`. For every choice of normalizations `ν_C : C̃ ⟶ C` of the
one-dimensional irreducible components `C` of `X`,
`∑_C m_C deg(ν_C^* M) = χ(X, M) - χ(X, 𝒪_X)`, where `m_C` is the length of `𝒪_{X,η_C}`. -/
private theorem finsum_length_mul_degreeOn_eq_invertibleCurveDegree {K : Type*} [Field K]
    {X : Scheme} (sX : X ⟶ Spec (.of K)) [IsProper sX] (hX : topologicalKrullDim X ≤ 1)
    (M : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    (N : {C : Mori.ProperCurve sX // closure {C.point} ∈ irreducibleComponents X} → Scheme)
    (ν : ∀ C, N C ⟶ C.1.scheme) (hν : ∀ C, IsCurveNormalization (ν C))
    (hNdim : ∀ C, topologicalKrullDim (N C) ≤ 1) :
    ∑ᶠ C, ((Module.length (X.presheaf.stalk C.1.point)
        (X.presheaf.stalk C.1.point)).toNat : ℤ) *
      (haveI := (hν C).isFinite
       haveI : IsProper ((ν C ≫ C.1.ι) ≫ sX) := by
         rw [Category.assoc]; infer_instance
       Mori.degreeOn K sX (ν C ≫ C.1.ι) (hNdim C) M) =
      invertibleCurveDegree K sX hX M := by
  classical
  rw [finsum_dimIntegral_eq sX hX M]
  let e := Equiv.ofBijective
    (fun C : {C : Mori.ProperCurve sX // closure {C.point} ∈ irreducibleComponents X} =>
      toW sX C.1) ⟨fun C C' h => Subtype.ext (toW_injective sX h),
      fun W => exists_properCurve sX hX W⟩
  refine Eq.trans (finsum_congr fun C => ?_) (finsum_comp_equiv e)
  change _ = Stacks.Chow.sheafMultiplicity (pushforwardUnitModule X) (toW sX C.1).genericPt * _
  rw [sheafMultiplicity_pushforwardUnitModule, genericPt_toW]
  congr 1
  have := (hν C).isFinite
  have : IsProper ((ν C ≫ C.1.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  exact degreeOn_normalization C.1 (hν C) (hNdim C) M

end DegreeOnComponents

section family

open MMP MMP.Flips

private theorem exists_curveNormalization {K : Type u} [Field K] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of K)) (C : MMP.Mori.ProperCurve sX) :
    ∃ (N : Scheme.{u}) (ν : N ⟶ C.scheme) (_ : IsCurveNormalization ν),
      topologicalKrullDim N ≤ 1 := by
  let p := C.ι ≫ sX
  haveI : AlgebraicGeometry.IsCurve K p := C.isCurve
  have hX := finite_irreducibleComponents_of_locallyOfFiniteType K p
  haveI hvar : AlgebraicGeometry.IsVariety K (normalizationOverField K p ≫ p) :=
    isVariety_normalizationOverField K p
  haveI : IsIntegral (normalizationSchemeOverField K p) := hvar.toIsIntegral
  haveI : IsFinite (normalizationOverField K p) := isFinite_normalizationOverField K p
  have hν : IsCurveNormalization (normalizationOverField K p) :=
    { isIntegral := inferInstance
      isNormal := Scheme.isNormal_normalizationScheme C.scheme hX
      isFinite := inferInstance
      isBirationalMorphism := by
        haveI : Finite (irreducibleComponents (normalizationSchemeOverField K p)) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        haveI : Finite (irreducibleComponents C.scheme) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        obtain ⟨U, V, hUV, hU, hV, hiso⟩ := exists_dense_opens_isIso_resLE_of_isBirational
          (normalizationOverField K p) (Scheme.isBirational_normalization C.scheme hX)
          (Or.inl ⟨inferInstance, inferInstance⟩)
        exact isBirationalMorphism_of_isIso_resLE _ U V hU.nonempty hV.nonempty hUV hiso }
  exact ⟨_, _, hν, (topologicalKrullDim_normalizationSchemeOverField K p).le.trans C.dim_le⟩

/-- Positivity of the multiplicity of a component: the stalk at the generic point of an
irreducible component of a locally noetherian scheme has finite positive length. -/
private theorem length_toNat_pos_of_mem_irreducibleComponents {X : Scheme.{u}}
    [IsLocallyNoetherian X] (x : X) (hx : closure ({x} : Set X) ∈ irreducibleComponents X) :
    0 < (Module.length (X.presheaf.stalk x) (X.presheaf.stalk x)).toNat := by
  have hdim := Stacks.Chow.ringKrullDim_stalk_eq_zero_of_mem_genericPoints (W := X) ⟨x, hx⟩
  have hk : Ring.KrullDimLE 0 (X.presheaf.stalk x) := by
    rw [Ring.krullDimLE_iff, hdim]; rfl
  have : IsArtinianRing (X.presheaf.stalk x) :=
    isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.mpr ⟨inferInstance, hk⟩
  have hne : Module.length (X.presheaf.stalk x) (X.presheaf.stalk x) ≠ ⊤ := Module.length_ne_top
  have hpos : 0 < Module.length (X.presheaf.stalk x) (X.presheaf.stalk x) := Module.length_pos
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
  rw [← hn] at hpos ⊢
  rw [ENat.toNat_coe]
  exact_mod_cast hpos

private theorem eq_of_mem_irreducibleComponents_of_preirreducible {X : Scheme.{u}}
    [PreirreducibleSpace X] {a b : X} (ha : closure ({a} : Set X) ∈ irreducibleComponents X)
    (hb : closure ({b} : Set X) ∈ irreducibleComponents X) : a = b := by
  have key : ∀ {c : X}, closure ({c} : Set X) ∈ irreducibleComponents X →
      closure ({c} : Set X) = Set.univ := fun {c} hc => by
    have hirr : IsIrreducible (Set.univ : Set X) :=
      ⟨⟨c, trivial⟩, PreirreducibleSpace.isPreirreducible_univ⟩
    exact Set.eq_univ_of_univ_subset (hc.2 hirr (Set.subset_univ _))
  exact ((inseparable_iff_closure_eq).mpr ((key ha).trans (key hb).symm)).eq

/-- If `M` has degree zero on every proper curve of `X`, then it has total degree zero. -/
private theorem invertibleCurveDegree_eq_zero_of_forall {K : Type u} [Field K] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of K)) [IsProper sX] (hX : topologicalKrullDim X ≤ 1)
    (M : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    (h : ∀ C : ProperCurve sX, degreeOn K sX C.ι C.dim_le M = 0) :
    invertibleCurveDegree K sX hX M = 0 := by
  choose N ν hν hNdim using
    fun C : {C : ProperCurve sX // closure {C.point} ∈ irreducibleComponents X} =>
      exists_curveNormalization sX C.1
  rw [← finsum_length_mul_degreeOn_eq_invertibleCurveDegree sX hX M N ν hν hNdim]
  refine finsum_eq_zero_of_forall_eq_zero fun C => ?_
  have := (hν C).isFinite
  have : IsProper ((ν C ≫ C.1.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  rw [degreeOn_normalization C.1 (hν C) (hNdim C) M, h C.1, mul_zero]

/-- On a preirreducible proper scheme of dimension at most one, total degree zero forces degree
zero on every proper curve. -/
private theorem degreeOn_eq_zero_of_invertibleCurveDegree_eq_zero {K : Type u} [Field K]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of K)) [IsProper sX] [PreirreducibleSpace X]
    (hX : topologicalKrullDim X ≤ 1)
    (M : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    (h : invertibleCurveDegree K sX hX M = 0) (C : ProperCurve sX) :
    degreeOn K sX C.ι C.dim_le M = 0 := by
  classical
  have hloc : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  choose N ν hν hNdim using
    fun C : {C : ProperCurve sX // closure {C.point} ∈ irreducibleComponents X} =>
      exists_curveNormalization sX C.1
  have hmem : closure ({C.point} : Set X) ∈ irreducibleComponents X := by
    have := closure_genericPt_mem_irreducibleComponents hX
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({C.point} : Set X))) C.dim_eq
    rwa [show (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({C.point} : Set X))).subschemeι (genericPoint _) = C.point from
        C.ι_genericPoint] at this
  rw [← finsum_length_mul_degreeOn_eq_invertibleCurveDegree sX hX M N ν hν hNdim,
    finsum_eq_single _ (⟨C, hmem⟩ : {C : ProperCurve sX //
      closure {C.point} ∈ irreducibleComponents X})] at h
  · have := (hν ⟨C, hmem⟩).isFinite
    have : IsProper ((ν ⟨C, hmem⟩ ≫ C.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
    have hpos := length_toNat_pos_of_mem_irreducibleComponents C.point hmem
    have h2 := (mul_eq_zero.mp h).resolve_left (by exact_mod_cast hpos.ne')
    rw [← degreeOn_normalization C (hν ⟨C, hmem⟩) (hNdim ⟨C, hmem⟩) M]
    exact h2
  · intro C' hne
    exact absurd (ProperCurve.ext (eq_of_mem_irreducibleComponents_of_preirreducible C'.2 hmem))
      (fun h => hne (Subtype.ext h))

/-- The degree-zero condition at the point `s` of the base of a proper morphism `π : G ⟶ Δ`:
the invertible sheaf `L` has degree zero over `κ(s)` on every proper curve of the fibre
`π⁻¹(s)`. -/
private def FDZ {G Δ : Scheme.{u}} (π : G ⟶ Δ) [IsProper π] (L : G.Modules)
    [SheafOfModules.IsInvertible G.presheaf G.ringCatSheaf.2 L] (s : Δ) : Prop :=
  ∀ C : ProperCurve (π.fiberToSpecResidueField s),
    haveI : IsProper (C.ι ≫ π.fiberToSpecResidueField s) := C.isProperCurve.isProper
    degreeOn (Δ.residueField s) (π.fiberToSpecResidueField s) C.ι C.dim_le
      ((Scheme.Modules.pullback (π.fiberι s)).obj L) = 0

/-- **Degree zero propagates along a flat proper family with irreducible fibres of dimension
at most one over a connected base.** -/
private theorem FDZ_of_flat_family {G Δ : Scheme.{u}} (π : G ⟶ Δ) [IsProper π] [Flat π]
    [LocallyOfFinitePresentation π] [ConnectedSpace Δ] (L : G.Modules)
    [hL : SheafOfModules.IsInvertible G.presheaf G.ringCatSheaf.2 L]
    (hdim : ∀ s : Δ, topologicalKrullDim (π.fiber s) ≤ 1)
    (hirr : ∀ s : Δ, PreirreducibleSpace (π.fiber s)) (s₀ s : Δ) (h₀ : FDZ π L s₀) :
    FDZ π L s := by
  have : Stacks.Ample.IsInvertibleModule G L := inferInstance
  have hconst := (fibreEulerCharacteristic_tensorPowModule_eq π L).2 hdim s₀ s
  have hp0 : IsProper (π.fiberToSpecResidueField s₀) :=
    inferInstanceAs (IsProper (Limits.pullback.snd π (Δ.fromSpecResidueField s₀)))
  have hp1 : IsProper (π.fiberToSpecResidueField s) :=
    inferInstanceAs (IsProper (Limits.pullback.snd π (Δ.fromSpecResidueField s)))
  have h1 := @invertibleCurveDegree_eq_zero_of_forall (Δ.residueField s₀) _ _
    (π.fiberToSpecResidueField s₀) hp0 (hdim s₀)
    ((Scheme.Modules.pullback (π.fiberι s₀)).obj L) _ h₀
  have := hirr s
  exact @degreeOn_eq_zero_of_invertibleCurveDegree_eq_zero (Δ.residueField s) _ _
    (π.fiberToSpecResidueField s) hp1 _ (hdim s) _ _ (hconst ▸ h1)

/-- **Master transfer.** Let `F → F'` be a finite extension of fields, `f : X' ⟶ X` a morphism of
schemes over `Spec F' → Spec F`, `C'` a proper curve of the `F'`-scheme `X'` and `M` invertible
on `X`. Then `[F' : F] · deg_{F'}(C', f^*M)` is the degree of `M` on the push-forward cycle of
`C'`. -/
private theorem finrank_mul_degreeOn_eq_degree_pushforward {F F' : Type u} [Field F] [Field F']
    [Algebra F F'] [Module.Finite F F'] {X X' : Scheme.{u}} (s : X ⟶ Spec (.of F))
    (s' : X' ⟶ Spec (.of F')) (f : X' ⟶ X)
    (hf : f ≫ s = s' ≫ Spec.map (CommRingCat.ofHom (algebraMap F F')))
    [IsSeparated s] [LocallyOfFiniteType s]
    (M : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    (C' : ProperCurve s') :
    (((Module.finrank F F' : ℤ) * degreeOn F' s' C'.ι C'.dim_le
        ((Scheme.Modules.pullback f).obj M) : ℤ) : ℝ) =
      OneCycle.degree ℝ s M (cyclePushforwardOfPoint ℝ s f C'.point) := by
  have hfin : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap F F'))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have hpp : IsProper (C'.ι ≫ s' ≫ Spec.map (CommRingCat.ofHom (algebraMap F F'))) := by
    rw [← Category.assoc]; infer_instance
  let Ck : ProperCurve (s' ≫ Spec.map (CommRingCat.ofHom (algebraMap F F'))) :=
    ⟨C'.point, C'.dim_eq, hpp⟩
  have hpush := ProperCurve.degree_pushforward_eq_degree_pullback f hf Ck M
  have hpp' : IsProper ((C'.ι ≫ s') ≫ Spec.map (CommRingCat.ofHom (algebraMap F F'))) := by
    rwa [Category.assoc]
  have h1 : Ck.degree F ((Scheme.Modules.pullback f).obj M) =
      invertibleCurveDegree F ((C'.ι ≫ s') ≫ Spec.map (CommRingCat.ofHom (algebraMap F F')))
        C'.dim_le ((Scheme.Modules.pullback C'.ι).obj ((Scheme.Modules.pullback f).obj M)) :=
    invertibleCurveDegree_congr_structure (Category.assoc _ _ _).symm _ _
  have h2 := (invertibleCurveDegree_tower (F := F) (F' := F') (C'.ι ≫ s') C'.dim_le
    ((Scheme.Modules.pullback C'.ι).obj ((Scheme.Modules.pullback f).obj M)))
  have h3 : Ck.degree F ((Scheme.Modules.pullback f).obj M) = (Module.finrank F F' : ℤ) *
      degreeOn F' s' C'.ι C'.dim_le ((Scheme.Modules.pullback f).obj M) := h1.trans h2
  rw [← h3]
  exact hpush.symm

end family

section assembly

open MMP MMP.Flips Limits

section fibreMap

variable {W S Y Y' : Scheme.{u}} (g : Y' ⟶ Y) (h : S ⟶ Y) (πW : W ⟶ S) (q : W ⟶ Y')
  (hq : q ≫ g = πW ≫ h) (s : S)

/-- The morphism on fibres induced by a commutative square. -/
private noncomputable def fibreMap : πW.fiber s ⟶ g.fiber (h s) :=
  pullback.lift (πW.fiberι s ≫ q) (πW.fiberToSpecResidueField s ≫ Spec.map (h.residueFieldMap s))
    (by
      rw [Category.assoc, hq, ← Category.assoc,
        show πW.fiberι s ≫ πW = πW.fiberToSpecResidueField s ≫ S.fromSpecResidueField s from
          pullback.condition, Category.assoc, Category.assoc,
        h.SpecMap_residueFieldMap_fromSpecResidueField])

private theorem fibreMap_ι : fibreMap g h πW q hq s ≫ g.fiberι (h s) = πW.fiberι s ≫ q :=
  pullback.lift_fst _ _ _

private theorem fibreMap_snd : fibreMap g h πW q hq s ≫ g.fiberToSpecResidueField (h s) =
    πW.fiberToSpecResidueField s ≫ Spec.map (h.residueFieldMap s) :=
  pullback.lift_snd _ _ _

/-- The comparison of pull-backs along the fibre map. -/
private noncomputable def fibreMapPullbackIso {W S Y Y' : Scheme.{u}} (g : Y' ⟶ Y) (h : S ⟶ Y)
    (πW : W ⟶ S) (q : W ⟶ Y') (hq : q ≫ g = πW ≫ h) (s : S) (L : Y'.Modules) :
    (Scheme.Modules.pullback (fibreMap g h πW q hq s)).obj
        ((Scheme.Modules.pullback (g.fiberι (h s))).obj L) ≅
      (Scheme.Modules.pullback (πW.fiberι s)).obj ((Scheme.Modules.pullback q).obj L) :=
  (Scheme.Modules.pullbackComp (fibreMap g h πW q hq s) (g.fiberι (h s))).app L ≪≫
    (Scheme.Modules.pullbackCongr (fibreMap_ι g h πW q hq s)).app L ≪≫
    ((Scheme.Modules.pullbackComp (πW.fiberι s) q).app L).symm

end fibreMap

/-- A morphism of schemes over `F` which is non-constant on a proper curve has positive residue
degree at the generic point of the curve. -/
private theorem residueFieldDegree_pos_of_not_constant {F : Type u} [Field F] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of F)} {sY : Y ⟶ Spec (.of F)} [IsSeparated sY] [LocallyOfFiniteType sY]
    (f : X ⟶ Y) (hf : f ≫ sY = sX) (C : ProperCurve sX)
    (hnc : ¬ ∃ y : Y, Set.range (C.ι ≫ f) = {y}) : 0 < residueFieldDegree f C.point := by
  set φ := C.ι ≫ f with hφdef
  have hφ : φ ≫ sY = C.ι ≫ sX := by rw [hφdef, Category.assoc, hf]
  have : IsProper (φ ≫ sY) := hφ ▸ inferInstance
  have : IsProper φ := IsProper.of_comp _ sY
  have := C.isCurve
  have : AlgebraicGeometry.IsCurve F (φ ≫ sY) := hφ ▸ inferInstance
  have hdeg : residueFieldDegree f C.point = degreeOver φ.toImage := by
    have h1 := residueDegree_comp C.ι f (genericPoint C.scheme)
    rw [C.ι_genericPoint, Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion C.ι, mul_one]
      at h1
    have h2 := residueDegree_comp φ.toImage φ.imageι (genericPoint C.scheme)
    rw [Scheme.Hom.toImage_imageι,
      Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion φ.imageι,
      one_mul, residueDegree_genericPoint_eq_degreeOver φ.toImage] at h2
    exact h1.symm.trans h2
  rw [hdeg]
  letI := (functionFieldMap φ.toImage).toAlgebra
  have hfin : Module.Finite φ.image.functionField C.scheme.functionField :=
    finite_functionField_image sY φ hnc
  have heq : functionFieldMap φ.toImage = dominantFunctionFieldMap φ.toImage :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target φ.toImage (genericPoint C.scheme)
        (map_genericPoint_of_isDominant φ.toImage))).symm
  rw [degreeOver_eq_finrank φ.toImage heq]
  exact Module.finrank_pos

/-- A one-dimensional integral closed subscheme has a point other than its generic point. -/
private theorem exists_ne_mem_closure_of_dim_eq_one {X : Scheme.{u}} (x : X)
    (h : topologicalKrullDim (curveSubschemeAt x) = 1) : ∃ y ∈ closure ({x} : Set X), y ≠ x := by
  by_contra! hcon
  have hsub : Subsingleton (curveSubschemeAt x) := by
    refine ⟨fun a b => ?_⟩
    have ha : curveSubschemeAtι x a ∈ closure ({x} : Set X) :=
      range_curveSubschemeAtι x ▸ ⟨a, rfl⟩
    have hb : curveSubschemeAtι x b ∈ closure ({x} : Set X) :=
      range_curveSubschemeAtι x ▸ ⟨b, rfl⟩
    exact (curveSubschemeAtι x).isEmbedding.injective ((hcon _ ha).trans (hcon _ hb).symm)
  have : topologicalKrullDim (curveSubschemeAt x) ≤ 0 := by
    have : Subsingleton (TopologicalSpace.IrreducibleCloseds (curveSubschemeAt x)) :=
      ⟨fun S T => TopologicalSpace.IrreducibleCloseds.ext <|
        (Subsingleton.eq_univ_of_nonempty S.isIrreducible.nonempty).trans
          (Subsingleton.eq_univ_of_nonempty T.isIrreducible.nonempty).symm⟩
    exact Order.krullDim_nonpos_of_subsingleton
  rw [h] at this
  exact absurd this (by decide)

/-- **Descent of degree zero along a covering by finite base change.** Let `h : S ⟶ Y` be a
morphism, `s` a point of `S` with `κ(h s) → κ(s)` finite, and `W_a ⟶ S` a family of proper
`S`-schemes with maps `q_a : W_a ⟶ Y'` over `Y`, whose fibres over `s` have dimension at most one
and cover the fibre `g⁻¹(h s)`. If the pull-back of `L` has degree zero on every proper curve of
each fibre `(W_a)_s`, then `L` has degree zero on every proper curve of `g⁻¹(h s)`. -/
private theorem fdz_of_covering {Y' Y S : Scheme.{u}} (g : Y' ⟶ Y) [IsProper g] (h : S ⟶ Y)
    (L : Y'.Modules) [SheafOfModules.IsInvertible Y'.presheaf Y'.ringCatSheaf.2 L] (s : S)
    {ι : Type*} (W : ι → Scheme.{u}) (πW : ∀ a, W a ⟶ S) (q : ∀ a, W a ⟶ Y')
    (hq : ∀ a, q a ≫ g = πW a ≫ h) [∀ a, IsProper (πW a)]
    (hdim : ∀ a, topologicalKrullDim ((πW a).fiber s) ≤ 1)
    (hfdz : ∀ a, FDZ (πW a) ((Scheme.Modules.pullback (q a)).obj L) s)
    (hfin : @Module.Finite (Y.residueField (h s)) (S.residueField s) _ _
      (h.residueFieldMap s).hom.toAlgebra.toModule)
    (hcov : ∀ d : g.fiber (h s), ∃ a, ∃ z : (πW a).fiber s,
      fibreMap g h (πW a) (q a) (hq a) s z = d) :
    FDZ g L (h s) := by
  classical
  letI : Algebra (Y.residueField (h s)) (S.residueField s) := (h.residueFieldMap s).hom.toAlgebra
  intro C
  obtain ⟨a, z, hz⟩ := hcov C.point
  set φ := fibreMap g h (πW a) (q a) (hq a) s with hφ
  set F := Y.residueField (h s)
  set F' := S.residueField s
  have hfinS : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap F F'))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr hfin)
  let st : g.fiber (h s) ⟶ Spec (.of F) := g.fiberToSpecResidueField (h s)
  let s' : (πW a).fiber s ⟶ Spec (.of F') := (πW a).fiberToSpecResidueField s
  have hst : IsProper st :=
    inferInstanceAs (IsProper (pullback.snd g (Y.fromSpecResidueField (h s))))
  have hs' : IsProper s' :=
    inferInstanceAs (IsProper (pullback.snd (πW a) (S.fromSpecResidueField s)))
  have hφst : φ ≫ st = s' ≫ Spec.map (CommRingCat.ofHom (algebraMap F F')) :=
    fibreMap_snd g h (πW a) (q a) (hq a) s
  have hpφ : IsProper φ := by
    haveI : IsProper (φ ≫ st) := by
      rw [hφst]; infer_instance
    exact IsProper.of_comp φ st
  obtain ⟨d', hd'cl, hd'ne⟩ := exists_ne_mem_closure_of_dim_eq_one C.point C.dim_eq
  have hmap : closure ({C.point} : Set (g.fiber (h s))) ⊆ φ '' closure ({z} : Set _) := by
    have hcl : IsClosed (φ '' closure ({z} : Set _)) := φ.isClosedMap _ isClosed_closure
    refine closure_minimal ?_ hcl
    rintro _ rfl
    exact ⟨z, subset_closure rfl, hz⟩
  obtain ⟨z', hz'cl, hz'⟩ := hmap hd'cl
  have hzne : z' ≠ z := fun hh => hd'ne (by rw [← hz', hh, hz])
  haveI := Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure z
  have hge : (1 : WithBot ℕ∞) ≤ topologicalKrullDim (curveSubschemeAt z) := by
    obtain ⟨u, hu⟩ : z' ∈ Set.range (curveSubschemeAtι z) := by
      rwa [range_curveSubschemeAtι]
    refine one_le_topologicalKrullDim_of_specializes_of_ne
      (x := genericPoint (curveSubschemeAt z)) (y := u) (genericPoint_specializes u) ?_
    intro h0
    apply hzne
    rw [← hu, ← h0]
    exact Scheme.IdealSheafData.subschemeι_genericPoint_vanishingIdeal_closure z
  have hle : topologicalKrullDim (curveSubschemeAt z) ≤ 1 :=
    (curveSubschemeAtι z).isEmbedding.isInducing.topologicalKrullDim_le.trans (hdim a)
  have hdz : topologicalKrullDim (curveSubschemeAt z) = 1 := le_antisymm hle hge
  have hpz : IsProper (curveSubschemeAtι z ≫ s') := inferInstance
  have hpz' :
      IsProper (curveSubschemeAtι z ≫ s' ≫ Spec.map (CommRingCat.ofHom (algebraMap F F'))) := by
    rw [← Category.assoc]; infer_instance
  let Ca : ProperCurve s' := ⟨z, hdz, hpz⟩
  let Cb : ProperCurve (s' ≫ Spec.map (CommRingCat.ofHom (algebraMap F F'))) := ⟨z, hdz, hpz'⟩
  have hnc : ¬ ∃ y, Set.range (Cb.ι ≫ φ) = {y} := by
    rintro ⟨y, hy⟩
    have hr : Set.range (Cb.ι ≫ φ) = φ '' closure ({z} : Set _) := by
      show Set.range (⇑φ ∘ ⇑(curveSubschemeAtι z)) = _
      rw [Set.range_comp, range_curveSubschemeAtι]
    have h1 : C.point ∈ Set.range (Cb.ι ≫ φ) := hr ▸ hmap (subset_closure rfl)
    have h2 : d' ∈ Set.range (Cb.ι ≫ φ) := hr ▸ hmap hd'cl
    rw [hy] at h1 h2
    exact hd'ne (by rw [Set.mem_singleton_iff] at h1 h2; rw [h2, h1])
  have hpos := residueFieldDegree_pos_of_not_constant
    (sX := s' ≫ Spec.map (CommRingCat.ofHom (algebraMap F F'))) (sY := st) φ hφst Cb hnc
  haveI : SheafOfModules.IsInvertible (g.fiber (h s)).presheaf (g.fiber (h s)).ringCatSheaf.2
      ((Scheme.Modules.pullback (g.fiberι (h s))).obj L) := inferInstance
  have hmt := finrank_mul_degreeOn_eq_degree_pushforward (F := F) (F' := F') st s' φ hφst
    ((Scheme.Modules.pullback (g.fiberι (h s))).obj L) Ca
  have hdeg0 : degreeOn F' s' Ca.ι Ca.dim_le ((Scheme.Modules.pullback φ).obj
      ((Scheme.Modules.pullback (g.fiberι (h s))).obj L)) = 0 :=
    (degreeOn_eq_of_iso F' s' Ca.ι Ca.dim_le
      (fibreMapPullbackIso g h (πW a) (q a) (hq a) s L)).trans (hfdz a Ca)
  rw [hdeg0, mul_zero, Int.cast_zero] at hmt
  have hpc : IsProperCurve st (φ z) := by rw [hz]; exact C.isProperCurve
  have hCe : (⟨φ z, hpc⟩ : ProperCurve st) = C := ProperCurve.ext hz
  have hmt' : OneCycle.degree ℝ st ((Scheme.Modules.pullback (g.fiberι (h s))).obj L)
      (cyclePushforwardOfPoint ℝ st φ z) = 0 := hmt.symm
  rw [cyclePushforwardOfPoint, dif_pos hpc] at hmt'
  rw [hCe] at hmt'
  erw [OneCycle.degree_apply, Finsupp.sum_single_index (by simp)] at hmt'
  have hposR : (residueFieldDegree φ z : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  have h0 := (mul_eq_zero.mp hmt').resolve_left hposR
  exact_mod_cast h0

/-- If `M` has degree zero on every proper curve of `X`, then every pull-back of `M` along a
morphism over a finite extension of the base field has degree zero on every proper curve. -/
private theorem degreeOn_pullback_eq_zero_of_forall {F F' : Type u} [Field F] [Field F']
    [Algebra F F'] [Module.Finite F F'] {X X' : Scheme.{u}} (s : X ⟶ Spec (.of F))
    (s' : X' ⟶ Spec (.of F')) (f : X' ⟶ X)
    (hf : f ≫ s = s' ≫ Spec.map (CommRingCat.ofHom (algebraMap F F')))
    [IsSeparated s] [LocallyOfFiniteType s]
    (M : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    (hM : ∀ D : ProperCurve s, D.degree F M = 0) (C' : ProperCurve s') :
    degreeOn F' s' C'.ι C'.dim_le ((Scheme.Modules.pullback f).obj M) = 0 := by
  have hmt := finrank_mul_degreeOn_eq_degree_pushforward s s' f hf M C'
  suffices h : OneCycle.degree ℝ s M (cyclePushforwardOfPoint ℝ s f C'.point) = 0 by
    rw [h] at hmt
    exact (mul_eq_zero.mp (by exact_mod_cast hmt)).resolve_left
      (by exact_mod_cast (Module.finrank_pos (R := F) (M := F')).ne')
  by_cases hpc : IsProperCurve s (f C'.point)
  · rw [cyclePushforwardOfPoint, dif_pos hpc, OneCycle.degree_apply,
      Finsupp.sum_single_index (by simp)]
    simp [hM]
  · rw [cyclePushforwardOfPoint, dif_neg hpc, map_zero]

end assembly

section goodCover

open MMP MMP.Flips Limits

variable {Y' Y S : Scheme.{u}} (g : Y' ⟶ Y) (h : S ⟶ Y)

/-- The reduced closed subscheme of the base change `Y' ×_Y S` on an irreducible component. -/
private noncomputable abbrev compIdeal (Z : irreducibleComponents (pullback g h : Scheme.{u})) :
    (pullback g h : Scheme.{u}).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    (⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩ : Closeds (pullback g h : Scheme.{u}))

/-- The structure morphism to `S` of the component `Z` of `Y' ×_Y S`. -/
private noncomputable abbrev compπ (Z : irreducibleComponents (pullback g h : Scheme.{u})) :
    (compIdeal g h Z).subscheme ⟶ S :=
  (compIdeal g h Z).subschemeι ≫ pullback.snd g h

/-- The map to `Y'` of the component `Z` of `Y' ×_Y S`. -/
private noncomputable abbrev compq (Z : irreducibleComponents (pullback g h : Scheme.{u})) :
    (compIdeal g h Z).subscheme ⟶ Y' :=
  (compIdeal g h Z).subschemeι ≫ pullback.fst g h

private theorem compq_comp (Z : irreducibleComponents (pullback g h : Scheme.{u})) (V : S.Opens) :
    ((compπ g h Z ⁻¹ᵁ V).ι ≫ compq g h Z) ≫ g = (compπ g h Z ∣_ V) ≫ V.ι ≫ h := by
  rw [← Category.assoc (compπ g h Z ∣_ V), morphismRestrict_ι]
  simp only [Category.assoc, pullback.condition]

private theorem exists_component_fibre_preimage (V : S.Opens) (s : V.toScheme)
    (d : g.fiber ((V.ι ≫ h) s)) :
    ∃ (Z : irreducibleComponents (pullback g h : Scheme.{u}))
      (z : (compπ g h Z ∣_ V).fiber s),
      fibreMap g (V.ι ≫ h) (compπ g h Z ∣_ V) ((compπ g h Z ⁻¹ᵁ V).ι ≫ compq g h Z)
        (compq_comp g h Z V) s z = d := by
  classical
  have hy' : g (g.fiberι ((V.ι ≫ h) s) d) = (V.ι ≫ h) s := by
    have : g.fiberι ((V.ι ≫ h) s) d ∈ Set.range (g.fiberι ((V.ι ≫ h) s)) := ⟨d, rfl⟩
    rw [g.range_fiberι ((V.ι ≫ h) s)] at this
    exact this
  obtain ⟨z₁, hz₁p, hz₁π⟩ := Scheme.Pullback.exists_preimage_pullback (f := g) (g := h)
    (g.fiberι ((V.ι ≫ h) s) d) (V.ι s) (by rw [hy']; rfl)
  obtain ⟨Z, hZ, hz₁Z⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    ({z₁} : Set (pullback g h : Scheme.{u})) isIrreducible_singleton
  let Z' : irreducibleComponents (pullback g h : Scheme.{u}) := ⟨Z, hZ⟩
  have hz₁mem : z₁ ∈ Set.range (compIdeal g h Z').subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact hz₁Z rfl
  obtain ⟨w, hw⟩ := hz₁mem
  have hwV : w ∈ (compπ g h Z' ⁻¹ᵁ V : Set _) := by
    show (compπ g h Z') w ∈ (V : Set S)
    have : (compπ g h Z') w = V.ι s := by
      show (pullback.snd g h) ((compIdeal g h Z').subschemeι w) = _
      rw [hw, hz₁π]
    rw [this]; exact s.2
  let w' : (compπ g h Z' ⁻¹ᵁ V).toScheme := ⟨w, hwV⟩
  have hπw : (compπ g h Z' ∣_ V) w' = s := by
    apply Subtype.ext
    rw [morphismRestrict_base_coe]
    show (compπ g h Z') w = _
    show (pullback.snd g h) ((compIdeal g h Z').subschemeι w) = _
    rw [hw, hz₁π]; rfl
  obtain ⟨x, hx⟩ : ∃ x, V.toScheme.fromSpecResidueField s x = s := by
    have : s ∈ Set.range (V.toScheme.fromSpecResidueField s) := by
      rw [Scheme.range_fromSpecResidueField]; rfl
    exact this
  obtain ⟨z, hzf, hzs⟩ := Scheme.Pullback.exists_preimage_pullback (f := compπ g h Z' ∣_ V)
    (g := V.toScheme.fromSpecResidueField s) w' x (by rw [hπw, hx])
  let zf : (compπ g h Z' ∣_ V).fiber s := z
  refine ⟨Z', zf, ?_⟩
  apply (g.fiberι ((V.ι ≫ h) s)).isEmbedding.injective
  have e1 : (g.fiberι ((V.ι ≫ h) s)) (fibreMap g (V.ι ≫ h) (compπ g h Z' ∣_ V)
      ((compπ g h Z' ⁻¹ᵁ V).ι ≫ compq g h Z') (compq_comp g h Z' V) s zf) =
      ((compπ g h Z' ⁻¹ᵁ V).ι ≫ compq g h Z') (((compπ g h Z' ∣_ V).fiberι s) zf) := by
    rw [← Scheme.Hom.comp_apply, fibreMap_ι]; rfl
  rw [e1]
  have hfz : ((compπ g h Z' ∣_ V).fiberι s) zf = w' := hzf
  rw [hfz]
  show (pullback.fst g h) ((compIdeal g h Z').subschemeι w) = _
  rw [hw, hz₁p]

/-- **Descent of the degree-zero condition along a good finite cover.** -/
private theorem fdz_of_good_cover (g : Y' ⟶ Y) [IsProper g] (h : S ⟶ Y) [IsIntegral S]
    [IsLocallyNoetherian S]
    (L : Y'.Modules) [SheafOfModules.IsInvertible Y'.presheaf Y'.ringCatSheaf.2 L]
    (hdeg : FDZ g L (h (genericPoint S))) (V : S.Opens) (hV : genericPoint S ∈ V)
    (hfinres : ∀ s : V.toScheme, @Module.Finite (Y.residueField ((V.ι ≫ h) s))
      (V.toScheme.residueField s) _ _ ((V.ι ≫ h).residueFieldMap s).hom.toAlgebra.toModule)
    (hflat : ∀ Z : irreducibleComponents (pullback g h : Scheme.{u}), Flat (compπ g h Z ∣_ V))
    (hdim : ∀ (Z : irreducibleComponents (pullback g h : Scheme.{u})) (s : V.toScheme),
      topologicalKrullDim ((compπ g h Z ∣_ V).fiber s) ≤ 1)
    (hirr : ∀ (Z : irreducibleComponents (pullback g h : Scheme.{u})) (s : V.toScheme),
      PreirreducibleSpace ((compπ g h Z ∣_ V).fiber s))
    (s : S) (hs : s ∈ V) : FDZ g L (h s) := by
  haveI : Nonempty V.toScheme := ⟨⟨genericPoint S, hV⟩⟩
  haveI : IsIntegral V.toScheme := inferInstance
  haveI : IsLocallyNoetherian V.toScheme := inferInstance
  haveI : ConnectedSpace V.toScheme := inferInstance
  let s₀ : V.toScheme := ⟨genericPoint S, hV⟩
  let sV : V.toScheme := ⟨s, hs⟩
  have hfdz : ∀ Z : irreducibleComponents (pullback g h : Scheme.{u}),
      FDZ (compπ g h Z ∣_ V)
        ((Scheme.Modules.pullback ((compπ g h Z ⁻¹ᵁ V).ι ≫ compq g h Z)).obj L) sV := by
    intro Z
    haveI := hflat Z
    haveI : LocallyOfFinitePresentation (compπ g h Z ∣_ V) := inferInstance
    refine FDZ_of_flat_family (compπ g h Z ∣_ V) _ (hdim Z) (hirr Z) s₀ sV ?_
    intro C'
    letI : Algebra (Y.residueField ((V.ι ≫ h) s₀)) (V.toScheme.residueField s₀) :=
      ((V.ι ≫ h).residueFieldMap s₀).hom.toAlgebra
    haveI : Module.Finite (Y.residueField ((V.ι ≫ h) s₀)) (V.toScheme.residueField s₀) :=
      hfinres s₀
    let F := Y.residueField ((V.ι ≫ h) s₀)
    let F' := V.toScheme.residueField s₀
    let st : g.fiber ((V.ι ≫ h) s₀) ⟶ Spec (.of F) := g.fiberToSpecResidueField _
    let s' : (compπ g h Z ∣_ V).fiber s₀ ⟶ Spec (.of F') :=
      (compπ g h Z ∣_ V).fiberToSpecResidueField s₀
    have hseps : IsSeparated st :=
      inferInstanceAs (IsSeparated (pullback.snd g (Y.fromSpecResidueField ((V.ι ≫ h) s₀))))
    have hlft : LocallyOfFiniteType st :=
      inferInstanceAs (LocallyOfFiniteType (pullback.snd g (Y.fromSpecResidueField ((V.ι ≫ h) s₀))))
    have hφst : fibreMap g (V.ι ≫ h) (compπ g h Z ∣_ V) ((compπ g h Z ⁻¹ᵁ V).ι ≫ compq g h Z)
        (compq_comp g h Z V) s₀ ≫ st = s' ≫ Spec.map (CommRingCat.ofHom (algebraMap F F')) :=
      fibreMap_snd g (V.ι ≫ h) (compπ g h Z ∣_ V) ((compπ g h Z ⁻¹ᵁ V).ι ≫ compq g h Z)
        (compq_comp g h Z V) s₀
    have hM : ∀ D : ProperCurve st,
        D.degree F ((Scheme.Modules.pullback (g.fiberι ((V.ι ≫ h) s₀))).obj L) = 0 := hdeg
    have key := degreeOn_pullback_eq_zero_of_forall st s' _ hφst
      ((Scheme.Modules.pullback (g.fiberι ((V.ι ≫ h) s₀))).obj L) hM C'
    haveI : IsProper (C'.ι ≫ s') := C'.isProperCurve.isProper
    exact (degreeOn_eq_of_iso F' s' C'.ι C'.dim_le
      (fibreMapPullbackIso g (V.ι ≫ h) (compπ g h Z ∣_ V) _ (compq_comp g h Z V) s₀ L).symm).trans
      key
  exact fdz_of_covering g (V.ι ≫ h) L sV (fun Z => (compπ g h Z ⁻¹ᵁ V).toScheme)
    (fun Z => compπ g h Z ∣_ V) (fun Z => (compπ g h Z ⁻¹ᵁ V).ι ≫ compq g h Z)
    (fun Z => compq_comp g h Z V) (fun Z => hdim Z sV) hfdz (hfinres sV)
    (fun d => exists_component_fibre_preimage g h V sV d)

end goodCover

/-- A proper curve contracted by `g` to a point of `U₀` lies over a point of `T' = closure {η'}`:
over `U₀ ∖ T'` the morphism `g` is an isomorphism and contracts no curve. -/
private theorem mem_closure_of_isContractedBy
    (hY' : MMP.Mori.IsVariety k sY') {g : Y' ⟶ Y} {η' : Y} (U₀ : Y.Opens)
    (hiso : IsBiregular g (U₀ ⊓ ⟨(closure {η'})ᶜ, isClosed_closure.isOpen_compl⟩))
    (C : ProperCurve sY') (hC : C.IsContractedBy g) (hCU : g C.point ∈ U₀) :
    g C.point ∈ closure ({η'} : Set Y) := by
  by_contra hx
  set U : Y.Opens := U₀ ⊓ ⟨(closure {η'})ᶜ, isClosed_closure.isOpen_compl⟩
  have : IsIso (g ∣_ U) := hiso
  have hinj : ∀ a b : Y', a ∈ g ⁻¹ᵁ U → b ∈ g ⁻¹ᵁ U → g a = g b → a = b := by
    intro a b ha hb hab
    have hbij : Function.Bijective (g ∣_ U) :=
      ConcreteCategory.bijective_of_isIso (g ∣_ U).base
    have := hbij.1 (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩)
      (Subtype.ext ((morphismRestrict_base_coe g U ⟨a, ha⟩).trans
        (hab.trans (morphismRestrict_base_coe g U ⟨b, hb⟩).symm)))
    exact congrArg Subtype.val this
  have hxU : C.point ∈ (g ⁻¹ᵁ U : Set Y') := ⟨hCU, hx⟩
  have hsing : closure {C.point} ∩ (g ⁻¹ᵁ U : Set Y') = {C.point} := by
    ext z
    refine ⟨fun ⟨hz, hzU⟩ => hinj _ _ hzU hxU (hC z hz), ?_⟩
    rintro rfl
    exact ⟨subset_closure rfl, hxU⟩
  have : JacobsonSpace Y' := LocallyOfFiniteType.jacobsonSpace sY'
  have hcl : IsClosed ({C.point} : Set Y') :=
    isClosed_singleton_of_isLocallyClosed_singleton
      (hsing ▸ ⟨_, _, (g ⁻¹ᵁ U).isOpen, isClosed_closure, Set.inter_comm _ _⟩)
  obtain ⟨y, hy, hne⟩ := exists_ne_mem_closure_of_dim_eq_one C.point C.dim_eq
  exact hne (by rwa [hcl.closure_eq, Set.mem_singleton_iff] at hy)

omit [IsLocallyNoetherian Y'] [IsNormal Y'] [QuasiCompact sY'] in
/-- The image of a proper curve contracted by a proper morphism is a closed point. -/
public theorem isClosed_singleton_of_isContractedBy {g : Y' ⟶ Y} [IsProper g]
    (C : ProperCurve sY') (hC : C.IsContractedBy g) : IsClosed ({g C.point} : Set Y) := by
  have h : g '' closure ({C.point} : Set Y') = {g C.point} := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hC x hx
    · rintro _ rfl
      exact ⟨C.point, subset_closure rfl, rfl⟩
  rw [← h]
  exact g.isClosedMap _ isClosed_closure

omit [IsLocallyNoetherian Y'] [IsNormal Y'] in
variable (sY') in
/-- `FiberDegreeZero sY' g hD t` says that `𝒪_{Y'}(m D')`, with `m` the Cartier index of `D'`,
has degree zero over `κ(t)` on every proper curve of the fibre `g⁻¹(t)`. -/
@[expose] public def FiberDegreeZero (g : Y' ⟶ Y) [IsProper g]
    {D' : QDivisor Y'} (hD : D'.IsQCartier) (t : Y) : Prop :=
  haveI := QuasiCompact.compactSpace_of_compactSpace sY'
  haveI := (QDivisor.isCartierDivisor_cartierIndex_smul hD).isCartier_toDivisor
    |>.isInvertibleModule_divisorialSheaf
  ∀ C : ProperCurve (g.fiberToSpecResidueField t),
    haveI : IsProper (C.ι ≫ g.fiberToSpecResidueField t) := C.isProperCurve.isProper
    degreeOn (Y.residueField t) (g.fiberToSpecResidueField t) C.ι C.dim_le
      ((Scheme.Modules.pullback (g.fiberι t)).obj
        (QDivisor.isCartierDivisor_cartierIndex_smul hD).toDivisor.divisorialSheaf) = 0

/-- If `D'` has degree zero over `κ(t)` on every proper curve of the fibre `g⁻¹(t)`,
then `(D' · C) = 0` for every proper curve `C` of `Y'` contracted to `t`. -/
public theorem intersectionNumber_eq_zero_of_fiberDegreeZero
    (hY' : MMP.Mori.IsVariety k sY') (hY : MMP.Mori.IsVariety k sY) {g : Y' ⟶ Y} [IsProper g]
    (hg : g ≫ sY = sY') {D' : QDivisor Y'} (hD : D'.IsQCartier) (t : Y) (htc : IsClosed {t})
    (ht : FiberDegreeZero sY' g hD t)
    (C : ProperCurve sY') (hCt : g C.point = t) :
    D'.intersectionNumber k sY' C.ι C.dim_le hD = 0 := by
  classical
  haveI := QuasiCompact.compactSpace_of_compactSpace sY'
  haveI hinv := (QDivisor.isCartierDivisor_cartierIndex_smul hD).isCartier_toDivisor
    |>.isInvertibleModule_divisorialSheaf
  set L := (QDivisor.isCartierDivisor_cartierIndex_smul hD).toDivisor.divisorialSheaf with hL
  suffices hz : C.degree k L = 0 by
    unfold QDivisor.intersectionNumber
    have : (QDivisor.isCartierDivisor_cartierIndex_smul hD).toDivisor.degreeOn k sY' C.ι C.dim_le
        (QDivisor.isCartierDivisor_cartierIndex_smul hD).isCartier_toDivisor = 0 := hz
    rw [this]; simp
  -- the residue field and the fibre
  set κ := Y.residueField t
  letI : Algebra k κ := ((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appTop ≫ Y.Γevaluation t).hom.toAlgebra
  haveI : Module.Finite k κ := finite_residueField_over_field_of_isClosed k sY t htc
  set st := g.fiberToSpecResidueField t with hst
  haveI : IsProper st :=
    inferInstanceAs (IsProper (Limits.pullback.snd g (Y.fromSpecResidueField t)))
  have hcl : IsClosedImmersion (Y.fromSpecResidueField t) :=
    isClosed_singleton_iff_isClosedImmersion.mp htc
  haveI : IsClosedImmersion (g.fiberι t) :=
    inferInstanceAs (IsClosedImmersion (Limits.pullback.fst g (Y.fromSpecResidueField t)))
  obtain ⟨c, hc⟩ : C.point ∈ Set.range (g.fiberι t) := by
    rw [Scheme.Hom.range_fiberι]; exact hCt
  set ψ : CommRingCat.of k ⟶ Y.residueField t :=
    (Scheme.ΓSpecIso (.of k)).inv ≫ sY.appTop ≫ Y.Γevaluation t with hψ
  have hSpec : Y.fromSpecResidueField t ≫ sY = Spec.map ψ := fromSpecResidueField_comp t sY
  have hf : g.fiberι t ≫ sY' = st ≫ Spec.map ψ := by
    rw [← hSpec, ← hg, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ sY) Limits.pullback.condition
  have hfin : IsFinite (Spec.map ψ) := (IsFinite.SpecMap_iff ψ).mpr ‹Module.Finite k κ›
  have hdimc : topologicalKrullDim (curveSubschemeAt c) = 1 := by
    rw [topologicalKrullDim_curveSubschemeAt_eq (g.fiberι t) c, hc]; exact C.dim_eq
  let Ck : ProperCurve (st ≫ Spec.map ψ) := ⟨c, hdimc, inferInstance⟩
  haveI : IsProper (curveSubschemeAtι c) := inferInstance
  haveI : IsProper (show g.fiber t ⟶ Spec (.of κ) from st) :=
    inferInstanceAs (IsProper (Limits.pullback.snd g (Y.fromSpecResidueField t)))
  have hpp : IsProper (curveSubschemeAtι c ≫ g.fiberToSpecResidueField t) := inferInstance
  let Cκ : ProperCurve st := ⟨c, hdimc, hpp⟩
  have hz := ht Cκ
  haveI hMinv : SheafOfModules.IsInvertible Y'.presheaf Y'.ringCatSheaf.2 L := hinv
  have hpush := ProperCurve.degree_pushforward_eq_degree_pullback (g.fiberι t) hf Ck L
  have hpc : IsProperCurve sY' (g.fiberι t c) := by rw [hc]; exact C.isProperCurve
  have hres : residueFieldDegree (g.fiberι t) c = 1 := by
    have := Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion (g.fiberι t) c
    unfold residueFieldDegree; exact this
  have hCk : Ck.degree k ((Scheme.Modules.pullback (g.fiberι t)).obj L) = 0 := by
    have h1 : Ck.degree k ((Scheme.Modules.pullback (g.fiberι t)).obj L) =
        invertibleCurveDegree k ((Ck.ι ≫ st) ≫ Spec.map ψ) Ck.dim_le
          ((Scheme.Modules.pullback Ck.ι).obj ((Scheme.Modules.pullback (g.fiberι t)).obj L)) :=
      invertibleCurveDegree_congr_structure (Category.assoc _ _ _).symm _ _
    rw [h1]
    refine (invertibleCurveDegree_tower (F := k) (F' := κ) (Ck.ι ≫ st) Ck.dim_le _).trans ?_
    have h2 : invertibleCurveDegree κ (Ck.ι ≫ st) Ck.dim_le
          ((Scheme.Modules.pullback Ck.ι).obj ((Scheme.Modules.pullback (g.fiberι t)).obj L)) = 0 :=
      hz
    rw [h2, mul_zero]
  have hCe : (⟨g.fiberι t c, hpc⟩ : ProperCurve sY') = C := ProperCurve.ext hc
  have hpush' : OneCycle.degree ℝ sY' L (cyclePushforwardOfPoint ℝ sY' (g.fiberι t) c) =
      (Ck.degree k ((Scheme.Modules.pullback (g.fiberι t)).obj L) : ℝ) := hpush
  rw [hCk, cyclePushforwardOfPoint, dif_pos hpc] at hpush'
  simp only [OneCycle.degree, Finsupp.linearCombination_single, smul_eq_mul, hres, hCe] at hpush'
  simpa using hpush'

section SpreadingOut

open MMP MMP.Flips Limits

private theorem exists_fiber_restrict_homeo {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    (v : V.toScheme) : Nonempty ((f ∣_ V).fiber v ≃ₜ f.fiber (V.ι v)) := by
  have h :=
    isPullback_fiberToSpecResidueField_of_isPullback (isPullback_morphismRestrict f V).flip v
  have : IsIso (V.ι.residueFieldMap v) := inferInstance
  have : IsIso (Spec.map (V.ι.residueFieldMap v)) :=
    (Scheme.Spec.mapIso (asIso (V.ι.residueFieldMap v)).op).isIso_hom
  have hi := h.isIso_fst_of_isIso
  exact ⟨(@asIso _ _ _ _ _ hi).schemeIsoToHomeo⟩

private theorem flat_morphismRestrict_mono {X S : Scheme.{u}} (p : X ⟶ S) {V V₂ : S.Opens}
    (hV : V ≤ V₂) (h : Flat (p ∣_ V₂)) : Flat (p ∣_ V) := by
  have hj : Scheme.homOfLE S hV ≫ V₂.ι = V.ι := by simp
  let a : (p ⁻¹ᵁ V).toScheme ⟶ (p ⁻¹ᵁ V₂).toScheme :=
    Scheme.homOfLE X (Scheme.Hom.preimage_mono p hV)
  have w : a ≫ (p ∣_ V₂) = (p ∣_ V) ≫ Scheme.homOfLE S hV := by
    rw [← cancel_mono V₂.ι]
    simp [a, hj]
  have hout : IsPullback (a ≫ (p ⁻¹ᵁ V₂).ι) (p ∣_ V) p (Scheme.homOfLE S hV ≫ V₂.ι) := by
    have : a ≫ (p ⁻¹ᵁ V₂).ι = (p ⁻¹ᵁ V).ι := by simp [a]
    rw [this, hj]
    exact (isPullback_morphismRestrict p V).flip
  have hsq := IsPullback.of_right hout w (isPullback_morphismRestrict p V₂).flip
  exact MorphismProperty.of_isPullback hsq h

private theorem exists_open_flat_dim_irr {S W : Scheme.{u}} [IsIntegral S] (p : W ⟶ S)
    [LocallyOfFiniteType p] [QuasiCompact p] [UniversallyClosed p]
    (hdim : topologicalKrullDim (p.fiber (genericPoint S)) ≤ 1)
    (hgi : GeometricallyIrreducible (p.fiberToSpecResidueField (genericPoint S))) :
    ∃ V : S.Opens, genericPoint S ∈ V ∧ Flat (p ∣_ V) ∧ ∀ s ∈ V,
      topologicalKrullDim (p.fiber s) ≤ 1 ∧ PreirreducibleSpace (p.fiber s) := by
  have hmem : ∀ V : S.Opens, (V : Set S).Nonempty → genericPoint S ∈ V := fun V hV =>
    ((genericPoint_spec S).mem_open_set_iff V.isOpen).mpr (by simpa using hV)
  obtain ⟨V₁, hV₁ne, hV₁⟩ := geometricallyIrreducibleAfterShrinking p inferInstance inferInstance
    inferInstance _ (genericPoint_spec S) hgi
  obtain ⟨V₂, hV₂d, hV₂, -⟩ :=
    exists_dense_open_flat_finitePresentation p (SheafOfModules.unit W.ringCatSheaf)
  rw [Scheme.Hom.resLE_eq_morphismRestrict] at hV₂
  have hup := upperSemicontinuous_fiberDimension p
  have h3 : IsOpen {y : S | p.fiberDimension y < 2} :=
    (upperSemicontinuous_iff_isOpen_preimage.mp hup) 2
  have hlt : ∀ y : S, p.fiberDimension y < 2 → topologicalKrullDim (p.fiber y) ≤ 1 := by
    intro y hy
    have : p.fiberDimension y < (1 : WithBot ℕ∞) + 1 := by
      have e : (2 : WithBot ℕ∞) = (1 : WithBot ℕ∞) + 1 := by norm_num
      rwa [e] at hy
    exact ENat.WithBot.lt_add_one_iff.mp this
  have hη3 : genericPoint S ∈ ({y : S | p.fiberDimension y < 2} : Set S) :=
    lt_of_le_of_lt hdim (by exact_mod_cast Nat.one_lt_two)
  let V₃ : S.Opens := ⟨_, h3⟩
  have hV₁m := hmem V₁ (by simpa using hV₁ne)
  have hV₂m : genericPoint S ∈ V₂ := hmem V₂ hV₂d.nonempty
  have hle1 : V₁ ⊓ V₂ ⊓ V₃ ≤ V₁ := inf_le_left.trans inf_le_left
  have hle2 : V₁ ⊓ V₂ ⊓ V₃ ≤ V₂ := inf_le_left.trans inf_le_right
  have hgi' : GeometricallyIrreducible (p ∣_ (V₁ ⊓ V₂ ⊓ V₃)) := by
    rw [geometricallyIrreducible_morphismRestrict_iff_forall]
    have := (geometricallyIrreducible_morphismRestrict_iff_forall p V₁).mp hV₁
    intro v
    exact this ⟨v.1, hle1 v.2⟩
  have hirr : ∀ v : (V₁ ⊓ V₂ ⊓ V₃).toScheme,
      PreirreducibleSpace ((p ∣_ (V₁ ⊓ V₂ ⊓ V₃)).fiber v) := by
    intro v
    haveI : IrreducibleSpace ((p ∣_ (V₁ ⊓ V₂ ⊓ V₃)).fiber v) := inferInstance
    infer_instance
  refine ⟨V₁ ⊓ V₂ ⊓ V₃, ⟨⟨hV₁m, hV₂m⟩, hη3⟩, flat_morphismRestrict_mono p hle2 hV₂,
    fun s hs => ⟨hlt s hs.2, ?_⟩⟩
  obtain ⟨e⟩ := exists_fiber_restrict_homeo p (V₁ ⊓ V₂ ⊓ V₃) ⟨s, hs⟩
  haveI := hirr ⟨s, hs⟩
  show PreirreducibleSpace (p.fiber ((V₁ ⊓ V₂ ⊓ V₃).ι ⟨s, hs⟩))
  exact Function.Surjective.preirreducibleSpace e.continuous e.surjective

private theorem irreducibleSpace_pullback_comp_iff {A B T : Scheme.{u}} (i : A ⟶ B)
    [IsClosedImmersion i] (s : B ⟶ T) {K : Type u} [Field K] (y : Spec (.of K) ⟶ T) :
    IrreducibleSpace (pullback (i ≫ s) y : Scheme.{u}) ↔
      IsIrreducible ((pullback.fst s y : (pullback s y : Scheme.{u}) ⟶ B) ⁻¹' Set.range i) := by
  have e := pullbackRightPullbackFstIso s y i
  rw [← e.hom.homeomorph.irreducibleSpace_iff]
  have hemb : Topology.IsEmbedding (pullback.snd i (pullback.fst s y)) :=
    (pullback.snd i (pullback.fst s y)).isEmbedding
  rw [hemb.toHomeomorph.irreducibleSpace_iff, ← isIrreducible_iff_irreducibleSpace,
    Scheme.Pullback.range_snd]

/-- Geometric irreducibility of a closed subscheme of `B` over `T` depends only on its support. -/
private theorem geometricallyIrreducible_of_range_eq {A₁ A₂ B T : Scheme.{u}} (i₁ : A₁ ⟶ B)
    (i₂ : A₂ ⟶ B) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hr : Set.range i₁ = Set.range i₂) (s : B ⟶ T) (h : GeometricallyIrreducible (i₁ ≫ s)) :
    GeometricallyIrreducible (i₂ ≫ s) := by
  rw [GeometricallyIrreducible.eq_geometrically] at h ⊢
  intro K _ y Z fst snd hZ
  have hZ₁ : IrreducibleSpace (pullback (i₁ ≫ s) y : Scheme.{u}) :=
    h y (pullback.fst _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
  rw [irreducibleSpace_pullback_comp_iff] at hZ₁
  have e : Z ≅ (pullback (i₂ ≫ s) y : Scheme.{u}) := hZ.isoPullback
  show IrreducibleSpace Z
  rw [e.hom.homeomorph.irreducibleSpace_iff, irreducibleSpace_pullback_comp_iff]
  rwa [← hr]

/-- A finite extension of the fraction field of the image of a ring has a model finite over the
ring: the subalgebra generated by integral multiples of a spanning set. -/
private theorem exists_finite_model {A : Type u} [CommRing A] {K k' : Type u} [Field K]
    [Field k'] [Algebra K k'] [Module.Finite K k'] (ψ₀ : A →+* K)
    (hK : ∀ x : K, ∃ a b : A, ψ₀ b ≠ 0 ∧ x * ψ₀ b = ψ₀ a) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (ψ' : A →+* R') (ρ : R' →+* k'),
      Function.Injective ρ ∧ ρ.comp ψ' = (algebraMap K k').comp ψ₀ ∧ ψ'.Finite ∧
      (∀ x : k', ∃ r s : R', ρ s ≠ 0 ∧ x * ρ s = ρ r) ∧
      (∀ q : Ideal R', q.IsPrime → q.comap ψ' = RingHom.ker ψ' → q = ⊥) := by
  classical
  let R₀ : Subring K := ψ₀.range
  letI : Algebra R₀ K := R₀.subtype.toAlgebra
  letI : Algebra R₀ k' := ((algebraMap K k').comp R₀.subtype).toAlgebra
  haveI : IsScalarTower R₀ K k' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hfrac : IsFractionRing R₀ K := by
    have : FaithfulSMul R₀ K :=
      (faithfulSMul_iff_algebraMap_injective R₀ K).mpr Subtype.val_injective
    refine IsFractionRing.of_field _ _ fun z => ?_
    obtain ⟨a, b, hb, hz⟩ := hK z
    refine ⟨⟨ψ₀ a, ⟨a, rfl⟩⟩, ⟨ψ₀ b, ⟨b, rfl⟩⟩, ?_⟩
    show z = ψ₀ a / ψ₀ b
    rw [eq_div_iff hb]
    exact hz
  have hinj0 : Function.Injective (algebraMap R₀ k') :=
    (algebraMap K k').injective.comp Subtype.val_injective
  obtain ⟨s, hs⟩ := (Module.finite_def.mp inferInstance : (⊤ : Submodule K k').FG)
  have hint : ∀ x : k', ∃ m : nonZeroDivisors R₀, IsIntegral R₀ (m • x) := fun x =>
    IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors R₀) (Rₘ := K) x
      (Algebra.IsIntegral.isIntegral x)
  choose m hm using hint
  let T : Finset k' := s.image fun x => m x • x
  let B : Subalgebra R₀ k' := Algebra.adjoin R₀ (T : Set k')
  haveI : Module.Finite R₀ B :=
    Algebra.finite_adjoin_of_finite_of_isIntegral T.finite_toSet (by
      intro y hy
      simp only [T, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hy
      obtain ⟨x, -, rfl⟩ := hy
      exact hm x)
  -- every element of `k'` has a multiple by a nonzero element of `R₀` lying in `B`
  let N : Submodule K k' :=
    { carrier := {z | ∃ d : nonZeroDivisors R₀, d • z ∈ B}
      add_mem' := by
        rintro z₁ z₂ ⟨d₁, h₁⟩ ⟨d₂, h₂⟩
        refine ⟨d₁ * d₂, ?_⟩
        have : (d₁ * d₂) • (z₁ + z₂) = d₂ • (d₁ • z₁) + d₁ • (d₂ • z₂) := by
          rw [smul_add, ← mul_smul, ← mul_smul, mul_comm d₂ d₁]
        rw [this]
        exact B.add_mem (B.smul_mem h₁ _) (B.smul_mem h₂ _)
      zero_mem' := ⟨1, by simp⟩
      smul_mem' := by
        rintro c z ⟨d, hd⟩
        obtain ⟨⟨a, e⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R₀) c
        refine ⟨d * e, ?_⟩
        have : (d * e) • (IsLocalization.mk' K a e • z) = a • (d • z) := by
          have key := congrArg (algebraMap K k') (IsLocalization.mk'_spec K a e)
          simp only [Submonoid.smul_def, Algebra.smul_def, Submonoid.coe_mul, map_mul] at key ⊢
          have e1 : ∀ r : R₀, algebraMap R₀ k' r = algebraMap K k' (algebraMap R₀ K r) :=
            fun r => rfl
          rw [e1, e1 a]
          linear_combination (algebraMap K k' (algebraMap R₀ K d) * z) * key
        rw [this]
        exact B.smul_mem hd _ }
  have hN : N = ⊤ := by
    rw [eq_top_iff, ← hs, Submodule.span_le]
    intro x hx
    refine ⟨m x, Algebra.subset_adjoin ?_⟩
    simp only [T, Finset.coe_image]
    exact ⟨x, hx, rfl⟩
  haveI : Algebra.IsIntegral R₀ B := Algebra.IsIntegral.of_finite R₀ B
  have hinjB : Function.Injective (algebraMap R₀ B) := by
    intro x y hxy
    apply hinj0
    have := congrArg (fun t : B => (t : k')) hxy
    exact this
  refine ⟨B, inferInstance, inferInstance, (algebraMap R₀ B).comp ψ₀.rangeRestrict,
    (B.val : B →ₐ[R₀] k').toRingHom, Subtype.val_injective, ?_, ?_, ?_, ?_⟩
  · refine RingHom.ext fun a => ?_
    rfl
  · exact RingHom.Finite.comp (RingHom.finite_algebraMap.mpr inferInstance)
      (RingHom.Finite.of_surjective _ ψ₀.rangeRestrict_surjective)
  · intro z
    have hz : z ∈ N := hN ▸ Submodule.mem_top
    obtain ⟨d, hd⟩ := hz
    refine ⟨⟨d • z, hd⟩, algebraMap R₀ B d, ?_, ?_⟩
    · show algebraMap R₀ k' d ≠ 0
      rw [map_ne_zero_iff _ hinj0]
      exact nonZeroDivisors.coe_ne_zero d
    · show z * algebraMap R₀ k' d = d • z
      rw [Submonoid.smul_def, Algebra.smul_def, mul_comm]
  · intro q hq hcomap
    apply Ideal.eq_bot_of_under_eq_bot (R := R₀)
    have hsurj := ψ₀.rangeRestrict_surjective
    have h1 :
        (q.comap (algebraMap R₀ B)).comap ψ₀.rangeRestrict = RingHom.ker ψ₀.rangeRestrict := by
      rw [Ideal.comap_comap]
      rw [← RingHom.ker_comp_of_injective ψ₀.rangeRestrict hinjB]
      exact hcomap
    rw [Ideal.under_def, ← Ideal.map_comap_of_surjective _ hsurj (q.comap (algebraMap R₀ B)), h1]
    exact Ideal.map_eq_bot_iff_le_ker _ |>.mpr le_rfl

private theorem evaluation_fraction {Y : Scheme.{u}} {U : Y.Opens} (hU : IsAffineOpen U)
    (y : Y) (hy : y ∈ U) (x : Y.residueField y) :
    ∃ a b : Γ(Y, U), (Y.evaluation U y hy).hom b ≠ 0 ∧
      x * (Y.evaluation U y hy).hom b = (Y.evaluation U y hy).hom a := by
  letI : Algebra Γ(Y, U) (Y.presheaf.stalk y) := (Y.presheaf.germ U y hy).hom.toAlgebra
  haveI := hU.isLocalization_stalk ⟨y, hy⟩
  obtain ⟨t, rfl⟩ := Y.residue_surjective y x
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl t
  refine ⟨a, b, ?_, ?_⟩
  · have hu : IsUnit (algebraMap Γ(Y, U) (Y.presheaf.stalk y) b) :=
      IsLocalization.map_units (Y.presheaf.stalk y) b
    exact (hu.map (Y.residue y).hom).ne_zero
  · have := congrArg (Y.residue y).hom hab
    simpa [Scheme.evaluation, RingHom.algebraMap_toAlgebra] using this

private theorem fromSpecResidueField_eq_evaluation {Y : Scheme.{u}} {U : Y.Opens}
    (hU : IsAffineOpen U) (y : Y) (hy : y ∈ U) :
    Y.fromSpecResidueField y = Spec.map (Y.evaluation U y hy) ≫ hU.fromSpec := by
  rw [Scheme.fromSpecResidueField, ← IsAffineOpen.fromSpecStalk_eq_fromSpecStalk hU hy,
    IsAffineOpen.fromSpecStalk, ← Category.assoc, ← Spec.map_comp]
  rfl

private theorem exists_model_scheme {Y : Scheme.{u}} [IsLocallyNoetherian Y] (y : Y)
    (k' : Type u) [Field k'] [Algebra (Y.residueField y) k'] [Module.Finite (Y.residueField y) k'] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsNoetherianRing R')
      (U : Y.Opens) (hU : IsAffineOpen U) (hyU : y ∈ U)
      (ψ' : Γ(Y, U) ⟶ CommRingCat.of R') (ρ : CommRingCat.of R' ⟶ CommRingCat.of k'),
      Function.Injective ρ ∧ ψ'.hom.Finite ∧
      (∀ x : k', ∃ r s : R', ρ s ≠ 0 ∧ x * ρ s = ρ r) ∧
      (∀ q : Ideal R', q.IsPrime → q.comap ψ'.hom = RingHom.ker ψ'.hom → q = ⊥) ∧
      Spec.map ρ ≫ Spec.map ψ' ≫ hU.fromSpec =
        Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) k')) ≫
          Y.fromSpecResidueField y := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ y) isOpen_univ
  obtain ⟨R', _, _, ψ', ρ, hρ, hcomp, hfin, hfrac, hinc⟩ :=
    exists_finite_model (k' := k') (Y.evaluation U y hyU).hom (evaluation_fraction hU y hyU)
  haveI : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  letI : Algebra Γ(Y, U) R' := ψ'.toAlgebra
  haveI : Module.Finite Γ(Y, U) R' := hfin
  haveI : IsNoetherianRing R' := IsNoetherianRing.of_finite Γ(Y, U) R'
  refine ⟨R', inferInstance, inferInstance, inferInstance, U, hU, hyU, CommRingCat.ofHom ψ',
    CommRingCat.ofHom ρ, hρ, hfin, hfrac, hinc, ?_⟩
  rw [fromSpecResidueField_eq_evaluation hU y hyU, ← Category.assoc, ← Category.assoc,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  exact CommRingCat.hom_ext hcomp

private theorem fromSpecResidueField_Spec_eq (R : CommRingCat.{u}) (x : Spec R) :
    (Spec R).fromSpecResidueField x =
      Spec.map ((Scheme.ΓSpecIso R).inv ≫ (Spec R).Γevaluation x) := by
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField R x, ← Spec.map_comp]
  congr 1
  rw [Scheme.Spec.algebraMap_residueFieldIso_inv]
  rfl

private theorem exists_iso_generic_fibre {R' k' : Type u} [CommRing R'] [IsDomain R'] [Field k']
    (ρ : R' →+* k') (hρ : Function.Injective ρ)
    (hfrac : ∀ x : k', ∃ r s : R', ρ s ≠ 0 ∧ x * ρ s = ρ r) :
    ∃ (x : Spec (.of R')) (_ : x = genericPoint (Spec (.of R')))
      (e : Spec (.of k') ≅ Spec ((Spec (.of R')).residueField x)),
      e.hom ≫ (Spec (.of R')).fromSpecResidueField x = Spec.map (CommRingCat.ofHom ρ) := by
  set c : Spec (.of k') ⟶ Spec (.of R') := Spec.map (CommRingCat.ofHom ρ) with hcdef
  let x : Spec (.of R') := c (IsLocalRing.closedPoint k')
  let lam := Scheme.descResidueField (Scheme.stalkClosedPointTo c)
  have hc : Spec.map lam ≫ (Spec (.of R')).fromSpecResidueField x = c :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k' _ c
  have hx : x = genericPoint (Spec (.of R')) := by
    rw [genericPoint_eq_bot_of_affine]
    apply PrimeSpectrum.ext
    show Ideal.comap ρ (IsLocalRing.maximalIdeal k') = ⊥
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact Ideal.comap_bot_of_injective ρ hρ
  set ev := (Scheme.ΓSpecIso (CommRingCat.of R')).inv ≫ (Spec (.of R')).Γevaluation x with hev
  have hρ' : CommRingCat.ofHom ρ = ev ≫ lam := by
    rw [← Spec.map_inj, Spec.map_comp, ← fromSpecResidueField_Spec_eq]
    exact hc.symm
  have hlam : ∀ r : R', lam.hom (ev.hom r) = ρ r := fun r =>
    (congrArg (fun f => f.hom r) hρ').symm
  have hsurj : Function.Surjective lam.hom := by
    intro z
    obtain ⟨r, s, hs, hz⟩ := hfrac z
    have hs' : ev.hom s ≠ 0 := fun h => hs (by rw [← hlam, h, map_zero])
    refine ⟨ev.hom r * (ev.hom s)⁻¹, ?_⟩
    rw [map_mul, map_inv₀, hlam, hlam]
    field_simp
    exact hz.symm.trans (mul_comm _ _)
  haveI : IsIso lam := (ConcreteCategory.isIso_iff_bijective lam).mpr ⟨lam.hom.injective, hsurj⟩
  haveI : IsIso (Spec.map lam) := (Scheme.Spec.mapIso (asIso lam).op).isIso_hom
  exact ⟨x, hx, asIso (Spec.map lam), hc⟩

/-- Base change of the fibre along an isomorphism of the spectra of fields. -/
private theorem exists_isPullback_fiber_iso {W S : Scheme.{u}} (p : W ⟶ S) (x : S) {T : Scheme.{u}}
    (e : T ≅ Spec ((S.residueField x))) :
    ∃ m : (pullback p (e.hom ≫ S.fromSpecResidueField x) : Scheme.{u}) ⟶ p.fiber x,
      IsPullback m (pullback.snd p (e.hom ≫ S.fromSpecResidueField x))
        (p.fiberToSpecResidueField x) e.hom := by
  have hout : IsPullback (pullback.fst p (e.hom ≫ S.fromSpecResidueField x))
      (pullback.snd p (e.hom ≫ S.fromSpecResidueField x)) p (e.hom ≫ S.fromSpecResidueField x) :=
    IsPullback.of_hasPullback _ _
  let m : (pullback p (e.hom ≫ S.fromSpecResidueField x) : Scheme.{u}) ⟶ p.fiber x :=
    pullback.lift (pullback.fst p _) (pullback.snd p _ ≫ e.hom) (by simp [pullback.condition])
  have hm1 : m ≫ p.fiberι x = pullback.fst p (e.hom ≫ S.fromSpecResidueField x) :=
    pullback.lift_fst _ _ _
  have hm2 : m ≫ p.fiberToSpecResidueField x =
      pullback.snd p (e.hom ≫ S.fromSpecResidueField x) ≫ e.hom := pullback.lift_snd _ _ _
  refine ⟨m, IsPullback.of_right ?_ hm2 (isPullback_fiberι_fiberToSpecResidueField p x)⟩
  rw [hm1]
  exact hout

private theorem geometricallyIrreducible_fiber_of_iso {W S : Scheme.{u}} (p : W ⟶ S) (x : S)
    {T : Scheme.{u}} (e : T ≅ Spec ((S.residueField x)))
    (h : GeometricallyIrreducible (pullback.snd p (e.hom ≫ S.fromSpecResidueField x))) :
    GeometricallyIrreducible (p.fiberToSpecResidueField x) := by
  obtain ⟨m, hm⟩ := exists_isPullback_fiber_iso p x e
  have : MorphismProperty.RespectsIso @GeometricallyIrreducible.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact (morphismProperty_iff_of_isPullback_of_isIso (P := @GeometricallyIrreducible) hm).mp h

/-- Pasting: the base change to `T` of the fibre `g⁻¹(y)` is the base change of
`Y' ×_Y S ⟶ S` along `T ⟶ S`. -/
private theorem exists_iso_fibre_baseChange {Y' Y S T : Scheme.{u}} (g : Y' ⟶ Y) (h : S ⟶ Y)
    (c : T ⟶ S) (y : Y) (φ' : T ⟶ Spec (Y.residueField y))
    (hcomm : c ≫ h = φ' ≫ Y.fromSpecResidueField y) :
    ∃ θ : (pullback (g.fiberToSpecResidueField y) φ' : Scheme.{u}) ≅
        (pullback (pullback.snd g h) c : Scheme.{u}),
      θ.hom ≫ pullback.snd (pullback.snd g h) c = pullback.snd (g.fiberToSpecResidueField y) φ' ∧
      θ.hom ≫ pullback.fst (pullback.snd g h) c ≫ pullback.fst g h =
        pullback.fst (g.fiberToSpecResidueField y) φ' ≫ g.fiberι y := by
  have P1 := (IsPullback.of_hasPullback (g.fiberToSpecResidueField y) φ').paste_horiz
    (isPullback_fiberι_fiberToSpecResidueField g y)
  have P2 := (IsPullback.of_hasPullback (pullback.snd g h) c).paste_horiz
    (IsPullback.of_hasPullback g h)
  rw [← hcomm] at P1
  exact ⟨P1.isoIsPullback _ _ P2, IsPullback.isoIsPullback_hom_snd _ _ P1 P2,
    IsPullback.isoIsPullback_hom_fst _ _ P1 P2⟩

private theorem preimage_mem_irreducibleComponents_of_fibre {X F S : Type*} [TopologicalSpace X]
    [TopologicalSpace F] [TopologicalSpace S] [QuasiSober X] [T0Space S]
    (π : X → S) (hπ : Continuous π) (ε : F → X) (hε : Topology.IsEmbedding ε) (η : S)
    (hη : IsGenericPoint η Set.univ) (hrange : Set.range ε = π ⁻¹' {η})
    (Z : Set X) (hZ : Z ∈ irreducibleComponents X) (hne : (ε ⁻¹' Z).Nonempty) :
    ε ⁻¹' Z ∈ irreducibleComponents F := by
  have hZc : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
  obtain ⟨ζ, hζ⟩ := QuasiSober.sober hZ.1 hZc
  obtain ⟨z₀, hz₀⟩ := hne
  have h1 : ζ ⤳ ε z₀ := by
    rw [specializes_iff_mem_closure, hζ.def]
    exact hz₀
  have h2 : π ζ ⤳ η := by
    have := h1.map hπ
    have hz : π (ε z₀) = η := by
      have : ε z₀ ∈ π ⁻¹' {η} := hrange ▸ Set.mem_range_self z₀
      exact this
    rwa [hz] at this
  have h3 : η ⤳ π ζ := by
    rw [specializes_iff_mem_closure, hη.def]
    trivial
  have hζη : π ζ = η := (h2.antisymm h3).eq
  obtain ⟨ζ', hζ'⟩ : ζ ∈ Set.range ε := by
    rw [hrange]
    exact hζη
  have hZeq : ε ⁻¹' Z = closure {ζ'} := by
    rw [hε.closure_eq_preimage_closure_image, Set.image_singleton, hζ', hζ.def]
  rw [hZeq]
  refine ⟨isIrreducible_singleton.closure, fun s hs hle => ?_⟩
  have hζs : ζ ∈ ε '' s := ⟨ζ', hle (subset_closure rfl), hζ'⟩
  have hirr : IsIrreducible (closure (ε '' s)) :=
    (hs.image ε hε.continuous.continuousOn).closure
  have hZle : Z ≤ closure (ε '' s) := by
    rw [← hζ.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr (subset_closure hζs)) isClosed_closure
  have := hZ.2 hirr hZle
  intro x hx
  rw [← hZeq]
  exact this (subset_closure ⟨x, hx, rfl⟩)

private theorem fibre_gi_of_component {Y' Y S : Scheme.{u}} (g : Y' ⟶ Y) [IsProper g] (h : S ⟶ Y)
    {k' : Type u} [Field k'] (y : Y) [Algebra (Y.residueField y) k']
    (c : Spec (.of k') ⟶ S) (x : S) (hx : IsGenericPoint x Set.univ)
    (e : Spec (.of k') ≅ Spec (S.residueField x)) (he : e.hom ≫ S.fromSpecResidueField x = c)
    (hcomm : c ≫ h = Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) k')) ≫
      Y.fromSpecResidueField y)
    (hGI : ∀ W : irreducibleComponents (pullback (g.fiberToSpecResidueField y)
        (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) k'))) : Scheme.{u}),
      GeometricallyIrreducible ((Scheme.IdealSheafData.vanishingIdeal
        ⟨W.1, isClosed_of_mem_irreducibleComponents W.1 W.2⟩).subschemeι ≫ pullback.snd _ _))
    (Z : irreducibleComponents (pullback g h : Scheme.{u}))
    (hne : ∃ z : ↑(pullback g h : Scheme.{u}), z ∈ Z.1 ∧ pullback.snd g h z = x) :
    GeometricallyIrreducible ((compπ g h Z).fiberToSpecResidueField x) := by
  classical
  have hRI : MorphismProperty.RespectsIso @GeometricallyIrreducible.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  set φ' := Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) k')) with hφ'
  obtain ⟨θ, hθ1, hθ2⟩ := exists_iso_fibre_baseChange g h c y φ' hcomm
  have hcpre : IsPreimmersion c := by rw [← he]; infer_instance
  let ε : (pullback (pullback.snd g h) c : Scheme.{u}) ⟶ pullback g h :=
    pullback.fst (pullback.snd g h) c
  have hε : Topology.IsEmbedding ε := ε.isEmbedding
  have hrc : Set.range c = {x} := by
    rw [← he]
    show Set.range (⇑(S.fromSpecResidueField x) ∘ ⇑e.hom) = {x}
    rw [Set.range_comp, Set.range_eq_univ.mpr e.hom.surjective, Set.image_univ,
      Scheme.range_fromSpecResidueField]
  have hrange : Set.range ε = (pullback.snd g h) ⁻¹' {x} := by
    rw [Scheme.Pullback.range_fst, hrc]
  have hne' : (ε ⁻¹' Z.1).Nonempty := by
    obtain ⟨z, hzZ, hzx⟩ := hne
    have : z ∈ Set.range ε := by rw [hrange]; exact hzx
    obtain ⟨w, rfl⟩ := this
    exact ⟨w, hzZ⟩
  have hZc : ε ⁻¹' Z.1 ∈ irreducibleComponents (pullback (pullback.snd g h) c : Scheme.{u}) :=
    preimage_mem_irreducibleComponents_of_fibre (pullback.snd g h) (pullback.snd g h).continuous
      ε hε x hx hrange Z.1 Z.2 hne'
  have hW := preimage_mem_irreducibleComponents_of_iso θ hZc
  have hGW := hGI ⟨_, hW⟩
  have hrZ : Set.range (compIdeal g h Z).subschemeι = Z.1 := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hrW : Set.range (Scheme.IdealSheafData.vanishingIdeal
      (⟨_, isClosed_of_mem_irreducibleComponents _ hW⟩ :
        Closeds (pullback (g.fiberToSpecResidueField y) φ' : Scheme.{u}))).subschemeι =
      θ.hom.base ⁻¹' (ε ⁻¹' Z.1) := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  let i₁ := (Scheme.IdealSheafData.vanishingIdeal
      (⟨_, isClosed_of_mem_irreducibleComponents _ hW⟩ :
        Closeds (pullback (g.fiberToSpecResidueField y) φ' : Scheme.{u}))).subschemeι ≫ θ.hom
  have hi₁ : GeometricallyIrreducible (i₁ ≫ pullback.snd (pullback.snd g h) c) := by
    have : i₁ ≫ pullback.snd (pullback.snd g h) c =
        (Scheme.IdealSheafData.vanishingIdeal
          (⟨_, isClosed_of_mem_irreducibleComponents _ hW⟩ :
            Closeds (pullback (g.fiberToSpecResidueField y) φ' : Scheme.{u}))).subschemeι ≫
          pullback.snd (g.fiberToSpecResidueField y) φ' := by
      simp only [i₁, Category.assoc, hθ1]
    rw [this]
    exact hGW
  let i₂ := pullback.snd (compIdeal g h Z).subschemeι ε
  have hr1 : Set.range i₁ = ε ⁻¹' Z.1 := by
    show Set.range (⇑θ.hom ∘ ⇑(Scheme.IdealSheafData.vanishingIdeal
      (⟨_, isClosed_of_mem_irreducibleComponents _ hW⟩ :
        Closeds (pullback (g.fiberToSpecResidueField y) φ' : Scheme.{u}))).subschemeι) = _
    rw [Set.range_comp, hrW]
    exact Set.image_preimage_eq _ θ.hom.surjective
  have hr2 : Set.range i₂ = ε ⁻¹' Z.1 := by
    rw [Scheme.Pullback.range_snd, hrZ]
  have h1 := geometricallyIrreducible_of_range_eq i₁ i₂ (hr1.trans hr2.symm) _ hi₁
  have h2 : (pullbackRightPullbackFstIso (pullback.snd g h) c
        (compIdeal g h Z).subschemeι).hom ≫
      pullback.snd ((compIdeal g h Z).subschemeι ≫ pullback.snd g h) c =
      i₂ ≫ pullback.snd (pullback.snd g h) c := pullbackRightPullbackFstIso_hom_snd _ _ _
  have h3 : GeometricallyIrreducible
      (pullback.snd ((compIdeal g h Z).subschemeι ≫ pullback.snd g h) c) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso @GeometricallyIrreducible
      (pullbackRightPullbackFstIso (pullback.snd g h) c (compIdeal g h Z).subschemeι).hom, h2]
    exact h1
  refine geometricallyIrreducible_fiber_of_iso (compπ g h Z) x e ?_
  rw [he]
  exact h3

private theorem fibre_dim_of_component {Y' Y S : Scheme.{u}} (g : Y' ⟶ Y) (h : S ⟶ Y)
    {k' : Type u} [Field k'] (y : Y) [Algebra (Y.residueField y) k']
    [Module.Finite (Y.residueField y) k']
    (c : Spec (.of k') ⟶ S) (x : S)
    (e : Spec (.of k') ≅ Spec (S.residueField x)) (he : e.hom ≫ S.fromSpecResidueField x = c)
    (hcomm : c ≫ h = Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) k')) ≫
      Y.fromSpecResidueField y)
    (hfib : topologicalKrullDim (g.fiber y) ≤ 1)
    (Z : irreducibleComponents (pullback g h : Scheme.{u})) :
    topologicalKrullDim ((compπ g h Z).fiber x) ≤ 1 := by
  set φ' := Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) k')) with hφ'
  obtain ⟨θ, hθ1, hθ2⟩ := exists_iso_fibre_baseChange g h c y φ' hcomm
  let ε : (pullback (pullback.snd g h) c : Scheme.{u}) ⟶ pullback g h :=
    pullback.fst (pullback.snd g h) c
  let i₂ := pullback.snd (compIdeal g h Z).subschemeι ε
  let e₂ := pullbackRightPullbackFstIso (pullback.snd g h) c (compIdeal g h Z).subschemeι
  haveI : IsIntegralHom φ' := by
    rw [hφ', IsIntegralHom.SpecMap_iff]
    exact RingHom.IsIntegral.of_finite (RingHom.finite_algebraMap.mpr inferInstance)
  let q : (pullback ((compIdeal g h Z).subschemeι ≫ pullback.snd g h) c : Scheme.{u}) ⟶
      g.fiber y := e₂.inv ≫ i₂ ≫ θ.inv ≫ pullback.fst (g.fiberToSpecResidueField y) φ'
  haveI : IsIntegralHom q := by
    dsimp only [q]
    infer_instance
  obtain ⟨m, hm⟩ := exists_isPullback_fiber_iso (compπ g h Z) x e
  haveI : IsIso m := hm.isIso_fst_of_isIso
  have h1 : topologicalKrullDim ((compπ g h Z).fiber x) =
      topologicalKrullDim
        (pullback (compπ g h Z) (e.hom ≫ S.fromSpecResidueField x) : Scheme.{u}) :=
    (IsHomeomorph.topologicalKrullDim_eq _ (asIso m).hom.homeomorph.isHomeomorph).symm
  rw [h1, he]
  exact (AlgebraicGeometry.topologicalKrullDim_le_of_isIntegralHom q).trans hfib

private theorem exists_open_for_component {Y' Y S : Scheme.{u}} (g : Y' ⟶ Y) [IsProper g]
    (h : S ⟶ Y) [IsIntegral S] {k' : Type u} [Field k'] (y : Y) [Algebra (Y.residueField y) k']
    [Module.Finite (Y.residueField y) k'] (c : Spec (.of k') ⟶ S)
    (e : Spec (.of k') ≅ Spec (S.residueField (genericPoint S)))
    (he : e.hom ≫ S.fromSpecResidueField (genericPoint S) = c)
    (hcomm : c ≫ h = Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) k')) ≫
      Y.fromSpecResidueField y)
    (hGI : ∀ W : irreducibleComponents (pullback (g.fiberToSpecResidueField y)
        (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) k'))) : Scheme.{u}),
      GeometricallyIrreducible ((Scheme.IdealSheafData.vanishingIdeal
        ⟨W.1, isClosed_of_mem_irreducibleComponents W.1 W.2⟩).subschemeι ≫ pullback.snd _ _))
    (hfib : topologicalKrullDim (g.fiber y) ≤ 1)
    (Z : irreducibleComponents (pullback g h : Scheme.{u})) :
    ∃ V : S.Opens, genericPoint S ∈ V ∧ Flat (compπ g h Z ∣_ V) ∧ ∀ s ∈ V,
      topologicalKrullDim ((compπ g h Z).fiber s) ≤ 1 ∧
        PreirreducibleSpace ((compπ g h Z).fiber s) := by
  classical
  haveI : IsProper (compπ g h Z) := inferInstance
  by_cases hit : ∃ z : ↑(pullback g h : Scheme.{u}), z ∈ Z.1 ∧ pullback.snd g h z = genericPoint S
  · exact exists_open_flat_dim_irr (compπ g h Z)
      (fibre_dim_of_component g h y c (genericPoint S) e he hcomm hfib Z)
      (fibre_gi_of_component g h y c (genericPoint S) (genericPoint_spec S) e he hcomm hGI Z hit)
  · have hrZ : Set.range (compIdeal g h Z).subschemeι = Z.1 := by
      rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
      rfl
    have hnot : ∀ w, compπ g h Z w ≠ genericPoint S := by
      intro w hw
      exact hit ⟨(compIdeal g h Z).subschemeι w, hrZ ▸ Set.mem_range_self w, hw⟩
    let V : S.Opens := ⟨(Set.range (compπ g h Z))ᶜ,
      (compπ g h Z).isClosedMap.isClosed_range.isOpen_compl⟩
    have hempty : ∀ w, compπ g h Z w ∉ V := fun w hw => hw ⟨w, rfl⟩
    refine ⟨V, fun ⟨w, hw⟩ => hnot w hw, ?_, ?_⟩
    · refine Flat.of_stalkMap (compπ g h Z ∣_ V) ?_
      intro w
      exact absurd w.2 (hempty w.1)
    · intro s hs
      haveI : IsEmpty ((compπ g h Z).fiber s) := ⟨fun z => by
        have := Scheme.Hom.apply_fiberι (compπ g h Z) s z
        exact hs ⟨_, this⟩⟩
      have hb : (compπ g h Z).fiberDimension s = ⊥ :=
        (Scheme.Hom.fiberDimension_eq_bot_iff_isEmpty _ s).mpr inferInstance
      exact ⟨le_trans (le_of_eq hb) bot_le, inferInstance⟩

private theorem exists_open_of_finite_family {S : Scheme.{u}} {ι : Type*} [Finite ι] (x : S)
    (P : ι → S.Opens → Prop) (hmono : ∀ i V V', V ≤ V' → P i V' → P i V)
    (hex : ∀ i, ∃ V : S.Opens, x ∈ V ∧ P i V) :
    ∃ V : S.Opens, x ∈ V ∧ ∀ i, P i V := by
  classical
  haveI := Fintype.ofFinite ι
  have : ∀ F : Finset ι, ∃ V : S.Opens, x ∈ V ∧ ∀ i ∈ F, P i V := by
    intro F
    induction F using Finset.induction_on with
    | empty => exact ⟨⊤, trivial, by simp⟩
    | insert a F ha ih =>
      obtain ⟨V, hxV, hV⟩ := ih
      obtain ⟨V', hxV', hV'⟩ := hex a
      refine ⟨V ⊓ V', ⟨hxV, hxV'⟩, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hmono _ _ _ inf_le_right hV'
      · exact hmono _ _ _ inf_le_left (hV i hi)
  obtain ⟨V, hxV, hV⟩ := this Finset.univ
  exact ⟨V, hxV, fun i => hV i (Finset.mem_univ i)⟩

private theorem finite_residue_of_isFinite {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (x : X) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    Module.Finite (Y.residueField (f x)) (X.residueField x) := by
  haveI : DiscreteTopology (f.fiber (f x)) :=
    (IsArtinianScheme.iff_isNoetherian_and_discreteTopology.mp inferInstance).2
  exact (isClosed_asFiber_iff_finite_residueField f x).mp (isClosed_discrete _)

private theorem exists_model {Y : Scheme.{u}} [IsLocallyNoetherian Y] (y : Y) (k' : Type u)
    [Field k'] [Algebra (Y.residueField y) k'] [Module.Finite (Y.residueField y) k'] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsNoetherianRing R')
      (h : Spec (.of R') ⟶ Y) (c : Spec (.of k') ⟶ Spec (.of R'))
      (e : Spec (.of k') ≅ Spec ((Spec (.of R')).residueField (genericPoint (Spec (.of R'))))),
      e.hom ≫ (Spec (.of R')).fromSpecResidueField (genericPoint (Spec (.of R'))) = c ∧
      c ≫ h = Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) k')) ≫
        Y.fromSpecResidueField y ∧
      h (genericPoint (Spec (.of R'))) = y ∧
      (∀ s : Spec (.of R'), letI := (h.residueFieldMap s).hom.toAlgebra
        Module.Finite (Y.residueField (h s)) ((Spec (.of R')).residueField s)) ∧
      (∀ V : (Spec (.of R')).Opens, genericPoint (Spec (.of R')) ∈ V →
        ∃ U : Y.Opens, y ∈ U ∧ ∀ t ∈ U, t ∈ closure ({y} : Set Y) → ∃ s ∈ V, h s = t) := by
  obtain ⟨R', _, _, _, U, hU, hyU, ψ', ρ, hρ, hfin, hfrac, hinc, hcomm⟩ :=
    exists_model_scheme y k'
  obtain ⟨x, hx, e, he⟩ := exists_iso_generic_fibre ρ.hom hρ hfrac
  subst hx
  have he' : e.hom ≫ (Spec (.of R')).fromSpecResidueField (genericPoint (Spec (.of R'))) =
      Spec.map ρ := he
  have hgen : (Spec.map ψ' ≫ hU.fromSpec) (genericPoint (Spec (.of R'))) = y := by
    have hc : ∀ p, (Spec.map ρ : Spec (.of k') ⟶ Spec (.of R')) p =
        genericPoint (Spec (.of R')) := fun p => by
      rw [← he', Scheme.Hom.comp_apply]
      exact Scheme.fromSpecResidueField_apply _ _
    obtain ⟨p0⟩ : Nonempty (Spec (.of k')) := inferInstance
    have h1 := congrArg (fun f : Spec (.of k') ⟶ Y => f p0) hcomm
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h1
    rw [hc] at h1
    rw [Scheme.Hom.comp_apply, h1]
    exact Scheme.fromSpecResidueField_apply (X := Y) y
      (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) k')) p0)
  refine ⟨R', inferInstance, inferInstance, inferInstance, Spec.map ψ' ≫ hU.fromSpec,
    Spec.map ρ, e, he', by rw [← Category.assoc] at hcomm; exact hcomm, ?_, ?_, ?_⟩
  · exact hgen
  · intro s
    haveI hf : IsFinite (Spec.map ψ') := (IsFinite.SpecMap_iff ψ').mpr hfin
    have h2 := finite_residue_of_isFinite (Spec.map ψ') s
    have hcomp : (Spec.map ψ' ≫ hU.fromSpec).residueFieldMap s =
        hU.fromSpec.residueFieldMap ((Spec.map ψ') s) ≫ (Spec.map ψ').residueFieldMap s :=
      Scheme.residueFieldMap_comp _ _ _
    show RingHom.Finite ((Spec.map ψ' ≫ hU.fromSpec).residueFieldMap s).hom
    rw [hcomp]
    show RingHom.Finite (((Spec.map ψ').residueFieldMap s).hom.comp
      (hU.fromSpec.residueFieldMap ((Spec.map ψ') s)).hom)
    refine RingHom.Finite.comp h2 (RingHom.Finite.of_surjective _ ?_)
    have : IsIso (hU.fromSpec.residueFieldMap ((Spec.map ψ') s)) := inferInstance
    exact ((ConcreteCategory.isIso_iff_bijective _).mp this).2
  · intro V hV
    haveI hf : IsFinite (Spec.map ψ') := (IsFinite.SpecMap_iff ψ').mpr hfin
    set h₀ : Spec (.of R') ⟶ Spec Γ(Y, U) := Spec.map ψ' with hh₀
    have hy₀ : hU.fromSpec (h₀ (genericPoint (Spec (.of R')))) = y := by
      rw [← Scheme.Hom.comp_apply]; exact hgen
    have hD : IsClosed (h₀ '' (V : Set (Spec (.of R')))ᶜ) := h₀.isClosedMap _ V.2.isClosed_compl
    have incomp : ∀ s : Spec (.of R'), h₀ s = h₀ (genericPoint (Spec (.of R'))) →
        s = genericPoint (Spec (.of R')) := by
      intro s hs
      rw [genericPoint_eq_bot_of_affine]
      apply PrimeSpectrum.ext
      apply hinc s.asIdeal s.isPrime
      have := congrArg PrimeSpectrum.asIdeal hs
      rw [genericPoint_eq_bot_of_affine] at this
      exact this
    have hy₀D : h₀ (genericPoint (Spec (.of R'))) ∉ h₀ '' (V : Set (Spec (.of R')))ᶜ := by
      rintro ⟨s, hsC, hs⟩
      exact hsC (incomp s hs ▸ hV)
    refine ⟨⟨hU.fromSpec '' (h₀ '' (V : Set (Spec (.of R')))ᶜ)ᶜ,
      hU.fromSpec.isOpenEmbedding.isOpenMap _ hD.isOpen_compl⟩,
      ⟨_, hy₀D, hy₀⟩, ?_⟩
    rintro t ⟨t₀, ht₀D, rfl⟩ htcl
    have h1 : t₀ ∈ closure {h₀ (genericPoint (Spec (.of R')))} := by
      have := hU.fromSpec.isEmbedding.closure_eq_preimage_closure_image
        ({h₀ (genericPoint (Spec (.of R')))} : Set (Spec Γ(Y, U)))
      rw [Set.image_singleton, hy₀] at this
      rw [this]
      exact htcl
    have hrange : closure {h₀ (genericPoint (Spec (.of R')))} ⊆ Set.range h₀ :=
      closure_minimal (Set.singleton_subset_iff.mpr ⟨_, rfl⟩) h₀.isClosedMap.isClosed_range
    obtain ⟨s, hs⟩ := hrange h1
    refine ⟨s, ?_, by rw [Scheme.Hom.comp_apply, hs]⟩
    by_contra hsV
    exact ht₀D ⟨s, hsV, hs⟩

private theorem exists_good_cover {k : Type u} [Field k] {Y' Y : Scheme.{u}}
    {sY' : Y' ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    (hY' : MMP.Mori.IsVariety k sY') (hY : MMP.Mori.IsVariety k sY) {g : Y' ⟶ Y} [IsProper g]
    {η' : Y} (hfib : topologicalKrullDim (g.fiber η') ≤ 1) :
    ∃ (S : Scheme.{u}) (_ : IsIntegral S) (_ : IsLocallyNoetherian S) (h : S ⟶ Y),
      h (genericPoint S) = η' ∧
      ∃ (V : S.Opens) (_ : genericPoint S ∈ V) (U : Y.Opens), η' ∈ U ∧
        (∀ t ∈ U, t ∈ closure ({η'} : Set Y) → ∃ s : S, s ∈ V ∧ h s = t) ∧
        (∀ s : V.toScheme, @Module.Finite (Y.residueField ((V.ι ≫ h) s))
          (V.toScheme.residueField s) _ _ ((V.ι ≫ h).residueFieldMap s).hom.toAlgebra.toModule) ∧
        (∀ Z : irreducibleComponents (Limits.pullback g h : Scheme.{u}), Flat (compπ g h Z ∣_ V)) ∧
        (∀ (Z : irreducibleComponents (Limits.pullback g h : Scheme.{u})) (s : V.toScheme),
          topologicalKrullDim ((compπ g h Z ∣_ V).fiber s) ≤ 1) ∧
        (∀ (Z : irreducibleComponents (Limits.pullback g h : Scheme.{u})) (s : V.toScheme),
          PreirreducibleSpace ((compπ g h Z ∣_ V).fiber s)) := by
  classical
  haveI := hY
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  let f : g.fiber η' ⟶ Spec (.of (Y.residueField η')) := g.fiberToSpecResidueField η'
  haveI hfl : LocallyOfFiniteType f :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd g (Y.fromSpecResidueField η')))
  haveI hfq : QuasiCompact f :=
    inferInstanceAs (QuasiCompact (pullback.snd g (Y.fromSpecResidueField η')))
  haveI : CompactSpace (g.fiber η') := QuasiCompact.compactSpace_of_compactSpace f
  haveI : IsLocallyNoetherian (g.fiber η') := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : IsNoetherian (g.fiber η') := {}
  have hcomp : (irreducibleComponents (g.fiber η')).Finite :=
    finite_irreducibleComponents_of_isNoetherian
  obtain ⟨k', _, _, hfd, hsep, hGI⟩ :=
    exists_finite_separable_extension_geometricallyIrreducible_components (Y.residueField η')
      (g.fiber η') f hcomp
  haveI : Module.Finite (Y.residueField η') k' := hfd
  obtain ⟨R', _, _, _, h, c, e, he, hcomm, hhη, hfinres, hsurj⟩ := exists_model η' k'
  haveI : IsIntegral (Spec (.of R')) := inferInstance
  haveI : IsLocallyNoetherian (Spec (.of R')) := inferInstance
  haveI : LocallyOfFiniteType (pullback.snd g h) := inferInstance
  haveI : IsLocallyNoetherian (pullback g h : Scheme.{u}) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd g h)
  haveI : CompactSpace (pullback g h : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd g h)
  haveI : IsNoetherian (pullback g h : Scheme.{u}) := {}
  have hGfin : (irreducibleComponents (pullback g h : Scheme.{u})).Finite :=
    finite_irreducibleComponents_of_isNoetherian
  haveI : Finite (irreducibleComponents (pullback g h : Scheme.{u})) := hGfin.to_subtype
  obtain ⟨V, hηV, hV⟩ := exists_open_of_finite_family (genericPoint (Spec (.of R')))
    (fun (Z : irreducibleComponents (pullback g h : Scheme.{u})) (V : (Spec (.of R')).Opens) =>
      Flat (compπ g h Z ∣_ V) ∧ ∀ s ∈ V, topologicalKrullDim ((compπ g h Z).fiber s) ≤ 1 ∧
        PreirreducibleSpace ((compπ g h Z).fiber s))
    (fun Z V V' hle ⟨hf, hrest⟩ => ⟨flat_morphismRestrict_mono _ hle hf,
      fun s hs => hrest s (hle hs)⟩)
    (fun Z => by
      obtain ⟨V, hx, hf, hr⟩ := exists_open_for_component g h η' c e he hcomm hGI hfib Z
      exact ⟨V, hx, hf, hr⟩)
  obtain ⟨U, hηU, hU⟩ := hsurj V hηV
  refine ⟨Spec (.of R'), inferInstance, inferInstance, h, hhη, V, hηV, U, hηU,
    fun t ht hcl => hU t ht hcl, ?_, fun Z => (hV Z).1, ?_, ?_⟩
  · intro s
    have h1 := hfinres (V.ι s)
    have hcomp : (V.ι ≫ h).residueFieldMap s =
        h.residueFieldMap (V.ι s) ≫ V.ι.residueFieldMap s := Scheme.residueFieldMap_comp _ _ _
    show RingHom.Finite ((V.ι ≫ h).residueFieldMap s).hom
    rw [hcomp]
    show RingHom.Finite ((V.ι.residueFieldMap s).hom.comp (h.residueFieldMap (V.ι s)).hom)
    refine RingHom.Finite.comp (RingHom.Finite.of_surjective _ ?_) h1
    have : IsIso (V.ι.residueFieldMap s) := inferInstance
    exact ((ConcreteCategory.isIso_iff_bijective _).mp this).2
  · intro Z s
    obtain ⟨eh⟩ := exists_fiber_restrict_homeo (compπ g h Z) V s
    rw [IsHomeomorph.topologicalKrullDim_eq _ eh.isHomeomorph]
    exact ((hV Z).2 (V.ι s) s.2).1
  · intro Z s
    obtain ⟨eh⟩ := exists_fiber_restrict_homeo (compπ g h Z) V s
    haveI := ((hV Z).2 (V.ι s) s.2).2
    exact Function.Surjective.preirreducibleSpace eh.symm.continuous eh.symm.surjective

end SpreadingOut

/-- Spreading out the fibre degrees: over a neighbourhood of `η'`, `D'` has degree zero over
`κ(t)` on every proper curve of the fibre over each point `t` of `T' = {η'}⁻`. -/
public theorem exists_open_fiberDegreeZero
    (hY' : MMP.Mori.IsVariety k sY') (hY : MMP.Mori.IsVariety k sY) {g : Y' ⟶ Y} [IsProper g]
    {η' : Y} (hfib : topologicalKrullDim (g.fiber η') ≤ 1)
    {D' : QDivisor Y'} (hD : D'.IsQCartier)
    (hdeg : FiberDegreeZero sY' g hD η') :
    ∃ U : Y.Opens, η' ∈ U ∧ ∀ t ∈ U, t ∈ closure ({η'} : Set Y) →
      FiberDegreeZero sY' g hD t := by
  haveI := QuasiCompact.compactSpace_of_compactSpace sY'
  haveI hinv := (QDivisor.isCartierDivisor_cartierIndex_smul hD).isCartier_toDivisor
    |>.isInvertibleModule_divisorialSheaf
  obtain ⟨S, hSi, hSn, h, hηS, V, hV, U, hηU, hsurj, hfin, hflat, hdim, hirr⟩ :=
    exists_good_cover hY' hY hfib
  refine ⟨U, hηU, fun t htU htT => ?_⟩
  obtain ⟨s, hsV, hst⟩ := hsurj t htU htT
  have hdeg' : FDZ g (QDivisor.isCartierDivisor_cartierIndex_smul hD).toDivisor.divisorialSheaf
      (h (genericPoint S)) := by rw [hηS]; exact hdeg
  exact hst ▸ fdz_of_good_cover g h
    (QDivisor.isCartierDivisor_cartierIndex_smul hD).toDivisor.divisorialSheaf hdeg' V hV hfin
    hflat hdim hirr s hsV

end RelativeNumericalTriviality

open RelativeNumericalTriviality in
/-- **Relative numerical triviality, local form.** As
`intersectionNumber_eq_zero_of_degreeOn_fiber_eq_zero`, with `g` an isomorphism only over
`U₀ ∖ T'` for an open neighbourhood `U₀` of `η'`; the neighbourhood `U` lies in `U₀`. -/
public theorem intersectionNumber_eq_zero_of_degreeOn_fiber_eq_zero_of_isBiregular
    (hY' : Mori.IsVariety k sY') (hY : Mori.IsVariety k sY) {g : Y' ⟶ Y} [IsProper g]
    (hg : g ≫ sY = sY') {η' : Y} (hfib : topologicalKrullDim (g.fiber η') ≤ 1) (U₀ : Y.Opens) (hU₀ : η' ∈ U₀)
    (hiso : IsBiregular g (U₀ ⊓ ⟨(closure {η'})ᶜ, isClosed_closure.isOpen_compl⟩))
    {D' : QDivisor Y'} (hD : D'.IsQCartier) (hdeg : FiberDegreeZero sY' g hD η') :
    ∃ U : Y.Opens, U ≤ U₀ ∧ η' ∈ U ∧ ∀ C : ProperCurve sY', C.IsContractedBy g →
      g C.point ∈ U → D'.intersectionNumber k sY' C.ι C.dim_le hD = 0 := by
  obtain ⟨U, hηU, hU⟩ := exists_open_fiberDegreeZero hY' hY hfib hD hdeg
  refine ⟨U ⊓ U₀, inf_le_right, ⟨hηU, hU₀⟩, fun C hC hCU => ?_⟩
  exact intersectionNumber_eq_zero_of_fiberDegreeZero hY' hY hg hD _
    (isClosed_singleton_of_isContractedBy C hC)
    (hU _ hCU.1 (mem_closure_of_isContractedBy hY' U₀ hiso C hC hCU.2)) C rfl

open RelativeNumericalTriviality in
/-- **Relative numerical triviality.** Let `g : Y' ⟶ Y` be a projective birational morphism of
`k`-varieties, `Y'` normal, `η'` the generic point of a curve in `Y` off which `g` is an
isomorphism, and `dim g⁻¹(η') ≤ 1`. If a
`ℚ`-Cartier `ℚ`-divisor `D'` on `Y'` has degree zero on every proper curve of the generic fibre
`g⁻¹(η')` over `κ(η')`, then there is an open neighbourhood `U` of `η'` such that `(D' · C) = 0`
for every proper curve `C ⊆ Y'` contracted by `g` to a point of `U`. -/
@[mmp "lem_oai4_c2_relative_numerical_triviality"]
public theorem intersectionNumber_eq_zero_of_degreeOn_fiber_eq_zero
    (hY' : Mori.IsVariety k sY') (hY : Mori.IsVariety k sY) {g : Y' ⟶ Y} [IsProper g]
    (hproj : IsProjectiveMorphism g) (hbir : IsBirationalMorphism g) (hg : g ≫ sY = sY')
    {η' : Y} (hη : topologicalKrullDim (curveSubschemeAt η') = 1)
    (hfib : topologicalKrullDim (g.fiber η') ≤ 1)
    (hiso : IsIso (g ∣_ ⟨(closure {η'})ᶜ, isClosed_closure.isOpen_compl⟩))
    {D' : QDivisor Y'} (hD : D'.IsQCartier)
    (hdeg : haveI := QuasiCompact.compactSpace_of_compactSpace sY'
      haveI := (QDivisor.isCartierDivisor_cartierIndex_smul hD).isCartier_toDivisor
        |>.isInvertibleModule_divisorialSheaf
      ∀ C : ProperCurve (g.fiberToSpecResidueField η'),
        haveI : IsProper (C.ι ≫ g.fiberToSpecResidueField η') := C.isProperCurve.isProper
        degreeOn (Y.residueField η') (g.fiberToSpecResidueField η') C.ι C.dim_le
          ((Scheme.Modules.pullback (g.fiberι η')).obj
            (QDivisor.isCartierDivisor_cartierIndex_smul hD).toDivisor.divisorialSheaf) = 0) :
    ∃ U : Y.Opens, η' ∈ U ∧ ∀ C : ProperCurve sY', C.IsContractedBy g → g C.point ∈ U →
      D'.intersectionNumber k sY' C.ι C.dim_le hD = 0 := by
  obtain ⟨U, -, hηU, hU⟩ := intersectionNumber_eq_zero_of_degreeOn_fiber_eq_zero_of_isBiregular
    hY' hY hg hfib ⊤ trivial (by rwa [top_inf_eq]) hD hdeg
  exact ⟨U, hηU, hU⟩

end NumericalTriviality

end MMP.Fourfold
