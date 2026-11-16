/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.Surface.CurveMultiplicity
public import StacksFrontier.AlgebraicGeometry.HProjective.QuasiProjective
public import StacksFrontier.AlgebraicGeometry.HProjective.AffineBase
public import StacksFrontier.AlgebraicGeometry.AmpleAffineAvoidance.AmpleFiniteSet

/-!
# The semi-local ring of finitely many points of a curve (Kollár 1.20)

A finite set of points of a quasi-projective scheme over a field lies in an affine open (by
Stacks Tag 01ZY, through the ample invertible module given by quasi-projectivity over an affine
base). Consequently, for a finite nonempty set `P` of closed points of a quasi-projective curve
`C`, the semi-local ring `𝒪_{P,C}` is a localization of the coordinate ring of an affine open; it
is a Noetherian domain with fraction field `k(C)`, its maximal ideals are the `𝔪_p ∩ 𝒪_{P,C}`,
its localizations at them are the local rings `𝒪_{p,C}`, and it has finite colength over `k`.

## Main results

* `MMP.Resolution.exists_isAffineOpen_finite_subset`
* `MMP.Resolution.semilocalRing_properties`

## Implementation notes

Quasi-projectivity is Stacks' (Tag 01VW: of finite type with a relatively ample invertible
module), which over a field describes the locally closed subschemes of projective spaces.

## References

* [J. Kollár, *Lectures on resolution of singularities*][KollarResolution], 1.20
* [Stacks Project, Tag 01ZY](https://stacks.math.columbia.edu/tag/01ZY)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace MMP.Resolution

/-- **A finite set of points of a quasi-projective scheme lies in an affine open.** Let `X` be a
quasi-projective scheme over a field `k` (its structure morphism is quasi-projective, Stacks
Tag 01VW: of finite type with a relatively ample invertible module; over a field these are the
locally closed subschemes of some `ℙⁿ_k`) and `F ⊆ X` a finite set of points. Then there is an
affine open `U ⊆ X` with `F ⊆ U`. -/
@[mmp "lem_mmp_foundation_quasiprojective_finite_set_affine_open"]
theorem exists_isAffineOpen_finite_subset {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : Stacks.HProjective.IsQuasiProjective sX) {F : Set X}
    (hF : F.Finite) : ∃ U : X.Opens, IsAffineOpen U ∧ F ⊆ (U : Set X) := by
  obtain ⟨-, L, hL, hrel⟩ := hX
  exact Stacks.AmpleAffineAvoidance.exists_affineOpen_containing_finite_of_ample L
    (Stacks.HProjective.isAmple_of_isRelativelyAmple_of_isAffine sX L hrel) hF

/-! ### Semi-local rings as localizations inside a fraction field

Let `A` be a domain with fraction field `K` and `q i`, `i ∈ P`, finitely many primes of `A`. A
subring `R ⊆ K` whose elements are exactly those lying in every `A_{q i}` is the localization of
`A` at the elements outside every `q i` (prime avoidance); its maximal ideals are the extensions
of the maximal `q i`, and its quotients by nonzero elements are finite over a base field when `A`
is of finite type of dimension at most one. -/

namespace Semilocal

variable {A K : Type*} [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
  {ι : Type*} (P : Finset ι) (q : ι → Ideal A) (hq : ∀ i ∈ P, (q i).IsPrime)

/-- The elements of `A` outside every `q i`, `i ∈ P`. -/
def avoid : Submonoid A where
  carrier := {s | ∀ i ∈ P, s ∉ q i}
  one_mem' := fun i hi h => (hq i hi).ne_top ((Ideal.eq_top_iff_one _).2 h)
  mul_mem' := fun {_ _} ha hb i hi h => ((hq i hi).mem_or_mem h).elim (ha i hi) (hb i hi)

/-- Membership in `avoid P q hq`: lying outside every `q i`, `i ∈ P`. -/
@[simp]
theorem mem_avoid {s : A} : s ∈ avoid P q hq ↔ ∀ i ∈ P, s ∉ q i := Iff.rfl

variable (R : Subring K)
  (hR : ∀ x : K, x ∈ R ↔ ∀ i ∈ P, ∃ a s : A, s ∉ q i ∧ x * algebraMap A K s = algebraMap A K a)

omit [IsFractionRing A K] in
include hq hR in
/-- The image in `K` of every element of `A` lies in `R`. -/
theorem algebraMap_mem (a : A) : algebraMap A K a ∈ R :=
  (hR _).2 fun i hi => ⟨a, 1, fun h => (hq i hi).ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩

/-- The `A`-algebra structure of `R`. -/
@[instance_reducible]
def algA : Algebra A R :=
  ((algebraMap A K).codRestrict R (algebraMap_mem P q hq R hR)).toAlgebra

include hq hR in
/-- If `P` is nonempty, then `R` is the localization of `A` at `avoid P q hq`. -/
theorem isLocalization (hP : P.Nonempty) :
    letI := algA P q hq R hR
    IsLocalization (avoid P q hq) R := by
  let := algA P q hq R hR
  have hinj := IsFractionRing.injective A K
  constructor
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨i₀, hi₀⟩ := hP
    have hs0 : algebraMap A K s ≠ 0 := by
      rw [map_ne_zero_iff _ hinj]
      rintro rfl
      exact hs i₀ hi₀ (q i₀).zero_mem
    have hmem : (algebraMap A K s)⁻¹ ∈ R := (hR _).2 fun i hi =>
      ⟨1, s, hs i hi, by simp [hs0]⟩
    refine IsUnit.of_mul_eq_one (M := R) ⟨_, hmem⟩ (Subtype.ext ?_)
    change algebraMap A K s * (algebraMap A K s)⁻¹ = 1
    exact mul_inv_cancel₀ hs0
  · rintro ⟨x, hx⟩
    have hx' := (hR x).1 hx
    let J : Ideal A := Submodule.comap (LinearMap.toSpanSingleton A K x)
      (LinearMap.range (Algebra.linearMap A K))
    have hJ : ∀ s, s ∈ J ↔ ∃ a, algebraMap A K a = algebraMap A K s * x := by
      intro s
      simp [J, Algebra.smul_def]
    obtain ⟨i₀, hi₀⟩ := hP
    have hnot : ¬ ((J : Set A) ⊆ ⋃ i ∈ (↑P : Set ι), (q i : Set A)) := by
      intro h
      rw [Ideal.subset_union_prime i₀ i₀ (fun i hi _ _ => hq i hi)] at h
      obtain ⟨i, hi, hJi⟩ := h
      obtain ⟨a, s, hs, e⟩ := hx' i hi
      exact hs (hJi ((hJ s).2 ⟨a, by rw [← e, mul_comm]⟩))
    obtain ⟨s, hsJ, hsq⟩ := Set.not_subset.1 hnot
    simp only [Set.mem_iUnion, SetLike.mem_coe, not_exists] at hsq
    obtain ⟨a, ha⟩ := (hJ s).1 hsJ
    refine ⟨(a, ⟨s, fun i hi => hsq i hi⟩), Subtype.ext ?_⟩
    change x * algebraMap A K s = algebraMap A K a
    rw [ha, mul_comm]
  · intro a b h
    exact ⟨1, by rw [hinj (congrArg Subtype.val h)]⟩

include hq hR in
/-- If `A` is Noetherian and `P` is nonempty, then `R` is Noetherian. -/
theorem isNoetherianRing (hP : P.Nonempty) [IsNoetherianRing A] : IsNoetherianRing R := by
  let := algA P q hq R hR
  have := isLocalization P q hq R hR hP
  exact IsLocalization.isNoetherianRing (avoid P q hq) R inferInstance

include hq hR in
/-- If `P` is nonempty, then `K` is the fraction field of `R`. -/
theorem isFractionRing (hP : P.Nonempty) : IsFractionRing R K := by
  have : IsDomain A := (IsFractionRing.injective A K).isDomain (algebraMap A K)
  let := algA P q hq R hR
  have := isLocalization P q hq R hR hP
  have : IsScalarTower A R K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (avoid P q hq) R K

/-- The submonoid `avoid P q hq` is disjoint from `q i` for every `i ∈ P`. -/
theorem disjoint_avoid {i : ι} (hi : i ∈ P) : Disjoint (avoid P q hq : Set A) (q i) :=
  Set.disjoint_left.2 fun _ hs hsq => hs i hi hsq

include hq hR in
/-- If `P` is nonempty and `i ∈ P`, an element `r` of `R` lies in the extension of `q i` to `R`
iff `r * t = b` in `K` for some `b ∈ q i` and `t ∉ q i`. -/
theorem mem_map_iff (hP : P.Nonempty) {i : ι} (hi : i ∈ P) (r : R) :
    letI := algA P q hq R hR
    r ∈ (q i).map (algebraMap A R) ↔
      ∃ b t : A, b ∈ q i ∧ t ∉ q i ∧ (r : K) * algebraMap A K t = algebraMap A K b := by
  let := algA P q hq R hR
  have := isLocalization P q hq R hR hP
  rw [IsLocalization.mem_map_algebraMap_iff (avoid P q hq) R]
  constructor
  · rintro ⟨⟨⟨b, hb⟩, ⟨t, ht⟩⟩, e⟩
    exact ⟨b, t, hb, ht i hi, congrArg Subtype.val e⟩
  · rintro ⟨b, t, hb, ht, e⟩
    obtain ⟨⟨c, ⟨u, hu⟩⟩, e'⟩ := IsLocalization.surj (avoid P q hq) r
    have e'' : (r : K) * algebraMap A K u = algebraMap A K c := congrArg Subtype.val e'
    have hinj := IsFractionRing.injective A K
    have hct : c * t = b * u := hinj <| by
      rw [map_mul, map_mul, ← e'', ← e]
      ring
    have hc : c ∈ q i := by
      have : c * t ∈ q i := hct ▸ (q i).mul_mem_right u hb
      exact ((hq i hi).mem_or_mem this).resolve_right ht
    exact ⟨⟨⟨c, hc⟩, ⟨u, hu⟩⟩, e'⟩

include hq hR in
/-- If `P` is nonempty and every `q i`, `i ∈ P`, is maximal, then the maximal ideals of `R` are
exactly the extensions to `R` of the ideals `q i`, `i ∈ P`. -/
theorem isMaximal_iff (hP : P.Nonempty) (hmax : ∀ i ∈ P, (q i).IsMaximal) (M : Ideal R) :
    letI := algA P q hq R hR
    M.IsMaximal ↔ ∃ i ∈ P, M = (q i).map (algebraMap A R) := by
  let := algA P q hq R hR
  have := isLocalization P q hq R hR hP
  have hmaxmap : ∀ i ∈ P, ((q i).map (algebraMap A R)).IsMaximal := fun i hi => by
    have := hmax i hi
    exact IsLocalization.isMaximal_of_isMaximal_disjoint (avoid P q hq) R (q i)
      (disjoint_avoid P q hq hi)
  constructor
  · intro hM
    obtain ⟨i₀, hi₀⟩ := hP
    let Q := M.comap (algebraMap A R)
    have hQ : (Q : Set A) ⊆ ⋃ i ∈ (↑P : Set ι), (q i : Set A) := by
      intro x hx
      by_contra hxu
      simp only [Set.mem_iUnion, SetLike.mem_coe, not_exists] at hxu
      have hu : IsUnit (algebraMap A R x) :=
        IsLocalization.map_units R (⟨x, fun i hi => hxu i hi⟩ : avoid P q hq)
      exact hM.ne_top (M.eq_top_of_isUnit_mem hx hu)
    rw [Ideal.subset_union_prime i₀ i₀ (fun i hi _ _ => hq i hi)] at hQ
    obtain ⟨i, hi, hQi⟩ := hQ
    refine ⟨i, hi, ?_⟩
    have hle : M ≤ (q i).map (algebraMap A R) := by
      rw [← IsLocalization.map_under (avoid P q hq) R M]
      exact Ideal.map_mono hQi
    exact hM.eq_of_le (hmaxmap i hi).ne_top hle
  · rintro ⟨i, hi, rfl⟩
    exact hmaxmap i hi

include hq hR in
/-- For `i ∈ P`, an element `x` of `K` is a fraction `a / s` with `a, s ∈ A` and `s ∉ q i` iff
`x * s = r` for some `r, s ∈ R` such that `s` is not of the form `b / t` with `b ∈ q i` and
`t ∉ q i`. -/
theorem mem_loc_iff {i : ι} (hi : i ∈ P) (x : K) :
    (∃ a s : A, s ∉ q i ∧ x * algebraMap A K s = algebraMap A K a) ↔
      ∃ r s : R, ¬ (∃ b t : A, b ∈ q i ∧ t ∉ q i ∧ (s : K) * algebraMap A K t = algebraMap A K b) ∧
        x * (s : K) = r := by
  have hinj := IsFractionRing.injective A K
  constructor
  · rintro ⟨a, s, hs, e⟩
    refine ⟨⟨_, algebraMap_mem P q hq R hR a⟩, ⟨_, algebraMap_mem P q hq R hR s⟩, ?_, e⟩
    rintro ⟨b, t, hb, ht, e'⟩
    have : s * t = b := hinj (by rwa [map_mul])
    exact ((hq i hi).mem_or_mem (this ▸ hb)).elim hs ht
  · rintro ⟨r, s, hs, e⟩
    obtain ⟨a, u, hu, eu⟩ := (hR r).1 r.2 i hi
    obtain ⟨c, v, hv, ev⟩ := (hR s).1 s.2 i hi
    have hc : c ∉ q i := fun hc => hs ⟨c, v, hc, hv, ev⟩
    refine ⟨a * v, u * c, fun h => ((hq i hi).mem_or_mem h).elim hu hc, ?_⟩
    rw [map_mul, map_mul, ← eu, ← ev, ← e]
    ring

/-- In a Noetherian ring of Krull dimension at most one, the quotient by a nonzero divisor is
Artinian. -/
theorem isArtinianRing_quotient_span_singleton {A : Type*} [CommRing A] [IsNoetherianRing A]
    [Ring.KrullDimLE 1 A] {a : A} (ha : a ∈ nonZeroDivisors A) :
    IsArtinianRing (A ⧸ Ideal.span {a}) := by
  have hdim : Ring.KrullDimLE 0 (A ⧸ Ideal.span {a}) := by
    rw [Ring.KrullDimLE, Order.krullDimLE_iff,
      ← ENat.WithBot.add_le_add_one_right_iff, Nat.cast_zero, zero_add]
    exact (ringKrullDim_quotient_succ_le_of_nonZeroDivisor ha).trans
      (Order.KrullDimLE.krullDim_le)
  exact isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.2 ⟨inferInstance, hdim⟩

/-- If `R` is a localization of `A` and `A ⧸ (a)` is Artinian, then every element of `R` is
congruent modulo `a` to the image of an element of `A`. -/
theorem exists_algebraMap_sub_mem_span_singleton {A R : Type*} [CommRing A] [CommRing R]
    [Algebra A R] (M : Submonoid A) [IsLocalization M R] (a : A)
    [IsArtinianRing (A ⧸ Ideal.span {a})] (x : R) :
    ∃ y : A, algebraMap A R y - x ∈ Ideal.span {algebraMap A R a} := by
  obtain ⟨⟨b, ⟨u, hu⟩⟩, ex⟩ := IsLocalization.surj M x
  have hU : IsUnit (algebraMap A R u) := IsLocalization.map_units R (⟨u, hu⟩ : M)
  obtain ⟨v, hv⟩ : ∃ v : R, algebraMap A R u * v = 1 := ⟨_, hU.mul_val_inv⟩
  obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd
    (Ideal.Quotient.mk (Ideal.span {a}) u) (1 : A ⧸ Ideal.span {a})
  obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective y
  have hy' : u ^ (n + 1) * y' - u ^ n ∈ Ideal.span {a} := by
    rw [← Ideal.Quotient.eq]
    simpa using hy
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hy'
  refine ⟨b * y', Ideal.mem_span_singleton'.2 ?_⟩
  set U := algebraMap A R u
  have e3 : U ^ (n + 1) * algebraMap A R y' - U ^ n = algebraMap A R w * algebraMap A R a := by
    have := congrArg (algebraMap A R) hw
    simp only [map_mul, map_sub, map_pow] at this
    rw [← this]
  have e4 : U * algebraMap A R y' - 1 = algebraMap A R a * (algebraMap A R w * v ^ n) := by
    calc U * algebraMap A R y' - 1 = (U * v) ^ n * (U * algebraMap A R y' - 1) := by
          rw [hv, one_pow, one_mul]
      _ = (U ^ (n + 1) * algebraMap A R y' - U ^ n) * v ^ n := by ring
      _ = _ := by
          rw [e3]
          ring
  simp only at ex
  refine ⟨algebraMap A R b * v * algebraMap A R w * v ^ n, ?_⟩
  rw [map_mul]
  linear_combination -(algebraMap A R b * v) * e4 + v * ex +
    (algebraMap A R b * algebraMap A R y' - x) * hv

section FiniteColength

variable (k : Type*) [Field k] [Algebra k A] [Algebra k R]
  (hcompat : ∀ c : k, ((algebraMap k R c : R) : K) = algebraMap A K (algebraMap k A c))

include hq hR hcompat in
/-- Let `A` be of finite type and of Krull dimension at most one over a field `k`, and
let `R` carry a `k`-algebra structure compatible with that of `A`. If `P` is nonempty, then for
every nonzero divisor `r` of `R` the quotient `R ⧸ (r)` is a finite-dimensional `k`-vector
space. -/
theorem finite_quotient_span_singleton (hP : P.Nonempty) [Algebra.FiniteType k A]
    [Ring.KrullDimLE 1 A] (r : R) (hr : r ∈ nonZeroDivisors R) :
    Module.Finite k (R ⧸ Ideal.span {r}) := by
  have : IsDomain A := (IsFractionRing.injective A K).isDomain (algebraMap A K)
  let := algA P q hq R hR
  have hloc := isLocalization P q hq R hR hP
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  obtain ⟨⟨a, ⟨u, hu⟩⟩, e⟩ := IsLocalization.surj (avoid P q hq) r
  have hU : IsUnit (algebraMap A R u) := IsLocalization.map_units R (⟨u, hu⟩ : avoid P q hq)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at e
    exact nonZeroDivisors.ne_zero hr ((hU.mul_left_eq_zero).1 e)
  have hspan : Ideal.span {r} = Ideal.span {algebraMap A R a} := by
    rw [← e, Ideal.span_singleton_mul_right_unit hU]
  rw [hspan]
  set I : Ideal R := Ideal.span {algebraMap A R a}
  have := isArtinianRing_quotient_span_singleton (mem_nonZeroDivisors_of_ne_zero ha0)
  have : Module.Finite k (A ⧸ Ideal.span {a}) := Module.finite_of_isArtinianRing k _
  let g : A →ₐ[k] R :=
    { algebraMap A R with commutes' := fun c => Subtype.ext (hcompat c).symm }
  let f : (A ⧸ Ideal.span {a}) →ₐ[k] R ⧸ I :=
    Ideal.Quotient.liftₐ (Ideal.span {a}) ((Ideal.Quotient.mkₐ k I).comp g) (by
      intro y hy
      obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hy
      change Ideal.Quotient.mk I (algebraMap A R (w * a)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, map_mul]
      exact I.mul_mem_left _ (Ideal.subset_span rfl))
  refine Module.Finite.of_surjective f.toLinearMap fun z => ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨y, hy⟩ := exists_algebraMap_sub_mem_span_singleton (avoid P q hq) a x
  refine ⟨Ideal.Quotient.mk _ y, ?_⟩
  change Ideal.Quotient.mk I (algebraMap A R y) = Ideal.Quotient.mk I x
  exact Ideal.Quotient.eq.2 hy

end FiniteColength

end Semilocal

/-- Let `O` be the localization of `A` at a prime `q`, with `A → K` injective. An element `x` of
`K` lies in the image of `O` iff `x * s = a` in `K` for some `a, s ∈ A` with `s ∉ q`. -/
theorem mem_range_algebraMap_iff_of_isLocalization {A O K : Type*} [CommRing A] [CommRing O]
    [Field K] [Algebra A O] [Algebra O K] [Algebra A K] [IsScalarTower A O K] (q : Ideal A)
    [q.IsPrime] [IsLocalization.AtPrime O q] (hinj : Function.Injective (algebraMap A K)) (x : K) :
    x ∈ (algebraMap O K).range ↔ ∃ a s : A, s ∉ q ∧ x * algebraMap A K s = algebraMap A K a := by
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨⟨a, s⟩, e⟩ := IsLocalization.surj q.primeCompl y
    refine ⟨a, s, s.2, ?_⟩
    have := congrArg (algebraMap O K) e
    rwa [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at this
  · rintro ⟨a, s, hs, e⟩
    refine ⟨IsLocalization.mk' O a (⟨s, hs⟩ : q.primeCompl), ?_⟩
    have hs0 : algebraMap A K s ≠ 0 := by
      rw [map_ne_zero_iff _ hinj]
      rintro rfl
      exact hs q.zero_mem
    apply mul_right_cancel₀ hs0
    rw [e, IsScalarTower.algebraMap_apply A O K s, ← map_mul]
    have hspec := IsLocalization.mk'_spec O a (⟨s, hs⟩ : q.primeCompl)
    simp only at hspec
    rw [hspec, ← IsScalarTower.algebraMap_apply]

/-- Let `O` be the localization of `A` at a prime `q`, with `A → K` injective. An element `x` of
`K` is the image of an element of the maximal ideal of `O` iff `x * t = b` in `K` for some
`b ∈ q` and `t ∉ q`. -/
theorem exists_mem_maximalIdeal_algebraMap_eq_iff {A O K : Type*} [CommRing A] [CommRing O]
    [Field K] [Algebra A O] [Algebra O K] [Algebra A K] [IsScalarTower A O K] (q : Ideal A)
    [q.IsPrime] [IsLocalization.AtPrime O q] [IsLocalRing O]
    (hinj : Function.Injective (algebraMap A K)) (x : K) :
    (∃ a ∈ IsLocalRing.maximalIdeal O, algebraMap O K a = x) ↔
      ∃ b t : A, b ∈ q ∧ t ∉ q ∧ x * algebraMap A K t = algebraMap A K b := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q O]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [IsLocalization.mem_map_algebraMap_iff q.primeCompl O] at hy
    obtain ⟨⟨⟨b, hb⟩, ⟨t, ht⟩⟩, e⟩ := hy
    refine ⟨b, t, hb, ht, ?_⟩
    have := congrArg (algebraMap O K) e
    rwa [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at this
  · rintro ⟨b, t, hb, ht, e⟩
    refine ⟨IsLocalization.mk' O b (⟨t, ht⟩ : q.primeCompl), ?_, ?_⟩
    · rw [IsLocalization.mem_map_algebraMap_iff q.primeCompl O]
      exact ⟨⟨⟨b, hb⟩, ⟨t, ht⟩⟩, IsLocalization.mk'_spec _ _ _⟩
    · have ht0 : algebraMap A K t ≠ 0 := by
        rw [map_ne_zero_iff _ hinj]
        rintro rfl
        exact ht q.zero_mem
      apply mul_right_cancel₀ ht0
      rw [e, IsScalarTower.algebraMap_apply A O K t, ← map_mul]
      have hspec := IsLocalization.mk'_spec O b (⟨t, ht⟩ : q.primeCompl)
      simp only at hspec
      rw [hspec, ← IsScalarTower.algebraMap_apply]

/-- For an affine open `U` of an integral scheme and `p ∈ U` with prime `q` of `Γ(X, U)`, an
element of the function field lies in the image of the stalk at `p` iff it is a fraction `a / s`
of sections over `U` with `s ∉ q`. -/
theorem mem_range_algebraMap_stalk_iff {X : Scheme.{u}} [IsIntegral X] {U : X.Opens}
    [Nonempty U] (hU : IsAffineOpen U) {p : X} (hp : p ∈ U) {q : Ideal Γ(X, U)}
    (hq : q = (hU.primeIdealOf ⟨p, hp⟩).asIdeal) (x : X.functionField) :
    x ∈ (algebraMap (X.presheaf.stalk p) X.functionField).range ↔
      ∃ a s : Γ(X, U), s ∉ q ∧
        x * algebraMap Γ(X, U) X.functionField s = algebraMap Γ(X, U) X.functionField a := by
  let := X.presheaf.algebra_section_stalk ⟨p, hp⟩
  have := hU.isLocalization_stalk ⟨p, hp⟩
  have := functionField_isScalarTower X U ⟨p, hp⟩
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  subst hq
  exact mem_range_algebraMap_iff_of_isLocalization _ (IsFractionRing.injective _ _) x

/-- For an affine open `U` of an integral scheme and `p ∈ U` with prime `q` of `Γ(X, U)`, an
element of the function field is the image of an element of the maximal ideal of the stalk at `p`
iff it is a fraction `b / t` of sections over `U` with `b ∈ q` and `t ∉ q`. -/
theorem exists_mem_maximalIdeal_stalk_algebraMap_eq_iff {X : Scheme.{u}} [IsIntegral X]
    {U : X.Opens} [Nonempty U] (hU : IsAffineOpen U) {p : X} (hp : p ∈ U) {q : Ideal Γ(X, U)}
    (hq : q = (hU.primeIdealOf ⟨p, hp⟩).asIdeal) (x : X.functionField) :
    (∃ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk p),
        algebraMap (X.presheaf.stalk p) X.functionField a = x) ↔
      ∃ b t : Γ(X, U), b ∈ q ∧ t ∉ q ∧
        x * algebraMap Γ(X, U) X.functionField t = algebraMap Γ(X, U) X.functionField b := by
  let := X.presheaf.algebra_section_stalk ⟨p, hp⟩
  have := hU.isLocalization_stalk ⟨p, hp⟩
  have := functionField_isScalarTower X U ⟨p, hp⟩
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  subst hq
  exact exists_mem_maximalIdeal_algebraMap_eq_iff _ (IsFractionRing.injective _ _) x

/-- The ring of sections over an affine open of a scheme of dimension at most one has Krull
dimension at most one. -/
theorem krullDimLE_one_of_isAffineOpen {X : Scheme.{u}} (hX : topologicalKrullDim X ≤ 1)
    {U : X.Opens} (hU : IsAffineOpen U) : Ring.KrullDimLE 1 Γ(X, U) := by
  rw [Ring.krullDimLE_iff, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(X, U)]
  change topologicalKrullDim (Spec Γ(X, U)) ≤ _
  rw [← IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph]
  exact (topologicalKrullDim_subspace_le X U).trans hX

/-- **Kollár 1.20, pp. 16–17: the semi-local ring of finitely many points of a curve.** Let `C` be
a quasi-projective curve over a field `k` (an integral quasi-projective `k`-scheme of dimension
`1`), `P = {p₁, …, p_n}` a finite nonempty set of closed points and `R = 𝒪_{P,C}` its semi-local
ring. Then `R` is a Noetherian domain with fraction field `k(C)`; its maximal ideals are exactly
the ideals `𝔪_{p_i} ∩ R`; the localization of `R` at `𝔪_{p_i} ∩ R` is `𝒪_{p_i,C}` (as subrings
of `k(C)`: the fractions `r / s` with `r, s ∈ R`, `s ∉ 𝔪_{p_i}`); and `R` is a `k`-algebra of
finite colength. -/
@[mmp "lem_kr1a_semilocal_ring_of_points_properties"]
theorem semilocalRing_properties {k : Type u} [Field k] {C : Scheme.{u}} [IsIntegral C]
    (sC : C ⟶ Spec (.of k)) (hC : Stacks.HProjective.IsQuasiProjective sC)
    (hdim : topologicalKrullDim C = 1) (P : Finset C) (hP : P.Nonempty)
    (hPc : ∀ p ∈ P, IsClosed ({p} : Set C)) :
    IsNoetherianRing (semilocalRing P) ∧ IsDomain (semilocalRing P) ∧
      IsFractionRing (semilocalRing P) C.functionField ∧
      (∀ M : Ideal (semilocalRing P), M.IsMaximal ↔ ∃ p ∈ P, ∀ r : semilocalRing P,
        r ∈ M ↔ ∃ a ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk p),
          algebraMap _ C.functionField a = r) ∧
      (∀ p ∈ P, ((algebraMap (C.presheaf.stalk p) C.functionField).range : Set C.functionField) =
        {x : C.functionField | ∃ r s : semilocalRing P,
          (∀ a ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk p),
            algebraMap _ C.functionField a ≠ s) ∧ x * (s : C.functionField) = r}) ∧
      letI := semilocalRingAlgebra sC P
      IsFiniteColength k (semilocalRing P) := by
  classical
  obtain ⟨U, hU, hPU⟩ := exists_isAffineOpen_finite_subset sC hC P.finite_toSet
  have hPU' : ∀ p ∈ P, p ∈ U := fun p hp => hPU hp
  have : Nonempty U := ⟨⟨_, hPU' _ hP.choose_spec⟩⟩
  have hfr : IsFractionRing Γ(C, U) C.functionField :=
    functionField_isFractionRing_of_isAffineOpen C U hU
  let q : C → Ideal Γ(C, U) := fun p =>
    if h : p ∈ U then (hU.primeIdealOf ⟨p, h⟩).asIdeal else ⊤
  have hqp : ∀ p (h : p ∈ U), q p = (hU.primeIdealOf ⟨p, h⟩).asIdeal := fun p h =>
    dif_pos h
  have hq : ∀ p ∈ P, (q p).IsPrime := fun p hp => hqp p (hPU' p hp) ▸ inferInstance
  have hmax : ∀ p ∈ P, (q p).IsMaximal := fun p hp =>
    hqp p (hPU' p hp) ▸ hU.primeIdealOf_isMaximal_of_isClosed ⟨p, hPU' p hp⟩ (hPc p hp)
  have hloc := fun p (hp : p ∈ P) =>
    mem_range_algebraMap_stalk_iff hU (hPU' p hp) (hqp p (hPU' p hp))
  have hm := fun p (hp : p ∈ P) =>
    exists_mem_maximalIdeal_stalk_algebraMap_eq_iff hU (hPU' p hp) (hqp p (hPU' p hp))
  have hR : ∀ x : C.functionField, x ∈ semilocalRing P ↔ ∀ p ∈ P, ∃ a s : Γ(C, U), s ∉ q p ∧
      x * algebraMap Γ(C, U) C.functionField s = algebraMap Γ(C, U) C.functionField a := fun x => by
    simpa only [semilocalRing, Subring.mem_iInf] using forall₂_congr fun p hp => hloc p hp x
  let : Algebra k Γ(C, U) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ sC.appLE ⊤ U (by simp)).hom.toAlgebra
  have : LocallyOfFiniteType sC := hC.locallyOfFiniteType
  have hft : Algebra.FiniteType k Γ(C, U) := by
    have h2 : (Scheme.ΓSpecIso (.of k)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2
    exact (sC.finiteType_appLE (isAffineOpen_top _) hU (by simp)).comp h2
  have := krullDimLE_one_of_isAffineOpen hdim.le hU
  have : IsNoetherianRing Γ(C, U) := Algebra.FiniteType.isNoetherianRing k Γ(C, U)
  refine ⟨Semilocal.isNoetherianRing P q hq _ hR hP, inferInstance,
    Semilocal.isFractionRing P q hq _ hR hP, ?_, ?_, ?_⟩
  · intro M
    rw [Semilocal.isMaximal_iff P q hq _ hR hP hmax M]
    refine exists_congr fun p => and_congr_right fun hp => ?_
    rw [Ideal.ext_iff]
    exact forall_congr' fun r => by rw [Semilocal.mem_map_iff P q hq _ hR hP hp r, hm p hp]
  · intro p hp
    ext x
    rw [SetLike.mem_coe, hloc p hp x, Semilocal.mem_loc_iff P q hq _ hR hp x]
    simp only [Set.mem_ofPred_eq, ← hm p hp, not_exists, not_and]
  · let := semilocalRingAlgebra sC P
    refine fun r hr => Semilocal.finite_quotient_span_singleton P q hq _ hR k (fun c => ?_) hP r hr
    change ((Scheme.ΓSpecIso (.of k)).inv ≫ sC.appTop ≫ C.presheaf.germ ⊤ _ _).hom c =
      (((Scheme.ΓSpecIso (.of k)).inv ≫ sC.appLE ⊤ U _) ≫ C.germToFunctionField U).hom c
    congr 2
    simp only [Scheme.Hom.appLE, Scheme.germToFunctionField, Category.assoc,
      TopCat.Presheaf.germ_res]
    rfl

end MMP.Resolution
