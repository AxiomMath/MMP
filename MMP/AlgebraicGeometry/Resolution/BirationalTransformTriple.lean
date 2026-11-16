/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.Sequence
public import MMP.AlgebraicGeometry.Resolution.OneBlowupTotalTransform
public import MMP.AlgebraicGeometry.Resolution.SNCPullback
public import MMP.AlgebraicGeometry.Resolution.ExceptionalDivisorPrime
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.GenericPoints
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyLocallyClosed
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.StalkPrimes

/-!
# The transform of a triple is a triple

Let `(X, I, E)` be a triple (Kollár, Notation 3.64): `X` smooth, equidimensional and of finite type
over a field `k` of characteristic `0`, `I` an ideal sheaf nonzero at the generic points of `X` and
`E = (E^1, …, E^s)` an ordered simple normal crossing divisor. Let `Z ⊆ X` be a closed subscheme
having simple normal crossings with `∑ᵢ E^i`, and `π : B = B_ZX → X` its blow-up. Then
`(B, π⁻¹_{Z*}I, π⁻¹_tot(E))` is a triple, and so is `(B, π⁻¹_{Z*}(I, m), π⁻¹_tot(E))` for every
marking `m`: their marked versions are marked triples.

`Z` is smooth, so `B` is smooth over `k`; it is of finite type since `π` is proper. Every generic
point of `B` lies off the exceptional divisor, where `π` is an isomorphism, over a generic point of
`X` (Stacks, Tag 0BFM). Hence an irreducible component `B_0` of `B` and the component of `X` under
it contain homeomorphic nonempty open parts, so they have the same dimension and `B` is
equidimensional; and the inverse image `π^*I`, which is contained in both transforms of `I`, is
nonzero at the generic points of `B`.

The entries of `π⁻¹_tot(E)` are checked point by point. Let `x' ∈ B` and `x = π(x')`. If
`x ∉ Z`, `π` is a local isomorphism at `x'` and the entries through `x'` are the inverse images of
the `E^i` through `x`. If `x ∈ Z`, take local coordinates `z_1, …, z_n` at `x` with
`E^i = (z_{c(i)} = 0)` and `Z = (z_j = 0 : j ∈ J)` near `x`, and the coordinates `w` at `x'` of a
chart `D_+(z_m)`, `m ∈ J`, of the blow-up of `(z_j)_{j ∈ J}`: `z_m = w_{i₀}` is the local
equation of the exceptional divisor, `z_j = w_{σ(j)}` for `j ∉ J` and `z_j = w_{σ(j)} w_{i₀}` or
`z_j = (unit)·w_{i₀}` for `j ∈ J ∖ {m}`. The component of `Z` through `x` is the closure of the
point of the prime `(z_j : j ∈ J)`; it has codimension `≥ 2` when `|J| ≥ 2`, and it is a
component of `Supp E` when `J = {c(i)}`. On `Spec 𝒪_{B,x'}`, the `i`-th entry
`π⁻¹(E^i ∖ Z^{≥2})‾` is then `(w_{σ(c(i))} = 0)`, `(w_{i₀} = 0)` or empty, and the last entry is
`(w_{i₀} = 0)` or empty. Distinct entries receive distinct coordinates: the stalk map
`𝒪_{X,x} → 𝒪_{B,x'}` is injective (the generic point of `Spec 𝒪_{B,x'}` is a generic point of
`B`), so the `σ(j)`, `j ∉ U ∪ {m}`, are distinct. Finally the stalk at `x'` of the reduced ideal of
a closed set whose inverse image in `Spec 𝒪_{B,x'}` is `(w_c = 0)` is `(w_c)`, and a closed
subscheme cut out near each of its points by one regular parameter is reduced, smooth, of pure
codimension one and an effective Cartier divisor.

## Main results

* `MMP.Resolution.isTriple_controlledTransform_totalTransform`: the transform
  `(B_ZX, π⁻¹_{Z*}I, π⁻¹_tot(E))` of a triple is a triple.
* `MMP.Resolution.isTriple_birationalTransform_totalTransform`: the transform
  `(B_ZX, π⁻¹_{Z*}(I, m), π⁻¹_tot(E))` of a marked triple is a marked triple.
* `MMP.Resolution.isOrderedSNC_totalTransform`: the total transform of an ordered snc divisor
  under the blow-up of a centre having snc with it is an ordered snc divisor.
* `MMP.Resolution.equidimensional_blowUp`: a blow-up of an equidimensional scheme locally of
  finite type over a field is equidimensional.
* `MMP.Resolution.injective_stalkMap_blowUpToBase`: the stalk maps of a blow-up between integral
  local rings are injective.

## Implementation notes

The source assumes that every irreducible component of `Z` has codimension `≥ 1`, and, for the
marked statement, that `ord_Z I ≥ m`. Neither is used: both transforms of `I` contain `π^*I`
(they are ideal quotients of `π^*I`), which is already nonzero at the generic points of `B`, and
the conditions on `E` and `Z` do not involve `I`. The statements are therefore proved without
these hypotheses. Smoothness of `Z` is a consequence of its having simple normal crossings with
`E`.

## References

* [J. Kollár, *Lectures on resolution of singularities*, Notation 3.64, Def. 3.65–3.66]
* [Stacks Project, Tag 0BFM](https://stacks.math.columbia.edu/tag/0BFM)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Resolution

section Stalks

variable {Y : Scheme.{u}}

/-- The stalk of the ideal sheaf of a reduced closed subscheme is a radical ideal. -/
theorem isRadical_stalk_vanishingIdeal (T : Closeds Y) (y : Y) :
    (IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal T) y).IsRadical := by
  set D := Scheme.IdealSheafData.vanishingIdeal T
  by_cases hy : y ∈ D.support
  · obtain ⟨z, rfl⟩ : ∃ z, D.subschemeι z = y := by
      rwa [← SetLike.mem_coe, ← D.range_subschemeι] at hy
    have : IsReduced D.subscheme := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
    exact (Ideal.isRadical_iff_quotient_reduced _).mpr <| isReduced_of_injective
      (MMP.Flips.ResolutionInputs.stalkQuotientEquiv D z) (RingEquiv.injective _)
  · rw [(IdealSheafData.stalk_eq_top_iff_notMem_support D y).2 hy]
    exact le_top

/-- If the inverse image of a closed set `T` in `Spec 𝒪_{Y,y}` is the zero locus of an element
`a` generating a prime ideal, then the stalk at `y` of the reduced ideal of `T` is `(a)`. -/
theorem stalk_vanishingIdeal_eq_span_singleton (T : Closeds Y) (y : Y)
    {a : Y.presheaf.stalk y} (ha : (Ideal.span {a}).IsPrime)
    (hT : ∀ p : PrimeSpectrum (Y.presheaf.stalk y),
      Y.fromSpecStalk y p ∈ (T : Set Y) ↔ a ∈ p.asIdeal) :
    IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal T) y = Ideal.span {a} := by
  set K := IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal T) y
  have hzl : PrimeSpectrum.zeroLocus (K : Set (Y.presheaf.stalk y)) =
      PrimeSpectrum.zeroLocus ((Ideal.span {a} : Ideal _) : Set (Y.presheaf.stalk y)) := by
    rw [← preimage_fromSpecStalk_support, Scheme.IdealSheafData.coe_support_vanishingIdeal,
      PrimeSpectrum.zeroLocus_span]
    ext (p : PrimeSpectrum (Y.presheaf.stalk y))
    change Y.fromSpecStalk y p ∈ (T : Set Y) ↔ {a} ⊆ (p.asIdeal : Set _)
    rw [Set.singleton_subset_iff]
    exact hT p
  calc K = K.radical := (isRadical_stalk_vanishingIdeal T y).radical.symm
    _ = (Ideal.span {a}).radical := by
      rw [← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical,
        ← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, hzl]
    _ = Ideal.span {a} := ha.radical

/-- The points of `Spec 𝒪_{Y,y}` lying over the closure of the image of a point `q` are those
specializing `q`. -/
theorem fromSpecStalk_mem_closure_iff (y : Y) (q p : PrimeSpectrum (Y.presheaf.stalk y)) :
    Y.fromSpecStalk y p ∈ closure {Y.fromSpecStalk y q} ↔ q.asIdeal ≤ p.asIdeal := by
  rw [← specializes_iff_mem_closure]
  exact (Y.fromSpecStalk y).isEmbedding.isInducing.specializes_iff.trans
    (PrimeSpectrum.le_iff_specializes q p).symm

/-- A point of `Spec 𝒪_{Y,y}` specializes to the closed point, so its image specializes to `y`. -/
theorem fromSpecStalk_specializes_self (y : Y) (p : PrimeSpectrum (Y.presheaf.stalk y)) :
    Y.fromSpecStalk y p ⤳ y :=
  Scheme.range_fromSpecStalk.subset ⟨p, rfl⟩

/-- Every generization of `y` is the image of a point of `Spec 𝒪_{Y,y}`. -/
theorem exists_fromSpecStalk_eq_of_specializes {y η : Y} (h : η ⤳ y) :
    ∃ q : PrimeSpectrum (Y.presheaf.stalk y), Y.fromSpecStalk y q = η :=
  Scheme.range_fromSpecStalk.ge h

end Stalks

section Closure

variable {Y : Scheme.{u}} [NoetherianSpace Y]

/-- In a Noetherian scheme, a point of the closure of `A ∖ B`, `A` and `B` closed, is a
specialization of a point of `A ∖ B`. -/
theorem exists_specializes_of_mem_closure_diff {A B : Set Y} (hA : IsClosed A) (hB : IsClosed B)
    {t : Y} (ht : t ∈ closure (A \ B)) : ∃ s ∈ A \ B, s ⤳ t := by
  obtain ⟨hfin, hcov⟩ := Aux.finite_and_cover_componentsOf hA
  set C := ⋃₀ {W | W ∈ componentsOf A ∧ ¬ W ⊆ B}
  have hC : IsClosed C :=
    (hfin.subset fun W hW => hW.1).isClosed_sUnion fun W hW =>
      Aux.isClosed_of_mem_componentsOf hA hW.1
  have hsub : A \ B ⊆ C := by
    rintro a ⟨haA, haB⟩
    obtain ⟨W, hW, haW⟩ := hcov haA
    exact ⟨W, ⟨hW, fun h => haB (h haW)⟩, haW⟩
  obtain ⟨W, ⟨hW, hWB⟩, htW⟩ := closure_minimal hsub hC ht
  obtain ⟨ξ, hξA, rfl⟩ := Aux.exists_eq_closure_of_mem_componentsOf hA hW
  refine ⟨ξ, ⟨hξA, fun hξB => hWB (closure_minimal (Set.singleton_subset_iff.2 hξB) hB)⟩,
    specializes_iff_mem_closure.2 htW⟩

end Closure

section RSOP

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- The ideal generated by some members of a regular system of parameters is prime. -/
theorem span_image_isPrime_of_isRegularSystemOfParameters {m : ℕ} {w : Fin m → R}
    (hw : IsRegularSystemOfParameters w) (s : Finset (Fin m)) :
    (Ideal.span (w '' (s : Set (Fin m)))).IsPrime := by
  have := isRegularLocalRing_of_isRegularSystemOfParameters hw
  obtain ⟨hreg, -, -⟩ := MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_quotient_image hw s
  have := IsRegularLocalRing.isDomain (R ⧸ Ideal.span (w '' (s : Set (Fin m))))
  exact (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance

/-- A member of a regular system of parameters generates a prime ideal. -/
theorem span_singleton_isPrime_of_isRegularSystemOfParameters {m : ℕ} {w : Fin m → R}
    (hw : IsRegularSystemOfParameters w) (j : Fin m) : (Ideal.span {w j}).IsPrime := by
  have h := span_image_isPrime_of_isRegularSystemOfParameters hw {j}
  rwa [Finset.coe_singleton, Set.image_singleton] at h

/-- A member of a regular system of parameters is not a multiple of another member. -/
theorem notMem_span_singleton_of_ne_of_isRegularSystemOfParameters {m : ℕ} {w : Fin m → R}
    (hw : IsRegularSystemOfParameters w) {i j : Fin m} (hij : i ≠ j) :
    w j ∉ Ideal.span {w i} := by
  classical
  intro hmem
  have := isRegularLocalRing_of_isRegularSystemOfParameters hw
  set s : Set R := w '' ({j}ᶜ : Set (Fin m)) with hs
  have hspan : Ideal.span s = maximalIdeal R := by
    rw [← hw.1]
    refine le_antisymm (Ideal.span_mono ?_) (Ideal.span_le.2 ?_)
    · rintro _ ⟨l, -, rfl⟩
      exact ⟨l, rfl⟩
    · rintro _ ⟨l, rfl⟩
      obtain rfl | hl := eq_or_ne l j
      · have hi : w i ∈ s := ⟨i, hij, rfl⟩
        exact Ideal.span_mono (Set.singleton_subset_iff.2 hi) hmem
      · exact Ideal.subset_span ⟨l, hl, rfl⟩
  have hle := Submodule.spanFinrank_span_le_ncard_of_finite (R := R) (Set.toFinite s)
  rw [show Submodule.span R s = maximalIdeal R from hspan] at hle
  have hcard : s.ncard ≤ m - 1 := by
    rw [hs]
    refine (Set.ncard_image_le (Set.toFinite _)).trans ?_
    rw [Set.ncard_eq_toFinset_card']
    simp [Finset.card_compl]
  have hrank := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
  rw [hw.2] at hrank
  have : (maximalIdeal R).spanFinrank = m := by exact_mod_cast hrank
  have := j.2
  omega

/-- Members of a regular system of parameters at distinct indices are distinct. -/
theorem ne_of_isRegularSystemOfParameters {m : ℕ} {w : Fin m → R}
    (hw : IsRegularSystemOfParameters w) {i j : Fin m} (hij : i ≠ j) : w i ≠ w j := fun h =>
  notMem_span_singleton_of_ne_of_isRegularSystemOfParameters hw hij (h ▸ Ideal.subset_span rfl)

/-- In a blow-up chart, the coordinates `w_{σ(a)}` attached to the indices `a ∉ U ∪ {m}` are
pairwise distinct: `φ(z_a)` is `w_{σ(a)}` or `w_{σ(a)} w_{i₀}`, with `w_{i₀} = φ(z_m)`, and `φ`
is injective. -/
theorem eq_of_chart_coordinates {S : Type*} [CommRing S] {n N : ℕ} {z : Fin n → R}
    (hz : IsRegularSystemOfParameters z) {φ : R →+* S} (hφ : Function.Injective φ)
    {w : Fin N → S} {σ : Fin n → Fin N} {i₀ : Fin N} {m : Fin n} {J U : Finset (Fin n)}
    (hwi₀ : w i₀ = φ (z m)) (hout : ∀ j ∉ J, w (σ j) = φ (z j))
    (hin : ∀ j ∈ J, j ≠ m → j ∉ U → φ (z j) = w (σ j) * w i₀) {a a' : Fin n}
    (ham : a ≠ m) (haU : a ∉ U) (ham' : a' ≠ m) (haU' : a' ∉ U) (hσ : σ a = σ a') : a = a' := by
  have hval : ∀ a, a ≠ m → a ∉ U →
      (a ∉ J ∧ φ (z a) = w (σ a)) ∨ (a ∈ J ∧ φ (z a) = w (σ a) * w i₀) := by
    intro a ham haU
    by_cases haJ : a ∈ J
    · exact Or.inr ⟨haJ, hin a haJ ham haU⟩
    · exact Or.inl ⟨haJ, (hout a haJ).symm⟩
  by_contra hne
  rcases hval a ham haU with ⟨-, ha⟩ | ⟨-, ha⟩ <;>
    rcases hval a' ham' haU' with ⟨-, ha'⟩ | ⟨-, ha'⟩
  · exact ne_of_isRegularSystemOfParameters hz hne (hφ (by rw [ha, ha', hσ]))
  · have : z a' = z a * z m := hφ (by rw [ha', map_mul, ha, hσ, hwi₀])
    exact notMem_span_singleton_of_ne_of_isRegularSystemOfParameters hz hne
      (this ▸ Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  · have : z a = z a' * z m := hφ (by rw [ha, map_mul, ha', hσ, hwi₀])
    exact notMem_span_singleton_of_ne_of_isRegularSystemOfParameters hz (Ne.symm hne)
      (this ▸ Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  · exact ne_of_isRegularSystemOfParameters hz hne (hφ (by rw [ha, ha', hσ]))

/-- In a blow-up chart, the centre `(z_j)_{j ∈ J}` pulls back into an ideal `I` exactly when the
coordinate `w_{i₀} = φ(z_m)` of the exceptional divisor lies in `I`. -/
theorem span_image_le_comap_iff_of_chart {S : Type*} [CommRing S] {n N : ℕ} {z : Fin n → R}
    {φ : R →+* S} {w : Fin N → S} {σ : Fin n → Fin N} {i₀ : Fin N} {m : Fin n}
    {J U : Finset (Fin n)} (hmJ : m ∈ J) (hwi₀ : w i₀ = φ (z m))
    (hin : ∀ j ∈ J, j ≠ m → j ∉ U → φ (z j) = w (σ j) * w i₀)
    (hunit : ∀ j ∈ U, ∃ u, IsUnit u ∧ φ (z j) = u * w i₀) (I : Ideal S) :
    Ideal.span (z '' (J : Set (Fin n))) ≤ I.comap φ ↔ w i₀ ∈ I := by
  rw [Ideal.span_le]
  refine ⟨fun h => hwi₀ ▸ h ⟨m, hmJ, rfl⟩, ?_⟩
  rintro h _ ⟨j, hj, rfl⟩
  change φ (z j) ∈ I
  by_cases hjm : j = m
  · rwa [hjm, ← hwi₀]
  by_cases hjU : j ∈ U
  · obtain ⟨u, -, hu⟩ := hunit j hjU
    rw [hu]
    exact Ideal.mul_mem_left _ _ h
  · rw [hin j hj hjm hjU]
    exact Ideal.mul_mem_left _ _ h

/-- The primes below `p` containing `w_{i₀}`, and not containing it when `b` holds, exist exactly
when `b` fails and `w_{i₀} ∈ p`. -/
theorem exists_le_mem_not_and_iff_ite {S : Type*} [CommRing S] {N : ℕ} (w : Fin N → S)
    (i₀ : Fin N) (b : Prop) [Decidable b] (p : PrimeSpectrum S) :
    (∃ q : PrimeSpectrum S, q.asIdeal ≤ p.asIdeal ∧ w i₀ ∈ q.asIdeal ∧
        ¬(b ∧ w i₀ ∈ q.asIdeal)) ↔
      ∃ c, (if b then none else some i₀) = some c ∧ w c ∈ p.asIdeal := by
  by_cases hbb : b
  · rw [ite_eq_left hbb]
    constructor
    · rintro ⟨q, -, h1, h2⟩
      exact absurd ⟨hbb, h1⟩ h2
    · rintro ⟨_, ⟨⟩, -⟩
  · rw [ite_eq_right hbb]
    constructor
    · rintro ⟨q, hq, h1, -⟩
      exact ⟨i₀, rfl, hq h1⟩
    · rintro ⟨c', hc', h⟩
      obtain rfl := Option.some_inj.1 hc'
      exact ⟨p, le_rfl, h, fun h' => hbb h'.1⟩

/-- A prime containing a unit multiple `v = u t` of `t` contains `t`. -/
theorem exists_le_mem_not_and_iff_none_of_isUnit {S : Type*} [CommRing S] {N : ℕ}
    (w : Fin N → S) {b : Prop} (hb : b) {v t : S} (hv : ∃ u, IsUnit u ∧ v = u * t)
    (p : PrimeSpectrum S) :
    (∃ q : PrimeSpectrum S, q.asIdeal ≤ p.asIdeal ∧ v ∈ q.asIdeal ∧ ¬(b ∧ t ∈ q.asIdeal)) ↔
      ∃ c, (none : Option (Fin N)) = some c ∧ w c ∈ p.asIdeal := by
  obtain ⟨u, hu, rfl⟩ := hv
  constructor
  · rintro ⟨q, -, h1, h2⟩
    refine absurd ⟨hb, (q.isPrime.mem_or_mem h1).resolve_left fun h' => ?_⟩ h2
    exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h' hu)
  · rintro ⟨_, ⟨⟩, -⟩

/-- If `v` is `w_k` or, when `b` holds, `w_k w_{i₀}` with `k ≠ i₀`, the primes below `p` containing
`v`, and not containing `w_{i₀}` when `b` holds, exist exactly when `w_k ∈ p`. -/
theorem exists_le_mem_not_and_iff_some_of_isRegularSystemOfParameters {N : ℕ} {w : Fin N → R}
    (hw : IsRegularSystemOfParameters w) {i₀ k : Fin N} (hk : k ≠ i₀) {b : Prop} {v : R}
    (hv : v = w k ∨ (b ∧ v = w k * w i₀)) (p : PrimeSpectrum R) :
    (∃ q : PrimeSpectrum R, q.asIdeal ≤ p.asIdeal ∧ v ∈ q.asIdeal ∧
        ¬(b ∧ w i₀ ∈ q.asIdeal)) ↔
      ∃ c, some k = some c ∧ w c ∈ p.asIdeal := by
  constructor
  · rintro ⟨q, hq, h1, h2⟩
    refine ⟨k, rfl, hq ?_⟩
    rcases hv with rfl | ⟨hbb, rfl⟩
    · exact h1
    · exact (q.isPrime.mem_or_mem h1).resolve_right fun h' => h2 ⟨hbb, h'⟩
  · rintro ⟨c', hc', h⟩
    obtain rfl := Option.some_inj.1 hc'
    refine ⟨⟨Ideal.span {w k}, span_singleton_isPrime_of_isRegularSystemOfParameters hw k⟩,
      (Ideal.span_singleton_le_iff_mem _).2 h, ?_,
      fun h' => notMem_span_singleton_of_ne_of_isRegularSystemOfParameters hw hk h'.2⟩
    rcases hv with rfl | ⟨-, rfl⟩
    · exact Ideal.subset_span rfl
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

/-- In a blow-up chart, the primes below `p` containing `φ(z_a)`, and not containing `w_{i₀}` when
`b` holds, exist exactly when `p` contains the coordinate the chart assigns to `a`: `w_{i₀}` for
`a = m` (none if `b`), none for `a ∈ U`, and `w_{σ(a)}` otherwise. -/
theorem exists_le_mem_not_and_iff_chart {A : Type*} [CommRing A] {n N : ℕ} {z : Fin n → A}
    {φ : A →+* R} {w : Fin N → R} (hw : IsRegularSystemOfParameters w) {σ : Fin n → Fin N}
    {i₀ : Fin N} {m : Fin n} {J U : Finset (Fin n)} (hU : U ⊆ J.erase m)
    (hwi₀ : w i₀ = φ (z m)) (hout : ∀ j ∉ J, w (σ j) = φ (z j))
    (hin : ∀ j ∈ J, j ≠ m → j ∉ U → φ (z j) = w (σ j) * w i₀)
    (hunit : ∀ j ∈ U, ∃ u, IsUnit u ∧ φ (z j) = u * w i₀) (hσ₀ : ∀ j, j ≠ m → j ∉ U → σ j ≠ i₀)
    {b : Prop} [Decidable b] (hJm : ¬ b → ∀ j ∈ J, j = m) (a : Fin n) (p : PrimeSpectrum R) :
    (∃ q : PrimeSpectrum R, q.asIdeal ≤ p.asIdeal ∧ φ (z a) ∈ q.asIdeal ∧
        ¬(b ∧ w i₀ ∈ q.asIdeal)) ↔
      ∃ c, (if a = m then (if b then none else some i₀)
        else if a ∈ U then none else some (σ a)) = some c ∧ w c ∈ p.asIdeal := by
  by_cases ham : a = m
  · rw [ite_eq_left ham, ham, ← hwi₀]
    exact exists_le_mem_not_and_iff_ite w i₀ b p
  rw [ite_eq_right ham]
  by_cases haU : a ∈ U
  · rw [ite_eq_left haU]
    exact exists_le_mem_not_and_iff_none_of_isUnit w (b := b) (Classical.byContradiction
      fun hbb => ham (hJm hbb a (Finset.mem_erase.1 (hU haU)).2)) (hunit a haU) p
  rw [ite_eq_right haU]
  refine exists_le_mem_not_and_iff_some_of_isRegularSystemOfParameters hw (hσ₀ a ham haU)
    (b := b) ?_ p
  by_cases haJ : a ∈ J
  · exact Or.inr ⟨Classical.byContradiction fun hbb => ham (hJm hbb a haJ),
      hin a haJ ham haU⟩
  · exact Or.inl (hout a haJ).symm

end RSOP

section Downstairs

variable {X : Scheme.{u}}

/-- A point of `Spec 𝒪_{X,x}` lies over the support of an ideal sheaf `K` exactly when it
contains the stalk of `K`. -/
theorem fromSpecStalk_mem_support_iff_stalk_le (K : X.IdealSheafData) (x : X)
    (p : PrimeSpectrum (X.presheaf.stalk x)) :
    X.fromSpecStalk x p ∈ (K.support : Set X) ↔ IdealSheafData.stalk K x ≤ p.asIdeal :=
  (Set.ext_iff.1 (preimage_fromSpecStalk_support K x) p).trans (PrimeSpectrum.mem_zeroLocus _ _)

variable [IsLocallyNoetherian X] {x : X} {n : ℕ} {z : Fin n → X.presheaf.stalk x}

/-- The prime `(z_j : j ∈ J)` of `𝒪_{X,x}`, as a point of `Spec 𝒪_{X,x}`. -/
def coordPrime (hz : IsRegularSystemOfParameters z) (J : Finset (Fin n)) :
    PrimeSpectrum (X.presheaf.stalk x) :=
  ⟨Ideal.span (z '' (J : Set (Fin n))), span_image_isPrime_of_isRegularSystemOfParameters hz J⟩

omit [IsLocallyNoetherian X] in
/-- The closures of the images of two points of `Spec 𝒪_{X,x}` are strictly nested when the
points are. -/
theorem closure_fromSpecStalk_ssubset {q q' : PrimeSpectrum (X.presheaf.stalk x)}
    (h : q'.asIdeal < q.asIdeal) :
    closure {X.fromSpecStalk x q} ⊂ closure {X.fromSpecStalk x q'} :=
  ⟨closure_minimal (Set.singleton_subset_iff.2
    ((fromSpecStalk_mem_closure_iff x q' q).2 h.le)) isClosed_closure, fun h' =>
      h.not_ge ((fromSpecStalk_mem_closure_iff x q q').1 (h' (subset_closure rfl)))⟩

/-- If two distinct members of a regular system of parameters at `x` lie in `J`, the closure of the
point of `X` given by the prime `(z_j : j ∈ J)` has codimension `≥ 2`. -/
theorem two_le_codimension_closure_coordPrime (hz : IsRegularSystemOfParameters z)
    {J : Finset (Fin n)} {a b : Fin n} (ha : a ∈ J) (hb : b ∈ J) (hab : a ≠ b)
    (hirr : IsIrreducible (closure {X.fromSpecStalk x (coordPrime hz J)})) :
    2 ≤ codimension (irreducibleClosure hirr) := by
  have := isRegularLocalRing_of_isRegularSystemOfParameters hz
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk x)
  let q₁ : PrimeSpectrum (X.presheaf.stalk x) :=
    ⟨Ideal.span {z a}, span_singleton_isPrime_of_isRegularSystemOfParameters hz a⟩
  let q₂ : PrimeSpectrum (X.presheaf.stalk x) := ⟨⊥, Ideal.isPrime_bot⟩
  have h01 : q₂.asIdeal < q₁.asIdeal := by
    refine bot_lt_iff_ne_bot.2 fun h => ?_
    have : z a ∈ q₁.asIdeal := Ideal.subset_span rfl
    rw [h] at this
    exact ne_zero_of_isRegularSystemOfParameters hz a ((Submodule.mem_bot _).1 this)
  have h12 : q₁.asIdeal < (coordPrime hz J).asIdeal := by
    refine lt_of_le_of_ne ((Ideal.span_singleton_le_iff_mem _).2
      (Ideal.subset_span ⟨a, ha, rfl⟩)) fun h => ?_
    have : z b ∈ q₁.asIdeal := by
      rw [h]
      exact Ideal.subset_span ⟨b, hb, rfl⟩
    exact notMem_span_singleton_of_ne_of_isRegularSystemOfParameters hz hab this
  let C₁ : IrreducibleCloseds X :=
    ⟨closure {X.fromSpecStalk x q₁}, isIrreducible_singleton.closure, isClosed_closure⟩
  let C₂ : IrreducibleCloseds X :=
    ⟨closure {X.fromSpecStalk x q₂}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hl1 : irreducibleClosure hirr < C₁ := by
    change closure (closure {X.fromSpecStalk x (coordPrime hz J)}) ⊂ _
    rw [closure_closure]
    exact closure_fromSpecStalk_ssubset h12
  unfold codimension
  calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
    _ ≤ Order.coheight C₂ + 1 + 1 := by
      gcongr
      exact bot_le
    _ ≤ Order.coheight C₁ + 1 := by
      gcongr
      exact Order.coheight_add_one_le (closure_fromSpecStalk_ssubset h01)
    _ ≤ _ := Order.coheight_add_one_le hl1

end Downstairs

section Components

variable {X : Scheme.{u}} [IsLocallyNoetherian X] {x : X} {n : ℕ}
  {z : Fin n → X.presheaf.stalk x} (hz : IsRegularSystemOfParameters z) {J : Finset (Fin n)}
  {Z : X.IdealSheafData} (hJ : IdealSheafData.stalk Z x = (coordPrime hz J).asIdeal)

include hJ

/-- An irreducible component of `Z` through `x` is the closure of the point given by the prime
`(z_j : j ∈ J) = I_{Z,x}`. -/
theorem eq_closure_coordPrime_of_mem_componentsOf {W : Set X}
    (hW : W ∈ componentsOf (Z.support : Set X)) (hxW : x ∈ W) :
    W = closure {X.fromSpecStalk x (coordPrime hz J)} := by
  obtain ⟨η, hηZ, rfl⟩ := Aux.exists_eq_closure_of_mem_componentsOf Z.support.isClosed hW
  obtain ⟨q, rfl⟩ := exists_fromSpecStalk_eq_of_specializes (specializes_iff_mem_closure.2 hxW)
  have hPq : (coordPrime hz J).asIdeal ≤ q.asIdeal := by
    rw [← hJ]
    exact (fromSpecStalk_mem_support_iff_stalk_le Z x q).1 hηZ
  have hsub : closure {X.fromSpecStalk x q} ⊆ closure {X.fromSpecStalk x (coordPrime hz J)} :=
    closure_minimal (Set.singleton_subset_iff.2
      ((fromSpecStalk_mem_closure_iff x _ q).2 hPq)) isClosed_closure
  have hPZ : closure {X.fromSpecStalk x (coordPrime hz J)} ⊆ (Z.support : Set X) :=
    closure_minimal (Set.singleton_subset_iff.2
      ((fromSpecStalk_mem_support_iff_stalk_le Z x _).2 hJ.le)) Z.support.isClosed
  exact hsub.antisymm (hW.2 ⟨isIrreducible_singleton.closure, hPZ⟩ hsub)

/-- The closure of the point given by `I_{Z,x}` is an irreducible component of `Z`. -/
theorem closure_coordPrime_mem_componentsOf [NoetherianSpace X] (hx : x ∈ (Z.support : Set X)) :
    closure {X.fromSpecStalk x (coordPrime hz J)} ∈ componentsOf (Z.support : Set X) := by
  obtain ⟨-, hcov⟩ := Aux.finite_and_cover_componentsOf Z.support.isClosed
  obtain ⟨W, hW, hxW⟩ := hcov hx
  rwa [← eq_closure_coordPrime_of_mem_componentsOf hz hJ hW hxW]

/-- Near `x`, a union of irreducible components of `Z` selected by a property `P` is either empty
or all of `Z`, according as the component through `x` has `P`. -/
theorem fromSpecStalk_mem_biUnion_componentsOf_iff [NoetherianSpace X]
    (hx : x ∈ (Z.support : Set X)) (P : Set X → Prop)
    (p : PrimeSpectrum (X.presheaf.stalk x)) :
    X.fromSpecStalk x p ∈ ⋃ (W : Set X) (_ : W ∈ componentsOf (Z.support : Set X)) (_ : P W), W ↔
      P (closure {X.fromSpecStalk x (coordPrime hz J)}) ∧
        (coordPrime hz J).asIdeal ≤ p.asIdeal := by
  constructor
  · intro h
    obtain ⟨W, hW, hPW, hpW⟩ := by simpa only [Set.mem_iUnion, exists_prop] using h
    have hxW : x ∈ W := (fromSpecStalk_specializes_self x p).mem_closed
      (Aux.isClosed_of_mem_componentsOf Z.support.isClosed hW) hpW
    obtain rfl := eq_closure_coordPrime_of_mem_componentsOf hz hJ hW hxW
    exact ⟨hPW, (fromSpecStalk_mem_closure_iff x _ p).1 hpW⟩
  · rintro ⟨hP, hp⟩
    simp only [Set.mem_iUnion, exists_prop]
    exact ⟨_, closure_coordPrime_mem_componentsOf hz hJ hx, hP,
      (fromSpecStalk_mem_closure_iff x _ p).2 hp⟩

omit hJ in
/-- If the coordinate prime is `(z_c)` and `(z_c)` is the stalk at `x` of a member `E^{i₀}` of a
family whose members through `x` have stalks `(z_{c(i)})`, then the closure of the corresponding
point is an irreducible component of `⋃ᵢ E^i`. -/
theorem closure_coordPrime_mem_componentsOf_iUnion {s : ℕ} (E : Fin s → X.IdealSheafData)
    (c : {i // x ∈ (E i).support} → Fin n)
    (hc : ∀ i, IdealSheafData.stalk (E i.1) x = Ideal.span {z (c i)})
    (i₀ : {i // x ∈ (E i).support}) (hJc : J = {c i₀}) :
    closure {X.fromSpecStalk x (coordPrime hz J)} ∈
      componentsOf (⋃ i, ((E i).support : Set X)) := by
  have hP : (coordPrime hz J).asIdeal = Ideal.span {z (c i₀)} := by
    change Ideal.span (z '' (J : Set (Fin n))) = _
    rw [hJc, Finset.coe_singleton, Set.image_singleton]
  have hSc : IsClosed (⋃ i, ((E i).support : Set X)) :=
    isClosed_iUnion_of_finite fun i => (E i).support.isClosed
  have hPS : X.fromSpecStalk x (coordPrime hz J) ∈ ⋃ i, ((E i).support : Set X) :=
    Set.mem_iUnion.2 ⟨i₀.1, (fromSpecStalk_mem_support_iff_stalk_le _ x _).2 (by rw [hc i₀, hP])⟩
  refine ⟨⟨isIrreducible_singleton.closure,
    closure_minimal (Set.singleton_subset_iff.2 hPS) hSc⟩, fun W' hW' hle => ?_⟩
  obtain ⟨hW'irr, hW'S⟩ := hW'
  have hgen := hW'irr.isGenericPoint_genericPoint_closure
  set η := hW'irr.genericPoint
  have hηS : η ∈ ⋃ i, ((E i).support : Set X) :=
    closure_minimal hW'S hSc hgen.mem
  have hPη : X.fromSpecStalk x (coordPrime hz J) ∈ closure {η} := by
    rw [hgen.def]
    exact subset_closure (hle (subset_closure rfl))
  have hηx : η ⤳ x := (specializes_iff_mem_closure.2 hPη).trans
    (fromSpecStalk_specializes_self x _)
  obtain ⟨q, hq⟩ := exists_fromSpecStalk_eq_of_specializes hηx
  rw [← hq] at hPη hηS
  have hqP := (fromSpecStalk_mem_closure_iff x q _).1 hPη
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hηS
  have hxj : x ∈ (E j).support := (fromSpecStalk_specializes_self x q).mem_closed
    (E j).support.isClosed hj
  have hjq := (fromSpecStalk_mem_support_iff_stalk_le _ x q).1 hj
  rw [hc ⟨j, hxj⟩] at hjq
  have hzq : z (c ⟨j, hxj⟩) ∈ q.asIdeal := hjq (Ideal.subset_span rfl)
  have hcj : c ⟨j, hxj⟩ = c i₀ := by
    by_contra hne
    refine notMem_span_singleton_of_ne_of_isRegularSystemOfParameters hz (Ne.symm hne) ?_
    rw [← hP]
    exact hqP hzq
  have hqeq : q = coordPrime hz J := by
    refine PrimeSpectrum.ext (le_antisymm hqP ?_)
    rw [hP, ← hcj]
    exact hjq
  intro y hy
  have h1 : y ∈ closure {η} := by
    rw [hgen.def]
    exact subset_closure hy
  rwa [← hq, hqeq] at h1

end Components

section Morphism

variable {X Y : Scheme.{u}}

/-- A morphism maps the point of `Spec 𝒪_{Y,y}` given by a prime `p` to the point of
`Spec 𝒪_{X,g(y)}` given by the inverse image of `p` under the stalk map. -/
theorem apply_fromSpecStalk (g : Y ⟶ X) (y : Y) (p : PrimeSpectrum (Y.presheaf.stalk y)) :
    g (Y.fromSpecStalk y p) =
      X.fromSpecStalk (g y) (PrimeSpectrum.comap (g.stalkMap y).hom p) :=
  (congrArg (fun k : Spec (Y.presheaf.stalk y) ⟶ X => k (p : Spec _))
    (Scheme.SpecMap_stalkMap_fromSpecStalk g (x := y))).symm

/-- A morphism maps a point of `Spec 𝒪_{Y,y}` outside a closed set if it maps `y` outside it. -/
theorem apply_fromSpecStalk_notMem_of_notMem (g : Y ⟶ X) {y : Y} {A : Set X} (hA : IsClosed A)
    (hy : g y ∉ A) (q : PrimeSpectrum (Y.presheaf.stalk y)) :
    g (Y.fromSpecStalk y q) ∉ A :=
  fun h => hy (((fromSpecStalk_specializes_self y q).map g.continuous).mem_closed hA h)

/-- If the members through `g(y)` of a family `E` of closed subschemes have stalks `(z_{c(i)})`,
a point of `Spec 𝒪_{Y,y}` lies over `E^i` exactly when it contains the image of `z_{c(i)}`. -/
theorem apply_fromSpecStalk_mem_support_iff {s n : ℕ} (E : Fin s → X.IdealSheafData) (g : Y ⟶ X)
    (y : Y) {z : Fin n → X.presheaf.stalk (g y)} {c : {i // g y ∈ (E i).support} → Fin n}
    (hc : ∀ i, IdealSheafData.stalk (E i.1) (g y) = Ideal.span {z (c i)}) (i : Fin s)
    (q : PrimeSpectrum (Y.presheaf.stalk y)) :
    g (Y.fromSpecStalk y q) ∈ ((E i).support : Set X) ↔
      ∃ h : g y ∈ (E i).support, (g.stalkMap y).hom (z (c ⟨i, h⟩)) ∈ q.asIdeal := by
  rw [apply_fromSpecStalk]
  constructor
  · intro h
    have hxi : g y ∈ (E i).support :=
      (fromSpecStalk_specializes_self _ _).mem_closed (E i).support.isClosed h
    refine ⟨hxi, ?_⟩
    rw [fromSpecStalk_mem_support_iff_stalk_le, hc ⟨i, hxi⟩] at h
    exact h (Ideal.subset_span rfl)
  · rintro ⟨hxi, h⟩
    rwa [fromSpecStalk_mem_support_iff_stalk_le, hc ⟨i, hxi⟩, Ideal.span_le,
      Set.singleton_subset_iff]

/-- A point of `Spec 𝒪_{Y,y}` given by a minimal prime is a generic point of `Y`. -/
theorem fromSpecStalk_mem_genericPoints_of_isMin (y : Y) (p : PrimeSpectrum (Y.presheaf.stalk y))
    (hp : ∀ q : PrimeSpectrum (Y.presheaf.stalk y), q.asIdeal ≤ p.asIdeal → q = p) :
    Y.fromSpecStalk y p ∈ genericPoints Y := by
  refine ⟨isIrreducible_singleton.closure, fun T hT hle => ?_⟩
  have hgen := hT.isGenericPoint_genericPoint_closure
  have hmem : Y.fromSpecStalk y p ∈ closure {hT.genericPoint} := by
    rw [hgen.def]
    exact subset_closure (hle (subset_closure rfl))
  have hsp : hT.genericPoint ⤳ y :=
    (specializes_iff_mem_closure.2 hmem).trans (fromSpecStalk_specializes_self y p)
  obtain ⟨q, hq⟩ := exists_fromSpecStalk_eq_of_specializes hsp
  rw [← hq] at hmem
  have hqp := hp q ((fromSpecStalk_mem_closure_iff y q p).1 hmem)
  intro t ht
  have : t ∈ closure {hT.genericPoint} := by
    rw [hgen.def]
    exact subset_closure ht
  rwa [← hq, hqp] at this

/-- A generic point of `X` lying in the image of `Spec 𝒪_{X,x}` comes from a minimal prime. -/
theorem le_of_fromSpecStalk_mem_genericPoints (x : X) {p : PrimeSpectrum (X.presheaf.stalk x)}
    (hp : X.fromSpecStalk x p ∈ genericPoints X) (q : PrimeSpectrum (X.presheaf.stalk x))
    (hq : q.asIdeal ≤ p.asIdeal) : p.asIdeal ≤ q.asIdeal :=
  (fromSpecStalk_mem_closure_iff x p q).1 (hp.2 isIrreducible_singleton.closure
    (closure_minimal (Set.singleton_subset_iff.2
      ((fromSpecStalk_mem_closure_iff x q p).2 hq)) isClosed_closure) (subset_closure rfl))

/-- **The stalk maps of a blow-up of a scheme with integral local rings are injective.** If
`𝒪_{X,π(x')}` and `𝒪_{B,x'}` are domains, the stalk map `𝒪_{X,π(x')} → 𝒪_{B,x'}` of the
blow-up `π : B = B_ZX → X` is injective: the generic point of `Spec 𝒪_{B,x'}` is a generic point
of `B`, which `π` maps to a generic point of `X`. -/
theorem injective_stalkMap_blowUpToBase (Z : X.IdealSheafData) (x' : blowUp Z)
    [IsDomain (X.presheaf.stalk (blowUpToBase Z x'))]
    [IsDomain ((blowUp Z).presheaf.stalk x')] :
    Function.Injective ((blowUpToBase Z).stalkMap x').hom := by
  set φ := ((blowUpToBase Z).stalkMap x').hom
  let p₀ : PrimeSpectrum ((blowUp Z).presheaf.stalk x') := ⟨⊥, Ideal.isPrime_bot⟩
  have hgen : (blowUp Z).fromSpecStalk x' p₀ ∈ genericPoints (blowUp Z) :=
    fromSpecStalk_mem_genericPoints_of_isMin x' p₀ fun q hq =>
      PrimeSpectrum.ext (le_antisymm hq bot_le)
  have h1 := ((bijOn_genericPoints_blowUpToBase Z).1 hgen).1
  rw [apply_fromSpecStalk] at h1
  rw [injective_iff_map_eq_zero]
  intro a ha
  have : a ∈ (PrimeSpectrum.comap φ p₀).asIdeal := by
    change φ a ∈ (⊥ : Ideal _)
    rw [ha]
    exact Submodule.zero_mem _
  exact (Submodule.mem_bot _).1
    (le_of_fromSpecStalk_mem_genericPoints _ h1 ⟨⊥, Ideal.isPrime_bot⟩ bot_le this)

end Morphism

section Assembly

variable {Y : Scheme.{u}} [IsLocallyNoetherian Y]

/-- **Coordinates for a family of reduced closed subschemes from their local equations.** Let
`T_i ⊆ Y` be a family of subsets and `w` a regular system of parameters at `y`. If each `T_i` is
assigned at most one index `d(i)`, distinct members getting distinct indices, such that on
`Spec 𝒪_{Y,y}` the closure of `T_i` is `(w_{d(i)} = 0)` (empty if `T_i` has no index), then the
stalk at `y` of the reduced ideal of the closure of each `T_i` through `y` is `(w_{d(i)})`. -/
theorem exists_stalk_eq_of_assignment {ι : Type*} (T : ι → Set Y) (y : Y) {N : ℕ}
    {w : Fin N → Y.presheaf.stalk y} (hw : IsRegularSystemOfParameters w)
    (d : ι → Option (Fin N))
    (h1 : ∀ i (p : PrimeSpectrum (Y.presheaf.stalk y)),
      Y.fromSpecStalk y p ∈ closure (T i) ↔ ∃ c, d i = some c ∧ w c ∈ p.asIdeal)
    (h2 : ∀ i j c, d i = some c → d j = some c → i = j) :
    ∃ c : {i // y ∈ (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure (T i))).support} →
        Fin N,
      (∀ i, IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure (T i.1))) y = Ideal.span {w (c i)}) ∧ Function.Injective c := by
  have hex : ∀ i : {i // y ∈ (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure (T i))).support}, ∃ c, d i.1 = some c := by
    rintro ⟨i, hi⟩
    rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal,
      Closeds.coe_closure] at hi
    rw [← Scheme.fromSpecStalk_closedPoint (x := y)] at hi
    obtain ⟨c, hc, -⟩ := (h1 i _).1 hi
    exact ⟨c, hc⟩
  choose c hc using hex
  refine ⟨c, fun i => ?_, fun i j hij => Subtype.ext (h2 i.1 j.1 (c i) (hc i) (hij ▸ hc j))⟩
  refine stalk_vanishingIdeal_eq_span_singleton _ y
    (span_singleton_isPrime_of_isRegularSystemOfParameters hw _) fun p => ?_
  rw [Closeds.coe_closure, h1]
  constructor
  · rintro ⟨c', hc', hp⟩
    rw [hc i] at hc'
    rwa [Option.some_inj.1 hc']
  · exact fun hp => ⟨c i, hc i, hp⟩

end Assembly

section TotalTransformSets

variable {X : Scheme.{u}}

/-- The sets whose closures are the entries of `π⁻¹_tot(E)`: `π⁻¹(E^i ∖ Z^{≥2})` for `i ≤ s`,
and the union of the `π⁻¹(Z_j)` for the components `Z_j` of `Z` that are no components of
`Supp E`. -/
def totalTransformSet (E : OrderedDivisor X) (Z : X.IdealSheafData) :
    Fin (E.s + 1) → Set (blowUp Z) :=
  Fin.snoc (α := fun _ => Set (blowUp Z))
    (fun i => blowUpToBase Z ⁻¹'
      ((E.E i).support \ componentsOfCodimAtLeastTwo (Z.support : Set X)))
    (⋃ (W : Set X) (_ : W ∈ componentsOf (Z.support : Set X)) (_ : W ∉ componentsOf E.support),
      blowUpToBase Z ⁻¹' W)

/-- The `i`-th entry of the total transform `π⁻¹_tot(E)` is the vanishing ideal of the closure of
`totalTransformSet E Z i`. -/
theorem totalTransform_E_eq (E : OrderedDivisor X) (Z : X.IdealSheafData) (i : Fin (E.s + 1)) :
    (E.totalTransform Z).E i = Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure (totalTransformSet E Z i)) := by
  induction i using Fin.lastCases with
  | last => simp [OrderedDivisor.totalTransform, totalTransformSet]
  | cast i => simp [OrderedDivisor.totalTransform, totalTransformSet]

/-- The union of the components of codimension `≥ 2` of `Z`, as a union of the components with
a property not depending on the proof of membership. -/
theorem componentsOfCodimAtLeastTwo_eq (Z : Set X) :
    componentsOfCodimAtLeastTwo Z = ⋃ (W : Set X) (_ : W ∈ componentsOf Z)
      (_ : ∃ hW : IsIrreducible W, 2 ≤ codimension (irreducibleClosure hW)), W := by
  ext y
  simp only [componentsOfCodimAtLeastTwo, Set.mem_iUnion, exists_prop]
  exact ⟨fun ⟨W, hW, h2, hy⟩ => ⟨W, hW, ⟨hW.1.1, h2⟩, hy⟩,
    fun ⟨W, hW, ⟨_, h2⟩, hy⟩ => ⟨W, hW, h2, hy⟩⟩

/-- In a Noetherian space, a union of components of a closed set is closed. -/
theorem isClosed_biUnion_componentsOf [NoetherianSpace X] {Z : Set X} (hZ : IsClosed Z)
    (P : Set X → Prop) : IsClosed (⋃ (W : Set X) (_ : W ∈ componentsOf Z) (_ : P W), W) := by
  obtain ⟨hfin, -⟩ := Aux.finite_and_cover_componentsOf hZ
  have h : (⋃ (W : Set X) (_ : W ∈ componentsOf Z) (_ : P W), W) =
      ⋃ W ∈ {W | W ∈ componentsOf Z ∧ P W}, W := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop, and_assoc]
  rw [h]
  exact (hfin.subset fun W hW => hW.1).isClosed_biUnion fun W hW =>
    Aux.isClosed_of_mem_componentsOf hZ hW.1

/-- In a Noetherian space, the union of the codimension `≥ 2` components of a closed set is
closed. -/
theorem isClosed_componentsOfCodimAtLeastTwo [NoetherianSpace X] {Z : Set X} (hZ : IsClosed Z) :
    IsClosed (componentsOfCodimAtLeastTwo Z) := by
  rw [componentsOfCodimAtLeastTwo_eq]
  exact isClosed_biUnion_componentsOf hZ _

/-- The union of the codimension `≥ 2` components of a set is contained in it. -/
private theorem componentsOfCodimAtLeastTwo_subset (Z : Set X) :
    componentsOfCodimAtLeastTwo Z ⊆ Z := by
  intro y hy
  simp only [componentsOfCodimAtLeastTwo, Set.mem_iUnion] at hy
  obtain ⟨W, hW, -, hyW⟩ := hy
  exact hW.1.2 hyW

/-- The last entry of `π⁻¹_tot(E)` lies over the centre `Z`. -/
theorem totalTransformSet_last_subset (E : OrderedDivisor X) (Z : X.IdealSheafData) :
    totalTransformSet E Z (Fin.last E.s) ⊆ blowUpToBase Z ⁻¹' (Z.support : Set X) := by
  intro y hy
  simp only [totalTransformSet, Fin.snoc_last, Set.mem_iUnion] at hy
  obtain ⟨W, hW, -, hyW⟩ := hy
  exact hW.1.2 hyW

end TotalTransformSets

/-- An assignment `Fin.snoc dE o` of optional labels to `Fin (s + 1)` gives distinct entries
distinct labels if `dE` does and `o` is no label of `dE`. -/
theorem eq_of_snoc_eq_some {α : Type*} {s : ℕ} {dE : Fin s → Option α} {o : Option α}
    (hE : ∀ i j a, dE i = some a → dE j = some a → i = j)
    (ho : ∀ i a, dE i = some a → o ≠ some a) {i j : Fin (s + 1)} {a : α}
    (hi : Fin.snoc (α := fun _ => Option α) dE o i = some a)
    (hj : Fin.snoc (α := fun _ => Option α) dE o j = some a) : i = j := by
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => rfl
    | cast j =>
      simp only [Fin.snoc_last, Fin.snoc_castSucc] at hi hj
      exact absurd hi (ho j a hj)
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last, Fin.snoc_castSucc] at hi hj
      exact absurd hj (ho i a hi)
    | cast j =>
      simp only [Fin.snoc_castSucc] at hi hj
      rw [hE i j a hi hj]

/-- The chart assignment of the total transform gives distinct entries distinct coordinates: an
entry `i` gets the exceptional coordinate `i₀` (only when `¬ b`) or the coordinate `σ (c i)` of
its hyperplane, and the last entry gets `i₀` (only when `b'`). -/
theorem eq_of_snoc_eq_some_of_chart {s n N : ℕ} {P : Fin s → Prop}
    {c : {i // P i} → Fin n} (hinj : Function.Injective c) {m : Fin n} {U : Finset (Fin n)}
    {σ : Fin n → Fin N} {i₀ : Fin N} {b b' : Prop}
    (hσinj : ∀ a a', a ≠ m → a ∉ U → a' ≠ m → a' ∉ U → σ a = σ a' → a = a')
    (hσ₀ : ∀ a, a ≠ m → a ∉ U → σ a ≠ i₀) (hcross : ∀ i (h : P i), c ⟨i, h⟩ = m → ¬ b → ¬ b')
    {dE : Fin s → Option (Fin N)}
    (hdE : ∀ i c₀, dE i = some c₀ → ∃ h : P i, (c ⟨i, h⟩ = m ∧ ¬ b ∧ c₀ = i₀) ∨
      (c ⟨i, h⟩ ≠ m ∧ c ⟨i, h⟩ ∉ U ∧ c₀ = σ (c ⟨i, h⟩)))
    {o : Option (Fin N)} (ho : ∀ c₀, o = some c₀ → b' ∧ c₀ = i₀) {i j : Fin (s + 1)} {c₀ : Fin N}
    (hi : Fin.snoc (α := fun _ => Option (Fin N)) dE o i = some c₀)
    (hj : Fin.snoc (α := fun _ => Option (Fin N)) dE o j = some c₀) : i = j := by
  refine eq_of_snoc_eq_some (fun i j c₀ hi hj => ?_) (fun i c₀ hi ho' => ?_) hi hj
  · obtain ⟨hxi, hi'⟩ := hdE i c₀ hi
    obtain ⟨hxj, hj'⟩ := hdE j c₀ hj
    have hcij : c ⟨i, hxi⟩ = c ⟨j, hxj⟩ := by
      rcases hi' with ⟨hai, -, hci⟩ | ⟨hai, haU, hci⟩ <;>
        rcases hj' with ⟨haj, -, hcj⟩ | ⟨haj, haU', hcj⟩
      · rw [hai, haj]
      · exact absurd (hcj ▸ hci) (hσ₀ _ haj haU')
      · exact absurd (hci ▸ hcj) (hσ₀ _ hai haU)
      · exact hσinj _ _ hai haU haj haU' (hci ▸ hcj)
    exact congrArg Subtype.val (hinj hcij)
  · obtain ⟨hb', hc₀⟩ := ho c₀ ho'
    obtain ⟨hxi, ⟨ham, hnb, -⟩ | ⟨ham, haU, hc₀'⟩⟩ := hdE i c₀ hi
    · exact hcross i hxi ham hnb hb'
    · exact hσ₀ _ ham haU (hc₀' ▸ hc₀)

/-- In a blow-up chart `φ : A → R`, with `w_{i₀} = φ(z_m)`, the predicates `C i` on `Spec R`
described by the coordinates `z_{c(i)}` (for `i ≤ s`) and by `w_{i₀}` (for the last entry) are
given by an assignment of optional coordinates `w_{d(i)}` taking distinct values on distinct
entries. -/
theorem exists_assignment_of_chart {A R : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {n N s : ℕ}
    {z : Fin n → A} (hz : IsRegularSystemOfParameters z) {φ : A →+* R}
    (hφ : Function.Injective φ) {w : Fin N → R} (hw : IsRegularSystemOfParameters w)
    {σ : Fin n → Fin N} {i₀ : Fin N} {m : Fin n} {J U : Finset (Fin n)} (hU : U ⊆ J.erase m)
    (hwi₀ : w i₀ = φ (z m)) (hout : ∀ j ∉ J, w (σ j) = φ (z j))
    (hin : ∀ j ∈ J, j ≠ m → j ∉ U → φ (z j) = w (σ j) * w i₀)
    (hunit : ∀ j ∈ U, ∃ u, IsUnit u ∧ φ (z j) = u * w i₀) (hσ₀ : ∀ j, j ≠ m → j ∉ U → σ j ≠ i₀)
    {b b' : Prop} (hJm : ¬ b → ∀ j ∈ J, j = m) {P : Fin s → Prop} {c : {i // P i} → Fin n}
    (hinj : Function.Injective c) (hcross : ∀ i (h : P i), c ⟨i, h⟩ = m → ¬ b → ¬ b')
    {M : Fin s → PrimeSpectrum R → Prop}
    (hM : ∀ i q, M i q ↔ ∃ h : P i, φ (z (c ⟨i, h⟩)) ∈ q.asIdeal)
    {C : Fin (s + 1) → PrimeSpectrum R → Prop}
    (hC : ∀ i p, C (Fin.castSucc i) p ↔ ∃ q : PrimeSpectrum R, q.asIdeal ≤ p.asIdeal ∧ M i q ∧
      ¬(b ∧ w i₀ ∈ q.asIdeal))
    (hL : ∀ p, C (Fin.last s) p ↔ b' ∧ w i₀ ∈ p.asIdeal) :
    ∃ d : Fin (s + 1) → Option (Fin N), (∀ i p, C i p ↔ ∃ c, d i = some c ∧ w c ∈ p.asIdeal) ∧
      ∀ i j c, d i = some c → d j = some c → i = j := by
  classical
  let dE : Fin s → Option (Fin N) := fun i =>
    if h : P i then
      (if c ⟨i, h⟩ = m then (if b then none else some i₀)
        else if c ⟨i, h⟩ ∈ U then none else some (σ (c ⟨i, h⟩)))
    else none
  have hdE : ∀ i c₀, dE i = some c₀ → ∃ h : P i,
      (c ⟨i, h⟩ = m ∧ ¬ b ∧ c₀ = i₀) ∨
        (c ⟨i, h⟩ ≠ m ∧ c ⟨i, h⟩ ∉ U ∧ c₀ = σ (c ⟨i, h⟩)) := by
    intro i c₀ h
    simp only [dE] at h
    split_ifs at h with h1 h2 h3 h4
    · exact ⟨h1, Or.inl ⟨h2, h3, (Option.some_inj.1 h).symm⟩⟩
    · exact ⟨h1, Or.inr ⟨h2, h4, (Option.some_inj.1 h).symm⟩⟩
  refine ⟨Fin.snoc (α := fun _ => Option (Fin N)) dE (if b' then some i₀ else none),
    fun i p => ?_, fun i j c₀ hi hj => eq_of_snoc_eq_some_of_chart (b' := b') hinj
      (fun _ _ h₁ h₂ h₃ h₄ => eq_of_chart_coordinates hz hφ hwi₀ hout hin h₁ h₂ h₃ h₄)
      hσ₀ hcross hdE (fun c₀ h => ?_) hi hj⟩
  · induction i using Fin.lastCases with
    | last =>
      rw [hL]
      simp only [Fin.snoc_last]
      split_ifs with h <;> simp [h]
    | cast i =>
      rw [hC]
      simp only [Fin.snoc_castSucc, dE]
      by_cases hP : P i
      · rw [dite_eq_left hP, ← exists_le_mem_not_and_iff_chart hw hU hwi₀ hout hin hunit hσ₀
          hJm (c ⟨i, hP⟩) p]
        exact exists_congr fun q => and_congr_right fun _ =>
          and_congr ((hM i q).trans ⟨fun ⟨_, h⟩ => h, fun h => ⟨hP, h⟩⟩) Iff.rfl
      · rw [dite_eq_right hP]
        constructor
        · rintro ⟨q, -, hq, -⟩
          obtain ⟨h, -⟩ := (hM i q).1 hq
          exact (hP h).elim
        · rintro ⟨_, ⟨⟩, -⟩
  · split_ifs at h with hb'
    exact ⟨hb', (Option.some_inj.1 h).symm⟩

section Pointwise

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]

/-- On `Spec 𝒪_{B,x'}`, `B = B_ZX`, the closure of `π⁻¹(A ∖ B)`, `A`, `B` closed, consists of
the specializations of the points over `A ∖ B`. -/
theorem fromSpecStalk_mem_closure_preimage_diff_iff {Z : X.IdealSheafData} (x' : blowUp Z)
    {A C : Set X} (hA : IsClosed A) (hC : IsClosed C)
    (p : PrimeSpectrum ((blowUp Z).presheaf.stalk x')) :
    (blowUp Z).fromSpecStalk x' p ∈ closure (blowUpToBase Z ⁻¹' (A \ C)) ↔
      ∃ q : PrimeSpectrum ((blowUp Z).presheaf.stalk x'), q.asIdeal ≤ p.asIdeal ∧
        blowUpToBase Z ((blowUp Z).fromSpecStalk x' q) ∈ A ∧
          blowUpToBase Z ((blowUp Z).fromSpecStalk x' q) ∉ C := by
  have : IsLocallyNoetherian (blowUp Z) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase Z)
  have : CompactSpace (blowUp Z) := QuasiCompact.compactSpace_of_compactSpace (blowUpToBase Z)
  have : IsNoetherian (blowUp Z) := {}
  constructor
  · intro h
    rw [Set.preimage_sdiff] at h
    obtain ⟨t, ⟨htA, htC⟩, hts⟩ := exists_specializes_of_mem_closure_diff
      (hA.preimage (blowUpToBase Z).continuous) (hC.preimage (blowUpToBase Z).continuous) h
    obtain ⟨q, rfl⟩ := exists_fromSpecStalk_eq_of_specializes
      (hts.trans (fromSpecStalk_specializes_self x' p))
    exact ⟨q, (fromSpecStalk_mem_closure_iff x' q p).1 (specializes_iff_mem_closure.1 hts),
      htA, htC⟩
  · rintro ⟨q, hqp, hqA, hqC⟩
    have h1 : (blowUp Z).fromSpecStalk x' q ∈ blowUpToBase Z ⁻¹' (A \ C) := ⟨hqA, hqC⟩
    have h2 := (fromSpecStalk_mem_closure_iff x' q p).2 hqp
    exact closure_mono (Set.singleton_subset_iff.2 h1) h2

/-- On `Spec 𝒪_{B,x'}`, the closure of the `i`-th entry `π⁻¹(E^i ∖ Z^{≥2})` of `π⁻¹_tot(E)`, for
`i ≤ s`, consists of the specializations of the points over `E^i ∖ Z^{≥2}`. -/
theorem fromSpecStalk_mem_closure_totalTransformSet_castSucc_iff (E : OrderedDivisor X)
    {Z : X.IdealSheafData} (x' : blowUp Z) (i : Fin E.s)
    (p : PrimeSpectrum ((blowUp Z).presheaf.stalk x')) :
    (blowUp Z).fromSpecStalk x' p ∈ closure (totalTransformSet E Z (Fin.castSucc i)) ↔
      ∃ q : PrimeSpectrum ((blowUp Z).presheaf.stalk x'), q.asIdeal ≤ p.asIdeal ∧
        blowUpToBase Z ((blowUp Z).fromSpecStalk x' q) ∈ ((E.E i).support : Set X) ∧
          blowUpToBase Z ((blowUp Z).fromSpecStalk x' q) ∉
            componentsOfCodimAtLeastTwo (Z.support : Set X) := by
  have : IsNoetherian X := {}
  simp only [totalTransformSet, Fin.snoc_castSucc]
  exact fromSpecStalk_mem_closure_preimage_diff_iff x' (E.E i).support.isClosed
    (isClosed_componentsOfCodimAtLeastTwo Z.support.isClosed) p

/-- At a point `x'` over the centre `Z` with `I_{Z,π(x')} = (z_j : j ∈ J)`, a point of
`Spec 𝒪_{B,x'}` lies over the codimension `≥ 2` components of `Z` iff the component through
`π(x')` has codimension `≥ 2` and the point lies over it. -/
theorem apply_fromSpecStalk_mem_componentsOfCodimAtLeastTwo_iff {Z : X.IdealSheafData}
    {x' : blowUp Z} (hx : blowUpToBase Z x' ∈ (Z.support : Set X)) {n : ℕ}
    {z : Fin n → X.presheaf.stalk (blowUpToBase Z x')} (hz : IsRegularSystemOfParameters z)
    {J : Finset (Fin n)}
    (hJ : IdealSheafData.stalk Z (blowUpToBase Z x') = (coordPrime hz J).asIdeal)
    (p : PrimeSpectrum ((blowUp Z).presheaf.stalk x')) :
    blowUpToBase Z ((blowUp Z).fromSpecStalk x' p) ∈
        componentsOfCodimAtLeastTwo (Z.support : Set X) ↔
      (∃ hW : IsIrreducible (closure {X.fromSpecStalk (blowUpToBase Z x') (coordPrime hz J)}),
        2 ≤ codimension (irreducibleClosure hW)) ∧
        (coordPrime hz J).asIdeal ≤
          (PrimeSpectrum.comap ((blowUpToBase Z).stalkMap x').hom p).asIdeal := by
  have : IsNoetherian X := {}
  rw [apply_fromSpecStalk, componentsOfCodimAtLeastTwo_eq,
    fromSpecStalk_mem_biUnion_componentsOf_iff hz hJ hx _ _]

/-- At a point `x'` over the centre `Z` with `I_{Z,π(x')} = (z_j : j ∈ J)`, a point of
`Spec 𝒪_{B,x'}` lies in the closure of the last entry of `π⁻¹_tot(E)` iff the component of `Z`
through `π(x')` is no component of `Supp E` and the point lies over it. -/
theorem fromSpecStalk_mem_closure_totalTransformSet_last_iff (E : OrderedDivisor X)
    {Z : X.IdealSheafData} {x' : blowUp Z} (hx : blowUpToBase Z x' ∈ (Z.support : Set X))
    {n : ℕ} {z : Fin n → X.presheaf.stalk (blowUpToBase Z x')}
    (hz : IsRegularSystemOfParameters z) {J : Finset (Fin n)}
    (hJ : IdealSheafData.stalk Z (blowUpToBase Z x') = (coordPrime hz J).asIdeal)
    (p : PrimeSpectrum ((blowUp Z).presheaf.stalk x')) :
    (blowUp Z).fromSpecStalk x' p ∈ closure (totalTransformSet E Z (Fin.last E.s)) ↔
      closure {X.fromSpecStalk (blowUpToBase Z x') (coordPrime hz J)} ∉ componentsOf E.support ∧
        (coordPrime hz J).asIdeal ≤
          (PrimeSpectrum.comap ((blowUpToBase Z).stalkMap x').hom p).asIdeal := by
  have : IsNoetherian X := {}
  have hLeq : totalTransformSet E Z (Fin.last E.s) = blowUpToBase Z ⁻¹'
      (⋃ (W : Set X) (_ : W ∈ componentsOf (Z.support : Set X))
        (_ : W ∉ componentsOf E.support), W) := by
    simp only [totalTransformSet, Fin.snoc_last, Set.preimage_iUnion]
  have hLc : IsClosed (totalTransformSet E Z (Fin.last E.s)) := by
    rw [hLeq]
    exact (isClosed_biUnion_componentsOf Z.support.isClosed _).preimage
      (blowUpToBase Z).continuous
  rw [hLc.closure_eq, hLeq, Set.mem_preimage, apply_fromSpecStalk,
    fromSpecStalk_mem_biUnion_componentsOf_iff hz hJ hx _ _]

/-- `exists_assignment_totalTransformSet` at a point `x'` of the blow-up over the centre `Z`, in
the coordinates of a chart `D_+(z_m)` of the blow-up. -/
theorem exists_assignment_totalTransformSet_of_mem (E : OrderedDivisor X) {Z : X.IdealSheafData}
    (hZ : HasSNCWith E.E Z) {x' : blowUp Z} (hx : blowUpToBase Z x' ∈ (Z.support : Set X)) :
    ∃ (N : ℕ) (w : Fin N → (blowUp Z).presheaf.stalk x') (d : Fin (E.s + 1) → Option (Fin N)),
      IsRegularSystemOfParameters w ∧
      (∀ i (p : PrimeSpectrum ((blowUp Z).presheaf.stalk x')),
        (blowUp Z).fromSpecStalk x' p ∈ closure (totalTransformSet E Z i) ↔
          ∃ c, d i = some c ∧ w c ∈ p.asIdeal) ∧
      (∀ i j c, d i = some c → d j = some c → i = j) := by
  classical
  have : IsNoetherian X := {}
  have : IsLocallyNoetherian (blowUp Z) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase Z)
  set π := blowUpToBase Z
  set x := π x'
  set φ := (π.stalkMap x').hom
  set f' := (blowUp Z).fromSpecStalk x'
  obtain ⟨n, z, c, J, hz, hc, hinj, hJ⟩ := hZ x hx
  obtain ⟨N, w, m, i₀, σ, U, hw, hmJ, hU, hwi₀, hout, hin, hunit, hσ₀⟩ :=
    exists_chart_coordinates Z x' hx hz hJ
  have := isRegularLocalRing_of_isRegularSystemOfParameters hz
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk x)
  have := isRegularLocalRing_of_isRegularSystemOfParameters hw
  have := IsRegularLocalRing.isDomain ((blowUp Z).presheaf.stalk x')
  have hφinj : Function.Injective φ := injective_stalkMap_blowUpToBase Z x'
  have hJ' : IdealSheafData.stalk Z x = (coordPrime hz J).asIdeal := hJ
  set W₀ := closure {X.fromSpecStalk x (coordPrime hz J)}
  set b : Prop := ∃ hW : IsIrreducible W₀, 2 ≤ codimension (irreducibleClosure hW)
  set b' : Prop := W₀ ∉ componentsOf E.support
  have hJm : ¬ b → ∀ j ∈ J, j = m := by
    intro hnb j hj
    by_contra hjm
    exact hnb ⟨isIrreducible_singleton.closure,
      two_le_codimension_closure_coordPrime hz hj hmJ hjm _⟩
  have mZ : ∀ q : PrimeSpectrum ((blowUp Z).presheaf.stalk x'),
      (coordPrime hz J).asIdeal ≤ (PrimeSpectrum.comap φ q).asIdeal ↔ w i₀ ∈ q.asIdeal := by
    intro q
    change Ideal.span (z '' (J : Set (Fin n))) ≤ _ ↔ _
    exact span_image_le_comap_iff_of_chart hmJ hwi₀ hin hunit q.asIdeal
  have hcross : ∀ i (h : x ∈ (E.E i).support), c ⟨i, h⟩ = m → ¬ b → ¬ b' :=
    fun i hxi ham hnb hbb' => hbb' (closure_coordPrime_mem_componentsOf_iUnion hz E.E c hc ⟨i, hxi⟩
      (by rw [ham]; exact Finset.eq_singleton_iff_unique_mem.2 ⟨hmJ, hJm hnb⟩))
  obtain ⟨d, hd⟩ := exists_assignment_of_chart hz hφinj hw hU hwi₀ hout hin hunit hσ₀ hJm hinj
    hcross (M := fun i q => π (f' q) ∈ ((E.E i).support : Set X))
    (C := fun i p => f' p ∈ closure (totalTransformSet E Z i))
    (apply_fromSpecStalk_mem_support_iff E.E π x' hc)
    (fun i p => (fromSpecStalk_mem_closure_totalTransformSet_castSucc_iff E x' i p).trans
      (exists_congr fun q => and_congr_right fun _ => and_congr Iff.rfl
      (not_congr ((apply_fromSpecStalk_mem_componentsOfCodimAtLeastTwo_iff hx hz hJ' q).trans
        (and_congr Iff.rfl (mZ q))))))
    fun p => (fromSpecStalk_mem_closure_totalTransformSet_last_iff E hx hz hJ' p).trans
      (and_congr Iff.rfl (mZ p))
  exact ⟨N, w, d, hw, hd⟩

/-- `exists_assignment_totalTransformSet` at a point `x'` of the blow-up off the centre `Z`, where
the blow-up is a local isomorphism. -/
theorem exists_assignment_totalTransformSet_of_notMem (E : OrderedDivisor X)
    (hE : ∀ x : X, ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x)
      (c : {i // x ∈ (E.E i).support} → Fin n),
      IsRegularSystemOfParameters z ∧
        (∀ i, IdealSheafData.stalk (E.E i.1) x = Ideal.span {z (c i)}) ∧ Function.Injective c)
    {Z : X.IdealSheafData} {x' : blowUp Z} (hx : blowUpToBase Z x' ∉ (Z.support : Set X)) :
    ∃ (N : ℕ) (w : Fin N → (blowUp Z).presheaf.stalk x') (d : Fin (E.s + 1) → Option (Fin N)),
      IsRegularSystemOfParameters w ∧
      (∀ i (p : PrimeSpectrum ((blowUp Z).presheaf.stalk x')),
        (blowUp Z).fromSpecStalk x' p ∈ closure (totalTransformSet E Z i) ↔
          ∃ c, d i = some c ∧ w c ∈ p.asIdeal) ∧
      (∀ i j c, d i = some c → d j = some c → i = j) := by
  classical
  have : IsNoetherian X := {}
  have : IsLocallyNoetherian (blowUp Z) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase Z)
  set π := blowUpToBase Z
  set x := π x'
  set φ := (π.stalkMap x').hom
  set f' := (blowUp Z).fromSpecStalk x'
  obtain ⟨n, z, c, hz, hc, hinj⟩ := hE x
  have hiso : IsIso (π.stalkMap x') :=
    isIso_stalkMap_of_isIso_morphismRestrict π (isIso_blowUpToBase_restrict_compl_support Z)
      (show x' ∈ π ⁻¹ᵁ Z.support.compl from hx)
  have hw : IsRegularSystemOfParameters fun i => φ (z i) :=
    isRegularSystemOfParameters_map_ringEquiv (asIso (π.stalkMap x')).commRingCatIsoToRingEquiv hz
  have hnZ : ∀ q : PrimeSpectrum ((blowUp Z).presheaf.stalk x'),
      π (f' q) ∉ (Z.support : Set X) :=
    apply_fromSpecStalk_notMem_of_notMem π Z.support.isClosed hx
  have mE : ∀ (i : Fin E.s) (q : PrimeSpectrum ((blowUp Z).presheaf.stalk x')),
      π (f' q) ∈ ((E.E i).support : Set X) ↔
      ∃ h : x ∈ (E.E i).support, φ (z (c ⟨i, h⟩)) ∈ q.asIdeal :=
    apply_fromSpecStalk_mem_support_iff E.E π x' hc
  let dE : Fin E.s → Option (Fin n) := fun i =>
    if h : x ∈ (E.E i).support then some (c ⟨i, h⟩) else none
  refine ⟨n, fun i => φ (z i), Fin.snoc (α := fun _ => Option (Fin n)) dE none, hw, ?_, ?_⟩
  · intro i p
    induction i using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last, reduceCtorEq, false_and, exists_false, iff_false]
      exact fun h => hnZ p (closure_minimal (totalTransformSet_last_subset E Z)
        (Z.support.isClosed.preimage π.continuous) h)
    | cast i =>
      refine (fromSpecStalk_mem_closure_totalTransformSet_castSucc_iff E x' i p).trans ?_
      simp only [Fin.snoc_castSucc, dE]
      by_cases hxi : x ∈ (E.E i).support
      · simp only [hxi, dite_true, Option.some.injEq, exists_eq_left']
        exact ⟨fun ⟨q, hq, h1, _⟩ => hq ((mE i q).1 h1).2, fun h => ⟨p, le_rfl,
          (mE i p).2 ⟨hxi, h⟩, fun h' => hnZ p (componentsOfCodimAtLeastTwo_subset _ h')⟩⟩
      · simp only [hxi, dite_false, reduceCtorEq, false_and, exists_false, iff_false]
        exact fun ⟨q, _, h1, _⟩ =>
          apply_fromSpecStalk_notMem_of_notMem π (E.E i).support.isClosed hxi q h1
  · refine fun i j c₀ hi hj => eq_of_snoc_eq_some (fun i j c₀ hi hj => ?_)
      (fun _ _ _ => by simp) hi hj
    simp only [dE] at hi hj
    split_ifs at hi hj with hxi hxj
    exact congrArg Subtype.val (hinj ((Option.some_inj.1 hi).trans
      (Option.some_inj.1 hj).symm))

/-- **The entries of `π⁻¹_tot(E)` at a point of the blow-up.** Let `E = (E^1, …, E^s)` be a
family of closed subschemes such that at every point `x` of `X` there are local coordinates in
which the `E^i` through `x` are distinct coordinate hyperplanes, and let `Z` have simple normal
crossings with `E`. At every point `x'` of `B_ZX` there are local coordinates `w` and an
assignment `d` of at most one coordinate to every entry of `π⁻¹_tot(E)`, distinct entries
getting distinct coordinates, such that on `Spec 𝒪_{B,x'}` the entry is `(w_{d(i)} = 0)` (empty
if it has no coordinate). -/
theorem exists_assignment_totalTransformSet (E : OrderedDivisor X)
    (hE : ∀ x : X, ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x)
      (c : {i // x ∈ (E.E i).support} → Fin n),
      IsRegularSystemOfParameters z ∧
        (∀ i, IdealSheafData.stalk (E.E i.1) x = Ideal.span {z (c i)}) ∧ Function.Injective c)
    {Z : X.IdealSheafData} (hZ : HasSNCWith E.E Z) (x' : blowUp Z) :
    ∃ (N : ℕ) (w : Fin N → (blowUp Z).presheaf.stalk x') (d : Fin (E.s + 1) → Option (Fin N)),
      IsRegularSystemOfParameters w ∧
      (∀ i (p : PrimeSpectrum ((blowUp Z).presheaf.stalk x')),
        (blowUp Z).fromSpecStalk x' p ∈ closure (totalTransformSet E Z i) ↔
          ∃ c, d i = some c ∧ w c ∈ p.asIdeal) ∧
      (∀ i j c, d i = some c → d j = some c → i = j) := by
  by_cases hx : blowUpToBase Z x' ∈ (Z.support : Set X)
  · exact exists_assignment_totalTransformSet_of_mem E hZ hx
  · exact exists_assignment_totalTransformSet_of_notMem E hE hx

end Pointwise

section OrderedSNC

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- **The total transform of an ordered snc divisor is an ordered snc divisor.** Let `X` be of
finite type over a field `k` of characteristic `0`, `E` an ordered divisor whose sum is a simple
normal crossing divisor, and `Z ⊆ X` a closed subscheme having simple normal crossings with
`∑ᵢ E^i`. Then `π⁻¹_tot(E)` is an ordered snc divisor on `B_ZX`. -/
theorem isOrderedSNC_totalTransform [CharZero k] (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] [QuasiCompact sX] {E : OrderedDivisor X} (hE : E.IsSNC sX)
    {Z : X.IdealSheafData} (hZ : HasSNCWith E.E Z) :
    (E.totalTransform Z).IsOrderedSNC (blowUpToBase Z ≫ sX) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsLocallyNoetherian (blowUp Z) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase Z)
  have hcoord : ∀ x' : blowUp Z, ∃ (N : ℕ) (w : Fin N → (blowUp Z).presheaf.stalk x')
      (c : {i // x' ∈ ((E.totalTransform Z).E i).support} → Fin N),
      IsRegularSystemOfParameters w ∧
        (∀ i, IdealSheafData.stalk ((E.totalTransform Z).E i.1) x' = Ideal.span {w (c i)}) ∧
          Function.Injective c := by
    intro x'
    obtain ⟨N, w, d, hw, h1, h2⟩ := exists_assignment_totalTransformSet E hE.2 hZ x'
    obtain ⟨c, hc, hinj⟩ := exists_stalk_eq_of_assignment (totalTransformSet E Z) x' hw d h1 h2
    have hEq : (E.totalTransform Z).E = fun i => Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure (totalTransformSet E Z i)) := funext (totalTransform_E_eq E Z)
    rw [hEq]
    exact ⟨N, w, c, hw, hc, hinj⟩
  have hpar : ∀ i, ∀ y ∈ ((E.totalTransform Z).E i).support,
      ∃ (m : ℕ) (w : Fin m → (blowUp Z).presheaf.stalk y) (j : Fin m),
        IsRegularSystemOfParameters w ∧
          IdealSheafData.stalk ((E.totalTransform Z).E i) y = Ideal.span {w j} := by
    intro i y hy
    obtain ⟨N, w, c, hw, hc, -⟩ := hcoord y
    exact ⟨N, w, c ⟨i, hy⟩, hw, hc ⟨i, hy⟩⟩
  refine ⟨fun i => ⟨isReduced_subscheme_of_stalk_eq_span_parameter _ (hpar i),
    isEffectiveCartierDivisor_of_stalk_eq_span_parameter _ (hpar i)⟩,
    ⟨fun i => ⟨isReduced_subscheme_of_stalk_eq_span_parameter _ (hpar i),
      isPureCodimOne_support_of_stalk_eq_span_parameter _ (hpar i),
      isSmoothScheme_subscheme_of_stalk_eq_span_parameter _ _ (hpar i)⟩, hcoord⟩⟩

end OrderedSNC

section GenericPoints

variable {X : Scheme.{u}}

/-- An ideal sheaf is contained in its ideal quotient by any ideal sheaf. -/
theorem le_idealColon (A B : X.IdealSheafData) : A ≤ idealColon A B := by
  unfold idealColon
  rw [Scheme.IdealSheafData.le_ofIdeals_iff]
  intro V a ha
  rw [Submodule.mem_colon]
  intro b _
  rw [smul_eq_mul]
  exact (A.ideal V).mul_mem_right b ha

/-- The inverse image along a blow-up of an ideal sheaf nonzero at the generic points of `X` is
nonzero at the generic points of the blow-up: these lie off the exceptional divisor, where the
blow-up is an isomorphism, over generic points of `X`. -/
theorem isNonzeroAtGenericPoints_comap_blowUpToBase (Z : X.IdealSheafData)
    {I : X.IdealSheafData} (hI : IsNonzeroAtGenericPoints I) :
    IsNonzeroAtGenericPoints (I.comap (blowUpToBase Z)) := by
  intro η hη
  have hgen : η ∈ genericPoints (blowUp Z) := hη
  obtain ⟨hπη, hZ⟩ := (bijOn_genericPoints_blowUpToBase Z).1 hgen
  have hZ' : blowUpToBase Z η ∉ (Z.support : Set X) := fun h =>
    hZ (Scheme.IdealSheafData.mem_supportSet_iff_mem_support.2 h)
  have hiso : IsIso ((blowUpToBase Z).stalkMap η) :=
    isIso_stalkMap_of_isIso_morphismRestrict (blowUpToBase Z)
      (isIso_blowUpToBase_restrict_compl_support Z)
      (show η ∈ blowUpToBase Z ⁻¹ᵁ Z.support.compl from hZ')
  rw [IdealSheafData.stalk_comap]
  intro h
  exact hI _ hπη ((Ideal.map_eq_bot_iff_of_injective
    (asIso ((blowUpToBase Z).stalkMap η)).commRingCatIsoToRingEquiv.injective).1 h)

/-- An ideal quotient of the inverse image of an ideal sheaf nonzero at the generic points under a
blow-up is nonzero at the generic points of the blow-up. -/
theorem isNonzeroAtGenericPoints_idealColon_comap (Z : X.IdealSheafData) {I : X.IdealSheafData}
    (hI : IsNonzeroAtGenericPoints I) (K : (blowUp Z).IdealSheafData) :
    IsNonzeroAtGenericPoints (idealColon (I.comap (blowUpToBase Z)) K) := by
  intro η hη h
  refine isNonzeroAtGenericPoints_comap_blowUpToBase Z hI η hη (eq_bot_iff.2 ?_)
  rw [← h]
  exact stalk_le_stalk_of_le (le_idealColon _ _) η

end GenericPoints

section Equidimensional

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- If `f` restricts over an open `U` to a surjective open immersion and `η` is a generic point of
`C` over `U`, then every point of `U` in the closure of `f(η)` is the image of a point of `C`
over `U`. -/
theorem exists_mem_apply_eq_of_mem_closure {Y : Scheme.{u}} {f : Y ⟶ X} {U : X.Opens}
    [IsOpenImmersion (f ∣_ U)] [Surjective (f ∣_ U)] {C : Set Y} {η : Y}
    (hgen : IsGenericPoint η C) (hηU : f η ∈ U) {y : X} (hyη : y ∈ closure {f η})
    (hyU : y ∈ U) : ∃ b ∈ C, b ∈ f ⁻¹ᵁ U ∧ f b = y := by
  obtain ⟨b', hb'⟩ := (f ∣_ U).surjective ⟨y, hyU⟩
  have hb'y : f b'.1 = y := by
    have := congrArg (fun t : U => (t : X)) hb'
    simp only at this
    rw [← this]
    change f ((f ⁻¹ᵁ U).ι b') = U.ι ((f ∣_ U) b')
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, morphismRestrict_ι]
  have : IsOpenImmersion ((f ⁻¹ᵁ U).ι ≫ f) := by
    rw [← morphismRestrict_ι]
    infer_instance
  have hsp : ((f ⁻¹ᵁ U).ι ≫ f) ⟨η, hηU⟩ ⤳ ((f ⁻¹ᵁ U).ι ≫ f) b' := by
    change f η ⤳ f b'.1
    rw [hb'y]
    exact specializes_iff_mem_closure.2 hyη
  have hsp' := (((f ⁻¹ᵁ U).ι ≫ f).isOpenEmbedding.isInducing.specializes_iff.1 hsp).map
    continuous_subtype_val
  refine ⟨b'.1, ?_, b'.2, hb'y⟩
  rw [← hgen.def]
  exact specializes_iff_mem_closure.1 hsp'

/-- An irreducible component of the blow-up `B_ZX` has the dimension of an irreducible component
of `X`: its generic point lies off the exceptional divisor, the blow-up is an isomorphism over
`X ∖ Z`, and a nonempty open part of an irreducible closed subset of a scheme locally of finite
type over a field has its dimension. -/
theorem exists_topologicalKrullDim_eq_of_mem_irreducibleComponents_blowUp
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (Z : X.IdealSheafData) {C : Set (blowUp Z)}
    (hC : C ∈ irreducibleComponents (blowUp Z)) :
    ∃ D ∈ irreducibleComponents X, topologicalKrullDim C = topologicalKrullDim D := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  set π := blowUpToBase Z
  have hCcl : IsClosed C := isClosed_of_mem_irreducibleComponents C hC
  have hgenC := hC.1.isGenericPoint_genericPoint_closure
  set η := hC.1.genericPoint
  rw [hCcl.closure_eq] at hgenC
  have hηgen : η ∈ genericPoints (blowUp Z) := by
    change closure {η} ∈ irreducibleComponents (blowUp Z)
    rw [hgenC.def]
    exact hC
  obtain ⟨hπη, hπηZ⟩ := (bijOn_genericPoints_blowUpToBase Z).1 hηgen
  have hπηU : π η ∉ (Z.support : Set X) := fun h =>
    hπηZ (Scheme.IdealSheafData.mem_supportSet_iff_mem_support.2 h)
  set D := closure ({π η} : Set X)
  have hD : D ∈ irreducibleComponents X := hπη
  have hDcl : IsClosed D := isClosed_closure
  set U : X.Opens := Z.support.compl
  set O : (blowUp Z).Opens := π ⁻¹ᵁ U
  have hηC : η ∈ C := hgenC.mem
  have hηO : η ∈ (O : Set (blowUp Z)) := hπηU
  refine ⟨D, hD, ?_⟩
  rw [← topologicalKrullDim_inter_isOpen_eq k (π ≫ sX) hCcl hC.1 O.isOpen ⟨η, hηC, hηO⟩,
    ← topologicalKrullDim_inter_isOpen_eq k sX hDcl hD.1 U.isOpen
      ⟨π η, subset_closure rfl, hπηU⟩]
  have hι : IsOpenImmersion (O.ι ≫ π) := by
    rw [← morphismRestrict_ι]
    infer_instance
  have he := (O.ι ≫ π).isOpenEmbedding
  have hmapD : ∀ b ∈ C, π b ∈ D := fun b hb => by
    rw [← hgenC.def] at hb
    exact ((specializes_iff_mem_closure.2 hb).map π.continuous).mem_closed hDcl
      (subset_closure rfl)
  let F : ↥(C ∩ (O : Set (blowUp Z))) → ↥(D ∩ (U : Set X)) := fun b =>
    ⟨π b.1, hmapD b.1 b.2.1, b.2.2⟩
  have hFc : Continuous F :=
    (π.continuous.comp continuous_subtype_val).subtype_mk _
  refine IsHomeomorph.topologicalKrullDim_eq F
    (isHomeomorph_iff_isEmbedding_surjective.2 ⟨?_, ?_⟩)
  · refine Topology.IsEmbedding.of_comp hFc continuous_subtype_val ?_
    let g : ↥(C ∩ (O : Set (blowUp Z))) → O := fun b => ⟨b.1, b.2.2⟩
    have hg : Topology.IsEmbedding g :=
      Topology.IsEmbedding.of_comp (continuous_subtype_val.subtype_mk _) continuous_subtype_val
        Topology.IsEmbedding.subtypeVal
    exact he.isEmbedding.comp hg
  · rintro ⟨y, hyD, hyU⟩
    obtain ⟨b, hbC, hbO, hb⟩ :=
      exists_mem_apply_eq_of_mem_closure (f := π) (U := U) hgenC hπηU hyD hyU
    exact ⟨⟨b, hbC, hbO⟩, Subtype.ext hb⟩

/-- The blow-up of an equidimensional scheme locally of finite type over a field is
equidimensional. -/
theorem equidimensional_blowUp (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    (Z : X.IdealSheafData) (hX : Equidimensional X) : Equidimensional (blowUp Z) := by
  intro C hC C' hC'
  obtain ⟨D, hD, h⟩ := exists_topologicalKrullDim_eq_of_mem_irreducibleComponents_blowUp sX Z hC
  obtain ⟨D', hD', h'⟩ :=
    exists_topologicalKrullDim_eq_of_mem_irreducibleComponents_blowUp sX Z hC'
  rw [h, h']
  exact hX D hD D' hD'

end Equidimensional

section Triple

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- Let `(X, I, E)` be a triple and `Z ⊆ X` a closed subscheme having simple normal crossings with
`∑ᵢ E^i`. Then `(B_ZX, J, π⁻¹_tot(E))` is a triple for every ideal sheaf `J` on `B_ZX` nonzero at
the generic points. -/
theorem isTriple_blowUp_totalTransform {I : X.IdealSheafData} {E : OrderedDivisor X}
    (h : IsTriple sX I E) {Z : X.IdealSheafData} (hZ : HasSNCWith E.E Z)
    {J : (blowUp Z).IdealSheafData} (hJ : IsNonzeroAtGenericPoints J) :
    IsTriple (blowUpToBase Z ≫ sX) J (E.totalTransform Z) := by
  obtain ⟨hchar, hsm, hlft, hqc, heq, hI, hE⟩ := h
  have := hchar
  have := hlft
  have := hqc
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have hZsm : IsSmoothScheme (Z.subschemeι ≫ sX) :=
    isSmoothScheme_of_hasSNCWith ⟨⟨X, I, E⟩, k, sX⟩ ⟨hchar, hsm, hlft, hqc, heq, hI, hE⟩ Z hZ
  have hBsm : Smooth (blowUpToBase Z ≫ sX) :=
    (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sX Z ⟨hsm, hZsm⟩).1
  exact ⟨hchar, isSmoothScheme_of_smooth _, inferInstance, inferInstance,
    equidimensional_blowUp sX Z heq, hJ, isOrderedSNC_totalTransform sX hE.2 hZ⟩

/-- **The transform of a triple is a triple** (Kollár, Def. 3.65–3.66). Let `(X, I, E)` be a
triple and `Z ⊆ X` a closed subscheme having simple normal crossings with `∑ᵢ E^i`, with blow-up
`π : B_ZX → X`. Then `(B_ZX, π⁻¹_{Z*}I, π⁻¹_tot(E))` is a triple. -/
@[mmp "lem_kr3c_birational_transform_triple_is_triple"]
theorem isTriple_controlledTransform_totalTransform {I : X.IdealSheafData}
    {E : OrderedDivisor X} (h : IsTriple sX I E) {Z : X.IdealSheafData}
    (hZ : HasSNCWith E.E Z) :
    IsTriple (blowUpToBase Z ≫ sX) (controlledTransform Z I) (E.totalTransform Z) :=
  isTriple_blowUp_totalTransform h hZ
    (isNonzeroAtGenericPoints_idealColon_comap Z h.2.2.2.2.2.1 _)

/-- **The transform of a marked triple is a marked triple** (Kollár, Def. 3.65–3.66). Let
`(X, I, m, E)` be a marked triple and `Z ⊆ X` a closed subscheme having simple normal crossings
with `∑ᵢ E^i`, with blow-up `π : B_ZX → X`. Then `(B_ZX, π⁻¹_{Z*}(I, m), π⁻¹_tot(E))` is a marked
triple. -/
@[mmp "lem_kr3c_birational_transform_triple_is_triple"]
theorem isTriple_birationalTransform_totalTransform (a : MarkedIdeal X) {E : OrderedDivisor X}
    (h : IsTriple sX a.I E) {Z : X.IdealSheafData} (hZ : HasSNCWith E.E Z) :
    IsTriple (blowUpToBase Z ≫ sX) (a.birationalTransform Z).I (E.totalTransform Z) :=
  isTriple_blowUp_totalTransform h hZ
    (isNonzeroAtGenericPoints_idealColon_comap Z h.2.2.2.2.2.1 _)

end Triple

end MMP.Resolution
