module

public import MMP.AlgebraicGeometry.Intersection.Surface.BlowupGenusDropAdjunction
public import MMP.AlgebraicGeometry.Intersection.SelfIntersectionHilbertDegree

/-!
# Curves on smooth surfaces: projection, adjunction, and the relative nefness of `K_Y`

Let `k` be an algebraically closed field.

* **Projection formula.** For a proper morphism `g : Y' ⟶ Y` of varieties over `k` with `Y`
  normal, a `ℚ`-Cartier `ℚ`-divisor `L` on `Y` and a proper irreducible curve `C ⊆ Y'`, the
  intersection number `(g^*L · C)` vanishes if `g(C)` is a point, and equals
  `[k(C) : k(g(C))] · (L · g(C))` otherwise.
* **Adjunction and genus.** For a proper irreducible curve `C` on a smooth surface `S` with
  canonical divisor `K_S`, `((K_S + C) · C) = 2 p_a(C) - 2`, where `p_a(C) = 1 - χ(𝒪_C) ≥ 0`, and
  `p_a(C) = 0` exactly when `C ≅ ℙ¹_k`.
* **Intersections of distinct curves.** For distinct irreducible curves `C`, `C'` on `S` with `C`
  proper, `(C · C') ≥ 0`, with equality iff `C ∩ C' = ∅`, and `(C · C') = 1` iff `C` and `C'` meet
  in exactly one point, transversally.
* **Minimal resolutions.** Let `f : Y ⟶ X` be a minimal resolution of a normal surface `X` and
  `K_Y` a canonical divisor of `Y`. Then `(K_Y · E) ≥ 0` for every `f`-exceptional curve `E`.
  Indeed `E` is proper with `(E · E) < 0`, and adjunction gives
  `(K_Y · E) + (E · E) = 2 p_a(E) - 2`. If `(K_Y · E) < 0`, then `p_a(E) = 0`, so `E ≅ ℙ¹`, and
  `(E · E) = -1`: `E` is an exceptional `(-1)`-curve, which minimality excludes.

## Main results

* `MMP.Mori.intersectionNumber_projection_and_surface_curve`: the projection formula, adjunction
  and genus, and intersections of distinct curves, over a field of characteristic zero.
* `MMP.Mori.IsMinimalSurfaceResolution.exists_isIntersectionNumber_canonical_nonneg`: on a
  minimal resolution, the intersection number `(K_Y · E)` with every exceptional curve `E` is
  defined and nonnegative.

## Implementation notes

The intersection number `(g^*L · C)` is `MMP.Mori.QDivisor.intersectionNumber` of `L` along the
composite `C ⟶ Y' ⟶ Y`: it is `(1 / m) · deg_C (g ∘ i)^* 𝒪_Y(mL)` for the Cartier index `m` of
`L`, which is the definition of `(g^*L · C)` of [KM, Notation 0.4(5)] and requires no pull-back of
Weil divisors along `g`. The image `g(C)` is the scheme-theoretic image of `C ⟶ Y`, which is its
reduced induced structure, and `deg(C / g(C))` is `AlgebraicGeometry.degreeOver` of `C ⟶ g(C)`,
the degree of the function field extension `k(C) / k(g(C))`.

On a smooth surface the irreducible curves are the prime divisors; a prime divisor `C` is read as
the divisor `1 · C` and as the reduced closed subscheme on its support. The curves `C` and `C'`
meet transversally at `q` when their local equations at `q` generate the maximal ideal of
`𝒪_{S,q}`, that is, form a regular system of parameters: both curves are smooth at `q` with
distinct tangent lines. That `C ≅ ℙ¹_k` is pinned as an isomorphism over `k`.

The relative nefness of `K_Y` asserts that `(K_Y · E)` is defined (`E` is proper and `K_Y` is
Cartier on the smooth surface `Y`) and that its value is nonnegative. The field must be
algebraically closed: over `ℝ`, a smooth conic without real points can be an exceptional curve with
`(E · E) = -1` and `(K_Y · E) = -1`, and the resolution is still minimal because the conic is not
isomorphic to `ℙ¹_ℝ`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Notation 0.4,
  Proposition 1.10, proofs of 4.5 and 4.7, §5.3
* [R. Hartshorne, *Algebraic geometry*][Har77], V.1
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

/-! ### Curves on smooth surfaces -/

/-- The reduced subscheme on the support of the divisor `1 · E` of a prime divisor `E` is `E`. -/
private theorem suppIdeal_single_one {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y]
    (E : Mori.PrimeDivisor Y) :
    DivisorWithCoeffs.suppIdeal (Finsupp.single E (1 : ℤ) : Divisor Y) = E.idealSheaf := by
  rw [← vanishingIdeal_closure_genericPoint_eq_idealSheaf E, DivisorWithCoeffs.suppIdeal]
  congr 1
  apply TopologicalSpace.Closeds.ext
  rw [TopologicalSpace.Closeds.coe_closure,
    ← AlgebraicGeometry.PrimeDivisor.support_eq_closure E, DivisorWithCoeffs.coe_supp,
    Finsupp.support_single_ne_zero _ one_ne_zero]
  simp

/-- **Adjunction along a prime divisor.** For a proper prime divisor `C` on a smooth surface,
`((K + C) · C) = 2 p_a(C) - 2`. -/
private theorem isIntersectionNumber_canonical_add_single {k : Type u} [Field k] [IsAlgClosed k]
    {S : Scheme.{u}} {sS : S ⟶ Spec (.of k)} [QuasiCompact sS] [IsLocallyNoetherian S]
    [IsNormal S] (hS : Mori.IsVariety k sS) (hsm : IsSmoothScheme sS)
    (hS2 : topologicalKrullDim S = 2) {K : Divisor S} (hK : K.IsCanonicalDivisor sS 2)
    (C : Mori.PrimeDivisor S) [IsProper (C.idealSheaf.subschemeι ≫ sS)] :
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
      (C.idealSheaf.subschemeι ≫ sS)
    IsIntersectionNumber sS (Divisor.toQDivisor (K + Finsupp.single C 1)) C.idealSheaf
      (2 * arithmeticGenus (C.idealSheaf.subschemeι ≫ sS) - 2) := by
  have hI := suppIdeal_single_one C
  have hpr : IsProper ((DivisorWithCoeffs.suppIdeal
      (Finsupp.single C (1 : ℤ) : Divisor S)).subschemeι ≫ sS) := by
    rw [hI]
    infer_instance
  have h := MMP.Threefold.isIntersectionNumber_canonical_add_eq_neg_two_mul_eulerCharacteristic
    hS hsm hS2 hK _ (fun F hF => by
      rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hF
      rw [hF, Finsupp.single_eq_same]) hpr
  revert h hpr
  generalize DivisorWithCoeffs.suppIdeal (Finsupp.single C (1 : ℤ) : Divisor S) = I at hI ⊢
  subst hI
  intro _ h
  convert h using 1
  rw [MMP.Mori.arithmeticGenus]
  push_cast
  ring

/-- Over an algebraically closed field `k`, a nonzero finite-dimensional quotient `A ⧸ J` of a
`k`-algebra is one-dimensional exactly when `J` is a maximal ideal. -/
private theorem finrank_quotient_eq_one_iff_isMaximal {k A : Type*} [Field k] [IsAlgClosed k]
    [CommRing A] [Algebra k A] {J : Ideal A} (hpos : 0 < Module.finrank k (A ⧸ J)) :
    Module.finrank k (A ⧸ J) = 1 ↔ J.IsMaximal := by
  refine ⟨fun h => ?_, fun hJ => ?_⟩
  · have hb := (Algebra.finrank_eq_one_iff_bijective_algebraMap (F := k) (E := A ⧸ J)).mp h
    exact Ideal.Quotient.maximal_of_isField J
      ((RingEquiv.ofBijective _ hb).symm.toMulEquiv.isField (Field.toIsField k))
  · letI := Ideal.Quotient.field J
    have : Module.Finite k (A ⧸ J) := Module.finite_of_finrank_pos hpos
    exact (Algebra.finrank_eq_one_iff_bijective_algebraMap).mpr
      IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- The local ideal of the divisor `1 · E` of a prime divisor `E` is the ideal of `E`. -/
private theorem localIdeal_single_one {Y : Scheme.{u}} (q : Y) (E : Mori.PrimeDivisor Y) :
    localIdeal q (Finsupp.single E 1) = IdealSheafData.stalk E.idealSheaf q := by
  simp [localIdeal, Finsupp.support_single_ne_zero]

/-- Over an algebraically closed field, a positive local intersection number of two prime
divisors at `y` is one exactly when their ideals generate the maximal ideal of `𝒪_{S,y}`. -/
private theorem localIntersectionNumber_eq_one_iff {k : Type u} [Field k] [IsAlgClosed k]
    {S : Scheme.{u}} (sS : S ⟶ Spec (.of k)) (y : S)
    (C C' : Mori.PrimeDivisor S)
    (hpos : 0 < localIntersectionNumber sS y (Finsupp.single C 1) (Finsupp.single C' 1)) :
    localIntersectionNumber sS y (Finsupp.single C 1) (Finsupp.single C' 1) = 1 ↔
      IdealSheafData.stalk C.idealSheaf y ⊔ IdealSheafData.stalk C'.idealSheaf y =
        IsLocalRing.maximalIdeal (S.presheaf.stalk y) := by
  letI := stalkAlgebra sS y
  simp only [localIntersectionNumber] at hpos ⊢
  rw [localIdeal_single_one, localIdeal_single_one] at hpos ⊢
  rw [finrank_quotient_eq_one_iff_isMaximal hpos]
  exact ⟨IsLocalRing.eq_maximalIdeal, fun h => h ▸ inferInstance⟩

/-- A sum of positive natural numbers over a finite set vanishes exactly when the set is
empty. -/
private theorem finsum_mem_eq_zero_iff_of_pos {ι : Type*} {T : Set ι} (hT : T.Finite)
    {f : ι → ℕ} (hf : ∀ y ∈ T, 0 < f y) : ∑ᶠ y ∈ T, f y = 0 ↔ T = ∅ := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hT, Finset.sum_eq_zero_iff,
    Set.eq_empty_iff_forall_notMem]
  simp only [Set.Finite.mem_toFinset]
  exact ⟨fun h y hy => (hf y hy).ne' (h y hy), fun h y hy => absurd hy (h y)⟩

/-- A sum of positive natural numbers over a finite set `T` is `1` exactly when `T` is a
singleton `{q}` with `f q = 1`. -/
private theorem finsum_mem_eq_one_iff_of_pos {ι : Type*} {T : Set ι} (hT : T.Finite)
    {f : ι → ℕ} (hf : ∀ y ∈ T, 0 < f y) : ∑ᶠ y ∈ T, f y = 1 ↔ ∃ q, T = {q} ∧ f q = 1 := by
  refine ⟨fun h => ?_, by rintro ⟨q, rfl, hq⟩; simpa using hq⟩
  obtain ⟨q, hq⟩ : T.Nonempty := Set.nonempty_iff_ne_empty.mpr (by rintro rfl; simp at h)
  rw [finsum_mem_eq_finite_toFinset_sum _ hT] at h
  have h1 := Finset.sum_le_one_iff.mp h.le
  simp only [Set.Finite.mem_toFinset] at h1
  exact ⟨q, Set.eq_singleton_iff_unique_mem.mpr ⟨hq, fun y hy =>
    (h1 y q hy hq (hf y hy).ne' (hf q hq).ne').1⟩, (h1 q q hq hq (hf q hq).ne' (hf q hq).ne').2⟩

/-- **Projection formula, adjunction, genus and intersections of curves on surfaces.**
Let `k` be an algebraically closed field of characteristic zero.

1. Let `g : Y' ⟶ Y` be a proper morphism of varieties over `k` with `Y` normal, `L` a `ℚ`-Cartier
   `ℚ`-divisor on `Y` and `i : C ⟶ Y'` a proper irreducible closed curve. If `g(C)` is a point,
   then `(g^*L · C) = 0`; otherwise `(g^*L · C) = [k(C) : k(g(C))] · (L · g(C))`.
2. Let `S` be a smooth surface over `k`, `K` a canonical divisor of `S` and `C` a prime divisor of
   `S` proper over `k`. Then `((K + C) · C) = 2 p_a(C) - 2`, `p_a(C) ≥ 0`, and `p_a(C) = 0` if and
   only if `C ≅ ℙ¹_k` over `k`.
3. Let `C ≠ C'` be prime divisors of a smooth surface `S` over `k`, with `C` proper over `k`.
   Then `(C' · C)` is defined and nonnegative; it vanishes iff `C ∩ C' = ∅`; and it equals `1` iff
   `C ∩ C'` is a single point `q` at which the ideals of `C` and `C'` generate the maximal ideal of
   `𝒪_{S,q}`. -/
@[mmp "lem_mmp_foundation_km5b_surface_curve_package"]
public theorem intersectionNumber_projection_and_surface_curve
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] :
    (∀ {Y Y' C : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (sY' : Y' ⟶ Spec (.of k))
        [IsVariety k sY] [IsVariety k sY'] [IsNormal Y] (g : Y' ⟶ Y) [IsProper g]
        (hg : g ≫ sY = sY') (i : C ⟶ Y') [IsClosedImmersion i] [IsCurve k (i ≫ sY')]
        [IsProper (i ≫ sY')] (L : QDivisor Y)
        (hL : haveI := LocallyOfFiniteType.isLocallyNoetherian sY; L.IsQCartier),
      haveI := LocallyOfFiniteType.isLocallyNoetherian sY
      haveI : IsCurve k ((i ≫ g) ≫ sY) := by rw [Category.assoc, hg]; infer_instance
      haveI : IsProper ((i ≫ g) ≫ sY) := by rw [Category.assoc, hg]; infer_instance
      haveI : IsProper (i ≫ g) := IsProper.of_comp (i ≫ g) sY
      haveI : IsProper ((i ≫ g).imageι ≫ sY) := isProper_imageι_comp (i ≫ g) sY
      ((∃ y : Y, Set.range (i ≫ g) = {y}) →
          L.intersectionNumber k sY (i ≫ g)
            (IsCurve.topologicalKrullDim_eq_one (f := i ≫ sY')).le hL = 0) ∧
        ((¬ ∃ y : Y, Set.range (i ≫ g) = {y}) →
          L.intersectionNumber k sY (i ≫ g)
              (IsCurve.topologicalKrullDim_eq_one (f := i ≫ sY')).le hL =
            (degreeOver (i ≫ g).toImage : ℚ) *
              L.intersectionNumber k sY (i ≫ g).imageι
                (topologicalKrullDim_image_le_one sY (i ≫ g)) hL)) ∧
    (∀ {S : Scheme.{u}} (sS : S ⟶ Spec (.of k)) [IsVariety k sS] (hsm : IsSmoothScheme sS)
        (_ : topologicalKrullDim S = 2),
      haveI := (Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hsm).1
      haveI := (Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hsm).2
      ∀ (K : Divisor S) (_ : K.IsCanonicalDivisor sS 2) (C : PrimeDivisor S)
        [IsProper (C.idealSheaf.subschemeι ≫ sS)],
        haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
          (C.idealSheaf.subschemeι ≫ sS)
        IsIntersectionNumber sS (Divisor.toQDivisor (K + Finsupp.single C 1)) C.idealSheaf
            (2 * arithmeticGenus (C.idealSheaf.subschemeι ≫ sS) - 2) ∧
          0 ≤ arithmeticGenus (C.idealSheaf.subschemeι ≫ sS) ∧
          (arithmeticGenus (C.idealSheaf.subschemeι ≫ sS) = 0 ↔
            ∃ e : projectiveLine k ≅ C.idealSheaf.subscheme,
              e.hom ≫ C.idealSheaf.subschemeι ≫ sS = projectiveLine k ↘ Spec (.of k))) ∧
    (∀ {S : Scheme.{u}} (sS : S ⟶ Spec (.of k)) [IsVariety k sS] (hsm : IsSmoothScheme sS)
        (_ : topologicalKrullDim S = 2),
      haveI := (Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hsm).1
      haveI := (Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hsm).2
      ∀ (C C' : PrimeDivisor S) (_ : C ≠ C') [IsProper (C.idealSheaf.subschemeι ≫ sS)],
        ∃ n : ℚ, IsIntersectionNumber sS (Finsupp.single C' 1) C.idealSheaf n ∧ 0 ≤ n ∧
          (n = 0 ↔ C.support ∩ C'.support = ∅) ∧
          (n = 1 ↔ ∃ q : S, C.support ∩ C'.support = {q} ∧
            IdealSheafData.stalk C.idealSheaf q ⊔ IdealSheafData.stalk C'.idealSheaf q =
              IsLocalRing.maximalIdeal (S.presheaf.stalk q))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro Y Y' C sY sY' _ _ _ g _ hg i _ _ _ L hL
    have := LocallyOfFiniteType.isLocallyNoetherian sY
    have : Mori.IsCurve k ((i ≫ g) ≫ sY) := by
      rw [Category.assoc, hg]
      infer_instance
    have : IsProper ((i ≫ g) ≫ sY) := by
      rw [Category.assoc, hg]
      infer_instance
    have := QuasiCompact.compactSpace_of_compactSpace sY
    have := (QDivisor.isCartierDivisor_cartierIndex_smul hL).isCartier_toDivisor
      |>.isInvertibleModule_divisorialSheaf
    refine ⟨fun hpt => ?_, fun hnc => ?_⟩
    · rw [QDivisor.intersectionNumber, Divisor.degreeOn,
        degreeOn_eq_zero_of_range_eq_singleton sY (i ≫ g) _ hpt]
      simp
    · rw [QDivisor.intersectionNumber, QDivisor.intersectionNumber, Divisor.degreeOn,
        Divisor.degreeOn, degreeOn_eq_degreeOver_mul sY (i ≫ g) _ hnc]
      push_cast
      ring
  · intro S sS _ hsm hS2 K hK C _
    obtain ⟨_, _⟩ := Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hsm
    have := C.integral
    exact ⟨isIntersectionNumber_canonical_add_single inferInstance hsm hS2 hK C,
      arithmeticGenus_nonneg_and_eq_zero_iff (C.idealSheaf.subschemeι ≫ sS)
        (MMP.Flips.isCurveIn_idealSheaf_of_topologicalKrullDim_eq_two (sY := sS) inferInstance
          hS2 C).2⟩
  · intro S sS _ hsm hS2 C C' hne _
    obtain ⟨_, _⟩ := Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hsm
    obtain ⟨hfin, hI, hpos⟩ := isIntersectionNumber_finsum_localIntersectionNumber_of_ne sS
      inferInstance hsm hS2 hne inferInstance
    rw [← Nat.cast_finsum_mem hfin] at hI
    refine ⟨_, hI, Nat.cast_nonneg _, ?_, ?_⟩
    · rw [Nat.cast_eq_zero, finsum_mem_eq_zero_iff_of_pos hfin hpos]
    · rw [Nat.cast_eq_one, finsum_mem_eq_one_iff_of_pos hfin hpos]
      exact exists_congr fun q => and_congr_right fun hq =>
        localIntersectionNumber_eq_one_iff sS q C C' (hpos q (hq ▸ rfl))

/-! ### The canonical divisor of a minimal resolution -/

section

variable {k : Type u} [Field k] {Y : Scheme.{u}}

/-- A curve on an integral surface of finite type over `k` is a prime divisor, and its support is
the closure of the generic point of that divisor. -/
private lemma exists_primeDivisor_of_isCurveIn (s : Y ⟶ Spec (.of k)) [IsIntegral Y]
    [LocallyOfFiniteType s] [IsLocallyNoetherian Y] [IsNormal Y] (hYd : topologicalKrullDim Y = 2)
    {C : Y.IdealSheafData} (hC : IsCurveIn C) :
    ∃ Q : MMP.Mori.PrimeDivisor Y, Q.idealSheaf = C ∧
      closure ({Q.genericPoint} : Set Y) = C.support := by
  have : IsIntegral C.subscheme := hC.1
  obtain ⟨c, hcC, -⟩ := hC.exists_isGenericPoint
  have hcoh : Order.coheight c = 1 := by
    have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight s c
    rw [hcC, ← topologicalKrullDim_subscheme_eq, hC.2, hYd] at h
    generalize Order.coheight c = d at h ⊢
    induction d using ENat.recTopCoe with
    | top => exact absurd h (by decide)
    | coe d =>
      have : 1 + d = 2 := Nat.cast_injective (R := WithBot ℕ∞) (by push_cast; exact h)
      obtain rfl : d = 1 := by omega
      rfl
  let Q : MMP.Mori.PrimeDivisor Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne c hcoh
  have hQξ : Q.genericPoint = c := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  refine ⟨Q, ?_, by rw [hQξ, hcC]⟩
  rw [← vanishingIdeal_closure_genericPoint_eq_idealSheaf, hQξ,
    ← vanishingIdeal_support_eq_self C]
  exact congrArg _ (TopologicalSpace.Closeds.ext hcC)

/-- The generic point of a prime divisor whose subscheme is a proper curve is a proper curve. -/
private lemma isProperCurve_genericPoint [IsLocallyNoetherian Y] [IsNormal Y]
    {s : Y ⟶ Spec (.of k)} {Q : MMP.Mori.PrimeDivisor Y}
    (hQ : topologicalKrullDim Q.idealSheaf.subscheme = 1)
    (hQp : IsProper (Q.idealSheaf.subschemeι ≫ s)) : IsProperCurve s Q.genericPoint := by
  have h := vanishingIdeal_closure_genericPoint_eq_idealSheaf Q
  refine ⟨?_, ?_⟩
  · change topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure ({Q.genericPoint} : Set Y))).subscheme = 1
    rwa [h]
  · change IsProper ((Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure ({Q.genericPoint} : Set Y))).subschemeι ≫ s)
    rwa [h]

/-- A curve which a morphism contracts to a point lies in its exceptional set. -/
private lemma support_subset_exceptionalSet {X : Scheme.{u}} {f : Y ⟶ X}
    {C : Y.IdealSheafData} (hC : IsExceptionalCurve f C) :
    (C.support : Set Y) ⊆ (exceptionalSet f : Set Y) := by
  obtain ⟨hCcurve, x, hx⟩ := hC
  have hfC : ∀ y ∈ (C.support : Set Y), f y = x := fun y hy ↦
    Set.mem_singleton_iff.mp (hx ▸ Set.mem_image_of_mem f.base hy)
  intro y hy hybir
  have : IsIso (f ∣_ biregularLocus f) := isBiregular_biregularLocus f
  refine hCcurve.not_subsingleton fun a ha b hb ↦ ?_
  have hxV : f a ∈ biregularLocus f := by rwa [hfC a ha, ← hfC y hy]
  exact Stacks.Models.eq_of_isIso_morphismRestrict f _ hxV ((hfC a ha).trans (hfC b hb).symm)

/-- The arithmetic of adjunction: if `(K · E) + (E · E) = 2 p_a(E) - 2` with `p_a(E) ≥ 0`,
`(E · E) < 0` an integer and `(K · E) < 0`, then `p_a(E) = 0` and `(E · E) = -1`. -/
private lemma eq_zero_and_eq_neg_one_of_neg {p z : ℤ} {n : ℚ} (hp : 0 ≤ p) (hz : z < 0)
    (hn : n < 0) (h : n + z = 2 * p - 2) : p = 0 ∧ z = -1 := by
  have : ((2 * p - 2 - z : ℤ) : ℚ) < 0 := by push_cast; linarith
  have : 2 * p - 2 - z < 0 := by exact_mod_cast this
  omega

/-- On a smooth surface over an algebraically closed field, a proper curve `E` with `(E · E) < 0`
and `(K · E) < 0` is a smooth rational curve with `(E · E) = -1`. -/
private lemma isSmoothRationalCurve_and_self_eq_neg_one [IsAlgClosed k] {s : Y ⟶ Spec (.of k)}
    [QuasiCompact s] [IsLocallyNoetherian Y] [IsNormal Y]
    (hY : MMP.Mori.IsVariety k s) (hYs : IsSmoothScheme s) (hYd : topologicalKrullDim Y = 2)
    {K : Divisor Y} (hK : K.IsCanonicalDivisor s 2) {Q : MMP.Mori.PrimeDivisor Y}
    (hQ : IsCurveIn Q.idealSheaf) [hQp : IsProper (Q.idealSheaf.subschemeι ≫ s)]
    {n : ℚ} (hKQ : IsIntersectionNumber s (Divisor.toQDivisor K) Q.idealSheaf n) (hn : n < 0)
    {z : ℤ} (hQQ : IsIntersectionNumber s (Divisor.toQDivisor (Finsupp.single Q 1))
      Q.idealSheaf z) (hz : z < 0) :
    IsSmoothRationalCurve s Q.idealSheaf ∧
      IsIntersectionNumber s (Finsupp.single Q 1) Q.idealSheaf (-1) := by
  have : IsIntegral Q.idealSheaf.subscheme := hQ.1
  have := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k (Q.idealSheaf.subschemeι ≫ s)
  have hadj := isIntersectionNumber_canonical_add_single hY hYs hYd hK Q
  rw [map_add] at hadj
  obtain ⟨hpa0, hpaiff⟩ := arithmeticGenus_nonneg_and_eq_zero_iff (Q.idealSheaf.subschemeι ≫ s) hQ.2
  obtain ⟨hpa, rfl⟩ := eq_zero_and_eq_neg_one_of_neg hpa0 hz hn
    ((MMP.Flips.isIntersectionNumber_add hKQ hQQ).unique hadj)
  obtain ⟨e, he⟩ := hpaiff.mp hpa
  refine ⟨⟨⟨hQ, hQp, e.hom, he, inferInstance, isBirationalMorphism_of_isIso _⟩, e, he⟩, ?_⟩
  rw [MMP.Threefold.Resolution.toQDivisor_single] at hQQ
  exact_mod_cast hQQ

end

/-- Let `f : Y ⟶ X` be a minimal resolution of a normal surface `X` over an algebraically closed
field `k`, and `K` a canonical divisor of `Y`. Then for every `f`-exceptional curve `C` the
intersection number `(K · C)` is defined and nonnegative. -/
@[mmp "lem_km4a_minimal_resolution_canonical_relatively_nef"]
public theorem IsMinimalSurfaceResolution.exists_isIntersectionNumber_canonical_nonneg
    {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) (hdim : topologicalKrullDim X = 2)
    {f : Y ⟶ X} [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y]
    (hf : IsMinimalSurfaceResolution sX f)
    {K : Divisor Y} (hK : K.IsCanonicalDivisor (f ≫ sX) 2)
    {C : Y.IdealSheafData} (hC : IsExceptionalCurve f C) :
    ∃ n : ℚ, IsIntersectionNumber (f ≫ sX) (Divisor.toQDivisor K) C n ∧ 0 ≤ n := by
  have hXv := hX.1
  have : IsIntegral X := hXv.toIsIntegral
  have : LocallyOfFiniteType sX := hXv.toLocallyOfFiniteType
  obtain ⟨hYn, hYd, -⟩ := hf.1.isNormalVariety hX
  rw [hdim] at hYd
  have hYv := hYn.1
  have hYs : IsSmoothScheme (f ≫ sX) := hf.1.isSmoothScheme
  have : IsProper f := hf.1.isProper
  have : IsIntegral Y := hYv.toIsIntegral
  have : LocallyOfFiniteType (f ≫ sX) := hYv.toLocallyOfFiniteType
  have hexc := support_subset_exceptionalSet hC
  obtain ⟨hCcurve, x, hx⟩ := hC
  obtain ⟨Q, rfl, hQcl⟩ := exists_primeDivisor_of_isCurveIn (f ≫ sX) hYd hCcurve
  have hfQ : ∀ y ∈ (Q.idealSheaf.support : Set Y), f y = x := fun y hy ↦
    Set.mem_singleton_iff.mp (hx ▸ Set.mem_image_of_mem f.base hy)
  have hxcl : IsClosed ({x} : Set X) := by
    rw [← hx]
    exact f.isClosedMap _ Q.idealSheaf.support.isClosed
  have : IsIntegral Q.idealSheaf.subscheme := hCcurve.1
  have hQp : IsProper (Q.idealSheaf.subschemeι ≫ f ≫ sX) := by
    rw [← Category.assoc]
    refine isProper_comp_of_range_subset_singleton sX _ hxcl ?_
    rintro _ ⟨z, rfl⟩
    exact hfQ _ (Q.idealSheaf.range_subschemeι ▸ ⟨z, rfl⟩)
  let CQ : ProperCurve (f ≫ sX) := ⟨Q.genericPoint, isProperCurve_genericPoint hCcurve.2 hQp⟩
  have : IsProper (CQ.ι ≫ f ≫ sX) := CQ.isProper_ι_comp
  have hCQ : CQ.IsContractedBy f := fun y hy ↦ by
    rw [hQcl] at hy
    rw [hfQ y hy, hfQ _ (hQcl ▸ subset_closure rfl)]
  have hneg := MMP.Threefold.Resolution.intersectionNumber_self_neg_of_isBirationalMorphism hYv
    hYs hYd hXv rfl hf.1.isBirationalMorphism Q CQ rfl hCQ
  obtain ⟨z, hz⟩ : ∃ z : ℤ, (Divisor.toQDivisor (Finsupp.single Q 1)).intersectionNumber k
      (f ≫ sX) CQ.ι CQ.dim_le (MMP.Threefold.Mori.isQCartier_single_of_isSmoothScheme hYs Q) = z :=
    ⟨_, QDivisor.intersectionNumber_toQDivisor k (f ≫ sX) CQ.ι CQ.dim_le _
      (MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hYs Q) _⟩
  have hQQ := isIntersectionNumber_of_properCurve _
    (MMP.Threefold.Mori.isQCartier_single_of_isSmoothScheme hYs Q) CQ Q rfl
  rw [hz] at hneg hQQ
  have hKQ := isIntersectionNumber_of_properCurve (Divisor.toQDivisor K)
    (MMP.Fourfold.isQCartier_of_isSmoothScheme hYs _) CQ Q rfl
  exact ⟨_, hKQ, not_lt.mp fun hn ↦ hf.2 ⟨Q, hexc, isSmoothRationalCurve_and_self_eq_neg_one
    hYv hYs hYd hK hCcurve hKQ hn hQQ (by exact_mod_cast hneg)⟩⟩

end MMP.Mori

end
