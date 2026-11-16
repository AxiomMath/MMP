module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Intersection.OneCycles
public import MMP.AlgebraicGeometry.Intersection.Nef
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
public import MMP.AlgebraicGeometry.Positivity.AmpleNumerical
public import MMP.AlgebraicGeometry.Vanishing.KodairaSerreDual
public import MMP.AlgebraicGeometry.Intersection.EulerCharacteristicNumerical
public import MMP.AlgebraicGeometry.Resolution.Principalization.ResolutionPrincipalization
public import MMP.AlgebraicGeometry.Positivity.BigAmplePlusEffective
public import MMP.AlgebraicGeometry.Intersection.BirationalInvariance
public import MMP.AlgebraicGeometry.Divisor.SmoothWeilCartier
public import MMP.AlgebraicGeometry.MMP.Threefold.Basic
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
public import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
public import MMP.AlgebraicGeometry.Divisor.PullbackExistence
public import MMP.AlgebraicGeometry.Resolution.BlowupChartClosedImmersion
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafMul

/-!
# Nef Cartier divisors with positive top self-intersection are big

Let `X` be a projective variety of dimension `n` over an algebraically closed field `k` of
characteristic zero, and `D` a Cartier divisor on `X` which is nef (`deg_C 𝒪_X(D) ≥ 0` for every
closed curve `C ⊆ X`) with `(Dⁿ) > 0`. Then `D` is big: `h⁰(X, 𝒪_X(mD)) > c mⁿ` for some
`c > 0` and all large `m`. This is the converse of
`MMP.Mori.sheafSelfIntersectionNumber_pos_of_isNef_of_isBigCartier`.

## Main results

* `MMP.Mori.isBigCartier_of_isNef_of_sheafSelfIntersectionNumber_pos`: a nef Cartier divisor
  `D` on a projective variety of dimension `n` with `(Dⁿ) > 0` is big.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Prop. 2.61
-/

@[expose] public section

section

/-!
## Proof: Nef Cartier divisors with positive top self-intersection are big

Let `X` be a projective variety of dimension `n` over an algebraically closed field `k` of
characteristic zero and `D` a nef Cartier divisor with `(Dⁿ) > 0`. Then `D` is big:
`h⁰(X, 𝒪_X(mD)) > c mⁿ` for some `c > 0` and all large `m`.

A resolution `g : X' ⟶ X` reduces the statement to `X` smooth: `g^*D` is nef, because the degree
of `g^*𝒪_X(D)` on a curve `C ⊆ X'` is `0` or a positive multiple of the degree of `𝒪_X(D)` on the
image curve; `((g^*D)ⁿ) = (Dⁿ)` since `g` is birational; and bigness is a birational invariant.

On smooth `X`, let `K` be a canonical divisor, `H` an ample divisor and `B = K + H`. For `m ≥ 0`
the divisor `mD + B - K = H + mD` is ample (ample plus nef), so Kodaira vanishing gives
`h⁰(X, 𝒪_X(mD + B)) = χ(X, 𝒪_X(mD + B))`. The Euler characteristic `χ(𝒪_X(aD + bB))` is a
polynomial `P(a, b)` of total degree at most `n` whose degree-`n` part takes the value `(Dⁿ)/n!`
at `(1, 0)`, so `χ(𝒪_X(mD + B)) = (Dⁿ)/n! · mⁿ + O(m^{n-1})`. Finally
`h⁰(𝒪_X(mD + B)) ≤ h⁰(𝒪_X(mD)) + O(m^{n-1})`: the difference sequences
`0 → 𝒜 → 𝒪_X → 𝒬 → 0`, `0 → 𝒜 → 𝒪_X(-B) → 𝒬' → 0` of a regular meromorphic section of
`𝒪_X(-B)` have `dim Supp 𝒬 ≤ n - 1`, and twisting them by `𝒪_X(B) ⊗ 𝒪_X(D)^{⊗ m}` bounds the
difference by `h⁰` of a twist of `𝒬`, which grows like `m^{n-1}`.

## Main results

* `MMP.Mori.isBigCartier_of_isNef_of_sheafSelfIntersectionNumber_pos`: Kollár–Mori 2.61,
  (2) ⇒ (1).

## Implementation notes

The source takes `B` to be the zero divisor of a non-zero section of `𝒪_X(rH)`, with `rH - K_X`
ample, so that `B` is effective and `0 → 𝒪_X(mD) → 𝒪_X(mD + B) → 𝒪_B(mD + B)` bounds
`h⁰(mD + B) - h⁰(mD)` by sections on `B`. Here `B = K + H` need not be effective; the same bound
comes from the difference sequences of `𝒪_X(-B)` twisted by `𝒪_X(B)`, whose cokernels are
supported in dimension `n - 1` exactly as `𝒪_B(B)` is.

When `n = 0`, `X` is a point, every invertible sheaf on it is trivial and
`h⁰(𝒪_X(mD)) = h⁰(𝒪_X(mD + B)) = (D⁰) ≥ 1`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Prop. 2.61
-/

namespace MMP.FourfoldProofs.Km2cBigOfNefTopPositiveComplexProof

open MMP.Mori.TwistGrowth

open CategoryTheory AlgebraicGeometry

section Pullback

/-- Along a dominant morphism of integral locally Noetherian schemes every Cartier divisor has a
pull-back. -/
private theorem exists_isPullback_of_isDominant {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (g : Y ⟶ X) [IsDominant g]
    (D : X.CartierDivisor) : ∃ D', MMP.Intersection.IsPullback g D D' := by
  refine MMP.Intersection.exists_isPullback fun η hη => ?_
  rw [schemeAssociatedPoints_eq_singleton_genericPoint, Set.mem_singleton_iff] at hη
  rw [hη, MMP.Positivity.map_genericPoint_eq_of_isDominant g]
  have : IsArtinianRing (X.presheaf.stalk (genericPoint X)) :=
    (inferInstance : IsArtinianRing X.functionField)
  exact MMP.Intersection.notMem_cartierSupport_of_isArtinianRing D _

/-- The intersection number depends on the structure morphism only through its value. -/
private theorem sheafIntersectionNumber_congr_structure (k : Type) [Field k] {X Z : Scheme.{0}}
    {s s' : X ⟶ Spec (.of k)} (hs : s = s') [IsProper s] [IsProper s'] {i : Z ⟶ X}
    [IsClosedImmersion i] {d : ℕ} {hd : topologicalKrullDim Z ≤ d} {L : Fin d → X.Modules}
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] :
    MMP.Mori.sheafIntersectionNumber k s i d hd L =
      MMP.Mori.sheafIntersectionNumber k s' i d hd L := by
  subst hs; rfl

/-- The intersection number depends on the closed immersion only through its value. -/
private theorem sheafIntersectionNumber_congr_closedImmersion (k : Type) [Field k]
    {X Z : Scheme.{0}} {s : X ⟶ Spec (.of k)} [IsProper s] {i i' : Z ⟶ X} (hi : i = i')
    [IsClosedImmersion i] [IsClosedImmersion i'] {d : ℕ} {hd : topologicalKrullDim Z ≤ d}
    {L : Fin d → X.Modules} [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] :
    MMP.Mori.sheafIntersectionNumber k s i d hd L =
      MMP.Mori.sheafIntersectionNumber k s i' d hd L := by
  subst hi; rfl

end Pullback

section Growth

open MMP.Mori MMP.Intersection
open scoped Stacks.SmallDerivedModel

variable {k : Type} [Field k] {X : Scheme.{0}}

/-- **`h⁰` of a fixed twist exceeds `h⁰` by `O(m^{n-1})`.** On a projective variety `X` of
dimension `n ≥ 1`, for Cartier divisors `B` and `D` there is `C > 0` with
`h⁰(X, 𝒪_X(mD + B)) ≤ h⁰(X, 𝒪_X(mD)) + C m^{n-1}` for all `m > 0`. -/
private theorem cartierH0_add_le_add_pow (f : X ⟶ Spec (.of k))
    (hX : MMP.Mori.IsProjectiveVariety k f) {n : ℕ} (hn : topologicalKrullDim X = n)
    (hn1 : 1 ≤ n) (B D : X.CartierDivisor) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m → (cartierH0 k f (m • D + B) : ℝ) ≤
      cartierH0 k f (m • D) + C * (m : ℝ) ^ (n - 1) := by
  have : IsIntegral X := hX.toIsIntegral
  have : LocallyOfFiniteType f := hX.toLocallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsProper f := isProper_of_isProjectiveMorphism f hX.isProjective
  set O := SheafOfModules.unit X.ringCatSheaf
  have hO := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k f
  have hsuppO : _root_.SheafOfModules.supp O = Set.univ := supp_unit_eq_univ X
  have hdimO : natDimSupp O = n := by
    have := coe_natDimSupp_eq k f O (by rw [hsuppO]; exact Set.univ_nonempty.ne_empty)
    rw [topologicalKrullDim_supp_unit, hn] at this
    exact_mod_cast this
  obtain ⟨s, hs⟩ := exists_isRegularMeromorphicSection_of_hasNoEmbeddedPoints X
    (PlaneConic.hasNoEmbeddedPoints_of_isIntegral X) (sh (-B))
  obtain ⟨S, T, hS, hT, cS1, cS2, cS3, cT1, cT2, cT3, ⟨eS⟩, ⟨eT⟩, ⟨e01⟩, -, -, hS3, -⟩ :=
    exists_differenceSequences_of_supp_eq_univ k f (sh (-B)) O hO (by omega)
      (PlaneConic.hasNoEmbeddedPoints_of_isIntegral X) hsuppO s hs
  -- the twist by `𝒪_X(B)`
  let LB : Fin 1 → X.Modules := fun _ => sh B
  let F := twistedSheafFunctor LB (fun _ => (1 : ℤ))
  have hS' : (S.map F).ShortExact := shortExact_map_twistedSheafFunctor LB hS _
  have hT' : (T.map F).ShortExact := shortExact_map_twistedSheafFunctor LB hT _
  have hcoh : ∀ G : X.Modules, _root_.SheafOfModules.IsCoherent G →
      _root_.SheafOfModules.IsCoherent (F.obj G) := fun G hG => by
    have := hG
    rw [twistedSheafFunctor_obj]
    exact twistedSheaf_isCoherent G LB _
  have hsupp : _root_.SheafOfModules.supp (F.obj S.X₃) ⊆ _root_.SheafOfModules.supp S.X₃ := by
    intro x hx
    by_contra hx'
    rw [twistedSheafFunctor_obj] at hx
    exact notMem_supp_tensorSheaf_of_notMem_supp S.X₃ _ hx' hx
  have hd3 : topologicalKrullDim (_root_.SheafOfModules.supp (F.obj S.X₃)) ≤
      ((n - 1 : ℕ) : WithBot ℕ∞) := by
    refine ((Topology.IsEmbedding.inclusion hsupp).isInducing.topologicalKrullDim_le).trans ?_
    by_cases h : _root_.SheafOfModules.supp S.X₃ = ∅
    · rw [(topologicalKrullDim_supp_eq_bot_iff _).2 h]
      exact bot_le
    · rw [← coe_natDimSupp_eq k f _ h]
      exact_mod_cast (by omega : natDimSupp S.X₃ ≤ n - 1)
  obtain ⟨C, hC, hb⟩ :=
    MMP.Foundations.exists_finrank_cohomologyOverField_zero_twistedSheaf_le_pow k f (sh D)
      (F.obj S.X₃) (hcoh _ cS3) (n - 1) hd3
  refine ⟨C, hC, fun m hm => ?_⟩
  obtain ⟨z⟩ := nonempty_sheaf_zero_iso (X := X)
  obtain ⟨j2⟩ := nonempty_twistedSheaf_iso (z ≪≫ eS.symm) B 1
  have eS' : sh (0 + (1 : ℤ) • B) ≅ F.obj S.X₂ :=
    j2.symm ≪≫ (twistedSheafFunctorObjIso LB _ S.X₂).symm
  have eA : sh (0 + -B) ≅ T.X₂ :=
    (MMP.CartierDivisorSheaf.sheafMulIso 0 (-B)).symm ≪≫
      ((tens X).mapIso z).app (sh (-B)) ≪≫ eT.symm
  obtain ⟨j3⟩ := nonempty_twistedSheaf_iso eA B 1
  have eT' : sh ((0 + -B) + (1 : ℤ) • B) ≅ F.obj T.X₂ :=
    j3.symm ≪≫ (twistedSheafFunctorObjIso LB _ T.X₂).symm
  obtain ⟨i2⟩ := nonempty_twistedSheaf_iso eS' D (m : ℤ)
  obtain ⟨i3⟩ := nonempty_twistedSheaf_iso eT' D (m : ℤ)
  have h2 : cartierH0 k f (m • D + B) = Module.finrank k (cohomologyOverField k f
      (twistedSheaf (F.obj S.X₂) (fun _ : Fin 1 => sh D) (fun _ => (m : ℤ))) 0) := by
    rw [cartierH0_eq_finrank, finrank_cohomologyOverField_eq_of_iso k f i2 0,
      show (0 + (1 : ℤ) • B) + (m : ℤ) • D = m • D + B by rw [natCast_zsmul]; abel]
  have h3 : cartierH0 k f (m • D) = Module.finrank k (cohomologyOverField k f
      (twistedSheaf (F.obj T.X₂) (fun _ : Fin 1 => sh D) (fun _ => (m : ℤ))) 0) := by
    rw [cartierH0_eq_finrank, finrank_cohomologyOverField_eq_of_iso k f i3 0,
      show (0 + -B + (1 : ℤ) • B) + (m : ℤ) • D = m • D by rw [natCast_zsmul]; abel]
  have hle1 := finrank_twistedSheaf_le_add k f (fun _ : Fin 1 => sh D) hS' (hcoh _ cS1)
    (hcoh _ cS2) (hcoh _ cS3) (fun _ => (m : ℤ))
  have hle2 := finrank_twistedSheaf_le_of_shortExact k f (fun _ : Fin 1 => sh D) hT'
    (hcoh _ cT2) (fun _ => (m : ℤ))
  simp only [ShortComplex.map_X₁, ShortComplex.map_X₂, ShortComplex.map_X₃] at hle1 hle2
  rw [finrank_cohomologyOverField_eq_of_iso k f (twistedSheafIsoOfIso _ (F.mapIso e01) _) 0]
    at hle1
  have hb' := hb m (by exact_mod_cast hm)
  push_cast at hb'
  rw [h2, h3]
  calc _ ≤ ((Module.finrank k (cohomologyOverField k f
          (twistedSheaf (F.obj T.X₁) (fun _ : Fin 1 => sh D) (fun _ => (m : ℤ))) 0) +
        Module.finrank k (cohomologyOverField k f
          (twistedSheaf (F.obj S.X₃) (fun _ : Fin 1 => sh D) (fun _ => (m : ℤ))) 0) : ℕ) : ℝ) := by
        exact_mod_cast hle1
    _ ≤ _ := by push_cast; gcongr

end Growth

section Polynomial

open MvPolynomial

/-- The value at `(1, 0)` of the degree-`n` homogeneous part of a polynomial in two variables is
the coefficient of `X₀ⁿ`. -/
private theorem eval_homogeneousComponent_one_zero (P : MvPolynomial (Fin 2) ℚ) (n : ℕ) :
    eval ![1, 0] (homogeneousComponent n P) = P.coeff (Finsupp.single 0 n) := by
  rw [homogeneousComponent_apply, map_sum]
  simp only [eval_monomial, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, one_pow, one_mul]
  rw [Finset.sum_eq_single (Finsupp.single 0 n)]
  · simp
  · intro s hs hne
    rw [Finset.mem_filter] at hs
    have h1 : s 1 ≠ 0 := by
      intro h1
      apply hne
      ext i
      fin_cases i
      · have := hs.2
        rw [Finsupp.degree_eq_sum, Fin.sum_univ_two, h1] at this
        simpa using this
      · simp [h1]
    simp [zero_pow h1]
  · intro h
    simp only [Finset.mem_filter, mem_support_iff, not_and_or, not_not] at h
    rcases h with h | h
    · simp [h]
    · exfalso
      apply h
      simp [Finsupp.degree_eq_sum, Fin.sum_univ_two]

/-- For a polynomial `P` in two variables of total degree at most `n`,
`P(m, 1) = c mⁿ + O(m^{n-1})` for `m ≥ 1`, where `c = P_n(1, 0)` is the value of the degree-`n`
homogeneous part at `(1, 0)`. -/
private theorem abs_eval_sub_le (P : MvPolynomial (Fin 2) ℚ) {n : ℕ} (hP : P.totalDegree ≤ n) :
    ∃ C : ℝ, ∀ m : ℕ, 1 ≤ m →
      |((eval ![(m : ℚ), 1] P : ℚ) : ℝ) -
        ((eval ![1, 0] (homogeneousComponent n P) : ℚ) : ℝ) * (m : ℝ) ^ n| ≤
        C * (m : ℝ) ^ (n - 1) := by
  classical
  refine ⟨∑ s ∈ P.support, |((P.coeff s : ℚ) : ℝ)|, fun m hm => ?_⟩
  rw [eval_homogeneousComponent_one_zero, eval_eq']
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, one_pow, mul_one]
  have hsplit : ((∑ s ∈ P.support, P.coeff s * (m : ℚ) ^ s 0 : ℚ) : ℝ) -
      ((P.coeff (Finsupp.single 0 n) : ℚ) : ℝ) * (m : ℝ) ^ n =
      ∑ s ∈ P.support.erase (Finsupp.single 0 n), ((P.coeff s : ℚ) : ℝ) * (m : ℝ) ^ s 0 := by
    push_cast
    by_cases h : Finsupp.single 0 n ∈ P.support
    · rw [← Finset.add_sum_erase _ _ h]
      simp
    · rw [Finset.erase_eq_of_notMem h]
      rw [mem_support_iff, not_not] at h
      simp [h]
  rw [hsplit, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun s hs => ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      fun _ _ _ => by positivity)
  have hs0 : s 0 ≤ n - 1 := by
    obtain ⟨hne, hs⟩ := Finset.mem_erase.mp hs
    have hdeg : s 0 + s 1 ≤ n := by
      have := (le_totalDegree hs).trans hP
      rwa [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at this
    have : s 0 ≠ n := by
      intro h0
      apply hne
      ext i
      fin_cases i
      · simpa using h0
      · simp; omega
    omega
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ s 0)]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hm1 hs0) (abs_nonneg _)

/-- The cast `ℤ → ℚ` commutes with `finsum`. -/
private theorem cast_finsum_int (g : ℕ → ℤ) : ((∑ᶠ j, g j : ℤ) : ℚ) = ∑ᶠ j, (g j : ℚ) :=
  (Int.castAddHom ℚ).map_finsum_of_injective Int.cast_injective g

/-- **Leading term beats a lower-order defect.** If `a m = c mⁿ + O(m^{n-1})` with `c > 0` and
`a m ≤ b m + O(m^{n-1})`, then `b m > (c / 2) mⁿ` for all large `m`. -/
private theorem exists_half_mul_pow_lt {a b : ℕ → ℝ} {c C₁ C₂ : ℝ} (hc : 0 < c) {n : ℕ}
    (hn : 1 ≤ n) (hab : ∀ m : ℕ, 0 < m → a m ≤ b m + C₁ * (m : ℝ) ^ (n - 1))
    (ha : ∀ m : ℕ, 1 ≤ m → |a m - c * (m : ℝ) ^ n| ≤ C₂ * (m : ℝ) ^ (n - 1)) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → c / 2 * (m : ℝ) ^ n < b m := by
  refine ⟨⌈2 * (|C₁| + |C₂|) / c⌉₊ + 1, fun m hm => ?_⟩
  have hm1 : 1 ≤ m := by omega
  have hcm : 2 * (|C₁| + |C₂|) < m * c := by
    rw [← div_lt_iff₀ hc]
    exact (Nat.le_ceil _).trans_lt (by exact_mod_cast hm)
  have hp : (0 : ℝ) < (m : ℝ) ^ (n - 1) := by positivity
  have hmn : (m : ℝ) ^ n = m * (m : ℝ) ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h1 := hab m hm1
  have h2 := (abs_le.mp (ha m hm1)).1
  rw [hmn] at h2 ⊢
  nlinarith [mul_lt_mul_of_pos_right hcm hp, mul_le_mul_of_nonneg_right (le_abs_self C₂) hp.le,
    mul_le_mul_of_nonneg_right (le_abs_self C₁) hp.le]

end Polynomial

open MMP.FourfoldProofs.Km2cEulerCharacteristicNumericalProof (weilOfCartier isAmple_weilOfCartier)

/-- An integral scheme of dimension zero is a point. -/
private theorem subsingleton_of_topologicalKrullDim_eq_zero {X : Scheme.{0}} [IsIntegral X]
    (h : topologicalKrullDim X = 0) : Subsingleton X := by
  have hmax := Order.krullDim_nonpos_iff_forall_isMax.mp h.le
  have key : ∀ z : X, z = genericPoint X := fun z => by
    let Z : TopologicalSpace.IrreducibleCloseds X :=
      ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩
    let U : TopologicalSpace.IrreducibleCloseds X :=
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
    have hU : U ≤ Z := hmax Z fun _ _ => trivial
    have hg : IsGenericPoint z Set.univ :=
      le_antisymm (Set.subset_univ _) (fun x hx => hU hx)
    exact hg.eq (genericPoint_spec X)
  exact ⟨fun x y => (key x).trans (key y).symm⟩

open MMP.Mori in
/-- **The smooth case.** On a smooth projective variety, a nef Cartier divisor `D` with
`(Dⁿ) > 0` is big. -/
private theorem isBigCartier_of_isSmoothScheme {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} (f : X ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k f]
    (hsm : IsSmoothScheme f) {n : ℕ} (hn : topologicalKrullDim X = n) (D : X.CartierDivisor)
    (hnef : IsNef k f (MMP.CartierDivisor.sheaf D))
    (hpos : 0 < sheafSelfIntersectionNumber k f (𝟙 X) n hn.le (MMP.CartierDivisor.sheaf D)) :
    IsBigCartier k f D := by
  have hXv : AlgebraicGeometry.IsVariety k f := inferInstance
  haveI : IsIntegral X := hXv.toIsIntegral
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : IsNoetherian X := ⟨⟩
  have hfproj : IsProjective f :=
    IsProjectiveMorphism.isProjective (IsProjectiveVariety.isProjective (k := k))
  haveI : IsProper f := hfproj.isProper
  haveI : Smooth f := MMP.Threefold.Resolution.smooth_of_isSmoothScheme hsm
  haveI : IsSmoothVariety k f := ⟨⟩
  haveI : IsNormal X := isNormal_of_smooth_over_field (k := k) f
  obtain ⟨hcart, -, ⟨-, hΦ⟩, hiso, hinv, -⟩ :=
    Divisor.cartier_weil_dictionary_of_isSmoothVariety k f
  replace hΦ : Function.Surjective (weilOfCartier X) := hΦ
  replace hiso : ∀ τ : X.CartierDivisor,
      Nonempty ((weilOfCartier X τ).divisorialSheaf ≅ MMP.CartierDivisor.sheaf τ) := hiso
  -- a canonical divisor `K` and an ample divisor `H`
  obtain ⟨K, hK⟩ := exists_isCanonicalDivisor_of_isSmoothScheme f hsm hn
  obtain ⟨τK, hτK⟩ := hΦ K
  obtain ⟨M, hM, hMa⟩ := Stacks.HProjective.exists_isAmple_of_isAffine (Spec (.of k))
  obtain ⟨L, hL, hLa⟩ := exists_isAmple_of_isProjectiveMorphism f M hMa
    AlgebraicGeometry.IsProjectiveVariety.isProjective
  obtain ⟨H, ⟨eH⟩⟩ := hinv L hL
  obtain ⟨τH, rfl⟩ := hΦ H
  have hHa : Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf τH) := by
    obtain ⟨e⟩ := hiso τH
    haveI := (hcart (weilOfCartier X τH)).isInvertibleModule_divisorialSheaf
    exact (Stacks.RelativeVeryAmple.isAmple_congr _ _
      (e.symm ≪≫ eH)).mpr hLa
  have hHq : (Divisor.toQDivisor (weilOfCartier X τH)).IsAmple :=
    ⟨1, one_pos, _, by simp, hcart _, isAmple_weilOfCartier hcart hiso τH hHa⟩
  set B : X.CartierDivisor := τK + τH with hB
  -- the Weil divisor of `D` is nef
  have hWDnef : (weilOfCartier X D).IsNef k f := by
    refine ⟨hcart _, fun C i _ _ _ hC => ?_⟩
    obtain ⟨e⟩ := hiso D
    haveI := (hcart (weilOfCartier X D)).isInvertibleModule_divisorialSheaf
    change 0 ≤ MMP.Mori.degreeOn k f i hC.le (weilOfCartier X D).divisorialSheaf
    rw [degreeOn_eq_of_iso k f i hC.le e]
    exact hnef C i hC
  -- Kodaira vanishing: `Hʲ(X, 𝒪_X(mD + B)) = 0` for `j > 0`
  have hvan : ∀ m : ℕ, ∀ j : ℕ, 0 < j → Module.finrank k (cohomologyOverField k f
      (MMP.CartierDivisor.sheaf (m • D + B)) j) = 0 := by
    intro m j hj
    have hNnef : (Divisor.toQDivisor (m • weilOfCartier X D)).IsNef k f :=
      (QDivisor.isNef_toQDivisor_iff (k := k) (sX := f) _ ((hcart _).nsmul m)).mpr
        ⟨(hcart _).nsmul m, fun C i _ _ _ hC => by
          rw [Divisor.degreeOn_nsmul' k f i hC.le _ (hcart _) m]
          exact mul_nonneg (Nat.cast_nonneg _) (hWDnef.2 C i hC)⟩
    have hEq : weilOfCartier X (m • D + B) - K =
        weilOfCartier X τH + m • weilOfCartier X D := by
      rw [hB, map_add, map_add, map_nsmul, hτK]; abel
    have hA : ∃ h : (weilOfCartier X (m • D + B) - K).IsCartier,
        (weilOfCartier X (m • D + B) - K).IsAmple h := by
      refine ⟨hcart _, QDivisor.isAmple_of_numericallyEquivalent_add_of_isNef f hHq hNnef
        (B := Divisor.toQDivisor (weilOfCartier X (m • D + B) - K)) ?_ 1 one_pos _
        (by simp) (hcart _)⟩
      rw [hEq, ← map_add]
      exact QDivisor.NumericallyEquivalent.refl (QDivisor.isQCartier_toQDivisor (hcart _))
    have hs := subsingleton_derivedCohomologyOverField_divisorialSheaf_of_isAmple_sub f hsm K
      (weilOfCartier X (m • D + B)) hK hA j (by omega)
    obtain ⟨e⟩ := hiso (m • D + B)
    rw [← finrank_cohomologyOverField_eq_of_iso k f e j,
      (Stacks.Duality.cohomologyOverFieldLinearEquivDerivedCohomologyOverField k f _
        j).finrank_eq]
    exact Module.finrank_zero_of_subsingleton
  -- Riemann–Roch: `χ(𝒪_X(aD + bB))` is a polynomial `P(a, b)` with leading part `(Dⁿ)/n!`
  obtain ⟨P, hdeg, hP⟩ :=
    MMP.Resolution.Bridges.exists_polynomial_eulerChar_cartierSheaf_sum k f n hn ![D, B]
  have hlead := MMP.Threefold.Mori.eval_homogeneousComponent_of_eulerChar k f hn ![D, B] P
    (fun m => by
      rw [hP m, MMP.Threefold.Mori.eulerCharCartierCombination, cast_finsum_int]; push_cast; rfl)
    ![1, 0]
  set c : ℚ := (sheafSelfIntersectionNumber k f (𝟙 X) n hn.le
    (MMP.CartierDivisor.sheaf D) : ℚ) / n.factorial with hc
  have hc10 : MvPolynomial.eval ![1, 0] (MvPolynomial.homogeneousComponent n P) = c := by
    have h1 : (fun i => (((![1, 0] : Fin 2 → ℤ) i : ℤ) : ℚ)) = ![1, 0] := by
      funext i; fin_cases i <;> simp
    have h2 : (∑ i, (![1, 0] : Fin 2 → ℤ) i • (![D, B] : Fin 2 → X.CartierDivisor) i) = D := by
      simp [Fin.sum_univ_two]
    rw [h1] at hlead
    rw [hlead, hc]
    congr 3
    rw [h2]
  have hχ : ∀ m : ℕ, MvPolynomial.eval ![(m : ℚ), 1] P = (cartierH0 k f (m • D + B) : ℚ) := by
    intro m
    have h := hP ![(m : ℤ), 1]
    have hm : (fun i => (((![(m : ℤ), 1] : Fin 2 → ℤ) i : ℤ) : ℚ)) = ![(m : ℚ), 1] := by
      funext i; fin_cases i <;> simp
    have hs : (∑ i, (![(m : ℤ), 1] : Fin 2 → ℤ) i • (![D, B] : Fin 2 → X.CartierDivisor) i) =
        m • D + B := by
      simp [Fin.sum_univ_two, natCast_zsmul]
    rw [hm, hs] at h
    rw [h, finsum_eq_single _ 0 (fun j hj => by rw [hvan m j (by omega)]; simp)]
    simp [cartierH0_eq_finrank k f]
  have hcpos : (0 : ℝ) < (c : ℝ) := by
    rw [hc]; push_cast
    exact div_pos (by exact_mod_cast hpos) (by positivity)
  refine ⟨n, hn, (c : ℝ) / 2, by positivity, ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · -- a point: `𝒪_X(mD) ≅ 𝒪_X ≅ 𝒪_X(mD + B)`
    haveI := subsingleton_of_topologicalKrullDim_eq_zero hn
    refine ⟨0, fun m hm => ?_⟩
    lift m to ℕ using hm
    obtain ⟨t⟩ : Nonempty X := inferInstance
    have h1 : cartierH0 k f ((m : ℤ) • D) = cartierH0 k f (m • D + B) := by
      obtain ⟨e1⟩ := nonempty_iso_unit_of_subsingleton
        (MMP.CartierDivisor.sheaf ((m : ℤ) • D)) t
      obtain ⟨e2⟩ := nonempty_iso_unit_of_subsingleton
        (MMP.CartierDivisor.sheaf (m • D + B)) t
      rw [cartierH0_eq_finrank k f, cartierH0_eq_finrank k f,
        finrank_cohomologyOverField_eq_of_iso k f (e1 ≪≫ e2.symm) 0]
    have hP0 : P = MvPolynomial.C (P.coeff 0) :=
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (by omega)
    have hcm : (cartierH0 k f (m • D + B) : ℚ) = c := by
      rw [← hχ m, ← hc10, hP0]
      simp
    rw [h1, pow_zero, mul_one, show (cartierH0 k f (m • D + B) : ℝ) = c by exact_mod_cast hcm]
    linarith
  · obtain ⟨C1, -, hb1⟩ := cartierH0_add_le_add_pow f inferInstance hn hn1 B D
    obtain ⟨C2, hb2⟩ := abs_eval_sub_le P hdeg
    obtain ⟨N, hN⟩ := exists_half_mul_pow_lt (a := fun m => (cartierH0 k f (m • D + B) : ℝ))
      (b := fun m => (cartierH0 k f (m • D) : ℝ)) hcpos hn1 hb1 fun m hm => by
        simpa [hc10, hχ] using hb2 m hm
    refine ⟨N, fun m hm => ?_⟩
    lift m to ℕ using (by omega)
    rw [natCast_zsmul, Int.cast_natCast]
    exact hN m (by omega)

open MMP.Mori in
/-- Nefness pulls back along a morphism of `k`-schemes. -/
private theorem isNef_pullback {k : Type} [Field k] {X Y : Scheme.{0}} (f : X ⟶ Spec (.of k))
    [IsSeparated f] [LocallyOfFiniteType f] (g : Y ⟶ X) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (hL : IsNef k f L) :
    haveI := SheafOfModules.isInvertible_pullback g L
    IsNef k (g ≫ f) ((Scheme.Modules.pullback g).obj L) := by
  intro C i _ _ _ hC
  haveI : IsProper ((i ≫ g) ≫ f) := by rw [Category.assoc]; infer_instance
  rw [degreeOn_pullback_eq_degreeOn_comp (g ≫ f) f g i rfl hC.le L]
  haveI : UniversallyClosed ((i ≫ g) ≫ f) := IsProper.toUniversallyClosed
  haveI : QuasiCompact ((i ≫ g) ≫ f) :=
    ⟨fun _ _ => (Scheme.Hom.isProperMap ((i ≫ g) ≫ f)).isCompact_preimage⟩
  haveI : AlgebraicGeometry.IsCurve k ((i ≫ g) ≫ f) :=
    (MMP.Mori.isCurve_iff k _).2 ⟨(MMP.Mori.isVariety_iff k _).2
      ⟨inferInstance, inferInstance, IsProper.toLocallyOfFiniteType, inferInstance⟩, hC⟩
  by_cases hpt : ∃ x : X, Set.range (i ≫ g) = {x}
  · exact (degreeOn_eq_zero_of_range_eq_singleton f (i ≫ g) L hpt).ge
  · rw [degreeOn_eq_degreeOver_mul f (i ≫ g) L hpt]
    haveI : IsProper (i ≫ g) := IsProper.of_comp (i ≫ g) f
    haveI : IsProper ((i ≫ g).imageι ≫ f) := isProper_imageι_comp (i ≫ g) f
    have hcurve := isCurve_imageι_comp f (i ≫ g) hpt
    haveI : IsIntegral (i ≫ g).image := hcurve.toIsVariety.toIsIntegral
    exact mul_nonneg (by positivity)
      (hL _ (i ≫ g).imageι (IsCurve.topologicalKrullDim_eq_one (f := (i ≫ g).imageι ≫ f)))

end MMP.FourfoldProofs.Km2cBigOfNefTopPositiveComplexProof

end

section

public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

open MMP.FourfoldProofs MMP.FourfoldProofs.Km2cBigOfNefTopPositiveComplexProof in
/-- **Nef with positive top self-intersection implies big** (Kollár–Mori 2.61 (2) ⇒ (1)). On a
projective variety `X` of dimension `n` over an algebraically closed field `k` of characteristic
zero, a Cartier divisor `D` whose invertible sheaf `𝒪_X(D)` is nef and with `(Dⁿ) > 0` is big. -/
@[mmp "lem_km2c_big_of_nef_top_positive_complex"]
public theorem isBigCartier_of_isNef_of_sheafSelfIntersectionNumber_pos {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} (f : X ⟶ Spec (.of k))
    [IsProjectiveVariety k f] {n : ℕ} (hn : topologicalKrullDim X = n) (D : X.CartierDivisor)
    (hnef : IsNef k f (MMP.CartierDivisor.sheaf D))
    (hpos : 0 < sheafSelfIntersectionNumber k f (𝟙 X) n hn.le (MMP.CartierDivisor.sheaf D)) :
    IsBigCartier k f D := by
  have hXv : AlgebraicGeometry.IsVariety k f := inferInstance
  haveI : IsIntegral X := hXv.toIsIntegral
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hfproj : IsProjective f :=
    IsProjectiveMorphism.isProjective (IsProjectiveVariety.isProjective (k := k))
  haveI : IsProper f := hfproj.isProper
  obtain ⟨Y, g, hYv, hgproj, hbir, hsm, -⟩ :=
    MMP.Resolution.exists_isResolutionOfVariety_isEffectiveCartierDivisor_comap f hXv ⊤
      (fun h => by
        have h' := congrArg Scheme.IdealSheafData.support h
        rw [Scheme.IdealSheafData.support_top, Scheme.IdealSheafData.support_bot] at h'
        exact (Set.univ_nonempty (α := X)).ne_empty (congrArg SetLike.coe h').symm)
  haveI := hYv
  haveI : IsIntegral Y := hYv.toIsIntegral
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (g ≫ f)
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  haveI : QuasiSeparatedSpace X := inferInstance
  have hYproj : IsProjective (g ≫ f) := IsProjective.comp hgproj hfproj
  haveI : MMP.Mori.IsProjectiveVariety k (g ≫ f) :=
    (MMP.Mori.isProjectiveVariety_iff k _).2
      ⟨hYv, isProjectiveMorphism_of_isProjective_of_isAffine _ hYproj⟩
  haveI : IsProper (g ≫ f) := hYproj.isProper
  haveI : IsDominant g := hbir.isDominant
  obtain ⟨D', hD'⟩ := exists_isPullback_of_isDominant g D
  obtain ⟨e⟩ := MMP.ProgramBaseChange.nonempty_pullback_sheaf_iso g hD'
  have hdim : topologicalKrullDim X = topologicalKrullDim Y :=
    MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism f (g ≫ f) hbir
  have hn' : topologicalKrullDim Y = n := hdim ▸ hn
  have hnef' : IsNef k (g ≫ f) (MMP.CartierDivisor.sheaf D') := by
    intro C i _ _ _ hC
    haveI := SheafOfModules.isInvertible_pullback g (MMP.CartierDivisor.sheaf D)
    rw [← degreeOn_eq_of_iso k (g ≫ f) i hC.le e]
    exact isNef_pullback f g _ hnef C i hC
  have hpos' : 0 < sheafSelfIntersectionNumber k (g ≫ f) (𝟙 Y) n hn'.le
      (MMP.CartierDivisor.sheaf D') := by
    haveI := SheafOfModules.isInvertible_pullback g (MMP.CartierDivisor.sheaf D)
    have h := sheafIntersectionNumber_pullback_eq_of_isBirationalMorphism k f (g ≫ f) g rfl
      (𝟙 X) (𝟙 Y) g (by simp) hbir n hn hn' (fun _ => MMP.CartierDivisor.sheaf D)
    have key := sheafIntersectionNumber_comp_eq_of_iso k (g ≫ f) (𝟙 Y) (𝟙 Y) n hn'.le
      (fun _ => (Scheme.Modules.pullback g).obj (MMP.CartierDivisor.sheaf D))
      (fun _ => MMP.CartierDivisor.sheaf D')
      (fun _ => (Scheme.Modules.pullbackId Y).app _ ≪≫ e)
    rw [sheafIntersectionNumber_congr_closedImmersion k (Category.id_comp (𝟙 Y)),
      sheafIntersectionNumber_congr_structure k (Category.id_comp (g ≫ f))] at key
    unfold sheafSelfIntersectionNumber at hpos ⊢
    rw [← key, ← h]
    exact hpos
  exact (isBigCartier_iff_of_isPullback ((MMP.Mori.isProperVariety_iff k f).2 ⟨hXv, inferInstance⟩)
    ((MMP.Mori.isProperVariety_iff k _).2 ⟨hYv, inferInstance⟩) g rfl hbir hD').2
    (isBigCartier_of_isSmoothScheme (g ≫ f) hsm hn' D' hnef' hpos')

end MMP.Mori

end

end
