/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.AlgebraicGeometry.Singularities.Semismooth.Defs
public import MMP.AlgebraicGeometry.Singularities.Semismooth.Normalization
public import MMP.AlgebraicGeometry.Normalization.Completion
public import MMP.AlgebraicGeometry.Resolution.Basic
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AmpleSmoothIrreducible
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.FibreRegularity
public import StacksFrontier.AlgebraicGeometry.NormalProperModel.Basic
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.RegularLocalRing.Criteria
public import StacksFrontier.RingTheory.RegularLocalRing.UniqueFactorization
public import StacksFrontier.RingTheory.NodalChart.Regularity
public import StacksFrontier.RingTheory.RegularLocalRing.Colimit
public import StacksFrontier.RingTheory.CompleteLocalRing.Regular
public import StacksFrontier.RingTheory.RegularRing.GlobalDimension
public import StacksFrontier.RingTheory.AdicCompletion.QuotientCompletionMap
public import StacksFrontier.RingTheory.GRing.Henselization
public import StacksFrontier.RingTheory.GRing.EssFiniteType
public import StacksFrontier.RingTheory.Regular.AscentAlongRegularRingHom
public import StacksFrontier.RingTheory.RegularLocalRing.FlatLocalHom
public import StacksFrontier.AlgebraicGeometry.Morphisms.SingularLocus.JTwoStandardClasses
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.RegularStalk
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.StalkSpecialization
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.PreimageDimension
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NodalResolution
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.StandardNodalModelRegularLocus

/-!
# The singular locus of a semismooth `n`-fold

Let `X` be a semismooth `n`-fold over a field `k` (FA 12.2.1), `n ≥ 1`: every closed point of `X`
is smooth, a double normal crossing point (`𝒪̂_{X,x} ≅ k[[x₀, …, xₙ]] ⧸ (x₀x₁)`) or a pinch point
(`𝒪̂_{X,x} ≅ k[[x₀, …, xₙ]] ⧸ (x₀² - x₁x₂²)`). We prove that the singular locus `D_X`, with its
reduced structure, is smooth over `k` and of pure dimension `n - 1`.

The argument runs through regularity rather than through differentials. On `X` the smooth locus
is the regular locus: regular points form an open set (`X` is J-2, being of finite type over a
field), so a regular non-smooth point would specialize to a closed one, and closed points with
one of the two models are not regular. Let `z` be a closed point of `D_X` over `x ∈ X`, and let
`I` be the kernel of `𝒪_{X,x} → 𝒪_{D,z}`. A prime `p` of `𝒪_{X,x}` contains `I` exactly when the
corresponding point lies on `D_X`, that is, when `(𝒪_{X,x})_p` is not regular. As `𝒪_{X,x}` is a
G-ring, the map to its completion is regular, so a prime `Q` of `𝒪̂_{X,x}` has regular local ring
exactly when its contraction does. In the model `k[[x]] ⧸ (h)` the non-regular primes are those
containing `(x₀, x₁)`, respectively `(x₀, x₂)`: there `h` lies in the square of the prime, and
elsewhere a partial derivative of `h` is a unit. Since the completion of the reduced G-ring
`𝒪_{X,x} ⧸ I` is reduced, `I 𝒪̂_{X,x}` is radical, hence equal to that prime, and the completion
of `𝒪_{D,z}` is `k[[x]] ⧸ (x₀, x₁)`, respectively `k[[x]] ⧸ (x₀, x₂)`: a regular local ring of
dimension `n - 1` with residue field `k`. Smoothness of `D_X` follows at closed points, hence
everywhere, and the dimension of an irreducible component is read at a closed point lying on no
other component.

## Main results

* `MMP.Flips.IsDoubleNormalCrossingPoint.not_isRegularLocalRing`,
  `MMP.Flips.IsDoubleNormalCrossingPoint.notMem_smoothLocus`: a double normal crossing point is
  neither regular nor smooth.
* `MMP.Flips.mem_smoothLocus_iff_isRegularLocalRing`: if every closed point of `X` is smooth,
  a double normal crossing point or a pinch point, the smooth locus of `X` is its regular locus.
* `MMP.Flips.IsSemismooth.singularLocus_smooth`: FA 12.2.1(2), the singular locus of a
  semismooth `n`-fold is a smooth `(n - 1)`-fold.

## Implementation notes

The source identifies the completion of `𝒪_{D,z}` through the Jacobian criterion and the Fitting
ideal of the differentials. The proof here identifies the same ideal through the regular locus
of the model instead, which needs no comparison of differentials with their completion, and
works over an arbitrary field `k`, in every characteristic.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 12.2.1
-/

@[expose] public noncomputable section

universe u

namespace MMP.Flips.SingLoc

open IsLocalRing MvPowerSeries MMP.Flips.Normalization

/-! ### Power series rings -/

variable (k : Type u) [Field k] (m : ℕ)

private instance isRegularLocalRing_mvPowerSeries :
    IsRegularLocalRing (MvPowerSeries (Fin m) k) :=
  MvPowerSeries.isRegularLocalRing k m

private instance isRegularRing_mvPowerSeries : IsRegularRing (MvPowerSeries (Fin m) k) :=
  ((IsLocalRing.isRegularRing_tfae (R := MvPowerSeries (Fin m) k)).out 1 3).mp
    (isRegularLocalRing_mvPowerSeries k m)

private instance isDomain_mvPowerSeries : IsDomain (MvPowerSeries (Fin m) k) :=
  IsRegularLocalRing.isDomain _

variable {k m}

private theorem mem_maximalIdeal_mvPowerSeries_iff {f : MvPowerSeries (Fin m) k} :
    f ∈ maximalIdeal (MvPowerSeries (Fin m) k) ↔ constantCoeff f = 0 := by
  rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff,
    isUnit_iff_ne_zero, not_not]

/-- Elements of `𝔪²` have vanishing linear part, read through a partial derivative. -/
private theorem constantCoeff_pderiv_eq_zero_of_mem_sq (l : Fin m) {f : MvPowerSeries (Fin m) k}
    (hf : f ∈ maximalIdeal (MvPowerSeries (Fin m) k) ^ 2) :
    constantCoeff (pderiv l f) = 0 := by
  rw [pow_two] at hf
  refine Submodule.mul_induction_on hf (fun a ha b hb => ?_) (fun x y hx hy => ?_)
  · rw [mem_maximalIdeal_mvPowerSeries_iff] at ha hb
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, ha, hb]
    ring
  · rw [map_add, map_add, hx, hy, add_zero]

private theorem X_ne_zero' (i : Fin m) : (X i : MvPowerSeries (Fin m) k) ≠ 0 := by
  intro h
  simpa using congrArg (pderiv i) h

private theorem X_mem_maximalIdeal (i : Fin m) :
    (X i : MvPowerSeries (Fin m) k) ∈ maximalIdeal (MvPowerSeries (Fin m) k) :=
  mem_maximalIdeal_mvPowerSeries_iff.mpr (constantCoeff_X i)

private theorem X_notMem_sq (i : Fin m) :
    (X i : MvPowerSeries (Fin m) k) ∉ maximalIdeal (MvPowerSeries (Fin m) k) ^ 2 :=
  fun h => by simpa using constantCoeff_pderiv_eq_zero_of_mem_sq i h

/-- Cutting `k[[x]]` by one variable gives a regular local ring of one dimension less. -/
private theorem isRegularLocalRing_quotient_X (i : Fin m) :
    IsRegularLocalRing (MvPowerSeries (Fin m) k ⧸ Ideal.span {(X i : MvPowerSeries (Fin m) k)}) :=
  Stacks.RegularLocalRing.DirectedColimit.isRegularLocalRing_quotient_span_singleton
    (X_mem_maximalIdeal i) (X_notMem_sq i)

private theorem ringKrullDim_quotient_X (i : Fin m) :
    ringKrullDim (MvPowerSeries (Fin m) k ⧸ Ideal.span {(X i : MvPowerSeries (Fin m) k)}) + 1 =
      m := by
  rw [ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero (X_ne_zero' i)) (X_mem_maximalIdeal i),
    MvPowerSeries.ringKrullDim_eq]

private theorem mk_X_notMem_sq {i j : Fin m} (hij : i ≠ j) :
    letI := isRegularLocalRing_quotient_X (k := k) i
    Ideal.Quotient.mk (Ideal.span {X i}) (X j : MvPowerSeries (Fin m) k) ∉
      maximalIdeal (MvPowerSeries (Fin m) k ⧸ Ideal.span {X i}) ^ 2 := by
  let := isRegularLocalRing_quotient_X (k := k) i
  intro h
  rw [← IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective,
    ← Ideal.map_pow, ← Ideal.mem_comap,
    Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, Submodule.mem_sup] at h
  obtain ⟨a, ha, b, hb, hab⟩ := h
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hb
  have h1 := constantCoeff_pderiv_eq_zero_of_mem_sq j ha
  have h2 : constantCoeff (pderiv j (X j : MvPowerSeries (Fin m) k)) = 1 := by simp
  rw [← hab, map_add, Derivation.leibniz, pderiv_X_of_ne hij, smul_zero, zero_add, smul_eq_mul,
    map_add, h1, map_mul, constantCoeff_X, zero_mul, add_zero] at h2
  exact zero_ne_one h2

private theorem mk_X_mem_maximalIdeal (i j : Fin m) :
    letI := isRegularLocalRing_quotient_X (k := k) i
    Ideal.Quotient.mk (Ideal.span {X i}) (X j : MvPowerSeries (Fin m) k) ∈
      maximalIdeal (MvPowerSeries (Fin m) k ⧸ Ideal.span {X i}) := by
  let := isRegularLocalRing_quotient_X (k := k) i
  rw [← IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective]
  exact Ideal.mem_map_of_mem _ (X_mem_maximalIdeal j)

/-- `k[[x]] ⧸ (xᵢ, xⱼ)` is a regular local ring of dimension `m - 2`. -/
private theorem isRegularLocalRing_quotient_X_X {i j : Fin m} (hij : i ≠ j) :
    IsRegularLocalRing (MvPowerSeries (Fin m) k ⧸
        Ideal.span {(X i : MvPowerSeries (Fin m) k), X j}) ∧
      ringKrullDim (MvPowerSeries (Fin m) k ⧸
        Ideal.span {(X i : MvPowerSeries (Fin m) k), X j}) + 2 = m := by
  let := isRegularLocalRing_quotient_X (k := k) i
  have hsup : Ideal.span {X i} ⊔ Ideal.span {X j} =
      Ideal.span {(X i : MvPowerSeries (Fin m) k), X j} := by
    rw [← Ideal.span_union, Set.singleton_union]
  let e := (DoubleQuot.quotQuotEquivQuotSup (Ideal.span {(X i : MvPowerSeries (Fin m) k)})
    (Ideal.span {X j})).trans (Ideal.quotEquivOfEq hsup)
  have hmap : (Ideal.span {(X j : MvPowerSeries (Fin m) k)}).map
      (Ideal.Quotient.mk (Ideal.span {X i})) =
      Ideal.span {Ideal.Quotient.mk (Ideal.span {X i}) (X j)} := by
    rw [Ideal.map_span, Set.image_singleton]
  have hreg := Stacks.RegularLocalRing.DirectedColimit.isRegularLocalRing_quotient_span_singleton
    (mk_X_mem_maximalIdeal (k := k) i j) (mk_X_notMem_sq hij)
  rw [← hmap] at hreg
  refine ⟨IsRegularLocalRing.of_ringEquiv e, ?_⟩
  have hne : Ideal.Quotient.mk (Ideal.span {X i}) (X j : MvPowerSeries (Fin m) k) ≠ 0 :=
    fun h0 => mk_X_notMem_sq (k := k) hij (h0 ▸ zero_mem _)
  have : IsDomain (MvPowerSeries (Fin m) k ⧸ Ideal.span {(X i : MvPowerSeries (Fin m) k)}) :=
    IsRegularLocalRing.isDomain _
  have hdim := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hne) (mk_X_mem_maximalIdeal (k := k) i j)
  rw [← hmap, ringKrullDim_eq_of_ringEquiv e] at hdim
  rw [← ringKrullDim_quotient_X (k := k) i, ← hdim, add_assoc]
  rfl

/-! ### The regular locus of a hypersurface model -/

/-- The regular locus of `k[[x]] ⧸ (h)` is the complement of `V(xᵢ, xⱼ)`, as soon as `h ∈ p²` for
primes containing `xᵢ, xⱼ`, and some partial derivative of `h` avoids every other prime
containing `h`. -/
private theorem isRegularLocalRing_localization_iff {h : MvPowerSeries (Fin m) k} (h0 : h ≠ 0)
    {i j : Fin m}
    (hsq : ∀ p : Ideal (MvPowerSeries (Fin m) k), p.IsPrime → X i ∈ p → X j ∈ p → h ∈ p ^ 2)
    (hder : ∀ p : Ideal (MvPowerSeries (Fin m) k), p.IsPrime → h ∈ p → ¬ (X i ∈ p ∧ X j ∈ p) →
      ∃ l, pderiv l h ∉ p)
    (q : Ideal (MvPowerSeries (Fin m) k ⧸ Ideal.span {h})) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) ↔
      ¬ (Ideal.Quotient.mk _ (X i) ∈ q ∧ Ideal.Quotient.mk _ (X j) ∈ q) := by
  set p := q.comap (Ideal.Quotient.mk (Ideal.span {h}))
  have hp : p.IsPrime := Ideal.IsPrime.comap _
  have hhp : h ∈ p := by
    change Ideal.Quotient.mk (Ideal.span {h}) h ∈ q
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self h)]
    exact q.zero_mem
  constructor
  · rintro hreg ⟨hi, hj⟩
    exact Stacks.SemistableReduction.not_isRegularLocalRing_localization_quotient_of_mem_sq h0 p
      (hsq p hp hi hj) q rfl hreg
  · intro hn
    obtain ⟨l, hl⟩ := hder p hp hhp hn
    let : Algebra ℤ (MvPowerSeries (Fin m) k) := Ring.toIntAlgebra _
    exact Stacks.isRegularLocalRing_localization_quotient_span_singleton_of_notMem_sq h q
      (Stacks.notMem_sq_of_derivation
        { toFun := pderiv l
          map_add' := map_add _
          map_smul' := fun r a => map_zsmul (pderiv l) r a
          map_one_eq_zero' := (pderiv l).map_one_eq_zero
          leibniz' := (pderiv l).leibniz } hl)

namespace Pub

/-- The double normal crossing equation `x₀x₁`. -/
abbrev dncEq (k : Type u) [Field k] (m : ℕ) : MvPowerSeries (Fin (m + 1 + 1)) k := X 0 * X 1

/-- The pinch point equation `x₀² - x₁x₂²`. -/
abbrev pinchEq (k : Type u) [Field k] (m : ℕ) : MvPowerSeries (Fin (m + 1 + 1 + 1)) k :=
  X 0 ^ 2 - X 1 * X 2 ^ 2

/-- In `k[[x₀, …, x_{m+1}]]/(x₀x₁)`, the regular primes are those not containing both `x₀`
and `x₁`. -/
theorem isRegularLocalRing_localization_dnc_iff
    (q : Ideal (MvPowerSeries (Fin (m + 1 + 1)) k ⧸ Ideal.span {dncEq k m})) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) ↔
      ¬ (Ideal.Quotient.mk _ (X 0) ∈ q ∧ Ideal.Quotient.mk _ (X 1) ∈ q) := by
  refine isRegularLocalRing_localization_iff (mul_ne_zero (X_ne_zero' _) (X_ne_zero' _))
    (fun p _ h0 h1 => ?_) (fun p hp _ hn => ?_) q
  · simpa only [pow_two] using Ideal.mul_mem_mul h0 h1
  · by_cases h0 : (X 0 : MvPowerSeries (Fin (m + 1 + 1)) k) ∈ p
    · refine ⟨0, ?_⟩
      have h1 : (X 1 : MvPowerSeries (Fin (m + 1 + 1)) k) ∉ p := fun h1 => hn ⟨h0, h1⟩
      simpa [Derivation.leibniz] using h1
    · refine ⟨1, ?_⟩
      simpa [Derivation.leibniz] using h0

private theorem pderiv_one_pinchEq :
    pderiv 1 (pinchEq k m) = -(X 2 ^ 2) := by
  have h21 : (2 : Fin (m + 1 + 1 + 1)) ≠ 1 :=
    Fin.ne_of_val_ne (by simp only [Fin.val_two, Fin.val_one]; omega)
  have h01 : (0 : Fin (m + 1 + 1 + 1)) ≠ 1 := Fin.ne_of_val_ne (by simp)
  simp [pinchEq, Derivation.leibniz, Derivation.leibniz_pow, pderiv_X_of_ne h21,
    pderiv_X_of_ne h01]

private theorem pinchEq_ne_zero : pinchEq k m ≠ 0 := by
  intro h
  have := congrArg (pderiv 1) h
  rw [pderiv_one_pinchEq, map_zero, neg_eq_zero] at this
  exact X_ne_zero' (k := k) (2 : Fin (m + 1 + 1 + 1)) (pow_eq_zero_iff two_ne_zero |>.mp this)

/-- In `k[[x₀, …, x_{m+2}]]/(x₀² - x₁x₂²)`, the regular primes are those not containing
both `x₀` and `x₂`. -/
theorem isRegularLocalRing_localization_pinch_iff
    (q : Ideal (MvPowerSeries (Fin (m + 1 + 1 + 1)) k ⧸ Ideal.span {pinchEq k m})) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) ↔
      ¬ (Ideal.Quotient.mk _ (X 0) ∈ q ∧ Ideal.Quotient.mk _ (X 2) ∈ q) := by
  refine isRegularLocalRing_localization_iff pinchEq_ne_zero (fun p _ h0 h2 => ?_)
    (fun p hp hh hn => ?_) q
  · exact sub_mem (Ideal.pow_mem_pow h0 2) (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow h2 2))
  · refine ⟨1, ?_⟩
    have h2 : (X 2 : MvPowerSeries (Fin (m + 1 + 1 + 1)) k) ∉ p := by
      intro h2
      refine hn ⟨hp.mem_of_pow_mem 2 ?_, h2⟩
      have : (X 0 : MvPowerSeries (Fin (m + 1 + 1 + 1)) k) ^ 2 = pinchEq k m + X 1 * X 2 ^ 2 := by
        simp [pinchEq]
      rw [this]
      exact add_mem hh (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ h2 2 two_pos))
    rw [pderiv_one_pinchEq, neg_mem_iff]
    exact fun h => h2 (hp.mem_of_pow_mem 2 h)

end Pub

open Pub

/-- The quotient of the model by the ideal of the double locus. -/
private def quotientDoubleLocusEquiv {h : MvPowerSeries (Fin m) k} {i j : Fin m}
    (hh : h ∈ Ideal.span {(X i : MvPowerSeries (Fin m) k), X j}) :
    (MvPowerSeries (Fin m) k ⧸ Ideal.span {h}) ⧸
        (Ideal.span {(X i : MvPowerSeries (Fin m) k), X j}).map
          (Ideal.Quotient.mk (Ideal.span {h})) ≃+*
      MvPowerSeries (Fin m) k ⧸ Ideal.span {(X i : MvPowerSeries (Fin m) k), X j} :=
  (DoubleQuot.quotQuotEquivQuotSup _ _).trans (Ideal.quotEquivOfEq
    (sup_eq_right.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hh)))

private theorem map_span_pair_le_iff {h : MvPowerSeries (Fin m) k} {i j : Fin m}
    (q : Ideal (MvPowerSeries (Fin m) k ⧸ Ideal.span {h})) :
    (Ideal.span {(X i : MvPowerSeries (Fin m) k), X j}).map
        (Ideal.Quotient.mk (Ideal.span {h})) ≤ q ↔
      (Ideal.Quotient.mk _ (X i) ∈ q ∧ Ideal.Quotient.mk _ (X j) ∈ q) := by
  rw [Ideal.map_span, Ideal.span_le, Set.image_pair, Set.insert_subset_iff,
    Set.singleton_subset_iff]
  rfl

end MMP.Flips.SingLoc

/-! ### Regularity along the completion of a local G-ring -/

namespace MMP.Flips.SingLoc

open IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- Along the completion of a local G-ring, a prime upstairs has regular local ring exactly when
its contraction does. -/
theorem isRegularLocalRing_localization_adicCompletion_iff (hR : IsGRing R)
    (Q : Ideal (AdicCompletion (maximalIdeal R) R)) [Q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime Q) ↔
      IsRegularLocalRing (Localization.AtPrime
        (Q.comap (algebraMap R (AdicCompletion (maximalIdeal R) R)))) := by
  set f := algebraMap R (AdicCompletion (maximalIdeal R) R)
  set P := Q.comap f
  have : P.IsPrime := Ideal.IsPrime.comap _
  have hreg : IsRegularRingHom f := isRegularRingHom_algebraMap_adicCompletion hR _
  have : IsNoetherianRing (Localization.AtPrime P) :=
    IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  have : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance
  constructor
  · intro hQ
    let : Algebra (Localization.AtPrime P) (Localization.AtPrime Q) :=
      (Localization.localRingHom P Q f rfl).toAlgebra
    have : Module.Flat (Localization.AtPrime P) (Localization.AtPrime Q) :=
      RingHom.Flat.localRingHom hreg.1 Q P rfl
    have : IsLocalHom (algebraMap (Localization.AtPrime P) (Localization.AtPrime Q)) :=
      Localization.isLocalHom_localRingHom P Q f rfl
    exact IsRegularLocalRing.of_flat_of_isLocalHom (Localization.AtPrime Q)
  · intro hP
    have hall := ((isRegularRingHom_tfae_localizations f).out 1 2).mp hreg
    have hloc : IsRegularRingHom (Localization.localRingHom P Q f rfl) := hall P Q rfl
    have : IsRegularRing (Localization.AtPrime P) :=
      ((IsLocalRing.isRegularRing_tfae (R := Localization.AtPrime P)).out 1 3).mp hP
    have : IsRegularRing (Localization.AtPrime Q) := isRegularRing_of_isRegularRingHom _ hloc
    exact IsRegularLocalRing.of_isRegularRing_of_isLocalRing _

/-- **The extended ideal of the non-regular locus.** Let `R` be a Noetherian local G-ring and
`I` an ideal cutting out the non-regular locus of `R`, with `R ⧸ I` reduced. If the non-regular
locus of the completion is `V(Q₀)` for a prime `Q₀`, then `I` extends to `Q₀`. -/
private theorem map_eq_of_regularLocus (hR : IsGRing R) (I : Ideal R) [IsLocalRing (R ⧸ I)]
    [IsReduced (R ⧸ I)]
    (hI : ∀ (p : Ideal R) [p.IsPrime], I ≤ p ↔ ¬ IsRegularLocalRing (Localization.AtPrime p))
    (Q₀ : Ideal (AdicCompletion (maximalIdeal R) R)) [Q₀.IsPrime]
    (hQ₀ : ∀ (Q : Ideal (AdicCompletion (maximalIdeal R) R)) [Q.IsPrime],
      IsRegularLocalRing (Localization.AtPrime Q) ↔ ¬ Q₀ ≤ Q) :
    I.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) = Q₀ := by
  set J := I.map (algebraMap R (AdicCompletion (maximalIdeal R) R))
  have hGI : IsGRing (R ⧸ I) := isGRing_of_essFiniteType hR
  have : IsReduced (AdicCompletion (maximalIdeal (R ⧸ I)) (R ⧸ I)) :=
    isReduced_of_isRegularRingHom _ (isRegularRingHom_algebraMap_adicCompletion hGI _)
  have hrad : J.IsRadical := by
    have := (RingHom.ker_isRadical_iff_reduced_of_surjective
      (adicCompletionMapQuotient_surjective I)).mpr inferInstance
    rwa [ker_adicCompletionMapQuotient] at this
  have hV : ∀ Q : Ideal (AdicCompletion (maximalIdeal R) R), Q.IsPrime → (J ≤ Q ↔ Q₀ ≤ Q) := by
    intro Q _
    rw [Ideal.map_le_iff_le_comap, hI, ← isRegularLocalRing_localization_adicCompletion_iff hR,
      hQ₀, not_not]
  rw [← hrad.radical, Ideal.radical_eq_sInf,
    ← (Ideal.IsPrime.isRadical (inferInstance : Q₀.IsPrime)).radical,
    Ideal.radical_eq_sInf]
  congr 1
  ext Q
  exact ⟨fun ⟨h1, h2⟩ => ⟨(hV Q h2).mp h1, h2⟩, fun ⟨h1, h2⟩ => ⟨(hV Q h2).mpr h1, h2⟩⟩

end MMP.Flips.SingLoc

/-! ### Scheme-theoretic part -/

namespace MMP.Flips.SingLoc

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing MMP.Mori

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

private theorem withBot_add_one_eq_natCast {d : WithBot ℕ∞} {m : ℕ}
    (h : d + 1 = ((m + 1 : ℕ) : WithBot ℕ∞)) : d = m := by
  induction d using WithBot.recBotCoe with
  | bot => exact absurd h (by rw [WithBot.bot_add]; exact WithBot.bot_ne_coe)
  | coe e =>
    have h' : e + 1 = ((m + 1 : ℕ) : ℕ∞) := by exact_mod_cast h
    induction e using ENat.recTopCoe with
    | top => exact absurd h' (by rw [top_add]; exact ENat.top_ne_natCast _)
    | coe a =>
      have : a + 1 = m + 1 := by exact_mod_cast h'
      exact_mod_cast (by omega : a = m)

private theorem withBot_add_two_eq_natCast {d : WithBot ℕ∞} {m : ℕ}
    (h : d + 2 = ((m + 1 + 1 : ℕ) : WithBot ℕ∞)) : d = m := by
  refine withBot_add_one_eq_natCast (withBot_add_one_eq_natCast ?_)
  rw [add_assoc, ← h]
  norm_num

private theorem isExcellent_stalk' [LocallyOfFiniteType sX] (x : X) :
    IsExcellent (X.presheaf.stalk x) :=
  AlgebraicGeometry.isExcellent_stalk_of_locallyOfFiniteType_of_isExcellent k
    ((isExcellent_of_standard_classes_and_finiteType.{u, u}).1 k) sX x

/-- A closed point with a hypersurface model `k[[x]] ⧸ (h)`, `0 ≠ h ∈ 𝔪²`, is not regular. -/
theorem not_isRegularLocalRing_stalk_of_model [LocallyOfFiniteType sX] {w : X} {m : ℕ}
    {h : MvPowerSeries (Fin m) k} (h0 : h ≠ 0)
    (h2 : h ∈ maximalIdeal (MvPowerSeries (Fin m) k) ^ 2)
    (hmod : HasCompletedLocalModel sX w h) : ¬ IsRegularLocalRing (X.presheaf.stalk w) := by
  intro hreg
  have : IsNoetherianRing (X.presheaf.stalk w) := (isExcellent_stalk' (sX := sX) w).1.1
  let := (stalkStructureMap sX w).toAlgebra
  obtain ⟨e⟩ := hmod
  have := isRegularLocalRing_iff_adicCompletion_maximalIdeal.mp hreg
  exact Stacks.not_isRegularLocalRing_quotient_span_singleton_of_mem_sq
    (mem_nonZeroDivisors_of_ne_zero h0) h2 (IsRegularLocalRing.of_ringEquiv e.toRingEquiv)

/-- The local ring of a scheme at a point smooth over a field is regular. -/
private theorem isRegularLocalRing_stalk_of_mem_smoothLocus {y : X} (hy : y ∈ smoothLocus sX) :
    IsRegularLocalRing (X.presheaf.stalk y) := by
  obtain ⟨U, hyU, hU⟩ := mem_smoothLocus_iff.mp hy
  have : Smooth (U.ι ≫ sX) := hU
  have := isRegularLocalRing_stalk_of_smooth_over_field (U.ι ≫ sX) ⟨y, hyU⟩
  exact IsRegularLocalRing.of_ringEquiv (U.stalkIso ⟨y, hyU⟩).commRingCatIsoToRingEquiv

/-- The local ring at a double normal crossing point, `𝒪̂_{X,x} ≅ k[[x₀, …, xₙ]] ⧸ (x₀x₁)`, is not
regular. -/
theorem _root_.MMP.Flips.IsDoubleNormalCrossingPoint.not_isRegularLocalRing
    [LocallyOfFiniteType sX] {n : ℕ} {x : X} (h : IsDoubleNormalCrossingPoint sX n x) :
    ¬ IsRegularLocalRing (X.presheaf.stalk x) :=
  not_isRegularLocalRing_stalk_of_model (mul_ne_zero (X_ne_zero' _) (X_ne_zero' _))
    (by rw [pow_two]; exact Ideal.mul_mem_mul (X_mem_maximalIdeal _) (X_mem_maximalIdeal _)) h.2.2

/-- A double normal crossing point is not a smooth point. -/
theorem _root_.MMP.Flips.IsDoubleNormalCrossingPoint.notMem_smoothLocus
    [LocallyOfFiniteType sX] {n : ℕ} {x : X} (h : IsDoubleNormalCrossingPoint sX n x) :
    x ∉ smoothLocus sX :=
  fun hx => h.not_isRegularLocalRing (isRegularLocalRing_stalk_of_mem_smoothLocus hx)

/-- **On a semismooth scheme the smooth locus is the regular locus.** Let `X` be locally of
finite type over a field `k`, with every closed point smooth, a double normal crossing point or
a pinch point. Then a point of `X` is smooth over `k` exactly when its local ring is regular. -/
theorem _root_.MMP.Flips.mem_smoothLocus_iff_isRegularLocalRing {n : ℕ} [LocallyOfFiniteType sX]
    (hpts : ∀ x : X, IsClosed ({x} : Set X) →
      x ∈ smoothLocus sX ∨ IsDoubleNormalCrossingPoint sX n x ∨ IsPinchPoint sX n x)
    (y : X) : y ∈ smoothLocus sX ↔ IsRegularLocalRing (X.presheaf.stalk y) := by
  refine ⟨isRegularLocalRing_stalk_of_mem_smoothLocus, fun hy => ?_⟩
  by_contra hns
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have hopen : IsOpen (regularLocus X) :=
    (Scheme.isJ2_of_locallyOfFiniteType_over_field k sX).isOpen_regularLocus (𝟙 X)
  have hlc : IsLocallyClosed (regularLocus X ∩ (smoothLocus sX : Set X)ᶜ) :=
    hopen.isLocallyClosed.inter (smoothLocus sX).isOpen.isClosed_compl.isLocallyClosed
  obtain ⟨w, ⟨hwreg, hwns⟩, hwc⟩ := nonempty_inter_closedPoints
    (Z := regularLocus X ∩ (smoothLocus sX : Set X)ᶜ) ⟨y, hy, hns⟩ hlc
  rcases hpts w hwc with hs | hd | hp
  · exact hwns hs
  · exact hd.not_isRegularLocalRing hwreg
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by have := hp.1; omega⟩
    exact not_isRegularLocalRing_stalk_of_model Pub.pinchEq_ne_zero
      (sub_mem (Ideal.pow_mem_pow (X_mem_maximalIdeal _) 2)
        (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow (X_mem_maximalIdeal _) 2))) hp.2.2.2 hwreg

/-- Regularity of the localization at a prime is invariant under a ring isomorphism. -/
theorem isRegularLocalRing_localization_comap_iff {S T : Type*} [CommRing S] [CommRing T]
    (e : S ≃+* T) (q : Ideal T) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime (q.comap e)) ↔
      IsRegularLocalRing (Localization.AtPrime q) := by
  let f := IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime (q.comap e))
    (Localization.AtPrime q) e (e.map_primeCompl_comap_eq q)
  exact ⟨fun _ => IsRegularLocalRing.of_ringEquiv f,
    fun _ => IsRegularLocalRing.of_ringEquiv f.symm⟩

private theorem not_isUnit_mk_of_constantCoeff {m : ℕ} {h g : MvPowerSeries (Fin m) k}
    (hh : MvPowerSeries.constantCoeff h = 0) (hg : MvPowerSeries.constantCoeff g = 0) :
    ¬ IsUnit (Ideal.Quotient.mk (Ideal.span {h}) g) := by
  rintro ⟨u, hu⟩
  obtain ⟨v, hv⟩ := Ideal.Quotient.mk_surjective (↑u⁻¹ : MvPowerSeries (Fin m) k ⧸ Ideal.span {h})
  have h1 : Ideal.Quotient.mk (Ideal.span {h}) (g * v) = Ideal.Quotient.mk _ 1 := by
    rw [map_mul, hv, ← hu, Units.mul_inv, map_one]
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp h1)
  have := congrArg MvPowerSeries.constantCoeff hw
  simp [hh, hg] at this

/-- At the image `y` of a prime `p` of `𝒪_{X,x}` under `Spec 𝒪_{X,x} → X`, the local ring `𝒪_{X,y}`
is regular exactly when the localization of `𝒪_{X,x}` at `p` is. -/
private theorem isRegularLocalRing_stalk_iff_localization {x y : X} (hyx : y ⤳ x)
    (p : Ideal (X.presheaf.stalk x)) [p.IsPrime]
    (hy : X.fromSpecStalk x (⟨p, inferInstance⟩ : PrimeSpectrum _) = y) :
    IsRegularLocalRing (X.presheaf.stalk y) ↔ IsRegularLocalRing (Localization.AtPrime p) := by
  let : Algebra (X.presheaf.stalk x) (X.presheaf.stalk y) :=
    (X.presheaf.stalkSpecializes hyx).hom.toAlgebra
  have hloc := Stacks.StalkSpecialization.isLocalization_atPrime_stalkSpecializes hyx
  have hp' : (maximalIdeal (X.presheaf.stalk y)).under (X.presheaf.stalk x) = p := by
    have h1 := Scheme.SpecMap_stalkSpecializes_fromSpecStalk hyx
    have h2 := congrArg (fun g => g (closedPoint (X.presheaf.stalk y))) h1
    simp only [Scheme.fromSpecStalk_closedPoint] at h2
    exact congrArg PrimeSpectrum.asIdeal
      ((X.fromSpecStalk x).isEmbedding.injective (h2.trans hy.symm))
  have := Stacks.StalkSpecialization.isLocalization_atPrime_of_eq hp' hloc
  let f := IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) (X.presheaf.stalk y)
  exact ⟨fun _ => IsRegularLocalRing.of_ringEquiv f.symm.toRingEquiv,
    fun _ => IsRegularLocalRing.of_ringEquiv f.toRingEquiv⟩

/-- A prime `p` of `𝒪_{X,x}`, for `x = ι z`, contains the kernel of `𝒪_{X,x} → 𝒪_{D,z}` exactly
when its image in `X` lies on `D`. -/
private theorem ker_stalkMap_subschemeι_le_iff (D : X.IdealSheafData) (z : D.subscheme) {y : X}
    (hyx : y ⤳ D.subschemeι z) (p : Ideal (X.presheaf.stalk (D.subschemeι z))) [p.IsPrime]
    (hy : X.fromSpecStalk (D.subschemeι z) (⟨p, inferInstance⟩ : PrimeSpectrum _) = y) :
    RingHom.ker (D.subschemeι.stalkMap z).hom ≤ p ↔ y ∈ Set.range D.subschemeι := by
  have hFinj : Function.Injective (X.fromSpecStalk (D.subschemeι z)) :=
    (X.fromSpecStalk (D.subschemeι z)).isEmbedding.injective
  have hsq := Scheme.SpecMap_stalkMap_fromSpecStalk (f := D.subschemeι) (x := z)
  constructor
  · intro hIp
    obtain ⟨P', hP'⟩ : (⟨p, inferInstance⟩ : PrimeSpectrum _) ∈
        Set.range (PrimeSpectrum.comap (D.subschemeι.stalkMap z).hom) := by
      rw [range_comap_of_surjective _ _ (D.subschemeι.stalkMap_surjective z)]
      exact hIp
    refine ⟨D.subscheme.fromSpecStalk z P', ?_⟩
    rw [← hy, ← hP']
    exact (congrArg (fun g => g P') hsq).symm
  · rintro ⟨w, hw⟩
    have hwz : w ⤳ z := D.subschemeι.isEmbedding.isInducing.specializes_iff.mp (hw ▸ hyx)
    obtain ⟨P', rfl⟩ : w ∈ Set.range (D.subscheme.fromSpecStalk z) := by
      rw [Scheme.range_fromSpecStalk]
      exact hwz
    have h2 := congrArg (fun g => g P') hsq
    have hp : p = (P' : PrimeSpectrum _).asIdeal.comap (D.subschemeι.stalkMap z).hom :=
      (congrArg PrimeSpectrum.asIdeal (hFinj ((h2.trans hw).trans hy.symm))).symm
    rw [hp]
    intro r hr
    rw [Ideal.mem_comap, RingHom.mem_ker.mp hr]
    exact zero_mem _

/-- **The non-regular locus of the local ring at a point of the singular locus.** For `x = ι z`,
a prime `p` of `𝒪_{X,x}` contains the kernel of `𝒪_{X,x} → 𝒪_{D,z}` exactly when the local ring
at `p` is not regular. -/
private theorem ker_le_iff_not_isRegularLocalRing
    (hsing : ∀ y : X, y ∈ smoothLocus sX ↔ IsRegularLocalRing (X.presheaf.stalk y))
    (D : X.IdealSheafData) (hD : ∀ y : X, y ∈ (D.support : Set X) ↔ y ∉ smoothLocus sX)
    (z : D.subscheme) (p : Ideal (X.presheaf.stalk (D.subschemeι z))) [p.IsPrime] :
    RingHom.ker (D.subschemeι.stalkMap z).hom ≤ p ↔
      ¬ IsRegularLocalRing (Localization.AtPrime p) := by
  have hyx : X.fromSpecStalk (D.subschemeι z) (⟨p, inferInstance⟩ : PrimeSpectrum _) ⤳
      D.subschemeι z := by
    have : X.fromSpecStalk (D.subschemeι z) (⟨p, inferInstance⟩ : PrimeSpectrum _) ∈
        Set.range (X.fromSpecStalk (D.subschemeι z)) := ⟨_, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  generalize hy : X.fromSpecStalk (D.subschemeι z) (⟨p, inferInstance⟩ : PrimeSpectrum _) = y
    at hyx
  rw [ker_stalkMap_subschemeι_le_iff D z hyx p hy,
    ← isRegularLocalRing_stalk_iff_localization hyx p hy, ← hsing, D.range_subschemeι, hD]

/-- At a point with a model `k[[x]] ⧸ (h)`, `h ∈ 𝔪`, every element of the local ring is congruent
to a constant modulo the maximal ideal. -/
private theorem exists_sub_stalkStructureMap_mem_maximalIdeal {x : X} {m : ℕ}
    {h : MvPowerSeries (Fin m) k} (hh : MvPowerSeries.constantCoeff h = 0)
    (hmod : HasCompletedLocalModel sX x h) (r : X.presheaf.stalk x) :
    ∃ c : k, r - stalkStructureMap sX x c ∈ maximalIdeal (X.presheaf.stalk x) := by
  let := (stalkStructureMap sX x).toAlgebra
  obtain ⟨e⟩ := hmod
  let R := X.presheaf.stalk x
  obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective
    (e (algebraMap R (AdicCompletion (maximalIdeal R) R) r))
  refine ⟨MvPowerSeries.constantCoeff f, ?_⟩
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have hu2 := (hu.map (algebraMap R (AdicCompletion (maximalIdeal R) R))).map e
  have hval : e (algebraMap R (AdicCompletion (maximalIdeal R) R)
      (r - stalkStructureMap sX x (MvPowerSeries.constantCoeff f))) =
      Ideal.Quotient.mk _ (f - MvPowerSeries.C (MvPowerSeries.constantCoeff f)) := by
    rw [map_sub, map_sub, ← hf, map_sub]
    congr 1
    exact (e.commutes _).trans rfl
  rw [hval] at hu2
  exact not_isUnit_mk_of_constantCoeff hh (by simp) hu2

/-- Let `R` be a Noetherian local G-ring with completion `k[[x]] ⧸ (h)`, where `h ∈ (xᵢ, xⱼ)` and
the non-regular locus of the model is `V(xᵢ, xⱼ)`, and let `I` cut out the non-regular locus of
`R`, with `R ⧸ I` reduced. Then `R ⧸ I` is regular of dimension `m - 2`. -/
private theorem isRegularLocalRing_quotient_of_completion_model {R : Type u} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (hR : IsGRing R) (I : Ideal R) [IsLocalRing (R ⧸ I)]
    [IsReduced (R ⧸ I)]
    (hI : ∀ (p : Ideal R) [p.IsPrime], I ≤ p ↔ ¬ IsRegularLocalRing (Localization.AtPrime p))
    {m : ℕ} {h : MvPowerSeries (Fin m) k} {i j : Fin m} (hij : i ≠ j)
    (hh : h ∈ Ideal.span {(MvPowerSeries.X i : MvPowerSeries (Fin m) k), MvPowerSeries.X j})
    (hreg : ∀ (q : Ideal (MvPowerSeries (Fin m) k ⧸ Ideal.span {h})) [q.IsPrime],
      IsRegularLocalRing (Localization.AtPrime q) ↔
        ¬ (Ideal.Quotient.mk _ (MvPowerSeries.X i) ∈ q ∧
          Ideal.Quotient.mk _ (MvPowerSeries.X j) ∈ q))
    (e : AdicCompletion (maximalIdeal R) R ≃+* MvPowerSeries (Fin m) k ⧸ Ideal.span {h}) :
    IsRegularLocalRing (R ⧸ I) ∧ ringKrullDim (R ⧸ I) + 2 = m := by
  set Q₀' : Ideal (MvPowerSeries (Fin m) k ⧸ Ideal.span {h}) :=
    (Ideal.span {(MvPowerSeries.X i : MvPowerSeries (Fin m) k), MvPowerSeries.X j}).map
      (Ideal.Quotient.mk _)
  obtain ⟨hCreg, hCdim⟩ := isRegularLocalRing_quotient_X_X (k := k) hij
  have : IsDomain (MvPowerSeries (Fin m) k ⧸
      Ideal.span {(MvPowerSeries.X i : MvPowerSeries (Fin m) k), MvPowerSeries.X j}) :=
    IsRegularLocalRing.isDomain _
  have : IsDomain ((MvPowerSeries (Fin m) k ⧸ Ideal.span {h}) ⧸ Q₀') :=
    (quotientDoubleLocusEquiv hh).toMulEquiv.isDomain
  have : Q₀'.IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp this
  set Q₀ := Q₀'.comap e
  have hQ₀ : ∀ (Q : Ideal (AdicCompletion (maximalIdeal R) R)) [Q.IsPrime],
      IsRegularLocalRing (Localization.AtPrime Q) ↔ ¬ Q₀ ≤ Q := by
    intro Q _
    obtain ⟨q, hq, rfl⟩ : ∃ q : Ideal (MvPowerSeries (Fin m) k ⧸ Ideal.span {h}), q.IsPrime ∧
        q.comap e = Q :=
      ⟨Q.map e, Ideal.map_isPrime_of_equiv _, Ideal.comap_map_of_bijective _ e.bijective⟩
    rw [isRegularLocalRing_localization_comap_iff e q, hreg q,
      Ideal.comap_le_comap_iff_of_surjective _ e.surjective, map_span_pair_le_iff]
  have hJ := map_eq_of_regularLocus hR I hI Q₀ hQ₀
  let E : AdicCompletion (maximalIdeal (R ⧸ I)) (R ⧸ I) ≃+*
      MvPowerSeries (Fin m) k ⧸
        Ideal.span {(MvPowerSeries.X i : MvPowerSeries (Fin m) k), MvPowerSeries.X j} :=
    (RingHom.quotientKerEquivOfSurjective (adicCompletionMapQuotient_surjective I)).symm.trans
      ((Ideal.quotEquivOfEq ((ker_adicCompletionMapQuotient I).trans hJ)).trans
        ((Ideal.quotientEquiv Q₀ Q₀' e
          (Ideal.map_comap_of_surjective _ e.surjective Q₀').symm).trans
          (quotientDoubleLocusEquiv hh)))
  have : IsRegularLocalRing (AdicCompletion (maximalIdeal (R ⧸ I)) (R ⧸ I)) :=
    IsRegularLocalRing.of_ringEquiv E.symm
  refine ⟨isRegularLocalRing_iff_adicCompletion_maximalIdeal.mpr this, ?_⟩
  rw [_root_.ringKrullDim_adicCompletion_maximalIdeal, ringKrullDim_eq_of_ringEquiv E, hCdim]

/-- **The local ring of the singular locus over a model point.** Let `z` be a point of `D_X`
over a closed point `x` with `𝒪̂_{X,x} ≅ k[[x]] ⧸ (h)`, where `h ∈ (xᵢ, xⱼ)` and the
non-regular locus of the model is `V(xᵢ, xⱼ)`. Then `𝒪_{D,z}` is regular with residue field
`k`, of dimension `m - 2`. -/
private theorem stalk_props_of_model [LocallyOfFiniteType sX]
    (hsing : ∀ y : X, y ∈ smoothLocus sX ↔ IsRegularLocalRing (X.presheaf.stalk y))
    (D : X.IdealSheafData) (hD : ∀ y : X, y ∈ (D.support : Set X) ↔ y ∉ smoothLocus sX)
    [IsReduced D.subscheme] (z : D.subscheme)
    {m : ℕ} {h : MvPowerSeries (Fin m) k} {i j : Fin m} (hij : i ≠ j)
    (hh : h ∈ Ideal.span {(MvPowerSeries.X i : MvPowerSeries (Fin m) k), MvPowerSeries.X j})
    (hreg : ∀ (q : Ideal (MvPowerSeries (Fin m) k ⧸ Ideal.span {h})) [q.IsPrime],
      IsRegularLocalRing (Localization.AtPrime q) ↔
        ¬ (Ideal.Quotient.mk _ (MvPowerSeries.X i) ∈ q ∧
          Ideal.Quotient.mk _ (MvPowerSeries.X j) ∈ q))
    (hmod : HasCompletedLocalModel sX (D.subschemeι z) h) :
    IsRegularLocalRing (D.subscheme.presheaf.stalk z) ∧
      (∀ a : D.subscheme.presheaf.stalk z, ∃ c : k,
        a - stalkStructureMap (D.subschemeι ≫ sX) z c ∈
          maximalIdeal (D.subscheme.presheaf.stalk z)) ∧
      ringKrullDim (D.subscheme.presheaf.stalk z) + 2 = m := by
  let ι := D.subschemeι
  let R := X.presheaf.stalk (ι z)
  let A := D.subscheme.presheaf.stalk z
  have hexc := isExcellent_stalk' (sX := sX) (ι z)
  have : IsNoetherianRing R := hexc.1.1
  let φ : R →+* A := (ι.stalkMap z).hom
  have hφ : Function.Surjective φ := ι.stalkMap_surjective z
  let I := RingHom.ker φ
  let eA : R ⧸ I ≃+* A := RingHom.quotientKerEquivOfSurjective hφ
  have : Nontrivial (R ⧸ I) := eA.toEquiv.nontrivial
  have : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have : IsReduced (R ⧸ I) := isReduced_of_injective eA.toRingHom eA.injective
  have hh0 : MvPowerSeries.constantCoeff h = 0 := by
    have : Ideal.span {(MvPowerSeries.X i : MvPowerSeries (Fin m) k), MvPowerSeries.X j} ≤
        RingHom.ker (MvPowerSeries.constantCoeff (R := k) (σ := Fin m)) := by
      rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨MvPowerSeries.constantCoeff_X i, MvPowerSeries.constantCoeff_X j⟩
    exact this hh
  have hres := exists_sub_stalkStructureMap_mem_maximalIdeal hh0 hmod
  let := (stalkStructureMap sX (ι z)).toAlgebra
  obtain ⟨e⟩ := hmod
  obtain ⟨hregRI, hdim⟩ := isRegularLocalRing_quotient_of_completion_model hexc.1.2.1 I
    (fun p _ => ker_le_iff_not_isRegularLocalRing hsing D hD z p) hij hh hreg e.toRingEquiv
  refine ⟨IsRegularLocalRing.of_ringEquiv eA, fun a => ?_,
    by rwa [← ringKrullDim_eq_of_ringEquiv eA]⟩
  obtain ⟨r, rfl⟩ := hφ a
  obtain ⟨c, hR⟩ := hres r
  refine ⟨c, ?_⟩
  have hA : φ (r - stalkStructureMap sX (ι z) c) ∈ maximalIdeal A := by
    rw [mem_maximalIdeal, mem_nonunits_iff] at hR ⊢
    exact fun hu => hR (isUnit_of_map_unit φ _ hu)
  rwa [map_sub, show φ (stalkStructureMap sX (ι z) c) = stalkStructureMap (ι ≫ sX) z c from
    stalkMap_stalkStructureMap ι z _] at hA

/-- On a scheme whose closed points are smooth, double normal crossing or pinch points, the local
ring of the singular locus `D` at a closed point is regular of dimension `n - 1`, with residue
field `k`. -/
private theorem stalk_props_of_isClosed [LocallyOfFiniteType sX] {m : ℕ}
    (hpts : ∀ x : X, IsClosed ({x} : Set X) → x ∈ smoothLocus sX ∨
      IsDoubleNormalCrossingPoint sX (m + 1) x ∨ IsPinchPoint sX (m + 1) x)
    (D : X.IdealSheafData) (hD : ∀ y : X, y ∈ (D.support : Set X) ↔ y ∉ smoothLocus sX)
    [IsReduced D.subscheme] (z : D.subscheme) (hz : IsClosed ({z} : Set D.subscheme)) :
    IsRegularLocalRing (D.subscheme.presheaf.stalk z) ∧
      (∀ a : D.subscheme.presheaf.stalk z, ∃ c : k,
        a - stalkStructureMap (D.subschemeι ≫ sX) z c ∈
          maximalIdeal (D.subscheme.presheaf.stalk z)) ∧
      ringKrullDim (D.subscheme.presheaf.stalk z) = m := by
  have hsing := mem_smoothLocus_iff_isRegularLocalRing hpts
  have hx : IsClosed ({D.subschemeι z} : Set X) := by
    rw [← Set.image_singleton]
    exact D.subschemeι.isClosedEmbedding.isClosedMap _ hz
  rcases hpts _ hx with hs | hd | hp
  · exact absurd hs ((hD _).mp (D.range_subschemeι ▸ ⟨z, rfl⟩))
  · have hh : Pub.dncEq k m ∈ Ideal.span {(MvPowerSeries.X 0 :
        MvPowerSeries (Fin (m + 1 + 1)) k), MvPowerSeries.X 1} :=
      Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))
    obtain ⟨hr, hres, hdim⟩ := stalk_props_of_model hsing D hD z
      (Fin.ne_of_val_ne (by simp) : (0 : Fin (m + 1 + 1)) ≠ 1) hh
      (fun q _ => Pub.isRegularLocalRing_localization_dnc_iff q) hd.2.2
    exact ⟨hr, hres, withBot_add_two_eq_natCast hdim⟩
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by have := hp.1; omega⟩
    have h02 : (0 : Fin (m' + 1 + 1 + 1)) ≠ 2 :=
      Fin.ne_of_val_ne (by simp only [Fin.val_zero, Fin.val_two]; omega)
    have hh : Pub.pinchEq k m' ∈ Ideal.span {(MvPowerSeries.X 0 :
        MvPowerSeries (Fin (m' + 1 + 1 + 1)) k), MvPowerSeries.X 2} := by
      have h0 : (MvPowerSeries.X 0 : MvPowerSeries (Fin (m' + 1 + 1 + 1)) k) ∈
          Ideal.span {MvPowerSeries.X 0, MvPowerSeries.X 2} := Ideal.subset_span (by simp)
      have h2 : (MvPowerSeries.X 2 : MvPowerSeries (Fin (m' + 1 + 1 + 1)) k) ∈
          Ideal.span {MvPowerSeries.X 0, MvPowerSeries.X 2} := Ideal.subset_span (by simp)
      exact sub_mem (Ideal.pow_mem_of_mem _ h0 2 two_pos)
        (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ h2 2 two_pos))
    obtain ⟨hr, hres, hdim⟩ := stalk_props_of_model hsing D hD z h02 hh
      (fun q _ => Pub.isRegularLocalRing_localization_pinch_iff q) hp.2.2.2
    exact ⟨hr, hres, withBot_add_two_eq_natCast hdim⟩

end MMP.Flips.SingLoc

namespace MMP.Flips

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing MMP.Mori

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- **The singular locus of a semismooth `n`-fold is a smooth `(n - 1)`-fold** (FA 12.2.1(2)).
Let `X` be a semismooth `n`-fold, `n ≥ 1`. Then `D_X`, the singular locus of `X` with its reduced
structure, is smooth over `k` and of pure dimension `n - 1` (or empty): every irreducible
component of `D_X` has dimension `n - 1`. -/
@[mmp "lem_fa12a_semismooth_singular_locus_smooth"]
theorem IsSemismooth.singularLocus_smooth {n : ℕ} (h : IsSemismooth sX n) (hn : 1 ≤ n) :
    IsSmoothScheme ((MMP.Resolution.reducedSingularLocus sX).subschemeι ≫ sX) ∧
      ∀ Z ∈ irreducibleComponents (MMP.Resolution.reducedSingularLocus sX).subscheme,
        topologicalKrullDim Z = (n - 1 : ℕ) := by
  obtain ⟨⟨⟨-, hlft, hqc⟩, hred, -⟩, hpts⟩ := h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set D := MMP.Resolution.reducedSingularLocus sX
  have : LocallyOfFinitePresentation (D.subschemeι ≫ sX) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := D.subschemeι ≫ sX)).mpr
      inferInstance
  have : IsReduced D.subscheme := by
    change IsReduced (Scheme.IdealSheafData.vanishingIdeal _).subscheme
    infer_instance
  have hD : ∀ y : X, y ∈ (D.support : Set X) ↔ y ∉ smoothLocus sX := fun y => by
    rw [MMP.Resolution.support_reducedSingularLocus]
    rfl
  have hlocal := SingLoc.stalk_props_of_isClosed hpts D hD
  have : JacobsonSpace D.subscheme := LocallyOfFiniteType.jacobsonSpace (D.subschemeι ≫ sX)
  refine ⟨?_, ?_⟩
  · rw [IsSmoothScheme, eq_top_iff]
    intro z _
    by_contra hz
    have hZ : IsClosed ((smoothLocus (D.subschemeι ≫ sX) : Set D.subscheme)ᶜ) :=
      (smoothLocus (D.subschemeι ≫ sX)).isOpen.isClosed_compl
    obtain ⟨w, hw, hwc⟩ := nonempty_inter_closedPoints ⟨z, hz⟩ hZ.isLocallyClosed
    exact hw (mem_smoothLocus_of_isRegularLocalRing _ w (hlocal w hwc).1
      (hlocal w hwc).2.1)
  · intro Z hZ
    have : IsLocallyNoetherian D.subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian (D.subschemeι ≫ sX)
    have : CompactSpace D.subscheme :=
      QuasiCompact.compactSpace_of_compactSpace (D.subschemeι ≫ sX)
    have : IsNoetherian D.subscheme := {}
    obtain ⟨w, hwc, hwZ, huniq⟩ := exists_closed_point_mem_unique_irreducibleComponent k
      D.subscheme (D.subschemeι ≫ sX) Z hZ
    rw [topologicalKrullDim_eq_ringKrullDim_stalk_of_unique_irreducibleComponent k D.subscheme
      (D.subschemeι ≫ sX) Z hZ w hwZ hwc huniq, Nat.add_sub_cancel]
    exact (hlocal w hwc).2.2

end MMP.Flips
