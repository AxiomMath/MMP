module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.Surface.MultiplicitySequence
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupEmbedded
public import MMP.AlgebraicGeometry.Resolution.CurveOnSurface.MultiplePoint
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
import MMP.AlgebraicGeometry.Resolution.CurveOnSurface.MultiplicityIdealMembership
import MMP.AlgebraicGeometry.Resolution.CurveOnSurface.InfinitelyNearPointsFinite
import MMP.AlgebraicGeometry.Resolution.CurveOnSurface.ReducedGermNotFormalPower
import MMP.AlgebraicGeometry.Resolution.Surface.RegularSurfaceBlowup
import MMP.AlgebraicGeometry.Resolution.CurveOnSurface.WeakSequenceLengthBound
import MMP.AlgebraicGeometry.Intersection.CartierRestriction
import MMP.AlgebraicGeometry.Resolution.Surface.RegularLocus

/-!
# Embedded resolution of curves on smooth surfaces

Let `S` be a smooth surface over a perfect field `k` and `C ⊆ S` a curve. This file proves the
local method of Kollár for embedded resolution of `C` by blowing up closed points.

An infinite blow-up sequence of constant multiplicity `m ≥ 2` starting at a closed point `p₀` of
a reduced curve `C₀` makes a local equation of `C₀` an `m`-th power `y_∞ ^ m` in the completion
of `𝒪_{S,p₀}`, where `y_∞` is the limit of the partial sums `y - ∑_{k=1}^n a_k x^k` attached to
the sequence. Over a perfect field a reduced curve germ is not a formal `m`-th power, so no such
sequence exists. By Kőnig's lemma the tree of infinitely near singular points of `C₀` is then
finite, and every maximal weak embedded resolution sequence stops, with smooth final birational
transform.

Running weak embedded resolution twice, first on `C_red` and then on the reduced inverse image
`C_m ∪ E_m`, gives a composite of point blow-ups `π : S' → S` with `π⁻¹(C)_red` a simple normal
crossing divisor: blowing up points preserves simple normal crossings, so the transforms of `C_m`
and of `E_m` are each snc together with the exceptional curves of the second run, and at a point
where the final transform is regular only one of them passes. Every strong embedded resolution
sequence is dominated by such a `π`, so it is finite, and a maximal one stops.

## Main results

* `PointBlowupSequence.exists_mem_span_pow_adicCompletion_of_isConstantMultiplicity`: an
  infinite blow-up sequence of multiplicity `m` gives a formal `m`-th power (Corollary 1.71).
* `PointBlowupSequence.length_ne_top_of_isConstantMultiplicity`: on a smooth surface over a perfect
  field there is no infinite blow-up sequence of multiplicity `m ≥ 2` (Lemma 1.68).
* `PointBlowupSequence.weakEmbeddedResolutionStops_of_maximal`: weak embedded resolution, local
  method (Theorem 1.67).
* `exists_isCompositeOfPointBlowups_isSNCSubscheme`: existence of an snc model (1.48).
* `PointBlowupSequence.strongEmbeddedResolutionStops_of_maximal`: strong embedded resolution
  (Theorem 1.47).

## Implementation notes

A smooth surface is a smooth, quasi-compact morphism `S ⟶ Spec k` of relative dimension `2`; a
curve is an effective Cartier divisor `C : S.IdealSheafData`, reduced where the source asks for a
reduced curve. A blow-up sequence is a `MMP.Resolution.PointBlowupSequence`; it starts at `p₀`
when its first centre maps to `p₀` under `zeroIso`, and it is infinite when its length is `⊤`.
The `𝔪`-adic completion is `AdicCompletion (maximalIdeal R₀) R₀`, which carries no topology
instance, so convergence of the partial sums is stated in the `𝔪R̂₀`-adic filtration. A weak or
strong embedded resolution sequence `s` is *maximal* when no such sequence of greater length
extends it, i.e. has the same schemes `S_i` (`i ≤ n`), the same identification `S_0 ≅ S`, the
same centres `p_i` and the same isomorphisms `S_{i+1} ≅ B_{p_i}S_i` (`i < n`). The reduced
inverse image `π⁻¹(C)_red` is `Scheme.IdealSheafData.vanishingIdeal` on the support of
`C.comap π`, and smoothness of `C_n` is smoothness of `C_n ⟶ S_n ⟶ S ⟶ Spec k`.

## References

* [J. Kollár, *Lectures on resolution of singularities*][kollar2007], 1.47, 1.48, 1.67, 1.68,
  1.71
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing Filter

universe u

namespace MMP.Resolution

/-! ### Formal limits in the adic completion -/

/-- For ideals `A, B` and `m ≥ 1`, `(A ⊔ B) ^ m ≤ A ⊔ B ^ m`. -/
private theorem sup_pow_le_sup_pow {R : Type*} [CommRing R] (A B : Ideal R) :
    ∀ m : ℕ, 1 ≤ m → (A ⊔ B) ^ m ≤ A ⊔ B ^ m
  | 0, h => absurd h (by norm_num)
  | 1, _ => by simp
  | m + 2, _ => by
    rw [pow_succ]
    calc (A ⊔ B) ^ (m + 1) * (A ⊔ B) ≤ (A ⊔ B ^ (m + 1)) * (A ⊔ B) :=
          Ideal.mul_mono_left (sup_pow_le_sup_pow A B (m + 1) (by omega))
      _ ≤ A ⊔ B ^ (m + 2) := by
        rw [Ideal.mul_sup, Ideal.sup_mul, Ideal.sup_mul, pow_succ B (m + 1)]
        exact sup_le (sup_le (le_sup_of_le_left Ideal.mul_le_left)
          (le_sup_of_le_left Ideal.mul_le_right)) (sup_le
          (le_sup_of_le_left Ideal.mul_le_left) le_sup_right)

/-- The partial sums `y - ∑_{k=1}^n a k x^k` differ by multiples of `x^(n+1)`. -/
private theorem sub_mem_span_pow {R : Type*} [CommRing R] (x y : R) (a : ℕ → R)
    {n n' : ℕ} (h : n ≤ n') :
    (y - ∑ k ∈ Finset.Icc 1 n, a k * x ^ k) - (y - ∑ k ∈ Finset.Icc 1 n', a k * x ^ k) ∈
      Ideal.span {x ^ (n + 1)} := by
  rw [sub_sub_sub_cancel_left, ← Finset.sum_sdiff (Finset.Icc_subset_Icc le_rfl h),
    add_sub_cancel_right]
  refine Ideal.sum_mem _ fun k hk => Ideal.mem_span_singleton.2 ?_
  simp only [Finset.mem_sdiff, Finset.mem_Icc, not_and, not_le] at hk
  exact (pow_dvd_pow x (by have := hk.2 hk.1.1; omega)).mul_left _

/-- **Limits of adic Cauchy sequences.** If `I` is finitely generated and
`Y n ≡ Y (n + 1) mod I ^ n` for all `n`, then there is `z ∈ R̂_I` with
`z - Y n ∈ (I R̂_I) ^ n` for all `n`. -/
private theorem exists_sub_algebraMap_mem_map_pow {R : Type*} [CommRing R] {I : Ideal R}
    (hI : I.FG) (Y : ℕ → R) (hY : ∀ n, Y n - Y (n + 1) ∈ I ^ n) :
    ∃ z : AdicCompletion I R,
      ∀ n, z - algebraMap R _ (Y n) ∈ I.map (algebraMap R (AdicCompletion I R)) ^ n := by
  have hcauchy : ∀ n, Y n ≡ Y (n + 1) [SMOD (I ^ n • ⊤ : Submodule R R)] := fun n => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    exact hY n
  refine ⟨AdicCompletion.mk I R (AdicCompletion.AdicCauchySequence.mk I R Y hcauchy),
    fun n => ?_⟩
  rw [← Ideal.map_pow, ← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval hI, LinearMap.mem_ker, map_sub,
    AdicCompletion.algebraMap_apply, AdicCompletion.eval_of, AdicCompletion.coe_eval]
  simp

/-- **Krull's intersection theorem, for a quotient.** In a Noetherian local ring every ideal
`J` is closed: if `F ∈ 𝔪 ^ j + J` for every `j`, then `F ∈ J`. -/
private theorem mem_of_forall_mem_maximalIdeal_pow_sup {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] {J : Ideal R} {F : R}
    (h : ∀ j, F ∈ maximalIdeal R ^ j ⊔ J) : F ∈ J := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  refine (IsHausdorff.of_le_jacobson _ (R ⧸ J) (maximalIdeal_le_jacobson (R := R) ⊥)).haus _
    fun n => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (h n)
  rw [SModEq.zero, map_add, Ideal.Quotient.eq_zero_iff_mem.2 hb, add_zero, ← mul_one a,
    map_mul, ← Ideal.Quotient.algebraMap_eq, ← Algebra.smul_def]
  exact Submodule.smul_mem_smul ha trivial

/-- **The formal limit of the partial sums.** Let `R` be a Noetherian local ring, `x ∈ 𝔪`,
`a : ℕ → R` and `m ≥ 1`. If `f ∈ (x ^ (j + 1), y - ∑_{k=1}^j a k x ^ k) ^ m` for every `j`, then
the partial sums converge `𝔪`-adically to some `z` in the completion `R̂`, and `f ∈ z ^ m R̂`. -/
private theorem exists_tendsto_and_mem_span_pow {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {x : R} (y : R) (a : ℕ → R) (hx : x ∈ maximalIdeal R)
    {m : ℕ} (hm : 1 ≤ m) {f : R}
    (hmem : ∀ j : ℕ, f ∈ Ideal.span {x ^ (j + 1), y - ∑ i ∈ Finset.Icc 1 j, a i * x ^ i} ^ m) :
    ∃ z : AdicCompletion (maximalIdeal R) R,
      (∀ N : ℕ, ∀ᶠ n in atTop, z - algebraMap _ _ (y - ∑ k ∈ Finset.Icc 1 n, a k * x ^ k) ∈
        (maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal R) R)) ^ N) ∧
      algebraMap _ (AdicCompletion (maximalIdeal R) R) f ∈ Ideal.span {z ^ m} := by
  set Y : ℕ → R := fun n => y - ∑ k ∈ Finset.Icc 1 n, a k * x ^ k
  have hfg := (maximalIdeal R).fg_of_isNoetherianRing
  obtain ⟨z, hz⟩ := exists_sub_algebraMap_mem_map_pow hfg Y fun n =>
    Ideal.pow_le_pow_right n.le_succ <| (Ideal.span_singleton_le_iff_mem _).2
      (Ideal.pow_mem_pow hx (n + 1)) (sub_mem_span_pow x y a n.le_succ)
  refine ⟨z, fun N => eventually_atTop.2 ⟨N, fun n hn => Ideal.pow_le_pow_right hn (hz n)⟩, ?_⟩
  have := AdicCompletion.isNoetherianRing (maximalIdeal R) (R := R)
  have := AdicCompletion.isLocalRing_of_fg hfg
  refine mem_of_forall_mem_maximalIdeal_pow_sup fun j => ?_
  rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.span_singleton_pow]
  refine sup_pow_le_sup_pow _ _ m hm <| Ideal.pow_right_mono ?_ m <| by
    simpa only [Ideal.map_pow, Ideal.map_span, Set.image_pair, map_pow] using
      Ideal.mem_map_of_mem (algebraMap R (AdicCompletion (maximalIdeal R) R)) (hmem j)
  rw [Ideal.span_le]
  rintro _ (rfl | rfl)
  · exact Ideal.mem_sup_left <| Ideal.pow_le_pow_right j.le_succ <|
      Ideal.pow_mem_pow (Ideal.mem_map_of_mem _ hx) _
  · rw [← sub_sub_cancel z (algebraMap R _ (Y j))]
    exact Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self z))
      (Ideal.mem_sup_left (hz j))

namespace PointBlowupSequence

/-- **Kollár, Corollary 1.71 (⇒).** Let `S₀` be a two-dimensional regular Noetherian scheme,
`C₀ ⊆ S₀` a reduced effective Cartier divisor, `p₀ ∈ C₀` a point with
`multAt C₀ p₀ = m ≥ 2`, and `f` a generator of the stalk `I_{C₀,p₀} ⊆ 𝒪_{S₀,p₀}`. If `s` is an
infinite blow-up sequence of multiplicity `m` for `C₀` starting at `p₀`, then there are a regular
system of parameters `x, y` of `𝒪_{S₀,p₀}`, elements `a k`, and `z` in the
`𝔪`-adic completion such that `y - ∑_{k=1}^n a k * x ^ k` converges to `z` and the image of `f`
lies in `Ideal.span {z ^ m}`. -/
@[mmp "prop_kr1c_infinite_sequence_gives_formal_mth_power"]
theorem exists_mem_span_pow_adicCompletion_of_isConstantMultiplicity
    {S₀ : Scheme.{u}} [IsNoetherian S₀]
    (hreg : ∀ q : S₀, IsRegularLocalRing (S₀.presheaf.stalk q))
    (hdim : topologicalKrullDim S₀ = 2)
    (C₀ : S₀.IdealSheafData) (hC : Stacks.Divisors.IsEffectiveCartierDivisor C₀)
    [IsReduced C₀.subscheme] {p₀ : S₀}
    (hp₀C : p₀ ∈ C₀.support) {m : ℕ} (hm : 2 ≤ m) (hmult : multAt C₀ p₀ = m)
    {f : S₀.presheaf.stalk p₀} (hf : IdealSheafData.stalk C₀ p₀ = Ideal.span {f})
    (s : PointBlowupSequence S₀) (hlen : s.length = ⊤)
    (hp₀ : s.zeroIso.hom.base (s.p 0) = p₀) (hs : s.IsConstantMultiplicity C₀ m) :
    ∃ (x y : S₀.presheaf.stalk p₀) (a : ℕ → S₀.presheaf.stalk p₀)
      (z : AdicCompletion (maximalIdeal (S₀.presheaf.stalk p₀)) (S₀.presheaf.stalk p₀)),
      MMP.Mori.IsRegularSystemOfParameters ![x, y] ∧
      (∀ N : ℕ, ∀ᶠ n in atTop, z - algebraMap _ _ (y - ∑ k ∈ Finset.Icc 1 n, a k * x ^ k) ∈
        (maximalIdeal (S₀.presheaf.stalk p₀)).map
          (algebraMap (S₀.presheaf.stalk p₀)
            (AdicCompletion (maximalIdeal (S₀.presheaf.stalk p₀)) (S₀.presheaf.stalk p₀))) ^ N) ∧
      algebraMap _ (AdicCompletion (maximalIdeal (S₀.presheaf.stalk p₀))
        (S₀.presheaf.stalk p₀)) f ∈ Ideal.span {z ^ m} := by
  obtain ⟨x, y, a, hpar, hmem⟩ :=
    MMP.Resolution.PointBlowupSequence.exists_forall_mem_span_pow_of_isConstantMultiplicity
      hreg hdim C₀ hC hp₀C hm hmult hf s hp₀ hs
  have : IsNoetherianRing (S₀.presheaf.stalk p₀) := (hreg p₀).toIsNoetherian
  obtain ⟨z, hz, hfz⟩ := exists_tendsto_and_mem_span_pow y a
    (hpar.1 ▸ Ideal.subset_span ⟨0, rfl⟩) (by omega) fun j => hmem j (hlen ▸ le_top)
  exact ⟨x, y, a, z, hpar, hz, hfz⟩

end PointBlowupSequence

/-! ### No infinite blow-up sequence of constant multiplicity -/

/-- The multiplicity of an ideal sheaf is unchanged by pulling back along an isomorphism. -/
private theorem multAt_comap_of_isIso {X Y : Scheme.{u}} (φ : Y ⟶ X) [IsIso φ]
    (I : X.IdealSheafData) (y : Y) :
    MMP.Resolution.multAt (I.comap φ) y = MMP.Resolution.multAt I (φ y) := by
  have : IsIso (φ.stalkMap y) := ((isIso_iff_isIso_stalkMap φ).mp inferInstance).2 _
  rw [MMP.Resolution.multAt, MMP.Resolution.multAt, IdealSheafData.stalk_comap]
  exact MMP.Threefold.Resolution.idealOrder_map_ringEquiv
    (asIso (φ.stalkMap y)).commRingCatIsoToRingEquiv (IdealSheafData.stalk I (φ y))

namespace PointBlowupSequence

/-- **Kollár, Lemma 1.68.** Let `S₀` be a smooth surface over a perfect field `k`, `C₀ ⊆ S₀` a
reduced effective Cartier divisor, `p₀ ∈ C₀` a closed point and `m ≥ 2`. A sequence of point
blow-ups `s` starting at `p₀` which is a blow-up sequence of multiplicity `m` for `C₀`
(`IsConstantMultiplicity`) has finite length. -/
@[mmp "lem_kr1c_no_infinite_constant_multiplicity_sequence"]
theorem length_ne_top_of_isConstantMultiplicity
    {k : Type u} [Field k] [PerfectField k] {S₀ : Scheme.{u}} (sS : S₀ ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 2 sS] [QuasiCompact sS]
    (C₀ : S₀.IdealSheafData) (hC : Stacks.Divisors.IsEffectiveCartierDivisor C₀)
    [IsReduced C₀.subscheme] {p₀ : S₀} (hp₀c : IsClosed ({p₀} : Set S₀))
    (hp₀C : p₀ ∈ C₀.support) {m : ℕ} (hm : 2 ≤ m)
    (s : PointBlowupSequence S₀) (hp₀ : s.zeroIso.hom.base (s.p 0) = p₀)
    (hs : s.IsConstantMultiplicity C₀ m) :
    s.length ≠ ⊤ := by
  intro hlen
  have : Smooth sS := SmoothOfRelativeDimension.smooth 2 sS
  have : IsLocallyNoetherian S₀ := LocallyOfFiniteType.isLocallyNoetherian sS
  have : CompactSpace S₀ := QuasiCompact.compactSpace_of_compactSpace sS
  have : IsNoetherian S₀ := {}
  have : Nonempty S₀ := ⟨p₀⟩
  have hreg := (MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk sS).mp
    inferInstance
  have hdim : topologicalKrullDim S₀ = 2 :=
    topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 2 sS
  obtain ⟨f, hfnzd, hfI⟩ :=
    MMP.Resolution.Kr1c.hasPrincipalStalks_of_isEffectiveCartierDivisor hC p₀
  have hmult : MMP.Resolution.multAt C₀ p₀ = m := by
    rw [← hp₀, ← multAt_comap_of_isIso s.zeroIso.hom]
    exact hs.1 0 zero_le
  obtain ⟨x, y, a, z, hxy, hconv, hmem⟩ :=
    MMP.Resolution.PointBlowupSequence.exists_mem_span_pow_adicCompletion_of_isConstantMultiplicity
      hreg hdim C₀ hC hp₀C hm hmult hfI s hlen hp₀ hs
  let := MMP.Mori.stalkAlgebra sS p₀
  obtain ⟨-, -, _⟩ := MMP.Flips.ResolutionInputs.stalk_facts sS p₀
  have := MMP.Flips.ResolutionInputs.finite_residueField_of_isClosed sS p₀ hp₀c
  have hmem_max : ∀ i, ![x, y] i ∈ maximalIdeal (S₀.presheaf.stalk p₀) := fun i =>
    hxy.1 ▸ Ideal.subset_span ⟨i, rfl⟩
  obtain ⟨n, hn⟩ := (hconv 1).exists
  have hw : y - ∑ k ∈ Finset.Icc 1 n, a k * x ^ k ∈ maximalIdeal (S₀.presheaf.stalk p₀) :=
    Ideal.sub_mem _ (hmem_max 1) (Ideal.sum_mem _ fun k hk => Ideal.mul_mem_left _ _
      (Ideal.pow_mem_of_mem _ (hmem_max 0) _ (Finset.mem_Icc.mp hk).1))
  have hzw : z - algebraMap _ _ (y - ∑ k ∈ Finset.Icc 1 n, a k * x ^ k) ∈
      (maximalIdeal (S₀.presheaf.stalk p₀)).map (algebraMap _
        (AdicCompletion (maximalIdeal (S₀.presheaf.stalk p₀)) (S₀.presheaf.stalk p₀))) := by
    simpa using hn
  have hz : z ∈ (maximalIdeal (S₀.presheaf.stalk p₀)).map (algebraMap _
      (AdicCompletion (maximalIdeal (S₀.presheaf.stalk p₀)) (S₀.presheaf.stalk p₀))) := by
    simpa using Ideal.add_mem _ hzw (Ideal.mem_map_of_mem _ hw)
  let e := IdealSheafData.subschemeStalkQuotEquiv C₀ (IdealSheafData.subschemePoint C₀ p₀ hp₀C)
  have hred : IsReduced (S₀.presheaf.stalk p₀ ⧸ IdealSheafData.stalk C₀ p₀) :=
    isReduced_of_injective e.toRingHom e.injective
  rw [hfI] at hred
  exact MMP.Resolution.algebraMap_notMem_span_pow_adicCompletion k hxy
    (nonZeroDivisors.ne_zero hfnzd) hred hm hz hmem

end PointBlowupSequence

/-! ### Smooth surfaces and their point blow-ups -/

/-- The residue field at a closed point of a scheme locally of finite type over a perfect field
is separable over it. -/
private theorem isSeparable_residueField {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] {o : X} (ho : IsClosed ({o} : Set X)) :
    letI : Algebra k (X.residueField o) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫ X.Γevaluation o).hom.toAlgebra
    Algebra.IsSeparable k (X.residueField o) := by
  let : Algebra k (X.residueField o) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫ X.Γevaluation o).hom.toAlgebra
  have : Module.Finite k (X.residueField o) :=
    MMP.Flips.ResolutionInputs.finite_residueField_of_isClosed sX o ho
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

/-- A smooth morphism is smooth of some relative dimension near every point of the source. -/
private theorem exists_smoothOfRelativeDimension_nbhd {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    (x : X) : ∃ V : X.Opens, x ∈ V ∧ ∃ n : ℕ, SmoothOfRelativeDimension n (V.ι ≫ f) := by
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ := Smooth.exists_isStandardSmooth f x
  obtain ⟨n, hn⟩ : ∃ n, (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension n := by
    let := (f.appLE U V e).hom.toAlgebra
    obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hf.toAlgebra.out
    exact ⟨P.dimension, P.isStandardSmoothOfRelativeDimension rfl⟩
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have hQi := (HasRingHomProperty.isLocal_ringHomProperty
    (@SmoothOfRelativeDimension n)).respectsIso
  have : (RingHom.toMorphismProperty
      (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n))).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp hQi
  have h : SmoothOfRelativeDimension n (f.resLE U V e) := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension n)]
    exact (MorphismProperty.arrow_mk_iso_iff (RingHom.toMorphismProperty
      (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)))
      (arrowResLEAppIso f U V e)).mpr
      (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ hn)
  refine ⟨V, hx, n, ?_⟩
  rw [← Scheme.Hom.resLE_comp_ι f e]
  exact inferInstanceAs (SmoothOfRelativeDimension (n + 0) _)

/-- Every point of the blow-up `B` of a closed point of a scheme, when `B` is smooth over a field,
is a specialization of a point off the exceptional curve: the local equation of the exceptional
curve is a nonzero element of the domain `𝒪_{B,w}`. -/
private theorem exists_specializes_notMem_support_exceptionalIdeal {k : Type u} [Field k]
    {X : Scheme.{u}} (I : X.IdealSheafData) (f : blowUp I ⟶ Spec (.of k)) [Smooth f]
    (w : blowUp I) : ∃ η, η ⤳ w ∧ η ∉ (exceptionalIdeal I).support := by
  have hreg := isRegularLocalRing_stalk_of_smooth_over_field f w
  have : IsDomain ((blowUp I).presheaf.stalk w) := IsRegularLocalRing.isDomain _
  obtain ⟨a, ha, hspan⟩ :=
    Stacks.Divisors.exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor
      (exceptionalIdeal I) (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal _) w
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact not_isRegular_zero ha
  let P : PrimeSpectrum ((blowUp I).presheaf.stalk w) := ⟨⊥, Ideal.isPrime_bot⟩
  have hsp : (blowUp I).fromSpecStalk w P ⤳ w := MMP.Resolution.specializes_fromSpecStalk w P
  refine ⟨_, hsp, fun hmem => ?_⟩
  rw [MMP.Resolution.mem_support_iff_stalk_le_primeOfSpecializes _ hsp,
    MMP.Resolution.primeOfSpecializes_fromSpecStalk, hspan, Ideal.span_le,
    Set.singleton_subset_iff] at hmem
  exact ha0 hmem

/-- The blow-up of a closed point of a smooth quasi-compact surface over a perfect field is again a
smooth quasi-compact surface. -/
private theorem smoothOfRelativeDimension_blowUpToBase_comp {k : Type u} [Field k]
    [PerfectField k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 sX]
    [QuasiCompact sX] {p : X} (hp : IsClosed ({p} : Set X)) :
    SmoothOfRelativeDimension 2
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ≫ sX) ∧
      QuasiCompact (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ≫ sX) := by
  set I := Scheme.IdealSheafData.vanishingIdeal (⟨{p}, hp⟩ : TopologicalSpace.Closeds X)
  have : Smooth sX := SmoothOfRelativeDimension.smooth 2 sX
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsProper (blowUpToBase I) := isProper_blowUpToBase I
  refine ⟨?_, inferInstance⟩
  have : Smooth (blowUpToBase I ≫ sX) :=
    MMP.Resolution.Kollar.smooth_blowUpToBase_comp_of_isSeparable sX hp
      (isSeparable_residueField sX hp)
  -- the local dimension of the blow-up is `2` at every point
  have hloc : ∀ x : blowUp I, topologicalKrullDimAt (blowUp I) x = (2 : ℕ) := by
    intro x
    obtain ⟨V, hxV, m, hm⟩ := exists_smoothOfRelativeDimension_nbhd (blowUpToBase I ≫ sX) x
    obtain ⟨η, hηx, hηE⟩ :=
      exists_specializes_notMem_support_exceptionalIdeal I (blowUpToBase I ≫ sX) x
    have hV : ∀ y : V.toScheme, topologicalKrullDimAt (blowUp I) (V.ι y) = m := fun y =>
      (V.ι.isOpenEmbedding.topologicalKrullDimAt_eq y).trans
        (topologicalKrullDimAt_eq_of_smoothOfRelativeDimension_over_field m
          (V.ι ≫ blowUpToBase I ≫ sX) y)
    let O : (blowUp I).Opens := (exceptionalIdeal I).support.compl
    have := MMP.Resolution.Kr1c.isOpenImmersion_compl_exceptional I
    have : SmoothOfRelativeDimension 2 (O.ι ≫ blowUpToBase I ≫ sX) := by
      rw [← Category.assoc]
      exact inferInstanceAs (SmoothOfRelativeDimension (0 + 2) _)
    exact (hV (⟨x, hxV⟩ : V.toScheme)).trans
      ((hV (⟨η, hηx.mem_open V.isOpen hxV⟩ : V.toScheme)).symm.trans
        ((O.ι.isOpenEmbedding.topologicalKrullDimAt_eq (⟨η, hηE⟩ : O.toScheme)).trans
          (topologicalKrullDimAt_eq_of_smoothOfRelativeDimension_over_field 2
            (O.ι ≫ blowUpToBase I ≫ sX) _)))
  refine Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq _ 2 fun x => ?_
  set f := blowUpToBase I ≫ sX
  have : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have hpre : f.base ⁻¹' {f.base x} = (Set.univ : Set (blowUp I)) := by
    ext y
    simp [Subsingleton.elim (f.base y) (f.base x)]
  let e : f.fiber (f.base x) ≃ₜ blowUp I :=
    (f.fiberHomeo _).trans ((Homeomorph.setCongr hpre).trans (Homeomorph.Set.univ _))
  have he : e (f.asFiber x) = x := f.fiberι_asFiber x
  calc topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x)
      = topologicalKrullDimAt (blowUp I) (e (f.asFiber x)) :=
        (e.isOpenEmbedding.topologicalKrullDimAt_eq _).symm
    _ = _ := by rw [he]; exact hloc x

/-- A smooth quasi-compact surface over a field is a regular surface. -/
private theorem isRegularSurface_of_smoothOfRelativeDimension {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 sX]
    [QuasiCompact sX] : IsRegularSurface X := by
  have : Smooth sX := SmoothOfRelativeDimension.smooth 2 sX
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := {}
  refine ⟨inferInstance, isRegularLocalRing_stalk_of_smooth_over_field sX, fun x hx => ?_⟩
  rw [← topologicalKrullDimAt_eq_ringKrullDim_stalk_of_closed_point sX x hx,
    topologicalKrullDimAt_eq_of_smoothOfRelativeDimension_over_field 2 sX x]
  rfl

/-! ### Birational transforms of reduced effective Cartier divisors -/

/-- The multiplicity of a nonzero element of a Noetherian local ring is finite (Krull's
intersection theorem). -/
private theorem mult_ne_top_of_ne_zero {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {f : R} (hf : f ≠ 0) : mult f ≠ ⊤ := by
  have hK := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal R) (maximalIdeal.isMaximal R).ne_top
  obtain ⟨j, hj⟩ : ∃ j : ℕ, f ∉ maximalIdeal R ^ j := by
    by_contra! h
    apply hf
    have : f ∈ ⨅ i : ℕ, maximalIdeal R ^ i := Ideal.mem_iInf.mpr h
    rwa [hK] at this
  refine ne_top_of_le_ne_top (ENat.natCast_ne_top j) (iSup₂_le fun i hi => ?_)
  by_contra! hlt
  exact hj (Ideal.pow_le_pow_right (by exact_mod_cast hlt.le)
    (hi (Ideal.mem_span_singleton_self f)))

/-- The birational transform of an effective Cartier divisor in the blow-up of a closed point of
a regular surface is an effective Cartier divisor. -/
private theorem isEffectiveCartierDivisor_birationalTransform {S : Scheme.{u}}
    (hS : IsRegularSurface S) {p : S} (hp : IsClosed ({p} : Set S)) {C : S.IdealSheafData}
    (hC : Stacks.Divisors.IsEffectiveCartierDivisor C) :
    Stacks.Divisors.IsEffectiveCartierDivisor (birationalTransform p hp C) := by
  have : IsNoetherian S := hS.1
  have : IsLocallyNoetherian (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) :=
    (Stacks.ResolutionOfSurfaces.isNoetherian_blowUp _).toIsLocallyNoetherian
  have hreg := hS.2.1 p
  have : IsNoetherianRing (S.presheaf.stalk p) := hreg.toIsNoetherian
  have hPS := MMP.Resolution.Kr1c.hasPrincipalStalks_of_isEffectiveCartierDivisor hC
  have hm : multAt C p ≠ ⊤ := by
    obtain ⟨g, hg, hspan⟩ := hPS p
    rw [multAt, hspan]
    exact mult_ne_top_of_ne_zero (nonZeroDivisors.ne_zero hg)
  exact Stacks.Divisors.isEffectiveCartierDivisor_of_stalk_isPrincipal_nonZeroDivisor _
    fun x _ => MMP.Resolution.Kr1c.hasPrincipalStalks_birationalTransform hp hreg (hS.2.2 p hp)
      hPS hm x

/-- The birational transform of a reduced closed subscheme in the blow-up of a closed point is
reduced. -/
private theorem isReduced_birationalTransform {S : Scheme.{u}} {p : S}
    (hp : IsClosed ({p} : Set S)) (C : S.IdealSheafData) [IsReduced C.subscheme] :
    IsReduced (birationalTransform p hp C).subscheme := by
  set I := Scheme.IdealSheafData.vanishingIdeal (⟨{p}, hp⟩ : TopologicalSpace.Closeds S)
  let g := Limits.pullback.snd C.subschemeι (blowUpToBase I)
  let O : (blowUp I).Opens := (exceptionalIdeal I).support.compl
  -- off the exceptional curve, `C ×_S B` is an open subscheme of `C`
  have := MMP.Resolution.Kr1c.isOpenImmersion_compl_exceptional I
  have hsq : IsPullback ((g ⁻¹ᵁ O).ι ≫ Limits.pullback.fst C.subschemeι (blowUpToBase I))
      (g ∣_ O) C.subschemeι (O.ι ≫ blowUpToBase I) :=
    (isPullback_morphismRestrict g O).flip.paste_horiz
      (IsPullback.of_hasPullback C.subschemeι (blowUpToBase I))
  have : IsOpenImmersion
      ((g ⁻¹ᵁ O).ι ≫ Limits.pullback.fst C.subschemeι (blowUpToBase I)) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hsq.flip inferInstance
  have : IsReduced (g ⁻¹ᵁ O).toScheme := isReduced_of_isOpenImmersion
    ((g ⁻¹ᵁ O).ι ≫ Limits.pullback.fst C.subschemeι (blowUpToBase I))
  exact inferInstanceAs (IsReduced ((g ⁻¹ᵁ O).ι ≫ g).image)

/-! ### Smoothness along a sequence of point blow-ups -/

/-- Every surface `S_i` of a sequence of point blow-ups of a smooth quasi-compact surface over a
perfect field is a smooth quasi-compact surface. -/
private theorem smoothOfRelativeDimension_π_comp {k : Type u} [Field k] [PerfectField k]
    {S₀ : Scheme.{u}} (sS : S₀ ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 sS]
    [QuasiCompact sS] (s : PointBlowupSequence S₀) :
    ∀ (i : ℕ) (hi : (i : ℕ∞) ≤ s.length),
      SmoothOfRelativeDimension 2 (s.π i hi ≫ sS) ∧ QuasiCompact (s.π i hi ≫ sS)
  | 0, _ => by
    change SmoothOfRelativeDimension 2 (s.zeroIso.hom ≫ sS) ∧ QuasiCompact (s.zeroIso.hom ≫ sS)
    exact ⟨inferInstanceAs (SmoothOfRelativeDimension (0 + 2) _), inferInstance⟩
  | i + 1, hi => by
    have hlt := PointBlowupSequence.coe_lt_of_succ_le hi
    obtain ⟨h1, h2⟩ := smoothOfRelativeDimension_π_comp sS s i hlt.le
    obtain ⟨h3, h4⟩ := smoothOfRelativeDimension_blowUpToBase_comp (s.π i hlt.le ≫ sS)
      (s.isClosed_p i hlt)
    change SmoothOfRelativeDimension 2 ((s.blowupIso i hlt).hom ≫ (blowUpToBase _ ≫
        (s.π i hlt.le ≫ sS))) ∧ QuasiCompact ((s.blowupIso i hlt).hom ≫ (blowUpToBase _ ≫
        (s.π i hlt.le ≫ sS)))
    exact ⟨inferInstanceAs (SmoothOfRelativeDimension (0 + 2) _), inferInstance⟩

/-! ### Sequences of point blow-ups of a regular surface -/

/-- Being a regular surface is invariant under isomorphism. -/
private theorem isRegularSurface_of_iso {X Y : Scheme.{u}} (e : X ≅ Y)
    (hY : IsRegularSurface Y) : IsRegularSurface X := by
  obtain ⟨hN, hreg, hdim⟩ := hY
  have hst : ∀ x : X, IsIso (e.hom.stalkMap x) := fun x =>
    ((isIso_iff_isIso_stalkMap e.hom).mp (inferInstanceAs (IsIso e.hom))).2 x
  let st : ∀ x : X, Y.presheaf.stalk (e.hom.base x) ≃+* X.presheaf.stalk x := fun x =>
    (@asIso _ _ _ _ (e.hom.stalkMap x) (hst x)).commRingCatIsoToRingEquiv
  refine ⟨?_, fun x => IsRegularLocalRing.of_ringEquiv (st x), fun x hx => ?_⟩
  · have : IsLocallyNoetherian Y := hN.toIsLocallyNoetherian
    have : IsLocallyNoetherian X := isLocallyNoetherian_of_isOpenImmersion e.hom
    have : CompactSpace X := e.hom.homeomorph.symm.compactSpace
    exact {}
  · rw [← ringKrullDim_eq_of_ringEquiv (st x)]
    refine hdim _ ?_
    rw [← Set.image_singleton]
    exact e.hom.homeomorph.isClosedMap _ hx

/-- Every scheme `S_i` of a sequence of point blow-ups of a regular surface is a regular
surface. -/
private theorem isRegularSurface_S {S₀ : Scheme.{u}} (hS : IsRegularSurface S₀)
    (s : PointBlowupSequence S₀) : ∀ i : ℕ, (i : ℕ∞) ≤ s.length → IsRegularSurface (s.S i)
  | 0, _ => isRegularSurface_of_iso s.zeroIso hS
  | i + 1, hi =>
    have hlt := PointBlowupSequence.coe_lt_of_succ_le hi
    isRegularSurface_of_iso (s.blowupIso i hlt)
      (isRegularSurface_blowUp (isRegularSurface_S hS s i hlt.le) _ (s.isClosed_p i hlt))

/-- `π_i : S_i → S₀` is a composite of `i` point blow-ups. -/
private theorem isCompositeOfPointBlowupsOfLength_π {S₀ : Scheme.{u}}
    (s : PointBlowupSequence S₀) :
    ∀ (i : ℕ) (hi : (i : ℕ∞) ≤ s.length), IsCompositeOfPointBlowupsOfLength i (s.π i hi)
  | 0, _ => inferInstanceAs (IsIso s.zeroIso.hom)
  | i + 1, hi =>
    have hlt := PointBlowupSequence.coe_lt_of_succ_le hi
    ⟨s.S i, s.π i hlt.le, s.p i, s.isClosed_p i hlt,
      isCompositeOfPointBlowupsOfLength_π s i hlt.le, s.blowupIso i hlt, by
        rw [PointBlowupSequence.π, PointBlowupSequence.σ, Category.assoc]⟩

/-! ### Points off the support and points of the blow-up -/

/-- A closed subscheme has simple normal crossings at a point with regular local ring off its
support: there the ideal is the unit ideal, the empty monomial in a regular system of
parameters. -/
private theorem hasSNCAt_of_notMem_support {X : Scheme.{u}} (D : X.IdealSheafData) {x : X}
    [IsRegularLocalRing (X.presheaf.stalk x)] (hx : x ∉ D.support) : HasSNCAt D x := by
  classical
  obtain ⟨N, w, hw⟩ := MMP.Mori.exists_isRegularSystemOfParameters (X.presheaf.stalk x)
  choose V hV t ht using fun c => X.presheaf.exists_germ_eq (x := x) (w c)
  let W : X.Opens := Finset.univ.inf V ⊓ D.support.compl
  have hxW : x ∈ W := by
    refine ⟨?_, hx⟩
    change x ∈ ((Finset.univ.inf V : X.Opens) : Set X)
    rw [TopologicalSpace.Opens.coe_finset_inf, Finset.inf_eq_iInf]
    exact Set.mem_iInter₂.2 fun c _ => hV c
  have hWV : ∀ c, W ≤ V c := fun c => inf_le_left.trans (Finset.inf_le (Finset.mem_univ c))
  refine ⟨N, W, hxW, fun c => (X.presheaf.map (homOfLE (hWV c)).op).hom (t c), 0, ?_,
    fun y hy => ?_⟩
  · convert hw using 1
    funext c
    rw [X.presheaf.germ_res_apply, ht]
  · simp only [Pi.zero_apply, pow_zero, Finset.prod_const_one, map_one, Ideal.span_singleton_one]
    exact (IdealSheafData.stalk_eq_top_iff_notMem_support D y).2 hy.2

/-- The blow-up of a closed point of a regular surface is nonempty. -/
private theorem nonempty_blowUp {X : Scheme.{u}} (hX : IsRegularSurface X) (x : X)
    (hx : IsClosed ({x} : Set X)) :
    Nonempty (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩)) := by
  set I := Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : TopologicalSpace.Closeds X)
  obtain ⟨y, hy⟩ : ∃ y : X, y ≠ x := by
    by_contra! hall
    have h2 := hX.2.2 x hx
    rw [ringKrullDim_stalk_eq_coheight, Order.coheight_eq_zero.mpr
      (fun y _ => (hall y).symm ▸ le_rfl)] at h2
    exact absurd h2 (by decide)
  have hyU : y ∈ (I.support.compl : X.Opens) := by
    change y ∉ (I.support : Set X)
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact hy
  have := isIso_blowUp_restrict_compl_support I
  exact ⟨((inv (blowUpToBase I ∣_ (I.support.compl : X.Opens))).base ⟨y, hyU⟩).1⟩

/-! ### The vertices of the tree of infinitely near singularities -/

/-- The standing hypotheses at a vertex `t`: `t.S` is a smooth quasi-compact surface over `k` and
`t.C` is a reduced effective Cartier divisor. -/
private structure IsGoodVertex (k : Type u) [Field k] (t : PointedSubscheme.{u}) : Prop where
  smooth : ∃ sX : t.S ⟶ Spec (.of k), SmoothOfRelativeDimension 2 sX ∧ QuasiCompact sX
  cartier : Stacks.Divisors.IsEffectiveCartierDivisor t.C
  reduced : IsReduced t.C.subscheme

/-- The children of a good vertex are good, and are closed points of the curve. -/
private theorem isGoodVertex_of_mem_first {k : Type u} [Field k] [PerfectField k]
    {t t' : PointedSubscheme.{u}} (ht : IsGoodVertex k t)
    (ht' : t' ∈ firstInfinitelyNearSingularities t) :
    IsGoodVertex k t' ∧ IsClosed ({t'.q} : Set t'.S) ∧ t'.q ∈ t'.C.support := by
  obtain ⟨⟨sX, h1, h2⟩, hcart, hred⟩ := ht
  by_cases h : IsClosed ({t.q} : Set t.S)
  · rw [firstInfinitelyNearSingularities, dite_eq_left h] at ht'
    obtain ⟨q, hqc, hqC, -, -, rfl⟩ := ht'
    have hS := isRegularSurface_of_smoothOfRelativeDimension sX
    have : IsNoetherian t.S := hS.1
    obtain ⟨h3, h4⟩ := smoothOfRelativeDimension_blowUpToBase_comp sX h
    exact ⟨⟨⟨_, h3, h4⟩, isEffectiveCartierDivisor_birationalTransform hS h hcart,
      isReduced_birationalTransform h t.C⟩, hqc, hqC⟩
  · rw [firstInfinitelyNearSingularities, dite_eq_right h] at ht'
    exact ht'.elim

/-- Every infinitely near singular point of a good vertex at a closed point of its curve is good,
and is a closed point of its curve. -/
private theorem isGoodVertex_of_mem {k : Type u} [Field k] [PerfectField k]
    {t : PointedSubscheme.{u}} (ht : IsGoodVertex k t) (hqc : IsClosed ({t.q} : Set t.S))
    (hqC : t.q ∈ t.C.support) :
    ∀ (n : ℕ), ∀ t' ∈ infinitelyNearSingularities t n,
      IsGoodVertex k t' ∧ IsClosed ({t'.q} : Set t'.S) ∧ t'.q ∈ t'.C.support := by
  intro n
  induction n with
  | zero =>
    intro t' ht'
    rw [infinitelyNearSingularities, Set.mem_singleton_iff] at ht'
    subst ht'
    exact ⟨ht, hqc, hqC⟩
  | succ n ih =>
    intro t' ht'
    rw [infinitelyNearSingularities, Set.mem_iUnion₂] at ht'
    obtain ⟨t'', ht'', ht'⟩ := ht'
    exact isGoodVertex_of_mem_first (ih t'' ht'').1 ht'

/-! ### The curve -/

/-- The dimension of local rings grows along specialization. -/
private theorem ringKrullDim_stalk_le_of_specializes {X : Scheme.{u}} {x y : X} (h : x ⤳ y) :
    ringKrullDim (X.presheaf.stalk x) ≤ ringKrullDim (X.presheaf.stalk y) := by
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight]
  exact_mod_cast Order.coheight_anti (α := X) (show y ≤ x from h)

/-- A closed point of a closed subscheme is a closed point of the ambient scheme lying on the
support. -/
private theorem isClosed_and_mem_support_of_isClosed {S : Scheme.{u}} (C : S.IdealSheafData)
    {z : C.subscheme} (hz : IsClosed ({z} : Set C.subscheme)) :
    IsClosed ({C.subschemeι z} : Set S) ∧ C.subschemeι z ∈ C.support := by
  refine ⟨by simpa only [Set.image_singleton] using
    C.subschemeι.isClosedEmbedding.isClosedMap _ hz, ?_⟩
  rw [← SetLike.mem_coe, ← Scheme.IdealSheafData.range_subschemeι]
  exact ⟨z, rfl⟩

/-- A nonempty effective Cartier divisor on a smooth quasi-compact surface over a field has
dimension one. -/
private theorem topologicalKrullDim_subscheme_eq_one {k : Type u} [Field k] {S : Scheme.{u}}
    (sS : S ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 sS] [QuasiCompact sS]
    (C : S.IdealSheafData) (hC : Stacks.Divisors.IsEffectiveCartierDivisor C)
    (hne : (C.support : Set S).Nonempty) : topologicalKrullDim C.subscheme = 1 := by
  have hS := isRegularSurface_of_smoothOfRelativeDimension sS
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
  have : CompactSpace C.subscheme := C.subschemeι.isClosedEmbedding.compactSpace
  have hPS := MMP.Resolution.Kr1c.hasPrincipalStalks_of_isEffectiveCartierDivisor hC
  -- at a closed point of the curve the local ring has dimension one
  have hcl : ∀ z : C.subscheme, IsClosed ({z} : Set C.subscheme) →
      ringKrullDim (C.subscheme.presheaf.stalk z) = 1 := by
    intro z hz
    obtain ⟨hzS, hzC⟩ := isClosed_and_mem_support_of_isClosed C hz
    obtain ⟨g, hg, hspan⟩ := hPS (C.subschemeι z)
    have := hS.2.1 (C.subschemeι z)
    have hgm : g ∈ maximalIdeal (S.presheaf.stalk (C.subschemeι z)) := by
      have hne : IdealSheafData.stalk C (C.subschemeι z) ≠ ⊤ := fun h =>
        ((IdealSheafData.stalk_eq_top_iff_notMem_support C _).1 h) hzC
      rw [hspan, Ne, Ideal.span_singleton_eq_top] at hne
      exact (mem_maximalIdeal g).mpr hne
    rw [← ringKrullDim_eq_of_ringEquiv (IdealSheafData.subschemeStalkQuotEquiv C z), hspan]
    exact (ringKrullDim_quotient_span_singleton_eq_one_and_not_isFiniteLength (hS.2.2 _ hzS)
      (nonZeroDivisors.ne_zero hg) hgm).1
  rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
  obtain ⟨x, hx⟩ := hne
  obtain ⟨z₀, -, hz₀⟩ := isClosed_univ.exists_closed_singleton
    ⟨IdealSheafData.subschemePoint C x hx, Set.mem_univ _⟩
  refine le_antisymm (iSup_le fun z => ?_) ((hcl z₀ hz₀).symm.le.trans (le_iSup
    (fun z => ringKrullDim (C.subscheme.presheaf.stalk z)) z₀))
  obtain ⟨z', hz', hz'c⟩ :=
    (isClosed_closure (s := ({z} : Set C.subscheme))).exists_closed_singleton
      ⟨z, subset_closure rfl⟩
  exact (ringKrullDim_stalk_le_of_specializes (specializes_iff_mem_closure.mpr hz')).trans
    (hcl z' hz'c).le

/-- A reduced effective Cartier divisor on a smooth quasi-compact surface over a field has finitely
many singular points. -/
private theorem finite_singular_points {k : Type u} [Field k] {S : Scheme.{u}}
    (sS : S ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 sS] [QuasiCompact sS]
    (C : S.IdealSheafData) (hC : Stacks.Divisors.IsEffectiveCartierDivisor C)
    [IsReduced C.subscheme] :
    {p : S | IsClosed ({p} : Set S) ∧ p ∈ C.support ∧
      ¬ IsRegularLocalRing (S.presheaf.stalk p ⧸ IdealSheafData.stalk C p)}.Finite := by
  by_cases hne : (C.support : Set S).Nonempty
  swap
  · exact Set.finite_empty.subset fun p hp => (hne ⟨p, hp.2.1⟩).elim
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
  have : CompactSpace C.subscheme := C.subschemeι.isClosedEmbedding.compactSpace
  have : Smooth sS := SmoothOfRelativeDimension.smooth 2 sS
  have : LocallyOfFiniteType (C.subschemeι ≫ sS) := inferInstance
  have : IsLocallyNoetherian C.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (C.subschemeι ≫ sS)
  have : IsNoetherian C.subscheme := {}
  have hT : IsClosed (singularLocus C.subscheme) :=
    MMP.Resolution.isClosed_setOf_not_isRegularLocalRing (C.subschemeι ≫ sS)
  have hfin : (singularLocus C.subscheme).Finite :=
    Stacks.Topology.Dimension.finite_of_not_irreducibleComponent_subset
      (topologicalKrullDim_subscheme_eq_one sS C hC hne).le hT
      fun _ hZ => not_subset_singularLocus_of_mem_irreducibleComponents C.subscheme hZ
  refine (hfin.image C.subschemeι).subset fun p hp => ?_
  obtain ⟨-, hpC, hsing⟩ := hp
  obtain ⟨z, hzp⟩ : ∃ z : C.subscheme, C.subschemeι z = p :=
    ⟨_, IdealSheafData.subschemeι_subschemePoint C p hpC⟩
  refine ⟨z, fun hreg => hsing ?_, hzp⟩
  have : IsRegularLocalRing (C.subscheme.presheaf.stalk z) := hreg
  subst hzp
  exact IsRegularLocalRing.of_ringEquiv (IdealSheafData.subschemeStalkQuotEquiv C z).symm

/-- A closed subscheme of a smooth quasi-compact scheme over a perfect field which is regular at
each of its closed points is smooth. -/
private theorem smooth_subschemeι_comp {k : Type u} [Field k] [PerfectField k] {S : Scheme.{u}}
    (sS : S ⟶ Spec (.of k)) [Smooth sS] [QuasiCompact sS] (C : S.IdealSheafData)
    (hC : ∀ q : S, IsClosed ({q} : Set S) → q ∈ C.support →
      IsRegularLocalRing (S.presheaf.stalk q ⧸ IdealSheafData.stalk C q)) :
    Smooth (C.subschemeι ≫ sS) := by
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
  have : CompactSpace C.subscheme := C.subschemeι.isClosedEmbedding.compactSpace
  rw [MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk]
  by_contra! hne
  obtain ⟨z₀, hz₀⟩ := hne
  have hT : IsClosed (regularLocus C.subscheme)ᶜ :=
    (MMP.Flips.isOpen_regularLocus_of_locallyOfFiniteType (C.subschemeι ≫ sS)).isClosed_compl
  obtain ⟨z, hz, hzc⟩ := hT.exists_closed_singleton ⟨z₀, hz₀⟩
  obtain ⟨hzS, hzC⟩ := isClosed_and_mem_support_of_isClosed C hzc
  have := hC _ hzS hzC
  exact hz (IsRegularLocalRing.of_ringEquiv (IdealSheafData.subschemeStalkQuotEquiv C z))

/-! ### The tree of infinitely near singular points -/

/-- **Finiteness of the tree.** Over a reduced effective Cartier divisor `C₀` of a smooth
quasi-compact surface over a perfect field, the chains of infinitely near singular points starting
at the closed singular points of `C₀` form a finite set: there are finitely many such points, and
over each the tree is finite by Kőnig's lemma, since no vertex admits an infinite blow-up sequence
of constant multiplicity `μ ≥ 2`. -/
private theorem finite_chains {k : Type u} [Field k] [PerfectField k] {S₀ : Scheme.{u}}
    (sS : S₀ ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 sS] [QuasiCompact sS]
    (C₀ : S₀.IdealSheafData) (hC : Stacks.Divisors.IsEffectiveCartierDivisor C₀)
    [IsReduced C₀.subscheme] [Nonempty S₀] :
    {l : List PointedSubscheme.{u} | ∃ p : S₀, IsClosed ({p} : Set S₀) ∧ p ∈ C₀.support ∧
      ¬ IsRegularLocalRing (S₀.presheaf.stalk p ⧸ IdealSheafData.stalk C₀ p) ∧
      l.head? = some ⟨S₀, C₀, p⟩ ∧
      List.IsChain (fun t t' => t' ∈ firstInfinitelyNearSingularities t) l}.Finite := by
  have hS := isRegularSurface_of_smoothOfRelativeDimension sS
  have : IsNoetherian S₀ := hS.1
  refine ((finite_singular_points sS C₀ hC).biUnion fun p hp =>
    finite_isChain_firstInfinitelyNearSingularities_of_length_ne_top hS.2.1
      (topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 2 sS) C₀ hC hp.1 hp.2.1
      ?_).subset ?_
  · intro n t ht μ hμ s' hs'0 hs'
    obtain ⟨⟨⟨sX, _, _⟩, hcart, _⟩, hqc, hqC⟩ := isGoodVertex_of_mem (k := k)
      (t := ⟨S₀, C₀, p⟩) ⟨⟨sS, inferInstance, inferInstance⟩, hC, inferInstance⟩ hp.1 hp.2.1 n t ht
    exact PointBlowupSequence.length_ne_top_of_isConstantMultiplicity sX t.C hcart hqc hqC
      hμ s' hs'0 hs'
  · rintro l ⟨p, hpc, hpC, hpsing, hl⟩
    exact Set.mem_biUnion (x := p) ⟨hpc, hpC, hpsing⟩ hl

/-- A weak embedded resolution sequence of the empty curve has length `0`, and stops. -/
private theorem weakEmbeddedResolutionStops_of_support_eq_empty {S₀ : Scheme.{u}}
    {C₀ : S₀.IdealSheafData} (hne : (C₀.support : Set S₀) = ∅) {s : PointBlowupSequence S₀}
    (hs : s.IsWeakEmbeddedResolution C₀) : s.WeakEmbeddedResolutionStops C₀ := by
  have hsupp : ∀ q : s.S 0, q ∉ (C₀.comap s.zeroIso.hom).support := fun q hq => by
    change q ∈ ((C₀.comap s.zeroIso.hom).support : Set (s.S 0)) at hq
    rw [Scheme.IdealSheafData.support_comap] at hq
    change s.zeroIso.hom q ∈ (C₀.support : Set S₀) at hq
    rw [hne] at hq
    exact hq
  have hlen : s.length = 0 := by
    by_contra h
    exact hsupp _ (hs 0 (pos_iff_ne_zero.mpr h)).1
  exact ⟨0, hlen, fun q _ hq => (hsupp q hq).elim⟩

namespace PointBlowupSequence

/-- **Kollár, Theorem 1.67 (weak embedded resolution, local method).** Let `S₀` be a smooth
surface over a perfect field `k` and `C₀ ⊆ S₀` a reduced effective Cartier divisor. Every weak
embedded resolution sequence `s` for `(S₀, C₀)` which no longer weak embedded resolution sequence
extends stops (`WeakEmbeddedResolutionStops`), and its final birational transform `C_n ⊆ S_n` is
smooth over `k`. -/
@[mmp "thm_kr1c_weak_embedded_resolution_local"]
theorem weakEmbeddedResolutionStops_of_maximal
    {k : Type u} [Field k] [PerfectField k] {S₀ : Scheme.{u}} (sS : S₀ ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 2 sS] [QuasiCompact sS]
    (C₀ : S₀.IdealSheafData) (hC : Stacks.Divisors.IsEffectiveCartierDivisor C₀)
    [IsReduced C₀.subscheme]
    (s : PointBlowupSequence S₀) (hs : s.IsWeakEmbeddedResolution C₀)
    (hmax : ∀ s' : PointBlowupSequence S₀, s'.IsWeakEmbeddedResolution C₀ →
      s.length < s'.length →
      ¬ ((∀ i : ℕ, (i : ℕ∞) ≤ s.length → s'.S i = s.S i) ∧ HEq s'.zeroIso s.zeroIso ∧
        (∀ i : ℕ, (i : ℕ∞) < s.length → HEq (s'.p i) (s.p i)) ∧
        ∀ (i : ℕ) (hi : (i : ℕ∞) < s.length) (hi' : (i : ℕ∞) < s'.length),
          HEq (s'.blowupIso i hi') (s.blowupIso i hi))) :
    s.WeakEmbeddedResolutionStops C₀ ∧
      ∃ (n : ℕ) (hn : s.length = n),
        Smooth ((s.transformedSubscheme C₀ n).subschemeι ≫ s.π n hn.ge ≫ sS) := by
  have hstops : s.WeakEmbeddedResolutionStops C₀ := by
    obtain hne | hne := (C₀.support : Set S₀).eq_empty_or_nonempty
    · exact weakEmbeddedResolutionStops_of_support_eq_empty hne hs
    have : Nonempty S₀ := ⟨hne.some⟩
    exact (PointBlowupSequence.length_le_ncard_and_stops_of_finite
      (isRegularSurface_of_smoothOfRelativeDimension sS) C₀ inferInstance
      (topologicalKrullDim_subscheme_eq_one sS C₀ hC hne) (finite_chains sS C₀ hC)).2 s hs hmax
  obtain ⟨n, hn, hreg⟩ := hstops
  refine ⟨⟨n, hn, hreg⟩, n, hn, ?_⟩
  obtain ⟨_, _⟩ := smoothOfRelativeDimension_π_comp sS s n hn.ge
  have : Smooth (s.π n hn.ge ≫ sS) := SmoothOfRelativeDimension.smooth 2 _
  exact smooth_subschemeι_comp (s.π n hn.ge ≫ sS) _ hreg

end PointBlowupSequence

/-! ### Radicals of principal ideals in a factorial ring -/

/-- In a unique factorization domain the radical of a nonzero principal ideal is principal,
generated by a nonzero element. -/
private theorem exists_radical_span_singleton_eq {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] {a : R} (ha : a ≠ 0) :
    ∃ g : R, g ≠ 0 ∧ (Ideal.span {a}).radical = Ideal.span {g} := by
  classical
  let : NormalizationMonoid R :=
    UniqueFactorizationMonoid.strongNormalizationMonoid.toNormalizationMonoid
  refine ⟨UniqueFactorizationMonoid.radical a, UniqueFactorizationMonoid.radical_ne_zero, ?_⟩
  ext x
  rw [Ideal.mem_radical_iff, Ideal.mem_span_singleton]
  simp only [Ideal.mem_span_singleton]
  exact UniqueFactorizationMonoid.exists_dvd_pow_iff_radical_dvd ha

/-! ### Simple normal crossings are read off the stalk -/

/-- A closed subscheme has simple normal crossings at `x` as soon as its stalk at `x` is
generated by a monomial in a regular system of parameters of `𝒪_{X,x}`. -/
private theorem hasSNCAt_of_stalk_eq_span_prod {X : Scheme.{u}} [IsLocallyNoetherian X]
    (D : X.IdealSheafData) (x : X) {N : ℕ} {w : Fin N → X.presheaf.stalk x}
    (hw : MMP.Mori.IsRegularSystemOfParameters w) (m : Fin N → ℕ)
    (h : IdealSheafData.stalk D x = Ideal.span {∏ c, w c ^ m c}) : HasSNCAt D x := by
  classical
  choose V hV t ht using fun c => X.presheaf.exists_germ_eq (x := x) (w c)
  let W : X.Opens := Finset.univ.inf V
  have hxW : x ∈ W := by
    change x ∈ ((Finset.univ.inf V : X.Opens) : Set X)
    rw [TopologicalSpace.Opens.coe_finset_inf, Finset.inf_eq_iInf]
    exact Set.mem_iInter₂.2 fun c _ => hV c
  have hWV : ∀ c, W ≤ V c := fun c => Finset.inf_le (Finset.mem_univ c)
  let t' : Fin N → Γ(X, W) := fun c => (X.presheaf.map (homOfLE (hWV c)).op).hom (t c)
  have ht' : ∀ c (y : X) (hy : y ∈ W), (X.presheaf.germ W y hy).hom (t' c) =
      (X.presheaf.germ (V c) y (hWV c hy)).hom (t c) := fun c y hy =>
    X.presheaf.germ_res_apply (homOfLE (hWV c)) y hy (t c)
  let g : Γ(X, W) := ∏ c, t' c ^ m c
  have hg : (X.presheaf.germ W x hxW).hom g = ∏ c, w c ^ m c := by
    simp only [g, map_prod, map_pow, ht', ht]
  obtain ⟨U, hUW, hxU, hU⟩ := MMP.Flips.ResolutionInputs.exists_ideal_eq_span_of_stalk_eq D hxW
    (fun _ : Unit => g) (by rw [Set.range_const, hg, h])
  let r : Fin N → Γ(X, U) := fun c => (X.presheaf.map (homOfLE hUW).op).hom (t' c)
  have hr : ∀ c (y : X) (hy : y ∈ U), (X.presheaf.germ U y hy).hom (r c) =
      (X.presheaf.germ W y (hUW hy)).hom (t' c) := fun c y hy =>
    X.presheaf.germ_res_apply (homOfLE hUW) y hy (t' c)
  refine ⟨N, U, hxU, r, m, ?_, fun y hy => ?_⟩
  · convert hw using 1
    funext c
    rw [hr, ht', ht]
  · obtain ⟨W', hW', hyW', hW'U⟩ := exists_isAffineOpen_mem_and_subset hy
    rw [IdealSheafData.stalk_eq_map_germ D y ⟨W', hW'⟩ hyW', hU ⟨W', hW'⟩ hW'U, Ideal.map_span,
      Set.range_const, Set.image_singleton]
    congr 2
    have h1 : (X.presheaf.germ W' y hyW').hom (restrictSection ⟨W', hW'⟩ (hW'U.trans hUW) g) =
        (X.presheaf.germ W y (hUW hy)).hom g :=
      X.presheaf.germ_res_apply (homOfLE (hW'U.trans hUW)) y hyW' g
    rw [h1]
    simp only [g, map_prod, map_pow, hr]

/-- Simple normal crossings at `x` are a condition on the stalk at `x`: the stalk is generated
by a monomial in a regular system of parameters. -/
private theorem hasSNCAt_iff {X : Scheme.{u}} [IsLocallyNoetherian X] (D : X.IdealSheafData)
    (x : X) : HasSNCAt D x ↔ ∃ (N : ℕ) (w : Fin N → X.presheaf.stalk x) (m : Fin N → ℕ),
      MMP.Mori.IsRegularSystemOfParameters w ∧
        IdealSheafData.stalk D x = Ideal.span {∏ c, w c ^ m c} := by
  refine ⟨fun ⟨d, U, hU, s, m, hreg, hst⟩ => ⟨d, _, m, hreg, ?_⟩,
    fun ⟨N, w, m, hw, h⟩ => hasSNCAt_of_stalk_eq_span_prod D x hw m h⟩
  simp only [hst x hU, map_prod, map_pow]

/-- Simple normal crossings at `x` only depend on the stalk at `x`. -/
private theorem hasSNCAt_congr {X : Scheme.{u}} [IsLocallyNoetherian X] {D D' : X.IdealSheafData}
    {x : X} (h : IdealSheafData.stalk D x = IdealSheafData.stalk D' x) :
    HasSNCAt D x ↔ HasSNCAt D' x := by
  rw [hasSNCAt_iff, hasSNCAt_iff, h]

/-- Along an open immersion, the inverse image of the reduced structure on a closed set is the
reduced structure on its preimage. -/
private theorem comap_vanishingIdeal {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (C : TopologicalSpace.Closeds Y) :
    (Scheme.IdealSheafData.vanishingIdeal C).comap f =
      Scheme.IdealSheafData.vanishingIdeal ⟨f ⁻¹' C, C.isClosed.preimage f.continuous⟩ := by
  set J := Scheme.IdealSheafData.vanishingIdeal C
  have : IsReduced (J.comap f).subscheme :=
    isReduced_of_isOpenImmersion ((J.comapIso f).hom ≫ Limits.pullback.snd f J.subschemeι)
  refine Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ ?_
  rw [Scheme.IdealSheafData.support_comap]
  ext1
  simp [J]

/-- Simple normal crossings of a reduced closed subscheme are transported along an
isomorphism. -/
private theorem isSNCSubscheme_vanishingIdeal_preimage {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (e : X ≅ Y) (Z : TopologicalSpace.Closeds Y)
    (hZ : IsSNCSubscheme (Scheme.IdealSheafData.vanishingIdeal Z)) :
    IsSNCSubscheme (Scheme.IdealSheafData.vanishingIdeal
      ⟨e.hom ⁻¹' Z, Z.isClosed.preimage e.hom.continuous⟩) := by
  intro q hq
  have hcl : IsClosed ({e.hom q} : Set Y) := by
    have := e.hom.isClosedEmbedding.isClosedMap _ hq
    rwa [Set.image_singleton] at this
  obtain ⟨N, w, m, hw, h⟩ := (hasSNCAt_iff _ _).1 (hZ _ hcl)
  rw [← comap_vanishingIdeal, hasSNCAt_iff]
  have : IsIso (e.hom.stalkMap q) := IsOpenImmersion.instIsIsoCommRingCatStalkMap e.hom q
  let φ := (asIso (e.hom.stalkMap q)).commRingCatIsoToRingEquiv
  refine ⟨N, fun c => φ (w c), m, hw.map_ringEquiv φ, ?_⟩
  rw [IdealSheafData.stalk_comap, h, Ideal.map_span, Set.image_singleton, map_prod]
  simp only [map_pow]
  rfl

/-- On a regular surface, the reduced structure on the support of a regular effective Cartier
divisor has simple normal crossings at every closed point. -/
private theorem hasSNCAt_vanishingIdeal_support_of_isRegularLocalRing {X : Scheme.{u}}
    (hX : IsRegularSurface X) (Γ : X.IdealSheafData)
    (hΓ : Stacks.Divisors.IsEffectiveCartierDivisor Γ) {x : X} (hx : IsClosed ({x} : Set X))
    (hreg : x ∈ Γ.support →
      IsRegularLocalRing (X.presheaf.stalk x ⧸ IdealSheafData.stalk Γ x)) :
    HasSNCAt (Scheme.IdealSheafData.vanishingIdeal Γ.support) x := by
  have : IsLocallyNoetherian X := hX.1.toIsLocallyNoetherian
  have := hX.2.1 x
  by_cases hxΓ : x ∈ Γ.support
  swap
  · refine hasSNCAt_of_notMem_support _ ?_
    rwa [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hq := hreg hxΓ
  obtain ⟨g, hg, hspan⟩ := MMP.Resolution.Kr1c.hasPrincipalStalks_of_isEffectiveCartierDivisor hΓ x
  have hg0 : g ≠ 0 := nonZeroDivisors.ne_zero hg
  have hgm : g ∈ maximalIdeal (X.presheaf.stalk x) := by
    have hne : IdealSheafData.stalk Γ x ≠ ⊤ := fun h =>
      ((IdealSheafData.stalk_eq_top_iff_notMem_support Γ x).1 h) hxΓ
    rw [hspan, Ne, Ideal.span_singleton_eq_top] at hne
    exact (mem_maximalIdeal g).mpr hne
  rw [hspan] at hq
  have hdim := (MMP.Resolution.ringKrullDim_quotient_span_singleton_eq_one_and_not_isFiniteLength
    (hX.2.2 x hx) hg0 hgm).1
  have hrange : Set.range ![g] = {g} := by simp
  obtain ⟨m, t, ht⟩ := (MMP.Flips.ResolutionInputs.isRegularLocalRing_quotient_and_add_eq_iff
    ![g]).1 ⟨by rwa [hrange], by rw [hrange, hdim, hX.2.2 x hx]; rfl⟩
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk x ⧸ Ideal.span {g})
  have hprime : (Ideal.span {g}).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).1 this
  refine (hasSNCAt_iff _ x).2 ⟨1 + m, Fin.append ![g] t, Fin.append ![1] 0, ht, ?_⟩
  rw [Scheme.IdealSheafData.vanishingIdeal_support, MMP.Resolution.stalk_radical, hspan,
    hprime.isRadical.radical, Fin.prod_univ_add]
  simp

/-! ### Effective Cartier divisors on regular surfaces -/

/-- On a locally Noetherian scheme with regular local rings, the reduced structure on the
support of an effective Cartier divisor is an effective Cartier divisor: in the factorial local
rings, the radical of a nonzero principal ideal is principal. -/
private theorem isEffectiveCartierDivisor_vanishingIdeal_support {X : Scheme.{u}}
    [IsLocallyNoetherian X] (hX : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    {J : X.IdealSheafData} (hJ : Stacks.Divisors.IsEffectiveCartierDivisor J) :
    Stacks.Divisors.IsEffectiveCartierDivisor
      (Scheme.IdealSheafData.vanishingIdeal J.support) := by
  refine Stacks.Divisors.isEffectiveCartierDivisor_of_stalk_isPrincipal_nonZeroDivisor _
    fun x _ => ?_
  have := hX x
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk x)
  have := IsRegularLocalRing.uniqueFactorizationMonoid (X.presheaf.stalk x)
  obtain ⟨a, ha, hspan⟩ := MMP.Resolution.Kr1c.hasPrincipalStalks_of_isEffectiveCartierDivisor hJ x
  obtain ⟨g, hg, hrad⟩ := exists_radical_span_singleton_eq (nonZeroDivisors.ne_zero ha)
  refine ⟨g, mem_nonZeroDivisors_of_ne_zero hg, ?_⟩
  rw [Scheme.IdealSheafData.vanishingIdeal_support, MMP.Resolution.stalk_radical, hspan, hrad]

/-- The inverse image of an effective Cartier divisor under a blow-up which is smooth over a
field is an effective Cartier divisor: the pulled-back local equation does not vanish at the
points off the exceptional divisor, which specialize to every point. -/
private theorem isEffectiveCartierDivisor_comap_blowUpToBase {k : Type u} [Field k]
    {W : Scheme.{u}} (I : W.IdealSheafData) {C : W.IdealSheafData}
    (hC : Stacks.Divisors.IsEffectiveCartierDivisor C) (f : blowUp I ⟶ Spec (.of k)) [Smooth f] :
    Stacks.Divisors.IsEffectiveCartierDivisor (C.comap (blowUpToBase I)) := by
  have : IsLocallyNoetherian (blowUp I) := LocallyOfFiniteType.isLocallyNoetherian f
  refine Stacks.Divisors.isEffectiveCartierDivisor_of_stalk_isPrincipal_nonZeroDivisor _
    fun y _ => ?_
  have := isRegularLocalRing_stalk_of_smooth_over_field f y
  have := IsRegularLocalRing.isDomain ((blowUp I).presheaf.stalk y)
  obtain ⟨U, hU, hyU, a, ha, hgen⟩ :=
    Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor C hC
      (blowUpToBase I y)
  refine ⟨((blowUp I).presheaf.germ (blowUpToBase I ⁻¹ᵁ U) y hyU).hom
    ((blowUpToBase I).app U |>.hom a), ?_, ?_⟩
  · refine mem_nonZeroDivisors_of_ne_zero fun h0 => ?_
    obtain ⟨η, hηy, hηE⟩ := exists_specializes_notMem_support_exceptionalIdeal I f y
    have hηU : η ∈ blowUpToBase I ⁻¹ᵁ U := hηy.mem_open (blowUpToBase I ⁻¹ᵁ U).isOpen hyU
    have h1 : ((blowUp I).presheaf.germ (blowUpToBase I ⁻¹ᵁ U) η hηU).hom
        ((blowUpToBase I).app U |>.hom a) = 0 := by
      rw [← TopCat.Presheaf.germ_stalkSpecializes_apply (F := (blowUp I).presheaf)
        (U := blowUpToBase I ⁻¹ᵁ U) hyU hηy, h0, map_zero]
    have hiso : IsIso ((blowUpToBase I).stalkMap η) :=
      isIso_stalkMap_of_isIso_morphismRestrict (blowUpToBase I)
        (isIso_blowUp_restrict_compl_support I) (x := η) (by
          change blowUpToBase I η ∉ (I.support : Set W)
          intro h
          exact hηE ((MMP.Resolution.Kr1c.mem_support_comap_iff _ _ _).2 h))
    rw [← Scheme.Hom.germ_stalkMap_apply (blowUpToBase I) U η hηU] at h1
    have h2 : (W.presheaf.germ U (blowUpToBase I η) hηU).hom a = 0 :=
      (ConcreteCategory.injective_of_mono_of_preservesPullback
        ((blowUpToBase I).stalkMap η)) (by rw [h1, map_zero])
    exact nonZeroDivisors.ne_zero
      (Stacks.Divisors.germ_mem_nonZeroDivisors hU ha (blowUpToBase I η) hηU) h2
  · rw [IdealSheafData.stalk_comap, IdealSheafData.stalk_eq_map_germ C _ ⟨U, hU⟩ hyU, hgen,
      Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton,
      Scheme.Hom.germ_stalkMap_apply]

/-! ### Sequences of point blow-ups of a smooth surface -/

section Sequence

variable {X : Scheme.{u}} (s : PointBlowupSequence X)

/-- `π_{i+1} = φ_i ≫ σ ≫ π_i`, with `φ_i : S_{i+1} ≅ B_{p_i}S_i` and `σ` the blow-up morphism. -/
private theorem π_succ (i : ℕ) (hi : ((i + 1 : ℕ) : ℕ∞) ≤ s.length) :
    s.π (i + 1) hi = (s.blowupIso i (PointBlowupSequence.coe_lt_of_succ_le hi)).hom ≫
      blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
        ⟨{s.p i}, s.isClosed_p i (PointBlowupSequence.coe_lt_of_succ_le hi)⟩) ≫
      s.π i (PointBlowupSequence.coe_lt_of_succ_le hi).le := by
  simp only [PointBlowupSequence.π, PointBlowupSequence.σ, Category.assoc]

variable {k : Type u} [Field k] [PerfectField k] (sS : X ⟶ Spec (.of k))
  [SmoothOfRelativeDimension 2 sS] [QuasiCompact sS]

include sS in
/-- The inverse image of an effective Cartier divisor under `π_i` is an effective Cartier
divisor. -/
private theorem isEffectiveCartierDivisor_comap_π {C : X.IdealSheafData}
    (hC : Stacks.Divisors.IsEffectiveCartierDivisor C) :
    ∀ (i : ℕ) (hi : (i : ℕ∞) ≤ s.length),
      Stacks.Divisors.IsEffectiveCartierDivisor (C.comap (s.π i hi))
  | 0, _ => Stacks.Blowup.isEffectiveCartierDivisor_comap_of_isOpenImmersion C hC s.zeroIso.hom
  | i + 1, hi => by
    have hlt := PointBlowupSequence.coe_lt_of_succ_le hi
    obtain ⟨_, _⟩ := smoothOfRelativeDimension_π_comp sS s i hlt.le
    obtain ⟨h1, -⟩ := smoothOfRelativeDimension_blowUpToBase_comp (s.π i hlt.le ≫ sS)
      (s.isClosed_p i hlt)
    have : Smooth (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
        ⟨{s.p i}, s.isClosed_p i hlt⟩) ≫ s.π i hlt.le ≫ sS) := SmoothOfRelativeDimension.smooth 2 _
    rw [π_succ, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp]
    exact Stacks.Blowup.isEffectiveCartierDivisor_comap_of_isOpenImmersion _
      (isEffectiveCartierDivisor_comap_blowUpToBase _
        (isEffectiveCartierDivisor_comap_π hC i hlt.le)
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
          ⟨{s.p i}, s.isClosed_p i hlt⟩) ≫ s.π i hlt.le ≫ sS)) _

omit [PerfectField k] in
include sS in
/-- The birational transforms of an effective Cartier divisor are effective Cartier
divisors. -/
private theorem isEffectiveCartierDivisor_transformedSubscheme {C : X.IdealSheafData}
    (hC : Stacks.Divisors.IsEffectiveCartierDivisor C) :
    ∀ (i : ℕ), (i : ℕ∞) ≤ s.length →
      Stacks.Divisors.IsEffectiveCartierDivisor (s.transformedSubscheme C i)
  | 0, _ => Stacks.Blowup.isEffectiveCartierDivisor_comap_of_isOpenImmersion C hC s.zeroIso.hom
  | i + 1, hi => by
    have hX := isRegularSurface_of_smoothOfRelativeDimension sS
    have hlt := PointBlowupSequence.coe_lt_of_succ_le hi
    rw [PointBlowupSequence.transformedSubscheme, dite_eq_left hlt]
    exact Stacks.Blowup.isEffectiveCartierDivisor_comap_of_isOpenImmersion _
      (isEffectiveCartierDivisor_birationalTransform (isRegularSurface_S hX s i hlt.le) _
        (isEffectiveCartierDivisor_transformedSubscheme hC i hlt.le)) _

end Sequence

/-! ### Composites of point blow-ups -/

/-- Precomposing a composite of `n` point blow-ups with an isomorphism gives a composite of `n`
point blow-ups. -/
private theorem isCompositeOfPointBlowupsOfLength_iso_comp :
    ∀ (n : ℕ) {S' T S : Scheme.{u}} (e : S' ⟶ T) [IsIso e] {g : T ⟶ S},
      IsCompositeOfPointBlowupsOfLength n g → IsCompositeOfPointBlowupsOfLength n (e ≫ g)
  | 0, _, _, _, e, _, g, hg => by
    have : IsIso g := hg
    change IsIso (e ≫ g)
    infer_instance
  | n + 1, _, _, _, e, _, g, hg => by
    obtain ⟨W, h, w, hw, hh, φ, rfl⟩ := hg
    refine ⟨W, h, w, hw, hh, asIso e ≪≫ φ, ?_⟩
    rw [Iso.trans_hom, asIso_hom, Category.assoc]

/-- If `g` is a composite of `n` point blow-ups and `h` one of `r` point blow-ups, then `h ≫ g`
is a composite of `n + r` point blow-ups. -/
private theorem isCompositeOfPointBlowupsOfLength_comp (n : ℕ) :
    ∀ (r : ℕ) {S' T S : Scheme.{u}} {h : S' ⟶ T} {g : T ⟶ S},
      IsCompositeOfPointBlowupsOfLength n g → IsCompositeOfPointBlowupsOfLength r h →
        IsCompositeOfPointBlowupsOfLength (n + r) (h ≫ g)
  | 0, _, _, _, h, g, hg, hh => by
    have : IsIso h := hh
    exact isCompositeOfPointBlowupsOfLength_iso_comp n h hg
  | r + 1, _, _, _, h, g, hg, hh => by
    obtain ⟨W, h', w, hw, hh', φ, rfl⟩ := hh
    refine ⟨W, h' ≫ g, w, hw, isCompositeOfPointBlowupsOfLength_comp n r hg hh', φ, ?_⟩
    simp only [Category.assoc]

/-! ### Strict transforms of closed sets -/

/-- `b⁻¹(T ∪ F) ∪ E = closure (b⁻¹ T ∖ E) ∪ (b⁻¹ F ∪ E)` for `T` closed. -/
private theorem preimage_union_union_eq {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (b : α → β) (hb : Continuous b) (E : Set α) {T F : Set β} (hT : IsClosed T) :
    b ⁻¹' (T ∪ F) ∪ E = closure (b ⁻¹' T \ E) ∪ (b ⁻¹' F ∪ E) := by
  apply Set.Subset.antisymm
  · rintro x ((hx | hx) | hx)
    · by_cases hxE : x ∈ E
      · exact Or.inr (Or.inr hxE)
      · exact Or.inl (subset_closure ⟨hx, hxE⟩)
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr hx)
  · rintro x (hx | hx | hx)
    · exact Or.inl (Or.inl (closure_minimal Set.sdiff_subset (hT.preimage hb) hx))
    · exact Or.inl (Or.inr hx)
    · exact Or.inr hx

/-- If `E = b⁻¹(p)`, `T` is closed and `p ∈ T ∪ F`, then
`b⁻¹(T ∪ F) = closure (b⁻¹ T ∖ E) ∪ (b⁻¹ F ∪ E)`. -/
private theorem preimage_union_eq {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (b : α → β) (hb : Continuous b) {p : β} {E : Set α} (hE : E = b ⁻¹' {p}) {T F : Set β}
    (hT : IsClosed T) (hp : p ∈ T ∪ F) :
    b ⁻¹' (T ∪ F) = closure (b ⁻¹' T \ E) ∪ (b ⁻¹' F ∪ E) := by
  rw [← preimage_union_union_eq b hb E hT, eq_comm, Set.union_eq_left, hE]
  intro x hx
  rwa [Set.mem_preimage, Set.mem_singleton_iff.1 hx]

/-- The support of the birational transform of `T` in the blow-up of a closed point `p` of a
Noetherian scheme is the closure of `π⁻¹(T) ∖ E`. -/
private theorem support_birationalTransform {S : Scheme.{u}} [IsNoetherian S] {p : S}
    (hp : IsClosed ({p} : Set S)) (T : S.IdealSheafData) :
    ((birationalTransform p hp T).support :
      Set (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))) =
      closure (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ⁻¹'
        (T.support : Set S) \
          (exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).support) := by
  have : IsNoetherian (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) :=
    Stacks.ResolutionOfSurfaces.isNoetherian_blowUp _
  set q := Limits.pullback.snd T.subschemeι
    (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))
  set U := q ⁻¹ᵁ (exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).support.compl
  have : TopologicalSpace.NoetherianSpace U.toScheme :=
    (q.isClosedEmbedding.isInducing.comp U.ι.isOpenEmbedding.isInducing).noetherianSpace
  rw [birationalTransform, Scheme.Hom.support_ker]
  congr 1
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
    Scheme.Hom.coe_preimage, Set.image_preimage_eq_inter_range, Scheme.Pullback.range_snd,
    Scheme.IdealSheafData.range_subschemeι, Set.sdiff_eq, Set.inter_comm]
  rfl

/-- Snc of reduced closed subschemes only depends on the underlying closed set. -/
private theorem isSNCSubscheme_vanishingIdeal_congr {X : Scheme.{u}}
    {Z Z' : TopologicalSpace.Closeds X} (h : (Z : Set X) = Z')
    (hZ : IsSNCSubscheme (Scheme.IdealSheafData.vanishingIdeal Z)) :
    IsSNCSubscheme (Scheme.IdealSheafData.vanishingIdeal Z') := by
  rwa [← TopologicalSpace.Closeds.ext h]

section Transform

variable {X : Scheme.{u}} (s : PointBlowupSequence X)

open Classical in
/-- The strict transforms `A_i ⊆ S_i` of a set `A ⊆ X`: `A_0 = A` on `S_0 ≅ X`, and `A_{i+1}` is
the closure of the inverse image of `A_i` off the exceptional curve of `S_{i+1} → S_i`. -/
private noncomputable def strictSet (A : Set X) : ∀ i : ℕ, Set (s.S i)
  | 0 => s.zeroIso.hom ⁻¹' A
  | i + 1 =>
    if hi : (i : ℕ∞) < s.length then
      (s.blowupIso i hi).hom ⁻¹' closure
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{s.p i}, s.isClosed_p i hi⟩) ⁻¹'
            strictSet A i \
          (exceptionalIdeal
            (Scheme.IdealSheafData.vanishingIdeal ⟨{s.p i}, s.isClosed_p i hi⟩)).support)
    else ∅

open Classical in
/-- The exceptional sets `F_i ⊆ S_i` of `S_i → S_0`: `F_0 = ∅`, and `F_{i+1}` is the inverse
image of `F_i` together with the exceptional curve of `S_{i+1} → S_i`. -/
private noncomputable def excSet : ∀ i : ℕ, Set (s.S i)
  | 0 => ∅
  | i + 1 =>
    if hi : (i : ℕ∞) < s.length then
      (s.blowupIso i hi).hom ⁻¹'
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{s.p i}, s.isClosed_p i hi⟩) ⁻¹'
            excSet i ∪
          (exceptionalIdeal
            (Scheme.IdealSheafData.vanishingIdeal ⟨{s.p i}, s.isClosed_p i hi⟩)).support)
    else ∅

private theorem strictSet_succ (A : Set X) (i : ℕ) (hi : (i : ℕ∞) < s.length) :
    strictSet s A (i + 1) = (s.blowupIso i hi).hom ⁻¹' closure
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{s.p i}, s.isClosed_p i hi⟩) ⁻¹'
          strictSet s A i \
        (exceptionalIdeal
          (Scheme.IdealSheafData.vanishingIdeal ⟨{s.p i}, s.isClosed_p i hi⟩)).support) := by
  rw [strictSet, dite_eq_left hi]

private theorem excSet_succ (i : ℕ) (hi : (i : ℕ∞) < s.length) :
    excSet s (i + 1) = (s.blowupIso i hi).hom ⁻¹'
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{s.p i}, s.isClosed_p i hi⟩) ⁻¹'
          excSet s i ∪
        (exceptionalIdeal
          (Scheme.IdealSheafData.vanishingIdeal ⟨{s.p i}, s.isClosed_p i hi⟩)).support) := by
  rw [excSet, dite_eq_left hi]

private theorem isClosed_strictSet {A : Set X} (hA : IsClosed A) :
    ∀ i : ℕ, IsClosed (strictSet s A i)
  | 0 => hA.preimage s.zeroIso.hom.continuous
  | i + 1 => by
    by_cases hi : (i : ℕ∞) < s.length
    · rw [strictSet_succ s A i hi]
      exact isClosed_closure.preimage (s.blowupIso i hi).hom.continuous
    · rw [strictSet, dite_eq_right hi]
      exact isClosed_empty

private theorem isClosed_excSet : ∀ i : ℕ, IsClosed (excSet s i)
  | 0 => isClosed_empty
  | i + 1 => by
    by_cases hi : (i : ℕ∞) < s.length
    · rw [excSet_succ s i hi]
      exact (((isClosed_excSet i).preimage (blowUpToBase _).continuous).union
        (exceptionalIdeal _).support.isClosed).preimage (s.blowupIso i hi).hom.continuous
    · rw [excSet, dite_eq_right hi]
      exact isClosed_empty

private theorem strictSet_union (A B : Set X) :
    ∀ i : ℕ, strictSet s (A ∪ B) i = strictSet s A i ∪ strictSet s B i
  | 0 => Set.preimage_union
  | i + 1 => by
    by_cases hi : (i : ℕ∞) < s.length
    · rw [strictSet_succ s _ i hi, strictSet_succ s _ i hi, strictSet_succ s _ i hi,
        strictSet_union A B i, Set.preimage_union, Set.union_sdiff_distrib, closure_union,
        Set.preimage_union]
    · rw [strictSet, dite_eq_right hi, strictSet, dite_eq_right hi, strictSet, dite_eq_right hi,
        Set.union_empty]

private theorem strictSet_empty : ∀ i : ℕ, strictSet s ∅ i = ∅
  | 0 => Set.preimage_empty
  | i + 1 => by
    by_cases hi : (i : ℕ∞) < s.length
    · rw [strictSet_succ s _ i hi, strictSet_empty i, Set.preimage_empty, Set.empty_sdiff,
        closure_empty, Set.preimage_empty]
    · rw [strictSet, dite_eq_right hi]

variable {k : Type u} [Field k] (sS : X ⟶ Spec (.of k))
  [SmoothOfRelativeDimension 2 sS] [QuasiCompact sS]

include sS in
/-- The support of the `i`-th birational transform of `C` is the strict transform of the support
of `C`. -/
private theorem coe_support_transformedSubscheme (C : X.IdealSheafData) :
    ∀ (i : ℕ) (_ : (i : ℕ∞) ≤ s.length),
      ((s.transformedSubscheme C i).support : Set (s.S i)) = strictSet s C.support i
  | 0, _ => by
    rw [PointBlowupSequence.transformedSubscheme, Scheme.IdealSheafData.support_comap]
    rfl
  | i + 1, hi => by
    have hX := isRegularSurface_of_smoothOfRelativeDimension sS
    have hlt := PointBlowupSequence.coe_lt_of_succ_le hi
    have : IsNoetherian (s.S i) := (isRegularSurface_S hX s i hlt.le).1
    rw [PointBlowupSequence.transformedSubscheme, dite_eq_left hlt,
      Scheme.IdealSheafData.support_comap,
      strictSet_succ s _ i hlt, ← coe_support_transformedSubscheme C i hlt.le,
      ← support_birationalTransform]
    rfl

include sS in
/-- The centres of a weak embedded resolution sequence of `D` lie on the strict transforms of
the support of `D`. -/
private theorem p_mem_strictSet {D : X.IdealSheafData} (hs : s.IsWeakEmbeddedResolution D)
    (j : ℕ) (hj : (j : ℕ∞) < s.length) : s.p j ∈ strictSet s D.support j := by
  rw [← coe_support_transformedSubscheme s sS D j hj.le]
  exact (hs j hj).1

/-- If the centres lie on the strict transforms of a closed set `A`, the inverse image of `A`
under `π_i` is the strict transform of `A` together with the exceptional set. -/
private theorem preimage_π {A : Set X} (hA : IsClosed A) :
    ∀ (i : ℕ) (hi : (i : ℕ∞) ≤ s.length), (∀ j < i, s.p j ∈ strictSet s A j) →
      s.π i hi ⁻¹' A = strictSet s A i ∪ excSet s i
  | 0, _, _ => by
    rw [excSet, Set.union_empty]
    rfl
  | i + 1, hi, hp => by
    have hlt := PointBlowupSequence.coe_lt_of_succ_le hi
    rw [π_succ, strictSet_succ s A i hlt, excSet_succ s i hlt, ← Set.preimage_union]
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp, Scheme.Hom.comp_base,
      TopCat.coe_comp, Set.preimage_comp]
    congr 1
    have ih := preimage_π hA i hlt.le fun j hj => hp j (Nat.lt_succ_of_lt hj)
    rw [ih]
    exact preimage_union_eq _ (blowUpToBase _).continuous
      (Set.ext (MMP.Resolution.Kr1c.mem_support_exceptionalIdeal_iff _ (s.isClosed_p i hlt)))
      (isClosed_strictSet s hA i)
      (Or.inl (hp i (Nat.lt_succ_self i)))

include sS in
/-- If the reduced structure on a closed set `A ⊆ X` is snc, so is the reduced structure on
`A_i ∪ F_i ⊆ S_i`, the strict transform of `A` together with the exceptional set. -/
private theorem isSNCSubscheme_strictSet_union_excSet {A : Set X} (hA : IsClosed A)
    (hsnc : IsSNCSubscheme (Scheme.IdealSheafData.vanishingIdeal ⟨A, hA⟩)) :
    ∀ (i : ℕ) (_ : (i : ℕ∞) ≤ s.length),
      IsSNCSubscheme (Scheme.IdealSheafData.vanishingIdeal
        ⟨strictSet s A i ∪ excSet s i, (isClosed_strictSet s hA i).union (isClosed_excSet s i)⟩)
  | 0, h0 => by
    have hX := isRegularSurface_of_smoothOfRelativeDimension sS
    have : IsLocallyNoetherian (s.S 0) :=
      (isRegularSurface_S hX s 0 h0).1.toIsLocallyNoetherian
    have : IsLocallyNoetherian X := hX.1.toIsLocallyNoetherian
    refine isSNCSubscheme_vanishingIdeal_congr ?_
      (isSNCSubscheme_vanishingIdeal_preimage s.zeroIso ⟨A, hA⟩ hsnc)
    change s.zeroIso.hom ⁻¹' A = s.zeroIso.hom ⁻¹' A ∪ ∅
    rw [Set.union_empty]
  | i + 1, hi => by
    have hX := isRegularSurface_of_smoothOfRelativeDimension sS
    have hlt := PointBlowupSequence.coe_lt_of_succ_le hi
    have hS := isRegularSurface_S hX s i hlt.le
    have : IsLocallyNoetherian (s.S (i + 1)) :=
      (isRegularSurface_S hX s (i + 1) hi).1.toIsLocallyNoetherian
    obtain ⟨hB, hZ'⟩ := isSNCSubscheme_vanishingIdeal_preimage_union_exceptional hS
      ⟨strictSet s A i ∪ excSet s i, (isClosed_strictSet s hA i).union (isClosed_excSet s i)⟩
      (isSNCSubscheme_strictSet_union_excSet hA hsnc i hlt.le) (s.p i) (s.isClosed_p i hlt)
      ⟨_, ((((isClosed_strictSet s hA i).union (isClosed_excSet s i)).preimage
        (blowUpToBase _).continuous).union (exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal
          ⟨{s.p i}, s.isClosed_p i hlt⟩)).support.isClosed)⟩ rfl
    have : IsLocallyNoetherian
        (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{s.p i}, s.isClosed_p i hlt⟩)) :=
      hB.1.toIsLocallyNoetherian
    refine isSNCSubscheme_vanishingIdeal_congr ?_
      (isSNCSubscheme_vanishingIdeal_preimage (s.blowupIso i hlt) _ hZ')
    change _ = strictSet s A (i + 1) ∪ excSet s (i + 1)
    rw [strictSet_succ s A i hlt, excSet_succ s i hlt, ← Set.preimage_union,
      ← preimage_union_union_eq _ (blowUpToBase _).continuous _ (isClosed_strictSet s hA i)]
    rfl

include sS in
/-- The reduced structure on the exceptional set `F_i ⊆ S_i` is snc: the case `A = ∅` of
`isSNCSubscheme_strictSet_union_excSet`. -/
private theorem isSNCSubscheme_excSet (i : ℕ) (hi : (i : ℕ∞) ≤ s.length) :
    IsSNCSubscheme (Scheme.IdealSheafData.vanishingIdeal ⟨excSet s i, isClosed_excSet s i⟩) := by
  have hX := isRegularSurface_of_smoothOfRelativeDimension sS
  have : IsLocallyNoetherian X := hX.1.toIsLocallyNoetherian
  refine isSNCSubscheme_vanishingIdeal_congr ?_
    (isSNCSubscheme_strictSet_union_excSet s sS isClosed_empty (fun p _ => ?_) i hi)
  · change strictSet s ∅ i ∪ excSet s i = excSet s i
    rw [strictSet_empty, Set.empty_union]
  · have := hX.2.1 p
    refine hasSNCAt_of_notMem_support _ fun h => ?_
    rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal] at h
    exact Set.notMem_empty p h

end Transform

/-! ### Weak embedded resolution sequences that stop -/

section Stopping

/-- The sequence of point blow-ups of length `0` of a nonempty scheme. -/
private noncomputable def trivialSeq (T : Scheme.{u}) [Nonempty T] : PointBlowupSequence T where
  length := 0
  S := fun _ => T
  zeroIso := Iso.refl T
  p := fun _ => Classical.arbitrary T
  isClosed_p := fun _ hi => by simp at hi
  blowupIso := fun _ hi => by simp at hi

/-- The schemes of `prepend`: `T`, followed by those of `s'`. -/
private def prependS (T : Scheme.{u}) (S' : ℕ → Scheme.{u}) : ℕ → Scheme.{u}
  | 0 => T
  | i + 1 => S' i

private theorem coe_lt_of_succ_lt_add_one {j : ℕ} {n : ℕ∞} (h : ((j + 1 : ℕ) : ℕ∞) < n + 1) :
    (j : ℕ∞) < n := by
  rw [Nat.cast_succ] at h
  exact (ENat.add_lt_add_iff_right ENat.one_ne_top).1 h

private theorem succ_lt_add_one {j : ℕ} {n : ℕ∞} (h : (j : ℕ∞) < n) :
    ((j + 1 : ℕ) : ℕ∞) < n + 1 := by
  rw [Nat.cast_succ]
  exact (ENat.add_lt_add_iff_right ENat.one_ne_top).2 h

/-- Blow up the closed point `q ∈ T` first, then follow a sequence of point blow-ups of
`B_qT`. -/
private noncomputable def prepend {T : Scheme.{u}} {q : T} (hq : IsClosed ({q} : Set T))
    (s' : PointBlowupSequence (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{q}, hq⟩))) :
    PointBlowupSequence T where
  length := s'.length + 1
  S := prependS T s'.S
  zeroIso := Iso.refl T
  p := fun i => match i with
    | 0 => q
    | j + 1 => s'.p j
  isClosed_p := fun i hi => match i, hi with
    | 0, _ => hq
    | j + 1, hi => s'.isClosed_p j (coe_lt_of_succ_lt_add_one hi)
  blowupIso := fun i hi => match i, hi with
    | 0, _ => s'.zeroIso
    | j + 1, hi => s'.blowupIso j (coe_lt_of_succ_lt_add_one hi)

private theorem transformedSubscheme_prepend_zero {T : Scheme.{u}} {q : T}
    (hq : IsClosed ({q} : Set T))
    (s' : PointBlowupSequence (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{q}, hq⟩)))
    (C : T.IdealSheafData) : (prepend hq s').transformedSubscheme C 0 = C := by
  rw [PointBlowupSequence.transformedSubscheme]
  exact Scheme.IdealSheafData.comap_id C

/-- The birational transforms along `prepend hq s'` are, after the first blow-up, those along
`s'` of the birational transform of `C`. -/
private theorem transformedSubscheme_prepend_succ {T : Scheme.{u}} {q : T}
    (hq : IsClosed ({q} : Set T))
    (s' : PointBlowupSequence (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{q}, hq⟩)))
    (C : T.IdealSheafData) : ∀ i : ℕ,
      (prepend hq s').transformedSubscheme C (i + 1) =
        s'.transformedSubscheme (birationalTransform q hq C) i
  | 0 => by
    conv_lhs => rw [PointBlowupSequence.transformedSubscheme]
    rw [dite_eq_left (show ((0 : ℕ) : ℕ∞) < (prepend hq s').length from
      Nat.cast_zero (R := ℕ∞) ▸ zero_lt_one.trans_le le_add_self),
      transformedSubscheme_prepend_zero]
    rfl
  | i + 1 => by
    conv_lhs => rw [PointBlowupSequence.transformedSubscheme]
    conv_rhs => rw [PointBlowupSequence.transformedSubscheme]
    by_cases hi : (i : ℕ∞) < s'.length
    · rw [dite_eq_left (show ((i + 1 : ℕ) : ℕ∞) < (prepend hq s').length from succ_lt_add_one hi),
        dite_eq_left hi, transformedSubscheme_prepend_succ hq s' C i]
      rfl
    · rw [dite_eq_right (show ¬ ((i + 1 : ℕ) : ℕ∞) < (prepend hq s').length from
        fun h => hi (coe_lt_of_succ_lt_add_one h)), dite_eq_right hi]
      rfl

/-- A curve on `T` *has a stopping sequence* if some weak embedded resolution sequence for it
stops. -/
private def HasStoppingSequence (T : Scheme.{u}) (C : T.IdealSheafData) : Prop :=
  ∃ s : PointBlowupSequence T, s.IsWeakEmbeddedResolution C ∧ s.WeakEmbeddedResolutionStops C

/-- If the birational transform of `C` in the blow-up of a singular point `q` of `C` has a
stopping sequence, so has `C`. -/
private theorem hasStoppingSequence_of_blowUp {T : Scheme.{u}} {C : T.IdealSheafData} {q : T}
    (hq : IsClosed ({q} : Set T)) (hqC : q ∈ C.support)
    (hsing : ¬ IsRegularLocalRing (T.presheaf.stalk q ⧸ IdealSheafData.stalk C q))
    (h : HasStoppingSequence _ (birationalTransform q hq C)) : HasStoppingSequence T C := by
  obtain ⟨s', hs', n, hn, hreg⟩ := h
  refine ⟨prepend hq s', fun i hi => ?_, n + 1, ?_, fun q' hq' hmem => ?_⟩
  · match i, hi with
    | 0, _ =>
      rw [transformedSubscheme_prepend_zero]
      exact ⟨hqC, hsing⟩
    | j + 1, hi =>
      rw [transformedSubscheme_prepend_succ]
      exact hs' j (coe_lt_of_succ_lt_add_one hi)
  · change s'.length + 1 = ((n + 1 : ℕ) : ℕ∞)
    rw [hn, Nat.cast_succ]
  · rw [transformedSubscheme_prepend_succ] at hmem ⊢
    exact hreg q' hq' hmem

/-- A curve without closed singular points on a nonempty scheme has a stopping sequence, of
length `0`. -/
private theorem hasStoppingSequence_of_forall {T : Scheme.{u}} [Nonempty T] {C : T.IdealSheafData}
    (h : ∀ q : T, IsClosed ({q} : Set T) → q ∈ C.support →
      IsRegularLocalRing (T.presheaf.stalk q ⧸ IdealSheafData.stalk C q)) :
    HasStoppingSequence T C := by
  have h0 : (trivialSeq T).transformedSubscheme C 0 = C := by
    rw [PointBlowupSequence.transformedSubscheme]
    exact Scheme.IdealSheafData.comap_id C
  refine ⟨trivialSeq T, fun i hi => absurd (show (i : ℕ∞) < 0 from hi)
    (not_lt_of_ge zero_le), 0, rfl, fun q hq hmem => ?_⟩
  rw [h0] at hmem ⊢
  exact h q hq hmem

/-- The standing hypotheses of the recursion: a nonempty smooth quasi-compact surface over `k`
with a curve that has no stopping sequence. -/
private def NoStop (k : Type u) [Field k] (x : Σ T : Scheme.{u}, T.IdealSheafData) : Prop :=
  (∃ sX : x.1 ⟶ Spec (.of k), SmoothOfRelativeDimension 2 sX ∧ QuasiCompact sX) ∧
    Nonempty x.1 ∧ ¬ HasStoppingSequence x.1 x.2

/-- A curve with no stopping sequence has a closed singular point, and its birational transform
in the blow-up of that point has no stopping sequence either. -/
private theorem exists_noStop {k : Type u} [Field k] [PerfectField k]
    {x : Σ T : Scheme.{u}, T.IdealSheafData} (hx : NoStop k x) :
    ∃ (q : x.1) (hq : IsClosed ({q} : Set x.1)), q ∈ x.2.support ∧
      ¬ IsRegularLocalRing (x.1.presheaf.stalk q ⧸ IdealSheafData.stalk x.2 q) ∧
      NoStop k ⟨blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{q}, hq⟩),
        birationalTransform q hq x.2⟩ := by
  obtain ⟨⟨sX, _, _⟩, hne, hno⟩ := hx
  have : Nonempty x.1 := hne
  obtain ⟨q, hq, hqC, hsing⟩ : ∃ q : x.1, IsClosed ({q} : Set x.1) ∧ q ∈ x.2.support ∧
      ¬ IsRegularLocalRing (x.1.presheaf.stalk q ⧸ IdealSheafData.stalk x.2 q) := by
    by_contra! h
    exact hno (hasStoppingSequence_of_forall fun q hq hmem => h q hq hmem)
  have hS := isRegularSurface_of_smoothOfRelativeDimension sX
  obtain ⟨h1, h2⟩ := smoothOfRelativeDimension_blowUpToBase_comp sX hq
  exact ⟨q, hq, hqC, hsing, ⟨_, h1, h2⟩, nonempty_blowUp hS q hq,
    fun h => hno (hasStoppingSequence_of_blowUp hq hqC hsing h)⟩

/-- One step of the recursion: blow up a closed singular point of the curve. -/
private noncomputable def nextNoStop {k : Type u} [Field k] [PerfectField k]
    (x : {x : Σ T : Scheme.{u}, T.IdealSheafData // NoStop k x}) :
    {x : Σ T : Scheme.{u}, T.IdealSheafData // NoStop k x} :=
  ⟨⟨blowUp (Scheme.IdealSheafData.vanishingIdeal
      ⟨{(exists_noStop x.2).choose}, (exists_noStop x.2).choose_spec.choose⟩),
    birationalTransform _ (exists_noStop x.2).choose_spec.choose x.1.2⟩,
    (exists_noStop x.2).choose_spec.choose_spec.2.2⟩

/-- Iterating `nextNoStop`. -/
private noncomputable def noStopChain {k : Type u} [Field k] [PerfectField k]
    (x₀ : {x : Σ T : Scheme.{u}, T.IdealSheafData // NoStop k x}) :
    ℕ → {x : Σ T : Scheme.{u}, T.IdealSheafData // NoStop k x}
  | 0 => x₀
  | n + 1 => nextNoStop (noStopChain x₀ n)

/-- The infinite weak embedded resolution sequence built by `noStopChain`. -/
private noncomputable def noStopSeq {k : Type u} [Field k] [PerfectField k]
    (x₀ : {x : Σ T : Scheme.{u}, T.IdealSheafData // NoStop k x}) :
    PointBlowupSequence x₀.1.1 where
  length := ⊤
  S := fun i => (noStopChain x₀ i).1.1
  zeroIso := Iso.refl _
  p := fun i => (exists_noStop (noStopChain x₀ i).2).choose
  isClosed_p := fun i _ => (exists_noStop (noStopChain x₀ i).2).choose_spec.choose
  blowupIso := fun _ _ => Iso.refl _

private theorem transformedSubscheme_noStopSeq {k : Type u} [Field k] [PerfectField k]
    (x₀ : {x : Σ T : Scheme.{u}, T.IdealSheafData // NoStop k x}) :
    ∀ i : ℕ, (noStopSeq x₀).transformedSubscheme x₀.1.2 i = (noStopChain x₀ i).1.2
  | 0 => by
    conv_lhs => rw [PointBlowupSequence.transformedSubscheme]
    exact Scheme.IdealSheafData.comap_id _
  | i + 1 => by
    conv_lhs => rw [PointBlowupSequence.transformedSubscheme]
    rw [dite_eq_left (show ((i : ℕ) : ℕ∞) < (noStopSeq x₀).length from WithTop.coe_lt_top _),
      transformedSubscheme_noStopSeq x₀ i]
    exact Scheme.IdealSheafData.comap_id _

/-- **Existence of stopping sequences.** A reduced effective Cartier divisor on a nonempty smooth
quasi-compact surface over a perfect field has a weak embedded resolution sequence that
stops: otherwise blowing up singular points forever gives an infinite weak embedded resolution
sequence, which does not stop. -/
private theorem hasStoppingSequence {k : Type u} [Field k] [PerfectField k] {T : Scheme.{u}}
    [Nonempty T] (sT : T ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 sT] [QuasiCompact sT]
    (D : T.IdealSheafData) (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    [IsReduced D.subscheme] : HasStoppingSequence T D := by
  by_contra hno
  let x₀ : {x : Σ T : Scheme.{u}, T.IdealSheafData // NoStop k x} :=
    ⟨⟨T, D⟩, ⟨sT, inferInstance, inferInstance⟩, inferInstance, hno⟩
  have hweak : (noStopSeq x₀).IsWeakEmbeddedResolution D := fun i _ => by
    have h := (exists_noStop (noStopChain x₀ i).2).choose_spec.choose_spec
    rw [transformedSubscheme_noStopSeq x₀ i]
    exact ⟨h.1, h.2.1⟩
  obtain ⟨⟨n, hn, -⟩, -⟩ := PointBlowupSequence.weakEmbeddedResolutionStops_of_maximal sT D hD
    (noStopSeq x₀) hweak fun s' _ hlt => absurd (show (⊤ : ℕ∞) < s'.length from hlt) not_top_lt
  exact ENat.top_ne_natCast n hn

end Stopping

/-! ### The snc model -/

/-- The stalk of the reduced structure on a union is the intersection of the stalks. -/
private theorem stalk_vanishingIdeal_union {Y : Scheme.{u}} {Z₁ Z₂ : Set Y} (h₁ : IsClosed Z₁)
    (h₂ : IsClosed Z₂) (y : Y) :
    IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal ⟨Z₁ ∪ Z₂, h₁.union h₂⟩) y =
      IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal ⟨Z₁, h₁⟩) y ⊓
        IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal ⟨Z₂, h₂⟩) y := by
  rw [MMP.Resolution.stalk_vanishingIdeal_eq, MMP.Resolution.stalk_vanishingIdeal_eq,
    MMP.Resolution.stalk_vanishingIdeal_eq]
  exact (congrArg PrimeSpectrum.vanishingIdeal Set.preimage_union).trans
    (PrimeSpectrum.vanishingIdeal_union _ _)

/-- **The pointwise step.** Let `A`, `B`, `F` be closed sets of a locally Noetherian scheme with
`A ∪ F` and `B ∪ F` snc, and `D` a closed subscheme with support `A ∪ B` whose local rings at
the closed points of `A ∩ B` are regular. Then `A ∪ B ∪ F` is snc: at a point of `A ∩ B` the
prime ideal of `D` is the intersection of the ideals of `A` and `B`, hence equal to one of them,
so near the point `A ∪ B ∪ F` is `A ∪ F` or `B ∪ F`. -/
private theorem isSNCSubscheme_vanishingIdeal_union_union {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    {A B F : Set Y} (hA : IsClosed A) (hB : IsClosed B) (hF : IsClosed F)
    (hAF : IsSNCSubscheme (Scheme.IdealSheafData.vanishingIdeal ⟨A ∪ F, hA.union hF⟩))
    (hBF : IsSNCSubscheme (Scheme.IdealSheafData.vanishingIdeal ⟨B ∪ F, hB.union hF⟩))
    (D : Y.IdealSheafData) (hD : (D.support : Set Y) = A ∪ B)
    (hreg : ∀ q : Y, IsClosed ({q} : Set Y) → q ∈ D.support →
      IsRegularLocalRing (Y.presheaf.stalk q ⧸ IdealSheafData.stalk D q)) :
    IsSNCSubscheme (Scheme.IdealSheafData.vanishingIdeal
      ⟨A ∪ B ∪ F, (hA.union hB).union hF⟩) := by
  intro q hq
  by_cases hqA : q ∈ A
  swap
  · have h : IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal
        ⟨A ∪ B ∪ F, (hA.union hB).union hF⟩) q =
        IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal ⟨B ∪ F, hB.union hF⟩) q :=
      MMP.Mori.stalk_vanishingIdeal_eq_of_inter_eq _ _ (U := ⟨Aᶜ, hA.isOpen_compl⟩) hqA (by
        ext x
        simp only [TopologicalSpace.Closeds.coe_mk, TopologicalSpace.Opens.coe_mk,
          Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff]
        tauto)
    exact (hasSNCAt_congr h).2 (hBF q hq)
  by_cases hqB : q ∈ B
  swap
  · have h : IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal
        ⟨A ∪ B ∪ F, (hA.union hB).union hF⟩) q =
        IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal ⟨A ∪ F, hA.union hF⟩) q :=
      MMP.Mori.stalk_vanishingIdeal_eq_of_inter_eq _ _ (U := ⟨Bᶜ, hB.isOpen_compl⟩) hqB (by
        ext x
        simp only [TopologicalSpace.Closeds.coe_mk, TopologicalSpace.Opens.coe_mk,
          Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff]
        tauto)
    exact (hasSNCAt_congr h).2 (hAF q hq)
  have hqD : q ∈ D.support := by
    rw [← SetLike.mem_coe, hD]
    exact Or.inl hqA
  have := hreg q hq hqD
  have hP : (IdealSheafData.stalk D q).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).1 (IsRegularLocalRing.isDomain _)
  have hDAB : IdealSheafData.stalk D q =
      IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal ⟨A, hA⟩) q ⊓
        IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal ⟨B, hB⟩) q := by
    rw [← stalk_vanishingIdeal_union hA hB]
    have : Scheme.IdealSheafData.vanishingIdeal ⟨A ∪ B, hA.union hB⟩ = D.radical := by
      rw [← Scheme.IdealSheafData.vanishingIdeal_support]
      congr 1
      exact TopologicalSpace.Closeds.ext hD.symm
    rw [this, MMP.Resolution.stalk_radical, hP.isRadical.radical]
  have hunion := stalk_vanishingIdeal_union (hA.union hB) hF q
  rw [stalk_vanishingIdeal_union hA hB] at hunion
  rcases (hP.inf_le).1 hDAB.symm.le with h | h
  · rw [inf_eq_left.2 (h.trans (hDAB.le.trans inf_le_right)),
      ← stalk_vanishingIdeal_union hA hF] at hunion
    exact (hasSNCAt_congr hunion).2 (hAF q hq)
  · rw [inf_eq_right.2 (h.trans (hDAB.le.trans inf_le_left)),
      ← stalk_vanishingIdeal_union hB hF] at hunion
    exact (hasSNCAt_congr hunion).2 (hBF q hq)

/-- **The second run.** On a smooth quasi-compact surface `T` over a perfect field, let `A`, `B`
be closed sets with snc reduced structures whose union is the support of an effective Cartier
divisor `J`. Then some composite of point blow-ups `π` makes `π⁻¹(J)_red` snc: run weak
embedded resolution on `J_red`; the inverse image of `A ∪ B` is the union of the strict
transforms of `A` and `B` with the exceptional set, the strict transform of each with the
exceptional set is snc, and the regularity of the final transform of `J_red` lets
`isSNCSubscheme_vanishingIdeal_union_union` glue them. -/
private theorem exists_isSNCSubscheme_comap_of_support_eq_union {k : Type u} [Field k]
    [PerfectField k] {T : Scheme.{u}} (sT : T ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 sT]
    [QuasiCompact sT] {A B : Set T} (hA : IsClosed A) (hB : IsClosed B)
    (hAsnc : IsSNCSubscheme (Scheme.IdealSheafData.vanishingIdeal ⟨A, hA⟩))
    (hBsnc : IsSNCSubscheme (Scheme.IdealSheafData.vanishingIdeal ⟨B, hB⟩))
    (J : T.IdealSheafData) (hJ : Stacks.Divisors.IsEffectiveCartierDivisor J)
    (hJAB : (J.support : Set T) = A ∪ B) :
    ∃ (T' : Scheme.{u}) (π : T' ⟶ T), IsCompositeOfPointBlowups π ∧
      IsSNCSubscheme (Scheme.IdealSheafData.vanishingIdeal (J.comap π).support) := by
  by_cases hne : Nonempty T
  swap
  · exact ⟨T, 𝟙 T, ⟨0, (inferInstance : IsIso (𝟙 T))⟩, fun p _ => (hne ⟨p⟩).elim⟩
  have hT := isRegularSurface_of_smoothOfRelativeDimension sT
  have : IsLocallyNoetherian T := hT.1.toIsLocallyNoetherian
  have : IsReduced (Scheme.IdealSheafData.vanishingIdeal J.support).subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  obtain ⟨s, hs, n, hn, hreg⟩ :=
    hasStoppingSequence sT _ (isEffectiveCartierDivisor_vanishingIdeal_support hT.2.1 hJ)
  have : IsLocallyNoetherian (s.S n) :=
    (isRegularSurface_S hT s n hn.ge).1.toIsLocallyNoetherian
  have hsupp :
      ((s.transformedSubscheme (Scheme.IdealSheafData.vanishingIdeal J.support) n).support :
        Set (s.S n)) = strictSet s A n ∪ strictSet s B n := by
    rw [coe_support_transformedSubscheme s sT _ n hn.ge,
      Scheme.IdealSheafData.coe_support_vanishingIdeal, hJAB, strictSet_union]
  have hpre : ((J.comap (s.π n hn.ge)).support : Set (s.S n)) =
      strictSet s A n ∪ strictSet s B n ∪ excSet s n := by
    rw [Scheme.IdealSheafData.support_comap]
    change s.π n hn.ge ⁻¹' (J.support : Set T) = _
    rw [hJAB, preimage_π s (hA.union hB) n hn.ge fun j hj => ?_, strictSet_union]
    have := p_mem_strictSet s sT hs j (by rw [hn]; exact_mod_cast hj)
    rwa [Scheme.IdealSheafData.coe_support_vanishingIdeal, hJAB] at this
  refine ⟨s.S n, s.π n hn.ge, ⟨n, isCompositeOfPointBlowupsOfLength_π s n hn.ge⟩,
    isSNCSubscheme_vanishingIdeal_congr (Z := ⟨_, ((isClosed_strictSet s hA n).union
      (isClosed_strictSet s hB n)).union (isClosed_excSet s n)⟩) hpre.symm ?_⟩
  exact isSNCSubscheme_vanishingIdeal_union_union (isClosed_strictSet s hA n)
    (isClosed_strictSet s hB n) (isClosed_excSet s n)
    (isSNCSubscheme_strictSet_union_excSet s sT hA hAsnc n hn.ge)
    (isSNCSubscheme_strictSet_union_excSet s sT hB hBsnc n hn.ge) _ hsupp hreg

/-- **Kollár 1.48 (existence of an snc model).** Let `S` be a smooth surface over a perfect field
`k` and `C ⊆ S` an effective Cartier divisor. There is a composite of blow-ups of closed points
`π : S' ⟶ S` such that the reduced inverse image `π⁻¹(C)_red` is a simple normal crossing
divisor. -/
@[mmp "lem_kr1c_exists_snc_model"]
theorem exists_isCompositeOfPointBlowups_isSNCSubscheme
    {k : Type u} [Field k] [PerfectField k] {S : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 2 sS] [QuasiCompact sS]
    (C : S.IdealSheafData) (hC : Stacks.Divisors.IsEffectiveCartierDivisor C) :
    ∃ (S' : Scheme.{u}) (π : S' ⟶ S), IsCompositeOfPointBlowups π ∧
      IsSNCSubscheme (Scheme.IdealSheafData.vanishingIdeal (C.comap π).support) := by
  have hS := isRegularSurface_of_smoothOfRelativeDimension sS
  have : IsLocallyNoetherian S := hS.1.toIsLocallyNoetherian
  by_cases hne : Nonempty S
  swap
  · exact ⟨S, 𝟙 S, ⟨0, (inferInstance : IsIso (𝟙 S))⟩, fun p _ => (hne ⟨p⟩).elim⟩
  /- The first run, on `C_red`, of length `m`: `π₁⁻¹(C) = A₀ ∪ B₀` with `A₀` the smooth
  transform of `C` and `B₀` the exceptional set. -/
  have hC₁ := isEffectiveCartierDivisor_vanishingIdeal_support hS.2.1 hC
  have : IsReduced (Scheme.IdealSheafData.vanishingIdeal C.support).subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  obtain ⟨s₁, hs₁, m, hm, hreg₁⟩ := hasStoppingSequence sS _ hC₁
  obtain ⟨_, _⟩ := smoothOfRelativeDimension_π_comp sS s₁ m hm.ge
  have hT := isRegularSurface_of_smoothOfRelativeDimension (s₁.π m hm.ge ≫ sS)
  have hA₀ := isClosed_strictSet s₁ C.support.isClosed m
  have hZ₀ : ((C.comap (s₁.π m hm.ge)).support : Set (s₁.S m)) =
      strictSet s₁ (C.support : Set S) m ∪ excSet s₁ m := by
    rw [Scheme.IdealSheafData.support_comap]
    refine preimage_π s₁ C.support.isClosed m hm.ge fun j hj => ?_
    have := p_mem_strictSet s₁ sS hs₁ j (by rw [hm]; exact_mod_cast hj)
    rwa [Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
  -- the transform `A₀` of `C` is smooth, hence snc
  have hA₀snc : IsSNCSubscheme (Scheme.IdealSheafData.vanishingIdeal ⟨_, hA₀⟩) :=
    isSNCSubscheme_vanishingIdeal_congr (by
      rw [coe_support_transformedSubscheme s₁ sS _ m hm.ge,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]; rfl) fun q hq =>
      hasSNCAt_vanishingIdeal_support_of_isRegularLocalRing hT _
        (isEffectiveCartierDivisor_transformedSubscheme s₁ sS hC₁ m hm.ge) hq (hreg₁ q hq)
  -- the second run, on `π₁⁻¹(C)_red`
  obtain ⟨T', π₂, ⟨n, hπ₂⟩, hsnc⟩ := exists_isSNCSubscheme_comap_of_support_eq_union
    (s₁.π m hm.ge ≫ sS) hA₀ (isClosed_excSet s₁ m) hA₀snc (isSNCSubscheme_excSet s₁ sS m hm.ge)
    _ (isEffectiveCartierDivisor_comap_π s₁ sS hC m hm.ge) hZ₀
  refine ⟨T', π₂ ≫ s₁.π m hm.ge, ⟨m + n, isCompositeOfPointBlowupsOfLength_comp m n
    (isCompositeOfPointBlowupsOfLength_π s₁ m hm.ge) hπ₂⟩, ?_⟩
  rwa [Scheme.IdealSheafData.comap_comp]

/-! ### Strong embedded resolution: the length is bounded -/

/-- A strong embedded resolution sequence dominated by a composite of `N` point blow-ups with snc
reduced preimage of `C` has length at most `N`. -/
private theorem length_le {S Sstar : Scheme.{u}} (hS : IsRegularSurface S)
    (C : S.IdealSheafData) {πstar : Sstar ⟶ S} {N : ℕ}
    (hN : IsCompositeOfPointBlowupsOfLength N πstar)
    (hsnc : IsSNCSubscheme (Scheme.IdealSheafData.vanishingIdeal (C.comap πstar).support))
    (s : PointBlowupSequence S) (hs : s.IsStrongEmbeddedResolution C) : s.length ≤ N := by
  by_contra h
  have hi : ((N + 1 : ℕ) : ℕ∞) ≤ s.length := by
    rw [Nat.cast_succ]; exact Order.add_one_le_of_lt (not_le.mp h)
  obtain ⟨g, hg, hcomp⟩ := PointBlowupSequence.exists_isCompositeOfPointBlowups_comp_π_eq hS C
    ⟨N, hN⟩ hsnc s hs (N + 1) hi
  have := IsCompositeOfPointBlowupsOfLength.le_of_comp hS
    (isCompositeOfPointBlowupsOfLength_π s (N + 1) hi) hg (hcomp ▸ hN)
  omega

/-! ### Extending a sequence by one blow-up -/

/-- `s'` agrees with `s` on all the data of `s`: the same schemes `S_i` (`i ≤ s.length`), the same
identification `S_0 ≅ S₀`, the same centres `p_i` and the same isomorphisms `S_{i+1} ≅ B_{p_i}S_i`
(`i < s.length`). -/
private abbrev Agrees {S₀ : Scheme.{u}} (s s' : PointBlowupSequence S₀) : Prop :=
  (∀ i : ℕ, (i : ℕ∞) ≤ s.length → s'.S i = s.S i) ∧ HEq s'.zeroIso s.zeroIso ∧
    (∀ i : ℕ, (i : ℕ∞) < s.length → HEq (s'.p i) (s.p i)) ∧
    ∀ (i : ℕ) (hi : (i : ℕ∞) < s.length) (hi' : (i : ℕ∞) < s'.length),
      HEq (s'.blowupIso i hi') (s.blowupIso i hi)

section Extension

/-- Transport of a point along an equality of schemes. -/
private noncomputable def castPt {X Y : Scheme.{u}} (e : X = Y) (x : X) : Y :=
  cast (congrArg (fun Z : Scheme.{u} => (Z : Type u)) e) x

private theorem castPt_heq {X Y : Scheme.{u}} (e : X = Y) (x : X) : HEq (castPt e x) x :=
  cast_heq _ _

/-- Blow-ups of corresponding closed points of equal schemes are equal. -/
private theorem blowUp_congr {X Y : Scheme.{u}} (h : X = Y) {x : X} {y : Y} (hxy : HEq x y)
    (hx : IsClosed ({x} : Set X)) (hy : IsClosed ({y} : Set Y)) :
    blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩) =
      blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) := by
  subst h; cases hxy; rfl

private theorem isClosed_congr {X Y : Scheme.{u}} (h : X = Y) {x : X} {y : Y} (hxy : HEq x y)
    (hy : IsClosed ({y} : Set Y)) : IsClosed ({x} : Set X) := by
  subst h; cases hxy; exact hy

private theorem heq_eqToIso_trans {A A' B B' : Scheme.{u}} (e₁ : A' = A) (f : A ≅ B)
    (e₂ : B = B') : HEq (eqToIso e₁ ≪≫ f ≪≫ eqToIso e₂) f := by
  subst e₁ e₂; simp

private theorem heq_eqToIso_trans' {A A' B : Scheme.{u}} (e₁ : A' = A) (f : A ≅ B) :
    HEq (eqToIso e₁ ≪≫ f) f := by
  subst e₁; simp

private theorem heq_eqToIso_trans_hom {A A' B : Scheme.{u}} (e₁ : A' = A) (f : A ≅ B) :
    HEq (eqToIso e₁ ≪≫ f).hom f.hom := by
  subst e₁; simp

private theorem heq_comp_blowUpToBase {S₀ X Y X' Y' : Scheme.{u}} (e : X = Y) {x : X} {y : Y}
    (hxy : HEq x y) (hx : IsClosed ({x} : Set X)) (hy : IsClosed ({y} : Set Y)) (e' : X' = Y')
    (φ : X' ≅ blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩))
    (ψ : Y' ≅ blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) (hφψ : HEq φ ψ)
    {f : X ⟶ S₀} {g : Y ⟶ S₀} (hfg : HEq f g) :
    HEq ((φ.hom ≫ blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩)) ≫ f)
      ((ψ.hom ≫ blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) ≫ g) := by
  subst e; cases hxy; subst e'; cases hφψ; cases hfg; rfl

private theorem strong_congr {S₀ X Y : Scheme.{u}} (e : X = Y) {x : X} {y : Y} (hxy : HEq x y)
    {f : X ⟶ S₀} {g : Y ⟶ S₀} (hfg : HEq f g) (C : S₀.IdealSheafData)
    (h : y ∈ (C.comap g).support ∧
      ¬ HasSNCAt (Scheme.IdealSheafData.vanishingIdeal (C.comap g).support) y) :
    x ∈ (C.comap f).support ∧
      ¬ HasSNCAt (Scheme.IdealSheafData.vanishingIdeal (C.comap f).support) x := by
  subst e; cases hxy; cases hfg; exact h

variable {S₀ : Scheme.{u}} (s : PointBlowupSequence S₀) (n : ℕ) {q : s.S n}
  (hq : IsClosed ({q} : Set (s.S n)))

/-- The schemes of the extension. -/
private noncomputable def extS (i : ℕ) : Scheme.{u} :=
  if i ≤ n then s.S i else blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{q}, hq⟩)

private theorem extS_le {i : ℕ} (h : i ≤ n) : extS s n hq i = s.S i := ite_eq_left h

private theorem extS_gt {i : ℕ} (h : ¬ i ≤ n) :
    extS s n hq i = blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{q}, hq⟩) := ite_eq_right h

/-- The centres of the extension. -/
private noncomputable def extP (b : blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{q}, hq⟩))
    (i : ℕ) : extS s n hq i :=
  if h : i < n then castPt (extS_le s n hq h.le).symm (s.p i)
  else if h' : i = n then castPt (extS_le s n hq h'.le).symm (castPt (congrArg s.S h'.symm) q)
  else castPt (extS_gt s n hq (by omega)).symm b

private theorem extP_heq_lt (b) {i : ℕ} (h : i < n) : HEq (extP s n hq b i) (s.p i) := by
  rw [extP, dite_eq_left h]; exact castPt_heq _ _

private theorem extP_heq_eq (b) : HEq (extP s n hq b n) q := by
  rw [extP, dite_eq_right (lt_irrefl n), dite_eq_left rfl]
  exact (castPt_heq _ _).trans (castPt_heq _ _)

variable {s n} (hn : s.length = n)

include hn

private theorem lt_of_lt_ext {i : ℕ} (h : i < n) : (i : ℕ∞) < s.length := by
  rw [hn]; exact_mod_cast h

private theorem le_of_le_ext {i : ℕ} (h : i ≤ n) : (i : ℕ∞) ≤ s.length := by
  rw [hn]; exact_mod_cast h

private theorem extP_isClosed (b) (i : ℕ) (hi : (i : ℕ∞) < ((n + 1 : ℕ) : ℕ∞)) :
    IsClosed ({extP s n hq b i} : Set (extS s n hq i)) := by
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (ENat.natCast_lt_natCast.mp hi)
  rcases hi'.lt_or_eq with h | rfl
  · exact isClosed_congr (extS_le s n hq h.le) (extP_heq_lt s n hq b h)
      (s.isClosed_p i (lt_of_lt_ext hn h))
  · exact isClosed_congr (extS_le s i hq le_rfl) (extP_heq_eq s i hq b) hq

/-- The extension of `s`, of length `n`, by the blow-up of `q`; the point `b` fills the unused
slot `p (n + 1)`. -/
private noncomputable def extendSeq (b : blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{q}, hq⟩)) :
    PointBlowupSequence S₀ where
  length := (n + 1 : ℕ)
  S := extS s n hq
  zeroIso := eqToIso (extS_le s n hq (Nat.zero_le n)) ≪≫ s.zeroIso
  p := extP s n hq b
  isClosed_p := extP_isClosed hq hn b
  blowupIso i hi :=
    if h : i < n then
      eqToIso (extS_le s n hq (Nat.succ_le_of_lt h)) ≪≫ s.blowupIso i (lt_of_lt_ext hn h) ≪≫
        eqToIso (blowUp_congr (extS_le s n hq h.le).symm (extP_heq_lt s n hq b h).symm _ _)
    else
      have hin : i = n := by have := ENat.natCast_lt_natCast.mp hi; omega
      eqToIso (extS_gt s n hq (by omega)) ≪≫
        eqToIso (blowUp_congr (by subst hin; exact (extS_le s i hq le_rfl).symm)
          (by subst hin; exact (extP_heq_eq s i hq b).symm) _ _)

private theorem ext_blowupIso_heq (b) {i : ℕ} (h : i < n)
    (hi' : (i : ℕ∞) < (extendSeq hq hn b).length) :
    HEq ((extendSeq hq hn b).blowupIso i hi') (s.blowupIso i (lt_of_lt_ext hn h)) := by
  dsimp only [extendSeq]
  split
  · exact heq_eqToIso_trans _ _ _
  · contradiction

private theorem ext_π_heq (b) :
    ∀ (i : ℕ) (h : i ≤ n) (hi : (i : ℕ∞) ≤ (extendSeq hq hn b).length),
      HEq ((extendSeq hq hn b).π i hi) (s.π i (le_of_le_ext hn h))
  | 0, _, _ => heq_eqToIso_trans_hom _ _
  | i + 1, h, hi => by
    have hi' : i < n := h
    rw [PointBlowupSequence.π, PointBlowupSequence.π, PointBlowupSequence.σ,
      PointBlowupSequence.σ]
    exact heq_comp_blowUpToBase (extS_le s n hq hi'.le) (extP_heq_lt s n hq b hi') _ _
      (extS_le s n hq h) _ _ (ext_blowupIso_heq hq hn b hi' _)
      (ext_π_heq b i hi'.le _)

/-- A strong embedded resolution sequence of finite length `n` with a closed point `q` of
`π_n⁻¹(C₀)` at which its reduced structure is not snc extends, by blowing up `q`, to a longer one
agreeing with it on all its data. -/
private theorem exists_extension_of_point (C₀ : S₀.IdealSheafData)
    (hs : s.IsStrongEmbeddedResolution C₀)
    (hqC : q ∈ (C₀.comap (s.π n (le_of_le_ext hn le_rfl))).support)
    (hqsnc : ¬ HasSNCAt (Scheme.IdealSheafData.vanishingIdeal
      (C₀.comap (s.π n (le_of_le_ext hn le_rfl))).support) q)
    (b : blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{q}, hq⟩)) :
    ∃ s' : PointBlowupSequence S₀, s'.IsStrongEmbeddedResolution C₀ ∧ s.length < s'.length ∧
      Agrees s s' := by
  have hlt : ∀ {i : ℕ}, (i : ℕ∞) < s.length → i < n := fun h => by
    rw [hn] at h; exact_mod_cast h
  refine ⟨extendSeq hq hn b, fun i hi => ?_, ?_, fun i hi => extS_le s n hq ?_,
    heq_eqToIso_trans' _ _, fun i hi => extP_heq_lt s n hq b (hlt hi),
    fun i hi hi' => ext_blowupIso_heq hq hn b (hlt hi) hi'⟩
  · have hi' : i ≤ n := Nat.lt_succ_iff.mp (ENat.natCast_lt_natCast.mp hi)
    rcases hi'.lt_or_eq with h | rfl
    · exact strong_congr (extS_le s n hq h.le) (extP_heq_lt s n hq b h)
        (ext_π_heq hq hn b i h.le _) C₀ (hs i (lt_of_lt_ext hn h))
    · exact strong_congr (extS_le s i hq le_rfl) (extP_heq_eq s i hq b)
        (ext_π_heq hq hn b i le_rfl _) C₀ ⟨hqC, hqsnc⟩
  · rw [hn]; change ((n : ℕ) : ℕ∞) < ((n + 1 : ℕ) : ℕ∞); exact_mod_cast Nat.lt_succ_self n
  · rw [hn] at hi; exact_mod_cast hi

end Extension

namespace PointBlowupSequence

/-- **Kollár, Theorem 1.47 (strong embedded resolution).** Let `S` be a smooth surface over a
perfect field `k` and `C ⊆ S` an effective Cartier divisor. Every strong embedded resolution
sequence `s` for `(S, C)` which no longer strong embedded resolution sequence extends stops
(`StrongEmbeddedResolutionStops`): it has finite length `n` and `π_n⁻¹(C)_red` is a simple
normal crossing divisor. -/
@[mmp "thm_kr1c_strong_embedded_resolution"]
theorem strongEmbeddedResolutionStops_of_maximal
    {k : Type u} [Field k] [PerfectField k] {S : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 2 sS] [QuasiCompact sS]
    (C : S.IdealSheafData) (hC : Stacks.Divisors.IsEffectiveCartierDivisor C)
    (s : PointBlowupSequence S) (hs : s.IsStrongEmbeddedResolution C)
    (hmax : ∀ s' : PointBlowupSequence S, s'.IsStrongEmbeddedResolution C →
      s.length < s'.length →
      ¬ ((∀ i : ℕ, (i : ℕ∞) ≤ s.length → s'.S i = s.S i) ∧ HEq s'.zeroIso s.zeroIso ∧
        (∀ i : ℕ, (i : ℕ∞) < s.length → HEq (s'.p i) (s.p i)) ∧
        ∀ (i : ℕ) (hi : (i : ℕ∞) < s.length) (hi' : (i : ℕ∞) < s'.length),
          HEq (s'.blowupIso i hi') (s.blowupIso i hi))) :
    s.StrongEmbeddedResolutionStops C := by
  have hS := isRegularSurface_of_smoothOfRelativeDimension sS
  obtain ⟨Sstar, πstar, ⟨N, hN⟩, hsnc⟩ := exists_isCompositeOfPointBlowups_isSNCSubscheme sS C hC
  have hlen := length_le hS C hN hsnc s hs
  obtain ⟨n, hn⟩ : ∃ n : ℕ, s.length = n :=
    ⟨s.length.toNat,
      (ENat.natCast_toNat (ne_top_of_le_ne_top (ENat.natCast_ne_top N) hlen)).symm⟩
  refine ⟨n, hn, fun q hq => ?_⟩
  by_contra hnot
  have hSn := isRegularSurface_S hS s n hn.ge
  have hqC : q ∈ (C.comap (s.π n hn.ge)).support := by
    by_contra hqC
    have := hSn.2.1 q
    refine hnot (hasSNCAt_of_notMem_support _ fun h => hqC ?_)
    rwa [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal] at h
  obtain ⟨b⟩ := nonempty_blowUp hSn q hq
  obtain ⟨s', hs', hlt, hagree⟩ := exists_extension_of_point hq hn C hs hqC hnot b
  exact hmax s' hs' hlt hagree

end PointBlowupSequence

end MMP.Resolution
