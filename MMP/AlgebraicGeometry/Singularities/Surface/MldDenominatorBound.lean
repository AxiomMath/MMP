module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldTerminalChainLabel
public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
import MMP.AlgebraicGeometry.Singularities.Surface.NormalizedExceptionalMatrix
import MMP.AlgebraicGeometry.Singularities.Surface.SingularPointMldBound
import MMP.AlgebraicGeometry.Resolution.Surface.MinimalResolutionExists
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
import MMP.AlgebraicGeometry.Divisor.SmoothWeilCartier
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.Singularities.GenericSurfaceCodimTwo
import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.SurfaceMatrix
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback

/-!
# Low log discrepancies at surface points and at singular codimension-two points

This file proves two bounds on minimal log discrepancies.

Let `(S, B)` be a klt surface pair over a field `k` of characteristic zero and `x ∈ S` a closed
point. Fix integers `q ≥ 1`, `N ≥ 0` and a rational `0 < δ ≤ 1`, and suppose that `qB` is
integral, that every divisor over `S` with centre `x` has log discrepancy at least `δ`, and that
at most `N` divisorial valuations centred at `x` have log discrepancy at most one. Put
`C = ⌈4 / δ²⌉`. Then there is an integer `1 ≤ D ≤ q N! C^N` such that every log discrepancy of a
divisor over `S` with centre `x` lies in `(1/D) ℤ`; in particular `mld_x(S, B)`, when it lies in
`[δ, 1]`, is of the form `r / D`. On the minimal resolution of an affine neighbourhood of `x` the
prime divisors `E_1, …, E_s` over `x` have log discrepancies in `[δ, 1]`, so `s ≤ N`, and their
normalized intersection matrix `M'` has entries bounded by `C`; hence `0 < |det M'| ≤ N! C^N`,
and Cramer's rule puts every `α_i - 1` in `(1/D) ℤ` for `D = q |det M'|`. The crepant boundary
on the resolution then has coefficients in `(1/D) ℤ` near the fibre over `x`; after
multiplication by `D` it is an integral divisor on a smooth surface, hence has a local equation
at the centre of any divisorial valuation centred at `x`, whose log discrepancy therefore lies in
`(1/D) ℤ`.

Let `(X, B)` be an effective pair over an algebraically closed field of characteristic zero and
`x ∈ X` a singular point of codimension two. The generic surface `S` through `x` is a normal
affine surface over a purely transcendental extension of `k`, with a singular closed point whose
local ring is `𝒪_{X,x}`. A divisor over `S` centred at that point with log discrepancy at most
one spreads out to a divisor over an affine neighbourhood of `x`, and its valuation is realized
by a proper divisor over `X` with centre `closure {x}` and the same log discrepancy. Hence
`mld_x(X, B) ≤ 1`.

## Main results

* `MMP.Fourfold.IsCharZeroKltPair.exists_denominator_logDiscrepancy_le`: bounded denominators
  of the log discrepancies at a surface point with few low places.
* `MMP.Threefold.minimalLogDiscrepancy_le_one_of_coheight_eq_two`: `mld_x(X, B) ≤ 1` at every
  singular point `x` of codimension two.

## Implementation notes

* A divisorial valuation centred at `x` is a divisor `(Y, f, E)` over `S`
  (`MMP.Mori.DivisorOver`) whose centre `MMP.Mori.DivisorOver.center` is `{x}`; its log
  discrepancy is `MMP.Intersection.IsLogDiscrepancy` (which forces `f` proper). Divisors are
  counted up to their valuation of `k(S)` (`MMP.Mori.DivisorOver.valuation`), so "at most `N`
  valuations" is a bound on the `Set.encard` of a set of valuations.
* The finite set `⋃_{D ≤ D_max} {r/D : δ ≤ r/D ≤ 1}` of the source is expressed by giving the
  minimal log discrepancy `MMP.Fourfold.minimalLogDiscrepancy` as `r / D` for the same `D`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.25, 4.1
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MMP.Mori
open scoped WithZero

universe u

/-! ### Divisors over an open subscheme -/

namespace MMP

/-- A nonempty open subscheme of an irreducible scheme is dense. -/
private theorem isDominant_opens_ι {Y : Scheme.{u}} [IrreducibleSpace Y] (V : Y.Opens)
    [Nonempty V] : IsDominant V.ι :=
  Opens.isDominant_ι (V.isOpen.dense ⟨_, (Classical.arbitrary V).2⟩)

/-- A nonempty open subscheme of an integral scheme has the same function field. -/
private theorem functionFieldMap_opens_ι_bijective {Y : Scheme.{u}} [IsIntegral Y] (V : Y.Opens)
    [Nonempty V] [IsDominant V.ι] : Function.Bijective (functionFieldMap V.ι) :=
  functionFieldMap_bijective_of_isOpenImmersion V.ι ⊤ ⟨Classical.arbitrary V, trivial⟩

/-- Pulling valuations back along a surjective ring map is injective. -/
private theorem valuation_comap_injective {R S Γ₀ : Type*} [Ring R] [Ring S]
    [LinearOrderedCommMonoidWithZero Γ₀] (f : R →+* S) (hf : Function.Surjective f) :
    Function.Injective (fun v : Valuation S Γ₀ => v.comap f) := by
  intro v w h
  ext g
  obtain ⟨g, rfl⟩ := hf g
  exact congrArg (fun u : Valuation R Γ₀ => u g) h

/-- An open immersion `U ⟶ X` restricted to its image is an isomorphism. -/
private theorem isIso_ι_restrict_self {X : Scheme.{u}} (U : X.Opens) : IsIso (U.ι ∣_ U) := by
  have : Surjective (U.ι ∣_ U) := by
    refine ⟨fun y => ?_⟩
    let x : (U.ι ⁻¹ᵁ U).toScheme := ⟨y, by simp⟩
    refine ⟨x, U.ι.isOpenEmbedding.injective ?_⟩
    have := Scheme.Hom.comp_apply (U.ι ∣_ U) U.ι x
    rw [morphismRestrict_ι] at this
    exact this.symm
  exact isIso_of_mono_of_strongEpi (U.ι ∣_ U)

/-- The inverse transform of a divisor along the inclusion of an open subscheme is its
restriction. -/
private theorem inverseTransformDivisor_ι_eq_restrictOpen {X : Scheme.{u}} {R : Type*}
    [AddCommMonoid R] (U : X.Opens) (B : DivisorWithCoeffs R X) :
    inverseTransformDivisor U.ι B = B.restrictOpen U := by
  have hbir : ∀ x : U.toScheme, U.ι x ∈ biregularLocus U.ι := fun x =>
    le_biregularLocus (isIso_ι_restrict_self U)
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

/-- **Log discrepancies over an open subscheme.** For a pair `(X, B)`, a proper divisor `D` over
`X` whose centre meets `U` and a proper divisor `D'` over `U` with the same valuation have the same
log discrepancies, for `B` and `B|_U` respectively. -/
theorem isLogDiscrepancy_open_iff {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} (hB : MMP.Mori.IsPair sX B) {n : ℕ} (hn : topologicalKrullDim X = n)
    (U : X.Opens) [Nonempty U] [IsIntegral U] [IsLocallyNoetherian U] [IsNormal U]
    (D : DivisorOver k sX) (hDp : IsProper D.f) (hDU : D.f D.E.genericPoint ∈ U)
    (D' : DivisorOver k (U.ι ≫ sX)) (hD'p : IsProper D'.f)
    (hv : D.valuation = D'.valuation.comap (functionFieldMap U.ι)) (a : ℝ) :
    MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) D a ↔
      MMP.Intersection.IsLogDiscrepancy (U.ι ≫ sX) n
        (QDivisor.toRDivisor (MMP.Mori.inverseTransformDivisor U.ι B)) D' a := by
  classical
  haveI := isDominant_opens_ι U
  obtain ⟨hXv, n0, K, hK, hQ⟩ := hB
  obtain rfl : n0 = n := by exact_mod_cast hK.topologicalKrullDim_eq.symm.trans hn
  have hPW : MMP.Mori.IsPairWith sX n0 K B := ⟨hXv, hK, hQ⟩
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy ⟨hXv, n0, K, hK, hQ⟩ hK D
  have hcen : ((D.center : Set X) ∩ U).Nonempty :=
    ⟨_, by rw [D.center_eq_closure_genericPoint]; exact subset_closure rfl, hDU⟩
  obtain ⟨hY, hf, E', -, hval, hiff⟩ :=
    MMP.Mori.DivisorOver.exists_restrict_isDiscrepancy_iff hPW D U hcen
  have hcU := (hiff c).1 hc
  haveI : IsProper (D.f ∣_ U) := by haveI := hDp; infer_instance
  obtain ⟨c', hc'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hcU.isPair hcU.2.1 D'
  have hDUv : DivisorOver.valuation (⟨_, D.f ∣_ U, hY, hf, E'⟩ : DivisorOver k (U.ι ≫ sX)) =
      D'.valuation :=
    valuation_comap_injective (functionFieldMap U.ι) (functionFieldMap_opens_ι_bijective U).2
      (hval.symm.trans hv)
  have hcc : (c' : ℝ) = c := by
    have h1 := (MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy hc' (1 + c')).2
      ⟨hD'p, rfl⟩
    have h2 := (MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy hcU (1 + c)).2
      ⟨inferInstance, rfl⟩
    have := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq h1 h2 hDUv.symm
    linarith
  rw [MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy hc,
    inverseTransformDivisor_ι_eq_restrictOpen,
    MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy hc', hcc]
  exact ⟨fun h => ⟨hD'p, h.2⟩, fun h => ⟨hDp, h.2⟩⟩

/-- The valuation of a divisor over `X` dominates the local ring of `X` at the image of the generic
point of the divisor. -/
private theorem divisorOver_dominates {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] (D : DivisorOver k sX) {y : X}
    (hy : D.f D.E.genericPoint = y) :
    (∀ a : X.presheaf.stalk y, D.valuation (algebraMap _ X.functionField a) ≤ 1) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y),
        D.valuation (algebraMap _ X.functionField a) < 1 := by
  subst hy
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  have happ : ∀ a : X.presheaf.stalk (D.f D.E.genericPoint),
      D.valuation (algebraMap _ X.functionField a) = D.E.divisorialValuation
        (algebraMap D.E.localRing D.Y.functionField ((D.f.stalkMap D.E.genericPoint).hom a)) :=
    fun a => by
      change D.E.divisorialValuation (functionFieldMap D.f _) = _
      rw [MMP.Mori.functionFieldMap_algebraMap_stalk]
  refine ⟨fun a => ?_, fun a ha => ?_⟩
  · rw [happ, MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff]
    exact ⟨_, rfl⟩
  · rw [happ]
    have hm : (D.f.stalkMap D.E.genericPoint).hom a ∈ IsLocalRing.maximalIdeal D.E.localRing :=
      (IsLocalRing.mem_maximalIdeal _).2 fun hu =>
        (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit _ _ hu)
    haveI := D.E.isDiscreteValuationRing_localRing
    exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem
      (IsDiscreteValuationRing.maximalIdeal D.E.localRing) _).2 hm

/-- Domination of local rings passes to the restriction of a valuation along a dominant
morphism. -/
private theorem dominates_comap {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z] (f : Y ⟶ Z)
    [IsDominant f] (w : Valuation Y.functionField ℤᵐ⁰) (y : Y)
    (h : (∀ a : Y.presheaf.stalk y, w (algebraMap _ Y.functionField a) ≤ 1) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y),
        w (algebraMap _ Y.functionField a) < 1) :
    (∀ a : Z.presheaf.stalk (f y),
        (w.comap (functionFieldMap f)) (algebraMap _ Z.functionField a) ≤ 1) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (Z.presheaf.stalk (f y)),
        (w.comap (functionFieldMap f)) (algebraMap _ Z.functionField a) < 1 := by
  refine ⟨fun a => ?_, fun a ha => ?_⟩
  · rw [Valuation.comap_apply, MMP.Mori.functionFieldMap_algebraMap_stalk]
    exact h.1 _
  · rw [Valuation.comap_apply, MMP.Mori.functionFieldMap_algebraMap_stalk]
    exact h.2 _ ((IsLocalRing.mem_maximalIdeal _).2 fun hu =>
      (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit _ a hu))

/-- The valuation of a divisor over `Y`, restricted along a birational dominant `f : Y ⟶ X`, is a
divisor of the function field of `X`. -/
private theorem isDivisorOfFunctionField_comap {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsIntegral Y] (f : Y ⟶ X) [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) (D : DivisorOver k (f ≫ sX)) :
    MMP.Flips.IsDivisorOfFunctionField k sX (D.valuation.comap (functionFieldMap f)) := by
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  letI := MMP.Mori.functionFieldAlgebra sX
  letI := MMP.Mori.functionFieldAlgebra (f ≫ sX)
  letI := MMP.Mori.functionFieldAlgebra (D.f ≫ f ≫ sX)
  letI := MMP.Mori.functionFieldMapAlgebra f
  letI := MMP.Mori.functionFieldMapAlgebra D.f
  haveI := MMP.Mori.isScalarTower_functionFieldMap sX f
  haveI := MMP.Mori.isScalarTower_functionFieldMap (f ≫ sX) D.f
  let e₀ : X.functionField →ₐ[k] D.Y.functionField :=
    (IsScalarTower.toAlgHom k Y.functionField D.Y.functionField).comp
      (IsScalarTower.toAlgHom k X.functionField Y.functionField)
  have he : Function.Bijective e₀ := D.isBirationalMorphism.functionFieldMap_bijective.comp hf
  refine ⟨D.Y, D.f ≫ f ≫ sX, D.isNormalVariety, D.E, AlgEquiv.ofBijective e₀ he, ?_⟩
  ext g
  rfl

end MMP

namespace MMP.Fourfold

section BoundedDenominators

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### Orders along a centred valuation -/

section Hartogs

/-- **Hartogs for a centred valuation.** Let `Y` be normal and `ξ` a valuation of `k(Y)` which is
at most one on `𝒪_{Y,y}`, and let `g_j` be nonzero rational functions with `ξ(g_j) = exp(n_j)`.
If a real combination of the orders of the `g_j` vanishes along every prime divisor through `y`,
the same combination of the `n_j` vanishes. -/
private theorem sum_mul_eq_zero_of_valuation_le_one {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (ξ : Valuation Y.functionField ℤᵐ⁰) {y : Y}
    (hξ : ∀ a : Y.presheaf.stalk y, ξ (algebraMap _ Y.functionField a) ≤ 1)
    {p : Type*} [Fintype p] (g : p → Y.functionField) (hg : ∀ j, g j ≠ 0) (n : p → ℤ)
    (hn : ∀ j, ξ (g j) = WithZero.exp (n j)) (s : p → ℝ)
    (hs : ∀ Γ : MMP.Mori.PrimeDivisor Y, y ∈ Γ.support →
      ∑ j, (Y.ord (g j) Γ.genericPoint : ℝ) * s j = 0) :
    ∑ j, (n j : ℝ) * s j = 0 := by
  classical
  refine MMP.Threefold.Bridges.sum_real_eq_zero_of_int
    (ι := {Γ : MMP.Mori.PrimeDivisor Y // y ∈ Γ.support})
    (fun Γ j => Y.ord (g j) Γ.1.genericPoint) n (fun e he => ?_) s (fun Γ => hs Γ.1 Γ.2)
  set G : Y.functionField := ∏ j, g j ^ e j with hGdef
  have hG : G ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (hg i)
  obtain ⟨t, ht, htG⟩ := MMP.Mori.exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero
    y hG fun Γ hΓ => by
      rw [hGdef, MMP.Threefold.Bridges.ord_prod_zpow _ _ _ hg]
      simpa [mul_comm] using he ⟨Γ, hΓ⟩
  have h1 : ξ G = 1 := htG ▸ Valuation.Integers.one_of_isUnit' (v := ξ) ht hξ
  have h2 : ξ G = WithZero.exp (∑ j, n j * e j) := by
    rw [hGdef, map_prod]
    simp only [map_zpow₀, hn, ← WithZero.exp_zsmul, smul_eq_mul]
    simp [WithZero.exp, ofAdd_sum, ← WithZero.coeMonoidHom_apply, map_prod, mul_comm]
  rw [h1, ← WithZero.exp_zero] at h2
  exact (WithZero.exp_injective h2).symm

end Hartogs

/-! ### Divisors over a surface and their centres -/

section Centres

/-- A divisor over `X` whose centre is a closed point `x` has its generic point over `x`. -/
private theorem map_genericPoint_eq_of_center_eq {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (D : DivisorOver k sX) {x : X}
    (hc : (D.center : Set X) = {x}) : D.f D.E.genericPoint = x := by
  change _ ∈ ({x} : Set X)
  rw [← hc, D.center_eq_closure_genericPoint]
  exact subset_closure rfl

/-- A prime divisor of `Y` lies over the closure of the image of its generic point. -/
private theorem map_mem_closure_of_mem_support {S Y : Scheme.{u}} {f : Y ⟶ S}
    (E : MMP.Mori.PrimeDivisor Y) {z : Y}
    (hz : z ∈ E.support) : f z ∈ closure ({f E.genericPoint} : Set S) := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hz
  exact specializes_iff_mem_closure.mp
    ((specializes_iff_mem_closure.mpr hz).map f.continuous)

open MMP.Flips in
/-- On a surface `S`, an exceptional prime divisor of `f : Y ⟶ S` lies over a closed point. -/
private theorem isClosed_singleton_of_isExceptionalPrimeDivisor {k : Type u} [Field k]
    {S Y : Scheme.{u}} {sS : S ⟶ Spec (.of k)} {f : Y ⟶ S} [IsIntegral S]
    [LocallyOfFiniteType sS] [CompactSpace S] (hS2 : topologicalKrullDim S = 2)
    {E : MMP.Mori.PrimeDivisor Y} (h : IsExceptionalPrimeDivisor sS f E) :
    IsClosed ({f E.genericPoint} : Set S) := by
  obtain ⟨_, _, _, hexc⟩ := h
  set x := f E.genericPoint
  have hx : topologicalKrullDim (closure {x} : Set S) + 2 ≤ 2 := by
    unfold ProperDivisorOver.IsExceptional at hexc
    rwa [ProperDivisorOver.center_eq_toDivisorOver_center,
      DivisorOver.center_eq_closure_genericPoint, hS2] at hexc
  by_contra hn
  obtain ⟨c, -, hxc, hne⟩ := MMP.Mori.exists_isClosed_singleton_specializes hn
  have h1 := one_le_topologicalKrullDim_of_specializes_of_ne
    (x := (⟨x, subset_closure rfl⟩ : closure ({x} : Set S)))
    (y := ⟨c, specializes_iff_mem_closure.mp hxc⟩) ((subtype_specializes_iff _ _).mpr hxc)
    (fun h => hne (congrArg Subtype.val h))
  exact absurd ((add_le_add h1 (le_refl (2 : WithBot ℕ∞))).trans hx) (by decide)

/-- If every coefficient of `D` lies in `(1/c) ℤ`, so does every coefficient of its linear
extension along a partial map of prime divisors. -/
private theorem exists_int_mul_mapPrimeDivisors {X Y : Scheme.{u}} {R : Type*} [CommRing R]
    (φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)) (c : R)
    (D : DivisorWithCoeffs R X)
    (hD : ∀ P, ∃ n : ℤ, c * D P = n) (P : MMP.Mori.PrimeDivisor Y) :
    ∃ n : ℤ, c * DivisorWithCoeffs.mapPrimeDivisors φ D P = n := by
  classical
  induction D using Finsupp.induction with
  | zero => exact ⟨0, by simp⟩
  | single_add a b g ha hb ih =>
    have hga : g a = 0 := Finsupp.notMem_support_iff.mp ha
    obtain ⟨nb, hnb⟩ : ∃ n : ℤ, c * b = n := by
      obtain ⟨n, hn⟩ := hD a
      exact ⟨n, by simpa [hga] using hn⟩
    have hg : ∀ Q, ∃ n : ℤ, c * g Q = n := fun Q => by
      by_cases hQ : Q = a
      · exact ⟨0, by simp [hQ, hga]⟩
      · obtain ⟨n, hn⟩ := hD Q
        exact ⟨n, by simpa [Finsupp.single_apply, Ne.symm hQ] using hn⟩
    obtain ⟨n, hn⟩ := ih hg
    rw [map_add, Finsupp.add_apply, DivisorWithCoeffs.mapPrimeDivisors_single, mul_add, hn]
    rcases φ a with _ | E'
    · exact ⟨n, by simp⟩
    · simp only [Option.elim_some, Finsupp.single_apply]
      split_ifs
      · exact ⟨nb + n, by rw [hnb]; push_cast; ring⟩
      · exact ⟨n, by simp⟩

/-- The linear extension of a partial map of prime divisors preserves effectivity. -/
private theorem mapPrimeDivisors_nonneg {X Y : Scheme.{u}}
    (φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)) (D : QDivisor X)
    (hD : ∀ P, 0 ≤ D P) (P : MMP.Mori.PrimeDivisor Y) :
    0 ≤ DivisorWithCoeffs.mapPrimeDivisors φ D P := by
  classical
  induction D using Finsupp.induction with
  | zero => simp
  | single_add a b g ha hb ih =>
    have hga : g a = 0 := Finsupp.notMem_support_iff.mp ha
    have hb0 : 0 ≤ b := by simpa [hga] using hD a
    have hg : ∀ Q, 0 ≤ g Q := fun Q => by
      by_cases hQ : Q = a
      · subst hQ; rw [hga]
      · have := hD Q
        simpa [Finsupp.single_apply, Ne.symm hQ] using this
    rw [map_add, Finsupp.add_apply, DivisorWithCoeffs.mapPrimeDivisors_single]
    refine add_nonneg ?_ (ih hg)
    rcases φ a with _ | E'
    · simp
    · simp only [Option.elim_some, Finsupp.single_apply]
      split_ifs <;> simp [hb0]

end Centres

/-! ### The denominator of an arbitrary log discrepancy -/

section Denominator

open MMP.Flips

/-- **Denominators of log discrepancies at `x`.** Let `(S, B)` be a pair on a surface over a
field of characteristic zero with `qB` integral, `f : Y ⟶ S` a smooth resolution, `E_1, …, E_s`
the prime divisors of `Y` over the closed point `x`, with log discrepancies `α_i ∈ 1 + (1/D) ℤ`, and
`q ∣ D`. Then every log discrepancy of a divisor over `S` with centre `x` lies in `(1/D) ℤ`. -/
private theorem exists_eq_div_of_isLogDiscrepancy {k : Type u} [Field k] [CharZero k]
    {S Y : Scheme.{u}} {sS : S ⟶ Spec (.of k)} [IsIntegral S] [IsLocallyNoetherian S]
    [IsNormal S] {B : QDivisor S} (hBp : MMP.Mori.IsPair sS B)
    (hS2 : topologicalKrullDim S = 2) {x : S} (hx : IsClosed ({x} : Set S))
    {f : Y ⟶ S} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (hYv : MMP.Mori.IsVariety k (f ≫ sS)) (hres : IsSmoothResolution sS f)
    {s : ℕ} (E : Fin s → MMP.Mori.PrimeDivisor Y)
    (hEall : ∀ P : MMP.Mori.PrimeDivisor Y, P.support ⊆ f.base ⁻¹' {x} → ∃ i, E i = P)
    (α : Fin s → ℝ)
    (hα : ∀ i, MMP.Intersection.IsLogDiscrepancy sS 2 (QDivisor.toRDivisor B)
      ⟨Y, f, ⟨hYv, inferInstance⟩, hres.isBirationalMorphism, E i⟩ (α i))
    {q D : ℕ} (hqD : q ∣ D) (hD : 0 < D) (hqB : ∀ P, ∃ n : ℤ, (q : ℚ) * B.coeff P = n)
    (hαD : ∀ i, ∃ r : ℤ, α i - 1 = r / D)
    (F : DivisorOver k sS) (a : ℝ)
    (ha : MMP.Intersection.IsLogDiscrepancy sS 2 (QDivisor.toRDivisor B) F a)
    (hc : (F.center : Set S) = {x}) : ∃ r : ℤ, a = r / D := by
  classical
  have hsm := hres.isSmoothScheme
  haveI : IsProper f := hres.isProper
  have hf := hres.isBirationalMorphism
  have hSn : IsNormalVariety k sS := hBp.1
  have hYn : IsNormalVariety k (f ≫ sS) := ⟨hYv, inferInstance⟩
  haveI : MMP.Mori.IsVariety k sS := hSn.1
  haveI := hYv
  haveI : LocallyOfFiniteType sS := hSn.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (f ≫ sS) := hYv.toLocallyOfFiniteType
  haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sS)
  haveI : IsDominant f := hf.isDominant
  haveI := F.isIntegral
  haveI := F.isLocallyNoetherian
  haveI := F.isNormal
  haveI := F.isDominant
  have hFx : F.f F.E.genericPoint = x := map_genericPoint_eq_of_center_eq F hc
  -- a rational top form `ω` on `S` and a presentation of `K_S + B`, from `ha`
  obtain ⟨-, hFp, ω, hω0, ⟨K₀, hK₀, hK₀ω⟩, m, r, Cc, -, hCcart, hdec, -, -⟩ := id ha
  haveI : IsProper F.f := hFp
  haveI : CompactSpace F.Y := by
    haveI : QuasiCompact F.f := inferInstance
    exact QuasiCompact.compactSpace_of_compactSpace F.f
  have hdivω : divisorOfForm ω = K₀ :=
    DivisorWithCoeffs.ext' fun Γ => by rw [coeff_divisorOfForm, hK₀ω]
  have hKω : (divisorOfForm ω).IsCanonicalDivisor sS 2 := hdivω ▸ hK₀
  have hcomb : IsCartierCombination
      (Divisor.toRDivisor (divisorOfForm ω) + QDivisor.toRDivisor B) := by
    refine ⟨m, r, Cc, hCcart, Finsupp.ext fun Γ => ?_⟩
    have h := hdec Γ
    simp only [Finsupp.add_apply, Finsupp.coe_finset_sum, Finset.sum_apply,
      Finsupp.smul_apply, smul_eq_mul]
    rw [show (Divisor.toRDivisor (divisorOfForm ω)) Γ = ((Γ.ordForm ω : ℤ) : ℝ) by
      rw [← coeff_divisorOfForm ω Γ]; rfl]
    exact h
  obtain ⟨Ex, a', G, hEx', ⟨m', r', L, L', hLc, hLdec, hLpb, rfl⟩, -, heq⟩ :=
    discrepancy_formula hSn (QDivisor.toRDivisor B) ω hω0 hKω hcomb f hYn hf
  set K' := divisorOfForm (pullbackRationalPluriForms sS f ω) with hK'
  set R : RDivisor Y := ∑ E ∈ Ex, Finsupp.single E (a' E) with hR
  have hLdec' : ∀ Γ : MMP.Mori.PrimeDivisor S, (Γ.ordForm ω : ℝ) + (QDivisor.toRDivisor B).coeff Γ =
      ∑ l, r' l * (L l).coeff Γ := fun Γ => by
    have h := congrArg (fun F : RDivisor S => F Γ) hLdec
    simp only [Finsupp.add_apply, Finsupp.coe_finset_sum, Finset.sum_apply,
      Finsupp.smul_apply, smul_eq_mul] at h
    rw [← coeff_divisorOfForm ω Γ]
    exact h
  -- the log discrepancies in terms of the presentation `(r', L)`
  have hαi : ∀ i, α i = 1 + (K' (E i) : ℝ) - ∑ l, r' l * (L' l (E i) : ℝ) := by
    intro i
    refine MMP.Threefold.Bridges.IsLogDiscrepancy.unique (hα i)
      ⟨hSn, inferInstance, ω, hω0, ⟨K₀, hK₀, hK₀ω⟩, m', r', L, L', hLc, hLdec', hLpb, ?_⟩
    change _ = 1 + ((E i).ordForm (pullbackRationalPluriForms sS f ω) : ℝ) - _
    rw [← coeff_divisorOfForm]
    rfl
  choose L'' hL'' using fun l => MMP.Threefold.Bridges.exists_isPullback_of_isDominant F.f (hLc l)
  have haF : a = 1 + (F.ordPullback ω : ℝ) - ∑ l, r' l * (L'' l F.E : ℝ) :=
    MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha
      ⟨hSn, hFp, ω, hω0, ⟨K₀, hK₀, hK₀ω⟩, m', r', L, L'', hLc, hLdec',
        fun l => ⟨_, hL'' l⟩, rfl⟩
  -- the centre `y` of the valuation of `F` on `Y`
  have hbij : Function.Bijective (functionFieldMap f) := hf.functionFieldMap_bijective
  set e := RingEquiv.ofBijective (functionFieldMap f) hbij with he
  set ξY : Valuation Y.functionField (WithZero (Multiplicative ℤ)) :=
    F.valuation.comap (e.symm : Y.functionField →+* S.functionField) with hξYdef
  have hξY : ∀ g, ξY (functionFieldMap f g) = F.valuation g := fun g => by
    rw [hξYdef, Valuation.comap_apply]
    congr 1
    exact e.symm_apply_apply g
  have hdomS := divisorOver_dominates F hFx
  obtain ⟨y, hyξ, hfy⟩ := MMP.Fourfold.SNCWeight.SNCModel.exists_dominates_of_isProper f ξY x
    ⟨fun a => by rw [Valuation.comap_apply, hξY]; exact hdomS.1 a,
      fun a ha => by rw [Valuation.comap_apply, hξY]; exact hdomS.2 a ha⟩
  have hηx : ∀ P : MMP.Mori.PrimeDivisor Y, y ∈ P.support → f P.genericPoint ⤳ x :=
    fun P hP => by
      rw [← hfy]
      refine (specializes_iff_mem_closure.mpr ?_).map f.continuous
      rwa [← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  -- the crepant boundary has coefficients in `(1/D) ℤ` along the prime divisors through `y`
  have hint : ∀ P : MMP.Mori.PrimeDivisor Y, y ∈ P.support →
      ∃ z : ℤ, (D : ℝ) * ∑ l, r' l * (L' l P : ℝ) = z := by
    intro P hP
    obtain ⟨d₀, rfl⟩ := hqD
    have hDR : ((q * d₀ : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
    by_cases hPEx : P ∈ Ex
    · -- `P` lies over `x`, so it is one of the `E_i`
      have hcl := isClosed_singleton_of_isExceptionalPrimeDivisor hS2 ((hEx' P).mp hPEx)
      have hsub : ∀ z ∈ P.support, f z = f P.genericPoint := fun z hz => by
        have := map_mem_closure_of_mem_support (f := f) P hz
        rwa [hcl.closure_eq] at this
      have hPx : f P.genericPoint = x := by rw [← hsub y hP, hfy]
      obtain ⟨i, rfl⟩ := hEall P fun z hz => by
        change f z ∈ ({x} : Set S)
        rw [hsub z hz, hPx]
        rfl
      obtain ⟨t, ht⟩ := hαD i
      refine ⟨q * d₀ * K' (E i) - t, ?_⟩
      have hsum : ∑ l, r' l * (L' l (E i) : ℝ) = (K' (E i) : ℝ) - t / ((q * d₀ : ℕ) : ℝ) := by
        linarith [hαi i, ht]
      rw [hsum]
      field_simp
      push_cast
      ring
    · -- `P` is not exceptional: the coefficient is that of the strict transform of `B`
      have hRP : R P = 0 := by
        rw [hR, Finsupp.finset_sum_apply]
        exact Finset.sum_eq_zero fun E' hE' =>
          Finsupp.single_eq_of_ne' (fun h => hPEx (h ▸ hE'))
      have h := congrArg (fun F : RDivisor Y => F P) heq
      simp only [Finsupp.add_apply, Finsupp.coe_finset_sum, Finset.sum_apply,
        Finsupp.smul_apply, smul_eq_mul, hRP, add_zero] at h
      obtain ⟨n, hn⟩ := exists_int_mul_mapPrimeDivisors
        (RationalMap.IsBirational.inverse hf).transformPrimeDivisor (q : ℝ)
        (QDivisor.toRDivisor B) (fun Q => by
          obtain ⟨n, hn⟩ := hqB Q
          refine ⟨n, ?_⟩
          change (q : ℝ) * ((B Q : ℚ) : ℝ) = n
          have := congrArg (Rat.cast : ℚ → ℝ) hn
          push_cast at this
          exact this) P
      refine ⟨q * d₀ * K' P + d₀ * n, ?_⟩
      have h2 : (Divisor.toRDivisor K') P = ((K' P : ℤ) : ℝ) := rfl
      have h3 : ∀ l, (Divisor.toRDivisor (L' l)) P = ((L' l P : ℤ) : ℝ) := fun l => rfl
      simp only [h2, h3] at h
      have hn' : (q : ℝ) * (birationalInverseTransform f hf (QDivisor.toRDivisor B)) P = n := hn
      rw [← h]
      push_cast
      linear_combination (d₀ : ℝ) * hn'
  -- the integral divisor `D · f^*(K_S + B)` near `y`, and a local equation `ψ` of it at `y`
  have hfin : (Function.support fun P : MMP.Mori.PrimeDivisor Y =>
      if y ∈ P.support then round ((D : ℝ) * ∑ l, r' l * (L' l P : ℝ)) else 0).Finite := by
    refine (Set.finite_iUnion fun l => (L' l).support.finite_toSet).subset fun P hP => ?_
    by_contra hPn
    simp only [Set.mem_iUnion, Finset.mem_coe, Finsupp.mem_support_iff, not_exists,
      not_not] at hPn
    apply hP
    simp [hPn]
  set Gi : Divisor Y := Finsupp.ofSupportFinite _ hfin with hGi
  have hGiP : ∀ P, y ∈ P.support → ((Gi P : ℤ) : ℝ) = (D : ℝ) * ∑ l, r' l * (L' l P : ℝ) := by
    intro P hP
    obtain ⟨z, hz⟩ := hint P hP
    simp only [hGi, Finsupp.ofSupportFinite_coe, if_pos hP, hz, round_intCast]
  obtain ⟨V', hyV', ψ, hψ⟩ := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm Gi y
  -- local equations `φ_l` of the `L_l` near `x`
  choose V hxV φ hφ using fun l => hLc l x
  choose hB' hpb' using hLpb
  set Zx := MMP.Mori.pointComponent x
  set Zy := MMP.Mori.pointComponent y
  set gS : Fin m' → S.functionField := fun l =>
    MMP.Threefold.Mori.Helpers.evalFF Zx (φ l : MMP.Mori.RationalFunctions S) with hgS
  have hgS0 : ∀ l, gS l ≠ 0 := fun l =>
    ((φ l).isUnit.map (MMP.Threefold.Mori.Helpers.evalFF Zx)).ne_zero
  set h : Y.functionField :=
    MMP.Threefold.Mori.Helpers.evalFF Zy (ψ : MMP.Mori.RationalFunctions Y) with hh
  have hh0 : h ≠ 0 := (ψ.isUnit.map (MMP.Threefold.Mori.Helpers.evalFF Zy)).ne_zero
  set g : Option (Fin m') → Y.functionField := fun j =>
    j.elim h fun l => functionFieldMap f (gS l) with hg
  have hg0 : ∀ j, g j ≠ 0 := by
    rintro (_ | l)
    · exact hh0
    · exact (map_ne_zero _).mpr (hgS0 l)
  set n : Option (Fin m') → ℤ := fun j =>
    j.elim (WithZero.log (ξY h)) fun l =>
      -F.Y.ord (functionFieldMap F.f (gS l)) F.E.genericPoint with hn
  have hn' : ∀ j, ξY (g j) = WithZero.exp (n j) := by
    rintro (_ | l)
    · exact (WithZero.exp_log ((Valuation.ne_zero_iff ξY).mpr hh0)).symm
    · change ξY (functionFieldMap f (gS l)) = _
      rw [hξY]
      change F.E.divisorialValuation (functionFieldMap F.f (gS l)) = _
      exact F.E.divisorialValuation_eq_exp_neg_ord ((map_ne_zero _).mpr (hgS0 l))
  set c : Option (Fin m') → ℝ := fun j => j.elim (-1) fun l => (D : ℝ) * r' l with hc'
  have hzero := sum_mul_eq_zero_of_valuation_le_one ξY hyξ.1 g hg0 n hn' c (fun Γ hΓ => by
    rw [Fintype.sum_option]
    have hΓV : ∀ l, f Γ.genericPoint ∈ V l := fun l =>
      (hηx Γ hΓ).mem_open (V l).isOpen (hxV l)
    have hL : ∀ l, Y.ord (g (some l)) Γ.genericPoint = L' l Γ := fun l =>
      (MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF (hpb' l) (hφ l) Γ (hΓV l) Zx).symm
    have hG : Y.ord (g none) Γ.genericPoint = Gi Γ := by
      have h1 := hψ Γ ⟨y, hΓ, hyV'⟩
      rw [MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord] at h1
      have hZ : Γ.component = Zy :=
        Subsingleton.elim (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents) _ _
      rw [hZ] at h1
      exact h1.symm
    simp only [hc', Option.elim_none, Option.elim_some, hL, hG, hGiP Γ hΓ, Finset.mul_sum]
    rw [mul_neg_one, neg_add_eq_zero]
    exact Finset.sum_congr rfl fun l _ => by ring)
  -- the coefficients of the `L_l` pulled back to the model of `F`
  have hnL : ∀ l, (n (some l) : ℝ) = -(L'' l F.E : ℝ) := fun l => by
    have h1 := MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF (hL'' l) (hφ l) F.E
      (by rw [hFx]; exact hxV l) Zx
    change ((-F.Y.ord (functionFieldMap F.f (gS l)) F.E.genericPoint : ℤ) : ℝ) = _
    rw [← h1]
    push_cast
    rfl
  rw [Fintype.sum_option] at hzero
  simp only [hc', Option.elim_none, Option.elim_some, hnL] at hzero
  have hS1 : (D : ℝ) * ∑ l, r' l * (L'' l F.E : ℝ) = -(n none : ℝ) := by
    have e : ∑ l, -(L'' l F.E : ℝ) * ((D : ℝ) * r' l) =
        -((D : ℝ) * ∑ l, r' l * (L'' l F.E : ℝ)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
    linarith [hzero, e]
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  refine ⟨D * (1 + F.ordPullback ω) + n none, ?_⟩
  rw [haF, eq_div_iff hDR]
  push_cast
  linear_combination (-1 : ℝ) * hS1

end Denominator

/-! ### The canonical divisor of the minimal resolution -/

section MinimalResolution

open MMP.Resolution

/-- If `𝒪_X(D)` is the divisorial sheaf of a Cartier Weil divisor `D'`, then the intersection
number of `D` with a projective curve is the degree of `D'` along it. -/
private theorem cartierCurveIntersection_eq_degreeOn {k : Type u} [Field k] {S : Scheme.{u}}
    {sS : S ⟶ Spec (.of k)} [IsNormal S] [IsLocallyNoetherian S] [QuasiCompact sS]
    {D : S.CartierDivisor} {D' : Divisor S} (hD' : D'.IsCartier)
    (e : MMP.CartierDivisor.sheaf D ≅ D'.divisorialSheaf) (C : ProperCurve sS)
    (hC : IsProjectiveMorphism (C.ι ≫ sS)) :
    cartierCurveIntersection D C = D'.degreeOn k sS C.ι C.dim_le hD' := by
  haveI := QuasiCompact.compactSpace_of_compactSpace sS
  haveI hinv := hD'.isInvertibleModule_divisorialSheaf
  haveI : Stacks.Ample.IsInvertibleModule S (MMP.CartierDivisor.sheaf D) :=
    Stacks.UFDExtensionGlobal.isInvertible_of_iso e.symm hinv
  haveI : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
      (MMP.CartierDivisor.sheaf D) := this
  haveI : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 D'.divisorialSheaf := hinv
  have hcurve : AlgebraicGeometry.IsCurve k (C.ι ≫ sS) :=
    { toIsIntegral := inferInstance
      toIsSeparated := inferInstance
      toLocallyOfFiniteType := inferInstance
      toQuasiCompact := inferInstance
      topologicalKrullDim_eq_one := C.dim_eq }
  have : AlgebraicGeometry.IsProjectiveVariety k (C.ι ≫ sS) :=
    { toIsVariety := hcurve.toIsVariety
      isProjective := hC }
  have : Stacks.Ample.IsInvertibleModule C.scheme
      ((Scheme.Modules.pullback C.ι).obj (MMP.CartierDivisor.sheaf D)) :=
    MMP.Mori.isInvertible_pullback_obj C.ι _
  unfold cartierCurveIntersection lineBundleCurveIntersection
  rw [MMP.Resolution.degree_eq_invertibleCurveDegree (C.ι ≫ sS) _ C.dim_le,
    ← MMP.Mori.degreeOn_eq_invertibleCurveDegree, MMP.Mori.degreeOn_eq_of_iso k sS C.ι C.dim_le e]
  rfl

/-- **`K_Y` is relatively nef on a minimal resolution.** For the minimal resolution `f : Y ⟶ S`
and a nonzero rational `2`-form `ω` on `Y`, the divisor `div(ω)` meets every projective curve
contracted by `f` nonnegatively. -/
private theorem intersectionNumber_divisorOfForm_nonneg {k : Type u} [Field k]
    {S Y : Scheme.{u}} {sS : S ⟶ Spec (.of k)} [IsIntegral Y] [IsNoetherian Y] {f : Y ⟶ S}
    [LocallyOfFiniteType (f ≫ sS)] (hmin : MMP.Resolution.IsMinimalSurfaceResolution sS f)
    [IsNormal Y] [QuasiCompact (f ≫ sS)]
    (ω : RationalPluriForms (f ≫ sS) 2 1) (hω : ω ≠ 0) (C : ProperCurve (f ≫ sS))
    (hC : IsContractedProjectiveCurve (f ≫ sS) f C) :
    0 ≤ (Divisor.toQDivisor (divisorOfForm ω)).intersectionNumber k (f ≫ sS) C.ι C.dim_le
      (MMP.Fourfold.isQCartier_of_isSmoothScheme hmin.1.isSmoothScheme _) := by
  have hf := hmin.1
  haveI hYv : AlgebraicGeometry.IsVariety k sS := hf.isVariety
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hf.isProjectiveMorphism
  haveI hXv : AlgebraicGeometry.IsVariety k (f ≫ sS) := {}
  haveI : IsSmoothVariety k (f ≫ sS) :=
    { toIsVariety := hXv,
      toSmooth := (@isSmoothScheme_iff _ _ _
        (LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance)).mp
          hf.isSmoothScheme }
  obtain ⟨Kc, hKc, hnef⟩ := hmin.2 ω hω
  set B : Divisor Y := divisorOfForm ω
  have hBK : weilDivisorEquivFinsupp (cartierWeilDivisor Kc) = B := by
    ext P
    refine (hKc P).trans ?_
    simp only [divisorOfFormOnSmoothLocus, Finsupp.filter_apply]
    split_ifs with hP
    · rfl
    · refine absurd ⟨AlgebraicGeometry.PrimeDivisor.genericPoint P, ?_, ?_⟩ hP
      · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
      · rw [show smoothLocus (f ≫ sS) = ⊤ from hf.isSmoothScheme]; trivial
  obtain ⟨hcart, -, -, hdict, -, -⟩ :=
    Divisor.cartier_weil_dictionary_of_isSmoothVariety k (f ≫ sS)
  have eB : MMP.CartierDivisor.sheaf Kc ≅ B.divisorialSheaf := by
    have e := (hdict Kc).some
    rw [hBK] at e
    exact e.symm
  have hnefC := hnef C hC
  simp only [curveIntersectionPairing, MMP.Mori.KCartierDivisor.ofCartier,
    MMP.Mori.ProperCurve.cycle, Finsupp.linearCombination_single, LinearMap.smul_apply,
    one_smul] at hnefC
  rw [QDivisor.intersectionNumber_toQDivisor k (f ≫ sS) C.ι C.dim_le B (hcart B),
    ← cartierCurveIntersection_eq_degreeOn (hcart B) eB C hC.1]
  exact_mod_cast hnefC

/-- A proper curve contracted by a projective birational morphism from a surface is a projective
curve: it is the generic point of a prime divisor mapping to a closed point. -/
private theorem isContractedProjectiveCurve_of_isContractedBy {k : Type u} [Field k]
    {S Y : Scheme.{u}} {sS : S ⟶ Spec (.of k)} (hS : AlgebraicGeometry.IsVariety k sS)
    [IsIntegral Y] (f : Y ⟶ S) (hY : AlgebraicGeometry.IsVariety k (f ≫ sS))
    (hdimY : topologicalKrullDim Y = 2) (hproj : IsProjectiveMorphism f)
    (C : ProperCurve (f ≫ sS)) (hC : C.IsContractedBy f) :
    IsContractedProjectiveCurve (f ≫ sS) f C := by
  haveI : LocallyOfFiniteType (f ≫ sS) := hY.toLocallyOfFiniteType
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hproj
  have hCdim : topologicalKrullDim (closure {C.point} : Set Y) = 1 := by
    have h := C.dim_eq
    rw [MMP.Mori.topologicalKrullDim_subscheme_eq] at h
    exact h
  have hco : Order.coheight C.point = 1 := by
    have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (f ≫ sS) C.point
    rw [hCdim, hdimY] at h
    have h' : ((Order.coheight C.point : ℕ∞) : WithBot ℕ∞) = 1 :=
      ENat.WithBot.add_one_cancel.mp (by rw [add_comm]; exact h)
    exact_mod_cast h'
  set G := AlgebraicGeometry.PrimeDivisor.ofCoheightOne C.point hco
  have hG : G.genericPoint = C.point :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  have hsupp : (G.support : Set Y) = closure {C.point} := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, hG]
  have himg : f.base '' (G.support : Set Y) = {f C.point} := by
    rw [hsupp]
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩; exact hC z hz
    · rintro _ rfl; exact ⟨C.point, subset_closure rfl, rfl⟩
  have hcl : IsClosed (f.base '' (G.support : Set Y)) :=
    f.isClosedMap _ (hsupp ▸ isClosed_closure)
  have hP : topologicalKrullDim (closure (f.base '' (G.support : Set Y))) <
      topologicalKrullDim (G.support : Set Y) := by
    rw [hcl.closure_eq, himg, hsupp, hCdim]
    have h0 : topologicalKrullDim ({f C.point} : Set S) ≤ 0 :=
      @topologicalKrullDim_zero_of_discreteTopology _ _
        (@Subsingleton.discreteTopology _ _ (Set.subsingleton_singleton (a := f C.point)).coe_sort)
    exact lt_of_le_of_lt h0 (by decide)
  obtain ⟨C', hC'p, hC'⟩ :=
    exists_isContractedProjectiveCurve_of_isExceptional (sS := f ≫ sS) (sX := sS) hY hdimY hS f
      rfl hproj G hP
  have : C' = C := ProperCurve.ext (hC'p.trans hG)
  exact this ▸ hC'

/-- On the minimal resolution `f : Y ⟶ S` of a surface there is a canonical divisor `K_Y` which is
`f`-nef. -/
private theorem exists_isCanonicalDivisor_isRelativelyNef {k : Type u} [Field k] [CharZero k]
    {S Y : Scheme.{u}} {sS : S ⟶ Spec (.of k)} [IsIntegral Y] [IsNoetherian Y] [IsNormal Y]
    {f : Y ⟶ S} [LocallyOfFiniteType (f ≫ sS)] [QuasiCompact (f ≫ sS)]
    (hmin : MMP.Resolution.IsMinimalSurfaceResolution sS f)
    (hYn : IsNormalVariety k (f ≫ sS)) :
    ∃ K : Divisor Y, K.IsCanonicalDivisor (f ≫ sS) 2 ∧
      (Divisor.toQDivisor K).IsRelativelyNef (f ≫ sS) f := by
  have hf := hmin.1
  have hsm := hf.isSmoothScheme
  haveI : AlgebraicGeometry.IsVariety k (f ≫ sS) := hYn.1
  obtain ⟨K, hK⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (f ≫ sS) hsm
    (n := 2) hf.dim_source_eq
  obtain ⟨ω, hω0, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hYn hK
  have hdiv : divisorOfForm ω = K :=
    DivisorWithCoeffs.ext' fun Γ => by rw [coeff_divisorOfForm, hωK]
  refine ⟨K, hK, MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg (f ≫ sS)
    (MMP.Fourfold.isQCartier_of_isSmoothScheme hsm _) fun C hC => ?_⟩
  have hC' := isContractedProjectiveCurve_of_isContractedBy hf.isVariety f hYn.1
    hf.dim_source_eq hf.isProjectiveMorphism C hC
  have := intersectionNumber_divisorOfForm_nonneg hmin ω hω0 C hC'
  rwa [MMP.Fourfold.intersectionNumber_congr (f ≫ sS) C.ι C.dim_le _ _
    (by rw [hdiv])] at this

end MinimalResolution

/-! ### The prime divisors over the point -/

section Fibre

variable {k : Type u} [Field k] {S Y : Scheme.{u}}

/-- A prime divisor of `Y` lying over a point `x` of `S` has its generic point over `x`. -/
private theorem map_genericPoint_eq_of_support_subset {f : Y ⟶ S} {x : S}
    {E : MMP.Mori.PrimeDivisor Y} (hE : E.support ⊆ f.base ⁻¹' {x}) : f E.genericPoint = x :=
  hE (by rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl)

/-- On a surface integral and locally of finite type over `k`, a prime divisor is a curve. -/
private theorem topologicalKrullDim_idealSheaf_subscheme (sY : Y ⟶ Spec (.of k)) [IsIntegral Y]
    [LocallyOfFiniteType sY] [IsLocallyNoetherian Y] [IsNormal Y]
    (hdim : topologicalKrullDim Y = 2) (E : MMP.Mori.PrimeDivisor Y) :
    topologicalKrullDim E.idealSheaf.subscheme = 1 := by
  rw [MMP.Mori.topologicalKrullDim_subscheme_eq]
  change topologicalKrullDim (E.support : Set Y) = 1
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY E.genericPoint
  rw [E.coheight_genericPoint, hdim] at h
  exact ENat.WithBot.add_one_cancel.mp h

/-- A prime divisor of `Y` lying over a closed point of `S` is proper over `k`. -/
private theorem isProper_idealSheaf_subschemeι (sS : S ⟶ Spec (.of k)) (f : Y ⟶ S)
    [LocallyOfFiniteType sS] [IsProper f] [IsLocallyNoetherian Y] [IsNormal Y]
    {x : S} (hx : IsClosed ({x} : Set S)) (E : MMP.Mori.PrimeDivisor Y)
    (hE : E.support ⊆ f.base ⁻¹' {x}) :
    IsProper (E.idealSheaf.subschemeι ≫ f ≫ sS) := by
  haveI := E.integral
  have := MMP.Mori.isProper_comp_of_range_subset_singleton sS (E.idealSheaf.subschemeι ≫ f) hx
    (by
      rintro _ ⟨z, rfl⟩
      have hz : E.idealSheaf.subschemeι z ∈ (E.support : Set Y) := by
        change _ ∈ (E.idealSheaf.support : Set Y)
        rw [← Scheme.IdealSheafData.range_subschemeι]
        exact ⟨z, rfl⟩
      exact hE hz)
  rwa [Category.assoc] at this

/-- A prime divisor of a surface `Y` lying over a closed point of `S` is a proper curve of `Y`
contracted by `f`. -/
private theorem exists_properCurve (sS : S ⟶ Spec (.of k)) (f : Y ⟶ S)
    [LocallyOfFiniteType sS] [IsProper f] [IsIntegral Y] [LocallyOfFiniteType (f ≫ sS)]
    [IsLocallyNoetherian Y] [IsNormal Y] (hdim : topologicalKrullDim Y = 2)
    {x : S} (hx : IsClosed ({x} : Set S)) (E : MMP.Mori.PrimeDivisor Y)
    (hE : E.support ⊆ f.base ⁻¹' {x}) :
    ∃ C : ProperCurve (f ≫ sS), C.point = E.genericPoint ∧ C.IsContractedBy f := by
  have h := vanishingIdeal_closure_genericPoint_eq_idealSheaf E
  have hcl : closure ({E.genericPoint} : Set Y) = E.support :=
    (AlgebraicGeometry.PrimeDivisor.support_eq_closure E).symm
  refine ⟨⟨E.genericPoint, ⟨?_, ?_⟩⟩, rfl, fun z hz => ?_⟩
  · change topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal _).subscheme = 1
    rw [h]; exact topologicalKrullDim_idealSheaf_subscheme (f ≫ sS) hdim E
  · change IsProper ((Scheme.IdealSheafData.vanishingIdeal _).subschemeι ≫ f ≫ sS)
    rw [h]; exact isProper_idealSheaf_subschemeι sS f hx E hE
  · change z ∈ closure ({E.genericPoint} : Set Y) at hz
    rw [hcl] at hz
    exact (hE hz).trans (map_genericPoint_eq_of_support_subset hE).symm

/-- The prime divisors of `Y` lying over a point `x` which is not the image of the generic point
are finitely many. -/
private theorem finite_setOf_support_subset [IsIntegral Y] [IsLocallyNoetherian Y]
    [CompactSpace Y] (f : Y ⟶ S) {x : S} (hx : IsClosed ({x} : Set S))
    (hη : f (genericPoint Y) ≠ x) :
    {P : MMP.Mori.PrimeDivisor Y | P.support ⊆ f.base ⁻¹' {x}}.Finite := by
  haveI : AlgebraicGeometry.IsNoetherian Y := ⟨⟩
  set U : Y.Opens := ⟨(f.base ⁻¹' {x})ᶜ, (hx.preimage f.continuous).isOpen_compl⟩
  have hηU : genericPoint Y ∈ U := hη
  refine Set.Finite.of_finite_image
    ((MMP.Mori.finite_coheight_eq_one_mem_closure_notMem (genericPoint Y) U hηU).subset ?_)
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective.injOn
  rintro - ⟨P, hP, rfl⟩
  refine ⟨by rw [(genericPoint_spec Y).def]; trivial, fun hmem => hmem ?_,
    P.coheight_genericPoint⟩
  exact map_genericPoint_eq_of_support_subset hP

/-- Distinct prime divisors of `Y` give distinct divisorial valuations of `k(S)` through a
birational morphism `f : Y ⟶ S`. -/
private theorem eq_of_valuation_eq {sS : S ⟶ Spec (.of k)} [IsIntegral S] {f : Y ⟶ S}
    (hYv : IsNormalVariety k (f ≫ sS)) (hf : IsBirationalMorphism f)
    {P Q : MMP.Mori.PrimeDivisor Y}
    (h : (⟨Y, f, hYv, hf, P⟩ : DivisorOver k sS).valuation =
      (⟨Y, f, hYv, hf, Q⟩ : DivisorOver k sS).valuation) :
    P = Q := by
  haveI : IsIntegral Y := hYv.1.toIsIntegral
  haveI : IsNormal Y := hYv.2
  haveI : LocallyOfFiniteType (f ≫ sS) := hYv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sS)
  haveI : IsDominant f := hf.isDominant
  have hdiv : P.divisorialValuation = Q.divisorialValuation := by
    ext g
    obtain ⟨g, rfl⟩ := hf.functionFieldMap_bijective.2 g
    exact congrArg (fun v => v g) h
  have hv : (DivisorOver.ofPrimeDivisor k hYv P).valuation =
      (DivisorOver.ofPrimeDivisor k hYv Q).valuation := by
    ext g
    change P.divisorialValuation (functionFieldMap (𝟙 Y) g) =
      Q.divisorialValuation (functionFieldMap (𝟙 Y) g)
    rw [hdiv]
  have := MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hYv.1 hv
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective this

/-- The centre of a prime divisor of `Y` lying over a closed point `x` is `x`. -/
private theorem center_eq_singleton {sS : S ⟶ Spec (.of k)} {f : Y ⟶ S}
    (hYv : IsNormalVariety k (f ≫ sS)) (hf : IsBirationalMorphism f)
    {x : S} (hx : IsClosed ({x} : Set S)) {P : MMP.Mori.PrimeDivisor Y}
    (hP : P.support ⊆ f.base ⁻¹' {x}) :
    ((⟨Y, f, hYv, hf, P⟩ : DivisorOver k sS).center : Set S) = {x} := by
  rw [DivisorOver.center_eq_closure_genericPoint]
  change closure {f P.genericPoint} = _
  rw [map_genericPoint_eq_of_support_subset hP, hx.closure_eq]

end Fibre

/-! ### Linear algebra of the normalized matrix -/

section LinearAlgebra

open Matrix

/-- A `2 × 2` principal minor of a positive definite real matrix is positive. -/
private theorem mul_lt_mul_of_posDef {s : ℕ} {A : Matrix (Fin s) (Fin s) ℝ} (hA : A.PosDef)
    {i j : Fin s} (hij : i ≠ j) : A i j * A j i < A i i * A j j := by
  have hsymm : A j i = A i j := by
    have := congrFun (congrFun hA.1 i) j
    simpa using this
  have hii : 0 < A i i := hA.diag_pos
  set v : Fin s → ℝ := Pi.single i (A i j) + Pi.single j (-A i i) with hv
  have hv0 : v ≠ 0 := by
    intro h
    have := congrFun h j
    simp [hv, Pi.single_apply, hij.symm] at this
    linarith
  have hq := hA.dotProduct_mulVec_pos hv0
  have hval : star v ⬝ᵥ (A *ᵥ v) = A i i * (A i i * A j j - A i j * A j i) := by
    simp only [star_trivial, hv, Matrix.mulVec_add, dotProduct_add, add_dotProduct,
      Matrix.mulVec_single, single_dotProduct, dotProduct_single]
    simp [Pi.single_apply, hij, hij.symm, hsymm]
    ring
  rw [hval] at hq
  nlinarith [(mul_pos_iff_of_pos_left hii).mp hq]

/-- **Entries of a normalized intersection matrix.** Let `M` be an integral matrix, symmetrizable
by positive weights `d`, with positive principal `2 × 2` minors, diagonal entries `≤ -1` and
nonnegative off-diagonal entries. If every `-M_ii` is at most `b`, every entry has absolute value
at most `b²`. -/
private theorem abs_le_sq_of_symmetrizable {s : ℕ} (M : Matrix (Fin s) (Fin s) ℤ) (d : Fin s → ℝ)
    (hd : ∀ i, 0 < d i) (hsymm : ∀ i j, d i * M i j = d j * M j i)
    (hminor : ∀ i j, i ≠ j → (M i j : ℝ) * M j i < M i i * M j j)
    (hdiag : ∀ i, 1 ≤ -M i i) (hoff : ∀ i j, i ≠ j → 0 ≤ M i j) {b : ℝ}
    (hb : ∀ i, (-M i i : ℝ) ≤ b) (i j : Fin s) : |(M i j : ℝ)| ≤ b ^ 2 := by
  have hdiagR : ∀ i, (1 : ℝ) ≤ -M i i := fun i => by exact_mod_cast hdiag i
  have hb1 : 1 ≤ b := (hdiagR i).trans (hb i)
  obtain rfl | hij := eq_or_ne i j
  · rw [abs_of_neg (by linarith [hdiagR i])]
    nlinarith [hb i]
  rcases (hoff i j hij).eq_or_lt with h | h
  · rw [← h]; simp; positivity
  have hji : (0 : ℝ) < M j i :=
    pos_of_mul_pos_right (hsymm i j ▸ mul_pos (hd i) (by exact_mod_cast h)) (hd j).le
  have h1 : (1 : ℝ) ≤ M i j := by exact_mod_cast h
  have hji1 : (1 : ℝ) ≤ M j i := by exact_mod_cast (show (0 : ℤ) < M j i by exact_mod_cast hji)
  rw [abs_of_pos (by linarith)]
  nlinarith [hminor i j hij, hb i, hb j, hdiagR i, hdiagR j,
    mul_le_mul (hb i) (hb j) (by linarith [hdiagR j]) (by linarith)]

/-- **The Leibniz bound.** An integral `s × s` matrix with `s ≤ N` and entries bounded by
`C ≥ 1` has `|det M| ≤ N! C^N`. -/
private theorem natAbs_det_le {s N C : ℕ} (hs : s ≤ N) (hC : 1 ≤ C)
    (M : Matrix (Fin s) (Fin s) ℤ) (hM : ∀ i j, |M i j| ≤ C) :
    M.det.natAbs ≤ N.factorial * C ^ N := by
  have h1 := Matrix.det_le (abv := AbsoluteValue.abs) hM
  simp only [AbsoluteValue.abs_apply, Fintype.card_fin, nsmul_eq_mul] at h1
  have h2 : s.factorial * C ^ s ≤ N.factorial * C ^ N :=
    Nat.mul_le_mul (Nat.factorial_le hs) (Nat.pow_le_pow_right hC hs)
  zify
  exact h1.trans (by exact_mod_cast h2)

/-- **Cramer's rule.** If `M` is an invertible integral matrix and every entry of `M c` lies in
`(1/q) ℤ`, then every entry of `c` lies in `(1/(q |det M|)) ℤ`. -/
private theorem exists_eq_div_of_mulVec {s q : ℕ} (hq : 0 < q) (M : Matrix (Fin s) (Fin s) ℤ)
    (hdet : M.det ≠ 0) (c : Fin s → ℝ) (hc : ∀ i, ∃ n : ℤ, ∑ j, (M i j : ℝ) * c j = n / q)
    (i : Fin s) : ∃ r : ℤ, c i = r / (q * M.det.natAbs) := by
  choose n hn using hc
  set A : Matrix (Fin s) (Fin s) ℝ := M.map (Int.cast : ℤ → ℝ) with hA
  have hAc : A *ᵥ c = fun i => (n i : ℝ) / q := by
    funext i; rw [← hn i]; rfl
  have hadj : A.adjugate = M.adjugate.map (Int.cast : ℤ → ℝ) :=
    ((Int.castRingHom ℝ).map_adjugate M).symm
  have hdetA : A.det = (M.det : ℝ) := ((Int.castRingHom ℝ).map_det M).symm
  have key : A.det • c = A.adjugate *ᵥ (A *ᵥ c) := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hi := congrFun key i
  rw [hAc, hadj, hdetA] at hi
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.map_apply] at hi
  set T : ℤ := ∑ j, M.adjugate i j * n j with hT
  have hTR : ((T : ℤ) : ℝ) = ∑ j, (M.adjugate i j : ℝ) * n j := by rw [hT]; push_cast; rfl
  have hsum : ∑ j, (M.adjugate i j : ℝ) * ((n j : ℝ) / q) = (T : ℝ) / q := by
    rw [hTR, Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsum] at hi
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  generalize M.det = d at *
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hdet
  have hi' : (d : ℝ) * c i * q = T := by rw [hi]; field_simp
  have hci : c i = (T : ℝ) / (q * (d : ℝ)) := by
    rw [eq_div_iff (mul_ne_zero hqR hdR)]; linear_combination hi'
  rw [Nat.cast_natAbs, Int.cast_abs]
  rcases le_or_gt 0 (d : ℝ) with h | h
  · exact ⟨T, by rw [hci, abs_of_nonneg h]⟩
  · exact ⟨-T, by rw [hci, abs_of_neg h, Int.cast_neg]; ring⟩

/-- **Entry bound from the log discrepancies.** For a matrix as in
`abs_le_sq_of_symmetrizable` with `δ ≤ α_i` and `α_i (-M_ii) ≤ 2`, every entry has absolute value
at most `⌈4/δ²⌉`. -/
private theorem abs_le_ceil_four_div_sq {s : ℕ} (M : Matrix (Fin s) (Fin s) ℤ) (d : Fin s → ℝ)
    (hd : ∀ i, 0 < d i) (hsymm : ∀ i j, d i * M i j = d j * M j i)
    (hminor : ∀ i j, i ≠ j → (M i j : ℝ) * M j i < M i i * M j j)
    (hdiag : ∀ i, 1 ≤ -M i i) (hoff : ∀ i j, i ≠ j → 0 ≤ M i j) {δ : ℚ} (hδ0 : 0 < δ)
    {α : Fin s → ℝ} (hδα : ∀ i, (δ : ℝ) ≤ α i) (hα : ∀ i, α i * (-M i i : ℝ) ≤ 2)
    (i j : Fin s) : |M i j| ≤ (⌈(4 : ℚ) / δ ^ 2⌉₊ : ℤ) := by
  set Cb := ⌈(4 : ℚ) / δ ^ 2⌉₊ with hCb
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ0
  have hC : (4 : ℝ) / (δ : ℝ) ^ 2 ≤ Cb := by
    have h := Nat.le_ceil ((4 : ℚ) / δ ^ 2)
    have h' : (((4 : ℚ) / δ ^ 2 : ℚ) : ℝ) ≤ ((Cb : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    exact h'
  have hb : ∀ i, (-M i i : ℝ) ≤ 2 / δ := fun i => by
    rw [le_div_iff₀ hδR]
    nlinarith [hδα i, hα i, (show (1 : ℝ) ≤ -M i i by exact_mod_cast hdiag i)]
  have h := abs_le_sq_of_symmetrizable M d hd hsymm hminor hdiag hoff hb i j
  have e : (2 / (δ : ℝ)) ^ 2 = 4 / δ ^ 2 := by ring
  exact_mod_cast h.trans (e ▸ hC)

end LinearAlgebra

/-! ### The minimal log discrepancy from the denominators -/

/-- If every log discrepancy of a divisor centred at the closed point `x` lies in `(1/D) ℤ` and is
at least `δ > 0`, then the minimal log discrepancy at `x`, when it lies in `[δ, 1]`, is `r / D`. -/
private theorem exists_minimalLogDiscrepancy_eq_div_of_le_one {k : Type u} [Field k]
    {S : Scheme.{u}} {sS : S ⟶ Spec (.of k)} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    {B : QDivisor S} (hS2 : topologicalKrullDim S = 2) {x : S} (hx : IsClosed ({x} : Set S))
    {δ : ℚ} (hδ0 : 0 < δ)
    (hδ : ∀ (E : DivisorOver k sS) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sS 2 (QDivisor.toRDivisor B) E a →
        (E.center : Set S) = {x} → (δ : ℝ) ≤ a)
    {D : ℕ} (hD : 1 ≤ D)
    (hden : ∀ (E : DivisorOver k sS) (a : ℝ),
        MMP.Intersection.IsLogDiscrepancy sS 2 (QDivisor.toRDivisor B) E a →
          (E.center : Set S) = {x} → ∃ r : ℤ, a = r / D)
    (hle : minimalLogDiscrepancy sS B x ≤ 1) :
    ∃ r : ℤ, minimalLogDiscrepancy sS B x = (((r : ℝ) / D : ℝ) : EReal) := by
  classical
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  set T : Set EReal := {t : EReal | ∃ (n : ℕ) (E : DivisorOver k sS) (a : ℝ),
    MMP.Intersection.IsLogDiscrepancy sS n (QDivisor.toRDivisor B) E a ∧
      (E.center : Set S) = closure {x} ∧ t = a} with hT
  have hmld : minimalLogDiscrepancy sS B x = sInf T := rfl
  -- every element of `T` is `m / D` for a positive integer `m`
  have hTm : ∀ t ∈ T, ∃ m : ℕ, 0 < m ∧ t = (((m : ℝ) / D : ℝ) : EReal) := by
    rintro t ⟨n, E, a, ha, hc, rfl⟩
    have hn : n = 2 := by
      have h := (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha).symm.trans hS2
      exact_mod_cast h
    subst hn
    rw [hx.closure_eq] at hc
    obtain ⟨r, hr⟩ := hden E a ha hc
    have hδa := hδ E a ha hc
    have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ0
    have hr0 : (0 : ℝ) < r := by
      have : (0 : ℝ) < r / D := hr ▸ hδR.trans_le hδa
      exact (div_pos_iff_of_pos_right hDpos).mp this
    have hr0' : 0 < r := by exact_mod_cast hr0
    refine ⟨r.toNat, by omega, ?_⟩
    rw [hr]
    congr 2
    exact_mod_cast (Int.toNat_of_nonneg hr0'.le).symm
  -- `T` is nonempty, since its infimum is at most one
  have hne : T.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [hmld, h, sInf_empty] at hle
    exact absurd hle (not_le.mpr (by exact_mod_cast EReal.coe_lt_top 1))
  obtain ⟨t₀, ht₀⟩ := hne
  have hP : ∃ m : ℕ, (((m : ℝ) / D : ℝ) : EReal) ∈ T := by
    obtain ⟨m, -, rfl⟩ := hTm t₀ ht₀
    exact ⟨m, ht₀⟩
  refine ⟨Nat.find hP, ?_⟩
  rw [hmld]
  have hleast : IsLeast T (((Nat.find hP : ℝ) / D : ℝ) : EReal) := by
    refine ⟨Nat.find_spec hP, fun t ht => ?_⟩
    obtain ⟨m, -, rfl⟩ := hTm t ht
    have hm : Nat.find hP ≤ m := Nat.find_min' hP ht
    exact EReal.coe_le_coe_iff.mpr
      (div_le_div_of_nonneg_right (by exact_mod_cast hm) hDpos.le)
  rw [hleast.csInf_eq, Int.cast_natCast]

/-! ### The quasi-projective case -/

/-- An integral scheme of dimension `2` is not the closure of a closed point. -/
private theorem genericPoint_ne_of_topologicalKrullDim_eq_two {S : Scheme.{u}} [IsIntegral S]
    (hS2 : topologicalKrullDim S = 2) {x : S} (hx : IsClosed ({x} : Set S)) :
    genericPoint S ≠ x := by
  intro h
  have hu : (Set.univ : Set S) = {x} := by
    rw [← hx.closure_eq, ← h]
    exact (genericPoint_spec S).def.symm
  haveI : Subsingleton S := ⟨fun a b => by
    have ha : a ∈ ({x} : Set S) := hu ▸ Set.mem_univ a
    have hb : b ∈ ({x} : Set S) := hu ▸ Set.mem_univ b
    exact ha.trans hb.symm⟩
  haveI : DiscreteTopology S := Subsingleton.discreteTopology
  have h0 := topologicalKrullDim_zero_of_discreteTopology S
  rw [hS2] at h0
  exact absurd h0 (by decide)

/-- A negative definite matrix `N_{ij} = d_i M_{ij}` that is symmetric has `d_i > 0`, positive
principal `2 × 2` minors of `M`, and `d_i M_{ij} = d_j M_{ji}`. -/
private theorem symmetrizable_of_posDef_neg {s : ℕ} {Nm : Fin s → Fin s → ℚ} {d : Fin s → ℕ}
    {M : Matrix (Fin s) (Fin s) ℤ} (hNM : ∀ i j, Nm i j = (d i : ℚ) * M i j)
    (hsymm : ∀ i j, Nm i j = Nm j i) (hneg : (-Matrix.of fun i j => (Nm i j : ℝ)).PosDef) :
    (∀ i, (0 : ℝ) < d i) ∧ (∀ i j, i ≠ j → (M i j : ℝ) * M j i < M i i * M j j) ∧
      ∀ i j, (d i : ℝ) * M i j = d j * M j i := by
  have hNii : ∀ i, Nm i i < 0 := fun i => by
    have h := hneg.diag_pos (i := i)
    simp only [Matrix.neg_apply, Matrix.of_apply, neg_pos] at h
    exact_mod_cast h
  have hdR : ∀ i, (0 : ℝ) < d i := fun i => by
    exact_mod_cast Nat.pos_of_ne_zero fun h0 =>
      (hNii i).ne (by rw [hNM, h0, Nat.cast_zero, zero_mul])
  refine ⟨hdR, fun i j hij => ?_, fun i j => ?_⟩
  · have h := mul_lt_mul_of_posDef hneg hij
    have e : ∀ a b, ((Nm a b : ℚ) : ℝ) = (d a : ℝ) * M a b := fun a b => by
      rw [hNM]
      push_cast
      ring
    simp only [Matrix.neg_apply, Matrix.of_apply, neg_mul_neg, e] at h
    have h' : (d i * d j : ℝ) * ((M i j : ℝ) * M j i) < (d i * d j : ℝ) * (M i i * M j j) := by
      linarith
    exact lt_of_mul_lt_mul_left h' (mul_pos (hdR i) (hdR j)).le
  · have h := congrArg (fun t : ℚ => (t : ℝ)) (hsymm i j)
    simp only [hNM] at h
    exact_mod_cast h

/-- **Bounded denominators on a quasi-projective surface.** On a quasi-projective klt surface,
under the hypotheses of `exists_denominator_logDiscrepancy_le`, there is `1 ≤ D ≤ q N! C^N`,
`C = ⌈4/δ²⌉`, such that every log discrepancy of a divisor centred at `x` lies in `(1/D) ℤ`. -/
private theorem exists_denominator_of_isQuasiProjectiveVariety {k : Type u} [Field k]
    {S : Scheme.{u}} {sS : S ⟶ Spec (.of k)} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    [IsQuasiProjectiveVariety k sS]
    {B : QDivisor S} (hB : IsCharZeroKltPair sS B) (hS2 : topologicalKrullDim S = 2)
    {x : S} (hx : IsClosed ({x} : Set S))
    {q N : ℕ} (hq : 1 ≤ q) (hqB : ∀ P, ∃ n : ℤ, (q : ℚ) * B.coeff P = n)
    {δ : ℚ} (hδ0 : 0 < δ)
    (hδ : ∀ (E : DivisorOver k sS) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sS 2 (QDivisor.toRDivisor B) E a →
        (E.center : Set S) = {x} → (δ : ℝ) ≤ a)
    (hlow : {v : Valuation S.functionField (WithZero (Multiplicative ℤ)) |
      ∃ (E : DivisorOver k sS) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sS 2 (QDivisor.toRDivisor B) E a ∧
        (E.center : Set S) = {x} ∧ a ≤ 1 ∧ E.valuation = v}.encard ≤ N) :
    ∃ D : ℕ, 1 ≤ D ∧ D ≤ q * N.factorial * ⌈(4 : ℚ) / δ ^ 2⌉₊ ^ N ∧
      (∀ (E : DivisorOver k sS) (a : ℝ),
        MMP.Intersection.IsLogDiscrepancy sS 2 (QDivisor.toRDivisor B) E a →
          (E.center : Set S) = {x} → ∃ r : ℤ, a = r / D) := by
  classical
  haveI := hB.1.charZero
  have hBp : MMP.Mori.IsPair sS B := hB.1.isPair
  have hX : IsNormalVariety k sS := hBp.isNormalVariety
  haveI hSv : AlgebraicGeometry.IsVariety k sS := hX.1
  haveI : LocallyOfFiniteType sS := hSv.toLocallyOfFiniteType
  haveI : QuasiCompact sS := hSv.toQuasiCompact
  haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
  -- the minimal resolution `f : Y ⟶ S`
  obtain ⟨Y, hYi, hYn, f, hft, hmin, -⟩ := MMP.Resolution.exists_isMinimalSurfaceResolution sS hS2
  have hf := hmin.1
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hf.isProjectiveMorphism
  have hsm : IsSmoothScheme (f ≫ sS) := hf.isSmoothScheme
  have hres : IsSmoothResolution sS f := ⟨inferInstance, hf.isBirationalMorphism, hsm⟩
  obtain ⟨hYv, -, -⟩ := hres.isNormalVariety hX
  haveI : IsNormal Y := hYv.2
  haveI : QuasiCompact (f ≫ sS) := hYv.1.toQuasiCompact
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sS)
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sS)
  haveI : IsDominant f := hf.isBirationalMorphism.isDominant
  have hdimY : topologicalKrullDim Y = 2 := hf.dim_source_eq
  have hKnef := exists_isCanonicalDivisor_isRelativelyNef hmin hYv
  -- the prime divisors `E_1, …, E_s` of `Y` over `x`
  have hηx : f (genericPoint Y) ≠ x := by
    rw [map_genericPoint_of_isDominant]
    exact genericPoint_ne_of_topologicalKrullDim_eq_two hS2 hx
  have hfin := finite_setOf_support_subset f hx hηx
  set T := hfin.toFinset
  set s := T.card
  let E : Fin s → MMP.Mori.PrimeDivisor Y := fun i => (T.equivFin.symm i).1
  have hEinj : Function.Injective E := fun i j h =>
    T.equivFin.symm.injective (Subtype.ext h)
  have hEx : ∀ i, (E i).support ⊆ f.base ⁻¹' {x} := fun i =>
    (Set.Finite.mem_toFinset hfin).mp (T.equivFin.symm i).2
  have hEall : ∀ P : MMP.Mori.PrimeDivisor Y, P.support ⊆ f.base ⁻¹' {x} → ∃ i, E i = P :=
    fun P hP => ⟨T.equivFin ⟨P, (Set.Finite.mem_toFinset hfin).mpr hP⟩, by simp [E]⟩
  -- their log discrepancies `α_i`
  let DE : Fin s → DivisorOver k sS := fun i =>
    ⟨Y, f, ⟨hYv.1, inferInstance⟩, hres.isBirationalMorphism, E i⟩
  have hαex : ∀ i, ∃ a : ℝ, MMP.Intersection.IsLogDiscrepancy sS 2 (QDivisor.toRDivisor B)
      (DE i) a := by
    intro i
    obtain ⟨-, n, K, hK, -⟩ := id hBp
    obtain rfl : n = 2 := by exact_mod_cast hK.topologicalKrullDim_eq.symm.trans hS2
    obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hBp hK (DE i)
    exact ⟨1 + c, (MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy hc _).2
      ⟨inferInstanceAs (IsProper f), rfl⟩⟩
  choose α hα using hαex
  -- the normalized intersection matrix
  obtain ⟨M, β, hMint, -, hαb, hdet, hdiag, hoff, hident, hint⟩ :=
    IsCharZeroKltPair.exists_int_normalized_intersectionMatrix hB hS2 hx hYv.1 hres
      hf.isProjectiveMorphism hKnef E hEinj hEx hEall α hα
  set d : Fin s → ℕ := fun i => Module.finrank k
    (cohomologyOverField k ((E i).idealSheaf.subschemeι ≫ f ≫ sS)
      (SheafOfModules.unit (E i).idealSheaf.subscheme.ringCatSheaf) 0)
  -- `δ ≤ α_i ≤ 1`, so there are at most `N` prime divisors over `x`
  have hcen : ∀ i, ((DE i).center : Set S) = {x} := fun i =>
    center_eq_singleton ⟨hYv.1, inferInstance⟩ hres.isBirationalMorphism hx (hEx i)
  have hδα : ∀ i, (δ : ℝ) ≤ α i := fun i => hδ (DE i) (α i) (hα i) (hcen i)
  have hsN : s ≤ N := by
    have h1 : (Set.univ : Set (Fin s)).encard ≤ N := by
      refine le_trans (Set.encard_le_encard_of_injOn (f := fun i => (DE i).valuation)
        ?_ (fun i _ j _ h => hEinj (eq_of_valuation_eq _ _ h))) hlow
      exact fun i _ => ⟨DE i, α i, hα i, hcen i, (hαb i).2, rfl⟩
    rw [Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin] at h1
    exact_mod_cast h1
  -- the intersection matrix of the `E_i` is negative definite
  choose C hC hCc using fun i => exists_properCurve sS f hdimY hx (E i) (hEx i)
  set Nm : Fin s → Fin s → ℚ := fun i j =>
    (Divisor.toQDivisor (Finsupp.single (E i) 1)).intersectionNumber k (f ≫ sS) (C j).ι
      (C j).dim_le (MMP.Threefold.Mori.isQCartier_single_of_isSmoothScheme hsm (E i))
  have hNM : ∀ i j, Nm i j = (d i : ℚ) * M i j := fun i j =>
    (MMP.Mori.isIntersectionNumber_of_properCurve _ _ (C j) (E j) (hC j)).unique (hMint i j)
  have hneg := MMP.Threefold.Resolution.posDef_neg_intersectionMatrix_of_isBirationalMorphism
    hYv.1 hsm hdimY hSv rfl hres.isBirationalMorphism E hEinj C hC hCc
  have hsymm : ∀ i j, Nm i j = Nm j i := fun i j =>
    MMP.Threefold.Resolution.intersectionNumber_single_comm hsm (E j) (E i) (C j) (C i)
      (hC j) (hC i)
  obtain ⟨hdR, hminor, hsymmM⟩ := symmetrizable_of_posDef_neg hNM hsymm hneg
  -- the entries of `M'` are bounded by `C = ⌈4 / δ²⌉`
  set Cb := ⌈(4 : ℚ) / δ ^ 2⌉₊
  have hbound : ∀ i j, |M i j| ≤ (Cb : ℤ) :=
    abs_le_ceil_four_div_sq M _ hdR hsymmM hminor hdiag hoff hδ0 hδα fun i => (hident i).2
  have hC1 : 1 ≤ Cb := Nat.one_le_ceil_iff.mpr (by positivity)
  -- `D = q |det M'|`
  have hdet1 : 1 ≤ M.det.natAbs := Int.natAbs_pos.mpr hdet
  refine ⟨q * M.det.natAbs, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)),
    ?_, ?_⟩
  · simpa only [mul_assoc] using Nat.mul_le_mul_left q (natAbs_det_le hsN hC1 M hbound)
  · intro F a ha hc
    refine exists_eq_div_of_isLogDiscrepancy hBp hS2 hx hYv.1 hres E hEall α hα
      (Dvd.intro _ rfl) (by positivity) hqB (fun i => ?_) F a ha hc
    obtain ⟨r, hr⟩ := exists_eq_div_of_mulVec hq M hdet (fun j => α j - 1)
      (hint q hq hqB) i
    exact ⟨r, by
      rw [hr]
      push_cast
      ring⟩

/-! ### Restriction to an affine neighbourhood -/

section Open

variable {k : Type u} [Field k]

/-- A nonempty open subscheme of a variety has the dimension of the variety. -/
private theorem topologicalKrullDim_opens_eq {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX] (U : X.Opens)
    [Nonempty U] [IsDominant U.ι] : topologicalKrullDim U = topologicalKrullDim X := by
  have hbij := functionFieldMap_opens_ι_bijective U
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (U.ι ≫ sX)
  rw [← toENat_trdeg_functionField (sX := U.ι ≫ sX),
    ← trdeg_functionField_eq_of_bijective sX U.ι hbij, toENat_trdeg_functionField (sX := sX)]

/-- A nonempty open subscheme of a normal variety is a normal variety. -/
private theorem isNormalVariety_ι {Y : Scheme.{u}} {s : Y ⟶ Spec (.of k)}
    (h : IsNormalVariety k s) (V : Y.Opens) [Nonempty V] : IsNormalVariety k (V.ι ≫ s) := by
  have := h.1
  have := h.2
  have : IsIntegral Y := h.1.toIsIntegral
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
  have : IsNoetherian Y := {}
  exact ⟨⟨⟩, inferInstance⟩

/-- A proper divisor over an open subscheme `U` of `X` with a log discrepancy is realized by a
proper divisor over `X` with the same valuation, centre and log discrepancy. -/
private theorem exists_isLogDiscrepancy_of_opens [PerfectField k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} (hB : MMP.Mori.IsPair sX B)
    (U : X.Opens) [Nonempty U] [IsIntegral U] [IsLocallyNoetherian U] [IsNormal U] {n : ℕ}
    (D' : DivisorOver k (U.ι ≫ sX)) (a : ℝ)
    (ha : MMP.Intersection.IsLogDiscrepancy (U.ι ≫ sX) n
      (QDivisor.toRDivisor (MMP.Mori.inverseTransformDivisor U.ι B)) D' a) :
    ∃ D : DivisorOver k sX, MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) D a ∧
      D.valuation = D'.valuation.comap (functionFieldMap U.ι) ∧
      D.f D.E.genericPoint = U.ι (D'.f D'.E.genericPoint) := by
  haveI := isDominant_opens_ι U
  haveI : AlgebraicGeometry.IsVariety k sX := hB.1.1
  have hn : topologicalKrullDim X = n :=
    (topologicalKrullDim_opens_eq (sX := sX) U).symm.trans
      (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha)
  have hv := isDivisorOfFunctionField_comap sX U.ι (functionFieldMap_opens_ι_bijective U) D'
  have hdom0 := divisorOver_dominates D' rfl
  have hdom := dominates_comap U.ι D'.valuation _ hdom0
  obtain ⟨D, -, hDv, hDx⟩ :=
    MMP.Flips.exists_properDivisorOver_isProjective_of_dominates sX hv _ hdom.1 hdom.2
  have hDU : D.f D.E.genericPoint ∈ U := by
    rw [hDx]; exact (D'.f D'.E.genericPoint).2
  exact ⟨D.toDivisorOver, (isLogDiscrepancy_open_iff sX hB hn U D.toDivisorOver D.isProper hDU
    D' ha.2.1 hDv a).2 ha, hDv, hDx⟩

/-- A proper divisor over `X` whose centre meets `U`, with a log discrepancy, restricts to a
proper divisor over `U` with the same valuation, centre and log discrepancy. -/
theorem exists_isLogDiscrepancy_restrict [PerfectField k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} (hB : MMP.Mori.IsPair sX B)
    (U : X.Opens) [Nonempty U] [IsIntegral U] [IsLocallyNoetherian U] [IsNormal U] {n : ℕ}
    (D : DivisorOver k sX) (hDU : D.f D.E.genericPoint ∈ U) (a : ℝ)
    (ha : MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) D a) :
    ∃ D' : DivisorOver k (U.ι ≫ sX), MMP.Intersection.IsLogDiscrepancy (U.ι ≫ sX) n
        (QDivisor.toRDivisor (MMP.Mori.inverseTransformDivisor U.ι B)) D' a ∧
      U.ι (D'.f D'.E.genericPoint) = D.f D.E.genericPoint := by
  haveI := isDominant_opens_ι U
  have hn : topologicalKrullDim X = n :=
    MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha
  obtain ⟨hXv, n0, K, hK, hQ⟩ := id hB
  have hn0 : n0 = n := by
    have := hK.topologicalKrullDim_eq.symm.trans hn
    exact_mod_cast this
  subst hn0
  have hcen : ((D.center : Set X) ∩ U).Nonempty :=
    ⟨_, by rw [D.center_eq_closure_genericPoint]; exact subset_closure rfl, hDU⟩
  obtain ⟨hY, hf, E', hE', hval, -⟩ :=
    MMP.Mori.DivisorOver.exists_restrict_isDiscrepancy_iff ⟨hXv, hK, hQ⟩ D U hcen
  have hDp : IsProper D.f := ha.2.1
  haveI : IsProper (D.f ∣_ U) := by haveI := hDp; infer_instance
  refine ⟨⟨_, D.f ∣_ U, hY, hf, E'⟩, (isLogDiscrepancy_open_iff sX hB hn U D hDp hDU _
    inferInstance hval a).1 ha, ?_⟩
  change U.ι ((D.f ∣_ U) E'.genericPoint) = _
  rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply, ← hE',
    ← OpenWeilRestriction.genericPoint_primeDivisorMap]

/-- A closed point of a surface `S` of finite type over `k` has coheight two. -/
private theorem coheight_eq_two_of_isClosed {S : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    [IsIntegral S] [LocallyOfFiniteType sS] (hS2 : topologicalKrullDim S = 2) {x : S}
    (hx : IsClosed ({x} : Set S)) : Order.coheight x = 2 := by
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sS x
  rw [hx.closure_eq, hS2] at h
  have h0 : topologicalKrullDim ({x} : Set S) ≤ 0 :=
    @topologicalKrullDim_zero_of_discreteTopology _ _
      (@Subsingleton.discreteTopology _ _ (Set.subsingleton_singleton (a := x)).coe_sort)
  generalize topologicalKrullDim ({x} : Set S) = d at h h0
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe e =>
    have he : e = 0 := le_antisymm (by exact_mod_cast h0) (by simp)
    subst he
    rw [WithBot.coe_zero, zero_add] at h
    exact WithBot.coe_injective h

end Open

/-! ### The main result -/

/-- **Bounded denominators.** Under the hypotheses of `exists_denominator_logDiscrepancy_le`,
there is `1 ≤ D ≤ q N! C^N` with every log discrepancy of a divisor centred at `x` in `(1/D) ℤ`. -/
private theorem exists_denominator {k : Type u} [Field k] {S : Scheme.{u}}
    {sS : S ⟶ Spec (.of k)} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    {B : QDivisor S} (hB : IsCharZeroKltPair sS B) (hS2 : topologicalKrullDim S = 2)
    {x : S} (hx : IsClosed ({x} : Set S))
    {q N : ℕ} (hq : 1 ≤ q) (hqB : ∀ P, ∃ n : ℤ, (q : ℚ) * B.coeff P = n)
    {δ : ℚ} (hδ0 : 0 < δ)
    (hδ : ∀ (E : DivisorOver k sS) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sS 2 (QDivisor.toRDivisor B) E a →
        (E.center : Set S) = {x} → (δ : ℝ) ≤ a)
    (hlow : {v : Valuation S.functionField (WithZero (Multiplicative ℤ)) |
      ∃ (E : DivisorOver k sS) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sS 2 (QDivisor.toRDivisor B) E a ∧
        (E.center : Set S) = {x} ∧ a ≤ 1 ∧ E.valuation = v}.encard ≤ N) :
    ∃ D : ℕ, 1 ≤ D ∧ D ≤ q * N.factorial * ⌈(4 : ℚ) / δ ^ 2⌉₊ ^ N ∧
      (∀ (E : DivisorOver k sS) (a : ℝ),
        MMP.Intersection.IsLogDiscrepancy sS 2 (QDivisor.toRDivisor B) E a →
          (E.center : Set S) = {x} → ∃ r : ℤ, a = r / D) := by
  classical
  haveI := hB.1.charZero
  have hBp : MMP.Mori.IsPair sS B := hB.1.isPair
  have hX : IsNormalVariety k sS := hBp.isNormalVariety
  haveI hSv : AlgebraicGeometry.IsVariety k sS := hX.1
  haveI : LocallyOfFiniteType sS := hSv.toLocallyOfFiniteType
  -- an affine open neighbourhood `U` of `x`
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  haveI := isDominant_opens_ι U
  have hUn : IsNormalVariety k (U.ι ≫ sS) := isNormalVariety_ι hX U
  haveI : IsIntegral U := hUn.1.toIsIntegral
  haveI : IsNormal U := hUn.2
  haveI : LocallyOfFiniteType (U.ι ≫ sS) := hUn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ sS)
  haveI : IsAffine U := hU
  haveI : IsQuasiProjectiveVariety k (U.ι ≫ sS) :=
    { toIsVariety := hUn.1
      isQuasiProjective := isQuasiProjective_of_isQuasiAffineHom _ inferInstance }
  set BU : QDivisor U := inverseTransformDivisor U.ι B with hBU
  set xU : U.toScheme := ⟨x, hxU⟩ with hxUdef
  have hxU' : IsClosed ({xU} : Set U.toScheme) := by
    have h := hx.preimage U.ι.continuous
    convert h using 1
    ext z
    simp only [Set.mem_singleton_iff, Set.mem_preimage, Scheme.Opens.ι_apply, xU]
    exact Subtype.ext_iff
  have hS2U : topologicalKrullDim U = 2 :=
    (topologicalKrullDim_opens_eq (sX := sS) U).trans hS2
  -- `(U, B|_U)` is a pair: restrict a discrepancy of a prime divisor through `x`
  have hBUp : MMP.Mori.IsPair (U.ι ≫ sS) BU := by
    obtain ⟨-, n, K, hK, hQ⟩ := id hBp
    have hcoh := coheight_eq_two_of_isClosed sS hS2 hx
    obtain ⟨p, hxp, hp1⟩ := ((Order.coheight_eq_coe_add_one_iff (n := 1)).mp hcoh).2.1
    have hpx : p ⤳ x := Scheme.le_iff_specializes.mp hxp.le
    have hpU : p ∈ U := hpx.mem_open U.isOpen hxU
    set P := AlgebraicGeometry.PrimeDivisor.ofCoheightOne p hp1
    have hPp : P.genericPoint = p := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
    set D := DivisorOver.ofPrimeDivisor k hX P
    have hcen : ((D.center : Set S) ∩ U).Nonempty :=
      ⟨p, by rw [D.center_eq_closure_genericPoint]; exact subset_closure (by
        change p = 𝟙 S P.genericPoint; rw [hPp]; rfl), hpU⟩
    obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hBp hK D
    obtain ⟨hY, hf, E', hE', hval, hiff⟩ :=
      MMP.Mori.DivisorOver.exists_restrict_isDiscrepancy_iff ⟨hBp.1, hK, hQ⟩ D U hcen
    have := ((hiff c).1 hc).isPair
    rwa [hBU, inverseTransformDivisor_ι_eq_restrictOpen]
  have hBU0 : ∀ P, 0 ≤ BU.coeff P := fun P =>
    mapPrimeDivisors_nonneg _ B hB.1.nonneg P
  have hBUk : IsCharZeroKltPair (U.ι ≫ sS) BU := ⟨⟨inferInstance, hBUp, hBU0⟩, fun n D' a ha => by
    obtain ⟨D, hD, -, -⟩ := exists_isLogDiscrepancy_of_opens hBp U D' a ha
    exact hB.2 n D a hD⟩
  have hqBU : ∀ P, ∃ n : ℤ, (q : ℚ) * BU.coeff P = n := fun P =>
    exists_int_mul_mapPrimeDivisors _ (q : ℚ) B hqB P
  -- a divisor over `U` centred at `xU` is realized over `S`, centred at `x`
  have hcenS : ∀ (D' : DivisorOver k (U.ι ≫ sS)) (D : DivisorOver k sS),
      (D'.center : Set U.toScheme) = {xU} → D.f D.E.genericPoint = U.ι (D'.f D'.E.genericPoint) →
        (D.center : Set S) = {x} := fun D' D hc h => by
    rw [D.center_eq_closure_genericPoint, h, map_genericPoint_eq_of_center_eq D' hc]
    exact hx.closure_eq
  have hδU : ∀ (E : DivisorOver k (U.ι ≫ sS)) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy (U.ι ≫ sS) 2 (QDivisor.toRDivisor BU) E a →
        (E.center : Set U.toScheme) = {xU} → (δ : ℝ) ≤ a := fun D' a ha hc => by
    obtain ⟨D, hD, -, hDx⟩ := exists_isLogDiscrepancy_of_opens hBp U D' a ha
    exact hδ D a hD (hcenS D' D hc hDx)
  have hlowU : {v : Valuation U.toScheme.functionField (WithZero (Multiplicative ℤ)) |
      ∃ (E : DivisorOver k (U.ι ≫ sS)) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy (U.ι ≫ sS) 2 (QDivisor.toRDivisor BU) E a ∧
        (E.center : Set U.toScheme) = {xU} ∧ a ≤ 1 ∧ E.valuation = v}.encard ≤ N := by
    refine le_trans (Set.encard_le_encard_of_injOn
      (f := fun v => v.comap (functionFieldMap U.ι)) ?_ ?_) hlow
    · rintro v ⟨D', a, ha, hc, ha1, rfl⟩
      obtain ⟨D, hD, hDv, hDx⟩ := exists_isLogDiscrepancy_of_opens hBp U D' a ha
      exact ⟨D, a, hD, hcenS D' D hc hDx, ha1, hDv⟩
    · intro v _ w _ h
      exact valuation_comap_injective _ (functionFieldMap_opens_ι_bijective U).2 h
  obtain ⟨D, hD1, hDle, hden⟩ := exists_denominator_of_isQuasiProjectiveVariety hBUk hS2U hxU'
    hq hqBU hδ0 hδU hlowU
  refine ⟨D, hD1, hDle, fun E a ha hc => ?_⟩
  have hEx := map_genericPoint_eq_of_center_eq E hc
  obtain ⟨E', hE', hEη⟩ := exists_isLogDiscrepancy_restrict hBp U E (by rw [hEx]; exact hxU) a ha
  refine hden E' a hE' ?_
  have hE'x : E'.f E'.E.genericPoint = xU :=
    U.ι.isOpenEmbedding.injective (by rw [hEη, hEx, Scheme.Opens.ι_apply])
  rw [E'.center_eq_closure_genericPoint, hE'x, hxU'.closure_eq]

variable {k : Type u} [Field k] {S : Scheme.{u}} {sS : S ⟶ Spec (.of k)}
  [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]

/-- **Bounded denominators with few low places.** Let `(S, B)` be a klt surface pair over a field
of characteristic zero (`MMP.Fourfold.IsCharZeroKltPair`) and `x ∈ S` a closed point. Let
`q ≥ 1`, `N ≥ 0` be integers and `0 < δ ≤ 1` rational, and suppose `qB` is integral, every
divisor over `S` with centre `x` has log discrepancy at least `δ`, and at most `N` divisorial
valuations centred at `x` have log discrepancy at most one. Then there is `1 ≤ D ≤ q N! C^N`,
`C = ⌈4/δ²⌉`, with every log discrepancy at `x` in `(1/D) ℤ`; and if `δ ≤ mld_x(S, B) ≤ 1`
then `mld_x(S, B) = r / D` for an integer `r`. -/
@[mmp "thm_mmp_surface_bounded_low_place_denominators"]
public theorem IsCharZeroKltPair.exists_denominator_logDiscrepancy_le
    {B : QDivisor S} (hB : IsCharZeroKltPair sS B) (hS2 : topologicalKrullDim S = 2)
    {x : S} (hx : IsClosed ({x} : Set S))
    {q N : ℕ} (hq : 1 ≤ q) (hqB : ∀ P, ∃ n : ℤ, (q : ℚ) * B.coeff P = n)
    {δ : ℚ} (hδ0 : 0 < δ) (_hδ1 : δ ≤ 1)
    (hδ : ∀ (E : DivisorOver k sS) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sS 2 (QDivisor.toRDivisor B) E a →
        (E.center : Set S) = {x} → (δ : ℝ) ≤ a)
    (hlow : {v : Valuation S.functionField (WithZero (Multiplicative ℤ)) |
      ∃ (E : DivisorOver k sS) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sS 2 (QDivisor.toRDivisor B) E a ∧
        (E.center : Set S) = {x} ∧ a ≤ 1 ∧ E.valuation = v}.encard ≤ N) :
    ∃ D : ℕ, 1 ≤ D ∧ D ≤ q * N.factorial * ⌈(4 : ℚ) / δ ^ 2⌉₊ ^ N ∧
      (∀ (E : DivisorOver k sS) (a : ℝ),
        MMP.Intersection.IsLogDiscrepancy sS 2 (QDivisor.toRDivisor B) E a →
          (E.center : Set S) = {x} → ∃ r : ℤ, a = r / D) ∧
      (((δ : ℝ) : EReal) ≤ minimalLogDiscrepancy sS B x → minimalLogDiscrepancy sS B x ≤ 1 →
        ∃ r : ℤ, minimalLogDiscrepancy sS B x = (((r : ℝ) / D : ℝ) : EReal)) := by
  obtain ⟨D, hD1, hDle, hden⟩ := exists_denominator hB hS2 hx hq hqB hδ0 hδ hlow
  exact ⟨D, hD1, hDle, hden, fun _ hle =>
    exists_minimalLogDiscrepancy_eq_div_of_le_one hS2 hx hδ0 hδ hD1 hden hle⟩

end BoundedDenominators

end MMP.Fourfold

namespace MMP.Threefold

/-- **A singular codimension-two point has minimal log discrepancy at most one.** Let `(X, B)` be
an effective pair over an algebraically closed field `k` of characteristic zero
(`MMP.Fourfold.IsPair`) and `x ∈ X` a point of codimension two that is not in the smooth locus of
`X ⟶ Spec k`. Then `MMP.Fourfold.minimalLogDiscrepancy sX B x ≤ 1`. -/
@[mmp "thm_mmp_threefold_singular_codimension_two_mld"]
public theorem minimalLogDiscrepancy_le_one_of_coheight_eq_two
    {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : MMP.Mori.QDivisor X} (hB : MMP.Fourfold.IsPair sX B) {x : X}
    (hx : Order.coheight x = 2) (hsing : x ∉ MMP.Mori.smoothLocus sX) :
    MMP.Fourfold.minimalLogDiscrepancy sX B x ≤ 1 := by
  have := hB.charZero
  obtain ⟨U, hxU, hUa, iU1, iU2, iU3, d, K, iK1, iK2, -, hdX, S, sS, iS1, iS2, iS3, iS4, iS5,
    hSa, hSn, hSd, ι, iι, p, hp, hcomm, hιp, hiso, hsm, BS, hBS, hBS0, -, hspread⟩ :=
    MMP.Threefold.exists_generic_surface_of_coheight_eq_two sX hB hx
  -- `p` is singular on `S`
  have hpsing : p ∉ MMP.Mori.smoothLocus sS := by
    rw [MMP.Mori.smoothLocus_eq_smoothLocus, hsm, ← MMP.Mori.smoothLocus_eq_smoothLocus]
    exact hsing
  haveI : IsQuasiProjectiveVariety K sS :=
    { toIsVariety := hSn.1
      isQuasiProjective := isQuasiProjective_of_isQuasiAffineHom sS inferInstance }
  obtain ⟨D, hDp, hDs, hDc, a, ha, hDa⟩ :=
    MMP.Threefold.exists_isLogDiscrepancy_le_one_of_notMem_smoothLocus sS hSd (Δ := BS)
      ⟨charZero_of_injective_algebraMap (algebraMap k K).injective, hBS, hBS0⟩ hp hpsing
  obtain ⟨D', hD'c, -, hD'a⟩ := hspread D (isProper_of_isProjectiveMorphism _ hDp) hDc
  have hD'a := (hD'a a).1 hDa
  haveI : AlgebraicGeometry.IsVariety k sX := hB.isPair.1.1
  -- realize the valuation of `D'` by a proper divisor over `X` centred at `x`
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  haveI := isDominant_opens_ι U
  have hD'x : D'.f D'.E.genericPoint = ⟨x, hxU⟩ :=
    (inseparable_iff_closure_eq.2 (hD'c ▸ D'.center_eq_closure_genericPoint).symm).eq
  have hdom := dominates_comap U.ι D'.valuation ⟨x, hxU⟩ (divisorOver_dominates D' hD'x)
  obtain ⟨D'', -, hD''v, hD''x⟩ := MMP.Flips.exists_properDivisorOver_isProjective_of_dominates sX
    (isDivisorOfFunctionField_comap sX U.ι (functionFieldMap_opens_ι_bijective U) D') x
    hdom.1 hdom.2
  have hXa : MMP.Intersection.IsLogDiscrepancy sX (d + 2) (QDivisor.toRDivisor B)
      D''.toDivisorOver a :=
    (isLogDiscrepancy_open_iff sX hB.isPair hdX U D''.toDivisorOver D''.isProper
      (by rw [show D''.toDivisorOver.f D''.toDivisorOver.E.genericPoint = x from hD''x]
          exact hxU)
      D' hD'a.2.1 hD''v a).2 hD'a
  refine le_trans (sInf_le ⟨d + 2, D''.toDivisorOver, a, hXa, ?_, rfl⟩) (by exact_mod_cast ha)
  rw [D''.toDivisorOver.center_eq_closure_genericPoint]
  exact congrArg (fun y => closure {y}) hD''x

end MMP.Threefold

end
