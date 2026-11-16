module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancy
public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
import MMP.AlgebraicGeometry.Singularities.DltKltPerturbation
import MMP.AlgebraicGeometry.MMP.Flip.NegativeContractionDiscrepancy
import MMP.AlgebraicGeometry.MMP.MinimalModel.DiscrepancyComparisonCommonBase
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
import MMP.AlgebraicGeometry.Singularities.LogResolution.ReducedUnion
import MMP.AlgebraicGeometry.Resolution.ZariskiSequence
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.RingTheory.Kaehler.PluriformProduct
import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Singularities.Adjunction.CartierCodimTwo

/-!
# Dlt pairs: klt perturbations and flips

Three results on dlt pairs over an algebraically closed field of characteristic zero.

A dlt pair `(X, Δ)` all of whose coefficients are `< 1` has `⌊Δ⌋ = 0`, so it is klt
(Kollár–Mori 2.41), here in the sense of `MMP.Fourfold.IsKltPair`.

If `(X, Δ)` is dlt on a quasi-projective variety, `H` is ample Cartier and `0 ≤ Δ₁ ≤ Δ` with
`Supp Δ₁ = Supp Δ`, then the dlt perturbation `Δ - εΔ₁ + εD` by a general member `D` of
`|mΔ₁ + m'H|`, divided by `m`, has all coefficients `< 1` for small `ε > 0`, so it is klt
(Kollár–Mori 2.43).

Flips preserve dlt pairs (Kollár–Mori 3.44): away from the images of the exceptional loci the flip
is an isomorphism transporting the smooth snc open set of `(X, Δ)`, and over the exceptional loci
the discrepancies on the flip are strictly larger than those on `X`, which are `≥ -1`.

## Main results

* `MMP.Intersection.IsDltPair.isKltPair_of_forall_coeff_lt_one`: a dlt pair with `⌊Δ⌋ = 0` is
  klt.
* `MMP.Mori.IsDltPair.exists_forall_isKltPair_sub_smul_add_smul`: perturbing a dlt pair to a klt
  pair.
* `MMP.Mori.IsFlip.isDltPair`, `MMP.Mori.IsFlipRationalMap.isDltPair`: flips preserve dlt pairs.
* `MMP.Mori.IsFlip.isCanonicalDivisor_flipTransform`: `(f⁺)⁻¹_* f_* K` is a canonical divisor of
  the flip.
* `MMP.Mori.IsFlipRationalMap.transformDivisor_eq_flipTransform`: the flip `φ` pushes divisors
  forward as `(f⁺)⁻¹_* f_*`.
* `MMP.Mori.transformDivisor_eq_flipTransform_of_isIso_restrict`,
  `MMP.Mori.isCanonicalDivisor_flipTransform_of_isIso_restrict`: the same two facts for any
  proper birational `f`, `f⁺` which are isomorphisms over an open `V` containing the images of
  the points of codimension at most one.
* `MMP.Mori.IsFlip.exists_opens_isIso`, `MMP.Mori.exists_opens_isIso_of_isSmall`,
  `MMP.Fourfold.IsRealFlipStep.exists_opens_isIso`: such a `V` exists for a flip, for two small
  contractions, and for a step of an extremal real flip sequence.
* `MMP.Mori.IsFlip.exists_divisorOver_valuation_comap_eq`: every divisor over `X⁺` has the
  valuation of a divisor over `X`, and the two have the same centre on `Y`
  (`MMP.Mori.map_genericPoint_eq_of_valuation_comap_eq`).
* `MMP.Mori.DivisorWithCoeffs.IsSNC.comapDomain_of_range_subset`: a divisor whose restriction
  to an open subscheme is snc has snc restriction to every smaller open subscheme; smoothness
  is local on the source (`MMP.Mori.mem_smoothLocus_iff_of_comp_eq`).

## Implementation notes

In the perturbation result the linear equivalence `mD ∼ mΔ₁ + m'H` is between integral divisors
`E = mD` and `E₁ = mΔ₁`. A flip is `MMP.Mori.IsFlip`, with boundary and canonical divisor
the transforms `MMP.Mori.flipTransform f f⁺ Δ` and `MMP.Mori.flipTransform f f⁺ K`; for the flip
as a rational map `φ` (`MMP.Mori.IsFlipRationalMap`) the boundary is `φ_* Δ`, the same divisor.
Each result's auxiliary lemmas live in a namespace `Proof_<tag>` named after its label,
opened only for that result; those about the locus over which a flip and its contraction are
isomorphisms, about divisors over `X` and `X⁺`, and about snc divisors along open immersions,
are public in `MMP.Mori`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori],
  Propositions 2.41 and 2.43, Corollary 3.44
-/

@[expose] public section

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Intersection

open CategoryTheory AlgebraicGeometry

open MMP.Mori (QDivisor)

/-- A dlt pair `(X, Δ)` all of whose coefficients are less than one is klt. -/
@[mmp "lem_fourfold_dlt_no_reduced_klt"]
public theorem IsDltPair.isKltPair_of_forall_coeff_lt_one {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {Δ : QDivisor X}
    (h : IsDltPair sX Δ) (hΔ : ∀ P, Δ.coeff P < 1) : MMP.Fourfold.IsKltPair sX Δ := by
  obtain ⟨-, n, K, hK, -⟩ := h.1.1
  refine (MMP.Fourfold.isKltPair_iff_mori_isKltPair sX hK ⟨inferInstance, inferInstance, h.1.1,
    h.1.2.1⟩).mpr <| ((MMP.Threefold.Bridges.isDltPair_iff_isDltPair sX hK Δ).mp
      h).isKltPair_iff_roundDown_eq_zero.mpr ?_
  ext P
  simpa [MMP.Mori.DivisorWithCoeffs.coeff_roundDown] using ⟨h.1.2.1 P, hΔ P⟩

end MMP.Intersection

namespace Proof_prop_km2b_dlt_perturbation_klt

open CategoryTheory AlgebraicGeometry MMP.Mori Filter Topology

/-- If `Supp Δ₁ = Supp Δ`, every prime divisor with nonzero coefficient in `Δ` has nonzero
coefficient in `Δ₁`. -/
private theorem coeff_ne_zero_of_supp_eq {X : Scheme.{u}} {Δ Δ₁ : QDivisor X}
    (hsupp : Δ₁.supp = Δ.supp) {P : MMP.Mori.PrimeDivisor X} (hP : Δ.coeff P ≠ 0) :
    Δ₁.coeff P ≠ 0 := by
  have hη : P.genericPoint ∈ P.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have h1 : P.genericPoint ∈ Δ₁.supp := by
    rw [hsupp]; exact DivisorWithCoeffs.support_subset_supp hP hη
  obtain ⟨E, hE, hηE⟩ := DivisorWithCoeffs.mem_supp_iff.mp h1
  rwa [MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support hηE] at hE

/-- A coefficient `a ≤ 1` of the boundary stays `< 1` under `a - εb + εd` for small `ε > 0`,
provided that `b > 0` and `d = 0` whenever `a = 1`. -/
private theorem eventually_sub_mul_add_mul_lt_one {a b d : ℚ} (ha : a ≤ 1)
    (h1 : a = 1 → 0 < b ∧ d = 0) : ∀ᶠ ε in 𝓝[>] (0 : ℚ), a - ε * b + ε * d < 1 := by
  rcases ha.lt_or_eq with ha | rfl
  · exact nhdsWithin_le_nhds
      (ContinuousAt.eventually_lt (by fun_prop) continuousAt_const (by simpa using ha))
  · obtain ⟨hb, rfl⟩ := h1 rfl
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    nlinarith

end Proof_prop_km2b_dlt_perturbation_klt

namespace MMP.Mori

open CategoryTheory AlgebraicGeometry
open Proof_prop_km2b_dlt_perturbation_klt

/-- **Perturbing a dlt pair to a klt pair** (Kollár–Mori 2.43). Let `(X, Δ)` be a dlt pair,
with canonical divisor `K` of dimension `n`, on a quasi-projective variety over an algebraically
closed field of characteristic zero, let `H` be an ample Cartier divisor, and let `Δ₁` be an
effective `ℚ`-divisor with `Δ - Δ₁` effective and `Supp Δ₁ = Supp Δ`. Then there are integers
`m, m' > 0`, an effective `ℚ`-divisor `D` with `mD ∼ mΔ₁ + m'H` (both sides integral), and a
rational `ε₀ > 0` such that `(X, Δ - εΔ₁ + εD)` is klt for every rational `0 < ε < ε₀`. -/
@[mmp "prop_km2b_dlt_perturbation_klt"]
public theorem IsDltPair.exists_forall_isKltPair_sub_smul_add_smul {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {n : ℕ} {K : Divisor X}
    {Δ : QDivisor X} (h : IsDltPair sX n K Δ) (hqp : IsQuasiProjective sX)
    {H : Divisor X} (hH : H.IsCartier) (hHa : H.IsAmple hH)
    {Δ₁ : QDivisor X} (hΔ₁ : Δ₁.IsEffective) (hΔΔ₁ : (Δ - Δ₁).IsEffective)
    (hsupp : Δ₁.supp = Δ.supp) :
    ∃ m m' : ℕ, 0 < m ∧ 0 < m' ∧ ∃ D : QDivisor X, D.IsEffective ∧
      (∃ E E₁ : Divisor X, Divisor.toQDivisor E = (m : ℚ) • D ∧
        Divisor.toQDivisor E₁ = (m : ℚ) • Δ₁ ∧ E.LinearlyEquivalent (E₁ + m' • H)) ∧
      ∃ ε₀ : ℚ, 0 < ε₀ ∧ ∀ ε : ℚ, 0 < ε → ε < ε₀ →
        IsKltPair sX n K (Δ - ε • Δ₁ + ε • D) := by
  open Filter Topology in
  obtain ⟨m, m', hm, hm', D, hD, hE, hdisj, ε₀, hε₀, hdlt⟩ :=
    h.exists_forall_isDltPair_sub_smul_add_smul hqp hH hHa hΔ₁ hΔΔ₁
  have hcoeff (ε : ℚ) (P : MMP.Mori.PrimeDivisor X) :
      (Δ - ε • Δ₁ + ε • D).coeff P = Δ.coeff P - ε * Δ₁.coeff P + ε * D.coeff P := by
    simp [DivisorWithCoeffs.coeff_apply]
  have hle (P : MMP.Mori.PrimeDivisor X) : Δ₁.coeff P ≤ Δ.coeff P := by
    simpa [DivisorWithCoeffs.coeff_apply] using hΔΔ₁ P
  -- every coefficient of the perturbation is eventually `< 1`
  have hlt : ∀ᶠ ε in 𝓝[>] (0 : ℚ), ∀ P, (Δ - ε • Δ₁ + ε • D).coeff P < 1 := by
    classical
    filter_upwards [(Δ.support ∪ D.support).eventually_all.mpr fun P _ =>
      eventually_sub_mul_add_mul_lt_one (h.2.1 P).2 fun ha1 =>
        ⟨(hΔ₁ P).lt_of_ne (coeff_ne_zero_of_supp_eq hsupp (by simp [ha1])).symm,
          Finsupp.notMem_support_iff.mp fun hP => Finset.disjoint_left.mp hdisj hP <|
            Finsupp.mem_support_iff.mpr <| by
              change Δ.roundDown.coeff P ≠ 0
              simp [DivisorWithCoeffs.coeff_roundDown, ha1]⟩] with ε hε P
    by_cases hP : P ∈ Δ.support ∪ D.support
    · rw [hcoeff]; exact hε P hP
    · simp only [Finset.mem_union, Finsupp.mem_support_iff, not_or, not_not] at hP
      have h0 : Δ.coeff P = 0 := hP.1
      have h0' : D.coeff P = 0 := hP.2
      have : Δ₁.coeff P = 0 := le_antisymm (h0 ▸ hle P) (hΔ₁ P)
      simp [hcoeff, h0, h0', this]
  obtain ⟨δ, hδ, hδlt⟩ := (nhdsGT_basis (0 : ℚ)).eventually_iff.mp hlt
  refine ⟨m, m', hm, hm', D, hD, hE, min ε₀ δ, lt_min hε₀ hδ, fun ε hε hεlt => ?_⟩
  have hd := hdlt ε hε (hεlt.trans_le (min_le_left _ _))
  refine hd.isKltPair_iff_roundDown_eq_zero.mpr ?_
  ext P
  rw [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_zero, Int.floor_eq_zero_iff]
  exact ⟨(hd.2.1 P).1, hδlt ⟨hε, hεlt.trans_le (min_le_right _ _)⟩ P⟩

end MMP.Mori

namespace Proof_thm_km3c_dlt_preserved_flip

open CategoryTheory TopologicalSpace
open AlgebraicGeometry hiding PrimeDivisor
open MMP.Mori
open scoped WithZero

/-! ### Points over the locus where both contractions are isomorphisms -/

section Points

variable {X Y : Scheme.{u}}

/-- A point of coheight at most one does not lie in a closed set of codimension at least two. -/
private theorem notMem_of_coheight_le_one {T : Scheme.{u}} {Z : Closeds T}
    (h2 : 2 ≤ closedsCodimension Z) {x : T} (hx : Order.coheight x ≤ 1) : x ∉ Z := fun hxZ =>
  absurd ((MMP.Flips.le_closedsCodimension_iff_le_coheight.mp h2 x hxZ).trans hx) (by decide)

/-- Over an open `V` such that `f ∣_ V` is an isomorphism, `f` is injective. -/
private theorem eq_of_apply_eq (f : X ⟶ Y) (V : Y.Opens) [IsIso (f ∣_ V)] {x₁ x₂ : X}
    (h₁ : f x₁ ∈ V) (h₂ : f x₂ ∈ V) (h : f x₁ = f x₂) : x₁ = x₂ :=
  congrArg Subtype.val ((f ∣_ V).isOpenEmbedding.injective (a₁ := ⟨x₁, h₁⟩) (a₂ := ⟨x₂, h₂⟩)
    (Subtype.ext ((morphismRestrict_base_coe f V ⟨x₁, h₁⟩).trans
      (h.trans (morphismRestrict_base_coe f V ⟨x₂, h₂⟩).symm))))

/-- Over an open `V` such that `f ∣_ V` is an isomorphism, every point of `V` is in the image
of `f`. -/
private theorem exists_apply_eq (f : X ⟶ Y) (V : Y.Opens) [IsIso (f ∣_ V)] {y : Y}
    (hy : y ∈ V) : ∃ x, f x = y := by
  obtain ⟨p, hp⟩ := (f ∣_ V).surjective ⟨y, hy⟩
  exact ⟨p.1, (morphismRestrict_base_coe f V p).symm.trans (congrArg Subtype.val hp)⟩

/-- Over an open `V` such that `f ∣_ V` is an isomorphism, `f` preserves coheights. -/
private theorem coheight_apply_eq (f : X ⟶ Y) (V : Y.Opens) [IsIso (f ∣_ V)] {x : X}
    (hx : f x ∈ V) : Order.coheight (f x) = Order.coheight x :=
  MMP.Positivity.coheight_map_of_mem_biregularLocus f
    ((isBiregular_iff_le_biregularLocus.mp ‹IsIso (f ∣_ V)›) hx)

/-- Prime divisors correspond over `V`: if `f` and `f⁺` are isomorphisms over `V`, every prime
divisor `P⁺` of `X⁺` lying over `V` has a prime divisor `P` of `X` over the same point of `Y`. -/
theorem _root_.MMP.Mori.exists_primeDivisor_genericPoint_eq {X' : Scheme.{u}} (f : X ⟶ Y)
    (fp : X' ⟶ Y) (V : Y.Opens) [IsIso (f ∣_ V)] [IsIso (fp ∣_ V)] (P' : PrimeDivisor X')
    (hP' : fp P'.genericPoint ∈ V) :
    ∃ P : PrimeDivisor X, f P.genericPoint = fp P'.genericPoint := by
  obtain ⟨x, hx⟩ := exists_apply_eq f V hP'
  have hxV : f x ∈ V := hx ▸ hP'
  have hco : Order.coheight x = 1 := by
    rw [← coheight_apply_eq f V hxV, hx, coheight_apply_eq fp V hP',
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hco,
    (congrArg f (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hco)).trans hx⟩

end Points

/-! ### The two transforms of divisors -/

section Transforms

/-- The coefficients of `(f⁺)⁻¹_* f_* D`: if `f` and `f⁺` are isomorphisms over `V`, over which
lie the points of codimension at most one of `X`, the coefficient of `P⁺` is that of the prime
divisor `P` of `X` over the same point of `Y`. -/
theorem _root_.MMP.Mori.flipTransform_apply {k : Type u} [Field k] {X X' Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] {sY : Y ⟶ Spec (.of k)} (hY : IsNormalVariety k sY)
    {f : X ⟶ Y} {fp : X' ⟶ Y} (hX : IsNormalVariety k (f ≫ sY)) [IsProper f]
    (hf : IsBirationalMorphism f) (V : Y.Opens) [IsIso (f ∣_ V)] [IsIso (fp ∣_ V)]
    (hXV : ∀ x : X, Order.coheight x ≤ 1 → f x ∈ V) {P : PrimeDivisor X}
    {P' : PrimeDivisor X'} (hPP : f P.genericPoint = fp P'.genericPoint) {R : Type*}
    [AddCommMonoid R] (D : DivisorWithCoeffs R X) : flipTransform f fp D P' = D P := by
  have : IsNormal Y := hY.2
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have hV : f P.genericPoint ∈ V :=
    hXV _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P).le
  have hV' : fp P'.genericPoint ∈ V := hPP ▸ hV
  have hco : Order.coheight (fp P'.genericPoint) = 1 := by
    rw [coheight_apply_eq fp V hV', AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
  set Q := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco
  have hQ : Q.genericPoint = fp P'.genericPoint :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco
  have hbir : fp P'.genericPoint ∈ biregularLocus fp :=
    (isBiregular_iff_le_biregularLocus.mp ‹IsIso (fp ∣_ V)›) hV'
  have huniq : ∀ Q₁ : PrimeDivisor Y, inverseTransformPrimeDivisor fp Q₁ = some P' → Q₁ = Q := by
    intro Q₁ hQ₁
    obtain ⟨h1, -⟩ :=
      MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hQ₁
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (h1.symm.trans hQ.symm)
  have h1 : inverseTransformDivisor fp (MMP.Mori.RationalMap.transformDivisor (X := X)
      f.toRationalMap D) P' = MMP.Mori.RationalMap.transformDivisor (X := X) f.toRationalMap D Q :=
    MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
      (MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint
        hQ.symm hbir) huniq _
  obtain ⟨E, hEQ, -, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hY hX hf Q
  change inverseTransformDivisor fp (MMP.Mori.RationalMap.transformDivisor (X := X)
    f.toRationalMap D) P' = _
  rw [h1, htr]
  have hE : f E.genericPoint = f P.genericPoint := hEQ.trans (hQ.trans hPP.symm)
  rw [AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (eq_of_apply_eq f V (hE ▸ hV) hV hE)]

/-- If `f⁺` is an isomorphism over `U`, two morphisms into `(f⁺)⁻¹(U)` which agree after
composing with `f⁺` are equal. -/
private theorem eq_of_comp_eq {T X' Y : Scheme.{u}} (fp : X' ⟶ Y) (U : Y.Opens)
    [IsIso (fp ∣_ U)] (a b : T ⟶ X') (ha : Set.range a ⊆ (fp ⁻¹ᵁ U : Set X'))
    (hb : Set.range b ⊆ (fp ⁻¹ᵁ U : Set X')) (h : a ≫ fp = b ≫ fp) : a = b := by
  have ha' : Set.range a ⊆ Set.range (fp ⁻¹ᵁ U).ι := by rwa [Scheme.Opens.range_ι]
  have hb' : Set.range b ⊆ Set.range (fp ⁻¹ᵁ U).ι := by rwa [Scheme.Opens.range_ι]
  rw [← IsOpenImmersion.lift_fac _ _ ha', ← IsOpenImmersion.lift_fac _ _ hb']
  congr 1
  rw [← cancel_mono (fp ∣_ U), ← cancel_mono U.ι, Category.assoc, Category.assoc,
    morphismRestrict_ι, ← Category.assoc, IsOpenImmersion.lift_fac, ← Category.assoc,
    IsOpenImmersion.lift_fac, h]

/-- A morphism `a : T ⟶ X'` with `a ≫ f⁺ = c ≫ f` for some `c` landing in `f⁻¹(U)` lands in
`(f⁺)⁻¹(U)`. -/
private theorem range_subset_of_comp_eq {T X X' Y : Scheme.{u}} {f : X ⟶ Y} {fp : X' ⟶ Y}
    {U : Y.Opens} (a : T ⟶ X') (c : T ⟶ X) (hc : ∀ t, c t ∈ f ⁻¹ᵁ U) (h : a ≫ fp = c ≫ f) :
    Set.range a ⊆ (fp ⁻¹ᵁ U : Set X') := by
  rintro _ ⟨t, rfl⟩
  change fp (a t) ∈ U
  rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]
  exact hc t

/-- Let `f⁺` be an isomorphism over `U`. A partial map `p : X ⇀ X'` defined inside `f⁻¹(U)` with
`f⁺ ∘ p = f` represents every rational map `g` with `f⁺ ∘ g = f`. -/
private theorem toRationalMap_eq_of_comp_eq {X X' Y : Scheme.{u}} {f : X ⟶ Y} (fp : X' ⟶ Y)
    (U : Y.Opens) [IsIso (fp ∣_ U)] (p : X.PartialMap X') (hpU : p.domain ≤ f ⁻¹ᵁ U)
    (hp : p.hom ≫ fp = p.domain.ι ≫ f) (g : X.PartialMap X')
    (hg : g.toRationalMap.compHom fp = f.toPartialMap.toRationalMap) :
    p.toRationalMap = g.toRationalMap := by
  rw [← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff] at hg
  obtain ⟨W, hWd, hWl, _, hWe⟩ := hg
  replace hWl : W ≤ g.domain := hWl
  have h2 : W ⊓ p.domain ≤ g.domain := inf_le_left.trans hWl
  have hc : ∀ t, (W ⊓ p.domain).ι t ∈ f ⁻¹ᵁ U := fun t ↦ hpU t.2.2
  have ha : (X.homOfLE (inf_le_right : W ⊓ p.domain ≤ _) ≫ p.hom) ≫ fp =
      (W ⊓ p.domain).ι ≫ f := by
    rw [Category.assoc, hp, Scheme.homOfLE_ι_assoc]
  have hb : (X.homOfLE h2 ≫ g.hom) ≫ fp = (W ⊓ p.domain).ι ≫ f := by
    have hWe' : X.homOfLE hWl ≫ g.hom ≫ fp = X.homOfLE (le_top : W ≤ ⊤) ≫ X.topIso.hom ≫ f := hWe
    rw [Category.assoc, ← X.homOfLE_homOfLE (inf_le_left : W ⊓ p.domain ≤ W) hWl,
      Category.assoc, hWe', Scheme.topIso_hom, ← Category.assoc, ← Category.assoc,
      Scheme.homOfLE_homOfLE, Scheme.homOfLE_ι]
  rw [Scheme.PartialMap.toRationalMap_eq_iff]
  exact ⟨_, hWd.inter_of_isOpen_left p.dense_domain W.isOpen, inf_le_right, h2,
    eq_of_comp_eq fp U _ _ (range_subset_of_comp_eq _ _ hc ha)
      (range_subset_of_comp_eq _ _ hc hb) (ha.trans hb.symm)⟩

/-- A rational map `φ : X ⤏ X⁺` with `f⁺ ∘ φ = f`, where `f` and `f⁺` are isomorphisms over a
`V` whose preimage in `X` is dense, is represented on `f⁻¹(V)` by `(f⁺)⁻¹ ∘ f`. -/
private theorem exists_partialMap {X X' Y : Scheme.{u}} {f : X ⟶ Y} (fp : X' ⟶ Y) (V : Y.Opens)
    [IsIso (f ∣_ V)] [IsIso (fp ∣_ V)] (hd : Dense (f ⁻¹ᵁ V : Set X))
    {φ : X.RationalMap X'} (hφ : φ.compHom fp = f.toRationalMap) :
    ∃ g : X.PartialMap X', g.domain = f ⁻¹ᵁ V ∧ g.toRationalMap = φ ∧
      g.hom ≫ fp = g.domain.ι ≫ f ∧ ∀ t, fp (g.hom t) ∈ V := by
  let g : X.PartialMap X' := ⟨f ⁻¹ᵁ V, hd, (f ∣_ V) ≫ inv (fp ∣_ V) ≫ (fp ⁻¹ᵁ V).ι⟩
  have hg : g.hom ≫ fp = g.domain.ι ≫ f := by
    change ((f ∣_ V) ≫ inv (fp ∣_ V) ≫ (fp ⁻¹ᵁ V).ι) ≫ fp = (f ⁻¹ᵁ V).ι ≫ f
    rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc,
      morphismRestrict_ι]
  refine ⟨g, rfl, ?_, hg, fun t => ?_⟩
  · obtain ⟨g₀, rfl⟩ := Quotient.exists_rep φ
    exact toRationalMap_eq_of_comp_eq fp V g le_rfl hg g₀ hφ
  · change fp ((fp ⁻¹ᵁ V).ι ((inv (fp ∣_ V)) ((f ∣_ V) t))) ∈ V
    exact ((inv (fp ∣_ V)) ((f ∣_ V) t)).2

/-- The transform of a prime divisor `P` under a rational map represented by `g'`, defined at
`η_P`, is the closure of `g'(η_P)`. -/
private theorem coe_transform_eq_closure_singleton {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = φ) (P : PrimeDivisor X) (hP : P.genericPoint ∈ g'.domain) :
    (MMP.Mori.RationalMap.transform φ P.idealSheaf.support : Set Y) =
      closure {g'.hom ⟨P.genericPoint, hP⟩} := by
  have hZ : closure ((P.idealSheaf.support : Set X) ∩ g'.domain) = P.idealSheaf.support := by
    refine le_antisymm ?_ ?_
    · exact closure_minimal Set.inter_subset_left P.idealSheaf.support.isClosed
    · change P.support ⊆ _
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      refine closure_mono (Set.singleton_subset_iff.mpr ⟨?_, hP⟩)
      change P.genericPoint ∈ P.support
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
  rw [← MMP.Positivity.closure_image_eq_transform g' hg' _ hZ, Closeds.coe_closure]
  refine le_antisymm (closure_minimal ?_ isClosed_closure) (closure_mono ?_)
  · rintro _ ⟨q, hq, rfl⟩
    have hq' : P.genericPoint ⤳ g'.domain.ι q := by
      have : g'.domain.ι q ∈ P.support := hq
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
      exact specializes_iff_mem_closure.mpr this
    have h1 := (g'.domain.ι.isOpenEmbedding.isInducing.specializes_iff (y := q)
      (x := ⟨P.genericPoint, hP⟩)).mp (by rwa [Scheme.Opens.ι_apply])
    exact specializes_iff_mem_closure.mp (h1.map g'.hom.continuous)
  · rw [Set.singleton_subset_iff]
    refine ⟨⟨P.genericPoint, hP⟩, ?_, rfl⟩
    change g'.domain.ι ⟨P.genericPoint, hP⟩ ∈ P.support
    rw [Scheme.Opens.ι_apply, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl

/-- If `φ_* P = E` and `φ` is represented by `g'` near `η_P`, then `η_E = g'(η_P)`. -/
private theorem genericPoint_eq_of_transformPrimeDivisor_eq_some {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : PrimeDivisor X}
    {E : PrimeDivisor Y} (h : MMP.Mori.RationalMap.transformPrimeDivisor φ P = some E)
    (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ) (hP : P.genericPoint ∈ g'.domain) :
    E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩ := by
  have h1 := MMP.Mori.RationalMap.support_transformPrimeDivisor h
  rw [coe_transform_eq_closure_singleton g' hg' P hP,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h1
  exact (inseparable_iff_closure_eq.2 h1).eq

/-- If `φ` is represented by `g'` near `η_P` and `η_E = g'(η_P)`, then `φ_* P = E`. -/
private theorem transformPrimeDivisor_eq_some_of_genericPoint_eq {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : PrimeDivisor X}
    {E : PrimeDivisor Y} (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ)
    (hP : P.genericPoint ∈ g'.domain) (hE : E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩) :
    MMP.Mori.RationalMap.transformPrimeDivisor φ P = some E := by
  refine MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mpr
    ⟨MMP.Mori.RationalMap.definedAt_iff.mpr ⟨g', hP, hg'⟩, ?_⟩
  have h1 : MMP.Mori.RationalMap.transform φ P.idealSheaf.support = E.idealSheaf.support := by
    apply SetLike.coe_injective
    rw [coe_transform_eq_closure_singleton g' hg' P hP, ← hE]
    exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure E).symm
  have := E.integral
  rw [MMP.Mori.RationalMap.transformIdeal, h1, MMP.Positivity.vanishingIdeal_support_of_isReduced]

/-- The coefficients of `φ_* D` for a rational map `φ : X ⤏ X⁺` with `f⁺ ∘ φ = f`, when `f` and
`f⁺` are isomorphisms over `V`, over which lie the points of codimension at most one of `X`: the
coefficient of `P⁺` is that of the prime divisor `P` of `X` over the same point of `Y`. -/
private theorem transformDivisor_apply {X X' Y : Scheme.{u}} [IsIntegral X]
    [IsSeparated (X' ↘ ⊤_ Scheme)] {f : X ⟶ Y} (fp : X' ⟶ Y) (V : Y.Opens) [IsIso (f ∣_ V)]
    [IsIso (fp ∣_ V)] (hXV : ∀ x : X, Order.coheight x ≤ 1 → f x ∈ V)
    {φ : X.RationalMap X'} (hφ : φ.compHom fp = f.toRationalMap) {P : PrimeDivisor X}
    {P' : PrimeDivisor X'} (hPP : f P.genericPoint = fp P'.genericPoint) {R : Type*}
    [AddCommMonoid R] (D : DivisorWithCoeffs R X) :
    MMP.Mori.RationalMap.transformDivisor φ D P' = D P := by
  have hgen : Order.coheight (genericPoint X) ≤ 1 :=
    (Order.coheight_eq_zero.mpr fun z _ ↦ genericPoint_specializes z).trans_le zero_le_one
  obtain ⟨g, hgd, hgφ, hgc, hgV⟩ :=
    exists_partialMap fp V ((f ⁻¹ᵁ V).isOpen.dense ⟨_, hXV _ hgen⟩) hφ
  have hmem : ∀ Q : PrimeDivisor X, Q.genericPoint ∈ g.domain := fun Q => by
    rw [hgd]; exact hXV _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Q).le
  have hval : ∀ Q : PrimeDivisor X,
      fp (g.hom ⟨Q.genericPoint, hmem Q⟩) = f Q.genericPoint := fun Q =>
    congrArg (fun h => h.base ⟨Q.genericPoint, hmem Q⟩) hgc
  have hPV : ∀ Q : PrimeDivisor X, f Q.genericPoint ∈ V := fun Q =>
    hXV _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Q).le
  refine MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    (transformPrimeDivisor_eq_some_of_genericPoint_eq g hgφ (hmem P) ?_) (fun P₁ hP₁ => ?_) D
  · exact eq_of_apply_eq fp V (hPP ▸ hPV P) (hgV _) (hPP.symm.trans (hval P).symm)
  · have h1 := genericPoint_eq_of_transformPrimeDivisor_eq_some hP₁ g hgφ (hmem P₁)
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective <|
      eq_of_apply_eq f V (hPV P₁) (hPV P) (by rw [← hval P₁, ← h1, ← hPP])

/-- **The flip transforms divisors as `(f⁺)⁻¹_* f_*`.** If `f` and `f⁺` are isomorphisms over `V`,
over which lie the points of codimension at most one of `X` and of `X⁺`, then
`φ_* D = (f⁺)⁻¹_* f_* D` for every rational map `φ : X ⤏ X⁺` with `f⁺ ∘ φ = f`. -/
theorem _root_.MMP.Mori.transformDivisor_eq_flipTransform_of_isIso_restrict {k : Type u}
    [Field k] {X X' Y : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsSeparated (X' ↘ ⊤_ Scheme)]
    {sY : Y ⟶ Spec (.of k)} (hY : IsNormalVariety k sY) {f : X ⟶ Y} {fp : X' ⟶ Y}
    (hX : IsNormalVariety k (f ≫ sY)) [IsProper f] (hf : IsBirationalMorphism f) (V : Y.Opens)
    [IsIso (f ∣_ V)] [IsIso (fp ∣_ V)] (hXV : ∀ x : X, Order.coheight x ≤ 1 → f x ∈ V)
    (hX'V : ∀ x : X', Order.coheight x ≤ 1 → fp x ∈ V) {φ : X.RationalMap X'}
    (hφ : φ.compHom fp = f.toRationalMap) {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R X) :
    MMP.Mori.RationalMap.transformDivisor φ D = flipTransform f fp D := by
  refine Finsupp.ext fun P' => ?_
  obtain ⟨P, hP⟩ := exists_primeDivisor_genericPoint_eq f fp V P'
    (hX'V _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P').le)
  rw [transformDivisor_apply fp V hXV hφ hP, flipTransform_apply hY hX hf V hXV hP]

end Transforms

/-! ### The canonical divisor of the flip -/

section Canonical

/-- The pull-back of a nonzero form along a dominant morphism inducing an isomorphism of
function fields is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX]
    {Y : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ X) [IsDominant f]
    (hbij : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d)
    {m : ℤ} {τ : RationalPluriForms sX d m} (hτ : τ ≠ 0) :
    pullbackRationalPluriForms sX f τ ≠ 0 := by
  let := functionFieldAlgebra sX
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX f hbij hd
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  have hpull : pullbackRationalPluriForms sX f τ = pullbackFormsAlong hω m τ :=
    pullbackForms_eq hω m τ
  have hrepr := repr_pullbackFormsAlong hω m τ
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := hpull ▸ h0
  have h1 : algebraMap X.functionField Y.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← hrepr, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

/-- **The transformed canonical divisor is canonical.** Let `f : X ⟶ Y` and `f⁺ : X⁺ ⟶ Y` be
proper birational morphisms of normal varieties which are isomorphisms over an open `V ⊆ Y` over
which lie the points of codimension at most one of `X` and `X⁺`. If `K` is a canonical divisor of
`X`, then `(f⁺)⁻¹_* f_* K` is a canonical divisor of `X⁺`. -/
theorem _root_.MMP.Mori.isCanonicalDivisor_flipTransform_of_isIso_restrict {k : Type u}
    [Field k] [PerfectField k]
    {X X' Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    {sY : Y ⟶ Spec (.of k)} (hY : IsNormalVariety k sY) {f : X ⟶ Y} {fp : X' ⟶ Y}
    (hX : IsNormalVariety k (f ≫ sY)) (hX' : IsNormalVariety k (fp ≫ sY)) [IsProper f]
    (hf : IsBirationalMorphism f) (hfp : IsBirationalMorphism fp) (V : Y.Opens)
    [IsIso (f ∣_ V)] [IsIso (fp ∣_ V)] (hXV : ∀ x : X, Order.coheight x ≤ 1 → f x ∈ V)
    (hX'V : ∀ x : X', Order.coheight x ≤ 1 → fp x ∈ V) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor (f ≫ sY) n) :
    Divisor.IsCanonicalDivisor (fp ≫ sY) n (flipTransform f fp K) := by
  have : IsIntegral Y := hY.1.toIsIntegral
  have : IsNormal Y := hY.2
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsDominant f := hf.isDominant
  have : IsDominant fp := hfp.isDominant
  have hbij := hf.functionFieldMap_bijective
  have hbij' := hfp.functionFieldMap_bijective
  have : MMP.Mori.IsVariety k sY := hY.1
  have : MMP.Mori.IsVariety k (f ≫ sY) := hX.1
  have : MMP.Mori.IsVariety k (fp ≫ sY) := hX'.1
  have hnY : topologicalKrullDim Y = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (f ≫ sY) hf).trans
      hK.topologicalKrullDim_eq
  have hnX' : topologicalKrullDim X' = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (fp ≫ sY) hfp).symm.trans
      hnY
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY) hnY
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor (fp ≫ sY) hX' hnX'
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  -- `ω = f^*τ` for a rational top form `τ` on `Y`
  let := functionFieldAlgebra sY
  let := functionFieldAlgebra (f ≫ sY)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sY f
  obtain ⟨ω₀, hω₀⟩ := exists_isPullbackGenerator_of_bijective sY f hbij hd
  obtain ⟨g, hg⟩ := hbij.2
    ((ZTensorPower.basis (basisOfSpanSingleton hω₀.2.1 hω₀.2.2) 1).repr ω ())
  let τ : RationalPluriForms sY n 1 :=
    g • ZTensorPower.basis (basisOfSpanSingleton hω₀.1 hω₀.ne_zero) 1 ()
  have hτ : pullbackRationalPluriForms sY f τ = ω := by
    change pullbackForms (K := Y.functionField) (K' := X.functionField) 1 τ = ω
    rw [pullbackForms_eq hω₀, pullbackFormsAlong]
    simp only [τ, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_eq_same, smul_eq_mul, mul_one]
    change functionFieldMap f g • _ = ω
    rw [hg]
    exact basis_unit_repr_smul _ ω
  have hτ0 : τ ≠ 0 := by
    intro h0
    apply hω0
    rw [← hτ, h0]
    change pullbackForms (K := Y.functionField) (K' := X.functionField) 1 0 = 0
    rw [pullbackForms_eq hω₀, pullbackFormsAlong]
    simp
  have hω'0 : pullbackRationalPluriForms sY fp τ ≠ 0 :=
    pullbackRationalPluriForms_ne_zero fp hbij' hd hτ0
  have hdiv : divisorOfForm (pullbackRationalPluriForms sY fp τ) = flipTransform f fp K := by
    refine Finsupp.ext fun P' => ?_
    have hV' : fp P'.genericPoint ∈ V :=
      hX'V _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P').le
    obtain ⟨P, hP⟩ := exists_primeDivisor_genericPoint_eq f fp V P' hV'
    have hco : Order.coheight (fp P'.genericPoint) = 1 := by
      rw [coheight_apply_eq fp V hV', AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
    set Q : PrimeDivisor Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco
    have hQ : Q.genericPoint = fp P'.genericPoint :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco
    have := Q.isDiscreteValuationRing_localRing
    have : ValuationRing (Y.presheaf.stalk (fp P'.genericPoint)) := by
      rw [← hQ]; infer_instance
    have : ValuationRing (Y.presheaf.stalk (f P.genericPoint)) := by
      rw [hP, ← hQ]; infer_instance
    have := MMP.Positivity.isIso_stalkMap_of_valuationRing fp hbij' P'.genericPoint
    have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hbij P.genericPoint
    change P'.ordForm (pullbackRationalPluriForms sY fp τ) = flipTransform f fp K P'
    rw [flipTransform_apply hY hX hf V hXV hP K,
      MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso fp hbij' hd P' Q hQ.symm τ,
      ← MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso f hbij hd P Q
        (hP.trans hQ.symm) τ, hτ, hω P]
    rfl
  rw [← hdiv]
  exact hK₀.of_linearlyEquivalent (by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hX' hK₀ hω'0)

end Canonical

/-! ### Snc divisors along open immersions -/

section SNC

/-- Smoothness is local on the source: if open immersions `ι : T ⟶ X` and `j : T ⟶ X'` satisfy
`j ≫ s' = ι ≫ s`, then `j t` is a smooth point of `s'` exactly when `ι t` is one of `s`. -/
theorem _root_.MMP.Mori.mem_smoothLocus_iff_of_comp_eq {T X X' S : Scheme.{u}} (ι : T ⟶ X)
    (j : T ⟶ X') [IsOpenImmersion ι] [IsOpenImmersion j] (s : X ⟶ S) (s' : X' ⟶ S)
    [LocallyOfFinitePresentation s] [LocallyOfFinitePresentation s'] (h : j ≫ s' = ι ≫ s)
    (t : T) : j t ∈ s'.smoothLocus ↔ ι t ∈ s.smoothLocus := by
  change t ∈ j ⁻¹ᵁ s'.smoothLocus ↔ t ∈ ι ⁻¹ᵁ s.smoothLocus
  rw [Scheme.Hom.preimage_smoothLocus_eq, Scheme.Hom.preimage_smoothLocus_eq]
  have key : ∀ (g : T ⟶ S) [LocallyOfFinitePresentation g], g = ι ≫ s →
      (t ∈ g.smoothLocus ↔ t ∈ (ι ≫ s).smoothLocus) := by
    rintro g _ rfl; rfl
  exact key _ h

open MMP.Threefold.Mori.OpenRestriction in
/-- **Being snc passes to smaller opens.** If `j₁, j₂` are open immersions into `X` with the image
of `j₁` contained in that of `j₂`, and the restriction of `D` along `j₂` is snc, so is its
restriction along `j₁`. -/
theorem _root_.MMP.Mori.DivisorWithCoeffs.IsSNC.comapDomain_of_range_subset {R : Type*} [Zero R]
    {X Y V₁ V₂ : Scheme.{u}} (g : X ⟶ Y)
    [∀ E : PrimeDivisor X, LocallyOfFinitePresentation (E.idealSheaf.subschemeι ≫ g)]
    (j₁ : V₁ ⟶ X) (j₂ : V₂ ⟶ X) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (h : Set.range j₁ ⊆ Set.range j₂) (D : DivisorWithCoeffs R X)
    (hD : DivisorWithCoeffs.IsSNC (j₂ ≫ g)
      (Finsupp.comapDomain (OpenWeilRestriction.primeDivisorMap j₂) D
        (OpenWeilRestriction.primeDivisorMap_injective j₂).injOn)) :
    DivisorWithCoeffs.IsSNC (j₁ ≫ g)
      (Finsupp.comapDomain (OpenWeilRestriction.primeDivisorMap j₁) D
        (OpenWeilRestriction.primeDivisorMap_injective j₁).injOn) := by
  refine ⟨fun E₀ hE₀ => ?_, fun x => ?_⟩
  · have hDE : D (OpenWeilRestriction.primeDivisorMap j₁ E₀) ≠ 0 :=
      (Finsupp.mem_support_iff.mp hE₀ :)
    refine (isSmoothScheme_comap_iff j₁ g (OpenWeilRestriction.primeDivisorMap j₁ E₀).idealSheaf
      E₀.idealSheaf (idealSheaf_comap_primeDivisorMap j₁ E₀)).mpr ?_
    rintro z ⟨u, hu⟩
    obtain ⟨w, hw⟩ := h ⟨u, hu⟩
    have hEsupp : (OpenWeilRestriction.primeDivisorMap j₁ E₀).idealSheaf.subschemeι z ∈
        (OpenWeilRestriction.primeDivisorMap j₁ E₀).support := by
      have hr : (OpenWeilRestriction.primeDivisorMap j₁ E₀).idealSheaf.subschemeι z ∈
          Set.range (OpenWeilRestriction.primeDivisorMap j₁ E₀).idealSheaf.subschemeι :=
        ⟨z, rfl⟩
      rwa [Scheme.IdealSheafData.range_subschemeι] at hr
    obtain ⟨E', hE'⟩ := exists_primeDivisorMap_eq_of_mem_support j₂
      (OpenWeilRestriction.primeDivisorMap j₁ E₀) w (hw ▸ hEsupp)
    have hE'supp : E' ∈ (Finsupp.comapDomain (OpenWeilRestriction.primeDivisorMap j₂) D
        (OpenWeilRestriction.primeDivisorMap_injective j₂).injOn).support := by
      rw [Finsupp.mem_support_iff]
      change D (OpenWeilRestriction.primeDivisorMap j₂ E') ≠ 0
      rwa [hE']
    exact (isSmoothScheme_comap_iff j₂ g
      (OpenWeilRestriction.primeDivisorMap j₁ E₀).idealSheaf E'.idealSheaf
      (hE' ▸ idealSheaf_comap_primeDivisorMap _ E')).mp (hD.1 E' hE'supp) z ⟨w, hw⟩
  · obtain ⟨w, hw⟩ := h ⟨x, rfl⟩
    have h1 : SNCStalk D (j₂ w) := (sncStalk_restrict_iff j₂ D w).mp (hD.2 w)
    rw [hw] at h1
    exact (sncStalk_restrict_iff j₁ D x).mpr h1

end SNC

/-! ### Divisors over `X` and over `X⁺` -/

section DivisorsOver

/-- A divisor over `X` whose centre has its generic point outside an open `U` has its whole
centre outside `U`. -/
private theorem center_subset_compl {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (D : DivisorOver k sX) {U : X.Opens}
    (h : D.f D.E.genericPoint ∉ U) : (D.center : Set X) ⊆ (U : Set X)ᶜ := by
  rw [D.center_eq_closure_genericPoint]
  exact closure_minimal (Set.singleton_subset_iff.mpr h) U.isOpen.isClosed_compl

/-- Let `D` be a divisor over an integral scheme `X` and `f : X ⟶ Y` dominant. The valuation of
`D`, read on `k(Y)` through `f`, dominates the local ring of `Y` at `f(x)`, where `x` is the
generic point of the center of `D`. -/
private theorem valuation_comap_dominates {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f]
    (D : DivisorOver k sX) :
    (∀ a : Y.presheaf.stalk (f (D.f D.E.genericPoint)),
      D.valuation.comap (functionFieldMap f) (algebraMap _ Y.functionField a) ≤ 1) ∧
    (∀ a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk (f (D.f D.E.genericPoint))),
      D.valuation.comap (functionFieldMap f) (algebraMap _ Y.functionField a) < 1) := by
  refine ⟨fun a ↦ ?_, fun a ha ↦ ?_⟩
  · rw [Valuation.comap_apply, MMP.Mori.functionFieldMap_algebraMap_stalk]
    exact MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D _ rfl _
  · rw [Valuation.comap_apply, MMP.Mori.functionFieldMap_algebraMap_stalk]
    refine MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one D _ rfl _ ?_
    exact (IsLocalRing.mem_maximalIdeal _).2 fun hu ↦
      (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit _ _ hu)

/-- Divisors `D` over `X` and `D'` over `X'` whose valuations agree on `k(Y)`, read through
dominant morphisms `f : X ⟶ Y` and `f' : X' ⟶ Y` to a separated `Y`, have the same center
on `Y`. -/
theorem _root_.MMP.Mori.map_genericPoint_eq_of_valuation_comap_eq {k : Type u} [Field k]
    {X X' Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    (sY : Y ⟶ Spec (.of k)) [IsSeparated sY] [IsIntegral X] [IsIntegral X'] [IsIntegral Y]
    (f : X ⟶ Y) (f' : X' ⟶ Y) [IsDominant f] [IsDominant f'] (D : DivisorOver k sX)
    (D' : DivisorOver k sX')
    (h : D.valuation.comap (functionFieldMap f) = D'.valuation.comap (functionFieldMap f')) :
    f (D.f D.E.genericPoint) = f' (D'.f D'.E.genericPoint) := by
  obtain ⟨h1, h2⟩ := valuation_comap_dominates f D
  obtain ⟨h1', h2'⟩ := valuation_comap_dominates f' D'
  rw [← h] at h1' h2'
  exact MMP.Positivity.DivisorOver.eq_of_dominates sY _ h1 h2 h1' h2'

/-- **Divisors over `X⁺` are divisors over `X`.** Let `f : X ⟶ Y` be a proper birational
morphism from a normal variety and `f⁺ : X⁺ ⟶ Y` a birational morphism. Every divisor `D⁺` over
`X⁺` has, read on `k(Y)`, the valuation of a divisor `D` over `X`. -/
theorem _root_.MMP.Mori.exists_divisorOver_valuation_comap_eq {k : Type u} [Field k]
    {X X' Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsIntegral X'] {f : X ⟶ Y}
    {fp : X' ⟶ Y} (hX : IsNormalVariety k (f ≫ sY)) (hf : IsBirationalMorphism f) [IsProper f]
    (hfp : IsBirationalMorphism fp) (D' : DivisorOver k (fp ≫ sY)) :
    haveI : IsIntegral X := hX.1.toIsIntegral
    haveI : IsDominant f := hf.isDominant
    haveI : IsDominant fp := hfp.isDominant
    ∃ D : DivisorOver k (f ≫ sY),
      D.valuation.comap (functionFieldMap f) = D'.valuation.comap (functionFieldMap fp) := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsDominant f := hf.isDominant
  have : IsDominant fp := hfp.isDominant
  have hbX := hf.functionFieldMap_bijective
  let e : Y.functionField ≃+* X.functionField := RingEquiv.ofBijective (functionFieldMap f) hbX
  set ξY : Valuation Y.functionField ℤᵐ⁰ := D'.valuation.comap (functionFieldMap fp)
  let ξ : Valuation X.functionField ℤᵐ⁰ := ξY.comap (e.symm : X.functionField →+* Y.functionField)
  have hξ : ξ.comap (functionFieldMap f) = ξY := by
    ext t
    change ξY (e.symm (functionFieldMap f t)) = ξY t
    rw [show e.symm (functionFieldMap f t) = t from e.symm_apply_apply t]
  obtain ⟨hz1, -⟩ := valuation_comap_dominates fp D'
  -- `ξ` dominates the local ring of a point of `X` (valuative criterion for `f`)
  obtain ⟨x, h1, h2⟩ : ∃ x : X, (∀ a : X.presheaf.stalk x,
      ξ (algebraMap _ X.functionField a) ≤ 1) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x),
        ξ (algebraMap _ X.functionField a) < 1 := by
    set z := fp (D'.f D'.E.genericPoint)
    have hw : ∀ b : Y.presheaf.stalk z,
        ξ (functionFieldMap f (algebraMap _ Y.functionField b)) =
          ξY (algebraMap _ Y.functionField b) := by
      intro b
      simpa only [Valuation.comap_apply] using
        congrArg (fun v => v (algebraMap _ Y.functionField b)) hξ
    let R := ξ.valuationSubring
    let φ : Y.presheaf.stalk z →+* R :=
      ((functionFieldMap f).comp (algebraMap (Y.presheaf.stalk z) Y.functionField)).codRestrict R
        fun b => (ξ.mem_valuationSubring_iff _).2 (by
          rw [RingHom.comp_apply, hw]
          exact hz1 b)
    have hgen : genericPoint Y ⤳ z := (genericPoint_spec Y).specializes trivial
    have hex : ValuativeCriterion.Existence f := by
      have h : @IsProper _ _ f := inferInstance
      rw [IsProper.eq_valuativeCriterion] at h
      exact h.1.1.1.existence
    let S : ValuativeCommSq f :=
      { R := R
        K := X.functionField
        i₁ := X.fromSpecStalk (genericPoint X)
        i₂ := Spec.map (CommRingCat.ofHom φ) ≫ Y.fromSpecStalk z
        commSq := ⟨by
          rw [← functionFieldMap_fromSpecStalk f,
            ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgen, ← Category.assoc,
            ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
          rfl⟩ }
    obtain ⟨⟨l, hl₁, -⟩⟩ := (hex S).exists_lift
    have hl₁' : Spec.map (CommRingCat.ofHom (algebraMap R X.functionField)) ≫ l =
        X.fromSpecStalk (genericPoint X) := hl₁
    set x := l (IsLocalRing.closedPoint R)
    have hx : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
    let g := Scheme.stalkClosedPointTo l
    have hg : g ≫ CommRingCat.ofHom (algebraMap R X.functionField) =
        X.presheaf.stalkSpecializes hx := by
      apply Spec.map_injective
      apply (cancel_mono (X.fromSpecStalk x)).mp
      rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hl₁',
        Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    have hga : ∀ a : X.presheaf.stalk x,
        algebraMap _ X.functionField a = ((g.hom a : R) : X.functionField) := fun a =>
      (congrArg (fun q => q.hom a) hg).symm
    refine ⟨x, fun a => ?_, fun a ha => ?_⟩
    · rw [hga]; exact (g.hom a).2
    · rw [hga]
      exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp
        (fun hu => (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit g.hom a hu))
  -- `ξ` is a divisor of `k(X)`: `ord_E` on `D'.Y`, along `k(X) ≅ k(Y) ≅ k(X⁺) ≅ k(D'.Y)`
  have : AlgebraicGeometry.IsVariety k (f ≫ sY) := hX.1
  have hdiv : MMP.Flips.IsDivisorOfFunctionField k (f ≫ sY) ξ := by
    have := D'.isIntegral
    have := D'.isNormal
    have := D'.isLocallyNoetherian
    have := D'.isDominant
    refine ⟨D'.Y, D'.f ≫ fp ≫ sY, D'.isNormalVariety, D'.E, ?_⟩
    let := MMP.Mori.functionFieldAlgebra sY
    let := MMP.Mori.functionFieldAlgebra (f ≫ sY)
    let := MMP.Mori.functionFieldAlgebra (fp ≫ sY)
    let := MMP.Mori.functionFieldAlgebra (D'.f ≫ fp ≫ sY)
    let eX := MMP.Mori.functionFieldAlgEquiv sY f hbX
    let eX' := MMP.Mori.functionFieldAlgEquiv sY fp hfp.functionFieldMap_bijective
    let eY := MMP.Mori.functionFieldAlgEquiv (fp ≫ sY) D'.f
      D'.isBirationalMorphism.functionFieldMap_bijective
    refine ⟨eX.symm.trans (eX'.trans eY), ?_⟩
    ext t
    obtain ⟨s, rfl⟩ := hbX.2 t
    have h1 : eX.symm (functionFieldMap f s) = s := eX.symm_apply_apply s
    change ξY (e.symm (functionFieldMap f s)) =
      D'.E.divisorialValuation (eY (eX' (eX.symm (functionFieldMap f s))))
    rw [h1, show e.symm (functionFieldMap f s) = s from e.symm_apply_apply s]
    rfl
  obtain ⟨D, -, hv, -⟩ :=
    MMP.Flips.exists_properDivisorOver_isProjective_of_dominates (f ≫ sY) hdiv x h1 h2
  refine ⟨D.toDivisorOver, ?_⟩
  change D.valuation.comap _ = _
  rw [hv, hξ]

end DivisorsOver

/-! ### Relative nefness and push-forwards -/

section Comparison

/-- A `ℚ`-divisor with an `f`-ample Cartier multiple is `f`-nef. -/
theorem _root_.MMP.Mori.isRelativelyNef_of_hasRelativelyAmpleMultiple {k : Type u} [Field k]
    {X Y : Scheme.{u}} [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {f : X ⟶ Y} {D : QDivisor X}
    (h : D.HasRelativelyAmpleMultiple f) : D.IsRelativelyNef sX f := by
  obtain ⟨m, hm, L, hL, hLD, hamp⟩ := h
  have hq : D.IsQCartier := ⟨m, by exact_mod_cast hm.ne', L, hLD, hL⟩
  refine ⟨hq, fun C hC => ?_⟩
  rw [QDivisor.associatedCartier, CartierDivisorWithCoeffs.ofCartier, Finsupp.smul_single,
    Finsupp.sum_single_index (by simp)]
  set F : Divisor X := (D.cartierIndexSMul hq : Divisor X)
  have hFc : F.IsCartier := (D.cartierIndexSMul hq).2
  set N := D.cartierIndex hq
  have hLpos : 0 < L.degreeOn k sX C.ι C.dim_le hL := by
    have := hL.isInvertibleModule_divisorialSheaf
    exact MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy f
      L.divisorialSheaf hamp C hC
  have hFL : m • F = N • L := by
    apply Divisor.toQDivisor_injective
    rw [map_nsmul, map_nsmul, QDivisor.toQDivisor_cartierIndexSMul, hLD, ← natCast_zsmul,
      ← natCast_zsmul, smul_smul, smul_smul, mul_comm]
  have key : (m : ℤ) * F.degreeOn k sX C.ι C.dim_le hFc =
      N * L.degreeOn k sX C.ι C.dim_le hL := by
    rw [← Divisor.degreeOn_nsmul', ← Divisor.degreeOn_nsmul', Divisor.degreeOn_congr hFL]
  have hFpos : 0 ≤ F.degreeOn k sX C.ι C.dim_le hFc :=
    nonneg_of_mul_nonneg_right (a := (m : ℤ)) (by rw [key]; positivity) (by exact_mod_cast hm)
  exact mul_nonneg (by positivity) (by exact_mod_cast hFpos)

/-- For a proper birational morphism `g : X' ⟶ Y` onto a normal variety with exceptional set of
codimension at least two, `g_* g⁻¹_* B = B` for every divisor `B` on `Y`. -/
theorem _root_.MMP.Mori.transformDivisor_inverseTransformDivisor {k : Type u} [Field k]
    {X' Y : Scheme.{u}} [IsLocallyNoetherian X'] [IsNormal X'] {sY : Y ⟶ Spec (.of k)}
    (hY : IsNormalVariety k sY) {g : X' ⟶ Y}
    (hX' : IsNormalVariety k (g ≫ sY)) [IsProper g] (hg : IsBirationalMorphism g)
    (h2 : 2 ≤ closedsCodimension (exceptionalSet g)) {R : Type*} [AddCommMonoid R]
    (B : DivisorWithCoeffs R Y) :
    MMP.Mori.RationalMap.transformDivisor (X := X') g.toRationalMap
      (inverseTransformDivisor g B) = B := by
  have : IsIntegral Y := hY.1.toIsIntegral
  have : IsNormal Y := hY.2
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsIntegral X' := hX'.1.toIsIntegral
  have : CompactSpace Y := (hY.1.toQuasiCompact).compactSpace_of_compactSpace
  have : IsDominant g := hg.isDominant
  refine Finsupp.ext fun Q => ?_
  obtain ⟨E, hEQ, -, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hY hX' hg Q
  rw [htr]
  have hQV : g E.genericPoint ∈ biregularLocus g := by
    rw [hEQ]
    exact MMP.Positivity.mem_biregularLocus_of_coheight_le_one g hg.functionFieldMap_bijective h2
      Q.coheight_genericPoint.le
  refine MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    (MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hEQ hQV)
    (fun Q' hQ' => ?_) B
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    ((MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
      hQ').1.symm.trans hEQ)

/-- **Strict comparison over the flipping locus.** Let `f⁺ : X⁺ ⟶ Y` be a `(K + Δ)`-flip of
`f : X ⟶ Y`, and let `D` over `X` and `D'` over `X⁺` be divisors with the same valuation which are
exceptional over `Y`. If the centre of `D` on `Y` lies in `f(Ex f) ∪ f⁺(Ex f⁺)`, then
`a(D, X, Δ) < a(D', X⁺, Δ⁺)`. -/
private theorem isDiscrepancy_lt_of_mem_image_exceptionalSet {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {n : ℕ} {X X' Y : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    {K : Divisor X} {Δ : QDivisor X} {f : X ⟶ Y} {fp : X' ⟶ Y}
    (hK : K.IsCanonicalDivisor sX n) (hflip : IsFlip sX sY sX' K Δ f fp)
    (hK' : Divisor.IsCanonicalDivisor sX' n (flipTransform f fp K))
    (D : DivisorOver k sX) (D' : DivisorOver k sX')
    (hv : haveI : IsIntegral Y := hflip.isFlippingContraction.isNormalVariety_target.1.toIsIntegral
      haveI : IsDominant f := hflip.isFlippingContraction.isBirationalMorphism.isDominant
      haveI : IsDominant fp := hflip.isBirationalMorphism.isDominant
      D.valuation.comap (functionFieldMap f) = D'.valuation.comap (functionFieldMap fp))
    (hE : RationalMap.IsExceptional (X := D.Y) (D.f ≫ f).toRationalMap D.E)
    (hW : f (D.f D.E.genericPoint) ∈
      f '' (exceptionalSet f : Set X) ∪ fp '' (exceptionalSet fp : Set X'))
    {a a' : ℚ} (ha : IsDiscrepancy sX n K Δ D a)
    (ha' : IsDiscrepancy sX' n (flipTransform f fp K) (flipTransform f fp Δ) D' a') :
    a < a' := by
  have hFC := hflip.isFlippingContraction
  have hYv := hFC.isNormalVariety_target
  have : IsProper f := hFC.isProper
  have : IsProper fp := hflip.isProper
  have : IsIntegral Y := hYv.1.toIsIntegral
  have : IsSeparated sY := hYv.1.toIsSeparated
  have : IsDominant f := hFC.isBirationalMorphism.isDominant
  have : IsDominant fp := hflip.isBirationalMorphism.isDominant
  have : QuasiCompact sX := hFC.isNormalVariety_source.1.toQuasiCompact
  have : QuasiCompact sX' := hflip.isNormalVariety.1.toQuasiCompact
  have hN := isRelativelyNef_of_hasRelativelyAmpleMultiple (sX := sX)
    hFC.hasRelativelyAmpleMultiple
  have hN' := isRelativelyNef_of_hasRelativelyAmpleMultiple (sX := sX')
    hflip.hasRelativelyAmpleMultiple
  have hΔY := (transformDivisor_inverseTransformDivisor hYv
    (by rw [hflip.comp_eq]; exact hflip.isNormalVariety) hflip.isBirationalMorphism
    hflip.two_le_codimension
    (MMP.Mori.RationalMap.transformDivisor (X := X) f.toRationalMap Δ)).symm
  rcases hW with h1 | h1
  · rw [MMP.Positivity.image_exceptionalSet_eq f f.surjective] at h1
    exact isDiscrepancy_lt_of_neg_hasRelativelyAmpleMultiple hFC.isNormalVariety_source
      hflip.isNormalVariety hYv hFC.comp_eq hflip.comp_eq hFC.isBirationalMorphism
      hflip.isBirationalMorphism hK hK' hΔY hN hN' hFC.hasRelativelyAmpleMultiple D D' hv hE h1
      ha ha'
  · rw [MMP.Positivity.image_exceptionalSet_eq fp fp.surjective,
      map_genericPoint_eq_of_valuation_comap_eq sY f fp D D' hv] at h1
    exact isDiscrepancy_lt_of_hasRelativelyAmpleMultiple_target hFC.isNormalVariety_source
      hflip.isNormalVariety hYv hFC.comp_eq hflip.comp_eq hFC.isBirationalMorphism
      hflip.isBirationalMorphism hK hK' hΔY hN hN' D D' hv hE hflip.hasRelativelyAmpleMultiple h1
      ha ha'

end Comparison

end Proof_thm_km3c_dlt_preserved_flip

namespace MMP.Mori

open CategoryTheory
open AlgebraicGeometry hiding PrimeDivisor
open Proof_thm_km3c_dlt_preserved_flip

/-! ### The locus over which both contractions are isomorphisms -/

/-- A flip `f⁺` of `f` and `f` itself are isomorphisms over an open `V ⊆ Y` over which lie the
points of codimension at most one of `X` and of `X⁺`: the complement of
`f(Ex f) ∪ f⁺(Ex f⁺)`. -/
public theorem IsFlip.exists_opens_isIso {k : Type u} [Field k] {X X' Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    {K : Divisor X} {Δ : QDivisor X} {f : X ⟶ Y} {fp : X' ⟶ Y}
    (hflip : IsFlip sX sY sX' K Δ f fp) :
    ∃ V : Y.Opens, IsIso (f ∣_ V) ∧ IsIso (fp ∣_ V) ∧
      (∀ x : X, Order.coheight x ≤ 1 → f x ∈ V) ∧
      (∀ x : X', Order.coheight x ≤ 1 → fp x ∈ V) ∧
      ∀ y ∉ V, y ∈ f '' (exceptionalSet f : Set X) ∪ fp '' (exceptionalSet fp : Set X') := by
  obtain ⟨hW, hbf, hbp, hcf, hcp, -⟩ :=
    MMP.Positivity.IsFlip.exists_isClosed_image_exceptionalSet hflip
  exact ⟨⟨_, hW.isOpen_compl⟩, hbf, hbp, fun x hx => notMem_of_coheight_le_one hcf hx,
    fun x hx => notMem_of_coheight_le_one hcp hx, fun _ hy => not_not.mp hy⟩

/-- A small contraction `f : X ⟶ Y` is an isomorphism over an open `W ⊆ Y` whose complement has
codimension at least two and over which lie the points of codimension at most one of `X`. -/
private theorem _root_.MMP.Flips.IsSmall.exists_opens_isIso_of_two_le_coheight_compl
    {k : Type u} [Field k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {sY : Y ⟶ Spec (.of k)} {f : X ⟶ Y}
    (hf : MMP.Flips.IsSmall k sY sX f) :
    ∃ W : Y.Opens, IsIso (f ∣_ W) ∧ (∀ y ∉ W, 2 ≤ Order.coheight y) ∧
      ∀ x : X, Order.coheight x ≤ 1 → f x ∈ W := by
  obtain ⟨V, W, hV, hW, h, hiso⟩ := hf.exists_isIso
  have hV' := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hV
  have hW' := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hW
  have : IsIntegral X := hf.isVariety_source.toIsIntegral
  have : IsProper f := hf.isProper
  have hVc : ∀ x : X, Order.coheight x ≤ 1 → x ∈ V.compl := fun x hx hxV =>
    absurd ((hV' x hxV).trans hx) (by decide)
  refine ⟨W.compl, ?_, fun y hy => hW' y (not_not.mp hy), fun x hx => h (hVc x hx)⟩
  set j := X.homOfLE h
  have hjg : j ≫ (f ∣_ W.compl) = f.resLE W.compl V.compl h := rfl
  set s := inv (f.resLE W.compl V.compl h) ≫ j
  have : IsClosedImmersion (s ≫ (f ∣_ W.compl)) := by
    rw [show s ≫ (f ∣_ W.compl) = 𝟙 _ by simp [s, hjg]]; infer_instance
  have : IsClosedImmersion s := IsClosedImmersion.of_comp s (f ∣_ W.compl)
  have : IsClosedImmersion j := by
    rw [show j = f.resLE W.compl V.compl h ≫ s by simp [s]]; infer_instance
  have hgen : genericPoint X ∈ (V.compl : Set X) :=
    hVc _ ((Order.coheight_eq_zero.mpr fun z _ => genericPoint_specializes z).trans_le
      zero_le_one)
  have : Nonempty (f ⁻¹ᵁ W.compl) := ⟨⟨_, h hgen⟩⟩
  have hrange : Set.range j = Set.univ :=
    (isClopen_iff.mp ⟨j.isClosedEmbedding.isClosed_range, j.isOpenEmbedding.isOpen_range⟩
      ).resolve_left (Set.nonempty_iff_ne_empty.mp ⟨_, ⟨⟨_, hgen⟩, rfl⟩⟩)
  have : Surjective j := ⟨Set.range_eq_univ.mp hrange⟩
  have : IsIso j := (isIso_iff_isOpenImmersion_and_surjective j).mpr ⟨inferInstance, inferInstance⟩
  rw [show f ∣_ W.compl = inv j ≫ f.resLE W.compl V.compl h by rw [← hjg]; simp]
  infer_instance

/-- Two small contractions `f : X ⟶ Y` and `f⁺ : X⁺ ⟶ Y` are isomorphisms over an open
`V ⊆ Y` over which lie the points of codimension at most one of `X` and of `X⁺`. -/
public theorem exists_opens_isIso_of_isSmall {k : Type u} [Field k] {X X' Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} {f : X ⟶ Y}
    {fp : X' ⟶ Y} (hf : MMP.Flips.IsSmall k sY sX f) (hfp : MMP.Flips.IsSmall k sY sX' fp) :
    ∃ V : Y.Opens, IsIso (f ∣_ V) ∧ IsIso (fp ∣_ V) ∧
      (∀ x : X, Order.coheight x ≤ 1 → f x ∈ V) ∧
      (∀ x : X', Order.coheight x ≤ 1 → fp x ∈ V) := by
  obtain ⟨W, hW, hWc, hWx⟩ := hf.exists_opens_isIso_of_two_le_coheight_compl
  obtain ⟨W', hW', hW'c, hW'x⟩ := hfp.exists_opens_isIso_of_two_le_coheight_compl
  have hmem : ∀ {Z : Scheme.{u}} (g : Z ⟶ Y) {U U' : Y.Opens} [IsIso (g ∣_ U)],
      (∀ y ∉ U', 2 ≤ Order.coheight y) → ∀ x : Z, g x ∈ U → Order.coheight x ≤ 1 →
        g x ∈ U ⊓ U' := fun g _ _ _ hU' x hx h1 =>
    ⟨hx, by_contra fun hn => absurd ((hU' _ hn).trans
      ((MMP.Positivity.coheight_map_of_mem_biregularLocus g
        (isBiregular_iff_le_biregularLocus.mp ‹_› hx)).trans_le h1)) (by decide)⟩
  refine ⟨W ⊓ W', ?_, ?_, fun x hx => hmem f hW'c x (hWx x hx) hx, fun x hx => ?_⟩
  · exact isBiregular_iff_le_biregularLocus.mpr
      (inf_le_left.trans (isBiregular_iff_le_biregularLocus.mp hW))
  · exact isBiregular_iff_le_biregularLocus.mpr
      (inf_le_right.trans (isBiregular_iff_le_biregularLocus.mp hW'))
  · rw [inf_comm]; exact hmem fp hWc x (hW'x x hx) hx

section

variable {k : Type u} [Field k] {n : ℕ} {X X' Y : Scheme.{u}}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
  {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
  {K : Divisor X} {Δ : QDivisor X} {f : X ⟶ Y} {fp : X' ⟶ Y}

/-- **The flip transforms divisors as `(f⁺)⁻¹_* f_*`.** For a flip `φ : X ⤏ X⁺`, given by
`f⁺ : X⁺ ⟶ Y`, of `f : X ⟶ Y`, the push-forward `φ_* D` of a divisor `D` on `X` is
`(f⁺)⁻¹_* f_* D`. -/
public theorem IsFlipRationalMap.transformDivisor_eq_flipTransform {φ : RationalMap X X'}
    (hφ : IsFlipRationalMap sX sY sX' K Δ f fp φ) {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R X) : φ.transformDivisor D = flipTransform f fp D := by
  obtain ⟨hflip, hcomp⟩ := hφ
  have hFC := hflip.isFlippingContraction
  have : IsProper f := hFC.isProper
  have := hflip.isNormalVariety.1.toIsSeparated
  have : IsSeparated (X' ↘ ⊤_ Scheme) := by
    rw [show (X' ↘ ⊤_ Scheme) = sX' ≫ Limits.terminal.from (Spec (.of k)) from
      Subsingleton.elim _ _]
    infer_instance
  obtain ⟨V, _, _, hXV, hX'V, -⟩ := hflip.exists_opens_isIso
  exact transformDivisor_eq_flipTransform_of_isIso_restrict
    hFC.isNormalVariety_target (hFC.comp_eq ▸ hFC.isNormalVariety_source)
    hFC.isBirationalMorphism V hXV hX'V hcomp D

/-- **Divisors over the flip are divisors over `X`.** For a flip `f⁺ : X⁺ ⟶ Y` of `f : X ⟶ Y`,
every divisor `D⁺` over `X⁺` has, read on `k(Y)`, the valuation of a divisor `D` over `X`. -/
public theorem IsFlip.exists_divisorOver_valuation_comap_eq [IsIntegral X']
    (hflip : IsFlip sX sY sX' K Δ f fp) (D' : DivisorOver k sX') :
    haveI : IsIntegral Y := hflip.isFlippingContraction.isNormalVariety_target.1.toIsIntegral
    haveI : IsDominant f := hflip.isFlippingContraction.isBirationalMorphism.isDominant
    haveI : IsDominant fp := hflip.isBirationalMorphism.isDominant
    ∃ D : DivisorOver k sX,
      D.valuation.comap (functionFieldMap f) = D'.valuation.comap (functionFieldMap fp) := by
  have hFC := hflip.isFlippingContraction
  have : IsProper f := hFC.isProper
  have : IsIntegral Y := hFC.isNormalVariety_target.1.toIsIntegral
  obtain ⟨D₀, hv⟩ := _root_.MMP.Mori.exists_divisorOver_valuation_comap_eq
    (by rw [hFC.comp_eq]; exact hFC.isNormalVariety_source) hFC.isBirationalMorphism
    hflip.isBirationalMorphism
    ⟨D'.Y, D'.f, by rw [hflip.comp_eq]; exact D'.isNormalVariety, D'.isBirationalMorphism, D'.E⟩
  exact ⟨⟨D₀.Y, D₀.f, by rw [← hFC.comp_eq]; exact D₀.isNormalVariety, D₀.isBirationalMorphism,
    D₀.E⟩, hv⟩

/-- **The canonical divisor of a flip.** If `K` is a canonical divisor of `X` and `f⁺ : X⁺ ⟶ Y`
is a `(K + Δ)`-flip of `f : X ⟶ Y`, then `(f⁺)⁻¹_* f_* K` is a canonical divisor of `X⁺`. -/
public theorem IsFlip.isCanonicalDivisor_flipTransform [PerfectField k] [IsIntegral X']
    (hK : K.IsCanonicalDivisor sX n) (hflip : IsFlip sX sY sX' K Δ f fp) :
    Divisor.IsCanonicalDivisor sX' n (flipTransform f fp K) := by
  have hFC := hflip.isFlippingContraction
  have : IsProper f := hFC.isProper
  obtain ⟨V, _, _, hXV, hX'V, -⟩ := hflip.exists_opens_isIso
  have := isCanonicalDivisor_flipTransform_of_isIso_restrict
    hFC.isNormalVariety_target
    (hFC.comp_eq ▸ hFC.isNormalVariety_source) (hflip.comp_eq ▸ hflip.isNormalVariety)
    hFC.isBirationalMorphism hflip.isBirationalMorphism V hXV hX'V (n := n) (hFC.comp_eq ▸ hK)
  rwa [hflip.comp_eq] at this

/-- **Flips preserve dlt pairs**, with the flip given by its morphism `f⁺ : X⁺ ⟶ Y`. Let `(X, Δ)`
be a dlt pair with canonical divisor `K` of dimension `n`, over an algebraically closed field of
characteristic zero, and let `f⁺ : X⁺ ⟶ Y` be a `(K + Δ)`-flip of the flipping contraction
`f : X ⟶ Y`. Then `(X⁺, (f⁺)⁻¹_* f_* Δ)` is dlt, with canonical divisor `(f⁺)⁻¹_* f_* K`. -/
public theorem IsFlip.isDltPair [IsAlgClosed k] [CharZero k] [IsIntegral X']
    (h : IsDltPair sX n K Δ) (hflip : IsFlip sX sY sX' K Δ f fp) :
    IsDltPair sX' n (flipTransform f fp K) (flipTransform f fp Δ) := by
  have hlc := h.isLcPair
  obtain ⟨hpair, hcoeff, U, hUsm, hsnc, hZ⟩ := h
  have hFC := hflip.isFlippingContraction
  have hXv := hFC.isNormalVariety_source
  have hYv := hFC.isNormalVariety_target
  have hX'v := hflip.isNormalVariety
  have hfs := hFC.comp_eq
  have hfs' := hflip.comp_eq
  have hf := hFC.isBirationalMorphism
  have hfp := hflip.isBirationalMorphism
  have hXv' : IsNormalVariety k (f ≫ sY) := by rw [hfs]; exact hXv
  have : IsProper f := hFC.isProper
  have : IsProper fp := hflip.isProper
  have : IsIntegral Y := hYv.1.toIsIntegral
  have : IsNormal Y := hYv.2
  have : LocallyOfFiniteType sY := hYv.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsSeparated sY := hYv.1.toIsSeparated
  have : IsDominant f := hf.isDominant
  have : IsDominant fp := hfp.isDominant
  have : QuasiCompact sX := hXv.1.toQuasiCompact
  have : QuasiCompact sX' := hX'v.1.toQuasiCompact
  have : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType sX' := hX'v.1.toLocallyOfFiniteType
  -- `f` and `f⁺` are isomorphisms over `V = Y ∖ (f(Ex f) ∪ f⁺(Ex f⁺))`
  obtain ⟨V, _, _, hXV, hX'V, hVc⟩ := hflip.exists_opens_isIso
  have hP'V : ∀ P' : PrimeDivisor X', fp P'.genericPoint ∈ V := fun P' =>
    hX'V _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P').le
  -- the coefficients of `Δ⁺ = (f⁺)⁻¹_* f_* Δ`
  have hΔP : ∀ (P : PrimeDivisor X) (P' : PrimeDivisor X'),
      f P.genericPoint = fp P'.genericPoint → flipTransform f fp Δ P' = Δ P := fun P P' hPP =>
    flipTransform_apply hYv hXv' hf V hXV hPP Δ
  -- `K_{X⁺} = (f⁺)⁻¹_* f_* K` is a canonical divisor, and `(X⁺, Δ⁺)` is a pair
  have hK' := hflip.isCanonicalDivisor_flipTransform hpair.2.1
  have hpair' : IsPairWith sX' n (flipTransform f fp K) (flipTransform f fp Δ) :=
    ⟨hX'v, hK', hflip.isQCartier⟩
  -- the open `U⁺ ⊆ X⁺` corresponding to `U ∩ f⁻¹(V)`
  set S : X.Opens := U ⊓ f ⁻¹ᵁ V
  let j : S.toScheme ⟶ X' :=
    X.homOfLE (inf_le_right : S ≤ f ⁻¹ᵁ V) ≫ (f ∣_ V) ≫ inv (fp ∣_ V) ≫ (fp ⁻¹ᵁ V).ι
  have hj : j ≫ fp = S.ι ≫ f := by
    simp only [j, Category.assoc]
    rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc, morphismRestrict_ι,
      Scheme.homOfLE_ι_assoc]
  have hjs : j ≫ sX' = S.ι ≫ sX := by
    rw [← hfs', ← hfs, ← Category.assoc, hj, Category.assoc]
  have hjapp : ∀ s : S.toScheme, fp (j s) = f (S.ι s) := fun s =>
    congrArg (fun g => g.base s) hj
  have hjV : ∀ s : S.toScheme, fp (j s) ∈ V := fun s => by
    rw [hjapp]; exact s.2.2
  have hU' : ∀ (x' : X') (z : X), f z ∈ V → f z = fp x' → z ∈ U → x' ∈ j.opensRange := by
    intro x' z hzV hzx hzU
    let s : S.toScheme := ⟨z, hzU, hzV⟩
    refine ⟨s, eq_of_apply_eq fp V (hjV s) (hzx ▸ hzV) ((hjapp s).trans hzx)⟩
  refine ⟨hpair', fun P' => ?_, j.opensRange, ?_, ?_, ?_⟩
  · -- the coefficients of `Δ⁺` lie in `[0, 1]`
    obtain ⟨P, hP⟩ := exists_primeDivisor_genericPoint_eq f fp V P' (hP'V P')
    change 0 ≤ flipTransform f fp Δ P' ∧ flipTransform f fp Δ P' ≤ 1
    rw [hΔP P P' hP]
    exact hcoeff P
  · -- `U⁺` is smooth
    rintro _ ⟨s, rfl⟩
    have hs : S.ι s ∈ smoothLocus sX := hUsm s.2.1
    rw [smoothLocus_eq_smoothLocus] at hs ⊢
    exact (mem_smoothLocus_iff_of_comp_eq S.ι j sX sX' hjs s).2 hs
  · -- `Δ⁺|_{U⁺}` is snc
    have hrange : Set.range j.opensRange.ι = Set.range j := by
      rw [Scheme.Opens.range_ι, Scheme.Hom.coe_opensRange]
    refine DivisorWithCoeffs.IsSNC.comapDomain_of_range_subset sX' j.opensRange.ι j hrange.le _ ?_
    have hcomap : Finsupp.comapDomain (OpenWeilRestriction.primeDivisorMap j)
        (flipTransform f fp Δ) (OpenWeilRestriction.primeDivisorMap_injective j).injOn =
        Finsupp.comapDomain (OpenWeilRestriction.primeDivisorMap S.ι) Δ
          (OpenWeilRestriction.primeDivisorMap_injective S.ι).injOn := by
      refine Finsupp.ext fun E => ?_
      rw [Finsupp.comapDomain_apply, Finsupp.comapDomain_apply]
      refine hΔP _ _ ?_
      have e1 : MMP.Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap S.ι E) =
          S.ι E.genericPoint := OpenWeilRestriction.genericPoint_primeDivisorMap _ _
      have e2 : MMP.Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap j E) =
          j E.genericPoint := OpenWeilRestriction.genericPoint_primeDivisorMap _ _
      rw [e1, e2, hjapp]
    rw [hcomap, hjs]
    have hSU : Set.range S.ι ⊆ Set.range U.ι := by
      rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
      exact fun x hx => hx.1
    exact DivisorWithCoeffs.IsSNC.comapDomain_of_range_subset sX S.ι U.ι hSU Δ hsnc
  · -- the discrepancies of divisors with center outside `U⁺`
    intro D' a' hcen ha'
    set x' := D'.f D'.E.genericPoint
    have hx'U : x' ∉ j.opensRange := fun hx => by
      have hmem : x' ∈ (D'.center : Set X') := by
        rw [D'.center_eq_closure_genericPoint]; exact subset_closure rfl
      exact hcen hmem hx
    -- no point of `U` lies over `f⁺(x')`
    have hnotU : ∀ z : X, f z ∈ V → f z = fp x' → z ∉ U := fun z hzV hzx hzU =>
      hx'U (hU' x' z hzV hzx hzU)
    by_cases hE' : D'.IsExceptional
    · -- `D'` is exceptional: compare with a divisor `D` over `X` of the same valuation
      obtain ⟨D, hv⟩ := hflip.exists_divisorOver_valuation_comap_eq D'
      obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hpair.isPair hpair.2.1 D
      have hxx' : f (D.f D.E.genericPoint) = fp x' :=
        map_genericPoint_eq_of_valuation_comap_eq sY f fp D D' hv
      obtain ⟨hexc, hexcY⟩ := hflip.isExceptional_iff_and_isExceptional_comp D D' hv
      have hE := hexc.mp hE'
      have hEY := hexcY hE
      by_cases hfV : f (D.f D.E.genericPoint) ∈ V
      · -- the center on `Y` lies in `V`: the center on `X` misses `U`
        exact (hZ D a (center_subset_compl D (hnotU _ hfV hxx')) ha).trans_le
          (IsFlip.isDiscrepancy_le hpair.isPair hflip D D' hv hEY ha ha')
      · -- the center on `Y` lies in `f(Ex f) ∪ f⁺(Ex f⁺)`: strict comparison
        have hla : -1 ≤ a := by
          have h2 : ((-1 : ℝ) : EReal) ≤ ((a : ℝ) : EReal) := by
            simpa using hlc.2.trans (discrep_le hE ha)
          exact_mod_cast EReal.coe_le_coe_iff.mp h2
        exact hla.trans_lt (isDiscrepancy_lt_of_mem_image_exceptionalSet hpair.2.1 hflip hK' D D'
          hv hEY (hVc _ hfV) ha ha')
    · -- `D'` is a prime divisor `P'` of `X⁺`: `a' = -coeff_{P'} Δ⁺ = -coeff_P Δ`
      obtain ⟨P', hP'⟩ :=
        MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hX'v D' hE'
      have hx'P' : x' = P'.genericPoint :=
        MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hX'v hP'
      obtain ⟨b', hb'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hpair'.isPair hK'
        (DivisorOver.ofPrimeDivisor k hX'v P')
      have hab : a' = b' := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hpair' hP' ha' hb'
      have hb'eq := hb'.eq_neg_coeff_of_ofPrimeDivisor hX'v
      obtain ⟨P, hP⟩ := exists_primeDivisor_genericPoint_eq f fp V P' (hP'V P')
      obtain ⟨b, hb⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hpair.isPair hpair.2.1
        (DivisorOver.ofPrimeDivisor k hXv P)
      have hbeq := hb.eq_neg_coeff_of_ofPrimeDivisor hXv
      rw [hab, hb'eq, show (flipTransform f fp Δ).coeff P' = Δ.coeff P from
        hΔP P P' hP, ← hbeq]
      exact hZ _ b (center_subset_compl _ (hnotU P.genericPoint
        (hXV _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P).le)
        (hP.trans (congrArg fp hx'P').symm))) hb

end

/-- **Flips preserve dlt pairs** (Kollár–Mori, Corollary 3.44). Let `(X, Δ)` be a dlt pair with
canonical divisor `K` of dimension `n`, over an algebraically closed field of characteristic zero,
and let `φ : X ⤏ X⁺` be a `(K + Δ)`-flip (`MMP.Mori.IsFlipRationalMap`) of the flipping
contraction `f : X ⟶ Y`, given by `f⁺ : X⁺ ⟶ Y`. Then `(X⁺, φ_* Δ)` is dlt, with canonical
divisor `(f⁺)⁻¹_* f_* K`: this is `MMP.Mori.IsFlip.isDltPair`, as `φ_* Δ = (f⁺)⁻¹_* f_* Δ`. -/
@[mmp "thm_km3c_dlt_preserved_flip"]
public theorem IsFlipRationalMap.isDltPair {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {n : ℕ} {X X' Y : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    {K : Divisor X} {Δ : QDivisor X} {f : X ⟶ Y} {fp : X' ⟶ Y} {φ : RationalMap X X'}
    (h : IsDltPair sX n K Δ) (hφ : IsFlipRationalMap sX sY sX' K Δ f fp φ) :
    IsDltPair sX' n (flipTransform f fp K) (φ.transformDivisor Δ) := by
  rw [hφ.transformDivisor_eq_flipTransform]
  exact hφ.1.isDltPair h

end MMP.Mori

namespace MMP.Fourfold

open CategoryTheory AlgebraicGeometry
open MMP.Mori (Divisor RDivisor)

/-- Both contractions `f : X ⟶ Z` and `f⁺ : X⁺ ⟶ Z` of a step of an extremal real flip sequence
are isomorphisms over an open `V ⊆ Z` over which lie the points of codimension at most one of `X`
and of `X⁺`. -/
public theorem IsRealFlipStep.exists_opens_isIso {X Z X' : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X']
    [IsLocallyNoetherian X'] [IsNormal X'] {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    {sX' : X' ⟶ Spec (.of ℂ)} {K : Divisor X} {B : RDivisor X} {K' : Divisor X'}
    {B' : RDivisor X'} {f : X ⟶ Z} {fp : X' ⟶ Z}
    (h : IsRealFlipStep sX sZ sX' K B K' B' f fp) :
    ∃ V : Z.Opens, IsIso (f ∣_ V) ∧ IsIso (fp ∣_ V) ∧
      (∀ x : X, Order.coheight x ≤ 1 → f x ∈ V) ∧
      (∀ x : X', Order.coheight x ≤ 1 → fp x ∈ V) :=
  MMP.Mori.exists_opens_isIso_of_isSmall h.isSmall h.isSmall_flip

end MMP.Fourfold

end
