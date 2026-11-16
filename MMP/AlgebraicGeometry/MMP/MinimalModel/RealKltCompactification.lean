module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.RationalProgram
public import MMP.AlgebraicGeometry.MMP.Fourfold.FiniteGeneration
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import StacksFrontier.AlgebraicGeometry.Chow.NormalConeZeroSectionGysin
import StacksFrontier.AlgebraicGeometry.Spaces.SchemeModuleBridge.StrictTransformChart
import StacksFrontier.AlgebraicGeometry.Curves.ModelNormalization
import StacksFrontier.AlgebraicGeometry.Algebraization.CurveThroughPoints
import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveBundleCycleClassBridge
import StacksFrontier.AlgebraicGeometry.DeRham.BlowupEtaleChartTransfer
import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.QuasiProjectiveDisjointUnion
import StacksFrontier.AlgebraicGeometry.FlatBaseChange.GlobalGeneration
import MMP.AlgebraicGeometry.Singularities.RealKltPolytope
import MMP.AlgebraicGeometry.MMP.MinimalModel.KltCompactification

/-!
# Real klt compactifications in a rational family

Let `d ≥ 2` and assume the rational birational program property `Q(d)`
(`MMP.Fourfold.RationalBirationalProgramProperty`). Let `T` be a normal affine complex variety
and `f : S ⟶ T` a projective morphism from a normal `ℚ`-factorial complex variety `S` of
dimension `d`, and let `Θ` be an effective real divisor on `S` with `(S, Θ)` klt. Then there are
a normal projective compactification `ι : T ⟶ T̄` of `T` and a projective morphism `f̄ : S̄ ⟶ T̄`
from a projective `ℚ`-factorial variety `S̄` with `S = S̄ ×_{T̄} T`, such that the divisor `Θ̄`
obtained from `Θ` by taking the closure of each of its prime components (with the same
coefficient), and giving every other prime divisor of `S̄` coefficient zero, is klt.

The extension `Φ ↦ Φ̄` of real divisors on `S` is the push-forward along the injective map of
prime divisors `W ↦ W̄`; it is linear and defined over `ℚ`, and it identifies the smallest
rational affine hull of `Θ` with that of `Θ̄`.

## Main results

* `MMP.Fourfold.IsQFactorial.isRCartier`: on a `ℚ`-factorial variety every `ℝ`-divisor is
  `ℝ`-Cartier.
* `MMP.Fourfold.pos_of_isLogDiscrepancy_of_le`: on a `ℚ`-factorial complete variety, positivity
  of all log discrepancies is preserved when the boundary is lowered.
* `MMP.Fourfold.IsRealKltPair.of_le`: lowering a real klt boundary on a `ℚ`-factorial complete
  variety keeps it klt.
* `MMP.Fourfold.isQuasiProjectiveVariety_of_isProjectiveMorphism`: a variety projective over
  an affine variety is quasi-projective.
* `MMP.Fourfold.IsRealKltPair.exists_isKltPair_ge`: on a quasi-projective `ℚ`-factorial variety,
  an effective real klt boundary lies coefficientwise below a klt `ℚ`-boundary.
* `MMP.Fourfold.exists_realKltCompactification_of_rationalBirationalProgramProperty`: the real
  klt compactification described above, assuming `Q(d)`.

## Implementation notes

As for `MMP.Fourfold.exists_kltCompactification_of_rationalBirationalProgramProperty`, the
compactification is an open immersion `ι : T ⟶ T̄` over `ℂ` into a normal projective variety and
`S̄_T = S` is a pull-back square whose top arrow `j : S ⟶ S̄` is an open immersion. The closure of
a prime divisor `W` of `S` is `AlgebraicGeometry.OpenWeilRestriction.primeDivisorMap j W`, and the
extension of a real divisor `Φ` is `Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap j) Φ`.
The smallest rational affine hull is `MMP.Fourfold.IsInSmallestRationalAffineHull`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

/-! ### Smallest rational affine hulls under an injective map of primes -/

section Hull

variable {α β : Type*}

/-- A rational linear form evaluated on a real finitely supported function, summed over either
support. -/
private theorem sum_ratCast_mul_comm (c : α →₀ ℚ) (D : α →₀ ℝ) :
    (c.sum fun P cP => (cP : ℝ) * D P) = D.sum fun P t => (c P : ℝ) * t := by
  classical
  rw [Finsupp.sum_of_support_subset c Finset.subset_union_left _ (by simp),
    Finsupp.sum_of_support_subset D Finset.subset_union_right _ (by simp)]

/-- A rational linear form on `β`, evaluated on the push-forward of `D` along an injective map, is
the pulled-back form evaluated on `D`. -/
private theorem sum_ratCast_mul_mapDomain {g : α → β} (hg : Function.Injective g) (c : β →₀ ℚ)
    (D : α →₀ ℝ) :
    (c.sum fun P cP => (cP : ℝ) * Finsupp.mapDomain g D P) =
      (Finsupp.comapDomain g c hg.injOn).sum fun W cW => (cW : ℝ) * D W := by
  rw [sum_ratCast_mul_comm, sum_ratCast_mul_comm,
    Finsupp.sum_mapDomain_index (fun _ => mul_zero _) fun _ _ _ => mul_add _ _ _]
  rfl

/-- Push-forward of real divisors along an injective map of prime divisors identifies the smallest
rational affine hull of `Θ` with that of its push-forward. -/
private theorem isInSmallestRationalAffineHull_mapDomain_iff {X Y : Scheme.{0}}
    {g : MMP.Mori.PrimeDivisor X → MMP.Mori.PrimeDivisor Y} (hg : Function.Injective g)
    (Θ : RDivisor X) (Ψ : RDivisor Y) :
    IsInSmallestRationalAffineHull (Finsupp.mapDomain g Θ) Ψ ↔
      ∃ Φ : RDivisor X, IsInSmallestRationalAffineHull Θ Φ ∧ Ψ = Finsupp.mapDomain g Φ := by
  classical
  simp only [IsInSmallestRationalAffineHull, DivisorWithCoeffs.coeff_apply]
  rw [Finsupp.mapDomain_support_of_injective hg]
  constructor
  · rintro ⟨hsupp, heq⟩
    have hrange : (Ψ.support : Set _) ⊆ Set.range g := fun P hP => by
      obtain ⟨W, -, rfl⟩ := Finset.mem_image.mp (hsupp hP)
      exact ⟨W, rfl⟩
    have hΨ : Ψ = Finsupp.mapDomain g (Finsupp.comapDomain g Ψ hg.injOn) :=
      (Finsupp.mapDomain_comapDomain g hg Ψ hrange).symm
    refine ⟨Finsupp.comapDomain g Ψ hg.injOn, ⟨fun W hW => ?_, fun c q hc => ?_⟩, hΨ⟩
    · rw [Finsupp.mem_support_iff, Finsupp.comapDomain_apply] at hW
      obtain ⟨W', hW', hgW⟩ := Finset.mem_image.mp (hsupp (Finsupp.mem_support_iff.mpr hW))
      rwa [← hg hgW]
    · have h := heq (Finsupp.mapDomain g c) q
        (by rwa [sum_ratCast_mul_mapDomain hg, Finsupp.comapDomain_mapDomain g hg])
      rwa [hΨ, sum_ratCast_mul_mapDomain hg, Finsupp.comapDomain_mapDomain g hg] at h
  · rintro ⟨Φ, ⟨hsupp, heq⟩, rfl⟩
    refine ⟨?_, fun c q hc => ?_⟩
    · rw [Finsupp.mapDomain_support_of_injective hg]
      exact Finset.image_subset_image hsupp
    · rw [sum_ratCast_mul_mapDomain hg] at hc ⊢
      exact heq _ q hc

end Hull

/-! ### Coefficients of finite sums of prime divisors -/

/-- The coefficient of `∑_{i ∈ s} yᵢ · i` at `P`. -/
private theorem sum_single_apply {α R : Type*} [DecidableEq α] [AddCommMonoid R] (s : Finset α)
    (y : s → R) (P : α) :
    (∑ i : s, Finsupp.single (i : α) (y i)) P = if h : P ∈ s then y ⟨P, h⟩ else 0 := by
  rw [Finset.univ_eq_attach, ← Finsupp.indicator_eq_sum_attach_single (f := fun a h => y ⟨a, h⟩),
    Finsupp.indicator_apply]

/-! ### `ℝ`-Cartier divisors and klt boundaries on `ℚ`-factorial varieties -/

section RCartier

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] {sX : X ⟶ Spec (.of k)}

/-- On a `ℚ`-factorial variety every `ℝ`-divisor is `ℝ`-Cartier. -/
public theorem IsQFactorial.isRCartier (hX : IsQFactorial sX) (D : RDivisor X) :
    RDivisor.IsRCartier D := by
  classical
  choose m hm hmC using fun P : MMP.Mori.PrimeDivisor X => hX.2 (Finsupp.single P 1)
  let e := D.support.equivFin
  refine ⟨D.support.card, fun i => D (e.symm i) / m (e.symm i),
    fun i => ((m (e.symm i) : ℕ) : ℤ) •
      Finsupp.single (e.symm i : MMP.Mori.PrimeDivisor X) (1 : ℤ),
    fun i => hmC _, fun Γ => ?_⟩
  let F : MMP.Mori.PrimeDivisor X → ℝ := fun P =>
    D P / m P * ((((m P : ℕ) : ℤ) • Finsupp.single P (1 : ℤ)) Γ : ℤ)
  have hF : ∀ i, D (e.symm i) / m (e.symm i) *
      ((DivisorWithCoeffs.coeff (((m (e.symm i) : ℕ) : ℤ) •
        Finsupp.single (e.symm i : MMP.Mori.PrimeDivisor X) (1 : ℤ)) Γ : ℤ) : ℝ) =
        F (e.symm i) := fun i => rfl
  simp_rw [hF]
  rw [Equiv.sum_comp e.symm (fun i : D.support => F i), Finset.sum_coe_sort D.support F,
    DivisorWithCoeffs.coeff_apply]
  by_cases hΓ : Γ ∈ D.support
  · rw [Finset.sum_eq_single Γ (fun P _ hP => by simp [F, Finsupp.single_apply, hP])
      (fun h => absurd hΓ h)]
    have := (hm Γ).ne'
    simp only [Finsupp.smul_single, Int.zsmul_eq_mul, mul_one, Finsupp.single_eq_same,
      Int.cast_natCast, F]
    field_simp
  · rw [Finsupp.notMem_support_iff.mp hΓ]
    refine (Finset.sum_eq_zero fun P hP => ?_).symm
    have hne : P ≠ Γ := fun e => hΓ (e ▸ hP)
    simp [F, Finsupp.single_apply, hne]

/-- Lowering a boundary on a `ℚ`-factorial complete variety preserves positivity of log
discrepancies: if `B ≤ Δ` coefficientwise and every log discrepancy of `(X, Δ)` is positive, so is
every log discrepancy of `(X, B)`. -/
public theorem pos_of_isLogDiscrepancy_of_le [CompactSpace X] (hX : IsQFactorial sX)
    {Δ B : RDivisor X} (hle : ∀ P, B.coeff P ≤ Δ.coeff P)
    (hΔ : ∀ (n : ℕ) (E : DivisorOver k sX) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sX n Δ E a → 0 < a)
    (n : ℕ) (E : DivisorOver k sX) (a : ℝ) (ha : MMP.Intersection.IsLogDiscrepancy sX n B E a) :
    0 < a := by
  classical
  obtain ⟨hXn, hprop, ω, hω, hKω, m, r, L, L', hL, hsum, hpb, rfl⟩ := ha
  obtain ⟨m₂, s, M, hM, hMsum⟩ := hX.isRCartier (Δ - B)
  haveI := E.isIntegral
  haveI := E.isLocallyNoetherian
  haveI := E.isNormal
  haveI := E.isDominant
  haveI : CompactSpace E.Y := QuasiCompact.compactSpace_of_compactSpace E.f
  choose M' hM' using fun j => (hM j).exists_isPullback
    (map_componentGenericPoint_notMem_supp_of_isDominant E.f (M j))
  have hMpb : ∀ j, ∃ h, (M j).IsPullback E.f h (M' j) := fun j => ⟨_, hM' j⟩
  have hpos := hΔ n E _ ⟨hXn, hprop, ω, hω, hKω, m + m₂, Fin.append r s, Fin.append L M,
    Fin.append L' M', Fin.addCases (fun i => by simpa using hL i) (fun j => by simpa using hM j),
    fun Γ => ?_, Fin.addCases (fun i => by simpa using hpb i)
      (fun j => by simpa using hMpb j), rfl⟩
  · rw [Fin.sum_univ_add] at hpos
    simp only [Fin.append_left, Fin.append_right] at hpos
    have heff := (isEffective_of_isRCartierPullback E.f ⟨m₂, s, M, hM, hMsum⟩
      fun P => sub_nonneg.mpr (hle P)).2
      (∑ j, s j • Divisor.toRDivisor (M' j))
      ⟨m₂, s, M, M', hM, by ext P; rw [hMsum P, coeff_sum_smul_toRDivisor], hMpb, rfl⟩
    have hE := heff E.E
    rw [show (∑ j, s j • Divisor.toRDivisor (M' j)) E.E =
      (∑ j, s j • Divisor.toRDivisor (M' j)).coeff E.E from rfl,
      coeff_sum_smul_toRDivisor] at hE
    simp only [Finsupp.coe_zero, Pi.zero_apply] at hE
    linarith
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    have h1 := hsum Γ
    have h2 := hMsum Γ
    simp only [DivisorWithCoeffs.coeff_apply, Finsupp.coe_sub, Pi.sub_apply] at h1 h2 ⊢
    linarith

/-- **Lowering a real klt boundary.** On a `ℚ`-factorial complete variety, a real divisor `B`
coefficientwise below a real klt boundary `Δ` is a real klt boundary. -/
public theorem IsRealKltPair.of_le [CompactSpace X] (hX : IsQFactorial sX) {Δ B : RDivisor X}
    (hle : ∀ P, B.coeff P ≤ Δ.coeff P) (hΔ : IsRealKltPair sX Δ) : IsRealKltPair sX B := by
  obtain ⟨n, K, hK, -⟩ := hΔ.2.2.1
  exact ⟨hX.1, fun P => (hle P).trans_lt (hΔ.2.1 P), ⟨n, K, hK, hX.isRCartier _⟩,
    pos_of_isLogDiscrepancy_of_le hX hle hΔ.2.2.2⟩

/-- **Effective subboundaries of klt boundaries.** On a `ℚ`-factorial complete variety, a real
divisor `B` with coefficients less than one, coefficientwise below a klt `ℚ`-boundary `C`, is a
real klt boundary. -/
private theorem isRealKltPair_of_le_of_isKltPair [CompactSpace X] (hX : IsQFactorial sX)
    {C : QDivisor X} (hC : IsKltPair sX C) {B : RDivisor X} (hB : ∀ P, B.coeff P < 1)
    (hle : ∀ P, B.coeff P ≤ C.coeff P) : IsRealKltPair sX B := by
  obtain ⟨-, n, K, hK, -⟩ := hC.1.isPair
  exact ⟨hX.1, hB, ⟨n, K, hK, hX.isRCartier _⟩,
    pos_of_isLogDiscrepancy_of_le (Δ := QDivisor.toRDivisor C) hX hle hC.2⟩

end RCartier

/-! ### Quasi-projectivity over an affine base -/

/-- A variety projective over an affine variety is quasi-projective. -/
public theorem isQuasiProjectiveVariety_of_isProjectiveMorphism {k : Type} [Field k]
    {S T : Scheme.{0}} [IsAffine T] {sT : T ⟶ Spec (.of k)} (hT : MMP.Mori.IsVariety k sT)
    {sS : S ⟶ Spec (.of k)} (hS : MMP.Mori.IsVariety k sS) {f : S ⟶ T} (hfs : f ≫ sT = sS)
    (hf : IsProjectiveMorphism f) : AlgebraicGeometry.IsQuasiProjectiveVariety k sS := by
  refine (isQuasiProjectiveVariety_iff k sS).mpr ⟨hS, ?_⟩
  subst hfs
  exact isQuasiProjective_comp_of_exists_isAmple f sT ⟨_, inferInstance,
    Stacks.Ample.isAmple_unitModule_of_isAffine _⟩
    (Stacks.HProjective.isQuasiProjective_of_isHQuasiProjective f hf.isHQuasiProjective)
    (isQuasiProjective_of_isQuasiAffineHom sT hT.toLocallyOfFiniteType)

/-! ### A rational klt boundary above a real one -/

/-- **Rational klt boundaries above a real one.** On a quasi-projective `ℚ`-factorial variety, an
effective real klt boundary `Θ` lies coefficientwise below a klt `ℚ`-boundary. -/
public theorem IsRealKltPair.exists_isKltPair_ge {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] (sS : S ⟶ Spec (.of k))
    (hSq : AlgebraicGeometry.IsQuasiProjectiveVariety k sS) (hSQ : IsQFactorial sS)
    {Θ : RDivisor S} (hΘ : ∀ P, 0 ≤ Θ.coeff P) (hΘk : IsRealKltPair sS Θ) :
    ∃ C : QDivisor S, IsKltPair sS C ∧ ∀ P, Θ.coeff P ≤ C.coeff P := by
  classical
  let p : Θ.support → MMP.Mori.PrimeDivisor S := Subtype.val
  let x : Θ.support → ℝ := fun i => Θ i
  have hΘsum : ∑ i, Finsupp.single (p i) (x i) = Θ := by
    rw [Finset.sum_coe_sort Θ.support fun P => Finsupp.single P (Θ P)]
    exact Θ.sum_single
  have hev := (eventually_isRealKltPair_and_isRealTerminalPair sS hSq hSQ p x).1
    (by rwa [hΘsum])
  obtain ⟨U, hUo, hxU, hU⟩ := mem_nhdsWithin.mp hev
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUo x hxU
  choose q hq using fun i => exists_rat_btwn (lt_add_of_pos_right (x i) hε)
  have hy : IsRealKltPair sS (∑ i, Finsupp.single (p i) ((q i : ℚ) : ℝ)) := by
    refine hU ⟨hball ((dist_pi_lt_iff hε).mpr fun i => ?_), fun i => (hΘ _).trans (hq i).1.le⟩
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [(hq i).1, (hq i).2]
  let C : QDivisor S := ∑ i, Finsupp.single (p i) (q i)
  have hCR : QDivisor.toRDivisor C = ∑ i, Finsupp.single (p i) ((q i : ℚ) : ℝ) := by
    refine Finsupp.ext fun P => ?_
    change ((C P : ℚ) : ℝ) = _
    rw [sum_single_apply, sum_single_apply]
    split_ifs <;> simp
  have hle : ∀ W, Θ.coeff W ≤ C.coeff W := fun W => by
    rw [DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply, sum_single_apply]
    split_ifs with h
    · exact (hq ⟨W, h⟩).1.le
    · simp [Finsupp.notMem_support_iff.mp h]
  obtain ⟨n, K, hK, -⟩ := hΘk.2.2.1
  refine ⟨C, ⟨⟨inferInstance, inferInstance, ⟨hSQ.1, n, K, hK,
    isQCartier_of_isQFactorial sS hSQ _⟩, fun W => ?_⟩, fun n E a h => ?_⟩, hle⟩
  · exact_mod_cast (hΘ W).trans (hle W)
  · exact hy.2.2.2 n E a (hCR ▸ h)

/-- **Real klt compactification in a rational family.** Let `d ≥ 2` with `Q(d)`, let `T` be a
normal affine complex variety, `f : S ⟶ T` a projective morphism over `ℂ` from a `ℚ`-factorial
(normal) complex variety `S` of dimension `d`, and `Θ` an effective real divisor on `S` with
`(S, Θ)` klt (`MMP.Fourfold.IsRealKltPair`). Then there are an open immersion `ι : T ⟶ T̄` over
`ℂ` into a normal projective variety `T̄`, a projective morphism `f̄ : S̄ ⟶ T̄` over `ℂ` from a
`ℚ`-factorial projective variety `S̄` and an open immersion `j : S ⟶ S̄` making `S` the pull-back
`S̄ ×_{T̄} T`, such that

* the divisor `Θ̄ = Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap j) Θ`, whose
  coefficient along the closure of each prime `W` of `S` is that of `Θ` and which vanishes along
  every other prime divisor of `S̄`, makes `(S̄, Θ̄)` klt;
* a real divisor `Ψ` on `S̄` lies in the smallest rational affine hull of `Θ̄` if and only if it
  is the extension `Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap j) Φ` of a real
  divisor `Φ` in the smallest rational affine hull of `Θ`. -/
@[mmp "lem_fourfold_real_family_compactification_from_rational_program"]
public theorem exists_realKltCompactification_of_rationalBirationalProgramProperty
    {d : ℕ} (hd : 2 ≤ d) (hQ : RationalBirationalProgramProperty d)
    {T : Scheme.{0}} (sT : T ⟶ Spec (.of ℂ)) (hT : IsNormalVariety ℂ sT) [IsAffine T]
    {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    (sS : S ⟶ Spec (.of ℂ)) (hSQ : IsQFactorial sS) (hSd : topologicalKrullDim S = d)
    (f : S ⟶ T) (hfs : f ≫ sT = sS) (hf : IsProjectiveMorphism f)
    (Θ : RDivisor S) (hΘ : ∀ P, 0 ≤ Θ.coeff P) (hΘk : IsRealKltPair sS Θ) :
    ∃ (Tbar : Scheme.{0}) (sTbar : Tbar ⟶ Spec (.of ℂ)) (ι : T ⟶ Tbar),
      MMP.Mori.IsProjectiveVariety ℂ sTbar ∧ IsNormalVariety ℂ sTbar ∧
      IsOpenImmersion ι ∧ ι ≫ sTbar = sT ∧
      ∃ (Sbar : Scheme.{0}) (_ : IsIntegral Sbar) (_ : IsLocallyNoetherian Sbar)
        (_ : IsNormal Sbar) (sSbar : Sbar ⟶ Spec (.of ℂ)) (fbar : Sbar ⟶ Tbar)
        (j : S ⟶ Sbar) (_ : IsOpenImmersion j),
        MMP.Mori.IsProjectiveVariety ℂ sSbar ∧ IsQFactorial sSbar ∧
        IsProjectiveMorphism fbar ∧ fbar ≫ sTbar = sSbar ∧
        IsPullback j f fbar ι ∧
        IsRealKltPair sSbar (Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap j) Θ) ∧
        ∀ Ψ : RDivisor Sbar,
          IsInSmallestRationalAffineHull
              (Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap j) Θ) Ψ ↔
            ∃ Φ : RDivisor S, IsInSmallestRationalAffineHull Θ Φ ∧
              Ψ = Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap j) Φ := by
  obtain ⟨C, hCk, hΘC⟩ := IsRealKltPair.exists_isKltPair_ge sS
    (isQuasiProjectiveVariety_of_isProjectiveMorphism hT.1 hSQ.1.1 hfs hf) hSQ hΘ hΘk
  obtain ⟨Tbar, sTbar, ι, hTp, hTn, hι, hιs, Sbar, h1, h2, h3, sSbar, fbar, Cbar, j, hj, hSp,
    hSbarQ, hfbar, hfbs, hCbar, hpb, hcoef⟩ :=
    exists_kltCompactification_of_rationalBirationalProgramProperty hd hQ sT hT sS hSQ hSd f hfs
      hf C hCk
  have hinj := OpenWeilRestriction.primeDivisorMap_injective j
  refine ⟨Tbar, sTbar, ι, hTp, hTn, hι, hιs, Sbar, h1, h2, h3, sSbar, fbar, j, hj, hSp, hSbarQ,
    hfbar, hfbs, hpb, ?_, isInSmallestRationalAffineHull_mapDomain_iff hinj Θ⟩
  haveI : CompactSpace Sbar := by
    haveI := hSp.toIsVariety
    exact QuasiCompact.compactSpace_of_compactSpace sSbar
  refine isRealKltPair_of_le_of_isKltPair hSbarQ hCbar (fun P => ?_) (fun P => ?_) <;>
    rw [DivisorWithCoeffs.coeff_apply] <;>
    by_cases hP : P ∈ Set.range (OpenWeilRestriction.primeDivisorMap j)
  · obtain ⟨W, rfl⟩ := hP
    rw [Finsupp.mapDomain_apply_of_injective hinj]
    exact hΘk.2.1 W
  · rw [Finsupp.mapDomain_notin_range _ _ hP]
    exact one_pos
  · obtain ⟨W, rfl⟩ := hP
    rw [Finsupp.mapDomain_apply_of_injective hinj, hcoef W]
    exact_mod_cast hΘC W
  · rw [Finsupp.mapDomain_notin_range _ _ hP]
    exact_mod_cast hCbar.1.nonneg P

end MMP.Fourfold
