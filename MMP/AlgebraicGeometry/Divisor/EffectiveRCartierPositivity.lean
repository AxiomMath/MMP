module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Contraction.Defs
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs
public import MMP.AlgebraicGeometry.Intersection.RCartierCurveDegree
public import MMP.AlgebraicGeometry.Divisor.Basic
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Resolution.Surface.SemilocalRing
import MMP.AlgebraicGeometry.Resolution.DisjoiningSequence
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.MMP.Contraction.SmallContractionBasics
import StacksFrontier.AlgebraicGeometry.Curves.ModelNormalization
import StacksFrontier.AlgebraicGeometry.Algebraization.CurveThroughPoints
import MMP.AlgebraicGeometry.Variety.Basic
public import MMP.AlgebraicGeometry.Chow.FieldSituation
import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.DvrCycleClasses
import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyLocallyClosed
import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.ClosedImmersion

/-!
# Effective divisors, negativity over a point, and curves through points

This file collects the sign properties of effective `ℝ`-Cartier divisors used in the negativity
lemma, the negativity lemma over a point, and the existence of curves through prescribed points.

Let `X` be a normal variety over a field `k`.

* If `G` is an effective `ℝ`-Cartier divisor and `F` a divisor of `k(X)` with nonempty center on
  `X`, the multiplicity `mult_F(G)` is nonnegative. For integral coefficients this is the
  effectivity of pull-backs of effective Cartier divisors; rational coefficients reduce to it by
  clearing denominators, and real ones by density of rational points among the coefficient
  vectors satisfying the same rational relations.
* Consequently discrepancies decrease as the boundary increases: if `D' ≤ D` then
  `a(F, D) ≤ a(F, D')`, since `a(F, D) = a(F, D') - mult_F(D - D')`.
* An effective `ℝ`-Cartier divisor `D` has `D · C ≥ 0` on every proper curve `C ⊄ Supp D`, and
  `D · C > 0` if moreover `C` meets `Supp D`. The Cartier case is the degree of a pulled-back
  effective divisor on the normalization of `C`; the real case follows by approximating the
  coefficient vector by rational vectors satisfying every integral relation it satisfies.
* **Negativity lemma over a point.** If `f : Y ⟶ X` is a proper birational morphism of normal
  varieties and `B` an effective `ℝ`-Cartier divisor with `-B` `f`-nef, every fibre `f⁻¹(x)` is
  contained in `Supp B` or disjoint from it. Over a closed point the fibre is connected and
  proper, so otherwise it contains a contracted proper curve meeting `Supp B` without lying in
  it, on which `B` is positive.
* Two closed points of a positive-dimensional variety lie on a closed integral curve, proper when
  the variety is; over a field a nonempty finite set of closed points of a projective variety of
  positive dimension lies on an irreducible closed subset of dimension one.

## Main results

* `MMP.Flips.IsMultiplicityAlong.nonneg`: `mult_F(G) ≥ 0` for effective `G`.
* `MMP.Flips.IsDiscrepancy.le_of_le`: `D' ≤ D` implies `a(F, D) ≤ a(F, D')`.
* `MMP.Flips.IsRIntersectionNumber.nonneg_of_isEffective`: `D · C ≥ 0` for `C ⊄ Supp D`.
* `MMP.Flips.IsRIntersectionNumber.pos_of_isEffective`: `D · C > 0` if moreover `C` meets
  `Supp D`.
* `MMP.Flips.preimage_singleton_subset_supp_or_disjoint_of_isRelativelyNef_neg`: the negativity
  lemma over a point.
* `MMP.exists_isClosedImmersion_isCurve_and_isProper_of_isClosed_singleton`: a curve through two
  closed points.
* `MMP.exists_isClosed_isIrreducible_topologicalKrullDim_eq_one_superset`: a curve through
  finitely many closed points of a projective variety.

## Implementation notes

Multiplicities, discrepancies and intersection numbers are relations (`IsMultiplicityAlong`,
`IsDiscrepancy`, `IsRIntersectionNumber`) between a presentation `D = ∑ r_j L_j` by Cartier
divisors and a value, so each inequality is stated for every value computed from every
presentation. The base is an arbitrary field rather than `ℂ`. A curve not contained in the closed
set `Supp D` is one whose generic point is not in it. The negativity lemma produces its curve
inside the scheme-theoretic fibre rather than through an irreducible component of the fibre and
two closed points on it. The curve through finitely many points is recorded by its underlying
irreducible closed subset (its reduced induced structure is the integral curve); it is found by
descending through irreducible closed subsets using the affine form of Bertini's theorem in one
affine chart containing the points, rather than by a general hypersurface section.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.17.3, 2.19,
  2.24.4
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.39(2)
* [Stacks Project, Tag 01ZY](https://stacks.math.columbia.edu/tag/01ZY)
* [Stacks Project, Tag 0G4F](https://stacks.math.columbia.edu/tag/0G4F)
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry MMP.Mori
open scoped WithZero

namespace MMP.Flips

/-! ### Multiplicities and discrepancies -/

/-- Clearing denominators of finitely many rationals. -/
private lemma exists_pos_nat_mul_eq_intCast {m : ℕ} (q : Fin m → ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∃ n : Fin m → ℤ, ∀ j, (N : ℚ) * q j = n j := by
  refine ⟨∏ j, (q j).den, Finset.prod_pos fun j _ => (q j).den_pos, ?_⟩
  have h : ∀ j, ∃ K : ℕ, ∏ i, (q i).den = (q j).den * K := fun j =>
    Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  choose K hK using h
  refine ⟨fun j => K j * (q j).num, fun j => ?_⟩
  rw [hK j]
  push_cast
  rw [mul_comm ((q j).den : ℚ), mul_assoc, Rat.den_mul_eq_num]

/-- Clearing denominators: the inequality for integral coefficient vectors gives it for rational
ones. -/
private theorem rat_nonneg_of_int {m : ℕ} {κ : Type*} (a : κ → Fin m → ℤ) (c : Fin m → ℤ)
    (hZ : ∀ n : Fin m → ℤ, (∀ P, 0 ≤ ∑ j, n j * a P j) → 0 ≤ ∑ j, n j * c j)
    (q : Fin m → ℚ) (hq : ∀ P, 0 ≤ ∑ j, q j * a P j) : 0 ≤ ∑ j, q j * c j := by
  obtain ⟨N, hN, n, hn⟩ := exists_pos_nat_mul_eq_intCast q
  have hNpos : (0 : ℚ) < N := by exact_mod_cast hN
  have hsign : ∀ v : Fin m → ℤ, 0 ≤ ∑ j, n j * v j ↔ 0 ≤ ∑ j, q j * v j := fun v => by
    have h : ((∑ j, n j * v j : ℤ) : ℚ) = N * ∑ j, q j * v j := by
      push_cast
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [← hn]; ring
    rw [← mul_nonneg_iff_of_pos_left hNpos, ← h]
    exact_mod_cast Iff.rfl
  exact (hsign c).1 (hZ n fun P => (hsign (a P)).2 (hq P))

/-- Rational coordinates of finitely many reals: `r` is a rational combination of a family `β` of
reals that is linearly independent over `ℚ`. -/
private theorem exists_rat_coords {m : ℕ} (r : Fin m → ℝ) :
    ∃ (d : ℕ) (q : Fin m → Fin d → ℚ) (β : Fin d → ℝ), (∀ j, r j = ∑ t, (q j t : ℝ) * β t) ∧
      ∀ c : Fin d → ℚ, ∑ t, (c t : ℝ) * β t = 0 → ∀ t, c t = 0 := by
  set S : Submodule ℚ ℝ := Submodule.span ℚ (Set.range r)
  have hmem : ∀ j, r j ∈ S := fun j => Submodule.subset_span ⟨j, rfl⟩
  haveI : Module.Finite ℚ S := FiniteDimensional.span_of_finite ℚ (Set.finite_range r)
  let b := Module.finBasis ℚ S
  refine ⟨_, fun j t => b.repr ⟨r j, hmem j⟩ t, fun t => (b t : ℝ), fun j => ?_, fun c hc => ?_⟩
  · have := congrArg (fun x : S => (x : ℝ)) (b.sum_repr ⟨r j, hmem j⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Rat.smul_def] at this
    exact this.symm
  · refine Fintype.linearIndependent_iff.mp b.linearIndependent c (Subtype.ext ?_)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Rat.smul_def, Submodule.coe_zero]
    exact hc

/-- Density of rational points: the inequality for rational coefficient vectors gives it for real
ones, provided only finitely many constraints occur. -/
private theorem real_nonneg_of_rat {m : ℕ} {κ : Type*} [Finite κ] (a : κ → Fin m → ℚ)
    (c : Fin m → ℚ)
    (hQ : ∀ q : Fin m → ℚ, (∀ P, 0 ≤ ∑ j, q j * a P j) → 0 ≤ ∑ j, q j * c j)
    (r : Fin m → ℝ) (hr : ∀ P, 0 ≤ ∑ j, r j * a P j) : 0 ≤ ∑ j, r j * c j := by
  obtain ⟨d, q, β, hrq, hind⟩ := exists_rat_coords r
  set C : κ → Fin d → ℚ := fun P t => ∑ j, q j t * a P j
  set s : κ → (Fin d → ℝ) → ℝ := fun P γ => ∑ t, γ t * C P t
  set ρ : (Fin d → ℝ) → Fin m → ℝ := fun γ j => ∑ t, (q j t : ℝ) * γ t
  have hs : ∀ P γ, ∑ j, ρ γ j * a P j = s P γ := by
    intro P γ
    simp only [ρ, s, C, Rat.cast_sum, Rat.cast_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun j _ => by ring
  have hρβ : ρ β = r := funext fun j => (hrq j).symm
  have hsβ : ∀ P, 0 ≤ s P β := fun P => by
    rw [← hs, hρβ]
    exact hr P
  have hzero : ∀ P, s P β = 0 → ∀ t, C P t = 0 := fun P hP =>
    hind (C P) (by
      rw [← hP]
      exact Finset.sum_congr rfl fun t _ => mul_comm _ _)
  set U : Set (Fin d → ℝ) := ⋂ P, {γ | 0 < s P β → 0 < s P γ}
  have hU : IsOpen U := by
    refine isOpen_iInter_of_finite fun P => ?_
    by_cases h : 0 < s P β
    · simpa [h] using isOpen_lt continuous_const (by fun_prop : Continuous (s P))
    · simp [h]
  set Φ : (Fin d → ℝ) → ℝ := fun γ => ∑ j, ρ γ j * c j
  have hΦ : Continuous Φ := by fun_prop
  set R : Set (Fin d → ℝ) := Set.range fun v : Fin d → ℚ => fun t => (v t : ℝ)
  have hR : Dense R := DenseRange.piMap fun _ => Rat.denseRange_cast
  have hsub : U ∩ R ⊆ {γ | 0 ≤ Φ γ} := by
    rintro γ ⟨hγU, v, rfl⟩
    set q' : Fin m → ℚ := fun j => ∑ t, q j t * v t
    have hcast : ∀ j, (q' j : ℝ) = ρ (fun t => (v t : ℝ)) j := fun j => by
      simp [q', ρ]
    have h1 := hQ q' fun P => by
      have : (0 : ℝ) ≤ ∑ j, (q' j : ℝ) * a P j := by
        simp_rw [hcast]
        rw [hs]
        by_cases hP : 0 < s P β
        · exact (Set.mem_iInter.mp hγU P hP).le
        · have hP0 : s P β = 0 := le_antisymm (not_lt.mp hP) (hsβ P)
          simp [s, hzero P hP0]
      exact_mod_cast this
    have : (0 : ℝ) ≤ ∑ j, (q' j : ℝ) * c j := by exact_mod_cast h1
    simpa [Φ, hcast] using this
  simpa [Φ, hρβ] using closure_minimal hsub (isClosed_le continuous_const hΦ)
    (hR.open_subset_closure_inter hU (Set.mem_iInter.mpr fun P h => h))

section Pullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y]
  [IsNormal Y] {f : Y ⟶ X}

private theorem notMem_supp_zsmul {D : Divisor X} {x : X} (hx : x ∉ D.supp) (n : ℤ) :
    x ∉ (n • D).supp := by
  rw [DivisorWithCoeffs.mem_supp_iff] at hx ⊢
  rintro ⟨E, hE, hxE⟩
  refine hx ⟨E, fun h => hE ?_, hxE⟩
  rw [DivisorWithCoeffs.coeff_smul, h, smul_zero]

/-- Integral combinations of Cartier divisors with pull-backs are Cartier, with the
corresponding combination of the pull-backs as pull-back. -/
private theorem isPullback_sum {m : ℕ} {L : Fin m → Divisor X} (hLc : ∀ j, (L j).IsCartier)
    {L' : Fin m → Divisor Y}
    (hL' : ∀ j, ∃ hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ (L j).supp,
      (L j).IsPullback f hB (L' j)) (n : Fin m → ℤ) (s : Finset (Fin m)) :
    (∑ j ∈ s, n j • L j).IsCartier ∧
      ∃ hB : ∀ Z : irreducibleComponents Y,
          f (componentGenericPoint Y Z) ∉ (∑ j ∈ s, n j • L j).supp,
        (∑ j ∈ s, n j • L j).IsPullback f hB (∑ j ∈ s, n j • L' j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨Divisor.isCartier_zero, fun Z h => by
      rw [DivisorWithCoeffs.supp_zero] at h
      simpa using (show _ ∈ ((⊥ : TopologicalSpace.Closeds X) : Set X) from h),
      Divisor.isPullback_zero _⟩
  | insert j s hj ih =>
    obtain ⟨hc, hB, hp⟩ := ih
    obtain ⟨hBj, hpj⟩ := hL' j
    simp only [Finset.sum_insert hj]
    have hBn := fun Z => notMem_supp_zsmul (hBj Z) (n j)
    exact ⟨((hLc j).zsmul (n j)).add hc,
      fun Z h => (DivisorWithCoeffs.supp_add_le _ _ h).elim (hBn Z) (hB Z),
      ((hpj.zsmul (hLc j) (n j) hBn)).add ((hLc j).zsmul (n j)) hc _ hp⟩

/-- The integral case: if `∑ n_j L_j` is effective, so is its pull-back, and its coefficient
along `E` is `∑ n_j coeff_E(L'_j) ≥ 0`. -/
private theorem int_nonneg {m : ℕ} {L : Fin m → Divisor X} (hLc : ∀ j, (L j).IsCartier)
    {L' : Fin m → Divisor Y}
    (hL' : ∀ j, ∃ hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ (L j).supp,
      (L j).IsPullback f hB (L' j)) (E : MMP.Mori.PrimeDivisor Y) (n : Fin m → ℤ)
    (hn : ∀ P : MMP.Mori.PrimeDivisor X, 0 ≤ ∑ j, n j * (L j).coeff P) :
    0 ≤ ∑ j, n j * (L' j).coeff E := by
  obtain ⟨hc, hB, hp⟩ := isPullback_sum hLc hL' n Finset.univ
  have key := MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn (V := ⊤) hc
    (fun P _ => by
      simpa [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply] using hn P) hp E
    (by simpa using E.support_nonempty)
  simpa [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply] using key

end Pullback

/-- **Multiplicities of effective divisors are nonnegative.** Let `X` be a normal variety over
`k`, `G ≥ 0` an effective `ℝ`-Cartier divisor on `X` with a presentation `G = ∑ r_j L_j`, and `F`
a divisor of `k(X)` with nonempty center on `X`, realized by `E`. If `μ = mult_F(G)`, then
`0 ≤ μ`. -/
@[mmp "lem_fa2_multiplicity_effective_nonneg"]
public theorem IsMultiplicityAlong.nonneg {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] {G : RDivisor X} {m : ℕ} {r : Fin m → ℝ}
    {L : Fin m → Divisor X} {F : Valuation X.functionField ℤᵐ⁰} {E : ProperDivisorOver k sX}
    {μ : ℝ} (h : IsMultiplicityAlong sX G r L F E μ) (hG : 0 ≤ G) : 0 ≤ μ := by
  obtain ⟨-, -, -, hLc, hGeq, hrest⟩ := h
  haveI := E.isLocallyNoetherian
  haveI := E.isNormal
  obtain ⟨L', hL', hμ⟩ := hrest
  classical
  set T : Finset (MMP.Mori.PrimeDivisor X) := Finset.univ.biUnion fun j => (L j).support
  have hT : ∀ P ∉ T, ∀ j, (L j).coeff P = 0 := fun P hP j => by
    by_contra h
    exact hP (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Finsupp.mem_support_iff.mpr h⟩)
  have hGc : ∀ P, G.coeff P = ∑ j, r j * ((L j).coeff P : ℝ) := fun P => by
    rw [hGeq]
    simp only [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply, Finsupp.smul_apply,
      smul_eq_mul]
    rfl
  have hZ : ∀ n : Fin m → ℤ, (∀ P : T, 0 ≤ ∑ j, n j * (L j).coeff P.1) →
      0 ≤ ∑ j, n j * (L' j).coeff E.E := fun n hn =>
    int_nonneg hLc hL' E.E n fun P => by
      by_cases hP : P ∈ T
      · exact hn ⟨P, hP⟩
      · simp [hT P hP]
  have hQ := rat_nonneg_of_int (fun (P : T) j => (L j).coeff P.1) (fun j => (L' j).coeff E.E) hZ
  have hR := real_nonneg_of_rat (fun (P : T) j => ((L j).coeff P.1 : ℚ))
    (fun j => ((L' j).coeff E.E : ℚ)) hQ r fun P => by
      have : 0 ≤ G.coeff P.1 := hG P.1
      rw [hGc] at this
      simpa using this
  rw [hμ]
  simpa using hR

/-- Every presentation `G = ∑ r_j L_j` by Cartier divisors and every divisor `E` over `X`
realizing `F` compute some multiplicity `mult_F(G)`: the pull-backs of the `L_j` to `E.Y` exist. -/
private theorem exists_isMultiplicityAlong {k : Type u} [Field k] {X : Scheme}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] {G : RDivisor X} {m : ℕ} {r : Fin m → ℝ}
    {L : Fin m → Divisor X} {F : Valuation X.functionField ℤᵐ⁰} {E : ProperDivisorOver k sX}
    (hX : IsNormalVariety k sX) (hF : HasNonemptyCenter k sX F) (hE : E.valuation = F)
    (hc : ∀ j, (L j).IsCartier) (hG : G = ∑ j, r j • Divisor.toRDivisor (L j)) :
    ∃ μ, IsMultiplicityAlong sX G r L F E μ := by
  have := E.isIntegral
  have := E.isLocallyNoetherian
  have := E.isNormal
  have := E.isDominant
  have : IsProper E.f := E.isProper
  have : CompactSpace E.Y := QuasiCompact.compactSpace_of_compactSpace E.f
  choose M hM using fun j => MMP.Threefold.Bridges.exists_isPullback_of_isDominant E.f (hc j)
  exact ⟨_, hX, hF, hE, hc, hG, M, fun j => ⟨_, hM j⟩, rfl⟩

/-- **Discrepancies decrease as the boundary increases.** Let `X` be a normal variety of
dimension `n` over a perfect field `k`, `K_X` a canonical divisor and `D' ≤ D` two `ℝ`-divisors on
`X` with `K_X + D` and `K_X + D'` `ℝ`-Cartier. If `a = a(F, D)` and `a' = a(F, D')` are the
discrepancies of a divisor `F` of `k(X)` with nonempty center on `X`, then `a ≤ a'`. -/
@[mmp "lem_fa2_discrepancy_monotone"]
public theorem IsDiscrepancy.le_of_le {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] {n : ℕ} {K : Divisor X} {D D' : RDivisor X}
    {F : Valuation X.functionField ℤᵐ⁰} {a a' : ℝ} (h : IsDiscrepancy sX n K D F a)
    (h' : IsDiscrepancy sX n K D' F a') (hD : D' ≤ D) : a ≤ a' := by
  obtain ⟨-, -, hF, E₁, ω₁, m₁, r₁, L₁, -, hω₁, hX, -, -, hL₁c, hsum₁, -⟩ := id h
  obtain ⟨-, -, -, E₂, ω₂, m₂, r₂, L₂, hE₂, hω₂, -, -, -, hL₂c, hsum₂, -⟩ := id h'
  obtain ⟨μ, hμ⟩ := exists_isMultiplicityAlong (G := D - D') (r := Fin.append r₁ (-r₂))
    (L := Fin.append L₁ L₂) hX hF hE₂
    (Fin.addCases (fun j => by simpa using hL₁c j) (fun j => by simpa using hL₂c j)) (by
      simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, Pi.neg_apply, neg_smul,
        Finset.sum_neg_distrib, ← hsum₁, ← hsum₂, hω₁, hω₂]
      abel)
  linarith [h.eq (h'.sub_of_isMultiplicityAlong hμ), hμ.nonneg (sub_nonneg.mpr hD)]

/-! ### Effective `ℝ`-Cartier divisors on curves -/

section Curves

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- A real vector `r` is approximated, in any open neighbourhood, by rational vectors satisfying
every integral linear relation that `r` satisfies. -/
private lemma exists_rat_approx {m : ℕ} (r : Fin m → ℝ) {O : Set (Fin m → ℝ)}
    (hO : IsOpen O) (hr : r ∈ O) :
    ∃ q : Fin m → ℚ, (fun j => (q j : ℝ)) ∈ O ∧
      ∀ c : Fin m → ℤ, ∑ j, (c j : ℝ) * r j = 0 → ∑ j, (c j : ℚ) * q j = 0 := by
  let V := Submodule.span ℚ (Set.range r)
  haveI : FiniteDimensional ℚ V := FiniteDimensional.span_of_finite ℚ (Set.finite_range r)
  let b := Module.finBasis ℚ V
  let v : Fin m → V := fun j => ⟨r j, Submodule.subset_span ⟨j, rfl⟩⟩
  let a : Fin m → Fin (Module.finrank ℚ V) → ℚ := fun j i => b.repr (v j) i
  let F : (Fin (Module.finrank ℚ V) → ℝ) → (Fin m → ℝ) := fun t j => ∑ i, t i * a j i
  have hF : Continuous F := by fun_prop
  have hω : F (fun i => ((b i : V) : ℝ)) = r := by
    funext j
    have h := congrArg Subtype.val (b.sum_repr (v j))
    simp only [Submodule.coe_sum, Submodule.coe_smul, Rat.smul_def] at h
    simp only [F, a]
    refine Eq.trans ?_ h
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hdense : DenseRange (fun t : Fin (Module.finrank ℚ V) → ℚ => fun i => (t i : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  obtain ⟨t, ht⟩ := hdense.exists_mem_open (hO.preimage hF)
    ⟨_, (show _ ∈ F ⁻¹' O by rw [Set.mem_preimage, hω]; exact hr)⟩
  refine ⟨fun j => ∑ i, t i * a j i, ?_, fun c hc => ?_⟩
  · have : (fun j => ((∑ i, t i * a j i : ℚ) : ℝ)) = F (fun i => (t i : ℝ)) := by
      funext j
      push_cast [F]
      rfl
    exact this ▸ ht
  · have hV : ∑ j, (c j : ℚ) • v j = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, Rat.smul_def, v, Rat.cast_intCast,
        Submodule.coe_zero]
      exact hc
    have hi : ∀ i, ∑ j, (c j : ℚ) * a j i = 0 := fun i => by
      have := congrArg (fun w => b.repr w i) hV
      simpa [map_sum, a] using this
    calc ∑ j, (c j : ℚ) * ∑ i, t i * a j i = ∑ i, t i * ∑ j, (c j : ℚ) * a j i := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by simp [hi]

/-- Clearing the denominators of a rational vector `q` such that `∑ q_j L_j` has positive
coefficients exactly on the prime divisors of `Supp Δ`: a positive multiple of `∑ q_j L_j` is an
effective Cartier divisor with support `Supp Δ`. -/
private lemma exists_isCartier_supp_eq_of_rat {W : Scheme.{u}} [IsLocallyNoetherian W]
    [IsNormal W] {Δ : RDivisor W} {m : ℕ} (L : Fin m → Divisor W) (hL : ∀ j, (L j).IsCartier)
    (q : Fin m → ℚ) (hpos : ∀ P ∈ Δ.support, (0 : ℚ) < ∑ j, q j * (L j P))
    (hzero : ∀ P ∉ Δ.support, ∑ j, q j * (L j P) = 0) :
    ∃ N : ℕ, 0 < N ∧ ∃ E : Divisor W, E.IsCartier ∧ 0 ≤ E ∧ E.supp = Δ.supp ∧
      ∀ P, ((E P : ℤ) : ℚ) = N * ∑ j, q j * (L j P) := by
  obtain ⟨N, hN, n, hn⟩ := exists_pos_nat_mul_eq_intCast q
  let E : Divisor W := ∑ j, n j • L j
  have hEP : ∀ P, ((E P : ℤ) : ℚ) = N * ∑ j, q j * (L j P) := fun P => by
    simp only [E, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul, Int.cast_sum,
      Int.cast_mul, Finset.mul_sum, ← hn, mul_assoc]
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have hE : ∀ P, (P ∈ Δ.support → 0 < E P) ∧ (P ∉ Δ.support → E P = 0) := fun P =>
    ⟨fun hP => by exact_mod_cast (hEP P).symm ▸ mul_pos hNq (hpos P hP),
      fun hP => by exact_mod_cast (hEP P).trans (by rw [hzero P hP, mul_zero] : _ = (0 : ℚ))⟩
  have hE0 : 0 ≤ E := fun P => by
    by_cases hP : P ∈ Δ.support
    exacts [((hE P).1 hP).le, ((hE P).2 hP).ge]
  have hsupp : E.support = Δ.support := by
    ext P
    by_cases hP : P ∈ Δ.support
    · exact iff_of_true (Finsupp.mem_support_iff.mpr ((hE P).1 hP).ne') hP
    · exact iff_of_false (Finsupp.notMem_support_iff.mpr ((hE P).2 hP)) hP
  exact ⟨N, hN, E, Divisor.cartierSubgroup.sum_mem fun j _ => (hL j).zsmul (n j), hE0,
    by simp only [DivisorWithCoeffs.supp, hsupp], hEP⟩

/-- **The rational case.** If `q` is a rational vector such that `∑ q_j L_j` has positive
coefficients exactly on the prime divisors of `Supp Δ`, and `C` is not contained in `Supp Δ`, then
`∑ q_j (L_j · C) ≥ 0`, and `∑ q_j (L_j · C) > 0` if moreover `C` meets `Supp Δ`. -/
private lemma sum_mul_nonneg_and_pos_of_rat (k : Type u) [Field k] {W : Scheme.{u}}
    (sW : W ⟶ Spec (.of k)) [QuasiCompact sW] [IsLocallyNoetherian W] [IsNormal W]
    {Δ : RDivisor W} (C : ProperCurve sW) (hC : ¬ Set.range C.ι ⊆ (Δ.supp : Set W))
    {m : ℕ} (L : Fin m → Divisor W) (hL : ∀ j, (L j).IsCartier) (d : Fin m → ℤ)
    (hd : ∀ j, IsCartierIntersectionNumber k sW C (L j) (hL j) (d j))
    {C' : Scheme.{u}} {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν)
    (hdim : topologicalKrullDim C' ≤ 1) (q : Fin m → ℚ)
    (hpos : ∀ P ∈ Δ.support, (0 : ℚ) < ∑ j, q j * (L j P))
    (hzero : ∀ P ∉ Δ.support, ∑ j, q j * (L j P) = 0) :
    (0 : ℝ) ≤ ∑ j, (q j : ℝ) * d j ∧
      ((Set.range C.ι ∩ (Δ.supp : Set W)).Nonempty → (0 : ℝ) < ∑ j, (q j : ℝ) * d j) := by
  obtain ⟨N, hN, E, hEc, hE0, hsupp, hEP⟩ := exists_isCartier_supp_eq_of_rat L hL q hpos hzero
  have := hν.isFinite
  have := hν.isIntegral
  haveI : IsDominant ν := hν.isBirationalMorphism.isDominant
  haveI : IsProper ((ν ≫ C.ι) ≫ sW) := by
    rw [Category.assoc]
    infer_instance
  have hsurj : Function.Surjective ν := ν.surjective
  have hne : ∃ c : C', (ν ≫ C.ι) c ∉ E.supp := by
    obtain ⟨_, ⟨c, rfl⟩, hc⟩ := Set.not_subset.mp hC
    obtain ⟨c', rfl⟩ := hsurj c
    exact ⟨c', by rw [hsupp]; exact hc⟩
  obtain ⟨hnn, hiff⟩ :=
    MMP.Threefold.Mori.degreeOn_nonneg_and_eq_zero_iff sW (ν ≫ C.ι) hdim E hEc hE0 hne
  have h1 : IsRIntersectionNumber k sW (Divisor.toRDivisor E) ![1] ![E] C
      (E.degreeOn k sW (ν ≫ C.ι) hdim hEc) := by
    refine ⟨fun j => by fin_cases j; exact hEc, ![E.degreeOn k sW (ν ≫ C.ι) hdim hEc], ?_,
      fun j => ?_, by simp⟩
    · simp
    · fin_cases j
      exact ⟨C', ν, hν, hdim, rfl⟩
  have h2 : IsRIntersectionNumber k sW (Divisor.toRDivisor E) (fun j => (N : ℝ) * q j) L C
      (∑ j, ((N : ℝ) * q j) * d j) := by
    refine ⟨hL, d, ?_, hd, rfl⟩
    ext P
    have h := congrArg (fun z : ℚ => (z : ℝ)) (hEP P)
    simp only [Rat.cast_intCast, Rat.cast_mul, Rat.cast_sum, Rat.cast_natCast] at h
    simp only [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply, Finsupp.smul_apply,
      smul_eq_mul] at h ⊢
    change ((E P : ℤ) : ℝ) = ∑ j, (N : ℝ) * q j * ((L j P : ℤ) : ℝ)
    rw [h, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have heq := (IsRIntersectionNumber.eq_and_linear k sW C).1 _ _ _ _ _ _ _ h1 h2
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hmul : (E.degreeOn k sW (ν ≫ C.ι) hdim hEc : ℝ) = N * ∑ j, (q j : ℝ) * d j := by
    rw [heq, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  refine ⟨(mul_nonneg_iff_of_pos_left hNr).mp (by rw [← hmul]; exact_mod_cast hnn),
    fun hmeet => pos_of_mul_pos_right ?_ hNr.le⟩
  have hdeg : 0 < E.degreeOn k sW (ν ≫ C.ι) hdim hEc := by
    refine lt_of_le_of_ne hnn fun h0 => ?_
    obtain ⟨_, ⟨c, rfl⟩, hc⟩ := hmeet
    obtain ⟨c', rfl⟩ := hsurj c
    exact (hiff.mp h0.symm) c' (by rw [hsupp]; exact hc)
  rw [← hmul]
  exact_mod_cast hdeg

/-- The coefficients of a divisor presented as `∑ r_j L_j`. -/
private lemma apply_eq_sum_of_eq_sum {W : Scheme.{u}} [IsLocallyNoetherian W] [IsNormal W]
    {Δ : RDivisor W} {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor W}
    (h : Δ = ∑ j, r j • Divisor.toRDivisor (L j)) : ∀ P, Δ P = ∑ j, r j * (L j P) := fun P => by
  rw [h]
  simp only [Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul]
  rfl

/-- Rational vectors `q` close to the coefficient vector `r` of an effective presentation
`Δ = ∑ r_j L_j`, and satisfying every integral relation `r` satisfies, make `∑ q_j L_j` positive
exactly on the prime divisors of `Supp Δ`. -/
private lemma exists_isOpen_forall_rat {W : Scheme.{u}} [IsLocallyNoetherian W] [IsNormal W]
    {Δ : RDivisor W} (hΔeff : Δ.IsEffective) {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor W}
    (hΔr : Δ = ∑ j, r j • Divisor.toRDivisor (L j)) :
    ∃ O : Set (Fin m → ℝ), IsOpen O ∧ r ∈ O ∧ ∀ q : Fin m → ℚ, (fun j => (q j : ℝ)) ∈ O →
      (∀ c : Fin m → ℤ, ∑ j, (c j : ℝ) * r j = 0 → ∑ j, (c j : ℚ) * q j = 0) →
      (∀ P ∈ Δ.support, (0 : ℚ) < ∑ j, q j * (L j P)) ∧
        ∀ P ∉ Δ.support, ∑ j, q j * (L j P) = 0 := by
  have hΔP := apply_eq_sum_of_eq_sum hΔr
  have hrel : ∀ P ∉ Δ.support, ∑ j, ((L j P : ℤ) : ℝ) * r j = 0 := fun P hP => by
    rw [Finsupp.notMem_support_iff, hΔP] at hP
    rw [← hP]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  let O : Set (Fin m → ℝ) := {s | ∀ P ∈ Δ.support, 0 < ∑ j, s j * (L j P)}
  have hOopen : IsOpen O := by
    simp only [O, Set.setOf_forall]
    exact isOpen_biInter_finset fun P _ => isOpen_lt continuous_const (by fun_prop)
  have hrO : r ∈ O := fun P hP => by
    rw [← hΔP]
    exact lt_of_le_of_ne (hΔeff P) (Ne.symm (Finsupp.mem_support_iff.mp hP))
  refine ⟨O, hOopen, hrO, fun q hqO hq => ⟨fun P hP => ?_, fun P hP => ?_⟩⟩
  · have h : (0 : ℝ) < ∑ j, (q j : ℝ) * ((L j P : ℤ) : ℝ) := hqO P hP
    exact_mod_cast h
  · rw [← hq _ (hrel P hP)]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- **Effective `ℝ`-Cartier divisors are nonnegative on curves outside their support.** On a
normal variety `X`, if `D` is an effective `ℝ`-Cartier divisor and `C` a proper curve not
contained in `Supp D`, then `D · C ≥ 0` for every presentation `D = ∑ r_j L_j`. -/
@[mmp "lem_fa2_effective_r_cartier_nonneg_on_curves"]
public theorem IsRIntersectionNumber.nonneg_of_isEffective (k : Type u) [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [QuasiCompact sX] [IsLocallyNoetherian X]
    [IsNormal X] (hX : IsNormalVariety k sX) (D : RDivisor X) (hD : IsCartierCombination D)
    (hD0 : D.IsEffective) (C : ProperCurve sX) (hC : C.point ∉ D.supp)
    {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor X) {x : ℝ}
    (hx : IsRIntersectionNumber k sX D r L C x) : 0 ≤ x := by
  obtain ⟨hL, d, hDr, hd, hxd⟩ := hx
  rw [hxd]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  obtain ⟨C', ν, hν, hdim, -⟩ := hd ⟨0, hm⟩
  obtain ⟨O, hO, hrO, hgood⟩ := exists_isOpen_forall_rat hD0 hDr
  by_contra hneg
  obtain ⟨q, ⟨hqO, hqd⟩, hq⟩ := exists_rat_approx r
    (hO.inter (isOpen_lt (f := fun s : Fin m → ℝ => ∑ j, s j * d j) (by fun_prop)
      continuous_const)) ⟨hrO, not_le.mp hneg⟩
  obtain ⟨hpos, hzero⟩ := hgood q hqO hq
  refine ((sum_mul_nonneg_and_pos_of_rat k sX C (fun h => hC (h ?_)) L hL d hd hν hdim q hpos
    hzero).1).not_gt hqd
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  exact subset_closure rfl

/-- An effective `ℝ`-Cartier divisor `Δ` on a normal variety has positive intersection number
with every proper irreducible curve `C` that meets `Supp Δ` and is not contained in it: for any
presentation `Δ = ∑ r_j L_j` by Cartier divisors, the value `x = Δ · C` it computes is
positive. -/
@[mmp "lem_fa2_effective_r_cartier_pos_on_curves"]
public theorem IsRIntersectionNumber.pos_of_isEffective (k : Type u) [Field k] {W : Scheme.{u}}
    (sW : W ⟶ Spec (.of k)) [QuasiCompact sW] [IsLocallyNoetherian W] [IsNormal W]
    (hW : IsNormalVariety k sW) {Δ : RDivisor W} (hΔ : IsCartierCombination Δ)
    (hΔeff : Δ.IsEffective) (C : ProperCurve sW)
    (hC : ¬ Set.range C.ι ⊆ (Δ.supp : Set W))
    (hmeet : (Set.range C.ι ∩ (Δ.supp : Set W)).Nonempty)
    {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor W) {x : ℝ}
    (hx : IsRIntersectionNumber k sW Δ r L C x) :
    0 < x := by
  obtain ⟨hL, d, hΔr, hd, hxd⟩ := hx
  have hm : m ≠ 0 := by
    rintro rfl
    obtain ⟨_, -, hy⟩ := hmeet
    rw [SetLike.mem_coe, DivisorWithCoeffs.mem_supp_iff] at hy
    obtain ⟨E, hE, -⟩ := hy
    exact hE (by simp [DivisorWithCoeffs.coeff_apply, apply_eq_sum_of_eq_sum hΔr])
  obtain ⟨C', ν, hν, hdim, -⟩ := hd ⟨0, Nat.pos_of_ne_zero hm⟩
  have hrat := fun q hpos hzero =>
    (sum_mul_nonneg_and_pos_of_rat k sW C hC L hL d hd hν hdim q hpos hzero).2 hmeet
  obtain ⟨O, hO, hrO, hgood⟩ := exists_isOpen_forall_rat hΔeff hΔr
  rw [hxd]
  by_contra hneg
  rcases (not_lt.mp hneg).lt_or_eq with hlt | heq
  · obtain ⟨q, ⟨hqO, hqd⟩, hq⟩ := exists_rat_approx r
      (hO.inter (isOpen_lt (f := fun s : Fin m → ℝ => ∑ j, s j * d j) (by fun_prop)
        continuous_const)) ⟨hrO, hlt⟩
    obtain ⟨hpos, hzero⟩ := hgood q hqO hq
    exact (hrat q hpos hzero).not_gt hqd
  · obtain ⟨q, hqO, hq⟩ := exists_rat_approx r hO hrO
    obtain ⟨hpos, hzero⟩ := hgood q hqO hq
    have h0 := hq d (by rw [← heq]; exact Finset.sum_congr rfl fun j _ => mul_comm _ _)
    have h0' : ∑ j, (q j : ℝ) * d j = 0 := by
      have := congrArg (fun z : ℚ => (z : ℝ)) h0
      push_cast at this
      rw [← this]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    exact (hrat q hpos hzero).ne' h0'

/-! ### The negativity lemma over a point -/

/-- Every Cartier divisor has an intersection number with a proper curve: the normalization
of the curve is a regular proper curve birational to it. -/
private theorem exists_isCartierIntersectionNumber (k : Type u) [Field k] {Y : Scheme}
    (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]
    (C : MMP.Mori.ProperCurve sY) (L : MMP.Mori.Divisor Y)
    (hL : L.IsCartier) : ∃ d, MMP.Flips.IsCartierIntersectionNumber k sY C L hL d := by
  let p := C.ι ≫ sY
  haveI : AlgebraicGeometry.IsCurve k p := C.isCurve
  have hX := finite_irreducibleComponents_of_locallyOfFiniteType k p
  haveI hvar : AlgebraicGeometry.IsVariety k (normalizationOverField k p ≫ p) :=
    isVariety_normalizationOverField k p
  haveI : IsIntegral (normalizationSchemeOverField k p) := hvar.toIsIntegral
  haveI : IsFinite (normalizationOverField k p) := isFinite_normalizationOverField k p
  have hν : IsCurveNormalization (normalizationOverField k p) :=
    { isIntegral := inferInstance
      isNormal := Scheme.isNormal_normalizationScheme C.scheme hX
      isFinite := inferInstance
      isBirationalMorphism := by
        haveI : Finite (irreducibleComponents (normalizationSchemeOverField k p)) := by
          rw [irreducibleComponents_eq_singleton]
          exact Set.finite_singleton _
        haveI : Finite (irreducibleComponents C.scheme) := by
          rw [irreducibleComponents_eq_singleton]
          exact Set.finite_singleton _
        obtain ⟨U, V, hUV, hU, hV, hiso⟩ := exists_dense_opens_isIso_resLE_of_isBirational
          (normalizationOverField k p) (Scheme.isBirational_normalization C.scheme hX)
          (Or.inl ⟨inferInstance, inferInstance⟩)
        exact isBirationalMorphism_of_isIso_resLE _ U V hU.nonempty hV.nonempty hUV hiso }
  exact ⟨_, _, _, hν, (topologicalKrullDim_normalizationSchemeOverField k p).le.trans C.dim_le,
    rfl⟩

/-- A proper curve contracted by `f` that meets `Supp B` without lying in it contradicts
`-B` being `f`-nef: `B` is positive on it. -/
private theorem not_isContractedBy_of_isRelativelyNef_neg (k : Type u) [Field k] {X Y : Scheme}
    (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]
    (hY : IsNormalVariety k sY) (f : Y ⟶ X)
    {B : RDivisor Y} (hB : IsCartierCombination B) (hBeff : B.IsEffective)
    (hnef : IsRelativelyNef k sY f (-B)) (C : MMP.Mori.ProperCurve sY)
    (hC : ¬ Set.range C.ι ⊆ (B.supp : Set Y))
    (hmeet : (Set.range C.ι ∩ (B.supp : Set Y)).Nonempty) :
    ¬ C.IsContractedBy f := by
  intro hCf
  obtain ⟨m, r, L, hL, hpres, hall⟩ := hnef
  choose d hd using fun j => exists_isCartierIntersectionNumber k sY C (L j) (hL j)
  have h0 := hall C hCf (∑ j, r j * d j) ⟨hL, d, hpres, hd, rfl⟩
  have hBpres : B = ∑ j, (-r j) • Divisor.toRDivisor (L j) := by
    rw [← neg_neg B, hpres]
    simp [neg_smul, Finset.sum_neg_distrib]
  have hpos := IsRIntersectionNumber.pos_of_isEffective k sY hY hB hBeff C hC hmeet (-r) L
    (x := ∑ j, (-r j) * d j) ⟨hL, d, hBpres, hd, rfl⟩
  simp only [neg_mul, Finset.sum_neg_distrib, neg_pos] at hpos
  linarith

/-- A closed connected subset `F` of a Noetherian quasi-sober space which meets a closed set `S`
without lying in it contains a point outside `S` specializing to a point of `S`. -/
private theorem exists_notMem_specializes_mem_of_isConnected {Y : Type*} [TopologicalSpace Y]
    [TopologicalSpace.NoetherianSpace Y] [QuasiSober Y] {F S : Set Y} (hF : IsClosed F)
    (hFc : _root_.IsConnected F) (hS : IsClosed S) (hmeet : (F ∩ S).Nonempty) (hsub : ¬ F ⊆ S) :
    ∃ η ∈ F, η ∉ S ∧ ∃ s ∈ S, η ⤳ s := by
  set T := F \ S
  have hTF : closure T ⊆ F := closure_minimal Set.diff_subset hF
  by_cases hdis : (closure T ∩ S).Nonempty
  · obtain ⟨s, hsT, hsS⟩ := hdis
    obtain ⟨Z, hZfin, hZcl, hZirr, hZeq⟩ :=
      TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible
        (isClosed_closure : IsClosed (closure T))
    have hsub' : closure T ⊆ ⋃₀ {t ∈ Z | (t ∩ T).Nonempty} := by
      refine closure_minimal (fun y hy => ?_) ?_
      · have : y ∈ ⋃₀ Z := hZeq ▸ subset_closure hy
        obtain ⟨z, hz, hyz⟩ := this
        exact ⟨z, ⟨hz, y, hyz, hy⟩, hyz⟩
      · exact (hZfin.subset (Set.sep_subset _ _)).isClosed_sUnion fun t ht => hZcl t ht.1
    obtain ⟨z, ⟨hzZ, t, htz, htT⟩, hsz⟩ := hsub' hsT
    obtain ⟨ζ, hζ⟩ := QuasiSober.sober (hZirr z hzZ) (hZcl z hzZ)
    have hzT : z ⊆ closure T := hZeq ▸ Set.subset_sUnion_of_mem hzZ
    exact ⟨ζ, hTF (hzT hζ.mem), fun hζS => htT.2 ((hζ.specializes htz).mem_closed hS hζS),
      s, hsS, hζ.specializes hsz⟩
  · obtain ⟨y, hyF, hyS⟩ := Set.not_subset.mp hsub
    obtain ⟨w, -, hwT, hwS⟩ := isPreconnected_closed_iff.mp hFc.isPreconnected _ _
      isClosed_closure hS (fun a ha => by
        by_cases haS : a ∈ S
        · exact Or.inr haS
        · exact Or.inl (subset_closure (show a ∈ T from ⟨ha, haS⟩)))
      ⟨y, hyF, subset_closure (show y ∈ T from ⟨hyF, hyS⟩)⟩ hmeet
    exact (hdis ⟨w, hwT, hwS⟩).elim

/-- The scheme-theoretic fibre of a proper morphism of `k`-schemes over a closed point is proper
over `k`. -/
private theorem isProper_fiberι_comp {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (f : Y ⟶ X)
    (hf : f ≫ sX = sY) [IsProper f] (x : X) (hx : IsClosed ({x} : Set X)) :
    IsProper (f.fiberι x ≫ sY) := by
  have h : f.fiberι x ≫ sY = f.fiberToSpecResidueField x ≫ (X.fromSpecResidueField x ≫ sX) := by
    simp only [← hf, Scheme.Hom.fiber_fac_assoc]
  rw [h]
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  haveI : LocallyOfFiniteType (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_locallyOfFiniteType.mp hx
  haveI : IsFinite (X.fromSpecResidueField x ≫ sX) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  haveI : IsProper (f.fiberToSpecResidueField x) :=
    inferInstanceAs (IsProper (Limits.pullback.snd f (X.fromSpecResidueField x)))
  haveI : IsProper (X.fromSpecResidueField x ≫ sX) := inferInstance
  infer_instance

/-- The image in `Y` of a proper curve of the fibre `f⁻¹(x)` is a proper curve of `Y` contained
in `f⁻¹(x)`. -/
private theorem exists_properCurve_closure_subset_preimage (k : Type u) [Field k] {X Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsSeparated sY] [LocallyOfFiniteType sY] (f : Y ⟶ X) (x : X)
    [IsProper (f.fiberι x ≫ sY)] (C' : MMP.Mori.ProperCurve (f.fiberι x ≫ sY)) :
    ∃ C : MMP.Mori.ProperCurve sY, C.point = f.fiberι x C'.point ∧
      closure {C.point} ⊆ f.base ⁻¹' {x} := by
  let ι := f.fiberι x
  have hφsY : (C'.ι ≫ ι) ≫ sY = C'.ι ≫ (ι ≫ sY) := Category.assoc _ _ _
  haveI : AlgebraicGeometry.IsCurve k ((C'.ι ≫ ι) ≫ sY) := hφsY ▸ C'.isCurve
  haveI : IsProper ((C'.ι ≫ ι) ≫ sY) := by
    rw [hφsY]
    infer_instance
  have hrange : Set.range (C'.ι ≫ ι) = closure {ι C'.point} := C'.range_comp ι rfl
  have hinj : Function.Injective (C'.ι ≫ ι) := fun a b h =>
    C'.ι.isEmbedding.injective (ι.isEmbedding.injective (by simpa using h))
  have hnc : ¬ ∃ z, Set.range (C'.ι ≫ ι) = {z} := by
    rintro ⟨z, hz⟩
    have : Subsingleton C'.scheme := ⟨fun a b => hinj (by
      have ha : (C'.ι ≫ ι) a ∈ ({z} : Set Y) := hz ▸ ⟨a, rfl⟩
      have hb : (C'.ι ≫ ι) b ∈ ({z} : Set Y) := hz ▸ ⟨b, rfl⟩
      exact ha.trans hb.symm)⟩
    have h0 := topologicalKrullDim_zero_of_discreteTopology C'.scheme
    rw [C'.dim_eq] at h0
    exact absurd h0 (by decide)
  have hcurve := MMP.Mori.isCurve_imageι_comp sY (C'.ι ≫ ι) hnc
  have hker := C'.ker_comp ι
  have hdim : topologicalKrullDim (curveSubschemeAt (ι C'.point)) = 1 := by
    have h1 := hcurve.topologicalKrullDim_eq_one
    change topologicalKrullDim (C'.ι ≫ ι).ker.subscheme = 1 at h1
    rwa [hker] at h1
  have hprop : IsProper (curveSubschemeAtι (ι C'.point) ≫ sY) := by
    have h1 : IsProper ((C'.ι ≫ ι).imageι ≫ sY) := isProper_imageι_comp _ sY
    change IsProper ((C'.ι ≫ ι).ker.subschemeι ≫ sY) at h1
    rwa [hker] at h1
  let C : MMP.Mori.ProperCurve sY := ⟨ι C'.point, ⟨hdim, hprop⟩⟩
  refine ⟨C, rfl, ?_⟩
  change closure {ι C'.point} ⊆ _
  rw [← hrange, ← f.range_fiberι x]
  rintro _ ⟨w, rfl⟩
  exact ⟨C'.ι w, by simp [ι]⟩

/-- The fibre of `f` over a closed point is connected and proper, so if it meets a closed set `S`
without lying in it, it contains a proper curve contracted by `f` that meets `S` without lying
in it. -/
private theorem exists_properCurve_isContractedBy (k : Type u) [Field k] {X Y : Scheme}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY] [IsLocallyNoetherian Y]
    [IsNormal Y] (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY)
    (f : Y ⟶ X) (hf : f ≫ sX = sY) [IsProper f] (hfb : IsBirationalMorphism f)
    (x : X) (hx : IsClosed ({x} : Set X)) {S : Set Y} (hS : IsClosed S)
    (hmeet : (f.base ⁻¹' {x} ∩ S).Nonempty) (hsub : ¬ f.base ⁻¹' {x} ⊆ S) :
    ∃ C : MMP.Mori.ProperCurve sY, C.IsContractedBy f ∧ ¬ Set.range C.ι ⊆ S ∧
      (Set.range C.ι ∩ S).Nonempty := by
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  haveI : IsSeparated sY := hY.1.toIsSeparated
  haveI : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace sY
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI : IsNoetherian Y := {}
  have hconn := (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism
    sY sX hY.1 hX f hfb).2 x
  have hFcl : IsClosed (f.base ⁻¹' {x}) := hx.preimage f.continuous
  obtain ⟨η, hηF, hηS, s, hsS, hηs⟩ :=
    exists_notMem_specializes_mem_of_isConnected hFcl hconn hS hmeet hsub
  obtain ⟨p, hps, hpc⟩ := nonempty_inter_closedPoints
    ⟨s, (show s ∈ closure {s} from subset_closure rfl)⟩ isClosed_closure.isLocallyClosed
  have hηp : η ⤳ p := hηs.trans (specializes_iff_mem_closure.mpr hps)
  have hpS : p ∈ S := (specializes_iff_mem_closure.mpr hps).mem_closed hS hsS
  have hpF : p ∈ f.base ⁻¹' {x} := hηp.mem_closed hFcl hηF
  let ι := f.fiberι x
  let sF := ι ≫ sY
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : IsProper sF := isProper_fiberι_comp sX sY f hf x hx
  haveI : IsLocallyNoetherian (f.fiber x) := LocallyOfFiniteType.isLocallyNoetherian sF
  have hrι : Set.range ι = f.base ⁻¹' {x} := f.range_fiberι x
  obtain ⟨η', hη'⟩ : η ∈ Set.range ι := hrι ▸ hηF
  obtain ⟨p', hp'⟩ : p ∈ Set.range ι := hrι ▸ hpF
  have hemb : Topology.IsEmbedding ι := ι.isEmbedding
  have hη'p' : η' ⤳ p' := by
    rw [← hemb.isInducing.specializes_iff, hη', hp']
    exact hηp
  have hp'c : IsClosed ({p'} : Set (f.fiber x)) := by
    have : ({p'} : Set (f.fiber x)) = ι ⁻¹' {p} := by
      ext z
      simp [← hp', hemb.injective.eq_iff]
    rw [this]
    exact (mem_closedPoints_iff.mp hpc).preimage ι.continuous
  obtain ⟨y', -, hy'p', hy'S, hy'⟩ := MMP.Fourfold.exists_isProperCurve_of_specializes sF hη'p'
    hp'c (hS.preimage ι.continuous) (by simpa [hp'] using hpS)
    (by simpa [hη'] using hηS)
  let C' : MMP.Mori.ProperCurve sF := ⟨y', hy'⟩
  obtain ⟨C, hCp, hclF⟩ := exists_properCurve_closure_subset_preimage k sY f x C'
  have hCf : C.IsContractedBy f := fun z hz => by
    have h1 := hclF hz
    have h2 := hclF (subset_closure rfl : C.point ∈ closure {C.point})
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at h1 h2
    exact h1.trans h2.symm
  refine ⟨C, hCf, ?_, ?_⟩
  · rw [C.range_ι, hCp]
    intro h
    exact hy'S (h (subset_closure rfl))
  · refine ⟨p, ?_, hpS⟩
    rw [C.range_ι, hCp, ← hp']
    exact specializes_iff_mem_closure.mp (hy'p'.map ι.continuous)

/-- **Negativity lemma over a point.** If `f : Y ⟶ X` is a proper birational morphism of normal
varieties over `k` and `B` is an effective `ℝ`-Cartier divisor on `Y` with `-B` `f`-nef, then
every fibre `f⁻¹(x)`, `x ∈ X`, is either contained in `Supp B` or disjoint from `Supp B`. -/
@[mmp "thm_fa2_negativity_lemma_fibers"]
public theorem preimage_singleton_subset_supp_or_disjoint_of_isRelativelyNef_neg
    (k : Type u) [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]
    (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY)
    (f : Y ⟶ X) (hf : f ≫ sX = sY) [IsProper f] (hfb : IsBirationalMorphism f)
    {B : RDivisor Y} (hB : IsCartierCombination B) (hBeff : B.IsEffective)
    (hnef : IsRelativelyNef k sY f (-B)) (x : X) :
    f.base ⁻¹' {x} ⊆ (B.supp : Set Y) ∨ Disjoint (f.base ⁻¹' {x}) (B.supp : Set Y) := by
  by_contra h
  rw [not_or, Set.not_disjoint_iff] at h
  obtain ⟨hsub, y1, hy1, hy1S⟩ := h
  obtain ⟨y2, hy2, hy2S⟩ := Set.not_subset.mp hsub
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  haveI : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace sY
  have hT : IsLocallyClosed (closure {y2} ∩ (B.supp : Set Y)ᶜ) :=
    isClosed_closure.isLocallyClosed.inter B.supp.isClosed.isOpen_compl.isLocallyClosed
  obtain ⟨q, ⟨hq2, hqS⟩, hqc⟩ :=
    nonempty_inter_closedPoints
      ⟨y2, (show y2 ∈ closure {y2} ∩ (B.supp : Set Y)ᶜ from ⟨subset_closure rfl, hy2S⟩)⟩ hT
  have hqc' : IsClosed ({f q} : Set X) := by
    simpa using f.isClosedMap _ (mem_closedPoints_iff.mp hqc)
  have hxq : x ⤳ f q := by
    have h2 : y2 ⤳ q := specializes_iff_mem_closure.mpr hq2
    have h3 := h2.map f.continuous
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy2
    rwa [hy2] at h3
  have hfS : IsClosed (f '' (B.supp : Set Y)) := f.isClosedMap _ B.supp.isClosed
  obtain ⟨y3, hy3S, hy3⟩ := hxq.mem_closed hfS ⟨y1, hy1S, hy1⟩
  obtain ⟨C, hCf, hC, hCS⟩ := exists_properCurve_isContractedBy k sX sY hX hY f hf hfb (f q) hqc'
    B.supp.isClosed ⟨y3, hy3, hy3S⟩ fun h => hqS (h rfl)
  exact not_isContractedBy_of_isRelativelyNef_neg k sY hY f hB hBeff hnef C hC hCS hCf

end Curves

end MMP.Flips

/-! ### Curves through prescribed points -/

namespace MMP

/-- A variety of dimension at least one over `k` has, besides any given closed point `v`, another
closed point: otherwise `v` would be dense (closed points of a Jacobson space are dense), hence
the whole space, and the dimension would be zero. -/
private theorem exists_isClosed_singleton_ne {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (hX : 1 ≤ topologicalKrullDim X) {v : X}
    (hv : IsClosed ({v} : Set X)) :
    ∃ v' : X, IsClosed ({v'} : Set X) ∧ v ≠ v' := by
  by_contra! h
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hsub : closedPoints X ⊆ {v} := fun x hx ↦ (h x hx).symm
  have huniv : (Set.univ : Set X) ⊆ {v} := by
    rw [← closure_closedPoints]
    exact (closure_mono hsub).trans hv.closure_eq.le
  haveI : Subsingleton X := ⟨fun a b ↦ by
    rw [Set.mem_singleton_iff.1 (huniv (Set.mem_univ a)),
      Set.mem_singleton_iff.1 (huniv (Set.mem_univ b))]⟩
  haveI : Subsingleton (TopologicalSpace.IrreducibleCloseds X) := ⟨fun Z Z' ↦ by
    ext x
    obtain ⟨z, hz⟩ := Z.isIrreducible.nonempty
    obtain ⟨z', hz'⟩ := Z'.isIrreducible.nonempty
    constructor
    · intro _
      rwa [Subsingleton.elim x z']
    · intro _
      rwa [Subsingleton.elim x z]⟩
  have h0 : topologicalKrullDim X ≤ 0 := Order.krullDim_nonpos_of_subsingleton
  exact absurd (hX.trans h0) (by decide)

/-- On a positive-dimensional variety `X` over a field `k`, any two closed points `x` and `y`
(possibly equal) lie on a closed integral curve: there is a closed immersion `i : C ⟶ X` such
that `C` is a curve over `k` via `i ≫ f` whose image contains `x` and `y`, and `C` is proper over
`k` whenever `X` is. -/
@[mmp "lem_mmp_foundation_fa2_curve_two_points"]
public theorem exists_isClosedImmersion_isCurve_and_isProper_of_isClosed_singleton
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [MMP.Mori.IsVariety k f]
    (hdim : 0 < topologicalKrullDim X) {x y : X}
    (hx : IsClosed ({x} : Set X)) (hy : IsClosed ({y} : Set X)) :
    ∃ (C : Scheme.{u}) (i : C ⟶ X),
      IsClosedImmersion i ∧ MMP.Mori.IsCurve k (i ≫ f) ∧
        x ∈ Set.range i ∧ y ∈ Set.range i ∧ (IsProper f → IsProper (i ≫ f)) := by
  have curve : ∀ {p q : X}, IsClosed ({p} : Set X) → IsClosed ({q} : Set X) → p ≠ q →
      ∃ C : TopologicalSpace.IrreducibleCloseds X, topologicalKrullDim (C : Set X) = 1 ∧
        p ∈ (C : Set X) ∧ q ∈ (C : Set X) := fun hp hq hpq ↦
    Stacks.Algebraization.CurveThroughPoints.exists_dim_one_of_mem f
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩ (Set.mem_univ _)
      (Set.mem_univ _) hp hq hpq
  obtain ⟨C, hC, hxC, hyC⟩ : ∃ C : TopologicalSpace.IrreducibleCloseds X,
      topologicalKrullDim (C : Set X) = 1 ∧ x ∈ (C : Set X) ∧ y ∈ (C : Set X) := by
    rcases eq_or_ne x y with rfl | hxy
    · obtain ⟨z, hz, hne⟩ :=
        exists_isClosed_singleton_ne f ((WithBot.one_le_iff_pos _).mpr hdim) hx
      obtain ⟨C, hC, hxC, -⟩ := curve hx hz hne
      exact ⟨C, hC, hxC, hxC⟩
    · exact curve hx hy hxy
  let W := MMP.Intersection.Scheme.Subvariety.ofIsIrreducible
    ⟨(C : Set X), C.isClosed⟩ C.isIrreducible
  haveI := W.isIntegral
  have hr : Set.range W.ideal.subschemeι = (C : Set X) := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have hdimW : topologicalKrullDim W.ideal.subscheme = 1 := by
    have he := (IsClosedImmersion.isClosedEmbedding W.ideal.subschemeι).isEmbedding
    rw [IsHomeomorph.topologicalKrullDim_eq _ he.toHomeomorph.isHomeomorph, hr]
    exact hC
  refine ⟨W.ideal.subscheme, W.ideal.subschemeι, inferInstance,
    (MMP.Mori.isCurve_iff k _).2 ⟨{ }, hdimW⟩, hr ▸ hxC, hr ▸ hyC, fun _ => inferInstance⟩

/-- The affine chart of the irreducible closed subset `W` with generic point `η`: if `η` lies in
the affine open `U`, then `Spec (Γ(X, U) ⧸ 𝔭)`, with `𝔭` the prime of `η`, embeds into `X` with
image `W ∩ U`. -/
private theorem exists_isEmbedding_range_eq_inter {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) {W : Set X} {η : X} (hη : IsGenericPoint η W) (hηU : η ∈ U) :
    ∃ (𝔭 : Ideal Γ(X, U)) (_ : 𝔭.IsPrime) (e : PrimeSpectrum (Γ(X, U) ⧸ 𝔭) → X),
      Topology.IsEmbedding e ∧ Set.range e = W ∩ U := by
  let ι : PrimeSpectrum Γ(X, U) → X := hU.fromSpec
  have hι : Topology.IsEmbedding ι := hU.fromSpec.isOpenEmbedding.isEmbedding
  have hιsp : ∀ p q, ι p ⤳ ι q ↔ p.asIdeal ≤ q.asIdeal := fun p q => by
    rw [hι.isInducing.specializes_iff, ← PrimeSpectrum.le_iff_specializes]
    rfl
  have hpt : ∀ x (hx : x ∈ U), ι (hU.primeIdealOf ⟨x, hx⟩) = x := fun x hx =>
    hU.fromSpec_primeIdealOf ⟨x, hx⟩
  let 𝔭 := (hU.primeIdealOf ⟨η, hηU⟩).asIdeal
  let mk := Ideal.Quotient.mk 𝔭
  have hmk : Function.Surjective mk := Ideal.Quotient.mk_surjective
  refine ⟨𝔭, inferInstance, fun q => ι (PrimeSpectrum.comap mk q),
    hι.comp (PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _ hmk).isEmbedding, ?_⟩
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨?_, hU.range_fromSpec ▸ Set.mem_range_self _⟩
    rw [← hη.specializes_iff_mem, ← hpt η hηU, hιsp]
    exact Ideal.mk_ker.symm.trans_le (Ideal.comap_mono bot_le)
  · rintro ⟨hxW, hxU⟩
    obtain ⟨q, hq⟩ : hU.primeIdealOf ⟨x, hxU⟩ ∈ Set.range (PrimeSpectrum.comap mk) := by
      rw [range_comap_of_surjective _ mk hmk, Ideal.mk_ker, PrimeSpectrum.mem_zeroLocus]
      change 𝔭 ≤ _
      rw [← hιsp, hpt, hpt]
      exact hη.specializes hxW
    exact ⟨q, by simp only [hq, hpt]⟩

/-- **A point specializing to finitely many prescribed points.** Let `X` be locally of finite
type over a field, `W ⊆ X` irreducible closed of dimension at least two, and `A ⊆ W` a nonempty
finite set of closed points lying in one affine open `U`. Then some point `t` of `W`, not its
generic point, specializes to every point of `A`. In the chart
`exists_isEmbedding_range_eq_inter` of `W` this is a nonzero prime of a finite type domain of
dimension at least two contained in finitely many maximal ideals, given by
`Stacks.Bertini.exists_isPrime_ne_bot_le_of_isMaximal`. -/
private theorem exists_specializes_of_subset_isAffineOpen
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    {U : X.Opens} (hU : IsAffineOpen U) (A : Finset X) (hAU : (A : Set X) ⊆ U)
    (hA : A.Nonempty) (hAcl : ∀ a ∈ A, IsClosed ({a} : Set X))
    (W : Set X) (hWc : IsClosed W) (hWi : IsIrreducible W) (hW : 2 ≤ topologicalKrullDim W)
    (hAW : (A : Set X) ⊆ W) :
    ∃ t ∈ W, closure {t} ≠ W ∧ ∀ a ∈ A, t ⤳ a := by
  classical
  obtain ⟨η, hη⟩ := QuasiSober.sober hWi hWc
  obtain ⟨a₀, ha₀⟩ := hA
  have hηU : η ∈ U := (hη.specializes (hAW ha₀)).mem_open U.isOpen (hAU ha₀)
  letI := Stacks.Algebraization.CurveThroughPoints.sectionsAlgebra f U
  haveI := Stacks.Algebraization.CurveThroughPoints.finiteType_sections f hU
  obtain ⟨𝔭, _, e, he, hre⟩ := exists_isEmbedding_range_eq_inter hU hη hηU
  have hesp : ∀ p q, e p ⤳ e q ↔ p.asIdeal ≤ q.asIdeal := fun p q => by
    rw [he.isInducing.specializes_iff, ← PrimeSpectrum.le_iff_specializes]
    rfl
  have hdim : 2 ≤ ringKrullDim (Γ(X, U) ⧸ 𝔭) := by
    rwa [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      he.toHomeomorph.isHomeomorph.topologicalKrullDim_eq, hre,
      AlgebraicGeometry.topologicalKrullDim_inter_isOpen_eq k f hWc hWi U.isOpen
        ⟨η, hη.mem, hηU⟩]
  have hq : ∀ a ∈ A, ∃ q, e q = a := fun a ha => by
    rw [← Set.mem_range, hre]
    exact ⟨hAW ha, hAU ha⟩
  obtain ⟨P, hP, hP0, hPs⟩ := Stacks.Bertini.exists_isPrime_ne_bot_le_of_isMaximal (k := k) hdim
    ((A.preimage e he.injective.injOn).image PrimeSpectrum.asIdeal) (by
      simp only [Finset.mem_image, Finset.mem_preimage, forall_exists_index, and_imp]
      rintro _ q hqA rfl
      rw [← PrimeSpectrum.isClosed_singleton_iff_isMaximal, ← he.injective.preimage_image {q},
        Set.image_singleton]
      exact (hAcl _ hqA).preimage he.continuous)
  have htW : e ⟨P, hP⟩ ∈ W := (hre.subset ⟨_, rfl⟩).1
  refine ⟨e ⟨P, hP⟩, htW, fun h => hP0 ?_, fun a ha => ?_⟩
  · have hbot := (show IsGenericPoint (e ⟨P, hP⟩) W from h).specializes
      (hre.subset ⟨⟨⊥, inferInstance⟩, rfl⟩).1
    exact le_bot_iff.mp ((hesp _ ⟨⊥, inferInstance⟩).mp hbot)
  · obtain ⟨q, rfl⟩ := hq a ha
    exact (hesp _ _).mpr (hPs _ (Finset.mem_image_of_mem _ (Finset.mem_preimage.mpr ha)))

/-- The closure of a point of an irreducible closed subset `W` is contained in `W`. -/
private theorem closureSingleton_le {X : Type*} [TopologicalSpace X]
    {W : TopologicalSpace.IrreducibleCloseds X} {x : X} (hx : x ∈ W) :
    TopologicalSpace.IrreducibleCloseds.closureSingleton x ≤ W := by
  rw [← SetLike.coe_subset_coe, TopologicalSpace.IrreducibleCloseds.coe_closureSingleton]
  exact closure_minimal (Set.singleton_subset_iff.mpr hx) W.isClosed'

/-- A closed point `a` of an irreducible closed subset `W` containing a second point `b` is a
proper irreducible closed subset of `W`. -/
private theorem closureSingleton_lt {X : Type*} [TopologicalSpace X]
    {W : TopologicalSpace.IrreducibleCloseds X} {a b : X} (ha : a ∈ W) (hb : b ∈ W)
    (hac : IsClosed ({a} : Set X)) (hab : a ≠ b) :
    TopologicalSpace.IrreducibleCloseds.closureSingleton a < W := by
  refine lt_of_le_of_ne (closureSingleton_le ha) fun h => hab ?_
  have : b ∈ (TopologicalSpace.IrreducibleCloseds.closureSingleton a : Set X) := h ▸ hb
  rw [TopologicalSpace.IrreducibleCloseds.coe_closureSingleton, hac.closure_eq] at this
  exact this.symm

/-- Iterating `exists_specializes_of_subset_isAffineOpen` along the height: an irreducible closed
subset of finite height containing two distinct closed points `a`, `b` of a finite set `A` of
closed points lying in one affine open contains an irreducible closed subset of dimension one
containing `A`. -/
private theorem exists_curve_of_height_le
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    {U : X.Opens} (hU : IsAffineOpen U) (A : Finset X) (hAU : (A : Set X) ⊆ U)
    (hAcl : ∀ a ∈ A, IsClosed ({a} : Set X)) {a b : X} (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b)
    (N : ℕ) : ∀ W : TopologicalSpace.IrreducibleCloseds X, Order.height W ≤ N →
      (A : Set X) ⊆ W → ∃ C : TopologicalSpace.IrreducibleCloseds X,
        topologicalKrullDim (C : Set X) = 1 ∧ (A : Set X) ⊆ C := by
  open TopologicalSpace in
  induction N with
  | zero =>
    intro W hN hAW
    have h := closureSingleton_lt (hAW ha) (hAW hb) (hAcl a ha) hab
    exact absurd ((Order.height_strictMono h (((Order.height_mono h.le).trans hN).trans_lt
      (by simp))).trans_le hN) (by simp)
  | succ N ih =>
    intro W hN hAW
    have hfin : Order.height W ≠ ⊤ := ne_top_of_le_ne_top (by simp) hN
    have hlt {C : IrreducibleCloseds X} (h : C < W) : Order.height C < Order.height W :=
      Order.height_strictMono h ((Order.height_mono h.le).trans_lt hfin.lt_top)
    by_cases h2 : 2 ≤ topologicalKrullDim (W : Set X)
    · obtain ⟨t, htW, hne, ht⟩ := exists_specializes_of_subset_isAffineOpen f hU A hAU
        ⟨a, ha⟩ hAcl W W.isClosed' W.isIrreducible' h2 hAW
      have hTW : IrreducibleCloseds.closureSingleton t < W := by
        refine lt_of_le_of_ne (closureSingleton_le htW) fun h => hne ?_
        rw [← IrreducibleCloseds.coe_closureSingleton, h]
      refine ih _ (Order.le_of_lt_succ (by simpa using (hlt hTW).trans_le hN)) fun x hx => ?_
      rw [SetLike.mem_coe, ← SetLike.mem_coe, IrreducibleCloseds.coe_closureSingleton]
      exact specializes_iff_mem_closure.mp (ht x hx)
    · refine ⟨W, ?_, hAW⟩
      push Not at h2
      rw [Stacks.Algebraization.CurveThroughPoints.topologicalKrullDim_eq_height] at h2 ⊢
      have h1 : 1 ≤ Order.height W := Order.one_le_iff_pos.mpr
        (bot_le.trans_lt (hlt (closureSingleton_lt (hAW ha) (hAW hb) (hAcl a ha) hab)))
      have h2' : Order.height W ≤ 1 :=
        Order.le_of_lt_succ (by simpa [one_add_one_eq_two] using (WithBot.coe_lt_coe.mp h2 :
          Order.height W < 2))
      exact_mod_cast le_antisymm h2' h1

/-- Over a field, a nonempty finite set of closed points of a projective
variety of positive dimension lies on an irreducible closed subset of dimension one. -/
@[mmp "lem_mmp_foundation_projective_curve_prescribed_points"]
public theorem exists_isClosed_isIrreducible_topologicalKrullDim_eq_one_superset
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (hXp : MMP.Mori.IsProjectiveVariety k f) (hX : 0 < topologicalKrullDim X)
    (A : Finset X) (hA : A.Nonempty) (hAcl : ∀ a ∈ A, IsClosed ({a} : Set X)) :
    ∃ Z : Set X, IsClosed Z ∧ IsIrreducible Z ∧ topologicalKrullDim Z = 1 ∧ (A : Set X) ⊆ Z := by
  classical
  haveI : AlgebraicGeometry.IsProjectiveVariety k f := hXp
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hbc, hab⟩ :=
    exists_isClosed_singleton_ne f ((WithBot.one_le_iff_pos _).mpr hX) (hAcl a ha)
  set A' := insert b A
  obtain ⟨U, hU, hAU⟩ := MMP.Resolution.exists_isAffineOpen_finite_subset f
    (Stacks.HProjective.isQuasiProjective_of_isHQuasiProjective f
      hXp.isProjective.isHQuasiProjective) A'.finite_toSet
  have hAcl' : ∀ x ∈ A', IsClosed ({x} : Set X) := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    exacts [hbc, hAcl x hx]
  let W : TopologicalSpace.IrreducibleCloseds X :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hfin : Order.height W ≠ ⊤ := by
    have h1 := Order.height_le_krullDim W
    have h2 := topologicalKrullDim_ne_top_of_locallyOfFiniteType k f
    intro h
    rw [h] at h1
    exact h2 (top_le_iff.mp h1)
  obtain ⟨C, hC, hAC⟩ := exists_curve_of_height_le f hU A' hAU hAcl' (Finset.mem_insert_self b A)
    (Finset.mem_insert_of_mem ha) hab.symm (Order.height W).toNat W
    (by rw [ENat.coe_toNat hfin]) (fun x _ => Set.mem_univ x)
  exact ⟨C, C.isClosed', C.isIrreducible', hC,
    (Finset.coe_subset.mpr (Finset.subset_insert b A)).trans hAC⟩

end MMP

end
