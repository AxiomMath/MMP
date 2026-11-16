module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancy
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
public import MMP.AlgebraicGeometry.Intersection.Nef
public import MMP.AlgebraicGeometry.MMP.Fourfold.BasepointFree.LcCentreNonvanishing
public import MMP.AlgebraicGeometry.MMP.BasepointFree.Basic
public import MMP.AlgebraicGeometry.Resolution.LogResolutionAmpleSubtraction
public import MMP.AlgebraicGeometry.Positivity.AmpleNefBig
public import MMP.AlgebraicGeometry.MMP.BasepointFree.RelativelyFreeTwist
public import MMP.AlgebraicGeometry.Vanishing.LcCentreUnionExtension
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
public import MMP.AlgebraicGeometry.Singularities.LocalGenerator
public import MMP.AlgebraicGeometry.Singularities.DivisorOver
public import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
public import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
public import MMP.AlgebraicGeometry.MMP.Abundance.Basic
public import MMP.AlgebraicGeometry.Modules.CurveFibreLineBundle
public import MMP.AlgebraicGeometry.MMP.Abundance.NumericalDimensionOnePencil
public import MMP.AlgebraicGeometry.Positivity.AmpleNumerical
public import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive
public import MMP.AlgebraicGeometry.Intersection.PairingSeparation
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafTensor
public import MMP.AlgebraicGeometry.Divisor.CartierLineBundle
public import MMP.AlgebraicGeometry.MMP.Threefold.Basic
public import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
public import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
public import MMP.AlgebraicGeometry.Positivity.Kleiman.AbsoluteCartier
public import MMP.AlgebraicGeometry.Positivity.CartierTwistEulerPolynomial
public import MMP.AlgebraicGeometry.Resolution.ProjectiveLogResolution
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyBoundaryChange
public import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
public import MMP.AlgebraicGeometry.Singularities.BoundaryLowering
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
public import MMP.AlgebraicGeometry.Curves.Maps.ScalarAutomorphisms
public import MMP.AlgebraicGeometry.Positivity.AmplePointConcentration
public import MMP.AlgebraicGeometry.Resolution.DivisorTupleRestrictionLift
public import MMP.AlgebraicGeometry.Singularities.LcCentreHighMultiplicity
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
public import MMP.AlgebraicGeometry.Positivity.RelativeAmplePullbackTwist
public import MMP.AlgebraicGeometry.Positivity.RelativeNefBigSurface
public import MMP.AlgebraicGeometry.Singularities.Bertini.GeneralMemberSNC
public import MMP.AlgebraicGeometry.MMP.Abundance.LogElliptic.GenericFibreDegree
public import MMP.AlgebraicGeometry.ChowForm.FibreKoszulBase
public import MMP.AlgebraicGeometry.Intersection.CurveCartierLocal
public import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
public import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
public import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy

/-!
# The basepoint-free theorem for projective lc fourfolds

Let `(X, B)` be a log canonical pair, with `B` a `ℚ`-divisor, on a normal projective complex
variety `X` of dimension four, and let `K` be a canonical divisor of `X`. Let `L` be a nef
Cartier divisor on `X` such that `aL - (K + B)` is ample for some rational `a > 0`. Then the
linear system `|mL|` is basepoint free for every sufficiently large integer `m`.

The proof shows that for a prime `p` the base locus of `|p^e L|` strictly shrinks while it is
nonempty: by nonvanishing along lc centres it contains no lc centre, and adding a multiple of
general members of `|p^e L|` at the log canonical threshold creates a new lc centre inside it.
Two free multiples `p^e L` and `q^f L` with `p ≠ q` primes then give freeness of `|mL|` for all
`m ≥ (p^e - 1) q^f`.

## Main results

* `MMP.Intersection.IsLogCanonicalPair.exists_isBasepointFree_nsmul`: the statement above.

## Implementation notes

* The lc condition is `MMP.Intersection.IsLogCanonicalPair`: it contains that `X` is a normal
  variety, that `B` is effective and that `K + B` is `ℚ`-Cartier. "Rational" means that `B` is a
  `ℚ`-divisor.
* Nefness of `L` is `MMP.Mori.Divisor.IsNef`, which includes that `L` is Cartier; ampleness of
  the `ℚ`-divisor `aL - (K + B)` is `MMP.Mori.QDivisor.IsAmple`.
* Basepoint freeness of `|mL|` is `MMP.Mori.Divisor.IsBasepointFree` of `m • L`, with `m : ℕ`.

## References

* [OpenAI, *Termination for projective log canonical fourfolds with rational boundary*][OAI4]
-/

@[expose] public section

section

namespace Proof_thm_mmp_projective_fourfold_lc_basepoint_free

open CategoryTheory AlgebraicGeometry Filter TopologicalSpace MonoidalCategory
open MMP.Mori (Divisor QDivisor DivisorOver)
open MMP.Intersection (IsLogCanonicalPair IsLogDiscrepancy)

open MMP.Mori in
private theorem isLcPair_of_isLogCanonicalPair {X : Scheme.{0}} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X}
    (hB : MMP.Intersection.IsLogCanonicalPair sX B) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) : IsLcPair sX n K B := by
  obtain ⟨⟨hX, n', K', hK', hQ'⟩, -, hlc⟩ := hB
  haveI : CompactSpace X := haveI := hX.1; QuasiCompact.compactSpace_of_compactSpace sX
  have hlin : K'.LinearlyEquivalent K :=
    MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX hX hK' hK
  have hP : IsPairWith sX n K B := ⟨hX, hK, hQ'.add_of_linearlyEquivalent hlin⟩
  refine ⟨hP, le_discrep_iff.mpr fun D a hD ha => ?_⟩
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  obtain ⟨⟨E, hEp⟩, hEv⟩ := MMP.Threefold.Bridges.exists_properDivisorOver_valuation_eq hX D
  obtain ⟨a', ha'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP.isPair hK E
  have haa : a' = a := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hP hEv ha' ha
  have h0 := hlc n _ _ (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy ha' hEp)
  simpa using EReal.coe_le_coe_iff.mpr (show (-1 : ℝ) ≤ a by rw [← haa]; linarith)

/-- The zero divisor `div σ + M` of a nonzero section of `𝒪_X(M)`, `M` Cartier, is Cartier. -/
private theorem isCartier_zeroDivisor {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {M : Divisor X} (hM : M.IsCartier) (σ : M.divisorialSubmodule ⊤)
    (hσ : σ ≠ 0) : (M.zeroDivisor σ hσ).IsCartier :=
  (MMP.Mori.Divisor.isCartier_principalDivisor _).add hM

section Setup

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  (sX : X ⟶ Spec (.of ℂ)) [QuasiCompact sX]

/-- The lc centres of `(X, B)`: the centres of the divisors over `X` of log discrepancy `0`. -/
private def lcCentres (B : QDivisor X) : Set (IrreducibleCloseds X) :=
  {Z | ∃ E : DivisorOver ℂ sX, IsLogDiscrepancy sX 4 (QDivisor.toRDivisor B) E 0 ∧ E.center = Z}

/-- An lc place, a divisor over `X` of log discrepancy `0` over `(X, B)`, has discrepancy `-1`. -/
private theorem isDiscrepancy_neg_one_of_isLogDiscrepancy_zero {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX 4) {B : QDivisor X} (hB : IsLogCanonicalPair sX B)
    {E : DivisorOver ℂ sX} (hE : IsLogDiscrepancy sX 4 (QDivisor.toRDivisor B) E 0) :
    MMP.Mori.IsDiscrepancy sX 4 K B E (-1) := by
  obtain ⟨b, hb⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy
    (isLcPair_of_isLogCanonicalPair hB hK).1.isPair hK E
  have h := MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy hb hE
  have hb1 : b = -1 := by exact_mod_cast (show ((b : ℚ) : ℝ) = -1 by linarith)
  exact hb1 ▸ hb

/-- A nonnegative rational multiple of a nef Cartier divisor is a nef `ℚ`-divisor. -/
private theorem isNef_smul_toQDivisor {L : Divisor X} (hL : L.IsNef ℂ sX) {t : ℚ} (ht : 0 ≤ t) :
    (t • Divisor.toQDivisor L).IsNef ℂ sX := by
  have hnum : 0 ≤ t.num := Rat.num_nonneg.mpr ht
  have hden : 0 < t.den := t.den_pos
  have hE : Divisor.toQDivisor (t.num.toNat • L) =
      ((t.den : ℕ) : ℤ) • (t • Divisor.toQDivisor L) := by
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
    congr 1
    push_cast
    rw [Rat.den_mul_eq_num]
    exact_mod_cast Int.toNat_of_nonneg hnum
  have hEc : (t.num.toNat • L).IsCartier := hL.1.nsmul _
  have hq : (t • Divisor.toQDivisor L).IsQCartier :=
    ⟨t.den, by exact_mod_cast hden.ne', by rw [← hE]; exact QDivisor.isCartierDivisor_toQDivisor.mpr hEc⟩
  refine ⟨hq, fun C i _ _ _ hC => ?_⟩
  rw [QDivisor.intersectionNumber_eq_of_smul ℂ sX i hC.le _ hq hden _ hEc hE,
    Divisor.degreeOn_nsmul' ℂ sX i hC.le L hL.1]
  have := hL.2 C i hC
  positivity

/-- A rational multiple of a `ℚ`-Cartier `ℚ`-divisor is `ℚ`-Cartier. -/
private theorem isQCartier_smul' {D : QDivisor X} (h : D.IsQCartier) (t : ℚ) :
    (t • D).IsQCartier := by
  obtain ⟨m, hm, D', hD', hc⟩ := h
  refine ⟨m * t.den, mul_ne_zero hm (by exact_mod_cast t.den_pos.ne'), t.num • D', ?_,
    hc.zsmul _⟩
  rw [map_zsmul, hD', ← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ,
    ← Int.cast_smul_eq_zsmul ℚ, smul_smul, smul_smul]
  congr 1
  push_cast
  rw [mul_assoc, Rat.den_mul_eq_num]
  ring

/-- An ample Cartier divisor is nef: it has positive degree on every proper curve. -/
private theorem isNef_of_isAmple {D : Divisor X} (hD : D.IsCartier) (h : D.IsAmple hD) :
    D.IsNef ℂ sX := by
  haveI := hD.isInvertibleModule_divisorialSheaf
  refine ⟨hD, fun C i _ _ _ hC => ?_⟩
  have h' : Scheme.Modules.IsAmple X D.divisorialSheaf :=
    (Stacks.AmpleBridge.isAmple_iff_isAmple X _).1 h
  exact (invertibleCurveDegree_pullback_pos_of_isAmple_of_isAffineHom ℂ (i ≫ sX) hC i _ h').le

/-- **Positive multiples of ample divisors are ample**: `pD ≡ D + (p - 1) D` with `D` nef. -/
private theorem isAmple_nsmul_of_isAmple (hX : MMP.Mori.IsProjectiveVariety ℂ sX) {D : Divisor X}
    (hD : D.IsCartier) (h : D.IsAmple hD) {p : ℕ} (hp : 0 < p) : (p • D).IsAmple (hD.nsmul p) := by
  haveI := hX
  have hN := isNef_smul_toQDivisor sX (isNef_of_isAmple sX hD h) (t := ((p - 1 : ℕ) : ℚ))
    (by positivity)
  refine MMP.Mori.QDivisor.isAmple_of_numericallyEquivalent_add_of_isNef sX
    ⟨1, one_pos, D, by simp, hD, h⟩ hN (MMP.Mori.QDivisor.NumericallyEquivalent.refl
      ((QDivisor.isQCartier_toQDivisor hD).add hN.1)) 1 one_pos (p • D) ?_ (hD.nsmul p)
  rw [map_nsmul, Nat.cast_one, one_smul, ← Nat.cast_smul_eq_nsmul ℚ]
  have : (p : ℚ) = 1 + ((p - 1 : ℕ) : ℚ) := by
    rw [Nat.cast_sub hp, Nat.cast_one]; ring
  rw [this, add_smul, one_smul]

/-- Ampleness of a Cartier divisor depends only on its linear equivalence class. -/
private theorem isAmple_of_linearlyEquivalent' {D D' : Divisor X} (hD : D.IsCartier)
    (h : D.IsAmple hD) (hD' : D'.IsCartier) (he : D'.LinearlyEquivalent D) : D'.IsAmple hD' := by
  haveI := hD.isInvertibleModule_divisorialSheaf
  haveI := hD'.isInvertibleModule_divisorialSheaf
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _ he.divisorialSheafIso).2 h

/-- **A positive multiple of an ample `ℚ`-divisor, moved by a principal `ℚ`-divisor, is
ample.** -/
private theorem isAmple_smul_add_principal (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    {A : QDivisor X} (hA : A.IsAmple) {s : ℚ} (hs : 0 < s) (t : ℚ)
    (φ : (MMP.Mori.RationalFunctions X)ˣ) :
    (s • A + t • Divisor.toQDivisor (MMP.Mori.principalDivisor φ)).IsAmple := by
  obtain ⟨m, hm, D, hD, hDc, hDamp⟩ := hA
  have hsn : 0 < s.num := Rat.num_pos.mpr hs
  set j : ℕ := s.num.toNat * t.den
  set P := MMP.Mori.principalDivisor φ
  set D' : Divisor X := j • D + ((m : ℤ) * s.den * t.num) • P
  have hD'c : D'.IsCartier :=
    (hDc.nsmul j).add ((MMP.Mori.Divisor.isCartier_principalDivisor φ).zsmul _)
  refine ⟨m * s.den * t.den, by positivity, D', ?_, hD'c, ?_⟩
  · have h1 : ((s.num.toNat : ℕ) : ℚ) = s.den * s := by
      rw [Rat.den_mul_eq_num]; exact_mod_cast Int.toNat_of_nonneg hsn.le
    have h2 : (((m : ℤ) * s.den * t.num : ℤ) : ℚ) = m * s.den * (t.den * t) := by
      rw [Rat.den_mul_eq_num]; push_cast; ring
    simp only [D', j, map_add, map_nsmul, map_zsmul, hD]
    rw [← Int.cast_smul_eq_zsmul ℚ, h2, ← Nat.cast_smul_eq_nsmul ℚ]
    push_cast
    rw [h1]
    module
  · have hj : 0 < j := Nat.mul_pos (by omega) t.den_pos
    refine isAmple_of_linearlyEquivalent' (hDc.nsmul j) (isAmple_nsmul_of_isAmple sX hX hDc hDamp hj)
      hD'c ?_
    rw [MMP.Mori.Divisor.linearlyEquivalent_iff_sub_mem_range]
    simp only [D', add_sub_cancel_left]
    exact AddSubgroup.zsmul_mem _ (AddMonoidHom.mem_range.mpr ⟨Additive.ofMul φ, rfl⟩) _

section GeneralMemberLc

open MMP.Mori MMP.Resolution

universe u

section Hironaka

variable {k : Type u} [Field k] {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}

variable {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- The support of the reduced divisor on a finite set of prime divisors is that set. -/
private theorem support_sum_single (s : Finset (MMP.Mori.PrimeDivisor Y)) :
    (∑ E ∈ s, Finsupp.single E (1 : ℤ) : Divisor Y).support = s := by
  classical
  ext E
  simp [Finsupp.finset_sum_apply, Finsupp.single_apply]

/-- A prime divisor whose generic point lies on finitely many prime divisors is one of them. -/
private theorem mem_of_genericPoint_mem_iUnion {Y : Scheme.{u}}
    {s : Finset (MMP.Mori.PrimeDivisor Y)} {C : Set Y}
    (hs : (⋃ E ∈ s, (E.support : Set Y)) = C) {F : MMP.Mori.PrimeDivisor Y}
    (hF : F.genericPoint ∈ C) : F ∈ s := by
  rw [← hs] at hF
  obtain ⟨E, hE, hgen⟩ := Set.mem_iUnion₂.mp hF
  rwa [MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hgen] at hE

/-- The exceptional prime divisors of a log resolution are finitely many. -/
private theorem exists_finset_isExceptional {D : RDivisor X} {Y : Scheme.{u}} {f : Y ⟶ X}
    (hf : MMP.Mori.IsLogResolution sX D f) :
    ∃ Ex : Finset (MMP.Mori.PrimeDivisor Y),
      ∀ F : MMP.Mori.PrimeDivisor Y, F ∈ Ex ↔ RationalMap.IsExceptional f.toRationalMap F := by
  classical
  have hmem : ∀ F : MMP.Mori.PrimeDivisor Y, RationalMap.IsExceptional f.toRationalMap F →
      F.genericPoint ∈ ((exceptionalSet f ⊔ D.supp.preimage f.continuous : Closeds Y) : Set Y) :=
    fun F hF => Or.inl (MMP.Positivity.support_subset_exceptionalSet F hF
      (MMP.Flips.primeDivisor_genericPoint_mem_support F))
  rcases hf.isSNCSubset with h0 | ⟨s, hs, -⟩
  · refine ⟨∅, fun F => ⟨fun h => absurd h (Finset.notMem_empty _), fun hF => ?_⟩⟩
    have := hmem F hF
    rw [h0] at this
    exact absurd this (by simp)
  · refine ⟨s.filter (fun F => RationalMap.IsExceptional f.toRationalMap F), fun F => ?_⟩
    rw [Finset.mem_filter]
    refine ⟨fun h => h.2, fun hF => ⟨?_, hF⟩⟩
    exact mem_of_genericPoint_mem_iUnion hs (hmem F hF)

end Hironaka

/-! ### Proper birational morphisms over prime divisors -/

section CodimOne

/-- Two points of `X` over the generic point of a prime divisor `Q` of the normal scheme `Y` are
equal, for `f : X ⟶ Y` separated, dominant and birational. -/
private theorem eq_of_map_eq_genericPoint {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) [IsSeparated f] [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) (Q : MMP.Mori.PrimeDivisor Y) {x₁ x₂ : X}
    (h₁ : f x₁ = Q.genericPoint) (h₂ : f x₂ = Q.genericPoint) : x₁ = x₂ := by
  have := Q.isDiscreteValuationRing_localRing
  haveI : ValuationRing (Y.presheaf.stalk (f x₁)) := by rw [h₁]; infer_instance
  haveI : ValuationRing (Y.presheaf.stalk (f x₂)) := by rw [h₂]; infer_instance
  haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing f hf x₁
  haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing f hf x₂
  exact MMP.Positivity.eq_of_isIso_stalkMap f hf (h₂.trans h₁.symm)

/-- A proper birational morphism onto a normal integral scheme is an isomorphism over every point
with finite fibre. -/
private theorem mem_biregularLocus_of_finite {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
    [IsNormal Z] (f : X ⟶ Z) [IsProper f] (hb : IsBirationalMorphism f) {z : Z}
    (hz : (f ⁻¹' {z}).Finite) : z ∈ biregularLocus f := by
  obtain ⟨hU, hiso⟩ := (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso f
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hb)).1 inferInstance
  exact le_biregularLocus (V := ⟨_, hU⟩) hiso hz

/-- A proper birational morphism onto a normal integral scheme is an isomorphism over the generic
point of every prime divisor. -/
private theorem genericPoint_mem_biregularLocus {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) [IsProper f]
    (hf : IsBirationalMorphism f) (P : MMP.Mori.PrimeDivisor Y) :
    P.genericPoint ∈ biregularLocus f :=
  haveI := hf.isDominant
  mem_biregularLocus_of_finite f hf (Set.Subsingleton.finite fun _ ha _ hb =>
    eq_of_map_eq_genericPoint f hf.functionFieldMap_bijective P ha hb)

variable {k : Type u} [Field k] [PerfectField k] {X W : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral W]

/-- **A non-exceptional prime divisor of a proper birational model is a strict transform.** If
`F` is a prime divisor of `W` which is not exceptional over `X`, then `π` maps the generic point
of `F` to that of a prime divisor `P` of `X`, `F = π⁻¹_* P`, and the discrepancy of `F` over a
pair `(X, Δ)` is `-coeff_P Δ`. -/
private theorem exists_inverseTransformPrimeDivisor_eq_some {n : ℕ} {K : Divisor X}
    {Δ : QDivisor X} (hP : IsPairWith sX n K Δ) {π : W ⟶ X} [IsProper π]
    (hW : IsNormalVariety k (π ≫ sX)) (hbir : IsBirationalMorphism π)
    (F : MMP.Mori.PrimeDivisor W) (hF : ¬ RationalMap.IsExceptional π.toRationalMap F) :
    ∃ P : MMP.Mori.PrimeDivisor X, π F.genericPoint = P.genericPoint ∧
      inverseTransformPrimeDivisor π P = some F ∧
      IsDiscrepancy sX n K Δ ⟨W, π, hW, hbir, F⟩ (-Δ.coeff P) := by
  obtain ⟨P, hc, hd⟩ := DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff hP
    ⟨W, π, hW, hbir, F⟩ hF
  have hη : π F.genericPoint = P.genericPoint := by
    rw [DivisorOver.center_eq_closure_genericPoint,
      AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hc
    exact (inseparable_iff_closure_eq.2 hc).eq
  refine ⟨P, hη, ?_, hd⟩
  exact MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hη
    (hη ▸ genericPoint_mem_biregularLocus π hbir P)

/-- The coefficient of `π⁻¹_* B` along `π⁻¹_* P` is the coefficient of `B` along `P`. -/
private theorem coeff_inverseTransformDivisor_of_eq_some {R : Type*} [AddCommMonoid R]
    {g : W ⟶ X} {P : MMP.Mori.PrimeDivisor X} {F : MMP.Mori.PrimeDivisor W}
    (hP : inverseTransformPrimeDivisor g P = some F) (B : DivisorWithCoeffs R X) :
    (inverseTransformDivisor g B).coeff F = B.coeff P :=
  MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hP (fun _ hP' =>
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective <|
      (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
        hP').1.symm.trans
      (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hP).1) B

/-- A strict transform `π⁻¹_* P` of a component `P` of `B` is a component of `π⁻¹_* B`. -/
private theorem mem_support_inverseTransformDivisor {π : W ⟶ X} {B : QDivisor X}
    {P : MMP.Mori.PrimeDivisor X} {F : MMP.Mori.PrimeDivisor W}
    (hinv : inverseTransformPrimeDivisor π P = some F) (hP : B.coeff P ≠ 0) :
    F ∈ (inverseTransformDivisor π B).support := by
  rw [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply,
    coeff_inverseTransformDivisor_of_eq_some hinv]
  exact hP

open Classical in
/-- **The snc boundary of a log resolution.** The snc divisor `Ex(π) ∪ π⁻¹ Supp B` of a log
resolution `π` of `(X, B)` is the union of finitely many prime divisors, each a component of
`π⁻¹_* B` or exceptional. -/
private theorem exists_finset_subset_support_union {n : ℕ} {K : Divisor X} {B : QDivisor X}
    (hPW : IsPairWith sX n K B) {π : W ⟶ X} [IsProper π] (hπ : MMP.Fourfold.IsLogResolution sX B π)
    (hW : IsNormalVariety k (π ≫ sX)) (hbir : IsBirationalMorphism π)
    (Ex : Finset (MMP.Mori.PrimeDivisor W))
    (hEx : ∀ F : MMP.Mori.PrimeDivisor W, F ∈ Ex ↔ RationalMap.IsExceptional π.toRationalMap F) :
    ∃ s : Finset (MMP.Mori.PrimeDivisor W), (⋃ E ∈ s, (E.support : Set W)) =
      ((exceptionalSet π ⊔ (QDivisor.toRDivisor B).supp.preimage π.continuous : Closeds W) :
        Set W) ∧ s ⊆ (inverseTransformDivisor π B).support ∪ Ex := by
  rcases hπ.isSNCSubset with h0 | ⟨s, hs, -⟩
  · exact ⟨∅, by rw [h0]; simp, Finset.empty_subset _⟩
  refine ⟨s, hs, fun E hE => ?_⟩
  by_cases hEE : E ∈ Ex
  · exact Finset.mem_union_right _ hEE
  obtain ⟨P, hη, hinv, -⟩ :=
    exists_inverseTransformPrimeDivisor_eq_some hPW hW hbir E (fun h => hEE ((hEx E).mpr h))
  refine Finset.mem_union_left _ (mem_support_inverseTransformDivisor hinv ?_)
  have hmem : E.genericPoint ∈ ((exceptionalSet π ⊔
      (QDivisor.toRDivisor B).supp.preimage π.continuous : Closeds W) : Set W) := by
    rw [← hs]
    exact Set.mem_iUnion₂.mpr ⟨E, hE, MMP.Flips.primeDivisor_genericPoint_mem_support E⟩
  rcases hmem with hx | hx
  · exfalso
    rw [SetLike.mem_coe, mem_exceptionalSet, hη] at hx
    exact hx (genericPoint_mem_biregularLocus π hbir P)
  · change π E.genericPoint ∈ (QDivisor.toRDivisor B).supp at hx
    rw [QDivisor.supp_toRDivisor, hη, DivisorWithCoeffs.mem_supp_iff] at hx
    obtain ⟨Q, hQ, hPQ⟩ := hx
    obtain rfl := MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hPQ
    exact hQ

end CodimOne

/-! ### Rescaling an integral divisor -/

section InvSmul

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {r : ℕ}

/-- An integral divisor `D` is `r • (D / r)`. -/
private theorem toQDivisor_eq_zsmul_inv_smul (hr : r ≠ 0) (D : Divisor X) :
    Divisor.toQDivisor D = (r : ℤ) • ((r : ℚ)⁻¹ • Divisor.toQDivisor D) := by
  rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul]
  push_cast
  rw [mul_inv_cancel₀ (by exact_mod_cast hr), one_smul]

private theorem coeff_inv_smul_toQDivisor (D : Divisor X) (P : MMP.Mori.PrimeDivisor X) :
    ((r : ℚ)⁻¹ • Divisor.toQDivisor D).coeff P = (r : ℚ)⁻¹ * D.coeff P := by
  rw [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor, smul_eq_mul]

/-- `D / r` is `ℚ`-Cartier for a Cartier divisor `D`. -/
private theorem isQCartier_inv_smul_toQDivisor (hr : r ≠ 0) {D : Divisor X} (hD : D.IsCartier) :
    ((r : ℚ)⁻¹ • Divisor.toQDivisor D).IsQCartier :=
  ⟨r, by exact_mod_cast hr, ⟨D, toQDivisor_eq_zsmul_inv_smul hr D, hD⟩⟩

private theorem inv_smul_toQDivisor_nonneg {D : Divisor X} (hD : 0 ≤ D) :
    0 ≤ (r : ℚ)⁻¹ • Divisor.toQDivisor D := fun P => by
  change (0 : ℚ) ≤ DivisorWithCoeffs.coeff ((r : ℚ)⁻¹ • Divisor.toQDivisor D) P
  rw [coeff_inv_smul_toQDivisor]
  have : (0 : ℚ) ≤ D.coeff P := by exact_mod_cast hD P
  positivity

/-- For `B ≥ 0` and `D ≥ 0`, the support of `B + D / r` is the union of the supports. -/
private theorem mem_supp_add_inv_smul_iff {B : QDivisor X} (hB : ∀ P, 0 ≤ B.coeff P)
    {D : Divisor X} (hD : 0 ≤ D) (hr : r ≠ 0) (x : X) :
    x ∈ (QDivisor.toRDivisor (B + (r : ℚ)⁻¹ • Divisor.toQDivisor D)).supp ↔
      x ∈ D.supp ∨ x ∈ (QDivisor.toRDivisor B).supp := by
  have hc : ∀ P, (B + (r : ℚ)⁻¹ • Divisor.toQDivisor D).coeff P ≠ 0 ↔
      D.coeff P ≠ 0 ∨ B.coeff P ≠ 0 := fun P => by
    have : (0 : ℚ) ≤ D.coeff P := by exact_mod_cast hD P
    rw [DivisorWithCoeffs.coeff_add, coeff_inv_smul_toQDivisor, ne_eq,
      add_eq_zero_iff_of_nonneg (hB P) (by positivity)]
    simp [hr]
    tauto
  simp only [QDivisor.supp_toRDivisor, DivisorWithCoeffs.mem_supp_iff, hc, or_and_right,
    exists_or]

end InvSmul

/-! ### Adding a general member to an lc pair -/

section LogCanonical

variable {k : Type u} [Field k] {X W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]

open Classical in
/-- The coefficient of the reduced divisor `∑_{E ∈ S} E` at `F` is `1` or `0`. -/
private theorem coeff_sum_single {Y : Scheme.{u}} (S : Finset (MMP.Mori.PrimeDivisor Y))
    (F : MMP.Mori.PrimeDivisor Y) :
    DivisorWithCoeffs.coeff (∑ E ∈ S, Finsupp.single E (1 : ℤ) : Divisor Y) F =
      if F ∈ S then 1 else 0 := by
  change (∑ E ∈ S, Finsupp.single E (1 : ℤ)) F = _
  rw [Finsupp.finset_sum_apply]
  simp [Finsupp.single_apply]

open Classical in
/-- **A general member keeps a pair log canonical** (Kollár–Mori, proof of 5.17). Let `(X, B)` be
an lc pair, `π : W ⟶ X` a log resolution of `(X, B)` with exceptional prime divisors `Ex`, and
`G` an effective Cartier divisor whose pull-back `H' = π^*G` is such that
`H' + ∑ π⁻¹_* B_j + ∑ E_i` is a reduced snc divisor. Then `(X, B + G / r)` is lc for every
integer `r > 0`. -/
private theorem isLogCanonicalPair_add_inv_smul [IsLocallyNoetherian W] [IsNormal W]
    {B : QDivisor X} (hBp : MMP.Fourfold.IsPair sX B)
    (hB : MMP.Intersection.IsLogCanonicalPair sX B) {π : W ⟶ X}
    (hπ : MMP.Fourfold.IsLogResolution sX B π) (Ex : Finset (MMP.Mori.PrimeDivisor W))
    (hEx : ∀ F : MMP.Mori.PrimeDivisor W, F ∈ Ex ↔ RationalMap.IsExceptional π.toRationalMap F)
    {G : Divisor X} (hG0 : 0 ≤ G) (hGc : G.IsCartier)
    {hBG : ∀ Z : irreducibleComponents W, π (componentGenericPoint W Z) ∉ G.supp}
    {H' : Divisor W} (hH' : G.IsPullback π hBG H')
    (hcoef : ∀ F : MMP.Mori.PrimeDivisor W,
      (H' + ∑ F ∈ (inverseTransformDivisor π B).support ∪ Ex,
        Finsupp.single F (1 : ℤ)).coeff F = 0 ∨
      (H' + ∑ F ∈ (inverseTransformDivisor π B).support ∪ Ex,
        Finsupp.single F (1 : ℤ)).coeff F = 1)
    (hsnc : DivisorWithCoeffs.IsSNC (π ≫ sX)
      (H' + ∑ F ∈ (inverseTransformDivisor π B).support ∪ Ex, Finsupp.single F (1 : ℤ)))
    {r : ℕ} (hr : 0 < r) :
    MMP.Intersection.IsLogCanonicalPair sX (B + (r : ℚ)⁻¹ • Divisor.toQDivisor G) := by
  haveI : IsAlgClosed k := hBp.isAlgClosed
  haveI : CharZero k := hBp.charZero
  obtain ⟨hXn, n, K, hK, hKq⟩ := hB.1
  have hPW : IsPairWith sX n K B := ⟨hXn, hK, hKq⟩
  set A : QDivisor X := (r : ℚ)⁻¹ • Divisor.toQDivisor G
  have hAq : A.IsQCartier := isQCartier_inv_smul_toQDivisor hr.ne' hGc
  -- the log resolution and its source
  have hbir : IsBirationalMorphism π := hπ.isBirationalMorphism
  have hW : IsNormalVariety k (π ≫ sX) :=
    (hπ.toIsSmoothResolution.isNormalVariety hXn).1
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : IsDominant π := hbir.isDominant
  haveI : IsProper π := hπ.toIsSmoothResolution.isProper
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace π
  -- the crepant boundary of `(X, B)` and the pull-back of `A`
  obtain ⟨BW, hBW, -⟩ := (MMP.Mori.IsPair.existsUnique_isCrepantBoundary hB.1 hK π hW hbir).1
  have hle1 : ∀ F, BW.coeff F ≤ 1 :=
    (MMP.Fourfold.isLogCanonicalPair_iff_forall_coeff_le_one sX hBp hπ hW hBW).mp hB
  have hBA : ∀ Z : irreducibleComponents W, π (componentGenericPoint W Z) ∉ A.supp := by
    intro Z
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, map_genericPoint_of_isDominant]
    exact MMP.Fourfold.genericPoint_notMem_supp A
  set B' := A.pullback hAq hBA with hB'def
  have hB' : A.IsPullback π hBA B' := QDivisor.isPullback_pullback hAq hBA
  have hB'H : ∀ F, B'.coeff F = (r : ℚ)⁻¹ * H'.coeff F := by
    obtain ⟨D', hD', hpD'⟩ := hB' r hr G (toQDivisor_eq_zsmul_inv_smul hr.ne' G) hGc
    obtain rfl := hpD'.eq hGc hH'
    intro F
    have := congrArg (fun E : QDivisor W => E.coeff F) hD'
    simp only [DivisorWithCoeffs.coeff_smul, zsmul_eq_mul, Divisor.coeff_toQDivisor] at this
    rw [this]
    push_cast
    field_simp
  -- the crepant boundary of `(X, B + A)`
  have hBW' : IsCrepantBoundary sX n K (B + A) π hW hbir (BW + B') := by
    intro F
    obtain ⟨-, hB'', hiff⟩ := IsPairWith.isDiscrepancy_add_smul_iff hPW hAq ⟨W, π, hW, hbir, F⟩
    have h := ((hiff B' hB').1 (-BW.coeff F)).mpr (hBW F)
    convert h using 1
    rw [DivisorWithCoeffs.coeff_add]
    ring
  -- `(X, B + A)` is a pair
  have hpairBA : MMP.Fourfold.IsPair sX (B + A) := by
    refine ⟨hBp.isAlgClosed, hBp.charZero, ⟨hXn, n, K, hK, add_assoc _ B A ▸ hKq.add hAq⟩,
      fun P => ?_⟩
    rw [DivisorWithCoeffs.coeff_add]
    exact add_nonneg (hBp.nonneg P) (inv_smul_toQDivisor_nonneg hG0 P)
  set S₀ := (inverseTransformDivisor π B).support ∪ Ex with hS₀
  -- the coefficients of `H'`
  have hH'0 : ∀ F, 0 ≤ H'.coeff F := fun F =>
    MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn (V := ⊤) hGc (fun P _ => hG0 P) hH'
      F ⟨F.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support F, trivial⟩
  have hH'01 : ∀ F, H'.coeff F = 0 ∨ (H'.coeff F = 1 ∧ F ∉ S₀) := by
    intro F
    have h := hcoef F
    rw [DivisorWithCoeffs.coeff_add, coeff_sum_single] at h
    have h0 := hH'0 F
    split_ifs at h with hF
    · left; omega
    · rcases h with h | h
      · left; omega
      · right; exact ⟨by omega, hF⟩
  -- off the snc boundary, the crepant boundary of `(X, B)` vanishes
  have hzero : ∀ F, F ∉ S₀ → BW.coeff F = 0 := by
    intro F hF
    obtain ⟨P, -, hinv, hd⟩ := exists_inverseTransformPrimeDivisor_eq_some hPW hW hbir F
      fun h => hF (Finset.mem_union_right _ ((hEx F).mpr h))
    rw [show BW.coeff F = B.coeff P by linarith [(hBW F).eq hd]]
    by_contra hP
    exact hF (Finset.mem_union_left _ (mem_support_inverseTransformDivisor hinv hP))
  -- `π` is a log resolution of `(X, B + A)`
  obtain ⟨s, hs, hsS₀⟩ := exists_finset_subset_support_union hPW hπ hW hbir Ex hEx
  have hsuppH' : (H'.supp : Set W) = π ⁻¹' (G.supp : Set X) :=
    MMP.Flips.supp_eq_preimage_supp_of_isPullback hGc hG0 hH'
  have hSNCsub : IsSNCSubset (π ≫ sX)
      (exceptionalSet π ⊔ (QDivisor.toRDivisor (B + A)).supp.preimage π.continuous) := by
    refine Or.inr ⟨H'.support ∪ s, ?_, ?_⟩
    · rw [Finset.set_biUnion_union, hs, ← DivisorWithCoeffs.coe_supp, hsuppH']
      ext x
      simp only [Closeds.coe_sup, Set.mem_union, Set.mem_preimage, SetLike.mem_coe]
      change π x ∈ G.supp ∨ x ∈ exceptionalSet π ∨ π x ∈ (QDivisor.toRDivisor B).supp ↔
        x ∈ exceptionalSet π ∨ π x ∈ (QDivisor.toRDivisor (B + A)).supp
      rw [mem_supp_add_inv_smul_iff hBp.nonneg hG0 hr.ne']
      tauto
    · refine hsnc.of_support_subset ?_
      rw [support_sum_single]
      intro F hF
      rw [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply,
        DivisorWithCoeffs.coeff_add, coeff_sum_single]
      rcases Finset.mem_union.mp hF with hF | hF
      · have hF' : H'.coeff F ≠ 0 := by
          rwa [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply] at hF
        rcases hH'01 F with h | ⟨h, hFS⟩
        · exact absurd h hF'
        · rw [if_neg hFS, h]; norm_num
      · rw [if_pos (hsS₀ hF)]
        have := hH'0 F
        omega
  have hπ' : MMP.Fourfold.IsLogResolution sX (B + A) π :=
    ⟨⟨hπ.toIsSmoothResolution, hπ.isPureCodimOne_exceptionalSet, hSNCsub⟩,
      hπ.isProjectiveMorphism⟩
  refine (MMP.Fourfold.isLogCanonicalPair_iff_forall_coeff_le_one sX hpairBA hπ' hW hBW').mpr fun F => ?_
  rw [DivisorWithCoeffs.coeff_add, hB'H]
  rcases hH'01 F with h | ⟨h, hFS⟩
  · rw [h]
    simpa using hle1 F
  · rw [h, hzero F hFS]
    push_cast
    rw [zero_add, mul_one]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast hr)

end LogCanonical

end GeneralMemberLc

/-- **Restricting sections to an open subscheme.** For a Cartier `M` and a dense open `U`, the
divisorial sections of `𝒪_X(M)` restrict to those of `𝒪_U(M|_U)`, compatibly with the scalars,
and the zero divisor of the restriction is the restriction of the zero divisor. -/
private theorem exists_restrict_sections {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] (U : X.Opens) [Nonempty U] [IsIntegral U]
    [IsLocallyNoetherian U] [IsNormal U] [CompactSpace U] [IsDominant U.ι]
    {M : Divisor X} (hMc : M.IsCartier) :
    ∃ ρ : M.divisorialSubmodule ⊤ →+
        MMP.Mori.Divisor.divisorialSubmodule (M.restrictOpen U) ⊤,
      (∀ (r : Γ(X, ⊤)) (s : M.divisorialSubmodule ⊤), ρ (r • s) = U.ι.appTop r • ρ s) ∧
      ∀ (s : M.divisorialSubmodule ⊤) (hs : s ≠ 0), ∃ h : ρ s ≠ 0,
        MMP.Mori.Divisor.zeroDivisor (M.restrictOpen U) (ρ s) h =
          (M.zeroDivisor s hs).restrictOpen U := by
  have hM' := MMP.Flips.isPullback_restrictOpen U hMc
  refine ⟨MMP.Mori.pullSec U.ι hMc hM', fun r s => MMP.Mori.pullSec_smul U.ι hMc hM' r s,
    fun s hs => ?_⟩
  have hZc := isCartier_zeroDivisor hMc s hs
  obtain ⟨h, hpb⟩ := MMP.Mori.isPullback_zeroDivisor_pullSec U.ι hMc hM' s hs
    (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant U.ι _)
  exact ⟨h, hpb.eq hZc (MMP.Flips.isPullback_restrictOpen U hZc)⟩

/-- A non-exceptional divisor over a pair has discrepancy minus the coefficient of the prime
divisor of `X` with the same valuation. -/
private theorem exists_coeff_eq_of_not_isExceptional {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} {n : ℕ} {K : Divisor Y}
    {Δ : QDivisor Y} (hP : MMP.Mori.IsPairWith sY n K Δ) {D : DivisorOver ℂ sY}
    (hD : ¬ D.IsExceptional) {a : ℚ} (ha : MMP.Mori.IsDiscrepancy sY n K Δ D a) :
    ∃ P : MMP.Mori.PrimeDivisor Y, a = -Δ.coeff P := by
  obtain ⟨P, hv⟩ := MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hP.1 D hD
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP.isPair hP.2.1
    (DivisorOver.ofPrimeDivisor ℂ hP.1 P)
  refine ⟨P, ?_⟩
  rw [MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hP hv ha hc]
  exact MMP.Mori.IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hP.1 hc

/-- The coefficients of the boundary of an lc pair are at most one. -/
private theorem coeff_le_one_of_isLogCanonicalPair' {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} {n : ℕ} {K : Divisor Y}
    {Δ : QDivisor Y} (hP : MMP.Mori.IsPairWith sY n K Δ) (hlc : IsLogCanonicalPair sY Δ)
    (P : MMP.Mori.PrimeDivisor Y) : Δ.coeff P ≤ 1 := by
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP.isPair hP.2.1
    (DivisorOver.ofPrimeDivisor ℂ hP.1 P)
  have h0 := hlc.2.2 n _ _ (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc
    (show IsProper (𝟙 Y) from inferInstance))
  rw [MMP.Mori.IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hP.1 hc] at h0
  have : ((Δ.coeff P : ℚ) : ℝ) ≤ 1 := by push_cast at h0; linarith
  exact_mod_cast this

/-- **Log canonical pairs restrict to open subschemes.** -/
private theorem isLogCanonicalPair_restrictOpen' {B : QDivisor X} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX 4) (hB : IsLogCanonicalPair sX B) (U : X.Opens) [Nonempty U] :
    IsLogCanonicalPair (U.ι ≫ sX) (B.restrictOpen U) := by
  have hlc := isLcPair_of_isLogCanonicalPair hB hK
  have hPU := hlc.1.restrictOpen U
  refine ⟨hPU.isPair, fun P => hB.2.1 _, fun n' D a ha => ?_⟩
  have hn' : n' = 4 := by
    have h1 := MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha
    rw [hPU.2.1.topologicalKrullDim_eq] at h1
    exact_mod_cast h1.symm
  subst hn'
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPU.isPair hPU.2.1 D
  rw [MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy hc ha]
  suffices hc1 : (-1 : ℚ) ≤ c by
    have : (-1 : ℝ) ≤ c := by exact_mod_cast hc1
    linarith
  by_cases hD : D.IsExceptional
  · obtain ⟨D₁, hE₁, -, -, hb⟩ := hlc.1.exists_isDiscrepancy_of_restrictOpen U hD hc
    have h2 := hlc.2.trans (MMP.Mori.discrep_le hE₁ hb)
    have : ((-1 : ℝ) : EReal) ≤ ((c : ℝ) : EReal) := by simpa using h2
    exact_mod_cast EReal.coe_le_coe_iff.mp this
  · obtain ⟨P, hP⟩ := exists_coeff_eq_of_not_isExceptional hPU hD hc
    rw [hP, MMP.Mori.DivisorWithCoeffs.coeff_restrictOpen]
    linarith [coeff_le_one_of_isLogCanonicalPair' hlc.1 hB
      (OpenWeilRestriction.primeDivisorMap U.ι P)]

/-- Log canonicity on an open subscheme bounds the log discrepancies of the divisors over `X`
whose centre meets it. -/
private theorem nonneg_of_isLogDiscrepancy_of_restrictOpen {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {n : ℕ} {K : Divisor X}
    {Δ : QDivisor X} (hP : MMP.Mori.IsPairWith sX n K Δ) (U : X.Opens) [Nonempty U]
    (hlc : IsLogCanonicalPair (U.ι ≫ sX) (Δ.restrictOpen U)) {E : DivisorOver ℂ sX}
    (hE : ((E.center : Set X) ∩ U).Nonempty) {t : ℝ}
    (ht : IsLogDiscrepancy sX n (QDivisor.toRDivisor Δ) E t) : 0 ≤ t := by
  obtain ⟨b, hb⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP.isPair hP.2.1 E
  rw [MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy hb ht]
  obtain ⟨hY, hf, E', -, -, hiff⟩ := DivisorOver.exists_restrict_isDiscrepancy_iff hP E U hE
  haveI : IsProper E.f := ht.2.1
  have hb' := (hiff b).1 hb
  have hl := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hb'
    (inferInstance : IsProper (E.f ∣_ U))
  exact hlc.2.2 n _ _ hl

/-- **Bertini off a closed subset.** For an lc pair `(X, B)` and finitely many sections of a
Cartier `𝒪_X(M)` without common zero off a closed `W`, a general member `H` of their span makes
`(X, B + H/ρ)` lc outside `W` for every `ρ > 0`; in particular the general section is nonzero. -/
private theorem exists_polynomial_lc_off (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4) {B : QDivisor X}
    (hB : IsLogCanonicalPair sX B) (W : Set X) (hW : IsClosed W) (hWu : W ≠ Set.univ)
    {M : Divisor X} (hMc : M.IsCartier) {ι : Type} [Fintype ι] (s : ι → M.divisorialSubmodule ⊤)
    (hs : ∀ y : X, y ∉ W → ∃ (i : ι) (hi : s i ≠ 0), y ∉ (M.zeroDivisor (s i) hi).supp) :
    ∃ Q : MvPolynomial ι ℂ, Q ≠ 0 ∧ ∀ c : ι → ℂ, MvPolynomial.eval c Q ≠ 0 →
      ∃ hσ : (∑ i, MMP.Mori.scalarsToGlobalSections ℂ sX (c i) • s i) ≠ 0,
      ∀ ρ : ℕ, 0 < ρ → ∀ (E : DivisorOver ℂ sX) (t : ℝ), ¬ (E.center : Set X) ⊆ W →
        IsLogDiscrepancy sX 4 (QDivisor.toRDivisor (B + (ρ : ℚ)⁻¹ •
          Divisor.toQDivisor (M.zeroDivisor _ hσ))) E t → 0 ≤ t := by
  classical
  set U : X.Opens := ⟨Wᶜ, hW.isOpen_compl⟩ with hUdef
  obtain ⟨y₀, hy₀⟩ : ∃ y, y ∉ W := by
    by_contra h
    push Not at h
    exact hWu (Set.eq_univ_iff_forall.2 h)
  haveI : Nonempty U := ⟨⟨y₀, hy₀⟩⟩
  have hXn : MMP.Mori.IsNormalVariety ℂ sX := hB.1.1
  have hUn : MMP.Mori.IsNormalVariety ℂ (U.ι ≫ sX) := hXn.restrictOpen U
  haveI : IsDominant U.ι := AlgebraicGeometry.Opens.isDominant_ι (U.isOpen.dense ⟨y₀, hy₀⟩)
  haveI : IsIntegral U := hUn.1.toIsIntegral
  haveI : IsLocallyNoetherian U := hUn.isLocallyNoetherian
  haveI : IsNormal U := hUn.2
  haveI : CompactSpace U := haveI := hUn.1.toQuasiCompact
    QuasiCompact.compactSpace_of_compactSpace (U.ι ≫ sX)
  -- the sections on `U`
  obtain ⟨ρU, hρs, hρz⟩ := exists_restrict_sections U hMc
  set t : ι → MMP.Mori.Divisor.divisorialSubmodule (M.restrictOpen U) ⊤ := fun i => ρU (s i)
  have ht : ∀ x : U, ∃ (i : ι) (hi : t i ≠ 0),
      x ∉ (MMP.Mori.Divisor.zeroDivisor (M.restrictOpen U) (t i) hi).supp := by
    intro x
    obtain ⟨i, hi, hx⟩ := hs (U.ι x) x.2
    obtain ⟨h, heq⟩ := hρz (s i) hi
    refine ⟨i, h, fun hmem => hx ?_⟩
    have hmem' : x ∈ ((M.zeroDivisor (s i) hi).restrictOpen U).supp := heq ▸ hmem
    obtain ⟨P, hP, hxP⟩ := MMP.Mori.DivisorWithCoeffs.mem_supp_iff.1 hmem'
    exact MMP.Mori.DivisorWithCoeffs.mem_supp_iff.2 ⟨_, hP,
      (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff U.ι P x).2 hxP⟩
  -- the pair on `U` and a log resolution of it
  set BU := B.restrictOpen U
  have hBU : IsLogCanonicalPair (U.ι ≫ sX) BU := isLogCanonicalPair_restrictOpen' sX hK hB U
  have hBUp : MMP.Fourfold.IsPair (U.ι ≫ sX) BU := ⟨inferInstance, inferInstance, hBU.1, hBU.2.1⟩
  obtain ⟨Y, π, hπ, hπp⟩ := MMP.Mori.exists_isLogResolution_isProjectiveMorphism (U.ι ≫ sX) hUn
    (QDivisor.toRDivisor BU)
  obtain ⟨Ex, hEx⟩ := exists_finset_isExceptional hπ
  have hYn : MMP.Mori.IsNormalVariety ℂ (π ≫ U.ι ≫ sX) :=
    (hπ.toIsSmoothResolution.isNormalVariety hUn).1
  haveI : IsLocallyNoetherian Y := hYn.isLocallyNoetherian
  haveI : IsNormal Y := hYn.2
  obtain ⟨Q, hQ0, hQ⟩ :=
    MMP.Mori.IsLogResolution.exists_polynomial_isSNC_pullback_zeroDivisor_add' hBU.1 hπ Ex hEx t ht
  refine ⟨Q, hQ0, fun c hc => ?_⟩
  obtain ⟨hσU, hBG, H', hH', hcoef, hsnc, -⟩ := hQ c hc
  set σ := ∑ i, MMP.Mori.scalarsToGlobalSections ℂ sX (c i) • s i with hσdef
  have hρσ : ρU σ = ∑ i, MMP.Mori.scalarsToGlobalSections ℂ (U.ι ≫ sX) (c i) • t i := by
    rw [hσdef, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hρs]; rfl
  have hσ : σ ≠ 0 := fun h => hσU (by rw [← hρσ, h, map_zero])
  refine ⟨hσ, fun ρ hρ E t' hE ht' => ?_⟩
  obtain ⟨h0, hzero⟩ := hρz σ hσ
  have hzcongr : ∀ {a b : MMP.Mori.Divisor.divisorialSubmodule (M.restrictOpen U) ⊤} (e : a = b)
      (ha : a ≠ 0) (hb : b ≠ 0), MMP.Mori.Divisor.zeroDivisor (M.restrictOpen U) a ha =
        MMP.Mori.Divisor.zeroDivisor (M.restrictOpen U) b hb := by
    intro a b e ha hb; subst e; rfl
  have hG : MMP.Mori.Divisor.zeroDivisor (M.restrictOpen U) _ hσU =
      (M.zeroDivisor σ hσ).restrictOpen U := (hzcongr hρσ.symm hσU h0).trans hzero
  have hMUc : MMP.Mori.Divisor.IsCartier (M.restrictOpen U) :=
    MMP.Fourfold.isCartier_of_isPullback U.ι hMc (MMP.Flips.isPullback_restrictOpen U hMc)
  have hlcU := isLogCanonicalPair_add_inv_smul hBUp hBU ⟨hπ, hπp⟩ Ex hEx
    (MMP.Mori.Divisor.zeroDivisor_nonneg _ _ hσU)
    (isCartier_zeroDivisor hMUc _ hσU)
    hH' hcoef hsnc hρ
  rw [hG] at hlcU
  have hres : BU + (ρ : ℚ)⁻¹ • Divisor.toQDivisor ((M.zeroDivisor σ hσ).restrictOpen U) =
      (B + (ρ : ℚ)⁻¹ • Divisor.toQDivisor (M.zeroDivisor σ hσ)).restrictOpen U := by
    ext P
    rfl
  rw [hres] at hlcU
  have hlc := isLcPair_of_isLogCanonicalPair hB hK
  have hHc := isCartier_zeroDivisor hMc σ hσ
  have hPW : MMP.Mori.IsPairWith sX 4 K (B + (ρ : ℚ)⁻¹ • Divisor.toQDivisor (M.zeroDivisor σ hσ)) :=
    ⟨hXn, hK, by rw [← add_assoc]; exact hlc.1.2.2.add (isQCartier_smul'
      (MMP.Mori.QDivisor.isQCartier_toQDivisor hHc) _)⟩
  exact nonneg_of_isLogDiscrepancy_of_restrictOpen hPW U hlcU (Set.not_subset.1 hE) ht'

/-- If the pull-back of an effective `ℚ`-Cartier `G` along a proper birational `π` has positive
coefficient along a prime divisor `F`, then the centre of `F` lies in `Supp G`. -/
private theorem centre_subset_supp_of_pos {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {π : Y ⟶ X}
    (hY : MMP.Mori.IsNormalVariety ℂ (π ≫ sX)) (hbir : MMP.Mori.IsBirationalMorphism π)
    {G : QDivisor X} (hGq : G.IsQCartier)
    (hGsupp : ∀ Z : irreducibleComponents Y, π (MMP.Mori.componentGenericPoint Y Z) ∉ G.supp)
    {Gπ : QDivisor Y} (hGπ : G.IsPullback π hGsupp Gπ) (F : MMP.Mori.PrimeDivisor Y)
    (hF : 0 < Gπ.coeff F) :
    ((⟨Y, π, hY, hbir, F⟩ : DivisorOver ℂ sX).center : Set X) ⊆ (G.supp : Set X) := by
  rw [DivisorOver.center_eq_closure_genericPoint]
  refine closure_minimal ?_ (G.supp).isClosed
  rintro _ rfl
  obtain ⟨m, hm, D, hD, hDc⟩ := hGq.exists_pos
  obtain ⟨D', hD', hpb⟩ := hGπ m hm D hD hDc
  have hFD' : F.genericPoint ∈ (D'.supp : Set Y) := by
    refine MMP.Mori.DivisorWithCoeffs.mem_supp_iff.mpr ⟨F, fun h0 => ?_, ?_⟩
    · have := congrArg (fun Q : QDivisor Y => Q.coeff F) hD'
      simp only [Divisor.coeff_toQDivisor, h0, MMP.Mori.DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at this
      push_cast at this
      have hm' : (0 : ℚ) < m := by exact_mod_cast hm
      nlinarith
    · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  have := MMP.Flips.supp_subset_preimage_supp_of_isPullback hDc hpb hFD'
  rw [Set.mem_preimage, QDivisor.supp_eq_of_toQDivisor_eq (by exact_mod_cast hm.ne') hD] at this
  exact this

/-- **The log canonical threshold of a boundary concentrated on a closed set.** For an lc pair
`(X, B)` and an effective `ℚ`-Cartier `G` containing no lc centre, with `(X, B + G)` lc outside a
subset `W` but not lc, the log canonical threshold `c` of `G` is rational with `0 < c < 1`, and
`(X, B + cG)` has an lc centre contained in `W`. -/
private theorem exists_lct_lt_one
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4)
    {B : QDivisor X} (hB : IsLogCanonicalPair sX B) {W : Set X}
    {G : QDivisor X} (hG0 : ∀ P, 0 ≤ G.coeff P) (hGq : G.IsQCartier)
    (hGc : ∀ Z ∈ lcCentres sX B, ¬ (Z : Set X) ⊆ (G.supp : Set X))
    (hGW : ∀ (E : DivisorOver ℂ sX) (r : ℝ), ¬ (E.center : Set X) ⊆ W →
        IsLogDiscrepancy sX 4 (QDivisor.toRDivisor (B + G)) E r → 0 ≤ r)
    (hGnlc : ¬ IsLogCanonicalPair sX (B + G)) :
    ∃ c : ℚ, 0 < c ∧ c < 1 ∧ IsLogCanonicalPair sX (B + c • G) ∧
      ∃ E : DivisorOver ℂ sX, IsLogDiscrepancy sX 4 (QDivisor.toRDivisor (B + c • G)) E 0 ∧
        (E.center : Set X) ⊆ W := by
  haveI := hX
  have hlc := isLcPair_of_isLogCanonicalPair hB hK
  have hPW := hlc.1
  have hXn : MMP.Mori.IsNormalVariety ℂ sX := hPW.1
  obtain ⟨Y, π, hπ, hπp⟩ := MMP.Mori.exists_isLogResolution_isProjectiveMorphism sX hXn
    (QDivisor.toRDivisor (B + G))
  obtain ⟨hY, -, -⟩ := MMP.Mori.IsSmoothResolution.isNormalVariety hXn hπ.toIsSmoothResolution
  have hbir := hπ.isBirationalMorphism
  haveI := hπ.isProper
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : IsNormal Y := hY.2
  haveI : IsLocallyNoetherian Y :=
    haveI := hY.1.toLocallyOfFiniteType; LocallyOfFiniteType.isLocallyNoetherian (π ≫ sX)
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace π
  haveI : IsDominant π := hbir.isDominant
  -- the crepant boundary of `(X, B)` and the pull-back of `G`
  obtain ⟨⟨B₀, hB₀, -⟩, -⟩ := MMP.Mori.IsPair.existsUnique_isCrepantBoundary hPW.isPair hK π hY hbir
  have hGsupp : ∀ Z : irreducibleComponents Y, π (MMP.Mori.componentGenericPoint Y Z) ∉ G.supp := by
    intro Z
    obtain ⟨m, hm, D, hD, -⟩ := hGq.exists_pos
    rw [← QDivisor.supp_eq_of_toQDivisor_eq (by exact_mod_cast hm.ne') hD]
    exact MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant π D Z
  obtain ⟨Gπ, hGπ, -⟩ := hGq.existsUnique_isPullback (f := π) hGsupp
  set E : MMP.Mori.PrimeDivisor Y → DivisorOver ℂ sX := fun F => ⟨Y, π, hY, hbir, F⟩
  -- the discrepancies of `(X, B + tG)` along the prime divisors of `Y` are affine in `t`
  have hdisc : ∀ (t : ℚ) (F : MMP.Mori.PrimeDivisor Y),
      MMP.Mori.IsDiscrepancy sX 4 K (B + t • G) (E F) (-B₀.coeff F - t * Gπ.coeff F) := by
    intro t F
    obtain ⟨-, hB', h⟩ := hPW.isDiscrepancy_add_smul_iff hGq (E F)
    exact ((h Gπ hGπ).2 t (-B₀.coeff F)).2 (hB₀ F)
  have hlog : ∀ (t : ℚ) (F : MMP.Mori.PrimeDivisor Y),
      IsLogDiscrepancy sX 4 (QDivisor.toRDivisor (B + t • G)) (E F)
        (((1 - B₀.coeff F - t * Gπ.coeff F : ℚ) : ℝ)) := by
    intro t F
    have := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy (hdisc t F) hπ.isProper
    convert this using 2; push_cast; ring
  -- `(X, B)` is lc and `(X, B + G)` is lc outside `W`
  have hd1 : ∀ F, B₀.coeff F ≤ 1 := by
    intro F
    have := hB.2.2 4 (E F) _ (by simpa using hlog 0 F)
    have : (0 : ℝ) ≤ ((1 - B₀.coeff F : ℚ) : ℝ) := by simpa using this
    exact_mod_cast (sub_nonneg.mp (by exact_mod_cast this))
  have hcentre : ∀ F, ¬ ((E F).center : Set X) ⊆ W → B₀.coeff F + Gπ.coeff F ≤ 1 := by
    intro F hF
    have := hGW (E F) _ hF (by simpa using hlog 1 F)
    have : (0 : ℝ) ≤ ((1 - B₀.coeff F - Gπ.coeff F : ℚ) : ℝ) := by simpa using this
    have := (show (0 : ℚ) ≤ 1 - B₀.coeff F - Gπ.coeff F by exact_mod_cast this)
    linarith
  -- the crepant boundaries and the log canonical criterion on `Y`
  have hcrep : ∀ t : ℚ, MMP.Mori.IsCrepantBoundary sX 4 K (B + t • G) π hY hbir (B₀ + t • Gπ) := by
    intro t F
    convert hdisc t F using 1
    simp only [MMP.Mori.DivisorWithCoeffs.coeff_add, MMP.Mori.DivisorWithCoeffs.coeff_smul,
      smul_eq_mul]
    ring
  have hres : ∀ t : ℚ, 0 < t →
      MMP.Fourfold.IsLogResolution sX (B + t • G) π := by
    intro t ht
    have hsupp : (QDivisor.toRDivisor (B + t • G)).supp = (QDivisor.toRDivisor (B + G)).supp := by
      ext x
      simp only [SetLike.mem_coe, MMP.Mori.DivisorWithCoeffs.mem_supp_iff]
      refine exists_congr fun P => and_congr_left fun _ => ?_
      have h1 := hB.2.1 P
      have h2 := hG0 P
      rw [QDivisor.coeff_toRDivisor, QDivisor.coeff_toRDivisor, MMP.Mori.DivisorWithCoeffs.coeff_add,
        MMP.Mori.DivisorWithCoeffs.coeff_add, MMP.Mori.DivisorWithCoeffs.coeff_smul, smul_eq_mul, ne_eq, ne_eq,
        Rat.cast_eq_zero, Rat.cast_eq_zero]
      constructor
      · intro h h'
        apply h
        have hb : B.coeff P = 0 := by linarith [mul_nonneg ht.le h2]
        have hg : G.coeff P = 0 := by linarith
        rw [hb, hg]; ring
      · intro h h'
        apply h
        have hb : B.coeff P = 0 := by nlinarith [mul_nonneg ht.le h2]
        have hg : G.coeff P = 0 := by
          by_contra hg
          have : 0 < t * G.coeff P := mul_pos ht (lt_of_le_of_ne h2 (Ne.symm hg))
          linarith
        rw [hb, hg]; ring
    exact ⟨⟨hπ.toIsSmoothResolution, hπ.isPureCodimOne_exceptionalSet,
      hsupp ▸ hπ.isSNCSubset⟩, hπp⟩
  have hcrit : ∀ t : ℚ, 0 < t → (IsLogCanonicalPair sX (B + t • G) ↔
      ∀ F, B₀.coeff F + t * Gπ.coeff F ≤ 1) := by
    intro t ht
    have hpair : MMP.Mori.IsPairWith sX 4 K (B + t • G) :=
      ⟨hPW.1, hPW.2.1, by rw [← add_assoc]; exact hPW.2.2.add (isQCartier_smul' hGq t)⟩
    have hpair' : MMP.Fourfold.IsPair sX (B + t • G) :=
      ⟨inferInstance, inferInstance, hpair.isPair, fun P => by
        rw [MMP.Mori.DivisorWithCoeffs.coeff_add, MMP.Mori.DivisorWithCoeffs.coeff_smul,
          smul_eq_mul]
        exact add_nonneg (hB.2.1 P) (mul_nonneg ht.le (hG0 P))⟩
    rw [MMP.Fourfold.isLogCanonicalPair_iff_forall_coeff_le_one sX hpair' (hres t ht) hY
      (hcrep t)]
    simp [MMP.Mori.DivisorWithCoeffs.coeff_add, MMP.Mori.DivisorWithCoeffs.coeff_smul, smul_eq_mul]
  -- `(X, B + G)` is not lc
  have hbad : ∃ F, 1 < B₀.coeff F + Gπ.coeff F := by
    by_contra h
    push Not at h
    exact hGnlc (by simpa using (hcrit 1 one_pos).2 (fun F => by simpa using h F))
  classical
  set T := Gπ.support.filter fun F => 0 < Gπ.coeff F
  obtain ⟨F₁, hF₁⟩ := hbad
  have hF₁T : F₁ ∈ T := by
    have h1 := hd1 F₁
    simp only [T, Finset.mem_filter, Finsupp.mem_support_iff]
    refine ⟨fun h => ?_, by linarith⟩
    rw [MMP.Mori.DivisorWithCoeffs.coeff_apply Gπ F₁, h] at hF₁
    linarith
  -- the threshold
  set r : MMP.Mori.PrimeDivisor Y → ℚ := fun F => (1 - B₀.coeff F) / Gπ.coeff F
  set c := T.inf' ⟨F₁, hF₁T⟩ r
  have hTpos : ∀ F ∈ T, 0 < Gπ.coeff F := fun F hF => (Finset.mem_filter.mp hF).2
  have hcle : ∀ F ∈ T, c ≤ r F := fun F hF => Finset.inf'_le _ hF
  obtain ⟨F₀, hF₀T, hcF₀⟩ := Finset.exists_mem_eq_inf' ⟨F₁, hF₁T⟩ r
  have hg₀ := hTpos F₀ hF₀T
  -- no place of `T` is an lc place of `(X, B)`: `G` contains no lc centre
  have hT1 : ∀ F ∈ T, B₀.coeff F < 1 := by
    intro F hF
    refine lt_of_le_of_ne (hd1 F) fun h1 => ?_
    have hlc0 : IsLogDiscrepancy sX 4 (QDivisor.toRDivisor B) (E F) 0 := by
      have := hlog 0 F
      rw [h1] at this
      simpa using this
    refine hGc (E F).center ⟨E F, hlc0, rfl⟩ ?_
    exact centre_subset_supp_of_pos sX hY hbir hGq hGsupp hGπ F (hTpos F hF)
  have hc0 : 0 < c := by
    rw [show c = r F₀ from hcF₀]
    exact div_pos (by linarith [hT1 F₀ hF₀T]) hg₀
  have hc1 : c < 1 := by
    refine lt_of_le_of_lt (hcle F₁ hF₁T) ?_
    rw [div_lt_one (hTpos F₁ hF₁T)]
    linarith
  have hlcc : IsLogCanonicalPair sX (B + c • G) := by
    refine (hcrit c hc0).2 fun F => ?_
    by_cases hF : F ∈ T
    · have := hcle F hF
      rw [le_div_iff₀ (hTpos F hF)] at this
      linarith
    · have hg : Gπ.coeff F ≤ 0 := by
        by_contra hg
        push Not at hg
        exact hF (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hg.ne', hg⟩)
      have := hd1 F
      nlinarith
  have hF₀eq : B₀.coeff F₀ + c * Gπ.coeff F₀ = 1 := by
    rw [show c = r F₀ from hcF₀]
    simp only [r]
    field_simp
    ring
  refine ⟨c, hc0, hc1, hlcc, E F₀, ?_, ?_⟩
  · have := hlog c F₀
    rw [show (1 - B₀.coeff F₀ - c * Gπ.coeff F₀ : ℚ) = 0 by linarith] at this
    simpa using this
  · by_contra h
    have := hcentre F₀ h
    nlinarith

/-! ### Sections free off the base locus, and their powers -/

/-- Finitely many nonzero sections of `𝒪_X(M)` have no common zero off `Bs|M|`. -/
private theorem exists_finset_free_off_baseLocus (M : Divisor X) :
    ∃ t : Finset {σ : M.divisorialSubmodule ⊤ // σ ≠ 0}, ∀ y : X,
      y ∉ (M.baseLocus : Set X) → ∃ i ∈ t, y ∉ ((M.zeroDivisor i.1 i.2).supp : Set X) := by
  have : IsNoetherian X := ⟨⟩
  have hc : IsCompact ((M.baseLocus : Set X)ᶜ) := NoetherianSpace.isCompact _
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover
    (fun i : {σ : M.divisorialSubmodule ⊤ // σ ≠ 0} => ((M.zeroDivisor i.1 i.2).supp : Set X)ᶜ)
    (fun i => (M.zeroDivisor i.1 i.2).supp.isClosed.isOpen_compl) (fun y hy => by
      have hy' : ¬ ∀ (σ : M.divisorialSubmodule ⊤) (hσ : σ ≠ 0),
          y ∈ ((M.zeroDivisor σ hσ).supp : Set X) := fun h =>
        hy ((Divisor.mem_baseLocus_iff M y).2 h)
      push Not at hy'
      obtain ⟨σ, hσ, h⟩ := hy'
      exact Set.mem_iUnion.2 ⟨⟨σ, hσ⟩, h⟩)
  refine ⟨t, fun y hy => ?_⟩
  obtain ⟨i, hi, h⟩ := Set.mem_iUnion₂.1 (ht hy)
  exact ⟨i, hi, h⟩

/-- The `k`-th power `σᵏ ∈ H⁰(X, 𝒪_X(kM))` of a section `σ ∈ H⁰(X, 𝒪_X(M))`. -/
private noncomputable def secPow {M : Divisor X} (σ : M.divisorialSubmodule ⊤) (k : ℕ) :
    (k • M).divisorialSubmodule ⊤ :=
  ⟨σ.1 ^ k, by
    induction k with
    | zero => rw [pow_zero, zero_smul]; exact Divisor.IsDivisorialSection.one le_rfl ⊤
    | succ k ih => rw [pow_succ, succ_nsmul]; exact ih.mul σ.2⟩

private theorem sectionToRationalFunctions_secPow {M : Divisor X} (σ : M.divisorialSubmodule ⊤)
    (k : ℕ) : Divisor.sectionToRationalFunctions (secPow σ k) =
      Divisor.sectionToRationalFunctions σ ^ k :=
  map_pow (MMP.Mori.rationalFunctionsPresheafTopEquiv X) σ.1 k

private theorem secPow_ne_zero {M : Divisor X} {σ : M.divisorialSubmodule ⊤} (hσ : σ ≠ 0)
    (k : ℕ) : secPow σ k ≠ 0 := by
  intro h
  have hu := (Divisor.isUnit_sectionToRationalFunctions hσ).pow k
  rw [← sectionToRationalFunctions_secPow, h] at hu
  have h00 : Divisor.sectionToRationalFunctions (0 : (k • M).divisorialSubmodule ⊤) = 0 :=
    map_zero (MMP.Mori.rationalFunctionsPresheafTopEquiv X)
  obtain ⟨y⟩ : Nonempty X := inferInstance
  have hu' := (Pi.isUnit_iff.mp hu) (MMP.Mori.pointComponent y)
  rw [h00] at hu'
  exact not_isUnit_zero hu'

/-- `(σᵏ)₀ = k (σ)₀`. -/
private theorem zeroDivisor_secPow {M : Divisor X} {σ : M.divisorialSubmodule ⊤} (hσ : σ ≠ 0)
    (k : ℕ) : (k • M).zeroDivisor (secPow σ k) (secPow_ne_zero hσ k) =
      k • M.zeroDivisor σ hσ := by
  have hu : (Divisor.isUnit_sectionToRationalFunctions (secPow_ne_zero hσ k)).unit =
      (Divisor.isUnit_sectionToRationalFunctions hσ).unit ^ k :=
    Units.ext (by rw [Units.val_pow_eq_pow_val]; exact sectionToRationalFunctions_secPow σ k)
  rw [Divisor.zeroDivisor_eq, Divisor.zeroDivisor_eq, hu, smul_add]
  congr 1
  ext P
  simp [MMP.Mori.coeff_principalDivisor, MMP.Mori.PrimeDivisor.ord_pow]

end Setup

/-! ### Orders of vanishing of a general member -/

section Orders

variable {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]

open MMP.Mori in
/-- For a nonzero section `ρ` of `𝒪_Y(N)`, `(ρ)₀` has coefficient at least `n` along `F` iff
`v_F(ρ) ≥ n - N_F`. -/
private theorem ordGE_iff_le_coeff_zeroDivisor {N : Divisor Y} (ρ : N.divisorialSubmodule ⊤)
    (hρ : ρ ≠ 0) (F : MMP.Mori.PrimeDivisor Y) (n : ℤ) :
    F.OrdGE (n - N.coeff F) (ρ.1 ⟨F.component, trivial⟩) ↔
      n ≤ (N.zeroDivisor ρ hρ).coeff F := by
  set u := (Divisor.isUnit_sectionToRationalFunctions hρ).unit
  have hu : (u : RationalFunctions Y) F.component = ρ.1 ⟨F.component, trivial⟩ := rfl
  have hunit : IsUnit ((u : RationalFunctions Y) F.component) :=
    (Pi.isUnit_iff.mp u.isUnit) F.component
  have hc : (N.zeroDivisor ρ hρ).coeff F = F.ord u + N.coeff F := rfl
  rw [hc, ← hu]
  unfold MMP.Mori.PrimeDivisor.OrdGE
  rw [F.valuation_component, WithZero.exp_le_exp]
  constructor
  · rintro (h | h)
    · exact absurd h hunit.ne_zero
    · omega
  · intro h
    right
    omega

open MMP.Mori in
/-- **Orders of a general member.** Let `f : Y ⟶ X` be dominant, `N` Cartier on `X` and `F` a
prime divisor of `Y`. If `f^*(τ_i)₀` has coefficient at least `n` along `F` for every nonzero
`τ_i ∈ H⁰(X, 𝒪_X(N))`, so has `f^*(σ)₀` for every nonzero combination `σ = ∑ r_i τ_i`. -/
private theorem le_coeff_pullback_zeroDivisor_sum {f : Y ⟶ X} [IsDominant f] {N : Divisor X}
    (hNc : N.IsCartier) (F : MMP.Mori.PrimeDivisor Y) (n : ℤ) {ι : Type} [Fintype ι]
    (τ : ι → N.divisorialSubmodule ⊤) (r : ι → Γ(X, ⊤))
    (hτ : ∀ (i : ι) (hi : τ i ≠ 0)
      (hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉
        (N.zeroDivisor (τ i) hi).supp) (D' : Divisor Y),
      (N.zeroDivisor (τ i) hi).IsPullback f hB D' → n ≤ D'.coeff F)
    (hσ : (∑ i, r i • τ i) ≠ 0)
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉
      (N.zeroDivisor _ hσ).supp} {D' : Divisor Y}
    (hD' : (N.zeroDivisor _ hσ).IsPullback f hB D') : n ≤ D'.coeff F := by
  classical
  have hBN : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ N.supp :=
    fun Z => MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant f _ Z
  obtain ⟨N', hN'⟩ := hNc.exists_isPullback hBN
  set ρ := MMP.Mori.pullSec f hNc hN'
  have hpb : ∀ (τ : N.divisorialSubmodule ⊤) (hτ : τ ≠ 0)
      (hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉
        (N.zeroDivisor τ hτ).supp) (D' : Divisor Y),
      (N.zeroDivisor τ hτ).IsPullback f hB D' → ∃ h : ρ τ ≠ 0, D' = N'.zeroDivisor (ρ τ) h := by
    intro τ hτ hB D' hD'
    obtain ⟨h, hpb⟩ := MMP.Mori.isPullback_zeroDivisor_pullSec f hNc hN' τ hτ hB
    exact ⟨h, hD'.eq (isCartier_zeroDivisor hNc τ hτ) hpb⟩
  have hP : ∀ i, F.OrdGE (n - N'.coeff F) ((ρ (τ i)).1 ⟨F.component, trivial⟩) := by
    intro i
    by_cases hi : τ i = 0
    · rw [hi, map_zero]
      exact MMP.Mori.PrimeDivisor.OrdGE.zero _
    · have hBi : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉
          (N.zeroDivisor (τ i) hi).supp :=
        fun Z => MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant f _ Z
      obtain ⟨D'', hD''⟩ := (isCartier_zeroDivisor hNc _ hi).exists_isPullback hBi
      obtain ⟨h, hDeq⟩ := hpb _ hi hBi D'' hD''
      have := hτ i hi hBi D'' hD''
      rw [hDeq] at this
      exact (ordGE_iff_le_coeff_zeroDivisor _ h F n).2 this
  have hsmul : ∀ (s : Γ(Y, ⊤)) (φ : ToType ((rationalFunctionsPresheaf Y).obj (Opposite.op ⊤))),
      F.OrdGE (n - N'.coeff F) (φ ⟨F.component, trivial⟩) →
        F.OrdGE (n - N'.coeff F) ((s • φ) ⟨F.component, trivial⟩) := by
    intro s φ h
    have hE : F.genericPoint ∈ (⊤ : Y.Opens) := trivial
    rw [rationalFunctions_smul_apply, ← TopCat.Presheaf.germ_stalkSpecializes_apply Y.presheaf hE
      F.specializes_genericPoint]
    exact h.toComponent_mul _
  have hsum : F.OrdGE (n - N'.coeff F) ((ρ (∑ i, r i • τ i)).1 ⟨F.component, trivial⟩) := by
    rw [map_sum, Submodule.coe_sum]
    refine Finset.sum_induction _
      (p := fun φ : ToType ((rationalFunctionsPresheaf Y).obj (Opposite.op ⊤)) =>
        F.OrdGE (n - N'.coeff F) (φ ⟨F.component, trivial⟩))
      (fun a b ha hb => MMP.Mori.PrimeDivisor.OrdGE.add ha hb)
      (MMP.Mori.PrimeDivisor.OrdGE.zero _) fun i _ => ?_
    rw [MMP.Mori.pullSec_smul, Submodule.coe_smul]
    exact hsmul _ _ (hP i)
  obtain ⟨h, rfl⟩ := hpb _ hσ hB D' hD'
  exact (ordGE_iff_le_coeff_zeroDivisor _ h F n).1 hsum

open MMP.Mori in
/-- If an effective Cartier `D` contains the image of the generic point of `F`, then `f^*D` has
coefficient at least one along `F`. -/
private theorem one_le_coeff_of_isPullback {f : Y ⟶ X} {D : Divisor X} (hDc : D.IsCartier)
    (hD0 : 0 ≤ D) {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ D.supp}
    {D' : Divisor Y} (hD' : D.IsPullback f hB D') (F : MMP.Mori.PrimeDivisor Y)
    (hF : f F.genericPoint ∈ (D.supp : Set X)) : 1 ≤ D'.coeff F := by
  have hsupp := MMP.Flips.supp_eq_preimage_supp_of_isPullback hDc hD0 hD'
  have hη : F.genericPoint ∈ (D'.supp : Set Y) := by rw [hsupp]; exact hF
  obtain ⟨P, hP, hηP⟩ := DivisorWithCoeffs.mem_supp_iff.1 hη
  have hPE : P = F := MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hηP
  subst hPE
  have hnn := MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn hDc (V := ⊤)
    (fun Q _ => hD0 Q) hD' P
    ⟨P.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support P, trivial⟩
  have hne : D'.coeff P ≠ 0 := hP
  omega

end Orders

/-! ### A divisor over a closed subset -/

/-- The support of a finite product of ideal sheaves is the union of the supports. -/
private theorem support_prod {Y : Scheme.{0}} {ι : Type*} (s : Finset ι)
    (g : ι → Y.IdealSheafData) :
    (∏ i ∈ s, g i).support = s.sup fun i => (g i).support := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Scheme.IdealSheafData.support_mul, ih, Finset.sup_insert]

section Setup

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  (sX : X ⟶ Spec (.of ℂ)) [QuasiCompact sX]

/-- **A divisor over a closed subset.** On a normal projective variety `X` over `ℂ`, every
nonempty closed subset `Z ≠ X` contains the centre of a divisor over `X` with proper model:
principalize the ideal of `Z` on a log resolution `f : Y ⟶ X`; the support of
`f⁻¹ℐ_Z · 𝒪_Y = 𝒪_Y(-D)` is `f⁻¹(Z)`, a nonempty union of prime divisors. -/
private theorem exists_divisorOver_center_subset (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (Δ : QDivisor X) {A : QDivisor X} (hA : A.IsAmple) (Z : Closeds X)
    (hZ : (Z : Set X).Nonempty) (hZu : (Z : Set X) ≠ Set.univ) :
    ∃ E : DivisorOver ℂ sX, IsProper E.f ∧ (E.center : Set X) ⊆ Z := by
  classical
  haveI := hX
  obtain ⟨hnef, hbig⟩ := MMP.Mori.QDivisor.isNef_and_isBig_of_isAmple sX hA
  set I := Scheme.IdealSheafData.vanishingIdeal Z with hIdef
  have hIsupp : (I.support : Set X) = Z := Scheme.IdealSheafData.coe_support_vanishingIdeal Z
  have hI : I ≠ ⊥ := by
    intro h
    apply hZu
    rw [← hIsupp, h, Scheme.IdealSheafData.support_bot]
    rfl
  obtain ⟨Y, f, hLR, -, hYln, hYn, hYc, D, -, -, hID, -⟩ :=
    MMP.Mori.exists_isLogResolution_isAmple_pullback_sub_sum sX Δ I hI A hnef hbig
  have hXn : MMP.Mori.IsNormalVariety ℂ sX :=
    ⟨(MMP.Mori.isProperVariety_iff ℂ sX).1 inferInstance |>.1, inferInstance⟩
  obtain ⟨hY, -, -⟩ := MMP.Mori.IsSmoothResolution.isNormalVariety hXn hLR.toIsSmoothResolution
  have hbir := hLR.isBirationalMorphism
  haveI := hLR.isProper
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : IsDominant f := hbir.isDominant
  have hsupp : ((I.comap f).support : Set Y) = f ⁻¹' Z := by
    rw [Scheme.IdealSheafData.support_comap]
    change f ⁻¹' (I.support : Set X) = _
    rw [hIsupp]
  obtain ⟨z, hz⟩ := hZ
  obtain ⟨y, rfl⟩ := f.surjective z
  set A' : AlgebraicGeometry.PrimeDivisor Y → ℕ := fun E => (D E).toNat
  have hprod : MMP.Resolution.divisorIdeal A' = ∏ E ∈ D.support, E.idealSheaf ^ A' E := by
    unfold MMP.Resolution.divisorIdeal
    refine finprod_eq_prod_of_mulSupport_subset _ fun E hE => ?_
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    intro h0
    exact hE (by change E.idealSheaf ^ (D E).toNat = 1; rw [h0, Int.toNat_zero, pow_zero])
  have hy : y ∈ ((∏ E ∈ D.support, E.idealSheaf ^ A' E).support : Set Y) := by
    rw [← hprod, ← hID, hsupp]
    exact hz
  rw [support_prod, TopologicalSpace.Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion] at hy
  simp only [Set.mem_iUnion, Function.comp_apply] at hy
  obtain ⟨E, hE, hyE⟩ := hy
  have hA'E : A' E ≠ 0 := by
    intro h0
    rw [h0, pow_zero, Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.support_top] at hyE
    exact hyE
  have hEsupp : (E.support : Set Y) ⊆ f ⁻¹' Z := by
    intro w hw
    rw [← hsupp, hID, hprod, support_prod, TopologicalSpace.Closeds.coe_finset_sup,
      Finset.sup_set_eq_biUnion]
    refine Set.mem_biUnion hE ?_
    change w ∈ ((E.idealSheaf ^ A' E).support : Set Y)
    rw [Scheme.IdealSheafData.support_pow _ _ hA'E]
    exact hw
  refine ⟨⟨Y, f, hY, hbir, E⟩, hLR.isProper, ?_⟩
  rw [DivisorOver.center_eq_closure_genericPoint]
  refine closure_minimal ?_ Z.isClosed
  rintro _ rfl
  exact hEsupp (MMP.Flips.primeDivisor_genericPoint_mem_support E)

/-! ### A general member of high order along a divisor over the base locus -/

/-- **Log discrepancies after adding an effective Cartier divisor.** If `a(E, X, B) = b` with
`E` proper over `X`, then `a(E, X, B + H) = 1 + b - coeff_E(f^*H)` for a Cartier `H`. -/
private theorem exists_isLogDiscrepancy_add {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4)
    {B : QDivisor X} (hB : IsLogCanonicalPair sX B) {H : Divisor X} (hHc : H.IsCartier)
    (E : DivisorOver ℂ sX) {b : ℚ} (hEp : IsProper E.f)
    (hb : MMP.Mori.IsDiscrepancy sX 4 K B E b) :
    haveI := E.isLocallyNoetherian
    haveI := E.isNormal
    ∃ (hB' : ∀ Z : irreducibleComponents E.Y, E.f (MMP.Mori.componentGenericPoint E.Y Z) ∉ H.supp)
      (H' : Divisor E.Y), H.IsPullback E.f hB' H' ∧
      IsLogDiscrepancy sX 4 (QDivisor.toRDivisor (B + Divisor.toQDivisor H)) E
        (((1 + b - H'.coeff E.E : ℚ)) : ℝ) := by
  haveI := E.isLocallyNoetherian
  haveI := E.isNormal
  haveI := E.isIntegral
  haveI := E.isDominant
  haveI : CompactSpace E.Y := QuasiCompact.compactSpace_of_compactSpace E.f
  have hlc := isLcPair_of_isLogCanonicalPair hB hK
  obtain ⟨-, hBH, hiff⟩ :=
    hlc.1.isDiscrepancy_add_smul_iff (MMP.Mori.QDivisor.isQCartier_toQDivisor hHc) E
  have hBH' : ∀ Z : irreducibleComponents E.Y, E.f (MMP.Mori.componentGenericPoint E.Y Z) ∉ H.supp :=
    fun Z => MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant E.f _ Z
  obtain ⟨H', hH'⟩ := hHc.exists_isPullback hBH'
  have hpbQ := MMP.Mori.QDivisor.isPullback_toQDivisor hHc hBH hH'
  have hdisc := ((hiff _ hpbQ).1 b).2 hb
  have hlog := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hdisc hEp
  refine ⟨hBH', H', hH', ?_⟩
  convert hlog using 1
  rw [Divisor.coeff_toQDivisor]
  push_cast
  ring

/-- **A divisor lc off `W` contains no lc centre off `W`.** If `(X, B + H)` is lc off `W` for an
effective Cartier `H`, and no lc centre of `(X, B)` lies in `W`, then `H` contains no lc centre:
along an lc place `E` the coefficient of `f^*H` would be positive, making
`a(E, X, B + H) < 0`. -/
private theorem not_subset_supp_of_lc_off {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4)
    {B : QDivisor X} (hB : IsLogCanonicalPair sX B) {H : Divisor X} (hHc : H.IsCartier)
    (hH0 : 0 ≤ H) {W : Set X}
    (hGW : ∀ (E : DivisorOver ℂ sX) (r : ℝ), ¬ (E.center : Set X) ⊆ W →
      IsLogDiscrepancy sX 4 (QDivisor.toRDivisor (B + Divisor.toQDivisor H)) E r → 0 ≤ r)
    (hlcW : ∀ E : DivisorOver ℂ sX, IsLogDiscrepancy sX 4 (QDivisor.toRDivisor B) E 0 →
      ¬ (E.center : Set X) ⊆ W) :
    ∀ Z ∈ lcCentres sX B, ¬ (Z : Set X) ⊆ ((Divisor.toQDivisor H).supp : Set X) := by
  rintro Z ⟨E, hE0, rfl⟩ hZH
  rw [Divisor.supp_toQDivisor] at hZH
  have hb := isDiscrepancy_neg_one_of_isLogDiscrepancy_zero sX hK hB hE0
  obtain ⟨hBH', H', hH', hlog⟩ := exists_isLogDiscrepancy_add sX hK hB hHc E hE0.2.1 hb
  haveI := E.isLocallyNoetherian
  haveI := E.isNormal
  haveI := E.isIntegral
  haveI : IsProper E.f := hE0.2.1
  haveI : CompactSpace E.Y := QuasiCompact.compactSpace_of_compactSpace E.f
  have hηc : E.f E.E.genericPoint ∈ (E.center : Set X) := by
    rw [DivisorOver.center_eq_closure_genericPoint]; exact subset_closure rfl
  have h1 := one_le_coeff_of_isPullback hHc hH0 hH' E.E (hZH hηc)
  have h0 := hGW E _ (hlcW E hE0) hlog
  have h1' : (1 : ℚ) ≤ H'.coeff E.E := by exact_mod_cast h1
  have : (0 : ℚ) ≤ 1 + -1 - H'.coeff E.E := by exact_mod_cast h0
  linarith

/-- **Order of a general member of the system of `k`-th powers.** If `f(η_F)` lies in the zero
divisor of every section in a finite family of nonzero sections of a Cartier `M`, then for
every nonzero combination `σ` of their `k`-th powers, `f^*(σ)₀` has coefficient at least `k`
along `F`. -/
private theorem le_coeff_pullback_secPow_sum {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X} [IsDominant f]
    {M : Divisor X} (hMc : M.IsCartier) (k : ℕ) {ι : Type} [Fintype ι]
    (σ : ι → {σ : M.divisorialSubmodule ⊤ // σ ≠ 0}) (r : ι → Γ(X, ⊤))
    (F : MMP.Mori.PrimeDivisor Y)
    (hF : ∀ i, f F.genericPoint ∈ ((M.zeroDivisor (σ i).1 (σ i).2).supp : Set X))
    (hσ : (∑ i, r i • secPow (σ i).1 k) ≠ 0)
    {hB : ∀ Z : irreducibleComponents Y, f (MMP.Mori.componentGenericPoint Y Z) ∉
      ((k • M).zeroDivisor _ hσ).supp} {D' : Divisor Y}
    (hD' : ((k • M).zeroDivisor _ hσ).IsPullback f hB D') : (k : ℤ) ≤ D'.coeff F := by
  refine le_coeff_pullback_zeroDivisor_sum (hMc.nsmul k) F k (fun i => secPow (σ i).1 k) r ?_
    hσ hD'
  intro i hi hBi D' hD'
  have hBs' : ∀ Z : irreducibleComponents Y,
      f (MMP.Mori.componentGenericPoint Y Z) ∉ (M.zeroDivisor (σ i).1 (σ i).2).supp :=
    fun Z => MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant f _ Z
  have hσic := isCartier_zeroDivisor hMc (σ i).1 (σ i).2
  obtain ⟨D₁, hD₁⟩ := hσic.exists_isPullback hBs'
  have hkpb := hD₁.zsmul hσic (k : ℤ)
    (fun Z => MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant f _ Z)
  have heq : (k • M).zeroDivisor (secPow (σ i).1 k) hi =
      ((k : ℤ) • M.zeroDivisor (σ i).1 (σ i).2) := by
    rw [natCast_zsmul]
    exact zeroDivisor_secPow (σ i).2 k
  have hD'eq : D' = (k : ℤ) • D₁ :=
    hD'.eq (isCartier_zeroDivisor (hMc.nsmul k) _ hi) (hkpb.of_eq heq.symm)
  have h1 := one_le_coeff_of_isPullback hσic (Divisor.zeroDivisor_nonneg _ _ _) hD₁ F (hF i)
  rw [hD'eq, MMP.Mori.DivisorWithCoeffs.coeff_smul, smul_eq_mul]
  nlinarith

/-- **A general boundary concentrated on the base locus.** Let `(X, B)` be an lc pair and `M` a
Cartier divisor whose base locus `Z` is nonempty, not all of `X`, and contains no lc centre.
Then for some `k > 0` a general member `H ∈ |kM|` (of the span of the `k`-th powers of sections
of `M`) makes `(X, B + H)` lc off `Z` but not lc, and contains no lc centre. -/
private theorem exists_boundary_not_lc (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4) {B : QDivisor X}
    (hB : IsLogCanonicalPair sX B) {A : QDivisor X} (hA : A.IsAmple) {M : Divisor X}
    (hMc : M.IsCartier) (hZne : (M.baseLocus : Set X).Nonempty)
    (hZu : (M.baseLocus : Set X) ≠ Set.univ)
    (hlcZ : ∀ E : DivisorOver ℂ sX, IsLogDiscrepancy sX 4 (QDivisor.toRDivisor B) E 0 →
      ¬ (E.center : Set X) ⊆ M.baseLocus) :
    ∃ (k : ℕ) (σ : (k • M).divisorialSubmodule ⊤) (hσ : σ ≠ 0),
      (∀ (E : DivisorOver ℂ sX) (r : ℝ), ¬ (E.center : Set X) ⊆ M.baseLocus →
        IsLogDiscrepancy sX 4
          (QDivisor.toRDivisor (B + Divisor.toQDivisor ((k • M).zeroDivisor σ hσ))) E r →
            0 ≤ r) ∧
      ¬ IsLogCanonicalPair sX (B + Divisor.toQDivisor ((k • M).zeroDivisor σ hσ)) := by
  classical
  -- a divisor `E₀` over the base locus and an integer `k > 1 + a(E₀, X, B)`
  obtain ⟨E₀, hE₀p, hE₀Z⟩ :=
    exists_divisorOver_center_subset sX hX B hA M.baseLocus hZne hZu
  have hlc := isLcPair_of_isLogCanonicalPair hB hK
  obtain ⟨b₀, hb₀⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hlc.1.isPair hK E₀
  obtain ⟨k, hk⟩ := exists_nat_gt (1 + b₀)
  -- sections of `M` free off its base locus, and their `k`-th powers
  obtain ⟨t, ht⟩ := exists_finset_free_off_baseLocus M
  have hNc : (k • M).IsCartier := hMc.nsmul k
  let τ : t → (k • M).divisorialSubmodule ⊤ := fun i => secPow i.1.1 k
  have hτ : ∀ y : X, y ∉ (M.baseLocus : Set X) → ∃ (i : t) (hi : τ i ≠ 0),
      y ∉ ((k • M).zeroDivisor (τ i) hi).supp := by
    intro y hy
    obtain ⟨i, hit, hyi⟩ := ht y hy
    refine ⟨⟨i, hit⟩, secPow_ne_zero i.2 k, fun hmem => hyi ?_⟩
    change y ∈ (((k • M).zeroDivisor (secPow i.1 k) (secPow_ne_zero i.2 k)).supp : Set X) at hmem
    rw [zeroDivisor_secPow i.2 k] at hmem
    obtain ⟨P, hP, hyP⟩ := MMP.Mori.DivisorWithCoeffs.mem_supp_iff.1 hmem
    refine MMP.Mori.DivisorWithCoeffs.mem_supp_iff.2 ⟨P, fun h0 => hP ?_, hyP⟩
    change (k • M.zeroDivisor i.1 i.2) P = 0
    rw [Finsupp.smul_apply, show M.zeroDivisor i.1 i.2 P = 0 from h0, smul_zero]
  -- a general member `H` of the span of the `τ i`
  obtain ⟨Q, hQ0, hQ⟩ :=
    exists_polynomial_lc_off sX hX hK hB (M.baseLocus : Set X) M.baseLocus.isClosed hZu hNc τ hτ
  obtain ⟨c, hcQ⟩ : ∃ c : t → ℂ, MvPolynomial.eval c Q ≠ 0 := by
    by_contra h
    push Not at h
    exact hQ0 (MvPolynomial.funext fun x => by rw [h x, map_zero])
  obtain ⟨hσ, hoff⟩ := hQ c hcQ
  refine ⟨k, _, hσ, fun E r hE hr => ?_, fun hlcH => ?_⟩
  · exact hoff 1 one_pos E r hE (by simpa using hr)
  -- `E₀^*H ≥ k E₀`, so `a(E₀, X, B + H) < 0`
  have hHc := isCartier_zeroDivisor hNc _ hσ
  obtain ⟨hBH', H', hH', hlog⟩ := exists_isLogDiscrepancy_add sX hK hB hHc E₀ hE₀p hb₀
  haveI := E₀.isLocallyNoetherian
  haveI := E₀.isNormal
  haveI := E₀.isIntegral
  haveI := E₀.isDominant
  haveI : CompactSpace E₀.Y := QuasiCompact.compactSpace_of_compactSpace E₀.f
  have hηc : E₀.f E₀.E.genericPoint ∈ (E₀.center : Set X) := by
    rw [DivisorOver.center_eq_closure_genericPoint]; exact subset_closure rfl
  have hk' : (k : ℤ) ≤ H'.coeff E₀.E :=
    le_coeff_pullback_secPow_sum hMc k (fun i : t => i.1)
      (fun i => MMP.Mori.scalarsToGlobalSections ℂ sX (c i)) E₀.E
      (fun i => Divisor.baseLocus_le_supp M i.1.1 i.1.2 (hE₀Z hηc)) hσ
      (hB := fun Z => MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant E₀.f _ Z) hH'
  have h0 := hlcH.2.2 4 E₀ _ hlog
  have hk'' : (k : ℚ) ≤ H'.coeff E₀.E := by exact_mod_cast hk'
  have : (0 : ℚ) ≤ 1 + b₀ - H'.coeff E₀.E := by exact_mod_cast h0
  linarith

/-- **The ample gap of the perturbed pair.** For a nonzero section `σ` of `𝒪_X(NL)` and `c ≥ 0`,
`(a + cN) L - (K + B + c(σ)₀) ∼_ℚ aL - (K + B)` is ample when `aL - (K + B)` is. -/
private theorem isAmple_add_smul_zeroDivisor (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    {K L : Divisor X} {B : QDivisor X} {a : ℚ}
    (hample : (a • Divisor.toQDivisor L - (Divisor.toQDivisor K + B)).IsAmple) {N : ℕ}
    {M : Divisor X} (hM : M = N • L) (σ : M.divisorialSubmodule ⊤) (hσ : σ ≠ 0) (c : ℚ) :
    ((a + c * N) • Divisor.toQDivisor L -
      (Divisor.toQDivisor K + (B + c • Divisor.toQDivisor (M.zeroDivisor σ hσ)))).IsAmple := by
  subst hM
  set φ := (Divisor.isUnit_sectionToRationalFunctions hσ).unit
  have hHeq : Divisor.toQDivisor ((N • L).zeroDivisor σ hσ) =
      Divisor.toQDivisor (MMP.Mori.principalDivisor φ) + (N : ℚ) • Divisor.toQDivisor L := by
    rw [Divisor.zeroDivisor_eq, map_add, map_nsmul, Nat.cast_smul_eq_nsmul]
  have h := isAmple_smul_add_principal sX hX hample (s := 1) one_pos (-c) φ
  convert h using 1
  rw [hHeq]
  module

/-! ### The stable base loci are empty -/

/-- **The stable base loci of an lc pair with an lc centre are empty.** Let `(X, B)` be an lc
pair on a normal projective complex fourfold which has an lc centre, `L` nef Cartier with
`aL - (K + B)` ample, `a > 0`, and `s ≥ 2`. Then `B_s = ⋂_{u ≥ 1} Bs|sᵘL|` is empty.

Otherwise put `M = sᵘL` with `u` so large that `Bs|M| = B_s` and that no lc centre lies in
`Bs|M|`. By `exists_boundary_not_lc` a general `H ∈ |kM|` makes `(X, B + H)` lc off `B_s` but not
lc. Its log canonical threshold `c` gives an lc pair `(X, B + cH)` with an lc centre inside `B_s`
and the ample gap `(a + c k sᵘ) L - (K + B + cH) ∼_ℚ aL - (K + B)`. Nonvanishing along lc centres
for this pair contradicts `Bs|sᵘ'L| = B_s` for `u'` large. -/
private theorem stableBaseLocusOfPowers_eq_bot (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hdim : topologicalKrullDim X = 4) {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4)
    {B : QDivisor X} (hB : IsLogCanonicalPair sX B) {L : Divisor X} (hL : L.IsNef ℂ sX)
    {a : ℚ} (ha : 0 < a) (hample : (a • Divisor.toQDivisor L - (Divisor.toQDivisor K + B)).IsAmple)
    (hcen : ∃ E : DivisorOver ℂ sX, IsLogDiscrepancy sX 4 (QDivisor.toRDivisor B) E 0)
    {s : ℕ} (hs : 2 ≤ s) : L.stableBaseLocusOfPowers s = ⊥ := by
  by_contra hne
  obtain ⟨u₀, -, hu₀⟩ :=
    MMP.Mori.Divisor.exists_baseLocusOfMultiple_pow_eq_stableBaseLocusOfPowers L s
  have hpow : ∀ u, u < s ^ u := fun u => Nat.lt_pow_self (by omega)
  -- for every lc pair with an ample gap, no lc centre lies in `B_s`
  have hbig : ∀ (B' : QDivisor X) (a' : ℚ), IsLogCanonicalPair sX B' → 0 < a' →
      (a' • Divisor.toQDivisor L - (Divisor.toQDivisor K + B')).IsAmple →
      ∀ E : DivisorOver ℂ sX, IsLogDiscrepancy sX 4 (QDivisor.toRDivisor B') E 0 →
        ¬ (E.center : Set X) ⊆ L.stableBaseLocusOfPowers s := by
    intro B' a' hB' ha' hample' E hE hsub
    obtain ⟨m₁, hm₁⟩ := Filter.eventually_atTop.1
      (MMP.Fourfold.not_center_subset_baseLocusOfMultiple sX hX hdim hK hB' hL ha' hample')
    set u := max u₀ m₁
    refine hm₁ (s ^ u) ((le_max_right _ _).trans (hpow u).le) 4 E hE ?_
    rw [hu₀ u (le_max_left _ _)]
    exact hsub
  -- `M = s^{u₀} L`
  have hBs : ((s ^ u₀) • L).baseLocus = L.stableBaseLocusOfPowers s := hu₀ u₀ le_rfl
  have hlcZ : ∀ E : DivisorOver ℂ sX, IsLogDiscrepancy sX 4 (QDivisor.toRDivisor B) E 0 →
      ¬ (E.center : Set X) ⊆ ((s ^ u₀) • L).baseLocus :=
    fun E hE => hBs ▸ hbig B a hB ha hample E hE
  have hZne : ((((s ^ u₀) • L).baseLocus : Closeds X) : Set X).Nonempty := by
    rw [hBs]
    by_contra h
    exact hne (TopologicalSpace.Closeds.ext (Set.not_nonempty_iff_eq_empty.1 h))
  obtain ⟨E₁, hE₁⟩ := hcen
  have hZu : ((((s ^ u₀) • L).baseLocus : Closeds X) : Set X) ≠ Set.univ :=
    fun h => hlcZ E₁ hE₁ (h ▸ Set.subset_univ _)
  obtain ⟨k, σ, hσ, hGW, hGnlc⟩ :=
    exists_boundary_not_lc sX hX hK hB hample (hL.1.nsmul _) hZne hZu hlcZ
  set H := (k • (s ^ u₀) • L).zeroDivisor σ hσ with hHdef
  have hHc : H.IsCartier := isCartier_zeroDivisor ((hL.1.nsmul _).nsmul k) σ hσ
  have hH0 : 0 ≤ H := Divisor.zeroDivisor_nonneg _ _ _
  have hGc := not_subset_supp_of_lc_off sX hK hB hHc hH0 hGW hlcZ
  have hG0 : ∀ P, 0 ≤ (Divisor.toQDivisor H).coeff P := fun P => by
    rw [Divisor.coeff_toQDivisor]; exact_mod_cast hH0 P
  -- the log canonical threshold of `H`
  obtain ⟨c, hc0, -, hBc, E', hE'0, hE'Z⟩ := exists_lct_lt_one sX hX hK hB hG0
    (MMP.Mori.QDivisor.isQCartier_toQDivisor hHc) hGc hGW hGnlc
  -- the new pair has an lc centre in `B_s`, against nonvanishing along its lc centres
  have hamp' := isAmple_add_smul_zeroDivisor sX hX hample (N := k * s ^ u₀) (smul_smul _ _ _)
    σ hσ c
  rw [hBs] at hE'Z
  exact hbig _ _ hBc (add_pos_of_pos_of_nonneg ha (mul_nonneg hc0.le (Nat.cast_nonneg _))) hamp'
    E' hE'0 hE'Z

open MMP.Mori in
/-- **The klt case.** An lc pair `(X, B)` without lc places is klt, so the basepoint-free theorem
of Kollár–Mori applies: `|mL|` is basepoint free for all large `m`. -/
private theorem exists_isBasepointFree_nsmul_of_klt (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hdim : topologicalKrullDim X = 4) {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4)
    {B : QDivisor X} (hlc : IsLogCanonicalPair sX B) {L : Divisor X} (hL : L.IsNef ℂ sX)
    {a : ℚ} (ha₀ : 0 < a) (ha : (a • Divisor.toQDivisor L - (Divisor.toQDivisor K + B)).IsAmple)
    (hcen : ∀ E : DivisorOver ℂ sX, ¬ IsLogDiscrepancy sX 4 (QDivisor.toRDivisor B) E 0) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → (m • L).IsBasepointFree := by
  haveI := hX
  have hpair : MMP.Fourfold.IsPair sX B := ⟨inferInstance, inferInstance, hlc.1, hlc.2.1⟩
  have hkltF : MMP.Fourfold.IsKltPair sX B := by
    refine ⟨hpair, fun n' D t ht => lt_of_le_of_ne (hlc.2.2 n' D t ht) fun h => ?_⟩
    subst h
    have hn' : n' = 4 := by
      have := MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ht
      rw [hdim] at this
      exact_mod_cast this.symm
    subst hn'
    exact hcen D ht
  have heq : a • Divisor.toQDivisor L - Divisor.toQDivisor K - B =
      a • Divisor.toQDivisor L - (Divisor.toQDivisor K + B) := by abel
  obtain ⟨hnef, hbig⟩ := QDivisor.isNef_and_isBig_of_isAmple sX ha
  exact IsBasepointFreeDatum.exists_isBasepointFree_nsmul
    { isProperVariety := inferInstance
      isKltPair := (MMP.Fourfold.isKltPair_iff_mori_isKltPair sX hK hpair).1 hkltF
      isEffective := hlc.2.1
      isCartier := hL.1
      isNef := hL
      pos := ha₀
      isQCartier_sub := heq ▸ hnef.1
      isNef_sub := heq ▸ hnef
      isBig_sub := heq ▸ hbig : IsBasepointFreeDatum sX 4 K B L a }

end Setup

open MMP.Mori in
private theorem solution : ∀ {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] (sX : X ⟶ Spec (.of ℂ)) [QuasiCompact sX] (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hdim : topologicalKrullDim X = 4) {B : QDivisor X}
    (hlc : MMP.Intersection.IsLogCanonicalPair sX B)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    {L : Divisor X} (hL : L.IsNef ℂ sX) {a : ℚ} (ha₀ : 0 < a)
    (ha : (a • Divisor.toQDivisor L - (Divisor.toQDivisor K + B)).IsAmple),
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → (m • L).IsBasepointFree := by
  intro X _ _ _ _ sX _ hX hdim B hlc n K hK L hL a ha₀ ha
  have hn : n = 4 := by
    have := hK.topologicalKrullDim_eq
    rw [hdim] at this
    exact_mod_cast this.symm
  subst hn
  by_cases hcen : ∃ E : DivisorOver ℂ sX, IsLogDiscrepancy sX 4 (QDivisor.toRDivisor B) E 0
  · exact Divisor.exists_isBasepointFree_nsmul_of_coprime L (by norm_num : Nat.Coprime 2 3)
      (stableBaseLocusOfPowers_eq_bot sX hX hdim hK hlc hL ha₀ ha hcen le_rfl)
      (stableBaseLocusOfPowers_eq_bot sX hX hdim hK hlc hL ha₀ ha hcen (by norm_num))
  · exact exists_isBasepointFree_nsmul_of_klt sX hX hdim hK hlc hL ha₀ ha (not_exists.mp hcen)

end Proof_thm_mmp_projective_fourfold_lc_basepoint_free

end

open CategoryTheory AlgebraicGeometry MMP.Mori

namespace MMP.Intersection

/-- **The basepoint-free theorem for lc fourfolds.** Let `(X, B)` be a log canonical pair on a
normal projective complex fourfold, with `B` a `ℚ`-divisor and `K` a canonical divisor. Let `L`
be a nef Cartier divisor such that `aL - (K + B)` is ample for some rational `a > 0`. Then there
is `m₀` such that `|mL|` is basepoint free for every `m ≥ m₀`. -/
@[mmp "thm_mmp_projective_fourfold_lc_basepoint_free"]
public theorem IsLogCanonicalPair.exists_isBasepointFree_nsmul
    {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) [QuasiCompact sX] (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hdim : topologicalKrullDim X = 4) {B : QDivisor X}
    (hlc : IsLogCanonicalPair sX B)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    {L : Divisor X} (hL : L.IsNef ℂ sX) {a : ℚ} (ha₀ : 0 < a)
    (ha : (a • Divisor.toQDivisor L - (Divisor.toQDivisor K + B)).IsAmple) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → (m • L).IsBasepointFree :=
      by revert X sX hX hdim B hlc n K hK L hL a ha₀ ha; first | exact Proof_thm_mmp_projective_fourfold_lc_basepoint_free.solution | exact Proof_thm_mmp_projective_fourfold_lc_basepoint_free.solution _ | exact Proof_thm_mmp_projective_fourfold_lc_basepoint_free.solution _ _ | exact Proof_thm_mmp_projective_fourfold_lc_basepoint_free.solution _ _ _ | exact Proof_thm_mmp_projective_fourfold_lc_basepoint_free.solution _ _ _ _

end MMP.Intersection

