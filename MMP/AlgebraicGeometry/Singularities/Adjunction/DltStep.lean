module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.StratumAdjunction
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancy
import MMP.AlgebraicGeometry.Singularities.DltFloorComponentsNormal
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Singularities.Adjunction.ForwardDiscrepancy
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointCodimension
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferentExistence

/-!
# One adjunction step from a dlt pair

Let `(Y, B_Y)` be a dlt pair over an algebraically closed field `k` of characteristic zero and
`P` a prime divisor of `Y` with coefficient `1` in `B_Y`. Then `P`, with its reduced structure, is
a normal variety (Kollár–Mori 5.52), and the residue different `Diff_P(B_Y - P)` of Kollár
[SMMP, Def. 4.2] is defined: there is one adjunction step `(Y, B_Y) ⇝ (P, B_P)`
(`MMP.Fourfold.IsAdjunctionStep`).

## Main results

* `MMP.Fourfold.isNormalVariety_subscheme_of_isDltPair`: a prime divisor of coefficient at least
  one in the boundary of a dlt pair is a normal variety.
* `MMP.Fourfold.exists_isAdjunctionStep_of_isDltPair`: one adjunction step onto such a prime
  divisor exists.

## Implementation notes

In dimension at least two normality is
`MMP.Mori.IsDltPair.isNormal_subscheme_of_coeff_roundDown_ne_zero`; on a curve the prime divisor
is a point, and an integral scheme of dimension zero is the spectrum of a field. The residue
different exists because `K_Y + B_Y` is `ℚ`-Cartier and `P` is normal
(`MMP.Fourfold.exists_isAdjunctionStep_of_isQCartier`).

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998], 5.52
* [J. Kollár, *Singularities of the minimal model program*][Kollar2013], Definition 4.2
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori

/-- An integral scheme of topological Krull dimension zero is normal. -/
theorem isNormal_of_topologicalKrullDim_eq_zero {X : Scheme.{u}} [IsIntegral X]
    (h : topologicalKrullDim X = 0) : IsNormal X := by
  have hx : ∀ x : X, x = genericPoint X := by
    intro x
    have h1 := AlgebraicGeometry.coheight_le_topologicalKrullDim x
    rw [h] at h1
    have h0 : Order.coheight x = 0 := by exact_mod_cast nonpos_iff_eq_zero.mp (by exact_mod_cast h1)
    have hmax : IsMax x := Order.coheight_eq_zero.mp h0
    have h2 : (⊤ : X) ≤ x := hmax le_top
    exact ((show x ⤳ genericPoint X from h2).antisymm (genericPoint_specializes x)).eq
  refine ⟨fun x => inferInstance, fun x => ?_⟩
  obtain rfl := hx x
  change IsIntegrallyClosed X.functionField
  infer_instance

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {Y : Scheme.{0}}
  {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {BY : QDivisor Y}

/-- **Floor components of a dlt pair are normal** (Kollár–Mori 5.52). For a dlt pair `(Y, B_Y)`
and a prime divisor `P` with coefficient at least one in `B_Y`, the reduced subscheme `P` is a
normal variety. -/
theorem isNormalVariety_subscheme_of_isDltPair (hB : MMP.Intersection.IsDltPair sY BY)
    (P : MMP.Mori.PrimeDivisor Y) (hP : 1 ≤ BY.coeff P) :
    haveI := P.integral
    IsNormalVariety k (P.idealSheaf.subschemeι ≫ sY) := by
  have := P.integral
  obtain ⟨⟨hpair, hB0, -⟩, hB1, -⟩ := id hB
  obtain ⟨hX, N, K, hK, -⟩ := hpair
  have : AlgebraicGeometry.IsVariety k sY := hX.1
  have : LocallyOfFiniteType sY := hX.1.toLocallyOfFiniteType
  have hvar : AlgebraicGeometry.IsVariety k (P.idealSheaf.subschemeι ≫ sY) :=
    (MMP.Mori.isVariety_iff k _).mpr ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  refine ⟨hvar, ?_⟩
  have hP1 : BY.coeff P = 1 := le_antisymm (hB1 P) hP
  obtain ⟨n, hn⟩ := MMP.Fourfold.exists_topologicalKrullDim_eq_add_one sY P
  obtain rfl : N = n + 1 := by exact_mod_cast hK.topologicalKrullDim_eq.symm.trans hn
  rcases n with _ | n
  · -- `Y` is a curve and `P` a point
    have hdim : topologicalKrullDim Y = (0 : ℕ) + 1 := by
      rw [hK.topologicalKrullDim_eq]; rfl
    have hdimT := MMP.Fourfold.topologicalKrullDim_eq_of_range_eq_support sY hdim
      P.idealSheaf.subschemeι P (Scheme.IdealSheafData.range_subschemeι P.idealSheaf)
    exact isNormal_of_topologicalKrullDim_eq_zero (by exact_mod_cast hdimT)
  · have hKM : MMP.Mori.IsDltPair sY (n + 1 + 1) K BY :=
      (MMP.Threefold.Bridges.isDltPair_iff_isDltPair sY hK BY).mp hB
    refine hKM.isNormal_subscheme_of_coeff_roundDown_ne_zero (by omega)
      hB0 P ?_
    rw [DivisorWithCoeffs.coeff_roundDown, hP1]
    norm_num

/-- **One adjunction step from a dlt pair** (Kollár–Mori 5.52; Kollár [SMMP, Def. 4.2]). For a
dlt pair `(Y, B_Y)` and a prime divisor `P` with coefficient at least one in `B_Y`, there is an
adjunction step `(Y, B_Y) ⇝ (T, B_T)` onto `P`: `T` is `P` with its reduced structure, a normal
variety, and `B_T = Diff_T(B_Y - T)` is the residue different. -/
theorem exists_isAdjunctionStep_of_isDltPair (hB : MMP.Intersection.IsDltPair sY BY)
    (P : MMP.Mori.PrimeDivisor Y) (hP : 1 ≤ BY.coeff P) :
    ∃ (T : Scheme.{0}) (j : T ⟶ Y) (BT : QDivisor T),
      Set.range j.base = (P.support : Set Y) ∧ IsAdjunctionStep sY BY j BT := by
  have := P.integral
  have hj : Set.range P.idealSheaf.subschemeι.base = (P.support : Set Y) :=
    Scheme.IdealSheafData.range_subschemeι P.idealSheaf
  have hT := isNormalVariety_subscheme_of_isDltPair hB P hP
  obtain ⟨⟨hpair, -, -⟩, hB1, -⟩ := hB
  obtain ⟨hY, N, K, hK, hQ⟩ := hpair
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  obtain ⟨n, hn⟩ := MMP.Fourfold.exists_topologicalKrullDim_eq_add_one sY P
  obtain rfl : N = n + 1 := by exact_mod_cast hK.topologicalKrullDim_eq.symm.trans hn
  obtain ⟨BT, hBT⟩ := exists_isAdjunctionStep_of_isQCartier hY hK hQ P
    (le_antisymm (hB1 P) hP) P.idealSheaf.subschemeι hj hT
  exact ⟨_, P.idealSheaf.subschemeι, BT, hj, hBT⟩

end MMP.Fourfold

end
