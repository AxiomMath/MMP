/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Combinatorics.WeightedGraph.Shapes
public import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGerm
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupEmbedded

/-!
# Types of log surface germs in FA Fig. 3, and the boundary `Θ_{g,a}`

Some of the types of surface germs with boundary `(X, P; B)` listed in Fig. 3 of Chapter 3 of
Kollár et al., *Flips and abundance for algebraic threefolds* (FA), described through the
weighted dual graph `Γ(f)` and the extended dual graph `Γ^*(f)` of the minimal resolution
`f : Y ⟶ X` with exceptional curves `E_1, …, E_n`, together with the `ℚ`-divisor
`Θ_{g,a} = g⁻¹_* B + ∑_j (1 - a_j) E_j` on a resolution `g` (FA 3.1.4, 3.1.5, 3.3.2).

## Main definitions

* `MMP.Flips.logPullbackBoundary`: `Θ_{g,a} = g⁻¹_* B + ∑_j (1 - a_j) E_j`.
* `MMP.Flips.IsFig3Type1`: type (1), `B = 0` and `Γ(f)` a chain (FA Fig. 3 (1); 3.2.1).
* `MMP.Flips.IsFig3Type2`: type (2), `B = 0` and `Γ(f)` a star with three arms of determinants
  `{2, 2, m}`, `{2, 3, 3}`, `{2, 3, 4}` or `{2, 3, 5}` (FA Fig. 3 (2); 3.2.2).
* `MMP.Flips.IsFig3Type3`: type (3), one boundary point at the end of a chain (FA Fig. 3 (3)).
* `MMP.Flips.IsFig3Type9`: type (9), two boundary points at the two ends of a chain
  (FA Fig. 3 (9); 3.3.2).
* `MMP.Flips.IsFig3Type10`: type (10), a forked chain with one boundary point
  (FA Fig. 3 (10)).

## Main results

* `MMP.Flips.isGermLogDiscrepancyVector_iff`: `a` is a log discrepancy vector on `g` iff
  `((K_Y + Θ_{g,a}) · E_i) = 0` for every `i`.

## Implementation notes

*The minimal resolution.* As in `MMP.Flips.IsMinimalWeightedDualGraph`, "the" minimal
resolution `f` is used existentially. In types (3), (9) and (10) one and the same minimal
resolution `f`, with one enumeration `E_1, …, E_n` of its exceptional curves, carries both
`Γ(f)` and `Γ^*(f)`: `MMP.Flips.IsExtendedDualGraph` contains the statement that the
`∘`-vertices of `Γ^*(f)` form `Γ(f)` for this `f` and `E`. The number `n` is the number of
exceptional curves of that `f` (`MMP.Flips.IsExceptionalCurveEnumeration`).

*Boundary points.* "`Γ^*(f)` has exactly one (two) boundary point(s)" is an enumeration
`Fin 1 → _` (`Fin 2 → _`) of the boundary points, each listed exactly once. "Joined by an edge
of weight `1` to `w_1` and to no other vertex" is: the edge weight between that `•`-vertex and
the `∘`-vertex `v_j` is `1` if `v_j = w_1` and `0` otherwise.

*Chains.* "`Γ(f)` is a weighted chain `w_1, …, w_s`" is an enumeration `e : Fin n ≃ Fin n`
(`w_{i+1} = v_{e i}`, so `s = n`) with `MMP.Flips.WeightedGraph.IsChainOrder`.

*Type (10).* The vertices `w_1, …, w_s, u_1, u_2` are an enumeration `e : Fin (s + 2) ≃ Fin n`,
`e i = w_{i+1}` for `i < s`, `e s = u_1`, `e (s + 1) = u_2`, and the edges are given by
`MMP.Flips.fig3Type10Adj`: `w_i w_{i+1}`, `w_s u_1`, `w_s u_2` and no others.

*Smooth points of curves, multiplicities, the blow-up.* In the `n = 0` branch of type (3),
"the curve `C` is smooth at `P`" is read as: the local ring `𝒪_{C,P} = 𝒪_{X,P} / I_{C,P}` is a
regular local ring, as for Kollár's nonsingular points (Kollár 1.19; see
`MMP.Resolution.PointBlowupSequence.IsWeakEmbeddedResolution`). Over the algebraically closed
(so perfect) field `k`, for a curve of finite type over `k` this is smoothness over `k` at `P`.
In the `n = 0` branch of type (9), `mult_P B = ∑ bᵢ mult_P Bᵢ` with
`mult_P Bᵢ = ord(I_{Bᵢ,P})` (`MMP.Resolution.multAt`, Kollár 1.38), the blow-up of `P` is
`AlgebraicGeometry.blowUp` of the reduced point with exceptional curve
`AlgebraicGeometry.exceptionalIdeal`, and the birational transform of `B` is
`∑ bᵢ (Bᵢ)₁` with `(Bᵢ)₁` the birational transform `MMP.Resolution.birationalTransform` of the
curve `Bᵢ` (Kollár 1.38). As a set it is the union of the supports of the `(Bᵢ)₁`, all `bᵢ`
being nonzero; "meets the exceptional curve in two distinct points" is: this set meets the
support of the exceptional curve in exactly two points.

*Θ_{g,a}.* `MMP.Flips.logPullbackBoundary` is defined for every morphism `g`, list `E` of prime
divisors and vector `a`; the source considers it for a resolution `g` of `(X, P)` with
exceptional curves `E`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], (3.1.4),
  (3.1.5), (3.1.14), (3.2.1), (3.2.2), (3.3.2), Fig. 3
* [J. Kollár, *Lectures on resolution of singularities*], 1.19, 1.36, 1.38
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace MMP.Flips

open MMP.Mori

/-! ### The boundary `Θ_{g,a}` -/

section Theta

variable {X Y : Scheme.{u}}

/-- The `ℚ`-divisor `Θ_{g,a} := g⁻¹_* B + ∑_{j=1}^n (1 - a_j) E_j` on `Y` (implicit in FA 3.1.4,
3.1.5, 3.3.2), for a resolution `g : Y ⟶ X` of `(X, P)` with exceptional curves
`E_1, …, E_n` and `a ∈ ℚ^n`. -/
@[mmp "def_fa3_log_pullback_boundary"]
def logPullbackBoundary (g : Y ⟶ X) (B : QDivisor X) {n : ℕ}
    (E : Fin n → Mori.PrimeDivisor Y) (a : Fin n → ℚ) : QDivisor Y :=
  inverseTransformDivisor g B + ∑ j, Finsupp.single (E j) (1 - a j)

variable {k : Type u} [Field k] (sX : X ⟶ Spec (.of k)) (P : X) (B : QDivisor X) (g : Y ⟶ X)
  [QuasiCompact (g ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y] {n : ℕ}
  (E : Fin n → Mori.PrimeDivisor Y)

/-- `a` is a log discrepancy vector of `(X, P; B)` on `g` iff
`((K_Y + Θ_{g,a}) · E_i) = 0` for every `i` and every canonical divisor `K_Y` (FA 3.0.2,
3.1.4). -/
@[mmp "def_fa3_log_pullback_boundary"]
theorem isGermLogDiscrepancyVector_iff (a : Fin n → ℚ) :
    IsGermLogDiscrepancyVector sX P B g E a ↔
      IsSurfaceGermWithBoundary sX P B ∧ IsGermResolution sX P g ∧
        IsExceptionalCurveEnumeration g P E ∧
        ∀ K : Divisor Y, K.IsCanonicalDivisor (g ≫ sX) 2 → ∀ i,
          IsIntersectionNumber (g ≫ sX)
            (Divisor.toQDivisor K + logPullbackBoundary g B E a) (E i).idealSheaf 0 := by
  simp only [IsGermLogDiscrepancyVector, logPullbackBoundary, add_assoc]

end Theta

/-! ### Types (1) and (2): `B = 0` -/

section Types

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- `(X, P; B)` is of *type (1)* (FA Fig. 3 (1); 3.2.1) if `B = 0` and `Γ(f)` is a weighted chain
with all weights `≥ 2` (possibly empty), `f` the minimal resolution. -/
@[mmp "def_fa3_fig3_case1"]
def IsFig3Type1 (P : X) (B : QDivisor X) : Prop :=
  B = 0 ∧ ∃ (n : ℕ) (Γ : WeightedGraph (Fin n)), IsMinimalWeightedDualGraph sX P B Γ ∧
    Γ.IsWeightedChain ∧ ∀ j, 2 ≤ Γ.weight j

/-- `(X, P; B)` is of *type (2)* (FA Fig. 3 (2); 3.2.2.1–3.2.2.4) if `B = 0` and `Γ(f)` is a
star with three arms `Γ_1, Γ_2, Γ_3`, all weights `≥ 2`, and the multiset
`{Δ_1, Δ_2, Δ_3}` (`Δ_i = Δ(Γ_i)`) is `{2, 2, m}` for some `m ≥ 2`, or `{2, 3, 3}`,
`{2, 3, 4}` or `{2, 3, 5}`, `f` the minimal resolution. -/
@[mmp "def_fa3_fig3_case2"]
def IsFig3Type2 (P : X) (B : QDivisor X) : Prop :=
  B = 0 ∧ ∃ (n : ℕ) (Γ : WeightedGraph (Fin n)) (v : Fin n) (arms : Fin 3 → Finset (Fin n)),
    IsMinimalWeightedDualGraph sX P B Γ ∧ Γ.IsStar v arms ∧ (∀ j, 2 ≤ Γ.weight j) ∧
    let Δ : Multiset ℤ := {Γ.delta (arms 0), Γ.delta (arms 1), Γ.delta (arms 2)}
    (∃ m : ℤ, 2 ≤ m ∧ Δ = {2, 2, m}) ∨ Δ = {2, 3, 3} ∨ Δ = {2, 3, 4} ∨ Δ = {2, 3, 5}

/-! ### Types (3) and (9): chains with boundary points at the ends -/

/-- `(X, P; B)` is of *type (3)* (FA Fig. 3 (3)), `f : Y ⟶ X` the minimal resolution with
exceptional curves `E_1, …, E_n`, if either `n = 0` and `B` has exactly one component `C`,
smooth at `P` (`𝒪_{C,P}` is a regular local ring); or `n ≥ 1`, `Γ(f)` is a weighted chain
`w_1, …, w_s` with all weights `≥ 2`, and `Γ^*(f)` has exactly one boundary point, joined by an
edge of weight `1` to `w_1` and to no other vertex. -/
@[mmp "def_fa3_fig3_case3"]
def IsFig3Type3 (P : X) (B : QDivisor X) : Prop :=
  IsSurfaceGermWithBoundary sX P B ∧
  ∃ (Y : Scheme.{u}) (f : Y ⟶ X) (_ : QuasiCompact (f ≫ sX)) (_ : IsLocallyNoetherian Y)
    (_ : IsNormal Y) (n : ℕ) (E : Fin n → Mori.PrimeDivisor Y),
    IsMinimalGermResolution sX P f ∧ IsExceptionalCurveEnumeration f P E ∧
    ((n = 0 ∧ ∃ C : Mori.PrimeDivisor X, B.support = {C} ∧
        IsRegularLocalRing (X.presheaf.stalk P ⧸ IdealSheafData.stalk C.idealSheaf P)) ∨
      ∃ (hn : 1 ≤ n) (pt : Fin 1 → Mori.PrimeDivisor Y × Y)
        (Γ : ExtendedWeightedGraph (Fin n) (Fin 1)) (e : Fin n ≃ Fin n),
        IsExtendedDualGraph sX P B f E pt Γ ∧ Γ.toWeightedGraph.IsChainOrder e ∧
        (∀ j, 2 ≤ Γ.toWeightedGraph.weight j) ∧
        ∀ j, Γ.boundaryEdgeWeight j 0 = if j = e ⟨0, hn⟩ then 1 else 0)

/-- `(X, P; B)` is of *type (9)* (FA Fig. 3 (9); 3.3.2), `f : Y ⟶ X` the minimal resolution
with exceptional curves `E_1, …, E_n`, if either `n = 0`, `mult_P B = 2` and the birational
transform of `B` on the blow-up of `P` meets the exceptional curve in two distinct points; or
`n ≥ 1`, `Γ(f)` is a weighted chain `w_1, …, w_s` with all weights `≥ 2`, and `Γ^*(f)` has
exactly two boundary points `(C_1, y_1)`, `(C_2, y_2)`, with `y_1 ≠ y_2`, the first joined by
an edge of weight `1` to `w_1` only and the second by an edge of weight `1` to `w_s` only.

Here `mult_P B = ∑ bᵢ mult_P Bᵢ`, the multiplicities `mult_P Bᵢ` being finite, and the
birational transform `∑ bᵢ (Bᵢ)₁` meets the exceptional curve `E` in exactly two points:
`(⋃ᵢ (Bᵢ)₁) ∩ E` has exactly two elements. -/
@[mmp "def_fa3_fig3_case9"]
def IsFig3Type9 (P : X) (B : QDivisor X) : Prop :=
  IsSurfaceGermWithBoundary sX P B ∧
  ∃ (Y : Scheme.{u}) (f : Y ⟶ X) (_ : QuasiCompact (f ≫ sX)) (_ : IsLocallyNoetherian Y)
    (_ : IsNormal Y) (n : ℕ) (E : Fin n → Mori.PrimeDivisor Y),
    IsMinimalGermResolution sX P f ∧ IsExceptionalCurveEnumeration f P E ∧
    ((n = 0 ∧ ∃ (hP : IsClosed ({P} : Set X)) (m : Mori.PrimeDivisor X → ℕ),
        (∀ C ∈ B.support, MMP.Resolution.multAt C.idealSheaf P = m C) ∧
        ∑ C ∈ B.support, B C * m C = 2 ∧
        ((⋃ C ∈ B.support,
            SetLike.coe (MMP.Resolution.birationalTransform P hP C.idealSheaf).support) ∩
          SetLike.coe (exceptionalIdeal
            (Scheme.IdealSheafData.vanishingIdeal ⟨{P}, hP⟩)).support).ncard = 2) ∨
      ∃ (hn : 1 ≤ n) (pt : Fin 2 → Mori.PrimeDivisor Y × Y)
        (Γ : ExtendedWeightedGraph (Fin n) (Fin 2)) (e : Fin n ≃ Fin n),
        IsExtendedDualGraph sX P B f E pt Γ ∧ Γ.toWeightedGraph.IsChainOrder e ∧
        (∀ j, 2 ≤ Γ.toWeightedGraph.weight j) ∧ (pt 0).2 ≠ (pt 1).2 ∧
        (∀ j, Γ.boundaryEdgeWeight j 0 = if j = e ⟨0, hn⟩ then 1 else 0) ∧
        ∀ j, Γ.boundaryEdgeWeight j 1 = if j = e ⟨n - 1, by omega⟩ then 1 else 0)

/-! ### Type (10) -/

/-- The edges of the graph of FA Fig. 3 (10) on the vertices `Fin (s + 2)`, where `i < s` stands
for `w_{i+1}`, `s` for `u_1` and `s + 1` for `u_2`: `w_i w_{i+1}` (`1 ≤ i < s`), `w_s u_1` and
`w_s u_2`. -/
@[mmp "def_fa3_fig3_case10"]
def fig3Type10Adj (s : ℕ) (i j : Fin (s + 2)) : Prop :=
  ((i : ℕ) + 1 = j ∧ (j : ℕ) < s) ∨ ((j : ℕ) + 1 = i ∧ (i : ℕ) < s) ∨
    ((i : ℕ) + 1 = s ∧ s ≤ (j : ℕ)) ∨ ((j : ℕ) + 1 = s ∧ s ≤ (i : ℕ))

/-- The adjacency relation `fig3Type10Adj s` is decidable. -/
instance (s : ℕ) (i j : Fin (s + 2)) : Decidable (fig3Type10Adj s i j) := by
  unfold fig3Type10Adj; infer_instance

/-- `(X, P; B)` is of *type (10)* (FA Fig. 3 (10)), `f : Y ⟶ X` the minimal resolution with
exceptional curves `E_1, …, E_n`, if `n ≥ 1`, `Γ(f)` is the rational tree with vertices
`w_1, …, w_s` (`s ≥ 1`), `u_1, u_2`, edges `w_i w_{i+1}`, `w_s u_1`, `w_s u_2` (and no others),
and `n(u_1) = n(u_2) = 2`, and `Γ^*(f)` has exactly one boundary point, joined by an edge of
weight `1` to `w_1` and to no other vertex. The vertices are listed by `e : Fin (s + 2) ≃ Fin n`
with `e i = w_{i+1}` for `i < s`, `e s = u_1` and `e (s + 1) = u_2`. -/
@[mmp "def_fa3_fig3_case10"]
def IsFig3Type10 (P : X) (B : QDivisor X) : Prop :=
  ∃ (Y : Scheme.{u}) (f : Y ⟶ X) (_ : QuasiCompact (f ≫ sX)) (_ : IsLocallyNoetherian Y)
    (_ : IsNormal Y) (n : ℕ) (E : Fin n → Mori.PrimeDivisor Y),
    IsMinimalGermResolution sX P f ∧ IsExceptionalCurveEnumeration f P E ∧ 1 ≤ n ∧
    ∃ (s : ℕ) (hs : 1 ≤ s) (e : Fin (s + 2) ≃ Fin n) (pt : Fin 1 → Mori.PrimeDivisor Y × Y)
      (Γ : ExtendedWeightedGraph (Fin n) (Fin 1)),
      IsExtendedDualGraph sX P B f E pt Γ ∧ Γ.toWeightedGraph.IsRationalTree ∧
      (∀ i j, i ≠ j → Γ.toWeightedGraph.edgeWeight (e i) (e j) =
        if fig3Type10Adj s i j then 1 else 0) ∧
      Γ.toWeightedGraph.weight (e (Fin.last s).castSucc) = 2 ∧
      Γ.toWeightedGraph.weight (e (Fin.last (s + 1))) = 2 ∧
      ∀ j, Γ.boundaryEdgeWeight j 0 = if j = e ⟨0, by omega⟩ then 1 else 0

end Types

end MMP.Flips
