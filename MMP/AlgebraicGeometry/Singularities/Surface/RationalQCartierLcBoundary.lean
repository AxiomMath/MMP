module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.PairClasses
public import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGerm
public import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGermTypes
public import MMP.AlgebraicGeometry.Singularities.Basic
import MMP.AlgebraicGeometry.MMP.Abundance.Defs
import MMP.Combinatorics.WeightedGraph.BranchValues
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Singularities.Surface.SingleCurveTangencyNotLc
import MMP.AlgebraicGeometry.Singularities.Surface.NoetherFormulaLcObstruction
import MMP.AlgebraicGeometry.Singularities.Surface.WeightedDualGraph
import MMP.AlgebraicGeometry.Intersection.Surface.BlowupGenusDropAdjunction
import MMP.AlgebraicGeometry.Singularities.Surface.LcRationalTree
import MMP.AlgebraicGeometry.Singularities.Surface.RationalNumericallyTrivialPrincipal
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBirationalTransform
import MMP.AlgebraicGeometry.Singularities.Surface.WeightedGraphLogDiscrepancy
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.NormalThreefoldSlice
import MMP.AlgebraicGeometry.Singularities.Surface.DualGraphBoundaryDegree
import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor

/-!
# Rational surface singularities and log canonical germs with reduced boundary

This file proves two results of FA Chapter 3 on surface germs over an algebraically closed
field `k`.

*Divisors near a rational surface singularity are `ℚ`-Cartier.* Let `(X, P)` be a rational
surface singularity. Then every `ℚ`-divisor `D` on `X` is `ℚ`-Cartier near `P`: on some open
neighbourhood `U` of `P`, `D|_U` is a `ℚ`-linear combination of Cartier divisors; in particular
`K_X + B` is `ℚ`-Cartier near `P` for a surface germ with boundary `(X, P; B)`. Choose `N ≥ 1`
with `N D` integral and let `D'` be its transform on the minimal resolution `f : Y ⟶ X`, with
exceptional curves `E_1, …, E_n`. The intersection matrix `((E_i · E_j))` is negative definite,
so there is a unique `c ∈ ℚ^n` with `((D' + ∑ c_j E_j) · E_i) = 0` for all `i`; for `M ≥ 1`
clearing the denominators of `c`, `L = M D' + ∑ M c_j E_j` is numerically trivial on every
exceptional curve, hence principal, `L = div(φ)`, over a neighbourhood `U` of `P`. The prime
divisors of `U` are curves, not the closed point `P`, so they lie where `f` is an isomorphism,
and `M N D = div(φ)` on `U`.

*Log canonical germs with nonzero reduced boundary* (FA 3.3.1). Let `(X, P; B)` be a surface
germ with boundary, `B ≠ 0` reduced, whose minimal resolution has `n ≥ 1` exceptional curves.
If `(X, B)` is log canonical near `P`, then `(X, P; B)` is of type (3), (9) or (10) of FA
Fig. 3: a chain with one boundary point at an end, a chain with boundary points at its two ends,
or a forked chain with one boundary point at the end opposite the fork. The log discrepancy
vector `a` of the dual graph `Γ` is `≥ 0` and some boundary degree `β_j` is positive, so `Γ` is
a rational tree with integral `β_j`, a chain or a star with three arms. Every boundary point lies
on some exceptional curve and `β_j` is the sum of the weights of the boundary points on `E_j`;
this counts the boundary points. For a chain the list of boundary degrees gives types (3), (10)
and (9); when the two ends of a chain of length two share their boundary point, `Θ_{f,0}` has
multiplicity `3` there and `(X, B)` is not log canonical. For a star, the branch decomposition
of `a_v` shows that two arms are single `(-2)`-vertices and `β` is the indicator of the far end
of the third arm, which is type (10).

## Main results

* `MMP.Flips.IsRationalSurfaceSingularity.exists_isCartierCombination_restrictOpen`: every
  `ℚ`-divisor is a `ℚ`-combination of Cartier divisors on a neighbourhood of a rational
  surface singularity.
* `MMP.Flips.IsSurfaceGermWithBoundary.isFig3Type3_or_isFig3Type9_or_isFig3Type10`: a log
  canonical germ with nonzero reduced boundary is of type (3), (9) or (10).

## Implementation notes

The second statement asks `K|_U` to be a canonical divisor of the neighbourhood `U` of `P`
only. A canonical divisor of `X` with the same restriction to `U` exists: it is the divisor of
the rational top form on `X` which restricts to a top form on `U` with divisor `K|_U`. Log
canonicity near `P` is then expressed with a canonical divisor of `X`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], Chapter 3,
  3.3.1, Fig. 3
* [J. Lipman, *Rational singularities with applications to algebraic surfaces and unique
  factorization*][Lipman1969], §17
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Flips

open MMP.Mori

/-! ## Divisors near a rational surface singularity -/

/-- The exceptional curves of a resolution of a surface germ are finitely many: their supports are
irreducible components of the closed fibre `f⁻¹(P)` of the Noetherian scheme `Y`, and a prime
divisor is determined by its support. -/
private theorem exists_finset_isGermExceptionalCurve {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {P : X} {f : Y ⟶ X} [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y]
    (hf : IsGermResolution sX P f) :
    ∃ S : Finset (MMP.Mori.PrimeDivisor Y), ∀ C, C ∈ S ↔ IsGermExceptionalCurve f P C := by
  classical
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  have : IsNoetherian Y := {}
  obtain ⟨Z, hZf, hZc, hZirr, hZ⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible
      (hf.isSurfaceGerm.2.2.1.preimage f.continuous)
  have key : ∀ C, IsGermExceptionalCurve f P C → C.support ∈ Z := by
    intro C hC
    have hsub : C.support ⊆ ⋃₀ (hZf.toFinset : Set (Set Y)) := by
      rw [hZf.coe_toFinset, ← hZ]; exact hC.1.prop.2
    obtain ⟨W, hW, hCW⟩ := (isIrreducible_iff_sUnion_isClosed.1 hC.1.prop.1) hZf.toFinset
      (fun W hW => hZc W (hZf.mem_toFinset.1 hW)) hsub
    have hW' := hZf.mem_toFinset.1 hW
    have hWF : W ⊆ f.base ⁻¹' {P} := by rw [hZ]; exact Set.subset_sUnion_of_mem hW'
    rw [hC.1.eq_of_le ⟨hZirr W hW', hWF⟩ hCW]
    exact hW'
  have hfin : {C | IsGermExceptionalCurve f P C}.Finite :=
    Set.Finite.of_finite_image (hZf.subset (by rintro _ ⟨C, hC, rfl⟩; exact key C hC))
      (fun C _ C' _ h => AlgebraicGeometry.PrimeDivisor.eq_of_support_eq h)
  exact ⟨hfin.toFinset, fun C => hfin.mem_toFinset⟩

/-- A divisor with a local equation on a nonempty open `W` of an integral scheme has Cartier
restriction to `W`. -/
private theorem isCartier_restrictOpen_of_isLocalEquation {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {D : Divisor Y} {W : Y.Opens}
    {g : (RationalFunctions Y)ˣ} (hg : D.IsLocalEquation W g) (hne : Nonempty W) :
    Divisor.IsCartier (D.restrictOpen W) := by
  have : IsDominant W.ι := Opens.isDominant_ι (W.isOpen.dense (by
    obtain ⟨y⟩ := hne; exact ⟨y.1, y.2⟩))
  intro x
  obtain ⟨g', hg', hφg'⟩ := MMP.Positivity.exists_ord_eq_of_units g
  obtain ⟨φ', hφ'⟩ := MMP.Positivity.exists_units_of_ne_zero
    ((map_ne_zero (functionFieldMap W.ι)).2 hg')
  refine ⟨W.ι ⁻¹ᵁ W, x.2, φ', fun E hE => ?_⟩
  have hP : ((OpenWeilRestriction.primeDivisorMap W.ι E).support ∩ W).Nonempty := by
    rw [← PrimeDivisor.genericPoint_mem_iff]
    exact (congrArg (· ∈ W) (OpenWeilRestriction.genericPoint_primeDivisorMap W.ι E)).mpr
      ((E.genericPoint_mem_iff _).2 hE)
  rw [DivisorWithCoeffs.coeff_restrictOpen, hg _ hP, hφg', hφ',
    MMP.Positivity.ord_functionFieldMap_of_isIso W.ι E _
      (OpenWeilRestriction.genericPoint_primeDivisorMap _ _).symm]

/-- The coefficient of `g⁻¹_*(D)` in `g⁻¹_* B` is that of `D` in `B`. -/
private theorem inverseTransformDivisor_apply_of_eq_some {X Y : Scheme.{u}} {R : Type*}
    [AddCommMonoid R] {g : Y ⟶ X} {D : MMP.Mori.PrimeDivisor X} {C : MMP.Mori.PrimeDivisor Y}
    (hD : inverseTransformPrimeDivisor g D = some C) (B : DivisorWithCoeffs R X) :
    inverseTransformDivisor g B C = B D :=
  MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hD (fun _ hD' =>
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective <|
      (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
        hD').1.symm.trans
      (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hD).1) B

/-- **Divisors near a rational surface singularity are `ℚ`-Cartier.** If `(X, P)` is a rational
surface singularity over an algebraically closed field, then every `ℚ`-divisor `D` on `X` is,
on some open neighbourhood `U` of `P`, a `ℚ`-linear combination of Cartier divisors. -/
@[mmp "lem_fa3_rational_q_cartier"]
public theorem IsRationalSurfaceSingularity.exists_isCartierCombination_restrictOpen
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {P : X}
    [IsLocallyNoetherian X] [IsNormal X] (h : IsRationalSurfaceSingularity sX P)
    (D : QDivisor X) :
    ∃ U : X.Opens, P ∈ U ∧ IsCartierCombination (D.restrictOpen U) := by
  classical
  obtain ⟨Y, f, _, _, _, hmin, -⟩ := id h
  have hres := hmin.1
  have hXn : IsNormalVariety k sX := hres.isSurfaceGerm.1
  have : IsIntegral X := hXn.1.toIsIntegral
  have : IsIntegral Y := hres.isIntegral sX
  have := hres.isSmoothResolution.isProper
  have hsm := hres.isSmoothResolution.isSmoothScheme
  have hb := hres.isSmoothResolution.isBirationalMorphism
  have : IsDominant f := hb.isDominant
  have hYn : IsNormalVariety k (f ≫ sX) := ⟨hres.isVariety, inferInstance⟩
  -- an integral multiple `N D` and its transform `D'` on `Y`
  obtain ⟨N, hN, D₀, hD₀⟩ := exists_pos_smul_eq_toQDivisor D
  set D' : Divisor Y := inverseTransformDivisor f D₀ with hD'def
  -- the exceptional curves `E_1, …, E_n`
  obtain ⟨S, hS⟩ := exists_finset_isGermExceptionalCurve hres
  let e := S.equivFin
  let E : Fin S.card → MMP.Mori.PrimeDivisor Y := fun j => (e.symm j).1
  have hEinj : Function.Injective E := fun a b hab => e.symm.injective (Subtype.ext hab)
  have hEexc : ∀ j, IsGermExceptionalCurve f P (E j) := fun j => (hS _).1 (e.symm j).2
  have hEall : ∀ F, IsGermExceptionalCurve f P F → ∃ j, E j = F := fun F hF =>
    ⟨e ⟨F, (hS F).2 hF⟩, by simp [E]⟩
  choose C hC hCc using fun i => (hEexc i).exists_properCurve hres
  have hneg := MMP.Threefold.Resolution.posDef_neg_intersectionMatrix_of_isBirationalMorphism
    hres.isVariety hsm hres.topologicalKrullDim_eq hXn.1 rfl hb E hEinj C hC hCc
  set M : Matrix (Fin S.card) (Fin S.card) ℚ := Matrix.of fun i j =>
    (Divisor.toQDivisor (Finsupp.single (E i) 1)).intersectionNumber k (f ≫ sX) (C j).ι
      (C j).dim_le (MMP.Threefold.Mori.isQCartier_single_of_isSmoothScheme hsm (E i)) with hMdef
  have hM : M.det ≠ 0 := MMP.MatrixPosDef.det_ne_zero_of_posDef_neg_map M hneg
  have hμ : ∀ i j, IsIntersectionNumber (f ≫ sX) (Divisor.toQDivisor (Finsupp.single (E i) 1))
      (E j).idealSheaf (M i j) := fun i j =>
    isIntersectionNumber_of_properCurve _ _ (C j) (E j) (hC j)
  set β : Fin S.card → ℚ := fun j => (Divisor.toQDivisor D').intersectionNumber k (f ≫ sX)
    (C j).ι (C j).dim_le (MMP.Fourfold.isQCartier_of_isSmoothScheme hsm _)
  have hβ : ∀ j, IsIntersectionNumber (f ≫ sX) (Divisor.toQDivisor D') (E j).idealSheaf (β j) :=
    fun j => isIntersectionNumber_of_properCurve _ _ (C j) (E j) (hC j)
  -- the unique solution `c` of `β_j + ∑ c_i (E_i · E_j) = 0`, and a common denominator `m`
  obtain ⟨c, hc, -⟩ := MMP.MatrixPosDef.existsUnique_add_sum_mul_eq_zero M hM β
  set m : ℕ := ∏ i, (c i).den with hmdef
  have hm : 0 < m := Finset.prod_pos fun i _ => (c i).den_pos
  have hint : ∀ i, ∃ a : ℤ, (m : ℚ) * c i = a := by
    intro i
    obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem (fun i => (c i).den) (Finset.mem_univ i)
    refine ⟨(d : ℤ) * (c i).num, ?_⟩
    have h1 : ((c i).den : ℚ) * c i = (c i).num := Rat.den_mul_eq_num _
    have h2 : (m : ℚ) = ((c i).den : ℚ) * d := by exact_mod_cast hd
    push_cast
    rw [h2, ← h1]
    ring
  choose a ha using hint
  set L : Divisor Y := (m : ℤ) • D' + ∑ i, Finsupp.single (E i) (a i) with hLdef
  have hLc : L.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm L
  have hLE : ∀ F : MMP.Mori.PrimeDivisor Y, IsGermExceptionalCurve f P F →
      IsIntersectionNumber (f ≫ sX) (Divisor.toQDivisor L) F.idealSheaf 0 := by
    intro F hF
    obtain ⟨j, rfl⟩ := hEall F hF
    have hsingle : ∀ (i : Fin S.card) (r : ℤ), Divisor.toQDivisor (Finsupp.single (E i) r) =
        (r : ℚ) • Divisor.toQDivisor (Finsupp.single (E i) 1) := by
      intro i r
      ext G
      by_cases hG : E i = G
      · subst hG
        simp [Divisor.toQDivisor, DivisorWithCoeffs.mapCoeffsAddMonoidHom]
      · simp [Divisor.toQDivisor, DivisorWithCoeffs.mapCoeffsAddMonoidHom]
    have hval : IsIntersectionNumber (f ≫ sX) (Divisor.toQDivisor L) (E j).idealSheaf
        (((m : ℤ) : ℚ) * β j + ∑ i, (a i : ℚ) * M i j) := by
      rw [hLdef, map_add, map_sum, map_zsmul, ← Int.cast_smul_eq_zsmul ℚ]
      refine isIntersectionNumber_add ((hβ j).smul _
        (MMP.Fourfold.isQCartier_of_isSmoothScheme hsm _)) (isIntersectionNumber_sum _
          (isIntersectionNumber_zero (hβ j)) fun i _ => ?_)
      rw [hsingle]
      exact (hμ i j).smul _ (MMP.Fourfold.isQCartier_of_isSmoothScheme hsm _)
    have h0 : ((m : ℤ) : ℚ) * β j + ∑ i, (a i : ℚ) * M i j = 0 := by
      simp_rw [← ha]
      calc _ = (m : ℚ) * (β j + ∑ i, c i * M i j) := by
            rw [mul_add, Finset.mul_sum]
            push_cast
            congr 1
            exact Finset.sum_congr rfl fun i _ => by ring
        _ = 0 := by rw [hc j, mul_zero]
    rwa [h0] at hval
  obtain ⟨U, hPU, φ, hφ⟩ :=
    IsMinimalGermResolution.exists_mem_isLocalEquation_preimage h hmin hLc hLE
  -- transfer the local equation to `X`
  obtain ⟨gY, hgY0, hgY⟩ := MMP.Positivity.exists_ord_eq_of_units φ
  obtain ⟨gX, rfl⟩ := hb.functionFieldMap_bijective.2 gY
  obtain ⟨ψ, hψ⟩ := MMP.Positivity.exists_units_of_ne_zero (g := gX)
    (fun h0 => hgY0 (by rw [h0, map_zero]))
  have hloc : ((m : ℤ) • D₀).IsLocalEquation U ψ := by
    intro W hW
    have hWU : W.genericPoint ∈ U := (W.genericPoint_mem_iff U).2 hW
    have hWP : W.genericPoint ≠ P := by
      intro hWP
      have h1 := MMP.Threefold.Resolution.coheight_eq_two_of_isClosed hXn.1
        hres.isSurfaceGerm.2.1 hres.isSurfaceGerm.2.2.1
      rw [← hWP, MMP.Mori.PrimeDivisor.coheight_genericPoint] at h1
      exact absurd h1 (by decide)
    obtain ⟨W', hW'eq, hiso, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hXn hYn hb W
    have hW'U : (W'.support ∩ (f ⁻¹ᵁ U : Set Y)).Nonempty :=
      (W'.genericPoint_mem_iff _).1 (show f W'.genericPoint ∈ U by rwa [hW'eq])
    rw [hψ, ← MMP.Positivity.ord_functionFieldMap_of_isIso f W' W hW'eq, ← hgY W',
      ← hφ W' hW'U]
    obtain ⟨U₀, hU₀, hiso₀⟩ := hres.isIso_away
    have hbir : f W'.genericPoint ∈ biregularLocus f := le_biregularLocus hiso₀ (by
      rw [hW'eq]
      change W.genericPoint ∈ (U₀ : Set X)
      rw [hU₀]
      exact hWP)
    have hinv : inverseTransformPrimeDivisor f W = some W' :=
      MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hW'eq hbir
    have hD'W : D' W' = D₀ W := inverseTransformDivisor_apply_of_eq_some hinv D₀
    have hEW : ∀ i, E i ≠ W' := by
      intro i hi
      apply hWP
      rw [← hW'eq, ← hi]
      exact (hEexc i).1.prop.2 (by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact subset_closure rfl)
    simp [hLdef, DivisorWithCoeffs.coeff_apply, hD'W, hEW]
  refine ⟨U, hPU, 1, fun _ => 1 / ((m : ℚ) * N), fun _ => ((m : ℤ) • D₀).restrictOpen U,
    fun _ => isCartier_restrictOpen_of_isLocalEquation hloc ⟨⟨P, hPU⟩⟩, ?_⟩
  rw [Fin.sum_univ_one]
  ext W
  have h1 := congrArg (fun G : QDivisor X => G (OpenWeilRestriction.primeDivisorMap U.ι W)) hD₀
  simp only [Divisor.toQDivisor, DivisorWithCoeffs.mapCoeffsAddMonoidHom_apply,
    DivisorWithCoeffs.mapCoeffs, Finsupp.smul_apply, Finsupp.mapRange_apply] at h1
  change D.coeff (OpenWeilRestriction.primeDivisorMap U.ι W) = _
  simp only [DivisorWithCoeffs.mapCoeffs]
  change _ = 1 / ((m : ℚ) * N) * (((m : ℤ) • D₀) (OpenWeilRestriction.primeDivisorMap U.ι W) : ℚ)
  rw [Finsupp.smul_apply, smul_eq_mul, Int.cast_mul]
  simp only [Int.coe_castAddHom, zsmul_eq_mul, Int.cast_natCast] at h1
  rw [h1, DivisorWithCoeffs.coeff_apply]
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hN0 : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [Int.cast_natCast]
  field_simp

/-! ## Log canonical germs with nonzero reduced boundary -/

section ReducedBoundary

open Finset

/-! ### Chains and stars -/

section Graph

open MMP.Flips.WeightedGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- A sequence of consecutively adjacent vertices gives a walk through them. -/
private theorem exists_walk_support_eq {G : SimpleGraph V} (f : ℕ → V) :
    ∀ m : ℕ, (∀ t < m, G.Adj (f t) (f (t + 1))) →
      ∃ p : G.Walk (f 0) (f m), p.support = (List.range (m + 1)).map f
  | 0, _ => ⟨SimpleGraph.Walk.nil, by simp⟩
  | m + 1, h => by
    obtain ⟨p, hp⟩ := exists_walk_support_eq f m (fun t ht => h t (by omega))
    refine ⟨p.concat (h m (by omega)), ?_⟩
    rw [SimpleGraph.Walk.support_concat, hp, List.range_succ (n := m + 1), List.map_append]
    simp

/-- In an acyclic graph, the path between the ends of an injective sequence of consecutively
adjacent vertices has the vertices of the sequence as its vertex set. -/
private theorem treePath_eq_image {Γ : WeightedGraph V} (hΓ : Γ.IsAcyclic) (f : ℕ → V) (m : ℕ)
    (h : ∀ t < m, Γ.underlyingGraph.Adj (f t) (f (t + 1)))
    (hinj : ∀ a ≤ m, ∀ b ≤ m, f a = f b → a = b) :
    Γ.treePath (f 0) (f m) = (range (m + 1)).image f := by
  obtain ⟨p, hp⟩ := exists_walk_support_eq f m h
  have hpath : p.IsPath := by
    rw [SimpleGraph.Walk.isPath_def, hp]
    exact List.Nodup.map_on (fun a ha b hb hab => hinj a (Nat.lt_succ_iff.mp (List.mem_range.mp ha))
      b (Nat.lt_succ_iff.mp (List.mem_range.mp hb)) hab) List.nodup_range
  rw [Γ.treePath_eq_support hΓ ⟨p, hpath⟩]
  ext y
  simp [hp]

omit [DecidableEq V] in
/-- Consecutive vertices of a chain are adjacent in `Γ`. -/
private theorem adj_of_isChainOrder {Γ : WeightedGraph V} {C : Finset V} {s : ℕ} {e : Fin s ≃ C}
    (he : (Γ.restrict C).IsChainOrder e) (t : ℕ) (ht : t + 1 < s) :
    Γ.underlyingGraph.Adj (e ⟨t, by omega⟩ : V) (e ⟨t + 1, ht⟩) := by
  have hw := he.edgeWeight_eq ⟨t, by omega⟩ ⟨t + 1, ht⟩
  simp only [true_or, ↓reduceIte] at hw
  refine ⟨fun h => ?_, ?_⟩
  · have := e.injective (Subtype.ext h)
    simp [Fin.ext_iff] at this
  · change 0 < (Γ.restrict C).edgeWeight _ _
    rw [hw]
    exact one_pos

/-- In an acyclic graph, the path from the first vertex `e 0` of a chain `C` to its vertex `e t`
consists of the vertices `e i`, `i ≤ t`. -/
private theorem treePath_chain {Γ : WeightedGraph V} (hΓ : Γ.IsAcyclic) {C : Finset V} {r : ℕ}
    (hr : 0 < r) {e : Fin r ≃ C} (he : (Γ.restrict C).IsChainOrder e) (t : Fin r) :
    Γ.treePath (e ⟨0, hr⟩) (e t) =
      (univ.filter fun i : Fin r => i ≤ t).image fun i => (e i : V) := by
  let f : ℕ → V := fun i => if h : i < r then (e ⟨i, h⟩ : V) else e ⟨0, hr⟩
  have hf : ∀ i (hi : i < r), f i = e ⟨i, hi⟩ := fun i hi => by simp [f, hi]
  have key := treePath_eq_image hΓ f t
    (fun i hi => by
      rw [hf i (by omega), hf (i + 1) (by omega)]
      exact adj_of_isChainOrder he i (by omega))
    (fun a ha b hb hab => by
      rw [hf a (by omega), hf b (by omega)] at hab
      simpa using e.injective (Subtype.ext hab))
  rw [hf 0 hr, hf t t.2] at key
  rw [key]
  ext y
  simp only [mem_image, mem_range, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, by omega⟩, Fin.le_iff_val_le_val.mpr (by simp only [Fin.val_mk]; omega),
      (hf i (by omega)).symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by rw [Fin.le_iff_val_le_val] at hi; omega, hf i i.2⟩

/-- In a chain `C` with all weights `≥ 2`, the vertices strictly beyond position `t` (when there
are any) span a subgraph of determinant at least `2`. -/
private theorem two_le_delta_tail {Γ : WeightedGraph V} (hw : ∀ j, 2 ≤ Γ.weight j)
    {C : Finset V} {r : ℕ} {e : Fin r ≃ C} (he : (Γ.restrict C).IsChainOrder e) (t : Fin r)
    (ht : (t : ℕ) + 1 < r) :
    2 ≤ Γ.delta ((univ.filter fun i : Fin r => t < i).image fun i => (e i : V)) := by
  set R := (univ.filter fun i : Fin r => t < i).image fun i => (e i : V) with hR
  set q := r - 1 - t with hq
  have hmem : ∀ i : Fin q, (e ⟨t + 1 + i, by omega⟩ : V) ∈ R := fun i => by
    rw [hR, mem_image]
    exact ⟨⟨t + 1 + i, by omega⟩, by
      simp only [mem_filter, mem_univ, true_and]
      exact Fin.lt_def.mpr (show (t : ℕ) < t + 1 + i by omega), rfl⟩
  let g : Fin q → R := fun i => ⟨e ⟨t + 1 + i, by omega⟩, hmem i⟩
  have hg : Function.Bijective g := by
    refine ⟨fun i j hij => ?_, fun y => ?_⟩
    · have h0 : ((g i : R) : V) = g j := congrArg Subtype.val hij
      have h1 := e.injective (Subtype.ext h0)
      simp only [Fin.mk.injEq] at h1
      exact Fin.ext (by omega)
    · obtain ⟨y, hy⟩ := y
      rw [hR, mem_image] at hy
      obtain ⟨i, hi, rfl⟩ := hy
      simp only [mem_filter, mem_univ, true_and] at hi
      have hi' : (t : ℕ) < i := Fin.lt_def.mp hi
      refine ⟨⟨i - t - 1, by omega⟩, Subtype.ext ?_⟩
      change (e ⟨t + 1 + (i - t - 1), _⟩ : V) = e i
      congr 2
      exact Fin.ext (by simp only []; omega)
  let g' : Fin q ≃ R := Equiv.ofBijective g hg
  have hchain : (Γ.restrict R).IsChainOrder g' := by
    refine ⟨fun i => he.genus_eq_zero _, fun i j => ?_⟩
    have h := he.edgeWeight_eq ⟨t + 1 + i, by omega⟩ ⟨t + 1 + j, by omega⟩
    change (Γ.restrict C).edgeWeight _ _ = _
    rw [h]
    simp only []
    congr 1
    apply propext
    omega
  have h := add_one_le_det_of_isChainOrder (Γ.restrict R) (by omega) g' hchain (fun w => hw w)
  rw [det_restrict] at h
  omega

omit [DecidableEq V] in
/-- If `w` is the only vertex of `C` adjacent to `v`, then `Γ.branchNeighbor v C = w`. -/
private theorem branchNeighbor_eq {Γ : WeightedGraph V} {v w : V} {C : Finset V} (hw : w ∈ C)
    (hvw : Γ.underlyingGraph.Adj v w) (huniq : ∀ w' ∈ C, Γ.underlyingGraph.Adj v w' → w' = w) :
    Γ.branchNeighbor v C = w := by
  have h : ∃! w, w ∈ C ∧ Γ.underlyingGraph.Adj v w :=
    ⟨w, ⟨hw, hvw⟩, fun w' hw' => huniq w' hw'.1 hw'.2⟩
  classical
  simp only [branchNeighbor, h, ↓reduceDIte]
  exact h.unique h.choose_spec.1 ⟨hw, hvw⟩

/-- In a chain `C` with all weights `≥ 2`, if `Δ(C \ path(e 0, k)) = 1` then `k` is the far end. -/
private theorem eq_last_of_delta_sdiff_treePath_eq_one {Γ : WeightedGraph V} (hac : Γ.IsAcyclic)
    (hw : ∀ j, 2 ≤ Γ.weight j) {C : Finset V} {r : ℕ} (hr : 0 < r) {e : Fin r ≃ C}
    (he : (Γ.restrict C).IsChainOrder e) {k : V} (hk : k ∈ C)
    (h1 : Γ.delta (C \ Γ.treePath (e ⟨0, hr⟩) k) = 1) : k = e ⟨r - 1, by omega⟩ := by
  set t := e.symm ⟨k, hk⟩ with htdef
  have hkt : (e t : V) = k := by simp [t]
  by_contra hne
  have ht : (t : ℕ) + 1 < r := by
    by_contra h
    apply hne
    rw [← hkt]
    congr 2
    exact Fin.ext (by simp only []; omega)
  have hsd : C \ Γ.treePath (e ⟨0, hr⟩) k =
      (univ.filter fun i : Fin r => t < i).image fun i => (e i : V) := by
    rw [← hkt, treePath_chain hac hr he t]
    ext y
    constructor
    · intro hy
      obtain ⟨hyC, hyn⟩ := mem_sdiff.mp hy
      refine mem_image.mpr ⟨e.symm ⟨y, hyC⟩, ?_, by simp⟩
      simp only [mem_filter, mem_univ, true_and]
      by_contra hle
      exact hyn (mem_image.mpr ⟨e.symm ⟨y, hyC⟩, by simpa using not_lt.mp hle, by simp⟩)
    · intro hy
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hy
      simp only [mem_filter, mem_univ, true_and] at hi
      refine mem_sdiff.mpr ⟨(e i).2, fun h => ?_⟩
      obtain ⟨i', hi', he'⟩ := mem_image.mp h
      obtain rfl := e.injective (Subtype.ext he')
      simp only [mem_filter, mem_univ, true_and] at hi'
      exact absurd hi' (not_le.mpr hi)
  have := two_le_delta_tail hw he t ht
  rw [← hsd, h1] at this
  omega

/-- `Γ` with every boundary degree replaced by `0`. -/
private def zeroBoundary (Γ : WeightedGraph V) : WeightedGraph V :=
  { Γ with boundary := fun _ => 0, boundary_nonneg := fun _ => le_rfl }

/-- On a chain attached to `v` at an end, with arbitrary boundary degrees,
`σ(Γ, v, Γ_i) = 1 - ∑_k Δ(Γ_i - path(w_i, v_k)) β_k`. -/
private theorem branchValue_eq_one_sub {Γ : WeightedGraph V} (hs : Γ.HasSimpleEdges) {v : V}
    {C : Finset V} (hC : Γ.IsChainAttachedAtEnd v C) :
    Γ.branchValue v C = 1 - ∑ k ∈ C,
      (Γ.delta (C \ Γ.treePath (Γ.branchNeighbor v C) k) : ℚ) * Γ.boundary k := by
  have hC0 : (zeroBoundary Γ).IsChainAttachedAtEnd v C := by
    obtain ⟨ht, hc, s, hs0, e, he, hadj, hu⟩ := hC
    exact ⟨ht, hc, s, hs0, e, ⟨he.1, he.2⟩, hadj, hu⟩
  have h1 := (zeroBoundary Γ).branchValue_eq_one_of_isChainAttachedAtEnd hs hC0 (fun _ _ => rfl)
  rw [← h1]
  unfold branchValue
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun k _ => ?_
  change _ = (Γ.delta (C \ Γ.treePath (Γ.branchNeighbor v C) k) : ℚ) * (zeroBoundary Γ).c k - _
  simp only [WeightedGraph.c, zeroBoundary]
  ring

/-- A negative definite weighted graph has positive determinant `Δ(Γ) = Δ(V)`. -/
private theorem det_pos {Γ : WeightedGraph V} (hneg : Γ.IsNegDef) : 0 < Γ.det := by
  have h := hneg.delta_pos univ
  rw [← det_restrict, WeightedGraph.det, ← Matrix.det_submatrix_equiv_self
    (Equiv.subtypeUnivEquiv mem_univ).symm] at h
  convert h using 1
  rw [WeightedGraph.det]
  congr 1
  ext x y
  simp only [WeightedGraph.matrix, Matrix.neg_apply, Matrix.of_apply, Matrix.submatrix_apply,
    Equiv.subtypeUnivEquiv_symm_apply, Subtype.ext_iff]
  rfl

/-- If all weights are at least `2`, a chain `C` attached to `v` at an end has `Δ(C) ≥ 2`, and
`Δ(C) = 2` only if `C` is a single vertex of weight `2`. -/
private theorem two_le_delta_and {Γ : WeightedGraph V} (hw' : ∀ j, 2 ≤ Γ.weight j) {v : V}
    {C : Finset V} (hC : Γ.IsChainAttachedAtEnd v C) :
    2 ≤ Γ.delta C ∧ (Γ.delta C = 2 → ∃ u, C = {u} ∧ Γ.weight u = 2) := by
  obtain ⟨-, -, s, hs, e, he, -, -⟩ := hC
  have hw : ∀ w, 2 ≤ (Γ.restrict C).weight w := fun w => hw' w
  refine ⟨?_, fun h2 => ?_⟩
  · have := add_one_le_det_of_isChainOrder (Γ.restrict C) hs e he hw
    unfold WeightedGraph.delta
    omega
  · obtain ⟨rfl, hwt⟩ := (det_eq_two_iff_of_isChainOrder (Γ.restrict C) hs e he hw).1 h2
    exact ⟨e 0, eq_singleton_iff_unique_mem.2 ⟨(e 0).2, fun x hx =>
      congrArg Subtype.val (e.symm_apply_eq.1 (Subsingleton.elim (e.symm ⟨x, hx⟩) 0))⟩, hwt⟩

/-- The arithmetic of the star case: with `Δ_i ≥ 2`, integers `b_i ≥ 0` and
`1 + β_v ≤ ∑ (1 - b_i)/Δ_i`, `b_0 ≥ 1` forces `β_v = 0`, `b = (1, 0, 0)` and `Δ_1 = Δ_2 = 2`. -/
private theorem star_arith {Δ₀ Δ₁ Δ₂ : ℚ} (h₀ : 2 ≤ Δ₀) (h₁ : 2 ≤ Δ₁) (h₂ : 2 ≤ Δ₂)
    {nv b₀ b₁ b₂ : ℕ}
    (h : 1 + (nv : ℚ) ≤ (1 - b₀) / Δ₀ + (1 - b₁) / Δ₁ + (1 - b₂) / Δ₂) (hb : 1 ≤ b₀) :
    nv = 0 ∧ b₀ = 1 ∧ b₁ = 0 ∧ b₂ = 0 ∧ Δ₁ = 2 ∧ Δ₂ = 2 := by
  have hb₀ : (1 : ℚ) ≤ b₀ := by exact_mod_cast hb
  have t0 : (1 - b₀) / Δ₀ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  have key : ∀ {Δ : ℚ} {b : ℕ}, 2 ≤ Δ → (1 - b) / Δ ≤ 1 / Δ ∧ 1 / Δ ≤ 1 / 2 ∧
      (1 ≤ b → (1 - b) / Δ ≤ 0) := by
    intro Δ b hΔ
    refine ⟨div_le_div_of_nonneg_right (by have := b.cast_nonneg (α := ℚ); linarith)
      (by linarith), one_div_le_one_div_of_le (by norm_num) hΔ, fun hb => ?_⟩
    have : (1 : ℚ) ≤ b := by exact_mod_cast hb
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  obtain ⟨a₁, c₁, d₁⟩ := key (b := b₁) h₁
  obtain ⟨a₂, c₂, d₂⟩ := key (b := b₂) h₂
  have hnv : (nv : ℚ) ≤ 0 := by linarith
  have hb₁ : b₁ = 0 := by
    by_contra hne
    have := d₁ (Nat.one_le_iff_ne_zero.mpr hne)
    linarith [nv.cast_nonneg (α := ℚ)]
  have hb₂ : b₂ = 0 := by
    by_contra hne
    have := d₂ (Nat.one_le_iff_ne_zero.mpr hne)
    linarith [nv.cast_nonneg (α := ℚ)]
  subst hb₁ hb₂
  simp only [Nat.cast_zero, sub_zero] at h
  have hΔ₁ : 1 / 2 ≤ 1 / Δ₁ := by linarith [nv.cast_nonneg (α := ℚ)]
  have hΔ₂ : 1 / 2 ≤ 1 / Δ₂ := by linarith [nv.cast_nonneg (α := ℚ)]
  have e₁ : Δ₁ ≤ 2 := by
    rw [div_le_div_iff₀ (by norm_num) (by linarith)] at hΔ₁; linarith
  have e₂ : Δ₂ ≤ 2 := by
    rw [div_le_div_iff₀ (by norm_num) (by linarith)] at hΔ₂; linarith
  have hz : 0 ≤ (1 - b₀) / Δ₀ := by linarith [nv.cast_nonneg (α := ℚ)]
  have hb₀' : (b₀ : ℚ) ≤ 1 := by
    have := (div_nonneg_iff.mp hz)
    rcases this with ⟨h1, -⟩ | ⟨-, h2⟩
    · linarith
    · linarith
  refine ⟨by exact_mod_cast le_antisymm (by exact_mod_cast hnv) (Nat.zero_le _),
    le_antisymm (by exact_mod_cast hb₀') hb, rfl, rfl, le_antisymm e₁ h₁, le_antisymm e₂ h₂⟩

/-- A finite sum of natural numbers equal to `1` has exactly one nonzero term, equal to `1`. -/
private theorem exists_eq_one_of_sum_eq_one {ι : Type*} {s : Finset ι} {f : ι → ℕ}
    (h : ∑ i ∈ s, f i = 1) : ∃ i ∈ s, f i = 1 ∧ ∀ j ∈ s, j ≠ i → f j = 0 := by
  classical
  obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h.symm ▸ one_ne_zero)
  have hle : f i ≤ 1 := h ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
  refine ⟨i, hi, by omega, fun j hj hji => ?_⟩
  have := Finset.sum_le_sum_of_subset_of_nonneg (f := f)
    (insert_subset hj (singleton_subset_iff.mpr hi))
    (fun _ _ _ => Nat.zero_le _)
  rw [sum_pair hji, h] at this
  omega

/-- Let `w j l ∈ ℕ` be such that every `l` has some `w j l ≥ 1`. If the row sums
`∑_l w j l` are the indicator of `j₀`, then there is exactly one index `l`, and `w · l` is
the indicator of `j₀`. -/
private theorem exists_eq_one_and_apply_eq_ite {ι : Type*} [DecidableEq ι] {m : ℕ}
    {w : ι → Fin m → ℕ} (hon : ∀ l, ∃ j, 1 ≤ w j l) {j₀ : ι}
    (hN : ∀ j, ∑ l, w j l = if j = j₀ then 1 else 0) :
    ∃ hm : m = 1, ∀ j, w j (Fin.cast hm.symm 0) = if j = j₀ then 1 else 0 := by
  have hz : ∀ j, j ≠ j₀ → ∀ l, w j l = 0 := fun j hj l =>
    sum_eq_zero_iff.mp ((hN j).trans (if_neg hj)) l (mem_univ l)
  obtain ⟨l₀, -, hl₀, hl₀z⟩ := exists_eq_one_of_sum_eq_one ((hN j₀).trans (if_pos rfl))
  have hall : ∀ l, l = l₀ := fun l => by
    obtain ⟨j, hj⟩ := hon l
    by_contra hne
    by_cases hjj : j = j₀
    · rw [hjj, hl₀z l (mem_univ l) hne] at hj; omega
    · rw [hz j hjj l] at hj; omega
  have hm : m = 1 := by simpa using Fintype.card_eq_one_iff.mpr ⟨l₀, hall⟩
  refine ⟨hm, fun j => ?_⟩
  rw [hall (Fin.cast hm.symm 0)]
  by_cases hjj : j = j₀
  · rw [if_pos hjj, hjj, hl₀]
  · rw [if_neg hjj, hz j hjj]

/-- Let `w j l ∈ ℕ` be such that every `l` has some `w j l ≥ 1`. If the row sums
`∑_l w j l` are the sum of the indicators of `j₁ ≠ j₂`, then there are at most two indices
`l₁, l₂` with `w j₁ l₁ = w j₂ l₂ = 1`, and when they differ `w · l_i` is the indicator of `j_i`. -/
private theorem exists_pair_of_sum_eq_ite_add_ite {ι : Type*} [DecidableEq ι] {m : ℕ}
    {w : ι → Fin m → ℕ} (hon : ∀ l, ∃ j, 1 ≤ w j l) {j₁ j₂ : ι} (h12 : j₁ ≠ j₂)
    (hN : ∀ j, ∑ l, w j l = (if j = j₁ then 1 else 0) + (if j = j₂ then 1 else 0)) :
    ∃ l₁ l₂, w j₁ l₁ = 1 ∧ w j₂ l₂ = 1 ∧ (∀ l, l = l₁ ∨ l = l₂) ∧
      (l₁ ≠ l₂ → (∀ j, w j l₁ = if j = j₁ then 1 else 0) ∧
        ∀ j, w j l₂ = if j = j₂ then 1 else 0) := by
  obtain ⟨l₁, -, hl₁, hl₁z⟩ := exists_eq_one_of_sum_eq_one ((hN j₁).trans (by simp [h12]))
  obtain ⟨l₂, -, hl₂, hl₂z⟩ :=
    exists_eq_one_of_sum_eq_one ((hN j₂).trans (by simp [Ne.symm h12]))
  have hz : ∀ j, j ≠ j₁ → j ≠ j₂ → ∀ l, w j l = 0 := fun j h1 h2 l =>
    sum_eq_zero_iff.mp ((hN j).trans (by simp [h1, h2])) l (mem_univ l)
  refine ⟨l₁, l₂, hl₁, hl₂, fun l => ?_, fun hne => ⟨fun j => ?_, fun j => ?_⟩⟩
  · obtain ⟨j, hj⟩ := hon l
    by_contra h
    obtain ⟨h1, h2⟩ := not_or.mp h
    by_cases hj1 : j = j₁
    · rw [hj1, hl₁z l (mem_univ l) h1] at hj; omega
    by_cases hj2 : j = j₂
    · rw [hj2, hl₂z l (mem_univ l) h2] at hj; omega
    rw [hz j hj1 hj2 l] at hj; omega
  · by_cases hj1 : j = j₁
    · rw [if_pos hj1, hj1, hl₁]
    by_cases hj2 : j = j₂
    · rw [if_neg hj1, hj2, hl₂z l₁ (mem_univ _) hne]
    · rw [if_neg hj1, hz j hj1 hj2 l₁]
  · by_cases hj2 : j = j₂
    · rw [if_pos hj2, hj2, hl₂]
    by_cases hj1 : j = j₁
    · rw [if_neg hj2, hj1, hl₁z l₂ (mem_univ _) (Ne.symm hne)]
    · rw [if_neg hj2, hz j hj1 hj2 l₂]

/-- **FA 3.3.1, one fork.** Let `Γ` be a negative definite rational tree which is a star with
three arms at `v`, with integral boundary degrees, some `β_j > 0`, and a log discrepancy vector
`a ≥ 0`. Then two arms are single vertices of weight `2`, and `β` is `1` at the end of the third
arm not adjacent to `v` and `0` elsewhere. -/
private theorem boundary_eq_of_isStar {Γ : WeightedGraph V} (hΓ : Γ.IsRationalTree)
    (hneg : Γ.IsNegDef) {v : V} {arms : Fin 3 → Finset V} (hstar : Γ.IsStar v arms)
    (hβ : ∀ j, ∃ n : ℕ, Γ.boundary j = n) (hpos : ∃ j, 0 < Γ.boundary j)
    {a : V → ℚ} (ha : Γ.IsLogDiscrepancyVector a) (ha0 : ∀ k, 0 ≤ a k) :
    ∃ i : Fin 3, (∀ l, l ≠ i → ∃ u, arms l = {u} ∧ Γ.weight u = 2) ∧
      ∃ (r : ℕ) (hr : 0 < r) (e : Fin r ≃ arms i), (Γ.restrict (arms i)).IsChainOrder e ∧
        Γ.underlyingGraph.Adj v (e ⟨0, hr⟩) ∧
        (∀ w ∈ arms i, Γ.underlyingGraph.Adj v w → w = e ⟨0, hr⟩) ∧
        ∀ j, Γ.boundary j = if j = (e ⟨r - 1, by omega⟩ : V) then 1 else 0 := by
  classical
  have hw := hΓ.two_le_weight
  have hs := hstar.hasSimpleEdges
  have hac : Γ.IsAcyclic := hstar.isTree.isAcyclic
  choose n hn using hβ
  choose r hr e he hadj huniq using fun i => (hstar.isChainAttachedAtEnd i).2.2
  set D : Fin 3 → V → ℤ := fun i k => Γ.delta (arms i \ Γ.treePath (e i ⟨0, hr i⟩ : V) k)
    with hD
  have hD1 : ∀ i k, 1 ≤ D i k := fun i k => hneg.delta_pos _
  set bN : Fin 3 → ℕ := fun i => ∑ k ∈ arms i, (D i k).toNat * n k with hbN
  have hσ : ∀ i, Γ.branchValue v (arms i) = 1 - bN i := by
    intro i
    rw [branchValue_eq_one_sub hs (hstar.isChainAttachedAtEnd i),
      branchNeighbor_eq (e i ⟨0, hr i⟩).2 (hadj i) (huniq i)]
    congr 1
    simp only [hbN, Nat.cast_sum, Nat.cast_mul]
    refine sum_congr rfl fun k _ => ?_
    rw [hn k]
    congr 1
    have := hD1 i k
    have h2 : ((D i k).toNat : ℤ) = D i k := Int.toNat_of_nonneg (by omega)
    exact_mod_cast h2.symm
  have hdec := ha.apply_eq_branchValue_of_isTree hneg hs hstar.isTree v arms hstar.isComponent
    hstar.pairwise_disjoint hstar.biUnion_eq
  have hdet : (0 : ℚ) < Γ.det := by exact_mod_cast det_pos hneg
  have hdetv : (0 : ℚ) < (Γ.removeVertex v).det := by
    rw [det_removeSet]; exact_mod_cast hneg.delta_pos _
  have hcv : Γ.c v = -1 - n v := by
    rw [c_eq_of_hasSimpleEdges Γ hs, hΓ.genus_eq_zero, hstar.degree_eq, hn v]
    push_cast
    ring
  have hS : 1 + (n v : ℚ) ≤ ∑ i, (1 - (bN i : ℚ)) / Γ.delta (arms i) := by
    have h0 := ha0 v
    rw [hdec] at h0
    have := (mul_nonneg_iff_of_pos_left (div_pos hdetv hdet)).mp h0
    rw [hcv] at this
    simp only [hσ] at this
    linarith
  have hΔ : ∀ i, (2 : ℚ) ≤ Γ.delta (arms i) := fun i => by
    exact_mod_cast (two_le_delta_and hw (hstar.isChainAttachedAtEnd i)).1
  have hterm : ∀ i, (1 - (bN i : ℚ)) / Γ.delta (arms i) ≤ 1 / 2 := fun i => by
    have h2 := hΔ i
    have hb := (bN i).cast_nonneg (α := ℚ)
    calc (1 - (bN i : ℚ)) / Γ.delta (arms i) ≤ 1 / Γ.delta (arms i) :=
          div_le_div_of_nonneg_right (by linarith) (by linarith)
      _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
  rw [Fin.sum_univ_three] at hS
  have hnv : n v = 0 := by
    have := hterm 0; have := hterm 1; have := hterm 2
    have : (n v : ℚ) < 1 := by linarith
    exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast this)
  -- some arm carries boundary
  have hvmem : ∀ i, v ∉ arms i := fun i =>
    Γ.notMem_of_isComponentOfRemoveVertex (hstar.isComponent i)
  have hmem : ∀ j, j ≠ v → ∃ i, j ∈ arms i := fun j hj => by
    have : j ∈ univ.biUnion arms := by rw [hstar.biUnion_eq]; simp [hj]
    simpa using this
  obtain ⟨i₀, hi₀⟩ : ∃ i, 1 ≤ bN i := by
    obtain ⟨j, hj⟩ := hpos
    have hjv : j ≠ v := by rintro rfl; rw [hn, hnv] at hj; simp at hj
    obtain ⟨i, hi⟩ := hmem j hjv
    refine ⟨i, ?_⟩
    have h1 : (D i j).toNat * n j ≤ bN i :=
      Finset.single_le_sum (f := fun k => (D i k).toNat * n k) (fun _ _ => Nat.zero_le _) hi
    have h2 : 1 ≤ (D i j).toNat := by have := hD1 i j; omega
    have h3 : 1 ≤ n j := by
      rw [hn] at hj
      exact Nat.one_le_iff_ne_zero.mpr (by rintro h; rw [h] at hj; simp at hj)
    nlinarith
  have hres : bN i₀ = 1 ∧ ∀ l, l ≠ i₀ → bN l = 0 ∧ Γ.delta (arms l) = 2 := by
    fin_cases i₀
    · obtain ⟨-, h1, h2, h3, h4, h5⟩ := star_arith (hΔ 0) (hΔ 1) (hΔ 2) hS hi₀
      refine ⟨h1, fun l hl => ?_⟩
      fin_cases l
      · exact absurd rfl hl
      · exact ⟨h2, by exact_mod_cast h4⟩
      · exact ⟨h3, by exact_mod_cast h5⟩
    · obtain ⟨-, h1, h2, h3, h4, h5⟩ := star_arith (nv := n v) (b₀ := bN 1) (b₁ := bN 0)
        (b₂ := bN 2) (hΔ 1) (hΔ 0) (hΔ 2) (by linarith) hi₀
      refine ⟨h1, fun l hl => ?_⟩
      fin_cases l
      · exact ⟨h2, by exact_mod_cast h4⟩
      · exact absurd rfl hl
      · exact ⟨h3, by exact_mod_cast h5⟩
    · obtain ⟨-, h1, h2, h3, h4, h5⟩ := star_arith (nv := n v) (b₀ := bN 2) (b₁ := bN 0)
        (b₂ := bN 1) (hΔ 2) (hΔ 0) (hΔ 1) (by linarith) hi₀
      refine ⟨h1, fun l hl => ?_⟩
      fin_cases l
      · exact ⟨h2, by exact_mod_cast h4⟩
      · exact ⟨h3, by exact_mod_cast h5⟩
      · exact absurd rfl hl
  obtain ⟨hb1, hrest⟩ := hres
  obtain ⟨k₀, hk₀, hk₀1, hk₀z⟩ := exists_eq_one_of_sum_eq_one hb1
  obtain ⟨hDk₀, hnk₀⟩ := mul_eq_one.mp hk₀1
  have hDk₀' : D i₀ k₀ = 1 := by have := hD1 i₀ k₀; omega
  have hlast := eq_last_of_delta_sdiff_treePath_eq_one hac hw (hr i₀) (he i₀) hk₀ hDk₀'
  have hnz : ∀ k ∈ arms i₀, k ≠ k₀ → n k = 0 := fun k hk hkk => by
    have := hk₀z k hk hkk
    have h2 : 1 ≤ (D i₀ k).toNat := by have := hD1 i₀ k; omega
    rcases Nat.mul_eq_zero.mp this with h | h
    · omega
    · exact h
  have hzero : ∀ l, l ≠ i₀ → ∀ k ∈ arms l, n k = 0 := fun l hl k hk => by
    have := (Finset.sum_eq_zero_iff.mp (hrest l hl).1) k hk
    have h2 : 1 ≤ (D l k).toNat := by have := hD1 l k; omega
    rcases Nat.mul_eq_zero.mp this with h | h
    · omega
    · exact h
  refine ⟨i₀, fun l hl => (two_le_delta_and hw (hstar.isChainAttachedAtEnd l)).2 (hrest l hl).2,
    r i₀, hr i₀, e i₀, he i₀, hadj i₀, huniq i₀, fun j => ?_⟩
  rw [hn j, ← hlast]
  by_cases hjv : j = v
  · rw [hjv, hnv, if_neg (fun h : v = k₀ => hvmem i₀ (h ▸ hk₀))]
    simp
  · obtain ⟨l, hl⟩ := hmem j hjv
    by_cases hli : l = i₀
    · subst hli
      by_cases hjk : j = k₀
      · subst hjk; rw [hnk₀, if_pos rfl]; simp
      · rw [hnz j hl hjk, if_neg hjk]; simp
    · have hjk : j ≠ k₀ := fun h =>
        Finset.disjoint_left.mp (hstar.pairwise_disjoint hli) hl (h ▸ hk₀)
      rw [hzero l hli j hl, if_neg hjk]
      simp

/-- The vertex enumeration `w_1, …, w_s, u_1, u_2` of FA Fig. 3 (10) for the weighted graph `Γ`:
the edges are those of `fig3Type10Adj`, `n(u_1) = n(u_2) = 2`, and `β` is `1` at `w_1` and `0`
elsewhere. -/
private def IsFig3Type10Order (Γ : WeightedGraph V) (s : ℕ) (e : Fin (s + 2) ≃ V) : Prop :=
  (∀ i j, i ≠ j → Γ.edgeWeight (e i) (e j) = if fig3Type10Adj s i j then 1 else 0) ∧
    Γ.weight (e (Fin.last s).castSucc) = 2 ∧ Γ.weight (e (Fin.last (s + 1))) = 2 ∧
    ∀ j, Γ.boundary j = if j = e ⟨0, by omega⟩ then 1 else 0

/-- Chain case (b): the chain `w_1, w_2, w_3` with `n(w_1) = n(w_3) = 2` and `β = e_{w_2}` is
the graph of FA Fig. 3 (10) with `s = 1`, middle vertex first. -/
private theorem isFig3Type10Order_of_chain {Γ : WeightedGraph V} {e : Fin 3 ≃ V}
    (he : Γ.IsChainOrder e)
    (hβ : ∀ i : Fin 3, Γ.boundary (e i) = (if (i : ℕ) = 1 then 1 else 0) ∧
      ((i : ℕ) ≠ 1 → Γ.weight (e i) = 2)) :
    IsFig3Type10Order Γ 1 ((Equiv.swap 0 1).trans e) := by
  refine ⟨fun i j hij => ?_, (hβ 0).2 (by decide), (hβ 2).2 (by decide), fun j => ?_⟩
  · simp only [Equiv.trans_apply]
    rw [he.edgeWeight_eq]
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide
  · obtain ⟨i, rfl⟩ := e.surjective j
    rw [(hβ i).1]
    simp only [Equiv.trans_apply, EmbeddingLike.apply_eq_iff_eq]
    fin_cases i <;> decide

/-- In a graph with simple edges, the edge weight between distinct vertices is `1` or `0`
according as they are adjacent. -/
private theorem edgeWeight_eq_ite {Γ : WeightedGraph V} (hs : Γ.HasSimpleEdges) {x y : V}
    (hxy : x ≠ y) : Γ.edgeWeight x y = if Γ.underlyingGraph.Adj x y then 1 else 0 := by
  classical
  split_ifs with h
  · exact (hs x y h).2
  · by_contra hne
    exact h ⟨hxy, Nat.pos_of_ne_zero hne⟩

/-- The star case: a star with three arms at `v`, two of them single vertices `u_1, u_2` of
weight `2` and the third a chain `e 0, …, e (r - 1)` attached at `e 0`, with `β` the indicator
of `e (r - 1)`, is the graph of FA Fig. 3 (10) with `s = r + 1`:
`w_1 = e (r - 1), …, w_r = e 0, w_{r+1} = v`. -/
private theorem exists_isFig3Type10Order_of_isStar {Γ : WeightedGraph V} {v : V}
    {arms : Fin 3 → Finset V} (hstar : Γ.IsStar v arms) {i₀ l₁ l₂ : Fin 3} (h01 : i₀ ≠ l₁)
    (h02 : i₀ ≠ l₂) (h12 : l₁ ≠ l₂) {u₁ u₂ : V} (hu₁ : arms l₁ = {u₁}) (hu₂ : arms l₂ = {u₂})
    (hw₁ : Γ.weight u₁ = 2) (hw₂ : Γ.weight u₂ = 2) {r : ℕ} (hr : 0 < r)
    {e : Fin r ≃ arms i₀} (he : (Γ.restrict (arms i₀)).IsChainOrder e)
    (hadj : Γ.underlyingGraph.Adj v (e ⟨0, hr⟩))
    (huniq : ∀ w ∈ arms i₀, Γ.underlyingGraph.Adj v w → w = e ⟨0, hr⟩)
    (hβ : ∀ j, Γ.boundary j = if j = (e ⟨r - 1, by omega⟩ : V) then 1 else 0) :
    ∃ e' : Fin (r + 1 + 2) ≃ V, IsFig3Type10Order Γ (r + 1) e' := by
  classical
  have hs := hstar.hasSimpleEdges
  have hvmem : ∀ i, v ∉ arms i := fun i =>
    Γ.notMem_of_isComponentOfRemoveVertex (hstar.isComponent i)
  have hcov : ∀ i, i = i₀ ∨ i = l₁ ∨ i = l₂ := by
    intro i
    have := Fin.val_ne_of_ne h01; have := Fin.val_ne_of_ne h02; have := Fin.val_ne_of_ne h12
    have := i.2; have := i₀.2; have := l₁.2; have := l₂.2
    rw [Fin.ext_iff, Fin.ext_iff, Fin.ext_iff]
    omega
  have hdisj : ∀ {i j}, i ≠ j → ∀ x ∈ arms i, x ∉ arms j := fun hij x hx hx' =>
    Finset.disjoint_left.mp (hstar.pairwise_disjoint hij) hx hx'
  have hu₁m : u₁ ∈ arms l₁ := by rw [hu₁]; exact mem_singleton_self _
  have hu₂m : u₂ ∈ arms l₂ := by rw [hu₂]; exact mem_singleton_self _
  have hadjU : ∀ {l u}, arms l = {u} → Γ.underlyingGraph.Adj v u := fun {l u} hlu => by
    obtain ⟨-, -, s', hs', e', -, hadj', -⟩ := hstar.isChainAttachedAtEnd l
    have : (e' ⟨0, hs'⟩ : V) = u := mem_singleton.mp (hlu ▸ (e' ⟨0, hs'⟩).2)
    exact this ▸ hadj'
  -- the enumeration
  let f : Fin (r + 1 + 2) → V := fun i =>
    if h : (i : ℕ) < r then (e ⟨r - 1 - i, by omega⟩ : V)
    else if (i : ℕ) = r then v else if (i : ℕ) = r + 1 then u₁ else u₂
  have hf1 : ∀ (i : Fin (r + 1 + 2)) (h : (i : ℕ) < r), f i = e ⟨r - 1 - i, by omega⟩ :=
    fun i h => by simp [f, h]
  have hf2 : ∀ i : Fin (r + 1 + 2), (i : ℕ) = r → f i = v := fun i h => by simp [f, h]
  have hf3 : ∀ i : Fin (r + 1 + 2), (i : ℕ) = r + 1 → f i = u₁ := fun i h => by simp [f, h]
  have hf4 : ∀ i : Fin (r + 1 + 2), (i : ℕ) = r + 2 → f i = u₂ := fun i h => by
    simp [f, h]
  have hcases : ∀ i : Fin (r + 1 + 2), (i : ℕ) < r ∨ (i : ℕ) = r ∨ (i : ℕ) = r + 1 ∨
      (i : ℕ) = r + 2 := fun i => by omega
  have hmemA : ∀ (i : Fin (r + 1 + 2)) (h : (i : ℕ) < r), f i ∈ arms i₀ := fun i h => by
    rw [hf1 i h]; exact (e _).2
  have hinj : Function.Injective f := by
    intro i j hij
    rcases hcases i with hi | hi | hi | hi <;> rcases hcases j with hj | hj | hj | hj
    all_goals first
      | exact Fin.ext (by omega)
      | skip
    · rw [hf1 i hi, hf1 j hj] at hij
      have := e.injective (Subtype.ext hij)
      simp only [Fin.mk.injEq] at this
      exact Fin.ext (by omega)
    · exact absurd (hf2 j hj ▸ hij ▸ hmemA i hi) (hvmem i₀)
    · exact absurd (hf3 j hj ▸ hij ▸ hmemA i hi) (hdisj (Ne.symm h01) _ hu₁m)
    · exact absurd (hf4 j hj ▸ hij ▸ hmemA i hi) (hdisj (Ne.symm h02) _ hu₂m)
    · exact absurd (hf2 i hi ▸ hij.symm ▸ hmemA j hj) (hvmem i₀)
    · rw [hf2 i hi, hf3 j hj] at hij; exact absurd (hij ▸ hu₁m) (hvmem l₁)
    · rw [hf2 i hi, hf4 j hj] at hij; exact absurd (hij ▸ hu₂m) (hvmem l₂)
    · exact absurd (hf3 i hi ▸ hij.symm ▸ hmemA j hj) (hdisj (Ne.symm h01) _ hu₁m)
    · rw [hf3 i hi, hf2 j hj] at hij; exact absurd (hij ▸ hu₁m) (hvmem l₁)
    · rw [hf3 i hi, hf4 j hj] at hij; exact absurd (hij ▸ hu₁m) (hdisj (Ne.symm h12) _ hu₂m)
    · exact absurd (hf4 i hi ▸ hij.symm ▸ hmemA j hj) (hdisj (Ne.symm h02) _ hu₂m)
    · rw [hf4 i hi, hf2 j hj] at hij; exact absurd (hij ▸ hu₂m) (hvmem l₂)
    · rw [hf4 i hi, hf3 j hj] at hij; exact absurd (hij ▸ hu₂m) (hdisj h12 _ hu₁m)
  have hcard : Fintype.card (Fin (r + 1 + 2)) = Fintype.card V := by
    have hA : #(arms i₀) = r := by
      rw [← Fintype.card_coe, Fintype.card_congr e.symm, Fintype.card_fin]
    have hU : univ = insert v (univ.biUnion arms) := by
      rw [hstar.biUnion_eq]; ext x; by_cases hx : x = v <;> simp [hx]
    have hsum : #(univ.biUnion arms) = r + 2 := by
      rw [card_biUnion (fun i _ j _ hij => hstar.pairwise_disjoint hij)]
      have h3 : ∀ i : Fin 3, #(arms i) = if i = i₀ then r else 1 := fun i => by
        rcases hcov i with rfl | rfl | rfl
        · simp [hA]
        · simp [hu₁, Ne.symm h01]
        · simp [hu₂, Ne.symm h02]
      simp only [h3, Fin.sum_univ_three]
      fin_cases i₀ <;> simp <;> omega
    rw [Fintype.card_fin, ← card_univ (α := V), hU, card_insert_of_notMem (by simp [hvmem]),
      hsum]
  let e' : Fin (r + 1 + 2) ≃ V :=
    Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩)
  have he' : ∀ i, e' i = f i := fun _ => rfl
  -- edge weights
  have hvA : ∀ x ∈ arms i₀, Γ.edgeWeight v x = if x = e ⟨0, hr⟩ then 1 else 0 := by
    intro x hx
    rw [edgeWeight_eq_ite hs (fun h : v = x => hvmem i₀ (h ▸ hx))]
    by_cases hx0 : x = e ⟨0, hr⟩
    · rw [if_pos (hx0 ▸ hadj), if_pos hx0]
    · rw [if_neg (fun h => hx0 (huniq x hx h)), if_neg hx0]
  have hzero : ∀ {i j : Fin 3}, i ≠ j → ∀ x ∈ arms i, ∀ y ∈ arms j, Γ.edgeWeight x y = 0 :=
    fun hij x hx y hy => Γ.edgeWeight_eq_zero_of_isComponentOfRemoveVertex (hstar.isComponent _)
      hx (hdisj (Ne.symm hij) y hy) (fun h => hvmem _ (h ▸ hy))
  have hvU : ∀ {l u}, arms l = {u} → Γ.edgeWeight v u = 1 := fun hlu =>
    (hs _ _ (hadjU hlu)).2
  have key : ∀ i j : Fin (r + 1 + 2), (i : ℕ) < j →
      Γ.edgeWeight (f i) (f j) = if fig3Type10Adj (r + 1) i j then 1 else 0 := by
    intro i j hij
    have hT : ∀ (P : Prop) (_ : P ↔ fig3Type10Adj (r + 1) i j) (n : ℕ) [Decidable P],
        n = (if P then 1 else 0) → n = if fig3Type10Adj (r + 1) i j then 1 else 0 :=
      fun P hP n _ h => h.trans (if_congr hP rfl rfl)
    have hpos : ∀ (_ : fig3Type10Adj (r + 1) i j) (n : ℕ), n = 1 →
        n = if fig3Type10Adj (r + 1) i j then 1 else 0 := fun h n hn => by rw [if_pos h, hn]
    have hneg : ∀ (_ : ¬ fig3Type10Adj (r + 1) i j) (n : ℕ), n = 0 →
        n = if fig3Type10Adj (r + 1) i j then 1 else 0 := fun h n hn => by rw [if_neg h, hn]
    rcases hcases i with hi | hi | hi | hi <;> rcases hcases j with hj | hj | hj | hj
    all_goals try omega
    · rw [hf1 i hi, hf1 j hj]
      have h := he.edgeWeight_eq ⟨r - 1 - i, by omega⟩ ⟨r - 1 - j, by omega⟩
      change Γ.edgeWeight _ _ = _ at h
      refine hT _ ?_ _ h
      simp only [fig3Type10Adj]
      omega
    · rw [hf1 i hi, hf2 j hj, Γ.edgeWeight_symm, hvA _ (e _).2]
      have : ((e ⟨r - 1 - i, by omega⟩ : V) = e ⟨0, hr⟩) ↔ (i : ℕ) + 1 = r := by
        constructor
        · intro h
          have := e.injective (Subtype.ext h)
          simp only [Fin.mk.injEq] at this
          omega
        · intro h
          congr 2
          exact Fin.ext (by simp only []; omega)
      by_cases hir : (i : ℕ) + 1 = r
      · rw [if_pos (this.mpr hir)]
        exact hpos (by simp only [fig3Type10Adj]; omega) _ rfl
      · rw [if_neg (fun h => hir (this.mp h))]
        exact hneg (by simp only [fig3Type10Adj]; omega) _ rfl
    · rw [hf1 i hi, hf3 j hj]
      exact hneg (by simp only [fig3Type10Adj]; omega) _ (hzero h01 _ (e _).2 _ hu₁m)
    · rw [hf1 i hi, hf4 j hj]
      exact hneg (by simp only [fig3Type10Adj]; omega) _ (hzero h02 _ (e _).2 _ hu₂m)
    · rw [hf2 i hi, hf3 j hj]
      exact hpos (by simp only [fig3Type10Adj]; omega) _ (hvU hu₁)
    · rw [hf2 i hi, hf4 j hj]
      exact hpos (by simp only [fig3Type10Adj]; omega) _ (hvU hu₂)
    · rw [hf3 i hi, hf4 j hj]
      exact hneg (by simp only [fig3Type10Adj]; omega) _ (hzero h12 _ hu₁m _ hu₂m)
  refine ⟨e', ⟨fun i j hij => ?_, ?_, ?_, fun j => ?_⟩⟩
  · rw [he', he']
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
    · exact key i j h
    · rw [Γ.edgeWeight_symm, key j i h]
      exact if_congr (by simp only [fig3Type10Adj]; tauto) rfl rfl
  · rwa [he', hf3 _ (by simp)]
  · rwa [he', hf4 _ (by simp)]
  · rw [hβ j, he', hf1 _ (show 0 < r from hr)]
    rfl

omit [DecidableEq V] in
/-- A chain read backwards is a chain. -/
private theorem isChainOrder_revPerm {Γ : WeightedGraph V} {s : ℕ} {e : Fin s ≃ V}
    (he : Γ.IsChainOrder e) : Γ.IsChainOrder (Fin.revPerm.trans e) := by
  refine ⟨fun i => he.1 _, fun i j => ?_⟩
  simp only [Equiv.trans_apply, Fin.revPerm_apply]
  rw [he.2]
  refine if_congr ?_ rfl rfl
  simp only [Fin.val_rev]
  omega

end Graph

/-! ### Boundary points -/

section BoundaryPoints

/-- In a Noetherian space every point `y` of a closed set `F` lies on a maximal irreducible
subset `Z` of `F`, and `F ⊆ Z ∪ C` for a closed set `C` not containing `Z`. -/
private lemma exists_maximal_isIrreducible_subset {T : Type*} [TopologicalSpace T]
    [TopologicalSpace.NoetherianSpace T] {F : Set T} (hF : IsClosed F) {y : T} (hy : y ∈ F) :
    ∃ Z C : Set T, Maximal (fun W : Set T => IsIrreducible W ∧ W ⊆ F) Z ∧ IsClosed Z ∧ y ∈ Z ∧
      IsClosed C ∧ F ⊆ Z ∪ C ∧ ¬ Z ⊆ C := by
  obtain ⟨S, hSfin, hScl, hSirr, hSeq⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hF
  obtain ⟨T₀, hT₀, hyT₀⟩ : y ∈ ⋃₀ S := hSeq ▸ hy
  obtain ⟨Z, hT₀Z, hZ⟩ := hSfin.exists_le_maximal hT₀
  have hZS : Z ∈ S := hZ.prop
  have hZF : Z ⊆ F := hSeq ▸ Set.subset_sUnion_of_mem hZS
  have hsub : ∀ {W : Set T}, IsIrreducible W → ∀ {S' : Set (Set T)}, S' ⊆ S →
      W ⊆ ⋃₀ S' → ∃ t ∈ S', W ⊆ t := by
    intro W hW S' hS' hWS
    have hfin : S'.Finite := hSfin.subset hS'
    obtain ⟨t, ht, hWt⟩ := (isIrreducible_iff_sUnion_isClosed.mp hW) hfin.toFinset
      (fun t ht => hScl t (hS' (hfin.mem_toFinset.mp ht))) (by simpa using hWS)
    exact ⟨t, hfin.mem_toFinset.mp ht, hWt⟩
  have hmax : Maximal (fun W : Set T => IsIrreducible W ∧ W ⊆ F) Z := by
    refine ⟨⟨hSirr Z hZS, hZF⟩, fun W hW hZW => ?_⟩
    obtain ⟨t, htS, hWt⟩ := hsub hW.1 le_rfl (hSeq ▸ hW.2)
    exact (hZ.2 htS (hZW.trans hWt)).trans' hWt
  refine ⟨Z, ⋃₀ (S \ {Z}), hmax, hScl Z hZS, hT₀Z hyT₀,
    (hSfin.subset Set.sdiff_subset).isClosed_sUnion fun t ht => hScl t ht.1, ?_, ?_⟩
  · intro x hx
    obtain ⟨t, htS, hxt⟩ := (hSeq ▸ hx : x ∈ ⋃₀ S)
    by_cases htZ : t = Z
    · exact Or.inl (htZ ▸ hxt)
    · exact Or.inr ⟨t, ⟨htS, htZ⟩, hxt⟩
  · intro hZC
    obtain ⟨t, ⟨htS, htZ⟩, hZt⟩ := hsub (hSirr Z hZS) Set.sdiff_subset hZC
    exact htZ (le_antisymm (hZ.2 htS hZt) hZt)

/-- A prime divisor in the support of `mapPrimeDivisors φ D` is `φ` of some prime divisor. -/
private theorem exists_eq_some_of_mem_support_mapPrimeDivisors {X Y : Scheme.{u}} {R : Type*}
    [AddCommMonoid R] {φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)}
    {D : DivisorWithCoeffs R X} {Q : MMP.Mori.PrimeDivisor Y}
    (hQ : Q ∈ (DivisorWithCoeffs.mapPrimeDivisors φ D).support) : ∃ E, φ E = some Q := by
  classical
  by_contra! h
  refine Finsupp.mem_support_iff.mp hQ ?_
  clear hQ
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' hD hD' => rw [map_add, Finsupp.add_apply, hD, hD', add_zero]
  | single E r =>
    rw [DivisorWithCoeffs.mapPrimeDivisors_single]
    rcases hφ : φ E with _ | Q'
    · rfl
    · simp [show Q' ≠ Q from fun h' => h E (h' ▸ hφ)]

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {P : X} {B : QDivisor X} {f : Y ⟶ X} [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y]
    [IsNormal Y] {n : ℕ} {E : Fin n → MMP.Mori.PrimeDivisor Y} {Γ : WeightedGraph (Fin n)}

/-- If the fibre `f⁻¹(P)` is preconnected and there is at least one exceptional curve, then
`f⁻¹(P)` is the union of the exceptional curves. -/
private lemma exists_mem_support_of_isPreconnected (hΓ : IsWeightedDualGraph sX P B f E Γ)
    (hconn : _root_.IsPreconnected (f.base ⁻¹' {P})) (u : Fin n) {y : Y} (hy : f y = P) :
    ∃ j, y ∈ (E j).support := by
  have hg := hΓ.isGermResolution
  have hE := hΓ.isExceptionalCurveEnumeration
  have hYv := hg.isVariety
  have : IsIntegral Y := hYv.toIsIntegral
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  have : IsNoetherian Y := {}
  have hP : IsClosed ({P} : Set X) := hg.isSurfaceGerm.2.2.1
  have hFcl : IsClosed (f.base ⁻¹' {P}) := hP.preimage f.base.hom.continuous
  obtain ⟨Z, C, hZ, hZcl, hyZ, hCcl, hFZC, hZC⟩ := exists_maximal_isIrreducible_subset hFcl hy
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hZ.prop.1 hZcl
  have hξZ : ξ ∈ Z := hξ.mem
  have hEuF : ((E u).support : Set Y) ⊆ f.base ⁻¹' {P} :=
    (hE.isGermExceptionalCurve u).1.prop.2
  have hξncl : ¬ IsClosed ({ξ} : Set Y) := by
    intro hcl
    have hZξ : Z = {ξ} := by rw [← hξ.def, hcl.closure_eq]
    have hξC : ξ ∉ C := fun h => hZC (hZξ ▸ Set.singleton_subset_iff.mpr h)
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hconn {ξ} C hcl hCcl
        (hZξ ▸ hFZC) (by rw [Set.singleton_inter_eq_empty.mpr hξC, Set.inter_empty]) with h | h
    · exact (((hE.isGermExceptionalCurve u).2).not_subsingleton)
        ((Set.subsingleton_singleton).anti (hEuF.trans h))
    · exact hξC (h (hZ.prop.2 hξZ))
  obtain ⟨c, hcZ, hccl⟩ := hZcl.exists_closed_singleton ⟨ξ, hξZ⟩
  have hcξ : c ≠ ξ := fun h => hξncl (h ▸ hccl)
  have hξc : ξ ⤳ c := hξ.specializes hcZ
  have hco2 := MMP.Threefold.Resolution.coheight_eq_two_of_isClosed hYv
    hg.topologicalKrullDim_eq hccl
  have hξmax : ¬ IsMax ξ := by
    intro hmax
    have : IsIntegral X := hg.isSurfaceGerm.1.1.toIsIntegral
    have := hg.isSmoothResolution.isBirationalMorphism.isDominant
    have h2 : ξ ⤳ genericPoint Y := hmax (genericPoint_specializes ξ)
    have hgη : f (genericPoint Y) = P := hZ.prop.2 (h2.mem_closed hZcl hξZ)
    rw [map_genericPoint_of_isDominant] at hgη
    have : Subsingleton X := ⟨fun a b => by
      have ha := (genericPoint_specializes a).mem_closed hP (by rw [hgη]; rfl)
      have hb := (genericPoint_specializes b).mem_closed hP (by rw [hgη]; rfl)
      rw [Set.mem_singleton_iff] at ha hb
      rw [ha, hb]⟩
    have h0 := topologicalKrullDim_zero_of_discreteTopology X
    rw [hg.isSurfaceGerm.2.1] at h0
    exact absurd h0 (by decide)
  have hco : Order.coheight ξ = 1 := by
    have hcξlt : c < ξ := lt_of_le_not_ge hξc fun h =>
      hcξ ((h : c ⤳ ξ).mem_closed hccl rfl).symm
    have hlt : Order.coheight ξ < 2 := hco2 ▸ Order.coheight_strictAnti hcξlt
      (lt_of_le_of_lt (hco2 ▸ Order.coheight_anti hcξlt.le) (by decide))
    have hne : Order.coheight ξ ≠ 0 := fun h => hξmax (Order.coheight_eq_zero.mp h)
    generalize Order.coheight ξ = d at hlt hne ⊢
    induction d using ENat.recTopCoe with
    | top => exact absurd hlt (by decide)
    | coe d =>
      norm_cast at hlt hne ⊢
      omega
  let D : MMP.Mori.PrimeDivisor Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne ξ hco
  have hDsupp : (D.support : Set Y) = Z := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne, hξ.def]
  obtain ⟨j, hj⟩ := hE.exists_eq D ⟨hDsupp ▸ hZ,
    isCurveIn_idealSheaf_of_topologicalKrullDim_eq_two hYv hg.topologicalKrullDim_eq D⟩
  exact ⟨j, by rwa [hj, hDsupp]⟩

/-- With at least one exceptional curve, every point of `Y` over `P` lies on one of them. -/
private lemma exists_mem_support_of_map_eq (hΓ : IsWeightedDualGraph sX P B f E Γ)
    (hn : 0 < n) {y : Y} (hy : f y = P) : ∃ j, y ∈ (E j).support := by
  have hg := hΓ.isGermResolution
  have : IsProper f := hg.isSmoothResolution.isProper
  exact exists_mem_support_of_isPreconnected hΓ
    ((MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism
      (f ≫ sX) sX hg.isVariety hg.isSurfaceGerm.1 f
      hg.isSmoothResolution.isBirationalMorphism).2 P).isPreconnected ⟨0, hn⟩ hy

/-- A component of `g⁻¹_* B` does not lie over the closed point `P` of a surface germ. -/
private theorem map_genericPoint_ne_of_mem_support (hX : IsSurfaceGerm sX P)
    {C : MMP.Mori.PrimeDivisor Y} (hC : C ∈ (inverseTransformDivisor f B).support) :
    f.base C.genericPoint ≠ P := by
  intro hP
  obtain ⟨D, hD⟩ := exists_eq_some_of_mem_support_mapPrimeDivisors hC
  have h := MMP.Positivity.coheight_map_of_mem_biregularLocus f
    (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hD).2
  rw [hP, MMP.Threefold.Resolution.coheight_eq_two_of_isClosed hX.1.1 hX.2.1 hX.2.2.1,
    C.coheight_genericPoint] at h
  exact absurd h (by decide)

/-- The components of `f⁻¹_* B` have nonnegative coefficients and are not exceptional curves. -/
private theorem nonneg_and_ne_of_mem_support_inverseTransformDivisor
    (hg : IsGermResolution sX P f) (hB : IsSurfaceGermWithBoundary sX P B)
    {E C : MMP.Mori.PrimeDivisor Y} (hE : IsGermExceptionalCurve f P E)
    (hC : C ∈ (inverseTransformDivisor f B).support) :
    0 ≤ inverseTransformDivisor f B C ∧ E ≠ C := by
  obtain ⟨D, hD⟩ := exists_eq_some_of_mem_support_mapPrimeDivisors hC
  refine ⟨inverseTransformDivisor_apply_of_eq_some hD B ▸ (hB.2.2 D).1, fun hEC => ?_⟩
  refine map_genericPoint_ne_of_mem_support hg.isSurfaceGerm hC <| hE.1.prop.2 ?_
  rw [hEC, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact subset_closure rfl

/-- The boundary points of `f` are finitely many. -/
private lemma finite_setOf_isGermBoundaryPoint (hΓ : IsWeightedDualGraph sX P B f E Γ)
    (hn : 0 < n) :
    {p : MMP.Mori.PrimeDivisor Y × Y | IsGermBoundaryPoint f P B p.1 p.2}.Finite := by
  have hg := hΓ.isGermResolution
  have hE := hΓ.isExceptionalCurveEnumeration
  have hfin : ∀ C ∈ (inverseTransformDivisor f B).support, ∀ j,
      ((E j).support ∩ C.support : Set Y).Finite := fun C hC j =>
    (MMP.Mori.isIntersectionNumber_finsum_localIntersectionNumber_of_ne (f ≫ sX) hg.isVariety
      hg.isSmoothResolution.isSmoothScheme hg.topologicalKrullDim_eq
      (nonneg_and_ne_of_mem_support_inverseTransformDivisor hg hΓ.isSurfaceGermWithBoundary
        (hE.isGermExceptionalCurve j) hC).2
      ((hE.isGermExceptionalCurve j).isProper sX hg).2).1
  refine (Set.Finite.biUnion (Finset.finite_toSet (inverseTransformDivisor f B).support)
    fun C hC => Set.Finite.biUnion (Set.finite_univ (α := Fin n)) fun j _ =>
      (Set.finite_singleton C).prod (hfin C hC j)).subset ?_
  rintro ⟨C, y⟩ ⟨hC, hy, hyP⟩
  obtain ⟨j, hj⟩ := exists_mem_support_of_map_eq hΓ hn hyP
  simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ, exists_true_left]
  exact ⟨C, Finsupp.mem_support_iff.mpr hC, j, rfl, hj, hy⟩

/-- The boundary points of `f` can be enumerated, each exactly once. -/
private lemma exists_boundaryPoint_enum (hΓ : IsWeightedDualGraph sX P B f E Γ) (hn : 0 < n) :
    ∃ (m : ℕ) (pt : Fin m → MMP.Mori.PrimeDivisor Y × Y), Function.Injective pt ∧
      (∀ l, IsGermBoundaryPoint f P B (pt l).1 (pt l).2) ∧
      ∀ C y, IsGermBoundaryPoint f P B C y → ∃ l, pt l = (C, y) := by
  have hfin := finite_setOf_isGermBoundaryPoint hΓ hn
  let σ := hfin.toFinset.equivFin
  refine ⟨hfin.toFinset.card, fun l => (σ.symm l).1, fun l l' h =>
    σ.symm.injective (Subtype.ext h), fun l => hfin.mem_toFinset.mp (σ.symm l).2,
    fun C y hCy => ⟨σ ⟨(C, y), hfin.mem_toFinset.mpr hCy⟩, by simp⟩⟩

/-- The extended weighted graph `Γ^*` on `Γ` with `•`-vertices `pt` and edge weights
`(C_l · E_j)_{y_l}` (or `0`). -/
private noncomputable def extGraph (sX : X ⟶ Spec (.of k)) (f : Y ⟶ X)
    (E : Fin n → MMP.Mori.PrimeDivisor Y) (Γ : WeightedGraph (Fin n)) {m : ℕ}
    (pt : Fin m → MMP.Mori.PrimeDivisor Y × Y) : ExtendedWeightedGraph (Fin n) (Fin m) :=
  ⟨Γ, fun j l =>
    haveI := Classical.propDecidable ((pt l).2 ∈ (E j).support)
    if (pt l).2 ∈ (E j).support then
      localIntersectionNumber (f ≫ sX) (pt l).2 (Finsupp.single (pt l).1 1)
        (Finsupp.single (E j) 1)
    else 0⟩

/-- An enumeration of the boundary points gives the extended dual graph. -/
private lemma isExtendedDualGraph_extGraph (hred : IsReducedBoundary B)
    (hΓ : IsWeightedDualGraph sX P B f E Γ) {m : ℕ} {pt : Fin m → MMP.Mori.PrimeDivisor Y × Y}
    (hinj : Function.Injective pt) (hbp : ∀ l, IsGermBoundaryPoint f P B (pt l).1 (pt l).2)
    (hcov : ∀ C y, IsGermBoundaryPoint f P B C y → ∃ l, pt l = (C, y)) :
    IsExtendedDualGraph sX P B f E pt (extGraph sX f E Γ pt) :=
  ⟨hred, hΓ, hinj, hbp, hcov, fun _ _ => rfl⟩

end BoundaryPoints

section Multiplicity

open MMP.Threefold.Resolution MMP.Resolution in
/-- A point common to two distinct prime divisors of a surface is a closed point. -/
private theorem isClosed_singleton_of_mem_inter {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] (hdim : topologicalKrullDim X = 2) {C D : MMP.Mori.PrimeDivisor X} (hCD : C ≠ D)
    {y : X} (hy : y ∈ C.support ∩ D.support) : IsClosed ({y} : Set X) := by
  have hne : y ≠ C.genericPoint := by
    rintro rfl
    exact hCD (MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support D C hy.2).symm
  have hle : y ≤ C.genericPoint := by
    have h := hy.1
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h
    exact specializes_iff_mem_closure.mpr h
  have hlt : y < C.genericPoint := lt_of_le_not_ge hle fun h =>
    hne (Specializes.antisymm (show y ⤳ C.genericPoint from h)
      (show C.genericPoint ⤳ y from hle)).eq
  have h2 := Order.coheight_add_one_le hlt
  rw [MMP.Mori.PrimeDivisor.coheight_genericPoint] at h2
  refine closure_subset_iff_isClosed.mp fun w hw => ?_
  have hwy : w ≤ y := specializes_iff_mem_closure.mpr hw
  by_contra hne
  have hlt' : w < y := lt_of_le_not_ge hwy fun h => hne (Specializes.antisymm
    (show w ⤳ y from h) (show y ⤳ w from hwy)).eq
  have h4 := Order.coheight_add_one_le hlt'
  have h5 := coheight_le_topologicalKrullDim w
  rw [hdim] at h5
  have h6 : (1 : ℕ∞) + 1 + 1 ≤ 2 :=
    (add_le_add h2 (le_refl (1 : ℕ∞))).trans (h4.trans (WithBot.coe_le_coe.mp h5))
  exact absurd h6 (by decide)

/-- On a smooth variety a prime divisor has multiplicity at least one at each of its points. -/
private theorem one_le_toNat_multiplicityAt {k : Type u} [Field k] {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of k)}
    (hsm : IsSmoothScheme sY) (P : MMP.Mori.PrimeDivisor Y) {y : Y} (hy : y ∈ P.support) :
    1 ≤ (P.multiplicityAt y).toNat := by
  have htop := MMP.Threefold.Resolution.multiplicityAt_ne_top P
    (MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsm P) y
  have h1 : (1 : ℕ∞) ≤ P.multiplicityAt y := by
    refine le_iSup₂_of_le (f := fun (m : ℕ) (_ : P.idealSheaf.stalkIdeal y ≤
      IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ m) => (m : ℕ∞)) 1 ?_ (by simp)
    rw [pow_one]
    exact IsLocalRing.le_maximalIdeal
      ((Scheme.IdealSheafData.stalkIdeal_eq_top_iff _).not.mpr (not_not.mpr hy))
  lift P.multiplicityAt y to ℕ using htop with m
  exact_mod_cast h1

/-- If `Θ` is effective, the multiplicities at `x` of any finite set of prime divisors which all
have coefficient `1` in `Θ` sum to at most `mult_x Θ`. -/
private theorem natCast_sum_multiplicityAt_le {Y : Scheme.{u}} {Θ : QDivisor Y} {x : Y}
    (hnn : ∀ D, 0 ≤ Θ D) (S : Finset (MMP.Mori.PrimeDivisor Y)) (hS : ∀ D ∈ S, Θ D = 1) :
    ((∑ D ∈ S, (D.multiplicityAt x).toNat : ℕ) : ℚ) ≤ DivisorWithCoeffs.multiplicityAt Θ x := by
  classical
  have hmult : DivisorWithCoeffs.multiplicityAt Θ x =
      ∑ D ∈ S ∪ Θ.support, (D.multiplicityAt x).toNat • Θ D := by
    unfold DivisorWithCoeffs.multiplicityAt
    exact Finsupp.sum_of_support_subset _ Finset.subset_union_right _ (fun _ _ => smul_zero _)
  rw [hmult, Nat.cast_sum]
  refine le_of_eq_of_le (Finset.sum_congr rfl fun D hD => by rw [hS D hD, nsmul_one])
    (Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      fun D _ _ => nsmul_nonneg (hnn D) _)

end Multiplicity

section DualGraph

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {P : X} {B : QDivisor X} {f : Y ⟶ X} [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y]
    [IsNormal Y] {n : ℕ} {E : Fin n → MMP.Mori.PrimeDivisor Y} {Γ : WeightedGraph (Fin n)}

/-- A common point of `E_j` and `E_l` (`j ≠ l`) makes `v_j` and `v_l` adjacent in `Γ`. -/
private lemma adj_of_mem_inter (hΓ : IsWeightedDualGraph sX P B f E Γ) {j l : Fin n}
    (hjl : j ≠ l) {y : Y} (hy : y ∈ ((E j).support ∩ (E l).support : Set Y)) :
    Γ.underlyingGraph.Adj l j := by
  have hg := hΓ.isGermResolution
  have hCD : E j ≠ E l := fun h => hjl (hΓ.isExceptionalCurveEnumeration.injective h)
  have hC := ((hΓ.isExceptionalCurveEnumeration.isGermExceptionalCurve j).isProper sX hg).2
  obtain ⟨hfin, hI, hpos⟩ := isIntersectionNumber_finsum_localIntersectionNumber_of_ne (f ≫ sX)
    hg.isVariety hg.isSmoothResolution.isSmoothScheme hg.topologicalKrullDim_eq hCD hC
  have heq := (hΓ.edgeWeight l j (Ne.symm hjl)).unique hI
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at heq
  refine ⟨Ne.symm hjl, ?_⟩
  rw [show Γ.edgeWeight l j = _ by exact_mod_cast heq]
  exact Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨y, hfin.mem_toFinset.mpr hy, hpos y hy⟩

/-- A nonzero boundary has a boundary point on any resolution: a component `C` of `B` passes
through `P`, and its transform meets the fibre over `P`. -/
private lemma exists_isGermBoundaryPoint (hΓ : IsWeightedDualGraph sX P B f E Γ)
    (hB0 : B ≠ 0) : ∃ C y, IsGermBoundaryPoint f P B C y := by
  obtain ⟨C, hC⟩ := Finsupp.support_nonempty_iff.mpr hB0
  have hg := hΓ.isGermResolution
  have hB := hΓ.isSurfaceGermWithBoundary
  have hXs := hg.isSurfaceGerm
  have hXv : MMP.Mori.IsNormalVariety k sX := hXs.1
  have : IsProper f := hg.isSmoothResolution.isProper
  have hCc := isCurveIn_idealSheaf_of_topologicalKrullDim_eq_two hXv.1 hXs.2.1 C
  have hηP : C.genericPoint ≠ P := by
    intro h
    refine hCc.not_subsingleton ((Set.subsingleton_singleton (a := P)).anti fun z hz => ?_)
    change z ∈ C.support at hz
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hz
    change z ∈ closure {C.genericPoint} at hz
    rwa [h, hXs.2.2.1.closure_eq] at hz
  have hηV : C.genericPoint ∈ biregularLocus f := by
    obtain ⟨U, hU, hiso⟩ := hg.isIso_away
    refine le_biregularLocus (V := U) hiso ?_
    change C.genericPoint ∈ (U : Set X)
    rw [hU]
    exact hηP
  obtain ⟨C', hC', hgC'⟩ := exists_inverseTransformPrimeDivisor_eq_some C hηV
  have hC'mem : C'.genericPoint ∈ C'.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  obtain ⟨y, hyC', hyP⟩ : ∃ y ∈ C'.support, f y = P := by
    refine (AlgebraicGeometry.PrimeDivisor.support_eq_closure C ▸
      (f.isClosedMap _ C'.idealSheaf.support.isClosed).closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr ⟨_, hC'mem, hgC'⟩)) (hB.2.1 C hC)
  refine ⟨C', y, ?_, hyC', hyP⟩
  rw [inverseTransformDivisor_apply_of_eq_some hC' B]
  exact Finsupp.mem_support_iff.mp hC

end DualGraph

section Node

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] {P : X} {B : QDivisor X} {f : Y ⟶ X} [QuasiCompact (f ≫ sX)]
    [IsLocallyNoetherian Y] [IsNormal Y] {n : ℕ} {E : Fin n → MMP.Mori.PrimeDivisor Y}
    {Γ : WeightedGraph (Fin n)}

/-- **Fig. 3 (9) with two vertices meeting at a boundary point.** Let `B` be reduced and `Γ(f)`
a rational tree which is a chain `w_1, w_2` with `β = e_{w_1} + e_{w_2}`, and suppose some
boundary point `(C, z)` has `z ∈ E_{w_1} ∩ E_{w_2}`. Then `(X, B)` is not log canonical near
`P`: `a = 0`, so `Θ_{f,0} = f⁻¹_* B + E_{w_1} + E_{w_2}` has multiplicity `≥ 3` at `z`. -/
private theorem not_isLogCanonical_of_mem_inter (hred : IsReducedBoundary B)
    (hΓ : IsWeightedDualGraph sX P B f E Γ) (hrat : Γ.IsRationalTree) {e : Fin 2 ≃ Fin n}
    (he : Γ.IsChainOrder e) (hβ : ∀ i, Γ.boundary (e i) = 1) {C : MMP.Mori.PrimeDivisor Y}
    {z : Y} (hCz : IsGermBoundaryPoint f P B C z)
    (hz : z ∈ (E (e 0)).support ∩ (E (e 1)).support)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 2) :
    ¬ HoldsOnGerm {P} fun U : X.Opens => ∀ [Nonempty U],
      haveI : CompactSpace U := isCompact_iff_compactSpace.mp
        (@NoetherianSpace.isCompact _ _ (haveI : IsNoetherian X := {}; inferInstance) _)
      IsLogCanonical (U.ι ≫ sX) 2 (DivisorWithCoeffs.restrictOpen U K)
        (DivisorWithCoeffs.restrictOpen U (QDivisor.toRDivisor B)) := by
  classical
  have hg := hΓ.isGermResolution
  have hEn := hΓ.isExceptionalCurveEnumeration
  have hBs := hΓ.isSurfaceGermWithBoundary
  have hsm := hg.isSmoothResolution.isSmoothScheme
  have hYd := hg.topologicalKrullDim_eq
  have ha : IsGermLogDiscrepancyVector sX P B f E 0 := by
    refine (hΓ.isGermLogDiscrepancyVector_iff 0).mpr ?_
    refine (WeightedGraph.isLogDiscrepancyVector_iff_eq_zero_of_isChainOrder hrat hΓ.isNegDef
      two_pos he fun i => ?_).mpr rfl
    rw [hβ i]
    fin_cases i <;> norm_num
  set Θ := logPullbackBoundary f B E 0 with hΘdef
  have hΘapp : ∀ D, Θ D = inverseTransformDivisor f B D +
      ∑ j, Finsupp.single (E j) (1 : ℚ) D := by
    intro D
    simp [hΘdef, logPullbackBoundary]
  have hsumE : ∀ D, (∑ j, Finsupp.single (E j) (1 : ℚ) D) = if ∃ j, E j = D then 1 else 0 := by
    intro D
    split_ifs with h
    · obtain ⟨j, rfl⟩ := h
      rw [Finset.sum_eq_single j (fun j' _ hj' => Finsupp.single_eq_of_ne
        (fun h => hj' (hEn.injective h).symm)) (by simp), Finsupp.single_eq_same]
    · exact Finset.sum_eq_zero fun j _ => Finsupp.single_eq_of_ne (fun hDE => h ⟨j, hDE.symm⟩)
  have hCsupp : C ∈ (inverseTransformDivisor f B).support := Finsupp.mem_support_iff.mpr hCz.1
  have hCE : ∀ j, E j ≠ C := fun j =>
    (nonneg_and_ne_of_mem_support_inverseTransformDivisor hg hBs (hEn.isGermExceptionalCurve j)
      hCsupp).2
  have hΘC : Θ C = 1 := by
    obtain ⟨D, hD⟩ := exists_eq_some_of_mem_support_mapPrimeDivisors hCsupp
    have hCD := inverseTransformDivisor_apply_of_eq_some hD B
    have hDB : D ∈ B.support := by
      rw [Finsupp.mem_support_iff, ← hCD]
      exact hCz.1
    rw [hΘapp, hCD, hred D hDB, hsumE, if_neg (fun ⟨j, hj⟩ => hCE j hj), add_zero]
  have hΘE : ∀ j, Θ (E j) = 1 := by
    intro j
    have h0 : inverseTransformDivisor f B (E j) = 0 := by
      by_contra hne
      exact (nonneg_and_ne_of_mem_support_inverseTransformDivisor hg hBs
        (hEn.isGermExceptionalCurve j) (Finsupp.mem_support_iff.mpr hne)).2 rfl
    rw [hΘapp, h0, hsumE, if_pos ⟨j, rfl⟩, zero_add]
  have hΘnn : ∀ D, 0 ≤ Θ D := by
    intro D
    rw [hΘapp, hsumE]
    refine add_nonneg ?_ (by split_ifs <;> norm_num)
    by_cases hD : D ∈ (inverseTransformDivisor f B).support
    · exact (nonneg_and_ne_of_mem_support_inverseTransformDivisor hg hBs
        (hEn.isGermExceptionalCurve (e 0)) hD).1
    · rw [Finsupp.notMem_support_iff.mp hD]
  have h01 : E (e 0) ≠ E (e 1) := fun h => absurd (e.injective (hEn.injective h)) (by decide)
  have hzcl : IsClosed ({z} : Set Y) := isClosed_singleton_of_mem_inter hYd h01 hz
  refine ha.not_isLogCanonical_of_two_lt_multiplicityAt hzcl hCz.2.2
    (lt_of_lt_of_le ?_ (natCast_sum_multiplicityAt_le hΘnn {C, E (e 0), E (e 1)}
      (by simp [hΘC, hΘE]))) hK
  rw [Finset.sum_insert (by simp [(hCE _).symm]), Finset.sum_pair h01]
  have := one_le_toNat_multiplicityAt hsm _ hCz.2.1
  have := one_le_toNat_multiplicityAt hsm _ hz.1
  have := one_le_toNat_multiplicityAt hsm _ hz.2
  exact_mod_cast (show 2 < _ by omega)

end Node

section CanonicalDivisorExistence

open MMP.Fourfold

open Opposite TopologicalSpace

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X]

/-- A nonempty open subscheme of an irreducible scheme is dense. -/
private theorem isDominant_opens_ι {Y : Scheme.{u}} [IrreducibleSpace Y] (V : Y.Opens)
    [Nonempty V] : IsDominant V.ι :=
  Opens.isDominant_ι (V.isOpen.dense ⟨_, (Classical.arbitrary V).2⟩)

/-- A nonempty open subscheme of an integral scheme has the same function field. -/
private theorem functionFieldMap_opens_ι_bijective {Y : Scheme.{u}} [IsIntegral Y] (V : Y.Opens)
    [Nonempty V] [IsDominant V.ι] : Function.Bijective (functionFieldMap V.ι) :=
  functionFieldMap_bijective_of_isOpenImmersion V.ι ⊤ ⟨Classical.arbitrary V, trivial⟩

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

/-- The pull-back of rational forms along an isomorphism of function fields is surjective. -/
private theorem pullbackForms_surjective {k K K' : Type*} [CommRing k] [Field K] [Field K']
    [Algebra k K] [Algebra k K'] [Algebra K K'] [IsScalarTower k K K'] {d : ℕ}
    (hbij : Function.Bijective (algebraMap K K')) {ω : ⋀[K]^d Ω[K⁄k]}
    (hω : IsPullbackGenerator K' ω) (m : ℤ) :
    Function.Surjective (pullbackForms (k := k) (K := K) (K' := K') (d := d) m) := by
  intro σ
  set b' := ZTensorPower.basis (basisOfSpanSingleton hω.2.1 hω.2.2) m
  set b := ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m
  obtain ⟨c, hc⟩ := hbij.2 (b'.repr σ ())
  refine ⟨c • b (), ?_⟩
  have h1 : b.repr (c • b ()) () = c := by
    simp [Module.Basis.repr_self]
  rw [pullbackForms_eq hω, pullbackFormsAlong]
  change algebraMap K K' (b.repr (c • b ()) ()) • b' () = σ
  rw [h1, hc]
  exact basis_unit_repr_smul b' σ

/-- Every rational top form on a nonempty open subscheme `U` of a variety `X` is the restriction
of one on `X`. -/
private theorem exists_pullbackRationalPluriForms_ι_eq [PerfectField k] [LocallyOfFiniteType sX]
    (U : X.Opens) [Nonempty U] [IsDominant U.ι] {n : ℕ} (hn : topologicalKrullDim X = n)
    (σ : RationalPluriForms (U.ι ≫ sX) n 1) :
    ∃ ω : RationalPluriForms sX n 1, pullbackRationalPluriForms sX U.ι ω = σ := by
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have hbij := functionFieldMap_opens_ι_bijective U
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (U.ι ≫ sX)
  let := functionFieldMapAlgebra U.ι
  have := isScalarTower_functionFieldMap sX U.ι
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX U.ι hbij hd
  exact pullbackForms_surjective hbij hω 1 σ

/-- The divisor of the restriction of a rational top form to a nonempty open subscheme is the
restriction of its divisor. -/
private theorem divisorOfForm_pullback_ι [PerfectField k] [CompactSpace X]
    [LocallyOfFiniteType sX] (U : X.Opens) [Nonempty U] [CompactSpace U] [IsDominant U.ι]
    {n : ℕ} (hn : topologicalKrullDim X = n) (ω : RationalPluriForms sX n 1) :
    divisorOfForm (pullbackRationalPluriForms sX U.ι ω) = (divisorOfForm ω).restrictOpen U := by
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have hbij := functionFieldMap_opens_ι_bijective U
  ext W
  rw [DivisorWithCoeffs.coeff_restrictOpen, coeff_divisorOfForm, coeff_divisorOfForm]
  exact MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso U.ι hbij hd W _
    (OpenWeilRestriction.genericPoint_primeDivisorMap _ _).symm ω

/-- The pull-back of the zero form is zero. -/
private theorem pullbackRationalPluriForms_zero (U : X.Opens) [Nonempty U] [IsDominant U.ι]
    {n : ℕ} : pullbackRationalPluriForms sX U.ι (0 : RationalPluriForms sX n 1) = 0 := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (U.ι ≫ sX)
  let := functionFieldMapAlgebra U.ι
  have := isScalarTower_functionFieldMap sX U.ι
  have h := pullbackForms_smul (K' := (U : Scheme).functionField) (k := k) (d := n) (m := 1)
    (0 : X.functionField) (0 : RationalPluriForms sX n 1)
  simp only [zero_smul, map_zero] at h
  exact h

/-- **A canonical divisor agreeing with a given one near a point.** Let `X` be a normal variety
of dimension `n` over a perfect field and `U ⊆ X` a nonempty open subset on which `K|_U` is a
canonical divisor. Then there is a canonical divisor `K'` of `X` with `K'|_U = K|_U`. -/
private theorem exists_isCanonicalDivisor_restrictOpen_eq [PerfectField k] [CompactSpace X]
    [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) (U : X.Opens) [Nonempty U] [CompactSpace U]
    {K : Divisor X}
    (hKU : Divisor.IsCanonicalDivisor (U.ι ≫ sX) n (DivisorWithCoeffs.restrictOpen U K)) :
    ∃ K' : Divisor X, K'.IsCanonicalDivisor sX n ∧ K'.restrictOpen U = K.restrictOpen U := by
  have : IsDominant U.ι := isDominant_opens_ι U
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety sX hX hn
  have hXU : IsNormalVariety k (U.ι ≫ sX) := isNormalVariety_ι hX U
  obtain ⟨σ, hσ0, hσ⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hXU hKU
  obtain ⟨ω, hω⟩ := exists_pullbackRationalPluriForms_ι_eq U hn σ
  have hω0 : ω ≠ 0 := by
    rintro rfl
    exact hσ0 (hω ▸ pullbackRationalPluriForms_zero U)
  refine ⟨divisorOfForm ω, ?_, ?_⟩
  · have h := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hX hK₀ (m := 1) hω0
    rw [one_smul] at h
    exact hK₀.of_linearlyEquivalent h
  · rw [← divisorOfForm_pullback_ι U hn ω, hω]
    exact DivisorWithCoeffs.ext' fun Γ => by rw [coeff_divisorOfForm, hσ]

end CanonicalDivisorExistence

/-! ### The list -/

/-- **Log canonical germs with nonzero reduced boundary** (FA 3.3.1). Let `(X, P; B)` be a surface
germ with boundary over an algebraically closed field `k`, with `B ≠ 0` reduced, whose minimal
resolution has `n ≥ 1` exceptional curves. If `(X, B)` is log canonical near `P` — on some open
neighbourhood `U` of `P` the pair `(U, B|_U)` with canonical divisor `K|_U` is log canonical —
then `(X, P; B)` is of type (3), (9) or (10) (`IsFig3Type3`, `IsFig3Type9`, `IsFig3Type10`). -/
@[mmp "lem_fa3_reduced_boundary_lc_graph_list"]
public theorem IsSurfaceGermWithBoundary.isFig3Type3_or_isFig3Type9_or_isFig3Type10
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] {P : X} {B : QDivisor X}
    (hB : IsSurfaceGermWithBoundary sX P B) (hred : IsReducedBoundary B) (hB0 : B ≠ 0)
    (hn : ∃ (n : ℕ) (Γ : WeightedGraph (Fin n)), 1 ≤ n ∧ IsMinimalWeightedDualGraph sX P B Γ)
    {K : Divisor X}
    (hlc : HoldsOnGerm {P} fun U : X.Opens => ∀ [Nonempty U],
      haveI : CompactSpace U := isCompact_iff_compactSpace.mp
        (@NoetherianSpace.isCompact _ _ (haveI : IsNoetherian X := {}; inferInstance) _)
      IsLogCanonical (U.ι ≫ sX) 2 (DivisorWithCoeffs.restrictOpen U K)
        (DivisorWithCoeffs.restrictOpen U (QDivisor.toRDivisor B))) :
    IsFig3Type3 sX P B ∨ IsFig3Type9 sX P B ∨ IsFig3Type10 sX P B := by
  classical
  obtain ⟨n, Γ, hn1, Y, f, _, _, _, E, hf, hΓ⟩ := hn
  have hg := hΓ.isGermResolution
  have hEn := hΓ.isExceptionalCurveEnumeration
  have hXv : IsNormalVariety k sX := hB.1.1
  have hdimX : topologicalKrullDim X = 2 := hB.1.2.1
  -- a canonical divisor of `X` agreeing with `K` near `P`
  obtain ⟨U, hPU, hlcU⟩ := hlc
  have hPU' : P ∈ U := hPU rfl
  have : Nonempty U := ⟨⟨P, hPU'⟩⟩
  have : CompactSpace U := isCompact_iff_compactSpace.mp
    (@NoetherianSpace.isCompact _ _ (haveI : IsNoetherian X := {}; inferInstance) _)
  obtain ⟨K', hK', hK'U⟩ := exists_isCanonicalDivisor_restrictOpen_eq hXv hdimX U hlcU.2.1
  have hlc' : HoldsOnGerm {P} fun U : X.Opens => ∀ [Nonempty U],
      haveI : CompactSpace U := isCompact_iff_compactSpace.mp
        (@NoetherianSpace.isCompact _ _ (haveI : IsNoetherian X := {}; inferInstance) _)
      IsLogCanonical (U.ι ≫ sX) 2 (DivisorWithCoeffs.restrictOpen U K')
        (DivisorWithCoeffs.restrictOpen U (QDivisor.toRDivisor B)) :=
    ⟨U, hPU, fun {_} => by rw [hK'U]; exact hlcU⟩
  -- the log discrepancy vector is nonnegative
  have hneg := hΓ.isNegDef
  obtain ⟨a, ha, -⟩ := WeightedGraph.existsUnique_isLogDiscrepancyVector Γ (det_pos hneg).ne'
  have ha0 : ∀ j, 0 ≤ a j := fun j =>
    ((hΓ.isGermLogDiscrepancyVector_iff a).mpr ha).nonneg_of_isLogCanonical hK' hlc' j
  -- the boundary points and the extended dual graph
  obtain ⟨m, pt, hinj, hbp, hcov⟩ := exists_boundaryPoint_enum hΓ hn1
  have hext := isExtendedDualGraph_extGraph hred hΓ hinj hbp hcov
  set w := (extGraph sX f E Γ pt).boundaryEdgeWeight with hwdef
  have hw0 : ∀ j l, (pt l).2 ∉ (E j).support → w j l = 0 := fun j l h => by
    simp only [hwdef, extGraph]
    rw [if_neg h]
  have hwpos : ∀ j l, (pt l).2 ∈ (E j).support → 1 ≤ w j l := fun j l h =>
    (hext.boundary_eq_sum_boundaryEdgeWeight j).2 l h
  have hsum : ∀ j, Γ.boundary j = ((∑ l, w j l : ℕ) : ℚ) := fun j => by
    have h := (hext.boundary_eq_sum_boundaryEdgeWeight j).1
    change Γ.boundary j = _ at h
    rw [h, Finset.sum_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs with h
    · rfl
    · rw [hw0 j l h]; rfl
  have hon : ∀ l, ∃ j, 1 ≤ w j l := fun l => by
    obtain ⟨j, hj⟩ := exists_mem_support_of_map_eq hΓ hn1 (hbp l).2.2
    exact ⟨j, hwpos j l hj⟩
  have hmem : ∀ j l, 1 ≤ w j l → (pt l).2 ∈ (E j).support := fun j l h => by
    by_contra hn; rw [hw0 j l hn] at h; omega
  have hβnat : ∀ j, ∃ N : ℕ, Γ.boundary j = N := fun j => ⟨_, hsum j⟩
  have hβpos : ∃ j, 0 < Γ.boundary j := by
    obtain ⟨C, y, hCy⟩ := exists_isGermBoundaryPoint hΓ hB0
    obtain ⟨l, hl⟩ := hcov C y hCy
    obtain ⟨j, hj⟩ := hon l
    refine ⟨j, ?_⟩
    rw [hsum j]
    have : 1 ≤ ∑ l, w j l := le_trans hj (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ l))
    exact_mod_cast this
  -- `Γ` is a rational tree
  have hrat : Γ.IsRationalTree := by
    refine hf.isRationalTree_of_logDiscrepancy_nonneg hΓ ha ha0 ?_ ?_
    · rintro ⟨-, h⟩
      obtain ⟨j, hj⟩ := hβpos
      rw [(h j).2] at hj
      exact lt_irrefl _ hj
    · rintro ⟨e, he⟩
      obtain ⟨j, hj⟩ := hβpos
      have := he.boundary_eq_zero (e.symm j)
      rw [Equiv.apply_symm_apply] at this
      rw [this] at hj
      exact lt_irrefl _ hj
  -- one boundary point, at the vertex `j₀` with `β = e_{j₀}`
  have hone : ∀ j₀, (∀ j, Γ.boundary j = if j = j₀ then 1 else 0) →
      ∃ hm : m = 1, ∀ j, w j (Fin.cast hm.symm 0) = if j = j₀ then 1 else 0 := by
    intro j₀ hj₀
    refine exists_eq_one_and_apply_eq_ite hon fun j => ?_
    have := (hsum j).symm.trans (hj₀ j)
    split_ifs at this ⊢ <;> exact_mod_cast this
  -- type (3) from a chain with `β = e_{w_1}`
  have fin3 : ∀ e : Fin n ≃ Fin n, Γ.IsChainOrder e →
      (∀ j, Γ.boundary j = if j = e ⟨0, hn1⟩ then 1 else 0) → IsFig3Type3 sX P B := by
    intro e he hβe
    obtain ⟨hm, hw⟩ := hone _ hβe
    subst hm
    exact ⟨hB, Y, f, inferInstance, inferInstance, inferInstance, n, E, hf, hEn,
      Or.inr ⟨hn1, pt, extGraph sX f E Γ pt, e, hext, he, hrat.two_le_weight, hw⟩⟩
  -- type (10) from the graph of Fig. 3 (10)
  have fin10 : ∀ (s : ℕ), 1 ≤ s → ∀ e : Fin (s + 2) ≃ Fin n, IsFig3Type10Order Γ s e →
      IsFig3Type10 sX P B := by
    intro s hs e he
    obtain ⟨hm, hw⟩ := hone _ he.2.2.2
    subst hm
    exact ⟨Y, f, inferInstance, inferInstance, inferInstance, n, E, hf, hEn, hn1, s, hs, e, pt,
      extGraph sX f E Γ pt, hext, hrat, he.1, he.2.1, he.2.2.1, hw⟩
  -- type (9) from two boundary points `l₁ ≠ l₂` at the two ends of a chain
  have fin9 : ∀ e : Fin n ≃ Fin n, Γ.IsChainOrder e → ∀ l₁ l₂ : Fin m, l₁ ≠ l₂ →
      (∀ l, l = l₁ ∨ l = l₂) → (pt l₁).2 ≠ (pt l₂).2 →
      (∀ j, w j l₁ = if j = e ⟨0, hn1⟩ then 1 else 0) →
      (∀ j, w j l₂ = if j = e ⟨n - 1, by omega⟩ then 1 else 0) → IsFig3Type9 sX P B := by
    intro e he l₁ l₂ h12 hcov12 hy hw₁ hw₂
    let g : Fin 2 → Fin m := ![l₁, l₂]
    have hginj : Function.Injective g := by
      intro i i' h
      fin_cases i <;> fin_cases i'
      · rfl
      · exact absurd h h12
      · exact absurd h.symm h12
      · rfl
    have hgsurj : Function.Surjective g := fun l => by
      rcases hcov12 l with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    have hext' := isExtendedDualGraph_extGraph hred hΓ (hinj.comp hginj) (fun l => hbp (g l))
      (fun C y hCy => by
        obtain ⟨l, hl⟩ := hcov C y hCy
        obtain ⟨i, rfl⟩ := hgsurj l
        exact ⟨i, hl⟩)
    exact ⟨hB, Y, f, inferInstance, inferInstance, inferInstance, n, E, hf, hEn,
      Or.inr ⟨hn1, pt ∘ g, extGraph sX f E Γ (pt ∘ g), e, hext', he, hrat.two_le_weight, hy,
        hw₁, hw₂⟩⟩
  -- the graph list
  rcases hf.isWeightedChain_or_isStar_of_boundary_pos hΓ hrat hβpos ha ha0 with
    ⟨s, e, he⟩ | ⟨v, arms, hstar, -⟩
  · -- `Γ` is a chain
    have hsn : s = n := by simpa using Fintype.card_congr e
    subst hsn
    rcases WeightedGraph.IsLogDiscrepancyVector.boundary_cases_of_isChainOrder hrat hneg hn1 he
      hβnat hβpos ha ha0 with (hA | hA) | ⟨hs3, hb⟩ | ⟨hs2, hc⟩ | ⟨hs1, hd⟩
    · -- (a), `β = e_{w_1}`
      left
      refine fin3 e he fun j => ?_
      obtain ⟨i, rfl⟩ := e.surjective j
      rw [hA i]
      simp only [EmbeddingLike.apply_eq_iff_eq, Fin.ext_iff]
    · -- (a), `β = e_{w_s}`: read the chain backwards
      left
      refine fin3 _ (isChainOrder_revPerm he) fun j => ?_
      obtain ⟨i, rfl⟩ := e.surjective j
      rw [hA i]
      simp only [Equiv.trans_apply, Fin.revPerm_apply, EmbeddingLike.apply_eq_iff_eq, Fin.ext_iff,
        Fin.val_rev]
      refine if_congr ?_ rfl rfl
      omega
    · -- (b): the tree of type (10) with `s = 1`
      right; right
      subst hs3
      exact fin10 1 le_rfl _ (isFig3Type10Order_of_chain he hb)
    · -- (c): two boundary points at the two ends
      right; left
      have hN : ∀ j, ∑ l, w j l = (if j = e ⟨0, hn1⟩ then 1 else 0) +
          (if j = e ⟨s - 1, by omega⟩ then 1 else 0) := fun j => by
        obtain ⟨i, rfl⟩ := e.surjective j
        have := (hsum (e i)).symm.trans (hc i)
        simp only [EmbeddingLike.apply_eq_iff_eq, Fin.ext_iff]
        split_ifs at this ⊢ <;> first | omega | exact_mod_cast this
      have hends : e ⟨0, hn1⟩ ≠ e ⟨s - 1, by omega⟩ := fun h => by
        have := congrArg Fin.val (e.injective h); simp at this; omega
      obtain ⟨l₁, l₂, hl₁, hl₂, hall, hind⟩ := exists_pair_of_sum_eq_ite_add_ite hon hends hN
      have hy₂ := hmem _ _ hl₂.ge
      by_cases h12 : l₁ = l₂
      · -- a common point of `E_{w_1}` and `E_{w_s}`: `s = 2` and `(X, B)` is not lc
        subst h12
        have hy₁ := hmem _ _ hl₁.ge
        have hadj := adj_of_mem_inter hΓ hends ⟨hy₁, hy₂⟩
        have hs2' : s = 2 := by
          have h := hadj.2
          rw [he.edgeWeight_eq] at h
          by_contra hne
          rw [if_neg (show ¬(s - 1 + 1 = 0 ∨ 0 + 1 = s - 1) by omega)] at h
          exact lt_irrefl 0 h
        subst hs2'
        exfalso
        refine not_isLogCanonical_of_mem_inter hred hΓ hrat he (fun i => ?_) (hbp l₁)
          ⟨hy₁, hy₂⟩ hK' hlc'
        rw [hc i]
        fin_cases i <;> norm_num
      · obtain ⟨hw₁, hw₂⟩ := hind h12
        refine fin9 e he l₁ l₂ h12 hall (fun hy => ?_) hw₁ hw₂
        have := hwpos _ _ (hy ▸ hy₂)
        rw [hw₁, if_neg (Ne.symm hends)] at this
        omega
    · -- (d): one vertex with `β = 2`
      right; left
      subst hs1
      have hβ2 : Γ.boundary 0 = 2 := by
        have := hd (e.symm 0); rwa [Equiv.apply_symm_apply] at this
      by_contra hcon
      apply IsExtendedDualGraph.not_isLogCanonical_of_boundary_eq_two hf hext hrat hβ2 ?_ hK' hlc'
      rintro ⟨l₁, l₂, h12, hall, hy, hw₁, hw₂⟩
      refine hcon (fin9 e he l₁ l₂ h12 hall hy (fun j => ?_) (fun j => ?_))
      · rw [Subsingleton.elim j (e ⟨0, hn1⟩), if_pos rfl, Subsingleton.elim (e ⟨0, hn1⟩) 0]
        exact hw₁
      · rw [Subsingleton.elim j (e ⟨1 - 1, by omega⟩), if_pos rfl,
          Subsingleton.elim (e ⟨1 - 1, by omega⟩) 0]
        exact hw₂
  · -- `Γ` is a star with three arms
    right; right
    obtain ⟨i, hsingle, r, hr, e, he, hadj, huniq, hβ⟩ :=
      boundary_eq_of_isStar hrat hneg hstar hβnat hβpos ha ha0
    obtain ⟨l₁, l₂, h01, h02, h12⟩ : ∃ l₁ l₂ : Fin 3, i ≠ l₁ ∧ i ≠ l₂ ∧ l₁ ≠ l₂ := by
      fin_cases i
      · exact ⟨1, 2, by decide, by decide, by decide⟩
      · exact ⟨0, 2, by decide, by decide, by decide⟩
      · exact ⟨0, 1, by decide, by decide, by decide⟩
    obtain ⟨u₁, hu₁, hw₁⟩ := hsingle l₁ (Ne.symm h01)
    obtain ⟨u₂, hu₂, hw₂⟩ := hsingle l₂ (Ne.symm h02)
    obtain ⟨e', he'⟩ := exists_isFig3Type10Order_of_isStar hstar h01 h02 h12 hu₁ hu₂ hw₁ hw₂ hr
      he hadj huniq hβ
    exact fin10 (r + 1) (by omega) e' he'

end ReducedBoundary

end MMP.Flips
