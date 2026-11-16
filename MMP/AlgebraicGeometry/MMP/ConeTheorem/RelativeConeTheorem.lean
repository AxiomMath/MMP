module

public import MMP.AlgebraicGeometry.MMP.ConeTheorem.RationalCurves
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.DltNegativeFace
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeConeInAbsolute

/-!
# The relative cone theorem for a morphism of projective varieties

Let `(X, Δ)` be a klt pair with `Δ` effective, and let `f : X ⟶ Y` be a morphism of projective
varieties over an algebraically closed field `k` of characteristic zero. Then there are countably
many rational curves `Cⱼ ⊆ X`, each contracted by `f` and with
`0 < -((K_X + Δ) · Cⱼ) ≤ 2 dim X`, such that the relative closed cone of curves decomposes as

`NE̅(X/Y) = NE̅(X/Y)_{(K_X + Δ) ≥ 0} + ∑ⱼ ℝ_{≥0} [Cⱼ]`.

The proof starts from the absolute cone theorem on `X`. Write `ι : N₁(X/Y) → N₁(X)` for the
natural (injective) map and `f_* : N₁(X) → N₁(Y)` for the push-forward. For `ξ ∈ NE̅(X/Y)` write
`ι ξ = η + w` with `η ∈ NE̅(X)_{(K_X + Δ) ≥ 0}` and `w` a non-negative combination of the curves
of the absolute theorem. Then `f_* η + f_* w = f_* ι ξ = 0` with both terms in `NE̅(Y)`, which
contains no line, so `f_* w = 0`. An induction over the cone spanned by the curves, using once more
that `NE̅(Y)` contains no line, shows that `w` is then a non-negative combination of curves with
`f_* [C] = 0`, and such a curve is contracted by `f`, since an ample divisor on `Y` has degree
zero on its image. So `w = ι b` with `b` in the cone spanned by the contracted curves, and
`η = ι (ξ - b)` lies in `NE̅(X) ∩ ι N₁(X/Y) = ι NE̅(X/Y)`.

## Main results

* `MMP.Mori.IsKltPair.exists_relativeClosedConeOfCurves_eq_add_hull`: the decomposition.

## Implementation notes

The countable family of curves is indexed by a countable type `ι`; the sum `∑ⱼ ℝ_{≥0}[Cⱼ]` of
the rays is the convex cone they span, `PointedCone.hull ℝ`, whose elements are the finite
non-negative combinations of the classes `[Cⱼ]`. A curve is an `MMP.Mori.ProperCurve`, and it is
rational when its reduced closed subscheme is (`MMP.Mori.IsRationalCurve`). The pairing with
`K_X + Δ` on `N₁(X/Y)` is `MMP.Fourfold.QDivisor.relativeCurveForm`. The dimension of `X` is the
integer `n` of the klt pair, which equals `dim X` by
`MMP.Mori.IsCanonicalDivisor.topologicalKrullDim_eq`.

## References

* [KM98] J. Kollár, S. Mori, *Birational geometry of algebraic varieties*, Theorem 3.25(1) in
  case 3.21(0), proof 3.28.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Pointwise MMP.Fourfold
open AlgebraicGeometry hiding IsProjectiveVariety

namespace MMP.Mori

section Helpers

variable {k : Type} [Field k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)}

/-- The natural map sends the relative class of a contracted curve to its absolute class. -/
private theorem relativeToAbsolute_relativeClass (f : X ⟶ Y) {C : ProperCurve sX}
    (hC : C.IsContractedBy f) :
    relativeToAbsolute sX f (C.relativeClass f hC) = OneCycle.numericalClass sX (C.cycle ℝ) :=
  isNaturalRelativeMap_relativeToAbsolute sX f _

/-- A curve whose class has vanishing push-forward is contracted: an ample divisor on `Y` has
degree zero on its image. -/
private theorem isContractedBy_of_pushforward_eq_zero [IsProjectiveVariety k sX]
    {sY : Y ⟶ Spec (.of k)} [IsProjectiveVariety k sY] (f : X ⟶ Y) (hf : f ≫ sY = sX)
    (C : ProperCurve sX)
    (hC : NumericalCurveClasses.pushforward f hf (OneCycle.numericalClass sX (C.cycle ℝ)) = 0) :
    C.IsContractedBy f := by
  obtain ⟨H, _, hHa⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety
    (inferInstance : IsProjectiveVariety k sY)
  refine MMP.ProgramBaseChange.isContractedBy_of_degree_pullback_eq_zero f hf H hHa C ?_
  have h := NumericalCurveClasses.degree_pushforward f hf H
    (OneCycle.numericalClass sX (C.cycle ℝ))
  rw [hC, map_zero, NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle] at h
  exact_mod_cast h.symm

end Helpers

section ConeLemmas

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- In a cone containing no line, two elements with sum zero vanish. -/
private theorem eq_zero_of_add_eq_zero {K : PointedCone ℝ V} (hK : K.lineal = ⊥) {u v : V}
    (hu : u ∈ K) (hv : v ∈ K) (huv : u + v = 0) : u = 0 := by
  have hmem : u ∈ K.lineal := by
    rw [PointedCone.mem_lineal]
    exact ⟨hu, by rwa [neg_eq_of_add_eq_zero_right huv]⟩
  rwa [hK, Submodule.mem_bot] at hmem

/-- Let `φ` map every generator of a cone into a cone `K` containing no line. Then an element of
the cone killed by `φ` is a non-negative combination of generators killed by `φ`. -/
private theorem mem_hull_setOf_map_eq_zero (φ : V →ₗ[ℝ] W) {K : PointedCone ℝ W}
    (hK : K.lineal = ⊥) {s : Set V} (hs : ∀ v ∈ s, φ v ∈ K) {w : V}
    (hw : w ∈ PointedCone.hull ℝ s) (h0 : φ w = 0) :
    w ∈ PointedCone.hull ℝ {v ∈ s | φ v = 0} := by
  suffices φ w ∈ K ∧ (φ w = 0 → w ∈ PointedCone.hull ℝ {v ∈ s | φ v = 0}) from this.2 h0
  clear h0
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨hs x hx, fun h => Submodule.subset_span ⟨hx, h⟩⟩
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    refine ⟨add_mem hx.1 hy.1, fun h => ?_⟩
    exact add_mem (hx.2 (eq_zero_of_add_eq_zero hK hx.1 hy.1 h))
      (hy.2 (eq_zero_of_add_eq_zero hK hy.1 hx.1 (by rwa [add_comm])))
  | smul c x _ hx =>
    rw [LinearMap.map_smul_of_tower]
    refine ⟨Submodule.smul_mem _ c hx.1, fun h => ?_⟩
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    · exact Submodule.smul_mem _ c (hx.2 ((smul_eq_zero.mp h).resolve_left hc))

end ConeLemmas

section RelativeCone

variable {k : Type} [Field k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)}

/-- A relative class whose image in `N₁(X)` lies in `NE̅(X)` lies in `NE̅(X/Y)`. -/
private theorem mem_relativeClosedConeOfCurves_of_relativeToAbsolute_mem [IsAlgClosed k]
    [CharZero k] [IsProjectiveVariety k sX] {sY : Y ⟶ Spec (.of k)} [IsProjectiveVariety k sY]
    (f : X ⟶ Y) (hf : f ≫ sY = sX) {ζ : RelativeNumericalCurveClasses sX f}
    (h : relativeToAbsolute sX f ζ ∈ closedConeOfCurves sX) :
    ζ ∈ relativeClosedConeOfCurves sX f := by
  obtain ⟨ζ', hζ', h'⟩ : relativeToAbsolute sX f ζ ∈
      relativeToAbsolute sX f '' (relativeClosedConeOfCurves sX f : Set _) := by
    rw [image_relativeClosedConeOfCurves_eq_inter_range sX sY f hf]
    exact ⟨h, ζ, rfl⟩
  rwa [← (existsUnique_isNaturalRelativeMap_and_injective sX f).2 _
    (isNaturalRelativeMap_relativeToAbsolute sX f) h']

/-- A non-negative combination of classes of curves in `S` with vanishing push-forward is the
image of a non-negative combination of relative classes of contracted curves in `S`. -/
private theorem mem_map_hull_relativeClass_of_pushforward_eq_zero [IsProjectiveVariety k sX]
    {sY : Y ⟶ Spec (.of k)} [IsProjectiveVariety k sY] (f : X ⟶ Y) (hf : f ≫ sY = sX)
    {S : Set (ProperCurve sX)} {w : NumericalCurveClasses sX}
    (hw : w ∈ PointedCone.hull ℝ
      ((fun C : ProperCurve sX => OneCycle.numericalClass sX (C.cycle ℝ)) '' S))
    (h0 : NumericalCurveClasses.pushforward f hf w = 0) :
    w ∈ (PointedCone.hull ℝ (Set.range fun j : {C : ProperCurve sX // C ∈ S ∧ C.IsContractedBy f} =>
      j.1.relativeClass f j.2.2)).map (relativeToAbsolute sX f) := by
  refine Submodule.span_le.mpr ?_
    (mem_hull_setOf_map_eq_zero _ (lineal_closedConeOfCurves_eq_bot sY) ?_ hw h0)
  · rintro _ ⟨⟨C, hCS, rfl⟩, hC0⟩
    have hCc := isContractedBy_of_pushforward_eq_zero f hf C hC0
    exact ⟨_, Submodule.subset_span ⟨⟨C, hCS, hCc⟩, rfl⟩, relativeToAbsolute_relativeClass f hCc⟩
  · rintro _ ⟨C, -, rfl⟩
    exact image_closedConeOfCurves_subset f hf
      (NumericalCurveClasses.isNumericalPushforward_pushforward f hf)
      ⟨_, coneOfCurves_le_closedConeOfCurves sX (numericalClass_cycle_mem_coneOfCurves sX C), rfl⟩

end RelativeCone

/-- **The relative cone theorem** for a morphism of projective varieties. Let `(X, Δ)` be a klt
pair (canonical divisor `K`, `n = dim X`) with `Δ` effective, over an algebraically closed field
of characteristic zero, and `f : X ⟶ Y` a morphism of projective varieties. Then there is a
countable family of rational curves `C j` contracted by `f`, with
`0 < -((K + Δ) · [C j]) ≤ 2n`, such that `relativeClosedConeOfCurves sX f` is the sum of its part
where `K + Δ` is non-negative and the convex cone spanned by the classes `[C j]`. -/
@[mmp "thm_km3b_relative_cone_theorem_decomposition"]
public theorem IsKltPair.exists_relativeClosedConeOfCurves_eq_add_hull
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} (sY : Y ⟶ Spec (.of k)) [IsProjectiveVariety k sX]
    [IsProjectiveVariety k sY] [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] (f : X ⟶ Y) (hf : f ≫ sY = sX)
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} (hΔ : IsKltPair sX n K Δ) (hΔ0 : 0 ≤ Δ) :
    ∃ (ι : Type) (_ : Countable ι) (C : ι → ProperCurve sX)
      (hC : ∀ j, (C j).IsContractedBy f),
      (∀ j, IsRationalCurve sX
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({(C j).point} : Set X)))) ∧
      (∀ j, 0 < -QDivisor.relativeCurveForm sX f (Divisor.toQDivisor K + Δ) hΔ.1.2.2
          ((C j).relativeClass f (hC j)) ∧
        -QDivisor.relativeCurveForm sX f (Divisor.toQDivisor K + Δ) hΔ.1.2.2
          ((C j).relativeClass f (hC j)) ≤ 2 * n) ∧
      (relativeClosedConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f)) =
        {z | z ∈ relativeClosedConeOfCurves sX f ∧
          0 ≤ QDivisor.relativeCurveForm sX f (Divisor.toQDivisor K + Δ) hΔ.1.2.2 z} +
        (PointedCone.hull ℝ (Set.range fun j => (C j).relativeClass f (hC j)) :
          Set (RelativeNumericalCurveClasses sX f)) := by
  obtain ⟨S, hSc, hS, hNE⟩ :=
    exists_countable_isRationalCurve_closedConeOfCurves_eq hΔ
      (DivisorWithCoeffs.isEffective_iff_nonneg.mpr hΔ0)
  set ι := relativeToAbsolute sX f
  set φ := NumericalCurveClasses.pushforward f hf
  have hform : ∀ z, QDivisor.relativeCurveForm sX f (Divisor.toQDivisor K + Δ) hΔ.1.2.2 z =
      QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hΔ.1.2.2 (ι z) := fun z => by
    rw [QDivisor.relativeCurveForm_eq_comp]; rfl
  have hφNE : ∀ z ∈ closedConeOfCurves sX, φ z ∈ closedConeOfCurves sY := fun z hz =>
    image_closedConeOfCurves_subset f hf
      (NumericalCurveClasses.isNumericalPushforward_pushforward f hf) ⟨z, hz, rfl⟩
  have hclassNE : ∀ C : ProperCurve sX,
      OneCycle.numericalClass sX (C.cycle ℝ) ∈ closedConeOfCurves sX := fun C =>
    coneOfCurves_le_closedConeOfCurves sX (numericalClass_cycle_mem_coneOfCurves sX C)
  let T := {C : ProperCurve sX // C ∈ S ∧ C.IsContractedBy f}
  have hTc : Countable T := (hSc.mono fun _ h => h.1).to_subtype
  set B : PointedCone ℝ (RelativeNumericalCurveClasses sX f) :=
    PointedCone.hull ℝ (Set.range fun j : T => j.1.relativeClass f j.2.2)
  refine ⟨T, hTc, fun j => j.1, fun j => j.2.2, fun j => (hS _ j.2.1).1, fun j => ?_, ?_⟩
  · rw [hform, relativeToAbsolute_relativeClass]
    exact (hS _ j.2.1).2
  have hBle : B ≤ relativeClosedConeOfCurves sX f := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, ← SetLike.mem_coe, coe_relativeClosedConeOfCurves]
    exact subset_closure (relativeClass_mem_relativeConeOfCurves j.2.2)
  refine Set.Subset.antisymm (fun ξ hξ => ?_) ?_
  · have hιξ : ι ξ ∈ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) :=
      ((image_relativeClosedConeOfCurves_eq_inter_range sX sY f hf).subset ⟨ξ, hξ, rfl⟩).1
    rw [hNE] at hιξ
    obtain ⟨η, ⟨hηNE, hηD⟩, w, hw, hηw⟩ := hιξ
    replace hηw : η + w = ι ξ := hηw
    have hwNE : w ∈ closedConeOfCurves sX :=
      Submodule.span_le.mpr (by rintro _ ⟨C, -, rfl⟩; exact hclassNE C) hw
    have hφw : φ w = 0 := by
      refine eq_zero_of_add_eq_zero (lineal_closedConeOfCurves_eq_bot sY) (hφNE w hwNE)
        (hφNE η hηNE) ?_
      rw [← map_add, add_comm, hηw]
      exact range_relativeToAbsolute_le_ker_pushforward f hf ⟨ξ, rfl⟩
    obtain ⟨b, hb, rfl⟩ := mem_map_hull_relativeClass_of_pushforward_eq_zero f hf hw hφw
    have hη : η = ι (ξ - b) := by
      rw [map_sub, ← hηw]
      exact (add_sub_cancel_right η _).symm
    refine ⟨ξ - b, ⟨mem_relativeClosedConeOfCurves_of_relativeToAbsolute_mem f hf (hη ▸ hηNE),
      ?_⟩, b, hb, sub_add_cancel ξ b⟩
    rwa [hform, ← hη]
  · rintro _ ⟨a, ⟨ha, -⟩, b, hb, rfl⟩
    exact add_mem ha (hBle hb)

end MMP.Mori
