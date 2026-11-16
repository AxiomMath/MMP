module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.DltProgram
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Basic
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.MMP.Threefold.Discrepancy
import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CurveInputs
import MMP.Analysis.Convex.Cone.ExtremalRays
import MMP.Analysis.Convex.Cone.CompactSlices
import MMP.Analysis.Convex.FiniteDimensional
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
import MMP.AlgebraicGeometry.Singularities.DltKltShrinkBoundary
import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.AmpleStrictlyPositive
import MMP.AlgebraicGeometry.Resolution.MaximalOrderAttained
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.Corollaries
import MMP.AlgebraicGeometry.Intersection.N1CartierCoordinates
import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeConeInAbsolute

/-!
# A `(K + Δ)`-negative face of a dlt pair is `(K + (1 - δ)Δ)`-negative for a klt pair

Let `(X, Δ)` be a dlt pair with `X` a `ℚ`-factorial projective variety, and let `f : X ⟶ S` be a
morphism of projective varieties. If `F` is a convex extremal face of the relative closed cone
of curves `NE(X/S)‾` on which `K_X + Δ` is negative away from `0`, then for some rational
`0 < δ < 1` the pair `(X, (1 - δ)Δ)` is klt and `K_X + (1 - δ)Δ` is still negative on `F \ {0}`.

## Main results

* `MMP.Mori.IsDltPair.exists_isKltPair_one_sub_smul_of_isExtremalFace`: a `(K + Δ)`-negative
  extremal face of `NE̅(X/S)` of a dlt pair is `(K + (1 - δ)Δ)`-negative, with `(X, (1 - δ)Δ)` klt.
* `MMP.Mori.QDivisor.relativeCurveForm_eq_comp`: the pairing with `N₁(X/S)` factors through
  the natural map `N₁(X/S) → N₁(X)`.
* `MMP.Fourfold.QDivisor.curveForm_add`, `MMP.Fourfold.QDivisor.curveForm_smul`: the curve form
  `N₁(X) → ℝ` of a `ℚ`-Cartier `ℚ`-divisor is additive and `ℚ`-homogeneous in the divisor.

## Implementation notes

The natural map `N₁(X/S) → N₁(X)` followed by a Cartier coordinate system `N₁(X) ≃ ℝ^r` is an
injective linear map carrying `NE̅(X/S)` onto a closed cone `C ⊆ ℝ^r` on which an ample divisor
`A` is positive off `0`. The image of `F` is an extremal face of `C`, hence closed. Its slice
`{A = 1}` is compact, so `K + Δ` is bounded above by some `-c < 0` there and `Δ` is bounded; for
small `δ` the form `K + (1 - δ)Δ = (K + Δ) - δΔ` stays negative on the slice, hence on
`F ∖ {0}`. Shrinking `δ` further makes `(X, (1 - δ)Δ)` klt.

## References

* [KM98] J. Kollár, S. Mori, *Birational geometry of algebraic varieties*, proof of Thm. 3.35.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace MMP.Fourfold.QDivisor

open MMP.Mori

section CurveForm

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX]

/-- The curve form is additive in the divisor. -/
theorem curveForm_add (D D' : QDivisor X) (hD : D.IsQCartier) (hD' : D'.IsQCartier)
    (hDD' : (D + D').IsQCartier) :
    curveForm sX (D + D') hDD' = curveForm sX D hD + curveForm sX D' hD' := by
  refine MMP.ProgramBaseChange.linearMap_ext_numericalClass_cycle sX fun C => ?_
  rw [LinearMap.add_apply, MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
    MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
    MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
    MMP.Mori.QDivisor.intersectionNumber_add' k sX C.ι C.dim_le D D' hD hD' hDD']
  push_cast; rfl

/-- The curve form is `ℚ`-homogeneous in the divisor. -/
theorem curveForm_smul (q : ℚ) (D : QDivisor X) (hD : D.IsQCartier)
    (hqD : (q • D).IsQCartier) :
    curveForm sX (q • D) hqD = (q : ℝ) • curveForm sX D hD := by
  refine MMP.ProgramBaseChange.linearMap_ext_numericalClass_cycle sX fun C => ?_
  rw [LinearMap.smul_apply, MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
    MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
    MMP.Mori.QDivisor.intersectionNumber_smul k sX C.ι C.dim_le q D hD hqD]
  push_cast; rfl

end CurveForm

end MMP.Fourfold.QDivisor

namespace MMP.Mori

open MMP.Fourfold

/-- On `N₁(X/S)` the pairing with a `ℚ`-Cartier `ℚ`-divisor is the pairing on `N₁(X)` composed
with the natural map `N₁(X/S) → N₁(X)`. -/
theorem QDivisor.relativeCurveForm_eq_comp {k : Type*} [Field k] {X S : Scheme}
    (sX : X ⟶ Spec (.of k)) (f : X ⟶ S) [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (D : QDivisor X) (h : D.IsQCartier) :
    QDivisor.relativeCurveForm sX f D h =
      QDivisor.curveForm sX D h ∘ₗ relativeToAbsolute sX f := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun Z => ?_)
  simp only [QDivisor.relativeCurveForm, QDivisor.curveForm, Finsupp.sum, LinearMap.comp_apply,
    LinearMap.sum_apply, LinearMap.smul_apply]
  rfl

section Helpers

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### Convex geometry in a finite-dimensional normed space -/

section Convex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Uniform negativity on an extremal face.** Let `C` be a closed cone in a finite-dimensional
real normed space, `A` a linear form positive on `C ∖ {0}` and `F` an extremal face of `C` on
which the linear form `L` is negative off `0`. For every linear form `M` there is `0 < ε` such
that `L - δ M` is negative on `F ∖ {0}` for every `0 ≤ δ < ε`. -/
private theorem exists_forall_sub_smul_neg {C F : Set E} (hC : IsCone ℝ C) (hCcl : IsClosed C)
    (hF : IsExtremalFace ℝ C F) {A L : E →ₗ[ℝ] ℝ} (hA : ∀ z ∈ C, z ≠ 0 → 0 < A z)
    (hL : ∀ z ∈ F, z ≠ 0 → L z < 0) (M : E →ₗ[ℝ] ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 ≤ δ → δ < ε → ∀ z ∈ F, z ≠ 0 → L z - δ * M z < 0 := by
  have hFconv : Convex ℝ F := fun x hx y hy a b ha hb _ =>
    hF.2.2.1 _ (MMP.Positivity.smul_mem_of_isCone hF.2.1 hx ha) _
      (MMP.Positivity.smul_mem_of_isCone hF.2.1 hy hb)
  have hFcl := MMP.Positivity.IsExtremalFace.isClosed hCcl hF hFconv
  have hAc := LinearMap.continuous_of_finiteDimensional A
  have hLc := LinearMap.continuous_of_finiteDimensional L
  have hMc := LinearMap.continuous_of_finiteDimensional M
  set K : Set E := {z | z ∈ F ∧ A z = 1}
  have hKc : IsCompact K := by
    refine (MMP.Positivity.isCompact_slice_of_normed hC hCcl hA 1).of_isClosed_subset
      (hFcl.inter (isClosed_eq hAc continuous_const)) fun z hz => ⟨hF.1 hz.1, hz.2.le⟩
  -- every nonzero point of `F` is a positive multiple of a point of `K`
  have hscale : ∀ z ∈ F, z ≠ 0 → 0 < A z ∧ (A z)⁻¹ • z ∈ K := fun z hz hz0 => by
    have ha := hA z (hF.1 hz) hz0
    exact ⟨ha, hF.2.1.2 z hz _ (inv_pos.mpr ha), by simp [ha.ne']⟩
  -- it suffices to treat `K`
  suffices h : ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 ≤ δ → δ < ε → ∀ z ∈ K, L z - δ * M z < 0 by
    obtain ⟨ε, hε, h⟩ := h
    refine ⟨ε, hε, fun δ hδ hδε z hz hz0 => ?_⟩
    obtain ⟨ha, hK⟩ := hscale z hz hz0
    have := h δ hδ hδε _ hK
    rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at this
    have e : L z - δ * M z = A z * ((A z)⁻¹ * L z - δ * ((A z)⁻¹ * M z)) := by
      field_simp
    rw [e]
    exact mul_neg_of_pos_of_neg ha this
  rcases K.eq_empty_or_nonempty with hK | hK
  · exact ⟨1, one_pos, fun δ _ _ z hz => by simp [hK] at hz⟩
  obtain ⟨z₀, hz₀, hmax⟩ := hKc.exists_isMaxOn hK hLc.continuousOn
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn hMc.continuousOn
  have hz₀0 : z₀ ≠ 0 := fun h => by simpa [h] using hz₀.2
  have hc : 0 < -L z₀ := neg_pos.mpr (hL z₀ hz₀.1 hz₀0)
  refine ⟨-L z₀ / (|B| + 1), by positivity, fun δ hδ hδε z hz => ?_⟩
  have hLz : L z ≤ L z₀ := hmax hz
  have hMz : |M z| ≤ |B| := (Real.norm_eq_abs _ ▸ hB z hz).trans (le_abs_self B)
  have h1 : δ * (|B| + 1) < -L z₀ := (lt_div_iff₀ (by positivity)).mp hδε
  have h2 : -(δ * M z) ≤ δ * |M z| := by
    rw [← mul_neg]; exact mul_le_mul_of_nonneg_left (neg_le_abs _) hδ
  nlinarith [mul_le_mul_of_nonneg_left hMz hδ]

/-- The image of an extremal face under an injective linear map is an extremal face of the image
cone. -/
private theorem IsExtremalFace.image {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W]
    [Module ℝ W] {N F : Set V} (hF : IsExtremalFace ℝ N F) {j : V →ₗ[ℝ] W}
    (hj : Function.Injective j) : IsExtremalFace ℝ (j '' N) (j '' F) := by
  obtain ⟨hFN, ⟨h0, hs⟩, hadd, hext⟩ := hF
  refine ⟨Set.image_mono hFN, ⟨⟨0, h0, map_zero j⟩, ?_⟩, ?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩ c hc
    exact ⟨c • v, hs v hv c hc, map_smul j c v⟩
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    exact ⟨u + v, hadd u hu v hv, map_add j u v⟩
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ ⟨m, hm, hmuv⟩
    rw [← map_add] at hmuv
    obtain rfl := hj hmuv
    obtain ⟨hu', hv'⟩ := hext u hu v hv hm
    exact ⟨⟨u, hu', rfl⟩, ⟨v, hv', rfl⟩⟩

end Convex

/-! ### Curve forms -/

section CurveForm

variable {k : Type} [Field k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k))
  [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX]

/-- The curve form of `D + (1 - δ)Δ` is that of `D + Δ` minus `δ` times that of `Δ`. -/
private theorem curveForm_add_one_sub_smul (D Δ : QDivisor X) (δ : ℚ)
    (h : (D + (1 - δ) • Δ).IsQCartier) (hDΔ : (D + Δ).IsQCartier) (hΔ : Δ.IsQCartier)
    (hδΔ : ((-δ) • Δ).IsQCartier) :
    QDivisor.curveForm sX (D + (1 - δ) • Δ) h =
      QDivisor.curveForm sX (D + Δ) hDΔ - (δ : ℝ) • QDivisor.curveForm sX Δ hΔ := by
  have e : D + (1 - δ) • Δ = (D + Δ) + (-δ) • Δ := by
    rw [sub_smul, one_smul, neg_smul]; abel
  rw [show QDivisor.curveForm sX (D + (1 - δ) • Δ) h =
      QDivisor.curveForm sX ((D + Δ) + (-δ) • Δ) (e ▸ h) from by congr 1,
    MMP.Fourfold.QDivisor.curveForm_add sX _ _ hDΔ hδΔ,
    MMP.Fourfold.QDivisor.curveForm_smul sX _ _ hΔ]
  simp [sub_eq_add_neg]

end CurveForm

/-- The natural map `N₁(X/S) → N₁(X)` is injective. -/
private theorem relativeToAbsolute_injective {k : Type} [Field k] {X S : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (f : X ⟶ S) : Function.Injective (relativeToAbsolute sX f) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX f z
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (mem_relativeNumericallyTrivial.mpr ((Submodule.Quotient.mk_eq_zero _).mp hz))

/-- A projective variety carries a Cartier divisor whose invertible sheaf is ample. -/
private theorem exists_isAmple_sheaf {k : Type*} [Field k] {X : Scheme} {sX : X ⟶ Spec (.of k)}
    [h : AlgebraicGeometry.IsProjectiveVariety k sX] :
    ∃ D : X.CartierDivisor, Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf D) := by
  obtain ⟨⟨L, hL, hrel, hA⟩, -⟩ :=
    MMP.Foundations.IsProjective.exists_isRelativelyAmple h.isProjective.isProjective
  obtain ⟨A, ⟨e⟩⟩ := hA h.toIsIntegral
  exact ⟨A, (Stacks.RelativeVeryAmple.isAmple_congr _ _ e).mpr
    (Stacks.HProjective.isAmple_of_isRelativelyAmple_of_isAffine sX L hrel)⟩

/-- **Coordinates for the relative cone.** The natural map `N₁(X/S) → N₁(X)` followed by a
Cartier coordinate system `N₁(X) ≃ ℝ^ι` is an injective linear map `j` carrying `NE̅(X/S)` onto a
closed cone of `ℝ^ι`, on which some linear form (an ample divisor) is positive off `0`. -/
private theorem exists_coordinates_relativeClosedConeOfCurves {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X S : Scheme.{0}} (sX : X ⟶ Spec (.of k)) (sS : S ⟶ Spec (.of k))
    [MMP.Mori.IsProjectiveVariety k sX] [MMP.Mori.IsProjectiveVariety k sS] (f : X ⟶ S)
    (hf : f ≫ sS = sX) :
    ∃ (ι : Type) (_ : Fintype ι) (Φ : NumericalCurveClasses sX ≃L[ℝ] (ι → ℝ))
      (A : (ι → ℝ) →ₗ[ℝ] ℝ),
      Function.Injective (Φ.toLinearMap ∘ₗ relativeToAbsolute sX f) ∧
      IsCone ℝ ((Φ.toLinearMap ∘ₗ relativeToAbsolute sX f) ''
        (relativeClosedConeOfCurves sX f : Set _)) ∧
      IsClosed ((Φ.toLinearMap ∘ₗ relativeToAbsolute sX f) ''
        (relativeClosedConeOfCurves sX f : Set _)) ∧
      ∀ z ∈ (Φ.toLinearMap ∘ₗ relativeToAbsolute sX f) ''
        (relativeClosedConeOfCurves sX f : Set _), z ≠ 0 → 0 < A z := by
  obtain ⟨hfd, -, hext, hcoord, -⟩ :=
    NumericalCurveClasses.exists_cartier_coordinates_of_isProperVariety sX
  obtain ⟨t, -, ht, htspan⟩ := hext ∅ (linearIndepOn_empty _ _)
  rw [Set.image_eq_range] at htspan
  obtain ⟨⟨Φ, -⟩, -⟩ := hcoord (fun E : t => (E : X.CartierDivisor)) ht htspan
  have := hfd
  have : Fintype t := @Fintype.ofFinite _ ht.finite
  set ι := relativeToAbsolute sX f
  set j := Φ.toLinearMap ∘ₗ ι
  have hNimg := image_relativeClosedConeOfCurves_eq_inter_range sX sS f hf
  obtain ⟨H, hH⟩ := exists_isAmple_sheaf (sX := sX)
  set Aform := NumericalCurveClasses.intersectionNumber (sX := sX) (KCartierDivisor.ofCartier ℝ H)
  refine ⟨t, inferInstance, Φ, Aform ∘ₗ Φ.symm.toLinearMap,
    Φ.injective.comp (relativeToAbsolute_injective sX f), ?_, ?_, ?_⟩
  · exact isCone_coe ((relativeClosedConeOfCurves sX f).map j)
  · rw [show (j : _ → _) = Φ ∘ ι from rfl, Set.image_comp, hNimg, Set.image_inter Φ.injective,
      ← Set.range_comp]
    refine (Φ.toHomeomorph.isClosedMap _ isClosed_closure).inter ?_
    rw [show (Φ ∘ ι) = (j : _ → _) from rfl, ← LinearMap.coe_range]
    exact (LinearMap.range j).closed_of_finiteDimensional
  · rintro _ ⟨w, hw, rfl⟩ hw0
    have hιw : ι w ∈ closedConeOfCurves sX := (hNimg.subset ⟨w, hw, rfl⟩).1
    obtain ⟨Z, hZ⟩ := OneCycle.numericalClass_surjective sX (ι w)
    change 0 < Aform (Φ.symm (Φ (ι w)))
    rw [Φ.symm_apply_apply, ← hZ, NumericalCurveClasses.intersectionNumber_numericalClass]
    exact closedConeOfCurves_diff_zero_subset_posHalfspace sX H hH
      ⟨hιw, fun h => hw0 (by simp [Set.mem_singleton_iff.mp h])⟩ Z hZ

end Helpers

/-- Let `(X, Δ)` be a dlt pair (with canonical divisor `K` of dimension `n`), with `X` a
`ℚ`-factorial projective variety over an algebraically closed field of characteristic zero, and
`f : X ⟶ S` a morphism of projective varieties. If `F` is an extremal face of
`relativeClosedConeOfCurves sX f` with `((K + Δ) · z) < 0` for every `z ∈ F`, `z ≠ 0`, then there
is a rational `0 < δ < 1` such that `(X, (1 - δ)Δ)` is klt and `((K + (1 - δ)Δ) · z) < 0` for
every `z ∈ F`, `z ≠ 0`. -/
@[mmp "lem_km3c_dlt_negative_face_is_klt_negative"]
theorem IsDltPair.exists_isKltPair_one_sub_smul_of_isExtremalFace
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X S : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} (sS : S ⟶ Spec (.of k)) [IsProjectiveVariety k sX]
    [IsProjectiveVariety k sS] [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] (f : X ⟶ S) (hf : f ≫ sS = sX)
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} (hΔ : IsDltPair sX n K Δ) (hX : IsQFactorial sX)
    {F : Set (RelativeNumericalCurveClasses sX f)}
    (hF : IsExtremalFace ℝ (relativeClosedConeOfCurves sX f :
      Set (RelativeNumericalCurveClasses sX f)) F)
    (hneg : ∀ z ∈ F, z ≠ 0 →
      QDivisor.relativeCurveForm sX f (Divisor.toQDivisor K + Δ) hΔ.1.2.2 z < 0) :
    ∃ δ : ℚ, 0 < δ ∧ δ < 1 ∧ ∃ hδ : IsKltPair sX n K ((1 - δ) • Δ),
      ∀ z ∈ F, z ≠ 0 →
        QDivisor.relativeCurveForm sX f (Divisor.toQDivisor K + (1 - δ) • Δ) hδ.1.2.2 z < 0 := by
  obtain ⟨ι, _, Φ, A, hj, hC, hCcl, hA⟩ := exists_coordinates_relativeClosedConeOfCurves sX sS f hf
  set j := Φ.toLinearMap ∘ₗ relativeToAbsolute sX f
  have hQ := isQCartier_of_isQFactorial sX hX
  set L := QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hΔ.1.2.2
  set M := QDivisor.curveForm sX Δ (hQ Δ)
  obtain ⟨ε, hε, hεneg⟩ := exists_forall_sub_smul_neg hC hCcl (IsExtremalFace.image hF hj) hA
    (L := L ∘ₗ Φ.symm.toLinearMap) (by
      rintro _ ⟨w, hw, rfl⟩ hw0
      have := hneg w hw fun h => hw0 (by simp [h])
      rw [QDivisor.relativeCurveForm_eq_comp] at this
      simpa [j, L] using this) (M ∘ₗ Φ.symm.toLinearMap)
  obtain ⟨δ₀, hδ₀, hklt⟩ := hΔ.exists_forall_isKltPair_one_sub_smul hX
    (isQuasiProjective_of_isProjective
      (AlgebraicGeometry.IsProjectiveVariety.isProjective (k := k) (f := sX)).isProjective)
  obtain ⟨δ, hδpos, hδlt⟩ := exists_rat_btwn (lt_min hε (lt_min (Rat.cast_pos.mpr hδ₀) one_pos))
  simp only [lt_min_iff] at hδlt
  obtain ⟨hδε, hδδ₀, hδ1⟩ := hδlt
  have hδpos' : (0 : ℚ) < δ := mod_cast hδpos
  have hδklt := hklt δ hδpos' (mod_cast hδδ₀)
  refine ⟨δ, hδpos', mod_cast hδ1, hδklt, fun z hz hz0 => ?_⟩
  rw [QDivisor.relativeCurveForm_eq_comp, LinearMap.comp_apply,
    curveForm_add_one_sub_smul sX _ _ _ _ hΔ.1.2.2 (hQ Δ) (hQ _)]
  simpa [j, L, M, sub_eq_add_neg] using
    hεneg δ hδpos.le hδε (j z) ⟨z, hz, rfl⟩ fun h => hz0 (hj (by simpa using h))

end MMP.Mori
