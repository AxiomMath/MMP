module

public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.AmpleStrictlyPositive
public import MMP.AlgebraicGeometry.Intersection.N1CartierCoordinates
public import MMP.AlgebraicGeometry.Resolution.MaximalOrderAttained
public import MMP.Analysis.Convex.Cone.ExtremalRays

/-!
# Negative extremal rays in a nef-null face

Let `(X, Θ)` be a klt log variety in the sense of Kollár et al., with `Θ` a `ℚ`-divisor and
`K_X + Θ` `ℚ`-Cartier, where `X` is a projective variety over an algebraically closed field of
characteristic zero. Let `L` be a nef `ℚ`-Cartier `ℚ`-divisor and `z ∈ NE̅(X)` a class with
`L · z = 0` and `(K_X + Θ) · z < 0`. Then there is a `(K_X + Θ)`-negative extremal ray `R` of
`NE̅(X)` on which `L` vanishes identically.

The nef form `L` cuts out the extremal face `F = NE̅(X) ∩ L^⊥` of `NE̅(X)`, which contains `z`.
In Cartier coordinates `N₁(X) ≃ ℝ^r`, `F` is a closed convex cone, and it contains no line
because an ample divisor is positive on `NE̅(X) \ {0}`. Hence `z` is a finite sum of elements of
extremal rays of `F`; one of the summands is `(K_X + Θ)`-negative, so its ray is
`(K_X + Θ)`-negative. An extremal ray of the extremal face `F` is an extremal ray of `NE̅(X)`,
and `L` vanishes on it.

## Main results

* `MMP.Flips.IsKawamataLogTerminal.exists_isNegativeExtremalRayOf_of_curveForm_eq_zero`.

## Implementation notes

The extremal rays come from the decomposition of a closed pointed cone into extremal rays,
`MMP.Positivity.exists_sum_mem_isExtremalRay`, applied to the face `F`, rather than from the
curves of the cone theorem: the cone theorem in the form
`MMP.Mori.exists_countable_isRationalCurve_closedConeOfCurves_eq` does not assert that its
curves span extremal rays.

The source works over `ℂ`; the statement is made over any algebraically closed field of
characteristic zero, and in any dimension `n`. Intersection numbers with classes in `N₁(X)` are
the linear forms `MMP.Fourfold.QDivisor.curveForm`; nefness is
`MMP.Fourfold.QDivisor.IsNefOnCurves`, nonnegativity on every proper curve.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 1.15, 3.7
* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], Ch. 15
* [KM98] J. Kollár, S. Mori, *Birational geometry of algebraic varieties*, Thm. 3.7.
-/

section

open CategoryTheory AlgebraicGeometry

namespace MMP.FourfoldProofs.FourfoldFa15ProjectiveNefNullConeProof

open MMP MMP.Flips MMP.Mori MMP.Fourfold

/-- A projective variety carries a Cartier divisor whose invertible sheaf is ample. -/
private theorem exists_isAmple_sheaf {k : Type*} [Field k] {X : Scheme} {sX : X ⟶ Spec (.of k)}
    [h : AlgebraicGeometry.IsProjectiveVariety k sX] :
    ∃ D : X.CartierDivisor, Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf D) := by
  obtain ⟨⟨L, hL, hrel, hA⟩, -⟩ :=
    MMP.Foundations.IsProjective.exists_isRelativelyAmple h.isProjective.isProjective
  obtain ⟨A, ⟨e⟩⟩ := hA h.toIsIntegral
  exact ⟨A, (Stacks.RelativeVeryAmple.isAmple_congr _ _ e).mpr
    (Stacks.HProjective.isAmple_of_isRelativelyAmple_of_isAffine sX L hrel)⟩

/-- A linear form on a real vector space with a continuous linear equivalence to `ι → ℝ`, `ι`
finite, is continuous. -/
theorem continuous_of_continuousLinearEquiv_pi {E ι : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [Finite ι] (Φ : E ≃L[ℝ] (ι → ℝ)) (f : E →ₗ[ℝ] ℝ) : Continuous f := by
  have : (f : E → ℝ) = (f ∘ₗ Φ.symm.toLinearMap) ∘ Φ := by
    ext w
    simp
  rw [this]
  exact (LinearMap.continuous_of_finiteDimensional _).comp Φ.continuous

/-- A nef `ℚ`-Cartier `ℚ`-divisor with continuous intersection form is nonnegative on
`NE̅(X)`. -/
theorem curveForm_nonneg_of_mem_closedConeOfCurves {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] [LocallyOfFiniteType sX] {L : QDivisor X} (hL : QDivisor.IsNefOnCurves sX L)
    (hc : Continuous (QDivisor.curveForm sX L hL.1)) {w : NumericalCurveClasses sX}
    (hw : w ∈ closedConeOfCurves sX) : 0 ≤ QDivisor.curveForm sX L hL.1 w := by
  have hsub : (coneOfCurves sX : Set (NumericalCurveClasses sX)) ⊆
      {w | 0 ≤ QDivisor.curveForm sX L hL.1 w} := by
    intro w hw
    change w ∈ PointedCone.hull ℝ _ at hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨C, rfl⟩ := hx
      exact hL.2 C
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Set.mem_ofPred_eq, map_add] at hx hy ⊢
      exact add_nonneg hx hy
    | smul c x _ hx =>
      simp only [Set.mem_ofPred_eq] at hx ⊢
      change 0 ≤ QDivisor.curveForm sX L hL.1 ((c : ℝ) • x)
      rw [map_smul, smul_eq_mul]
      exact mul_nonneg c.2 hx
  exact closure_minimal hsub (isClosed_le continuous_const hc) hw

/-- The image under a linear equivalence of a set containing `0`, on which a linear form is
positive off `0`, meets its negative only in `0`. -/
theorem image_inter_neg_image_eq_singleton_zero {E V : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup V] [Module ℝ V] (Φ : E ≃ₗ[ℝ] V) {S : Set E} (h0 : (0 : E) ∈ S)
    (a : E →ₗ[ℝ] ℝ) (ha : ∀ w ∈ S, w ≠ 0 → 0 < a w) : Φ '' S ∩ -(Φ '' S) = {0} := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_neg, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨p, hp, rfl⟩, ⟨q, hq, hqp⟩⟩
    obtain rfl : q = -p := Φ.injective (by rw [hqp, map_neg])
    by_contra hp0
    have hp0' : p ≠ 0 := fun h => hp0 (by simp [h])
    have h₂ := ha (-p) hq (neg_ne_zero.2 hp0')
    rw [map_neg] at h₂
    linarith [ha p hp hp0']
  · rintro rfl
    exact ⟨⟨0, h0, map_zero Φ⟩, ⟨0, h0, by simp⟩⟩

/-- The image of a cone under a linear map is a cone. -/
theorem isCone_image {E V : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup V] [Module ℝ V]
    (Φ : E →ₗ[ℝ] V) {S : Set E} (hS : IsCone ℝ S) : IsCone ℝ (Φ '' S) := by
  refine ⟨⟨0, hS.1, map_zero Φ⟩, ?_⟩
  rintro _ ⟨p, hp, rfl⟩ c hc
  exact ⟨c • p, hS.2 p hp c hc, map_smul Φ c p⟩

end MMP.FourfoldProofs.FourfoldFa15ProjectiveNefNullConeProof

end

section

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Flips

open MMP.Mori MMP.Fourfold MMP.FourfoldProofs.FourfoldFa15ProjectiveNefNullConeProof

/-- **A negative extremal ray in a nef-null face.** Let `X` be a projective variety over an
algebraically closed field of characteristic zero, `K` a canonical divisor and `Θ` a `ℚ`-divisor
with `K + Θ` `ℚ`-Cartier such that `(X, Θ)` is klt (`MMP.Flips.IsKawamataLogTerminal`). Let `L`
be a nef `ℚ`-Cartier `ℚ`-divisor and `z ∈ NE̅(X)` with `L · z = 0` and `(K + Θ) · z < 0`. Then
there is a `(K + Θ)`-negative extremal ray `R` of `NE̅(X)` with `L · u = 0` for all `u ∈ R`. -/
@[mmp "thm_fourfold_fa15_projective_nef_null_cone"]
public theorem IsKawamataLogTerminal.exists_isNegativeExtremalRayOf_of_curveForm_eq_zero
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] [LocallyOfFiniteType sX] {n : ℕ} {K : Divisor X} {Θ : QDivisor X}
    (_hklt : IsKawamataLogTerminal sX n K (QDivisor.toRDivisor Θ))
    (hKΘ : (Divisor.toQDivisor K + Θ).IsQCartier)
    (hXp : MMP.Mori.IsProjectiveVariety k sX) {L : QDivisor X}
    (hL : QDivisor.IsNefOnCurves sX L) {z : NumericalCurveClasses sX}
    (hz : z ∈ closedConeOfCurves sX) (hLz : QDivisor.curveForm sX L hL.1 z = 0)
    (hKz : QDivisor.curveForm sX (Divisor.toQDivisor K + Θ) hKΘ z < 0) :
    ∃ R : Set (NumericalCurveClasses sX),
      IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + Θ) R ∧
        ∀ u ∈ R, QDivisor.curveForm sX L hL.1 u = 0 := by
  have := hXp
  obtain ⟨hfd, -, hext, hcoord, -⟩ :=
    NumericalCurveClasses.exists_cartier_coordinates_of_isProperVariety sX
  obtain ⟨t, -, ht, htspan⟩ := hext ∅ (linearIndepOn_empty _ _)
  obtain ⟨⟨Φ, -⟩, -⟩ := hcoord (fun E : t => (E : X.CartierDivisor)) ht
    (by rwa [Set.image_eq_range] at htspan)
  have := hfd
  have : Fintype t := @Fintype.ofFinite _ ht.finite
  set N : Set (NumericalCurveClasses sX) :=
    ((closedConeOfCurves sX : PointedCone ℝ _) : Set (NumericalCurveClasses sX))
  set ℓ := QDivisor.curveForm sX L hL.1
  set d := QDivisor.curveForm sX (Divisor.toQDivisor K + Θ) hKΘ
  obtain ⟨H, hH⟩ := exists_isAmple_sheaf (sX := sX)
  set a := NumericalCurveClasses.intersectionNumber (sX := sX) (KCartierDivisor.ofCartier ℝ H)
  have ha : ∀ w ∈ N, w ≠ 0 → 0 < a w := fun w hw hw0 => by
    obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX w
    rw [NumericalCurveClasses.intersectionNumber_numericalClass]
    exact closedConeOfCurves_diff_zero_subset_posHalfspace sX H hH ⟨hw, hw0⟩ Z rfl
  have hcont := continuous_of_continuousLinearEquiv_pi Φ
  have hNadd : ∀ u ∈ N, ∀ v ∈ N, u + v ∈ N := fun _ hu _ hv => add_mem hu hv
  set F := faceOfNefForm N ℓ
  have hF : IsExtremalFace ℝ N F := isExtremalFace_faceOfNefForm (isCone_coe _) hNadd
    fun _ hw => curveForm_nonneg_of_mem_closedConeOfCurves hL (hcont ℓ) hw
  have hFcl : IsClosed F := show IsClosed (closure (coneOfCurves sX : Set _) ∩ {y | ℓ y = 0}) from
    isClosed_closure.inter (isClosed_eq (hcont ℓ) continuous_const)
  set F' : Set (t → ℝ) := Φ '' F with hF'def
  have hF'cone : IsCone ℝ F' := isCone_image Φ.toLinearMap hF.2.1
  have hF'conv : Convex ℝ F' := Convex.linear_image (s := F) (fun p hp q hq b c hb hc _ =>
    ⟨hNadd _ ((closedConeOfCurves sX).smul_mem hb hp.1) _
      ((closedConeOfCurves sX).smul_mem hc hq.1), by simp [hp.2, hq.2]⟩) Φ.toLinearMap
  have hF'pt : F' ∩ -F' = {0} :=
    image_inter_neg_image_eq_singleton_zero Φ.toLinearEquiv hF.2.1.1 a fun w hw => ha w hw.1
  obtain ⟨s, R, w, hR, hzw⟩ := MMP.Positivity.exists_sum_mem_isExtremalRay hF'cone hF'conv
    (Φ.toHomeomorph.isClosedMap F hFcl) hF'pt (v := Φ z) ⟨z, ⟨hz, hLz⟩, rfl⟩
  obtain ⟨i, hi⟩ : ∃ i, d (Φ.symm (w i)) < 0 := by
    by_contra! hcon
    have h : d (∑ i, Φ.symm (w i)) < 0 := by
      rwa [← map_sum, ← hzw, ContinuousLinearEquiv.symm_apply_apply]
    rw [map_sum] at h
    linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hcon i]
  obtain ⟨hRi, hwi⟩ := hR i
  have hRF : IsExtremalRay ℝ F (Φ.symm '' R i) := by
    simpa [hF'def, Set.image_image] using
      MMP.ProgramBaseChange.isExtremalRay_image Φ.symm.toLinearEquiv hRi
  obtain ⟨v, -, hRv⟩ := hRi.2
  obtain ⟨c₀, hc₀, hc₀v⟩ := hRv ▸ hwi
  rw [← hc₀v, map_smul, map_smul, smul_eq_mul] at hi
  have hdv := neg_of_mul_neg_right hi hc₀
  refine ⟨Φ.symm '' R i, ⟨hKΘ, ⟨MMP.Positivity.isExtremalFace_trans hF hRF.1, hRF.2⟩, ?_⟩,
    fun _ hu => (hRF.1.1 hu).2⟩
  rintro _ ⟨y, hy, rfl⟩ hy0
  obtain ⟨c, hc, rfl⟩ := hRv ▸ hy
  rw [map_smul] at hy0 ⊢
  have hc0 : c ≠ 0 := fun h' => hy0 (by simp [h'])
  rw [map_smul, smul_eq_mul]
  exact mul_neg_of_pos_of_neg (lt_of_le_of_ne hc (Ne.symm hc0)) hdv

end MMP.Flips

end

end
