module

public import MMP.AlgebraicGeometry.MMP.Contraction.SupportingDivisorDescent
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.NegativeFaceCurve

universe u

section

/-!
# Line bundles trivial on a negative extremal face descend to its contraction

Let `(X, Δ)` be a klt pair, `X` a projective variety over an algebraically closed field `k` of
characteristic zero and `Δ ≥ 0`, let `F` be a `(K_X + Δ)`-negative extremal face of `NE̅(X)`,
`g : X ⟶ Z` a contraction of `F`, and `L` an invertible sheaf with `deg_C L = 0` for every curve
`C` with `[C] ∈ F`. Then `L ≅ g^* L_Z` for an invertible sheaf `L_Z` on `Z`.

Write `L ≅ 𝒪_X(E)` for a Cartier divisor `E` and let `D` be a supporting divisor of `F`. The form
`(E · _)` vanishes on `F`: `F` is spanned by negative extremal rays, each of which contains the
class of a curve, and classes of curves are nonzero on a projective variety. Then `E + mD` is a
supporting divisor of `F` for some `m > 0`: if `F = {0}`, `D` is ample by Kleiman's criterion,
`mD + E` is ample for `m ≫ 0` and hence positive on `NE̅(X) ∖ {0}`; otherwise `K_X + Δ` is not
nef, and the supporting forms of `F` are an open cone in `⟨F⟩^⊥` containing `(D · _)`, so it
also contains `(D · _) + (1/m) (E · _)` for `m ≫ 0`. Both `mD` and `E + mD` are then linearly
equivalent to pull-backs `g^*D_Z`, `g^*M_Z`, so `E ∼ g^*(M_Z - D_Z)` and
`L ≅ 𝒪_X(g^*(M_Z - D_Z)) ≅ g^*𝒪_Z(M_Z - D_Z)`.

## Main results

* `MMP.Mori.exists_isInvertible_iso_pullback_of_isContractionOfFace`: the statement above.

## Implementation notes

An irreducible curve `C ⊆ X` is a `MMP.Mori.ProperCurve`, its class is
`OneCycle.numericalClass sX (C.cycle ℝ)` (the class used in `MMP.Mori.IsContractionOfFace`), and
`(L · C)` is `MMP.Mori.ProperCurve.degree`. A line bundle is an invertible sheaf of
`𝒪`-modules, and `g^*` is `AlgebraicGeometry.Scheme.Modules.pullback g`. The pull-back of
Cartier divisors used is `MMP.CartierDivisor.pullback` to an integral scheme, with its additivity
`f^*(A - B) = f^*A - f^*B` (`MMP.CartierDivisor.pullback_sub`).

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Theorem 3.7(4)
-/

open CategoryTheory AlgebraicGeometry MMP.Mori

namespace MMP.FourfoldProofs.Km3bContractionPullbackLineBundleProof

section CartierPullback

variable {X : Scheme.{u}}

/-- `|A - B| ⊆ |A| ∪ |B|`. -/
private theorem notMem_support_sub {A B : X.CartierDivisor} {x : X}
    (hA : x ∉ MMP.Intersection.cartierSupport A)
    (hB : x ∉ MMP.Intersection.cartierSupport B) : x ∉ MMP.Intersection.cartierSupport (A - B) := by
  simp only [MMP.Intersection.cartierSupport, Set.mem_setOf_eq, not_not, map_sub] at hA hB ⊢
  rw [hA, hB, sub_zero]

end CartierPullback

section Forms

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}

/-- `deg_C 𝒪_X(E + E') = deg_C 𝒪_X(E) + deg_C 𝒪_X(E')` along a proper curve. -/
private theorem degree_cartierSheaf_add (C : ProperCurve sX) (E E' : X.CartierDivisor) :
    C.degree k (MMP.CartierDivisor.sheaf (E + E')) =
      C.degree k (MMP.CartierDivisor.sheaf E) +
        C.degree k (MMP.CartierDivisor.sheaf E') := by
  haveI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
        X.toRingedSpace.IsSheaf⟩).obj (MMP.CartierDivisor.sheaf E)).obj
          (MMP.CartierDivisor.sheaf E')) :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible X.presheaf X.ringCatSheaf.2 _ _
  unfold ProperCurve.degree
  rw [← degreeOn_tensorSheaf]
  exact (degreeOn_eq_of_iso k sX C.ι C.dim_le
    (L := ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
        X.toRingedSpace.IsSheaf⟩).obj (MMP.CartierDivisor.sheaf E)).obj
          (MMP.CartierDivisor.sheaf E'))
    (MMP.CartierDivisorSheaf.sheafMulIso E E')).symm

variable (sX) in
/-- The form `z ↦ (E · z)` on `N₁(X)` of a Cartier divisor `E`, additive in `E`. -/
private noncomputable def cartierForm :
    X.CartierDivisor →+ Module.Dual ℝ (NumericalCurveClasses sX) :=
  AddMonoidHom.mk' (fun E => NumericalCurveClasses.intersectionNumber
      (KCartierDivisor.ofCartier ℝ E)) fun E E' => by
    refine LinearMap.ext fun z => ?_
    obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX z
    simp only [LinearMap.add_apply, NumericalCurveClasses.intersectionNumber_numericalClass,
      OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree, OneCycle.degree_apply]
    rw [← Finsupp.sum_add]
    refine Finsupp.sum_congr fun C _ => ?_
    rw [degree_cartierSheaf_add]
    push_cast
    ring

private theorem cartierForm_apply (E : X.CartierDivisor) :
    cartierForm sX E = NumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ E) :=
  rfl

/-- The form of `E` at the class of a curve `C` is `deg_C L` for any `L ≅ 𝒪_X(E)`. -/
private theorem cartierForm_numericalClass_cycle {E : X.CartierDivisor} {L : X.Modules}
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (e : L ≅ MMP.CartierDivisor.sheaf E) (C : ProperCurve sX) :
    cartierForm sX E (OneCycle.numericalClass sX (C.cycle ℝ)) = (C.degree k L : ℝ) := by
  rw [cartierForm_apply, NumericalCurveClasses.intersectionNumber_numericalClass,
    OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree, OneCycle.degree_cycle]
  unfold ProperCurve.degree
  rw [degreeOn_eq_of_iso k sX C.ι C.dim_le e]

/-- A supporting divisor in terms of its form: nonnegative on `NE̅(X)` with zero set `F`. -/
private theorem isSupportingDivisor_iff [AlgebraicGeometry.IsProjectiveVariety k sX]
    {F : Set (NumericalCurveClasses sX)} (D : X.CartierDivisor) :
    IsSupportingDivisor k sX F D ↔ (∀ z ∈ closedConeOfCurves sX, 0 ≤ cartierForm sX D z) ∧
      {z | z ∈ closedConeOfCurves sX ∧ cartierForm sX D z = 0} = F := by
  unfold IsSupportingDivisor
  refine and_congr ?_ Iff.rfl
  rw [KCartierDivisor.isNef_iff_closedConeOfCurves_subset_nonnegHalfspace sX]
  refine ⟨fun h z hz => ?_, fun h z hz => ?_⟩
  · have := h hz
    rwa [KCartierDivisor.mem_nonnegHalfspace_iff] at this
  · rw [KCartierDivisor.mem_nonnegHalfspace_iff]
    exact h z hz

/-- A projective variety carries a Cartier divisor whose invertible sheaf is ample. -/
private theorem exists_isAmple_sheaf [h : AlgebraicGeometry.IsProjectiveVariety k sX] :
    ∃ D : X.CartierDivisor, Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf D) := by
  obtain ⟨⟨L, hL, hrel, hA⟩, -⟩ :=
    MMP.Foundations.IsProjective.exists_isRelativelyAmple h.isProjective.isProjective
  obtain ⟨A, ⟨e⟩⟩ := hA h.toIsIntegral
  exact ⟨A, (Stacks.RelativeVeryAmple.isAmple_congr _ _ e).mpr
    (Stacks.HProjective.isAmple_of_isRelativelyAmple_of_isAffine sX L hrel)⟩

/-- On a projective variety the class of a curve in `N₁(X)` is nonzero. -/
private theorem numericalClass_cycle_ne_zero [AlgebraicGeometry.IsProjectiveVariety k sX]
    (C : ProperCurve sX) : OneCycle.numericalClass sX (C.cycle ℝ) ≠ 0 := by
  obtain ⟨H, hH⟩ := exists_isAmple_sheaf (sX := sX)
  intro h0
  have hpos := MMP.Threefold.Mori.degreeOn_cartierSheaf_pos_of_isAmple
    (inferInstance : AlgebraicGeometry.IsVariety k sX) H hH C
  have h1 := cartierForm_numericalClass_cycle (Iso.refl _) C (E := H)
  rw [h0, map_zero] at h1
  unfold ProperCurve.degree at h1
  exact_mod_cast hpos.ne' (by exact_mod_cast h1.symm)

/-- A positive multiple of a supporting divisor of `F` supports `F`. -/
theorem isSupportingDivisor_nsmul [AlgebraicGeometry.IsProjectiveVariety k sX]
    {F : Set (NumericalCurveClasses sX)} {D : X.CartierDivisor} {m : ℕ} (hm : 0 < m)
    (hD : IsSupportingDivisor k sX F D) : IsSupportingDivisor k sX F (m • D) := by
  rw [isSupportingDivisor_iff] at hD ⊢
  rw [map_nsmul]
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨fun z hz => ?_, ?_⟩
  · rw [LinearMap.smul_apply, nsmul_eq_mul]
    exact mul_nonneg m.cast_nonneg (hD.1 z hz)
  · rw [← hD.2]
    ext z
    simp only [Set.mem_setOf_eq, LinearMap.smul_apply, nsmul_eq_mul, mul_eq_zero, hm', false_or]

end Forms

section Descent

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
  [AlgebraicGeometry.IsProjectiveVariety k sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
  {F : Set (NumericalCurveClasses sX)}

/-- The form of `E` vanishes on a negative extremal face `F` if `deg_C 𝒪_X(E) = 0` on `F`. -/
theorem cartierForm_eq_zero_of_mem_face (hklt : IsKltPair sX n K Δ) (hΔ : Δ.IsEffective)
    (hF : IsNegativeExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
      (MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2) F)
    {E : X.CartierDivisor} {L : X.Modules}
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (eL : L ≅ MMP.CartierDivisor.sheaf E)
    (hL : ∀ C : ProperCurve sX, OneCycle.numericalClass sX (C.cycle ℝ) ∈ F → C.degree k L = 0) :
    ∀ z ∈ F, cartierForm sX E z = 0 := by
  obtain ⟨m, ξ, hFξ, hray⟩ := exists_eq_hull_of_isNegativeExtremalFace hklt hΔ hF
  have hξ : ∀ j, cartierForm sX E (ξ j) = 0 := by
    intro j
    obtain ⟨_, ⟨hRface, v, hv0, hRv⟩, hneg⟩ := hray j
    have hRF : IsNegativeExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
        (MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2)
        {w | ∃ c : ℝ, 0 ≤ c ∧ c • (ξ j : NumericalCurveClasses sX) = w} :=
      ⟨hRface, hRface.2.2.1, hneg⟩
    have hR0 : {w | ∃ c : ℝ, 0 ≤ c ∧ c • (ξ j : NumericalCurveClasses sX) = w} ≠ {0} := by
      intro h
      have hv : v ∈ {w | ∃ c : ℝ, 0 ≤ c ∧ c • (ξ j : NumericalCurveClasses sX) = w} := by
        rw [hRv]
        exact ⟨1, zero_le_one, one_smul _ _⟩
      rw [h] at hv
      exact hv0 hv
    obtain ⟨C, c, hc, hcξ⟩ :=
      exists_properCurve_numericalClass_mem_of_isNegativeExtremalFace hklt hΔ hRF hR0
    have hCF : OneCycle.numericalClass sX (C.cycle ℝ) ∈ F := by
      rw [← hcξ, hFξ]
      exact PointedCone.smul_mem _ hc (PointedCone.subset_hull ⟨j, rfl⟩)
    have hdeg : cartierForm sX E (OneCycle.numericalClass sX (C.cycle ℝ)) = 0 := by
      rw [cartierForm_numericalClass_cycle eL, hL C hCF, Int.cast_zero]
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hcξ
      exact numericalClass_cycle_ne_zero C hcξ.symm
    rw [← hcξ, map_smul, smul_eq_mul] at hdeg
    exact (mul_eq_zero.mp hdeg).resolve_left hc0
  intro z hz
  rw [hFξ] at hz
  have : PointedCone.hull ℝ (Set.range fun j => (ξ j : NumericalCurveClasses sX)) ≤
      (LinearMap.ker (cartierForm sX E)).restrictScalars _ :=
    Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hξ j)
  exact this hz

/-- If `F = {0}` and `D` supports `F`, then `E + m • D` supports `F` for some `m > 0`. -/
theorem exists_isSupportingDivisor_add_nsmul_of_eq_zero {D : X.CartierDivisor}
    (hD : IsSupportingDivisor k sX F D) (E : X.CartierDivisor) (hF0 : F = {0}) :
    ∃ m : ℕ, 0 < m ∧ IsSupportingDivisor k sX F (E + m • D) := by
  rw [isSupportingDivisor_iff] at hD
  have hDpos : ∀ z ∈ closedConeOfCurves sX, z ≠ 0 →
      0 < NumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ D) z := by
    intro z hz hz0
    refine lt_of_le_of_ne (hD.1 z hz) fun h => hz0 ?_
    have : z ∈ F := hD.2 ▸ ⟨hz, h.symm⟩
    rwa [hF0] at this
  have hDamp := (isAmple_cartierSheaf_iff_forall_closedConeOfCurves_pos sX D).2 hDpos
  obtain ⟨m, hamp, hm⟩ := ((eventually_isAmple_cartierSheaf_nsmul_add D E hDamp).and
    (Filter.eventually_gt_atTop 0)).exists
  have hpos := (isAmple_cartierSheaf_iff_forall_closedConeOfCurves_pos sX (m • D + E)).1 hamp
  refine ⟨m, hm, ?_⟩
  rw [add_comm, isSupportingDivisor_iff]
  refine ⟨fun z hz => ?_, ?_⟩
  · rcases eq_or_ne z 0 with rfl | hz0
    · simp
    · exact (hpos z hz hz0).le
  · rw [hF0]
    ext z
    refine ⟨fun ⟨hz, hz'⟩ => ?_, fun hz => ?_⟩
    · by_contra hz0
      exact (hpos z hz hz0).ne' hz'
    · rw [Set.mem_singleton_iff.mp hz]
      exact ⟨(closedConeOfCurves sX).zero_mem, map_zero _⟩

/-- `K + Δ` is not nef if it is negative on a nonzero face `F`. -/
theorem not_isNef_of_isNegativeExtremalFace (hklt : IsKltPair sX n K Δ) (hΔ : Δ.IsEffective)
    (hF : IsNegativeExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
      (MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2) F)
    (hF0 : F ≠ {0}) : ¬ QDivisor.IsNef k sX (Divisor.toQDivisor K + Δ) := by
  rintro ⟨_, hC⟩
  obtain ⟨C, hCF⟩ := exists_properCurve_numericalClass_mem_of_isNegativeExtremalFace hklt hΔ hF hF0
  have hlt := hF.2.2 _ hCF (numericalClass_cycle_ne_zero C)
  rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle] at hlt
  exact absurd hlt (not_lt.2 (by exact_mod_cast hC C.scheme C.ι C.dim_eq))

/-- If `F ≠ {0}` and the form of `E` vanishes on `F`, `E + m • D` supports `F` for some
`m > 0`. -/
theorem exists_isSupportingDivisor_add_nsmul_of_ne_zero (hklt : IsKltPair sX n K Δ)
    (hΔ : Δ.IsEffective)
    (hF : IsNegativeExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
      (MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2) F)
    {D E : X.CartierDivisor} (hD : IsSupportingDivisor k sX F D)
    (hEF : ∀ z ∈ F, cartierForm sX E z = 0) (hF0 : F ≠ {0}) :
    ∃ m : ℕ, 0 < m ∧ IsSupportingDivisor k sX F (E + m • D) := by
  rw [isSupportingDivisor_iff] at hD
  obtain ⟨-, hSA, hSopen, hScone⟩ := supportingForms_nonempty_isOpen_of_isNegativeExtremalFace
    hklt hΔ (not_isNef_of_isNegativeExtremalFace hklt hΔ hF hF0) hF
  have hDA : cartierForm sX D ∈ (Submodule.span ℝ F).dualAnnihilator := hSA ⟨hD.1, hD.2⟩
  have hEA : cartierForm sX E ∈ (Submodule.span ℝ F).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro w hw
    exact Submodule.span_le.2 (fun z hz => LinearMap.mem_ker.2 (hEF z hz)) hw
  letI : TopologicalSpace (Submodule.span ℝ F).dualAnnihilator :=
    moduleTopology ℝ (Submodule.span ℝ F).dualAnnihilator
  haveI : IsModuleTopology ℝ (Submodule.span ℝ F).dualAnnihilator := ⟨rfl⟩
  haveI : ContinuousAdd (Submodule.span ℝ F).dualAnnihilator :=
    ModuleTopology.continuousAdd ℝ _
  haveI : ContinuousSMul ℝ (Submodule.span ℝ F).dualAnnihilator :=
    ModuleTopology.continuousSMul ℝ _
  let γ : ℝ → (Submodule.span ℝ F).dualAnnihilator := fun t =>
    ⟨cartierForm sX D, hDA⟩ + t • ⟨cartierForm sX E, hEA⟩
  have hγ : Continuous γ := continuous_const.add (continuous_id.smul continuous_const)
  have hγv : ∀ t, ((γ t : (Submodule.span ℝ F).dualAnnihilator) :
      Module.Dual ℝ (NumericalCurveClasses sX)) = cartierForm sX D + t • cartierForm sX E :=
    fun t => rfl
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hSopen.preimage hγ) 0 (by
    simpa only [Set.mem_preimage, Set.mem_setOf_eq, hγv, zero_smul, add_zero] using hD)
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  obtain ⟨h1a, h1b⟩ := hball (show 1 / ((m : ℝ) + 1) ∈ Metric.ball (0 : ℝ) ε by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    exact hm)
  have h2 := hScone (cartierForm sX D + (1 / ((m : ℝ) + 1)) • cartierForm sX E) h1a h1b
    ((m : ℝ) + 1) (by positivity)
  have hform : ((m : ℝ) + 1) • (cartierForm sX D + (1 / ((m : ℝ) + 1)) • cartierForm sX E) =
      cartierForm sX E + (m + 1) • cartierForm sX D := by
    refine LinearMap.ext fun z => ?_
    simp only [LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul, nsmul_eq_mul]
    push_cast
    field_simp
    ring
  rw [hform] at h2
  refine ⟨m + 1, m.succ_pos, ?_⟩
  rwa [isSupportingDivisor_iff, map_add, map_nsmul]

end Descent

end MMP.FourfoldProofs.Km3bContractionPullbackLineBundleProof

end

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

open MMP.FourfoldProofs.Km3bContractionPullbackLineBundleProof in
/-- **Line bundles descend to the contraction** (Kollár–Mori 3.7(4)). Let `X` be a projective
variety over an algebraically closed field `k` of characteristic zero, `(X, Δ)` a klt pair with
canonical divisor `K` and `Δ` effective, `F` a `(K + Δ)`-negative extremal face of `NE̅(X)`,
`g : X ⟶ Z` a contraction of `F`, and `L` an invertible sheaf on `X` with `deg_C L = 0` for
every curve `C ⊆ X` with `[C] ∈ F`. Then `L ≅ g^* L_Z` for an invertible sheaf `L_Z` on `Z`. -/
@[mmp "thm_km3b_contraction_pullback_line_bundle"]
public theorem exists_isInvertible_iso_pullback_of_isContractionOfFace {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
    [AlgebraicGeometry.IsProjectiveVariety k sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hklt : IsKltPair sX n K Δ) (hΔ : Δ.IsEffective) {F : Set (NumericalCurveClasses sX)}
    (hF : IsNegativeExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
      (MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2) F)
    {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of k)} {g : X ⟶ Z} (hg : IsContractionOfFace k sX sZ F g)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : ∀ C : ProperCurve sX, OneCycle.numericalClass sX (C.cycle ℝ) ∈ F → C.degree k L = 0) :
    ∃ LZ : Z.Modules, SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 LZ ∧
      Nonempty (L ≅ (Scheme.Modules.pullback g).obj LZ) := by
  obtain ⟨D, hD⟩ := exists_isSupportingDivisor_of_isNegativeExtremalFace hklt hΔ hF
  obtain ⟨E, ⟨eL⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf L
  obtain ⟨m, hm0, hS⟩ : ∃ m : ℕ, 0 < m ∧ IsSupportingDivisor k sX F (E + m • D) := by
    by_cases hF0 : F = {0}
    · exact exists_isSupportingDivisor_add_nsmul_of_eq_zero hD E hF0
    · exact exists_isSupportingDivisor_add_nsmul_of_ne_zero hklt hΔ hF hD
        (cartierForm_eq_zero_of_mem_face hklt hΔ hF eL hL) hF0
  obtain ⟨DZ, hDZ, hDlin⟩ := exists_linearlyEquivalent_pullback_of_isSupportingDivisor hklt hΔ hF
    (isSupportingDivisor_nsmul hm0 hD) hg
  obtain ⟨MZ, hMZ, hMlin⟩ :=
    exists_linearlyEquivalent_pullback_of_isSupportingDivisor hklt hΔ hF hS hg
  have hNZ : ¬ Set.range g ⊆ MMP.Intersection.cartierSupport (MZ - DZ) := by
    rw [← MMP.CartierDivisor.genericPoint_notMem_cartierSupport_iff] at hMZ hDZ ⊢
    exact notMem_support_sub hMZ hDZ
  have hlin : MMP.Intersection.LinearlyEquivalent
      (MMP.CartierDivisor.pullback g (MZ - DZ) hNZ) E := by
    rw [MMP.CartierDivisor.pullback_sub g MZ DZ hNZ hMZ hDZ]
    unfold MMP.Intersection.LinearlyEquivalent
    convert (MMP.Intersection.principalSubgroup X).sub_mem hMlin hDlin using 1
    abel
  obtain ⟨φ⟩ := (MMP.CartierDivisor.nonempty_sheaf_iso_iff _ _).2 hlin
  exact ⟨MMP.CartierDivisor.sheaf (MZ - DZ), MMP.CartierDivisor.isInvertible_sheaf (MZ - DZ),
    ⟨eL ≪≫ φ.symm ≪≫ MMP.CartierDivisor.pullbackSheafIso g _ hNZ⟩⟩

end MMP.Mori

end
