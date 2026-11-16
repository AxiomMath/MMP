module

public import MMP.AlgebraicGeometry.MMP.ConeTheorem.NegativeFacePolyhedral
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.NegativeFaceSupportingForms
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.AmpleStrictlyPositive

@[expose] public section

section

/-!
# Negative extremal faces of the cone of curves have supporting divisors

Let `X` be a projective variety over an algebraically closed field `k` of characteristic zero
and `(X, Δ)` a klt pair with `Δ` effective. Every `(K_X + Δ)`-negative extremal face `F` of
`NE̅(X)` has a supporting divisor: a nef Cartier divisor `D` with
`{z ∈ NE̅(X) | (D · z) = 0} = F`.

If `K_X + Δ` is nef, then `F = {0}` and any ample Cartier divisor supports it. Otherwise the
forms `λ ≥ 0` on `NE̅(X)` with zero set `F` form a nonempty open cone in `⟨F⟩^⊥`. Since `F` is
spanned by classes `ξ₁, …, ξ_m` of the lattice `N₁(X)_ℤ`, the space `⟨F⟩^⊥` is cut out by
equations with integral coefficients in a basis of `N₁(X)_ℤ`, so its rational points are dense
and one of them lies in the cone. A positive multiple of it is integral on `N₁(X)_ℤ`, hence lies
in `Num(X)`, hence is `(D · _)` for a Cartier divisor `D`.

## Main results

* `MMP.Mori.exists_isSupportingDivisor_of_isNegativeExtremalFace`: the statement above.

## Implementation notes

"Supporting divisor" is `MMP.Mori.IsSupportingDivisor`. The form `z ↦ ((K_X + Δ) · z)` is
`MMP.Fourfold.QDivisor.curveForm` of `K_X + Δ`, which is `ℚ`-Cartier by the pair condition, and
a `(K_X + Δ)`-negative extremal face is `MMP.Mori.IsNegativeExtremalFace` for that form.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.3 Step 6
-/

open CategoryTheory AlgebraicGeometry Module MMP.Mori

namespace MMP.FourfoldProofs.Km3bNegativeFaceSupportingDivisorProof

/-- **Rational points of a subspace cut out by integral equations.** Let `β` be a basis of a real
vector space `V` and `A` the space of linear forms `μ` with `∑ᵢ nⱼᵢ μ(βᵢ) = 0` for an integer
matrix `n`. Every nonempty open subset of `A` contains a form taking rational values on `β`. -/
private theorem exists_mem_rat_of_isOpen {V : Type*} [AddCommGroup V] [Module ℝ V]
    {ι : Type*} [Fintype ι] (β : Basis ι ℝ V) {m : ℕ} (n : Fin m → ι → ℤ)
    (A : Submodule ℝ (Dual ℝ V))
    (hA : ∀ μ : Dual ℝ V, μ ∈ A ↔ ∀ j, ∑ i, (n j i : ℝ) * μ (β i) = 0)
    {U : Set A} (hU : @IsOpen _ (moduleTopology ℝ A) U) (hne : U.Nonempty) :
    ∃ μ ∈ U, ∀ i, ∃ q : ℚ, (μ : Dual ℝ V) (β i) = q := by
  classical
  let S : Submodule ℚ (ι → ℚ) := Submodule.span ℚ (Set.range fun j i => (n j i : ℚ))
  let γ := Module.Free.chooseBasis ℚ ((ι → ℚ) ⧸ S)
  let r : ι → Module.Free.ChooseBasisIndex ℚ ((ι → ℚ) ⧸ S) → ℚ :=
    fun i k => γ.repr (S.mkQ (Pi.single i 1)) k
  have hr : ∀ j k, ∑ i, (n j i : ℚ) * r i k = 0 := by
    intro j k
    have h0 : S.mkQ (fun i => (n j i : ℚ)) = 0 :=
      (Submodule.Quotient.mk_eq_zero S).2 (Submodule.subset_span ⟨j, rfl⟩)
    have hsum : (fun i => (n j i : ℚ)) = ∑ i, (n j i : ℚ) • Pi.single i 1 := by
      ext i'
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hsum, map_sum] at h0
    simpa [r, map_sum, Finsupp.coe_finset_sum, Finset.sum_apply, mul_comm] using
      congrArg (fun x => γ.repr x k) h0
  let φ : Module.Free.ChooseBasisIndex ℚ ((ι → ℚ) ⧸ S) → Dual ℝ V :=
    fun k => β.constr ℝ (fun i => (r i k : ℝ))
  let Φ := Fintype.linearCombination ℝ φ
  have hΦβ : ∀ c i, Φ c (β i) = ∑ k, c k * r i k := by
    intro c i
    simp [Φ, φ, Fintype.linearCombination_apply, LinearMap.sum_apply, Basis.constr_basis]
  have hΦA : ∀ c, Φ c ∈ A := by
    intro c
    rw [hA]
    intro j
    simp_rw [hΦβ, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun k _ => ?_
    have := congrArg (fun x : ℚ => (x : ℝ) * c k) (hr j k)
    simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast, Rat.cast_zero, zero_mul,
      Finset.sum_mul] at this
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => by ring
  let Φ' := Φ.codRestrict A hΦA
  letI : TopologicalSpace A := moduleTopology ℝ A
  haveI : IsModuleTopology ℝ A := ⟨rfl⟩
  haveI : ContinuousAdd A := ModuleTopology.continuousAdd ℝ A
  haveI : ContinuousSMul ℝ A := ModuleTopology.continuousSMul ℝ A
  have hcont : Continuous Φ' := IsModuleTopology.continuous_of_linearMap Φ'
  obtain ⟨μ0, hμ0⟩ := hne
  let L : (ι → ℚ) →ₗ[ℚ] ℝ := Fintype.linearCombination ℚ fun i => (μ0 : Dual ℝ V) (β i)
  have hL : S ≤ LinearMap.ker L := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, L, Fintype.linearCombination_apply,
      Rat.smul_def, Rat.cast_intCast]
    exact (hA μ0).1 μ0.2 j
  let ψ := S.liftQ L hL
  have hc : Φ' (fun k => ψ (γ k)) = μ0 := by
    apply Subtype.ext
    refine β.ext fun i => ?_
    change Φ _ (β i) = _
    rw [hΦβ]
    have h1 : ∑ k, r i k • γ k = S.mkQ (Pi.single i 1) := γ.sum_repr _
    have h2 := congrArg ψ h1
    rw [map_sum] at h2
    simp only [map_smul, Rat.smul_def] at h2
    rw [show ψ (S.mkQ (Pi.single i 1)) = L (Pi.single i 1) from rfl] at h2
    simp only [L, Fintype.linearCombination_apply, Pi.single_apply, ite_smul, one_smul,
      zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
    rw [← h2]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  obtain ⟨q, hq⟩ := (DenseRange.piMap fun _ => (Rat.denseRange_cast (𝕜 := ℝ))).exists_mem_open
    (hU.preimage hcont) ⟨_, show Φ' _ ∈ U from hc ▸ hμ0⟩
  refine ⟨Φ' (Pi.map (fun _ => Rat.cast) q), hq, fun i => ⟨∑ k, q k * r i k, ?_⟩⟩
  change Φ _ (β i) = _
  rw [hΦβ]
  push_cast
  rfl

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

/-- On an integral scheme every element of `Num(X)` is the form `z ↦ (D · z)` of a single
Cartier divisor `D`. -/
private theorem exists_eq_of_mem_numericalDivisorGroup [IsIntegral X]
    {φ : Module.Dual ℝ (NumericalCurveClasses sX)} (hφ : φ ∈ numericalDivisorGroup sX) :
    ∃ D : X.CartierDivisor,
      NumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ D) = φ := by
  have : numericalDivisorGroup sX ≤ (cartierForm sX).range := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨L, hL, rfl⟩
    obtain ⟨E, ⟨e⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf L
    refine ⟨E, ?_⟩
    change NumericalCurveClasses.intersectionNumber _ = _
    rw [NumericalCurveClasses.intersectionNumber_ofCartier]
    refine LinearMap.ext fun z => ?_
    obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX z
    rw [NumericalCurveClasses.degree_numericalClass, NumericalCurveClasses.degree_numericalClass,
      OneCycle.degree_apply, OneCycle.degree_apply]
    refine Finsupp.sum_congr fun C _ => ?_
    unfold ProperCurve.degree
    rw [degreeOn_eq_of_iso k sX C.ι C.dim_le e]
  exact this hφ

/-- A projective variety carries a Cartier divisor whose invertible sheaf is ample. -/
private theorem exists_isAmple_sheaf [h : AlgebraicGeometry.IsProjectiveVariety k sX] :
    ∃ D : X.CartierDivisor, Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf D) := by
  obtain ⟨⟨L, hL, hrel, hA⟩, -⟩ :=
    MMP.Foundations.IsProjective.exists_isRelativelyAmple h.isProjective.isProjective
  obtain ⟨A, ⟨e⟩⟩ := hA h.toIsIntegral
  exact ⟨A, (Stacks.RelativeVeryAmple.isAmple_congr _ _ e).mpr
    (Stacks.HProjective.isAmple_of_isRelativelyAmple_of_isAffine sX L hrel)⟩

/-- The curve form of a nef `ℚ`-Cartier `ℚ`-divisor is nonnegative on `NE̅(X)`. -/
private theorem curveForm_nonneg_of_isNef [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [QuasiCompact sX] {D : QDivisor X} (hD : D.IsNef k sX) (h : D.IsQCartier) :
    ∀ z ∈ closedConeOfCurves sX, 0 ≤ MMP.Fourfold.QDivisor.curveForm sX D h z := by
  have hcont : Continuous (MMP.Fourfold.QDivisor.curveForm sX D h) := by
    unfold MMP.Fourfold.QDivisor.curveForm Finsupp.sum
    rw [LinearMap.coe_sum, Finset.sum_fn]
    refine continuous_finset_sum _ fun E _ => ?_
    haveI := (Divisor.mem_cartierSubgroup.mp E.2).isInvertibleModule_divisorialSheaf
    exact (NumericalCurveClasses.continuous_degree sX _).const_smul _
  intro z hz
  replace hz : z ∈ closure (coneOfCurves sX : Set (NumericalCurveClasses sX)) := hz
  refine closure_minimal (s := (coneOfCurves sX : Set (NumericalCurveClasses sX)))
    (t := ((PointedCone.positive ℝ ℝ).comap (MMP.Fourfold.QDivisor.curveForm sX D h) :
      Set (NumericalCurveClasses sX))) (Submodule.span_le.2 ?_)
    (isClosed_Ici.preimage hcont) hz
  rintro _ ⟨C, rfl⟩
  obtain ⟨_, hC⟩ := hD
  change 0 ≤ MMP.Fourfold.QDivisor.curveForm sX D h _
  rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle]
  exact_mod_cast hC C.scheme C.ι C.dim_eq

/-- Clearing denominators: a positive integer multiple of finitely many rationals is integral. -/
private theorem exists_pos_nat_mul_eq_int {ι : Type*} [Fintype ι] (q : ι → ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∀ i, ∃ c : ℤ, (N : ℚ) * q i = c := by
  refine ⟨∏ i, (q i).den, Finset.prod_pos fun i _ => (q i).den_pos, fun i => ?_⟩
  obtain ⟨c, hc⟩ : (q i).den ∣ ∏ i, (q i).den := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  refine ⟨c * (q i).num, ?_⟩
  rw [hc]
  push_cast
  rw [← Rat.den_mul_eq_num (q i)]
  ring

/-- A form vanishes on the span of the hull of `ξ₁, …, ξ_m` iff it vanishes on every `ξⱼ`. -/
private theorem mem_dualAnnihilator_span_iff {V : Type*} [AddCommGroup V] [Module ℝ V]
    {F : Set V} {m : ℕ} {ξ : Fin m → V} (hFξ : F = PointedCone.hull ℝ (Set.range ξ))
    (μ : Module.Dual ℝ V) :
    μ ∈ (Submodule.span ℝ F).dualAnnihilator ↔ ∀ j, μ (ξ j) = 0 := by
  rw [Submodule.mem_dualAnnihilator]
  refine ⟨fun h j => h _ (Submodule.subset_span ?_), fun h w hw => ?_⟩
  · rw [hFξ]
    exact PointedCone.subset_hull ⟨j, rfl⟩
  · have hF' : F ⊆ (LinearMap.ker μ : Set V) := by
      rw [hFξ]
      have : PointedCone.hull ℝ (Set.range ξ) ≤ (LinearMap.ker μ).restrictScalars _ :=
        Submodule.span_le.2 (Set.range_subset_iff.2 h)
      exact this
    exact Submodule.span_le.2 hF' hw

/-- A Cartier divisor whose form is nonnegative on `NE̅(X)` with zero set `F` supports `F`. -/
private theorem isSupportingDivisor_of_nonneg [QuasiCompact sX] [Mori.IsProperVariety k sX]
    {F : Set (NumericalCurveClasses sX)} {D : X.CartierDivisor}
    (h0 : ∀ z ∈ closedConeOfCurves sX,
      0 ≤ NumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ D) z)
    (hF : {z | z ∈ closedConeOfCurves sX ∧
      NumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ D) z = 0} = F) :
    IsSupportingDivisor k sX F D :=
  ⟨(KCartierDivisor.isNef_iff_closedConeOfCurves_subset_nonnegHalfspace sX _).2 fun z hz =>
    (KCartierDivisor.mem_nonnegHalfspace_iff sX _ z).2 (h0 z hz), hF⟩

/-- If `K + Δ` is nef, a `(K + Δ)`-negative extremal face is `{0}`, supported by any ample
divisor. -/
private theorem exists_isSupportingDivisor_of_isNef [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [QuasiCompact sX] [AlgebraicGeometry.IsProjectiveVariety k sX]
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} (hklt : IsKltPair sX n K Δ)
    {F : Set (NumericalCurveClasses sX)}
    (hF : IsNegativeExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
      (MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2) F)
    (hnef : QDivisor.IsNef k sX (Divisor.toQDivisor K + Δ)) :
    ∃ D : X.CartierDivisor, IsSupportingDivisor k sX F D := by
  have hF0 : F = {0} := by
    ext z
    refine ⟨fun hz => ?_, fun hz => (Set.mem_singleton_iff.mp hz) ▸ hF.1.2.1.1⟩
    by_contra h0
    exact (hF.2.2 z hz h0).not_ge (curveForm_nonneg_of_isNef hnef hklt.1.2.2 z (hF.1.1 hz))
  obtain ⟨D, hD⟩ := exists_isAmple_sheaf (sX := sX)
  have hpos := closedConeOfCurves_diff_zero_subset_posHalfspace sX D hD
  have hpos' : ∀ z ∈ closedConeOfCurves sX, z ≠ 0 →
      0 < NumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ D) z := by
    intro z hz hz0
    obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX z
    exact hpos ⟨hz, hz0⟩ Z rfl
  refine ⟨D, isSupportingDivisor_of_nonneg (fun z hz => ?_) ?_⟩
  · rcases eq_or_ne z 0 with rfl | hz0
    · rw [map_zero]
    · exact (hpos' z hz hz0).le
  · rw [hF0]
    ext z
    refine ⟨fun ⟨hz, hz'⟩ => ?_, fun hz => ?_⟩
    · by_contra hz0
      exact (hpos' z hz hz0).ne' hz'
    · rw [Set.mem_singleton_iff.mp hz]
      exact ⟨(closedConeOfCurves sX).zero_mem, map_zero _⟩

/-- If `K + Δ` is not nef, a rational point of the open cone of supporting forms, scaled to be
integral, is the form of a supporting Cartier divisor. -/
private theorem exists_isSupportingDivisor_of_not_isNef [IsAlgClosed k] [CharZero k]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [QuasiCompact sX]
    [AlgebraicGeometry.IsProjectiveVariety k sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hklt : IsKltPair sX n K Δ) (hΔ : Δ.IsEffective) {F : Set (NumericalCurveClasses sX)}
    (hF : IsNegativeExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
      (MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2) F)
    (hnef : ¬ QDivisor.IsNef k sX (Divisor.toQDivisor K + Δ)) :
    ∃ D : X.CartierDivisor, IsSupportingDivisor k sX F D := by
  obtain ⟨⟨l₀, hl₀⟩, hSA, hSopen, hScone⟩ :=
    supportingForms_nonempty_isOpen_of_isNegativeExtremalFace hklt hΔ hnef hF
  obtain ⟨m, ξ, hFξ, -⟩ := exists_eq_hull_of_isNegativeExtremalFace hklt hΔ hF
  obtain ⟨a, ha, hCart⟩ := hklt.1.2.2.exists_pos
  obtain ⟨hfree, hfin, hbij, -, -⟩ :=
    exists_coneDatum_numericalCurveLattice_of_isKltPair hklt hΔ hnef
      (a := (a : ℤ)) (by exact_mod_cast ha) hCart
  let e := numericalDivisorGroupEquivDual sX
  classical
  let b := Module.Free.chooseBasis ℤ (numericalCurveLattice sX)
  let T := LinearMap.liftBaseChange ℝ (numericalCurveLattice sX).subtype.toIntLinearMap
  let β := (Algebra.TensorProduct.basis ℝ b).map (LinearEquiv.ofBijective T hbij)
  have hβ : ∀ i, β i = (b i : NumericalCurveClasses sX) := by
    intro i
    simp [β, T, Algebra.TensorProduct.basis_apply]
  let nn : Fin m → Module.Free.ChooseBasisIndex ℤ (numericalCurveLattice sX) → ℤ :=
    fun j i => b.repr (ξ j) i
  have hξ : ∀ j, (ξ j : NumericalCurveClasses sX) = ∑ i, (nn j i : ℝ) • β i := by
    intro j
    conv_lhs => rw [← b.sum_repr (ξ j)]
    rw [AddSubgroup.val_finset_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hβ, Int.cast_smul_eq_zsmul]
    rfl
  have hA : ∀ μ : Module.Dual ℝ (NumericalCurveClasses sX),
      μ ∈ (Submodule.span ℝ F).dualAnnihilator ↔ ∀ j, ∑ i, (nn j i : ℝ) * μ (β i) = 0 := by
    intro μ
    have hμξ : ∀ j, ∑ i, (nn j i : ℝ) * μ (β i) = μ (ξ j) := by
      intro j
      rw [hξ, map_sum]
      simp [smul_eq_mul]
    simp_rw [hμξ]
    exact mem_dualAnnihilator_span_iff hFξ μ
  obtain ⟨μ, hμU, hμq⟩ := exists_mem_rat_of_isOpen β nn _ hA hSopen ⟨⟨l₀, hSA hl₀⟩, hl₀⟩
  choose q hq using hμq
  obtain ⟨N, hN, hNq⟩ := exists_pos_nat_mul_eq_int q
  set ν : Module.Dual ℝ (NumericalCurveClasses sX) := (N : ℝ) • (μ : Module.Dual ℝ _) with hν
  have hνS := hScone _ hμU.1 hμU.2 (N : ℝ) (by exact_mod_cast hN)
  have hνint : ∀ i, ∃ z : ℤ, ν (β i) = z := fun i => (hNq i).imp fun c hc => by
    rw [hν, LinearMap.smul_apply, hq i, smul_eq_mul]
    exact_mod_cast hc
  choose z hz using hνint
  let θ : Module.Dual ℤ (numericalCurveLattice sX) := b.constr ℤ z
  have hφν : ((e.symm θ : numericalDivisorGroup sX) : Module.Dual ℝ _) = ν := by
    refine β.ext fun i => ?_
    rw [hz i, hβ, ← intCast_numericalDivisorGroupEquivDual_apply sX, e.apply_symm_apply]
    simp [θ, Basis.constr_basis]
  obtain ⟨D, hD⟩ := exists_eq_of_mem_numericalDivisorGroup (hφν ▸ (e.symm θ).2)
  exact ⟨D, isSupportingDivisor_of_nonneg (by rw [hD]; exact hνS.1) (by rw [hD]; exact hνS.2)⟩

end MMP.FourfoldProofs.Km3bNegativeFaceSupportingDivisorProof

end

section

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

/-- **Negative extremal faces have supporting divisors** (Kollár–Mori 3.3, Step 6). Let `X` be a
projective variety over an algebraically closed field `k` of characteristic zero, `(X, Δ)` a
klt pair with canonical divisor `K` and `Δ` effective, and `F` a `(K + Δ)`-negative extremal face
of `NE̅(X)`. Then there is a nef Cartier divisor `D` on `X` with
`{z ∈ NE̅(X) | (D · z) = 0} = F`. -/
@[mmp "lem_km3b_negative_face_supporting_divisor"]
public theorem exists_isSupportingDivisor_of_isNegativeExtremalFace {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
    [AlgebraicGeometry.IsProjectiveVariety k sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hklt : IsKltPair sX n K Δ) (hΔ : Δ.IsEffective) {F : Set (NumericalCurveClasses sX)}
    (hF : IsNegativeExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
      (MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2) F) :
    ∃ D : X.CartierDivisor, IsSupportingDivisor k sX F D := by
  by_cases hnef : QDivisor.IsNef k sX (Divisor.toQDivisor K + Δ)
  · exact FourfoldProofs.Km3bNegativeFaceSupportingDivisorProof.exists_isSupportingDivisor_of_isNef
      hklt hF hnef
  · exact FourfoldProofs.Km3bNegativeFaceSupportingDivisorProof.exists_isSupportingDivisor_of_not_isNef
      hklt hΔ hF hnef

end MMP.Mori

end
