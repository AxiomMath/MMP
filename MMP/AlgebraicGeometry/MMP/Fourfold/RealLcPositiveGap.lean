module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancy
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.MMP.Fourfold.ConeTheorem.LcRelativeCone
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
public import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive

/-!
# A uniform rational curve and a positive gap on a fixed real lc fourfold

Let `f : X ⟶ Z` be a morphism of projective complex varieties, with `X` a normal `ℚ`-factorial
fourfold with canonical divisor `K_X`. Let `P` be the convex hull of finitely many effective
`ℚ`-divisors `V₁, …, V_k` with every `(X, Vᵢ)` log canonical, and let `B ∈ P` be written as
`B = ∑ⱼ rⱼ Bⱼ` with real weights `rⱼ > 0`, `∑ rⱼ = 1`, and rational points `Bⱼ ∈ P` with every
`(X, Bⱼ)` log canonical. There is a `τ > 0` such that every extremal ray `R` of the relative
closed cone of curves `NE̅(X/Z)` on which `K_X + B'` is negative for some `B' ∈ P` is spanned by
the class of a rational curve `L` contracted by `f` with `(K_X + B') · L ≥ -8` for every
`B' ∈ P`, and with `(K_X + B) · L ≥ τ` as soon as `(K_X + B) · L > 0`.

The curve is a rational curve in `R` of least positive degree with respect to a fixed ample
divisor; comparing it with the curves of length at most `8 = 2 dim X` that the lc cone theorem
provides for the negative vertices gives the lower bound on the vertices, hence on `P` by
convexity. Clearing the Cartier indices of the `K_X + Bⱼ` by one integer `m`, the numbers
`m (K_X + Bⱼ) · L` are integers bounded below by `-8m`, so the positive values of
`m (K_X + B) · L` in `(0, m]` form a finite set, and `τ` is its minimum divided by `m`.

## Main results

* `MMP.Fourfold.exists_pos_forall_isExtremalRay_exists_isRationalCurve_neg_eight_le`.

## Implementation notes

The vertices of `P` and the decomposition of `B` are indexed by arbitrary finite types. The
points `Bⱼ` are only required to be rational points of `P`; any such points are vertices of the
rational polytope they span, which lies in `P`. An `ℝ`-Cartier divisor `K_X + B'` is paired with
a class `z ∈ N₁(X/Z)` through a presentation `K_X + B' = ∑ cᵢ Mᵢ` by Cartier divisors `Mᵢ`
(`MMP.Fourfold.RDivisor.IsRCartier`), as `∑ cᵢ (z · 𝒪_X(Mᵢ))` computed with
`MMP.Mori.RelativeNumericalCurveClasses.degree`. The pairing does not depend on the
presentation, so negativity on `R` asks for one presentation and the bounds are asserted for
all of them. The dimension of `X` is the `4` of `MMP.Mori.Divisor.IsCanonicalDivisor`. A curve
is an `MMP.Mori.ProperCurve` contracted by `f`, rational when its reduced closed subscheme is
(`MMP.Mori.IsRationalCurve`), with class `MMP.Mori.ProperCurve.relativeClass`; a nonzero class
in the ray `R` spans it.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Theorem 3.7
-/

@[expose] public section

section

open AlgebraicGeometry CategoryTheory TopologicalSpace MMP.Mori MMP.Fourfold
open scoped TensorProduct

namespace Proof_lem_fourfold_real_lc_fixed_model_positive_gap

section Pairing

variable {X Z : Scheme.{0}} [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX] (f : X ⟶ Z)

/-- The degree of `𝒪_X(M + N)` on a relative class is the sum of the degrees. -/
private theorem degree_divisorialSheaf_add (M N : Divisor X) (hM : M.IsCartier)
    (hN : N.IsCartier) (z : RelativeNumericalCurveClasses sX f) :
    (haveI := (hM.add hN).isInvertibleModule_divisorialSheaf;
        RelativeNumericalCurveClasses.degree sX f (M + N).divisorialSheaf z) =
      (haveI := hM.isInvertibleModule_divisorialSheaf;
        RelativeNumericalCurveClasses.degree sX f M.divisorialSheaf z) +
      (haveI := hN.isInvertibleModule_divisorialSheaf;
        RelativeNumericalCurveClasses.degree sX f N.divisorialSheaf z) := by
  obtain ⟨Zc, rfl⟩ := relativeNumericalClass_surjective sX f z
  simp only [RelativeNumericalCurveClasses.degree_relativeNumericalClass, OneCycle.degree_apply]
  rw [← Finsupp.sum_add]
  refine Finsupp.sum_congr fun C _ => ?_
  have h := Divisor.degreeOn_add ℂ sX C.ι C.dim_le M N hM hN
  have e1 : ∀ (D : Divisor X) (hD : D.IsCartier),
      (haveI := hD.isInvertibleModule_divisorialSheaf; C.degree ℂ D.divisorialSheaf) =
        D.degreeOn ℂ sX C.ι C.dim_le hD := fun D hD => rfl
  rw [e1 _ (hM.add hN), e1 _ hM, e1 _ hN, h]
  push_cast
  ring

/-- `M ↦ (z · 𝒪_X(M))` as an additive map on Cartier divisors. -/
private noncomputable def cartierDegree (z : RelativeNumericalCurveClasses sX f) :
    Divisor.cartierSubgroup (X := X) →+ ℝ :=
  AddMonoidHom.mk' (fun M =>
    haveI := (Divisor.mem_cartierSubgroup.mp M.2).isInvertibleModule_divisorialSheaf
    RelativeNumericalCurveClasses.degree sX f (M : Divisor X).divisorialSheaf z)
    fun M N => degree_divisorialSheaf_add f _ _ (Divisor.mem_cartierSubgroup.mp M.2)
      (Divisor.mem_cartierSubgroup.mp N.2) z

/-- The extension `Ca(X) ⊗ ℝ → ℝ` of `cartierDegree`. -/
private noncomputable def tensorDegree (z : RelativeNumericalCurveClasses sX f) :
    Divisor.cartierSubgroup (X := X) ⊗[ℤ] ℝ →+ ℝ :=
  TensorProduct.liftAddHom (AddMonoidHom.mul.comp (cartierDegree f z))
    fun n M r => by simp [mul_assoc, mul_left_comm]

private theorem tensorDegree_tmul (z : RelativeNumericalCurveClasses sX f)
    (M : Divisor.cartierSubgroup (X := X)) (r : ℝ) :
    tensorDegree f z (M ⊗ₜ r) = cartierDegree f z M * r := by
  simp [tensorDegree]

/-- The degree `(z · 𝒪_X(M))` of a Cartier divisor `M` on a relative class `z`. -/
private noncomputable def degreeOf (z : RelativeNumericalCurveClasses sX f) (M : Divisor X)
    (hM : M.IsCartier) : ℝ :=
  haveI := hM.isInvertibleModule_divisorialSheaf
  RelativeNumericalCurveClasses.degree sX f M.divisorialSheaf z

private theorem degreeOf_smul (μ : ℝ) (z : RelativeNumericalCurveClasses sX f) (M : Divisor X)
    (hM : M.IsCartier) : degreeOf f (μ • z) M hM = μ * degreeOf f z M hM := by
  haveI := hM.isInvertibleModule_divisorialSheaf
  simp only [degreeOf, map_smul, smul_eq_mul]

/-- **Independence of the presentation.** Two presentations of the same `ℝ`-divisor by Cartier
divisors give the same degree on every relative class. -/
private theorem sum_mul_degree_eq_of_sum_smul_eq {α β : Type*} [Fintype α] [Fintype β]
    (z : RelativeNumericalCurveClasses sX f) (c : α → ℝ) (M : α → Divisor X)
    (hM : ∀ a, (M a).IsCartier) (c' : β → ℝ) (M' : β → Divisor X) (hM' : ∀ b, (M' b).IsCartier)
    (h : ∑ a, c a • Divisor.toRDivisor (M a) = ∑ b, c' b • Divisor.toRDivisor (M' b)) :
    ∑ a, c a * degreeOf f z (M a) (hM a) = ∑ b, c' b * degreeOf f z (M' b) (hM' b) := by
  have ht : ∑ a, (⟨M a, Divisor.mem_cartierSubgroup.mpr (hM a)⟩ :
      Divisor.cartierSubgroup (X := X)) ⊗ₜ[ℤ] c a =
      ∑ b, (⟨M' b, Divisor.mem_cartierSubgroup.mpr (hM' b)⟩ :
        Divisor.cartierSubgroup (X := X)) ⊗ₜ[ℤ] c' b := by
    apply MMP.Flips.rDivisorTensorMap_cartierSubgroup_injective
    simpa only [map_sum, MMP.Flips.rDivisorTensorMap_tmul, AddSubgroup.coe_subtype] using h
  have := congrArg (tensorDegree f z) ht
  simp only [map_sum, tensorDegree_tmul] at this
  calc _ = ∑ a, cartierDegree f z ⟨M a, Divisor.mem_cartierSubgroup.mpr (hM a)⟩ * c a :=
        Finset.sum_congr rfl fun a _ => mul_comm _ _
    _ = _ := this
    _ = _ := Finset.sum_congr rfl fun b _ => mul_comm _ _

/-- The degree of `𝒪_X(M)` on the class of a contracted curve is an integer. -/
private theorem degree_relativeClass (L : ProperCurve sX) (hL : L.IsContractedBy f)
    (M : Divisor X) (hM : M.IsCartier) :
    (haveI := hM.isInvertibleModule_divisorialSheaf;
        RelativeNumericalCurveClasses.degree sX f M.divisorialSheaf (L.relativeClass f hL)) =
      (M.degreeOn ℂ sX L.ι L.dim_le hM : ℝ) := by
  haveI := hM.isInvertibleModule_divisorialSheaf
  rw [ProperCurve.relativeClass, RelativeNumericalCurveClasses.degree_relativeNumericalClass]
  exact OneCycle.degree_cycle ℝ _ L

/-- The form `relativeCurveForm` of a `ℚ`-Cartier `ℚ`-divisor `D` is `1 / m_D` times the degree
of `𝒪_X(m_D D)`. -/
private theorem relativeCurveForm_apply (D : QDivisor X) (hD : D.IsQCartier)
    (z : RelativeNumericalCurveClasses sX f) :
    QDivisor.relativeCurveForm sX f D hD z =
      (1 / (D.cartierIndex hD : ℝ)) * cartierDegree f z (D.cartierIndexSMul hD) := by
  rw [QDivisor.relativeCurveForm, QDivisor.associatedCartier, CartierDivisorWithCoeffs.ofCartier,
    Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.sum_single_index]
  · rw [LinearMap.smul_apply, smul_eq_mul]
    push_cast
    rfl
  · simp

end Pairing

/-- `D₀ + ∑ wₐ Dₐ = ∑ wₐ (D₀ + Dₐ)` when `∑ wₐ = 1`. -/
private theorem add_sum_smul_eq {E : Type*} [AddCommGroup E] [Module ℝ E] {α : Type*}
    [Fintype α] (w : α → ℝ) (hw : ∑ a, w a = 1) (D₀ : E) (D : α → E) :
    D₀ + ∑ a, w a • D a = ∑ a, w a • (D₀ + D a) := by
  simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hw, one_smul]

/-- `D = (1 / m_D) • (m_D D)` as `ℝ`-divisors. -/
private theorem toRDivisor_eq_smul_cartierIndexSMul {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] (D : QDivisor X) (hD : D.IsQCartier) :
    QDivisor.toRDivisor D =
      (1 / (D.cartierIndex hD : ℝ)) • Divisor.toRDivisor (D.cartierIndexSMul hD : Divisor X) := by
  have hm : (D.cartierIndex hD : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (QDivisor.cartierIndex_pos hD).ne'
  rw [← QDivisor.toRDivisor_toQDivisor, QDivisor.toQDivisor_cartierIndexSMul, map_zsmul,
    ← Int.cast_smul_eq_zsmul ℝ, smul_smul]
  push_cast
  rw [one_div_mul_cancel hm, one_smul]

/-- **The arithmetic gap.** For positive weights `r j` and positive integers `m j`, the positive
values of `∑ r j * x j` over the tuples with `x j ≥ b` and `m j * x j ∈ ℤ` are bounded below by a
positive constant. -/
private theorem exists_pos_le_sum_mul {κ : Type*} [Fintype κ] (r : κ → ℝ) (hr : ∀ j, 0 < r j)
    (m : κ → ℕ) (hm : ∀ j, 0 < m j) (b : ℝ) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ x : κ → ℝ, (∀ j, b ≤ x j) → (∀ j, ∃ n : ℤ, (m j : ℝ) * x j = n) →
      0 < ∑ j, r j * x j → τ ≤ ∑ j, r j * x j := by
  classical
  set A : ℝ := 1 + |b| * ∑ k, r k
  have hbound : ∀ x : κ → ℝ, (∀ j, b ≤ x j) → ∑ j, r j * x j < 1 → ∀ j, x j ≤ A / r j := by
    intro x hb hs j
    rw [le_div_iff₀ (hr j)]
    have hsplit := Finset.add_sum_erase Finset.univ (fun k => r k * x k) (Finset.mem_univ j)
    have h1 := Finset.add_sum_erase Finset.univ (fun k => r k * (-|b|)) (Finset.mem_univ j)
    have h2 : ∑ k ∈ Finset.univ.erase j, r k * (-|b|) ≤ ∑ k ∈ Finset.univ.erase j, r k * x k :=
      Finset.sum_le_sum fun k _ =>
        mul_le_mul_of_nonneg_left ((neg_abs_le b).trans (hb k)) (hr k).le
    have h3 : ∑ k, r k * (-|b|) = -(|b| * ∑ k, r k) := by rw [← Finset.sum_mul]; ring
    have h4 : r j * (-|b|) ≤ 0 := by nlinarith [abs_nonneg b, hr j]
    linarith
  let F : κ → Set ℝ := fun j => {y | b ≤ y ∧ y ≤ A / r j ∧ ∃ n : ℤ, (m j : ℝ) * y = n}
  have hF : ∀ j, (F j).Finite := by
    intro j
    have hmj : (0 : ℝ) < m j := by exact_mod_cast hm j
    refine ((Set.finite_Icc (⌊b * m j⌋) (⌈A / r j * m j⌉)).image
      (fun n : ℤ => (n : ℝ) / m j)).subset ?_
    rintro y ⟨hby, hyA, n, hn⟩
    refine ⟨n, ⟨?_, ?_⟩, ?_⟩
    · have : b * m j ≤ (n : ℝ) := by rw [← hn]; nlinarith
      exact (Int.floor_mono this).trans (Int.floor_intCast n).le
    · have : (n : ℝ) ≤ A / r j * m j := by rw [← hn]; nlinarith
      exact (Int.ceil_intCast n).symm.le.trans (Int.ceil_mono this)
    · simp only
      rw [← hn]
      field_simp
  have hT : (Set.univ.pi F).Finite := Set.Finite.pi hF
  let S : Set ℝ := ((fun x : κ → ℝ => ∑ j, r j * x j) '' Set.univ.pi F) ∩ Set.Ioi 0
  have hS : S.Finite := (hT.image _).inter_of_left _
  have hmem : ∀ x : κ → ℝ, (∀ j, b ≤ x j) → (∀ j, ∃ n : ℤ, (m j : ℝ) * x j = n) →
      0 < ∑ j, r j * x j → ∑ j, r j * x j < 1 → ∑ j, r j * x j ∈ S :=
    fun x hb hn hpos h1 =>
      ⟨⟨x, fun j _ => ⟨hb j, hbound x hb h1 j, hn j⟩, rfl⟩, hpos⟩
  by_cases hne : S.Nonempty
  · obtain ⟨s0, hs0, hmin⟩ := Set.exists_min_image S id hS hne
    refine ⟨min 1 s0, lt_min one_pos hs0.2, fun x hb hn hpos => ?_⟩
    by_cases h1 : 1 ≤ ∑ j, r j * x j
    · exact (min_le_left _ _).trans h1
    · exact (min_le_right _ _).trans (hmin _ (hmem x hb hn hpos (not_le.mp h1)))
  · refine ⟨1, one_pos, fun x hb hn hpos => ?_⟩
    by_contra h1
    exact hne ⟨_, hmem x hb hn hpos (not_le.mp h1)⟩

/-- **The uniform curve along a ray.** Let `g i` be the values of finitely many forms on a
generator of a ray, some negative, and let each negative form `i` come with a positive multiple
`μ i` of the generator on which it is at least `b ≤ 0`. Then the least multiple `μ i₀` makes
every form at least `b`. -/
private theorem exists_forall_le_mul_of_min {ι : Type*} [Fintype ι] (g : ι → ℝ)
    (hg : ∃ i, g i < 0) (μ : ∀ i, g i < 0 → ℝ) (hμ : ∀ i hi, 0 < μ i hi) {b : ℝ} (hb : b ≤ 0)
    (hle : ∀ i hi, b ≤ μ i hi * g i) : ∃ i₀ hi₀, ∀ i, b ≤ μ i₀ hi₀ * g i := by
  classical
  obtain ⟨i₁, hi₁⟩ := hg
  obtain ⟨i₀, hi₀N, hmin⟩ := (Finset.univ.filter fun i => g i < 0).exists_min_image
    (fun i => if h : g i < 0 then μ i h else 0) ⟨i₁, by simp [hi₁]⟩
  have hi₀ : g i₀ < 0 := (Finset.mem_filter.mp hi₀N).2
  refine ⟨i₀, hi₀, fun i => ?_⟩
  by_cases hi : g i < 0
  · have : μ i₀ hi₀ ≤ μ i hi := by simpa [hi, hi₀] using hmin i (by simp [hi])
    nlinarith [hle i hi]
  · nlinarith [hμ i₀ hi₀, not_lt.mp hi]

private theorem solution :
    ∀ {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) {f : X ⟶ Z} (hf : f ≫ sZ = sX)
    (hXq : IsQFactorial sX) {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4)
    {ι : Type*} [Fintype ι] {V : ι → QDivisor X} (hV0 : ∀ i P, 0 ≤ (V i).coeff P)
    (hV : ∀ i, MMP.Intersection.IsLogCanonicalPair sX (V i))
    {B : RDivisor X}
    (hBP : B ∈ convexHull ℝ (Set.range fun i => QDivisor.toRDivisor (V i)))
    {κ : Type*} [Fintype κ] {r : κ → ℝ} (hr : ∀ j, 0 < r j) (hr1 : ∑ j, r j = 1)
    {Bj : κ → QDivisor X}
    (hBjP : ∀ j, QDivisor.toRDivisor (Bj j) ∈
      convexHull ℝ (Set.range fun i => QDivisor.toRDivisor (V i)))
    (hBjlc : ∀ j, MMP.Intersection.IsLogCanonicalPair sX (Bj j))
    (hBeq : B = ∑ j, r j • QDivisor.toRDivisor (Bj j)),
    ∃ τ : ℝ, 0 < τ ∧
      ∀ R : Set (RelativeNumericalCurveClasses sX f),
        IsExtremalRay ℝ
          (relativeClosedConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f)) R →
        (∃ B' ∈ convexHull ℝ (Set.range fun i => QDivisor.toRDivisor (V i)),
          ∃ (n : ℕ) (c : Fin n → ℝ) (M : Fin n → Divisor X) (hM : ∀ i, (M i).IsCartier),
            Divisor.toRDivisor K + B' = ∑ i, c i • Divisor.toRDivisor (M i) ∧
            ∀ u ∈ R, u ≠ 0 →
              ∑ i, c i * (haveI := (hM i).isInvertibleModule_divisorialSheaf
                RelativeNumericalCurveClasses.degree sX f (M i).divisorialSheaf u) < 0) →
        ∃ (L : ProperCurve sX) (hL : L.IsContractedBy f),
          IsRationalCurve sX
            (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({L.point} : Set X))) ∧
          L.relativeClass f hL ∈ R ∧ L.relativeClass f hL ≠ 0 ∧
          (∀ B' ∈ convexHull ℝ (Set.range fun i => QDivisor.toRDivisor (V i)),
            ∀ (n : ℕ) (c : Fin n → ℝ) (M : Fin n → Divisor X) (hM : ∀ i, (M i).IsCartier),
              Divisor.toRDivisor K + B' = ∑ i, c i • Divisor.toRDivisor (M i) →
              -8 ≤ ∑ i, c i * (haveI := (hM i).isInvertibleModule_divisorialSheaf
                RelativeNumericalCurveClasses.degree sX f (M i).divisorialSheaf
                  (L.relativeClass f hL))) ∧
          ∀ (n : ℕ) (c : Fin n → ℝ) (M : Fin n → Divisor X) (hM : ∀ i, (M i).IsCartier),
            Divisor.toRDivisor K + B = ∑ i, c i • Divisor.toRDivisor (M i) →
            0 < ∑ i, c i * (haveI := (hM i).isInvertibleModule_divisorialSheaf
                RelativeNumericalCurveClasses.degree sX f (M i).divisorialSheaf
                  (L.relativeClass f hL)) →
            τ ≤ ∑ i, c i * (haveI := (hM i).isInvertibleModule_divisorialSheaf
                RelativeNumericalCurveClasses.degree sX f (M i).divisorialSheaf
                  (L.relativeClass f hL)) := by
  intro X Z _ _ _ _ sX sZ hX hZ f hf _hXq K hK ι _ V _hV0 hV B _hBP κ _ r hr hr1 Bj hBjP
    hBjlc hBeq
  haveI : QuasiCompact sX := inferInstance
  have hdim : topologicalKrullDim X = 4 := by exact_mod_cast hK.1
  have cone := fun (D : QDivisor X) (hD : MMP.Intersection.IsLogCanonicalPair sX D) =>
    exists_relativeClosedConeOfCurves_eq_add_hull_of_isLogCanonicalPair hX hZ f hf hdim hK hD
  choose hDV hconeV using fun i => cone (V i) (hV i)
  choose hDB _ using fun j => cone (Bj j) (hBjlc j)
  -- the Cartier multiples `m (K + V i)` and `m (K + Bj j)`
  let mV : ι → ℕ := fun i => (Divisor.toQDivisor K + V i).cartierIndex (hDV i)
  let EV : ι → Divisor X := fun i =>
    ((Divisor.toQDivisor K + V i).cartierIndexSMul (hDV i) : Divisor X)
  have hEV : ∀ i, (EV i).IsCartier := fun i =>
    Divisor.mem_cartierSubgroup.mp ((Divisor.toQDivisor K + V i).cartierIndexSMul (hDV i)).2
  have hpresV : ∀ i, Divisor.toRDivisor K + QDivisor.toRDivisor (V i) =
      (1 / (mV i : ℝ)) • Divisor.toRDivisor (EV i) := fun i => by
    rw [← toRDivisor_eq_smul_cartierIndexSMul, map_add, QDivisor.toRDivisor_toQDivisor]
  let mB : κ → ℕ := fun j => (Divisor.toQDivisor K + Bj j).cartierIndex (hDB j)
  have hmB : ∀ j, 0 < mB j := fun j => QDivisor.cartierIndex_pos _
  let EB : κ → Divisor X := fun j =>
    ((Divisor.toQDivisor K + Bj j).cartierIndexSMul (hDB j) : Divisor X)
  have hEB : ∀ j, (EB j).IsCartier := fun j =>
    Divisor.mem_cartierSubgroup.mp ((Divisor.toQDivisor K + Bj j).cartierIndexSMul (hDB j)).2
  have hpresB : ∀ j, Divisor.toRDivisor K + QDivisor.toRDivisor (Bj j) =
      (1 / (mB j : ℝ)) • Divisor.toRDivisor (EB j) := fun j => by
    rw [← toRDivisor_eq_smul_cartierIndexSMul, map_add, QDivisor.toRDivisor_toQDivisor]
  -- the forms `(K + V i) · z`
  let G : ι → RelativeNumericalCurveClasses sX f → ℝ := fun i z =>
    1 / (mV i : ℝ) * degreeOf f z (EV i) (hEV i)
  have hGsmul : ∀ i (μ : ℝ) z, G i (μ • z) = μ * G i z := fun i μ z => by
    simp only [G, degreeOf_smul]; ring
  have hGrel : ∀ i z, QDivisor.relativeCurveForm sX f (Divisor.toQDivisor K + V i) (hDV i) z =
      G i z := fun i z => relativeCurveForm_apply f _ _ z
  -- the pairing with `K + B'` for `B' ∈ P` is a convex combination of the forms `G i`
  have hval : ∀ B' ∈ convexHull ℝ (Set.range fun i => QDivisor.toRDivisor (V i)),
      ∃ (α : Type) (_ : Fintype α) (w : α → ℝ) (g : α → ι), (∀ a, 0 ≤ w a) ∧ ∑ a, w a = 1 ∧
        ∀ (β : Type) [Fintype β] (c : β → ℝ) (M : β → Divisor X) (hM : ∀ b, (M b).IsCartier),
          Divisor.toRDivisor K + B' = ∑ b, c b • Divisor.toRDivisor (M b) →
          ∀ z, ∑ b, c b * degreeOf f z (M b) (hM b) = ∑ a, w a * G (g a) z := by
    intro B' hB'
    obtain ⟨α, _, w, zz, hw0, hw1, hzz, hsum⟩ := mem_convexHull_iff_exists_fintype.mp hB'
    choose g hg using hzz
    refine ⟨α, inferInstance, w, g, hw0, hw1, fun β _ c M hM hpres z => ?_⟩
    have hrepr : Divisor.toRDivisor K + B' =
        ∑ a, (w a / mV (g a)) • Divisor.toRDivisor (EV (g a)) := by
      rw [← hsum, add_sum_smul_eq w hw1]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← hg a, hpresV, smul_smul]
      congr 1
      ring
    rw [sum_mul_degree_eq_of_sum_smul_eq f z c M hM _ _ (fun a => hEV (g a))
      (hpres.symm.trans hrepr)]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [G]
    ring
  obtain ⟨τ, hτ, hgap⟩ := exists_pos_le_sum_mul r hr mB hmB (-8)
  refine ⟨τ, hτ, fun R hR hneg => ?_⟩
  obtain ⟨-, v, hv0, hRv⟩ := id hR
  have hvR : v ∈ R := hRv ▸ ⟨1, zero_le_one, one_smul _ _⟩
  -- a vertex negative on `R`
  obtain ⟨B', hB', n, c, M, hM, hpres, hnegB⟩ := hneg
  obtain ⟨α, _, w, g, hw0, hw1, hpair⟩ := hval B' hB'
  have hsumneg : ∑ a, w a * G (g a) v < 0 := by
    rw [← hpair (Fin n) c M hM hpres v]
    exact hnegB v hvR hv0
  have hex : ∃ i, G i v < 0 := by
    by_contra hcon
    simp only [not_exists, not_lt] at hcon
    exact absurd hsumneg (not_lt.mpr (Finset.sum_nonneg fun a _ => mul_nonneg (hw0 a) (hcon _)))
  -- the cone theorem on each negative vertex
  have hcurve : ∀ i, G i v < 0 → ∃ (C : ProperCurve sX) (hC : C.IsContractedBy f),
      IsRationalCurve sX
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({C.point} : Set X))) ∧
      (∃ μ : ℝ, 0 < μ ∧ C.relativeClass f hC = μ • v) ∧ -8 ≤ G i (C.relativeClass f hC) := by
    intro i hi
    have hnegray : IsNegativeRelativeExtremalRayOf sX f (Divisor.toQDivisor K + V i) R := by
      refine ⟨hDV i, hR, fun u hu hu0 => ?_⟩
      rw [hRv] at hu
      obtain ⟨μ, hμ, rfl⟩ := hu
      have hμ0 : μ ≠ 0 := by rintro rfl; exact hu0 (zero_smul _ _)
      rw [hGrel, hGsmul]
      exact mul_neg_of_pos_of_neg (lt_of_le_of_ne hμ (Ne.symm hμ0)) hi
    obtain ⟨C, hC, hrat, hRC, hpos, hle⟩ := (hconeV i).1 R hnegray
    have hCR : C.relativeClass f hC ∈ R := hRC ▸ ⟨1, zero_le_one, one_smul _ _⟩
    rw [hRv] at hCR
    obtain ⟨μ, hμ, hμv⟩ := hCR
    refine ⟨C, hC, hrat, ⟨μ, lt_of_le_of_ne hμ ?_, hμv.symm⟩, ?_⟩
    · rintro rfl
      rw [zero_smul] at hμv
      rw [← hμv, map_zero, neg_zero] at hpos
      exact lt_irrefl _ hpos
    · rw [← hGrel]
      linarith
  choose C hC hrat hμ hle using hcurve
  choose μ hμpos hμv using hμ
  obtain ⟨i₀, hi₀, hvert⟩ := exists_forall_le_mul_of_min (fun i => G i v) hex μ hμpos
    (b := -8) (by norm_num) fun i hi => by simpa [hμv, hGsmul] using hle i hi
  have hLv : (C i₀ hi₀).relativeClass f (hC i₀ hi₀) = μ i₀ hi₀ • v := hμv i₀ hi₀
  replace hvert : ∀ i, -8 ≤ G i ((C i₀ hi₀).relativeClass f (hC i₀ hi₀)) := fun i => by
    rw [hLv, hGsmul]; exact hvert i
  have hlow : ∀ B' ∈ convexHull ℝ (Set.range fun i => QDivisor.toRDivisor (V i)),
      ∀ (β : Type) [Fintype β] (c : β → ℝ) (M : β → Divisor X) (hM : ∀ b, (M b).IsCartier),
        Divisor.toRDivisor K + B' = ∑ b, c b • Divisor.toRDivisor (M b) →
        -8 ≤ ∑ b, c b * degreeOf f ((C i₀ hi₀).relativeClass f (hC i₀ hi₀)) (M b) (hM b) := by
    intro B' hB' β _ c M hM hpres
    obtain ⟨α, _, w, g, hw0, hw1, hpair⟩ := hval B' hB'
    rw [hpair β c M hM hpres]
    calc (-8 : ℝ) = ∑ a, w a * (-8) := by rw [← Finset.sum_mul, hw1]; ring
      _ ≤ _ := Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hvert (g a)) (hw0 a)
  refine ⟨C i₀ hi₀, hC i₀ hi₀, hrat i₀ hi₀, ?_, ?_,
    fun B' hB' n c M hM hpres => hlow B' hB' (Fin n) c M hM hpres, ?_⟩
  · rw [hLv, hRv]
    exact ⟨_, (hμpos i₀ hi₀).le, rfl⟩
  · rw [hLv]
    exact smul_ne_zero (hμpos i₀ hi₀).ne' hv0
  · intro n c M hM hpres hpos
    set z := (C i₀ hi₀).relativeClass f (hC i₀ hi₀)
    let x : κ → ℝ := fun j => 1 / (mB j : ℝ) * degreeOf f z (EB j) (hEB j)
    have hrepr : Divisor.toRDivisor K + B = ∑ j, (r j / mB j) • Divisor.toRDivisor (EB j) := by
      rw [hBeq, add_sum_smul_eq r hr1]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hpresB, smul_smul]
      congr 1
      ring
    have hx : ∑ i, c i * degreeOf f z (M i) (hM i) = ∑ j, r j * x j := by
      rw [sum_mul_degree_eq_of_sum_smul_eq f z c M hM _ _ hEB (hpres.symm.trans hrepr)]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [x]
      ring
    have hxb : ∀ j, -8 ≤ x j := fun j => by
      have := hlow _ (hBjP j) Unit (fun _ => 1 / (mB j : ℝ)) (fun _ => EB j) (fun _ => hEB j)
        (by simpa using hpresB j)
      simpa [x] using this
    have hxint : ∀ j, ∃ k : ℤ, (mB j : ℝ) * x j = k := fun j => by
      refine ⟨(EB j).degreeOn ℂ sX (C i₀ hi₀).ι (C i₀ hi₀).dim_le (hEB j), ?_⟩
      have hm : (mB j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hmB j).ne'
      simp only [x, degreeOf]
      rw [degree_relativeClass f (C i₀ hi₀) (hC i₀ hi₀) (EB j) (hEB j)]
      field_simp
    have hpos' : 0 < ∑ j, r j * x j := by rw [← hx]; exact hpos
    exact (hgap x hxb hxint hpos').trans_eq hx.symm

end Proof_lem_fourfold_real_lc_fixed_model_positive_gap

end

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace MMP.Fourfold

open MMP.Mori

/-- **A uniform rational curve and positive gap on a fixed real lc fourfold.** Let `f : X ⟶ Z`
be a morphism of projective complex varieties, `X` normal `ℚ`-factorial of dimension four with
canonical divisor `K`. Let `P` be the convex hull of effective `ℚ`-divisors `V i` with every
`(X, V i)` log canonical, and let `B = ∑ⱼ r j • B j` with `r j > 0`, `∑ r j = 1` and `B j` rational
points of `P` with `(X, B j)` log canonical. Then there is `τ > 0` such that every extremal ray
`R` of `NE̅(X/Z)` on which `K + B'` is negative for some `B' ∈ P` contains the nonzero class of
a rational curve `L` contracted by `f` with `-8 ≤ (K + B') · L` for every `B' ∈ P`, and with
`τ ≤ (K + B) · L` whenever `0 < (K + B) · L`; each intersection number is computed from any
presentation of the divisor by Cartier divisors. -/
@[mmp "lem_fourfold_real_lc_fixed_model_positive_gap"]
public theorem exists_pos_forall_isExtremalRay_exists_isRationalCurve_neg_eight_le
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) {f : X ⟶ Z} (hf : f ≫ sZ = sX)
    (hXq : IsQFactorial sX) {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4)
    {ι : Type*} [Fintype ι] {V : ι → QDivisor X} (hV0 : ∀ i P, 0 ≤ (V i).coeff P)
    (hV : ∀ i, MMP.Intersection.IsLogCanonicalPair sX (V i))
    {B : RDivisor X}
    (hBP : B ∈ convexHull ℝ (Set.range fun i => QDivisor.toRDivisor (V i)))
    {κ : Type*} [Fintype κ] {r : κ → ℝ} (hr : ∀ j, 0 < r j) (hr1 : ∑ j, r j = 1)
    {Bj : κ → QDivisor X}
    (hBjP : ∀ j, QDivisor.toRDivisor (Bj j) ∈
      convexHull ℝ (Set.range fun i => QDivisor.toRDivisor (V i)))
    (hBjlc : ∀ j, MMP.Intersection.IsLogCanonicalPair sX (Bj j))
    (hBeq : B = ∑ j, r j • QDivisor.toRDivisor (Bj j)) :
    ∃ τ : ℝ, 0 < τ ∧
      ∀ R : Set (RelativeNumericalCurveClasses sX f),
        IsExtremalRay ℝ
          (relativeClosedConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f)) R →
        (∃ B' ∈ convexHull ℝ (Set.range fun i => QDivisor.toRDivisor (V i)),
          ∃ (n : ℕ) (c : Fin n → ℝ) (M : Fin n → Divisor X) (hM : ∀ i, (M i).IsCartier),
            Divisor.toRDivisor K + B' = ∑ i, c i • Divisor.toRDivisor (M i) ∧
            ∀ u ∈ R, u ≠ 0 →
              ∑ i, c i * (haveI := (hM i).isInvertibleModule_divisorialSheaf
                RelativeNumericalCurveClasses.degree sX f (M i).divisorialSheaf u) < 0) →
        ∃ (L : ProperCurve sX) (hL : L.IsContractedBy f),
          IsRationalCurve sX
            (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({L.point} : Set X))) ∧
          L.relativeClass f hL ∈ R ∧ L.relativeClass f hL ≠ 0 ∧
          (∀ B' ∈ convexHull ℝ (Set.range fun i => QDivisor.toRDivisor (V i)),
            ∀ (n : ℕ) (c : Fin n → ℝ) (M : Fin n → Divisor X) (hM : ∀ i, (M i).IsCartier),
              Divisor.toRDivisor K + B' = ∑ i, c i • Divisor.toRDivisor (M i) →
              -8 ≤ ∑ i, c i * (haveI := (hM i).isInvertibleModule_divisorialSheaf
                RelativeNumericalCurveClasses.degree sX f (M i).divisorialSheaf
                  (L.relativeClass f hL))) ∧
          ∀ (n : ℕ) (c : Fin n → ℝ) (M : Fin n → Divisor X) (hM : ∀ i, (M i).IsCartier),
            Divisor.toRDivisor K + B = ∑ i, c i • Divisor.toRDivisor (M i) →
            0 < ∑ i, c i * (haveI := (hM i).isInvertibleModule_divisorialSheaf
                RelativeNumericalCurveClasses.degree sX f (M i).divisorialSheaf
                  (L.relativeClass f hL)) →
            τ ≤ ∑ i, c i * (haveI := (hM i).isInvertibleModule_divisorialSheaf
                RelativeNumericalCurveClasses.degree sX f (M i).divisorialSheaf
                  (L.relativeClass f hL)) :=
                    by revert X Z sX sZ hX hZ f hf hXq K hK ι V hV0 hV B hBP κ r hr hr1 Bj hBjP hBjlc hBeq; first | exact Proof_lem_fourfold_real_lc_fixed_model_positive_gap.solution | exact Proof_lem_fourfold_real_lc_fixed_model_positive_gap.solution _ | exact Proof_lem_fourfold_real_lc_fixed_model_positive_gap.solution _ _ | exact Proof_lem_fourfold_real_lc_fixed_model_positive_gap.solution _ _ _ | exact Proof_lem_fourfold_real_lc_fixed_model_positive_gap.solution _ _ _ _

end MMP.Fourfold

