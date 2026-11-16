module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.DltProgram
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.LcFourfoldSupportingDivisor
public import MMP.AlgebraicGeometry.MMP.Fourfold.ConeTheorem.LcRelativeCone
public import MMP.AlgebraicGeometry.MMP.Fourfold.BasepointFree.LcBasepointFree
public import MMP.AlgebraicGeometry.MMP.Contraction.SemiampleSupportingDivisor
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeRayAbsolute
public import StacksFrontier.AlgebraicGeometry.Limits.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
public import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceZero
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
public import StacksFrontier.AlgebraicGeometry.FiniteMorphismProjective.Projective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Composition
public import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive
public import MMP.AlgebraicGeometry.Intersection.PairingSeparation
public import MMP.AlgebraicGeometry.MMP.Fourfold.AffineBaseRegularGeneration
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.SurfaceMatrix
public import MMP.AlgebraicGeometry.Intersection.N1CartierCoordinates
public import MMP.AlgebraicGeometry.Positivity.Kleiman.AbsoluteCartier
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeConeInAbsolute
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
public import MMP.AlgebraicGeometry.Resolution.BlowupChartClosedImmersion
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.Corollaries
public import MMP.AlgebraicGeometry.MMP.Fourfold.ConvexGeography
public import MMP.AlgebraicGeometry.Morphisms.HProjective
public import MMP.AlgebraicGeometry.Modules.FiniteLocallyFreeRankOne

/-!
# The contraction theorem for projective lc fourfolds

Let `h : X ⟶ S` be a morphism of normal projective complex varieties, with `X` of dimension
four, let `(X, B)` be a log canonical pair with `B` a `ℚ`-divisor, and let `R` be a
`(K_X + B)`-negative extremal ray of the relative closed cone of curves `NE̅(X/S)`. Then `R` has
a contraction over `S`: a projective contraction `c : X ⟶ Z` onto a normal variety `Z`
projective over `S`, with `c_* 𝒪_X = 𝒪_Z` and `ρ(X/Z) = 1`, such that `-(K_X + B)` is ample
over `Z` and a curve `C` contracted by `h` is contracted by `c` exactly when its class lies
in `R`.

The proof regards `R` as an extremal ray of the absolute cone `NE̅(X)`, takes a nef Cartier
divisor `L` supporting it with `a L - (K_X + B)` ample, makes a multiple of `L` base point free
by the lc base point free theorem, and takes for `c` the Stein factorisation of the morphism
it defines.

## Main results

* `MMP.Fourfold.exists_isRelativeContractionOfFace_of_isNegativeRelativeExtremalRayOf`.

## Implementation notes

The ray is `MMP.Fourfold.IsNegativeRelativeExtremalRayOf` in `N₁(X/S)` for `K + B`, and the
contraction over `S` is `MMP.Mori.IsRelativeContractionOfFace` (the factorisation `c ≫ g = h`
with `g` projective, `c_* 𝒪_X = 𝒪_Z`, and the curve criterion). That `c` is a projective
surjective morphism of normal varieties is `MMP.Fourfold.IsContraction`, the relative Picard
number is `MMP.Fourfold.relativePicardNumberN1`, and relative ampleness of the `ℚ`-divisor
`-(K + B)` is `MMP.Mori.QDivisor.HasRelativelyAmpleMultiple`. Since `S` is projective, so is
`Z`; this is recorded as well.

## References

* [KM98] J. Kollár, S. Mori, *Birational geometry of algebraic varieties*, Theorem 3.25.
* [Fuj11] O. Fujino, *Fundamental theorems for the log minimal model program*.
-/

@[expose] public section

section

namespace Proof_thm_mmp_projective_fourfold_lc_contraction

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### Curve forms of Cartier divisors -/

section CurveForm

variable {k : Type} [Field k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k))
  [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX]

/-- Two linear forms on `N₁(X)_ℝ` agreeing on the classes of proper curves are equal. -/
private theorem linearMap_ext_numericalClass_cycle
    {φ ψ : NumericalCurveClasses sX →ₗ[ℝ] ℝ}
    (h : ∀ C : ProperCurve sX,
      φ (OneCycle.numericalClass sX (C.cycle ℝ)) = ψ (OneCycle.numericalClass sX (C.cycle ℝ))) :
    φ = ψ :=
  Submodule.linearMap_qext _ (Finsupp.lhom_ext' fun C => LinearMap.ext_ring (h C))

/-- The curve form is additive in the divisor. -/
private theorem curveForm_add (D D' : QDivisor X) (hD : D.IsQCartier) (hD' : D'.IsQCartier)
    (hDD' : (D + D').IsQCartier) :
    QDivisor.curveForm sX (D + D') hDD' =
      QDivisor.curveForm sX D hD + QDivisor.curveForm sX D' hD' := by
  refine linearMap_ext_numericalClass_cycle sX fun C => ?_
  rw [LinearMap.add_apply, MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
    MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
    MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
    QDivisor.intersectionNumber_add' k sX C.ι C.dim_le D D' hD hD' hDD']
  push_cast; rfl

/-- The curve form is `ℚ`-homogeneous in the divisor. -/
private theorem curveForm_smul (q : ℚ) (D : QDivisor X) (hD : D.IsQCartier)
    (hqD : (q • D).IsQCartier) :
    QDivisor.curveForm sX (q • D) hqD = (q : ℝ) • QDivisor.curveForm sX D hD := by
  refine linearMap_ext_numericalClass_cycle sX fun C => ?_
  rw [LinearMap.smul_apply, MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
    MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
    QDivisor.intersectionNumber_smul k sX C.ι C.dim_le q D hD hqD]
  push_cast; rfl

/-- The curve form depends only on the divisor. -/
private theorem curveForm_congr {D D' : QDivisor X} (e : D = D') (hD : D.IsQCartier)
    (hD' : D'.IsQCartier) : QDivisor.curveForm sX D hD = QDivisor.curveForm sX D' hD' := by
  subst e; rfl

/-- The curve form of a Cartier divisor on the class of a proper curve is its degree there. -/
private theorem curveForm_toQDivisor_numericalClass (W : Divisor X) (hW : W.IsCartier)
    (h : (Divisor.toQDivisor W).IsQCartier) (C : ProperCurve sX) :
    QDivisor.curveForm sX (Divisor.toQDivisor W) h (OneCycle.numericalClass sX (C.cycle ℝ)) =
      (W.degreeOn k sX C.ι C.dim_le hW : ℝ) := by
  rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
    QDivisor.intersectionNumber_toQDivisor k sX C.ι C.dim_le W hW h]
  push_cast; rfl

/-- The curve form of a Cartier divisor `W` is the intersection form of any Cartier divisor `E`
with `𝒪_X(W) ≅ 𝒪_X(E)`. -/
private theorem curveForm_toQDivisor_eq_intersectionNumber (W : Divisor X) (hW : W.IsCartier)
    (h : (Divisor.toQDivisor W).IsQCartier) (E : X.CartierDivisor)
    (e : W.divisorialSheaf ≅ MMP.CartierDivisor.sheaf E) :
    QDivisor.curveForm sX (Divisor.toQDivisor W) h =
      NumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ E) := by
  haveI := hW.isInvertibleModule_divisorialSheaf
  refine linearMap_ext_numericalClass_cycle sX fun C => ?_
  rw [curveForm_toQDivisor_numericalClass sX W hW h C,
    NumericalCurveClasses.intersectionNumber_ofCartier, NumericalCurveClasses.degree_numericalClass,
    OneCycle.degree_cycle]
  exact_mod_cast degreeOn_eq_of_iso k sX C.ι C.dim_le e

/-- The curve form of a Cartier divisor `W` is the degree form of `𝒪_X(W)`. -/
private theorem curveForm_toQDivisor_eq_degree (W : Divisor X) (hW : W.IsCartier)
    (h : (Divisor.toQDivisor W).IsQCartier) :
    haveI := hW.isInvertibleModule_divisorialSheaf
    QDivisor.curveForm sX (Divisor.toQDivisor W) h =
      NumericalCurveClasses.degree sX W.divisorialSheaf := by
  haveI := hW.isInvertibleModule_divisorialSheaf
  refine linearMap_ext_numericalClass_cycle sX fun C => ?_
  rw [curveForm_toQDivisor_numericalClass sX W hW h C, NumericalCurveClasses.degree_numericalClass,
    OneCycle.degree_cycle]
  rfl

private theorem toQDivisor_zsmul (n : ℤ) (W : Divisor X) :
    Divisor.toQDivisor (n • W) = (n : ℚ) • Divisor.toQDivisor W := by
  rw [map_zsmul, Int.cast_smul_eq_zsmul]

/-- The curve form is additive on Cartier divisors. -/
private theorem curveForm_toQDivisor_add {W W' : Divisor X} (hW : W.IsCartier)
    (hW' : W'.IsCartier) (h : (Divisor.toQDivisor (W + W')).IsQCartier) :
    QDivisor.curveForm sX (Divisor.toQDivisor (W + W')) h =
      QDivisor.curveForm sX (Divisor.toQDivisor W) (QDivisor.isQCartier_toQDivisor hW) +
        QDivisor.curveForm sX (Divisor.toQDivisor W') (QDivisor.isQCartier_toQDivisor hW') := by
  have e := map_add Divisor.toQDivisor W W'
  rw [curveForm_congr sX e h (e ▸ h), curveForm_add sX _ _ (QDivisor.isQCartier_toQDivisor hW)
    (QDivisor.isQCartier_toQDivisor hW') (e ▸ h)]

/-- The curve form is subtractive on Cartier divisors. -/
private theorem curveForm_toQDivisor_sub {W W' : Divisor X} (hW : W.IsCartier)
    (hW' : W'.IsCartier) (h : (Divisor.toQDivisor (W - W')).IsQCartier) :
    QDivisor.curveForm sX (Divisor.toQDivisor (W - W')) h =
      QDivisor.curveForm sX (Divisor.toQDivisor W) (QDivisor.isQCartier_toQDivisor hW) -
        QDivisor.curveForm sX (Divisor.toQDivisor W') (QDivisor.isQCartier_toQDivisor hW') := by
  rw [eq_sub_iff_add_eq, ← curveForm_toQDivisor_add sX (hW.sub hW') hW'
    (QDivisor.isQCartier_toQDivisor ((hW.sub hW').add hW'))]
  exact curveForm_congr sX (by rw [sub_add_cancel]) _ _

/-- The curve form of an integer multiple of a Cartier divisor. -/
private theorem curveForm_toQDivisor_zsmul (n : ℤ) {W : Divisor X} (hW : W.IsCartier)
    (h : (Divisor.toQDivisor (n • W)).IsQCartier) :
    QDivisor.curveForm sX (Divisor.toQDivisor (n • W)) h =
      (n : ℝ) • QDivisor.curveForm sX (Divisor.toQDivisor W) (QDivisor.isQCartier_toQDivisor hW) := by
  have e := toQDivisor_zsmul n W
  rw [curveForm_congr sX e h (e ▸ h),
    curveForm_smul sX _ _ (QDivisor.isQCartier_toQDivisor hW) (e ▸ h), Rat.cast_intCast]

/-- The curve form of a natural multiple of a Cartier divisor. -/
private theorem curveForm_toQDivisor_nsmul (n : ℕ) {W : Divisor X} (hW : W.IsCartier)
    (h : (Divisor.toQDivisor (n • W)).IsQCartier) :
    QDivisor.curveForm sX (Divisor.toQDivisor (n • W)) h =
      (n : ℝ) • QDivisor.curveForm sX (Divisor.toQDivisor W) (QDivisor.isQCartier_toQDivisor hW) := by
  have e : Divisor.toQDivisor (n • W) = (n : ℚ) • Divisor.toQDivisor W := by
    rw [map_nsmul, Nat.cast_smul_eq_nsmul]
  rw [curveForm_congr sX e h (e ▸ h),
    curveForm_smul sX _ _ (QDivisor.isQCartier_toQDivisor hW) (e ▸ h), Rat.cast_natCast]

/-- On `N₁(X/S)` the curve form is the absolute one composed with the natural map. -/
private theorem relativeCurveForm_eq_comp {S : Scheme.{0}} (f : X ⟶ S) (D : QDivisor X)
    (h : D.IsQCartier) :
    QDivisor.relativeCurveForm sX f D h =
      QDivisor.curveForm sX D h ∘ₗ relativeToAbsolute sX f := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun Z => ?_)
  simp only [QDivisor.relativeCurveForm, QDivisor.curveForm, Finsupp.sum, LinearMap.comp_apply,
    LinearMap.sum_apply, LinearMap.smul_apply]
  exact Finset.sum_congr rfl fun _ _ => rfl

end CurveForm

/-! ### Relative ampleness -/

/-- An `f`-ample Cartier divisor is ample over an affine neighbourhood of every point. -/
private theorem isRelativelyAmple_of_isRelativelyAmpleCartier {X Y : Scheme.{0}}
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X} {W : Divisor Y}
    (hW : MMP.Flips.IsRelativelyAmpleCartier f W) : W.IsRelativelyAmple f hW.1 := by
  obtain ⟨hWc, hamp⟩ := hW
  have := hWc.isInvertibleModule_divisorialSheaf
  intro y
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ y)
  exact ⟨V, hV, hyV, hamp V hV⟩

/-! ### Numerical classes -/

section Classes

variable {k : Type} [Field k] {X Y : Scheme.{0}} (sX : X ⟶ Spec (.of k))

/-- Numerical classes are separated by the degree forms of invertible sheaves. -/
private theorem numericalCurveClasses_ext {z z' : NumericalCurveClasses sX}
    (h : ∀ (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L],
      NumericalCurveClasses.degree sX L z = NumericalCurveClasses.degree sX L z') : z = z' := by
  obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX z
  obtain ⟨Z', rfl⟩ := OneCycle.numericalClass_surjective sX z'
  rw [← sub_eq_zero, ← map_sub]
  refine (Submodule.Quotient.mk_eq_zero _).mpr (OneCycle.mem_numericallyTrivial.mpr fun L _ => ?_)
  have := h L
  simp only [NumericalCurveClasses.degree_numericalClass] at this
  rw [map_sub, this, sub_self]

/-- A ray `ℝ_{≥0} · v`, `v ≠ 0`, is closed in `N₁(X)` for the numerical topology. -/
private theorem isClosed_ray {v : NumericalCurveClasses sX} (hv : v ≠ 0) :
    IsClosed {w : NumericalCurveClasses sX | ∃ c : ℝ, 0 ≤ c ∧ c • v = w} := by
  obtain ⟨L₀, hL₀, hv₀⟩ : ∃ (L₀ : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf
      X.ringCatSheaf.2 L₀), NumericalCurveClasses.degree sX L₀ v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv (numericalCurveClasses_ext sX fun L _ => by rw [hcon L, map_zero])
  set a := NumericalCurveClasses.degree sX L₀ v
  have hS : {w : NumericalCurveClasses sX | ∃ c : ℝ, 0 ≤ c ∧ c • v = w} =
      {w | 0 ≤ NumericalCurveClasses.degree sX L₀ w / a} ∩
        ⋂ (L : X.Modules) (h : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
          {w | NumericalCurveClasses.degree sX L w =
            NumericalCurveClasses.degree sX L₀ w / a * NumericalCurveClasses.degree sX L v} := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨c, hc, rfl⟩
      have hca : NumericalCurveClasses.degree sX L₀ (c • v) / a = c := by
        rw [map_smul, smul_eq_mul, mul_div_assoc, div_self hv₀, mul_one]
      refine ⟨by rw [hca]; exact hc, fun L _ => ?_⟩
      rw [hca, map_smul, smul_eq_mul]
    · rintro ⟨hc, hL⟩
      refine ⟨_, hc, numericalCurveClasses_ext sX fun L _ => ?_⟩
      rw [map_smul, smul_eq_mul, hL L]
  rw [hS]
  have hc₀ := NumericalCurveClasses.continuous_degree sX L₀
  refine (isClosed_le continuous_const (hc₀.div_const a)).inter
    (isClosed_iInter fun L => isClosed_iInter fun h => ?_)
  have hc := NumericalCurveClasses.continuous_degree sX L
  exact isClosed_eq hc ((hc₀.div_const a).mul continuous_const)

variable (f : X ⟶ Y)

/-- The relative degree form of `L` is the absolute one composed with `N₁(X/Y) → N₁(X)`. -/
private theorem relativeDegree_eq_comp (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    RelativeNumericalCurveClasses.degree sX f L =
      (NumericalCurveClasses.degree sX L).comp (relativeToAbsolute sX f) := by
  apply Submodule.linearMap_qext
  rfl

private theorem continuous_relativeToAbsolute : Continuous (relativeToAbsolute sX f) := by
  refine continuous_iInf_rng.2 fun L => continuous_iInf_rng.2 fun h => continuous_induced_rng.2 ?_
  have := h
  have hc := RelativeNumericalCurveClasses.continuous_degree sX f L
  rw [relativeDegree_eq_comp sX f L, LinearMap.coe_comp] at hc
  exact hc

private theorem injective_relativeToAbsolute : Function.Injective (relativeToAbsolute sX f) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro z hz
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX f z
  have hZ : OneCycle.numericalClass sX (Z : OneCycle ℝ sX) = 0 := LinearMap.mem_ker.mp hz
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    ((Submodule.Quotient.mk_eq_zero (OneCycle.numericallyTrivial sX)).mp hZ)

/-- `f`-ampleness of an invertible sheaf only depends on its isomorphism class. -/
private theorem isRelativelyAmple_of_iso {L L' : X.Modules} [Stacks.Ample.IsInvertibleModule X L]
    [Stacks.Ample.IsInvertibleModule X L'] (e : L ≅ L') (h : IsRelativelyAmple f L) :
    IsRelativelyAmple f L' := by
  intro y
  obtain ⟨V, hV, hyV, hA⟩ := h y
  exact ⟨V, hV, hyV, (Stacks.RelativeVeryAmple.isAmple_congr _ _
    (Functor.mapIso _ e)).mp hA⟩

/-- If every curve contracted by `f` has its class on the ray `ℝ≥0 · v`, then so does the image
in `N₁(X)` of every class of the closed relative cone `NE̅(X/Y)`. -/
private theorem relativeToAbsolute_mem_ray {v : NumericalCurveClasses sX} (hv : v ≠ 0)
    (hcontr : ∀ C : ProperCurve sX, C.IsContractedBy f →
      ∃ c : ℝ, 0 ≤ c ∧ c • v = OneCycle.numericalClass sX (C.cycle ℝ))
    {z : RelativeNumericalCurveClasses sX f} (hz : z ∈ relativeClosedConeOfCurves sX f) :
    ∃ c : ℝ, 0 ≤ c ∧ c • v = relativeToAbsolute sX f z := by
  set ι := relativeToAbsolute sX f
  have hsub : (relativeConeOfCurves sX f : Set _) ⊆ ι ⁻¹' {w | ∃ c : ℝ, 0 ≤ c ∧ c • v = w} := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨C, hC⟩, rfl⟩ := hx
      exact hcontr C hC
    | zero => exact ⟨0, le_rfl, by rw [zero_smul, map_zero]⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, hcx⟩ := hx
      obtain ⟨c', hc', hcy⟩ := hy
      exact ⟨c + c', add_nonneg hc hc', by rw [add_smul, hcx, hcy, map_add]⟩
    | smul a x _ hx =>
      obtain ⟨c, hc, hcx⟩ := hx
      exact ⟨a * c, mul_nonneg a.2 hc, by rw [mul_smul, hcx]; exact (map_smul ι (a : ℝ) x).symm⟩
  exact closure_minimal hsub
    ((isClosed_ray sX hv).preimage (continuous_relativeToAbsolute sX f)) hz

/-- If the Cartier divisor `A` has sheaf `𝒪_X(-E)`, its relative intersection form is minus the
degree form of `𝒪_X(E)` read through `N₁(X/Y) → N₁(X)`. -/
private theorem intersectionNumber_ofCartier_eq_neg_degree [QuasiCompact sX]
    [IsLocallyNoetherian X] [IsNormal X] {E : Divisor X} (hE : E.IsCartier)
    [Stacks.Ample.IsInvertibleModule X E.divisorialSheaf]
    [Stacks.Ample.IsInvertibleModule X (-E).divisorialSheaf] {A : X.CartierDivisor}
    (e : (-E).divisorialSheaf ≅ MMP.CartierDivisor.sheaf A)
    (z : RelativeNumericalCurveClasses sX f) :
    RelativeNumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ A) z =
      -NumericalCurveClasses.degree sX E.divisorialSheaf (relativeToAbsolute sX f z) := by
  have hdeg (C : ProperCurve sX) : C.degree k (MMP.CartierDivisor.sheaf A) =
      -C.degree k E.divisorialSheaf := by
    rw [ProperCurve.degree, ProperCurve.degree, ← degreeOn_eq_of_iso k sX C.ι C.dim_le e]
    exact Divisor.degreeOn_neg' k sX C.ι C.dim_le _ hE
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX f z
  rw [RelativeNumericalCurveClasses.intersectionNumber_relativeNumericalClass,
    OneCycle.intersectionNumber_ofCartier]
  change OneCycle.degree ℝ sX _ (Z : OneCycle ℝ sX) =
    -(OneCycle.degree ℝ sX E.divisorialSheaf (Z : OneCycle ℝ sX))
  simp only [OneCycle.degree_apply, Finsupp.sum, hdeg, Int.cast_neg, mul_neg,
    Finset.sum_neg_distrib]

/-- The numerical class of a curve pairs with an invertible sheaf by its degree. -/
private theorem degree_numericalClass_cycle (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (C : ProperCurve sX) :
    NumericalCurveClasses.degree sX L (OneCycle.numericalClass sX (C.cycle ℝ)) =
      (C.degree k L : ℝ) := by
  rw [NumericalCurveClasses.degree_numericalClass, OneCycle.degree_apply, ProperCurve.cycle,
    Finsupp.sum_single_index (by simp), one_mul]

/-- The numerical class of a curve pairs with a Cartier divisor by its degree. -/
private theorem intersectionNumber_numericalClass_cycle (L : X.CartierDivisor)
    (C : ProperCurve sX) :
    NumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ L)
        (OneCycle.numericalClass sX (C.cycle ℝ)) =
      (C.degree k (MMP.CartierDivisor.sheaf L) : ℝ) := by
  rw [NumericalCurveClasses.intersectionNumber_numericalClass,
    OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree,
    ← NumericalCurveClasses.degree_numericalClass, degree_numericalClass_cycle]

end Classes

/-! ### Ample sheaves on projective varieties -/

section Ample

/-- A Cartier divisor ample over `Spec k` is ample. -/
private theorem isAmple_of_isRelativelyAmpleCartier {k : Type} [Field k] {Z : Scheme.{0}}
    [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z] (sZ : Z ⟶ Spec (.of k))
    [QuasiCompact sZ] {A : Divisor Z} (hA : MMP.Flips.IsRelativelyAmpleCartier sZ A) :
    haveI := hA.1.isInvertibleModule_divisorialSheaf
    Scheme.Modules.IsAmple Z A.divisorialSheaf := by
  haveI := hA.1.isInvertibleModule_divisorialSheaf
  exact (Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mp
    ((Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple sZ _).mp
      (Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple sZ _
        inferInstance (isRelativelyAmple_of_isRelativelyAmpleCartier hA)))

end Ample

/-- **`-D` is ample over a contraction of a `D`-negative ray.** Let `c : X ⟶ Z` be projective
and suppose every curve contracted by `c` has class on the ray `ℝ≥0 · w₀`, `w₀ ≠ 0`, on which
the Cartier multiple `E = (index D) • D` is negative. Then `-D` has a `c`-ample Cartier multiple,
namely `-E`: by the relative Kleiman criterion it suffices that `-E` is positive on the nonzero
classes of `NE̅(X/Z)`, and these map onto positive multiples of `w₀`. -/
private theorem hasRelativelyAmpleMultiple_neg_of_forall_isContractedBy {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X Z : Scheme.{0}} [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral X] (sX : X ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    [AlgebraicGeometry.IsVariety k sX] [AlgebraicGeometry.IsVariety k sZ] (c : X ⟶ Z)
    (hc : IsProjective c) (hcomp : c ≫ sZ = sX) {D : QDivisor X}
    (hq : D.IsQCartier) {w₀ : NumericalCurveClasses sX} (hw₀ : w₀ ≠ 0)
    (hray : ∀ C : ProperCurve sX, C.IsContractedBy c →
      ∃ t : ℝ, 0 ≤ t ∧ t • w₀ = OneCycle.numericalClass sX (C.cycle ℝ))
    (hdeg : haveI := (Divisor.mem_cartierSubgroup.mp
        (D.cartierIndexSMul hq).2).isInvertibleModule_divisorialSheaf
      NumericalCurveClasses.degree sX ((D.cartierIndexSMul hq : Divisor X)).divisorialSheaf w₀ <
        0) :
    (-D).HasRelativelyAmpleMultiple c := by
  set E := D.cartierIndexSMul hq
  have hEc : (E : Divisor X).IsCartier := Divisor.mem_cartierSubgroup.mp E.2
  refine ⟨_, QDivisor.cartierIndex_pos hq, -(E : Divisor X), hEc.neg,
    by rw [map_neg, QDivisor.toQDivisor_cartierIndexSMul, smul_neg], ?_⟩
  haveI := hEc.neg.isInvertibleModule_divisorialSheaf
  haveI := hEc.isInvertibleModule_divisorialSheaf
  obtain ⟨A', ⟨e'⟩⟩ :=
    MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf (-(E : Divisor X)).divisorialSheaf
  rw [Divisor.isRelativelyAmple_iff]
  refine isRelativelyAmple_of_iso c e'.symm <|
    (isRelativelyAmple_cartierSheaf_iff_forall_relativeClosedConeOfCurves_pos sZ sX c hc
      hcomp A').mpr fun z hz hz0 => ?_
  obtain ⟨t, ht, htz⟩ := relativeToAbsolute_mem_ray sX c hw₀ hray hz
  have ht0 : 0 < t := ht.lt_of_ne <| by
    rintro rfl
    rw [zero_smul] at htz
    exact hz0 (injective_relativeToAbsolute sX c (htz.symm.trans (map_zero _).symm))
  rw [intersectionNumber_ofCartier_eq_neg_degree sX c hEc e', ← htz, map_smul, smul_eq_mul]
  nlinarith

section Cone

variable {ι : Type*} [Fintype ι] {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

private theorem continuous_of_coordinates (Φ : V ≃L[ℝ] (ι → ℝ)) (f : V →ₗ[ℝ] ℝ) : Continuous f := by
  have : (f : V → ℝ) = (f ∘ₗ (Φ.symm : (ι → ℝ) →ₗ[ℝ] V)) ∘ Φ := by
    funext z; simp
  rw [this]
  exact (LinearMap.continuous_of_finiteDimensional _).comp Φ.continuous

private theorem isCompact_unitSlice (Φ : V ≃L[ℝ] (ι → ℝ)) {N : Set V} (hN : IsClosed N) :
    IsCompact {z | z ∈ N ∧ ‖Φ z‖ = 1} := by
  have hc : IsClosed (Φ '' N) := Φ.toHomeomorph.isClosedMap N hN
  have h : {z | z ∈ N ∧ ‖Φ z‖ = 1} = Φ.toHomeomorph ⁻¹' (Φ '' N ∩ Metric.sphere 0 1) := by
    ext z
    simp [Φ.injective.mem_set_image]
  rw [h, Φ.toHomeomorph.isCompact_preimage]
  exact (isCompact_sphere 0 1).inter_left hc

/-- A nonzero element of a set closed under nonnegative scaling, rescaled to the unit sphere of a
coordinate system. -/
private theorem mem_unitSlice_of_smul_mem (Φ : V ≃L[ℝ] (ι → ℝ)) {S : Set V}
    (hS : ∀ z ∈ S, ∀ c : ℝ, 0 ≤ c → c • z ∈ S) {z : V} (hz : z ∈ S) (hz0 : z ≠ 0) :
    0 < ‖Φ z‖ ∧ ‖Φ z‖⁻¹ • z ∈ {z | z ∈ S ∧ ‖Φ z‖ = 1} := by
  have hr : 0 < ‖Φ z‖ := norm_pos_iff.mpr fun h => hz0 (Φ.injective (by simp [h]))
  refine ⟨hr, hS z hz _ (inv_nonneg.mpr hr.le), ?_⟩
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), inv_mul_cancel₀ hr.ne']

private theorem pos_of_forall_unitSlice (Φ : V ≃L[ℝ] (ι → ℝ)) (N : PointedCone ℝ V) (f : V →ₗ[ℝ] ℝ)
    (h : ∀ z ∈ {z | z ∈ (N : Set V) ∧ ‖Φ z‖ = 1}, 0 < f z) {z : V} (hz : z ∈ N) (hz0 : z ≠ 0) :
    0 < f z := by
  obtain ⟨hr, hmem⟩ := mem_unitSlice_of_smul_mem Φ (fun _ hz _ hc => N.smul_mem hc hz) hz hz0
  have := h _ hmem
  rw [map_smul, smul_eq_mul] at this
  exact (mul_pos_iff_of_pos_left (inv_pos.mpr hr)).mp this

private theorem exists_pos_lt_mul (Φ : V ≃L[ℝ] (ι → ℝ)) (N : PointedCone ℝ V) (hN : IsClosed (N : Set V))
    (ℓ φ : V →ₗ[ℝ] ℝ) (hℓ : ∀ z ∈ N, 0 ≤ ℓ z) (h0 : ∀ z ∈ N, z ≠ 0 → ℓ z = 0 → φ z < 0) :
    ∃ a : ℝ, 0 < a ∧ ∀ z ∈ N, z ≠ 0 → φ z < a * ℓ z := by
  set K := {z | z ∈ (N : Set V) ∧ ‖Φ z‖ = 1}
  have hK : IsCompact K := isCompact_unitSlice Φ hN
  have hφc := continuous_of_coordinates Φ φ
  have hℓc := continuous_of_coordinates Φ ℓ
  obtain ⟨M, hM⟩ := hK.bddAbove_image hφc.continuousOn
  set K₀ := K ∩ {z | 0 ≤ φ z}
  have hK₀ : IsCompact K₀ := hK.inter_right (isClosed_le continuous_const hφc)
  have key : ∃ a : ℝ, 0 < a ∧ ∀ z ∈ K, φ z < a * ℓ z := by
    rcases K₀.eq_empty_or_nonempty with hK₀e | hK₀ne
    · refine ⟨1, one_pos, fun z hz => ?_⟩
      have : φ z < 0 := by
        by_contra h
        exact Set.eq_empty_iff_forall_notMem.mp hK₀e z ⟨hz, not_lt.mp h⟩
      linarith [hℓ z hz.1]
    obtain ⟨x₁, hx₁, hmin⟩ := hK₀.exists_isMinOn hK₀ne hℓc.continuousOn
    have hx₁0 : x₁ ≠ 0 := fun h => by
      have := hx₁.1.2; rw [h, map_zero, norm_zero] at this; exact zero_ne_one this
    have hm₁ : 0 < ℓ x₁ := by
      rcases (hℓ x₁ hx₁.1.1).lt_or_eq with h | h
      · exact h
      · exact absurd hx₁.2 (not_le.mpr (h0 x₁ hx₁.1.1 hx₁0 h.symm))
    refine ⟨(|M| + 1) / ℓ x₁, by positivity, fun z hz => ?_⟩
    by_cases hφz : 0 ≤ φ z
    · have h1 : ℓ x₁ ≤ ℓ z := hmin ⟨hz, hφz⟩
      have h2 : φ z ≤ M := hM ⟨z, hz, rfl⟩
      calc φ z ≤ M := h2
        _ < |M| + 1 := by linarith [le_abs_self M]
        _ = (|M| + 1) / ℓ x₁ * ℓ x₁ := by field_simp
        _ ≤ (|M| + 1) / ℓ x₁ * ℓ z := by gcongr
    · have := hℓ z hz.1
      have : 0 ≤ (|M| + 1) / ℓ x₁ * ℓ z := by positivity
      linarith
  obtain ⟨a, ha, hKa⟩ := key
  refine ⟨a, ha, fun z hz hz0 => ?_⟩
  have := pos_of_forall_unitSlice Φ N (a • ℓ - φ) (fun z hz => by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, sub_pos]
    exact hKa z hz) hz hz0
  simpa [sub_pos] using this

end Cone

section RayTransport

variable {P Q : Type*} [AddCommGroup P] [Module ℝ P] [AddCommGroup Q] [Module ℝ Q]

private theorem isExtremalRay_image (f : P ≃ₗ[ℝ] Q) {A R : Set P}
    (h : IsExtremalRay ℝ A R) : IsExtremalRay ℝ (f '' A) (f '' R) := by
  obtain ⟨⟨hRA, ⟨hR0, hRs⟩, hRadd, hRext⟩, v, hv0, hRv⟩ := h
  refine ⟨⟨Set.image_mono hRA, ⟨⟨0, hR0, map_zero f⟩, ?_⟩, ?_, ?_⟩, f v,
    fun h => hv0 (f.injective (by rw [h, map_zero])), ?_⟩
  · rintro _ ⟨r, hr, rfl⟩ c hc
    exact ⟨c • r, hRs r hr c hc, map_smul _ _ _⟩
  · rintro _ ⟨r, hr, rfl⟩ _ ⟨r', hr', rfl⟩
    exact ⟨r + r', hRadd r hr r' hr', map_add _ _ _⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ ⟨r, hr, hrab⟩
    have : a + b = r := f.injective (by rw [hrab, map_add])
    obtain ⟨haR, hbR⟩ := hRext a ha b hb (this ▸ hr)
    exact ⟨⟨a, haR, rfl⟩, ⟨b, hbR, rfl⟩⟩
  · rw [hRv]
    ext w
    constructor
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨c, hc, (map_smul _ _ _).symm⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c • v, ⟨c, hc, rfl⟩, map_smul _ _ _⟩

end RayTransport

section WeilOfCartier

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]

/-- On an integral Noetherian scheme every Cartier divisor has a Weil divisor. -/
private theorem exists_isWeilDivisorOfCartier (A : X.CartierDivisor) :
    ∃ w : Divisor X, MMP.Intersection.IsWeilDivisorOfCartier A w := by
  letI : IsNoetherian X := ⟨⟩
  have h0 : ∀ s ∈ MMP.Intersection.cartierSupport A, Order.coheight s = 0 → False := by
    intro s hs h0
    have : Ring.KrullDimLE 0 (X.presheaf.stalk s) := krullDimLE_of_coheight_le (by simp [h0])
    have : IsArtinianRing (X.presheaf.stalk s) := isArtinianRing_iff_krullDimLE_zero.mpr this
    exact MMP.Intersection.notMem_cartierSupport_of_isArtinianRing A s hs
  have hfin := finite_setOf_genericPoint_mem
    (MMP.Intersection.isClosed_cartierSupport A) h0
  refine ⟨Finsupp.ofSupportFinite (fun P => MMP.Intersection.primeDivisorOrder P A)
    (hfin.subset fun P hP => ?_), fun P => ?_⟩
  · by_contra h
    have hg : (MMP.Intersection.primeDivisorSubvariety P).genericPoint = P.genericPoint := rfl
    refine hP ((MMP.Intersection.isOrderAlong_primeDivisorOrder A P).eq_zero_of_not_subset
      fun h' => h ?_)
    show P.genericPoint ∈ MMP.Intersection.cartierSupport A
    rw [← hg]
    exact MMP.Intersection.genericPoint_mem_cartierSupport_iff.mpr h'
  · rw [DivisorWithCoeffs.coeff_apply, Finsupp.ofSupportFinite_coe]
    exact MMP.Intersection.isOrderAlong_primeDivisorOrder A P

/-- Every Cartier divisor has a Cartier Weil divisor with the same sheaf. -/
private theorem exists_divisor_iso_sheaf (A : X.CartierDivisor) :
    ∃ w : Divisor X, w.IsCartier ∧
      Nonempty (w.divisorialSheaf ≅ MMP.CartierDivisor.sheaf A) := by
  obtain ⟨w, hw⟩ := exists_isWeilDivisorOfCartier A
  obtain ⟨e⟩ := hw.nonempty_sheaf_iso_divisorialSheaf
  exact ⟨w, hw.isCartier, ⟨e.symm⟩⟩

end WeilOfCartier

section Kleiman

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  (sX : X ⟶ Spec (.of ℂ)) [AlgebraicGeometry.IsProjectiveVariety ℂ sX]

/-- An ample Cartier divisor is positive on `NE̅(X) ∖ 0`. -/
private theorem curveForm_pos_of_isAmple (W : Divisor X) (hW : W.IsCartier) (hA : W.IsAmple hW)
    (h : (Divisor.toQDivisor W).IsQCartier) :
    ∀ z ∈ closedConeOfCurves sX, z ≠ 0 →
      0 < QDivisor.curveForm sX (Divisor.toQDivisor W) h z := by
  haveI := hW.isInvertibleModule_divisorialSheaf
  obtain ⟨E, ⟨e⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf W.divisorialSheaf
  rw [curveForm_toQDivisor_eq_intersectionNumber sX W hW h E e]
  exact (isAmple_cartierSheaf_iff_forall_closedConeOfCurves_pos sX E).mp
    ((Stacks.RelativeVeryAmple.isAmple_congr _ _ e).mp hA)

/-- **Kleiman's criterion** for a Cartier Weil divisor. -/
private theorem isAmple_of_curveForm_pos (W : Divisor X) (hW : W.IsCartier)
    (h : (Divisor.toQDivisor W).IsQCartier)
    (hpos : ∀ z ∈ closedConeOfCurves sX, z ≠ 0 →
      0 < QDivisor.curveForm sX (Divisor.toQDivisor W) h z) :
    W.IsAmple hW := by
  haveI := hW.isInvertibleModule_divisorialSheaf
  obtain ⟨E, ⟨e⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf W.divisorialSheaf
  rw [curveForm_toQDivisor_eq_intersectionNumber sX W hW h E e] at hpos
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _ e).mpr
    ((isAmple_cartierSheaf_iff_forall_closedConeOfCurves_pos sX E).mpr hpos)

omit [AlgebraicGeometry.IsProjectiveVariety ℂ sX] in
/-- A projective variety carries a Cartier divisor whose invertible sheaf is ample. -/
private theorem exists_isAmple_sheaf (h : AlgebraicGeometry.IsProjectiveVariety ℂ sX) :
    ∃ D : X.CartierDivisor, Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf D) := by
  obtain ⟨⟨L, hL, hrel, hA⟩, -⟩ :=
    MMP.Foundations.IsProjective.exists_isRelativelyAmple h.isProjective.isProjective
  obtain ⟨A, ⟨e⟩⟩ := hA h.toIsIntegral
  exact ⟨A, (Stacks.RelativeVeryAmple.isAmple_congr _ _ e).mpr
    (Stacks.HProjective.isAmple_of_isRelativelyAmple_of_isAffine sX L hrel)⟩

/-- The kernel of a closed immersion from a reduced scheme is the vanishing ideal of its range. -/
private theorem ker_eq_vanishingIdeal_of_isReduced {Y W : Scheme.{0}} (ι : Y ⟶ W)
    [IsClosedImmersion ι] [IsReduced Y] (T : TopologicalSpace.Closeds W)
    (hT : (T : Set W) = Set.range ι) :
    ι.ker = Scheme.IdealSheafData.vanishingIdeal T := by
  have hrad : ι.ker.radical = ι.ker := by
    refine Scheme.IdealSheafData.ext (funext fun U => ?_)
    simp only [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
    apply le_antisymm
    · intro x hx
      obtain ⟨n, hn⟩ := hx
      rw [RingHom.mem_ker, map_pow] at hn
      rw [RingHom.mem_ker]
      exact IsReduced.eq_zero _ ⟨n, hn⟩
    · exact Ideal.le_radical
  have hs : (ι.ker.support : Set W) = Set.range ι := by
    rw [Scheme.Hom.support_ker, (ι.isClosedEmbedding).isClosed_range.closure_eq]
  have : ι.ker.support = T := by
    apply TopologicalSpace.Closeds.ext
    rw [hs, hT]
  rw [← this, Scheme.IdealSheafData.vanishingIdeal_support, hrad]

/-- A closed immersion from an integral scheme is, up to isomorphism, the closed immersion of the
closure of the image of the generic point. -/
private theorem exists_iso_curveSubschemeAt {Y W : Scheme.{0}} [IsIntegral Y] (ι : Y ⟶ W)
    [IsClosedImmersion ι] :
    ∃ e : Y ≅ curveSubschemeAt (ι (genericPoint Y)), e.hom ≫ curveSubschemeAtι _ = ι := by
  have hrange : Set.range ι = closure {ι (genericPoint Y)} := by
    rw [← Set.image_singleton, ι.isClosedEmbedding.closure_image_eq,
      (genericPoint_spec Y).def]
    simp
  have hker : ι.ker = (curveSubschemeAtι (ι (genericPoint Y))).ker := by
    rw [ker_eq_vanishingIdeal_of_isReduced ι (TopologicalSpace.Closeds.closure
      {ι (genericPoint Y)}) hrange.symm]
    unfold curveSubschemeAtι
    rw [Scheme.IdealSheafData.ker_subschemeι]
  have hf : IsIso (IsClosedImmersion.lift (curveSubschemeAtι (ι (genericPoint Y))) ι hker.ge) :=
    IsClosedImmersion.isIso_of_ker_eq ι (curveSubschemeAtι _) _
      (IsClosedImmersion.lift_fac _ _ _) hker
  exact ⟨asIso (IsClosedImmersion.lift (curveSubschemeAtι (ι (genericPoint Y))) ι hker.ge),
    IsClosedImmersion.lift_fac _ _ _⟩

/-- A Cartier divisor whose curve form is nonnegative on the classes of proper curves is nef. -/
private theorem isNef_of_forall_properCurve (L : Divisor X) (hL : L.IsCartier)
    (h : (Divisor.toQDivisor L).IsQCartier)
    (hnn : ∀ C : ProperCurve sX, 0 ≤ QDivisor.curveForm sX (Divisor.toQDivisor L) h
      (OneCycle.numericalClass sX (C.cycle ℝ))) : L.IsNef ℂ sX := by
  refine ⟨hL, fun C c _ _ _ hC => ?_⟩
  obtain ⟨e, he⟩ := exists_iso_curveSubschemeAt c
  have hι : curveSubschemeAtι (c (genericPoint C)) = e.inv ≫ c := (Iso.eq_inv_comp e).mpr he
  have hdim : topologicalKrullDim (curveSubschemeAt (c (genericPoint C))) = 1 := by
    rw [← hC]
    exact (IsHomeomorph.topologicalKrullDim_eq _ e.inv.homeomorph.isHomeomorph)
  have hprop : IsProper (curveSubschemeAtι (c (genericPoint C)) ≫ sX) := by
    rw [hι, Category.assoc]; infer_instance
  let C₀ : ProperCurve sX := ⟨c (genericPoint C), ⟨hdim, hprop⟩⟩
  have h0 := hnn C₀
  rw [curveForm_toQDivisor_numericalClass sX L hL h C₀] at h0
  have : L.degreeOn ℂ sX c hC.le hL = L.degreeOn ℂ sX C₀.ι C₀.dim_le hL := by
    haveI := hL.isInvertibleModule_divisorialSheaf
    exact MMP.Threefold.Resolution.degreeOn_eq_of_iso_comp ℂ sX c C₀.ι hC.le C₀.dim_le e he _
  rw [this]
  exact_mod_cast h0

end Kleiman

section Absolute

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))

/-- Every proper curve is contracted by the structure morphism. -/
private theorem isContractedBy_structure (C : ProperCurve sX) : C.IsContractedBy sX :=
  fun _ _ => Subsingleton.elim _ _

/-- Over the base point, the natural map `N₁(X / Spec ℂ) → N₁(X)` is bijective. -/
private theorem relativeToAbsolute_bijective :
    Function.Bijective (relativeToAbsolute sX sX) := by
  refine ⟨?_, fun z => ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX sX z
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (mem_relativeNumericallyTrivial.mpr ((Submodule.Quotient.mk_eq_zero _).mp hz))
  · obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX z
    have hZ : Z ∈ relativeOneCycles sX sX :=
      (Finsupp.mem_supported ℝ Z).mpr fun C _ => isContractedBy_structure sX C
    exact ⟨relativeNumericalClass sX sX ⟨Z, hZ⟩,
      isNaturalRelativeMap_relativeToAbsolute sX sX ⟨Z, hZ⟩⟩

end Absolute

section ConeTheorem

variable {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)}

/-- The lc cone theorem for a projective complex fourfold, read in the absolute space `N₁(X)`
(the relative cone theorem over the base point `Spec ℂ`): every `(K + B)`-negative extremal ray is
spanned by the class of a curve; for an ample Cartier `A` and `ε > 0` only finitely many of them
are `(K + B + εA)`-negative; and `NE̅(X)` is the sum of its part where `K + B ≥ 0` and the convex
cone spanned by the negative extremal rays. -/
private theorem closedConeOfCurves_structure (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4) {B : QDivisor X}
    (hB : MMP.Intersection.IsLogCanonicalPair sX B)
    (hD : (Divisor.toQDivisor K + B).IsQCartier) :
    (∀ R', IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R' →
      ∃ C : ProperCurve sX,
        R' = {w | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass sX (C.cycle ℝ) = w}) ∧
    (∀ (A : Divisor X) (hA : A.IsCartier), A.IsAmple hA → ∀ ε : ℝ, 0 < ε →
      haveI := hA.isInvertibleModule_divisorialSheaf
      {R' | IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R' ∧ ∀ u ∈ R', u ≠ 0 →
        QDivisor.curveForm sX (Divisor.toQDivisor K + B) hD u +
          ε * NumericalCurveClasses.degree sX A.divisorialSheaf u < 0}.Finite) ∧
    (∀ z ∈ closedConeOfCurves sX, ∃ a ∈ closedConeOfCurves sX,
      0 ≤ QDivisor.curveForm sX (Divisor.toQDivisor K + B) hD a ∧
      ∃ b ∈ PointedCone.hull ℝ
        (⋃₀ {R' | IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R'}), z = a + b) := by
  haveI hXp : AlgebraicGeometry.IsProjectiveVariety ℂ sX := hX
  set D := Divisor.toQDivisor K + B with hDdef
  set φ := QDivisor.curveForm sX D hD with hφdef
  set N := closedConeOfCurves sX with hNdef
  have hS : MMP.Mori.IsProjectiveVariety ℂ (𝟙 (Spec (.of ℂ))) :=
    (AlgebraicGeometry.isProjectiveVariety_iff ℂ _).mpr
      ⟨(MMP.Mori.isVariety_iff ℂ _).mpr ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩,
        MMP.isProjectiveMorphism_of_isClosedImmersion _⟩
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ (𝟙 (Spec (.of ℂ))) := hS
  obtain ⟨hD₀, hray, -, hdec, hfin, -, -⟩ :=
    exists_relativeClosedConeOfCurves_eq_add_hull_of_isLogCanonicalPair hX hS sX
      (Category.comp_id sX) hK.1 hK hB
  have hbij := relativeToAbsolute_bijective sX
  set e := LinearEquiv.ofBijective (relativeToAbsolute sX sX) hbij with hedef
  have hNimg : e '' (relativeClosedConeOfCurves sX sX : Set _) = (N : Set _) := by
    have := image_relativeClosedConeOfCurves_eq_inter_range sX (𝟙 (Spec (.of ℂ))) sX
      (Category.comp_id sX)
    rw [hbij.2.range_eq, Set.inter_univ] at this
    exact this
  have hNpre : e.symm '' (N : Set _) = (relativeClosedConeOfCurves sX sX : Set _) := by
    rw [← hNimg, ← Set.image_comp]; simp
  have hform : ∀ u, QDivisor.relativeCurveForm sX sX D hD u = φ (e u) := fun u => by
    rw [relativeCurveForm_eq_comp]; rfl
  have hneg_img : ∀ R₀, IsNegativeRelativeExtremalRayOf sX sX D R₀ →
      IsNegativeExtremalRayOf sX D (e '' R₀) := by
    rintro R₀ ⟨h1, h2, h3⟩
    refine ⟨hD, hNimg ▸ isExtremalRay_image e h2, ?_⟩
    rintro _ ⟨u, hu, rfl⟩ hu0
    rw [← hform]
    exact h3 u hu (fun h => hu0 (by rw [h, map_zero]))
  have hneg_pre : ∀ R', IsNegativeExtremalRayOf sX D R' →
      IsNegativeRelativeExtremalRayOf sX sX D (e ⁻¹' R') := by
    rintro R' ⟨h1, h2, h3⟩
    refine ⟨hD, ?_, fun u hu hu0 => ?_⟩
    · rw [← e.image_symm_eq_preimage, ← hNpre]; exact isExtremalRay_image e.symm h2
    · rw [hform]
      exact h3 (e u) hu (fun h => hu0 (e.injective (by rw [h, map_zero])))
  refine ⟨fun R' hR' => ?_, fun A hA hAamp ε hε => ?_, fun z hz => ?_⟩
  · obtain ⟨C, hC, -, hRC, -, -⟩ := hray _ (hneg_pre R' hR')
    have hev : e (C.relativeClass sX hC) = OneCycle.numericalClass sX (C.cycle ℝ) :=
      isNaturalRelativeMap_relativeToAbsolute sX sX _
    refine ⟨C, ?_⟩
    rw [← Set.image_preimage_eq R' e.surjective, hRC]
    ext w
    constructor
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩; exact ⟨c, hc, by rw [map_smul, hev]⟩
    · rintro ⟨c, hc, rfl⟩; exact ⟨c • C.relativeClass sX hC, ⟨c, hc, rfl⟩, by rw [map_smul, hev]⟩
  · haveI := hA.isInvertibleModule_divisorialSheaf
    refine ((hfin A hA hAamp ε hε).image fun R₀ => e '' R₀).subset ?_
    rintro R' ⟨hR'neg, hR'ψ⟩
    refine ⟨e ⁻¹' R', ⟨hneg_pre R' hR'neg, fun u hu hu0 => ?_⟩,
      Set.image_preimage_eq R' e.surjective⟩
    have := hR'ψ (e u) hu (fun h => hu0 (e.injective (by rw [h, map_zero])))
    rw [relativeCurveForm_eq_comp, relativeDegree_eq_comp]
    exact this
  · obtain ⟨w₀, hw₀, rfl⟩ : ∃ w₀ ∈ (relativeClosedConeOfCurves sX sX : Set _), e w₀ = z := by
      have : z ∈ (N : Set (NumericalCurveClasses sX)) := hz
      rw [← hNimg] at this
      exact this
    rw [hdec] at hw₀
    obtain ⟨a, ⟨ha, haφ⟩, b, hb, rfl⟩ := Set.mem_add.mp hw₀
    have hhull : ∀ y ∈ Submodule.span NNReal (⋃₀ {R₀ : Set (RelativeNumericalCurveClasses sX sX) |
        IsNegativeRelativeExtremalRayOf sX sX D R₀}),
        e y ∈ PointedCone.hull ℝ (⋃₀ {R' | IsNegativeExtremalRayOf sX D R'}) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨R₀, hR₀, hxR₀⟩ := hx
        exact Submodule.subset_span ⟨e '' R₀, hneg_img R₀ hR₀, x, hxR₀, rfl⟩
      | zero => simp
      | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
      | smul r x _ hx =>
        rw [NNReal.smul_def, map_smul, ← NNReal.smul_def]
        exact Submodule.smul_mem _ r hx
    have haN : e a ∈ N := by
      have : e a ∈ e '' (relativeClosedConeOfCurves sX sX : Set _) := ⟨a, ha, rfl⟩
      rw [hNimg] at this
      exact this
    refine ⟨e a, haN, ?_, e b, hhull b hb, map_add _ _ _⟩
    have := hform a
    rw [← this]
    exact haφ

end ConeTheorem

section Coordinates

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  (sX : X ⟶ Spec (.of ℂ)) [AlgebraicGeometry.IsProjectiveVariety ℂ sX]

/-- `N₁(X)` has linear coordinates given by intersection with finitely many Cartier divisors. -/
private theorem exists_cartier_coordinates :
    ∃ (t : Set X.CartierDivisor) (_ : Fintype t) (Φ : NumericalCurveClasses sX ≃L[ℝ] (t → ℝ)),
      ∀ z (i : t), Φ z i = NumericalCurveClasses.intersectionNumber
        (KCartierDivisor.ofCartier ℝ (i : X.CartierDivisor)) z := by
  obtain ⟨hfd, -, hextc, hcoord, -⟩ :=
    NumericalCurveClasses.exists_cartier_coordinates_of_isProperVariety sX
  obtain ⟨t, -, ht, htspan⟩ := hextc ∅ (linearIndepOn_empty _ _)
  rw [Set.image_eq_range] at htspan
  obtain ⟨⟨Φ, hΦ⟩, -⟩ := hcoord (fun E : t => (E : X.CartierDivisor)) ht htspan
  haveI := hfd
  exact ⟨t, @Fintype.ofFinite _ ht.finite, Φ, fun z i => by
    simpa using congrArg (fun f : NumericalCurveClasses sX →ₗ[ℝ] t → ℝ => f z i) hΦ⟩

end Coordinates

section Ampleness

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  (sX : X ⟶ Spec (.of ℂ)) [AlgebraicGeometry.IsProjectiveVariety ℂ sX]

/-- If a Cartier divisor `L` is nonnegative on `NE̅(X)` and a `ℚ`-Cartier `D` is negative on every
nonzero class of `NE̅(X)` on which `L` vanishes, then `a L - D` is ample for some rational
`a > 0`. -/
private theorem exists_isAmple_smul_sub (L : Divisor X) (hLc : L.IsCartier) (D : QDivisor X)
    (hD : D.IsQCartier)
    (hnn : ∀ z ∈ closedConeOfCurves sX,
      0 ≤ QDivisor.curveForm sX (Divisor.toQDivisor L) (QDivisor.isQCartier_toQDivisor hLc) z)
    (hneg : ∀ z ∈ closedConeOfCurves sX, z ≠ 0 →
      QDivisor.curveForm sX (Divisor.toQDivisor L) (QDivisor.isQCartier_toQDivisor hLc) z = 0 →
        QDivisor.curveForm sX D hD z < 0) :
    ∃ a : ℚ, 0 < a ∧ (a • Divisor.toQDivisor L - D).IsAmple := by
  have hLQ := QDivisor.isQCartier_toQDivisor hLc
  set φ := QDivisor.curveForm sX D hD with hφdef
  set FL := QDivisor.curveForm sX (Divisor.toQDivisor L) hLQ with hFLdef
  set N := closedConeOfCurves sX with hNdef
  have hNclosed : IsClosed (N : Set (NumericalCurveClasses sX)) := by
    rw [hNdef, coe_closedConeOfCurves]; exact isClosed_closure
  obtain ⟨t, _, Φ, -⟩ := exists_cartier_coordinates sX
  obtain ⟨a₀, ha₀, ha₀lt⟩ := exists_pos_lt_mul Φ N hNclosed FL φ hnn hneg
  set a : ℕ := ⌈a₀⌉₊ + 1 with hadef
  have ha : (0 : ℚ) < a := by positivity
  have haa : a₀ ≤ (a : ℝ) := by
    simp only [hadef]; push_cast; linarith [Nat.le_ceil a₀]
  obtain ⟨m', hm', D', hD'eq, hD'c⟩ : ∃ m' : ℕ, 0 < m' ∧ ∃ D' : Divisor X,
      Divisor.toQDivisor D' = ((m' : ℤ) • D) ∧ D'.IsCartier := hD.exists_pos
  set W' : Divisor X := ((m' * a : ℕ) : ℤ) • L - D' with hW'def
  have hW'c : W'.IsCartier := (hLc.zsmul _).sub hD'c
  have hW'eq : Divisor.toQDivisor W' = (m' : ℚ) • ((a : ℚ) • Divisor.toQDivisor L - D) := by
    rw [hW'def, map_sub, map_zsmul, hD'eq, ← Int.cast_smul_eq_zsmul ℚ,
      ← Int.cast_smul_eq_zsmul ℚ]
    push_cast
    module
  have hW'Q := QDivisor.isQCartier_toQDivisor hW'c
  have hD'form : QDivisor.curveForm sX (Divisor.toQDivisor D')
      (QDivisor.isQCartier_toQDivisor hD'c) = (m' : ℝ) • φ := by
    have e : Divisor.toQDivisor D' = (m' : ℚ) • D := by
      rw [hD'eq, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast]
    rw [curveForm_congr sX e _ (e ▸ QDivisor.isQCartier_toQDivisor hD'c),
      curveForm_smul sX _ _ hD, Rat.cast_natCast]
  have hFW : ∀ z, QDivisor.curveForm sX (Divisor.toQDivisor W') hW'Q z =
      m' * (a * FL z) - m' * φ z := fun z => by
    rw [show QDivisor.curveForm sX (Divisor.toQDivisor W') hW'Q = _ from
      curveForm_toQDivisor_sub sX (hLc.zsmul _) hD'c hW'Q, curveForm_toQDivisor_zsmul sX _ hLc,
      hD'form, ← hFLdef]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    push_cast; ring
  have hW'amp : W'.IsAmple hW'c := isAmple_of_curveForm_pos sX W' hW'c hW'Q fun z hz hz0 => by
    rw [hFW]
    have h1 := ha₀lt z hz hz0
    have h2 := hnn z hz
    have h3 : a₀ * FL z ≤ a * FL z := mul_le_mul_of_nonneg_right haa h2
    have hm'0 : (0 : ℝ) < m' := by exact_mod_cast hm'
    nlinarith
  exact ⟨a, ha, m', hm', W', hW'eq, hW'c, hW'amp⟩

end Ampleness

/-! ### Nefness of `t L + F` for large `t` -/

section Nonneg

variable {ι : Type*} [Fintype ι] {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

/-- A linear form positive on the nonzero elements of a closed set `S` closed under nonnegative
scaling is bounded below on `S` by a positive multiple of the norm. -/
private theorem exists_pos_mul_norm_le_of_smul_mem (Φ : V ≃L[ℝ] (ι → ℝ)) {S : Set V}
    (hSc : IsClosed S) (hS : ∀ z ∈ S, ∀ c : ℝ, 0 ≤ c → c • z ∈ S) (α : V →ₗ[ℝ] ℝ)
    (hα : ∀ z ∈ S, z ≠ 0 → 0 < α z) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ z ∈ S, μ * ‖Φ z‖ ≤ α z := by
  set K := {z | z ∈ S ∧ ‖Φ z‖ = 1}
  have hK : IsCompact K := isCompact_unitSlice Φ hSc
  rcases K.eq_empty_or_nonempty with hK0 | hKne
  · refine ⟨1, one_pos, fun z hz => ?_⟩
    by_cases hz0 : z = 0
    · simp [hz0]
    · exact (Set.eq_empty_iff_forall_notMem.mp hK0 _
        (mem_unitSlice_of_smul_mem Φ hS hz hz0).2).elim
  obtain ⟨x₀, hx₀, hmin⟩ :=
    hK.exists_isMinOn hKne (continuous_of_coordinates Φ α).continuousOn
  have hx₀0 : x₀ ≠ 0 := fun h => by
    have := hx₀.2; rw [h, map_zero, norm_zero] at this; exact zero_ne_one this
  refine ⟨α x₀, hα x₀ hx₀.1 hx₀0, fun z hz => ?_⟩
  by_cases hz0 : z = 0
  · simp [hz0]
  obtain ⟨hr, hmem⟩ := mem_unitSlice_of_smul_mem Φ hS hz hz0
  have h1 : α x₀ ≤ α (‖Φ z‖⁻¹ • z) := hmin hmem
  rw [map_smul, smul_eq_mul] at h1
  have := mul_le_mul_of_nonneg_left h1 hr.le
  rwa [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul, mul_comm] at this

/-- **`t ℓ + F` is nonnegative on a cone with locally polyhedral negative part, for `t ≫ 0`.**
Let `N` be a closed pointed cone, `α > 0` on `N ∖ 0`, and suppose `N` is the sum of its part where
`φ ≥ 0` and the cone spanned by a family `𝓡` of rays of `N`, of which only finitely many are
`ψ`-negative for `ψ = φ + ε α`, `ε ≥ 0`. Let `ℓ ≥ 0` on `N` vanish on `N` only along the ray of a
`ψ`-negative class `v`, and let `F` vanish at `v`. Then `t ℓ + F ≥ 0` on `N` for every large `t`:
on the closed cone `N ∩ {ψ ≥ 0}` the form `ℓ` dominates the norm, and on the finitely many
`ψ`-negative rays other than that of `v` it is positive. -/
private theorem exists_forall_nonneg_mul_add (Φ : V ≃L[ℝ] (ι → ℝ)) (N : PointedCone ℝ V)
    (hN : IsClosed (N : Set V)) (φ α ℓ F : V →ₗ[ℝ] ℝ) (hα : ∀ z ∈ N, z ≠ 0 → 0 < α z)
    {ε : ℝ} (hε : 0 ≤ ε) {v : V} (hψv : φ v + ε * α v < 0) (hFv : F v = 0)
    (hℓ : ∀ z ∈ N, 0 ≤ ℓ z) (hℓ0 : ∀ z ∈ N, ℓ z = 0 → ∃ s : ℝ, 0 ≤ s ∧ s • v = z)
    (𝓡 : Set (Set V))
    (h𝓡 : ∀ R' ∈ 𝓡, R' ⊆ N ∧ ∃ g : V, R' = {w | ∃ c : ℝ, 0 ≤ c ∧ c • g = w})
    (hfin : {R' | R' ∈ 𝓡 ∧ ∀ u ∈ R', u ≠ 0 → φ u + ε * α u < 0}.Finite)
    (hdec : ∀ z ∈ N, ∃ a ∈ N, 0 ≤ φ a ∧ ∃ b ∈ PointedCone.hull ℝ (⋃₀ 𝓡), z = a + b) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ∀ z ∈ N, 0 ≤ t * ℓ z + F z := by
  classical
  set ψ : V →ₗ[ℝ] ℝ := φ + ε • α with hψdef
  have hψ : ∀ z, ψ z = φ z + ε * α z := fun z => by simp [hψdef]
  have hα0 : ∀ z ∈ N, 0 ≤ α z := fun z hz => by
    by_cases h0 : z = 0
    · simp [h0]
    · exact (hα z hz h0).le
  -- the part of `N` where `ψ ≥ 0`
  set S : Set V := {z | z ∈ N ∧ 0 ≤ ψ z} with hSdef
  have hSc : IsClosed S :=
    hN.inter (isClosed_le continuous_const (continuous_of_coordinates Φ ψ))
  have hSs : ∀ z ∈ S, ∀ c : ℝ, 0 ≤ c → c • z ∈ S := fun z hz c hc =>
    ⟨N.smul_mem hc hz.1, by rw [map_smul, smul_eq_mul]; exact mul_nonneg hc hz.2⟩
  have hℓS : ∀ z ∈ S, z ≠ 0 → 0 < ℓ z := by
    intro z hz hz0
    rcases (hℓ z hz.1).lt_or_eq with h | h
    · exact h
    obtain ⟨s, hs, rfl⟩ := hℓ0 z hz.1 h.symm
    have h1 := hz.2
    rw [map_smul, smul_eq_mul, hψ] at h1
    have hs0 : s = 0 := by
      by_contra hs0
      have := mul_neg_of_pos_of_neg (lt_of_le_of_ne hs (Ne.symm hs0)) hψv
      linarith
    exact absurd (by rw [hs0, zero_smul]) hz0
  obtain ⟨μ, hμ, hμS⟩ := exists_pos_mul_norm_le_of_smul_mem Φ hSc hSs ℓ hℓS
  -- a bound for `F` by the norm
  set F' : (ι → ℝ) →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap (F ∘ₗ (Φ.symm : (ι → ℝ) →ₗ[ℝ] V)) with hF'def
  have hF' : ∀ z, |F z| ≤ ‖F'‖ * ‖Φ z‖ := fun z => by
    have := F'.le_opNorm (Φ z)
    simpa [F', Real.norm_eq_abs] using this
  -- generators of the finitely many `ψ`-negative rays
  set 𝓕 := {R' | R' ∈ 𝓡 ∧ ∀ u ∈ R', u ≠ 0 → φ u + ε * α u < 0} with h𝓕def
  choose gen hgen using fun R' (hR' : R' ∈ 𝓡) => (h𝓡 R' hR').2
  let bd : Set V → ℝ := fun R' => if hR' : R' ∈ 𝓡 then
    (if 0 < ℓ (gen R' hR') then -F (gen R' hR') / ℓ (gen R' hR') else 0) else 0
  obtain ⟨T₂, hT₂⟩ := (hfin.image bd).bddAbove
  refine ⟨max (‖F'‖ / μ) T₂, fun t ht z hz => ?_⟩
  have ht1 : ‖F'‖ / μ ≤ t := le_trans (le_max_left _ _) ht
  have ht2 : T₂ ≤ t := le_trans (le_max_right _ _) ht
  have ht0 : 0 ≤ t := le_trans (div_nonneg (norm_nonneg _) hμ.le) ht1
  set G : Set V := {x | 0 ≤ t * ℓ x + F x} with hGdef
  have hG0 : (0 : V) ∈ G := by simp [G]
  have hGadd : ∀ x ∈ G, ∀ y ∈ G, x + y ∈ G := fun x hx y hy => by
    simp only [G, Set.mem_setOf_eq, map_add] at hx hy ⊢
    linarith
  have hGsmul : ∀ x ∈ G, ∀ c : ℝ, 0 ≤ c → c • x ∈ G := fun x hx c hc => by
    simp only [G, Set.mem_setOf_eq, map_smul, smul_eq_mul] at hx ⊢
    nlinarith
  have hSG : ∀ x ∈ S, x ∈ G := by
    intro x hx
    have h1 := hμS x hx
    have h2 := hF' x
    have h3 : ‖F'‖ ≤ t * μ := by rwa [div_le_iff₀ hμ] at ht1
    have h4 : 0 ≤ ‖Φ x‖ := norm_nonneg _
    have e1 := mul_le_mul_of_nonneg_left h1 ht0
    have e2 := mul_le_mul_of_nonneg_right h3 h4
    have e3 := neg_abs_le (F x)
    show 0 ≤ t * ℓ x + F x
    nlinarith
  have hgenG : ∀ R' (hR' : R' ∈ 𝓡), R' ∈ 𝓕 → gen R' hR' ∈ G := by
    intro R' hR' hR'F
    have hgN : gen R' hR' ∈ N :=
      (h𝓡 R' hR').1 ((Set.ext_iff.mp (hgen R' hR') (gen R' hR')).mpr
        ⟨1, zero_le_one, one_smul _ _⟩)
    show 0 ≤ t * ℓ (gen R' hR') + F (gen R' hR')
    rcases (hℓ _ hgN).lt_or_eq with hpos | h0
    · have hb : bd R' ≤ T₂ := hT₂ ⟨R', hR'F, rfl⟩
      simp only [bd, dif_pos hR', if_pos hpos] at hb
      have := (div_le_iff₀ hpos).mp (hb.trans ht2)
      linarith
    · obtain ⟨s, -, hs⟩ := hℓ0 _ hgN h0.symm
      rw [← h0, ← hs, map_smul, hFv, smul_zero]
      simp
  have hrayG : ∀ x ∈ ⋃₀ 𝓡, x ∈ G := by
    rintro x ⟨R', hR', hx⟩
    have hxN : x ∈ N := (h𝓡 R' hR').1 hx
    by_cases hψx : 0 ≤ ψ x
    · exact hSG x ⟨hxN, hψx⟩
    push Not at hψx
    have hx0 : x ≠ 0 := fun h => by rw [h, map_zero] at hψx; exact lt_irrefl _ hψx
    rw [hgen R' hR'] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    have hψg : ψ (gen R' hR') < 0 := by
      rw [map_smul, smul_eq_mul] at hψx
      exact neg_of_mul_neg_right hψx hc
    have hR'F : R' ∈ 𝓕 := by
      refine ⟨hR', fun u hu hu0 => ?_⟩
      rw [hgen R' hR'] at hu
      obtain ⟨d, hd, rfl⟩ := hu
      have hd0 : 0 < d := hd.lt_of_ne (by rintro rfl; exact hu0 (zero_smul _ _))
      rw [← hψ, map_smul, smul_eq_mul]
      exact mul_neg_of_pos_of_neg hd0 hψg
    exact hGsmul _ (hgenG R' hR' hR'F) c hc
  have hhullG : ∀ x ∈ PointedCone.hull ℝ (⋃₀ 𝓡), x ∈ G := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hrayG x hx
    | zero => exact hG0
    | add x y _ _ hx hy => exact hGadd x hx y hy
    | smul r x _ hx => exact hGsmul x hx r r.2
  obtain ⟨a, haN, hφa, b', hb', rfl⟩ := hdec z hz
  have haS : a ∈ S := ⟨haN, by rw [hψ]; exact add_nonneg hφa (mul_nonneg hε (hα0 a haN))⟩
  exact hGadd _ (hSG a haS) _ (hhullG b' hb')

end Nonneg

/-! ### Basepoint free linear systems -/

section Generation

variable {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]

/-- The global section of `𝒪_X(W)` defined by an element of `H⁰(X, 𝒪_X(W)) ⊆ K(X)`. -/
private noncomputable def globalSection (W : Divisor X) (σ : W.divisorialSubmodule ⊤) :
    W.divisorialSheaf.sections :=
  PresheafOfModules.sectionsMk (M := W.divisorialSheaf.val)
    (fun U => W.divisorialRestrict (homOfLE le_top : U.unop ⟶ ⊤) σ)
    fun _ _ _ => Subtype.ext (funext fun _ => rfl)

private theorem globalSection_eval_top (W : Divisor X) (σ : W.divisorialSubmodule ⊤) :
    (globalSection W σ).eval (Opposite.op ⊤) = σ :=
  Subtype.ext (funext fun _ => rfl)

/-- **A basepoint free linear system generates its sheaf.** If the base locus of `|W|` is empty,
the global sections of `𝒪_X(W)` generate it: near a point `x` off the zero divisor of a global
section `σ`, every local section `t` is `(t / σ) · σ` with `t / σ` regular by algebraic Hartogs,
since `div (t / σ) ≥ -(σ)₀` and `(σ)₀` misses `x`. -/
private theorem isGeneratedByGlobalSections_of_isBasepointFree (W : Divisor X)
    (hW : W.IsBasepointFree) : SheafOfModules.IsGeneratedByGlobalSections W.divisorialSheaf := by
  classical
  refine ⟨⟨W.divisorialSubmodule ⊤, globalSection W,
    (AlgebraicGeometry.generates_iff_stalkwise_generates X.ringCatSheaf W.divisorialSheaf
      (globalSection W)).mpr ?_⟩⟩
  intro x
  rw [Submodule.eq_top_iff']
  intro z
  obtain ⟨U, hxU, t, rfl⟩ := TopCat.Presheaf.germ_exist W.divisorialSheaf.val.presheaf z
  -- a global section whose zero divisor misses `x`
  have hx : x ∉ (W.baseLocus : Set X) := by
    rw [show W.baseLocus = ⊥ from hW]
    exact fun h => h
  rw [Divisor.mem_baseLocus_iff] at hx
  push Not at hx
  obtain ⟨σ, hσ, hxσ⟩ := hx
  set Zσ := W.zeroDivisor σ hσ with hZσ
  let V : X.Opens := U ⊓ ⟨(Zσ.supp : Set X)ᶜ, Zσ.supp.isClosed.isOpen_compl⟩
  have hxV : x ∈ V := ⟨hxU, hxσ⟩
  have hVU : V ≤ U := inf_le_left
  set u := (Divisor.isUnit_sectionToRationalFunctions hσ).unit with hu
  have hu_apply : ∀ Z, (u : RationalFunctions X) Z = σ.1 ⟨Z, trivial⟩ := fun _ => rfl
  -- the quotient `t / σ` on `V`
  let ψ : ToType ((rationalFunctionsPresheaf X).obj (Opposite.op V)) :=
    (rationalFunctionsPresheaf X).map (homOfLE hVU).op t.1 *
      (rationalFunctionsPresheaf X).map (homOfLE le_top).op
        ((rationalFunctionsPresheafTopEquiv X).symm ((u⁻¹ : (RationalFunctions X)ˣ) :
          RationalFunctions X))
  have hψ : (0 : Divisor X).IsDivisorialSection V ψ := by
    intro E hE
    have hcoeff : Zσ.coeff E = 0 := by
      by_contra hne
      obtain ⟨y, hyE, hyV⟩ := hE
      exact hyV.2 (DivisorWithCoeffs.support_subset_supp hne hyE)
    have ht := t.2 E (hE.mono (Set.inter_subset_inter_right _ hVU))
    have hZE : Zσ.coeff E = E.ord u + W.coeff E := rfl
    have hu' : E.OrdGE (W.coeff E)
        (((u⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) E.component) := by
      refine Or.inr (le_of_eq ?_)
      rw [PrimeDivisor.valuation_component, PrimeDivisor.ord_inv]
      congr 1
      omega
    have := ht.mul hu'
    rw [neg_add_cancel] at this
    exact this
  obtain ⟨r, hr⟩ := Divisor.IsDivisorialSection.exists_eq hψ
  -- `t = r σ` on `V`
  have heq : W.divisorialSheaf.presheaf.map (homOfLE hVU).op t =
      r • W.divisorialSheaf.presheaf.map (homOfLE le_top).op
        ((globalSection W σ).eval (Opposite.op ⊤)) := by
    rw [globalSection_eval_top]
    apply Subtype.ext
    funext Z
    change ((rationalFunctionsPresheaf X).map (homOfLE hVU).op t.1) Z =
      X.presheaf.germ V _ Z.2 r * σ.1 ⟨Z.1, trivial⟩
    have h1 := congrFun hr Z
    rw [toRationalFunctionsPresheaf_app_apply] at h1
    rw [h1]
    change _ = ((rationalFunctionsPresheaf X).map (homOfLE hVU).op t.1) Z *
      ((u⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z.1 * (u : RationalFunctions X) Z.1
    rw [mul_assoc, ← Pi.mul_apply (((u⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X)),
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Pi.one_apply, mul_one]
  have hgerm : TopCat.Presheaf.germ W.divisorialSheaf.val.presheaf U x hxU t =
      TopCat.Presheaf.germ X.ringCatSheaf.obj V x hxV r •
        (TopCat.Presheaf.Γgerm W.divisorialSheaf.val.presheaf x).hom
          ((globalSection W σ).eval (Opposite.op ⊤)) := by
    rw [← TopCat.Presheaf.germ_res_apply W.divisorialSheaf.val.presheaf (homOfLE hVU) x hxV t]
    erw [heq, PresheafOfModules.germ_ringCat_smul]
    congr 1
    exact TopCat.Presheaf.Γgerm_res_apply W.divisorialSheaf.val.presheaf x hxV _
  rw [hgerm]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ, rfl⟩)

end Generation

/-! ### The Stein factorisation of a free divisor -/

private theorem isLocalEquationAt_zero_one (Z : Scheme.{0}) (x : Z) :
    MMP.Intersection.IsLocalEquationAt (0 : Z.CartierDivisor) x 1 :=
  ⟨⊤, trivial, 1, MMP.Intersection.isLocalEquationOn_one _, by simp⟩

/-- The zero Cartier divisor pulls back to the zero Cartier divisor. -/
private theorem isPullback_zero {X Y : Scheme.{0}} (g : Y ⟶ X) :
    MMP.Intersection.IsPullback g (0 : X.CartierDivisor) 0 := by
  refine ⟨fun η _ => ?_, fun y => ⟨1, 1,
    ⟨1, isLocalEquationAt_zero_one _ _, MMP.Intersection.isFraction_one_one_one _⟩,
    ?_, ?_, 1, isLocalEquationAt_zero_one _ _, ?_⟩⟩
  · simp [MMP.Intersection.cartierSupport]
  · simp
  · simp
  · simpa only [map_one] using MMP.Intersection.isFraction_one_one_one y

/-- The projection of `ℙ(G) = Proj_Z(Sym G)` is proper when `G` is quasi-coherent of finite
type. -/
private theorem isProper_relativeProj_toBase {Z : Scheme.{0}} (G : Z.Modules) [G.IsQuasicoherent]
    [G.IsFiniteType] :
    IsProper (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
      (Stacks.SymGraded.schemeSheafGradedAlgebra G
        (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent G))).toBase := by
  have h := Stacks.RelativeProj.isProper_projectiveBundleToBase_of_isFiniteType Z G
  rw [← Stacks.RelativeProj.bundlePresentationIso_inv_comp_toBase G] at h
  exact (MorphismProperty.cancel_left_of_respectsIso @IsProper _ _).mp h

/-- The Stein step: a Stein factorization of the morphism `Φ : X ⟶ P` defined by `mL`
supplies the data of `exists_of_steinFactor`. -/
private theorem exists_steinFactor {k : Type} [Field k] {X P : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sX] (M : X.CartierDivisor)
    (πP : P ⟶ Spec (.of k)) (hπ : IsProper πP) (Φ : X ⟶ P) [IsProper Φ] (hΦ : Φ ≫ πP = sX)
    (hall : ∀ (YL : Scheme.{0}) (ρ : X ⟶ YL) (τ : YL ⟶ P),
      Stacks.SteinFactorization.IsSteinFactorization Φ ρ τ →
        MMP.Mori.IsNormalVariety k (τ ≫ πP ≫ 𝟙 (Spec (.of k))) ∧
          (∀ U : YL.Opens, IsIso (ρ.app U)) ∧ IsFinite τ ∧
          ∃ (_ : IsLocallyNoetherian YL) (_ : IsNormal YL) (_ : CompactSpace YL)
            (A : Divisor YL), MMP.Flips.IsRelativelyAmpleCartier (τ ≫ πP) A ∧
            Nonempty (MMP.CartierDivisor.sheaf M ≅
              (Scheme.Modules.pullback ρ).obj A.divisorialSheaf)) :
    ∃ (Z : Scheme.{0}) (sZ : Z ⟶ Spec (.of k)) (c : X ⟶ Z) (_ : MMP.Mori.IsNormalVariety k sZ)
      (_ : c ≫ sZ = sX) (_ : IsProper c) (_ : Surjective c) (_ : IsIso c.c) (_ : IsProper sZ)
      (_ : IsLocallyNoetherian Z) (_ : IsNormal Z) (_ : CompactSpace Z)
      (_ : ∀ U : Z.Opens, IsIso (c.app U)) (A : Divisor Z),
      MMP.Flips.IsRelativelyAmpleCartier sZ A ∧
        Nonempty (MMP.CartierDivisor.sheaf M ≅
          (Scheme.Modules.pullback c).obj A.divisorialSheaf) := by
  haveI := hπ
  obtain ⟨Z, c, τ, ⟨hSt⟩, hcp, hcs, hcapp, -, hτ, -, -, -, -, -⟩ :=
    MMP.Resolution.Bridges.exists_steinFactorization_of_isVariety sX (πP ≫ 𝟙 _) Φ
      (by rw [Category.comp_id, hΦ])
  obtain ⟨hZn, -, -, i1, i2, i3, A, hA, hMA⟩ := hall Z c τ hSt
  have hZn' : MMP.Mori.IsNormalVariety k (τ ≫ πP) := by
    simpa only [Category.comp_id] using hZn
  exact ⟨Z, τ ≫ πP, c, hZn', by rw [← Category.assoc, hSt.comp, hΦ], hcp, hcs,
    hSt.structureSheaf, inferInstance, i1, i2, i3, hcapp, A, hA, hMA⟩

/-! ### Free Cartier divisors trivial on the contracted curves descend -/

section Descent

/-- **A free Cartier divisor of degree zero on the curves contracted by `c` is a pull-back from
`Z`.** The morphism `X ⟶ ℙ` defined by the free divisor `G` has a Stein factorisation
`ρ : X ⟶ Z'` with an ample `A` on `Z'` and `𝒪_X(G) ≅ ρ^* 𝒪(A)`; a curve contracted by `c` has
`A`-degree zero, so it is contracted by `ρ`, and rigidity factors `ρ = u ∘ c`. -/
private theorem mem_pullbackNumericalClasses_of_isGeneratedByGlobalSections
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (c : X ⟶ Z) (hcomp : c ≫ sZ = sX) (hcproj : IsProjectiveMorphism c) [Surjective c]
    [IsIso c.c] (G : X.CartierDivisor)
    (hG : SheafOfModules.IsGeneratedByGlobalSections (MMP.CartierDivisor.sheaf G))
    (hdeg : ∀ C : ProperCurve sX, C.IsContractedBy c →
      C.degree ℂ (MMP.CartierDivisor.sheaf G) = 0) :
    numericalDivisorClass sX (KCartierDivisor.ofCartier ℝ G) ∈ pullbackNumericalClasses sX c := by
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX := hX
  haveI : AlgebraicGeometry.IsVariety ℂ sX := hX.toIsVariety
  haveI : IsProper sX := isProper_of_isProjectiveMorphism _ hX.isProjective
  have hXn : MMP.Mori.IsNormalVariety ℂ sX := ⟨hX.toIsVariety, inferInstance⟩
  haveI : AlgebraicGeometry.IsVariety ℂ (𝟙 (Spec (.of ℂ))) := ⟨⟩
  have hfree : IsRelativelyFreeCartier sX G :=
    isRelativelyFreeCartier_of_isGeneratedByGlobalSections_add_pullback (sY := 𝟙 _)
      (Category.comp_id sX) G (isPullback_zero sX) (by rwa [add_zero])
  have key := IsRelativelyFreeCartier.steinFactor_isRelativelyAmpleCartier sX (𝟙 _) hXn
    (inferInstance : AlgebraicGeometry.IsVariety ℂ (𝟙 (Spec (.of ℂ)))) sX
    (Category.comp_id sX) G hfree
  dsimp only at key
  obtain ⟨⟨Φ, hΦ, e, hdef⟩, hall⟩ := key
  obtain ⟨hΦp, hall⟩ := hall Φ hΦ e hdef
  haveI : ((Scheme.Modules.pushforward sX).obj
      (MMP.CartierDivisor.sheaf G)).IsQuasicoherent :=
    ProperCoherentFiniteType.isQuasicoherent_pushforward sX _ inferInstance
  haveI : ((Scheme.Modules.pushforward sX).obj
      (MMP.CartierDivisor.sheaf G)).IsFiniteType :=
    (AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward sX
      (MMP.CartierDivisor.sheaf G)).isFiniteType
  obtain ⟨Z', sZ', ρ, hZ'n, hρcomp, _, _, _, _, _, _, _, -, A, hA, ⟨eG⟩⟩ :=
    exists_steinFactor sX G _ (isProper_relativeProj_toBase _) Φ hΦ fun YL ρ τ hS => by
      obtain ⟨h1, h2, h3, i1, i2, i3, A, hA, -, hM⟩ := hall YL ρ τ hS
      exact ⟨h1, h2, h3, i1, i2, i3, A, hA, hM⟩
  haveI : AlgebraicGeometry.IsVariety ℂ sZ' := hZ'n.1
  haveI hAinv := hA.1.isInvertibleModule_divisorialSheaf
  have hZ'proj : IsProjective sZ' :=
    MMP.isProjective_of_isProper_of_isRelativelyAmple sZ' A.divisorialSheaf
      (isRelativelyAmple_of_isRelativelyAmpleCartier hA)
  have hZ'p : MMP.Mori.IsProjectiveVariety ℂ sZ' :=
    (isProjectiveVariety_iff_isProjective' ℂ sZ').mpr ⟨inferInstance, hZ'proj⟩
  have hamp := isAmple_of_isRelativelyAmpleCartier sZ' hA
  have hvert : ∀ C : ProperCurve sX, C.IsContractedBy c → C.IsContractedBy ρ := fun C hC =>
    MMP.ProgramBaseChange.isContractedBy_of_degree_pullback_eq_zero ρ hρcomp _ hamp C
      ((degreeOn_eq_of_iso ℂ sX C.ι C.dim_le eG).symm.trans (hdeg C hC))
  obtain ⟨u, hu, -⟩ :=
    existsUnique_comp_eq_of_isContractedBy hX hZ hZ'p hcproj hcomp hρcomp hvert
  haveI : SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2
      ((Scheme.Modules.pullback u).obj A.divisorialSheaf) :=
    Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback u.toLRSHom.toShHom _
  exact Submodule.subset_span ⟨G, (Scheme.Modules.pullback u).obj A.divisorialSheaf,
    inferInstance, ⟨eG ≪≫ (Scheme.Modules.pullbackCongr hu.symm).app _ ≪≫
      ((Scheme.Modules.pullbackComp c u).app _).symm⟩, rfl⟩

end Descent

/-! ### Numerical classes of divisors -/

section NumericalDivisorClasses

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}

private theorem intersectionNumber_add (D D' : KCartierDivisor ℝ X) :
    NumericalCurveClasses.intersectionNumber (sX := sX) (D + D') =
      NumericalCurveClasses.intersectionNumber D + NumericalCurveClasses.intersectionNumber D' :=
  Submodule.linearMap_qext _ (LinearMap.ext fun Z => by
    simp [NumericalCurveClasses.intersectionNumber])

private theorem intersectionNumber_smul (r : ℝ) (D : KCartierDivisor ℝ X) :
    NumericalCurveClasses.intersectionNumber (sX := sX) (r • D) =
      r • NumericalCurveClasses.intersectionNumber D :=
  Submodule.linearMap_qext _ (LinearMap.ext fun Z => by
    simp [NumericalCurveClasses.intersectionNumber])

private theorem intersectionNumber_sub (D D' : KCartierDivisor ℝ X) :
    NumericalCurveClasses.intersectionNumber (sX := sX) (D - D') =
      NumericalCurveClasses.intersectionNumber D - NumericalCurveClasses.intersectionNumber D' := by
  rw [sub_eq_add_neg, intersectionNumber_add, ← neg_one_smul ℝ D', intersectionNumber_smul,
    neg_one_smul, sub_eq_add_neg]

/-- Numerical classes of `ℝ`-Cartier divisors are determined by their intersection forms. -/
private theorem numericalDivisorClass_eq_of_intersectionNumber_eq {D D' : KCartierDivisor ℝ X}
    (h : NumericalCurveClasses.intersectionNumber (sX := sX) D =
      NumericalCurveClasses.intersectionNumber D') :
    numericalDivisorClass sX D = numericalDivisorClass sX D' := by
  refine (Submodule.Quotient.eq _).mpr (mem_numericallyTrivialDivisors.mpr fun C => ?_)
  have := congrArg (fun f => f (OneCycle.numericalClass sX (C.cycle ℝ)))
    ((intersectionNumber_sub D D').trans (sub_eq_zero.mpr h))
  simpa [NumericalCurveClasses.intersectionNumber_numericalClass] using this

end NumericalDivisorClasses

/-! ### Surjectivity of a contraction -/

section Surjective

/-- A morphism to an integral scheme all of whose maps on sections are isomorphisms is
dominant: over an open set missing its image, the sections upstairs vanish. -/
private theorem isDominant_of_forall_isIso_app {V W : Scheme.{0}} (g : V ⟶ W) [IsIntegral W]
    (hg : ∀ U : W.Opens, IsIso (g.app U)) : IsDominant g := by
  constructor
  by_contra hd
  rw [DenseRange, dense_iff_closure_eq] at hd
  let U' : W.Opens := ⟨(closure (Set.range g))ᶜ, isClosed_closure.isOpen_compl⟩
  have hbot : g ⁻¹ᵁ U' = ⊥ := by
    ext x
    exact iff_of_false (fun hx => hx (subset_closure ⟨x, rfl⟩)) id
  have : Nonempty U' := (Set.nonempty_compl.mpr hd).to_subtype
  have : Subsingleton Γ(V, g ⁻¹ᵁ U') := by rw [hbot]; infer_instance
  exact not_subsingleton Γ(W, U')
    (asIso (g.app U')).commRingCatIsoToRingEquiv.injective.subsingleton

/-- A proper morphism to an integral scheme all of whose maps on sections are isomorphisms is
surjective. -/
private theorem surjective_of_isIso_app {V W : Scheme.{0}} (g : V ⟶ W) [IsIntegral W]
    [IsProper g] (hg : ∀ U : W.Opens, IsIso (g.app U)) : Function.Surjective g :=
  have := isDominant_of_forall_isIso_app g hg
  g.surjective

end Surjective

/-! ### Descent of divisors trivial on the contracted ray -/

/-- **A Cartier divisor trivial on the contracted ray is numerically a pull-back** (KM 3.7(4)).
Let `c : X ⟶ Z` contract exactly the curves with class on the ray `ℝ≥0 · w₀`, let `L` be nef with
`NE̅(X) ∩ L^⊥ = ℝ≥0 · w₀`, `(K + B) · w₀ < 0`, and let `m L` be numerically the free Cartier
divisor `Lc`, a pull-back from `Z`. If `W'` is Cartier with `(W' · w₀) = 0` and `n L + W'` is nef
on `NE̅(X)` for `n ≫ 0`, then `W = n L + W'` is nef and `W - (K + B)/a` is ample, so a multiple
`k W` is free by the base point free theorem; trivial on the curves contracted by `c`, it is a
pull-back from `Z`, hence so is `W' ≡ (1/k)(k W) - (n/m) Lc`. -/
private theorem mem_pullbackNumericalClasses_of_curveForm_eq_zero
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hdim : topologicalKrullDim X = 4)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4)
    {B : QDivisor X} (hB : MMP.Intersection.IsLogCanonicalPair sX B)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (c : X ⟶ Z) (hcomp : c ≫ sZ = sX)
    (hcproj : IsProjectiveMorphism c) [Surjective c] [IsIso c.c] {w₀ : NumericalCurveClasses sX}
    (hray : ∀ C : ProperCurve sX, C.IsContractedBy c → ∃ t : ℝ, 0 ≤ t ∧
      t • w₀ = OneCycle.numericalClass sX (C.cycle ℝ))
    {L : Divisor X} (hLnef : L.IsNef ℂ sX) (hLQ : (Divisor.toQDivisor L).IsQCartier)
    (hℓ : ∀ z ∈ closedConeOfCurves sX, 0 ≤ QDivisor.curveForm sX (Divisor.toQDivisor L) hLQ z)
    (hℓ0 : ∀ z ∈ closedConeOfCurves sX, QDivisor.curveForm sX (Divisor.toQDivisor L) hLQ z = 0 →
      ∃ s : ℝ, 0 ≤ s ∧ s • w₀ = z)
    (hℓw₀ : QDivisor.curveForm sX (Divisor.toQDivisor L) hLQ w₀ = 0)
    (hD : (Divisor.toQDivisor K + B).IsQCartier)
    (hneg : QDivisor.curveForm sX (Divisor.toQDivisor K + B) hD w₀ < 0)
    {m : ℕ} (hm : 0 < m) (Lc : X.CartierDivisor)
    (hLcform : NumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ Lc) =
      (m : ℝ) • QDivisor.curveForm sX (Divisor.toQDivisor L) hLQ)
    (hLcP : numericalDivisorClass sX (KCartierDivisor.ofCartier ℝ Lc) ∈
      pullbackNumericalClasses sX c)
    {W' : Divisor X} (hW' : W'.IsCartier)
    (hW'0 : QDivisor.curveForm sX (Divisor.toQDivisor W') (QDivisor.isQCartier_toQDivisor hW') w₀ =
      0)
    (hT : ∃ T : ℝ, ∀ s : ℝ, T ≤ s → ∀ z ∈ closedConeOfCurves sX,
      0 ≤ s * QDivisor.curveForm sX (Divisor.toQDivisor L) hLQ z +
        QDivisor.curveForm sX (Divisor.toQDivisor W') (QDivisor.isQCartier_toQDivisor hW') z)
    {x : KCartierDivisor ℝ X}
    (hx : NumericalCurveClasses.intersectionNumber x =
      QDivisor.curveForm sX (Divisor.toQDivisor W') (QDivisor.isQCartier_toQDivisor hW')) :
    numericalDivisorClass sX x ∈ pullbackNumericalClasses sX c := by
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX := hX
  haveI : AlgebraicGeometry.IsVariety ℂ sZ := hZ.toIsVariety
  set D := Divisor.toQDivisor K + B with hDdef
  set P := pullbackNumericalClasses sX c with hPdef
  set ℓ := QDivisor.curveForm sX (Divisor.toQDivisor L) hLQ with hℓdef
  set F := QDivisor.curveForm sX (Divisor.toQDivisor W') (QDivisor.isQCartier_toQDivisor hW')
    with hFdef
  set N := closedConeOfCurves sX with hNdef
  have hclassN : ∀ C : ProperCurve sX, OneCycle.numericalClass sX (C.cycle ℝ) ∈ N := fun C =>
    coneOfCurves_le_closedConeOfCurves sX (numericalClass_cycle_mem_coneOfCurves sX C)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨T, hT⟩ := hT
  obtain ⟨n, hn⟩ := exists_nat_ge (T + 1)
  set W := n • L + W' with hWdef
  have hWc : W.IsCartier := (hLnef.1.nsmul n).add hW'
  have hWQ := QDivisor.isQCartier_toQDivisor hWc
  have hWform : QDivisor.curveForm sX (Divisor.toQDivisor W) hWQ = (n : ℝ) • ℓ + F := by
    refine (curveForm_toQDivisor_add sX (hLnef.1.nsmul n) hW' hWQ).trans ?_
    rw [curveForm_toQDivisor_nsmul sX n hLnef.1]
  have hWnn : ∀ z ∈ N, 0 ≤ QDivisor.curveForm sX (Divisor.toQDivisor W) hWQ z := fun z hz => by
    rw [hWform]
    have := hT n (by linarith) z hz
    simpa using this
  have hWnef : W.IsNef ℂ sX := isNef_of_forall_properCurve sX W hWc hWQ fun C => hWnn _ (hclassN C)
  obtain ⟨a', ha', hamp'⟩ := exists_isAmple_smul_sub sX W hWc D hD hWnn (fun z hz hz0 h0 => by
    rw [hWform] at h0
    have h1 := hT (n - 1) (by linarith) z hz
    have h2 := hℓ z hz
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at h0
    have hℓz : ℓ z = 0 := by nlinarith
    obtain ⟨s, hs, rfl⟩ := hℓ0 z hz hℓz
    have hs0 : 0 < s := hs.lt_of_ne (by rintro rfl; exact hz0 (zero_smul _ _))
    rw [map_smul, smul_eq_mul]
    exact mul_neg_of_pos_of_neg hs0 hneg)
  obtain ⟨k₀, hk₀⟩ := MMP.Intersection.IsLogCanonicalPair.exists_isBasepointFree_nsmul sX hX hdim
    hB hK hWnef ha' hamp'
  set k := k₀ + 1 with hkdef
  have hkW : (k • W).IsCartier := hWc.nsmul k
  haveI := hkW.isInvertibleModule_divisorialSheaf
  obtain ⟨Gk, ⟨eG⟩⟩ :=
    MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf (k • W).divisorialSheaf
  obtain ⟨σ⟩ := isGeneratedByGlobalSections_of_isBasepointFree (k • W) (hk₀ k (by omega))
  have hGgen : SheafOfModules.IsGeneratedByGlobalSections
      (MMP.CartierDivisor.sheaf Gk) :=
    ⟨SheafOfModules.GeneratingSections.equivOfIso eG σ⟩
  have hGform : NumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ Gk) =
      (k : ℝ) • ((n : ℝ) • ℓ + F) := by
    rw [← curveForm_toQDivisor_eq_intersectionNumber sX (k • W) hkW
      (QDivisor.isQCartier_toQDivisor hkW) Gk eG, curveForm_toQDivisor_nsmul sX k hWc, hWform]
  have hGP : numericalDivisorClass sX (KCartierDivisor.ofCartier ℝ Gk) ∈ P :=
    mem_pullbackNumericalClasses_of_isGeneratedByGlobalSections hX hZ c hcomp hcproj Gk hGgen
      fun C hC => by
        obtain ⟨s, -, hs⟩ := hray C hC
        have h1 := intersectionNumber_numericalClass_cycle sX Gk C
        rw [hGform, ← hs] at h1
        simp only [map_smul, LinearMap.smul_apply, LinearMap.add_apply, hℓw₀, hW'0,
          smul_zero, add_zero] at h1
        exact_mod_cast h1.symm
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hxeq : numericalDivisorClass sX x =
      numericalDivisorClass sX ((k : ℝ)⁻¹ • KCartierDivisor.ofCartier ℝ Gk -
        ((n : ℝ) / m) • KCartierDivisor.ofCartier ℝ Lc) := by
    apply numericalDivisorClass_eq_of_intersectionNumber_eq
    rw [intersectionNumber_sub, intersectionNumber_smul, intersectionNumber_smul, hGform,
      hLcform, hx]
    refine LinearMap.ext fun z => ?_
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
    have h1 : (n : ℝ) / m * (m * ℓ z) = n * ℓ z := by field_simp
    rw [inv_mul_cancel_left₀ hk0, h1]
    ring
  rw [hxeq, map_sub, map_smul, map_smul]
  exact P.sub_mem (P.smul_mem _ hGP) (P.smul_mem _ hLcP)

/-! ### The relative Picard number -/

/-- **The relative Picard number of the contraction is one** (KM 3.7(4), numerically). The form
`d ↦ (d · C₀)` on `N¹(X)` is onto and kills `c^* N¹(Z)`. Its kernel is spanned by classes of
Cartier divisors `W'` with `(W' · C₀) = 0`; for such a `W'` the cone theorem makes `n L + W'` nef
and `n L + W' - (K + B)` ample, a multiple `k (n L + W')` is free by the base point free theorem,
and, being trivial on the curves contracted by `c`, it is a pull-back from `Z`, like `m L`. -/
private theorem relativePicardNumberN1_eq_one
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hdim : topologicalKrullDim X = 4)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4)
    {B : QDivisor X} (hB : MMP.Intersection.IsLogCanonicalPair sX B)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (c : X ⟶ Z) (hcomp : c ≫ sZ = sX)
    (hcproj : IsProjectiveMorphism c) [Surjective c] [IsIso c.c]
    (C₀ : ProperCurve sX) (hC₀ : C₀.IsContractedBy c)
    (hw₀ : OneCycle.numericalClass sX (C₀.cycle ℝ) ≠ 0)
    (hray : ∀ C : ProperCurve sX, C.IsContractedBy c → ∃ t : ℝ, 0 ≤ t ∧
      t • OneCycle.numericalClass sX (C₀.cycle ℝ) = OneCycle.numericalClass sX (C.cycle ℝ))
    {L : Divisor X} (hLnef : L.IsNef ℂ sX) (hLQ : (Divisor.toQDivisor L).IsQCartier)
    (hface : {z | z ∈ closedConeOfCurves sX ∧
      QDivisor.curveForm sX (Divisor.toQDivisor L) hLQ z = 0} =
        {w | ∃ t : ℝ, 0 ≤ t ∧ t • OneCycle.numericalClass sX (C₀.cycle ℝ) = w})
    (hD : (Divisor.toQDivisor K + B).IsQCartier)
    (hneg : QDivisor.curveForm sX (Divisor.toQDivisor K + B) hD
      (OneCycle.numericalClass sX (C₀.cycle ℝ)) < 0)
    {m : ℕ} (hm : 0 < m) (Lc : X.CartierDivisor)
    (hLcnef : (KCartierDivisor.ofCartier ℝ Lc).IsNef ℂ sX)
    (hLcgen : SheafOfModules.IsGeneratedByGlobalSections
      (MMP.CartierDivisor.sheaf Lc))
    (hLcform : NumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ Lc) =
      (m : ℝ) • QDivisor.curveForm sX (Divisor.toQDivisor L) hLQ) :
    relativePicardNumberN1 sX c = 1 := by
  classical
  haveI hXp : AlgebraicGeometry.IsProjectiveVariety ℂ sX := hX
  haveI : IsProper sX := isProper_of_isProjectiveMorphism _ hX.isProjective
  haveI : AlgebraicGeometry.IsVariety ℂ sZ := hZ.toIsVariety
  set w₀ := OneCycle.numericalClass sX (C₀.cycle ℝ) with hw₀def
  set D := Divisor.toQDivisor K + B with hDdef
  set P := pullbackNumericalClasses sX c with hPdef
  set ℓ := QDivisor.curveForm sX (Divisor.toQDivisor L) hLQ with hℓdef
  set N := closedConeOfCurves sX with hNdef
  have hNclosed : IsClosed (N : Set (NumericalCurveClasses sX)) := by
    rw [hNdef, coe_closedConeOfCurves]; exact isClosed_closure
  have hclassN : ∀ C : ProperCurve sX, OneCycle.numericalClass sX (C.cycle ℝ) ∈ N := fun C =>
    coneOfCurves_le_closedConeOfCurves sX (numericalClass_cycle_mem_coneOfCurves sX C)
  have hw₀N : w₀ ∈ N := hclassN C₀
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  -- `ℓ ≥ 0` on `NE̅(X)`, vanishing exactly along the ray of `w₀`
  have hℓ : ∀ z ∈ N, 0 ≤ ℓ z := by
    intro z hz
    have h1 := (KCartierDivisor.mem_nonnegHalfspace_iff sX _ z).1
      ((KCartierDivisor.isNef_iff_closedConeOfCurves_subset_nonnegHalfspace sX _).1 hLcnef hz)
    rw [hLcform, LinearMap.smul_apply, smul_eq_mul] at h1
    exact nonneg_of_mul_nonneg_right (by linarith) hm0
  have hℓ0 : ∀ z ∈ N, ℓ z = 0 → ∃ s : ℝ, 0 ≤ s ∧ s • w₀ = z := fun z hz h0 => by
    have : z ∈ {z | z ∈ closedConeOfCurves sX ∧ ℓ z = 0} := ⟨hz, h0⟩
    rw [hface] at this
    exact this
  have hℓw₀ : ℓ w₀ = 0 := by
    have : w₀ ∈ {w | ∃ t : ℝ, 0 ≤ t ∧ t • w₀ = w} := ⟨1, zero_le_one, one_smul _ _⟩
    rw [← hface] at this
    exact this.2
  -- the cone theorem in `N₁(X)`
  obtain ⟨-, hfin, hdec⟩ := closedConeOfCurves_structure hX hK hB hD
  obtain ⟨H, hHamp⟩ := exists_isAmple_sheaf sX hXp
  obtain ⟨A, hAc, ⟨eA⟩⟩ := exists_divisor_iso_sheaf H
  haveI := hAc.isInvertibleModule_divisorialSheaf
  have hAamp : A.IsAmple hAc := (Stacks.RelativeVeryAmple.isAmple_congr _ _ eA).mpr hHamp
  set α := NumericalCurveClasses.degree sX A.divisorialSheaf with hαdef
  have hα : ∀ z ∈ N, z ≠ 0 → 0 < α z := by
    rw [hαdef, ← curveForm_toQDivisor_eq_degree sX A hAc (QDivisor.isQCartier_toQDivisor hAc)]
    exact curveForm_pos_of_isAmple sX A hAc hAamp _
  set φ := QDivisor.curveForm sX D hD with hφdef
  have hαv : 0 < α w₀ := hα w₀ hw₀N hw₀
  set ε : ℝ := -φ w₀ / (2 * α w₀) with hεdef
  have hε : 0 < ε := div_pos (by linarith) (by linarith)
  have hψv : φ w₀ + ε * α w₀ < 0 := by
    have : ε * α w₀ = -φ w₀ / 2 := by
      rw [hεdef]; field_simp
    linarith
  obtain ⟨t, _, Φ, -⟩ := exists_cartier_coordinates sX
  have hnef : ∀ F : NumericalCurveClasses sX →ₗ[ℝ] ℝ, F w₀ = 0 →
      ∃ T : ℝ, ∀ s : ℝ, T ≤ s → ∀ z ∈ N, 0 ≤ s * ℓ z + F z := fun F hF =>
    exists_forall_nonneg_mul_add Φ N hNclosed φ α ℓ F hα hε.le hψv hF hℓ hℓ0
      {R' | IsNegativeExtremalRayOf sX D R'}
      (fun R' hR' => ⟨hR'.2.1.1.1, let ⟨g, _, hg⟩ := hR'.2.1.2; ⟨g, hg⟩⟩)
      (hfin A hAc hAamp ε hε) hdec
  -- `m L` is a pull-back from `Z`
  have hLcP : numericalDivisorClass sX (KCartierDivisor.ofCartier ℝ Lc) ∈ P :=
    mem_pullbackNumericalClasses_of_isGeneratedByGlobalSections hX hZ c hcomp hcproj Lc hLcgen
      fun C hC => by
        obtain ⟨s, -, hs⟩ := hray C hC
        have h1 := intersectionNumber_numericalClass_cycle sX Lc C
        rw [hLcform, ← hs, map_smul, LinearMap.smul_apply, hℓw₀, smul_zero, smul_zero] at h1
        exact_mod_cast h1.symm
  -- the form `d ↦ (d · C₀)` on `N¹(X)`
  set ψ0 : KCartierDivisor ℝ X →ₗ[ℝ] ℝ :=
    (OneCycle.intersectionPairing (sX := sX)).flip (C₀.cycle ℝ) with hψ0def
  have hψ0 : ∀ x, ψ0 x = NumericalCurveClasses.intersectionNumber x w₀ := fun _ => rfl
  set ψb : NumericalDivisorClasses sX →ₗ[ℝ] ℝ :=
    (numericallyTrivialDivisors sX).liftQ ψ0 (fun x hx => by
      rw [LinearMap.mem_ker]
      exact mem_numericallyTrivialDivisors.mp hx C₀) with hψbdef
  have hψb : ∀ x, ψb (numericalDivisorClass sX x) = ψ0 x := fun _ => rfl
  -- a Cartier divisor of nonzero degree on `C₀`
  obtain ⟨E₀, hE₀⟩ : ∃ E₀ : X.CartierDivisor,
      C₀.degree ℂ (MMP.CartierDivisor.sheaf E₀) ≠ 0 := by
    have hnt : C₀.cycle ℝ ∉ OneCycle.numericallyTrivial sX := fun hmem =>
      hw₀ ((Submodule.Quotient.mk_eq_zero _).mpr hmem)
    rw [OneCycle.mem_numericallyTrivial] at hnt
    push Not at hnt
    obtain ⟨L', hL', hdeg⟩ := hnt
    obtain ⟨E', ⟨e'⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf L'
    refine ⟨E', fun h0 => hdeg ?_⟩
    rw [← NumericalCurveClasses.degree_numericalClass, degree_numericalClass_cycle]
    have := degreeOn_eq_of_iso ℂ sX C₀.ι C₀.dim_le e'
    rw [ProperCurve.degree] at h0 ⊢
    rw [this, h0]
    simp
  set e₀ : ℤ := C₀.degree ℂ (MMP.CartierDivisor.sheaf E₀) with he₀def
  have he₀ : (e₀ : ℝ) ≠ 0 := by exact_mod_cast hE₀
  have hψE (E : X.CartierDivisor) : ψ0 (KCartierDivisor.ofCartier ℝ E) =
      (C₀.degree ℂ (MMP.CartierDivisor.sheaf E) : ℝ) := by
    rw [hψ0]; exact intersectionNumber_numericalClass_cycle sX E C₀
  obtain ⟨W₀, hW₀c, ⟨eW₀⟩⟩ := exists_divisor_iso_sheaf E₀
  -- every class is a multiple of `[E₀]` modulo `P`
  have hQ : ∀ x : KCartierDivisor ℝ X,
      numericalDivisorClass sX (x - (ψ0 x / e₀) • KCartierDivisor.ofCartier ℝ E₀) ∈ P := by
    intro x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy =>
      have : x + y - (ψ0 (x + y) / e₀) • KCartierDivisor.ofCartier ℝ E₀ =
          (x - (ψ0 x / e₀) • KCartierDivisor.ofCartier ℝ E₀) +
            (y - (ψ0 y / e₀) • KCartierDivisor.ofCartier ℝ E₀) := by
        rw [map_add, add_div, add_smul]; abel
      rw [this, map_add]
      exact P.add_mem hx hy
    | single E r =>
      obtain ⟨WE, hWEc, ⟨eWE⟩⟩ := exists_divisor_iso_sheaf E
      set eE : ℤ := C₀.degree ℂ (MMP.CartierDivisor.sheaf E) with heEdef
      have hsingle : (Finsupp.single E r : KCartierDivisor ℝ X) =
          r • KCartierDivisor.ofCartier ℝ E := by
        simp [KCartierDivisor.ofCartier]
      set y : KCartierDivisor ℝ X := (e₀ : ℝ) • KCartierDivisor.ofCartier ℝ E -
        (eE : ℝ) • KCartierDivisor.ofCartier ℝ E₀ with hydef
      have hxy : Finsupp.single E r - (ψ0 (Finsupp.single E r) / e₀) •
          KCartierDivisor.ofCartier ℝ E₀ = (r / e₀) • y := by
        rw [hsingle, map_smul, hψE, smul_eq_mul, hydef, smul_sub, smul_smul, smul_smul,
          div_mul_cancel₀ _ he₀]
        congr 2
        ring
      set W' : Divisor X := e₀ • WE - eE • W₀ with hW'def
      have hW'c : W'.IsCartier := (hWEc.zsmul _).sub (hW₀c.zsmul _)
      have hW'form : QDivisor.curveForm sX (Divisor.toQDivisor W')
          (QDivisor.isQCartier_toQDivisor hW'c) =
          (e₀ : ℝ) • NumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ E) -
            (eE : ℝ) • NumericalCurveClasses.intersectionNumber
              (KCartierDivisor.ofCartier ℝ E₀) := by
        refine (curveForm_toQDivisor_sub sX (hWEc.zsmul e₀) (hW₀c.zsmul eE) _).trans ?_
        rw [curveForm_toQDivisor_zsmul sX _ hWEc, curveForm_toQDivisor_zsmul sX _ hW₀c,
          curveForm_toQDivisor_eq_intersectionNumber sX WE hWEc _ E eWE,
          curveForm_toQDivisor_eq_intersectionNumber sX W₀ hW₀c _ E₀ eW₀]
      have hW'0 : QDivisor.curveForm sX (Divisor.toQDivisor W')
          (QDivisor.isQCartier_toQDivisor hW'c) w₀ = 0 := by
        rw [hW'form]
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
        rw [intersectionNumber_numericalClass_cycle sX E C₀,
          intersectionNumber_numericalClass_cycle sX E₀ C₀]
        ring
      have hyP : numericalDivisorClass sX y ∈ P :=
        mem_pullbackNumericalClasses_of_curveForm_eq_zero hX hdim hK hB hZ c hcomp hcproj hray
          hLnef hLQ hℓ hℓ0 hℓw₀ hD hneg hm Lc hLcform hLcP hW'c hW'0 (hnef _ hW'0)
          (by rw [hW'form, hydef, intersectionNumber_sub, intersectionNumber_smul,
            intersectionNumber_smul])
      rw [hxy, map_smul]
      exact P.smul_mem _ hyP
  -- `P` is the kernel of `ψb`
  have hker : P = LinearMap.ker ψb := by
    apply le_antisymm
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨E, M, hM, ⟨e⟩, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, hψb, hψE]
      have h0 : C₀.degree ℂ (MMP.CartierDivisor.sheaf E) = 0 :=
        (degreeOn_eq_of_iso ℂ sX C₀.ι C₀.dim_le e).trans
          (ProperCurve.degree_pullback_eq_zero_of_isContractedBy c hcomp C₀ hC₀ M)
      rw [h0]
      simp
    · intro d hd
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ d
      have hx0 : ψ0 x = 0 := hd
      have := hQ x
      rwa [hx0, zero_div, zero_smul, sub_zero] at this
  have hsurj : Function.Surjective ψb := fun y =>
    ⟨(y / e₀) • numericalDivisorClass sX (KCartierDivisor.ofCartier ℝ E₀), by
      rw [map_smul, hψb, hψE, smul_eq_mul, div_mul_cancel₀ _ he₀]⟩
  have hrank :=
    ((Submodule.quotEquivOfEq _ _ hker).trans (ψb.quotKerEquivOfSurjective hsurj)).lift_rank_eq
  rw [Module.rank_self, Cardinal.lift_one, Cardinal.lift_eq_one] at hrank
  rw [relativePicardNumberN1, hrank, map_one]

/-! ### The contraction theorem -/

/-- **The contraction theorem for projective lc fourfolds.** -/
private theorem solution
    {X S : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    (hSn : MMP.Mori.IsNormalVariety ℂ sS)
    (h : X ⟶ S) (hh : h ≫ sS = sX) (hdim : topologicalKrullDim X = 4)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4)
    {B : QDivisor X} (hB : MMP.Intersection.IsLogCanonicalPair sX B)
    {R : Set (RelativeNumericalCurveClasses sX h)}
    (hR : IsNegativeRelativeExtremalRayOf sX h (Divisor.toQDivisor K + B) R) :
    ∃ (Z : Scheme.{0}) (sZ : Z ⟶ Spec (.of ℂ)) (c : X ⟶ Z) (g : Z ⟶ S),
      IsContraction sX sZ c ∧ IsRelativeContractionOfFace h R c g ∧ g ≫ sS = sZ ∧
        MMP.Mori.IsProjectiveVariety ℂ sZ ∧ relativePicardNumberN1 sX c = 1 ∧
        (-(Divisor.toQDivisor K + B)).HasRelativelyAmpleMultiple c := by
  classical
  haveI hXp : AlgebraicGeometry.IsProjectiveVariety ℂ sX := hX
  haveI hSp : AlgebraicGeometry.IsProjectiveVariety ℂ sS := hS
  haveI : IsProper sX := isProper_of_isProjectiveMorphism _ hX.isProjective
  have hXn : MMP.Mori.IsNormalVariety ℂ sX := ⟨hX.toIsVariety, inferInstance⟩
  set D := Divisor.toQDivisor K + B with hDdef
  -- the lc cone theorem: `R` is spanned by the class of a curve `C₀` contracted by `h`
  obtain ⟨hD, hray, -⟩ :=
    exists_relativeClosedConeOfCurves_eq_add_hull_of_isLogCanonicalPair hX hS h hh hdim hK hB
  obtain ⟨C₀, hC₀, -, hRC, -, -⟩ := hray R hR
  set w₀ := OneCycle.numericalClass sX (C₀.cycle ℝ) with hw₀def
  have hvw : relativeToAbsolute sX h (C₀.relativeClass h hC₀) = w₀ := rfl
  have himg : relativeToAbsolute sX h '' R = {w | ∃ t : ℝ, 0 ≤ t ∧ t • w₀ = w} := by
    rw [hRC]
    ext w
    constructor
    · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨t, ht, by rw [map_smul, hvw]⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t • C₀.relativeClass h hC₀, ⟨t, ht, rfl⟩, by rw [map_smul, hvw]⟩
  -- `R` is a `D`-negative extremal ray of `NE̅(X)`
  have hRabs : IsNegativeExtremalRayOf sX D (relativeToAbsolute sX h '' R) := by
    obtain ⟨hD', hext, hneg⟩ := hR
    refine ⟨hD, isExtremalRay_image_relativeToAbsolute sX sS h hh hext, ?_⟩
    rintro _ ⟨u, hu, rfl⟩ hu0
    have := hneg u hu (fun h0 => hu0 (by rw [h0, map_zero]))
    rw [relativeCurveForm_eq_comp] at this
    exact this
  have hw₀ : w₀ ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := hRabs.2.1.2
    have hvR : v ∈ relativeToAbsolute sX h '' R := hv ▸ ⟨1, zero_le_one, one_smul _ _⟩
    rw [himg] at hvR
    obtain ⟨t, -, ht⟩ := hvR
    rw [h0, smul_zero] at ht
    exact hv0 ht.symm
  have hnegw₀ : QDivisor.curveForm sX D hD w₀ < 0 :=
    hRabs.2.2 w₀ (himg ▸ ⟨1, zero_le_one, one_smul _ _⟩) hw₀
  -- the supporting divisor and the base point free theorem
  obtain ⟨L, hLnef, ⟨hLQ, hface⟩, a, ha, hamp⟩ :=
    exists_isNef_curveForm_eq_zero_and_isAmple_of_isNegativeExtremalRayOf hX hK hB hRabs
  obtain ⟨m₀, hm₀⟩ :=
    MMP.Intersection.IsLogCanonicalPair.exists_isBasepointFree_nsmul sX hX hdim hB hK hLnef ha hamp
  set m := m₀ + 1 with hmdef
  have hbpf : (m • L).IsBasepointFree := hm₀ m (by omega)
  have hmLc : (m • L).IsCartier := hLnef.1.nsmul m
  haveI := hmLc.isInvertibleModule_divisorialSheaf
  obtain ⟨Lc, ⟨eL⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf (m • L).divisorialSheaf
  have hLcform : NumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ Lc) =
      (m : ℝ) • QDivisor.curveForm sX (Divisor.toQDivisor L) hLQ := by
    rw [← curveForm_toQDivisor_eq_intersectionNumber sX (m • L) hmLc
      (QDivisor.isQCartier_toQDivisor hmLc) Lc eL, curveForm_toQDivisor_nsmul sX m hLnef.1]
  have hsupp : IsSupportingDivisor ℂ sX (relativeToAbsolute sX h '' R) Lc := by
    refine ⟨fun C => ?_, ?_⟩
    · rw [← NumericalCurveClasses.intersectionNumber_numericalClass, hLcform,
        LinearMap.smul_apply, smul_eq_mul,
        curveForm_toQDivisor_numericalClass sX L hLnef.1 hLQ C]
      exact mul_nonneg (Nat.cast_nonneg _) (by exact_mod_cast hLnef.2 _ C.ι C.isProperCurve.1)
    · rw [← hface]
      ext z
      have hm0 : (m : ℝ) ≠ 0 := by positivity
      simp only [Set.mem_setOf_eq, hLcform, LinearMap.smul_apply, smul_eq_mul, mul_eq_zero, hm0,
        false_or]
  have hLcgen : SheafOfModules.IsGeneratedByGlobalSections
      (MMP.CartierDivisor.sheaf Lc) := by
    obtain ⟨σ⟩ := isGeneratedByGlobalSections_of_isBasepointFree (m • L) hbpf
    exact ⟨SheafOfModules.GeneratingSections.equivOfIso eL σ⟩
  have hLm : ∃ m : ℕ, 0 < m ∧ SheafOfModules.IsGeneratedByGlobalSections
      (MMP.CartierDivisor.sheaf ((m : ℤ) • Lc)) := by
    refine ⟨1, one_pos, ?_⟩
    rw [Nat.cast_one, one_smul]
    exact hLcgen
  -- the contraction
  obtain ⟨Z, sZ, c, g, hcon, hcproj, hgS⟩ :=
    exists_isNegativeRelativeRayContraction_of_isSupportingDivisor sX sS hXn hX hSn hS h hh hR
      ⟨C₀, hC₀, hRC⟩ hsupp hLm
  obtain ⟨-, hface', ⟨-, hZn, -, ⟨hZv, -, hcomp, hcprop, hcapp⟩, hanti, -⟩⟩ := hcon
  have hZp : MMP.Mori.IsProjectiveVariety ℂ sZ := by
    rw [← hgS]
    exact (MMP.Mori.isProjectiveVariety_iff ℂ _).mpr ⟨hgS ▸ hZv, hface'.isProjectiveMorphism.comp
      hS.isProjective⟩
  haveI : IsIntegral Z := hZv.toIsIntegral
  have hcsurj : Function.Surjective c := surjective_of_isIso_app c hcapp
  haveI : Surjective c := ⟨hcsurj⟩
  haveI : ∀ U, IsIso (c.c.app U) := fun U => hcapp U.unop
  haveI : IsIso c.c := NatIso.isIso_of_isIso_app _
  have hcray : ∀ C : ProperCurve sX, C.IsContractedBy c → ∃ t : ℝ, 0 ≤ t ∧
      t • w₀ = OneCycle.numericalClass sX (C.cycle ℝ) := by
    intro C hC
    have hCh : C.IsContractedBy h := fun x hx => by
      rw [← hface'.comp_eq, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hC x hx]
    have hmem : relativeToAbsolute sX h (C.relativeClass h hCh) ∈
        relativeToAbsolute sX h '' R :=
      ⟨_, (hface'.isContractedBy_iff C hCh).mp hC, rfl⟩
    rw [himg] at hmem
    exact hmem
  have hC₀c : C₀.IsContractedBy c :=
    (hface'.isContractedBy_iff C₀ hC₀).mpr (hRC ▸ ⟨1, zero_le_one, one_smul _ _⟩)
  refine ⟨Z, sZ, c, g, ⟨hXn, hZn, hcomp, hcproj, hcsurj, hcapp⟩, hface', hgS, hZp,
    relativePicardNumberN1_eq_one hX hdim hK hB hZp c hcomp hcproj C₀ hC₀c hw₀ hcray hLnef hLQ
      (hface.trans himg) hD hnegw₀ (by omega) Lc hsupp.1 hLcgen hLcform, ?_⟩
  haveI : AlgebraicGeometry.IsVariety ℂ sX := hX.toIsVariety
  haveI : AlgebraicGeometry.IsVariety ℂ sZ := hZv
  have hcP : IsProjective c := IsProjective.of_comp c sZ (by
    rw [hcomp]; exact ((isProjectiveVariety_iff_isProjective' ℂ sX).mp hX).2)
  refine hasRelativelyAmpleMultiple_neg_of_forall_isContractedBy sX sZ c hcP hcomp hD hw₀ hcray ?_
  have h0 := hnegw₀
  rw [QDivisor.curveForm, QDivisor.associatedCartier, CartierDivisorWithCoeffs.ofCartier,
    Finsupp.smul_single, Finsupp.sum_single_index (by simp), LinearMap.smul_apply] at h0
  exact neg_of_smul_neg_left h0 (by have := QDivisor.cartierIndex_pos hD; positivity)

end Proof_thm_mmp_projective_fourfold_lc_contraction

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori

/-- **The contraction theorem for projective lc fourfolds.** Let `h : X ⟶ S` be a morphism of
normal projective complex varieties with `dim X = 4`, `K` a canonical divisor of `X`, `(X, B)` a
log canonical pair with `B` a `ℚ`-divisor, and `R` a `(K + B)`-negative extremal ray of
`relativeClosedConeOfCurves sX h`. Then there are a normal projective variety `Z`, a projective
contraction `c : X ⟶ Z` and a projective morphism `g : Z ⟶ S` with `c ≫ g = h`, such that
`c_* 𝒪_X = 𝒪_Z`, a curve contracted by `h` is contracted by `c` if and only if its class lies in
`R`, `ρ(X/Z) = 1`, and `-(K + B)` is `c`-ample. -/
@[mmp "thm_mmp_projective_fourfold_lc_contraction"]
public theorem exists_isRelativeContractionOfFace_of_isNegativeRelativeExtremalRayOf
    {X S : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    (hSn : MMP.Mori.IsNormalVariety ℂ sS)
    (h : X ⟶ S) (hh : h ≫ sS = sX) (hdim : topologicalKrullDim X = 4)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4)
    {B : QDivisor X} (hB : MMP.Intersection.IsLogCanonicalPair sX B)
    {R : Set (RelativeNumericalCurveClasses sX h)}
    (hR : IsNegativeRelativeExtremalRayOf sX h (Divisor.toQDivisor K + B) R) :
    ∃ (Z : Scheme.{0}) (sZ : Z ⟶ Spec (.of ℂ)) (c : X ⟶ Z) (g : Z ⟶ S),
      IsContraction sX sZ c ∧ IsRelativeContractionOfFace h R c g ∧ g ≫ sS = sZ ∧
        MMP.Mori.IsProjectiveVariety ℂ sZ ∧ relativePicardNumberN1 sX c = 1 ∧
        (-(Divisor.toQDivisor K + B)).HasRelativelyAmpleMultiple c :=
          by revert X S sX sS hX hS hSn h hh hdim K hK B hB R hR; first | exact Proof_thm_mmp_projective_fourfold_lc_contraction.solution | exact Proof_thm_mmp_projective_fourfold_lc_contraction.solution _ | exact Proof_thm_mmp_projective_fourfold_lc_contraction.solution _ _ | exact Proof_thm_mmp_projective_fourfold_lc_contraction.solution _ _ _ | exact Proof_thm_mmp_projective_fourfold_lc_contraction.solution _ _ _ _

end MMP.Fourfold

