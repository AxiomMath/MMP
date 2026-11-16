module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.AlgebraicGeometry.Morphisms.FiniteCoverTrace
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
import MMP.AlgebraicGeometry.Positivity.RelativeAmplePullbackTwist
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Valuation
import MMP.AlgebraicGeometry.Divisor.Negativity.CodimTwoCentres

/-!
# Exceptional prime divisors of an extremal birational contraction are negative on the ray

Let `X` be a normal projective `ℚ`-factorial variety over a field `k`, `R ⊆ NE̅(X)` an extremal
ray and `f : X ⟶ Y` a birational contraction of `R`. If `E ⊆ Ex(f)` is a prime divisor, then
`(E · C) < 0` for every irreducible curve `C ⊆ X` such that `f(C)` is a point. The proof writes
`[C] = λ_C v` with `λ_C > 0` for a generator `v` of `R`, and shows `(E · v) < 0` by the
negativity lemma applied to `-E`, whose push-forward `f_* (-E)` vanishes.

## Main results

* `MMP.Mori.intersectionNumber_single_neg_of_isContractionOfFace`: `(E · C) < 0`.

## Implementation notes

The auxiliary lemmas live in the namespace `MMP.Mori.ExceptionalDivisorNegativeOnRay` and are
opened only for the main result. `[C] ≠ 0` comes from the
positivity of an ample invertible sheaf on `C`; `f_* E = 0` from the codimension-two complement
of the biregular locus of `f` in the normal variety `Y`; and the negativity lemma is
`MMP.Mori.QDivisor.isEffective_iff_isEffective_transformDivisor_of_isRelativelyNef_neg`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Proposition 2.5, Lemma 3.39
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Mori.ExceptionalDivisorNegativeOnRay

open MMP.Mori

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

section Intersection

variable [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- The intersection number `(D · C)` is `deg_C 𝒪_X(m_D D) / m_D`, computed with the Cartier
divisor `m_D D` that also defines the associated `ℚ`-Cartier divisor of `D`. -/
private theorem intersectionNumber_eq_degreeOn_div (D : QDivisor X) (hD : D.IsQCartier)
    (C : ProperCurve sX) :
    D.intersectionNumber k sX C.ι C.dim_le hD =
      ((D.cartierIndexSMul hD : Divisor X).degreeOn k sX C.ι C.dim_le
        (D.cartierIndexSMul hD).2 : ℚ) / D.cartierIndex hD :=
  QDivisor.intersectionNumber_eq_of_toQDivisor_eq k sX C.ι C.dim_le D hD _ _
    (QDivisor.toQDivisor_cartierIndexSMul D hD)

/-- A `ℚ`-Cartier `ℚ`-divisor with `(D · C) ≥ 0` for every proper curve `C` contracted by `f` is
`f`-nef. -/
private theorem isRelativelyNef_of_intersectionNumber_nonneg {Y : Scheme.{u}} (f : X ⟶ Y)
    (D : QDivisor X) (hD : D.IsQCartier)
    (h : ∀ C : ProperCurve sX, C.IsContractedBy f →
      0 ≤ D.intersectionNumber k sX C.ι C.dim_le hD) :
    D.IsRelativelyNef sX f := by
  refine ⟨hD, fun C hC => ?_⟩
  have key := h C hC
  rw [intersectionNumber_eq_degreeOn_div,
    le_div_iff₀ (by exact_mod_cast QDivisor.cartierIndex_pos hD), zero_mul] at key
  rw [QDivisor.associatedCartier, CartierDivisorWithCoeffs.ofCartier, Finsupp.smul_single,
    Finsupp.sum_single_index (by simp), smul_eq_mul]
  have : (0 : ℚ) ≤ (1 / (D.cartierIndex hD : ℚ)) * 1 *
      ((D.cartierIndexSMul hD : Divisor X).degreeOn k sX C.ι C.dim_le
        (D.cartierIndexSMul hD).2 : ℚ) := by positivity
  exact_mod_cast this

/-- The intersection number `(D · C)`, as a real number, is the degree of `𝒪_X(m_D D)` on the
class `[C] ∈ N₁(X)`, divided by `m_D`. -/
private theorem intersectionNumber_eq_degree_numericalClass_div (D : QDivisor X)
    (hD : D.IsQCartier) (C : ProperCurve sX) :
    haveI := QuasiCompact.compactSpace_of_compactSpace sX
    haveI := (D.cartierIndexSMul hD).2.isInvertibleModule_divisorialSheaf
    ((D.intersectionNumber k sX C.ι C.dim_le hD : ℚ) : ℝ) =
      NumericalCurveClasses.degree sX (D.cartierIndexSMul hD : Divisor X).divisorialSheaf
        (OneCycle.numericalClass sX (C.cycle ℝ)) / D.cartierIndex hD := by
  rw [intersectionNumber_eq_degreeOn_div, NumericalCurveClasses.degree_numericalClass,
    OneCycle.degree_cycle, ProperCurve.degree_divisorialSheaf]
  push_cast
  rfl

/-- The intersection number `(D · C)` is nonnegative exactly when the degree form of
`𝒪_X(m_D D)` is nonnegative at the class `[C] ∈ N₁(X)`. -/
private theorem intersectionNumber_nonneg_iff (D : QDivisor X) (hD : D.IsQCartier)
    (C : ProperCurve sX) :
    haveI := QuasiCompact.compactSpace_of_compactSpace sX
    haveI := (D.cartierIndexSMul hD).2.isInvertibleModule_divisorialSheaf
    0 ≤ D.intersectionNumber k sX C.ι C.dim_le hD ↔
      0 ≤ NumericalCurveClasses.degree sX (D.cartierIndexSMul hD : Divisor X).divisorialSheaf
        (OneCycle.numericalClass sX (C.cycle ℝ)) := by
  rw [← Rat.cast_nonneg (K := ℝ), intersectionNumber_eq_degree_numericalClass_div,
    le_div_iff₀ (by exact_mod_cast QDivisor.cartierIndex_pos hD), zero_mul]

end Intersection

/-- On a projective variety the numerical class `[C] ∈ N₁(X)` of a proper curve is nonzero. -/
private theorem numericalClass_cycle_ne_zero (hX : MMP.Mori.IsProjectiveVariety k sX)
    (C : ProperCurve sX) : OneCycle.numericalClass sX (C.cycle ℝ) ≠ 0 := by
  have hproj : IsProjectiveMorphism sX := hX.isProjective
  obtain ⟨L, hL, hLa⟩ := exists_isAmple_of_isQuasiProjective sX
    (Stacks.Ample.unitModule (Spec (.of k)))
    (Stacks.Ample.isAmple_unitModule_of_isAffine _)
    (isQuasiProjective_of_isHQuasiProjective sX hproj.isHQuasiProjective)
  have hpos := MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy sX L
    (MMP.Threefold.Resolution.isRelativelyAmple_of_isAmple sX L hLa) C
    (fun _ _ => Subsingleton.elim _ _)
  intro h0
  have h := OneCycle.mem_numericallyTrivial.mp ((Submodule.Quotient.mk_eq_zero _).mp h0) L
  rw [OneCycle.degree_cycle] at h
  unfold ProperCurve.degree at h
  have : (0 : ℝ) < (degreeOn k sX C.ι C.dim_le L : ℝ) := by exact_mod_cast hpos
  linarith

/-- A prime divisor contained in the exceptional set of a proper birational morphism `f` to a
normal variety has no transform under `f`: its image has codimension at least two. -/
private theorem transformPrimeDivisor_eq_none_of_support_subset {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [hY : MMP.Mori.IsVariety k sY] [IsNormal Y] [IsReduced X]
    (f : X ⟶ Y) [MMP.Mori.IsVariety k (f ≫ sY)] [IsProper f] (hf : IsBirationalMorphism f)
    (E : MMP.Mori.PrimeDivisor X) (hE : E.support ⊆ (exceptionalSet f : Set X)) :
    RationalMap.transformPrimeDivisor (X := X) f.toRationalMap E = none := by
  have : IsSeparated sY := hY.toIsSeparated
  have : IsSeparated (Y ↘ Limits.terminal Scheme) := by
    rw [show (Y ↘ Limits.terminal Scheme) = sY ≫ (Spec (.of k) ↘ Limits.terminal Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  rcases h : RationalMap.transformPrimeDivisor (X := X) f.toRationalMap E with _ | Q
  · rfl
  exfalso
  have hfQ := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f E Q).mp h
  have hmem : Q.genericPoint ∈ ((biregularLocus f).compl : Set Y) := by
    rw [← hfQ]
    refine hE ?_
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have hcod := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp
    (two_le_closedsCodimension_compl_biregularLocus sY f hf) _ hmem
  rw [Q.coheight_genericPoint] at hcod
  exact absurd hcod (by decide)

/-- **Negativity.** If `f` is a birational contraction of a face and `E` is a prime divisor
contained in the exceptional set of `f`, then the `ℚ`-divisor `1 · E` is not `f`-nef. -/
private theorem not_isRelativelyNef_single_of_support_subset {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsLocallyNoetherian X] [IsNormal X]
    [QuasiCompact sX] {R : Set (NumericalCurveClasses sX)} {f : X ⟶ Y}
    (hf : IsContractionOfFace k sX sY R f) (hbir : IsBirationalMorphism f)
    (E : MMP.Mori.PrimeDivisor X) (hE : E.support ⊆ (exceptionalSet f : Set X)) :
    ¬ QDivisor.IsRelativelyNef sX f (Finsupp.single E (1 : ℚ)) := by
  intro hnef
  obtain ⟨hXv, hXproj⟩ := (MMP.Mori.isProjectiveVariety_iff k sX).mp hf.isProjectiveVariety_source
  obtain ⟨hYv, -⟩ := (MMP.Mori.isProjectiveVariety_iff k sY).mp hf.isProjectiveVariety_target
  have hXv' : MMP.Mori.IsVariety k (f ≫ sY) := hf.comp_eq ▸ hXv
  have : IsIntegral X := hXv.toIsIntegral
  have : IsIntegral Y := hYv.toIsIntegral
  have : IsProper sX := isProper_of_isProjectiveMorphism sX hXproj
  have : IsSeparated sY := hYv.toIsSeparated
  have : IsProper (f ≫ sY) := hf.comp_eq ▸ inferInstance
  have : IsProper f := IsProper.of_comp f sY
  have : IsDominant f := hbir.isDominant
  have : ∀ U, IsIso (f.c.app U) := fun U => hf.isIso_app U.unop
  have : IsIso f.c := NatIso.isIso_of_isIso_app _
  have : IsNormal Y := isNormal_of_isIso_c sY f hYv hXv'
  have heff := (QDivisor.isEffective_iff_isEffective_transformDivisor_of_isRelativelyNef_neg
    k sY sX ⟨hYv, inferInstance⟩ ⟨hXv, inferInstance⟩ f hf.comp_eq hbir
    (B := -Finsupp.single E (1 : ℚ))
    (by obtain ⟨m, hm0, h⟩ := hnef.1; exact ⟨m, hm0, by rw [smul_neg]; exact h.neg⟩)
    (by rwa [neg_neg])).mpr (by
      rw [map_neg, RationalMap.transformDivisor_single_of_eq_none
        (transformPrimeDivisor_eq_none_of_support_subset sY f hbir E hE), neg_zero]
      exact DivisorWithCoeffs.isEffective_zero)
  have h := DivisorWithCoeffs.isEffective_iff_nonneg.mp heff E
  norm_num at h

end MMP.Mori.ExceptionalDivisorNegativeOnRay

namespace MMP.Mori

open ExceptionalDivisorNegativeOnRay

/-- **Exceptional prime divisors are negative on the contracted ray.** Let `X` be a normal
projective `ℚ`-factorial variety over `k`, `R ⊆ NE̅(X)` an extremal ray and `f : X ⟶ Y` a
birational contraction of `R`. If `E` is a prime divisor of `X` contained in the exceptional set
`MMP.Mori.exceptionalSet f`, then `(E · C) < 0` for every proper curve `C ⊆ X` contracted by
`f`. -/
@[mmp "lem_km2a_exceptional_divisor_negative_on_ray"]
public theorem intersectionNumber_single_neg_of_isContractionOfFace
    {k : Type u} [Field k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX]
    (hX : MMP.Fourfold.IsQFactorial sX) {R : Set (NumericalCurveClasses sX)}
    (hR : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R)
    {f : X ⟶ Y} (hf : IsContractionOfFace k sX sY R f) (hbir : IsBirationalMorphism f)
    (E : PrimeDivisor X) (hE : E.support ⊆ (exceptionalSet f : Set X))
    (C : ProperCurve sX) (hC : C.IsContractedBy f) :
    QDivisor.intersectionNumber k sX C.ι C.dim_le (Finsupp.single E (1 : ℚ))
      (MMP.Fourfold.isQCartier_of_isQFactorial sX hX _) < 0 := by
  set D : QDivisor X := Finsupp.single E (1 : ℚ)
  set hD := MMP.Fourfold.isQCartier_of_isQFactorial sX hX D
  -- the classes of contracted curves lie on the ray `R = ℝ_{≥ 0} v`, and `[C] = c v` with `c > 0`
  obtain ⟨-, v, -, hRv⟩ := hR
  have hray : ∀ C' : ProperCurve sX, C'.IsContractedBy f →
      ∃ c : ℝ, 0 ≤ c ∧ c • v = OneCycle.numericalClass sX (C'.cycle ℝ) := fun C' hC' => by
    simpa only [hRv, Set.mem_setOf_eq] using (hf.isContractedBy_iff C').mp hC'
  obtain ⟨c, hc0, hcv⟩ := hray C hC
  have hc : 0 < c := hc0.lt_of_ne <| by
    rintro rfl
    exact numericalClass_cycle_ne_zero hf.isProjectiveVariety_source C (by rw [← hcv, zero_smul])
  -- if `(E · C) ≥ 0` then `(E · v) ≥ 0`, so `E` is `f`-nef
  refine lt_of_not_ge fun hneg => not_isRelativelyNef_single_of_support_subset hf hbir E hE
    (isRelativelyNef_of_intersectionNumber_nonneg f D hD fun C' hC' => ?_)
  obtain ⟨c', hc'0, hc'v⟩ := hray C' hC'
  rw [intersectionNumber_nonneg_iff, ← hcv, map_smul, smul_eq_mul] at hneg
  rw [intersectionNumber_nonneg_iff, ← hc'v, map_smul, smul_eq_mul]
  exact mul_nonneg hc'0 (nonneg_of_mul_nonneg_right hneg hc)

end MMP.Mori
