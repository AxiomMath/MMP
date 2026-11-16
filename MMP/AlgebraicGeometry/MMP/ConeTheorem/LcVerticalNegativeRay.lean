module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
import MMP.AlgebraicGeometry.Intersection.PairingSeparation
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.MMP.ConeTheorem.NegativeVerticalExtremalRay

/-!
# A vertical negative extremal ray of a projective lc pair

Let `(U, Δ)` be a projective lc pair over an algebraically closed field `k` of characteristic
zero, with canonical divisor `K`, and let `h : U ⟶ Z` be a projective morphism to a projective
variety such that `K + Δ` is not nef over `Z`. Then `NE̅(U)` has a `(K + Δ)`-negative extremal
ray `R` all of whose curves are contracted by `h`: every curve `C ⊆ U` with `[C] ∈ R` has `h(C)`
a point. The ray is an extremal ray of the absolute cone `NE̅(U)`, not merely of the relative
cone, and it is not claimed to be spanned by the class of a rational curve.

This is the case `D = K + Δ` of
`MMP.Mori.exists_isExtremalRay_neg_contractedBy_of_not_isRelativelyNef`; the lc hypothesis
makes `K + Δ` `ℚ`-Cartier, so that it defines a linear form on `N₁(U)_ℝ`.

## Main results

* `MMP.Fourfold.exists_isNegativeExtremalRayOf_isContractedBy_of_not_isRelativelyNef`: the ray.

## Implementation notes

Since canonical divisors are unique up to linear equivalence, `K + Δ` is `ℚ`-Cartier. Writing
its associated `ℚ`-Cartier divisor as `∑ⱼ cⱼ Eⱼ` and choosing, for each Cartier Weil divisor `Eⱼ`,
a Cartier divisor `Eⱼ'` with `𝒪_U(Eⱼ') ≅ 𝒪_U(Eⱼ)`, the `ℝ`-Cartier divisor `D = ∑ⱼ cⱼ Eⱼ'` has
the same degree as `K + Δ` on every curve. So `D` is not nef over `Z`, and a `D`-negative
vertical extremal ray of `NE̅(U)` is a `(K + Δ)`-negative one.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

section Helpers

variable {k : Type*} [Field k] {X : Scheme} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]

/-- A Cartier divisor `E'` with `𝒪_X(E') ≅ 𝒪_X(E)`, for a Cartier Weil divisor `E`. -/
private noncomputable def toCartier (E : Divisor.cartierSubgroup (X := X)) : X.CartierDivisor :=
  haveI := (Divisor.mem_cartierSubgroup.mp E.2).isInvertibleModule_divisorialSheaf
  (exists_nonempty_iso_cartierDivisor_sheaf (E : Divisor X).divisorialSheaf).choose

private theorem degree_toCartier (E : Divisor.cartierSubgroup (X := X)) (Z : OneCycle ℝ sX) :
    haveI := (Divisor.mem_cartierSubgroup.mp E.2).isInvertibleModule_divisorialSheaf
    OneCycle.cartierDegree (toCartier E) Z =
      OneCycle.degree ℝ sX (E : Divisor X).divisorialSheaf Z := by
  haveI := (Divisor.mem_cartierSubgroup.mp E.2).isInvertibleModule_divisorialSheaf
  obtain ⟨e⟩ :=
    (exists_nonempty_iso_cartierDivisor_sheaf (E : Divisor X).divisorialSheaf).choose_spec
  rw [OneCycle.cartierDegree, OneCycle.degree, OneCycle.degree]
  congr 2
  funext C
  exact congrArg _ (degreeOn_eq_of_iso k sX C.ι C.dim_le e).symm

/-- The `ℝ`-Cartier divisor `∑ⱼ cⱼ Eⱼ'` of a `ℚ`-Cartier `ℚ`-divisor with associated
`ℚ`-Cartier divisor `∑ⱼ cⱼ Eⱼ`. -/
private noncomputable def toReal (D : QDivisor X) (h : D.IsQCartier) : KCartierDivisor ℝ X :=
  (D.associatedCartier h).sum fun E c => (c : ℝ) • KCartierDivisor.ofCartier ℝ (toCartier E)

private theorem intersectionNumber_toReal (D : QDivisor X) (h : D.IsQCartier)
    (Z : OneCycle ℝ sX) :
    Z.intersectionNumber (toReal D h) = (D.associatedCartier h).sum fun E c =>
      haveI := (Divisor.mem_cartierSubgroup.mp E.2).isInvertibleModule_divisorialSheaf
      (c : ℝ) * OneCycle.degree ℝ sX (E : Divisor X).divisorialSheaf Z := by
  rw [OneCycle.intersectionNumber, toReal, map_finsuppSum, LinearMap.finsupp_sum_apply]
  refine Finsupp.sum_congr fun E _ => ?_
  rw [map_smul, LinearMap.smul_apply, ← OneCycle.intersectionNumber,
    OneCycle.intersectionNumber_ofCartier, degree_toCartier, smul_eq_mul]

private theorem intersectionNumber_toReal_eq_curveForm (D : QDivisor X) (h : D.IsQCartier) :
    NumericalCurveClasses.intersectionNumber (toReal D h) = QDivisor.curveForm sX D h := by
  refine LinearMap.ext fun z => ?_
  obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX z
  rw [NumericalCurveClasses.intersectionNumber_numericalClass, intersectionNumber_toReal,
    QDivisor.curveForm, LinearMap.finsupp_sum_apply]
  rfl

private theorem not_isRelativelyNef_toReal {Y : Scheme} (f : X ⟶ Y)
    (D : QDivisor X) (h : D.IsQCartier) (hD : ¬ QDivisor.IsRelativelyNef sX f D) :
    ¬ (toReal D h).IsRelativelyNef sX f := by
  refine fun hnef => hD ⟨h, fun C hC => (hnef C hC).trans_eq ?_⟩
  rw [intersectionNumber_toReal]
  refine Finsupp.sum_congr fun E _ => ?_
  rw [OneCycle.degree_cycle]
  rfl

end Helpers

/-- **A vertical negative extremal ray.** Let `(U, Δ)` be a projective lc pair over an
algebraically closed field of characteristic zero, with canonical divisor `K`, and `h : U ⟶ Z` a
projective morphism to a projective variety such that `K + Δ` is not nef over `Z`. Then `NE̅(U)`
has a `(K + Δ)`-negative extremal ray `R` such that every curve `C ⊆ U` whose class lies in `R`
is contracted by `h`. -/
@[mmp "lem_oai4_vertical_ray"]
public theorem exists_isNegativeExtremalRayOf_isContractedBy_of_not_isRelativelyNef
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {U Z : Scheme.{0}}
    [IsIntegral U] [CompactSpace U] [IsLocallyNoetherian U] [IsNormal U]
    {sU : U ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    (hU : MMP.Mori.IsProjectiveVariety k sU) (hZ : MMP.Mori.IsProjectiveVariety k sZ)
    {K : Divisor U} (hK : ∃ n : ℕ, K.IsCanonicalDivisor sU n) {Δ : QDivisor U}
    (hΔ : MMP.Intersection.IsLogCanonicalPair sU Δ)
    {h : U ⟶ Z} (hh : IsProjectiveMorphism h) (hhZ : h ≫ sZ = sU)
    (hnef : ¬ QDivisor.IsRelativelyNef sU h (Divisor.toQDivisor K + Δ)) :
    ∃ R : Set (NumericalCurveClasses sU),
      IsNegativeExtremalRayOf sU (Divisor.toQDivisor K + Δ) R ∧
      ∀ C : ProperCurve sU, OneCycle.numericalClass sU (C.cycle ℝ) ∈ R → C.IsContractedBy h := by
  obtain ⟨hP, -, -⟩ := hΔ
  obtain ⟨_, K₀, hK₀, hQ⟩ := hP.isQCartier_of_linearlyEquivalent
  obtain ⟨_, hKn⟩ := hK
  have hQK := hQ K (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sU
    hP.isNormalVariety hKn hK₀)
  obtain ⟨R, hR, hneg, hvert⟩ :=
    exists_isExtremalRay_neg_contractedBy_of_not_isRelativelyNef hU hZ hhZ
      (not_isRelativelyNef_toReal h _ hQK hnef)
  refine ⟨R, ⟨hQK, hR, fun u hu hu0 => ?_⟩, hvert⟩
  rw [← intersectionNumber_toReal_eq_curveForm]
  exact hneg u hu hu0

end MMP.Fourfold
