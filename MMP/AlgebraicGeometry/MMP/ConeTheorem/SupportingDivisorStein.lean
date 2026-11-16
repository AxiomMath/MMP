module
public import MMP.Attr
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Basic
public import MMP.AlgebraicGeometry.Divisor.Basic
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Comparison
public import StacksFrontier.AlgebraicGeometry.ProjCoherentCohomologyFinite.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.AmpleTwistingSheaf
import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.FiniteDominant
import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CurveInputs
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafMul
import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.AmpleStrictlyPositive
import MMP.AlgebraicGeometry.Resolution.MaximalOrderAttained
import MMP.AlgebraicGeometry.Divisor.QuasiProjectiveCartierSupport

/-!
# Supporting divisors, Stein contractions and the salience of `NE̅(X)`

Let `X` be a projective variety over a field `k`.

An ample Cartier divisor `H` on `X` is strictly positive on every nonzero class of the closed
cone of curves `NE̅(X)`; since `z ↦ (H · z)` is linear, `z` and `-z` cannot both be nonzero
members of the cone, so `NE̅(X) ∩ (-NE̅(X)) = {0}`.

Let moreover `X` be normal, `F` an extremal face of `NE̅(X)`, and `D` a supporting divisor of
`F`. Suppose that for some `b ≥ 1` the divisor `bD` defines a `k`-morphism `φ : X ⟶ ℙᴺ_k`, that
is, `φ^* 𝒪_{ℙᴺ}(1) ≅ 𝒪_X(bD)`, and that `φ = h ∘ ψ` with `ψ : X ⟶ Z` surjective onto a normal
variety, `ψ_* 𝒪_X = 𝒪_Z`, and `h` finite. The pullback `h^* 𝒪(1)` is ample on the proper
variety `Z`, so `Z` is projective. For a curve `C ⊆ X`, `ψ(C)` is a point exactly when `φ(C)` is
one, since the fibres of `h` are discrete; and `(bD · C) = deg_C φ^* 𝒪(1)` vanishes when `φ(C)`
is a point and equals `[k(C) : k(φ(C))] · deg_{φ(C)} 𝒪(1) > 0` otherwise. Hence `ψ` contracts
`C` if and only if `(D · C) = 0`, that is, `[C] ∈ F`: `ψ` is a contraction of `F`.

## Main results

* `MMP.Mori.IsProjectiveVariety.exists_isAmple_cartierDivisorSheaf`: a projective variety carries
  a Cartier divisor whose invertible sheaf is ample.
* `MMP.Mori.lineal_closedConeOfCurves_eq_bot`: the lineality space of `NE̅(X)` is `⊥`.
* `MMP.Mori.isContractionOfFace_of_isSupportingDivisor`: `ψ` is a contraction of `F`, and in
  particular `Z` is a projective variety.
* `MMP.Mori.isContractionOfFace_of_isSupportingDivisor_of_isAmple`: the same for any
  `k`-morphism `φ : X ⟶ P` to a proper `k`-scheme with `φ^* O ≅ 𝒪_X(bD)`, `O` ample invertible.
* `MMP.Mori.ProperCurve.degree_sheaf_nsmul`: `deg_C 𝒪_X(nD) = n · deg_C 𝒪_X(D)` for `n ≥ 1`.
* `MMP.Mori.IsSupportingDivisor.numericalClass_mem_iff_degree_eq_zero`: for a supporting
  divisor `D` of `F`, `[C] ∈ F` iff `deg_C 𝒪_X(D) = 0`.

## Implementation notes

The condition `NE̅(X) ∩ (-NE̅(X)) = {0}` is stated as the vanishing of the lineality space
`PointedCone.lineal`, which is by definition `NE̅(X) ⊓ -NE̅(X)` as a submodule
(`PointedCone.ofSubmodule_lineal`). No hypothesis on the base field is made.

The proof uses of `ℙᴺ_k` only that it is proper over `k` and that `𝒪(1)` is ample, so it is
carried out for an arbitrary proper `k`-scheme `P` with an ample invertible sheaf `O`; neither
normality of `X` and `Z` nor surjectivity of `ψ` is needed there, only that `Z` is a variety.

The `k`-structure of `Z` is `h` followed by the structure morphism of `ℙᴺ_k`, so that `h` is a
`k`-morphism and `ψ` is one as soon as `φ` is. The condition `ψ_* 𝒪_X = 𝒪_Z` is that
`ψ^♯ : 𝒪_Z(U) → 𝒪_X(ψ⁻¹ U)` is an isomorphism for every open `U ⊆ Z`, as in
`MMP.Mori.IsContractionOfFace`. Projectivity of `Z` is the field
`MMP.Mori.IsContractionOfFace.isProjectiveVariety_target` of the conclusion.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998], 1.18 and
  3.3 Step 7.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace MMP.Mori

section ConePointed

/-- A projective variety carries a Cartier divisor whose invertible sheaf is ample. -/
public theorem IsProjectiveVariety.exists_isAmple_cartierDivisorSheaf {k : Type*} [Field k]
    {X : Scheme} {sX : X ⟶ Spec (.of k)} [h : AlgebraicGeometry.IsProjectiveVariety k sX] :
    ∃ D : X.CartierDivisor, Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf D) := by
  obtain ⟨⟨L, hL, hrel, hA⟩, -⟩ :=
    MMP.Foundations.IsProjective.exists_isRelativelyAmple h.isProjective.isProjective
  obtain ⟨A, ⟨e⟩⟩ := hA inferInstance
  exact ⟨A, (Stacks.RelativeVeryAmple.isAmple_congr _ _ e).mpr
    (Stacks.HProjective.isAmple_of_isRelativelyAmple_of_isAffine sX L hrel)⟩

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- The closed cone of curves `NE̅(X)` of a projective variety contains no line:
`NE̅(X) ∩ (-NE̅(X)) = {0}`. -/
@[mmp "lem_mmp_foundation_full_field_projective_cone_pointed"]
public theorem lineal_closedConeOfCurves_eq_bot [IsProjectiveVariety k sX] :
    (closedConeOfCurves sX).lineal = ⊥ := by
  obtain ⟨H, hH⟩ := IsProjectiveVariety.exists_isAmple_cartierDivisorSheaf (sX := sX)
  have hpos := closedConeOfCurves_diff_zero_subset_posHalfspace sX H hH
  refine (Submodule.eq_bot_iff _).2 fun z hz => ?_
  rw [PointedCone.mem_lineal] at hz
  by_contra hz0
  have h1 := (KCartierDivisor.mem_posHalfspace_iff sX _ _).1 (hpos ⟨hz.1, hz0⟩)
  have h2 := (KCartierDivisor.mem_posHalfspace_iff sX _ _).1 (hpos ⟨hz.2, neg_ne_zero.2 hz0⟩)
  rw [map_neg] at h2
  linarith

end ConePointed

section SteinContraction

attribute [local instance] MvPolynomial.gradedAlgebra

open Stacks.AlgebraicGeometry.ProjPolyChart

/-- `deg_C 𝒪_X(nD) = n · deg_C 𝒪_X(D)` for `n ≥ 1`. -/
public theorem ProperCurve.degree_sheaf_nsmul {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (C : ProperCurve sX) (D : X.CartierDivisor) {n : ℕ} (hn : 1 ≤ n) :
    C.degree k (CartierDivisor.sheaf (n • D)) = n * C.degree k (CartierDivisor.sheaf D) := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [succ_nsmul]
    unfold ProperCurve.degree at *
    haveI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
        ((MMP.CartierDivisor.sheaf (n • D)).tensorObj (MMP.CartierDivisor.sheaf D)) :=
      Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible X.presheaf X.ringCatSheaf.2 _ _
    rw [degreeOn_eq_of_iso k sX C.ι C.dim_le (MMP.CartierDivisorSheaf.sheafMulIso (n • D) D).symm]
    refine (degreeOn_tensorSheaf k sX C.ι C.dim_le _ _ (hLM := this)).trans ?_
    rw [ih]
    push_cast
    ring

/-- For a supporting divisor `D` of `F`, a curve `C` has `[C] ∈ F` iff `deg_C 𝒪_X(D) = 0`. -/
public theorem IsSupportingDivisor.numericalClass_mem_iff_degree_eq_zero {k : Type u} [Field k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {F : Set (NumericalCurveClasses sX)}
    {D : X.CartierDivisor} (hD : IsSupportingDivisor k sX F D) (C : ProperCurve sX) :
    OneCycle.numericalClass sX (C.cycle ℝ) ∈ F ↔ C.degree k (MMP.CartierDivisor.sheaf D) = 0 := by
  rw [← hD.2]
  simp only [Set.mem_setOf_eq, NumericalCurveClasses.intersectionNumber_numericalClass,
    OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree, OneCycle.degree_cycle,
    Int.cast_eq_zero, and_iff_right_iff_imp]
  exact fun _ => coneOfCurves_le_closedConeOfCurves _ (numericalClass_cycle_mem_coneOfCurves _ C)

/-- A curve `C ⊆ X` is contracted by `ψ` iff its image under `ψ ≫ h` is a point, when `h` is
finite. -/
private theorem isContractedBy_iff_range_eq_singleton {k : Type u} [Field k]
    {X Z P : Scheme.{u}} {sX : X ⟶ Spec (.of k)} (C : ProperCurve sX) (ψ : X ⟶ Z) (h : Z ⟶ P)
    [IsFinite h] : C.IsContractedBy ψ ↔ ∃ y, Set.range (C.ι ≫ ψ ≫ h) = {y} := by
  constructor
  · intro hc
    refine ⟨h (ψ C.point), Set.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩⟩
    · obtain ⟨c, hc'⟩ : C.point ∈ Set.range C.ι := C.range_ι ▸ subset_closure rfl
      exact ⟨c, by simp [hc']⟩
    · rintro _ ⟨c, rfl⟩
      simp [hc _ (C.range_ι ▸ ⟨c, rfl⟩ : C.ι c ∈ closure {C.point})]
  · rintro ⟨y, hy⟩ x hx
    have hφx : ∀ x ∈ closure ({C.point} : Set X), h (ψ x) = y := by
      intro x hx
      obtain ⟨c, rfl⟩ : x ∈ Set.range C.ι := C.range_ι ▸ hx
      have : (C.ι ≫ ψ ≫ h) c ∈ Set.range (C.ι ≫ ψ ≫ h) := ⟨c, rfl⟩
      rw [hy] at this
      simpa only [Scheme.Hom.comp_apply, Set.mem_singleton_iff] using this
    exact ((h.isDiscrete_preimage_singleton (h (ψ C.point))).eq_of_specializes
      ((specializes_iff_mem_closure.mpr hx).map ψ.continuous) rfl
      ((hφx x hx).trans (hφx _ (subset_closure rfl)).symm)).symm

/-- For a proper curve `φ : C ⟶ X` over `k` and an ample invertible sheaf `M` on `X`, the degree
of `M` on `C` vanishes iff `φ` maps `C` to a single point. -/
private theorem degreeOn_eq_zero_iff_of_isAmple {k : Type u} [Field k] {C X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsSeparated sX] [LocallyOfFiniteType sX] (φ : C ⟶ X)
    [AlgebraicGeometry.IsCurve k (φ ≫ sX)] [IsProper (φ ≫ sX)] (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    (hM : Scheme.Modules.IsAmple X M) :
    degreeOn k sX φ (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (f := φ ≫ sX)).le M
      = 0 ↔ ∃ x, Set.range φ = {x} := by
  refine ⟨fun h0 => ?_, degreeOn_eq_zero_of_range_eq_singleton sX φ M⟩
  by_contra hnc
  have : IsProper φ := IsProper.of_comp φ sX
  have : IsProper (φ.imageι ≫ sX) := isProper_imageι_comp φ sX
  have : AlgebraicGeometry.IsCurve k (φ.imageι ≫ sX) := isCurve_imageι_comp sX φ hnc
  have hpos := invertibleCurveDegree_pos_of_isAmple_of_isCurve k (φ.imageι ≫ sX)
    (topologicalKrullDim_image_le_one sX φ) _ (isAmple_pullback_of_isFinite φ.imageι M hM)
  have hd : 0 < degreeOver φ.toImage := by
    apply degreeOver_pos
    rw [dominantFunctionFieldMap_eq_functionFieldMap (f := φ.toImage)]
    exact finite_functionField_image sX φ hnc
  rw [degreeOn_eq_degreeOver_mul sX φ M hnc] at h0
  exact (mul_pos (by exact_mod_cast hd) hpos).ne' h0

/-- Let `X` be a projective variety over `k`, `F` an extremal face of `NE̅(X)`, `D` a supporting
divisor of `F`, `b ≥ 1`, and `φ : X ⟶ P` a `k`-morphism to a proper `k`-scheme with
`φ^* O ≅ 𝒪_X(bD)` for an ample invertible sheaf `O` on `P`. If `φ = ψ ≫ h` with `ψ : X ⟶ Z` to a
variety, `ψ_* 𝒪_X = 𝒪_Z`, and `h` finite, then `ψ` is a contraction of `F`; in particular `Z` is
projective, since `h^* O` is ample. -/
public theorem isContractionOfFace_of_isSupportingDivisor_of_isAmple (k : Type u) [Field k]
    {X Z P : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hXp : IsProjectiveVariety k sX)
    {F : Set (NumericalCurveClasses sX)}
    (hF : IsExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) F)
    {D : X.CartierDivisor} (hD : IsSupportingDivisor k sX F D) {b : ℕ} (hb : 1 ≤ b)
    (sP : P ⟶ Spec (.of k)) [IsProper sP] (O : P.Modules)
    [SheafOfModules.IsInvertible P.presheaf P.ringCatSheaf.2 O]
    (hO : Scheme.Modules.IsAmple P O) (φ : X ⟶ P) (hφ : φ ≫ sP = sX)
    (e : (Scheme.Modules.pullback φ).obj O ≅ MMP.CartierDivisor.sheaf (b • D))
    (ψ : X ⟶ Z) (h : Z ⟶ P) (hψh : ψ ≫ h = φ) (hZ : IsVariety k (h ≫ sP))
    (hψ : ∀ U : Z.Opens, IsIso (ψ.app U)) [IsFinite h] :
    IsContractionOfFace k sX (h ≫ sP) F ψ := by
  subst hψh
  have hZp : IsProjectiveVariety k (h ≫ sP) :=
    (AlgebraicGeometry.isProjectiveVariety_iff k _).2 ⟨hZ,
      Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.isProjectiveMorphism_of_isAmple _ _
        ((Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple _ _).mp
          (isAmple_pullback_of_isFinite h O hO))⟩
  refine ⟨hXp, hZp, by rw [← hφ, Category.assoc], hF, fun C => ?_, hψ⟩
  have hg : (C.ι ≫ ψ ≫ h) ≫ sP = C.ι ≫ sX := by simp [← hφ]
  haveI : AlgebraicGeometry.IsCurve k ((C.ι ≫ ψ ≫ h) ≫ sP) := hg ▸ C.isCurve
  haveI : IsProper ((C.ι ≫ ψ ≫ h) ≫ sP) := hg ▸ (inferInstance : IsProper (C.ι ≫ sX))
  -- `deg_C 𝒪_X(bD) = deg_C φ^* O`
  have hdeg : C.degree k (MMP.CartierDivisor.sheaf (b • D)) =
      degreeOn k sP (C.ι ≫ ψ ≫ h) C.dim_le O := by
    rw [ProperCurve.degree, ← degreeOn_eq_of_iso k _ C.ι C.dim_le e]
    exact degreeOn_pullback_eq_degreeOn_comp (sX := sX) (sY := sP) (f := ψ ≫ h) (i := C.ι) hφ
      C.dim_le O
  rw [isContractedBy_iff_range_eq_singleton C ψ h,
    ← degreeOn_eq_zero_iff_of_isAmple (sX := sP) _ O hO, ← hdeg, C.degree_sheaf_nsmul D hb,
    hD.numericalClass_mem_iff_degree_eq_zero]
  simp [Nat.one_le_iff_ne_zero.mp hb]

/-- Let `X` be a normal projective variety over `k`, `F` an extremal face of `NE̅(X)`, `D` a
supporting divisor of `F`, `b ≥ 1`, and `φ : X ⟶ ℙᴺ_k` a `k`-morphism with
`φ^* 𝒪(1) ≅ 𝒪_X(bD)`. If `φ = ψ ≫ h` with `ψ : X ⟶ Z` surjective onto a normal variety,
`ψ_* 𝒪_X = 𝒪_Z`, and `h` finite, then `ψ` is a contraction of `F`; in particular `Z` is
projective. -/
@[mmp "lem_km3b_supporting_divisor_stein_contraction"]
public theorem isContractionOfFace_of_isSupportingDivisor (k : Type u) [Field k]
    {X Z : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : IsNormalVariety k sX)
    (hXp : IsProjectiveVariety k sX) {F : Set (NumericalCurveClasses sX)}
    (hF : IsExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) F)
    {D : X.CartierDivisor} (hD : IsSupportingDivisor k sX F D) {b : ℕ} (hb : 1 ≤ b)
    {N : ℕ} (φ : X ⟶ AlgebraicGeometry.Proj (polyGrading k N)) (hφ : φ ≫ projToSpecCoeff k N = sX)
    (e : (Scheme.Modules.pullback φ).obj
        (ProjectiveSpectrum.Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)
          1) ≅ MMP.CartierDivisor.sheaf (b • D))
    (ψ : X ⟶ Z) (h : Z ⟶ AlgebraicGeometry.Proj (polyGrading k N)) (hψh : ψ ≫ h = φ)
    (hψs : Function.Surjective ψ) (hZ : IsNormalVariety k (h ≫ projToSpecCoeff k N))
    (hψ : ∀ U : Z.Opens, IsIso (ψ.app U)) [IsFinite h] :
    IsContractionOfFace k sX (h ≫ projToSpecCoeff k N) F ψ := by
  have : IsProper (projToSpecCoeff k N) :=
    Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff k N
  exact isContractionOfFace_of_isSupportingDivisor_of_isAmple k sX hXp hF hD hb _ _
    ((Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple _ _).mpr
      (Stacks.ProjectiveSpace.isAmple_twistingSheaf_one k N)) φ hφ e ψ h hψh hZ.1 hψ

end SteinContraction

end MMP.Mori

end
