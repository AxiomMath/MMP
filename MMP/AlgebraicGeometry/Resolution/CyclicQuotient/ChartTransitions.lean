module
public import MMP.AlgebraicGeometry.Intersection.Surface.Symmetry
public import MMP.AlgebraicGeometry.Resolution.CyclicQuotient.NodeRing

/-!
# Chart transitions and Laurent algebra for marked chains

Pullback of invertible sheaves to normal curves, and the Laurent-polynomial and model-ring algebra
of transitions between formal coordinate charts.

## Main results

* `degreeOn_invertibleSheaf_eq`: the degree of `𝒪(C)` on a proper curve `D` of a smooth scheme is
  the intersection number `C · D`.
* `bijective_comap_intersection`: if `C · D = 1`, the scheme-theoretic intersection `C ∩ D` is a
  single reduced `k`-point.
* `normal_pullback_twist`: the restriction of `𝒪(C)` to `C ≅ ℙ¹` is `𝒪(-b)` when `C · C = -b`.
* `laurent_unit`: the units of `K[T, T⁻¹]` are the monomials `c * T n`.
* `exists_transition_exponent`: on the overlap of consecutive charts of a chain of smooth rational
  curves, the transition `x_{j+1} = c * x_j ^ n * y_j` holds to first order.
-/

open AlgebraicGeometry hiding PrimeDivisor
open CategoryTheory Opposite MMP.Mori

namespace MMP.Resolution.MarkedChain

universe u

@[expose] public section

/-- A scheme smooth of relative dimension `2` over a field `k` is a smooth `k`-scheme. -/
theorem smoothScheme_of_smooth {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 sX] : IsSmoothScheme sX := by
  unfold IsSmoothScheme
  refine top_unique fun _ _ => ?_
  have : Smooth sX := SmoothOfRelativeDimension.smooth 2 sX
  exact MMP.Mori.mem_smoothLocus_iff.2 ⟨⊤, trivial, inferInstance⟩

open MMP.Resolution.Bridges in
/-- On a smooth scheme over an algebraically closed field, if the intersection number of a prime
divisor `C` with `D` is `n`, then `D` is a proper curve and the invertible sheaf `𝒪(C)` has degree
`n` on `D`. -/
theorem degreeOn_invertibleSheaf_eq {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]
    (hsm : IsSmoothScheme sY) (C : PrimeDivisor Y)
    [hcart : Stacks.Divisors.IsEffectiveCartierDivisor C.idealSheaf] (D : Y.IdealSheafData) (n : ℤ)
    (hnum : IsIntersectionNumber sY (Finsupp.single C 1) D (n : ℚ)) :
    ∃ (hprop : IsProper (D.subschemeι ≫ sY)) (hdim1 : topologicalKrullDim D.subscheme ≤ 1),
      haveI := hprop
      MMP.Mori.degreeOn k sY D.subschemeι hdim1
        (Stacks.Divisors.invertibleSheaf' C.idealSheaf : Y.Modules) = n := by
  have hcartD : MMP.Mori.Divisor.IsCartier (Finsupp.single C 1 : MMP.Mori.Divisor Y) :=
    MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hsm C
  obtain ⟨hprop, hdim1, hQ, hnum⟩ := hnum
  refine ⟨hprop, hdim1, ?_⟩
  have := hprop
  have hq : (MMP.Mori.Divisor.toQDivisor (Finsupp.single C 1 : MMP.Mori.Divisor Y)) =
      (Finsupp.single C 1 : MMP.Mori.QDivisor Y) := by
    refine Finsupp.ext fun E => ?_
    change ((Finsupp.single C (1 : ℤ) E : ℤ) : ℚ) = Finsupp.single C (1 : ℚ) E
    by_cases h : C = E
    · subst h
      simp
    · simp [h]
  have hnumZ : MMP.Mori.Divisor.degreeOn k sY D.subschemeι hdim1
      (Finsupp.single C 1) hcartD = n := by
    have h1 := MMP.Mori.QDivisor.intersectionNumber_toQDivisor k sY D.subschemeι hdim1
      _ hcartD (hq ▸ hQ)
    have h2 : (MMP.Mori.Divisor.degreeOn k sY D.subschemeι hdim1
      (Finsupp.single C 1) hcartD : ℚ) = (n : ℚ) := by
      rw [← h1, ← hnum]
      congr 1
    exact_mod_cast h2
  have := QuasiCompact.compactSpace_of_compactSpace sY
  obtain ⟨b'⟩ := MMP.Threefold.Resolution.nonempty_divisorialSheaf_single_iso_invertibleSheaf'
    C hcart hcartD
  rw [← hnumZ]
  have := hcartD.isInvertibleModule_divisorialSheaf
  exact MMP.Mori.degreeOn_eq_of_iso k sY D.subschemeι hdim1 b'.symm

open MMP.Resolution.Bridges in
/-- On a smooth scheme, if an integral curve `D` not contained in the prime divisor `C` meets it
with intersection number `1`, then the global sections of the scheme-theoretic intersection
`C ∩ D` form a `k`-vector space of dimension `1`. -/
theorem finrank_comap_eq_one {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]
    (hsm : IsSmoothScheme sY) (C : PrimeDivisor Y)
    [Stacks.Divisors.IsEffectiveCartierDivisor C.idealSheaf] (D : Y.IdealSheafData)
    [AlgebraicGeometry.IsIntegral D.subscheme]
    (hDC : ¬ D.supportSet ⊆ C.idealSheaf.supportSet)
    (hnum : IsIntersectionNumber sY (Finsupp.single C 1) D (1 : ℤ)) :
    letI : Algebra k Γ((C.idealSheaf.comap D.subschemeι).subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫
        ((C.idealSheaf.comap D.subschemeι).subschemeι ≫ D.subschemeι ≫ sY).appTop).hom.toAlgebra
    Module.finrank k Γ((C.idealSheaf.comap D.subschemeι).subscheme, ⊤) = 1 := by
  obtain ⟨hprop, hdim1, hdeg⟩ := degreeOn_invertibleSheaf_eq sY hsm C D 1 (by exact_mod_cast hnum)
  have := hprop
  have : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (Stacks.Divisors.invertibleSheaf' C.idealSheaf : Y.Modules) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).1
      (Stacks.Divisors.isTensorInvertible_invertibleSheaf C.idealSheaf)
  set L := (Scheme.Modules.pullback D.subschemeι).obj
    (Stacks.Divisors.invertibleSheaf' C.idealSheaf)
  have : SheafOfModules.IsInvertible D.subscheme.presheaf D.subscheme.ringCatSheaf.2 L :=
    isInvertible_pullback_obj _ _
  have hs : (Stacks.Divisors.sectionsOfTop L
      (Stacks.Divisors.pullbackCanonicalSection D.subschemeι C.idealSheaf)).eval (op ⊤) ≠ 0 := by
    rw [Stacks.Divisors.sectionsOfTop_eval_top]
    exact Stacks.Models.pullbackCanonicalSection_subschemeι_ne_zero D C.idealSheaf hDC
  obtain ⟨e⟩ := nonempty_pullback_zeroScheme_iso_unit k (D.subschemeι ≫ sY) hdim1 L _ hs
  have hdeg' := invertibleCurveDegree_eq_finrank_cohomologyOverField_zero_zeroScheme k
    (D.subschemeι ≫ sY) hdim1 L _ hs (forall_finiteDimensional_cohomologyOverField_unit k _)
  have hdeg2 : invertibleCurveDegree k (D.subschemeι ≫ sY) hdim1 L = 1 := hdeg
  rw [hdeg2, finrank_cohomologyOverField_eq_of_iso k _ e 0,
    finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections] at hdeg'
  rw [← Stacks.Divisors.zeroScheme_sectionsOfTop_pullbackCanonicalSection D.subschemeι C.idealSheaf]
  exact_mod_cast hdeg'.symm

open MMP.Resolution.Bridges in
/-- On a smooth scheme, if an integral curve `D` not contained in the prime divisor `C` meets it
with intersection number `1`, then the structure map from `k` to the global sections of the
scheme-theoretic intersection `C ∩ D` is bijective. -/
theorem bijective_comap_intersection {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]
    (hsm : IsSmoothScheme sY) (C : PrimeDivisor Y)
    [Stacks.Divisors.IsEffectiveCartierDivisor C.idealSheaf] (D : Y.IdealSheafData)
    [AlgebraicGeometry.IsIntegral D.subscheme]
    (hDC : ¬ D.supportSet ⊆ C.idealSheaf.supportSet)
    (hnum : IsIntersectionNumber sY (Finsupp.single C 1) D (1 : ℤ)) :
    Function.Bijective ((Scheme.ΓSpecIso (.of k)).inv ≫
        ((C.idealSheaf.comap D.subschemeι).subschemeι ≫ D.subschemeι ≫ sY).appTop).hom := by
  have h := finrank_comap_eq_one sY hsm C D hDC hnum
  letI : Algebra k Γ((C.idealSheaf.comap D.subschemeι).subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫
      ((C.idealSheaf.comap D.subschemeι).subschemeι ≫ D.subschemeι ≫ sY).appTop).hom.toAlgebra
  exact Algebra.finrank_eq_one_iff_bijective_algebraMap.mp h

/-- The twisting sheaves `𝒪(m)` and `𝒪(n)` on the projective line are isomorphic only if
`m = n`. -/
theorem twist_iso_unique {k : Type u} [Field k] (m n : ℤ)
    (φ : ProjectiveSpectrum.Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin 2) k) m ≅
      ProjectiveSpectrum.Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin 2) k) n) :
    m = n := by
  have hdim := (topologicalKrullDim_projectiveLineProj k).le
  have : IsProper (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff k 1) :=
    Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff k 1
  have h := @invertibleCurveDegree_eq_of_iso k _ _
    (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff k 1) _ hdim _ _
    (Stacks.PicardUFD.isInvertible_twistingSheaf k 1 m)
    (Stacks.PicardUFD.isInvertible_twistingSheaf k 1 n) φ
  rwa [invertibleCurveDegree_twistingSheaf_projectiveLineProj,
    invertibleCurveDegree_twistingSheaf_projectiveLineProj] at h

open MMP.Resolution.Bridges in
/-- On a smooth scheme, if a prime divisor `C` is isomorphic over `k` to the projective line and
has self-intersection `-b`, then the restriction of `𝒪(C)` to `C`, transported to the projective
line, is isomorphic to the twisting sheaf `𝒪(-b)`. -/
theorem normal_pullback_twist {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]
    (hsm : IsSmoothScheme sY) (C : PrimeDivisor Y) (b : ℤ)
    (hnum : IsIntersectionNumber sY (Finsupp.single C 1) C.idealSheaf (-(b : ℚ)))
    (e : projectiveLineProj k ≅ C.idealSheaf.subscheme)
    (he : e.hom ≫ C.idealSheaf.subschemeι ≫ sY =
      Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff k 1) :
    Nonempty ((Scheme.Modules.pullback e.hom).obj
        ((Scheme.Modules.pullback C.idealSheaf.subschemeι).obj
          (Stacks.Divisors.invertibleSheaf' C.idealSheaf : Y.Modules)) ≅
      ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) (-b)) := by
  have hYreg := ((isRegular_iff_regular_stalks Y).1 (isRegular_of_isSmoothScheme sY hsm)).2
  have hcart : Stacks.Divisors.IsEffectiveCartierDivisor C.idealSheaf :=
    PrimeDivisor.isEffectiveCartierDivisor_idealSheaf
      (fun x => by
        have := hYreg x
        exact IsRegularLocalRing.uniqueFactorizationMonoid _) C
  obtain ⟨d, ⟨φ⟩⟩ :=
    AlgebraicGeometry.ExceptionalCurveContraction.exists_iso_twistingSheaf_pullback (e := e)
      (Stacks.Divisors.invertibleSheaf' C.idealSheaf)
  suffices hd : d = -b by
    subst hd
    exact ⟨φ⟩
  obtain ⟨hprop, hdim1, h1⟩ :=
    degreeOn_invertibleSheaf_eq sY hsm C C.idealSheaf (-b) (by exact_mod_cast hnum)
  have := QuasiCompact.compactSpace_of_compactSpace sY
  have := hprop
  have : IsProper (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff k 1) :=
    Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff k 1
  have hdimP := (topologicalKrullDim_projectiveLineProj k).le
  have hLst : Stacks.SheafOfModules.IsInvertible Y.presheaf
      (structureSheafRing Y.toRingedSpace).property
      (Stacks.Divisors.invertibleSheaf' C.idealSheaf) :=
    Stacks.Divisors.isTensorInvertible_invertibleSheaf C.idealSheaf
  have hL : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (Stacks.Divisors.invertibleSheaf' C.idealSheaf : Y.Modules) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).1 hLst
  have hM : AlgebraicGeometry.SheafOfModules.IsInvertible C.idealSheaf.subscheme.presheaf
      C.idealSheaf.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback C.idealSheaf.subschemeι).obj
        (Stacks.Divisors.invertibleSheaf' C.idealSheaf : Y.Modules)) :=
    Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry
      C.idealSheaf.subschemeι.toLRSHom.toShHom _ hL
  have hP : AlgebraicGeometry.SheafOfModules.IsInvertible (projectiveLineProj k).presheaf
      (projectiveLineProj k).ringCatSheaf.2 ((Scheme.Modules.pullback e.hom).obj
        ((Scheme.Modules.pullback C.idealSheaf.subschemeι).obj
          (Stacks.Divisors.invertibleSheaf' C.idealSheaf : Y.Modules))) :=
    Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry
      e.hom.toLRSHom.toShHom _ hM
  have h2 : MMP.Mori.degreeOn k sY C.idealSheaf.subschemeι hdim1
      (Stacks.Divisors.invertibleSheaf' C.idealSheaf : Y.Modules) =
      invertibleCurveDegree k (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff k 1) hdimP
        ((Scheme.Modules.pullback e.hom).obj
          ((Scheme.Modules.pullback C.idealSheaf.subschemeι).obj
            (Stacks.Divisors.invertibleSheaf' C.idealSheaf : Y.Modules))) := by
    have key : ∀ (g : projectiveLineProj k ⟶ Spec (.of k)) [IsProper g],
        e.hom ≫ C.idealSheaf.subschemeι ≫ sY = g →
        invertibleCurveDegree k (C.idealSheaf.subschemeι ≫ sY) hdim1
          ((Scheme.Modules.pullback C.idealSheaf.subschemeι).obj
            (Stacks.Divisors.invertibleSheaf' C.idealSheaf : Y.Modules)) =
        invertibleCurveDegree k g hdimP ((Scheme.Modules.pullback e.hom).obj
          ((Scheme.Modules.pullback C.idealSheaf.subschemeι).obj
            (Stacks.Divisors.invertibleSheaf' C.idealSheaf : Y.Modules))) := by
      intro g _ hg
      subst hg
      unfold invertibleCurveDegree
      congr 1
      · exact finsum_congr fun n => by
          rw [finrank_cohomologyOverField_pullback k e.hom _ _ n]
      · exact finsum_congr fun n => by
          rw [finrank_cohomologyOverField_unit_pushforward k e.hom _ n]
    exact key _ he
  have h3 := (@invertibleCurveDegree_eq_of_iso k _ _
    (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff k 1) _ hdimP _ _ hP
    (Stacks.PicardUFD.isInvertible_twistingSheaf k 1 d) φ).trans
    (invertibleCurveDegree_twistingSheaf_projectiveLineProj k d)
  omega

open LaurentPolynomial Polynomial in
/-- Units of the Laurent polynomial ring over a field are the monomials `c * T n`. -/
theorem laurent_unit {K : Type u} [Field K] (u : (LaurentPolynomial K)ˣ) :
    ∃ (c : K) (n : ℤ), c ≠ 0 ∧ (u : LaurentPolynomial K) = LaurentPolynomial.C c * T n := by
  obtain ⟨n, p, hp⟩ := exists_T_pow (u : LaurentPolynomial K)
  obtain ⟨m, q, hq⟩ := exists_T_pow ((u⁻¹ : (LaurentPolynomial K)ˣ) : LaurentPolynomial K)
  have hpq : toLaurent (p * q) = toLaurent ((Polynomial.X : K[X]) ^ (n + m)) := by
    rw [map_mul, hp, hq, map_pow, Polynomial.toLaurent_X, T_pow, mul_one]
    calc (u : LaurentPolynomial K) * T (n : ℤ) *
          (((u⁻¹ : (LaurentPolynomial K)ˣ) : LaurentPolynomial K) * T (m : ℤ))
        = ((u : LaurentPolynomial K) * ((u⁻¹ : (LaurentPolynomial K)ˣ) : LaurentPolynomial K)) *
            (T (n : ℤ) * T (m : ℤ)) := by ring
      _ = T (((n + m : ℕ) : ℤ)) := by rw [Units.mul_inv, one_mul, ← T_add]; push_cast; rfl
  obtain ⟨k, hk, w, hw⟩ := (dvd_prime_pow (Polynomial.prime_X (R := K)) (n + m)).1
    ⟨q, (Polynomial.toLaurent_injective hpq).symm⟩
  obtain ⟨r, hr, hrw⟩ := Polynomial.isUnit_iff.1 w.isUnit
  have hpe : p = Polynomial.C (r⁻¹) * Polynomial.X ^ k := by
    have : p * Polynomial.C r = Polynomial.X ^ k := by rwa [hrw]
    calc p = p * Polynomial.C r * Polynomial.C (r⁻¹) := by
          rw [mul_assoc, ← map_mul, mul_inv_cancel₀ hr.ne_zero, map_one, mul_one]
      _ = _ := by rw [this]; ring
  refine ⟨r⁻¹, k - n, inv_ne_zero hr.ne_zero, ?_⟩
  have h2 : (u : LaurentPolynomial K) = (u : LaurentPolynomial K) * T n * T (-n) := by
    rw [mul_assoc, ← T_add]
    simp
  rw [h2, ← hp, hpe, map_mul, Polynomial.toLaurent_C, map_pow, Polynomial.toLaurent_X, T_pow,
    mul_one, mul_assoc, ← T_add, ← sub_eq_add_neg]

section ModelAlg

open MvPolynomial

variable {K : Type u} [Field K] {u v : Fin 2} {J : Ideal (MvPolynomial (Fin 2) K)}
 {B1 B0 A1 A0 : Type u} [CommRing B1] [CommRing B0] [CommRing A1] [CommRing A0]
 [Algebra K B1] [Algebra K B0] [Algebra K A1] [Algebra K A0]
 (e1 : MvPolynomial (Fin 2) K →ₐ[K] B1) (e0 : MvPolynomial (Fin 2) K →ₐ[K] B0)

/-- If `e0` has kernel `(X v)` or `(X u * X v)`, then `e0 (X v)` vanishes in the localization of
the target away from `e0 (X u)`. -/
theorem algebraMap_X_eq_zero_of_ker_eq (hJ : J = Ideal.span {X v} ∨ J = Ideal.span {X u * X v})
    (h0k : RingHom.ker e0 = J)
    [Algebra B0 A0] [IsLocalization.Away (e0 (X u)) A0] :
    algebraMap B0 A0 (e0 (X v)) = 0 := by
  rcases hJ with rfl | rfl
  · have : e0 (X v) = 0 := by
      rw [← RingHom.mem_ker, h0k]
      exact Ideal.subset_span rfl
    rw [this, map_zero]
  · have h : e0 (X u) * e0 (X v) = 0 := by
      rw [← map_mul, ← RingHom.mem_ker, h0k]
      exact Ideal.subset_span rfl
    have hu : IsUnit (algebraMap B0 A0 (e0 (X u))) :=
      IsLocalization.Away.algebraMap_isUnit (e0 (X u))
    have := congrArg (algebraMap B0 A0) h
    rw [map_mul, map_zero] at this
    exact (hu.mul_right_eq_zero).1 this

/-- If `e1` has kernel `J ^ 2` with `J = (X v)` or `J = (X u * X v)`, then the square of
`e1 (X v)` vanishes in the localization of the target away from `e1 (X u)`. -/
theorem algebraMap_X_sq_eq_zero_of_ker_eq_sq
    (hJ : J = Ideal.span {X v} ∨ J = Ideal.span {X u * X v})
    (h1k : RingHom.ker e1 = J ^ 2)
    [Algebra B1 A1] [IsLocalization.Away (e1 (X u)) A1] :
    algebraMap B1 A1 (e1 (X v)) ^ 2 = 0 := by
  have hu : IsUnit (algebraMap B1 A1 (e1 (X u))) :=
    IsLocalization.Away.algebraMap_isUnit (e1 (X u))
  rcases hJ with rfl | rfl
  · have : e1 (X v) ^ 2 = 0 := by
      rw [← map_pow, ← RingHom.mem_ker, h1k, Ideal.span_singleton_pow]
      exact Ideal.subset_span rfl
    rw [← map_pow, this, map_zero]
  · have h : e1 (X u) ^ 2 * e1 (X v) ^ 2 = 0 := by
      rw [← mul_pow, ← map_mul, ← map_pow, ← RingHom.mem_ker, h1k, Ideal.span_singleton_pow]
      exact Ideal.subset_span rfl
    have := congrArg (algebraMap B1 A1) h
    rw [map_mul, map_pow, map_pow, map_zero] at this
    exact ((hu.pow 2).mul_right_eq_zero).1 this

/-- If `J = (X v)` or `J = (X u * X v)` with `u ≠ v`, and `X u ^ k * P * X v ∈ J ^ 2`, then
`X v` divides `P`. -/
theorem X_dvd_of_X_pow_mul_mul_X_mem_sq
    (hJ : J = Ideal.span {X v} ∨ J = Ideal.span {X u * X v})
    (huv : u ≠ v) {k : ℕ} {P : MvPolynomial (Fin 2) K}
    (h : (X u) ^ k * P * X v ∈ J ^ 2) : (X v : MvPolynomial (Fin 2) K) ∣ P := by
  have hv : (X v : MvPolynomial (Fin 2) K) ≠ 0 := X_prime.ne_zero
  have h1 : (X v : MvPolynomial (Fin 2) K) ∣ (X u) ^ k * P := by
    rcases hJ with rfl | rfl
    · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
      have : (X v : MvPolynomial (Fin 2) K) * X v ∣ ((X u) ^ k * P) * X v := by
        rwa [← pow_two]
      exact (mul_dvd_mul_iff_right hv).1 this
    · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
      have : ((X u : MvPolynomial (Fin 2) K) ^ 2 * X v) * X v ∣ ((X u) ^ k * P) * X v := by
        have e : ((X u : MvPolynomial (Fin 2) K) * X v) ^ 2 = ((X u) ^ 2 * X v) * X v := by ring
        rwa [← e]
      exact dvd_trans (dvd_mul_left _ _) ((mul_dvd_mul_iff_right hv).1 this)
  exact ((X_prime (i := v) (σ := Fin 2) (R := K)).dvd_or_dvd h1).resolve_left fun h2 =>
    huv.symm (X_dvd_X.1 (X_prime.dvd_of_dvd_pow h2))

variable (ρB : B1 →ₐ[K] B0) (hρB : ρB.comp e1 = e0)
  [Algebra B1 A1] [Algebra B0 A0]
  [IsLocalization.Away (e1 (X u)) A1] [IsLocalization.Away (e0 (X u)) A0]
  (ρA : A1 →+* A0) (hρA : ∀ b, ρA (algebraMap B1 A1 b) = algebraMap B0 A0 (ρB b))

include hρB hρA in
/-- Every element of the kernel of `ρA` is a multiple of the image of `e1 (X v)` in the
localization `A1`. -/
theorem exists_eq_mul_algebraMap_X_of_map_eq_zero
    (hJ : J = Ideal.span {X v} ∨ J = Ideal.span {X u * X v})
    (h1s : Function.Surjective e1) (h0k : RingHom.ker e0 = J)
    {z : A1} (hz : ρA z = 0) :
    ∃ w : A1, z = w * algebraMap B1 A1 (e1 (X v)) := by
  obtain ⟨⟨b, ⟨_, m, rfl⟩⟩, hzb⟩ := IsLocalization.surj (Submonoid.powers (e1 (X u))) z
  obtain ⟨P, rfl⟩ := h1s b
  have h1 := congrArg ρA hzb
  rw [map_mul, hz, zero_mul, hρA] at h1
  obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers (e0 (X u))) A0 _).1 h1.symm
  have h4 : (X u) ^ k * P ∈ J := by
    rw [← h0k, RingHom.mem_ker, map_mul, map_pow, ← AlgHom.congr_fun hρB P]
    exact hk
  have h5 : ∃ b' : B1, e1 (X u) ^ k * e1 P = e1 (X v) * b' := by
    rcases hJ with rfl | rfl <;> obtain ⟨Q, hQ⟩ := Ideal.mem_span_singleton'.1 h4
    · exact ⟨e1 Q, by rw [← map_pow, ← map_mul, ← hQ, map_mul, mul_comm]⟩
    · refine ⟨e1 (X u * Q), ?_⟩
      rw [← map_pow, ← map_mul, ← hQ, ← map_mul]
      congr 1
      ring
  obtain ⟨b', hb'⟩ := h5
  have hx : IsUnit (algebraMap B1 A1 (e1 (X u))) := IsLocalization.Away.algebraMap_isUnit _
  have hU := hx.pow (m + k)
  refine ⟨algebraMap B1 A1 b' * ↑(hU.unit⁻¹), ?_⟩
  have e1' : z * algebraMap B1 A1 (e1 (X u) ^ m) = algebraMap B1 A1 (e1 P) := hzb
  have e2 : z * ↑hU.unit = algebraMap B1 A1 (e1 (X v)) * algebraMap B1 A1 b' := by
    calc z * ↑hU.unit = (z * algebraMap B1 A1 (e1 (X u) ^ m)) *
          algebraMap B1 A1 (e1 (X u) ^ k) := by
          rw [IsUnit.unit_spec, pow_add, map_pow, map_pow, mul_assoc]
      _ = algebraMap B1 A1 (e1 P) * algebraMap B1 A1 (e1 (X u) ^ k) := by rw [e1']
      _ = _ := by rw [← map_mul, mul_comm (e1 P), hb', map_mul]
  calc z = z * ↑hU.unit * ↑(hU.unit⁻¹) := by rw [mul_assoc, Units.mul_inv, mul_one]
    _ = _ := by rw [e2]; ring

include hρB hρA in
/-- Every element of `A1` annihilating the image of `e1 (X v)` lies in the kernel of `ρA`. -/
theorem map_eq_zero_of_mul_algebraMap_X_eq_zero
    (hJ : J = Ideal.span {X v} ∨ J = Ideal.span {X u * X v})
    (huv : u ≠ v) (h1s : Function.Surjective e1) (h1k : RingHom.ker e1 = J ^ 2)
    (h0k : RingHom.ker e0 = J) {z : A1}
    (hz : z * algebraMap B1 A1 (e1 (X v)) = 0) : ρA z = 0 := by
  obtain ⟨⟨b, ⟨_, m, rfl⟩⟩, hzb⟩ := IsLocalization.surj (Submonoid.powers (e1 (X u))) z
  obtain ⟨P, rfl⟩ := h1s b
  have hzb' : z * algebraMap B1 A1 (e1 (X u) ^ m) = algebraMap B1 A1 (e1 P) := hzb
  have h1 : algebraMap B1 A1 (e1 P * e1 (X v)) = 0 := by
    rw [map_mul, ← hzb', mul_right_comm, hz, zero_mul]
  obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers (e1 (X u))) A1 _).1 h1
  have hmem : (X u) ^ k * P * X v ∈ J ^ 2 := by
    rw [← h1k, RingHom.mem_ker, map_mul, map_mul, map_pow, mul_assoc]
    exact hk
  obtain ⟨Q, rfl⟩ := X_dvd_of_X_pow_mul_mul_X_mem_sq hJ huv hmem
  have hy0 := algebraMap_X_eq_zero_of_ker_eq e0 hJ h0k (A0 := A0)
  have hxm : IsUnit (algebraMap B0 A0 (e0 (X u)) ^ m) :=
    (IsLocalization.Away.algebraMap_isUnit (e0 (X u))).pow m
  have hρe : ∀ P, ρB (e1 P) = e0 P := fun P => AlgHom.congr_fun hρB P
  have h2 := congrArg ρA hzb'
  rw [map_mul, hρA, hρA, map_pow, hρe, hρe, map_mul, map_mul, ← map_pow] at h2
  rw [hy0, zero_mul, map_pow, map_pow] at h2
  exact (hxm.mul_left_eq_zero).1 h2

open LaurentPolynomial in
/-- If `e0` is surjective with kernel `(X v)` or `(X u * X v)`, `u ≠ v`, then the localization of
its target away from `e0 (X u)` is isomorphic to the Laurent polynomial ring `K[T, T⁻¹]`, by a
ring isomorphism compatible with the constants `K` and sending `T` to `e0 (X u)`. -/
theorem model_laurent (hJ : J = Ideal.span {X v} ∨ J = Ideal.span {X u * X v})
    (huv : u ≠ v) (h0s : Function.Surjective e0) (h0k : RingHom.ker e0 = J)
    [IsScalarTower K B0 A0] :
    ∃ Λ : LaurentPolynomial K ≃+* A0,
      Λ (T 1) = algebraMap B0 A0 (e0 (X u)) ∧
        ∀ k : K, Λ (LaurentPolynomial.C k) = algebraMap K A0 k := by
  have hx : IsUnit (algebraMap B0 A0 (e0 (X u))) :=
    IsLocalization.Away.algebraMap_isUnit _
  let Λ : LaurentPolynomial K →+* A0 := LaurentPolynomial.eval₂ (algebraMap K A0) hx.unit
  have hΛT : Λ (T 1) = algebraMap B0 A0 (e0 (X u)) := by
    simp [Λ, LaurentPolynomial.eval₂_T]
  have hΛC : ∀ k : K, Λ (LaurentPolynomial.C k) = algebraMap K A0 k := fun k =>
    LaurentPolynomial.eval₂_C _ _ _
  have hy0 := algebraMap_X_eq_zero_of_ker_eq e0 hJ h0k (A0 := A0)
  let rpoly : MvPolynomial (Fin 2) K →ₐ[K] LaurentPolynomial K :=
    MvPolynomial.aeval (fun i => if i = u then T 1 else 0)
  have hrker : ∀ a ∈ RingHom.ker e0, rpoly a = 0 := by
    intro a ha
    rw [h0k] at ha
    have hXv : rpoly (X v) = 0 := by simp [rpoly, huv.symm]
    rcases hJ with rfl | rfl
    · obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [map_mul, hXv, mul_zero]
    · obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [map_mul, map_mul, hXv, mul_zero, mul_zero]
  let r0B : B0 →ₐ[K] LaurentPolynomial K :=
    (Ideal.Quotient.liftₐ (RingHom.ker e0) rpoly hrker).comp
      (Ideal.quotientKerAlgEquivOfSurjective h0s).symm.toAlgHom
  have hr0B : ∀ P, r0B (e0 P) = rpoly P := by
    intro P
    simp only [r0B, AlgHom.comp_apply]
    have : (Ideal.quotientKerAlgEquivOfSurjective h0s).symm (e0 P) =
        Ideal.Quotient.mk (RingHom.ker e0) P := by
      rw [AlgEquiv.symm_apply_eq]; rfl
    show (Ideal.Quotient.liftₐ (RingHom.ker e0) rpoly hrker)
      ((Ideal.quotientKerAlgEquivOfSurjective h0s).symm (e0 P)) = rpoly P
    rw [this]
    rfl
  have hrT : IsUnit (r0B (e0 (X u))) := by
    have hXu : rpoly (X u) = T 1 := by simp [rpoly]
    rw [hr0B, hXu]
    exact LaurentPolynomial.isUnit_T 1
  let r0A : A0 →+* LaurentPolynomial K :=
    IsLocalization.Away.lift (e0 (X u)) (g := (r0B : B0 →+* LaurentPolynomial K)) hrT
  have hr0A : ∀ b, r0A (algebraMap B0 A0 b) = r0B b := fun b => IsLocalization.lift_eq _ _
  have hKr : ∀ k : K, r0A (algebraMap K A0 k) = LaurentPolynomial.C k := by
    intro k
    rw [IsScalarTower.algebraMap_apply K B0 A0, hr0A, AlgHom.commutes]
    rfl
  have hTr : r0A (algebraMap B0 A0 (e0 (X u))) = T 1 := by
    rw [hr0A, hr0B]
    simp [rpoly]
  have hretr : ∀ f : LaurentPolynomial K, r0A (Λ f) = f := by
    have hT1 : r0A (Λ (T 1)) = T 1 := by rw [hΛT, hTr]
    have hTm : r0A (Λ (T (-1))) = T (-1) := by
      have h1 : T (-1) * T (1 : ℤ) = (1 : LaurentPolynomial K) := by
        rw [← T_add]
        simp
      have h2 : r0A (Λ (T (-1))) * T 1 = 1 := by
        rw [← hT1, ← map_mul, ← map_mul, h1, map_one, map_one]
      exact left_inv_eq_right_inv h2 (by rw [← T_add]; simp)
    intro f
    refine LaurentPolynomial.induction_on f ?_ (fun {p q} hp hq => by rw [map_add, map_add, hp, hq])
      ?_ ?_
    · intro a
      rw [hΛC, hKr]
    · intro n a h
      have : (LaurentPolynomial.C a * T (n + 1) : LaurentPolynomial K) =
          LaurentPolynomial.C a * T n * T 1 := by
        rw [mul_assoc, ← T_add]
      rw [this, map_mul, map_mul, h, hT1]
    · intro n a h
      have : (LaurentPolynomial.C a * T (-n - 1) : LaurentPolynomial K) =
          LaurentPolynomial.C a * T (-n) * T (-1) := by
        rw [mul_assoc, ← T_add]
        congr 2
      rw [this, map_mul, map_mul, h, hTm]
  have hinj : Function.Injective Λ := Function.LeftInverse.injective hretr
  have hmem : ∀ P : MvPolynomial (Fin 2) K, algebraMap B0 A0 (e0 P) ∈ Λ.range := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C a =>
      refine ⟨LaurentPolynomial.C a, ?_⟩
      rw [hΛC, MvPolynomial.algHom_C, ← IsScalarTower.algebraMap_apply]
    | add p q hp hq =>
      rw [map_add, map_add]
      exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul, map_mul]
      by_cases hi : i = u
      · subst hi
        obtain ⟨f, hf⟩ := hp
        exact ⟨f * T 1, by rw [map_mul, hΛT, hf]⟩
      · obtain rfl : i = v := by grind
        rw [hy0, mul_zero]
        exact zero_mem _
  have hsurj : Function.Surjective Λ := by
    intro z
    obtain ⟨⟨b, ⟨_, m, rfl⟩⟩, hz⟩ := IsLocalization.surj (Submonoid.powers (e0 (X u))) z
    obtain ⟨P, rfl⟩ := h0s b
    have hz' : z * algebraMap B0 A0 (e0 (X u) ^ m) = algebraMap B0 A0 (e0 P) := hz
    obtain ⟨f, hf⟩ := hmem P
    refine ⟨f * T (-(m : ℤ)), ?_⟩
    rw [map_mul, hf, ← hz', mul_assoc]
    have : Λ (T (-(m : ℤ))) = ↑(hx.unit⁻¹ ^ m) := LaurentPolynomial.eval₂_T_neg_n _ _ m
    rw [this, map_pow]
    have hinv := Units.mul_inv hx.unit
    rw [IsUnit.unit_spec] at hinv
    rw [Units.val_pow_eq_pow_val, ← mul_pow, hinv, one_pow, mul_one]
  exact ⟨RingEquiv.ofBijective Λ ⟨hinj, hsurj⟩, hΛT, hΛC⟩

open LaurentPolynomial in
/-- Let `ρ : A1 → A0` have target `K[T, T⁻¹]` with `T = ρ xc` for a unit `xc`, let `yc` and `xs`
lie in its kernel and each generate it, with `yc ^ 2 = 0` and the annihilator of `yc` contained
in the kernel. Then `xs = c * xc ^ n * yc` for some nonzero `c : K` and `n : ℤ`. -/
theorem exists_eq_algebraMap_mul_zpow_mul {K : Type u} [Field K] {A1 A0 : Type u}
    [CommRing A1] [CommRing A0]
    [Algebra K A1] [Algebra K A0] (ρ : A1 →ₐ[K] A0) (xc yc xs : A1) (hxc : IsUnit xc)
    (Λ : LaurentPolynomial K ≃+* A0) (hΛT : Λ (T 1) = ρ xc)
    (hΛC : ∀ k : K, Λ (LaurentPolynomial.C k) = algebraMap K A0 k)
    (hyc : ρ yc = 0) (hxs : ρ xs = 0) (hyc2 : yc ^ 2 = 0)
    (hd1 : ∀ z, ρ z = 0 → ∃ w, z = w * yc) (hd2 : ∀ z, ρ z = 0 → ∃ w, z = w * xs)
    (he : ∀ z, z * yc = 0 → ρ z = 0) :
    ∃ (c : K) (u : A1ˣ) (n : ℤ), c ≠ 0 ∧ (u : A1) = xc ∧
      xs = algebraMap K A1 c * ↑(u ^ n) * yc := by
  obtain ⟨a, ha⟩ := hd1 xs hxs
  obtain ⟨b, hb⟩ := hd2 yc hyc
  have h1 : (b * a - 1) * yc = 0 := by
    have : yc = b * a * yc := hb.trans (by rw [ha]; ring)
    rw [sub_mul, one_mul, ← this, sub_self]
  have h2 : ρ b * ρ a = 1 := by
    have := he _ h1
    rw [map_sub, map_mul, map_one] at this
    exact sub_eq_zero.1 this
  let u : A1ˣ := hxc.unit
  have hρa : IsUnit (ρ a) := IsUnit.of_mul_eq_one_right (ρ b) h2
  have hLu : IsUnit (Λ.symm (ρ a)) := hρa.map Λ.symm
  obtain ⟨c, n, hc, hcn⟩ := laurent_unit hLu.unit
  have hcn' : Λ.symm (ρ a) = LaurentPolynomial.C c * T n := by
    simpa using hcn
  have hρa' : ρ a = algebraMap K A0 c * Λ (T n) := by
    have := congrArg Λ hcn'
    rwa [RingEquiv.apply_symm_apply, map_mul, hΛC] at this
  have hux : (u : A1) = xc := hxc.unit_spec
  have hTm : Λ (T (-1)) = ρ ↑(u⁻¹) :=
    left_inv_eq_right_inv (a := ρ xc) (by rw [← hΛT, ← map_mul, ← T_add]; simp)
      (by rw [← map_mul, ← hux, Units.mul_inv, map_one])
  have hTn : ∀ n : ℤ, Λ (T n) = ρ ↑(u ^ n) := by
    intro n
    refine Int.induction_on n ?_ ?_ ?_
    · simp
    · intro i ih
      have : (T ((i : ℤ) + 1) : LaurentPolynomial K) = T i * T 1 := by rw [← T_add]
      rw [this, map_mul, ih, hΛT, zpow_add_one, Units.val_mul, map_mul, hux]
    · intro i ih
      have : (T (-(i : ℤ) - 1) : LaurentPolynomial K) = T (-i) * T (-1) := by
        rw [← T_add]
        congr 1
      rw [this, map_mul, ih, hTm, zpow_sub_one, Units.val_mul, map_mul]
  refine ⟨c, u, n, hc, rfl, ?_⟩
  have hz : ρ (a - algebraMap K A1 c * ↑(u ^ n)) = 0 := by
    rw [map_sub, map_mul, AlgHom.commutes, ← hTn, hρa', sub_self]
  obtain ⟨w, hw⟩ := hd1 _ hz
  have : a = algebraMap K A1 c * ↑(u ^ n) + w * yc := by
    rw [← hw]; ring
  rw [ha, this]
  have : w * yc * yc = 0 := by rw [mul_assoc, ← pow_two, hyc2, mul_zero]
  rw [add_mul, this, add_zero]

/-- For two first-order charts presented by `ec1` and `es1`, with exceptional ideals `Jc` and `Js`,
whose localizations away from `X 0` and `X 1` respectively agree in `A1`, the image of `es1 (X 0)`
is `c * u ^ n * ec1 (X 1)` with `u` the image of `ec1 (X 0)` and `c ≠ 0`; and every element
annihilating the image of `ec1 (X 1)` lies in the kernel of `ρA`. -/
theorem exists_chart_transition {K : Type u} [Field K]
    {A1 A0 Bc1 Bc0 Bs1 Bs0 : Type u} [CommRing A1] [CommRing A0] [CommRing Bc1] [CommRing Bc0]
    [CommRing Bs1] [CommRing Bs0] [Algebra K A1] [Algebra K A0] [Algebra K Bc1] [Algebra K Bc0]
    [Algebra K Bs1] [Algebra K Bs0] (ρA : A1 →ₐ[K] A0)
    (Jc Js : Ideal (MvPolynomial (Fin 2) K))
    (hJc : Jc = Ideal.span {X 1} ∨ Jc = Ideal.span {X 0 * X 1})
    (hJs : Js = Ideal.span {X 0} ∨ Js = Ideal.span {X 1 * X 0})
    (ec1 : MvPolynomial (Fin 2) K →ₐ[K] Bc1) (ec0 : MvPolynomial (Fin 2) K →ₐ[K] Bc0)
    (es1 : MvPolynomial (Fin 2) K →ₐ[K] Bs1) (es0 : MvPolynomial (Fin 2) K →ₐ[K] Bs0)
    (hc1s : Function.Surjective ec1) (hc0s : Function.Surjective ec0)
    (hs1s : Function.Surjective es1)
    (hc1k : RingHom.ker ec1 = Jc ^ 2) (hc0k : RingHom.ker ec0 = Jc)
    (hs0k : RingHom.ker es0 = Js)
    (ρc : Bc1 →ₐ[K] Bc0) (hρc : ρc.comp ec1 = ec0)
    (ρs : Bs1 →ₐ[K] Bs0) (hρs : ρs.comp es1 = es0)
    [Algebra Bc1 A1] [Algebra Bc0 A0] [Algebra Bs1 A1] [Algebra Bs0 A0]
    [IsScalarTower K Bc0 A0]
    [IsLocalization.Away (ec1 (X 0)) A1] [IsLocalization.Away (ec0 (X 0)) A0]
    [IsLocalization.Away (es1 (X 1)) A1] [IsLocalization.Away (es0 (X 1)) A0]
    (hρAc : ∀ b, ρA (algebraMap Bc1 A1 b) = algebraMap Bc0 A0 (ρc b))
    (hρAs : ∀ b, ρA (algebraMap Bs1 A1 b) = algebraMap Bs0 A0 (ρs b)) :
    (∃ (c : K) (u : A1ˣ) (n : ℤ), c ≠ 0 ∧ (u : A1) = algebraMap Bc1 A1 (ec1 (X 0)) ∧
      algebraMap Bs1 A1 (es1 (X 0)) =
        algebraMap K A1 c * ↑(u ^ n) * algebraMap Bc1 A1 (ec1 (X 1))) ∧
    (∀ z : A1, z * algebraMap Bc1 A1 (ec1 (X 1)) = 0 → ρA z = 0) := by
  have huc : (0 : Fin 2) ≠ 1 := by decide
  have hyc0 := algebraMap_X_eq_zero_of_ker_eq ec0 hJc hc0k (A0 := A0)
  have hxs0 := algebraMap_X_eq_zero_of_ker_eq es0 hJs hs0k (A0 := A0)
  obtain ⟨Λ, hΛT, hΛC⟩ := model_laurent ec0 hJc huc hc0s hc0k (A0 := A0)
  have hρe : ∀ P, ρc (ec1 P) = ec0 P := fun P => AlgHom.congr_fun hρc P
  have hρe' : ∀ P, ρs (es1 P) = es0 P := fun P => AlgHom.congr_fun hρs P
  have hxc : IsUnit (algebraMap Bc1 A1 (ec1 (X 0))) :=
    IsLocalization.Away.algebraMap_isUnit _
  have hann : ∀ z : A1, z * algebraMap Bc1 A1 (ec1 (X 1)) = 0 → ρA z = 0 := fun _ hz =>
    map_eq_zero_of_mul_algebraMap_X_eq_zero ec1 ec0 ρc hρc ρA.toRingHom hρAc hJc huc hc1s hc1k hc0k
      hz
  refine ⟨exists_eq_algebraMap_mul_zpow_mul ρA (algebraMap Bc1 A1 (ec1 (X 0)))
    (algebraMap Bc1 A1 (ec1 (X 1)))
    (algebraMap Bs1 A1 (es1 (X 0))) hxc Λ
    (by rw [hΛT, hρAc, hρe]) hΛC
    (by rw [hρAc, hρe, hyc0])
    (by rw [hρAs, hρe', hxs0])
    (algebraMap_X_sq_eq_zero_of_ker_eq_sq ec1 hJc hc1k (A1 := A1))
    (fun _ hz => exists_eq_mul_algebraMap_X_of_map_eq_zero ec1 ec0 ρc hρc ρA.toRingHom hρAc hJc hc1s
      hc0k hz)
    (fun _ hz => exists_eq_mul_algebraMap_X_of_map_eq_zero es1 es0 ρs hρs ρA.toRingHom hρAs hJs hs1s
      hs0k hz)
    hann, hann⟩

end ModelAlg

/-- Let `E` be a chain of smooth rational curves on a smooth surface, with charts `V j` of its
thickenings given by coordinates `x j n` and `y j n`. On each overlap `V j ⊓ V (j+1)` the product
`y (j+1) * x j` is a nonzero constant at level zero, and at level one `x (j+1) = c * x j ^ n * y j`
for a unit `x j`, a nonzero `c : K` and some `n : ℤ`; moreover every element annihilating `y j` at
level one vanishes at level zero. -/
theorem exists_transition_exponent
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 2 sX]
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    {r : ℕ} (hr : 0 < r) (E : Fin r → PrimeDivisor X) (b : Fin r → ℤ)
    (hinj : Function.Injective E)
    (hrat : ∀ i, IsSmoothRationalCurve sX (E i).idealSheaf)
    (hself : ∀ i, IsIntersectionNumber sX (Finsupp.single (E i) 1) (E i).idealSheaf (-(b i)))
    (hadj : ∀ i j : Fin r, i.val + 1 = j.val →
      IsIntersectionNumber sX (Finsupp.single (E i) 1) (E j).idealSheaf 1)
    (hfar : ∀ i j : Fin r, i.val + 1 < j.val → Disjoint (E i).support (E j).support)
    (pL pR : X) (hpLR : pL ≠ pR)
    (hpL : pL ∈ (E ⟨0, hr⟩).support) (hpL' : ∀ i, i ≠ ⟨0, hr⟩ → pL ∉ (E i).support)
    (hpR : pR ∈ (E ⟨r - 1, by omega⟩).support)
    (hpR' : ∀ i, i ≠ ⟨r - 1, by omega⟩ → pR ∉ (E i).support)
    (ZL ZR : ℕ → X.IdealSheafData)
    (hZL : ∀ n, (∏ i, (E i).idealSheaf) ^ (n + 1) ≤ ZL n)
    (hZR : ∀ n, (∏ i, (E i).idealSheaf) ^ (n + 1) ≤ ZR n)
    (hZL_succ : ∀ n, ZL n = ZL (n + 1) ⊔ (∏ i, (E i).idealSheaf) ^ (n + 1))
    (hZR_succ : ∀ n, ZR n = ZR (n + 1) ⊔ (∏ i, (E i).idealSheaf) ^ (n + 1))
    (hZL_zero : ((ZL 0).support : Set X) = {pL}) (hZR_zero : ((ZR 0).support : Set X) = {pR})
    (hZL_curvilinear : ∀ n, ∃ e : (ZL n).subscheme ≅
      Spec (.of (Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ (n + 1)})),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K _)) = (ZL n).subschemeι ≫ sX)
    (hZR_curvilinear : ∀ n, ∃ e : (ZR n).subscheme ≅
      Spec (.of (Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ (n + 1)})),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K _)) = (ZR n).subschemeι ≫ sX) :
    let I := ∏ i, (E i).idealSheaf
    -- the `(n+1)`-st thickening `(n+1)E` and the trace on it of an open of `X`
    let S : ℕ → Scheme.{u} := fun n => (I ^ (n + 1)).subscheme
    let tr : ∀ n, X.Opens → (S n).Opens := fun n V => (I ^ (n + 1)).subschemeι ⁻¹ᵁ V
    -- the constants `K → Γ((n+1)E, U)`
    let σ : ∀ n (U : (S n).Opens), K →+* Γ(S n, U) := fun n U =>
      ((Scheme.ΓSpecIso (.of K)).inv ≫
        ((I ^ (n + 1)).subschemeι ≫ sX).appLE ⊤ U le_top).hom
    -- the restriction `(n+2)E → (n+1)E`
    let ρ : ∀ n (V : X.Opens), Γ(S (n + 1), tr (n + 1) V) → Γ(S n, tr n V) := fun n V =>
      ((Scheme.IdealSheafData.inclusion (pow_le_pow_right_of_le_one' le_top
          (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1))).appLE (tr (n + 1) V) (tr n V)
        (by
          simp only [tr, ← Scheme.Hom.comp_preimage,
            Scheme.IdealSheafData.inclusion_subschemeι, le_refl])).hom
    -- restriction to a smaller open of `X`
    let res : ∀ n (V W : X.Opens), W ≤ V → Γ(S n, tr n V) → Γ(S n, tr n W) :=
      fun n _ _ h => ((S n).presheaf.map (homOfLE (Scheme.Hom.preimage_mono _ h)).op).hom
    -- the exceptional ideal of chart `j`: `(y)`, `(x y)` or `(x)`
    let J : Fin (r + 1) → Ideal (MvPolynomial (Fin 2) K) := fun j =>
      if j = 0 then Ideal.span {MvPolynomial.X 1}
      else if j = Fin.last r then Ideal.span {MvPolynomial.X 0}
      else Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1}
    ∀ (V : Fin (r + 1) → X.Opens) (x y : ∀ j n, Γ(S n, tr n (V j))),
      (((I.support : Set X) ⊆ ⋃ j, (V j : Set X)) ∧
      (pL ∈ V 0 ∧ pR ∈ V (Fin.last r) ∧
          (RingHom.ker ((Scheme.IdealSheafData.inclusion (hZL 0)).app (tr 0 (V 0))).hom =
            Ideal.span {(fun j => x j 0) 0} ∧
          RingHom.ker ((Scheme.IdealSheafData.inclusion (hZR 0)).app
            (tr 0 (V (Fin.last r)))).hom = Ideal.span {(fun j => y j 0) (Fin.last r)})) ∧
      (∀ j, IsAffineOpen (tr 0 (V j)) ∧
        Function.Surjective (MvPolynomial.eval₂Hom (σ 0 (tr 0 (V j)))
          ![(fun j => x j 0) j, (fun j => y j 0) j]) ∧
        RingHom.ker (MvPolynomial.eval₂Hom (σ 0 (tr 0 (V j)))
          ![(fun j => x j 0) j, (fun j => y j 0) j]) = J j ^ (0 + 1)) ∧
      (∀ j : Fin r, ((V j.castSucc ⊓ V j.succ : X.Opens) : Set X) ∩ I.support ⊆ (E j).support) ∧
      (∀ j : Fin r,
        tr 0 (V j.castSucc ⊓ V j.succ) = (S 0).basicOpen ((fun j => x j 0) j.castSucc) ∧
        tr 0 (V j.castSucc ⊓ V j.succ) = (S 0).basicOpen ((fun j => y j 0) j.succ)) ∧
      (∀ j k : Fin (r + 1), j.val + 2 ≤ k.val →
        ((V j ⊓ V k : X.Opens) : Set X) ∩ I.support = ∅) ∧
      (∀ j : Fin r, ∃ d : K, d ≠ 0 ∧
        res 0 (V j.succ) (V j.castSucc ⊓ V j.succ) inf_le_right ((fun j => y j 0) j.succ) *
          res 0 (V j.castSucc) (V j.castSucc ⊓ V j.succ) inf_le_left
            ((fun j => x j 0) j.castSucc) = σ 0 (tr 0 (V j.castSucc ⊓ V j.succ)) d) ∧
      LocalEquations E V (fun j => x j 0) (fun j => y j 0)) →
      (∀ n, LevelEq E V n (fun j => x j n) (fun j => y j n)) →
      (∀ j n, ρ n (V j) (x j (n + 1)) = x j n ∧ ρ n (V j) (y j (n + 1)) = y j n) →
      (∀ j n, IsAffineOpen (tr n (V j)) ∧
        Function.Surjective (MvPolynomial.eval₂Hom (σ n (tr n (V j))) ![x j n, y j n]) ∧
        RingHom.ker (MvPolynomial.eval₂Hom (σ n (tr n (V j))) ![x j n, y j n]) = J j ^ (n + 1)) →
      (∀ j : Fin r, ∀ n, tr n (V j.castSucc ⊓ V j.succ) = (S n).basicOpen (x j.castSucc n) ∧
        tr n (V j.castSucc ⊓ V j.succ) = (S n).basicOpen (y j.succ n)) →
      (∀ j : Fin r, ∃ c d : K, c ≠ 0 ∧ d ≠ 0 ∧
        res 0 (V j.succ) (V j.castSucc ⊓ V j.succ) inf_le_right (y j.succ 0) *
          res 0 (V j.castSucc) (V j.castSucc ⊓ V j.succ) inf_le_left (x j.castSucc 0) =
            σ 0 (tr 0 (V j.castSucc ⊓ V j.succ)) d ∧
        ∃ (n : ℤ) (u : (Γ(S 1, tr 1 (V j.castSucc ⊓ V j.succ)))ˣ),
          (u : Γ(S 1, tr 1 (V j.castSucc ⊓ V j.succ))) =
            res 1 (V j.castSucc) (V j.castSucc ⊓ V j.succ) inf_le_left (x j.castSucc 1) ∧
          res 1 (V j.succ) (V j.castSucc ⊓ V j.succ) inf_le_right (x j.succ 1) =
            σ 1 (tr 1 (V j.castSucc ⊓ V j.succ)) c * ↑(u ^ n) *
              res 1 (V j.castSucc) (V j.castSucc ⊓ V j.succ) inf_le_left (y j.castSucc 1) ∧
          ∀ z : Γ(S 1, tr 1 (V j.castSucc ⊓ V j.succ)),
            z * res 1 (V j.castSucc) (V j.castSucc ⊓ V j.succ) inf_le_left (y j.castSucc 1) = 0 →
              ρ 0 (V j.castSucc ⊓ V j.succ) z = 0) := by
  intro I S tr σ ρ res J V x y hP hlev hcomp hchart hov j
  obtain ⟨-, -, -, -, -, -, hd0, -⟩ := hP
  obtain ⟨d, hd, hd0j⟩ := hd0 j
  let ρR : ∀ n (V : X.Opens), Γ(S (n + 1), tr (n + 1) V) →+* Γ(S n, tr n V) := fun n V =>
    ((Scheme.IdealSheafData.inclusion (pow_le_pow_right_of_le_one' le_top
          (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1))).appLE (tr (n + 1) V) (tr n V)
        (by
          simp only [tr, ← Scheme.Hom.comp_preimage,
            Scheme.IdealSheafData.inclusion_subschemeι, le_refl])).hom
  have hρσ : ∀ n (V : X.Opens) (k : K),
      ρR n V (σ (n + 1) (tr (n + 1) V) k) = σ n (tr n V) k := by
    intro n V k
    refine map_constants_hom ((I ^ (n + 1)).subschemeι ≫ sX) ((I ^ (n + 1 + 1)).subschemeι ≫ sX)
      (Scheme.IdealSheafData.inclusion (pow_le_pow_right_of_le_one' le_top
          (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1)))
      (by rw [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]) _ _ _ k
  have hresσ : ∀ n (V W : X.Opens) (h : W ≤ V) (k : K),
      res n V W h (σ n (tr n V) k) = σ n (tr n W) k := by
    intro n V W h k
    exact map_constants_restrict _ _ _ _ k
  have hρres : ∀ n (V W : X.Opens) (h : W ≤ V) (z : Γ(S (n + 1), tr (n + 1) V)),
      ρ n W (res (n + 1) V W h z) = res n V W h (ρ n V z) := by
    intro n V W h z
    show (CommRingCat.Hom.hom _) ((CommRingCat.Hom.hom _) z) =
      (CommRingCat.Hom.hom _) ((CommRingCat.Hom.hom _) z)
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE,
      Scheme.Hom.appLE_map]
  letI algK : ∀ n (U : (S n).Opens), Algebra K Γ(S n, U) := fun n U => (σ n U).toAlgebra
  let ec : ∀ n, MvPolynomial (Fin 2) K →ₐ[K] Γ(S n, tr n (V j.castSucc)) := fun n =>
    MvPolynomial.aeval ![x j.castSucc n, y j.castSucc n]
  let es : ∀ n, MvPolynomial (Fin 2) K →ₐ[K] Γ(S n, tr n (V j.succ)) := fun n =>
    MvPolynomial.aeval ![x j.succ n, y j.succ n]
  have hecs : ∀ n, Function.Surjective (ec n) := fun n => (hchart j.castSucc n).2.1
  have hess : ∀ n, Function.Surjective (es n) := fun n => (hchart j.succ n).2.1
  have heck : ∀ n, RingHom.ker (ec n) = J j.castSucc ^ (n + 1) := fun n =>
    (hchart j.castSucc n).2.2
  have hesk : ∀ n, RingHom.ker (es n) = J j.succ ^ (n + 1) := fun n => (hchart j.succ n).2.2
  let ρA : ∀ n (V : X.Opens), Γ(S (n + 1), tr (n + 1) V) →ₐ[K] Γ(S n, tr n V) := fun n V =>
    { ρR n V with commutes' := fun k => hρσ n V k }
  have hρc : (ρA 0 (V j.castSucc)).comp (ec 1) = ec 0 := by
    refine MvPolynomial.algHom_ext fun i => ?_
    obtain ⟨h1, h2⟩ := hcomp j.castSucc 0
    fin_cases i
    · show ρA 0 _ (ec 1 (MvPolynomial.X 0)) = ec 0 (MvPolynomial.X 0)
      simp only [ec, MvPolynomial.aeval_X]
      exact h1
    · show ρA 0 _ (ec 1 (MvPolynomial.X 1)) = ec 0 (MvPolynomial.X 1)
      simp only [ec, MvPolynomial.aeval_X]
      exact h2
  have hρs : (ρA 0 (V j.succ)).comp (es 1) = es 0 := by
    refine MvPolynomial.algHom_ext fun i => ?_
    obtain ⟨h1, h2⟩ := hcomp j.succ 0
    fin_cases i
    · show ρA 0 _ (es 1 (MvPolynomial.X 0)) = es 0 (MvPolynomial.X 0)
      simp only [es, MvPolynomial.aeval_X]
      exact h1
    · show ρA 0 _ (es 1 (MvPolynomial.X 1)) = es 0 (MvPolynomial.X 1)
      simp only [es, MvPolynomial.aeval_X]
      exact h2
  have hJc : J j.castSucc = Ideal.span {MvPolynomial.X 1} ∨
      J j.castSucc = Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1} := by
    have hl : j.castSucc ≠ Fin.last r := (Fin.castSucc_lt_last j).ne
    by_cases h0 : j.castSucc = 0
    · exact .inl (by simp [J, h0])
    · exact .inr (by simp [J, h0, hl])
  have hJs : J j.succ = Ideal.span {MvPolynomial.X 0} ∨
      J j.succ = Ideal.span {MvPolynomial.X 1 * MvPolynomial.X 0} := by
    have h0 : j.succ ≠ 0 := Fin.succ_ne_zero j
    by_cases hl : j.succ = Fin.last r
    · have h0' : (Fin.last r : Fin (r + 1)) ≠ 0 := hl ▸ h0
      exact .inl (by simp [J, hl, h0'])
    · exact .inr (by simp [J, h0, hl, mul_comm])
  letI algc : ∀ n, Algebra Γ(S n, tr n (V j.castSucc)) Γ(S n, tr n (V j.castSucc ⊓ V j.succ)) :=
    fun n => ((S n).presheaf.map (homOfLE (Scheme.Hom.preimage_mono _
      (inf_le_left : V j.castSucc ⊓ V j.succ ≤ V j.castSucc))).op).hom.toAlgebra
  letI algs : ∀ n, Algebra Γ(S n, tr n (V j.succ)) Γ(S n, tr n (V j.castSucc ⊓ V j.succ)) :=
    fun n => ((S n).presheaf.map (homOfLE (Scheme.Hom.preimage_mono _
      (inf_le_right : V j.castSucc ⊓ V j.succ ≤ V j.succ))).op).hom.toAlgebra
  have hlocc : ∀ n,
      IsLocalization.Away (x j.castSucc n) Γ(S n, tr n (V j.castSucc ⊓ V j.succ)) :=
    fun n => (hchart j.castSucc n).1.isLocalization_of_eq_basicOpen (x j.castSucc n)
      (homOfLE (Scheme.Hom.preimage_mono _
        (inf_le_left : V j.castSucc ⊓ V j.succ ≤ V j.castSucc)))
      (hov j n).1
  have hlocs : ∀ n, IsLocalization.Away (y j.succ n) Γ(S n, tr n (V j.castSucc ⊓ V j.succ)) :=
    fun n => (hchart j.succ n).1.isLocalization_of_eq_basicOpen (y j.succ n)
      (homOfLE (Scheme.Hom.preimage_mono _ (inf_le_right : V j.castSucc ⊓ V j.succ ≤ V j.succ)))
      (hov j n).2
  have hec : ∀ n, ec n (MvPolynomial.X 0) = x j.castSucc n := fun n => by simp [ec]
  have hes : ∀ n, es n (MvPolynomial.X 1) = y j.succ n := fun n => by simp [es]
  haveI : IsLocalization.Away (ec 1 (MvPolynomial.X 0))
      Γ(S 1, tr 1 (V j.castSucc ⊓ V j.succ)) := by
    rw [hec]
    exact hlocc 1
  haveI : IsLocalization.Away (ec 0 (MvPolynomial.X 0))
      Γ(S 0, tr 0 (V j.castSucc ⊓ V j.succ)) := by
    rw [hec]
    exact hlocc 0
  haveI : IsLocalization.Away (es 1 (MvPolynomial.X 1))
      Γ(S 1, tr 1 (V j.castSucc ⊓ V j.succ)) := by
    rw [hes]
    exact hlocs 1
  haveI : IsLocalization.Away (es 0 (MvPolynomial.X 1))
      Γ(S 0, tr 0 (V j.castSucc ⊓ V j.succ)) := by
    rw [hes]
    exact hlocs 0
  haveI : IsScalarTower K Γ(S 0, tr 0 (V j.castSucc)) Γ(S 0, tr 0 (V j.castSucc ⊓ V j.succ)) :=
    IsScalarTower.of_algebraMap_eq fun k => (hresσ 0 _ _ inf_le_left k).symm
  obtain ⟨⟨c, u, n, hc, hu, hrel⟩, hann⟩ := exists_chart_transition (ρA 0 (V j.castSucc ⊓ V j.succ))
    (J j.castSucc) (J j.succ) hJc hJs (ec 1) (ec 0) (es 1) (es 0) (hecs 1) (hecs 0) (hess 1)
    (heck 1) ((heck 0).trans (by simp)) ((hesk 0).trans (by simp))
    (ρA 0 (V j.castSucc)) hρc (ρA 0 (V j.succ)) hρs
    (fun b => hρres 0 (V j.castSucc) _ inf_le_left b)
    (fun b => hρres 0 (V j.succ) _ inf_le_right b)
  have e1 : es 1 (MvPolynomial.X 0) = x j.succ 1 := by simp [es]
  have e2 : ec 1 (MvPolynomial.X 1) = y j.castSucc 1 := by simp [ec]
  refine ⟨c, d, hc, hd, hd0j, n, u, ?_, ?_, ?_⟩
  · rw [hu, hec]; rfl
  · rwa [e1, e2] at hrel
  · exact fun z hz => hann z (by rwa [e2])

end

end MMP.Resolution.MarkedChain
