module

public import MMP.AlgebraicGeometry.Intersection.HilbertPolynomialCurveDegree
public import MMP.AlgebraicGeometry.Intersection.AmpleDegreePositive
public import MMP.AlgebraicGeometry.Intersection.SelfIntersectionHilbertDegree
public import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
public import StacksFrontier.AlgebraicGeometry.ClosedSubschemeProjectiveSpace.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeriesChartRatio

/-!
# A uniform arithmetic-genus bound for integral curves of bounded degree

Let `k` be an algebraically closed field of characteristic zero and `C ⊆ ℙᴺ_k` an integral
closed subscheme of dimension one and degree `e`. Then its arithmetic genus satisfies
`0 ≤ p_a(C) ≤ (e - 1)(e - 2)/2`: global functions on `C` are constants, so
`p_a(C) = h¹(C, 𝒪_C) ≥ 0`, and a general linear projection maps `C` finitely and birationally
onto a plane curve of degree `e`, whose arithmetic genus is `(e - 1)(e - 2)/2` and bounds that
of `C`.

Consequently, for a closed subscheme `X ⊆ ℙᴹ_k` with polarization `L = 𝒪(1)|_X` and a natural
number `d`, there are finitely many integers `c` such that every effective 1-cycle
`Z₀ = ∑ nᵢ Cᵢ` of degree `d` on `X` is the push-forward of the fundamental 1-cycle of a closed
subscheme `Z ⊆ X × ℙ¹` of dimension at most one whose Hilbert polynomial for the product
polarization `L ⊠ 𝒪(1)` is `m ↦ d m + c` for one of them: place `nᵢ` disjoint copies of each
`Cᵢ` over distinct points of `ℙ¹`; then `χ(Z, (L ⊠ 𝒪(1))^{⊗ m}) = d m + ∑ nᵢ (1 - p_a(Cᵢ))`.

## Main results

* `MMP.Mori.arithmeticGenus_bound_projectiveSpace`: the genus bound for integral curves in
  `ℙᴺ_k`, and the finiteness of the Hilbert polynomials representing effective 1-cycles of fixed
  degree on a projective `X`.

## Implementation notes

The degree of `C ⊆ ℙᴺ_k` is `MMP.Mori.hilbertDegree` with respect to
`Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf`, and the arithmetic genus is
`MMP.Mori.arithmeticGenus`, `1 - χ(𝒪_C)`. The bound `p_a ≤ (e - 1)(e - 2)/2` is stated as
`2 p_a ≤ (e - 1)(e - 2)` in `ℤ`.

The product `X × ℙ¹` is the relative projective line `ℙ¹_X = projectiveSpaceOver 1 X`, and the
`m`-th power of the product polarization is the twist of `𝒪` by `p^* L` and `𝒪_{ℙ¹_X}(1)`,
both with exponent `m`, where `p : ℙ¹_X ⟶ X` is the projection; `p^* L` is written as the
pull-back of `𝒪(1)` along `p ≫ j`. The fundamental 1-cycle of `Z` is the 1-cycle on `Z` whose
coefficient at a proper curve with generic point `η` is the length of `𝒪_{Z,η}`; its push-forward
to `X` is `MMP.Mori.OneCycle.pushforward`.

## References

* [R. Hartshorne, *Algebraic geometry*][Har77], IV.3, III.Ex. 5.3
* [J. Kollár, *Rational curves on algebraic varieties*][Kollar96], I.3–I.6
-/

open CategoryTheory AlgebraicGeometry Stacks.AmpleProjectiveImmersion

universe u

namespace MMP.Mori.GenusBound

private theorem hasNoEmbeddedPoints_of_isIntegral (W : Scheme.{u}) [IsIntegral W] :
    HasNoEmbeddedPoints W := by
  have h : Stacks.Divisors.schemeWeaklyAssociatedPoints W = {genericPoint W} :=
    (weaklyAssociatedPointsOfScheme_eq_genericPoints W).trans genericPoints_eq_singleton
  intro x ⟨hx, x', hx', hs, hne⟩
  have h1' : x ∈ Stacks.Divisors.schemeWeaklyAssociatedPoints W :=
    associatedPoints_subset_weaklyAssociatedPoints _ hx
  have h2' : x' ∈ Stacks.Divisors.schemeWeaklyAssociatedPoints W :=
    associatedPoints_subset_weaklyAssociatedPoints _ hx'
  rw [h] at h1' h2'
  exact hne (by rw [Set.mem_singleton_iff.mp h1', Set.mem_singleton_iff.mp h2'])

open AlgebraicGeometry.ProjectiveSpectrum.Proj in
private theorem exists_planeCurveData (k : Type u) [Field k] {C : Scheme.{u}}
    (i : C ⟶ projectiveSpaceOver 2 (Spec (.of k)))
    [IsClosedImmersion i] [IsIntegral C] (hC : topologicalKrullDim C = 1) :
    ∃ (D : PlaneCurveData k) (ε : C ≅ D.Z),
      ε.hom ≫ D.toSpec = i ≫ projectiveSpaceOver 2 (Spec (.of k)) ↘ Spec (.of k) ∧
      ε.hom ≫ D.i = i ≫ (Stacks.ProjectiveCohomology.projModelIso k 2).inv := by
  let e := Stacks.ProjectiveCohomology.projModelIso k 2
  have : Nonempty C := inferInstance
  let i' : C ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k 2) :=
    i ≫ e.inv
  haveI : IsClosedImmersion i' := inferInstance
  have hdim : ∀ W ∈ irreducibleComponents C, topologicalKrullDim W = 1 := by
    intro W hW
    rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hW
    subst hW
    rw [← hC]
    exact IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ C).isHomeomorph
  refine ⟨planeCurveData k i' (hasNoEmbeddedPoints_of_isIntegral C) hdim, Iso.refl _, ?_,
    Category.id_comp _⟩
  show 𝟙 C ≫ i' ≫ _ = _
  rw [Category.id_comp]
  have h1 : e.inv ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff k 2 =
      projectiveSpaceOver 2 (Spec (.of k)) ↘ Spec (.of k) := by
    rw [Stacks.ProjectiveCohomology.projToSpecCoeff_eq_projModelToSpec,
      ← Stacks.ProjectiveCohomology.projModelIso_hom_structureMorphism k 2, Iso.inv_hom_id_assoc]
    rfl
  simp only [i', Category.assoc, h1]

private theorem isProper_projToSpecCoeff (k : Type u) [Field k] (n : ℕ) :
    IsProper (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff k n) := by
  rw [Stacks.ProjectiveCohomology.projToSpecCoeff_eq_projModelToSpec]
  exact Stacks.ProjectiveCohomology.isProper_projModelToSpec k n

open AlgebraicGeometry.ProjectiveSpectrum.Proj in
/-- A plane curve is proper over the base field. -/
private theorem isProper_toSpec {k : Type u} [Field k] (D : PlaneCurveData k) :
    IsProper D.toSpec := by
  have := D.isClosedImmersion
  have := isProper_projToSpecCoeff k 2
  exact inferInstanceAs
    (IsProper (D.i ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff k 2))

/-- `2 · ⌊(d - 1)(d - 2) / 2⌋ = (d - 1)(d - 2)` for `d ≥ 1`, the product being even. -/
private theorem two_mul_div_two_eq (d : ℕ) (hd : 0 < d) :
    2 * (((d - 1) * (d - 2) / 2 : ℕ) : ℤ) = ((d : ℤ) - 1) * ((d : ℤ) - 2) := by
  obtain ⟨_ | m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  · norm_num
  have h : (2 : ℤ) * ((m * (m + 1) / 2 : ℕ) : ℤ) = m * (m + 1) := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.even_mul_succ_self m).two_dvd
  rw [show (m + 1 + 1 - 1) * (m + 1 + 1 - 2) = m * (m + 1) by simp [mul_comm], h]
  push_cast
  ring

open AlgebraicGeometry.ProjectiveSpectrum.Proj in
/-- The arithmetic genus of a plane curve is `(deg - 1)(deg - 2)/2`. -/
private theorem two_mul_arithmeticGenus_eq_planeCurveData (k : Type u) [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (i : C ⟶ projectiveSpaceOver 2 (Spec (.of k)))
    [IsClosedImmersion i] [IsIntegral C] (hC : topologicalKrullDim C = 1) (D : PlaneCurveData k)
    (ε : C ≅ D.Z)
    (hε : ε.hom ≫ D.toSpec = i ≫ projectiveSpaceOver 2 (Spec (.of k)) ↘ Spec (.of k)) :
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
      (i ≫ projectiveSpaceOver 2 (Spec (.of k)) ↘ Spec (.of k))
    2 * arithmeticGenus (i ≫ projectiveSpaceOver 2 (Spec (.of k)) ↘ Spec (.of k)) =
      ((D.deg : ℤ) - 1) * ((D.deg : ℤ) - 2) := by
  haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
    (i ≫ projectiveSpaceOver 2 (Spec (.of k)) ↘ Spec (.of k))
  have := isProper_toSpec D
  have hsC : IsProper (i ≫ projectiveSpaceOver 2 (Spec (.of k)) ↘ Spec (.of k)) := by
    rw [← hε]
    infer_instance
  have h1 := (arithmeticGenus_eq_finrank_cohomologyOverField_one
    (i ≫ projectiveSpaceOver 2 (Spec (.of k)) ↘ Spec (.of k)) hC.le).2.1
  have e1 := (AlgebraicGeometry.structureSheafCohomologyIsoCohomologyOverField k
    (i ≫ projectiveSpaceOver 2 (Spec (.of k)) ↘ Spec (.of k)) 1).toLinearEquiv.finrank_eq
  have hg : (Module.finrank k (cohomologyOverField k
      (i ≫ projectiveSpaceOver 2 (Spec (.of k)) ↘ Spec (.of k))
      (SheafOfModules.unit C.ringCatSheaf) 1)) = genus D.toSpec := by
    rw [← e1, ← AlgebraicGeometry.genus_eq_finrank_structureSheafCohomology, ← hε,
      AlgebraicGeometry.genus_comp_iso_eq k D.toSpec ε]
  rw [h1, hg, genus_planeCurve]
  exact two_mul_div_two_eq D.deg D.deg_pos

section Cartier

open Stacks.ProjectiveSpace.Cohomology Stacks.AlgebraicGeometry.ProjPolyChart Opposite
open MonoidalCategory AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover (twistMultiplicationIso)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The monoidal structure on the category of sheaves of modules on a scheme `X`, given by the
sheafified tensor product over the structure sheaf. -/
noncomputable local instance hypersurfaceModulesMonoidal (X : AlgebraicGeometry.Scheme.{u}) :
    MonoidalCategory X.Modules :=
  Stacks.SheafOfModules.sheafTensorMonoidal X.sheaf.obj X.ringCatSheaf.property

private theorem finrank_cohomologyOverField_twist (k : Type u) [Field k] (m : ℤ) (q : ℕ) :
    Module.finrank k (cohomologyOverField k (projToSpecCoeff k 2)
      (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheafModule (polyGrading k 2) m) q) =
    Module.finrank k (twistCohomology k 2 m q) :=
  (cohomologyOverFieldIsoRestrictScalarsCoeffScalar k 2 _ q).toLinearEquiv.finrank_eq

private theorem finrank_twistCohomology_eq_zero (k : Type u) [Field k] (m : ℤ) (q : ℕ)
    (hq : ¬(q = 0 ∧ 0 ≤ m ∨ q = 2 ∧ m < 0)) :
    Module.finrank k (twistCohomology k 2 m q) = 0 :=
  have := ModuleCat.subsingleton_of_isZero (isZero_twistCohomology k 2 m q hq)
  Module.finrank_zero_of_subsingleton

private theorem two_mul_eulerCharacteristic_twist (k : Type u) [Field k] (m : ℤ)
    [IsProper (projToSpecCoeff k 2)]
    [(AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheafModule (polyGrading k 2)
        m).IsCoherent] :
    2 * eulerCharacteristic k (projToSpecCoeff k 2)
      (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheafModule (polyGrading k 2) m) =
      (m + 1) * (m + 2) := by
  rw [eulerCharacteristic_eq_finsum]
  simp only [finrank_cohomologyOverField_twist]
  have hsupp : (Function.support fun q : ℕ => (-1 : ℤ) ^ q *
      (Module.finrank k (twistCohomology k 2 m q) : ℤ)) ⊆ ↑(Finset.range 3) := by
    intro q hq
    simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hq
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hge
    exact hq.2 (by simp [finrank_twistCohomology_eq_zero k m q (by omega)])
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  rw [finrank_twistCohomology_eq_zero k m 1 (by simp)]
  rcases le_or_gt 0 m with hm | hm
  · rw [finrank_twistCohomology_eq_zero k m 2 (by omega),
      (twistCohomologyIsoHomogeneous k 2 m hm).toLinearEquiv.finrank_eq,
      MvPolynomial.finrank_homogeneousSubmodule]
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n := ⟨m.toNat, by omega⟩
    simp only [Int.toNat_natCast, Fintype.card_fin]
    have h3 : (2 + 1 + n - 1).choose n = (n + 2) * (n + 1) / 2 := by
      rw [show 2 + 1 + n - 1 = n + 2 by omega, Nat.choose_symm_add, Nat.choose_two_right]
      simp [Nat.add_sub_cancel]
    rw [h3]
    have hev : 2 ∣ (n + 2) * (n + 1) := by
      have := (Nat.even_mul_succ_self (n + 1)).two_dvd
      rwa [mul_comm] at this
    have h6 : (2 : ℤ) * (((n + 2) * (n + 1) / 2 : ℕ) : ℤ) = ((n : ℤ) + 2) * ((n : ℤ) + 1) := by
      exact_mod_cast Nat.mul_div_cancel' hev
    simp only [pow_zero, one_mul, Nat.cast_zero, mul_zero, add_zero]
    linarith
  · rw [finrank_twistCohomology_eq_zero k m 0 (by omega)]
    obtain ⟨d, rfl⟩ : ∃ d : ℕ, m = -(d : ℤ) := ⟨(-m).toNat, by omega⟩
    rw [finrank_twistCohomology_plane_top]
    have := two_mul_div_two_eq d (by omega)
    simp only [Nat.cast_zero, mul_zero, zero_add, even_two, Even.neg_one_pow, one_mul]
    linarith

/-- transport of the Euler characteristic along an isomorphism `e : Z ≅ Z'` over a base. -/
private theorem eulerCharacteristic_pullback_iso (k : Type u) [Field k] {Z Z' : Scheme.{u}}
    (e : Z ≅ Z') (q : Z' ⟶ Spec (.of k)) [IsProper q] [IsLocallyNoetherian Z]
    (G : Z'.Modules) [G.IsCoherent] [((Scheme.Modules.pullback e.hom).obj G).IsCoherent]
    [IsProper (e.hom ≫ q)] :
    eulerCharacteristic k (e.hom ≫ q) ((Scheme.Modules.pullback e.hom).obj G) =
      eulerCharacteristic k q G := by
  have hpush : ((Scheme.Modules.pushforward e.hom).obj ((Scheme.Modules.pullback e.hom).obj
      G)).IsCoherent :=
    Stacks.AlgebraicGeometry.RelativeSerreVanishing.isCoherent_of_iso
        (Stacks.Cohomology.SchemeIso.pushforwardPullbackIso e G).symm
      inferInstance
  rw [← eulerCharacteristic_pushforward_of_isClosedImmersion k e.hom q _ ‹_› hpush]
  exact eulerCharacteristic_eq_of_iso k q (Stacks.Cohomology.SchemeIso.pushforwardPullbackIso e G)

private theorem eulerCharacteristic_congr_hom (k : Type u) [Field k] {X : Scheme.{u}}
    (f g : X ⟶ Spec (.of k)) (h : f = g) [IsProper f] [IsProper g] (F : X.Modules) [F.IsCoherent] :
    eulerCharacteristic k f F = eulerCharacteristic k g F := by
  subst h
  rfl

private theorem two_mul_chi_pullback_twist (k : Type u) [Field k] (D : PlaneCurveData k) (t : ℤ)
    [IsProper D.toSpec]
    [((Scheme.Modules.pullback D.i).obj
      (twistingSheafModule (polyGrading k 2) t)).IsCoherent] :
    2 * eulerCharacteristic k D.toSpec ((Scheme.Modules.pullback D.i).obj
      (twistingSheafModule (polyGrading k 2) t)) =
      (t + 1) * (t + 2) - (t - D.deg + 1) * (t - D.deg + 2) := by
  have := D.isClosedImmersion
  haveI := isProper_projToSpecCoeff k 2
  let F : polyGrading k 2 D.deg := ⟨D.F, D.isHomogeneous⟩
  have hgen := MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin (2 + 1)) k
  let L := twistingSheafModule (polyGrading k 2) (D.deg : ℤ)
  let s := Stacks.PresheafOfModules.sectionOfTop L.val (degreeSection (polyGrading k 2) D.deg F)
  have ht : s.eval (op ⊤) = degreeSection (polyGrading k 2) D.deg F :=
    Stacks.PresheafOfModules.sectionOfTop_val_top _ _
  have hs : s.eval (op ⊤) ≠ 0 :=
    ht ▸ Stacks.ProjectiveSpace.Cohomology.degreeSection_ne_zero k 2 D.deg F D.F_ne_zero
  have hreg := isRegularSection_of_eval_top_ne_zero L s hs
  let M := twistingSheafModule (polyGrading k 2) (t - D.deg)
  obtain ⟨h, hse⟩ := shortExact_zeroScheme_twist_of_isRegularSection
    (AlgebraicGeometry.Proj (polyGrading k 2)) L s hreg M
  have hJ : D.i.ker = zeroScheme (AlgebraicGeometry.Proj (polyGrading k 2)) L (s.eval (op ⊤)) := by
    rw [ht]
    exact projectiveSpace_ker_eq_zeroScheme_of_idealOfClosedSubscheme_eq_span k 3 D.i F
      D.span_eq
  let J := zeroScheme (AlgebraicGeometry.Proj (polyGrading k 2)) L (s.eval (op ⊤))
  have hjker : J.subschemeι.ker = D.i.ker := J.ker_subschemeι.trans hJ.symm
  have hφ : IsClosedImmersion.lift J.subschemeι D.i (le_of_eq hjker) ≫ J.subschemeι = D.i :=
    IsClosedImmersion.lift_fac _ _ _
  have _hiso : IsIso (IsClosedImmersion.lift J.subschemeι D.i (le_of_eq hjker)) :=
    IsClosedImmersion.isIso_of_ker_eq D.i J.subschemeι _ hφ hjker.symm
  let e0 : D.Z ≅ J.subscheme := asIso (IsClosedImmersion.lift J.subschemeι D.i (le_of_eq hjker))
  let eN : (M ⊗ L : (AlgebraicGeometry.Proj (polyGrading k 2)).Modules) ≅
      twistingSheafModule (polyGrading k 2) t :=
    twistMultiplicationIso (polyGrading k 2)
      (Stacks.AlgebraicGeometry.ProjDegreeOne.iSup_basicOpen_degreeOne_eq_top _ hgen) (t - D.deg)
          D.deg ≪≫
      eqToIso (congrArg (twistingSheaf (polyGrading k 2)) (sub_add_cancel t (D.deg : ℤ)))
  haveI : IsLocallyNoetherian J.subscheme := isLocallyNoetherian_of_isClosedImmersion J.subschemeι
  haveI : IsLocallyNoetherian D.Z := isLocallyNoetherian_of_isClosedImmersion D.i
  haveI hcM : M.IsCoherent := inferInstance
  haveI hcO : (twistingSheafModule (polyGrading k 2) t).IsCoherent := inferInstance
  haveI hcN : (M ⊗ L : (AlgebraicGeometry.Proj (polyGrading k 2)).Modules).IsCoherent :=
    Stacks.AlgebraicGeometry.RelativeSerreVanishing.isCoherent_of_iso eN.symm hcO
  let S := ShortComplex.mk _ _ h
  haveI : S.X₃.IsCoherent :=
      Stacks.AlgebraicGeometry.ProperMapping.isCoherent_X₃_of_shortExact_modules hse hcM hcN
  have hadd := eulerCharacteristic_add_of_shortExact k (projToSpecCoeff k 2) hse
  have hNO := eulerCharacteristic_eq_of_iso k (projToSpecCoeff k 2) eN
  have hO := two_mul_eulerCharacteristic_twist k t
  have hMM := two_mul_eulerCharacteristic_twist k (t - D.deg)
  haveI hcpb : ((Scheme.Modules.pullback J.subschemeι).obj
      (M ⊗ L : (AlgebraicGeometry.Proj (polyGrading k 2)).Modules)).IsCoherent :=
    isCoherent_pullback J.subschemeι _
  haveI hpush : ((Scheme.Modules.pushforward J.subschemeι).obj
      ((Scheme.Modules.pullback J.subschemeι).obj
        (M ⊗ L : (AlgebraicGeometry.Proj (polyGrading k 2)).Modules))).IsCoherent :=
    inferInstanceAs S.X₃.IsCoherent
  have hT := eulerCharacteristic_pushforward_of_isClosedImmersion k J.subschemeι
    (projToSpecCoeff k 2) ((Scheme.Modules.pullback J.subschemeι).obj
        (M ⊗ L : (AlgebraicGeometry.Proj (polyGrading k 2)).Modules)) hcpb hpush
  haveI hcpe0 : ((Scheme.Modules.pullback e0.hom).obj
      ((Scheme.Modules.pullback J.subschemeι).obj
        (M ⊗ L : (AlgebraicGeometry.Proj (polyGrading k 2)).Modules))).IsCoherent :=
    isCoherent_pullback e0.hom _
  have hf : e0.hom ≫ J.subschemeι ≫ projToSpecCoeff k 2 = D.toSpec := by
    show e0.hom ≫ J.subschemeι ≫ projToSpecCoeff k 2 = D.i ≫ projToSpecCoeff k 2
    rw [← hφ, Category.assoc]
    rfl
  haveI hpr0 : IsProper (e0.hom ≫ J.subschemeι ≫ projToSpecCoeff k 2) := inferInstance
  have hX1 := eulerCharacteristic_pullback_iso k e0 (J.subschemeι ≫ projToSpecCoeff k 2)
    ((Scheme.Modules.pullback J.subschemeι).obj
        (M ⊗ L : (AlgebraicGeometry.Proj (polyGrading k 2)).Modules))
  have hX2 := eulerCharacteristic_congr_hom k _ _ hf ((Scheme.Modules.pullback e0.hom).obj
      ((Scheme.Modules.pullback J.subschemeι).obj
        (M ⊗ L : (AlgebraicGeometry.Proj (polyGrading k 2)).Modules)))
  let eZ : (Scheme.Modules.pullback D.i).obj (twistingSheafModule (polyGrading k 2) t) ≅
      (Scheme.Modules.pullback e0.hom).obj ((Scheme.Modules.pullback J.subschemeι).obj
        (M ⊗ L : (AlgebraicGeometry.Proj (polyGrading k 2)).Modules)) :=
    ((Scheme.Modules.pullbackCongr hφ).symm.app _ ≪≫
      ((Scheme.Modules.pullbackComp e0.hom J.subschemeι).app _).symm ≪≫
      (Scheme.Modules.pullback e0.hom).mapIso ((Scheme.Modules.pullback J.subschemeι).mapIso
          eN.symm))
  have hX3 := eulerCharacteristic_eq_of_iso k D.toSpec eZ
  linarith

end Cartier

section TransportMMP

open Stacks.AlgebraicGeometry.ProjPolyChart Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj

private theorem transport_one (k : Type u) [Field k] {C : Scheme.{u}}
    (i : C ⟶ projectiveSpaceOver 2 (Spec (.of k))) (D : PlaneCurveData k) (ε : C ≅ D.Z)
    (hε' : ε.hom ≫ D.i = i ≫ (Stacks.ProjectiveCohomology.projModelIso k 2).inv) :
    Nonempty ((Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf 2 (Spec (.of k))) ≅
      (Scheme.Modules.pullback ε.hom).obj ((Scheme.Modules.pullback D.i).obj
        (twistingSheafModule (polyGrading k 2) 1))) := by
  have hi : ε.hom ≫ D.i ≫ (Stacks.ProjectiveCohomology.projModelIso k 2).hom = i := by
    rw [← Category.assoc, hε', Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact ⟨(Scheme.Modules.pullbackCongr hi.symm).app _ ≪≫
    ((Scheme.Modules.pullbackComp ε.hom (D.i ≫ (Stacks.ProjectiveCohomology.projModelIso k
        2).hom)).app _).symm ≪≫
    (Scheme.Modules.pullback ε.hom).mapIso
      (((Scheme.Modules.pullbackComp D.i (Stacks.ProjectiveCohomology.projModelIso k 2).hom).app
          _).symm ≪≫
        (Scheme.Modules.pullback D.i).mapIso
          (Stacks.ProjectiveCohomology.pullbackProjModelIsoHomTwistOverIso k 2 1))⟩

private theorem transport_zero (k : Type u) [Field k] {C : Scheme.{u}} (D : PlaneCurveData k)
    (ε : C ≅ D.Z) :
    Nonempty ((SheafOfModules.unit C.ringCatSheaf : C.Modules) ≅
      (Scheme.Modules.pullback ε.hom).obj ((Scheme.Modules.pullback D.i).obj
        (twistingSheafModule (polyGrading k 2) 0))) :=
  ⟨(pullbackObjUnitIsoUnit ε.hom).symm ≪≫ (Scheme.Modules.pullback ε.hom).mapIso
    ((pullbackObjUnitIsoUnit D.i).symm ≪≫ (Scheme.Modules.pullback D.i).mapIso
      (Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit (polyGrading k 2)).symm)⟩

private theorem subschemeHilbertFunction_eq_of_iso (k : Type u) [Field k] {C : Scheme.{u}}
    (i : C ⟶ projectiveSpaceOver 2 (Spec (.of k))) [IsClosedImmersion i]
    (D : PlaneCurveData k) (ε : C ≅ D.Z)
    (hε : ε.hom ≫ D.toSpec = i ≫ projectiveSpaceOver 2 (Spec (.of k)) ↘ Spec (.of k)) (t : ℤ)
    [IsProper D.toSpec] [IsLocallyNoetherian C]
    [((Scheme.Modules.pullback D.i).obj (twistingSheafModule (polyGrading k 2) t)).IsCoherent]
    [((Scheme.Modules.pullback ε.hom).obj ((Scheme.Modules.pullback D.i).obj
        (twistingSheafModule (polyGrading k 2) t))).IsCoherent]
    (e : twistedSheaf (SheafOfModules.unit C.ringCatSheaf)
        (fun _ : Fin 1 => (Scheme.Modules.pullback i).obj
          (projectiveSpaceTwistingSheaf 2 (Spec (.of k)))) (fun _ => t) ≅
      (Scheme.Modules.pullback ε.hom).obj ((Scheme.Modules.pullback D.i).obj
        (twistingSheafModule (polyGrading k 2) t))) :
    subschemeHilbertFunction k (projectiveSpaceOver 2 (Spec (.of k)) ↘ Spec (.of k)) i
      (projectiveSpaceTwistingSheaf 2 (Spec (.of k))) t =
    eulerCharacteristic k D.toSpec ((Scheme.Modules.pullback D.i).obj
      (twistingSheafModule (polyGrading k 2) t)) := by
  unfold subschemeHilbertFunction
  haveI hcc := isCoherent_twistedSheafUnitPullback k
    (projectiveSpaceOver 2 (Spec (.of k)) ↘ Spec (.of k)) i
    (fun _ : Fin 1 => projectiveSpaceTwistingSheaf 2 (Spec (.of k))) (fun _ => t)
  rw [eulerCharacteristic_eq_of_iso k _ e]
  have hpr : IsProper (ε.hom ≫ D.toSpec) := inferInstance
  rw [eulerCharacteristic_congr_hom k _ _ hε.symm]
  exact eulerCharacteristic_pullback_iso k ε D.toSpec _

/-- the twisted sheaf by `0` is the structure sheaf. -/
private noncomputable def twistedSheafIsoUnitZero {X : Scheme.{u}} (N : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N] :
    twistedSheaf (SheafOfModules.unit X.ringCatSheaf) (fun _ : Fin 1 => N) (fun _ => (0 : ℤ)) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  MMP.Mori.Twist.twistedSheafUnitIsoTensorPower (fun _ : Fin 1 => N) N (fun _ => Iso.refl _) (fun
      _ => (0 : ℤ)) ≪≫
    eqToIso (congrArg (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 N)
      (show (∑ _i : Fin 1, (0 : ℤ)) = 0 by simp))

/-- the twisted sheaf by `1` is the sheaf itself. -/
private noncomputable def twistedSheafIsoSelfOne {X : Scheme.{u}} (N : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N] :
    twistedSheaf (SheafOfModules.unit X.ringCatSheaf) (fun _ : Fin 1 => N) (fun _ => (1 : ℤ)) ≅
      N :=
  MMP.Mori.Twist.twistedSheafUnitIsoTensorPower (fun _ : Fin 1 => N) N (fun _ => Iso.refl _) (fun
      _ => (1 : ℤ)) ≪≫
    eqToIso (congrArg (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 N)
      (show (∑ _i : Fin 1, (1 : ℤ)) = 1 by simp)) ≪≫
    Stacks.SheafOfModules.Invertible.tensorPowerOneIso X.presheaf X.ringCatSheaf.2 N

end TransportMMP

open AlgebraicGeometry.ProjectiveSpectrum.Proj Stacks.AlgebraicGeometry.ProjPolyChart in
/-- The Hilbert function of a plane curve at `0` and `1`:
`2 χ(C, 𝒪_C(t)) = (t+1)(t+2) - (t-d+1)(t-d+2)`. -/
private theorem two_mul_subschemeHilbertFunction_planeCurve (k : Type u) [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (i : C ⟶ projectiveSpaceOver 2 (Spec (.of k)))
    [IsClosedImmersion i] [IsIntegral C] (D : PlaneCurveData k)
    (ε : C ≅ D.Z)
    (hε : ε.hom ≫ D.toSpec = i ≫ projectiveSpaceOver 2 (Spec (.of k)) ↘ Spec (.of k))
    (hε' : ε.hom ≫ D.i = i ≫ (Stacks.ProjectiveCohomology.projModelIso k 2).inv)
    (t : ℤ) (ht : t = 0 ∨ t = 1) :
    2 * subschemeHilbertFunction k (projectiveSpaceOver 2 (Spec (.of k)) ↘ Spec (.of k)) i
        (projectiveSpaceTwistingSheaf 2 (Spec (.of k))) t =
      (t + 1) * (t + 2) - (t - D.deg + 1) * (t - D.deg + 2) := by
  have := D.isClosedImmersion
  haveI := isProper_toSpec D
  haveI : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian
    (i ≫ projectiveSpaceOver 2 (Spec (.of k)) ↘ Spec (.of k))
  haveI : IsLocallyNoetherian D.Z := isLocallyNoetherian_of_isClosedImmersion D.i
  haveI hc1 : ((Scheme.Modules.pullback D.i).obj
      (twistingSheafModule (polyGrading k 2) t)).IsCoherent := isCoherent_pullback D.i _
  haveI hc2 : ((Scheme.Modules.pullback ε.hom).obj ((Scheme.Modules.pullback D.i).obj
      (twistingSheafModule (polyGrading k 2) t))).IsCoherent := isCoherent_pullback ε.hom _
  rcases ht with rfl | rfl
  · obtain ⟨a⟩ := transport_zero k D ε
    rw [subschemeHilbertFunction_eq_of_iso k i D ε hε 0 (twistedSheafIsoUnitZero _ ≪≫ a)]
    exact two_mul_chi_pullback_twist k D 0
  · obtain ⟨a⟩ := transport_one k i D ε hε'
    rw [subschemeHilbertFunction_eq_of_iso k i D ε hε 1 (twistedSheafIsoSelfOne _ ≪≫ a)]
    exact two_mul_chi_pullback_twist k D 1

open AlgebraicGeometry.ProjectiveSpectrum.Proj in
/-- The degree of a plane curve in the sense of the Hilbert polynomial is the degree of its
equation. -/
private theorem hilbertDegree_eq_planeCurveData_deg (k : Type u) [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (i : C ⟶ projectiveSpaceOver 2 (Spec (.of k)))
    [IsClosedImmersion i] [IsIntegral C] (hC : topologicalKrullDim C = 1) (D : PlaneCurveData k)
    (ε : C ≅ D.Z)
    (hε : ε.hom ≫ D.toSpec = i ≫ projectiveSpaceOver 2 (Spec (.of k)) ↘ Spec (.of k))
    (hε' : ε.hom ≫ D.i = i ≫ (Stacks.ProjectiveCohomology.projModelIso k 2).inv) :
    hilbertDegree k (projectiveSpaceOver 2 (Spec (.of k)) ↘ Spec (.of k)) i 1 hC
        (projectiveSpaceTwistingSheaf 2 (Spec (.of k))) = D.deg := by
  have h0 := two_mul_subschemeHilbertFunction_planeCurve k i D ε hε hε' 0 (Or.inl rfl)
  have h1 := two_mul_subschemeHilbertFunction_planeCurve k i D ε hε hε' 1 (Or.inr rfl)
  unfold hilbertDegree
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  norm_num
  nlinarith

/-- Plane-curve genus: an integral closed curve of degree `e` in `ℙ²_k` has `2 p_a =
(e-1)(e-2)`. -/
private theorem two_mul_arithmeticGenus_plane_curve
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (i : C ⟶ projectiveSpaceOver 2 (Spec (.of k)))
    [IsClosedImmersion i] [IsIntegral C] (hC : topologicalKrullDim C = 1) :
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
      (i ≫ projectiveSpaceOver 2 (Spec (.of k)) ↘ Spec (.of k))
    2 * arithmeticGenus (i ≫ projectiveSpaceOver 2 (Spec (.of k)) ↘ Spec (.of k)) =
      (hilbertDegree k (projectiveSpaceOver 2 (Spec (.of k)) ↘ Spec (.of k)) i 1 hC
          (projectiveSpaceTwistingSheaf 2 (Spec (.of k))) - 1) *
        (hilbertDegree k (projectiveSpaceOver 2 (Spec (.of k)) ↘ Spec (.of k)) i 1 hC
          (projectiveSpaceTwistingSheaf 2 (Spec (.of k))) - 2) := by
  obtain ⟨D, ε, hε, hε'⟩ := exists_planeCurveData k i hC
  rw [hilbertDegree_eq_planeCurveData_deg k i hC D ε hε hε']
  exact two_mul_arithmeticGenus_eq_planeCurveData k i hC D ε hε

/-- Genus goes down along a proper birational morphism of integral proper curves. -/
private theorem arithmeticGenus_le_of_birational
    (k : Type u) [Field k] [IsAlgClosed k] {C C' : Scheme.{u}} (sC : C ⟶ Spec (.of k))
    (sC' : C' ⟶ Spec (.of k)) (f : C ⟶ C') (hf : f ≫ sC' = sC)
    [IsProper sC] [IsProper sC'] [IsIntegral C] [IsIntegral C']
    (hbir : AlgebraicGeometry.IsBirational f) (hC : topologicalKrullDim C ≤ 1)
    (hC' : topologicalKrullDim C' ≤ 1) :
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k sC
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k sC'
    arithmeticGenus sC ≤ arithmeticGenus sC' := by
  subst hf
  have hpf : IsProper f := IsProper.of_comp f sC'
  have hgen := AlgebraicGeometry.genus_le_of_isProper_of_isBirational k sC' f hbir hC'
  have h1 := (arithmeticGenus_eq_finrank_cohomologyOverField_one (f ≫ sC') hC).2.1
  have h2 := (arithmeticGenus_eq_finrank_cohomologyOverField_one sC' hC').2.1
  rw [h1, h2]
  have e1 := (AlgebraicGeometry.structureSheafCohomologyIsoCohomologyOverField k (f ≫ sC')
    1).toLinearEquiv.finrank_eq
  have e2 := (AlgebraicGeometry.structureSheafCohomologyIsoCohomologyOverField k sC'
    1).toLinearEquiv.finrank_eq
  rw [AlgebraicGeometry.genus_eq_finrank_structureSheafCohomology, e1] at hgen
  rw [AlgebraicGeometry.genus_eq_finrank_structureSheafCohomology, e2] at hgen
  exact_mod_cast hgen

/-! ### Field-theoretic input and degrees -/

section FieldLemma

open IntermediateField

private theorem exists_notMem_of_ne_top {k E : Type*} [Field k] [Infinite k] [AddCommGroup E]
    [Module k E] (s : Finset (Submodule k E)) (hs : ∀ w ∈ s, w ≠ ⊤) :
    ∃ c : E, ∀ w ∈ s, c ∉ w := by
  have h := Subspace.biUnion_ne_univ_of_top_notMem (k := k) (E := E) (s := s)
    (fun h => hs _ h rfl)
  by_contra hcon
  push Not at hcon
  apply h
  ext c
  simp only [Set.mem_iUnion, SetLike.mem_coe, Set.mem_univ, iff_true]
  obtain ⟨w, hw, hc⟩ := hcon c
  exact ⟨w, hw, hc⟩

/-- The `k`-linear combination map. -/
private def combo {k K ι : Type*} [Field k] [Field K] [Algebra k K] [Fintype ι] (a : ι → K) :
    (ι → k) →ₗ[k] K :=
  Fintype.linearCombination k a

private theorem combo_apply {k K ι : Type*} [Field k] [Field K] [Algebra k K] [Fintype ι]
    (a : ι → K) (c : ι → k) : combo a c = ∑ j, c j • a j := by
  simp [combo, Fintype.linearCombination_apply]

private theorem combo_single {k K ι : Type*} [Field k] [Field K] [Algebra k K] [Fintype ι]
    [DecidableEq ι] (a : ι → K) (j : ι) : combo a (Pi.single j (1 : k)) = a j := by
  simp [combo_apply, Pi.single_apply]

private theorem mem_range_of_isAlgebraic {k K : Type*} [Field k] [IsAlgClosed k] [Field K]
    [Algebra k K] {y : K} (hy : IsAlgebraic k y) : y ∈ Set.range (algebraMap k K) := by
  have hint : IsIntegral k y := hy.isIntegral
  haveI : FiniteDimensional k k⟮y⟯ := IntermediateField.adjoin.finiteDimensional hint
  have hb : k⟮y⟯ = ⊥ := IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic _
  have : y ∈ (⊥ : IntermediateField k K) := by
    rw [← hb]; exact IntermediateField.mem_adjoin_simple_self k y
  exact IntermediateField.mem_bot.mp this

/-- If `K` has transcendence degree one and is generated by `a`, not every `k`-linear
combination of `a` is a constant. -/
private theorem comap_combo_range_ne_top {k K ι : Type*} [Field k] [Field K] [Algebra k K]
    [Fintype ι] (a : ι → K) (hgen : IntermediateField.adjoin k (Set.range a) = ⊤)
    (htr : Algebra.trdeg k K = 1) : (Algebra.linearMap k K).range.comap (combo a) ≠ ⊤ := by
  classical
  intro h
  have hmem : ∀ j, a j ∈ Set.range (algebraMap k K) := by
    intro j
    have : (Pi.single j (1 : k) : ι → k) ∈
        (Algebra.linearMap k K).range.comap (combo a) := by rw [h]; trivial
    have h2 : combo a (Pi.single j (1 : k)) ∈ (Algebra.linearMap k K).range := this
    rwa [combo_single] at h2
  have hbot : IntermediateField.adjoin k (Set.range a) = ⊥ := by
    rw [eq_bot_iff, IntermediateField.adjoin_le_iff]
    rintro _ ⟨j, rfl⟩
    exact IntermediateField.mem_bot.mpr (hmem j)
  rw [hgen] at hbot
  have : Algebra.IsAlgebraic k K := by
    constructor
    intro x
    have hx : x ∈ (⊥ : IntermediateField k K) := by rw [← hbot]; trivial
    obtain ⟨r, rfl⟩ := IntermediateField.mem_bot.mp hx
    exact isAlgebraic_algebraMap r
  rw [← trdeg_eq_zero_iff] at this
  exact zero_ne_one (this ▸ htr)

/-- A field of transcendence degree one is algebraic over the subfield generated by any
transcendental element. -/
private theorem isAlgebraic_adjoin_simple_of_trdeg_eq_one {k K : Type*} [Field k] [Field K]
    [Algebra k K] (htr : Algebra.trdeg k K = 1) {y : K} (hy : Transcendental k y) :
    Algebra.IsAlgebraic k⟮y⟯ K := by
  have hFtr : Algebra.Transcendental k k⟮y⟯ := by
    refine ⟨⟨y, IntermediateField.mem_adjoin_simple_self k y⟩, ?_⟩
    exact (transcendental_algebraMap_iff (R := k) (A := K) (S := k⟮y⟯)
      (a := ⟨y, IntermediateField.mem_adjoin_simple_self k y⟩)
      (algebraMap k⟮y⟯ K).injective).mp hy
  have hpos : 0 < Algebra.trdeg k k⟮y⟯ := trdeg_pos k k⟮y⟯
  by_contra hnot
  have hT : Algebra.Transcendental k⟮y⟯ K := by
    rwa [Algebra.transcendental_iff_not_isAlgebraic]
  have h2 : 0 < Algebra.trdeg k⟮y⟯ K := trdeg_pos k⟮y⟯ K
  have h3 : (1 : Cardinal) + 1 ≤ Algebra.trdeg k k⟮y⟯ + Algebra.trdeg k⟮y⟯ K :=
    add_le_add (Cardinal.one_le_iff_pos.mpr hpos) (Cardinal.one_le_iff_pos.mpr h2)
  rw [trdeg_add_eq k k⟮y⟯ (A := K), htr] at h3
  norm_num at h3

/-- If `a` generates `K` over `F` and `K/F` has finitely many intermediate fields, some
`k`-linear combination of `a` is a primitive element of `K/F`. -/
private theorem exists_combo_adjoin_eq_top {k K ι : Type*} [Field k] [Infinite k] [Field K]
    [Algebra k K] [Fintype ι] (a : ι → K) {F : IntermediateField k K}
    [Finite (IntermediateField F K)]
    (hadj : IntermediateField.adjoin F (Set.range a) = ⊤) :
    ∃ d : ι → k, IntermediateField.adjoin F {combo a d} = ⊤ := by
  classical
  let Wk : IntermediateField F K → Submodule k (ι → k) := fun M =>
    ((M.toSubalgebra.toSubmodule).restrictScalars k).comap (combo a)
  have hWk : ∀ M : IntermediateField F K, M ≠ ⊤ → Wk M ≠ ⊤ := by
    intro M hM htop
    apply hM
    rw [eq_top_iff, ← hadj, IntermediateField.adjoin_le_iff]
    rintro _ ⟨j, rfl⟩
    have : (Pi.single j (1 : k) : ι → k) ∈ Wk M := by rw [htop]; trivial
    have h4 : combo a (Pi.single j (1 : k)) ∈ M := this
    rwa [combo_single] at h4
  obtain ⟨d, hd⟩ := exists_notMem_of_ne_top (k := k)
    ((Set.toFinite {M : IntermediateField F K | M ≠ ⊤}).toFinset.image Wk) (by
      intro w hw
      obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp hw
      exact hWk M (by simpa using hM))
  refine ⟨d, ?_⟩
  by_contra hne
  exact hd _ (Finset.mem_image.mpr ⟨_, by simpa using hne, rfl⟩)
    (IntermediateField.mem_adjoin_simple_self F _)

/-- A finite family generating `K` as a field, with `K` of transcendence degree one, has a
non-constant `k`-linear combination avoiding finitely many proper subspaces, and a second
combination which together with the first generates `K`. -/
private theorem exists_two_generators {k K ι : Type*} [Field k] [IsAlgClosed k] [CharZero k]
    [Field K] [Algebra k K] [Fintype ι] (a : ι → K)
    (hgen : IntermediateField.adjoin k (Set.range a) = ⊤) (htr : Algebra.trdeg k K = 1)
    (W : Finset (Submodule k (ι → k))) (hW : ∀ w ∈ W, w ≠ ⊤) :
    ∃ c d : ι → k, (∀ w ∈ W, c ∉ w) ∧ combo a c ∉ Set.range (algebraMap k K) ∧
      IntermediateField.adjoin k {combo a c, combo a d} = ⊤ := by
  classical
  let V0 : Submodule k (ι → k) := (Algebra.linearMap k K).range.comap (combo a)
  have hV0 : V0 ≠ ⊤ := comap_combo_range_ne_top a hgen htr
  obtain ⟨c, hc⟩ := exists_notMem_of_ne_top (k := k) (insert V0 W) (by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hV0
    · exact hW w hw)
  have hcV0 : c ∉ V0 := hc V0 (Finset.mem_insert_self _ _)
  have hcW : ∀ w ∈ W, c ∉ w := fun w hw => hc w (Finset.mem_insert_of_mem hw)
  have hy1 : combo a c ∉ Set.range (algebraMap k K) := hcV0
  have htrans : Transcendental k (combo a c) := fun h => hy1 (mem_range_of_isAlgebraic h)
  set y1 := combo a c
  let F : IntermediateField k K := k⟮y1⟯
  have hFK : Algebra.IsAlgebraic F K := isAlgebraic_adjoin_simple_of_trdeg_eq_one htr htrans
  have hadj : IntermediateField.adjoin F (Set.range a) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ IntermediateField.adjoin k (Set.range a) := by rw [hgen]; trivial
    have hle : IntermediateField.adjoin k (Set.range a) ≤
        (IntermediateField.adjoin F (Set.range a)).restrictScalars k := by
      rw [IntermediateField.adjoin_le_iff]
      exact IntermediateField.subset_adjoin F _
    exact hle hx
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  haveI : FiniteDimensional F K := by
    have h1 : FiniteDimensional F (IntermediateField.adjoin F (Set.range a)) :=
      IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
    rw [hadj] at h1
    exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional
  haveI : Algebra.IsSeparable F K := inferInstance
  haveI : Finite (IntermediateField F K) :=
    Field.finite_intermediateField_of_exists_primitive_element F K
      (Field.exists_primitive_element F K)
  obtain ⟨d, hFγ⟩ := exists_combo_adjoin_eq_top a hadj
  refine ⟨c, d, hcW, hy1, ?_⟩
  have h := IntermediateField.adjoin_adjoin_left k {y1} {combo a d}
  have h' : IntermediateField.adjoin k ({y1} ∪ {combo a d}) = ⊤ := by
    rw [← h]
    change (IntermediateField.adjoin (IntermediateField.adjoin k {y1}) {(combo a
        d)}).restrictScalars k = ⊤
    rw [show (IntermediateField.adjoin (IntermediateField.adjoin k {y1}) {combo a d}) = ⊤ from hFγ]
    rfl
  rwa [Set.singleton_union] at h'

end FieldLemma

/-- The Hilbert function of a closed subscheme at `0` is the Euler characteristic of its
structure sheaf. -/
private theorem subschemeHilbertFunction_zero (k : Type u) [Field k] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i] (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    haveI : IsProper (i ≫ f) := inferInstance
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k (i ≫ f)
    subschemeHilbertFunction k f i L 0 =
      eulerCharacteristic k (i ≫ f) (SheafOfModules.unit Z.ringCatSheaf) := by
  haveI hcU := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k (i ≫ f)
  haveI := isCoherent_twistedSheafUnitPullback k f i (fun _ : Fin 1 => L) (fun _ => (0 : ℤ))
  exact eulerCharacteristic_eq_of_iso (k := k) (f := i ≫ f) (twistedSheafIsoUnitZero _)

/-- For a closed subscheme `i : Z ⟶ X` of dimension one of a proper `k`-scheme, the Hilbert
degree is the degree along the curve. -/
private theorem hilbertDegree_one_eq_degreeOn (k : Type u) [Field k] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (hd : topologicalKrullDim Z = 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    haveI : IsProper (i ≫ f) := inferInstance
    hilbertDegree k f i 1 hd L = degreeOn k f i hd.le L := by
  haveI hP : IsProper (i ≫ f) := inferInstance
  haveI hcU := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k (i ≫ f)
  haveI hcP : ((Scheme.Modules.pullback i).obj L).IsCoherent :=
    SheafOfModules.isCoherent_of_isInvertible k (i ≫ f) _
  have h0 := subschemeHilbertFunction_zero k f i L
  have h1 : subschemeHilbertFunction k f i L 1 =
      eulerCharacteristic k (i ≫ f) ((Scheme.Modules.pullback i).obj L) := by
    haveI hF1 := isCoherent_twistedSheafUnitPullback k f i (fun _ : Fin 1 => L) (fun _ => (1 : ℤ))
    unfold subschemeHilbertFunction
    exact eulerCharacteristic_eq_of_iso (k := k) (f := i ≫ f) (twistedSheafIsoSelfOne _)
  unfold hilbertDegree
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  rw [degreeOn_eq_eulerCharacteristic_sub]
  simp only [Nat.cast_zero, Nat.cast_one, Nat.choose_zero_right, Nat.choose_self, Nat.sub_zero,
    Nat.sub_self]
  rw [h0, h1]
  ring

section Projection

open Stacks.ProjectiveFromSections Stacks.TwistPullbackPinned

/-- The composite of a morphism to `ℙᴺ_k` with the projection to the integral model. -/
private noncomputable abbrev toModel (k : Type u) [Field k] {C : Scheme.{u}} {N : ℕ}
    (i : C ⟶ projectiveSpaceOver N (Spec (.of k))) : C ⟶ projectiveSpaceAtUniverse.{u} N :=
  i ≫ projectiveSpaceOver.toIntegralAtUniverse N (Spec (.of k))

section ChartGeneration

attribute [local implicit_reducible] AlgebraicGeometry.projectiveSpaceAtUniverse

private theorem toProjectiveSpaceAtUniverse_taut (k : Type u) [Field k] {C : Scheme.{u}} {N : ℕ}
    (i : C ⟶ projectiveSpaceOver N (Spec (.of k))) :
    toProjectiveSpaceAtUniverse (pullbackCoordSection (toModel k i))
      (Stacks.ProjectiveSpaceModuli.taut_generates (toModel k i)) = toModel k i :=
  Stacks.ProjectiveSpaceModuli.eq_of_pin _ (Stacks.ProjectiveSpaceModuli.taut_generates _) _ _
    (ι_toProjectiveSpaceAtUniverse _ _) (Stacks.ProjectiveSpaceModuli.taut_pin _)

private theorem toProjectiveSpaceOver_taut (k : Type u) [Field k] {C : Scheme.{u}} {N : ℕ}
    (i : C ⟶ projectiveSpaceOver N (Spec (.of k))) :
    toProjectiveSpaceOver (pullbackCoordSection (toModel k i))
      (Stacks.ProjectiveSpaceModuli.taut_generates (toModel k i))
      (i ≫ projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of k)) = i := by
  unfold toProjectiveSpaceOver
  rw [toProjectiveSpaceAtUniverse_taut]
  exact Stacks.AmpleProjectiveImmersion.liftOver_eq _ i rfl

private theorem surjective_appLE_of_isClosedImmersion {X Y : Scheme.{u}} (φ : X ⟶ Y)
    [IsClosedImmersion φ] {V : Y.Opens} (hV : IsAffineOpen V) (W : X.Opens) (hW : W = φ ⁻¹ᵁ V)
    (e : W ≤ φ ⁻¹ᵁ V) : Function.Surjective (φ.appLE V W e).hom := by
  subst hW
  have h := Scheme.Hom.app_surjective φ V hV
  simpa [Scheme.Hom.appLE] using h

open Stacks.ProjectiveSpaceChartRatio Stacks.AlgebraicGeometry.ProjBaseChange
  Stacks.AlgebraicGeometry.ProjPolyChart

private theorem isClosedImmersion_toPolynomialModel (k : Type u) [Field k] {C : Scheme.{u}}
    {N : ℕ} (i : C ⟶ projectiveSpaceOver N (Spec (.of k))) [IsClosedImmersion i] :
    IsClosedImmersion (toPolynomialModel (pullbackCoordSection (toModel k i))
      (Stacks.ProjectiveSpaceModuli.taut_generates (toModel k i))
      (i ≫ projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of k))) := by
  unfold toPolynomialModel
  rw [toProjectiveSpaceOver_taut]
  infer_instance

private theorem preimage_basicOpen_toPolynomialModel (k : Type u) [Field k] {C : Scheme.{u}}
    {N : ℕ} (i : C ⟶ projectiveSpaceOver N (Spec (.of k))) (i₀ : Fin (N + 1)) :
    toPolynomialModel (pullbackCoordSection (toModel k i))
      (Stacks.ProjectiveSpaceModuli.taut_generates (toModel k i))
      (i ≫ projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of k)) ⁻¹ᵁ
      AlgebraicGeometry.Proj.basicOpen (polyGrading k N) (MvPolynomial.X i₀) =
      nvCover (pullbackCoordSection (toModel k i)) i₀ := by
  set s := pullbackCoordSection (toModel k i)
  set hs := Stacks.ProjectiveSpaceModuli.taut_generates (toModel k i)
  set f := i ≫ projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of k)
  refine le_antisymm ?_ (nvCover_le_preimage_basicOpen_toPolynomialModel s hs f i₀)
  have h1 := preimage_basicOpen_le_nvCover_canonical s hs i₀
  rw [← toPolynomialModel_comp_coordinateProjMap s hs f, Scheme.Hom.comp_preimage,
    coordinateProjMap_preimage_basicOpen k N i₀] at h1
  exact h1

private theorem surjective_chartPullback (k : Type u) [Field k] {C : Scheme.{u}} {N : ℕ}
    (i : C ⟶ projectiveSpaceOver N (Spec (.of k))) [IsClosedImmersion i] (i₀ : Fin (N + 1)) :
    Function.Surjective (chartPullback (pullbackCoordSection (toModel k i))
      (Stacks.ProjectiveSpaceModuli.taut_generates (toModel k i))
      (i ≫ projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of k)) i₀) := by
  set s := pullbackCoordSection (toModel k i)
  set hs := Stacks.ProjectiveSpaceModuli.taut_generates (toModel k i)
  set f := i ≫ projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of k)
  haveI := isClosedImmersion_toPolynomialModel k i
  have hpre := preimage_basicOpen_toPolynomialModel k i i₀
  have hAff : IsAffineOpen
      (AlgebraicGeometry.Proj.basicOpen (polyGrading k N) (MvPolynomial.X i₀)) :=
    AlgebraicGeometry.Proj.isAffineOpen_basicOpen _ _ (X_mem_one k N i₀) Nat.one_pos
  have hApp : Function.Surjective ((toPolynomialModel s hs f).appLE
      (AlgebraicGeometry.Proj.basicOpen (polyGrading k N) (MvPolynomial.X i₀)) (nvCover s i₀)
      (nvCover_le_preimage_basicOpen_toPolynomialModel s hs f i₀)).hom :=
    surjective_appLE_of_isClosedImmersion _ hAff _ hpre.symm _
  have hA : Function.Surjective (AlgebraicGeometry.Proj.awayToSection (polyGrading k N)
      (MvPolynomial.X i₀)).hom := by
    have : IsIso (AlgebraicGeometry.Proj.awayToSection (polyGrading k N) (MvPolynomial.X i₀)) := by
      rw [← AlgebraicGeometry.Proj.basicOpenIsoAway_hom (polyGrading k N) (MvPolynomial.X i₀)
        (X_mem_one k N i₀) Nat.one_pos]
      infer_instance
    exact (ConcreteCategory.bijective_of_isIso _).2
  have hE : Function.Surjective (chartEquiv k N i₀) := (chartEquiv k N i₀).surjective
  intro y
  obtain ⟨a, ha⟩ := hApp y
  obtain ⟨b, hb⟩ := hA a
  obtain ⟨c, hc⟩ := hE b
  exact ⟨c, by rw [chartPullback_apply, hc, hb, ha]⟩

private theorem isAffineOpen_nvCover_taut (k : Type u) [Field k] {C : Scheme.{u}} {N : ℕ}
    (i : C ⟶ projectiveSpaceOver N (Spec (.of k))) [IsClosedImmersion i] (i₀ : Fin (N + 1)) :
    IsAffineOpen (nvCover (pullbackCoordSection (toModel k i)) i₀) := by
  haveI := isClosedImmersion_toPolynomialModel k i
  rw [← preimage_basicOpen_toPolynomialModel k i i₀]
  exact IsAffineHom.isAffine_preimage _
    (AlgebraicGeometry.Proj.isAffineOpen_basicOpen _ _ (X_mem_one k N i₀) Nat.one_pos)

/-- The function field of a closed integral subscheme of `ℙᴺ_k` is generated over `k` by the
coordinate ratios `x_j / x_{i₀}` at a coordinate `x_{i₀}` not vanishing at the generic point. -/
private theorem exists_coordinate_ratios_generate (k : Type u) [Field k] {C : Scheme.{u}}
    [IsIntegral C] {N : ℕ} (i : C ⟶ projectiveSpaceOver N (Spec (.of k))) [IsClosedImmersion i] :
    ∃ (i₀ : Fin (N + 1)) (h : genericPoint C ∈ nvCover (pullbackCoordSection (toModel k i)) i₀),
      letI := functionFieldAlgebra (i ≫ projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of k))
      IntermediateField.adjoin k (Set.range fun j =>
        C.presheaf.germ (nvCover (pullbackCoordSection (toModel k i)) i₀) (genericPoint C) h
          (ratio (pullbackCoordSection (toModel k i)) i₀ j)) = ⊤ := by
  classical
  set s := pullbackCoordSection (toModel k i)
  set hs := Stacks.ProjectiveSpaceModuli.taut_generates (toModel k i)
  set f := i ≫ projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of k)
  obtain ⟨i₀, hi₀⟩ := exists_mem_nvCover_of_generatesStalks s hs (genericPoint C)
  refine ⟨i₀, hi₀, ?_⟩
  letI := functionFieldAlgebra f
  set F := IntermediateField.adjoin k (Set.range fun j =>
    C.presheaf.germ (nvCover s i₀) (genericPoint C) hi₀ (ratio s i₀ j)) with hF
  haveI : Nonempty (nvCover s i₀) := ⟨⟨genericPoint C, hi₀⟩⟩
  have hfrac := functionField_isFractionRing_of_isAffineOpen C _ (isAffineOpen_nvCover_taut k i i₀)
  have hbase : ∀ r : k, C.presheaf.germ (nvCover s i₀) (genericPoint C) hi₀
      (chartBaseHom s f i₀ r) = algebraMap k C.functionField r := by
    intro r
    show _ = ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
      C.presheaf.germ ⊤ (genericPoint C) (TopologicalSpace.Opens.mem_top _)).hom r
    simp only [chartBaseHom, Scheme.Hom.appLE, Scheme.Hom.appTop, RingHom.comp_apply,
      CommRingCat.hom_comp, ConcreteCategory.comp_apply, TopCat.Presheaf.germ_res_apply]
    rfl
  have hmem : ∀ P, C.presheaf.germ (nvCover s i₀) (genericPoint C) hi₀
      (chartPullback s hs f i₀ P) ∈ F := by
    intro P
    rw [chartPullback_eq]
    induction P using MvPolynomial.induction_on with
    | C a =>
      rw [MvPolynomial.eval₂Hom_C, hbase]
      exact F.algebraMap_mem a
    | add p q hp hq => rw [map_add, map_add]; exact F.add_mem hp hq
    | mul_X p j hp =>
      rw [map_mul, map_mul, MvPolynomial.eval₂Hom_X']
      exact F.mul_mem hp (IntermediateField.subset_adjoin k _ ⟨j.1, rfl⟩)
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := Γ(C, nvCover s i₀)) x
  have hg : ∀ a : Γ(C, nvCover s i₀), algebraMap Γ(C, nvCover s i₀) C.functionField a =
      C.presheaf.germ (nvCover s i₀) (genericPoint C) hi₀ a := fun a => rfl
  have hin : ∀ a : Γ(C, nvCover s i₀), algebraMap Γ(C, nvCover s i₀) C.functionField a ∈ F := by
    intro a
    obtain ⟨P, rfl⟩ := surjective_chartPullback k i i₀ a
    rw [hg]
    exact hmem P
  exact F.div_mem (hin a) (hin b)

end ChartGeneration

/-- The morphism attached to three generating sections of `i^*𝒪(1)` has the pullback of
`𝒪(1)` isomorphic to `i^*𝒪(1)`, and lies over `Spec k`. -/
private theorem exists_projection_morphism_of_sections (k : Type u) [Field k] {C : Scheme.{u}}
    [IsIntegral C] {N : ℕ} (i : C ⟶ projectiveSpaceOver N (Spec (.of k))) [IsClosedImmersion i]
    (s : Fin 3 → Γ((Scheme.Modules.pullback (toModel k i)).obj
      (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} N), ⊤))
    (hs : GeneratesStalks s)
    (hR : ∀ y : C.presheaf.stalk (genericPoint C), y ∈
      ((toProjectiveSpaceOver s hs (i ≫ projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of
          k))).stalkMap
        (genericPoint C)).hom.range)
    (hnc : ¬ ∃ x, Set.range (toProjectiveSpaceOver s hs
      (i ≫ projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of k))) = {x}) :
    ∃ g : C ⟶ projectiveSpaceOver 2 (Spec (.of k)),
      g ≫ projectiveSpaceOver 2 (Spec (.of k)) ↘ Spec (.of k) =
        i ≫ projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of k) ∧
      Nonempty ((Scheme.Modules.pullback g).obj (projectiveSpaceTwistingSheaf 2 (Spec (.of k))) ≅
        (Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf N (Spec (.of k)))) ∧
      (¬ ∃ x, Set.range g = {x}) ∧
      ∀ y : C.presheaf.stalk (genericPoint C), y ∈ (g.stalkMap (genericPoint C)).hom.range := by
  haveI : Stacks.Ample.IsInvertibleModule C ((Scheme.Modules.pullback (toModel k i)).obj
      (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} N)) := inferInstance
  refine ⟨toProjectiveSpaceOver s hs (i ≫ projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of k)),
    ?_, ?_, hnc, hR⟩
  · exact toProjectiveSpaceOver_fst s hs _
  · obtain ⟨α, hαiso, -⟩ :=
      AlgebraicGeometry.exists_iso_twistingSheafAtUniverse_toProjectiveSpaceAtUniverse s hs
    haveI := hαiso
    have hi : Stacks.AmpleProjectiveImmersion.liftOver
        (i ≫ projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of k)) (toModel k i) = i :=
      Stacks.AmpleProjectiveImmersion.liftOver_eq _ i rfl
    exact ⟨(Stacks.AmpleProjectiveImmersion.liftOverTwistIso _ (toProjectiveSpaceAtUniverse s hs))
        ≪≫
      asIso α ≪≫ ((Scheme.Modules.pullbackCongr hi.symm).app _ ≪≫
        Stacks.AmpleProjectiveImmersion.liftOverTwistIso _ (toModel k i)).symm⟩

end Projection

section Selection

open Stacks.ProjectiveFromSections Stacks.TwistPullbackPinned

section Combination

variable {C : Scheme.{u}} {L : C.Modules} [Stacks.Ample.IsInvertibleModule C L]
  {k : Type*} [Field k] {ι : Type*} [Fintype ι]

/-- The `k`-linear combination of global sections, `k` acting through `β`. -/
private noncomputable def sectionCombo (β : k →+* Γ(C, ⊤)) (x : ι → Γ(L, ⊤)) (c : ι → k) :
    Γ(L, ⊤) := ∑ m, β (c m) • x m

private theorem exists_subspace_notMem_nvOpen (β : k →+* Γ(C, ⊤)) (x : ι → Γ(L, ⊤))
    (hx : GeneratesStalks x) (p : C) :
    ∃ W : Submodule k (ι → k), W ≠ ⊤ ∧ ∀ c, c ∉ W → p ∈ nvOpen L (sectionCombo β x c) := by
  classical
  obtain ⟨j, hj⟩ := exists_mem_nvCover_of_generatesStalks x hx p
  have hj' : p ∈ Stacks.Ample.nonvanishingLocus L (x j) := hj
  have hr : ∀ m, ∃ r : C.presheaf.stalk p,
      (L.presheaf.Γgerm p).hom (x m) = r • (L.presheaf.Γgerm p).hom (x j) := fun m =>
    Stacks.SectionProduct.exists_smul_Γgerm L (x j) hj' _
  choose r hr using hr
  let r' : ι → C.presheaf.stalk p := fun m => if m = j then 1 else r m
  have hr' : ∀ m, (L.presheaf.Γgerm p).hom (x m) = r' m • (L.presheaf.Γgerm p).hom (x j) := by
    intro m
    by_cases h : m = j
    · subst h; simp [r']
    · simp [r', h, hr m]
  let ρ : k →+* IsLocalRing.ResidueField (C.presheaf.stalk p) :=
    (IsLocalRing.residue _).comp ((C.presheaf.germ ⊤ p trivial).hom.comp β)
  let e := (L.presheaf.Γgerm p).hom (x j)
  let ev : (ι → k) → IsLocalRing.ResidueField (C.presheaf.stalk p) := fun c =>
    ∑ m, ρ (c m) * IsLocalRing.residue _ (r' m)
  let W : Submodule k (ι → k) :=
    { carrier := {c | ev c = 0}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, ev, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
            at *
        rw [ha, hb, add_zero]
      zero_mem' := by simp [ev]
      smul_mem' := by
        intro a c hc
        simp only [Set.mem_setOf_eq, ev, Pi.smul_apply, smul_eq_mul, map_mul] at *
        simp_rw [mul_assoc]
        rw [← Finset.mul_sum, hc, mul_zero] }
  refine ⟨W, ?_, ?_⟩
  · intro htop
    have h1 : (Pi.single j (1 : k) : ι → k) ∈ W := by rw [htop]; trivial
    have h2 : ev (Pi.single j (1 : k)) = 0 := h1
    have h3 : ev (Pi.single j (1 : k)) = 1 := by
      simp only [ev]
      rw [Finset.sum_eq_single j]
      · simp [r']
      · intro b _ hb; simp [hb]
      · simp
    rw [h3] at h2
    exact one_ne_zero h2
  · intro c hc
    have hg : (L.presheaf.Γgerm p).hom (sectionCombo β x c) =
        (∑ m, (C.presheaf.germ ⊤ p trivial).hom (β (c m)) * r' m) • e := by
      unfold sectionCombo
      rw [map_sum, Finset.sum_smul]
      refine Finset.sum_congr rfl fun m _ => ?_
      have := Stacks.ModuleStalk.germ_smul L p ⊤ trivial (β (c m)) (x m)
      change (L.presheaf.germ ⊤ p trivial).hom (β (c m) • x m) = _ at this
      rw [mul_smul]
      change (L.presheaf.germ ⊤ p trivial).hom (β (c m) • x m) = _
      rw [this]
      congr 1
      exact hr' m
    set a := ∑ m, (C.presheaf.germ ⊤ p trivial).hom (β (c m)) * r' m with ha
    have hres : IsLocalRing.residue _ a = ev c := by
      simp only [ha, ev, map_sum, map_mul]
      rfl
    have hunit : IsUnit a := by
      by_contra hn
      apply hc
      show ev c = 0
      rw [← hres, IsLocalRing.residue_eq_zero_iff]
      exact (IsLocalRing.mem_maximalIdeal a).mpr hn
    rw [Stacks.NonvanishingOpen.mem_nonvanishingOpen, Stacks.Ample.mem_nonvanishingLocus_iff, hg,
      Stacks.ModuleStalk.smul_mem_maximalSmul_iff, not_or]
    exact ⟨not_not.mpr hunit, (Stacks.Ample.mem_nonvanishingLocus_iff _ _ _).mp hj'⟩

/-- The ratio of a combination of sections by the first one is the same combination of the ratios
(over any open in both nonvanishing opens). -/
private theorem resO_ratio_sectionCombo (β : k →+* Γ(C, ⊤)) (x : ι → Γ(L, ⊤)) (i₀ : ι)
    (c : ι → k) {κ : Type*} (t : κ → Γ(L, ⊤)) (a b : κ) (ht0 : t a = x i₀)
    (ht1 : t b = sectionCombo β x c)
    (W : C.Opens) (hW : W ≤ nvCover t a) (hWx : W ≤ nvCover x i₀) :
    resO hW (ratio t a b) =
      ∑ m, resO (le_top : W ≤ ⊤) (β (c m)) * resO hWx (ratio x i₀ m) := by
  have hW' : W ≤ nvOpen L (x i₀) := hWx
  refine eq_of_smul_eq_smul (x i₀) hW' ?_
  have h1 := resO_ratio_smul t hW b
  rw [ht0, ht1] at h1
  rw [h1, Finset.sum_smul]
  unfold sectionCombo
  simp only [resT, resM, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mul_smul]
  have h2 := resO_ratio_smul x hWx m
  rw [h2]
  exact resM_smul (le_top : W ≤ ⊤) (β (c m)) (x m)

end Combination

section StalkRange

variable {C : Scheme.{u}} {L : C.Modules} [Stacks.Ample.IsInvertibleModule C L]
  {k : Type u} [Field k] [IsIntegral C]

/-- The stalk map of a morphism at a point factors the stalk map of its composite with a
morphism equal to it. -/
private theorem mem_range_stalkMap_of_comp_eq {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    (g' : X ⟶ Z) (hg : g ≫ h = g') (x : X)
    {z : X.presheaf.stalk x} (hz : z ∈ (g'.stalkMap x).hom.range) : z ∈ (g.stalkMap x).hom.range
        := by
  subst hg
  obtain ⟨w, rfl⟩ := hz
  rw [Scheme.Hom.stalkMap_comp]
  exact ⟨(h.stalkMap (g x)).hom w, rfl⟩

/-- The range of the stalk map at the generic point of an integral scheme is a subfield. -/
private theorem range_stalkMap_genericPoint (sC : C ⟶ Spec (.of k)) {Y : Scheme.{u}} (g : C ⟶ Y)
    (π : Y ⟶ Spec (.of k)) (hg : g ≫ π = sC) :
    letI := functionFieldAlgebra sC
    ∃ F : IntermediateField k C.functionField,
      (F : Set C.functionField) = (g.stalkMap (genericPoint C)).hom.range := by
  letI := functionFieldAlgebra sC
  let φ := (g.stalkMap (genericPoint C)).hom
  have hloc : IsLocalHom φ := inferInstance
  have hbase : ∀ r : k, algebraMap k C.functionField r ∈ φ.range := by
    intro r
    have key : ∀ f : C ⟶ Spec (.of k), g ≫ π = f →
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
          C.presheaf.germ ⊤ (genericPoint C) trivial).hom r ∈ φ.range := by
      intro f hf
      subst hf
      refine ⟨Y.presheaf.germ ⊤ (g (genericPoint C)) trivial
        (π.appTop ((Scheme.ΓSpecIso (.of k)).inv.hom r)), ?_⟩
      have := Scheme.Hom.germ_stalkMap_apply g ⊤ (genericPoint C) trivial
        (π.appTop ((Scheme.ΓSpecIso (.of k)).inv.hom r))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.comp_appTop,
        ConcreteCategory.comp_apply]
      rw [this]
      rfl
    exact key sC hg
  refine ⟨
    { carrier := φ.range
      mul_mem' := fun {a b} ha hb => φ.range.mul_mem ha hb
      one_mem' := φ.range.one_mem
      add_mem' := fun {a b} ha hb => φ.range.add_mem ha hb
      zero_mem' := φ.range.zero_mem
      algebraMap_mem' := hbase
      inv_mem' := ?_ }, rfl⟩
  rintro a ⟨z, rfl⟩
  by_cases h0 : φ z = 0
  · rw [h0, inv_zero]; exact φ.range.zero_mem
  · have hu : IsUnit (φ z) := (isUnit_iff_ne_zero).mpr h0
    have hzu : IsUnit z := hloc.map_nonunit z hu
    obtain ⟨u, rfl⟩ := hzu
    refine ⟨↑u⁻¹, ?_⟩
    have hmul : φ ↑u * φ ↑u⁻¹ = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    exact (inv_eq_of_mul_eq_one_right hmul).symm

/-- If the ratios of three generating sections generate the function field, the stalk map of the
attached morphism at the generic point is onto. -/
private theorem stalkMap_range_eq_top (sC : C ⟶ Spec (.of k)) (s : Fin 3 → Γ(L, ⊤))
    (hs : GeneratesStalks s) (h0 : genericPoint C ∈ nvCover s 0)
    (hgen : letI := functionFieldAlgebra sC
      IntermediateField.adjoin k {C.presheaf.germ (nvCover s 0) (genericPoint C) h0 (ratio s 0 1),
        C.presheaf.germ (nvCover s 0) (genericPoint C) h0 (ratio s 0 2)} = ⊤) :
    ∀ y : C.presheaf.stalk (genericPoint C),
      y ∈ ((toProjectiveSpaceOver s hs sC).stalkMap (genericPoint C)).hom.range := by
  letI := functionFieldAlgebra sC
  obtain ⟨F, hF⟩ := range_stalkMap_genericPoint sC (toProjectiveSpaceOver s hs sC)
    (projectiveSpaceOver 2 (Spec (.of k)) ↘ Spec (.of k)) (toProjectiveSpaceOver_fst s hs sC)
  have hm : ∀ m : Fin 3, C.presheaf.germ (nvCover s 0) (genericPoint C) h0 (ratio s 0 m) ∈
      ((toProjectiveSpaceOver s hs sC).stalkMap (genericPoint C)).hom.range := fun m =>
    mem_range_stalkMap_of_comp_eq _ (projectiveSpaceOver.toIntegralAtUniverse 2 (Spec (.of k)))
      (toProjectiveSpaceAtUniverse s hs) (toProjectiveSpaceOver_snd s hs sC) _
      (germ_ratio_mem_range_stalkMap s hs 0 m h0)
  have hle : IntermediateField.adjoin k {C.presheaf.germ (nvCover s 0) (genericPoint C) h0 (ratio
      s 0 1),
        C.presheaf.germ (nvCover s 0) (genericPoint C) h0 (ratio s 0 2)} ≤ F := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ (rfl | rfl)
    · show _ ∈ (F : Set C.functionField)
      rw [hF]; exact hm 1
    · show _ ∈ (F : Set C.functionField)
      rw [hF]; exact hm 2
  rw [hgen] at hle
  intro y
  have : y ∈ (F : Set C.functionField) := hle trivial
  rwa [hF] at this

end StalkRange

section Topology

open TopologicalSpace

/-- **A specialization in a T0 space strictly shrinks the closure of a point.** Stated at
`TopologicalSpace.IrreducibleCloseds` so that it can be chained into a length-two chain. -/
private theorem closureSingleton_lt_of_specializes {Z : Type*} [TopologicalSpace Z] [T0Space Z]
    {x y : Z} (hxy : x ⤳ y) (hne : x ≠ y) :
    IrreducibleCloseds.closureSingleton y < IrreducibleCloseds.closureSingleton x := by
  refine lt_of_le_of_ne ?_ ?_
  · rw [← SetLike.coe_subset_coe, IrreducibleCloseds.coe_closureSingleton,
      IrreducibleCloseds.coe_closureSingleton]
    exact closure_minimal
      (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hxy)) isClosed_closure
  · intro heq
    have hclosures : closure ({y} : Set Z) = closure {x} := by
      simpa only [IrreducibleCloseds.coe_closureSingleton] using
        congrArg (fun C : IrreducibleCloseds Z => (C : Set Z)) heq
    have hyx : y ⤳ x := by
      rw [specializes_iff_mem_closure, hclosures]
      exact subset_closure rfl
    exact hne (hxy.antisymm hyx).eq

/-- **A T0 space of dimension at most one has no chain of three distinct specializations.** -/
private theorem not_specializes_chain_of_topologicalKrullDim_le_one {T : Type*} [TopologicalSpace T]
    [T0Space T]
    (hdim : topologicalKrullDim T ≤ 1) {a b c : T} (hab : a ⤳ b) (hbc : b ⤳ c)
    (h1 : a ≠ b) (h2 : b ≠ c) : False := by
  have h01 := closureSingleton_lt_of_specializes hbc h2
  have h12 := closureSingleton_lt_of_specializes hab h1
  have hchain : (2 : WithBot ℕ∞) ≤ topologicalKrullDim T := by
    unfold topologicalKrullDim Order.krullDim
    refine le_iSup_of_le
      (((RelSeries.singleton _ (IrreducibleCloseds.closureSingleton a)).cons
        (IrreducibleCloseds.closureSingleton b)
          (by exact h12)).cons
          (IrreducibleCloseds.closureSingleton c)
          (by exact h01)) le_rfl
  have : (2 : WithBot ℕ∞) ≤ 1 := hchain.trans hdim
  norm_num at this

/-- **Every point of a sober space is a specialization of a generic point lying in any given set
of generic points.** -/
private theorem exists_specializes_mem_of_genericPoints_subset {Z : Type*} [TopologicalSpace Z]
    [T0Space Z] [QuasiSober Z] {U : Set Z} (hgeneric : genericPoints Z ⊆ U) (z : Z) :
    ∃ η : Z, η ⤳ z ∧ η ∈ U := by
  have hirr : IsIrreducible (irreducibleComponent z) := isIrreducible_irreducibleComponent
  refine ⟨hirr.genericPoint, ?_, hgeneric ?_⟩
  · exact (hirr.isGenericPoint_genericPoint isClosed_irreducibleComponent).specializes
      mem_irreducibleComponent
  · change closure ({hirr.genericPoint} : Set Z) ∈ irreducibleComponents Z
    rw [(hirr.isGenericPoint_genericPoint isClosed_irreducibleComponent).def]
    exact irreducibleComponent_mem_irreducibleComponents z

/-- **In a Noetherian sober space of dimension at most one, the complement of an open subset
containing all the generic points is a finite set of closed points.** -/
private theorem finite_compl_of_genericPoints_subset {Z : Type*} [TopologicalSpace Z] [T0Space Z]
    [QuasiSober Z] [NoetherianSpace Z] {U : Set Z} (hU : IsOpen U)
    (hdim : topologicalKrullDim Z ≤ 1) (hgeneric : genericPoints Z ⊆ U) :
    (Uᶜ).Finite ∧ ∀ z ∈ Uᶜ, IsClosed ({z} : Set Z) := by
  obtain ⟨S, hSfinite, hSclosed, hSirred, hScover⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hU.isClosed_compl
  have hsingleton : ∀ C ∈ S, ∃ z, C = {z} := by
    intro C hC
    have hCirr : IsIrreducible C := hSirred C hC
    set η := hCirr.genericPoint with hηdef
    have hηC : IsGenericPoint η C := hCirr.isGenericPoint_genericPoint (hSclosed C hC)
    have hnotU : η ∉ U := by
      have : η ∈ Uᶜ := hScover ▸ Set.mem_sUnion.mpr ⟨C, hC, hηC.mem⟩
      exact this
    obtain ⟨ξ, hξη, hξU⟩ := exists_specializes_mem_of_genericPoints_subset hgeneric η
    have hξne : ξ ≠ η := fun h => hnotU (h ▸ hξU)
    have hEq : ∀ z ∈ C, z = η := by
      intro z hz
      by_contra hne
      exact not_specializes_chain_of_topologicalKrullDim_le_one hdim hξη (hηC.specializes hz) hξne
        (Ne.symm hne)
    refine ⟨η, ?_⟩
    ext z
    simp only [Set.mem_singleton_iff]
    exact ⟨hEq z, fun hz => hz ▸ hηC.mem⟩
  refine ⟨?_, ?_⟩
  · rw [hScover]
    refine hSfinite.sUnion fun C hC => ?_
    obtain ⟨z, rfl⟩ := hsingleton C hC
    exact Set.finite_singleton z
  · intro z hz
    obtain ⟨C, hC, hzC⟩ := Set.mem_sUnion.mp (hScover ▸ hz)
    obtain ⟨w, hw⟩ := hsingleton C hC
    rw [hw, Set.mem_singleton_iff] at hzC
    subst hzC
    exact hw ▸ hSclosed C hC

end Topology

section ZeroSet

attribute [local implicit_reducible] AlgebraicGeometry.projectiveSpaceAtUniverse

variable {C : Scheme.{u}} {L : C.Modules} [Stacks.Ample.IsInvertibleModule C L]
  {k : Type u} [Field k] [IsIntegral C]

/-- The zero locus of a section of an invertible module on an integral curve proper over `k`,
not vanishing at the generic point, is finite. -/
private theorem finite_compl_nvOpen (sC : C ⟶ Spec (.of k)) [IsProper sC]
    (hdim : topologicalKrullDim C ≤ 1) (u : Γ(L, ⊤)) (hη : genericPoint C ∈ nvOpen L u) :
    ((nvOpen L u : Set C)ᶜ).Finite := by
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian sC
  have : CompactSpace C := (quasiCompact_iff_compactSpace sC).1 inferInstance
  have : IsNoetherian C := ⟨⟩
  exact (finite_compl_of_genericPoints_subset (nvOpen L u).isOpen hdim (by
    intro x hx
    rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
    exact hx ▸ hη)).1

/-- Global functions on a proper integral scheme over an algebraically closed field are
constants. -/
private theorem surjective_appTop_of_isAlgClosed' [IsAlgClosed k] (sC : C ⟶ Spec (.of k))
    [IsProper sC] :
    Function.Surjective ((Scheme.ΓSpecIso (.of k)).inv ≫ sC.appTop).hom := by
  let : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ sC.appTop).hom.toAlgebra
  let : Field Γ(C, ⊤) := (isField_of_universallyClosed k sC).toField
  let : Module.Finite k Γ(C, ⊤) := by
    rw [← RingHom.finite_algebraMap]
    exact (finite_appTop_of_universallyClosed k sC).comp
      (RingHom.Finite.of_surjective ((Scheme.ΓSpecIso (.of k)).inv.hom)
        (fun x => ⟨(Scheme.ΓSpecIso (.of k)).hom.hom x, by simp⟩))
  have : Algebra.IsIntegral k Γ(C, ⊤) := Algebra.IsIntegral.of_finite k _
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := Γ(C, ⊤))).surjective

/-- The morphism attached to generating sections whose first ratio is not a constant is not
constant: otherwise the first chart is everything and the ratio is a global function. -/
private theorem not_exists_range_eq_singleton [IsAlgClosed k] (sC : C ⟶ Spec (.of k)) [IsProper sC]
    (s : Fin 3 → Γ(L, ⊤)) (hs : GeneratesStalks s) (h0 : genericPoint C ∈ nvCover s 0)
    (hnot : letI := functionFieldAlgebra sC
      C.presheaf.germ (nvCover s 0) (genericPoint C) h0 (ratio s 0 1) ∉
        Set.range (algebraMap k C.functionField)) :
    ¬ ∃ q, Set.range (toProjectiveSpaceOver s hs sC) = {q} := by
  letI := functionFieldAlgebra sC
  rintro ⟨q, hq⟩
  have hpre := preimage_basicOpen_eq_nvCover_canonical s hs 0
  have hg : ∀ c : C, toProjectiveSpaceOver s hs sC c = q := fun c =>
    (Set.eq_singleton_iff_unique_mem.mp hq).2 _ ⟨c, rfl⟩
  have hat : ∀ c : C, toProjectiveSpaceAtUniverse s hs c =
      projectiveSpaceOver.toIntegralAtUniverse 2 (Spec (.of k)) q := fun c => by
    rw [← toProjectiveSpaceOver_snd s hs sC, Scheme.Hom.comp_apply, hg]
  have hmem : ∀ c d : C, toProjectiveSpaceAtUniverse s hs c = toProjectiveSpaceAtUniverse s hs d →
      (c ∈ nvCover s 0 ↔ d ∈ nvCover s 0) := by
    intro c d h
    obtain ⟨D, hD⟩ : ∃ D : (projectiveSpaceAtUniverse.{u} 2).Opens,
      toProjectiveSpaceAtUniverse s hs ⁻¹ᵁ D = nvCover s 0 := ⟨_, hpre⟩
    rw [← hD]
    show toProjectiveSpaceAtUniverse s hs c ∈ D ↔ toProjectiveSpaceAtUniverse s hs d ∈ D
    rw [h]
  have hT : nvCover s 0 = ⊤ := by
    refine eq_top_iff.mpr fun c _ => ?_
    exact (hmem c (genericPoint C) ((hat c).trans (hat _).symm)).mpr h0
  obtain ⟨c₀, hc₀⟩ := surjective_appTop_of_isAlgClosed' sC
    (C.presheaf.map (homOfLE hT.ge).op (ratio s 0 1))
  apply hnot
  refine ⟨c₀, ?_⟩
  have h1 := TopCat.Presheaf.germ_res_apply C.presheaf (homOfLE hT.ge) (genericPoint C) trivial
    (ratio s 0 1)
  rw [← hc₀] at h1
  exact h1

end ZeroSet

section GermCombo

variable {C : Scheme.{u}} {L : C.Modules} [Stacks.Ample.IsInvertibleModule C L]
  {k : Type u} [Field k] [IsIntegral C] {ι κ : Type*} [Fintype ι]

/-- At the generic point, the ratio of a combination of sections by the first one is the same
combination, with coefficients in `k`, of the ratios. -/
private theorem germ_ratio_sectionCombo (sC : C ⟶ Spec (.of k)) (x : ι → Γ(L, ⊤)) (i₀ : ι)
    (h : genericPoint C ∈ nvCover x i₀) (c : ι → k) (t : κ → Γ(L, ⊤)) (a b : κ)
    (ht0 : t a = x i₀)
    (ht1 : t b = sectionCombo ((Scheme.ΓSpecIso (.of k)).inv ≫ sC.appTop).hom x c)
    (h0 : genericPoint C ∈ nvCover t a) :
    letI := functionFieldAlgebra sC
    C.presheaf.germ (nvCover t a) (genericPoint C) h0 (ratio t a b) =
      ∑ m, c m • C.presheaf.germ (nvCover x i₀) (genericPoint C) h (ratio x i₀ m) := by
  letI := functionFieldAlgebra sC
  have hWx : nvCover t a ≤ nvCover x i₀ := by
    show nvOpen L (t a) ≤ nvOpen L (x i₀)
    rw [ht0]
  have key := resO_ratio_sectionCombo _ x i₀ c t a b ht0 ht1 (nvCover t a) le_rfl hWx
  have h1 := TopCat.Presheaf.germ_res_apply C.presheaf (homOfLE (le_refl (nvCover t a)))
    (genericPoint C) h0 (ratio t a b)
  change _ = C.presheaf.germ (nvCover t a) (genericPoint C) h0 (ratio t a b) at h1
  rw [← h1]
  change C.presheaf.germ (nvCover t a) (genericPoint C) h0 (resO le_rfl (ratio t a b)) = _
  rw [key, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, Algebra.smul_def]
  congr 1
  · exact (TopCat.Presheaf.germ_res_apply C.presheaf (homOfLE (le_top : nvCover t a ≤ ⊤))
      (genericPoint C) h0 _).trans rfl
  · exact TopCat.Presheaf.germ_res_apply C.presheaf (homOfLE hWx) (genericPoint C) h0
      (ratio x i₀ m)

end GermCombo

end Selection

open Stacks.ProjectiveFromSections Stacks.TwistPullbackPinned in
/-- A general linear projection of `C ⊆ ℙᴺ_k` to a morphism `g : C ⟶ ℙ²_k` of the same
degree, nonconstant, whose map on the local ring at the generic point is onto. -/
private theorem exists_projection_morphism
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (N : ℕ) {C : Scheme.{u}} (i : C ⟶ projectiveSpaceOver N (Spec (.of k)))
    [IsClosedImmersion i] [IsIntegral C] (hC : topologicalKrullDim C = 1) :
    ∃ g : C ⟶ projectiveSpaceOver 2 (Spec (.of k)),
      g ≫ projectiveSpaceOver 2 (Spec (.of k)) ↘ Spec (.of k) =
        i ≫ projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of k) ∧
      Nonempty ((Scheme.Modules.pullback g).obj (projectiveSpaceTwistingSheaf 2 (Spec (.of k))) ≅
        (Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf N (Spec (.of k)))) ∧
      (¬ ∃ x, Set.range g = {x}) ∧
      ∀ y : C.presheaf.stalk (genericPoint C), y ∈ (g.stalkMap (genericPoint C)).hom.range := by
  classical
  set sC := i ≫ projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of k) with hsC
  haveI : IsProper sC := inferInstance
  letI := functionFieldAlgebra sC
  set x := pullbackCoordSection (toModel k i) with hx
  have hxs : GeneratesStalks x := Stacks.ProjectiveSpaceModuli.taut_generates (toModel k i)
  obtain ⟨i₀, h, hgen⟩ := exists_coordinate_ratios_generate k i
  have htr : Algebra.trdeg k C.functionField = 1 := by
    have h1 := toENat_trdeg_functionField (sX := sC)
    rw [hC] at h1
    have h2 : Cardinal.toENat (Algebra.trdeg k C.functionField) = 1 := by exact_mod_cast h1
    exact Cardinal.toENat_eq_one.mp h2
  let β : k →+* Γ(C, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ sC.appTop).hom
  have hfin := finite_compl_nvOpen sC hC.le (x i₀) h
  choose W hWne hW using fun p : C => exists_subspace_notMem_nvOpen β x hxs p
  let a : Fin (N + 1) → C.functionField := fun m =>
    C.presheaf.germ (nvCover x i₀) (genericPoint C) h (ratio x i₀ m)
  obtain ⟨c, d, hcW, hc, hcd⟩ := exists_two_generators a hgen htr (hfin.toFinset.image W) (by
    intro w hw
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hw
    exact hWne p)
  let t : Fin 3 → Γ((Scheme.Modules.pullback (toModel k i)).obj
      (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} N), ⊤) :=
    ![x i₀, sectionCombo β x c, sectionCombo β x d]
  have hts : GeneratesStalks t := by
    rw [Stacks.AmpleImmersionReduction.generatesStalks_iff_forall_exists_mem]
    intro p
    by_cases hp : p ∈ nvOpen _ (x i₀)
    · exact ⟨0, hp⟩
    · exact ⟨1, hW p c (hcW _ (Finset.mem_image_of_mem W (hfin.mem_toFinset.mpr hp)))⟩
  have h0 : genericPoint C ∈ nvCover t 0 := h
  have hg1 := germ_ratio_sectionCombo sC x i₀ h c t 0 1 rfl rfl h0
  have hg2 := germ_ratio_sectionCombo sC x i₀ h d t 0 2 rfl rfl h0
  have e1 : C.presheaf.germ (nvCover t 0) (genericPoint C) h0 (ratio t 0 1) = combo a c := by
    rw [hg1, combo_apply]
  have e2 : C.presheaf.germ (nvCover t 0) (genericPoint C) h0 (ratio t 0 2) = combo a d := by
    rw [hg2, combo_apply]
  refine exists_projection_morphism_of_sections k i t hts ?_ ?_
  · exact stalkMap_range_eq_top sC t hts h0 (by rwa [e1, e2])
  · exact not_exists_range_eq_singleton sC t hts h0 (by rwa [e1])

/-- An integral closed curve in `ℙᴺ_k` admits a finite birational morphism onto a plane curve
of the same degree. -/
private theorem exists_finite_birational_plane_projection
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (N : ℕ) {C : Scheme.{u}} (i : C ⟶ projectiveSpaceOver N (Spec (.of k)))
    [IsClosedImmersion i] [IsIntegral C] (hC : topologicalKrullDim C = 1) :
    ∃ (C' : Scheme.{u}) (i' : C' ⟶ projectiveSpaceOver 2 (Spec (.of k)))
      (_ : IsClosedImmersion i') (_ : IsIntegral C') (f : C ⟶ C')
      (hC' : topologicalKrullDim C' = 1),
      IsFinite f ∧ AlgebraicGeometry.IsBirational f ∧
      f ≫ i' ≫ projectiveSpaceOver 2 (Spec (.of k)) ↘ Spec (.of k) =
        i ≫ projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of k) ∧
      hilbertDegree k (projectiveSpaceOver 2 (Spec (.of k)) ↘ Spec (.of k)) i' 1 hC'
          (projectiveSpaceTwistingSheaf 2 (Spec (.of k))) =
        hilbertDegree k (projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of k)) i 1 hC
          (projectiveSpaceTwistingSheaf N (Spec (.of k))) := by
  obtain ⟨g, hg, ⟨e⟩, hnc, hsurj⟩ := exists_projection_morphism k N i hC
  have hPN : IsProper (i ≫ projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of k)) := inferInstance
  haveI hPg : IsProper (g ≫ projectiveSpaceOver 2 (Spec (.of k)) ↘ Spec (.of k)) := by
    rwa [hg]
  haveI hVar : AlgebraicGeometry.IsVariety k (i ≫ projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of
      k)) :=
    AlgebraicGeometry.IsVariety.mk
  haveI hCurve : AlgebraicGeometry.IsCurve k (i ≫ projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of
      k)) :=
    (AlgebraicGeometry.isCurve_iff _ _).mpr ⟨hVar, hC⟩
  haveI hCurve' : AlgebraicGeometry.IsCurve k (g ≫ projectiveSpaceOver 2 (Spec (.of k)) ↘ Spec
      (.of k)) := by
    rwa [hg]
  haveI : IsProper g := IsProper.of_comp g (projectiveSpaceOver 2 (Spec (.of k)) ↘ Spec (.of k))
  haveI : AlgebraicGeometry.IsCurve k (g.imageι ≫ projectiveSpaceOver 2 (Spec (.of k)) ↘ Spec (.of
      k)) :=
    MMP.Mori.isCurve_imageι_comp _ g hnc
  haveI : IsIntegral g.image := inferInstance
  haveI : IsDominant g.toImage := inferInstance
  haveI : LocallyOfFiniteType g := inferInstance
  haveI : LocallyOfFiniteType g.toImage := inferInstance
  have hgenpt : g.toImage (genericPoint C) = genericPoint g.image := by
    refine IsGenericPoint.eq ?_ (genericPoint_spec g.image)
    have h1 := (genericPoint_spec C).image g.toImage.continuous
    have h2 : closure (g.toImage '' Set.univ) = Set.univ := by
      rw [Set.image_univ]; exact g.toImage.denseRange.closure_range
    rwa [h2] at h1
  have hiso : IsIso (g.toImage.stalkMap (genericPoint C)) := by
    have hsurj' : Function.Surjective (g.toImage.stalkMap (genericPoint C)).hom := by
      intro y
      obtain ⟨z, hz⟩ := RingHom.mem_range.mp (hsurj y)
      obtain ⟨E, hE⟩ : ∃ E : (projectiveSpaceOver 2 (Spec (.of k))).presheaf.stalk
            ((g.toImage ≫ g.imageι) (genericPoint C)) ≅
          (projectiveSpaceOver 2 (Spec (.of k))).presheaf.stalk (g (genericPoint C)),
          (g.toImage ≫ g.imageι).stalkMap (genericPoint C) = E.hom ≫ g.stalkMap (genericPoint C) :=
        ⟨_, Scheme.Hom.stalkMap_congr_hom _ _ g.toImage_imageι _⟩
      rw [Scheme.Hom.stalkMap_comp] at hE
      obtain ⟨z', hz'⟩ := (ConcreteCategory.bijective_of_isIso E.hom).2 z
      refine ⟨(g.imageι.stalkMap (g.toImage (genericPoint C))).hom z', ?_⟩
      have h3 : (g.toImage.stalkMap (genericPoint C)).hom
          ((g.imageι.stalkMap (g.toImage (genericPoint C))).hom z') =
          (g.stalkMap (genericPoint C)).hom (E.hom.hom z') :=
        ConcreteCategory.congr_hom hE z'
      rw [h3, hz', hz]
    have hinj : Function.Injective (g.toImage.stalkMap (genericPoint C)).hom := by
      have hF : IsField (g.image.presheaf.stalk (g.toImage (genericPoint C))) := by
        rw [hgenpt]; exact Field.toIsField g.image.functionField
      letI : Field (g.image.presheaf.stalk (g.toImage (genericPoint C))) := hF.toField
      exact RingHom.injective _
    exact (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj'⟩
  have hbir : AlgebraicGeometry.IsBirational g.toImage := by
    simp only [AlgebraicGeometry.isBirational_iff, genericPoints_eq_singleton, Set.bijOn_singleton,
      Set.mem_singleton_iff, forall_eq]
    exact ⟨hgenpt, hiso⟩
  have hdeg1 : degreeOver g.toImage = 1 := by
    letI : Algebra g.image.functionField C.functionField :=
      (dominantFunctionFieldMap g.toImage).toAlgebra
    rw [degreeOver_eq_finrank g.toImage rfl]
    have hb : Function.Bijective (algebraMap g.image.functionField C.functionField) := by
      show Function.Bijective (dominantFunctionFieldMap g.toImage)
      have key : ∀ (z : g.image) (h : g.toImage.base (genericPoint C) = z),
          Function.Bijective ((h ▸ g.toImage.stalkMap (genericPoint C)).hom) := by
        intro z h
        cases h
        exact ConcreteCategory.bijective_of_isIso _
      exact key _ _
    exact (AlgEquiv.ofBijective (Algebra.ofId g.image.functionField C.functionField)
      hb).toLinearEquiv.finrank_eq.symm.trans (Module.finrank_self _)
  have hhg : g.toImage ≫ g.imageι ≫ projectiveSpaceOver 2 (Spec (.of k)) ↘ Spec (.of k) =
      i ≫ projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of k) := by
    rw [← Category.assoc, g.toImage_imageι, hg]
  haveI : IsProper (g.imageι ≫ projectiveSpaceOver 2 (Spec (.of k)) ↘ Spec (.of k)) :=
    isProper_imageι_comp g _
  refine ⟨g.image, g.imageι, inferInstance, inferInstance, g.toImage,
    AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one
      (f := g.imageι ≫ projectiveSpaceOver 2 (Spec (.of k)) ↘ Spec (.of k)), ?_, hbir, hhg, ?_⟩
  · exact isFinite_of_not_constant k _ _ g.toImage hhg (MMP.Mori.not_exists_toImage_eq g hnc)
  · rw [hilbertDegree_one_eq_degreeOn, hilbertDegree_one_eq_degreeOn]
    have hproj := MMP.Mori.degreeOn_eq_degreeOver_mul
      (projectiveSpaceOver 2 (Spec (.of k)) ↘ Spec (.of k)) g
      (projectiveSpaceTwistingSheaf 2 (Spec (.of k))) hnc
    rw [hdeg1] at hproj
    have hdegeq : degreeOn k (projectiveSpaceOver 2 (Spec (.of k)) ↘ Spec (.of k)) g hC.le
        (projectiveSpaceTwistingSheaf 2 (Spec (.of k))) =
        degreeOn k (projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of k)) i hC.le
          (projectiveSpaceTwistingSheaf N (Spec (.of k))) := by
      unfold degreeOn
      rw [invertibleCurveDegree_congr_structure hg]
      exact invertibleCurveDegree_eq_of_iso k _ _ e
    rw [← hdegeq]
    simpa using hproj.symm

/-- The Castelnuovo-type bound `2 p_a(C) ≤ (e - 1)(e - 2)` for an integral curve of degree `e`
in `ℙᴺ_k`, by general projection to a plane curve of degree `e`. -/
private theorem two_mul_arithmeticGenus_le
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (N : ℕ) {C : Scheme.{u}} (i : C ⟶ projectiveSpaceOver N (Spec (.of k)))
    [IsClosedImmersion i] [IsIntegral C] (hC : topologicalKrullDim C = 1) :
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
      (i ≫ projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of k))
    2 * arithmeticGenus (i ≫ projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of k)) ≤
      (hilbertDegree k (projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of k)) i 1 hC
          (projectiveSpaceTwistingSheaf N (Spec (.of k))) - 1) *
        (hilbertDegree k (projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of k)) i 1 hC
          (projectiveSpaceTwistingSheaf N (Spec (.of k))) - 2) := by
  obtain ⟨C', i', hi', hint', f, hC', hfin, hbir, hcomm, hdeg⟩ :=
    exists_finite_birational_plane_projection k N i hC
  haveI := hi'
  haveI := hint'
  haveI := hfin
  have h1 := two_mul_arithmeticGenus_plane_curve k i' hC'
  have hc := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
    (i ≫ projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of k))
  have hc' := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
    (i' ≫ projectiveSpaceOver 2 (Spec (.of k)) ↘ Spec (.of k))
  have h2 := arithmeticGenus_le_of_birational k
    (i ≫ projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of k))
    (i' ≫ projectiveSpaceOver 2 (Spec (.of k)) ↘ Spec (.of k)) f hcomm hbir hC.le hC'.le
  rw [hdeg] at h1
  have h3 : (2 : ℤ) * arithmeticGenus (i ≫ projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of k)) ≤
      2 * arithmeticGenus (i' ≫ projectiveSpaceOver 2 (Spec (.of k)) ↘ Spec (.of k)) := by
    linarith
  exact h3.trans h1.le

section DisjointCopies

open CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.ProjectiveFromSections Stacks.TwistPullbackPinned
open Stacks.SectionsToProjectiveSpace (coordGrading)

/-! ### Products of sheaves of modules on a coproduct -/

private noncomputable def secFunctor (X : Scheme.{u}) (U : X.Opens) : X.Modules ⥤ Type u :=
  SheafOfModules.evaluation X.ringCatSheaf (Opposite.op U) ⋙ forget _

private instance (X : Scheme.{u}) (U : X.Opens) {J : Type u} [Finite J] :
    PreservesLimitsOfShape (Discrete J) (secFunctor X U) := by
  unfold secFunctor
  exact comp_preservesLimitsOfShape _ _

private theorem pi_app_bijective (X : Scheme.{u}) (U : X.Opens) {J : Type u} [Finite J]
    (E : J → X.Modules) :
    Function.Bijective (fun z : Γ(∏ᶜ E, U) => fun j => (Pi.π E j).app U z) := by
  have hlim := isLimitOfPreserves (secFunctor X U) (productIsProduct E)
  constructor
  · intro z z' h
    have := hlim.hom_ext (W := PUnit.{u+1}) (f := (TypeCat.ofHom (fun _ => z) : PUnit.{u+1} ⟶
        (secFunctor X U).obj (∏ᶜ E)))
      (f' := (TypeCat.ofHom (fun _ => z') : PUnit.{u+1} ⟶ (secFunctor X U).obj (∏ᶜ E))) (fun j => by
      ext _
      exact congrFun h j.as)
    exact congrArg (fun f : PUnit.{u+1} ⟶ (secFunctor X U).obj (∏ᶜ E) => ConcreteCategory.hom
        f PUnit.unit) this
  · intro t
    let c : Cone (Discrete.functor E ⋙ secFunctor X U) :=
      { pt := PUnit.{u+1}
        π := { app := fun j => TypeCat.ofHom (fun _ => t j.as)
               naturality := by
                 rintro ⟨a⟩ ⟨b⟩ ⟨⟨rfl⟩⟩
                 rfl } }
    refine ⟨(ConcreteCategory.hom (hlim.lift c)) PUnit.unit, funext fun j => ?_⟩
    exact congrArg (fun f : PUnit.{u+1} ⟶ (secFunctor X U).obj (E j) => ConcreteCategory.hom
        f PUnit.unit) (hlim.fac c ⟨j⟩)

private theorem glue_bijective {X : Scheme.{u}} (M : X.Modules) {I : Type u} (A : I → X.Opens)
    (U : X.Opens) (hAU : ∀ i, A i ≤ U)
    (hdisj : Pairwise fun i j => Disjoint (A i) (A j)) (hcover : U ≤ iSup A) :
    Function.Bijective (fun x : Γ(M, U) => fun i : I => M.presheaf.map (homOfLE (hAU i)).op x) := by
  let S : TopCat.Sheaf Ab X.toTopCat := ⟨M.presheaf, Scheme.Modules.isSheaf M⟩
  have hbot : ∀ (W : X.Opens), W = ⊥ → ∀ (a b : ToType (S.1.obj (op W))), a = b := by
    rintro W rfl a b
    exact TopCat.Sheaf.eq_of_locally_eq' S (fun _ : PEmpty.{u+1} => (⊥ : X.Opens)) ⊥ (fun e =>
        e.elim)
      (by simp) a b (fun e => e.elim)
  refine ⟨fun a b hab => TopCat.Sheaf.eq_of_locally_eq' S A U (fun i => homOfLE (hAU i)) hcover
    a b (congrFun hab), fun t => ?_⟩
  have hcompat : TopCat.Presheaf.IsCompatible S.1 A t := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rfl
    · exact hbot _ (disjoint_iff.mp (hdisj hij)) _ _
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' S A U
    (fun i => homOfLE (hAU i)) hcover t hcompat
  exact ⟨s, funext hs⟩

open Scheme.Modules in
private theorem sigma_modules_iso {I : Type u} [Finite I] (W : I → Scheme.{u})
    (F : (∐ W : Scheme.{u}).Modules) :
    IsIso (Pi.lift (fun i => (restrictAdjunction (Sigma.ι W i)).unit.app F) :
      F ⟶ ∏ᶜ fun i => (pushforward (Sigma.ι W i)).obj ((restrictFunctor (Sigma.ι W i)).obj F)) := by
  rw [Hom.isIso_iff_isIso_app]
  intro U
  rw [ConcreteCategory.isIso_iff_bijective]
  set E : I → (∐ W : Scheme.{u}).Modules := fun i =>
    (pushforward (Sigma.ι W i)).obj ((restrictFunctor (Sigma.ι W i)).obj F) with hE
  have hρ := pi_app_bijective (∐ W : Scheme.{u}) U E
  have hdisj : Pairwise fun i j => Disjoint ((Sigma.ι W i) ''ᵁ ((Sigma.ι W i) ⁻¹ᵁ U))
      ((Sigma.ι W j) ''ᵁ ((Sigma.ι W j) ⁻¹ᵁ U)) := by
    intro i j hij
    refine (disjoint_opensRange_sigmaι W i j hij).mono ?_ ?_ <;> exact fun x ⟨y, _, hy⟩ => ⟨y, hy⟩
  have hcov : U ≤ ⨆ i, (Sigma.ι W i) ''ᵁ ((Sigma.ι W i) ⁻¹ᵁ U) := by
    intro x hx
    obtain ⟨i, y, rfl⟩ := Stacks.Chow.exists_mem_range_sigmaι W x
    exact Opens.mem_iSup.mpr ⟨i, y, hx, rfl⟩
  have hglue := glue_bijective F (fun i => (Sigma.ι W i) ''ᵁ ((Sigma.ι W i) ⁻¹ᵁ U)) U
    (fun i => (Sigma.ι W i).image_preimage_le U) hdisj hcov
  refine (Function.Bijective.of_comp_iff' hρ _).mp ?_
  have key : ((fun z j => (ConcreteCategory.hom (Hom.app (Pi.π E j) U)) z) ∘
      ⇑(ConcreteCategory.hom (Hom.app (Pi.lift fun i ↦ (restrictAdjunction (Sigma.ι W i)).unit.app
          F) U))) =
      fun x i => (ConcreteCategory.hom (F.presheaf.map (homOfLE ((Sigma.ι W i).image_preimage_le
          U)).op)) x := by
    funext x i
    have h1 : (Pi.lift fun i ↦ (restrictAdjunction (Sigma.ι W i)).unit.app F) ≫ Pi.π E i =
        (restrictAdjunction (Sigma.ι W i)).unit.app F := Pi.lift_comp_π _ _
    have h2 := congrArg (fun φ => ConcreteCategory.hom (Hom.app φ U) x) h1
    simp only [Hom.comp_app] at h2
    exact h2
  have hb : Function.Bijective ((fun z j => (ConcreteCategory.hom (Hom.app (Pi.π E j) U)) z) ∘
      ⇑(ConcreteCategory.hom (Hom.app (Pi.lift fun i ↦ (restrictAdjunction (Sigma.ι W i)).unit.app
          F) U))) := by
    rw [key]
    exact hglue
  exact hb

/-! ### Disjoint unions of closed immersions -/

private theorem isClosedImmersion_sigmaDesc {I : Type u} [Finite I] (W : I → Scheme.{u})
    {Y : Scheme.{u}} (ψ : ∀ i, W i ⟶ Y) [∀ i, IsClosedImmersion (ψ i)]
    (hdisj : Pairwise fun i j => Disjoint (Set.range (ψ i)) (Set.range (ψ j))) :
    IsClosedImmersion (Sigma.desc ψ) := by
  have : ∀ i, SurjectiveOnStalks (ψ i) := inferInstance
  have := Stacks.Chow.surjectiveOnStalks_sigmaDesc W ψ
  have hfin : LocallyFinite fun i => Set.range (ψ i) := locallyFinite_of_finite _
  have := Stacks.Chow.isProper_sigmaDesc_of_locallyFinite W ψ hfin
  have hinj : Function.Injective (Sigma.desc ψ) := by
    intro x y hxy
    obtain ⟨i, x', rfl⟩ := Stacks.Chow.exists_mem_range_sigmaι W x
    obtain ⟨j, y', rfl⟩ := Stacks.Chow.exists_mem_range_sigmaι W y
    have h1 : ψ i x' = ψ j y' := by
      have e1 : (Sigma.desc ψ) ((Sigma.ι W i) x') = ψ i x' := by
        rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]
      have e2 : (Sigma.desc ψ) ((Sigma.ι W j) y') = ψ j y' := by
        rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]
      rwa [← e1, ← e2]
    by_cases hij : i = j
    · subst hij
      have := (ψ i).injective h1
      rw [this]
    · exact absurd ⟨y', h1.symm⟩ (Set.disjoint_left.mp (hdisj hij) ⟨x', rfl⟩)
  have hclosed : IsClosedMap (Sigma.desc ψ) := (Sigma.desc ψ).isClosedMap
  have hemb : Topology.IsClosedEmbedding (Sigma.desc ψ) :=
    Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap (Sigma.desc ψ).continuous hinj
        hclosed
  have : IsPreimmersion (Sigma.desc ψ) := ⟨hemb.isEmbedding⟩
  exact IsClosedImmersion.of_isPreimmersion _ hemb.isClosed_range

/-! ### Constant sections of `ℙ¹_X ⟶ X` -/

private noncomputable def cs {X : Scheme.{u}} {k : Type u} [Field k] (f : X ⟶ Spec (.of k))
    (c : k) : Γ(X, ⊤) :=
  f.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom c)

private noncomputable def secVec {X : Scheme.{u}} {k : Type u} [Field k] (f : X ⟶ Spec (.of k))
    (c : k) : Fin 2 → Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), ⊤) :=
  ![(show Γ(X, ⊤) from 1 : Γ(X, ⊤)), cs f c]

private theorem mem_nvCover_zero {X : Scheme.{u}} {k : Type u} [Field k] (f : X ⟶ Spec (.of k))
    (c : k) (x : X) :
    x ∈ nvCover (secVec f c) 0 := by
  change x ∈ Stacks.Ample.nonvanishingLocus (SheafOfModules.unit X.ringCatSheaf : X.Modules) _
  refine (Stacks.SectionProduct.mem_nonvanishingLocus_iff_generates (X := X)
    (SheafOfModules.unit X.ringCatSheaf : X.Modules) _ x).mpr ?_
  intro w
  obtain ⟨r, hr⟩ := Stacks.UnitStalk.surjective_toUnitStalk X x w
  exact ⟨r, hr.symm⟩

private theorem generatesStalks_secVec {X : Scheme.{u}} {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) (c : k) :
    GeneratesStalks (secVec f c) :=
  Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem _ fun x => ⟨0,
      mem_nvCover_zero f c x⟩

private theorem ratio_secVec {X : Scheme.{u}} {k : Type u} [Field k] (f : X ⟶ Spec (.of k))
    (c : k) :
    ratio (secVec f c) 0 1 = X.presheaf.map (homOfLE (le_top : nvCover (secVec f c) 0 ≤ ⊤)).op (cs
        f c) := by
  symm
  refine eq_div _ le_rfl ?_
  show _ * _ = _
  change X.presheaf.map _ (cs f c) * X.presheaf.map _ (1 : Γ(X, ⊤)) = X.presheaf.map _ (cs f c)
  rw [map_one]
  exact mul_one _

private noncomputable def sect {X : Scheme.{u}} {k : Type u} [Field k] (f : X ⟶ Spec (.of k))
    (c : k) : X ⟶ projectiveSpaceOver 1 X :=
  toProjectiveSpaceOver (secVec f c) (generatesStalks_secVec f c) (𝟙 X)

private theorem sect_comp {X : Scheme.{u}} {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) (c : k) :
    sect f c ≫ projectiveSpaceOver 1 X ↘ X = 𝟙 X :=
  toProjectiveSpaceOver_fst _ _ _

private instance isClosedImmersion_sect {X : Scheme.{u}} {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) (c : k) :
    IsClosedImmersion (sect f c) := by
  haveI : IsSeparated (projectiveSpaceOver 1 X ↘ X) := inferInstance
  haveI : IsClosedImmersion (sect f c ≫ projectiveSpaceOver 1 X ↘ X) := by
    rw [sect_comp]; infer_instance
  exact IsClosedImmersion.of_comp (sect f c) (projectiveSpaceOver 1 X ↘ X)

private theorem sect_twist {X : Scheme.{u}} {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) (c : k) :
    Nonempty ((Scheme.Modules.pullback (sect f c)).obj (projectiveSpaceTwistingSheaf 1 X) ≅
      (SheafOfModules.unit X.ringCatSheaf : X.Modules)) := by
  obtain ⟨α, hαiso, -⟩ :=
      AlgebraicGeometry.exists_iso_twistingSheafAtUniverse_toProjectiveSpaceAtUniverse
    (secVec f c) (generatesStalks_secVec f c)
  haveI := hαiso
  exact ⟨(Stacks.AmpleProjectiveImmersion.liftOverTwistIso _
    (toProjectiveSpaceAtUniverse (secVec f c) (generatesStalks_secVec f c))) ≪≫ asIso α⟩

private theorem disjoint_range_of_appLE_eq_zero_of_isUnit {X P : Scheme.{u}} (σ₁ σ₂ : X ⟶ P)
    (U : P.Opens) (g : Γ(P, U))
    (hz : ∀ x : X, ∃ (W : X.Opens) (_ : x ∈ W) (hW : W ≤ σ₁ ⁻¹ᵁ U), σ₁.appLE U W hW g = 0)
    (hu : ∀ y : X, ∃ (W : X.Opens) (_ : y ∈ W) (hW : W ≤ σ₂ ⁻¹ᵁ U), IsUnit (σ₂.appLE U W hW g)) :
    Disjoint (Set.range σ₁) (Set.range σ₂) := by
  rw [Set.disjoint_left]
  rintro z ⟨x, rfl⟩ ⟨y, hy⟩
  obtain ⟨W₁, hxW₁, hW₁, h1⟩ := hz x
  obtain ⟨W₂, hyW₂, hW₂, h2⟩ := hu y
  have hxU : σ₁ x ∈ U := hW₁ hxW₁
  have hyU : σ₂ y ∈ U := hW₂ hyW₂
  have hnu : ¬ IsUnit (P.presheaf.germ U (σ₁ x) hxU g) := by
    intro hunit
    have hmap : IsUnit (σ₁.stalkMap x (P.presheaf.germ U (σ₁ x) hxU g)) := hunit.map _
    have e : σ₁.stalkMap x (P.presheaf.germ U (σ₁ x) hxU g) =
        X.presheaf.germ W₁ x hxW₁ (σ₁.appLE U W₁ hW₁ g) := by
      rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE, ConcreteCategory.comp_apply,
        X.presheaf.germ_res_apply]
    rw [e, h1, map_zero] at hmap
    exact not_isUnit_zero hmap
  have hun : IsUnit (P.presheaf.germ U (σ₂ y) hyU g) := by
    have e : σ₂.stalkMap y (P.presheaf.germ U (σ₂ y) hyU g) =
        X.presheaf.germ W₂ y hyW₂ (σ₂.appLE U W₂ hW₂ g) := by
      rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE, ConcreteCategory.comp_apply,
        X.presheaf.germ_res_apply]
    have : IsUnit (σ₂.stalkMap y (P.presheaf.germ U (σ₂ y) hyU g)) := by
      rw [e]; exact h2.map _
    exact (isUnit_of_map_unit (σ₂.stalkMap y).hom _ this)
  have hcongr : ∀ (a b : P) (hab : a = b) (ha : a ∈ U) (hb : b ∈ U),
      IsUnit (P.presheaf.germ U a ha g) ↔ IsUnit (P.presheaf.germ U b hb g) := by
    intro a b hab ha hb; subst hab; rfl
  exact hnu ((hcongr _ _ hy.symm _ hyU).mpr hun)

section Disj

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{u}} {k : Type u} [Field k] (f : X ⟶ Spec (.of k))

/-- the standard open `D₊(T₀)` of the integral model -/
private noncomputable abbrev stdOpen : (projectiveSpaceAtUniverse.{u} 1).Opens :=
  AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} 1) (MvPolynomial.X 0)

/-- the coordinate function `T₁ / T₀` -/
private noncomputable abbrev coordFn : Γ(projectiveSpaceAtUniverse.{u} 1, stdOpen) :=
  (AlgebraicGeometry.Proj.awayToSection (coordGrading.{u} 1) (MvPolynomial.X 0)).hom
      (coordFrac.{u} 0 1)

private noncomputable abbrev coordOpen : (projectiveSpaceOver 1 X).Opens :=
  (projectiveSpaceOver.toIntegralAtUniverse 1 X) ⁻¹ᵁ stdOpen

private noncomputable abbrev coordSec : Γ(projectiveSpaceOver 1 X, coordOpen (X := X)) :=
  (projectiveSpaceOver.toIntegralAtUniverse 1 X).app stdOpen coordFn

private theorem sect_snd (c : k) : sect f c ≫ projectiveSpaceOver.toIntegralAtUniverse 1 X =
    toProjectiveSpaceAtUniverse (secVec f c) (generatesStalks_secVec f c) :=
  toProjectiveSpaceOver_snd _ _ _

private theorem nvCover_le_sect (c : k) :
    nvCover (secVec f c) 0 ≤ sect f c ⁻¹ᵁ coordOpen (X := X) := by
  have hpin := ι_toProjectiveSpaceAtUniverse (secVec f c) (generatesStalks_secVec f c) 0
  have := nvCover_le_preimage_basicOpen (secVec f c) (toProjectiveSpaceAtUniverse (secVec f c)
    (generatesStalks_secVec f c)) 0 hpin
  rw [← sect_snd f c] at this
  exact this

private theorem sect_appLE_coordSec (c : k) :
    (sect f c).appLE coordOpen (nvCover (secVec f c) 0) (nvCover_le_sect f c) coordSec =
      X.presheaf.map (homOfLE (le_top : nvCover (secVec f c) 0 ≤ ⊤)).op (cs f c) := by
  set s := secVec f c
  set hs := generatesStalks_secVec f c
  set g := toProjectiveSpaceAtUniverse s hs
  have hpin := ι_toProjectiveSpaceAtUniverse s hs 0
  have hle := nvCover_le_preimage_basicOpen s g 0 hpin
  have hchart := appLE_coordFrac_chart s g 0 1 hpin
  have e1 : coordSec (X := X) = (projectiveSpaceOver.toIntegralAtUniverse 1 X).appLE stdOpen
      (coordOpen (X := X)) le_rfl coordFn := by
    unfold coordSec
    rw [Scheme.Hom.app_eq_appLE]
  have e2 := Scheme.Hom.appLE_comp_appLE (sect f c) (projectiveSpaceOver.toIntegralAtUniverse 1 X)
    stdOpen (coordOpen (X := X)) (nvCover s 0) le_rfl (nvCover_le_sect f c)
  have key : ∀ (φ ψ : X ⟶ projectiveSpaceAtUniverse.{u} 1) (h : φ = ψ) (e : nvCover s 0 ≤ φ ⁻¹ᵁ
      stdOpen)
      (e' : nvCover s 0 ≤ ψ ⁻¹ᵁ stdOpen),
      φ.appLE stdOpen (nvCover s 0) e coordFn = ψ.appLE stdOpen (nvCover s 0) e' coordFn := by
    intro φ ψ h; subst h; intros; rfl
  rw [e1]
  have e3 := ConcreteCategory.congr_hom e2 coordFn
  rw [ConcreteCategory.comp_apply] at e3
  rw [e3]
  rw [key _ g (sect_snd f c) _ hle]
  exact hchart.trans (ratio_secVec f c)

end Disj

section Disj2

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{u}} {k : Type u} [Field k] (f : X ⟶ Spec (.of k))

private theorem appLE_of_eq_id (φ : X ⟶ X) (hφ : φ = 𝟙 X) (N : X.Opens) (e : N ≤ φ ⁻¹ᵁ ⊤) (a :
    Γ(X, ⊤)) :
    φ.appLE ⊤ N e a = X.presheaf.map (homOfLE (le_top : N ≤ ⊤)).op a := by
  subst hφ
  simp [Scheme.Hom.appLE]

private noncomputable def piPull (a : Γ(X, ⊤)) : Γ(projectiveSpaceOver 1 X, coordOpen (X := X)) :=
  (projectiveSpaceOver 1 X ↘ X).appLE ⊤ coordOpen (by simp) a

private theorem sect_appLE_piPull (c : k) (a : Γ(X, ⊤)) :
    (sect f c).appLE coordOpen (nvCover (secVec f c) 0) (nvCover_le_sect f c) (piPull a) =
      X.presheaf.map (homOfLE (le_top : nvCover (secVec f c) 0 ≤ ⊤)).op a := by
  have e2 := Scheme.Hom.appLE_comp_appLE (sect f c) (projectiveSpaceOver 1 X ↘ X)
    ⊤ coordOpen (nvCover (secVec f c) 0) (by simp) (nvCover_le_sect f c)
  have e3 := ConcreteCategory.congr_hom e2 a
  rw [ConcreteCategory.comp_apply] at e3
  unfold piPull
  rw [e3]
  exact appLE_of_eq_id _ (sect_comp f c) _ _ _

end Disj2

section Disj3

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{u}} {k : Type u} [Field k] (f : X ⟶ Spec (.of k))

private theorem cs_sub (c d : k) : cs f (d - c) = cs f d - cs f c := by
  unfold cs
  rw [map_sub, map_sub]

private theorem isUnit_cs {c : k} (hc : c ≠ 0) : IsUnit (cs f c) := by
  unfold cs
  exact (IsUnit.mk0 c hc).map ((f.appTop.hom).comp (Scheme.ΓSpecIso (.of k)).inv.hom)

private theorem sect_disjoint {c d : k} (h : c ≠ d) :
    Disjoint (Set.range (sect f c)) (Set.range (sect f d)) := by
  refine disjoint_range_of_appLE_eq_zero_of_isUnit (sect f c) (sect f d) coordOpen
    (coordSec (X := X) - piPull (cs f c)) (fun x => ⟨nvCover (secVec f c) 0, mem_nvCover_zero f c x,
      nvCover_le_sect f c, ?_⟩) (fun y => ⟨nvCover (secVec f d) 0, mem_nvCover_zero f d y,
      nvCover_le_sect f d, ?_⟩)
  · rw [map_sub, sect_appLE_coordSec, sect_appLE_piPull, sub_self]
  · rw [map_sub, sect_appLE_coordSec, sect_appLE_piPull, ← map_sub, ← cs_sub]
    exact (isUnit_cs f (sub_ne_zero.2 h.symm)).map _

end Disj3

/-! ### Dimension of a coproduct -/

private theorem topologicalKrullDim_sigma_le {I : Type u} (W : I → Scheme.{u}) (n : WithBot ℕ∞)
    (h : ∀ i, topologicalKrullDim (W i) ≤ n) : topologicalKrullDim (∐ W : Scheme.{u}) ≤ n := by
  rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
  refine iSup_le fun x => ?_
  obtain ⟨i, y, rfl⟩ := Stacks.Chow.exists_mem_range_sigmaι W x
  haveI : IsOpenImmersion (Sigma.ι W i) := inferInstance
  haveI : IsIso ((Sigma.ι W i).stalkMap y) := inferInstanceAs (IsIso ((Sigma.ι W
      i).toLRSHom.stalkMap y))
  have e : ringKrullDim ((∐ W : Scheme.{u}).presheaf.stalk (Sigma.ι W i y)) =
      ringKrullDim ((W i).presheaf.stalk y) :=
    ringKrullDim_eq_of_ringEquiv (asIso ((Sigma.ι W i).stalkMap y)).commRingCatIsoToRingEquiv
  rw [e]
  refine le_trans ?_ (h i)
  rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
  exact le_iSup (fun y => ringKrullDim ((W i).presheaf.stalk y)) y

/-! ### Proper curves from non-constant maps -/

private theorem isProperCurve_of_curve_map {k : Type u} [Field k] {Z C : Scheme.{u}}
    (sZ : Z ⟶ Spec (.of k)) [IsSeparated sZ] [LocallyOfFiniteType sZ] [IsIntegral C]
    (φ : C ⟶ Z) [AlgebraicGeometry.IsCurve k (φ ≫ sZ)] [IsProper (φ ≫ sZ)]
    (hnc : ¬ ∃ x : Z, Set.range φ = {x}) : IsProperCurve sZ (φ (genericPoint C)) := by
  have : IsProper φ := IsProper.of_comp φ sZ
  have hker : φ.ker = Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure {φ (genericPoint C)}) := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    congr 1
    refine Closeds.ext ?_
    rw [Closeds.coe_closure, Closeds.coe_closure, φ.isClosedMap.isClosed_range.closure_eq]
    apply le_antisymm
    · rintro _ ⟨c, rfl⟩
      have hc : c ∈ closure {genericPoint C} := by
        rw [(genericPoint_spec C).def]; trivial
      have := image_closure_subset_closure_image φ.continuous ⟨_, hc, rfl⟩
      rwa [Set.image_singleton] at this
    · exact closure_minimal (by rintro _ rfl; exact ⟨_, rfl⟩) φ.isClosedMap.isClosed_range
  have hcurve := isCurve_imageι_comp sZ φ hnc
  have hdim : topologicalKrullDim (curveSubschemeAt (φ (genericPoint C))) = 1 := by
    have h1 := hcurve.topologicalKrullDim_eq_one
    change topologicalKrullDim φ.ker.subscheme = 1 at h1
    rwa [hker] at h1
  have hprop : IsProper (curveSubschemeAtι (φ (genericPoint C)) ≫ sZ) := by
    have h1 : IsProper (φ.imageι ≫ sZ) := isProper_imageι_comp φ sZ
    change IsProper (φ.ker.subschemeι ≫ sZ) at h1
    rwa [hker] at h1
  exact ⟨hdim, hprop⟩

/-! ### Points with a proper specialization -/

/-- a point `x` of an open-and-closed piece with a proper specialization is the generic point -/
private theorem eq_genericPoint_of_exists_proper_specialization {W Z : Type*} [TopologicalSpace W]
    [TopologicalSpace Z] [T0Space W] [QuasiSober W] [IrreducibleSpace W]
    (hdim : topologicalKrullDim W ≤ 1) (ι : W → Z) (hι : Topology.IsInducing ι)
    (hcl : IsClosed (Set.range ι)) {y : W} {x' : Z} (hx' : ι y ⤳ x') (hne : x' ≠ ι y) :
    y = genericPoint W := by
  by_contra hy
  have hx'mem : x' ∈ Set.range ι := hcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr ⟨y,
      rfl⟩)
    (specializes_iff_mem_closure.mp hx')
  obtain ⟨y', rfl⟩ := hx'mem
  have hyy' : y ⤳ y' := hι.specializes_iff.mp hx'
  have hne' : y ≠ y' := fun h => hne (by rw [h])
  exact not_specializes_chain_of_topologicalKrullDim_le_one hdim (genericPoint_specializes y) hyy'
    (Ne.symm hy) hne'

/-! ### Disjoint copies of the components of a 1-cycle -/

section Cycle

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  (π : Y ⟶ X) {P : Type u} [Fintype P] (W : P → ProperCurve sX)

/-- The coproduct of the pieces `W p`. -/
private noncomputable abbrev pieces : Scheme.{u} := ∐ fun p => (W p).scheme

/-- The inclusion of the piece `W p` into the coproduct. -/
private noncomputable abbrev pieceι (p : P) : (W p).scheme ⟶ pieces W :=
  Sigma.ι (fun p => (W p).scheme) p

variable {W} (ψ : pieces W ⟶ Y) (hψ : ∀ p, pieceι W p ≫ ψ ≫ π = (W p).ι)

include hψ in
private theorem piece_comp (p : P) : pieceι W p ≫ ψ ≫ π ≫ sX = (W p).ι ≫ sX := by
  rw [← hψ p]; simp

private instance (p : P) : IsOpenImmersion (pieceι W p) := inferInstance

private theorem not_exists_range_pieceι_eq_singleton (p : P) :
    ¬ ∃ z : pieces W, Set.range (pieceι W p) = {z} := by
  rintro ⟨z, hz⟩
  have hsub : Subsingleton (W p).scheme := ⟨fun a b => by
    have ha : pieceι W p a ∈ Set.range (pieceι W p) := ⟨a, rfl⟩
    have hb : pieceι W p b ∈ Set.range (pieceι W p) := ⟨b, rfl⟩
    rw [hz] at ha hb
    exact (pieceι W p).isOpenEmbedding.injective ((Set.mem_singleton_iff.mp ha).trans
      (Set.mem_singleton_iff.mp hb).symm)⟩
  have h0 : topologicalKrullDim (W p).scheme ≤ 0 := by
    have : DiscreteTopology (W p).scheme := inferInstance
    exact topologicalKrullDim_zero_of_discreteTopology _
  have h1 := (W p).dim_eq
  rw [h1] at h0
  norm_num at h0

variable [IsSeparated (ψ ≫ π ≫ sX)] [LocallyOfFiniteType (ψ ≫ π ≫ sX)]

include hψ in
private theorem piece_isProperCurve (p : P) :
    IsProperCurve (ψ ≫ π ≫ sX) (pieceι W p (genericPoint (W p).scheme)) := by
  have hc := piece_comp π ψ hψ p
  haveI : AlgebraicGeometry.IsCurve k (pieceι W p ≫ (ψ ≫ π ≫ sX)) := by
    rw [hc]; exact (W p).isCurve
  haveI : IsProper (pieceι W p ≫ (ψ ≫ π ≫ sX)) := by rw [hc]; infer_instance
  exact isProperCurve_of_curve_map (ψ ≫ π ≫ sX) (pieceι W p)
    (not_exists_range_pieceι_eq_singleton p)

include hψ in
private theorem exists_piece_of_isProperCurve (D : ProperCurve (ψ ≫ π ≫ sX)) :
    ∃ p : P, D.point = pieceι W p (genericPoint (W p).scheme) := by
  set x := D.point with hx
  have hdim := D.dim_eq
  have hspec : ∃ x', x ⤳ x' ∧ x' ≠ x := by
    by_contra h
    push Not at h
    have hsub : Subsingleton (curveSubschemeAt x) := ⟨fun t u => by
      have key : ∀ t : curveSubschemeAt x, curveSubschemeAtι x t = x := fun t => by
        have ht : curveSubschemeAtι x t ∈ closure {x} :=
          range_curveSubschemeAtι x ▸ ⟨t, rfl⟩
        exact h _ (specializes_iff_mem_closure.mpr ht)
      exact (curveSubschemeAtι x).isEmbedding.injective ((key t).trans (key u).symm)⟩
    have h0 : topologicalKrullDim (curveSubschemeAt x) ≤ 0 := by
      have : DiscreteTopology (curveSubschemeAt x) := inferInstance
      exact topologicalKrullDim_zero_of_discreteTopology _
    rw [hdim] at h0
    norm_num at h0
  obtain ⟨x', hxx', hne⟩ := hspec
  obtain ⟨p, y, hy⟩ := Stacks.Chow.exists_mem_range_sigmaι (fun p => (W p).scheme) x
  refine ⟨p, ?_⟩
  have hy' : y = genericPoint (W p).scheme := by
    refine eq_genericPoint_of_exists_proper_specialization (W p).dim_le (pieceι W p)
      (pieceι W p).isOpenEmbedding.isInducing
      (Stacks.Chow.isClosedImmersion_sigmaι (fun p => (W p).scheme)
          p).isClosedEmbedding.isClosed_range
      (x' := x') ?_ ?_
    · rwa [show pieceι W p y = x from hy]
    · rwa [show pieceι W p y = x from hy]
  rw [← hy', show pieceι W p y = x from hy]

omit [Fintype P] in
private theorem length_stalk_piece (p : P) :
    (Module.length ((pieces W).presheaf.stalk (pieceι W p (genericPoint (W p).scheme)))
      ((pieces W).presheaf.stalk (pieceι W p (genericPoint (W p).scheme)))).toNat = 1 := by
  haveI : IsOpenImmersion (pieceι W p) := inferInstance
  haveI : IsIso ((pieceι W p).stalkMap (genericPoint (W p).scheme)) :=
    inferInstanceAs (IsIso ((pieceι W p).toLRSHom.stalkMap (genericPoint (W p).scheme)))
  have e := (asIso ((pieceι W p).stalkMap (genericPoint (W p).scheme))).commRingCatIsoToRingEquiv
  have hF : IsField ((pieces W).presheaf.stalk (pieceι W p (genericPoint (W p).scheme))) :=
    e.toMulEquiv.isField (Field.toIsField (W p).scheme.functionField)
  letI := hF.toField
  rw [Module.length_eq_one]
  rfl

private theorem residueFieldDegree_eq_one_of_isIso_stalkMap' {A B : Scheme.{u}} (f : A ⟶ B) (x : A)
    (h : IsIso (f.stalkMap x)) : residueFieldDegree f x = 1 := by
  unfold residueFieldDegree
  let _ := (f.residueFieldMap x).hom.toAlgebra
  have : IsIso (f.residueFieldMap x) :=
    ((IsLocalRing.ResidueField.mapEquiv
      (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv).toCommRingCatIso).isIso_hom
  have hbij : Function.Bijective (algebraMap (B.residueField (f x)) (A.residueField x)) :=
    (asIso (f.residueFieldMap x)).commRingCatIsoToRingEquiv.bijective
  rw [← (AlgEquiv.ofBijective (Algebra.ofId _ _) hbij).toLinearEquiv.finrank_eq,
    Module.finrank_self]

omit [Fintype P] in
private theorem residueFieldDegree_piece {ψ : pieces W ⟶ Y}
    (hψ : ∀ p, pieceι W p ≫ ψ ≫ π = (W p).ι) (p : P) :
    residueFieldDegree (ψ ≫ π) (pieceι W p (genericPoint (W p).scheme)) = 1 := by
  haveI : IsOpenImmersion (pieceι W p) := inferInstance
  have h1 := Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion (W p).ι (genericPoint (W
      p).scheme)
  have h2 := residueDegree_comp (pieceι W p) (ψ ≫ π) (genericPoint (W p).scheme)
  have h3 : residueFieldDegree (pieceι W p) (genericPoint (W p).scheme) = 1 :=
    residueFieldDegree_eq_one_of_isIso_stalkMap' _ _
      (inferInstanceAs (IsIso ((pieceι W p).toLRSHom.stalkMap (genericPoint (W p).scheme))))
  rw [hψ p, h1, show (pieceι W p).residueDegree (genericPoint (W p).scheme) = 1 from h3,
    mul_one] at h2
  exact h2.symm

include hψ in
private theorem exists_cycle_sigma :
    ∃ Γ : OneCycle ℤ (ψ ≫ π ≫ sX),
      (∀ D : ProperCurve (ψ ≫ π ≫ sX),
        Γ D = ((Module.length ((pieces W).presheaf.stalk D.point)
          ((pieces W).presheaf.stalk D.point)).toNat : ℤ)) ∧
      OneCycle.pushforward ℤ (ψ ≫ π ≫ sX) sX (ψ ≫ π) Γ = ∑ p, Finsupp.single (W p) (1 : ℤ) := by
  classical
  let D : P → ProperCurve (ψ ≫ π ≫ sX) := fun p =>
    ⟨pieceι W p (genericPoint (W p).scheme), piece_isProperCurve π ψ hψ p⟩
  have hDinj : Function.Injective D := by
    intro p q hpq
    by_contra hne
    have h1 : pieceι W p (genericPoint (W p).scheme) = pieceι W q (genericPoint (W q).scheme) :=
      congrArg ProperCurve.point hpq
    exact Set.disjoint_left.mp (Stacks.Chow.pairwise_disjoint_range_sigmaι
      (fun p => (W p).scheme) hne) ⟨_, rfl⟩ ⟨_, h1.symm⟩
  refine ⟨∑ p, Finsupp.single (D p) (1 : ℤ), ?_, ?_⟩
  · intro D'
    obtain ⟨p, hp⟩ := exists_piece_of_isProperCurve π ψ hψ D'
    obtain rfl : D' = D p := ProperCurve.ext hp
    have hsum : (∑ q, Finsupp.single (D q) (1 : ℤ)) (D p) = 1 := by
      rw [Finsupp.finsetSum_apply, Finset.sum_eq_single p]
      · simp
      · intro q _ hq
        rw [Finsupp.single_apply, if_neg (fun h => hq (hDinj h))]
      · simp
    rw [hsum]
    exact_mod_cast (length_stalk_piece p).symm
  · rw [map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    have h1 : OneCycle.pushforward ℤ (ψ ≫ π ≫ sX) sX (ψ ≫ π) (Finsupp.single (D p) (1 : ℤ)) =
        cyclePushforwardOfPoint ℤ sX (ψ ≫ π) (D p).point :=
      OneCycle.pushforward_cycle ℤ sX (ψ ≫ π) (D p)
    rw [h1]
    have hpt : (ψ ≫ π) (D p).point = (W p).point := by
      show (ψ ≫ π) (pieceι W p (genericPoint (W p).scheme)) = _
      rw [← Scheme.Hom.comp_apply, hψ p]
      exact (W p).ι_genericPoint
    have hh : IsProperCurve sX ((ψ ≫ π) (D p).point) := hpt ▸ (W p).isProperCurve
    simp only [cyclePushforwardOfPoint, dif_pos hh]
    rw [residueFieldDegree_piece π hψ p]
    congr 1
    exact ProperCurve.ext hpt

end Cycle

section ChiSigma

open Stacks.SheafOfModules.Invertible

private noncomputable def twistedSheafProdIso {X : Scheme.{u}} {J : Type u} [Finite J]
    (E : J → X.Modules) (L : Fin 2 → X.Modules)
    [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)] (n : Fin 2 → ℤ) :
    twistedSheaf (∏ᶜ E) L n ≅ ∏ᶜ fun j => twistedSheaf (E j) L n := by
  haveI h0 : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (tensorPower X.presheaf X.ringCatSheaf.2 (L 0) (n 0)) := inferInstance
  haveI h1 : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (tensorPower X.presheaf X.ringCatSheaf.2 (L 1) (n 1)) := inferInstance
  let T₀ : X.Modules ⥤ X.Modules := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      X.sheaf).flip.obj
    (tensorPower X.presheaf X.ringCatSheaf.2 (L 0) (n 0))
  let T₁ : X.Modules ⥤ X.Modules := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      X.sheaf).flip.obj
    (tensorPower X.presheaf X.ringCatSheaf.2 (L 1) (n 1))
  haveI : T₀.IsEquivalence :=
      AlgebraicGeometry.CoherentModuleFunctors.tensorRightFunctor_isEquivalence _
  haveI : T₁.IsEquivalence :=
      AlgebraicGeometry.CoherentModuleFunctors.tensorRightFunctor_isEquivalence _
  haveI p0 : PreservesLimitsOfShape (Discrete J) T₀ := inferInstance
  haveI p1 : PreservesLimitsOfShape (Discrete J) T₁ := inferInstance
  haveI : PreservesLimit (Discrete.functor E) T₀ := p0.preservesLimit
  haveI : PreservesLimit (Discrete.functor fun j => T₀.obj (E j)) T₁ := p1.preservesLimit
  exact T₁.mapIso (PreservesProduct.iso T₀ E) ≪≫ PreservesProduct.iso T₁ (fun j => T₀.obj (E j))

private theorem eulerCharacteristic_pi {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] {P : Type u} [Fintype P] (E : P → X.Modules)
    [hE : ∀ p, (E p).IsCoherent]
    [hEb : (∏ᶜ E).IsCoherent] :
    eulerCharacteristic k f (∏ᶜ E) = ∑ p, eulerCharacteristic k f (E p) := by
  classical
  let n := Fintype.card P
  let e : P ≃ Fin n := Fintype.equivFin P
  let E' : Fin n → X.Modules := fun j => E (e.symm j)
  have hcoh : ∀ j, (E' j).IsCoherent := fun j => hE _
  haveI : HasBiproduct E' := HasBiproduct.of_hasProduct E'
  have hEb' : (⨁ E').IsCoherent := AlgebraicGeometry.SheafOfModules.isCoherent_biproduct E' hcoh
  have key := AlgebraicGeometry.eulerCharacteristic_biproduct k f E' hcoh hEb'
    (X.affineCoverNum ⊤)
    (fun j m _ => AlgebraicGeometry.finiteDimensional_cohomologyOverField_of_isProper k f (E' j) m)
    (fun j m hm => by
      haveI : (E' j).IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent (M := E' j)
      exact AlgebraicGeometry.isZero_cohomologyOverField_of_affineCoverNum_le k f (E' j) m hm)
  have e2 : ∏ᶜ E ≅ ⨁ E' :=
    (Pi.whiskerEquiv e.symm (fun j => Iso.refl _)).symm ≪≫ (biproduct.isoProduct E').symm
  rw [eulerCharacteristic_eq_of_iso k f e2, key]
  exact Equiv.sum_comp e.symm (fun p => eulerCharacteristic k f (E p))

private theorem eulerCharacteristic_sigma_twist {k : Type u} [Field k] {P : Type u} [Fintype P]
    (W : P → Scheme.{u}) (f : (∐ W : Scheme.{u}) ⟶ Spec (.of k)) [IsProper f]
    [hpr : ∀ p, IsProper (Sigma.ι W p ≫ f)]
    (L : Fin 2 → (∐ W : Scheme.{u}).Modules)
    [hL : ∀ t, SheafOfModules.IsInvertible (∐ W : Scheme.{u}).presheaf
      (∐ W : Scheme.{u}).ringCatSheaf.2 (L t)]
    [hLp : ∀ p t, SheafOfModules.IsInvertible (W p).presheaf (W p).ringCatSheaf.2
      ((Scheme.Modules.pullback (Sigma.ι W p)).obj (L t))]
    (n : Fin 2 → ℤ)
    [hT : (twistedSheaf (SheafOfModules.unit (∐ W : Scheme.{u}).ringCatSheaf) L n).IsCoherent]
    [hM : ∀ p, (twistedSheaf (SheafOfModules.unit (W p).ringCatSheaf)
      (fun t => (Scheme.Modules.pullback (Sigma.ι W p)).obj (L t)) n).IsCoherent] :
    eulerCharacteristic k f (twistedSheaf (SheafOfModules.unit (∐ W : Scheme.{u}).ringCatSheaf) L
        n) =
      ∑ p, eulerCharacteristic k (Sigma.ι W p ≫ f)
        (twistedSheaf (SheafOfModules.unit (W p).ringCatSheaf)
          (fun t => (Scheme.Modules.pullback (Sigma.ι W p)).obj (L t)) n) := by
  classical
  haveI : IsLocallyNoetherian (∐ W : Scheme.{u}) :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isLocallyNoetherian_of_isProper_over_field k f
  haveI : ∀ p, IsClosedImmersion (Sigma.ι W p) := fun p => Stacks.Chow.isClosedImmersion_sigmaι W p
  let e1a : (SheafOfModules.unit (∐ W : Scheme.{u}).ringCatSheaf : (∐ W : Scheme.{u}).Modules) ≅
      ∏ᶜ fun p => (Scheme.Modules.pushforward (Sigma.ι W p)).obj
        ((Scheme.Modules.restrictFunctor (Sigma.ι W p)).obj
          (SheafOfModules.unit (∐ W : Scheme.{u}).ringCatSheaf : (∐ W : Scheme.{u}).Modules)) :=
    @asIso _ _ _ _ _ (sigma_modules_iso W (SheafOfModules.unit (∐ W : Scheme.{u}).ringCatSheaf :
      (∐ W : Scheme.{u}).Modules))
  let e1 : (SheafOfModules.unit (∐ W : Scheme.{u}).ringCatSheaf : (∐ W : Scheme.{u}).Modules) ≅
      ∏ᶜ fun p => (Scheme.Modules.pushforward (Sigma.ι W p)).obj
        (SheafOfModules.unit (W p).ringCatSheaf : (W p).Modules) :=
    e1a ≪≫ Pi.mapIso fun p => (Scheme.Modules.pushforward (Sigma.ι W p)).mapIso
        (Scheme.Modules.restrictUnitIso (Sigma.ι W p))
  let e2 := twistedSheafIsoOfIso L e1 n
  let e3 := twistedSheafProdIso (fun p => (Scheme.Modules.pushforward (Sigma.ι W p)).obj
        (SheafOfModules.unit (W p).ringCatSheaf : (W p).Modules)) L n
  let e4 : (∏ᶜ fun p => twistedSheaf ((Scheme.Modules.pushforward (Sigma.ι W p)).obj
        (SheafOfModules.unit (W p).ringCatSheaf : (W p).Modules)) L n) ≅
      ∏ᶜ fun p => (Scheme.Modules.pushforward (Sigma.ι W p)).obj
        (twistedSheaf (SheafOfModules.unit (W p).ringCatSheaf)
          (fun t => (Scheme.Modules.pullback (Sigma.ι W p)).obj (L t)) n) :=
    Pi.mapIso fun p => pushforwardTwistedSheafIso (Sigma.ι W p) L
      (SheafOfModules.unit (W p).ringCatSheaf : (W p).Modules) n
  let eT := e2 ≪≫ e3 ≪≫ e4
  haveI hE : ∀ p, ((Scheme.Modules.pushforward (Sigma.ι W p)).obj
      (twistedSheaf (SheafOfModules.unit (W p).ringCatSheaf)
        (fun t => (Scheme.Modules.pullback (Sigma.ι W p)).obj (L t)) n)).IsCoherent := fun p =>
    isCoherent_pushforward_of_isClosedImmersion (Sigma.ι W p) _
  haveI hEb : (∏ᶜ fun p => (Scheme.Modules.pushforward (Sigma.ι W p)).obj
      (twistedSheaf (SheafOfModules.unit (W p).ringCatSheaf)
        (fun t => (Scheme.Modules.pullback (Sigma.ι W p)).obj (L t)) n)).IsCoherent :=
    Stacks.AlgebraicGeometry.RelativeSerreVanishing.isCoherent_of_iso eT hT
  rw [eulerCharacteristic_eq_of_iso k f eT, eulerCharacteristic_pi]
  refine Finset.sum_congr rfl fun p _ => ?_
  exact eulerCharacteristic_pushforward_of_isClosedImmersion k (Sigma.ι W p) f _ (hM p) (hE p)

/-- The Hilbert degree of a proper curve `C ⊆ X ⊆ ℙᴹ_k` is its degree for `𝒪(1)|_X`. -/
private theorem hilbertDegree_properCurve_eq_degree
    (k : Type u) [Field k] (M : ℕ) {X : Scheme.{u}}
    (j : X ⟶ projectiveSpaceOver M (Spec (.of k))) [IsClosedImmersion j]
    (C : ProperCurve (j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k))) :
    hilbertDegree k (projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k))
      (C.ι ≫ j) 1 C.dim_eq (projectiveSpaceTwistingSheaf M (Spec (.of k))) =
      C.degree k ((Scheme.Modules.pullback j).obj
        (projectiveSpaceTwistingSheaf M (Spec (.of k)))) := by
  rw [hilbertDegree_one_eq_degreeOn]
  exact (degreeOn_pullback_eq_degreeOn_comp
    (j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k))
    (projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k)) j C.ι rfl C.dim_eq.le _).symm

private theorem eulerCharacteristic_curve_twist
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] (M : ℕ) {X : Scheme.{u}}
    (j : X ⟶ projectiveSpaceOver M (Spec (.of k))) [IsClosedImmersion j]
    (C : ProperCurve (j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k))) (m : ℤ) :
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
      (C.ι ≫ j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k))
    haveI : IsClosedImmersion (C.ι ≫ j) := inferInstance
    haveI : IsProper ((C.ι ≫ j) ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k)) :=
      inferInstance
    subschemeHilbertFunction k (projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k)) (C.ι ≫ j)
        (projectiveSpaceTwistingSheaf M (Spec (.of k))) m =
      C.degree k ((Scheme.Modules.pullback j).obj (projectiveSpaceTwistingSheaf M (Spec (.of k))))
          * m +
        (1 - arithmeticGenus (C.ι ≫ j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k))) := by
  haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
    (C.ι ≫ j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k))
  haveI : IsClosedImmersion (C.ι ≫ j) := inferInstance
  haveI : IsProper ((C.ι ≫ j) ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k)) :=
    inferInstance
  have hC1 : topologicalKrullDim C.scheme = 1 := C.dim_eq
  have hdegEq := hilbertDegree_properCurve_eq_degree k M j C
  obtain ⟨P, hdeg, -, hval⟩ := exists_polynomial_subschemeHilbertFunction_projectiveSpace k M
    (C.ι ≫ j) 1 hC1
  have hvalN : ∀ t : ℕ, P.eval (t : ℚ) = subschemeHilbertFunction k
      (projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k)) (C.ι ≫ j)
      (projectiveSpaceTwistingSheaf M (Spec (.of k))) t := fun t => by
    have := hval (t : ℤ)
    simpa using this
  have hcoef := hilbertDegree_eq_factorial_mul_coeff k
    (projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k)) (C.ι ≫ j) 1 hC1
    (projectiveSpaceTwistingSheaf M (Spec (.of k))) P hdeg.le hvalN
  have h0 := subschemeHilbertFunction_zero k (projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k))
    (C.ι ≫ j) (projectiveSpaceTwistingSheaf M (Spec (.of k)))
  have hP : ∀ x : ℚ, P.eval x = P.coeff 0 + P.coeff 1 * x := fun x => by
    rw [Polynomial.eval_eq_sum_range' (n := 2) (by omega)]
    simp [Finset.sum_range_succ]
  have hc0 : P.coeff 0 = (subschemeHilbertFunction k
      (projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k)) (C.ι ≫ j)
      (projectiveSpaceTwistingSheaf M (Spec (.of k))) 0 : ℚ) := by
    have h := hval 0
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simpa using h
  have hc1 : P.coeff 1 = (C.degree k ((Scheme.Modules.pullback j).obj
      (projectiveSpaceTwistingSheaf M (Spec (.of k)))) : ℚ) := by
    rw [← hdegEq, hcoef]; simp
  have hm := hval m
  rw [hP, hc0, hc1] at hm
  have hassoc : eulerCharacteristic k ((C.ι ≫ j) ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec
      (.of k))
        (SheafOfModules.unit C.scheme.ringCatSheaf) =
      eulerCharacteristic k (C.ι ≫ j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k))
        (SheafOfModules.unit C.scheme.ringCatSheaf) :=
    eulerCharacteristic_congr_hom k _ _ (Category.assoc _ _ _) _
  rw [h0, hassoc] at hm
  unfold arithmeticGenus
  have h2 : ((subschemeHilbertFunction k (projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k))
      (C.ι ≫ j) (projectiveSpaceTwistingSheaf M (Spec (.of k))) m : ℤ) : ℚ) =
      (((C.degree k ((Scheme.Modules.pullback j).obj
        (projectiveSpaceTwistingSheaf M (Spec (.of k)))) * m +
        (1 - (1 - eulerCharacteristic k
          (C.ι ≫ j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k))
          (SheafOfModules.unit C.scheme.ringCatSheaf))) : ℤ)) : ℚ) := by
    rw [← hm]; push_cast; ring
  exact_mod_cast h2

private theorem nonempty_tensorPower_unit_int {X : Scheme.{u}} (n : ℤ) :
    Nonempty (tensorPower X.presheaf X.ringCatSheaf.2
      (SheafOfModules.unit X.ringCatSheaf : X.Modules) n ≅
      (SheafOfModules.unit X.ringCatSheaf : X.Modules)) := by
  have step : ∀ m : ℤ, Nonempty (tensorPower X.presheaf X.ringCatSheaf.2
      (SheafOfModules.unit X.ringCatSheaf : X.Modules) (m + 1) ≅
      tensorPower X.presheaf X.ringCatSheaf.2
      (SheafOfModules.unit X.ringCatSheaf : X.Modules) m) := fun m =>
    ⟨(tensorPowerSuccIso X.presheaf X.ringCatSheaf.2 (SheafOfModules.unit X.ringCatSheaf :
        X.Modules) m).symm
      ≪≫ tensorProductRightUnitor X.presheaf X.ringCatSheaf.2 _⟩
  induction n using Int.induction_on with
  | zero => exact ⟨Iso.refl _⟩
  | succ i ih =>
      obtain ⟨e⟩ := ih
      obtain ⟨s⟩ := step i
      exact ⟨s ≪≫ e⟩
  | pred i ih =>
      obtain ⟨e⟩ := ih
      obtain ⟨s⟩ := step (-(i : ℤ) - 1)
      have : (-(i : ℤ) - 1 + 1) = -(i : ℤ) := by ring
      exact ⟨(tensorPowerReindex X.presheaf X.ringCatSheaf.2 _ this.symm ≪≫ s).symm ≪≫ e⟩

private theorem nonempty_twist2_iso {X : Scheme.{u}} (L : Fin 2 → X.Modules)
    [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)] (N : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]
    (eA : L 0 ≅ N) (eB : L 1 ≅ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) (n : Fin 2 → ℤ) :
    Nonempty (twistedSheaf (SheafOfModules.unit X.ringCatSheaf : X.Modules) L n ≅
      tensorPower X.presheaf X.ringCatSheaf.2 N (n 0)) := by
  obtain ⟨u⟩ := nonempty_tensorPower_unit_int (X := X) (n 1)
  have e : twistedSheaf (SheafOfModules.unit X.ringCatSheaf : X.Modules) L n =
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj
          (SheafOfModules.unit X.ringCatSheaf : X.Modules)).obj
          (tensorPower X.presheaf X.ringCatSheaf.2 (L 0) (n 0)))).obj
        (tensorPower X.presheaf X.ringCatSheaf.2 (L 1) (n 1))) := rfl
  rw [e]
  exact ⟨tensorProductIso X.presheaf X.ringCatSheaf.2 (Iso.refl _)
      (MMP.Mori.Twist.tensorPowerIsoOfIso (L 1) _ eB (n 1) ≪≫ u) ≪≫
    tensorProductRightUnitor X.presheaf X.ringCatSheaf.2 _ ≪≫
    tensorProductLeftUnitor X.presheaf X.ringCatSheaf.2 _ ≪≫
    MMP.Mori.Twist.tensorPowerIsoOfIso (L 0) N eA (n 0)⟩

private theorem nonempty_twist1_iso {X : Scheme.{u}} (A N : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 A]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N] (e : A ≅ N) (m : ℤ) :
    Nonempty (twistedSheaf (SheafOfModules.unit X.ringCatSheaf : X.Modules) (fun _ : Fin 1 => A)
      (fun _ => m) ≅ tensorPower X.presheaf X.ringCatSheaf.2 N m) :=
  ⟨MMP.Mori.Twist.twistedSheafUnitIsoTensorPower (fun _ : Fin 1 => A) N (fun _ => e) (fun _ => m) ≪≫
    eqToIso (congrArg (tensorPower X.presheaf X.ringCatSheaf.2 N)
      (show (∑ _i : Fin 1, m) = m by simp))⟩

private theorem eulerCharacteristic_piece_family
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] (M : ℕ) {X : Scheme.{u}}
    (j : X ⟶ projectiveSpaceOver M (Spec (.of k))) [IsClosedImmersion j]
    (C : ProperCurve (j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k)))
    {Z' : Scheme.{u}} (θ : C.scheme ⟶ Z') (ψ' : Z' ⟶ projectiveSpaceOver 1 X) (c : k)
    (hθ : θ ≫ ψ' = C.ι ≫ sect (j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k)) c)
    (m : ℤ)
    [hinv : ∀ t, SheafOfModules.IsInvertible C.scheme.presheaf C.scheme.ringCatSheaf.2
      ((Scheme.Modules.pullback θ).obj ((Scheme.Modules.pullback ψ').obj
        (![(Scheme.Modules.pullback (projectiveSpaceOver 1 X ↘ X ≫ j)).obj
            (projectiveSpaceTwistingSheaf M (Spec (.of k))),
          projectiveSpaceTwistingSheaf 1 X] t)))]
    [hpr : IsProper (θ ≫ ψ' ≫ projectiveSpaceOver 1 X ↘ X ≫ j ≫
      projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k))]
    [hco : (twistedSheaf (SheafOfModules.unit C.scheme.ringCatSheaf : C.scheme.Modules)
      (fun t => (Scheme.Modules.pullback θ).obj ((Scheme.Modules.pullback ψ').obj
        (![(Scheme.Modules.pullback (projectiveSpaceOver 1 X ↘ X ≫ j)).obj
            (projectiveSpaceTwistingSheaf M (Spec (.of k))),
          projectiveSpaceTwistingSheaf 1 X] t))) (fun _ => m)).IsCoherent] :
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
      (C.ι ≫ j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k))
    eulerCharacteristic k (θ ≫ ψ' ≫ projectiveSpaceOver 1 X ↘ X ≫ j ≫
        projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k))
      (twistedSheaf (SheafOfModules.unit C.scheme.ringCatSheaf : C.scheme.Modules)
        (fun t => (Scheme.Modules.pullback θ).obj ((Scheme.Modules.pullback ψ').obj
          (![(Scheme.Modules.pullback (projectiveSpaceOver 1 X ↘ X ≫ j)).obj
              (projectiveSpaceTwistingSheaf M (Spec (.of k))),
            projectiveSpaceTwistingSheaf 1 X] t))) (fun _ => m)) =
      C.degree k ((Scheme.Modules.pullback j).obj (projectiveSpaceTwistingSheaf M (Spec (.of k)))) *
        m + (1 - arithmeticGenus (C.ι ≫ j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k)))
            := by
  have h1 : θ ≫ ψ' ≫ projectiveSpaceOver 1 X ↘ X ≫ j = C.ι ≫ j := by
    calc θ ≫ ψ' ≫ projectiveSpaceOver 1 X ↘ X ≫ j
        = (θ ≫ ψ') ≫ projectiveSpaceOver 1 X ↘ X ≫ j := (Category.assoc _ _ _).symm
      _ = (C.ι ≫ sect (j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k)) c) ≫
          projectiveSpaceOver 1 X ↘ X ≫ j := by rw [hθ]
      _ = C.ι ≫ (sect (j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k)) c ≫
          projectiveSpaceOver 1 X ↘ X) ≫ j := by simp only [Category.assoc]
      _ = C.ι ≫ j := by rw [sect_comp, Category.id_comp]
  have h2 : θ ≫ ψ' ≫ projectiveSpaceOver 1 X ↘ X ≫ j ≫
      projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k) =
      (C.ι ≫ j) ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k) := by
    rw [← h1]; simp only [Category.assoc]
  obtain ⟨et⟩ := sect_twist (j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k)) c
  let N : C.scheme.Modules := (Scheme.Modules.pullback (C.ι ≫ j)).obj
    (projectiveSpaceTwistingSheaf M (Spec (.of k)))
  let eA : (Scheme.Modules.pullback θ).obj ((Scheme.Modules.pullback ψ').obj
      ((Scheme.Modules.pullback (projectiveSpaceOver 1 X ↘ X ≫ j)).obj
        (projectiveSpaceTwistingSheaf M (Spec (.of k))))) ≅ N :=
    (Scheme.Modules.pullback θ).mapIso
        ((Scheme.Modules.pullbackComp ψ' (projectiveSpaceOver 1 X ↘ X ≫ j)).app _) ≪≫
      ((Scheme.Modules.pullbackComp θ (ψ' ≫ projectiveSpaceOver 1 X ↘ X ≫ j)).app _) ≪≫
      (Scheme.Modules.pullbackCongr h1).app _
  let eB : (Scheme.Modules.pullback θ).obj ((Scheme.Modules.pullback ψ').obj
      (projectiveSpaceTwistingSheaf 1 X)) ≅ (SheafOfModules.unit C.scheme.ringCatSheaf :
          C.scheme.Modules) :=
    ((Scheme.Modules.pullbackComp θ ψ').app _) ≪≫ (Scheme.Modules.pullbackCongr hθ).app _ ≪≫
      ((Scheme.Modules.pullbackComp C.ι (sect (j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec
          (.of k)) c)).app _).symm ≪≫
      (Scheme.Modules.pullback C.ι).mapIso et ≪≫ pullbackObjUnitIsoUnit C.ι
  haveI hN : SheafOfModules.IsInvertible C.scheme.presheaf C.scheme.ringCatSheaf.2 N :=
      inferInstance
  haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
    (C.ι ≫ j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k))
  haveI : IsClosedImmersion (C.ι ≫ j) := inferInstance
  haveI : IsProper ((C.ι ≫ j) ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k)) :=
    inferInstance
  obtain ⟨T2⟩ := nonempty_twist2_iso
    (fun t => (Scheme.Modules.pullback θ).obj ((Scheme.Modules.pullback ψ').obj
      (![(Scheme.Modules.pullback (projectiveSpaceOver 1 X ↘ X ≫ j)).obj
            (projectiveSpaceTwistingSheaf M (Spec (.of k))),
          projectiveSpaceTwistingSheaf 1 X] t))) N eA eB (fun _ => m)
  obtain ⟨T1⟩ := nonempty_twist1_iso N N (Iso.refl N) m
  have hco1 := isCoherent_twistedSheafUnitPullback k
    (projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k)) (C.ι ≫ j)
    (fun _ : Fin 1 => projectiveSpaceTwistingSheaf M (Spec (.of k))) (fun _ => m)
  have key := eulerCharacteristic_curve_twist k M j C m
  unfold subschemeHilbertFunction at key
  rw [eulerCharacteristic_congr_hom k _ _ h2]
  refine Eq.trans ?_ key
  exact eulerCharacteristic_eq_of_iso (k := k)
    (f := (C.ι ≫ j) ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k)) (T2 ≪≫ T1.symm)

end ChiSigma

end DisjointCopies

/-- Placing `nᵢ` disjoint copies of each component `Cᵢ` of an effective 1-cycle over distinct
`k`-points of `ℙ¹` gives a closed subscheme of `ℙ¹_X` of dimension at most one whose fundamental
cycle pushes forward to the cycle, with Euler characteristic `(Z₀ · L) m + ∑ nᵢ (1 - p_a(Cᵢ))`. -/
private theorem exists_disjoint_copies
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] (M : ℕ) {X : Scheme.{u}}
    (j : X ⟶ projectiveSpaceOver M (Spec (.of k))) [IsClosedImmersion j]
    (Z₀ : OneCycle ℤ (j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k)))
    (hZ₀ : ∀ C, 0 ≤ Z₀ C) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ projectiveSpaceOver 1 X) (_ : IsClosedImmersion i)
      (Γ : OneCycle ℤ (i ≫ projectiveSpaceOver 1 X ↘ X ≫ j ≫
        projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k))),
      topologicalKrullDim Z ≤ 1 ∧
      (∀ D, Γ D = ((Module.length (Z.presheaf.stalk D.point)
        (Z.presheaf.stalk D.point)).toNat : ℤ)) ∧
      OneCycle.pushforward ℤ _ (j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k))
        (i ≫ projectiveSpaceOver 1 X ↘ X) Γ = Z₀ ∧
      ∀ m : ℤ,
            haveI : ∀ t, SheafOfModules.IsInvertible (projectiveSpaceOver 1 X).presheaf
                (projectiveSpaceOver 1 X).ringCatSheaf.2
                (![(Scheme.Modules.pullback (projectiveSpaceOver 1 X ↘ X ≫ j)).obj
                    (projectiveSpaceTwistingSheaf M (Spec (.of k))),
                  projectiveSpaceTwistingSheaf 1 X] t) :=
              fun t => by fin_cases t <;> dsimp <;> infer_instance
            haveI := isCoherent_twistedSheafUnitPullback k
              (projectiveSpaceOver 1 X ↘ X ≫ j ≫
                projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k)) i
              ![(Scheme.Modules.pullback (projectiveSpaceOver 1 X ↘ X ≫ j)).obj
                  (projectiveSpaceTwistingSheaf M (Spec (.of k))),
                projectiveSpaceTwistingSheaf 1 X] fun _ => m
            eulerCharacteristic k
                (i ≫ projectiveSpaceOver 1 X ↘ X ≫ j ≫
                  projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k))
                (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
                  (fun t => (Scheme.Modules.pullback i).obj
                    (![(Scheme.Modules.pullback (projectiveSpaceOver 1 X ↘ X ≫ j)).obj
                        (projectiveSpaceTwistingSheaf M (Spec (.of k))),
                      projectiveSpaceTwistingSheaf 1 X] t))
                  fun _ => m) =
              OneCycle.degree ℤ (j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k))
                ((Scheme.Modules.pullback j).obj (projectiveSpaceTwistingSheaf M (Spec (.of k))))
                    Z₀ * m +
                Z₀.sum fun C n =>
                  haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
                    (C.ι ≫ j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k))
                  n * (1 - arithmeticGenus (C.ι ≫ j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec
                      (.of k)))  := by
  classical
  let P := Σ C : Z₀.support, Fin (Z₀ C).toNat
  let W : P → ProperCurve (j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k)) := fun p =>
      p.1.1
  haveI : Infinite k := inferInstance
  obtain ⟨a⟩ : Nonempty (P ↪ k) :=
    (Cardinal.le_def P k).mp (Cardinal.mk_lt_aleph0.le.trans (Cardinal.aleph0_le_mk k))
  let ψp : ∀ p : P, (W p).scheme ⟶ projectiveSpaceOver 1 X := fun p => (W p).ι ≫ sect (j ≫
      projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k)) (a p)
  have hdisj : Pairwise fun p q => Disjoint (Set.range (ψp p)) (Set.range (ψp q)) := by
    intro p q hpq
    refine (sect_disjoint (j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k)) (fun h => hpq
        (a.injective h))).mono ?_ ?_
    · rintro _ ⟨x, rfl⟩; exact ⟨(W p).ι x, rfl⟩
    · rintro _ ⟨x, rfl⟩; exact ⟨(W q).ι x, rfl⟩
  haveI : ∀ p, IsClosedImmersion (ψp p) := fun p => inferInstance
  let ψ : pieces W ⟶ projectiveSpaceOver 1 X := Limits.Sigma.desc ψp
  have hψcl : IsClosedImmersion ψ := isClosedImmersion_sigmaDesc _ ψp hdisj
  have hψ : ∀ p, pieceι W p ≫ ψ ≫ projectiveSpaceOver 1 X ↘ X = (W p).ι := fun p => by
    rw [← Category.assoc]
    show (Limits.Sigma.ι (fun p => (W p).scheme) p ≫ Limits.Sigma.desc ψp) ≫ _ = _
    rw [Limits.Sigma.ι_desc]
    simp only [ψp, Category.assoc, sect_comp, Category.comp_id]
  haveI : IsProper (projectiveSpaceOver 1 X ↘ X) := isProper_projectiveSpaceOver 1 X
  haveI : IsProper (j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k)) := inferInstance
  haveI : IsSeparated (ψ ≫ projectiveSpaceOver 1 X ↘ X ≫ (j ≫ projectiveSpaceOver M (Spec (.of k))
      ↘ Spec (.of k))) := inferInstance
  haveI : LocallyOfFiniteType (ψ ≫ projectiveSpaceOver 1 X ↘ X ≫ (j ≫ projectiveSpaceOver M (Spec
      (.of k)) ↘ Spec (.of k))) := inferInstance
  obtain ⟨Γ, hΓ1, hΓ2⟩ := exists_cycle_sigma (sX := (j ≫ projectiveSpaceOver M (Spec (.of k)) ↘
      Spec (.of k))) (projectiveSpaceOver 1 X ↘ X) ψ hψ
  have hsum : ∑ p : P, Finsupp.single (W p) (1 : ℤ) = Z₀ := by
    rw [Fintype.sum_sigma]
    have h1 : ∀ C : Z₀.support, ∑ i : Fin (Z₀ C).toNat, Finsupp.single (W ⟨C, i⟩) (1 : ℤ) =
        Finsupp.single C.1 (Z₀ C.1) := fun C => by
      simp only [W, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      rw [Finsupp.smul_single, nsmul_eq_mul, mul_one]
      congr 1
      exact Int.toNat_of_nonneg (hZ₀ C.1)
    rw [Finset.sum_congr rfl fun C _ => h1 C,
      Finset.sum_coe_sort Z₀.support (fun C => Finsupp.single C (Z₀ C))]
    exact Finsupp.sum_single Z₀
  refine ⟨pieces W, ψ, hψcl, Γ, ?_, hΓ1, hΓ2.trans hsum, ?_⟩
  · exact topologicalKrullDim_sigma_le (fun p => (W p).scheme) 1 (fun p => (W p).dim_le)
  · intro m
    have hfam : ∀ t : Fin 2, SheafOfModules.IsInvertible (projectiveSpaceOver 1 X).presheaf
        (projectiveSpaceOver 1 X).ringCatSheaf.2
        (![(Scheme.Modules.pullback (projectiveSpaceOver 1 X ↘ X ≫ j)).obj
            (projectiveSpaceTwistingSheaf M (Spec (.of k))),
          projectiveSpaceTwistingSheaf 1 X] t) :=
      fun t => by fin_cases t <;> dsimp <;> infer_instance
    haveI := hfam
    haveI hco := isCoherent_twistedSheafUnitPullback k
      (projectiveSpaceOver 1 X ↘ X ≫ j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k)) ψ
      ![(Scheme.Modules.pullback (projectiveSpaceOver 1 X ↘ X ≫ j)).obj
          (projectiveSpaceTwistingSheaf M (Spec (.of k))),
        projectiveSpaceTwistingSheaf 1 X] fun _ => m
    have hsumF : ∀ F : ProperCurve (j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k)) → ℤ,
        ∑ p : P, F (W p) = Z₀.sum fun C n => n * F C := fun F => by
      rw [Fintype.sum_sigma]
      have h1 : ∀ C : Z₀.support, ∑ i : Fin (Z₀ C).toNat, F (W ⟨C, i⟩) = Z₀ C.1 * F C.1 :=
        fun C => by
          simp only [W, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          congr 1
          exact_mod_cast Int.toNat_of_nonneg (hZ₀ C.1)
      rw [Finset.sum_congr rfl fun C _ => h1 C,
        Finset.sum_coe_sort Z₀.support (fun C => Z₀ C * F C)]
      rfl
    haveI hLinv : ∀ t, SheafOfModules.IsInvertible (pieces W).presheaf (pieces W).ringCatSheaf.2
        ((Scheme.Modules.pullback ψ).obj
          (![(Scheme.Modules.pullback (projectiveSpaceOver 1 X ↘ X ≫ j)).obj
              (projectiveSpaceTwistingSheaf M (Spec (.of k))),
            projectiveSpaceTwistingSheaf 1 X] t)) :=
      fun t => SheafOfModules.isInvertible_pullback ψ _
    haveI hLp : ∀ (p : P) (t : Fin 2), SheafOfModules.IsInvertible (W p).scheme.presheaf
        (W p).scheme.ringCatSheaf.2
        ((Scheme.Modules.pullback (pieceι W p)).obj ((Scheme.Modules.pullback ψ).obj
          (![(Scheme.Modules.pullback (projectiveSpaceOver 1 X ↘ X ≫ j)).obj
              (projectiveSpaceTwistingSheaf M (Spec (.of k))),
            projectiveSpaceTwistingSheaf 1 X] t))) :=
      fun p t => SheafOfModules.isInvertible_pullback (pieceι W p) _
    haveI hpr : ∀ p : P, IsProper (pieceι W p ≫ ψ ≫ projectiveSpaceOver 1 X ↘ X ≫ j ≫
        projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k)) := fun p => by
      haveI : IsClosedImmersion (pieceι W p) := Stacks.Chow.isClosedImmersion_sigmaι _ p
      infer_instance
    haveI hM : ∀ p : P, (twistedSheaf (SheafOfModules.unit (W p).scheme.ringCatSheaf)
        (fun t => (Scheme.Modules.pullback (pieceι W p)).obj ((Scheme.Modules.pullback ψ).obj
          (![(Scheme.Modules.pullback (projectiveSpaceOver 1 X ↘ X ≫ j)).obj
              (projectiveSpaceTwistingSheaf M (Spec (.of k))),
            projectiveSpaceTwistingSheaf 1 X] t))) (fun _ => m)).IsCoherent := fun p => by
      have hu := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
        (pieceι W p ≫ ψ ≫ projectiveSpaceOver 1 X ↘ X ≫ j ≫
          projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k))
      exact @twistedSheaf_isCoherent (W p).scheme 2 _ _ _ hu _
    refine Eq.trans (eulerCharacteristic_sigma_twist (fun p => (W p).scheme)
      (ψ ≫ projectiveSpaceOver 1 X ↘ X ≫ j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k))
      (fun t => (Scheme.Modules.pullback ψ).obj
        (![(Scheme.Modules.pullback (projectiveSpaceOver 1 X ↘ X ≫ j)).obj
            (projectiveSpaceTwistingSheaf M (Spec (.of k))),
          projectiveSpaceTwistingSheaf 1 X] t)) (fun _ => m)) ?_
    have hterm := fun p : P => eulerCharacteristic_piece_family k M j (W p) (pieceι W p) ψ (a p)
        (Limits.Sigma.ι_desc ψp p) m
    rw [Finset.sum_congr rfl fun p _ => hterm p]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    congr 1
    · rw [OneCycle.degree_apply]
      simp only [Int.cast_id]
      congr 1
      exact hsumF (fun C => C.degree k ((Scheme.Modules.pullback j).obj
        (projectiveSpaceTwistingSheaf M (Spec (.of k)))))
    · exact hsumF (fun C =>
        haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
          (C.ι ≫ j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k))
        1 - arithmeticGenus (C.ι ≫ j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k)))

/-- The numerical facts about a proper curve `C ⊆ X ⊆ ℙᴹ_k`: its degree `e` is positive, its
arithmetic genus is nonnegative and `2 p_a ≤ (e - 1)(e - 2)`. -/
private theorem properCurve_degree_genus
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] (M : ℕ) {X : Scheme.{u}}
    (j : X ⟶ projectiveSpaceOver M (Spec (.of k))) [IsClosedImmersion j]
    (C : ProperCurve (j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k))) :
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
      (C.ι ≫ j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k))
    1 ≤ C.degree k ((Scheme.Modules.pullback j).obj (projectiveSpaceTwistingSheaf M (Spec (.of
        k)))) ∧
      0 ≤ arithmeticGenus (C.ι ≫ j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k)) ∧
      2 * arithmeticGenus (C.ι ≫ j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k)) ≤
        (C.degree k ((Scheme.Modules.pullback j).obj
            (projectiveSpaceTwistingSheaf M (Spec (.of k)))) - 1) *
          (C.degree k ((Scheme.Modules.pullback j).obj
            (projectiveSpaceTwistingSheaf M (Spec (.of k)))) - 2) := by
  have hC1 : topologicalKrullDim C.scheme = 1 := C.dim_eq
  haveI : IsClosedImmersion (C.ι ≫ j) := inferInstance
  haveI : IsProper ((C.ι ≫ j) ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k)) :=
    inferInstance
  have hdegEq := hilbertDegree_properCurve_eq_degree k M j C
  have hpos := hilbertDegree_pos k (projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k))
    (C.ι ≫ j) 1 hC1 (projectiveSpaceTwistingSheaf M (Spec (.of k)))
    (Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple _ _
      (Stacks.ProjectiveSpace.isAmple_projectiveSpaceTwistingSheaf M (Spec (.of k))))
  have h2 := two_mul_arithmeticGenus_le k M (C.ι ≫ j) hC1
  have h3 := (arithmeticGenus_eq_finrank_cohomologyOverField_one
    ((C.ι ≫ j) ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k)) hC1.le).2.2
  rw [hdegEq] at hpos h2
  exact ⟨hpos, h3, h2⟩

/-- The constant term `∑ nᵢ (1 - p_a(Cᵢ))` of an effective 1-cycle of degree `d` lies in a
finite set depending only on `d`: `p_a ≥ 0` and `2 p_a ≤ (e - 1)(e - 2)` with `1 ≤ e ≤ d` for
each component. -/
private theorem constant_term_mem_Icc
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] (M : ℕ) {X : Scheme.{u}}
    (j : X ⟶ projectiveSpaceOver M (Spec (.of k))) [IsClosedImmersion j] (d : ℕ)
    (Z₀ : OneCycle ℤ (j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k)))
    (hZ₀ : ∀ C, 0 ≤ Z₀ C)
    (hdeg : OneCycle.degree ℤ (j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k))
      ((Scheme.Modules.pullback j).obj (projectiveSpaceTwistingSheaf M (Spec (.of k)))) Z₀ = d) :
    (Z₀.sum fun C n =>
      haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
        (C.ι ≫ j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k))
      n * (1 - arithmeticGenus (C.ι ≫ j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k)))) ∈
      Finset.Icc (-(d : ℤ) ^ 2) (d : ℤ) := by
  classical
  set L := (Scheme.Modules.pullback j).obj (projectiveSpaceTwistingSheaf M (Spec (.of k)))
  have hsum : ∑ C ∈ Z₀.support, Z₀ C * C.degree k L = d := by
    have h := OneCycle.degree_apply ℤ (j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k))
      L Z₀
    rwa [hdeg, eq_comm] at h
  have hfacts := properCurve_degree_genus k M j
  have hn : ∀ C ∈ Z₀.support, 1 ≤ Z₀ C := fun C hC => by
    have := Finsupp.mem_support_iff.mp hC
    have := hZ₀ C
    omega
  have he : ∀ C ∈ Z₀.support, 1 ≤ C.degree k L := fun C _ => (hfacts C).1
  have hterm_nn : ∀ C ∈ Z₀.support, 0 ≤ Z₀ C * C.degree k L := fun C hC =>
    mul_nonneg (hZ₀ C) (by linarith [he C hC])
  have hle_d : ∀ C ∈ Z₀.support, C.degree k L ≤ d := by
    intro C hC
    have h1 : Z₀ C * C.degree k L ≤ d := by
      rw [← hsum]
      exact Finset.single_le_sum (f := fun C => Z₀ C * C.degree k L) hterm_nn hC
    nlinarith [hn C hC, he C hC]
  rw [Finset.mem_Icc]
  unfold Finsupp.sum
  let gC : ProperCurve (j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k)) → ℤ := fun C =>
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
      (C.ι ≫ j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k))
    arithmeticGenus (C.ι ≫ j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k))
  change (-(d : ℤ) ^ 2 ≤ ∑ C ∈ Z₀.support, Z₀ C * (1 - gC C)) ∧
    ∑ C ∈ Z₀.support, Z₀ C * (1 - gC C) ≤ d
  have hfacts' : ∀ C ∈ Z₀.support, 1 ≤ C.degree k L ∧ 0 ≤ gC C ∧
      2 * gC C ≤ (C.degree k L - 1) * (C.degree k L - 2) := fun C _ => hfacts C
  constructor
  · calc -(d : ℤ) ^ 2 = ∑ C ∈ Z₀.support, -(Z₀ C * C.degree k L * d) := by
          rw [Finset.sum_neg_distrib, ← Finset.sum_mul, hsum]; ring
      _ ≤ _ := by
          refine Finset.sum_le_sum fun C hC => ?_
          obtain ⟨he1, hg0, hg2⟩ := hfacts' C hC
          have hed := hle_d C hC
          have hn0 := hZ₀ C
          have hg3 : gC C ≤ C.degree k L * d := by nlinarith
          nlinarith
  · calc ∑ C ∈ Z₀.support, Z₀ C * (1 - gC C) ≤ ∑ C ∈ Z₀.support, Z₀ C * C.degree k L := by
          refine Finset.sum_le_sum fun C hC => ?_
          obtain ⟨he1, hg0, hg2⟩ := hfacts' C hC
          have hn0 := hZ₀ C
          nlinarith
      _ = d := hsum

/-- Effective 1-cycles of degree `d` on a projective `X` are represented by closed subschemes of
`ℙ¹_X` with Hilbert polynomial `d m + c` for `c` in a finite set. -/
private theorem exists_finset_hilbertPolynomial_constant
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] :
    ∀ (M : ℕ) {X : Scheme.{u}} (j : X ⟶ projectiveSpaceOver M (Spec (.of k)))
        [IsClosedImmersion j] (d : ℕ),
      ∃ S : Finset ℤ, ∀ Z₀ : OneCycle ℤ (j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k)),
        (∀ C, 0 ≤ Z₀ C) →
        OneCycle.degree ℤ (j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k))
            ((Scheme.Modules.pullback j).obj (projectiveSpaceTwistingSheaf M (Spec (.of k)))) Z₀ =
          d →
        ∃ (Z : Scheme.{u}) (i : Z ⟶ projectiveSpaceOver 1 X) (_ : IsClosedImmersion i)
          (Γ : OneCycle ℤ (i ≫ projectiveSpaceOver 1 X ↘ X ≫ j ≫
            projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k))),
          topologicalKrullDim Z ≤ 1 ∧
          (∀ D, Γ D = ((Module.length (Z.presheaf.stalk D.point)
            (Z.presheaf.stalk D.point)).toNat : ℤ)) ∧
          OneCycle.pushforward ℤ _ (j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k))
            (i ≫ projectiveSpaceOver 1 X ↘ X) Γ = Z₀ ∧
          ∃ c ∈ S, ∀ m : ℤ,
            haveI : ∀ t, SheafOfModules.IsInvertible (projectiveSpaceOver 1 X).presheaf
                (projectiveSpaceOver 1 X).ringCatSheaf.2
                (![(Scheme.Modules.pullback (projectiveSpaceOver 1 X ↘ X ≫ j)).obj
                    (projectiveSpaceTwistingSheaf M (Spec (.of k))),
                  projectiveSpaceTwistingSheaf 1 X] t) :=
              fun t => by fin_cases t <;> dsimp <;> infer_instance
            haveI := isCoherent_twistedSheafUnitPullback k
              (projectiveSpaceOver 1 X ↘ X ≫ j ≫
                projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k)) i
              ![(Scheme.Modules.pullback (projectiveSpaceOver 1 X ↘ X ≫ j)).obj
                  (projectiveSpaceTwistingSheaf M (Spec (.of k))),
                projectiveSpaceTwistingSheaf 1 X] fun _ => m
            eulerCharacteristic k
                (i ≫ projectiveSpaceOver 1 X ↘ X ≫ j ≫
                  projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k))
                (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
                  (fun t => (Scheme.Modules.pullback i).obj
                    (![(Scheme.Modules.pullback (projectiveSpaceOver 1 X ↘ X ≫ j)).obj
                        (projectiveSpaceTwistingSheaf M (Spec (.of k))),
                      projectiveSpaceTwistingSheaf 1 X] t))
                  fun _ => m) =
              d * m + c := by
  intro M X j _ d
  refine ⟨Finset.Icc (-(d : ℤ) ^ 2) (d : ℤ), fun Z₀ hZ₀ hdeg => ?_⟩
  obtain ⟨Z, i, hi, Γ, h1, h2, h3, h4⟩ := exists_disjoint_copies k M j Z₀ hZ₀
  refine ⟨Z, i, hi, Γ, h1, h2, h3, _, constant_term_mem_Icc k M j d Z₀ hZ₀ hdeg, fun m => ?_⟩
  rw [h4 m, hdeg]

end MMP.Mori.GenusBound

namespace MMP.Mori

/-- **A uniform arithmetic-genus bound for integral curves of bounded degree.** Let `k` be an
algebraically closed field of characteristic zero.

1. If `C ⊆ ℙᴺ_k` is an integral closed subscheme of dimension one and degree `e`, then
   `0 ≤ p_a(C)` and `2 p_a(C) ≤ (e - 1)(e - 2)`.
2. If `j : X ⟶ ℙᴹ_k` is a closed immersion, `L = j^* 𝒪(1)` and `d : ℕ`, there is a finite set
   `S ⊆ ℤ` such that every effective 1-cycle `Z₀` on `X` with `(Z₀ · L) = d` is the push-forward
   along `Z ⟶ ℙ¹_X ⟶ X` of the fundamental 1-cycle of a closed subscheme `Z ⊆ ℙ¹_X = X × ℙ¹`
   of dimension at most one, with `χ(Z, (L ⊠ 𝒪(1))^{⊗ m}|_Z) = d m + c` for all `m ∈ ℤ` and
   some `c ∈ S`. -/
@[mmp "lem_mmp_chow_integral_curve_genus_bound"]
public theorem arithmeticGenus_bound_projectiveSpace
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] :
    (∀ (N : ℕ) {C : Scheme.{u}} (i : C ⟶ projectiveSpaceOver N (Spec (.of k)))
        [IsClosedImmersion i] [IsIntegral C] (hC : topologicalKrullDim C = 1),
      haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
        (i ≫ projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of k))
      0 ≤ arithmeticGenus (i ≫ projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of k)) ∧
        2 * arithmeticGenus (i ≫ projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of k)) ≤
          (hilbertDegree k (projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of k)) i 1 hC
              (projectiveSpaceTwistingSheaf N (Spec (.of k))) - 1) *
            (hilbertDegree k (projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of k)) i 1 hC
              (projectiveSpaceTwistingSheaf N (Spec (.of k))) - 2)) ∧
    (∀ (M : ℕ) {X : Scheme.{u}} (j : X ⟶ projectiveSpaceOver M (Spec (.of k)))
        [IsClosedImmersion j] (d : ℕ),
      ∃ S : Finset ℤ, ∀ Z₀ : OneCycle ℤ (j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k)),
        (∀ C, 0 ≤ Z₀ C) →
        OneCycle.degree ℤ (j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k))
            ((Scheme.Modules.pullback j).obj (projectiveSpaceTwistingSheaf M (Spec (.of k)))) Z₀ =
          d →
        ∃ (Z : Scheme.{u}) (i : Z ⟶ projectiveSpaceOver 1 X) (_ : IsClosedImmersion i)
          (Γ : OneCycle ℤ (i ≫ projectiveSpaceOver 1 X ↘ X ≫ j ≫
            projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k))),
          topologicalKrullDim Z ≤ 1 ∧
          (∀ D, Γ D = ((Module.length (Z.presheaf.stalk D.point)
            (Z.presheaf.stalk D.point)).toNat : ℤ)) ∧
          OneCycle.pushforward ℤ _ (j ≫ projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k))
            (i ≫ projectiveSpaceOver 1 X ↘ X) Γ = Z₀ ∧
          ∃ c ∈ S, ∀ m : ℤ,
            haveI : ∀ t, SheafOfModules.IsInvertible (projectiveSpaceOver 1 X).presheaf
                (projectiveSpaceOver 1 X).ringCatSheaf.2
                (![(Scheme.Modules.pullback (projectiveSpaceOver 1 X ↘ X ≫ j)).obj
                    (projectiveSpaceTwistingSheaf M (Spec (.of k))),
                  projectiveSpaceTwistingSheaf 1 X] t) :=
              fun t => by fin_cases t <;> dsimp <;> infer_instance
            haveI := isCoherent_twistedSheafUnitPullback k
              (projectiveSpaceOver 1 X ↘ X ≫ j ≫
                projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k)) i
              ![(Scheme.Modules.pullback (projectiveSpaceOver 1 X ↘ X ≫ j)).obj
                  (projectiveSpaceTwistingSheaf M (Spec (.of k))),
                projectiveSpaceTwistingSheaf 1 X] fun _ => m
            eulerCharacteristic k
                (i ≫ projectiveSpaceOver 1 X ↘ X ≫ j ≫
                  projectiveSpaceOver M (Spec (.of k)) ↘ Spec (.of k))
                (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
                  (fun t => (Scheme.Modules.pullback i).obj
                    (![(Scheme.Modules.pullback (projectiveSpaceOver 1 X ↘ X ≫ j)).obj
                        (projectiveSpaceTwistingSheaf M (Spec (.of k))),
                      projectiveSpaceTwistingSheaf 1 X] t))
                  fun _ => m) =
              d * m + c) := by
  refine ⟨fun N C i _ _ hC => ⟨?_, GenusBound.two_mul_arithmeticGenus_le k N i hC⟩,
    GenusBound.exists_finset_hilbertPolynomial_constant k⟩
  have : IsProper (i ≫ projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of k)) := inferInstance
  exact (arithmeticGenus_eq_finrank_cohomologyOverField_one _ hC.le).2.2

end MMP.Mori
