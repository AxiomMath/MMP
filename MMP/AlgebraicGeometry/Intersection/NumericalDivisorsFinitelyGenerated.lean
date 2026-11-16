module

public import MMP.AlgebraicGeometry.Analytic.ProjectiveSingularSheafComparison
public import MMP.AlgebraicGeometry.Analytic.FiniteCochainsBetti
public import MMP.AlgebraicGeometry.Analytic.LogObstructionCurveDegree

/-!
# Finite generation of numerical Cartier classes on a projective complex variety

Let `X` be a projective variety over `ℂ`. Two Cartier divisors `E, E'` on `X` are numerically
equivalent when `deg_C 𝒪_X(E) = deg_C 𝒪_X(E')` for every integral proper curve `C ⊆ X`. The
group `Div(X)` of Cartier divisors modulo numerical equivalence is finitely generated: there are
finitely many Cartier divisors `D₁, …, D_r` such that every Cartier divisor is numerically
equivalent to an integral combination `∑ nⱼ Dⱼ`. Consequently the real vector space
`N¹(X)_ℝ` of `ℝ`-Cartier divisors modulo numerical equivalence is finite-dimensional.

## Main results

* `MMP.Fourfold.exists_finset_cartierDivisor_degree_eq_sum_and_finiteDimensional`: finite
  generation of Cartier divisors modulo numerical equivalence, and finite-dimensionality of
  `MMP.Fourfold.NumericalDivisorClasses`.

## Implementation notes

Finite generation of the quotient group is stated through generators: a finite set `s` of
Cartier divisors such that every Cartier divisor `E` has, for some integers `n D`, the same
degree `MMP.Mori.ProperCurve.degree` as `∑ D ∈ s, n D • D` on every proper curve. This is
equivalent to the finite generation of `Div(X)/≡` and does not presuppose that the degree is
additive in the divisor. The degree of a Cartier divisor `E` along a curve is the degree of its
invertible sheaf `MMP.CartierDivisor.sheaf E`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MMP.Mori

namespace MMP.Fourfold

attribute [local instance] CategoryTheory.hasExt_of_enoughInjectives
  Stacks.Cohomology.Generators.picardGroupAddCommGroup
attribute [local implicit_reducible] TopCat.Sheaf

/-- The tensor product of the invertible sheaves of two Cartier divisors is invertible. -/
private theorem isInvertible_sheafTensor_sheaf {X : Scheme.{0}} (B B' : X.CartierDivisor) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
        X.toRingedSpace.IsSheaf⟩).obj (MMP.CartierDivisor.sheaf B)).obj
          (MMP.CartierDivisor.sheaf B')) :=
  Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible X.presheaf X.ringCatSheaf.2 _ _

/-- The degree of the sheaf of a sum of Cartier divisors along a proper curve. -/
private theorem degree_sheaf_add {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    (B B' : X.CartierDivisor) (C : ProperCurve sX) :
    C.degree ℂ (MMP.CartierDivisor.sheaf (B + B')) =
      C.degree ℂ (MMP.CartierDivisor.sheaf B) +
        C.degree ℂ (MMP.CartierDivisor.sheaf B') := by
  unfold ProperCurve.degree
  rw [← degreeOn_tensorSheaf ℂ sX C.ι C.dim_le (hLM := isInvertible_sheafTensor_sheaf B B')]
  exact (degreeOn_eq_of_iso ℂ sX C.ι C.dim_le
    (MMP.CartierDivisorSheaf.sheafMulIso B B')).symm

/-- The degree along a proper curve, as an additive map on Cartier divisors. -/
private noncomputable def degreeHom {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    (C : ProperCurve sX) : X.CartierDivisor →+ ℤ :=
  AddMonoidHom.mk' (fun B => C.degree ℂ (MMP.CartierDivisor.sheaf B))
    fun B B' => degree_sheaf_add B B' C

private theorem degreeHom_apply {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    (C : ProperCurve sX) (B : X.CartierDivisor) :
    degreeHom C B = C.degree ℂ (MMP.CartierDivisor.sheaf B) := rfl

/-- If `φ : G →+ M` lands in a finitely generated abelian group, then finitely many elements of
`G` generate `G` modulo the kernel of `φ`. -/
private theorem exists_finset_map_sub_sum_eq_zero {G M : Type*} [AddCommGroup G]
    [AddCommGroup M] [Module.Finite ℤ M] (φ : G →+ M) :
    ∃ s : Finset G, ∀ g : G, ∃ n : G → ℤ, φ (g - ∑ x ∈ s, n x • x) = 0 := by
  classical
  have : IsNoetherian ℤ M := isNoetherian_of_isNoetherianRing_of_finite ℤ M
  obtain ⟨t, hts, ht⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (R := ℤ) (Set.range φ)).1
    (IsNoetherian.noetherian _)
  obtain ⟨s, -, rfl⟩ := Finset.subset_set_image_iff.1 (Set.image_univ (f := φ) ▸ hts)
  refine ⟨s, fun g => ?_⟩
  obtain ⟨x, hx, hxg⟩ : φ g ∈ (Submodule.span ℤ (s : Set G)).map φ.toIntLinearMap := by
    rw [← Submodule.span_image, ← Finset.coe_image]
    exact ht ▸ Submodule.subset_span ⟨g, rfl⟩
  obtain ⟨n, -, rfl⟩ := Submodule.mem_span_finset.1 hx
  exact ⟨n, by rw [map_sub, sub_eq_zero]; exact hxg.symm⟩

/-- The logarithmic obstruction of a pulled-back tensor product is the sum of the obstructions
of the pulled-back factors. -/
private theorem picardObstruction_classOf_pullback_tensor {A Y : RingedSpace.{0}}
    [∀ x, IsLocalRing (A.presheaf.stalk x)] (f : A ⟶ Y) {F M : TopCat.Sheaf AddCommGrpCat.{0} A}
    {i : F ⟶ M} {e : M ⟶ Stacks.Cohomology.Generators.unitsSheaf A} {w : i ≫ e = 0}
    (hS : (ShortComplex.mk i e w).ShortExact)
    (L N : SheafOfModules.{0} (Stacks.RingedSpace.structureRingSheaf Y))
    (hL : Stacks.SheafOfModules.IsInvertible _ _ ((Stacks.RingedSpace.pullbackFunctor f).obj L))
    (hN : Stacks.SheafOfModules.IsInvertible _ _ ((Stacks.RingedSpace.pullbackFunctor f).obj N))
    (hLN : Stacks.SheafOfModules.IsInvertible _ _ ((Stacks.RingedSpace.pullbackFunctor f).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.presheaf, Y.IsSheaf⟩).obj L).obj N))) :
    MMP.Analytic.picardObstruction A hS (Stacks.SheafOfModules.Picard.classOf _ _
        ((Stacks.RingedSpace.pullbackFunctor f).obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.presheaf, Y.IsSheaf⟩).obj L).obj N))
        hLN) =
      MMP.Analytic.picardObstruction A hS (Stacks.SheafOfModules.Picard.classOf _ _
          ((Stacks.RingedSpace.pullbackFunctor f).obj L) hL) +
        MMP.Analytic.picardObstruction A hS (Stacks.SheafOfModules.Picard.classOf _ _
          ((Stacks.RingedSpace.pullbackFunctor f).obj N) hN) := by
  have hT := @Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible _ _ _ _ _ _ _ _ _ hL hN
  rw [← map_add, Stacks.SheafOfModules.Picard.classOf_tensor _ _ _ _ hL hN hT]
  congr 1
  exact (Stacks.SheafOfModules.Picard.classOf_eq_classOf_iff _ _ _ _ _ _).2
    ⟨(Stacks.RingedSpace.comparisonBifunctorIso f).app (L, N)⟩

/-- `H²(X^an, ℤ)` of a projective complex scheme is a finitely generated abelian group. -/
private theorem finite_sheafH_two {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (hX : IsProjectiveMorphism sX) :
    Module.Finite ℤ (Sheaf.H.{0} ((constantSheaf (Opens.grothendieckTopology
      (MMP.Analytic.Analytification.space sX)) AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)) 2) := by
  obtain ⟨φ, -⟩ := MMP.Analytic.exists_addEquiv_sheafH_constantSheaf_singularCohomology ℤ 2
  have h :=
    (MMP.Analytic.exists_homotopyEquiv_singularChainComplex_of_isProjectiveMorphism sX hX).2.1 2
  rw [MMP.Analytic.singularCohomology, MMP.cohomologyWithSupports.univ] at h
  exact Module.Finite.equiv (φ sX hX).symm.toIntLinearEquiv

/-- The analytification of the invertible sheaf of a Cartier divisor is invertible. -/
private theorem isInvertible_analytifyModule_sheaf {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (E : X.CartierDivisor) : Stacks.SheafOfModules.IsInvertible _ _
      ((MMP.Analytic.analytifyModule sX).obj (MMP.CartierDivisor.sheaf E)) :=
  @Stacks.InvertiblePullback.isInvertible_pullback _ _ (MMP.Analytic.analytificationHom sX)
    (MMP.CartierDivisor.sheaf E)
    (inferInstance : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 _)

/-- The logarithmic obstruction `E ↦ c_exp(𝒪_X(E)^an)`, as an additive map on Cartier
divisors. -/
private noncomputable def obstructionHom {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType sX]
    {F M : TopCat.Sheaf AddCommGrpCat.{0} (MMP.Analytic.analytification sX)} {i : F ⟶ M}
    {e : M ⟶ Stacks.Cohomology.Generators.unitsSheaf _} {w : i ≫ e = 0}
    (hS : (ShortComplex.mk i e w).ShortExact) :=
  AddMonoidHom.mk' (fun E : X.CartierDivisor =>
      MMP.Analytic.picardObstruction (MMP.Analytic.analytification sX) hS
      (Stacks.SheafOfModules.Picard.classOf _ _ _ (isInvertible_analytifyModule_sheaf sX E)))
    fun E F => by
      refine Eq.trans ?_ (picardObstruction_classOf_pullback_tensor
        (MMP.Analytic.analytificationHom sX) hS _ _ (isInvertible_analytifyModule_sheaf sX E)
        (isInvertible_analytifyModule_sheaf sX F)
        (@Stacks.InvertiblePullback.isInvertible_pullback _ _
          (MMP.Analytic.analytificationHom sX) _ (isInvertible_sheafTensor_sheaf E F)))
      exact congrArg (MMP.Analytic.picardObstruction _ hS)
        ((Stacks.SheafOfModules.Picard.classOf_eq_classOf_iff _ _ _ _ _ _).2
          ⟨(MMP.Analytic.analytifyModule sX).mapIso
            (MMP.CartierDivisorSheaf.sheafMulIso E F).symm⟩)

/-- There is a finite set `s` of Cartier divisors such that every Cartier divisor has the same
degree on every proper curve as some integral combination `∑ D ∈ s, n D • D`. -/
private theorem exists_finset_degree_eq_sum {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (hX : IsProjective sX) :
    ∃ s : Finset X.CartierDivisor, ∀ E : X.CartierDivisor, ∃ n : X.CartierDivisor → ℤ,
      ∀ C : ProperCurve sX, degreeHom C E = degreeHom C (∑ D ∈ s, n D • D) := by
  haveI := hX.isProper
  have hS := (MMP.Analytic.exists_shortExact_exponentialSequence sX).choose_spec.choose_spec
    |>.choose_spec.1
  have : Module.Finite ℤ (Sheaf.H.{0} ((constantSheaf (Opens.grothendieckTopology
      (MMP.Analytic.Analytification.space sX)) AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ))
        (1 + 1)) := finite_sheafH_two sX (isProjectiveMorphism_of_isProjective_of_isAffine sX hX)
  obtain ⟨s, hs⟩ := exists_finset_map_sub_sum_eq_zero (obstructionHom sX hS)
  refine ⟨s, fun E => ?_⟩
  obtain ⟨n, hn⟩ := hs E
  refine ⟨n, fun C => ?_⟩
  rw [← sub_eq_zero, ← map_sub, degreeHom_apply]
  refine MMP.Analytic.degreeOn_eq_zero_of_tmul_picardObstruction_eq_zero sX hX _
    (fun _ => ?_) C.scheme C.ι C.dim_le
  exact (congrArg ((1 : ℚ) ⊗ₜ[ℤ] ·) hn).trans (TensorProduct.tmul_zero _ _)

/-- The intersection number of an integral Cartier divisor with a proper curve is its degree. -/
private theorem intersectionPairing_ofCartier {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    (E : X.CartierDivisor) (C : ProperCurve sX) :
    OneCycle.intersectionPairing (sX := sX) (KCartierDivisor.ofCartier ℝ E) (C.cycle ℝ) =
      (degreeHom C E : ℝ) := by
  change (C.cycle ℝ).intersectionNumber _ = _
  rw [OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree, OneCycle.degree_cycle,
    degreeHom_apply]

/-- An integral Cartier divisor numerically equivalent to `∑ nⱼ Dⱼ` has the real numerical class
`∑ nⱼ [Dⱼ]`. -/
private theorem numericalDivisorClass_ofCartier_eq_sum {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    {E : X.CartierDivisor} {s : Finset X.CartierDivisor} {n : X.CartierDivisor → ℤ}
    (h : ∀ C : ProperCurve sX, degreeHom C E = degreeHom C (∑ D ∈ s, n D • D)) :
    MMP.Fourfold.numericalDivisorClass sX (KCartierDivisor.ofCartier ℝ E) =
      ∑ D ∈ s, (n D : ℝ) • MMP.Fourfold.numericalDivisorClass sX
        (KCartierDivisor.ofCartier ℝ D) := by
  simp_rw [← map_smul, ← map_sum]
  refine (Submodule.Quotient.eq _).2 (MMP.Fourfold.mem_numericallyTrivialDivisors.2 fun C => ?_)
  change OneCycle.intersectionPairing (sX := sX) (_ - _) (C.cycle ℝ) = 0
  rw [map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply]
  simp only [map_smul, LinearMap.smul_apply, intersectionPairing_ofCartier, h C, map_sum,
    map_zsmul, smul_eq_mul]
  push_cast
  ring

/-- The real numerical classes are spanned by the classes of integral Cartier divisors. -/
private theorem span_numericalDivisorClass_ofCartier {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) :
    Submodule.span ℝ (Set.range fun E : X.CartierDivisor =>
      MMP.Fourfold.numericalDivisorClass sX (KCartierDivisor.ofCartier ℝ E)) = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun x => ?_
  obtain ⟨D, rfl⟩ := Submodule.mkQ_surjective _ x
  change MMP.Fourfold.numericalDivisorClass sX D ∈ _
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' h h' => rw [map_add]; exact add_mem h h'
  | single E c =>
    rw [← mul_one c, ← smul_eq_mul, ← Finsupp.smul_single, map_smul]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨E, rfl⟩)

/-- **Theorem of the base for numerical equivalence on a projective complex variety.** Let `X` be
a scheme projective over `ℂ` (structure morphism `sX`). There is a finite set `s` of
Cartier divisors such that every Cartier divisor `E` has the same degree on every proper curve
as some integral combination `∑ D ∈ s, n D • D`; and the real vector space
`MMP.Fourfold.NumericalDivisorClasses sX` of `ℝ`-Cartier divisors modulo numerical equivalence
is finite-dimensional. -/
@[mmp "lem_mmp_projective_numerical_divisors_finite"]
public theorem exists_finset_cartierDivisor_degree_eq_sum_and_finiteDimensional
    {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (hX : IsProjective sX) :
    (∃ s : Finset X.CartierDivisor, ∀ E : X.CartierDivisor, ∃ n : X.CartierDivisor → ℤ,
      ∀ C : ProperCurve sX,
        C.degree ℂ (MMP.CartierDivisor.sheaf E) =
          C.degree ℂ (MMP.CartierDivisor.sheaf (∑ D ∈ s, n D • D))) ∧
      FiniteDimensional ℝ (NumericalDivisorClasses sX) := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_degree_eq_sum sX hX
  refine ⟨⟨s, hs⟩, Module.finite_def.2 ⟨s.image fun D =>
    MMP.Fourfold.numericalDivisorClass sX (KCartierDivisor.ofCartier ℝ D), ?_⟩⟩
  rw [eq_top_iff, ← span_numericalDivisorClass_ofCartier sX, Submodule.span_le]
  rintro _ ⟨E, rfl⟩
  obtain ⟨n, hn⟩ := hs E
  dsimp only
  rw [SetLike.mem_coe, numericalDivisorClass_ofCartier_eq_sum hn]
  exact Submodule.sum_mem _ fun D hD =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_image_of_mem _ hD))

end MMP.Fourfold
