module

public import MMP.AlgebraicGeometry.Analytic.FiniteCochainsBetti
public import MMP.AlgebraicGeometry.Analytic.ProjectiveSingularSheafComparison

/-!
# Rank of the image of integral cohomology

Let `X` be a projective scheme over `ℂ` and `X^an` its complex points with the analytic topology.
For any sheaf of abelian groups `F` on `X^an` and any map `ι : ℤ_{X^an} ⟶ F` from the constant
sheaf, the image `Γ` of `H^n(X^an, ℤ) → H^n(X^an, F)` is a finitely generated abelian group of
rank at most `b_n = dim_ℂ H^n(X^an; ℂ)`. For `ι` the first map of the exponential sequence
`0 → ℤ → 𝒪 → 𝒪^× → 0` and `n = 1`, `Γ` is the image of `H¹(X^an, ℤ)` in `H¹(X^an, 𝒪)`.

The rank count rests on two facts: `H^n(X^an; ℤ)` is finitely generated and its rationalization
is `H^n(X^an; ℚ)`, and the change of coefficients `H^n(Y; ℚ) → H^n(Y; ℂ)` carries
`ℚ`-linearly independent classes to `ℂ`-linearly independent ones, for any space `Y`; the latter
is proved on cochains, with `ℚ`-linear functionals `ℂ → ℚ`.

Conversely, a finitely generated subgroup `Γ` of a complex vector space `W` that spans `W` over
`ℝ` has rank at least `dim_ℝ W = 2 dim_ℂ W`. Together: if the image of `H¹(X^an, ℤ)` spans
`H¹(X, 𝒪_X)` over `ℝ`, then `2 h¹(𝒪_X) ≤ b₁`.

## Main results

* `MMP.Analytic.SurfaceHodge.linearIndependent_mapCoeff_rat_complex`: `H^n(Y; ℚ) → H^n(Y; ℂ)`
  preserves linear independence.
* `MMP.Analytic.SurfaceHodge.finrank_rat_le_finrank_complex`: `dim_ℚ H^n(Y; ℚ) ≤ dim_ℂ H^n(Y; ℂ)`.
* `MMP.Analytic.SurfaceHodge.finite_range_of_sheafH_constantSheaf`,
  `MMP.Analytic.SurfaceHodge.finrank_range_le_finrank_analyticSingularCohomology`: the image of
  any additive map out of `H^n(X^an, ℤ)` (for instance `H^n(X^an, ℤ) → H^n(X^an, F)`) is finitely
  generated, of rank at most `b_n`.
* `MMP.Analytic.SurfaceHodge.two_mul_finrank_le_finrank_of_span_real_eq_top`: a finitely
  generated subgroup spanning a complex vector space `W` over `ℝ` has rank `≥ 2 dim_ℂ W`.
* `MMP.Analytic.SurfaceHodge.two_mul_finrank_le_finrank_analyticSingularCohomology`:
  `2 dim_ℂ W ≤ b_n` when the image of `H^n(X^an, ℤ)` spans `W` over `ℝ`.
* `MMP.Analytic.SurfaceHodge.two_mul_finrank_cohomologyOverField_unit_one_le`:
  `2 h¹(𝒪_X) ≤ b₁` when the image of `H¹(X^an, ℤ)` spans `H¹(X, 𝒪_X)` over `ℝ`.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][griffithsharris1978], Ch. 2 §6.
* [A. Hatcher, *Algebraic Topology*][hatcher2002], §3.1.
-/

public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.SingularChain MMP.SingularCochain

namespace MMP.Analytic.SurfaceHodge

section Coefficients

variable {R S : Type} [CommRing R] [CommRing S] {Y : TopCat.{0}}

/-- An additive map `π : R → S` of coefficients commutes with the coboundary. -/
private lemma coboundary_comp_addMonoidHom (π : R →+ S) (n : ℕ) (α : Simplex Y n → R) :
    coboundary S n (π ∘ α) = π ∘ coboundary R n α := by
  ext σ
  simp only [coboundary_apply, Function.comp_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases Nat.even_or_odd (i : ℕ) with h | h <;> simp [h.neg_one_pow]

/-- An additive map of coefficients carries relative coboundaries to relative coboundaries. -/
private lemma comp_mem_relCoboundaries (π : R →+ S) {A : Set Y} {n : ℕ}
    {ψ : Simplex Y n → R} (h : ψ ∈ relCoboundaries R A n) :
    (π ∘ ψ) ∈ relCoboundaries S A n := by
  cases n with
  | zero =>
    simp only [relCoboundaries, Submodule.mem_bot] at h ⊢
    subst h
    funext σ
    simp
  | succ m =>
    obtain ⟨α, hα, rfl⟩ := h
    exact ⟨π ∘ α, fun σ hσ => by simp [hα σ hσ], coboundary_comp_addMonoidHom π m α⟩

end Coefficients

/-- A linear combination of classes in a quotient is the class of the linear combination. -/
private lemma sum_smul_mk {K M : Type*} [Ring K] [AddCommGroup M] [Module K M]
    (p : Submodule K M) {ι : Type*} (s : Finset ι) (g : ι → K) (c : ι → M) :
    ∑ x ∈ s, g x • (Submodule.Quotient.mk (c x) : M ⧸ p) =
      Submodule.Quotient.mk (∑ x ∈ s, g x • c x) := by
  simp only [← Submodule.mkQ_apply p, map_sum, map_smul]

/-- **Rational and complex classes.** The change of coefficients `H^n(Y; ℚ) → H^n(Y; ℂ)` carries a
`ℚ`-linearly independent family to a `ℂ`-linearly independent family. -/
theorem linearIndependent_mapCoeff_rat_complex {Y : TopCat.{0}} {n : ℕ} {ι : Type*}
    {v : ι → singularCohomology ℚ Y n} (hv : LinearIndependent ℚ v) :
    LinearIndependent ℂ fun i => singularCohomology.mapCoeff (algebraMap ℚ ℂ) n (v i) := by
  classical
  set eQ := relativeSingularCohomologyEquiv ℚ (Set.univᶜ : Set Y) n
  set eC := relativeSingularCohomologyEquiv ℂ (Set.univᶜ : Set Y) n
  choose φ hφ using fun i => Submodule.Quotient.mk_surjective _ (eQ (v i))
  rw [linearIndependent_iff'] at hv ⊢
  intro s g hg i hi
  have hC : ∀ j, eC (singularCohomology.mapCoeff (algebraMap ℚ ℂ) n (v j)) =
      Submodule.Quotient.mk (singularCohomology.relCocyclesMap (algebraMap ℚ ℂ) _ n (φ j)) := by
    intro j
    simp only [singularCohomology.mapCoeff, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply]
    rw [← hφ j]
    exact (eC.apply_symm_apply _).trans (Submodule.mapQ_apply _ _ _ _)
  have hcob : (∑ j ∈ s, g j • singularCohomology.cochainMap (algebraMap ℚ ℂ) n
      (φ j : Simplex Y n → ℚ)) ∈ relCoboundaries ℂ (Set.univᶜ : Set Y) n := by
    have h1 := congrArg eC hg
    rw [map_zero, map_sum] at h1
    simp_rw [map_smul, hC] at h1
    rw [sum_smul_mk, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.coe_subtype] at h1
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
    exact h1
  refine (Module.forall_dual_apply_eq_zero_iff ℚ (g i)).1 fun π => ?_
  refine hv s (fun j => π (g j)) ?_ i hi
  apply eQ.injective
  rw [map_sum, map_zero]
  simp_rw [map_smul, ← hφ]
  rw [sum_smul_mk, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype]
  convert comp_mem_relCoboundaries π.toAddMonoidHom hcob using 1
  funext σ
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    Function.comp_apply, map_sum, smul_eq_mul, singularCohomology.cochainMap_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.toAddMonoidHom_coe, mul_comm (g j), ← Algebra.smul_def, map_smul, smul_eq_mul]
  exact mul_comm _ _

/-- `dim_ℚ H^n(Y; ℚ) ≤ dim_ℂ H^n(Y; ℂ)` when `H^n(Y; ℂ)` is finite-dimensional. -/
theorem finrank_rat_le_finrank_complex (Y : TopCat.{0}) (n : ℕ)
    [Module.Finite ℂ (singularCohomology ℂ Y n)] :
    Module.finrank ℚ (singularCohomology ℚ Y n) ≤ Module.finrank ℂ (singularCohomology ℂ Y n) := by
  by_cases hf : Module.Finite ℚ (singularCohomology ℚ Y n)
  · simpa using (linearIndependent_mapCoeff_rat_complex
      (Module.finBasis ℚ (singularCohomology ℚ Y n)).linearIndependent).fintype_card_le_finrank
  · simp [Module.finrank_of_not_finite hf]

/-- `H^n(X^an, ℤ)` of a projective scheme over `ℂ` is finitely generated, of rank
`dim_ℚ H^n(X^an; ℚ)`. -/
private lemma finite_and_finrank_sheafH_constantSheaf {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (hX : IsProjectiveMorphism sX) (n : ℕ) :
    Module.Finite ℤ (Sheaf.H.{0} ((constantSheaf (Opens.grothendieckTopology
        (Analytification.space sX)) AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)) n) ∧
      Module.finrank ℤ (Sheaf.H.{0} ((constantSheaf (Opens.grothendieckTopology
        (Analytification.space sX)) AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)) n) =
        Module.finrank ℚ (analyticSingularCohomology ℚ sX n) := by
  obtain ⟨φ, -⟩ := exists_addEquiv_sheafH_constantSheaf_singularCohomology ℤ n
  have hfin := (exists_homotopyEquiv_singularChainComplex_of_isProjectiveMorphism sX hX).2.1 n
  have hb := isBaseChange_mapCoeff_of_isProjectiveMorphism sX hX n
  have hl := (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ _).2 hb
  have hr := @IsLocalizedModule.finrank_eq _ _ _ _ _ _ _ _ (nonZeroDivisors ℤ) _ hl le_rfl
  rw [← IsFractionRing.finrank_right_eq ℤ ℚ] at hr
  change Module.finrank ℚ _ = Module.finrank ℤ
    (MMP.Analytic.singularCohomology ℤ (ComplexPoints.analyticSpace sX) n) at hr
  rw [MMP.Analytic.singularCohomology, cohomologyWithSupports.univ] at hfin hr
  exact ⟨Module.Finite.equiv (φ sX hX).symm.toIntLinearEquiv,
    (φ sX hX).toIntLinearEquiv.finrank_eq.trans hr.symm⟩

/-- **The image of integral cohomology is finitely generated.** For a projective scheme `X` over
`ℂ` and an additive map `g` out of `H^n(X^an, ℤ)`, the image of `g` is a finitely generated
abelian group. -/
theorem finite_range_of_sheafH_constantSheaf {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (hX : IsProjectiveMorphism sX) (n : ℕ) {M : Type*} [AddCommGroup M]
    (g : Sheaf.H.{0} ((constantSheaf (Opens.grothendieckTopology (Analytification.space sX))
      AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)) n →+ M) : Module.Finite ℤ g.range := by
  have := (finite_and_finrank_sheafH_constantSheaf sX hX n).1
  exact Module.Finite.of_surjective g.rangeRestrict.toIntLinearMap g.rangeRestrict_surjective

/-- **Rank of the image of integral cohomology.** For a projective scheme `X` over `ℂ` and an
additive map `g` out of `H^n(X^an, ℤ)`, the image of `g` has rank at most
`b_n = dim_ℂ H^n(X^an; ℂ)`. -/
theorem finrank_range_le_finrank_analyticSingularCohomology {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) (hX : IsProjectiveMorphism sX) (n : ℕ) {M : Type*} [AddCommGroup M]
    (g : Sheaf.H.{0} ((constantSheaf (Opens.grothendieckTopology (Analytification.space sX))
      AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)) n →+ M) :
    Module.finrank ℤ g.range ≤ Module.finrank ℂ (analyticSingularCohomology ℂ sX n) := by
  obtain ⟨hfin, hrk⟩ := finite_and_finrank_sheafH_constantSheaf sX hX n
  have : Module.Finite ℂ (analyticSingularCohomology ℂ sX n) :=
    finite_analyticSingularCohomology_of_isProjectiveMorphism sX hX ℂ n
  calc Module.finrank ℤ g.range ≤ Module.finrank ℤ (Sheaf.H.{0} ((constantSheaf
        (Opens.grothendieckTopology (Analytification.space sX)) AddCommGrpCat.{0}).obj
          (AddCommGrpCat.of ℤ)) n) :=
        LinearMap.finrank_le_finrank_of_surjective (f := g.rangeRestrict.toIntLinearMap)
          g.rangeRestrict_surjective
    _ = Module.finrank ℚ (analyticSingularCohomology ℚ sX n) := hrk
    _ ≤ _ := finrank_rat_le_finrank_complex _ n

/-- **Rank of a spanning subgroup.** A finitely generated subgroup `Γ` of a complex vector space
`W` whose `ℝ`-span is `W` has rank at least `dim_ℝ W = 2 dim_ℂ W`. -/
theorem two_mul_finrank_le_finrank_of_span_real_eq_top {W : Type*} [AddCommGroup W]
    [Module ℂ W] {Γ : AddSubgroup W} [Module.Finite ℤ Γ]
    (hΓ : Submodule.span ℝ (Γ : Set W) = ⊤) :
    2 * Module.finrank ℂ W ≤ Module.finrank ℤ Γ := by
  have : Module.IsTorsionFree ℤ Γ := ⟨fun r hr x y h => by
    have hr0 : (r : ℂ) ≠ 0 := Int.cast_ne_zero.2 hr.ne_zero
    apply Subtype.ext
    have h' : (r : ℂ) • (x : W) = (r : ℂ) • (y : W) := by
      rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
      simpa using congrArg Subtype.val h
    exact smul_right_injective W hr0 h'⟩
  have : Module.Free ℤ Γ := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis ℤ Γ
  have hspan : Submodule.span ℝ (Set.range fun i => (b i : W)) = ⊤ := by
    refine top_unique (hΓ ▸ Submodule.span_le.2 fun x hx => ?_)
    have hx' : x = ∑ i, (b.repr ⟨x, hx⟩ i : ℝ) • (b i : W) := by
      calc x = Γ.subtype (∑ i, b.repr ⟨x, hx⟩ i • b i) := by rw [b.sum_repr]; rfl
        _ = _ := by simp only [map_sum, map_zsmul, Int.cast_smul_eq_zsmul]; rfl
    rw [hx']
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have : Module.Finite ℝ W :=
    Module.finite_def.2 (hspan ▸ Submodule.fg_span (Set.finite_range _))
  have : Module.Finite ℂ W := Module.Finite.of_restrictScalars_finite ℝ ℂ W
  have hle := finrank_range_le_card (R := ℝ) fun i => (b i : W)
  rw [Set.finrank, hspan, finrank_top, finrank_real_of_complex] at hle
  rwa [Module.finrank_eq_card_chooseBasisIndex ℤ Γ]

/-- **The rank count.** Let `X` be a projective scheme over `ℂ`, `F` a sheaf of abelian groups
on `X^an` with a map `ι : ℤ_{X^an} ⟶ F`, and `e : H^n(X^an, F) →+ W` an additive map to a complex
vector space. If the image of `H^n(X^an, ℤ)` in `W` spans `W` over `ℝ`, then
`2 dim_ℂ W ≤ b_n`. -/
theorem two_mul_finrank_le_finrank_analyticSingularCohomology {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) (hX : IsProjectiveMorphism sX) (n : ℕ)
    {F : Sheaf (Opens.grothendieckTopology (Analytification.space sX)) AddCommGrpCat.{0}}
    (ι : (constantSheaf (Opens.grothendieckTopology (Analytification.space sX))
      AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ) ⟶ F) {W : Type*} [AddCommGroup W] [Module ℂ W]
    (e : Sheaf.H.{0} F n →+ W)
    (hspan : Submodule.span ℝ (Set.range fun x => e (Sheaf.H.map ι n x)) = ⊤) :
    2 * Module.finrank ℂ W ≤ Module.finrank ℂ (analyticSingularCohomology ℂ sX n) := by
  have := finite_range_of_sheafH_constantSheaf sX hX n (e.comp (Sheaf.H.map ι n))
  calc 2 * Module.finrank ℂ W ≤ Module.finrank ℤ (e.comp (Sheaf.H.map ι n)).range :=
        two_mul_finrank_le_finrank_of_span_real_eq_top (by rwa [AddMonoidHom.coe_range])
    _ ≤ _ := finrank_range_le_finrank_analyticSingularCohomology sX hX n _

/-- **`2 h¹(𝒪_X) ≤ b₁`.** Let `X` be a projective variety over `ℂ`, `F` a sheaf of abelian groups
on `X^an` with a map `ι : ℤ_{X^an} ⟶ F` (for instance `𝒪_{X^an}` and the first map of the
exponential sequence) and `e : H¹(X^an, F) →+ H¹(X, 𝒪_X)` an additive map (for instance the GAGA
comparison). If the image of `H¹(X^an, ℤ)` in `H¹(X, 𝒪_X)` spans it over `ℝ`, then
`2 h¹(𝒪_X) ≤ b₁`. -/
theorem two_mul_finrank_cohomologyOverField_unit_one_le {X : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ))]
    {F : Sheaf (Opens.grothendieckTopology (Analytification.space (X ↘ Spec (.of ℂ))))
      AddCommGrpCat.{0}}
    (ι : (constantSheaf (Opens.grothendieckTopology
      (Analytification.space (X ↘ Spec (.of ℂ)))) AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ) ⟶ F)
    (e : Sheaf.H.{0} F 1 →+ cohomologyOverField ℂ (X ↘ Spec (.of ℂ))
      (SheafOfModules.unit X.ringCatSheaf) 1)
    (hspan : Submodule.span ℝ (Set.range fun x => e (Sheaf.H.map ι 1 x)) = ⊤) :
    2 * Module.finrank ℂ (cohomologyOverField ℂ (X ↘ Spec (.of ℂ))
        (SheafOfModules.unit X.ringCatSheaf) 1) ≤
      Module.finrank ℂ (analyticSingularCohomology ℂ (X ↘ Spec (.of ℂ)) 1) :=
  two_mul_finrank_le_finrank_analyticSingularCohomology _
    (IsProjectiveVariety.isProjective (k := ℂ)) 1 ι e hspan

end MMP.Analytic.SurfaceHodge
