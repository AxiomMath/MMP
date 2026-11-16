module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Intersection.OneCycles
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.Divisor.RationalCycleMap
public import MMP.AlgebraicGeometry.Modules.ProjectionFormulaInvertible
public import MMP.AlgebraicGeometry.Divisor.Basic
public import MMP.AlgebraicGeometry.Morphisms.Birational.RationalMap
public import MMP.AlgebraicGeometry.Singularities.CyclicCover.Basic
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
import MMP.AlgebraicGeometry.Resolution.OrderUpperSemicontinuous
import MMP.AlgebraicGeometry.Curves.Maps.Injectivity
import MMP.AlgebraicGeometry.Modules.SquareZeroInvertibleLift
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Modules.CurveFibreLineBundle
import MMP.AlgebraicGeometry.Divisor.WeilSubsheaf.S2
import MMP.AlgebraicGeometry.Cohomology.LongExactDimensionBounds

/-!
# Foundational results: ampleness, affine pull-push, surfaces, Cohen–Macaulay modules

This file collects independent foundational facts used throughout the minimal model program.

*Ample twists and real ampleness.* On a scheme `X` proper over a field, if `𝒪_X(D)` is ample
then `𝒪_X(mD + E)` is ample for `m ≫ 0`. Consequently, on a scheme projective over a field, a
positive real combination `H = ∑ᵢ aᵢ Aᵢ` of ample Cartier divisors stays such a combination
after any small perturbation `H + ∑ⱼ tⱼ Eⱼ` in finitely many `ℝ`-Cartier directions. Expanding
each `Eⱼ = ∑ₗ cⱼₗ Fⱼₗ` in integral Cartier divisors, one chooses `N` with every `N A₁ ± Fⱼₗ`
ample and uses
`a₁ A₁ + ∑ₗ uₗ Fₗ = (a₁ - 2NKη) A₁ + ∑ₗ (η + uₗ / 2) (N A₁ + Fₗ) + ∑ₗ (η - uₗ / 2) (N A₁ - Fₗ)`,
`K` the number of the `Fₗ`, all of whose coefficients are positive once every `|uₗ| < η` and
`2NKη < a₁`.

*Affine pull-push.* For an affine morphism `f : Y ⟶ X` and a quasi-coherent `𝒪_X`-module `F`,
`f_* f^* F ≅ F ⊗ f_* 𝒪_Y`, and under this isomorphism the unit of `f^* ⊣ f_*` is `id_F ⊗ f^♯`.
Over an affine open `Spec A` with preimage `Spec B` and `F = M~` this is the symmetry
`B ⊗_A M ≅ M ⊗_A B`, carrying `m ↦ 1 ⊗ m` to `m ↦ m ⊗ 1`.

*Surfaces and smoothness.* Every normal surface over an algebraically closed field admits a
proper birational morphism from a smooth surface (Lipman). Over an algebraically closed field of
characteristic zero, the smooth locus of a scheme of finite type is its regular locus.

*Cohen–Macaulay modules.* For a Noetherian local ring `R` and a finite `R`-module `N`,
Cohen–Macaulayness localizes at every prime (the zero module counting as Cohen–Macaulay), and
for `x ∈ 𝔪` regular on `N`, `N` is Cohen–Macaulay if and only if `N/xN` is. Cohen–Macaulayness
of a module over a local quotient `S` of `R` is the same over `S` as over `R`, since
`Spec S → Spec R` identifies the supports as ordered sets and regular sequences lift.

*Semicontinuity.* For a projective morphism `f : Z ⟶ T` of Noetherian schemes and a coherent
`𝒪_Z`-module `𝓕` flat over `T`, `t ↦ dim_{κ(t)} H^i(Z_t, 𝓕_t)` is upper semicontinuous.

## Main results

* `MMP.Mori.eventually_isAmple_cartierSheaf_nsmul_add_of_isProper`: `mD + E` is ample for
  `m ≫ 0` on a proper scheme, when `D` is ample.
* `MMP.Intersection.exists_pos_forall_abs_lt_isRepresentation_ample_add_sum`: openness of real
  ampleness in a finite span.
* `MMP.Modules.exists_pushforward_pullback_iso_tensor_unit`: affine pull-push is tensoring with
  `f_* 𝒪_Y`, with the unit identified as `id ⊗ f^♯`.
* `MMP.Mori.exists_smooth_isProper_isBirationalMorphism_of_isNormalVariety`: resolution of
  normal surfaces over an algebraically closed field.
* `MMP.Mori.IsCMModule.of_isLocalizedModule`: Cohen–Macaulay modules localize.
* `MMP.Mori.isCMModule_quotSMulTop_iff`: Cohen–Macaulayness and quotients by a regular element.
* `MMP.Mori.mem_smoothLocus_iff_isRegularLocalRing`: the smooth locus is the regular locus.
* `MMP.upperSemicontinuous_finrank_cohomologyOverField_fiber`: semicontinuity of fibre
  cohomology.

## Implementation notes

Ampleness of a Cartier divisor `D` is ampleness (`Stacks.Ample.IsAmple`, Stacks Tag 01PS) of
`MMP.CartierDivisor.sheaf D`, and "for `m ≫ 0`" is `∀ᶠ m in Filter.atTop`.
`ℝ`-Cartier divisors are `MMP.Intersection.RCartierDivisor X = X.CartierDivisor ⊗[ℤ] ℝ`; the
coefficients sit in the right factor, which carries no `ℝ`-module instance, so `tⱼ Eⱼ` is
`MMP.Intersection.coeffSMul (t j) (E j)` and `D = ∑ᵢ aᵢ Aᵢ` is
`MMP.Intersection.CartierDivisorWithCoeffs.IsRepresentation D a A`. Projectivity over a field
is `AlgebraicGeometry.IsProjectiveMorphism` of the structure morphism (Stacks Tag 01W8).

The tensor product of `𝒪_X`-modules is that of `Stacks.SheafOfModules.Strict.monoidalCategory`
(the tensor product sheaf of Stacks 01CA, with unit the structure sheaf), supplied by `letI`
since it is not an instance; `f^♯ : 𝒪_X ⟶ f_* 𝒪_Y` is
`SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom`. The isomorphism is the case
`G = 𝒪_Y` of the affine projection formula (Stacks 0FZE), composed with the braiding.

A surface over `k` is a variety `X ⟶ Spec k` with `topologicalKrullDim X = 2`. Localizations
are presented abstractly, by `IsLocalization.AtPrime` and `IsLocalizedModule`; the instance
`IsLocalRing Rₚ`, which instance search does not find, is an argument. The quotient `N/xN` is
`QuotSMulTop x N`, and the change of base ring is stated for an arbitrary surjective local
`R`-algebra `S`. The fibre `Z_t` is `AlgebraicGeometry.Scheme.Hom.fiber` and `H^i(Z_t, 𝓕_t)` is
`AlgebraicGeometry.cohomologyOverField`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], §0.4, §1.4, 5.1
* [R. Lazarsfeld, *Positivity in algebraic geometry I*][Lazarsfeld], Example 1.3.14
* [J. Lipman, *Desingularization of two-dimensional schemes*][Lipman1978]
* [Hartshorne, *Algebraic Geometry*, III.12.8]
* [Stacks Project, Tags 01PS, 0FZE, 01SB, 0BGP, 0AAG, 00TV, 0BDN]
-/

open CategoryTheory AlgebraicGeometry

universe u

/-! ### Ample twists and real ampleness -/

namespace MMP.Mori

/-- On a scheme `X` proper over a field `k`, if `D` is a Cartier divisor with `𝒪_X(D)` ample and
`E` is any Cartier divisor, then `𝒪_X(mD + E)` is ample for all sufficiently large `m`. This is
the special case of `MMP.Mori.eventually_isAmple_cartierSheaf_nsmul_add`, which needs no
properness. -/
@[mmp "lem_mmp_foundation_proper_ample_twist"]
public theorem eventually_isAmple_cartierSheaf_nsmul_add_of_isProper {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] (D E : X.CartierDivisor)
    (hD : Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf D)) :
    ∀ᶠ m : ℕ in Filter.atTop,
      Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf (m • D + E)) :=
  eventually_isAmple_cartierSheaf_nsmul_add D E hD

end MMP.Mori

namespace MMP.Intersection

open TensorProduct

/-- A finite positive combination indexed by any nonempty finite type is a representation
indexed by some `Fin m` with `1 ≤ m`. -/
private theorem exists_isRepresentation_fin_of_fintype {X : Scheme.{u}} {T : Type*} [Fintype T]
    [Nonempty T] {D : RCartierDivisor X} (b : T → ℝ) (B : T → X.CartierDivisor) (hb : ∀ x, 0 < b x)
    (hB : ∀ x, Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf (B x)))
    (hD : D = ∑ x, B x ⊗ₜ b x) :
    ∃ (m : ℕ) (a : Fin m → ℝ) (A : Fin m → X.CartierDivisor), 1 ≤ m ∧ (∀ i, 0 < a i) ∧
      (∀ i, Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf (A i))) ∧
      CartierDivisorWithCoeffs.IsRepresentation D a A := by
  let e := Fintype.equivFin T
  refine ⟨Fintype.card T, fun i => b (e.symm i), fun i => B (e.symm i), Fintype.card_pos,
    fun i => hb _, fun i => hB _, ?_⟩
  rw [CartierDivisorWithCoeffs.IsRepresentation, hD]
  exact (e.symm.sum_comp (fun x => B x ⊗ₜ b x)).symm

/-- The two twists `N B ± G`, weighted by `η ± u / 2`, add up to `2Nη B + u G`. -/
private theorem nsmul_add_tmul_add_nsmul_sub_tmul {M : Type*} [AddCommGroup M] (N : ℕ)
    (B G : M) (η u : ℝ) :
    (N • B + G) ⊗ₜ[ℤ] (η + u / 2) + (N • B - G) ⊗ₜ[ℤ] (η - u / 2) =
      B ⊗ₜ (2 * N * η) + G ⊗ₜ u := by
  have hns : ∀ r : ℝ, (N • B) ⊗ₜ[ℤ] r = B ⊗ₜ[ℤ] ((N : ℝ) * r) := fun r => by
    rw [TensorProduct.smul_tmul, nsmul_eq_mul]
  have key : ∀ x y : ℝ, (N • B + G) ⊗ₜ[ℤ] x + (N • B - G) ⊗ₜ[ℤ] y =
      B ⊗ₜ (N * x + N * y) + G ⊗ₜ (x - y) := fun x y => by
    rw [add_tmul, sub_tmul, hns, hns, tmul_add B, tmul_sub G]
    abel
  rw [key]
  congr 2 <;> ring

/-- The perturbation step: if `H = ∑ᵢ aᵢ Aᵢ` is a positive combination of ample divisors and
every `N A_{i₀} ± F_s` is ample, then `H + ∑ₛ uₛ Fₛ` is again a positive combination of ample
divisors as soon as every `|uₛ| < η` and `2 N K η < a_{i₀}`, `K` the number of directions. -/
private theorem exists_isRepresentation_add_sum_tmul {X : Scheme.{u}} {m : ℕ}
    {a : Fin m → ℝ} {A : Fin m → X.CartierDivisor} {H : RCartierDivisor X}
    (ha : ∀ i, 0 < a i)
    (hA : ∀ i, Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf (A i)))
    (hH : CartierDivisorWithCoeffs.IsRepresentation H a A) (i₀ : Fin m) (N : ℕ)
    {σ : Type*} [Fintype σ] (F : σ → X.CartierDivisor)
    (hN : ∀ s, Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf (N • A i₀ + F s)) ∧
      Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf (N • A i₀ - F s)))
    (u : σ → ℝ) (η : ℝ) (hu : ∀ s, |u s| < η)
    (hη : 2 * N * Fintype.card σ * η < a i₀) :
    ∃ (m : ℕ) (a : Fin m → ℝ) (A : Fin m → X.CartierDivisor), 1 ≤ m ∧ (∀ i, 0 < a i) ∧
      (∀ i, Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf (A i))) ∧
      CartierDivisorWithCoeffs.IsRepresentation (H + ∑ s, F s ⊗ₜ u s) a A := by
  set δ : ℝ := 2 * N * Fintype.card σ * η
  let a' : Fin m → ℝ := fun i => a i - if i = i₀ then δ else 0
  have ha' : ∀ i, 0 < a' i := fun i => by
    obtain rfl | h := eq_or_ne i i₀
    · simp [a', hη]
    · simp [a', h, ha i]
  have hsum' : ∑ i, A i ⊗ₜ[ℤ] a' i = ∑ i, A i ⊗ₜ a i - A i₀ ⊗ₜ δ := by
    have hite : ∑ i, A i ⊗ₜ[ℤ] (if i = i₀ then δ else 0) = A i₀ ⊗ₜ δ := by
      rw [Finset.sum_eq_single i₀ (fun i _ hi => by simp [hi]) (by simp)]
      simp
    simp only [a', tmul_sub, Finset.sum_sub_distrib, hite]
  have : Nonempty (Fin m ⊕ (σ ⊕ σ)) := ⟨Sum.inl i₀⟩
  refine exists_isRepresentation_fin_of_fintype (T := Fin m ⊕ (σ ⊕ σ))
    (Sum.elim a' (Sum.elim (fun s => η + u s / 2) (fun s => η - u s / 2)))
    (Sum.elim A (Sum.elim (fun s => N • A i₀ + F s) (fun s => N • A i₀ - F s)))
    (by
      rintro (i | s | s) <;> simp only [Sum.elim_inl, Sum.elim_inr]
      exacts [ha' i, by linarith [abs_lt.1 (hu s)], by linarith [abs_lt.1 (hu s)]])
    (by rintro (i | s | s) <;> simp [hA, hN]) ?_
  rw [CartierDivisorWithCoeffs.IsRepresentation] at hH
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, ← Finset.sum_add_distrib,
    nsmul_add_tmul_add_nsmul_sub_tmul]
  rw [Finset.sum_add_distrib, ← tmul_sum, hsum', hH]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, δ]
  rw [show (Fintype.card σ : ℝ) * (2 * N * η) = 2 * N * Fintype.card σ * η by ring]
  abel

/-- On a scheme `X` projective over a field, if the `ℝ`-Cartier divisor `H` is a positive finite
real combination of ample Cartier divisors and `E : ι → RCartierDivisor X` is a finite family of
`ℝ`-Cartier divisors, then for some `ε₀ > 0` every `H + ∑ⱼ tⱼ Eⱼ` with all `|tⱼ| < ε₀` is again a
positive finite real combination of ample Cartier divisors. -/
@[mmp "lem_mmp_finite_span_ample_real_perturbation"]
public theorem exists_pos_forall_abs_lt_isRepresentation_ample_add_sum {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (hf : IsProjectiveMorphism f)
    {ι : Type*} [Fintype ι] (H : RCartierDivisor X) (E : ι → RCartierDivisor X)
    (hH : ∃ (m : ℕ) (a : Fin m → ℝ) (A : Fin m → X.CartierDivisor), 1 ≤ m ∧ (∀ i, 0 < a i) ∧
      (∀ i, Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf (A i))) ∧
      CartierDivisorWithCoeffs.IsRepresentation H a A) :
    ∃ ε₀ > (0 : ℝ), ∀ t : ι → ℝ, (∀ j, |t j| < ε₀) →
      ∃ (m : ℕ) (a : Fin m → ℝ) (A : Fin m → X.CartierDivisor), 1 ≤ m ∧ (∀ i, 0 < a i) ∧
        (∀ i, Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf (A i))) ∧
        CartierDivisorWithCoeffs.IsRepresentation (H + ∑ j, coeffSMul (t j) (E j)) a A := by
  obtain ⟨m, a, A, hm, ha, hA, hH⟩ := hH
  have := isProper_of_isProjectiveMorphism f hf
  choose n c F hEF using fun j => CartierDivisorWithCoeffs.exists_isRepresentation (E j)
  let i₀ : Fin m := ⟨0, hm⟩
  -- one twist `N` absorbing every `± F`
  obtain ⟨N, hN⟩ := (Filter.eventually_all.2 fun s : Σ j, Fin (n j) =>
    (Mori.eventually_isAmple_cartierSheaf_nsmul_add_of_isProper f _ (F s.1 s.2) (hA i₀)).and
      (Mori.eventually_isAmple_cartierSheaf_nsmul_add_of_isProper f _ (-F s.1 s.2)
        (hA i₀))).exists
  let K : ℕ := Fintype.card (Σ j, Fin (n j))
  let C : ℝ := 1 + ∑ s : Σ j, Fin (n j), |c s.1 s.2|
  have hC : 0 < C := by positivity
  let η : ℝ := a i₀ / (2 * N * K + 1)
  have hη : 0 < η := div_pos (ha i₀) (by positivity)
  refine ⟨η / C, div_pos hη hC, fun t ht => ?_⟩
  have hsum : ∑ j, coeffSMul (t j) (E j) =
      ∑ s : Σ j, Fin (n j), F s.1 s.2 ⊗ₜ (t s.1 * c s.1 s.2) := by
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hEF j, map_sum]
    simp
  rw [hsum]
  refine exists_isRepresentation_add_sum_tmul ha hA hH i₀ N (fun s => F s.1 s.2)
    (fun s => by simpa [sub_eq_add_neg] using hN s) _ η (fun s : Σ j, Fin (n j) => ?_) ?_
  · have hcC : |c s.1 s.2| ≤ C := (Finset.single_le_sum (f := fun s : Σ j, Fin (n j) =>
      |c s.1 s.2|) (fun _ _ => abs_nonneg _) (Finset.mem_univ s)).trans
      (le_add_of_nonneg_left zero_le_one)
    rw [abs_mul]
    calc |t s.1| * |c s.1 s.2| ≤ |t s.1| * C := by gcongr
      _ < η := (lt_div_iff₀ hC).1 (ht _)
  · rw [show 2 * (N : ℝ) * K * η = a i₀ * (2 * N * K / (2 * N * K + 1)) by
      simp only [η]
      field_simp]
    exact mul_lt_of_lt_one_right (ha i₀) ((div_lt_one (by positivity)).2 (lt_add_one _))

end MMP.Intersection

/-! ### Affine pull-push -/

namespace MMP.Modules

open MonoidalCategory
open scoped TensorProduct

section TensorSections

attribute [local implicit_reducible] Stacks.SheafOfModules.TensorSheafification.structureSheaf
  Stacks.SheafOfModules.TensorSheafification.sheafify Stacks.SheafOfModules.Tensor.ringSheaf

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalCategory in
/-- The tensor product of two morphisms on the sheafification unit of a local pure tensor. -/
private theorem tensorHom_val_app_toSheafify_tmul {C : Type*} [Category C]
    {J : GrothendieckTopology C} (O : Cᵒᵖ ⥤ CommRingCat.{u})
    (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    {A A' D D' :
      SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)}
    (a : A ⟶ A') (b : D ⟶ D') (V : Cᵒᵖ) (x : A.val.obj V) (y : D.val.obj V) :
    (a ⊗ₘ b).val.app V ((Stacks.SheafOfModules.TensorSheafification.toSheafify O hO
        (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := O) A.val D.val)).app V (x ⊗ₜ y)) =
      (Stacks.SheafOfModules.TensorSheafification.toSheafify O hO
        (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := O) A'.val D'.val)).app V
          (a.val.app V x ⊗ₜ b.val.app V y) :=
  (congrArg (fun h => h.val.app V ((Stacks.SheafOfModules.TensorSheafification.toSheafify O hO
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := O) A.val D.val)).app V (x ⊗ₜ y)))
    (Stacks.SheafOfModules.tensorHom_eq_sheafify_map O hO a b)).trans
    (Stacks.SheafOfModules.sheafify_map_toSheafify_app O hO (a.val ⊗ₘ b.val) V (x ⊗ₜ y))

/-- The map out of a sheafification induced by `α`, on the image of a section under the
sheafification unit, is `α` of that section. -/
private theorem sheafify_map_comp_sheafifyValIso_hom_val_app_toSheafify {C : Type*}
    [Category C] {J : GrothendieckTopology C} (O : Cᵒᵖ ⥤ CommRingCat.{u})
    (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    {P : PresheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O)}
    {T : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)}
    (α : P ⟶ T.val) (V : Cᵒᵖ) (x : P.obj V) :
    ((Stacks.SheafOfModules.sheafifyFunctor O hO).map α ≫
        (Stacks.SheafOfModules.sheafifyValIso O hO T).hom).val.app V
        ((Stacks.SheafOfModules.TensorSheafification.toSheafify O hO P).app V x) = α.app V x :=
  (congrArg (((Stacks.SheafOfModules.sheafifyValIso O hO T).hom).val.app V)
    (Stacks.SheafOfModules.sheafify_map_toSheafify_app O hO α V x)).trans
    (Stacks.SheafOfModules.counit_toSheafify_app O hO T V (α.app V x))

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalCategory in
/-- Two maps out of a tensor product sheaf agree once they agree on the images of local pure
tensors. -/
private theorem sheafify_tensor_hom_ext {C : Type*} [Category C]
    {J : GrothendieckTopology C} (O : Cᵒᵖ ⥤ CommRingCat.{u})
    (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    {A D T : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)}
    {f₁ f₂ : A ⊗ D ⟶ T}
    (h : ∀ (V : Cᵒᵖ) (a : A.val.obj V) (d : D.val.obj V),
      f₁.val.app V ((Stacks.SheafOfModules.TensorSheafification.toSheafify O hO
          (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := O) A.val D.val)).app V (a ⊗ₜ d)) =
        f₂.val.app V ((Stacks.SheafOfModules.TensorSheafification.toSheafify O hO
          (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := O) A.val D.val)).app V (a ⊗ₜ d))) :
    f₁ = f₂ :=
  ((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction O hO).homEquiv _ _).injective <|
    PresheafOfModules.hom_ext fun V => ModuleCat.MonoidalCategory.tensor_ext fun a d => h V a d

end TensorSections

/-- On a scheme, the left unitor of the tensor product of `𝒪_X`-modules sends the image of a
local pure tensor `a ⊗ m` to `a • m`. -/
private lemma leftUnitor_hom_val_app_toSheafify_tmul {X : Scheme.{u}} (F : X.Modules)
    (V : (TopologicalSpace.Opens X)ᵒᵖ) (a : Γ(X, V.unop)) (m : Γ(F, V.unop)) :
    letI : MonoidalCategory X.Modules := Stacks.SheafOfModules.Strict.monoidalCategory
      X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)
    (λ_ F).hom.val.app V ((Stacks.SheafOfModules.TensorSheafification.toSheafify
      X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj (𝟙_ X.Modules).val F.val)).app V (a ⊗ₜ m)) =
      a • m := by
  letI : MonoidalCategory X.Modules := Stacks.SheafOfModules.Strict.monoidalCategory
    X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)
  rw [show (λ_ F) = Stacks.SheafOfModules.tensorSheafLeftUnitor X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) F from
    Stacks.SheafOfModules.Strict_leftUnitor_eq _ _ F]
  exact (sheafify_map_comp_sheafifyValIso_hom_val_app_toSheafify _ _ _ V _).trans rfl

/-- In a braided category, `ρ⁻¹ ≫ (F ◁ g) ≫ β` is `λ⁻¹ ≫ (g ▷ F)`. -/
private lemma rightUnitor_inv_whiskerLeft_braiding_comp {C : Type*} [Category C]
    [MonoidalCategory C] [BraidedCategory C] {F P Z : C} (g : 𝟙_ C ⟶ P) (k : P ⊗ F ⟶ Z) :
    (ρ_ F).inv ≫ F ◁ g ≫ (β_ F P).hom ≫ k = (λ_ F).inv ≫ g ▷ F ≫ k := by
  rw [BraidedCategory.braiding_naturality_right_assoc, rightUnitor_inv_braiding_assoc]

/-- **Affine pull-push is tensoring with `f_* 𝒪_Y`, with the canonical unit.** For an affine
morphism `f : Y ⟶ X` and a quasi-coherent `𝒪_X`-module `F` there is an isomorphism
`e : F ⊗ f_* 𝒪_Y ≅ f_* f^* F` under which the unit `F ⟶ f_* f^* F` of
`Scheme.Modules.pullbackPushforwardAdjunction f` is `id_F ⊗ f^♯`, with
`f^♯ = SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom`. -/
@[mmp "lem_mmp_foundation_affine_pull_push_unit"]
public theorem exists_pushforward_pullback_iso_tensor_unit {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsAffineHom f] (F : X.Modules) [F.IsQuasicoherent] :
    letI : MonoidalCategory X.Modules := Stacks.SheafOfModules.Strict.monoidalCategory
      X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)
    ∃ e : F ⊗ (Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
        (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj F),
      (ρ_ F).inv ≫ (F ◁ SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫ e.hom =
        (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F := by
  letI : MonoidalCategory X.Modules := Stacks.SheafOfModules.Strict.monoidalCategory
      X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)
  letI : BraidedCategory X.Modules := Stacks.SheafOfModules.Strict.braidedCategory
      X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)
  let E := Stacks.AlgebraicGeometry.ProjectionFormula.pushforwardUnitTensorIso f F ‹_›
  refine ⟨β_ _ _ ≪≫ E, ?_⟩
  refine (rightUnitor_inv_whiskerLeft_braiding_comp _ _).trans ?_
  refine (Iso.inv_comp_eq _).mpr ?_
  refine sheafify_tensor_hom_ext X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) fun V a m => ?_
  refine (PresheafOfModules.comp_app_apply _ _ _ _).trans ?_
  refine Eq.trans ?_ (PresheafOfModules.comp_app_apply _ _ _ _).symm
  refine Eq.trans ?_ (congrArg _ (leftUnitor_hom_val_app_toSheafify_tmul F V a m)).symm
  refine Eq.trans ?_ (Scheme.Modules.Hom.app_smul (U := V.unop)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F) a m).symm
  refine (congrArg (ConcreteCategory.hom (E.hom.val.app V))
    ((congrArg (fun φ : 𝟙_ X.Modules ⊗ F ⟶ _ => φ.val.app V _)
      (MonoidalCategory.tensorHom_id _ F).symm).trans
      (tensorHom_val_app_toSheafify_tmul _ _ _ (𝟙 F) V a m))).trans ?_
  refine (PresheafOfModules.comp_app_apply _ _ _ _).trans ?_
  refine (congrArg _ (Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap_unit_tmul
    f Y.unitModule F V _ m)).trans ?_
  exact Stacks.RingedSpace.tensorSheafUnitLeftIso_hom_tensorSheafUnit_tmul _ _ _ _ _

end MMP.Modules

/-! ### Surfaces and the smooth locus -/

namespace MMP.Mori

/-- A proper morphism of integral schemes onto a Noetherian scheme which is birational in the
sense of [Stacks, Tag 01RO] is birational in the sense of rational maps: it is an isomorphism
over a dense open of the target. -/
private theorem isBirationalMorphism_of_isBirational {Y X : Scheme.{u}} [IsIntegral X]
    [IsNoetherian X] [IsIntegral Y] (f : Y ⟶ X) [IsProper f] (hf : IsBirational f) :
    IsBirationalMorphism f := by
  obtain ⟨V, hV, hiso⟩ :=
    exists_dense_open_isIso_morphismRestrict_of_isBirational_of_isNoetherian f hf
  obtain ⟨x, hx⟩ := hV.nonempty
  obtain ⟨y, rfl⟩ := surjective_of_isProper_of_isBirational f hf x
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE f (f ⁻¹ᵁ V) V ⟨y, hx⟩ ⟨_, hx⟩ le_rfl ?_
  rwa [Scheme.Hom.resLE_eq_morphismRestrict]

/-- **Resolution of normal surfaces of finite type over an excellent field.** A normal integral
Noetherian two-dimensional scheme locally of finite type over an excellent field has a
resolution of singularities ([Stacks, Tag 0BGP]). -/
private theorem exists_isResolution_of_isNormal {k : Type u} [Field k] (hk : IsExcellent k)
    {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X] [IsNormal X] (s : X ⟶ Spec (.of k))
    [LocallyOfFiniteType s] (hdim : topologicalKrullDim X = 2) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsResolution f := by
  have hY : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite :=
    finite_irreducibleComponents_of_isCompact X
  let ν := Scheme.normalization X hY
  have : IsIso ν := (Scheme.isIso_normalization_iff_isNormal X hY).2 inferInstance
  have hdimN : topologicalKrullDim (X.normalizationScheme hY) = 2 :=
    (IsHomeomorph.topologicalKrullDim_eq ν (Scheme.homeoOfIso (asIso ν)).isHomeomorph).trans hdim
  have : IsNoetherian (X.normalizationScheme hY) := (isNoetherian_iff _).2
    ⟨isLocallyNoetherian_of_isOpenImmersion ν, QuasiCompact.compactSpace_of_compactSpace ν⟩
  have : IsNormal (X.normalizationScheme hY) := Scheme.isNormal_normalizationScheme X hY
  have hT := (tfae_exists_isAlteration_isRegular X hdim).out 4 2
  exact hT.1 ⟨hY, inferInstance,
    finite_singularLocus_of_locallyOfFiniteType_of_isExcellent hk (ν ≫ s) hdimN.le,
    fun y _ => isNormalRing_adicCompletion_of_isExcellent_of_isNormalRing _
      (isExcellent_stalk_of_locallyOfFiniteType hk (ν ≫ s) y)
      (Stacks.Models.isNormalRing_stalk inferInstance y)⟩

/-- **Resolution of normal surfaces.** Over an algebraically closed field `k`, every normal
surface `X` admits a proper birational `k`-morphism `f : Y ⟶ X` from a surface `Y` smooth
over `k`. -/
@[mmp "lem_mmp_foundation_alg_closed_normal_surface_resolution"]
public theorem exists_smooth_isProper_isBirationalMorphism_of_isNormalVariety
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (hX : IsNormalVariety k sX) (hdim : topologicalKrullDim X = 2) :
    ∃ (Y : Scheme.{u}) (sY : Y ⟶ Spec (.of k)) (f : Y ⟶ X),
      IsVariety k sY ∧ Smooth sY ∧ topologicalKrullDim Y = 2 ∧ f ≫ sX = sY ∧
        IsProper f ∧ IsBirationalMorphism f := by
  have : AlgebraicGeometry.IsVariety k sX := hX.1
  have : IsNormal X := hX.2
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := ⟨⟩
  obtain ⟨Y, f, ⟨hbir, hprop, hint⟩, hreg⟩ := exists_isResolution_of_isNormal
    (isExcellent_of_standard_classes_and_finiteType.{u, u}.1 k) sX hdim
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  refine ⟨Y, f ≫ sX, f, (isVariety_iff k _).2 ⟨hint, inferInstance, inferInstance,
    inferInstance⟩, (MMP.mem_smoothLocus_iff_isRegularLocalRing_of_perfectField (f ≫ sX)).2.2
      hreg.isRegularLocalRing_stalk,
    (topologicalKrullDim_eq_of_isModification f ⟨hbir, hprop, hint⟩).trans hdim, rfl, hprop,
    isBirationalMorphism_of_isBirational f hbir⟩

/-- For a scheme of finite type over an algebraically closed field `k` of characteristic zero, a
point lies in the smooth locus `MMP.Mori.smoothLocus f` of the structure morphism
`f : X ⟶ Spec k` if and only if the local ring of `X` at that point is a regular local ring. -/
@[mmp "lem_mmp_foundation_km_smooth_iff_regular"]
public theorem mem_smoothLocus_iff_isRegularLocalRing
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] (x : X) :
    x ∈ smoothLocus f ↔ IsRegularLocalRing (X.presheaf.stalk x) := by
  rw [smoothLocus_eq_smoothLocus]
  exact (MMP.mem_smoothLocus_iff_isRegularLocalRing_of_perfectField f).1 x

/-! ### Cohen–Macaulay modules -/

/-- For a nonzero finite module over a Noetherian local ring, `IsCohenMacaulayModule` is the
equation `depth_𝔪 M = dim Supp M` with the depth `Module.depth`. -/
private theorem isCohenMacaulayModule_iff_depth_eq_supportDim {R M : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Nontrivial M] :
    IsCohenMacaulayModule R M ↔
      (Module.depth R (IsLocalRing.maximalIdeal R) M : WithBot ℕ∞) = Module.supportDim R M := by
  rw [show Module.depth R (IsLocalRing.maximalIdeal R) M =
      Module.depthSup R (IsLocalRing.maximalIdeal R) M by
    rw [Module.depth, if_neg (Module.maximalIdeal_smul_top_ne_top M), Module.depthSup_eq_iSup]]
  rfl

/-- **Cohen–Macaulayness localizes.** Let `(R, 𝔪)` be a Noetherian local ring, `N` a finite
Cohen–Macaulay `R`-module and `p` a prime ideal of `R`. For any localization `Rₚ` of `R` at `p`
and any localization `f : N →ₗ[R] Nₚ` of `N` at `p`, the `Rₚ`-module `Nₚ` is Cohen–Macaulay.
This includes the case `p ∉ Supp N`, where `Nₚ = 0` (Stacks 0AAG). -/
@[mmp "lem_mmp_foundation_km5a_cm_localizes"]
public theorem IsCMModule.of_isLocalizedModule {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N]
    (hN : IsCMModule R N) (p : Ideal R) [p.IsPrime] (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ]
    [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ] {Nₚ : Type*} [AddCommGroup Nₚ] [Module R Nₚ]
    [Module Rₚ Nₚ] [IsScalarTower R Rₚ Nₚ] (f : N →ₗ[R] Nₚ) [IsLocalizedModule p.primeCompl f] :
    IsCMModule Rₚ Nₚ := by
  rcases subsingleton_or_nontrivial Nₚ with hNₚ | hNₚ
  · exact isCMModule_of_subsingleton
  have : Nontrivial N := not_subsingleton_iff_nontrivial.mp fun _ ↦
    not_subsingleton Nₚ (IsLocalizedModule.subsingleton_of_subsingleton p.primeCompl f)
  have : IsNoetherianRing Rₚ := IsLocalization.isNoetherianRing p.primeCompl Rₚ ‹_›
  have : Module.Finite Rₚ Nₚ := Module.Finite.of_isLocalizedModule p.primeCompl f
  have hd := isCohenMacaulayModule_iff_depth_eq_supportDim.mp
    ((isCMModule_iff_localDepth_eq_supportDim_and_isCohenMacaulayModule R N).2.mp hN)
  exact (isCMModule_iff_localDepth_eq_supportDim_and_isCohenMacaulayModule Rₚ Nₚ).2.mpr
    (isCohenMacaulayModule_iff_depth_eq_supportDim.mpr
      (Module.depth_eq_supportDim_of_isLocalizedModule N hd p Rₚ Nₚ f))

section BaseChange

open IsLocalRing RingTheory.Sequence

variable {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] [Algebra R S]
  (hf : Function.Surjective (algebraMap R S))
  {M : Type*} [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

include hf

/-- Along a surjection of local rings, the maximal ideal is the preimage of the maximal ideal. -/
private lemma algebraMap_mem_maximalIdeal_iff {r : R} :
    algebraMap R S r ∈ maximalIdeal S ↔ r ∈ maximalIdeal R := by
  have : (Ideal.comap (algebraMap R S) (maximalIdeal S)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ hf
  rw [← Ideal.mem_comap, IsLocalRing.eq_maximalIdeal this]

/-- Along a surjection of local rings, a sequence is regular on an `S`-module if and only if its
image is. -/
private lemma isRegularSequence_map_algebraMap_iff (xs : List R) :
    IsRegularSequence S M (xs.map (algebraMap R S)) ↔ IsRegularSequence R M xs := by
  unfold IsRegularSequence
  rw [isWeaklyRegular_map_algebraMap_iff]
  simp only [List.forall_mem_map, algebraMap_mem_maximalIdeal_iff hf]

omit hf in
/-- A prime of `R` in the support of an `S`-module contains the kernel of `R → S`. -/
private lemma ker_le_of_mem_support {p : PrimeSpectrum R} (hp : p ∈ Module.support R M) :
    RingHom.ker (algebraMap R S) ≤ p.asIdeal := by
  obtain ⟨m, hm⟩ := Module.mem_support_iff'.mp hp
  intro i hi
  by_contra h
  exact hm i h (by rw [← algebraMap_smul S i m, (RingHom.mem_ker).mp hi, zero_smul])

/-- Along a surjection `R → S`, `Spec S → Spec R` identifies the support of an `S`-module `M`
with its support as an `R`-module, as ordered sets. -/
private def supportOrderIso : Module.support S M ≃o Module.support R M where
  toFun q := ⟨PrimeSpectrum.comap (algebraMap R S) q.1,
    Module.support_subset_preimage_comap (R := R) (A := S) (M := M) q.2⟩
  invFun p := ⟨⟨Ideal.map (algebraMap R S) p.1.asIdeal,
      Ideal.map_isPrime_of_surjective hf (ker_le_of_mem_support p.2)⟩, by
    obtain ⟨m, hm⟩ := Module.mem_support_iff'.mp p.2
    refine Module.mem_support_iff'.mpr ⟨m, fun s hs => ?_⟩
    obtain ⟨r, rfl⟩ := hf s
    rw [algebraMap_smul]
    exact hm r fun hr => hs (Ideal.mem_map_of_mem _ hr)⟩
  left_inv q := Subtype.ext <| PrimeSpectrum.ext <| Ideal.map_comap_of_surjective _ hf _
  right_inv p := Subtype.ext <| PrimeSpectrum.ext <| by
    change Ideal.comap _ (Ideal.map _ _) = _
    rw [Ideal.comap_map_of_surjective' _ hf, sup_eq_left.mpr (ker_le_of_mem_support p.2)]
  map_rel_iff' {q₁ q₂} := Ideal.comap_le_comap_iff_of_surjective _ hf q₁.1.asIdeal q₂.1.asIdeal

/-- Along a surjection of local rings `R → S`, an `S`-module is Cohen–Macaulay over `S` if and
only if it is over `R`. -/
private lemma isCMModule_iff_of_surjective : IsCMModule S M ↔ IsCMModule R M := by
  unfold IsCMModule
  rw [Module.supportDim, Module.supportDim, Order.krullDim_eq_of_orderIso (supportOrderIso hf)]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨ys, hys, hlen⟩
    refine ⟨ys.map (Function.surjInv hf), ?_, by simpa using hlen⟩
    rwa [← isRegularSequence_map_algebraMap_iff hf, List.map_map,
      show algebraMap R S ∘ Function.surjInv hf = id from funext (Function.surjInv_eq hf),
      List.map_id]
  · rintro ⟨xs, hxs, hlen⟩
    exact ⟨xs.map (algebraMap R S), (isRegularSequence_map_algebraMap_iff hf xs).mpr hxs,
      by simpa using hlen⟩

end BaseChange

/-- Let `(R, 𝔪)` be a Noetherian local ring, `N` a finite `R`-module and `x ∈ 𝔪` regular on `N`.
Then `N/xN` is Cohen–Macaulay if and only if `N` is. Moreover, being Cohen–Macaulay does not
depend on whether a module is regarded over `R` or over a local quotient `S` of `R` (such as
`R/xR`, over which `N/xN` is a module). -/
@[mmp "lem_mmp_foundation_km5a_cm_regular_element_quotient"]
public theorem isCMModule_quotSMulTop_iff {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N] {x : R}
    (hx : x ∈ IsLocalRing.maximalIdeal R) (hreg : IsSMulRegular N x) :
    (IsCMModule R (QuotSMulTop x N) ↔ IsCMModule R N) ∧
      ∀ (S : Type*) [CommRing S] [IsLocalRing S] [Algebra R S],
        Function.Surjective (algebraMap R S) →
        ∀ (M : Type*) [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M],
          (IsCMModule S M ↔ IsCMModule R M) := by
  refine ⟨?_, fun S _ _ _ hf M _ _ _ _ => isCMModule_iff_of_surjective hf⟩
  rcases subsingleton_or_nontrivial N with hN | hN
  · exact iff_of_true isCMModule_of_subsingleton isCMModule_of_subsingleton
  · have := nontrivial_quotSMulTop_of_mem_maximalIdeal N hx
    rw [(isCMModule_iff_localDepth_eq_supportDim_and_isCohenMacaulayModule R N).2,
      (isCMModule_iff_localDepth_eq_supportDim_and_isCohenMacaulayModule R _).2]
    exact (isCohenMacaulayModule_iff_isCohenMacaulayModule_quotSMulTop hx hreg).symm

end MMP.Mori

/-! ### Semicontinuity of fibre cohomology -/

namespace MMP

/-- **Semicontinuity of fibre cohomology.** For a projective morphism `f : Z ⟶ T` of Noetherian
schemes and a coherent `𝒪_Z`-module `𝓕` flat over `T`, the function
`t ↦ dim_{κ(t)} H^i(Z_t, 𝓕_t)` is upper semicontinuous on `T` for every `i`. -/
@[mmp "lem_mmp_foundation_laz_coherent_cohomology_semicontinuity"]
public theorem upperSemicontinuous_finrank_cohomologyOverField_fiber
    {Z T : Scheme.{u}} (f : Z ⟶ T) (hf : IsProjective f) [IsNoetherian Z] [IsNoetherian T]
    (F : Z.Modules) [F.IsCoherent] (hF : IsFlatOver f.toLRSHom.toShHom F) (i : ℕ) :
    UpperSemicontinuous fun t : T =>
      Module.finrank (T.residueField t)
        (cohomologyOverField (T.residueField t) (f.fiberToSpecResidueField t)
          ((Scheme.Modules.pullback (f.fiberι t)).obj F) i) := by
  have : IsProper f := hf.isProper
  have : IsLocallyNoetherian T := IsNoetherian.toIsLocallyNoetherian
  have hfp : FinitePresentation f := finitePresentation_of_finiteType f
  have : F.IsFinitePresentation := isFinitePresentation_of_isCoherent F
  have h : FibreBetti.IsFlatFamily f F := ⟨hfp, inferInstance, inferInstance, hF⟩
  convert (FibreBetti.fibreBetti_baseChange_upperSemicontinuous_isLocallyConstructible f hfp F
    hF (i : ℤ)).2.1 using 1
  funext t
  exact (ProperFlatFibreEulerCharacteristic.fibreBetti_eq_finrank_cohomologyOverField h t _ _
    (IsPullback.of_hasPullback f (T.fromSpecResidueField t)) i).symm

end MMP
