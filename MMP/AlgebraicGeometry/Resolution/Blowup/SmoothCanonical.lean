module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.OrderAlongExceptional
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
public import MMP.AlgebraicGeometry.Divisor.Canonical.TopFormGenerator
public import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
public import MMP.AlgebraicGeometry.MMP.Abundance.Basic
public import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParameters
public import MMP.AlgebraicGeometry.Morphisms.Smooth.EtaleCoordinateCharts
public import MMP.AlgebraicGeometry.Divisor.PullbackExistence
public import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
public import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCentre
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Integral
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.RegularStalk
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen
public import StacksFrontier.AlgebraicGeometry.Duality.FundamentalClassDeterminantDual
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal

/-!
# The canonical divisor of a smooth blow-up

Let `Y` be a smooth variety of dimension `d` over a field `k`, `Z ⊂ Y` a smooth irreducible closed
subscheme of codimension `c`, `π : V = Bl_Z Y ⟶ Y` the blow-up and `E` its exceptional divisor.
For every nonzero rational top form `σ` on `Y`,

`div_V(π^*σ) = π^*div_Y(σ) + (c - 1)E`.

The coefficients are compared one prime divisor `F` of `V` at a time. Let `σ_A` generate the top
forms at `π(η_F)` and `σ_B` those at `η_F`, with `π^*σ_A = g σ_B`. Writing `σ = a σ_A`, the
coefficient of `F` in `div_V(π^*σ)` is `v_F(π^*a) + v_F(g)`. A local equation `b` of the Cartier
divisor `div_Y(σ)` near `π(η_F)` differs from `a` by a unit of `𝒪_{Y,π(η_F)}` (algebraic Hartogs),
so `v_F(π^*a)` is the coefficient of `F` in `π^*div_Y(σ)`. It remains to see that `v_F(g)` is `0`
for `F ≠ E` and `c - 1` for `F = E`.

* If `F ≠ E`, then `π(η_F) ∉ Z`, and `π` is an isomorphism over `Y ∖ Z`; so `g` is a unit.
* If `F = E`, take local coordinates `x_1, …, x_n` near the generic point of `Z` whose first `c`
  cut out `Z`, and a chart `U_ℓ` of the blow-up containing `η_E`. There `x_i = x_ℓ T_i` for
  `i ≤ c`, `i ≠ ℓ`, so `d x_i = T_i d x_ℓ + x_ℓ d T_i` and
  `π^*(dx_1 ∧ ⋯ ∧ dx_n) = x_ℓ^{c-1} τ`, where `τ` is the same wedge with `d x_i` replaced by
  `d T_i` for these `i`. The chart ring is generated over `𝒪(U)` by the `T_i`, so `τ` generates
  the top forms of the chart; and `x_ℓ` generates the ideal of `E`, a uniformizer at `η_E`.

## Main results

* `MMP.Threefold.Resolution.divisorOfForm_pullbackRationalPluriForms_blowUpToBase`:
  `div_V(π^*σ) = π^*div_Y(σ) + (c - 1)E`.
* `MMP.Threefold.Resolution.ιMulti_D_algebraMap_eq`, `MMP.Threefold.Resolution.span_chartDiffs`:
  the pull-back of `dx_1 ∧ ⋯ ∧ dx_n` to a chart and the generation of the chart differentials.
* `MMP.Threefold.Resolution.ordForm_pullbackRationalPluriForms_eq`: the order of a pulled-back
  form along a prime divisor, through generators of the top forms at the two local rings.
* `MMP.Threefold.Resolution.exists_basis_D_of_isLocalCoordinates`: étale coordinates give a basis
  of the differentials.

## Implementation notes

* The divisor of a form is `MMP.Mori.divisorOfForm`, the pull-back of forms
  `MMP.Mori.pullbackRationalPluriForms` (through the extension of function fields), and the
  pull-back of a Cartier divisor `MMP.Mori.Divisor.pullback`; `div_Y(σ)` is Cartier because `Y`
  is smooth (`MMP.Fourfold.isCartier_of_isSmoothScheme`).
* "Top form" is read as a rational `d`-form for `d = dim Y`. The variety `Y` is only assumed
  integral and quasi-compact, and the codimension `c ≥ 1` (for `c = 1` the formula says
  `div_V(π^*σ) = π^*div_Y(σ)`); the source assumes `c ≥ 2`.
* The centre, the blow-up and the exceptional prime divisor are as in
  `MMP.Resolution.IsSmoothBlowup`, `AlgebraicGeometry.blowUpToBase` and
  `MMP.Resolution.exceptionalPrimeDivisor`; the chart rings are
  `MMP.Resolution.BlowupChartData` with the presentation
  `MMP.Flips.ResolutionInputs.chartPresentation_surjective_and_ker`.

## References

* [R. Hartshorne, *Algebraic geometry*][Har77], II, Exercise 8.5
* [J. Kollár, *Lectures on resolution of singularities*], Notation 3.19
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Threefold.Resolution

section ChartDifferentials

open KaehlerDifferential

/-- Replacing, at each index `i ∈ S`, the vector `v i` by `a i • v ℓ + b i • v i` (with `ℓ ∉ S`)
multiplies the value of an alternating map by `∏ b i`. -/
theorem alternatingMap_apply_ite_smul_add {R M N ι : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] [DecidableEq ι] (f : M [⋀^ι]→ₗ[R] N)
    (v : ι → M) (ℓ : ι) (a b : ι → R) (S : Finset ι) (hℓ : ℓ ∉ S) :
    f (fun i => if i ∈ S then a i • v ℓ + b i • v i else v i) = (∏ i ∈ S, b i) • f v := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert j S hj ih =>
    have hℓS : ℓ ∉ S := fun h => hℓ (Finset.mem_insert_of_mem h)
    have hjℓ : j ≠ ℓ := fun h => hℓ (h ▸ Finset.mem_insert_self j S)
    set w : ι → M := fun i => if i ∈ S then a i • v ℓ + b i • v i else v i with hw
    have hwj : w j = v j := by simp [hw, hj]
    have hwℓ : w ℓ = v ℓ := by simp [hw, hℓS]
    have heq : (fun i => if i ∈ insert j S then a i • v ℓ + b i • v i else v i) =
        Function.update w j (a j • v ℓ + b j • v j) := by
      funext i
      by_cases hij : i = j
      · subst hij; simp
      · simp [hw, Finset.mem_insert, hij]
    rw [heq, f.map_update_add, f.map_update_smul, f.map_update_smul]
    have h0 : f (Function.update w j (v ℓ)) = 0 := by
      refine f.map_eq_zero_of_eq _ (i := j) (j := ℓ) ?_ hjℓ
      rw [Function.update_self, Function.update_of_ne hjℓ.symm, hwℓ]
    have h1 : Function.update w j (v j) = w := by
      rw [← hwj, Function.update_eq_self]
    rw [h0, smul_zero, zero_add, h1, ih hℓS, smul_smul, Finset.prod_insert hj]

variable (k : Type*) {A B : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A]
  [Algebra k B] [Algebra A B] [IsScalarTower k A B] {n : ℕ}

/-- The differentials of a blow-up chart: for `i ∈ S` the differential `dT_i` of the chart
coordinate `T_i = x_i / x_ℓ`, and otherwise the differential of the pull-back of `x_i`. -/
noncomputable def chartDiffs (x : Fin n → A) (S : Finset (Fin n)) (T : Fin n → B) :
    Fin n → Ω[B⁄k] := fun i =>
  if i ∈ S then D k B (T i) else D k B (algebraMap A B (x i))

variable {k} {x : Fin n → A} {S : Finset (Fin n)} {ℓ : Fin n} {T : Fin n → B}

omit [Algebra k A] [IsScalarTower k A B] in
/-- If `x_i = T_i x_ℓ` on the chart for `i ∈ S`, every `d(π^*x_i)` lies in the span of the chart
differentials: `d(π^*x_i) = T_i d(π^*x_ℓ) + π^*x_ℓ dT_i`. -/
theorem D_algebraMap_mem_span (hℓ : ℓ ∉ S)
    (hT : ∀ i ∈ S, algebraMap A B (x i) = T i * algebraMap A B (x ℓ)) (i : Fin n) :
    D k B (algebraMap A B (x i)) ∈ Submodule.span B (Set.range (chartDiffs k x S T)) := by
  have hv : ∀ j, chartDiffs k x S T j ∈ Submodule.span B (Set.range (chartDiffs k x S T)) :=
    fun j => Submodule.subset_span ⟨j, rfl⟩
  by_cases hi : i ∈ S
  · rw [hT i hi, Derivation.leibniz]
    have h1 : chartDiffs k x S T ℓ = D k B (algebraMap A B (x ℓ)) := by simp [chartDiffs, hℓ]
    have h2 : chartDiffs k x S T i = D k B (T i) := by simp [chartDiffs, hi]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (h1 ▸ hv ℓ))
      (Submodule.smul_mem _ _ (h2 ▸ hv i))
  · have h2 : chartDiffs k x S T i = D k B (algebraMap A B (x i)) := by simp [chartDiffs, hi]
    exact h2 ▸ hv i

/-- **The chart differentials span.** If the `dx_i` span `Ω_{A/k}`, `x_i = T_i x_ℓ` in `B` for
`i ∈ S` (with `ℓ ∉ S`), and `B` is generated over `A` by the `T_i`, then the chart differentials
span `Ω_{B/k}`. -/
theorem span_chartDiffs (hspan : Submodule.span A (Set.range (fun i => D k A (x i))) = ⊤)
    (hℓ : ℓ ∉ S) (hT : ∀ i ∈ S, algebraMap A B (x i) = T i * algebraMap A B (x ℓ))
    (hgen : Algebra.adjoin A (T '' S) = ⊤) :
    Submodule.span B (Set.range (chartDiffs k x S T)) = ⊤ := by
  set N := Submodule.span B (Set.range (chartDiffs k x S T)) with hN
  have hA : ∀ a : A, D k B (algebraMap A B a) ∈ N := by
    intro a
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp
      (hspan ▸ Submodule.mem_top : D k A a ∈ _)
    have : D k B (algebraMap A B a) = ∑ i, algebraMap A B (c i) • D k B (algebraMap A B (x i)) := by
      rw [← KaehlerDifferential.map_D k k A B, ← hc, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, KaehlerDifferential.map_D, algebraMap_smul]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (D_algebraMap_mem_span hℓ hT i)
  have hall : ∀ b : B, D k B b ∈ N := by
    intro b
    have hb : b ∈ Algebra.adjoin A (T '' S) := hgen ▸ Algebra.mem_top
    induction hb using Algebra.adjoin_induction with
    | mem t ht =>
      obtain ⟨i, hi, rfl⟩ := ht
      have h2 : chartDiffs k x S T i = D k B (T i) := by simp [chartDiffs, Finset.mem_coe.mp hi]
      exact h2 ▸ Submodule.subset_span ⟨i, rfl⟩
    | algebraMap a => exact hA a
    | add p q _ _ hp hq => rw [map_add]; exact N.add_mem hp hq
    | mul p q _ _ hp hq =>
      rw [Derivation.leibniz]; exact N.add_mem (N.smul_mem _ hq) (N.smul_mem _ hp)
  refine eq_top_iff.mpr ?_
  rw [← KaehlerDifferential.span_range_derivation k B, Submodule.span_le]
  rintro - ⟨b, rfl⟩
  exact hall b

/-- **The pull-back of `dx_1 ∧ ⋯ ∧ dx_n` to a blow-up chart.** If `x_i = T_i x_ℓ` for `i ∈ S`,
with `ℓ ∉ S`, then `d(π^*x_1) ∧ ⋯ ∧ d(π^*x_n) = (π^*x_ℓ)^{|S|}` times the wedge of the chart
differentials. -/
theorem ιMulti_D_algebraMap_eq (hℓ : ℓ ∉ S)
    (hT : ∀ i ∈ S, algebraMap A B (x i) = T i * algebraMap A B (x ℓ)) :
    exteriorPower.ιMulti B n (fun i => D k B (algebraMap A B (x i))) =
      algebraMap A B (x ℓ) ^ S.card • exteriorPower.ιMulti B n (chartDiffs k x S T) := by
  classical
  have h1 : chartDiffs k x S T ℓ = D k B (algebraMap A B (x ℓ)) := by simp [chartDiffs, hℓ]
  have heq : (fun i => D k B (algebraMap A B (x i))) = fun i =>
      if i ∈ S then T i • chartDiffs k x S T ℓ + algebraMap A B (x ℓ) • chartDiffs k x S T i
      else chartDiffs k x S T i := by
    funext i
    by_cases hi : i ∈ S
    · simp only [hi, ite_true, h1]
      rw [hT i hi, Derivation.leibniz]
      simp [chartDiffs, hi, add_comm]
    · simp [chartDiffs, hi]
  rw [heq, alternatingMap_apply_ite_smul_add _ _ _ _ _ _ hℓ, Finset.prod_const]

end ChartDifferentials

section Transfer

variable {k : Type*} [CommRing k] {d : ℕ}
  {K K' : Type*} [Field K] [Field K'] [Algebra k K] [Algebra k K'] [Algebra K K']
  [IsScalarTower k K K']
  {A B : Type*} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B] [Algebra A K]
  [IsScalarTower k A K] [IsFractionRing A K] [Algebra B K'] [IsScalarTower k B K']
  [IsFractionRing B K'] [Algebra A B] [IsScalarTower k A B] [Algebra A K'] [IsScalarTower A B K']
  [IsScalarTower A K K'] [IsScalarTower k A K']
  {σA : ⋀[A]^d Ω[A⁄k]} (hσA : Submodule.span A {σA} = ⊤) (h0A : topFormsMap k A K d σA ≠ 0)
  {σB : ⋀[B]^d Ω[B⁄k]} (hσB : Submodule.span B {σB} = ⊤) (h0B : topFormsMap k B K' d σB ≠ 0)
  {h : B}

include hσA hσB h0B in
/-- If a generator `σ_A` of `Ω^d_{A/k}` maps to `h • σ_B` in `Ω^d_{B/k}`, for a generator `σ_B` and
`h` nonzero in the fraction field `K'` of `B`, then the image of `σ_A` in `Ω^d_{K/k}` is a
pull-back generator for `K → K'`. -/
theorem isPullbackGenerator_of_topFormsMap_eq_smul
    (hrel : topFormsMap k A B d σA = h • σB) (hh : algebraMap B K' h ≠ 0) :
    IsPullbackGenerator K' (topFormsMap k A K d σA) := by
  have hK := span_singleton_topFormsMap (K := K) (nonZeroDivisors A) hσA
  have hK' := span_singleton_topFormsMap (K := K') (nonZeroDivisors B) hσB
  have hcomp : topFormsMap k K K' d (topFormsMap k A K d σA) =
      algebraMap B K' h • topFormsMap k B K' d σB := by
    rw [MMP.Threefold.Mori.Helpers.topFormsMap_comp,
      ← MMP.Threefold.Mori.Helpers.topFormsMap_comp (B := B), hrel, map_smul, algebraMap_smul]
  refine ⟨hK, ?_, ?_⟩
  · rwa [hcomp, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hh)]
  · rw [hcomp]
    exact smul_ne_zero hh h0B

/-- **Coordinates of a pulled-back form.** If a generator `σ_A` of `Ω^d_{A/k}` maps to `h • σ_B`
for a generator `σ_B` of `Ω^d_{B/k}`, then the coordinate of `u^*τ` along `σ_B^{⊗m}` is the image
of the coordinate of `τ` along `σ_A^{⊗m}` times `h^m`. -/
theorem formCoeff_pullbackForms_of_topFormsMap_eq_smul
    (hrel : topFormsMap k A B d σA = h • σB) (hh : algebraMap B K' h ≠ 0) {m : ℤ}
    (τ : PluriForms k K d m) :
    formCoeff B hσB h0B (pullbackForms (K' := K') m τ) =
      algebraMap K K' (formCoeff A hσA h0A τ) * algebraMap B K' h ^ m := by
  have hω := isPullbackGenerator_of_topFormsMap_eq_smul (K := K) hσA hσB h0B hrel hh
  rw [pullbackForms_eq hω, pullbackFormsAlong]
  have hb1 : basisOfSpanSingleton hω.2.1 hω.2.2 () =
      algebraMap B K' h • topFormsBasis B hσB h0B () := by
    rw [basisOfSpanSingleton_apply, topFormsBasis_apply,
      MMP.Threefold.Mori.Helpers.topFormsMap_comp,
      ← MMP.Threefold.Mori.Helpers.topFormsMap_comp (B := B), hrel, map_smul, algebraMap_smul]
  have hb2 : basisOfSpanSingleton hω.1 hω.ne_zero () = (1 : K) • topFormsBasis A hσA h0A () := by
    simp
  rw [ZTensorPower.basis_apply_of_eq_smul hb1, ZTensorPower.basis_repr_of_eq_smul hb2, smul_smul,
    formCoeff_smul]
  have : formCoeff B hσB h0B (ZTensorPower.basis (topFormsBasis B hσB h0B) m ()) = 1 := by
    simp [formCoeff]
  rw [this, mul_one, one_zpow, inv_one, one_mul]
  rfl

end Transfer

section Coordinates

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- **Étale coordinates give a basis of the differentials.** If `x_1, …, x_n` are local
coordinates on an affine open `U` (the morphism `U ⟶ 𝔸^n_k` they define is étale), then
`dx_1, …, dx_n` is a basis of `Ω_{𝒪(U)/k}`. -/
theorem exists_basis_D_of_isLocalCoordinates {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ}
    (x : Fin n → Γ(X, U)) (hx : MMP.Resolution.IsLocalCoordinates sX U x) :
    letI := MMP.Mori.sectionAlgebra sX U
    ∃ b : Module.Basis (Fin n) Γ(X, U) Ω[Γ(X, U)⁄k],
      ∀ i, b i = KaehlerDifferential.D k Γ(X, U) (x i) := by
  have : IsAffine U.toScheme := hU
  set ι := ULift.{u} (Fin n)
  set π := AffineSpace.homOfVector (n := ι) (U.ι ≫ sX) fun i => U.topIso.inv.hom (x i.down)
    with hπ
  have hπe : Etale π := hx
  have H : Etale (π ≫ (AffineSpace.isoOfIsAffine ι (Spec (.of k))).hom) := inferInstance
  rw [HasRingHomProperty.iff_of_isAffine (P := @Etale), Scheme.Hom.comp_appTop,
    AffineSpace.isoOfIsAffine_hom_appTop] at H
  set e := MvPolynomial.eval₂Hom ((AffineSpace ι (Spec (.of k)) ↘ Spec (.of k)).appTop).hom
    (AffineSpace.coord (Spec (.of k)))
  set φ : MvPolynomial ι Γ(Spec (.of k), ⊤) →+* Γ(X, U) :=
    U.topIso.hom.hom.comp (π.appTop.hom.comp e) with hφ
  have hφe : φ.Etale := by
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at H
    have h2 : (π.appTop.hom.comp e) =
        ((π.appTop.hom.comp e).comp
          (Scheme.ΓSpecIso (.of (MvPolynomial ι Γ(Spec (.of k), ⊤)))).hom.hom).comp
          (Scheme.ΓSpecIso (.of (MvPolynomial ι Γ(Spec (.of k), ⊤)))).inv.hom := by
      ext a <;> simp
    refine RingHom.Etale.stableUnderComposition _ _ ?_
      (RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso _))
    rw [h2]
    refine RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso _)) ?_
    simpa [RingHom.comp_assoc] using H
  have hφX : ∀ i, φ (MvPolynomial.X i) = x i.down := by
    intro i
    simp only [φ, e, RingHom.comp_apply, MvPolynomial.eval₂Hom_X', hπ,
      AffineSpace.homOfVector_appTop_coord]
    exact Iso.inv_hom_id_apply U.topIso (x i.down)
  have key : (U.ι ≫ sX).appTop = sX.appLE ⊤ U le_top ≫ U.topIso.inv := by
    rw [Iso.eq_comp_inv, Scheme.Hom.comp_appTop, Scheme.Opens.ι_appTop,
      Scheme.Opens.topIso_hom]
    simp only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    erw [Scheme.Hom.appLE_map, Scheme.Hom.appLE_map]
  have hφC : ∀ r, φ (MvPolynomial.C r) = (sX.appLE ⊤ U le_top).hom r := by
    intro r
    have h1 := congrArg (fun g ↦ g.appTop.hom r) (AffineSpace.homOfVector_over (U.ι ≫ sX)
      (fun i : ι ↦ U.topIso.inv (x i.down)))
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h1
    simp only [φ, e, RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
    rw [← hπ] at h1
    rw [h1]
    simpa only [Scheme.Hom.comp_appTop, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      CommRingCat.hom_comp, RingHom.comp_apply] using
      congrArg (fun g => (g ≫ U.topIso.hom).hom r) key
  let := MMP.Mori.sectionAlgebra sX U
  let algkR : Algebra k Γ(Spec (.of k), ⊤) := (Scheme.ΓSpecIso (.of k)).inv.hom.toAlgebra
  let algPU : Algebra (MvPolynomial ι Γ(Spec (.of k), ⊤)) Γ(X, U) := φ.toAlgebra
  have hsurj : Function.Surjective (algebraMap k Γ(Spec (.of k), ⊤)) :=
    (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.surjective
  have : IsScalarTower k (MvPolynomial ι Γ(Spec (.of k), ⊤)) Γ(X, U) := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    change _ = φ (MvPolynomial.C (algebraMap k Γ(Spec (.of k), ⊤) c))
    rw [hφC]
    rfl
  have : Algebra.FormallyEtale (MvPolynomial ι Γ(Spec (.of k), ⊤)) Γ(X, U) := by
    have : Algebra.Etale (MvPolynomial ι Γ(Spec (.of k), ⊤)) Γ(X, U) := hφe
    infer_instance
  let E := Stacks.RelativeDifferentialStalkMap.kaehlerMapEquivOfSurjective k
    Γ(Spec (.of k), ⊤) (MvPolynomial ι Γ(Spec (.of k), ⊤)) hsurj
  let b0 : Module.Basis ι (MvPolynomial ι Γ(Spec (.of k), ⊤))
      Ω[MvPolynomial ι Γ(Spec (.of k), ⊤)⁄k] :=
    (KaehlerDifferential.mvPolynomialBasis Γ(Spec (.of k), ⊤) ι).map E.symm
  have hb0 : ∀ i, b0 i = KaehlerDifferential.D k _ (MvPolynomial.X i) := by
    intro i
    simp only [b0, Module.Basis.map_apply, KaehlerDifferential.mvPolynomialBasis_apply,
      LinearEquiv.symm_apply_eq]
    exact (Stacks.RelativeDifferentialStalkMap.kaehlerMapEquivOfSurjective_D k _ _ hsurj _).symm
  obtain ⟨b', hb'⟩ := MMP.Flips.ResolutionInputs.exists_basis_kaehler_of_formallyEtale
    (T := Γ(X, U)) b0 MvPolynomial.X hb0
  refine ⟨b'.reindex Equiv.ulift, fun i => ?_⟩
  rw [Module.Basis.reindex_apply, hb']
  change KaehlerDifferential.D k Γ(X, U) (φ (MvPolynomial.X _)) = _
  rw [hφX]
  rfl

/-- On a scheme smooth over `k`, `Ω_{𝒪_{X,p}/k}` is free, of rank the local dimension of `X` at
`p`. -/
theorem exists_basis_kaehler_stalk [Smooth sX] (p : X) :
    letI := stalkAlgebra sX p
    ∃ n : ℕ, Nonempty (Module.Basis (Fin n) (X.presheaf.stalk p) Ω[X.presheaf.stalk p⁄k]) ∧
      topologicalKrullDimAt X p = n := by
  obtain ⟨U, hpU, n, x, hx, -, hdim⟩ := MMP.Flips.ResolutionInputs.exists_isLocalCoordinatesOn sX p
  obtain ⟨W, hW, hpW, hWU⟩ := exists_isAffineOpen_mem_and_subset hpU
  obtain ⟨b, -⟩ := hx ⟨W, hW⟩ hWU
  let := sectionAlgebra sX W
  let := stalkAlgebra sX p
  let : Algebra Γ(X, W) (X.presheaf.stalk p) := X.presheaf.algebra_section_stalk ⟨p, hpW⟩
  have : IsScalarTower k Γ(X, W) (X.presheaf.stalk p) := isScalarTower_section_stalk sX W ⟨p, hpW⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk p) (hW.primeIdealOf ⟨p, hpW⟩).asIdeal :=
    hW.isLocalization_stalk ⟨p, hpW⟩
  have : Algebra.FormallyEtale Γ(X, W) (X.presheaf.stalk p) :=
    Algebra.FormallyEtale.of_isLocalization (hW.primeIdealOf ⟨p, hpW⟩).asIdeal.primeCompl
  refine ⟨n, ⟨(b.baseChange (X.presheaf.stalk p)).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k Γ(X, W) (X.presheaf.stalk p))⟩, hdim⟩

/-- **Generators of the top forms at a point of a smooth variety.** On an integral scheme `X` of
dimension `d` smooth over `k`, `Ω^d_{𝒪_{X,p}/k}` has a generator with nonzero image in
`Ω^d_{k(X)/k}`, for every `p ∈ X`. -/
theorem exists_topForms_generator_stalk [IsIntegral X] [Smooth sX] {d : ℕ}
    (hd : topologicalKrullDim X = d) (p : X) :
    letI := stalkAlgebra sX p
    letI := functionFieldAlgebra sX
    haveI := isScalarTower_stalk_functionField sX p
    ∃ σ : ⋀[X.presheaf.stalk p]^d Ω[X.presheaf.stalk p⁄k],
      Submodule.span (X.presheaf.stalk p) {σ} = ⊤ ∧
      topFormsMap k (X.presheaf.stalk p) X.functionField d σ ≠ 0 := by
  let := stalkAlgebra sX p
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX p
  obtain ⟨n, ⟨b⟩, hn⟩ := exists_basis_kaehler_stalk sX p
  have hnd : n = d := by
    have := (topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k X sX p).trans hn
    rw [hd] at this
    exact_mod_cast this.symm
  have : Module.Free (X.presheaf.stalk p) Ω[X.presheaf.stalk p⁄k] := .of_basis b
  have : Module.Finite (X.presheaf.stalk p) Ω[X.presheaf.stalk p⁄k] := .of_basis b
  exact exists_topForms_generator_of_free
    (by rw [Module.finrank_eq_card_basis b, Fintype.card_fin, hnd])

/-- On an integral scheme of dimension `d` smooth over `k`, `Ω^d_{k(X)/k} ≠ 0`. -/
theorem nontrivial_topForms [IsIntegral X] [Smooth sX] {d : ℕ}
    (hd : topologicalKrullDim X = d) :
    letI := functionFieldAlgebra sX
    Nontrivial (⋀[X.functionField]^d Ω[X.functionField⁄k]) := by
  let := functionFieldAlgebra sX
  obtain ⟨σ, -, h0⟩ := exists_topForms_generator_stalk sX hd (genericPoint X)
  exact ⟨⟨_, 0, h0⟩⟩

end Coordinates

section Stalks

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (f : Y ⟶ X)
  [IsIntegral X] [IsIntegral Y] [IsDominant f]

omit [IsIntegral X] [IsIntegral Y] [IsDominant f] in
/-- The `k`-algebra map `𝒪_{X,f(y)} → 𝒪_{Y,y}` is compatible with the structure maps. -/
theorem isScalarTower_stalkMap (y : Y) :
    letI := stalkAlgebra sX (f y)
    letI := stalkAlgebra (f ≫ sX) y
    letI := (f.stalkMap y).hom.toAlgebra
    IsScalarTower k (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) := by
  let := stalkAlgebra sX (f y)
  let := stalkAlgebra (f ≫ sX) y
  let := (f.stalkMap y).hom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq' ?_
  have h : (Scheme.ΓSpecIso (.of k)).inv ≫ (f ≫ sX).appTop ≫
        Y.presheaf.germ ⊤ y (TopologicalSpace.Opens.mem_top _) =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
        X.presheaf.germ ⊤ (f y) (TopologicalSpace.Opens.mem_top _)) ≫ f.stalkMap y := by
    simp only [Scheme.Hom.comp_appTop, Category.assoc, Scheme.Hom.germ_stalkMap]
    rfl
  exact congrArg CommRingCat.Hom.hom h

variable [IsLocallyNoetherian Y] {d : ℕ} {m : ℤ}

/-- **The order of a pulled-back form along a prime divisor.** Let `f : Y ⟶ X` be dominant,
`F` a prime divisor of `Y`, `σ_A` a generator of `Ω^d` at `f(η_F)` and `σ_B` one at `η_F`, with
`f^♯σ_A = h • σ_B`. Then `ord_F(f^*τ) = v_F(f^*(τ / σ_A^{⊗m})) + m · v_F(h)`. -/
theorem ordForm_pullbackRationalPluriForms_eq (F : MMP.Mori.PrimeDivisor Y)
    {σA : letI := stalkAlgebra sX (f F.genericPoint)
      ⋀[X.presheaf.stalk (f F.genericPoint)]^d Ω[X.presheaf.stalk (f F.genericPoint)⁄k]}
    (hσA : Submodule.span (X.presheaf.stalk (f F.genericPoint)) {σA} = ⊤)
    (h0A : letI := stalkAlgebra sX (f F.genericPoint)
      letI := functionFieldAlgebra sX
      haveI := isScalarTower_stalk_functionField sX (f F.genericPoint)
      topFormsMap k (X.presheaf.stalk (f F.genericPoint)) X.functionField d σA ≠ 0)
    {σB : letI := stalkAlgebra (f ≫ sX) F.genericPoint
      ⋀[F.localRing]^d Ω[F.localRing⁄k]}
    (hσB : Submodule.span F.localRing {σB} = ⊤)
    (h0B : letI := stalkAlgebra (f ≫ sX) F.genericPoint
      letI := functionFieldAlgebra (f ≫ sX)
      haveI := isScalarTower_stalk_functionField (f ≫ sX) F.genericPoint
      topFormsMap k F.localRing Y.functionField d σB ≠ 0)
    (h : F.localRing)
    (hrel : letI := stalkAlgebra sX (f F.genericPoint)
      letI := stalkAlgebra (f ≫ sX) F.genericPoint
      letI := (f.stalkMap F.genericPoint).hom.toAlgebra
      haveI := isScalarTower_stalkMap sX f F.genericPoint
      topFormsMap k (X.presheaf.stalk (f F.genericPoint)) F.localRing d σA = h • σB)
    (hh : algebraMap F.localRing Y.functionField h ≠ 0)
    {τ : RationalPluriForms sX d m} (hτ : τ ≠ 0) :
    letI := stalkAlgebra sX (f F.genericPoint)
    letI := functionFieldAlgebra sX
    haveI := isScalarTower_stalk_functionField sX (f F.genericPoint)
    F.ordForm (pullbackRationalPluriForms sX f τ) =
      Y.ord (functionFieldMap f
          (formCoeff (k := k) (X.presheaf.stalk (f F.genericPoint)) hσA h0A τ))
        F.genericPoint + m * Y.ord (algebraMap F.localRing Y.functionField h) F.genericPoint := by
  let := stalkAlgebra sX (f F.genericPoint)
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX (f F.genericPoint)
  let := stalkAlgebra (f ≫ sX) F.genericPoint
  let := functionFieldAlgebra (f ≫ sX)
  have := isScalarTower_stalk_functionField (f ≫ sX) F.genericPoint
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  let := (f.stalkMap F.genericPoint).hom.toAlgebra
  have := isScalarTower_stalkMap sX f F.genericPoint
  let : Algebra (X.presheaf.stalk (f F.genericPoint)) Y.functionField :=
    ((algebraMap X.functionField Y.functionField).comp
      (algebraMap (X.presheaf.stalk (f F.genericPoint)) X.functionField)).toAlgebra
  have : IsScalarTower (X.presheaf.stalk (f F.genericPoint)) X.functionField Y.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower (X.presheaf.stalk (f F.genericPoint)) F.localRing Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun a =>
      functionFieldMap_algebraMap_stalk f F.genericPoint a
  have : IsScalarTower k (X.presheaf.stalk (f F.genericPoint)) Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => by
      rw [IsScalarTower.algebraMap_apply k X.functionField Y.functionField,
        IsScalarTower.algebraMap_apply k (X.presheaf.stalk (f F.genericPoint)) X.functionField]
      rfl
  have hc := formCoeff_pullbackForms_of_topFormsMap_eq_smul (K := X.functionField)
    (K' := Y.functionField) hσA h0A hσB h0B hrel hh τ
  have hne : formCoeff (k := k) (X.presheaf.stalk (f F.genericPoint)) hσA h0A τ ≠ 0 :=
    fun h0 => hτ ((formCoeff_eq_zero_iff hσA h0A τ).mp h0)
  rw [F.ordForm_eq _ hσB h0B]
  change Y.ord (formCoeff F.localRing hσB h0B
    (pullbackForms (K := X.functionField) (K' := Y.functionField) m τ)) F.genericPoint = _
  rw [hc, Scheme.ord_mul ((map_ne_zero _).mpr hne) (zpow_ne_zero _ hh),
    ord_zpow _ hh]
  rfl

end Stalks

section Specializes

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
  [IsLocallyNoetherian X] {d : ℕ} {m : ℤ}

omit [IsIntegral X] [IsLocallyNoetherian X] in
/-- The specialization map of stalks is `k`-linear. -/
theorem isScalarTower_stalkSpecializes {x' x : X} (hs : x' ⤳ x) :
    letI := stalkAlgebra sX x
    letI := stalkAlgebra sX x'
    letI := (X.presheaf.stalkSpecializes hs).hom.toAlgebra
    IsScalarTower k (X.presheaf.stalk x) (X.presheaf.stalk x') := by
  let := stalkAlgebra sX x
  let := stalkAlgebra sX x'
  let := (X.presheaf.stalkSpecializes hs).hom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq' ?_
  have h : (Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
        X.presheaf.germ ⊤ x' (TopologicalSpace.Opens.mem_top _) =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
        X.presheaf.germ ⊤ x (TopologicalSpace.Opens.mem_top _)) ≫
          X.presheaf.stalkSpecializes hs := by
    simp
  exact congrArg CommRingCat.Hom.hom h

/-- The order along a prime divisor `Γ` through `x` of a form is read off a generator of the top
forms at `x`. -/
theorem ordForm_eq_ord_formCoeff (x : X) (Γ : MMP.Mori.PrimeDivisor X) (hx : x ∈ Γ.support)
    {σ : letI := stalkAlgebra sX x
      ⋀[X.presheaf.stalk x]^d Ω[X.presheaf.stalk x⁄k]}
    (hσ : Submodule.span (X.presheaf.stalk x) {σ} = ⊤)
    (h0 : letI := stalkAlgebra sX x
      letI := functionFieldAlgebra sX
      haveI := isScalarTower_stalk_functionField sX x
      topFormsMap k (X.presheaf.stalk x) X.functionField d σ ≠ 0)
    (τ : RationalPluriForms sX d m) :
    letI := stalkAlgebra sX x
    letI := functionFieldAlgebra sX
    haveI := isScalarTower_stalk_functionField sX x
    Γ.ordForm τ = X.ord (formCoeff (k := k) (X.presheaf.stalk x) hσ h0 τ) Γ.genericPoint := by
  let := stalkAlgebra sX x
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX x
  let := stalkAlgebra sX Γ.genericPoint
  have := isScalarTower_stalk_functionField sX Γ.genericPoint
  have hs : Γ.genericPoint ⤳ x := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hx
    exact specializes_iff_mem_closure.mpr hx
  let := (X.presheaf.stalkSpecializes hs).hom.toAlgebra
  have := isScalarTower_stalkSpecializes sX hs
  have hloc := MMP.Intersection.isLocalization_stalkSpecializes hs
  have : IsScalarTower (X.presheaf.stalk x) Γ.localRing X.functionField :=
    IsScalarTower.of_algebraMap_eq fun a => (algebraMap_stalkSpecializes hs a).symm
  have hσ' := span_singleton_topFormsMap (K := Γ.localRing) (d := d)
    ((IsLocalRing.maximalIdeal Γ.localRing).comap (X.presheaf.stalkSpecializes hs).hom).primeCompl
    hσ
  have hcomp : topFormsMap k Γ.localRing X.functionField d
      (topFormsMap k (X.presheaf.stalk x) Γ.localRing d σ) =
      topFormsMap k (X.presheaf.stalk x) X.functionField d σ :=
    MMP.Threefold.Mori.Helpers.topFormsMap_comp σ
  have h0' : topFormsMap k Γ.localRing X.functionField d
      (topFormsMap k (X.presheaf.stalk x) Γ.localRing d σ) ≠ 0 := hcomp ▸ h0
  rw [Γ.ordForm_eq _ hσ' h0']
  congr 1
  unfold formCoeff
  have hb : topFormsBasis Γ.localRing hσ' h0' () = (1 : X.functionField) •
      topFormsBasis (X.presheaf.stalk x) hσ h0 () := by
    rw [topFormsBasis_apply, topFormsBasis_apply, one_smul, hcomp]
  exact (ZTensorPower.basis_repr_of_eq_smul hb m τ).trans (by rw [one_zpow, inv_one, one_mul])

end Specializes

section BlowUp

variable {k : Type u} [Field k]

/-- A morphism smooth at every point is smooth. -/
theorem smooth_of_isSmoothScheme {X S : Scheme.{u}} {f : X ⟶ S}
    (h : MMP.Mori.IsSmoothScheme f) : Smooth f := by
  have : IsZariskiLocalAtSource @Smooth := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @Smooth)
    (fun U : {U : X.Opens // Smooth (U.ι ≫ f)} => U.1) ?_ fun U => U.2
  rw [← h, MMP.Mori.smoothLocus, sSup_eq_iSup']
  rfl

open MMP.Resolution

variable {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (I : Y.IdealSheafData)

/-- A centre of positive codimension is not everything. -/
theorem compl_support_nonempty (hirr : IsIrreducible (I.support : Set Y))
    (hc : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y)) :
    (I.supportᶜ : Set Y).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at hne
  have h0 : codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y) = 0 :=
    Order.coheight_eq_zero.mpr fun b _ => fun x _ => by
      change x ∈ (I.support : Set Y); rw [hne]; trivial
  rw [h0] at hc
  exact absurd hc (by decide)

/-- The ideal of a centre of positive codimension is nonzero. -/
theorem ne_bot_of_one_le_codimension (hirr : IsIrreducible (I.support : Set Y))
    (hc : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y)) :
    I ≠ ⊥ := by
  rintro rfl
  obtain ⟨y, hy⟩ := compl_support_nonempty _ hirr hc
  exact hy (by simp)

/-- The blow-up of an irreducible scheme along a centre of positive codimension is dominant: it is
an isomorphism over the dense open complement of the centre. -/
theorem isDominant_blowUpToBase [IrreducibleSpace Y] (hirr : IsIrreducible (I.support : Set Y))
    (hc : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y)) :
    IsDominant (blowUpToBase I) := by
  have hiso := isIso_blowUp_restrict_compl_support I
  set W : Y.Opens := ⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩
  have hsub : (W : Set Y) ⊆ Set.range (blowUpToBase I) := by
    intro y hy
    obtain ⟨x, hx⟩ := (asIso (blowUpToBase I ∣_ W)).hom.homeomorph.surjective ⟨y, hy⟩
    refine ⟨x.1, ?_⟩
    simpa [morphismRestrict_base_coe] using congrArg Subtype.val hx
  have hdense : Dense (W : Set Y) :=
    W.isOpen.dense (compl_support_nonempty I hirr hc)
  exact ⟨hdense.mono hsub⟩

/-- The blow-up of an integral scheme along a centre of positive codimension is integral. -/
theorem isIntegral_blowUp_of_one_le_codimension [IsIntegral Y]
    (hirr : IsIrreducible (I.support : Set Y))
    (hc : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y)) :
    IsIntegral (blowUp I) :=
  isIntegral_blowUp I (ne_bot_of_one_le_codimension I hirr hc)

/-- The blow-up of an integral scheme along a centre of positive codimension is birational. -/
theorem isBirationalMorphism_blowUpToBase [IsIntegral Y] (hirr : IsIrreducible (I.support : Set Y))
    (hc : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y)) :
    haveI := isIntegral_blowUp_of_one_le_codimension I hirr hc
    IsBirationalMorphism (blowUpToBase I) := by
  have := isIntegral_blowUp_of_one_le_codimension I hirr hc
  have hiso := isIso_blowUp_restrict_compl_support I
  set W : Y.Opens := ⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩
  obtain ⟨y, hy⟩ := compl_support_nonempty I hirr hc
  obtain ⟨x, -⟩ := (asIso (blowUpToBase I ∣_ W)).hom.homeomorph.surjective ⟨y, hy⟩
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE (blowUpToBase I) (blowUpToBase I ⁻¹ᵁ W) W
    ⟨x.1, x.2⟩ ⟨y, hy⟩ le_rfl ?_
  rwa [Scheme.Hom.resLE_eq_morphismRestrict]

/-- A smooth blow-up of a variety of dimension `d` has dimension `d`. -/
theorem topologicalKrullDim_blowUp [IsIntegral Y] (h : IsSmoothBlowup sY I)
    (hirr : IsIrreducible (I.support : Set Y))
    (hc : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y)) {d : ℕ}
    (hd : topologicalKrullDim Y = d) : topologicalKrullDim (blowUp I) = d := by
  have : Smooth sY := smooth_of_isSmoothScheme h.1
  have := isIntegral_blowUp_of_one_le_codimension I hirr hc
  have := isDominant_blowUpToBase I hirr hc
  have := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sY I h).1
  have hbij := (isBirationalMorphism_blowUpToBase I hirr hc).functionFieldMap_bijective
  have h1 := toENat_trdeg_functionField (sX := sY)
  have h2 := toENat_trdeg_functionField (sX := blowUpToBase I ≫ sY)
  rw [← h2, ← trdeg_functionField_eq_of_bijective sY (blowUpToBase I) hbij, h1, hd]

/-- The generic point of a prime divisor lies on no other prime divisor. -/
theorem genericPoint_notMem_support_of_ne {X : Scheme.{u}} {F G : MMP.Mori.PrimeDivisor X}
    (hFG : F ≠ G) : F.genericPoint ∉ G.support := by
  intro hF
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hF
  have hle : F.genericPoint ≤ G.genericPoint := specializes_iff_mem_closure.mpr hF
  have hlt : F.genericPoint < G.genericPoint := lt_of_le_not_ge hle fun h' =>
    hFG (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (Specializes.antisymm (show F.genericPoint ⤳ G.genericPoint from h')
        (show G.genericPoint ⤳ F.genericPoint from hle)).eq)
  have h2 := Order.coheight_add_one_le hlt
  rw [MMP.Mori.PrimeDivisor.coheight_genericPoint, MMP.Mori.PrimeDivisor.coheight_genericPoint]
    at h2
  exact absurd h2 (by decide)

/-- **Away from the exceptional divisor.** For a prime divisor `F ≠ E` of the blow-up, `π` is a
local isomorphism at `η_F`, so a generator of the top forms at `π(η_F)` pulls back to a generator
at `η_F`. -/
theorem exists_topForms_rel_of_ne (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] (h : IsSmoothBlowup sY I)
    (hirr : IsIrreducible (I.support : Set Y))
    (hc : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y))
    {d : ℕ} (hd : topologicalKrullDim Y = d) :
    haveI := isIntegral_blowUp_of_one_le_codimension I hirr hc
    haveI := isDominant_blowUpToBase I hirr hc
    haveI := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sY I h).1
    haveI : IsLocallyNoetherian (blowUp I) :=
      isLocallyNoetherian_of_smooth (blowUpToBase I ≫ sY)
    ∀ F : MMP.Mori.PrimeDivisor (blowUp I), F ≠ exceptionalPrimeDivisor sY I h hirr hc →
    letI := stalkAlgebra sY (blowUpToBase I F.genericPoint)
    letI := functionFieldAlgebra sY
    haveI := isScalarTower_stalk_functionField sY (blowUpToBase I F.genericPoint)
    letI := stalkAlgebra (blowUpToBase I ≫ sY) F.genericPoint
    letI := functionFieldAlgebra (blowUpToBase I ≫ sY)
    haveI := isScalarTower_stalk_functionField (blowUpToBase I ≫ sY) F.genericPoint
    letI := ((blowUpToBase I).stalkMap F.genericPoint).hom.toAlgebra
    haveI := isScalarTower_stalkMap sY (blowUpToBase I) F.genericPoint
    ∃ (σA : ⋀[Y.presheaf.stalk (blowUpToBase I F.genericPoint)]^d
        Ω[Y.presheaf.stalk (blowUpToBase I F.genericPoint)⁄k])
      (_ : Submodule.span (Y.presheaf.stalk (blowUpToBase I F.genericPoint)) {σA} = ⊤)
      (_ : topFormsMap k (Y.presheaf.stalk (blowUpToBase I F.genericPoint)) Y.functionField d
        σA ≠ 0)
      (σB : ⋀[F.localRing]^d Ω[F.localRing⁄k]) (_ : Submodule.span F.localRing {σB} = ⊤)
      (_ : topFormsMap k F.localRing (blowUp I).functionField d σB ≠ 0) (g : F.localRing),
      topFormsMap k (Y.presheaf.stalk (blowUpToBase I F.genericPoint)) F.localRing d σA = g • σB ∧
      algebraMap F.localRing (blowUp I).functionField g ≠ 0 ∧
      (blowUp I).ord (algebraMap F.localRing (blowUp I).functionField g) F.genericPoint = 0 := by
  have : Smooth sY := smooth_of_isSmoothScheme h.1
  have := isIntegral_blowUp_of_one_le_codimension I hirr hc
  have := isDominant_blowUpToBase I hirr hc
  have := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sY I h).1
  have : IsLocallyNoetherian (blowUp I) := isLocallyNoetherian_of_smooth (blowUpToBase I ≫ sY)
  intro F hFE
  let := stalkAlgebra sY (blowUpToBase I F.genericPoint)
  let := functionFieldAlgebra sY
  have := isScalarTower_stalk_functionField sY (blowUpToBase I F.genericPoint)
  let := stalkAlgebra (blowUpToBase I ≫ sY) F.genericPoint
  let := functionFieldAlgebra (blowUpToBase I ≫ sY)
  have := isScalarTower_stalk_functionField (blowUpToBase I ≫ sY) F.genericPoint
  let := ((blowUpToBase I).stalkMap F.genericPoint).hom.toAlgebra
  have := isScalarTower_stalkMap sY (blowUpToBase I) F.genericPoint
  -- `π` is an isomorphism near `η_F`
  have hFE' := genericPoint_notMem_support_of_ne hFE
  have hηW : F.genericPoint ∈ blowUpToBase I ⁻¹ᵁ
      (⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩ : Y.Opens) := by
    intro hmem
    apply hFE'
    change F.genericPoint ∈ ((exceptionalIdeal I).support : Set (blowUp I))
    rwa [exceptionalIdeal, Scheme.IdealSheafData.support_comap]
  have hiso := isIso_blowUp_restrict_compl_support I
  have key : ∀ {A B : Scheme.{u}} (g : A ⟶ B) [IsIso g] (a : A), IsIso (g.stalkMap a) :=
    fun _ _ _ => inferInstance
  have hstalk : IsIso ((blowUpToBase I).stalkMap F.genericPoint) :=
    ((MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff
      (morphismRestrictStalkMap (blowUpToBase I) _ ⟨F.genericPoint, hηW⟩)).mp
      (key _ _)
  have hbij : Function.Bijective
      (algebraMap (Y.presheaf.stalk (blowUpToBase I F.genericPoint)) F.localRing) :=
    (ConcreteCategory.isIso_iff_bijective _).mp hstalk
  obtain ⟨σA, hσA, h0A⟩ := exists_topForms_generator_stalk sY hd (blowUpToBase I F.genericPoint)
  have : IsLocalization (⊥ : Submonoid (Y.presheaf.stalk (blowUpToBase I F.genericPoint)))
      F.localRing := by
    let e : Y.presheaf.stalk (blowUpToBase I F.genericPoint) ≃ₐ[_] F.localRing :=
      AlgEquiv.ofBijective (Algebra.ofId _ _) hbij
    exact (IsLocalization.isLocalization_iff_of_algEquiv (⊥ : Submonoid _) e).mp
      (IsLocalization.self (M := ⊥) (fun x hx => by
        rw [Submonoid.mem_bot.mp hx]
        exact isUnit_one))
  have hσB := span_singleton_topFormsMap (K := F.localRing) (d := d) (⊥ : Submonoid _) hσA
  obtain ⟨σ', -, h0'⟩ := exists_topForms_generator_stalk (blowUpToBase I ≫ sY)
    (topologicalKrullDim_blowUp sY I h hirr hc hd) F.genericPoint
  have : Nontrivial (⋀[(blowUp I).functionField]^d Ω[(blowUp I).functionField⁄k]) :=
    ⟨⟨_, 0, h0'⟩⟩
  refine ⟨σA, hσA, h0A, _, hσB, topFormsMap_ne_zero_of_span_eq_top hσB, 1, by rw [one_smul],
    by simp, by simp⟩

/-- **Adapted coordinates at the generic point of the centre.** For a smooth irreducible centre
`Z = V(I)` of codimension `c` in a smooth `Y`, the local ring of `Y` at the generic point `η` of
`Z` has dimension `c`, and there are local coordinates `x_1, …, x_n` on an affine open `U ∋ η`
whose first `c` cut out `Z ∩ U`. -/
theorem exists_isLocalCoordinates_genericPoint (sY : Y ⟶ Spec (.of k)) (h : IsSmoothBlowup sY I)
    (hirr : IsIrreducible (I.support : Set Y)) {c : ℕ}
    (hc : (c : ℕ∞) = codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y)) :
    haveI := isIntegral_subscheme_of_isIrreducible sY I h.2 hirr
    ringKrullDim (Y.presheaf.stalk (I.subschemeι (genericPoint I.subscheme))) = c ∧
    ∃ (U : Y.Opens) (_ : IsAffineOpen U) (_ : I.subschemeι (genericPoint I.subscheme) ∈ U)
      (n : ℕ) (x : Fin n → Γ(Y, U)), IsLocalCoordinates sY U x ∧
        Bridges.IsCutOutByFirst I U x c := by
  have := isIntegral_subscheme_of_isIrreducible sY I h.2 hirr
  have : Smooth sY := smooth_of_isSmoothScheme h.1
  have : Smooth (I.subschemeι ≫ sY) := smooth_of_isSmoothScheme h.2
  set z := genericPoint I.subscheme
  have hcl := closure_subschemeι_genericPoint I
  have heq : (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y) =
      IrreducibleCloseds.closureSingleton (I.subschemeι z) := by
    ext1; exact hcl.symm
  have hdim : ringKrullDim (Y.presheaf.stalk (I.subschemeι z)) = c := by
    have h2 : (c : ℕ∞) = Order.coheight (I.subschemeι z) := by
      rw [hc, heq, Stacks.Divisors.PrimeDivisor.codimension_closureSingleton]
    rw [ringKrullDim_stalk_eq_coheight, ← h2]
    rfl
  have hdimZ : ringKrullDim (I.subscheme.presheaf.stalk z) = 0 :=
    ringKrullDim_eq_zero_of_field (I.subscheme.functionField)
  have hc' : topologicalKrullDimAt Y (I.subschemeι z) =
      topologicalKrullDimAt I.subscheme z + (c : WithBot ℕ∞) := by
    rw [topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k Y sY,
      topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k I.subscheme (I.subschemeι ≫ sY),
      ← trdeg_residueField_of_surjectiveOnStalks k sY I.subschemeι z, hdim, hdimZ, add_zero]
  obtain ⟨U, hU, hzU, x, hx, hcut⟩ := Bridges.exists_isLocalCoordinates_adapted sY I z hc'
  exact ⟨hdim, U, hU, hzU, _, x, hx, hcut⟩

open MMP.Flips.ResolutionInputs in
/-- **The pull-back of the coordinate top form on a blow-up chart.** -/
theorem exists_topForms_rel_of_chart (sY : Y ⟶ Spec (.of k)) [Smooth sY] [IsIntegral Y]
    [IsIntegral (blowUp I)] [IsDominant (blowUpToBase I)] [Smooth (blowUpToBase I ≫ sY)]
    {d : ℕ} (hdY : topologicalKrullDim Y = d) (hdV : topologicalKrullDim (blowUp I) = d)
    (cd : BlowupChartData I) (hU : IsAffineOpen cd.U) {n : ℕ} (x : Fin n → Γ(Y, cd.U))
    (hx : IsLocalCoordinates sY cd.U x) (hrn : cd.r ≤ n) (hcx : ∀ i, cd.x i = x (Fin.castLE hrn i))
    (ℓ : Fin cd.r) (F : MMP.Mori.PrimeDivisor (blowUp I)) (hF : F.genericPoint ∈ cd.chart ℓ) :
    letI := stalkAlgebra sY (blowUpToBase I F.genericPoint)
    letI := functionFieldAlgebra sY
    haveI := isScalarTower_stalk_functionField sY (blowUpToBase I F.genericPoint)
    letI := stalkAlgebra (blowUpToBase I ≫ sY) F.genericPoint
    letI := functionFieldAlgebra (blowUpToBase I ≫ sY)
    haveI := isScalarTower_stalk_functionField (blowUpToBase I ≫ sY) F.genericPoint
    letI := ((blowUpToBase I).stalkMap F.genericPoint).hom.toAlgebra
    haveI := isScalarTower_stalkMap sY (blowUpToBase I) F.genericPoint
    ∃ (σA : ⋀[Y.presheaf.stalk (blowUpToBase I F.genericPoint)]^d
        Ω[Y.presheaf.stalk (blowUpToBase I F.genericPoint)⁄k])
      (_ : Submodule.span (Y.presheaf.stalk (blowUpToBase I F.genericPoint)) {σA} = ⊤)
      (_ : topFormsMap k (Y.presheaf.stalk (blowUpToBase I F.genericPoint)) Y.functionField d
        σA ≠ 0)
      (σB : ⋀[F.localRing]^d Ω[F.localRing⁄k]) (_ : Submodule.span F.localRing {σB} = ⊤)
      (_ : topFormsMap k F.localRing (blowUp I).functionField d σB ≠ 0),
      topFormsMap k (Y.presheaf.stalk (blowUpToBase I F.genericPoint)) F.localRing d σA =
        ((blowUp I).presheaf.germ (cd.chart ℓ) F.genericPoint hF
          (cd.chartPullback ℓ (cd.x ℓ))) ^ (cd.r - 1) • σB := by
  classical
  -- notation
  have hyU : blowUpToBase I F.genericPoint ∈ cd.U := cd.chart_le ℓ hF
  let := stalkAlgebra sY (blowUpToBase I F.genericPoint)
  let := functionFieldAlgebra sY
  have := isScalarTower_stalk_functionField sY (blowUpToBase I F.genericPoint)
  let := stalkAlgebra (blowUpToBase I ≫ sY) F.genericPoint
  let := functionFieldAlgebra (blowUpToBase I ≫ sY)
  have := isScalarTower_stalk_functionField (blowUpToBase I ≫ sY) F.genericPoint
  let := ((blowUpToBase I).stalkMap F.genericPoint).hom.toAlgebra
  have := isScalarTower_stalkMap sY (blowUpToBase I) F.genericPoint
  let := sectionAlgebra sY cd.U
  let := sectionAlgebra (blowUpToBase I ≫ sY) (cd.chart ℓ)
  let algAB0 : Algebra Γ(Y, cd.U) Γ(blowUp I, cd.chart ℓ) := (chartPullbackHom cd ℓ).toAlgebra
  have : IsScalarTower k Γ(Y, cd.U) Γ(blowUp I, cd.chart ℓ) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    have h1 := Scheme.Hom.appLE_comp_appLE (blowUpToBase I) sY ⊤ cd.U (cd.chart ℓ) (by simp)
      (cd.chart_le ℓ)
    exact (congrArg (fun t => ((Scheme.ΓSpecIso (.of k)).inv ≫ t).hom) h1).symm
  let : Algebra Γ(Y, cd.U) (Y.presheaf.stalk (blowUpToBase I F.genericPoint)) :=
    Y.presheaf.algebra_section_stalk ⟨_, hyU⟩
  have : IsScalarTower k Γ(Y, cd.U) (Y.presheaf.stalk (blowUpToBase I F.genericPoint)) :=
    isScalarTower_section_stalk sY cd.U ⟨_, hyU⟩
  let : Algebra Γ(blowUp I, cd.chart ℓ) F.localRing :=
    (blowUp I).presheaf.algebra_section_stalk ⟨_, hF⟩
  have : IsScalarTower k Γ(blowUp I, cd.chart ℓ) F.localRing :=
    isScalarTower_section_stalk (blowUpToBase I ≫ sY) (cd.chart ℓ) ⟨_, hF⟩
  let : Algebra Γ(Y, cd.U) F.localRing :=
    ((algebraMap (Y.presheaf.stalk (blowUpToBase I F.genericPoint)) F.localRing).comp
      (algebraMap Γ(Y, cd.U) (Y.presheaf.stalk (blowUpToBase I F.genericPoint)))).toAlgebra
  have : IsScalarTower Γ(Y, cd.U) (Y.presheaf.stalk (blowUpToBase I F.genericPoint)) F.localRing :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Γ(Y, cd.U) Γ(blowUp I, cd.chart ℓ) F.localRing :=
    IsScalarTower.of_algebraMap_eq fun a => (cd.stalkMap_germ ℓ hF a)
  have : IsScalarTower k Γ(Y, cd.U) F.localRing :=
    IsScalarTower.of_algebraMap_eq fun c => by
      rw [IsScalarTower.algebraMap_apply k (Y.presheaf.stalk (blowUpToBase I F.genericPoint))
        F.localRing c, IsScalarTower.algebraMap_apply k Γ(Y, cd.U)
        (Y.presheaf.stalk (blowUpToBase I F.genericPoint)) c]
      rfl
  -- the differentials on `U`
  obtain ⟨b, hb⟩ := exists_basis_D_of_isLocalCoordinates sY hU x hx
  have hnd : n = d := by
    have : IsLocalization.AtPrime (Y.presheaf.stalk (blowUpToBase I F.genericPoint))
        (hU.primeIdealOf ⟨_, hyU⟩).asIdeal := hU.isLocalization_stalk ⟨_, hyU⟩
    have : Algebra.FormallyEtale Γ(Y, cd.U) (Y.presheaf.stalk (blowUpToBase I F.genericPoint)) :=
      Algebra.FormallyEtale.of_isLocalization (hU.primeIdealOf ⟨_, hyU⟩).asIdeal.primeCompl
    let bA := (b.baseChange (Y.presheaf.stalk (blowUpToBase I F.genericPoint))).map
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k Γ(Y, cd.U)
        (Y.presheaf.stalk (blowUpToBase I F.genericPoint)))
    obtain ⟨n', ⟨b'⟩, hn'⟩ := exists_basis_kaehler_stalk sY (blowUpToBase I F.genericPoint)
    have h1 := (topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k Y sY _).trans hn'
    rw [hdY] at h1
    have h2 : n' = d := by exact_mod_cast h1.symm
    have h3 := (Module.finrank_eq_card_basis bA).symm.trans (Module.finrank_eq_card_basis b')
    simp only [Fintype.card_fin] at h3
    omega
  subst hnd
  -- the coordinate top form on `U` and its germ at `π(ξ)`
  have hspanD : Submodule.span Γ(Y, cd.U)
      (Set.range fun i => KaehlerDifferential.D k Γ(Y, cd.U) (x i)) = ⊤ := by
    rw [← b.span_eq]
    congr 1
    ext w
    simp [hb]
  let σU := exteriorPower.ιMulti Γ(Y, cd.U) n (fun i => KaehlerDifferential.D k Γ(Y, cd.U) (x i))
  have hσU : Submodule.span Γ(Y, cd.U) {σU} = ⊤ :=
    ExteriorAlgebra.span_singleton_ιMulti_eq_top _ hspanD
  have : IsLocalization.AtPrime (Y.presheaf.stalk (blowUpToBase I F.genericPoint))
      (hU.primeIdealOf ⟨_, hyU⟩).asIdeal := hU.isLocalization_stalk ⟨_, hyU⟩
  have hσA := span_singleton_topFormsMap (K := Y.presheaf.stalk (blowUpToBase I F.genericPoint))
    (d := n) (hU.primeIdealOf ⟨_, hyU⟩).asIdeal.primeCompl hσU
  obtain ⟨σ₁, -, h₁⟩ := exists_topForms_generator_stalk sY hdY (blowUpToBase I F.genericPoint)
  have : Nontrivial (⋀[Y.functionField]^n Ω[Y.functionField⁄k]) := ⟨⟨_, 0, h₁⟩⟩
  -- the chart differentials
  let ℓ' : Fin n := Fin.castLE hrn ℓ
  let S : Finset (Fin n) := (Finset.univ.filter (· ≠ ℓ)).map (Fin.castLEEmb hrn)
  let T : Fin n → Γ(blowUp I, cd.chart ℓ) := fun j =>
    if hj : (j : ℕ) < cd.r then chartFraction cd ℓ ⟨j, hj⟩ else 0
  have hℓS : ℓ' ∉ S := by
    simp only [S, ℓ', Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.castLEEmb_apply, not_exists, not_and]
    intro j hj hjℓ
    exact hj (Fin.castLE_injective hrn hjℓ)
  have hTS : ∀ j : Fin cd.r, T (Fin.castLE hrn j) = chartFraction cd ℓ j := fun j => by
    simp [T, j.2]
  have hT : ∀ i ∈ S, algebraMap Γ(Y, cd.U) Γ(blowUp I, cd.chart ℓ) (x i) =
      T i * algebraMap Γ(Y, cd.U) Γ(blowUp I, cd.chart ℓ) (x ℓ') := by
    intro i hi
    obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hi
    rw [Fin.castLEEmb_apply, hTS, ← hcx, ← hcx]
    exact chartPullback_eq_chartFraction_mul cd ℓ j
  have hgen : Algebra.adjoin Γ(Y, cd.U) (T '' S) = ⊤ := by
    obtain ⟨hsurj, -⟩ := chartPresentation_surjective_and_ker cd sY hU x hx hrn hcx ℓ
    refine eq_top_iff.mpr fun t _ => ?_
    obtain ⟨P, rfl⟩ := hsurj t
    have hle : Set.range (fun i : {i : Fin cd.r // i ≠ ℓ} => chartFraction cd ℓ i.1) ⊆ T '' S := by
      rintro - ⟨i, rfl⟩
      exact ⟨Fin.castLE hrn i.1, Finset.mem_map.mpr ⟨i.1, by simp [i.2], rfl⟩, hTS i.1⟩
    refine Algebra.adjoin_mono hle ?_
    rw [Algebra.adjoin_range_eq_range_aeval]
    exact ⟨P, rfl⟩
  have hcard : S.card = cd.r - 1 := by
    simp only [S, Finset.card_map]
    rw [Finset.filter_ne' , Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin]
  have hspanB0 := span_chartDiffs (k := k) hspanD hℓS hT hgen
  have hτ0 := ExteriorAlgebra.span_singleton_ιMulti_eq_top _ hspanB0
  have : IsLocalization.AtPrime F.localRing
      ((isAffineOpen_chart cd hU ℓ).primeIdealOf ⟨_, hF⟩).asIdeal :=
    (isAffineOpen_chart cd hU ℓ).isLocalization_stalk ⟨_, hF⟩
  have hσB := span_singleton_topFormsMap (k := k) (A := Γ(blowUp I, cd.chart ℓ))
    (K := F.localRing) (d := n)
    ((isAffineOpen_chart cd hU ℓ).primeIdealOf ⟨_, hF⟩).asIdeal.primeCompl hτ0
  have : Nontrivial (⋀[(blowUp I).functionField]^n Ω[(blowUp I).functionField⁄k]) :=
    nontrivial_topForms (blowUpToBase I ≫ sY) hdV
  refine ⟨_, hσA, topFormsMap_ne_zero_of_span_eq_top hσA, _, hσB,
    topFormsMap_ne_zero_of_span_eq_top hσB, ?_⟩
  have e1 : topFormsMap k (Y.presheaf.stalk (blowUpToBase I F.genericPoint)) F.localRing n
      (topFormsMap k Γ(Y, cd.U) (Y.presheaf.stalk (blowUpToBase I F.genericPoint)) n σU) =
      topFormsMap k Γ(Y, cd.U) F.localRing n σU :=
    MMP.Threefold.Mori.Helpers.topFormsMap_comp σU
  have e2 : topFormsMap k Γ(blowUp I, cd.chart ℓ) F.localRing n
      (topFormsMap k Γ(Y, cd.U) Γ(blowUp I, cd.chart ℓ) n σU) =
      topFormsMap k Γ(Y, cd.U) F.localRing n σU :=
    MMP.Threefold.Mori.Helpers.topFormsMap_comp σU
  have h1 : topFormsMap k Γ(Y, cd.U) Γ(blowUp I, cd.chart ℓ) n σU =
      algebraMap Γ(Y, cd.U) Γ(blowUp I, cd.chart ℓ) (x ℓ') ^ S.card •
        exteriorPower.ιMulti Γ(blowUp I, cd.chart ℓ) n (chartDiffs k x S T) := by
    refine Eq.trans ?_ (ιMulti_D_algebraMap_eq (k := k) hℓS hT)
    refine (topFormsMap_ιMulti _).trans ?_
    congr 1
    funext i
    exact KaehlerDifferential.map_D k k Γ(Y, cd.U) Γ(blowUp I, cd.chart ℓ) (x i)
  have hsc : algebraMap Γ(blowUp I, cd.chart ℓ) F.localRing
      (algebraMap Γ(Y, cd.U) Γ(blowUp I, cd.chart ℓ) (x ℓ') ^ S.card) =
      ((blowUp I).presheaf.germ (cd.chart ℓ) F.genericPoint hF
          (cd.chartPullback ℓ (cd.x ℓ))) ^ (cd.r - 1) := by
    rw [hcard, map_pow, hcx ℓ]
    rfl
  refine e1.trans (e2.symm.trans ?_)
  refine (congrArg (topFormsMap k Γ(blowUp I, cd.chart ℓ) F.localRing n) h1).trans ?_
  refine (LinearMap.map_smul (topFormsMap k Γ(blowUp I, cd.chart ℓ) F.localRing n) _ _).trans ?_
  refine (algebraMap_smul F.localRing _ _).symm.trans ?_
  exact congrArg (fun t => t • _) hsc

/-- Every point over the open `U` of a chart datum lies in one of the charts `U_ℓ`. -/
theorem exists_mem_chart (cd : BlowupChartData I) {p : blowUp I} (hp : blowUpToBase I p ∈ cd.U) :
    ∃ ℓ, p ∈ cd.chart ℓ :=
  TopologicalSpace.Opens.mem_iSup.mp ((MMP.Flips.ResolutionInputs.iSup_chart_eq_preimage cd).ge hp)

/-- Local coordinates whose first `c` cut out the centre give a chart datum with `min(c, n)`
generators. -/
theorem exists_blowupChartData (sY : Y ⟶ Spec (.of k)) {U : Y.Opens} (hU : IsAffineOpen U)
    {p : Y} (hp : p ∈ U) {n c : ℕ} (x : Fin n → Γ(Y, U)) (hx : IsLocalCoordinates sY U x)
    (hcut : Bridges.IsCutOutByFirst I U x c) :
    ∃ (cd : BlowupChartData I), IsAffineOpen cd.U ∧ p ∈ cd.U ∧
      ∃ (x' : Fin n → Γ(Y, cd.U)), IsLocalCoordinates sY cd.U x' ∧
      ∃ (hrn : cd.r ≤ n), cd.r = min c n ∧ ∀ i, cd.x i = x' (Fin.castLE hrn i) := by
  have hrn : min c n ≤ n := min_le_right _ _
  let cd : BlowupChartData I :=
    { U := U
      r := min c n
      x := fun i => x (Fin.castLE hrn i)
      generates := fun V hV => by
        rw [hcut V hV]
        congr 1
        ext s
        constructor
        · rintro ⟨i, hi, rfl⟩
          exact ⟨⟨i, lt_min hi i.2⟩, rfl⟩
        · rintro ⟨j, rfl⟩
          exact ⟨Fin.castLE hrn j, lt_of_lt_of_le j.2 (min_le_left _ _), rfl⟩ }
  exact ⟨cd, hU, hp, x, hx, hrn, rfl, fun _ => rfl⟩

/-- **Along the exceptional divisor.** On the chart `U_ℓ` containing the generic point `ξ` of
`E`, `π^*(dx_1 ∧ ⋯ ∧ dx_n) = (π^*x_ℓ)^{c-1} τ` with `τ` a generator at `ξ`, and `π^*x_ℓ` is a
uniformizer of `𝒪_{V,E}`, so the factor has order `c - 1`. -/
theorem exists_topForms_rel_exceptional (sY : Y ⟶ Spec (.of k)) [IsIntegral Y]
    (h : IsSmoothBlowup sY I)
    (hirr : IsIrreducible (I.support : Set Y)) {c : ℕ}
    (hc : (c : ℕ∞) = codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y))
    (hc1 : 1 ≤ c) {d : ℕ} (hd : topologicalKrullDim Y = d) :
    haveI := isIntegral_blowUp_of_one_le_codimension I hirr (hc ▸ by exact_mod_cast hc1)
    haveI := isDominant_blowUpToBase I hirr (hc ▸ by exact_mod_cast hc1)
    haveI := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sY I h).1
    haveI : IsLocallyNoetherian (blowUp I) :=
      isLocallyNoetherian_of_smooth (blowUpToBase I ≫ sY)
    ∀ F : MMP.Mori.PrimeDivisor (blowUp I),
    F = exceptionalPrimeDivisor sY I h hirr (hc ▸ by exact_mod_cast hc1) →
    letI := stalkAlgebra sY (blowUpToBase I F.genericPoint)
    letI := functionFieldAlgebra sY
    haveI := isScalarTower_stalk_functionField sY (blowUpToBase I F.genericPoint)
    letI := stalkAlgebra (blowUpToBase I ≫ sY) F.genericPoint
    letI := functionFieldAlgebra (blowUpToBase I ≫ sY)
    haveI := isScalarTower_stalk_functionField (blowUpToBase I ≫ sY) F.genericPoint
    letI := ((blowUpToBase I).stalkMap F.genericPoint).hom.toAlgebra
    haveI := isScalarTower_stalkMap sY (blowUpToBase I) F.genericPoint
    ∃ (σA : ⋀[Y.presheaf.stalk (blowUpToBase I F.genericPoint)]^d
        Ω[Y.presheaf.stalk (blowUpToBase I F.genericPoint)⁄k])
      (_ : Submodule.span (Y.presheaf.stalk (blowUpToBase I F.genericPoint)) {σA} = ⊤)
      (_ : topFormsMap k (Y.presheaf.stalk (blowUpToBase I F.genericPoint)) Y.functionField d
        σA ≠ 0)
      (σB : ⋀[F.localRing]^d Ω[F.localRing⁄k]) (_ : Submodule.span F.localRing {σB} = ⊤)
      (_ : topFormsMap k F.localRing (blowUp I).functionField d σB ≠ 0) (g : F.localRing),
      topFormsMap k (Y.presheaf.stalk (blowUpToBase I F.genericPoint)) F.localRing d σA = g • σB ∧
      algebraMap F.localRing (blowUp I).functionField g ≠ 0 ∧
      (blowUp I).ord (algebraMap F.localRing (blowUp I).functionField g) F.genericPoint =
        (c : ℤ) - 1 := by
  classical
  have : Smooth sY := smooth_of_isSmoothScheme h.1
  have hc1' : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y) :=
    hc ▸ by exact_mod_cast hc1
  have := isIntegral_blowUp_of_one_le_codimension I hirr hc1'
  have := isDominant_blowUpToBase I hirr hc1'
  have := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sY I h).1
  have : IsLocallyNoetherian (blowUp I) := isLocallyNoetherian_of_smooth (blowUpToBase I ≫ sY)
  have : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
  have := AlgebraicGeometry.isNormal_of_smooth (blowUpToBase I ≫ sY)
  have : IsLocallyNoetherian Y := isLocallyNoetherian_of_smooth sY
  have := isIntegral_subscheme_of_isIrreducible sY I h.2 hirr
  intro F hF
  -- the generic point of `E` and its image
  have : IsIntegral (exceptionalIdeal I).subscheme := isIntegral_exceptionalDivisor sY I h hirr hc1'
  have hξ : F.genericPoint =
      (exceptionalIdeal I).subschemeι (genericPoint (exceptionalIdeal I).subscheme) := by
    rw [hF]; rfl
  have hEξ : IdealSheafData.stalk (I.comap (blowUpToBase I)) F.genericPoint =
      IsLocalRing.maximalIdeal ((blowUp I).presheaf.stalk F.genericPoint) := by
    rw [hξ]
    exact IdealSheafData.stalk_subschemeι_genericPoint_eq_maximalIdeal (exceptionalIdeal I)
  obtain ⟨-, F', hF'id, -, hFimg⟩ :=
    isSmoothScheme_blowUp_and_exists_primeDivisor_exceptionalIdeal sY I h hirr hc1'
  have hsuppF : F.support = ((exceptionalIdeal I).support : Set (blowUp I)) := by rw [hF]; rfl
  have hsuppF' : F'.support = ((exceptionalIdeal I).support : Set (blowUp I)) := by
    simp only [AlgebraicGeometry.PrimeDivisor.support, hF'id]
  have hgenπ : IsGenericPoint (blowUpToBase I F.genericPoint) (I.support : Set Y) := by
    change closure {blowUpToBase I F.genericPoint} = _
    rw [← Set.image_singleton, (blowUpToBase I).isClosedMap.closure_image_eq_of_continuous
      (blowUpToBase I).continuous, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure, hsuppF,
      ← hsuppF', hFimg]
  have hgenη : IsGenericPoint (I.subschemeι (genericPoint I.subscheme)) (I.support : Set Y) :=
    closure_subschemeι_genericPoint I
  have hπξ : blowUpToBase I F.genericPoint = I.subschemeι (genericPoint I.subscheme) :=
    hgenπ.eq hgenη
  -- adapted coordinates at the generic point of the centre
  obtain ⟨hdimA, U, hU, hηU, n, x, hx, hcut⟩ :=
    exists_isLocalCoordinates_genericPoint I sY h hirr hc
  have hcd := exists_blowupChartData I sY hU hηU x hx hcut
  let cd := hcd.choose
  have hcdU : IsAffineOpen cd.U := hcd.choose_spec.1
  have hηcd : I.subschemeι (genericPoint I.subscheme) ∈ cd.U := hcd.choose_spec.2.1
  let x' := hcd.choose_spec.2.2.choose
  have hx' : IsLocalCoordinates sY cd.U x' := hcd.choose_spec.2.2.choose_spec.1
  have hrn : cd.r ≤ n := hcd.choose_spec.2.2.choose_spec.2.choose
  have hcdr : cd.r = min c n := hcd.choose_spec.2.2.choose_spec.2.choose_spec.1
  have hcx : ∀ i, cd.x i = x' (Fin.castLE hrn i) := hcd.choose_spec.2.2.choose_spec.2.choose_spec.2
  have hξU : blowUpToBase I F.genericPoint ∈ cd.U := by rw [hπξ]; exact hηcd
  have hℓ' := exists_mem_chart I cd hξU
  let ℓ := hℓ'.choose
  have hℓ : F.genericPoint ∈ cd.chart ℓ := hℓ'.choose_spec
  have hdV := topologicalKrullDim_blowUp sY I h hirr hc1' hd
  have key := exists_topForms_rel_of_chart I sY hd hdV cd hcdU x' hx' hrn hcx ℓ F hℓ
  -- the local equation of `E` on the chart is a uniformizer
  have := F.isDiscreteValuationRing_localRing
  let t := (blowUp I).presheaf.germ (cd.chart ℓ) F.genericPoint hℓ (cd.chartPullback ℓ (cd.x ℓ))
  have hm : IsLocalRing.maximalIdeal F.localRing = Ideal.span {t} := by
    rw [← hEξ, cd.stalk_comap_eq_span hcdU ℓ hℓ]
  have ht0 : t ≠ 0 := by
    intro h0
    rw [h0, Ideal.span_singleton_eq_bot.mpr rfl] at hm
    exact IsDiscreteValuationRing.not_a_field F.localRing hm
  have hirrt : Irreducible t := IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal t ht0 hm
  have htK : algebraMap F.localRing (blowUp I).functionField t ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ht0)
  have hordt : (blowUp I).ord (algebraMap F.localRing (blowUp I).functionField t)
      F.genericPoint = 1 := by
    rw [Scheme.ord_eq_iff F.coheight_genericPoint htK]
    have : Ring.KrullDimLE 1 F.localRing := krullDimLE_of_coheight_le F.coheight_genericPoint.le
    exact Ring.ordFrac_irreducible hirrt
  -- the number of generators is the codimension
  have hrc : cd.r = c := by
    refine le_antisymm (hcdr ▸ min_le_left _ _) ?_
    have hmA : IsLocalRing.maximalIdeal (Y.presheaf.stalk (I.subschemeι (genericPoint I.subscheme)))
        = Ideal.span (Set.range fun i => (Y.presheaf.germ cd.U _ hηcd).hom (cd.x i)) := by
      rw [← IdealSheafData.stalk_subschemeι_genericPoint_eq_maximalIdeal I,
        IdealSheafData.stalk_eq_map_germ I _ ⟨cd.U, hcdU⟩ hηcd, cd.ideal_eq_span hcdU,
        Ideal.map_span, ← Set.range_comp]
      rfl
    have h1 := ringKrullDim_le_spanFinrank_maximalIdeal
      (Y.presheaf.stalk (I.subschemeι (genericPoint I.subscheme)))
    rw [hdimA, hmA] at h1
    have h2 := Submodule.spanFinrank_span_le_ncard_of_finite
      (R := Y.presheaf.stalk (I.subschemeι (genericPoint I.subscheme)))
      (Set.finite_range fun i => (Y.presheaf.germ cd.U _ hηcd).hom (cd.x i))
    have h3 : (Set.range fun i => (Y.presheaf.germ cd.U _ hηcd).hom (cd.x i)).ncard ≤ cd.r := by
      rw [← Set.image_univ]
      exact (Set.ncard_image_le Set.finite_univ).trans (by simp [Set.ncard_univ])
    have h1' : c ≤ (Submodule.span (Y.presheaf.stalk (I.subschemeι (genericPoint I.subscheme)))
        (Set.range fun i => (Y.presheaf.germ cd.U _ hηcd).hom (cd.x i))).spanFinrank := by
      exact_mod_cast h1
    omega
  have hg : algebraMap F.localRing (blowUp I).functionField (t ^ (cd.r - 1)) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero _ htK
  have hord : (blowUp I).ord (algebraMap F.localRing (blowUp I).functionField (t ^ (cd.r - 1)))
      F.genericPoint = (c : ℤ) - 1 := by
    rw [map_pow, ← zpow_natCast, MMP.Mori.ord_zpow _ htK, hordt, mul_one, hrc, Nat.cast_sub hc1,
      Nat.cast_one]
  exact key.elim fun σA h1 => h1.elim fun hσA h2 => h2.elim fun h0A h3 => h3.elim fun σB h4 =>
    h4.elim fun hσB h5 => h5.elim fun h0B hrel =>
      ⟨σA, hσA, h0A, σB, hσB, h0B, t ^ (cd.r - 1), hrel, hg, hord⟩

open Classical in
/-- **Comparison of top forms along every prime divisor of a smooth blow-up.** For every prime
divisor `F` of `V = Bl_Z Y` there are generators `σ_A` of the top forms of `Y` at `π(η_F)` and
`σ_B` of those of `V` at `η_F` with `π^♯σ_A = g • σ_B` and `v_F(g) = c - 1` if `F = E`, `0`
otherwise. -/
theorem exists_topForms_rel (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] (h : IsSmoothBlowup sY I)
    (hirr : IsIrreducible (I.support : Set Y)) {c : ℕ}
    (hc : (c : ℕ∞) = codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y))
    (hc1 : 1 ≤ c) {d : ℕ} (hd : topologicalKrullDim Y = d) :
    haveI := isIntegral_blowUp_of_one_le_codimension I hirr (hc ▸ by exact_mod_cast hc1)
    haveI := isDominant_blowUpToBase I hirr (hc ▸ by exact_mod_cast hc1)
    haveI := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sY I h).1
    haveI : IsLocallyNoetherian (blowUp I) :=
      isLocallyNoetherian_of_smooth (blowUpToBase I ≫ sY)
    ∀ F : MMP.Mori.PrimeDivisor (blowUp I),
    letI := stalkAlgebra sY (blowUpToBase I F.genericPoint)
    letI := functionFieldAlgebra sY
    haveI := isScalarTower_stalk_functionField sY (blowUpToBase I F.genericPoint)
    letI := stalkAlgebra (blowUpToBase I ≫ sY) F.genericPoint
    letI := functionFieldAlgebra (blowUpToBase I ≫ sY)
    haveI := isScalarTower_stalk_functionField (blowUpToBase I ≫ sY) F.genericPoint
    letI := ((blowUpToBase I).stalkMap F.genericPoint).hom.toAlgebra
    haveI := isScalarTower_stalkMap sY (blowUpToBase I) F.genericPoint
    ∃ (σA : ⋀[Y.presheaf.stalk (blowUpToBase I F.genericPoint)]^d
        Ω[Y.presheaf.stalk (blowUpToBase I F.genericPoint)⁄k])
      (_ : Submodule.span (Y.presheaf.stalk (blowUpToBase I F.genericPoint)) {σA} = ⊤)
      (_ : topFormsMap k (Y.presheaf.stalk (blowUpToBase I F.genericPoint)) Y.functionField d
        σA ≠ 0)
      (σB : ⋀[F.localRing]^d Ω[F.localRing⁄k]) (_ : Submodule.span F.localRing {σB} = ⊤)
      (_ : topFormsMap k F.localRing (blowUp I).functionField d σB ≠ 0) (g : F.localRing),
      topFormsMap k (Y.presheaf.stalk (blowUpToBase I F.genericPoint)) F.localRing d σA = g • σB ∧
      algebraMap F.localRing (blowUp I).functionField g ≠ 0 ∧
      (blowUp I).ord (algebraMap F.localRing (blowUp I).functionField g) F.genericPoint =
        if F = exceptionalPrimeDivisor sY I h hirr (hc ▸ by exact_mod_cast hc1) then (c : ℤ) - 1
        else 0 := by
  intro F
  by_cases hFE : F = exceptionalPrimeDivisor sY I h hirr (hc ▸ by exact_mod_cast hc1)
  · obtain ⟨σA, hσA, h0A, σB, hσB, h0B, g, h1, h2, h3⟩ :=
      exists_topForms_rel_exceptional I sY h hirr hc hc1 hd F hFE
    exact ⟨σA, hσA, h0A, σB, hσB, h0B, g, h1, h2, by rw [h3]; simp [hFE]⟩
  · obtain ⟨σA, hσA, h0A, σB, hσB, h0B, g, h1, h2, h3⟩ :=
      exists_topForms_rel_of_ne I sY h hirr (hc ▸ by exact_mod_cast hc1) hd F hFE
    exact ⟨σA, hσA, h0A, σB, hσB, h0B, g, h1, h2, by rw [h3]; simp [hFE]⟩

/-- **The canonical divisor of a smooth blow-up: `div_V(π^*σ) = π^*div_Y(σ) + (c-1)E`.** Let `Y`
be an integral quasi-compact scheme smooth over `k`, of dimension `d`, `Z = V(I)` an irreducible
closed subscheme smooth over `k` of codimension `c ≥ 1`, `π : V = Bl_Z Y ⟶ Y` the blow-up and `E`
its exceptional prime divisor. For every nonzero rational `d`-form `σ` on `Y`, the divisor of
`π^*σ` is the pull-back of the Cartier divisor `div_Y(σ)` plus `(c - 1)E`. -/
@[mmp "lem_mmp_threefold_smooth_blowup_geometry"]
theorem divisorOfForm_pullbackRationalPluriForms_blowUpToBase (sY : Y ⟶ Spec (.of k))
    [IsIntegral Y] [CompactSpace Y] (h : IsSmoothBlowup sY I)
    (hirr : IsIrreducible (I.support : Set Y)) {c : ℕ}
    (hc : (c : ℕ∞) = codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y))
    (hc1 : 1 ≤ c) {d : ℕ} (hd : topologicalKrullDim Y = d) (σ : RationalPluriForms sY d 1)
    (hσ : σ ≠ 0) :
    haveI := smooth_of_isSmoothScheme h.1
    haveI : IsLocallyNoetherian Y := isLocallyNoetherian_of_smooth sY
    haveI : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
    haveI := AlgebraicGeometry.isNormal_of_smooth sY
    haveI := isIntegral_blowUp_of_one_le_codimension I hirr (hc ▸ by exact_mod_cast hc1)
    haveI := isDominant_blowUpToBase I hirr (hc ▸ by exact_mod_cast hc1)
    haveI := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sY I h).1
    haveI : IsLocallyNoetherian (blowUp I) := isLocallyNoetherian_of_smooth (blowUpToBase I ≫ sY)
    haveI := AlgebraicGeometry.isNormal_of_smooth (blowUpToBase I ≫ sY)
    haveI := TwoStepTower.compactSpace_blowUp (TwoStepTower.isFiniteType_of_isLocallyNoetherian I)
    divisorOfForm (pullbackRationalPluriForms sY (blowUpToBase I) σ) =
      (divisorOfForm σ).pullback (MMP.Fourfold.isCartier_of_isSmoothScheme h.1 _)
          (MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant (blowUpToBase I) _) +
        ((c : ℤ) - 1) • Finsupp.single
          (exceptionalPrimeDivisor sY I h hirr (hc ▸ by exact_mod_cast hc1)) 1 := by
  have : Smooth sY := smooth_of_isSmoothScheme h.1
  have : IsLocallyNoetherian Y := isLocallyNoetherian_of_smooth sY
  have : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
  have := AlgebraicGeometry.isNormal_of_smooth sY
  have := isIntegral_blowUp_of_one_le_codimension I hirr (hc ▸ by exact_mod_cast hc1)
  have := isDominant_blowUpToBase I hirr (hc ▸ by exact_mod_cast hc1)
  have := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sY I h).1
  have : IsLocallyNoetherian (blowUp I) := isLocallyNoetherian_of_smooth (blowUpToBase I ≫ sY)
  have := AlgebraicGeometry.isNormal_of_smooth (blowUpToBase I ≫ sY)
  have := TwoStepTower.compactSpace_blowUp (TwoStepTower.isFiniteType_of_isLocallyNoetherian I)
  set π := blowUpToBase I with hπ
  set E := exceptionalPrimeDivisor sY I h hirr (hc ▸ by exact_mod_cast hc1) with hE
  have hC := MMP.Fourfold.isCartier_of_isSmoothScheme h.1 (divisorOfForm σ)
  have hB := MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant π (divisorOfForm σ)
  have hpb := Divisor.isPullback_pullback hC hB
  ext F
  rw [DivisorWithCoeffs.coeff_add, coeff_divisorOfForm]
  set y := π F.genericPoint with hy
  obtain ⟨σA, hσA, h0A, σB, hσB, h0B, g, hrel, hg, hord⟩ :=
    exists_topForms_rel I sY h hirr hc hc1 hd F
  let := stalkAlgebra sY y
  let := functionFieldAlgebra sY
  have := isScalarTower_stalk_functionField sY y
  have hST := ordForm_pullbackRationalPluriForms_eq sY π F hσA h0A hσB h0B g hrel hg hσ
  rw [hST]
  -- a local equation of `div σ` near `y`
  obtain ⟨U, hyU, φ, hφ⟩ := hC y
  set Z0 := pointComponent y
  obtain ⟨a, ha⟩ : ∃ a, formCoeff (k := k) (Y.presheaf.stalk y) hσA h0A
      (show PluriForms k Y.functionField d 1 from σ) = a := ⟨_, rfl⟩
  set b := MMP.Threefold.Mori.Helpers.evalFF Z0 (φ : RationalFunctions Y) with hb
  have ha0 : a ≠ 0 := fun h0 => hσ ((formCoeff_eq_zero_iff hσA h0A _).mp (ha.trans h0))
  have hb0 : b ≠ 0 := ((φ.isUnit.map _).ne_zero)
  have hpbF := MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hpb hφ F hyU Z0
  rw [hpbF]
  -- Hartogs: `a / b` is a unit at `y`
  have hu : ∀ Γ : MMP.Mori.PrimeDivisor Y, y ∈ Γ.support →
      Y.ord (a * b⁻¹) Γ.genericPoint = 0 := by
    intro Γ hΓ
    have e1 := ordForm_eq_ord_formCoeff sY y Γ hΓ hσA h0A σ
    have e2 := hφ Γ ⟨y, hΓ, hyU⟩
    rw [coeff_divisorOfForm, e1, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord] at e2
    have hZ : Γ.component = Z0 := Subsingleton.elim
      (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := Y)) _ _
    rw [hZ] at e2
    rw [Scheme.ord_mul ha0 (inv_ne_zero hb0), ← zpow_neg_one, MMP.Mori.ord_zpow _ hb0, ← ha, e2,
      ← hb]
    ring
  obtain ⟨r, hr, hra⟩ := MMP.Mori.exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero y
    (mul_ne_zero ha0 (inv_ne_zero hb0)) hu
  have hab : a = (a * b⁻¹) * b := by field_simp
  have hφu : (blowUp I).ord (functionFieldMap π (a * b⁻¹)) F.genericPoint = 0 := by
    rw [← hra, MMP.Mori.functionFieldMap_algebraMap_stalk π F.genericPoint r]
    exact F.ord_algebraMap_of_isUnit (hr.map _)
  have hφa : (blowUp I).ord (functionFieldMap π a) F.genericPoint =
      (blowUp I).ord (functionFieldMap π b) F.genericPoint := by
    conv_lhs => rw [hab, map_mul]
    rw [Scheme.ord_mul ((map_ne_zero _).mpr (mul_ne_zero ha0 (inv_ne_zero hb0)))
      ((map_ne_zero _).mpr hb0), hφu, zero_add]
  rw [ha, hφa, hord, DivisorWithCoeffs.coeff_smul]
  split_ifs with hFE
  · subst hFE
    rw [DivisorWithCoeffs.coeff_single_self]
    simp [hb]
  · rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hFE)]
    simp [hb]

end BlowUp

end MMP.Threefold.Resolution
