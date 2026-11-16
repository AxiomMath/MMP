/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.Blowup.Charts

/-!
# The chart functions of a coordinate-centre blow-up are local coordinates

Let `x_1, …, x_n` be a system of local coordinates on an affine open `U` of a scheme `X` over a
field `k`, so that `(x_1, …, x_n) : U → 𝔸^n_k` is étale, and let the first `r` of them generate
the ideal of the centre `Z` on `U`. For `ℓ ≤ r` the chart `U_ℓ` of the blow-up `π : B_Z X → X`
carries the functions `x_i / x_ℓ` (`i ≤ r`, `i ≠ ℓ`) and `π^*x_i` (`i = ℓ` or `i > r`). They form
a system of local coordinates on `U_ℓ` (Kollár (3.60.2)).

The ring of `U_ℓ` is `𝒪(U)[T_i : i ≤ r, i ≠ ℓ]/(x_i - T_i x_ℓ)`
(`MMP.Flips.ResolutionInputs.chartPresentation_surjective_and_ker`). With
`P = k[X_1, …, X_n]` and the polynomial ring `Q = k[Y_1, …, Y_n]` viewed as a `P`-algebra via
`X_i ↦ Y_i Y_ℓ` (`i ≤ r`, `i ≠ ℓ`) and `X_j ↦ Y_j` otherwise, this ring is `Q ⊗_P 𝒪(U)`; so
`U_ℓ → 𝔸^n_k` is the base change of the étale morphism `U → 𝔸^n_k` along `𝔸^n_k → 𝔸^n_k`, and is
étale.

## Main definitions

* `MMP.Flips.ResolutionInputs.chartCoordinates`: the functions `x_i / x_ℓ` (`i ≤ r`, `i ≠ ℓ`)
  and `π^*x_i` (`i = ℓ` or `i > r`) on `U_ℓ`.

## Main results

* `MMP.Flips.ResolutionInputs.etale_of_chartPresentation`: the ring-theoretic base change
  statement.
* `MMP.Flips.ResolutionInputs.isLocalCoordinates_chartCoordinates`: the chart functions are a
  system of local coordinates on `U_ℓ`.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.60]
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite MvPolynomial TensorProduct

universe u

namespace MMP.Flips.ResolutionInputs

open MMP.Resolution

/-! ### The ring-theoretic statement -/

/-- The substitution `X_{e j} ↦ Y_j Y_ℓ` for `j` in the range of `ε`, and `X_{e j} ↦ Y_j`
otherwise. -/
def chartSubstitution {K ι ι' τ : Type*} [CommRing K] (e : ι ≃ ι') (ε : τ → ι) (ℓ : ι) :
    MvPolynomial ι' K →+* MvPolynomial ι K :=
  open Classical in
  eval₂Hom MvPolynomial.C fun j' =>
    if e.symm j' ∈ Set.range ε then X (e.symm j') * X ℓ else X (e.symm j')

/-- Off the range of `ε`, the chart substitution sends `X_{e j}` to `Y_j`. -/
theorem chartSubstitution_X_of_notMem {K ι ι' τ : Type*} [CommRing K] (e : ι ≃ ι') (ε : τ → ι)
    (ℓ : ι) {j : ι} (hj : j ∉ Set.range ε) :
    chartSubstitution (K := K) e ε ℓ (X (e j)) = X j := by
  simp [chartSubstitution, hj]

/-- On the range of `ε`, the chart substitution sends `X_{e (ε a)}` to `Y_{ε a} Y_ℓ`. -/
theorem chartSubstitution_X_apply {K ι ι' τ : Type*} [CommRing K] (e : ι ≃ ι') (ε : τ → ι)
    {ℓ : ι} (hℓ : ℓ ∉ Set.range ε) (a : τ) :
    chartSubstitution (K := K) e ε ℓ (X (e (ε a))) =
      X (ε a) * chartSubstitution e ε ℓ (X (e ℓ)) := by
  rw [chartSubstitution_X_of_notMem e ε ℓ hℓ]
  simp [chartSubstitution]

/-- A ring map `ψ` out of `K[Y_j]` agreeing with the presentation of `C` factors the chart
substitution through `π ∘ φ`. -/
theorem comp_chartSubstitution {K ι ι' A C : Type u} {τ : Type*} [CommRing K] [CommRing A]
    [CommRing C] (φ : MvPolynomial ι' K →+* A) (e : ι ≃ ι') (ε : τ → ι) {ℓ : ι}
    (hℓ : ℓ ∉ Set.range ε) (π : A →+* C) (t : τ → C)
    (hker : RingHom.ker (eval₂Hom π t) = Ideal.span (Set.range fun a : τ =>
      MvPolynomial.C (φ (X (e (ε a)))) - X a * MvPolynomial.C (φ (X (e ℓ)))))
    (ψ : MvPolynomial ι K →+* C) (hψC : ∀ c, ψ (MvPolynomial.C c) = π (φ (MvPolynomial.C c)))
    (hψε : ∀ a, ψ (X (ε a)) = t a)
    (hψ : ∀ j, j ∉ Set.range ε → ψ (X j) = π (φ (X (e j)))) :
    ψ.comp (chartSubstitution e ε ℓ) = π.comp φ := by
  classical
  refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j' => ?_)
  · simp [chartSubstitution, hψC]
  · obtain ⟨j, rfl⟩ := e.surjective j'
    by_cases hj : j ∈ Set.range ε
    · obtain ⟨a, rfl⟩ := hj
      have hmem : MvPolynomial.C (φ (X (e (ε a)))) - X a * MvPolynomial.C (φ (X (e ℓ))) ∈
          RingHom.ker (eval₂Hom π t) := hker ▸ Ideal.subset_span ⟨a, rfl⟩
      rw [RingHom.mem_ker] at hmem
      rw [RingHom.comp_apply, RingHom.comp_apply, chartSubstitution_X_apply e ε hℓ, map_mul,
        chartSubstitution_X_of_notMem e ε ℓ hℓ, hψε, hψ ℓ hℓ]
      exact (sub_eq_zero.mp (by simpa using hmem)).symm
    · rw [RingHom.comp_apply, RingHom.comp_apply, chartSubstitution_X_of_notMem e ε ℓ hj, hψ j hj]

/-- Let `f_Q : Q → C` and `f_A : A → C` be `R`-algebra maps such that `C` is generated over `A`
by elements `t a = f_Q (q a)`. If `G : C → Q ⊗[R] A` sends `f_Q x ↦ x ⊗ 1` and `f_A a ↦ 1 ⊗ a`,
then `C ≅ Q ⊗[R] A`, so `f_Q` is étale when `A` is étale over `R`. -/
theorem etale_of_inverse_productLeftAlgHom {R Q A C : Type u} {τ : Type*} [CommRing R]
    [CommRing Q] [CommRing A] [CommRing C] [Algebra R Q] [Algebra R A] [Algebra R C]
    [Algebra.Etale R A]
    (fQ : Q →ₐ[R] C) (fA : A →ₐ[R] C) (q : τ → Q) (t : τ → C) (hq : ∀ a, fQ (q a) = t a)
    (hsurj : Function.Surjective (eval₂Hom (fA : A →+* C) t)) (G : C →+* Q ⊗[R] A)
    (hGQ : ∀ x, G (fQ x) = x ⊗ₜ 1) (hGA : ∀ a, G (fA a) = 1 ⊗ₜ a) :
    (fQ : Q →+* C).Etale := by
  let F := Algebra.TensorProduct.productLeftAlgHom fQ fA
  have hGF : ∀ d, G (F d) = d := by
    intro d
    induction d using TensorProduct.induction_on with
    | zero => simp
    | tmul x a =>
      change G (fQ x * fA a) = x ⊗ₜ a
      rw [map_mul, hGQ, hGA, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add d d' hd hd' => rw [map_add, map_add, hd, hd']
  have hFG : (F : Q ⊗[R] A →+* C).comp (G.comp (eval₂Hom (fA : A →+* C) t)) =
      eval₂Hom (fA : A →+* C) t := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun a => ?_)
    · simp only [RingHom.comp_apply, eval₂Hom_C, RingHom.coe_coe, hGA]
      change fQ 1 * fA a = fA a
      rw [map_one, one_mul]
    · simp only [RingHom.comp_apply, eval₂Hom_X', RingHom.coe_coe, ← hq, hGQ]
      change fQ (q a) * fA 1 = fQ (q a)
      rw [map_one, mul_one]
  have hbij : Function.Bijective F := ⟨fun d d' h => by rw [← hGF d, ← hGF d', h], fun y => by
    obtain ⟨p, rfl⟩ := hsurj y
    exact ⟨G (eval₂Hom (fA : A →+* C) t p), congrArg (fun f => f p) hFG⟩⟩
  have hfQ : (fQ : Q →+* C) = (RingEquiv.ofBijective (F : Q ⊗[R] A →+* C) hbij).toRingHom.comp
      (algebraMap Q (Q ⊗[R] A)) := by
    refine RingHom.ext fun x => ?_
    change fQ x = fQ x * fA 1
    rw [map_one, mul_one]
  have hQ : (algebraMap Q (Q ⊗[R] A)).Etale := by
    rw [RingHom.etale_algebraMap]
    infer_instance
  rw [hfQ]
  exact RingHom.Etale.respectsIso.1 _ _ hQ

/-- **Base change along `X_i ↦ Y_i Y_ℓ`.** Let `φ : K[X_j : j ∈ ι'] → A` be étale, and let `C`
be presented over `A` as `A[T_a : a ∈ τ]/(φ(X_{ε a}) - T_a φ(X_ℓ))`, with `T_a ↦ t_a`, where
`ε : τ → ι` misses `ℓ` (variables matched along `e : ι ≃ ι'`). Then the ring map
`K[Y_j : j ∈ ι] → C` sending `Y_{ε a}` to `t_a` and every other `Y_j` to the image of `X_j` is
étale: `C` is the base change of `A` along `X_{ε a} ↦ Y_{ε a} Y_ℓ`, `X_j ↦ Y_j`. -/
theorem etale_of_chartPresentation {K ι ι' A C : Type u} {τ : Type*} [CommRing K] [CommRing A]
    [CommRing C]
    (φ : MvPolynomial ι' K →+* A) (hφ : φ.Etale) (e : ι ≃ ι') (ε : τ → ι) (ℓ : ι)
    (hℓ : ∀ a, ε a ≠ ℓ) (π : A →+* C) (t : τ → C)
    (hsurj : Function.Surjective (eval₂Hom π t))
    (hker : RingHom.ker (eval₂Hom π t) = Ideal.span (Set.range fun a : τ =>
      MvPolynomial.C (φ (X (e (ε a)))) - X a * MvPolynomial.C (φ (X (e ℓ)))))
    (ψ : MvPolynomial ι K →+* C) (hψC : ∀ c, ψ (MvPolynomial.C c) = π (φ (MvPolynomial.C c)))
    (hψε : ∀ a, ψ (X (ε a)) = t a)
    (hψ : ∀ j, j ∉ Set.range ε → ψ (X j) = π (φ (X (e j)))) : ψ.Etale := by
  classical
  have hℓr : ℓ ∉ Set.range ε := fun ⟨a, ha⟩ => hℓ a ha
  let : Algebra (MvPolynomial ι' K) A := φ.toAlgebra
  let : Algebra (MvPolynomial ι' K) (MvPolynomial ι K) := (chartSubstitution e ε ℓ).toAlgebra
  let : Algebra (MvPolynomial ι' K) C := (π.comp φ).toAlgebra
  have : Algebra.Etale (MvPolynomial ι' K) A := hφ
  let D := MvPolynomial ι K ⊗[MvPolynomial ι' K] A
  have hψβ := comp_chartSubstitution φ e ε hℓr π t hker ψ hψC hψε hψ
  let fQ : MvPolynomial ι K →ₐ[MvPolynomial ι' K] C :=
    { ψ with commutes' := fun p => congrArg (fun f => f p) hψβ }
  let fA : A →ₐ[MvPolynomial ι' K] C := { π with commutes' := fun p => rfl }
  let G0 : MvPolynomial τ A →+* D :=
    eval₂Hom (Algebra.TensorProduct.includeRight : A →ₐ[MvPolynomial ι' K] D).toRingHom
      fun a => X (ε a) ⊗ₜ 1
  have hrel : ∀ p : MvPolynomial ι' K, (1 : MvPolynomial ι K) ⊗ₜ[MvPolynomial ι' K] φ p =
      chartSubstitution e ε ℓ p ⊗ₜ 1 := fun p =>
    (Algebra.TensorProduct.tmul_one_eq_one_tmul (A := MvPolynomial ι K) (B := A) p).symm
  have hG0 : RingHom.ker (eval₂Hom π t) ≤ RingHom.ker G0 := by
    rw [hker, Ideal.span_le]
    rintro _ ⟨a, rfl⟩
    simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_mul, G0, eval₂Hom_C, eval₂Hom_X',
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
    rw [hrel, hrel, chartSubstitution_X_apply e ε hℓr, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one, sub_self]
  let G : C →+* D := RingHom.liftOfSurjective _ hsurj ⟨G0, hG0⟩
  have hG : ∀ p, G (eval₂Hom π t p) = G0 p := RingHom.liftOfRightInverse_comp_apply _ _ _ _
  have hGπ : ∀ a, G (π a) = 1 ⊗ₜ a := fun a => by
    simpa [G0] using hG (MvPolynomial.C a)
  have hGt : ∀ a, G (t a) = X (ε a) ⊗ₜ 1 := fun a => by
    simpa [G0] using hG (X a)
  have hGψ : G.comp ψ = (Algebra.TensorProduct.includeLeftRingHom :
      MvPolynomial ι K →+* D) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
    · rw [RingHom.comp_apply, hψC, hGπ, hrel]
      simp only [chartSubstitution, eval₂Hom_C]
      rfl
    · by_cases hj : j ∈ Set.range ε
      · obtain ⟨a, rfl⟩ := hj
        rw [RingHom.comp_apply, hψε, hGt]
        rfl
      · rw [RingHom.comp_apply, hψ j hj, hGπ, hrel, chartSubstitution_X_of_notMem e ε ℓ hj]
        rfl
  exact etale_of_inverse_productLeftAlgHom fQ fA (fun a => X (ε a)) t hψε hsurj G
    (fun x => congrArg (fun f => f x) hGψ) hGπ

/-! ### The chart coordinates -/

variable {X : Scheme.{u}} {I : X.IdealSheafData} (c : BlowupChartData I)

/-- The functions on the chart `U_ℓ` attached to functions `x_1, …, x_n` on `U` whose first `r`
are the generators of the centre: `x_i / x_ℓ` for `i ≤ r`, `i ≠ ℓ`, and `π^*x_i` for `i = ℓ`
or `i > r`. -/
def chartCoordinates {n : ℕ} (x : Fin n → Γ(X, c.U)) (ℓ : Fin c.r) (j : Fin n) :
    Γ(blowUp I, c.chart ℓ) :=
  if h : (j : ℕ) < c.r then
    if (⟨j, h⟩ : Fin c.r) = ℓ then c.chartPullback ℓ (x j) else chartFraction c ℓ ⟨j, h⟩
  else c.chartPullback ℓ (x j)

/-- For `i ≠ ℓ` among the first `r` indices, the `i`-th chart coordinate on `U_ℓ` is
`chartFraction c ℓ i`, the quotient of the `i`-th generator of the centre by the `ℓ`-th. -/
theorem chartCoordinates_castLE_of_ne {n : ℕ} (x : Fin n → Γ(X, c.U)) (hrn : c.r ≤ n)
    {ℓ i : Fin c.r} (hi : i ≠ ℓ) :
    chartCoordinates c x ℓ (Fin.castLE hrn i) = chartFraction c ℓ i := by
  have h : ((Fin.castLE hrn i : Fin n) : ℕ) < c.r := i.2
  have hi' : (⟨_, h⟩ : Fin c.r) = i := Fin.ext rfl
  rw [chartCoordinates, dite_eq_left h, hi', ite_eq_right hi]

/-- An index `j` that is not one of the first `r` indices other than `ℓ` has as chart coordinate
on `U_ℓ` the pullback `π^*x_j`. -/
theorem chartCoordinates_of_forall_ne {n : ℕ} (x : Fin n → Γ(X, c.U)) (hrn : c.r ≤ n)
    {ℓ : Fin c.r} {j : Fin n} (hj : ∀ i : Fin c.r, i ≠ ℓ → Fin.castLE hrn i ≠ j) :
    chartCoordinates c x ℓ j = c.chartPullback ℓ (x j) := by
  rw [chartCoordinates]
  split_ifs with h h'
  · rfl
  · exact absurd (Fin.ext rfl) (hj ⟨j, h⟩ h')
  · rfl

/-- The global sections of `𝔸^n_k` are the polynomial ring, with `coord i ↦ X i`. -/
private def affineSpaceΓEquiv (k : Type u) [Field k] (ι : Type u) :
    Γ(AffineSpace ι (Spec (.of k)), ⊤) ≃+* MvPolynomial ι k :=
  ((Scheme.Γ.mapIso (AffineSpace.SpecIso ι (.of k)).op).symm ≪≫
    Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv

private theorem affineSpaceΓEquiv_symm_X (k : Type u) [Field k] (ι : Type u) (i : ι) :
    (affineSpaceΓEquiv k ι).symm (MvPolynomial.X i) = AffineSpace.coord (Spec (.of k)) i := by
  apply (affineSpaceΓEquiv k ι).injective
  rw [RingEquiv.apply_symm_apply]
  change _ = (Scheme.ΓSpecIso _).hom.hom
    ((AffineSpace.SpecIso ι (.of k)).inv.appTop.hom (AffineSpace.coord (Spec (.of k)) i))
  rw [AffineSpace.SpecIso_inv_appTop_coord, ← CommRingCat.comp_apply, Iso.inv_hom_id,
    CommRingCat.id_apply]

private theorem affineSpaceΓEquiv_symm_C (k : Type u) [Field k] (ι : Type u) (a : k) :
    (affineSpaceΓEquiv k ι).symm (MvPolynomial.C a) =
      (AffineSpace ι (Spec (.of k)) ↘ Spec (.of k)).appTop.hom
        ((Scheme.ΓSpecIso (.of k)).inv.hom a) := by
  change (AffineSpace.SpecIso ι (.of k)).hom.appTop.hom
    ((Scheme.ΓSpecIso (.of (MvPolynomial ι k))).inv.hom (MvPolynomial.C a)) = _
  have hover : (AffineSpace.SpecIso ι (.of k)).hom ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial ι k)) =
      AffineSpace ι (Spec (.of k)) ↘ Spec (.of k) :=
    (Iso.eq_inv_comp _).mp (AffineSpace.SpecIso_inv_over (n := ι) (.of k)).symm
  have key : (Scheme.ΓSpecIso (.of (MvPolynomial ι k))).inv.hom (MvPolynomial.C a) =
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial ι k))).appTop.hom
        ((Scheme.ΓSpecIso (.of k)).inv.hom a) := by
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
    rfl
  rw [key, ← hover, Scheme.Hom.comp_appTop]
  rfl

/-- `(U.ι ≫ f).appTop` followed by `Γ(U, ⊤) ≅ Γ(X, U)` is `f.appLE ⊤ U`. -/
private theorem appTop_ι_comp_topIso_hom {Y : Scheme.{u}} (f : X ⟶ Y) (U : X.Opens) :
    (U.ι ≫ f).appTop ≫ U.topIso.hom = f.appLE ⊤ U le_top := by
  rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
  erw [← Functor.map_comp]
  rfl

private theorem topIso_hom_homOfVector_appTop_X {k : Type u} [Field k] {ι : Type u}
    {Y : Scheme.{u}} (U : Y.Opens) (s : U.toScheme ⟶ Spec (.of k)) (v : ι → Γ(Y, U)) (j : ι) :
    U.topIso.hom.hom ((AffineSpace.homOfVector s fun i => U.topIso.inv.hom (v i)).appTop.hom
      ((affineSpaceΓEquiv k ι).symm (MvPolynomial.X j))) = v j := by
  rw [affineSpaceΓEquiv_symm_X, AffineSpace.homOfVector_appTop_coord,
    ← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

private theorem topIso_hom_homOfVector_appTop_C {k : Type u} [Field k] {ι : Type u}
    {Y : Scheme.{u}} (U : Y.Opens) (s : Y ⟶ Spec (.of k)) (v : ι → Γ(Y, U)) (a : k) :
    U.topIso.hom.hom ((AffineSpace.homOfVector (U.ι ≫ s) fun i => U.topIso.inv.hom (v i)).appTop.hom
      ((affineSpaceΓEquiv k ι).symm (MvPolynomial.C a))) =
      (s.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (.of k)).inv.hom a) := by
  rw [affineSpaceΓEquiv_symm_C]
  have e : (AffineSpace ι (Spec (.of k)) ↘ Spec (.of k)).appTop ≫
      (AffineSpace.homOfVector (U.ι ≫ s) fun i => U.topIso.inv.hom (v i)).appTop ≫
        U.topIso.hom = s.appLE ⊤ U le_top := by
    rw [← Category.assoc, ← Scheme.Hom.comp_appTop, AffineSpace.homOfVector_over,
      appTop_ι_comp_topIso_hom]
  exact congrArg (fun f => f.hom ((Scheme.ΓSpecIso (.of k)).inv.hom a)) e

/-- The ring-level chart statement: if `φ : k[X_j] → 𝒪(U)`, `X_j ↦ x_j`, is étale, then so is any
`ψ : k[X_j] → 𝒪(U_ℓ)` sending `X_j` to the chart coordinates and agreeing with `π^* ∘ φ` on
constants. -/
theorem etale_of_chartCoordinates {k : Type u} [Field k] (sX : X ⟶ Spec (.of k))
    (hU : IsAffineOpen c.U) {n : ℕ} (x : Fin n → Γ(X, c.U)) (hx : IsLocalCoordinates sX c.U x)
    (hrn : c.r ≤ n) (hcx : ∀ i, c.x i = x (Fin.castLE hrn i)) (ℓ : Fin c.r)
    (φ : MvPolynomial (ULift.{u} (Fin n)) k →+* Γ(X, c.U)) (hφ : φ.Etale)
    (hφX : ∀ j, φ (MvPolynomial.X j) = x j.down)
    (ψ : MvPolynomial (ULift.{u} (Fin n)) k →+* Γ(blowUp I, c.chart ℓ))
    (hψX : ∀ j, ψ (MvPolynomial.X j) = chartCoordinates c x ℓ j.down)
    (hψC : ∀ a, ψ (MvPolynomial.C a) = chartPullbackHom c ℓ (φ (MvPolynomial.C a))) :
    ψ.Etale := by
  let τ := {i : Fin c.r // i ≠ ℓ}
  let ε : τ → ULift.{u} (Fin n) := fun a => ULift.up (Fin.castLE hrn a.1)
  have hℓ : ∀ a : τ, ε a ≠ ULift.up (Fin.castLE hrn ℓ) := fun a ha =>
    a.2 (Fin.castLE_injective hrn (congrArg ULift.down ha))
  obtain ⟨hsurj, hker⟩ := chartPresentation_surjective_and_ker c sX hU x hx hrn hcx ℓ
  refine etale_of_chartPresentation φ hφ (Equiv.refl _) ε (ULift.up (Fin.castLE hrn ℓ)) hℓ
    (chartPullbackHom c ℓ) (fun a : τ => chartFraction c ℓ a.1) hsurj ?_ ψ hψC ?_ ?_
  · rw [show eval₂Hom (chartPullbackHom c ℓ) (fun a : τ => chartFraction c ℓ a.1) =
      chartPresentation c ℓ from rfl, hker]
    simp only [Equiv.refl_apply, hφX, ε, hcx]
    rfl
  · intro a
    rw [hψX]
    exact chartCoordinates_castLE_of_ne c x hrn a.2
  · intro j hj
    rw [hψX, Equiv.refl_apply, hφX]
    exact chartCoordinates_of_forall_ne c x hrn fun i hi hij =>
      hj ⟨⟨i, hi⟩, congrArg ULift.up hij⟩

/-- **The chart functions are local coordinates** (Kollár (3.60.2)). Let `x_1, …, x_n` be a
system of local coordinates on an affine open `U` of a scheme `X` over `k` whose first `r`
generate the ideal of the centre on `U`. Then on the chart `U_ℓ` of the blow-up the functions
`x_i / x_ℓ` (`i ≤ r`, `i ≠ ℓ`) and `π^*x_i` (`i = ℓ` or `i > r`) form a system of local
coordinates. -/
@[mmp "lem_kr3c_blowup_chart_coordinates"]
theorem isLocalCoordinates_chartCoordinates {k : Type u} [Field k] (sX : X ⟶ Spec (.of k))
    (hU : IsAffineOpen c.U) {n : ℕ} (x : Fin n → Γ(X, c.U)) (hx : IsLocalCoordinates sX c.U x)
    (hrn : c.r ≤ n) (hcx : ∀ i, c.x i = x (Fin.castLE hrn i)) (ℓ : Fin c.r) :
    IsLocalCoordinates (blowUpToBase I ≫ sX) (c.chart ℓ) (chartCoordinates c x ℓ) := by
  set W := c.chart ℓ
  have hW : IsAffineOpen W := isAffineOpen_chart c hU ℓ
  have : IsAffine W.toScheme := hW
  have : IsAffine c.U.toScheme := hU
  set g := AffineSpace.homOfVector (n := ULift.{u} (Fin n)) (c.U.ι ≫ sX)
    fun i => c.U.topIso.inv.hom (x i.down) with hg
  set h := AffineSpace.homOfVector (n := ULift.{u} (Fin n)) (W.ι ≫ blowUpToBase I ≫ sX)
    fun i => W.topIso.inv.hom (chartCoordinates c x ℓ i.down) with hh
  have : Etale g := hx
  have hgE : RingHom.Etale g.appTop.hom := HasRingHomProperty.appTop @Etale g inferInstance
  change Etale h
  rw [HasRingHomProperty.iff_of_isAffine (P := @Etale)]
  set E := affineSpaceΓEquiv k (ULift.{u} (Fin n))
  let EU := c.U.topIso.commRingCatIsoToRingEquiv
  let EW := W.topIso.commRingCatIsoToRingEquiv
  let φ : MvPolynomial (ULift.{u} (Fin n)) k →+* Γ(X, c.U) :=
    EU.toRingHom.comp (g.appTop.hom.comp E.symm.toRingHom)
  let ψ : MvPolynomial (ULift.{u} (Fin n)) k →+* Γ(blowUp I, W) :=
    EW.toRingHom.comp (h.appTop.hom.comp E.symm.toRingHom)
  have hφ : φ.Etale :=
    RingHom.Etale.respectsIso.1 _ _ (RingHom.Etale.respectsIso.2 _ _ hgE)
  have hφX : ∀ j, φ (MvPolynomial.X j) = x j.down := fun j => by
    change c.U.topIso.hom.hom (g.appTop.hom (E.symm (MvPolynomial.X j))) = _
    rw [hg, topIso_hom_homOfVector_appTop_X]
  have hψX : ∀ j, ψ (MvPolynomial.X j) = chartCoordinates c x ℓ j.down := fun j => by
    change W.topIso.hom.hom (h.appTop.hom (E.symm (MvPolynomial.X j))) = _
    rw [hh, topIso_hom_homOfVector_appTop_X]
  have hψC : ∀ a, ψ (MvPolynomial.C a) = chartPullbackHom c ℓ (φ (MvPolynomial.C a)) := by
    intro a
    change W.topIso.hom.hom (h.appTop.hom (E.symm (MvPolynomial.C a))) =
      chartPullbackHom c ℓ (c.U.topIso.hom.hom (g.appTop.hom (E.symm (MvPolynomial.C a))))
    rw [hh, hg, topIso_hom_homOfVector_appTop_C, topIso_hom_homOfVector_appTop_C,
      ← Scheme.Hom.appLE_comp_appLE (blowUpToBase I) sX ⊤ c.U W (by simp) (c.chart_le ℓ)]
    rfl
  have hψ := etale_of_chartCoordinates c sX hU x hx hrn hcx ℓ φ hφ hφX ψ hψX hψC
  have : h.appTop.hom = EW.symm.toRingHom.comp (ψ.comp E.toRingHom) := by
    refine RingHom.ext fun p => ?_
    simp [ψ]
  rw [this]
  exact RingHom.Etale.respectsIso.1 _ _ (RingHom.Etale.respectsIso.2 _ _ hψ)

end MMP.Flips.ResolutionInputs

end
