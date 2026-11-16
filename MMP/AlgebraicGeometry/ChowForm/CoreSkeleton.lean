module

public import MMP.AlgebraicGeometry.ChowForm.Defs
public import MMP.AlgebraicGeometry.ProjectiveSpace.MorphismFromForms
public import MMP.Algebra.Homology.ComplexDeterminant
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.PicardUFD.ProjectiveSpace

/-!
# Free local data and the Koszul determinant of a family of curves

For a proper flat family of curves `π : 𝒞 ⟶ S` mapping to `ℙᴺ`, an affine open `U = Spec R` of
the base over which the direct images of the twists `H^{-j} ⊗ A^n`, `j = 0, 1, 2`, are free
gives the Koszul complex `V₂ → V₁ ⊕ V₁ → V₀` of the universal pair of hyperplanes over
`R[u, v]`, and its determinant. This file sets up these data, proves that the determinant is
bihomogeneous of bidegree `(d, d)` under scaling of the hyperplanes, and that over each closed
point of the base some pair of hyperplanes avoids the image of the fibre.

## Main definitions

* `MMP.Chow.DeterminantCurveForm.LocalFreeData`: an affine open of the base with the matrices of
  multiplication by the coordinates of `ℙᴺ` on free direct images.
* `MMP.Chow.DeterminantCurveForm.LocalFreeData.F`: the determinant of the Koszul complex of the
  universal pair of hyperplanes.
* `MMP.Chow.DeterminantCurveForm.KoszulFamily`: an invertible relatively ample module with an
  exponent and an affine open over which the direct images of the twists are free.
* `MMP.Chow.DeterminantCurveForm.KoszulFamily.toLocalFreeData`: the free local data of a
  `KoszulFamily`.

## Main results

* `MMP.Chow.DeterminantCurveForm.LocalFreeData.scale_eq`: scaling the hyperplane pair by `(t, s)`
  multiplies the determinant by `(t s)^d`.
* `MMP.Chow.DeterminantCurveForm.exists_avoidsPair`: over a closed point of the base there is a
  pair of hyperplanes without common point on the image of the fibre.

## References

* [J. Kollár, *Rational curves on algebraic varieties*][Kollar1996], I.3
-/

@[expose] public section

universe u

namespace MMP.Chow.DeterminantCurveForm

open MMP CategoryTheory Limits AlgebraicGeometry Stacks.AlgebraicGeometry.ProjPolyChart MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

section Defs

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {Y : Scheme.{u}} {N : ℕ}

/-! ### Free local data, the Koszul complex and its determinant -/

section Skeleton

/-- The linear form `∑ a_j X_j` on `ℙᴺ`. -/
noncomputable def linForm (a : Fin (N + 1) → k) : MvPolynomial (Fin (N + 1)) k :=
  ∑ j, MvPolynomial.C (a j) * X j

/-- The pair of hyperplanes `(a, b)` has no common point on the set `T` of points of `ℙᴺ`. -/
def AvoidsPair (T : Set (AlgebraicGeometry.Proj (polyGrading k N)))
    (a b : Fin (N + 1) → k) : Prop :=
  ∀ p ∈ T, ¬ (linForm a ∈ ProjectiveSpectrum.asHomogeneousIdeal p ∧
    linForm b ∈ ProjectiveSpectrum.asHomogeneousIdeal p)

/-- The set of points of `ℙᴺ` met by the fibre over `u` of the pulled back family. -/
def fibreImage {S 𝒞 U : Scheme.{u}} (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (ι : U ⟶ S) (u : U) :
    Set (AlgebraicGeometry.Proj (polyGrading k N)) :=
  Set.range ((pullback.snd π ι).fiberι u ≫ pullback.fst π ι ≫ q ≫ g)

/-- The `k`-algebra structure of a scheme over `k`, evaluated at the point `u`. -/
noncomputable def kEval {U : Scheme.{u}} (sU : U ⟶ Spec (.of k)) (u : U) :
    k →+* U.residueField u :=
  letI := MMP.Chow.structureAlgebra (k := k) sU
  (U.Γevaluation u).hom.comp (algebraMap k Γ(U, ⊤))

/-- At a closed point of a scheme locally of finite type over an algebraically closed field the
structure map `k → κ(x)` is bijective. -/
theorem kEval_bijective {U : Scheme.{u}} (sU : U ⟶ Spec (.of k)) [LocallyOfFiniteType sU]
    (x : U) (hx : IsClosed ({x} : Set U)) : Function.Bijective (kEval sU x) := by
  letI : Algebra k (U.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ sU.appTop ≫ U.Γevaluation x).hom.toAlgebra
  have hfin : Module.Finite k (U.residueField x) := by
    have : LocallyOfFiniteType (U.fromSpecResidueField x) := by
      have hclosedImmersion := isClosed_singleton_iff_isClosedImmersion.mp hx
      infer_instance
    have hcomp : LocallyOfFiniteType (U.fromSpecResidueField x ≫ sU) := inferInstance
    rw [← sU.SpecMap_residueFieldMap_fromSpecResidueField x] at hcomp
    simp only [Scheme.fromSpecResidueField, Spec.fromSpecStalk_eq, Spec.map_comp] at hcomp
    simp only [← Spec.map_comp] at hcomp
    change LocallyOfFiniteType (Spec.map _) at hcomp
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hcomp
    have : Algebra.FiniteType k (U.residueField x) := by
      change RingHom.FiniteType (algebraMap k (U.residueField x))
      convert hcomp using 1
      · simp only [RingHom.algebraMap_toAlgebra]
        rw [← Scheme.Γevaluation_naturality]
        simp only [Scheme.Γevaluation, Scheme.evaluation, Category.assoc]
    exact finite_of_finite_type_of_isJacobsonRing _ _
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := U.residueField x)

/-- At a closed point `x` of a scheme locally of finite type over `k`, evaluation of global
sections `Γ(U, ⊤) → κ(x)` is surjective. -/
theorem Γevaluation_surjective {U : Scheme.{u}} (sU : U ⟶ Spec (.of k))
    [LocallyOfFiniteType sU] (x : U) (hx : IsClosed ({x} : Set U)) :
    Function.Surjective (U.Γevaluation x).hom := by
  intro y
  obtain ⟨a, ha⟩ := (kEval_bijective sU x hx).2 y
  exact ⟨(MMP.Chow.structureAlgebra (k := k) sU).algebraMap a, ha⟩

open Opposite in
/-- The composite `Spec κ(x) ⟶ U ⟶ Spec Γ(U, ⊤)` is `Spec` of the evaluation at `x`. -/
theorem fromSpecResidueField_comp_toSpecΓ {U : Scheme.{u}} (x : U) :
    U.fromSpecResidueField x ≫ U.toSpecΓ = Spec.map (U.Γevaluation x) := by
  apply ext_of_isAffine
  simp [Scheme.fromSpecResidueField, Scheme.fromSpecStalk_appTop]
  rw [show U.Γevaluation x = U.presheaf.germ ⊤ x trivial ≫ U.residue x from rfl, Spec.map_comp]
  rfl

open Opposite in
/-- The composite `Spec κ(x) ⟶ U ⟶ Spec k` is `Spec` of the structure map `kEval sU x`. -/
theorem fromSpecResidueField_comp {U : Scheme.{u}} (sU : U ⟶ Spec (.of k)) (x : U) :
    U.fromSpecResidueField x ≫ sU = Spec.map (CommRingCat.ofHom (kEval sU x)) := by
  letI := MMP.Chow.structureAlgebra (k := k) sU
  conv_lhs => rw [MMP.Chow.eq_toSpecΓ_comp_structureAlgebra sU]
  rw [← Category.assoc, fromSpecResidueField_comp_toSpecΓ, ← Spec.map_comp]
  rfl

/-- The fibre of `π` over `x`, mapped to `Spec k` through `S`, factors through `Spec κ(x)` via
the structure map `kEval sS x`. -/
theorem fiber_structure_eq {S 𝒞 : Scheme.{u}} (sS : S ⟶ Spec (.of k)) (π : 𝒞 ⟶ S) (x : S) :
    π.fiberι x ≫ π ≫ sS =
      π.fiberToSpecResidueField x ≫ Spec.map (CommRingCat.ofHom (kEval sS x)) := by
  rw [← Category.assoc, Scheme.Hom.fiber_fac, Category.assoc, fromSpecResidueField_comp]
  rfl

section MatrixAux

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable {ι₂ ι₁ ι₀ : Type*} [Fintype ι₂] [Fintype ι₁] [Fintype ι₀]
  [DecidableEq ι₂] [DecidableEq ι₁] [DecidableEq ι₀]

/-- Multiplying the `S`-block of the split matrix `[A | S]` on the right by `N` is right
multiplication of `[A | S]` by the block diagonal matrix `diag(1, N)`. -/
theorem splitMatrix_mul_right {K : Type*} [CommRing K] (e : ι₂ ⊕ ι₀ ≃ ι₁) (A : Matrix ι₁ ι₂ K)
    (S : Matrix ι₁ ι₀ K) (N : Matrix ι₀ ι₀ K) :
    MMP.Chow.splitMatrix e A (S * N) = MMP.Chow.splitMatrix e A S * Matrix.fromBlocks 1 0 0 N := by
  ext i (j | j)
  · simp [MMP.Chow.splitMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks,
      Matrix.one_apply, Matrix.fromCols]
  · simp [MMP.Chow.splitMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks,
      Matrix.fromCols]

/-- Multiplying the split matrix `[A | S]` by a vector `y` of `ι₂ ⊕ ι₀`. -/
theorem splitMatrix_mulVec {R : Type*} [CommRing R] (e : ι₂ ⊕ ι₀ ≃ ι₁) (A : Matrix ι₁ ι₂ R)
    (S : Matrix ι₁ ι₀ R) (y : ι₂ ⊕ ι₀ → R) :
    (MMP.Chow.splitMatrix e A S).mulVec y =
      (A.mulVec (y ∘ Sum.inl) + S.mulVec (y ∘ Sum.inr)) ∘ e := by
  have hyy : y = Sum.elim (y ∘ Sum.inl) (y ∘ Sum.inr) := by ext (i | i) <;> rfl
  conv_lhs => rw [hyy]
  rw [MMP.Chow.splitMatrix, Matrix.fromCols_mulVec_sumElim]
  have a1 : (A.submatrix e id).mulVec (y ∘ Sum.inl) = (A.mulVec (y ∘ Sum.inl)) ∘ e := by
    simpa using Matrix.submatrix_mulVec_equiv A (y ∘ Sum.inl) e (Equiv.refl _)
  have a2 : (S.submatrix e id).mulVec (y ∘ Sum.inr) = (S.mulVec (y ∘ Sum.inr)) ∘ e := by
    simpa using Matrix.submatrix_mulVec_equiv S (y ∘ Sum.inr) e (Equiv.refl _)
  rw [a1, a2]
  rfl

/-- If a complex of matrices over a domain `R` becomes split exact along a surjection `R → L`
onto a field, it is split exact over the fraction field of `R`. -/
theorem isSplitExact_of_surjective_hom {R : Type*} [CommRing R] [IsDomain R] {K : Type*} [Field K]
    [Algebra R K] [IsFractionRing R K] {L : Type*} [Field L] (ψ : R →+* L)
    (hψ : Function.Surjective ψ) {e : ι₂ ⊕ ι₀ ≃ ι₁} {A : Matrix ι₁ ι₂ R} {B : Matrix ι₀ ι₁ R}
    (h : MMP.Chow.IsSplitExact e (A.map ψ) (B.map ψ)) :
    MMP.Chow.IsSplitExact e (A.map (algebraMap R K)) (B.map (algebraMap R K)) := by
  obtain ⟨S₀, hS₀, hd⟩ := h
  choose f hf using hψ
  set St : Matrix ι₁ ι₀ R := S₀.map f
  have hSt : St.map ψ = S₀ := by
    ext i j
    simp [St, hf]
  have h1 : ψ (B * St).det = 1 := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul, hSt, hS₀]
    simp
  have h2 : ψ (MMP.Chow.splitMatrix e A St).det ≠ 0 := by
    rwa [RingHom.map_det, RingHom.mapMatrix_apply, ← MMP.Chow.splitMatrix_map, hSt]
  have hdM : (B * St).det ≠ 0 := fun h0 => by rw [h0, map_zero] at h1; exact zero_ne_one h1
  have hdA : (MMP.Chow.splitMatrix e A St).det ≠ 0 := fun h0 => by
    rw [h0, map_zero] at h2
    exact h2 rfl
  set MK := (B * St).map (algebraMap R K) with hMK
  have hMKd : MK.det ≠ 0 := by
    rw [hMK, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hdM
  have hMKu : IsUnit MK.det := isUnit_iff_ne_zero.2 hMKd
  refine ⟨St.map (algebraMap R K) * MK⁻¹, ?_, ?_⟩
  · rw [← Matrix.mul_assoc, ← Matrix.map_mul]
    exact Matrix.mul_nonsing_inv _ hMKu
  · rw [splitMatrix_mul_right, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁,
      MMP.Chow.splitMatrix_map]
    refine mul_ne_zero ?_ ?_
    · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hdA
    · simp [Matrix.det_nonsing_inv, hMKd]

/-- Scaling the blocks of a split exact complex `[-V; U]`, `[U₀ | V₀]` by `t` and `s` multiplies
its Cayley determinant by `(t s)^d`, where `d` is the difference of ranks. -/
theorem cayleyDet_scale {K : Type*} [Field K] (e : β ⊕ γ ≃ α ⊕ α)
    (V U : Matrix α β K) (U0 V0 : Matrix γ α K) (t s : K) (ht : t ≠ 0) (hs : s ≠ 0)
    (hBA : Matrix.fromCols U0 V0 * Matrix.fromRows (-V) U = 0)
    (h : MMP.Chow.IsSplitExact e (Matrix.fromRows (-V) U) (Matrix.fromCols U0 V0))
    (d : ℕ) (hd : Fintype.card γ = Fintype.card α + d) :
    MMP.Chow.cayleyDet e (Matrix.fromRows (-(s • V)) (t • U)) (Matrix.fromCols (t • U0) (s • V0)) =
      (t * s) ^ d * MMP.Chow.cayleyDet e (Matrix.fromRows (-V) U) (Matrix.fromCols U0 V0) := by
  set P₁ : Matrix (α ⊕ α) (α ⊕ α) K := Matrix.fromBlocks (s • 1) 0 0 (t • 1) with hP₁
  set P₁' : Matrix (α ⊕ α) (α ⊕ α) K := Matrix.fromBlocks (s⁻¹ • 1) 0 0 (t⁻¹ • 1) with hP₁'
  set P₂ : Matrix β β K := 1
  set P₀ : Matrix γ γ K := (t * s) • 1 with hP₀
  set P₀' : Matrix γ γ K := (t * s)⁻¹ • 1 with hP₀'
  have e1 : P₁ * P₁' = 1 := by
    rw [hP₁, hP₁', Matrix.fromBlocks_multiply]
    simp [smul_smul, hs, ht]
  have e0 : P₀ * P₀' = 1 := by
    rw [hP₀, hP₀', smul_mul_smul_comm, mul_inv_cancel₀ (mul_ne_zero ht hs)]
    simp
  have hA : Matrix.fromRows (-(s • V)) (t • U) = P₁ * Matrix.fromRows (-V) U * P₂ := by
    ext (i | i) j <;> simp [hP₁, P₂, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
      Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr]
  have hB : Matrix.fromCols (t • U0) (s • V0) = P₀ * Matrix.fromCols U0 V0 * P₁' := by
    ext i (j | j) <;> simp [hP₀, hP₁', Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
      Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr]
    all_goals field_simp
  have hdet : (P₁.det * P₂.det * P₀'.det)⁻¹ = (t * s) ^ d := by
    have h1 : P₁.det = s ^ Fintype.card α * t ^ Fintype.card α := by
      rw [hP₁, Matrix.det_fromBlocks_zero₂₁]; simp [Matrix.det_smul]
    have h2 : P₀'.det = ((t * s)⁻¹) ^ Fintype.card γ := by
      rw [hP₀']; simp [Matrix.det_smul]
    have hne : t * s ≠ 0 := mul_ne_zero ht hs
    rw [h1, h2, hd, show P₂.det = 1 by simp [P₂], mul_one, inv_pow, pow_add, mul_pow]
    field_simp
  have key := MMP.Chow.cayleyDet_change hBA h e1 (P₂ := P₂) (P₂' := (1 : Matrix β β K))
    (by simp [P₂]) e0
  rw [hA, hB]
  rwa [hdet] at key

/-- An injective ring endomorphism of a domain extends to an endomorphism of its fraction
field. -/
theorem exists_fractionRing_lift {A K : Type*} [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] (f : A →+* A) (hf : Function.Injective f) :
    ∃ φ : K →+* K, φ.comp (algebraMap A K) = (algebraMap A K).comp f := by
  have hinj : Function.Injective ((algebraMap A K).comp f) :=
    (IsFractionRing.injective A K).comp hf
  exact ⟨IsFractionRing.lift hinj, RingHom.ext fun x => IsFractionRing.lift_algebraMap hinj x⟩

/-- Applying a ring map entrywise to `[-(c • V); c' • U]`. -/
theorem fromRows_neg_smul_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (c c' : R) (V U : Matrix α β R) :
    (Matrix.fromRows (-(c • V)) (c' • U)).map f =
      Matrix.fromRows (-(f c • V.map f)) (f c' • U.map f) := by
  ext (i | i) j <;> simp

/-- Applying a ring map entrywise to `[c • U | c' • V]`. -/
theorem fromCols_smul_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (c c' : R) (U V : Matrix γ α R) :
    (Matrix.fromCols (c • U) (c' • V)).map f =
      Matrix.fromCols (f c • U.map f) (f c' • V.map f) := by
  ext i (j | j) <;> simp

/-- The constant polynomial of a unit is nonzero in the fraction field of `MvPolynomial ι R`. -/
theorem algebraMap_C_unit_ne_zero {ι R K : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra (MvPolynomial ι R) K] [IsFractionRing (MvPolynomial ι R) K] (t : Rˣ) :
    algebraMap (MvPolynomial ι R) K (MvPolynomial.C (t : R)) ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial ι R) K)).2
    ((MvPolynomial.C_ne_zero).2 (Units.ne_zero t))

/-- A ring endomorphism of `R[X ⊕ Y]` fixing constants and sending `X_a ↦ t X_a`, `Y_a ↦ s Y_a`
sends the monomial `c X^e` to `t^{|e_X|} s^{|e_Y|} c X^e`. -/
theorem map_monomial_eq_of_map_X {R : Type*} [CommRing R] {n : ℕ} (t s : R)
    (σ : MvPolynomial (Fin n ⊕ Fin n) R →+* MvPolynomial (Fin n ⊕ Fin n) R)
    (hC : ∀ r, σ (C r) = C r)
    (hl : ∀ a, σ (X (Sum.inl a)) = C t * X (Sum.inl a))
    (hr : ∀ a, σ (X (Sum.inr a)) = C s * X (Sum.inr a))
    (e : (Fin n ⊕ Fin n) →₀ ℕ) (c : R) :
    σ (monomial e c) = monomial e (t ^ (∑ j, e (Sum.inl j)) * s ^ (∑ j, e (Sum.inr j)) * c) := by
  classical
  have hw : ∀ i : Fin n ⊕ Fin n, σ (X i) = C (Sum.elim (fun _ => t) (fun _ => s) i) * X i := by
    rintro (a | a)
    · exact hl a
    · exact hr a
  rw [MvPolynomial.monomial_eq, map_mul, hC, Finsupp.prod, map_prod]
  simp only [map_pow, hw, mul_pow, Finset.prod_mul_distrib]
  have hprod : ∏ i ∈ e.support, (C (Sum.elim (fun _ : Fin n => t) (fun _ : Fin n => s) i) :
      MvPolynomial (Fin n ⊕ Fin n) R) ^ e i =
      (C (t ^ (∑ j, e (Sum.inl j)) * s ^ (∑ j, e (Sum.inr j))) :
        MvPolynomial (Fin n ⊕ Fin n) R) := by
    simp only [← map_pow]
    rw [← map_prod]
    congr 1
    rw [Finset.prod_subset (Finset.subset_univ e.support)
        (fun i _ hi => by simp [Finsupp.notMem_support_iff.mp hi]),
      Fintype.prod_sum_type]
    simp [Finset.prod_pow_eq_pow_sum]
  rw [hprod, MvPolynomial.monomial_eq, Finsupp.prod]
  simp only [C_mul]
  ring

/-- In a nontrivial algebra over a field of characteristic zero, `2 ^ m = 2 ^ n` implies
`m = n`. -/
theorem two_pow_inj {K Γ : Type*} [Field K] [CharZero K] [CommRing Γ] [Nontrivial Γ]
    [Algebra K Γ] {m n : ℕ} (h : (algebraMap K Γ 2) ^ m = (algebraMap K Γ 2) ^ n) : m = n := by
  rw [← map_pow, ← map_pow] at h
  have h2 := (algebraMap K Γ).injective h
  have h3 : ((2 ^ m : ℕ) : K) = ((2 ^ n : ℕ) : K) := by simpa using h2
  exact Nat.pow_right_injective (le_refl 2) (Nat.cast_injective h3)

/-- In a local ring, an element whose image under a surjection onto a field is nonzero is a
unit. -/
theorem isUnit_of_map_ne_zero {Mr Fld : Type*} [CommRing Mr] [IsLocalRing Mr] [Field Fld]
    (ψ : Mr →+* Fld) (hψ : Function.Surjective ψ) {x : Mr} (hx : ψ x ≠ 0) : IsUnit x := by
  by_contra hnu
  have hxm : x ∈ IsLocalRing.maximalIdeal Mr := hnu
  rw [← IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective ψ hψ)] at hxm
  exact hx hxm

open MMP.Chow in
/-- Specialization of the determinant along a surjection onto a domain. -/
theorem specialize_complexDet {T Tx K K' : Type*} [CommRing T] [IsDomain T] [CommRing Tx]
    [IsDomain Tx] [Field K] [Field K'] [Algebra T K] [IsFractionRing T K] [Algebra Tx K']
    [IsFractionRing Tx K'] (ψ : T →+* Tx) (hψ : Function.Surjective ψ)
    {e : ι₂ ⊕ ι₀ ≃ ι₁} {A : Matrix ι₁ ι₂ T} {B : Matrix ι₀ ι₁ T}
    (hfib : IsSplitExact e ((A.map ψ).map (algebraMap Tx K')) ((B.map ψ).map (algebraMap Tx K')))
    (hBA' : B * A = 0) (P : T) (hP : algebraMap T K P = complexDet K e A B) :
    algebraMap Tx K' (ψ P) = complexDet K' e (A.map ψ) (B.map ψ) := by
  classical
  set p : Ideal T := RingHom.ker ψ with hp
  haveI hpp : p.IsPrime := RingHom.ker_isPrime ψ
  set L := Localization.AtPrime p
  have hnz : ∀ y : p.primeCompl, algebraMap Tx K' (ψ y) ≠ 0 := by
    intro y h0
    have := (map_eq_zero_iff _ (IsFractionRing.injective Tx K')).1 h0
    exact y.2 (by simpa [hp, RingHom.mem_ker] using this)
  let ψL : L →+* K' := IsLocalization.lift (M := p.primeCompl) (S := L)
    (g := (algebraMap Tx K').comp ψ) (fun y => isUnit_iff_ne_zero.2 (hnz y))
  have hψL : ∀ x : T, ψL (algebraMap T L x) = algebraMap Tx K' (ψ x) := fun x =>
    IsLocalization.lift_eq _ x
  have hsurj : Function.Surjective ψL := by
    intro y
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := Tx) y
    obtain ⟨a', rfl⟩ := hψ a
    obtain ⟨b', rfl⟩ := hψ b
    have hb' : b' ∈ p.primeCompl := by
      intro h; apply nonZeroDivisors.ne_zero hb; simpa [hp, RingHom.mem_ker] using h
    refine ⟨algebraMap T L a' * (IsLocalization.mk' L (1 : T) ⟨b', hb'⟩), ?_⟩
    rw [map_mul, hψL]
    have : ψL (IsLocalization.mk' L (1 : T) ⟨b', hb'⟩) = (algebraMap Tx K' (ψ b'))⁻¹ := by
      have h1 := congrArg ψL (IsLocalization.mk'_spec L (1 : T) ⟨b', hb'⟩)
      rw [map_mul, hψL, map_one, map_one] at h1
      exact eq_inv_of_mul_eq_one_left h1
    rw [this, div_eq_mul_inv]
  have hunit : ∀ x : L, ψL x ≠ 0 → IsUnit x := fun _ => isUnit_of_map_ne_zero ψL hsurj
  let _ : Algebra L K :=
    (IsLocalization.lift (M := p.primeCompl) (S := L) (g := algebraMap T K) (fun y => by
        have hy0 : (y : T) ≠ 0 := fun h0 => y.2 (h0 ▸ p.zero_mem)
        exact isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective T K)).2 hy0))
      ).toAlgebra
  have _ : IsScalarTower T L K :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq _ x).symm
  have _ : IsFractionRing L K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl _ K
  obtain ⟨S₀, hS₀, hd⟩ := hfib
  choose f hf using hsurj
  set St : Matrix ι₁ ι₀ L := S₀.map f
  have hSt : St.map ψL = S₀ := by
    ext i j
    simp [St, hf]
  set AL : Matrix ι₁ ι₂ L := A.map (algebraMap T L) with hAL
  set BL : Matrix ι₀ ι₁ L := B.map (algebraMap T L) with hBL
  have hAψ : AL.map ψL = (A.map ψ).map (algebraMap Tx K') := by
    ext i j; simp [AL, hψL]
  have hBψ : BL.map ψL = (B.map ψ).map (algebraMap Tx K') := by
    ext i j; simp [BL, hψL]
  set M : Matrix ι₀ ι₀ L := BL * St with hM
  have hψM : ψL M.det = 1 := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hM, Matrix.map_mul, hBψ, hSt, hS₀]
    simp
  have hMu : IsUnit M.det := hunit _ (by rw [hψM]; exact one_ne_zero)
  have hdsp : ψL (splitMatrix e AL St).det =
      (splitMatrix e ((A.map ψ).map (algebraMap Tx K')) S₀).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ← splitMatrix_map, hAψ, hSt]
  have hAu : IsUnit (splitMatrix e AL St).det := hunit _ (by rwa [hdsp])
  set S : Matrix ι₁ ι₀ L := St * M⁻¹ with hS
  have hBS : BL * S = 1 := by
    rw [hS, ← Matrix.mul_assoc]; exact Matrix.mul_nonsing_inv _ hMu
  have hdS : (splitMatrix e AL S).det = (splitMatrix e AL St).det * M⁻¹.det := by
    rw [hS, splitMatrix_mul_right, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁]; simp
  set δ := (splitMatrix e AL S).det with hδ
  have hδu : IsUnit δ := by rw [hdS]; exact hAu.mul (M.isUnit_nonsing_inv_det hMu)
  have hBA : B.map (algebraMap T K) * A.map (algebraMap T K) = 0 := map_mul_eq_zero (K := K) hBA'
  have hmapA : A.map (algebraMap T K) = AL.map (algebraMap L K) := by
    ext i j; simp [AL, ← IsScalarTower.algebraMap_apply]
  have hmapB : B.map (algebraMap T K) = BL.map (algebraMap L K) := by
    ext i j; simp [BL, ← IsScalarTower.algebraMap_apply]
  have hSK : B.map (algebraMap T K) * S.map (algebraMap L K) = 1 := by
    rw [hmapB, ← Matrix.map_mul, hBS]; simp
  have hdetK : (splitMatrix e (A.map (algebraMap T K)) (S.map (algebraMap L K))).det =
      algebraMap L K δ := by
    rw [hmapA, splitMatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  have hδne : algebraMap L K δ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective L K)).2 hδu.ne_zero
  have hcdK : complexDet K e A B = (algebraMap L K δ)⁻¹ := by
    rw [complexDet, cayleyDet_eq_inv_det hBA hSK (by rw [hdetK]; exact hδne), hdetK]
  have h1 : algebraMap T L P * δ = 1 := by
    apply IsFractionRing.injective L K
    rw [map_mul, map_one, ← IsScalarTower.algebraMap_apply, hP, hcdK, inv_mul_cancel₀ hδne]
  have h2 : ψL (algebraMap T L P) *
      (splitMatrix e ((A.map ψ).map (algebraMap Tx K')) S₀).det = 1 := by
    have := congrArg ψL h1
    rw [map_mul, map_one] at this
    have hMinv : ψL M⁻¹.det = 1 := by
      have := congrArg ψL (congrArg Matrix.det (Matrix.nonsing_inv_mul M hMu))
      rwa [Matrix.det_mul, map_mul, hψM, mul_one, Matrix.det_one, map_one] at this
    rwa [hdS, map_mul, hdsp, hMinv, mul_one] at this
  have hBA2 : (B.map ψ).map (algebraMap Tx K') * (A.map ψ).map (algebraMap Tx K') = 0 :=
    map_mul_eq_zero (K := K') (by rw [← Matrix.map_mul, hBA']; simp)
  rw [complexDet, cayleyDet_eq_inv_det hBA2 hS₀ hd, ← hψL, ← eq_inv_of_mul_eq_one_left h2]

/-- For a maximal ideal `m` of `Γ(U, ⊤)` on an affine scheme, there is a closed point at which
every element of `m` vanishes. -/
theorem exists_closed_pt_ker (U : Scheme.{u}) [IsAffine U] (m : Ideal Γ(U, ⊤)) (hm : m.IsMaximal) :
    ∃ x : U, IsClosed ({x} : Set U) ∧ ∀ f ∈ m, U.Γevaluation x f = 0 := by
  let y : PrimeSpectrum Γ(U, ⊤) := ⟨m, hm.isPrime⟩
  obtain ⟨x, hx⟩ := (inferInstance : Surjective U.toSpecΓ).surj y
  refine ⟨x, ?_, ?_⟩
  · rw [(U.toSpecΓ.isClosedEmbedding).isClosed_iff_image_isClosed]
    simp only [Set.image_singleton]
    change IsClosed {U.toSpecΓ.base x}
    rw [hx]
    exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).2 hm
  · intro f hf
    have h2 := Scheme.evaluation_eq_zero_iff_notMem_basicOpen (X := U) (U := ⊤) x trivial f
    have hb : x ∈ U.basicOpen f ↔ f ∉ (U.toSpecΓ.base x).asIdeal := by
      rw [← Scheme.toSpecΓ_preimage_basicOpen]
      exact PrimeSpectrum.mem_basicOpen _ _
    have : f ∈ (U.toSpecΓ.base x).asIdeal := by rw [hx]; exact hf
    exact h2.2 (fun h => (hb.1 h) this)

section

open MMP.Chow

/-- A split exact complex over a ring (section with unit determinant) is exact with `H₀ = 0`. -/
theorem exact_of_section {R : Type*} [CommRing R] {e : ι₂ ⊕ ι₀ ≃ ι₁} {A : Matrix ι₁ ι₂ R}
    {B : Matrix ι₀ ι₁ R} (hBA : B * A = 0) {S : Matrix ι₁ ι₀ R} (hS : B * S = 1)
    (hu : IsUnit (splitMatrix e A S).det) :
    (∀ v, B.mulVec v = 0 → ∃ w, A.mulVec w = v) ∧ LinearMap.range B.mulVecLin = ⊤ := by
  constructor
  · intro v hv
    have hsurj : Function.Surjective (splitMatrix e A S).mulVec :=
      Matrix.mulVec_surjective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hu)
    obtain ⟨y, hy⟩ := hsurj (v ∘ e)
    have h1 := splitMatrix_mulVec e A S y
    rw [hy] at h1
    have h2 : A.mulVec (y ∘ Sum.inl) + S.mulVec (y ∘ Sum.inr) = v := by
      funext i
      obtain ⟨j, rfl⟩ := e.surjective i
      exact (congrFun h1 j).symm
    have h3 : y ∘ Sum.inr = 0 := by
      have := congrArg B.mulVec h2
      rwa [Matrix.mulVec_add, Matrix.mulVec_mulVec, hBA, Matrix.mulVec_mulVec, hS, hv,
        Matrix.zero_mulVec, zero_add, Matrix.one_mulVec] at this
    exact ⟨y ∘ Sum.inl, by rwa [h3, Matrix.mulVec_zero, add_zero] at h2⟩
  · rw [LinearMap.range_eq_top]
    intro y
    exact ⟨S.mulVec y, by simp [Matrix.mulVec_mulVec, hS]⟩

/-- Over a local ring, a complex which is split exact along a surjection onto a field has a
section `S` of `B` with `[A | S]` of unit determinant. -/
theorem exists_section_of_local {Mr Fld : Type*} [CommRing Mr] [IsLocalRing Mr] [Field Fld]
    (ψ : Mr →+* Fld) (hψ : Function.Surjective ψ) {e : ι₂ ⊕ ι₀ ≃ ι₁} {A : Matrix ι₁ ι₂ Mr}
    {B : Matrix ι₀ ι₁ Mr} (h : IsSplitExact e (A.map ψ) (B.map ψ)) :
    ∃ S : Matrix ι₁ ι₀ Mr, B * S = 1 ∧ IsUnit (splitMatrix e A S).det := by
  have hunit : ∀ x : Mr, ψ x ≠ 0 → IsUnit x := fun _ => isUnit_of_map_ne_zero ψ hψ
  obtain ⟨S₀, hS₀, hd⟩ := h
  choose f hf using hψ
  set St : Matrix ι₁ ι₀ Mr := S₀.map f
  have hSt : St.map ψ = S₀ := by
    ext i j
    simp [St, hf]
  set M : Matrix ι₀ ι₀ Mr := B * St with hM
  have hψM : ψ M.det = 1 := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hM, Matrix.map_mul, hSt, hS₀]
    simp
  have hMu : IsUnit M.det := hunit _ (by rw [hψM]; exact one_ne_zero)
  have hdsp : ψ (splitMatrix e A St).det = (splitMatrix e (A.map ψ) S₀).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ← splitMatrix_map, hSt]
  have hAu : IsUnit (splitMatrix e A St).det := hunit _ (by rwa [hdsp])
  refine ⟨St * M⁻¹, ?_, ?_⟩
  · rw [← Matrix.mul_assoc]; exact Matrix.mul_nonsing_inv _ hMu
  · rw [splitMatrix_mul_right, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one,
      one_mul]
    exact hAu.mul (M.isUnit_nonsing_inv_det hMu)

/-- If a complex is split exact along a surjection `ψ` onto a field, then at every prime
`p ≤ ker ψ` the localized complex is exact at the middle term and has cokernel of finite
length. -/
theorem exact_at_prime_of_residue {T Fld : Type*} [CommRing T] [Field Fld] (ψ : T →+* Fld)
    (hψ : Function.Surjective ψ) (p : Ideal T) [p.IsPrime] (hpk : p ≤ RingHom.ker ψ)
    {e : ι₂ ⊕ ι₀ ≃ ι₁} {A : Matrix ι₁ ι₂ T} {B : Matrix ι₀ ι₁ T} (hBA : B * A = 0)
    (h : IsSplitExact e (A.map ψ) (B.map ψ)) :
    (∀ v, (B.map (algebraMap T (Localization.AtPrime p))).mulVec v = 0 →
      ∃ w, (A.map (algebraMap T (Localization.AtPrime p))).mulVec w = v) ∧
    Module.length (Localization.AtPrime p) ((ι₀ → Localization.AtPrime p) ⧸
      LinearMap.range (B.map (algebraMap T (Localization.AtPrime p))).mulVecLin) ≠ ⊤ := by
  have hmax : (RingHom.ker ψ).IsMaximal := RingHom.ker_isMaximal_of_surjective ψ hψ
  set m : Ideal T := RingHom.ker ψ with hm
  have hnz : ∀ y : m.primeCompl, ψ y ≠ 0 := fun y h0 =>
    y.2 (by simpa [hm, RingHom.mem_ker] using h0)
  let ψM : Localization.AtPrime m →+* Fld :=
    IsLocalization.lift (M := m.primeCompl) (g := ψ) (fun y => isUnit_iff_ne_zero.2 (hnz y))
  have hψM : ∀ x : T, ψM (algebraMap T (Localization.AtPrime m) x) = ψ x := fun x =>
    IsLocalization.lift_eq _ x
  have hψMs : Function.Surjective ψM := fun y => by
    obtain ⟨x, rfl⟩ := hψ y
    exact ⟨algebraMap T _ x, hψM x⟩
  have hAψ : (A.map (algebraMap T (Localization.AtPrime m))).map ψM = A.map ψ := by
    ext i j; simp [hψM]
  have hBψ : (B.map (algebraMap T (Localization.AtPrime m))).map ψM = B.map ψ := by
    ext i j; simp [hψM]
  obtain ⟨S, hBS, hSu⟩ := exists_section_of_local ψM hψMs (e := e)
    (A := A.map (algebraMap T (Localization.AtPrime m)))
    (B := B.map (algebraMap T (Localization.AtPrime m))) (by rw [hAψ, hBψ]; exact h)
  let f : Localization.AtPrime m →+* Localization.AtPrime p :=
    IsLocalization.lift (M := m.primeCompl) (g := algebraMap T (Localization.AtPrime p))
      (fun y => IsLocalization.map_units (Localization.AtPrime p)
        (⟨y, fun hy => y.2 (hpk hy)⟩ : p.primeCompl))
  have hf : ∀ x : T, f (algebraMap T (Localization.AtPrime m) x) =
      algebraMap T (Localization.AtPrime p) x := fun x => IsLocalization.lift_eq _ x
  have hAf : (A.map (algebraMap T (Localization.AtPrime m))).map f =
      A.map (algebraMap T (Localization.AtPrime p)) := by ext i j; simp [hf]
  have hBf : (B.map (algebraMap T (Localization.AtPrime m))).map f =
      B.map (algebraMap T (Localization.AtPrime p)) := by ext i j; simp [hf]
  have hS1 : B.map (algebraMap T (Localization.AtPrime p)) * S.map f = 1 := by
    rw [← hBf, ← Matrix.map_mul, hBS]; simp
  have hSu1 :
      IsUnit (splitMatrix e (A.map (algebraMap T (Localization.AtPrime p))) (S.map f)).det := by
    rw [← hAf, splitMatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hSu.map f
  have hBA1 : B.map (algebraMap T (Localization.AtPrime p)) *
      A.map (algebraMap T (Localization.AtPrime p)) = 0 := by
    rw [← Matrix.map_mul, hBA]; simp
  obtain ⟨hex, hrange⟩ := exact_of_section hBA1 hS1 hSu1
  refine ⟨hex, ?_⟩
  rw [hrange]
  have : Subsingleton ((ι₀ → Localization.AtPrime p) ⧸
      (⊤ : Submodule (Localization.AtPrime p) (ι₀ → Localization.AtPrime p))) :=
    Submodule.Quotient.subsingleton_iff.2 rfl
  rw [Module.length_eq_zero]
  exact ENat.zero_ne_top

end

/-- A polynomial ring in finitely many variables over an integrally closed domain is integrally
closed. -/
theorem isIntegrallyClosed_mvPolynomial_fin (R : Type*) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] (n : ℕ) : IsIntegrallyClosed (MvPolynomial (Fin n) R) := by
  induction n with
  | zero => exact IsIntegrallyClosed.of_equiv (MvPolynomial.isEmptyRingEquiv R (Fin 0)).symm
  | succ n ih =>
    haveI := ih
    haveI : IsDomain (MvPolynomial (Fin n) R) := NoZeroDivisors.to_isDomain _
    exact IsIntegrallyClosed.of_equiv (MvPolynomial.finSuccEquiv R n).symm.toRingEquiv

/-- The polynomial ring `R[u, v]` in two families of `n` variables over an integrally closed
domain is integrally closed. -/
theorem isIntegrallyClosed_mvPolynomial_sum (R : Type*) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] (n : ℕ) : IsIntegrallyClosed (MvPolynomial (Fin n ⊕ Fin n) R) := by
  haveI := isIntegrallyClosed_mvPolynomial_fin R (n + n)
  exact IsIntegrallyClosed.of_equiv
    (MvPolynomial.renameEquiv R (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n))).symm.toRingEquiv

end MatrixAux

/-- The localized complex `A, B` at the prime `p` is exact at the middle term. -/
def ExactAt {R : Type*} [CommRing R] {ι₂ ι₁ ι₀ : Type*} [Fintype ι₂] [Fintype ι₁]
    (A : Matrix ι₁ ι₂ R) (B : Matrix ι₀ ι₁ R) (p : Ideal R) [p.IsPrime] : Prop :=
  ∀ v, (B.map (algebraMap R (Localization.AtPrime p))).mulVec v = 0 →
    ∃ w, (A.map (algebraMap R (Localization.AtPrime p))).mulVec w = v

/-- The length of the cokernel of `B` after localizing at `p`. -/
noncomputable def cokerLength {R : Type*} [CommRing R] {ι₁ ι₀ : Type*} [Fintype ι₁]
    (B : Matrix ι₀ ι₁ R) (p : Ideal R) [p.IsPrime] : ℕ∞ :=
  Module.length (Localization.AtPrime p) ((ι₀ → Localization.AtPrime p) ⧸
    LinearMap.range (B.map (algebraMap R (Localization.AtPrime p))).mulVecLin)

/-- Exactness at the middle term survives every localization. -/
theorem exactAt_of_forall {R : Type*} [CommRing R] {ι₂ ι₁ ι₀ : Type*} [Fintype ι₂]
    [Fintype ι₁] [Fintype ι₀] (A : Matrix ι₁ ι₂ R) (B : Matrix ι₀ ι₁ R)
    (h : ∀ v, B.mulVec v = 0 → ∃ w, A.mulVec w = v) (p : Ideal R) [p.IsPrime] :
    ExactAt A B p := by
  classical
  set M := p.primeCompl
  set L := Localization.AtPrime p
  intro v hv
  obtain ⟨s, hv'⟩ := IsLocalization.exist_integer_multiples_of_finite M v
  choose x hx using hv'
  have hxv : (fun i => algebraMap R L (x i)) = (s : R) • v := funext fun i => (hx i)
  have hBx : (B.map (algebraMap R L)).mulVec (fun i => algebraMap R L (x i)) = 0 := by
    rw [hxv, Matrix.mulVec_smul, hv, smul_zero]
  have hBx' : (fun j => algebraMap R L (B.mulVec x j)) = 0 := by
    rw [← hBx]; funext j; simp [Matrix.mulVec, dotProduct, map_sum]
  have : ∀ j, ∃ t : M, (t : R) * B.mulVec x j = 0 := fun j =>
    (IsLocalization.map_eq_zero_iff M L _).1 (congrFun hBx' j)
  choose t ht using this
  let T : M := ∏ j, t j
  have hT : B.mulVec ((T : R) • x) = 0 := by
    funext j
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have : (T : R) = (∏ j' ∈ Finset.univ.erase j, (t j' : R)) * t j := by
      simp only [T, Submonoid.coe_finset_prod]
      rw [Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
    rw [this, mul_assoc, ht j, mul_zero]
  obtain ⟨w, hw⟩ := h _ hT
  have hu : IsUnit (algebraMap R L ((T : R) * s)) := IsLocalization.map_units L (T * s)
  refine ⟨(hu.unit⁻¹ : Lˣ) • (fun i => algebraMap R L (w i)), ?_⟩
  rw [Matrix.mulVec_smul]
  have e : (A.map (algebraMap R L)).mulVec (fun i => algebraMap R L (w i)) =
      fun j => algebraMap R L (A.mulVec w j) := by
    funext j; simp [Matrix.mulVec, dotProduct, map_sum]
  rw [e, hw]
  funext j
  simp only [Pi.smul_apply, smul_eq_mul, Units.smul_def]
  have : algebraMap R L ((T : R) * x j) = algebraMap R L ((T : R) * s) * v j := by
    have := congrFun hxv j
    simp only [Pi.smul_apply, Algebra.smul_def] at this
    rw [map_mul, map_mul, this, mul_assoc]
  rw [this, ← mul_assoc]
  simp

/-- If `B` is surjective over the fraction field, then at a height-one prime the cokernel of `B`
has finite length. -/
theorem length_coker_ne_top_of_mul_eq_one {T : Type*} [CommRing T] [IsDomain T]
    [IsNoetherianRing T] {ι₁ ι₀ : Type*} [Fintype ι₁] [Fintype ι₀] [DecidableEq ι₀]
    (B : Matrix ι₀ ι₁ T) (S : Matrix ι₁ ι₀ (FractionRing T))
    (hS : B.map (algebraMap T (FractionRing T)) * S = 1)
    (p : Ideal T) [p.IsPrime] (hp : p.height = 1) :
    Module.length (Localization.AtPrime p) ((ι₀ → Localization.AtPrime p) ⧸
      LinearMap.range (B.map (algebraMap T (Localization.AtPrime p))).mulVecLin) ≠ ⊤ := by
  classical
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors T)
    (fun ij : ι₁ × ι₀ => S ij.1 ij.2)
  choose S' hS' using hc
  let S₀ : Matrix ι₁ ι₀ T := Matrix.of fun i j => S' (i, j)
  have hBS : ∀ i j, (B * S₀) i j = if i = j then (c : T) else 0 := by
    intro i j
    apply IsFractionRing.injective T (FractionRing T)
    have h1 := congrFun (congrFun hS i) j
    have : algebraMap T (FractionRing T) ((B * S₀) i j) =
        (c : T) • (B.map (algebraMap T (FractionRing T)) * S) i j := by
      simp only [Matrix.mul_apply, map_sum, map_mul, Matrix.map_apply, Finset.smul_sum, S₀,
        Matrix.of_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hS' (l, j), Algebra.smul_def, Algebra.smul_def]; ring
    rw [this, h1, Matrix.one_apply]
    split_ifs <;> simp [Algebra.smul_def]
  set L := Localization.AtPrime p
  set R := LinearMap.range (B.map (algebraMap T L)).mulVecLin
  have hmem : ∀ (i : ι₀) (a : L), Pi.single i (algebraMap T L c * a) ∈ R := by
    intro i a
    refine ⟨(S₀.map (algebraMap T L)).mulVec (Pi.single i a), ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← Matrix.map_mul]
    funext j
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Matrix.map_apply, hBS]
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  haveI : Ring.KrullDimLE 1 L := by
    rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height p L, hp]
    rfl
  have hc0 : algebraMap T L c ∈ nonZeroDivisors L := by
    refine mem_nonZeroDivisors_of_ne_zero ?_
    exact (map_ne_zero_iff _ (IsLocalization.injective L p.primeCompl_le_nonZeroDivisors)).2
      (nonZeroDivisors.ne_zero c.2)
  have hfl := isFiniteLength_quotient_span_singleton (R := L) hc0
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at hfl
  obtain ⟨-, hart⟩ := hfl
  rw [Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian]
  refine ⟨inferInstance, ?_⟩
  let φ : ι₀ → (L ⧸ Ideal.span {algebraMap T L c}) →ₗ[L] ((ι₀ → L) ⧸ R) := fun i =>
    (Ideal.span {algebraMap T L c}).liftQ (R.mkQ ∘ₗ LinearMap.single L (fun _ => L) i) (by
      intro a ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [LinearMap.mem_ker]
      show R.mkQ (Pi.single i _) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, mul_comm]
      exact hmem i b)
  let g : (ι₀ → L ⧸ Ideal.span {algebraMap T L c}) →ₗ[L] ((ι₀ → L) ⧸ R) :=
    ∑ i, (φ i) ∘ₗ LinearMap.proj i
  have hg : Function.Surjective g := by
    intro m
    obtain ⟨y, rfl⟩ := R.mkQ_surjective m
    refine ⟨fun i => Ideal.Quotient.mk _ (y i), ?_⟩
    have : g (fun i => Ideal.Quotient.mk _ (y i)) = ∑ i, R.mkQ (Pi.single i (y i)) := by
      simp only [g, LinearMap.sum_apply]
      rfl
    rw [this, ← map_sum, Finset.univ_sum_single y]
  exact isArtinian_of_surjective _ g hg

/-- A complex of vector spaces for which `e` identifies `ι₂ ⊕ ι₀` with `ι₁`, injective on the left
and exact in the middle, is split exact. -/
theorem isSplitExact_of_injective_of_ker_le {K : Type*} [Field K] {ι₂ ι₁ ι₀ : Type*}
    [Fintype ι₂] [Fintype ι₁] [Fintype ι₀] [DecidableEq ι₂] [DecidableEq ι₁] [DecidableEq ι₀]
    (e : ι₂ ⊕ ι₀ ≃ ι₁) {A : Matrix ι₁ ι₂ K} {B : Matrix ι₀ ι₁ K} (hBA : B * A = 0)
    (hA : Function.Injective A.mulVec) (hex : ∀ v, B.mulVec v = 0 → ∃ w, A.mulVec w = v) :
    MMP.Chow.IsSplitExact e A B := by
  classical
  have hker : LinearMap.ker B.mulVecLin = LinearMap.range A.mulVecLin := by
    refine le_antisymm (fun v hv => hex v hv) ?_
    rintro _ ⟨w, rfl⟩
    simp [LinearMap.mem_ker, Matrix.mulVec_mulVec, hBA]
  have hrA : Module.finrank K (LinearMap.range A.mulVecLin) = Fintype.card ι₂ := by
    rw [LinearMap.finrank_range_of_inj hA, Module.finrank_fintype_fun_eq_card]
  have hcard : Fintype.card ι₁ = Fintype.card ι₂ + Fintype.card ι₀ := by
    rw [← Fintype.card_sum]; exact (Fintype.card_congr e).symm
  have hrn := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
  rw [hker, hrA, Module.finrank_fintype_fun_eq_card] at hrn
  have hBsurj : LinearMap.range B.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fintype_fun_eq_card]; omega
  obtain ⟨σ, hσ⟩ := LinearMap.exists_rightInverse_of_surjective B.mulVecLin hBsurj
  set S := LinearMap.toMatrix' σ
  have hS : B * S = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_one]
    simp only [S, Matrix.toLin'_toMatrix']
    exact hσ
  refine ⟨S, hS, ?_⟩
  have hinj : Function.Injective (MMP.Chow.splitMatrix e A S).mulVec := by
    intro y₁ y₂ hy12
    rw [← sub_eq_zero] at hy12 ⊢
    rw [← Matrix.mulVec_sub] at hy12
    generalize y₁ - y₂ = y at hy12 ⊢
    have hy : (MMP.Chow.splitMatrix e A S).mulVec y = 0 := hy12
    have h1 := splitMatrix_mulVec e A S y
    have h2 : A.mulVec (y ∘ Sum.inl) + S.mulVec (y ∘ Sum.inr) = 0 := by
      funext i
      obtain ⟨j, rfl⟩ := e.surjective i
      have := congrFun h1 j
      rw [hy] at this
      exact this.symm
    have h3 : y ∘ Sum.inr = 0 := by
      have := congrArg B.mulVec h2
      rwa [Matrix.mulVec_add, Matrix.mulVec_mulVec, hBA, Matrix.mulVec_mulVec, hS,
        Matrix.zero_mulVec, zero_add, Matrix.one_mulVec, Matrix.mulVec_zero] at this
    rw [h3, Matrix.mulVec_zero, add_zero] at h2
    have h4 : y ∘ Sum.inl = 0 := hA (by rw [h2, Matrix.mulVec_zero])
    ext (i | i)
    · exact congrFun h4 i
    · exact congrFun h3 i
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.mulVec_injective_iff_isUnit.1 hinj)).ne_zero

/-- **Free local data.**  An affine open `U = Spec R` of the base around `s`, with `R` a normal
Noetherian domain, on which the direct images `V_j = H⁰(𝒞_U, 𝒪 ⊗ A^n ⊗ H^{-j})`, `j = 0, 1, 2`, are
free of ranks `r_j` (with `r_j - r_{j+1} = d`), together with the matrices `X₀ a : V₁ → V₀` and
`X₁ a : V₂ → V₁` of multiplication by the coordinate `x_a` of `ℙᴺ`, in chosen bases. -/
structure LocalFreeData (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    {S 𝒞 : Scheme.{u}} (sS : S ⟶ Spec (.of k)) (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (d : ℕ) (s : S) where
  /-- The affine open `U = Spec R` of the base. -/
  U : Scheme.{u}
  /-- The open immersion of `U` into the base. -/
  ι : U ⟶ S
  [isOpenImmersion : IsOpenImmersion ι]
  /-- The point `s` lies in the image of `U`. -/
  mem : s ∈ Set.range ι
  [isAffine : IsAffine U]
  [isDomain : IsDomain Γ(U, ⊤)]
  [isNoetherian : IsNoetherianRing Γ(U, ⊤)]
  [isIntegrallyClosed : IsIntegrallyClosed Γ(U, ⊤)]
  [locFT : LocallyOfFiniteType (ι ≫ sS)]
  /-- The rank of the free module `V₀`. -/
  r₀ : ℕ
  /-- The rank of the free module `V₁`. -/
  r₁ : ℕ
  /-- The rank of the free module `V₂`. -/
  r₂ : ℕ
  /-- The matrix of multiplication by the coordinate `x_a`, `V₁ → V₀`. -/
  X₀ : Fin (N + 1) → Matrix (Fin r₀) (Fin r₁) Γ(U, ⊤)
  /-- The matrix of multiplication by the coordinate `x_a`, `V₂ → V₁`. -/
  X₁ : Fin (N + 1) → Matrix (Fin r₁) (Fin r₂) Γ(U, ⊤)
  /-- Multiplication by the coordinates commutes: `x_a x_b = x_b x_a` as maps `V₂ → V₀`. -/
  comm : ∀ a b, X₀ a * X₁ b = X₀ b * X₁ a
  /-- `r₀ = r₁ + d`. -/
  rank₀ : r₀ = r₁ + d
  /-- `r₁ = r₂ + d`. -/
  rank₁ : r₁ = r₂ + d

attribute [local instance] LocalFreeData.isOpenImmersion LocalFreeData.isAffine
  LocalFreeData.isDomain LocalFreeData.isNoetherian LocalFreeData.isIntegrallyClosed
  LocalFreeData.locFT

namespace LocalFreeData

variable {g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)} {S 𝒞 : Scheme.{u}}
  {sS : S ⟶ Spec (.of k)} {π : 𝒞 ⟶ S} {q : 𝒞 ⟶ Y} {d : ℕ} {s : S}
  (D : LocalFreeData g sS π q d s)

/-- The polynomial ring `R[u, v]` of the universal pair of hyperplanes. -/
abbrev Pol := MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) Γ(D.U, ⊤)

/-- The polynomial ring `κ(u)[u, v]` over the residue field of a point. -/
abbrev PolAt (u : D.U) := MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) (D.U.residueField u)

/-- The universal first hyperplane `∑ u_a x_a` acting `V₁ → V₀`. -/
noncomputable def ellU₀ : Matrix (Fin D.r₀) (Fin D.r₁) D.Pol :=
  ∑ a, (MvPolynomial.X (Sum.inl a) : D.Pol) • (D.X₀ a).map MvPolynomial.C

/-- The universal second hyperplane `∑ v_a x_a` acting `V₁ → V₀`. -/
noncomputable def ellV₀ : Matrix (Fin D.r₀) (Fin D.r₁) D.Pol :=
  ∑ a, (MvPolynomial.X (Sum.inr a) : D.Pol) • (D.X₀ a).map MvPolynomial.C

/-- The universal first hyperplane acting `V₂ → V₁`. -/
noncomputable def ellU₁ : Matrix (Fin D.r₁) (Fin D.r₂) D.Pol :=
  ∑ a, (MvPolynomial.X (Sum.inl a) : D.Pol) • (D.X₁ a).map MvPolynomial.C

/-- The universal second hyperplane acting `V₂ → V₁`. -/
noncomputable def ellV₁ : Matrix (Fin D.r₁) (Fin D.r₂) D.Pol :=
  ∑ a, (MvPolynomial.X (Sum.inr a) : D.Pol) • (D.X₁ a).map MvPolynomial.C

/-- The first Koszul differential `V₂ → V₁ ⊕ V₁`, `x ↦ (-ℓ_v x, ℓ_u x)`. -/
noncomputable def A : Matrix (Fin D.r₁ ⊕ Fin D.r₁) (Fin D.r₂) D.Pol :=
  Matrix.fromRows (-D.ellV₁) D.ellU₁

/-- The second Koszul differential `V₁ ⊕ V₁ → V₀`, `(x, y) ↦ ℓ_u x + ℓ_v y`. -/
noncomputable def B : Matrix (Fin D.r₀) (Fin D.r₁ ⊕ Fin D.r₁) D.Pol :=
  Matrix.fromCols D.ellU₀ D.ellV₀

/-- The Koszul differentials compose to zero. -/
theorem B_mul_A : D.B * D.A = 0 := by
  have key : D.ellU₀ * D.ellV₁ = D.ellV₀ * D.ellU₁ := by
    simp only [ellU₀, ellV₁, ellV₀, ellU₁]
    simp only [Matrix.sum_mul, Matrix.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul,
      mul_comm (MvPolynomial.X (Sum.inr b) : D.Pol), ← Matrix.map_mul, ← Matrix.map_mul, D.comm a b]
  rw [B, A, Matrix.fromCols_mul_fromRows, Matrix.mul_neg]
  exact neg_add_eq_zero.mpr key

/-- The identification `V₂ ⊕ V₀ ≃ V₁ ⊕ V₁` of index sets (the alternating rank is zero). -/
def e : Fin D.r₂ ⊕ Fin D.r₀ ≃ Fin D.r₁ ⊕ Fin D.r₁ :=
  (finSumFinEquiv.trans (finCongr (by have := D.rank₀; have := D.rank₁; omega))).trans
    finSumFinEquiv.symm

/-- **The determinant form** of the Koszul complex `V₂ → V₁ ⊕ V₁ → V₀` over `R[u, v]`, as an
element of the fraction field of `R[u, v]`. -/
noncomputable def F : FractionRing D.Pol :=
  MMP.Chow.complexDet (FractionRing D.Pol) D.e D.A D.B

/-- The specialization `R[u, v] → κ(x)[u, v]` at a point. -/
noncomputable def specHom (x : D.U) : D.Pol →+* D.PolAt x :=
  MvPolynomial.map (D.U.Γevaluation x).hom

/-- The determinant of the fibre Koszul complex over `κ(x)[u, v]`. -/
noncomputable def fibreDet (x : D.U) : FractionRing (D.PolAt x) :=
  MMP.Chow.complexDet (FractionRing (D.PolAt x)) D.e (D.A.map (D.specHom x))
    (D.B.map (D.specHom x))

/-- The evaluation `R[u, v] → κ(x)` at the hyperplane pair `(a, b)` defined over `k`. -/
noncomputable def evalPt (x : D.U) (a b : Fin (N + 1) → k) : D.Pol →+* D.U.residueField x :=
  MvPolynomial.eval₂Hom (D.U.Γevaluation x).hom
    (Sum.elim (fun j => kEval (D.ι ≫ sS) x (a j)) (fun j => kEval (D.ι ≫ sS) x (b j)))

/-- The pushed-forward fundamental cycle of the fibre of the family over `D.U` at `x`. -/
noncomputable def cycAt (x : D.U) : Mori.OneCycle ℤ (projToSpecCoeff k N) :=
  cyc g (D.ι ≫ sS) (pullback.snd π D.ι) (pullback.fst π D.ι ≫ q) x

/-- **The specification of free local data** by the geometry: the three facts about the matrices
that come from the sheaves they represent (direct images of the Koszul complex, base change,
Koszul regularity). -/
structure Realizes : Prop where
  /-- Over a closed point, a pair of hyperplanes avoiding the fibre makes the fibre complex
  exact. -/
  exact_of_avoid : ∀ x : D.U, IsClosed ({x} : Set D.U) → ∀ a b : Fin (N + 1) → k,
    AvoidsPair (fibreImage g π q D.ι x) a b →
      MMP.Chow.IsSplitExact D.e (D.A.map (D.evalPt x a b)) (D.B.map (D.evalPt x a b))
  /-- At a horizontal height-one prime of `R[u, v]` the complex is exact at `V₁ ⊕ V₁` with `H₀` of
  finite length (Koszul regularity and finiteness of the incidence over the generic point). -/
  horizontal : ∀ (p : Ideal D.Pol) [p.IsPrime], p.height = 1 →
    p.comap (MvPolynomial.C : Γ(D.U, ⊤) →+* D.Pol) = ⊥ →
      ExactAt D.A D.B p ∧ cokerLength D.B p ≠ ⊤

/-- Over a closed point, the determinant of the fibre complex is, up to a nonzero scalar, the
product of the incidence forms of the curves of the fibre cycle with their multiplicities. -/
def FibreDetSpec : Prop :=
  ∀ x : D.U, IsClosed ({x} : Set D.U) →
    ∀ G : Mori.ProperCurve (projToSpecCoeff k N) → MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k,
      (∀ C ∈ (D.cycAt x).support, IncForm C (G C)) →
      ∃ l : D.U.residueField x, l ≠ 0 ∧
        D.fibreDet x = algebraMap (D.PolAt x) (FractionRing (D.PolAt x))
          (MvPolynomial.C l * MvPolynomial.map (kEval (D.ι ≫ sS) x)
            (∏ C ∈ (D.cycAt x).support, G C ^ ((D.cycAt x) C).toNat))

/-- The affine open `D.U` has a closed point. -/
theorem exists_isClosed_point : ∃ x : D.U, IsClosed ({x} : Set D.U) := by
  obtain ⟨x, -, hx⟩ := (isClosed_univ : IsClosed (Set.univ : Set D.U)).exists_closed_singleton
    ⟨D.mem.choose, trivial⟩
  exact ⟨x, hx⟩

/-- At a closed point, the evaluation `R[u, v] → κ(x)` at a pair of hyperplanes is surjective. -/
theorem evalPt_surjective (x : D.U) (hx : IsClosed ({x} : Set D.U)) (a b : Fin (N + 1) → k) :
    Function.Surjective (D.evalPt x a b) := by
  intro y
  obtain ⟨r, hr⟩ := Γevaluation_surjective (D.ι ≫ sS) x hx y
  exact ⟨MvPolynomial.C r, by simpa [evalPt] using hr⟩

/-- If every closed point of `D.U` admits a pair of hyperplanes avoiding its fibre, the complex
over `R[u, v]` is split exact over the fraction field. -/
theorem generic_isSplitExact (hD : D.Realizes)
    (h0 : ∀ x : D.U, IsClosed ({x} : Set D.U) →
      ∃ a b : Fin (N + 1) → k, AvoidsPair (fibreImage g π q D.ι x) a b) :
    MMP.Chow.IsSplitExact D.e (D.A.map (algebraMap D.Pol (FractionRing D.Pol)))
      (D.B.map (algebraMap D.Pol (FractionRing D.Pol))) := by
  obtain ⟨x, hx⟩ := D.exists_isClosed_point
  obtain ⟨a, b, hab⟩ := h0 x hx
  exact isSplitExact_of_surjective_hom (D.evalPt x a b) (D.evalPt_surjective x hx a b)
    (hD.exact_of_avoid x hx a b hab)

/-- The scaling `u ↦ t u`, `v ↦ s v` of the universal pair of hyperplanes. -/
noncomputable def scale (t s : Γ(D.U, ⊤)) : D.Pol →+* D.Pol :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (Sum.elim (fun a => MvPolynomial.C t * MvPolynomial.X (Sum.inl a))
      (fun a => MvPolynomial.C s * MvPolynomial.X (Sum.inr a)))

/-- The scaling fixes constants. -/
theorem scale_C (t s r : Γ(D.U, ⊤)) : D.scale t s (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [scale]

/-- The scaling sends `u_a` to `t u_a`. -/
theorem scale_Xl (t s : Γ(D.U, ⊤)) (a : Fin (N + 1)) :
    D.scale t s (MvPolynomial.X (Sum.inl a)) = MvPolynomial.C t * MvPolynomial.X (Sum.inl a) := by
  simp [scale]

/-- The scaling sends `v_a` to `s v_a`. -/
theorem scale_Xr (t s : Γ(D.U, ⊤)) (a : Fin (N + 1)) :
    D.scale t s (MvPolynomial.X (Sum.inr a)) = MvPolynomial.C s * MvPolynomial.X (Sum.inr a) := by
  simp [scale]

/-- Scaling by units is injective. -/
theorem scale_injective (t s : Γ(D.U, ⊤)ˣ) :
    Function.Injective (D.scale (t : Γ(D.U, ⊤)) (s : Γ(D.U, ⊤))) := by
  refine Function.LeftInverse.injective (g := D.scale ((t⁻¹ : Γ(D.U, ⊤)ˣ) : Γ(D.U, ⊤))
    ((s⁻¹ : Γ(D.U, ⊤)ˣ) : Γ(D.U, ⊤))) (fun P => ?_)
  have : (D.scale ((t⁻¹ : Γ(D.U, ⊤)ˣ) : Γ(D.U, ⊤)) ((s⁻¹ : Γ(D.U, ⊤)ˣ) : Γ(D.U, ⊤))).comp
      (D.scale (t : Γ(D.U, ⊤)) (s : Γ(D.U, ⊤))) = RingHom.id _ := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · change D.scale _ _ (D.scale _ _ (MvPolynomial.C r)) = MvPolynomial.C r
      rw [scale_C, scale_C]
    · rcases i with a | a
      · change D.scale _ _ (D.scale _ _ (MvPolynomial.X (Sum.inl a))) = MvPolynomial.X (Sum.inl a)
        rw [scale_Xl, map_mul, scale_C, scale_Xl, ← mul_assoc, ← MvPolynomial.C_mul,
          Units.mul_inv, MvPolynomial.C_1, one_mul]
      · change D.scale _ _ (D.scale _ _ (MvPolynomial.X (Sum.inr a))) = MvPolynomial.X (Sum.inr a)
        rw [scale_Xr, map_mul, scale_C, scale_Xr, ← mul_assoc, ← MvPolynomial.C_mul,
          Units.mul_inv, MvPolynomial.C_1, one_mul]
  exact RingHom.congr_fun this P

/-- Scaling multiplies `ℓ_u : V₁ → V₀` by `t`. -/
theorem ellU₀_map_scale (t s : Γ(D.U, ⊤)) :
    D.ellU₀.map (D.scale t s) = (MvPolynomial.C t : D.Pol) • D.ellU₀ := by
  ext i j
  simp [ellU₀, Matrix.sum_apply, scale_Xl, scale_C, Finset.mul_sum, mul_assoc]

/-- Scaling multiplies `ℓ_v : V₁ → V₀` by `s`. -/
theorem ellV₀_map_scale (t s : Γ(D.U, ⊤)) :
    D.ellV₀.map (D.scale t s) = (MvPolynomial.C s : D.Pol) • D.ellV₀ := by
  ext i j
  simp [ellV₀, Matrix.sum_apply, scale_Xr, scale_C, Finset.mul_sum, mul_assoc]

/-- Scaling multiplies `ℓ_u : V₂ → V₁` by `t`. -/
theorem ellU₁_map_scale (t s : Γ(D.U, ⊤)) :
    D.ellU₁.map (D.scale t s) = (MvPolynomial.C t : D.Pol) • D.ellU₁ := by
  ext i j
  simp [ellU₁, Matrix.sum_apply, scale_Xl, scale_C, Finset.mul_sum, mul_assoc]

/-- Scaling multiplies `ℓ_v : V₂ → V₁` by `s`. -/
theorem ellV₁_map_scale (t s : Γ(D.U, ⊤)) :
    D.ellV₁.map (D.scale t s) = (MvPolynomial.C s : D.Pol) • D.ellV₁ := by
  ext i j
  simp [ellV₁, Matrix.sum_apply, scale_Xr, scale_C, Finset.mul_sum, mul_assoc]

/-- The first Koszul differential after scaling is `[-(s ℓ_v); t ℓ_u]`. -/
theorem A_map_scale (t s : Γ(D.U, ⊤)) :
    D.A.map (D.scale t s) = Matrix.fromRows (-((MvPolynomial.C s : D.Pol) • D.ellV₁))
      ((MvPolynomial.C t : D.Pol) • D.ellU₁) := by
  rw [← D.ellV₁_map_scale t s, ← D.ellU₁_map_scale t s]
  ext (i | i) j <;> simp [A]

/-- The second Koszul differential after scaling is `[t ℓ_u | s ℓ_v]`. -/
theorem B_map_scale (t s : Γ(D.U, ⊤)) :
    D.B.map (D.scale t s) = Matrix.fromCols ((MvPolynomial.C t : D.Pol) • D.ellU₀)
      ((MvPolynomial.C s : D.Pol) • D.ellV₀) := by
  rw [← D.ellV₀_map_scale t s, ← D.ellU₀_map_scale t s]
  ext i (j | j) <;> simp [B]

/-- The first Koszul differential under a ring map `f` is `[-(f ℓ_v); f ℓ_u]`. -/
theorem A_map_ring {T : Type*} [CommRing T] (f : D.Pol →+* T) :
    D.A.map f = Matrix.fromRows (-(D.ellV₁.map f)) (D.ellU₁.map f) := by
  ext (i | i) j <;> simp [A]

/-- The second Koszul differential under a ring map `f` is `[f ℓ_u | f ℓ_v]`. -/
theorem B_map_ring {T : Type*} [CommRing T] (f : D.Pol →+* T) :
    D.B.map f = Matrix.fromCols (D.ellU₀.map f) (D.ellV₀.map f) := by
  ext i (j | j) <;> simp [B]

/-- **Scaling the hyperplane pair scales the determinant**: `P(t u, s v) = (t s)^d P(u, v)`. -/
theorem scale_eq (hD : D.Realizes)
    (h0 : ∀ x : D.U, IsClosed ({x} : Set D.U) →
      ∃ a b : Fin (N + 1) → k, AvoidsPair (fibreImage g π q D.ι x) a b)
    (t s : Γ(D.U, ⊤)ˣ) (P : D.Pol)
    (hP : algebraMap D.Pol (FractionRing D.Pol) P = D.F) :
    D.scale t s P = MvPolynomial.C (((t : Γ(D.U, ⊤)) * s) ^ d) * P := by
  obtain ⟨φ, hφ⟩ := exists_fractionRing_lift (K := FractionRing D.Pol) (D.scale t s)
    (D.scale_injective t s)
  have hgen := D.generic_isSplitExact hD h0
  obtain ⟨-, hcd⟩ := MMP.Chow.complexDet_map (D.scale t s) φ hφ D.B_mul_A hgen
  have hAs : (D.A.map (D.scale t s)).map (algebraMap D.Pol (FractionRing D.Pol)) =
      Matrix.fromRows (-(algebraMap D.Pol (FractionRing D.Pol) (MvPolynomial.C (s : Γ(D.U, ⊤))) •
        D.ellV₁.map (algebraMap D.Pol (FractionRing D.Pol))))
        (algebraMap D.Pol (FractionRing D.Pol) (MvPolynomial.C (t : Γ(D.U, ⊤))) •
          D.ellU₁.map (algebraMap D.Pol (FractionRing D.Pol))) := by
    rw [A_map_scale, fromRows_neg_smul_map]
  have hBs : (D.B.map (D.scale t s)).map (algebraMap D.Pol (FractionRing D.Pol)) =
      Matrix.fromCols (algebraMap D.Pol (FractionRing D.Pol) (MvPolynomial.C (t : Γ(D.U, ⊤))) •
          D.ellU₀.map (algebraMap D.Pol (FractionRing D.Pol)))
        (algebraMap D.Pol (FractionRing D.Pol) (MvPolynomial.C (s : Γ(D.U, ⊤))) •
          D.ellV₀.map (algebraMap D.Pol (FractionRing D.Pol))) := by
    rw [B_map_scale, fromCols_smul_map]
  have ht' := algebraMap_C_unit_ne_zero (ι := Fin (N + 1) ⊕ Fin (N + 1)) (R := Γ(D.U, ⊤))
    (K := FractionRing D.Pol) t
  have hs' := algebraMap_C_unit_ne_zero (ι := Fin (N + 1) ⊕ Fin (N + 1)) (R := Γ(D.U, ⊤))
    (K := FractionRing D.Pol) s
  have hAk := D.A_map_ring (algebraMap D.Pol (FractionRing D.Pol))
  have hBk := D.B_map_ring (algebraMap D.Pol (FractionRing D.Pol))
  have hBA := MMP.Chow.map_mul_eq_zero (K := FractionRing D.Pol) D.B_mul_A
  rw [hAk, hBk] at hBA hgen
  have key := cayleyDet_scale D.e _ _ _ _ _ _ ht' hs' hBA hgen d (by simp [D.rank₀])
  have hcd' : MMP.Chow.cayleyDet D.e
      ((D.A.map (D.scale t s)).map (algebraMap D.Pol (FractionRing D.Pol)))
      ((D.B.map (D.scale t s)).map (algebraMap D.Pol (FractionRing D.Pol))) = φ D.F := hcd
  rw [hAs, hBs, key] at hcd'
  have hF : MMP.Chow.cayleyDet D.e
      (Matrix.fromRows (-(D.ellV₁.map (algebraMap D.Pol (FractionRing D.Pol))))
        (D.ellU₁.map (algebraMap D.Pol (FractionRing D.Pol))))
      (Matrix.fromCols (D.ellU₀.map (algebraMap D.Pol (FractionRing D.Pol)))
        (D.ellV₀.map (algebraMap D.Pol (FractionRing D.Pol)))) = D.F := by
    rw [← hAk, ← hBk]
    rfl
  rw [hF, ← hP, ← RingHom.comp_apply φ, hφ, RingHom.comp_apply] at hcd'
  apply IsFractionRing.injective D.Pol (FractionRing D.Pol)
  rw [← hcd']
  simp only [map_mul, map_pow]

/-- The coefficients of the scaled polynomial. -/
theorem scale_coeff (t s : Γ(D.U, ⊤)) (P : D.Pol) (e : (Fin (N + 1) ⊕ Fin (N + 1)) →₀ ℕ) :
    (D.scale t s P).coeff e =
      t ^ (∑ j, e (Sum.inl j)) * s ^ (∑ j, e (Sum.inr j)) * P.coeff e := by
  induction P using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [show D.scale t s (MvPolynomial.monomial u a) = MvPolynomial.monomial u
        (t ^ (∑ j, u (Sum.inl j)) * s ^ (∑ j, u (Sum.inr j)) * a) from
      map_monomial_eq_of_map_X t s (D.scale t s) (D.scale_C t s) (D.scale_Xl t s)
        (D.scale_Xr t s) u a]
    by_cases h : u = e
    · subst h; simp [MvPolynomial.coeff_monomial]
    · simp [MvPolynomial.coeff_monomial, h]
  | add p q hp hq => simp [map_add, hp, hq, mul_add]

/-- Every monomial `u^α v^β` in the support of a polynomial representing `D.F` satisfies
`t^{|α|} s^{|β|} = (t s)^d` for all units `t`, `s`. -/
theorem scale_coeff_eq (hD : D.Realizes)
    (h0 : ∀ x : D.U, IsClosed ({x} : Set D.U) →
      ∃ a b : Fin (N + 1) → k, AvoidsPair (fibreImage g π q D.ι x) a b)
    (t s : Γ(D.U, ⊤)ˣ) (P : D.Pol) (hP : algebraMap D.Pol (FractionRing D.Pol) P = D.F)
    (e : (Fin (N + 1) ⊕ Fin (N + 1)) →₀ ℕ) (he : e ∈ P.support) :
    (t : Γ(D.U, ⊤)) ^ (∑ j, e (Sum.inl j)) * (s : Γ(D.U, ⊤)) ^ (∑ j, e (Sum.inr j)) =
      ((t : Γ(D.U, ⊤)) * s) ^ d := by
  have h1 := MvPolynomial.ext_iff.mp (D.scale_eq hD h0 t s P hP) e
  rw [D.scale_coeff, MvPolynomial.coeff_C_mul] at h1
  exact mul_right_cancel₀ (MvPolynomial.mem_support_iff.mp he) h1

end LocalFreeData

/-! ### Avoiding pairs of hyperplanes and the Koszul family -/

section CoreLemmas

/-! #### Topological input of the avoiding pair -/

/-- A specialization of the image lifts along a closed map. -/
theorem exists_specializes_lift {F G : Type*} [TopologicalSpace F] [TopologicalSpace G]
    {φ : F → G} (hφ : IsClosedMap φ) {z : F} {w : G} (h : φ z ⤳ w) :
    ∃ z' : F, z ⤳ z' ∧ φ z' = w :=
  hφ.specializingMap h

/-- A space of Krull dimension at most one has no chain `a ⤳ b ⤳ c` of three distinct points. -/
theorem not_chain_of_topologicalKrullDim_le_one {F : Type*} [TopologicalSpace F] [T0Space F]
    (h : topologicalKrullDim F ≤ 1) {a b c : F} (hab : a ⤳ b) (hbc : b ⤳ c) (hab' : a ≠ b)
    (hbc' : b ≠ c) : False := by
  let I : F → TopologicalSpace.IrreducibleCloseds F := fun x =>
    ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  have key : ∀ x y : F, x ⤳ y → x ≠ y → I y < I x := by
    intro x y hxy hne
    refine lt_of_le_of_ne ?_ ?_
    · change closure {y} ⊆ closure {x}
      exact closure_minimal (by simpa using specializes_iff_mem_closure.mp hxy) isClosed_closure
    · intro heq
      have : (I y : Set F) = I x := congrArg SetLike.coe heq
      have hx : x ∈ (I y : Set F) := by
        rw [this]
        exact subset_closure rfl
      exact hne ((specializes_iff_mem_closure.mpr hx).antisymm hxy).eq.symm
  let s1 : LTSeries (TopologicalSpace.IrreducibleCloseds F) :=
    (RelSeries.singleton _ (I c)).snoc (I b) (key b c hbc hbc')
  have hl : s1.last = I b := RelSeries.last_snoc _ _ _
  let s : LTSeries (TopologicalSpace.IrreducibleCloseds F) :=
    s1.snoc (I a) (by rw [hl]; exact key a b hab hab')
  have h1 := Order.LTSeries.length_le_krullDim s
  have h2 : (s.length : WithBot ℕ∞) = 2 := rfl
  have : (2 : WithBot ℕ∞) ≤ 1 := by
    have := h1.trans h
    simpa [h2] using this
  exact absurd this (by decide)

/-- A point of a proper `k`-scheme with no chain of three points below it is closed or the
generic point of a proper curve. -/
theorem isClosed_or_isProperCurve {G : Scheme.{u}} (sG : G ⟶ Spec (.of k))
    [IsProper sG] (y : G)
    (hno : ∀ w₁ w₂ : G, y ⤳ w₁ → w₁ ⤳ w₂ → y ≠ w₁ → w₁ ≠ w₂ → False) :
    IsClosed ({y} : Set G) ∨ Mori.IsProperCurve sG y := by
  by_cases hy : IsClosed ({y} : Set G)
  · exact Or.inl hy
  right
  haveI : CompactSpace G := QuasiCompact.compactSpace_of_compactSpace sG
  obtain ⟨p, hp, hpc⟩ :=
    (isClosed_closure : IsClosed (closure ({y} : Set G))).exists_closed_singleton
      ⟨y, subset_closure rfl⟩
  have hyp : y ⤳ p := specializes_iff_mem_closure.mpr hp
  have hne : y ≠ p := by rintro rfl; exact hy hpc
  refine ⟨MMP.Fourfold.topologicalKrullDim_curveSubschemeAt_eq_one sG hyp hne hpc ?_, ?_⟩
  · intro z hyz hzp
    by_contra hcon
    push Not at hcon
    exact hno z p hyz hzp (Ne.symm hcon.1) hcon.2
  · infer_instance

/-- A nonzero linear polynomial vanishing at the coefficient vectors of the hyperplanes through a
point of `ℙᴺ`. -/
theorem exists_poly_of_point (y : AlgebraicGeometry.Proj (polyGrading k N)) :
    ∃ P : MvPolynomial (Fin (N + 1)) k, P ≠ 0 ∧
      ∀ u, linForm u ∈ y.asHomogeneousIdeal → eval u P = 0 := by
  classical
  haveI : y.asHomogeneousIdeal.toIdeal.IsPrime := y.isPrime
  obtain ⟨j, hj⟩ := exists_notMem_X (k := k) (N := N) (𝔭 := y.asHomogeneousIdeal.toIdeal)
    y.not_irrelevant_le
  let lin : (Fin (N + 1) → k) →ₗ[k] MvPolynomial (Fin (N + 1)) k :=
    Fintype.linearCombination k (fun j => (X j : MvPolynomial (Fin (N + 1)) k))
  have hlin : ∀ u, lin u = linForm u := fun u => by
    simp [lin, linForm, Fintype.linearCombination_apply, MvPolynomial.smul_eq_C_mul]
  let W : Submodule k (Fin (N + 1) → k) :=
    Submodule.comap lin (Submodule.restrictScalars k y.asHomogeneousIdeal.toIdeal)
  have hmem : ∀ u, u ∈ W ↔ linForm u ∈ y.asHomogeneousIdeal.toIdeal := fun u => by
    simp [W, hlin]
  have hWlt : W < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hj ?_
    have : (Pi.single j (1 : k) : Fin (N + 1) → k) ∈ W := h ▸ Submodule.mem_top
    have h2 := (hmem _).mp this
    have h3 : linForm (Pi.single j (1 : k) : Fin (N + 1) → k) = X j := by
      simp [linForm, Pi.single_apply]
    rwa [h3] at h2
  obtain ⟨f, hf0, hWf⟩ := Submodule.exists_le_ker_of_lt_top W hWlt
  have hev : ∀ b, eval b (∑ i, MvPolynomial.C (f (Pi.single i (1 : k))) * X i) = f b := by
    intro b
    simp only [map_sum, map_mul, eval_C, eval_X]
    conv_rhs => rw [LinearMap.pi_apply_eq_sum_univ f b]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, mul_comm]
    congr 2
    ext l
    simp [Pi.single_apply, eq_comm]
  refine ⟨_, fun h0 => hf0 (LinearMap.ext fun b => ?_), fun u hu => (hev u).trans
    (hWf ((hmem u).2 hu))⟩
  rw [← hev, h0, map_zero, LinearMap.zero_apply]

/-- **A nonzero polynomial in the pair of hyperplanes for each point of dimension at most one.**
If `y` is a closed point or the generic point of a proper curve, a pair of hyperplanes
`(u, v)` at which the polynomial does not vanish has no common point on the closure of `y`. -/
theorem exists_poly_avoid (y : AlgebraicGeometry.Proj (polyGrading k N))
    (hy : IsClosed ({y} : Set (AlgebraicGeometry.Proj (polyGrading k N))) ∨
      Mori.IsProperCurve (projToSpecCoeff k N) y) :
    ∃ P : MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k, P ≠ 0 ∧ ∀ u v : Fin (N + 1) → k,
      eval (Sum.elim u v) P ≠ 0 →
        ∀ p ∈ closure ({y} : Set (AlgebraicGeometry.Proj (polyGrading k N))),
          ¬ (linForm u ∈ ProjectiveSpectrum.asHomogeneousIdeal p ∧
            linForm v ∈ ProjectiveSpectrum.asHomogeneousIdeal p) := by
  classical
  rcases hy with hy | hy
  · obtain ⟨P, hP0, hP⟩ := exists_poly_of_point y
    refine ⟨rename Sum.inl P, (map_ne_zero_iff _ (rename_injective _ Sum.inl_injective)).2 hP0,
      fun u v hne p hp hb => ?_⟩
    rw [hy.closure_eq, Set.mem_singleton_iff] at hp
    subst hp
    rw [eval_rename, Sum.elim_comp_inl] at hne
    exact hne (hP u hb.1)
  · obtain ⟨G, hG⟩ := exists_incForm (⟨y, hy⟩ : Mori.ProperCurve (projToSpecCoeff k N))
    exact ⟨G, hG.1.ne_zero, fun u v hne p hp hb => hne ((hG.2 u v).mpr ⟨p, hp, hb.1, hb.2⟩)⟩

/-- The map from the fibre over `t` to `ℙᴺ`. -/
noncomputable abbrev fibrePsi (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    {S 𝒞 : Scheme.{u}} (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (t : S) :
    π.fiber t ⟶ AlgebraicGeometry.Proj (polyGrading k N) :=
  π.fiberι t ≫ q ≫ g

/-- The generic points of the irreducible components of the fibre over `t`. -/
def fibreComponents {S 𝒞 : Scheme.{u}} (π : 𝒞 ⟶ S) (t : S) : Set (π.fiber t) :=
  {ξ | closure ({ξ} : Set (π.fiber t)) ∈ irreducibleComponents (π.fiber t)}

/-- **The structure of a closed fibre.** The fibre over a closed point is proper over `k` of
dimension at most one; it has finitely many irreducible components, every point lies on one, and
each component maps to a closed point or onto a proper curve of `ℙᴺ`. -/
theorem fibre_facts {S 𝒞 : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k))
    (hS : Mori.IsNormalVariety k sS) (hY : IsProjectiveMorphism sY)
    (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)) (hg : IsProjectiveMorphism g)
    (hgY : g ≫ projToSpecCoeff k N = sY)
    (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (hπq : π ≫ sS = q ≫ sY)
    [IsClosedImmersion (pullback.lift π q hπq)] [IsProper π] [Flat π]
    (hdim : ∀ s : S, IsClosed ({s} : Set S) → topologicalKrullDim (π.fiber s) = 1)
    (t : S) (ht : IsClosed ({t} : Set S)) :
    IsProper (fibrePsi g π q t) ∧ IsProper (π.fiberι t ≫ π ≫ sS) ∧
      topologicalKrullDim (π.fiber t) ≤ 1 ∧ (fibreComponents π t).Finite ∧
      (∀ y, ∃ ξ ∈ fibreComponents π t, ξ ⤳ y) ∧
      ∀ ξ ∈ fibreComponents π t, IsClosed ({fibrePsi g π q t ξ} : Set _) ∨
        Mori.IsProperCurve (projToSpecCoeff k N) (fibrePsi g π q t ξ) := by
  classical
  haveI : LocallyOfFiniteType sS := hS.1.toLocallyOfFiniteType
  set φ := fibrePsi g π q t with hφ
  have hφs : φ ≫ projToSpecCoeff k N = π.fiberι t ≫ π ≫ sS := by
    rw [hφ, Category.assoc, Category.assoc, hgY, ← hπq]
  have hbij := kEval_bijective sS t ht
  haveI : IsIso (CommRingCat.ofHom (kEval sS t)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  haveI hFprop : IsProper (π.fiberι t ≫ π ≫ sS) := by
    rw [fiber_structure_eq sS π t]
    have hbig : IsPullback (π.fiberι t) (π.fiberToSpecResidueField t) π
        (S.fromSpecResidueField t) := IsPullback.of_hasPullback _ _
    haveI : IsProper (π.fiberToSpecResidueField t) :=
      MorphismProperty.of_isPullback (P := @IsProper) hbig ‹IsProper π›
    haveI : IsProper (Spec.map (CommRingCat.ofHom (kEval sS t))) := inferInstance
    exact MorphismProperty.comp_mem _ _ _ ‹_› ‹_›
  haveI : IsProper (projToSpecCoeff k N) :=
    Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff k N
  haveI hφp : IsProper φ := by
    haveI : IsProper (φ ≫ projToSpecCoeff k N) := by rwa [hφs]
    exact IsProper.of_comp φ (projToSpecCoeff k N)
  have hclosed : IsClosedMap φ := φ.isClosedMap
  have hdimF : topologicalKrullDim (π.fiber t) ≤ 1 := (hdim t ht).le
  haveI : LocallyOfFiniteType (π.fiberι t ≫ π ≫ sS) := hFprop.toLocallyOfFiniteType
  haveI : QuasiCompact (π.fiberι t ≫ π ≫ sS) :=
    @instQuasiCompactOfUniversallyClosed _ _ _ hFprop.toUniversallyClosed
  haveI : IsLocallyNoetherian (π.fiber t) :=
    LocallyOfFiniteType.isLocallyNoetherian (π.fiberι t ≫ π ≫ sS)
  haveI : CompactSpace (π.fiber t) :=
    QuasiCompact.compactSpace_of_compactSpace (π.fiberι t ≫ π ≫ sS)
  haveI : AlgebraicGeometry.IsNoetherian (π.fiber t) := AlgebraicGeometry.IsNoetherian.mk
  refine ⟨hφp, hFprop, hdimF, ?_, ?_, ?_⟩
  · exact Set.Finite.of_injOn (f := fun ξ => closure ({ξ} : Set (π.fiber t))) (fun ξ hξ => hξ)
      (fun a _ b _ hab => (inseparable_iff_closure_eq.mpr hab).eq)
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  · intro z
    obtain ⟨ξ, hξ⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := z))
      isClosed_irreducibleComponent
    have hcl : closure ({ξ} : Set (π.fiber t)) = irreducibleComponent z := hξ.def
    refine ⟨ξ, ?_, ?_⟩
    · change closure ({ξ} : Set (π.fiber t)) ∈ irreducibleComponents (π.fiber t)
      rw [hcl]
      exact irreducibleComponent_mem_irreducibleComponents z
    · rw [specializes_iff_mem_closure, hcl]
      exact mem_irreducibleComponent
  · intro ξ _
    refine isClosed_or_isProperCurve (projToSpecCoeff k N) (φ ξ) fun w₁ w₂ h1 h2 h3 h4 => ?_
    obtain ⟨z₁, hz₁, rfl⟩ := hclosed.specializingMap h1
    obtain ⟨z₂, hz₂, rfl⟩ := hclosed.specializingMap h2
    exact not_chain_of_topologicalKrullDim_le_one hdimF hz₁ hz₂ (fun h => h3 (by rw [h]))
      (fun h => h4 (by rw [h]))

/-- The image of the fibre over a closed point of an open of the base is the image of the fibre of
the original family. -/
theorem fibreImage_eq_range {S 𝒞 U : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    [LocallyOfFiniteType sS] (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)) (π : 𝒞 ⟶ S)
    (q : 𝒞 ⟶ Y) (ι : U ⟶ S) [IsOpenImmersion ι] (x : U) (hx : IsClosed ({x} : Set U)) :
    fibreImage g π q ι x = Set.range (π.fiberι (ι x) ≫ q ≫ g) := by
  obtain ⟨e, he⟩ := exists_fiber_iso sS (ι ≫ sS) π ι rfl x hx
  have hcomp : (pullback.snd π ι).fiberι x ≫ pullback.fst π ι ≫ q ≫ g =
      e.hom ≫ π.fiberι (ι x) ≫ q ≫ g := by
    rw [← Category.assoc e.hom (π.fiberι (ι x)), he]
    simp
  unfold fibreImage
  rw [hcomp]
  ext p
  simp only [Set.mem_range, Scheme.Hom.comp_apply]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨e.hom z, rfl⟩
  · rintro ⟨z, rfl⟩
    refine ⟨e.inv z, ?_⟩
    have : e.hom (e.inv z) = z := by rw [← Scheme.Hom.comp_apply]; simp
    rw [this]

/-- **An avoiding pair of hyperplanes.** For each closed point of an open of the base there is a
pair of hyperplanes of `ℙᴺ` without common point on the (at most one-dimensional) image of the
fibre. -/
theorem exists_avoidsPair {S 𝒞 : Scheme.{u}} (sS : S ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    (hS : Mori.IsNormalVariety k sS) (hY : IsProjectiveMorphism sY)
    (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)) (hg : IsProjectiveMorphism g)
    (hgY : g ≫ projToSpecCoeff k N = sY)
    (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (hπq : π ≫ sS = q ≫ sY)
    [IsClosedImmersion (pullback.lift π q hπq)] [IsProper π] [Flat π]
    (hdim : ∀ s : S, IsClosed ({s} : Set S) → topologicalKrullDim (π.fiber s) = 1)
    {U : Scheme.{u}} (ι : U ⟶ S) [IsOpenImmersion ι] (x : U) (hx : IsClosed ({x} : Set U)) :
    ∃ a b : Fin (N + 1) → k, AvoidsPair (fibreImage g π q ι x) a b := by
  classical
  haveI : LocallyOfFiniteType sS := hS.1.toLocallyOfFiniteType
  rw [fibreImage_eq_range sS g π q ι x hx]
  obtain ⟨-, -, -, hfin, hcover, hclass⟩ := fibre_facts sS sY hS hY g hg hgY π q hπq hdim (ι x)
    (isClosed_image_of_isClosed sS (ι ≫ sS) ι rfl x hx)
  choose! P hP using fun ξ hξ => exists_poly_avoid (fibrePsi g π q (ι x) ξ) (hclass ξ hξ)
  let Q : MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k := ∏ ξ ∈ hfin.toFinset, P ξ
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun ξ hξ => (hP ξ (hfin.mem_toFinset.mp hξ)).1
  obtain ⟨w, hw⟩ : ∃ w, eval w Q ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hQ (MvPolynomial.funext fun w => by simpa using hcon w)
  refine ⟨w ∘ Sum.inl, w ∘ Sum.inr, ?_⟩
  rintro p ⟨z, rfl⟩
  obtain ⟨ξ, hξ, hξz⟩ := hcover z
  have hne : eval (Sum.elim (w ∘ Sum.inl) (w ∘ Sum.inr)) (P ξ) ≠ 0 := by
    rw [Sum.elim_comp_inl_inr]
    simp only [Q, map_prod] at hw
    exact (Finset.prod_ne_zero_iff.mp hw) ξ (hfin.mem_toFinset.mpr hξ)
  exact (hP ξ hξ).2 _ _ hne _
    (specializes_iff_mem_closure.mp (hξz.map (fibrePsi g π q (ι x)).continuous))

/-! #### The sheaf-theoretic data behind the local free data

The family `π : 𝒞 ⟶ S` carries the pull-back `H` of `𝒪(1)` along `q ≫ g` with its coordinate
sections `x_a`, and an invertible module `A` which is relatively ample over `S`.  For `n` large
the direct images of the twists `H^{-j} ⊗ A^n`, `j = 0, 1, 2`, have no higher direct images and
commute with every base change
(`MMP.Chow.exists_forall_isZero_higherDirectImage_and_isFiniteLocallyFree_and_isIso_baseChange`);
over an affine open `W` where they are free, multiplication by `x_a` has matrices
(`MMP.Chow.KoszulSheafData.matrix₀`, `MMP.Chow.KoszulSheafData.matrix₁`) which commute. -/

section KoszulBridge

open Stacks.Ample in
/-- The pull-back to the family of the hyperplane bundle `𝒪(1)` of `ℙᴺ`, along `q ≫ g`. -/
noncomputable abbrev hyperplaneBundle (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    {𝒞 : Scheme.{u}} (q : 𝒞 ⟶ Y) : 𝒞.Modules :=
  (Scheme.Modules.pullback (q ≫ g)).obj
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k N) 1)

/-- The pull-back of `𝒪(1)` to the family is invertible. -/
instance isInvertibleModule_hyperplaneBundle (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    {𝒞 : Scheme.{u}} (q : 𝒞 ⟶ Y) : Stacks.Ample.IsInvertibleModule 𝒞 (hyperplaneBundle g q) :=
  haveI := Stacks.PicardUFD.isInvertible_twistingSheaf k N 1
  Stacks.InvertiblePullback.isInvertibleModule_pullback (q ≫ g) _

/-- The `a`-th coordinate section of `H`: the pull-back of the coordinate `x_a ∈ Γ(ℙᴺ, 𝒪(1))`. -/
noncomputable def coordSection (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    {𝒞 : Scheme.{u}} (q : 𝒞 ⟶ Y) (a : Fin (N + 1)) : Γ(hyperplaneBundle g q, ⊤) :=
  (pullbackGlobalSections (q ≫ g) (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k N) 1)).hom
    (ProjectiveSpectrum.Proj.degreeSection (polyGrading k N) 1
      ⟨MvPolynomial.X a,
        (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_X k a)⟩)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The uniform vanishing and base change statements for the three twists
`H^{m} ⊗ A^n`, `m = -2, -1, 0`, as given by
`MMP.Chow.exists_forall_isZero_higherDirectImage_and_isFiniteLocallyFree_and_isIso_baseChange`. -/
structure UniformTwist {𝒞 S : Scheme.{u}} (π : 𝒞 ⟶ S) (H A : 𝒞.Modules)
    [Stacks.Ample.IsInvertibleModule 𝒞 H] [Stacks.Ample.IsInvertibleModule 𝒞 A] (n : ℕ) : Prop where
  /-- The higher direct images of the three twists vanish. -/
  higher_zero : ∀ m : ℤ, (m = -2 ∨ m = -2 + 1 ∨ m = -2 + 1 + 1) → ∀ i : ℤ, 0 < i →
    IsZero (((Scheme.Modules.pushforward π).rightDerivedPlus i).obj (MMP.Chow.twistMod H A n m))
  /-- The direct images of the three twists commute with base change along any pullback
  square. -/
  base_change : ∀ m : ℤ, (m = -2 ∨ m = -2 + 1 ∨ m = -2 + 1 + 1) →
    ∀ {X' S' : Scheme.{u}} (g' : S' ⟶ S) (f' : X' ⟶ S') (g'' : X' ⟶ 𝒞)
      (hsq : IsPullback g'' f' π g'),
      IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans hsq.w).app
        (MMP.Chow.twistMod H A n m))

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The geometric input of the local free data**: an invertible module `A`, relatively ample over
`S`, an exponent `n` for which the direct images of the three twists are well behaved, and an
affine open `W ∋ s` over which they are free with bases of ranks `r₀ = r₁ + d`, `r₁ = r₂ + d`. -/
structure KoszulFamily (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    {S 𝒞 : Scheme.{u}} (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (d : ℕ) (s : S) where
  /-- The invertible module `A`, relatively ample over `S`. -/
  A : 𝒞.Modules
  [invertible : Stacks.Ample.IsInvertibleModule 𝒞 A]
  /-- The exponent of `A` in the twists. -/
  n : ℕ
  /-- `A` is relatively ample over `S`. -/
  ample : Stacks.RelativeAmple.IsRelativelyAmple π A
  /-- The direct images of the three twists vanish in positive degree and commute with base
  change. -/
  uniform : UniformTwist π (hyperplaneBundle g q) A n
  /-- The affine open `W` with bases of the direct images and the matrices of multiplication by
  sections of `H`. -/
  data : MMP.Chow.KoszulSheafData π (hyperplaneBundle g q) A n
  /-- The point `s` lies in `W`. -/
  mem : s ∈ data.W
  /-- `W` is affine. -/
  affine : IsAffineOpen data.W
  /-- `r₀ = r₁ + d`. -/
  rank₀ : data.r₀ = data.r₁ + d
  /-- `r₁ = r₂ + d`. -/
  rank₁ : data.r₁ = data.r₂ + d
  /-- The higher cohomology of the three twists restricted to `π⁻¹ W` vanishes. -/
  vanishing : ∀ m : ℤ, (m = -2 ∨ m = -2 + 1 ∨ m = -2 + 1 + 1) → ∀ p : ℕ, 0 < p → Subsingleton
    (((AlgebraicGeometry.moduleGlobalSections (π ⁻¹ᵁ data.W)).rightDerived p).obj
      ((Scheme.Modules.pullback (π ⁻¹ᵁ data.W).ι).obj
        (MMP.Chow.twistMod (hyperplaneBundle g q) A n m)))

attribute [local instance] KoszulFamily.invertible

/-- The local free data attached to a `KoszulFamily`: the open `W` as a scheme, with the matrices
of multiplication by the coordinate sections `x_a`, transported to `Γ(W, ⊤)`. -/
noncomputable def KoszulFamily.toLocalFreeData
    {g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)} {S 𝒞 : Scheme.{u}} {sS : S ⟶ Spec (.of k)}
    {π : 𝒞 ⟶ S} {q : 𝒞 ⟶ Y} {d : ℕ} {s : S} (F : KoszulFamily g π q d s)
    (hS : Mori.IsNormalVariety k sS) : LocalFreeData g sS π q d s :=
  haveI : IsIntegral S := hS.1.toIsIntegral
  haveI : IsNormal S := hS.2
  haveI : LocallyOfFiniteType sS := hS.1.toLocallyOfFiniteType
  haveI : Nonempty F.data.W := ⟨⟨s, F.mem⟩⟩
  haveI : IsAffine (F.data.W : Scheme.{u}) := F.affine
  haveI : IsLocallyNoetherian S := AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian sS
  haveI : IsIntegrallyClosed Γ((F.data.W : Scheme.{u}), ⊤) := normal_globalSections _
  haveI : IsNoetherianRing Γ((F.data.W : Scheme.{u}), ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  { U := F.data.W
    ι := F.data.W.ι
    mem := ⟨⟨s, F.mem⟩, rfl⟩
    locFT := inferInstance
    r₀ := F.data.r₀
    r₁ := F.data.r₁
    r₂ := F.data.r₂
    X₀ := fun a => (F.data.matrix₀ (coordSection g q a)).map (F.data.W.topIso.inv).hom
    X₁ := fun a => (F.data.matrix₁ (coordSection g q a)).map (F.data.W.topIso.inv).hom
    comm := fun a b => by
      rw [← Matrix.map_mul, ← Matrix.map_mul, F.data.matrix₀_mul_matrix₁_comm]
    rank₀ := F.rank₀
    rank₁ := F.rank₁ }

end KoszulBridge

end CoreLemmas

end Skeleton

end Defs

end MMP.Chow.DeterminantCurveForm
