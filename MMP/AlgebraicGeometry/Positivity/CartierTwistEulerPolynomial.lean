module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Intersection.OneCycles
public import MMP.AlgebraicGeometry.Divisor.LinearSeries
public import MMP.AlgebraicGeometry.Divisor.CartierLineBundle
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.EulerPolynomialProper
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFibreEulerCharacteristicUnconditional
public import StacksFrontier.AlgebraicGeometry.CurveEulerBridge.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.PositivityZeroDim
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafMul

/-!
# Euler characteristics of Cartier twists and very ample multiples

For a scheme `X` proper over a field `k` and Cartier divisors `L₁, …, L_r` on `X`, the function
`(k₁, …, k_r) ↦ χ(X, 𝒪_X(∑ᵢ kᵢ Lᵢ))` is a polynomial with rational coefficients of total
degree at most `dim X`; and for an ample Cartier divisor `L`, the multiple `νL` is very ample for
every `ν ≫ 0`.

## Main results

* `MMP.Resolution.Bridges.exists_polynomial_eulerChar_cartierSheaf_sum`: Snapper's polynomiality
  of `χ(X, 𝒪_X(∑ᵢ kᵢ Lᵢ))`.
* `MMP.Resolution.Bridges.lineBundle_nsmul_iso_tensorPow`: `𝒪_X(νL) ≅ 𝒪_X(L)^{⊗ ν}`, the bridge
  for very ampleness of multiples.

## Implementation notes

* `𝒪_X(D)` in the Euler characteristic statement is `MMP.CartierDivisor.sheaf D`,
  invertible by `MMP.Mori.isInvertible_cartierSheaf`; very ampleness and ampleness are the
  notions `MMP.Intersection.IsVeryAmpleDivisor` and `MMP.Intersection.IsAmpleDivisor` (Lazarsfeld
  Def. 1.2.1), which are stated through `MMP.CartierDivisor.sheaf D`.
* The Euler characteristic is written as the alternating sum
  `∑ⱼ (-1)ʲ dim_k Hʲ(X, 𝒪_X(D))` of the dimensions of `AlgebraicGeometry.cohomologyOverField`,
  which is `AlgebraicGeometry.eulerCharacteristic` by definition and needs no coherence instance.
* The library results `AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_isProper`
  (Stacks 0BEM) and `Stacks.AmpleRelativeFiniteType.tfae_six` are phrased with tensor powers of
  invertible modules; the bridges `cartierSheaf_sum_iso_twistedSheaf` and
  `lineBundle_nsmul_iso_tensorPow` identify the sheaf of a linear combination of Cartier divisors
  with the corresponding tensor product of powers.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace MMP.Resolution.Bridges

/-! ### Auxiliary identifications -/

section Aux

open Stacks.SheafOfModules.Invertible

variable {X : Scheme.{u}}

private noncomputable abbrev sh (D : X.CartierDivisor) := MMP.CartierDivisor.sheaf D

private noncomputable abbrev tens (X : Scheme.{u}) : X.Modules ⥤ X.Modules ⥤ X.Modules :=
  Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat) (X.ringCatSheaf.2)⟩

private theorem cancel (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] {A B : X.Modules}
    (h : ((tens X).obj A).obj L ≅ ((tens X).obj B).obj L) : Nonempty (A ≅ B) := by
  haveI : ((tens X).flip.obj L).IsEquivalence := (isInvertible_iff_tensorRightFunctor_isEquivalence X.presheaf X.ringCatSheaf.2 L).1 inferInstance
  exact ⟨((tens X).flip.obj L).preimageIso h⟩

private theorem sheaf_zero_iso : Nonempty
    (CartierDivisor.sheaf (0 : X.CartierDivisor) ≅ SheafOfModules.unit X.ringCatSheaf) := by
  set s0 := MMP.CartierDivisor.sheaf (0 : X.CartierDivisor)
  have h1 : ((tens X).obj (SheafOfModules.unit X.ringCatSheaf)).obj s0 ≅ s0 :=
    (tensorPowerSuccIso X.presheaf X.ringCatSheaf.2 s0 0).symm ≪≫
      tensorPowerReindex X.presheaf X.ringCatSheaf.2 s0 (by norm_num : (0:ℤ) + 1 = 1) ≪≫
      tensorPowerOneIso X.presheaf X.ringCatSheaf.2 s0
  have h2 : ((tens X).obj s0).obj s0 ≅ s0 :=
    MMP.CartierDivisorSheaf.sheafMulIso (0 : X.CartierDivisor) 0 ≪≫
      eqToIso (by rw [add_zero])
  exact cancel s0 (h2.trans h1.symm)

open MMP.CartierDivisorSheaf in
private theorem nsmul_iso (D : X.CartierDivisor) (n : ℤ) :
    Nonempty (MMP.CartierDivisor.sheaf (n • D) ≅
      tensorPower X.presheaf X.ringCatSheaf.2 (MMP.CartierDivisor.sheaf D) n) := by
  set L := MMP.CartierDivisor.sheaf D
  induction n using Int.induction_on with
  | zero =>
    obtain ⟨e⟩ := sheaf_zero_iso (X := X)
    exact ⟨eqToIso (by rw [zero_smul]) ≪≫ e⟩
  | succ i ih =>
    obtain ⟨e⟩ := ih
    have h : (sh (((i : ℤ) + 1) • D)) ≅ ((tens X).obj (sh ((i:ℤ) • D))).obj L :=
      eqToIso (by rw [add_smul, one_smul]) ≪≫ (sheafMulIso ((i:ℤ) • D) D).symm
    exact ⟨h ≪≫ ((tens X).obj _).mapIso (Iso.refl L) ≪≫ ((tens X).mapIso e).app L ≪≫
      tensorPowerSuccIso X.presheaf X.ringCatSheaf.2 L i⟩
  | pred i ih =>
    obtain ⟨e⟩ := ih
    have h : ((tens X).obj (sh ((-(i:ℤ) - 1) • D))).obj L ≅ sh ((-(i:ℤ)) • D) :=
      sheafMulIso _ D ≪≫ eqToIso (by rw [sub_smul, one_smul, sub_add_cancel])
    have h2 : ((tens X).obj (tensorPower X.presheaf X.ringCatSheaf.2 L (-(i:ℤ) - 1))).obj L ≅
        sh ((-(i:ℤ)) • D) :=
      tensorPowerSuccIso X.presheaf X.ringCatSheaf.2 L _ ≪≫
        tensorPowerReindex X.presheaf X.ringCatSheaf.2 L (n := -(i:ℤ) - 1 + 1) (m := -(i:ℤ)) (by ring) ≪≫ e.symm
    exact (cancel L (h.trans h2.symm))

open MMP.CartierDivisorSheaf in
private theorem fold_iso {r : ℕ} (L : Fin r → X.CartierDivisor) (n : Fin r → ℤ) (l : List (Fin r)) :
    ∀ (M : X.Modules) (D : X.CartierDivisor), Nonempty (sh D ≅ M) →
      Nonempty (l.foldl (fun M i => ((tens X).obj M).obj
        (tensorPower X.presheaf X.ringCatSheaf.2 (sh (L i)) (n i))) M ≅
        sh (D + (l.map fun i => n i • L i).sum)) := by
  induction l with
  | nil => intro M D ⟨e⟩; exact ⟨e.symm ≪≫ eqToIso (by simp)⟩
  | cons a l ih =>
    intro M D ⟨e⟩
    obtain ⟨e'⟩ := nsmul_iso (L a) (n a)
    have h : sh (D + n a • L a) ≅ ((tens X).obj M).obj
        (tensorPower X.presheaf X.ringCatSheaf.2 (sh (L a)) (n a)) :=
      (sheafMulIso D (n a • L a)).symm ≪≫ tensorIso e e'
    obtain ⟨g⟩ := ih _ _ ⟨h⟩
    exact ⟨g ≪≫ eqToIso (by simp [add_assoc])⟩

end Aux

/-! ### Snapper's polynomial -/

section Snapper

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The sheaf of a linear combination of Cartier divisors is the twist of `𝒪_X` by the
corresponding tensor powers: `𝒪_X(∑ᵢ kᵢ Lᵢ) ≅ 𝒪_X ⊗ 𝒪_X(L₁)^{⊗ k₁} ⊗ ⋯ ⊗ 𝒪_X(L_r)^{⊗ k_r}`. -/
theorem cartierSheaf_sum_iso_twistedSheaf {r : ℕ} (L : Fin r → X.CartierDivisor)
    (n : Fin r → ℤ) :
    Nonempty (MMP.CartierDivisor.sheaf (∑ i, n i • L i) ≅
      twistedSheaf (SheafOfModules.unit X.ringCatSheaf)
        (fun i => MMP.CartierDivisor.sheaf (L i)) n) := by
  obtain ⟨z⟩ := sheaf_zero_iso (X := X)
  obtain ⟨g⟩ := fold_iso L n (List.finRange r) _ 0 ⟨z⟩
  refine ⟨eqToIso ?_ ≪≫ g.symm⟩
  rw [zero_add, Fin.sum_univ_def]

/-- **Euler characteristic is a polynomial in Cartier twists.** Let `X` be a proper scheme of
dimension `n` (over a field `k`) and `L₁, …, L_r` Cartier divisors on `X`. Then the function
`ℤʳ → ℤ`, `(k₁, …, k_r) ↦ χ(X, 𝒪_X(∑ᵢ kᵢ Lᵢ))`, is given by a polynomial in `k₁, …, k_r` with
rational coefficients and of total degree at most `n`. -/
@[mmp "lem_mmp_foundation_snapper_polynomial_by_support_filtration"]
theorem exists_polynomial_eulerChar_cartierSheaf_sum [IsProper f] (n : ℕ)
    (hn : topologicalKrullDim X = n) {r : ℕ} (L : Fin r → X.CartierDivisor) :
    ∃ P : MvPolynomial (Fin r) ℚ, P.totalDegree ≤ n ∧
      ∀ m : Fin r → ℤ, MvPolynomial.eval (fun i => (m i : ℚ)) P =
        ((∑ᶠ j : ℕ, (-1 : ℤ) ^ j * (Module.finrank k (cohomologyOverField k f
          (MMP.CartierDivisor.sheaf (∑ i, m i • L i)) j) : ℤ)) : ℚ) := by
  have hc := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k f
  obtain ⟨P, hP, hPe⟩ := exists_eulerPolynomial_twistedSheaf_of_isProper k f
    (fun i => MMP.CartierDivisor.sheaf (L i)) (SheafOfModules.unit X.ringCatSheaf) hc
  refine ⟨P, ?_, fun m => ?_⟩
  · rcases hP with rfl | h
    · simp
    · rw [topologicalKrullDim_supp_unit, hn] at h
      exact_mod_cast h
  · obtain ⟨e⟩ := cartierSheaf_sum_iso_twistedSheaf L m
    rw [hPe m]
    have := ProperFlatFibreEulerCharacteristic.eulerSum_congr k f e
    have h2 := (Int.castAddHom ℚ).map_finsum_of_injective Int.cast_injective
      (fun j : ℕ => (-1 : ℤ) ^ j * (Module.finrank k (cohomologyOverField k f
          (MMP.CartierDivisor.sheaf (∑ i, m i • L i)) j) : ℤ))
    have h3 := congrArg (Int.cast : ℤ → ℚ) this.symm
    refine h3.trans (Eq.trans (b := ((∑ᶠ j : ℕ, (-1 : ℤ) ^ j * (Module.finrank k (cohomologyOverField k f
          (MMP.CartierDivisor.sheaf (∑ i, m i • L i)) j) : ℤ) : ℤ) : ℚ)) rfl ?_)
    simpa using h2

end Snapper

/-! ### Very ample multiples of an ample divisor -/

section VeryAmple

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

open MMP.Intersection (IsAmpleDivisor IsVeryAmpleDivisor)

/-- The sheaf of a multiple of a Cartier divisor is the tensor power of its sheaf:
`𝒪_X(νL) ≅ 𝒪_X(L)^{⊗ ν}`. -/
theorem lineBundle_nsmul_iso_tensorPow (L : X.CartierDivisor) (ν : ℕ) :
    Nonempty (MMP.CartierDivisor.sheaf (ν • L) ≅ MMP.Intersection.Scheme.Modules.tensorPow
        (MMP.CartierDivisor.sheaf L) ν) := by
  open CategoryTheory.MonoidalCategory in
  induction ν with
  | zero =>
    obtain ⟨e⟩ := sheaf_zero_iso (X := X)
    exact ⟨eqToIso (by rw [zero_smul]) ≪≫ e⟩
  | succ n ih =>
    obtain ⟨e⟩ := ih
    exact ⟨eqToIso (by rw [succ_nsmul]) ≪≫
      (MMP.CartierDivisorSheaf.sheafMulIso (n • L) L).symm ≪≫ whiskerRightIso e _⟩

end VeryAmple

end MMP.Resolution.Bridges
