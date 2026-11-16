module

public import MMP.AlgebraicGeometry.Intersection.CartierRestriction
public import MMP.AlgebraicGeometry.Cohomology.Duality.SmoothSerreDuality
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector

/-!
# Riemann–Roch and the Hodge index theorem on a smooth projective surface

Let `S` be a smooth projective surface over a field `k`. This file proves the Riemann–Roch
formula `χ(𝒪_S(D)) = ½ ((D · D) - (D · K_S)) + χ(𝒪_S)` for a divisor `D` and a canonical divisor
`K_S`, and the Hodge index theorem: for rational combinations `A`, `B` of invertible sheaves with
`(A²) > 0` and `(A · B) = 0`, `(B²) ≤ 0`, with equality exactly when `B` is numerically trivial.
Both hold over an arbitrary field; the source states the Hodge index theorem over an
algebraically closed one.

Riemann–Roch comes from the Snapper polynomial `P(a, b) = χ(𝒪_S(aD + bK_S))`, of total degree at
most two, whose second differences are the intersection numbers `(D · D)` and `(D · K_S)`.
Serre duality with `ω_S ≅ 𝒪_S(K_S)` gives the symmetry `P(a, b) = P(-a, 1 - b)`, which pins
down the linear coefficient of `P` in `a`.

The Hodge index theorem is proved in three steps.
* If `A` is ample and `(L · A) = 0`, then `(L²) ≤ 0`. After clearing denominators `L` is an
  invertible sheaf. If `(L²) > 0`, then `L^{⊗ t}` has no nonzero section for `t ≠ 0`, because
  the zero scheme of a section would be a curve meeting `A` positively. So Serre duality bounds
  `χ(L^{⊗ t})` by `h⁰(ω_S ⊗ L^{⊗ -t})`. For large `t`, Riemann–Roch at `-t` gives a nonzero
  section of `ω_S ⊗ L^{⊗ t}`, and multiplying by it bounds `h⁰(ω_S ⊗ L^{⊗ -t})` by
  `h⁰(ω_S^{⊗ 2})`. This contradicts the quadratic growth of `χ(L^{⊗ t})`.
* If moreover `(L²) = 0`, then `L` is orthogonal to every invertible sheaf `E`: the square of
  `nL + (H²) E - (E · H) H` is non-positive for every `n`, which forces `(L · E) = 0`. Cutting
  down by prime curves then shows that `L` is numerically trivial. Conversely, a numerically
  trivial `L` is orthogonal to every `𝒪_S(D) = 𝒪_S(∑ n_P P)`.
* For `(A²) > 0` with `A` arbitrary, apply the first step against an ample `H` to `xA + yB`.
  This gives the binary inequality `(H²) (xA + yB)² ≤ ((xA + yB) · H)²`, from which `(B²) ≤ 0`
  follows, and `(B²) = 0` forces `(B · H) = 0`.

## Main results

* `MMP.Mori.Divisor.IsCanonicalDivisor.nonempty_exteriorPower_iso_divisorialSheaf`: on a smooth
  scheme, `⋀ⁿ Ω_{X/k} ≅ 𝒪_X(K)` for a canonical divisor `K`.
* `MMP.Mori.Divisor.two_mul_eulerCharacteristic_divisorialSheaf_eq`: Riemann–Roch,
  `2 χ(𝒪_S(D)) = (D · D) - (D · K_S) + 2 χ(𝒪_S)`.
* `MMP.Mori.sheafCombinationIntersectionNumber_two_nonpos_of_isAmple`: `(P · A) = 0` for an
  ample `A` implies `(P²) ≤ 0`.
* `MMP.Mori.sheafCombinationIntersectionNumber_two_eq_zero_iff_of_isAmple`: if `(L · H) = 0`
  for an ample `H`, then `(L²) = 0` if and only if `L` has degree zero on every proper curve.
* `MMP.Mori.sheafCombinationIntersectionNumber_two_nonpos_of_pos`: the Hodge index theorem for
  a divisor `A` of positive square.
* `MMP.Mori.sheafCombinationIntersectionNumber_two_nonpos_of_isAmple'`,
  `MMP.Mori.sheafCombinationIntersectionNumber_two_eq_zero_iff_of_isAmple'`,
  `MMP.Mori.sheafCombinationIntersectionNumber_two_nonpos_of_pos'`: the same three statements
  over an arbitrary field.

## Implementation notes

A rational Cartier divisor is a finite family `c : Fin s → ℚ` of coefficients together with
invertible sheaves `M : Fin s → S.Modules`. Its intersection numbers are
`MMP.Mori.sheafCombinationIntersectionNumber`, the multilinear expansion of the intersection
numbers of the `Mⱼ`, and its degree on a curve `C` is `∑ⱼ cⱼ · MMP.Mori.ProperCurve.degree C Mⱼ`.
On the integral scheme `S` every invertible sheaf is `𝒪_S(D)` for a Cartier divisor `D`, so this
covers every rational Cartier divisor. Riemann–Roch is multiplied by `2` so that it is an
identity of integers.

The source proves Riemann–Roch by adding prime curves and using adjunction. Here Serre duality
for invertible sheaves takes the place of adjunction, so the formula holds over any field with
no descent from an algebraic closure. To bound `h⁰(ω_S ⊗ L^{⊗ -t})`, the source restricts to a
smooth member of a very ample multiple of `A`; this file uses multiplication by a section of
`ω_S ⊗ L^{⊗ t}` instead, which avoids Bertini's theorem. Neither step uses that the ground field is
algebraically closed, so the three Hodge index statements are proved over an arbitrary field
and the source's algebraically closed versions are their special cases.

## References

* [R. Hartshorne, *Algebraic geometry*][Har77], V.1.6, V.1.9
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 1.33–1.34
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Stacks.SheafOfModules.Invertible

-- The Stacks results used here are stated at the locally small models of `D(R)`, `D(𝒪_X)` and
-- `D(SheafOfModules R)`, which Stacks scopes
-- (`StacksFrontier.Homology.DerivedCategory.LocallySmall`).
open scoped Stacks.SmallDerivedModel

universe u

namespace MMP.Mori

/-! ### Cohomology and Serre duality -/

section Duality

variable {X : Scheme.{u}}

/-- The tensor product `A ⊗ B` of two `𝒪_X`-modules. -/
private noncomputable abbrev tens (A B : X.Modules) : X.Modules :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
    X.presheaf (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).obj A).obj B

/-- The Euler characteristic only depends on the structure morphism, not on how it is
written. -/
private theorem eulerCharacteristic_congr_hom (k : Type u) [Field k]
    {f g : X ⟶ Spec (.of k)} [IsProper f] [IsProper g] (h : g = f) (F : X.Modules)
    [F.IsCoherent] : eulerCharacteristic k g F = eulerCharacteristic k f F := by
  subst h; rfl

/-- The cohomology of a module in negative degrees vanishes. -/
private theorem subsingleton_derivedCohomologyOverField_of_neg (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) (F : X.Modules) {m : ℤ} (hm : m < 0) :
    Subsingleton (Stacks.Duality.derivedCohomologyOverField f
      ((DerivedCategory.singleFunctor X.Modules 0).obj F) m) := by
  letI : Linear k X.Modules := Scheme.Modules.linearOverBase f
  letI : Functor.Linear k (globalSectionsOver f) := globalSectionsOver_linear_linearOverBase f
  haveI := DerivedCategory.TStructure.t.isGE_shift
    ((DerivedCategory.singleFunctor X.Modules 0).obj F) 0 m (-m) (by omega)
  haveI : Subsingleton (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor X.Modules 0).obj (Stacks.Ample.unitModule X))
      ((DerivedCategory.singleFunctor X.Modules 0).obj F) m) :=
    ⟨fun a b => by
      rw [DerivedCategory.TStructure.t.zero a 0 (-m) (by omega),
        DerivedCategory.TStructure.t.zero b 0 (-m) (by omega)]⟩
  exact (Stacks.Duality.nonempty_derivedCohomologyOverFieldLinearEquivExtUnit f
    ((DerivedCategory.singleFunctor X.Modules 0).obj F) m).some.toEquiv.subsingleton

/-- The cohomology of a module in negative degrees has dimension zero. -/
private theorem finrank_derivedCohomologyOverField_of_neg (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) (F : X.Modules) {i : ℤ} (hi : i < 0) :
    Module.finrank k (Stacks.Duality.derivedCohomologyOverField f
      ((DerivedCategory.singleFunctor X.Modules 0).obj F) i) = 0 :=
  have := subsingleton_derivedCohomologyOverField_of_neg k f F hi
  Module.finrank_zero_of_subsingleton

/-- In nonnegative degrees the derived cohomology is sheaf cohomology. -/
private theorem finrank_derivedCohomologyOverField_natCast (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) (F : X.Modules) (m : ℕ) :
    Module.finrank k (Stacks.Duality.derivedCohomologyOverField f
      ((DerivedCategory.singleFunctor X.Modules 0).obj F) m) =
      Module.finrank k (cohomologyOverField k f F m) :=
  (Stacks.Duality.cohomologyOverFieldLinearEquivDerivedCohomologyOverField k f F
    m).finrank_eq.symm

/-- Isomorphic modules have cohomology of the same dimension in every integer degree. -/
private theorem finrank_derivedCohomologyOverField_eq_of_iso (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) [IsProper f] {F F' : X.Modules} (e : F ≅ F') (i : ℤ) :
    Module.finrank k (Stacks.Duality.derivedCohomologyOverField f
      ((DerivedCategory.singleFunctor X.Modules 0).obj F) i) =
      Module.finrank k (Stacks.Duality.derivedCohomologyOverField f
        ((DerivedCategory.singleFunctor X.Modules 0).obj F') i) := by
  rcases lt_or_ge i 0 with hi | hi
  · rw [finrank_derivedCohomologyOverField_of_neg k f F hi,
      finrank_derivedCohomologyOverField_of_neg k f F' hi]
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, i = m := ⟨i.toNat, by omega⟩
    rw [finrank_derivedCohomologyOverField_natCast, finrank_derivedCohomologyOverField_natCast,
      finrank_cohomologyOverField_eq_of_iso k f e m]

/-- **Serre duality for invertible sheaves, degree by degree.** On a smooth projective variety
of dimension `n` with `ω_X = ⋀ⁿ Ω_{X/k}`, if `G ⊗ E ≅ 𝒪_X` for an invertible `E` and
`H ≅ ω_X ⊗ E`, then `hⁱ(G) = hⁿ⁻ⁱ(H)` for every integer `i`. -/
private theorem finrank_derivedCohomologyOverField_eq_sub (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsProjectiveVariety k f] (hsm : IsSmoothScheme f)
    (n : ℕ) (hn : topologicalKrullDim X = n) (E G H : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 E]
    (eG : tens G E ≅ SheafOfModules.unit X.ringCatSheaf)
    (eH : H ≅ tens (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) n) E)
    (i : ℤ) :
    Module.finrank k (Stacks.Duality.derivedCohomologyOverField f
      ((DerivedCategory.singleFunctor X.Modules 0).obj G) i) =
      Module.finrank k (Stacks.Duality.derivedCohomologyOverField f
        ((DerivedCategory.singleFunctor X.Modules 0).obj H) (n - i)) := by
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E 1
  obtain ⟨L⟩ := nonempty_linearEquiv_dual_exteriorPower_tensor f hsm n hn E i
  exact (finrank_derivedCohomologyOverField_eq_of_iso k f
    (Stacks.SheafOfModules.isoOfTensorIsoUnit X.presheaf _ E G _ eG
      (Stacks.SheafOfModules.Scheme.evaluationIso X E)) i).trans
    (L.finrank_eq.trans (Subspace.dual_finrank_eq.trans
      (finrank_derivedCohomologyOverField_eq_of_iso k f eH (n - i)).symm))

/-- If the cohomology of a coherent module vanishes above degree `n`, its Euler characteristic
is the alternating sum of its first `n + 1` cohomology dimensions. -/
private theorem eulerCharacteristic_eq_sum_range (k : Type u) [Field k] (f : X ⟶ Spec (.of k))
    [IsProper f] (F : X.Modules) [F.IsCoherent] (n : ℕ)
    (hF : ∀ i : ℤ, (n : ℤ) < i → Module.finrank k (Stacks.Duality.derivedCohomologyOverField f
      ((DerivedCategory.singleFunctor X.Modules 0).obj F) i) = 0) :
    eulerCharacteristic k f F = ∑ m ∈ Finset.range (n + 1), (-1 : ℤ) ^ m *
      (Module.finrank k (Stacks.Duality.derivedCohomologyOverField f
        ((DerivedCategory.singleFunctor X.Modules 0).obj F) m) : ℤ) := by
  rw [eulerCharacteristic_eq_finsum,
    finsum_eq_sum_of_support_subset (s := Finset.range (n + 1))]
  · exact Finset.sum_congr rfl fun m _ => by rw [finrank_derivedCohomologyOverField_natCast]
  · intro m hm
    simp only [Function.mem_support] at hm
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    apply hm
    rw [← finrank_derivedCohomologyOverField_natCast, hF m (by omega)]
    simp

/-- **Serre duality for Euler characteristics.** On a smooth projective variety of dimension
`n` with `ω_X = ⋀ⁿ Ω_{X/k}`, if `G ⊗ E ≅ 𝒪_X` for an invertible `E` and `H ≅ ω_X ⊗ E`, then
`χ(G) = (-1)ⁿ χ(H)`. -/
private theorem eulerCharacteristic_eq_neg_one_pow_mul_of_tensor_iso (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsProjectiveVariety k f] (hsm : IsSmoothScheme f)
    (n : ℕ) (hn : topologicalKrullDim X = n) (E G H : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 E] [G.IsCoherent] [H.IsCoherent]
    (eG : tens G E ≅ SheafOfModules.unit X.ringCatSheaf)
    (eH : H ≅ tens (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) n) E) :
    eulerCharacteristic k f G = (-1) ^ n * eulerCharacteristic k f H := by
  let g : ℤ → ℕ := fun i => Module.finrank k (Stacks.Duality.derivedCohomologyOverField f
    ((DerivedCategory.singleFunctor X.Modules 0).obj G) i)
  let h : ℤ → ℕ := fun i => Module.finrank k (Stacks.Duality.derivedCohomologyOverField f
    ((DerivedCategory.singleFunctor X.Modules 0).obj H) i)
  have key : ∀ i : ℤ, g i = h (n - i) :=
    finrank_derivedCohomologyOverField_eq_sub k f hsm n hn E G H eG eH
  have hgv : ∀ i : ℤ, (n : ℤ) < i → g i = 0 := fun i hi => by
    rw [key]
    exact finrank_derivedCohomologyOverField_of_neg k f H (by omega)
  have hhv : ∀ i : ℤ, (n : ℤ) < i → h i = 0 := fun i hi => by
    rw [← sub_sub_cancel (n : ℤ) i, ← key]
    exact finrank_derivedCohomologyOverField_of_neg k f G (by omega)
  rw [eulerCharacteristic_eq_sum_range k f G n hgv, eulerCharacteristic_eq_sum_range k f H n hhv,
    Finset.mul_sum, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_range] at hm
  rw [show n + 1 - 1 - m = n - m by omega]
  change (-1 : ℤ) ^ (n - m) * (g ((n - m : ℕ) : ℤ) : ℤ) = (-1) ^ n * ((-1) ^ m * (h m : ℤ))
  rw [key, show (n : ℤ) - ((n - m : ℕ) : ℤ) = m by
    push_cast [Nat.cast_sub (by omega : m ≤ n)]; ring]
  have hpow : (-1 : ℤ) ^ n = (-1) ^ (n - m) * (-1) ^ m := by
    rw [← pow_add, Nat.sub_add_cancel (by omega)]
  rw [hpow, mul_assoc, ← mul_assoc ((-1 : ℤ) ^ m), ← pow_add, ← two_mul, pow_mul]
  simp

/-- **`χ ≤ h⁰ + h²` on a smooth projective surface, with `h²` computed by Serre duality.** If
`G ⊗ E ≅ 𝒪_X` for an invertible `E` and `H ≅ ω_X ⊗ E`, with `ω_X = ⋀² Ω_{X/k}`, then
`χ(G) ≤ h⁰(G) + h⁰(H)`: indeed `hⁱ(G) = h^{2-i}(H)`, so `hⁱ(G) = 0` for `i > 2` and
`h²(G) = h⁰(H)`. -/
private theorem eulerCharacteristic_le_finrank_add_finrank (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsProjectiveVariety k f]
    (hsm : IsSmoothScheme f) (hn : topologicalKrullDim X = (2 : ℕ)) (E G H : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 E] [G.IsCoherent]
    (eG : tens G E ≅ SheafOfModules.unit X.ringCatSheaf)
    (eH : H ≅ tens (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) 2) E) :
    eulerCharacteristic k f G ≤ (Module.finrank k (cohomologyOverField k f G 0) : ℤ) +
      Module.finrank k (cohomologyOverField k f H 0) := by
  have key := finrank_derivedCohomologyOverField_eq_sub k f hsm 2 hn E G H eG eH
  have h2 := key 2
  rw [show ((2 : ℕ) : ℤ) - 2 = ((0 : ℕ) : ℤ) by norm_num] at h2
  rw [eulerCharacteristic_eq_sum_range k f G 2 fun i hi => by
      rw [key]; exact finrank_derivedCohomologyOverField_of_neg k f H (by omega),
    ← finrank_derivedCohomologyOverField_natCast k f G 0,
    ← finrank_derivedCohomologyOverField_natCast k f H 0, ← h2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat]
  omega

end Duality

/-! ### Riemann–Roch -/

section Algebra

open MvPolynomial

/-- A polynomial in two variables of total degree at most two is the quadratic form given by its
six coefficients. -/
private theorem eval_eq_of_totalDegree_le_two (P : MvPolynomial (Fin 2) ℚ)
    (hP : P.totalDegree ≤ 2) (x : Fin 2 → ℚ) :
    eval x P = P.coeff 0 + P.coeff (Finsupp.single 0 1) * x 0 +
      P.coeff (Finsupp.single 1 1) * x 1 + P.coeff (Finsupp.single 0 2) * x 0 ^ 2 +
      P.coeff (Finsupp.single 0 1 + Finsupp.single 1 1) * (x 0 * x 1) +
      P.coeff (Finsupp.single 1 2) * x 1 ^ 2 := by
  let S : Finset (Fin 2 →₀ ℕ) := {0, Finsupp.single 0 1, Finsupp.single 1 1,
    Finsupp.single 0 2, Finsupp.single 0 1 + Finsupp.single 1 1, Finsupp.single 1 2}
  have hsupp : P.support ⊆ S := by
    intro s hs
    have h := le_totalDegree hs
    have h2 : s 0 + s 1 ≤ 2 := by
      rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two] at h
      omega
    have hs' : s = Finsupp.single 0 (s 0) + Finsupp.single 1 (s 1) := by
      ext i
      fin_cases i <;> simp
    rw [hs']
    have : s 0 ≤ 2 := by omega
    have : s 1 ≤ 2 := by omega
    interval_cases h0 : s 0 <;> interval_cases h1 : s 1 <;> simp_all [S] <;> omega
  rw [eval_eq, Finset.sum_subset hsupp (fun s _ hs => by simp [notMem_support_iff.1 hs])]
  have hprod : ∀ s : Fin 2 →₀ ℕ, (∏ i ∈ s.support, x i ^ s i) = x 0 ^ s 0 * x 1 ^ s 1 := by
    intro s
    rw [Finset.prod_subset (Finset.subset_univ _)
      (fun i _ hi => by simp [Finsupp.notMem_support_iff.1 hi]), Fin.prod_univ_two]
  simp only [hprod]
  simp only [S]
  rw [Finset.sum_insert (by simp [Finsupp.ext_iff, Fin.forall_fin_two]),
    Finset.sum_insert (by simp [Finsupp.ext_iff, Fin.forall_fin_two]),
    Finset.sum_insert (by simp [Finsupp.ext_iff, Fin.forall_fin_two]),
    Finset.sum_insert (by simp [Finsupp.ext_iff, Fin.forall_fin_two]),
    Finset.sum_insert (by simp [Finsupp.ext_iff, Fin.forall_fin_two]), Finset.sum_singleton]
  simp
  ring

/-- **The second difference on `ℤ²`.** The alternating sum over `I ⊆ {0, 1}` of `q` at minus the
indicator of `I`. -/
private theorem sum_neg_one_pow_card_fin_two (q : (Fin 2 → ℤ) → ℤ) :
    ∑ I : Finset (Fin 2), (-1 : ℤ) ^ I.card * q (fun j => if j ∈ I then -1 else 0) =
      q ![0, 0] - q ![-1, 0] - q ![0, -1] + q ![-1, -1] := by
  have hI : ∀ I : Finset (Fin 2), (fun j => if j ∈ I then (-1 : ℤ) else 0) =
      ![if 0 ∈ I then -1 else 0, if 1 ∈ I then -1 else 0] := fun I => by
    funext j; fin_cases j <;> rfl
  simp only [hI]
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp
  ring

/-- **Riemann–Roch for a quadratic function with Serre symmetry.** If `p : ℤ² → ℤ` is given by
a polynomial of total degree at most `2` and satisfies `p(-c, 0) = p(c, 1)`, then twice `p(1, 0)`
is the second difference of `p` in the first variable, minus the mixed second difference at the
origin, plus twice `p(0, 0)`. -/
private theorem two_mul_eq_of_symm (P : MvPolynomial (Fin 2) ℚ) (hP : P.totalDegree ≤ 2)
    (p : (Fin 2 → ℤ) → ℤ) (hp : ∀ n, eval (fun i => (n i : ℚ)) P = p n)
    (hS : ∀ c, p ![-c, 0] = p ![c, 1]) :
    2 * p ![1, 0] = (p ![0, 0] - 2 * p ![-1, 0] + p ![-2, 0]) -
      (p ![0, 0] - p ![-1, 0] - p ![0, -1] + p ![-1, -1]) + 2 * p ![0, 0] := by
  have h : ∀ a b : ℤ, (p ![a, b] : ℚ) = P.coeff 0 + P.coeff (Finsupp.single 0 1) * a +
      P.coeff (Finsupp.single 1 1) * b + P.coeff (Finsupp.single 0 2) * a ^ 2 +
      P.coeff (Finsupp.single 0 1 + Finsupp.single 1 1) * (a * b) +
      P.coeff (Finsupp.single 1 2) * b ^ 2 := fun a b => by
    rw [← hp, eval_eq_of_totalDegree_le_two P hP]; simp
  have h1 : (p ![1, 0] : ℚ) = p ![-1, 1] := by exact_mod_cast by simpa using hS (-1)
  have h0 : (p ![0, 0] : ℚ) = p ![0, 1] := by exact_mod_cast by simpa using hS 0
  rw [h, h] at h1 h0
  have := h 1 0; have := h 0 0; have := h (-1) 0; have := h 0 (-1); have := h (-1) (-1)
  have := h (-2) 0
  push_cast at *
  have : (2 * p ![1, 0] : ℚ) = (p ![0, 0] - 2 * p ![-1, 0] + p ![-2, 0]) -
      (p ![0, 0] - p ![-1, 0] - p ![0, -1] + p ![-1, -1]) + 2 * p ![0, 0] := by linarith
  exact_mod_cast this

end Algebra

section Canonical

variable {X : Scheme.{u}}

/-- **The canonical sheaf of a smooth scheme.** If `X` is smooth over `k` and `K` is a canonical
divisor of `X`, then `ω_X = ⋀ⁿ Ω_{X/k} ≅ 𝒪_X(K)`. -/
public theorem Divisor.IsCanonicalDivisor.nonempty_exteriorPower_iso_divisorialSheaf
    (k : Type u) [Field k] (f : X ⟶ Spec (.of k)) [IsLocallyNoetherian X] [IsNormal X]
    (hsm : IsSmoothScheme f) {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor f n) :
    Nonempty (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) n ≅
      K.divisorialSheaf) := by
  let ι := (smoothLocus f).ι
  haveI : IsIso ι := by
    change IsIso (smoothLocus f).ι
    rw [show smoothLocus f = ⊤ from hsm, ← Scheme.topIso_hom]
    infer_instance
  -- `A ≅ (inv ι)^* ι^* A` for every module `A`.
  have cancel : ∀ A : X.Modules,
      A ≅ (Scheme.Modules.pullback (inv ι)).obj ((Scheme.Modules.pullback ι).obj A) :=
    fun A => ((Scheme.Modules.pullbackId (X := X)).app A).symm ≪≫
      (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id ι).symm).app A ≪≫
      ((Scheme.Modules.pullbackComp (inv ι) ι).app A).symm
  let e : (Scheme.Modules.pullback ι).obj
      (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) n) ≅
      (Scheme.Modules.pullback ι).obj K.divisorialSheaf :=
    @asIso _ _ _ _ (Scheme.Hom.relativeDifferentialFormsMap ι f (ι ≫ f) (𝟙 _)
        (Category.comp_id _).symm n)
      (Scheme.Hom.isIso_relativeDifferentialFormsMap_of_etale ι f (ι ≫ f) (𝟙 _)
        (Category.comp_id _).symm n) ≪≫ hK.iso.symm ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback ι).app _
  exact ⟨cancel _ ≪≫ (Scheme.Modules.pullback (inv ι)).mapIso e ≪≫ (cancel _).symm⟩

end Canonical

namespace Divisor

/-- **Riemann–Roch on a smooth projective surface.** Let `X` be a smooth projective surface
over a field `k`, `K` a canonical divisor and `D` a divisor on `X`. Then
`2 χ(X, 𝒪_X(D)) = (D · D) - (D · K) + 2 χ(X, 𝒪_X)`. -/
@[mmp "lem_mmp_foundation_surface_riemann_roch_by_prime_addition"]
public theorem two_mul_eulerCharacteristic_divisorialSheaf_eq
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [Smooth f]
    [IsLocallyNoetherian X] [IsNormal X] (hX : IsProjectiveVariety k f)
    (hdim : topologicalKrullDim X = 2) (K : Divisor X) (hK : K.IsCanonicalDivisor f 2)
    (D : Divisor X) :
    haveI hsm : IsSmoothScheme f := (isSmoothScheme_iff f).2 inferInstance
    haveI := QuasiCompact.compactSpace_of_compactSpace f
    haveI := (MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm D)
      |>.isInvertibleModule_divisorialSheaf
    haveI : D.divisorialSheaf.IsCoherent :=
      Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X D.divisorialSheaf
    haveI : (SheafOfModules.unit X.ringCatSheaf).IsCoherent :=
      Stacks.AlgebraicGeometry.CoherentKernel.structureSheaf_isCoherent X
    2 * eulerCharacteristic k f D.divisorialSheaf =
      intersectionNumberOn k f (𝟙 X) 2 (by rw [hdim]; rfl) ![D, D]
          (fun _ => MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm _) -
        intersectionNumberOn k f (𝟙 X) 2 (by rw [hdim]; rfl) ![D, K]
          (fun _ => MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm _) +
        2 * eulerCharacteristic k f (SheafOfModules.unit X.ringCatSheaf) := by
  have hsm : IsSmoothScheme f := (isSmoothScheme_iff f).2 inferInstance
  haveI := QuasiCompact.compactSpace_of_compactSpace f
  haveI := (MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm D)
    |>.isInvertibleModule_divisorialSheaf
  haveI := (MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm K)
    |>.isInvertibleModule_divisorialSheaf
  haveI : D.divisorialSheaf.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X D.divisorialSheaf
  haveI : (SheafOfModules.unit X.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.structureSheaf_isCoherent X
  have hid : 𝟙 X ≫ f = f := Category.id_comp f
  let L : Fin 2 → X.Modules := fun j => (![D, K] j).divisorialSheaf
  haveI : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j) := by
    intro j
    fin_cases j
    exacts [inferInstanceAs (SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      D.divisorialSheaf), inferInstanceAs (SheafOfModules.IsInvertible X.presheaf
      X.ringCatSheaf.2 K.divisorialSheaf)]
  let M : Fin 2 → X.Modules := fun j => (Scheme.Modules.pullback (𝟙 X)).obj (L j)
  let T : (Fin 2 → ℤ) → X.Modules := fun n => twistedSheaf (SheafOfModules.unit X.ringCatSheaf) M n
  haveI hTc : ∀ n, (T n).IsCoherent := fun n => isCoherent_twistedSheafUnitPullback k f (𝟙 X) L n
  let p : (Fin 2 → ℤ) → ℤ := fun n => eulerCharacteristic k (𝟙 X ≫ f) (T n)
  obtain ⟨P, hP0, hP⟩ := exists_eulerPolynomial_twistedSheaf_of_isProper k (𝟙 X ≫ f) M
    (SheafOfModules.unit X.ringCatSheaf)
    (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k (𝟙 X ≫ f))
  have hdeg : P.totalDegree ≤ 2 := by
    rcases hP0 with rfl | h
    · simp
    · have h2 := h.trans (topologicalKrullDim_subspace_le X _)
      rw [hdim] at h2
      exact_mod_cast h2
  -- the intersection number `D · K`
  have hDK : intersectionNumberOn k f (𝟙 X) 2 (by rw [hdim]; rfl) ![D, K]
      (fun _ => MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm _) =
      p ![0, 0] - p ![-1, 0] - p ![0, -1] + p ![-1, -1] :=
    sum_neg_one_pow_card_fin_two p
  -- the intersection number `D · D`
  have hDD : intersectionNumberOn k f (𝟙 X) 2 (by rw [hdim]; rfl) ![D, D]
      (fun _ => MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm _) =
      p ![0, 0] - 2 * p ![-1, 0] + p ![-2, 0] := by
    let L' : Fin 2 → X.Modules := fun j => (![D, D] j).divisorialSheaf
    haveI : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L' j) := by
      intro j
      fin_cases j <;> exact (inferInstance : SheafOfModules.IsInvertible X.presheaf
        X.ringCatSheaf.2 D.divisorialSheaf)
    let T' : (Fin 2 → ℤ) → X.Modules := fun n => twistedSheaf (SheafOfModules.unit X.ringCatSheaf)
      (fun j => (Scheme.Modules.pullback (𝟙 X)).obj (L' j)) n
    haveI : ∀ n, (T' n).IsCoherent := fun n => isCoherent_twistedSheafUnitPullback k f (𝟙 X) L' n
    have hT' : ∀ n : Fin 2 → ℤ, eulerCharacteristic k (𝟙 X ≫ f) (T' n) = p ![n 0 + n 1, 0] := by
      intro n
      let e : T' n ≅ T ![n 0 + n 1, 0] :=
        tensorProductAssociator X.presheaf X.ringCatSheaf.2 _ _ _ ≪≫
          tensorProductIso X.presheaf X.ringCatSheaf.2 (Iso.refl _)
            ((tensorPowerCoherence X.presheaf X.ringCatSheaf.2 (M 0)).mulIso (n 0) (n 1)) ≪≫
          (tensorProductRightUnitor X.presheaf X.ringCatSheaf.2 _).symm
      exact eulerCharacteristic_eq_of_iso k (𝟙 X ≫ f) e
    refine (sum_neg_one_pow_card_fin_two fun n => eulerCharacteristic k (𝟙 X ≫ f) (T' n)).trans ?_
    simp only [hT']
    simp
    ring
  have hχD : eulerCharacteristic k f D.divisorialSheaf = p ![1, 0] := by
    let e : D.divisorialSheaf ≅ T ![1, 0] :=
      ((Scheme.Modules.pullbackId (X := X)).app _).symm ≪≫
        (tensorPowerOneIso X.presheaf X.ringCatSheaf.2 (M 0)).symm ≪≫
        (tensorProductLeftUnitor X.presheaf X.ringCatSheaf.2 _).symm ≪≫
        (tensorProductRightUnitor X.presheaf X.ringCatSheaf.2 _).symm
    rw [eulerCharacteristic_eq_of_iso k f e]
    exact (eulerCharacteristic_congr_hom k hid _).symm
  have hχO : eulerCharacteristic k f (SheafOfModules.unit X.ringCatSheaf) = p ![0, 0] := by
    let e : SheafOfModules.unit X.ringCatSheaf ≅ T ![0, 0] :=
      (tensorProductRightUnitor X.presheaf X.ringCatSheaf.2 _).symm ≪≫
        (tensorProductRightUnitor X.presheaf X.ringCatSheaf.2 _).symm
    rw [eulerCharacteristic_eq_of_iso k f e]
    exact (eulerCharacteristic_congr_hom k hid _).symm
  obtain ⟨eω⟩ := hK.nonempty_exteriorPower_iso_divisorialSheaf k f hsm
  let eωB : Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) (2 : ℕ) ≅ M 1 :=
    eω ≪≫ ((Scheme.Modules.pullbackId (X := X)).app _).symm
  haveI : IsProjectiveVariety k f := hX
  have hS : ∀ c : ℤ, p ![-c, 0] = p ![c, 1] := by
    intro c
    let E := tensorPower X.presheaf X.ringCatSheaf.2 (M 0) c
    let eG : tens (T ![-c, 0]) E ≅ SheafOfModules.unit X.ringCatSheaf :=
      tensorProductIso X.presheaf X.ringCatSheaf.2
          (tensorProductRightUnitor X.presheaf X.ringCatSheaf.2 _ ≪≫
            tensorProductLeftUnitor X.presheaf X.ringCatSheaf.2 _) (Iso.refl E) ≪≫
        (tensorPowerCoherence X.presheaf X.ringCatSheaf.2 (M 0)).mulIso (-c) c ≪≫
        tensorPowerReindex X.presheaf X.ringCatSheaf.2 (M 0) (by ring : -c + c = 0)
    let eH : T ![c, 1] ≅ tens (Scheme.Modules.exteriorPower
        (Scheme.Hom.relativeDifferentials f) (2 : ℕ)) E :=
      tensorProductIso X.presheaf X.ringCatSheaf.2
          (tensorProductLeftUnitor X.presheaf X.ringCatSheaf.2 _)
          (tensorPowerOneIso X.presheaf X.ringCatSheaf.2 (M 1)) ≪≫
        tensorProductBraiding X.presheaf X.ringCatSheaf.2 _ _ ≪≫
        tensorProductIso X.presheaf X.ringCatSheaf.2 eωB.symm (Iso.refl E)
    have := eulerCharacteristic_eq_neg_one_pow_mul_of_tensor_iso k f hsm 2
      (by rw [hdim]; rfl) E (T ![-c, 0]) (T ![c, 1]) eG eH
    simp only [p, eulerCharacteristic_congr_hom k hid]
    rw [this]
    ring
  rw [hDK, hDD, hχD, hχO]
  exact two_mul_eq_of_symm P hdeg p hP hS

end Divisor

/-! ### Divisors orthogonal to an ample class -/

/-- A quadratic with positive leading coefficient eventually exceeds any bound, at `t` and at
`-t` simultaneously. -/
private theorem exists_lt_quadratic {a b c K : ℚ} (hc : 0 < c) :
    ∃ t : ℕ, 1 ≤ t ∧ K < c * t ^ 2 + b * t + a ∧ 0 < c * t ^ 2 - b * t + a := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((|b| + |a| + |K| + 1) / c)
  refine ⟨n + 1, by omega, ?_, ?_⟩
  all_goals
    have h1 : |b| + |a| + |K| + 1 < c * ((n + 1 : ℕ) : ℚ) := by
      rw [div_lt_iff₀ hc] at hn
      push_cast
      nlinarith
    have ht : (1 : ℚ) ≤ ((n + 1 : ℕ) : ℚ) := by norm_num
    have hb := neg_abs_le b
    have hb' := le_abs_self b
    have ha := neg_abs_le a
    have hK := le_abs_self K
    set T : ℚ := ((n + 1 : ℕ) : ℚ)
    have hT0 : (0 : ℚ) ≤ T := by linarith
    have e1 : T * (|b| + |a| + |K| + 1) ≤ c * T ^ 2 := by nlinarith
    have e2 : 0 ≤ (T - 1) * (|a| + |K| + 1) := mul_nonneg (by linarith) (by positivity)
    have e3 : 0 ≤ (|b| + b) * T := mul_nonneg (by linarith) hT0
    have e4 : 0 ≤ (|b| - b) * T := mul_nonneg (by linarith) hT0
    nlinarith [abs_nonneg K]

/-! ### Multilinearity of the intersection number -/

section Multilinear

variable (k : Type u) [Field k] {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
  (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ) (hd : topologicalKrullDim Z ≤ (d : WithBot ℕ∞))

/-- **Replacing one entry by an integer tensor power multiplies the intersection number**:
`(⋯ N^{⊗ m} ⋯ · Z) = m (⋯ N ⋯ · Z)` for every `m ∈ ℤ`. -/
private theorem intersectionNumber_update_tensorPower_int (G : Fin d → X.Modules)
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (G q)] (j : Fin d)
    (N : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N] (m : ℤ) :
    haveI := isInvertible_update G j (tensorPower X.presheaf X.ringCatSheaf.2 N m)
    haveI := isInvertible_update G j N
    intersectionNumber k f i d hd
        (Function.update G j (tensorPower X.presheaf X.ringCatSheaf.2 N m)) =
      m * intersectionNumber k f i d hd (Function.update G j N) := by
  haveI hN := isInvertible_update G j N
  have hnat : ∀ n : ℕ,
      haveI := isInvertible_update G j (tensorPower X.presheaf X.ringCatSheaf.2 N n)
      intersectionNumber k f i d hd
        (Function.update G j (tensorPower X.presheaf X.ringCatSheaf.2 N n)) =
      n * intersectionNumber k f i d hd (Function.update G j N) := by
    intro n
    have h := intersectionNumber_update_tensorPower k f i d hd (Function.update G j N) j n
    convert h using 3
    refine (Function.update_idem (f := G) (a := j) N _).symm.trans ?_
    congr 2
    exact (Function.update_self j N G).symm
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · exact hnat n
  · haveI := isInvertible_update G j (tensorPower X.presheaf X.ringCatSheaf.2 N (-(n : ℤ)))
    haveI := isInvertible_update G j (tensorPower X.presheaf X.ringCatSheaf.2 N (n : ℤ))
    haveI := isInvertible_update G j (tensorPower X.presheaf X.ringCatSheaf.2 N ((0 : ℕ) : ℤ))
    have h0 := hnat 0
    have hsum := intersectionNumber_tensor k f i d hd j
      (Function.update G j (tensorPower X.presheaf X.ringCatSheaf.2 N ((0 : ℕ) : ℤ)))
      (Function.update G j (tensorPower X.presheaf X.ringCatSheaf.2 N (-(n : ℤ))))
      (Function.update G j (tensorPower X.presheaf X.ringCatSheaf.2 N (n : ℤ)))
      (fun q hq => (Function.update_of_ne hq _ _).trans (Function.update_of_ne hq _ _).symm)
      (fun q hq => (Function.update_of_ne hq _ _).trans (Function.update_of_ne hq _ _).symm)
      (eqToIso (Function.update_self j _ G) ≪≫
        tensorPowerReindex X.presheaf X.ringCatSheaf.2 N
          (by push_cast; ring : ((0 : ℕ) : ℤ) = -(n : ℤ) + n) ≪≫
        ((tensorPowerCoherence X.presheaf X.ringCatSheaf.2 N).mulIso (-(n : ℤ)) n).symm ≪≫
        eqToIso (congrArg₂ tens (Function.update_self j _ G).symm
          (Function.update_self j _ G).symm))
    rw [h0, hnat n] at hsum
    push_cast at hsum ⊢
    linarith

/-- A twist of an invertible module by integer powers of invertible modules is invertible. -/
private theorem isInvertible_twistList {s : ℕ} (M : Fin s → X.Modules)
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M q)] (n : Fin s → ℤ) :
    ∀ (l : List (Fin s)) (F : X.Modules) [SheafOfModules.IsInvertible X.presheaf
      X.ringCatSheaf.2 F],
      SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (twistList M n l F)
  | [], _, h => h
  | q :: l, F, _ =>
    haveI := Stacks.SheafOfModules.tensorProduct_isInvertible X.presheaf X.ringCatSheaf.2 F
      (tensorPower X.presheaf X.ringCatSheaf.2 (M q) (n q))
    isInvertible_twistList M n l (tens F (tensorPower X.presheaf X.ringCatSheaf.2 (M q) (n q)))

/-- **The intersection number is additive along a twist**: with
`T = F ⊗ M_{q₁}^{⊗ n_{q₁}} ⊗ ⋯` the fold of the twists over a list `l = [q₁, …]` of indices,
`(⋯ T ⋯ · Z) = (⋯ F ⋯ · Z) + ∑_{q ∈ l} n_q (⋯ M_q ⋯ · Z)`. -/
private theorem intersectionNumber_update_twistList (G : Fin d → X.Modules)
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (G q)] (j : Fin d)
    {s : ℕ} (M : Fin s → X.Modules)
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M q)] (n : Fin s → ℤ) :
    ∀ (l : List (Fin s)) (F : X.Modules) [SheafOfModules.IsInvertible X.presheaf
      X.ringCatSheaf.2 F],
    haveI := isInvertible_twistList M n l F
    haveI := isInvertible_update G j (twistList M n l F)
    haveI := isInvertible_update G j F
    haveI := fun q => isInvertible_update G j (M q)
    intersectionNumber k f i d hd (Function.update G j (twistList M n l F)) =
      intersectionNumber k f i d hd (Function.update G j F) +
        (l.map fun q => n q * intersectionNumber k f i d hd (Function.update G j (M q))).sum
  | [], F, _ => (add_zero _).symm
  | q :: l, F, _ => by
    haveI := Stacks.SheafOfModules.tensorProduct_isInvertible X.presheaf X.ringCatSheaf.2 F
      (tensorPower X.presheaf X.ringCatSheaf.2 (M q) (n q))
    haveI := fun q => isInvertible_update G j (M q)
    haveI := isInvertible_update G j F
    haveI := isInvertible_update G j (tensorPower X.presheaf X.ringCatSheaf.2 (M q) (n q))
    haveI := isInvertible_update G j
      (tens F (tensorPower X.presheaf X.ringCatSheaf.2 (M q) (n q)))
    have ih := intersectionNumber_update_twistList G j M n l
      (tens F (tensorPower X.presheaf X.ringCatSheaf.2 (M q) (n q)))
    have hadd := intersectionNumber_tensor k f i d hd j
      (Function.update G j (tens F (tensorPower X.presheaf X.ringCatSheaf.2 (M q) (n q))))
      (Function.update G j F)
      (Function.update G j (tensorPower X.presheaf X.ringCatSheaf.2 (M q) (n q)))
      (fun r hr => (Function.update_of_ne hr _ _).trans (Function.update_of_ne hr _ _).symm)
      (fun r hr => (Function.update_of_ne hr _ _).trans (Function.update_of_ne hr _ _).symm)
      (eqToIso ((Function.update_self j _ G).trans (congrArg₂ tens
        (Function.update_self j _ G).symm (Function.update_self j _ G).symm)))
    have hpow := intersectionNumber_update_tensorPower_int k f i d hd G j (M q) (n q)
    haveI := isInvertible_twistList M n l
      (tens F (tensorPower X.presheaf X.ringCatSheaf.2 (M q) (n q)))
    haveI := isInvertible_update G j (twistList M n l
      (tens F (tensorPower X.presheaf X.ringCatSheaf.2 (M q) (n q))))
    change intersectionNumber k f i d hd (Function.update G j (twistList M n l
      (tens F (tensorPower X.presheaf X.ringCatSheaf.2 (M q) (n q))))) = _
    rw [ih, hadd, hpow, List.map_cons, List.sum_cons]
    ring

/-- **The intersection number is linear along `𝒪_X ⊗ M₁^{⊗ n₁} ⊗ ⋯ ⊗ M_s^{⊗ n_s}`**:
`(⋯ (∑ₗ nₗ Mₗ) ⋯ · Z) = ∑ₗ nₗ (⋯ Mₗ ⋯ · Z)`. -/
private theorem intersectionNumber_update_twistedSheaf (G : Fin d → X.Modules)
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (G q)] (j : Fin d)
    {s : ℕ} (M : Fin s → X.Modules)
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M q)] (n : Fin s → ℤ) :
    haveI := tensorPower_isInvertible X.presheaf X.ringCatSheaf.2 (G j) 0
    haveI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
        (twistedSheaf (SheafOfModules.unit X.ringCatSheaf) M n) :=
      isInvertible_twistList M n (List.finRange s) (SheafOfModules.unit X.ringCatSheaf)
    haveI := isInvertible_update G j (twistedSheaf (SheafOfModules.unit X.ringCatSheaf) M n)
    haveI := fun q => isInvertible_update G j (M q)
    intersectionNumber k f i d hd
        (Function.update G j (twistedSheaf (SheafOfModules.unit X.ringCatSheaf) M n)) =
      ∑ q, n q * intersectionNumber k f i d hd (Function.update G j (M q)) := by
  haveI := tensorPower_isInvertible X.presheaf X.ringCatSheaf.2 (G j) 0
  haveI := isInvertible_update G j (SheafOfModules.unit X.ringCatSheaf)
  have h0 := intersectionNumber_update_tensorPower_int k f i d hd G j (G j) 0
  rw [zero_mul] at h0
  refine (intersectionNumber_update_twistList k f i d hd G j M n (List.finRange s)
    (SheafOfModules.unit X.ringCatSheaf)).trans ?_
  rw [Fin.sum_univ_def]
  exact (congrArg (· + _) h0).trans (zero_add _)

end Multilinear

/-! ### Global sections -/

section Sections

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- **Global sections are left exact**: a monomorphism `F ⟶ G` into a coherent module gives
`h⁰(F) ≤ h⁰(G)`. -/
private theorem finrank_cohomologyOverField_zero_le_of_mono {F G : X.Modules} [G.IsCoherent]
    (φ : F ⟶ G) [Mono φ] :
    Module.finrank k (cohomologyOverField k f F 0) ≤
      Module.finrank k (cohomologyOverField k f G 0) := by
  obtain ⟨-, hinj, -, -, -⟩ := exists_cohomologyOverField_longExactSequence k f
    (ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel φ) ‹Mono φ›
      (inferInstance : Epi (Limits.cokernel.π φ)))
  have := finiteDimensional_cohomologyOverField_of_isProper k f G 0
  exact LinearMap.finrank_le_finrank_of_injective
    (f := (cohomologyOverFieldMap k f φ 0).hom) hinj

/-- A module with nonzero `h⁰` has a nonzero global section. -/
private theorem exists_ne_zero_of_finrank_ne_zero {N : X.Modules}
    (h : Module.finrank k (cohomologyOverField k f N 0) ≠ 0) :
    ∃ σ : N.val.obj (Opposite.op ⊤), σ ≠ 0 := by
  have e := cohomologyOverFieldZeroLinearEquivGlobalSectionsOver f N
  have : Nontrivial ((globalSectionsOver f).obj N) :=
    Module.nontrivial_of_finrank_pos (R := k) (e.finrank_eq ▸ Nat.pos_of_ne_zero h)
  exact exists_ne (0 : (globalSectionsOver f).obj N)

/-- **Multiplication by a nonzero section.** On an integral scheme, if the invertible module `V`
has a nonzero global section then `h⁰(U) ≤ h⁰(V ⊗ U)` for every invertible `U`: the section is a
regular section `𝒪_X ↪ V`, and tensoring with `U` is an equivalence, so it stays a monomorphism
`U ≅ 𝒪_X ⊗ U ↪ V ⊗ U`. -/
private theorem finrank_cohomologyOverField_zero_le_tens [IsIntegral X] (U V : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 U]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 V]
    (hV : Module.finrank k (cohomologyOverField k f V 0) ≠ 0) :
    Module.finrank k (cohomologyOverField k f U 0) ≤
      Module.finrank k (cohomologyOverField k f (tens V U) 0) := by
  obtain ⟨σ, hσ⟩ := exists_ne_zero_of_finrank_ne_zero k f hV
  have : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property V := ‹_›
  have hreg := isRegularSection_of_eval_top_ne_zero V (Stacks.SheafOfModules.sectionsOfTop V σ)
    (ne_of_eq_of_ne (Stacks.SheafOfModules.sectionsOfTop_eval_top V σ) hσ)
  let ι : SheafOfModules.unit X.ringCatSheaf ⟶ V :=
    V.unitHomEquiv.symm (Stacks.SheafOfModules.sectionsOfTop V σ)
  have hιm : Mono ι := hreg
  let T := (Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
    X.presheaf (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).flip.obj U
  have : T.IsEquivalence :=
    Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_stacksIsInvertible X.presheaf
      X.ringCatSheaf.2 U
  have hι : Mono (T.map ι) := @Functor.PreservesMonomorphisms.preserves _ _ _ _ T _ _ _ ι hιm
  have := Stacks.SheafOfModules.tensorProduct_isInvertible X.presheaf X.ringCatSheaf.2 V U
  have := SheafOfModules.isCoherent_of_isInvertible k f (tens V U)
  rw [finrank_cohomologyOverField_eq_of_iso k f
    (tensorProductLeftUnitor X.presheaf X.ringCatSheaf.2 U).symm 0]
  exact @finrank_cohomologyOverField_zero_le_of_mono k _ X f _ _ _ _ (T.map ι) hι

/-- **A nonzero section and an ample module.** On an integral surface `X` proper over `k`, an
invertible module `N` with a nonzero global section is trivial or has positive intersection
number `(N · A) > 0` with an ample invertible module `A`: the zero scheme `D` of the section is an
effective Cartier divisor with `𝒪_X(D) ≅ N`; if it is empty `N ≅ 𝒪_X`, and otherwise `D` is a
curve and `(N · A) = (A · D) > 0`. -/
private theorem nonempty_iso_unit_or_intersectionNumber_pos [IsIntegral X]
    (hdim : topologicalKrullDim X = (2 : ℕ)) (N A : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 A]
    (hA : Scheme.Modules.IsAmple X A)
    (hN : Module.finrank k (cohomologyOverField k f N 0) ≠ 0) :
    haveI : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (![N, A] j) := by
      intro j; fin_cases j <;> assumption
    Nonempty (N ≅ SheafOfModules.unit X.ringCatSheaf) ∨
      0 < intersectionNumber k f (𝟙 X) 2 hdim.le ![N, A] := by
  haveI : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (![N, A] j) := by
    intro j; fin_cases j <;> assumption
  obtain ⟨σ, hσ⟩ := exists_ne_zero_of_finrank_ne_zero k f hN
  have : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N := ‹_›
  have hS : (Stacks.SheafOfModules.sectionsOfTop N σ).eval (Opposite.op ⊤) ≠ 0 :=
    ne_of_eq_of_ne (Stacks.SheafOfModules.sectionsOfTop_eval_top N σ) hσ
  have hreg := isRegularSection_of_eval_top_ne_zero N _ hS
  have hD : Stacks.Divisors.IsEffectiveCartierDivisor (zeroScheme X N
      ((Stacks.SheafOfModules.sectionsOfTop N σ).eval (Opposite.op ⊤))) :=
    (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection X N _).2 hreg
  obtain ⟨e, -⟩ := (existsUnique_invertibleSheafIso_zeroScheme X N _ hreg).exists
  by_cases hne : Nonempty (zeroScheme X N
      ((Stacks.SheafOfModules.sectionsOfTop N σ).eval (Opposite.op ⊤))).subscheme
  · right
    have hdimD := topologicalKrullDim_subscheme_of_isEffectiveCartierDivisor k f _ hD
      (d := 1) hdim
    have hcut := intersectionNumber_eq_of_isEffectiveCartierDivisor' k f (𝟙 X) 1 hdim.le
      ![N, A] _ ((Scheme.Modules.pullbackId X).app N ≪≫ e.symm)
    refine lt_of_lt_of_eq ?_ hcut.symm
    exact intersectionNumber_pos k f _ 1 hdimD _ fun j => by fin_cases j; exact hA
  · left
    have htop : zeroScheme X N
        ((Stacks.SheafOfModules.sectionsOfTop N σ).eval (Opposite.op ⊤)) = ⊤ := by
      rw [← Scheme.IdealSheafData.support_eq_bot_iff]
      apply SetLike.coe_injective
      rw [← Scheme.IdealSheafData.range_subschemeι]
      haveI := not_nonempty_iff.mp hne
      exact Set.range_eq_empty _
    exact ⟨e.symm ≪≫ eqToIso (congrArg Stacks.Divisors.invertibleSheaf' htop) ≪≫
      Stacks.Divisors.invertibleSheafTopIsoUnit⟩

/-- **The Euler characteristics of the powers of an invertible module on a surface.** On a
scheme of dimension at most two proper over `k`, `t ↦ χ(L^{⊗ t})` is a quadratic polynomial
with leading coefficient `(L · L)/2` ([Stacks, Tag 0BEM] in one variable; the intersection
number is the second difference `χ(𝒪_X) - 2χ(L^{⊗ -1}) + χ(L^{⊗ -2})`). -/
private theorem exists_eulerCharacteristic_tensorPower_eq (hd : topologicalKrullDim X ≤ (2 : ℕ))
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    haveI : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (![L, L] j) := by
      intro j; fin_cases j <;> assumption
    ∃ b c : ℚ, ∀ t : ℤ,
      ((@eulerCharacteristic k _ X f _ (tensorPower X.presheaf X.ringCatSheaf.2 L t)
          (SheafOfModules.isCoherent_of_isInvertible k f _) : ℤ) : ℚ) =
        (intersectionNumber k f (𝟙 X) 2 hd ![L, L] : ℚ) / 2 * t ^ 2 + b * t + c := by
  classical
  haveI : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (![L, L] j) := by
    intro j; fin_cases j <;> assumption
  haveI hunit : (SheafOfModules.unit X.ringCatSheaf : X.Modules).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k f
  let q : ℤ → ℤ := fun t => @eulerCharacteristic k _ X f _
    (tensorPower X.presheaf X.ringCatSheaf.2 L t) (SheafOfModules.isCoherent_of_isInvertible k f _)
  -- the Euler polynomial in one variable
  obtain ⟨P, hP0, hP⟩ := exists_eulerPolynomial_twistedSheaf_of_isProper k f
    (fun _ : Fin 1 => L) (SheafOfModules.unit X.ringCatSheaf) hunit
  have htotal : P.totalDegree ≤ 2 := by
    rcases hP0 with h | h
    · simp [h]
    · exact_mod_cast h.trans ((topologicalKrullDim_subspace_le X _).trans hd)
  let p : Polynomial ℚ := MvPolynomial.uniqueAlgEquiv ℚ (Fin 1) P
  have hcoeff : ∀ s, 2 < s → p.coeff s = 0 := by
    intro s hs
    change (MvPolynomial.uniqueAlgEquiv ℚ (Fin 1) P).coeff s = 0
    rw [MvPolynomial.coeff_uniqueAlgEquiv]
    by_contra hne
    have hle := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.2 hne)
    rw [Finsupp.sum_single_index rfl] at hle
    omega
  have hpeval : ∀ m : ℤ, p.eval (m : ℚ) = q m := by
    intro m
    have he : p.eval₂ (RingHom.id ℚ) (m : ℚ) =
        P.eval₂ (RingHom.id ℚ) (fun _ : Fin 1 => (m : ℚ)) :=
      MvPolynomial.eval₂_const_uniqueAlgEquiv
    rw [Polynomial.eval₂_id] at he
    rw [he, MvPolynomial.eval₂_id, hP (fun _ => m)]
    have eiso : twistedSheaf (SheafOfModules.unit X.ringCatSheaf) (fun _ : Fin 1 => L)
        (fun _ => m) ≅ tensorPower X.presheaf X.ringCatSheaf.2 L m :=
      MMP.Mori.Twist.twistedSheafUnitIsoTensorPower (fun _ : Fin 1 => L) L
          (fun _ => Iso.refl L) (fun _ => m) ≪≫
        tensorPowerReindex X.presheaf X.ringCatSheaf.2 L (by simp)
    haveI : (twistedSheaf (SheafOfModules.unit X.ringCatSheaf) (fun _ : Fin 1 => L)
        (fun _ => m)).IsCoherent := twistedSheaf_isCoherent _ _ _
    haveI := SheafOfModules.isCoherent_of_isInvertible k f
      (tensorPower X.presheaf X.ringCatSheaf.2 L m)
    exact_mod_cast eulerCharacteristic_eq_of_iso k f eiso
  have hpx : ∀ x : ℚ, p.eval x = p.coeff 0 + p.coeff 1 * x + p.coeff 2 * x ^ 2 := by
    intro x
    have hnat : p.natDegree < 3 := by
      by_contra h
      replace h := not_lt.mp h
      have h0 : p.coeff p.natDegree = 0 := hcoeff _ (by omega)
      rw [Polynomial.coeff_natDegree, Polynomial.leadingCoeff_eq_zero] at h0
      rw [h0, Polynomial.natDegree_zero] at h
      omega
    rw [Polynomial.eval_eq_sum_range' hnat]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    ring
  -- the intersection number is the second difference
  have hterm : ∀ I : Finset (Fin 2),
      @eulerCharacteristic k _ X (𝟙 X ≫ f) inferInstance
        (twistedSheaf (SheafOfModules.unit X.ringCatSheaf)
          (fun j => (Scheme.Modules.pullback (𝟙 X)).obj (![L, L] j))
          (fun j => if j ∈ I then -1 else 0))
        (isCoherent_twistedSheafUnitPullback k f (𝟙 X) _ _) = q (-(I.card : ℤ)) := by
    intro I
    have hsum : (∑ j : Fin 2, if j ∈ I then (-1 : ℤ) else 0) = -(I.card : ℤ) := by
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_neg,
        mul_one]
    have eiso : twistedSheaf (SheafOfModules.unit X.ringCatSheaf)
        (fun j => (Scheme.Modules.pullback (𝟙 X)).obj (![L, L] j))
        (fun j => if j ∈ I then -1 else 0) ≅
        tensorPower X.presheaf X.ringCatSheaf.2 L (-(I.card : ℤ)) :=
      MMP.Mori.Twist.twistedSheafUnitIsoTensorPower _ L
          (fun j => (Scheme.Modules.pullbackId X).app _ ≪≫ eqToIso (by fin_cases j <;> rfl)) _ ≪≫
        tensorPowerReindex X.presheaf X.ringCatSheaf.2 L hsum
    haveI := isCoherent_twistedSheafUnitPullback k f (𝟙 X) ![L, L]
      (fun j => if j ∈ I then -1 else 0)
    haveI := SheafOfModules.isCoherent_of_isInvertible k f
      (tensorPower X.presheaf X.ringCatSheaf.2 L (-(I.card : ℤ)))
    rw [eulerCharacteristic_eq_of_iso k (𝟙 X ≫ f) eiso]
    exact eulerCharacteristic_congr_hom k (Category.id_comp f) _
  have hII : (intersectionNumber k f (𝟙 X) 2 hd ![L, L] : ℤ) = q 0 - 2 * q (-1) + q (-2) := by
    rw [← Snapper.sheafIntersectionNumber_eq_intersectionNumber, sheafIntersectionNumber]
    simp only [hterm]
    rw [← Finset.powerset_univ, Finset.sum_powerset_apply_card
      (f := fun m => (-1 : ℤ) ^ m * q (-(m : ℤ)))]
    simp [Finset.sum_range_succ]
    ring
  refine ⟨p.coeff 1, p.coeff 0, fun t => ?_⟩
  rw [show ((q t : ℤ) : ℚ) = _ from rfl, ← hpeval, hpx, hII]
  push_cast
  rw [← hpeval, ← hpeval, ← hpeval, hpx, hpx, hpx]
  push_cast
  ring

end Sections

/-! ### The intersection pairing on a surface -/

section Pairing

variable (k : Type u) [Field k] {S : Scheme.{u}} (f : S ⟶ Spec (.of k)) [IsProper f]
  (hd : topologicalKrullDim S ≤ (2 : ℕ))

/-- The pair `![N₁, N₂]` of invertible sheaves is a family of invertible sheaves. -/
private theorem isInvertible_pair (N₁ N₂ : S.Modules)
    [h₁ : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₁]
    [h₂ : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₂] :
    ∀ j : Fin 2, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (![N₁, N₂] j) := by
  intro j
  fin_cases j
  exacts [h₁, h₂]

/-- The intersection pairing `(N₁ · N₂)` of two invertible sheaves on a proper surface. -/
private noncomputable def pair (N₁ N₂ : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₁]
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₂] : ℤ :=
  haveI := isInvertible_pair N₁ N₂
  AlgebraicGeometry.intersectionNumber k f (𝟙 S) 2 hd ![N₁, N₂]

/-- The pairing is the intersection number of the family `![N₁, N₂]`. -/
private theorem pair_def (N₁ N₂ : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₁]
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₂] :
    haveI := isInvertible_pair N₁ N₂
    pair k f hd N₁ N₂ = AlgebraicGeometry.intersectionNumber k f (𝟙 S) 2 hd ![N₁, N₂] := rfl

/-- The pairing is symmetric. -/
private theorem pair_comm (N₁ N₂ : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₁]
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₂] :
    pair k f hd N₁ N₂ = pair k f hd N₂ N₁ := by
  haveI := isInvertible_pair N₁ N₂
  haveI := isInvertible_pair N₂ N₁
  rw [pair_def, pair_def,
    ← AlgebraicGeometry.intersectionNumber_comp_perm k f (𝟙 S) 2 hd ![N₂, N₁] (Equiv.swap 0 1)]
  exact AlgebraicGeometry.intersectionNumber_congr_family k f (𝟙 S) 2 hd
    (funext fun j => by fin_cases j <;> rfl)

/-- The pairing depends only on the isomorphism class of the first sheaf. -/
private theorem pair_congr_left {N₁ N₁' : S.Modules} (N₂ : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₁]
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₁']
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₂] (e : N₁ ≅ N₁') :
    pair k f hd N₁ N₂ = pair k f hd N₁' N₂ := by
  haveI := isInvertible_pair N₁ N₂
  haveI := isInvertible_pair N₁' N₂
  rw [pair_def, pair_def]
  exact AlgebraicGeometry.intersectionNumber_eq_of_iso_at k f (𝟙 S) 2 hd _ _ 0
    (fun q hq => by fin_cases q <;> first | exact absurd rfl hq | rfl) e

/-- The pairing of a Weil divisor sum: `(𝒪(D + D') · N) = (𝒪(D) · N) + (𝒪(D') · N)`. -/
private theorem pair_divisorialSheaf_add [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
    {D D' : Divisor S} (hD : D.IsCartier) (hD' : D'.IsCartier) (N : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N] :
    haveI : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 D.divisorialSheaf :=
      hD.isInvertibleModule_divisorialSheaf
    haveI : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 D'.divisorialSheaf :=
      hD'.isInvertibleModule_divisorialSheaf
    haveI : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (D + D').divisorialSheaf :=
      (hD.add hD').isInvertibleModule_divisorialSheaf
    pair k f hd (D + D').divisorialSheaf N =
      pair k f hd D.divisorialSheaf N + pair k f hd D'.divisorialSheaf N := by
  haveI : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 D.divisorialSheaf :=
    hD.isInvertibleModule_divisorialSheaf
  haveI : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 D'.divisorialSheaf :=
    hD'.isInvertibleModule_divisorialSheaf
  haveI : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (D + D').divisorialSheaf :=
    (hD.add hD').isInvertibleModule_divisorialSheaf
  haveI := isInvertible_pair (D + D').divisorialSheaf N
  haveI := isInvertible_pair D.divisorialSheaf N
  haveI := isInvertible_pair D'.divisorialSheaf N
  rw [pair_def, pair_def, pair_def]
  exact AlgebraicGeometry.intersectionNumber_tensor k f (𝟙 S) 2 hd 0 _ _ _
    (fun q hq => by fin_cases q <;> first | exact absurd rfl hq | rfl)
    (fun q hq => by fin_cases q <;> first | exact absurd rfl hq | rfl)
    (hD.divisorialSheafTensorIso hD').symm

/-- **Cutting down by a curve.** On a smooth proper surface, the pairing of an invertible sheaf
`I ≅ 𝒪_S(P)` of a prime divisor `P` with `N` is the degree of `N` on the proper curve `C` with
the same generic point. -/
private theorem pair_eq_degree_of_iso_invertibleSheaf [IsLocallyNoetherian S] [IsNormal S]
    (hsm : IsSmoothScheme f) (P : MMP.Mori.PrimeDivisor S) (C : ProperCurve f)
    (hC : C.point = P.genericPoint) (I N : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 I]
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N]
    (e : I ≅ (Stacks.Divisors.invertibleSheaf' P.idealSheaf : S.Modules)) :
    pair k f hd I N = C.degree k N := by
  haveI := MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsm P
  haveI := isInvertible_pair I N
  have hL : (Scheme.Modules.pullback (𝟙 S)).obj (![I, N] 0) ≅
      (Stacks.Divisors.invertibleSheaf P.idealSheaf : S.Modules) :=
    (Scheme.Modules.pullbackId S).app I ≪≫ e
  rw [pair_def, AlgebraicGeometry.intersectionNumber_eq_of_isEffectiveCartierDivisor' k f (𝟙 S) 1
    hd ![I, N] P.idealSheaf hL]
  rw [ProperCurve.degree, degreeOn,
    ← AlgebraicGeometry.intersectionNumber_one_eq_invertibleCurveDegree k f C.ι C.dim_le N]
  rw [AlgebraicGeometry.intersectionNumber_congr_family k f _ 1 _
    (show (fun t : Fin 1 => ![I, N] t.succ) = fun _ => N from funext fun t => by fin_cases t; rfl)]
  rw [← Snapper.sheafIntersectionNumber_eq_intersectionNumber]
  have hker : (P.idealSheaf.subschemeι ≫ 𝟙 S).ker = C.ι.ker := by
    rw [Category.comp_id, Scheme.IdealSheafData.ker_subschemeι,
      Scheme.IdealSheafData.ker_subschemeι, hC,
      MMP.Mori.vanishingIdeal_closure_genericPoint_eq_idealSheaf]
  exact (sheafIntersectionNumber_eq_of_ker_eq k f _ _ hker 1 _ C.dim_le _).trans
    (Snapper.sheafIntersectionNumber_eq_intersectionNumber k f C.ι 1 _ _)

/-- An intersection number of two sheaves on `S` is their pairing. -/
private theorem sheafIntersectionNumber_two_eq_pair (L : Fin 2 → S.Modules)
    [hL : ∀ j, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (L j)]
    (hd' : topologicalKrullDim S ≤ (2 : ℕ)) :
    sheafIntersectionNumber k f (𝟙 S) 2 hd' L = pair k f hd (L 0) (L 1) := by
  haveI := isInvertible_pair (L 0) (L 1)
  rw [Snapper.sheafIntersectionNumber_eq_intersectionNumber, pair_def]
  exact AlgebraicGeometry.intersectionNumber_congr_family k f (𝟙 S) 2 hd
    (funext fun j => by fin_cases j <;> rfl)

/-- The self-intersection `(M²)` of a rational combination `M = ∑ cᵢ Mᵢ`, as a double sum of
pairings. -/
private theorem sheafCombinationIntersectionNumber_two_eq_sum {s : ℕ} (c : Fin s → ℚ)
    (M : Fin s → S.Modules) [∀ j, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (M j)]
    (hd' : topologicalKrullDim S ≤ ((2 + 0 : ℕ) : WithBot ℕ∞)) :
    haveI : ∀ j : Fin 0, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
        ((![] : Fin 0 → S.Modules) j) := fun j => j.elim0
    sheafCombinationIntersectionNumber k f (𝟙 S) ℚ c M 2 ![] hd' =
      ∑ i, ∑ j, c i * c j * (pair k f hd (M i) (M j) : ℚ) := by
  haveI : ∀ j : Fin 0, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
      ((![] : Fin 0 → S.Modules) j) := fun j => j.elim0
  rw [sheafCombinationIntersectionNumber, ← Fintype.sum_prod_type',
    ← (finTwoArrowEquiv (Fin s)).symm.sum_comp]
  refine Fintype.sum_congr _ _ fun p => ?_
  rw [Fin.prod_univ_two]
  congr 1
  exact_mod_cast sheafIntersectionNumber_two_eq_pair k f hd _ hd'
    (hL := isInvertible_finAppend (a := 2) (b := 0) _ _)

/-- The intersection number `(M · H)` of a rational combination `M = ∑ cᵢ Mᵢ` with `H`, as a sum
of pairings. -/
private theorem sheafCombinationIntersectionNumber_one_eq_sum {s : ℕ} (c : Fin s → ℚ)
    (M : Fin s → S.Modules) [∀ j, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (M j)]
    (H : S.Modules) [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 H]
    (hd' : topologicalKrullDim S ≤ ((1 + 1 : ℕ) : WithBot ℕ∞)) :
    haveI : ∀ j : Fin 1, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
        ((![H] : Fin 1 → S.Modules) j) := fun _ => by simpa
    sheafCombinationIntersectionNumber k f (𝟙 S) ℚ c M 1 ![H] hd' =
      ∑ i, c i * (pair k f hd (M i) H : ℚ) := by
  haveI : ∀ j : Fin 1, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
      ((![H] : Fin 1 → S.Modules) j) := fun _ => by simpa
  rw [sheafCombinationIntersectionNumber, ← (Equiv.funUnique (Fin 1) (Fin s)).symm.sum_comp]
  refine Fintype.sum_congr _ _ fun i => ?_
  rw [Fin.prod_univ_one]
  congr 1
  exact_mod_cast sheafIntersectionNumber_two_eq_pair k f hd _ hd'
    (hL := isInvertible_finAppend (a := 1) (b := 1) _ _)

end Pairing

section PowerPairing

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} [IsProper f]
  {hd : topologicalKrullDim X ≤ (2 : ℕ)}

/-- Replacing the first entry of a pair gives the pair with the new entry. -/
private theorem intersectionNumber_update_zero_pair (B C N : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 B]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 C]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N] :
    haveI := isInvertible_pair B C
    haveI := isInvertible_update ![B, C] 0 N
    intersectionNumber k f (𝟙 X) 2 hd (Function.update ![B, C] 0 N) = pair k f hd N C := by
  haveI := isInvertible_pair B C
  haveI := isInvertible_update ![B, C] 0 N
  haveI := isInvertible_pair N C
  exact intersectionNumber_congr_family k f (𝟙 X) 2 hd (funext fun j => by fin_cases j <;> rfl)

/-- `(N^{⊗ t} · B) = t (N · B)`. -/
private theorem pair_tensorPower_left (N B : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 B] (t : ℤ) :
    haveI := tensorPower_isInvertible X.presheaf X.ringCatSheaf.2 N t
    pair k f hd (tensorPower X.presheaf X.ringCatSheaf.2 N t) B = t * pair k f hd N B := by
  haveI := tensorPower_isInvertible X.presheaf X.ringCatSheaf.2 N t
  haveI := isInvertible_pair B B
  exact (intersectionNumber_update_zero_pair B B _).symm.trans
    ((intersectionNumber_update_tensorPower_int k f (𝟙 X) 2 hd ![B, B] 0 N t).trans
      (congrArg _ (intersectionNumber_update_zero_pair B B N)))

/-- `(N^{⊗ t} · N^{⊗ t}) = t² (N · N)`. -/
private theorem pair_tensorPower_tensorPower (N : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N] (t : ℤ) :
    haveI := tensorPower_isInvertible X.presheaf X.ringCatSheaf.2 N t
    pair k f hd (tensorPower X.presheaf X.ringCatSheaf.2 N t)
      (tensorPower X.presheaf X.ringCatSheaf.2 N t) = t * t * pair k f hd N N := by
  haveI := tensorPower_isInvertible X.presheaf X.ringCatSheaf.2 N t
  exact (pair_tensorPower_left N _ t).trans <| .trans (congrArg (t * ·)
    ((pair_comm k f hd N _).trans (pair_tensorPower_left N N t))) (mul_assoc _ _ _).symm

/-- `(L · B) = ∑ₗ nₗ (Mₗ · B)` for `L = 𝒪_X ⊗ M₁^{⊗ n₁} ⊗ ⋯ ⊗ M_s^{⊗ n_s}`. -/
private theorem pair_twistedSheaf_left {s : ℕ} (M : Fin s → X.Modules)
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M q)] (n : Fin s → ℤ)
    (B : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 B] :
    haveI := tensorPower_isInvertible X.presheaf X.ringCatSheaf.2 B 0
    haveI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
        (twistedSheaf (SheafOfModules.unit X.ringCatSheaf) M n) :=
      isInvertible_twistList M n (List.finRange s) (SheafOfModules.unit X.ringCatSheaf)
    pair k f hd (twistedSheaf (SheafOfModules.unit X.ringCatSheaf) M n) B =
      ∑ q, n q * pair k f hd (M q) B := by
  haveI := tensorPower_isInvertible X.presheaf X.ringCatSheaf.2 B 0
  haveI := isInvertible_pair B B
  haveI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (twistedSheaf (SheafOfModules.unit X.ringCatSheaf) M n) :=
    isInvertible_twistList M n (List.finRange s) (SheafOfModules.unit X.ringCatSheaf)
  exact (intersectionNumber_update_zero_pair B B _).symm.trans
    ((intersectionNumber_update_twistedSheaf k f (𝟙 X) 2 hd ![B, B] 0 M n).trans
      (Finset.sum_congr rfl fun q _ => congrArg _ (intersectionNumber_update_zero_pair B B (M q))))

end PowerPairing

/-! ### Clearing denominators -/

/-- Finitely many rationals have a common positive denominator. -/
private theorem exists_nat_mul_eq_intCast {s : ℕ} (c : Fin s → ℚ) :
    ∃ b : ℕ, 0 < b ∧ ∃ n : Fin s → ℤ, ∀ j, (n j : ℚ) = b * c j := by
  refine ⟨∏ j, (c j).den, Finset.prod_pos fun j _ => (c j).den_pos,
    fun j => (c j).num * ((∏ i, (c i).den) / (c j).den : ℕ), fun j => ?_⟩
  obtain ⟨m, hm⟩ : (c j).den ∣ ∏ i, (c i).den := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  dsimp only
  rw [hm, Nat.mul_div_cancel_left _ (c j).den_pos]
  push_cast
  rw [← Rat.mul_den_eq_num]
  ring

/-! ### The inequality for one invertible module -/

section Single

variable (k : Type u) [Field k] {W : Scheme.{u}} (f : W ⟶ Spec (.of k)) [IsProper f]
  [IsIntegral W] (hdim : topologicalKrullDim W = (2 : ℕ))
  (A : W.Modules) [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 A]
  (hA : Scheme.Modules.IsAmple W A) (L : W.Modules)
  [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L]

include hA

/-- **No sections of the nonzero powers.** On an integral proper surface, if `(L · A) = 0` for
an ample `A` and `(L²) > 0`, then `L^{⊗ t}` has no nonzero global section for `t ≠ 0`. -/
private theorem finrank_cohomologyOverField_tensorPower_eq_zero
    (hLA : pair k f hdim.le L A = 0) (hLL : 0 < pair k f hdim.le L L) {t : ℤ}
    (ht : t ≠ 0) :
    Module.finrank k (cohomologyOverField k f (tensorPower W.presheaf W.ringCatSheaf.2 L t) 0)
      = 0 := by
  haveI := tensorPower_isInvertible W.presheaf W.ringCatSheaf.2 L t
  by_contra h
  rcases nonempty_iso_unit_or_intersectionNumber_pos k f hdim _ A hA h with he | hp
  · obtain ⟨e⟩ := he
    haveI := isInvertible_pair (tensorPower W.presheaf W.ringCatSheaf.2 L t)
      (tensorPower W.presheaf W.ringCatSheaf.2 L t)
    have h0 : pair k f hdim.le (tensorPower W.presheaf W.ringCatSheaf.2 L t)
        (tensorPower W.presheaf W.ringCatSheaf.2 L t) = 0 :=
      (Snapper.sheafIntersectionNumber_eq_intersectionNumber ..).symm.trans
        (sheafIntersectionNumber_eq_zero_of_iso_unit k f (𝟙 W) 2 hdim.le _ 0 e)
    exact mul_ne_zero (mul_ne_zero ht ht) hLL.ne' ((pair_tensorPower_tensorPower L t).symm.trans h0)
  · exact hp.ne' ((pair_tensorPower_left L A t).trans (by rw [hLA, mul_zero]))

/-- **The Hodge index inequality for one invertible module.** On a smooth projective surface
`W` over a field, if `(L · A) = 0` for an ample `A` then `(L²) ≤ 0`.

Otherwise `L^{⊗ t}` has no sections for `t ≠ 0`, so Serre duality gives
`χ(L^{⊗ t}) ≤ h⁰(ω_W ⊗ L^{⊗ -t})`, and `χ(L^{⊗ t})` grows like `(L²) t² / 2`. For `t` large,
`χ(L^{⊗ -t}) > 0` gives a nonzero section of `ω_W ⊗ L^{⊗ t}`, and multiplication by it bounds
`h⁰(ω_W ⊗ L^{⊗ -t}) ≤ h⁰(ω_W^{⊗ 2})`, which contradicts the growth of `χ(L^{⊗ t})`. -/
private theorem pair_self_nonpos [Smooth f] [MMP.Mori.IsProjectiveVariety k f]
    (hLA : pair k f hdim.le L A = 0) : pair k f hdim.le L L ≤ 0 := by
  refine not_lt.mp fun hLL => ?_
  have hsm : IsSmoothScheme f := (isSmoothScheme_iff f).2 inferInstance
  let Lt : ℤ → W.Modules := tensorPower W.presheaf W.ringCatSheaf.2 L
  haveI : ∀ t, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 (Lt t) :=
    tensorPower_isInvertible W.presheaf W.ringCatSheaf.2 L
  let ω := Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) 2
  haveI : SmoothOfRelativeDimension 2 f := smoothOfRelativeDimension_of_equidimensional k f
    (TopologicalSpace.Equidimensional.of_preirreducibleSpace W) 2 hdim
  haveI : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 ω :=
    Stacks.Discriminant.isInvertible_relativeDifferentialForms f 2
  haveI : ∀ t, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 (tens ω (Lt t)) :=
    fun t => Stacks.SheafOfModules.tensorProduct_isInvertible W.presheaf W.ringCatSheaf.2 ω (Lt t)
  let h0 : W.Modules → ℕ := fun F => Module.finrank k (cohomologyOverField k f F 0)
  let q : ℤ → ℤ := fun t => @eulerCharacteristic k _ W f _ (Lt t)
    (SheafOfModules.isCoherent_of_isInvertible k f _)
  let eG : ∀ a b : ℤ, a + b = 0 → (tens (Lt a) (Lt b) ≅ SheafOfModules.unit W.ringCatSheaf) :=
    fun a b hab => (tensorPowerCoherence W.presheaf W.ringCatSheaf.2 L).mulIso a b ≪≫
      tensorPowerReindex W.presheaf W.ringCatSheaf.2 L hab
  -- Serre duality, with `h⁰(L^{⊗ a}) = 0` for `a ≠ 0`
  have hdual : ∀ a b : ℤ, a + b = 0 → a ≠ 0 → (q a : ℚ) ≤ h0 (tens ω (Lt b)) := fun a b hab ha => by
    haveI := SheafOfModules.isCoherent_of_isInvertible k f (Lt a)
    have := eulerCharacteristic_le_finrank_add_finrank k f hsm hdim (Lt b) (Lt a)
      (tens ω (Lt b)) (eG a b hab) (Iso.refl _)
    have hv : h0 (Lt a) = 0 :=
      finrank_cohomologyOverField_tensorPower_eq_zero k f hdim A hA L hLA hLL ha
    have : q a ≤ (h0 (Lt a) : ℤ) + h0 (tens ω (Lt b)) := this
    exact_mod_cast (by omega : q a ≤ h0 (tens ω (Lt b)))
  -- Riemann–Roch: `χ(L^{⊗ t})` is quadratic with leading coefficient `(L²)/2 > 0`
  obtain ⟨β, γ, hq⟩ := exists_eulerCharacteristic_tensorPower_eq k f hdim.le L
  obtain ⟨t, ht1, hK, hneg⟩ := exists_lt_quadratic (a := γ) (b := β)
    (K := (h0 (tens ω ω) : ℚ)) (c := (pair k f hdim.le L L : ℚ) / 2)
    (div_pos (Int.cast_pos.mpr hLL) two_pos)
  have ht0 : (t : ℤ) ≠ 0 := by omega
  have hq' : ∀ t : ℤ, (q t : ℚ) = (pair k f hdim.le L L : ℚ) / 2 * t ^ 2 + β * t + γ := hq
  have hqt := hq' t
  have hqt' := hq' (-t)
  push_cast at hqt hqt'
  -- `χ(L^{⊗ -t}) > 0` gives a nonzero section of `ω_W ⊗ L^{⊗ t}`
  have hsec : h0 (tens ω (Lt t)) ≠ 0 := fun hz => by
    have := hdual (-t) t (neg_add_cancel _) (neg_ne_zero.mpr ht0)
    rw [hz, Nat.cast_zero] at this
    linarith
  -- multiplication by it bounds `h⁰(ω_W ⊗ L^{⊗ -t})` by `h⁰(ω_W ⊗ ω_W)`
  have hmul : h0 (tens ω (Lt (-t))) ≤ h0 (tens ω ω) :=
    (finrank_cohomologyOverField_zero_le_tens k f (tens ω (Lt (-t))) (tens ω (Lt t)) hsec).trans
      (finrank_cohomologyOverField_eq_of_iso k f
        (tensorProductAssociator W.presheaf W.ringCatSheaf.2 ω (Lt t) (tens ω (Lt (-t))) ≪≫
          tensorProductIso W.presheaf W.ringCatSheaf.2 (Iso.refl ω)
            ((tensorProductAssociator W.presheaf W.ringCatSheaf.2 (Lt t) ω (Lt (-t))).symm ≪≫
              tensorProductIso W.presheaf W.ringCatSheaf.2
                (tensorProductBraiding W.presheaf W.ringCatSheaf.2 (Lt t) ω) (Iso.refl _) ≪≫
              tensorProductAssociator W.presheaf W.ringCatSheaf.2 ω (Lt t) (Lt (-t)) ≪≫
              tensorProductIso W.presheaf W.ringCatSheaf.2 (Iso.refl ω)
                (eG t (-t) (add_neg_cancel _)) ≪≫
              tensorProductRightUnitor W.presheaf W.ringCatSheaf.2 ω)) 0).le
  have := hdual t (-t) (add_neg_cancel _) ht0
  change (q t : ℚ) ≤ _ at this
  have : (h0 (tens ω (Lt (-t))) : ℚ) ≤ h0 (tens ω ω) := by exact_mod_cast hmul
  linarith

end Single

/-- **Divisors orthogonal to an ample class have non-positive square.** Let `W` be a smooth
projective surface over a field `k`, `A` an ample invertible sheaf on `W`
and `P = ∑ⱼ cⱼ Mⱼ` a rational combination of invertible sheaves `Mⱼ`. If `(P · A) = 0`, then
`(P²) ≤ 0`. -/
public theorem sheafCombinationIntersectionNumber_two_nonpos_of_isAmple'
    (k : Type u) [Field k] {W : Scheme.{u}} (f : W ⟶ Spec (.of k))
    [IsProper f] [Smooth f] (hW : IsProjectiveVariety k f) (hdim : topologicalKrullDim W = 2)
    (A : W.Modules) [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 A]
    [Stacks.Ample.IsInvertibleModule W A] (hA : Stacks.Ample.IsAmple W A)
    {s : ℕ} (c : Fin s → ℚ) (M : Fin s → W.Modules)
    [∀ j, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 (M j)] :
    haveI : ∀ j : Fin 1, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2
        ((![A] : Fin 1 → W.Modules) j) := fun _ => by simpa
    haveI : ∀ j : Fin 0, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2
        ((![] : Fin 0 → W.Modules) j) := fun j => j.elim0
    sheafCombinationIntersectionNumber k f (𝟙 W) ℚ c M 1 ![A] (by rw [hdim]; rfl) = 0 →
      sheafCombinationIntersectionNumber k f (𝟙 W) ℚ c M 2 ![] (by rw [hdim]; rfl) ≤ 0 := by
  intro hPA
  have hdim2 : topologicalKrullDim W = (2 : ℕ) := hdim
  haveI : AlgebraicGeometry.IsProjectiveVariety k f := hW
  rw [sheafCombinationIntersectionNumber_one_eq_sum k f hdim2.le] at hPA
  rw [sheafCombinationIntersectionNumber_two_eq_sum k f hdim2.le]
  -- `L = 𝒪_W ⊗ M₁^{⊗ n₁} ⊗ ⋯` is the class of `b P`
  obtain ⟨b, hb, n, hn⟩ := exists_nat_mul_eq_intCast c
  haveI := tensorPower_isInvertible W.presheaf W.ringCatSheaf.2 A 0
  haveI : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2
      (twistedSheaf (SheafOfModules.unit W.ringCatSheaf) M n) :=
    isInvertible_twistList M n (List.finRange s) (SheafOfModules.unit W.ringCatSheaf)
  have hL : ∀ (B : W.Modules) [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 B],
      (pair k f hdim2.le (twistedSheaf (SheafOfModules.unit W.ringCatSheaf) M n) B : ℚ) =
        b * ∑ j, c j * (pair k f hdim2.le (M j) B : ℚ) := fun B _ => by
    rw [pair_twistedSheaf_left]
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hn j]; ring
  have hLA := pair_self_nonpos k f hdim2 A
    (Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple W A hA)
    (twistedSheaf (SheafOfModules.unit W.ringCatSheaf) M n)
    (by have := hL A; rw [hPA, mul_zero] at this; exact_mod_cast this)
  have hLL : (pair k f hdim2.le (twistedSheaf (SheafOfModules.unit W.ringCatSheaf) M n)
      (twistedSheaf (SheafOfModules.unit W.ringCatSheaf) M n) : ℚ) =
      b ^ 2 * ∑ i, ∑ j, c i * c j * (pair k f hdim2.le (M i) (M j) : ℚ) := by
    have hc : ∀ (B C : W.Modules) [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 B]
        [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 C],
        (pair k f hdim2.le B C : ℚ) = pair k f hdim2.le C B := fun B C _ _ =>
      congrArg Int.cast (pair_comm k f hdim2.le B C)
    rw [hL, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc, hL]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hc (M j)]
    ring
  have : (pair k f hdim2.le (twistedSheaf (SheafOfModules.unit W.ringCatSheaf) M n)
      (twistedSheaf (SheafOfModules.unit W.ringCatSheaf) M n) : ℚ) ≤ 0 := by exact_mod_cast hLA
  rw [hLL] at this
  exact nonpos_of_mul_nonpos_right this (by positivity)

/-- **Divisors orthogonal to an ample class have non-positive square.** Let `W` be a smooth
projective surface over an algebraically closed field `k`, `A` an ample invertible sheaf on `W`
and `P = ∑ⱼ cⱼ Mⱼ` a rational combination of invertible sheaves `Mⱼ`. If `(P · A) = 0`, then
`(P²) ≤ 0`.
The proof does not use that `k` is algebraically closed: see
`sheafCombinationIntersectionNumber_two_nonpos_of_isAmple'`. -/
@[mmp "lem_fourfold_surface_orthogonal_square_nonpositive"]
public theorem sheafCombinationIntersectionNumber_two_nonpos_of_isAmple
    (k : Type u) [Field k] [IsAlgClosed k] {W : Scheme.{u}} (f : W ⟶ Spec (.of k))
    [IsProper f] [Smooth f] (hW : IsProjectiveVariety k f) (hdim : topologicalKrullDim W = 2)
    (A : W.Modules) [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 A]
    [Stacks.Ample.IsInvertibleModule W A] (hA : Stacks.Ample.IsAmple W A)
    {s : ℕ} (c : Fin s → ℚ) (M : Fin s → W.Modules)
    [∀ j, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 (M j)] :
    haveI : ∀ j : Fin 1, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2
        ((![A] : Fin 1 → W.Modules) j) := fun _ => by simpa
    haveI : ∀ j : Fin 0, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2
        ((![] : Fin 0 → W.Modules) j) := fun j => j.elim0
    sheafCombinationIntersectionNumber k f (𝟙 W) ℚ c M 1 ![A] (by rw [hdim]; rfl) = 0 →
      sheafCombinationIntersectionNumber k f (𝟙 W) ℚ c M 2 ![] (by rw [hdim]; rfl) ≤ 0 :=
  sheafCombinationIntersectionNumber_two_nonpos_of_isAmple' k f hW hdim A hA c M

/-! ### The null case -/

/-- A scheme smooth over a field is normal: its local rings are regular. -/
private theorem isNormal_of_smooth {k : Type u} [Field k] {S : Scheme.{u}}
    (f : S ⟶ Spec (.of k)) [Smooth f] : IsNormal S where
  stalk_isDomain x :=
    have := isRegularLocalRing_stalk_of_smooth_over_field f x
    (AlgebraicGeometry.isNormalDomain_of_isRegularLocalRing _).1
  stalk_normal x :=
    have := isRegularLocalRing_stalk_of_smooth_over_field f x
    (AlgebraicGeometry.isNormalDomain_of_isRegularLocalRing _).2

/-- The double sum of `c'ₓ c'ᵧ Bₓᵧ` over the extended coefficient vector
`c' = (n c₁, …, n c_s, a, b)`. -/
private theorem sum_sum_append_mul (s : ℕ) (n a b : ℚ) (c : Fin s → ℚ)
    (B : Fin (s + 2) → Fin (s + 2) → ℚ) :
    ∑ x, ∑ y, Fin.append (fun i => n * c i) ![a, b] x * Fin.append (fun i => n * c i) ![a, b] y *
        B x y =
      n ^ 2 * ∑ i, ∑ j, c i * c j * B (Fin.castAdd 2 i) (Fin.castAdd 2 j) +
      n * (∑ i, c i * (a * B (Fin.castAdd 2 i) (Fin.natAdd s 0) +
        b * B (Fin.castAdd 2 i) (Fin.natAdd s 1))) +
      n * (∑ j, c j * (a * B (Fin.natAdd s 0) (Fin.castAdd 2 j) +
        b * B (Fin.natAdd s 1) (Fin.castAdd 2 j))) +
      (a * a * B (Fin.natAdd s 0) (Fin.natAdd s 0) + a * b * B (Fin.natAdd s 0) (Fin.natAdd s 1) +
        b * a * B (Fin.natAdd s 1) (Fin.natAdd s 0) +
        b * b * B (Fin.natAdd s 1) (Fin.natAdd s 1)) := by
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Finset.sum_add_distrib, Finset.mul_sum, mul_add]
  ring_nf

/-- The sum of `c'ₓ Bₓ` over the extended coefficient vector `c' = (n c₁, …, n c_s, a, b)`. -/
private theorem sum_append_mul (s : ℕ) (n a b : ℚ) (c : Fin s → ℚ) (B : Fin (s + 2) → ℚ) :
    ∑ x, Fin.append (fun i => n * c i) ![a, b] x * B x =
      n * ∑ i, c i * B (Fin.castAdd 2 i) + (a * B (Fin.natAdd s 0) + b * B (Fin.natAdd s 1)) := by
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Finset.mul_sum]
  ring_nf

/-- A combination `∑ cᵢ xᵢ` that vanishes still vanishes after scaling every `xᵢ` by `a`. -/
private theorem sum_mul_mul_eq_zero {s : ℕ} (c x : Fin s → ℚ) (a : ℚ)
    (h : ∑ i, c i * x i = 0) : ∑ i, c i * (a * x i) = 0 := by
  simp_rw [mul_left_comm (c _), ← Finset.mul_sum, h, mul_zero]

section Forward

variable (k : Type u) [Field k] {S : Scheme.{u}} (f : S ⟶ Spec (.of k)) [IsProper f]
  (hd : topologicalKrullDim S ≤ (2 : ℕ))

/-- The linear part `∑ cᵢ aᵢ` of `∑ cᵢ (α aᵢ + β bᵢ)`. -/
private theorem sum_mul_add_mul {s : ℕ} (c a b : Fin s → ℚ) (α β : ℚ) :
    ∑ i, c i * (α * a i + β * b i) = α * ∑ i, c i * a i + β * ∑ i, c i * b i := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The orthogonality step.** Let `H` be an invertible sheaf with `(H²) > 0` such that every
rational combination `P` with `(P · H) = 0` has `(P²) ≤ 0`, and let `L = ∑ cᵢ Mᵢ` satisfy
`(L · H) = 0` and `(L²) = 0`. Then `(L · E) = 0` for every invertible sheaf `E`: with
`E' = (H²) E - (E · H) H`, the combination `nL + E'` is orthogonal to `H` for every `n`, and
`(nL + E')² = 2n (H²) (L · E) + (E')²` is non-positive for all rational `n`. -/
private theorem sum_mul_pair_eq_zero (H E : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 H]
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 E]
    (hH : 0 < pair k f hd H H)
    (hnp : ∀ {s' : ℕ} (c' : Fin s' → ℚ) (M' : Fin s' → S.Modules)
      [∀ j, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (M' j)],
      ∑ i, c' i * (pair k f hd (M' i) H : ℚ) = 0 →
        ∑ i, ∑ j, c' i * c' j * (pair k f hd (M' i) (M' j) : ℚ) ≤ 0)
    {s : ℕ} (c : Fin s → ℚ) (M : Fin s → S.Modules)
    [∀ j, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (M j)]
    (hLH : ∑ i, c i * (pair k f hd (M i) H : ℚ) = 0)
    (hQ : ∑ i, ∑ j, c i * c j * (pair k f hd (M i) (M j) : ℚ) = 0) :
    ∑ i, c i * (pair k f hd (M i) E : ℚ) = 0 := by
  haveI := isInvertible_pair E H
  have hEM : ∀ j, pair k f hd E (M j) = pair k f hd (M j) E := fun j => pair_comm k f hd _ _
  have hHM : ∀ j, pair k f hd H (M j) = pair k f hd (M j) H := fun j => pair_comm k f hd _ _
  have hHE : pair k f hd H E = pair k f hd E H := pair_comm k f hd _ _
  set h2 : ℚ := (pair k f hd H H : ℚ) with hh2
  set eh : ℚ := (pair k f hd E H : ℚ) with heh
  set X := ∑ i, c i * (pair k f hd (M i) E : ℚ) with hX
  set K : ℚ := h2 * h2 * (pair k f hd E E : ℚ) - 2 * h2 * eh * eh + eh * eh * h2 with hK
  have key : ∀ n : ℚ, 2 * n * h2 * X + K ≤ 0 := by
    intro n
    obtain ⟨M', hM'⟩ : ∃ M' : Fin (s + 2) → S.Modules, M' = Fin.append M ![E, H] := ⟨_, rfl⟩
    haveI : ∀ j, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (M' j) := by
      rw [hM']; exact isInvertible_finAppend M ![E, H]
    have hlin : ∑ x, Fin.append (fun i => n * c i) ![h2, -eh] x *
        (pair k f hd (M' x) H : ℚ) = 0 := by
      subst hM'
      rw [sum_append_mul]
      simp only [Fin.append_left, Fin.append_right, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hLH]
      ring
    have h := hnp (Fin.append (fun i => n * c i) ![h2, -eh]) M' hlin
    subst hM'
    rw [sum_sum_append_mul] at h
    simp only [Fin.append_left, Fin.append_right, Matrix.cons_val_zero, Matrix.cons_val_one,
      hEM, hHM, hHE, sum_mul_add_mul] at h
    rw [hQ, hLH] at h
    linear_combination h
  by_contra hX0
  have hpos : (0 : ℚ) < h2 := by rw [hh2]; exact_mod_cast hH
  have := key ((1 - K) / (2 * h2 * X))
  rw [show 2 * ((1 - K) / (2 * h2 * X)) * h2 * X = 1 - K by field_simp] at this
  linarith

end Forward

section Dimension

open Order

variable {k : Type u} [Field k] {S : Scheme.{u}} (f : S ⟶ Spec (.of k))

/-- The dimension of the reduced closed subscheme on `{x}⁻` is the height of `x`. -/
private theorem topologicalKrullDim_curveSubschemeAt (x : S) :
    topologicalKrullDim (curveSubschemeAt x) = (height x : WithBot ℕ∞) := by
  have h := MMP.Intersection.subvarietyDim_eq_height (MMP.Intersection.associatedSubvariety x)
  rw [MMP.Intersection.genericPoint_associatedSubvariety] at h
  exact h

/-- On an integral `k`-surface locally of finite type, `height x + coheight x = 2`. -/
private theorem height_add_coheight_eq_two [IsIntegral S] [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim S = 2) (x : S) : height x + coheight x = 2 := by
  letI : S.Over (Spec (.of k)) := ⟨f⟩
  have : LocallyOfFiniteType (S ↘ Spec (.of k)) := ‹LocallyOfFiniteType f›
  have hpure : MMP.Intersection.IsPureDimensional S 2 := by
    intro Z hZ
    rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hZ
    subst hZ
    rw [(Homeomorph.Set.univ S).isHomeomorph.topologicalKrullDim_eq, hdim]
    rfl
  exact MMP.Intersection.height_add_coheight_eq_of_isPureDimensional k hpure x

private theorem eq_one_of_add_eq_two {a b : ℕ∞} (h : a + b = 2) (hb : b = 1) : a = 1 := by
  subst hb
  exact WithTop.add_right_cancel ENat.one_ne_top (h.trans one_add_one_eq_two.symm)

/-- The generic point of a proper curve on a surface has coheight one. -/
private theorem coheight_point_eq_one [IsIntegral S] [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim S = 2) (C : ProperCurve f) : coheight C.point = 1 := by
  have h := height_add_coheight_eq_two f hdim C.point
  have h1 : height C.point = 1 := by
    have := C.dim_eq
    rw [topologicalKrullDim_curveSubschemeAt] at this
    exact_mod_cast this
  rw [add_comm] at h
  exact eq_one_of_add_eq_two h h1

/-- The generic point of a prime divisor on a proper surface is the generic point of a proper
curve. -/
private theorem isProperCurve_genericPoint [IsProper f] [IsIntegral S]
    (hdim : topologicalKrullDim S = 2) (P : MMP.Mori.PrimeDivisor S) :
    IsProperCurve f P.genericPoint := by
  refine isProperCurve_of_isProper f ?_
  rw [topologicalKrullDim_curveSubschemeAt]
  have h := height_add_coheight_eq_two f hdim P.genericPoint
  rw [eq_one_of_add_eq_two h (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P)]
  rfl

end Dimension

section Converse

variable (k : Type u) [Field k] {S : Scheme.{u}} (f : S ⟶ Spec (.of k)) [IsProper f]
  (hd : topologicalKrullDim S ≤ (2 : ℕ))

/-- **Numerically trivial combinations are orthogonal to everything.** On a smooth proper
surface, if `L = ∑ cᵢ Mᵢ` has degree zero on every proper curve, then `(L · N) = 0` for every
invertible sheaf `N`: `N ≅ 𝒪_S(D)` for a divisor `D = ∑ n_P P`, and
`(L · 𝒪_S(D)) = ∑ n_P deg_P L`. -/
private theorem sum_mul_pair_eq_zero_of_forall_degree [IsIntegral S] [IsLocallyNoetherian S]
    [IsNormal S] [CompactSpace S] (hsm : IsSmoothScheme f) (hdim : topologicalKrullDim S = 2)
    {s : ℕ} (c : Fin s → ℚ) (M : Fin s → S.Modules)
    [∀ j, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (M j)]
    (hnum : ∀ C : ProperCurve f, ∑ j, c j * (C.degree k (M j) : ℚ) = 0) (N : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N] :
    ∑ i, c i * (pair k f hd (M i) N : ℚ) = 0 := by
  have hcart := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm
  haveI hinv : ∀ D : Divisor S, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
      D.divisorialSheaf := fun D => (hcart D).isInvertibleModule_divisorialSheaf
  have hN : SheafOfModules.IsInvertible S.sheaf.obj S.ringCatSheaf.property N := ‹_›
  obtain ⟨D, ⟨e⟩⟩ := exists_divisorialSheaf_iso_of_isInvertible N
  let φ : Fin s → Divisor S →+ ℤ := fun i =>
    AddMonoidHom.mk' (fun D => pair k f hd D.divisorialSheaf (M i))
      (fun D D' => pair_divisorialSheaf_add k f hd (hcart D) (hcart D') (M i))
  have hφ : ∀ i (D : Divisor S), φ i D = D.sum fun P n => n * φ i (Finsupp.single P 1) := by
    intro i D
    conv_lhs => rw [← Finsupp.sum_single D]
    rw [map_finsuppSum]
    refine Finsupp.sum_congr fun P _ => ?_
    rw [← Finsupp.smul_single_one, map_zsmul, smul_eq_mul]
  let C : MMP.Mori.PrimeDivisor S → ProperCurve f := fun P =>
    ⟨P.genericPoint, isProperCurve_genericPoint f hdim P⟩
  have hdeg : ∀ i P, φ i (Finsupp.single P 1) = (C P).degree k (M i) := by
    intro i P
    haveI := MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsm P
    obtain ⟨eP⟩ := MMP.Threefold.Resolution.nonempty_divisorialSheaf_single_iso_invertibleSheaf' P
      inferInstance (hcart _)
    exact pair_eq_degree_of_iso_invertibleSheaf k f hd hsm P (C P) rfl _ _ eP
  have h1 : ∀ i, (pair k f hd (M i) N : ℚ) =
      ∑ P ∈ D.support, (D P : ℚ) * ((C P).degree k (M i) : ℚ) := by
    intro i
    rw [pair_comm, ← pair_congr_left k f hd (M i) e]
    have := hφ i D
    simp only [hdeg] at this
    change (φ i D : ℚ) = _
    rw [this, Finsupp.sum]
    push_cast
    rfl
  simp only [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero fun P _ => sum_mul_mul_eq_zero c _ _ (hnum (C P))

/-- The degree on a proper curve `C` is the pairing with an invertible sheaf, namely
`𝒪_S(C)`. -/
private theorem exists_isInvertible_degree_eq_pair [IsIntegral S] [IsLocallyNoetherian S]
    [IsNormal S] [CompactSpace S] (hsm : IsSmoothScheme f) (hdim : topologicalKrullDim S = 2)
    (C : ProperCurve f) :
    ∃ (N : S.Modules) (_ : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N),
      ∀ (M : S.Modules) [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 M],
        (C.degree k M : ℚ) = pair k f hd M N := by
  set P : MMP.Mori.PrimeDivisor S :=
    AlgebraicGeometry.PrimeDivisor.ofCoheightOne C.point (coheight_point_eq_one f hdim C)
  have hP : C.point = P.genericPoint :=
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _).symm
  have hcart := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm (Finsupp.single P 1)
  haveI : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
      (Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor S)) :=
    hcart.isInvertibleModule_divisorialSheaf
  haveI := MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsm P
  obtain ⟨eP⟩ := MMP.Threefold.Resolution.nonempty_divisorialSheaf_single_iso_invertibleSheaf' P
    inferInstance hcart
  refine ⟨Divisor.divisorialSheaf (Finsupp.single P 1), inferInstance, fun M _ => ?_⟩
  rw [pair_comm, pair_eq_degree_of_iso_invertibleSheaf k f hd hsm P C hP _ _ eP]

end Converse

/-- **The null case of the Hodge index inequality.** Let `S` be a smooth projective surface over
a field `k`, `H` an ample invertible sheaf on `S` and `L = ∑ⱼ cⱼ Mⱼ` a
rational combination of invertible sheaves with `(L · H) = 0`. Then `(L²) = 0` if and only if
`∑ⱼ cⱼ deg_C Mⱼ = 0` for every proper curve `C ⊆ S`. -/
public theorem sheafCombinationIntersectionNumber_two_eq_zero_iff_of_isAmple'
    (k : Type u) [Field k] {S : Scheme.{u}} (f : S ⟶ Spec (.of k))
    [IsProper f] [Smooth f] (hS : IsProjectiveVariety k f) (hdim : topologicalKrullDim S = 2)
    (H : S.Modules) [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 H]
    [Stacks.Ample.IsInvertibleModule S H] (hH : Stacks.Ample.IsAmple S H)
    {s : ℕ} (c : Fin s → ℚ) (M : Fin s → S.Modules)
    [∀ j, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (M j)] :
    haveI : ∀ j : Fin 1, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
        ((![H] : Fin 1 → S.Modules) j) := fun _ => by simpa
    haveI : ∀ j : Fin 0, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
        ((![] : Fin 0 → S.Modules) j) := fun j => j.elim0
    sheafCombinationIntersectionNumber k f (𝟙 S) ℚ c M 1 ![H] (by rw [hdim]; rfl) = 0 →
      (sheafCombinationIntersectionNumber k f (𝟙 S) ℚ c M 2 ![] (by rw [hdim]; rfl) = 0 ↔
        ∀ C : ProperCurve f, ∑ j, c j * (C.degree k (M j) : ℚ) = 0) := by
  intro hLH
  haveI : ∀ j : Fin 1, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
      ((![H] : Fin 1 → S.Modules) j) := fun _ => by simpa
  haveI : ∀ j : Fin 0, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
      ((![] : Fin 0 → S.Modules) j) := fun j => j.elim0
  have hd : topologicalKrullDim S ≤ (2 : ℕ) := by rw [hdim]; rfl
  haveI := hS
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace f
  haveI := isNormal_of_smooth f
  have hsm : IsSmoothScheme f := (isSmoothScheme_iff f).2 inferInstance
  rw [sheafCombinationIntersectionNumber_one_eq_sum k f hd] at hLH
  rw [sheafCombinationIntersectionNumber_two_eq_sum k f hd]
  have hHH : 0 < pair k f hd H H := by
    haveI := isInvertible_pair H H
    have h := AlgebraicGeometry.selfIntersectionNumber_pos k f (𝟙 S) 2 hdim H
      (Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple S H hH)
    rw [AlgebraicGeometry.selfIntersectionNumber] at h
    rw [pair_def]
    convert h using 1
    exact AlgebraicGeometry.intersectionNumber_congr_family k f (𝟙 S) 2 hd
      (funext fun j => by fin_cases j <;> rfl)
  have hnp : ∀ {s' : ℕ} (c' : Fin s' → ℚ) (M' : Fin s' → S.Modules)
      [∀ j, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (M' j)],
      ∑ i, c' i * (pair k f hd (M' i) H : ℚ) = 0 →
        ∑ i, ∑ j, c' i * c' j * (pair k f hd (M' i) (M' j) : ℚ) ≤ 0 := by
    intro s' c' M' _ h
    have := sheafCombinationIntersectionNumber_two_nonpos_of_isAmple' k f hS hdim H hH c' M'
    rw [sheafCombinationIntersectionNumber_one_eq_sum k f hd,
      sheafCombinationIntersectionNumber_two_eq_sum k f hd] at this
    exact this h
  constructor
  · intro hQ C
    obtain ⟨N, _, hdeg⟩ := exists_isInvertible_degree_eq_pair k f hd hsm hdim C
    simp only [hdeg]
    exact sum_mul_pair_eq_zero k f hd H _ hHH hnp c M hLH hQ
  · intro hnum
    rw [Finset.sum_comm]
    simp_rw [mul_assoc]
    exact Finset.sum_eq_zero fun j _ => sum_mul_mul_eq_zero c _ _
      (sum_mul_pair_eq_zero_of_forall_degree k f hd hsm hdim c M hnum (M j))

/-- **The null case of the Hodge index inequality.** Let `S` be a smooth projective surface over
an algebraically closed field `k`, `H` an ample invertible sheaf on `S` and `L = ∑ⱼ cⱼ Mⱼ` a
rational combination of invertible sheaves with `(L · H) = 0`. Then `(L²) = 0` if and only if
`∑ⱼ cⱼ deg_C Mⱼ = 0` for every proper curve `C ⊆ S`.
The proof does not use that `k` is algebraically closed: see
`sheafCombinationIntersectionNumber_two_eq_zero_iff_of_isAmple'`. -/
@[mmp "lem_mmp_conductor_surface_index_null_numerical"]
public theorem sheafCombinationIntersectionNumber_two_eq_zero_iff_of_isAmple
    (k : Type u) [Field k] [IsAlgClosed k] {S : Scheme.{u}} (f : S ⟶ Spec (.of k))
    [IsProper f] [Smooth f] (hS : IsProjectiveVariety k f) (hdim : topologicalKrullDim S = 2)
    (H : S.Modules) [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 H]
    [Stacks.Ample.IsInvertibleModule S H] (hH : Stacks.Ample.IsAmple S H)
    {s : ℕ} (c : Fin s → ℚ) (M : Fin s → S.Modules)
    [∀ j, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (M j)] :
    haveI : ∀ j : Fin 1, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
        ((![H] : Fin 1 → S.Modules) j) := fun _ => by simpa
    haveI : ∀ j : Fin 0, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
        ((![] : Fin 0 → S.Modules) j) := fun j => j.elim0
    sheafCombinationIntersectionNumber k f (𝟙 S) ℚ c M 1 ![H] (by rw [hdim]; rfl) = 0 →
      (sheafCombinationIntersectionNumber k f (𝟙 S) ℚ c M 2 ![] (by rw [hdim]; rfl) = 0 ↔
        ∀ C : ProperCurve f, ∑ j, c j * (C.degree k (M j) : ℚ) = 0) :=
  sheafCombinationIntersectionNumber_two_eq_zero_iff_of_isAmple' k f hS hdim H hH c M

/-! ### Divisors of positive square -/

/-- **A binary quadratic form.** Let `h > 0` and `p > 0`. If
`h (x² p + y² q) ≤ (x α + y β)²` for all rational `x, y`, then `q ≤ 0`, and `q = 0` forces
`β = 0`: `(x, y) = (1, 0)` gives `α² ≥ h p > 0`, and `(x, y) = (β, -α)` gives
`p β² + q α² ≤ 0`. -/
private theorem nonpos_and_eq_zero_of_mul_le_sq {h α β p q : ℚ} (hh : 0 < h) (hp : 0 < p)
    (hf : ∀ x y : ℚ, h * (x ^ 2 * p + y ^ 2 * q) ≤ (x * α + y * β) ^ 2) :
    q ≤ 0 ∧ (q = 0 → β = 0) := by
  have hα : h * p ≤ α ^ 2 := by simpa using hf 1 0
  have hβα : p * β ^ 2 + q * α ^ 2 ≤ 0 :=
    nonpos_of_mul_nonpos_right (by nlinarith [hf β (-α)]) hh
  have hα0 : 0 < α ^ 2 := (mul_pos hh hp).trans_le hα
  refine ⟨nonpos_of_mul_nonpos_left (by nlinarith [sq_nonneg β]) hα0, fun hq => ?_⟩
  subst hq
  exact (pow_eq_zero_iff two_ne_zero).mp (by nlinarith [sq_nonneg β])

section Combination

variable (k : Type u) [Field k] {S : Scheme.{u}} (f : S ⟶ Spec (.of k)) [IsProper f]
  (hd : topologicalKrullDim S ≤ (2 : ℕ))

/-- The pairing `(∑ᵢ cᵢ Lᵢ · ∑ⱼ dⱼ L'ⱼ)` of two rational combinations of invertible sheaves, each
sheaf bundled with its invertibility. -/
private noncomputable def combPair {s t : ℕ} (c : Fin s → ℚ)
    (L : Fin s → {N : S.Modules // SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N})
    (d : Fin t → ℚ)
    (L' : Fin t → {N : S.Modules // SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N}) :
    ℚ :=
  ∑ i, ∑ j, c i * d j * (@pair k _ S f _ hd (L i).1 (L' j).1 (L i).2 (L' j).2 : ℚ)

variable {s t s' : ℕ} (c : Fin s → ℚ)
  (L : Fin s → {N : S.Modules // SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N})
  (d : Fin t → ℚ)
  (L' : Fin t → {N : S.Modules // SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N})
  (c' : Fin s' → ℚ)
  (L'' : Fin s' → {N : S.Modules // SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N})

private theorem combPair_comm : combPair k f hd c L d L' = combPair k f hd d L' c L := by
  unfold combPair
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [@pair_comm k _ S f _ hd (L i).1 (L' j).1 (L i).2 (L' j).2]
  ring

private theorem combPair_append_left :
    combPair k f hd (Fin.append c c') (Fin.append L L'') d L' =
      combPair k f hd c L d L' + combPair k f hd c' L'' d L' := by
  simp only [combPair, Fin.sum_univ_add, Fin.append_left, Fin.append_right]

private theorem combPair_append_right :
    combPair k f hd d L' (Fin.append c c') (Fin.append L L'') =
      combPair k f hd d L' c L + combPair k f hd d L' c' L'' := by
  simp only [combPair, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
    Finset.sum_add_distrib]

private theorem combPair_smul_left (x : ℚ) :
    combPair k f hd (x • c) L d L' = x * combPair k f hd c L d L' := by
  simp only [combPair, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private theorem combPair_smul_right (x : ℚ) :
    combPair k f hd d L' (x • c) L = x * combPair k f hd d L' c L := by
  rw [combPair_comm, combPair_smul_left, combPair_comm]

/-- **The index inequality against `H`.** Let `H` be a combination with `(H²) > 0` such that
every combination orthogonal to `H` has non-positive square. Then `(H²) (P²) ≤ (P · H)²` for
every combination `P`: apply the hypothesis to `(H²) P - (P · H) H`. -/
private theorem mul_combPair_self_le_sq
    (H : Fin 1 → {N : S.Modules // SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N})
    (hH : 0 < combPair k f hd ![1] H ![1] H)
    (hnp : ∀ {s' : ℕ} (c' : Fin s' → ℚ)
      (L' : Fin s' → {N : S.Modules // SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N}),
      combPair k f hd c' L' ![1] H = 0 → combPair k f hd c' L' c' L' ≤ 0) :
    combPair k f hd ![1] H ![1] H * combPair k f hd c L c L ≤ combPair k f hd c L ![1] H ^ 2 := by
  have hHc : combPair k f hd ![1] H c L = combPair k f hd c L ![1] H := combPair_comm ..
  have := hnp (Fin.append (combPair k f hd ![1] H ![1] H • c)
    ((-combPair k f hd c L ![1] H) • ![1])) (Fin.append L H) (by
      rw [combPair_append_left, combPair_smul_left, combPair_smul_left]; ring)
  simp only [combPair_append_left, combPair_append_right, combPair_smul_left,
    combPair_smul_right, hHc] at this
  nlinarith

end Combination

/-- **Hodge index theorem for a divisor of positive square.** Let `S` be a smooth projective
surface over a field `k`, and `A = ∑ᵢ aᵢ Mᵢ`, `B = ∑ⱼ bⱼ Nⱼ` rational
combinations of invertible sheaves. If `(A²) > 0` and `(A · B) = ∑ⱼ bⱼ (A · Nⱼ) = 0`, then
`(B²) ≤ 0`, and `(B²) = 0` if and only if `∑ⱼ bⱼ deg_C Nⱼ = 0` for every proper curve `C ⊆ S`. -/
public theorem sheafCombinationIntersectionNumber_two_nonpos_of_pos'
    (k : Type u) [Field k] {S : Scheme.{u}} (f : S ⟶ Spec (.of k))
    [IsProper f] [Smooth f] (hS : IsProjectiveVariety k f) (hdim : topologicalKrullDim S = 2)
    {s : ℕ} (a : Fin s → ℚ) (M : Fin s → S.Modules)
    [∀ i, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (M i)]
    {t : ℕ} (b : Fin t → ℚ) (N : Fin t → S.Modules)
    [hN : ∀ j, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (N j)] :
    haveI : ∀ j : Fin 0, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
        ((![] : Fin 0 → S.Modules) j) := fun j => j.elim0
    haveI : ∀ (j : Fin t) (l : Fin 1), SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
        ((![N j] : Fin 1 → S.Modules) l) := fun j _ => by simpa using hN j
    0 < sheafCombinationIntersectionNumber k f (𝟙 S) ℚ a M 2 ![] (by rw [hdim]; rfl) →
      ∑ j, b j * sheafCombinationIntersectionNumber k f (𝟙 S) ℚ a M 1 ![N j]
        (by rw [hdim]; rfl) = 0 →
      sheafCombinationIntersectionNumber k f (𝟙 S) ℚ b N 2 ![] (by rw [hdim]; rfl) ≤ 0 ∧
        (sheafCombinationIntersectionNumber k f (𝟙 S) ℚ b N 2 ![] (by rw [hdim]; rfl) = 0 ↔
          ∀ C : ProperCurve f, ∑ j, b j * (C.degree k (N j) : ℚ) = 0) := by
  haveI : ∀ j : Fin 0, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
      ((![] : Fin 0 → S.Modules) j) := fun j => j.elim0
  haveI : ∀ (j : Fin t) (l : Fin 1), SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
      ((![N j] : Fin 1 → S.Modules) l) := fun j _ => by simpa using hN j
  intro hA hAB
  have hd : topologicalKrullDim S ≤ (2 : ℕ) := by rw [hdim]; rfl
  haveI := hS
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace f
  haveI := isNormal_of_smooth f
  have hsm : IsSmoothScheme f := (isSmoothScheme_iff f).2 inferInstance
  -- an ample invertible sheaf `H` on `S`
  obtain ⟨M₀, hM₀, hM₀a⟩ := Stacks.HProjective.exists_isAmple_of_isAffine (Spec (.of k))
  obtain ⟨H, hH, hHa⟩ := AlgebraicGeometry.exists_isAmple_of_isProjectiveMorphism f M₀ hM₀a
    hS.isProjective
  haveI : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 H := inferInstance
  -- invertible sheaves bundled with their invertibility
  let Mb : Fin s → {N : S.Modules // SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N} :=
    fun i => ⟨M i, inferInstance⟩
  let Nb : Fin t → {N : S.Modules // SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N} :=
    fun j => ⟨N j, hN j⟩
  let Hb : Fin 1 → {N : S.Modules // SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N} :=
    ![⟨H, inferInstance⟩]
  have hpairH : ∀ {s' : ℕ} (c' : Fin s' → ℚ)
      (L : Fin s' → {N : S.Modules // SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N}),
      combPair k f hd c' L ![1] Hb =
        ∑ i, c' i * (@pair k _ S f _ hd (L i).1 H (L i).2 inferInstance : ℚ) := by
    intro s' c' L
    simp [combPair, Hb]
  have hh : 0 < combPair k f hd ![1] Hb ![1] Hb := by
    have h0 := MMP.Threefold.Mori.sheafSelfIntersectionNumber_pos_of_isAmple k f H hHa S (𝟙 S)
      2 hdim
    unfold sheafSelfIntersectionNumber at h0
    rw [sheafIntersectionNumber_two_eq_pair k f hd] at h0
    rw [hpairH]
    simpa [Hb] using h0
  have hab : combPair k f hd a Mb b Nb = 0 := by
    simp only [sheafCombinationIntersectionNumber_one_eq_sum k f hd] at hAB
    rw [← hAB, combPair, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  -- the elementary index inequality: `(P · H) = 0` implies `(P²) ≤ 0`
  have hnp : ∀ {s' : ℕ} (c' : Fin s' → ℚ)
      (L : Fin s' → {N : S.Modules // SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N}),
      combPair k f hd c' L ![1] Hb = 0 → combPair k f hd c' L c' L ≤ 0 := by
    intro s' c' L h0
    haveI : ∀ i, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (L i).1 := fun i => (L i).2
    have := sheafCombinationIntersectionNumber_two_nonpos_of_isAmple' k f hS hdim H hHa c'
      (fun i => (L i).1)
    rw [sheafCombinationIntersectionNumber_one_eq_sum k f hd,
      sheafCombinationIntersectionNumber_two_eq_sum k f hd] at this
    exact this (by rw [← hpairH]; exact h0)
  -- `(H²) (xA + yB)² ≤ ((xA + yB) · H)²`, with `(A · B) = 0`
  obtain ⟨hq, hq0⟩ := nonpos_and_eq_zero_of_mul_le_sq (α := combPair k f hd a Mb ![1] Hb)
    (β := combPair k f hd b Nb ![1] Hb) (p := combPair k f hd a Mb a Mb)
    (q := combPair k f hd b Nb b Nb) hh
    (by rwa [sheafCombinationIntersectionNumber_two_eq_sum k f hd] at hA) fun x y => by
      have := mul_combPair_self_le_sq k f hd (Fin.append (x • a) (y • b)) (Fin.append Mb Nb) Hb
        hh hnp
      simp only [combPair_append_left, combPair_append_right, combPair_smul_left,
        combPair_smul_right, combPair_comm k f hd b Nb a Mb, hab] at this
      linear_combination this
  rw [sheafCombinationIntersectionNumber_two_eq_sum k f hd b N]
  refine ⟨hq, fun h0 => ?_, fun hnum => ?_⟩
  · -- `(B²) = 0` forces `(B · H) = 0`, and the null case applies
    refine (sheafCombinationIntersectionNumber_two_eq_zero_iff_of_isAmple' k f hS hdim H hHa b N
      ?_).mp ?_
    · rw [sheafCombinationIntersectionNumber_one_eq_sum k f hd]
      exact (hpairH b Nb).symm.trans (hq0 h0)
    · rw [sheafCombinationIntersectionNumber_two_eq_sum k f hd]
      exact h0
  · -- a numerically trivial combination is orthogonal to every invertible sheaf
    rw [Finset.sum_comm]
    simp_rw [mul_assoc]
    exact Finset.sum_eq_zero fun j _ => sum_mul_mul_eq_zero b _ _
      (sum_mul_pair_eq_zero_of_forall_degree k f hd hsm hdim b N hnum (N j))

/-- **Hodge index theorem for a divisor of positive square.** Let `S` be a smooth projective
surface over an algebraically closed field `k`, and `A = ∑ᵢ aᵢ Mᵢ`, `B = ∑ⱼ bⱼ Nⱼ` rational
combinations of invertible sheaves. If `(A²) > 0` and `(A · B) = ∑ⱼ bⱼ (A · Nⱼ) = 0`, then
`(B²) ≤ 0`, and `(B²) = 0` if and only if `∑ⱼ bⱼ deg_C Nⱼ = 0` for every proper curve `C ⊆ S`.
The proof does not use that `k` is algebraically closed: see
`sheafCombinationIntersectionNumber_two_nonpos_of_pos'`. -/
@[mmp "lem_mmp_foundation_surface_positive_square_hodge_index"]
public theorem sheafCombinationIntersectionNumber_two_nonpos_of_pos
    (k : Type u) [Field k] [IsAlgClosed k] {S : Scheme.{u}} (f : S ⟶ Spec (.of k))
    [IsProper f] [Smooth f] (hS : IsProjectiveVariety k f) (hdim : topologicalKrullDim S = 2)
    {s : ℕ} (a : Fin s → ℚ) (M : Fin s → S.Modules)
    [∀ i, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (M i)]
    {t : ℕ} (b : Fin t → ℚ) (N : Fin t → S.Modules)
    [hN : ∀ j, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (N j)] :
    haveI : ∀ j : Fin 0, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
        ((![] : Fin 0 → S.Modules) j) := fun j => j.elim0
    haveI : ∀ (j : Fin t) (l : Fin 1), SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
        ((![N j] : Fin 1 → S.Modules) l) := fun j _ => by simpa using hN j
    0 < sheafCombinationIntersectionNumber k f (𝟙 S) ℚ a M 2 ![] (by rw [hdim]; rfl) →
      ∑ j, b j * sheafCombinationIntersectionNumber k f (𝟙 S) ℚ a M 1 ![N j]
        (by rw [hdim]; rfl) = 0 →
      sheafCombinationIntersectionNumber k f (𝟙 S) ℚ b N 2 ![] (by rw [hdim]; rfl) ≤ 0 ∧
        (sheafCombinationIntersectionNumber k f (𝟙 S) ℚ b N 2 ![] (by rw [hdim]; rfl) = 0 ↔
          ∀ C : ProperCurve f, ∑ j, b j * (C.degree k (N j) : ℚ) = 0) :=
  sheafCombinationIntersectionNumber_two_nonpos_of_pos' k f hS hdim a M b N

end MMP.Mori
