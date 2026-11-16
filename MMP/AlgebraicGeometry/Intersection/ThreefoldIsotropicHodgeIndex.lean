module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Threefold.Basic
public import MMP.AlgebraicTopology.ComplexVectorBundle.FirstChernClass
import MMP.AlgebraicGeometry.Intersection.ThreefoldHodgeIndex
import MMP.AlgebraicGeometry.Intersection.OneCycles
import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafTensor
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Intersection.Surface.RiemannRochHodgeIndex
import MMP.AlgebraicGeometry.Intersection.EulerPolynomialGenericRank

/-!
# The isotropic index theorem on a smooth projective threefold

For an ample invertible sheaf `A` and rational combinations `H`, `L` of invertible sheaves on a
smooth projective complex threefold with `(H · A²) > 0`, `(H² · A) = 0` and `(L · H · A) = 0`,
we show `(L² · A) ≤ 0`, characterise the equality case, and show that in the equality case the
first Chern class of `L - cH` vanishes. The proof goes through the pairing
`(N₁, N₂) ↦ (N₁ · N₂ · A)`.
-/

open CategoryTheory AlgebraicGeometry

namespace MMP.Fold06.LemMmpThreefoldIsotropicDivisorIndex

open MMP.Mori MMP.Analytic

/-! ### The intersection pairing against `A` on a threefold -/

section Pairing

variable {V : Scheme.{0}} (f : V ⟶ Spec (.of ℂ)) [IsProper f]
  (hd : topologicalKrullDim V ≤ (3 : ℕ)) (A : V.Modules)
  [hA : SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 A]

/-- The triple `![N₁, N₂, A]` of invertible sheaves is a family of invertible sheaves. -/
private theorem isInvertible_triple (N₁ N₂ : V.Modules)
    [h₁ : SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 N₁]
    [h₂ : SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 N₂] :
    ∀ j : Fin 3, SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 (![N₁, N₂, A] j) := by
  intro j
  fin_cases j
  exacts [h₁, h₂, hA]

/-- The intersection pairing `(N₁ · N₂ · A)` of two invertible sheaves against `A`. -/
private noncomputable def pair (N₁ N₂ : V.Modules)
    [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 N₁]
    [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 N₂] : ℤ :=
  haveI := isInvertible_triple A N₁ N₂
  AlgebraicGeometry.intersectionNumber ℂ f (𝟙 V) 3 hd ![N₁, N₂, A]

private theorem pair_def (N₁ N₂ : V.Modules)
    [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 N₁]
    [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 N₂] :
    haveI := isInvertible_triple A N₁ N₂
    pair f hd A N₁ N₂ = AlgebraicGeometry.intersectionNumber ℂ f (𝟙 V) 3 hd ![N₁, N₂, A] :=
  rfl

/-- The pairing only depends on the two sheaves, not on how they are written. -/
private theorem pair_congr {N₁ N₁' N₂ N₂' : V.Modules}
    {_ : SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 N₁}
    [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 N₁']
    {_ : SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 N₂}
    [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 N₂']
    (h₁ : N₁ = N₁') (h₂ : N₂ = N₂') : pair f hd A N₁ N₂ = pair f hd A N₁' N₂' := by
  subst h₁ h₂
  rfl

/-- The pairing is symmetric. -/
private theorem pair_comm (N₁ N₂ : V.Modules)
    [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 N₁]
    [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 N₂] :
    pair f hd A N₁ N₂ = pair f hd A N₂ N₁ := by
  haveI := isInvertible_triple A N₁ N₂
  haveI := isInvertible_triple A N₂ N₁
  rw [pair_def, pair_def,
    ← AlgebraicGeometry.intersectionNumber_comp_perm ℂ f (𝟙 V) 3 hd ![N₂, N₁, A]
      (Equiv.swap 0 1)]
  exact AlgebraicGeometry.intersectionNumber_congr_family ℂ f (𝟙 V) 3 hd
    (funext fun j => by fin_cases j <;> rfl)

/-- The pairing depends only on the isomorphism class of the first sheaf. -/
private theorem pair_congr_left {N₁ N₁' : V.Modules} (N₂ : V.Modules)
    [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 N₁]
    [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 N₁']
    [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 N₂] (e : N₁ ≅ N₁') :
    pair f hd A N₁ N₂ = pair f hd A N₁' N₂ := by
  haveI := isInvertible_triple A N₁ N₂
  haveI := isInvertible_triple A N₁' N₂
  rw [pair_def, pair_def]
  exact AlgebraicGeometry.intersectionNumber_eq_of_iso_at ℂ f (𝟙 V) 3 hd _ _ 0
    (fun q hq => by fin_cases q <;> first | exact absurd rfl hq | rfl) e

/-- The pairing of a divisor sum: `(𝒪(D + D') · N · A) = (𝒪(D) · N · A) + (𝒪(D') · N · A)`. -/
private theorem pair_divisorialSheaf_add [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V]
    {D D' : Divisor V} (hD : D.IsCartier) (hD' : D'.IsCartier) (N : V.Modules)
    [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 N] :
    haveI : SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 D.divisorialSheaf :=
      hD.isInvertibleModule_divisorialSheaf
    haveI : SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 D'.divisorialSheaf :=
      hD'.isInvertibleModule_divisorialSheaf
    haveI : SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 (D + D').divisorialSheaf :=
      (hD.add hD').isInvertibleModule_divisorialSheaf
    pair f hd A (D + D').divisorialSheaf N =
      pair f hd A D.divisorialSheaf N + pair f hd A D'.divisorialSheaf N := by
  haveI : SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 D.divisorialSheaf :=
    hD.isInvertibleModule_divisorialSheaf
  haveI : SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 D'.divisorialSheaf :=
    hD'.isInvertibleModule_divisorialSheaf
  haveI : SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 (D + D').divisorialSheaf :=
    (hD.add hD').isInvertibleModule_divisorialSheaf
  haveI := isInvertible_triple A (D + D').divisorialSheaf N
  haveI := isInvertible_triple A D.divisorialSheaf N
  haveI := isInvertible_triple A D'.divisorialSheaf N
  rw [pair_def, pair_def, pair_def]
  exact AlgebraicGeometry.intersectionNumber_tensor ℂ f (𝟙 V) 3 hd 0 _ _ _
    (fun q hq => by fin_cases q <;> first | exact absurd rfl hq | rfl)
    (fun q hq => by fin_cases q <;> first | exact absurd rfl hq | rfl)
    (hD.divisorialSheafTensorIso hD').symm

/-- An intersection number of three sheaves on `V`, the last of which is `A`, is their
pairing. -/
private theorem sheafIntersectionNumber_three_eq_pair (L : Fin 3 → V.Modules)
    [hL : ∀ j, SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 (L j)]
    (hd' : topologicalKrullDim V ≤ (3 : ℕ)) (h2 : L 2 = A) :
    sheafIntersectionNumber ℂ f (𝟙 V) 3 hd' L = pair f hd A (L 0) (L 1) := by
  haveI := isInvertible_triple A (L 0) (L 1)
  rw [Snapper.sheafIntersectionNumber_eq_intersectionNumber, pair_def]
  exact AlgebraicGeometry.intersectionNumber_congr_family ℂ f (𝟙 V) 3 hd
    (funext fun j => by fin_cases j <;> first | rfl | exact h2)

/-- The intersection number `(M² · A)` of a rational combination `M = ∑ cᵢ Mᵢ`, as a double
sum of pairings. -/
private theorem sheafCombinationIntersectionNumber_two_eq_sum {s : ℕ} (c : Fin s → ℚ)
    (M : Fin s → V.Modules) [∀ j, SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 (M j)]
    (hd' : topologicalKrullDim V ≤ ((2 + 1 : ℕ) : WithBot ℕ∞)) :
    haveI : ∀ j : Fin 1, SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2
        ((![A] : Fin 1 → V.Modules) j) := fun _ => by simpa
    sheafCombinationIntersectionNumber ℂ f (𝟙 V) ℚ c M 2 ![A] hd' =
      ∑ i, ∑ j, c i * c j * (pair f hd A (M i) (M j) : ℚ) := by
  haveI : ∀ j : Fin 1, SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2
      ((![A] : Fin 1 → V.Modules) j) := fun _ => by simpa
  rw [sheafCombinationIntersectionNumber, ← Fintype.sum_prod_type',
    ← (finTwoArrowEquiv (Fin s)).symm.sum_comp]
  refine Fintype.sum_congr _ _ fun p => ?_
  rw [Fin.prod_univ_two]
  congr 1
  exact_mod_cast sheafIntersectionNumber_three_eq_pair f hd A _ hd'
    (hL := isInvertible_finAppend (a := 2) (b := 1) _ _) rfl

/-- The intersection number `(M · N · A)` of a rational combination `M = ∑ cᵢ Mᵢ`, as a sum
of pairings. -/
private theorem sheafCombinationIntersectionNumber_one_eq_sum {s : ℕ} (c : Fin s → ℚ)
    (M : Fin s → V.Modules) [∀ j, SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 (M j)]
    (N : V.Modules) [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 N]
    (hd' : topologicalKrullDim V ≤ ((1 + 2 : ℕ) : WithBot ℕ∞)) :
    haveI : ∀ j : Fin 2, SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2
        ((![N, A] : Fin 2 → V.Modules) j) := fun j => by fin_cases j <;> simpa
    sheafCombinationIntersectionNumber ℂ f (𝟙 V) ℚ c M 1 ![N, A] hd' =
      ∑ i, c i * (pair f hd A (M i) N : ℚ) := by
  haveI : ∀ j : Fin 2, SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2
      ((![N, A] : Fin 2 → V.Modules) j) := fun j => by fin_cases j <;> simpa
  rw [sheafCombinationIntersectionNumber, ← (Equiv.funUnique (Fin 1) (Fin s)).symm.sum_comp]
  refine Fintype.sum_congr _ _ fun i => ?_
  rw [Fin.prod_univ_one]
  congr 1
  exact_mod_cast sheafIntersectionNumber_three_eq_pair f hd A _ hd'
    (hL := isInvertible_finAppend (a := 1) (b := 2) _ _) rfl

end Pairing

/-! ### Numerically trivial combinations on a smooth projective threefold -/

section Congr

variable {V : Scheme.{0}} [V.Over (Spec (.of ℂ))]

/-- The rational first Chern class `c₁(N) ∈ H²(V^an; ℚ)` of an invertible sheaf. -/
private noncomputable abbrev ratChern (N : V.Modules)
    [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 N] :
    singularCohomology ℚ (Analytification.space (V ↘ Spec (.of ℂ))) 2 :=
  singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass N)

private theorem ratChern_congr {N N' : V.Modules}
    {_ : SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 N}
    [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 N'] (h : N = N') :
    ratChern N = ratChern N' := by
  subst h
  rfl

private theorem degree_congr (C : ProperCurve (V ↘ Spec (.of ℂ))) {N N' : V.Modules}
    {_ : SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 N}
    [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 N'] (h : N = N') :
    C.degree ℂ N = C.degree ℂ N' := by
  subst h
  rfl

end Congr

section Divisors

variable {V : Scheme.{0}} [V.Over (Spec (.of ℂ))] [IsProper (V ↘ Spec (.of ℂ))]
  [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V]
  (hcart : ∀ D : Divisor V, D.IsCartier)
  (hd : topologicalKrullDim V ≤ (3 : ℕ)) (A : V.Modules)
  [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 A]

/-- `D ↦ deg_C 𝒪_V(D)`, an additive map on divisors. -/
private noncomputable def degreeHom (C : ProperCurve (V ↘ Spec (.of ℂ))) : Divisor V →+ ℤ :=
  AddMonoidHom.mk' (fun D => haveI := (hcart D).isInvertibleModule_divisorialSheaf
      C.degree ℂ D.divisorialSheaf) fun D D' =>
    Divisor.degreeOn_add ℂ _ C.ι C.dim_le D D' (hcart D) (hcart D')

/-- `D ↦ (𝒪_V(D) · N · A)`, an additive map on divisors. -/
private noncomputable def pairHom (N : V.Modules)
    [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 N] : Divisor V →+ ℤ :=
  AddMonoidHom.mk' (fun D => haveI := (hcart D).isInvertibleModule_divisorialSheaf
      pair (V ↘ Spec (.of ℂ)) hd A D.divisorialSheaf N) fun D D' =>
    pair_divisorialSheaf_add _ hd A (hcart D) (hcart D') N

omit [V.Over (Spec (.of ℂ))] [IsProper (V ↘ Spec (.of ℂ))] [CompactSpace V]
  [IsLocallyNoetherian V] [IsNormal V] in
/-- A finite family of rationals has a common positive denominator. -/
private theorem exists_pos_nat_mul_eq_intCast {n : ℕ} (x : Fin n → ℚ) :
    ∃ b : ℕ, 0 < b ∧ ∃ m : Fin n → ℤ, ∀ i, (b : ℚ) * x i = m i := by
  refine ⟨∏ i, (x i).den, Finset.prod_pos fun i _ => (x i).den_pos,
    fun i => ((∏ j, (x j).den) / (x i).den : ℕ) * (x i).num, fun i => ?_⟩
  obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem (fun j => (x j).den) (Finset.mem_univ i)
  dsimp only
  rw [hq, Nat.mul_div_cancel_left _ (x i).den_pos]
  push_cast
  rw [← Rat.mul_den_eq_num]
  ring

omit [V.Over (Spec (.of ℂ))] [IsProper (V ↘ Spec (.of ℂ))] [CompactSpace V]
  [IsLocallyNoetherian V] [IsNormal V] in
/-- An additive map sends `∑ mᵢ δᵢ` to `b ∑ xᵢ φ(δᵢ)` when `b xᵢ = mᵢ`. -/
private theorem map_sum_zsmul_eq_mul {M : Type*} [AddCommGroup M]
    (φ : M →+ ℚ) {n : ℕ} (δ : Fin n → M) {v : Fin n → ℚ}
    (hφ : ∀ i, φ (δ i) = v i) {b : ℕ} {x : Fin n → ℚ} {m : Fin n → ℤ}
    (hm : ∀ i, (b : ℚ) * x i = m i) :
    φ (∑ i, m i • δ i) = (b : ℚ) * ∑ i, x i * v i := by
  simp only [map_sum, map_zsmul, hφ, Finset.mul_sum, ← mul_assoc, hm, zsmul_eq_mul]

private theorem degreeHom_eq (C : ProperCurve (V ↘ Spec (.of ℂ))) {D : Divisor V}
    {N : V.Modules} [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 N]
    (e : D.divisorialSheaf ≅ N) :
    degreeHom hcart C D = C.degree ℂ N :=
  haveI := (hcart D).isInvertibleModule_divisorialSheaf
  degreeOn_eq_of_iso ℂ _ C.ι C.dim_le e

private theorem pairHom_eq (N' : V.Modules)
    [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 N'] {D : Divisor V} {N : V.Modules}
    [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 N] (e : D.divisorialSheaf ≅ N) :
    pairHom hcart hd A N' D = pair (V ↘ Spec (.of ℂ)) hd A N N' :=
  haveI := (hcart D).isInvertibleModule_divisorialSheaf
  pair_congr_left _ hd A N' e

include hcart in
/-- **A numerically trivial combination is orthogonal to every invertible sheaf.** If
`∑ xᵢ deg_C Fᵢ = 0` for every proper curve `C`, then `∑ xᵢ (Fᵢ · N · A) = 0` for every `N`:
clearing denominators, a positive multiple of `∑ xᵢ Fᵢ` is a single numerically trivial
divisor `E`, and `(𝒪_V(E) · N · A) = 0`. -/
private theorem sum_mul_pair_eq_zero_of_forall_degree [IsIntegral V]
    {n : ℕ} (x : Fin n → ℚ) (F : Fin n → V.Modules)
    [∀ i, SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 (F i)]
    (hx : ∀ C : ProperCurve (V ↘ Spec (.of ℂ)), ∑ i, x i * (C.degree ℂ (F i) : ℚ) = 0)
    (N : V.Modules) [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 N] :
    ∑ i, x i * (pair (V ↘ Spec (.of ℂ)) hd A (F i) N : ℚ) = 0 := by
  choose δ e using fun i => @exists_divisorialSheaf_iso_of_isInvertible _ _ _ _ _ (F i)
    (inferInstance : SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 (F i))
  obtain ⟨b, hb, m, hm⟩ := exists_pos_nat_mul_eq_intCast x
  set E := ∑ i, m i • δ i
  haveI := (hcart E).isInvertibleModule_divisorialSheaf
  have hE : ∀ C : ProperCurve (V ↘ Spec (.of ℂ)), C.degree ℂ E.divisorialSheaf = 0 := by
    intro C
    have := map_sum_zsmul_eq_mul ((Int.castAddHom ℚ).comp (degreeHom hcart C)) δ
      (fun i => congrArg Int.cast (degreeHom_eq hcart C (e i).some)) hm
    simp only [hx C, mul_zero, AddMonoidHom.comp_apply, Int.coe_castAddHom,
      Int.cast_eq_zero] at this
    exact this
  have hpair := map_sum_zsmul_eq_mul ((Int.castAddHom ℚ).comp (pairHom hcart hd A N)) δ
    (fun i => congrArg Int.cast (pairHom_eq hcart hd A N (e i).some)) hm
  simp only [AddMonoidHom.comp_apply, Int.coe_castAddHom] at hpair
  haveI := isInvertible_triple A E.divisorialSheaf N
  have h0 : pairHom hcart hd A N E = 0 :=
    (sheafIntersectionNumber_three_eq_pair _ hd A ![E.divisorialSheaf, N, A] hd rfl).symm.trans
      (sheafIntersectionNumber_eq_zero_of_degree_eq_zero ℂ _ (𝟙 V) 2 hd _ hE)
  rw [h0, Int.cast_zero] at hpair
  simpa [hb.ne'] using hpair.symm

end Divisors

/-! ### The combination `L - dH` on the appended family `(L, H)` -/

section Append

variable {V : Scheme.{0}} [V.Over (Spec (.of ℂ))] [IsProper (V ↘ Spec (.of ℂ))]
  (hd : topologicalKrullDim V ≤ (3 : ℕ)) (A : V.Modules)
  [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 A] {t s : ℕ} {L : Fin t → V.Modules}
  {H : Fin s → V.Modules} [∀ i, SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 (L i)]
  [∀ j, SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 (H j)]
  {F : Fin (t + s) → V.Modules} [∀ i, SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 (F i)]
  (hFL : ∀ i, F (Fin.castAdd s i) = L i) (hFH : ∀ j, F (Fin.natAdd t j) = H j)
  (l : Fin t → ℚ) (h : Fin s → ℚ) (d : ℚ)

include hFL hFH in
/-- `((L - dH) · N · A) = (L · N · A) - d (H · N · A)` for `L = ∑ lᵢ Lᵢ`, `H = ∑ hⱼ Hⱼ`. -/
private theorem sum_finAppend_mul_pair (N : V.Modules)
    [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 N] :
    ∑ i, Fin.append l (fun j => -d * h j) i * (pair (V ↘ Spec (.of ℂ)) hd A (F i) N : ℚ) =
      ∑ i, l i * (pair (V ↘ Spec (.of ℂ)) hd A (L i) N : ℚ) -
        d * ∑ j, h j * (pair (V ↘ Spec (.of ℂ)) hd A (H j) N : ℚ) := by
  have e1 : ∀ i, pair (V ↘ Spec (.of ℂ)) hd A (F (Fin.castAdd s i)) N =
      pair (V ↘ Spec (.of ℂ)) hd A (L i) N := fun i => pair_congr _ hd A (hFL i) rfl
  have e2 : ∀ j, pair (V ↘ Spec (.of ℂ)) hd A (F (Fin.natAdd t j)) N =
      pair (V ↘ Spec (.of ℂ)) hd A (H j) N := fun j => pair_congr _ hd A (hFH j) rfl
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, e1, e2, Finset.mul_sum,
    sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

include hFL hFH in
/-- `deg_C (L - dH) = deg_C L - d deg_C H`. -/
private theorem sum_finAppend_mul_degree (C : ProperCurve (V ↘ Spec (.of ℂ))) :
    ∑ i, Fin.append l (fun j => -d * h j) i * (C.degree ℂ (F i) : ℚ) =
      ∑ i, l i * (C.degree ℂ (L i) : ℚ) - d * ∑ j, h j * (C.degree ℂ (H j) : ℚ) := by
  have e1 : ∀ i, C.degree ℂ (F (Fin.castAdd s i)) = C.degree ℂ (L i) :=
    fun i => degree_congr C (hFL i)
  have e2 : ∀ j, C.degree ℂ (F (Fin.natAdd t j)) = C.degree ℂ (H j) :=
    fun j => degree_congr C (hFH j)
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, e1, e2, Finset.mul_sum,
    sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

include hFL hFH in
/-- `c₁(L - dH) = c₁(L) - d c₁(H)`. -/
private theorem sum_finAppend_smul_ratChern :
    ∑ i, Fin.append l (fun j => -d * h j) i • ratChern (F i) =
      ∑ i, l i • ratChern (L i) - d • ∑ j, h j • ratChern (H j) := by
  have e1 : ∀ i, ratChern (F (Fin.castAdd s i)) = ratChern (L i) :=
    fun i => ratChern_congr (hFL i)
  have e2 : ∀ j, ratChern (F (Fin.natAdd t j)) = ratChern (H j) :=
    fun j => ratChern_congr (hFH j)
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, e1, e2, Finset.smul_sum,
    sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [smul_smul, ← neg_smul, neg_mul]

include hFL hFH in
/-- `((L - dH)² · A) = (L² · A) - 2d (L · H · A) + d² (H² · A)`, written with the pairing. -/
private theorem sum_sum_finAppend_mul_pair :
    ∑ i, ∑ j, Fin.append l (fun j => -d * h j) i * Fin.append l (fun j => -d * h j) j *
        (pair (V ↘ Spec (.of ℂ)) hd A (F i) (F j) : ℚ) =
      ∑ i, ∑ j, l i * l j * (pair (V ↘ Spec (.of ℂ)) hd A (L i) (L j) : ℚ) -
        2 * d * ∑ j, h j * ∑ i, l i * (pair (V ↘ Spec (.of ℂ)) hd A (L i) (H j) : ℚ) +
        d ^ 2 * ∑ i, ∑ j, h i * h j * (pair (V ↘ Spec (.of ℂ)) hd A (H i) (H j) : ℚ) := by
  have e1 : ∀ i j, pair (V ↘ Spec (.of ℂ)) hd A (F (Fin.castAdd s i)) (F (Fin.castAdd s j)) =
      pair (V ↘ Spec (.of ℂ)) hd A (L i) (L j) := fun i j => pair_congr _ hd A (hFL i) (hFL j)
  have e2 : ∀ i j, pair (V ↘ Spec (.of ℂ)) hd A (F (Fin.castAdd s i)) (F (Fin.natAdd t j)) =
      pair (V ↘ Spec (.of ℂ)) hd A (L i) (H j) := fun i j => pair_congr _ hd A (hFL i) (hFH j)
  have e3 : ∀ i j, pair (V ↘ Spec (.of ℂ)) hd A (F (Fin.natAdd t i)) (F (Fin.castAdd s j)) =
      pair (V ↘ Spec (.of ℂ)) hd A (H i) (L j) := fun i j => pair_congr _ hd A (hFH i) (hFL j)
  have e4 : ∀ i j, pair (V ↘ Spec (.of ℂ)) hd A (F (Fin.natAdd t i)) (F (Fin.natAdd t j)) =
      pair (V ↘ Spec (.of ℂ)) hd A (H i) (H j) := fun i j => pair_congr _ hd A (hFH i) (hFH j)
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, e1, e2, e3, e4,
    Finset.sum_add_distrib]
  have h2 : ∑ i, ∑ j, l i * (-d * h j) * (pair (V ↘ Spec (.of ℂ)) hd A (L i) (H j) : ℚ) =
      -d * ∑ j, h j * ∑ i, l i * (pair (V ↘ Spec (.of ℂ)) hd A (L i) (H j) : ℚ) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h3 : ∑ i, ∑ j, -d * h i * l j * (pair (V ↘ Spec (.of ℂ)) hd A (H i) (L j) : ℚ) =
      -d * ∑ j, h j * ∑ i, l i * (pair (V ↘ Spec (.of ℂ)) hd A (L i) (H j) : ℚ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pair_comm]
    ring
  have h4 : ∑ i, ∑ j, -d * h i * (-d * h j) * (pair (V ↘ Spec (.of ℂ)) hd A (H i) (H j) : ℚ) =
      d ^ 2 * ∑ i, ∑ j, h i * h j * (pair (V ↘ Spec (.of ℂ)) hd A (H i) (H j) : ℚ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h2, h3, h4]
  ring

end Append

/-- **The index theorem perpendicular to an isotropic class on a threefold**, written with the
pairing `(N₁, N₂) ↦ (N₁ · N₂ · A)`. The proof applies the Hodge index inequality on a threefold
to `M = L - cH`, for which `(M · A²) = 0` and `(M² · A) = (L² · A)`. -/
private theorem isotropic_index_pair {V : Scheme.{0}} [V.Over (Spec (.of ℂ))]
    [IsProper (V ↘ Spec (.of ℂ))] [Smooth (V ↘ Spec (.of ℂ))]
    (hV : MMP.Mori.IsProjectiveVariety ℂ (V ↘ Spec (.of ℂ))) (hdim : topologicalKrullDim V = 3)
    (hd : topologicalKrullDim V ≤ (3 : ℕ))
    (A : V.Modules) [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 A]
    [Stacks.Ample.IsInvertibleModule V A] (hA : Stacks.Ample.IsAmple V A)
    {s : ℕ} (h : Fin s → ℚ) (H : Fin s → V.Modules)
    [∀ j, SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 (H j)]
    {t : ℕ} (l : Fin t → ℚ) (L : Fin t → V.Modules)
    [∀ j, SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 (L j)]
    (hHA : 0 < ∑ j, h j * (pair (V ↘ Spec (.of ℂ)) hd A (H j) A : ℚ))
    (hHH : ∑ i, ∑ j, h i * h j * (pair (V ↘ Spec (.of ℂ)) hd A (H i) (H j) : ℚ) = 0)
    (hLH : ∑ j, h j * ∑ i, l i * (pair (V ↘ Spec (.of ℂ)) hd A (L i) (H j) : ℚ) = 0) :
    ∑ i, ∑ j, l i * l j * (pair (V ↘ Spec (.of ℂ)) hd A (L i) (L j) : ℚ) ≤ 0 ∧
      (∑ i, ∑ j, l i * l j * (pair (V ↘ Spec (.of ℂ)) hd A (L i) (L j) : ℚ) = 0 ↔
        ∃ d : ℚ, ∀ C : ProperCurve (V ↘ Spec (.of ℂ)),
          ∑ j, l j * (C.degree ℂ (L j) : ℚ) = d * ∑ j, h j * (C.degree ℂ (H j) : ℚ)) ∧
      (∑ i, ∑ j, l i * l j * (pair (V ↘ Spec (.of ℂ)) hd A (L i) (L j) : ℚ) = 0 →
        ∑ j, l j • ratChern (L j) -
          ((∑ i, l i * (pair (V ↘ Spec (.of ℂ)) hd A (L i) A : ℚ)) /
            ∑ j, h j * (pair (V ↘ Spec (.of ℂ)) hd A (H j) A : ℚ)) •
          ∑ j, h j • ratChern (H j) = 0) := by
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ (V ↘ Spec (.of ℂ)) := hV
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian (V ↘ Spec (.of ℂ))
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace (V ↘ Spec (.of ℂ))
  haveI : IsNormal V := isNormal_of_smooth_over_field (V ↘ Spec (.of ℂ))
  haveI : IsIntegral V := ((MMP.Mori.isProjectiveVariety_iff _ _).1 hV).1.toIsIntegral
  have hcart := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme
    ((isSmoothScheme_iff (V ↘ Spec (.of ℂ))).2 inferInstance)
  -- the combination `L - dH`, on the family `F = (L, H)`
  obtain ⟨F, hF⟩ : ∃ F : Fin (t + s) → V.Modules, F = Fin.append L H := ⟨_, rfl⟩
  haveI : ∀ i, SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 (F i) :=
    hF ▸ isInvertible_finAppend L H
  have hFL : ∀ i, F (Fin.castAdd s i) = L i := fun i => by rw [hF, Fin.append_left]
  have hFH : ∀ j, F (Fin.natAdd t j) = H j := fun j => by rw [hF, Fin.append_right]
  -- the index inequality on a threefold, applied to `L - dH`
  have hidx := fun d : ℚ => by
    simpa only [sheafCombinationIntersectionNumber_one_eq_sum _ hd,
      sheafCombinationIntersectionNumber_two_eq_sum _ hd] using
      sheafCombinationIntersectionNumber_two_nonpos_of_isAmple_of_dim_eq_three hV hdim A hA
        (Fin.append l (fun j => -d * h j)) F
  -- `((L - dH)² · A) = (L² · A)`, by the two vanishing cross terms
  have hQ : ∀ d : ℚ,
      ∑ i, ∑ j, Fin.append l (fun j => -d * h j) i * Fin.append l (fun j => -d * h j) j *
          (pair (V ↘ Spec (.of ℂ)) hd A (F i) (F j) : ℚ) =
        ∑ i, ∑ j, l i * l j * (pair (V ↘ Spec (.of ℂ)) hd A (L i) (L j) : ℚ) := fun d => by
    rw [sum_sum_finAppend_mul_pair hd A hFL hFH, hLH, hHH]
    ring
  -- `((L - cH) · A²) = 0` for `c = (L · A²) / (H · A²)`
  set c := (∑ i, l i * (pair (V ↘ Spec (.of ℂ)) hd A (L i) A : ℚ)) /
    ∑ j, h j * (pair (V ↘ Spec (.of ℂ)) hd A (H j) A : ℚ) with hc
  have hMA : ∑ i, Fin.append l (fun j => -c * h j) i *
      (pair (V ↘ Spec (.of ℂ)) hd A (F i) A : ℚ) = 0 := by
    rw [sum_finAppend_mul_pair hd A hFL hFH, hc, div_mul_cancel₀ _ hHA.ne', sub_self]
  have hnum := fun h0 => ((hidx c hMA).2 ((hQ c).trans h0))
  refine ⟨(hQ c).symm.trans_le (hidx c hMA).1, ⟨fun h0 => ⟨c, fun C => ?_⟩, ?_⟩, fun h0 => ?_⟩
  · linarith [(sum_finAppend_mul_degree hFL hFH l h c C).symm.trans ((hnum h0).1 C)]
  · rintro ⟨d, hdC⟩
    have hnumd : ∀ C : ProperCurve (V ↘ Spec (.of ℂ)),
        ∑ i, Fin.append l (fun j => -d * h j) i * (C.degree ℂ (F i) : ℚ) = 0 := fun C => by
      rw [sum_finAppend_mul_degree hFL hFH, hdC C, sub_self]
    rw [← hQ d, Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← mul_zero (Fin.append l (fun j => -d * h j) j),
      ← sum_mul_pair_eq_zero_of_forall_degree hcart hd A _ F hnumd (F j), Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  · rw [← sum_finAppend_smul_ratChern hFL hFH]
    exact (hnum h0).2

end MMP.Fold06.LemMmpThreefoldIsotropicDivisorIndex

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

open MMP.Analytic MMP.Fold06.LemMmpThreefoldIsotropicDivisorIndex

/-- **The intersection form perpendicular to an isotropic class on a threefold.** Let `V` be a
smooth projective complex threefold, `A` an ample invertible sheaf, and `H = ∑ⱼ hⱼ Hⱼ`,
`L = ∑ⱼ lⱼ Lⱼ` rational combinations of invertible sheaves with `(H · A²) > 0`, `(H² · A) = 0`
and `(L · H · A) = 0`. Then `(L² · A) ≤ 0`; `(L² · A) = 0` if and only if there is `d : ℚ` with
`deg_C L = d · deg_C H` for every proper curve `C ⊆ V`; and in that case, with
`c = (L · A²) / (H · A²)`, the class `∑ⱼ lⱼ c₁(Lⱼ) - c ∑ⱼ hⱼ c₁(Hⱼ)` vanishes in `H²(V^an, ℚ)`. -/
@[mmp "lem_mmp_threefold_isotropic_divisor_index"]
public theorem sheafCombinationIntersectionNumber_two_mul_nonpos_of_isotropic
    {V : Scheme.{0}} [V.Over (Spec (.of ℂ))] [IsProper (V ↘ Spec (.of ℂ))]
    [Smooth (V ↘ Spec (.of ℂ))] (hV : IsProjectiveVariety ℂ (V ↘ Spec (.of ℂ)))
    (hdim : topologicalKrullDim V = 3)
    (A : V.Modules) [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 A]
    [Stacks.Ample.IsInvertibleModule V A] (hA : Stacks.Ample.IsAmple V A)
    {s : ℕ} (h : Fin s → ℚ) (H : Fin s → V.Modules)
    [hH : ∀ j, SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 (H j)]
    {t : ℕ} (l : Fin t → ℚ) (L : Fin t → V.Modules)
    [∀ j, SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 (L j)] :
    haveI : ∀ j : Fin 1, SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2
        ((![A] : Fin 1 → V.Modules) j) := fun _ => by simpa
    haveI : ∀ j : Fin 2, SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2
        ((![A, A] : Fin 2 → V.Modules) j) := fun j => by fin_cases j <;> simpa
    haveI : ∀ (j : Fin s) (m : Fin 2), SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2
        ((![H j, A] : Fin 2 → V.Modules) m) := fun j m => by
      fin_cases m
      · simpa using hH j
      · simpa
    0 < sheafCombinationIntersectionNumber ℂ (V ↘ Spec (.of ℂ)) (𝟙 V) ℚ h H 1 ![A, A]
        (by rw [hdim]; rfl) →
    sheafCombinationIntersectionNumber ℂ (V ↘ Spec (.of ℂ)) (𝟙 V) ℚ h H 2 ![A]
        (by rw [hdim]; rfl) = 0 →
    ∑ j, h j * sheafCombinationIntersectionNumber ℂ (V ↘ Spec (.of ℂ)) (𝟙 V) ℚ l L 1 ![H j, A]
        (by rw [hdim]; rfl) = 0 →
    sheafCombinationIntersectionNumber ℂ (V ↘ Spec (.of ℂ)) (𝟙 V) ℚ l L 2 ![A]
        (by rw [hdim]; rfl) ≤ 0 ∧
      (sheafCombinationIntersectionNumber ℂ (V ↘ Spec (.of ℂ)) (𝟙 V) ℚ l L 2 ![A]
          (by rw [hdim]; rfl) = 0 ↔
        ∃ d : ℚ, ∀ C : ProperCurve (V ↘ Spec (.of ℂ)),
          ∑ j, l j * (C.degree ℂ (L j) : ℚ) = d * ∑ j, h j * (C.degree ℂ (H j) : ℚ)) ∧
      (sheafCombinationIntersectionNumber ℂ (V ↘ Spec (.of ℂ)) (𝟙 V) ℚ l L 2 ![A]
          (by rw [hdim]; rfl) = 0 →
        ∑ j, l j • singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
            (algebraicFirstChernClass (L j)) -
          (sheafCombinationIntersectionNumber ℂ (V ↘ Spec (.of ℂ)) (𝟙 V) ℚ l L 1 ![A, A]
              (by rw [hdim]; rfl) /
            sheafCombinationIntersectionNumber ℂ (V ↘ Spec (.of ℂ)) (𝟙 V) ℚ h H 1 ![A, A]
              (by rw [hdim]; rfl)) •
          ∑ j, h j • singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
            (algebraicFirstChernClass (H j)) = 0) := by
  haveI : ∀ j : Fin 1, SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2
      ((![A] : Fin 1 → V.Modules) j) := fun _ => by simpa
  haveI : ∀ j : Fin 2, SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2
      ((![A, A] : Fin 2 → V.Modules) j) := fun j => by fin_cases j <;> simpa
  intro hHA hHH hLH
  have hd : topologicalKrullDim V ≤ (3 : ℕ) := by rw [hdim]; rfl
  simp only [sheafCombinationIntersectionNumber_one_eq_sum _ hd,
    sheafCombinationIntersectionNumber_two_eq_sum _ hd] at hHA hHH hLH ⊢
  exact isotropic_index_pair hV hdim hd A hA h H l L hHA hHH hLH

end MMP.Mori
