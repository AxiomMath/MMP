module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Threefold.Basic
public import MMP.AlgebraicTopology.ComplexVectorBundle.FirstChernClass
import MMP.AlgebraicGeometry.Intersection.OneCycles
import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafTensor
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Intersection.Surface.RiemannRochHodgeIndex
import MMP.AlgebraicGeometry.Intersection.EulerPolynomialGenericRank
import MMP.AlgebraicGeometry.Analytic.NumericallyTrivialChernClass

/-!
# The intersection form perpendicular to an isotropic class

On a smooth projective complex surface `S` with an ample invertible sheaf `A`, let `H` be a
rational combination of invertible sheaves with `(H · A) > 0` and `(H²) = 0`. Every combination
`L` with `(L · H) = 0` has `(L²) ≤ 0`, with equality exactly when `L` is numerically a rational
multiple of `H`, and then `c₁(L - cH) = 0` in `H²(S^an; ℚ)`.

## Main results

* `MMP.Mori.sheafCombinationIntersectionNumber_two_nonpos_of_isotropic`
-/

open CategoryTheory AlgebraicGeometry

namespace MMP.Fold06.LemMmpSurfaceIsotropicDivisorIndex

open MMP.Mori MMP.Analytic

/-! ### The intersection pairing on a surface -/

section Pairing

variable {S : Scheme.{0}} (f : S ⟶ Spec (.of ℂ)) [IsProper f]
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
  AlgebraicGeometry.intersectionNumber ℂ f (𝟙 S) 2 hd ![N₁, N₂]

private theorem pair_def (N₁ N₂ : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₁]
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₂] :
    haveI := isInvertible_pair N₁ N₂
    pair f hd N₁ N₂ = AlgebraicGeometry.intersectionNumber ℂ f (𝟙 S) 2 hd ![N₁, N₂] := rfl

/-- The pairing only depends on the two sheaves, not on how they are written. -/
private theorem pair_congr {N₁ N₁' N₂ N₂' : S.Modules}
    {_ : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₁}
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₁']
    {_ : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₂}
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₂']
    (h₁ : N₁ = N₁') (h₂ : N₂ = N₂') : pair f hd N₁ N₂ = pair f hd N₁' N₂' := by
  subst h₁ h₂
  rfl

/-- The pairing is symmetric. -/
private theorem pair_comm (N₁ N₂ : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₁]
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₂] :
    pair f hd N₁ N₂ = pair f hd N₂ N₁ := by
  have := isInvertible_pair N₁ N₂
  have := isInvertible_pair N₂ N₁
  rw [pair_def, pair_def,
    ← AlgebraicGeometry.intersectionNumber_comp_perm ℂ f (𝟙 S) 2 hd ![N₂, N₁] (Equiv.swap 0 1)]
  exact AlgebraicGeometry.intersectionNumber_congr_family ℂ f (𝟙 S) 2 hd
    (funext fun j => by fin_cases j <;> rfl)

/-- The pairing depends only on the isomorphism class of the first sheaf. -/
private theorem pair_congr_left {N₁ N₁' : S.Modules} (N₂ : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₁]
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₁']
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₂] (e : N₁ ≅ N₁') :
    pair f hd N₁ N₂ = pair f hd N₁' N₂ := by
  have := isInvertible_pair N₁ N₂
  have := isInvertible_pair N₁' N₂
  rw [pair_def, pair_def]
  exact AlgebraicGeometry.intersectionNumber_eq_of_iso_at ℂ f (𝟙 S) 2 hd _ _ 0
    (fun q hq => by fin_cases q <;> first | exact absurd rfl hq | rfl) e

/-- The pairing of a divisor sum: `(𝒪(D + D') · N) = (𝒪(D) · N) + (𝒪(D') · N)`. -/
private theorem pair_divisorialSheaf_add [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
    {D D' : Divisor S} (hD : D.IsCartier) (hD' : D'.IsCartier) (N : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N] :
    haveI : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 D.divisorialSheaf :=
      hD.isInvertibleModule_divisorialSheaf
    haveI : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 D'.divisorialSheaf :=
      hD'.isInvertibleModule_divisorialSheaf
    haveI : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (D + D').divisorialSheaf :=
      (hD.add hD').isInvertibleModule_divisorialSheaf
    pair f hd (D + D').divisorialSheaf N =
      pair f hd D.divisorialSheaf N + pair f hd D'.divisorialSheaf N := by
  have : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 D.divisorialSheaf :=
    hD.isInvertibleModule_divisorialSheaf
  have : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 D'.divisorialSheaf :=
    hD'.isInvertibleModule_divisorialSheaf
  have : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (D + D').divisorialSheaf :=
    (hD.add hD').isInvertibleModule_divisorialSheaf
  have := isInvertible_pair (D + D').divisorialSheaf N
  have := isInvertible_pair D.divisorialSheaf N
  have := isInvertible_pair D'.divisorialSheaf N
  rw [pair_def, pair_def, pair_def]
  exact AlgebraicGeometry.intersectionNumber_tensor ℂ f (𝟙 S) 2 hd 0 _ _ _
    (fun q hq => by fin_cases q <;> first | exact absurd rfl hq | rfl)
    (fun q hq => by fin_cases q <;> first | exact absurd rfl hq | rfl)
    (hD.divisorialSheafTensorIso hD').symm

/-- An intersection number of two sheaves on `S` is their pairing. -/
private theorem sheafIntersectionNumber_two_eq_pair (L : Fin 2 → S.Modules)
    [hL : ∀ j, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (L j)]
    (hd' : topologicalKrullDim S ≤ (2 : ℕ)) :
    sheafIntersectionNumber ℂ f (𝟙 S) 2 hd' L = pair f hd (L 0) (L 1) := by
  have := isInvertible_pair (L 0) (L 1)
  rw [Snapper.sheafIntersectionNumber_eq_intersectionNumber, pair_def]
  exact AlgebraicGeometry.intersectionNumber_congr_family ℂ f (𝟙 S) 2 hd
    (funext fun j => by fin_cases j <;> rfl)

/-- The self-intersection `(M²)` of a rational combination `M = ∑ cᵢ Mᵢ`, as a double sum of
pairings. -/
private theorem sheafCombinationIntersectionNumber_two_eq_sum {s : ℕ} (c : Fin s → ℚ)
    (M : Fin s → S.Modules) [∀ j, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (M j)]
    (hd' : topologicalKrullDim S ≤ ((2 + 0 : ℕ) : WithBot ℕ∞)) :
    haveI : ∀ j : Fin 0, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
        ((![] : Fin 0 → S.Modules) j) := fun j => j.elim0
    sheafCombinationIntersectionNumber ℂ f (𝟙 S) ℚ c M 2 ![] hd' =
      ∑ i, ∑ j, c i * c j * (pair f hd (M i) (M j) : ℚ) := by
  have : ∀ j : Fin 0, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
      ((![] : Fin 0 → S.Modules) j) := fun j => j.elim0
  rw [sheafCombinationIntersectionNumber, ← Fintype.sum_prod_type',
    ← (finTwoArrowEquiv (Fin s)).symm.sum_comp]
  refine Fintype.sum_congr _ _ fun p => ?_
  rw [Fin.prod_univ_two]
  congr 1
  exact_mod_cast sheafIntersectionNumber_two_eq_pair f hd _ hd'
    (hL := isInvertible_finAppend (a := 2) (b := 0) _ _)

/-- The intersection number `(M · N)` of a rational combination `M = ∑ cᵢ Mᵢ` with `N`, as a sum
of pairings. -/
private theorem sheafCombinationIntersectionNumber_one_eq_sum {s : ℕ} (c : Fin s → ℚ)
    (M : Fin s → S.Modules) [∀ j, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (M j)]
    (N : S.Modules) [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N]
    (hd' : topologicalKrullDim S ≤ ((1 + 1 : ℕ) : WithBot ℕ∞)) :
    haveI : ∀ j : Fin 1, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
        ((![N] : Fin 1 → S.Modules) j) := fun _ => by simpa
    sheafCombinationIntersectionNumber ℂ f (𝟙 S) ℚ c M 1 ![N] hd' =
      ∑ i, c i * (pair f hd (M i) N : ℚ) := by
  have : ∀ j : Fin 1, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
      ((![N] : Fin 1 → S.Modules) j) := fun _ => by simpa
  rw [sheafCombinationIntersectionNumber, ← (Equiv.funUnique (Fin 1) (Fin s)).symm.sum_comp]
  refine Fintype.sum_congr _ _ fun i => ?_
  rw [Fin.prod_univ_one]
  congr 1
  exact_mod_cast sheafIntersectionNumber_two_eq_pair f hd _ hd'
    (hL := isInvertible_finAppend (a := 1) (b := 1) _ _)

end Pairing

/-! ### Divisors on a smooth projective surface -/

section Congr

variable {S : Scheme.{0}} [S.Over (Spec (.of ℂ))]

/-- The rational first Chern class `c₁(N) ∈ H²(S^an; ℚ)` of an invertible sheaf. -/
private noncomputable abbrev ratChern (N : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N] :
    singularCohomology ℚ (Analytification.space (S ↘ Spec (.of ℂ))) 2 :=
  singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass N)

private theorem ratChern_congr {N N' : S.Modules}
    {_ : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N}
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N'] (h : N = N') :
    ratChern N = ratChern N' := by
  subst h
  rfl

private theorem degree_congr (C : ProperCurve (S ↘ Spec (.of ℂ))) {N N' : S.Modules}
    {_ : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N}
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N'] (h : N = N') :
    C.degree ℂ N = C.degree ℂ N' := by
  subst h
  rfl

end Congr

section Divisors

variable {S : Scheme.{0}} [S.Over (Spec (.of ℂ))] [IsProper (S ↘ Spec (.of ℂ))]
  [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
  (hcart : ∀ D : Divisor S, D.IsCartier)

/-- `D ↦ deg_C 𝒪_S(D)`, an additive map on divisors. -/
private noncomputable def degreeHom (C : ProperCurve (S ↘ Spec (.of ℂ))) : Divisor S →+ ℤ :=
  AddMonoidHom.mk' (fun D => haveI := (hcart D).isInvertibleModule_divisorialSheaf
      C.degree ℂ D.divisorialSheaf) fun D D' =>
    Divisor.degreeOn_add ℂ _ C.ι C.dim_le D D' (hcart D) (hcart D')

/-- `D ↦ (𝒪_S(D) · N)`, an additive map on divisors. -/
private noncomputable def pairHom (hd : topologicalKrullDim S ≤ (2 : ℕ)) (N : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N] : Divisor S →+ ℤ :=
  AddMonoidHom.mk' (fun D => haveI := (hcart D).isInvertibleModule_divisorialSheaf
      pair (S ↘ Spec (.of ℂ)) hd D.divisorialSheaf N) fun D D' =>
    pair_divisorialSheaf_add _ hd (hcart D) (hcart D') N

/-- `D ↦ c₁(𝒪_S(D))` in `H²(S^an; ℚ)`, an additive map on divisors. -/
private noncomputable def chernHom :
    Divisor S →+ singularCohomology ℚ (Analytification.space (S ↘ Spec (.of ℂ))) 2 :=
  AddMonoidHom.mk' (fun D => haveI := (hcart D).isInvertibleModule_divisorialSheaf
      ratChern D.divisorialSheaf) fun D D' => by
    have := (hcart D).isInvertibleModule_divisorialSheaf
    have := (hcart D').isInvertibleModule_divisorialSheaf
    have := (hcart (D + D')).isInvertibleModule_divisorialSheaf
    have : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.presheaf, S.IsSheaf⟩).obj
          D.divisorialSheaf).obj D'.divisorialSheaf) :=
      (hcart D).isInvertibleModule_tensorSheaf (hcart D')
    simp only [ratChern]
    rw [← algebraicFirstChernClass_eq_of_iso ((hcart D).divisorialSheafTensorIso (hcart D')),
      algebraicFirstChernClass_sheafTensor, map_add]

/-- A finite family of rationals has a common positive denominator. -/
private theorem exists_pos_nat_mul_eq_intCast {n : ℕ} (x : Fin n → ℚ) :
    ∃ b : ℕ, 0 < b ∧ ∃ m : Fin n → ℤ, ∀ i, (b : ℚ) * x i = m i := by
  refine ⟨∏ i, (x i).den, Finset.prod_pos fun i _ => (x i).den_pos, ?_⟩
  have hdvd : ∀ i, (x i).den ∣ ∏ j, (x j).den := fun i =>
    Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  refine ⟨fun i => ((∏ j, (x j).den) / (x i).den : ℕ) * (x i).num, fun i => ?_⟩
  have hx : x i * (x i).den = (x i).num := Rat.mul_den_eq_num (x i)
  obtain ⟨q, hq⟩ := hdvd i
  have hden : (x i).den ≠ 0 := (x i).den_nz
  rw [hq]
  beta_reduce
  rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hden)]
  push_cast
  rw [← hx]
  ring

omit [IsProper (S ↘ Spec (.of ℂ))] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S] in
/-- An additive map sends `∑ mᵢ δᵢ` to `b ∑ xᵢ φ(δᵢ)` when `b xᵢ = mᵢ`. -/
private theorem map_sum_zsmul_eq_smul {M G : Type*} [AddCommGroup M] [AddCommGroup G]
    [Module ℚ G] (φ : M →+ G) {n : ℕ} (δ : Fin n → M) {v : Fin n → G}
    (hφ : ∀ i, φ (δ i) = v i) {b : ℕ} {x : Fin n → ℚ} {m : Fin n → ℤ}
    (hm : ∀ i, (b : ℚ) * x i = m i) :
    φ (∑ i, m i • δ i) = (b : ℚ) • ∑ i, x i • v i := by
  simp only [map_sum, map_zsmul, hφ, Finset.smul_sum, smul_smul, hm, Int.cast_smul_eq_zsmul]

private theorem degreeHom_eq (C : ProperCurve (S ↘ Spec (.of ℂ))) {D : Divisor S} {N : S.Modules}
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N] (e : D.divisorialSheaf ≅ N) :
    degreeHom hcart C D = C.degree ℂ N :=
  have := (hcart D).isInvertibleModule_divisorialSheaf
  degreeOn_eq_of_iso ℂ _ C.ι C.dim_le e

private theorem pairHom_eq (hd : topologicalKrullDim S ≤ (2 : ℕ)) (N' : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N'] {D : Divisor S} {N : S.Modules}
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N] (e : D.divisorialSheaf ≅ N) :
    pairHom hcart hd N' D = pair (S ↘ Spec (.of ℂ)) hd N N' :=
  have := (hcart D).isInvertibleModule_divisorialSheaf
  pair_congr_left _ hd N' e

omit [IsProper (S ↘ Spec (.of ℂ))] in
private theorem chernHom_eq {D : Divisor S} {N : S.Modules}
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N] (e : D.divisorialSheaf ≅ N) :
    chernHom hcart D = ratChern N := by
  have := (hcart D).isInvertibleModule_divisorialSheaf
  change ratChern D.divisorialSheaf = _
  rw [ratChern, algebraicFirstChernClass_eq_of_iso e]

/-- **Clearing denominators.** A numerically trivial rational combination `∑ xᵢ Fᵢ` of
invertible sheaves has a positive multiple `b ∑ xᵢ Fᵢ` which is the class of a single
numerically trivial divisor `E`: pairings and rational first Chern classes of `𝒪_S(E)` are `b`
times those of the combination. -/
private theorem exists_divisor_of_forall_degree [IsIntegral S]
    (hd : topologicalKrullDim S ≤ (2 : ℕ)) {n : ℕ} (x : Fin n → ℚ) (F : Fin n → S.Modules)
    [∀ i, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (F i)]
    (hx : ∀ C : ProperCurve (S ↘ Spec (.of ℂ)), ∑ i, x i * (C.degree ℂ (F i) : ℚ) = 0) :
    ∃ (b : ℕ) (E : Divisor S), 0 < b ∧
      haveI := (hcart E).isInvertibleModule_divisorialSheaf
      (∀ C : ProperCurve (S ↘ Spec (.of ℂ)), C.degree ℂ E.divisorialSheaf = 0) ∧
      (∀ (N : S.Modules) [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N],
        (pair (S ↘ Spec (.of ℂ)) hd E.divisorialSheaf N : ℚ) =
          b * ∑ i, x i * (pair (S ↘ Spec (.of ℂ)) hd (F i) N : ℚ)) ∧
      ratChern E.divisorialSheaf = (b : ℚ) • ∑ i, x i • ratChern (F i) := by
  choose δ e using fun i => @exists_divisorialSheaf_iso_of_isInvertible _ _ _ _ _ (F i)
    (inferInstance : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (F i))
  obtain ⟨b, hb, m, hm⟩ := exists_pos_nat_mul_eq_intCast x
  refine ⟨b, ∑ i, m i • δ i, hb, fun C => ?_, fun N _ => ?_, ?_⟩
  · have := map_sum_zsmul_eq_smul ((Int.castAddHom ℚ).comp (degreeHom hcart C)) δ
      (fun i => congrArg Int.cast (degreeHom_eq hcart C (e i).some)) hm
    simp only [smul_eq_mul, hx C, mul_zero, AddMonoidHom.comp_apply, Int.coe_castAddHom,
      Int.cast_eq_zero] at this
    exact this
  · have := map_sum_zsmul_eq_smul ((Int.castAddHom ℚ).comp (pairHom hcart hd N)) δ
      (fun i => congrArg Int.cast (pairHom_eq hcart hd N (e i).some)) hm
    simp only [smul_eq_mul, AddMonoidHom.comp_apply, Int.coe_castAddHom] at this
    exact this
  · exact map_sum_zsmul_eq_smul (chernHom hcart) δ (fun i => chernHom_eq hcart (e i).some) hm

include hcart in
/-- **A numerically trivial combination is orthogonal to every invertible sheaf.** If
`∑ xᵢ deg_C Fᵢ = 0` for every proper curve `C`, then `∑ xᵢ (Fᵢ · N) = 0` for every `N`. -/
private theorem sum_mul_pair_eq_zero_of_forall_degree [IsIntegral S]
    (hd : topologicalKrullDim S ≤ (2 : ℕ)) {n : ℕ} (x : Fin n → ℚ) (F : Fin n → S.Modules)
    [∀ i, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (F i)]
    (hx : ∀ C : ProperCurve (S ↘ Spec (.of ℂ)), ∑ i, x i * (C.degree ℂ (F i) : ℚ) = 0)
    (N : S.Modules) [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N] :
    ∑ i, x i * (pair (S ↘ Spec (.of ℂ)) hd (F i) N : ℚ) = 0 := by
  obtain ⟨b, E, hb, hE, hpair, -⟩ := exists_divisor_of_forall_degree hcart hd x F hx
  have := (hcart E).isInvertibleModule_divisorialSheaf
  have := isInvertible_pair E.divisorialSheaf N
  have h0 : pair (S ↘ Spec (.of ℂ)) hd E.divisorialSheaf N = 0 :=
    (sheafIntersectionNumber_two_eq_pair _ hd ![E.divisorialSheaf, N] hd).symm.trans
      (sheafIntersectionNumber_eq_zero_of_degree_eq_zero ℂ _ (𝟙 S) 1 hd _ hE)
  simpa [h0, hb.ne'] using (hpair N).symm

include hcart in
/-- **A numerically trivial combination has rationally trivial first Chern class.** If
`∑ xᵢ deg_C Fᵢ = 0` for every proper curve `C`, then `∑ xᵢ c₁(Fᵢ) = 0` in `H²(S^an; ℚ)`. -/
private theorem sum_smul_ratChern_eq_zero_of_forall_degree [IsIntegral S]
    [Smooth (S ↘ Spec (.of ℂ))] (hS : MMP.Mori.IsProjectiveVariety ℂ (S ↘ Spec (.of ℂ)))
    (hdim : topologicalKrullDim S = 2) {n : ℕ} (x : Fin n → ℚ) (F : Fin n → S.Modules)
    [∀ i, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (F i)]
    (hx : ∀ C : ProperCurve (S ↘ Spec (.of ℂ)), ∑ i, x i * (C.degree ℂ (F i) : ℚ) = 0) :
    ∑ i, x i • ratChern (F i) = 0 := by
  have : AlgebraicGeometry.IsProjectiveVariety ℂ (S ↘ Spec (.of ℂ)) := hS
  obtain ⟨b, E, hb, hE, -, hch⟩ :=
    exists_divisor_of_forall_degree hcart (by rw [hdim]; rfl) x F hx
  have := (hcart E).isInvertibleModule_divisorialSheaf
  have h0 := mapCoeff_algebraicFirstChernClass_eq_zero_of_degreeOn_eq_zero hdim
    E.divisorialSheaf fun C i _ _ _ hC => by
      have h2 := sheafIntersectionNumber_eq_zero_of_degree_eq_zero ℂ _ i 0 (by simpa using hC)
        (fun _ => E.divisorialSheaf) hE
      rw [Snapper.sheafIntersectionNumber_eq_intersectionNumber] at h2
      rw [degreeOn_eq_invertibleCurveDegree,
        ← AlgebraicGeometry.intersectionNumber_one_eq_invertibleCurveDegree ℂ _ i hC]
      exact h2
  rw [ratChern, h0, eq_comm, smul_eq_zero] at hch
  exact hch.resolve_left (by exact_mod_cast hb.ne')

end Divisors

section Append

variable {S : Scheme.{0}} [S.Over (Spec (.of ℂ))] [IsProper (S ↘ Spec (.of ℂ))]
  (hd : topologicalKrullDim S ≤ (2 : ℕ)) {t s : ℕ} {L : Fin t → S.Modules}
  {H : Fin s → S.Modules} [∀ i, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (L i)]
  [∀ j, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (H j)]
  {F : Fin (t + s) → S.Modules} [∀ i, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (F i)]
  (hFL : ∀ i, F (Fin.castAdd s i) = L i) (hFH : ∀ j, F (Fin.natAdd t j) = H j)
  (l : Fin t → ℚ) (h : Fin s → ℚ) (d : ℚ)

include hFL hFH in
/-- `((L - dH) · N) = (L · N) - d (H · N)` for `L = ∑ lᵢ Lᵢ`, `H = ∑ hⱼ Hⱼ`. -/
private theorem sum_finAppend_mul_pair (N : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N] :
    ∑ i, Fin.append l (fun j => -d * h j) i * (pair (S ↘ Spec (.of ℂ)) hd (F i) N : ℚ) =
      ∑ i, l i * (pair (S ↘ Spec (.of ℂ)) hd (L i) N : ℚ) -
        d * ∑ j, h j * (pair (S ↘ Spec (.of ℂ)) hd (H j) N : ℚ) := by
  have e1 : ∀ i, pair (S ↘ Spec (.of ℂ)) hd (F (Fin.castAdd s i)) N =
      pair (S ↘ Spec (.of ℂ)) hd (L i) N := fun i => pair_congr _ hd (hFL i) rfl
  have e2 : ∀ j, pair (S ↘ Spec (.of ℂ)) hd (F (Fin.natAdd t j)) N =
      pair (S ↘ Spec (.of ℂ)) hd (H j) N := fun j => pair_congr _ hd (hFH j) rfl
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, e1, e2, Finset.mul_sum,
    sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

include hFL hFH in
/-- `deg_C (L - dH) = deg_C L - d deg_C H`. -/
private theorem sum_finAppend_mul_degree (C : ProperCurve (S ↘ Spec (.of ℂ))) :
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
/-- `(L - dH)² = L² - 2d (L · H) + d² H²`, written with the pairing. -/
private theorem sum_sum_finAppend_mul_pair :
    ∑ i, ∑ j, Fin.append l (fun j => -d * h j) i * Fin.append l (fun j => -d * h j) j *
        (pair (S ↘ Spec (.of ℂ)) hd (F i) (F j) : ℚ) =
      ∑ i, ∑ j, l i * l j * (pair (S ↘ Spec (.of ℂ)) hd (L i) (L j) : ℚ) -
        2 * d * ∑ j, h j * ∑ i, l i * (pair (S ↘ Spec (.of ℂ)) hd (L i) (H j) : ℚ) +
        d ^ 2 * ∑ i, ∑ j, h i * h j * (pair (S ↘ Spec (.of ℂ)) hd (H i) (H j) : ℚ) := by
  have e1 : ∀ i j, pair (S ↘ Spec (.of ℂ)) hd (F (Fin.castAdd s i)) (F (Fin.castAdd s j)) =
      pair (S ↘ Spec (.of ℂ)) hd (L i) (L j) := fun i j => pair_congr _ hd (hFL i) (hFL j)
  have e2 : ∀ i j, pair (S ↘ Spec (.of ℂ)) hd (F (Fin.castAdd s i)) (F (Fin.natAdd t j)) =
      pair (S ↘ Spec (.of ℂ)) hd (L i) (H j) := fun i j => pair_congr _ hd (hFL i) (hFH j)
  have e3 : ∀ i j, pair (S ↘ Spec (.of ℂ)) hd (F (Fin.natAdd t i)) (F (Fin.castAdd s j)) =
      pair (S ↘ Spec (.of ℂ)) hd (H i) (L j) := fun i j => pair_congr _ hd (hFH i) (hFL j)
  have e4 : ∀ i j, pair (S ↘ Spec (.of ℂ)) hd (F (Fin.natAdd t i)) (F (Fin.natAdd t j)) =
      pair (S ↘ Spec (.of ℂ)) hd (H i) (H j) := fun i j => pair_congr _ hd (hFH i) (hFH j)
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, e1, e2, e3, e4,
    Finset.sum_add_distrib]
  have h2 : ∑ i, ∑ j, l i * (-d * h j) * (pair (S ↘ Spec (.of ℂ)) hd (L i) (H j) : ℚ) =
      -d * ∑ j, h j * ∑ i, l i * (pair (S ↘ Spec (.of ℂ)) hd (L i) (H j) : ℚ) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h3 : ∑ i, ∑ j, -d * h i * l j * (pair (S ↘ Spec (.of ℂ)) hd (H i) (L j) : ℚ) =
      -d * ∑ j, h j * ∑ i, l i * (pair (S ↘ Spec (.of ℂ)) hd (L i) (H j) : ℚ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pair_comm]
    ring
  have h4 : ∑ i, ∑ j, -d * h i * (-d * h j) * (pair (S ↘ Spec (.of ℂ)) hd (H i) (H j) : ℚ) =
      d ^ 2 * ∑ i, ∑ j, h i * h j * (pair (S ↘ Spec (.of ℂ)) hd (H i) (H j) : ℚ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h2, h3, h4]
  ring

end Append

/-- **The index theorem perpendicular to an isotropic class**, written with the pairing. On a
smooth projective surface with ample `A`, let `H = ∑ hⱼ Hⱼ` with `(H · A) > 0` and `(H²) = 0`,
and `L = ∑ lᵢ Lᵢ` with `(L · H) = 0`. Then `(L²) ≤ 0`; equality holds iff `L ≡ dH` numerically
for some `d`; and in that case `c₁(L - cH) = 0` in `H²(S^an; ℚ)` for `c = (L · A) / (H · A)`. -/
private theorem isotropic_index_pair {S : Scheme.{0}} [S.Over (Spec (.of ℂ))]
    [IsProper (S ↘ Spec (.of ℂ))] [Smooth (S ↘ Spec (.of ℂ))]
    (hS : MMP.Mori.IsProjectiveVariety ℂ (S ↘ Spec (.of ℂ))) (hdim : topologicalKrullDim S = 2)
    (hd : topologicalKrullDim S ≤ (2 : ℕ))
    (A : S.Modules) [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 A]
    [Stacks.Ample.IsInvertibleModule S A] (hA : Stacks.Ample.IsAmple S A)
    {s : ℕ} (h : Fin s → ℚ) (H : Fin s → S.Modules)
    [∀ j, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (H j)]
    {t : ℕ} (l : Fin t → ℚ) (L : Fin t → S.Modules)
    [∀ j, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (L j)]
    (hHA : 0 < ∑ j, h j * (pair (S ↘ Spec (.of ℂ)) hd (H j) A : ℚ))
    (hHH : ∑ i, ∑ j, h i * h j * (pair (S ↘ Spec (.of ℂ)) hd (H i) (H j) : ℚ) = 0)
    (hLH : ∑ j, h j * ∑ i, l i * (pair (S ↘ Spec (.of ℂ)) hd (L i) (H j) : ℚ) = 0) :
    ∑ i, ∑ j, l i * l j * (pair (S ↘ Spec (.of ℂ)) hd (L i) (L j) : ℚ) ≤ 0 ∧
      (∑ i, ∑ j, l i * l j * (pair (S ↘ Spec (.of ℂ)) hd (L i) (L j) : ℚ) = 0 ↔
        ∃ d : ℚ, ∀ C : ProperCurve (S ↘ Spec (.of ℂ)),
          ∑ j, l j * (C.degree ℂ (L j) : ℚ) = d * ∑ j, h j * (C.degree ℂ (H j) : ℚ)) ∧
      (∑ i, ∑ j, l i * l j * (pair (S ↘ Spec (.of ℂ)) hd (L i) (L j) : ℚ) = 0 →
        ∑ j, l j • ratChern (L j) -
          ((∑ i, l i * (pair (S ↘ Spec (.of ℂ)) hd (L i) A : ℚ)) /
            ∑ j, h j * (pair (S ↘ Spec (.of ℂ)) hd (H j) A : ℚ)) •
          ∑ j, h j • ratChern (H j) = 0) := by
  have : AlgebraicGeometry.IsProjectiveVariety ℂ (S ↘ Spec (.of ℂ)) := hS
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (S ↘ Spec (.of ℂ))
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace (S ↘ Spec (.of ℂ))
  have := isNormal_of_smooth_over_field (S ↘ Spec (.of ℂ))
  have : IsIntegral S := ((MMP.Mori.isProjectiveVariety_iff _ _).1 hS).1.toIsIntegral
  have hcart := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme
    ((isSmoothScheme_iff (S ↘ Spec (.of ℂ))).2 inferInstance)
  have : ∀ j : Fin 1, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
      ((![A] : Fin 1 → S.Modules) j) := fun _ => by simpa
  have : ∀ j : Fin 0, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
      ((![] : Fin 0 → S.Modules) j) := fun j => j.elim0
  -- the combination `L - dH`, on the family `F = (L, H)`
  obtain ⟨F, hF⟩ : ∃ F : Fin (t + s) → S.Modules, F = Fin.append L H := ⟨_, rfl⟩
  have : ∀ i, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (F i) :=
    hF ▸ isInvertible_finAppend L H
  have hFL : ∀ i, F (Fin.castAdd s i) = L i := fun i => by rw [hF, Fin.append_left]
  have hFH : ∀ j, F (Fin.natAdd t j) = H j := fun j => by rw [hF, Fin.append_right]
  -- the index theorem against the ample class `A` and its equality case
  have hnp := fun d : ℚ => by
    simpa only [sheafCombinationIntersectionNumber_one_eq_sum _ hd,
      sheafCombinationIntersectionNumber_two_eq_sum _ hd] using
      sheafCombinationIntersectionNumber_two_nonpos_of_isAmple ℂ (S ↘ Spec (.of ℂ)) hS
        hdim A hA (Fin.append l (fun j => -d * h j)) F
  have hiff := fun d : ℚ => by
    simpa only [sheafCombinationIntersectionNumber_one_eq_sum _ hd,
      sheafCombinationIntersectionNumber_two_eq_sum _ hd] using
      sheafCombinationIntersectionNumber_two_eq_zero_iff_of_isAmple ℂ (S ↘ Spec (.of ℂ)) hS
        hdim A hA (Fin.append l (fun j => -d * h j)) F
  -- `(L - dH)² = L²`, by the two vanishing cross terms
  have hQ : ∀ d : ℚ,
      ∑ i, ∑ j, Fin.append l (fun j => -d * h j) i * Fin.append l (fun j => -d * h j) j *
          (pair (S ↘ Spec (.of ℂ)) hd (F i) (F j) : ℚ) =
        ∑ i, ∑ j, l i * l j * (pair (S ↘ Spec (.of ℂ)) hd (L i) (L j) : ℚ) := fun d => by
    rw [sum_sum_finAppend_mul_pair hd hFL hFH, hLH, hHH]
    ring
  -- `((L - cH) · A) = 0` for `c = (L · A) / (H · A)`, so equality makes `L - cH` trivial
  set c := (∑ i, l i * (pair (S ↘ Spec (.of ℂ)) hd (L i) A : ℚ)) /
    ∑ j, h j * (pair (S ↘ Spec (.of ℂ)) hd (H j) A : ℚ) with hc
  have hMA : ∑ i, Fin.append l (fun j => -c * h j) i *
      (pair (S ↘ Spec (.of ℂ)) hd (F i) A : ℚ) = 0 := by
    rw [sum_finAppend_mul_pair hd hFL hFH, hc, div_mul_cancel₀ _ hHA.ne', sub_self]
  have hnum := fun h0 => (hiff c hMA).mp ((hQ c).trans h0)
  refine ⟨(hQ c).symm.trans_le (hnp c hMA), ⟨fun h0 => ⟨c, fun C => ?_⟩, ?_⟩, fun h0 => ?_⟩
  · linarith [(sum_finAppend_mul_degree hFL hFH l h c C).symm.trans (hnum h0 C)]
  · rintro ⟨d, hdC⟩
    have hnumd : ∀ C : ProperCurve (S ↘ Spec (.of ℂ)),
        ∑ i, Fin.append l (fun j => -d * h j) i * (C.degree ℂ (F i) : ℚ) = 0 := fun C => by
      rw [sum_finAppend_mul_degree hFL hFH, hdC C, sub_self]
    rw [← hQ d, Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← mul_zero (Fin.append l (fun j => -d * h j) j),
      ← sum_mul_pair_eq_zero_of_forall_degree hcart hd _ F hnumd (F j), Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  · rw [← sum_finAppend_smul_ratChern hFL hFH]
    exact sum_smul_ratChern_eq_zero_of_forall_degree hcart hS hdim _ F (hnum h0)

end MMP.Fold06.LemMmpSurfaceIsotropicDivisorIndex

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

open MMP.Analytic

/-- **The intersection form perpendicular to an isotropic class on a surface.** Let `S` be a
smooth projective complex surface, `A` an ample invertible sheaf, and `H = ∑ⱼ hⱼ Hⱼ`,
`L = ∑ⱼ lⱼ Lⱼ` rational combinations of invertible sheaves with `(H · A) > 0`, `(H²) = 0` and
`(L · H) = 0`. Then `(L²) ≤ 0`; `(L²) = 0` if and only if there is `d : ℚ` with
`deg_C L = d · deg_C H` for every proper curve `C ⊆ S`; and in that case, with
`c = (L · A) / (H · A)`, the class `∑ⱼ lⱼ c₁(Lⱼ) - c ∑ⱼ hⱼ c₁(Hⱼ)` vanishes in `H²(S^an; ℚ)`. -/
@[mmp "lem_mmp_surface_isotropic_divisor_index"]
public theorem sheafCombinationIntersectionNumber_two_nonpos_of_isotropic
    {S : Scheme.{0}} [S.Over (Spec (.of ℂ))] [IsProper (S ↘ Spec (.of ℂ))]
    [Smooth (S ↘ Spec (.of ℂ))] (hS : IsProjectiveVariety ℂ (S ↘ Spec (.of ℂ)))
    (hdim : topologicalKrullDim S = 2)
    (A : S.Modules) [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 A]
    [Stacks.Ample.IsInvertibleModule S A] (hA : Stacks.Ample.IsAmple S A)
    {s : ℕ} (h : Fin s → ℚ) (H : Fin s → S.Modules)
    [hH : ∀ j, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (H j)]
    {t : ℕ} (l : Fin t → ℚ) (L : Fin t → S.Modules)
    [∀ j, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (L j)] :
    haveI : ∀ j : Fin 1, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
        ((![A] : Fin 1 → S.Modules) j) := fun _ => by simpa
    haveI : ∀ j : Fin 0, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
        ((![] : Fin 0 → S.Modules) j) := fun j => j.elim0
    haveI : ∀ (j : Fin s) (m : Fin 1), SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
        ((![H j] : Fin 1 → S.Modules) m) := fun j _ => by simpa using hH j
    0 < sheafCombinationIntersectionNumber ℂ (S ↘ Spec (.of ℂ)) (𝟙 S) ℚ h H 1 ![A]
        (by rw [hdim]; rfl) →
    sheafCombinationIntersectionNumber ℂ (S ↘ Spec (.of ℂ)) (𝟙 S) ℚ h H 2 ![]
        (by rw [hdim]; rfl) = 0 →
    ∑ j, h j * sheafCombinationIntersectionNumber ℂ (S ↘ Spec (.of ℂ)) (𝟙 S) ℚ l L 1 ![H j]
        (by rw [hdim]; rfl) = 0 →
    sheafCombinationIntersectionNumber ℂ (S ↘ Spec (.of ℂ)) (𝟙 S) ℚ l L 2 ![]
        (by rw [hdim]; rfl) ≤ 0 ∧
      (sheafCombinationIntersectionNumber ℂ (S ↘ Spec (.of ℂ)) (𝟙 S) ℚ l L 2 ![]
          (by rw [hdim]; rfl) = 0 ↔
        ∃ d : ℚ, ∀ C : ProperCurve (S ↘ Spec (.of ℂ)),
          ∑ j, l j * (C.degree ℂ (L j) : ℚ) = d * ∑ j, h j * (C.degree ℂ (H j) : ℚ)) ∧
      (sheafCombinationIntersectionNumber ℂ (S ↘ Spec (.of ℂ)) (𝟙 S) ℚ l L 2 ![]
          (by rw [hdim]; rfl) = 0 →
        ∑ j, l j • singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
            (algebraicFirstChernClass (L j)) -
          (sheafCombinationIntersectionNumber ℂ (S ↘ Spec (.of ℂ)) (𝟙 S) ℚ l L 1 ![A]
              (by rw [hdim]; rfl) /
            sheafCombinationIntersectionNumber ℂ (S ↘ Spec (.of ℂ)) (𝟙 S) ℚ h H 1 ![A]
              (by rw [hdim]; rfl)) •
          ∑ j, h j • singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
            (algebraicFirstChernClass (H j)) = 0) := by
  have : ∀ j : Fin 1, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
      ((![A] : Fin 1 → S.Modules) j) := fun _ => by simpa
  have : ∀ j : Fin 0, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
      ((![] : Fin 0 → S.Modules) j) := fun j => j.elim0
  intro hHA hHH hLH
  have hd : topologicalKrullDim S ≤ (2 : ℕ) := by rw [hdim]; rfl
  simp only [Fold06.LemMmpSurfaceIsotropicDivisorIndex.sheafCombinationIntersectionNumber_one_eq_sum
      _ hd,
    Fold06.LemMmpSurfaceIsotropicDivisorIndex.sheafCombinationIntersectionNumber_two_eq_sum _ hd]
    at hHA hHH hLH ⊢
  exact Fold06.LemMmpSurfaceIsotropicDivisorIndex.isotropic_index_pair hS hdim hd A hA h H l L
    hHA hHH hLH

end MMP.Mori
