module

public import MMP.AlgebraicGeometry.Intersection.OneCycles
public import MMP.AlgebraicGeometry.Intersection.InvertibleSheafCurveDegree
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.ChowDegree
public import MMP.AlgebraicGeometry.Intersection.CartierRestriction
public import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
public import MMP.AlgebraicGeometry.Resolution.BlowupChartClosedImmersion
public import MMP.AlgebraicGeometry.Intersection.EulerPolynomialGenericRank
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.Additivity
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.PicardForm
public import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.IsolatedPointAlgebraicKernel
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafMul
public import MMP.AlgebraicGeometry.SubschemeOver

/-!
# Intersection numbers against divisors supported on curves of degree zero

Let `X` be a proper scheme over a field `k` of dimension at most three. This file proves that
intersection numbers `(N · D · L · X)` vanish when `D` is an effective Cartier divisor and `N` has
degree zero on every proper curve contained in `Supp D`: cutting down by `D` turns the number
into `(N|_D · L|_D · D)`, and on `D` the sheaf `𝒪(N)|_D` is numerically trivial. The same holds
for `ℚ`-combinations `N = ∑ c_P π_P` of Cartier divisors, and for `D` replaced by any invertible
sheaf `H ≅ 𝒪_X(D₁ - D₂)` with `D₁, D₂` effective. The quadratic numbers `(N · N · H · X)` then
vanish as well, by symmetry of intersection numbers.

This is the numerical part of the statement that, on a component `E` of the exceptional divisor
of a curve-and-point model with curve image `T`, a `ℚ`-divisor whose curve classes vanish on the
general fibres of `E → T` has `(M · H · A) = (M · M · H) = 0` for `H` pulled back from `Y`: a
Cartier divisor on `Y` pulls back to a difference of effective divisors supported on finitely
many general fibres, on whose curves `M` has degree zero.

## Main results

* `MMP.Mori.sheafIntersectionNumber_cartier_eq_zero_of_degree_eq_zero_on_isEffective`:
  `(N · D · L · X) = 0` if `deg_C 𝒪(N) = 0` on the proper curves `C ⊆ Supp D`.
* `MMP.Mori.sum_sheafIntersectionNumber_eq_zero_of_degree_eq_zero_on_isEffective`: the same for
  a `ℚ`-combination `∑ c_P π_P`.
* `MMP.Mori.sum_sheafIntersectionNumber_eq_zero_of_iso_sheaf_sub`: the same with `D` replaced by
  an invertible sheaf isomorphic to `𝒪_X(D₁ - D₂)`, `D₁, D₂` effective.
* `MMP.Mori.sum_sum_sheafIntersectionNumber_eq_zero_of_forall`: `∑ c_P c_Q (π_P · π_Q · H) = 0`
  once `∑ c_P (π_P · H · L) = 0` for every invertible `L`.
* `MMP.Mori.sheafIntersectionNumber_update_sheaf_add`: additivity in a Cartier slot of
  `MMP.Mori.sheafIntersectionNumber` (symmetry and isomorphism invariance are
  `MMP.Fold06.ThmMmpConductorIsolatedPointAlgebraicKernel.sIN_perm` and `sIN_congr_iso`).

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 1.33–1.36
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped MMP.SubschemeOver

namespace MMP.Mori

open MMP.Fold06.ThmMmpConductorIsolatedPointAlgebraicKernel (sIN_perm sIN_congr_iso)

section Additivity

variable (k : Type) [Field k] {X W : Scheme.{0}} (f : X ⟶ Spec (.of k)) [IsProper f]
  (i : W ⟶ X) [IsClosedImmersion i] (d : ℕ) (hd : topologicalKrullDim W ≤ d)

/-- Intersection numbers of equal families agree (the invertibility instances are proofs). -/
theorem sheafIntersectionNumber_congr_family {L L' : Fin d → X.Modules}
    [hL : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    [hL' : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L' j)] (h : L = L') :
    sheafIntersectionNumber k f i d hd L = sheafIntersectionNumber k f i d hd L' := by
  subst h
  rfl

/-- **Additivity in a Cartier slot**: `(⋯ 𝒪_X(B + B') ⋯ · W) = (⋯ 𝒪_X(B) ⋯ · W) +
(⋯ 𝒪_X(B') ⋯ · W)`, the divisor in slot `j`. -/
theorem sheafIntersectionNumber_update_sheaf_add (L : Fin d → X.Modules)
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L q)] (j : Fin d)
    (B B' : X.CartierDivisor) :
    @sheafIntersectionNumber k _ X W f _ i _ d hd
        (Function.update L j (MMP.CartierDivisor.sheaf (B + B'))) (isInvertible_update L j _) =
      @sheafIntersectionNumber k _ X W f _ i _ d hd
          (Function.update L j (MMP.CartierDivisor.sheaf B)) (isInvertible_update L j _) +
        @sheafIntersectionNumber k _ X W f _ i _ d hd
          (Function.update L j (MMP.CartierDivisor.sheaf B')) (isInvertible_update L j _) := by
  have := isInvertible_update L j (MMP.CartierDivisor.sheaf (B + B'))
  have := isInvertible_update L j (MMP.CartierDivisor.sheaf B)
  have := isInvertible_update L j (MMP.CartierDivisor.sheaf B')
  rw [Snapper.sheafIntersectionNumber_eq_intersectionNumber,
    Snapper.sheafIntersectionNumber_eq_intersectionNumber,
    Snapper.sheafIntersectionNumber_eq_intersectionNumber]
  refine intersectionNumber_tensor k f i d hd j _ _ _ (fun q hq ↦ ?_) (fun q hq ↦ ?_) ?_
  · simp [Function.update_of_ne hq]
  · simp [Function.update_of_ne hq]
  · exact eqToIso (by simp) ≪≫ (MMP.CartierDivisorSheaf.sheafMulIso B B').symm ≪≫
      eqToIso (by simp only [Function.update_self]; rfl)

end Additivity

section Cut

variable (k : Type) [Field k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [IsProper sX]

/-- **A divisor of degree zero on the curves of an effective divisor `D`.** Let `X` be a proper
`k`-scheme of dimension at most three, `D` an effective Cartier divisor on `X`, `N` a Cartier
divisor with `deg_C 𝒪_X(N) = 0` on every proper curve `C ⊆ Supp D`, and `L` an invertible sheaf
on `X`. Then `(N · D · L · X) = 0`. -/
theorem sheafIntersectionNumber_cartier_eq_zero_of_degree_eq_zero_on_isEffective
    (hd : topologicalKrullDim X ≤ (3 : ℕ)) (N D : X.CartierDivisor)
    (hD : MMP.Intersection.IsEffective D)
    (hN : ∀ C : ProperCurve sX, C.point ∈ (MMP.CartierDivisor.subscheme D hD).support →
      C.degree k (MMP.CartierDivisor.sheaf N) = 0)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    @sheafIntersectionNumber k _ X X sX _ (𝟙 X) _ 3 hd
      ![MMP.CartierDivisor.sheaf N, MMP.CartierDivisor.sheaf D, L]
      (fun t ↦ by fin_cases t <;> dsimp <;> infer_instance) = 0 := by
  have : ∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (![MMP.CartierDivisor.sheaf N, MMP.CartierDivisor.sheaf D, L] t) := fun t ↦ by
    fin_cases t <;> dsimp <;> infer_instance
  have hDNL : ∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (![MMP.CartierDivisor.sheaf D, MMP.CartierDivisor.sheaf N, L] t) := fun t ↦ by
    fin_cases t <;> dsimp <;> infer_instance
  set j := (MMP.CartierDivisor.subscheme D hD).subschemeι
  have hd' := topologicalKrullDim_subscheme_le_of_isEffective k sX (𝟙 X) 2 hd D hD
  have : ∀ t, SheafOfModules.IsInvertible (MMP.CartierDivisor.subscheme D hD).subscheme.presheaf
      (MMP.CartierDivisor.subscheme D hD).subscheme.ringCatSheaf.2
      ((fun t : Fin 2 ↦ (Scheme.Modules.pullback j).obj
      (![MMP.CartierDivisor.sheaf D, MMP.CartierDivisor.sheaf N, L] t.succ)) t) := fun t ↦ by
    fin_cases t <;> dsimp <;> infer_instance
  rw [← sIN_perm sX (𝟙 X) 3 hd _ (Equiv.swap 0 1),
    sheafIntersectionNumber_congr_family k sX (𝟙 X) 3 hd
      (hL' := hDNL) (funext fun t ↦ by fin_cases t <;> rfl),
    sheafIntersectionNumber_eq_of_isEffective k sX (𝟙 X) 2 hd _ D hD
      ((Scheme.Modules.pullbackId X).app _),
    sheafIntersectionNumber_congr_hom k sX (by rw [Category.comp_id, Category.id_comp] :
      j ≫ 𝟙 X = 𝟙 _ ≫ j),
    sheafIntersectionNumber_comp_eq_of_iso k sX j (𝟙 _) 2 hd' _ _ fun t ↦ Iso.refl _]
  refine sheafIntersectionNumber_eq_zero_of_degree_eq_zero k (j ≫ sX) (𝟙 _) 1 hd' _ fun C ↦ ?_
  change C.degree k ((Scheme.Modules.pullback j).obj (MMP.CartierDivisor.sheaf N)) = 0
  rw [ProperCurve.degree_pullback j rfl C]
  split_ifs with h
  · rw [hN ⟨_, h⟩ (by
      change j C.point ∈ ((MMP.CartierDivisor.subscheme D hD).support : Set X)
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨_, rfl⟩), mul_zero]
  · rfl

/-- **A `ℚ`-combination of divisors of degree zero on the curves of an effective divisor.** Let
`X` be a proper `k`-scheme of dimension at most three, `D` an effective Cartier divisor on `X` and
`N = ∑ c_P π_P` a `ℚ`-combination of Cartier divisors with `∑ c_P deg_C 𝒪_X(π_P) = 0` on every
proper curve `C ⊆ Supp D`. Then `∑ c_P (π_P · D · L · X) = 0` for every invertible sheaf `L`. -/
theorem sum_sheafIntersectionNumber_eq_zero_of_degree_eq_zero_on_isEffective {ι : Type*}
    (hd : topologicalKrullDim X ≤ (3 : ℕ)) (π : ι → X.CartierDivisor) (c : ι →₀ ℚ)
    (D : X.CartierDivisor) (hD : MMP.Intersection.IsEffective D)
    (hc : ∀ C : ProperCurve sX, C.point ∈ (MMP.CartierDivisor.subscheme D hD).support →
      (c.sum fun P a ↦ a * (C.degree k (MMP.CartierDivisor.sheaf (π P)) : ℚ)) = 0)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    (c.sum fun P a ↦ a * (@sheafIntersectionNumber k _ X X sX _ (𝟙 X) _ 3 hd
      ![MMP.CartierDivisor.sheaf (π P), MMP.CartierDivisor.sheaf D, L]
      (fun t ↦ by fin_cases t <;> dsimp <;> infer_instance) : ℚ)) = 0 := by
  classical
  -- clear the denominators of `c`
  set m : ℕ := ∏ P ∈ c.support, (c P).den with hm
  have hm0 : (m : ℚ) ≠ 0 := by
    rw [hm, Nat.cast_ne_zero, Finset.prod_ne_zero_iff]
    exact fun P _ ↦ (c P).den_nz
  have hn : ∀ P, ∃ z : ℤ, (m : ℚ) * c P = z := by
    intro P
    by_cases hP : P ∈ c.support
    · obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem (fun Q ↦ (c Q).den) hP
      refine ⟨q * (c P).num, ?_⟩
      rw [hm, hq]
      push_cast
      rw [mul_comm ((c P).den : ℚ), mul_assoc, Rat.den_mul_eq_num]
    · exact ⟨0, by rw [Finsupp.notMem_support_iff.1 hP, mul_zero, Int.cast_zero]⟩
  choose n hn using hn
  -- the slot-zero intersection number and the curve degrees are additive
  let F := ![MMP.CartierDivisor.sheaf D, MMP.CartierDivisor.sheaf D, L]
  have : ∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (F t) := fun t ↦ by
    fin_cases t <;> dsimp [F] <;> infer_instance
  have hF : ∀ B : X.CartierDivisor,
      ![MMP.CartierDivisor.sheaf B, MMP.CartierDivisor.sheaf D, L] =
        Function.update F 0 (MMP.CartierDivisor.sheaf B) := fun B ↦ funext fun t ↦ by
    fin_cases t <;> simp [F]
  let φ : X.CartierDivisor →+ ℤ := AddMonoidHom.mk' (fun B ↦
      @sheafIntersectionNumber k _ X X sX _ (𝟙 X) _ 3 hd
        (Function.update F 0 (MMP.CartierDivisor.sheaf B)) (isInvertible_update F 0 _))
    (sheafIntersectionNumber_update_sheaf_add k sX (𝟙 X) 3 hd F 0)
  have hφ : ∀ B : X.CartierDivisor, @sheafIntersectionNumber k _ X X sX _ (𝟙 X) _ 3 hd
      ![MMP.CartierDivisor.sheaf B, MMP.CartierDivisor.sheaf D, L]
      (fun t ↦ by fin_cases t <;> dsimp <;> infer_instance) = φ B := fun B ↦
    sheafIntersectionNumber_congr_family k sX (𝟙 X) 3 hd
      (hL := fun t ↦ by fin_cases t <;> dsimp <;> infer_instance)
      (hL' := isInvertible_update F 0 _) (hF B)
  let ψ : ProperCurve sX → X.CartierDivisor →+ ℤ := fun C ↦ AddMonoidHom.mk'
    (fun B ↦ C.degree k (MMP.CartierDivisor.sheaf B)) fun B B' ↦ by
      have : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
          ((MMP.CartierDivisor.sheaf B).tensorObj (MMP.CartierDivisor.sheaf B')) :=
        Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible X.presheaf
          X.ringCatSheaf.2 _ _
      exact (degreeOn_eq_of_iso k sX C.ι C.dim_le
        (MMP.CartierDivisorSheaf.sheafMulIso B B')).symm.trans
        (degreeOn_tensorSheaf k sX C.ι C.dim_le _ _ (hLM := this))
  -- the integral divisor `N = m ∑ c_P π_P`
  set N : X.CartierDivisor := ∑ P ∈ c.support, n P • π P with hN
  have hsum : ∀ g : X.CartierDivisor →+ ℤ,
      ((g N : ℤ) : ℚ) = (m : ℚ) * c.sum fun P a ↦ a * (g (π P) : ℚ) := by
    intro g
    rw [hN, map_sum, Finsupp.sum, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun P _ ↦ ?_
    rw [map_zsmul, smul_eq_mul, Int.cast_mul, ← hn P, mul_assoc]
  have hφN : φ N = 0 := by
    rw [← hφ N]
    refine sheafIntersectionNumber_cartier_eq_zero_of_degree_eq_zero_on_isEffective k sX hd N D
      hD (fun C hC ↦ ?_) L
    have h := hsum (ψ C)
    change ((C.degree k (MMP.CartierDivisor.sheaf N) : ℤ) : ℚ) =
      m * c.sum fun P a ↦ a * ((C.degree k (MMP.CartierDivisor.sheaf (π P)) : ℤ) : ℚ) at h
    rw [hc C hC, mul_zero] at h
    exact_mod_cast h
  have h := hsum φ
  rw [hφN, Int.cast_zero, eq_comm, mul_eq_zero] at h
  simp only [← hφ] at h
  exact h.resolve_left hm0

/-- **Replacing an effective divisor by a difference of effective divisors.** Let
`X` be a proper `k`-scheme of dimension at most three, `H` an invertible sheaf with
`H ≅ 𝒪_X(D₁ - D₂)` for effective Cartier divisors `D₁, D₂`, and `∑ c_P π_P` a `ℚ`-combination of
Cartier divisors with `∑ c_P deg_C 𝒪_X(π_P) = 0` on every proper curve `C ⊆ Supp D₁ ∪ Supp D₂`.
Then `∑ c_P (π_P · H · L · X) = 0` for every invertible sheaf `L`. -/
theorem sum_sheafIntersectionNumber_eq_zero_of_iso_sheaf_sub {ι : Type*}
    (hd : topologicalKrullDim X ≤ (3 : ℕ)) (π : ι → X.CartierDivisor) (c : ι →₀ ℚ)
    (H : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 H]
    (D₁ D₂ : X.CartierDivisor) (h₁ : MMP.Intersection.IsEffective D₁)
    (h₂ : MMP.Intersection.IsEffective D₂) (he : Nonempty (H ≅ MMP.CartierDivisor.sheaf (D₁ - D₂)))
    (hc : ∀ C : ProperCurve sX, (C.point ∈ (MMP.CartierDivisor.subscheme D₁ h₁).support ∨
        C.point ∈ (MMP.CartierDivisor.subscheme D₂ h₂).support) →
      (c.sum fun P a ↦ a * (C.degree k (MMP.CartierDivisor.sheaf (π P)) : ℚ)) = 0)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    (c.sum fun P a ↦ a * (@sheafIntersectionNumber k _ X X sX _ (𝟙 X) _ 3 hd
      ![MMP.CartierDivisor.sheaf (π P), H, L]
      (fun t ↦ by fin_cases t <;> dsimp <;> infer_instance) : ℚ)) = 0 := by
  classical
  have key : ∀ P, (@sheafIntersectionNumber k _ X X sX _ (𝟙 X) _ 3 hd
      ![MMP.CartierDivisor.sheaf (π P), H, L]
      (fun t ↦ by fin_cases t <;> dsimp <;> infer_instance) : ℚ) =
      (@sheafIntersectionNumber k _ X X sX _ (𝟙 X) _ 3 hd
        ![MMP.CartierDivisor.sheaf (π P), MMP.CartierDivisor.sheaf D₁, L]
        (fun t ↦ by fin_cases t <;> dsimp <;> infer_instance) : ℚ) -
      (@sheafIntersectionNumber k _ X X sX _ (𝟙 X) _ 3 hd
        ![MMP.CartierDivisor.sheaf (π P), MMP.CartierDivisor.sheaf D₂, L]
        (fun t ↦ by fin_cases t <;> dsimp <;> infer_instance) : ℚ) := by
    intro P
    let F := ![MMP.CartierDivisor.sheaf (π P), H, L]
    have : ∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (F t) := fun t ↦ by
      fin_cases t <;> dsimp [F] <;> infer_instance
    have hF : ∀ B : X.CartierDivisor,
        ![MMP.CartierDivisor.sheaf (π P), MMP.CartierDivisor.sheaf B, L] =
          Function.update F 1 (MMP.CartierDivisor.sheaf B) := fun B ↦ funext fun t ↦ by
      fin_cases t <;> simp [F]
    let φ : X.CartierDivisor →+ ℤ := AddMonoidHom.mk' (fun B ↦
        @sheafIntersectionNumber k _ X X sX _ (𝟙 X) _ 3 hd
          (Function.update F 1 (MMP.CartierDivisor.sheaf B)) (isInvertible_update F 1 _))
      (sheafIntersectionNumber_update_sheaf_add k sX (𝟙 X) 3 hd F 1)
    have hφ : ∀ B : X.CartierDivisor, @sheafIntersectionNumber k _ X X sX _ (𝟙 X) _ 3 hd
        ![MMP.CartierDivisor.sheaf (π P), MMP.CartierDivisor.sheaf B, L]
        (fun t ↦ by fin_cases t <;> dsimp <;> infer_instance) = φ B := fun B ↦
      sheafIntersectionNumber_congr_family k sX (𝟙 X) 3 hd
        (hL := fun t ↦ by fin_cases t <;> dsimp <;> infer_instance)
        (hL' := isInvertible_update F 1 _) (hF B)
    have hH : @sheafIntersectionNumber k _ X X sX _ (𝟙 X) _ 3 hd
        ![MMP.CartierDivisor.sheaf (π P), H, L]
        (fun t ↦ by fin_cases t <;> dsimp <;> infer_instance) = φ (D₁ - D₂) := by
      rw [← hφ]
      have : ∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
          (![MMP.CartierDivisor.sheaf (π P), MMP.CartierDivisor.sheaf (D₁ - D₂), L] t) := fun t ↦ by
        fin_cases t <;> dsimp <;> infer_instance
      refine sIN_congr_iso sX (𝟙 X) 3 hd _ _ fun t ↦ ?_
      fin_cases t
      · exact ⟨Iso.refl _⟩
      · exact he
      · exact ⟨Iso.refl _⟩
    rw [hH, map_sub, hφ, hφ]
    push_cast
    rfl
  simp only [key, mul_sub, Finsupp.sum_sub]
  rw [sum_sheafIntersectionNumber_eq_zero_of_degree_eq_zero_on_isEffective k sX hd π c D₁ h₁
      (fun C hC ↦ hc C (Or.inl hC)) L,
    sum_sheafIntersectionNumber_eq_zero_of_degree_eq_zero_on_isEffective k sX hd π c D₂ h₂
      (fun C hC ↦ hc C (Or.inr hC)) L, sub_zero]

/-- **The quadratic term from the linear one.** If `∑ c_P (π_P · H · L · X) = 0` for every
invertible sheaf `L` on `X`, then `∑_{P, Q} c_P c_Q (π_P · π_Q · H · X) = 0`. -/
theorem sum_sum_sheafIntersectionNumber_eq_zero_of_forall {ι : Type*}
    (hd : topologicalKrullDim X ≤ (3 : ℕ)) (π : ι → X.CartierDivisor) (c : ι →₀ ℚ)
    (H : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 H]
    (h : ∀ (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L],
      (c.sum fun P a ↦ a * (@sheafIntersectionNumber k _ X X sX _ (𝟙 X) _ 3 hd
        ![MMP.CartierDivisor.sheaf (π P), H, L]
        (fun t ↦ by fin_cases t <;> dsimp <;> infer_instance) : ℚ)) = 0) :
    (c.sum fun P a ↦ c.sum fun Q b ↦ a * b * (@sheafIntersectionNumber k _ X X sX _ (𝟙 X) _ 3 hd
      ![MMP.CartierDivisor.sheaf (π P), MMP.CartierDivisor.sheaf (π Q), H]
      (fun t ↦ by fin_cases t <;> dsimp <;> infer_instance) : ℚ)) = 0 := by
  have hswap : ∀ P Q, (@sheafIntersectionNumber k _ X X sX _ (𝟙 X) _ 3 hd
      ![MMP.CartierDivisor.sheaf (π P), MMP.CartierDivisor.sheaf (π Q), H]
      (fun t ↦ by fin_cases t <;> dsimp <;> infer_instance)) =
      @sheafIntersectionNumber k _ X X sX _ (𝟙 X) _ 3 hd
        ![MMP.CartierDivisor.sheaf (π P), H, MMP.CartierDivisor.sheaf (π Q)]
        (fun t ↦ by fin_cases t <;> dsimp <;> infer_instance) := by
    intro P Q
    have : ∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
        (![MMP.CartierDivisor.sheaf (π P), MMP.CartierDivisor.sheaf (π Q), H] t) := fun t ↦ by
      fin_cases t <;> dsimp <;> infer_instance
    rw [← sIN_perm sX (𝟙 X) 3 hd _ (Equiv.swap 1 2)]
    exact sheafIntersectionNumber_congr_family k sX (𝟙 X) 3 hd
      (hL' := fun t ↦ by fin_cases t <;> dsimp <;> infer_instance)
      (funext fun t ↦ by fin_cases t <;> rfl)
  have h0 := fun Q ↦ h (MMP.CartierDivisor.sheaf (π Q))
  simp only [hswap]
  simp only [Finsupp.sum] at h0 ⊢
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun Q _ ↦ ?_
  rw [← zero_mul (c Q), ← h0 Q, Finset.sum_mul]
  exact Finset.sum_congr rfl fun P _ ↦ by ring

end Cut

end MMP.Mori
