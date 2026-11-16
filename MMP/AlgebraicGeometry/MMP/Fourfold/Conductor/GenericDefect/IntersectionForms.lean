module

import StacksFrontier.AlgebraicGeometry.AffineClosedUnion.Global
public import Mathlib
public import MMP.AlgebraicGeometry.MMP.Fourfold.ConductorDefect
public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.IsolatedPointAlgebraicKernel
public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.GenericDefect.HodgeIndexNumerical
public import MMP.AlgebraicTopology.ComplexVectorBundle.FirstChernClass
import MMP.AlgebraicGeometry.Chow.CapDegreeDivisorGysinComponent
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.GenericDefect.IntersectionFormsDegree
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.VerticalKernelBlowup
import MMP.AlgebraicGeometry.Analytic.ThreefoldVanishingChernClass
import MMP.AlgebraicGeometry.Intersection.PullbackAmpleIntersectionNumbers
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.WeightedSurfaceIdentity
import MMP.AlgebraicGeometry.Resolution.BlowupChartClosedImmersion
import MMP.AlgebraicGeometry.Intersection.ThreefoldIsotropicHodgeIndex
import MMP.AlgebraicGeometry.Intersection.ThreefoldHodgeIndex
import MMP.AlgebraicGeometry.Intersection.Surface.IsotropicDivisorIndex
import MMP.AlgebraicGeometry.Positivity.BigAmplePlusEffective
public import MMP.AlgebraicGeometry.ReducedSubschemeOver
public import MMP.AlgebraicGeometry.SubschemeOver

/-!
# The intersection forms of the generic-defect Hodge index argument

Let `Z` be a smooth projective complex fourfold, `F = ∑ᵢ Fᵢ` a reduced snc divisor on `Z` with
components `Fᵢ`, `εᵢ` a Cartier divisor with Weil divisor `Fᵢ`, and for every prime divisor `P`
of `Fᵢ` a Cartier divisor `π_P` on `Fᵢ` with Weil divisor `P`. For Cartier divisors `A` and `H` on
`Z` with `𝒪_Z(A + ∑ₗ nₗ εₗ) ≅ 𝒪_Z(N H)` (that is, `A = N H - D` with `D = ∑ₗ nₗ Fₗ`), the
intersection numbers on the components and on the double surfaces satisfy the identities and
inequalities that the numerical Hodge index argument
`MMP.Fourfold.exists_mem_orientedSurfaceCoefficients_forall_sub_mem_of_hodgeIndex` takes as
hypotheses: the adjunction identities for `Fᵢ|_{Fᵢ}`, the two identities of a family of divisors
with zero ambient class, and the vanishing of the forms on divisors of class zero.

## Main results

* `MMP.Fourfold.num3_pullback_eq_of_iso`: `(M₁ · M₂ · A) = N (M₁ · M₂ · H) - ∑ₗ nₗ (M₁ · M₂ · Fₗ)`.
* `MMP.Fourfold.neg_mul_bilin_bG_eq_of_iso`:
  `-nᵢ (x² · Fᵢ) = x² · A - N (x² · H) + ∑_S n_{S'} (x|_S)²`.
* `MMP.Fourfold.neg_mul_lin_bGA_eq_of_iso`:
  `-nᵢ (x · A · Fᵢ) = x · A² - N (x · H · A) + ∑_S n_{S'} (x|_S · A|_S)`.
* `MMP.Fourfold.kernel_identities_sub_surfaceCoefficientDivisor`: the two identities of a family
  with zero ambient class, for `L - Z(a)`.
* `MMP.Fourfold.linearCombination_num3_eq_zero_of_divisorClass_eq_zero`: a `ℚ`-divisor of class
  zero on a smooth complete threefold has zero intersection numbers;
  `MMP.Fourfold.linearCombination_bGA_eq_zero_of_mem_ker` and
  `MMP.Fourfold.linearCombination_bUA_eq_zero_of_mem_ker` are its instances on the components.
* `MMP.Fourfold.threefold_index_of_isotropic`, `MMP.Fourfold.surface_index_of_isotropic`: the
  index theorems perpendicular to `H` on the components and double surfaces over curves.
* `MMP.Fourfold.eq_zero_of_sum_bilin_bB_div_eq_zero`: negative definiteness on the point-edge
  systems.

## Implementation notes

The forms are those of the point-image case (`bB`, `bG`, `bGA`, `bLam`, `bU`, `bC`, `bUA`); the
divisor `-D` of that case is `-∑ₗ nₗ εₗ`, and the identities for `A = N H - D` follow from those
for `-D` by additivity of the intersection numbers in the slot of `A`. The vanishing on divisors of
class zero goes through Stacks' Chow groups: `∑_P x_P c₁(π_P) ∩ [Fᵢ]` has cycle class `[x]`, and
a homologically trivial class has zero degree against `c₁(L₂) c₁(L₃)`.
-/

public section

open AlgebraicGeometry CategoryTheory MMP
open MMP.Fold06.ThmMmpConductorIsolatedPointAlgebraicKernel
open scoped MMP.SubschemeOver

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori TopologicalSpace

section Slot

variable {k : Type} [Field k] {X Y W : Scheme.{0}} (f : X ⟶ Spec (.of k)) [IsProper f]
  (i : Y ⟶ X) [IsClosedImmersion i] (d : ℕ) (hd : topologicalKrullDim Y ≤ d)
  (L : Fin d → X.Modules) [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L q)]
  (j : Fin d) (g : X ⟶ W)

/-- `slotHom` only depends on the isomorphism class of `𝒪_W(C)`. -/
theorem slotHom_eq_of_iso {C C' : W.CartierDivisor}
    (e : Nonempty (MMP.CartierDivisor.sheaf C ≅ MMP.CartierDivisor.sheaf C')) :
    slotHom f i d hd L j g C = slotHom f i d hd L j g C' := by
  have := isInvertible_update L j ((Scheme.Modules.pullback g).obj (MMP.CartierDivisor.sheaf C))
  have := isInvertible_update L j ((Scheme.Modules.pullback g).obj (MMP.CartierDivisor.sheaf C'))
  rw [slotHom_apply, slotHom_apply, Snapper.sheafIntersectionNumber_eq_intersectionNumber,
    Snapper.sheafIntersectionNumber_eq_intersectionNumber]
  exact AlgebraicGeometry.intersectionNumber_eq_of_iso_at k f i d hd _ _ j
    (fun q hq => by rw [Function.update_of_ne hq, Function.update_of_ne hq])
    (eqToIso (Function.update_self j _ L) ≪≫ (Scheme.Modules.pullback g).mapIso e.some ≪≫
      eqToIso (Function.update_self j _ L).symm)

end Slot

section Num

attribute [local instance] MMP.Fold06.ThmMmpConductorIsolatedPointAlgebraicKernel.inv_vec1
  MMP.Fold06.ThmMmpConductorIsolatedPointAlgebraicKernel.inv_vec2
  MMP.Fold06.ThmMmpConductorIsolatedPointAlgebraicKernel.inv_vec3

/-- **The adjunction relation in the last slot.** If `𝒪_X(A + ∑ₗ nₗ εₗ) ≅ 𝒪_X(N H)`, then for
`g : W ⟶ X`: `(M₁ · M₂ · g^*A) = N (M₁ · M₂ · g^*H) - ∑ₗ nₗ (M₁ · M₂ · g^*εₗ)`. -/
theorem num3_pullback_eq_of_iso {W X : Scheme.{0}} (f : W ⟶ Spec (.of ℂ)) [IsProper f]
    (g : W ⟶ X) (M₁ M₂ : W.Modules)
    [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 M₁]
    [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 M₂]
    {ι : Type*} (s : Finset ι) (Hc Hh : X.CartierDivisor) (ε : ι → X.CartierDivisor)
    (n : ι → ℕ) (N : ℕ)
    (hAH : Nonempty (MMP.CartierDivisor.sheaf (Hc + ∑ l ∈ s, n l • ε l) ≅
      MMP.CartierDivisor.sheaf (N • Hh))) :
    num3 W f M₁ M₂ ((Scheme.Modules.pullback g).obj (MMP.CartierDivisor.sheaf Hc)) =
      N * num3 W f M₁ M₂ ((Scheme.Modules.pullback g).obj (MMP.CartierDivisor.sheaf Hh)) -
        ∑ l ∈ s, (n l : ℚ) *
          num3 W f M₁ M₂ ((Scheme.Modules.pullback g).obj (MMP.CartierDivisor.sheaf (ε l))) := by
  unfold num3
  split_ifs with h
  · set L : Fin 3 → W.Modules :=
      ![M₁, M₂, (Scheme.Modules.pullback g).obj (MMP.CartierDivisor.sheaf Hc)]
    have hc : ∀ (L L' : Fin 3 → W.Modules)
        (hL : ∀ q, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 (L q))
        (hL' : ∀ q, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 (L' q)), L = L' →
        @sheafIntersectionNumber ℂ _ W W f _ (𝟙 W) _ 3 h L hL =
          @sheafIntersectionNumber ℂ _ W W f _ (𝟙 W) _ 3 h L' hL' := by
      rintro L _ hL hL' rfl; rfl
    have e : ∀ C : X.CartierDivisor,
        @sheafIntersectionNumber ℂ _ W W f _ (𝟙 W) _ 3 h
          ![M₁, M₂, (Scheme.Modules.pullback g).obj (MMP.CartierDivisor.sheaf C)] inv_vec3 =
        slotHom f (𝟙 W) 3 h L 2 g C := fun C => by
      rw [slotHom_apply]
      exact hc _ _ _ _ (funext fun t => by fin_cases t <;> rfl)
    have hsum := slotHom_eq_of_iso f (𝟙 W) 3 h L 2 g hAH
    rw [map_add, map_sum] at hsum
    simp only [map_nsmul, nsmul_eq_mul] at hsum
    rw [e Hc, e Hh]
    simp_rw [e]
    have := congrArg (fun z : ℤ => (z : ℚ)) hsum
    push_cast at this
    linarith
  · simp

/-- `(M · B · A)` for a rational combination `M = ∑ cⱼ Mⱼ` on a threefold. -/
theorem comb_one_pair_eq {W : Scheme.{0}} (f : W ⟶ Spec (.of ℂ)) [IsProper f] {s : ℕ}
    (c : Fin s → ℚ) (M : Fin s → W.Modules)
    [hM : ∀ j, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 (M j)] (B A : W.Modules)
    [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 B]
    [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 A]
    (hd : topologicalKrullDim W ≤ ((1 + 2 : ℕ) : WithBot ℕ∞)) :
    MMP.Mori.sheafCombinationIntersectionNumber ℂ f (𝟙 W) ℚ c M 1 ![B, A] hd =
      ∑ j, c j * num3 W f (M j) B A := by
  rw [MMP.Mori.sheafCombinationIntersectionNumber,
    ← (Equiv.funUnique (Fin 1) (Fin s)).symm.sum_comp]
  refine Fintype.sum_congr _ _ fun j => ?_
  rw [Fin.prod_univ_one, num3_eq _ _ _ _ hd]
  refine congrArg₂ (· * ·) rfl (congrArg (fun z : ℤ => (z : ℚ)) ?_)
  exact @sIN_congr_family ℂ _ W W f _ (𝟙 W) _ 3 hd _ _
    (MMP.Mori.isInvertible_finAppend (a := 1) (b := 2) _ _) inv_vec3
    (funext fun t => by fin_cases t <;> rfl)

end Num

section Class

attribute [local instance] MMP.Fold06.ThmMmpConductorIsolatedPointAlgebraicKernel.inv_vec3

/-- **Divisors of class zero have zero intersection numbers.** On a smooth projective complex
threefold `W` with Cartier divisors `π_P` cutting out the prime divisors `P`, a `ℚ`-divisor
`x = ∑_P x_P P` with `[x] = 0` in `H_4(W, ℚ)` has `∑_P x_P (π_P · L₂ · L₃) = 0` for all invertible
modules `L₂`, `L₃`. -/
theorem linearCombination_num3_eq_zero_of_divisorClass_eq_zero {W : Scheme.{0}}
    [W.Over (Spec (.of ℂ))] [IsComplexScheme W] [IsLocallyNoetherian W] [IsNormal W]
    (hWp : Mori.IsProjectiveVariety ℂ (W ↘ Spec (.of ℂ))) (hW : topologicalKrullDim W = 3)
    (hsm : Mori.IsSmoothScheme (W ↘ Spec (.of ℂ)))
    (π : Mori.PrimeDivisor W → W.CartierDivisor)
    (hπ : ∀ P, MMP.Intersection.IsWeilDivisorOfCartier (π P) (Finsupp.single P 1))
    (L₂ L₃ : W.Modules) [h₂ : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L₂]
    [h₃ : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L₃]
    (x : QDivisor W) (hx : MMP.Chow.divisorClass W x = 0) :
    haveI := (MMP.Mori.isProjectiveVariety_iff _ _).1 hWp
    haveI : IsProper (W ↘ Spec (.of ℂ)) := isProper_of_isProjectiveMorphism _ this.2
    Finsupp.linearCombination ℚ (fun P => num3 W (W ↘ Spec (.of ℂ))
      (MMP.CartierDivisor.sheaf (π P)) L₂ L₃) x = 0 := by
  classical
  have hWv := (MMP.Mori.isProjectiveVariety_iff _ _).1 hWp
  haveI : IsProper (W ↘ Spec (.of ℂ)) := isProper_of_isProjectiveMorphism _ hWv.2
  obtain ⟨A, hAi, hA⟩ := MMP.Chow.exists_isAmple_of_isProjective (W ↘ Spec (.of ℂ)) hWv.2
  have h3 : topologicalKrullDim W = ((2 + 1 : ℕ) : WithBot ℕ∞) := by rw [hW]; rfl
  have h3' : topologicalKrullDim W = ((1 + 1 + 1 : ℕ) : WithBot ℕ∞) := by rw [hW]; rfl
  haveI hK : ∀ j : Fin 1, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2
      ((fun _ : Fin 1 => L₂) j) := fun _ => h₂
  -- the cap with `c₁(π_P)` first
  let a : Mori.PrimeDivisor W →
      Stacks.Chow.chowGroup (Stacks.Chow.fieldChowSituation ℂ) (W ↘ Spec (.of ℂ))
        ((1 + 1 : ℕ) : ℤ) := fun P =>
    Stacks.Chow.firstChernClassCapChow (Stacks.Chow.fieldChowSituation ℂ) ((1 + 1 : ℕ) : ℤ)
      (W ↘ Spec (.of ℂ)) (MMP.CartierDivisor.sheaf (π P))
      (Stacks.Chow.fundamentalChowClass (Stacks.Chow.fieldChowSituation ℂ) (W ↘ Spec (.of ℂ))
        ((1 + 1 + 1 : ℕ) : ℤ))
  have hP : ∀ P, num3 W (W ↘ Spec (.of ℂ)) (MMP.CartierDivisor.sheaf (π P)) L₂ L₃ =
      (AlgebraicGeometry.capDegree ℂ (W ↘ Spec (.of ℂ))
        (Fin.snoc (fun _ : Fin 1 => L₂) L₃ : Fin (1 + 1) → W.Modules) (a P) : ℚ) := fun P =>
    (num3_eq_capDegree_firstChernClassCapChow_fundamentalChowClass _ L₂ L₃ h3').trans
      (congrArg (Int.cast : ℤ → ℚ) (MMP.Chow.capDegree_congr _ rfl rfl))
  have hcl : ∀ P, MMP.Chow.chowCycleClass ℚ (1 + 1) (a P) =
      MMP.Chow.divisorClass W (Finsupp.single P 1) := fun P =>
    MMP.Chow.chowCycleClass_firstChernClassCapChow_fundamentalChowClass hWp hsm h3 P (π P) (hπ P)
  obtain ⟨n₀, hn₀, c, hc⟩ := exists_nat_smul_eq_mapRange (fun _ : Unit => x)
  have hc' := hc ()
  have hb : ∑ P ∈ (c ()).support, c () P • MMP.Chow.chowCycleClass ℚ (1 + 1) (a P) = 0 := by
    simp only [hcl]
    have : ∑ P ∈ (c ()).support, c () P • MMP.Chow.divisorClass W (Finsupp.single P 1) =
        MMP.Chow.divisorClass W (((c ()).mapRange (Int.cast : ℤ → ℚ) Int.cast_zero)) := by
      conv_rhs => rw [← Finsupp.sum_single ((c ()).mapRange (Int.cast : ℤ → ℚ) Int.cast_zero)]
      rw [Finsupp.sum_mapRange_index (fun _ => Finsupp.single_zero _), Finsupp.sum, map_sum]
      refine Finset.sum_congr rfl fun P _ => ?_
      rw [← Int.cast_smul_eq_zsmul ℚ, ← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [this, hc', map_smul, hx, smul_zero]
  have hq : ∑ P ∈ (c ()).support, (c () P : ℚ) *
      (AlgebraicGeometry.capDegree ℂ (W ↘ Spec (.of ℂ))
        (Fin.snoc (fun _ : Fin 1 => L₂) L₃ : Fin (1 + 1) → W.Modules) (a P) : ℚ) = 0 :=
    sum_intCast_mul_capDegree_eq_zero_of_isAmple A hA
      (Fin.snoc (fun _ : Fin 1 => L₂) L₃ : Fin (1 + 1) → W.Modules) _ _ a hb
  rw [sum_support_mul_eq (c ()) x hn₀ hc'] at hq
  have hn : (n₀ : ℚ) ≠ 0 := by exact_mod_cast hn₀
  rw [show (fun P => num3 W (W ↘ Spec (.of ℂ)) (MMP.CartierDivisor.sheaf (π P)) L₂ L₃) =
    fun P => (AlgebraicGeometry.capDegree ℂ (W ↘ Spec (.of ℂ))
      (Fin.snoc (fun _ : Fin 1 => L₂) L₃ : Fin (1 + 1) → W.Modules) (a P) : ℚ) from funext hP]
  exact (mul_eq_zero.1 hq).resolve_left hn

end Class

section Forms

attribute [local instance] MMP.Fold06.ThmMmpConductorIsolatedPointAlgebraicKernel.inv_vec1
  MMP.Fold06.ThmMmpConductorIsolatedPointAlgebraicKernel.inv_vec2
  MMP.Fold06.ThmMmpConductorIsolatedPointAlgebraicKernel.inv_vec3

variable {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsProper (Z ↘ Spec (.of ℂ))] [IsIntegral Z]
  {F : Divisor Z} [Fintype (DoubleSurface F)]

omit [Z.Over (Spec (.of ℂ))] [IsProper (Z ↘ Spec (.of ℂ))] [IsIntegral Z]
  [Fintype (DoubleSurface F)] in
/-- With `D = ∑ₗ nₗ Fₗ`, the divisor `-D` satisfies the triviality hypothesis of the point-image
case: `𝒪_Z(-D + ∑ₗ nₗ εₗ) ≅ 𝒪_Z`. -/
theorem nonempty_sheaf_neg_sum_add_sum_iso (ε : F.support → Z.CartierDivisor)
    (n : F.support → ℕ) :
    Nonempty (CartierDivisor.sheaf (-(∑ l : F.support, n l • ε l) + ∑ l : F.support, n l • ε l) ≅
      SheafOfModules.unit Z.ringCatSheaf) := by
  rw [neg_add_cancel]
  exact MMP.Mori.TwistGrowth.nonempty_sheaf_zero_iso

/-- **The self-intersection form of `Fᵢ|_{Fᵢ}` with `D = N H - A`.** If
`𝒪_Z(A + ∑ₗ nₗ εₗ) ≅ 𝒪_Z(N H)`, then
`-nᵢ (x² · Fᵢ) = (x² · A) - N (x² · H) + ∑_{S ⊆ Fᵢ} n_{S'} (x|_S)²` on every component. -/
theorem neg_mul_bilin_bG_eq_of_iso [DecidableEq F.support] (hB : F.IsSNC (Z ↘ Spec (.of ℂ)))
    (hdim : topologicalKrullDim Z = 4) (hvar : Mori.IsVariety ℂ (Z ↘ Spec (.of ℂ)))
    (hsm : Mori.IsSmoothScheme (Z ↘ Spec (.of ℂ))) (ε : F.support → Z.CartierDivisor)
    (hε : ∀ i, MMP.Intersection.IsWeilDivisorOfCartier (ε i) (Finsupp.single i.1 1))
    (π : ∀ i : F.support, Mori.PrimeDivisor i.1.idealSheaf.subscheme →
      i.1.idealSheaf.subscheme.CartierDivisor)
    (Hc Hh : Z.CartierDivisor) (n : F.support → ℕ) (N : ℕ)
    (hAH : Nonempty (MMP.CartierDivisor.sheaf (Hc + ∑ l : F.support, n l • ε l) ≅
      MMP.CartierDivisor.sheaf (N • Hh)))
    (x : ∀ i : F.support, QDivisor i.1.idealSheaf.subscheme) (i : F.support) :
    -(n i : ℚ) * bilin (bG π ε i) (x i) (x i) =
      bilin (bB π Hc i) (x i) (x i) - (N : ℚ) * bilin (bB π Hh i) (x i) (x i) +
      ∑ σ : DoubleSurface F, if σ.fstComponent = i then
        (n σ.sndComponent : ℚ) * bilin (bU π σ) (x σ.fstComponent) (x σ.fstComponent)
        else 0 := by
  have h0 := nonempty_sheaf_neg_sum_add_sum_iso ε n
  have h := bilin_bG_eq hB hdim π hvar hsm ε hε _ n h0 x i
  have hb : bB π (-(∑ l : F.support, n l • ε l)) i =
      fun P Q => bB π Hc i P Q + (-(N : ℚ)) * bB π Hh i P Q := by
    funext P Q
    unfold bB
    rw [num3_pullback_eq_of_iso _ _ _ _ Finset.univ Hc Hh ε n N hAH,
      num3_A_eq ε _ n h0]
    ring
  rw [hb, bilin_add, bilin_smul] at h
  rw [h]
  ring

/-- **The linear form of `Fᵢ|_{Fᵢ}` against `A` with `D = N H - A`.** If
`𝒪_Z(A + ∑ₗ nₗ εₗ) ≅ 𝒪_Z(N H)`, then
`-nᵢ (x · A · Fᵢ) = (x · A²) - N (x · H · A) + ∑_{S ⊆ Fᵢ} n_{S'} (x|_S · A|_S)` on every
component. -/
theorem neg_mul_lin_bGA_eq_of_iso [DecidableEq F.support] (hB : F.IsSNC (Z ↘ Spec (.of ℂ)))
    (hdim : topologicalKrullDim Z = 4) (hvar : Mori.IsVariety ℂ (Z ↘ Spec (.of ℂ)))
    (hsm : Mori.IsSmoothScheme (Z ↘ Spec (.of ℂ))) (ε : F.support → Z.CartierDivisor)
    (hε : ∀ i, MMP.Intersection.IsWeilDivisorOfCartier (ε i) (Finsupp.single i.1 1))
    (π : ∀ i : F.support, Mori.PrimeDivisor i.1.idealSheaf.subscheme →
      i.1.idealSheaf.subscheme.CartierDivisor)
    (Hc Hh : Z.CartierDivisor) (n : F.support → ℕ) (N : ℕ)
    (hAH : Nonempty (MMP.CartierDivisor.sheaf (Hc + ∑ l : F.support, n l • ε l) ≅
      MMP.CartierDivisor.sheaf (N • Hh)))
    (x : ∀ i : F.support, QDivisor i.1.idealSheaf.subscheme) (i : F.support) :
    -(n i : ℚ) * Finsupp.linearCombination ℚ (bGA π ε Hc i) (x i) =
      Finsupp.linearCombination ℚ (bLam π Hc i) (x i) -
        (N : ℚ) * Finsupp.linearCombination ℚ (bGA π (fun _ => Hh) Hc i) (x i) +
      ∑ σ : DoubleSurface F, if σ.fstComponent = i then
        (n σ.sndComponent : ℚ) * Finsupp.linearCombination ℚ (bUA π Hc σ) (x σ.fstComponent)
        else 0 := by
  classical
  have h0 := nonempty_sheaf_neg_sum_add_sum_iso ε n
  rw [← lin_smul]
  have hrel : ∀ P, -(n i : ℚ) * bGA π ε Hc i P =
      (bLam π Hc i P + (-(N : ℚ)) * bGA π (fun _ => Hh) Hc i P) +
      ∑ σ : DoubleSurface F, if h : σ.fst = i.1 then (n (sndS F σ) : ℚ) *
        num2 (dsIdeal σ).subscheme ((dsIdeal σ).subschemeι ≫ Z ↘ Spec (.of ℂ))
          ((Scheme.Modules.pullback (sιOf σ h)).obj (MMP.CartierDivisor.sheaf (π i P)))
          ((Scheme.Modules.pullback (sιOf σ h)).obj
            ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj
              (MMP.CartierDivisor.sheaf Hc))) else 0 := by
    intro P
    have e1 := num3_self_eq hB hdim hvar hsm ε hε _ n h0 i (MMP.CartierDivisor.sheaf (π i P))
      ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hc))
    rw [num3_A_eq ε _ n h0] at e1
    have e2 := num3_pullback_eq_of_iso (i.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ))
      i.1.idealSheaf.subschemeι (MMP.CartierDivisor.sheaf (π i P))
      ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hc))
      Finset.univ Hc Hh ε n N hAH
    unfold bGA bLam
    rw [e1, e2]
    ring
  rw [show (fun P => -(n i : ℚ) * bGA π ε Hc i P) = _ from funext hrel, lin_add, lin_add,
    lin_smul, lin_sum]
  rw [sub_eq_add_neg, ← neg_mul]
  refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun σ _ => ?_)
  by_cases h : σ.fstComponent = i
  · subst h
    simp only [↓reduceIte, ↓reduceDIte]
    rw [lin_smul]
    refine congrArg (fun z => (n (sndS F σ) : ℚ) * z)
      (congrArg (fun b => Finsupp.linearCombination ℚ b (x σ.fstComponent))
        (funext fun P => ?_))
    exact num2_congr _ _ _ _ _ ⟨Iso.refl _⟩
      ⟨(Scheme.Modules.pullbackComp (sι σ) σ.fst.idealSheaf.subschemeι).app _ ≪≫
        (Scheme.Modules.pullbackCongr (sι_comp σ)).app _⟩
  · have h' : ¬ σ.fst = i.1 := fun e => h (Subtype.ext e)
    simp only [h, h', ↓reduceIte, ↓reduceDIte]
    simp [Finsupp.linearCombination_apply]

/-- **The two identities of a family with zero ambient class**, for `L - Z(a)` with `a` an
oriented system: the intersection with `A · Fᵢ` and the self-intersection. -/
theorem kernel_identities_sub_surfaceCoefficientDivisor [IsComplexScheme Z]
    [DecidableEq F.support] (hB : F.IsSNC (Z ↘ Spec (.of ℂ)))
    (hdim : topologicalKrullDim Z = 4) (hvar : Mori.IsVariety ℂ (Z ↘ Spec (.of ℂ)))
    (hsm : Mori.IsSmoothScheme (Z ↘ Spec (.of ℂ))) (ε : F.support → Z.CartierDivisor)
    (hε : ∀ i, MMP.Intersection.IsWeilDivisorOfCartier (ε i) (Finsupp.single i.1 1))
    (π : ∀ i : F.support, Mori.PrimeDivisor i.1.idealSheaf.subscheme →
      i.1.idealSheaf.subscheme.CartierDivisor)
    (hπ : ∀ i P, MMP.Intersection.IsWeilDivisorOfCartier (π i P) (Finsupp.single P 1))
    (hZp : IsProjectiveMorphism (Z ↘ Spec (.of ℂ)))
    (Hc : Z.CartierDivisor) (pt : DoubleSurface F → Prop)
    (Zl : (DoubleSurface F → ℚ) →ₗ[ℚ] ∀ i : F.support, QDivisor i.1.idealSheaf.subscheme)
    (hZl : ∀ a i, Zl a i = surfaceCoefficientDivisor a i.1)
    (L : ∀ i : F.support, QDivisor i.1.idealSheaf.subscheme)
    (hL : ∑ i : F.support, componentHomologyMap i.1 4
      (MMP.Chow.divisorClass i.1.idealSheaf.subscheme (L i)) = 0) :
    ∀ a ∈ orientedSurfaceCoefficients F, (∀ σ, ¬ pt σ → a σ = 0) →
      (∀ i, Finsupp.linearCombination ℚ (bGA π ε Hc i) ((L - Zl a) i) +
        ∑ σ : DoubleSurface F, (if σ.sndComponent = i then
          Finsupp.linearCombination ℚ (bUA π Hc σ) ((L - Zl a) σ.fstComponent) else 0) = 0) ∧
      ∑ i, bilin (bG π ε i) ((L - Zl a) i) ((L - Zl a) i) + ∑ σ : DoubleSurface F,
        bilin (bC π σ) ((L - Zl a) σ.fstComponent) ((L - Zl a) σ.sndComponent) = 0 := by
  intro a ha _
  refine kernel_identities hB hdim hvar hsm ε hε π hπ hZp Hc (L - Zl a) ?_
  simp only [Pi.sub_apply, map_sub, Finset.sum_sub_distrib, hZl]
  rw [hL,
    ConductorBlowup.sum_componentHomologyMap_divisorClass_eq_zero_of_topologicalKrullDim_eq_four
      hdim F a ha, sub_zero]

end Forms

section ClassForms

attribute [local instance] MMP.Fold06.ThmMmpConductorIsolatedPointAlgebraicKernel.inv_vec3

variable {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z]
  [IsProper (Z ↘ Spec (.of ℂ))] [IsIntegral Z] {F : Divisor Z}

/-- On a smooth component `Fᵢ` of a projective `Z`, the divisors of class zero are numerically
trivial against any two invertible modules. -/
private theorem linearCombination_num3_pullback_eq_zero (hB : F.IsSNC (Z ↘ Spec (.of ℂ)))
    (hdim : topologicalKrullDim Z = 4) (hZp : IsProjectiveMorphism (Z ↘ Spec (.of ℂ)))
    (i : F.support)
    (π : Mori.PrimeDivisor i.1.idealSheaf.subscheme → i.1.idealSheaf.subscheme.CartierDivisor)
    (hπ : ∀ P, MMP.Intersection.IsWeilDivisorOfCartier (π P) (Finsupp.single P 1))
    (L₂ L₃ : i.1.idealSheaf.subscheme.Modules)
    [SheafOfModules.IsInvertible i.1.idealSheaf.subscheme.presheaf
      i.1.idealSheaf.subscheme.ringCatSheaf.2 L₂]
    [SheafOfModules.IsInvertible i.1.idealSheaf.subscheme.presheaf
      i.1.idealSheaf.subscheme.ringCatSheaf.2 L₃]
    (k : QDivisor i.1.idealSheaf.subscheme)
    (hk : MMP.Chow.divisorClass i.1.idealSheaf.subscheme k = 0) :
    Finsupp.linearCombination ℚ (fun P => num3 i.1.idealSheaf.subscheme
      (i.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ))
      (MMP.CartierDivisor.sheaf (π P)) L₂ L₃) k = 0 := by
  have : IsIntegral i.1.idealSheaf.subscheme := i.1.integral
  have : IsComplexScheme i.1.idealSheaf.subscheme :=
    IsComplexScheme.of_isClosedImmersion i.1.idealSheaf.subschemeι
  have hsmX : Mori.IsSmoothScheme (i.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) := hB.1 i.1 i.2
  have : Smooth (i.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) := (MMP.Mori.isSmoothScheme_iff _).1 hsmX
  have hvX : Mori.IsVariety ℂ (i.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) :=
    (⟨⟩ : AlgebraicGeometry.IsVariety ℂ (i.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)))
  have hW : Mori.IsProjectiveVariety ℂ (i.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) :=
    (MMP.Mori.isProjectiveVariety_iff _ _).2
      ⟨hvX, isProjectiveMorphism_isClosedImmersion_comp _ _ hZp⟩
  have : IsLocallyNoetherian i.1.idealSheaf.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (i.1.idealSheaf.subscheme ↘ Spec (.of ℂ))
  have : IsNormal i.1.idealSheaf.subscheme :=
    isNormal_of_smooth_over_field (i.1.idealSheaf.subscheme ↘ Spec (.of ℂ))
  exact linearCombination_num3_eq_zero_of_divisorClass_eq_zero hW
    (topologicalKrullDim_component hdim i) hsmX π hπ L₂ L₃ k hk

/-- **Divisors of class zero on a component are orthogonal to `A · Fᵢ`.** -/
theorem linearCombination_bGA_eq_zero_of_mem_ker (hB : F.IsSNC (Z ↘ Spec (.of ℂ)))
    (hdim : topologicalKrullDim Z = 4) (hZp : IsProjectiveMorphism (Z ↘ Spec (.of ℂ)))
    (ε : F.support → Z.CartierDivisor)
    (π : ∀ i : F.support, Mori.PrimeDivisor i.1.idealSheaf.subscheme →
      i.1.idealSheaf.subscheme.CartierDivisor)
    (hπ : ∀ i P, MMP.Intersection.IsWeilDivisorOfCartier (π i P) (Finsupp.single P 1))
    (Hc : Z.CartierDivisor) :
    ∀ i : F.support, ∀ k ∈ LinearMap.ker (MMP.Chow.divisorClass i.1.idealSheaf.subscheme),
      Finsupp.linearCombination ℚ (bGA π ε Hc i) k = 0 := by
  intro i k hk
  exact linearCombination_num3_pullback_eq_zero hB hdim hZp i (π i) (hπ i) _ _ k
    (LinearMap.mem_ker.1 hk)

/-- **Divisors of class zero on a component are orthogonal to `A|_S` on its double surfaces.** -/
theorem linearCombination_bUA_eq_zero_of_mem_ker (hB : F.IsSNC (Z ↘ Spec (.of ℂ)))
    (hdim : topologicalKrullDim Z = 4) (hZp : IsProjectiveMorphism (Z ↘ Spec (.of ℂ)))
    (π : ∀ i : F.support, Mori.PrimeDivisor i.1.idealSheaf.subscheme →
      i.1.idealSheaf.subscheme.CartierDivisor)
    (hπ : ∀ i P, MMP.Intersection.IsWeilDivisorOfCartier (π i P) (Finsupp.single P 1))
    (Hc : Z.CartierDivisor) :
    ∀ σ : DoubleSurface F, ∀ k ∈ LinearMap.ker (MMP.Chow.divisorClass σ.fst.idealSheaf.subscheme),
      Finsupp.linearCombination ℚ (bUA π Hc σ) k = 0 := by
  intro σ k hk
  rw [show bUA π Hc σ = fun P => bB π Hc (fstS F σ) P (rho hB σ) from
    funext fun P => bUA_eq_bB hB hdim π hπ Hc σ P]
  exact linearCombination_num3_pullback_eq_zero hB hdim hZp (fstS F σ) (π (fstS F σ))
    (hπ (fstS F σ)) _ _ k (LinearMap.mem_ker.1 hk)

end ClassForms

section Index

attribute [local instance] MMP.Fold06.ThmMmpConductorIsolatedPointAlgebraicKernel.inv_vec1
  MMP.Fold06.ThmMmpConductorIsolatedPointAlgebraicKernel.inv_vec2
  MMP.Fold06.ThmMmpConductorIsolatedPointAlgebraicKernel.inv_vec3

variable {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z]
  [IsProper (Z ↘ Spec (.of ℂ))] [IsIntegral Z] {F : Divisor Z}

open MMP.Analytic in
/-- **The isotropic threefold index theorem on the curve components.** Let `Fᵢ` be a component
on which `H|_{Fᵢ}` is isotropic (`H|_{Fᵢ}² · A = 0`, `H|_{Fᵢ} · A² > 0`), with `A|_{Fᵢ}` ample,
and `hᵢ` a `ℚ`-divisor on `Fᵢ` with rational first Chern class `c₁(H|_{Fᵢ})`. If
`x · H · A = 0` then `x² · A ≤ 0`, and equality forces `[x - c hᵢ] = 0` in `H_4(Fᵢ, ℚ)` for some
`c ∈ ℚ`. -/
theorem threefold_index_of_isotropic (hB : F.IsSNC (Z ↘ Spec (.of ℂ)))
    (hdim : topologicalKrullDim Z = 4)
    (π : ∀ i : F.support, Mori.PrimeDivisor i.1.idealSheaf.subscheme →
      i.1.idealSheaf.subscheme.CartierDivisor)
    (hπ : ∀ i P, MMP.Intersection.IsWeilDivisorOfCartier (π i P) (Finsupp.single P 1))
    (hZp : IsProjectiveMorphism (Z ↘ Spec (.of ℂ))) (Hc Hh : Z.CartierDivisor)
    (cur : F.support → Prop) (hv : ∀ i : F.support, QDivisor i.1.idealSheaf.subscheme)
    (hAmp : ∀ i : F.support, Stacks.Ample.IsAmple i.1.idealSheaf.subscheme
      ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hc)))
    (hhv : ∀ i, cur i → Finsupp.linearCombination ℚ (fun Q =>
        singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
          (algebraicFirstChernClass (MMP.CartierDivisor.sheaf (π i Q)))) (hv i) =
      singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass
        ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hh))))
    {Y : Scheme.{0}} (pY : Y ⟶ Spec (.of ℂ)) [IsProper pY] (r : Z ⟶ Y)
    (hr : r ≫ pY = Z ↘ Spec (.of ℂ)) (MY : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 MY] (hM : Stacks.Ample.IsAmple Y MY)
    (eH : Nonempty (MMP.CartierDivisor.sheaf Hh ≅ (Scheme.Modules.pullback r).obj MY))
    (hcur : ∀ i, cur i →
      topologicalKrullDim (Set.range (i.1.idealSheaf.subschemeι ≫ r).base) = 1) :
    ∀ i, cur i → ∀ x : QDivisor i.1.idealSheaf.subscheme,
      Finsupp.linearCombination ℚ (bGA π (fun _ => Hh) Hc i) x = 0 →
      bilin (bB π Hh i) x x = 0 →
      bilin (bB π Hc i) x x ≤ 0 ∧ (bilin (bB π Hc i) x x = 0 →
        ∃ c : ℚ, x - c • hv i ∈
          LinearMap.ker (MMP.Chow.divisorClass i.1.idealSheaf.subscheme)) := by
  classical
  intro i hi x hx _
  have : IsIntegral i.1.idealSheaf.subscheme := i.1.integral
  have hvX : MMP.Mori.IsVariety ℂ (i.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) :=
    (⟨⟩ : AlgebraicGeometry.IsVariety ℂ (i.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)))
  have hsmX : MMP.Mori.IsSmoothScheme (i.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) := hB.1 i.1 i.2
  have : Smooth (i.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) :=
    (MMP.Mori.isSmoothScheme_iff _).1 hsmX
  have hW : MMP.Mori.IsProjectiveVariety ℂ (i.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) :=
    (MMP.Mori.isProjectiveVariety_iff _ _).2
      ⟨hvX, isProjectiveMorphism_isClosedImmersion_comp _ _ hZp⟩
  have hdim3 := topologicalKrullDim_component hdim i
  set A := (Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hc)
  set Hi := (Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hh)
  set e := x.support.equivFin
  let P : Fin x.support.card → Mori.PrimeDivisor i.1.idealSheaf.subscheme :=
    fun j => (e.symm j).1
  let l : Fin x.support.card → ℚ := fun j => x (P j)
  let L : Fin x.support.card → i.1.idealSheaf.subscheme.Modules :=
    fun j => MMP.CartierDivisor.sheaf (π i (P j))
  have hreidx : ∀ {N : Type} [AddCommMonoid N]
      (g : Mori.PrimeDivisor i.1.idealSheaf.subscheme → N),
      ∑ j, g (P j) = ∑ Q ∈ x.support, g Q := fun g => by
    rw [← Finset.sum_coe_sort x.support]
    exact Fintype.sum_equiv e.symm _ _ fun j => rfl
  let h1 : Fin 1 → ℚ := fun _ => 1
  let H1 : Fin 1 → i.1.idealSheaf.subscheme.Modules := fun _ => Hi
  have key := MMP.Mori.sheafCombinationIntersectionNumber_two_mul_nonpos_of_isotropic
    hW hdim3 A (hAmp i) h1 H1 l L
  have k1 : MMP.Mori.sheafCombinationIntersectionNumber ℂ
      (i.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) (𝟙 _) ℚ h1 H1 1 ![A, A]
      (by rw [hdim3]; rfl) = num3 i.1.idealSheaf.subscheme
        (i.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)) Hi A A := by
    rw [comb_one_eq, Fin.sum_univ_one, one_mul]; rfl
  have k2 : MMP.Mori.sheafCombinationIntersectionNumber ℂ
      (i.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) (𝟙 _) ℚ h1 H1 2 ![A]
      (by rw [hdim3]; rfl) = num3 i.1.idealSheaf.subscheme
        (i.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)) Hi Hi A := by
    rw [comb_two_eq, Fin.sum_univ_one, Fin.sum_univ_one, one_mul, one_mul]; rfl
  have k3 : ∑ j, h1 j * MMP.Mori.sheafCombinationIntersectionNumber ℂ
      (i.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) (𝟙 _) ℚ l L 1 ![H1 j, A]
      (by rw [hdim3]; rfl) = Finsupp.linearCombination ℚ (bGA π (fun _ => Hh) Hc i) x := by
    rw [Fin.sum_univ_one, one_mul, comb_one_pair_eq, Finsupp.linearCombination_apply,
      Finsupp.sum]
    simp only [smul_eq_mul]
    rw [← hreidx fun Q => x Q * bGA π (fun _ => Hh) Hc i Q]
    refine Finset.sum_congr rfl fun j _ => congrArg (fun t => l j * t) ?_
    unfold bGA
    exact num3_comm23 _ _ _ _
  have kl : MMP.Mori.sheafCombinationIntersectionNumber ℂ
      (i.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) (𝟙 _) ℚ l L 2 ![A] (by rw [hdim3]; rfl) =
      bilin (bB π Hc i) x x := by
    rw [comb_two_eq, bilin_apply]
    rw [← hreidx fun Q => ∑ Q' ∈ x.support, x Q * x Q' * bB π Hc i Q Q']
    refine Finset.sum_congr rfl fun j _ => ?_
    exact hreidx fun Q' => x (P j) * x Q' * bB π Hc i (P j) Q'
  have eHi : Nonempty (Hi ≅ (Scheme.Modules.pullback (i.1.idealSheaf.subschemeι ≫ r)).obj MY) :=
    ⟨(Scheme.Modules.pullback _).mapIso eH.some ≪≫ (Scheme.Modules.pullbackComp _ _).app MY⟩
  have hu : (i.1.idealSheaf.subschemeι ≫ r) ≫ pY =
      i.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ) := by
    rw [Category.assoc, hr]
  have him : topologicalKrullDim (Set.range
      (𝟙 i.1.idealSheaf.subscheme ≫ i.1.idealSheaf.subschemeι ≫ r).base) = 1 := by
    rw [Category.id_comp]; exact hcur i hi
  have hHA : 0 < num3 i.1.idealSheaf.subscheme
      (i.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)) Hi A A := by
    rw [num3_congr _ _ _ _ _ _ _ eHi ⟨Iso.refl _⟩ ⟨Iso.refl _⟩, num3_eq _ _ _ _ hdim3.le]
    have := sheafIntersectionNumber_pullback_isAmple_isAmple_pos ℂ
      (i.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)) pY (i.1.idealSheaf.subschemeι ≫ r) hu MY A
      (𝟙 _) hM (hAmp i) (by rw [hdim3]; rfl) (by rw [him]; exact zero_lt_one)
    exact_mod_cast this
  have hHH : num3 i.1.idealSheaf.subscheme
      (i.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)) Hi Hi A = 0 := by
    rw [num3_congr _ _ _ _ _ _ _ eHi eHi ⟨Iso.refl _⟩, num3_eq _ _ _ _ hdim3.le]
    have := sheafIntersectionNumber_pullback_pullback_isAmple_eq_zero ℂ
      (i.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)) pY (i.1.idealSheaf.subschemeι ≫ r) hu MY A
      (𝟙 _) (hAmp i) hdim3.le him.le
    exact_mod_cast this
  obtain ⟨hle, -, heq⟩ := key (by rw [k1]; exact hHA) (k2.trans hHH) (k3.trans hx)
  rw [kl] at hle
  refine ⟨hle, fun h0 => ?_⟩
  have hc := heq (kl.trans h0)
  set c := MMP.Mori.sheafCombinationIntersectionNumber ℂ
      (i.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) (𝟙 _) ℚ l L 1 ![A, A] (by rw [hdim3]; rfl) /
    MMP.Mori.sheafCombinationIntersectionNumber ℂ
      (i.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) (𝟙 _) ℚ h1 H1 1 ![A, A] (by rw [hdim3]; rfl)
  refine ⟨c, ?_⟩
  have : IsLocallyNoetherian i.1.idealSheaf.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (i.1.idealSheaf.subscheme ↘ Spec (.of ℂ))
  have : IsNormal i.1.idealSheaf.subscheme :=
    isNormal_of_smooth_over_field (i.1.idealSheaf.subscheme ↘ Spec (.of ℂ))
  have : IsComplexScheme i.1.idealSheaf.subscheme :=
    IsComplexScheme.of_isClosedImmersion i.1.idealSheaf.subschemeι
  refine LinearMap.mem_ker.2
    (divisorClass_eq_zero_of_sum_smul_mapCoeff_algebraicFirstChernClass_eq_zero hW hsmX hdim3
      (π i) (hπ i) _ ?_)
  rw [map_sub, map_smul, hhv i hi, Finsupp.linearCombination_apply, Finsupp.sum,
    ← hreidx fun Q => x Q • singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
      (algebraicFirstChernClass (MMP.CartierDivisor.sheaf (π i Q)))]
  simpa [h1, H1, Fin.sum_univ_one] using hc

/-- **The isotropic surface index theorem on the curve edges.** Let `S` be a double surface on
which `H|_S` is isotropic (`(H|_S)² = 0`, `H|_S · A|_S > 0`), with `A|_S` ample. For `x` on the
first component and `y` on the second with `x|_S · H|_S = 0 = y|_S · H|_S`:
`((x - y)|_S)² ≤ 0`. -/
theorem surface_index_of_isotropic (hB : F.IsSNC (Z ↘ Spec (.of ℂ)))
    (hdim : topologicalKrullDim Z = 4)
    (π : ∀ i : F.support, Mori.PrimeDivisor i.1.idealSheaf.subscheme →
      i.1.idealSheaf.subscheme.CartierDivisor)
    (hZp : IsProjectiveMorphism (Z ↘ Spec (.of ℂ))) (Hc Hh : Z.CartierDivisor)
    (pt : DoubleSurface F → Prop)
    (hAmpS : ∀ σ : DoubleSurface F, Stacks.Ample.IsAmple (dsIdeal σ).subscheme
      ((Scheme.Modules.pullback (dsIdeal σ).subschemeι).obj (MMP.CartierDivisor.sheaf Hc)))
    {Y : Scheme.{0}} (pY : Y ⟶ Spec (.of ℂ)) [IsProper pY] (r : Z ⟶ Y)
    (hr : r ≫ pY = Z ↘ Spec (.of ℂ)) (MY : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 MY] (hM : Stacks.Ample.IsAmple Y MY)
    (eH : Nonempty (MMP.CartierDivisor.sheaf Hh ≅ (Scheme.Modules.pullback r).obj MY))
    (hcur : ∀ σ : DoubleSurface F, ¬ pt σ →
      topologicalKrullDim (Set.range ((dsIdeal σ).subschemeι ≫ r).base) = 1) :
    ∀ σ : DoubleSurface F, ¬ pt σ → ∀ (x : QDivisor σ.fst.idealSheaf.subscheme)
      (y : QDivisor σ.snd.idealSheaf.subscheme),
      Finsupp.linearCombination ℚ (bUA π Hh σ) x = 0 →
      Finsupp.linearCombination ℚ (bUA π Hh σ.swap) y = 0 →
      bilin (bU π σ) x x - 2 * bilin (bC π σ) x y + bilin (bU π σ.swap) y y ≤ 0 := by
  classical
  intro σ hσ x y hx hy
  have : IsIntegral (dsIdeal σ).subscheme := isIntegral_dsIdeal hB σ
  have : Smooth ((dsIdeal σ).subscheme ↘ Spec (.of ℂ)) := smooth_dsIdeal hB σ
  have hvS : MMP.Mori.IsVariety ℂ ((dsIdeal σ).subscheme ↘ Spec (.of ℂ)) :=
    (⟨⟩ : AlgebraicGeometry.IsVariety ℂ ((dsIdeal σ).subschemeι ≫ Z ↘ Spec (.of ℂ)))
  have hW : MMP.Mori.IsProjectiveVariety ℂ ((dsIdeal σ).subscheme ↘ Spec (.of ℂ)) :=
    (MMP.Mori.isProjectiveVariety_iff _ _).2
      ⟨hvS, isProjectiveMorphism_isClosedImmersion_comp _ _ hZp⟩
  have hdim2 := topologicalKrullDim_dsIdeal hB hdim σ
  set A := (Scheme.Modules.pullback (dsIdeal σ).subschemeι).obj (MMP.CartierDivisor.sheaf Hc)
  set HS := (Scheme.Modules.pullback (dsIdeal σ).subschemeι).obj (MMP.CartierDivisor.sheaf Hh)
  set e₁ := x.support.equivFin
  set e₂ := y.support.equivFin
  let P₁ : Fin x.support.card → Mori.PrimeDivisor σ.fst.idealSheaf.subscheme :=
    fun j => (e₁.symm j).1
  let P₂ : Fin y.support.card → Mori.PrimeDivisor σ.snd.idealSheaf.subscheme :=
    fun j => (e₂.symm j).1
  have hre₁ : ∀ {N : Type} [AddCommMonoid N]
      (g : Mori.PrimeDivisor σ.fst.idealSheaf.subscheme → N),
      ∑ j, g (P₁ j) = ∑ Q ∈ x.support, g Q := fun g => by
    rw [← Finset.sum_coe_sort x.support]
    exact Fintype.sum_equiv e₁.symm _ _ fun j => rfl
  have hre₂ : ∀ {N : Type} [AddCommMonoid N]
      (g : Mori.PrimeDivisor σ.snd.idealSheaf.subscheme → N),
      ∑ j, g (P₂ j) = ∑ Q ∈ y.support, g Q := fun g => by
    rw [← Finset.sum_coe_sort y.support]
    exact Fintype.sum_equiv e₂.symm _ _ fun j => rfl
  let M : Fin (x.support.card + y.support.card) → (dsIdeal σ).subscheme.Modules :=
    Fin.append (fun j => (Scheme.Modules.pullback (sι σ)).obj
        (MMP.CartierDivisor.sheaf (π (fstS F σ) (P₁ j))))
      (fun j => (Scheme.Modules.pullback (tι σ)).obj
        (MMP.CartierDivisor.sheaf (π (sndS F σ) (P₂ j))))
  let c : Fin (x.support.card + y.support.card) → ℚ :=
    Fin.append (fun j => x (P₁ j)) (fun j => -y (P₂ j))
  have : ∀ j, SheafOfModules.IsInvertible (dsIdeal σ).subscheme.presheaf
      (dsIdeal σ).subscheme.ringCatSheaf.2 (M j) := MMP.Mori.isInvertible_finAppend _ _
  let h1 : Fin 1 → ℚ := fun _ => 1
  let H1 : Fin 1 → (dsIdeal σ).subscheme.Modules := fun _ => HS
  have key := MMP.Mori.sheafCombinationIntersectionNumber_two_nonpos_of_isotropic hW hdim2 A
    (hAmpS σ) h1 H1 c M
  have : ∀ j : Fin 0, SheafOfModules.IsInvertible (dsIdeal σ).subscheme.presheaf
      (dsIdeal σ).subscheme.ringCatSheaf.2 ((![] : Fin 0 → (dsIdeal σ).subscheme.Modules) j) :=
    fun j => j.elim0
  have k1 : MMP.Mori.sheafCombinationIntersectionNumber ℂ ((dsIdeal σ).subscheme ↘ Spec (.of ℂ))
      (𝟙 _) ℚ h1 H1 1 ![A] (by rw [hdim2]; rfl) =
      num2 (dsIdeal σ).subscheme ((dsIdeal σ).subschemeι ≫ Z ↘ Spec (.of ℂ)) HS A := by
    rw [comb_one_eq_two, Fin.sum_univ_one, one_mul]; rfl
  have k2 : MMP.Mori.sheafCombinationIntersectionNumber ℂ ((dsIdeal σ).subscheme ↘ Spec (.of ℂ))
      (𝟙 _) ℚ h1 H1 2 ![] (by rw [hdim2]; rfl) =
      num2 (dsIdeal σ).subscheme ((dsIdeal σ).subschemeι ≫ Z ↘ Spec (.of ℂ)) HS HS := by
    rw [comb_two_eq_two, Fin.sum_univ_one, Fin.sum_univ_one, one_mul, one_mul]; rfl
  have hx1 : ∑ j, x (P₁ j) * num2 (dsIdeal σ).subscheme ((dsIdeal σ).subscheme ↘ Spec (.of ℂ))
      ((Scheme.Modules.pullback (sι σ)).obj (MMP.CartierDivisor.sheaf (π (fstS F σ) (P₁ j)))) HS =
      Finsupp.linearCombination ℚ (bUA π Hh σ) x :=
    (hre₁ (fun Q => x Q * bUA π Hh σ Q)).trans (Finsupp.linearCombination_apply ℚ x).symm
  have hy1 : ∑ j, y (P₂ j) * num2 (dsIdeal σ).subscheme ((dsIdeal σ).subscheme ↘ Spec (.of ℂ))
      ((Scheme.Modules.pullback (tι σ)).obj (MMP.CartierDivisor.sheaf (π (sndS F σ) (P₂ j)))) HS =
      Finsupp.linearCombination ℚ (bUA π Hh σ.swap) y :=
    (hre₂ (fun Q => y Q * bUA π Hh σ.swap Q)).trans (Finsupp.linearCombination_apply ℚ y).symm
  have k3 : ∑ j, h1 j * MMP.Mori.sheafCombinationIntersectionNumber ℂ
      ((dsIdeal σ).subscheme ↘ Spec (.of ℂ)) (𝟙 _) ℚ c M 1 ![H1 j] (by rw [hdim2]; rfl) = 0 := by
    rw [Fin.sum_univ_one, one_mul, comb_one_eq_two, Fin.sum_univ_add]
    simp only [c, M, H1, Fin.append_left, Fin.append_right]
    rw [hx1]
    simp only [neg_mul, Finset.sum_neg_distrib]
    rw [hy1, hx, hy]
    ring
  have hxx : ∑ j, ∑ k, x (P₁ j) * x (P₁ k) * num2 (dsIdeal σ).subscheme
      ((dsIdeal σ).subscheme ↘ Spec (.of ℂ))
      ((Scheme.Modules.pullback (sι σ)).obj (MMP.CartierDivisor.sheaf (π (fstS F σ) (P₁ j))))
      ((Scheme.Modules.pullback (sι σ)).obj (MMP.CartierDivisor.sheaf (π (fstS F σ) (P₁ k)))) =
      bilin (bU π σ) x x := by
    refine Eq.trans ?_ (bilin_apply (bU π σ) x x).symm
    rw [← hre₁]
    exact Finset.sum_congr rfl fun j _ => hre₁ (fun Q => x (P₁ j) * x Q * bU π σ (P₁ j) Q)
  have hxy' : ∑ j, ∑ k, x (P₁ j) * y (P₂ k) * num2 (dsIdeal σ).subscheme
      ((dsIdeal σ).subscheme ↘ Spec (.of ℂ))
      ((Scheme.Modules.pullback (sι σ)).obj (MMP.CartierDivisor.sheaf (π (fstS F σ) (P₁ j))))
      ((Scheme.Modules.pullback (tι σ)).obj (MMP.CartierDivisor.sheaf (π (sndS F σ) (P₂ k)))) =
      bilin (bC π σ) x y := by
    refine Eq.trans ?_ (bilin_apply (bC π σ) x y).symm
    rw [← hre₁]
    exact Finset.sum_congr rfl fun j _ => hre₂ (fun Q => x (P₁ j) * y Q * bC π σ (P₁ j) Q)
  have hyy : ∑ j, ∑ k, y (P₂ j) * y (P₂ k) * num2 (dsIdeal σ).subscheme
      ((dsIdeal σ).subscheme ↘ Spec (.of ℂ))
      ((Scheme.Modules.pullback (tι σ)).obj (MMP.CartierDivisor.sheaf (π (sndS F σ) (P₂ j))))
      ((Scheme.Modules.pullback (tι σ)).obj (MMP.CartierDivisor.sheaf (π (sndS F σ) (P₂ k)))) =
      bilin (bU π σ.swap) y y := by
    refine Eq.trans ?_ (bilin_apply (bU π σ.swap) y y).symm
    refine (Finset.sum_congr rfl fun j _ =>
      hre₂ (fun Q => y (P₂ j) * y Q * bU π σ.swap (P₂ j) Q)).trans ?_
    exact hre₂ (fun P => ∑ Q ∈ y.support, y P * y Q * bU π σ.swap P Q)
  have hyx : ∑ j, ∑ k, y (P₂ j) * x (P₁ k) * num2 (dsIdeal σ).subscheme
      ((dsIdeal σ).subscheme ↘ Spec (.of ℂ))
      ((Scheme.Modules.pullback (tι σ)).obj (MMP.CartierDivisor.sheaf (π (sndS F σ) (P₂ j))))
      ((Scheme.Modules.pullback (sι σ)).obj (MMP.CartierDivisor.sheaf (π (fstS F σ) (P₁ k)))) =
      ∑ j, ∑ k, x (P₁ j) * y (P₂ k) * num2 (dsIdeal σ).subscheme
      ((dsIdeal σ).subscheme ↘ Spec (.of ℂ))
      ((Scheme.Modules.pullback (sι σ)).obj (MMP.CartierDivisor.sheaf (π (fstS F σ) (P₁ j))))
      ((Scheme.Modules.pullback (tι σ)).obj (MMP.CartierDivisor.sheaf (π (sndS F σ) (P₂ k)))) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [num2_comm, mul_comm (y (P₂ k))]
  have h2 : MMP.Mori.sheafCombinationIntersectionNumber ℂ ((dsIdeal σ).subscheme ↘ Spec (.of ℂ))
      (𝟙 _) ℚ c M 2 ![] (by rw [hdim2]; rfl) =
      bilin (bU π σ) x x - 2 * bilin (bC π σ) x y + bilin (bU π σ.swap) y y := by
    rw [comb_two_eq_two, Fin.sum_univ_add]
    simp only [Fin.sum_univ_add, c, M, Fin.append_left, Fin.append_right]
    rw [← hxx, ← hxy', ← hyy]
    simp only [Finset.sum_add_distrib, neg_mul, mul_neg, neg_neg, Finset.sum_neg_distrib]
    rw [hyx]
    ring
  rw [← h2]
  have eHS : Nonempty (HS ≅ (Scheme.Modules.pullback ((dsIdeal σ).subschemeι ≫ r)).obj MY) :=
    ⟨(Scheme.Modules.pullback _).mapIso eH.some ≪≫ (Scheme.Modules.pullbackComp _ _).app MY⟩
  have hu : ((dsIdeal σ).subschemeι ≫ r) ≫ pY =
      (dsIdeal σ).subschemeι ≫ Z ↘ Spec (.of ℂ) := by
    rw [Category.assoc, hr]
  have him : topologicalKrullDim (Set.range
      (𝟙 (dsIdeal σ).subscheme ≫ (dsIdeal σ).subschemeι ≫ r).base) = 1 := by
    rw [Category.id_comp]; exact hcur σ hσ
  have hHA : 0 < num2 (dsIdeal σ).subscheme
      ((dsIdeal σ).subschemeι ≫ Z ↘ Spec (.of ℂ)) HS A := by
    rw [num2_congr _ _ _ _ _ eHS ⟨Iso.refl _⟩, num2_eq _ _ _ hdim2.le]
    have := sheafIntersectionNumber_pullback_isAmple_pos ℂ
      ((dsIdeal σ).subschemeι ≫ Z ↘ Spec (.of ℂ)) pY ((dsIdeal σ).subschemeι ≫ r) hu MY A
      (𝟙 _) hM (hAmpS σ) (by rw [hdim2]; rfl) (by rw [him]; exact zero_lt_one)
    exact_mod_cast this
  have hHH : num2 (dsIdeal σ).subscheme
      ((dsIdeal σ).subschemeι ≫ Z ↘ Spec (.of ℂ)) HS HS = 0 := by
    rw [num2_congr _ _ _ _ _ eHS eHS, num2_eq _ _ _ hdim2.le]
    have := sheafIntersectionNumber_pullback_pullback_eq_zero ℂ
      ((dsIdeal σ).subschemeι ≫ Z ↘ Spec (.of ℂ)) pY ((dsIdeal σ).subschemeι ≫ r) hu MY A
      (𝟙 _) (hAmpS σ) hdim2.le him.le
    exact_mod_cast this
  exact (key (by rw [k1]; exact hHA) (k2.trans hHH) k3).1

omit [IsComplexScheme Z] in
/-- **Negative definiteness on the point-edge systems**, from the weighted surface identity, for
`A = N H - D` ample on every component and `H|_S · A|_S = 0` on the point edges `S`: an oriented
system `a` supported on the point edges with `∑ᵢ (Zᵢ(a)² · A) / nᵢ = 0` vanishes. -/
theorem eq_zero_of_sum_bilin_bB_div_eq_zero
    (hB : F.IsSNC (Z ↘ Spec (.of ℂ))) (hdim : topologicalKrullDim Z = 4)
    (π : ∀ i : F.support, Mori.PrimeDivisor i.1.idealSheaf.subscheme →
      i.1.idealSheaf.subscheme.CartierDivisor)
    (hπ : ∀ i P, MMP.Intersection.IsWeilDivisorOfCartier (π i P) (Finsupp.single P 1))
    (hvar : MMP.Mori.IsVariety ℂ (Z ↘ Spec (.of ℂ)))
    (hsm : MMP.Mori.IsSmoothScheme (Z ↘ Spec (.of ℂ)))
    (hZp : IsProjectiveMorphism (Z ↘ Spec (.of ℂ))) (hBred : ∀ E ∈ F.support, F E = 1)
    (ε : F.support → Z.CartierDivisor)
    (hε : ∀ i, MMP.Intersection.IsWeilDivisorOfCartier (ε i) (Finsupp.single i.1 1))
    (Hc Hh : Z.CartierDivisor) (n : F.support → ℕ) (hn : ∀ i, 0 < n i) (N : ℕ)
    (hAH : Nonempty (MMP.CartierDivisor.sheaf (Hc + ∑ l : F.support, n l • ε l) ≅
      MMP.CartierDivisor.sheaf (N • Hh)))
    (hAmp : ∀ i : F.support, Stacks.Ample.IsAmple i.1.idealSheaf.subscheme
      ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hc)))
    (pt : DoubleSurface F → Prop)
    (hAmpS : ∀ σ : DoubleSurface F, Stacks.Ample.IsAmple (dsIdeal σ).subscheme
      ((Scheme.Modules.pullback (dsIdeal σ).subschemeι).obj (MMP.CartierDivisor.sheaf Hc)))
    {Y : Scheme.{0}} (pY : Y ⟶ Spec (.of ℂ)) [IsProper pY] (r : Z ⟶ Y)
    (hr : r ≫ pY = Z ↘ Spec (.of ℂ)) (MY : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 MY]
    (eH : Nonempty (MMP.CartierDivisor.sheaf Hh ≅ (Scheme.Modules.pullback r).obj MY))
    (hpt : ∀ σ : DoubleSurface F, pt σ →
      topologicalKrullDim (Set.range ((dsIdeal σ).subschemeι ≫ r).base) ≤ 0)
    (Zl : (DoubleSurface F → ℚ) →ₗ[ℚ] ∀ i : F.support, QDivisor i.1.idealSheaf.subscheme)
    (hZl : ∀ a i, Zl a i = surfaceCoefficientDivisor a i.1) :
    ∀ a ∈ orientedSurfaceCoefficients F, (∀ σ, ¬ pt σ → a σ = 0) →
      ∑ i, bilin (bB π Hc i) (Zl a i) (Zl a i) / (n i : ℚ) = 0 → a = 0 := by
  intro a ha hapt h0
  simp only [hZl] at h0
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (Z ↘ Spec (.of ℂ))
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (Z ↘ Spec (.of ℂ))
  have : IsNoetherian Z := ⟨⟩
  have := DoubleSurface.finite (B := F)
  let _ : Fintype (DoubleSurface F) := Fintype.ofFinite _
  have hDA : ∀ σ : DoubleSurface F, pt σ → num2 (dsIdeal σ).subscheme
      ((dsIdeal σ).subschemeι ≫ Z ↘ Spec (.of ℂ))
      ((Scheme.Modules.pullback (dsIdeal σ).subschemeι).obj (MMP.CartierDivisor.sheaf Hh))
      ((Scheme.Modules.pullback (dsIdeal σ).subschemeι).obj (MMP.CartierDivisor.sheaf Hc)) = 0 := by
    intro σ hσ
    have hdim2 := topologicalKrullDim_dsIdeal hB hdim σ
    have eHS : Nonempty ((Scheme.Modules.pullback (dsIdeal σ).subschemeι).obj
        (MMP.CartierDivisor.sheaf Hh) ≅
          (Scheme.Modules.pullback ((dsIdeal σ).subschemeι ≫ r)).obj MY) :=
      ⟨(Scheme.Modules.pullback _).mapIso eH.some ≪≫ (Scheme.Modules.pullbackComp _ _).app MY⟩
    have hu : ((dsIdeal σ).subschemeι ≫ r) ≫ pY =
        (dsIdeal σ).subschemeι ≫ Z ↘ Spec (.of ℂ) := by
      rw [Category.assoc, hr]
    rw [num2_congr _ _ _ _ _ eHS ⟨Iso.refl _⟩, num2_eq _ _ _ hdim2.le]
    have := sheafIntersectionNumber_eq_zero_of_isAmple_of_pullback ℂ
      ((dsIdeal σ).subschemeι ≫ Z ↘ Spec (.of ℂ)) pY ((dsIdeal σ).subschemeι ≫ r) hu _ (hAmpS σ)
      (𝟙 _) 2 hdim2.le (fun _ => MY)
      ![(Scheme.Modules.pullback ((dsIdeal σ).subschemeι ≫ r)).obj MY,
        (Scheme.Modules.pullback (dsIdeal σ).subschemeι).obj (MMP.CartierDivisor.sheaf Hc)] {1}
      (fun q hq => by rw [Finset.mem_singleton.1 hq]; rfl)
      (fun q hq => by
        fin_cases q
        · rfl
        · exact absurd (Finset.mem_singleton_self _) hq)
      (by
        rw [Category.id_comp, Finset.card_singleton]
        exact (hpt σ hσ).trans_lt (by exact_mod_cast (show (0 : ℕ) < 2 - 1 by norm_num)))
    exact_mod_cast this
  classical
  let : LinearOrder F.support :=
    LinearOrder.lift' (Fintype.equivFin F.support) (Fintype.equivFin F.support).injective
  have W := sum_sq_mul_intersectionNumber_doubleSurface_eq ℂ (Z ↘ Spec (.of ℂ)) hvar hsm hZp hdim
    F hBred hB a ha (fun i => (n i : ℚ)) (fun i => by exact_mod_cast hn i)
    (Finsupp.single Hc 1) ε hε π hπ
  simp only [Finsupp.sum_single_index, zero_mul, mul_zero, one_mul, mul_one] at W
  -- the first term of the right side is the form `P(Z(a))`, which vanishes
  have hR1 : ∑ x : F.support, 1 / (n x : ℚ) *
      Finsupp.sum (surfaceCoefficientDivisor a x.1) (fun P cP =>
        Finsupp.sum (surfaceCoefficientDivisor a x.1) fun Q cQ => cP * cQ *
          (@sheafIntersectionNumber ℂ _ _ _ (x.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)) _
            (𝟙 _) _ 3 (topologicalKrullDim_component hdim x).le
            ![MMP.CartierDivisor.sheaf (π x P), MMP.CartierDivisor.sheaf (π x Q),
              (Scheme.Modules.pullback x.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hc)]
            inv_vec3 : ℚ)) = 0 := by
    rw [← h0]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [bilin_apply, one_div, div_eq_inv_mul]
    congr 1
    simp only [Finsupp.sum]
    refine Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun Q _ => ?_
    unfold bB
    rw [num3_eq _ _ _ _ (topologicalKrullDim_component hdim x).le]
  rw [show (∑ x : F.support, 1 / (n x : ℚ) * _) = (0 : ℚ) from hR1, zero_add] at W
  -- `(A · T) ≥ 0` on the triple curves
  have hTnn : ∀ (x : F.support) (T : Set Z) (_ : T ⊆ x.1.support)
      (hdT : topologicalKrullDim
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure T)).subscheme ≤
          ((1 : ℕ) : WithBot ℕ∞)),
      (0 : ℚ) ≤ (sheafIntersectionNumber ℂ (Z ↘ Spec (.of ℂ))
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure T)).subschemeι 1 hdT
        (fun _ => MMP.CartierDivisor.sheaf Hc) : ℚ) := by
    intro x T hTx hdT
    have hle : x.1.idealSheaf ≤
        Scheme.IdealSheafData.vanishingIdeal (Closeds.closure T) := by
      have := x.1.integral
      rw [Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme x.1.idealSheaf
        x.1.idealSheaf.support rfl]
      refine Scheme.IdealSheafData.vanishingIdeal_antimono ?_
      change closure T ⊆ (x.1.idealSheaf.support : Set Z)
      exact closure_minimal hTx x.1.idealSheaf.support.isClosed
    rw [MMP.Mori.sheafIntersectionNumber_congr_hom ℂ _
      (Scheme.IdealSheafData.inclusion_subschemeι hle).symm,
      MMP.Mori.sheafIntersectionNumber_comp_eq_of_iso ℂ _ x.1.idealSheaf.subschemeι
        (Scheme.IdealSheafData.inclusion hle) 1 hdT _
        (fun _ => (Scheme.Modules.pullback x.1.idealSheaf.subschemeι).obj
          (MMP.CartierDivisor.sheaf Hc)) (fun _ => Iso.refl _),
      MMP.Mori.Snapper.sheafIntersectionNumber_eq_intersectionNumber]
    exact_mod_cast MMP.Threefold.Mori.intersectionNumber_nonneg_of_isAmple ℂ _
      ((Scheme.Modules.pullback x.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hc))
      ((Scheme.Modules.pullback x.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hc))
      (hAmp x) 0
      (fun W i _ _ hW => by
        rw [AlgebraicGeometry.intersectionNumber_zero_eq_finrank_globalSections]
        exact_mod_cast Nat.zero_le _)
      (Scheme.IdealSheafData.inclusion hle) 1 hdT _ Finset.univ (fun _ _ => rfl)
      (fun q hq => absurd (Finset.mem_univ q) hq) (by simp)
  have hR2 : 0 ≤ ∑ x : F.support, ∑ x₁ : F.support, ∑ x₂ : F.support,
      if h : x < x₁ then if h₁ : x₁ < x₂ then
        ∑ᶠ (T : Set Z) (h₂ : T.Nonempty ∧ T ⊆ x.1.support ∩ x₁.1.support ∩ x₂.1.support ∧
          ∃ x₃ ∈ x.1.support ∩ x₁.1.support ∩ x₂.1.support,
            connectedComponentIn (x.1.support ∩ x₁.1.support ∩ x₂.1.support) x₃ = T),
          (n x : ℚ) * n x₁ * n x₂ *
            (coeffAlong a x.2 x₁.2 (fun e => h.ne (Subtype.ext e)) h₂.1
                (fun y hy => (h₂.2.1 hy).1) / (n x * n x₁) -
              coeffAlong a x.2 x₂.2 (fun e => (h.trans h₁).ne (Subtype.ext e)) h₂.1
                (fun y hy => ⟨(h₂.2.1 hy).1.1, (h₂.2.1 hy).2⟩) / (n x * n x₂) +
              coeffAlong a x₁.2 x₂.2 (fun e => h₁.ne (Subtype.ext e)) h₂.1
                (fun y hy => ⟨(h₂.2.1 hy).1.2, (h₂.2.1 hy).2⟩) / (n x₁ * n x₂)) ^ 2 *
            (sheafIntersectionNumber ℂ (Z ↘ Spec (.of ℂ))
              (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure T)).subschemeι 1
              (topologicalKrullDim_tripleCurve_le ℂ _ hvar hdim hB x x₁ x₂ h h₁ T h₂.2.1)
              (fun _ => MMP.CartierDivisor.sheaf Hc) : ℚ)
        else 0 else 0 := by
    refine Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun x₁ _ =>
      Finset.sum_nonneg fun x₂ _ => ?_
    split_ifs with h h₁
    · refine finsum_nonneg fun T => finsum_nonneg fun h₂ => ?_
      refine mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) ?_
      exact hTnn x T (fun y hy => (h₂.2.1 hy).1.1) _
    · exact le_rfl
    · exact le_rfl
  -- `∑ₗ mₗ (Eₗ · A · S) = -(A² · S)` with `(A² · S) > 0`
  have hq : ∀ σ : DoubleSurface F, pt σ → ∃ q : ℚ, 0 < q ∧ ∑ x : F.support, (n x : ℚ) *
      (sheafIntersectionNumber ℂ (Z ↘ Spec (.of ℂ))
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure σ.carrier)).subschemeι
        2 (topologicalKrullDim_doubleSurface_le ℂ _ hvar hdim hB σ)
        (fun t => MMP.CartierDivisor.sheaf (![ε x, Hc] t)) : ℚ) = -q := by
    intro σ hσ
    have hS := topologicalKrullDim_doubleSurface_le ℂ _ hvar hdim hB σ
    let Ls : Fin 2 → Z.Modules := fun t => MMP.CartierDivisor.sheaf (![Hc, Hc] t)
    have hslot : ∀ C : Z.CartierDivisor,
        (slotHom (Z ↘ Spec (.of ℂ)) (dsIdeal σ).subschemeι 2 hS Ls 0 (𝟙 Z) C : ℤ) =
          sheafIntersectionNumber ℂ (Z ↘ Spec (.of ℂ)) (dsIdeal σ).subschemeι 2 hS
            (fun t => MMP.CartierDivisor.sheaf (![C, Hc] t)) := by
      intro C
      rw [slotHom_apply]
      refine @sIN_congr_iso ℂ _ Z _ _ _ _ _ 2 hS _ _ (isInvertible_update Ls 0 _)
        (fun t => MMP.Mori.isInvertible_cartierSheaf _) fun q => ?_
      fin_cases q
      · exact ⟨eqToIso (Function.update_self _ _ _) ≪≫ (Scheme.Modules.pullbackId Z).app _⟩
      · exact ⟨eqToIso (Function.update_of_ne (by decide) _ _)⟩
    have key := slotHom_eq_of_iso (Z ↘ Spec (.of ℂ)) (dsIdeal σ).subschemeι 2 hS Ls 0 (𝟙 Z) hAH
    rw [map_add, map_sum] at key
    simp only [map_nsmul, nsmul_eq_mul] at key
    simp only [hslot] at key
    have hH0 : (sheafIntersectionNumber ℂ (Z ↘ Spec (.of ℂ)) (dsIdeal σ).subschemeι 2 hS
        (fun t => MMP.CartierDivisor.sheaf (![Hh, Hc] t)) : ℚ) = 0 := by
      rw [← hDA σ hσ, num2_eq _ _ _ (topologicalKrullDim_dsIdeal hB hdim σ).le,
        MMP.Mori.sheafIntersectionNumber_congr_hom ℂ _ (Category.id_comp _).symm,
        MMP.Mori.sheafIntersectionNumber_comp_eq_of_iso ℂ _ (dsIdeal σ).subschemeι (𝟙 _) 2 _ _
          (fun t => (Scheme.Modules.pullback (dsIdeal σ).subschemeι).obj
            (MMP.CartierDivisor.sheaf (![Hh, Hc] t))) (fun t => Iso.refl _)]
      exact congrArg (fun z : ℤ => (z : ℚ)) (sIN_congr_family _ _ _ _
        (funext fun t => by fin_cases t <;> rfl))
    refine ⟨(sheafIntersectionNumber ℂ (Z ↘ Spec (.of ℂ)) (dsIdeal σ).subschemeι 2 hS
      (fun t => MMP.CartierDivisor.sheaf (![Hc, Hc] t)) : ℚ), ?_, ?_⟩
    · have : IsIntegral (dsIdeal σ).subscheme := isIntegral_dsIdeal hB σ
      rw [MMP.Mori.sheafIntersectionNumber_congr_hom ℂ _ (sι_comp σ).symm,
        MMP.Mori.sheafIntersectionNumber_comp_eq_of_iso ℂ _ σ.fst.idealSheaf.subschemeι (sι σ) 2
          _ _ (fun t => (Scheme.Modules.pullback σ.fst.idealSheaf.subschemeι).obj
            (MMP.CartierDivisor.sheaf (![Hc, Hc] t))) (fun t => Iso.refl _)]
      have hpos := MMP.Threefold.Mori.sheafSelfIntersectionNumber_pos_of_isAmple ℂ
        (σ.fst.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ))
        ((Scheme.Modules.pullback σ.fst.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hc))
        (hAmp (fstS F σ)) (dsIdeal σ).subscheme (sι σ) 2 (topologicalKrullDim_dsIdeal hB hdim σ)
      unfold MMP.Mori.sheafSelfIntersectionNumber at hpos
      rw [sIN_congr_family _ _ _ _ (funext fun t => by fin_cases t <;> rfl :
        (fun _ : Fin 2 => (Scheme.Modules.pullback σ.fst.idealSheaf.subschemeι).obj
          (MMP.CartierDivisor.sheaf Hc)) = fun t => (Scheme.Modules.pullback
            σ.fst.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf (![Hc, Hc] t)))] at hpos
      exact_mod_cast hpos
    · have := congrArg (fun z : ℤ => (z : ℚ)) key
      push_cast at this
      rw [hH0, mul_zero] at this
      linarith
  choose q hqpos hqeq using hq
  rw [finsum_eq_sum_of_fintype] at W
  simp only [finsum_eq_if] at W
  have hnn : ∀ σ : DoubleSurface F, (if (⟨σ.fst, σ.fst_mem⟩ : F.support) < ⟨σ.snd, σ.snd_mem⟩ then
      (n ⟨σ.fst, σ.fst_mem⟩ : ℚ) * n ⟨σ.snd, σ.snd_mem⟩ *
        (a σ / (n ⟨σ.fst, σ.fst_mem⟩ * n ⟨σ.snd, σ.snd_mem⟩)) ^ 2 * ∑ x : F.support, (n x : ℚ) *
      (sheafIntersectionNumber ℂ (Z ↘ Spec (.of ℂ))
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure σ.carrier)).subschemeι
        2 (topologicalKrullDim_doubleSurface_le ℂ _ hvar hdim hB σ)
        (fun t => MMP.CartierDivisor.sheaf (![ε x, Hc] t)) : ℚ) else 0) ≤ 0 := by
    intro σ
    by_cases hσ : pt σ
    · rw [hqeq σ hσ]
      split_ifs
      · have h1 : (0 : ℚ) < n ⟨σ.fst, σ.fst_mem⟩ := by exact_mod_cast hn _
        have h2 : (0 : ℚ) < n ⟨σ.snd, σ.snd_mem⟩ := by exact_mod_cast hn _
        exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (mul_nonneg h1.le h2.le) (sq_nonneg _))
          (neg_nonpos.2 (hqpos σ hσ).le)
      · exact le_rfl
    · rw [hapt σ hσ]
      split_ifs <;> simp
  have hsum0 := le_antisymm (Finset.sum_nonpos fun σ _ => hnn σ) (W ▸ hR2)
  have hzero := (Finset.sum_eq_zero_iff_of_nonpos fun σ _ => hnn σ).1 hsum0
  have hlt : ∀ σ : DoubleSurface F, (⟨σ.fst, σ.fst_mem⟩ : F.support) < ⟨σ.snd, σ.snd_mem⟩ →
      a σ = 0 := by
    intro σ hσ
    by_cases hp : pt σ
    · have h := hzero σ (Finset.mem_univ σ)
      simp only [hσ, ↓reduceIte] at h
      rw [hqeq σ hp] at h
      have h1 : (n ⟨σ.fst, σ.fst_mem⟩ : ℚ) ≠ 0 := by exact_mod_cast (hn _).ne'
      have h2 : (n ⟨σ.snd, σ.snd_mem⟩ : ℚ) ≠ 0 := by exact_mod_cast (hn _).ne'
      simpa [h1, h2, (hqpos σ hp).ne'] using h
    · exact hapt σ hp
  funext σ
  rcases lt_trichotomy (⟨σ.fst, σ.fst_mem⟩ : F.support) ⟨σ.snd, σ.snd_mem⟩ with h | h | h
  · exact hlt σ h
  · exact absurd (congrArg Subtype.val h) σ.fst_ne_snd
  · have := hlt σ.swap h
    have hs := (mem_orientedSurfaceCoefficients F).1 ha σ
    rw [this] at hs
    simpa using hs.symm

end Index

end MMP.Fourfold
