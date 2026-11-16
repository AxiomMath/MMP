module
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Threefold.Basic
public import MMP.AlgebraicTopology.ComplexVectorBundle.FirstChernClass
import MMP.AlgebraicGeometry.Intersection.Surface.RiemannRochHodgeIndex
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.SurfaceClassKernel
import MMP.AlgebraicGeometry.Analytic.NumericallyTrivialChernClass
import MMP.AlgebraicGeometry.Analytic.WeakLefschetzInjectivity
import MMP.AlgebraicGeometry.Morphisms.ValuativeCentre
import MMP.AlgebraicGeometry.Analytic.CartierDivisorDictionary
import MMP.AlgebraicTopology.BorelMoore.CycleSpanRestriction
import MMP.AlgebraicGeometry.Resolution.OrderUpperSemicontinuous
import MMP.AlgebraicGeometry.Positivity.VeryAmpleMultiple
import MMP.AlgebraicGeometry.Intersection.Surface.Symmetry
import MMP.AlgebraicGeometry.Resolution.ExceptionalDivisorPrime
import MMP.AlgebraicGeometry.Intersection.PairingSeparation
import MMP.AlgebraicGeometry.Resolution.BlowupChartClosedImmersion
import MMP.AlgebraicGeometry.MMP.Fourfold.PreparedChainDifficulty
import MMP.AlgebraicGeometry.Divisor.SmoothWeilCartier
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.SncFibreHomologyThree
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafMul
public import MMP.AlgebraicGeometry.Variety.Subvariety
public import MMP.AlgebraicGeometry.Chow.CycleClassGenericPoint
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafSections

/-!
# thm mmp conductor threefold divisor index

Chain fold of: `thm_mmp_conductor_threefold_divisor_index`.
-/

/-! ### `thm_mmp_conductor_threefold_divisor_index` -/

open CategoryTheory AlgebraicGeometry

namespace MMP.Fold06.ThmMmpConductorThreefoldDivisorIndex

open MMP.Mori MMP.Analytic

section Combination

variable {k : Type} [Field k] {X Z : Scheme.{0}} (f : X ⟶ Spec (.of k)) [IsProper f]
  (i : Z ⟶ X) [IsClosedImmersion i]

/-- The intersection number `(M · N₁ ⋯ N_b · Z)` of a combination `M = ∑ⱼ cⱼ Mⱼ`, as a sum. -/
private theorem combo_one {s b : ℕ} (c : Fin s → ℚ) (M : Fin s → X.Modules)
    [hM : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M j)]
    (N : Fin b → X.Modules)
    [hN : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (N j)]
    (hd : topologicalKrullDim Z ≤ (1 + b : ℕ)) :
    sheafCombinationIntersectionNumber k f i ℚ c M 1 N hd =
      ∑ j, c j * (@intersectionNumber k _ X Z f _ i _ (1 + b) hd
        (Fin.append (fun _ : Fin 1 => M j) N)
        (isInvertible_finAppend (fun _ : Fin 1 => M j) N (hA := fun _ => hM j)) : ℚ) := by
  rw [sheafCombinationIntersectionNumber, ← (Equiv.funUnique (Fin 1) (Fin s)).symm.sum_comp]
  refine Fintype.sum_congr _ _ fun j => ?_
  rw [Fin.prod_univ_one]
  congr 1
  exact_mod_cast @Snapper.sheafIntersectionNumber_eq_intersectionNumber k _ X Z f _ i _ (1 + b) hd
    _ (isInvertible_finAppend _ N (hA := fun _ => hM _))

/-- The intersection number `(M² · N₁ ⋯ N_b · Z)` of a combination `M = ∑ⱼ cⱼ Mⱼ`, as a double
sum. -/
private theorem combo_two {s b : ℕ} (c : Fin s → ℚ) (M : Fin s → X.Modules)
    [hM : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M j)]
    (N : Fin b → X.Modules)
    [hN : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (N j)]
    (hd : topologicalKrullDim Z ≤ (2 + b : ℕ)) :
    sheafCombinationIntersectionNumber k f i ℚ c M 2 N hd =
      ∑ p, ∑ q, c p * c q * (@intersectionNumber k _ X Z f _ i _ (2 + b) hd
        (Fin.append (fun t => M (![p, q] t)) N)
        (isInvertible_finAppend (fun t => M (![p, q] t)) N (hA := fun t => hM _)) : ℚ) := by
  rw [sheafCombinationIntersectionNumber, ← Fintype.sum_prod_type',
    ← (finTwoArrowEquiv (Fin s)).symm.sum_comp]
  refine Fintype.sum_congr _ _ fun pq => ?_
  rw [Fin.prod_univ_two]
  congr 1
  exact_mod_cast @Snapper.sheafIntersectionNumber_eq_intersectionNumber k _ X Z f _ i _ (2 + b) hd
    _ (isInvertible_finAppend _ N (hA := fun _ => hM _))

/-- `Fin.append` of a singleton and a pair is a triple. -/
private theorem append_single_pair {α : Type*} (a b c : α) :
    Fin.append (fun _ : Fin 1 => a) ![b, c] = ![a, b, c] := by
  funext t; fin_cases t <;> rfl

/-- `Fin.append` of a pair and a singleton is a triple. -/
private theorem append_pair_single {α : Type*} {s : ℕ} (M : Fin s → α) (p q : Fin s) (c : α) :
    Fin.append (fun t => M (![p, q] t)) ![c] = ![M p, M q, c] := by
  funext t; fin_cases t <;> rfl

/-- `Fin.append` of two singletons is a pair. -/
private theorem append_single_single {α : Type*} (a b : α) :
    Fin.append (fun _ : Fin 1 => a) ![b] = ![a, b] := by
  funext t; fin_cases t <;> rfl

/-- `Fin.append` of a pair and the empty family is the pair. -/
private theorem append_pair_empty {α : Type*} {s : ℕ} (M : Fin s → α) (p q : Fin s) :
    Fin.append (fun t => M (![p, q] t)) ![] = ![M p, M q] := by
  funext t; fin_cases t <;> rfl

/-- `(M · b · c · Z)` for a combination `M`, as a sum of triple intersection numbers. -/
private theorem combo_one_pair {s : ℕ} (c : Fin s → ℚ) (M : Fin s → X.Modules)
    [hM : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M j)] (a b : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 a]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 b]
    [hN : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (![a, b] j)]
    (hd : topologicalKrullDim Z ≤ (1 + 2 : ℕ)) (hd' : topologicalKrullDim Z ≤ (3 : ℕ)) :
    sheafCombinationIntersectionNumber k f i ℚ c M 1 ![a, b] hd =
      ∑ j, c j * (@intersectionNumber k _ X Z f _ i _ 3 hd' ![M j, a, b]
        (fun t => by fin_cases t <;> simp <;> infer_instance) : ℚ) := by
  rw [combo_one]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact congrArg (fun x : ℤ => c j * (x : ℚ))
    (@intersectionNumber_congr_family k _ X Z _ _ i _ (1 + 2) _ _ _
      (isInvertible_finAppend _ _) (fun t => by fin_cases t <;> simp <;> infer_instance)
      (append_single_pair (M j) a b))

/-- `(M² · a · Z)` for a combination `M`, as a double sum of triple intersection numbers. -/
private theorem combo_two_single {s : ℕ} (c : Fin s → ℚ) (M : Fin s → X.Modules)
    [hM : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M j)] (a : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 a]
    [hN : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (![a] j)]
    (hd : topologicalKrullDim Z ≤ (2 + 1 : ℕ)) (hd' : topologicalKrullDim Z ≤ (3 : ℕ)) :
    sheafCombinationIntersectionNumber k f i ℚ c M 2 ![a] hd =
      ∑ p, ∑ q, c p * c q * (@intersectionNumber k _ X Z f _ i _ 3 hd' ![M p, M q, a]
        (fun t => by fin_cases t <;> simp <;> infer_instance) : ℚ) := by
  rw [combo_two]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  exact congrArg (fun x : ℤ => c p * c q * (x : ℚ))
    (@intersectionNumber_congr_family k _ X Z _ _ i _ (2 + 1) _ _ _
      (isInvertible_finAppend _ _) (fun t => by fin_cases t <;> simp <;> infer_instance)
      (append_pair_single M p q a))

/-- `(M · a · Z)` for a combination `M`, as a sum of intersection numbers of pairs. -/
private theorem combo_one_single {s : ℕ} (c : Fin s → ℚ) (M : Fin s → X.Modules)
    [hM : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M j)] (a : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 a]
    [hN : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (![a] j)]
    (hd : topologicalKrullDim Z ≤ (1 + 1 : ℕ)) (hd' : topologicalKrullDim Z ≤ (2 : ℕ)) :
    sheafCombinationIntersectionNumber k f i ℚ c M 1 ![a] hd =
      ∑ j, c j * (@intersectionNumber k _ X Z f _ i _ 2 hd' ![M j, a]
        (fun t => by fin_cases t <;> simp <;> infer_instance) : ℚ) := by
  rw [combo_one]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact congrArg (fun x : ℤ => c j * (x : ℚ))
    (@intersectionNumber_congr_family k _ X Z _ _ i _ (1 + 1) _ _ _
      (isInvertible_finAppend _ _) (fun t => by fin_cases t <;> simp <;> infer_instance)
      (append_single_single (M j) a))

/-- `(M² · Z)` for a combination `M`, as a double sum of intersection numbers of pairs. -/
private theorem combo_two_empty {s : ℕ} (c : Fin s → ℚ) (M : Fin s → X.Modules)
    [hM : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M j)]
    [hN : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      ((![] : Fin 0 → X.Modules) j)]
    (hd : topologicalKrullDim Z ≤ (2 + 0 : ℕ)) (hd' : topologicalKrullDim Z ≤ (2 : ℕ)) :
    sheafCombinationIntersectionNumber k f i ℚ c M 2 ![] hd =
      ∑ p, ∑ q, c p * c q * (@intersectionNumber k _ X Z f _ i _ 2 hd' ![M p, M q]
        (fun t => by fin_cases t <;> simp <;> infer_instance) : ℚ) := by
  rw [combo_two]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  exact congrArg (fun x : ℤ => c p * c q * (x : ℚ))
    (@intersectionNumber_congr_family k _ X Z _ _ i _ (2 + 0) _ _ _
      (isInvertible_finAppend _ _) (fun t => by fin_cases t <;> simp <;> infer_instance)
      (append_pair_empty M p q))

end Combination

section Restriction

open Stacks.SheafOfModules.Invertible

variable {W : Scheme.{0}} (f : W ⟶ Spec (.of ℂ)) [IsProper f]

/-- A three-term family of invertible sheaves is a family of invertible sheaves. -/
private theorem isInvertible_three (M₁ M₂ M₃ : W.Modules)
    [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 M₁]
    [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 M₂]
    [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 M₃] :
    ∀ j : Fin 3, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 (![M₁, M₂, M₃] j) := by
  intro j; fin_cases j <;> assumption

/-- A two-term family of invertible sheaves is a family of invertible sheaves. -/
private theorem isInvertible_two {Y : Scheme.{0}} (M₁ M₂ : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M₁]
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M₂] :
    ∀ j : Fin 2, SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 (![M₁, M₂] j) := by
  intro j; fin_cases j <;> assumption

/-- **Cutting down by a member of `|νA|`.** If `T` is an effective Cartier divisor with
`𝒪_W(T) ≅ A^{⊗ ν}`, then `(M₁|_T · M₂|_T)_T = ν (M₁ · M₂ · A)`. -/
private theorem intersectionNumber_restrict_eq_mul (T : W.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor T] (hd3 : topologicalKrullDim W ≤ (3 : ℕ))
    (hd2 : topologicalKrullDim T.subscheme ≤ (2 : ℕ)) (A : W.Modules)
    [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 A] (ν : ℕ)
    (e : tensorPower W.presheaf W.ringCatSheaf.2 A (ν : ℤ) ≅ Stacks.Divisors.invertibleSheaf' T)
    (M₁ M₂ : W.Modules) [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 M₁]
    [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 M₂] :
    haveI : ∀ j : Fin 3, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2
        (![M₁, M₂, A] j) := fun j => by fin_cases j <;> assumption
    haveI : SheafOfModules.IsInvertible T.subscheme.presheaf T.subscheme.ringCatSheaf.2
        ((Scheme.Modules.pullback T.subschemeι).obj M₁) := isInvertible_pullback_obj _ _
    haveI : SheafOfModules.IsInvertible T.subscheme.presheaf T.subscheme.ringCatSheaf.2
        ((Scheme.Modules.pullback T.subschemeι).obj M₂) := isInvertible_pullback_obj _ _
    haveI : ∀ j : Fin 2, SheafOfModules.IsInvertible T.subscheme.presheaf
        T.subscheme.ringCatSheaf.2 (![(Scheme.Modules.pullback T.subschemeι).obj M₁,
          (Scheme.Modules.pullback T.subschemeι).obj M₂] j) := fun j => by
      fin_cases j <;> assumption
    (intersectionNumber ℂ (T.subschemeι ≫ f) (𝟙 T.subscheme) 2 hd2
        ![(Scheme.Modules.pullback T.subschemeι).obj M₁,
          (Scheme.Modules.pullback T.subschemeι).obj M₂] : ℚ) =
      ν * intersectionNumber ℂ f (𝟙 W) 3 hd3 ![M₁, M₂, A] := by
  haveI := isInvertible_three M₁ M₂ A
  rw [eq_comm]
  norm_cast
  haveI := isInvertible_three A M₁ M₂
  haveI : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2
      (tensorPower W.presheaf W.ringCatSheaf.2 A (ν : ℤ)) := tensorPower_isInvertible _ _ _ _
  haveI := isInvertible_three (tensorPower W.presheaf W.ringCatSheaf.2 A (ν : ℤ)) M₁ M₂
  haveI : SheafOfModules.IsInvertible T.subscheme.presheaf T.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback T.subschemeι).obj M₁) := isInvertible_pullback_obj _ _
  haveI : SheafOfModules.IsInvertible T.subscheme.presheaf T.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback T.subschemeι).obj M₂) := isInvertible_pullback_obj _ _
  haveI := isInvertible_two ((Scheme.Modules.pullback T.subschemeι).obj M₁)
    ((Scheme.Modules.pullback T.subschemeι).obj M₂)
  -- move `A` to the front
  have hperm := intersectionNumber_comp_perm ℂ f (𝟙 W) 3 hd3 ![A, M₁, M₂] (finRotate 3)
  rw [intersectionNumber_congr_family ℂ f (𝟙 W) 3 hd3 (M := ![M₁, M₂, A])
    (funext fun j => by fin_cases j <;> rfl)] at hperm
  rw [hperm]
  -- replace `A` by `A^{⊗ ν}`
  have hpow := intersectionNumber_update_tensorPower ℂ f (𝟙 W) 3 hd3 ![A, M₁, M₂] 0 ν
  haveI : ∀ q, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2
      (Function.update ![A, M₁, M₂] 0
        (tensorPower W.presheaf W.ringCatSheaf.2 (![A, M₁, M₂] 0) (ν : ℤ)) q) :=
    isInvertible_update _ _ _
  rw [intersectionNumber_congr_family ℂ f (𝟙 W) 3 hd3
    (M := ![tensorPower W.presheaf W.ringCatSheaf.2 A (ν : ℤ), M₁, M₂])
    (funext fun j => by fin_cases j <;> rfl)] at hpow
  rw [← hpow]
  -- cut down by `T`
  rw [intersectionNumber_eq_of_isEffectiveCartierDivisor' ℂ f (𝟙 W) 2 hd3
    ![tensorPower W.presheaf W.ringCatSheaf.2 A (ν : ℤ), M₁, M₂] T
    ((Scheme.Modules.pullbackId W).app _ ≪≫ e :
      _ ≅ (Stacks.Divisors.invertibleSheaf T : W.Modules))]
  haveI := isInvertible_two M₁ M₂
  rw [intersectionNumber_congr_family ℂ f _ 2 _ (M := ![M₁, M₂])
    (funext fun t => by fin_cases t <;> rfl),
    ← Snapper.sheafIntersectionNumber_eq_intersectionNumber,
    ← Snapper.sheafIntersectionNumber_eq_intersectionNumber,
    sheafIntersectionNumber_congr_hom ℂ f
      (show T.subschemeι ≫ 𝟙 W = 𝟙 _ ≫ T.subschemeι by simp)]
  exact sheafIntersectionNumber_comp_eq_of_iso ℂ f T.subschemeι (𝟙 _) 2 hd2 ![M₁, M₂] _
    (fun t => eqToIso (by fin_cases t <;> rfl))

end Restriction

section Member

variable {W : Scheme.{0}} [W.Over (Spec (.of ℂ))]

/-- **A smooth integral member of a very ample linear system.** On a smooth projective complex
variety `W` of dimension at least two, an invertible sheaf `M` that is very ample and ample has
a member `T ∈ |M|` which is an integral effective Cartier divisor, smooth over `ℂ`, with
`𝒪_W(T) ≅ M`: Bertini gives a smooth member, and an ample divisor on a normal projective variety
of dimension at least two is connected. -/
private theorem exists_smooth_integral_member [IsProper (W ↘ Spec (.of ℂ))]
    [Smooth (W ↘ Spec (.of ℂ))] (hW : MMP.Mori.IsProjectiveVariety ℂ (W ↘ Spec (.of ℂ)))
    (hdim : 2 ≤ topologicalKrullDim W) (M : W.Modules)
    [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 M]
    [Stacks.Ample.IsInvertibleModule W M]
    (hva : MMP.Intersection.IsVeryAmple ℂ M) (hamp : Stacks.Ample.IsAmple W M) :
    ∃ T : W.IdealSheafData, Stacks.Divisors.IsEffectiveCartierDivisor T ∧
      IsIntegral T.subscheme ∧ Smooth (T.subschemeι ≫ (W ↘ Spec (.of ℂ))) ∧
      Nonempty (Stacks.Divisors.invertibleSheaf' T ≅ M) := by
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ (W ↘ Spec (.of ℂ)) := hW
  haveI : IsIntegral W := hW.toIsVariety.toIsIntegral
  haveI : IsSmoothVariety ℂ (W ↘ Spec (.of ℂ)) := {}
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (W ↘ Spec (.of ℂ))
  haveI : IsNormal W := isNormal_of_smooth_over_field (W ↘ Spec (.of ℂ))
  obtain ⟨E, ⟨eE⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf M
  let e' : M ≅ MMP.CartierDivisor.sheaf E := eE
  have hvaE : MMP.Intersection.IsVeryAmpleDivisor ℂ E := by
    obtain ⟨N, ι, h1, h2, ⟨e⟩⟩ := hva
    exact ⟨N, ι, h1, h2, ⟨e'.symm ≪≫ e⟩⟩
  obtain ⟨s, hs0, hsm⟩ :=
    MMP.Intersection.exists_ne_zero_smooth_zeroScheme_of_isVeryAmpleDivisor ℂ E hvaE
  haveI : Stacks.Ample.IsInvertibleModule W (MMP.CartierDivisor.sheaf E) :=
    MMP.CartierDivisor.isInvertibleModule_sheaf E
  haveI : SheafOfModules.IsInvertible W.sheaf.obj W.ringCatSheaf.property
      (MMP.CartierDivisor.sheaf E) := inferInstance
  have ht : (Stacks.SheafOfModules.sectionsOfTop (MMP.CartierDivisor.sheaf E) s).eval
      (Opposite.op ⊤) = s := Stacks.SheafOfModules.sectionsOfTop_eval_top _ s
  have hreg := isRegularSection_of_eval_top_ne_zero (MMP.CartierDivisor.sheaf E) _
    (ht ▸ hs0)
  have hD := (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection W
    (MMP.CartierDivisor.sheaf E) _).2 hreg
  have eT := invertibleSheafIsoZeroSchemeOfIsRegularSection (MMP.CartierDivisor.sheaf E) _ hreg
  rw [ht] at hD eT
  refine ⟨_, hD, ?_, hsm, ⟨eT.symm ≪≫ e'.symm⟩⟩
  set T := zeroScheme W (MMP.CartierDivisor.sheaf E) s
  haveI := hD
  haveI : Stacks.Ample.IsInvertibleModule W (Stacks.Divisors.divisorSheaf T) :=
    Stacks.Divisors.isInvertible_divisorSheaf T
  have hampT : Stacks.Ample.IsAmple W (Stacks.Divisors.divisorSheaf T) :=
    (Stacks.RelativeVeryAmple.isAmple_congr _ _ (eT.symm ≪≫ e'.symm)).2 hamp
  have hconn := MMP.Mori.isConnected_support_of_isAmple_divisorSheaf_of_isNormal
    (W ↘ Spec (.of ℂ)) ((AlgebraicGeometry.isProjectiveVariety_iff_isProjective ℂ _).mp hW)
    hdim T hampT
  -- a connected smooth scheme is integral
  have hc : _root_.IsConnected (T.subschemeι.base ⁻¹' (T.support : Set W)) :=
    hconn.preimage_of_isClosedMap T.subschemeι.isClosedEmbedding.injective
      T.subschemeι.isClosedEmbedding.isClosedMap (by rw [T.range_subschemeι])
  have : ConnectedSpace T.subscheme := by
    rw [connectedSpace_iff_univ]
    convert hc
    ext z
    simp only [Set.mem_univ, Set.mem_preimage, true_iff]
    rw [← T.range_subschemeι]
    exact ⟨z, rfl⟩
  exact Stacks.Chow.isIntegral_of_connectedSpace_of_smooth (T.subschemeι ≫ (W ↘ Spec (.of ℂ)))

end Member

section Slice

variable {W : Scheme.{0}} [W.Over (Spec (.of ℂ))]

/-- **Smooth hyperplane sections of all high powers.** On a smooth projective complex variety of
dimension at least two with an ample invertible sheaf `A`, there is `d₀ ≥ 1` such that for every
`d ≥ d₀` the power `A^{⊗ d}` has a member `T` which is an integral effective Cartier divisor
smooth over `ℂ`. -/
private theorem exists_slice [IsProper (W ↘ Spec (.of ℂ))] [Smooth (W ↘ Spec (.of ℂ))]
    (hW : MMP.Mori.IsProjectiveVariety ℂ (W ↘ Spec (.of ℂ))) (hdim : 2 ≤ topologicalKrullDim W)
    (A : W.Modules) [Stacks.Ample.IsInvertibleModule W A] (hA : Stacks.Ample.IsAmple W A) :
    ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d → ∃ T : W.IdealSheafData,
      Stacks.Divisors.IsEffectiveCartierDivisor T ∧ IsIntegral T.subscheme ∧
      Smooth (T.subschemeι ≫ (W ↘ Spec (.of ℂ))) ∧
      Nonempty (Stacks.Ample.tensorPowModule W A d ≅ Stacks.Divisors.invertibleSheaf' T) := by
  haveI : IsAffine (Spec (.of ℂ)) := inferInstance
  obtain ⟨d₀, hd₀1, hd₀⟩ :=
    ((Stacks.AmpleRelativeFiniteType.tfae_six (W ↘ Spec (.of ℂ)) A).out 1 6).1 hA
  refine ⟨d₀, hd₀1, fun d hd => ?_⟩
  have hva : MMP.Intersection.IsVeryAmple ℂ (Stacks.Ample.tensorPowModule W A d) :=
    MMP.Resolution.Bridges.isVeryAmple_of_hasImmersionTwistOver ℂ _ _ (Iso.refl _) (hd₀ d hd)
  have hamp := Stacks.AmplePositivePower.isAmple_tensorPowModule_of_isAmple A d
    (hd₀1.trans hd) hA
  obtain ⟨T, hT, hTi, hTs, ⟨e⟩⟩ := exists_smooth_integral_member hW hdim _ hva hamp
  exact ⟨T, hT, hTi, hTs, ⟨e.symm⟩⟩

/-- **An integral effective Cartier divisor is a prime divisor.** -/
private theorem exists_primeDivisor_idealSheaf_eq [IsLocallyNoetherian W] (T : W.IdealSheafData)
    [hT : Stacks.Divisors.IsEffectiveCartierDivisor T] [IsIntegral T.subscheme] :
    ∃ P : MMP.Mori.PrimeDivisor W, P.idealSheaf = T :=
  ⟨⟨T, inferInstance,
    (Stacks.AlgebraicGeometry.CodimensionOneDivisor.codimension_closureSingleton_eq_one_iff _).2
      (ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor T hT _
        ⟨⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩, genericPoint_spec _⟩)⟩,
    rfl⟩

end Slice

section Surface

variable {W : Scheme.{0}} [W.Over (Spec (.of ℂ))]

/-- An integral closed subscheme of a projective variety is a projective variety. -/
private theorem isProjectiveVariety_subscheme
    (hW : MMP.Mori.IsProjectiveVariety ℂ (W ↘ Spec (.of ℂ))) (T : W.IdealSheafData)
    [IsIntegral T.subscheme] :
    AlgebraicGeometry.IsProjectiveVariety ℂ (T.subschemeι ≫ (W ↘ Spec (.of ℂ))) := by
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ (W ↘ Spec (.of ℂ)) := hW
  obtain ⟨n, j, hj, hjp⟩ := hW.isProjective
  haveI := hj
  haveI : AlgebraicGeometry.IsVariety ℂ (T.subschemeι ≫ (W ↘ Spec (.of ℂ))) := {}
  exact ⟨⟨n, T.subschemeι ≫ j, inferInstance, by rw [Category.assoc, hjp]⟩⟩

end Surface

section Additive

variable {X : Scheme.{0}}

/-- `c₁(𝒪_X(D + D')) = c₁(𝒪_X(D)) + c₁(𝒪_X(D'))` for Cartier divisors `D`, `D'`. -/
private theorem algebraicFirstChernClass_sheaf_add [X.Over (Spec (.of ℂ))]
    (D D' : X.CartierDivisor) :
    algebraicFirstChernClass (MMP.CartierDivisor.sheaf (D + D')) =
      algebraicFirstChernClass (MMP.CartierDivisor.sheaf D) +
        algebraicFirstChernClass (MMP.CartierDivisor.sheaf D') := by
  haveI := Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible X.presheaf
    X.ringCatSheaf.2 (MMP.CartierDivisor.sheaf D) (MMP.CartierDivisor.sheaf D')
  exact (algebraicFirstChernClass_eq_of_iso (MMP.CartierDivisorSheaf.sheafMulIso D D')).symm.trans
    (algebraicFirstChernClass_sheafTensor _ _)

/-- `deg_C 𝒪_X(D + D') = deg_C 𝒪_X(D) + deg_C 𝒪_X(D')` for Cartier divisors `D`, `D'`. -/
private theorem degreeOn_sheaf_add {k : Type} [Field k] {C : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (i : C ⟶ X) [IsProper (i ≫ sX)] (hC : topologicalKrullDim C ≤ 1)
    (D D' : X.CartierDivisor) :
    degreeOn k sX i hC (MMP.CartierDivisor.sheaf (D + D')) =
      degreeOn k sX i hC (MMP.CartierDivisor.sheaf D) +
        degreeOn k sX i hC (MMP.CartierDivisor.sheaf D') := by
  haveI := Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible X.presheaf
    X.ringCatSheaf.2 (MMP.CartierDivisor.sheaf D) (MMP.CartierDivisor.sheaf D')
  exact (degreeOn_eq_of_iso k sX i hC (MMP.CartierDivisorSheaf.sheafMulIso D D')).symm.trans
    (degreeOn_tensorSheaf k sX i hC _ _)

/-- `c₁(M^{⊗ d}) = d c₁(M)` for `d ≥ 1`. -/
private theorem algebraicFirstChernClass_tensorPowModule [X.Over (Spec (.of ℂ))] (M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X M] (d : ℕ) (hd : 1 ≤ d) :
    algebraicFirstChernClass (Stacks.Ample.tensorPowModule X M d) =
      (d : ℤ) • algebraicFirstChernClass M := by
  induction d, hd using Nat.le_induction with
  | base =>
    rw [Nat.cast_one, algebraicFirstChernClass_eq_of_iso (Stacks.Ample.tensorPowModuleOneIso X M),
      one_smul]
  | succ d hd ih =>
    rw [← algebraicFirstChernClass_eq_of_iso (Stacks.Ample.tensorPowModuleAddIso X M d 1 ≪≫
        Stacks.RelativeVeryAmple.tensorPowModuleCongr X M (by push_cast; ring)),
      algebraicFirstChernClass_sheafTensor, ih,
      algebraicFirstChernClass_eq_of_iso (Stacks.Ample.tensorPowModuleOneIso X M)]
    push_cast
    rw [add_zsmul, one_zsmul]

/-- `deg_C(M^{⊗ d}) = d deg_C M` for `d ≥ 1`. -/
private theorem degreeOn_tensorPowModule {k : Type} [Field k] {C : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (i : C ⟶ X) [IsProper (i ≫ sX)] (hC : topologicalKrullDim C ≤ 1)
    (M : X.Modules) [Stacks.Ample.IsInvertibleModule X M] (d : ℕ) (hd : 1 ≤ d) :
    degreeOn k sX i hC (Stacks.Ample.tensorPowModule X M d) = d * degreeOn k sX i hC M := by
  induction d, hd using Nat.le_induction with
  | base =>
    rw [Nat.cast_one, degreeOn_eq_of_iso k sX i hC (Stacks.Ample.tensorPowModuleOneIso X M),
      one_mul]
  | succ d hd ih =>
    rw [← degreeOn_eq_of_iso k sX i hC (Stacks.Ample.tensorPowModuleAddIso X M d 1 ≪≫
        Stacks.RelativeVeryAmple.tensorPowModuleCongr X M (by push_cast; ring)),
      degreeOn_tensorSheaf, ih,
      degreeOn_eq_of_iso k sX i hC (Stacks.Ample.tensorPowModuleOneIso X M)]
    push_cast
    ring

/-- The degree along a curve does not depend on how the structure morphism is written. -/
private theorem invertibleCurveDegree_congr_hom {k : Type} [Field k] {C : Scheme.{0}}
    {g g' : C ⟶ Spec (.of k)} [IsProper g] [IsProper g'] (h : g = g')
    (hC : topologicalKrullDim C ≤ 1) (M : C.Modules)
    [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 M] :
    invertibleCurveDegree k g hC M = invertibleCurveDegree k g' hC M := by
  subst h; rfl

/-- **Degrees of a restriction.** For `j : Y ⟶ X` and a curve `i : C ⟶ Y`,
`deg_C (j^* M) = deg_{j ∘ i} M`. -/
private theorem degreeOn_pullback {k : Type} [Field k] {X Y C : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (j : Y ⟶ X) (i : C ⟶ Y) [IsProper (i ≫ j ≫ sX)]
    [IsProper ((i ≫ j) ≫ sX)] (hC : topologicalKrullDim C ≤ 1) (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 ((Scheme.Modules.pullback j).obj M)] :
    degreeOn k (j ≫ sX) i hC ((Scheme.Modules.pullback j).obj M) = degreeOn k sX (i ≫ j) hC M := by
  haveI : SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2
      ((Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback j).obj M)) :=
    isInvertible_pullback_obj _ _
  haveI : SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2
      ((Scheme.Modules.pullback (i ≫ j)).obj M) := isInvertible_pullback_obj _ _
  rw [degreeOn, degreeOn, invertibleCurveDegree_congr_hom (Category.assoc i j sX).symm]
  exact invertibleCurveDegree_eq_of_iso k _ hC ((Scheme.Modules.pullbackComp i j).app M)

end Additive

section Curves

variable {k : Type} [Field k] {S : Scheme.{0}} (sS : S ⟶ Spec (.of k)) [IsProper sS]

/-- **Degrees along integral curves are degrees along proper curves.** If an invertible sheaf `N`
on a proper `k`-scheme has degree zero on every proper curve, it has degree zero along every
integral closed subscheme of dimension at most one: a point carries no degree, and an integral
curve is the closure of its generic point. -/
private theorem degreeOn_eq_zero_of_forall_properCurve (N : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N]
    (hN : ∀ P : ProperCurve sS, P.degree k N = 0) {C : Scheme.{0}} (i : C ⟶ S)
    [IsClosedImmersion i] [IsIntegral C] [IsProper (i ≫ sS)] (hC : topologicalKrullDim C ≤ 1) :
    degreeOn k sS i hC N = 0 := by
  rw [degreeOn, ← intersectionNumber_one_eq_invertibleCurveDegree k sS i hC N]
  rcases lt_or_eq_of_le hC with hlt | heq
  · exact intersectionNumber_eq_zero_of_topologicalKrullDim_lt k sS i 1 hC (by exact_mod_cast hlt) _
  set x := i (genericPoint C) with hx
  have hrange : closure (Set.range i) = closure ({x} : Set S) := by
    refine le_antisymm (closure_minimal ?_ isClosed_closure)
      (closure_mono (Set.singleton_subset_iff.2 ⟨_, rfl⟩))
    rintro _ ⟨c, rfl⟩
    exact specializes_iff_mem_closure.1
      (((genericPoint_spec C).specializes (Set.mem_univ c)).map i.continuous)
  have hker : i.ker = (curveSubschemeAtι x).ker := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range, Scheme.IdealSheafData.ker_subschemeι]
    congr 1
    exact TopologicalSpace.Closeds.ext hrange
  haveI := IsClosedImmersion.isIso_lift (curveSubschemeAtι x) i hker.symm
  let e : C ≅ curveSubschemeAt x :=
    asIso (IsClosedImmersion.lift (curveSubschemeAtι x) i hker.symm.le)
  have hdimx : topologicalKrullDim (curveSubschemeAt x) = 1 := by
    rw [← IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph, heq]
  let P : ProperCurve sS := ⟨x, isProperCurve_of_isProper sS hdimx⟩
  have hP := hN P
  rw [ProperCurve.degree, degreeOn,
    ← intersectionNumber_one_eq_invertibleCurveDegree k sS P.ι P.dim_le N] at hP
  rw [← hP]
  have h := sheafIntersectionNumber_eq_of_ker_eq k sS i P.ι hker 1 (by exact_mod_cast hC)
    (by exact_mod_cast P.dim_le) (fun _ => N)
  rwa [Snapper.sheafIntersectionNumber_eq_intersectionNumber,
    Snapper.sheafIntersectionNumber_eq_intersectionNumber] at h

end Curves

section Numerical

variable {W : Scheme.{0}} [W.Over (Spec (.of ℂ))]

/-- **A line bundle with rationally trivial first Chern class has degree zero on curves.** On a
smooth projective complex threefold, write `𝒪_W(G)^{⊗ d} ≅ 𝒪_W(S₁ - S₂)` with `S₁`, `S₂`
smooth prime divisors (members of `|d(nA + G)|` and `|dnA|`); the class of `S₁ - S₂` in
`H₄(W, ℚ)` is `c₁ ∩ [W] = 0`, so `S₁ - S₂` is numerically trivial. -/
private theorem degree_eq_zero_of_mapCoeff_eq_zero [IsProper (W ↘ Spec (.of ℂ))]
    [Smooth (W ↘ Spec (.of ℂ))] (hW : MMP.Mori.IsProjectiveVariety ℂ (W ↘ Spec (.of ℂ)))
    (hdim : topologicalKrullDim W = 3) (A : W.Modules) [Stacks.Ample.IsInvertibleModule W A]
    (hA : Stacks.Ample.IsAmple W A) (G : W.CartierDivisor)
    (hG : singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
      (algebraicFirstChernClass (MMP.CartierDivisor.sheaf G)) = 0)
    (C : ProperCurve (W ↘ Spec (.of ℂ))) : C.degree ℂ (MMP.CartierDivisor.sheaf G) = 0 := by
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ (W ↘ Spec (.of ℂ)) := hW
  haveI : IsIntegral W := hW.toIsVariety.toIsIntegral
  haveI : IsSmoothVariety ℂ (W ↘ Spec (.of ℂ)) := {}
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (W ↘ Spec (.of ℂ))
  haveI : IsNormal W := isNormal_of_smooth_over_field (W ↘ Spec (.of ℂ))
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (W ↘ Spec (.of ℂ))
  haveI : IsComplexScheme W := MMP.Fourfold.isComplexScheme_of_isProjectiveVariety W hW
  have hsm : IsSmoothScheme (W ↘ Spec (.of ℂ)) := (isSmoothScheme_iff _).2 inferInstance
  have hdim2 : 2 ≤ topologicalKrullDim W := by
    rw [hdim]
    exact_mod_cast (by norm_num : (2 : ℕ) ≤ 3)
  obtain ⟨hcart, -, -, -, -, -⟩ :=
    Divisor.cartier_weil_dictionary_of_isSmoothVariety ℂ (W ↘ Spec (.of ℂ))
  -- the additive invariants `c₁ ∘ 𝒪(-)` and `deg_C ∘ 𝒪(-)` of Cartier divisors
  let χ : W.CartierDivisor →+ _ :=
    AddMonoidHom.mk' (fun D => algebraicFirstChernClass (MMP.CartierDivisor.sheaf D))
      algebraicFirstChernClass_sheaf_add
  let δ : W.CartierDivisor →+ ℤ :=
    AddMonoidHom.mk' (fun D => degreeOn ℂ (W ↘ Spec (.of ℂ)) C.ι C.dim_le (CartierDivisor.sheaf D))
      (degreeOn_sheaf_add _ _ _)
  -- `A = 𝒪(D_A)`, and two ample twists
  obtain ⟨DA, ⟨eA⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf A
  have hDA : Stacks.Ample.IsAmple W (MMP.CartierDivisor.sheaf DA) :=
    (Stacks.RelativeVeryAmple.isAmple_congr _ _ eA).1 hA
  obtain ⟨n, hn1, hn2⟩ := ((MMP.Mori.eventually_isAmple_cartierSheaf_nsmul_add DA G hDA).and
    (MMP.Mori.eventually_isAmple_cartierSheaf_nsmul_add DA 0 hDA)).exists
  -- smooth prime members `S₁ ∈ |d(nA + G)|`, `S₂ ∈ |d(nA)|`
  obtain ⟨d₁, h₁, hs₁⟩ := exists_slice hW hdim2 _ hn1
  obtain ⟨d₂, h₂, hs₂⟩ := exists_slice hW hdim2 _ hn2
  obtain ⟨T₁, hT₁, hT₁i, hT₁s, ⟨e₁⟩⟩ := hs₁ (max d₁ d₂) (le_max_left _ _)
  obtain ⟨T₂, hT₂, hT₂i, hT₂s, ⟨e₂⟩⟩ := hs₂ (max d₁ d₂) (le_max_right _ _)
  have hd : 1 ≤ max d₁ d₂ := h₁.trans (le_max_left _ _)
  obtain ⟨P₁, rfl⟩ := exists_primeDivisor_idealSheaf_eq T₁
  obtain ⟨P₂, rfl⟩ := exists_primeDivisor_idealSheaf_eq T₂
  obtain ⟨f₁⟩ := MMP.Threefold.Resolution.nonempty_divisorialSheaf_single_iso_invertibleSheaf' P₁
    hT₁ (hcart _)
  obtain ⟨f₂⟩ := MMP.Threefold.Resolution.nonempty_divisorialSheaf_single_iso_invertibleSheaf' P₂
    hT₂ (hcart _)
  set d := max d₁ d₂
  -- the divisor `F₀ = S₁ - S₂`
  set F₀ : Divisor W := Finsupp.single P₁ 1 - Finsupp.single P₂ 1 with hF₀_def
  have hF₀ : F₀ + Finsupp.single P₂ 1 = Finsupp.single P₁ 1 := sub_add_cancel _ _
  haveI := (hcart F₀).isInvertibleModule_divisorialSheaf
  haveI := (hcart (Finsupp.single P₁ 1)).isInvertibleModule_divisorialSheaf
  haveI := (hcart (Finsupp.single P₂ 1)).isInvertibleModule_divisorialSheaf
  haveI := (hcart (F₀ + Finsupp.single P₂ 1)).isInvertibleModule_divisorialSheaf
  have eF : (F₀ + Finsupp.single P₂ 1).divisorialSheaf ≅
      Divisor.divisorialSheaf (Finsupp.single P₁ 1 : Divisor W) := eqToIso (by rw [hF₀])
  -- its first Chern class
  have hcF : algebraicFirstChernClass F₀.divisorialSheaf = (d : ℤ) • χ G := by
    have hadd := (algebraicFirstChernClass_eq_of_iso
      ((hcart F₀).divisorialSheafTensorIso (hcart (Finsupp.single P₂ 1)) ≪≫ eF)).symm.trans
      (algebraicFirstChernClass_sheafTensor _ _)
    rw [algebraicFirstChernClass_eq_of_iso (f₁ ≪≫ e₁.symm),
      algebraicFirstChernClass_eq_of_iso (f₂ ≪≫ e₂.symm),
      algebraicFirstChernClass_tensorPowModule _ d hd,
      algebraicFirstChernClass_tensorPowModule _ d hd] at hadd
    have h1 : algebraicFirstChernClass (MMP.CartierDivisor.sheaf (n • DA + G)) =
        χ (n • DA) + χ G := map_add χ _ _
    have h2 : algebraicFirstChernClass (MMP.CartierDivisor.sheaf (n • DA + 0)) = χ (n • DA) := by
      rw [add_zero]; rfl
    rw [h1, h2] at hadd
    generalize χ (n • DA) = a at hadd
    generalize χ G = b at hadd ⊢
    generalize algebraicFirstChernClass F₀.divisorialSheaf = c at hadd ⊢
    rw [zsmul_add, add_comm c] at hadd
    exact (add_left_cancel hadd).symm
  -- its degree on `C`
  have hdF : F₀.degreeOn ℂ (W ↘ Spec (.of ℂ)) C.ι C.dim_le (hcart F₀) = d * δ G := by
    have hadd := Divisor.degreeOn_add ℂ (W ↘ Spec (.of ℂ)) C.ι C.dim_le F₀ (Finsupp.single P₂ 1)
      (hcart _) (hcart _)
    rw [Divisor.degreeOn_congr hF₀ _ (hcart _)] at hadd
    simp only [Divisor.degreeOn] at hadd ⊢
    rw [degreeOn_eq_of_iso _ _ _ _ (f₁ ≪≫ e₁.symm), degreeOn_eq_of_iso _ _ _ _ (f₂ ≪≫ e₂.symm),
      degreeOn_tensorPowModule _ _ _ _ d hd, degreeOn_tensorPowModule _ _ _ _ d hd] at hadd
    have h1 : degreeOn ℂ (W ↘ Spec (.of ℂ)) C.ι C.dim_le (MMP.CartierDivisor.sheaf (n • DA + G)) =
        δ (n • DA) + δ G := map_add δ _ _
    have h2 : degreeOn ℂ (W ↘ Spec (.of ℂ)) C.ι C.dim_le (MMP.CartierDivisor.sheaf (n • DA + 0)) =
        δ (n • DA) := by
      rw [add_zero]; rfl
    rw [h1, h2] at hadd
    linear_combination (-1 : ℤ) * hadd
  -- the rational first Chern class of `𝒪(F₀)` vanishes
  have hmc : singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
      (algebraicFirstChernClass F₀.divisorialSheaf) = 0 := by
    rw [hcF, map_zsmul]
    change (d : ℤ) • singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
      (algebraicFirstChernClass (MMP.CartierDivisor.sheaf G)) = 0
    rw [hG, smul_zero]
  -- so does its class in `H₄(W, ℚ)`
  have hξ : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (W ↘ Spec (.of ℂ)) (genericPoint W) = ((2 + 1 : ℕ) : ℤ) :=
    MMP.Chow.relativeDimension_genericPoint_eq ℂ _ (by rw [hdim]; rfl)
  have hdc : MMP.Chow.divisorClass W (Divisor.toQDivisor F₀) = 0 :=
    ((MMP.Fourfold.smul_rationalCycleClass_eq_capProductPullback hW hsm (d := 2)
      (by rw [hdim]; rfl) (Divisor.toQDivisor F₀) one_pos F₀ (by rw [Nat.cast_one, one_smul])
      (genericPoint W) hξ).2).2 hmc
  -- the components of `F₀` are `S₁` and `S₂`
  have hsupp : ∀ S ∈ (Divisor.toQDivisor F₀).support, S = P₁ ∨ S = P₂ := by
    classical
    intro S hS
    by_contra h
    push Not at h
    apply Finsupp.mem_support_iff.1 hS
    change ((F₀ S : ℤ) : ℚ) = 0
    rw [hF₀_def, Finsupp.sub_apply, Finsupp.single_apply, if_neg (Ne.symm h.1),
      Finsupp.single_apply, if_neg (Ne.symm h.2), sub_zero, Int.cast_zero]
  have hnt := MMP.Threefold.isNumericallyTrivial_of_divisorClass_eq_zero hW hsm hdim
    (Divisor.toQDivisor F₀)
    (fun S hS => by
      rcases hsupp S hS with rfl | rfl
      exacts [(isSmoothScheme_iff _).2 hT₁s, (isSmoothScheme_iff _).2 hT₂s])
    (fun S _ => hcart _) hdc
  obtain ⟨hQ, hnum⟩ := (QDivisor.isNumericallyTrivial_iff _).1 hnt
  haveI : IsIntegral C.scheme :=
    StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _
      isIrreducible_singleton.closure
  have h0 := hnum C.scheme C.ι C.dim_eq
  rw [QDivisor.intersectionNumber_eq_of_smul ℂ _ C.ι C.dim_eq.le _ hQ one_pos F₀ (hcart F₀)
    (by rw [Nat.cast_one, one_smul]), Nat.cast_one, div_one] at h0
  have h0' : F₀.degreeOn ℂ (W ↘ Spec (.of ℂ)) C.ι C.dim_le (hcart F₀) = 0 := by exact_mod_cast h0
  rw [hdF] at h0'
  exact (mul_eq_zero.1 h0').resolve_left (by exact_mod_cast (show d ≠ 0 by omega))

end Numerical

section Lefschetz

variable {W : Scheme.{0}} [W.Over (Spec (.of ℂ))]

/-- **Lifting the vanishing of `c₁` from an ample smooth divisor.** On a smooth projective complex
threefold, if `T` is a smooth effective Cartier divisor with `𝒪_W(T)` ample, an invertible sheaf
whose restriction to `T` has vanishing rational first Chern class has vanishing rational first
Chern class: restriction `H²(W, ℚ) ⟶ H²(T, ℚ)` is injective (weak Lefschetz) and commutes with
`c₁` and with the change of coefficients `ℤ ⟶ ℚ`. -/
private theorem mapCoeff_eq_zero_of_restrict [IsProper (W ↘ Spec (.of ℂ))]
    [Smooth (W ↘ Spec (.of ℂ))] (hW : MMP.Mori.IsProjectiveVariety ℂ (W ↘ Spec (.of ℂ)))
    (hdim : topologicalKrullDim W = 3) (T : W.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor T]
    (hTa : haveI := Stacks.Divisors.isInvertible_divisorSheaf T
      Stacks.Ample.IsAmple W (Stacks.Divisors.divisorSheaf T))
    (hTs : Smooth (T.subschemeι ≫ (W ↘ Spec (.of ℂ)))) (N : W.Modules)
    [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 N]
    (hN : letI : T.subscheme.Over (Spec (.of ℂ)) := ⟨T.subschemeι ≫ (W ↘ Spec (.of ℂ))⟩
      haveI : SheafOfModules.IsInvertible T.subscheme.presheaf T.subscheme.ringCatSheaf.2
          ((Scheme.Modules.pullback T.subschemeι).obj N) := isInvertible_pullback_obj _ _
      singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
        (algebraicFirstChernClass ((Scheme.Modules.pullback T.subschemeι).obj N)) = 0) :
    singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass N) = 0 := by
  letI : T.subscheme.Over (Spec (.of ℂ)) := ⟨T.subschemeι ≫ (W ↘ Spec (.of ℂ))⟩
  haveI : SheafOfModules.IsInvertible T.subscheme.presheaf T.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback T.subschemeι).obj N) := isInvertible_pullback_obj _ _
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ (W ↘ Spec (.of ℂ)) := hW
  haveI : Smooth (T.subschemeι ≫ (W ↘ Spec (.of ℂ))) := hTs
  have hinj := MMP.Analytic.injective_rationalCohomologyMap_subschemeι_of_isAmple
    (W ↘ Spec (.of ℂ)) (MMP.Resolution.isSmoothScheme_of_smooth _) (n := 3) (by rw [hdim]; rfl) T
    hTa (MMP.Resolution.isSmoothScheme_of_smooth _) (k := 2) (by norm_num)
  have hpb := algebraicFirstChernClass_pullback T.subschemeι
    (ComplexPoints.analyticMap (sX := T.subschemeι ≫ (W ↘ Spec (.of ℂ))) (sY := W ↘ Spec (.of ℂ))
      T.subschemeι rfl) (fun _ => rfl) N
  have key := singularCohomology.mapCoeff_relativeSingularCohomology_map (Int.castRingHom ℚ)
    (ComplexPoints.analyticMap (sX := T.subschemeι ≫ (W ↘ Spec (.of ℂ))) (sY := W ↘ Spec (.of ℂ))
      T.subschemeι rfl) (fun _ hx => (hx (Set.mem_univ _)).elim) 2 (algebraicFirstChernClass N)
  rw [hpb] at hN
  exact hinj ((key.symm.trans hN).trans (map_zero _).symm)

end Lefschetz

section Equality

/-- Clearing the denominators of finitely many rationals: `b lⱼ = nⱼ` with `b > 0`. -/
private theorem exists_pos_nat_mul_eq_intCast {t : ℕ} (l : Fin t → ℚ) :
    ∃ b : ℕ, 0 < b ∧ ∃ n : Fin t → ℤ, ∀ j, (n j : ℚ) = b * l j := by
  choose m hm using fun j => Finset.dvd_prod_of_mem (fun i => (l i).den) (Finset.mem_univ j)
  refine ⟨∏ i, (l i).den, Finset.prod_pos fun i _ => (l i).den_pos, fun j => m j * (l j).num,
    fun j => ?_⟩
  rw [hm j]
  push_cast
  rw [← Rat.mul_den_eq_num (l j)]
  ring

variable {W : Scheme.{0}} [W.Over (Spec (.of ℂ))]

/-- **The equality case.** If `L = ∑ⱼ lⱼ Lⱼ` restricts to a numerically trivial combination on a
smooth ample member `T`, then `L` is numerically trivial on `W` and `∑ⱼ lⱼ c₁(Lⱼ) = 0`: the
restriction of an integral multiple `𝒪_W(G)` has degree zero on the curves of `T`, hence
vanishing rational `c₁` on `T`, hence on `W` by weak Lefschetz, and then degree zero on the curves
of `W`. -/
private theorem equality_case [IsProper (W ↘ Spec (.of ℂ))] [Smooth (W ↘ Spec (.of ℂ))]
    (hW : MMP.Mori.IsProjectiveVariety ℂ (W ↘ Spec (.of ℂ))) (hdim : topologicalKrullDim W = 3)
    (A : W.Modules) [Stacks.Ample.IsInvertibleModule W A] (hA : Stacks.Ample.IsAmple W A)
    (T : W.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor T] [IsIntegral T.subscheme]
    (hTa : haveI := Stacks.Divisors.isInvertible_divisorSheaf T
      Stacks.Ample.IsAmple W (Stacks.Divisors.divisorSheaf T))
    (hTs : Smooth (T.subschemeι ≫ (W ↘ Spec (.of ℂ))))
    (hT2 : topologicalKrullDim T.subscheme = 2)
    {t : ℕ} (l : Fin t → ℚ) (L : Fin t → W.Modules)
    [∀ j, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 (L j)]
    (hnull : ∀ P : ProperCurve (T.subschemeι ≫ (W ↘ Spec (.of ℂ))),
      haveI : ∀ j, SheafOfModules.IsInvertible T.subscheme.presheaf T.subscheme.ringCatSheaf.2
          ((Scheme.Modules.pullback T.subschemeι).obj (L j)) :=
        fun _ => isInvertible_pullback_obj _ _
      ∑ j, l j * (P.degree ℂ ((Scheme.Modules.pullback T.subschemeι).obj (L j)) : ℚ) = 0) :
    (∀ C : ProperCurve (W ↘ Spec (.of ℂ)), ∑ j, l j * (C.degree ℂ (L j) : ℚ) = 0) ∧
      ∑ j, l j • singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
        (algebraicFirstChernClass (L j)) = 0 := by
  classical
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ (W ↘ Spec (.of ℂ)) := hW
  haveI : IsIntegral W := hW.toIsVariety.toIsIntegral
  haveI hLT : ∀ j, SheafOfModules.IsInvertible T.subscheme.presheaf T.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback T.subschemeι).obj (L j)) := fun _ => isInvertible_pullback_obj _ _
  -- an integral multiple `G = ∑ⱼ nⱼ Eⱼ` with `𝒪(Eⱼ) ≅ Lⱼ` and `nⱼ = b lⱼ`
  obtain ⟨b, hb, n, hn⟩ := exists_pos_nat_mul_eq_intCast l
  have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  choose E hE using fun j => MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf (L j)
  set G : W.CartierDivisor := ∑ j, n j • E j with hG
  haveI : SheafOfModules.IsInvertible T.subscheme.presheaf T.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback T.subschemeι).obj (MMP.CartierDivisor.sheaf G)) :=
    isInvertible_pullback_obj _ _
  -- the value at `G` of an additive invariant of Cartier divisors
  have hval : ∀ (φ : W.CartierDivisor →+ ℤ) (ψ : Fin t → ℤ), (∀ j, φ (E j) = ψ j) →
      ((φ G : ℤ) : ℚ) = b * ∑ j, l j * (ψ j : ℚ) := by
    intro φ ψ hφ
    rw [hG, map_sum, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, smul_eq_mul, hφ j]
    push_cast
    rw [hn j]
    ring
  -- the restriction of `𝒪(G)` to `T` has degree zero on the curves of `T`
  have hdegT : ∀ P : ProperCurve (T.subschemeι ≫ (W ↘ Spec (.of ℂ))),
      P.degree ℂ ((Scheme.Modules.pullback T.subschemeι).obj (MMP.CartierDivisor.sheaf G)) = 0 := by
    intro P
    let δP : W.CartierDivisor →+ ℤ := AddMonoidHom.mk'
      (fun D => degreeOn ℂ (W ↘ Spec (.of ℂ)) (P.ι ≫ T.subschemeι) P.dim_le
        (MMP.CartierDivisor.sheaf D)) (degreeOn_sheaf_add _ _ _)
    have h := hval δP (fun j => P.degree ℂ ((Scheme.Modules.pullback T.subschemeι).obj (L j)))
      (fun j => (degreeOn_eq_of_iso _ _ _ _ (hE j).some).symm.trans
        (degreeOn_pullback _ _ _ _ _).symm)
    rw [hnull P, mul_zero] at h
    exact (degreeOn_pullback _ _ _ _ _).trans (by exact_mod_cast h)
  -- hence vanishing rational `c₁` on `T`, and on `W`
  have hcW : singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
      (algebraicFirstChernClass (MMP.CartierDivisor.sheaf G)) = 0 := by
    letI : T.subscheme.Over (Spec (.of ℂ)) := ⟨T.subschemeι ≫ (W ↘ Spec (.of ℂ))⟩
    haveI : AlgebraicGeometry.IsProjectiveVariety ℂ (T.subscheme ↘ Spec (.of ℂ)) :=
      isProjectiveVariety_subscheme hW T
    haveI : Smooth (T.subscheme ↘ Spec (.of ℂ)) := hTs
    have hcT := MMP.Analytic.mapCoeff_algebraicFirstChernClass_eq_zero_of_degreeOn_eq_zero hT2
      ((Scheme.Modules.pullback T.subschemeι).obj (MMP.CartierDivisor.sheaf G))
      (fun C i _ _ _ hC => degreeOn_eq_zero_of_forall_properCurve _ _ hdegT i hC)
    exact mapCoeff_eq_zero_of_restrict hW hdim T hTa hTs _ hcT
  refine ⟨fun C => ?_, ?_⟩
  · -- numerical triviality on `W`
    let δ : W.CartierDivisor →+ ℤ := AddMonoidHom.mk'
      (fun D => degreeOn ℂ (W ↘ Spec (.of ℂ)) C.ι C.dim_le (MMP.CartierDivisor.sheaf D))
      (degreeOn_sheaf_add _ _ _)
    have h := hval δ (fun j => C.degree ℂ (L j))
      (fun j => (degreeOn_eq_of_iso _ _ _ _ (hE j).some).symm)
    have h0' : ((δ G : ℤ) : ℚ) = 0 := by
      exact_mod_cast degree_eq_zero_of_mapCoeff_eq_zero hW hdim A hA G hcW C
    rw [h0'] at h
    exact (mul_eq_zero.1 h.symm).resolve_left hb0
  · -- the rational first Chern class
    have hχ : algebraicFirstChernClass (MMP.CartierDivisor.sheaf G) =
        ∑ j, n j • algebraicFirstChernClass (L j) := by
      let χ := AddMonoidHom.mk' (fun D : W.CartierDivisor =>
        algebraicFirstChernClass (MMP.CartierDivisor.sheaf D)) algebraicFirstChernClass_sheaf_add
      change χ G = _
      rw [hG, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_zsmul]
      congr 1
      exact (algebraicFirstChernClass_eq_of_iso (hE j).some).symm
    rw [hχ, map_sum] at hcW
    have h : (b : ℚ) • ∑ j, l j • singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
        (algebraicFirstChernClass (L j)) = 0 := by
      rw [Finset.smul_sum, ← hcW]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_zsmul, smul_smul, ← hn j, Int.cast_smul_eq_zsmul]
    exact (smul_eq_zero.1 h).resolve_left hb0

end Equality

end MMP.Fold06.ThmMmpConductorThreefoldDivisorIndex

namespace MMP.Mori

open MMP.Analytic MMP.Fold06.ThmMmpConductorThreefoldDivisorIndex
  Stacks.SheafOfModules.Invertible

/-- **The Hodge index inequality on a threefold.** Let `W` be a smooth projective complex
threefold, `A` an ample invertible sheaf and `L = ∑ⱼ lⱼ Lⱼ` a rational combination of
invertible sheaves with `(L · A²) = 0`. Then `(L² · A) ≤ 0`, and if `(L² · A) = 0` then
`∑ⱼ lⱼ deg_C Lⱼ = 0` for every proper curve `C ⊆ W` and `∑ⱼ lⱼ c₁(Lⱼ) = 0` in `H²(W, ℚ)`. -/
@[mmp "thm_mmp_conductor_threefold_divisor_index"]
public theorem sheafCombinationIntersectionNumber_two_nonpos_of_isAmple_of_dim_eq_three
    {W : Scheme.{0}} [W.Over (Spec (.of ℂ))] [IsProper (W ↘ Spec (.of ℂ))]
    [Smooth (W ↘ Spec (.of ℂ))] (hW : IsProjectiveVariety ℂ (W ↘ Spec (.of ℂ)))
    (hdim : topologicalKrullDim W = 3)
    (A : W.Modules) [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 A]
    [Stacks.Ample.IsInvertibleModule W A] (hA : Stacks.Ample.IsAmple W A)
    {t : ℕ} (l : Fin t → ℚ) (L : Fin t → W.Modules)
    [∀ j, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 (L j)] :
    haveI : ∀ j : Fin 1, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2
        ((![A] : Fin 1 → W.Modules) j) := fun _ => by simpa
    haveI : ∀ j : Fin 2, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2
        ((![A, A] : Fin 2 → W.Modules) j) := fun j => by fin_cases j <;> simpa
    sheafCombinationIntersectionNumber ℂ (W ↘ Spec (.of ℂ)) (𝟙 W) ℚ l L 1 ![A, A]
        (by rw [hdim]; rfl) = 0 →
    sheafCombinationIntersectionNumber ℂ (W ↘ Spec (.of ℂ)) (𝟙 W) ℚ l L 2 ![A]
        (by rw [hdim]; rfl) ≤ 0 ∧
      (sheafCombinationIntersectionNumber ℂ (W ↘ Spec (.of ℂ)) (𝟙 W) ℚ l L 2 ![A]
          (by rw [hdim]; rfl) = 0 →
        (∀ C : ProperCurve (W ↘ Spec (.of ℂ)), ∑ j, l j * (C.degree ℂ (L j) : ℚ) = 0) ∧
          ∑ j, l j • singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
            (algebraicFirstChernClass (L j)) = 0) := by
  haveI : ∀ j : Fin 1, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2
      ((![A] : Fin 1 → W.Modules) j) := fun _ => by simpa
  haveI : ∀ j : Fin 2, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2
      ((![A, A] : Fin 2 → W.Modules) j) := fun j => by fin_cases j <;> simpa
  intro hLA
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ (W ↘ Spec (.of ℂ)) := hW
  haveI : IsIntegral W := hW.toIsVariety.toIsIntegral
  have hd3 : topologicalKrullDim W ≤ (3 : ℕ) := by rw [hdim]; rfl
  -- a smooth integral member `T ∈ |A^{⊗ ν}|`
  obtain ⟨ν, hν, hslice⟩ :=
    exists_slice hW (by rw [hdim]; exact_mod_cast (by norm_num : (2 : ℕ) ≤ 3)) A hA
  obtain ⟨T, hT, hTi, hTs, ⟨eT⟩⟩ := hslice ν le_rfl
  haveI := hT
  haveI := hTi
  have hT2 : topologicalKrullDim T.subscheme = (2 : ℕ) :=
    topologicalKrullDim_subscheme_of_isEffectiveCartierDivisor ℂ (W ↘ Spec (.of ℂ)) T hT
      (d := 2) (by rw [hdim]; rfl)
  let e : tensorPower W.presheaf W.ringCatSheaf.2 A (ν : ℤ) ≅
      Stacks.Divisors.invertibleSheaf' T :=
    Stacks.PowerFamilyBridge.tensorPowerModuleIso W A ν ≪≫ eT
  have key := intersectionNumber_restrict_eq_mul (W ↘ Spec (.of ℂ)) T hd3 hT2.le A ν e
  -- the surface `T`
  haveI hMT : ∀ j, SheafOfModules.IsInvertible T.subscheme.presheaf T.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback T.subschemeι).obj (L j)) := fun j => isInvertible_pullback_obj _ _
  haveI hHT : SheafOfModules.IsInvertible T.subscheme.presheaf T.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback T.subschemeι).obj A) := isInvertible_pullback_obj _ _
  haveI : Stacks.Ample.IsInvertibleModule T.subscheme
      ((Scheme.Modules.pullback T.subschemeι).obj A) :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hHT
  have hHa : Stacks.Ample.IsAmple T.subscheme ((Scheme.Modules.pullback T.subschemeι).obj A) :=
    (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple _ _).1
      (Scheme.Modules.isAmple_pullback_of_isClosedImmersion T.subschemeι A
        ((Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple _ _).2 hA))
  have hSp := isProjectiveVariety_subscheme hW T
  have hS2 : topologicalKrullDim T.subscheme = 2 := by exact_mod_cast hT2
  haveI : Smooth (T.subschemeι ≫ (W ↘ Spec (.of ℂ))) := hTs
  haveI : ∀ j : Fin 1, SheafOfModules.IsInvertible T.subscheme.presheaf T.subscheme.ringCatSheaf.2
      ((![(Scheme.Modules.pullback T.subschemeι).obj A] : Fin 1 → T.subscheme.Modules) j) :=
    fun _ => by simpa
  haveI : ∀ j : Fin 0, SheafOfModules.IsInvertible T.subscheme.presheaf T.subscheme.ringCatSheaf.2
      ((![] : Fin 0 → T.subscheme.Modules) j) := fun j => j.elim0
  -- the two numbers on `T` are `ν` times those on `W`
  have hT1v : sheafCombinationIntersectionNumber ℂ (T.subschemeι ≫ (W ↘ Spec (.of ℂ)))
      (𝟙 T.subscheme) ℚ l (fun j => (Scheme.Modules.pullback T.subschemeι).obj (L j)) 1
      ![(Scheme.Modules.pullback T.subschemeι).obj A] (by rw [hS2]; rfl) = 0 := by
    rw [combo_one_single _ _ _ _ _ _ hT2.le, ← mul_zero (ν : ℚ), ← hLA,
      combo_one_pair _ _ _ _ _ _ _ hd3, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [key (L j) A]
    ring
  have hT2v : sheafCombinationIntersectionNumber ℂ (T.subschemeι ≫ (W ↘ Spec (.of ℂ)))
      (𝟙 T.subscheme) ℚ l (fun j => (Scheme.Modules.pullback T.subschemeι).obj (L j)) 2
      ![] hT2.le = (ν : ℚ) * sheafCombinationIntersectionNumber ℂ
        (W ↘ Spec (.of ℂ)) (𝟙 W) ℚ l L 2 ![A] (by rw [hdim]; rfl) := by
    rw [combo_two_empty _ _ _ _ _ hT2.le, combo_two_single _ _ _ _ _ _ hd3, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [key (L p) (L q)]
    ring
  have hν' : (0 : ℚ) < ν := by exact_mod_cast hν
  have hsurf := sheafCombinationIntersectionNumber_two_nonpos_of_isAmple ℂ
    (T.subschemeι ≫ (W ↘ Spec (.of ℂ))) hSp hS2 _ hHa l
    (fun j => (Scheme.Modules.pullback T.subschemeι).obj (L j)) hT1v
  rw [hT2v] at hsurf
  refine ⟨nonpos_of_mul_nonpos_right (by linarith) hν', fun h0 => ?_⟩
  have hnull := (sheafCombinationIntersectionNumber_two_eq_zero_iff_of_isAmple ℂ
    (T.subschemeι ≫ (W ↘ Spec (.of ℂ))) hSp hS2 _ hHa l
    (fun j => (Scheme.Modules.pullback T.subschemeι).obj (L j)) hT1v).1
      (by rw [hT2v, h0, mul_zero])
  haveI : Stacks.Ample.IsInvertibleModule W (Stacks.Divisors.divisorSheaf T) :=
    Stacks.Divisors.isInvertible_divisorSheaf T
  have hTa : Stacks.Ample.IsAmple W (Stacks.Divisors.divisorSheaf T) :=
    (Stacks.RelativeVeryAmple.isAmple_congr _ _ eT).1
      (Stacks.AmplePositivePower.isAmple_tensorPowModule_of_isAmple A ν hν hA)
  exact equality_case hW hdim A hA T hTa hTs hS2 l L hnull

end MMP.Mori
