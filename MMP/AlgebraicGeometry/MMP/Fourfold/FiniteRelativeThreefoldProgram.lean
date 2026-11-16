module

public import MMP.AlgebraicGeometry.MMP.Fourfold.Flip
public import MMP.AlgebraicGeometry.MMP.Fourfold.DltProgram

/-!
# Finite relative threefold programmes

Let `Z` be a normal projective complex variety and `(V, Θ)` an effective rational klt pair on a
normal projective `ℚ`-factorial complex threefold, with a morphism `π : V ⟶ Z`. A *finite
relative programme over `Z` from `(V, Θ)`* is a finite sequence of threefold step diagrams
`(V_k, Θ_k) → T_k ← (V_{k+1}, Θ_{k+1})`, `0 ≤ k < m`, starting at `(V₀, Θ₀) = (V, Θ)`, together
with morphisms `π_k : V_k ⟶ Z` (`π₀ = π`) and `h_k : T_k ⟶ Z` with `π_k = h_k ∘ g_k` and
`π_{k+1} = h_k ∘ g_k⁺`, in which every `V_k` is `ℚ`-factorial and every `g_k` is the contraction
of a `(K_{V_k} + Θ_k)`-negative extremal ray `R_k` of `NE̅(V_k)`, spanned by the class of an
integral curve contracted by `π_k`, with `ρ(V_k/T_k) = 1`.

## Main definitions

* `MMP.Fourfold.RelativeThreefoldProgram`: finite relative threefold programmes.
* `MMP.Fourfold.RelativeThreefoldProgram.boundary`: the boundaries `Θ_k` of its models.

## Implementation notes

The models are `V₀ = V` and `V_{k+1} = Y k`, as for `MMP.Fourfold.Program`; the data indexed by
`k > m` (models) and `k ≥ m` (steps) are unconstrained. The canonical divisors `K_k` of the models
are cut out by one rational top form: `K₀ = K` is a canonical divisor of `V` and
`K_{k+1} = (g_k⁺)⁻¹_* (g_k)_* K_k`, the convention of `MMP.Fourfold.IsThreefoldStepDiagram`, which
also forces `Θ_{k+1} = (g_k⁺)⁻¹_* (g_k)_* Θ_k`. The morphisms `π` and `h_k` are morphisms of
complex varieties, that is, commute with the structure morphisms.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

section RelativeProgram

variable {V Z : Scheme.{0}} [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V]
  (sV : V ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) (π : V ⟶ Z)

/-- A *finite relative programme over `Z` from `(V, Θ)`*, with canonical divisor `K` of `V`. The
setting: `Z` is a normal projective complex variety, `V` a normal projective `ℚ`-factorial
complex threefold, `(V, Θ)` an effective rational klt pair and `π : V ⟶ Z` a morphism over `ℂ`.
The data: a number `m ∈ ℕ` of steps; models `V₀ = V`, `V_{k+1} = Y k` with canonical divisors
`K_k` (`K₀ = K`) and boundaries `Θ_k` (`Θ₀ = Θ`); morphisms `π_k : V_k ⟶ Z` (`π₀ = π`); and for
each `k < m` a threefold step diagram `(V_k, Θ_k) → T_k ← (V_{k+1}, Θ_{k+1})` by `g_k`, `g_k⁺`
(`MMP.Fourfold.IsThreefoldStepDiagram`) with `K_{k+1}`, `Θ_{k+1}` the strict transforms of `K_k`,
`Θ_k`, a morphism `h_k : T_k ⟶ Z` over `ℂ` with `π_k = g_k ≫ h_k` and `π_{k+1} = g_k⁺ ≫ h_k`,
and an extremal ray `R_k` of `NE̅(V_k)`, such that every `V_k`, `k ≤ m`, is `ℚ`-factorial and, for
`k < m`, `R_k` is `(K_k + Θ_k)`-negative and spanned by the class `[C]` of an integral curve `C`
contracted by `π_k`, `g_k` is the contraction of `R_k` and `ρ(V_k/T_k) = 1`. -/
@[mmp "def_mmp_indexc_relative_program"]
structure RelativeThreefoldProgram (K : Divisor V) (Θ : QDivisor V) where
  /-- The number `m` of steps. -/
  m : ℕ
  /-- The models after the first: `V_{k+1} = Y k`. -/
  Y : ℕ → Scheme.{0}
  /-- The structure morphisms `V_{k+1} ⟶ Spec ℂ`. -/
  sY : ∀ k, Y k ⟶ Spec (.of ℂ)
  [isIntegral : ∀ k, IsIntegral (Y k)]
  [compactSpace : ∀ k, CompactSpace (Y k)]
  [isLocallyNoetherian : ∀ k, IsLocallyNoetherian (Y k)]
  [isNormal : ∀ k, IsNormal (Y k)]
  /-- The canonical divisor `K_{k+1}` of `V_{k+1}`. -/
  KY : ∀ k, Divisor (Y k)
  /-- The boundary `Θ_{k+1}` on `V_{k+1}`. -/
  ΘY : ∀ k, QDivisor (Y k)
  /-- The morphism `π_{k+1} : V_{k+1} ⟶ Z`. -/
  πY : ∀ k, Y k ⟶ Z
  /-- The base `T_k` of the `k`-th step diagram. -/
  T : ℕ → Scheme.{0}
  /-- The structure morphism `T_k ⟶ Spec ℂ`. -/
  sT : ∀ k, T k ⟶ Spec (.of ℂ)
  /-- The morphism `g_k : V_k ⟶ T_k`. -/
  g : ∀ k, modelSeq V Y k ⟶ T k
  /-- The morphism `g_k⁺ : V_{k+1} ⟶ T_k`. -/
  gp : ∀ k, Y k ⟶ T k
  /-- The morphism `h_k : T_k ⟶ Z`. -/
  h : ∀ k, T k ⟶ Z
  /-- The extremal ray `R_k ⊆ N₁(V_k)_ℝ`. -/
  R : ∀ k, Set (NumericalCurveClasses (modelStr sV sY k))
  isProjectiveVariety_base : MMP.Mori.IsProjectiveVariety ℂ sZ
  isNormalVariety_base : IsNormalVariety ℂ sZ
  isProjectiveVariety : MMP.Mori.IsProjectiveVariety ℂ sV
  dim_eq : topologicalKrullDim V = 3
  isKltPair : IsKltPair sV Θ
  isCanonicalDivisor : ∃ n : ℕ, K.IsCanonicalDivisor sV n
  comp_eq : π ≫ sZ = sV
  isQFactorial : ∀ k ≤ m, IsQFactorial (modelStr sV sY k)
  isThreefoldStepDiagram : ∀ k < m,
    IsThreefoldStepDiagram (modelStr sV sY k) (sT k) (sY k) (divisorSeq K KY k)
      (divisorSeq Θ ΘY k) (g k) (gp k)
  KY_eq : ∀ k < m, KY k = flipTransform (g k) (gp k) (divisorSeq K KY k)
  ΘY_eq : ∀ k < m, ΘY k = flipTransform (g k) (gp k) (divisorSeq Θ ΘY k)
  comp_eq_base : ∀ k < m, h k ≫ sZ = sT k
  modelMap_eq : ∀ k < m, modelMap π πY k = g k ≫ h k
  πY_eq : ∀ k < m, πY k = gp k ≫ h k
  isNegativeExtremalRayOf : ∀ k < m,
    IsNegativeExtremalRayOf (modelStr sV sY k)
      (Divisor.toQDivisor (divisorSeq K KY k) + divisorSeq Θ ΘY k) (R k)
  exists_ray_eq : ∀ k < m, ∃ C : ProperCurve (modelStr sV sY k),
    C.IsContractedBy (modelMap π πY k) ∧
      R k = {u | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass _ (C.cycle ℝ) = u}
  isContractionOfRay : ∀ k < m, IsContractionOfRay (modelStr sV sY k) (sT k) (R k) (g k)
  relativePicardNumber_eq_one : ∀ k < m, relativePicardNumberN1 (modelStr sV sY k) (g k) = 1

attribute [instance] RelativeThreefoldProgram.isIntegral RelativeThreefoldProgram.compactSpace
  RelativeThreefoldProgram.isLocallyNoetherian RelativeThreefoldProgram.isNormal

namespace RelativeThreefoldProgram

variable {sV sZ π} {K : Divisor V} {Θ : QDivisor V} (P : RelativeThreefoldProgram sV sZ π K Θ)

/-- The boundary `Θ_k` on the model `V_k` of a finite relative programme; its *models* are the
pairs `(V_k, Θ_k)`, `k ≤ m`, and its *end* is `(V_m, Θ_m)`. -/
abbrev boundary (k : ℕ) : QDivisor (modelSeq V P.Y k) := divisorSeq Θ P.ΘY k

/-- The boundary `Θ₀` of the initial model is `Θ`. -/
@[simp]
theorem boundary_zero : P.boundary 0 = Θ := rfl

/-- The boundary `Θ_{k+1}` of the model `V_{k+1}` is `ΘY k`. -/
@[simp]
theorem boundary_succ (k : ℕ) : P.boundary (k + 1) = P.ΘY k := rfl

/-- The boundary of each later model is the strict transform of the previous one. -/
theorem boundary_succ_eq_flipTransform {k : ℕ} (hk : k < P.m) :
    P.boundary (k + 1) = flipTransform (P.g k) (P.gp k) (P.boundary k) :=
  P.ΘY_eq k hk

/-- The morphism `π_{k+1}` factors through the base of the `k`-th step diagram. -/
theorem modelMap_succ_eq {k : ℕ} (hk : k < P.m) :
    modelMap π P.πY (k + 1) = P.gp k ≫ P.h k :=
  P.πY_eq k hk

end RelativeThreefoldProgram

end RelativeProgram

end MMP.Fourfold
