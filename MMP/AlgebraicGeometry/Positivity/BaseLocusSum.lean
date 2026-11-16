module

public import MMP.AlgebraicGeometry.Divisor.LinearSystem
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Basic
public import MMP.AlgebraicGeometry.Intersection.Nef

/-!
# Base loci of sums and nef thresholds (KM 3.2, 3.5)

* `Bs|M₁ + M₂| ⊆ Bs|M₁| ∪ Bs|M₂|`: products of sections.
* For a proper normal variety `X`, a `ℚ`-Cartier `ℚ`-divisor `K` which is not nef and a nef
  `ℚ`-Cartier `ℚ`-divisor `H`, the set `T = {t : H + tK nef}` is a closed interval containing `0`
  with a largest element `r ≥ 0`, the unique nef threshold of `H` with respect to `K`.

## Main results

* `MMP.Positivity.baseLocus_add_le`
* `MMP.Positivity.exists_isNefThreshold`

## Implementation notes

The base-locus inclusion is stated for all divisors on a normal integral scheme, quasi-compact
and locally Noetherian; KM state it for Cartier divisors on a proper normal variety.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Positivity

open MMP.Mori

namespace Divisor

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]

/-- The product `σ₁ σ₂ ∈ H⁰(X, 𝒪_X(M₁ + M₂))` of global sections `σᵢ ∈ H⁰(X, 𝒪_X(Mᵢ))`. -/
def sectionMul {M₁ M₂ : Divisor X} (σ₁ : M₁.divisorialSubmodule ⊤)
    (σ₂ : M₂.divisorialSubmodule ⊤) : (M₁ + M₂).divisorialSubmodule ⊤ :=
  ⟨σ₁.1 * σ₂.1, Mori.Divisor.IsDivisorialSection.mul σ₁.2 σ₂.2⟩

/-- The rational function of the product section `sectionMul σ₁ σ₂` is the product of the rational
functions of `σ₁` and `σ₂`. -/
theorem sectionToRationalFunctions_sectionMul {M₁ M₂ : Divisor X}
    (σ₁ : M₁.divisorialSubmodule ⊤) (σ₂ : M₂.divisorialSubmodule ⊤) :
    Mori.Divisor.sectionToRationalFunctions (sectionMul σ₁ σ₂) =
      Mori.Divisor.sectionToRationalFunctions σ₁ * Mori.Divisor.sectionToRationalFunctions σ₂ :=
  map_mul (rationalFunctionsPresheafTopEquiv X) _ _

variable [CompactSpace X] [IsIntegral X]

omit [CompactSpace X] in
/-- The product of two nonzero global sections is nonzero. -/
theorem sectionMul_ne_zero {M₁ M₂ : Divisor X} {σ₁ : M₁.divisorialSubmodule ⊤}
    {σ₂ : M₂.divisorialSubmodule ⊤} (h₁ : σ₁ ≠ 0) (h₂ : σ₂ ≠ 0) : sectionMul σ₁ σ₂ ≠ 0 := by
  intro h
  have hu := (Mori.Divisor.isUnit_sectionToRationalFunctions h₁).mul
    (Mori.Divisor.isUnit_sectionToRationalFunctions h₂)
  rw [← sectionToRationalFunctions_sectionMul, h] at hu
  change IsUnit (rationalFunctionsPresheafTopEquiv X 0) at hu
  rw [map_zero, isUnit_zero_iff] at hu
  refine Mori.Divisor.sectionToRationalFunctions_ne_zero h₁ ?_
  rw [← mul_one (Mori.Divisor.sectionToRationalFunctions σ₁), ← hu, mul_zero]

/-- The divisor of zeros of the product `σ₁ σ₂` of nonzero sections is the sum of the divisors of
zeros of `σ₁` and `σ₂`. -/
theorem zeroDivisor_sectionMul {M₁ M₂ : Divisor X} {σ₁ : M₁.divisorialSubmodule ⊤}
    {σ₂ : M₂.divisorialSubmodule ⊤} (h₁ : σ₁ ≠ 0) (h₂ : σ₂ ≠ 0) :
    (M₁ + M₂).zeroDivisor (sectionMul σ₁ σ₂) (sectionMul_ne_zero h₁ h₂) =
      M₁.zeroDivisor σ₁ h₁ + M₂.zeroDivisor σ₂ h₂ := by
  have hu : (Mori.Divisor.isUnit_sectionToRationalFunctions (sectionMul_ne_zero h₁ h₂)).unit =
      (Mori.Divisor.isUnit_sectionToRationalFunctions h₁).unit *
        (Mori.Divisor.isUnit_sectionToRationalFunctions h₂).unit :=
    Units.ext (sectionToRationalFunctions_sectionMul σ₁ σ₂)
  rw [Mori.Divisor.zeroDivisor_eq, Mori.Divisor.zeroDivisor_eq, Mori.Divisor.zeroDivisor_eq, hu,
    Mori.principalDivisor_mul]
  abel

end Divisor

/-- **KM 3.2 Step 2.** `Bs|M₁ + M₂| ⊆ Bs|M₁| ∪ Bs|M₂|`. -/
@[mmp "lem_km3a_base_locus_of_sum"]
theorem baseLocus_add_le {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral X] (M₁ M₂ : Divisor X) :
    (M₁ + M₂).baseLocus ≤ M₁.baseLocus ⊔ M₂.baseLocus := by
  intro x hx
  by_contra hne
  have hne' : x ∉ (M₁.baseLocus : Set X) ∧ x ∉ (M₂.baseLocus : Set X) := by
    rwa [← SetLike.mem_coe, Closeds.coe_sup, Set.mem_union, not_or] at hne
  simp only [Mori.Divisor.mem_baseLocus_iff, not_forall] at hne'
  obtain ⟨⟨σ₁, h₁, hx₁⟩, ⟨σ₂, h₂, hx₂⟩⟩ := hne'
  have h := (Mori.Divisor.mem_baseLocus_iff _ x).mp hx _ (Divisor.sectionMul_ne_zero h₁ h₂)
  rw [Divisor.zeroDivisor_sectionMul h₁ h₂] at h
  rcases DivisorWithCoeffs.supp_add_le _ _ h with h | h
  · exact hx₁ h
  · exact hx₂ h

section NefThreshold

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
  [IsLocallyNoetherian X] [IsNormal X]

/-- The definition of `H + tK` being nef, for given proofs of the `ℚ`-Cartier conditions. -/
theorem isNefCombination_iff {H K : QDivisor X} (hH : H.IsQCartier) (hK : K.IsQCartier)
    (t : ℝ) : QDivisor.IsNefCombination k sX H K t ↔
      ∀ (C : Scheme.{u}) (i : C ⟶ X) [IsClosedImmersion i] [IsIntegral C] [IsProper (i ≫ sX)]
        (hC : topologicalKrullDim C = 1),
        0 ≤ (H.intersectionNumber k sX i hC.le hH : ℝ) +
          t * (K.intersectionNumber k sX i hC.le hK) :=
  ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨hH, hK, h⟩⟩

/-- The set of `t` with `H + tK` nef is convex. -/
theorem convex_setOf_isNefCombination {H K : QDivisor X} (hH : H.IsQCartier)
    (hK : K.IsQCartier) : Convex ℝ {t : ℝ | QDivisor.IsNefCombination k sX H K t} := by
  intro x hx y hy a b ha hb hab
  refine (isNefCombination_iff hH hK _).2 fun C i _ _ _ hC => ?_
  have h₁ := (isNefCombination_iff hH hK x).1 hx C i hC
  have h₂ := (isNefCombination_iff hH hK y).1 hy C i hC
  set A : ℝ := (H.intersectionNumber k sX i hC.le hH : ℝ)
  set B : ℝ := (K.intersectionNumber k sX i hC.le hK : ℝ)
  have e : A + (a • x + b • y) * B = a * (A + x * B) + b * (A + y * B) := by
    rw [smul_eq_mul, smul_eq_mul]
    linear_combination (-A) * hab
  rw [e]
  exact add_nonneg (mul_nonneg ha h₁) (mul_nonneg hb h₂)

/-- The set of `t` with `H + tK` nef is closed. -/
theorem isClosed_setOf_isNefCombination {H K : QDivisor X} (hH : H.IsQCartier)
    (hK : K.IsQCartier) : IsClosed {t : ℝ | QDivisor.IsNefCombination k sX H K t} := by
  refine isClosed_of_closure_subset fun t ht => (isNefCombination_iff hH hK t).2
    fun C i _ _ _ hC => ?_
  have hcl : IsClosed {s : ℝ | 0 ≤ (H.intersectionNumber k sX i hC.le hH : ℝ) +
      s * (K.intersectionNumber k sX i hC.le hK)} :=
    isClosed_le continuous_const (by fun_prop)
  exact closure_minimal (fun s hs => (isNefCombination_iff hH hK s).1 hs C i hC) hcl ht

/-- If `K` is `ℚ`-Cartier and not nef, the set of `t` with `H + tK` nef is bounded above. -/
theorem bddAbove_setOf_isNefCombination {H K : QDivisor X} (hH : H.IsQCartier)
    (hKq : K.IsQCartier) (hK : ¬ QDivisor.IsNef k sX K) :
    BddAbove {t : ℝ | QDivisor.IsNefCombination k sX H K t} := by
  rw [QDivisor.isNef_iff K hKq] at hK
  push Not at hK
  obtain ⟨C, i, _, _, _, hC, hneg⟩ := hK
  have hneg' : ((K.intersectionNumber k sX i hC.le hKq : ℚ) : ℝ) < 0 := by exact_mod_cast hneg
  refine ⟨-(H.intersectionNumber k sX i hC.le hH : ℝ) / (K.intersectionNumber k sX i hC.le hKq),
    fun t ht => ?_⟩
  have h := (isNefCombination_iff hH hKq t).1 ht C i hC
  rw [le_div_iff_of_neg hneg']
  linarith

end NefThreshold

/-- **KM Thm. 3.5, the nef threshold exists.** Let `X` be a proper normal variety, `K` a
`ℚ`-Cartier `ℚ`-divisor on `X` which is not nef and `H` a nef `ℚ`-Cartier `ℚ`-divisor. Then
`T = {t ∈ ℝ : H + tK nef}` is a closed interval containing `0` with a largest element `r ≥ 0`, and
`r` is the unique nef threshold of `H` with respect to `K`. Only properness of `X` and normality
are used, not that `X` is a variety. -/
@[mmp "lem_km3a_nef_threshold_exists"]
theorem exists_isNefThreshold {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsLocallyNoetherian X] [IsNormal X] [IsProper sX]
    {H K : QDivisor X} (hKq : K.IsQCartier) (hK : ¬ QDivisor.IsNef k sX K)
    (hH : QDivisor.IsNef k sX H) :
    ∃ r : ℝ, 0 ≤ r ∧
      Convex ℝ {t : ℝ | QDivisor.IsNefCombination k sX H K t} ∧
      IsClosed {t : ℝ | QDivisor.IsNefCombination k sX H K t} ∧
      (0 : ℝ) ∈ {t : ℝ | QDivisor.IsNefCombination k sX H K t} ∧
      IsGreatest {t : ℝ | QDivisor.IsNefCombination k sX H K t} r ∧
      ∀ r' : ℝ, QDivisor.IsNefThreshold k sX H K r' ↔ r' = r := by
  set T := {t : ℝ | QDivisor.IsNefCombination k sX H K t} with hT
  have hHq := hH.isQCartier
  have h0 : (0 : ℝ) ∈ T := (isNefCombination_iff hHq hKq 0).2 fun C i _ _ _ hC => by
    simpa using (QDivisor.isNef_iff H hHq).1 hH C i hC
  have hcl : IsClosed T := isClosed_setOf_isNefCombination hHq hKq
  have hbdd : BddAbove T := bddAbove_setOf_isNefCombination hHq hKq hK
  have hmem : sSup T ∈ T := hcl.csSup_mem ⟨0, h0⟩ hbdd
  have hgr : IsGreatest T (sSup T) := ⟨hmem, fun _ ht => le_csSup hbdd ht⟩
  refine ⟨sSup T, hgr.2 h0, convex_setOf_isNefCombination hHq hKq, hcl, h0, hgr,
    fun r' => ⟨fun h => ?_, ?_⟩⟩
  · refine le_antisymm (hgr.2 h.1) (not_lt.mp fun hlt => h.2 _ hlt hmem)
  · rintro rfl
    exact ⟨hmem, fun t ht htT => (not_le.mpr ht) (hgr.2 htT)⟩

end MMP.Positivity
