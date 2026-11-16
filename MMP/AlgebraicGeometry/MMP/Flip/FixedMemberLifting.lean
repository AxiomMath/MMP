module

public import MMP.AlgebraicGeometry.Singularities.AdjointIdeal.AsymptoticExtension
public import MMP.AlgebraicGeometry.Positivity.RelativeAmpleBasics
public import MMP.AlgebraicGeometry.Singularities.PltDifferentCoefficients

/-!
# Lifting below the asymptotic restricted fixed divisor, for a fixed ample member

Let `f : X ⟶ Z` be projective with `Z` normal and affine and `X` smooth of dimension at least
two, `S` a smooth prime divisor, `B ≥ 0` not containing `S`, `H ≥ 0` an `f`-ample Cartier divisor,
`a ≥ 3`, `A = H/a`, `Δ = S + A + B` and `D = K_X + Δ`. Let `F` be the asymptotic fixed part of the
restricted systems `|mD|_S`. The lifting theorem below `F` is stated in the source for a
sufficiently general member `H` of a relatively ample system. Its proof uses the generality of `H`
only through two properties of the pair: `(X, Δ + C)` is plt with `⌊Δ + C⌋ = S` for `C = A/c`, and
no component of `C|_S` lies in `F`. Both follow for one fixed `H` from the following hypotheses:
`(X, Δ + A)` is plt, `⌊Δ⌋ = S`, `cΔ` is integral, and no component of `H|_S` lies in `F`.

* For `c ≥ 2`: a component `E ≠ S` of `A` has `Δ_E + A_E/c < Δ_E + A_E ≤ 1`, because the
  coefficients of an lc boundary are at most one in dimension at least two.
* For `c = 1`: `Δ` is integral with `⌊Δ⌋ = S`, so `A` has no component other than `S`.

## Main results

* `MMP.Fourfold.exists_isRestrictionAlong_of_le_restrictedAsymptoticFixedPart_of_isPltPair_add`:
  every section of `𝒪_S(c(K_S + Ω - Φ))` is the restriction of a section of `𝒪_X(cD)`.

## References

* The fourfold source, *Section lifting*.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori MMP.Proof_thm_fourfold_asymptotic_section_lifting

/-- **Lifting below the asymptotic restricted fixed divisor, for a fixed ample member.** Let
`f : X ⟶ Z` be a projective morphism to a normal affine scheme from a smooth variety `X` of
dimension `n ≥ 2` over an algebraically closed field `k` of characteristic zero, with canonical
divisor `K_X`, `S` a smooth prime divisor with `K_X` of coefficient `-1` along `S`,
`K_S = (K_X + S)|_S`, `B ≥ 0` a `ℚ`-divisor not containing `S`, `H ≥ 0` an `f`-ample Cartier
divisor and `a ≥ 3`. Put `A = H/a`, `Δ = S + A + B`, `D = K_X + Δ`, `Ω = (A + B)|_S` and let `F`
be the asymptotic fixed part of the restricted systems `|mD|_S`. Assume `S ⊄ H`,
`(X, Δ + A)` is plt, `⌊Δ⌋ = S`, `(S, Ω + A|_S)` is canonical, some `mD` with `m > 0` has a
section not vanishing along `S`, and `H|_S` has no component in the support of `F`. Let
`0 < ε < 1` be rational with `εD + A` `f`-ample, `c > 0` with `cΔ` integral, and `Φ` a
`ℚ`-divisor on `S` with `cΦ` integral and `Ω ∧ (1 - ε/c)F ≤ Φ ≤ Ω`. Then every section of
`𝒪_S(c(K_S + Ω - Φ))` is the restriction of a section of `𝒪_X(cD)`. -/
theorem exists_isRestrictionAlong_of_le_restrictedAsymptoticFixedPart_of_isPltPair_add
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X Z : Scheme.{0}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (hX : IsNormalVariety k sX) (hXs : IsSmoothScheme sX)
    (f : X ⟶ Z) (hf : IsProjectiveMorphism f) [IsAffine Z] [IsNormal Z]
    (n : ℕ) (hn : 2 ≤ n) (KX : Divisor X) (hKX : KX.IsCanonicalDivisor sX n)
    (S : MMP.Mori.PrimeDivisor X) (hKXS : KX.coeff S = -1)
    [IsLocallyNoetherian S.idealSheaf.subscheme] [IsNormal S.idealSheaf.subscheme]
    [CompactSpace S.idealSheaf.subscheme]
    (hSs : IsSmoothScheme (S.idealSheaf.subschemeι ≫ sX))
    (B : QDivisor X) (hB0 : 0 ≤ B) (hBS : B.coeff S = 0)
    (H : Divisor X) (hH0 : 0 ≤ H) (hHa : MMP.Flips.IsRelativelyAmpleCartier f H)
    (a : ℕ) (ha : 3 ≤ a) :
    haveI := S.integral
    let A : QDivisor X := (a : ℚ)⁻¹ • Divisor.toQDivisor H
    let Δ : QDivisor X := Divisor.toQDivisor (Finsupp.single S 1) + A + B
    let D : QDivisor X := Divisor.toQDivisor KX + Δ
    let KS : Divisor S.idealSheaf.subscheme := (KX + Finsupp.single S 1).restrictPrimeDivisor S
    let Ω : QDivisor S.idealSheaf.subscheme := (A + B).restrictPrimeDivisor S
    let V : ℕ → Submodule ℤ (RationalFunctions S.idealSheaf.subscheme) := fun m =>
      AddSubgroup.toIntSubmodule <| AddSubgroup.closure
        {h | ((m : ℚ) • D).IsCartierDivisor ∧
          ∃ g ∈ sectionsIn (DivisorWithCoeffs.roundDown ((m : ℚ) • D)),
            IsRestrictionAlong S g (rationalFunctionsEquivFunctionField _ h)}
    let F := restrictedAsymptoticFixedPart KS Ω 1 V
    H.coeff S = 0 →
    MMP.Mori.IsPltPair sX n KX (Δ + A) →
    DivisorWithCoeffs.roundDown Δ = Finsupp.single S 1 →
    IsRealCanonicalPair (S.idealSheaf.subschemeι ≫ sX)
      (QDivisor.toRDivisor (Ω + A.restrictPrimeDivisor S)) →
    (∃ m : ℕ, 0 < m ∧ ((m : ℚ) • D).IsCartierDivisor ∧
      ∃ σ ∈ sectionsIn (DivisorWithCoeffs.roundDown ((m : ℚ) • D)),
        S.divisorialValuation σ =
          WithZero.exp ((DivisorWithCoeffs.roundDown ((m : ℚ) • D)).coeff S)) →
    (∀ G, (H.restrictPrimeDivisor S).coeff G ≠ 0 → F G = 0) →
    ∀ ε : ℚ, 0 < ε → ε < 1 → (ε • D + A).HasRelativelyAmpleMultiple f →
    ∀ c : ℕ, 0 < c → ((c : ℚ) • Δ).IsCartierDivisor →
    ∀ Φ : QDivisor S.idealSheaf.subscheme, ((c : ℚ) • Φ).IsCartierDivisor →
      coeffwiseMin Ω (fun G => ENNReal.ofReal (1 - (ε : ℝ) / c) * F G) ≤
        QDivisor.toRDivisor Φ →
      Φ ≤ Ω →
      ∀ u ∈ sectionsIn (DivisorWithCoeffs.roundDown
          ((c : ℚ) • (Divisor.toQDivisor KS + Ω - Φ))),
        ∃ g ∈ sectionsIn (DivisorWithCoeffs.roundDown ((c : ℚ) • D)),
          IsRestrictionAlong S g u := by
  haveI := S.integral
  intro A Δ D KS Ω V F hHS hplt' hfloor hcan hsec hHF ε hε0 hε1 hεA c hc hcΔ Φ hcΦ hΦlo hΦhi
    u hu
  have ha0 : (0 : ℚ) < a := by exact_mod_cast (show 0 < a by omega)
  have hA0 : 0 ≤ A := fun P => by
    have := hH0 P
    change (0 : ℚ) ≤ (a : ℚ)⁻¹ * ((H P : ℤ) : ℚ)
    exact mul_nonneg (inv_nonneg.mpr ha0.le) (by exact_mod_cast this)
  have hAS : A.coeff S = 0 := by
    change (a : ℚ)⁻¹ * ((H.coeff S : ℤ) : ℚ) = 0
    rw [hHS]; simp
  have hcq : (1 : ℚ) ≤ c := by exact_mod_cast hc
  have hpltC : IsPltPair sX n KX
      (Divisor.toQDivisor (Finsupp.single S 1) + A + B + (c : ℚ)⁻¹ • A) := by
    have hrem : 0 ≤ (1 - (c : ℚ)⁻¹) • A :=
      smul_nonneg (sub_nonneg.mpr (inv_le_one_of_one_le₀ hcq)) hA0
    refine isPltPair_of_add hX hXs hKX hrem ?_
    rw [add_assoc _ ((c : ℚ)⁻¹ • A), ← add_smul, add_sub_cancel, one_smul]
    exact hplt'
  have hfloorC : DivisorWithCoeffs.roundDown
      (Divisor.toQDivisor (Finsupp.single S 1) + A + B + (c : ℚ)⁻¹ • A) =
        Finsupp.single S 1 := by
    classical
    ext E
    have hE := congrArg (fun D : Divisor X => D E) hfloor
    have hle := hplt'.isLcPair.coeff_le_one hn E
    change ⌊((Finsupp.single S (1 : ℤ) E : ℤ) : ℚ) + A E + B E⌋ = Finsupp.single S (1 : ℤ) E
      at hE
    change ((Finsupp.single S (1 : ℤ) E : ℤ) : ℚ) + A E + B E + A E ≤ 1 at hle
    change ⌊((Finsupp.single S (1 : ℤ) E : ℤ) : ℚ) + A E + B E + (c : ℚ)⁻¹ * A E⌋ =
      Finsupp.single S (1 : ℤ) E
    by_cases hES : S = E
    · subst hES
      have : A S = 0 := hAS
      rw [this, mul_zero, add_zero]
      rwa [this] at hE
    rw [Finsupp.single_apply, if_neg hES] at hE hle ⊢
    push_cast at hE hle ⊢
    rw [zero_add] at hE hle ⊢
    rw [Int.floor_eq_zero_iff] at hE ⊢
    have hAE : 0 ≤ A E := hA0 E
    have hBE : 0 ≤ B E := hB0 E
    refine ⟨by positivity, ?_⟩
    rcases hAE.eq_or_lt with h0 | hpos
    · rw [← h0, mul_zero, add_zero]; linarith [hE.2]
    rcases (show c = 1 ∨ 2 ≤ c by omega) with rfl | hc2
    · exfalso
      obtain ⟨D', hD', -⟩ := hcΔ
      have h1 := congrArg (fun G : QDivisor X => G E) hD'
      change ((D' E : ℤ) : ℚ) = ((1 : ℕ) : ℚ) * (((Finsupp.single S (1 : ℤ) E : ℤ) : ℚ) +
        A E + B E) at h1
      rw [Finsupp.single_apply, if_neg hES] at h1
      simp only [Nat.cast_one, Int.cast_zero, one_mul, zero_add] at h1
      have h2 : (0 : ℚ) < D' E := by rw [h1]; linarith
      have h3 : (D' E : ℚ) < 1 := by rw [h1]; exact hE.2
      have h4 : (0 : ℤ) < D' E := by exact_mod_cast h2
      have h5 : D' E < (1 : ℤ) := by exact_mod_cast h3
      omega
    · have hc2' : (2 : ℚ) ≤ c := by exact_mod_cast hc2
      have : (c : ℚ)⁻¹ * A E < A E := by
        have hci : (c : ℚ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
        nlinarith
      linarith
  have hHc : H.IsCartier := hHa.1
  have hHamp : H.IsRelativelyAmple f hHc := hHa.isRelativelyAmple
  have hAamp : A.HasRelativelyAmpleMultiple f :=
    ⟨a, by omega, H, hHc, zsmul_inv_smul_eq _ ha0.ne', hHamp⟩
  haveI : IsNoetherian X := {}
  have hAF : ∀ G, (A.restrictPrimeDivisor S).coeff G ≠ 0 → F G = 0 := fun G hG =>
    hHF G (coeff_restrictPrimeDivisor_ne_zero_of_smul S hHS _ G hG)
  obtain ⟨P, hPc, hP0, hPS, M, hM, hext⟩ := exists_isRestrictionAlong_twist sX hX hXs f hf n KX
    hKX S hKXS hSs A B hA0 hB0 hAS hBS hAamp c hc hpltC hfloorC hcan hsec F rfl hAF ε hε0 hε1 hεA
    hcΔ Φ hcΦ hΦlo hΦhi
  have hABS : (A + B).coeff S = 0 := by
    change A S + B S = 0
    rw [show A S = 0 from hAS, show B S = 0 from hBS, add_zero]
  have hkltΩ : IsKltPair (S.idealSheaf.subschemeι ≫ sX) ((A + B).restrictPrimeDivisor S) :=
    isKltPair_of_isRealCanonicalPair_add hSs
      (coeff_restrictPrimeDivisor_nonneg' S (D := A + B)
        (fun P => add_nonneg (hA0 P) (hB0 P)) hABS)
      (coeff_restrictPrimeDivisor_nonneg' S hA0 hAS) hcan
  have hcD : ((c : ℚ) • (Divisor.toQDivisor KX + Divisor.toQDivisor (Finsupp.single S 1) + A +
      B)).IsCartierDivisor := by
    simpa only [Δ, add_assoc] using isCartierDivisor_smul_add hXs KX hcΔ
  have hΦ0 : 0 ≤ (A + B).restrictPrimeDivisor S - Φ := sub_nonneg.mpr hΦhi
  have hΦΩ : (A + B).restrictPrimeDivisor S - Φ ≤ (A + B).restrictPrimeDivisor S :=
    sub_le_self _ (nonneg_of_coeffwiseMin_le hΦlo)
  have hcΦ' : ((c : ℚ) • (Divisor.toQDivisor ((KX + Finsupp.single S 1).restrictPrimeDivisor S) +
      ((A + B).restrictPrimeDivisor S - Φ))).IsCartierDivisor := by
    refine isCartierDivisor_smul_add_sub hSs _
      (exists_toQDivisor_eq_smul_restrictPrimeDivisor S hABS
        (exists_toQDivisor_eq_smul_of_single_add S (by simpa only [Δ, add_assoc] using hcΔ)))
      hcΦ
  have hampP : ∃ L₀ : ℕ, ∀ l : ℕ, L₀ ≤ l → ((c : ℚ)⁻¹ • A - (((c : ℚ) - 1) / (c * l : ℕ)) •
      Divisor.toQDivisor P).HasRelativelyAmpleMultiple f :=
    Filter.eventually_atTop.mp (eventually_hasRelativelyAmpleMultiple_sub f hf
      (show 0 < a by omega) hHc hHamp (zsmul_inv_smul_eq _ ha0.ne') hc hPc)
  have hkltP : ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 ≤ t → t < δ →
      IsKltPair (S.idealSheaf.subschemeι ≫ sX) ((A + B).restrictPrimeDivisor S +
        t • (Divisor.toQDivisor P).restrictPrimeDivisor S) :=
    exists_isKltPair_add_smul hSs hkltΩ (fun Q => coeff_restrictPrimeDivisor_nonneg' S
      (fun E => by change (0 : ℚ) ≤ ((P E : ℤ) : ℚ); exact_mod_cast hP0 E)
      (by change ((P S : ℤ) : ℚ) = 0; exact_mod_cast hPS) Q)
  obtain ⟨L₀, hamp₁⟩ := hampP
  obtain ⟨δ₂, hδ₂, hklt₂⟩ := hkltP
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (1 / δ₂)
  set N₀ : ℕ := max N₁ L₀ with hN₀_def
  have hN₀ : 1 / δ₂ < N₀ := lt_of_lt_of_le hN₁ (by exact_mod_cast le_max_left N₁ L₀)
  set l : ℕ := M * a * (N₀ + 2) with hl_def
  have hl : 1 < l := by
    have : 1 ≤ M * a := Nat.one_le_iff_ne_zero.mpr (by positivity)
    rw [hl_def]
    nlinarith
  have hlA : ((l : ℚ) • A).IsCartierDivisor :=
    isCartierDivisor_natCast_smul_inv_smul hXs H ha0.ne'
  have ht0 : 0 ≤ ((c : ℚ) - 1) / ((c * l : ℕ) : ℚ) :=
    div_nonneg (sub_nonneg.mpr (by exact_mod_cast hc)) (Nat.cast_nonneg _)
  have ht1 : ((c : ℚ) - 1) / ((c * l : ℕ) : ℚ) < δ₂ :=
    div_lt_of_nat_gt hδ₂ hN₀ hc hM (by omega)
  have hlL : L₀ ≤ l := by
    have : 1 ≤ M * a := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have : L₀ ≤ N₀ := le_max_right _ _
    rw [hl_def]; nlinarith
  have hu' : u ∈ sectionsIn (DivisorWithCoeffs.roundDown ((c : ℚ) • (Divisor.toQDivisor
      ((KX + Finsupp.single S 1).restrictPrimeDivisor S) + ((A + B).restrictPrimeDivisor S - Φ))))
      := by
    simpa only [KS, Ω, add_sub_assoc] using hu
  obtain ⟨g', hg', hres⟩ := exists_isRestrictionAlong_of_exists_isRestrictionAlong_twist sX hX hXs
    f hf n KX hKX S hKXS hSs A B hA0 hB0 hAS hBS hAamp hkltΩ c hc hcD
    ((A + B).restrictPrimeDivisor S - Φ) hΦ0 hΦΩ hcΦ' l hl P hPc hP0 hPS hlA
    (hamp₁ l hlL) (hklt₂ _ ht0 ht1)
    (fun u' hu'' => hext (c * l) (Nat.mul_pos hc (by omega))
      (Dvd.dvd.mul_left (Dvd.intro _ (by rw [hl_def, mul_assoc])) c) u' hu'') u hu'
  refine ⟨g', ?_, hres⟩
  simpa only [D, Δ, add_assoc] using hg'

end MMP.Fourfold

end
