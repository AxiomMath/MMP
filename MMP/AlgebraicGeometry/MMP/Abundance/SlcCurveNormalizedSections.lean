module

public import MMP.AlgebraicGeometry.Singularities.Slc.NormalizedSections
import StacksFrontier.AlgebraicGeometry.Variety.Curve.RegularCompactification
import StacksFrontier.AlgebraicGeometry.Variety.Curve.SmoothRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Properties.NormalConnectedIntegral

/-!
# Normalized sections on slc curves, and completions of smooth curves

This file collects two independent results.

**Normalized sections on an slc curve.** Let `(C, Δ)` be an slc curve with normalization
`n : C̄ = ⨆ᵢ Cᵢ ⟶ C`, and let `m > 0` be even with `mΔ` integral. A section `s` of
`𝒪_C(m(K_C + Δ))` is normalized exactly when each restriction `n^*(s)|_{Cᵢ}` is a normalized
section of `𝒪_{Cᵢ}(m(K_{Cᵢ} + Δᵢ))`: the gluing condition at the nodes is automatic for tuples of
normalized sections, because both leading coefficients at the two preimages of a node are `1`
and `(-1)^m = 1`.

**Smooth projective completion of a smooth curve.** Over a perfect field `k`, every smooth,
separated, connected curve of finite type is an open subscheme, with finite complement, of a
smooth projective connected curve over `k`.

## Main results

* `MMP.Flips.NormalizationComponents.isNormalizedSlcSection_iff_forall_isNormalizedSection`
* `MMP.Curves.exists_isOpenImmersion_isProjective_of_smoothOfRelativeDimension_one`

## Implementation notes

A rational `m`-canonical form on `C` is the family `(n^*(s)|_{Cᵢ})ᵢ` itself, so the bijection
of normalized sections onto the product is stated as an equivalence of predicates on families.

A curve over `k` is a scheme with a structure morphism `f : X ⟶ Spec k` that is smooth of
relative dimension one, quasi-compact and separated, with `X` connected; the base is an
arbitrary perfect field rather than `ℂ`, since the proof needs only that normal curves over `k`
are smooth.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 12.2.11.1
-/
public section

universe u

open CategoryTheory AlgebraicGeometry

/-! ### Normalized sections on an slc curve -/

namespace MMP.Flips.NormalizationComponents

open MMP.Mori

/-- The coefficients of `G = mΔ` in a normalized section. -/
private lemma coeff_eq_mul_of_isNormalizedSection {k : Type u} [Field k]
    {ε : EllipticNormalizationDatum k} {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of k)} {Δ : QDivisor X} {m : ℕ} {G : Divisor X}
    {s : RationalPluriForms sX 1 m} (h : IsNormalizedSection ε sX Δ m G s)
    (P : Mori.PrimeDivisor X) : (G.coeff P : ℚ) = m * Δ.coeff P := by
  simpa [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] using
    congrArg (DivisorWithCoeffs.coeff · P) h.toQDivisor_eq

/-- A nonzero normalized section of `𝒪(m(K + Δ))` has order `≥ -m Δ_P` at every prime divisor `P`. -/
private lemma ordForm_add_nonneg_of_isNormalizedSection {k : Type u} [Field k]
    {ε : EllipticNormalizationDatum k} {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of k)} {Δ : QDivisor X} {m : ℕ} {G : Divisor X}
    {s : RationalPluriForms sX 1 m} (h : IsNormalizedSection ε sX Δ m G s)
    (hs : s ≠ 0) (P : Mori.PrimeDivisor X) :
    0 ≤ ((P.ordForm s : ℤ) : ℚ) + m * Δ.coeff P := by
  rw [← coeff_eq_mul_of_isNormalizedSection h P]
  exact_mod_cast (mem_pluricanonicalSections_of_ne_bot (U := ⊤) (by simp)).1 h.mem P
    ⟨P.genericPoint, by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact ⟨subset_closure rfl, trivial⟩⟩ hs

/-- Over a node of `C`, a normalized section on the component `Cᵢ` has leading coefficient `1`. -/
private lemma isLeadingCoeff_one_of_isDoubleNormalCrossingPoint {k : Type u} [Field k]
    {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)}
    {hC : ∀ U : C.Opens, IsCompact (U : Set C) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sC hC} {ε : EllipticNormalizationDatum k} {Δ : QWeilDivisor C}
    {n : ℕ} {i : N.ι} {Δi : QDivisor (N.X i)} {Gi : Divisor (N.X i)}
    {s : RationalPluriForms (N.n i ≫ sC) 1 n} (hΔi : N.IsComponentBoundary Δ i Δi)
    (hs : IsNormalizedSection ε (N.n i ≫ sC) Δi n Gi s) {P : Mori.PrimeDivisor (N.X i)}
    (hP : IsDoubleNormalCrossingPoint sC 1 ((N.n i).base P.genericPoint)) :
    N.IsLeadingCoeff i P s 1 := by
  have h1 : Δi.coeff P = 1 := by rw [hΔi.2, componentBoundaryCoeff, if_pos hP]
  have hG : Gi.coeff P = n := by
    have := coeff_eq_mul_of_isNormalizedSection hs P
    rw [h1, mul_one] at this
    exact_mod_cast this
  obtain ⟨z, hz, hv⟩ := hs.vanishes (by rintro ⟨-, -, h0, -⟩; simp [h0] at h1) P h1.ge
  refine ⟨z, hz, ?_⟩
  simp only [map_one, one_smul]
  exact hv.imp_right fun hv => by omega

variable {k : Type u} [Field k] {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)}
  {hC : ∀ U : C.Opens, IsCompact (U : Set C) → (irreducibleComponents U).Finite}
  (N : NormalizationComponents sC hC)

/-- **Normalized sections on an slc curve are tuples of normalized sections** (FA 12.2.11.1).
Let `(C, Δ)` be an slc curve, `n > 0` even with `nΔ` integral. A family
`s = (n^*(s)|_{Cᵢ})ᵢ` of rational `n`-canonical forms on the components `Cᵢ` of the
normalization is a normalized section of `𝒪_C(n(K_C + Δ))` (`IsNormalizedSlcSection`) if and
only if each `s i` is a normalized section of `𝒪_{Cᵢ}(n(K_{Cᵢ} + Δᵢ))`
(`MMP.Flips.IsNormalizedSection`, with `Δᵢ` the boundary of `IsComponentBoundary`). -/
@[mmp "lem_fa12a_normalized_sections_product"]
public theorem isNormalizedSlcSection_iff_forall_isNormalizedSection
    (ε : EllipticNormalizationDatum k) {Δ : QWeilDivisor C} (hΔ : IsSlcCurve sC Δ)
    {n : ℕ} (hn : Even n) (hn0 : 0 < n) (hint : ∀ Γ, ((n : ℚ) * Δ Γ).den = 1)
    (s : ∀ i : N.ι, RationalPluriForms (N.n i ≫ sC) 1 n) :
    N.IsNormalizedSlcSection ε Δ n s ↔
      ∀ i, ∃ (Δi : QDivisor (N.X i)) (Gi : Divisor (N.X i)),
        N.IsComponentBoundary Δ i Δi ∧ IsNormalizedSection ε (N.n i ≫ sC) Δi n Gi (s i) := by
  refine ⟨fun h => h.2.2.2.2, fun h => ⟨hΔ, hn0, hint, ⟨fun i P hs => ?_, ?_⟩, h⟩⟩
  · obtain ⟨Δi, Gi, hΔi, hN⟩ := h i
    simpa [hΔi.2] using ordForm_add_nonneg_of_isNormalizedSection hN hs P
  · have key : ∀ i P, IsDoubleNormalCrossingPoint sC 1 ((N.n i).base P.genericPoint) →
        N.IsLeadingCoeff i P (s i) 1 := fun i P hP => by
      obtain ⟨Δi, Gi, hΔi, hN⟩ := h i
      exact isLeadingCoeff_one_of_isDoubleNormalCrossingPoint hΔi hN hP
    intro i j P P' hPP' hP _
    exact ⟨1, key i P hP, by simpa [hn.neg_one_pow] using key j P' (hPP' ▸ hP)⟩

end MMP.Flips.NormalizationComponents

/-! ### Smooth projective completion of a smooth curve -/

namespace MMP.Curves

/-- **Smooth projective completion of a smooth curve.** A smooth, separated, connected curve `X`
of finite type over a perfect field `k` embeds over `k`, by an open immersion with finite
complement, into a smooth, projective, connected curve over `k`. -/
@[mmp "lem_mmp_smooth_complex_curve_completion"]
public theorem exists_isOpenImmersion_isProjective_of_smoothOfRelativeDimension_one
    (k : Type u) [Field k] [PerfectField k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [QuasiCompact f] [IsSeparated f] [ConnectedSpace X] :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of k)) (ι : X ⟶ Y),
      IsOpenImmersion ι ∧ ι ≫ g = f ∧ SmoothOfRelativeDimension 1 g ∧ IsProjective g ∧
        ConnectedSpace Y ∧ (Set.range ι)ᶜ.Finite := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsIntegral X := isIntegral_of_smooth_of_connectedSpace f
  have : IsCurve k f :=
    { topologicalKrullDim_eq_one := by
        exact_mod_cast topologicalKrullDim_eq_of_smoothOfRelativeDimension f 1 }
  obtain ⟨-, Y, g, ι, hι, hcomp, hcurve, hproj, -, hsm, hfin, -⟩ :=
    exists_smooth_isProjectiveMorphism_compactification_of_perfectField k f
      (isRegular_of_smooth_over_field f)
  have : IsCurve k g := hcurve
  have : Smooth g := hsm
  have : IsIntegral Y := hcurve.toIsIntegral
  exact ⟨Y, g, ι, hι, hcomp, smoothOfRelativeDimension_one_of_isCurve k g, hproj.isProjective,
    inferInstance, hfin⟩

end MMP.Curves

end
