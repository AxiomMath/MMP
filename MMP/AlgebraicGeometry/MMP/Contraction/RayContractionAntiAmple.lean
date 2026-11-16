module

public import MMP.AlgebraicGeometry.Positivity.Kleiman.RelativeCartier

/-!
# Contractions of a negative extremal ray are anti-ample

Let `(X, Δ)` be a pair over an algebraically closed field `k` of characteristic zero, with `X`
projective, let `R` be an extremal ray of the closed cone of curves `NE̅(X) ⊆ N₁(X)` on which
`K_X + Δ` is negative, and let `φ : X ⟶ Y` be a morphism to a projective variety contracting only
curves whose classes lie in `R`. Then `-(K_X + Δ)` is `φ`-ample: the closed relative cone
`NE̅(X/Y)` lies in `R`, so a Cartier multiple of `-(K_X + Δ)` is positive on `NE̅(X/Y) \ 0`, and
the relative Kleiman criterion applies.

## Main results

* `MMP.Mori.hasRelativelyAmpleMultiple_neg_of_isExtremalRay`: the statement above.

## Implementation notes

The pair is a normal variety `X` with a canonical divisor `K` such that `K + Δ` is `ℚ`-Cartier,
as in `MMP.Mori.IsFlippingContraction`. The intersection number `((K + Δ) · v)` of a class
`v ∈ N₁(X)` is computed from the associated `ℚ`-Cartier divisor
`⟨K + Δ⟩ = ∑ⱼ cⱼ Dⱼ` (`MMP.Mori.QDivisor.associatedCartier`) as `∑ⱼ cⱼ (v · 𝒪_X(Dⱼ))`, and
`φ`-ampleness of the `ℚ`-divisor `-(K + Δ)` is `MMP.Mori.QDivisor.HasRelativelyAmpleMultiple`:
some positive multiple is a Cartier divisor with `φ`-ample invertible sheaf.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proofs of
  3.31, 3.36, 3.37 and 3.43
-/

open AlgebraicGeometry CategoryTheory MMP.Mori

namespace MMP.FourfoldProofs.Km3cRayContractionAntiAmpleProof

section Helpers

variable {k : Type} [Field k] {X Y : Scheme.{0}} (sX : X ⟶ Spec (.of k))

/-- Numerical classes are separated by the degree forms of invertible sheaves. -/
private theorem numericalCurveClasses_ext {z z' : NumericalCurveClasses sX}
    (h : ∀ (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L],
      NumericalCurveClasses.degree sX L z = NumericalCurveClasses.degree sX L z') : z = z' := by
  obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX z
  obtain ⟨Z', rfl⟩ := OneCycle.numericalClass_surjective sX z'
  rw [← sub_eq_zero, ← map_sub]
  refine (Submodule.Quotient.mk_eq_zero _).mpr (OneCycle.mem_numericallyTrivial.mpr fun L _ => ?_)
  rw [map_sub, sub_eq_zero]
  simpa only [NumericalCurveClasses.degree_numericalClass] using h L

/-- A ray `ℝ_{≥0} · v`, `v ≠ 0`, is closed in `N₁(X)` for the numerical topology. -/
private theorem isClosed_ray {v : NumericalCurveClasses sX} (hv : v ≠ 0) :
    IsClosed {w : NumericalCurveClasses sX | ∃ c : ℝ, 0 ≤ c ∧ c • v = w} := by
  obtain ⟨L₀, hL₀, hv₀⟩ : ∃ (L₀ : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf
      X.ringCatSheaf.2 L₀), NumericalCurveClasses.degree sX L₀ v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv (numericalCurveClasses_ext sX fun L _ => by rw [hcon L, map_zero])
  set a := NumericalCurveClasses.degree sX L₀ v
  have hS : {w : NumericalCurveClasses sX | ∃ c : ℝ, 0 ≤ c ∧ c • v = w} =
      {w | 0 ≤ NumericalCurveClasses.degree sX L₀ w / a} ∩
        ⋂ (L : X.Modules) (h : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
          {w | NumericalCurveClasses.degree sX L w =
            NumericalCurveClasses.degree sX L₀ w / a * NumericalCurveClasses.degree sX L v} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨c, hc, rfl⟩
      have hca : NumericalCurveClasses.degree sX L₀ (c • v) / a = c := by
        rw [map_smul, smul_eq_mul, mul_div_assoc, div_self hv₀, mul_one]
      exact ⟨by rwa [hca], fun L _ => by rw [hca, map_smul, smul_eq_mul]⟩
    · rintro ⟨hc, hL⟩
      refine ⟨_, hc, numericalCurveClasses_ext sX fun L _ => ?_⟩
      rw [map_smul, smul_eq_mul, hL L]
  rw [hS]
  have hc₀ := NumericalCurveClasses.continuous_degree sX L₀
  exact (isClosed_le continuous_const (hc₀.div_const a)).inter
    (isClosed_iInter fun L => isClosed_iInter fun _ =>
      isClosed_eq (NumericalCurveClasses.continuous_degree sX L)
        ((hc₀.div_const a).mul continuous_const))

variable (f : X ⟶ Y)

/-- The relative degree form of `L` is the absolute one composed with `N₁(X/Y) → N₁(X)`. -/
private theorem relativeDegree_eq_comp (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    RelativeNumericalCurveClasses.degree sX f L =
      (NumericalCurveClasses.degree sX L).comp (relativeToAbsolute sX f) := by
  apply Submodule.linearMap_qext
  rfl

private theorem continuous_relativeToAbsolute : Continuous (relativeToAbsolute sX f) := by
  refine continuous_iInf_rng.2 fun L => continuous_iInf_rng.2 fun h => continuous_induced_rng.2 ?_
  have hc := RelativeNumericalCurveClasses.continuous_degree sX f L
  rwa [relativeDegree_eq_comp sX f L, LinearMap.coe_comp] at hc

private theorem injective_relativeToAbsolute : Function.Injective (relativeToAbsolute sX f) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro z hz
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX f z
  have hZ : OneCycle.numericalClass sX (Z : OneCycle ℝ sX) = 0 := LinearMap.mem_ker.mp hz
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    ((Submodule.Quotient.mk_eq_zero (OneCycle.numericallyTrivial sX)).mp hZ)

/-- `f`-ampleness of an invertible sheaf only depends on its isomorphism class. -/
private theorem isRelativelyAmple_of_iso {L L' : X.Modules} [Stacks.Ample.IsInvertibleModule X L]
    [Stacks.Ample.IsInvertibleModule X L'] (e : L ≅ L') (h : IsRelativelyAmple f L) :
    IsRelativelyAmple f L' := by
  intro y
  obtain ⟨V, hV, hyV, hA⟩ := h y
  exact ⟨V, hV, hyV, (Stacks.RelativeVeryAmple.isAmple_congr _ _
    (Functor.mapIso _ e)).mp hA⟩

/-- If every curve contracted by `f` has its class on the ray `ℝ≥0 · v`, then so does the image
in `N₁(X)` of every class of the closed relative cone `NE̅(X/Y)`. -/
private theorem relativeToAbsolute_mem_ray {v : NumericalCurveClasses sX} (hv : v ≠ 0)
    (hcontr : ∀ C : ProperCurve sX, C.IsContractedBy f →
      ∃ c : ℝ, 0 ≤ c ∧ c • v = OneCycle.numericalClass sX (C.cycle ℝ))
    {z : RelativeNumericalCurveClasses sX f} (hz : z ∈ relativeClosedConeOfCurves sX f) :
    ∃ c : ℝ, 0 ≤ c ∧ c • v = relativeToAbsolute sX f z := by
  set ι := relativeToAbsolute sX f
  have hsub : (relativeConeOfCurves sX f : Set _) ⊆ ι ⁻¹' {w | ∃ c : ℝ, 0 ≤ c ∧ c • v = w} := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨C, hC⟩, rfl⟩ := hx
      exact hcontr C hC
    | zero => exact ⟨0, le_rfl, by rw [zero_smul, map_zero]⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, hcx⟩ := hx
      obtain ⟨c', hc', hcy⟩ := hy
      exact ⟨c + c', add_nonneg hc hc', by rw [add_smul, hcx, hcy, map_add]⟩
    | smul a x _ hx =>
      obtain ⟨c, hc, hcx⟩ := hx
      exact ⟨a * c, mul_nonneg a.2 hc, by
        rw [mul_smul, hcx]
        exact (map_smul ι (a : ℝ) x).symm⟩
  exact closure_minimal hsub
    ((isClosed_ray sX hv).preimage (continuous_relativeToAbsolute sX f)) hz

/-- If the Cartier divisor `A` has sheaf `𝒪_X(-E)`, its relative intersection form is minus the
degree form of `𝒪_X(E)` read through `N₁(X/Y) → N₁(X)`. -/
private theorem intersectionNumber_ofCartier_eq_neg_degree [QuasiCompact sX]
    [IsLocallyNoetherian X] [IsNormal X] {E : Divisor X} (hE : E.IsCartier)
    [Stacks.Ample.IsInvertibleModule X E.divisorialSheaf]
    [Stacks.Ample.IsInvertibleModule X (-E).divisorialSheaf] {A : X.CartierDivisor}
    (e : (-E).divisorialSheaf ≅ MMP.CartierDivisor.sheaf A)
    (z : RelativeNumericalCurveClasses sX f) :
    RelativeNumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ A) z =
      -NumericalCurveClasses.degree sX E.divisorialSheaf (relativeToAbsolute sX f z) := by
  have hdeg (C : ProperCurve sX) : C.degree k (MMP.CartierDivisor.sheaf A) =
      -C.degree k E.divisorialSheaf := by
    rw [ProperCurve.degree, ProperCurve.degree, ← degreeOn_eq_of_iso k sX C.ι C.dim_le e]
    exact Divisor.degreeOn_neg' k sX C.ι C.dim_le _ hE
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX f z
  rw [RelativeNumericalCurveClasses.intersectionNumber_relativeNumericalClass,
    OneCycle.intersectionNumber_ofCartier]
  change OneCycle.degree ℝ sX _ (Z : OneCycle ℝ sX) =
    -(OneCycle.degree ℝ sX E.divisorialSheaf (Z : OneCycle ℝ sX))
  simp only [OneCycle.degree_apply, Finsupp.sum, hdeg, Int.cast_neg, mul_neg,
    Finset.sum_neg_distrib]

end Helpers

end MMP.FourfoldProofs.Km3cRayContractionAntiAmpleProof

@[expose] public section

open AlgebraicGeometry CategoryTheory MMP.FourfoldProofs.Km3cRayContractionAntiAmpleProof

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Mori

/-- **The contraction of a `(K + Δ)`-negative extremal ray is `-(K + Δ)`-ample.** Let `(X, Δ)`
be a pair over an algebraically closed field of characteristic zero with `X` projective, `K` a
canonical divisor, `R` an extremal ray of `NE̅(X)` with `((K + Δ) · v) < 0` for every nonzero
`v ∈ R`, and `φ : X ⟶ Y` a morphism to a projective variety such that every proper curve
`C ⊆ X` with `φ(C)` a point has `[C] ∈ R`. Then `-(K + Δ)` is `φ`-ample. -/
@[mmp "lem_km3c_ray_contraction_anti_ample"]
public theorem hasRelativelyAmpleMultiple_neg_of_isExtremalRay
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X Y : Scheme.{0}}
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    (_hX : IsNormalVariety k sX) (hXp : IsProjectiveVariety k sX) (hYp : IsProjectiveVariety k sY)
    {K : Divisor X} (_hK : ∃ n : ℕ, K.IsCanonicalDivisor sX n) {Δ : QDivisor X}
    (hQ : (Divisor.toQDivisor K + Δ).IsQCartier)
    {R : Set (NumericalCurveClasses sX)}
    (hR : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R)
    (hneg : ∀ v ∈ R, v ≠ 0 →
      (((Divisor.toQDivisor K + Δ).associatedCartier hQ).sum fun E c =>
        haveI := (Divisor.mem_cartierSubgroup.mp E.2).isInvertibleModule_divisorialSheaf
        (c : ℝ) * NumericalCurveClasses.degree sX (E : Divisor X).divisorialSheaf v) < 0)
    (φ : X ⟶ Y) (hφ : φ ≫ sY = sX)
    (hcontr : ∀ C : ProperCurve sX, C.IsContractedBy φ →
      OneCycle.numericalClass sX (C.cycle ℝ) ∈ R) :
    (-(Divisor.toQDivisor K + Δ)).HasRelativelyAmpleMultiple φ := by
  have := hXp.toIsVariety
  have := hYp.toIsVariety
  have : IsIntegral X := IsVariety.toIsIntegral (k := k) (f := sX)
  have hproj : IsProjective φ :=
    IsProjective.of_comp φ sY (hφ ▸ ((isProjectiveVariety_iff_isProjective' k sX).mp hXp).2)
  set E := (Divisor.toQDivisor K + Δ).cartierIndexSMul hQ
  have hEc : (E : Divisor X).IsCartier := Divisor.mem_cartierSubgroup.mp E.2
  refine ⟨_, QDivisor.cartierIndex_pos hQ, -(E : Divisor X), hEc.neg,
    by rw [map_neg, QDivisor.toQDivisor_cartierIndexSMul, smul_neg], ?_⟩
  have := hEc.neg.isInvertibleModule_divisorialSheaf
  have := hEc.isInvertibleModule_divisorialSheaf
  obtain ⟨A, ⟨e⟩⟩ :=
    MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf (-(E : Divisor X)).divisorialSheaf
  rw [Divisor.isRelativelyAmple_iff]
  refine isRelativelyAmple_of_iso φ e.symm <|
    (isRelativelyAmple_cartierSheaf_iff_forall_relativeClosedConeOfCurves_pos sY sX φ hproj hφ
      A).mpr fun z hz hz0 => ?_
  obtain ⟨v, hv0, rfl⟩ := hR.2
  have h := hneg _ (relativeToAbsolute_mem_ray sX φ hv0 hcontr hz)
    fun h => hz0 (injective_relativeToAbsolute sX φ (h.trans (map_zero _).symm))
  rw [QDivisor.associatedCartier, CartierDivisorWithCoeffs.ofCartier, Finsupp.smul_single,
    Finsupp.sum_single_index (by simp)] at h
  rw [intersectionNumber_ofCartier_eq_neg_degree sX φ hEc e, neg_pos]
  refine neg_of_mul_neg_right h (le_of_lt ?_)
  have := QDivisor.cartierIndex_pos hQ
  positivity

end MMP.Mori

end
