module

public import MMP.AlgebraicGeometry.MMP.Contraction.RelativeLineBundleDescent
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.DltNegativeFace

/-!
# A flip transfers a ℚ-Cartier divisor that is numerically trivial on the flipping ray

Let `f : X ⟶ Z ⟵ X⁺ : f⁺` be an `L`-flip (`MMP.Fourfold.IsFlipOf`) of projective normal
varieties, with `X` `ℚ`-factorial and `ρ(X/Z) = 1`, and suppose that some effective klt boundary
`B` makes `K_X + B` negative on every curve contracted by `f`. Then every `ℚ`-Cartier
`ℚ`-divisor `P` on `X` of degree zero on the curves contracted by `f` comes from `Z`: there is a
`ℚ`-Cartier `ℚ`-divisor `M` on `Z` with `P ∼_ℚ f^*M`, and the strict transform
`P⁺ = (f⁺)⁻¹_* f_* P` is `ℚ`-Cartier with `P⁺ ∼_ℚ (f⁺)^*M`.

The proof descends a Cartier multiple of `P` along the `(K_X + B)`-negative contraction `f`
(the contraction theorem), and transports the principal adjustment across the small maps `f`
and `f⁺`, which identify the function fields and the prime divisors of `X` and `X⁺`.

## Main results

* `MMP.Fourfold.IsFlipOf.exists_qLinearlyEquivalent_pullback_of_curveForm_eq_zero`.

## Implementation notes

The relative Picard number is `MMP.Flips.relativePicardNumber`, the dimension of
`N¹(X/Z)`: `ℝ`-Cartier divisors on `X` modulo those of degree zero on every curve contracted
by `f` (Kollár–Mori's form, as an extremal contraction supplies it).
"Negative on the contracted ray" and "degree zero on this ray" are stated curve by curve: for
every proper curve `A ⊆ X` contracted by `f`, `((K_X + B) · A) < 0` and `(P · A) = 0`. Since
the contracted ray is spanned by the classes of these curves, this is the same condition for
the linear forms `MMP.Fourfold.QDivisor.curveForm`. The pull-back `MMP.Mori.QDivisor.pullback`
takes as an argument the fact that the generic point of `X` (resp. `X⁺`) does not map into
`Supp M`; the conclusion asserts it.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Theorem 3.7(4)
-/

@[expose] public section

open AlgebraicGeometry hiding IsProjectiveVariety
open CategoryTheory MMP.Mori MMP.Fourfold

namespace MMP.Fourfold

section RelativeClasses

variable {k : Type} [Field k]

/-- The natural map `N₁(X/Y) → N₁(X)` is injective. -/
private theorem relativeToAbsolute_injective {X Y : Scheme.{0}} (sX : X ⟶ Spec (.of k))
    (f : X ⟶ Y) : Function.Injective (relativeToAbsolute sX f) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro z hz
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX f z
  rw [LinearMap.mem_ker, isNaturalRelativeMap_relativeToAbsolute sX f Z] at hz
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    ((Submodule.Quotient.mk_eq_zero (OneCycle.numericallyTrivial sX)).mp hz)

/-- With no curve contracted by `f`, `N₁(X/Y) = 0`. -/
private theorem eq_zero_of_forall_not_isContractedBy {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    {f : X ⟶ Y} (h : ∀ C : ProperCurve sX, ¬ C.IsContractedBy f)
    (z : RelativeNumericalCurveClasses sX f) : z = 0 := by
  obtain ⟨⟨Z, hZ⟩, rfl⟩ := relativeNumericalClass_surjective sX f z
  have hZ0 : Z = 0 := by
    rw [relativeOneCycles, Finsupp.mem_supported] at hZ
    ext C
    by_contra hne
    exact h C (hZ (Finsupp.mem_support_iff.mpr hne))
  subst hZ0
  exact map_zero _

/-- The pairing of a `ℚ`-Cartier `ℚ`-divisor with `N₁(X/S)` is continuous. -/
private theorem continuous_relativeCurveForm {X S : Scheme.{0}}
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of k)) (f : X ⟶ S)
    (D : QDivisor X) (h : D.IsQCartier) :
    Continuous (QDivisor.relativeCurveForm sX f D h) := by
  unfold QDivisor.relativeCurveForm
  rw [Finsupp.sum, LinearMap.coe_sum, Finset.sum_fn]
  refine continuous_finsetSum _ fun E _ => ?_
  have := (Divisor.mem_cartierSubgroup.mp E.2).isInvertibleModule_divisorialSheaf
  rw [LinearMap.coe_smul]
  exact (RelativeNumericalCurveClasses.continuous_degree sX f _).const_smul _

/-- **`ρ(X/Z) = 1` makes `N₁(X/Z)` at most a line.** The pairing embeds `N₁(X/Z)` into the
annihilator of the numerically `f`-trivial divisors, the dual of the line `N¹(X/Z)`; so every
class is a multiple of a nonzero one. -/
private theorem exists_smul_eq_of_relativePicardNumber_eq_one {X Z : Scheme.{0}}
    [IsIntegral X] {sX : X ⟶ Spec (.of k)} {f : X ⟶ Z}
    (hρ : MMP.Flips.relativePicardNumber sX f = 1)
    {v : RelativeNumericalCurveClasses sX f} (hv : v ≠ 0) (z : RelativeNumericalCurveClasses sX f) :
    ∃ c : ℝ, c • v = z := by
  set W := MMP.Flips.relativeNumericallyTrivialDivisors sX f
  have hrank : Module.finrank ℝ (KCartierDivisor ℝ X ⧸ W) = 1 := by
    have h1 : Module.rank ℝ (KCartierDivisor ℝ X ⧸ W) = 1 := by
      unfold MMP.Flips.relativePicardNumber at hρ
      exact Cardinal.toENat_eq_one.mp hρ
    exact Module.finrank_eq_of_rank_eq (by simp [h1])
  have : FiniteDimensional ℝ (KCartierDivisor ℝ X ⧸ W) :=
    Module.finite_of_finrank_eq_succ hrank
  have hann : ∀ (z : RelativeNumericalCurveClasses sX f) (D : KCartierDivisor ℝ X), D ∈ W →
      curvePairing sX (relativeToAbsolute sX f z) D = 0 := by
    intro z D hD
    obtain ⟨⟨Z, hZ⟩, rfl⟩ := relativeNumericalClass_surjective sX f z
    rw [isNaturalRelativeMap_relativeToAbsolute sX f]
    change OneCycle.intersectionPairing D Z = 0
    rw [MMP.Flips.mem_relativeNumericallyTrivialDivisors] at hD
    rw [relativeOneCycles, Finsupp.mem_supported] at hZ
    rw [← Finsupp.sum_single Z, Finsupp.sum, map_sum]
    refine Finset.sum_eq_zero fun C hC => ?_
    have hs : Finsupp.single C (Z C) = Z C • C.cycle ℝ := by
      rw [ProperCurve.cycle, Finsupp.smul_single_one]
    rw [hs, map_smul, show OneCycle.intersectionPairing D (C.cycle ℝ) = 0 from hD C (hZ hC),
      smul_zero]
  let φ : RelativeNumericalCurveClasses sX f →ₗ[ℝ] W.dualAnnihilator :=
    LinearMap.codRestrict W.dualAnnihilator (curvePairing sX ∘ₗ relativeToAbsolute sX f)
      fun z => (Submodule.mem_dualAnnihilator _).mpr fun D hD => hann z D hD
  let ψ := W.dualQuotEquivDualAnnihilator.symm.toLinearMap ∘ₗ φ
  have hψ : Function.Injective ψ := by
    intro z₁ z₂ h
    have h2 : curvePairing sX (relativeToAbsolute sX f z₁) =
        curvePairing sX (relativeToAbsolute sX f z₂) :=
      congrArg Subtype.val (W.dualQuotEquivDualAnnihilator.symm.injective h)
    refine relativeToAbsolute_injective sX f (numericalPairing_flip_injective sX ?_)
    refine LinearMap.ext fun d => ?_
    obtain ⟨D, rfl⟩ := (numericallyTrivialDivisors sX).mkQ_surjective d
    exact LinearMap.congr_fun h2 D
  have hfin : Module.finrank ℝ (Module.Dual ℝ (KCartierDivisor ℝ X ⧸ W)) = 1 := by
    rw [Subspace.dual_finrank_eq, hrank]
  have := Module.Finite.of_injective ψ hψ
  have hle : Module.finrank ℝ (RelativeNumericalCurveClasses sX f) ≤ 1 :=
    hfin ▸ LinearMap.finrank_le_finrank_of_injective hψ
  have h1 : Module.finrank ℝ (RelativeNumericalCurveClasses sX f) = 1 :=
    le_antisymm hle (Module.finrank_pos_iff_exists_ne_zero.mpr ⟨v, hv⟩)
  exact (finrank_eq_one_iff_of_nonzero' v hv).mp h1 z

/-- **The closed relative cone is negative when `ρ(X/Z) = 1`.** If `D` is negative on every curve
contracted by `f` and `ρ(X/Z) = 1`, then `(D · z) < 0` for every nonzero `z ∈ NE̅(X/Z)`: all of
`N₁(X/Z)` is the line through the class `[A]` of a contracted curve, the cone lies in the closed
half-line where `D` is `≤ 0`, and `D` vanishes only at `0` on that line. -/
private theorem curveForm_relativeToAbsolute_neg {X Z : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} {f : X ⟶ Z}
    (hρ : MMP.Flips.relativePicardNumber sX f = 1) {D : QDivisor X} (h : D.IsQCartier)
    (hD : ∀ A : ProperCurve sX, A.IsContractedBy f →
      QDivisor.curveForm sX D h (OneCycle.numericalClass sX (A.cycle ℝ)) < 0)
    (z : RelativeNumericalCurveClasses sX f)
    (hz : z ∈ (relativeClosedConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f)))
    (hz0 : z ≠ 0) : (QDivisor.curveForm sX D h ∘ₗ relativeToAbsolute sX f) z < 0 := by
  obtain ⟨A, hA⟩ : ∃ A : ProperCurve sX, A.IsContractedBy f := by
    by_contra! hA
    exact hz0 (eq_zero_of_forall_not_isContractedBy hA z)
  set ℓ := QDivisor.curveForm sX D h ∘ₗ relativeToAbsolute sX f
  have hℓ : ∀ (C : ProperCurve sX) (hC : C.IsContractedBy f), ℓ (C.relativeClass f hC) < 0 :=
    hD
  have hv : A.relativeClass f hA ≠ 0 := fun h0 => (hℓ A hA).ne (by rw [h0, map_zero])
  obtain ⟨c, rfl⟩ := exists_smul_eq_of_relativePicardNumber_eq_one hρ hv z
  have hle : ℓ (c • A.relativeClass f hA) ≤ 0 := by
    have hS : IsClosed {w : RelativeNumericalCurveClasses sX f | ℓ w ≤ 0} := by
      refine isClosed_le ?_ continuous_const
      have := continuous_relativeCurveForm sX f D h
      rwa [MMP.Mori.QDivisor.relativeCurveForm_eq_comp] at this
    have hcone : (relativeConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f)) ⊆
        {w | ℓ w ≤ 0} := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨⟨C, hC⟩, rfl⟩ := hx
        exact (hℓ C hC).le
      | zero => simp
      | add x y _ _ hx hy =>
        simp only [Set.mem_ofPred_eq, map_add] at hx hy ⊢
        linarith
      | smul t x _ hx =>
        simp only [Set.mem_ofPred_eq] at hx ⊢
        rw [show t • x = (t : ℝ) • x from rfl, map_smul, smul_eq_mul]
        exact mul_nonpos_of_nonneg_of_nonpos t.2 hx
    rw [coe_relativeClosedConeOfCurves] at hz
    exact closure_minimal hcone hS hz
  have hc : c ≠ 0 := by
    rintro rfl
    exact hz0 (zero_smul _ _)
  rw [map_smul, smul_eq_mul] at hle ⊢
  exact lt_of_le_of_ne hle (mul_ne_zero hc (hℓ A hA).ne)

end RelativeClasses

section Descent

/-- **Descent of a numerically trivial Cartier divisor along a klt-negative contraction.** Let
`f : X ⟶ Z` be a birational contraction of projective varieties with `ρ(X/Z) = 1`, `(X, B)` klt
with `K + B` negative on the curves contracted by `f`. A Cartier divisor `D` of degree zero on
these curves is, up to the divisor of a rational function `u` of `Z`, the pull-back of a Cartier
divisor `E` on `Z`: `D - f^* E = div(f^* u)`. -/
private theorem exists_sub_pullback_eq_principalDivisor {k : Type} [Field k] {X Z : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Z] [CompactSpace Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {f : X ⟶ Z} (hfC : IsContraction sX sZ f)
    (hfb : IsBirationalMorphism f)
    (hX : MMP.Mori.IsProjectiveVariety k sX) (hZ : MMP.Mori.IsProjectiveVariety k sZ)
    (hρ : MMP.Flips.relativePicardNumber sX f = 1)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    {B : QDivisor X} (hB : IsKltPair sX B)
    (hKB : ∃ h : (Divisor.toQDivisor K + B).IsQCartier, ∀ A : ProperCurve sX,
      A.IsContractedBy f →
        QDivisor.curveForm sX (Divisor.toQDivisor K + B) h
          (OneCycle.numericalClass sX (A.cycle ℝ)) < 0)
    {D : Divisor X} (hDc : D.IsCartier)
    (hD0 : ∀ A : ProperCurve sX, A.IsContractedBy f → D.degreeOn k sX A.ι A.dim_le hDc = 0) :
    ∃ (E : Divisor Z) (hEc : E.IsCartier)
      (hfE : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ E.supp)
      (u : (RationalFunctions Z)ˣ)
      (hu : ∀ W : irreducibleComponents X,
        f (componentGenericPoint X W) ∉ (principalDivisor u).supp),
      D - E.pullback (f := f) hEc hfE = principalDivisor (pullbackRationalFunction f u hu) := by
  have hP := hB.1
  have := hP.isAlgClosed
  have := hP.charZero
  have : AlgebraicGeometry.IsProjectiveVariety k sX := hX
  have : AlgebraicGeometry.IsProjectiveVariety k sZ := hZ
  have hklt : MMP.Mori.IsKltPair sX n K B := (isKltPair_iff_mori_isKltPair sX hK hP).mp hB
  have hset : IsProjectiveSetting k sX sZ f := ⟨‹_›, ‹_›, hX, hZ, hfC.comp_eq⟩
  have hB0 : 0 ≤ B := hP.nonneg
  obtain ⟨hKBq, hKBneg⟩ := hKB
  set F := (relativeClosedConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f))
  have hFace : IsExtremalFace ℝ F F :=
    ⟨subset_rfl, isCone_coe _, fun u hu v hv => add_mem hu hv, fun u hu v hv _ => ⟨hu, hv⟩⟩
  have hF : IsNegativeExtremalFace ℝ F
      ((QDivisor.curveForm sX (Divisor.toQDivisor K + B) hklt.1.2.2).comp
        (relativeToAbsolute sX f)) F :=
    ⟨hFace, fun u hu v hv => add_mem hu hv, fun z hz hz0 =>
      curveForm_relativeToAbsolute_neg hρ _ hKBneg z hz hz0⟩
  have hψ : IsRelativeContractionOfFace f F f (𝟙 Z) :=
    ⟨hFace, isProjectiveMorphism_id _, Category.comp_id f, hfC.isIso_app, fun C hC =>
      ⟨fun _ => subset_closure (relativeClass_mem_relativeConeOfCurves hC), fun _ => hC⟩⟩
  have := hDc.isInvertibleModule_divisorialSheaf
  obtain ⟨LZ, hLZ, ⟨e⟩⟩ := exists_isInvertible_iso_pullback_of_isRelativeContractionOfFace hset
    hklt hB0 hF hψ D.divisorialSheaf (fun C hC _ => hD0 C hC)
  obtain ⟨E, hEc, ⟨e'⟩⟩ := MMP.Mori.exists_isCartier_divisorialSheaf_iso LZ
  have := hfb.isDominant
  have hfE := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' f E
  obtain ⟨e''⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso (f := f) hEc hfE
  obtain ⟨u, hu⟩ := MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso
    (e ≪≫ (Scheme.Modules.pullback f).mapIso e'.symm ≪≫ e''.symm)
  obtain ⟨uZ, huZ, rfl⟩ := exists_pullbackRationalFunction_eq hfb u
  exact ⟨E, hEc, hfE, uZ, huZ, hu⟩

end Descent

section SmallMaps

/-- **Prime divisors across two small maps.** Let `f : X ⟶ Z ⟵ X⁺ : f⁺` with `f` proper
birational, `Z` a normal variety and `f⁺` small. Every prime divisor `P⁺` of `X⁺` has a prime
divisor `P` of `X` whose coefficient in any `D` is that of `P⁺` in the strict transform
`(f⁺)⁻¹_* f_* D`, and at which the pull-backs of any Cartier divisor `G` of `Z` along `f` and
along `f⁺` have the same coefficient: both lie over the same prime divisor of `Z`, with
isomorphic local rings. -/
private theorem exists_primeDivisor_flipTransform_apply {k : Type} [Field k]
    {X Z X' : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sZ : Z ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {f : X ⟶ Z} {fp : X' ⟶ Z}
    (hZ : IsNormalVariety k sZ) [IsProper f] (hfb : IsBirationalMorphism f)
    (hfp : IsSmallMorphism sX' sZ fp) (P' : MMP.Mori.PrimeDivisor X') :
    ∃ P : MMP.Mori.PrimeDivisor X,
      (∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X), flipTransform f fp D P' = D P) ∧
      ∀ {G : Divisor Z} {hG : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ G.supp}
        {hG' : ∀ W : irreducibleComponents X', fp (componentGenericPoint X' W) ∉ G.supp}
        {G₁ : Divisor X} {G₂ : Divisor X'}, G.IsCartier → G.IsPullback f hG G₁ →
          G.IsPullback fp hG' G₂ → G₁.coeff P = G₂.coeff P' := by
  have := hfb.isDominant
  have := hfp.isBirationalMorphism.isDominant
  obtain ⟨P, Q, -, hPQ, hP'Q⟩ :=
    exists_primeDivisor_valuationOver_eq_of_isSmallMorphism hZ hfb hfp P'
  have hP := map_genericPoint_eq_of_image_eq P Q hPQ
  have hP' := map_genericPoint_eq_of_image_eq P' Q hP'Q
  obtain ⟨P₀, hP₀, htr⟩ :=
    exists_eq_genericPoint_flipTransform_apply hfb hfp P' P.genericPoint (hP.trans hP'.symm)
  obtain rfl : P₀ = P := AlgebraicGeometry.PrimeDivisor.genericPoint_injective hP₀.symm
  have := isIso_stalkMap_of_map_eq_genericPoint hfb hP
  have := isIso_stalkMap_of_map_eq_genericPoint hfp.isBirationalMorphism hP'
  refine ⟨P₀, htr, fun hGc h₁ h₂ => ?_⟩
  rw [MMP.Positivity.coeff_eq_of_isPullback P₀ Q hP hGc h₁,
    MMP.Positivity.coeff_eq_of_isPullback P' Q hP' hGc h₂]

end SmallMaps

/-- **A flip transfers a numerically trivial `ℚ`-Cartier divisor.** Let `fp : X⁺ ⟶ Z` be an
`L`-flip of `f : X ⟶ Z`, with `X` and `Z` projective, `X` `ℚ`-factorial and `ρ(X/Z) = 1`, and
let `B` be a klt boundary with `K + B` negative on every curve contracted by `f`. If a
`ℚ`-Cartier `ℚ`-divisor `P` on `X` has degree zero on every curve contracted by `f`, then its
strict transform `flipTransform f fp P` is `ℚ`-Cartier, and there is a `ℚ`-Cartier `ℚ`-divisor
`M` on `Z` with `P ∼_ℚ f^*M` and `flipTransform f fp P ∼_ℚ fp^*M`. -/
@[mmp "lem_fourfold_projective_flip_null_divisor_transfer"]
public theorem IsFlipOf.exists_qLinearlyEquivalent_pullback_of_curveForm_eq_zero
    {k : Type} [Field k] {X Z X' : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    [CompactSpace Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    {L : QDivisor X} {f : X ⟶ Z} {fp : X' ⟶ Z}
    (hflip : IsFlipOf sX sZ sX' L f fp)
    (hX : MMP.Mori.IsProjectiveVariety k sX) (hZ : MMP.Mori.IsProjectiveVariety k sZ)
    (hQ : IsQFactorial sX) (hρ : MMP.Flips.relativePicardNumber sX f = 1)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    {B : QDivisor X} (hB : IsKltPair sX B)
    (hKB : ∃ h : (Divisor.toQDivisor K + B).IsQCartier, ∀ A : ProperCurve sX,
      A.IsContractedBy f →
        QDivisor.curveForm sX (Divisor.toQDivisor K + B) h
          (OneCycle.numericalClass sX (A.cycle ℝ)) < 0)
    {P : QDivisor X} (hP : P.IsQCartier)
    (hP0 : ∀ A : ProperCurve sX, A.IsContractedBy f →
      QDivisor.curveForm sX P hP (OneCycle.numericalClass sX (A.cycle ℝ)) = 0) :
    QDivisor.IsQCartier (flipTransform f fp P) ∧
      ∃ (M : QDivisor Z) (hM : M.IsQCartier)
        (hfM : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ M.supp)
        (hfpM : ∀ W : irreducibleComponents X', fp (componentGenericPoint X' W) ∉ M.supp),
        P.QLinearlyEquivalent (QDivisor.pullback (f := f) M hM hfM) ∧
          QDivisor.QLinearlyEquivalent (flipTransform f fp P)
            (QDivisor.pullback (f := fp) M hM hfpM) := by
  have hfS := hflip.isSmallMorphism
  have hfpS := hflip.isSmallMorphism_flip
  have hfb := hfS.isBirationalMorphism
  have hZv := hfS.isNormalVariety_target
  have : IsProper f := hfS.isProper
  have : IsIntegral Z := hZv.1.toIsIntegral
  have : IsIntegral X' := hfpS.isNormalVariety_source.1.toIsIntegral
  have := hfb.isDominant
  have := hfpS.isBirationalMorphism.isDominant
  have : AlgebraicGeometry.IsProjectiveVariety k sX := hX
  -- a Cartier multiple `D = mP`, of degree zero on the contracted curves
  obtain ⟨m, hm, D, hDP, hDc⟩ := hP.exists_pos
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have hD0 : ∀ A : ProperCurve sX, A.IsContractedBy f →
      D.degreeOn k sX A.ι A.dim_le hDc = 0 := by
    intro A hA
    have h := hP0 A hA
    rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
      QDivisor.intersectionNumber_eq_of_smul k sX A.ι A.dim_le P hP hm D hDc hDP] at h
    simpa [hm.ne'] using h
  -- descent: `D - f^* E = div(f^* u)`
  obtain ⟨E, hEc, hfE, uZ, huZ, hDE⟩ :=
    exists_sub_pullback_eq_principalDivisor hflip.isContraction hfb hX hZ hρ hK hB hKB hDc hD0
  set M : QDivisor Z := (m : ℚ)⁻¹ • Divisor.toQDivisor E with hMdef
  have hmM : Divisor.toQDivisor E = (m : ℤ) • M := by
    rw [hMdef, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
    simp [hm.ne']
  have hM : M.IsQCartier := ⟨m, hm', E, hmM, hEc⟩
  have hfM := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' f M
  have hfpM :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' fp M
  obtain ⟨D₁, hD₁, hD₁p⟩ := QDivisor.isPullback_pullback (f := f) hM hfM m hm E hmM hEc
  obtain ⟨D₂, hD₂, hD₂p⟩ :=
    QDivisor.isPullback_pullback (f := fp) hM hfpM m hm E hmM hEc
  have hD₁e : E.pullback (f := f) hEc hfE = D₁ := hD₁p.pullback_eq hEc
  have hD₂c : D₂.IsCartier := hD₂p.pullback_eq hEc ▸ hEc.isCartier_pullback fp _
  have hu' := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' fp
    (principalDivisor uZ)
  set u' := pullbackRationalFunction fp uZ hu'
  -- across the two small maps, `m P⁺ = (f⁺)^* E + div(u')`
  have hDm : D = D₁ + principalDivisor (pullbackRationalFunction f uZ huZ) := by
    rw [← hD₁e, ← hDE, add_sub_cancel]
  have key : (m : ℤ) • flipTransform f fp P = Divisor.toQDivisor (D₂ + principalDivisor u') := by
    refine Finsupp.ext fun P' => ?_
    obtain ⟨Pm, htr, hcoeff⟩ := exists_primeDivisor_flipTransform_apply hZv hfb hfpS P'
    rw [Finsupp.smul_apply, htr, ← Finsupp.smul_apply, ← hDP]
    change ((D.coeff Pm : ℤ) : ℚ) = (((D₂ + principalDivisor u').coeff P' : ℤ) : ℚ)
    rw [hDm, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_add, hcoeff hEc hD₁p hD₂p,
      hcoeff (Divisor.isCartier_principalDivisor uZ) (Divisor.isPullback_principalDivisor uZ huZ)
        (Divisor.isPullback_principalDivisor uZ hu')]
  refine ⟨⟨m, hm', D₂ + principalDivisor u', key.symm,
    hD₂c.add (Divisor.isCartier_principalDivisor u')⟩, M, hM, hfM, hfpM, ?_, ?_⟩
  · refine ⟨m, hm, pullbackRationalFunction f uZ huZ, ?_⟩
    rw [smul_sub, ← hDP, ← hD₁, ← hD₁e, ← map_sub, hDE]
  · refine ⟨m, hm, u', ?_⟩
    rw [smul_sub, key, ← hD₂, map_add, add_sub_cancel_left]

end MMP.Fourfold
