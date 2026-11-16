module

public import MMP.AlgebraicGeometry.MMP.Contraction.RelativeLineBundleDescent
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.DltNegativeFace

/-!
# Weil divisors on a flip of a `ℚ`-factorial dlt pair

Let `(X, Δ)` be a projective `ℚ`-factorial dlt pair over an algebraically closed field `k` of
characteristic zero, `R` a `(K_X + Δ)`-negative extremal ray of `NE̅(X)`, `g : X ⟶ Y` a
contraction of `R` which is a `(K + Δ)`-flipping contraction, and `g⁺ : X⁺ ⟶ Y` a `(K + Δ)`-flip
of `g`, with `K_{X⁺} = (g⁺)⁻¹_* g_* K_X` and `Δ⁺ = (g⁺)⁻¹_* g_* Δ`. Then every Weil divisor `D⁺`
on `X⁺` satisfies `m D⁺ + m r (K_{X⁺} + Δ⁺) ∼ (g⁺)^* D_Y` for some integer `m > 0`, a rational
number `r` with `m r (K_{X⁺} + Δ⁺)` Cartier, and a Cartier divisor `D_Y` on `Y`. This is the key
step in the proof that `X⁺` is again `ℚ`-factorial.

For a divisor `D⁺` on `X⁺` let `D` be its strict transform on `X`; it is `ℚ`-Cartier. Choose
integers so that the Cartier divisor `L = α (nD) + β (n_K (K + Δ))` has degree zero on a curve
whose class spans `R` (or on every contracted curve, if all of them are numerically trivial).
The degree of `L` then vanishes on every curve contracted by `g`, and `𝒪_X(L)` descends along
`g`: `L - g^* D_Y = div(g^* u)` for a Cartier divisor `D_Y` and a rational function `u` on `Y`.
Since `g` and `g⁺` are small, each prime divisor `P⁺` of `X⁺` and its strict transform `P` on
`X` lie over the same prime divisor of `Y`, with isomorphic local rings, so comparing
coefficients gives `m D⁺ + m r (K_{X⁺} + Δ⁺) - (g⁺)^* D_Y = div((g⁺)^* u)`.

## Main results

* `MMP.Mori.exists_linearlyEquivalent_pullback_of_isFlip`: the statement above.

## Implementation notes

The flip is `MMP.Mori.IsFlip`, which contains the flipping contraction
`MMP.Mori.IsFlippingContraction`; the transforms `K_{X⁺}`, `Δ⁺` are
`MMP.Mori.flipTransform g g⁺`. The ray is `MMP.Mori.IsExtremalRay` together with
`MMP.Mori.IsNegativeExtremalFace` for the linear form `((K + Δ) · _)`, and the contraction is
`MMP.Mori.IsContractionOfFace`. The divisor `m r (K_{X⁺} + Δ⁺)` being Cartier is
`MMP.Mori.QDivisor.IsCartierDivisor`, read as an integral divisor through
`MMP.Mori.QDivisor.IsCartierDivisor.toDivisor`. The pull-back `(g⁺)^* D_Y` is
`MMP.Mori.Divisor.pullback`, which asks that `g⁺` maps the generic point of `X⁺` outside
`Supp D_Y`; as `g⁺` is birational this holds for every divisor `D_Y`. The birational map
`φ = (g⁺)⁻¹ ∘ g` does not enter the conclusion and is not a hypothesis.

The descent step uses the relative klt statement
`MMP.Mori.exists_isInvertible_iso_pullback_of_isRelativeContractionOfFace` over `Y`, with
`ψ = g`, `𝟙 Y` and the face `{z ∈ NE̅(X/Y) | ι z ∈ R}`, after the perturbation of `Δ` to the klt
boundary `(1 - δ)Δ`; a curve `A` with `[A] ≠ 0` is used only to choose the rational number `r`,
and when every contracted curve is numerically trivial `r = 0`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Proposition 3.37
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Mori

section Cone

variable {k : Type} [Field k] {X Y : Scheme.{0}}

/-- The natural map `N₁(X/Y) → N₁(X)` is injective: a relative 1-cycle numerically trivial on
`X` is relatively numerically trivial. -/
private theorem relativeToAbsolute_injective (sX : X ⟶ Spec (.of k)) (f : X ⟶ Y) :
    Function.Injective (relativeToAbsolute sX f) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro z hz
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX f z
  rw [LinearMap.mem_ker, isNaturalRelativeMap_relativeToAbsolute sX f Z] at hz
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    ((Submodule.Quotient.mk_eq_zero (OneCycle.numericallyTrivial sX)).mp hz)

/-- The natural map `N₁(X/Y) → N₁(X)` is continuous for the numerical topologies. -/
private theorem continuous_relativeToAbsolute (sX : X ⟶ Spec (.of k)) (f : X ⟶ Y) :
    Continuous (relativeToAbsolute sX f) := by
  refine continuous_iInf_rng.2 fun L => continuous_iInf_rng.2 fun h =>
    continuous_induced_rng.2 ?_
  have he : ⇑(NumericalCurveClasses.degree sX L) ∘ ⇑(relativeToAbsolute sX f) =
      RelativeNumericalCurveClasses.degree sX f L := by
    funext z
    obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX f z
    rfl
  rw [he]
  exact RelativeNumericalCurveClasses.continuous_degree sX f L

/-- The natural map sends `NE̅(X/Y)` into `NE̅(X)`. -/
private theorem relativeToAbsolute_mem_closedConeOfCurves (sX : X ⟶ Spec (.of k)) (f : X ⟶ Y)
    {z : RelativeNumericalCurveClasses sX f} (hz : z ∈ relativeClosedConeOfCurves sX f) :
    relativeToAbsolute sX f z ∈ closedConeOfCurves sX := by
  have hcone : ∀ w ∈ relativeConeOfCurves sX f, relativeToAbsolute sX f w ∈ coneOfCurves sX := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨C, hC⟩, rfl⟩ := hx
      exact numericalClass_cycle_mem_coneOfCurves sX C
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul t x _ hx =>
      rw [show t • x = (t : ℝ) • x from rfl, map_smul]
      exact Submodule.smul_mem _ t hx
  have hz' : z ∈ closure (relativeConeOfCurves sX f : Set _) := by
    rwa [← coe_relativeClosedConeOfCurves]
  rw [← SetLike.mem_coe, coe_closedConeOfCurves]
  have h1 : relativeToAbsolute sX f z ∈
      closure (relativeToAbsolute sX f '' (relativeConeOfCurves sX f : Set _)) :=
    image_closure_subset_closure_image (continuous_relativeToAbsolute sX f) ⟨z, hz', rfl⟩
  exact closure_mono (by rintro _ ⟨w, hw, rfl⟩; exact hcone w hw) h1

/-- The classes in `NE̅(X/Y)` whose image in `N₁(X)` lies in an extremal face `R` of `NE̅(X)`
form an extremal face of `NE̅(X/Y)`. -/
private theorem isExtremalFace_preimage (sX : X ⟶ Spec (.of k)) (f : X ⟶ Y)
    {R : Set (NumericalCurveClasses sX)}
    (hR : IsExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R) :
    IsExtremalFace ℝ (relativeClosedConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f))
      {z | z ∈ relativeClosedConeOfCurves sX f ∧ relativeToAbsolute sX f z ∈ R} := by
  obtain ⟨-, ⟨h0, hsmul⟩, hadd, hext⟩ := hR
  refine ⟨fun z hz => hz.1, ⟨?_, fun v hv c hc => ?_⟩, fun u hu v hv => ?_,
    fun u hu v hv huv => ?_⟩
  · exact ⟨zero_mem _, by rw [map_zero]; exact h0⟩
  · exact ⟨Submodule.smul_mem _ (⟨c, hc.le⟩ : NNReal) hv.1, by
      rw [map_smul]; exact hsmul _ hv.2 c hc⟩
  · exact ⟨add_mem hu.1 hv.1, by rw [map_add]; exact hadd _ hu.2 _ hv.2⟩
  · have h := hext _ (relativeToAbsolute_mem_closedConeOfCurves sX f hu) _
      (relativeToAbsolute_mem_closedConeOfCurves sX f hv) (by rw [← map_add]; exact huv.2)
    exact ⟨⟨hu, h.1⟩, ⟨hv, h.2⟩⟩

end Cone

section Degree

variable {k : Type} [Field k] {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
  [CompactSpace X] (sX : X ⟶ Spec (.of k)) [QuasiCompact sX]

/-- The degree of a Cartier divisor on a curve is the degree of its sheaf on the numerical
class of the curve. -/
private theorem degreeOn_eq_degree_numericalClass {L : Divisor X} (hL : L.IsCartier)
    (C : ProperCurve sX) :
    haveI := hL.isInvertibleModule_divisorialSheaf
    (L.degreeOn k sX C.ι C.dim_le hL : ℝ) =
      NumericalCurveClasses.degree sX L.divisorialSheaf
        (OneCycle.numericalClass sX (C.cycle ℝ)) := by
  rw [NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle]
  rfl

/-- A Cartier divisor of degree zero on a curve `A` with `[A] ≠ 0` has degree zero on every
curve `C` with `[C]` on the line through `[A]`: both classes are multiples of one vector `v`. -/
private theorem degreeOn_eq_zero_of_smul_eq {v : NumericalCurveClasses sX} {L : Divisor X}
    (hL : L.IsCartier) {A C : ProperCurve sX} {cA cC : ℝ}
    (hA : cA • v = OneCycle.numericalClass sX (A.cycle ℝ))
    (hC : cC • v = OneCycle.numericalClass sX (C.cycle ℝ))
    (hA0 : OneCycle.numericalClass sX (A.cycle ℝ) ≠ 0)
    (hLA : L.degreeOn k sX A.ι A.dim_le hL = 0) : L.degreeOn k sX C.ι C.dim_le hL = 0 := by
  have := hL.isInvertibleModule_divisorialSheaf
  have hA' := degreeOn_eq_degree_numericalClass sX hL A
  have hC' := degreeOn_eq_degree_numericalClass sX hL C
  rw [hLA, ← hA, map_smul, smul_eq_mul, Int.cast_zero] at hA'
  rw [← hC, map_smul, smul_eq_mul] at hC'
  have hcA0 : cA ≠ 0 := by
    rintro rfl
    exact hA0 (by rw [← hA, zero_smul])
  have hv0 : NumericalCurveClasses.degree sX L.divisorialSheaf v = 0 :=
    (mul_eq_zero.1 hA'.symm).resolve_left hcA0
  have : ((L.degreeOn k sX C.ι C.dim_le hL : ℤ) : ℝ) = 0 := by rw [hC', hv0, mul_zero]
  exact_mod_cast this

/-- A Cartier divisor has degree zero on a numerically trivial curve. -/
private theorem degreeOn_eq_zero_of_numericalClass_eq_zero {L : Divisor X} (hL : L.IsCartier)
    {C : ProperCurve sX} (hC : OneCycle.numericalClass sX (C.cycle ℝ) = 0) :
    L.degreeOn k sX C.ι C.dim_le hL = 0 := by
  have := hL.isInvertibleModule_divisorialSheaf
  have hC' := degreeOn_eq_degree_numericalClass sX hL C
  rw [hC, map_zero] at hC'
  exact_mod_cast hC'

end Degree

section Descent

/-- **Descent along the contraction of a negative extremal ray of a dlt pair.** Let `(X, Δ)` be
a projective `ℚ`-factorial dlt pair, `R` a `(K + Δ)`-negative extremal ray and `g : X ⟶ Y` a
birational contraction of `R`. A Cartier divisor `L` of degree zero on every curve contracted by
`g` is `g^* E + div(g^* u)` for a Cartier divisor `E` and a rational function `u` on `Y`. -/
private theorem exists_sub_pullback_eq_principalDivisor
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX] [AlgebraicGeometry.IsProjectiveVariety k sX]
    (hQ : MMP.Fourfold.IsQFactorial sX) {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hdlt : IsDltPair sX n K Δ) {R : Set (NumericalCurveClasses sX)}
    (hR : IsNegativeExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
      (MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hdlt.1.2.2) R)
    {Y : Scheme.{0}} [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of k)} {g : X ⟶ Y}
    (hg : IsContractionOfFace k sX sY R g) (hgb : IsBirationalMorphism g)
    {L : Divisor X} (hLc : L.IsCartier)
    (hL0 : ∀ C : ProperCurve sX, C.IsContractedBy g → L.degreeOn k sX C.ι C.dim_le hLc = 0) :
    ∃ (E : Divisor Y) (hEc : E.IsCartier)
      (hgE : ∀ W : irreducibleComponents X, g (componentGenericPoint X W) ∉ E.supp)
      (u : (RationalFunctions Y)ˣ)
      (hu : ∀ W : irreducibleComponents X,
        g (componentGenericPoint X W) ∉ (principalDivisor u).supp),
      L - E.pullback (f := g) hEc hgE = principalDivisor (pullbackRationalFunction g u hu) := by
  set F := {z | z ∈ relativeClosedConeOfCurves sX g ∧ relativeToAbsolute sX g z ∈ R}
  have hFace : IsExtremalFace ℝ
      (relativeClosedConeOfCurves sX g : Set (RelativeNumericalCurveClasses sX g)) F :=
    isExtremalFace_preimage sX g hR.1
  have hneg : ∀ z ∈ F, z ≠ 0 →
      MMP.Fourfold.QDivisor.relativeCurveForm sX g (Divisor.toQDivisor K + Δ) hdlt.1.2.2 z < 0 := by
    intro z hz hz0
    rw [MMP.Mori.QDivisor.relativeCurveForm_eq_comp, LinearMap.comp_apply]
    exact hR.2.2 _ hz.2 fun h => hz0 (relativeToAbsolute_injective sX g (by rw [h, map_zero]))
  haveI : MMP.Mori.IsProjectiveVariety k sY := hg.isProjectiveVariety_target
  obtain ⟨δ, -, hδ1, hδ, hδneg⟩ :=
    hdlt.exists_isKltPair_one_sub_smul_of_isExtremalFace sY g hg.comp_eq hQ hFace hneg
  have hψ : IsRelativeContractionOfFace g F g (𝟙 Y) :=
    ⟨hFace, isProjectiveMorphism_id _, Category.comp_id g, hg.isIso_app, fun C hC =>
      ⟨fun _ => ⟨subset_closure (relativeClass_mem_relativeConeOfCurves hC),
        (hg.isContractedBy_iff C).1 hC⟩, fun _ => hC⟩⟩
  have := hLc.isInvertibleModule_divisorialSheaf
  obtain ⟨LY, hLY, ⟨e⟩⟩ := exists_isInvertible_iso_pullback_of_isRelativeContractionOfFace
    ⟨inferInstance, inferInstance, inferInstance, hg.isProjectiveVariety_target, hg.comp_eq⟩ hδ
    (smul_nonneg (sub_nonneg.2 hδ1.le) fun P => (hdlt.2.1 P).1)
    ⟨hFace, hFace.2.2.1, by rwa [← MMP.Mori.QDivisor.relativeCurveForm_eq_comp]⟩ hψ
    L.divisorialSheaf (fun C hC _ => hL0 C hC)
  obtain ⟨E, hEc, ⟨e'⟩⟩ := MMP.Mori.exists_isCartier_divisorialSheaf_iso LY
  have := hgb.isDominant
  have hgE := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' g E
  obtain ⟨e''⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso (f := g) hEc hgE
  obtain ⟨u, hu⟩ := MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso
    (e ≪≫ (Scheme.Modules.pullback g).mapIso e'.symm ≪≫ e''.symm)
  obtain ⟨uY, huY, rfl⟩ := MMP.Fourfold.exists_pullbackRationalFunction_eq hgb u
  exact ⟨E, hEc, hgE, uY, huY, hu⟩

/-- Given Cartier divisors `ED` and `EK`, with `EK` a positive multiple of `K + Δ`, and a
`(K + Δ)`-negative extremal ray `R` contracted by `g`, some combination `α ED + β EK` with `α > 0`
and `n' ∣ β` has degree zero on every curve contracted by `g`. -/
private theorem exists_degreeOn_zsmul_add_zsmul_eq_zero
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX] [AlgebraicGeometry.IsProjectiveVariety k sX]
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hdlt : IsDltPair sX n K Δ) {R : Set (NumericalCurveClasses sX)}
    (hRay : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R)
    (hR : IsNegativeExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
      (MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hdlt.1.2.2) R)
    {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of k)} {g : X ⟶ Y}
    (hg : IsContractionOfFace k sX sY R g) {ED EK : Divisor X} (hEDc : ED.IsCartier)
    (hEKc : EK.IsCartier) {nK : ℕ} (hnK : 0 < nK)
    (hEK : Divisor.toQDivisor EK = (nK : ℤ) • (Divisor.toQDivisor K + Δ)) {n' : ℕ} (hn' : 0 < n') :
    ∃ α β : ℤ, 0 < α ∧ (n' : ℤ) ∣ β ∧
      ∀ C : ProperCurve sX, C.IsContractedBy g →
        (α • ED + β • EK).degreeOn k sX C.ι C.dim_le ((hEDc.zsmul α).add (hEKc.zsmul β)) = 0 := by
  by_cases hA : ∃ A : ProperCurve sX, A.IsContractedBy g ∧
      OneCycle.numericalClass sX (A.cycle ℝ) ≠ 0
  · obtain ⟨A, hAc, hA0⟩ := hA
    set a := ED.degreeOn k sX A.ι A.dim_le hEDc
    set b := EK.degreeOn k sX A.ι A.dim_le hEKc
    have hb : b < 0 := by
      have h1 := hR.2.2 _ ((hg.isContractedBy_iff A).1 hAc) hA0
      rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
        QDivisor.intersectionNumber_eq_of_smul k sX A.ι A.dim_le _ hdlt.1.2.2 hnK EK hEKc
          hEK] at h1
      have h2 : ((b : ℚ) / nK) < 0 := by exact_mod_cast h1
      have h3 : (b : ℚ) < 0 := by
        by_contra! hcon
        exact h2.not_ge (div_nonneg hcon (by positivity))
      exact_mod_cast h3
    refine ⟨-b * n', n' * a, Int.mul_pos (by omega) (by exact_mod_cast hn'), ⟨a, rfl⟩,
      fun C hC => ?_⟩
    have hdA : ((-b * n') • ED + (n' * a) • EK).degreeOn k sX A.ι A.dim_le
        ((hEDc.zsmul _).add (hEKc.zsmul _)) = 0 := by
      rw [Divisor.degreeOn_add k sX A.ι A.dim_le _ _ (hEDc.zsmul _) (hEKc.zsmul _),
        MMP.Fourfold.degreeOn_zsmul sX A.ι A.dim_le _ hEDc,
        MMP.Fourfold.degreeOn_zsmul sX A.ι A.dim_le _ hEKc]
      ring
    obtain ⟨v, -, hReq⟩ := hRay.2
    have hmemA := (hg.isContractedBy_iff A).1 hAc
    have hmemC := (hg.isContractedBy_iff C).1 hC
    rw [hReq] at hmemA hmemC
    obtain ⟨cA, -, hcA⟩ := hmemA
    obtain ⟨cC, -, hcC⟩ := hmemC
    exact degreeOn_eq_zero_of_smul_eq sX _ hcA hcC hA0 hdA
  · exact ⟨1, 0, one_pos, dvd_zero _, fun C hC =>
      degreeOn_eq_zero_of_numericalClass_eq_zero sX _ (not_not.1 fun h => hA ⟨C, hC, h⟩)⟩

end Descent

section SmallMaps

/-- **Prime divisors across a flip.** Let `g : X ⟶ Y ⟵ X⁺ : g⁺` be small morphisms onto a normal
variety. Every prime divisor `P⁺` of `X⁺` has a prime divisor `P` of `X` such that the strict
transform `(g⁺)⁻¹_* g_*` takes the coefficient at `P` to the coefficient at `P⁺`, the strict
transform `g⁻¹_* g⁺_*` takes the coefficient at `P⁺` to the coefficient at `P`, and the pull-backs
of any Cartier divisor of `Y` along `g` and `g⁺` have the same coefficients at `P` and `P⁺`. -/
private theorem exists_primeDivisor_flipTransform_apply {k : Type} [Field k]
    {X Y X' : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    {g : X ⟶ Y} {gp : X' ⟶ Y}
    (hg : MMP.Fourfold.IsSmallMorphism sX sY g) (hgp : MMP.Fourfold.IsSmallMorphism sX' sY gp)
    (P' : MMP.Mori.PrimeDivisor X') :
    ∃ P : MMP.Mori.PrimeDivisor X,
      (∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X),
        flipTransform g gp D P' = D P) ∧
      (∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X'),
        flipTransform gp g D P = D P') ∧
      ∀ {G : Divisor Y} {hG : ∀ W : irreducibleComponents X, g (componentGenericPoint X W) ∉ G.supp}
        {hG' : ∀ W : irreducibleComponents X', gp (componentGenericPoint X' W) ∉ G.supp}
        {G₁ : Divisor X} {G₂ : Divisor X'}, G.IsCartier → G.IsPullback g hG G₁ →
          G.IsPullback gp hG' G₂ → G₁.coeff P = G₂.coeff P' := by
  have hgb := hg.isBirationalMorphism
  have hgpb := hgp.isBirationalMorphism
  have hYv := hg.isNormalVariety_target
  have : IsProper g := hg.isProper
  have : IsProper gp := hgp.isProper
  have := hgb.isDominant
  have := hgpb.isDominant
  obtain ⟨P, Q, -, hPQ, hP'Q⟩ :=
    MMP.Fourfold.exists_primeDivisor_valuationOver_eq_of_isSmallMorphism hYv hgb hgp P'
  have hP := MMP.Fourfold.map_genericPoint_eq_of_image_eq P Q hPQ
  have hP' := MMP.Fourfold.map_genericPoint_eq_of_image_eq P' Q hP'Q
  obtain ⟨P₀, hP₀, htr⟩ := MMP.Fourfold.exists_eq_genericPoint_flipTransform_apply hgb hgp P'
    P.genericPoint (hP.trans hP'.symm)
  obtain rfl : P₀ = P := AlgebraicGeometry.PrimeDivisor.genericPoint_injective hP₀.symm
  obtain ⟨P₁, hP₁, htr'⟩ := MMP.Fourfold.exists_eq_genericPoint_flipTransform_apply hgpb hg P₀
    P'.genericPoint (hP'.trans hP.symm)
  obtain rfl : P₁ = P' := AlgebraicGeometry.PrimeDivisor.genericPoint_injective hP₁.symm
  have := MMP.Fourfold.isIso_stalkMap_of_map_eq_genericPoint hgb hP
  have := MMP.Fourfold.isIso_stalkMap_of_map_eq_genericPoint hgpb hP'
  refine ⟨P₀, htr, htr', fun hGc h₁ h₂ => ?_⟩
  rw [MMP.Positivity.coeff_eq_of_isPullback P₀ Q hP hGc h₁,
    MMP.Positivity.coeff_eq_of_isPullback P₁ Q hP' hGc h₂]

/-- **Descent across a flip.** If `L - g^* E = div(g^* u)` on `X`, then the strict transform of
`L` on `X⁺` satisfies `(g⁺)⁻¹_* g_* L - (g⁺)^* E = div((g⁺)^* u)`. -/
private theorem flipTransform_sub_pullback_eq_principalDivisor {k : Type} [Field k]
    {X Y X' : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    {g : X ⟶ Y} {gp : X' ⟶ Y}
    (hg : MMP.Fourfold.IsSmallMorphism sX sY g) (hgp : MMP.Fourfold.IsSmallMorphism sX' sY gp)
    {L : Divisor X} {E : Divisor Y} (hEc : E.IsCartier)
    (hgE : ∀ W : irreducibleComponents X, g (componentGenericPoint X W) ∉ E.supp)
    (hB : ∀ W : irreducibleComponents X', gp (componentGenericPoint X' W) ∉ E.supp)
    {u : (RationalFunctions Y)ˣ}
    (hu : ∀ W : irreducibleComponents X, g (componentGenericPoint X W) ∉ (principalDivisor u).supp)
    (hu' : ∀ W : irreducibleComponents X',
      gp (componentGenericPoint X' W) ∉ (principalDivisor u).supp)
    (hLE : L - E.pullback (f := g) hEc hgE = principalDivisor (pullbackRationalFunction g u hu)) :
    flipTransform g gp L - E.pullback (f := gp) hEc hB =
      principalDivisor (pullbackRationalFunction gp u hu') := by
  refine Finsupp.ext fun P' => ?_
  obtain ⟨P, h1, -, h3⟩ := exists_primeDivisor_flipTransform_apply hg hgp P'
  have hL := congrArg (fun G : Divisor X => G P) hLE
  have e1 := h3 hEc (Divisor.isPullback_pullback (f := g) hEc hgE)
    (Divisor.isPullback_pullback (f := gp) hEc hB)
  have e2 := h3 (Divisor.isCartier_principalDivisor u)
    (Divisor.isPullback_principalDivisor (f := g) u hu)
    (Divisor.isPullback_principalDivisor (f := gp) u hu')
  simp only [DivisorWithCoeffs.coeff_apply] at e1 e2
  simp only [Finsupp.sub_apply] at hL ⊢
  rw [h1, ← e1, ← e2, hL]

/-- **Coefficients across a flip.** If `ED = nD D` for the strict transform `D` of `D⁺`,
`EK = nK (K + Δ)` and `C⁺ = n' (K⁺ + Δ⁺)`, and `m = nD α`, `β = n' γ`, then
`m D⁺ + γ nK C⁺` is the strict transform of `α ED + β EK`. -/
private theorem zsmul_add_zsmul_eq_flipTransform {k : Type} [Field k]
    {X Y X' : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    {g : X ⟶ Y} {gp : X' ⟶ Y}
    (hg : MMP.Fourfold.IsSmallMorphism sX sY g) (hgp : MMP.Fourfold.IsSmallMorphism sX' sY gp)
    {K ED EK : Divisor X} {Δ : QDivisor X} {D' C' : Divisor X'} {nD nK n' m : ℕ} {α β γ : ℤ}
    (hED : Divisor.toQDivisor ED = (nD : ℤ) • Divisor.toQDivisor (flipTransform gp g D'))
    (hEK : Divisor.toQDivisor EK = (nK : ℤ) • (Divisor.toQDivisor K + Δ))
    (hC' : Divisor.toQDivisor C' =
      (n' : ℤ) • (Divisor.toQDivisor (flipTransform g gp K) + flipTransform g gp Δ))
    (hγ : β = n' * γ) (hm : (m : ℚ) = nD * α) :
    (m : ℤ) • D' + (γ * nK) • C' = flipTransform g gp (α • ED + β • EK) := by
  refine Finsupp.ext fun P' => ?_
  obtain ⟨P, h1, h2, -⟩ := exists_primeDivisor_flipTransform_apply hg hgp P'
  have eD : ((ED P : ℤ) : ℚ) = nD * (D' P' : ℚ) := by
    have t := congrArg (fun G : QDivisor X => G P) hED
    simp only [Finsupp.smul_apply, zsmul_eq_mul, Int.cast_natCast] at t
    rwa [← h2 D']
  have eK : ((EK P : ℤ) : ℚ) = nK * ((K P : ℚ) + Δ P) := by
    have t := congrArg (fun G : QDivisor X => G P) hEK
    simp only [Finsupp.smul_apply, Finsupp.add_apply, zsmul_eq_mul, Int.cast_natCast] at t
    exact t
  have eC : ((C' P' : ℤ) : ℚ) = n' * ((K P : ℚ) + Δ P) := by
    have t := congrArg (fun G : QDivisor X' => G P') hC'
    simp only [Finsupp.smul_apply, Finsupp.add_apply, zsmul_eq_mul, Int.cast_natCast] at t
    rwa [← h1 K, ← h1 Δ]
  rw [h1]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  have key : (((m : ℤ) * D' P' + (γ * nK) * C' P' : ℤ) : ℚ) = ((α * ED P + β * EK P : ℤ) : ℚ) := by
    push_cast
    rw [eD, eK, eC, hγ, hm]
    push_cast
    ring
  exact_mod_cast key

end SmallMaps

/-- **Weil divisors on a flip** (Kollár–Mori, proof of Proposition 3.37). Let `(X, Δ)` be a
projective `ℚ`-factorial dlt pair over an algebraically closed field of characteristic zero with
canonical divisor `K`, `R` a `(K + Δ)`-negative extremal ray of `NE̅(X)`, `g : X ⟶ Y` a
contraction of `R`, and `g⁺ : X⁺ ⟶ Y` a `(K + Δ)`-flip of `g`. Write
`K⁺ + Δ⁺ = flipTransform g g⁺ K + flipTransform g g⁺ Δ`. Then for every divisor `D⁺` on `X⁺`
there are `m > 0`, `r ∈ ℚ` with `m r (K⁺ + Δ⁺)` a Cartier divisor, and a Cartier divisor `D_Y`
on `Y` with `m D⁺ + m r (K⁺ + Δ⁺)` linearly equivalent to `(g⁺)^* D_Y`. -/
@[mmp "lem_km3c_flip_weil_divisor_formula"]
public theorem exists_linearlyEquivalent_pullback_of_isFlip
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX] [AlgebraicGeometry.IsProjectiveVariety k sX]
    (hQ : MMP.Fourfold.IsQFactorial sX) {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hdlt : IsDltPair sX n K Δ) {R : Set (NumericalCurveClasses sX)}
    (hRay : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R)
    (hR : IsNegativeExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
      (MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hdlt.1.2.2) R)
    {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of k)} {g : X ⟶ Y}
    (hg : IsContractionOfFace k sX sY R g)
    {X' : Scheme.{0}} [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sX' : X' ⟶ Spec (.of k)} {gp : X' ⟶ Y} (hflip : IsFlip sX sY sX' K Δ g gp)
    (D' : Divisor X') :
    ∃ m : ℕ, 0 < m ∧ ∃ r : ℚ,
      ∃ hc : (((m : ℚ) * r) • (Divisor.toQDivisor (flipTransform g gp K) +
          flipTransform g gp Δ)).IsCartierDivisor,
      ∃ (DY : Divisor Y) (hDY : DY.IsCartier)
        (hB : ∀ Z : irreducibleComponents X', gp (componentGenericPoint X' Z) ∉ DY.supp),
        ((m : ℤ) • D' + hc.toDivisor).LinearlyEquivalent (DY.pullback hDY hB) := by
  have hFC := hflip.isFlippingContraction
  have hYv := hFC.isNormalVariety_target
  haveI : IsIntegral Y := hYv.1.toIsIntegral
  haveI : IsIntegral X' := hflip.isNormalVariety.1.toIsIntegral
  haveI : MMP.Mori.IsProjectiveVariety k sY := hg.isProjectiveVariety_target
  haveI : QuasiCompact sY := hYv.1.toQuasiCompact
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have hgS : MMP.Fourfold.IsSmallMorphism sX sY g :=
    ⟨hFC.isNormalVariety_source, hYv, hFC.comp_eq, hFC.isProper, hFC.isBirationalMorphism,
      hFC.two_le_codimension⟩
  have hgpS : MMP.Fourfold.IsSmallMorphism sX' sY gp :=
    ⟨hflip.isNormalVariety, hYv, hflip.comp_eq, hflip.isProper, hflip.isBirationalMorphism,
      hflip.two_le_codimension⟩
  have hgb := hFC.isBirationalMorphism
  haveI := hgb.isDominant
  haveI := hflip.isBirationalMorphism.isDominant
  set H' : QDivisor X' := Divisor.toQDivisor (flipTransform g gp K) + flipTransform g gp Δ
  obtain ⟨nD, hnD, hcD⟩ := (MMP.Fourfold.isQCartier_of_isQFactorial sX hQ
    (Divisor.toQDivisor (flipTransform gp g D'))).exists_pos
  obtain ⟨nK, hnK, hcK⟩ := hdlt.1.2.2.exists_pos
  obtain ⟨n', hn', hc'⟩ := hflip.isQCartier.exists_pos
  obtain ⟨α, β, hα, ⟨γ, hγ⟩, hdeg⟩ := exists_degreeOn_zsmul_add_zsmul_eq_zero hdlt hRay hR hg
    hcD.isCartier_toDivisor hcK.isCartier_toDivisor hnK hcK.toQDivisor_toDivisor hn'
  obtain ⟨E, hEc, hgE, u, hu, hLE⟩ := exists_sub_pullback_eq_principalDivisor hQ hdlt hR hg hgb
    ((hcD.isCartier_toDivisor.zsmul α).add (hcK.isCartier_toDivisor.zsmul β)) hdeg
  set m : ℕ := nD * α.toNat with hm
  have hαn : ((α.toNat : ℕ) : ℤ) = α := Int.toNat_of_nonneg hα.le
  have hm0 : 0 < m := Nat.mul_pos hnD (by omega)
  set r : ℚ := ((β * nK : ℤ) : ℚ) / m with hr
  have hmr : (m : ℚ) * r = ((γ * nK : ℤ) : ℚ) * n' := by
    rw [hr, mul_div_cancel₀ _ (by exact_mod_cast hm0.ne'), hγ]
    push_cast
    ring
  have hcQ : Divisor.toQDivisor ((γ * nK) • hc'.toDivisor) = ((m : ℚ) * r) • H' := by
    rw [map_zsmul, hc'.toQDivisor_toDivisor, hmr, smul_smul, ← Int.cast_smul_eq_zsmul ℚ]
    push_cast
    rfl
  have hc : (((m : ℚ) * r) • H').IsCartierDivisor :=
    ⟨_, hcQ, hc'.isCartier_toDivisor.zsmul _⟩
  have hB := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' gp E
  have hu' := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' gp
    (principalDivisor u)
  refine ⟨m, hm0, r, hc, E, hEc, hB, pullbackRationalFunction gp u hu', ?_⟩
  rw [hc.toDivisor_eq_iff.mpr hcQ, zsmul_add_zsmul_eq_flipTransform hgS hgpS
    hcD.toQDivisor_toDivisor hcK.toQDivisor_toDivisor hc'.toQDivisor_toDivisor hγ
    (by rw [hm, Nat.cast_mul, show ((α.toNat : ℕ) : ℚ) = α by exact_mod_cast hαn])]
  exact flipTransform_sub_pullback_eq_principalDivisor hgS hgpS hEc hgE hB hu hu' hLE

end MMP.Mori
