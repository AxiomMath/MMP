module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Contraction.LineBundleDescent
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.Divisor.Pullback
public import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
public import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
public import MMP.AlgebraicGeometry.Singularities.LocalGenerator
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
public import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
public import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.SupportingDivisorStein
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts

section

/-!
# Proportionality of the adjoint and the plt prime on a pl-ray

Let `(X, Δ)` be a projective `ℚ`-factorial plt pair over an algebraically closed field of
characteristic zero, `⌊Δ⌋ = S` prime, and `f : X ⟶ Z` the contraction of an extremal ray `R`
with `-(K + Δ)` and `-S` both `f`-ample. We prove `a (K + Δ) ∼_ℚ b S + f^* M` with `a, b > 0`
and `M` Cartier on `Z`.

If `R` contains the class of a curve `C₀`, then `C₀` is contracted, so `(K + Δ) · C₀ < 0` and
`S · C₀ < 0`. As `S · C₀ < 0`, the curve `C₀` lies in `S`, so `dim X ≥ 2`, and the coefficient of
`S` in the plt boundary `Δ` is one (Kollár–Mori 2.31). The pair `(X, Δ - tS)` is then klt for
`0 < t ≤ 1`, because lowering the boundary by an effective `ℚ`-Cartier divisor does not lower
discrepancies, and for small `t` the ray `R` stays `(K + Δ - tS)`-negative. The Cartier divisor
`L = a (K + Δ) - b S` with `(L · C₀) = 0` is trivial on `R`, so the contraction theorem descends
`𝒪_X(L)` to an invertible sheaf on `Z`, which is `𝒪_Z(M)` for a Cartier divisor `M`, and
`L ∼ f^* M`.

If `R` contains no curve class, `f` contracts no curve, and `f` is also the contraction of the
face `{0}` of the salient cone `NE̅(X)`; the contraction theorem for the klt pair
`(X, Δ - (coeff_S Δ) S)` and the face `{0}` descends any Cartier multiple of `K + Δ - S`.

## References

* [KM98] J. Kollár, S. Mori, *Birational geometry of algebraic varieties*, Cor. 2.31, Thm. 3.7.
-/

open CategoryTheory AlgebraicGeometry MMP.Mori

namespace MMP.FourfoldProofs.FourfoldProjectivePlRayProportionalityProof

/-! ### Coefficients -/

/-- If `⌊Δ⌋ = S`, the coefficient of `S` lies in `[1, 2)` and every other coefficient in
`[0, 1)`. -/
private theorem coeff_bounds_of_roundDown_eq_single {X : Scheme.{0}} {Δ : QDivisor X}
    {S : MMP.Mori.PrimeDivisor X} (hS : Δ.roundDown = Finsupp.single S 1) :
    (1 ≤ Δ.coeff S ∧ Δ.coeff S < 2) ∧ ∀ P, P ≠ S → 0 ≤ Δ.coeff P ∧ Δ.coeff P < 1 := by
  have h (P : MMP.Mori.PrimeDivisor X) :
      ⌊Δ.coeff P⌋ = DivisorWithCoeffs.coeff (Finsupp.single S (1 : ℤ)) P := by
    rw [← DivisorWithCoeffs.coeff_roundDown, hS]
  refine ⟨?_, fun P hP => ?_⟩
  · have hS1 := h S
    rw [DivisorWithCoeffs.coeff_single_self, Int.floor_eq_iff] at hS1
    norm_num at hS1
    exact hS1
  · have hP0 := h P
    rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hP), Int.floor_eq_iff] at hP0
    norm_num at hP0
    exact hP0

/-- **The coefficients of an lc boundary are at most one** in dimension at least two
(Kollár–Mori 2.31). -/
private theorem coeff_le_one_of_isLcPair {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} (h : IsLcPair sX n K Δ) (hn : 2 ≤ n)
    (P : MMP.Mori.PrimeDivisor X) : Δ.coeff P ≤ 1 := by
  by_contra hlt
  push Not at hlt
  have hX := h.1.1
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy h.1.isPair h.1.2.1
    (DivisorOver.ofPrimeDivisor k hX P)
  have htot := totalDiscrep_le_neg_coeff hX ⟨a, ha⟩
  have hc : (((-Δ.coeff P : ℚ) : ℝ) : EReal) < ((-1 : ℝ) : EReal) := by
    refine EReal.coe_lt_coe_iff.mpr ?_
    have : (1 : ℝ) < (Δ.coeff P : ℝ) := by exact_mod_cast hlt
    push_cast
    linarith
  have hbot := MMP.Mori.discrep_eq_bot_of_totalDiscrep_lt_neg_one h.1 hn
    (htot.trans_lt (hc.trans_eq (by norm_num)))
  have h2 := h.2
  rw [hbot] at h2
  exact ((EReal.bot_lt_coe (-1)).trans_eq (by simp)).not_ge h2

/-! ### Dimension -/

/-- If every point of a proper curve `C` lies on a prime divisor `S` of a variety `X` of
dimension `n`, then `n ≥ 2`. -/
private theorem two_le_of_forall_mem_support {k : Type} [Field k] {X : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} {n : ℕ}
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) (S : MMP.Mori.PrimeDivisor X)
    (C : ProperCurve sX) (hC : ∀ c : C.scheme, C.ι c ∈ S.support) : 2 ≤ n := by
  obtain ⟨c, hc⟩ : ∃ c : C.scheme, C.ι c ≠ S.genericPoint := by
    by_contra! h
    exact Stacks.Chow.not_subsingleton_of_one_le_topologicalKrullDim C.dim_eq.ge
      ⟨fun a b => C.ι.isClosedEmbedding.injective ((h a).trans (h b).symm)⟩
  have hmem := hC c
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hmem
  have hsp : S.genericPoint ⤳ C.ι c := specializes_iff_mem_closure.mpr hmem
  have hlt : C.ι c < S.genericPoint :=
    ⟨Scheme.le_iff_specializes.mpr hsp,
      fun h => hc (hsp.antisymm (Scheme.le_iff_specializes.mp h)).eq.symm⟩
  have h2 : (2 : ℕ∞) ≤ Order.coheight (C.ι c) := by
    have := Order.coheight_add_one_le hlt
    rw [MMP.Mori.PrimeDivisor.coheight_genericPoint] at this
    exact le_trans (by norm_num) this
  have h3 : (Order.coheight (C.ι c) : WithBot ℕ∞) ≤ topologicalKrullDim X :=
    (Order.coheight_le_krullDim (C.ι c)).trans_eq
      (Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints).symm
  rw [hK.topologicalKrullDim_eq] at h3
  have h4 : ((2 : ℕ∞) : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) := (WithBot.coe_le_coe.mpr h2).trans h3
  exact_mod_cast h4

/-! ### Degrees on curves -/

section Degree

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
  [IsLocallyNoetherian X] [IsNormal X]

private theorem degreeOn_sub' (C : ProperCurve sX) (A B : Divisor X) (hA : A.IsCartier)
    (hB : B.IsCartier) :
    (A - B).degreeOn k sX C.ι C.dim_le (hA.sub hB) =
      A.degreeOn k sX C.ι C.dim_le hA - B.degreeOn k sX C.ι C.dim_le hB := by
  rw [Divisor.degreeOn_congr (sub_eq_add_neg A B) _ (hA.add hB.neg),
    Divisor.degreeOn_add k sX C.ι C.dim_le A (-B) hA hB.neg,
    Divisor.degreeOn_neg' k sX C.ι C.dim_le B hB]
  ring

/-- A Cartier divisor `E = mD`, `m > 0`, has negative degree on every curve contracted by `f`
when `-D` has an `f`-ample multiple. -/
private theorem degreeOn_neg_of_hasRelativelyAmpleMultiple [CompactSpace X] {Z : Scheme.{0}}
    {f : X ⟶ Z} {D : QDivisor X} (hD : (-D).HasRelativelyAmpleMultiple f) {E : Divisor X}
    (hE : E.IsCartier) {m : ℕ} (hm : 0 < m) (hEm : Divisor.toQDivisor E = (m : ℤ) • D)
    (C : ProperCurve sX) (hC : C.IsContractedBy f) : E.degreeOn k sX C.ι C.dim_le hE < 0 := by
  obtain ⟨m', hm', L, hL, hLD, hamp⟩ := hD
  have hpos : 0 < L.degreeOn k sX C.ι C.dim_le hL := by
    have := hL.isInvertibleModule_divisorialSheaf
    exact MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy f
      L.divisorialSheaf hamp C hC
  have hrel : (m : ℤ) • L = -((m' : ℤ) • E) := by
    apply Divisor.toQDivisor_injective
    rw [map_zsmul, map_neg, map_zsmul, hLD, hEm, smul_smul, smul_smul, smul_neg, mul_comm]
  have h1 := Divisor.degreeOn_zsmul' k sX C.ι C.dim_le L hL m
  rw [Divisor.degreeOn_congr hrel _ (hE.zsmul _).neg,
    Divisor.degreeOn_neg' k sX C.ι C.dim_le _ (hE.zsmul (m' : ℤ)),
    Divisor.degreeOn_zsmul' k sX C.ι C.dim_le E hE m'] at h1
  have : (0 : ℤ) < m := by exact_mod_cast hm
  have : (0 : ℤ) < m' := by exact_mod_cast hm'
  nlinarith

end Degree

/-! ### Klt perturbation -/

section Klt

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}

private theorem isQCartier_neg' {D : QDivisor X} (h : D.IsQCartier) : (-D).IsQCartier := by
  obtain ⟨m, hm, hD⟩ := h
  exact ⟨m, hm, by rw [smul_neg]; exact hD.neg⟩

/-- On a `ℚ`-factorial variety, `t S` is `ℚ`-Cartier for every prime divisor `S` and `t ∈ ℚ`. -/
private theorem isQCartier_single (hX : MMP.Fourfold.IsQFactorial sX) (S : MMP.Mori.PrimeDivisor X)
    (t : ℚ) : QDivisor.IsQCartier (Finsupp.single S t : QDivisor X) := by
  obtain ⟨m, hm, hmC⟩ := hX.2 (Finsupp.single S 1)
  refine ⟨(t.den : ℤ) * m, mul_ne_zero (by exact_mod_cast t.den_ne_zero) (by omega),
    t.num • ((m : ℤ) • Finsupp.single S 1), ?_, hmC.zsmul _⟩
  classical
  refine Finsupp.ext fun P => ?_
  change (((t.num • ((m : ℤ) • Finsupp.single S (1 : ℤ))) P : ℤ) : ℚ) =
    ((t.den : ℤ) * m) • (Finsupp.single S t P)
  rw [Finsupp.smul_apply, Finsupp.smul_apply, Finsupp.single_apply, Finsupp.single_apply]
  split_ifs
  · simp only [smul_eq_mul, zsmul_eq_mul, mul_one]
    push_cast
    rw [← Rat.mul_den_eq_num]
    ring
  · simp

/-- **Lowering a plt boundary along a prime divisor gives a klt pair.** If `(X, Δ)` is plt on a
`ℚ`-factorial variety, `t > 0` and every coefficient of `Δ - tS` is `< 1`, then `(X, Δ - tS)` is
klt. -/
private theorem isKltPair_sub_single (hX : MMP.Fourfold.IsQFactorial sX) {n : ℕ} {K : Divisor X}
    {Δ : QDivisor X} (hΔ : IsPltPair sX n K Δ) (S : MMP.Mori.PrimeDivisor X) {t : ℚ}
    (ht : 0 < t) (hlt : ∀ P, (Δ - Finsupp.single S t).coeff P < 1) :
    IsKltPair sX n K (Δ - Finsupp.single S t) := by
  have hTq := isQCartier_single hX S t
  have hTe : DivisorWithCoeffs.IsEffective (Finsupp.single S t : QDivisor X) := fun P => by
    by_cases h : S = P
    · subst h; rw [DivisorWithCoeffs.coeff_single_self]; exact ht.le
    · rw [DivisorWithCoeffs.coeff_single_of_ne h]
  have hQ : (Divisor.toQDivisor K + (Δ - Finsupp.single S t)).IsQCartier := by
    have : Divisor.toQDivisor K + (Δ - Finsupp.single S t) =
        (Divisor.toQDivisor K + Δ) + -Finsupp.single S t := by abel
    rw [this]
    exact hΔ.1.2.2.add (isQCartier_neg' hTq)
  refine ⟨⟨hΔ.1.1, hΔ.1.2.1, hQ⟩, ?_, roundDown_nonpos_iff.mpr hlt⟩
  calc (-1 : EReal) < discrep sX n K Δ := hΔ.2
    _ = discrep sX n K (Δ - Finsupp.single S t + Finsupp.single S t) := by rw [sub_add_cancel]
    _ ≤ discrep sX n K (Δ - Finsupp.single S t) :=
      MMP.Threefold.Mori.Helpers.discrep_add_le hTe hTq

end Klt

/-! ### Descent of line bundles -/

/-- An invertible module on an integral Noetherian normal scheme is `𝒪_Y(D)` for a Cartier
divisor `D`. -/
private theorem exists_isCartier_divisorialSheaf_iso {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (L : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L] :
    ∃ D : Divisor Y, D.IsCartier ∧ Nonempty (D.divisorialSheaf ≅ L) := by
  have := Stacks.SheafOfModules.isInvertible_of_tensorInvertible (X := Y.toRingedSpace) L
  have : ∀ z : Y.toRingedSpace.carrier,
      IsLocalRing (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Y.toRingedSpace z) :=
    Y.isLocalRing
  choose W hW a ha using fun y : Y =>
    Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible (X := Y.toRingedSpace) L y
  obtain ⟨y₀⟩ : Nonempty Y := inferInstance
  let F : LocalFrame L :=
    { W := W, mem := hW, a := a, isLocalGenerator := ha, base := y₀ }
  exact ⟨F.divisor, fun y => ⟨F.W y, F.mem y, _, F.isLocalEquation_divisor y⟩,
    ⟨(@asIso _ _ _ _ F.toDivisorialSheaf F.isIso_toDivisorialSheaf).symm⟩⟩

/-- **Descent along a klt contraction.** A Cartier divisor `D` of degree zero on the curves
with class in a `(K + Δ)`-negative extremal face `F` of a projective klt pair is linearly
equivalent to `f^* M`, for `f` the contraction of `F` and `M` Cartier on `Z`. -/
private theorem exists_linearlyEquivalent_pullback {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X Z : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX]
    [IsLocallyNoetherian Z] [IsNormal Z]
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} (hklt : IsKltPair sX n K Δ) (hΔ : Δ.IsEffective)
    {F : Set (NumericalCurveClasses sX)} {f : X ⟶ Z}
    (hF : IsNegativeExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
      (MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2) F)
    (hg : IsContractionOfFace k sX sZ F f) (D : Divisor X) (hD : D.IsCartier)
    (hdeg : ∀ C : ProperCurve sX, OneCycle.numericalClass sX (C.cycle ℝ) ∈ F →
      D.degreeOn k sX C.ι C.dim_le hD = 0) :
    ∃ (M : Divisor Z) (hM : M.IsCartier)
      (hMf : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ M.supp),
      D.LinearlyEquivalent (M.pullback hM hMf) := by
  haveI : AlgebraicGeometry.IsProjectiveVariety k sX := hg.isProjectiveVariety_source
  have hpZ := hg.isProjectiveVariety_target
  haveI : AlgebraicGeometry.IsVariety k sZ := hpZ.toIsVariety
  haveI : IsIntegral Z := hpZ.toIsVariety.toIsIntegral
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI := hD.isInvertibleModule_divisorialSheaf
  obtain ⟨LZ, hLZ, ⟨e⟩⟩ := exists_isInvertible_iso_pullback_of_isContractionOfFace hklt hΔ hF hg
    D.divisorialSheaf (fun C hC => by
      rw [ProperCurve.degree_divisorialSheaf C D hD, hdeg C hC])
  haveI := hLZ
  obtain ⟨M, hM, ⟨eM⟩⟩ := exists_isCartier_divisorialSheaf_iso LZ
  have : IsProper (f ≫ sZ) := hg.comp_eq ▸ inferInstance
  have : IsProper f := IsProper.of_comp f sZ
  have hsurj : Surjective f := Scheme.Hom.surjective_of_isIso_app f hg.isIso_app
  have hMf : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ M.supp := by
    intro W hW
    apply MMP.Fourfold.genericPoint_notMem_supp M
    obtain ⟨x, hx⟩ := hsurj.surj (genericPoint Z)
    have h1 : componentGenericPoint X W ⤳ x := by
      rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint]
      exact (genericPoint_spec X).specializes (Set.mem_univ x)
    rw [← hx]
    exact (h1.map f.continuous).mem_closed M.supp.isClosed hW
  have hpb := Divisor.isPullback_pullback hM hMf
  exact ⟨M, hM, hMf, MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso
    (e ≪≫ (Scheme.Modules.pullback f).mapIso eM.symm ≪≫
      (Divisor.IsPullback.divisorialSheafIso (hBc := hM) hpb).symm)⟩

/-- A linear equivalence `L ∼ L'` with `L = A - B` and `L' = P` gives `A ∼_ℚ B + P`. -/
private theorem qLinearlyEquivalent_of_linearlyEquivalent {X : Scheme.{0}}
    [IsLocallyNoetherian X] [CompactSpace X] [IsNormal X] {A B P : QDivisor X} {L L' : Divisor X}
    (hL : Divisor.toQDivisor L = A - B) (hL' : Divisor.toQDivisor L' = P)
    (h : L.LinearlyEquivalent L') : A.QLinearlyEquivalent (B + P) := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨1, one_pos, φ, ?_⟩
  rw [Nat.cast_one, one_smul, ← hφ, map_sub, hL, hL']
  abel

/-- The salient cone `NE̅(X)` of a projective variety has `{0}` as an extremal face. -/
private theorem isExtremalFace_zero {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [AlgebraicGeometry.IsProjectiveVariety k sX] :
    IsExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) {0} := by
  refine ⟨Set.singleton_subset_iff.mpr (closedConeOfCurves sX).zero_mem,
    ⟨rfl, fun v hv c _ => by simp [Set.mem_singleton_iff.mp hv]⟩,
    fun u hu v hv => by simp [Set.mem_singleton_iff.mp hu, Set.mem_singleton_iff.mp hv],
    fun u hu v hv huv => ?_⟩
  have hvu : v = -u := eq_neg_of_add_eq_zero_right (Set.mem_singleton_iff.mp huv)
  have hl : u ∈ (closedConeOfCurves sX).lineal :=
    PointedCone.mem_lineal.mpr ⟨hu, hvu ▸ hv⟩
  rw [lineal_closedConeOfCurves_eq_bot] at hl
  have hu0 : u = 0 := (Submodule.mem_bot ℝ).mp hl
  exact ⟨hu0, by simp [hvu, hu0]⟩

/-- If `(X, Δ)` is a `ℚ`-factorial plt pair with `⌊Δ⌋ = S` prime and `f : X ⟶ Z` contracts an
extremal ray on which `-(K + Δ)` and `-S` are `f`-ample, then `a (K + Δ) ∼_ℚ b S + f^* M` for
some positive integers `a, b` and a Cartier divisor `M` on `Z`. -/
theorem solution : ∀ {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X Z : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Z] [IsNormal Z]
    (hX : MMP.Fourfold.IsQFactorial sX) {R : Set (NumericalCurveClasses sX)}
    (hR : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R)
    {f : X ⟶ Z} (hf : IsContractionOfFace k sX sZ R f) (hZ : IsNormalVariety k sZ)
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} (hΔ : IsPltPair sX n K Δ)
    {S : MMP.Mori.PrimeDivisor X} (hS : Δ.roundDown = Finsupp.single S 1)
    (hKΔ : (-(Divisor.toQDivisor K + Δ)).HasRelativelyAmpleMultiple f)
    (hSneg : (-Divisor.toQDivisor (Finsupp.single S 1)).HasRelativelyAmpleMultiple f),
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ ∃ (M : Divisor Z) (hM : M.IsCartier)
      (hMf : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ M.supp),
      ((a : ℤ) • (Divisor.toQDivisor K + Δ)).QLinearlyEquivalent
        ((b : ℤ) • Divisor.toQDivisor (Finsupp.single S 1) +
          Divisor.toQDivisor (M.pullback hM hMf)) := by
  intro k _ _ _ X Z sX sZ _ _ _ _ _ _ hX R hR f hf hZ n K Δ hΔ S hS hKΔ hSneg
  classical
  haveI : AlgebraicGeometry.IsProjectiveVariety k sX := hf.isProjectiveVariety_source
  haveI : QuasiCompact sX := hf.isProjectiveVariety_source.toIsVariety.toQuasiCompact
  obtain ⟨⟨hcS1, hcS2⟩, hcP⟩ := coeff_bounds_of_roundDown_eq_single hS
  obtain ⟨m₁, hm₁, D₁, hD₁, hD₁c⟩ := hΔ.1.2.2.exists_pos
  obtain ⟨m₂, hm₂, hE₁c⟩ := hX.2 (Finsupp.single S 1)
  set E₁ : Divisor X := (m₂ : ℤ) • Finsupp.single S 1 with hE₁
  have hE₁q : Divisor.toQDivisor E₁ = (m₂ : ℤ) • Divisor.toQDivisor (Finsupp.single S 1) :=
    map_zsmul _ _ _
  have hfinal : ∀ a₀ b₀ : ℕ, 0 < a₀ → 0 < b₀ →
      ∀ (M : Divisor Z) (hM : M.IsCartier)
        (hMf : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ M.supp),
        ((a₀ : ℤ) • D₁ - (b₀ : ℤ) • E₁).LinearlyEquivalent (M.pullback hM hMf) →
      ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ ∃ (M : Divisor Z) (hM : M.IsCartier)
        (hMf : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ M.supp),
        ((a : ℤ) • (Divisor.toQDivisor K + Δ)).QLinearlyEquivalent
          ((b : ℤ) • Divisor.toQDivisor (Finsupp.single S 1) +
            Divisor.toQDivisor (M.pullback hM hMf)) := by
    intro a₀ b₀ ha₀ hb₀ M hM hMf h
    refine ⟨a₀ * m₁, b₀ * m₂, Nat.mul_pos ha₀ hm₁, Nat.mul_pos hb₀ hm₂, M, hM, hMf,
      qLinearlyEquivalent_of_linearlyEquivalent ?_ rfl h⟩
    rw [map_sub, map_zsmul, map_zsmul, hD₁, hE₁q, smul_smul, smul_smul]
    push_cast
    rfl
  by_cases hcurve : ∃ C₀ : ProperCurve sX, OneCycle.numericalClass sX (C₀.cycle ℝ) ∈ R
  · obtain ⟨C₀, hC₀R⟩ := hcurve
    have hC₀ : C₀.IsContractedBy f := (hf.isContractedBy_iff C₀).mpr hC₀R
    have hα : D₁.degreeOn k sX C₀.ι C₀.dim_le hD₁c < 0 :=
      degreeOn_neg_of_hasRelativelyAmpleMultiple hKΔ hD₁c hm₁ hD₁ C₀ hC₀
    have hβ : E₁.degreeOn k sX C₀.ι C₀.dim_le hE₁c < 0 :=
      degreeOn_neg_of_hasRelativelyAmpleMultiple hSneg hE₁c hm₂ hE₁q C₀ hC₀
    -- `C₀` lies in `S`, so `dim X ≥ 2` and the coefficient of `S` in `Δ` is one
    have hE₁eq : E₁ = Finsupp.single S (m₂ : ℤ) := by
      rw [hE₁, Finsupp.smul_single, smul_eq_mul, mul_one]
    have hn : 2 ≤ n := by
      refine two_le_of_forall_mem_support hΔ.1.2.1 S C₀ fun c => ?_
      by_contra hc
      haveI : IsIntegral C₀.scheme := C₀.isCurve.toIsIntegral
      have hE₁eff : 0 ≤ E₁ := by rw [hE₁eq]; exact Finsupp.single_nonneg.mpr (by positivity)
      have hnn := (MMP.Threefold.Mori.degreeOn_nonneg_and_eq_zero_iff sX C₀.ι C₀.dim_le E₁ hE₁c
        hE₁eff ⟨c, fun hmem => hc (by
          rw [hE₁eq] at hmem
          exact DivisorWithCoeffs.supp_single_le S _ hmem)⟩).1
      omega
    have hc1 : Δ.coeff S = 1 := le_antisymm (coeff_le_one_of_isLcPair hΔ.isLcPair hn S) hcS1
    -- the klt perturbation `Δ' = Δ - t S` with `t = 1 / N`
    set N : ℕ := m₁ * (E₁.degreeOn k sX C₀.ι C₀.dim_le hE₁c).natAbs + 1 with hNdef
    have hN : 0 < N := Nat.succ_pos _
    have hNq : (0 : ℚ) < N := by exact_mod_cast hN
    have ht1 : (N : ℚ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hN)
    have hcoef : ∀ P, (Δ - Finsupp.single S (N : ℚ)⁻¹).coeff P =
        if P = S then 1 - (N : ℚ)⁻¹ else Δ.coeff P := by
      intro P
      rw [DivisorWithCoeffs.coeff_sub]
      by_cases h : P = S
      · rw [h, DivisorWithCoeffs.coeff_single_self, hc1, if_pos rfl]
      · rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm h), if_neg h, sub_zero]
    have hklt := isKltPair_sub_single hX hΔ S (inv_pos.mpr hNq) fun P => by
      rw [hcoef]
      split_ifs with h
      · linarith [inv_pos.mpr hNq]
      · exact (hcP P h).2
    have hΔ'e : DivisorWithCoeffs.IsEffective (Δ - Finsupp.single S (N : ℚ)⁻¹) := fun P => by
      rw [hcoef]
      split_ifs with h
      · linarith
      · exact (hcP P h).1
    -- a Cartier multiple `G` of `K + Δ'`, negative on `C₀`
    set G : Divisor X := ((N * m₂ : ℕ) : ℤ) • D₁ - (m₁ : ℤ) • E₁ with hGdef
    have hGc : G.IsCartier := (hD₁c.zsmul _).sub (hE₁c.zsmul _)
    have hGq : Divisor.toQDivisor G =
        ((N * m₁ * m₂ : ℕ) : ℤ) • (Divisor.toQDivisor K + (Δ - Finsupp.single S (N : ℚ)⁻¹)) := by
      rw [hGdef, map_sub, map_zsmul, map_zsmul, hD₁, hE₁q]
      refine Finsupp.ext fun P => ?_
      change ((N * m₂ : ℕ) : ℤ) • ((m₁ : ℤ) • (((K P : ℤ) : ℚ) + Δ P)) -
          (m₁ : ℤ) • ((m₂ : ℤ) • (((Finsupp.single S (1 : ℤ) P : ℤ)) : ℚ)) =
        ((N * m₁ * m₂ : ℕ) : ℤ) • (((K P : ℤ) : ℚ) + (Δ P - Finsupp.single S (N : ℚ)⁻¹ P))
      rw [Finsupp.single_apply, Finsupp.single_apply]
      split_ifs
      · simp only [zsmul_eq_mul]
        push_cast
        field_simp
        ring
      · simp only [zsmul_eq_mul]
        push_cast
        ring
    have hdegG : G.degreeOn k sX C₀.ι C₀.dim_le hGc =
        ((N * m₂ : ℕ) : ℤ) * D₁.degreeOn k sX C₀.ι C₀.dim_le hD₁c -
          (m₁ : ℤ) * E₁.degreeOn k sX C₀.ι C₀.dim_le hE₁c := by
      rw [Divisor.degreeOn_congr hGdef hGc ((hD₁c.zsmul _).sub (hE₁c.zsmul _)),
        degreeOn_sub' C₀ _ _ (hD₁c.zsmul _) (hE₁c.zsmul _),
        Divisor.degreeOn_zsmul' k sX C₀.ι C₀.dim_le D₁ hD₁c,
        Divisor.degreeOn_zsmul' k sX C₀.ι C₀.dim_le E₁ hE₁c]
    have hGneg : G.degreeOn k sX C₀.ι C₀.dim_le hGc < 0 := by
      rw [hdegG]
      have hN' : (N : ℤ) = m₁ * (-E₁.degreeOn k sX C₀.ι C₀.dim_le hE₁c) + 1 := by
        rw [hNdef]
        push_cast
        rw [abs_of_neg hβ]
      have hm₂' : (1 : ℤ) ≤ m₂ := by exact_mod_cast hm₂
      have hα' : D₁.degreeOn k sX C₀.ι C₀.dim_le hD₁c ≤ -1 := by omega
      have hNpos : (0 : ℤ) < N := by exact_mod_cast hN
      have hNm : (0 : ℤ) ≤ N * m₂ := by positivity
      have h1 : (N : ℤ) * m₂ * D₁.degreeOn k sX C₀.ι C₀.dim_le hD₁c ≤ -((N : ℤ) * m₂) := by
        nlinarith [mul_le_mul_of_nonneg_left hα' hNm]
      have h2 : (N : ℤ) ≤ N * m₂ := by nlinarith
      push_cast
      nlinarith
    have hval0 : MMP.Fourfold.QDivisor.curveForm sX
        (Divisor.toQDivisor K + (Δ - Finsupp.single S (N : ℚ)⁻¹)) hklt.1.2.2
        (OneCycle.numericalClass sX (C₀.cycle ℝ)) < 0 := by
      rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle sX _ _ C₀,
        QDivisor.intersectionNumber_eq_of_smul k sX C₀.ι C₀.dim_le _ hklt.1.2.2
          (by positivity : 0 < N * m₁ * m₂) G hGc hGq]
      have : ((G.degreeOn k sX C₀.ι C₀.dim_le hGc : ℚ) / ((N * m₁ * m₂ : ℕ) : ℚ)) < 0 :=
        div_neg_of_neg_of_pos (by exact_mod_cast hGneg) (by positivity)
      exact_mod_cast this
    -- every class in `R` is a nonnegative multiple of `[C₀]`, and `R` is `(K + Δ')`-negative
    obtain ⟨v, hv0, hRv⟩ := hR.2
    obtain ⟨c₀, hc₀, hc₀v⟩ : ∃ c : ℝ, 0 ≤ c ∧ c • v = OneCycle.numericalClass sX (C₀.cycle ℝ) := by
      rw [hRv] at hC₀R
      exact hC₀R
    have hc₀pos : 0 < c₀ := by
      refine lt_of_le_of_ne hc₀ fun h => ?_
      rw [← hc₀v, ← h, zero_smul, map_zero] at hval0
      exact lt_irrefl _ hval0
    have hray : ∀ u ∈ R, ∃ l : ℝ, 0 ≤ l ∧ u = l • OneCycle.numericalClass sX (C₀.cycle ℝ) := by
      intro u hu
      rw [hRv] at hu
      obtain ⟨c, hc, rfl⟩ := hu
      exact ⟨c / c₀, div_nonneg hc hc₀pos.le, by
        rw [← hc₀v, smul_smul, div_mul_cancel₀ _ hc₀pos.ne']⟩
    have hF : IsNegativeExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
        (MMP.Fourfold.QDivisor.curveForm sX
          (Divisor.toQDivisor K + (Δ - Finsupp.single S (N : ℚ)⁻¹)) hklt.1.2.2) R := by
      refine ⟨hR.1, hR.1.2.2.1, fun u hu hu0 => ?_⟩
      obtain ⟨l, hl, rfl⟩ := hray u hu
      have hl0 : 0 < l := lt_of_le_of_ne hl fun h => hu0 (by rw [← h, zero_smul])
      rw [map_smul, smul_eq_mul]
      exact mul_neg_of_pos_of_neg hl0 hval0
    -- `L = |β| D₁ - |α| E₁` has degree zero on `C₀`, hence on every curve in `R`
    have hLc : (((E₁.degreeOn k sX C₀.ι C₀.dim_le hE₁c).natAbs : ℤ) • D₁ -
        ((D₁.degreeOn k sX C₀.ι C₀.dim_le hD₁c).natAbs : ℤ) • E₁).IsCartier :=
      (hD₁c.zsmul _).sub (hE₁c.zsmul _)
    have hL0 : (((E₁.degreeOn k sX C₀.ι C₀.dim_le hE₁c).natAbs : ℤ) • D₁ -
        ((D₁.degreeOn k sX C₀.ι C₀.dim_le hD₁c).natAbs : ℤ) • E₁).degreeOn k sX C₀.ι C₀.dim_le
          hLc = 0 := by
      rw [degreeOn_sub' C₀ _ _ (hD₁c.zsmul _) (hE₁c.zsmul _),
        Divisor.degreeOn_zsmul' k sX C₀.ι C₀.dim_le D₁ hD₁c,
        Divisor.degreeOn_zsmul' k sX C₀.ι C₀.dim_le E₁ hE₁c, Int.ofNat_natAbs_of_nonpos hβ.le,
        Int.ofNat_natAbs_of_nonpos hα.le]
      ring
    have hdeg : ∀ C : ProperCurve sX, OneCycle.numericalClass sX (C.cycle ℝ) ∈ R →
        (((E₁.degreeOn k sX C₀.ι C₀.dim_le hE₁c).natAbs : ℤ) • D₁ -
          ((D₁.degreeOn k sX C₀.ι C₀.dim_le hD₁c).natAbs : ℤ) • E₁).degreeOn k sX C.ι C.dim_le
            hLc = 0 := by
      intro C hC
      obtain ⟨l, -, hCl⟩ := hray _ hC
      haveI := hLc.isInvertibleModule_divisorialSheaf
      have key : ∀ C' : ProperCurve sX,
          ((((E₁.degreeOn k sX C₀.ι C₀.dim_le hE₁c).natAbs : ℤ) • D₁ -
            ((D₁.degreeOn k sX C₀.ι C₀.dim_le hD₁c).natAbs : ℤ) • E₁).degreeOn k sX C'.ι
              C'.dim_le hLc : ℝ) =
            NumericalCurveClasses.degree sX
              (((E₁.degreeOn k sX C₀.ι C₀.dim_le hE₁c).natAbs : ℤ) • D₁ -
                ((D₁.degreeOn k sX C₀.ι C₀.dim_le hD₁c).natAbs : ℤ) • E₁).divisorialSheaf
              (OneCycle.numericalClass sX (C'.cycle ℝ)) := fun C' => by
        rw [NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle,
          ProperCurve.degree_divisorialSheaf]
      have h1 := key C
      rw [hCl, map_smul, ← key C₀, hL0] at h1
      have h2 : (((((E₁.degreeOn k sX C₀.ι C₀.dim_le hE₁c).natAbs : ℤ) • D₁ -
          ((D₁.degreeOn k sX C₀.ι C₀.dim_le hD₁c).natAbs : ℤ) • E₁).degreeOn k sX C.ι C.dim_le
            hLc : ℤ) : ℝ) = 0 := by
        rw [h1]
        simp
      exact_mod_cast h2
    obtain ⟨M, hM, hMf, hlin⟩ := exists_linearlyEquivalent_pullback hklt hΔ'e hF hf _ hLc hdeg
    exact hfinal _ _ (Int.natAbs_pos.mpr hβ.ne) (Int.natAbs_pos.mpr hα.ne) M hM hMf hlin
  · push Not at hcurve
    have hcoef : ∀ P, (Δ - Finsupp.single S (Δ.coeff S)).coeff P =
        if P = S then 0 else Δ.coeff P := by
      intro P
      rw [DivisorWithCoeffs.coeff_sub]
      by_cases h : P = S
      · rw [h, DivisorWithCoeffs.coeff_single_self, if_pos rfl, sub_self]
      · rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm h), if_neg h, sub_zero]
    have hklt := isKltPair_sub_single hX hΔ S (by linarith) fun P => by
      rw [hcoef]
      split_ifs with h
      · norm_num
      · exact (hcP P h).2
    have hΔ'e : DivisorWithCoeffs.IsEffective (Δ - Finsupp.single S (Δ.coeff S)) := fun P => by
      rw [hcoef]
      split_ifs with h
      · exact le_rfl
      · exact (hcP P h).1
    have h0R : (0 : NumericalCurveClasses sX) ∈ R := hR.1.2.1.1
    have hF0 : IsNegativeExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
        (MMP.Fourfold.QDivisor.curveForm sX
          (Divisor.toQDivisor K + (Δ - Finsupp.single S (Δ.coeff S))) hklt.1.2.2) {0} :=
      ⟨isExtremalFace_zero, isExtremalFace_zero.2.2.1,
        fun z hz hz0 => absurd (Set.mem_singleton_iff.mp hz) hz0⟩
    have hg0 : IsContractionOfFace k sX sZ {0} f :=
      { hf with
        isExtremalFace := isExtremalFace_zero
        isContractedBy_iff := fun C =>
          ⟨fun h => (hcurve C ((hf.isContractedBy_iff C).mp h)).elim,
            fun h => (hcurve C (by rw [Set.mem_singleton_iff.mp h]; exact h0R)).elim⟩ }
    have hLc : (((1 : ℕ) : ℤ) • D₁ - ((1 : ℕ) : ℤ) • E₁).IsCartier :=
      (hD₁c.zsmul _).sub (hE₁c.zsmul _)
    obtain ⟨M, hM, hMf, hlin⟩ := exists_linearlyEquivalent_pullback hklt hΔ'e hF0 hg0 _ hLc
      fun C hC => (hcurve C (by rw [Set.mem_singleton_iff.mp hC]; exact h0R)).elim
    exact hfinal 1 1 one_pos one_pos M hM hMf hlin

end MMP.FourfoldProofs.FourfoldProjectivePlRayProportionalityProof

end

section

/-!
# Proportionality of the adjoint and the plt prime on a pl-ray

Let `(X, Δ)` be a projective `ℚ`-factorial plt pair over an algebraically closed field of
characteristic zero whose round-down `⌊Δ⌋ = S` is a prime divisor, and let `f : X ⟶ Z` be the
contraction of an extremal ray `R` of `NE̅(X)` onto a normal projective variety such that both
`-(K_X + Δ)` and `-S` are `f`-ample. Both `K_X + Δ` and `S` are negative on `R`, so a positive
combination `a (K_X + Δ) - b S` is numerically trivial over `Z`; perturbing to the klt pair
`(X, Δ - t S)` and applying the contraction theorem, it is `ℚ`-linearly equivalent to the
pull-back of a Cartier divisor on `Z`:
`a (K_X + Δ) ∼_ℚ b S + f^* M`.

## Main results

* `MMP.Fourfold.IsPltPair.exists_qLinearlyEquivalent_add_pullback_of_isContractionOfFace`.

## Implementation notes

The source works over `ℂ`; the statement is made over any algebraically closed field of
characteristic zero. The contraction is `MMP.Mori.IsContractionOfFace` for a face `R` which is
an extremal ray (`MMP.Mori.IsExtremalRay`); it carries the projectivity of `X` and `Z`.
The divisor `M` on `Z` is taken Cartier, the strongest of the source's two forms; the form with
a `ℚ`-Cartier `M` follows through `MMP.Mori.QDivisor.isPullback_toQDivisor`. The pull-back
`MMP.Mori.Divisor.pullback` carries the side condition that no generic point of `X` maps into
`Supp M`, packaged existentially with `M`.

## References

* [KM98] J. Kollár, S. Mori, *Birational geometry of algebraic varieties*, Thm. 3.7 (4).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

/-- **Adjoint–prime proportionality on a pl-ray.** Let `(X, Δ)` be a `ℚ`-factorial plt pair over
an algebraically closed field of characteristic zero, `K` a canonical divisor, with `⌊Δ⌋ = S`
a prime divisor, and let `f : X ⟶ Z` be the contraction of an extremal ray `R` of `NE̅(X)` onto
a normal projective variety such that `-(K + Δ)` and `-S` are `f`-ample. Then there are
positive integers `a, b` and a Cartier divisor `M` on `Z` with `a (K + Δ) ∼_ℚ b S + f^* M`. -/
@[mmp "lem_fourfold_projective_pl_ray_proportionality"]
public theorem IsPltPair.exists_qLinearlyEquivalent_add_pullback_of_isContractionOfFace
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X Z : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Z] [IsNormal Z]
    (hX : IsQFactorial sX) {R : Set (NumericalCurveClasses sX)}
    (hR : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R)
    {f : X ⟶ Z} (hf : IsContractionOfFace k sX sZ R f) (hZ : IsNormalVariety k sZ)
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} (hΔ : IsPltPair sX n K Δ)
    {S : MMP.Mori.PrimeDivisor X} (hS : Δ.roundDown = Finsupp.single S 1)
    (hKΔ : (-(Divisor.toQDivisor K + Δ)).HasRelativelyAmpleMultiple f)
    (hSneg : (-Divisor.toQDivisor (Finsupp.single S 1)).HasRelativelyAmpleMultiple f) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ ∃ (M : Divisor Z) (hM : M.IsCartier)
      (hMf : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ M.supp),
      ((a : ℤ) • (Divisor.toQDivisor K + Δ)).QLinearlyEquivalent
        ((b : ℤ) • Divisor.toQDivisor (Finsupp.single S 1) +
          Divisor.toQDivisor (M.pullback hM hMf)) :=
  MMP.FourfoldProofs.FourfoldProjectivePlRayProportionalityProof.solution hX hR hf hZ hΔ hS hKΔ hSneg

end MMP.Fourfold

end
