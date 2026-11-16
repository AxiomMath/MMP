module

public import MMP.AlgebraicGeometry.MMP.Contraction.DivisorialExceptionalOnRay
public import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve

/-!
# Divisorial contractions preserve `ℚ`-factoriality

Let `X` be a `ℚ`-factorial projective variety over an algebraically closed field `k` of
characteristic zero, `(X, Δ)` a klt pair with `Δ` effective, `R` an extremal ray of `NE̅(X)` on
which `K_X + Δ` is negative away from `0`, and `g : X ⟶ Z` a contraction of `R` which is a
divisorial contraction. Then `Z` is `ℚ`-factorial.

## Main results

* `MMP.Mori.isQFactorial_of_isDivisorialContraction`: the statement above.

## Proof outline

Let `E` be the exceptional divisor of `g`. For a Weil divisor `B` on `Z`, let `B'` be its strict
transform, so `g_* B' = B`. If `C` is a curve with `[C] ∈ R`, then `(E · C) ≠ 0`, so
`s = -(B' · C)/(E · C)` makes `B' + sE` trivial on `R`. A Cartier multiple `D = m(B' + sE)` then
has `𝒪_X(D) ≅ g^* L_Z` with `L_Z ≅ 𝒪_Z(M)`, `M` Cartier, so `D ∼ g^* M`. Pushing forward,
`mB = g_* D ∼ g_* g^* M = M`, since `g_* E = 0`; hence `mB` is Cartier.

## Implementation notes

`MMP.Fourfold.IsQFactorial` is stated for a locally noetherian normal scheme, so the target `Z`
carries the instance arguments `[IsLocallyNoetherian Z] [IsNormal Z]`. Both hold for every
divisorial contraction (`Z` is a projective variety, and normal because `g_* 𝒪_X = 𝒪_Z` with
`X` normal), so these arguments do not restrict the statement.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Corollary 3.18
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

section Helpers

variable {k : Type} [Field k]

/-- A prime divisor `E` whose support is the exceptional set of a proper birational morphism
`f : X ⟶ Y` to a normal variety maps to no prime divisor of `Y`: `f(η_E)` lies outside the
biregular locus of `f`, whose complement has codimension at least two. -/
private theorem map_genericPoint_ne_of_support_eq_exceptionalSet {X Y : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} (hY : MMP.Mori.IsVariety k sY) [IsNormal Y] {f : X ⟶ Y}
    (hX : MMP.Mori.IsVariety k (f ≫ sY)) [IsProper f] (hf : IsBirationalMorphism f)
    {E : MMP.Mori.PrimeDivisor X} (hE : (exceptionalSet f : Set X) = E.support)
    (P : MMP.Mori.PrimeDivisor Y) : f E.genericPoint ≠ P.genericPoint := by
  intro hP
  have hmem : P.genericPoint ∈ ((biregularLocus f).compl : Set Y) := by
    rw [← hP]
    have : E.genericPoint ∈ (exceptionalSet f : Set X) := by
      rw [hE, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    exact this
  have hcod := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp
    (MMP.Mori.two_le_closedsCodimension_compl_biregularLocus sY f (hY := hY) (hX := hX) hf) _ hmem
  rw [P.coheight_genericPoint] at hcod
  exact absurd hcod (by decide)

/-- On a projective variety the class `[C] ∈ N₁(X)` of a proper curve is nonzero: an ample
invertible sheaf has positive degree on `C`. -/
private theorem numericalClass_cycle_ne_zero {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    (hX : MMP.Mori.IsProjectiveVariety k sX) (C : ProperCurve sX) :
    OneCycle.numericalClass sX (C.cycle ℝ) ≠ 0 := by
  have hproj : IsProjectiveMorphism sX := ((MMP.Mori.isProjectiveVariety_iff k sX).mp hX).2
  obtain ⟨L, hL, hLa⟩ := exists_isAmple_of_isQuasiProjective sX
    (Stacks.Ample.unitModule (Spec (.of k)))
    (Stacks.Ample.isAmple_unitModule_of_isAffine _)
    (isQuasiProjective_of_isHQuasiProjective sX hproj.isHQuasiProjective)
  have : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L := inferInstance
  have hpos := MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy sX L
    (MMP.Threefold.Resolution.isRelativelyAmple_of_isAmple sX L hLa) C
    (fun _ _ => Subsingleton.elim _ _)
  intro h0
  have h := OneCycle.mem_numericallyTrivial.mp ((Submodule.Quotient.mk_eq_zero _).mp h0) L
  rw [OneCycle.degree_cycle] at h
  have : (0 : ℝ) < (degreeOn k sX C.ι C.dim_le L : ℝ) := by exact_mod_cast hpos
  exact this.ne' h

/-- **Invertible sheaves are divisorial, with a Cartier divisor.** On an integral, locally
Noetherian, normal, quasi-compact scheme `Y`, every invertible `𝒪_Y`-module is `𝒪_Y(D)` for a
Cartier divisor `D`: the divisor of a local frame has the frame's transition functions as local
equations. -/
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
    { W := W, mem := hW, a := a, isLocalGenerator := fun y V hV => ha y V hV, base := y₀ }
  have := F.isIso_toDivisorialSheaf
  exact ⟨F.divisor, fun y => ⟨F.W y, F.mem y, _, F.isLocalEquation_divisor y⟩,
    ⟨(asIso F.toDivisorialSheaf).symm⟩⟩

end Helpers

/-- **Divisorial contractions preserve `ℚ`-factoriality** (Kollár–Mori, Corollary 3.18). Let `X`
be a `ℚ`-factorial projective variety over an algebraically closed field `k` of characteristic
zero, `(X, Δ)` a klt pair with canonical divisor `K` and `Δ` effective, `R` a subset of `N₁(X)`
with `(K + Δ) · z < 0` for `0 ≠ z ∈ R`, and `g : X ⟶ Z` a divisorial contraction of the extremal
ray `R`. Then `Z` is `ℚ`-factorial. -/
@[mmp "thm_km3b_divisorial_contraction_q_factorial"]
public theorem isQFactorial_of_isDivisorialContraction {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [AlgebraicGeometry.IsProjectiveVariety k sX] (hQ : MMP.Fourfold.IsQFactorial sX)
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hklt : IsKltPair sX n K Δ) (hΔ : Δ.IsEffective) {R : Set (NumericalCurveClasses sX)}
    (hR : ∀ z ∈ R, z ≠ 0 →
      MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2 z < 0)
    {Z : Scheme.{0}} [IsLocallyNoetherian Z] [IsNormal Z] {sZ : Z ⟶ Spec (.of k)} {g : X ⟶ Z}
    (hg : IsDivisorialContraction k sX sZ R g) :
    MMP.Fourfold.IsQFactorial sZ := by
  obtain ⟨E, hE⟩ := hg.exists_primeDivisor
  have hc := hg.isContractionOfFace
  have hbir := hg.isBirationalMorphism
  obtain ⟨hXv, hXproj⟩ := (MMP.Mori.isProjectiveVariety_iff k sX).mp hc.isProjectiveVariety_source
  obtain ⟨hZv, hZproj⟩ := (MMP.Mori.isProjectiveVariety_iff k sZ).mp
    hc.isProjectiveVariety_target
  have hXv' : MMP.Mori.IsVariety k (g ≫ sZ) := hc.comp_eq ▸ hXv
  have hZn : IsNormalVariety k sZ := ⟨hZv, inferInstance⟩
  have hXn : IsNormalVariety k (g ≫ sZ) := ⟨hXv', inferInstance⟩
  have : IsIntegral Z := hZv.toIsIntegral
  have : IsProper sX := isProper_of_isProjectiveMorphism sX hXproj
  have : IsProper sZ := isProper_of_isProjectiveMorphism sZ hZproj
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  have : IsProper (g ≫ sZ) := hc.comp_eq ▸ inferInstance
  have : IsProper g := IsProper.of_comp g sZ
  have : IsDominant g := hbir.isDominant
  refine ⟨hZn, fun B => ?_⟩
  choose ι hιgen _ hιtr using
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hZn hXn hbir
  have hιinj : Function.Injective ι := fun P Q h =>
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      ((hιgen P).symm.trans (h ▸ hιgen Q))
  have hιE : ∀ P, ι P ≠ E := fun P h =>
    map_genericPoint_ne_of_support_eq_exceptionalSet hZv hXv' hbir hE P (h ▸ hιgen P)
  set B' : Divisor X := Finsupp.mapDomain ι B
  have hB' : ∀ P, B' (ι P) = B P := fun P => Finsupp.mapDomain_apply_of_injective hιinj B P
  obtain ⟨hEq, hEne⟩ := curveForm_single_ne_zero_of_isDivisorialContraction hQ hklt hΔ hR hg hE
  have hRray := hg.isExtremalRay
  obtain ⟨v, hv0, hRv⟩ := hRray.2
  have hF : IsNegativeExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
      (MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2) R :=
    ⟨hRray.1, hRray.1.2.2.1, hR⟩
  have hF0 : R ≠ {0} := fun h => hv0 (by
    have : v ∈ R := by rw [hRv]; exact ⟨1, zero_le_one, one_smul _ _⟩
    rw [h] at this
    exact this)
  obtain ⟨C, hCR⟩ := exists_properCurve_numericalClass_mem_of_isNegativeExtremalFace hklt hΔ hF hF0
  have hC0 := numericalClass_cycle_ne_zero hc.isProjectiveVariety_source C
  have hQc := MMP.Fourfold.isQCartier_of_isQFactorial sX hQ
  set e : ℚ := QDivisor.intersectionNumber k sX C.ι C.dim_le (Finsupp.single E (1 : ℚ)) hEq
    with he_def
  set b : ℚ := (Divisor.toQDivisor B').intersectionNumber k sX C.ι C.dim_le (hQc _) with hb_def
  have he : e ≠ 0 := by
    intro h0
    apply hEne _ hCR hC0
    rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle, ← he_def, h0, Rat.cast_zero]
  set s : ℚ := -b / e with hs_def
  have hDsC : QDivisor.intersectionNumber k sX C.ι C.dim_le
      (Divisor.toQDivisor B' + s • Finsupp.single E 1) (hQc _) = 0 := by
    rw [QDivisor.intersectionNumber_add' k sX C.ι C.dim_le _ _ (hQc _) (hQc _),
      MMP.Fourfold.intersectionNumber_smul (k := k) sX C.ι C.dim_le _ hEq s (hQc _), ← he_def,
      ← hb_def, hs_def]
    field_simp
    ring
  set Ds : QDivisor X := Divisor.toQDivisor B' + s • Finsupp.single E 1 with hDs_def
  have hDs : Ds.IsQCartier := hQc Ds
  have hDsR : ∀ C' : ProperCurve sX, OneCycle.numericalClass sX (C'.cycle ℝ) ∈ R →
      Ds.intersectionNumber k sX C'.ι C'.dim_le hDs = 0 := by
    intro C' hC'
    rw [hRv] at hCR hC'
    obtain ⟨c, -, hcv⟩ := hCR
    obtain ⟨c', -, hc'v⟩ := hC'
    have hc : c ≠ 0 := by rintro rfl; exact hC0 (by rw [← hcv, zero_smul])
    have h1 := MMP.ProgramBaseChange.curveForm_numericalClass_cycle sX Ds hDs C
    have h2 := MMP.ProgramBaseChange.curveForm_numericalClass_cycle sX Ds hDs C'
    rw [← hcv, map_smul, hDsC, smul_eq_mul, Rat.cast_zero] at h1
    rw [← hc'v, map_smul, smul_eq_mul] at h2
    have hv : MMP.Fourfold.QDivisor.curveForm sX Ds hDs v = 0 :=
      (mul_eq_zero.mp h1).resolve_left hc
    rw [hv, mul_zero] at h2
    exact_mod_cast h2.symm
  obtain ⟨m, hm, D, hD, hDc⟩ := hDs.exists_pos
  haveI := hDc.isInvertibleModule_divisorialSheaf
  have hdeg : ∀ C' : ProperCurve sX, OneCycle.numericalClass sX (C'.cycle ℝ) ∈ R →
      C'.degree k D.divisorialSheaf = 0 := by
    intro C' hC'
    rw [ProperCurve.degree_divisorialSheaf C' D hDc]
    have h := QDivisor.intersectionNumber_eq_of_toQDivisor_eq_smul k sX C'.ι C'.dim_le
      (Divisor.degreeOn_add k sX C'.ι C'.dim_le) Ds hDs hm D hDc hD
    rw [hDsR C' hC'] at h
    have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    exact_mod_cast (div_eq_zero_iff.mp h.symm).resolve_right hm'
  obtain ⟨LZ, hLZ, ⟨α⟩⟩ :=
    exists_isInvertible_iso_pullback_of_isContractionOfFace hklt hΔ hF hc D.divisorialSheaf hdeg
  obtain ⟨M, hMc, ⟨β⟩⟩ := exists_isCartier_divisorialSheaf_iso LZ
  have hMB := MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant g M
  obtain ⟨γ⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso hMc g hMB
  obtain ⟨φ, hφ⟩ : D.LinearlyEquivalent (M.pullback hMc hMB) :=
    MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso
      (α ≪≫ (Scheme.Modules.pullback g).mapIso β.symm ≪≫ γ.symm)
  obtain ⟨ψ, hψ, rfl⟩ := MMP.Fourfold.exists_pullbackRationalFunction_eq hbir φ
  have hpush :
      RationalMap.transformDivisor (X := X) g.toRationalMap D = M + principalDivisor ψ := by
    rw [show D = M.pullback hMc hMB + principalDivisor (pullbackRationalFunction g ψ hψ) by
        rw [← hφ]; abel, map_add,
      MMP.Positivity.transformDivisor_of_isPullback_divisor hZn hXn hbir hMc
        (Divisor.isPullback_pullback hMc hMB),
      MMP.Positivity.transformDivisor_principalDivisor_pullback hZn hXn hbir]
  have hmB : (m : ℤ) • B = M + principalDivisor ψ := by
    rw [← hpush]
    refine Finsupp.ext fun P => ?_
    rw [hιtr P, Finsupp.smul_apply, smul_eq_mul]
    have h := congrArg (fun G : QDivisor X => G (ι P)) hD
    have hE0 : (Finsupp.single E (1 : ℚ) : QDivisor X) (ι P) = 0 := by
      classical
      rw [Finsupp.single_apply, if_neg (hιE P).symm]
    simp only [Finsupp.smul_apply, hDs_def, Finsupp.add_apply] at h
    rw [hE0, smul_zero, add_zero] at h
    change ((D (ι P) : ℤ) : ℚ) = (m : ℤ) • ((B' (ι P) : ℤ) : ℚ) at h
    rw [hB', zsmul_eq_mul] at h
    exact_mod_cast h.symm
  exact ⟨m, hm, hmB ▸ hMc.add (Divisor.isCartier_principalDivisor ψ)⟩

end MMP.Mori

end
