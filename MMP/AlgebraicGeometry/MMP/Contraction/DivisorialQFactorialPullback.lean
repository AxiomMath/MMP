module

public import MMP.AlgebraicGeometry.MMP.Contraction.ExceptionalDivisorNegativeOnRay
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantDltLiftNotNef
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback

universe u

section

/-!
# Divisorial contractions with the pullback property

Let `X` be a normal `ℚ`-factorial projective variety, `R` an extremal ray of `NE̅(X)` and
`g : X ⟶ Z` a divisorial contraction of `R` with exceptional divisor `E = Ex(g)`, such that every
invertible sheaf on `X` of degree `0` on the curves of `R` is a pull-back along `g`. Then:

1. `g` is not finite (it is not an isomorphism near `E`), so it contracts a proper curve `C`;
   an ample sheaf is positive on `C`, so `[C] ≠ 0` and `R = ℝ_{≥0}[C]`.
2. `(E · C) < 0` by the negativity lemma
   (`MMP.Mori.intersectionNumber_single_neg_of_isContractionOfFace`), hence `(E · z) ≠ 0` for
   `0 ≠ z ∈ R`.
3. For a Weil divisor `B` on `Z`, take `n₁ g⁻¹_* B` and `n₂ E` Cartier, and
   `D = b · n₁ g⁻¹_* B - a · n₂ E` with `a`, `b` their degrees on `C`. Then `D` has degree `0`
   on `R`, so `𝒪_X(D) ≅ g^* L`, `D ∼ g^* M` with `M` Cartier on `Z`, and pushing forward
   (`g_* g⁻¹_* B = B`, `g_* E = 0`, `g_* g^* M = M`, `g_*` of a principal divisor is principal)
   gives `b n₁ B = M + div ψ`, Cartier, with `b < 0`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Corollary 3.18
-/

open CategoryTheory AlgebraicGeometry MMP.Mori

namespace MMP.FourfoldProofs.Km3cDivisorialContractionQfactorialOverKProof

section Helpers

variable {k : Type u} [Field k] {X Z : Scheme.{u}}

/-- A proper morphism `g` with `g_* 𝒪_X = 𝒪_Z` which contracts no proper curve is finite, hence an
isomorphism over every affine open: its exceptional set is empty. So a point of `Ex(g)` forces a
contracted proper curve. -/
private theorem exists_properCurve_isContractedBy_of_mem_exceptionalSet
    {sX : X ⟶ Spec (.of k)} [IsProper sX] [IsLocallyNoetherian X] {g : X ⟶ Z} [IsProper g]
    (hO : ∀ U : Z.Opens, IsIso (g.app U)) {x : X} (hx : x ∈ exceptionalSet g) :
    ∃ C : ProperCurve sX, C.IsContractedBy g := by
  by_contra hno
  have hlqf : LocallyQuasiFinite g := by
    by_contra h
    exact hno (exists_properCurve_isContractedBy_of_not_locallyQuasiFinite h)
  have : IsFinite g := IsFinite.of_isProper_of_locallyQuasiFinite g
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := g x) (U := ⊤) trivial
  have hbir : IsBiregular g U := (isIso_morphismRestrict_iff_isIso_app g hU).mpr (hO U)
  exact hx (le_biregularLocus hbir hxU)

/-- On a proper birational morphism `g : X ⟶ Z` onto a normal variety, `g_* g⁻¹_* B = B` for every
divisor `B` of `Z`: `g` is biregular at every point of codimension one of `Z`. -/
private theorem transformDivisor_inverseTransformDivisor [IsLocallyNoetherian X] [IsNormal X]
    {sZ : Z ⟶ Spec (.of k)} (hZ : IsNormalVariety k sZ) {g : X ⟶ Z}
    (hX : IsNormalVariety k (g ≫ sZ)) [IsProper g] (hg : IsBirationalMorphism g)
    {R : Type*} [AddCommMonoid R] (B : DivisorWithCoeffs R Z) :
    RationalMap.transformDivisor (X := X) g.toRationalMap (inverseTransformDivisor g B) = B := by
  have : IsIntegral Z := hZ.1.toIsIntegral
  have : IsNormal Z := hZ.2
  have : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : IsIntegral X := hX.1.toIsIntegral
  refine Finsupp.ext fun Q => ?_
  obtain ⟨E, hEQ, -, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hZ hX hg Q
  rw [htr]
  have hQV : g E.genericPoint ∈ biregularLocus g := by
    rw [hEQ]
    exact MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal g hg
      Q.coheight_genericPoint.le
  refine MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    (MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hEQ hQV)
    (fun Q' hQ' => ?_) B
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    ((MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
      hQ').1.symm.trans hEQ)

/-- A prime divisor inside the exceptional set of a proper birational morphism `g` onto a normal
variety is contracted to codimension at least two: `g_* (r E) = 0`. -/
private theorem transformDivisor_single_eq_zero_of_support_subset [IsReduced X]
    {sZ : Z ⟶ Spec (.of k)} (hZ : IsNormalVariety k sZ) {g : X ⟶ Z}
    (hX : IsNormalVariety k (g ≫ sZ)) [IsProper g] (hg : IsBirationalMorphism g)
    (E : MMP.Mori.PrimeDivisor X) (hE : E.support ⊆ (exceptionalSet g : Set X))
    {R : Type*} [AddCommMonoid R] (r : R) :
    RationalMap.transformDivisor (X := X) g.toRationalMap (Finsupp.single E r) = 0 := by
  have : IsIntegral Z := hZ.1.toIsIntegral
  have : IsNormal Z := hZ.2
  have : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsSeparated sZ := hZ.1.toIsSeparated
  have : IsSeparated (Z ↘ Limits.terminal Scheme) := by
    rw [show (Z ↘ Limits.terminal Scheme) = sZ ≫ (Spec (.of k) ↘ Limits.terminal Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  refine RationalMap.transformDivisor_single_of_eq_none ?_ r
  rcases h : RationalMap.transformPrimeDivisor (X := X) g.toRationalMap E with _ | Q
  · rfl
  exfalso
  have hgQ := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff g E Q).mp h
  have hmem : E.genericPoint ∈ (exceptionalSet g : Set X) := hE (by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl)
  refine hmem ?_
  change g E.genericPoint ∈ biregularLocus g
  rw [hgQ]
  exact MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal g hg
    Q.coheight_genericPoint.le

/-- An invertible module on an integral, locally Noetherian, normal, quasi-compact scheme is the
divisorial sheaf `𝒪_Z(M)` of a Cartier divisor `M`: a local frame of it has Cartier divisor. -/
private theorem exists_isCartier_divisorialSheaf_iso_of_isInvertible [IsIntegral Z]
    [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z] (L : Z.Modules)
    [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 L] :
    ∃ M : Divisor Z, M.IsCartier ∧ Nonempty (M.divisorialSheaf ≅ L) := by
  have := Stacks.SheafOfModules.isInvertible_of_tensorInvertible (X := Z.toRingedSpace) L
  have : ∀ z : Z.toRingedSpace.carrier,
      IsLocalRing (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Z.toRingedSpace z) :=
    Z.isLocalRing
  choose W hW a ha using fun z : Z =>
    Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible (X := Z.toRingedSpace) L z
  obtain ⟨z₀⟩ : Nonempty Z := inferInstance
  let F : MMP.Mori.LocalFrame L :=
    { W := W, mem := hW, a := a, isLocalGenerator := ha, base := z₀ }
  exact ⟨F.divisor, fun z => ⟨F.W z, F.mem z, _, F.isLocalEquation_divisor z⟩,
    ⟨(@asIso _ _ _ _ F.toDivisorialSheaf F.isIso_toDivisorialSheaf).symm⟩⟩

/-- **Descent of a pulled-back divisorial sheaf.** Let `g : X ⟶ Z` be a proper birational morphism
of normal varieties and `D` a Cartier divisor on `X` with `𝒪_X(D) ≅ g^* L` for an invertible
`L` on `Z`. Then `g_* D = M + div(ψ)` for a Cartier divisor `M` on `Z` (with `𝒪_Z(M) ≅ L`) and a
rational function `ψ`: `D ∼ g^* M`, and `g_*` carries `g^* M` to `M` and principal divisors to
principal divisors. -/
private theorem exists_transformDivisor_eq_add_principalDivisor [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral Z] [IsLocallyNoetherian Z]
    [IsNormal Z] [CompactSpace Z] {sZ : Z ⟶ Spec (.of k)} (hZ : IsNormalVariety k sZ)
    {g : X ⟶ Z} (hX : IsNormalVariety k (g ≫ sZ)) [IsProper g] (hg : IsBirationalMorphism g)
    {D : Divisor X} (L : Z.Modules) [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 L]
    (e : D.divisorialSheaf ≅ (Scheme.Modules.pullback g).obj L) :
    ∃ (M : Divisor Z) (ψ : (RationalFunctions Z)ˣ), M.IsCartier ∧
      RationalMap.transformDivisor (X := X) g.toRationalMap D = M + principalDivisor ψ := by
  have : IsDominant g := hg.isDominant
  obtain ⟨M, hM, ⟨eM⟩⟩ := exists_isCartier_divisorialSheaf_iso_of_isInvertible L
  have hB : ∀ W : irreducibleComponents X, g (componentGenericPoint X W) ∉ M.supp :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' g M
  obtain ⟨eP⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso hM g hB
  obtain ⟨φ, hφ⟩ := MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso
    (e ≪≫ (Scheme.Modules.pullback g).mapIso eM.symm ≪≫ eP.symm)
  obtain ⟨ψ, hψ, rfl⟩ := MMP.Fourfold.exists_pullbackRationalFunction_eq hg φ
  refine ⟨M, ψ, hM, ?_⟩
  have h1 := MMP.Positivity.transformDivisor_principalDivisor_pullback hZ hX hg ψ hψ
  have h2 := MMP.Positivity.transformDivisor_of_isPullback_divisor hZ hX hg hM
    (Divisor.isPullback_pullback hM hB)
  rw [← h1, ← hφ, map_sub, h2, add_sub_cancel]

/-- The degree of an invertible sheaf along a proper curve only depends on the class of the curve
in `N₁(X)`, linearly. -/
private theorem degree_eq_mul_of_smul_numericalClass {sX : X ⟶ Spec (.of k)} (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] {C C' : ProperCurve sX} {c : ℝ}
    (h : c • OneCycle.numericalClass sX (C.cycle ℝ) = OneCycle.numericalClass sX (C'.cycle ℝ)) :
    (C'.degree k L : ℝ) = c * C.degree k L := by
  rw [← OneCycle.degree_cycle ℝ L C', ← NumericalCurveClasses.degree_numericalClass, ← h,
    map_smul, NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle, smul_eq_mul]

end Helpers

/-- A ray `ℝ_{≥0} v` containing a nonzero vector `v₀` is the ray `ℝ_{≥0} v₀`. -/
theorem setOf_smul_eq_of_smul_eq {V : Type*} [AddCommGroup V] [Module ℝ V] {v v₀ : V} {c₀ : ℝ}
    (hc₀ : 0 ≤ c₀) (hv₀ : v₀ ≠ 0) (h : c₀ • v = v₀) :
    {w | ∃ c : ℝ, 0 ≤ c ∧ c • v = w} = {w | ∃ c : ℝ, 0 ≤ c ∧ c • v₀ = w} := by
  have hc : 0 < c₀ := hc₀.lt_of_ne <| by
    rintro rfl
    rw [zero_smul] at h
    exact hv₀ h.symm
  ext w
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨d / c₀, div_nonneg hd hc₀, by rw [← h, smul_smul, div_mul_cancel₀ _ hc.ne']⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨d * c₀, mul_nonneg hd hc₀, by rw [← h, smul_smul]⟩

/-- A proper curve on a projective variety has nonzero numerical class: an ample sheaf has positive
degree on it. -/
theorem numericalClass_cycle_ne_zero {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [AlgebraicGeometry.IsProjectiveVariety k sX] (C : ProperCurve sX) :
    OneCycle.numericalClass sX (C.cycle ℝ) ≠ 0 := by
  have : IsProper sX := (instIsProperVarietyOfIsProjectiveVariety k sX).toIsProper
  obtain ⟨L, hL, hLa⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety
    (t := sX) inferInstance
  have : Stacks.Ample.IsInvertibleModule X L := hL
  have hpos := MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy sX L
    (MMP.Threefold.Resolution.isRelativelyAmple_of_isAmple sX L
      ((Stacks.AmpleBridge.isAmple_iff_isAmple X L).mpr hLa)) C
    (fun _ _ => Subsingleton.elim _ _)
  intro h0
  have h := OneCycle.mem_numericallyTrivial.mp ((Submodule.Quotient.mk_eq_zero _).mp h0) L
  rw [OneCycle.degree_cycle] at h
  have : (0 : ℝ) < (degreeOn k sX C.ι C.dim_le L : ℝ) := by exact_mod_cast hpos
  exact this.ne' h

/-- Let `g : X ⟶ Z` be a divisorial contraction of an extremal ray `R` of a normal `ℚ`-factorial
projective variety `X`, with exceptional set the prime divisor `E`, such that every invertible
sheaf on `X` of degree `0` on every curve with class in `R` is a pullback along `g`. If
`R = ℝ_{≥0}[C]` for a proper curve `C` contracted by `g`, then `Z` is `ℚ`-factorial. -/
theorem isQFactorial_of_forall_degree_eq_zero_pullback {k : Type} [Field k] {X : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsProper sX]
    [AlgebraicGeometry.IsProjectiveVariety k sX] (hQ : MMP.Fourfold.IsQFactorial sX)
    {R : Set (NumericalCurveClasses sX)} {Z : Scheme.{0}} [IsIntegral Z] [IsLocallyNoetherian Z]
    [IsNormal Z] [CompactSpace Z] {sZ : Z ⟶ Spec (.of k)} [IsSeparated sZ] [QuasiCompact sZ]
    {g : X ⟶ Z} [IsProper g] (hg : IsDivisorialContraction k sX sZ R g)
    {E : MMP.Mori.PrimeDivisor X} (hE : (exceptionalSet g : Set X) = E.support)
    (hpb : ∀ (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L],
      (∀ C' : ProperCurve sX, OneCycle.numericalClass sX (C'.cycle ℝ) ∈ R → C'.degree k L = 0) →
      ∃ LZ : Z.Modules, SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 LZ ∧
        Nonempty (L ≅ (Scheme.Modules.pullback g).obj LZ))
    (hZn : IsNormalVariety k sZ) (hXg : IsNormalVariety k (g ≫ sZ)) {C : ProperCurve sX}
    (hCg : C.IsContractedBy g)
    (hray : R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass sX (C.cycle ℝ) = w}) :
    MMP.Fourfold.IsQFactorial sZ := by
  refine ⟨hZn, fun B => ?_⟩
  obtain ⟨n₁, hn₁, hF⟩ := hQ.2 (inverseTransformDivisor g B)
  obtain ⟨n₂, hn₂, hG⟩ := hQ.2 (Finsupp.single E 1)
  set F : Divisor X := (n₁ : ℤ) • inverseTransformDivisor g B with hFdef
  set G : Divisor X := (n₂ : ℤ) • Finsupp.single E 1 with hGdef
  set a := F.degreeOn k sX C.ι C.dim_le hF
  set b := G.degreeOn k sX C.ι C.dim_le hG
  have hb : b < 0 := by
    have hneg := intersectionNumber_single_neg_of_isContractionOfFace hQ hg.isExtremalRay
      hg.isContractionOfFace hg.isBirationalMorphism E hE.ge C hCg
    rw [QDivisor.intersectionNumber_eq_of_smul k sX C.ι C.dim_le _ _ hn₂ G hG (by
      refine Finsupp.ext fun P => ?_
      change ((G P : ℤ) : ℚ) = _
      simp only [G, Finsupp.smul_apply, smul_eq_mul]
      by_cases h : E = P <;> simp [Finsupp.single_apply, h])] at hneg
    have hb' : (b : ℚ) < 0 := by
      by_contra h
      exact absurd hneg (not_lt.mpr (div_nonneg (not_lt.mp h) (Nat.cast_nonneg _)))
    exact_mod_cast hb'
  set D : Divisor X := b • F + (-a) • G with hDdef
  have hD : D.IsCartier := (hF.zsmul b).add (hG.zsmul (-a))
  have hDC : D.degreeOn k sX C.ι C.dim_le hD = 0 := by
    rw [Divisor.degreeOn_add k sX C.ι C.dim_le _ _ (hF.zsmul b) (hG.zsmul (-a)),
      Divisor.degreeOn_zsmul' k sX C.ι C.dim_le F hF b,
      Divisor.degreeOn_zsmul' k sX C.ι C.dim_le G hG (-a)]
    ring
  have := hD.isInvertibleModule_divisorialSheaf
  obtain ⟨LZ, hLZ, ⟨e⟩⟩ := hpb D.divisorialSheaf fun C' hC' => by
    rw [hray] at hC'
    obtain ⟨c, -, hc⟩ := hC'
    have h := degree_eq_mul_of_smul_numericalClass D.divisorialSheaf hc
    rw [ProperCurve.degree_divisorialSheaf C D hD, hDC] at h
    have h0 : ((C'.degree k D.divisorialSheaf : ℤ) : ℝ) = 0 := by
      rw [h]
      simp
    exact_mod_cast h0
  obtain ⟨M, ψ, hM, hMψ⟩ := exists_transformDivisor_eq_add_principalDivisor hZn hXg
    hg.isBirationalMorphism LZ e
  have hpush : RationalMap.transformDivisor (X := X) g.toRationalMap D = (b * n₁) • B := by
    rw [hDdef, hFdef, hGdef, map_add, map_zsmul, map_zsmul, map_zsmul, map_zsmul,
      transformDivisor_inverseTransformDivisor hZn hXg hg.isBirationalMorphism,
      transformDivisor_single_eq_zero_of_support_subset hZn hXg hg.isBirationalMorphism E hE.ge,
      smul_zero, smul_zero, add_zero, smul_smul]
  have hBc : ((b * n₁) • B).IsCartier := by
    rw [← hpush, hMψ]
    exact hM.add (Divisor.isCartier_principalDivisor ψ)
  have hbn : b * n₁ < 0 := mul_neg_of_neg_of_pos hb (by exact_mod_cast hn₁)
  refine ⟨(-(b * n₁)).toNat, by omega, ?_⟩
  rw [Int.toNat_of_nonneg (by omega), neg_smul]
  exact hBc.neg

end MMP.FourfoldProofs.Km3cDivisorialContractionQfactorialOverKProof

end

section

/-!
# Divisorial contractions with the pullback property

Let `X` be a normal `ℚ`-factorial projective variety over an algebraically closed field `k` of
characteristic zero, `R` an extremal ray of the closed cone of curves `NE̅(X)`, and
`g : X ⟶ Z` a divisorial contraction of `R` with exceptional divisor `E = Ex(g)`. Suppose
`(R, g)` has the *pullback property*: every invertible sheaf on `X` of degree `0` on every
curve with class in `R` is isomorphic to the pullback along `g` of an invertible sheaf on `Z`.
Then

1. `R = ℝ_{≥0}[C]` for an irreducible curve `C` contracted by `g`;
2. `E` is `ℚ`-Cartier and `(E · z) ≠ 0` for every `0 ≠ z ∈ R`;
3. `Z` is `ℚ`-factorial.

No singularity hypothesis on `X` and no negativity of `R` is assumed: the pullback property
takes the place of the descent theorem for line bundles used in
`MMP.Mori.curveForm_single_ne_zero_of_isDivisorialContraction` and
`MMP.Mori.isQFactorial_of_isDivisorialContraction`.

## Main results

* `exists_properCurve_and_curveForm_single_ne_zero_and_isQFactorial_of_isDivisorialContraction`:
  the statement above.

## Implementation notes

An irreducible curve is a `MMP.Mori.ProperCurve`, its class is
`OneCycle.numericalClass sX (C.cycle ℝ)`, and "contracted by `g`" is
`MMP.Mori.ProperCurve.IsContractedBy`. The exceptional divisor is a prime divisor `E` with
`Ex(g) = Supp E`; its intersection with classes is `MMP.Fourfold.QDivisor.curveForm` of
`E` with coefficient one, which needs a `ℚ`-Cartier witness, so part (2) also asserts that `E`
is `ℚ`-Cartier. `MMP.Fourfold.IsQFactorial` is stated for a locally noetherian normal scheme,
so `Z` carries the instance arguments `[IsLocallyNoetherian Z] [IsNormal Z]`; both hold for
every divisorial contraction (`Z` is a projective variety, normal since `g_* 𝒪_X = 𝒪_Z`).

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Corollary 3.18
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

open MMP.FourfoldProofs.Km3cDivisorialContractionQfactorialOverKProof in
/-- **Divisorial contractions with the pullback property** (Kollár–Mori, Corollary 3.18). Let
`X` be a normal `ℚ`-factorial projective variety over an algebraically closed field `k` of
characteristic zero and `g : X ⟶ Z` a divisorial contraction of the extremal ray `R` of `NE̅(X)`
whose exceptional set is the prime divisor `E`, such that every invertible sheaf on `X` of
degree `0` on every curve with class in `R` is the pullback along `g` of an invertible sheaf on
`Z`. Then `R = ℝ_{≥0}[C]` for a curve `C` contracted by `g`, `E` is `ℚ`-Cartier with
`(E · z) ≠ 0` for every `0 ≠ z ∈ R`, and `Z` is `ℚ`-factorial. -/
@[mmp "lem_km3c_divisorial_contraction_qfactorial_over_k"]
public theorem
    exists_properCurve_and_curveForm_single_ne_zero_and_isQFactorial_of_isDivisorialContraction
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX] [AlgebraicGeometry.IsProjectiveVariety k sX]
    (hQ : MMP.Fourfold.IsQFactorial sX) {R : Set (NumericalCurveClasses sX)}
    {Z : Scheme.{0}} [IsLocallyNoetherian Z] [IsNormal Z] {sZ : Z ⟶ Spec (.of k)} {g : X ⟶ Z}
    (hg : IsDivisorialContraction k sX sZ R g) {E : PrimeDivisor X}
    (hE : (exceptionalSet g : Set X) = E.support)
    (hpb : ∀ (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L],
      (∀ C' : ProperCurve sX, OneCycle.numericalClass sX (C'.cycle ℝ) ∈ R → C'.degree k L = 0) →
      ∃ LZ : Z.Modules, SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 LZ ∧
        Nonempty (L ≅ (Scheme.Modules.pullback g).obj LZ)) :
    (∃ C : ProperCurve sX, C.IsContractedBy g ∧
      R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass sX (C.cycle ℝ) = w}) ∧
    (∃ h : QDivisor.IsQCartier (Finsupp.single E 1 : QDivisor X), ∀ z ∈ R, z ≠ 0 →
      MMP.Fourfold.QDivisor.curveForm sX (Finsupp.single E 1) h z ≠ 0) ∧
    MMP.Fourfold.IsQFactorial sZ := by
  have hC := hg.isContractionOfFace
  have hXv : IsNormalVariety k sX := hg.isNormalVariety
  obtain ⟨hZv, hZproj⟩ := (MMP.Mori.isProjectiveVariety_iff k sZ).mp hC.isProjectiveVariety_target
  have : IsIntegral Z := hZv.toIsIntegral
  have : IsSeparated sZ := hZv.toIsSeparated
  have : QuasiCompact sZ := hZv.toQuasiCompact
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  have : IsProper sX := (instIsProperVarietyOfIsProjectiveVariety k sX).toIsProper
  have : IsProper (g ≫ sZ) := by rw [hC.comp_eq]; infer_instance
  have : IsProper g := IsProper.of_comp g sZ
  obtain ⟨x, hx⟩ : E.support.Nonempty := ⟨E.genericPoint, by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl⟩
  obtain ⟨C, hCg⟩ := exists_properCurve_isContractedBy_of_mem_exceptionalSet (sX := sX)
    hC.isIso_app (x := x) (hE.ge hx)
  have hray : R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass sX (C.cycle ℝ) = w} := by
    obtain ⟨-, v, -, hRv⟩ := hg.isExtremalRay
    have hCR := (hC.isContractedBy_iff C).mp hCg
    rw [hRv] at hCR ⊢
    obtain ⟨c₀, hc₀, hc₀v⟩ := hCR
    exact setOf_smul_eq_of_smul_eq hc₀ (numericalClass_cycle_ne_zero C) hc₀v
  refine ⟨⟨C, hCg, hray⟩, ?_,
    isQFactorial_of_forall_degree_eq_zero_pullback hQ hg hE hpb ⟨hZv, ‹IsNormal Z›⟩
      (by rw [hC.comp_eq]; exact hXv) hCg hray⟩
  have hneg := intersectionNumber_single_neg_of_isContractionOfFace hQ hg.isExtremalRay hC
    hg.isBirationalMorphism E hE.ge C hCg
  refine ⟨MMP.Fourfold.isQCartier_of_isQFactorial sX hQ _, fun z hz hz0 => ?_⟩
  rw [hray] at hz
  obtain ⟨c, -, rfl⟩ := hz
  have hc : c ≠ 0 := by rintro rfl; exact hz0 (zero_smul _ _)
  rw [map_smul, smul_eq_mul, MMP.ProgramBaseChange.curveForm_numericalClass_cycle]
  exact mul_ne_zero hc (by exact_mod_cast hneg.ne)

end MMP.Mori

end
