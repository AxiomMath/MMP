module

public import MMP.AlgebraicGeometry.MMP.Contraction.LineBundleDescent

/-!
# The exceptional divisor of a divisorial contraction is nonzero on the ray

Let `X` be a `ℚ`-factorial projective variety over an algebraically closed field `k` of
characteristic zero, `(X, Δ)` a klt pair with `Δ` effective, `R` an extremal ray of `NE̅(X)` on
which `K_X + Δ` is negative away from `0`, and `g : X ⟶ Z` a divisorial contraction of `R` with
exceptional divisor `E = Ex(g)`. Then `E` is `ℚ`-Cartier and `(E · z) ≠ 0` for every
`0 ≠ z ∈ R`.

Since `X` is `ℚ`-factorial, `D = mE` is Cartier for some `m > 0`. If `(E · z) = 0` for some
`0 ≠ z ∈ R`, then `(E · z)` vanishes on all of the ray `R`, so `deg_C 𝒪_X(D) = 0` for every curve
`C` with `[C] ∈ R`, and `𝒪_X(D) ≅ g^* 𝓛` for an invertible sheaf `𝓛 ≅ 𝒪_Z(M)` on `Z`, `M`
Cartier. Hence `D ∼ g^* M`, that is `D = g^*(M + div ψ)` for a rational function `ψ` on `Z`.
Pushing forward, `M + div ψ = g_* D = 0`, because `E` is contracted by `g` to a subset of
codimension at least two. So `D = g^* 0 = 0`, a contradiction.

## Main results

* `MMP.Mori.curveForm_single_ne_zero_of_isDivisorialContraction`: the statement above.

## Implementation notes

The exceptional divisor is the prime divisor `E` whose support is `exceptionalSet g`, viewed as
the `ℚ`-divisor `Finsupp.single E 1`; the pairing `(E · z)` is
`MMP.Fourfold.QDivisor.curveForm`, which needs a `ℚ`-Cartier witness, and this witness is part
of the conclusion (it comes from `ℚ`-factoriality).

The source shows `𝓛 ≅ 𝒪_Z` through `𝓛 ≅ g_* g^* 𝓛 ≅ g_* 𝒪_X(mE) = 𝒪_Z`; here the same
conclusion is reached on divisors: the push-forward `g_*` of divisors inverts the pull-back of
Cartier divisors along the birational morphism `g` and kills the exceptional divisor `E`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Corollary 3.18
-/

namespace MMP.Mori.DivisorialExceptionalOnRay

open CategoryTheory AlgebraicGeometry MMP.Mori

section Helpers

variable {k : Type} [Field k]

/-- A prime divisor `E` whose support is the exceptional set of a proper birational morphism
`f : X ⟶ Y` to a normal variety maps to no prime divisor of `Y`: the image of the generic point
of `E` is not the generic point of any prime divisor of `Y`. -/
private theorem map_genericPoint_ne_of_support_eq_exceptionalSet {X Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) (hY : MMP.Mori.IsVariety k sY) [IsNormal Y] (f : X ⟶ Y)
    (hX : MMP.Mori.IsVariety k (f ≫ sY)) [IsProper f] (hf : IsBirationalMorphism f)
    {E : MMP.Mori.PrimeDivisor X} (hE : (exceptionalSet f : Set X) = E.support)
    (P : MMP.Mori.PrimeDivisor Y) : f E.genericPoint ≠ P.genericPoint := by
  intro hP
  have hmem : P.genericPoint ∈ ((biregularLocus f).compl : Set Y) := by
    rw [← hP]
    change E.genericPoint ∈ (exceptionalSet f : Set X)
    rw [hE, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have hcod := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp
    (MMP.Mori.two_le_closedsCodimension_compl_biregularLocus sY f (hY := hY) (hX := hX) hf) _ hmem
  rw [P.coheight_genericPoint] at hcod
  exact absurd hcod (by decide)

/-- **Invertible sheaves are divisorial, with a Cartier divisor.** On an integral, locally
Noetherian, normal, quasi-compact scheme `Y`, every invertible `𝒪_Y`-module is `𝒪_Y(D)` for a
Cartier divisor `D`. -/
private theorem exists_isCartier_divisorialSheaf_iso {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (L : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L] :
    ∃ D : Divisor Y, D.IsCartier ∧ Nonempty (D.divisorialSheaf ≅ L) := by
  have := Stacks.SheafOfModules.isInvertible_of_tensorInvertible (X := Y.toRingedSpace) L
  have : ∀ z : Y.toRingedSpace.carrier,
      IsLocalRing (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Y.toRingedSpace z) :=
    fun z => Y.isLocalRing z
  choose W hW a ha using fun y : Y =>
    Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible (X := Y.toRingedSpace) L y
  obtain ⟨y₀⟩ : Nonempty Y := inferInstance
  let F : LocalFrame L :=
    { W := W, mem := hW, a := a, isLocalGenerator := fun y V hV => ha y V hV, base := y₀ }
  have := F.isIso_toDivisorialSheaf
  exact ⟨F.divisor, fun y => ⟨F.W y, F.mem y, _, F.isLocalEquation_divisor y⟩,
    ⟨(asIso F.toDivisorialSheaf).symm⟩⟩

end Helpers

end MMP.Mori.DivisorialExceptionalOnRay

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

/-- **The exceptional divisor is nonzero on the contracted ray** (Kollár–Mori, proof of 3.18).
Let `X` be a `ℚ`-factorial projective variety over an algebraically closed field `k` of
characteristic zero, `(X, Δ)` a klt pair with canonical divisor `K` and `Δ` effective, `R` a
subset of `N₁(X)` with `(K + Δ) · z < 0` for `0 ≠ z ∈ R`, and `g : X ⟶ Z` a divisorial
contraction of the extremal ray `R` whose exceptional set is the prime divisor `E`. Then `E` is
`ℚ`-Cartier and `(E · z) ≠ 0` for every `0 ≠ z ∈ R`. -/
@[mmp "lem_km3b_divisorial_exceptional_nonzero_on_ray"]
public theorem curveForm_single_ne_zero_of_isDivisorialContraction {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [AlgebraicGeometry.IsProjectiveVariety k sX] (hQ : MMP.Fourfold.IsQFactorial sX)
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hklt : IsKltPair sX n K Δ) (hΔ : Δ.IsEffective) {R : Set (NumericalCurveClasses sX)}
    (hR : ∀ z ∈ R, z ≠ 0 →
      MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2 z < 0)
    {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of k)} {g : X ⟶ Z}
    (hg : IsDivisorialContraction k sX sZ R g) {E : PrimeDivisor X}
    (hE : (exceptionalSet g : Set X) = E.support) :
    ∃ h : QDivisor.IsQCartier (Finsupp.single E 1 : QDivisor X), ∀ z ∈ R, z ≠ 0 →
      MMP.Fourfold.QDivisor.curveForm sX (Finsupp.single E 1) h z ≠ 0 := by
  have hEq : QDivisor.IsQCartier (Finsupp.single E 1 : QDivisor X) :=
    MMP.Fourfold.isQCartier_of_isQFactorial sX hQ _
  refine ⟨hEq, fun z hzR hz0 hEz => ?_⟩
  have hc := hg.isContractionOfFace
  have hbir := hg.isBirationalMorphism
  obtain ⟨hXv, hXproj⟩ := (MMP.Mori.isProjectiveVariety_iff k sX).mp hc.isProjectiveVariety_source
  obtain ⟨hZv, hZproj⟩ := (MMP.Mori.isProjectiveVariety_iff k sZ).mp
    hc.isProjectiveVariety_target
  have hXv' : MMP.Mori.IsVariety k (g ≫ sZ) := hc.comp_eq ▸ hXv
  have : IsIntegral Z := hZv.toIsIntegral
  have : IsProper sZ := isProper_of_isProjectiveMorphism sZ hZproj
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  have : IsProper (g ≫ sZ) := by
    rw [hc.comp_eq]
    exact isProper_of_isProjectiveMorphism sX hXproj
  have : IsProper g := IsProper.of_comp g sZ
  have : IsDominant g := hbir.isDominant
  -- `Z` is normal: the target of a contraction from a normal variety
  have : LocallyOfFiniteType sZ := hZv.toLocallyOfFiniteType
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : IsIso g.c := by
    have : ∀ U, IsIso (g.c.app U) := fun U => hc.isIso_app U.unop
    exact NatIso.isIso_of_isIso_app _
  have : IsNormal Z := isNormal_of_isIso_c sZ g hZv hXv'
  have hZn : IsNormalVariety k sZ := ⟨hZv, inferInstance⟩
  have hXn : IsNormalVariety k (g ≫ sZ) := ⟨hXv', inferInstance⟩
  -- `(E · -)` vanishes on the ray `R = ℝ_{≥0} v`
  obtain ⟨v, -, hRv⟩ := hg.isExtremalRay.2
  have hEv : MMP.Fourfold.QDivisor.curveForm sX (Finsupp.single E 1) hEq v = 0 := by
    rw [hRv] at hzR
    obtain ⟨c, -, rfl⟩ := hzR
    have hc0 : c ≠ 0 := by rintro rfl; exact hz0 (zero_smul _ _)
    rw [map_smul, smul_eq_mul] at hEz
    exact (mul_eq_zero.mp hEz).resolve_left hc0
  -- a Cartier multiple `D = mE`, trivial on the curves of `R`
  obtain ⟨m, hm, D, hD, hDc⟩ := QDivisor.IsQCartier.exists_pos hEq
  haveI := hDc.isInvertibleModule_divisorialSheaf
  have hdeg : ∀ C : ProperCurve sX, OneCycle.numericalClass sX (C.cycle ℝ) ∈ R →
      C.degree k D.divisorialSheaf = 0 := by
    intro C hC
    rw [ProperCurve.degree_divisorialSheaf C D hDc]
    have h := QDivisor.intersectionNumber_eq_of_toQDivisor_eq_smul k sX C.ι C.dim_le
      (Divisor.degreeOn_add k sX C.ι C.dim_le) _ hEq hm D hDc hD
    have h0 : QDivisor.intersectionNumber k sX C.ι C.dim_le
        (Finsupp.single E 1 : QDivisor X) hEq = 0 := by
      have h2 := MMP.ProgramBaseChange.curveForm_numericalClass_cycle sX _ hEq C
      rw [hRv] at hC
      obtain ⟨c, -, hcv⟩ := hC
      rw [← hcv, map_smul, hEv, smul_zero] at h2
      exact_mod_cast h2.symm
    rw [h0] at h
    have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    exact_mod_cast (div_eq_zero_iff.mp h.symm).resolve_right hm'
  -- descent: `𝒪_X(D) ≅ g^* 𝓛`, and `𝓛 ≅ 𝒪_Z(M)` with `M` Cartier
  have hF : IsNegativeExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
      (MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2) R :=
    ⟨hg.isExtremalRay.1, hg.isExtremalRay.1.2.2.1, hR⟩
  obtain ⟨LZ, hLZ, ⟨α⟩⟩ :=
    exists_isInvertible_iso_pullback_of_isContractionOfFace hklt hΔ hF hc D.divisorialSheaf hdeg
  obtain ⟨M, hMc, ⟨β⟩⟩ :=
    DivisorialExceptionalOnRay.exists_isCartier_divisorialSheaf_iso LZ
  have hMB := MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant g M
  obtain ⟨γ⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso hMc g hMB
  obtain ⟨φ, hφ⟩ : D.LinearlyEquivalent (M.pullback hMc hMB) :=
    MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso
      (α ≪≫ (Scheme.Modules.pullback g).mapIso β.symm ≪≫ γ.symm)
  obtain ⟨ψ, hψ, rfl⟩ := MMP.Fourfold.exists_pullbackRationalFunction_eq hbir φ
  -- `D = g^*(M + div ψ)`
  have hMψc : (M + principalDivisor ψ).IsCartier := hMc.add (Divisor.isCartier_principalDivisor ψ)
  have hMψB := MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant g
    (M + principalDivisor ψ)
  have hDpb : (M + principalDivisor ψ).IsPullback g hMψB D := by
    rw [show D = M.pullback hMc hMB + principalDivisor (pullbackRationalFunction g ψ hψ) by
        rw [← hφ]; abel]
    exact Divisor.IsPullback.add hMc (Divisor.isCartier_principalDivisor ψ) hMψB
      (Divisor.isPullback_pullback hMc hMB) (Divisor.isPullback_principalDivisor ψ hψ)
  -- push forward: `M + div ψ = g_* D = 0`, since `g_* E = 0`
  have hpush := MMP.Positivity.transformDivisor_of_isPullback_divisor hZn hXn hbir hMψc hDpb
  have hzero : RationalMap.transformDivisor (X := X) g.toRationalMap D = 0 := by
    refine Finsupp.ext fun P => ?_
    obtain ⟨E', hE'g, -, htr⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hZn hXn hbir P
    rw [htr, Finsupp.coe_zero, Pi.zero_apply]
    have hne : E' ≠ E := fun h =>
      DivisorialExceptionalOnRay.map_genericPoint_ne_of_support_eq_exceptionalSet
        sZ hZv g hXv' hbir hE P (h ▸ hE'g)
    have h := congrArg (fun G : QDivisor X => G E') hD
    classical
    simp only [Finsupp.smul_apply, Finsupp.single_apply, if_neg hne.symm, smul_zero] at h
    change ((D E' : ℤ) : ℚ) = 0 at h
    exact_mod_cast h
  rw [hzero] at hpush
  -- so `D = g^* 0 = 0`, contradicting `D = mE` with `m > 0`
  have hD0 : D = 0 :=
    (hDpb.of_eq hpush.symm
      (hB₂ := MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant g 0)).eq
      Divisor.isCartier_zero (Divisor.isPullback_zero _)
  have h := DFunLike.congr_fun hD E
  rw [hD0, map_zero, Finsupp.coe_zero, Pi.zero_apply, Finsupp.smul_apply,
    Finsupp.single_eq_same, zsmul_eq_mul, mul_one] at h
  exact hm.ne' (by exact_mod_cast h.symm)

end MMP.Mori

end
