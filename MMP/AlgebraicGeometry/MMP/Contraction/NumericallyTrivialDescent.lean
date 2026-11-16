module

public import MMP.AlgebraicGeometry.MMP.Contraction.LineBundleDescent

/-!
# Relatively numerically trivial divisors descend along a klt extremal contraction

Let `(U, Γ)` be a projective klt pair with a `ℚ`-boundary and canonical divisor `K`, let `R` be a
`(K + Γ)`-negative extremal ray of `NE̅(U)` and let `f : U ⟶ V` be the contraction of `R` onto a
normal projective variety. A `ℚ`-Cartier `ℚ`-divisor `L` on `U` of degree zero on every curve
contracted by `f` is `ℚ`-linearly equivalent to the pull-back `f^* M` of a `ℚ`-Cartier
`ℚ`-divisor `M` on `V`. This is the contraction theorem's description of `Pic(V)` inside
`Pic(U)`, after clearing denominators.

## Main results

* `MMP.Fourfold.IsKltPair.exists_qLinearlyEquivalent_pullback_of_isContractionOfRay`.

## Implementation notes

The source works over `ℂ`; the statement is made over any field `k`, the klt condition
`MMP.Fourfold.IsKltPair` already forcing `k` to be algebraically closed of characteristic zero.
Numerical triviality over `V` is stated with the curve form `MMP.Fourfold.QDivisor.curveForm`:
`(L · C) = 0` for every integral curve `C ⊆ U` proper over `k` and contracted by `f`. The
pull-back is `MMP.Mori.QDivisor.pullback`, whose side condition (the generic point of `U` maps
outside `Supp M`) is automatic for the surjective `f` and is packaged existentially with the
`ℚ`-linear equivalence.

## References

* [KM98] J. Kollár, S. Mori, *Birational geometry of algebraic varieties*, Thm. 3.7 (4).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

/-- On an integral, locally Noetherian, normal, quasi-compact scheme every invertible module is
isomorphic to `𝒪(D)` for a Cartier divisor `D`. -/
private theorem exists_isCartier_divisorialSheaf_iso {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L] :
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

/-- **Relatively numerically trivial divisors descend along a klt extremal contraction.** Let
`(U, Γ)` be a projective klt pair, `K` a canonical divisor of `U`, `R` a `(K + Γ)`-negative
extremal ray of `NE̅(U)` and `f : U ⟶ V` its contraction, with `V` projective. If `L` is a
`ℚ`-Cartier `ℚ`-divisor on `U` with `(L · C) = 0` for every curve `C` contracted by `f`, then
`L ∼_ℚ f^* M` for a `ℚ`-Cartier `ℚ`-divisor `M` on `V`. -/
@[mmp "lem_fourfold_relatively_trivial_descends"]
public theorem IsKltPair.exists_qLinearlyEquivalent_pullback_of_isContractionOfRay
    {k : Type} [Field k] {U V : Scheme.{0}} {sU : U ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)}
    [IsIntegral U] [CompactSpace U] [IsLocallyNoetherian U] [IsNormal U]
    [IsLocallyNoetherian V] [IsNormal V]
    {K : Divisor U} {Γ : QDivisor U} {R : Set (NumericalCurveClasses sU)} {f : U ⟶ V}
    (hΓ : IsKltPair sU Γ) (hUp : MMP.Mori.IsProjectiveVariety k sU)
    (hK : ∃ n : ℕ, K.IsCanonicalDivisor sU n)
    (hR : IsNegativeExtremalRayOf sU (Divisor.toQDivisor K + Γ) R)
    (hf : IsContractionOfRay sU sV R f) (hVp : MMP.Mori.IsProjectiveVariety k sV)
    {L : QDivisor U}
    (hL : ∃ h : L.IsQCartier, ∀ C : ProperCurve sU, C.IsContractedBy f →
      QDivisor.curveForm sU L h (OneCycle.numericalClass sU (C.cycle ℝ)) = 0) :
    ∃ (M : QDivisor V) (hM : M.IsQCartier)
      (hMf : ∀ Z : irreducibleComponents U, f (componentGenericPoint U Z) ∉ M.supp),
      L.QLinearlyEquivalent (M.pullback hM hMf) := by
  obtain ⟨n, hKn⟩ := hK
  obtain ⟨hLq, hL0⟩ := hL
  haveI : IsIntegral V := hVp.toIsIntegral
  haveI : IsAlgClosed k := hΓ.1.isAlgClosed
  haveI : CharZero k := hΓ.1.charZero
  have hklt : MMP.Mori.IsKltPair sU n K Γ :=
    (MMP.Fourfold.isKltPair_iff_mori_isKltPair sU hKn hΓ.1).mp hΓ
  set m := L.cartierIndex hLq
  have hm : 0 < m := MMP.Mori.QDivisor.cartierIndex_pos hLq
  obtain ⟨D₀, hD₀, hD₀c⟩ := MMP.Mori.QDivisor.isCartierDivisor_cartierIndex_smul hLq
  haveI : AlgebraicGeometry.IsProjectiveVariety k sU := hUp
  haveI := hD₀c.isInvertibleModule_divisorialSheaf
  have hdeg : ∀ C : ProperCurve sU, OneCycle.numericalClass sU (C.cycle ℝ) ∈ R →
      C.degree k D₀.divisorialSheaf = 0 := by
    intro C hC
    have h0 := hL0 C ((hf.isContractedBy_iff C).mpr hC)
    rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
      QDivisor.intersectionNumber_eq_of_toQDivisor_eq k sU C.ι C.dim_le L hLq D₀ hD₀c hD₀] at h0
    rw [ProperCurve.degree_divisorialSheaf C D₀ hD₀c]
    have : ((D₀.degreeOn k sU C.ι C.dim_le hD₀c : ℚ) : ℝ) = 0 := by
      push_cast at h0 ⊢
      exact (div_eq_zero_iff.mp h0).resolve_right (by exact_mod_cast hm.ne')
    exact_mod_cast this
  obtain ⟨_, hext, hneg⟩ := hR
  have hg : IsContractionOfFace k sU sV R f :=
    ⟨hUp, hVp, hf.comp_eq, hext.1, hf.isContractedBy_iff, hf.isIso_app⟩
  obtain ⟨LZ, hLZ, ⟨e⟩⟩ := exists_isInvertible_iso_pullback_of_isContractionOfFace hklt hΓ.1.nonneg
    ⟨hext.1, hext.1.2.2.1, hneg⟩ hg D₀.divisorialSheaf hdeg
  haveI : AlgebraicGeometry.IsProjectiveVariety k sV := hVp
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  obtain ⟨D, hDc, ⟨eD⟩⟩ := exists_isCartier_divisorialSheaf_iso LZ
  haveI : Surjective f := ⟨hf.surjective⟩
  have hB : ∀ Z : irreducibleComponents U, f (componentGenericPoint U Z) ∉ D.supp :=
    MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant f D
  obtain ⟨eP⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso hDc f hB
  obtain ⟨φ, hφ⟩ := MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso
    (e ≪≫ (Scheme.Modules.pullback f).mapIso eD.symm ≪≫ eP.symm)
  set M : QDivisor V := (m : ℚ)⁻¹ • Divisor.toQDivisor D
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hMD : Divisor.toQDivisor D = (m : ℤ) • M := by
    rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul]
    simp [hmq]
  have hMq : M.IsQCartier := ⟨m, by exact_mod_cast hm.ne', D, hMD, hDc⟩
  have hMf : ∀ Z : irreducibleComponents U, f (componentGenericPoint U Z) ∉ M.supp := by
    rw [← QDivisor.supp_eq_of_toQDivisor_eq (by exact_mod_cast hm.ne') hMD]
    exact hB
  obtain ⟨D', hD', hpb⟩ := QDivisor.isPullback_pullback hMq hMf m hm D hMD hDc
  refine ⟨M, hMq, hMf, m, hm, φ, ?_⟩
  rw [smul_sub, ← hD₀, ← hD', ← hpb.pullback_eq hDc, ← map_sub, hφ]

end MMP.Fourfold

end
