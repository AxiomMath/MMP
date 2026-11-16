module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.MMP.Fourfold.AlgClosed.FibreTypeMoriFibreSpace
public import MMP.AlgebraicGeometry.MMP.Fourfold.AlgClosed.Termination
public import MMP.AlgebraicGeometry.MMP.Fourfold.ContinuableRay
public import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
public import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
public import MMP.AlgebraicGeometry.Divisor.Canonical.TopFormGenerator
public import MMP.AlgebraicGeometry.Singularities.LocalGenerator
public import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
public import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
public import MMP.AlgebraicGeometry.Singularities.Adjunction.CartierCodimTwo

/-!
# Endpoints of maximal programs for projective lc fourfolds

Let `k` be an algebraically closed field of characteristic zero and `(X, B)` a projective lc
fourfold pair over `k` with rational boundary. Every maximal program from `(X, B)` has finitely
many birational steps, and it ends in one of two ways: either its last model `(X_n, B_n)` is a
projective lc pair with nef adjoint divisor `K_{X_n} + B_n`, or the program has a final
fibre-type ray whose contraction `g : X_n ⟶ T` is a Mori fibre space structure on `(X_n, B_n)`.

## Main results

* `MMP.Fourfold.Program.IsMaximal.isNefOnCurves_or_isMoriFibreSpace`: the endpoints of a maximal
  program.

## Implementation notes

The last stage of a program `P` with `P.n ≠ ⊤` is the model `MMP.Fourfold.modelSeq X P.Y P.n.toNat`
over `MMP.Fourfold.modelStr sX P.sY P.n.toNat`, with canonical divisor
`MMP.Fourfold.divisorSeq K P.KY P.n.toNat` and boundary `MMP.Fourfold.divisorSeq B P.BY P.n.toNat`;
the final contraction is `P.g : modelSeq X P.Y P.n.toNat ⟶ P.T`. The boundary is a `ℚ`-divisor,
so it is rational, and "fourfold" is `topologicalKrullDim X = 4`.
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold

namespace Proof_thm_main

universe u

private theorem natCast_lt_of_succ_le {n : ℕ∞} {j : ℕ} (h : ((j + 1 : ℕ) : ℕ∞) ≤ n) :
    (j : ℕ∞) < n := by
  push_cast at h
  exact (ENat.add_one_le_iff (ENat.coe_ne_top j)).mp h

section Forms

variable {k : Type u} [Field k] [PerfectField k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  [IsIntegral X] [IsIntegral Y] [LocallyOfFiniteType sX] (f : Y ⟶ X) [IsDominant f]

/-- Along a birational morphism every rational top form is a pull-back. -/
private theorem exists_pullbackRationalPluriForms_eq
    (hbij : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d)
    (ω : RationalPluriForms (f ≫ sX) d 1) :
    ∃ τ : RationalPluriForms sX d 1, pullbackRationalPluriForms sX f τ = ω := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  obtain ⟨ω', hω⟩ := exists_isPullbackGenerator_of_bijective sX f hbij hd
  obtain ⟨g, hg⟩ := hbij.2
    ((ZTensorPower.basis (basisOfSpanSingleton hω.2.1 hω.2.2) 1).repr ω ())
  refine ⟨g • ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) 1 (), ?_⟩
  change pullbackForms (K := X.functionField) (K' := Y.functionField) 1 _ = ω
  rw [pullbackForms_eq hω, pullbackFormsAlong]
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
    Finsupp.single_eq_same, smul_eq_mul, mul_one]
  change functionFieldMap f g • _ = ω
  rw [hg]
  exact basis_unit_repr_smul _ ω

omit [PerfectField k] [LocallyOfFiniteType sX] in
/-- The pull-back of the zero form is zero. -/
private theorem pullbackRationalPluriForms_zero {d : ℕ} {m : ℤ} :
    pullbackRationalPluriForms sX f (0 : RationalPluriForms sX d m) = 0 := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  change pullbackForms (K := X.functionField) (K' := Y.functionField) m 0 = 0
  simpa using pullbackForms_add (K' := Y.functionField) (m := m)
    (0 : PluriForms k X.functionField d m) 0

/-- The pull-back of a nonzero rational form along a birational morphism is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero
    (hbij : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d)
    {m : ℤ} {τ : RationalPluriForms sX d m} (hτ : τ ≠ 0) :
    pullbackRationalPluriForms sX f τ ≠ 0 := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX f hbij hd
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := (pullbackForms_eq hω m τ) ▸ h0
  have h1 : algebraMap X.functionField Y.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← repr_pullbackFormsAlong hω m τ, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

end Forms

/-- Along a proper birational `f : X⁻ ⟶ Z` and a small `f⁺ : X⁺ ⟶ Z`, the divisor of the
pull-back `(f⁺)^*τ` of a rational top form `τ` on `Z` is the strict transform `(f⁺)⁻¹_* f_* K` of
the divisor `K` of `f^*τ`: a prime divisor of `X⁺` and its counterpart on `X⁻` have the same
valuation over `Z`, and at both the stalk maps are isomorphisms. -/
private theorem divisorOfForm_pullback_eq_flipTransform {k : Type u} [Field k] [PerfectField k]
    {Xm Xp Z : Scheme.{u}} [IsIntegral Xm] [IsLocallyNoetherian Xm] [IsNormal Xm]
    [IsIntegral Xp] [IsLocallyNoetherian Xp] [IsNormal Xp] [CompactSpace Xp] [IsIntegral Z]
    [IsNormal Z] [IsLocallyNoetherian Z] {sZ : Z ⟶ Spec (.of k)} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    [LocallyOfFiniteType sZ] [LocallyOfFiniteType (fp ≫ sZ)] (hZ : IsNormalVariety k sZ)
    [IsProper fm] (hfm : IsBirationalMorphism fm) (hfp : IsSmallMorphism (fp ≫ sZ) sZ fp) {n : ℕ}
    (hdZ : (letI := functionFieldAlgebra sZ; Algebra.trdeg k Z.functionField).toNat = n)
    (τ : RationalPluriForms sZ n 1) {K : Divisor Xm}
    (hK : haveI := hfm.isDominant
      ∀ P : MMP.Mori.PrimeDivisor Xm, P.ordForm (pullbackRationalPluriForms sZ fm τ) = K.coeff P) :
    haveI := hfp.isBirationalMorphism.isDominant
    divisorOfForm (pullbackRationalPluriForms sZ fp τ) = flipTransform fm fp K := by
  have hbp := hfp.isBirationalMorphism
  haveI := hfm.isDominant
  haveI := hbp.isDominant
  ext P
  obtain ⟨Pm, Q, -, hPmQ, hPQ⟩ :=
    exists_primeDivisor_valuationOver_eq_of_isSmallMorphism hZ hfm hfp P
  have hPmQ' := map_genericPoint_eq_of_image_eq Pm Q hPmQ
  have hPQ' := map_genericPoint_eq_of_image_eq P Q hPQ
  obtain ⟨Pm', hPm', hc⟩ := exists_eq_genericPoint_flipTransform_apply
    hfm hfp P Pm.genericPoint (hPmQ'.trans hPQ'.symm)
  obtain rfl : Pm = Pm' := AlgebraicGeometry.PrimeDivisor.genericPoint_injective hPm'
  change P.ordForm _ = (flipTransform fm fp K).coeff P
  haveI := isIso_stalkMap_of_map_eq_genericPoint hbp hPQ'
  haveI := isIso_stalkMap_of_map_eq_genericPoint hfm hPmQ'
  rw [show (flipTransform fm fp K).coeff P = K.coeff Pm from hc K,
    MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso fp
      hbp.functionFieldMap_bijective hdZ P Q hPQ' τ,
    ← MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso fm
      hfm.functionFieldMap_bijective hdZ Pm Q hPmQ' τ, hK]

/-- The strict transform `(f⁺)⁻¹_* f_* K` of a canonical divisor `K` of `X⁻` along a proper
birational `f : X⁻ ⟶ Z` and a small `f⁺ : X⁺ ⟶ Z` is a canonical divisor of `X⁺`. -/
private theorem isCanonicalDivisor_flipTransform {k : Type u} [Field k] [PerfectField k]
    {Xm Xp Z : Scheme.{u}} [IsIntegral Xm] [IsLocallyNoetherian Xm] [IsNormal Xm]
    [IsIntegral Xp] [IsLocallyNoetherian Xp] [IsNormal Xp] [CompactSpace Xp]
    {sXm : Xm ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {sXp : Xp ⟶ Spec (.of k)}
    {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} (hXm : IsNormalVariety k sXm) (hcm : fm ≫ sZ = sXm)
    [IsProper fm] (hfm : IsBirationalMorphism fm) (hfp : IsSmallMorphism sXp sZ fp)
    {n : ℕ} {K : Divisor Xm} (hK : K.IsCanonicalDivisor sXm n) :
    Divisor.IsCanonicalDivisor sXp n (flipTransform fm fp K) := by
  have hZ := hfp.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have hbp := hfp.isBirationalMorphism
  haveI := hfm.isDominant
  haveI := hbp.isDominant
  have hXp := hfp.isNormalVariety_source
  haveI : MMP.Mori.IsVariety k sZ := hZ.1
  haveI : MMP.Mori.IsVariety k sXm := hXm.1
  haveI : MMP.Mori.IsVariety k sXp := hXp.1
  have hnZ : topologicalKrullDim Z = n := by
    rw [← hcm] at hK hXm
    haveI : MMP.Mori.IsVariety k (fm ≫ sZ) := hXm.1
    exact (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ (fm ≫ sZ)
      hfm).trans hK.topologicalKrullDim_eq
  have hnXp : topologicalKrullDim Xp = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ sXp hbp).symm.trans hnZ
  haveI : LocallyOfFiniteType sXp := hXp.1.toLocallyOfFiniteType
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor sXp hXp hnXp
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hXm hK
  have hdZ : (letI := functionFieldAlgebra sZ; Algebra.trdeg k Z.functionField).toNat = n :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq hnZ
  have hcp := hfp.comp_eq
  subst hcm hcp
  obtain ⟨τ, hτ⟩ := exists_pullbackRationalPluriForms_eq sZ fm hfm.functionFieldMap_bijective hdZ ω
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    exact hω0 (hτ.symm.trans (pullbackRationalPluriForms_zero sZ fm))
  have hτp0 := pullbackRationalPluriForms_ne_zero sZ fp hbp.functionFieldMap_bijective hdZ hτ0
  have hdiv := divisorOfForm_pullback_eq_flipTransform hZ hfm hfp hdZ τ (hτ ▸ hω)
  have hle := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hXp hK₀ hτp0
  rw [one_smul, hdiv] at hle
  exact hK₀.of_linearlyEquivalent hle

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {K : Divisor X} {B : QDivisor X}

/-- Every stage of a program from a projective lc fourfold pair is a projective lc fourfold pair
with canonical divisor `K_i`. -/
private theorem stage (hdim : topologicalKrullDim X = 4) (P : Program sX K B) :
    ∀ i : ℕ, (i : ℕ∞) ≤ P.n →
      MMP.Mori.IsProjectiveVariety k (modelStr sX P.sY i) ∧
      MMP.Intersection.IsLogCanonicalPair (modelStr sX P.sY i) (divisorSeq B P.BY i) ∧
      (∃ m : ℕ, Divisor.IsCanonicalDivisor (modelStr sX P.sY i) m (divisorSeq K P.KY i)) ∧
      topologicalKrullDim (modelSeq X P.Y i) = 4
  | 0, _ => ⟨P.isProjectiveVariety, P.isLogCanonicalPair, P.isCanonicalDivisor, hdim⟩
  | j + 1, h => by
    have hj := natCast_lt_of_succ_le h
    have hs := P.isPermittedStep j hj
    obtain ⟨-, -, -, ihdim⟩ := stage hdim P j hj.le
    have hsm := hs.isSmallMorphism_step
    have hfc := hs.isContractionOfRay
    haveI : IsProper (P.f j) := isProper_of_isProjectiveMorphism _ hfc.isProjectiveMorphism
    obtain ⟨m, hKm⟩ := hs.isCanonicalDivisor
    refine ⟨hs.isProjectiveVariety_step, ?_, ⟨m, ?_⟩, ?_⟩
    · change MMP.Intersection.IsLogCanonicalPair (P.sY j) (P.BY j)
      rw [P.BY_eq j hj]
      exact hs.isLogCanonicalPair_step
    · change Divisor.IsCanonicalDivisor (P.sY j) m (P.KY j)
      rw [P.KY_eq j hj]
      exact isCanonicalDivisor_flipTransform hfc.isNormalVariety_source hfc.comp_eq
        hs.isBirationalMorphism hsm hKm
    · change topologicalKrullDim (P.Y j) = 4
      haveI : MMP.Mori.IsVariety k (P.sZ j) := hsm.isNormalVariety_target.1
      haveI : MMP.Mori.IsVariety k (P.sY j) := hsm.isNormalVariety_source.1
      haveI : MMP.Mori.IsVariety k (modelStr sX P.sY j) := hfc.isNormalVariety_source.1
      rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (P.sZ j) (P.sY j)
          hsm.isBirationalMorphism,
        MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (P.sZ j)
          (modelStr sX P.sY j) hs.isBirationalMorphism, ihdim]

private theorem solution {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {K : Divisor X} {B : QDivisor X}
    (hdim : topologicalKrullDim X = 4) {P : Program sX K B} (hP : P.IsMaximal) :
    P.n ≠ ⊤ ∧
      ((MMP.Mori.IsProjectiveVariety k (modelStr sX P.sY P.n.toNat) ∧
          MMP.Intersection.IsLogCanonicalPair (modelStr sX P.sY P.n.toNat)
            (divisorSeq B P.BY P.n.toNat) ∧
          (∃ m : ℕ, Divisor.IsCanonicalDivisor (modelStr sX P.sY P.n.toNat) m
            (divisorSeq K P.KY P.n.toNat)) ∧
          QDivisor.IsNefOnCurves (modelStr sX P.sY P.n.toNat)
            (Divisor.toQDivisor (divisorSeq K P.KY P.n.toNat) + divisorSeq B P.BY P.n.toNat)) ∨
        (P.hasFinal ∧
          IsMoriFibreSpace (modelStr sX P.sY P.n.toNat) P.sT (divisorSeq K P.KY P.n.toNat)
            (divisorSeq B P.BY P.n.toNat) P.g)) := by
  have hn : P.n ≠ ⊤ := Program.n_ne_top_of_isAlgClosed hdim P
  have hle : ((P.n.toNat : ℕ) : ℕ∞) ≤ P.n := by rw [ENat.coe_toNat hn]
  obtain ⟨hproj, hlc, hK, hdn⟩ := stage hdim P P.n.toNat hle
  refine ⟨hn, ?_⟩
  rcases hP with htop | ⟨-, hnef⟩ | hfin
  · exact absurd htop hn
  · exact Or.inl ⟨hproj, hlc, hK, hnef⟩
  · obtain ⟨-, hR, hg, -, -, -, hdimT⟩ := P.final_spec hfin
    exact Or.inr ⟨hfin, IsContractionOfRay.isMoriFibreSpace_of_isFibreType hproj hdn hlc hK hR hg
      hdimT⟩

end Proof_thm_main

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori

/-- **Endpoints of maximal programs.** Let `(X, B)` be a projective lc fourfold pair over an
algebraically closed field of characteristic zero, and `P` a maximal program from `(X, B)`. Then
`P` has finitely many birational steps, and either its last model `(X_n, B_n)` is a projective lc
pair with canonical divisor `K_n` and `K_n + B_n` nef, or `P` has a final fibre-type ray and its
final contraction `P.g : X_n ⟶ T` is a Mori fibre space structure on `(X_n, B_n)`. -/
@[mmp "thm_main"]
public theorem Program.IsMaximal.isNefOnCurves_or_isMoriFibreSpace {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {K : Divisor X} {B : QDivisor X}
    (hdim : topologicalKrullDim X = 4) {P : Program sX K B} (hP : P.IsMaximal) :
    P.n ≠ ⊤ ∧
      ((MMP.Mori.IsProjectiveVariety k (modelStr sX P.sY P.n.toNat) ∧
          MMP.Intersection.IsLogCanonicalPair (modelStr sX P.sY P.n.toNat)
            (divisorSeq B P.BY P.n.toNat) ∧
          (∃ m : ℕ, Divisor.IsCanonicalDivisor (modelStr sX P.sY P.n.toNat) m
            (divisorSeq K P.KY P.n.toNat)) ∧
          QDivisor.IsNefOnCurves (modelStr sX P.sY P.n.toNat)
            (Divisor.toQDivisor (divisorSeq K P.KY P.n.toNat) + divisorSeq B P.BY P.n.toNat)) ∨
        (P.hasFinal ∧
          IsMoriFibreSpace (modelStr sX P.sY P.n.toNat) P.sT (divisorSeq K P.KY P.n.toNat)
            (divisorSeq B P.BY P.n.toNat) P.g)) :=
              by revert k X sX K B hdim P hP; first | exact Proof_thm_main.solution | exact Proof_thm_main.solution _ | exact Proof_thm_main.solution _ _ | exact Proof_thm_main.solution _ _ _ | exact Proof_thm_main.solution _ _ _ _

end MMP.Fourfold

