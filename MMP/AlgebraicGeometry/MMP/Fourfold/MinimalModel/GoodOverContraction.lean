module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.LogMinimalModel
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedLogMinimalModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.MinimalModel.LcBirationalBase
public import MMP.AlgebraicGeometry.MMP.Fourfold.Contraction.LcComplement
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
public import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv

/-!
# Good log minimal models over the base of a birational contraction

Let `(X, B)` be a projective lc fourfold pair over `ℂ` with rational boundary, `D = K_X + B`, and
`f : X ⟶ Z` a birational contraction onto a normal projective variety with `-D` `f`-ample. Then
`(X/Z, B)` has a log minimal model `(M/Z, B_M)` in the sense of Birkar such that `K_M + B_M` is
semiample over `Z`, that is, a good log minimal model.

## Main results

* `MMP.Fourfold.IsLogCanonicalPair.exists_isGoodLogMinimalModel_of_isContraction`.

## Implementation notes

The hypotheses are those of `MMP.Fourfold.IsAmpleModelDatum`: the canonical divisor `K` of `X`
is carried explicitly, `D = K + B`, a contraction is `MMP.Fourfold.IsContraction` (projective,
surjective, `f_* 𝒪_X = 𝒪_Z`, between normal varieties), and the `f`-ampleness of `-D` is
`MMP.Mori.QDivisor.HasRelativelyAmpleMultiple`. The conclusion is
`MMP.Fourfold.IsGoodLogMinimalModel`, a log minimal model with `K_M + B_M` semiample over `Z`.

## References

* [C. Birkar, *Existence of log canonical flips and a special LMMP*][BirkarLC], Section 2
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry

namespace Proof_lem_oai4_c3_good_minimal_model_exists

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Mori MMP.Fourfold

/-- On an integral, locally Noetherian, normal, quasi-compact scheme every invertible module is
`𝒪(E)` for a Cartier divisor `E`. -/
private theorem exists_isCartier_divisorialSheaf_iso {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (L : Y.Modules)
    [Stacks.Ample.IsInvertibleModule Y L] :
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
  exact ⟨F.divisor, fun y => ⟨F.W y, F.mem y, _, F.isLocalEquation_divisor y⟩,
    ⟨(@asIso _ _ _ _ F.toDivisorialSheaf F.isIso_toDivisorialSheaf).symm⟩⟩

/-- **A `ℚ`-divisor `ℚ`-linearly trivial over the base is a pull-back.** Let `f : X ⟶ Z` be a
dominant morphism of integral Noetherian normal schemes, and `D ∼_ℚ G` a `ℚ`-divisor on `X` with
`mG = L`, `m > 0`, where `𝒪_X(L) ≅ f^*M` for an invertible `𝒪_Z`-module `M`. Then
`D ∼_ℚ f^*H` for a `ℚ`-Cartier `ℚ`-divisor `H` on `Z`. -/
private theorem exists_qLinearlyEquivalent_pullback {X Z : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Z] [IsLocallyNoetherian Z]
    [IsNormal Z] [CompactSpace Z] (f : X ⟶ Z) [IsDominant f] {D G : QDivisor X}
    (hDG : D.QLinearlyEquivalent G) (M : Z.Modules) [Stacks.Ample.IsInvertibleModule Z M]
    {m : ℕ} (hm : 0 < m) {L : Divisor X} (hL : Divisor.toQDivisor L = (m : ℤ) • G)
    (e : L.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj M) :
    ∃ (H : QDivisor Z) (hHq : H.IsQCartier)
      (hfH : ∀ T : irreducibleComponents X, f (componentGenericPoint X T) ∉ H.supp),
      D.QLinearlyEquivalent (H.pullback hHq hfH) := by
  obtain ⟨E, hEc, ⟨eE⟩⟩ := exists_isCartier_divisorialSheaf_iso M
  have hfE : ∀ T : irreducibleComponents X, f (componentGenericPoint X T) ∉ E.supp :=
    MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant f E
  set P := E.pullback hEc hfE
  have hP : E.IsPullback f hfE P := Divisor.isPullback_pullback hEc hfE
  -- `𝒪_X(L) ≅ f^*M ≅ f^*𝒪_Z(E) ≅ 𝒪_X(f^*E)`, so `L ∼ f^*E`
  have hLP : L.LinearlyEquivalent P := MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso
    (e ≪≫ (Scheme.Modules.pullback f).mapIso eE.symm ≪≫
      (Divisor.IsPullback.divisorialSheafIso (hBc := hEc) hP).symm)
  set H : QDivisor Z := (m : ℚ)⁻¹ • Divisor.toQDivisor E
  have hEH : Divisor.toQDivisor E = (m : ℤ) • H := by
    rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul]
    simp [hm.ne']
  have hHq : H.IsQCartier := ⟨m, by exact_mod_cast hm.ne', E, hEH, hEc⟩
  have hfH := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' f H
  refine ⟨H, hHq, hfH, hDG.trans ?_⟩
  obtain ⟨P', hP', hEP'⟩ := QDivisor.isPullback_pullback hHq hfH m hm E hEH hEc
  have hPP' : P' = P := Divisor.IsPullback.eq hEc hEP' hP
  obtain ⟨φ, hφ⟩ := hLP
  refine ⟨m, hm, φ, ?_⟩
  rw [smul_sub, ← hL, ← hP', hPP', ← map_sub, hφ]

private theorem solution :
    ∀ {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sZ : Z ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hdim : topologicalKrullDim X = 4)
    {B : QDivisor X} (hB : MMP.Intersection.IsLogCanonicalPair sX B)
    {K : Divisor X} (hK : ∃ n : ℕ, K.IsCanonicalDivisor sX n)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    {f : X ⟶ Z} (hf : IsContraction sX sZ f) (hfb : IsBirationalMorphism f)
    (hamp : (-(Divisor.toQDivisor K + B)).HasRelativelyAmpleMultiple f),
    ∃ (M : Scheme.{0}) (_ : IsIntegral M) (_ : CompactSpace M) (_ : IsLocallyNoetherian M)
      (_ : IsNormal M) (sM : M ⟶ Spec (.of ℂ)) (_ : LocallyOfFiniteType sM)
      (_ : QuasiCompact sM) (πM : M ⟶ Z) (KM : Divisor M) (BM : QDivisor M)
      (φ : X.RationalMap M), IsGoodLogMinimalModel sX sZ sM f πM B KM BM φ := by
  intro X Z _ _ _ _ sX _ sZ hX hdim B hB K hK hZ f hf hfb hamp
  have hXn : IsNormalVariety ℂ sX := hf.isNormalVariety_source
  have hZn : IsNormalVariety ℂ sZ := hf.isNormalVariety_target
  haveI : IsIntegral Z := hZn.1.toIsIntegral
  haveI : IsNormal Z := hZn.2
  haveI : LocallyOfFiniteType sZ := hZn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : QuasiCompact sZ := hZn.1.toQuasiCompact
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI : Surjective f := ⟨hf.surjective⟩
  -- the lc complement over `Z`
  obtain ⟨A, hA0, hAq, ⟨G, MZ, hMZ, hDG, m, hm, L, hL, ⟨e⟩⟩, hlc⟩ :=
    exists_isLogCanonicalPair_add_of_hasRelativelyAmpleMultiple_neg sX sZ hX hdim hK hB hf hZ hamp
  obtain ⟨H, hHq, hfH, hlin⟩ := exists_qLinearlyEquivalent_pullback f hDG MZ hm hL e
  -- a projective log minimal model
  obtain ⟨M, _, _, _, _, sM, _, _, πM, KM, BM, φ, hMp, hM⟩ :=
    IsLogCanonicalPair.exists_isLogMinimalModel_of_isBirationalMorphism hX hdim hB hZ hZn hf.comp_eq
      hf.isProjectiveMorphism hfb
  -- dimensions and the canonical divisor
  have hdimZ : topologicalKrullDim Z = 4 := by
    haveI : MMP.Mori.IsVariety ℂ sX := hXn.1
    haveI : MMP.Mori.IsVariety ℂ sZ := hZn.1
    rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ sX hfb, hdim]
  have hK4 : K.IsCanonicalDivisor sX 4 := by
    obtain ⟨n, hn⟩ := hK
    obtain rfl : n = 4 := by exact_mod_cast (hdim ▸ hn.topologicalKrullDim_eq).symm
    exact hn
  exact ⟨M, inferInstance, inferInstance, inferInstance, inferInstance, sM, inferInstance,
    inferInstance, πM, KM, BM, φ,
    hM.isGoodLogMinimalModel_of_add_qLinearlyEquivalent_pullback hX hdim hZ hZn hdimZ
      hf.comp_eq hf.isProjectiveMorphism hfb hK4 (fun P => hB.2.1 P) hA0 hAq hlc hHq hfH hlin hMp⟩

end Proof_lem_oai4_c3_good_minimal_model_exists

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori

/-- **Good log minimal models over the base of a birational contraction.** Let `X` be a
projective fourfold over `ℂ`, `K` a canonical divisor of `X`, `B` a `ℚ`-divisor with `(X, B)` log
canonical, and `f : X ⟶ Z` a birational contraction (`MMP.Fourfold.IsContraction`,
`MMP.Mori.IsBirationalMorphism`) onto a normal projective variety `Z` with `-(K + B)` `f`-ample.
Then there are a normal variety `M` with a projective morphism `π_M : M ⟶ Z`, a canonical divisor
`K_M`, a `ℚ`-divisor `B_M` and a birational map `φ : X ⤏ M` over `Z` such that `(M/Z, B_M)` is a
log minimal model of `(X/Z, B)` with `K_M + B_M` semiample over `Z`
(`MMP.Fourfold.IsGoodLogMinimalModel`). -/
@[mmp "lem_oai4_c3_good_minimal_model_exists"]
public theorem IsLogCanonicalPair.exists_isGoodLogMinimalModel_of_isContraction
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sZ : Z ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hdim : topologicalKrullDim X = 4)
    {B : QDivisor X} (hB : MMP.Intersection.IsLogCanonicalPair sX B)
    {K : Divisor X} (hK : ∃ n : ℕ, K.IsCanonicalDivisor sX n)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    {f : X ⟶ Z} (hf : IsContraction sX sZ f) (hfb : IsBirationalMorphism f)
    (hamp : (-(Divisor.toQDivisor K + B)).HasRelativelyAmpleMultiple f) :
    ∃ (M : Scheme.{0}) (_ : IsIntegral M) (_ : CompactSpace M) (_ : IsLocallyNoetherian M)
      (_ : IsNormal M) (sM : M ⟶ Spec (.of ℂ)) (_ : LocallyOfFiniteType sM)
      (_ : QuasiCompact sM) (πM : M ⟶ Z) (KM : Divisor M) (BM : QDivisor M)
      (φ : X.RationalMap M), IsGoodLogMinimalModel sX sZ sM f πM B KM BM φ :=
        by revert X Z sX sZ hX hdim B hB K hK hZ f hf hfb hamp; first | exact Proof_lem_oai4_c3_good_minimal_model_exists.solution | exact Proof_lem_oai4_c3_good_minimal_model_exists.solution _ | exact Proof_lem_oai4_c3_good_minimal_model_exists.solution _ _ | exact Proof_lem_oai4_c3_good_minimal_model_exists.solution _ _ _ | exact Proof_lem_oai4_c3_good_minimal_model_exists.solution _ _ _ _

end MMP.Fourfold

