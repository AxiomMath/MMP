module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Defs
public import MMP.AlgebraicGeometry.Morphisms.Birational.RationalMap
public import MMP.AlgebraicGeometry.Divisor.Canonical.Basic
public import MMP.AlgebraicGeometry.Divisor.SNC
public import MMP.AlgebraicGeometry.Divisor.Arithmetic
public import MMP.AlgebraicGeometry.Divisor.Pullback
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveNumber
public import MMP.AlgebraicGeometry.Vanishing.KltRationalSingularities
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Valuation
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import StacksFrontier.AlgebraicGeometry.Perfect.VanishingHigherDirectImagesLocallyFree
public import MMP.AlgebraicGeometry.Positivity.RelativeAmplePullbackTwist
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback

section

/-!
# Relative vanishing with a pull-back adjoint gap and preserved floor strata

Let `p : W ⟶ X` be a projective birational morphism of projective varieties over an
algebraically closed field `k` of characteristic zero, with `W` smooth and `X` normal, let `K_W`
be a canonical divisor of `W` and `B` a `ℚ`-divisor with simple normal crossing support and
coefficients in `[0, 1]`, such that `p` is an isomorphism at the generic point of every stratum
of `⌊B⌋`. Assume there is an effective `ℚ`-Cartier `ℚ`-divisor `J` on `W` with `-J` `p`-ample,
`B + J` with snc support, and `Supp J` containing no stratum of `⌊B⌋`. If `M` is a Cartier
divisor on `W` with `M - (K_W + B) ∼_ℚ p^*L` for a `ℚ`-Cartier `ℚ`-divisor `L` on `X`, then
`R^i p_* 𝒪_W(M) = 0` for every `i > 0`.

Write `mJ = D` with `-D` `p`-ample. Relative ampleness is open, so `r(-D) + ⌊B⌋` is `p`-ample
for some `r > 0`. For a large integer `c` put `ε = 1/c`, `δ = rm/c` and
`Θ = B - ε⌊B⌋ + δJ`. No component of `⌊B⌋` lies in `Supp J`, since each such component is a
stratum of `⌊B⌋`; hence `Θ` is effective with coefficients `< 1`, and its support lies in that of
`B + J`, so it is snc. Moreover
`c(M - (K_W + Θ)) = c(M - (K_W + B)) + ⌊B⌋ + r(-D) ∼ c p^*L + ⌊B⌋ + r(-D)`, and twisting a
`p`-ample divisor by a pull-back from `X` or by a principal divisor keeps it `p`-ample. The
relative Kawamata–Viehweg vanishing theorem for the klt snc boundary `Θ` then gives the claim.

## Main results

* `MMP.Fourfold.isZero_rightDerived_pushforward_divisorialSheaf_of_qLinearlyEquivalent_pullback`

## Implementation notes

* `W` and `X` carry structure morphisms `sW`, `sX` to `Spec k`, and `p ≫ sX = sW` says that `p`
  is a morphism over `k`. The source works over `ℂ`; the statement is over any algebraically
  closed field of characteristic zero.
* "`p` is an isomorphism at the generic point of `S`" is `¬ S ⊆ Ex(p)` for the exceptional set
  `MMP.Mori.exceptionalSet`; the strata of `⌊B⌋` are `MMP.Fourfold.IsSNCStratum` of
  `MMP.Mori.DivisorWithCoeffs.roundDown`, and "`J` contains no stratum" is `¬ S ⊆ Supp J`.
* `-J` is `p`-ample when some positive multiple `mJ` is a Cartier divisor `D` with `-D` `p`-ample
  (`MMP.Mori.Divisor.IsRelativelyAmple`); this also makes `J` `ℚ`-Cartier.
* `p^*L` is `MMP.Mori.QDivisor.pullback`; its hypothesis that `p` maps no generic point of a
  component of `W` into `Supp L` holds for every birational `p`.
* `R^i p_*` is the `i`-th right derived functor of `Scheme.Modules.pushforward p`, and
  `𝒪_W(M)` is `MMP.Mori.Divisor.divisorialSheaf`.
* The source proceeds by induction on the dimension and on the number of components of `⌊B⌋`,
  restricting to a floor component. The perturbation above makes the induction unnecessary: the
  hypothesis that `Supp J` contains no stratum of `⌊B⌋` already allows lowering every coefficient
  `1` of `B` by `ε` while compensating with the `p`-ample `-δJ`, a standard argument
  ([KollarMori], proof of Theorem 2.64 / Corollary 2.68).

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
* [O. Fujino, *Fundamental theorems for the log minimal model program*][Fujino2011]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MMP.Mori

namespace MMP.FourfoldProofs.FourfoldPullbackGapReidFukudaProof

open RingedSpaceModuleAdjunction Stacks.Ample

section AmpleTools

variable {W X : Scheme.{0}} [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W]

/-- Relative ampleness of an invertible sheaf depends only on its isomorphism class. -/
private theorem isRelativelyAmple_of_iso (f : W ⟶ X) {L L' : W.Modules}
    [IsInvertibleModule W L] [IsInvertibleModule W L'] (e : L ≅ L')
    (h : MMP.Mori.IsRelativelyAmple f L) : MMP.Mori.IsRelativelyAmple f L' := by
  intro y
  obtain ⟨V, hV, hyV, hamp⟩ := h y
  exact ⟨V, hV, hyV, (Stacks.RelativeVeryAmple.isAmple_congr _ _
    ((modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).mapIso e)).1 hamp⟩

/-- Adding a principal divisor to an `f`-ample Cartier divisor keeps it `f`-ample. -/
private theorem isRelativelyAmple_add_principalDivisor (f : W ⟶ X) {A : Divisor W}
    (hA : A.IsCartier) (hAf : A.IsRelativelyAmple f hA) (φ : (RationalFunctions W)ˣ)
    (h : (A + principalDivisor φ).IsCartier) :
    (A + principalDivisor φ).IsRelativelyAmple f h := by
  haveI := hA.isInvertibleModule_divisorialSheaf
  haveI := h.isInvertibleModule_divisorialSheaf
  refine isRelativelyAmple_of_iso f (Divisor.divisorialSheafMulIso φ⁻¹ fun E => ?_) hAf
  rw [DivisorWithCoeffs.coeff_add, coeff_principalDivisor, PrimeDivisor.ord_inv]
  ring

/-- `𝒪(nA) ≅ 𝒪(A)^{⊗ n}` for a Cartier divisor `A`. -/
private noncomputable def divisorialSheafNsmulIso {A : Divisor W} (hA : A.IsCartier) (n : ℕ) :
    haveI := hA.isInvertibleModule_divisorialSheaf
    (n • A).divisorialSheaf ≅ tensorPowModule W A.divisorialSheaf (n : ℤ) := by
  haveI := hA.isInvertibleModule_divisorialSheaf
  induction n with
  | zero =>
    exact eqToIso (by rw [zero_smul]) ≪≫ Divisor.divisorialSheafZeroIso ≪≫
      (tensorPowModuleZeroIso W A.divisorialSheaf).symm
  | succ n ih =>
    exact eqToIso (by rw [succ_nsmul]) ≪≫
      ((hA.nsmul n).divisorialSheafTensorIso hA).symm ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso ih).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).obj _).mapIso
        (tensorPowModuleOneIso W A.divisorialSheaf).symm ≪≫
      tensorPowModuleAddIso W A.divisorialSheaf (n : ℤ) 1 ≪≫
      eqToIso (by push_cast; rfl)

/-- **Openness of relative ampleness.** If `H` is an `f`-ample Cartier divisor, `f` is
quasi-compact over a quasi-compact base, and `F` is any Cartier divisor, then `F + nH` is
`f`-ample for all large `n`. This is [Stacks, Tag 0C4K] for `𝟙 ≫ f`: every invertible sheaf is
ample relative to the identity. -/
private theorem exists_isRelativelyAmple_add_nsmul [CompactSpace X] (f : W ⟶ X) [QuasiCompact f]
    {H : Divisor W} (hH : H.IsCartier) (hHf : H.IsRelativelyAmple f hH) {F : Divisor W}
    (hF : F.IsCartier) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → (F + n • H).IsRelativelyAmple f (hF.add (hH.nsmul n)) := by
  haveI := hH.isInvertibleModule_divisorialSheaf
  haveI := hF.isInvertibleModule_divisorialSheaf
  have hL : Stacks.RelativeAmple.IsRelativelyAmple (𝟙 W) F.divisorialSheaf := by
    refine ⟨inferInstance, fun V hV => ?_⟩
    haveI : IsAffine ((𝟙 W) ⁻¹ᵁ V).toScheme := by
      rw [Scheme.Hom.id_preimage]; exact hV
    exact (Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mpr <|
      Scheme.Modules.isAmple_of_isAffine_of_isInvertible (X := ((𝟙 W) ⁻¹ᵁ V).toScheme)
      ((modulePullback ((𝟙 W) ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj F.divisorialSheaf)
  have hM : Stacks.RelativeAmple.IsRelativelyAmple f H.divisorialSheaf :=
    Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple f _ inferInstance
      hHf
  obtain ⟨n₀, hn₀⟩ := Stacks.AmplePullbackDatum.exists_threshold_isRelativelyAmple_comp (𝟙 W) f
    _ _ hL hM
  refine ⟨n₀, fun n hn => ?_⟩
  haveI := (hF.add (hH.nsmul n)).isInvertibleModule_divisorialSheaf
  have eB : (modulePullback (Scheme.Hom.toLRSHom (𝟙 W)).toShHom).obj H.divisorialSheaf ≅
      H.divisorialSheaf :=
    (Adjunction.leftAdjointUniq
      (modulePullbackPushforwardAdjunction (Scheme.Hom.toLRSHom (𝟙 W)).toShHom)
      (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 W))).app _ ≪≫
      (Scheme.Modules.pullbackId W).app _
  have e : Stacks.AmplePullbackPart1.tensorPullbackPowModule (𝟙 W) F.divisorialSheaf
      H.divisorialSheaf n ≅ (F + n • H).divisorialSheaf :=
    Stacks.RelativeVeryAmple.tensorModulesMapIso W (Iso.refl _)
        (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso (𝟙 W) _ n ≪≫
          Stacks.RelativeVeryAmple.tensorPowModuleIsoOfIso W _ _ eB n ≪≫
          (divisorialSheafNsmulIso hH n).symm) ≪≫
      hF.divisorialSheafTensorIso (hH.nsmul n)
  have h := (Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _ e).mp (hn₀ n hn)
  rw [Category.id_comp] at h
  exact MMP.Mori.IsRelativelyAmple.of_stacks _ _ h

end AmpleTools

/-! ### Divisor bookkeeping -/

section Bookkeeping

/-- The support of a component of a divisor is a stratum of it. -/
private theorem isSNCStratum_support {R : Type*} [Zero R] {Y : Scheme.{0}}
    {D : DivisorWithCoeffs R Y} {P : MMP.Mori.PrimeDivisor Y} (hP : D.coeff P ≠ 0) :
    MMP.Fourfold.IsSNCStratum D P.support := by
  refine ⟨{P}, by simpa using Finsupp.mem_support_iff.2 hP, ⟨?_, by simp⟩, ?_⟩
  · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isIrreducible_singleton.closure
  · rintro T ⟨-, hT⟩ -
    simpa using hT

/-- One coefficient of the perturbed boundary `B - ε⌊B⌋ + δJ`: if `b ∈ [0, 1]`, `j ≥ 0`
vanishes when `b = 1`, `0 < ε ≤ 1` and `δj < 1 - b` when `b < 1`, then
`b - ε⌊b⌋ + δj ∈ [0, 1)`. -/
private theorem sub_mul_floor_add_mul_mem_Ico {b j ε δ : ℚ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hj0 : 0 ≤ j) (hj : b = 1 → j = 0) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 ≤ δ)
    (hδ : b ≠ 1 → δ * j < 1 - b) :
    b - ε * ⌊b⌋ + δ * j ∈ Set.Ico 0 1 := by
  rcases eq_or_ne b 1 with rfl | h1
  · simp [hj rfl]; constructor <;> linarith
  · rw [Int.floor_eq_zero_iff.2 ⟨hb0, lt_of_le_of_ne hb1 h1⟩]
    have := hδ h1
    constructor <;> push_cast <;> nlinarith

/-- **The klt perturbation of a boundary.** Let `0 ≤ B ≤ 1` and `J ≥ 0` be `ℚ`-divisors with
`B + J` snc, `J` vanishing along every component of `⌊B⌋`. Then there is `δ₀ > 0` such that
for `0 < ε ≤ 1` and `0 ≤ δ < δ₀` the divisor `B - ε⌊B⌋ + δJ` is an effective snc divisor with
all coefficients `< 1`. -/
private theorem exists_isKlt_sub_smul_roundDown_add_smul {Y Z : Scheme.{0}} {s : Y ⟶ Z}
    {B J : QDivisor Y} (hB0 : ∀ P, 0 ≤ B.coeff P) (hB1 : ∀ P, B.coeff P ≤ 1)
    (hJ0 : ∀ P, 0 ≤ J.coeff P) (hJfl : ∀ P, B.coeff P = 1 → J.coeff P = 0)
    (hBJ : DivisorWithCoeffs.IsSNC s (B + J)) :
    ∃ δ₀ : ℚ, 0 < δ₀ ∧ ∀ ε δ : ℚ, 0 < ε → ε ≤ 1 → 0 ≤ δ → δ < δ₀ →
      (B - ε • Divisor.toQDivisor B.roundDown + δ • J).IsEffective ∧
      (∀ P, (B - ε • Divisor.toQDivisor B.roundDown + δ • J).coeff P < 1) ∧
      DivisorWithCoeffs.IsSNC s (B - ε • Divisor.toQDivisor B.roundDown + δ • J) := by
  set t : ℚ := ∑ P ∈ J.support, J.coeff P / (1 - B.coeff P)
  have hf : ∀ P, 0 ≤ J.coeff P / (1 - B.coeff P) := fun P =>
    div_nonneg (hJ0 P) (by linarith [hB1 P])
  have ht0 : 0 ≤ t := Finset.sum_nonneg fun P _ => hf P
  have ht : ∀ P, B.coeff P ≠ 1 → J.coeff P ≤ t * (1 - B.coeff P) := fun P hP => by
    rw [← div_le_iff₀ (by linarith [lt_of_le_of_ne (hB1 P) hP])]
    by_cases hJ : J.coeff P = 0
    · simpa [hJ] using ht0
    · exact Finset.single_le_sum (fun Q _ => hf Q) (Finsupp.mem_support_iff.2 hJ)
  refine ⟨1 / (t + 1), by positivity, fun ε δ hε0 hε1 hδ0 hδ => ?_⟩
  have hδt : δ * t < 1 := by
    rw [lt_div_iff₀ (by positivity)] at hδ
    nlinarith
  have hc : ∀ P, (B - ε • Divisor.toQDivisor B.roundDown + δ • J).coeff P ∈ Set.Ico 0 1 :=
    fun P => by
      simpa [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_sub,
        DivisorWithCoeffs.coeff_smul] using
        sub_mul_floor_add_mul_mem_Ico (hB0 P) (hB1 P) (hJ0 P) (hJfl P) hε0 hε1 hδ0 fun h1 => by
          nlinarith [ht P h1, lt_of_le_of_ne (hB1 P) h1]
  refine ⟨fun P => (hc P).1, fun P => (hc P).2, hBJ.of_support_subset fun P hP => ?_⟩
  rw [Finsupp.mem_support_iff] at hP ⊢
  change (B + J).coeff P ≠ 0
  intro h0
  rw [DivisorWithCoeffs.coeff_add] at h0
  have hB : B.coeff P = 0 := by linarith [hB0 P, hJ0 P]
  have hJ : J.coeff P = 0 := by linarith [hB0 P, hJ0 P]
  exact hP (by
    change DivisorWithCoeffs.coeff _ P = 0
    simp [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul,
      hB, hJ])

end Bookkeeping

end MMP.FourfoldProofs.FourfoldPullbackGapReidFukudaProof

end

section

public section

open CategoryTheory AlgebraicGeometry MMP.Mori

namespace MMP.Fourfold

open MMP.FourfoldProofs.FourfoldPullbackGapReidFukudaProof RingedSpaceModuleAdjunction Stacks.Ample
  CategoryTheory.Limits in
/-- **Relative vanishing with a pull-back adjoint gap** (Reid–Fukuda type). Let `p : W ⟶ X` be a
projective birational morphism of projective varieties over an algebraically closed field `k` of
characteristic zero, with `W` smooth of dimension `n` with canonical divisor `K` and `X` normal.
Let `B` be a `ℚ`-divisor with snc support and coefficients in `[0, 1]` such that no stratum of
`⌊B⌋` lies in the exceptional set of `p`. Let `J ≥ 0` be a `ℚ`-divisor with `mJ = D` Cartier and
`-D` `p`-ample for some `m > 0`, such that `B + J` is snc and `Supp J` contains no stratum of
`⌊B⌋`. If `M` is a Cartier divisor with `M - (K + B) ∼_ℚ p^*L` for a `ℚ`-Cartier `ℚ`-divisor
`L` on `X`, then `R^i p_* 𝒪_W(M) = 0` for every `i > 0`. -/
@[mmp "lem_fourfold_pullback_gap_reid_fukuda"]
public theorem isZero_rightDerived_pushforward_divisorialSheaf_of_qLinearlyEquivalent_pullback
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sX]
    [IsLocallyNoetherian X] [IsNormal X]
    {W : Scheme.{0}} (sW : W ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sW]
    (hWsm : IsSmoothScheme sW)
    [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W] (p : W ⟶ X) (hps : p ≫ sX = sW)
    (hpp : IsProjective p) (hpb : IsBirationalMorphism p)
    {n : ℕ} (K : Divisor W) (hK : K.IsCanonicalDivisor sW n)
    (B : QDivisor W) (hB : B.IsSNC sW) (hB0 : ∀ E, 0 ≤ B E) (hB1 : ∀ E, B E ≤ 1)
    (hstrata : ∀ S : Set W, IsSNCStratum B.roundDown S → ¬ S ⊆ (exceptionalSet p : Set W))
    (J : QDivisor W) (hJ0 : ∀ E, 0 ≤ J E) (m : ℕ) (hm : 0 < m) (D : Divisor W)
    (hD : D.IsCartier) (hDJ : Divisor.toQDivisor D = (m : ℤ) • J)
    (hJa : Divisor.IsRelativelyAmple p (-D) hD.neg) (hBJ : (B + J).IsSNC sW)
    (hJstrata : ∀ S : Set W, IsSNCStratum B.roundDown S → ¬ S ⊆ (J.supp : Set W))
    (L : QDivisor X) (hL : L.IsQCartier)
    (hLs : ∀ Z : irreducibleComponents W, p (componentGenericPoint W Z) ∉ L.supp)
    (M : Divisor W) (hM : M.IsCartier)
    (hgap : (Divisor.toQDivisor M - (Divisor.toQDivisor K + B)).QLinearlyEquivalent
      (L.pullback hL hLs))
    (i : ℕ) (hi : 0 < i) :
    Limits.IsZero (((Scheme.Modules.pushforward p).rightDerived i).obj M.divisorialSheaf) := by
  classical
  have hproj : IsProjectiveMorphism p :=
    IsProjectiveMorphism.of_comp p sX (hps ▸ IsProjectiveVariety.isProjective)
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hproj
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : IsDominant p := hpb.isDominant
  have hcart : ∀ G : Divisor W, G.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hWsm
  have hJfl : ∀ P, B.coeff P = 1 → J.coeff P = 0 := fun P h => by
    by_contra hJ
    exact hJstrata _ (isSNCStratum_support (by simp [h] : B.roundDown.coeff P ≠ 0))
      (DivisorWithCoeffs.support_subset_supp hJ)
  obtain ⟨δ₀, hδ₀, hklt⟩ := exists_isKlt_sub_smul_roundDown_add_smul hB0 hB1 hJ0 hJfl hBJ
  obtain ⟨r₀, hr₀⟩ := exists_isRelativelyAmple_add_nsmul p hD.neg hJa (hcart B.roundDown)
  obtain ⟨r, hr, C, hC, hCc⟩ := hL.exists_pos
  obtain ⟨C', hC', hCpb⟩ := QDivisor.isPullback_pullback hL hLs r hr C hC hCc
  obtain ⟨m₁, hm₁, φ, hφ⟩ := hgap
  obtain ⟨N, hN⟩ := exists_nat_gt ((r₀ * m : ℚ) / δ₀)
  have hN0 : 0 < N := by exact_mod_cast (by positivity : (0 : ℚ) ≤ _).trans_lt hN
  set c : ℕ := r * m₁ * N with hc
  have hc0 : 0 < c := by positivity
  have hcq : (0 : ℚ) < c := by exact_mod_cast hc0
  obtain ⟨hΘ0, hΘ1, hΘsnc⟩ := hklt (1 / c) ((r₀ * m : ℚ) / c) (by positivity)
    ((div_le_one hcq).2 (by exact_mod_cast hc0)) (by positivity) <| by
      rw [div_lt_iff₀ hδ₀] at hN
      rw [div_lt_iff₀ hcq]
      have : (1 : ℚ) ≤ r * m₁ := by exact_mod_cast Nat.mul_pos hr hm₁
      push_cast [hc]
      nlinarith [mul_le_mul_of_nonneg_right this (by positivity : (0 : ℚ) ≤ N * δ₀)]
  have hA1 := MMP.Threefold.Resolution.isRelativelyAmple_add_of_isPullback p (hcart _)
    (hr₀ r₀ le_rfl) (hCc.zsmul _)
    (hCpb.zsmul hCc ((m₁ * N : ℕ) : ℤ)
      (MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' p _))
    (hcart _)
  have hA2 := isRelativelyAmple_add_principalDivisor p (hcart _) hA1 (φ ^ (r * N)) (hcart _)
  refine MMP.Mori.isZero_rightDerived_pushforward_divisorialSheaf_of_hasRelativelyAmpleMultiple
    sW sX hWsm p hps hproj hK hΘ0 hΘsnc hΘ1 hM ⟨c, hc0, _, hcart _, ?_, hA2⟩ i hi
  ext P
  have hC'P : (C'.coeff P : ℚ) = r * (L.pullback hL hLs).coeff P := by
    simpa [DivisorWithCoeffs.coeff_smul] using congrArg (DivisorWithCoeffs.coeff · P) hC'
  have hφP : (P.ord φ : ℚ) = m₁ * (M.coeff P - (K.coeff P + B.coeff P) -
      (L.pullback hL hLs).coeff P) := by
    simpa [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_sub,
      DivisorWithCoeffs.coeff_add, coeff_principalDivisor] using
      (congrArg (DivisorWithCoeffs.coeff · P) hφ).symm
  have hDP : (D.coeff P : ℚ) = m * J.coeff P := by
    simpa [DivisorWithCoeffs.coeff_smul] using congrArg (DivisorWithCoeffs.coeff · P) hDJ
  change (DivisorWithCoeffs.coeff _ P : ℚ) = _
  simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
    DivisorWithCoeffs.coeff_neg, DivisorWithCoeffs.coeff_sub, coeff_principalDivisor,
    PrimeDivisor.ord_pow, Divisor.coeff_toQDivisor, smul_eq_mul, nsmul_eq_mul, zsmul_eq_mul]
  push_cast
  rw [hC'P, hφP, hDP, hc]
  push_cast
  field_simp
  ring

end MMP.Fourfold

end
