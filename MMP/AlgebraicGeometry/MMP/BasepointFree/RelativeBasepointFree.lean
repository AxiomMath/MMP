module

public import MMP.AlgebraicGeometry.MMP.BasepointFree.NefPullbackTwist
public import MMP.AlgebraicGeometry.MMP.BasepointFree.RelativeAmpleTwist

/-!
# The relative basepoint-free theorem for projective morphisms

Let `f : X ⟶ Y` be a morphism of projective varieties over an algebraically closed field `k` of
characteristic zero and `(X, Δ)` a klt pair with `Δ` effective. Let `D` be an `f`-nef Cartier
divisor on `X` such that `aD - K_X - Δ` is `f`-nef and `f`-big for some rational `a > 0`. Then
`bD` is `f`-free for all `b ≫ 0`: the natural map `f^* f_* 𝒪_X(bD) → 𝒪_X(bD)` is surjective.

The proof makes `aD - K_X - Δ` ample after twisting `D` by the pull-back of an ample divisor on
`Y` and enlarging the boundary slightly, makes the twist nef by a further pull-back, applies the
absolute basepoint-free theorem, and descends global generation of the twist to `f`-freeness
of `bD`.

## Main results

* `MMP.Mori.exists_forall_ge_isRelativelyFreeDivisor_of_isKltPair`: the statement above.

## Implementation notes

The divisor `D` is a Weil divisor with `D.IsCartier`, and `f`-freeness of `bD` is
`MMP.Fourfold.IsRelativelyFreeDivisor f (b • D)`, the surjectivity of the counit
`f^* f_* 𝒪_X(bD) → 𝒪_X(bD)` on the divisorial sheaf; for a Cartier divisor this is
`MMP.Mori.IsRelativelyFreeCartier`. The setting (3.21.0) is `MMP.Mori.IsProjectiveSetting`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Theorem 3.24
  in case (3.21.0), proof 3.26
-/

public section

open AlgebraicGeometry CategoryTheory

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Mori

section Helpers

variable {k : Type} [Field k] {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] [CompactSpace X]

/-- An ample invertible sheaf has nonnegative degree along every proper curve mapping to `T`. -/
private theorem degreeOn_nonneg_of_isAmple {C T : Scheme.{0}}
    (sT : T ⟶ Spec (.of k)) [IsSeparated sT] [LocallyOfFiniteType sT] (φ : C ⟶ T)
    [AlgebraicGeometry.IsCurve k (φ ≫ sT)] [IsProper (φ ≫ sT)] (L : T.Modules)
    [SheafOfModules.IsInvertible T.presheaf T.ringCatSheaf.2 L] (hL : Stacks.Ample.IsAmple T L) :
    0 ≤ degreeOn k sT φ (IsCurve.topologicalKrullDim_eq_one (f := φ ≫ sT)).le L := by
  by_cases hpt : ∃ x : T, Set.range φ = {x}
  · rw [degreeOn_eq_zero_of_range_eq_singleton sT φ L hpt]
  · rw [degreeOn_eq_degreeOver_mul sT φ L hpt]
    have : IsProper φ := IsProper.of_comp φ sT
    have : IsProper (φ.imageι ≫ sT) := isProper_imageι_comp φ sT
    have : AlgebraicGeometry.IsCurve k (φ.imageι ≫ sT) := isCurve_imageι_comp sT φ hpt
    have h1 := isAmple_pullback_of_isFinite φ.imageι L
      ((Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple T L).mpr hL)
    have := MMP.Mori.isInvertible_pullback_obj φ.imageι L
    exact mul_nonneg (by positivity) (invertibleCurveDegree_pos_of_isAmple_of_isCurve k
      (φ.imageι ≫ sT) (topologicalKrullDim_image_le_one sT φ) _ h1).le

/-- A Cartier divisor `G` with `𝒪_X(G) ≅ f^*L`, `L` ample, is nef. -/
private theorem isNef_toQDivisor_of_iso_pullback {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] {f : X ⟶ Y}
    (hf : f ≫ sY = sX) (L : Y.Modules) [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    (hL : Stacks.Ample.IsAmple Y L) {G : Divisor X} (hGc : G.IsCartier)
    (e : G.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj L) :
    (Divisor.toQDivisor G).IsNef k sX := by
  have hq := QDivisor.isQCartier_toQDivisor hGc
  refine ⟨hq, fun C i _ _ _ hC => ?_⟩
  have := hGc.isInvertibleModule_divisorialSheaf
  have := MMP.Mori.isInvertible_pullback_obj f L
  rw [QDivisor.intersectionNumber_toQDivisor k sX i hC.le G hGc hq]
  have hc : (i ≫ f) ≫ sY = i ≫ sX := by rw [Category.assoc, hf]
  have : IsProper ((i ≫ f) ≫ sY) := hc ▸ inferInstance
  have : AlgebraicGeometry.IsCurve k ((i ≫ f) ≫ sY) := by
    rw [hc]
    exact { topologicalKrullDim_eq_one := hC }
  have h1 : G.degreeOn k sX i hC.le hGc = degreeOn k sY (i ≫ f)
      (IsCurve.topologicalKrullDim_eq_one (f := (i ≫ f) ≫ sY)).le L := by
    rw [← degreeOn_pullback_eq_degreeOn_comp sX sY f i hf]
    exact degreeOn_eq_of_iso k sX i hC.le e
  rw [h1]
  exact_mod_cast degreeOn_nonneg_of_isAmple sY (i ≫ f) L hL

/-- A nonnegative rational multiple of a nef `ℚ`-divisor is nef. -/
private theorem isNef_smul {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {D : QDivisor X}
    (hD : D.IsNef k sX) {q : ℚ} (hq : 0 ≤ q) : (q • D).IsNef k sX := by
  obtain ⟨hDq, h⟩ := hD
  have hqD : (q • D).IsQCartier := MMP.Flips.QDivisor.IsQCartier.qsmul hDq q
  refine ⟨hqD, fun C i _ _ _ hC => ?_⟩
  rw [MMP.Fourfold.intersectionNumber_smul sX i hC.le D hDq q hqD]
  exact mul_nonneg hq (h C i hC)

/-- Twisting by a Cartier divisor `G` with `𝒪_X(G) ≅ f^*L` preserves `f`-nefness: `G` has degree
zero on every curve contracted by `f`. -/
private theorem isRelativelyNef_toQDivisor_add_of_iso_pullback {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX] {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]
    {f : X ⟶ Y} (hf : f ≫ sY = sX) (L : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L] {G : Divisor X}
    (hGc : G.IsCartier) (e : G.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj L)
    {D : Divisor X} (hDc : D.IsCartier) (hD : (Divisor.toQDivisor D).IsRelativelyNef sX f) :
    (Divisor.toQDivisor (D + G)).IsRelativelyNef sX f := by
  have hq := QDivisor.isQCartier_toQDivisor (hDc.add hGc)
  refine MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sX hq fun C hC => ?_
  have := hGc.isInvertibleModule_divisorialSheaf
  have := MMP.Mori.isInvertible_pullback_obj f L
  have h1 := MMP.Fourfold.QDivisor.IsRelativelyNef.intersectionNumber_nonneg sX hD
    (QDivisor.isQCartier_toQDivisor hDc) C hC
  rw [QDivisor.intersectionNumber_toQDivisor k sX C.ι C.dim_le D hDc] at h1
  have h2 : G.degreeOn k sX C.ι C.dim_le hGc = 0 := by
    rw [Divisor.degreeOn, degreeOn_eq_of_iso k sX C.ι C.dim_le e]
    exact C.degree_pullback_eq_zero_of_isContractedBy f hf hC L
  rwa [QDivisor.intersectionNumber_toQDivisor k sX C.ι C.dim_le _ (hDc.add hGc),
    Divisor.degreeOn_add k sX C.ι C.dim_le _ _ hDc hGc, h2, add_zero]

/-- **A globally generated twist by a divisor locally principal over the base is relatively
free.** If `|M + L|` is basepoint free and `L` has a local equation over a neighbourhood of every
point of `Z`, then `f^* f_* 𝒪_X(M) → 𝒪_X(M)` is surjective. -/
private theorem isRelativelyFreeDivisor_of_isBasepointFree_add {Z : Scheme.{0}} (f : X ⟶ Z)
    {M L : Divisor X} (hM : (M + L).IsBasepointFree)
    (hL : ∀ z : Z, ∃ U : Z.Opens, z ∈ U ∧ ∃ ψ : (RationalFunctions X)ˣ,
      L.IsLocalEquation (f ⁻¹ᵁ U) ψ) :
    MMP.Fourfold.IsRelativelyFreeDivisor f M := by
  refine MMP.Fourfold.isRelativelyFreeDivisor_of_forall_exists f fun x => ?_
  have hx : x ∉ ((M + L).baseLocus : Set X) := by
    rw [hM]
    exact fun h => h
  rw [Divisor.mem_baseLocus_iff] at hx
  push Not at hx
  obtain ⟨σ, hσ, hxσ⟩ := hx
  obtain ⟨U, hxU, χ, hχ⟩ := hL (f x)
  set φ := (Divisor.isUnit_sectionToRationalFunctions hσ).unit
  have hcoeff : ∀ P : MMP.Mori.PrimeDivisor X, (P.support ∩ f ⁻¹ᵁ U).Nonempty →
      M.coeff P + P.ord (φ * χ) = ((M + L).zeroDivisor σ hσ).coeff P := by
    intro P hP
    rw [Divisor.zeroDivisor_eq, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_add,
      coeff_principalDivisor, PrimeDivisor.ord_mul, hχ P hP]
    ring
  refine ⟨U, hxU, φ * χ, fun P hP => ?_, fun P hxP => ?_⟩
  · rw [hcoeff P hP]
    exact Divisor.zeroDivisor_nonneg _ σ hσ P
  · rw [hcoeff P ⟨x, hxP, hxU⟩]
    by_contra hne
    exact hxσ (DivisorWithCoeffs.mem_supp_iff.mpr ⟨P, hne, hxP⟩)

end Helpers

/-- **The relative basepoint-free theorem** (Kollár–Mori 3.24, case (3.21.0)). Let `f : X ⟶ Y`
be a morphism of projective varieties over an algebraically closed field `k` of characteristic
zero, `(X, Δ)` a klt pair with `Δ ≥ 0` and canonical divisor `K`, and `D` an `f`-nef Cartier
divisor on `X` such that `aD - K - Δ` is `f`-nef and `f`-big for some rational `a > 0`. Then
there is `b₀` such that for every `b ≥ b₀` the divisor `bD` is `f`-free: the counit
`f^* f_* 𝒪_X(bD) → 𝒪_X(bD)` is surjective. -/
@[mmp "thm_km3b_relative_basepoint_free_projective"]
public theorem exists_forall_ge_isRelativelyFreeDivisor_of_isKltPair {k : Type} [Field k]
    {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {sY : Y ⟶ Spec (.of k)} {f : X ⟶ Y}
    (hf : IsProjectiveSetting k sX sY f)
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} (hklt : IsKltPair sX n K Δ) (hΔ : 0 ≤ Δ)
    {D : Divisor X} (hDc : D.IsCartier) (hD : (Divisor.toQDivisor D).IsRelativelyNef sX f)
    {a : ℚ} (ha : 0 < a)
    (hnef : (a • Divisor.toQDivisor D - Divisor.toQDivisor K - Δ).IsRelativelyNef sX f)
    (hbig : (a • Divisor.toQDivisor D - Divisor.toQDivisor K - Δ).IsRelativelyBig f) :
    ∃ b₀ : ℕ, ∀ b : ℕ, b₀ ≤ b → MMP.Fourfold.IsRelativelyFreeDivisor f ((b : ℤ) • D) := by
  haveI := hf.isAlgClosed
  haveI := hf.charZero
  obtain ⟨H, hH, G, hGc, ⟨eG⟩, E', hE'0, hE'q, hklt', hA⟩ :=
    exists_isAmple_smul_add_pullback_sub_of_isKltPair hf hklt hΔ hDc hD ha hnef hbig
  haveI hXp : MMP.Mori.IsProjectiveVariety k sX := hf.isProjectiveVariety_source
  haveI hYp : MMP.Mori.IsProjectiveVariety k sY := hf.isProjectiveVariety_target
  haveI : AlgebraicGeometry.IsVariety k sX := hXp.toIsVariety
  haveI : AlgebraicGeometry.IsVariety k sY := hYp.toIsVariety
  have hcomp : f ≫ sY = sX := hf.comp_eq
  set L := MMP.CartierDivisor.sheaf H
  have hA₁ : (a • Divisor.toQDivisor (D + G) - Divisor.toQDivisor K - (Δ + E')).IsAmple := by
    rwa [← sub_sub]
  obtain ⟨m, hm⟩ := exists_forall_ge_isNef_add_nsmul_pullback hf hklt' (add_nonneg hΔ hE'0) H hH
    hGc ⟨eG⟩ (hDc.add hGc) (isRelativelyNef_toQDivisor_add_of_iso_pullback hcomp L hGc eG hDc hD)
    ha hA₁
  set D₂ := D + G + m • G with hD₂
  have hD₂c : D₂.IsCartier := (hDc.add hGc).add (hGc.nsmul m)
  have hN := isNef_smul (isNef_toQDivisor_of_iso_pullback hcomp L hH hGc eG) (q := a * m)
    (by positivity)
  have hA₂ : (a • Divisor.toQDivisor D₂ - Divisor.toQDivisor K - (Δ + E')).IsAmple := by
    have hBeq : a • Divisor.toQDivisor D₂ - Divisor.toQDivisor K - (Δ + E') =
        (a • Divisor.toQDivisor (D + G) - Divisor.toQDivisor K - (Δ + E')) +
          ∑ _i ∈ ({()} : Finset Unit), (a * m) • Divisor.toQDivisor G := by
      rw [Finset.sum_singleton, hD₂, map_add (Divisor.toQDivisor) (D + G), map_nsmul,
        ← Nat.cast_smul_eq_nsmul ℚ, smul_add, smul_smul]
      abel
    rw [hBeq]
    exact QDivisor.isAmple_of_numericallyEquivalent_add_sum_of_isNef sX {()} _ hA₁
      (fun _ _ => hN) (QDivisor.NumericallyEquivalent.refl
      ((QDivisor.isNef_and_isBig_of_isAmple sX hA₁).1.isQCartier.add (by simpa using hN.1)))
  obtain ⟨hA₂n, hA₂b⟩ := QDivisor.isNef_and_isBig_of_isAmple sX hA₂
  have hdatum : IsBasepointFreeDatum sX n K (Δ + E') D₂ a :=
    { isProperVariety := (MMP.Mori.isProperVariety_iff k sX).mpr ⟨inferInstance,
        (IsProjectiveMorphism.isProjective
          (AlgebraicGeometry.IsProjectiveVariety.isProjective (k := k) (f := sX))).isProper⟩
      isKltPair := hklt'
      isEffective := DivisorWithCoeffs.isEffective_iff_nonneg.mpr (add_nonneg hΔ hE'0)
      isCartier := hD₂c
      isNef := (QDivisor.isNef_toQDivisor_iff D₂ hD₂c).mp (hm m le_rfl)
      pos := ha
      isQCartier_sub := hA₂n.1
      isNef_sub := hA₂n
      isBig_sub := hA₂b }
  obtain ⟨b₀, hb₀⟩ := hdatum.exists_isBasepointFree_nsmul
  refine ⟨b₀, fun b hb => ?_⟩
  have heq : b • D₂ = (b : ℤ) • D + ((b : ℤ) * (1 + m)) • G := by
    simp only [hD₂, ← natCast_zsmul]
    module
  refine isRelativelyFreeDivisor_of_isBasepointFree_add f (heq ▸ hb₀ b hb) fun y => ?_
  obtain ⟨U, hyU, χ, hχ⟩ :=
    MMP.Fourfold.exists_isLocalEquation_preimage_of_iso_pullback f L eG y
  refine ⟨U, hyU, χ ^ ((b : ℤ) * (1 + m)), fun P hP => ?_⟩
  rw [DivisorWithCoeffs.coeff_smul, hχ P hP, PrimeDivisor.ord_zpow]

end MMP.Mori

end
