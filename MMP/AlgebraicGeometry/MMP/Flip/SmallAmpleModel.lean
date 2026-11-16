module
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
public import MMP.AlgebraicGeometry.MMP.BasepointFree.ProofData
public import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
public import MMP.AlgebraicGeometry.Resolution.SncPairStratumBlowup

/-!
# Relative curve classes, strip base loci, and flips as small ample models

This file collects three groups of results used in the cone theorem and the theory of flips.

*Relative curve classes.* Let `f : X ⟶ Y` be a morphism of `k`-schemes. A relative 1-cycle is
numerically trivial in `N₁(X/Y)` exactly when it is numerically trivial in `N₁(X)`, so there is a
unique natural map `ι : N₁(X/Y) → N₁(X)`, `[Z] ↦ [Z]`, and it is injective. A curve contracted by
`f` has a closed point as image, so its push-forward vanishes; hence `ι(N₁(X/Y)) ⊆ ker f_*`.

*Strip base loci.* For a `(p, q)`-adapted resolution `(f; F_•; a_•; p_•; r_•)` of a rationality
datum `(X, Δ, a, H)`, the base locus `L(p, q) = Bs|pH + qa(K_X + Δ)|` is the image under `f` of the
union of those `F_j` whose multiplicity `r_j` in the fixed part of `|f^*(pH + qa(K_X + Δ))|` is
positive. The divisor `M = pH + qa(K_X + Δ)` is Cartier, so for every nonzero section `σ` the
support of `f^*(σ)₀` is `f⁻¹ Supp (σ)₀`; the fixed-part condition then compares both sides.

*Flips.* A `(K + D)`-flip `f⁺ : X⁺ ⟶ Y` of a flipping contraction `f : X ⟶ Y` is proper and
carries an `f⁺`-ample Cartier divisor, hence is projective. For `r > 0` with `rD` integral, `f⁺` is
moreover a small ample model of `f_*(rK_X + rD)`: it is birational from a normal variety, `Ex(f⁺)`
has codimension at least two, and `(f⁺)⁻¹_* f_* (rK_X + rD) = r(K_{X⁺} + D⁺)` is `ℚ`-Cartier and
has an `f⁺`-ample Cartier multiple.

## Main results

* `MMP.Mori.existsUnique_isNaturalRelativeMap_and_injective`: there is a unique natural map
  `N₁(X/Y) → N₁(X)`, and every natural map is injective.
* `MMP.Mori.range_relativeToAbsolute_le_ker_pushforward`: `ι(N₁(X/Y)) ⊆ ker f_*`.
* `MMP.Mori.IsStripAdaptedResolution.stripBaseLocus_eq_image`: `L(p, q) = f(⋃_{r_j > 0} F_j)`.
* `MMP.Mori.IsFlip.isProjective`: a `(K + D)`-flip `f⁺ : X⁺ ⟶ Y` is projective.
* `MMP.Mori.IsFlip.isSmallAmpleModel`: a flip is a small ample model of `f_*(rK_X + rD)` over `Y`.

## Implementation notes

"Projective" is `AlgebraicGeometry.IsProjective` (EGA II 5.5: a closed immersion into `ℙ(ℰ)` for
some quasi-coherent `𝒪_Y`-module `ℰ` of finite type), not an embedding into a fixed `ℙⁿ_Y`: the
latter needs `Y` quasi-projective, which the base of a flip need not be.

The integral divisor `rD` is a Weil divisor `B` on `X` with `B = r • D` as `ℚ`-divisors; the
divisor `rK_X + rD` is then `r • K + B`, and its birational transform to `X⁺` is
`MMP.Mori.flipTransform f f⁺ (r • K + B)`. The ampleness of `r(K_{X⁺} + D⁺)` uses that a positive
multiple of an `f`-ample Cartier divisor is `f`-ample: `𝒪_X(nL) ≅ 𝒪_X(L)^{⊗ n}`, tensor powers
commute with restriction to opens, and an invertible sheaf is ample if and only if a positive
tensor power is.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Proposition
  3.27(3), proof of Theorem 3.5 (Step 8), 3.31, 3.33, Lemma 6.2 and Corollary 6.4
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Mori

/-! ### Relative curve classes -/

section RelativeCurves

/-- A natural map `N₁(X/Y) → N₁(X)` is injective. -/
theorem IsNaturalRelativeMap.injective {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {f : X ⟶ Y}
    {ι : RelativeNumericalCurveClasses sX f →ₗ[ℝ] NumericalCurveClasses sX}
    (h : IsNaturalRelativeMap sX f ι) : Function.Injective ι := by
  refine (injective_iff_map_eq_zero ι).mpr fun z hz => ?_
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX f z
  rw [h Z] at hz
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    ((Submodule.Quotient.mk_eq_zero (OneCycle.numericallyTrivial sX)).mp hz)

/-- There is exactly one natural linear map `ι : N₁(X/Y) → N₁(X)` (one sending the class of each
relative 1-cycle to its absolute class), and any such map is injective. -/
@[mmp "lem_km3b_relative_curve_space_injects"]
theorem existsUnique_isNaturalRelativeMap_and_injective {k : Type u} [Field k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (f : X ⟶ Y) :
    (∃! ι : RelativeNumericalCurveClasses sX f →ₗ[ℝ] NumericalCurveClasses sX,
        IsNaturalRelativeMap sX f ι) ∧
      ∀ ι : RelativeNumericalCurveClasses sX f →ₗ[ℝ] NumericalCurveClasses sX,
        IsNaturalRelativeMap sX f ι → Function.Injective ι := by
  refine ⟨⟨relativeToAbsolute sX f, isNaturalRelativeMap_relativeToAbsolute sX f,
    fun _ h => h.unique (isNaturalRelativeMap_relativeToAbsolute sX f)⟩, fun _ h => h.injective⟩

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {sY : Y ⟶ Spec (.of k)}

/-- A closed point is not the generic point of a curve: its closure is zero-dimensional. -/
private theorem not_isProperCurve_of_isClosed_singleton {y : Y} (hy : IsClosed ({y} : Set Y)) :
    ¬ IsProperCurve sY y := fun h => by
  have : Subsingleton (curveSubschemeAt y) := ⟨fun a b =>
    (curveSubschemeAtι y).isEmbedding.injective <| by
      have ha := hy.closure_eq ▸ range_curveSubschemeAtι y ▸
        Set.mem_range_self (f := curveSubschemeAtι y) a
      have hb := hy.closure_eq ▸ range_curveSubschemeAtι y ▸
        Set.mem_range_self (f := curveSubschemeAtι y) b
      exact ha.trans hb.symm⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology (curveSubschemeAt y)
  rw [h.dim_eq] at h0
  exact absurd h0 (by decide)

/-- The image of a curve contracted by `f` is a closed point. -/
private theorem isClosed_singleton_map_point_of_isContractedBy [IsSeparated sY]
    [LocallyOfFiniteType sY] (f : X ⟶ Y) (hf : f ≫ sY = sX) {C : ProperCurve sX}
    (hC : C.IsContractedBy f) : IsClosed ({f C.point} : Set Y) := by
  refine closure_eq_iff_isClosed.mp ?_
  rw [← C.range_comp f hf]
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨c, rfl⟩
    exact hC _ (C.range_ι ▸ ⟨c, rfl⟩)
  · rintro _ rfl
    exact ⟨genericPoint C.scheme, by rw [Scheme.Hom.comp_apply, C.ι_genericPoint]⟩

/-- The image of the natural map `ι : N₁(X/Y) → N₁(X)` is contained in the kernel of the
push-forward `f_* : N₁(X) → N₁(Y)`. -/
@[mmp "lem_km3b_relative_curves_in_kernel"]
theorem range_relativeToAbsolute_le_ker_pushforward [IsSeparated sY] [LocallyOfFiniteType sY]
    (f : X ⟶ Y) (hf : f ≫ sY = sX) :
    LinearMap.range (relativeToAbsolute sX f) ≤
      LinearMap.ker (NumericalCurveClasses.pushforward f hf) := by
  rintro _ ⟨z, rfl⟩
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX f z
  have hZ : OneCycle.pushforward ℝ sX sY f (Z : OneCycle ℝ sX) = 0 := by
    rw [OneCycle.pushforward, Finsupp.linearCombination_apply]
    refine Finset.sum_eq_zero fun C hC => ?_
    simp [cyclePushforwardOfPoint, not_isProperCurve_of_isClosed_singleton
      (isClosed_singleton_map_point_of_isContractedBy f hf (Z.2 hC))]
  change OneCycle.numericalClass sY (OneCycle.pushforward ℝ sX sY f (Z : OneCycle ℝ sX)) = 0
  rw [hZ, map_zero]

end RelativeCurves

/-! ### The strip base locus -/

section StripBaseLocus

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- The round-down of an integral divisor read as a `ℚ`-divisor is the divisor itself. -/
private theorem roundDown_toQDivisor {X : Scheme.{u}} (D : Divisor X) :
    (Divisor.toQDivisor D).roundDown = D := by
  ext E
  simp [DivisorWithCoeffs.coeff_roundDown, Divisor.coeff_toQDivisor]

/-- The coefficient of `F i` in `∑ j, r_j F_j` is `r_i`, for an injective family `F`. -/
private theorem coeff_sum_single {Y : Scheme.{u}} {s : ℕ} {F : Fin s → PrimeDivisor Y}
    (hF : Function.Injective F) (r : Fin s → ℤ) (i : Fin s) :
    DivisorWithCoeffs.coeff (∑ j, Finsupp.single (F j) (r j) : Divisor Y) (F i) = r i := by
  rw [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply,
    Finset.sum_eq_single i (fun j _ hj => Finsupp.single_eq_of_ne' (hF.ne hj)) (by simp)]
  simp

/-- A prime divisor with nonzero coefficient in `∑ j, r_j F_j` is some `F_j` with `r_j ≠ 0`. -/
private theorem exists_eq_of_coeff_sum_single_ne_zero {Y : Scheme.{u}} {s : ℕ}
    {F : Fin s → PrimeDivisor Y} (r : Fin s → ℤ) {E : PrimeDivisor Y}
    (hE : DivisorWithCoeffs.coeff (∑ j, Finsupp.single (F j) (r j) : Divisor Y) E ≠ 0) :
    ∃ j, F j = E ∧ r j ≠ 0 := by
  rw [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply] at hE
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hE
  by_cases h : F j = E
  · subst h
    exact ⟨j, rfl, by simpa using hj⟩
  · exact absurd (Finsupp.single_eq_of_ne' h) hj

/-- **`Supp f^*(σ)₀ = f⁻¹ Supp (σ)₀`**: for a Cartier divisor `M` and a nonzero section `σ` of
`𝒪(M)`, the support of the pull-back of the divisor of zeros `(σ)₀` is the preimage of its
support. -/
private theorem supp_pullback_zeroDivisor {X Y : Scheme.{u}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X}
    {M : Divisor X} (hM : M.IsCartier) {σ : M.divisorialSubmodule ⊤} {hσ : σ ≠ 0} {hB}
    {Z' : Divisor Y} (hpb : (M.zeroDivisor σ hσ).IsPullback f hB Z') :
    (Z'.supp : Set Y) = f.base ⁻¹' (M.zeroDivisor σ hσ).supp :=
  MMP.Flips.supp_eq_preimage_supp_of_isPullback
    ((Divisor.isCartier_principalDivisor _).add hM) (Divisor.zeroDivisor_nonneg _ σ hσ) hpb

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]

/-- For a `(p, q)`-adapted resolution `(f; F_•; a_•; p_•; r_•)` of a rationality datum
`(X, Δ, a, H)`, the strip base locus `L(p, q)` is `f(⋃_{r_j > 0} F_j)`. -/
@[mmp "lem_km3b_strip_fixed_part_image"]
theorem IsStripAdaptedResolution.stripBaseLocus_eq_image {n : ℕ} {K : Divisor X}
    {Δ : QDivisor X} {a : ℤ} {H : Divisor X} {p q : ℤ} {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X} {s : ℕ} {F : Fin s → PrimeDivisor Y}
    {aj pj : Fin s → ℚ} {rj : Fin s → ℕ}
    (h : IsStripAdaptedResolution sX n K Δ a H p q f F aj pj rj) :
    (stripBaseLocus K Δ a H p q : Set X) = f '' ⋃ (j : Fin s) (_ : 0 < rj j), (F j).support := by
  -- `M = pH + qa(K_X + Δ)` is Cartier
  have hM : (stripDivisor K Δ a H p q).IsCartier := by
    obtain ⟨D', hD', hD'c⟩ := h.isCartierDivisor
    rw [stripDivisor, ← hD', roundDown_toQDivisor]
    exact (h.isCartier_H.zsmul p).add (hD'c.zsmul q)
  have : IsDominant f := h.isLogResolution.isBirationalMorphism.isDominant
  have : IsProper f := h.isLogResolution.isProper
  ext x
  simp only [stripBaseLocus, Divisor.mem_baseLocus_iff, Set.mem_image, Set.mem_iUnion]
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := f.surjective x
    obtain ⟨σ, hσ, hB, Z', hpb, hy⟩ := h.exists_notMem_supp y
    obtain ⟨E, hE, hyE⟩ := DivisorWithCoeffs.mem_supp_iff.mp
      (show y ∈ (Z'.supp : Set Y) from supp_pullback_zeroDivisor hM hpb ▸ hx σ hσ)
    have hR : DivisorWithCoeffs.coeff
        (∑ j, Finsupp.single (F j) (rj j : ℤ) : Divisor Y) E ≠ 0 := fun h0 =>
      hy (DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, by simpa [h0] using hE, hyE⟩)
    obtain ⟨j, rfl, hj⟩ := exists_eq_of_coeff_sum_single_ne_zero _ hR
    exact ⟨y, ⟨j, by omega, hyE⟩, rfl⟩
  · rintro ⟨y, ⟨j, hj, hyj⟩, rfl⟩ σ hσ
    obtain ⟨hB, Z', hpb, hle⟩ := h.le_zeroDivisor σ hσ
    have hcoeff := hle (F j)
    rw [← DivisorWithCoeffs.coeff_apply, ← DivisorWithCoeffs.coeff_apply,
      coeff_sum_single h.injective] at hcoeff
    have : y ∈ (Z'.supp : Set Y) :=
      DivisorWithCoeffs.mem_supp_iff.mpr ⟨F j, by omega, hyj⟩
    rwa [supp_pullback_zeroDivisor hM hpb] at this

end StripBaseLocus

/-! ### Flips -/

section Flips

open RingedSpaceModuleAdjunction

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- Regarding a divisor as a `ℚ`-divisor commutes with pushing prime divisors forward. -/
private theorem toQDivisor_mapPrimeDivisors {X Y : Scheme}
    (φ : PrimeDivisor X → Option (PrimeDivisor Y)) (D : Divisor X) :
    Divisor.toQDivisor (DivisorWithCoeffs.mapPrimeDivisors φ D) =
      DivisorWithCoeffs.mapPrimeDivisors φ (Divisor.toQDivisor D) := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single E n =>
    have h1 : ∀ {Z : Scheme} (F : PrimeDivisor Z) (m : ℤ),
        Divisor.toQDivisor (Finsupp.single F m) = Finsupp.single F (m : ℚ) := fun F m => by
      simp only [Divisor.toQDivisor, DivisorWithCoeffs.mapCoeffsAddMonoidHom_apply,
        DivisorWithCoeffs.mapCoeffs, Finsupp.mapRange_single, Int.coe_castAddHom]
    rw [h1, DivisorWithCoeffs.mapPrimeDivisors_single, DivisorWithCoeffs.mapPrimeDivisors_single]
    cases φ E <;> simp [h1]

/-- Regarding a divisor as a `ℚ`-divisor commutes with the birational transform of a flip. -/
private theorem toQDivisor_flipTransform {X Y X' : Scheme} (f : X ⟶ Y) (fp : X' ⟶ Y)
    (D : Divisor X) :
    Divisor.toQDivisor (flipTransform f fp D) = flipTransform f fp (Divisor.toQDivisor D) := by
  simp only [flipTransform, AddMonoidHom.comp_apply, inverseTransformDivisor,
    RationalMap.transformDivisor, toQDivisor_mapPrimeDivisors]

/-- `𝒪_X(nL) ≅ 𝒪_X(L)^{⊗ n}` for a Cartier divisor `L` and `n ≥ 1`. -/
private theorem nonempty_divisorialSheaf_nsmul_iso {X : Scheme} [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {L : Divisor X} (hL : L.IsCartier) (n : ℕ) (hn : 1 ≤ n) :
    haveI := hL.isInvertibleModule_divisorialSheaf
    Nonempty ((n • L).divisorialSheaf ≅
      Stacks.Ample.tensorPowModule X L.divisorialSheaf (n : ℤ)) := by
  haveI := hL.isInvertibleModule_divisorialSheaf
  induction n, hn using Nat.le_induction with
  | base =>
    exact ⟨eqToIso (congrArg Divisor.divisorialSheaf (one_nsmul L)) ≪≫
      (Stacks.Ample.tensorPowModuleOneIso X _).symm⟩
  | succ n hn ih =>
    obtain ⟨e⟩ := ih
    refine ⟨eqToIso (congrArg Divisor.divisorialSheaf (succ_nsmul L n)) ≪≫
      ((hL.nsmul n).divisorialSheafTensorIso hL).symm ≪≫ ?_ ≪≫
      Stacks.Ample.tensorPowModuleAddIso X _ (n : ℤ) 1 ≪≫
      Stacks.RelativeVeryAmple.tensorPowModuleCongr X _ (by push_cast; rfl)⟩
    exact ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso e).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).obj _).mapIso
        (Stacks.Ample.tensorPowModuleOneIso X _).symm

/-- A positive multiple of an `f`-ample Cartier divisor is `f`-ample. -/
private theorem isRelativelyAmple_nsmul {X Y : Scheme} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {f : X ⟶ Y} {L : Divisor X} (hL : L.IsCartier)
    (h : L.IsRelativelyAmple f hL) (n : ℕ) (hn : 0 < n) :
    (n • L).IsRelativelyAmple f (hL.nsmul n) := by
  haveI := hL.isInvertibleModule_divisorialSheaf
  haveI := (hL.nsmul n).isInvertibleModule_divisorialSheaf
  intro y
  obtain ⟨V, hV, hyV, hA⟩ := h y
  refine ⟨V, hV, hyV, ?_⟩
  obtain ⟨e0⟩ := nonempty_divisorialSheaf_nsmul_iso hL n hn
  haveI := Stacks.Ample.isInvertibleModule_tensorPowModule (f ⁻¹ᵁ V).toScheme
    ((modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj L.divisorialSheaf) (n : ℤ)
  let e := (modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).mapIso e0 ≪≫
    Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso (f ⁻¹ᵁ V).ι _ n
  rw [Stacks.RelativeVeryAmple.isAmple_congr _ _ e]
  exact (Stacks.AmplePositivePower.isAmple_iff_isAmple_tensorPowModule _ n hn).1 hA

variable {k : Type u} [Field k] {X Y X' : Scheme.{u}}
  {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
  [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']

/-- **A flip is projective over the base.** If `f⁺ : X⁺ ⟶ Y` is a `(K + D)`-flip of the
`(K + D)`-flipping contraction `f : X ⟶ Y`, then `f⁺` is a projective morphism. -/
@[mmp "lem_km3c_flip_is_projective_over_base"]
theorem IsFlip.isProjective {K : Divisor X} {D : QDivisor X} {f : X ⟶ Y}
    {fp : X' ⟶ Y} (h : IsFlip sX sY sX' K D f fp) : AlgebraicGeometry.IsProjective fp := by
  obtain ⟨_, _, L, hL, -, hamp⟩ := h.hasRelativelyAmpleMultiple
  have : IsVariety k sX' := h.isNormalVariety.1
  have : IsVariety k sY := h.isFlippingContraction.isNormalVariety_target.1
  have : IsProper fp := h.isProper
  exact MMP.isProjective_of_isProper_of_divisor_isRelativelyAmple k sX' sY fp h.comp_eq L hL hamp

/-- A `(K + D)`-flip `f⁺ : X⁺ ⟶ Y` of a flipping contraction `f : X ⟶ Y` is a small ample model:
for `r > 0` and a Weil divisor `B = rD`, `f⁺` is a projective birational morphism from a normal
variety with `Ex(f⁺)` of codimension at least two, and `(f⁺)⁻¹_* f_* (rK + B)` is `ℚ`-Cartier
with an `f⁺`-ample Cartier multiple. -/
@[mmp "lem_km3c_flip_is_small_ample_model"]
theorem IsFlip.isSmallAmpleModel {K : Divisor X} {D : QDivisor X} {f : X ⟶ Y}
    {fp : X' ⟶ Y} (h : IsFlip sX sY sX' K D f fp) {r : ℕ} (hr : 0 < r) {B : Divisor X}
    (hB : Divisor.toQDivisor B = (r : ℤ) • D) :
    AlgebraicGeometry.IsProjective fp ∧ IsBirationalMorphism fp ∧ IsNormalVariety k sX' ∧
      2 ≤ closedsCodimension (exceptionalSet fp) ∧
      (Divisor.toQDivisor (flipTransform f fp (r • K + B))).IsQCartier ∧
      (Divisor.toQDivisor (flipTransform f fp (r • K + B))).HasRelativelyAmpleMultiple fp := by
  set E := Divisor.toQDivisor (flipTransform f fp K) + flipTransform f fp D with hE
  have hT : Divisor.toQDivisor (flipTransform f fp (r • K + B)) = (r : ℤ) • E := by
    rw [toQDivisor_flipTransform, map_add, map_add, hB, map_nsmul, map_nsmul, map_zsmul, hE,
      smul_add, ← toQDivisor_flipTransform]
    simp only [natCast_zsmul]
  rw [hT]
  refine ⟨h.isProjective, h.isBirationalMorphism, h.isNormalVariety, h.two_le_codimension,
    ?_, ?_⟩
  · obtain ⟨m, hm, M, hM, hMC⟩ := h.isQCartier
    refine ⟨m, hm, (r : ℤ) • M, ?_, hMC.zsmul _⟩
    rw [map_zsmul, hM, smul_comm]
  · obtain ⟨m, hm, L, hL, hLE, hamp⟩ := h.hasRelativelyAmpleMultiple
    refine ⟨m, hm, r • L, hL.nsmul r, ?_, isRelativelyAmple_nsmul hL hamp r hr⟩
    rw [map_nsmul, hLE, ← natCast_zsmul, smul_comm]

end Flips

end MMP.Mori
