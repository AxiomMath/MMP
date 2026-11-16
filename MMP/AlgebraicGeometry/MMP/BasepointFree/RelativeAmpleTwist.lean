module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
import MMP.AlgebraicGeometry.Positivity.RelativeBigDecomposition
import MMP.AlgebraicGeometry.Positivity.Kleiman.RelativeCartier
import MMP.AlgebraicGeometry.Singularities.DltKltPerturbation
import MMP.AlgebraicGeometry.Morphisms.ValuativeCentre
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
import MMP.AlgebraicGeometry.Intersection.PairingSeparation
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive
import MMP.AlgebraicGeometry.Positivity.SerreAmpleCartier
import MMP.AlgebraicGeometry.Singularities.LogResolution.ReducedUnion
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
public import MMP.AlgebraicGeometry.Morphisms.HProjective
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafMul
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafSections

/-!
# Making `aD - K_X - Δ` ample by a pull-back twist and a small boundary

Let `(X, Δ)` be a klt pair with `Δ` effective and `f : X ⟶ Y` a morphism of projective varieties
over an algebraically closed field `k` of characteristic zero. Let `D` be an `f`-nef Cartier
divisor on `X` and `a > 0` rational with `aD - K_X - Δ` `f`-nef and `f`-big. Then there are an
ample Cartier divisor `H` on `Y` and an effective `ℚ`-Cartier `ℚ`-divisor `E'` on `X` such that
`(X, Δ + E')` is klt and `a(D + f^*H) - K_X - Δ - E'` is ample.

Writing `B = aD - K_X - Δ`, a multiple of `B` decomposes as an `f`-ample plus an effective
Cartier divisor `E`; for small `δ > 0` the divisor `B - δE` is positive on `NE̅(X/Y) \ 0`, hence
`f`-ample by the relative Kleiman criterion, and `(X, Δ + δE)` stays klt. Adding a large multiple
of the pull-back of an ample divisor on `Y` makes it ample.

## Main results

* `MMP.Mori.exists_isAmple_smul_add_pullback_sub_of_isKltPair`: the statement above.

## Implementation notes

The pull-back `f^*H` enters only through its invertible sheaf: it is a Cartier (Weil) divisor
`G` on `X` with `𝒪_X(G) ≅ f^*𝒪_Y(H)`. Such a `G` is determined up to linear equivalence, which
does not change ampleness, and it exists without moving `H` off the image of the generic point
of `X`. The variety `Y` is not assumed normal, so `H` is a Cartier divisor in the sense of
`Scheme.CartierDivisor`, ample when its invertible sheaf is.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.26
-/

public section

open AlgebraicGeometry CategoryTheory MonoidalCategory

namespace MMP.Mori

/-! ### Comparison of divisorial and Cartier sheaves -/

section Comparison

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]

/-- On an integral Noetherian scheme every Cartier divisor has a Weil divisor. -/
private theorem exists_isWeilDivisorOfCartier (A : X.CartierDivisor) :
    ∃ w : Divisor X, MMP.Intersection.IsWeilDivisorOfCartier A w := by
  letI : IsNoetherian X := ⟨⟩
  have h0 : ∀ s ∈ MMP.Intersection.cartierSupport A, Order.coheight s = 0 → False := by
    intro s hs h0
    have : Ring.KrullDimLE 0 (X.presheaf.stalk s) := krullDimLE_of_coheight_le (by simp [h0])
    have : IsArtinianRing (X.presheaf.stalk s) := isArtinianRing_iff_krullDimLE_zero.mpr this
    exact MMP.Intersection.notMem_cartierSupport_of_isArtinianRing A s hs
  have hfin := finite_setOf_genericPoint_mem
    (MMP.Intersection.isClosed_cartierSupport A) h0
  refine ⟨Finsupp.ofSupportFinite (fun P => MMP.Intersection.primeDivisorOrder P A)
    (hfin.subset fun P hP => ?_), fun P => ?_⟩
  · by_contra h
    refine hP ((MMP.Intersection.isOrderAlong_primeDivisorOrder A P).eq_zero_of_not_subset
      fun h' => h ?_)
    show (MMP.Intersection.primeDivisorSubvariety P).genericPoint ∈
      MMP.Intersection.cartierSupport A
    exact MMP.Intersection.genericPoint_mem_cartierSupport_iff.mpr h'
  · rw [DivisorWithCoeffs.coeff_apply, Finsupp.ofSupportFinite_coe]
    exact MMP.Intersection.isOrderAlong_primeDivisorOrder A P

/-- Every Cartier divisor has a Cartier Weil divisor with the same sheaf. -/
private theorem exists_divisor_iso_sheaf (A : X.CartierDivisor) :
    ∃ w : Divisor X, w.IsCartier ∧
      Nonempty (w.divisorialSheaf ≅ MMP.CartierDivisor.sheaf A) := by
  obtain ⟨w, hw⟩ := exists_isWeilDivisorOfCartier A
  obtain ⟨e⟩ := hw.nonempty_sheaf_iso_divisorialSheaf
  exact ⟨w, hw.isCartier, ⟨e.symm⟩⟩

/-- Every Cartier Weil divisor has a Cartier divisor with the same sheaf. -/
private theorem exists_sheaf_iso_divisorialSheaf {D : Divisor X} (hD : D.IsCartier) :
    ∃ C : X.CartierDivisor,
      Nonempty (D.divisorialSheaf ≅ MMP.CartierDivisor.sheaf C) := by
  haveI := hD.isInvertibleModule_divisorialSheaf
  exact MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf D.divisorialSheaf

/-- The comparison of sheaves is additive. -/
private theorem nonempty_divisorialSheaf_add_iso {W₁ W₂ : Divisor X} (h₁ : W₁.IsCartier)
    (h₂ : W₂.IsCartier) {C₁ C₂ : X.CartierDivisor}
    (e₁ : W₁.divisorialSheaf ≅ MMP.CartierDivisor.sheaf C₁)
    (e₂ : W₂.divisorialSheaf ≅ MMP.CartierDivisor.sheaf C₂) :
    Nonempty ((W₁ + W₂).divisorialSheaf ≅ MMP.CartierDivisor.sheaf (C₁ + C₂)) :=
  ⟨(h₁.divisorialSheafTensorIso h₂).symm ≪≫ MonoidalCategory.tensorIso e₁ e₂ ≪≫
    MMP.CartierDivisorSheaf.sheafMulIso C₁ C₂⟩

/-- The comparison of sheaves is compatible with positive multiples. -/
private theorem nonempty_divisorialSheaf_nsmul_iso {W : Divisor X} (hW : W.IsCartier)
    {C : X.CartierDivisor} (e : W.divisorialSheaf ≅ MMP.CartierDivisor.sheaf C)
    (n : ℕ) (hn : 1 ≤ n) :
    Nonempty ((n • W).divisorialSheaf ≅ MMP.CartierDivisor.sheaf (n • C)) := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [one_nsmul, one_nsmul]
    exact ⟨e⟩
  | succ n hn ih =>
    obtain ⟨ie⟩ := ih
    rw [succ_nsmul, succ_nsmul]
    exact nonempty_divisorialSheaf_add_iso (hW.nsmul n) hW ie e

end Comparison

/-! ### Relative bigness and the decomposition `mD₀ ∼ A + E` -/

section Decomposition

/-- The generic rank only depends on the isomorphism class of the module. -/
private theorem relativeGenericRank_congr {X Y : Scheme.{0}} (f : X ⟶ Y) [IrreducibleSpace X]
    {F G : X.Modules} (e : F ≅ G) : relativeGenericRank f F = relativeGenericRank f G :=
  Scheme.Modules.fiberRank_eq_of_iso ((Scheme.Modules.pushforward f).mapIso e) _

/-- Bigness of a Cartier Weil divisor `D₀` transfers to a Cartier divisor `C` with
`𝒪_X(D₀) ≅ 𝒪_X(C)`. -/
private theorem isRelativelyBigCartier_of_isRelativelyBig {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (f : X ⟶ Y) {D₀ : Divisor X}
    (hD₀ : D₀.IsCartier) {C : X.CartierDivisor}
    (e : D₀.divisorialSheaf ≅ MMP.CartierDivisor.sheaf C)
    (hb : D₀.IsRelativelyBig f) : IsRelativelyBigCartier f C := by
  obtain ⟨a, b, ha, hb', c, hc, k₀, hk⟩ := hb
  refine ⟨a, b, ha, hb', c, hc, max k₀ 1, fun m hm => ?_⟩
  have hm1 : 1 ≤ m := le_trans (le_max_right _ _) hm
  have hk0 : k₀ ≤ m := le_trans (le_max_left _ _) hm
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = (n : ℤ) := ⟨m.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  obtain ⟨ie⟩ := nonempty_divisorialSheaf_nsmul_iso hD₀ e n (by omega)
  have h := hk _ hk0
  rw [natCast_zsmul] at h ⊢
  rwa [← relativeGenericRank_congr f ie]

/-- Linearly equivalent Cartier divisors have isomorphic sheaves. -/
private theorem nonempty_sheaf_iso_of_linearlyEquivalent {X : Scheme.{0}}
    {B B' : X.CartierDivisor} (h : MMP.Intersection.LinearlyEquivalent B B') :
    Nonempty (MMP.CartierDivisor.sheaf B ≅
      MMP.CartierDivisor.sheaf B') := by
  obtain ⟨c, hc⟩ := (MMP.Intersection.mem_principalSubgroup_iff).1 h
  obtain rfl : B = B' + MMP.Intersection.principalDivisor c := by
    rw [hc]
    abel
  exact ⟨(MMP.CartierDivisor.sheafAddPrincipalIso B' c).symm⟩

/-- **The relative Kodaira decomposition of an `f`-big Cartier divisor**, on the level of
sheaves: some multiple `m D₀` has the sheaf of `A + E` with `A` an `f`-ample Cartier divisor and
`E` the Cartier divisor of an effective Cartier Weil divisor `E_w`. -/
private theorem exists_nsmul_iso_ample_add_effective {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    [IsProjectiveVariety k sX] [IsProjectiveVariety k sY] (f : X ⟶ Y)
    (hf : f ≫ sY = sX) {D₀ : Divisor X} (hD₀ : D₀.IsCartier) (hb : D₀.IsRelativelyBig f) :
    ∃ m : ℕ, 0 < m ∧ ∃ A E : X.CartierDivisor,
      IsRelativelyAmple f (MMP.CartierDivisor.sheaf A) ∧
      Nonempty ((m • D₀).divisorialSheaf ≅ MMP.CartierDivisor.sheaf (A + E)) ∧
      ∃ Ew : Divisor X, Ew.IsCartier ∧ 0 ≤ Ew ∧
        Nonempty (Ew.divisorialSheaf ≅ MMP.CartierDivisor.sheaf E) := by
  obtain ⟨Ec, ⟨e⟩⟩ := exists_sheaf_iso_divisorialSheaf hD₀
  obtain ⟨m, hm, A, E, hA, hE, hlin⟩ :=
    (isRelativelyBigCartier_iff_exists_linearlyEquivalent_add sX sY f hf Ec).1
      (isRelativelyBigCartier_of_isRelativelyBig f hD₀ e hb)
  obtain ⟨ie⟩ := nonempty_divisorialSheaf_nsmul_iso hD₀ e m hm
  obtain ⟨eL⟩ := nonempty_sheaf_iso_of_linearlyEquivalent hlin
  obtain ⟨w, hw⟩ := exists_isWeilDivisorOfCartier E
  obtain ⟨ew⟩ := hw.nonempty_sheaf_iso_divisorialSheaf
  exact ⟨m, hm, A, E, hA, ⟨ie ≪≫ eL⟩, w, hw.isCartier,
    fun P => (hw P).nonneg_of_isEffective hE, ⟨ew.symm⟩⟩

end Decomposition

/-! ### Degree forms on `N₁(X/Y)` -/

section Degree

variable {k : Type} [Field k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {f : X ⟶ Y}

/-- `(z · 1 · E)` is the degree of `𝒪_X(E)` on `z`. -/
private theorem intersectionNumber_ofCartier_eq_degree (E : X.CartierDivisor) :
    RelativeNumericalCurveClasses.intersectionNumber (sX := sX) (f := f)
        (KCartierDivisor.ofCartier ℝ E) =
      RelativeNumericalCurveClasses.degree sX f (MMP.CartierDivisor.sheaf E) :=
  Submodule.linearMap_qext _
    (LinearMap.ext fun Z => OneCycle.intersectionNumber_ofCartier (Z : OneCycle ℝ sX) E)

/-- `deg_C 𝒪_X(E + E') = deg_C 𝒪_X(E) + deg_C 𝒪_X(E')` along a proper curve. -/
private theorem degree_cartierSheaf_add (C : ProperCurve sX) (E E' : X.CartierDivisor) :
    C.degree k (MMP.CartierDivisor.sheaf (E + E')) =
      C.degree k (MMP.CartierDivisor.sheaf E) +
        C.degree k (MMP.CartierDivisor.sheaf E') := by
  haveI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
        X.toRingedSpace.IsSheaf⟩).obj (MMP.CartierDivisor.sheaf E)).obj
          (MMP.CartierDivisor.sheaf E')) :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible X.presheaf X.ringCatSheaf.2 _ _
  unfold ProperCurve.degree
  rw [← degreeOn_tensorSheaf]
  exact (degreeOn_eq_of_iso k sX C.ι C.dim_le
    (L := ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
        X.toRingedSpace.IsSheaf⟩).obj (MMP.CartierDivisor.sheaf E)).obj
          (MMP.CartierDivisor.sheaf E'))
    (MMP.CartierDivisorSheaf.sheafMulIso E E')).symm

/-- The degree form on `N₁(X/Y)` is determined by the degrees on curves: if
`deg_C L = a deg_C L₁ + b deg_C L₂` for every proper curve `C`, then the same relation holds
for the degree forms. -/
private theorem degree_eq_smul_add_smul (L L₁ L₂ : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L₁]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L₂] (a b : ℝ)
    (h : ∀ C : ProperCurve sX,
      (C.degree k L : ℝ) = a * C.degree k L₁ + b * C.degree k L₂) :
    RelativeNumericalCurveClasses.degree sX f L =
      a • RelativeNumericalCurveClasses.degree sX f L₁ +
        b • RelativeNumericalCurveClasses.degree sX f L₂ := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun Z => ?_)
  change OneCycle.degree ℝ sX L (Z : OneCycle ℝ sX) =
    a * OneCycle.degree ℝ sX L₁ (Z : OneCycle ℝ sX) +
      b * OneCycle.degree ℝ sX L₂ (Z : OneCycle ℝ sX)
  simp only [OneCycle.degree_apply, h, Finsupp.sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun C _ => by ring

/-- A sheaf of nonnegative degree on every contracted curve has a degree form that is
nonnegative on the closed relative cone of curves. -/
private theorem degree_nonneg_of_forall (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (h : ∀ C : ProperCurve sX, C.IsContractedBy f → 0 ≤ C.degree k L)
    {z : RelativeNumericalCurveClasses sX f} (hz : z ∈ relativeClosedConeOfCurves sX f) :
    0 ≤ RelativeNumericalCurveClasses.degree sX f L z := by
  have hS : IsClosed {z : RelativeNumericalCurveClasses sX f |
      0 ≤ RelativeNumericalCurveClasses.degree sX f L z} :=
    isClosed_le continuous_const (RelativeNumericalCurveClasses.continuous_degree sX f _)
  refine closure_minimal (fun w hw => ?_) hS hz
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨C, hC⟩, rfl⟩ := hx
    show 0 ≤ OneCycle.degree ℝ sX _ (C.cycle ℝ)
    rw [OneCycle.degree_cycle]
    exact_mod_cast h C hC
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Set.mem_setOf_eq, map_add] at hx hy ⊢
    exact add_nonneg hx hy
  | smul a x _ hx =>
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [show a • x = (a : ℝ) • x from rfl, map_smul, smul_eq_mul]
    exact mul_nonneg a.2 hx

end Degree

/-! ### Pull-backs and ampleness -/

section Pullback

/-- Pulling back the sheaf of a Cartier divisor commutes with positive multiples. -/
private theorem nonempty_divisorialSheaf_nsmul_iso_pullback {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (f : X ⟶ Y) {G : Divisor X}
    (hG : G.IsCartier) {M : Y.CartierDivisor}
    (e : G.divisorialSheaf ≅
      (Scheme.Modules.pullback f).obj (MMP.CartierDivisor.sheaf M))
    (n : ℕ) (hn : 1 ≤ n) :
    Nonempty ((n • G).divisorialSheaf ≅
      (Scheme.Modules.pullback f).obj (MMP.CartierDivisor.sheaf (n • M))) := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [one_nsmul, one_nsmul]
    exact ⟨e⟩
  | succ n hn ih =>
    obtain ⟨ie⟩ := ih
    rw [succ_nsmul, succ_nsmul]
    exact ⟨((hG.nsmul n).divisorialSheafTensorIso hG).symm ≪≫ MonoidalCategory.tensorIso ie e ≪≫
      (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso f _ _).symm ≪≫
      (Scheme.Modules.pullback f).mapIso
        (MMP.CartierDivisorSheaf.sheafMulIso (n • M) M)⟩

/-- A projective variety carries a Cartier divisor whose sheaf is ample. -/
private theorem exists_isAmple_cartierSheaf {k : Type} [Field k] {Y : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} (hY : IsProjectiveVariety k sY) :
    ∃ M : Y.CartierDivisor,
      Stacks.Ample.IsAmple Y (MMP.CartierDivisor.sheaf M) := by
  haveI : IsIntegral Y := hY.toIsIntegral
  obtain ⟨H, hH, hHa⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety hY
  obtain ⟨M, ⟨e⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf H
  exact ⟨M, (Stacks.RelativeVeryAmple.isAmple_congr _ _ e).mp
    ((Stacks.AmpleBridge.isAmple_iff_isAmple Y H).mpr hHa)⟩

/-- A morphism of projective `k`-varieties is projective. -/
private theorem isProjective_of_comp_eq {k : Type} [Field k] {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    (hX : IsProjectiveVariety k sX) (hY : IsProjectiveVariety k sY)
    {f : X ⟶ Y} (hf : f ≫ sY = sX) : IsProjective f := by
  have : IsSeparated sY := hY.toIsVariety.toIsSeparated
  let γ : X ⟶ Limits.pullback sX sY := Limits.pullback.lift (𝟙 X) f (by simp [hf])
  have : IsClosedImmersion γ :=
    MorphismProperty.of_postcomp (W := @IsClosedImmersion) (W' := @IsSeparated) γ
      (Limits.pullback.fst sX sY) inferInstance
      (by simp only [γ, Limits.pullback.lift_fst]; infer_instance)
  have hγ : γ ≫ Limits.pullback.snd sX sY = f := Limits.pullback.lift_snd _ _ _
  rw [← hγ]
  exact ((MMP.isProjectiveMorphism_of_isClosedImmersion γ).comp
    (hX.isProjective.baseChange sY)).isProjective

end Pullback

/-! ### The Kleiman step -/

section Kleiman

variable {k : Type} [Field k] {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} {f : X ⟶ Y}

/-- If `m₀ B` is the Cartier divisor `D₀` for an `f`-nef `ℚ`-divisor `B`, then `D₀` has
nonnegative degree on every curve contracted by `f`. -/
private theorem degreeOn_nonneg_of_isRelativelyNef {B : QDivisor X}
    (hB : B.IsRelativelyNef sX f) {m₀ : ℕ} (hm₀ : 0 < m₀) {D₀ : Divisor X} (hD₀c : D₀.IsCartier)
    (hD₀B : Divisor.toQDivisor D₀ = (m₀ : ℚ) • B) (C : ProperCurve sX)
    (hC : C.IsContractedBy f) : 0 ≤ D₀.degreeOn k sX C.ι C.dim_le hD₀c := by
  have h := MMP.Fourfold.QDivisor.IsRelativelyNef.intersectionNumber_nonneg sX hB hB.fst C hC
  rw [QDivisor.intersectionNumber_eq_of_smul k sX C.ι C.dim_le B hB.fst hm₀ D₀ hD₀c
    (by rw [hD₀B, natCast_zsmul, Nat.cast_smul_eq_nsmul])] at h
  exact_mod_cast ((div_nonneg_iff.1 h).resolve_right fun h => (Nat.cast_pos.2 hm₀).not_ge h.2).1

variable [IsAlgClosed k] [CharZero k] {sY : Y ⟶ Spec (.of k)} [IsVariety k sX] [IsVariety k sY]

/-- **`r m D₀ - E` is `f`-ample** (relative Kleiman): let `D₀` be an `f`-nef Cartier divisor
with `m D₀ ∼ A + E`, `A` `f`-ample and `E` the Cartier divisor of `E_w`. For `r ≥ 1` the
divisor `r m D₀ - E_w = (r - 1) m D₀ + A` is positive on `NE̅(X/Y) \ 0`, so any Cartier divisor
with its sheaf is `f`-ample. -/
private theorem isRelativelyAmple_nsmul_sub (hfp : IsProjective f) (hcomp : f ≫ sY = sX)
    {D₀ Ew : Divisor X} (hD₀c : D₀.IsCartier) (hEwc : Ew.IsCartier)
    (hnn : ∀ C : ProperCurve sX, C.IsContractedBy f → 0 ≤ D₀.degreeOn k sX C.ι C.dim_le hD₀c)
    {m r : ℕ} (hr1 : 1 ≤ r) {A E Cr : X.CartierDivisor}
    (hA : IsRelativelyAmple f (MMP.CartierDivisor.sheaf A))
    (eD : (m • D₀).divisorialSheaf ≅ MMP.CartierDivisor.sheaf (A + E))
    (eE : Ew.divisorialSheaf ≅ MMP.CartierDivisor.sheaf E)
    (eF : (((r * m : ℕ) : ℤ) • D₀ + (-1 : ℤ) • Ew).divisorialSheaf ≅
      MMP.CartierDivisor.sheaf Cr) :
    IsRelativelyAmple f (MMP.CartierDivisor.sheaf Cr) := by
  have hFc : (((r * m : ℕ) : ℤ) • D₀ + (-1 : ℤ) • Ew).IsCartier :=
    (hD₀c.zsmul _).add (hEwc.zsmul _)
  haveI := hD₀c.isInvertibleModule_divisorialSheaf
  haveI := hFc.isInvertibleModule_divisorialSheaf
  haveI := (hD₀c.nsmul m).isInvertibleModule_divisorialSheaf
  haveI := hEwc.isInvertibleModule_divisorialSheaf
  -- on curves, `deg F = (r - 1) m deg D₀ + deg A`
  have hdeg (C : ProperCurve sX) :
      (C.degree k (MMP.CartierDivisor.sheaf Cr) : ℝ) =
        (((r : ℝ) - 1) * m) * C.degree k D₀.divisorialSheaf +
          1 * C.degree k (MMP.CartierDivisor.sheaf A) := by
    have h1 : C.degree k (MMP.CartierDivisor.sheaf Cr) =
        ((r * m : ℕ) : ℤ) * D₀.degreeOn k sX C.ι C.dim_le hD₀c -
          Ew.degreeOn k sX C.ι C.dim_le hEwc := by
      have h : C.degree k (MMP.CartierDivisor.sheaf Cr) =
          (((r * m : ℕ) : ℤ) • D₀ + (-1 : ℤ) • Ew).degreeOn k sX C.ι C.dim_le hFc :=
        (degreeOn_eq_of_iso k sX C.ι C.dim_le eF).symm
      rw [h, Divisor.degreeOn_add k sX C.ι C.dim_le _ _ (hD₀c.zsmul _) (hEwc.zsmul _),
        MMP.Fourfold.degreeOn_zsmul, MMP.Fourfold.degreeOn_zsmul]
      all_goals first | ring | assumption
    have h2 : C.degree k (MMP.CartierDivisor.sheaf E) =
        Ew.degreeOn k sX C.ι C.dim_le hEwc := (degreeOn_eq_of_iso k sX C.ι C.dim_le eE).symm
    have h3 : (m • D₀).degreeOn k sX C.ι C.dim_le (hD₀c.nsmul m) =
        C.degree k (MMP.CartierDivisor.sheaf (A + E)) :=
      degreeOn_eq_of_iso k sX C.ι C.dim_le eD
    rw [Divisor.degreeOn_nsmul' k sX C.ι C.dim_le D₀ hD₀c m, degree_cartierSheaf_add, h2] at h3
    have e2' : ((m : ℤ) : ℝ) * (D₀.degreeOn k sX C.ι C.dim_le hD₀c : ℝ) =
        (C.degree k (MMP.CartierDivisor.sheaf A) : ℝ) +
          (Ew.degreeOn k sX C.ι C.dim_le hEwc : ℝ) := by exact_mod_cast h3
    change _ = _ * (D₀.degreeOn k sX C.ι C.dim_le hD₀c : ℝ) + _
    rw [h1]
    push_cast at e2' ⊢
    linear_combination e2'
  have hform := degree_eq_smul_add_smul (f := f) (MMP.CartierDivisor.sheaf Cr)
    D₀.divisorialSheaf (MMP.CartierDivisor.sheaf A) _ 1 hdeg
  refine (isRelativelyAmple_cartierSheaf_iff_forall_relativeClosedConeOfCurves_pos sY sX f hfp
    hcomp Cr).2 fun z hz hz0 => ?_
  have hA' := (isRelativelyAmple_cartierSheaf_iff_forall_relativeClosedConeOfCurves_pos sY sX f
    hfp hcomp A).1 hA z hz hz0
  rw [intersectionNumber_ofCartier_eq_degree] at hA' ⊢
  have hc : (0 : ℝ) ≤ ((r : ℝ) - 1) * m :=
    mul_nonneg (sub_nonneg.2 (by exact_mod_cast hr1)) (Nat.cast_nonneg _)
  simp only [hform, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, one_mul]
  exact add_pos_of_nonneg_of_pos
    (mul_nonneg hc (degree_nonneg_of_forall (f := f) D₀.divisorialSheaf hnn hz)) hA'

end Kleiman

/-- A positive rational `ε` exceeds `1 / (r n)` for some integer `r ≥ 1`. -/
private theorem exists_one_le_inv_mul_lt {ε : ℚ} (hε : 0 < ε) {n : ℕ} (hn : 0 < n) :
    ∃ r : ℕ, 1 ≤ r ∧ ((r * n : ℕ) : ℚ)⁻¹ < ε := by
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  refine ⟨N + 1, by omega, lt_of_le_of_lt ?_ hN⟩
  rw [one_div]
  exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.le_mul_of_pos_right _ hn)

/-- **A pull-back twist and a small boundary make `a D - K_X - Δ` ample** (Kollár–Mori 3.26). Let
`f : X ⟶ Y` be a morphism of projective varieties over an algebraically closed field `k` of
characteristic zero, `(X, Δ)` a klt pair with `Δ ≥ 0` and canonical divisor `K`, `D` an `f`-nef
Cartier divisor and `a > 0` rational with `aD - K - Δ` `f`-nef and `f`-big. Then there are an
ample Cartier divisor `H` on `Y`, a Cartier divisor `G` on `X` with `𝒪_X(G) ≅ f^*𝒪_Y(H)` and an
effective `ℚ`-Cartier `ℚ`-divisor `E'` with `(X, Δ + E')` klt and `a(D + G) - K - Δ - E'`
ample. -/
@[mmp "lem_km3b_relative_bpf_make_ample"]
public theorem exists_isAmple_smul_add_pullback_sub_of_isKltPair {k : Type} [Field k]
    {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {sY : Y ⟶ Spec (.of k)} {f : X ⟶ Y}
    (hf : IsProjectiveSetting k sX sY f)
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} (hklt : IsKltPair sX n K Δ) (hΔ : 0 ≤ Δ)
    {D : Divisor X} (hDc : D.IsCartier) (hD : (Divisor.toQDivisor D).IsRelativelyNef sX f)
    {a : ℚ} (ha : 0 < a)
    (hnef : (a • Divisor.toQDivisor D - Divisor.toQDivisor K - Δ).IsRelativelyNef sX f)
    (hbig : (a • Divisor.toQDivisor D - Divisor.toQDivisor K - Δ).IsRelativelyBig f) :
    ∃ H : Y.CartierDivisor,
      Stacks.Ample.IsAmple Y (MMP.CartierDivisor.sheaf H) ∧
      ∃ G : Divisor X, G.IsCartier ∧
        Nonempty (G.divisorialSheaf ≅
          (Scheme.Modules.pullback f).obj (MMP.CartierDivisor.sheaf H)) ∧
      ∃ E' : QDivisor X, 0 ≤ E' ∧ E'.IsQCartier ∧ IsKltPair sX n K (Δ + E') ∧
        (a • Divisor.toQDivisor (D + G) - Divisor.toQDivisor K - Δ - E').IsAmple := by
  haveI := hf.isAlgClosed
  haveI := hf.charZero
  haveI hXp : IsProjectiveVariety k sX := hf.isProjectiveVariety_source
  haveI hYp : IsProjectiveVariety k sY := hf.isProjectiveVariety_target
  have hcomp : f ≫ sY = sX := hf.comp_eq
  haveI : IsVariety k sX := hXp.toIsVariety
  haveI : IsVariety k sY := hYp.toIsVariety
  have hfp : IsProjective f := isProjective_of_comp_eq hXp hYp hcomp
  set B := a • Divisor.toQDivisor D - Divisor.toQDivisor K - Δ with hBdef
  -- a multiple `m₀ B = D₀` is an `f`-big Cartier divisor, and `m D₀ ∼ A + E`
  obtain ⟨m₀, hm₀, D₀, hD₀B, hD₀c, hD₀b⟩ := hbig
  obtain ⟨m, hm, A, E, hA, ⟨eD⟩, Ew, hEwc, hEw0, ⟨eE⟩⟩ :=
    exists_nsmul_iso_ample_add_effective sX sY f hcomp hD₀c hD₀b
  -- the klt threshold for adding multiples of `E`
  have hEweff : (Divisor.toQDivisor Ew).IsEffective := fun P => by
    change (0 : ℚ) ≤ (Ew P : ℚ)
    exact_mod_cast hEw0 P
  have hEwq : (Divisor.toQDivisor Ew).IsQCartier := QDivisor.isQCartier_toQDivisor hEwc
  obtain ⟨ε₀, hε₀, hklt'⟩ := hklt.exists_forall_isKltPair_add_smul hEweff hEwq
  obtain ⟨r, hr1, hr⟩ := exists_one_le_inv_mul_lt hε₀ (Nat.mul_pos hm hm₀)
  set j : ℕ := r * (m * m₀) with hjdef
  have hj : 0 < j := Nat.mul_pos (by omega) (Nat.mul_pos hm hm₀)
  set E' : QDivisor X := ((j : ℚ)⁻¹) • Divisor.toQDivisor Ew with hE'def
  -- the Cartier divisor `F = r m D₀ - E_w` is `f`-ample
  set F : Divisor X := ((r * m : ℕ) : ℤ) • D₀ + (-1 : ℤ) • Ew with hFdef
  have hFc : F.IsCartier := (hD₀c.zsmul _).add (hEwc.zsmul _)
  obtain ⟨Cr, ⟨eF⟩⟩ := exists_sheaf_iso_divisorialSheaf hFc
  have hFamp : IsRelativelyAmple f (MMP.CartierDivisor.sheaf Cr) :=
    isRelativelyAmple_nsmul_sub hfp hcomp hD₀c hEwc
      (degreeOn_nonneg_of_isRelativelyNef hnef hm₀ hD₀c hD₀B) hr1 hA eD eE eF
  -- an ample `M₀` on `Y`, its pull-back `B₁`, and the Weil divisor `G₁` of `B₁`
  obtain ⟨M₀, hM₀⟩ := exists_isAmple_cartierSheaf hYp
  obtain ⟨B₁, ⟨eB₁⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf
    ((Scheme.Modules.pullback f).obj (MMP.CartierDivisor.sheaf M₀))
  obtain ⟨G₁, hG₁c, ⟨eG₁⟩⟩ := exists_divisor_iso_sheaf B₁
  -- `F + ν f^*M₀` is ample for `ν ≫ 0`
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (MMP.Foundations.isAmple_add_zsmul_pullback k hXp hYp hcomp hM₀ hFamp
      ⟨eB₁.symm⟩)
  -- write `a = α / β` and take `ν = j α s`, `H = β s M₀`
  set α : ℕ := a.num.toNat with hαdef
  set β : ℕ := a.den with hβdef
  have hnum : (0 : ℤ) ≤ a.num := Rat.num_nonneg.mpr ha.le
  have hα0 : 0 < α := by
    have := Rat.num_pos.mpr ha
    omega
  have hαβ : (α : ℚ) = a * β := by
    have h1 : ((a.num.toNat : ℕ) : ℚ) = ((a.num.toNat : ℤ) : ℚ) := by norm_cast
    rw [hαdef, hβdef, h1, Int.toNat_of_nonneg hnum, Rat.mul_den_eq_num]
  set s : ℕ := N.toNat + 1 with hsdef
  set ν : ℕ := j * α * s with hνdef
  have hs1 : 1 ≤ s := Nat.succ_pos _
  have hsν : s ≤ ν := Nat.le_mul_of_pos_left s (Nat.mul_pos hj hα0)
  have hamp := hN ν (by have := Int.self_le_toNat N; push_cast [hsdef] at hsν ⊢; omega)
  have hβs : 1 ≤ β * s := Nat.mul_pos a.den_pos hs1
  obtain ⟨eG⟩ := nonempty_divisorialSheaf_nsmul_iso_pullback f hG₁c
    (eG₁ ≪≫ eB₁.symm) (β * s) hβs
  obtain ⟨eν⟩ := nonempty_divisorialSheaf_nsmul_iso hG₁c eG₁ ν (hs1.trans hsν)
  obtain ⟨eFG⟩ := nonempty_divisorialSheaf_add_iso hFc (hG₁c.nsmul ν) eF eν
  refine ⟨(β * s) • M₀, ?_, (β * s) • G₁, hG₁c.nsmul _, ⟨eG⟩, E', fun P => ?_,
    MMP.Flips.QDivisor.IsQCartier.qsmul hEwq _, hklt' _ (by positivity) hr, ?_⟩
  · exact (MMP.Resolution.Bridges.isAmple_lineBundle_iff_nsmul M₀ (β * s) hβs).1 hM₀
  · change (0 : ℚ) ≤ (j : ℚ)⁻¹ * (Ew P : ℚ)
    exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (by exact_mod_cast hEw0 P)
  · refine ⟨j, hj, F + ν • G₁, ?_, hFc.add (hG₁c.nsmul ν), ?_⟩
    · have hEw' : Divisor.toQDivisor Ew = (j : ℚ) • E' := by
        rw [hE'def, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hj.ne'), one_smul]
      rw [hFdef, map_add, map_add, map_zsmul, map_zsmul, map_nsmul, map_add, map_nsmul, hD₀B,
        hEw']
      simp only [← Int.cast_smul_eq_zsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ]
      rw [hBdef, hνdef, hjdef]
      push_cast
      rw [hαβ]
      module
    · haveI := (hFc.add (hG₁c.nsmul ν)).isInvertibleModule_divisorialSheaf
      show Stacks.Ample.IsAmple X (F + ν • G₁).divisorialSheaf
      rw [natCast_zsmul] at hamp
      exact (Stacks.RelativeVeryAmple.isAmple_congr _ _ eFG).mpr hamp

end MMP.Mori
