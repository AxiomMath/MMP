module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.BasepointFree.ProofData
public import MMP.AlgebraicGeometry.Intersection.Nef
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
import MMP.AlgebraicGeometry.Resolution.LogResolutionAmpleSubtraction
import MMP.AlgebraicGeometry.Positivity.AmplePlusNefSum
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Singularities.CrepantBoundaryKlt
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafQuasicoherent
import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
import MMP.AlgebraicGeometry.RegularEmbedding.ConesBlowups
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
import MMP.AlgebraicGeometry.Positivity.AmpleNefBig
import MMP.AlgebraicGeometry.Morphisms.FiniteCoverTrace
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleEmbedding
import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.MMP.Abundance.FiniteRepresentationGeneration
import MMP.AlgebraicGeometry.Singularities.SncLogDiscrepancyFormula
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.MMP.Threefold.Discrepancy
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.Positivity.NefBigOfAmpleApproximation
import MMP.AlgebraicGeometry.Positivity.BigAmplePlusEffective
import MMP.AlgebraicGeometry.MMP.ConeTheorem.Rationality.EulerPolynomialLeadingCoeff
import MMP.AlgebraicGeometry.Intersection.PairingSeparation
import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
import MMP.AlgebraicGeometry.Divisor.PullbackExistence
import MMP.AlgebraicGeometry.Intersection.CurveCartierLocal
import MMP.AlgebraicGeometry.Divisor.CartierDivisorPullbackAdd
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafMul
import MMP.AlgebraicGeometry.Divisor.CartierDivisorPullbackSheaf

/-!
# Adapted resolutions, the reduction of non-vanishing, and nef plus big

Three steps of the proofs of the basepoint-free and non-vanishing theorems over an algebraically
closed field of characteristic `0`, all built on a projective log resolution
`f : Y → X` with snc boundary `∑ F_j ⊇ Ex(f) ∪ f⁻¹(Supp Δ)` and rationals `p_j > 0` such that
`f^*B - ∑ p_j F_j` is ample (`MMP.Mori.exists_isLogResolution_isAmple_pullback_sub_sum`).

* **Adapted resolutions.** For a basepoint-free datum `(X, Δ, D, a)` and `m ≥ 0` with
  `H⁰(X, mD) ≠ 0`, principalising the base ideal `I = ∑_σ 𝒪_X(-(σ)₀)` of `|mD|` gives an
  `m`-adapted resolution `(f; F_1, …, F_s; a_•; p_•; r_•)`: the `a_j` are the coefficients of
  the crepant boundary (`a_j > -1` since `(X, Δ)` is klt), `p_j = p'_j / N` for `N` large, so
  that `f^*(aD - K_X - Δ) - ∑ p_j F_j = N⁻¹ (f^*B - ∑ p'_j F_j) + (1 - N⁻¹) f^*B` is ample,
  and `∑ r_j F_j` is the fixed part of `f^*|mD|`, read off stalkwise from
  `f⁻¹I · 𝒪_Y = 𝒪_Y(-∑ r_j F_j)`.
* **Reduction of non-vanishing to smooth data.** If every smooth non-vanishing datum of
  dimension `n` has the non-vanishing property, so does every non-vanishing datum
  `(X, D, G, a)`: with `Δ'` the crepant boundary of `(X, -G)` on `Y` and `q` large,
  `(Y, f^*D, -Δ' - q⁻¹ ∑ p_j F_j, a)` is a smooth datum, and its sections push forward because
  along the strict transform of a prime divisor `P` one has `⌈g_P - p/q⌉ ≤ ⌈g_P⌉`.
* **Nef and big plus nef is nef and big.** On a resolution with `f^*B = A + P`, `A` ample and
  `P` effective, `f^*(M(B + N))` is an ample divisor plus `(1/n) MP` for infinitely many `n`,
  hence nef and big, and bigness descends along the birational `f`.

## Main results

* `MMP.Mori.IsBasepointFreeDatum.exists_isBasepointFreeAdaptedResolution`: an `m`-adapted
  resolution exists.
* `MMP.Mori.IsNonvanishingDatum.hasNonvanishingProperty_of_isSmoothNonvanishingDatum`: the
  non-vanishing theorem reduces to smooth data.
* `MMP.Mori.QDivisor.IsNef.isNef_and_isBig_add`: nef and big plus nef is nef and big.

## Implementation notes

The condition `H⁰(X, mD) ≠ 0` is the existence of a nonzero element of
`(m • D).divisorialSubmodule ⊤`. The ideal sheaf `𝒪_X(-A) ∩ 𝒪_X` of an effective Cartier
divisor `A` is built on affine opens from the quasi-coherence of the divisorial sheaf; its stalk
at `x` is generated by a local equation. Orders of pulled-back local equations along a prime
divisor `E` of `Y` are compared with the coefficients of the pull-back through the generization
`𝒪_{Y,y} ⟶ 𝒪_{Y,E}`.

In the reduction, the canonical divisor of `Y` is `div(f^*ω)` for a rational top form `ω` with
`div(ω) = K_X`, so that `K_Y + Δ'` is the pull-back of `K_X - G`; the hypothesis quantifies over
smooth data on schemes in the same universe as `X`.

Bigness descends through Cartier divisors: a Cartier Weil divisor `D` is compared with
a Cartier divisor `A` with `𝒪_X(A) ≅ 𝒪_X(D)`, whose pull-back `MMP.CartierDivisor.pullback` has
`𝒪_Y(f^*A) ≅ 𝒪_Y(f^*D)`, and `h⁰` of all positive multiples agree on both sides.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.2 Steps 1–2,
  3.4, 3.5
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Mori

section Positivity

variable {k : Type} [Field k]

/-- **The image of a curve that is not contracted is a curve.** -/
private theorem isProper_and_isCurve_imageι {V W C : Scheme.{0}} {sV : V ⟶ Spec (.of k)}
    {sW : W ⟶ Spec (.of k)} [IsSeparated sW] [LocallyOfFiniteType sW] {u : V ⟶ W}
    (hu : u ≫ sW = sV) (i : C ⟶ V)
    [AlgebraicGeometry.IsCurve k (i ≫ sV)] [IsProper (i ≫ sV)]
    (hpt : ¬ ∃ w : W, Set.range (i ≫ u) = {w}) :
    IsProper ((i ≫ u).imageι ≫ sW) ∧ AlgebraicGeometry.IsCurve k ((i ≫ u).imageι ≫ sW) := by
  have e : (i ≫ u) ≫ sW = i ≫ sV := by rw [Category.assoc, hu]
  have : IsProper ((i ≫ u) ≫ sW) := e ▸ inferInstance
  have : AlgebraicGeometry.IsCurve k ((i ≫ u) ≫ sW) := e ▸ inferInstance
  have : IsProper (i ≫ u) := IsProper.of_comp (i ≫ u) sW
  exact ⟨isProper_imageι_comp (i ≫ u) sW, isCurve_imageι_comp sW (i ≫ u) hpt⟩

attribute [local instance] AlgebraicGeometry.IsVariety.toIsIntegral in
/-- **The pull-back of a nef `ℚ`-divisor is nef.** -/
private theorem isNef_of_isPullback {V W : Scheme.{0}} {sV : V ⟶ Spec (.of k)}
    {sW : W ⟶ Spec (.of k)} [AlgebraicGeometry.IsVariety k sV]
    [AlgebraicGeometry.IsVariety k sW] [IsLocallyNoetherian V] [IsNormal V]
    [IsLocallyNoetherian W] [IsNormal W] {u : V ⟶ W} (hu : u ≫ sW = sV) {L : QDivisor W}
    (hL : L.IsNef k sW)
    {hLB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L.supp}
    {L' : QDivisor V} (h : L.IsPullback u hLB L') : L'.IsNef k sV := by
  refine ⟨h.isQCartier hL.1, fun C i _ _ _ hC => ?_⟩
  have : AlgebraicGeometry.IsCurve k (i ≫ sV) := { topologicalKrullDim_eq_one := hC }
  by_cases hpt : ∃ w : W, Set.range (i ≫ u) = {w}
  · exact (intersectionNumber_pullback_eq_zero k sV sW u hu i hL.1 h hpt).ge
  · obtain ⟨_, hcurve⟩ := isProper_and_isCurve_imageι hu i hpt
    rw [intersectionNumber_pullback_eq_degreeOver_mul k sV sW u hu i hL.1 h hcurve]
    exact mul_nonneg (by positivity)
      (hL.2 _ (i ≫ u).imageι hcurve.topologicalKrullDim_eq_one)

/-- A nonnegative multiple of a nef `ℚ`-divisor is nef. -/
private theorem isNef_smul {W : Scheme.{0}} [IsLocallyNoetherian W] [IsNormal W]
    {sW : W ⟶ Spec (.of k)} [QuasiCompact sW] {L : QDivisor W} (hL : L.IsNef k sW) {t : ℚ}
    (ht : 0 ≤ t) : (t • L).IsNef k sW :=
  ⟨MMP.Flips.QDivisor.IsQCartier.qsmul hL.1 t, fun C i _ _ _ hC => by
    rw [MMP.Fourfold.intersectionNumber_smul sW i hC.le L hL.1 t]
    exact mul_nonneg ht (hL.2 C i hC)⟩

/-- A positive rational multiple `N⁻¹ A` of an ample `ℚ`-divisor is ample. -/
private theorem isAmple_inv_natCast_smul {W : Scheme.{0}} [IsLocallyNoetherian W] [CompactSpace W]
    [IsNormal W] {A : QDivisor W} (hA : A.IsAmple) {N : ℕ} (hN : 0 < N) :
    ((N : ℚ)⁻¹ • A).IsAmple := by
  obtain ⟨m, hm, G, hG, hGc, hGa⟩ := hA
  refine ⟨m * N, Nat.mul_pos hm hN, G, ?_, hGc, hGa⟩
  rw [hG, smul_smul, Nat.cast_mul, mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hN.ne'),
    mul_one]

/-- **Shrinking an ample divisor by a nef one.** If `B` is nef and `B - P` is ample, then so is
`B - N⁻¹ P` for every `N > 0`: it is `N⁻¹ (B - P) + (1 - N⁻¹) B`. -/
private theorem isAmple_sub_inv_natCast_smul {W : Scheme.{0}} (sW : W ⟶ Spec (.of k))
    [MMP.Mori.IsProjectiveVariety k sW] [IsNormal W] [IsLocallyNoetherian W] [CompactSpace W]
    {B P : QDivisor W} (hB : B.IsNef k sW) (hBP : (B - P).IsAmple) {N : ℕ}
    (hN : 0 < N) (hQ : (B - (N : ℚ)⁻¹ • P).IsQCartier) : (B - (N : ℚ)⁻¹ • P).IsAmple := by
  have heq : (N : ℚ)⁻¹ • (B - P) + ∑ _i ∈ (Finset.univ : Finset Unit), (1 - (N : ℚ)⁻¹) • B =
      B - (N : ℚ)⁻¹ • P := by
    simp only [Finset.univ_unique, Finset.sum_singleton]
    module
  refine QDivisor.isAmple_of_numericallyEquivalent_add_sum_of_isNef sW Finset.univ
    (fun _ : Unit => (1 - (N : ℚ)⁻¹) • B) (isAmple_inv_natCast_smul hBP hN)
    (fun _ _ => isNef_smul hB (sub_nonneg.mpr (inv_le_one_of_one_le₀ (by exact_mod_cast hN)))) ?_
  rw [heq]
  exact QDivisor.NumericallyEquivalent.refl hQ

end Positivity

/-! ### Adapted resolutions of a basepoint-free datum -/

section EffIdeal

open Opposite

variable {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]

/-- The regular functions on `U` lying in `𝒪_X(-A)(U)`. -/
private noncomputable def effIdealOn (A : Divisor X) (U : X.Opens) : Ideal Γ(X, U) :=
  ((-A).divisorialSubmodule U).comap (Algebra.linearMap Γ(X, U) _)

/-- The ideals `effIdealOn A U` are compatible with restriction to basic opens: this is the
quasi-coherence of `𝒪_X(-A)`. -/
private theorem effIdealOn_map_basicOpen [CompactSpace X] {A : Divisor X} (hA : 0 ≤ A)
    (U : X.Opens) (f : Γ(X, U)) :
    (effIdealOn A U).map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom =
      effIdealOn A (X.basicOpen f) := by
  set V := X.basicOpen f
  have hVU : V ≤ U := X.basicOpen_le f
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro t ht
    change (-A).IsDivisorialSection V ((toRationalFunctionsPresheaf X).app (op V)
      (X.presheaf.map (homOfLE hVU).op t))
    rw [toRationalFunctionsPresheaf_app_map]
    exact Divisor.IsDivisorialSection.map (homOfLE hVU) ht
  · intro t' ht'
    let := Stacks.AlgebraicGeometry.QuasicoherentBaseChange.moduleOfLE
      (-A).divisorialSheaf hVU
    have := Divisor.isLocalizedModule_divisorialSheaf_restrictₗ (-A) f
    let ψ : Γ((-A).divisorialSheaf, V) :=
      (⟨(toRationalFunctionsPresheaf X).app (op V) t', ht'⟩ : (-A).divisorialSubmodule V)
    obtain ⟨⟨φ, ⟨_, k, rfl⟩⟩, hφ⟩ := IsLocalizedModule.surj (Submonoid.powers f)
      (Stacks.AlgebraicGeometry.QuasicoherentBaseChange.restrictₗ (-A).divisorialSheaf hVU) ψ
    have hφ0 : (0 : Divisor X).IsDivisorialSection U
        (φ : (-A).divisorialSubmodule U).1 :=
      Divisor.IsDivisorialSection.mono (φ : (-A).divisorialSubmodule U).2 (neg_nonpos.mpr hA)
    obtain ⟨s, hs⟩ := Divisor.IsDivisorialSection.exists_eq hφ0
    have hsI : s ∈ effIdealOn A U := by
      change (-A).IsDivisorialSection U ((toRationalFunctionsPresheaf X).app (op U) s)
      rw [hs]
      exact (φ : (-A).divisorialSubmodule U).2
    have hu : IsUnit (X.presheaf.map (homOfLE hVU).op f) :=
      X.toRingedSpace.isUnit_res_basicOpen f
    have key : (X.presheaf.map (homOfLE hVU).op f) ^ k * t' =
        X.presheaf.map (homOfLE hVU).op s := by
      apply toRationalFunctionsPresheaf_app_injective V
      have h1 := congrArg (fun ψ : Γ((-A).divisorialSheaf, V) =>
        (ψ : (-A).divisorialSubmodule V).1) hφ
      simp only at h1
      rw [toRationalFunctionsPresheaf_app_map, hs, map_mul, ← map_pow]
      exact h1
    have : t' = ((hu.unit⁻¹ : (Γ(X, V))ˣ) : Γ(X, V)) ^ k *
        X.presheaf.map (homOfLE hVU).op s := by
      rw [← key, ← mul_assoc, ← mul_pow, hu.val_inv_mul, one_pow, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hsI)

/-- The ideal sheaf `𝒪_X(-A) ∩ 𝒪_X` of an effective divisor `A`. -/
private noncomputable def effIdeal [CompactSpace X] (A : Divisor X) (hA : 0 ≤ A) :
    X.IdealSheafData where
  ideal U := effIdealOn A U
  map_ideal_basicOpen U f := effIdealOn_map_basicOpen hA U f

end EffIdeal

/-! ### Stalks of ideal sheaves -/

section Stalks

open Opposite

/-- The stalk of `f⁻¹I · 𝒪_Y` at `y` is generated by the image of the stalk of `I` at `f y`. -/
private theorem stalk_comap {X Y : Scheme.{0}} (I : X.IdealSheafData) (f : Y ⟶ X) (y : Y) :
    IdealSheafData.stalk (I.comap f) y =
      (IdealSheafData.stalk I (f y)).map (f.stalkMap y).hom := by
  obtain ⟨U, hU, hyU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := f y) (U := ⊤) (by simp)
  obtain ⟨V, hV, hyV, hVU⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := y) (U := f ⁻¹ᵁ U) hyU
  rw [IdealSheafData.stalk_eq_map_germ _ y ⟨V, hV⟩ hyV,
    IdealSheafData.stalk_eq_map_germ _ (f y) ⟨U, hU⟩ hyU,
    Stacks.IdealSheaf.ideal_comap_appLE I f ⟨U, hU⟩ ⟨V, hV⟩ hVU, Ideal.map_map, Ideal.map_map]
  congr 1
  ext t
  simp only [RingHom.comp_apply, Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE,
    CommRingCat.comp_apply]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

/-- The stalk of a supremum of ideal sheaves is the supremum of the stalks. -/
private theorem stalk_iSup {X : Scheme.{0}} {ι : Type*} (I : ι → X.IdealSheafData) (x : X) :
    IdealSheafData.stalk (⨆ i, I i) x = ⨆ i, IdealSheafData.stalk (I i) x := by
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) (by simp)
  simp_rw [IdealSheafData.stalk_eq_map_germ _ x ⟨U, hU⟩ hxU]
  rw [Scheme.IdealSheafData.ideal_iSup, iSup_apply, Ideal.map_iSup]

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]

omit [IsLocallyNoetherian X] [CompactSpace X] in
/-- A nonzero element of a local ring `𝒪_{X,x}` of an integral scheme is the component of a unit
of `K(X)`. -/
private theorem exists_unit_eq_of_ne_zero {x : X} {r : X.presheaf.stalk x} (hr : r ≠ 0) :
    ∃ τ : (RationalFunctions X)ˣ, ∀ (Z : irreducibleComponents X) (hxZ : x ∈ Z.1),
      (stalkToRationalFunctions X hxZ).hom r = (τ : RationalFunctions X) Z := by
  classical
  have hne : ∀ (Z : irreducibleComponents X) (hxZ : x ∈ Z.1),
      (stalkToRationalFunctions X hxZ).hom r ≠ 0 := fun Z hxZ h0 =>
    hr (stalkToRationalFunctions_injective hxZ (h0.trans (map_zero _).symm))
  refine ⟨(RationalFunctions.unitsEquiv X).symm fun Z =>
    (isUnit_of_ne_zero_stalk Z (hne Z (MMP.Fourfold.mem_irreducibleComponent_of_irreducibleSpace
      Z x))).unit, fun Z hxZ => rfl⟩

/-- **The stalk of `𝒪_X(-A)`.** If `φ` is a local equation of the effective divisor `A` near
`x` and `g ∈ 𝒪_{X,x}` has image `φ` in `K(X)`, then `𝒪_X(-A)_x = (g)`. -/
private theorem stalk_effIdeal {A : Divisor X} (hA : 0 ≤ A) {U₀ : X.Opens}
    {φ : (RationalFunctions X)ˣ} (hφ : A.IsLocalEquation U₀ φ) {x : X} (hx : x ∈ U₀)
    {Z : irreducibleComponents X} (hxZ : x ∈ Z.1) {g : X.presheaf.stalk x}
    (hg : (stalkToRationalFunctions X hxZ).hom g = (φ : RationalFunctions X) Z) :
    IdealSheafData.stalk (effIdeal A hA) x = Ideal.span {g} := by
  have := MMP.Fourfold.subsingleton_irreducibleComponents (X := X)
  obtain ⟨W, hxW, g₀, hg₀⟩ := X.presheaf.exists_germ_eq g
  obtain ⟨U, hU, hxU, hUsub⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := W ⊓ U₀) ⟨hxW, hx⟩
  set gU : Γ(X, U) := X.presheaf.map (homOfLE (hUsub.trans inf_le_left)).op g₀
  have hgU : X.presheaf.germ U x hxU gU = g :=
    (TopCat.Presheaf.germ_res_apply _ _ _ _ _).trans hg₀
  rw [IdealSheafData.stalk_eq_map_germ _ x ⟨U, hU⟩ hxU]
  change (effIdealOn A U).map _ = _
  have hcomp : ∀ (t : Γ(X, U)) (Z' : irreducibleComponents X)
      (hZ' : componentGenericPoint X Z' ∈ U),
      (toRationalFunctionsPresheaf X).app (op U) t ⟨Z', hZ'⟩ =
        (stalkToRationalFunctions X (MMP.Fourfold.mem_irreducibleComponent_of_irreducibleSpace
          Z' x)).hom (X.presheaf.germ U x hxU t) := fun t Z' hZ' =>
    (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hxU _ t).symm
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro t ht
    rw [Ideal.mem_comap]
    by_cases ht0 : X.presheaf.germ U x hxU t = 0
    · simp [ht0]
    obtain ⟨τ, hτ⟩ := exists_unit_eq_of_ne_zero ht0
    have hord : ∀ E : MMP.Mori.PrimeDivisor X, x ∈ E.support → A.coeff E ≤ E.ord τ := by
      intro E hE
      have h1 : E.OrdGE (-(-A).coeff E) ((toRationalFunctionsPresheaf X).app (op U) t
          ⟨E.component, E.componentGenericPoint_mem_of_nonempty ⟨x, hE, hxU⟩⟩) :=
        ht E ⟨x, hE, hxU⟩
      rw [hcomp, hτ, DivisorWithCoeffs.coeff_neg, neg_neg] at h1
      rcases h1 with h1 | h1
      · exact absurd h1 ((Pi.isUnit_iff.mp τ.isUnit) E.component).ne_zero
      · rwa [E.valuation_component, WithZero.exp_le_exp] at h1
    obtain ⟨r, hr⟩ := exists_stalk_eq_of_forall_zero_le_ord hxZ (τ * φ⁻¹) fun E hE => by
      rw [PrimeDivisor.ord_mul, PrimeDivisor.ord_inv, ← hφ E ⟨x, hE, hx⟩]
      linarith [hord E hE]
    refine Ideal.mem_span_singleton'.mpr ⟨r, stalkToRationalFunctions_injective hxZ ?_⟩
    rw [map_mul, hr, hg]
    refine Eq.trans ?_ (hτ Z hxZ).symm
    rw [← Pi.mul_apply, ← Units.val_mul, inv_mul_cancel_right]
  · rw [Ideal.span_le, Set.singleton_subset_iff, ← hgU]
    refine Ideal.mem_map_of_mem _ ?_
    intro E hEU
    change E.OrdGE (-(-A).coeff E) ((toRationalFunctionsPresheaf X).app (op U) gU
      ⟨E.component, E.componentGenericPoint_mem_of_nonempty hEU⟩)
    rw [hcomp, hgU]
    obtain rfl : Z = E.component := Subsingleton.elim _ _
    rw [hg, DivisorWithCoeffs.coeff_neg, neg_neg]
    refine Or.inr ?_
    rw [E.valuation_component, ← hφ E (hEU.mono (Set.inter_subset_inter_right _
      (hUsub.trans inf_le_right)))]

end Stalks

/-! ### Orders along prime divisors -/

section Orders

variable {Y : Scheme.{0}}

/-- The stalk of `𝒪_Y(-A) = ∏ I_E^{a_E}` at the generic point of a prime divisor `D` is
`𝔪^{a_D}`. -/
private theorem stalk_divisorIdeal_genericPoint (A : AlgebraicGeometry.PrimeDivisor Y → ℕ)
    (hfin : (Function.support A).Finite) (D : AlgebraicGeometry.PrimeDivisor Y) :
    IdealSheafData.stalk (MMP.Resolution.divisorIdeal A) D.genericPoint =
      IsLocalRing.maximalIdeal (Y.presheaf.stalk D.genericPoint) ^ A D := by
  classical
  unfold MMP.Resolution.divisorIdeal
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := hfin.toFinset) fun D' hD' => by
      simpa using fun h0 => hD' (by simp [h0]), MMP.Resolution.Aux.stalk_prod,
    Finset.prod_eq_single D (fun b _ hb => ?_) (fun hD => ?_), MMP.Resolution.Aux.stalk_pow,
    MMP.Resolution.Aux.stalk_idealSheaf_genericPoint]
  · rw [MMP.Resolution.Aux.stalk_pow, (IdealSheafData.stalk_eq_top_iff_notMem_support _ _).2,
      Ideal.top_pow, Ideal.one_eq_top]
    intro hmem
    exact hb (MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hmem)
  · have : A D = 0 := by simpa using hD
    rw [this, pow_zero, show (1 : Y.IdealSheafData) = ⊤ from rfl, MMP.Resolution.Aux.stalk_top,
      Ideal.one_eq_top]

variable [IsLocallyNoetherian Y] [IsNormal Y]

/-- An element of `𝔪^d ⊆ 𝒪_{Y,E}` has order at least `d` along `E`. -/
private theorem ordGE_toComponent_of_mem_pow (E : MMP.Mori.PrimeDivisor Y) {b : E.localRing}
    {d : ℕ} (hb : b ∈ IsLocalRing.maximalIdeal E.localRing ^ d) :
    E.OrdGE d (E.toComponent.hom b) := by
  have := E.isDiscreteValuationRing_localRing
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible E.localRing
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hb
  obtain ⟨c, rfl⟩ := hb
  have h1 : E.OrdGE 1 (E.toComponent.hom ϖ) :=
    Or.inr (by rw [E.valuation_toComponent_of_irreducible hϖ])
  have hc : E.OrdGE 0 (E.toComponent.hom c) := by
    by_cases hc0 : c = 0
    · exact Or.inl (by rw [hc0, map_zero])
    · exact Or.inr (by rw [WithZero.exp_zero]; exact E.one_le_valuation_toComponent hc0)
  rw [map_mul, map_pow]
  simpa using hc.mul (h1.pow d)

/-- If `(b) = 𝔪^d` in `𝒪_{Y,E}`, then `b` has order `d` along `E`. -/
private theorem valuation_toComponent_of_span_eq (E : MMP.Mori.PrimeDivisor Y)
    {b : E.localRing} {d : ℕ}
    (h : Ideal.span {b} = IsLocalRing.maximalIdeal E.localRing ^ d) :
    E.valuation (E.toComponent.hom b) = WithZero.exp (d : ℤ) := by
  have := E.isDiscreteValuationRing_localRing
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible E.localRing
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton] at h
  obtain ⟨u, hu⟩ := h
  have hb : b = ϖ ^ d * ((u⁻¹ : E.localRingˣ) : E.localRing) := by
    rw [← hu, mul_assoc, Units.mul_inv, mul_one]
  rw [hb, map_mul, map_mul, map_pow, map_pow, E.valuation_toComponent_of_irreducible hϖ,
    E.valuation_toComponent_of_isUnit (Units.isUnit _), mul_one, ← WithZero.exp_nsmul,
    nsmul_one]

/-- **Orders of a pulled-back local equation.** Let `f : Y ⟶ X`, `B'` the pull-back of a divisor
`B` with local equation `φ` near `f y`, and `g ∈ 𝒪_{X,f y}` with image `φ`. Then for every prime
divisor `E` through `y`, the order of `f^* g` along `E` is the coefficient of `E` in `B'`. -/
private theorem valuation_toComponent_stalkMap_eq {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] (f : Y ⟶ X) {B : Divisor X}
    (hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ B.supp)
    {B' : Divisor Y} (hp : B.IsPullback f hB B') {U₀ : X.Opens}
    {φ : (RationalFunctions X)ˣ} (hφ : B.IsLocalEquation U₀ φ) {y : Y} (hy : f y ∈ U₀)
    {Z : irreducibleComponents X} (hZ : f y ∈ Z.1) {g : X.presheaf.stalk (f y)}
    (hg : (stalkToRationalFunctions X hZ).hom g = (φ : RationalFunctions X) Z)
    (E : MMP.Mori.PrimeDivisor Y) (hyE : y ∈ E.support) :
    E.valuation (E.toComponent.hom (Y.presheaf.stalkSpecializes
      (MMP.Resolution.Aux.genericPoint_specializes_of_mem_support E hyE) (f.stalkMap y g))) =
      WithZero.exp (B'.coeff E) := by
  have := MMP.Fourfold.subsingleton_irreducibleComponents (X := X)
  have hE : (E.support ∩ f ⁻¹ᵁ U₀).Nonempty := ⟨y, hyE, hy⟩
  rw [hp U₀ φ hφ E hE, ← PrimeDivisor.valuation_eq_exp_ordUnit]
  congr 1
  set η := componentGenericPoint Y E.component
  have hηy : η ⤳ y := E.specializes_genericPoint.trans
    (MMP.Resolution.Aux.genericPoint_specializes_of_mem_support E hyE)
  have hfη : f η ∈ U₀ := (f.base.hom.map_specializes hηy).mem_open U₀.isOpen hy
  have hW : f η ∈ Z.1 := MMP.Fourfold.mem_irreducibleComponent_of_irreducibleSpace Z _
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hfη (hB _) hW
  rw [pullbackComponent_eq hB hφ (E.map_componentGenericPoint_mem f hE) hW a ha]
  have ha' : (a : X.presheaf.stalk (f η)) =
      X.presheaf.stalkSpecializes (f.base.hom.map_specializes hηy) g := by
    apply stalkToRationalFunctions_injective hW
    rw [ha, ← hg]
    change _ = (X.presheaf.stalkSpecializes _ ≫ X.presheaf.stalkSpecializes _).hom g
    rw [TopCat.Presheaf.stalkSpecializes_comp]
    rfl
  change _ = f.stalkMap η (a : X.presheaf.stalk (f η))
  rw [ha', Scheme.Hom.stalkSpecializes_stalkMap_apply f _ _ hηy]
  change (Y.presheaf.stalkSpecializes _ ≫ Y.presheaf.stalkSpecializes _).hom _ = _
  rw [TopCat.Presheaf.stalkSpecializes_comp]

end Orders

/-! ### Local equations, crepant boundaries and stalks of ideal sheaves -/

section Misc

/-- An effective Cartier divisor has, near every point `x`, a local equation `φ` whose component
is the image of an element `g` of `𝒪_{X,x}`. -/
private theorem exists_germ_of_isCartier {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {A : Divisor X} (hA : 0 ≤ A) (hAc : A.IsCartier) (x : X) :
    ∃ (U₀ : X.Opens) (φ : (RationalFunctions X)ˣ) (_ : A.IsLocalEquation U₀ φ) (_ : x ∈ U₀)
      (g : X.presheaf.stalk x),
      (stalkToRationalFunctions X (mem_pointComponent x)).hom g =
        (φ : RationalFunctions X) (pointComponent x) := by
  obtain ⟨U₀, hx, φ, hφ⟩ := hAc x
  obtain ⟨g, hg⟩ := exists_stalk_eq_of_forall_zero_le_ord (mem_pointComponent x) φ
    fun E hE => by rw [← hφ E ⟨x, hE, hx⟩]; exact hA E
  exact ⟨U₀, φ, hφ, hx, g, hg⟩

/-- **The support of the crepant boundary.** For a birational morphism `f : Y ⟶ X` from a normal
variety, every prime divisor in the support of the crepant boundary `Δ_Y` is `f`-exceptional or
lies over `Supp Δ`. -/
private theorem genericPoint_mem_exceptionalSet_or_mem_of_mem_support {k : Type} [Field k]
    [IsAlgClosed k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {f : Y ⟶ X}
    (hP : IsPairWith sX n K Δ) (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f)
    {ΔY : QDivisor Y} (hΔY : IsCrepantBoundary sX n K Δ f hY hf ΔY)
    {G : MMP.Mori.PrimeDivisor Y} (hG : G ∈ ΔY.support) :
    G.genericPoint ∈ (exceptionalSet f : Set Y) ∨ f G.genericPoint ∈ (Δ.supp : Set X) := by
  by_cases hGe : (⟨Y, f, hY, hf, G⟩ : DivisorOver k sX).IsExceptional
  · exact Or.inl (MMP.Positivity.support_subset_exceptionalSet G hGe
      (MMP.Flips.primeDivisor_genericPoint_mem_support G))
  · obtain ⟨P, hc, hd⟩ := DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff hP _ hGe
    have hη : f G.genericPoint = P.genericPoint := by
      refine (inseparable_iff_closure_eq.2 ?_).eq
      rw [← DivisorOver.center_eq_closure_genericPoint (⟨Y, f, hY, hf, G⟩ : DivisorOver k sX), hc,
        AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    have hc' : ΔY.coeff G = Δ.coeff P := neg_injective ((hΔY G).eq hd)
    refine Or.inr ?_
    rw [hη, DivisorWithCoeffs.coe_supp]
    refine Set.mem_iUnion₂.2 ⟨P, ?_, MMP.Flips.primeDivisor_genericPoint_mem_support P⟩
    rwa [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply, ← hc',
      DivisorWithCoeffs.coeff_apply, ← Finsupp.mem_support_iff]

/-- **A generator among generators.** In a local ring, if the principal ideal `(h)` of a
right-regular `h` is the supremum of principal ideals `(g i)`, then some `g i` generates `(h)`:
otherwise every `g i` lies in `𝔪 (h)`, hence so does `h`, and `h = c h` with `c ∈ 𝔪` forces
`c = 1`. -/
private theorem exists_span_singleton_eq_of_span_eq_iSup {R : Type*} [CommRing R]
    [IsLocalRing R] {ι : Type*} {g : ι → R} {h : R} (hreg : IsRightRegular h)
    (hsup : Ideal.span {h} = ⨆ i, Ideal.span {g i}) :
    ∃ i, Ideal.span {g i} = Ideal.span {h} := by
  by_contra hno
  push Not at hno
  have hmax : ∀ i, g i ∈ IsLocalRing.maximalIdeal R * Ideal.span {h} := by
    intro i
    have hle : Ideal.span {g i} ≤ Ideal.span {h} := hsup ▸ le_iSup (fun i => Ideal.span {g i}) i
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hle (Ideal.mem_span_singleton_self _))
    have hcu : c ∈ IsLocalRing.maximalIdeal R := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hcu
      apply hno i
      rw [← hc, mul_comm, Ideal.span_singleton_mul_right_unit hcu]
    rw [← hc]
    exact Ideal.mul_mem_mul hcu (Ideal.mem_span_singleton_self _)
  have hh : h ∈ IsLocalRing.maximalIdeal R * Ideal.span {h} :=
    iSup_le (fun i => (Ideal.span_singleton_le_iff_mem _).mpr (hmax i))
      (hsup ▸ Ideal.mem_span_singleton_self h)
  obtain ⟨c, hc, hch⟩ := Ideal.mem_mul_span_singleton.mp hh
  have hc1 : c = 1 := hreg (show c * h = 1 * h by rw [hch, one_mul])
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr (hc1 ▸ hc))

/-- The zero ideal sheaf has zero stalks. -/
private theorem stalk_bot {X : Scheme.{0}} (x : X) :
    IdealSheafData.stalk (⊥ : X.IdealSheafData) x = ⊥ := by
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) (by simp)
  rw [IdealSheafData.stalk_eq_map_germ _ x ⟨U, hU⟩ hxU, Scheme.IdealSheafData.ideal_bot]
  exact Ideal.map_bot

/-- On a nonempty scheme the unit ideal sheaf is nonzero. -/
private theorem idealSheafData_top_ne_bot {X : Scheme.{0}} [Nonempty X] :
    (⊤ : X.IdealSheafData) ≠ ⊥ := fun hI => by
  have h1 := congrArg Scheme.IdealSheafData.support hI
  rw [Scheme.IdealSheafData.support_top, Scheme.IdealSheafData.support_bot] at h1
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  have hx : x ∈ ((⊤ : TopologicalSpace.Closeds X) : Set X) := trivial
  rw [← h1, TopologicalSpace.Closeds.coe_bot] at hx
  exact hx

/-- The ideal sheaf `𝒪_Y(-A)` of an effective divisor on a smooth scheme is invertible. -/
private theorem isEffectiveCartierDivisor_divisorIdeal {k : Type} [Field k] {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (hY : MMP.Mori.IsSmoothScheme sY)
    (A : AlgebraicGeometry.PrimeDivisor Y → ℕ) (hA : (Function.support A).Finite) :
    Stacks.Divisors.IsEffectiveCartierDivisor (MMP.Resolution.divisorIdeal A) := by
  classical
  have hM : MMP.Resolution.divisorIdeal A = ∏ D ∈ hA.toFinset, D.idealSheaf ^ A D := by
    unfold MMP.Resolution.divisorIdeal
    refine finprod_eq_prod_of_mulSupport_subset _ fun D hD => ?_
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    intro h0
    exact hD (by change D.idealSheaf ^ A D = 1; rw [h0, pow_zero])
  rw [hM]
  exact Stacks.Divisors.isEffectiveCartierDivisor_prod _ _ _
    fun D _ => MMP.Resolution.Aux.isEffectiveCartierDivisor_idealSheaf sY hY D

/-- The ideal sheaf `𝒪_X(-A)` of an effective Cartier divisor is nonzero. -/
private theorem effIdeal_ne_bot_of_isCartier {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {A : Divisor X} (hA : 0 ≤ A)
    (hAc : A.IsCartier) : effIdeal A hA ≠ ⊥ := fun h0 => by
  obtain ⟨U₀, φ, hφ, hx, g, hg⟩ := exists_germ_of_isCartier hA hAc (genericPoint X)
  have hs := stalk_effIdeal hA hφ hx (mem_pointComponent _) hg
  rw [h0, stalk_bot, eq_comm, Ideal.span_singleton_eq_bot] at hs
  rw [hs, map_zero] at hg
  exact ((Pi.isUnit_iff.mp φ.isUnit) _).ne_zero hg.symm

/-- The pull-back of `𝒪_X(-B)` along `f : Y ⟶ X` is locally generated at `y` by an element whose
order along every prime divisor `E ∋ y` is the coefficient of `E` in `f^* B`. -/
private theorem exists_stalk_comap_effIdeal_eq_span {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] (f : Y ⟶ X) {B : Divisor X} (hB0 : 0 ≤ B) (hBc : B.IsCartier)
    (hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ B.supp) (y : Y) :
    ∃ g : Y.presheaf.stalk y, IdealSheafData.stalk ((effIdeal B hB0).comap f) y = Ideal.span {g} ∧
      ∀ (E : MMP.Mori.PrimeDivisor Y) (hyE : y ∈ E.support),
        E.valuation (E.toComponent.hom (Y.presheaf.stalkSpecializes
          (MMP.Resolution.Aux.genericPoint_specializes_of_mem_support E hyE) g)) =
          WithZero.exp ((B.pullback hBc hB).coeff E) := by
  obtain ⟨U₀, φ, hφ, hx, g, hg⟩ := exists_germ_of_isCartier hB0 hBc (f y)
  refine ⟨f.stalkMap y g, ?_, fun E hyE => valuation_toComponent_stalkMap_eq f hB
    (Divisor.isPullback_pullback hBc hB) hφ hx (mem_pointComponent _) hg E hyE⟩
  rw [stalk_comap, stalk_effIdeal _ hφ hx (mem_pointComponent _) hg, Ideal.map_span,
    Set.image_singleton]

end Misc

/-- **Adapted resolutions exist** (Kollár–Mori 3.2, Steps 1–2). Over an algebraically closed
field of characteristic `0`, let `(X, Δ, D, a)` be a basepoint-free datum and `m` a natural
number with `H⁰(X, mD) ≠ 0`. Then there is an `m`-adapted resolution
`(f; F_1, …, F_s; a_•; p_•; r_•)` of `(X, Δ, D, a)`. -/
@[mmp "lem_mmp_foundation_km3a_bpf_log_resolution_with_snc_containment"]
public theorem IsBasepointFreeDatum.exists_isBasepointFreeAdaptedResolution
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {D : Divisor X} {a : ℚ}
    (h : IsBasepointFreeDatum sX n K Δ D a) {m : ℕ}
    (hm : ∃ σ : (m • D).divisorialSubmodule ⊤, σ ≠ 0) :
    ∃ (Y : Scheme.{0}) (_ : IsLocallyNoetherian Y) (_ : IsNormal Y) (_ : CompactSpace Y)
      (f : Y ⟶ X) (s : ℕ) (F : Fin s → PrimeDivisor Y) (aj pj : Fin s → ℚ) (rj : Fin s → ℕ),
      IsBasepointFreeAdaptedResolution sX n K Δ D a m f F aj pj rj := by
  classical
  have : MMP.Mori.IsProperVariety k sX := h.isProperVariety
  have hX : IsNormalVariety k sX := h.isKltPair.1.1
  set M : Divisor X := m • D
  have hMc : M.IsCartier := h.isCartier.nsmul m
  have hZc : ∀ (σ : M.divisorialSubmodule ⊤) (hσ : σ ≠ 0), (M.zeroDivisor σ hσ).IsCartier :=
    fun σ hσ => (Divisor.isCartier_principalDivisor _).add hMc
  -- the base ideal of `|mD|`
  set I : X.IdealSheafData := ⨆ σ : {σ : M.divisorialSubmodule ⊤ // σ ≠ 0},
    effIdeal (M.zeroDivisor σ.1 σ.2) (Divisor.zeroDivisor_nonneg M σ.1 σ.2) with hIdef
  have hle : ∀ σ : {σ : M.divisorialSubmodule ⊤ // σ ≠ 0},
      effIdeal (M.zeroDivisor σ.1 σ.2) (Divisor.zeroDivisor_nonneg M σ.1 σ.2) ≤ I :=
    fun σ => le_iSup (fun σ : {σ : M.divisorialSubmodule ⊤ // σ ≠ 0} =>
      effIdeal (M.zeroDivisor σ.1 σ.2) (Divisor.zeroDivisor_nonneg M σ.1 σ.2)) σ
  have hI : I ≠ ⊥ := by
    obtain ⟨σ, hσ⟩ := hm
    exact fun hbot => effIdeal_ne_bot_of_isCartier _ (hZc σ hσ)
      (le_bot_iff.mp ((hle ⟨σ, hσ⟩).trans hbot.le))
  obtain ⟨Y, f, hLR, hproj, hYln, hYn, hYc, DI, hDI0, -, hIDI, Fs, hsnc, hsub, hBsupp, fB, p,
    hfB, hp, hA⟩ := exists_isLogResolution_isAmple_pullback_sub_sum sX Δ I hI
      (a • Divisor.toQDivisor D - Divisor.toQDivisor K - Δ) h.isNef_sub h.isBig_sub
  have hfres : IsSmoothResolution sX f := hLR.toIsSmoothResolution
  obtain ⟨hY, -, -⟩ := hfres.isNormalVariety hX
  have : IsIntegral Y := hY.1.toIsIntegral
  have : IsProper f := hfres.isProper
  have : IsDominant f := hfres.isBirationalMorphism.isDominant
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  have : AlgebraicGeometry.IsVariety k sX := hX.1
  have : AlgebraicGeometry.IsVariety k (f ≫ sX) := hY.1
  -- re-indexing the components of the snc divisor
  set s := Fs.card
  let e := Fs.equivFin
  let F : Fin s → MMP.Mori.PrimeDivisor Y := fun j => (e.symm j : MMP.Mori.PrimeDivisor Y)
  have hFmem : ∀ j, F j ∈ Fs := fun j => (e.symm j).2
  have hFinj : Function.Injective F := Subtype.val_injective.comp e.symm.injective
  have hsumF : ∀ {R : Type} [AddCommMonoid R] (c : MMP.Mori.PrimeDivisor Y → R),
      ∑ j, Finsupp.single (F j) (c (F j)) = ∑ E ∈ Fs, Finsupp.single E (c E) :=
    fun c => by
      rw [← Finset.sum_coe_sort Fs]
      exact e.symm.sum_comp (fun x : Fs => Finsupp.single (x : MMP.Mori.PrimeDivisor Y) (c x))
  have hmemF : ∀ E : MMP.Mori.PrimeDivisor Y,
      E.genericPoint ∈ ⋃ E' ∈ Fs, (E'.support : Set Y) → E ∈ Fs := fun E hE => by
    obtain ⟨E', hE', hgen⟩ := Set.mem_iUnion₂.mp hE
    rwa [MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hgen] at hE'
  have hsumEq : ∀ {R : Type} [AddCommMonoid R] (G : DivisorWithCoeffs R Y),
      (∀ E ∈ G.support, E ∈ Fs) → G = ∑ E ∈ Fs, Finsupp.single E (G E) :=
    fun G hG => G.sum_single.symm.trans
      (G.sum_of_support_subset hG _ fun _ _ => Finsupp.single_zero _)
  -- the crepant boundary
  obtain ⟨⟨ΔY, hΔY, -⟩, -⟩ := IsPair.existsUnique_isCrepantBoundary h.isKltPair.1.isPair
    h.isKltPair.1.2.1 f hY hfres.isBirationalMorphism
  have hΔYeq : ΔY = ∑ E ∈ Fs, Finsupp.single E (ΔY E) := hsumEq ΔY fun G hG => hmemF G
    (hsub (Or.inl (genericPoint_mem_exceptionalSet_or_mem_of_mem_support h.isKltPair.1 hY
      hfres.isBirationalMorphism hΔY hG)))
  set aj : Fin s → ℚ := fun j => -ΔY (F j)
  have haj : -∑ j, Finsupp.single (F j) (aj j) = ΔY := by
    simp only [aj, Finsupp.single_neg, Finset.sum_neg_distrib, neg_neg]
    rw [hsumF ΔY]
    exact hΔYeq.symm
  have haj1 : ∀ j, -1 < aj j := fun j => by
    have := MMP.Positivity.IsKltPair.coeff_lt_one_of_isCrepantBoundary h.isKltPair hY
      hfres.isBirationalMorphism hΔY (F j)
    rw [DivisorWithCoeffs.coeff_apply] at this
    simp only [aj]
    linarith
  -- the coefficients `p_j`
  have hpos : ∀ j, 0 < 1 + aj j := fun j => by linarith [haj1 j]
  have hq : ∀ j, 0 < p (F j) / (1 + aj j) := fun j => div_pos (hp _ (hFmem j)) (hpos j)
  obtain ⟨N, hN⟩ := exists_nat_gt (∑ j, p (F j) / (1 + aj j))
  have hterm : ∀ j, p (F j) / (1 + aj j) < N := fun j =>
    lt_of_le_of_lt (Finset.single_le_sum (fun i _ => (hq i).le) (Finset.mem_univ j)) hN
  have hN0 : 0 < N := by
    exact_mod_cast lt_of_le_of_lt (Finset.sum_nonneg fun i _ => (hq i).le) hN
  have hN0' : (0 : ℚ) < N := by exact_mod_cast hN0
  set pj : Fin s → ℚ := fun j => p (F j) / N
  -- the coefficients `r_j`
  set DI' : AlgebraicGeometry.PrimeDivisor Y → ℕ := fun E => (DI E).toNat
  have hDIfin : (Function.support DI').Finite := DI.support.finite_toSet.subset fun E hE => by
    simp only [Function.mem_support, DI', ne_eq] at hE
    simp only [Finset.mem_coe, Finsupp.mem_support_iff]
    intro h0
    rw [h0] at hE
    exact hE rfl
  set rj : Fin s → ℕ := fun j => DI' (F j)
  have hDIeq : ∑ j, Finsupp.single (F j) (rj j : ℤ) = DI := by
    have h1 := hsumF (fun E => ((DI' E : ℕ) : ℤ))
    rw [show (∑ j, Finsupp.single (F j) (rj j : ℤ)) =
      ∑ j, Finsupp.single (F j) ((DI' (F j) : ℕ) : ℤ) from rfl, h1]
    conv_rhs => rw [hsumEq DI fun E hE => hmemF E (hsub (Or.inr (by
      rw [DivisorWithCoeffs.coe_supp]
      exact Set.mem_iUnion₂.2 ⟨E, hE, MMP.Flips.primeDivisor_genericPoint_mem_support E⟩)))]
    refine Finset.sum_congr rfl fun E _ => ?_
    simp only [DI', Int.toNat_of_nonneg (hDI0 E)]
  -- the zero divisors of the sections and their pull-backs
  have hBσ : ∀ (σ : M.divisorialSubmodule ⊤) (hσ : σ ≠ 0) (Z : irreducibleComponents Y),
      f (componentGenericPoint Y Z) ∉ (M.zeroDivisor σ hσ).supp := fun σ hσ =>
    MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant f _
  have hcomap : ∀ (σ : M.divisorialSubmodule ⊤) (hσ : σ ≠ 0),
      (effIdeal (M.zeroDivisor σ hσ) (Divisor.zeroDivisor_nonneg M σ hσ)).comap f ≤
        MMP.Resolution.divisorIdeal DI' := fun σ hσ => by
    rw [← hIDI]
    exact (Scheme.IdealSheafData.map_gc f).monotone_l (hle ⟨σ, hσ⟩)
  have hloc : ∀ (σ : M.divisorialSubmodule ⊤) (hσ : σ ≠ 0) (y : Y), ∃ g : Y.presheaf.stalk y,
      IdealSheafData.stalk ((effIdeal (M.zeroDivisor σ hσ)
        (Divisor.zeroDivisor_nonneg M σ hσ)).comap f) y = Ideal.span {g} ∧
      ∀ (E : MMP.Mori.PrimeDivisor Y) (hyE : y ∈ E.support),
        E.valuation (E.toComponent.hom (Y.presheaf.stalkSpecializes
          (MMP.Resolution.Aux.genericPoint_specializes_of_mem_support E hyE) g)) =
          WithZero.exp (((M.zeroDivisor σ hσ).pullback (hZc σ hσ) (hBσ σ hσ)).coeff E) :=
    fun σ hσ => exists_stalk_comap_effIdeal_eq_span f _ (hZc σ hσ) (hBσ σ hσ)
  refine ⟨Y, hYln, hYn, hYc, f, s, F, aj, pj, rj,
    { toIsBasepointFreeDatum := h
      exists_section_ne_zero := hm
      isLogResolution := hLR
      isProjectiveVariety := hproj
      injective := hFinj
      isSNC := ?_
      subset_iUnion := ?_
      isCrepantBoundary := ⟨hY, by rw [haj]; exact hΔY⟩
      pos_p := fun j => div_pos (hp _ (hFmem j)) hN0'
      lt_one_add := fun j => by
        have h1 := hterm j
        rw [div_lt_iff₀ (hpos j)] at h1
        change p (F j) / N < 1 + aj j
        rw [div_lt_iff₀ hN0']
        linarith [mul_comm (N : ℚ) (1 + aj j)]
      isAmple := ?_
      le_zeroDivisor := ?_
      exists_notMem_supp := ?_ }⟩
  · convert hsnc using 1
    exact hsumF (fun _ => (1 : ℤ))
  · intro x hx
    obtain ⟨E, hE, hxE⟩ := Set.mem_iUnion₂.mp (hsub (Or.inl hx))
    exact Set.mem_iUnion.mpr ⟨e ⟨E, hE⟩, by simpa [F] using hxE⟩
  · -- (iv) ampleness of `f^*B - ∑ p_j F_j`
    refine ⟨hBsupp, fB, hfB, ?_⟩
    have : MMP.Mori.IsProjectiveVariety k (f ≫ sX) := hproj
    have hsum : ∑ j, Finsupp.single (F j) (pj j) =
        (N : ℚ)⁻¹ • ∑ E ∈ Fs, Finsupp.single E (p E) := by
      rw [show (∑ j, Finsupp.single (F j) (pj j)) =
        ∑ j, Finsupp.single (F j) ((fun E => p E / N) (F j)) from rfl,
        hsumF (fun E => p E / (N : ℚ)), Finset.smul_sum]
      refine Finset.sum_congr rfl fun E _ => ?_
      rw [Finsupp.smul_single, smul_eq_mul, div_eq_inv_mul]
    rw [hsum]
    exact isAmple_sub_inv_natCast_smul (f ≫ sX) (isNef_of_isPullback rfl h.isNef_sub hfB) hA hN0
      (MMP.Fourfold.isQCartier_of_isSmoothScheme hfres.isSmoothScheme _)
  · -- (v) the pulled-back zero divisors contain the fixed part
    intro σ hσ
    refine ⟨hBσ σ hσ, (M.zeroDivisor σ hσ).pullback (hZc σ hσ) (hBσ σ hσ),
      Divisor.isPullback_pullback (hZc σ hσ) (hBσ σ hσ), ?_⟩
    rw [hDIeq]
    intro E
    obtain ⟨g, hgs, hgv⟩ := hloc σ hσ E.genericPoint
    have hyE : E.genericPoint ∈ E.support := MMP.Flips.primeDivisor_genericPoint_mem_support E
    have hmem := MMP.Resolution.stalk_le_stalk_of_le (hcomap σ hσ) E.genericPoint
      (hgs ▸ Ideal.mem_span_singleton_self g)
    rw [stalk_divisorIdeal_genericPoint DI' hDIfin E] at hmem
    have h1 := ordGE_toComponent_of_mem_pow E hmem
    have h2 := hgv E hyE
    rw [TopCat.Presheaf.stalkSpecializes_refl, CategoryTheory.id_apply] at h2
    rcases h1 with h0 | h1
    · rw [h0, map_zero] at h2
      exact absurd h2.symm WithZero.exp_ne_zero
    · rw [h2, WithZero.exp_le_exp] at h1
      rw [← Int.toNat_of_nonneg (hDI0 E)]
      exact h1
  · -- (v) at every point some pulled-back zero divisor has no extra component
    intro y
    have hPc := isEffectiveCartierDivisor_divisorIdeal (f ≫ sX) hfres.isSmoothScheme DI' hDIfin
    obtain ⟨h₀, hreg, hPy⟩ :=
      AlgebraicGeometry.exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor _ hPc y
    choose gσ hgσs hgσv using fun σ : {σ : M.divisorialSubmodule ⊤ // σ ≠ 0} => hloc σ.1 σ.2 y
    have hsup : IdealSheafData.stalk (MMP.Resolution.divisorIdeal DI') y =
        ⨆ σ, Ideal.span {gσ σ} := by
      have hc := (Scheme.IdealSheafData.map_gc f).l_iSup
        (f := fun σ : {σ : M.divisorialSubmodule ⊤ // σ ≠ 0} =>
          effIdeal (M.zeroDivisor σ.1 σ.2) (Divisor.zeroDivisor_nonneg M σ.1 σ.2))
      rw [← hIDI, hIdef, hc, stalk_iSup]
      exact iSup_congr hgσs
    obtain ⟨σ, hσ⟩ := exists_span_singleton_eq_of_span_eq_iSup hreg.2 (hPy.symm.trans hsup)
    refine ⟨σ.1, σ.2, hBσ σ.1 σ.2, _, Divisor.isPullback_pullback (hZc σ.1 σ.2) (hBσ σ.1 σ.2),
      ?_⟩
    rw [hDIeq]
    intro hy
    obtain ⟨E, hE, hyE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hy
    apply hE
    have hsp := MMP.Resolution.Aux.genericPoint_specializes_of_mem_support E hyE
    have h1 : Ideal.span {Y.presheaf.stalkSpecializes hsp (gσ σ)} =
        IsLocalRing.maximalIdeal (Y.presheaf.stalk E.genericPoint) ^ DI' E := by
      rw [← stalk_divisorIdeal_genericPoint DI' hDIfin E,
        MMP.Resolution.Aux.stalk_eq_map_stalkSpecializes _ hsp, hPy, ← hσ, Ideal.map_span,
        Set.image_singleton]
    have h2 := valuation_toComponent_of_span_eq E h1
    rw [hgσv σ E hyE] at h2
    rw [DivisorWithCoeffs.coeff_sub, WithZero.exp_injective h2, DivisorWithCoeffs.coeff_apply,
      Int.toNat_of_nonneg (hDI0 E), sub_self]

/-! ### Reduction of non-vanishing to smooth data -/

section Helpers

variable {k : Type} [Field k] {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

omit [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral Y] [IsLocallyNoetherian Y]
  [IsNormal Y] in
/-- For a proper birational morphism `g : Y ⟶ X` of varieties with `X` normal, every prime divisor
`P` of `X` has a strict transform `P' = g⁻¹_* P`; the generic point of `P'` lies over that of
`P` and `g` induces an isomorphism `𝒪_{X,P} ≅ 𝒪_{Y,P'}`. -/
private theorem map_genericPoint_eq_and_isIso_of_inverseTransformPrimeDivisor_eq_some
    (sX : X ⟶ Spec (.of k)) (g : Y ⟶ X) (hX : MMP.Mori.IsVariety k sX)
    (hY : MMP.Mori.IsVariety k (g ≫ sX)) [IsProper g] (hg : IsBirationalMorphism g)
    {P : MMP.Mori.PrimeDivisor X} {P' : MMP.Mori.PrimeDivisor Y}
    (hPP' : inverseTransformPrimeDivisor g P = some P') :
    g P'.genericPoint = P.genericPoint ∧ IsIso (g.stalkMap P'.genericPoint) := by
  obtain ⟨V, hV2, hVi⟩ := exists_isIso_morphismRestrict_two_le_closedsCodimension k sX (g ≫ sX)
    ⟨hX, ‹IsNormal X›⟩ hY g rfl hg
  have hP : P.genericPoint ∈ biregularLocus g := by
    refine le_biregularLocus hVi ?_
    by_contra hP
    have hsub : ((TopologicalSpace.IrreducibleCloseds.closureSingleton P.genericPoint :
        TopologicalSpace.IrreducibleCloseds X) : Set X) ⊆ (V.compl : Set X) :=
      closure_minimal (Set.singleton_subset_iff.mpr hP) V.compl.isClosed
    have h4 := le_closedsCodimension_iff.mp hV2 _ hsub
    rw [codimension_eq_coheight, show TopologicalSpace.IrreducibleCloseds.closureSingleton
        P.genericPoint = (irreducibleSetEquivPoints (α := X)).symm P.genericPoint from rfl,
      Order.coheight_orderIso, P.coheight_genericPoint] at h4
    exact absurd h4 (by decide)
  have := hg.isDominant
  obtain ⟨y, hy⟩ := g.surjective P.genericPoint
  have hco : Order.coheight y = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus g (hy ▸ hP), hy]
    exact P.coheight_genericPoint
  set P'' : MMP.Mori.PrimeDivisor Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hco
  have hgen : P''.genericPoint = y :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne y hco
  have hη : g P''.genericPoint = P.genericPoint := by rw [hgen, hy]
  have hV : g P''.genericPoint ∈ biregularLocus g := hη ▸ hP
  have h'' := MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint
    hη hV
  obtain rfl : P' = P'' := Option.some.inj (hPP'.symm.trans h'')
  exact ⟨hη, MMP.Threefold.Resolution.isIso_stalkMap_of_mem_biregularLocus g hV⟩

/-- A discrepancy `a(E, X, Δ)` of a divisor `(Y, f, E)` over `X` whose centre is the generic
point of a prime divisor `P` of `X` is `-coeff_P(Δ)`. -/
private theorem eq_neg_coeff_of_map_genericPoint_eq [PerfectField k] {sX : X ⟶ Spec (.of k)}
    (hX : MMP.Mori.IsNormalVariety k sX) {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    {D : MMP.Mori.DivisorOver k sX} {P : MMP.Mori.PrimeDivisor X}
    (hP : D.f D.E.genericPoint = P.genericPoint) {a : ℚ}
    (h : MMP.Mori.IsDiscrepancy sX n K Δ D a) : a = -Δ.coeff P := by
  obtain ⟨hX', hK, m, hm, hC, U, hU, τ, hτ, hτa⟩ := h
  refine MMP.Mori.IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hX (P := P)
    ⟨hX', hK, m, hm, hC, U, ?_, τ, hτ, ?_⟩
  · convert hU using 2
    exact hP.symm
  · rw [hτa, MMP.Threefold.Mori.ModelIndependence.ordPullback_eq_of_valuation_eq hX
      hK.topologicalKrullDim_eq
      (MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq hX D P hP)]

omit [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] in
/-- Along a prime divisor `E` of `Y` lying over the generic point of a prime divisor `P` of `X`,
the crepant boundary of `(X, Δ)` on `Y` has the coefficient `coeff_P(Δ)`. -/
private theorem coeff_eq_of_isCrepantBoundary [PerfectField k] {sX : X ⟶ Spec (.of k)}
    (hX : MMP.Mori.IsNormalVariety k sX) {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {f : Y ⟶ X}
    {hY : MMP.Mori.IsNormalVariety k (f ≫ sX)} {hf : IsBirationalMorphism f} {ΔY : QDivisor Y}
    (hΔ : MMP.Mori.IsCrepantBoundary sX n K Δ f hY hf ΔY) {E : MMP.Mori.PrimeDivisor Y}
    {P : MMP.Mori.PrimeDivisor X} (hP : f E.genericPoint = P.genericPoint) :
    ΔY.coeff E = Δ.coeff P :=
  neg_inj.mp (eq_neg_coeff_of_map_genericPoint_eq hX (D := ⟨Y, f, hY, hf, E⟩) hP (hΔ E))

omit [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] in
/-- The crepant boundary of `(X, Δ)` on `Y` vanishes along a prime divisor `E` of `Y` whose
generic point maps into the biregular locus of `f` and outside `Supp Δ`. -/
private theorem coeff_eq_zero_of_isCrepantBoundary [PerfectField k] {sX : X ⟶ Spec (.of k)}
    (hX : MMP.Mori.IsNormalVariety k sX) {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {f : Y ⟶ X}
    {hY : MMP.Mori.IsNormalVariety k (f ≫ sX)} {hf : IsBirationalMorphism f} {ΔY : QDivisor Y}
    (hΔ : MMP.Mori.IsCrepantBoundary sX n K Δ f hY hf ΔY) {E : MMP.Mori.PrimeDivisor Y}
    (hE : f E.genericPoint ∈ biregularLocus f) (hΔE : f E.genericPoint ∉ (Δ.supp : Set X)) :
    ΔY.coeff E = 0 := by
  have hco : Order.coheight (f E.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f hE, E.coheight_genericPoint]
  set P : MMP.Mori.PrimeDivisor X := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco
  have hP : P.genericPoint = f E.genericPoint :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco
  rw [coeff_eq_of_isCrepantBoundary hX hΔ hP.symm]
  by_contra hc
  exact hΔE (DivisorWithCoeffs.mem_supp_iff.mpr
    ⟨P, hc, hP ▸ MMP.Flips.primeDivisor_genericPoint_mem_support P⟩)

end Helpers

/-- The coefficients of the `ℚ`-divisor `∑_{E ∈ s} p_E E`. -/
private theorem coeff_sum_single {X : Scheme.{0}} [DecidableEq (MMP.Mori.PrimeDivisor X)]
    (s : Finset (MMP.Mori.PrimeDivisor X)) (p : MMP.Mori.PrimeDivisor X → ℚ)
    (E : MMP.Mori.PrimeDivisor X) :
    (∑ E ∈ s, Finsupp.single E (p E) : QDivisor X).coeff E = if E ∈ s then p E else 0 := by
  rw [DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply]

/-- For finitely many `δ_i < 1` and `p_i ≥ 0` there is a natural number `q > 0`
with `p_i / q < 1 - δ_i` for all `i`. -/
private theorem exists_pos_nat_div_lt_one_sub {ι : Type*} (s : Finset ι) {p δ : ι → ℚ}
    (hp : ∀ i ∈ s, 0 ≤ p i) (hδ : ∀ i ∈ s, δ i < 1) :
    ∃ q : ℕ, 0 < q ∧ ∀ i ∈ s, p i / q < 1 - δ i := by
  set M : ℚ := ∑ i ∈ s, p i / (1 - δ i)
  refine ⟨⌈M⌉₊ + 1, Nat.succ_pos _, fun i hi => ?_⟩
  have hle : p i / (1 - δ i) ≤ M :=
    Finset.single_le_sum (f := fun i => p i / (1 - δ i))
      (fun j hj => div_nonneg (hp j hj) (by linarith [hδ j hj])) hi
  have hMq : M < ((⌈M⌉₊ + 1 : ℕ) : ℚ) := by push_cast; linarith [Nat.le_ceil M]
  exact (div_lt_comm₀ (by positivity) (by linarith [hδ i hi])).mpr (hle.trans_lt hMq)

section QPullback

variable {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y}

/-- A `ℚ`-divisor `B'` is the pull-back of `B` as soon as, for one `m > 0` with `mB` a Cartier
divisor `A`, the divisor `mB'` is the pull-back of `A`. -/
private theorem isPullback_of_isPullback_toQDivisor_eq_smul {B : QDivisor Y}
    {hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp}
    {B' : QDivisor X} {m : ℕ} (hm : 0 < m) {A : Divisor Y}
    (hA : Divisor.toQDivisor A = (m : ℤ) • B) (hAc : A.IsCartier)
    {hA0 : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ A.supp}
    {A' : Divisor X} (hA' : Divisor.toQDivisor A' = (m : ℤ) • B') (hp : A.IsPullback f hA0 A') :
    B.IsPullback f hB B' := by
  have hBq : B.IsQCartier := ⟨m, by exact_mod_cast hm.ne', A, hA, hAc⟩
  have hP := QDivisor.isPullback_pullback hBq hB
  obtain ⟨A'', hA'', hp''⟩ := hP m hm A hA hAc
  have hAA : A'' = A' := hp''.eq hAc hp
  have heq : B.pullback hBq hB = B' := by
    ext E
    have h1 := congrArg (fun G : QDivisor X => G.coeff E) (hA''.symm.trans (hAA ▸ hA'))
    simp only [DivisorWithCoeffs.coeff_smul, zsmul_eq_mul, Int.cast_natCast] at h1
    exact mul_left_cancel₀ (by exact_mod_cast hm.ne') h1
  rw [← heq]
  exact hP

/-- Pull-back commutes with rational multiples: `f^*(cB) = c f^*B` for a `ℚ`-Cartier `B`; and
`cB` is `ℚ`-Cartier. -/
private theorem isQCartier_smul_and_isPullback_smul {B : QDivisor Y} (hBq : B.IsQCartier)
    {hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp}
    {B' : QDivisor X} (hp : B.IsPullback f hB B') (c : ℚ)
    (hcB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ (c • B).supp) :
    (c • B).IsQCartier ∧ (c • B).IsPullback f hcB (c • B') := by
  obtain ⟨m, hm, A, hA, hAc⟩ := hBq.exists_pos
  obtain ⟨A', hA', hpA⟩ := hp m hm A hA hAc
  have hden : (0 : ℚ) < c.den := by exact_mod_cast c.den_pos
  have hc : (c.den : ℚ) * c = c.num := by rw [mul_comm, Rat.mul_den_eq_num]
  set N : ℕ := c.den * m
  have hN : 0 < N := Nat.mul_pos c.den_pos hm
  have hNA : Divisor.toQDivisor (c.num • A) = (N : ℤ) • (c • B) := by
    rw [map_zsmul, hA, ← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ,
      ← Int.cast_smul_eq_zsmul ℚ, smul_smul, smul_smul, ← hc]
    congr 1
    simp only [N]
    push_cast
    ring
  have hNA' : Divisor.toQDivisor (c.num • A') = (N : ℤ) • (c • B') := by
    rw [map_zsmul, hA', ← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ,
      ← Int.cast_smul_eq_zsmul ℚ, smul_smul, smul_smul, ← hc]
    congr 1
    simp only [N]
    push_cast
    ring
  have hAsupp : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ A.supp :=
    fun Z hZ => hB Z (by
      rwa [QDivisor.supp_eq_of_toQDivisor_eq (by exact_mod_cast hm.ne') hA] at hZ)
  have hNsupp : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ (c.num • A).supp :=
    fun Z hZ => hAsupp Z (by
      rw [← Divisor.supp_toQDivisor, map_zsmul] at hZ
      by_cases h0 : c.num = 0
      · rw [h0, zero_smul, DivisorWithCoeffs.supp_zero] at hZ
        have hZ' := SetLike.mem_coe.mpr hZ
        rw [TopologicalSpace.Closeds.coe_bot] at hZ'
        exact hZ'.elim
      · rwa [QDivisor.supp_zsmul h0, Divisor.supp_toQDivisor] at hZ)
  have hNAc : (c.num • A).IsCartier := hAc.zsmul _
  refine ⟨⟨N, by exact_mod_cast hN.ne', _, hNA, hNAc⟩, ?_⟩
  exact isPullback_of_isPullback_toQDivisor_eq_smul hN hNA hNAc hNA'
    (hpA.zsmul hAc c.num hNsupp)

/-- Pull-back of `ℚ`-Cartier `ℚ`-divisors is additive. -/
private theorem isPullback_add_of_isQCartier {G₁ G₂ : QDivisor Y}
    (hG₁ : G₁.IsQCartier) (hG₂ : G₂.IsQCartier)
    {h₁ : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ G₁.supp}
    {h₂ : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ G₂.supp}
    {R₁ R₂ : QDivisor X} (p₁ : G₁.IsPullback f h₁ R₁) (p₂ : G₂.IsPullback f h₂ R₂)
    (h : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ (G₁ + G₂).supp) :
    (G₁ + G₂).IsPullback f h (R₁ + R₂) := by
  obtain ⟨m₁, hm₁, A₁, hA₁, hA₁c⟩ := hG₁.exists_pos
  obtain ⟨m₂, hm₂, A₂, hA₂, hA₂c⟩ := hG₂.exists_pos
  obtain ⟨A₁', hA₁', p₁'⟩ := p₁ m₁ hm₁ A₁ hA₁ hA₁c
  obtain ⟨A₂', hA₂', p₂'⟩ := p₂ m₂ hm₂ A₂ hA₂ hA₂c
  have hsupp : ∀ {G : QDivisor Y} (A : Divisor Y) (c : ℤ), c ≠ 0 →
      Divisor.toQDivisor A = c • G →
      (∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ G.supp) →
      ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ A.supp :=
    fun A c hc hA hG W hW => hG W (by rwa [QDivisor.supp_eq_of_toQDivisor_eq hc hA] at hW)
  set N : ℕ := m₁ * m₂
  have hN : 0 < N := Nat.mul_pos hm₁ hm₂
  have hN' : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  have hA₁N : Divisor.toQDivisor ((m₂ : ℤ) • A₁) = (N : ℤ) • G₁ := by
    simp only [map_zsmul, hA₁, smul_smul, N]
    congr 1
    push_cast
    ring
  have hA₂N : Divisor.toQDivisor ((m₁ : ℤ) • A₂) = (N : ℤ) • G₂ := by
    simp only [map_zsmul, hA₂, smul_smul, N]
    push_cast
    ring_nf
  have hsum : Divisor.toQDivisor ((m₂ : ℤ) • A₁ + (m₁ : ℤ) • A₂) = (N : ℤ) • (G₁ + G₂) := by
    rw [map_add, hA₁N, hA₂N, smul_add]
  have hsum' : Divisor.toQDivisor ((m₂ : ℤ) • A₁' + (m₁ : ℤ) • A₂') = (N : ℤ) • (R₁ + R₂) := by
    simp only [map_add, map_zsmul, hA₁', hA₂', smul_smul, smul_add, N]
    congr 2
    push_cast
    ring
  have pA := (p₁'.zsmul hA₁c (m₂ : ℤ) (hsupp _ _ hN' hA₁N h₁)).add (hA₁c.zsmul _)
    (hA₂c.zsmul _) (hsupp _ _ hN' hsum h) (p₂'.zsmul hA₂c (m₁ : ℤ) (hsupp _ _ hN' hA₂N h₂))
  exact isPullback_of_isPullback_toQDivisor_eq_smul hN hsum ((hA₁c.zsmul _).add (hA₂c.zsmul _))
    hsum' pA

end QPullback

/-- **Reduction of non-vanishing to smooth data** (Kollár–Mori 3.5). Over an algebraically
closed field of characteristic `0`, if every smooth non-vanishing datum of dimension `n` has the
non-vanishing property, then every non-vanishing datum `(X, D, G, a)` of dimension `n` has it. -/
@[mmp "lem_mmp_foundation_km3a_nonvanishing_reduction_with_snc_containment"]
public theorem IsNonvanishingDatum.hasNonvanishingProperty_of_isSmoothNonvanishingDatum
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {n : ℕ}
    (H : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
      [CompactSpace Y] (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY] (KY DY : Divisor Y)
      (GY : QDivisor Y) (aY : ℚ),
      IsSmoothNonvanishingDatum sY n KY DY GY aY → HasNonvanishingProperty DY GY)
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {K D : Divisor X} {G : QDivisor X} {a : ℚ}
    (h : IsNonvanishingDatum sX n K D G a) :
    HasNonvanishingProperty D G := by
  classical
  have : AlgebraicGeometry.IsProperVariety k sX := h.isProperVariety
  set B : QDivisor X := a • Divisor.toQDivisor D + G - Divisor.toQDivisor K with hB_def
  obtain ⟨Y, f, hLR, hproj, hYln, hYn, hYc, DI, -, -, -, Fs, hsnc, hsub, hBf, fB, p, hfB, hp,
    hA⟩ := exists_isLogResolution_isAmple_pullback_sub_sum sX (-G) ⊤ idealSheafData_top_ne_bot B
      h.isNef_add h.isBig_add
  have : AlgebraicGeometry.IsVariety k (f ≫ sX) := hproj.toIsVariety
  have : IsIntegral Y := ‹AlgebraicGeometry.IsVariety k (f ≫ sX)›.toIsIntegral
  have : IsProper f := hLR.isProper
  have hX : IsNormalVariety k sX := ⟨inferInstance, inferInstance⟩
  have hYnv : IsNormalVariety k (f ≫ sX) := ⟨inferInstance, hYn⟩
  have hfb : IsBirationalMorphism f := hLR.isBirationalMorphism
  have : IsDominant f := hfb.isDominant
  have hklt := h.isKltPair
  -- the crepant boundary `Δ'` of `(X, -G)` on `Y`
  obtain ⟨Δ', hΔ'⟩ :=
    (hklt.isPair.existsUnique_isCrepantBoundary hklt.1.2.1 f hYnv hfb).1.exists
  -- the canonical divisor `K_Y = div(f^*ω)`
  obtain ⟨ω, hω0, hωK⟩ : ∃ ω : RationalPluriForms sX n 1, ω ≠ 0 ∧ divisorOfForm ω = K := by
    obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hklt.1.2.1
    exact ⟨ω, hω0, Finsupp.ext hω⟩
  set KY : Divisor Y := divisorOfForm (pullbackRationalPluriForms sX f ω)
  have hKY : KY.IsCanonicalDivisor (f ≫ sX) n := by
    have hn := hklt.1.2.1.topologicalKrullDim_eq
    obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (f ≫ sX)
      hLR.isSmoothScheme
      ((MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (f ≫ sX) hfb).symm.trans
        hn)
    exact hK₀.of_linearlyEquivalent <| by
      simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hYnv hK₀
        (MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' f
          hfb.functionFieldMap_bijective (toNat_trdeg_functionField_of_topologicalKrullDim_eq hn)
          hω0)
  obtain ⟨-, -, hBKG, hKG⟩ := hklt.isPair.isPullback_of_isCrepantBoundary f hYnv hfb
    hklt.1.2.1 hKY (Or.inl ⟨ω, hω0, hωK, rfl⟩) hΔ'
  -- the pull-back `D'` of `D`
  have hBD : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ D.supp :=
    MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant f D
  obtain ⟨D', hD'⟩ := h.isCartier.exists_isPullback hBD
  -- strict transforms of prime divisors of `X`
  have hstrict : ∀ (P : MMP.Mori.PrimeDivisor X) (P' : MMP.Mori.PrimeDivisor Y),
      inverseTransformPrimeDivisor f P = some P' →
        f P'.genericPoint = P.genericPoint ∧ IsIso (f.stalkMap P'.genericPoint) :=
    fun P P' hPP' => map_genericPoint_eq_and_isIso_of_inverseTransformPrimeDivisor_eq_some sX f
      hX.1 hYnv.1 hfb hPP'
  -- the coefficients of `Δ'`
  have hΔF : ∀ E, E ∉ Fs → Δ'.coeff E = 0 := by
    intro E hE
    have hη : E.genericPoint ∉ ⋃ E' ∈ Fs, PrimeDivisor.support E' := by
      simp only [Set.mem_iUnion]
      rintro ⟨E', hE', hmem⟩
      exact hE (MMP.Flips.eq_of_genericPoint_mem_primeDivisor_support hmem ▸ hE')
    exact coeff_eq_zero_of_isCrepantBoundary hX hΔ'
      (by_contra fun hc => hη (hsub (Or.inl (Or.inl (MMP.Mori.mem_exceptionalSet.mpr hc)))))
      (fun h => hη (hsub (Or.inl (Or.inr h))))
  have hΔP : ∀ (P : MMP.Mori.PrimeDivisor X) (P' : MMP.Mori.PrimeDivisor Y),
      inverseTransformPrimeDivisor f P = some P' → Δ'.coeff P' = -G.coeff P := fun P P' hPP' => by
    rw [coeff_eq_of_isCrepantBoundary hX hΔ' (hstrict P P' hPP').1, DivisorWithCoeffs.coeff_neg]
  -- the twist `t = 1 / q`
  obtain ⟨q, hq, hqF⟩ := exists_pos_nat_div_lt_one_sub Fs (fun E hE => (hp E hE).le)
    (fun E _ => MMP.Positivity.IsKltPair.coeff_lt_one_of_isCrepantBoundary hklt hYnv hfb hΔ' E)
  set S : QDivisor Y := ∑ E ∈ Fs, Finsupp.single E (p E) with hS_def
  set G'' : QDivisor Y := -Δ' - (q : ℚ)⁻¹ • S with hG''_def
  have hgen : ∀ C : QDivisor X, ∀ Z : irreducibleComponents Y,
      f (componentGenericPoint Y Z) ∉ C.supp := fun C Z =>
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' f C Z
  have hfBeq : fB = a • Divisor.toQDivisor D' - (Divisor.toQDivisor KY + Δ') := by
    obtain ⟨hq1, hp1⟩ :=
      isQCartier_smul_and_isPullback_smul (QDivisor.isQCartier_toQDivisor h.isCartier)
      (QDivisor.isPullback_toQDivisor h.isCartier (hgen _) hD') a (hgen _)
    obtain ⟨hq2, hp2⟩ := isQCartier_smul_and_isPullback_smul hklt.1.2.2 hKG (-1) (hgen _)
    have hp3 := isPullback_add_of_isQCartier hq1 hq2 hp1 hp2 (hgen _)
    have heq : a • Divisor.toQDivisor D + (-1 : ℚ) • (Divisor.toQDivisor K + -G) = B := by
      rw [hB_def, neg_one_smul]
      abel
    have hp4 : B.IsPullback f hBf _ := heq ▸ hp3
    rw [(h.isQCartier_add.existsUnique_isPullback hBf).unique hfB hp4, neg_one_smul]
    abel
  have hQ : ∀ L : QDivisor Y, L.IsQCartier :=
    MMP.Fourfold.isQCartier_of_isSmoothScheme hLR.isSmoothScheme
  have : MMP.Mori.IsProjectiveVariety k (f ≫ sX) := hproj
  have hamp : (a • Divisor.toQDivisor D' + G'' - Divisor.toQDivisor KY).IsAmple := by
    convert isAmple_sub_inv_natCast_smul (f ≫ sX) (isNef_of_isPullback rfl h.isNef_add hfB) hA hq
      (hQ _) using 1
    rw [hG''_def, hfBeq]
    module
  -- the smooth datum `(Y, f^*D, G'', a)`
  have hD'c : D'.IsCartier := hD'.isCartier h.isCartier
  have hSF : ∀ E ∈ Fs, S.coeff E = p E := fun E hE => by
    rw [hS_def, coeff_sum_single, ite_eq_left hE]
  have hG''F : ∀ E, E ∉ Fs → G''.coeff E = 0 := by
    intro E hE
    have hS : S.coeff E = 0 := by rw [hS_def, coeff_sum_single, ite_eq_right hE]
    rw [hG''_def, DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_neg,
      DivisorWithCoeffs.coeff_smul, hΔF E hE, hS]
    simp
  have hFsupp : Fs ⊆ (∑ E ∈ Fs, Finsupp.single E (1 : ℤ)).support := by
    intro E hE
    rw [Finsupp.mem_support_iff, Finsupp.finsetSum_apply]
    simp [Finsupp.single_apply, hE]
  have hsuppG : G''.support ⊆ Fs := fun E hE => by
    by_contra hc
    exact (Finsupp.mem_support_iff.mp hE) (hG''F E hc)
  have hcoeffG : ∀ E, (-G'').coeff E < 1 := by
    intro E
    rw [DivisorWithCoeffs.coeff_neg]
    by_cases hE : E ∈ Fs
    · rw [hG''_def, DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_neg,
        DivisorWithCoeffs.coeff_smul, hSF E hE, smul_eq_mul]
      have := hqF E hE
      rw [div_eq_inv_mul] at this
      linarith
    · rw [hG''F E hE]
      norm_num
  have hsncG : (-G'').IsSNC (f ≫ sX) :=
    hsnc.of_support_subset (by rw [Finsupp.support_neg]; exact hsuppG.trans hFsupp)
  have hnb := QDivisor.isNef_and_isBig_of_isAmple (f ≫ sX) hamp
  have hsm : IsSmoothNonvanishingDatum (f ≫ sX) n KY D' G'' a :=
    { isProperVariety := inferInstance
      isCartier := hD'c
      isNef := (QDivisor.isNef_toQDivisor_iff (k := k) (sX := f ≫ sX) D' hD'c).mp
        (isNef_of_isPullback rfl
          ((QDivisor.isNef_toQDivisor_iff (k := k) (sX := sX) D h.isCartier).mpr h.isNef)
          (QDivisor.isPullback_toQDivisor h.isCartier (hgen _) hD'))
      isKltPair := isKltPair_of_isSNC (f ≫ sX) hYnv hLR.isSmoothScheme hKY hsncG hcoeffG
      pos := h.pos
      isQCartier_add := hQ _
      isNef_add := hnb.1
      isBig_add := hnb.2
      isSmoothScheme := hLR.isSmoothScheme
      isProjectiveVariety := hproj
      isSNCSubset := Or.inr ⟨G''.support, (DivisorWithCoeffs.coe_supp G'').symm,
        hsnc.of_support_subset (Finsupp.support_finsetSum.trans <| Finset.biUnion_subset.mpr
          fun E hE => Finsupp.support_single_subset.trans
            (Finset.singleton_subset_iff.mpr (hFsupp (hsuppG hE))))⟩
      isAmple := hamp }
  obtain ⟨m₀, hm₀⟩ := H Y (f ≫ sX) KY D' G'' a hsm
  refine ⟨m₀, fun m hm => ?_⟩
  obtain ⟨σ, hσ⟩ := hm₀ m hm
  have hcoeff : ∀ (P : MMP.Mori.PrimeDivisor X) (P' : MMP.Mori.PrimeDivisor Y),
      inverseTransformPrimeDivisor f P = some P' →
        (m • D' + G''.roundUp).coeff P' ≤ (m • D + G.roundUp).coeff P := by
    intro P P' hPP'
    obtain ⟨hη, _⟩ := hstrict P P' hPP'
    have hDD : D'.coeff P' = D.coeff P :=
      MMP.Positivity.coeff_eq_of_isPullback P' P hη h.isCartier hD'
    have hS0 : 0 ≤ S.coeff P' := by
      rw [hS_def, coeff_sum_single]
      split_ifs with hE
      exacts [(hp _ hE).le, le_rfl]
    have hG'' : G''.coeff P' = G.coeff P - (q : ℚ)⁻¹ * S.coeff P' := by
      rw [hG''_def, DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_neg,
        DivisorWithCoeffs.coeff_smul, hΔP P P' hPP', smul_eq_mul]
      ring
    rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
      DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_roundUp,
      DivisorWithCoeffs.coeff_roundUp, hDD, hG'']
    gcongr
    linarith [show 0 ≤ (q : ℚ)⁻¹ * S.coeff P' by positivity]
  obtain ⟨τ, hτ⟩ := Divisor.exists_functionFieldMap_eq_of_isBirationalMorphism sX f hX.1 hYnv.1
    hfb (m • D' + G''.roundUp) (m • D + G.roundUp) hcoeff σ
  refine ⟨τ, fun hτ0 => ?_⟩
  subst hτ0
  refine Divisor.sectionToRationalFunctions_ne_zero hσ
    ((rationalFunctionsEquivFunctionField Y).injective ?_)
  rw [← hτ, map_zero]
  have h0 : Divisor.sectionToRationalFunctions
      (0 : (m • D + G.roundUp).divisorialSubmodule ⊤) = 0 := map_zero _
  rw [h0, map_zero, map_zero]

/-! ### Nef and big plus nef -/

section Multiples

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
  [IsLocallyNoetherian X] [IsNormal X]

/-- A `ℚ`-divisor with a positive multiple that is a Cartier divisor is `ℚ`-Cartier. -/
private theorem isQCartier_of_toQDivisor_eq_smul {B : QDivisor X} {m : ℕ} (hm : 0 < m)
    {F : Divisor X} (hF : F.IsCartier) (h : Divisor.toQDivisor F = (m : ℚ) • B) :
    B.IsQCartier :=
  ⟨m, by exact_mod_cast hm.ne', F, by rw [h, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast], hF⟩

/-- A `ℚ`-divisor `B` with a positive multiple `F = mB` a Cartier divisor is nef if and only if
`F` is. -/
private theorem isNef_iff_of_toQDivisor_eq_smul {B : QDivisor X} {m : ℕ} (hm : 0 < m)
    {F : Divisor X} (hF : F.IsCartier) (h : Divisor.toQDivisor F = (m : ℚ) • B) :
    B.IsNef k sX ↔ F.IsNef k sX := by
  have hB := isQCartier_of_toQDivisor_eq_smul hm hF h
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  have hint : ∀ {C : Scheme.{0}} (i : C ⟶ X) [IsProper (i ≫ sX)]
      (hdim : topologicalKrullDim C ≤ 1),
      B.intersectionNumber k sX i hdim hB = (F.degreeOn k sX i hdim hF : ℚ) / m :=
    fun i _ hdim => QDivisor.intersectionNumber_eq_of_smul k sX i hdim B hB hm F hF
      (by rw [h, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast])
  rw [QDivisor.isNef_iff B hB]
  constructor
  · refine fun H => ⟨hF, fun C i _ _ _ hC => ?_⟩
    have h1 := H C i hC
    rw [hint i hC.le] at h1
    have h2 := mul_nonneg h1 hm'.le
    rw [div_mul_cancel₀ _ hm'.ne'] at h2
    exact_mod_cast h2
  · rintro ⟨_, H⟩ C i _ _ _ hC
    rw [hint i hC.le]
    exact div_nonneg (by exact_mod_cast H C i hC) hm'.le

end Multiples

/-- A `ℚ`-divisor `A` such that `c A` is ample for some natural number `c > 0` is ample. -/
private theorem isAmple_of_natCast_smul {X : Scheme.{0}} [IsLocallyNoetherian X] [CompactSpace X]
    [IsNormal X] {A : QDivisor X} {c : ℕ} (hc : 0 < c) (h : ((c : ℚ) • A).IsAmple) :
    A.IsAmple := by
  obtain ⟨m, hm, D, hD, hDc, hDa⟩ := h
  exact ⟨m * c, Nat.mul_pos hm hc, D, by rw [hD, smul_smul]; push_cast; rfl, hDc, hDa⟩

/-- **Ample plus nef is ample, in multiples.** If `G - P` is ample and `G`, `N` are nef, then
`m G + n N - P = (G - P) + (m - 1) G + n N` is ample for all `m ≥ 1` and `n`. -/
private theorem isAmple_nsmul_add_nsmul_sub {k : Type} [Field k] {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sY] [IsNormal Y] [IsLocallyNoetherian Y]
    [CompactSpace Y] {G N P : QDivisor Y} (hG : G.IsNef k sY)
    (hN : N.IsNef k sY) (hA : (G - P).IsAmple) {m : ℕ} (hm : 1 ≤ m) (n : ℕ) :
    (m • G + n • N - P).IsAmple := by
  set s := (Finset.range (m - 1)).disjSum (Finset.range n)
  set Nf : ℕ ⊕ ℕ → QDivisor Y := Sum.elim (fun _ => G) (fun _ => N)
  have hNf : ∀ i ∈ s, (Nf i).IsNef k sY := by
    rintro (i | i) -
    exacts [hG, hN]
  have hAq : (G - P).IsQCartier := by
    obtain ⟨m, hm, D, hD, hDc, -⟩ := hA
    exact isQCartier_of_toQDivisor_eq_smul hm hDc hD
  have hsum : m • G + n • N - P = (G - P) + ∑ i ∈ s, Nf i := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hm
    simp only [s, Nf, Finset.sum_sumElim, Finset.sum_const, Finset.card_range,
      Nat.add_sub_cancel, succ_nsmul]
    abel
  rw [hsum]
  exact QDivisor.isAmple_of_numericallyEquivalent_add_sum_of_isNef sY s Nf hA hNf
    (QDivisor.NumericallyEquivalent.refl (hAq.add (Finset.sum_induction _ _
      (fun _ _ h h' => h.add h') QDivisor.isQCartier_zero fun i hi => (hNf i hi).isQCartier)))

/-- **The pull-back of a nef Cartier divisor is nef.** For a morphism `g : Y ⟶ X` of proper
varieties with `X` normal, a nef Cartier divisor `H` on `X` and a Cartier divisor `H'` on `Y`
with `𝒪_Y(H') ≅ g^*𝒪_X(H)`, the divisor `H'` is nef. -/
private theorem isNef_of_iso_pullback {k : Type} [Field k] {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} (g : Y ⟶ X) [hX : MMP.Mori.IsProperVariety k sX]
    [hY : MMP.Mori.IsProperVariety k (g ≫ sX)] [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y]
    {H : Divisor X} {H' : Divisor Y} (hH : H.IsNef k sX) (hH'c : H'.IsCartier)
    (e : H'.divisorialSheaf ≅ (Scheme.Modules.pullback g).obj H.divisorialSheaf) :
    H'.IsNef k (g ≫ sX) := by
  have hHc : H.IsCartier := hH.1
  have hXv := ((MMP.Mori.isProperVariety_iff k sX).mp hX).1
  have hYv := ((MMP.Mori.isProperVariety_iff k (g ≫ sX)).mp hY).1
  have : IsIntegral X := hXv.toIsIntegral
  have : IsIntegral Y := hYv.toIsIntegral
  have : QuasiCompact sX := hXv.toQuasiCompact
  have : QuasiCompact (g ≫ sX) := hYv.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (g ≫ sX)
  have := hHc.isInvertibleModule_divisorialSheaf
  have := hH'c.isInvertibleModule_divisorialSheaf
  have : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      ((Scheme.Modules.pullback g).obj H.divisorialSheaf) :=
    MMP.Mori.isInvertible_pullback_obj g _
  rw [Divisor.isNef_iff k _ _ hH'c]
  intro Cv i _ _ _ hCv
  have : AlgebraicGeometry.IsCurve k (i ≫ g ≫ sX) :=
    (AlgebraicGeometry.isCurve_iff k _).mpr ⟨{}, hCv⟩
  rw [degreeOn_eq_of_iso k (g ≫ sX) i hCv.le e]
  by_cases hpt : ∃ x : X, Set.range (i ≫ g) = {x}
  · rw [degreeOn_pullback_divisorialSheaf_eq_zero (g ≫ sX) sX g i rfl H hHc hpt]
  have hc : (i ≫ g) ≫ sX = i ≫ g ≫ sX := Category.assoc _ _ _
  have : IsProper ((i ≫ g) ≫ sX) := by rw [hc]; infer_instance
  have : AlgebraicGeometry.IsCurve k ((i ≫ g) ≫ sX) := by rw [hc]; infer_instance
  have : IsProper (i ≫ g) := IsProper.of_comp (i ≫ g) sX
  have : IsProper ((i ≫ g).imageι ≫ sX) := isProper_imageι_comp (i ≫ g) sX
  have hcurve := isCurve_imageι_comp sX (i ≫ g) hpt
  have : IsIntegral (i ≫ g).image := hcurve.toIsIntegral
  have h := degreeOn_pullback_divisorialSheaf_eq_degreeOver_mul_intersectionNumber
    (g ≫ sX) sX g i rfl H hHc hcurve
  have hHC := ((QDivisor.isNef_toQDivisor_iff (k := k) (sX := sX) H hHc).mpr hH).2 _
    (i ≫ g).imageι hcurve.topologicalKrullDim_eq_one
  exact_mod_cast h ▸ mul_nonneg (by positivity) hHC

/-! ### Sections of isomorphic invertible sheaves -/

section Sections

variable {k : Type u} [Field k]

/-- An `R`-linear equivalence between `R`-modules that are `k`-vector spaces through a ring map
`φ : k →+* R` preserves the `k`-dimension. -/
private theorem finrank_compHom_eq {R : Type u} [CommRing R] (φ : k →+* R) {M N : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (g : M ≃ₗ[R] N) :
    (letI := Module.compHom M φ; Module.finrank k M) =
      (letI := Module.compHom N φ; Module.finrank k N) := by
  let := Module.compHom M φ
  let := Module.compHom N φ
  let g' : M ≃ₗ[k] N :=
    { g.toEquiv with map_add' := g.map_add, map_smul' := fun c x => g.map_smul (φ c) x }
  exact g'.finrank_eq

/-- The `Γ(X, 𝒪_X)`-linear isomorphism `Γ(X, L) ≃ Γ(X, L')` induced by an isomorphism `L ≅ L'`. -/
private noncomputable def sectionsLinearEquiv {X : Scheme.{u}} {L L' : X.Modules} (e : L ≅ L') :
    Γ(L, ⊤) ≃ₗ[Γ(X, ⊤)] Γ(L', ⊤) where
  toFun := e.hom.app ⊤
  invFun := e.inv.app ⊤
  map_add' := map_add _
  map_smul' _ s := Scheme.Modules.Hom.app_smul e.hom _ s
  left_inv s := by
    change ((e.hom ≫ e.inv).app ⊤) s = s
    rw [Iso.hom_inv_id]
    rfl
  right_inv s := by
    change ((e.inv ≫ e.hom).app ⊤) s = s
    rw [Iso.inv_hom_id]
    rfl

/-- For a Cartier divisor `A` and a Cartier divisor `D` with `𝒪_X(A) ≅ 𝒪_X(D)`, the
isomorphisms `𝒪_X((n + 1) A) ≅ 𝒪_X((n + 1) D)`. -/
private noncomputable def sheafSuccNsmulIso {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] (A : X.CartierDivisor) (D : Divisor X) (hD : D.IsCartier)
    (e : MMP.CartierDivisor.sheaf A ≅ D.divisorialSheaf) :
    ∀ n : ℕ, MMP.CartierDivisor.sheaf ((n + 1) • A) ≅
      ((n + 1) • D).divisorialSheaf
  | 0 => eqToIso (by rw [zero_add, one_smul]) ≪≫ e ≪≫ eqToIso (by rw [zero_add, one_smul])
  | n + 1 => eqToIso (by rw [succ_nsmul]) ≪≫
      (MMP.CartierDivisorSheaf.sheafMulIso ((n + 1) • A) A).symm ≪≫
      Stacks.RelativeVeryAmple.tensorModulesMapIso X (sheafSuccNsmulIso A D hD e n) e ≪≫
      (hD.nsmul (n + 1)).divisorialSheafTensorIso hD ≪≫ eqToIso (by rw [← succ_nsmul])

/-- A Cartier divisor `C` with `𝒪_Y(C) ≅ 𝒪_Y(D)` for a Cartier divisor `D` is big if and only
if `D` is: `h⁰` of every positive multiple is the same on both sides. -/
private theorem isBigCartier_iff_isBig_of_iso {k : Type u} [Field k] {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (f : Y ⟶ Spec (.of k))
    (C : Y.CartierDivisor) {D : Divisor Y} (hD : D.IsCartier)
    (e : MMP.CartierDivisor.sheaf C ≅ D.divisorialSheaf) :
    IsBigCartier k f C ↔ D.IsBig k f := by
  have key : ∀ m : ℤ, 0 < m → cartierH0 k f (m • C) = (m • D).h0 k f := fun m hm => by
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = ((j + 1 : ℕ) : ℤ) := ⟨m.toNat - 1, by omega⟩
    rw [natCast_zsmul, natCast_zsmul]
    exact finrank_compHom_eq (scalarsToGlobalSections k f)
      (sectionsLinearEquiv (sheafSuccNsmulIso C D hD e j))
  constructor <;> rintro ⟨d, hd, c, hc, k₀, hk⟩ <;>
    refine ⟨d, hd, c, hc, max k₀ 1, fun m hm => ?_⟩
  · rw [← key m (by omega)]
    exact hk m (le_of_max_le_left hm)
  · rw [key m (by omega)]
    exact hk m (le_of_max_le_left hm)

end Sections

section Pullback

open Opposite MMP.Intersection MMP.CartierDivisorPullback

/-- The only associated point of an integral locally Noetherian scheme is its generic point. -/
private theorem eq_genericPoint_of_mem_schemeAssociatedPoints {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] {ξ : X} (h : ξ ∈ Stacks.Divisors.schemeAssociatedPoints X) :
    ξ = genericPoint X := by
  have h1 : ξ ∈ Stacks.Divisors.schemeWeaklyAssociatedPoints X := by
    rwa [Stacks.Divisors.schemeAssociatedPoints,
      associatedPoints_eq_weaklyAssociatedPoints X (SheafOfModules.unit X.ringCatSheaf)] at h
  rw [weaklyAssociatedPointsOfScheme_eq_genericPoints] at h1
  have h2 : closure ({ξ} : Set X) ∈ ({Set.univ} : Set (Set X)) := by
    rwa [← irreducibleComponents_eq_singleton]
  exact (show IsGenericPoint ξ Set.univ from h2).eq (genericPoint_spec X)

/-- On an integral scheme, the image of `s ∈ 𝒪_{Y,y}` in `𝓜_{Y,y}` is the germ of the rational
function `s` (the specialization of `s` to the generic point). -/
private theorem stalkToTotalQuotient_eq_germ {Y : Scheme.{u}} [IsIntegral Y] {V : Y.Opens}
    {y : Y} (hy : y ∈ V) (s : Y.presheaf.stalk y) :
    stalkToTotalQuotient y s = Y.totalQuotientSheaf.presheaf.germ V y hy
      (functionFieldToK V (Y.presheaf.stalkSpecializes
        ((genericPoint_spec Y).specializes (Set.mem_univ y)) s)) := by
  obtain ⟨W, hyW, t, rfl⟩ := Y.presheaf.exists_germ_eq s
  have hyVW : y ∈ V ⊓ W := ⟨hy, hyW⟩
  have hξ : genericPoint Y ∈ V ⊓ W := genericPoint_mem hyVW
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply,
    ← Y.totalQuotientSheaf.presheaf.germ_res_apply (homOfLE inf_le_left : V ⊓ W ⟶ V) y hyVW]
  have h1 : Y.totalQuotientSheaf.presheaf.map (homOfLE inf_le_left : V ⊓ W ⟶ V).op
      (functionFieldToK V (Y.presheaf.germ W (genericPoint Y) hξ.2 t)) =
        functionFieldToK (V ⊓ W) (Y.presheaf.germ W (genericPoint Y) hξ.2 t) :=
    (NatTrans.naturality_apply (functionFieldToTotalQuotientSheaf Y)
      (homOfLE inf_le_left : V ⊓ W ⟶ V).op _).symm
  rw [h1, ← Y.presheaf.germ_res_apply (homOfLE inf_le_right : V ⊓ W ⟶ W) _ hξ t,
    functionFieldToTotalQuotientSheaf_germ, ← Y.presheaf.germ_res_apply
      (homOfLE inf_le_right : V ⊓ W ⟶ W) y hyVW t]
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ _ _ _

/-- **The pull-back is a pull-back by local fractions.** For a morphism `f : Y ⟶ X` of
locally Noetherian schemes with `Y` integral and `f(Y) ⊄ Supp D`, the pull-back `f^*D` is
a pull-back of `D` in the sense of `MMP.Intersection.IsPullback`. -/
private theorem isPullback_cartierPullback {X Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (f : Y ⟶ X) (D : X.CartierDivisor)
    (hD : ¬ Set.range f ⊆ MMP.Intersection.cartierSupport D) :
    MMP.Intersection.IsPullback f D (MMP.CartierDivisor.pullback f D hD) := by
  have hξ : f (genericPoint Y) ∉ cartierSupport D :=
    (MMP.CartierDivisor.genericPoint_notMem_cartierSupport_iff f D).mpr hD
  have hcond : PullbackCondition f D := fun η hη => by
    rwa [eq_genericPoint_of_mem_schemeAssociatedPoints hη]
  refine ⟨hcond, fun y => ?_⟩
  obtain ⟨_, U, hyU, σ, hσ, rfl⟩ := exists_isLocalEquationAt D (f y)
  obtain ⟨a, b, hab, ha, hb⟩ :=
    exists_isFraction_stalkMap_mem_nonZeroDivisors hcond y ⟨U, hyU, σ, hσ, rfl⟩
  have hspec : genericPoint Y ⤳ y := (genericPoint_spec Y).specializes (Set.mem_univ y)
  have hηU : f (genericPoint Y) ∈ U := (hspec.map f.continuous).mem_open U.isOpen hyU
  obtain ⟨a₀, ha₀⟩ := MMP.CartierDivisor.exists_isGermUnit_of_not_range_subset f D hD hσ hηU
  set τ := ofFunctionField (f ⁻¹ᵁ U) (pullbackGerm f a₀)
  have hτ : IsLocalEquationOn (MMP.CartierDivisor.pullback f D hD) (f ⁻¹ᵁ U) τ :=
    MMP.CartierDivisor.isLocalEquationOn_pullback f D hD hσ hηU ha₀
  refine ⟨a, b, ⟨_, ⟨U, hyU, σ, hσ, rfl⟩, hab⟩, ha, hb, _, ⟨f ⁻¹ᵁ U, hyU, τ, hτ, rfl⟩,
    isUnit_stalkToTotalQuotient_of_mem_nonZeroDivisors hb, ?_⟩
  have hspX : f (genericPoint Y) ⤳ f y := hspec.map f.continuous
  have hnat : ∀ c : X.presheaf.stalk (f y),
      stalkToTotalQuotient _ (X.presheaf.stalkSpecializes hspX c) =
        X.totalQuotientSheaf.presheaf.stalkSpecializes hspX (stalkToTotalQuotient (f y) c) :=
    fun c => (ConcreteCategory.congr_hom
      (TopCat.Presheaf.stalkSpecializes_stalkFunctor_map X.toTotalQuotientSheaf.hom hspX) c)
  have hkey : X.presheaf.stalkSpecializes hspX b * a₀.val =
      X.presheaf.stalkSpecializes hspX a := by
    apply stalkToTotalQuotient_injective X (f (genericPoint Y))
    rw [map_mul, hnat, hnat, ha₀]
    have hg : TopCat.Presheaf.germ X.totalQuotientSheaf.obj U (f (genericPoint Y)) hηU σ.val =
        X.totalQuotientSheaf.presheaf.stalkSpecializes hspX
          (X.totalQuotientSheaf.presheaf.germ U (f y) hyU σ.val) :=
      (TopCat.Presheaf.germ_stalkSpecializes_apply _ hyU hspX _).symm
    rw [hg, ← map_mul, hab.2]
  have hcomm : ∀ c : X.presheaf.stalk (f y),
      Y.presheaf.stalkSpecializes hspec (f.stalkMap y c) =
        f.stalkMap (genericPoint Y) (X.presheaf.stalkSpecializes hspX c) :=
    fun c => (ConcreteCategory.congr_hom (Scheme.Hom.stalkSpecializes_stalkMap f _ _ hspec) c).symm
  have hyU' : y ∈ f ⁻¹ᵁ U := hyU
  rw [stalkToTotalQuotient_eq_germ hyU', stalkToTotalQuotient_eq_germ hyU', ← map_mul]
  congr 1
  have hpg : ((pullbackGerm f a₀ : Y.functionFieldˣ) : Y.functionField) =
      f.stalkMap (genericPoint Y) a₀.val := rfl
  change functionFieldToK (f ⁻¹ᵁ U) _ *
    functionFieldToK (f ⁻¹ᵁ U) (pullbackGerm f a₀).val = _
  rw [hpg, ← map_mul, hcomm, hcomm, ← map_mul, hkey]

end Pullback

/-- **Bigness descends along a birational morphism.** Let `f : Y ⟶ X` be a birational
morphism of proper normal varieties over `k`, `D` a Cartier divisor on `X` and `D'` its
pull-back. If `D'` is big then so is `D`. -/
private theorem isBig_of_isPullback {k : Type} [Field k] {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} (f : Y ⟶ X) (hX : MMP.Mori.IsProperVariety k sX)
    (hY : MMP.Mori.IsProperVariety k (f ≫ sX)) [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y]
    (hf : IsBirationalMorphism f) {D : Divisor X} (hDc : D.IsCartier)
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ D.supp}
    {D' : Divisor Y} (h : D.IsPullback f hB D') (hbig : D'.IsBig k (f ≫ sX)) :
    D.IsBig k sX := by
  have hXv := ((MMP.Mori.isProperVariety_iff k sX).mp hX).1
  have hYv := ((MMP.Mori.isProperVariety_iff k (f ≫ sX)).mp hY).1
  have : IsIntegral X := hXv.toIsIntegral
  have : IsIntegral Y := hYv.toIsIntegral
  have : QuasiCompact sX := hXv.toQuasiCompact
  have : QuasiCompact (f ≫ sX) := hYv.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  have : IsDominant f := hf.isDominant
  have := hDc.isInvertibleModule_divisorialSheaf
  -- a Cartier divisor `A` with `𝒪_X(A) ≅ 𝒪_X(D)`, and its pull-back
  obtain ⟨A, ⟨e⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf D.divisorialSheaf
  have hA : ¬ Set.range f ⊆ MMP.Intersection.cartierSupport A := fun hsub =>
    MMP.CartierDivisor.genericPoint_notMem_cartierSupport A
      (closure_minimal hsub (MMP.Intersection.isClosed_cartierSupport A)
        (by rw [f.denseRange.closure_eq]; trivial))
  have e' : MMP.CartierDivisor.sheaf
      (MMP.CartierDivisor.pullback f A hA) ≅ D'.divisorialSheaf :=
    MMP.CartierDivisor.pullbackSheafIso f A hA ≪≫ (Scheme.Modules.pullback f).mapIso e.symm ≪≫
      (h.divisorialSheafIso (hBc := hDc)).symm
  exact (isBigCartier_iff_isBig_of_iso sX A hDc e.symm).mp
    ((isBigCartier_iff_of_isPullback hX hY f rfl hf (isPullback_cartierPullback f A hA)).mpr
      ((isBigCartier_iff_isBig_of_iso (f ≫ sX) _ (h.isCartier hDc) e').mpr hbig))

namespace QDivisor

/-- **Nef and big plus nef is nef and big.** Let `X` be a proper normal variety over an
algebraically closed field `k` of characteristic zero, `B` a nef and big `ℚ`-Cartier
`ℚ`-divisor and `N` a nef `ℚ`-Cartier `ℚ`-divisor on `X`. Then `B + N` is nef and big. -/
@[mmp "lem_mmp_foundation_km3b_nef_plus_big_is_big_with_snc_containment"]
public theorem IsNef.isNef_and_isBig_add {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [hXp : IsProperVariety k sX] [IsLocallyNoetherian X]
    [IsNormal X] {B N : QDivisor X} (hBnef : B.IsNef k sX) (hBbig : B.IsBig k sX)
    (hN : N.IsNef k sX) :
    (B + N).IsNef k sX ∧ (B + N).IsBig k sX := by
  refine ⟨hBnef.add hN, ?_⟩
  have hXv := ((MMP.Mori.isProperVariety_iff k sX).mp hXp).1
  have : IsIntegral X := hXv.toIsIntegral
  have : QuasiCompact sX := hXv.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  -- a common Cartier multiple `M` of `B` and `N`
  obtain ⟨a, ha, DB, hDBa, hDBc⟩ := hBnef.isQCartier.exists_pos
  obtain ⟨b, hb, DN, hDNb, hDNc⟩ := hN.isQCartier.exists_pos
  set M : ℕ := a * b with hMdef
  have hM : 0 < M := Nat.mul_pos ha hb
  have hDB₀ : Divisor.toQDivisor (b • DB) = (M : ℚ) • B := by
    rw [map_nsmul, hDBa, ← Nat.cast_smul_eq_nsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ, smul_smul,
      hMdef]
    push_cast
    ring_nf
  have hDN₀ : Divisor.toQDivisor (a • DN) = (M : ℚ) • N := by
    rw [map_nsmul, hDNb, ← Nat.cast_smul_eq_nsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ, smul_smul,
      hMdef]
    push_cast
    ring_nf
  have hDB₀c : (b • DB).IsCartier := hDBc.nsmul b
  have hDN₀c : (a • DN).IsCartier := hDNc.nsmul a
  -- the projective resolution `f : Y ⟶ X` adapted to `B`
  obtain ⟨Y, f, hres, hYp, hYln, hYn, hYc, -, -, -, -, F, -, -, hB, fB, p, hfB, hp, hamp⟩ :=
    exists_isLogResolution_isAmple_pullback_sub_sum sX 0 ⊤ idealSheafData_top_ne_bot B hBnef
      hBbig
  have hbir : IsBirationalMorphism f := hres.isBirationalMorphism
  have hYv := ((MMP.Mori.isProjectiveVariety_iff k (f ≫ sX)).mp hYp).1
  have : IsIntegral Y := hYv.toIsIntegral
  have : QuasiCompact (f ≫ sX) := hYv.toQuasiCompact
  have : IsProper (f ≫ sX) := (IsProjectiveMorphism.isProjective
    (AlgebraicGeometry.IsProjectiveVariety.isProjective (k := k) (f := f ≫ sX))).isProper
  have hYpv : MMP.Mori.IsProperVariety k (f ≫ sX) :=
    (MMP.Mori.isProperVariety_iff k (f ≫ sX)).mpr ⟨hYv, inferInstance⟩
  have : IsDominant f := hbir.isDominant
  -- pull-backs of `M B` and `M N`
  obtain ⟨DB', hDB', hpB⟩ := hfB M hM (b • DB)
    (by rw [hDB₀, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast]) hDB₀c
  have hDB'q : Divisor.toQDivisor DB' = (M : ℚ) • fB := by
    rw [hDB', ← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast]
  obtain ⟨DN', hpN⟩ := hDN₀c.exists_isPullback (f := f)
    (MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' f _)
  have hDB'c : DB'.IsCartier := hpB.isCartier hDB₀c
  have hDN'c : DN'.IsCartier := hpN.isCartier hDN₀c
  have hpD := hpB.add hDB₀c hDN₀c
    (MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' f _) hpN
  -- nefness of the pull-backs
  have hDB'nef : DB'.IsNef k (f ≫ sX) := isNef_of_iso_pullback f
    ((isNef_iff_of_toQDivisor_eq_smul hM hDB₀c hDB₀).1 hBnef) hDB'c
    (hpB.divisorialSheafIso (hBc := hDB₀c))
  have hfBnef : fB.IsNef k (f ≫ sX) :=
    (isNef_iff_of_toQDivisor_eq_smul hM hDB'c hDB'q).2 hDB'nef
  have hDN'nef : (Divisor.toQDivisor DN').IsNef k (f ≫ sX) :=
    (QDivisor.isNef_toQDivisor_iff _ hDN'c).2 (isNef_of_iso_pullback f
      ((isNef_iff_of_toQDivisor_eq_smul hM hDN₀c hDN₀).1 hN) hDN'c
      (hpN.divisorialSheafIso (hBc := hDN₀c)))
  -- `f^*B = A + P` with `A` ample and `P` effective
  set P : QDivisor Y := ∑ E ∈ F, Finsupp.single E (p E)
  set A : QDivisor Y := fB - P with hAdef
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun E hE => Finsupp.single_nonneg.mpr (hp E hE).le
  have hAq : A.IsQCartier := by
    obtain ⟨m, hm, D, hD, hDc, -⟩ := hamp
    exact isQCartier_of_toQDivisor_eq_smul hm hDc hD
  set E : QDivisor Y := (M : ℚ) • P with hEdef
  have hE0 : 0 ≤ E := smul_nonneg (by positivity) hP0
  have hEq : E.IsQCartier := by
    have : E = Divisor.toQDivisor DB' + (-(M : ℚ)) • A := by
      rw [hDB'q, hAdef, hEdef]
      module
    rw [this]
    exact (QDivisor.isQCartier_toQDivisor hDB'c).add (MMP.Flips.QDivisor.IsQCartier.qsmul hAq _)
  -- the approximations `f^*(M(B + N)) = Aₙ + (1/n) E`
  set D' : Divisor Y := DB' + DN' with hD'def
  have hD'c : D'.IsCartier := hDB'c.add hDN'c
  set Aₙ : ℕ → QDivisor Y := fun n => Divisor.toQDivisor D' - (n : ℚ)⁻¹ • E with hAₙ
  have hinf : {n : ℕ | (Aₙ n).IsAmple ∧ (Divisor.toQDivisor D').NumericallyEquivalent k (f ≫ sX)
      (Aₙ n + (n : ℚ)⁻¹ • E)}.Infinite := by
    refine Set.infinite_of_injective_forall_mem (f := fun j : ℕ => M * (j + 1))
      (fun i j h => by simpa [hM.ne'] using h) fun j => ⟨?_, ?_⟩
    · refine isAmple_of_natCast_smul (c := j + 1) (by omega) ?_
      convert isAmple_nsmul_add_nsmul_sub (f ≫ sX) hfBnef hDN'nef hamp
        (m := M * (j + 1)) (Nat.one_le_iff_ne_zero.mpr (by positivity)) (j + 1) using 1
      simp only [hAₙ, hD'def, hEdef, ← Nat.cast_smul_eq_nsmul ℚ, map_add, hDB'q]
      have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
      match_scalars <;> field_simp
    · simp only [hAₙ, sub_add_cancel]
      exact QDivisor.NumericallyEquivalent.refl (QDivisor.isQCartier_toQDivisor hD'c)
  have key := Divisor.isNef_and_isBig_of_numericallyEquivalent_isAmple_add_smul (f ≫ sX) D' hD'c
    E hE0 hEq Aₙ hinf
  refine ⟨M, hM, b • DB + a • DN, by rw [map_add, hDB₀, hDN₀, smul_add], hDB₀c.add hDN₀c,
    isBig_of_isPullback f hXp hYpv hbir (hDB₀c.add hDN₀c) hpD key.2⟩

end QDivisor

end MMP.Mori

end
