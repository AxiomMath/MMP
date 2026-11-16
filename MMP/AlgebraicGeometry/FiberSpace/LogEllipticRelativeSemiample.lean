module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Positivity.RelativeNefBaseTwist
public import MMP.AlgebraicGeometry.MMP.Abundance.LogEllipticThreefold
public import MMP.AlgebraicGeometry.MMP.Fourfold.LogMinimalModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.Divisor.Principal
public import MMP.AlgebraicGeometry.Divisor.Pullback
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import MMP.AlgebraicGeometry.Intersection.PairingSeparation
public import MMP.AlgebraicGeometry.MMP.Abundance.FiniteRepresentationGeneration
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
public import MMP.AlgebraicGeometry.MMP.Abundance.SdltCommonBaseTwist
public import MMP.AlgebraicGeometry.Singularities.DltKltPerturbation
public import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
public import MMP.AlgebraicGeometry.MMP.Abundance.LogElliptic.GenericFibreDegree
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
public import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
public import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
public import MMP.AlgebraicGeometry.MMP.BasepointFree.RelativelyFreeTwist
public import StacksFrontier.AlgebraicGeometry.Perfect.C1590Private.GlobalGenerationNearFibre
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
public import MMP.AlgebraicGeometry.Positivity.BaseLocusSum
public import MMP.AlgebraicGeometry.Positivity.LogResolutionAmpleApproximation
public import MMP.AlgebraicGeometry.Positivity.AmpleNefBig
public import MMP.AlgebraicGeometry.Positivity.NefBigOfAmpleApproximation
public import MMP.AlgebraicGeometry.Divisor.PullbackExistence
public import MMP.AlgebraicGeometry.MMP.Abundance.NumericalDimensionOnePencil
public import MMP.AlgebraicGeometry.Divisor.AmpleSectionDivisor
public import MMP.AlgebraicGeometry.Positivity.CartierTwistEulerPolynomial
public import MMP.AlgebraicGeometry.Positivity.VeryAmpleMultiple
public import MMP.AlgebraicGeometry.Singularities.LogResolution.ReducedUnion
public import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.PushforwardComparison
public import MMP.AlgebraicGeometry.Chow.FieldSituation
public import MMP.AlgebraicGeometry.Divisor.MeromorphicFunctionField
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafSections

/-!
# Relative semiampleness of a klt adjoint trivial on the generic fibre over a surface

Let `(X, B)` be a klt pair, with `B` an effective `ℚ`-divisor, on a `ℚ`-factorial normal
projective threefold `X` over `ℂ`, and let
`f : X ⟶ Z` be a contraction onto a normal projective surface `Z`. If `D = K_X + B` is `f`-nef
and `D` is `ℚ`-linearly trivial on the generic fibre `X_η` of `f`, then `D` is semiample over
`Z`.

The proof twists `D` by the pull-back of a general member of a large multiple of an ample divisor
on `Z` to make it globally nef with Iitaka dimension at least two; `f` is then a log elliptic
fibre space and the log elliptic abundance theorem applies.

## Main results

* `MMP.Fourfold.isRelativelySemiample_of_isKltPair_of_isRelativelyNef`: the statement above.

## Implementation notes

* The prime divisors of the generic fibre `X_η` are the prime divisors `E` of `X` whose generic
  point lies over the generic point of `Z`, and the rational functions of `X_η` are those of
  `X`. So `D|_{X_η} ∼_ℚ 0` is stated on `X`: there are an integer `m > 0` and a unit `φ` of
  `K(X)` such that `m D - div(φ)` has coefficient zero along every such `E`.
* "Projective contraction" is `MMP.Fourfold.IsContraction`: a projective surjective morphism of
  normal varieties over `ℂ` with `f_* 𝒪_X = 𝒪_Z`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], Chapter 15
-/

@[expose] public section

section

open AlgebraicGeometry CategoryTheory MMP.Mori MMP.Fourfold

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace Proof_lem_fourfold_klt_log_elliptic_relative_semiample

/-! ### The general member -/

open MMP.Intersection in
/-- **A general pulled-back member keeps a klt pair klt.** Let `(X, B)` be a klt pair with `B ≥ 0`
and `f : X ⟶ Z` a morphism to a projective variety, `A` an ample Cartier divisor on `Z`. For some
`a ≥ 2` there are an effective `H ∼ a N A` with `f(η_X) ∉ Supp H` and a pull-back `f^*H`, with
Weil divisor `W ≥ 0`, such that `(X, B + a⁻¹ W)` is klt. -/
private theorem exists_generalTwist {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral Z] {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    (hZ : MMP.Mori.IsProjectiveVariety k sZ) {f : X ⟶ Z} (hf : f ≫ sZ = sX)
    {n : ℕ} {K : Divisor X} {B : QDivisor X} (hklt : MMP.Mori.IsKltPair sX n K B) (hB : 0 ≤ B)
    {A : Z.CartierDivisor} (hA : Stacks.Ample.IsAmple Z (MMP.CartierDivisor.sheaf A)) {N : ℕ} (hN :
        0 < N) :
    ∃ (a : ℕ) (H : Z.CartierDivisor) (HX : X.CartierDivisor) (W : Divisor X),
      2 ≤ a ∧ IsEffective H ∧ LinearlyEquivalent H ((a * N : ℕ) • A) ∧
      f (genericPoint X) ∉ cartierSupport H ∧ IsPullback f H HX ∧ IsWeilDivisorOfCartier HX W ∧
      0 ≤ W ∧ MMP.Mori.IsKltPair sX n K (B + (a : ℚ)⁻¹ • Divisor.toQDivisor W) := by
  have hdlt := (MMP.Threefold.Mori.IsKltPair.isDltPair hklt fun P => hB P).1
  obtain ⟨H, a, hHe, -, ha, haε, hlin, hHη, HX, hHX, hW⟩ :=
    hdlt.exists_isDltPair_add_inv_smul_pullback hZ.isProjective f hf hA hN (1 / 2)
      (by norm_num)
  haveI : IsNoetherian X := ⟨⟩
  obtain ⟨W, hWc⟩ := MMP.Intersection.exists_isWeilDivisorOfCartier (X := X) HX
  obtain ⟨hW1, hWB, hdltW⟩ := hW W hWc
  have ha2 : 2 ≤ a := by
    by_contra h
    have : a = 1 := by omega
    subst this
    norm_num at haε
  have hW0 : 0 ≤ W := fun P => by
    show (0 : ℤ) ≤ W.coeff P
    by_contra hneg
    push Not at hneg
    have h1 := (hdltW.2.1 P).1
    rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor,
      smul_eq_mul, hWB P hneg.ne, zero_add] at h1
    have hlt : (W.coeff P : ℚ) < 0 := by exact_mod_cast hneg
    have : (0 : ℚ) < (a : ℚ)⁻¹ := by positivity
    nlinarith
  refine ⟨a, H, HX, W, ha2, hHe, hlin, hHη, hHX, hWc, hW0, ?_⟩
  refine (hdltW.isKltPair_iff_roundDown_eq_zero).mpr (DivisorWithCoeffs.ext' fun P => ?_)
  rw [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_zero]
  refine Int.floor_eq_zero_iff.mpr ⟨(hdltW.2.1 P).1, ?_⟩
  rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor,
    smul_eq_mul]
  by_cases hP : W.coeff P = 0
  · rw [hP, Int.cast_zero, mul_zero, add_zero]
    exact roundDown_nonpos_iff.mp hklt.2.2 P
  · rw [hWB P hP, zero_add]
    have h1 : (W.coeff P : ℚ) ≤ 1 := by exact_mod_cast hW1 P
    have h2 : (a : ℚ)⁻¹ < 1 := by
      have : (2 : ℚ) ≤ a := by exact_mod_cast ha2
      rw [inv_lt_one_iff₀]; right; linarith
    have h3 : (0 : ℚ) ≤ (a : ℚ)⁻¹ := by positivity
    nlinarith

/-! ### Nefness of the twisted adjoint -/

/-- `(div ψ · C) = 0`. -/
private theorem intersectionNumber_principalDivisor {k : Type} [Field k] {X : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (sX : X ⟶ Spec (.of k)) [QuasiCompact sX] {C : Scheme.{0}} (i : C ⟶ X)
    [IsProper (i ≫ sX)] (hdim : topologicalKrullDim C ≤ 1) (ψ : (RationalFunctions X)ˣ)
    (h : (Divisor.toQDivisor (principalDivisor ψ)).IsQCartier) :
    (Divisor.toQDivisor (principalDivisor ψ)).intersectionNumber k sX i hdim h = 0 := by
  have hc : (principalDivisor ψ).IsCartier := Divisor.isCartier_principalDivisor ψ
  have hlin : (principalDivisor ψ).LinearlyEquivalent 0 := ⟨ψ, by rw [sub_zero]⟩
  have := hc.isInvertibleModule_divisorialSheaf
  have := (Divisor.isCartier_zero (X := X)).isInvertibleModule_divisorialSheaf
  have h0 := Divisor.degreeOn_zero' k sX i hdim
  rw [Divisor.degreeOn] at h0
  rw [QDivisor.intersectionNumber_toQDivisor k sX i hdim _ hc h, Divisor.degreeOn,
    degreeOn_eq_of_iso k sX i hdim hlin.divisorialSheafIso, h0]
  rfl

open MMP.Intersection in
/-- The Weil divisor of `n • E` is `n` times that of `E`. -/
private theorem isWeilDivisorOfCartier_nsmul {X : Scheme.{0}} [IsLocallyNoetherian X]
    {E : X.CartierDivisor} {w : Divisor X} (h : IsWeilDivisorOfCartier E w) (n : ℕ) :
    IsWeilDivisorOfCartier (n • E) ((n : ℤ) • w) := fun P => by
  have h' := isOrderAlong_primeDivisorOrder (n • E) P
  have e : primeDivisorOrder P (n • E) = (((n : ℤ) • w).coeff P) := by
    rw [map_nsmul, (h P).primeDivisorOrder_eq, DivisorWithCoeffs.coeff_smul, smul_eq_mul,
      nsmul_eq_mul]
  rwa [e] at h'

open MMP.Intersection in
/-- **Pull-backs of linearly equivalent divisors.** If `H ∼ c A` on `Z`, `W` is the Weil divisor of
a pull-back of `H` and `G` the pull-back of the Weil divisor of `A`, then `W ∼ c G`. -/
private theorem linearlyEquivalent_of_isPullback {X Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral Z] [IsLocallyNoetherian Z]
    [IsNormal Z] [CompactSpace Z] (f : X ⟶ Z) [IsDominant f]
    {A : Z.CartierDivisor}
    {AW : Divisor Z} (hAW : IsWeilDivisorOfCartier A AW)
    {hAη : ∀ Z' : irreducibleComponents X, f (componentGenericPoint X Z') ∉ AW.supp}
    {G : Divisor X} (hG : AW.IsPullback f hAη G) {c : ℕ} {H : Z.CartierDivisor}
    (hlin : LinearlyEquivalent H (c • A)) {HX : X.CartierDivisor} (hHX : IsPullback f H HX)
    {W : Divisor X} (hW : IsWeilDivisorOfCartier HX W) :
    W.LinearlyEquivalent ((c : ℤ) • G) := by
  have hη := map_componentGenericPoint_notMem_supp_of_isDominant f
  have hAWc : AW.IsCartier := hAW.isCartier
  obtain ⟨u, hu⟩ := mem_principalSubgroup_iff.mp hlin
  have hHu : H = c • A + principalDivisor u := by rw [hu]; abel
  have hcG : ((c : ℤ) • AW).IsPullback f (hη _) ((c : ℤ) • G) := hG.zsmul hAWc (c : ℤ) (hη _)
  obtain ⟨e1⟩ := hW.nonempty_sheaf_iso_divisorialSheaf
  obtain ⟨e2⟩ := MMP.ProgramBaseChange.nonempty_pullback_sheaf_iso f hHX
  have e3 : MMP.CartierDivisor.sheaf H ≅
      MMP.CartierDivisor.sheaf (c • A) :=
    eqToIso (by rw [hHu]) ≪≫
      (MMP.CartierDivisor.sheafAddPrincipalIso (c • A) u).symm
  obtain ⟨e4⟩ := (isWeilDivisorOfCartier_nsmul hAW c).nonempty_sheaf_iso_divisorialSheaf
  have e5 := hcG.divisorialSheafIso (hBc := hAWc.zsmul _)
  exact MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso
    (e1.symm ≪≫ e2.symm ≪≫ (Scheme.Modules.pullback f).mapIso (e3 ≪≫ e4) ≪≫ e5.symm)

/-- **The twisted adjoint is nef.** If `W ∼ a N G` with `𝒪(G) ≅ f^*𝒪(A)`, `A` ample and
`N ≥ 2n`, then `K + B + a⁻¹ W` is numerically the adjoint `K + B + N G` of the base twist, hence
nef. -/
private theorem isNef_add_inv_smul {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [AlgebraicGeometry.IsProjectiveVariety k sX] [QuasiCompact sX]
    {sZ : Z ⟶ Spec (.of k)} [AlgebraicGeometry.IsProjectiveVariety k sZ] (hQ : IsQFactorial sX)
    {f : X ⟶ Z} (hf : f ≫ sZ = sX)
    {n : ℕ} {K : Divisor X} {B : QDivisor X} (hklt : MMP.Mori.IsKltPair sX n K B) (hB : 0 ≤ B)
    (hD : (Divisor.toQDivisor K + B).IsRelativelyNef sX f)
    {A : Z.CartierDivisor} (hA : Stacks.Ample.IsAmple Z (MMP.CartierDivisor.sheaf A))
    {G : Divisor X}
    (eG : Nonempty (G.divisorialSheaf ≅
      (Scheme.Modules.pullback f).obj (MMP.CartierDivisor.sheaf A)))
    {N : ℕ} (hN : 2 * n ≤ N) {a : ℕ} (ha : 0 < a) {W : Divisor X}
    (hlin : W.LinearlyEquivalent (((a * N : ℕ) : ℤ) • G)) :
    (Divisor.toQDivisor K + B + (a : ℚ)⁻¹ • Divisor.toQDivisor W).IsNef k sX := by
  have hnef0 := MMP.Fourfold.IsKltPair.isNef_add_zsmul_of_isRelativelyNef hf hklt hB hD A hA G
    eG (N : ℤ) (by exact_mod_cast hN)
  -- `W = a N G + div ψ`
  obtain ⟨ψ, hψ⟩ := hlin
  have hW' : W = ((a * N : ℕ) : ℤ) • G + principalDivisor ψ := by rw [← hψ]; abel
  have hdec : Divisor.toQDivisor K + B + (a : ℚ)⁻¹ • Divisor.toQDivisor W =
      (Divisor.toQDivisor K + B + (N : ℤ) • Divisor.toQDivisor G) +
        (a : ℚ)⁻¹ • Divisor.toQDivisor (principalDivisor ψ) := by
    rw [hW', map_add, map_zsmul, smul_add]
    have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
    have e : (a : ℚ)⁻¹ • (((a * N : ℕ) : ℤ) • Divisor.toQDivisor G) =
        (N : ℤ) • Divisor.toQDivisor G := by
      rw [← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
      congr 1
      push_cast
      field_simp
    rw [e]
    abel
  obtain ⟨hQ0, hnn⟩ := hnef0
  refine ⟨isQCartier_of_isQFactorial sX hQ _, fun C i _ _ _ hC => ?_⟩
  have hQψ := isQCartier_of_isQFactorial sX hQ (Divisor.toQDivisor (principalDivisor ψ))
  have hQaψ := isQCartier_of_isQFactorial sX hQ
    ((a : ℚ)⁻¹ • Divisor.toQDivisor (principalDivisor ψ))
  rw [intersectionNumber_congr sX i hC.le _ (hQ0.add hQaψ) hdec,
    QDivisor.intersectionNumber_add' k sX i hC.le _ _ hQ0 hQaψ,
    intersectionNumber_smul sX i hC.le _ hQψ _ hQaψ,
    intersectionNumber_principalDivisor sX i hC.le ψ hQψ, mul_zero, add_zero]
  exact hnn C i hC

/-! ### A multiple of the twisted adjoint moves -/

open MMP.Intersection Stacks.Ample in
/-- **An effective member through a closed set.** If `A` is an ample Cartier divisor on the
normal integral `Z`, with Weil divisor `A_W`, then for every closed `T` missing the generic point
some effective Cartier `E ∼ n A_W`, `n > 0`, has support containing `T`: a section of `𝒪(nA)`
generating `𝒪(nA)` at the generic point but nowhere on `T` has divisor of zeros `E`. -/
private theorem exists_effective_subset_supp {Z : Scheme.{0}} [IsIntegral Z] [IsLocallyNoetherian Z]
    [IsNormal Z] [CompactSpace Z] {A : Z.CartierDivisor} (hA : IsAmple Z (MMP.CartierDivisor.sheaf
        A))
    {AW : Divisor Z} (hAW : IsWeilDivisorOfCartier A AW) {T : Set Z} (hT : IsClosed T)
    (hηT : genericPoint Z ∉ T) :
    ∃ n : ℕ, 0 < n ∧ ∃ E : Divisor Z, E.IsCartier ∧ 0 ≤ E ∧
      E.LinearlyEquivalent ((n : ℤ) • AW) ∧ T ⊆ E.supp := by
  obtain ⟨n, hn, s, -, hηs, hsT⟩ :=
    Stacks.AmpleFiniteAffineNonvanishing.exists_affine_nonvanishingOpen_containing_finite
      (MMP.CartierDivisor.sheaf A) hA (Set.finite_singleton (genericPoint Z)) ⟨Tᶜ, hT.isOpen_compl⟩
      (Set.singleton_subset_iff.2 hηT)
  have hDc : ((n : ℤ) • AW).IsCartier := hAW.isCartier.zsmul _
  haveI := hDc.isInvertibleModule_divisorialSheaf
  obtain ⟨e1⟩ := MMP.Resolution.Bridges.lineBundle_nsmul_iso_tensorPow A n
  obtain ⟨e2⟩ := MMP.Resolution.Bridges.nonempty_tensorPow_iso_tensorPowModule Z
      (MMP.CartierDivisor.sheaf A) n
  obtain ⟨e3⟩ := (isWeilDivisorOfCartier_nsmul hAW n).nonempty_sheaf_iso_divisorialSheaf
  let e : tensorPowModule Z (MMP.CartierDivisor.sheaf A) (n : ℤ) ≅ ((n : ℤ) • AW).divisorialSheaf :=
    e2.symm ≪≫ e1.symm ≪≫ e3
  let σ : ((n : ℤ) • AW).divisorialSubmodule ⊤ := e.hom.app ⊤ s
  have hnv : nonvanishingLocus ((n : ℤ) • AW).divisorialSheaf σ =
      nonvanishingLocus (tensorPowModule Z (MMP.CartierDivisor.sheaf A) (n : ℤ)) s :=
    Stacks.CokernelSupport.nonvanishingLocus_iso_app e s
  have hx₀ : genericPoint Z ∈ nonvanishingLocus (tensorPowModule Z (MMP.CartierDivisor.sheaf A) (n :
      ℤ)) s :=
    (Stacks.AmpleTheory.coe_powNonvanishingOpen Z (MMP.CartierDivisor.sheaf A) n s) ▸ hηs rfl
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, mem_nonvanishingLocus_iff] at hx₀
    exact hx₀ (by simp)
  have hσ : σ ≠ 0 := fun h => hs0 (by
    have h' : (e.hom.app ⊤) s = 0 := h
    have hinv : e.inv.app ⊤ (e.hom.app ⊤ s) = s := by
      rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.hom_inv_id]; rfl
    rw [← hinv, h', map_zero])
  have heq := MMP.Mori.Divisor.nonvanishingLocus_eq_compl_supp_zeroDivisor hDc σ hσ
  refine ⟨n, hn, ((n : ℤ) • AW).zeroDivisor σ hσ, ?_, Divisor.zeroDivisor_nonneg _ σ hσ,
    ⟨(Divisor.isUnit_sectionToRationalFunctions hσ).unit, by
      rw [Divisor.zeroDivisor_eq, add_sub_cancel_right]⟩, fun z hz => ?_⟩
  · rw [Divisor.zeroDivisor_eq]
    exact (Divisor.isCartier_principalDivisor _).add hDc
  · by_contra hzE
    have hz' : z ∈ nonvanishingLocus ((n : ℤ) • AW).divisorialSheaf σ := by
      rw [heq]; exact hzE
    rw [hnv] at hz'
    exact hsT ((Stacks.AmpleTheory.coe_powNonvanishingOpen Z (MMP.CartierDivisor.sheaf A) n s) ▸
        hz') hz

/-- **The pull-back of an effective Cartier divisor** has non-negative coefficients, positive
along every prime divisor whose generic point maps into the support. -/
private theorem coeff_nonneg_and_pos_of_isPullback {X Z : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Z] [IsNormal Z] {f : X ⟶ Z} {E : Divisor Z}
    (hEc : E.IsCartier) (hE0 : 0 ≤ E)
    {hη : ∀ Z' : irreducibleComponents X, f (componentGenericPoint X Z') ∉ E.supp}
    {F : Divisor X} (hF : E.IsPullback f hη F) (P : MMP.Mori.PrimeDivisor X) :
    0 ≤ F.coeff P ∧ (f P.genericPoint ∈ E.supp → 1 ≤ F.coeff P) := by
  set z := f P.genericPoint with hz
  obtain ⟨U, hzU, φ, hφ⟩ := hEc z
  have hPU : (P.support ∩ f ⁻¹ᵁ U).Nonempty := (P.genericPoint_mem_iff _).mp hzU
  have hW := mem_pointComponent z
  obtain ⟨ϖ, hϖ⟩ := exists_stalk_eq_of_forall_zero_le_ord hW φ fun Q hQ => by
    rw [← hφ Q ⟨z, hQ, hzU⟩]; exact hE0 Q
  have h1 := pullbackComponent_val_eq_stalkMap f hη hφ hW ϖ hϖ.symm P.genericPoint_mem_component
    (P.map_componentGenericPoint_mem f hPU)
  rw [hF U φ hφ P hPU]
  set u := pullbackComponent f hη hφ P.component (P.map_componentGenericPoint_mem f hPU)
  refine ⟨?_, fun hmem => ?_⟩
  · have hb0 : (f.stalkMap P.genericPoint).hom ϖ ≠ 0 := fun h0 => u.ne_zero (by
      rw [h1, h0, map_zero])
    have hv := P.one_le_valuation_toComponent hb0
    have h2 := P.valuation_eq_exp_ordUnit u
    have h3 : P.toComponent.hom ((f.stalkMap P.genericPoint).hom ϖ) = u := h1.symm
    rw [h3, h2] at hv
    rw [← WithZero.exp_zero, WithZero.exp_le_exp] at hv
    exact hv
  · have hϖm : ϖ ∈ IsLocalRing.maximalIdeal (Z.presheaf.stalk z) := by
      rw [IsLocalRing.mem_maximalIdeal]
      intro hunit
      obtain ⟨Q, hQ, hzQ⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
      apply hQ
      rw [hφ Q ⟨z, hzQ, hzU⟩]
      have hsp : Q.genericPoint ⤳ z := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hzQ
        exact specializes_iff_mem_closure.mpr hzQ
      have hQW : Q.component = pointComponent z :=
        eq_of_mem_irreducibleComponents (Q.support_subset_component hzQ) hW
      refine Q.ord_eq_zero_of_isUnit (a := (Z.presheaf.stalkSpecializes hsp).hom ϖ)
        (hunit.map _) ?_
      rw [Q.toComponent_stalkSpecializes hsp (Q.support_subset_component hzQ)]
      have key : ∀ (W' : irreducibleComponents Z) (hW' : z ∈ W'.1), W' = pointComponent z →
          (stalkToRationalFunctions Z hW').hom ϖ = (φ : RationalFunctions Z) W' := by
        rintro W' hW' rfl
        exact hϖ
      exact key _ _ hQW
    have := PrimeDivisor.ordUnit_pos_of_mem_maximalIdeal P
      (map_nonunit (f.stalkMap P.genericPoint).hom ϖ hϖm) h1.symm
    omega

/-- **Pull-backs of linearly equivalent divisors.** If `E ∼ c A` on `Z`, with `E`, `A` Cartier,
then `f^*E ∼ c f^*A`. -/
private theorem linearlyEquivalent_pullback {X Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral Z] [IsLocallyNoetherian Z]
    [IsNormal Z] [CompactSpace Z] {f : X ⟶ Z} [IsDominant f]
    {AW : Divisor Z} (hAWc : AW.IsCartier)
    {hAη : ∀ Z' : irreducibleComponents X, f (componentGenericPoint X Z') ∉ AW.supp}
    {G : Divisor X} (hG : AW.IsPullback f hAη G) {E : Divisor Z} (hEc : E.IsCartier) {c : ℤ}
    (hlin : E.LinearlyEquivalent (c • AW))
    {hEη : ∀ Z' : irreducibleComponents X, f (componentGenericPoint X Z') ∉ E.supp}
    {F : Divisor X} (hF : E.IsPullback f hEη F) : F.LinearlyEquivalent (c • G) := by
  have hη := map_componentGenericPoint_notMem_supp_of_isDominant f
  obtain ⟨ψ, hψ⟩ := hlin
  have hEeq : E = c • AW + principalDivisor ψ := by rw [← hψ]; abel
  have hp := (hG.zsmul hAWc c (hη _)).add (hAWc.zsmul _) (Divisor.isCartier_principalDivisor ψ)
    (hη _) (Divisor.isPullback_principalDivisor ψ (hη _))
  have hF' : F = c • G + principalDivisor (pullbackRationalFunction f ψ (hη _)) :=
    hF.eq hEc (hp.of_eq hEeq.symm)
  exact ⟨pullbackRationalFunction f ψ (hη _), by rw [hF']; abel⟩

/-- The section `χ` of `𝒪(D)` given by a unit `χ` with `D + div χ ≥ 0`; it is nonzero. -/
private theorem exists_ne_zero_section {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {D : Divisor X} (χ : (RationalFunctions X)ˣ)
    (h : ∀ P : MMP.Mori.PrimeDivisor X, 0 ≤ D.coeff P + P.ord χ) :
    ∃ σ : D.divisorialSubmodule ⊤, σ ≠ 0 := by
  refine ⟨⟨fun Z => (χ : RationalFunctions X) Z.1,
    MMP.Fourfold.isDivisorialSection_of_unit χ fun P _ => h P⟩, fun h0 => ?_⟩
  have h1 := congrArg Divisor.sectionToRationalFunctions h0
  obtain ⟨Z⟩ : Nonempty (irreducibleComponents X) :=
    ⟨⟨_, irreducibleComponent_mem_irreducibleComponents (genericPoint X)⟩⟩
  have h2 := congrFun h1 Z
  exact ((χ.isUnit.map (Pi.evalRingHom _ Z)).ne_zero) (h2.trans (by
    change Divisor.sectionToRationalFunctions (0 : D.divisorialSubmodule ⊤) Z = 0
    rfl))

/-- `h⁰(D) ≤ h⁰(D + div θ)`. -/
private theorem h0_le_add_principalDivisor {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k))
    [IsLocallyNoetherian X] [IsNormal X] [IsProper sX] [CompactSpace X] [IsIntegral X]
    {D : Divisor X} (hD : D.IsCartier) (θ : (RationalFunctions X)ˣ) :
    D.h0 k sX ≤ (D + MMP.Mori.principalDivisor θ).h0 k sX := by
  obtain ⟨σ, hσ⟩ := exists_ne_zero_section (D := MMP.Mori.principalDivisor θ) θ⁻¹ fun P => by
    rw [coeff_principalDivisor, PrimeDivisor.ord_inv]; simp
  exact MMP.Mori.Divisor.h0_le_of_add_le sX (hD.add (Divisor.isCartier_principalDivisor θ)) le_rfl
    σ hσ

/-- `h⁰(D) ≤ h⁰(D + S)` for `S ≥ 0`. -/
private theorem h0_le_add_of_nonneg {k : Type} [Field k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k))
    [IsLocallyNoetherian X] [IsNormal X] [IsProper sX] [CompactSpace X] [IsIntegral X]
    {D S : Divisor X} (hDS : (D + S).IsCartier) (hS : 0 ≤ S) :
    D.h0 k sX ≤ (D + S).h0 k sX := by
  obtain ⟨σ, hσ⟩ := exists_ne_zero_section (D := S) 1 fun P => by
    rw [PrimeDivisor.ord_one, add_zero]; exact hS P
  exact MMP.Mori.Divisor.h0_le_of_add_le sX hDS le_rfl σ hσ

/-- `div (φ ^ n) = n • div φ`. -/
private theorem principalDivisor_zpow {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] (φ : (RationalFunctions X)ˣ) (n : ℤ) :
    MMP.Mori.principalDivisor (φ ^ n) = n • MMP.Mori.principalDivisor φ := by
  ext D
  change D.ord (φ ^ n) = (n • MMP.Mori.principalDivisor φ).coeff D
  rw [PrimeDivisor.ord_zpow, DivisorWithCoeffs.coeff_smul, coeff_principalDivisor]

/-- **Bigness of an ample divisor on a surface**: two independent sections in all large multiples
of a fixed multiple. -/
private theorem exists_two_le_h0_nsmul {k : Type} [Field k] {Z : Scheme.{0}} [IsIntegral Z]
    [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z] {sZ : Z ⟶ Spec (.of k)}
    (hZ : MMP.Mori.IsProjectiveVariety k sZ) (hdimZ : topologicalKrullDim Z = 2)
    {AW : Divisor Z} (hAWc : AW.IsCartier) (hAWa : AW.IsAmple hAWc) :
    ∃ j₀ : ℕ, 0 < j₀ ∧ ∃ l₀ : ℕ, ∀ l : ℕ, l₀ ≤ l → 2 ≤ (((l * j₀ : ℕ) : ℤ) • AW).h0 k sZ := by
  haveI : AlgebraicGeometry.IsProjectiveVariety k sZ := hZ
  haveI : QuasiCompact sZ := hZ.toQuasiCompact
  have hAQ : (Divisor.toQDivisor AW).IsAmple :=
    ⟨1, one_pos, AW, by simp, hAWc, hAWa⟩
  obtain ⟨-, m₁, hm₁, D', hD', -, hbig⟩ := QDivisor.isNef_and_isBig_of_isAmple sZ hAQ
  have hD'eq : D' = (m₁ : ℤ) • AW := by
    apply Divisor.toQDivisor_injective
    rw [hD', map_zsmul, ← Int.cast_smul_eq_zsmul ℚ]
    push_cast
    rfl
  obtain ⟨nd, hnd, c', hc', k₀, hk₀⟩ := hbig
  have hnd2 : nd = 2 := by
    rw [hdimZ] at hnd
    exact_mod_cast hnd.symm
  subst hnd2
  obtain ⟨l₁, hl₁⟩ := exists_nat_ge (1 / c')
  refine ⟨m₁, hm₁, max (max l₁ k₀.toNat) 1, fun l hl => ?_⟩
  have hl1 : 1 ≤ l := le_trans (le_max_right _ _) hl
  have hlk : k₀ ≤ (l : ℤ) := by
    have := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hl)
    omega
  have h := hk₀ l hlk
  rw [hD'eq, smul_smul] at h
  have e : ((l * m₁ : ℕ) : ℤ) = (l : ℤ) * m₁ := by push_cast; ring
  rw [e]
  have hll : (1 : ℝ) ≤ c' * (l : ℝ) ^ 2 := by
    have h1 : (1 / c' : ℝ) ≤ l := by
      have := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hl)
      exact le_trans hl₁ (by exact_mod_cast this)
    have h2 : (l : ℝ) ≤ (l : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ l := by exact_mod_cast hl1
      nlinarith
    rw [div_le_iff₀ hc'] at h1
    nlinarith
  have : (1 : ℝ) < (((l : ℤ) * m₁) • AW).h0 k sZ := by
    push_cast at h
    linarith
  exact_mod_cast this

open MMP.Intersection in
/-- **(15.4.2) for the twisted adjoint.** -/
private theorem exists_two_le_h0 {k : Type} [Field k] {X Z : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z]
    {sX : X ⟶ Spec (.of k)} [IsProper sX] {sZ : Z ⟶ Spec (.of k)}
    (hZ : MMP.Mori.IsProjectiveVariety k sZ) (hdimZ : topologicalKrullDim Z = 2)
    (hQ : IsQFactorial sX) {f : X ⟶ Z} (hf : f ≫ sZ = sX) [IsDominant f] [QuasiCompact f]
    (L : QDivisor X)
    (hgen : ∃ m : ℕ, 0 < m ∧ ∃ φ : (RationalFunctions X)ˣ, ∀ E : MMP.Mori.PrimeDivisor X,
      f.base E.genericPoint = genericPoint Z →
        ((m : ℤ) • L - Divisor.toQDivisor (MMP.Mori.principalDivisor φ)).coeff E = 0)
    {A : Z.CartierDivisor} (hA : Stacks.Ample.IsAmple Z (MMP.CartierDivisor.sheaf A))
    {AW : Divisor Z} (hAW : IsWeilDivisorOfCartier A AW) (hAWa : AW.IsAmple hAW.isCartier)
    {hAη : ∀ Z' : irreducibleComponents X, f (componentGenericPoint X Z') ∉ AW.supp}
    {G : Divisor X} (hG : AW.IsPullback f hAη G) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ a : ℕ, 0 < a → ∀ W : Divisor X,
      W.LinearlyEquivalent (((a * N : ℕ) : ℤ) • G) →
      ∃ m : ℕ, 0 < m ∧ ∃ M : Divisor X,
        Divisor.toQDivisor M = (m : ℤ) • (L + (a : ℚ)⁻¹ • Divisor.toQDivisor W) ∧
          M.IsCartier ∧ 2 ≤ M.h0 k sX := by
  classical
  have hAWc : AW.IsCartier := hAW.isCartier
  have hη := map_componentGenericPoint_notMem_supp_of_isDominant f
  have hGc : G.IsCartier := hG.isCartier hAWc
  obtain ⟨m₀, hm₀, φ, hφ⟩ := hgen
  obtain ⟨d, hd, G₁, hG₁⟩ := MMP.Flips.exists_pos_smul_eq_toQDivisor L
  -- the vertical integral divisor `V₂ = d (m₀ L - div φ)`
  set V₂ : Divisor X := (m₀ : ℤ) • G₁ - (d : ℤ) • MMP.Mori.principalDivisor φ with hV₂def
  have hV₂q : Divisor.toQDivisor V₂ =
      (d : ℤ) • ((m₀ : ℤ) • L - Divisor.toQDivisor (MMP.Mori.principalDivisor φ)) := by
    rw [hV₂def, map_sub, map_zsmul, map_zsmul, hG₁, smul_sub, smul_smul, smul_smul, mul_comm]
  have hvert : ∀ P : MMP.Mori.PrimeDivisor X, V₂.coeff P ≠ 0 →
      f P.genericPoint ≠ genericPoint Z := by
    intro P hP hPη
    apply hP
    have h1 := congrArg (fun D : QDivisor X => D.coeff P) hV₂q
    simp only [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor] at h1
    rw [hφ P hPη, smul_zero] at h1
    exact_mod_cast h1
  -- the closed set `T` of images of the negative components
  set S := V₂.support.filter fun P => V₂.coeff P < 0 with hSdef
  set T : Set Z := ⋃ P ∈ S, closure {f P.genericPoint} with hTdef
  have hT : IsClosed T := isClosed_biUnion_finset fun _ _ => isClosed_closure
  have hηT : genericPoint Z ∉ T := by
    intro hmem
    obtain ⟨P, hP, hPm⟩ := Set.mem_iUnion₂.mp hmem
    have hsp : f P.genericPoint ⤳ genericPoint Z := specializes_iff_mem_closure.mpr hPm
    exact hvert P (Finsupp.mem_support_iff.mp (Finset.mem_filter.mp hP).1)
      (hsp.antisymm ((genericPoint_spec Z).specializes trivial)).eq
  obtain ⟨n, hn, E, hEc, hE0, hElin, hTE⟩ := exists_effective_subset_supp hA hAW hT hηT
  -- its pull-back `W_H ≥ 0`, positive along the negative components of `V₂`
  have hWHp : E.IsPullback f (hη E) (E.pullback hEc (hη E)) :=
    Divisor.isPullback_pullback hEc (hη E)
  set WH := E.pullback hEc (hη E) with hWHdef
  have hWH0 : 0 ≤ WH := fun P => by
    change (0 : ℤ) ≤ WH.coeff P
    exact (coeff_nonneg_and_pos_of_isPullback hEc hE0 hWHp P).1
  have hWHpos : ∀ P ∈ S, 1 ≤ WH.coeff P := fun P hP =>
    (coeff_nonneg_and_pos_of_isPullback hEc hE0 hWHp P).2
      (hTE (Set.mem_biUnion hP (subset_closure rfl)))
  have hWHlin : WH.LinearlyEquivalent ((n : ℤ) • G) :=
    linearlyEquivalent_pullback hAWc hG hEc hElin hWHp
  set k₁ : ℕ := ∑ P ∈ S, (V₂.coeff P).natAbs with hk₁
  have hVk : 0 ≤ V₂ + (k₁ : ℤ) • WH := fun P => by
    change (0 : ℤ) ≤ (V₂ + (k₁ : ℤ) • WH).coeff P
    rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
    have hW0 : (0 : ℤ) ≤ WH.coeff P := hWH0 P
    by_cases hP : P ∈ S
    · have h1 := hWHpos P hP
      have h2 : ((V₂.coeff P).natAbs : ℤ) ≤ k₁ := by
        rw [hk₁]
        exact_mod_cast Finset.single_le_sum (f := fun P => (V₂.coeff P).natAbs)
          (fun _ _ => Nat.zero_le _) hP
      have h3 : -(V₂.coeff P) ≤ ((V₂.coeff P).natAbs : ℤ) := by
        rw [Int.natCast_natAbs]; exact neg_le_abs _
      nlinarith
    · have h1 : 0 ≤ V₂.coeff P := by
        by_contra h
        push Not at h
        exact hP (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr h.ne, h⟩)
      positivity
  -- bigness on the base
  obtain ⟨j₀, hj₀, l₀, hbig⟩ := exists_two_le_h0_nsmul hZ hdimZ hAWc hAWa
  refine ⟨k₁ * n + 1, fun N hN a ha W hW => ?_⟩
  set D₁ : Divisor X := ((m₀ * a : ℕ) : ℤ) • G₁ + ((m₀ * d : ℕ) : ℤ) • W with hD₁def
  obtain ⟨c₀, hc₀, hc₀c⟩ := hQ.2 D₁
  set c : ℕ := c₀ * (j₀ * (l₀ + 1)) with hcdef
  have hMc : ((c : ℤ) • D₁).IsCartier := by
    have := hc₀c.zsmul ((j₀ * (l₀ + 1) : ℕ) : ℤ)
    rwa [smul_smul, show (((j₀ * (l₀ + 1) : ℕ) : ℤ) * (c₀ : ℤ)) = (c : ℤ) by
      rw [hcdef]; push_cast; ring] at this
  refine ⟨c * (m₀ * d * a), by positivity, (c : ℤ) • D₁, ?_, hMc, ?_⟩
  · rw [map_zsmul, hD₁def, map_add, map_zsmul, map_zsmul, hG₁, smul_add, smul_smul]
    have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
    ext P
    simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add, smul_eq_mul,
      zsmul_eq_mul, Int.cast_natCast, Nat.cast_mul]
    field_simp
    push_cast
    ring
  · obtain ⟨ψ, hψ⟩ := hW
    obtain ⟨Ξ, hΞ⟩ := hWHlin
    have hmd : 1 ≤ m₀ * d := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hNk : k₁ * n < m₀ * d * N := by nlinarith
    set l : ℕ := c₀ * (l₀ + 1) * a * (m₀ * d * N - k₁ * n) with hl
    set j : ℕ := l * j₀ with hj
    have hl₀ : l₀ ≤ l := by
      have h1 : 1 ≤ c₀ := hc₀
      have h2 : 1 ≤ a := ha
      have h3 : 1 ≤ m₀ * d * N - k₁ * n := by omega
      have : l₀ + 1 ≤ l := by
        rw [hl]
        calc l₀ + 1 = 1 * (l₀ + 1) * 1 * 1 := by ring
          _ ≤ c₀ * (l₀ + 1) * a * (m₀ * d * N - k₁ * n) := by gcongr
      omega
    have hjz : ((j : ℕ) : ℤ) = (c : ℤ) * a * (m₀ * d * N) - (c : ℤ) * a * (k₁ * n) := by
      rw [hj, hl, hcdef, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul,
        Nat.cast_sub hNk.le]
      push_cast
      ring
    set Θ : (RationalFunctions X)ˣ := φ ^ ((c * a * d : ℕ) : ℤ) * ψ ^ ((c * m₀ * d : ℕ) : ℤ) *
      Ξ ^ (-((c * a * k₁ : ℕ) : ℤ)) with hΘ
    set Sd : Divisor X := ((c * a : ℕ) : ℤ) • (V₂ + (k₁ : ℤ) • WH) with hSd
    have hdecomp : (c : ℤ) • D₁ = ((j : ℕ) : ℤ) • G + MMP.Mori.principalDivisor Θ + Sd := by
      ext P
      have hWP := congrArg (fun D : Divisor X => D.coeff P) hψ
      have hWHP := congrArg (fun D : Divisor X => D.coeff P) hΞ
      simp only [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul, smul_eq_mul,
        coeff_principalDivisor] at hWP hWHP
      change ((c : ℤ) • D₁).coeff P = ((((j : ℕ) : ℤ) • G + MMP.Mori.principalDivisor Θ +
        Sd)).coeff P
      simp only [hD₁def, hSd, hΘ, hV₂def, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_sub,
        DivisorWithCoeffs.coeff_smul, smul_eq_mul, coeff_principalDivisor, PrimeDivisor.ord_mul,
        PrimeDivisor.ord_zpow]
      rw [hjz]
      push_cast at hWP hWHP ⊢
      linear_combination ((c : ℤ) * m₀ * d) * hWP - ((c : ℤ) * a * k₁) * hWHP
    have hjAW : (((j : ℕ) : ℤ) • AW).IsCartier := hAWc.zsmul _
    have hjG : (((j : ℕ) : ℤ) • G).IsCartier := hGc.zsmul _
    have hpj : (((j : ℕ) : ℤ) • AW).IsPullback f (hη _) (((j : ℕ) : ℤ) • G) :=
      hG.zsmul hAWc _ (hη _)
    have e := hpj.divisorialSheafIso (hBc := hjAW)
    have hSd0 : 0 ≤ Sd := fun P => by
      change (0 : ℤ) ≤ (((c * a : ℕ) : ℤ) • (V₂ + (k₁ : ℤ) • WH)).coeff P
      rw [DivisorWithCoeffs.coeff_smul, smul_eq_mul]
      exact mul_nonneg (by positivity) (hVk P)
    calc 2 ≤ (((l * j₀ : ℕ) : ℤ) • AW).h0 k sZ := hbig l hl₀
      _ ≤ (((j : ℕ) : ℤ) • G).h0 k sX :=
          MMP.Mori.Divisor.h0_le_of_iso_pullback (k := k) f hf hjAW hjG e
      _ ≤ ((((j : ℕ) : ℤ) • G) + MMP.Mori.principalDivisor Θ).h0 k sX :=
          h0_le_add_principalDivisor sX hjG Θ
      _ ≤ ((((j : ℕ) : ℤ) • G) + MMP.Mori.principalDivisor Θ + Sd).h0 k sX :=
          h0_le_add_of_nonneg sX (by rw [← hdecomp]; exact hMc) hSd0
      _ = ((c : ℤ) • D₁).h0 k sX := by rw [hdecomp]

/-! ### The log elliptic fibre space -/

/-- The generic fibre degree is additive. -/
private theorem genericFiberDegree_add {V W : Scheme.{0}} [IrreducibleSpace W] (g : V ⟶ W)
    (D D' : QDivisor V) :
    MMP.Flips.genericFiberDegree g (D + D') =
      MMP.Flips.genericFiberDegree g D + MMP.Flips.genericFiberDegree g D' := by
  classical
  have h : ∀ E : QDivisor V, MMP.Flips.genericFiberDegree g E =
      E.sum fun P c => c * MMP.Flips.genericFiberPointDegree g P := fun _ => rfl
  rw [h, h, h, Finsupp.sum_add_index' (by simp) (by intros; ring)]

/-- The generic fibre degree is homogeneous. -/
private theorem genericFiberDegree_zsmul {V W : Scheme.{0}} [IrreducibleSpace W] (g : V ⟶ W) (m : ℤ)
    (D : QDivisor V) :
    MMP.Flips.genericFiberDegree g (m • D) = m * MMP.Flips.genericFiberDegree g D := by
  classical
  have h : ∀ E : QDivisor V, MMP.Flips.genericFiberDegree g E =
      E.sum fun P c => c * MMP.Flips.genericFiberPointDegree g P := fun _ => rfl
  rw [h, h, Finsupp.sum_smul_index' (by simp), Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  dsimp only
  rw [zsmul_eq_mul]
  ring

/-- A divisor with no component dominating `W` has generic fibre degree zero. -/
private theorem genericFiberDegree_eq_zero_of_coeff {V W : Scheme.{0}} [IrreducibleSpace W]
    (g : V ⟶ W)
    (D : QDivisor V) (hD : ∀ E : MMP.Mori.PrimeDivisor V, g E.genericPoint = genericPoint W →
      D.coeff E = 0) :
    MMP.Flips.genericFiberDegree g D = 0 := by
  classical
  refine Finset.sum_eq_zero fun P _ => ?_
  unfold MMP.Flips.genericFiberPointDegree
  split_ifs with h
  · rw [hD P h, zero_mul]
  · rw [Nat.cast_zero, mul_zero]

/-- **A principal divisor has degree zero on the generic fibre.** -/
private theorem genericFiberDegree_principalDivisor {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k]
    {V W : Scheme.{0}} (sV : V ⟶ Spec (.of k)) (sW : W ⟶ Spec (.of k))
    [IsIntegral V] [IsNormal V] [IsLocallyNoetherian V] [CompactSpace V]
    [IsSeparated sV] [LocallyOfFiniteType sV] [QuasiCompact sV]
    [IsIntegral W] [IsSeparated sW] [LocallyOfFiniteType sW] [QuasiCompact sW]
    (g : V ⟶ W) (hg : g ≫ sW = sV) [IsProper g] [Surjective g]
    (hdim : topologicalKrullDim V = topologicalKrullDim W + 1) (φ : (RationalFunctions V)ˣ) :
    MMP.Flips.genericFiberDegree g (Divisor.toQDivisor (MMP.Mori.principalDivisor φ)) = 0 := by
  haveI : JacobsonSpace W := LocallyOfFiniteType.jacobsonSpace sW
  have hL : (Divisor.toQDivisor (MMP.Mori.principalDivisor φ)).IsQCartier :=
    QDivisor.isQCartier_toQDivisor (Divisor.isCartier_principalDivisor φ)
  obtain ⟨U, hUd, hU⟩ :=
    MMP.Flips.exists_dense_open_genericFiberDegree_eq_sum_intersectionNumber sV sW g hg hdim _ hL
  obtain ⟨w, hwU, hwc⟩ := nonempty_inter_closedPoints (X := W) (Z := (U : Set W))
    (hUd.nonempty) U.isOpen.isLocallyClosed
  obtain ⟨S, -, hS⟩ := (hU w hwU).2 hwc
  rw [hS]
  exact Finset.sum_eq_zero fun C _ => intersectionNumber_principalDivisor sV C.ι C.dim_le φ hL

/-- **A contraction of relative dimension one with `ℚ`-linearly trivial adjoint on the generic
fibre is a log elliptic fibre space.** -/
private theorem isLogEllipticFiberSpace_of {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {V W : Scheme.{0}} {sV : V ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)}
    [IsIntegral V] [IsNormal V] [IsLocallyNoetherian V] [CompactSpace V] [IsIntegral W]
    (hV : IsNormalVariety k sV) (hW : MMP.Mori.IsVariety k sW)
    (g : V ⟶ W) (hg : g ≫ sW = sV) [IsProper g] (hgs : Function.Surjective g)
    (hiso : ∀ U : W.Opens, IsIso (g.app U))
    (hdim : topologicalKrullDim V = topologicalKrullDim W + 1)
    {n : ℕ} {K : Divisor V} (hK : K.IsCanonicalDivisor sV n) {Δ : QDivisor V}
    (hΔ : MMP.Flips.IsBoundary (QDivisor.toRDivisor Δ))
    (hQ : (Divisor.toQDivisor K + Δ).IsQCartier)
    (hgen : ∃ m : ℕ, 0 < m ∧ ∃ φ : (RationalFunctions V)ˣ, ∀ E : MMP.Mori.PrimeDivisor V,
      g.base E.genericPoint = genericPoint W →
        ((m : ℤ) • (Divisor.toQDivisor K + Δ) -
          Divisor.toQDivisor (MMP.Mori.principalDivisor φ)).coeff E = 0) :
    MMP.Flips.IsLogEllipticFiberSpace k sV sW n K Δ g := by
  haveI : IsSeparated sW := hW.toIsSeparated
  haveI : LocallyOfFiniteType sW := hW.toLocallyOfFiniteType
  haveI : QuasiCompact sW := hW.toQuasiCompact
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  haveI : IsSeparated sV := hV.1.toIsSeparated
  haveI : LocallyOfFiniteType sV := hV.1.toLocallyOfFiniteType
  haveI : QuasiCompact sV := hV.1.toQuasiCompact
  haveI : Surjective g := ⟨hgs⟩
  have hη := MMP.Flips.genericPoint_map_of_surjective g hgs
  refine ⟨⟨hV, hΔ⟩, hK, hQ, ⟨hW, hV.1, hg, inferInstance, hiso⟩, ?_, ?_, ?_⟩
  · rw [← isIrreducible_iff_closure]
    have : closure (g.base ⁻¹' {genericPoint W}) = Set.univ := by
      refine Set.eq_univ_of_univ_subset ?_
      rw [← (genericPoint_spec V).def]
      exact closure_mono (Set.singleton_subset_iff.mpr hη)
    rw [this]
    exact IrreducibleSpace.isIrreducible_univ _
  · rw [← (g.fiberHomeo (genericPoint W)).isHomeomorph.topologicalKrullDim_eq]
    exact MMP.Flips.topologicalKrullDim_genericFiber_eq_one sV sW g hg hgs hdim
  · obtain ⟨m, hm, φ, hφ⟩ := hgen
    have h1 := genericFiberDegree_eq_zero_of_coeff g _ fun E hE => hφ E hE
    have h2 := genericFiberDegree_principalDivisor sV sW g hg hdim φ
    have h3 := genericFiberDegree_add g ((m : ℤ) • (Divisor.toQDivisor K + Δ) -
      Divisor.toQDivisor (MMP.Mori.principalDivisor φ))
      (Divisor.toQDivisor (MMP.Mori.principalDivisor φ))
    rw [sub_add_cancel, genericFiberDegree_zsmul, h1, h2, add_zero] at h3
    have hm' : ((m : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    exact (mul_eq_zero.mp h3).resolve_left hm'

/-- The restriction to a dense open `U` of a Cartier divisor is its pull-back along `U ⟶ X`. -/
private theorem isPullback_restrictOpen {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] (U : X.Opens) [IsIntegral U] [CompactSpace U] [IsDominant U.ι] {N : Divisor X}
    (hN : N.IsCartier) :
    N.IsPullback U.ι (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant U.ι N)
      (N.restrictOpen U) := by
  obtain ⟨N', hN'⟩ := hN.exists_isPullback (f := U.ι)
    (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant U.ι N)
  have hiso : ∀ P : MMP.Mori.PrimeDivisor U, IsIso (U.ι.stalkMap P.genericPoint) := fun P =>
    inferInstanceAs <| IsIso (U.ι.toLRSHom.stalkMap P.genericPoint)
  have : N' = N.restrictOpen U := by
    ext P
    change N'.coeff P = (N.restrictOpen U).coeff P
    rw [DivisorWithCoeffs.coeff_restrictOpen]
    exact MMP.Positivity.coeff_eq_of_isPullback P _
      (OpenWeilRestriction.genericPoint_primeDivisorMap U.ι P).symm hN hN'
  exact this ▸ hN'

/-- **`f` is a log elliptic fibre space on the open `X ⊆ X`.** -/
private theorem exists_isLogEllipticFiberSpace {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral Z] {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    (hZ : MMP.Mori.IsVariety k sZ) {f : X ⟶ Z} (hf : f ≫ sZ = sX) [IsProper f]
    (hfs : Function.Surjective f) (hiso : ∀ U : Z.Opens, IsIso (f.app U))
    (hdim : topologicalKrullDim X = topologicalKrullDim Z + 1)
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} (hp : MMP.Mori.IsPairWith sX n K Δ)
    (hΔ : MMP.Flips.IsBoundary (QDivisor.toRDivisor Δ))
    (hgen : ∃ m : ℕ, 0 < m ∧ ∃ φ : (RationalFunctions X)ˣ, ∀ E : MMP.Mori.PrimeDivisor X,
      f.base E.genericPoint = genericPoint Z →
        ((m : ℤ) • (Divisor.toQDivisor K + Δ) -
          Divisor.toQDivisor (MMP.Mori.principalDivisor φ)).coeff E = 0) :
    ∃ (U : X.Opens) (_ : (U : Set X).Nonempty) (Z' : Scheme.{0}) (sZ' : Z' ⟶ Spec (.of k))
      (fU : U.toScheme ⟶ Z'),
      MMP.Flips.IsLogEllipticFiberSpace k (U.ι ≫ sX) sZ' n (DivisorWithCoeffs.restrict U.ι K)
        (DivisorWithCoeffs.restrict U.ι Δ) fU := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  haveI : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
  haveI : IsIso (⊤ : X.Opens).ι := by rw [← X.topIso_hom]; infer_instance
  haveI : CompactSpace (⊤ : X.Opens) :=
    isCompact_iff_compactSpace.mp (by simpa using (isCompact_univ (X := X)))
  haveI : IsDominant (⊤ : X.Opens).ι := inferInstance
  have hp' := hp.restrictOpen (⊤ : X.Opens)
  refine ⟨⊤, ⟨x, trivial⟩, Z, sZ, (⊤ : X.Opens).ι ≫ f, ?_⟩
  rw [MMP.Flips.restrict_ι_eq_restrictOpen, MMP.Flips.restrict_ι_eq_restrictOpen]
  have hcomp : ((⊤ : X.Opens).ι ≫ f) ≫ sZ = (⊤ : X.Opens).ι ≫ sX := by rw [Category.assoc, hf]
  have hsurj : Function.Surjective ((⊤ : X.Opens).ι ≫ f) := by
    have h1 : Function.Surjective (⊤ : X.Opens).ι := (⊤ : X.Opens).ι.homeomorph.surjective
    intro z
    obtain ⟨y, rfl⟩ := hfs z
    obtain ⟨w, rfl⟩ := h1 y
    exact ⟨w, rfl⟩
  have hiso' : ∀ V : Z.Opens, IsIso (((⊤ : X.Opens).ι ≫ f).app V) := fun V => by
    rw [Scheme.Hom.comp_app]
    exact IsIso.comp_isIso' (hiso V) (Scheme.Hom.instIsIsoCommRingCatApp _ _)
  have hdim' : topologicalKrullDim (⊤ : X.Opens) = topologicalKrullDim Z + 1 := by
    rw [← hdim]
    exact (⊤ : X.Opens).ι.homeomorph.isHomeomorph.topologicalKrullDim_eq
  have hΔ' : MMP.Flips.IsBoundary (QDivisor.toRDivisor (Δ.restrictOpen ⊤)) := fun P => by
    have := hΔ (OpenWeilRestriction.primeDivisorMap (⊤ : X.Opens).ι P)
    rw [QDivisor.coeff_toRDivisor] at this ⊢
    rwa [DivisorWithCoeffs.coeff_restrictOpen]
  have hgen' : ∃ m : ℕ, 0 < m ∧ ∃ φ : (RationalFunctions (⊤ : X.Opens))ˣ,
      ∀ E : MMP.Mori.PrimeDivisor (⊤ : X.Opens),
      ((⊤ : X.Opens).ι ≫ f).base E.genericPoint = genericPoint Z →
        ((m : ℤ) • (Divisor.toQDivisor (K.restrictOpen ⊤) + Δ.restrictOpen ⊤) -
          Divisor.toQDivisor (MMP.Mori.principalDivisor φ)).coeff E = 0 := by
    obtain ⟨m, hm, φ, hφ⟩ := hgen
    have hcart : (MMP.Mori.principalDivisor φ).IsCartier := Divisor.isCartier_principalDivisor φ
    have hφη := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant
      (⊤ : X.Opens).ι (MMP.Mori.principalDivisor φ)
    have h1 := isPullback_restrictOpen (⊤ : X.Opens) hcart
    have h2 := Divisor.isPullback_principalDivisor (f := (⊤ : X.Opens).ι) φ hφη
    have h3 : (MMP.Mori.principalDivisor φ).restrictOpen ⊤ =
        MMP.Mori.principalDivisor (pullbackRationalFunction (⊤ : X.Opens).ι φ hφη) :=
      h1.eq hcart h2
    refine ⟨m, hm, pullbackRationalFunction (⊤ : X.Opens).ι φ hφη, fun P hP => ?_⟩
    have hP' : f.base (OpenWeilRestriction.primeDivisorMap (⊤ : X.Opens).ι P).genericPoint =
        genericPoint Z := by
      rw [OpenWeilRestriction.genericPoint_primeDivisorMap (⊤ : X.Opens).ι P]
      exact hP
    have h4 := hφ _ hP'
    rw [← h3]
    simp only [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul,
      DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_restrictOpen]
      at h4 ⊢
    exact h4
  exact isLogEllipticFiberSpace_of hp'.1 hZ _ hcomp hsurj hiso' hdim' hp'.2.1 hΔ' hp'.2.2 hgen'

/-! ### From eventual freeness to relative semiampleness -/

/-- A `ℚ`-divisor `Q` such that `n Q` is the Weil divisor of an `f`-free Cartier divisor `E` is
semiample over the base: `n⁻¹ E` is a `ℚ`-Cartier representative of `Q`. -/
private theorem isRelativelySemiample_of_isRelativelyFreeCartier' {X Z : Scheme.{0}}
    [IsLocallyNoetherian X] (f : X ⟶ Z) (Q : QDivisor X) (n : ℕ) (hn : 0 < n) (D' : Divisor X)
    (hQ : ∀ P, (D'.coeff P : ℚ) = n * Q.coeff P) (E : X.CartierDivisor)
    (hE : MMP.Intersection.IsWeilDivisorOfCartier E D') (hfree : IsRelativelyFreeCartier f E) :
    QDivisor.IsRelativelySemiample f Q := by
  classical
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨Finsupp.single E ((n : ℚ)⁻¹), fun P => ?_, n, hn, ?_⟩
  · rw [Finsupp.sum_single_index (by simp),
      (MMP.Intersection.isOrderAlong_primeDivisorOrder E P).unique (hE P), hQ P]
    field_simp
  · have hc : (n : ℚ) • Finsupp.single E ((n : ℚ)⁻¹) =
        (Finsupp.single E (1 : ℤ)).mapRange (Int.cast : ℤ → ℚ) Int.cast_zero := by
      rw [Finsupp.smul_single, Finsupp.mapRange_single, smul_eq_mul, mul_inv_cancel₀ hn',
        Int.cast_one]
    have key : ∀ (c : KCartierDivisor ℚ X) (hc' : c = (Finsupp.single E (1 : ℤ)).mapRange
        (Int.cast : ℤ → ℚ) Int.cast_zero) (h : ∀ D, ∃ m : ℤ, c D = m),
        IsRelativelyFreeCartier f (KCartierDivisor.realization c h) := by
      rintro c rfl h
      have e : KCartierDivisor.realization _ h = E := by
        rw [KCartierDivisor.realization_eq_sum, Finsupp.sum_single_index (by simp), one_smul]
      rw [e]
      exact hfree
    exact ⟨fun D => ⟨(Finsupp.single E (1 : ℤ)) D, by rw [hc]; rfl⟩, key _ hc _⟩

/-- A positive multiple of a basepoint free divisor is basepoint free: `Bs|nM| ⊆ Bs|M|`. -/
private theorem isBasepointFree_nsmul {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {M : Divisor X} (hM : M.IsBasepointFree) (n : ℕ)
    (hn : 1 ≤ n) : (n • M).IsBasepointFree := by
  refine le_bot_iff.mp ?_
  induction n, hn using Nat.le_induction with
  | base => rw [one_smul]; exact hM.le
  | succ n _ ih =>
    rw [succ_nsmul]
    exact (MMP.Positivity.baseLocus_add_le _ _).trans (sup_le ih hM.le)

open MMP.Intersection MMP.CartierDivisorSheaf in
/-- **The principal divisor of a rational function is the Weil divisor of a Cartier divisor**: of
the principal Cartier divisor of the same function, whose order along `P` is computed on its
global local equation. -/
private theorem exists_isWeilDivisorOfCartier_principalDivisor {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (ψ : (RationalFunctions X)ˣ) :
    ∃ C : X.CartierDivisor, IsWeilDivisorOfCartier C (MMP.Mori.principalDivisor ψ) := by
  obtain ⟨Z₀⟩ : Nonempty (irreducibleComponents X) :=
    ⟨⟨_, irreducibleComponent_mem_irreducibleComponents (genericPoint X)⟩⟩
  have hcomp : ∀ Z' : irreducibleComponents X, Z' = Z₀ := fun Z' => by
    have h : ∀ W : irreducibleComponents X, W.1 = Set.univ := fun W => by
      have h' : W.1 ∈ ({Set.univ} : Set (Set X)) :=
        (irreducibleComponents_eq_singleton (X := X)) ▸ W.2
      exact h'
    exact Subtype.ext ((h Z').trans (h Z₀).symm)
  set r := MMP.Threefold.Mori.Helpers.evalFF Z₀ (ψ : RationalFunctions X) with hr
  have hr0 : r ≠ 0 := (ψ.isUnit.map (MMP.Threefold.Mori.Helpers.evalFF Z₀)).ne_zero
  set c : (X.totalQuotientSheaf.obj.obj (Opposite.op ⊤))ˣ :=
    Units.map (ofFunctionField ⊤).toMonoidHom (Units.mk0 r hr0) with hc
  haveI : IsNoetherian X := ⟨⟩
  obtain ⟨w, hw⟩ := MMP.Intersection.exists_isWeilDivisorOfCartier (X := X)
    (MMP.Intersection.principalDivisor c)
  have hwψ : w = MMP.Mori.principalDivisor ψ := by
    refine DivisorWithCoeffs.ext' fun P => ?_
    have hloc : IsLocalEquationAt (MMP.Intersection.principalDivisor c) P.genericPoint
        (X.totalQuotientSheaf.presheaf.germ ⊤ P.genericPoint trivial (c : _)) :=
      ⟨⊤, trivial, c, isLocalEquationOn_principalDivisor c, rfl⟩
    rw [← ord_eq_coeff_of_isLocalEquationAt hw P rfl hloc, coeff_principalDivisor,
      MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord, hcomp P.component]
    change X.ord (totalQuotientStalkToFunctionField P.genericPoint
      (X.totalQuotientSheaf.presheaf.germ ⊤ P.genericPoint trivial
        (ofFunctionField ⊤ r))) P.genericPoint = _
    erw [MMP.CartierDivisorSheaf.totalQuotientStalkToFunctionField_germ_top_ofFunctionField]
  exact ⟨_, hwψ ▸ hw⟩

open MMP.Intersection in
/-- **A Cartier Weil divisor is the Weil divisor of a Cartier divisor** on a normal integral
Noetherian scheme: a Cartier divisor `E₀` with `𝒪(E₀) ≅ 𝒪(D)` has Weil divisor `D + div ψ`, and
`E₀` minus the principal Cartier divisor of `ψ` has Weil divisor `D`. -/
private theorem exists_isWeilDivisorOfCartier_of_isCartier {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {D : Divisor X} (hD : D.IsCartier) :
    ∃ E : X.CartierDivisor, IsWeilDivisorOfCartier E D := by
  haveI := hD.isInvertibleModule_divisorialSheaf
  obtain ⟨E₀, ⟨e⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf D.divisorialSheaf
  haveI : IsNoetherian X := ⟨⟩
  obtain ⟨w, hw⟩ := MMP.Intersection.exists_isWeilDivisorOfCartier (X := X) E₀
  obtain ⟨e'⟩ := hw.nonempty_sheaf_iso_divisorialSheaf
  obtain ⟨ψ, hψ⟩ := MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso (e'.symm ≪≫ e.symm)
  obtain ⟨C, hC⟩ := exists_isWeilDivisorOfCartier_principalDivisor ψ
  refine ⟨E₀ - C, fun P => ?_⟩
  have h := isOrderAlong_primeDivisorOrder (E₀ - C) P
  have hψP := congrArg (fun G : Divisor X => G.coeff P) hψ
  simp only [DivisorWithCoeffs.coeff_sub] at hψP
  have e : primeDivisorOrder P (E₀ - C) = D.coeff P := by
    rw [map_sub, (hw P).primeDivisorOrder_eq, (hC P).primeDivisorOrder_eq]
    omega
  rwa [e] at h

open MMP.Intersection in
/-- The zero divisor is the pull-back of the zero divisor. -/
private theorem isPullback_zero' {X Y : Scheme.{0}} (g : Y ⟶ X) :
    IsPullback g (0 : X.CartierDivisor) 0 := by
  have h1 : ∀ x : X, IsLocalEquationAt (0 : X.CartierDivisor) x 1 := fun x =>
    ⟨⊤, trivial, 1, isLocalEquationOn_one _, by simp⟩
  have h2 : ∀ y : Y, IsLocalEquationAt (0 : Y.CartierDivisor) y 1 := fun y =>
    ⟨⊤, trivial, 1, isLocalEquationOn_one _, by simp⟩
  refine ⟨fun η _ => ?_, fun y => ⟨1, 1, ⟨1, h1 _, isFraction_one_one_one _⟩, ?_, ?_, 1, h2 _, ?_⟩⟩
  · simp [cartierSupport]
  · simp
  · simp
  · simpa only [map_one] using isFraction_one_one_one y

open MMP.Intersection in
/-- Pull-backs of Cartier divisors add. -/
private theorem isPullback_add' {X Y : Scheme.{0}} {g : Y ⟶ X} {D₁ D₂ : X.CartierDivisor}
    {D₁' D₂' : Y.CartierDivisor} (h₁ : IsPullback g D₁ D₁') (h₂ : IsPullback g D₂ D₂') :
    IsPullback g (D₁ + D₂) (D₁' + D₂') := by
  refine ⟨fun η hη => ?_, fun y => ?_⟩
  · have a₁ := h₁.1 η hη
    have a₂ := h₂.1 η hη
    rw [germ_cartierSupport_eq_zero_iff] at a₁ a₂ ⊢
    rw [map_add, a₁, a₂, add_zero]
  obtain ⟨a₁, b₁, ⟨e₁, he₁, hf₁⟩, ha₁, hb₁, e₁', he₁', hf₁'⟩ := h₁.2 y
  obtain ⟨a₂, b₂, ⟨e₂, he₂, hf₂⟩, ha₂, hb₂, e₂', he₂', hf₂'⟩ := h₂.2 y
  refine ⟨a₁ * a₂, b₁ * b₂, ⟨e₁ * e₂, he₁.add he₂, hf₁.mul hf₂⟩, ?_, ?_, e₁' * e₂',
    he₁'.add he₂', ?_⟩
  · rw [map_mul]; exact mul_mem ha₁ ha₂
  · rw [map_mul]; exact mul_mem hb₁ hb₂
  · rw [map_mul, map_mul]; exact hf₁'.mul hf₂'

open MMP.Intersection in
/-- Pull-backs of Cartier divisors commute with multiples. -/
private theorem isPullback_nsmul' {X Y : Scheme.{0}} {g : Y ⟶ X} {D : X.CartierDivisor}
    {D' : Y.CartierDivisor} (h : IsPullback g D D') : ∀ n : ℕ, IsPullback g (n • D) (n • D')
  | 0 => by simpa using isPullback_zero' g
  | n + 1 => by simpa [succ_nsmul] using isPullback_add' (isPullback_nsmul' h n) h

/-- A basepoint-free Cartier divisor has a globally generated divisorial sheaf. -/
private theorem isGeneratedByGlobalSections_of_isBasepointFree {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {M : Divisor X} (hMc : M.IsCartier)
    (hM : M.IsBasepointFree) :
    SheafOfModules.IsGeneratedByGlobalSections.{0, 0, 0} M.divisorialSheaf := by
  classical
  haveI := hMc.isInvertibleModule_divisorialSheaf
  have key : ∀ x : X, ∃ σ : M.divisorialSubmodule ⊤, ∃ hσ : σ ≠ 0,
      x ∉ (M.zeroDivisor σ hσ).supp := fun x => by
    have hx : x ∉ (M.baseLocus : Set X) := by
      rw [show M.baseLocus = ⊥ from hM]; exact fun h => h
    rw [Divisor.mem_baseLocus_iff] at hx
    push Not at hx
    exact hx
  choose σ hσ hxσ using key
  have hnv : ∀ x : X, Stacks.Ample.nonvanishingLocus M.divisorialSheaf (σ x) =
      ((M.zeroDivisor (σ x) (hσ x)).supp : Set X)ᶜ := fun x =>
    MMP.Mori.Divisor.nonvanishingLocus_eq_compl_supp_zeroDivisor hMc (σ x) (hσ x)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x => ((M.zeroDivisor (σ x) (hσ x)).supp : Set X)ᶜ)
    (fun x => (M.zeroDivisor (σ x) (hσ x)).supp.isClosed.isOpen_compl)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hxσ x⟩)
  let s : Fin t.card → Γ(M.divisorialSheaf, ⊤) := fun i => σ (t.equivFin.symm i)
  refine AlgebraicGeometry.C1590Private.nonempty_generatingSections_of_forall_mem_nonvanishingLocus
    _ s fun y => ?_
  obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
  refine ⟨t.equivFin ⟨x, hx⟩, ?_⟩
  change y ∈ Stacks.Ample.nonvanishingLocus M.divisorialSheaf
    (σ (t.equivFin.symm (t.equivFin ⟨x, hx⟩)))
  rw [Equiv.symm_apply_apply, hnv x]
  exact hyx

open MMP.Intersection in
/-- **Subtracting a pull-back from the base.** If `L + a⁻¹ f^*H` is eventually free, then `L` is
semiample over `Z`. -/
private theorem isRelativelySemiample_of_isEventuallyFree {k : Type} [Field k]
    {X Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z]
    {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {f : X ⟶ Z} (hf : IsContraction sX sZ f)
    (L : QDivisor X) {H : Z.CartierDivisor} {HX : X.CartierDivisor}
    (hHX : IsPullback f H HX) {W : Divisor X}
    (hW : IsWeilDivisorOfCartier HX W) {a : ℕ} (ha : 0 < a)
    (hfree : MMP.Flips.IsEventuallyFree k sX (L + (a : ℚ)⁻¹ • Divisor.toQDivisor W)) :
    QDivisor.IsRelativelySemiample f L := by
  obtain ⟨hXn, m, hm, M, hMeq, hMc, hMb⟩ := hfree
  haveI : AlgebraicGeometry.IsVariety k sX := hXn.1
  haveI : AlgebraicGeometry.IsVariety k sZ := hf.isNormalVariety_target.1
  haveI : IsProper f := isProper_of_isProjectiveMorphism _ hf.isProjectiveMorphism
  have hWc : W.IsCartier := hW.isCartier
  -- the integral divisor `L' = a M - m W = m a L`
  set L' : Divisor X := (a : ℤ) • M - (m : ℤ) • W with hL'def
  have hL' : Divisor.toQDivisor L' = ((m * a : ℕ) : ℤ) • L := by
    have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
    ext P
    have hMP := congrArg (fun D : QDivisor X => D.coeff P) hMeq
    simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add, smul_eq_mul,
      zsmul_eq_mul, Int.cast_natCast, Divisor.coeff_toQDivisor] at hMP
    simp only [hL'def, Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_sub,
      DivisorWithCoeffs.coeff_smul, smul_eq_mul, zsmul_eq_mul, Int.cast_natCast, Int.cast_sub,
      Int.cast_mul, Nat.cast_mul]
    rw [hMP]
    field_simp
    ring
  have hL'c : L'.IsCartier := by
    rw [hL'def, sub_eq_add_neg, ← neg_smul]
    exact (hMc.zsmul _).add (hWc.zsmul _)
  obtain ⟨E₁, hE₁⟩ := exists_isWeilDivisorOfCartier_of_isCartier (hMc.zsmul (a : ℤ))
  set E : X.CartierDivisor := E₁ - m • HX with hEdef
  have hE : IsWeilDivisorOfCartier E L' := fun P => by
    have h := isOrderAlong_primeDivisorOrder E P
    have e : primeDivisorOrder P E = L'.coeff P := by
      rw [hEdef, map_sub, map_nsmul, (hE₁ P).primeDivisorOrder_eq, (hW P).primeDivisorOrder_eq,
        hL'def]
      simp only [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul, smul_eq_mul,
        nsmul_eq_mul]
    rwa [e] at h
  -- `E + m f^*H` has Weil divisor `a M`, which is basepoint free
  have hEM : IsWeilDivisorOfCartier (E + m • HX) ((a : ℤ) • M) := fun P => by
    have h := isOrderAlong_primeDivisorOrder (E + m • HX) P
    have e : primeDivisorOrder P (E + m • HX) = ((a : ℤ) • M).coeff P := by
      rw [map_add, map_nsmul, (hE P).primeDivisorOrder_eq, (hW P).primeDivisorOrder_eq, hL'def]
      simp only [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul, smul_eq_mul,
        nsmul_eq_mul]
      ring
    rwa [e] at h
  have haM : ((a : ℤ) • M).IsBasepointFree := by
    rw [natCast_zsmul]; exact isBasepointFree_nsmul hMb a ha
  have hgg := isGeneratedByGlobalSections_of_isBasepointFree (hMc.zsmul _) haM
  obtain ⟨eM⟩ := hEM.nonempty_sheaf_iso_divisorialSheaf
  have hgg' : SheafOfModules.IsGeneratedByGlobalSections.{0, 0, 0}
      (MMP.CartierDivisor.sheaf (E + m • HX)) :=
    ⟨SheafOfModules.GeneratingSections.equivOfIso eM.symm hgg.some⟩
  have hfreeE : IsRelativelyFreeCartier f E :=
    MMP.Mori.isRelativelyFreeCartier_of_isGeneratedByGlobalSections_add_pullback hf.comp_eq E
      (isPullback_nsmul' hHX m) hgg'
  refine isRelativelySemiample_of_isRelativelyFreeCartier' f L (m * a)
    (Nat.mul_pos hm ha) L' (fun P => ?_) E hE hfreeE
  have h := congrArg (fun G : QDivisor X => G.coeff P) hL'
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul,
    Int.cast_natCast] at h
  exact h

/-! ### The proof -/

/-- **Relative semiampleness in the klt log elliptic threefold case.** -/
private theorem solution :
    ∀ {X Z : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral Z]
    {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX] {sZ : Z ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hdimX : topologicalKrullDim X = 3)
    (hQ : IsQFactorial sX)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hdimZ : topologicalKrullDim Z = 2)
    {f : X ⟶ Z} (hf : IsContraction sX sZ f)
    {K : Divisor X} {B : QDivisor X} (hklt : MMP.Mori.IsKltPair sX 3 K B) (hB : 0 ≤ B)
    (hnef : (Divisor.toQDivisor K + B).IsRelativelyNef sX f)
    (hgen : ∃ m : ℕ, 0 < m ∧ ∃ φ : (RationalFunctions X)ˣ, ∀ E : MMP.Mori.PrimeDivisor X,
      f.base E.genericPoint = genericPoint Z →
        ((m : ℤ) • (Divisor.toQDivisor K + B) - Divisor.toQDivisor (principalDivisor φ)).coeff E
          = 0),
    QDivisor.IsRelativelySemiample f (Divisor.toQDivisor K + B) := by
  intro X Z _ _ _ _ _ sX _ sZ hX hdimX hQ hZ hdimZ f hf K B hklt hB hnef hgen
  -- the setting
  haveI : IsNormal Z := hf.isNormalVariety_target.2
  haveI : QuasiCompact sZ := hZ.toQuasiCompact
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI : LocallyOfFiniteType sZ := hZ.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  haveI : IsProper sX := isProper_of_isProjectiveMorphism _ hX.isProjective
  haveI : IsProper f := isProper_of_isProjectiveMorphism _ hf.isProjectiveMorphism
  haveI : IsDominant f := ⟨hf.surjective.denseRange⟩
  have hfη := MMP.Flips.genericPoint_map_of_surjective f hf.surjective
  -- an ample `A` on `Z` and its pull-back `G`
  obtain ⟨A, -, -, hA⟩ := MMP.Fourfold.exists_isEffective_isRelativelyAmpleQ sZ hZ.isProjective
  have hAs : Stacks.Ample.IsAmple Z (MMP.CartierDivisor.sheaf A) :=
    (Stacks.RelativeVeryAmple.isAmple_congr _ _ (Iso.refl (MMP.CartierDivisor.sheaf A))).mp hA
  haveI : IsNoetherian Z := ⟨⟩
  obtain ⟨AW, hAW⟩ := MMP.Intersection.exists_isWeilDivisorOfCartier (X := Z) A
  have hAWc : AW.IsCartier := hAW.isCartier
  obtain ⟨eA⟩ := hAW.nonempty_sheaf_iso_divisorialSheaf
  have hAWa : AW.IsAmple hAWc := by
    have := hAWc.isInvertibleModule_divisorialSheaf
    exact (Stacks.RelativeVeryAmple.isAmple_congr _ _ eA).mp hAs
  have hη := map_componentGenericPoint_notMem_supp_of_isDominant f
  have hG : AW.IsPullback f (hη AW) (AW.pullback hAWc (hη AW)) :=
    Divisor.isPullback_pullback hAWc (hη AW)
  set G := AW.pullback hAWc (hη AW) with hGdef
  have eG : G.divisorialSheaf ≅
      (Scheme.Modules.pullback f).obj (MMP.CartierDivisor.sheaf A) :=
    hG.divisorialSheafIso (hBc := hAWc) ≪≫ (Scheme.Modules.pullback f).mapIso eA.symm
  -- the threshold for two sections, and the general member `H ∈ |a N A|`
  obtain ⟨N₀, hN₀⟩ := exists_two_le_h0 (sX := sX) hZ hdimZ hQ hf.comp_eq
    (Divisor.toQDivisor K + B) hgen hA hAW hAWa hG
  set N := max 6 N₀ with hNdef
  obtain ⟨a, H, HX, W, ha, -, hlinH, hHη, hHX, hWc, hW0, hkltΔ⟩ :=
    exists_generalTwist hZ hf.comp_eq hklt hB hA (N := N) (by positivity)
  have ha0 : 0 < a := by omega
  have hlin : W.LinearlyEquivalent (((a * N : ℕ) : ℤ) • G) :=
    linearlyEquivalent_of_isPullback f hAW hG hlinH hHX hWc
  set Δ := B + (a : ℚ)⁻¹ • Divisor.toQDivisor W with hΔdef
  have hKΔ : Divisor.toQDivisor K + Δ =
      Divisor.toQDivisor K + B + (a : ℚ)⁻¹ • Divisor.toQDivisor W := by
    rw [hΔdef, add_assoc]
  -- nefness
  have hnefΔ : (Divisor.toQDivisor K + Δ).IsNef ℂ sX := by
    rw [hKΔ]
    exact isNef_add_inv_smul hQ hf.comp_eq hklt hB hnef hAs ⟨eG⟩ (N := N)
      (le_trans (by norm_num) (le_max_left _ _)) ha0 hlin
  -- the boundary
  have hbd : MMP.Flips.IsBoundary (QDivisor.toRDivisor Δ) := by
    intro E
    rw [QDivisor.coeff_toRDivisor]
    have h1 := (roundDown_nonpos_iff.mp hkltΔ.2.2) E
    have h0 : 0 ≤ Δ.coeff E := by
      rw [hΔdef, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
        Divisor.coeff_toQDivisor,
        smul_eq_mul]
      have hW' : (0 : ℚ) ≤ (W.coeff E : ℚ) := by exact_mod_cast hW0 E
      exact add_nonneg (hB E) (mul_nonneg (by positivity) hW')
    exact ⟨by exact_mod_cast h0, by exact_mod_cast h1.le⟩
  have hK : K.IsCanonicalDivisor sX 3 := hkltΔ.1.2.1
  have hKΔQ : (Divisor.toQDivisor K + Δ).IsQCartier := hkltΔ.1.2.2
  haveI : PerfectField ℂ := PerfectField.ofCharZero
  have hFA : MMP.Flips.IsKawamataLogTerminal sX 3 K (QDivisor.toRDivisor Δ) :=
    (MMP.Fourfold.isKawamataLogTerminal_iff_isKltPair sX 3 K Δ hkltΔ.1.1 hK hbd hKΔQ).mpr hkltΔ
  -- `K + Δ` is `ℚ`-linearly trivial along the horizontal divisors
  have hgenΔ : ∃ m : ℕ, 0 < m ∧ ∃ φ : (RationalFunctions X)ˣ, ∀ E : MMP.Mori.PrimeDivisor X,
      f.base E.genericPoint = genericPoint Z →
        ((m : ℤ) • (Divisor.toQDivisor K + Δ) - Divisor.toQDivisor (principalDivisor φ)).coeff E
          = 0 := by
    obtain ⟨m, hm, φ, hφ⟩ := hgen
    refine ⟨m, hm, φ, fun E hE => ?_⟩
    have h1 := hφ E hE
    have h2 : W.coeff E = 0 := by
      rw [← (hWc E).primeDivisorOrder_eq]
      exact MMP.Fourfold.primeDivisorOrder_eq_zero_of_isPullback f hHX E
        (by rw [hE, ← hfη]; exact hHη)
    rw [hKΔ]
    simp only [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul,
      DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor] at h1 ⊢
    rw [h2]
    simpa using h1
  have hdim : topologicalKrullDim X = topologicalKrullDim Z + 1 := by
    rw [hdimX, hdimZ]; rfl
  have hLE := exists_isLogEllipticFiberSpace ((MMP.Mori.isProjectiveVariety_iff ℂ sZ).mp hZ).1
    hf.comp_eq hf.surjective hf.isIso_app hdim hkltΔ.1 hbd hgenΔ
  have hh0 := hN₀ N (le_max_right _ _) a ha0 W hlin
  have hAss : MMP.Flips.SatisfiesAbundanceAssumptions ℂ sX K Δ :=
    { isProjectiveVariety := hX
      isQFactorial := hQ
      dim_eq := hdimX
      isBoundary := hbd
      isKawamataLogTerminal := hFA
      isNef := hnefΔ
      exists_two_le_h0 := by rw [hKΔ]; exact hh0
      exists_isLogEllipticFiberSpace := hLE }
  have hfree := hAss.isEventuallyFree
  rw [hKΔ] at hfree
  exact isRelativelySemiample_of_isEventuallyFree hf _ hHX hWc ha0 hfree

end Proof_lem_fourfold_klt_log_elliptic_relative_semiample

end

open AlgebraicGeometry CategoryTheory MMP.Mori

namespace MMP.Fourfold

/-- **Relative semiampleness in the klt log elliptic threefold case.** Let `(X, B)` be a klt pair,
`B ≥ 0` a `ℚ`-divisor and `K` a canonical divisor, on a `ℚ`-factorial normal projective
threefold `X` over `ℂ`, and let
`f : X ⟶ Z` be a contraction (`MMP.Fourfold.IsContraction`) onto a projective surface `Z`.
If `K + B` is `f`-nef and `ℚ`-linearly trivial on the generic fibre of `f` (some `m (K + B)`,
`m > 0`, agrees with a principal divisor `div φ` along every prime divisor dominating `Z`),
then `K + B` is semiample over `Z`. -/
@[mmp "lem_fourfold_klt_log_elliptic_relative_semiample"]
public theorem isRelativelySemiample_of_isKltPair_of_isRelativelyNef
    {X Z : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral Z]
    {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX] {sZ : Z ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hdimX : topologicalKrullDim X = 3)
    (hQ : IsQFactorial sX)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hdimZ : topologicalKrullDim Z = 2)
    {f : X ⟶ Z} (hf : IsContraction sX sZ f)
    {K : Divisor X} {B : QDivisor X} (hklt : MMP.Mori.IsKltPair sX 3 K B) (hB : 0 ≤ B)
    (hnef : (Divisor.toQDivisor K + B).IsRelativelyNef sX f)
    (hgen : ∃ m : ℕ, 0 < m ∧ ∃ φ : (RationalFunctions X)ˣ, ∀ E : MMP.Mori.PrimeDivisor X,
      f.base E.genericPoint = genericPoint Z →
        ((m : ℤ) • (Divisor.toQDivisor K + B) - Divisor.toQDivisor (principalDivisor φ)).coeff E
          = 0) :
    QDivisor.IsRelativelySemiample f (Divisor.toQDivisor K + B) :=
      by revert X Z sX sZ hX hdimX hQ hZ hdimZ f hf K B hklt hB hnef hgen; first | exact Proof_lem_fourfold_klt_log_elliptic_relative_semiample.solution | exact Proof_lem_fourfold_klt_log_elliptic_relative_semiample.solution _ | exact Proof_lem_fourfold_klt_log_elliptic_relative_semiample.solution _ _ | exact Proof_lem_fourfold_klt_log_elliptic_relative_semiample.solution _ _ _ | exact Proof_lem_fourfold_klt_log_elliptic_relative_semiample.solution _ _ _ _

end MMP.Fourfold

