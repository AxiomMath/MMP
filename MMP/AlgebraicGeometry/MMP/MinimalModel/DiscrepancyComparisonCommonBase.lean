module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBoundaryChange
import MMP.AlgebraicGeometry.MMP.Flip.FiniteGeneration
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.Divisor.Pullback
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
import MMP.Analysis.Complex.CauchyTransformRungeMontel
import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantDltLiftNotNef
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.Divisor.Negativity.CodimTwoCentres
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# Comparison of discrepancies over a common base

Let `f : X ⟶ Y` and `f' : X' ⟶ Y` be proper birational morphisms of normal varieties over an
algebraically closed field of characteristic zero, and `Δ`, `Δ'` `ℚ`-divisors on `X`, `X'` with
`f_*Δ = f'_*Δ'`, `-(K_X + Δ)` `ℚ`-Cartier and `f`-nef and `K_{X'} + Δ'` `ℚ`-Cartier and
`f'`-nef. Then `a(E, X, Δ) ≤ a(E, X', Δ')` for every divisor `E` over `Y` exceptional over `Y`
(Kollár–Mori 3.38), and the inequality is strict when `-(K_X + Δ)` is `f`-ample and `f` is not an
isomorphism above the generic point of `center_Y E`, or when `K_{X'} + Δ'` is `f'`-ample and `f'`
is not an isomorphism above it. The proofs pass to a common normal model `Z` on which `E` is a
prime divisor and apply the negativity lemma to the difference of the two crepant boundaries.

## Main results

* `MMP.Mori.exists_isBirational_compHom_eq`: for birational morphisms `f : X ⟶ Y` and
  `f' : X' ⟶ Y` there is a birational map `φ : X ⇢ X'` with `f' ∘ φ = f`.
* `MMP.Mori.IsCrepantBoundary.isPullback_divisorOfForm_add`: for the crepant boundary `Δ` of
  `(X, B)` on `U` and `K = div(ω)`, `div(p^*ω) + Δ = p^*(K + B)`.
* `MMP.Mori.QDivisor.intersectionNumber_add_eq_of_linearlyEquivalent`: `((K + Δ) · C)` depends on
  `K` only up to linear equivalence; `MMP.Mori.QDivisor.intersectionNumber_neg`:
  `((-D) · C) = -(D · C)`, with `MMP.Mori.QDivisor.IsQCartier.neg`.
* `MMP.Mori.QDivisor.exists_intersectionNumber_pullback_eq_mul`,
  `MMP.Mori.QDivisor.intersectionNumber_pullback_eq_zero_or`: projection of a curve contracted by
  `u ≫ f`: `(u^*L · C)` is `0` when `u(C)` is a point and otherwise `deg(C/u(C)) (L · u(C))`,
  with `u(C)` a proper curve contracted by `f`.
* `MMP.Mori.QDivisor.HasRelativelyAmpleMultiple.intersectionNumber_pos`: an `f`-ample
  `ℚ`-divisor is positive on every proper curve contracted by `f`.
* `MMP.Mori.isDiscrepancy_le_of_isRelativelyNef`: `a(E, X, Δ) ≤ a(E, X', Δ')`.
* `MMP.Mori.isDiscrepancy_lt_of_forall_intersectionNumber_neg`: strict inequality when
  `K_X + Δ` is negative on every curve contracted by `f` and `center_Y E ⊆ f(Ex f)`.
* `MMP.Mori.isDiscrepancy_lt_of_neg_hasRelativelyAmpleMultiple`: strict inequality when
  `-(K_X + Δ)` is `f`-ample and `center_Y E ⊆ f(Ex f)`.
* `MMP.Mori.isDiscrepancy_lt_of_hasRelativelyAmpleMultiple_target`: strict inequality when
  `K_{X'} + Δ'` is `f'`-ample and `center_Y E ⊆ f'(Ex f')`.

## Implementation notes

A divisor `E` over `Y` is a divisor `D` over `X` and a divisor `D'` over `X'` inducing the same
valuation of `k(Y)`. "`f` is not an isomorphism above the generic point of `center_Y E`" is that
this point lies outside `MMP.Mori.biregularLocus f`, and `f`-ampleness of a `ℚ`-divisor is
`MMP.Mori.QDivisor.HasRelativelyAmpleMultiple`. Each result's auxiliary lemmas live in a namespace
`Proof_<tag>` named after its label, opened only for that result; the helpers shared by
the three results (the transform of exceptional divisors, the negativity lemma for exceptional
divisors, the pull-back of a nonzero form, a contracted curve over a point outside the biregular
locus) live in `Proof_lem_km3c_discrepancy_comparison`, which the strict results also open. The
strict results erase the instance `AlgebraicGeometry.IsVariety.toIsIntegral` locally.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Lemma 3.38
-/

@[expose] public section

universe u

namespace MMP.Mori

open CategoryTheory
open AlgebraicGeometry hiding PrimeDivisor

/-- A birational morphism `f : X ⟶ Y` restricts to an isomorphism of a dense open of `X` onto a
dense open of `Y`, under which it is the inclusion of that open. -/
private theorem exists_partialIso_isOver {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : IsBirationalMorphism f) : ∃ e : X.PartialIso Y, e.IsOver f (𝟙 Y) := by
  obtain ⟨e, he⟩ := hf
  obtain ⟨W, hW, hWl, hWr, heq⟩ := Scheme.PartialMap.toRationalMap_eq_iff.mp he
  simp only [Scheme.PartialMap.restrict_hom, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom] at heq
  have hWl' : W ≤ e.source := hWl
  refine ⟨e.restrictSource W hW hWl', ?_⟩
  have h1 : (Scheme.Opens.isoOfLE hWl').inv ≫ (e.source.ι ⁻¹ᵁ W).ι = X.homOfLE hWl' := by
    rw [← cancel_mono e.source.ι, Category.assoc, Scheme.Opens.isoOfLE_inv_ι, Scheme.homOfLE_ι]
  have h2 : X.homOfLE hWr ≫ X.topIso.hom = W.ι := by
    simp only [Scheme.topIso_hom]
    exact Scheme.homOfLE_ι X hWr
  change ((Scheme.Opens.isoOfLE hWl').inv ≫ (e.iso.hom.isoImage (e.source.ι ⁻¹ᵁ W)).hom ≫
    (e.target.ι.isoImage (e.iso.hom ''ᵁ e.source.ι ⁻¹ᵁ W)).hom) ≫
    (e.target.ι ''ᵁ e.iso.hom ''ᵁ e.source.ι ⁻¹ᵁ W).ι ≫ 𝟙 Y = W.ι ≫ f
  rw [Category.comp_id, Category.assoc, Category.assoc, Scheme.Hom.isoImage_hom_ι,
    Scheme.Hom.isoImage_hom_ι_assoc, ← Category.assoc, h1]
  exact heq.trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ f) h2))

/-- For birational morphisms `f : X ⟶ Y` and `f' : X' ⟶ Y`, the birational map
`φ = f'⁻¹ ∘ f : X ⇢ X'` satisfies `f' ∘ φ = f`. -/
public theorem exists_isBirational_compHom_eq {X X' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y}
    (hf : IsBirationalMorphism f) (hf' : IsBirationalMorphism f') :
    ∃ φ : RationalMap X X', φ.IsBirational ∧ φ.compHom f' = f.toRationalMap := by
  obtain ⟨e₁, h₁⟩ := exists_partialIso_isOver hf
  obtain ⟨e₂, h₂⟩ := exists_partialIso_isOver hf'
  set e := e₁.trans e₂.symm
  have h : e.IsOver f f' := h₁.trans h₂.symm
  refine ⟨e.toRationalMap, RationalMap.isBirational_toRationalMap e, ?_⟩
  rw [← Scheme.RationalMap.compHom_toRationalMap]
  refine Scheme.PartialMap.toRationalMap_eq_iff.mpr ⟨e.source, e.dense_source, le_rfl,
    le_top, ?_⟩
  change X.homOfLE le_rfl ≫ (e.iso.hom ≫ e.target.ι) ≫ f' =
    X.homOfLE (le_top : e.source ≤ ⊤) ≫ X.topIso.hom ≫ f
  rw [Category.assoc, h]
  simp

end MMP.Mori

namespace MMP.Mori

open CategoryTheory
open AlgebraicGeometry hiding PrimeDivisor

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

section Crepancy

/-- The order of `c ^ m * g⁻¹` along a point, for nonzero rational functions `c` and `g`. -/
private theorem ord_zpow_mul_inv {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] (z : Y)
    {c g : Y.functionField} (hc : c ≠ 0) (hg : g ≠ 0) (m : ℤ) :
    Y.ord (c ^ m * g⁻¹) z = m * Y.ord c z - Y.ord g z := by
  rw [Scheme.ord_mul (zpow_ne_zero _ hc) (inv_ne_zero hg), MMP.Mori.ord_zpow _ hc,
    ← zpow_neg_one, MMP.Mori.ord_zpow _ hg]
  ring

variable {k : Type u} [Field k] [PerfectField k] {X U : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral U] [CompactSpace U] [IsLocallyNoetherian U] [IsNormal U]

/-- Coefficientwise crepancy: along a prime divisor `F` of `U`, the pull-back of a Cartier
multiple `E = m (K + B)` has coefficient `m (ord_F div(p^*ω) + Δ_F)` when `K = div(ω)`. -/
private theorem coeff_pullback_eq {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) {p : U ⟶ X}
    [IsDominant p] [LocallyOfFiniteType (p ≫ sX)]
    (hY : IsNormalVariety k (p ≫ sX)) (hp : IsBirationalMorphism p) {n n' : ℕ} {K : Divisor X}
    (hK' : K.IsCanonicalDivisor sX n') {B : QDivisor X} {Δ : QDivisor U}
    (hcrep : IsCrepantBoundary sX n K B p hY hp Δ) {m : ℕ} (hm0 : 0 < m) {E : Divisor X}
    (hE : Divisor.toQDivisor E = (m : ℤ) • (Divisor.toQDivisor K + B)) (hEc : E.IsCartier)
    {hB : ∀ Z : irreducibleComponents U, p (componentGenericPoint U Z) ∉ E.supp}
    {Dp : Divisor U} (hDp : E.IsPullback p hB Dp) {ω : RationalPluriForms sX n' 1}
    (hω0 : ω ≠ 0) (hωK : ∀ Γ : MMP.Mori.PrimeDivisor X, Γ.ordForm ω = K.coeff Γ)
    (F : MMP.Mori.PrimeDivisor U) :
    (Dp.coeff F : ℚ) =
      m * ((divisorOfForm (pullbackRationalPluriForms sX p ω)).coeff F + Δ.coeff F) := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hK := (hcrep F).2.1
  obtain rfl : n = n' := by exact_mod_cast hK.1.symm.trans hK'.1
  have hn := hK.topologicalKrullDim_eq
  set D : DivisorOver k sX := ⟨U, p, hY, hp, F⟩ with hD
  obtain ⟨b, N', hb0⟩ := D.exists_ordPullback_eq hX hn
  have hb : ∀ (m : ℤ) (τ : RationalPluriForms sX n m), τ ≠ 0 → D.ordPullback τ =
      U.ord (functionFieldMap p ((ZTensorPower.basis b m).repr τ ())) F.genericPoint + m * N' :=
    hb0
  let := functionFieldAlgebra sX
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨V, hxV, φ, hφ⟩ := hEc (p F.genericPoint)
  let Z0 : irreducibleComponents X := ⟨Set.univ, by
    rw [irreducibleComponents_eq_singleton]; simp⟩
  set c := (ZTensorPower.basis b 1).repr ω () with hc_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hω0
  set g := MMP.Threefold.Mori.Helpers.evalFF Z0 (φ : RationalFunctions X) with hg_def
  have hg : g ≠ 0 := (φ.isUnit.map _).ne_zero
  set c'' : X.functionField := c ^ (m : ℤ) * g⁻¹ with hc''_def
  have hc'' : c'' ≠ 0 := mul_ne_zero (zpow_ne_zero _ hc) (inv_ne_zero hg)
  let τ : RationalPluriForms sX n m := c'' • ZTensorPower.basis b (m : ℤ) ()
  have hτr : (ZTensorPower.basis b (m : ℤ)).repr τ () = c'' := by simp [τ]
  have hτ0 : τ ≠ 0 := smul_ne_zero hc'' ((ZTensorPower.basis b (m : ℤ)).ne_zero ())
  have hKcoeff : ∀ Γ : MMP.Mori.PrimeDivisor X, ∃ NΓ : ℤ,
      (K.coeff Γ : ℤ) = X.ord c Γ.genericPoint + NΓ ∧
      (Γ.ordForm τ : ℤ) = m * X.ord c Γ.genericPoint - X.ord g Γ.genericPoint + m * NΓ := by
    intro Γ
    obtain ⟨NΓ, hNΓ⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
    refine ⟨NΓ, ?_, ?_⟩
    · rw [← hωK Γ, hNΓ 1 ω hω0]
      simp [hc_def]
    · rw [hNΓ _ τ hτ0, hτr, hc''_def, ord_zpow_mul_inv _ hc hg]
  have hgord : ∀ Γ : MMP.Mori.PrimeDivisor X, (Γ.support ∩ V).Nonempty →
      X.ord g Γ.genericPoint = E.coeff Γ := by
    intro Γ hΓ
    rw [hφ Γ hΓ, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord,
      Subsingleton.elim (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents)
        Γ.component Z0]
  have hCq : ∀ Γ : MMP.Mori.PrimeDivisor X,
      (E.coeff Γ : ℚ) = m * (K.coeff Γ + B.coeff Γ) := by
    intro Γ
    have := congrArg (fun D : QDivisor X => D.coeff Γ) hE
    rw [mul_add]
    simpa [zsmul_eq_mul] using this
  have hgen : GeneratesOn B m V τ := by
    refine ⟨hτ0, fun Γ hΓ => ?_⟩
    obtain ⟨NΓ, h1, h2⟩ := hKcoeff Γ
    have h3 := hgord Γ hΓ
    qify at h1 h2 h3
    linear_combination h2 - hCq Γ - h3 - (m : ℚ) * h1
  have hKY : (divisorOfForm (pullbackRationalPluriForms sX p ω)).coeff F =
      U.ord (functionFieldMap p c) F.genericPoint + N' := by
    have e : D.ordPullback ω = (divisorOfForm (pullbackRationalPluriForms sX p ω)).coeff F := by
      rw [coeff_divisorOfForm]
      rfl
    rw [← e, hb 1 ω hω0]
    simp [hc_def]
  have hcoeff : Dp.coeff F = U.ord (functionFieldMap p g) F.genericPoint :=
    MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hDp hφ F hxV Z0
  have hgY : functionFieldMap p g ≠ 0 := (map_ne_zero _).mpr hg
  have hcY : functionFieldMap p c ≠ 0 := (map_ne_zero _).mpr hc
  have hordτ : D.ordPullback τ = m * U.ord (functionFieldMap p c) F.genericPoint
      - U.ord (functionFieldMap p g) F.genericPoint + m * N' := by
    rw [hb _ τ hτ0, hτr, hc''_def, map_mul, map_zpow₀, map_inv₀, ord_zpow_mul_inv _ hcY hgY]
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm0.ne'
  have hdisc : IsDiscrepancy sX n K B D
      ((divisorOfForm (pullbackRationalPluriForms sX p ω)).coeff F - Dp.coeff F / m) := by
    refine ⟨hX, hK, m, hm0, ⟨E, hE, hEc⟩, V, hxV, τ, hgen, ?_⟩
    qify at hordτ hKY hcoeff
    rw [hordτ, hKY, hcoeff]
    field_simp
    ring
  have heq := IsDiscrepancy.eq (hcrep F) hdisc
  field_simp at heq
  linear_combination heq

/-- **Crepancy as a pull-back.** If `Δ` is the crepant boundary of `(X, B)` on `U` and
`K = div(ω)`, then `div(p^*ω) + Δ = p^*(K + B)`. -/
public theorem IsCrepantBoundary.isPullback_divisorOfForm_add {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX)
    {p : U ⟶ X} [IsDominant p] [LocallyOfFiniteType (p ≫ sX)]
    (hY : IsNormalVariety k (p ≫ sX)) (hp : IsBirationalMorphism p) {n n' : ℕ} {K : Divisor X}
    (hK' : K.IsCanonicalDivisor sX n') {B : QDivisor X} {Δ : QDivisor U}
    (hcrep : IsCrepantBoundary sX n K B p hY hp Δ) {ω : RationalPluriForms sX n' 1}
    (hω0 : ω ≠ 0) (hωK : ∀ Γ : MMP.Mori.PrimeDivisor X, Γ.ordForm ω = K.coeff Γ)
    (hLB : ∀ Z : irreducibleComponents U, p (componentGenericPoint U Z) ∉
      (Divisor.toQDivisor K + B).supp) :
    (Divisor.toQDivisor K + B).IsPullback p hLB
      (Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms sX p ω)) + Δ) := by
  intro m hm D hD hDc
  have hB' : ∀ Z : irreducibleComponents U, p (componentGenericPoint U Z) ∉ D.supp :=
    fun Z hZ => hLB Z (by
      rwa [QDivisor.supp_eq_of_toQDivisor_eq (by exact_mod_cast hm.ne') hD] at hZ)
  refine ⟨D.pullback hDc hB', ?_, Divisor.isPullback_pullback hDc hB'⟩
  ext F
  simpa only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add, zsmul_eq_mul,
    Divisor.coeff_toQDivisor, Int.cast_natCast] using
    coeff_pullback_eq hX hY hp hK' hcrep hm hD hDc (Divisor.isPullback_pullback hDc hB') hω0 hωK F

end Crepancy

section Curves

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- Intersection numbers of `K + Δ` along a curve depend on `K` only up to linear equivalence. -/
public theorem QDivisor.intersectionNumber_add_eq_of_linearlyEquivalent [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of k)) [QuasiCompact sX]
    {C : Scheme.{u}} (i : C ⟶ X)
    [IsProper (i ≫ sX)] (hdim : topologicalKrullDim C ≤ 1) {K₁ K₂ : Divisor X}
    (h : K₁.LinearlyEquivalent K₂) (Δ : QDivisor X) (h₁ : (Divisor.toQDivisor K₁ + Δ).IsQCartier)
    (h₂ : (Divisor.toQDivisor K₂ + Δ).IsQCartier) :
    (Divisor.toQDivisor K₁ + Δ).intersectionNumber k sX i hdim h₁ =
      (Divisor.toQDivisor K₂ + Δ).intersectionNumber k sX i hdim h₂ := by
  obtain ⟨D', hD', hD'c⟩ := QDivisor.isCartierDivisor_cartierIndex_smul h₂
  set m := (Divisor.toQDivisor K₂ + Δ).cartierIndex h₂
  have hm := QDivisor.cartierIndex_pos h₂
  obtain ⟨φ, hφ⟩ := h
  set a : Additive (RationalFunctions X)ˣ := (m : ℤ) • Additive.ofMul φ with ha
  set G := D' + principalDivisorHom a with hG_def
  have hGc : G.IsCartier := hD'c.add (Divisor.isCartier_principalDivisor _)
  have hG : Divisor.toQDivisor G = (m : ℤ) • (Divisor.toQDivisor K₁ + Δ) := by
    have e : principalDivisorHom a = (m : ℤ) • (K₁ - K₂) := by
      rw [ha, map_zsmul, principalDivisorHom_apply, toMul_ofMul, hφ]
    rw [hG_def, e, map_add, hD', map_zsmul, map_sub, ← smul_add]
    congr 1
    abel
  have hGD : G.LinearlyEquivalent D' := ⟨a.toMul, by
    rw [hG_def, add_sub_cancel_left, principalDivisorHom_apply]⟩
  rw [QDivisor.intersectionNumber_eq_of_smul k sX i hdim _ h₁ hm G hGc hG,
    QDivisor.intersectionNumber_eq_of_smul k sX i hdim _ h₂ hm D' hD'c hD']
  congr 2
  have := hGc.isInvertibleModule_divisorialSheaf
  have := hD'c.isInvertibleModule_divisorialSheaf
  exact degreeOn_eq_of_iso k sX i hdim hGD.divisorialSheafIso

/-- Intersection numbers are unchanged by an isomorphism of curves over `X`. -/
private theorem intersectionNumber_eq_of_iso_comp [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of k)) [QuasiCompact sX] {C C' : Scheme.{u}} (i : C ⟶ X) (i' : C' ⟶ X)
    [IsProper (i ≫ sX)] [IsProper (i' ≫ sX)] (hdim : topologicalKrullDim C ≤ 1)
    (hdim' : topologicalKrullDim C' ≤ 1) (e : C ≅ C') (he : e.hom ≫ i' = i) (D : QDivisor X)
    (hD : D.IsQCartier) :
    D.intersectionNumber k sX i hdim hD = D.intersectionNumber k sX i' hdim' hD := by
  have := QuasiCompact.compactSpace_of_compactSpace sX
  unfold QDivisor.intersectionNumber Divisor.degreeOn
  have := (QDivisor.isCartierDivisor_cartierIndex_smul hD).isCartier_toDivisor
    |>.isInvertibleModule_divisorialSheaf
  rw [MMP.Threefold.Resolution.degreeOn_eq_of_iso_comp k sX i i' hdim hdim' e he]

/-- The scheme-theoretic image of a proper curve `C ⊆ V` under `u : V ⟶ W` is the reduced
closure of `u(C)`'s generic point, as a closed subscheme over `W`. -/
private theorem exists_iso_ker_subscheme {V W : Scheme.{u}} {sV : V ⟶ Spec (.of k)}
    (C : ProperCurve sV) (u : V ⟶ W) {w : W} (hw : u C.point = w) :
    ∃ e : (C.ι ≫ u).ker.subscheme ≅ (Scheme.IdealSheafData.vanishingIdeal
        (TopologicalSpace.Closeds.closure ({w} : Set W))).subscheme,
      e.hom ≫ Scheme.IdealSheafData.subschemeι _ = (C.ι ≫ u).ker.subschemeι := by
  have hker : (C.ι ≫ u).ker = Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure ({w} : Set W)) := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    congr 1
    ext1
    simp only [TopologicalSpace.Closeds.coe_closure]
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, ProperCurve.range_ι,
      closure_image_closure u.continuous, Set.image_singleton, hw]
  rw [hker]
  exact ⟨Iso.refl _, by simp⟩

end Curves

/-- The negative of a `ℚ`-Cartier `ℚ`-divisor is `ℚ`-Cartier. -/
public theorem QDivisor.IsQCartier.neg {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D : QDivisor X} (h : D.IsQCartier) : (-D).IsQCartier := by
  obtain ⟨m, hm, h⟩ := h
  exact ⟨m, hm, by rw [smul_neg]; exact h.neg⟩

/-- `((-D) · C) = -(D · C)`. -/
public theorem QDivisor.intersectionNumber_neg (k : Type u) [Field k] {X C : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of k)) [QuasiCompact sX]
    (i : C ⟶ X) [IsProper (i ≫ sX)] (hdim : topologicalKrullDim C ≤ 1) {D : QDivisor X}
    (hD : D.IsQCartier) (hD' : (-D).IsQCartier) :
    (-D).intersectionNumber k sX i hdim hD' = -(D.intersectionNumber k sX i hdim hD) := by
  have hadd := QDivisor.intersectionNumber_add' k sX i hdim D (-D) hD hD'
    (by rw [add_neg_cancel]; exact QDivisor.isQCartier_zero)
  have h00 : (0 : QDivisor X).intersectionNumber k sX i hdim QDivisor.isQCartier_zero = 0 := by
    have := QDivisor.intersectionNumber_add' k sX i hdim (0 : QDivisor X) 0
      QDivisor.isQCartier_zero QDivisor.isQCartier_zero (by simpa using QDivisor.isQCartier_zero)
    simp only [add_zero] at this
    linarith
  rw [MMP.Fourfold.intersectionNumber_congr sX i hdim _ QDivisor.isQCartier_zero (add_neg_cancel D),
    h00] at hadd
  linarith

/-- **Projection of a contracted curve.** Let `L' = u^*L` be the pull-back of a `ℚ`-Cartier
`ℚ`-divisor along a proper morphism `u : V ⟶ W` of normal varieties and `C ⊆ V` a proper curve
contracted by `u ≫ f` whose image `u(C)` is not a point. Then `u(C)` is a proper curve of `W`
contracted by `f`, and `(L' · C) = d (L · u(C))` with `d = deg(C → u(C)) > 0`. -/
public theorem QDivisor.exists_intersectionNumber_pullback_eq_mul {k : Type u} [Field k]
    {V W Y : Scheme.{u}} {sV : V ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)}
    [AlgebraicGeometry.IsVariety k sV] [AlgebraicGeometry.IsVariety k sW]
    [IsLocallyNoetherian V] [IsNormal V] [IsLocallyNoetherian W] [IsNormal W]
    (u : V ⟶ W) [IsProper u] (hu : u ≫ sW = sV) (f : W ⟶ Y) {L : QDivisor W}
    (hL : L.IsQCartier)
    {hLB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L.supp}
    {L' : QDivisor V} (h : L.IsPullback u hLB L') (hL' : L'.IsQCartier) (C : ProperCurve sV)
    (hC : C.IsContractedBy (u ≫ f)) (hnc : ¬ ∃ w : W, Set.range (C.ι ≫ u) = {w}) :
    ∃ d : ℚ, 0 < d ∧ ∃ C'' : ProperCurve sW, C''.IsContractedBy f ∧
      L'.intersectionNumber k sV C.ι C.dim_le hL' =
        d * L.intersectionNumber k sW C''.ι C''.dim_le hL := by
  have := C.isCurve
  set φ := C.ι ≫ u with hφ
  have : AlgebraicGeometry.IsCurve k (φ ≫ sW) := by rw [hφ, Category.assoc, hu]; infer_instance
  have : IsProper (φ ≫ sW) := by rw [hφ, Category.assoc, hu]; infer_instance
  have hcurve := isCurve_imageι_comp sW φ hnc
  have key := intersectionNumber_pullback_eq_degreeOver_mul k sV sW u hu C.ι hL h hcurve
  obtain ⟨e, he⟩ := exists_iso_ker_subscheme C u rfl
  have : IsProper φ := IsProper.of_comp φ sW
  have : IsProper (φ.imageι ≫ sW) := isProper_imageι_comp φ sW
  have hdim : topologicalKrullDim (curveSubschemeAt (u C.point)) = 1 :=
    (IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph).symm.trans
      hcurve.topologicalKrullDim_eq_one
  have hprop : IsProper (curveSubschemeAtι (u C.point) ≫ sW) := by
    rw [show curveSubschemeAtι (u C.point) = e.inv ≫ φ.imageι from (Iso.eq_inv_comp _).mpr he,
      Category.assoc]
    infer_instance
  let C'' : ProperCurve sW := ⟨u C.point, ⟨hdim, hprop⟩⟩
  have hC'' : C''.IsContractedBy f := by
    intro x hx
    have hsub : closure ({u C.point} : Set W) ⊆ u '' closure ({C.point} : Set V) :=
      (u.isClosedMap _ isClosed_closure).closure_subset_iff.mpr (by
        rintro _ rfl; exact ⟨C.point, subset_closure rfl, rfl⟩)
    obtain ⟨z, hz, rfl⟩ := hsub hx
    simpa only [Scheme.Hom.comp_apply] using hC z hz
  have hcurve' : AlgebraicGeometry.IsCurve k (φ.imageι ≫ sW) := hcurve
  have hdeg : 0 < degreeOver φ.toImage :=
    degreeOver_pos_of_not_constant k (φ ≫ sW) (φ.imageι ≫ sW) φ.toImage (by simp)
      (not_exists_toImage_eq φ hnc)
  refine ⟨degreeOver φ.toImage, by exact_mod_cast hdeg, C'', hC'', key.trans ?_⟩
  rw [intersectionNumber_eq_of_iso_comp sW φ.imageι C''.ι _ C''.dim_le e he _ hL]

/-- **Projection of a contracted curve.** Let `L' = u^*L` be the pull-back of a `ℚ`-Cartier
`ℚ`-divisor along a proper morphism `u : V ⟶ W` of normal varieties and `C ⊆ V` a proper curve
contracted by `u ≫ f`. Either `(L' · C) = 0` (when `u(C)` is a point), or
`(L' · C) = d (L · u(C))` with `d ≥ 0`, where `u(C)` is a proper curve of `W` contracted by `f`. -/
public theorem QDivisor.intersectionNumber_pullback_eq_zero_or {k : Type u} [Field k]
    {V W Y : Scheme.{u}} {sV : V ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)}
    [AlgebraicGeometry.IsVariety k sV] [AlgebraicGeometry.IsVariety k sW]
    [IsLocallyNoetherian V] [IsNormal V] [IsLocallyNoetherian W] [IsNormal W]
    (u : V ⟶ W) [IsProper u] (hu : u ≫ sW = sV) (f : W ⟶ Y) {L : QDivisor W}
    (hL : L.IsQCartier)
    {hLB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L.supp}
    {L' : QDivisor V} (h : L.IsPullback u hLB L') (hL' : L'.IsQCartier) (C : ProperCurve sV)
    (hC : C.IsContractedBy (u ≫ f)) :
    L'.intersectionNumber k sV C.ι C.dim_le hL' = 0 ∨
      ∃ d : ℚ, 0 ≤ d ∧ ∃ C'' : ProperCurve sW, C''.IsContractedBy f ∧
        L'.intersectionNumber k sV C.ι C.dim_le hL' =
          d * L.intersectionNumber k sW C''.ι C''.dim_le hL := by
  by_cases hpt : ∃ w : W, Set.range (C.ι ≫ u) = {w}
  · have := C.isCurve
    exact .inl (intersectionNumber_pullback_eq_zero k sV sW u hu C.ι hL h hpt)
  · obtain ⟨d, hd, C'', hC'', heq⟩ :=
      QDivisor.exists_intersectionNumber_pullback_eq_mul u hu f hL h hL' C hC hpt
    exact .inr ⟨d, hd.le, C'', hC'', heq⟩

/-- An `f`-ample `ℚ`-divisor (a positive multiple is a Cartier divisor with `f`-ample invertible
sheaf) is positive on every proper curve contracted by `f`. -/
public theorem QDivisor.HasRelativelyAmpleMultiple.intersectionNumber_pos {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] [QuasiCompact sX] {f : X ⟶ Y} {D : QDivisor X}
    (hA : D.HasRelativelyAmpleMultiple f) (hD : D.IsQCartier) (C : ProperCurve sX)
    (hC : C.IsContractedBy f) : 0 < D.intersectionNumber k sX C.ι C.dim_le hD := by
  obtain ⟨m, hm, L, hL, hLeq, hamp⟩ := hA
  rw [QDivisor.intersectionNumber_eq_of_smul k sX C.ι C.dim_le D hD hm L hL hLeq]
  have hpos : 0 < L.degreeOn k sX C.ι C.dim_le hL := by
    haveI := hL.isInvertibleModule_divisorialSheaf
    exact MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy f _ hamp C hC
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  exact div_pos (by exact_mod_cast hpos) hm'

end MMP.Mori

namespace Proof_lem_km3c_discrepancy_comparison

open CategoryTheory
open AlgebraicGeometry hiding PrimeDivisor
open MMP.Mori
open scoped WithZero

/-- An exceptional prime divisor of a rational map has no birational transform. -/
private theorem transformPrimeDivisor_eq_none_of_isExceptional {X Y : Scheme.{u}}
    {φ : RationalMap X Y} {E : PrimeDivisor X} (h : φ.IsExceptional E) :
    φ.transformPrimeDivisor E = none := by
  rcases hQ : φ.transformPrimeDivisor E with _ | Q
  · rfl
  exfalso
  have hdef := (RationalMap.transformPrimeDivisor_eq_some_iff.mp hQ).1
  have hsupp := RationalMap.support_transformPrimeDivisor hQ
  rcases h with h | ⟨-, h⟩
  · exact h hdef
  have hmem : Q.genericPoint ∈ (φ.transform E.idealSheaf.support : Set Y) := by
    rw [← hsupp]
    exact MMP.Flips.primeDivisor_genericPoint_mem_support Q
  have := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp h Q.genericPoint hmem
  rw [Q.coheight_genericPoint] at this
  norm_num at this

/-- The birational transform of a divisor supported on exceptional prime divisors vanishes. -/
private theorem transformDivisor_eq_zero_of_forall_not_isExceptional {X Y : Scheme.{u}}
    {φ : RationalMap X Y} {G : QDivisor X}
    (hG : ∀ P : PrimeDivisor X, ¬ φ.IsExceptional P → G.coeff P = 0) :
    φ.transformDivisor G = 0 := by
  classical
  rw [← Finsupp.sum_single G, Finsupp.sum, map_sum]
  refine Finset.sum_eq_zero fun P hP => RationalMap.transformDivisor_single_of_eq_none
    (transformPrimeDivisor_eq_none_of_isExceptional ?_) _
  by_contra h
  exact Finsupp.mem_support_iff.mp hP (hG P h)

/-- A valuation of `k(X')` is determined by its restriction to `k(Y)` along a birational
morphism `f' : X' ⟶ Y`. -/
private theorem valuation_eq_of_comap_eq {X' Y : Scheme.{u}} [IsIntegral X'] [IsIntegral Y]
    {f' : X' ⟶ Y} (hf' : IsBirationalMorphism f') [IsDominant f']
    {v w : Valuation X'.functionField ℤᵐ⁰}
    (h : v.comap (functionFieldMap f') = w.comap (functionFieldMap f')) : v = w :=
  Valuation.ext fun t => by
    obtain ⟨s, rfl⟩ := hf'.functionFieldMap_bijective.2 t
    exact congrArg (fun u => u s) h

/-- **Negativity for exceptional divisors.** Let `h : Z ⟶ Y` be a proper birational morphism of
normal varieties and `H` an `h`-nef `ℚ`-divisor on `Z` supported on `h`-exceptional prime
divisors. Then `-H` is effective. -/
private theorem isEffective_neg_of_isRelativelyNef_of_coeff_eq_zero (k : Type u) [Field k]
    {Y Z : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k)) [QuasiCompact sZ]
    [IsLocallyNoetherian Z] [IsNormal Z] (hY : IsNormalVariety k sY) (hZ : IsNormalVariety k sZ)
    (h : Z ⟶ Y) (hh : h ≫ sY = sZ) [IsProper h] (hhb : IsBirationalMorphism h) {H : QDivisor Z}
    (hnef : H.IsRelativelyNef sZ h)
    (hexc : ∀ F : PrimeDivisor Z, ¬ RationalMap.IsExceptional (X := Z) h.toRationalMap F →
      H.coeff F = 0) :
    (-H).IsEffective :=
  (QDivisor.isEffective_iff_isEffective_transformDivisor_of_isRelativelyNef_neg k sY sZ hY hZ h
    hh hhb hnef.1.neg (by rwa [neg_neg])).mpr <| by
      rw [map_neg, transformDivisor_eq_zero_of_forall_not_isExceptional hexc, neg_zero]
      exact DivisorWithCoeffs.isEffective_zero

end Proof_lem_km3c_discrepancy_comparison

namespace MMP.Mori

open CategoryTheory
open AlgebraicGeometry hiding PrimeDivisor
open scoped WithZero
open Proof_lem_km3c_discrepancy_comparison

/-- **Comparison of discrepancies** (Kollár–Mori 3.38). Let `f : X ⟶ Y`, `f' : X' ⟶ Y` be
proper birational morphisms of normal varieties over an algebraically closed field of
characteristic zero, with canonical divisors `K_X`, `K_{X'}` of dimension `n`, and `Δ`, `Δ'`
`ℚ`-divisors on `X`, `X'` with `f_*Δ = f'_*Δ'`, `-(K_X + Δ)` `ℚ`-Cartier and `f`-nef and
`K_{X'} + Δ'` `ℚ`-Cartier and `f'`-nef. Let `D` be a divisor over `X` and `D'` a divisor over
`X'` inducing the same valuation of `k(Y)`, exceptional over `Y`. If `a = a(D, X, Δ)` and
`a' = a(D', X', Δ')`, then `a ≤ a'`. -/
@[mmp "lem_km3c_discrepancy_comparison"]
public theorem isDiscrepancy_le_of_isRelativelyNef {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {n : ℕ} {X X' Y : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [QuasiCompact sX] [QuasiCompact sX']
    (hX : IsNormalVariety k sX) (hX' : IsNormalVariety k sX') (hY : IsNormalVariety k sY)
    {f : X ⟶ Y} {f' : X' ⟶ Y} [IsProper f] [IsProper f']
    (hfs : f ≫ sY = sX) (hfs' : f' ≫ sY = sX')
    (hf : IsBirationalMorphism f) (hf' : IsBirationalMorphism f')
    {KX : Divisor X} {KX' : Divisor X'} (hK : KX.IsCanonicalDivisor sX n)
    (hK' : KX'.IsCanonicalDivisor sX' n) {Δ : QDivisor X} {Δ' : QDivisor X'}
    (hΔ : RationalMap.transformDivisor (X := X) f.toRationalMap Δ =
      RationalMap.transformDivisor (X := X') f'.toRationalMap Δ')
    (hN : QDivisor.IsRelativelyNef sX f (-(Divisor.toQDivisor KX + Δ)))
    (hN' : QDivisor.IsRelativelyNef sX' f' (Divisor.toQDivisor KX' + Δ'))
    (D : DivisorOver k sX) (D' : DivisorOver k sX')
    (hv : haveI : IsIntegral Y := hY.1.toIsIntegral
      haveI : IsDominant f := hf.isDominant
      haveI : IsDominant f' := hf'.isDominant
      D.valuation.comap (functionFieldMap f) = D'.valuation.comap (functionFieldMap f'))
    (hE : RationalMap.IsExceptional (X := D.Y) (D.f ≫ f).toRationalMap D.E)
    {a a' : ℚ} (ha : IsDiscrepancy sX n KX Δ D a) (ha' : IsDiscrepancy sX' n KX' Δ' D' a') :
    a ≤ a' := by
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : IsNormal Y := hY.2
  haveI := hY.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  haveI : IsDominant f := hf.isDominant
  haveI : IsDominant f' := hf'.isDominant
  obtain ⟨φ, hφ, hφS⟩ := exists_isBirational_compHom_eq hf hf'
  obtain ⟨Z, g, g', hZ, hg, hgp, hg'p, hg', -, hcomm, P, hP⟩ :=
    exists_isNormalVariety_isProper_isBirationalMorphism_primeDivisor_valuation_eq hX hX' f f' φ
      hφ hφS D
  haveI := hgp
  haveI := hg'p
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sX)
  haveI : IsDominant g := hg.isDominant
  haveI : IsDominant g' := hg'.isDominant
  have hZ' : IsNormalVariety k (g' ≫ sX') := by
    rwa [← hfs', ← Category.assoc, ← hcomm, Category.assoc, hfs]
  obtain ⟨⟨ΔZ, hΔZ, -⟩, -⟩ := IsPair.existsUnique_isCrepantBoundary ha.isPair hK g hZ hg
  obtain ⟨⟨ΔZ', hΔZ', -⟩, -⟩ := IsPair.existsUnique_isCrepantBoundary ha'.isPair hK' g' hZ' hg'
  -- `H = ∑_F (a(F, X, Δ) - a(F, X', Δ')) F`
  obtain ⟨hHnef, hHexc⟩ := isRelativelyNef_of_isDiscrepancy_sub hX hX' hY hfs hfs' hf hf' hK hK'
    hΔ hN hN' hZ hg hg' hcomm (ΔZ' - ΔZ) fun F b b' hb hb' => by
      have e1 := (hΔZ F).eq hb
      have e2 := (hΔZ' F).eq hb'
      change ΔZ'.coeff F - ΔZ.coeff F = b - b'
      linarith
  -- the negativity lemma applied to `-H`
  have hP0 : (0 : ℚ) ≤ -(ΔZ'.coeff P - ΔZ.coeff P) :=
    DivisorWithCoeffs.isEffective_iff_nonneg.mp
      (isEffective_neg_of_isRelativelyNef_of_coeff_eq_zero k sY (g ≫ sX) hY hZ (g ≫ f)
        (by rw [Category.assoc, hfs]) (isBirationalMorphism_comp_of_isBirational f g
          (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hf)
          (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hg)) hHnef hHexc) P
  -- the coefficient at `E` is computed on `Z`, on `X` and on `X'`
  have hv' : D'.valuation = (⟨Z, g', hZ', hg', P⟩ : DivisorOver k sX').valuation := by
    refine valuation_eq_of_comap_eq hf' (hv.symm.trans ?_)
    rw [← hP]
    refine Valuation.ext fun t => ?_
    change P.divisorialValuation (functionFieldMap g (functionFieldMap f t)) =
      P.divisorialValuation (functionFieldMap g' (functionFieldMap f' t))
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_congr hcomm]
  have e1 : a = -ΔZ.coeff P := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq
    ⟨hX, hK, by simpa only [neg_neg] using hN.1.neg⟩ hP.symm ha (hΔZ P)
  have e2 : a' = -ΔZ'.coeff P :=
    MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq ⟨hX', hK', hN'.1⟩ hv' ha' (hΔZ' P)
  linarith

end MMP.Mori

namespace Proof_lem_km3c_discrepancy_comparison

open CategoryTheory
open AlgebraicGeometry hiding PrimeDivisor
open MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

section Crepancy

variable {k : Type u} [Field k] [PerfectField k] {X U : Scheme.{u}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral U] [CompactSpace U] [IsLocallyNoetherian U] [IsNormal U]

omit [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace U]
    [IsLocallyNoetherian U] [IsNormal U] in
/-- The pull-back of a nonzero rational form along a birational morphism is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX)
    {p : U ⟶ X} [IsDominant p] (hp : IsBirationalMorphism p) {n : ℕ}
    (hn : topologicalKrullDim X = n) {m : ℤ} {τ : RationalPluriForms sX n m} (hτ : τ ≠ 0) :
    pullbackRationalPluriForms sX p τ ≠ 0 := by
  let := functionFieldAlgebra sX
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have hbij := hp.functionFieldMap_bijective
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX p hbij hd
  let := functionFieldAlgebra (p ≫ sX)
  let := functionFieldMapAlgebra p
  have := isScalarTower_functionFieldMap sX p
  have hpull : pullbackRationalPluriForms sX p τ = pullbackFormsAlong hω m τ :=
    pullbackForms_eq hω m τ
  have hrepr := repr_pullbackFormsAlong hω m τ
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := hpull ▸ h0
  have h1 : algebraMap X.functionField U.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← hrepr, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

end Crepancy

section Curves

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- A proper curve has more than one point. -/
private theorem not_subsingleton_range_ι {sX : X ⟶ Spec (.of k)} (C : ProperCurve sX) :
    ¬ (Set.range C.ι).Subsingleton := fun hs => by
  have : Subsingleton C.scheme := ⟨fun a b => C.ι.isEmbedding.injective (hs ⟨a, rfl⟩ ⟨b, rfl⟩)⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
  rw [C.dim_eq] at h0
  exact absurd h0 (by decide)

end Curves

/-- The divisors of two nonzero rational top forms on a normal variety are linearly
equivalent. -/
private theorem linearlyEquivalent_divisorOfForm {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) {τ ω : RationalPluriForms sX n 1} (hτ : τ ≠ 0)
    (hω : ω ≠ 0) : Divisor.LinearlyEquivalent (divisorOfForm τ) (divisorOfForm ω) := by
  let := functionFieldAlgebra sX
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨b⟩ := MMP.Positivity.exists_basis_topForms hX hn
  set c := (ZTensorPower.basis b 1).repr ω () with hc_def
  set e := (ZTensorPower.basis b 1).repr τ () with he_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hω
  have he : e ≠ 0 := repr_ne_zero_of_ne_zero b hτ
  obtain ⟨φ, hφ⟩ := MMP.Positivity.exists_units_of_ne_zero (mul_ne_zero he (inv_ne_zero hc))
  refine ⟨φ, ?_⟩
  ext Γ
  obtain ⟨N, hN⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
  have e1 := hN 1 ω hω
  have e2 := hN 1 τ hτ
  rw [← hc_def] at e1
  rw [← he_def] at e2
  rw [DivisorWithCoeffs.coeff_sub, coeff_principalDivisor, hφ Γ,
    Scheme.ord_mul he (inv_ne_zero hc), ← zpow_neg_one, ord_zpow _ hc, coeff_divisorOfForm,
    coeff_divisorOfForm, e1, e2]
  ring

/-- The fibre of a proper morphism `f` of `k`-schemes of finite type over a closed point is proper
over `k`. -/
private theorem isProper_fiberι_comp (k : Type u) [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (f : Y ⟶ X) [IsProper f] (x : X)
    (hx : IsClosed ({x} : Set X)) : IsProper (f.fiberι x ≫ f ≫ sX) := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  have : LocallyOfFiniteType (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_locallyOfFiniteType.mp hx
  have : IsFinite (X.fromSpecResidueField x ≫ sX) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  have : IsProper (f.fiberToSpecResidueField x) :=
    inferInstanceAs (IsProper (Limits.pullback.snd f (X.fromSpecResidueField x)))
  rw [Scheme.Hom.fiber_fac_assoc]
  infer_instance

/-- An injective morphism `ι : W ⟶ Y` to a separated `k`-scheme of finite type maps a proper curve
of `W` onto a proper curve of `Y`. -/
private theorem isProperCurve_of_injective {k : Type u} [Field k] {W Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsSeparated sY] [LocallyOfFiniteType sY] (ι : W ⟶ Y)
    (hι : Function.Injective ι) (C : ProperCurve (ι ≫ sY)) : IsProperCurve sY (ι C.point) := by
  have hφsY : (C.ι ≫ ι) ≫ sY = C.ι ≫ ι ≫ sY := Category.assoc _ _ _
  have : AlgebraicGeometry.IsCurve k ((C.ι ≫ ι) ≫ sY) := hφsY ▸ C.isCurve
  have : IsProper ((C.ι ≫ ι) ≫ sY) := by rw [hφsY]; infer_instance
  have hnc : ¬ ∃ z, Set.range (C.ι ≫ ι) = {z} := by
    rintro ⟨z, hz⟩
    refine not_subsingleton_range_ι C ?_
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    have ha : (C.ι ≫ ι) a ∈ ({z} : Set Y) := hz ▸ ⟨a, rfl⟩
    have hb : (C.ι ≫ ι) b ∈ ({z} : Set Y) := hz ▸ ⟨b, rfl⟩
    exact hι (by simpa using ha.trans hb.symm)
  have hker := C.ker_comp ι
  constructor
  · have h1 := (MMP.Mori.isCurve_imageι_comp sY (C.ι ≫ ι) hnc).topologicalKrullDim_eq_one
    change topologicalKrullDim (C.ι ≫ ι).ker.subscheme = 1 at h1
    rwa [hker] at h1
  · have h1 : IsProper ((C.ι ≫ ι).imageι ≫ sY) := isProper_imageι_comp _ sY
    change IsProper ((C.ι ≫ ι).ker.subschemeι ≫ sY) at h1
    rwa [hker] at h1

section Contracted

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- A proper curve lying in a fibre of `f` is contracted by `f`. -/
private theorem isContractedBy_of_closure_subset_preimage {Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {C : ProperCurve sX} {f : X ⟶ Y} {y : Y}
    (h : closure {C.point} ⊆ f.base ⁻¹' {y}) : C.IsContractedBy f :=
  fun _ hz => (h hz).trans (h (subset_closure rfl)).symm

/-- **A contracted curve over a point outside the biregular locus.** Let `f : X ⟶ Y` be a proper
birational morphism of varieties onto a normal variety and `y` a closed point of `Y` over which
`f` is not an isomorphism. Then the fibre `f⁻¹(y)` contains a proper curve `C ⊆ X`, which is then
contracted by `f`. -/
private theorem exists_properCurve_isContractedBy_of_notMem_biregularLocus {k : Type u}
    [Field k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    (hX : AlgebraicGeometry.IsVariety k sX) (hY : IsNormalVariety k sY) (f : X ⟶ Y)
    (hfs : f ≫ sY = sX) [IsProper f] (hf : IsBirationalMorphism f) {y : Y}
    (hy : IsClosed ({y} : Set Y)) (hyV : y ∉ biregularLocus f) :
    ∃ C : ProperCurve sX, C.IsContractedBy f ∧ closure {C.point} ⊆ f.base ⁻¹' {y} := by
  have : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  have : IsSeparated sX := hX.toIsSeparated
  have := hX.toIsIntegral
  have := hY.1.toIsIntegral
  haveI : IsNormal Y := hY.2
  haveI : IsDominant f := hf.isDominant
  obtain ⟨-, hEx, -⟩ := MMP.Resolution.Bridges.isIso_finiteFibreLocus_and_exceptionalSet_eq k hX
    hY.1 f hfs (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hf)
  obtain ⟨x, hx⟩ := f.surjective y
  have hxE : x ∈ (exceptionalSet f : Set X) := by
    change x ∉ (f ⁻¹ᵁ biregularLocus f : Set X)
    simpa [hx] using hyV
  rw [hEx, Set.mem_setOf_eq, hx] at hxE
  set ι := f.fiberι y
  set sF := ι ≫ sX
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have : IsProper sF := by simpa [sF, ι, hfs] using isProper_fiberι_comp k sY f y hy
  have : IsLocallyNoetherian (f.fiber y) := LocallyOfFiniteType.isLocallyNoetherian sF
  have : CompactSpace (f.fiber y) := QuasiCompact.compactSpace_of_compactSpace sF
  have hdim : 0 < topologicalKrullDim (f.fiber y) := by
    rw [IsHomeomorph.topologicalKrullDim_eq _ (f.fiberHomeo y).isHomeomorph]
    exact hxE
  rw [topologicalKrullDim, Order.krullDim_pos_iff] at hdim
  obtain ⟨A, B, hAB⟩ := hdim
  set η := B.isIrreducible.genericPoint
  have hη : closure ({η} : Set (f.fiber y)) = B := by
    rw [B.isIrreducible.isGenericPoint_genericPoint_closure, B.isClosed.closure_eq]
  obtain ⟨x₀, hx₀A, hx₀⟩ := A.isClosed.exists_closed_singleton A.isIrreducible.nonempty
  have hAB' : (A : Set (f.fiber y)) ⊆ B := hAB.le
  have hηx₀ : η ⤳ x₀ := specializes_iff_mem_closure.mpr (by rw [hη]; exact hAB' hx₀A)
  have hηne : η ∉ ({x₀} : Set (f.fiber y)) := by
    intro h
    rw [Set.mem_singleton_iff] at h
    apply hAB.not_ge
    intro z hz
    have hz' : z ∈ closure ({η} : Set (f.fiber y)) := by rwa [hη]
    rw [h, hx₀.closure_eq, Set.mem_singleton_iff] at hz'
    rw [hz']
    exact hx₀A
  obtain ⟨y', -, -, -, hcurve⟩ := MMP.Fourfold.exists_isProperCurve_of_specializes sF hηx₀ hx₀ hx₀
    (Set.mem_singleton _) hηne
  let C' : ProperCurve sF := ⟨y', hcurve⟩
  let C : ProperCurve sX := ⟨ι y', isProperCurve_of_injective sX ι ι.isEmbedding.injective C'⟩
  have hrι : Set.range ι = f.base ⁻¹' {y} := f.range_fiberι y
  have hcl : closure {C.point} ⊆ f.base ⁻¹' {y} :=
    closure_minimal (by rintro _ rfl; rw [← hrι]; exact ⟨y', rfl⟩) (hy.preimage f.continuous)
  exact ⟨C, isContractedBy_of_closure_subset_preimage hcl, hcl⟩

end Contracted

/-- **The degree of `Δ'_Z - Δ_Z` as a difference of pull-backs.** With `K_Z = div(g^*ω)` and
`K'_Z = div(g'^*ω')` for `K_X = div(ω)`, `K_{X'} = div(ω')`, crepancy gives
`K_Z + Δ_Z = g^*(K_X + Δ)` and `K'_Z + Δ'_Z = g'^*(K_{X'} + Δ')`, and since `K'_Z ∼ K_Z` the degree
of `Δ'_Z - Δ_Z` on a proper curve `C ⊆ Z` is `((K'_Z + Δ'_Z) · C) - ((K_Z + Δ_Z) · C)`. -/
private theorem exists_intersectionNumber_sub_eq_of_isCrepantBoundary {k : Type u} [Field k]
    [PerfectField k] {n : ℕ} {X X' Y Z : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [QuasiCompact sX] [QuasiCompact sX'] (hX : IsNormalVariety k sX)
    (hX' : IsNormalVariety k sX') {f : X ⟶ Y} {f' : X' ⟶ Y} (hfs : f ≫ sY = sX)
    (hfs' : f' ≫ sY = sX') {KX : Divisor X} {KX' : Divisor X'} (hK : KX.IsCanonicalDivisor sX n)
    (hK' : KX'.IsCanonicalDivisor sX' n) {Δ : QDivisor X} {Δ' : QDivisor X'}
    (hQ : (Divisor.toQDivisor KX + Δ).IsQCartier) (hQ' : (Divisor.toQDivisor KX' + Δ').IsQCartier)
    {g : Z ⟶ X} {g' : Z ⟶ X'} [IsProper g] [IsProper g'] (hZ : IsNormalVariety k (g ≫ sX))
    (hZ' : IsNormalVariety k (g' ≫ sX'))
    (hg : IsBirationalMorphism g) (hg' : IsBirationalMorphism g') (hcomm : g ≫ f = g' ≫ f')
    {ΔZ ΔZ' : QDivisor Z} (hΔZ : IsCrepantBoundary sX n KX Δ g hZ hg ΔZ)
    (hΔZ' : IsCrepantBoundary sX' n KX' Δ' g' hZ' hg' ΔZ') (hHq : (ΔZ' - ΔZ).IsQCartier)
    (C : ProperCurve (g ≫ sX)) :
    ∃ (hLB : ∀ W : irreducibleComponents Z, g (componentGenericPoint Z W) ∉
        (Divisor.toQDivisor KX + Δ).supp)
      (hLB' : ∀ W : irreducibleComponents Z, g' (componentGenericPoint Z W) ∉
        (Divisor.toQDivisor KX' + Δ').supp) (L L' : QDivisor Z)
      (_ : (Divisor.toQDivisor KX + Δ).IsPullback g hLB L)
      (_ : (Divisor.toQDivisor KX' + Δ').IsPullback g' hLB' L')
      (hL : L.IsQCartier) (hL' : L'.IsQCartier),
      (ΔZ' - ΔZ).intersectionNumber k (g ≫ sX) C.ι C.dim_le hHq =
        L'.intersectionNumber k (g ≫ sX) C.ι C.dim_le hL' -
          L.intersectionNumber k (g ≫ sX) C.ι C.dim_le hL := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType sX' := hX'.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (g ≫ sX) := hZ.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (g' ≫ sX') := hZ'.1.toLocallyOfFiniteType
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace sX'
  have : QuasiCompact (g ≫ sX) := hZ.1.toQuasiCompact
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (g ≫ sX)
  have : IsDominant g := hg.isDominant
  have : IsDominant g' := hg'.isDominant
  have : AlgebraicGeometry.IsVariety k sX := hX.1
  have : AlgebraicGeometry.IsVariety k sX' := hX'.1
  have : AlgebraicGeometry.IsVariety k (g ≫ sX) := hZ.1
  have hsZ : g' ≫ sX' = g ≫ sX := by
    rw [← hfs', ← Category.assoc, ← hcomm, Category.assoc, hfs]
  have hnZ : topologicalKrullDim Z = n := by
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (g ≫ sX) hg, hK.1]
  obtain ⟨ω, hω0, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain ⟨ω', hω0', hωK'⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX' hK'
  have hLB : ∀ W : irreducibleComponents Z, g (componentGenericPoint Z W) ∉
      (Divisor.toQDivisor KX + Δ).supp := fun W => by
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, map_genericPoint_of_isDominant]
    exact MMP.Fourfold.genericPoint_notMem_supp _
  have hLB' : ∀ W : irreducibleComponents Z, g' (componentGenericPoint Z W) ∉
      (Divisor.toQDivisor KX' + Δ').supp := fun W => by
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, map_genericPoint_of_isDominant]
    exact MMP.Fourfold.genericPoint_notMem_supp _
  set KZ := divisorOfForm (pullbackRationalPluriForms sX g ω)
  set KZ' := divisorOfForm (pullbackRationalPluriForms sX' g' ω')
  have hpb := hΔZ.isPullback_divisorOfForm_add hX hZ hg hK hω0 hωK hLB
  have hpb' := hΔZ'.isPullback_divisorOfForm_add hX' hZ' hg' hK' hω0' hωK' hLB'
  have hB := hpb.isQCartier hQ
  have hA := hpb'.isQCartier hQ'
  have hne : pullbackRationalPluriForms sX g ω ≠ 0 :=
    pullbackRationalPluriForms_ne_zero hX hg hK.1 hω0
  have hne' : pullbackRationalPluriForms sX' g' ω' ≠ 0 :=
    pullbackRationalPluriForms_ne_zero hX' hg' hK'.1 hω0'
  have hlin : KZ'.LinearlyEquivalent KZ := by
    have key : ∀ (s : Z ⟶ Spec (.of k)) (_ : s = g ≫ sX) [LocallyOfFiniteType s]
        (τ : RationalPluriForms s n 1), τ ≠ 0 → (divisorOfForm τ).LinearlyEquivalent KZ := by
      rintro s rfl _ τ hτ
      exact linearlyEquivalent_divisorOfForm hZ hnZ hτ hne
    exact key _ hsZ _ hne'
  have hA2 : (Divisor.toQDivisor KZ + ΔZ').IsQCartier := hA.add_of_linearlyEquivalent hlin
  have hBn : (-(Divisor.toQDivisor KZ + ΔZ)).IsQCartier := hB.neg
  have hH : ΔZ' - ΔZ = (Divisor.toQDivisor KZ + ΔZ') + -(Divisor.toQDivisor KZ + ΔZ) := by abel
  refine ⟨hLB, hLB', _, _, hpb, hpb', hB, hA, ?_⟩
  rw [MMP.Fourfold.intersectionNumber_congr _ C.ι C.dim_le hHq (hA2.add hBn) hH,
    QDivisor.intersectionNumber_add' k _ C.ι C.dim_le _ _ hA2 hBn,
    QDivisor.intersectionNumber_neg k _ C.ι C.dim_le hB hBn,
    ← QDivisor.intersectionNumber_add_eq_of_linearlyEquivalent (g ≫ sX) C.ι C.dim_le hlin ΔZ' hA
      hA2]
  ring

end Proof_lem_km3c_discrepancy_comparison

namespace Proof_lem_km3c_discrepancy_comparison_strict_source

open CategoryTheory
open AlgebraicGeometry hiding PrimeDivisor
open MMP.Mori
open Proof_lem_km3c_discrepancy_comparison
open scoped WithZero

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- **Strict positivity of `Δ'_Z - Δ_Z` on a curve lifting a `(K_X + Δ)`-negative curve.** With
`K_X = div(ω)`, `K_{X'} = div(ω')`, crepancy says `K_Z + Δ_Z = g^*(K_X + Δ)` and
`K'_Z + Δ'_Z = g'^*(K_{X'} + Δ')` for `K_Z = div(g^*ω)`, `K'_Z = div(g'^*ω')`, and `K'_Z ∼ K_Z`.
So on a curve `C` contracted by `g ≫ f` the degree of `Δ'_Z - Δ_Z` is
`(g'^*(K_{X'} + Δ') · C) - (g^*(K_X + Δ) · C)`. The first term is non-negative since `g'(C)` is a
point or a curve contracted by `f'`; if `g(C)` is a curve `C_X` with `((K_X + Δ) · C_X) < 0`, the
second is `deg(C/C_X) ((K_X + Δ) · C_X) < 0`. -/
private theorem intersectionNumber_sub_pos_of_isCrepantBoundary {k : Type u} [Field k]
    [PerfectField k]
    {n : ℕ} {X X' Y Z : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [QuasiCompact sX] [QuasiCompact sX']
    (hX : IsNormalVariety k sX) (hX' : IsNormalVariety k sX') (hY : IsNormalVariety k sY)
    {f : X ⟶ Y} {f' : X' ⟶ Y} [IsProper f] [IsProper f'] (hfs : f ≫ sY = sX)
    (hfs' : f' ≫ sY = sX') (hf : IsBirationalMorphism f) (hf' : IsBirationalMorphism f')
    {KX : Divisor X} {KX' : Divisor X'} (hK : KX.IsCanonicalDivisor sX n)
    (hK' : KX'.IsCanonicalDivisor sX' n) {Δ : QDivisor X} {Δ' : QDivisor X'}
    (hN : QDivisor.IsRelativelyNef sX f (-(Divisor.toQDivisor KX + Δ)))
    (hN' : QDivisor.IsRelativelyNef sX' f' (Divisor.toQDivisor KX' + Δ'))
    {g : Z ⟶ X} {g' : Z ⟶ X'} [IsProper g] [IsProper g'] (hZ : IsNormalVariety k (g ≫ sX))
    (hZ' : IsNormalVariety k (g' ≫ sX'))
    (hg : IsBirationalMorphism g) (hg' : IsBirationalMorphism g') (hcomm : g ≫ f = g' ≫ f')
    {ΔZ ΔZ' : QDivisor Z} (hΔZ : IsCrepantBoundary sX n KX Δ g hZ hg ΔZ)
    (hΔZ' : IsCrepantBoundary sX' n KX' Δ' g' hZ' hg' ΔZ') (hHq : (ΔZ' - ΔZ).IsQCartier)
    (C : ProperCurve (g ≫ sX)) (hC : C.IsContractedBy (g ≫ f)) (CX : ProperCurve sX)
    (hgC : g C.point = CX.point)
    (hneg : ∀ hQ : (Divisor.toQDivisor KX + Δ).IsQCartier,
      (Divisor.toQDivisor KX + Δ).intersectionNumber k sX CX.ι CX.dim_le hQ < 0) :
    0 < (ΔZ' - ΔZ).intersectionNumber k (g ≫ sX) C.ι C.dim_le hHq := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType sX' := hX'.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (g ≫ sX) := hZ.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (g' ≫ sX') := hZ'.1.toLocallyOfFiniteType
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace sX'
  have : QuasiCompact (g ≫ sX) := hZ.1.toQuasiCompact
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (g ≫ sX)
  have : IsDominant g := hg.isDominant
  have : IsDominant g' := hg'.isDominant
  have : AlgebraicGeometry.IsVariety k sX := hX.1
  have : AlgebraicGeometry.IsVariety k sX' := hX'.1
  have : AlgebraicGeometry.IsVariety k (g ≫ sX) := hZ.1
  have hsZ : g' ≫ sX' = g ≫ sX := by
    rw [← hfs', ← Category.assoc, ← hcomm, Category.assoc, hfs]
  have hQ : (Divisor.toQDivisor KX + Δ).IsQCartier := by
    simpa using hN.1.neg
  have hQ' : (Divisor.toQDivisor KX' + Δ').IsQCartier := hN'.1
  obtain ⟨_, _, L, L', hpb, hpb', hB, hA, heq⟩ :=
    exists_intersectionNumber_sub_eq_of_isCrepantBoundary hX hX' hfs hfs' hK hK' hQ hQ' hZ hZ' hg
      hg' hcomm hΔZ hΔZ' hHq C
  rw [heq]
  have h1 : 0 ≤ L'.intersectionNumber k (g ≫ sX) C.ι C.dim_le hA := by
    rcases QDivisor.intersectionNumber_pullback_eq_zero_or g' hsZ f' hQ' hpb' hA C
        (by rw [← hcomm]; exact hC) with h0 | ⟨d, hd, C'', hC'', heq⟩
    · rw [h0]
    · rw [heq]
      exact mul_nonneg hd
        (MMP.Fourfold.QDivisor.IsRelativelyNef.intersectionNumber_nonneg sX' hN' hQ' C'' hC'')
  have h2 : L.intersectionNumber k (g ≫ sX) C.ι C.dim_le hB < 0 := by
    haveI := C.isCurve
    haveI := CX.isCurve
    set φ := C.ι ≫ g with hφ
    obtain ⟨e, he⟩ := exists_iso_ker_subscheme C g hgC
    haveI : AlgebraicGeometry.IsCurve k (φ ≫ sX) := by rw [hφ, Category.assoc]; infer_instance
    haveI : IsProper (C.ι ≫ g ≫ sX) := C.isProper_ι_comp
    haveI : IsProper (φ ≫ sX) := by rw [hφ, Category.assoc]; infer_instance
    have hnc : ¬ ∃ x : X, Set.range φ = {x} := by
      intro hpt
      have := subsingleton_image sX φ hpt
      have h0 : topologicalKrullDim φ.image ≤ 0 := topologicalKrullDim_zero_of_discreteTopology _
      rw [IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph,
        CX.dim_eq] at h0
      norm_num at h0
    have hcurve := isCurve_imageι_comp sX φ hnc
    have key := intersectionNumber_pullback_eq_degreeOver_mul k (g ≫ sX) sX g rfl C.ι hQ hpb
      hcurve
    haveI : AlgebraicGeometry.IsCurve k (φ.imageι ≫ sX) := hcurve
    haveI : IsProper φ := IsProper.of_comp φ sX
    haveI : IsProper (φ.imageι ≫ sX) := isProper_imageι_comp φ sX
    have hd : (0 : ℚ) < degreeOver φ.toImage := by
      exact_mod_cast degreeOver_pos_of_not_constant k (φ ≫ sX) (φ.imageι ≫ sX) φ.toImage
        (by simp) (not_exists_toImage_eq φ hnc)
    rw [key, intersectionNumber_eq_of_iso_comp sX φ.imageι CX.ι _ CX.dim_le e he _ hQ]
    exact mul_neg_of_pos_of_neg hd (hneg hQ)
  linarith

/-- A proper curve `C_X` contracted by `f` lifts along a proper surjection `g : Z ⟶ X` of
varieties to a proper curve `C` of `Z` with `g(C) = C_X`, contracted by `g ≫ f`. -/
private theorem exists_properCurve_lift {k : Type u} [Field k] {X Y Z : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (g : Z ⟶ X) [IsProper g] [Surjective g]
    (hZ : IsNormalVariety k (g ≫ sX)) {f : X ⟶ Y} (CX : ProperCurve sX)
    (hCX : CX.IsContractedBy f) :
    ∃ C : ProperCurve (g ≫ sX), g C.point = CX.point ∧ C.IsContractedBy (g ≫ f) := by
  obtain ⟨C, hCimg⟩ := ProperCurve.exists_image_closure_eq_of_surjective hZ.1 hX.1 g rfl CX
  have hgC : g C.point = CX.point := by
    have h1 : closure ({g C.point} : Set X) = closure {CX.point} := by
      rw [← hCimg, ← Set.image_singleton, g.isClosedMap.closure_image_eq_of_continuous g.continuous]
    exact (inseparable_iff_closure_eq.mpr h1).eq
  refine ⟨C, hgC, fun w hw => ?_⟩
  have hw' : g w ∈ closure {CX.point} := hCimg ▸ ⟨w, hw, rfl⟩
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hCX _ hw', hgC]

end Proof_lem_km3c_discrepancy_comparison_strict_source

namespace MMP.Mori

open CategoryTheory
open AlgebraicGeometry hiding PrimeDivisor
open scoped WithZero

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open Proof_lem_km3c_discrepancy_comparison_strict_source
open Proof_lem_km3c_discrepancy_comparison

/-- **Strict comparison of discrepancies, curve form.** In the setting of
`MMP.Mori.isDiscrepancy_le_of_isRelativelyNef`, assume moreover that `K_X + Δ` is negative on
every proper curve contracted by `f`, and that `f` is not an isomorphism above the generic point
`f (D.f η_E)` of the center on `Y` of the divisor `E` represented by `D` and `D'`. If
`a = a(E, X, Δ)` and `a' = a(E, X', Δ')`, then `a < a'`. This is the form used for the
contraction of a `(K_X + Δ)`-negative extremal ray, where `f`-ampleness of `-(K_X + Δ)` is not
at hand; `MMP.Mori.isDiscrepancy_lt_of_neg_hasRelativelyAmpleMultiple` follows from it. -/
public theorem isDiscrepancy_lt_of_forall_intersectionNumber_neg {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {n : ℕ} {X X' Y : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [QuasiCompact sX] [QuasiCompact sX']
    (hX : IsNormalVariety k sX) (hX' : IsNormalVariety k sX') (hY : IsNormalVariety k sY)
    {f : X ⟶ Y} {f' : X' ⟶ Y} [IsProper f] [IsProper f']
    (hfs : f ≫ sY = sX) (hfs' : f' ≫ sY = sX')
    (hf : IsBirationalMorphism f) (hf' : IsBirationalMorphism f')
    {KX : Divisor X} {KX' : Divisor X'} (hK : KX.IsCanonicalDivisor sX n)
    (hK' : KX'.IsCanonicalDivisor sX' n) {Δ : QDivisor X} {Δ' : QDivisor X'}
    (hΔ : RationalMap.transformDivisor (X := X) f.toRationalMap Δ =
      RationalMap.transformDivisor (X := X') f'.toRationalMap Δ')
    (hN : QDivisor.IsRelativelyNef sX f (-(Divisor.toQDivisor KX + Δ)))
    (hN' : QDivisor.IsRelativelyNef sX' f' (Divisor.toQDivisor KX' + Δ'))
    (hneg : ∀ C : ProperCurve sX, C.IsContractedBy f →
      ∀ hQ : (Divisor.toQDivisor KX + Δ).IsQCartier,
        (Divisor.toQDivisor KX + Δ).intersectionNumber k sX C.ι C.dim_le hQ < 0)
    (D : DivisorOver k sX) (D' : DivisorOver k sX')
    (hv : haveI : IsIntegral Y := hY.1.toIsIntegral
      haveI : IsDominant f := hf.isDominant
      haveI : IsDominant f' := hf'.isDominant
      D.valuation.comap (functionFieldMap f) = D'.valuation.comap (functionFieldMap f'))
    (hE : RationalMap.IsExceptional (X := D.Y) (D.f ≫ f).toRationalMap D.E)
    (hW : f (D.f D.E.genericPoint) ∉ biregularLocus f)
    {a a' : ℚ} (ha : IsDiscrepancy sX n KX Δ D a) (ha' : IsDiscrepancy sX' n KX' Δ' D' a') :
    a < a' := by
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : IsNormal Y := hY.2
  haveI := hY.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  haveI : IsDominant f := hf.isDominant
  haveI : IsDominant f' := hf'.isDominant
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  obtain ⟨φ, hφ, hφS⟩ := exists_isBirational_compHom_eq hf hf'
  obtain ⟨Z, g, g', hZ, hg, hgp, hg'p, hg', -, hcomm, P, hP⟩ :=
    exists_isNormalVariety_isProper_isBirationalMorphism_primeDivisor_valuation_eq hX hX' f f' φ
      hφ hφS D
  haveI := hgp
  haveI := hg'p
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sX)
  haveI : IsDominant g := hg.isDominant
  haveI : IsDominant g' := hg'.isDominant
  have hZ' : IsNormalVariety k (g' ≫ sX') := by
    rwa [← hfs', ← Category.assoc, ← hcomm, Category.assoc, hfs]
  obtain ⟨⟨ΔZ, hΔZ, -⟩, -⟩ := IsPair.existsUnique_isCrepantBoundary ha.isPair hK g hZ hg
  obtain ⟨⟨ΔZ', hΔZ', -⟩, -⟩ := IsPair.existsUnique_isCrepantBoundary ha'.isPair hK' g' hZ' hg'
  -- `H = ∑_F (a(F, X, Δ) - a(F, X', Δ')) F = -B`
  obtain ⟨hHnef, hHexc⟩ := isRelativelyNef_of_isDiscrepancy_sub hX hX' hY hfs hfs' hf hf' hK hK'
    hΔ hN hN' hZ hg hg' hcomm (ΔZ' - ΔZ) fun F b b' hb hb' => by
      have e1 := (hΔZ F).eq hb
      have e2 := (hΔZ' F).eq hb'
      change ΔZ'.coeff F - ΔZ.coeff F = b - b'
      linarith
  have hhs : (g ≫ f) ≫ sY = g ≫ sX := by rw [Category.assoc, hfs]
  have hhb : IsBirationalMorphism (g ≫ f) := isBirationalMorphism_comp_of_isBirational f g
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hf)
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hg)
  have hBeff := isEffective_neg_of_isRelativelyNef_of_coeff_eq_zero k sY (g ≫ sX) hY hZ (g ≫ f)
    hhs hhb hHnef hHexc
  have hBq : (-(ΔZ' - ΔZ)).IsQCartier := hHnef.1.neg
  have hBnef : (-(-(ΔZ' - ΔZ))).IsRelativelyNef (g ≫ sX) (g ≫ f) := by rwa [neg_neg]
  -- the coefficient at `E` is computed on `Z`, on `X` and on `X'`
  have hv' : D'.valuation = (⟨Z, g', hZ', hg', P⟩ : DivisorOver k sX').valuation := by
    refine valuation_eq_of_comap_eq hf' (hv.symm.trans ?_)
    rw [← hP]
    refine Valuation.ext fun t => ?_
    change P.divisorialValuation (functionFieldMap g (functionFieldMap f t)) =
      P.divisorialValuation (functionFieldMap g' (functionFieldMap f' t))
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_congr hcomm]
  have e1 : a = -ΔZ.coeff P := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq
    ⟨hX, hK, by simpa only [neg_neg] using hN.1.neg⟩ hP.symm ha (hΔZ P)
  have e2 : a' = -ΔZ'.coeff P :=
    MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq ⟨hX', hK', hN'.1⟩ hv' ha' (hΔZ' P)
  have hP0' : (0 : ℚ) ≤ (-(ΔZ' - ΔZ)).coeff P := DivisorWithCoeffs.isEffective_iff_nonneg.mp hBeff P
  by_contra hlt
  have hP0 : (-(ΔZ' - ΔZ)).coeff P = 0 := by
    refine le_antisymm ?_ hP0'
    change -(ΔZ'.coeff P - ΔZ.coeff P) ≤ 0
    linarith
  -- the generic point of `P` is not in `Supp B`
  have hηP : P.genericPoint ∉ (-(ΔZ' - ΔZ)).supp := by
    intro hmem
    obtain ⟨Q, hQ, hPQ⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
    obtain rfl := MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support Q P hPQ
    exact hQ hP0
  -- a closed point `z ∈ P ∖ Supp B` and its image `y` in `Y`
  haveI : JacobsonSpace Z := LocallyOfFiniteType.jacobsonSpace (g ≫ sX)
  obtain ⟨z, ⟨hzP, hzB⟩, hzc⟩ := nonempty_inter_closedPoints
    (show (closure {P.genericPoint} ∩ ((-(ΔZ' - ΔZ)).supp : Set Z)ᶜ).Nonempty from
      ⟨P.genericPoint, subset_closure rfl, hηP⟩)
    (isClosed_closure.isLocallyClosed.inter
      (-(ΔZ' - ΔZ)).supp.isClosed.isOpen_compl.isLocallyClosed)
  have hzc' : IsClosed ({z} : Set Z) := mem_closedPoints_iff.mp hzc
  obtain ⟨y, hzy⟩ : ∃ y, (g ≫ f) z = y := ⟨_, rfl⟩
  obtain ⟨x, hzx⟩ : ∃ x, g z = x := ⟨_, rfl⟩
  have hxy : f x = y := by rw [← hzx, ← Scheme.Hom.comp_apply, hzy]
  have hxc : IsClosed ({x} : Set X) := by
    have := g.isClosedMap _ hzc'
    rwa [Set.image_singleton, hzx] at this
  -- the fibre `h⁻¹(y)` misses `Supp B`, by the negativity lemma over a point
  have hdisj : Disjoint ((g ≫ f).base ⁻¹' {y}) ((-(ΔZ' - ΔZ)).supp : Set Z) :=
    (QDivisor.preimage_singleton_subset_supp_or_disjoint_of_isRelativelyNef_neg k sY (g ≫ sX) hY
      hZ (g ≫ f) hhs hhb hBq hBeff hBnef y).resolve_left fun h => hzB (h hzy)
  -- `y` lies on the center of `E`, so outside the biregular locus of `f`
  have hcen : g P.genericPoint = D.f D.E.genericPoint :=
    MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hX hP
  have hyV : y ∉ biregularLocus f := by
    intro hy
    have hsp : (g ≫ f) P.genericPoint ⤳ y :=
      hzy ▸ (specializes_iff_mem_closure.mpr hzP).map (g ≫ f).continuous
    apply hW
    have := hsp.mem_open (biregularLocus f).isOpen hy
    rwa [Scheme.Hom.comp_apply, hcen] at this
  -- a proper curve `C_X` in `f⁻¹(y)`
  have hyc : IsClosed ({y} : Set Y) := by
    have := f.isClosedMap _ hxc
    rwa [Set.image_singleton, hxy] at this
  obtain ⟨CX, hCXf, hCXy⟩ :=
    exists_properCurve_isContractedBy_of_notMem_biregularLocus hX.1 hY f hfs hf hyc hyV
  -- a proper curve `C ⊆ Z` with `g(C) = C_X`
  obtain ⟨C, hgC, hCh⟩ := exists_properCurve_lift hX g hZ CX hCXf
  have hCy : (g ≫ f) C.point = y := by
    rw [Scheme.Hom.comp_apply, hgC]
    exact hCXy (subset_closure rfl)
  -- `(B · C) < 0` by the projection formula, but `C` misses `Supp B`
  have hstrict := intersectionNumber_sub_pos_of_isCrepantBoundary hX hX' hY hfs hfs' hf hf' hK hK'
    hN hN' hZ hZ' hg hg' hcomm hΔZ hΔZ' hHnef.1 C hCh CX hgC (hneg CX hCXf)
  have hCpt : C.point ∉ (-(ΔZ' - ΔZ)).supp := fun h => Set.disjoint_left.mp hdisj
    (show (g ≫ f) C.point ∈ ({y} : Set Y) from hCy) h
  obtain ⟨-, hiff⟩ := MMP.Fourfold.intersectionNumber_nonneg_and_eq_zero_iff (g ≫ sX) _ hBq hBeff
    C hCpt
  have h0 := hiff.mpr fun w hw hwB => Set.disjoint_left.mp hdisj
    (show (g ≫ f) w ∈ ({y} : Set Y) from
      (hCh w (specializes_iff_mem_closure.mp hw)).trans hCy) hwB
  rw [QDivisor.intersectionNumber_neg k (g ≫ sX) C.ι C.dim_le hHnef.1 hBq] at h0
  linarith

/-- **Strict comparison of discrepancies** (Kollár–Mori 3.38). In the setting of
`MMP.Mori.isDiscrepancy_le_of_isRelativelyNef`, assume moreover that `-(K_X + Δ)` is `f`-ample
and that `f` is not an isomorphism above the generic point `f (D.f η_E)` of the center on `Y` of
the divisor `E` represented by `D` and `D'`. If `a = a(E, X, Δ)` and `a' = a(E, X', Δ')`, then
`a < a'`. -/
@[mmp "lem_km3c_discrepancy_comparison_strict_source"]
public theorem isDiscrepancy_lt_of_neg_hasRelativelyAmpleMultiple {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {n : ℕ} {X X' Y : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [QuasiCompact sX] [QuasiCompact sX']
    (hX : IsNormalVariety k sX) (hX' : IsNormalVariety k sX') (hY : IsNormalVariety k sY)
    {f : X ⟶ Y} {f' : X' ⟶ Y} [IsProper f] [IsProper f']
    (hfs : f ≫ sY = sX) (hfs' : f' ≫ sY = sX')
    (hf : IsBirationalMorphism f) (hf' : IsBirationalMorphism f')
    {KX : Divisor X} {KX' : Divisor X'} (hK : KX.IsCanonicalDivisor sX n)
    (hK' : KX'.IsCanonicalDivisor sX' n) {Δ : QDivisor X} {Δ' : QDivisor X'}
    (hΔ : RationalMap.transformDivisor (X := X) f.toRationalMap Δ =
      RationalMap.transformDivisor (X := X') f'.toRationalMap Δ')
    (hN : QDivisor.IsRelativelyNef sX f (-(Divisor.toQDivisor KX + Δ)))
    (hN' : QDivisor.IsRelativelyNef sX' f' (Divisor.toQDivisor KX' + Δ'))
    (hA : haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
      (-(Divisor.toQDivisor KX + Δ)).HasRelativelyAmpleMultiple f)
    (D : DivisorOver k sX) (D' : DivisorOver k sX')
    (hv : haveI : IsIntegral Y := hY.1.toIsIntegral
      haveI : IsDominant f := hf.isDominant
      haveI : IsDominant f' := hf'.isDominant
      D.valuation.comap (functionFieldMap f) = D'.valuation.comap (functionFieldMap f'))
    (hE : RationalMap.IsExceptional (X := D.Y) (D.f ≫ f).toRationalMap D.E)
    (hW : f (D.f D.E.genericPoint) ∉ biregularLocus f)
    {a a' : ℚ} (ha : IsDiscrepancy sX n KX Δ D a) (ha' : IsDiscrepancy sX' n KX' Δ' D' a') :
    a < a' :=
  isDiscrepancy_lt_of_forall_intersectionNumber_neg hX hX' hY hfs hfs' hf hf' hK hK' hΔ hN hN'
    (fun C hC hQ => by
      haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
      have hpos := QDivisor.HasRelativelyAmpleMultiple.intersectionNumber_pos hA hN.1 C hC
      rw [QDivisor.intersectionNumber_neg k sX C.ι C.dim_le hQ hN.1] at hpos
      linarith) D D' hv hE hW ha ha'

end MMP.Mori

namespace Proof_lem_km3c_discrepancy_comparison_strict_target

open CategoryTheory
open AlgebraicGeometry hiding PrimeDivisor
open MMP.Mori
open Proof_lem_km3c_discrepancy_comparison
open scoped WithZero

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- **`Δ'_Z - Δ_Z` is positive on a curve not contracted by `g'`.** In the setting of
`MMP.Mori.isRelativelyNef_of_isDiscrepancy_sub`, assume moreover that `K_{X'} + Δ'` is positive
on every proper curve contracted by `f'`. Then `((Δ'_Z - Δ_Z) · C) > 0` for every proper curve
`C ⊆ Z` contracted by `g ≫ f` whose image under `g'` is not a point: by the projection formula,
`(g'^*(K_{X'} + Δ') · C) > 0` and `(g^*(K_X + Δ) · C) ≤ 0`. -/
private theorem intersectionNumber_sub_pos_of_isCrepantBoundary {k : Type u} [Field k]
    [PerfectField k] {n : ℕ} {X X' Y Z : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [QuasiCompact sX] [QuasiCompact sX']
    (hX : IsNormalVariety k sX) (hX' : IsNormalVariety k sX') (hY : IsNormalVariety k sY)
    {f : X ⟶ Y} {f' : X' ⟶ Y} [IsProper f] [IsProper f'] (hfs : f ≫ sY = sX)
    (hfs' : f' ≫ sY = sX') (hf : IsBirationalMorphism f) (hf' : IsBirationalMorphism f')
    {KX : Divisor X} {KX' : Divisor X'} (hK : KX.IsCanonicalDivisor sX n)
    (hK' : KX'.IsCanonicalDivisor sX' n) {Δ : QDivisor X} {Δ' : QDivisor X'}
    (hN : QDivisor.IsRelativelyNef sX f (-(Divisor.toQDivisor KX + Δ)))
    (hN' : QDivisor.IsRelativelyNef sX' f' (Divisor.toQDivisor KX' + Δ'))
    (hpos : ∀ C'' : ProperCurve sX', C''.IsContractedBy f' →
      0 < (Divisor.toQDivisor KX' + Δ').intersectionNumber k sX' C''.ι C''.dim_le hN'.1)
    {g : Z ⟶ X} {g' : Z ⟶ X'} [IsProper g] [IsProper g'] (hZ : IsNormalVariety k (g ≫ sX))
    (hZ' : IsNormalVariety k (g' ≫ sX'))
    (hg : IsBirationalMorphism g) (hg' : IsBirationalMorphism g') (hcomm : g ≫ f = g' ≫ f')
    {ΔZ ΔZ' : QDivisor Z} (hΔZ : IsCrepantBoundary sX n KX Δ g hZ hg ΔZ)
    (hΔZ' : IsCrepantBoundary sX' n KX' Δ' g' hZ' hg' ΔZ')
    [QuasiCompact (g ≫ sX)] (hHq : (ΔZ' - ΔZ).IsQCartier) (C : ProperCurve (g ≫ sX))
    (hC : C.IsContractedBy (g ≫ f)) (hnc : ¬ ∃ w : X', Set.range (C.ι ≫ g') = {w}) :
    0 < (ΔZ' - ΔZ).intersectionNumber k (g ≫ sX) C.ι C.dim_le hHq := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType sX' := hX'.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (g ≫ sX) := hZ.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (g' ≫ sX') := hZ'.1.toLocallyOfFiniteType
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace sX'
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (g ≫ sX)
  have : IsDominant g := hg.isDominant
  have : IsDominant g' := hg'.isDominant
  have : AlgebraicGeometry.IsVariety k sX := hX.1
  have : AlgebraicGeometry.IsVariety k sX' := hX'.1
  have : AlgebraicGeometry.IsVariety k (g ≫ sX) := hZ.1
  have hsZ : g' ≫ sX' = g ≫ sX := by
    rw [← hfs', ← Category.assoc, ← hcomm, Category.assoc, hfs]
  have hQ : (Divisor.toQDivisor KX + Δ).IsQCartier := by
    simpa using hN.1.neg
  have hQ' : (Divisor.toQDivisor KX' + Δ').IsQCartier := hN'.1
  obtain ⟨_, _, L, L', hpb, hpb', hB, hA, heq⟩ :=
    exists_intersectionNumber_sub_eq_of_isCrepantBoundary hX hX' hfs hfs' hK hK' hQ hQ' hZ hZ' hg
      hg' hcomm hΔZ hΔZ' hHq C
  rw [heq]
  have h1 : 0 < L'.intersectionNumber k (g ≫ sX) C.ι C.dim_le hA := by
    obtain ⟨d, hd, C'', hC'', heq⟩ := QDivisor.exists_intersectionNumber_pullback_eq_mul g' hsZ f'
      hQ' hpb' hA C (by rw [← hcomm]; exact hC) hnc
    exact heq ▸ mul_pos hd (hpos C'' hC'')
  have h2 : L.intersectionNumber k (g ≫ sX) C.ι C.dim_le hB ≤ 0 := by
    rcases QDivisor.intersectionNumber_pullback_eq_zero_or g rfl f hQ hpb hB C hC with
        h0 | ⟨d, hd, C'', hC'', heq⟩
    · rw [h0]
    · rw [heq]
      have := MMP.Fourfold.QDivisor.IsRelativelyNef.intersectionNumber_nonneg sX hN hN.1 C'' hC''
      rw [QDivisor.intersectionNumber_neg k sX C''.ι C''.dim_le hQ hN.1] at this
      nlinarith
  linarith

end Proof_lem_km3c_discrepancy_comparison_strict_target

namespace MMP.Mori

open CategoryTheory
open AlgebraicGeometry hiding PrimeDivisor
open scoped WithZero

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open Proof_lem_km3c_discrepancy_comparison_strict_target
open Proof_lem_km3c_discrepancy_comparison

/-- **Strict comparison of discrepancies** (Kollár–Mori 3.38(5)). In the setting of
`MMP.Mori.isDiscrepancy_le_of_isRelativelyNef`, assume moreover that `K_{X'} + Δ'` is `f'`-ample
and that the generic point of the center of `E` on `Y` lies outside the biregular locus of `f'`.
If `a = a(D, X, Δ)` and `a' = a(D', X', Δ')`, then `a < a'`. -/
@[mmp "lem_km3c_discrepancy_comparison_strict_target"]
public theorem isDiscrepancy_lt_of_hasRelativelyAmpleMultiple_target {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {n : ℕ} {X X' Y : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [QuasiCompact sX] [QuasiCompact sX']
    (hX : IsNormalVariety k sX) (hX' : IsNormalVariety k sX') (hY : IsNormalVariety k sY)
    {f : X ⟶ Y} {f' : X' ⟶ Y} [IsProper f] [IsProper f']
    (hfs : f ≫ sY = sX) (hfs' : f' ≫ sY = sX')
    (hf : IsBirationalMorphism f) (hf' : IsBirationalMorphism f')
    {KX : Divisor X} {KX' : Divisor X'} (hK : KX.IsCanonicalDivisor sX n)
    (hK' : KX'.IsCanonicalDivisor sX' n) {Δ : QDivisor X} {Δ' : QDivisor X'}
    (hΔ : RationalMap.transformDivisor (X := X) f.toRationalMap Δ =
      RationalMap.transformDivisor (X := X') f'.toRationalMap Δ')
    (hN : QDivisor.IsRelativelyNef sX f (-(Divisor.toQDivisor KX + Δ)))
    (hN' : QDivisor.IsRelativelyNef sX' f' (Divisor.toQDivisor KX' + Δ'))
    (D : DivisorOver k sX) (D' : DivisorOver k sX')
    (hv : haveI : IsIntegral Y := hY.1.toIsIntegral
      haveI : IsDominant f := hf.isDominant
      haveI : IsDominant f' := hf'.isDominant
      D.valuation.comap (functionFieldMap f) = D'.valuation.comap (functionFieldMap f'))
    (hE : RationalMap.IsExceptional (X := D.Y) (D.f ≫ f).toRationalMap D.E)
    (hA' : haveI : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace sX'
      (Divisor.toQDivisor KX' + Δ').HasRelativelyAmpleMultiple f')
    (hW : f' (D'.f D'.E.genericPoint) ∉ biregularLocus f')
    {a a' : ℚ} (ha : IsDiscrepancy sX n KX Δ D a) (ha' : IsDiscrepancy sX' n KX' Δ' D' a') :
    a < a' := by
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : IsNormal Y := hY.2
  haveI := hY.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  haveI : IsDominant f := hf.isDominant
  haveI : IsDominant f' := hf'.isDominant
  haveI : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace sX'
  obtain ⟨φ, hφ, hφS⟩ := exists_isBirational_compHom_eq hf hf'
  obtain ⟨Z, g, g', hZ, hg, hgp, hg'p, hg', -, hcomm, P, hP⟩ :=
    exists_isNormalVariety_isProper_isBirationalMorphism_primeDivisor_valuation_eq hX hX' f f' φ
      hφ hφS D
  haveI := hgp
  haveI := hg'p
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sX)
  haveI : IsDominant g := hg.isDominant
  haveI : IsDominant g' := hg'.isDominant
  haveI : QuasiCompact (g ≫ sX) := hZ.1.toQuasiCompact
  have hsZ : g' ≫ sX' = g ≫ sX := by
    rw [← hfs', ← Category.assoc, ← hcomm, Category.assoc, hfs]
  have hZ' : IsNormalVariety k (g' ≫ sX') := hsZ ▸ hZ
  obtain ⟨⟨ΔZ, hΔZ, -⟩, -⟩ := IsPair.existsUnique_isCrepantBoundary ha.isPair hK g hZ hg
  obtain ⟨⟨ΔZ', hΔZ', -⟩, -⟩ := IsPair.existsUnique_isCrepantBoundary ha'.isPair hK' g' hZ' hg'
  -- `H = ∑_F (a(F, X, Δ) - a(F, X', Δ')) F`
  obtain ⟨hHnef, hHexc⟩ := isRelativelyNef_of_isDiscrepancy_sub hX hX' hY hfs hfs' hf hf' hK hK'
    hΔ hN hN' hZ hg hg' hcomm (ΔZ' - ΔZ) fun F b b' hb hb' => by
      have e1 := (hΔZ F).eq hb
      have e2 := (hΔZ' F).eq hb'
      change ΔZ'.coeff F - ΔZ.coeff F = b - b'
      linarith
  have hh : (g ≫ f) ≫ sY = g ≫ sX := by rw [Category.assoc, hfs]
  have hhb : IsBirationalMorphism (g ≫ f) := isBirationalMorphism_comp_of_isBirational f g
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hf)
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hg)
  -- `B = -H` is effective by the negativity lemma
  have hBeff : (-(ΔZ' - ΔZ)).IsEffective :=
    isEffective_neg_of_isRelativelyNef_of_coeff_eq_zero k sY (g ≫ sX) hY hZ (g ≫ f) hh hhb
      hHnef hHexc
  -- the coefficient at `E` is computed on `Z`, on `X` and on `X'`
  have hv' : D'.valuation = (⟨Z, g', hZ', hg', P⟩ : DivisorOver k sX').valuation := by
    refine valuation_eq_of_comap_eq hf' (hv.symm.trans ?_)
    rw [← hP]
    refine Valuation.ext fun t => ?_
    change P.divisorialValuation (functionFieldMap g (functionFieldMap f t)) =
      P.divisorialValuation (functionFieldMap g' (functionFieldMap f' t))
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_congr hcomm]
  have e1 : a = -ΔZ.coeff P := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq
    ⟨hX, hK, by simpa only [neg_neg] using hN.1.neg⟩ hP.symm ha (hΔZ P)
  have e2 : a' = -ΔZ'.coeff P :=
    MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq ⟨hX', hK', hN'.1⟩ hv' ha' (hΔZ' P)
  rw [e1, e2]
  by_contra hle
  set B := -(ΔZ' - ΔZ) with hBdef
  have hBP : B.coeff P = 0 := by
    have h0 : (0 : ℚ) ≤ B.coeff P := DivisorWithCoeffs.isEffective_iff_nonneg.mp hBeff P
    have h1 : B.coeff P = -(ΔZ'.coeff P - ΔZ.coeff P) := rfl
    linarith
  -- `E ⊄ Supp B`
  have hηP : P.genericPoint ∉ B.supp := by
    rw [DivisorWithCoeffs.mem_supp_iff]
    rintro ⟨F, hF, hPF⟩
    rw [MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support F P hPF] at hF
    exact hF hBP
  -- a closed point `q ∈ E ∖ Supp B` and its image `y`
  have : JacobsonSpace Z := LocallyOfFiniteType.jacobsonSpace (g ≫ sX)
  have hT : IsLocallyClosed (closure {P.genericPoint} ∩ (B.supp : Set Z)ᶜ) :=
    isClosed_closure.isLocallyClosed.inter B.supp.isClosed.isOpen_compl.isLocallyClosed
  obtain ⟨q, ⟨hq2, hqS⟩, hqc⟩ :=
    nonempty_inter_closedPoints (⟨P.genericPoint, subset_closure rfl, hηP⟩ :
      (closure {P.genericPoint} ∩ (B.supp : Set Z)ᶜ).Nonempty) hT
  set y := (g ≫ f) q with hydef
  have hyc : IsClosed ({y} : Set Y) := by
    have h := (g ≫ f).isClosedMap _ (mem_closedPoints_iff.mp hqc)
    rwa [Set.image_singleton] at h
  -- the negativity lemma over `y`: `h⁻¹(y)` is disjoint from `Supp B`
  have hBq : B.IsQCartier := hHnef.1.neg
  have hnefB : (-B).IsRelativelyNef (g ≫ sX) (g ≫ f) := by rwa [hBdef, neg_neg]
  rcases QDivisor.preimage_singleton_subset_supp_or_disjoint_of_isRelativelyNef_neg k sY (g ≫ sX)
    hY hZ (g ≫ f) hh hhb hBq hBeff hnefB y with hsub | hdisj
  · exact hqS (hsub rfl)
  -- `y` lies outside the biregular locus of `f'`
  have hζ : D'.f D'.E.genericPoint = g' P.genericPoint :=
    MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hX' hv'
  have hspec : f' (g' P.genericPoint) ⤳ y := by
    have := (specializes_iff_mem_closure.mpr hq2).map (g' ≫ f').continuous
    rw [hydef, hcomm]
    simpa using this
  have hyV : y ∉ biregularLocus f' := fun hyV =>
    hW (by rw [hζ]; exact hspec.mem_open (biregularLocus f').isOpen hyV)
  -- a curve `C'` in `f'⁻¹(y)` and a curve `C ⊆ h⁻¹(y)` over it
  obtain ⟨C', -, hC'y⟩ :=
    exists_properCurve_isContractedBy_of_notMem_biregularLocus hX'.1 hY f' hfs' hf' hyc hyV
  obtain ⟨C, hCimg⟩ := ProperCurve.exists_image_closure_eq_of_surjective hZ.1 hX'.1 g' hsZ C'
  have hCy : closure {C.point} ⊆ (g ≫ f).base ⁻¹' {y} := by
    intro z hz
    have h1 : g' z ∈ closure {C'.point} := hCimg ▸ ⟨z, hz, rfl⟩
    change (g ≫ f) z = y
    rw [hcomm]
    exact hC'y h1
  have hCcon : C.IsContractedBy (g ≫ f) := isContractedBy_of_closure_subset_preimage hCy
  have hnc : ¬ ∃ w : X', Set.range (C.ι ≫ g') = {w} := by
    rintro ⟨w, hw⟩
    have hr : Set.range C'.ι = {w} := by
      rw [ProperCurve.range_ι, ← hCimg, ← ProperCurve.range_ι, ← hw, Scheme.Hom.comp_base,
        TopCat.coe_comp, Set.range_comp]
    exact not_subsingleton_range_ι C' (hr ▸ Set.subsingleton_singleton)
  -- `(-B · C) > 0` by the projection formula, `(B · C) = 0` as `C ∩ Supp B = ∅`
  have hpos := intersectionNumber_sub_pos_of_isCrepantBoundary hX hX' hY hfs hfs' hf hf' hK hK'
    hN hN' (fun C'' hC'' =>
      QDivisor.HasRelativelyAmpleMultiple.intersectionNumber_pos hA' hN'.1 C'' hC'')
    hZ hZ' hg hg' hcomm hΔZ hΔZ' hHnef.1 C hCcon hnc
  have hCB : C.point ∉ B.supp := fun h =>
    Set.disjoint_left.mp hdisj (hCy (subset_closure rfl)) h
  obtain ⟨-, hiff⟩ := MMP.Fourfold.intersectionNumber_nonneg_and_eq_zero_iff (g ≫ sX) B hBq
    hBeff C hCB
  have h0 := hiff.mpr fun x hx hxS =>
    Set.disjoint_left.mp hdisj (hCy (specializes_iff_mem_closure.mp hx)) hxS
  rw [QDivisor.intersectionNumber_neg k (g ≫ sX) C.ι C.dim_le hHnef.1 hBq] at h0
  linarith

end MMP.Mori

end
