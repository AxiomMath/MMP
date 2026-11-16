module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldBadBranchCount
import MMP.AlgebraicGeometry.MMP.Fourfold.EchoLogDiscrepancy
import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantJunction
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Flip.FiniteGeneration
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBoundaryChange
import MMP.AlgebraicGeometry.Divisor.Negativity.NegativityLemma
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
import MMP.Analysis.Complex.CauchyTransformRungeMontel
import MMP.AlgebraicGeometry.Curves.PluricanonicalSectionsSeparatePoints
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyRestrictOpen
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# Weights do not increase under moves of a prepared chain

Let `(Y, Θ) ⤏ (Y', Θ')` be a move of a prepared chain: a coefficient decrease
`(Y_i, Θ_i) ⇝ (Y_i, Θ_i')` or a small terminal flip `(Y⁻, Θ⁻) ⤏ (Y⁺, Θ⁺)` of a bridge. For every
normalized divisorial valuation `v` exceptional over both `Y` and `Y'`, the weight does not
increase: `w_v(Y', Θ') ≤ w_v(Y, Θ)`.

Log discrepancies do not decrease along a move, `a(v; Y, Θ) ≤ a(v; Y', Θ')`, and the weight
function is nondecreasing in `2 - a`, so `w_v(Y', Θ') ≤ w_v(Y, Θ)`. The monotonicity of log
discrepancies is proved for the two kinds of moves.

* Along a threefold step diagram `X⁻ → Z ← X⁺` with `B⁺` the strict transform of `B⁻`, every
  valuation has `a(ξ; X⁻, B⁻) ≤ a(ξ; X⁺, B⁺)`: on a common model `W` realizing `ξ = ord_E` the
  two discrepancies agree when `E` lies over the common biregular locus, and the comparison is
  strict when it lies over the bad locus (the negativity lemma). This covers the flips of a
  bridge, and the step diagrams of the tail.
* At a coefficient decrease `(Y_i, Θ_i) ⇝ (Y_i, Θ_i')` the boundary decreases: the coefficient
  at `E_{i,s}` changes from `1 - a_i(s)` to `1 - a_{i+1}(s)`, and `a_i(s) ≤ a_{i+1}(s)` by the
  step diagram comparison for the tail. Discrepancies decrease when an effective divisor is
  added to the boundary (Kollár–Mori 2.27).

Moves ending at a junction `Y_{i+1}` are read through the identification `e : V_{m_i} ≅ Y_{i+1}`
of the bridge, along which log discrepancies are transported.

## Main results

* `MMP.Fourfold.StabilizedTail.PreparedChain.le_of_isValuationWeight_of_move`: weights do not
  increase under the three kinds of moves of a prepared chain.

## Implementation notes

A move of a prepared chain is one of three kinds, and the statement is the conjunction of the
three cases:

* the coefficient decrease `(Y_i, Θ_i) ⇝ (Y_i, Θ_i')` from the junction `(i, none)` to the model
  `(i, some 0)` of the `i`-th bridge, when the bridge has at least one flip; both models live on
  `Y_i`, and a valuation of `ℂ(Y_i)` is a valuation of both;
* the coefficient decrease of a bridge without flips, from `(i, none)` to `(i + 1, none)`, where
  a valuation `v` of `ℂ(Y_i)` corresponds to the valuation `v'` of `ℂ(Y_{i+1})` obtained by
  pulling back along the identification `e : Y_i = V_0 ≅ Y_{i+1}` of the bridge;
* a small terminal flip move `μ` (`MMP.Fourfold.StabilizedTail.PreparedChain.FlipMove`) with step
  diagram `Y⁻ → Z ← Y⁺`, where `v'` on `Y⁺` corresponds to `v` on `Y⁻` when their restrictions
  to `ℂ(Z)` agree, as in `MMP.Fourfold.StabilizedTail.PreparedChain.flipBadSet`.

Weights are the predicate `MMP.Fourfold.StabilizedTail.TerminalChain.IsValuationWeight` at the
admissible scale of the prepared chain; it contains that the valuation is a normalized divisorial
valuation exceptional over the model, so "exceptional over both `Y` and `Y'`" is carried by the
two weight hypotheses.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.27, 3.38,
  3.39
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori MMP.Fourfold

universe u

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold.StabilizedTail.PreparedChain

section CommonModel

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]

/-- For birational morphisms `f : X ⟶ Y` and `f' : X' ⟶ Y` to a separated scheme, there is a
birational map `φ : X ⤏ X'` with `φ ≫ f' = f`. -/
private theorem exists_isBirational_compHom_eq {X X' Y : Scheme.{0}} [IsReduced X]
    [IsReduced X'] [IsSeparated (Y ↘ ⊤_ Scheme)] {f : X ⟶ Y} {f' : X' ⟶ Y}
    (hf : IsBirationalMorphism f) (hf' : IsBirationalMorphism f') :
    ∃ φ : MMP.Mori.RationalMap X X', MMP.Mori.RationalMap.IsBirational φ ∧
      φ.compHom f' = f.toRationalMap := by
  obtain ⟨em, hem⟩ := hf
  obtain ⟨ep, hep⟩ := hf'
  have h1 := MMP.Fourfold.PartialIso.isOver_comp_of_toRationalMap_eq em f (𝟙 Y) hem
  have h2 := MMP.Fourfold.PartialIso.isOver_comp_of_toRationalMap_eq ep f' (𝟙 Y) hep
  set e := em.trans ep.symm with he
  have H : e.IsOver (f ≫ 𝟙 Y) (f' ≫ 𝟙 Y) := h1.trans h2.symm
  have H' : e.iso.hom ≫ e.target.ι ≫ f' = e.source.ι ≫ f := by
    simpa only [Scheme.PartialIso.IsOver, Category.comp_id] using H
  refine ⟨e.toRationalMap, MMP.Mori.RationalMap.isBirational_toRationalMap e, ?_⟩
  rw [← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨e.source, e.dense_source, le_rfl, le_top, ?_⟩
  change X.homOfLE (le_rfl : e.source ≤ e.source) ≫ (e.iso.hom ≫ e.target.ι) ≫ f' =
    X.homOfLE (le_top : e.source ≤ ⊤) ≫ X.topIso.hom ≫ f
  rw [Category.assoc, H']
  simp

/-- **A common model realizing `D`.** For a threefold step diagram and a divisor `D` over `X⁻`
there is a normal variety `W` with proper birational morphisms `g : W ⟶ X⁻`, `g' : W ⟶ X⁺`,
`g ≫ f⁻ = g' ≫ f⁺`, and a prime divisor `E` of `W` with `ord_E` the valuation of `D`. -/
private theorem exists_commonModel {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    {sXp : Xp ⟶ Spec (.of ℂ)} {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp) (D : DivisorOver ℂ sXm) :
    ∃ (W : Scheme.{0}) (g : W ⟶ Xm) (g' : W ⟶ Xp) (hW : IsNormalVariety ℂ (g ≫ sXm))
      (hg : IsBirationalMorphism g), IsProper g ∧ IsProper g' ∧ IsBirationalMorphism g' ∧
      g ≫ fm = g' ≫ fp ∧ ∃ E : MMP.Mori.PrimeDivisor W,
        (⟨W, g, hW, hg, E⟩ : DivisorOver ℂ sXm).valuation = D.valuation := by
  have : IsSeparated sZ := h.isProjectiveVariety_target.1.toIsSeparated
  have : IsSeparated (Z ↘ ⊤_ Scheme) := by
    have e : (Z ↘ ⊤_ Scheme) = sZ ≫ Limits.terminal.from (Spec (.of ℂ)) := Subsingleton.elim _ _
    rw [e]
    infer_instance
  obtain ⟨φ, hφ, hφS⟩ := exists_isBirational_compHom_eq h.isBirationalMorphism_minus
    h.isSmallMorphism_plus.isBirationalMorphism
  haveI : IsProper fm := isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus
  haveI : IsProper fp := h.isSmallMorphism_plus.isProper
  obtain ⟨W, g, g', hW, hg, hgp, hg'p, hg', -, hcomm, P, hP⟩ :=
    MMP.Mori.exists_isNormalVariety_isProper_isBirationalMorphism_primeDivisor_valuation_eq
      h.isNormalVariety_minus h.isNormalVariety_plus fm fp φ hφ hφS D
  exact ⟨W, g, g', hW, hg, hgp, hg'p, hg', hcomm, P, hP⟩

end CommonModel

/-! ### Forms and orders over the base -/

section Forms

/-- The coefficient of `g⁻¹_* B` at `P` is that of `B` at `Q` when `g(η_P) = η_Q` lies in the
biregular locus of `g`. -/
private theorem inverseTransformDivisor_apply_of_map_genericPoint {X Y : Scheme.{0}} {R : Type*}
    [AddCommMonoid R] {g : X ⟶ Y} {P : MMP.Mori.PrimeDivisor X} {Q : MMP.Mori.PrimeDivisor Y}
    (hPQ : g P.genericPoint = Q.genericPoint) (hV : g P.genericPoint ∈ biregularLocus g)
    (B : DivisorWithCoeffs R Y) : inverseTransformDivisor g B P = B Q :=
  MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    (MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hPQ hV)
    (fun _ hQ' => AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      ((MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
        hQ').1.symm.trans hPQ)) B

variable {k : Type} [Field k] [PerfectField k]

/-- Along a morphism `f` inducing an isomorphism of function fields, every rational pluri-form
is a pull-back: `τ = f^*σ`, with `σ ≠ 0` when `τ ≠ 0`. -/
private theorem exists_pullbackRationalPluriForms_eq {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] {sY : Y ⟶ Spec (.of k)} [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sY; (Algebra.trdeg k Y.functionField).toNat = d) {m : ℤ}
    (τ : RationalPluriForms (f ≫ sY) d m) :
    ∃ σ : RationalPluriForms sY d m, pullbackRationalPluriForms sY f σ = τ ∧
      (τ ≠ 0 → σ ≠ 0) := by
  let := functionFieldAlgebra sY
  let := functionFieldAlgebra (f ≫ sY)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sY f
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sY f hf hd
  set bY := ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m with hbY
  set bX := ZTensorPower.basis (basisOfSpanSingleton hω.2.1 hω.2.2) m with hbX
  obtain ⟨c, hc⟩ := hf.2 (bX.repr τ ())
  have hpull : pullbackRationalPluriForms sY f (c • bY ()) = τ := by
    change pullbackForms m (c • bY ()) = τ
    rw [pullbackForms_eq hω m]
    apply bX.ext_elem
    intro i
    obtain rfl : i = () := rfl
    rw [repr_pullbackFormsAlong hω m]
    simp only [bY, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
      smul_eq_mul, mul_one]
    exact hc
  refine ⟨c • bY (), hpull, fun hτ hσ => hτ ?_⟩
  rw [← hpull, hσ]
  change pullbackForms m 0 = 0
  rw [pullbackForms_eq hω m]
  simp [pullbackFormsAlong]

/-- **Orders of pulled-back forms along a composite.** For `g : W ⟶ X` and a birational
`f : X ⟶ Y`, the order along `(W, g, F)` over `X` of `f^*σ` is the order along
`(W, g ≫ f, F)` over `Y` of `σ`. -/
private theorem ordPullback_pullbackRationalPluriForms {X Y W : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] {sY : Y ⟶ Spec (.of k)} [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsDominant f]
    [LocallyOfFiniteType (f ≫ sY)] (hf : IsBirationalMorphism f) {d : ℕ}
    (hd : letI := functionFieldAlgebra sY; (Algebra.trdeg k Y.functionField).toNat = d)
    {g : W ⟶ X} (hW : IsNormalVariety k (g ≫ f ≫ sY)) (hg : IsBirationalMorphism g)
    (hgf : IsBirationalMorphism (g ≫ f)) (F : MMP.Mori.PrimeDivisor W) {m : ℤ}
    (σ : RationalPluriForms sY d m) :
    (⟨W, g, hW, hg, F⟩ : DivisorOver k (f ≫ sY)).ordPullback
        (pullbackRationalPluriForms sY f σ) =
      (⟨W, g ≫ f, hW, hgf, F⟩ : DivisorOver k sY).ordPullback σ := by
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : IsDominant g := hg.isDominant
  haveI : IsNormal W := hW.2
  haveI : IsLocallyNoetherian W :=
    haveI := hW.1.toLocallyOfFiniteType
    LocallyOfFiniteType.isLocallyNoetherian (g ≫ f ≫ sY)
  change F.ordForm (pullbackRationalPluriForms (f ≫ sY) g (pullbackRationalPluriForms sY f σ)) =
    F.ordForm (pullbackRationalPluriForms sY (g ≫ f) σ)
  rw [MMP.Flips.pullbackRationalPluriForms_comp f g hf.functionFieldMap_bijective
    hg.functionFieldMap_bijective hd σ]
  rfl

/-- **Comparing two forms along a divisor over `X`.** If `m'·ord_Γ(τ) = m·ord_Γ(τ')` along every
prime divisor `Γ` through `f(η_E)`, then `m'·ord_E(f^*τ) = m·ord_E(f^*τ')`. -/
private theorem mul_ordPullback_eq_of_forall {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    {n : ℕ} (hn : topologicalKrullDim X = n) (D : DivisorOver k sX) {m m' : ℤ}
    {τ : RationalPluriForms sX n m} {τ' : RationalPluriForms sX n m'} (hτ : τ ≠ 0)
    (hτ' : τ' ≠ 0)
    (hord : ∀ Γ : MMP.Mori.PrimeDivisor X, D.f D.E.genericPoint ∈ Γ.support →
      (m' : ℚ) * Γ.ordForm τ = m * Γ.ordForm τ') :
    (m' : ℚ) * D.ordPullback τ = m * D.ordPullback τ' := by
  let := functionFieldAlgebra sX
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isDominant
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨b, N, hN⟩ := D.exists_ordPullback_eq hX hn
  set c := (ZTensorPower.basis b m).repr τ () with hc_def
  set c' := (ZTensorPower.basis b m').repr τ' () with hc'_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hτ
  have hc' : c' ≠ 0 := repr_ne_zero_of_ne_zero b hτ'
  set g : X.functionField := c ^ m' * c' ^ (-m) with hg_def
  have hg : g ≠ 0 := mul_ne_zero (zpow_ne_zero _ hc) (zpow_ne_zero _ hc')
  have hord' : ∀ Γ : MMP.Mori.PrimeDivisor X, D.f D.E.genericPoint ∈ Γ.support →
      X.ord g Γ.genericPoint = 0 := by
    intro Γ hΓ
    obtain ⟨NΓ, hNΓ⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
    have f1 : (Γ.ordForm τ : ℚ) = (X.ord c Γ.genericPoint : ℚ) + m * NΓ := by
      exact_mod_cast hNΓ m τ hτ
    have f2 : (Γ.ordForm τ' : ℚ) = (X.ord c' Γ.genericPoint : ℚ) + m' * NΓ := by
      exact_mod_cast hNΓ m' τ' hτ'
    have e := hord Γ hΓ
    rw [hg_def, Scheme.ord_mul (zpow_ne_zero _ hc) (zpow_ne_zero _ hc'), ord_zpow _ hc,
      ord_zpow _ hc']
    have : ((m' : ℚ) * X.ord c Γ.genericPoint + -(m : ℚ) * X.ord c' Γ.genericPoint) = 0 := by
      linear_combination e - (m' : ℚ) * f1 + (m : ℚ) * f2
    exact_mod_cast this
  obtain ⟨u, hu, hug⟩ := exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero _ hg hord'
  have hY0 : D.Y.ord (functionFieldMap D.f g) D.E.genericPoint = 0 := by
    rw [← hug, functionFieldMap_algebraMap_stalk]
    exact D.E.ord_algebraMap_of_isUnit (hu.map _)
  have hfc : functionFieldMap D.f c ≠ 0 := (map_ne_zero _).mpr hc
  have hfc' : functionFieldMap D.f c' ≠ 0 := (map_ne_zero _).mpr hc'
  rw [hg_def, map_mul, map_zpow₀, map_zpow₀,
    Scheme.ord_mul (zpow_ne_zero _ hfc) (zpow_ne_zero _ hfc'), ord_zpow _ hfc, ord_zpow _ hfc']
    at hY0
  have hY0' : ((m' : ℚ) * D.Y.ord (functionFieldMap D.f c) D.E.genericPoint +
      -(m : ℚ) * D.Y.ord (functionFieldMap D.f c') D.E.genericPoint) = 0 := by
    exact_mod_cast hY0
  have h1 : (D.ordPullback τ : ℚ) =
      (D.Y.ord (functionFieldMap D.f c) D.E.genericPoint : ℚ) + m * N := by
    exact_mod_cast hN m τ hτ
  have h2 : (D.ordPullback τ' : ℚ) =
      (D.Y.ord (functionFieldMap D.f c') D.E.genericPoint : ℚ) + m' * N := by
    exact_mod_cast hN m' τ' hτ'
  linear_combination (m' : ℚ) * h1 - (m : ℚ) * h2 + hY0'

end Forms

/-! ### Intersection numbers along curves -/

section IntersectionNumbers

section Intersection

open MMP.Flips

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- A normalization of a proper curve is not constant. -/
private theorem not_exists_forall_base_eq_of_isCurveNormalization (C : ProperCurve sX)
    {C' : Scheme.{u}} {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) :
    ¬ ∃ y : C.scheme, ∀ x : C', ν.base x = y := by
  rintro ⟨y, hy⟩
  have := hν.isFinite
  have : IsDominant ν := hν.isBirationalMorphism.isDominant
  have huniv : Set.range ν = Set.univ := by
    rw [← ν.isClosedMap.isClosed_range.closure_eq, ν.denseRange.closure_range]
  have : Subsingleton C.scheme := ⟨fun a b => by
    obtain ⟨x, rfl⟩ := huniv.ge (Set.mem_univ a)
    obtain ⟨x', rfl⟩ := huniv.ge (Set.mem_univ b)
    exact (hy x).trans (hy x').symm⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
  rw [C.dim_eq] at h0
  exact absurd h0 (by decide)

/-- A normalization of a proper curve is a curve. -/
private theorem isCurve_comp_of_isCurveNormalization (C : ProperCurve sX) {C' : Scheme.{u}}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1) :
    AlgebraicGeometry.IsCurve k (ν ≫ C.ι ≫ sX) := by
  have := hν.isFinite
  have := hν.isIntegral
  have hp : IsProper (ν ≫ C.ι ≫ sX) := inferInstance
  have : AlgebraicGeometry.IsVariety k (ν ≫ C.ι ≫ sX) :=
    { toIsIntegral := ‹_›, toIsSeparated := hp.toIsSeparated,
      toLocallyOfFiniteType := hp.toLocallyOfFiniteType, toQuasiCompact := inferInstance }
  refine ⟨le_antisymm hdim ?_⟩
  by_contra! h
  refine not_exists_forall_base_eq_of_isCurveNormalization C hν
    ⟨ν.base (genericPoint C'), fun x => ?_⟩
  by_cases hx : x = genericPoint C'
  · rw [hx]
  · exact absurd (one_le_topologicalKrullDim_of_specializes_of_ne
      (genericPoint_specializes x) (Ne.symm hx)) (not_le.mpr h)

/-- A birational morphism of integral schemes has degree one. -/
private theorem degreeOver_eq_one {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z] (f : Y ⟶ Z)
    (hf : IsBirationalMorphism f) [IsDominant f] [LocallyOfFiniteType f] : degreeOver f = 1 := by
  letI := (functionFieldMap f).toAlgebra
  have heq : functionFieldMap f = dominantFunctionFieldMap f :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target f (genericPoint Y) (map_genericPoint_of_isDominant f))).symm
  rw [degreeOver_eq_finrank f heq]
  let e := AlgEquiv.ofBijective (Algebra.ofId Z.functionField Y.functionField)
    (hf.functionFieldMap_bijective)
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]

/-- The degree of an invertible sheaf along a normalization of a proper curve `C` is its degree
along `C`. -/
private theorem degreeOn_normalization (C : ProperCurve sX) {C' : Scheme.{u}}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1)
    [IsProper ((ν ≫ C.ι) ≫ sX)] (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    MMP.Mori.degreeOn k sX (ν ≫ C.ι) hdim M = MMP.Mori.degreeOn k sX C.ι C.dim_le M := by
  have := hν.isFinite
  have := hν.isIntegral
  haveI : IsProper (ν ≫ C.ι ≫ sX) := by rw [← Category.assoc]; infer_instance
  have hc := isCurve_comp_of_isCurveNormalization C hν hdim
  have := C.isCurve
  haveI : IsDominant ν := hν.isBirationalMorphism.isDominant
  have key := curveDegree_pullback_eq_degreeOver_mul k (ν ≫ C.ι ≫ sX) (C.ι ≫ sX) ν rfl
    (not_exists_forall_base_eq_of_isCurveNormalization C hν) ((Scheme.Modules.pullback C.ι).obj M) 1
  rw [degreeOver_eq_one ν hν.isBirationalMorphism, Nat.cast_one, one_mul] at key
  let e : (Scheme.Modules.pullback (ν ≫ C.ι)).obj M ≅
      (Scheme.Modules.pullback ν).obj ((Scheme.Modules.pullback C.ι).obj M) :=
    ((Scheme.Modules.pullbackComp ν C.ι).app M).symm
  rw [MMP.Mori.degreeOn, MMP.Mori.degreeOn,
    invertibleCurveDegree_congr_structure (Category.assoc ν C.ι sX) hdim,
    invertibleCurveDegree_eq_of_iso k _ hdim e,
    invertibleCurveDegree_eq_curveDegree_one, invertibleCurveDegree_eq_curveDegree_one]
  exact key

variable (k sX) [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- `L · C` is the degree of `𝒪_X(L)` along `C`. -/
private theorem isCartierIntersectionNumber_degreeOn (C : ProperCurve sX) (L : Divisor X)
    (hL : L.IsCartier) :
    IsCartierIntersectionNumber k sX C L hL (L.degreeOn k sX C.ι C.dim_le hL) := by
  let p := C.ι ≫ sX
  haveI : AlgebraicGeometry.IsCurve k p := C.isCurve
  have hX := finite_irreducibleComponents_of_locallyOfFiniteType k p
  haveI hvar : AlgebraicGeometry.IsVariety k (normalizationOverField k p ≫ p) :=
    isVariety_normalizationOverField k p
  haveI : IsIntegral (normalizationSchemeOverField k p) := hvar.toIsIntegral
  haveI : IsFinite (normalizationOverField k p) := isFinite_normalizationOverField k p
  have hν : IsCurveNormalization (normalizationOverField k p) :=
    { isIntegral := inferInstance
      isNormal := Scheme.isNormal_normalizationScheme C.scheme hX
      isFinite := inferInstance
      isBirationalMorphism := by
        haveI : Finite (irreducibleComponents (normalizationSchemeOverField k p)) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        haveI : Finite (irreducibleComponents C.scheme) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        obtain ⟨U, V, hUV, hU, hV, hiso⟩ := exists_dense_opens_isIso_resLE_of_isBirational
          (normalizationOverField k p) (Scheme.isBirational_normalization C.scheme hX)
          (Or.inl ⟨inferInstance, inferInstance⟩)
        exact isBirationalMorphism_of_isIso_resLE _ U V hU.nonempty hV.nonempty hUV hiso }
  have hdim := (topologicalKrullDim_normalizationSchemeOverField k p).le.trans C.dim_le
  refine ⟨_, _, hν, hdim, ?_⟩
  haveI : IsProper ((normalizationOverField k p ≫ C.ι) ≫ sX) := by
    rw [Category.assoc]; infer_instance
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hL.isInvertibleModule_divisorialSheaf
  exact (degreeOn_normalization C hν hdim _).symm

end Intersection

section Crepancy

/-- The order of `c ^ m * g⁻¹` along a point, for nonzero rational functions `c` and `g`. -/
private theorem ord_zpow_mul_inv {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] (z : Y)
    {c g : Y.functionField} (hc : c ≠ 0) (hg : g ≠ 0) (m : ℤ) :
    Y.ord (c ^ m * g⁻¹) z = m * Y.ord c z - Y.ord g z := by
  rw [Scheme.ord_mul (zpow_ne_zero _ hc) (inv_ne_zero hg), MMP.Mori.ord_zpow _ hc,
    ← zpow_neg_one, MMP.Mori.ord_zpow _ hg]
  ring

variable {k : Type u} [Field k] [PerfectField k] {X U : Scheme.{u}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral U] [CompactSpace U] [IsLocallyNoetherian U] [IsNormal U]

omit [CompactSpace X] in
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
    rw [hφ Γ hΓ, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord]
    have : Γ.component = Z0 :=
      Subsingleton.elim (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents) _ _
    rw [this]
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
    have h := hb 1 ω hω0
    have e : D.ordPullback ω = (divisorOfForm (pullbackRationalPluriForms sX p ω)).coeff F := by
      rw [coeff_divisorOfForm]
      rfl
    rw [← e, h]
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

omit [CompactSpace X] in
/-- **Crepancy as a pull-back.** If `Δ` is the crepant boundary of `(X, B)` on `U` and
`K = div(ω)`, then `div(p^*ω) + Δ = p^*(K + B)`. -/
private theorem isPullback_divisorOfForm_add {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
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
  have h := coeff_pullback_eq hX hY hp hK' hcrep hm hD hDc
    (Divisor.isPullback_pullback hDc hB') hω0 hωK F
  simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add, zsmul_eq_mul,
    Divisor.coeff_toQDivisor, Int.cast_natCast]
  exact h

end Crepancy

section Curves

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- Intersection numbers of `K + Δ` along a curve depend on `K` only up to linear equivalence. -/
private theorem intersectionNumber_add_eq_of_linearlyEquivalent [CompactSpace X]
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

/-- Two closed subschemes cut out by equal ideal sheaves are isomorphic over `X`. -/
private theorem exists_iso_subscheme_of_eq {I J : X.IdealSheafData} (h : I = J) :
    ∃ e : I.subscheme ≅ J.subscheme, e.hom ≫ J.subschemeι = I.subschemeι := by
  subst h
  exact ⟨Iso.refl _, by simp⟩

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

/-- The negative of a `ℚ`-Cartier `ℚ`-divisor is `ℚ`-Cartier. -/
private theorem isQCartier_neg {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D : QDivisor X} (hD : D.IsQCartier) : (-D).IsQCartier := by
  obtain ⟨m, hm, hC⟩ := hD
  exact ⟨-m, neg_ne_zero.mpr hm, by rwa [neg_smul, smul_neg, neg_neg]⟩

/-- `((-D) · C) = -(D · C)`. -/
private theorem intersectionNumber_neg (k : Type u) [Field k] {X C : Scheme.{u}}
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

/-- **Projection onto the image curve.** Let `L' = u^*L` be the pull-back of a `ℚ`-Cartier
`ℚ`-divisor along a proper morphism `u : V ⟶ W` of normal varieties and `C ⊆ V` a proper curve
whose image `u(C)` is not a point. Then `u(C)` is a proper curve `C''` of `W` with generic point
`u(η_C)`, and `(L' · C) = d (L · C'')` with `d = [k(C) : k(C'')] > 0`. -/
private theorem exists_intersectionNumber_pullback_eq_mul {k : Type u} [Field k]
    {V W : Scheme.{u}} {sV : V ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)}
    [AlgebraicGeometry.IsVariety k sV] [AlgebraicGeometry.IsVariety k sW]
    [IsLocallyNoetherian V] [IsNormal V] [IsLocallyNoetherian W] [IsNormal W]
    (u : V ⟶ W) [IsProper u] (hu : u ≫ sW = sV) {L : QDivisor W} (hL : L.IsQCartier)
    {hLB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L.supp}
    {L' : QDivisor V} (h : L.IsPullback u hLB L') (hL' : L'.IsQCartier) (C : ProperCurve sV)
    (hpt : ¬ ∃ w : W, Set.range (C.ι ≫ u) = {w}) :
    ∃ C'' : ProperCurve sW, C''.point = u C.point ∧ ∃ d : ℚ, 0 < d ∧
      L'.intersectionNumber k sV C.ι C.dim_le hL' =
        d * L.intersectionNumber k sW C''.ι C''.dim_le hL := by
  have := C.isCurve
  set φ := C.ι ≫ u with hφ
  have : AlgebraicGeometry.IsCurve k (φ ≫ sW) := by rw [hφ, Category.assoc, hu]; infer_instance
  have : IsProper (φ ≫ sW) := by rw [hφ, Category.assoc, hu]; infer_instance
  have hcurve := isCurve_imageι_comp sW φ hpt
  have key := intersectionNumber_pullback_eq_degreeOver_mul k sV sW u hu C.ι hL h hcurve
  obtain ⟨e, he⟩ := exists_iso_subscheme_of_eq (C.ker_comp (f := u))
  have : IsProper φ := IsProper.of_comp φ sW
  have : IsProper (φ.imageι ≫ sW) := isProper_imageι_comp φ sW
  have hdim : topologicalKrullDim (curveSubschemeAt (u C.point)) = 1 :=
    (IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph).symm.trans
      hcurve.topologicalKrullDim_eq_one
  have hι : curveSubschemeAtι (u C.point) = e.inv ≫ φ.imageι := by
    rw [Iso.eq_inv_comp]; exact he
  have hprop : IsProper (curveSubschemeAtι (u C.point) ≫ sW) := by
    rw [hι, Category.assoc]; infer_instance
  let C'' : ProperCurve sW := ⟨u C.point, ⟨hdim, hprop⟩⟩
  have hφs : φ.toImage ≫ φ.imageι ≫ sW = C.ι ≫ sV := by
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, hφ, Category.assoc, hu]
  have : LocallyOfFiniteType φ.toImage := by
    have : LocallyOfFiniteType (φ.toImage ≫ φ.imageι ≫ sW) := by
      rw [hφs]; infer_instance
    exact locallyOfFiniteType_of_comp φ.toImage (φ.imageι ≫ sW)
  have hnc : ¬ ∃ y : φ.image, ∀ x : C.scheme, φ.toImage.base x = y := by
    rintro ⟨y, hy⟩
    have hφy : ∀ x, φ x = φ.imageι y := fun x => by
      calc φ x = (φ.toImage ≫ φ.imageι) x := by rw [Scheme.Hom.toImage_imageι]
        _ = φ.imageι y := by rw [Scheme.Hom.comp_apply, hy x]
    obtain ⟨x⟩ : Nonempty C.scheme := inferInstance
    exact hpt ⟨φ.imageι y, Set.eq_singleton_iff_unique_mem.mpr
      ⟨⟨x, hφy x⟩, by rintro _ ⟨x, rfl⟩; exact hφy x⟩⟩
  have hdeg : 0 < degreeOver φ.toImage :=
    degreeOver_pos_of_not_constant k (C.ι ≫ sV) (φ.imageι ≫ sW) φ.toImage hφs hnc
  refine ⟨C'', rfl, (degreeOver φ.toImage : ℚ), by exact_mod_cast hdeg, key.trans ?_⟩
  rw [intersectionNumber_eq_of_iso_comp sW φ.imageι C''.ι _ C''.dim_le e he _ hL]

/-- **Projection of a contracted curve.** With `L' = u^*L` as in
`exists_intersectionNumber_pullback_eq_mul` and `C ⊆ V` a proper curve contracted by `u ≫ f`,
either `(L' · C) = 0` (when `u(C)` is a point), or `(L' · C) = d (L · u(C))` with `d ≥ 0`, where
`u(C)` is a proper curve of `W` contracted by `f`. -/
private theorem intersectionNumber_pullback_eq_zero_or {k : Type u} [Field k]
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
  have := C.isCurve
  by_cases hpt : ∃ w : W, Set.range (C.ι ≫ u) = {w}
  · exact .inl (intersectionNumber_pullback_eq_zero k sV sW u hu C.ι hL h hpt)
  obtain ⟨C'', hC''u, d, hd, heq⟩ :=
    exists_intersectionNumber_pullback_eq_mul u hu hL h hL' C hpt
  refine .inr ⟨d, hd.le, C'', fun x hx => ?_, heq⟩
  have hsub : closure ({u C.point} : Set W) ⊆ u '' closure ({C.point} : Set V) :=
    (u.isClosedMap _ isClosed_closure).closure_subset_iff.mpr (by
      rintro _ rfl; exact ⟨C.point, subset_closure rfl, rfl⟩)
  rw [hC''u] at hx ⊢
  obtain ⟨z, hz, rfl⟩ := hsub hx
  simpa only [Scheme.Hom.comp_apply] using hC z hz

/-- An exceptional prime divisor of a morphism maps its generic point to a point of coheight at
least two. -/
private theorem two_le_coheight_of_isExceptional {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {f : Y ⟶ X} (E : MMP.Mori.PrimeDivisor Y)
    (hE : RationalMap.IsExceptional (X := Y) f.toRationalMap E) :
    2 ≤ Order.coheight (f E.genericPoint) := by
  set η := E.genericPoint
  have hdef : RationalMap.DefinedAt (X := Y) f.toRationalMap η := by
    rw [RationalMap.DefinedAt, RationalMap.dom_toRationalMap_hom]
    trivial
  have h2 := (RationalMap.isExceptional_iff.mp hE) hdef
  have hsub : (TopologicalSpace.IrreducibleCloseds.closureSingleton (f η) : Set X) ⊆
      (RationalMap.transform (X := Y) f.toRationalMap E.idealSheaf.support : Set X) := by
    rw [TopologicalSpace.IrreducibleCloseds.coe_closureSingleton]
    refine (TopologicalSpace.Closeds.isClosed _).closure_subset_iff.mpr ?_
    rintro _ rfl
    refine RationalMap.image_subset_transform f.toPartialMap rfl _ ?_
    rw [MMP.Positivity.image_toPartialMap_hom]
    refine ⟨η, ?_, rfl⟩
    change η ∈ E.support
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have hle := le_closedsCodimension_iff.mp h2 _ hsub
  have hcodim : codimension (TopologicalSpace.IrreducibleCloseds.closureSingleton (f η)) =
      Order.coheight (f η) := by
    have h : TopologicalSpace.IrreducibleCloseds.closureSingleton (f η) =
        irreducibleSetEquivPoints.symm (f η) :=
      TopologicalSpace.IrreducibleCloseds.ext (by
        rw [TopologicalSpace.IrreducibleCloseds.coe_closureSingleton,
          coe_irreducibleEquivPoints_symm_apply])
    rw [codimension_eq_coheight, h]
    exact Order.coheight_orderIso irreducibleSetEquivPoints.symm (f η)
  rwa [hcodim] at hle

end IntersectionNumbers

/-! ### Positivity, negativity and the projection formula -/

section Negativity

/-- A proper birational morphism onto a normal integral scheme is an isomorphism over the generic
point of every prime divisor. -/
private theorem genericPoint_mem_biregularLocus {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) [IsProper f]
    (hf : IsBirationalMorphism f) (P : MMP.Mori.PrimeDivisor Y) :
    P.genericPoint ∈ biregularLocus f := by
  have : IsDominant f := hf.isDominant
  have hbij := hf.functionFieldMap_bijective
  have := P.isDiscreteValuationRing_localRing
  have hsub : (f ⁻¹' {P.genericPoint}).Subsingleton := by
    intro a ha b hb
    have ha' : f a = P.genericPoint := ha
    have hb' : f b = P.genericPoint := hb
    have : ValuationRing (Y.presheaf.stalk (f a)) := by rw [ha']; infer_instance
    have : ValuationRing (Y.presheaf.stalk (f b)) := by rw [hb']; infer_instance
    have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hbij a
    have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hbij b
    exact MMP.Positivity.eq_of_isIso_stalkMap f hbij (hb'.trans ha'.symm)
  obtain ⟨hU, hiso⟩ := (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso f
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hf)).1 inferInstance
  exact le_biregularLocus (V := ⟨_, hU⟩) hiso hsub.finite

/-- A prime divisor exceptional over `X` is exceptional in the sense of the dimension of its
centre: `dim c_X(E) + 2 ≤ dim X`. -/
private theorem isExceptionalPrimeDivisor_of_isExceptional {k : Type u} [Field k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    {f : Y ⟶ X} (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) [hp : IsProper f]
    (E : MMP.Mori.PrimeDivisor Y)
    (hE : MMP.Mori.RationalMap.IsExceptional (X := Y) f.toRationalMap E) :
    MMP.Flips.IsExceptionalPrimeDivisor sX f E := by
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  refine ⟨hY, hf, hp, ?_⟩
  have h2 := two_le_coheight_of_isExceptional E hE
  unfold MMP.Flips.ProperDivisorOver.IsExceptional
  rw [MMP.Flips.ProperDivisorOver.center_eq_toDivisorOver_center,
    DivisorOver.center_eq_closure_genericPoint]
  rw [← MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX (f E.genericPoint)]
  gcongr
  have h2' : ((2 : ℕ∞) : WithBot ℕ∞) ≤ (Order.coheight (f E.genericPoint) : WithBot ℕ∞) :=
    WithBot.coe_le_coe.mpr h2
  exact le_of_eq_of_le (by norm_cast) h2'

/-- A `ℚ`-divisor with a relatively ample multiple is positive on every contracted curve. -/
private theorem intersectionNumber_pos_of_hasRelativelyAmpleMultiple {k : Type u} [Field k]
    {X Y : Scheme.{u}} [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {f : X ⟶ Y} {D : QDivisor X}
    (hA : D.HasRelativelyAmpleMultiple f) (hD : D.IsQCartier) (C : ProperCurve sX)
    (hC : C.IsContractedBy f) : 0 < D.intersectionNumber k sX C.ι C.dim_le hD := by
  obtain ⟨m, hm, L, hL, hLD, hamp⟩ := hA
  rw [QDivisor.intersectionNumber_eq_of_smul k sX C.ι C.dim_le D hD hm L hL hLD]
  have := hL.isInvertibleModule_divisorialSheaf
  have h : 0 < L.degreeOn k sX C.ι C.dim_le hL :=
    MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy f
      L.divisorialSheaf hamp C hC
  have h' : (0 : ℚ) < L.degreeOn k sX C.ι C.dim_le hL := by exact_mod_cast h
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  positivity

/-- **The negativity lemma for `ℚ`-Cartier divisors.** Let `f : Y ⟶ X` be a proper birational
morphism of normal varieties and `B` a `ℚ`-Cartier divisor on `Y` with `(B · C) ≤ 0` on every
curve contracted by `f`, whose coefficients along the prime divisors not exceptional over `X` are
nonnegative. Then `B` is effective. -/
private theorem nonneg_of_intersectionNumber_nonpos {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} [QuasiCompact sY] [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] (hX : IsNormalVariety k sX)
    (hY : IsNormalVariety k sY) (f : Y ⟶ X) (hf : f ≫ sX = sY) [IsProper f]
    (hfb : IsBirationalMorphism f) {B : QDivisor Y} (hB : B.IsQCartier)
    (hnef : ∀ C : ProperCurve sY, C.IsContractedBy f →
      B.intersectionNumber k sY C.ι C.dim_le hB ≤ 0)
    (hBG : ∀ P : MMP.Mori.PrimeDivisor Y, ¬ MMP.Flips.IsExceptionalPrimeDivisor sX f P →
      0 ≤ B.coeff P) :
    0 ≤ B := by
  obtain ⟨E, hEB, hEc⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hB
  have hm : 0 < B.cartierIndex hB := QDivisor.cartierIndex_pos hB
  set m := B.cartierIndex hB with hm_def
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  set BR := QDivisor.toRDivisor B with hBR
  have hBRE : BR = ((1 : ℝ) / m) • Divisor.toRDivisor E := by
    ext P
    have h1 := congrArg (fun D : QDivisor Y => D.coeff P) hEB
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul,
      Int.cast_natCast] at h1
    change (QDivisor.toRDivisor B).coeff P = (((1 : ℝ) / m) • Divisor.toRDivisor E).coeff P
    rw [DivisorWithCoeffs.coeff_smul, QDivisor.coeff_toRDivisor, Divisor.coeff_toRDivisor,
      smul_eq_mul]
    have h2 : ((E.coeff P : ℚ) : ℝ) = ((m * B.coeff P : ℚ) : ℝ) := by rw [h1]
    push_cast at h2
    rw [h2]
    field_simp
  have hL0 : MMP.Flips.IsCartierCombination (0 : RDivisor X) :=
    ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩
  have hpb0 : MMP.Flips.IsRCartierPullback f (0 : RDivisor X) 0 :=
    ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp, fun j => j.elim0, by simp⟩
  have hBRc : MMP.Flips.IsCartierCombination BR :=
    ⟨1, fun _ => 1 / (m : ℝ), fun _ => E, fun _ => hEc, by
      rw [Fin.sum_univ_one, ← MMP.Flips.toRDivisor_eq_mapCoeffs]
      exact hBRE⟩
  have hMc : MMP.Flips.IsCartierCombination (-BR) :=
    ⟨1, fun _ => -(1 / (m : ℝ)), fun _ => E, fun _ => hEc, by
      rw [Fin.sum_univ_one, ← MMP.Flips.toRDivisor_eq_mapCoeffs, hBRE, neg_smul]⟩
  have hpres : -BR = ∑ j : Fin 1, (fun _ => -(1 / (m : ℝ))) j •
      Divisor.toRDivisor ((fun _ => E) j) := by
    rw [Fin.sum_univ_one, hBRE, neg_smul]
  have hMnef : MMP.Flips.IsRelativelyNef k sY f (-BR) := by
    refine ⟨1, fun _ => -(1 / (m : ℝ)), fun _ => E, fun _ => hEc, hpres, fun C hC x hx => ?_⟩
    have hx₀ : MMP.Flips.IsRIntersectionNumber k sY (-BR) (fun _ => -(1 / (m : ℝ)))
        (fun _ => E) C (∑ j : Fin 1, (fun _ => -(1 / (m : ℝ))) j *
          ((E.degreeOn k sY C.ι C.dim_le hEc : ℤ) : ℝ)) :=
      ⟨fun _ => hEc, fun _ => E.degreeOn k sY C.ι C.dim_le hEc, hpres,
        fun _ => isCartierIntersectionNumber_degreeOn k sY C E hEc, rfl⟩
    rw [(MMP.Flips.IsRIntersectionNumber.eq_and_linear k sY C).1 _ _ _ _ _ _ _ hx hx₀,
      Fin.sum_univ_one]
    have hI := hnef C hC
    rw [QDivisor.intersectionNumber_eq_of_smul k sY C.ι C.dim_le B hB hm E hEc hEB] at hI
    have hmq : (0 : ℚ) < m := by exact_mod_cast hm
    have hdeg : (E.degreeOn k sY C.ι C.dim_le hEc : ℚ) ≤ 0 := by
      have := mul_nonpos_of_nonneg_of_nonpos hmq.le hI
      rwa [mul_div_cancel₀ _ hmq.ne'] at this
    have hdeg' : ((E.degreeOn k sY C.ι C.dim_le hEc : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hdeg
    have hmr : (0 : ℝ) < m := by exact_mod_cast hm
    have : 0 ≤ -(1 / (m : ℝ)) * ((E.degreeOn k sY C.ι C.dim_le hEc : ℤ) : ℝ) := by
      rw [neg_mul]
      exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (by positivity) hdeg')
    exact this
  have hBG' : ∀ P : MMP.Mori.PrimeDivisor Y, ¬ MMP.Flips.IsExceptionalPrimeDivisor sX f P →
      0 ≤ BR.coeff P := fun P hP => by
    rw [hBR, QDivisor.coeff_toRDivisor]
    exact_mod_cast hBG P hP
  have hnum : MMP.Flips.IsNumericallyEquivalentOver k sY f (0 : RDivisor Y) (-BR + BR) := by
    refine ⟨⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩, by
      rw [neg_add_cancel]; exact ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩,
      fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ => ?_⟩
    rw [neg_add_cancel] at h₂
    exact (MMP.Flips.IsRIntersectionNumber.eq_and_linear k sY C).1 _ _ _ _ _ _ _ h₁ h₂
  have heff := MMP.Flips.isEffective_of_isNumericallyEquivalentOver_pullback k sX sY hX hY f hf
    hfb hL0 hpb0 hMc hMnef hBRc hBG' hnum
  refine Finsupp.le_def.mpr fun P => ?_
  have hP := heff P
  rw [hBR, QDivisor.coeff_toRDivisor] at hP
  change (0 : ℚ) ≤ B.coeff P
  exact_mod_cast hP

end Negativity

/-! ### The difference of the crepant boundaries -/

section CrepantDifference

variable {k : Type u} [Field k] [PerfectField k]

/-- **Projection of a curve onto a curve.** If `u` maps the proper curve `C` onto the proper curve
`C''`, then `(u^*L · C) = d (L · C'')` with `d = [k(C) : k(C'')] > 0`. -/
private theorem intersectionNumber_pullback_eq_mul_of_image
    {V W : Scheme.{u}} {sV : V ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)}
    [AlgebraicGeometry.IsVariety k sV] [AlgebraicGeometry.IsVariety k sW]
    [IsLocallyNoetherian V] [IsNormal V] [IsLocallyNoetherian W] [IsNormal W]
    (u : V ⟶ W) [IsProper u] (hu : u ≫ sW = sV) {L : QDivisor W}
    (hL : L.IsQCartier)
    {hLB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L.supp}
    {L' : QDivisor V} (h : L.IsPullback u hLB L') (hL' : L'.IsQCartier) (C : ProperCurve sV)
    (C'' : ProperCurve sW) (hCC : u '' closure {C.point} = closure {C''.point}) :
    ∃ d : ℚ, 0 < d ∧ L'.intersectionNumber k sV C.ι C.dim_le hL' =
      d * L.intersectionNumber k sW C''.ι C''.dim_le hL := by
  have hcl : closure {u C.point} = closure {C''.point} := by
    rw [← hCC, ← Set.image_singleton, u.isClosedMap.closure_image_eq_of_continuous u.continuous]
  have hpt' : u C.point = C''.point :=
    ((specializes_iff_closure_subset.mpr hcl.ge).antisymm
      (specializes_iff_closure_subset.mpr hcl.le)).eq
  have hpt : ¬ ∃ w : W, Set.range (C.ι ≫ u) = {w} := by
    rintro ⟨w, hw⟩
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, C.range_ι, hCC] at hw
    have hr := C''.range_ι
    rw [hw] at hr
    have : Subsingleton C''.scheme := ⟨fun a b => C''.ι.isEmbedding.injective (by
      have ha : C''.ι a ∈ ({w} : Set W) := hr ▸ ⟨a, rfl⟩
      have hb : C''.ι b ∈ ({w} : Set W) := hr ▸ ⟨b, rfl⟩
      exact ha.trans hb.symm)⟩
    have h0 := topologicalKrullDim_zero_of_discreteTopology C''.scheme
    rw [C''.dim_eq] at h0
    exact absurd h0 (by decide)
  obtain ⟨C₁, hC₁, hd⟩ := exists_intersectionNumber_pullback_eq_mul u hu hL h hL' C hpt
  obtain rfl : C₁ = C'' := ProperCurve.ext (hC₁.trans hpt')
  exact hd

/-- **The difference of two crepant boundaries along curves.** With `K_Z = div(g^*ω)`, crepancy
`K_Z + Δ_Z = g^*(K_X + Δ)` and `K'_Z + Δ'_Z = g'^*(K_{X'} + Δ')` with `K'_Z ∼ K_Z` give
`((Δ_Z - Δ'_Z) · C) = (g^*(K_X + Δ) · C) - (g'^*(K_{X'} + Δ') · C)` for every curve `C`. -/
private theorem exists_intersectionNumber_sub_eq {n : ℕ} {X X' Z : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    [QuasiCompact sX] [QuasiCompact sX']
    (hX : IsNormalVariety k sX) (hX' : IsNormalVariety k sX')
    {KX : Divisor X} {KX' : Divisor X'} (hK : KX.IsCanonicalDivisor sX n)
    (hK' : KX'.IsCanonicalDivisor sX' n) {Δ : QDivisor X} {Δ' : QDivisor X'}
    (hQ : (Divisor.toQDivisor KX + Δ).IsQCartier)
    (hQ' : (Divisor.toQDivisor KX' + Δ').IsQCartier)
    {g : Z ⟶ X} {g' : Z ⟶ X'} [IsProper g] [IsProper g'] (hZ : IsNormalVariety k (g ≫ sX))
    (hZ' : IsNormalVariety k (g' ≫ sX'))
    (hg : IsBirationalMorphism g) (hg' : IsBirationalMorphism g') (hsZ : g' ≫ sX' = g ≫ sX)
    {ΔZ ΔZ' : QDivisor Z} (hΔZ : IsCrepantBoundary sX n KX Δ g hZ hg ΔZ)
    (hΔZ' : IsCrepantBoundary sX' n KX' Δ' g' hZ' hg' ΔZ') :
    haveI : QuasiCompact (g ≫ sX) := hZ.1.toQuasiCompact
    ∃ (hH : (ΔZ - ΔZ').IsQCartier) (L L' : QDivisor Z)
      (hLB : ∀ W : irreducibleComponents Z, g (componentGenericPoint Z W) ∉
        (Divisor.toQDivisor KX + Δ).supp)
      (hLB' : ∀ W : irreducibleComponents Z, g' (componentGenericPoint Z W) ∉
        (Divisor.toQDivisor KX' + Δ').supp)
      (_ : (Divisor.toQDivisor KX + Δ).IsPullback g hLB L)
      (_ : (Divisor.toQDivisor KX' + Δ').IsPullback g' hLB' L')
      (hLq : L.IsQCartier) (hLq' : L'.IsQCartier),
      ∀ C : ProperCurve (g ≫ sX), (ΔZ - ΔZ').intersectionNumber k (g ≫ sX) C.ι C.dim_le hH =
        L.intersectionNumber k (g ≫ sX) C.ι C.dim_le hLq -
          L'.intersectionNumber k (g ≫ sX) C.ι C.dim_le hLq' := by
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
  have : MMP.Mori.IsVariety k sX := hX.1
  have : MMP.Mori.IsVariety k (g ≫ sX) := hZ.1
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
  set KZ := divisorOfForm (pullbackRationalPluriForms sX g ω) with hKZ
  set KZ' := divisorOfForm (pullbackRationalPluriForms sX' g' ω') with hKZ'
  have hpb := isPullback_divisorOfForm_add hX hZ hg hK hΔZ hω0 hωK hLB
  have hpb' := isPullback_divisorOfForm_add hX' hZ' hg' hK' hΔZ' hω0' hωK' hLB'
  have hB := hpb.isQCartier hQ
  have hA := hpb'.isQCartier hQ'
  have hne : pullbackRationalPluriForms sX g ω ≠ 0 :=
    pullbackRationalPluriForms_ne_zero hX hg hK.1 hω0
  have hlin : KZ'.LinearlyEquivalent KZ := by
    have key : ∀ (s : Z ⟶ Spec (.of k)) (_ : s = g ≫ sX) [LocallyOfFiniteType s]
        (τ : RationalPluriForms s n 1), τ ≠ 0 → (divisorOfForm τ).LinearlyEquivalent KZ := by
      rintro s rfl _ τ hτ
      exact linearlyEquivalent_divisorOfForm hZ hnZ hτ hne
    exact key _ hsZ _ (pullbackRationalPluriForms_ne_zero hX' hg' hK'.1 hω0')
  have hA2 : (Divisor.toQDivisor KZ + ΔZ').IsQCartier := hA.add_of_linearlyEquivalent hlin
  have hBn : (-(Divisor.toQDivisor KZ + ΔZ')).IsQCartier := isQCartier_neg hA2
  have hH : ΔZ - ΔZ' = (Divisor.toQDivisor KZ + ΔZ) + -(Divisor.toQDivisor KZ + ΔZ') := by abel
  have hHq : (ΔZ - ΔZ').IsQCartier := hH ▸ hB.add hBn
  refine ⟨hHq, _, _, hLB, hLB', hpb, hpb', hB, hA, fun C => ?_⟩
  rw [MMP.Fourfold.intersectionNumber_congr _ C.ι C.dim_le hHq (hB.add hBn) hH,
    QDivisor.intersectionNumber_add' k _ C.ι C.dim_le _ _ hB hBn,
    intersectionNumber_neg k _ C.ι C.dim_le hA2 hBn,
    ← intersectionNumber_add_eq_of_linearlyEquivalent (g ≫ sX) C.ι C.dim_le hlin ΔZ' hA hA2]
  ring

end CrepantDifference

/-! ### The comparison of discrepancies -/

section Comparison

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]

/-- **Off the bad locus the discrepancies agree.** If `h(η_E) ∉ Σ`, then
`a(E, X⁻, B⁻) = a(E, X⁺, B⁺)`. -/
private theorem eq_of_notMem_badLocusBase {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    {sXp : Xp ⟶ Spec (.of ℂ)} {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp) {W : Scheme.{0}} {g : W ⟶ Xm}
    {g' : W ⟶ Xp} (hW : IsNormalVariety ℂ (g ≫ sXm)) (hW' : IsNormalVariety ℂ (g' ≫ sXp))
    (hg : IsBirationalMorphism g) (hg' : IsBirationalMorphism g') [IsProper g] [IsProper g']
    (hcomm : g ≫ fm = g' ≫ fp) (E : MMP.Mori.PrimeDivisor W)
    (hE : fm (g E.genericPoint) ∉ badLocusBase fm fp) {n : ℕ} {K' : Divisor Xp}
    (hK : K.IsCanonicalDivisor sXm n) (hK' : K'.IsCanonicalDivisor sXp n) {c c' : ℚ}
    (hc : IsDiscrepancy sXm n K B ⟨W, g, hW, hg, E⟩ c)
    (hc' : IsDiscrepancy sXp n K' (flipTransform fm fp B) ⟨W, g', hW', hg', E⟩ c') :
    c = c' := by
  have hZ := h.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have hfmb := h.isBirationalMorphism_minus
  have hfpb := h.isSmallMorphism_plus.isBirationalMorphism
  haveI := hfmb.isDominant
  haveI := hfpb.isDominant
  haveI : IsProper fm := isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus
  haveI : IsProper fp := h.isSmallMorphism_plus.isProper
  have hXm := h.isNormalVariety_minus
  have hXp := h.isNormalVariety_plus
  obtain rfl := h.comp_eq_minus
  obtain rfl := h.comp_eq_plus
  haveI : LocallyOfFiniteType (fm ≫ sZ) := hXm.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (fp ≫ sZ) := hXp.1.toLocallyOfFiniteType
  -- the image of `η_E` lies in the common biregular locus
  set z := fm (g E.genericPoint) with hz
  have hzU : z ∈ commonBiregularLocus fm fp := by
    by_contra hzU
    exact hE (by rw [← SetLike.mem_coe, coe_badLocusBase]; exact hzU)
  have hzm : z ∈ biregularLocus fm := (inf_le_left : commonBiregularLocus fm fp ≤ _) hzU
  have hzp : z ∈ biregularLocus fp := (inf_le_right : commonBiregularLocus fm fp ≤ _) hzU
  have hz' : fp (g' E.genericPoint) = z := by
    rw [hz, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hcomm]
  -- dimensions
  haveI : MMP.Mori.IsVariety ℂ sZ := hZ.1
  haveI : MMP.Mori.IsVariety ℂ (fm ≫ sZ) := hXm.1
  have hnZ : topologicalKrullDim Z = n := by
    rw [← hK.topologicalKrullDim_eq]
    exact MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (k := ℂ) sZ (fm ≫ sZ)
      hfmb
  have hdZ := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sZ) hnZ
  -- the generators, as pull-backs of forms on `Z`
  obtain ⟨-, -, m, hm, -, U₁, hU₁, τ, hτ, hτa⟩ := hc
  obtain ⟨-, -, m', hm', -, U₂, hU₂, τ', hτ', hτa'⟩ := hc'
  obtain ⟨σ, rfl, hσ⟩ := exists_pullbackRationalPluriForms_eq fm hfmb.functionFieldMap_bijective
    hdZ τ
  obtain ⟨σ', rfl, hσ'⟩ := exists_pullbackRationalPluriForms_eq fp hfpb.functionFieldMap_bijective
    hdZ τ'
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : IsNormal W := hW.2
  haveI : IsLocallyNoetherian W :=
    haveI := hW.1.toLocallyOfFiniteType
    LocallyOfFiniteType.isLocallyNoetherian (g ≫ fm ≫ sZ)
  haveI := hg.isDominant
  haveI := hg'.isDominant
  have hgf : IsBirationalMorphism (g ≫ fm) :=
    MMP.Mori.isBirationalMorphism_comp_of_isBirational fm g
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hfmb)
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hg)
  have hgf' : IsBirationalMorphism (g' ≫ fp) :=
    MMP.Mori.isBirationalMorphism_comp_of_isBirational fp g'
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hfpb)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hg')
  set DZ : DivisorOver ℂ sZ := ⟨W, g ≫ fm, hW, hgf, E⟩ with hDZ
  set DZ' : DivisorOver ℂ sZ := ⟨W, g' ≫ fp, hW', hgf', E⟩ with hDZ'
  have e1 := ordPullback_pullbackRationalPluriForms fm hfmb hdZ hW hg hgf E σ
  have e2 := ordPullback_pullbackRationalPluriForms fp hfpb hdZ hW' hg' hgf' E σ'
  haveI := hgf.isDominant
  haveI := hgf'.isDominant
  have hv : DZ'.valuation = DZ.valuation := by
    change E.valuationOver (g' ≫ fp) = E.valuationOver (g ≫ fm)
    simp only [hcomm]
  have e3 := MMP.Threefold.Mori.ModelIndependence.ordPullback_eq_of_valuation_eq hZ hnZ hv σ'
  -- the comparison along the prime divisors of `Z` through `z`
  have key := mul_ordPullback_eq_of_forall hZ hnZ DZ (hσ hτ.1) (hσ' hτ'.1) (m := (m : ℤ))
    (m' := (m' : ℤ)) fun Γ hΓ => by
    have hΓz : z ∈ Γ.support := hΓ
    have hηz : Γ.genericPoint ⤳ z := by
      rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact hΓz
    obtain ⟨Γm, hΓm, hisom, htrm⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hZ hXm hfmb Γ
    obtain ⟨Γp, hΓp, hisop, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hZ hXp hfpb Γ
    haveI := hisom
    haveI := hisop
    have o1 := MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso fm
      hfmb.functionFieldMap_bijective hdZ Γm Γ hΓm σ
    have o2 := MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso fp
      hfpb.functionFieldMap_bijective hdZ Γp Γ hΓp σ'
    have hm1 : g E.genericPoint ∈ Γm.support := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure]
      refine MMP.Threefold.Resolution.specializes_of_mem_biregularLocus fm
        (hΓm ▸ hηz.mem_open (biregularLocus fm).2 hzm)
        hzm ?_
      rw [hΓm]
      exact hηz
    have hp1 : g' E.genericPoint ∈ Γp.support := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure]
      refine MMP.Threefold.Resolution.specializes_of_mem_biregularLocus fp
        (hΓp ▸ hηz.mem_open (biregularLocus fp).2 hzp)
        (hz' ▸ hzp) ?_
      rw [hΓp, hz']
      exact hηz
    have g1 := hτ.2 Γm ⟨_, hm1, hU₁⟩
    have g2 := hτ'.2 Γp ⟨_, hp1, hU₂⟩
    have hcoeff : (flipTransform fm fp B).coeff Γp = B.coeff Γm := by
      change inverseTransformDivisor fp (RationalMap.transformDivisor (X := Xm) fm.toRationalMap B)
        Γp = B Γm
      rw [inverseTransformDivisor_apply_of_map_genericPoint hΓp
        (hΓp ▸ hηz.mem_open (biregularLocus fp).2 hzp)]
      exact htrm B
    rw [o1] at g1
    rw [o2, hcoeff] at g2
    linear_combination (m' : ℚ) * g1 - (m : ℚ) * g2
  rw [← e1] at key
  rw [← e3, ← e2] at key
  have hm0 : (m : ℚ) * m' ≠ 0 := by positivity
  have : (m : ℚ) * m' * (c - c') = 0 := by
    have k' : ((m' : ℤ) : ℚ) * ((m : ℚ) * c) = ((m : ℤ) : ℚ) * ((m' : ℚ) * c') := by
      rw [hτa, hτa']; exact key
    push_cast at k'
    linear_combination k'
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hm0)

/-- **A contracted curve in a positive-dimensional fibre.** Let `f : X ⟶ Z` be a proper
birational morphism of varieties with `f_* 𝒪_X = 𝒪_Z` that is not an isomorphism over `y`. Then,
given a closed point `x` over `y`, the fibre over `y` contains a proper curve of `X` contracted by
`f`. -/
private theorem exists_properCurve_isContractedBy_subset_fibre {Z X : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of ℂ)} (hZ : IsNormalVariety ℂ sZ) {sX : X ⟶ Spec (.of ℂ)} [IsProper sX]
    [IsLocallyNoetherian X] (f : X ⟶ Z) (hfs : f ≫ sZ = sX) [IsProper f]
    (hXv : AlgebraicGeometry.IsVariety ℂ sX) (hfb : IsBirationalMorphism f)
    (hO : ∀ U : Z.Opens, IsIso (f.app U)) {x : X} (hx : IsClosed ({x} : Set X)) {y : Z}
    (hfx : f x = y) (hyb : y ∉ biregularLocus f) :
    ∃ C : ProperCurve sX, C.IsContractedBy f ∧ closure {C.point} ⊆ f ⁻¹' {y} := by
  obtain ⟨C₀, hC₀c, hC₀i, hC₀d, hxC₀, y', hy'⟩ :=
    MMP.Mori.exists_isIrreducible_curve_image_eq_singleton_of_mem_exceptionalSet hXv hZ.1 f hfs
      hfb hO hx (mem_exceptionalSet.mpr (hfx ▸ hyb))
  have hy'y : y' = y := by
    have : f x ∈ f '' C₀ := ⟨x, hxC₀, rfl⟩
    rw [hy'] at this
    exact this.symm.trans hfx
  obtain ⟨η₀, hη₀⟩ := QuasiSober.sober hC₀i hC₀c
  have hη₀x : η₀ ⤳ x := hη₀.specializes hxC₀
  have hη₀ne : η₀ ∉ ({x} : Set X) := by
    intro hη
    have hC : C₀ = {x} := by
      rw [← hη₀.def, Set.mem_singleton_iff.mp hη, hx.closure_eq]
    rw [hC] at hC₀d
    have h0 := topologicalKrullDim_zero_of_discreteTopology ({x} : Set X)
    rw [hC₀d] at h0
    exact absurd h0 (by decide)
  obtain ⟨y₁, hη₀y₁, -, -, hy₁⟩ :=
    MMP.Fourfold.exists_isProperCurve_of_specializes sX hη₀x hx hx rfl hη₀ne
  have hcl₁ : closure {y₁} ⊆ C₀ := by
    refine closure_minimal (Set.singleton_subset_iff.mpr ?_) hC₀c
    rw [← hη₀.def]
    exact specializes_iff_mem_closure.mp hη₀y₁
  have hfib₁ : closure {y₁} ⊆ f ⁻¹' {y} := fun x' hx' => by
    have : f x' ∈ f '' C₀ := ⟨x', hcl₁ hx', rfl⟩
    rw [hy', hy'y] at this
    exact this
  refine ⟨⟨y₁, hy₁⟩, fun x' hx' => ?_, hfib₁⟩
  exact (hfib₁ hx').trans (hfib₁ (subset_closure rfl)).symm

/-- **Lifting a contracted curve to a model.** With `f` as in
`exists_properCurve_isContractedBy_subset_fibre` and `u : W ⟶ X` proper and surjective, every
closed point `e` of `W` over `y` gives a proper curve `C` of `W` contracted by `u ≫ f` inside the
fibre over `y`, whose image `u(C)` is a proper curve of `X` contracted by `f`. -/
private theorem exists_properCurve_lift_subset_fibre {Z X W : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of ℂ)} (hZ : IsNormalVariety ℂ sZ) {sX : X ⟶ Spec (.of ℂ)} [IsProper sX]
    [IsLocallyNoetherian X] (f : X ⟶ Z) (hfs : f ≫ sZ = sX) [IsProper f]
    (hXv : AlgebraicGeometry.IsVariety ℂ sX) (hfb : IsBirationalMorphism f)
    (hO : ∀ U : Z.Opens, IsIso (f.app U)) {sW : W ⟶ Spec (.of ℂ)}
    (hWv : AlgebraicGeometry.IsVariety ℂ sW) (u : W ⟶ X) (hu : u ≫ sX = sW) [IsProper u]
    [Surjective u] {e : W} (he : IsClosed ({e} : Set W)) {y : Z} (hy : f (u e) = y)
    (hyb : y ∉ biregularLocus f) :
    ∃ (CX : ProperCurve sX) (C : ProperCurve sW), CX.IsContractedBy f ∧
      u '' closure {C.point} = closure {CX.point} ∧ C.IsContractedBy (u ≫ f) ∧
      closure {C.point} ⊆ (u ≫ f) ⁻¹' {y} := by
  obtain ⟨CX, hCXf, hCXy⟩ := exists_properCurve_isContractedBy_subset_fibre hZ f hfs hXv hfb hO
    (by simpa using u.isClosedMap _ he) hy hyb
  obtain ⟨C, hC⟩ := MMP.Mori.ProperCurve.exists_image_closure_eq_of_surjective hWv hXv u hu CX
  have hCy : closure {C.point} ⊆ (u ≫ f) ⁻¹' {y} := fun w hw => by
    simpa only [Set.mem_preimage, Scheme.Hom.comp_apply] using
      hCXy (hC ▸ ⟨w, hw, rfl⟩ : u w ∈ closure {CX.point})
  exact ⟨CX, C, hCXf, hC, fun w hw => (hCy hw).trans (hCy (subset_closure rfl)).symm, hCy⟩

/-- Both canonical divisors of a threefold step diagram are canonical divisors of dimension
`3`. -/
private theorem isCanonicalDivisor_three {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    {sXp : Xp ⟶ Spec (.of ℂ)} {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp) :
    K.IsCanonicalDivisor sXm 3 ∧
      MMP.Mori.Divisor.IsCanonicalDivisor sXp 3 (flipTransform fm fp K) := by
  obtain ⟨n, hK⟩ := h.isCanonicalDivisor
  obtain ⟨n', hK'⟩ := h.isCanonicalDivisor_plus
  obtain rfl : n = 3 := by exact_mod_cast hK.topologicalKrullDim_eq.symm.trans h.dim_minus
  obtain rfl : n' = 3 := by exact_mod_cast hK'.topologicalKrullDim_eq.symm.trans h.dim_plus
  exact ⟨hK, hK'⟩

/-- **Over the bad locus the comparison is strict.** If `h(η_E) ∈ Σ`, then
`a(E, X⁻, B⁻) < a(E, X⁺, B⁺)`. -/
private theorem lt_of_mem_badLocusBase {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    {sXp : Xp ⟶ Spec (.of ℂ)} {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp) {W : Scheme.{0}} {g : W ⟶ Xm}
    {g' : W ⟶ Xp} (hW : IsNormalVariety ℂ (g ≫ sXm)) (hW' : IsNormalVariety ℂ (g' ≫ sXp))
    (hg : IsBirationalMorphism g) (hg' : IsBirationalMorphism g') [IsProper g] [IsProper g']
    (hcomm : g ≫ fm = g' ≫ fp) (E : MMP.Mori.PrimeDivisor W)
    (hE : fm (g E.genericPoint) ∈ badLocusBase fm fp) {c c' : ℚ}
    (hc : IsDiscrepancy sXm 3 K B ⟨W, g, hW, hg, E⟩ c)
    (hc' : IsDiscrepancy sXp 3 (flipTransform fm fp K) (flipTransform fm fp B)
      ⟨W, g', hW', hg', E⟩ c') :
    c < c' := by
  -- instances
  have hZ := h.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have hXm := h.isNormalVariety_minus
  have hXp := h.isNormalVariety_plus
  haveI : QuasiCompact sXm := hXm.1.toQuasiCompact
  haveI : QuasiCompact sXp := hXp.1.toQuasiCompact
  haveI : IsProper sXm :=
    isProper_of_isProjectiveMorphism sXm h.isProjectiveVariety_minus.isProjective
  haveI : IsProper sXp :=
    isProper_of_isProjectiveMorphism sXp h.isProjectiveVariety_plus.isProjective
  have hfmb := h.isBirationalMorphism_minus
  have hfpb := h.isSmallMorphism_plus.isBirationalMorphism
  haveI := hfmb.isDominant
  haveI := hfpb.isDominant
  haveI : IsProper fm := isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus
  haveI : IsProper fp := h.isSmallMorphism_plus.isProper
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : IsNormal W := hW.2
  haveI : LocallyOfFiniteType (g ≫ sXm) := hW.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sXm)
  haveI : QuasiCompact (g ≫ sXm) := hW.1.toQuasiCompact
  haveI := hg.isDominant
  haveI := hg'.isDominant
  haveI : AlgebraicGeometry.IsVariety ℂ (g ≫ sXm) := hW.1
  haveI : AlgebraicGeometry.IsVariety ℂ sXm := hXm.1
  haveI : AlgebraicGeometry.IsVariety ℂ sXp := hXp.1
  have hsZ : g' ≫ sXp = g ≫ sXm := by
    rw [← h.comp_eq_plus, ← Category.assoc, ← hcomm, Category.assoc, h.comp_eq_minus]
  set h₀ := g ≫ fm with hh₀_def
  have hh₀ : IsBirationalMorphism h₀ := MMP.Mori.isBirationalMorphism_comp_of_isBirational fm g
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hfmb)
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hg)
  have hsW : h₀ ≫ sZ = g ≫ sXm := by rw [hh₀_def, Category.assoc, h.comp_eq_minus]
  -- canonical divisors, pairs and crepant boundaries
  obtain ⟨hK, hK'⟩ := isCanonicalDivisor_three h
  have hPm : MMP.Mori.IsPair sXm B := ⟨hXm, 3, K, hK, h.isQCartier_minus⟩
  have hPp : MMP.Mori.IsPair sXp (flipTransform fm fp B) :=
    ⟨hXp, 3, flipTransform fm fp K, hK', h.isQCartier_plus⟩
  obtain ⟨⟨Δm, hΔm, -⟩, -⟩ := MMP.Mori.IsPair.existsUnique_isCrepantBoundary hPm hK g hW hg
  obtain ⟨⟨Δp, hΔp, -⟩, -⟩ := MMP.Mori.IsPair.existsUnique_isCrepantBoundary hPp hK' g' hW' hg'
  have hcE : c = -Δm.coeff E := IsDiscrepancy.eq hc (hΔm E)
  have hc'E : c' = -Δp.coeff E := IsDiscrepancy.eq hc' (hΔp E)
  -- the divisor `H = Δ⁻ - Δ⁺` along curves
  obtain ⟨hH, L, L', hLB, hLB', hL, hL', hLq, hLq', hform⟩ :=
    exists_intersectionNumber_sub_eq hXm hXp hK hK' h.isQCartier_minus h.isQCartier_plus hW hW'
      hg hg' hsZ hΔm hΔp
  set BW := Δm - Δp with hBW_def
  have hamp_m : ∀ C : ProperCurve sXm, C.IsContractedBy fm →
      (Divisor.toQDivisor K + B).intersectionNumber ℂ sXm C.ι C.dim_le h.isQCartier_minus < 0 :=
    fun C hC => by
      have hpos := intersectionNumber_pos_of_hasRelativelyAmpleMultiple
        h.hasRelativelyAmpleMultiple_minus (isQCartier_neg h.isQCartier_minus) C hC
      rw [intersectionNumber_neg ℂ sXm C.ι C.dim_le h.isQCartier_minus
        (isQCartier_neg h.isQCartier_minus)] at hpos
      linarith
  have hamp_p : ∀ C : ProperCurve sXp, C.IsContractedBy fp →
      0 < (Divisor.toQDivisor (flipTransform fm fp K) + flipTransform fm fp B).intersectionNumber
        ℂ sXp C.ι C.dim_le h.isQCartier_plus := fun C hC =>
    intersectionNumber_pos_of_hasRelativelyAmpleMultiple h.hasRelativelyAmpleMultiple_plus
      h.isQCartier_plus C hC
  have hLle : ∀ C : ProperCurve (g ≫ sXm), C.IsContractedBy h₀ →
      L.intersectionNumber ℂ (g ≫ sXm) C.ι C.dim_le hLq ≤ 0 := fun C hC => by
    rcases intersectionNumber_pullback_eq_zero_or g rfl fm h.isQCartier_minus hL hLq C hC with
      h0 | ⟨d, hd, C'', hC'', heq⟩
    · rw [h0]
    · rw [heq]
      exact mul_nonpos_of_nonneg_of_nonpos hd (hamp_m C'' hC'').le
  have hL'ge : ∀ C : ProperCurve (g ≫ sXm), C.IsContractedBy h₀ →
      0 ≤ L'.intersectionNumber ℂ (g ≫ sXm) C.ι C.dim_le hLq' := fun C hC => by
    rcases intersectionNumber_pullback_eq_zero_or g' hsZ fp h.isQCartier_plus hL' hLq' C
        (by rw [← hcomm]; exact hC) with h0 | ⟨d, hd, C'', hC'', heq⟩
    · rw [h0]
    · rw [heq]
      exact mul_nonneg hd (hamp_p C'' hC'').le
  have hnef : ∀ C : ProperCurve (g ≫ sXm), C.IsContractedBy h₀ →
      BW.intersectionNumber ℂ (g ≫ sXm) C.ι C.dim_le hH ≤ 0 := fun C hC => by
    rw [hform C]
    linarith [hLle C hC, hL'ge C hC]
  -- the coefficients off the exceptional divisors vanish
  have hWZ : IsNormalVariety ℂ (h₀ ≫ sZ) := by rw [hsW]; exact hW
  have hBG : ∀ P : MMP.Mori.PrimeDivisor W,
      ¬ MMP.Flips.IsExceptionalPrimeDivisor sZ h₀ P → 0 ≤ BW.coeff P := fun P hP => by
    by_cases hex : MMP.Mori.RationalMap.IsExceptional (X := W) h₀.toRationalMap P
    · exact absurd (isExceptionalPrimeDivisor_of_isExceptional hZ hWZ hh₀ P hex) hP
    · obtain ⟨Q, hv⟩ := MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hZ
        (⟨W, h₀, hWZ, hh₀, P⟩ : DivisorOver ℂ sZ) hex
      have hPQ : h₀ P.genericPoint = Q.genericPoint :=
        MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hZ.1 hv
      have hU : fm (g P.genericPoint) ∉ badLocusBase fm fp := by
        intro hmem
        rw [← SetLike.mem_coe, coe_badLocusBase] at hmem
        refine hmem ⟨?_, ?_⟩
        · change h₀ P.genericPoint ∈ biregularLocus fm
          rw [hPQ]; exact genericPoint_mem_biregularLocus fm hfmb Q
        · change h₀ P.genericPoint ∈ biregularLocus fp
          rw [hPQ]; exact genericPoint_mem_biregularLocus fp hfpb Q
      have := eq_of_notMem_badLocusBase h hW hW' hg hg' hcomm P hU hK hK' (hΔm P) (hΔp P)
      change 0 ≤ Δm.coeff P - Δp.coeff P
      linarith
  -- effectivity (the negativity lemma)
  have hBW : 0 ≤ BW := nonneg_of_intersectionNumber_nonpos hZ hW h₀ hsW hh₀ hH hnef hBG
  have hBWc : ∀ P, 0 ≤ BW.coeff P := fun P => Finsupp.le_def.mp hBW P
  -- strictness
  rw [hcE, hc'E, neg_lt_neg_iff]
  by_contra hle
  push Not at hle
  have hE0 : BW.coeff E = 0 := by
    refine le_antisymm ?_ (hBWc E)
    change Δm.coeff E - Δp.coeff E ≤ 0
    linarith
  have hηE : E.genericPoint ∉ BW.supp := by
    rw [DivisorWithCoeffs.mem_supp_iff]
    rintro ⟨P, hP, hEP⟩
    by_cases hPE : P = E
    · subst hPE; exact hP hE0
    · exact MMP.Threefold.Mori.CanonUniq.genericPoint_notMem_support_of_ne (Ne.symm hPE) hEP
  haveI : JacobsonSpace W := LocallyOfFiniteType.jacobsonSpace (g ≫ sXm)
  have hEsupp : E.genericPoint ∈ (E.support : Set W) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  have hEcl : IsClosed (E.support : Set W) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure
  obtain ⟨e, ⟨heE, heS⟩, hec⟩ := nonempty_inter_closedPoints
    (⟨E.genericPoint, hEsupp, hηE⟩ : ((E.support : Set W) ∩ (BW.supp : Set W)ᶜ).Nonempty)
    (hEcl.isLocallyClosed.inter BW.supp.isClosed.isOpen_compl.isLocallyClosed)
  have hecl : IsClosed ({e} : Set W) := mem_closedPoints_iff.mp hec
  set y := h₀ e with hy_def
  have hsp : E.genericPoint ⤳ e := by
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact heE
  have hyBad : y ∈ badLocusBase fm fp :=
    (hsp.map h₀.continuous).mem_closed (badLocusBase fm fp).isClosed hE
  -- the fibre over `y` misses `Supp H`
  have hnegq : (-BW).IsQCartier := isQCartier_neg hH
  have hnefneg : (-BW).IsRelativelyNef (g ≫ sXm) h₀ :=
    MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg (g ≫ sXm) hnegq
      fun C hC => by
        rw [intersectionNumber_neg ℂ (g ≫ sXm) C.ι C.dim_le hH hnegq]
        linarith [hnef C hC]
  have hfib := MMP.Mori.QDivisor.preimage_singleton_subset_supp_or_disjoint_of_isRelativelyNef_neg
    ℂ sZ (g ≫ sXm) hZ hW h₀ hsW hh₀ hH (DivisorWithCoeffs.isEffective_iff_nonneg.mpr hBW)
    hnefneg y
  have hdisj : Disjoint (h₀.base ⁻¹' {y}) (BW.supp : Set W) :=
    hfib.resolve_left fun hsub => heS (hsub rfl)
  -- a curve `C` in the fibre, contradicting `(H · C) < 0`
  have hzero : ∀ C : ProperCurve (g ≫ sXm), closure {C.point} ⊆ h₀.base ⁻¹' {y} →
      BW.intersectionNumber ℂ (g ≫ sXm) C.ι C.dim_le hH = 0 := fun C hCy => by
    have hpt : C.point ∉ BW.supp := fun hmem =>
      Set.disjoint_left.mp hdisj (hCy (subset_closure rfl)) hmem
    obtain ⟨-, hiff⟩ := MMP.Fourfold.intersectionNumber_nonneg_and_eq_zero_iff (g ≫ sXm) BW hH hBW
      C hpt
    exact hiff.mpr fun x hx hmem =>
      Set.disjoint_left.mp hdisj (hCy (specializes_iff_mem_closure.mp hx)) hmem
  have hyU : y ∉ biregularLocus fm ⊓ biregularLocus fp := by
    rw [← SetLike.mem_coe, coe_badLocusBase] at hyBad
    exact hyBad
  by_cases hym : y ∈ biregularLocus fm
  · -- `f⁺` is not an isomorphism over `y`
    obtain ⟨CX, C, hCXf, hC, hCcon, hCy⟩ := exists_properCurve_lift_subset_fibre hZ fp
      h.comp_eq_plus hXp.1 hfpb h.isIso_app_plus hW.1 g' hsZ hecl
      (by rw [hy_def, ← Scheme.Hom.comp_apply, ← hcomm]) fun hyp => hyU ⟨hym, hyp⟩
    rw [← hcomm] at hCcon hCy
    obtain ⟨d, hd, hdeq⟩ := intersectionNumber_pullback_eq_mul_of_image g' hsZ h.isQCartier_plus hL'
      hLq' C CX hC
    have : 0 < L'.intersectionNumber ℂ (g ≫ sXm) C.ι C.dim_le hLq' := by
      rw [hdeq]; exact mul_pos hd (hamp_p CX hCXf)
    linarith [hzero C hCy, hform C, hLle C hCcon]
  · -- `f⁻` is not an isomorphism over `y`
    obtain ⟨CX, C, hCXf, hC, hCcon, hCy⟩ := exists_properCurve_lift_subset_fibre hZ fm
      h.comp_eq_minus hXm.1 hfmb h.isIso_app_minus hW.1 g rfl hecl rfl hym
    obtain ⟨d, hd, hdeq⟩ := intersectionNumber_pullback_eq_mul_of_image g rfl h.isQCartier_minus hL
      hLq C CX hC
    have : L.intersectionNumber ℂ (g ≫ sXm) C.ι C.dim_le hLq < 0 := by
      rw [hdeq]; exact mul_neg_of_pos_of_neg hd (hamp_m CX hCXf)
    linarith [hzero C hCy, hform C, hL'ge C hCcon]

end Comparison

/-! ### Centres and log discrepancies -/

section Centre

/-- The log discrepancy of `ξ = ord_E` is `1 + a(E, X, B)`. -/
private theorem eq_one_add_of_isValuationLogDiscrepancy {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {n : ℕ} {K : Divisor X}
    {B : QDivisor X} {D : DivisorOver ℂ sX} (hDp : IsProper D.f) {c : ℚ}
    (hc : IsDiscrepancy sX n K B D c) {a : ℝ} (ha : IsValuationLogDiscrepancy sX B D.valuation a) :
    a = 1 + c := by
  obtain ⟨n', D', -, hv, hl⟩ := ha
  exact MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hl
    (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc hDp) hv

end Centre

section StepComparison

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]

/-- `ξ⁺`, the valuation of `k(X⁺)` corresponding to `ξ = ord_E`, is `ord_E` for `(W, g', E)`. -/
private theorem valuation_eq_of_comap_eq {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} [IsIntegral Z]
    [IsDominant fm] [IsDominant fp] (hfp : IsBirationalMorphism fp) {W : Scheme.{0}}
    {sXm : Xm ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)} {g : W ⟶ Xm} {g' : W ⟶ Xp}
    (hW : IsNormalVariety ℂ (g ≫ sXm)) (hW' : IsNormalVariety ℂ (g' ≫ sXp))
    (hg : IsBirationalMorphism g) (hg' : IsBirationalMorphism g') (hcomm : g ≫ fm = g' ≫ fp)
    (E : MMP.Mori.PrimeDivisor W) {ξp : Valuation Xp.functionField (WithZero (Multiplicative ℤ))}
    (hξ : ξp.comap (functionFieldMap fp) =
      (⟨W, g, hW, hg, E⟩ : DivisorOver ℂ sXm).valuation.comap (functionFieldMap fm)) :
    (⟨W, g', hW', hg', E⟩ : DivisorOver ℂ sXp).valuation = ξp := by
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : IsNormal W := hW.2
  haveI : IsLocallyNoetherian W :=
    haveI := hW.1.toLocallyOfFiniteType
    LocallyOfFiniteType.isLocallyNoetherian (g ≫ sXm)
  haveI : IsDominant g := hg.isDominant
  haveI : IsDominant g' := hg'.isDominant
  have hinj : Function.Injective
      (Valuation.comap (Γ₀ := WithZero (Multiplicative ℤ)) (functionFieldMap fp)) := by
    intro v w hvw
    ext x
    obtain ⟨y, rfl⟩ := hfp.functionFieldMap_bijective.2 x
    exact congrArg (fun v => v y) hvw
  apply hinj
  rw [hξ]
  ext x
  simp only [Valuation.comap_apply]
  change E.divisorialValuation (functionFieldMap g' (functionFieldMap fp x)) =
    E.divisorialValuation (functionFieldMap g (functionFieldMap fm x))
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
    MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
  simp only [hcomm]

/-- **The threefold comparison.** In a threefold step diagram `X⁻ → Z ← X⁺`, let `ξ` be a
valuation of `k(X⁻)` with log discrepancy `a⁻` over `(X⁻, B⁻)` and `ξ⁺` the corresponding
valuation of `k(X⁺)`, with log discrepancy `a⁺` over `(X⁺, B⁺)`, `B⁺` the strict transform of
`B⁻`. Then `a⁻ ≤ a⁺`. -/
private theorem le_of_isThreefoldStepDiagram {sXm : Xm ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp)
    {ξ : Valuation Xm.functionField (WithZero (Multiplicative ℤ))}
    {ξp : Valuation Xp.functionField (WithZero (Multiplicative ℤ))}
    (hξ : haveI : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
      haveI := h.isBirationalMorphism_minus.isDominant
      haveI := h.isSmallMorphism_plus.isBirationalMorphism.isDominant
      ξp.comap (functionFieldMap fp) = ξ.comap (functionFieldMap fm))
    {am ap : ℝ} (ham : IsValuationLogDiscrepancy sXm B ξ am)
    (hap : IsValuationLogDiscrepancy sXp (flipTransform fm fp B) ξp ap) : am ≤ ap := by
  haveI : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
  haveI := h.isBirationalMorphism_minus.isDominant
  haveI := h.isSmallMorphism_plus.isBirationalMorphism.isDominant
  obtain ⟨-, D, -, hDξ, -⟩ := id ham
  obtain ⟨W, g, g', hW, hg, hgp, hg'p, hg', hcomm, E, hE⟩ := exists_commonModel h D
  have hW' : IsNormalVariety ℂ (g' ≫ sXp) := by
    rwa [← h.comp_eq_plus, ← Category.assoc, ← hcomm, Category.assoc, h.comp_eq_minus]
  set Dm : DivisorOver ℂ sXm := ⟨W, g, hW, hg, E⟩ with hDm
  set Dp : DivisorOver ℂ sXp := ⟨W, g', hW', hg', E⟩ with hDp
  have hE' : Dm.valuation = ξ := hE.trans hDξ
  have hDpv : Dp.valuation = ξp :=
    valuation_eq_of_comap_eq h.isSmallMorphism_plus.isBirationalMorphism hW hW' hg hg' hcomm E
      (by rw [hE']; exact hξ)
  obtain ⟨hK, hK'⟩ := isCanonicalDivisor_three h
  have hPm : MMP.Mori.IsPair sXm B := ⟨h.isNormalVariety_minus, 3, K, hK, h.isQCartier_minus⟩
  have hPp : MMP.Mori.IsPair sXp (flipTransform fm fp B) :=
    ⟨h.isNormalVariety_plus, 3, flipTransform fm fp K, hK', h.isQCartier_plus⟩
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPm hK Dm
  obtain ⟨c', hc'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPp hK' Dp
  have ham' : am = 1 + c := eq_one_add_of_isValuationLogDiscrepancy hgp hc (hE' ▸ ham)
  have hap' : ap = 1 + c' := eq_one_add_of_isValuationLogDiscrepancy hg'p hc' (hDpv ▸ hap)
  rw [ham', hap', add_le_add_iff_left, Rat.cast_le]
  by_cases hmem : fm (g E.genericPoint) ∈ badLocusBase fm fp
  · exact (lt_of_mem_badLocusBase h hW hW' hg hg' hcomm E hmem hc hc').le
  · exact (eq_of_notMem_badLocusBase h hW hW' hg hg' hcomm E hmem hK hK' hc hc').le

end StepComparison

/-! ### Divisors over a variety seen over a birational model -/

section CompProper

variable {X X' : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']

/-- A divisor `(W, h, E)` over `X`, with `h` proper, seen over `X'` through a proper birational
morphism `g : X ⟶ X'` over `ℂ`: the divisor `(W, g ∘ h, E)`. -/
private noncomputable def compProper {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
    (g : X ⟶ X') [IsProper g] (hg : IsBirationalMorphism g) (hs : g ≫ sX' = sX)
    (D : DivisorOver ℂ sX) (hD : IsProper D.f) : DivisorOver ℂ sX' where
  Y := D.Y
  f := D.f ≫ g
  isNormalVariety := by
    rw [Category.assoc, hs]
    exact D.isNormalVariety
  isBirationalMorphism := by
    haveI := D.isIntegral
    haveI := hD
    exact isBirationalMorphism_comp_of_isBirational g D.f
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hg)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism D.isBirationalMorphism)
  E := D.E

/-- The divisor `(W, g ∘ h, E)` has the valuation `ord_E` read on `k(X')` through `g`. -/
private theorem valuation_compProper {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
    (g : X ⟶ X') [IsProper g] (hg : IsBirationalMorphism g) (hs : g ≫ sX' = sX)
    (D : DivisorOver ℂ sX) (hD : IsProper D.f) :
    haveI := hg.isDominant
    (compProper g hg hs D hD).valuation = D.valuation.comap (functionFieldMap g) := by
  haveI := hg.isDominant
  haveI := D.isIntegral
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI := D.isDominant
  ext t
  change D.E.divisorialValuation (functionFieldMap (D.f ≫ g) t) =
    D.E.divisorialValuation (functionFieldMap D.f (functionFieldMap g t))
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

end CompProper

/-! ### Transport of log discrepancies along an isomorphism -/

section Iso

variable {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

/-- Under an isomorphism `f : Y ⟶ X`, every prime divisor `Γ` of `X` is the image of a prime
divisor `P` of `Y`: `f(η_P) = η_Γ`. -/
private theorem exists_primeDivisor_map_genericPoint_eq (f : Y ⟶ X) [IsIso f]
    (Γ : MMP.Mori.PrimeDivisor X) :
    ∃ P : MMP.Mori.PrimeDivisor Y, f P.genericPoint = Γ.genericPoint := by
  set x : Y := (inv f) Γ.genericPoint
  have hx : f x = Γ.genericPoint := by
    simp only [x]
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    rfl
  have hco : Order.coheight x = 1 := by
    have h := ringKrullDim_eq_of_ringEquiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight, hx,
      Γ.coheight_genericPoint] at h
    exact_mod_cast h.symm
  let E : MMP.Mori.PrimeDivisor Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hco
  have hE : E.genericPoint = x := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hco
  exact ⟨E, hE ▸ hx⟩

/-- The only irreducible component of an irreducible space is the whole space. -/
private theorem mem_irreducibleComponent {T : Type*} [TopologicalSpace T] [IrreducibleSpace T]
    (W : irreducibleComponents T) (t : T) : t ∈ W.1 :=
  (Set.eq_univ_of_univ_subset
    (W.2.2 (IrreducibleSpace.isIrreducible_univ T) (Set.subset_univ _))).symm ▸ Set.mem_univ t

/-- **Pull-back of Cartier divisors along a composite**: `g^*(f^*L) = (f ∘ g)^*L`. -/
private theorem isPullback_comp {X Y Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] [IsLocallyNoetherian Z] [IsNormal Z]
    {f : Y ⟶ X} {g : Z ⟶ Y} {L : Divisor X} {L' : Divisor Y}
    {L'' : Divisor Z} {hB : ∀ W : irreducibleComponents Y, f (componentGenericPoint Y W) ∉ L.supp}
    {hB' : ∀ W : irreducibleComponents Z, g (componentGenericPoint Z W) ∉ L'.supp}
    (h : L.IsPullback f hB L') (h' : L'.IsPullback g hB' L'')
    (hB'' : ∀ W : irreducibleComponents Z, (g ≫ f) (componentGenericPoint Z W) ∉ L.supp) :
    L.IsPullback (g ≫ f) hB'' L'' := by
  intro U φ hφ E hE
  have hψ := h.isLocalEquation hφ
  rw [h' (f ⁻¹ᵁ U) _ hψ E hE]
  congr 1
  set z := componentGenericPoint Z E.component
  have hzU : f (g z) ∈ U := E.map_componentGenericPoint_mem (g ≫ f) hE
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hzU (hB'' _) (mem_irreducibleComponent
    (pointComponent ((g ≫ f) z)) _)
  rw [pullbackComponent_eq hB'' hφ hzU _ a ha]
  set W := pointComponent (g z)
  have hspec : componentGenericPoint Y W ⤳ g z :=
    (isGenericPoint_componentGenericPoint Y W).specializes (mem_pointComponent _)
  have hWU : f (componentGenericPoint Y W) ∈ U :=
    (f.base.hom.map_specializes hspec).mem_open U.isOpen hzU
  have hb : (stalkToRationalFunctions Y (mem_pointComponent (g z))).hom
      (Units.map (f.stalkMap (g z)).hom.toMonoidHom a) =
      ((pullbackLocalEquation f hB hφ : (RationalFunctions Y)ˣ) : RationalFunctions Y) W := by
    have e1 := congrArg Units.val (pullbackLocalEquation_apply f hB hφ W hWU)
    refine Eq.trans ?_ e1.symm
    rw [pullbackComponent_eq hB hφ hWU
      (mem_irreducibleComponent (pointComponent ((g ≫ f) z)) _)
      (Units.map (X.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec)).hom.toMonoidHom a)
      ?_]
    · change (stalkToRationalFunctions Y _).hom ((f.stalkMap (g z)).hom a.val) =
        (f.stalkMap _).hom ((X.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec)).hom
          a.val)
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, stalkToRationalFunctions,
        Scheme.Hom.stalkSpecializes_stalkMap]
    · change (X.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec) ≫
        X.presheaf.stalkSpecializes _).hom a.val = _
      rw [TopCat.Presheaf.stalkSpecializes_comp]
      exact ha
  rw [pullbackComponent_eq hB' hψ _ (mem_pointComponent (g z)) _ hb]
  ext
  change _ = ((g ≫ f).stalkMap z).hom a.val
  rw [Scheme.Hom.stalkMap_comp]
  rfl

/-- **Log discrepancies are preserved by isomorphisms of pairs.** Let `f : Y ⟶ X` be an
isomorphism carrying the boundary `B_Y` of `Y` to the boundary `B` of `X`, and let `X` have a
canonical divisor of dimension `n`. Then a log discrepancy `a` of a proper divisor `(W, g, E)`
over `(Y, B_Y)` is the log discrepancy of `(W, f ∘ g, E)` over `(X, B)`. -/
private theorem isLogDiscrepancy_compIso [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)}
    (f : Y ⟶ X) [IsIso f] {n : ℕ} {K₀ : Divisor X} (hK₀ : K₀.IsCanonicalDivisor sX n)
    {B : QDivisor X} {BY : QDivisor Y}
    (hB : ∀ (P : MMP.Mori.PrimeDivisor Y) (Γ : MMP.Mori.PrimeDivisor X),
      f P.genericPoint = Γ.genericPoint → BY.coeff P = B.coeff Γ)
    {D : DivisorOver ℂ (f ≫ sX)} (hD : IsProper D.f) {a : ℝ}
    (h : MMP.Intersection.IsLogDiscrepancy (f ≫ sX) n (QDivisor.toRDivisor BY) D a) :
    MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B)
      (compProper f (isBirationalMorphism_of_isIso f) rfl D hD) a := by
  obtain ⟨hYv, -, ω, hω0, -, m, r, C, C', hCc, hsum, hpb, rfl⟩ := h
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f
  haveI := D.isIntegral
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI := D.isDominant
  haveI := hD
  have hs : inv f ≫ f ≫ sX = sX := by simp
  have hXv : IsNormalVariety ℂ sX := by
    refine ⟨(isVariety_iff ℂ sX).2 ⟨inferInstance, ?_, ?_, ?_⟩, inferInstance⟩
    · haveI := hYv.1.toIsSeparated
      rw [← hs]
      infer_instance
    · haveI := hYv.1.toLocallyOfFiniteType
      rw [← hs]
      infer_instance
    · haveI := hYv.1.toQuasiCompact
      rw [← hs]
      infer_instance
  haveI : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (f ≫ sX) := hYv.1.toLocallyOfFiniteType
  have hn : topologicalKrullDim X = n := hK₀.topologicalKrullDim_eq
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have hbij := (isBirationalMorphism_of_isIso f).functionFieldMap_bijective
  obtain ⟨τ, rfl, hτ⟩ := exists_pullbackRationalPluriForms_eq f hbij hd ω
  have hτ0 : τ ≠ 0 := hτ hω0
  have hKτ : (divisorOfForm τ).IsCanonicalDivisor sX n := by
    refine hK₀.of_linearlyEquivalent ?_
    have := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hXv hK₀ hτ0
    rwa [one_smul] at this
  have hL : ∀ i, ∃ L : Divisor X, L.IsCartier ∧
      L.IsPullback f (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp f L) (C i) := by
    intro i
    obtain ⟨L, hLpb⟩ := (hCc i).exists_isPullback (f := inv f)
      (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp (inv f) (C i))
    have hLc : L.IsCartier := hLpb.isCartier (hCc i)
    obtain ⟨L₂, hL₂⟩ := hLc.exists_isPullback (f := f)
      (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp f L)
    refine ⟨L, hLc, ?_⟩
    convert hL₂ using 1
    refine Finsupp.ext fun P => ?_
    obtain ⟨Γ, hΓ⟩ := exists_primeDivisor_map_genericPoint_eq (inv f) P
    have hP : f P.genericPoint = Γ.genericPoint := by
      rw [← hΓ, ← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
      rfl
    have h1 := MMP.Positivity.coeff_eq_of_isPullback P Γ hP hLc hL₂
    have h2 := MMP.Positivity.coeff_eq_of_isPullback Γ P hΓ (hCc i) hLpb
    exact (h2.symm.trans h1.symm)
  choose L hLc hLpb using hL
  refine ⟨hXv, (inferInstance : IsProper (D.f ≫ f)), τ, hτ0,
    ⟨_, hKτ, fun Γ => coeff_divisorOfForm τ Γ⟩, m, r, L, C',
    hLc, fun Γ => ?_, fun i => ?_, ?_⟩
  · obtain ⟨P, hP⟩ := exists_primeDivisor_map_genericPoint_eq f Γ
    have hord := MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso f hbij hd P Γ hP τ
    have hc : ∀ i, (C i).coeff P = (L i).coeff Γ := fun i =>
      MMP.Positivity.coeff_eq_of_isPullback P Γ hP (hLc i) (hLpb i)
    have := hsum P
    simp only [QDivisor.coeff_toRDivisor, hord, hB P Γ hP, hc] at this ⊢
    exact this
  · obtain ⟨hC, hCpb⟩ := hpb i
    exact ⟨_, isPullback_comp (hLpb i) hCpb
      (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp (D.f ≫ f) (L i))⟩
  · have hcomp := MMP.Flips.pullbackRationalPluriForms_comp f D.f hbij
      D.isBirationalMorphism.functionFieldMap_bijective hd τ
    change 1 + (D.E.ordForm (pullbackRationalPluriForms (f ≫ sX) D.f
        (pullbackRationalPluriForms sX f τ)) : ℝ) - _ =
      1 + (D.E.ordForm (pullbackRationalPluriForms sX (D.f ≫ f) τ) : ℝ) - _
    rw [hcomp]
    rfl

end Iso

/-! ### Valuations of function fields -/

section Valuations

/-- Pulling a valuation back along a composite: `ξ ∘ (a ≫ b)^* = (ξ ∘ a^*) ∘ b^*`. -/
private theorem comap_functionFieldMap_comp {A B C : Scheme.{0}} [IsIntegral A] [IsIntegral B]
    [IsIntegral C] (a : A ⟶ B) (b : B ⟶ C) [IsDominant a] [IsDominant b] [IsDominant (a ≫ b)]
    (ξ : Valuation A.functionField (WithZero (Multiplicative ℤ))) :
    ξ.comap (functionFieldMap (a ≫ b)) =
      (ξ.comap (functionFieldMap a)).comap (functionFieldMap b) := by
  ext t
  simp only [Valuation.comap_apply]
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

/-- The map of function fields only depends on the morphism. -/
private theorem functionFieldMap_congr {A B : Scheme.{0}} [IsIntegral A] [IsIntegral B]
    {g g' : A ⟶ B} [IsDominant g] [IsDominant g'] (h : g = g') :
    functionFieldMap g = functionFieldMap g' := by
  subst h
  rfl

end Valuations

/-! ### Transport of log discrepancies along isomorphisms of models -/

section Transport

/-- **Log discrepancies of valuations are preserved by isomorphisms of pairs.** Let
`ψ : Y ⟶ X` be an isomorphism carrying the boundary `B_Y` to `B`. If `a` is the log
discrepancy of `v` over `(Y, B_Y)`, it is the log discrepancy of `v ∘ ψ^*` over `(X, B)`. -/
private theorem isValuationLogDiscrepancy_comap_of_isIso {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {sX : X ⟶ Spec (.of ℂ)} (ψ : Y ⟶ X) [IsIso ψ] {n : ℕ} {K₀ : Divisor X}
    (hK₀ : K₀.IsCanonicalDivisor sX n) (hdim : topologicalKrullDim Y = n)
    {B : QDivisor X} {BY : QDivisor Y}
    (hB : ∀ (P : MMP.Mori.PrimeDivisor Y) (Γ : MMP.Mori.PrimeDivisor X),
      ψ P.genericPoint = Γ.genericPoint → BY.coeff P = B.coeff Γ)
    {v : Valuation Y.functionField (WithZero (Multiplicative ℤ))} {a : ℝ}
    (ha : IsValuationLogDiscrepancy (ψ ≫ sX) BY v a) :
    haveI := (isBirationalMorphism_of_isIso ψ).isDominant
    IsValuationLogDiscrepancy sX B (v.comap (functionFieldMap ψ)) a := by
  obtain ⟨n', D, hDp, hDv, hl⟩ := ha
  obtain rfl : n' = n := by
    have h2 := MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hl
    rw [hdim] at h2
    exact_mod_cast h2.symm
  refine ⟨n', compProper ψ (isBirationalMorphism_of_isIso ψ) rfl D hDp,
    (inferInstance : IsProper (D.f ≫ ψ)), ?_, isLogDiscrepancy_compIso ψ hK₀ hB hDp hl⟩
  rw [valuation_compProper, hDv]

/-- Along an equality `a = b` of indices, the identification `V_a = V_b` of models of a programme
is compatible with the morphisms `π_a`, `π_b` to the base. -/
private theorem eqToHom_comp_modelMap {V Z : Scheme.{0}} {Y : ℕ → Scheme.{0}} (π : V ⟶ Z)
    (πY : ∀ k, Y k ⟶ Z) {a b : ℕ} (h : a = b) :
    eqToHom (congrArg (modelSeq V Y) h) ≫ modelMap π πY b = modelMap π πY a := by
  subst h; simp

/-- At the end `V_M ≅ W` of a programme, identified with `V_j`, the boundary `Θ_j` corresponds
to the boundary `B` of `W` when `Θ_M = e⁻¹_* B`. -/
private theorem coeff_eq_of_boundary_eq {V W : Scheme.{0}} {Y : ℕ → Scheme.{0}}
    {Θ : QDivisor V} {ΘY : ∀ k, QDivisor (Y k)} (B : QDivisor W) {M j : ℕ} (hM : M = j)
    (e : modelSeq V Y M ≅ W) (hb : divisorSeq Θ ΘY M = inverseTransformDivisor e.hom B)
    (P : MMP.Mori.PrimeDivisor W) (Γ : MMP.Mori.PrimeDivisor (modelSeq V Y j))
    (h : (e.inv ≫ eqToHom (congrArg (modelSeq V Y) hM)) P.genericPoint = Γ.genericPoint) :
    B.coeff P = (divisorSeq Θ ΘY j).coeff Γ := by
  subst hM
  simp only [eqToHom_refl, Category.comp_id] at h
  have hΓ : e.hom Γ.genericPoint = P.genericPoint := by
    rw [← h, ← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  change _ = divisorSeq Θ ΘY M Γ
  rw [hb, inverseTransformDivisor_apply_of_map_genericPoint hΓ
    (le_biregularLocus (V := ⊤) (inferInstance : IsIso (e.hom ∣_ ⊤)) trivial)]
  rfl

end Transport

/-! ### Coefficient decreases -/

section Decrease

/-- **Log discrepancies do not decrease at a coefficient decrease.** For a crepant junction
`(p_i, Θ_i)` of `(X_i, B_i)` and its decreased boundary `Θ_i'`, every valuation `ξ` of `k(Y_i)`
has `a(ξ; Y_i, Θ_i) ≤ a(ξ; Y_i, Θ_i')`. -/
private theorem le_of_isDecreasedBoundary {T : StabilizedTail} {i : ℕ}
    {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    (J : CrepantJunction (T.sX i) (T.B i) I) {Θ' : QDivisor J.Y}
    (hΘ' : StabilizedTail.IsDecreasedBoundary J Θ') {n : ℕ} {K : Divisor J.Y}
    (hK : K.IsCanonicalDivisor (J.p ≫ T.sX i) n)
    {ξ : Valuation J.Y.functionField (WithZero (Multiplicative ℤ))} {a a' : ℝ}
    (ha : IsValuationLogDiscrepancy (J.p ≫ T.sX i) J.Θ ξ a)
    (ha' : IsValuationLogDiscrepancy (J.p ≫ T.sX i) Θ' ξ a') : a ≤ a' := by
  classical
  obtain ⟨b, hb, hΘ⟩ := J.Θ_eq
  obtain ⟨b', hb', hΘ'⟩ := hΘ'
  have hbb : ∀ s : I, b s ≤ b' s := by
    intro s
    obtain ⟨s', hs', hl⟩ := hb' s
    have := le_of_isThreefoldStepDiagram (T.isThreefoldStepDiagram i) hs' (hb s)
      (by rw [← T.B_eq i]; exact hl)
    exact_mod_cast this
  set Δ : QDivisor J.Y := ∑ s : I, Finsupp.single (J.E s) (b' s - b s) with hΔ
  have hΔe : Δ.IsEffective := by
    intro P
    change 0 ≤ (∑ s : I, Finsupp.single (J.E s) (b' s - b s)) P
    rw [Finsupp.finset_sum_apply]
    refine Finset.sum_nonneg fun s _ => ?_
    rw [Finsupp.single_apply]
    split_ifs
    · exact sub_nonneg.mpr (hbb s)
    · exact le_rfl
  have hΘΔ : J.Θ = Θ' + Δ := by
    rw [hΘ, hΘ', hΔ, add_assoc, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finsupp.single_add]
    congr 1
    ring
  obtain ⟨-, D, hDp, hDv, -⟩ := id ha
  have hX : IsNormalVariety ℂ (J.p ≫ T.sX i) := J.isQFactorial.1
  have hP' : MMP.Mori.IsPair (J.p ≫ T.sX i) Θ' :=
    ⟨hX, n, K, hK, isQCartier_of_isQFactorial _ J.isQFactorial _⟩
  have hP : MMP.Mori.IsPair (J.p ≫ T.sX i) (Θ' + Δ) :=
    ⟨hX, n, K, hK, isQCartier_of_isQFactorial _ J.isQFactorial _⟩
  obtain ⟨c', hc'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP' hK D
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK D
  have h1 : a = 1 + c :=
    eq_one_add_of_isValuationLogDiscrepancy hDp hc (by rw [← hΘΔ, hDv]; exact ha)
  have h2 : a' = 1 + c' := eq_one_add_of_isValuationLogDiscrepancy hDp hc' (hDv ▸ ha')
  rw [h1, h2, add_le_add_iff_left, Rat.cast_le]
  exact MMP.Threefold.Mori.Helpers.isDiscrepancy_le_of_effective hΔe hc' hc

end Decrease

/-! ### Flips of a bridge -/

section Flip

/-- **Log discrepancies do not decrease across a flip of a bridge.** For the `k`-th flip
`(V_k, Θ_k) → T_k ← (V_{k+1}, Θ_{k+1})` of the `i`-th bridge of a terminal chain, with target
the model `C.flipTargetOf i k d` (`V_{k+1}` itself, or the next junction `Y_{i+1} ≅ V_{m_i}`),
`a(v; V_k, Θ_k) ≤ a(v'; V_{k+1}, Θ_{k+1})` for corresponding valuations `v`, `v'`. -/
private theorem le_of_isValuationLogDiscrepancy_flipTargetOf {T : StabilizedTail}
    (C : StabilizedTail.TerminalChain T) (i : ℕ) (k : Fin (C.bridge i).P.m)
    (d : Decidable (k.1 + 1 < (C.bridge i).P.m))
    {v : Valuation (C.model ⟨i, some k⟩).functionField (WithZero (Multiplicative ℤ))}
    {v' : Valuation (C.model (C.flipTargetOf i k d)).functionField (WithZero (Multiplicative ℤ))}
    (hv' : haveI := C.isIntegral_flipBase i k
      haveI := C.isDominant_flipSourceMap i k
      haveI := C.isDominant_flipTargetMapOf i k d
      v'.comap (functionFieldMap (C.flipTargetMapOf i k d)) =
        v.comap (functionFieldMap ((C.bridge i).P.g k)))
    {a a' : ℝ}
    (ha : IsValuationLogDiscrepancy (C.modelStructure ⟨i, some k⟩)
      (C.modelBoundary ⟨i, some k⟩) v a)
    (ha' : IsValuationLogDiscrepancy (C.modelStructure (C.flipTargetOf i k d))
      (C.modelBoundary (C.flipTargetOf i k d)) v' a') :
    a ≤ a' := by
  have hD := (C.bridge i).P.isThreefoldStepDiagram k k.2
  have hΘ := (C.bridge i).P.ΘY_eq k k.2
  haveI : CompactSpace (C.model ⟨i, some k⟩) :=
    inferInstanceAs (CompactSpace (modelSeq (C.junction i).Y (C.bridge i).P.Y k))
  cases d with
  | isTrue h =>
    refine le_of_isThreefoldStepDiagram hD hv' ha ?_
    rw [← hΘ]
    exact ha'
  | isFalse h =>
    haveI := C.isIntegral_flipBase i k
    haveI := C.isDominant_flipSourceMap i k
    haveI := hD.isSmallMorphism_plus.isBirationalMorphism.isDominant
    have hmk : (C.bridge i).P.m = k.1 + 1 := by omega
    let ψ : (C.junction (i + 1)).Y ≅ (C.bridge i).P.Y k := (C.bridge i).e.symm ≪≫
      eqToIso (congrArg (modelSeq (C.junction i).Y (C.bridge i).P.Y) hmk)
    haveI : IsIso ψ.hom := ψ.isIso_hom
    revert v'
    change ∀ v' : Valuation (C.junction (i + 1)).Y.functionField (WithZero (Multiplicative ℤ)),
      v'.comap (functionFieldMap (ψ.hom ≫ (C.bridge i).P.gp k)) =
        v.comap (functionFieldMap ((C.bridge i).P.g k)) →
      IsValuationLogDiscrepancy ((C.junction (i + 1)).p ≫ T.sX (i + 1))
        (C.junction (i + 1)).Θ v' a' → a ≤ a'
    intro v' hv' ha'
    have hv'' : (v'.comap (functionFieldMap ψ.hom)).comap
        (functionFieldMap ((C.bridge i).P.gp k)) =
        v.comap (functionFieldMap ((C.bridge i).P.g k)) := by
      rw [← comap_functionFieldMap_comp]
      exact hv'
    have hstr : ψ.hom ≫ (C.bridge i).P.sY k = (C.junction (i + 1)).p ≫ T.sX (i + 1) := by
      rw [← hD.comp_eq_plus, ← (C.bridge i).P.comp_eq_base k k.2, ← Category.assoc _ _ (T.sZ i),
        ← (C.bridge i).P.πY_eq k k.2]
      change ((C.bridge i).e.inv ≫
          eqToHom (congrArg (modelSeq (C.junction i).Y (C.bridge i).P.Y) hmk)) ≫
        modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY (k.1 + 1) ≫ T.sZ i = _
      rw [Category.assoc, ← Category.assoc (eqToHom _), eqToHom_comp_modelMap _ _ hmk,
        (C.bridge i).modelMap_eq]
      simp [(T.isThreefoldStepDiagram i).comp_eq_plus]
    rw [← hstr] at ha'
    obtain ⟨np, hKp⟩ := hD.isCanonicalDivisor_plus
    have hdim : topologicalKrullDim (C.junction (i + 1)).Y = np := by
      rw [(C.junction (i + 1)).dim_eq, ← hD.dim_plus, hKp.topologicalKrullDim_eq]
    have hiso := isValuationLogDiscrepancy_comap_of_isIso ψ.hom hKp hdim
      (B := (C.bridge i).P.ΘY k)
      (fun P Γ h => coeff_eq_of_boundary_eq _ hmk (C.bridge i).e (C.bridge i).boundary_eq P Γ h)
      ha'
    refine le_of_isThreefoldStepDiagram hD hv'' ha ?_
    rw [← hΘ]
    exact hiso

end Flip

/-- **Weights are antitone in log discrepancies.** If every log discrepancy of `v` on the
model `x` is at most every log discrepancy of `v'` on the model `y`, then the weight of `v'` is
at most the weight of `v`. -/
private theorem weight_le_of_forall_le {T : StabilizedTail} {C : StabilizedTail.TerminalChain T}
    {N : ℕ} {x y : C.ModelIndex}
    {v : Valuation (C.model x).functionField (WithZero (Multiplicative ℤ))}
    {v' : Valuation (C.model y).functionField (WithZero (Multiplicative ℤ))} {w w' : ℕ}
    (hw : C.IsValuationWeight N x v w) (hw' : C.IsValuationWeight N y v' w')
    (h : ∀ a a' : ℝ, IsValuationLogDiscrepancy (C.modelStructure x) (C.modelBoundary x) v a →
      IsValuationLogDiscrepancy (C.modelStructure y) (C.modelBoundary y) v' a' → a ≤ a') :
    w' ≤ w := by
  obtain ⟨-, a, ha, rfl⟩ := hw
  obtain ⟨-, a', ha', rfl⟩ := hw'
  exact difficultyWeight_mono _ (by linarith [h a a' ha ha'])

variable {T : StabilizedTail}

/-- Weights do not increase under a move of a prepared chain: for a coefficient decrease
`(Y_i, Θ_i) ⇝ (Y_i, Θ_i')` (inside a bridge with flips, or identified with the next junction
through the bridge's `e` when it has none) and for a small terminal flip `(Y⁻, Θ⁻) ⤏ (Y⁺, Θ⁺)`,
every normalized divisorial valuation `v` exceptional over both models has
`w_v(Y', Θ') ≤ w_v(Y, Θ)`. -/
@[mmp "lem_mmp_indexd_move_weight_monotone"]
public theorem le_of_isValuationWeight_of_move (Q : PreparedChain T) :
    (∀ (i : ℕ) (_ : Q.start ≤ i) (h : 0 < (Q.chain.bridge i).P.m)
      (v : Valuation (Q.chain.model ⟨i, none⟩).functionField (WithZero (Multiplicative ℤ)))
      (w w' : ℕ), Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ v w →
        Q.chain.IsValuationWeight Q.scale ⟨i, some ⟨0, h⟩⟩ v w' → w' ≤ w) ∧
    (∀ (i : ℕ) (_ : Q.start ≤ i) (h : (Q.chain.bridge i).P.m = 0)
      (v : Valuation (Q.chain.model ⟨i, none⟩).functionField (WithZero (Multiplicative ℤ)))
      (v' : Valuation (Q.chain.model ⟨i + 1, none⟩).functionField
        (WithZero (Multiplicative ℤ))) (w w' : ℕ),
      v' = v.comap (functionFieldMap (eqToHom (congrArg
        (modelSeq (Q.chain.junction i).Y (Q.chain.bridge i).P.Y) h.symm) ≫
          (Q.chain.bridge i).e.hom)) →
      Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ v w →
        Q.chain.IsValuationWeight Q.scale ⟨i + 1, none⟩ v' w' → w' ≤ w) ∧
    (∀ (μ : Q.FlipMove)
      (v : Valuation (Q.chain.model μ.source.1).functionField (WithZero (Multiplicative ℤ)))
      (v' : Valuation (Q.chain.model μ.target.1).functionField (WithZero (Multiplicative ℤ)))
      (w w' : ℕ),
      v'.comap (functionFieldMap μ.targetMap) = v.comap (functionFieldMap μ.sourceMap) →
      Q.chain.IsValuationWeight Q.scale μ.source.1 v w →
        Q.chain.IsValuationWeight Q.scale μ.target.1 v' w' → w' ≤ w) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i _ h v w w' hw hw'
    obtain ⟨n, hK⟩ := (Q.chain.bridge i).P.isCanonicalDivisor
    exact weight_le_of_forall_le hw hw' fun _ _ =>
      le_of_isDecreasedBoundary (Q.chain.junction i) (Q.chain.bridge i).isDecreasedBoundary hK
  · intro i _ h v v' w w' hv' hw hw'
    subst hv'
    refine weight_le_of_forall_le hw hw' fun a a' ha ha' => ?_
    -- the identification `ψ : Y_{i+1} ≅ V_{m_i} = V_0` of the bridge
    let ψI : (Q.chain.junction (i + 1)).Y ≅
        modelSeq (Q.chain.junction i).Y (Q.chain.bridge i).P.Y 0 :=
      (Q.chain.bridge i).e.symm ≪≫
        eqToIso (congrArg (modelSeq (Q.chain.junction i).Y (Q.chain.bridge i).P.Y) h)
    have hφ : eqToHom (congrArg (modelSeq (Q.chain.junction i).Y (Q.chain.bridge i).P.Y)
        h.symm) ≫ (Q.chain.bridge i).e.hom = ψI.inv := rfl
    have hvψ : ∀ u : Valuation
        (modelSeq (Q.chain.junction i).Y (Q.chain.bridge i).P.Y 0).functionField
        (WithZero (Multiplicative ℤ)), (u.comap (functionFieldMap (eqToHom (congrArg
          (modelSeq (Q.chain.junction i).Y (Q.chain.bridge i).P.Y) h.symm) ≫
            (Q.chain.bridge i).e.hom))).comap (functionFieldMap ψI.hom) = u := by
      intro u
      rw [← comap_functionFieldMap_comp]
      ext t
      simp only [Valuation.comap_apply]
      rw [functionFieldMap_congr (show _ ≫ ψI.hom = 𝟙 _ from by rw [hφ]; exact ψI.inv_hom_id),
        functionFieldMap_id_apply]
    -- `ψ` is compatible with the structure morphisms
    have hπ : ψI.hom ≫ modelMap ((Q.chain.junction i).p ≫ T.f i) (Q.chain.bridge i).P.πY 0 =
        (Q.chain.junction (i + 1)).p ≫ T.fp i := by
      change ((Q.chain.bridge i).e.inv ≫
        eqToHom (congrArg (modelSeq (Q.chain.junction i).Y (Q.chain.bridge i).P.Y) h)) ≫ _ = _
      rw [Category.assoc, eqToHom_comp_modelMap _ _ h, (Q.chain.bridge i).modelMap_eq,
        Iso.inv_hom_id_assoc]
    have hstr : ψI.hom ≫ modelStr ((Q.chain.junction i).p ≫ T.sX i) (Q.chain.bridge i).P.sY 0 =
        (Q.chain.junction (i + 1)).p ≫ T.sX (i + 1) := by
      have e0 : modelStr ((Q.chain.junction i).p ≫ T.sX i) (Q.chain.bridge i).P.sY 0 =
          modelMap ((Q.chain.junction i).p ≫ T.f i) (Q.chain.bridge i).P.πY 0 ≫ T.sZ i := by
        change (Q.chain.junction i).p ≫ T.sX i = ((Q.chain.junction i).p ≫ T.f i) ≫ T.sZ i
        rw [Category.assoc, (T.isThreefoldStepDiagram i).comp_eq_minus]
      rw [e0, ← Category.assoc, hπ, Category.assoc, (T.isThreefoldStepDiagram i).comp_eq_plus]
    have ha'' : IsValuationLogDiscrepancy
        (ψI.hom ≫ modelStr ((Q.chain.junction i).p ≫ T.sX i) (Q.chain.bridge i).P.sY 0)
        (Q.chain.junction (i + 1)).Θ (v.comap (functionFieldMap (eqToHom (congrArg
          (modelSeq (Q.chain.junction i).Y (Q.chain.bridge i).P.Y) h.symm) ≫
            (Q.chain.bridge i).e.hom))) a' := by
      rw [hstr]
      exact ha'
    -- transport to `(Y_i, Θ_i')`
    obtain ⟨n, hK⟩ := (Q.chain.bridge i).P.isCanonicalDivisor
    have hdim : topologicalKrullDim (Q.chain.junction (i + 1)).Y = n := by
      rw [(Q.chain.junction (i + 1)).dim_eq, ← (Q.chain.junction i).dim_eq,
        hK.topologicalKrullDim_eq]
    have hiso := isValuationLogDiscrepancy_comap_of_isIso ψI.hom hK hdim
      (B := (Q.chain.bridge i).Θ')
      (fun P Γ hP => coeff_eq_of_boundary_eq _ h (Q.chain.bridge i).e
        (Q.chain.bridge i).boundary_eq P Γ hP) ha''
    have hiso' : IsValuationLogDiscrepancy ((Q.chain.junction i).p ≫ T.sX i)
        (Q.chain.bridge i).Θ' v a' :=
      (congrArg (fun u => IsValuationLogDiscrepancy ((Q.chain.junction i).p ≫ T.sX i)
        (Q.chain.bridge i).Θ' u a') (hvψ v)).mp hiso
    exact le_of_isDecreasedBoundary (Q.chain.junction i) (Q.chain.bridge i).isDecreasedBoundary
      hK ha hiso'
  · intro μ v v' w w' hv' hw hw'
    exact weight_le_of_forall_le hw hw' fun _ _ =>
      le_of_isValuationLogDiscrepancy_flipTargetOf Q.chain μ.1.1 μ.1.2 inferInstance hv'

end MMP.Fourfold.StabilizedTail.PreparedChain
