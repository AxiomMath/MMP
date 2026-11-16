module

public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChainDifficulty
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.DecreasedPair
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.PrimeDivisorPersistence

/-!
# Monotonicity along a terminal chain

Let `(p_i, Θ_i)_{i ≥ 0}`, `p_i : Y_i ⟶ X_i`, be a terminal chain over a stabilized small klt tail
`(X_i, B_i, Z_i, f_i, f_i⁺)_{i ≥ 0}` of fourfolds, and let `(M_n, Θ^{M_n})_{n ≥ 0}` be its models,
in order. All the models are birational to `X_0`, so a valuation `ξ` of `k(X_0)` is a valuation
of the function field of every model.

* Log discrepancies do not decrease: `a(ξ; M_n, Θ^{M_n}) ≤ a(ξ; M_{n+1}, Θ^{M_{n+1}})`. The move
  from `M_n` to `M_{n+1}` is a coefficient decrease `(Y_i, Θ_i) ⇝ (Y_i, Θ_i')`, which only lowers
  the boundary; or a flip `V_k → T_k ← V_{k+1}` of a bridge, possibly followed by the
  identification of the end of the bridge with the next junction; or, for a bridge without
  steps, the identification of the decreased pair with the next junction. In the last two cases
  the comparison is a negativity argument on a smooth common model `W`, over the base, of a
  divisor realizing `ξ` and of the target: `u^*(K + Θ) - r^*(K' + Θ')` is exceptional over the
  target and minus it is nef over the target, so it is effective, and its coefficient along the
  divisor of `ξ` is the difference of the two log discrepancies.
* Hence boundary coefficients do not increase: every model is `ℚ`-factorial, so the coefficient
  of `Θ^M` at the centre `Q` of `ord_P`, `P` a prime divisor of `Y_0`, is `1 - a(ord_P; M, Θ^M)`.
* Hence a varying label `S_h`, one whose coefficients `b_h^{(i)}` at the junctions are not
  eventually constant, has `b_h^{(i)} > 0` for every `i`: the coefficients are nonnegative and
  nonincreasing, so if one vanished all later ones would, and the label would be fixed.

## Main results

* `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.le_of_isValuationLogDiscrepancy_succ`: the
  log discrepancy of a valuation on the `n`-th model is at most that on the `(n + 1)`-st.
* `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.coeff_modelBoundary_le_of_le`: if `n ≤ m`,
  the coefficient of `Θ^{M_m}` at the centre of `ord_P` is at most that of `Θ^{M_n}`.
* `TerminalChain.IsVaryingLabel.pos_of_isJunctionLabelCoefficient`, in the namespace
  `MMP.Fourfold.StabilizedSmallKltTail`: a varying label has positive coefficient at every
  junction.

## Implementation notes

* Log discrepancies of valuations are the predicate `MMP.Fourfold.IsValuationLogDiscrepancy`, so
  the inequality is stated for every value `a` of `a(ξ; M_n, Θ^{M_n})` and every value `a'` of
  `a(ξ; M_{n+1}, Θ^{M_{n+1}})`. A valuation having such a value is realized by a divisor over the
  model, hence is a normalized divisorial valuation.
* The incarnation of `ξ` on a model is recorded as in
  `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsLabelCentre`: a valuation `v` of the
  function field of a junction `Y_i` is `ξ` when `v`, regarded in `k(X_i)` through `p_i`, is `ξ`
  carried to `k(X_i)` (`MMP.Fourfold.StepSequence.Corresponds`); a valuation `v` of the function
  field of the model `V_k` of the `i`-th bridge is `ξ` when `v`, regarded in `k(Z_i)` through
  `π_k : V_k ⟶ Z_i`, is `ξ` carried to `k(Z_i)` through `k(X_i)` and `f_i`. Centres of `ord_P`
  are prime divisors whose valuation is so identified; by
  `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.primeDivisorEquivModel` the centre
  exists and is unique on every model.
* The label coefficient is the predicate
  `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsJunctionLabelCoefficient`; the statement
  is that every value of it is positive.

## References

* [OpenAI, *Termination for projective log canonical fourfolds with rational boundary*][oai4]
-/

@[expose] public section

namespace MMP.Fourfold

universe u

open CategoryTheory AlgebraicGeometry MMP.Mori
open scoped WithZero

section CommonModel

open MMP.Flips

/-! ### A common smooth model of two models -/

/-- **A smooth common model with projective maps.** Over a field of characteristic zero, two
proper birational morphisms `f₁ : X₁ ⟶ S`, `f₂ : X₂ ⟶ S` from normal varieties are dominated by
a smooth variety `W ⟶ S` through projective birational morphisms `g₁ : W ⟶ X₁`, `g₂ : W ⟶ X₂`. -/
private theorem exists_isSmoothScheme_common_model {k : Type u} [Field k] [CharZero k]
    {S X₁ X₂ : Scheme.{u}} (sS : S ⟶ Spec (.of k)) (f₁ : X₁ ⟶ S) [IsProper f₁]
    (hf₁ : IsBirationalMorphism f₁) (hX₁ : IsNormalVariety k (f₁ ≫ sS)) (f₂ : X₂ ⟶ S)
    [IsProper f₂] (hf₂ : IsBirationalMorphism f₂) (hX₂ : IsNormalVariety k (f₂ ≫ sS)) :
    ∃ (W : Scheme.{u}) (w : W ⟶ S) (g₁ : W ⟶ X₁) (g₂ : W ⟶ X₂),
      IsNormalVariety k (w ≫ sS) ∧ IsSmoothScheme (w ≫ sS) ∧ g₁ ≫ f₁ = w ∧ g₂ ≫ f₂ = w ∧
      IsProjectiveMorphism g₁ ∧ IsProjectiveMorphism g₂ ∧
      IsBirationalMorphism g₁ ∧ IsBirationalMorphism g₂ := by
  obtain ⟨Z, h₁, h₂, hZ, hh₁, hh₂, hb₁, hb₂, hc⟩ :=
    Oai4C1.CommonModel.exists_common_model_two sS f₁ hf₁ hX₁ f₂ hf₂ hX₂
  haveI : AlgebraicGeometry.IsVariety k (h₁ ≫ f₁ ≫ sS) := hZ.1
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  obtain ⟨W, p, n, i, hi, hip, hWv, hWs, hpp, hpb⟩ :=
    Oai4C1.CommonModel.exists_isImmersion_isSmoothScheme (h₁ ≫ f₁ ≫ sS)
  haveI : IsSeparated (f₁ ≫ sS) := hX₁.1.toIsSeparated
  haveI : IsSeparated (f₂ ≫ sS) := hX₂.1.toIsSeparated
  refine ⟨W, p ≫ h₁ ≫ f₁, p ≫ h₁, p ≫ h₂, ?_, by simpa using hWs, Category.assoc _ _ _,
    by rw [Category.assoc, hc],
    Oai4C1.CommonModel.isProjectiveMorphism_of_isImmersion i (p ≫ h₁) (f₁ ≫ sS) (by simp [hip]),
    Oai4C1.CommonModel.isProjectiveMorphism_of_isImmersion i (p ≫ h₂) (f₂ ≫ sS)
      (by simp [hip, reassoc_of% hc]),
    Oai4C1.CommonModel.isBirationalMorphism_comp hpb hb₁,
    Oai4C1.CommonModel.isBirationalMorphism_comp hpb hb₂⟩
  simp only [Category.assoc]
  exact ⟨hWv, (MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hWs).2⟩

end CommonModel

section Comparison

/-! ### Relative nefness of a difference of pull-backs -/

/-- **`-E` is relatively nef.** Let `q : W ⟶ Y`, `r : W ⟶ V` be proper morphisms with
`q ≫ h = r ≫ g`, `D_Y` a `ℚ`-Cartier `ℚ`-divisor on `Y` and `D_V` a `ℚ`-divisor on `V` with a
`g`-ample multiple. Then `r^* D_V - q^* D_Y` is `q`-nef: on a curve contracted by `q`, `q^* D_Y`
has degree zero, and `r^* D_V` has nonnegative degree, the curve being contracted by `r ≫ g`. -/
private theorem isRelativelyNef_neg_sub_of_isPullback {W V Y T : Scheme.{0}} [IsIntegral W]
    [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace V] [IsLocallyNoetherian V]
    [IsNormal V] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y] {sW : W ⟶ Spec (.of ℂ)}
    [QuasiCompact sW] {sV : V ⟶ Spec (.of ℂ)} [IsSeparated sV] [LocallyOfFiniteType sV]
    {sY : Y ⟶ Spec (.of ℂ)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    {q : W ⟶ Y} [IsDominant q] (hq : q ≫ sY = sW) {r : W ⟶ V} [IsProper r] (hr : r ≫ sV = sW)
    {h : Y ⟶ T} {g : V ⟶ T} (hcomp : q ≫ h = r ≫ g) {DY : QDivisor Y} (hDY : DY.IsQCartier)
    [QuasiCompact sV] {DV : QDivisor V} (hDV : DV.IsQCartier)
    (hamp : DV.HasRelativelyAmpleMultiple g ∨ Function.Injective g)
    {hA₀ : ∀ Z : irreducibleComponents W, q (componentGenericPoint W Z) ∉ DY.supp}
    {hR₀ : ∀ Z : irreducibleComponents W, r (componentGenericPoint W Z) ∉ DV.supp}
    {A R : QDivisor W} (hA : DY.IsPullback q hA₀ A) (hR : DV.IsPullback r hR₀ R) :
    (-(A - R)).IsRelativelyNef sW q := by
  have hRq := hR.isQCartier hDV
  have hnAq := Oai4C1.isQCartier_neg (hA.isQCartier hDY)
  rw [show -(A - R) = R + -A by abel]
  refine QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sW (hRq.add hnAq) fun C hC => ?_
  rw [QDivisor.intersectionNumber_add' ℂ sW C.ι C.dim_le _ _ hRq hnAq]
  have hA0 := (Oai4C1.intersectionNumber_isPullback_eq_zero q hq (Oai4C1.isQCartier_neg hDY)
    (Oai4C1.isPullback_neg hA
      (MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' _ _))
    C hC).ge
  have hgC : ∀ x ∈ closure ({C.point} : Set W), g (r x) = g (r C.point) := fun x hx => by
    have h1 := congrArg (fun φ : W ⟶ T => φ x) hcomp
    have h2 := congrArg (fun φ : W ⟶ T => φ C.point) hcomp
    simp only [Scheme.Hom.comp_apply] at h1 h2
    rw [← h1, ← h2, hC x hx]
  rcases hamp with hamp | hinj
  · refine add_nonneg
      (Oai4C1.intersectionNumber_nonneg_of_isPullback r hr hamp hR hRq C fun x hx => ?_) hA0
    simpa only [Scheme.Hom.comp_apply] using hgC x hx
  · exact add_nonneg (Oai4C1.intersectionNumber_isPullback_eq_zero r hr hDV hR C
      fun x hx => hinj (hgC x hx)).ge hA0

open MMP.Positivity

/-! ### The negativity lemma for exceptional `ℚ`-divisors -/

/-- **The negativity lemma for exceptional `ℚ`-divisors.** Let `f : Y ⟶ X` be a projective
birational morphism of normal varieties over a field of characteristic zero and `B` a `ℚ`-divisor
on `Y` whose coefficient vanishes along every prime divisor with a transform on `X`, so that
`f_* B = 0`. If `-B` is `f`-nef, then `B` is effective. -/
private theorem isEffective_of_isRelativelyNef_neg_of_isExceptional (k : Type u) [Field k]
    [CharZero k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    [QuasiCompact sY] [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y]
    (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY) (f : Y ⟶ X) (hf : f ≫ sX = sY)
    (hfp : IsProjectiveMorphism f) (hfb : IsBirationalMorphism f) {B : QDivisor Y}
    (hnef : (-B).IsRelativelyNef sY f)
    (hB : ∀ P Q, RationalMap.transformPrimeDivisor (X := Y) f.toRationalMap P = some Q → B P = 0) :
    B.IsEffective := by
  have hnefR : MMP.Flips.IsRelativelyNef k sY f (-QDivisor.toRDivisor B) := by
    simpa using Oai4C1.Negativity.isRelativelyNef_toRDivisor (k := k) hnef
  have hBc := Oai4C1.Negativity.isCartierCombination_neg
    (Oai4C1.Negativity.isCartierCombination_of_isRelativelyNef hnefR)
  rw [neg_neg] at hBc
  have h := MMP.Flips.isEffective_of_isRelativelyNef_neg_of_isEffective_transformDivisor k sX sY
    hX hY f hf hfp hfb hBc hnefR (by
      rw [RationalMap.transformDivisor, mapPrimeDivisors_eq_zero_of_forall _ fun P Q hPQ =>
        show ((B P : ℚ) : ℝ) = 0 by rw [hB P Q hPQ, Rat.cast_zero]]
      exact DivisorWithCoeffs.isEffective_zero)
  exact fun P => by exact_mod_cast (QDivisor.coeff_toRDivisor B P ▸ h P)

/-! ### Log discrepancies across a small modification over a base -/

/-- **Log discrepancies do not decrease across a small modification.** Let `f⁻ : X⁻ ⟶ Z` be a
proper birational morphism and `f⁺ : X⁺ ⟶ Z` a proper birational morphism which is an
isomorphism at the generic point of every prime divisor of `X⁺`, of normal complex varieties,
with `Z` projective and `X⁺` a `ℚ`-factorial fourfold. Let `K` be a canonical divisor of `X⁻`,
`B` a `ℚ`-divisor with `K + B` `ℚ`-Cartier and `-(K + B)` `f⁻`-ample (or `f⁻` injective), and
`B'` the `ℚ`-divisor on `X⁺` with the coefficients of `B` along the prime divisors mapping to the
same point of `Z`. For valuations `η`, `η'` of `k(X⁻)`, `k(X⁺)` with the same restriction to
`k(Z)`, `a(η; X⁻, B) ≤ a(η'; X⁺, B')`.

On a smooth model `W` of a divisor realizing `η` and of `X⁺` over `Z`, with `u : W ⟶ X⁻`,
`r : W ⟶ X⁺` and a compatible canonical divisor `K_W`, the divisor
`u^*(K + B) - r^*(K' + B')` is `r`-exceptional and its negative is `r`-nef, so it is effective by
the negativity lemma; its coefficient along the prime divisor of `η` is `a' - a`. -/
private theorem le_of_comap_eq {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm]
    [IsLocallyNoetherian Xm] [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp]
    [IsLocallyNoetherian Xp] [IsNormal Xp] [IsIntegral Z]
    {sXm : Xm ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} [IsDominant fm] [IsDominant fp]
    (hZ : IsNormalVariety ℂ sZ) (hZp : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hXi : IsNormalVariety ℂ sXm) (hX1 : IsNormalVariety ℂ sXp)
    (hfm : fm ≫ sZ = sXm) (hfp : fp ≫ sZ = sXp) [IsProper fm] [IsProper fp]
    (hbf : IsBirationalMorphism fm) (hbfp : IsBirationalMorphism fp)
    (hco : ∀ P₁ : MMP.Mori.PrimeDivisor Xp, Order.coheight (fp P₁.genericPoint) = 1)
    (hdim : topologicalKrullDim Xp = 4)
    {K : Divisor Xm} (hTKi : K.IsCanonicalDivisor sXm 4) {B : QDivisor Xm}
    (hXiQ : (Divisor.toQDivisor K + B).IsQCartier)
    (hamp : (-(Divisor.toQDivisor K + B)).HasRelativelyAmpleMultiple fm ∨ Function.Injective fm)
    (hQ : IsQFactorial sXp) {B' : QDivisor Xp}
    (hB : ∀ (P₀ : MMP.Mori.PrimeDivisor Xm) (P₁ : MMP.Mori.PrimeDivisor Xp),
      fm P₀.genericPoint = fp P₁.genericPoint → B' P₁ = B P₀)
    {η : Valuation Xm.functionField ℤᵐ⁰}
    {η' : Valuation Xp.functionField ℤᵐ⁰}
    (hη : η'.comap (functionFieldMap fp) = η.comap (functionFieldMap fm)) {a a' : ℝ}
    (ha : IsValuationLogDiscrepancy sXm B η a) (ha' : IsValuationLogDiscrepancy sXp B' η' a') :
    a ≤ a' := by
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsSeparated sZ := hZ.1.toIsSeparated
  haveI : IsSeparated sXm := hXi.1.toIsSeparated
  haveI : IsSeparated sXp := hX1.1.toIsSeparated
  haveI : LocallyOfFiniteType sXm := hXi.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sXp := hX1.1.toLocallyOfFiniteType
  haveI : QuasiCompact sXp := hX1.1.toQuasiCompact
  haveI : QuasiCompact sXm := hXi.1.toQuasiCompact
  obtain ⟨n, D, hDp, hDv, hDlog⟩ := ha
  obtain ⟨n', D', -, hD'v, hD'log⟩ := ha'
  -- a canonical divisor of `X⁺`, read off the log discrepancy over it
  obtain ⟨K₁, hTK1⟩ : ∃ K₁ : Divisor Xp, K₁.IsCanonicalDivisor sXp 4 := by
    obtain ⟨-, -, -, -, ⟨K₁, hK₁, -⟩, -⟩ := hD'log
    have h4 := hK₁.topologicalKrullDim_eq
    rw [hdim] at h4
    obtain rfl : n' = 4 := by exact_mod_cast h4.symm
    exact ⟨K₁, hK₁⟩
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  haveI := hDp
  have hDn : IsNormalVariety ℂ ((D.f ≫ fm) ≫ sZ) := by
    rw [Category.assoc, hfm]; exact D.isNormalVariety
  have hDb : IsBirationalMorphism (D.f ≫ fm) :=
    Oai4C1.CommonModel.isBirationalMorphism_comp
      D.isBirationalMorphism hbf
  -- a smooth `W` over `Z` with projective birational morphisms to `D.Y` and to `X⁺`
  obtain ⟨W, w, q, r, hWn, hWs, hq, hr, hqp, hrp, hqb, hrb⟩ :=
    exists_isSmoothScheme_common_model
      sZ (D.f ≫ fm) hDb hDn fp hbfp (by rw [hfp]; exact hX1)
  haveI : IsIntegral W := hWn.1.toIsIntegral
  haveI : IsNormal W := hWn.2
  haveI : LocallyOfFiniteType (w ≫ sZ) := hWn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (w ≫ sZ)
  haveI : QuasiCompact (w ≫ sZ) := hWn.1.toQuasiCompact
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (w ≫ sZ)
  haveI : IsProper q := isProper_of_isProjectiveMorphism _ hqp
  haveI : IsProper r := isProper_of_isProjectiveMorphism _ hrp
  haveI : IsProper sZ := isProper_of_isProjectiveMorphism _ hZp.isProjective
  haveI : IsProper (w ≫ sZ) := by rw [← hr]; infer_instance
  haveI := hqb.isDominant
  haveI := hrb.isDominant
  haveI : IsDominant w := by rw [← hr]; infer_instance
  set u : W ⟶ Xm := q ≫ D.f with hudef
  have hub : IsBirationalMorphism u :=
    Oai4C1.CommonModel.isBirationalMorphism_comp
      hqb D.isBirationalMorphism
  haveI : IsProper u := by rw [hudef]; infer_instance
  haveI := hub.isDominant
  have hcomp : r ≫ fp = u ≫ fm := by rw [hr, ← hq, hudef, Category.assoc]
  have hus : u ≫ sXm = w ≫ sZ := by
    rw [← hfm, ← Category.assoc, ← hcomp, hr]
  have hrs : r ≫ sXp = w ≫ sZ := by
    rw [← hfp, ← Category.assoc, hr]
  have hWnu : IsNormalVariety ℂ (u ≫ sXm) := by rw [hus]; exact hWn
  have hWnr : IsNormalVariety ℂ (r ≫ sXp) := by rw [hrs]; exact hWn
  haveI : LocallyOfFiniteType (u ≫ sXm) := hWnu.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (r ≫ sXp) := hWnr.1.toLocallyOfFiniteType
  haveI : QuasiCompact (r ≫ sXp) := hWnr.1.toQuasiCompact
  -- canonical divisors: `K_W` with `u_* K_W = K`, and `K' = r_* K_W` on `X⁺`
  have hdimW : topologicalKrullDim W = ((4 : ℕ) : WithBot ℕ∞) := by
    haveI : MMP.Mori.IsVariety ℂ (w ≫ sZ) := hWn.1
    haveI : MMP.Mori.IsVariety ℂ sXp := hX1.1
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sXp
      (w ≫ sZ) hrb, hdim]
    rfl
  haveI : MMP.Mori.IsVariety ℂ (w ≫ sZ) := hWn.1
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (w ≫ sZ) hWs hdimW
  obtain ⟨KW, hKW, hKWu⟩ := Oai4C1.Main.exists_isCanonicalDivisor_transformDivisor_eq hXi hWnu hub
    hTKi (K₀ := K₀) (by rw [hus]; exact hK₀)
  have hKWr : KW.IsCanonicalDivisor (r ≫ sXp) 4 := by rw [hrs, ← hus]; exact hKW
  have hK'c := Oai4C1.Main.isCanonicalDivisor_transformDivisor hX1 hWnr hrb hTK1 hKWr
  set K' : Divisor Xp := RationalMap.transformDivisor (X := W) r.toRationalMap KW
    with hK'def
  have hXQ : (Divisor.toQDivisor K' + B').IsQCartier := isQCartier_of_isQFactorial sXp hQ _
  -- the pull-backs `A = u^*(K + B)` and `R = r^*(K' + B')`
  have hA₀ : ∀ Z : irreducibleComponents W,
      u (componentGenericPoint W Z) ∉ (Divisor.toQDivisor K + B).supp :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' _ _
  have hR₀ : ∀ Z : irreducibleComponents W,
      r (componentGenericPoint W Z) ∉ (Divisor.toQDivisor K' + B').supp :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' _ _
  have hA := QDivisor.isPullback_pullback hXiQ hA₀
  have hR := QDivisor.isPullback_pullback hXQ hR₀
  set A := (Divisor.toQDivisor K + B).pullback hXiQ hA₀
  set R := (Divisor.toQDivisor K' + B').pullback hXQ hR₀
  haveI := isSeparated_toTerminal_of_isNormalVariety hX1
  haveI := isSeparated_toTerminal_of_isNormalVariety hXi
  haveI := isSeparated_toTerminal_of_isNormalVariety hZ
  haveI : IsSeparated u := IsSeparated.of_comp u sXm
  haveI : IsSeparated r := IsSeparated.of_comp r sXp
  -- `A - R` is `r`-exceptional: the coefficients agree along non-exceptional prime divisors
  have hexc : ∀ P P₁, RationalMap.transformPrimeDivisor (X := W) r.toRationalMap P = some P₁ →
      (A - R) P = 0 := by
    intro P P₁ hP₁
    have hrP : r P.genericPoint = P₁.genericPoint :=
      (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff r P P₁).mp hP₁
    have hζ : Order.coheight (fp P₁.genericPoint) = 1 := hco P₁
    set Q : MMP.Mori.PrimeDivisor Z := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hζ
    have hQ : fp P₁.genericPoint = Q.genericPoint :=
      (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hζ).symm
    have hzQ : fm (u P.genericPoint) = Q.genericPoint := by
      have := congrArg (fun g : W ⟶ Z => g P.genericPoint) hcomp
      simp only [Scheme.Hom.comp_apply] at this
      rw [← this, hrP, hQ]
    obtain ⟨P₀, hP₀, -⟩ :=
      Oai4C1.BridgeComparison.exists_primeDivisor_of_map_eq_genericPoint hbf hzQ
    have huP : u P.genericPoint = P₀.genericPoint := hP₀.symm
    have hfP₀ : fm P₀.genericPoint = Q.genericPoint := by rw [hP₀]; exact hzQ
    haveI := isIso_stalkMap_of_map_eq_genericPoint hub huP
    haveI := isIso_stalkMap_of_map_eq_genericPoint hrb hrP
    rw [Finsupp.sub_apply, coeff_eq_of_isPullback_qDivisor P P₀ huP hXiQ hA,
      coeff_eq_of_isPullback_qDivisor P P₁ hrP hXQ hR]
    change ((K P₀ : ℤ) : ℚ) + B P₀ - (((K' P₁ : ℤ) : ℚ) + B' P₁) = 0
    rw [← hKWu, hK'def, Oai4C1.transformDivisor_apply_of_map_genericPoint hub huP KW,
      Oai4C1.transformDivisor_apply_of_map_genericPoint hrb hrP KW, hB P₀ P₁ (hfP₀.trans hQ.symm),
      sub_self]
  -- `-(A - R)` is `r`-nef: `R` is trivial on `r`-contracted curves and `-A` is nonnegative on
  -- them
  have hnef' := isRelativelyNef_neg_sub_of_isPullback (sW := r ≫ sXp) (q := r) (r := u)
    rfl (hus.trans hrs.symm) hcomp (Oai4C1.isQCartier_neg hXQ) (Oai4C1.isQCartier_neg hXiQ) hamp
    (Oai4C1.isPullback_neg hR
      (MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' _ _))
    (Oai4C1.isPullback_neg hA
      (MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' _ _))
  have hnef : (-(A - R)).IsRelativelyNef (r ≫ sXp) r := by
    have e : -(-R - -A) = -(A - R) := by abel
    rwa [e] at hnef'
  -- the negativity lemma: `A - R ≥ 0`
  have heff := isEffective_of_isRelativelyNef_neg_of_isExceptional ℂ sXp
    (r ≫ sXp) hX1 hWnr r rfl hrp hrb hnef hexc
  -- the prime divisor `P` of `W` over `D.E`, which realizes `η` and `η'`
  have hDn' : IsNormalVariety ℂ (D.f ≫ sXm) := D.isNormalVariety
  have hWnq : IsNormalVariety ℂ (q ≫ D.f ≫ sXm) := by
    rw [← Category.assoc]; exact hWnu
  obtain ⟨P, hqP, hiso, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hDn' hWnq hqb D.E
  haveI := hiso
  have hv : D.valuation = (⟨W, u, hWnu, hub, P⟩ : DivisorOver ℂ sXm).valuation := by
    refine Valuation.ext fun t => ?_
    change D.E.divisorialValuation (functionFieldMap D.f t) =
      P.divisorialValuation (functionFieldMap u t)
    rw [← Oai4C1.functionFieldMap_comp_apply q D.f (c := u) rfl]
    exact (congrArg (fun v => v (functionFieldMap D.f t))
      (Oai4C1.valuationOver_eq_of_isIso q P D.E hqP)).symm
  have hv' : D'.valuation = (⟨W, r, hWnr, hrb, P⟩ : DivisorOver ℂ sXp).valuation := by
    rw [hD'v]
    refine Oai4C1.valuation_eq_of_comap_eq hbfp.functionFieldMap_bijective.2 (hη.trans ?_)
    rw [← hDv, hv]
    refine Valuation.ext fun t => ?_
    rw [Valuation.comap_apply, Valuation.comap_apply]
    change P.divisorialValuation (functionFieldMap u (functionFieldMap fm t)) =
      P.divisorialValuation (functionFieldMap r (functionFieldMap fp t))
    rw [Oai4C1.functionFieldMap_comp_apply u fm (c := w) (by rw [← hcomp, hr]),
      Oai4C1.functionFieldMap_comp_apply r fp (c := w) hr]
  -- reading the coefficients of `A` and `R` along `P`
  have hAP := Oai4C1.BridgeComparison.coeff_isPullback_eq_of_isLogDiscrepancy hXi hTKi hXiQ hub
    hWnu hKW hKWu hA P hDlog hv
  have hRP := Oai4C1.BridgeComparison.coeff_isPullback_eq_of_isLogDiscrepancy hX1 hK'c hXQ hrb
    hWnr hKWr rfl hR P hD'log hv'
  have h0 : 0 ≤ (A - R) P := heff P
  rw [Finsupp.sub_apply] at h0
  have h0' : (0 : ℝ) ≤ ((A P : ℚ) : ℝ) - ((R P : ℚ) : ℝ) := by exact_mod_cast h0
  linarith

end Comparison

namespace StabilizedSmallKltTail.TerminalChain

/-! ### Function fields of the models of a bridge -/

section Chain

/-- Restricting a valuation along a composite of dominant morphisms is restricting twice. -/
private theorem comap_functionFieldMap_comp {A B C : Scheme.{0}} [IsIntegral A] [IsIntegral B]
    [IsIntegral C] (a : A ⟶ B) (b : B ⟶ C) [IsDominant a] [IsDominant b] {c : A ⟶ C}
    [IsDominant c] (hc : a ≫ b = c) (v : Valuation A.functionField ℤᵐ⁰) :
    v.comap (functionFieldMap c) = (v.comap (functionFieldMap a)).comap (functionFieldMap b) :=
  Valuation.ext fun t => by
    rw [Valuation.comap_apply, Valuation.comap_apply, Valuation.comap_apply,
      Oai4C1.functionFieldMap_comp_apply a b hc]

/-- If `a ≫ b` induces a surjection of function fields, so does `b`. -/
private theorem surjective_functionFieldMap_of_comp {A B C : Scheme.{0}} [IsIntegral A]
    [IsIntegral B] [IsIntegral C] (a : A ⟶ B) (b : B ⟶ C) [IsDominant a] [IsDominant b]
    {c : A ⟶ C} [IsDominant c] (hc : a ≫ b = c) (h : Function.Surjective (functionFieldMap c)) :
    Function.Surjective (functionFieldMap b) := fun y => by
  obtain ⟨x, hx⟩ := h (functionFieldMap a y)
  exact ⟨x, (functionFieldMap a).injective (by rw [Oai4C1.functionFieldMap_comp_apply a b hc, hx])⟩

/-- A composite of dominant morphisms inducing surjections of function fields induces one. -/
private theorem surjective_functionFieldMap_comp {A B C : Scheme.{0}} [IsIntegral A]
    [IsIntegral B] [IsIntegral C] (a : A ⟶ B) (b : B ⟶ C) [IsDominant a] [IsDominant b]
    {c : A ⟶ C} [IsDominant c] (hc : a ≫ b = c) (ha : Function.Surjective (functionFieldMap a))
    (hb : Function.Surjective (functionFieldMap b)) : Function.Surjective (functionFieldMap c) :=
  fun z => by
    obtain ⟨y, rfl⟩ := ha z
    obtain ⟨x, rfl⟩ := hb y
    exact ⟨x, (Oai4C1.functionFieldMap_comp_apply a b hc x).symm⟩

/-- Along an isomorphism the inverse transform of a divisor has, at `P`, the coefficient of the
prime divisor under `P`. -/
private theorem inverseTransformDivisor_apply_of_isIso {X Y : Scheme.{0}} (g : X ⟶ Y) [IsIso g]
    {P : MMP.Mori.PrimeDivisor X} {Q : MMP.Mori.PrimeDivisor Y}
    (h : g P.genericPoint = Q.genericPoint) {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R Y) : inverseTransformDivisor g D P = D Q :=
  Oai4C1.inverseTransformDivisor_apply_of_map_genericPoint h
    (le_biregularLocus ((isBiregular_top_iff g).mpr inferInstance) trivial) D

/-- At a prime divisor of the target of a small step `f⁻ : X⁻ ⟶ Z ← X⁺ : f⁺`, the strict
transform `(f⁺)⁻¹_* f⁻_* B` has the coefficient of `B` at the prime divisor over the same point
of `Z`. -/
private theorem flipTransform_apply_of_small_of_map_genericPoint {Xm Xp Z : Scheme.{0}}
    [IsIntegral Xm] [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    [IsSeparated (Z ↘ Limits.terminal Scheme)] {fm : Xm ⟶ Z} [IsSeparated fm]
    (hfm : IsBirationalMorphism fm) {fp : Xp ⟶ Z}
    (hfp : 2 ≤ closedsCodimension (exceptionalSet fp)) {P₀ : MMP.Mori.PrimeDivisor Xm}
    {P₁ : MMP.Mori.PrimeDivisor Xp} (h : fm P₀.genericPoint = fp P₁.genericPoint)
    (B : QDivisor Xm) : flipTransform fm fp B P₁ = B P₀ := by
  have hV₁ := Oai4C1.map_genericPoint_mem_biregularLocus hfp P₁
  have hζ : Order.coheight (fp P₁.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus _ hV₁, P₁.coheight_genericPoint]
  set Q : MMP.Mori.PrimeDivisor Z := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hζ
  have hQ : fp P₁.genericPoint = Q.genericPoint :=
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hζ).symm
  simp only [flipTransform, AddMonoidHom.coe_comp, Function.comp_apply]
  rw [Oai4C1.inverseTransformDivisor_apply_of_map_genericPoint hQ (hQ ▸ hV₁),
    Oai4C1.transformDivisor_apply_of_map_genericPoint hfm (h.trans hQ)]

/-- The prime divisors of the target of a small morphism map to points of coheight one. -/
private theorem coheight_map_genericPoint {X Y : Scheme.{0}} {f : X ⟶ Y}
    (hf : 2 ≤ closedsCodimension (exceptionalSet f)) (P : MMP.Mori.PrimeDivisor X) :
    Order.coheight (f P.genericPoint) = 1 := by
  rw [MMP.Positivity.coheight_map_of_mem_biregularLocus _
    (Oai4C1.map_genericPoint_mem_biregularLocus hf P), P.coheight_genericPoint]

/-- A canonical divisor of a normal fourfold has dimension index four. -/
private theorem isCanonicalDivisor_four {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {K : Divisor X} (h : ∃ m : ℕ, K.IsCanonicalDivisor sX m)
    (hdim : topologicalKrullDim X = 4) : K.IsCanonicalDivisor sX 4 := by
  obtain ⟨m, hm⟩ := h
  have h4 := hm.topologicalKrullDim_eq
  rw [hdim] at h4
  obtain rfl : m = 4 := by exact_mod_cast h4.symm
  exact hm

/-- A valuation with a log discrepancy over `(X, Δ)` has one over every pair `(X, Δ')`: the
divisor realizing it has a discrepancy over `(X, Δ')`. -/
private theorem exists_isValuationLogDiscrepancy {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {Δ Δ' : QDivisor X}
    (hP : MMP.Mori.IsPair sX Δ') {v : Valuation X.functionField ℤᵐ⁰} {a : ℝ}
    (ha : IsValuationLogDiscrepancy sX Δ v a) : ∃ a', IsValuationLogDiscrepancy sX Δ' v a' := by
  obtain ⟨-, n, K, hK, -⟩ := id hP
  obtain ⟨-, D, hDp, hDv, -⟩ := ha
  obtain ⟨b, hb⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK D
  exact ⟨_, n, D, hDp, hDv, MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hb hDp⟩

variable {T : StabilizedSmallKltTail}

/-- The valuation of `k(X_i)` corresponding to a valuation of `k(X_0)` is unique. -/
private theorem corresponds_unique {ξ : Valuation (T.X 0).functionField ℤᵐ⁰} :
    ∀ {i : ℕ} {w w' : Valuation (T.X i).functionField ℤᵐ⁰},
      T.Corresponds i ξ w → T.Corresponds i ξ w' → w = w'
  | 0, _, _, h, h' => h.trans h'.symm
  | i + 1, _, _, ⟨ζ, hζ, h⟩, ⟨ζ', hζ', h'⟩ => by
    obtain rfl := corresponds_unique hζ hζ'
    haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_plus.isDominant
    exact Oai4C1.valuation_eq_of_comap_eq
      (T.isFourfoldStepDiagram i).isBirationalMorphism_plus.functionFieldMap_bijective.2
      (h.trans h'.symm)

variable (C : TerminalChain T)

/-- The morphisms `π_k : V_k ⟶ Z_i` of a bridge are dominant and induce isomorphisms of
function fields. -/
private theorem isDominant_toBase (i : ℕ) :
    ∀ k ≤ (C.bridge i).P.m, ∃ _ : IsDominant ((C.bridge i).P.toBase k),
      haveI := (T.isFourfoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
      Function.Surjective (functionFieldMap ((C.bridge i).P.toBase k))
  | 0, _ => by
    haveI := (T.isFourfoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
    have hb := Oai4C1.CommonModel.isBirationalMorphism_comp
      (C.junction i).isBirationalMorphism (T.isFourfoldStepDiagram i).isBirationalMorphism_minus
    haveI := hb.isDominant
    exact ⟨hb.isDominant, hb.functionFieldMap_bijective.2⟩
  | k + 1, hk => by
    haveI := (T.isFourfoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
    obtain ⟨hd, hs⟩ := isDominant_toBase i k (Nat.le_of_succ_le hk)
    have hS := (C.bridge i).P.isFourfoldStepDiagram k hk
    haveI := hS.isNormalVariety_target.1.toIsIntegral
    haveI : IsDominant ((C.bridge i).P.g k) := hS.isBirationalMorphism_minus.isDominant
    haveI hgp : IsDominant ((C.bridge i).P.gp k) := hS.isBirationalMorphism_plus.isDominant
    have he := (C.bridge i).P.modelMap_eq k hk
    haveI : IsDominant ((C.bridge i).P.h k) := by
      haveI : IsDominant ((C.bridge i).P.g k ≫ (C.bridge i).P.h k) := by
        rw [← he]; exact hd
      exact IsDominant.of_comp ((C.bridge i).P.g k) _
    have hh := surjective_functionFieldMap_of_comp _ _ he.symm hs
    have hp := (C.bridge i).P.πY_eq k hk
    haveI : IsDominant ((C.bridge i).P.toBase (k + 1)) := by
      change IsDominant ((C.bridge i).P.πY k)
      rw [hp]; infer_instance
    haveI : IsDominant (X := (C.bridge i).P.model (k + 1)) ((C.bridge i).P.gp k) := hgp
    exact ⟨inferInstance, surjective_functionFieldMap_comp (A := (C.bridge i).P.model (k + 1))
      ((C.bridge i).P.gp k) _ hp.symm
      hS.isBirationalMorphism_plus.functionFieldMap_bijective.2 hh⟩

/-- `v` is the valuation `ξ` of `k(X_0)` on the model `x` of the chain: on a junction `Y_i`, its
restriction to `k(X_i)` corresponds to `ξ`; on a model `V_k` of the `i`-th bridge, its
restriction to `k(Z_i)` is that of the valuation of `k(X_i)` corresponding to `ξ`. -/
def IsIncarnation (ξ : Valuation (T.X 0).functionField ℤᵐ⁰) :
    ∀ x : C.ModelIndex, Valuation (C.model x).functionField ℤᵐ⁰ → Prop
  | ⟨i, none⟩, (v : Valuation (C.junction i).Y.functionField ℤᵐ⁰) =>
    haveI := (C.junction i).isBirationalMorphism.isDominant
    ∃ w, T.Corresponds i ξ w ∧ v.comap (functionFieldMap (C.junction i).p) = w
  | ⟨i, some k⟩,
      (v : Valuation ((C.bridge i).P.model k).functionField ℤᵐ⁰) =>
    haveI := (T.isFourfoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
    haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_minus.isDominant
    ∃ w, T.Corresponds i ξ w ∧
      ∃ _ : IsDominant ((C.bridge i).P.toBase k),
        v.comap (functionFieldMap ((C.bridge i).P.toBase k)) = w.comap (functionFieldMap (T.f i))

/-- The pair `(V_k, Θ_k)` of a model of a bridge, `k ≤ m`, is a pair: `V_k` is `ℚ`-factorial and
has a canonical divisor. -/
private theorem isPair_decreased (i : ℕ) :
    MMP.Mori.IsPair (C.junction i).sY (C.bridge i).Θ' := by
  obtain ⟨n, hK⟩ := (C.bridge i).P.isCanonicalDivisor
  exact ⟨(C.junction i).isQFactorial.1, n, _, hK,
    isQCartier_of_isQFactorial _ (C.junction i).isQFactorial _⟩

/-- **The coefficient decrease** `(Y_i, Θ_i) ⇝ (Y_i, Θ_i')`. -/
private theorem le_of_decrease (ξ : Valuation (T.X 0).functionField ℤᵐ⁰)
    (i : ℕ) (v : Valuation (C.junction i).Y.functionField ℤᵐ⁰)
    (v' : Valuation ((C.bridge i).P.model 0).functionField ℤᵐ⁰)
    (hv : IsIncarnation C ξ ⟨i, none⟩ v)
    (hv' : haveI := (T.isFourfoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
      haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_minus.isDominant
      ∃ w, T.Corresponds i ξ w ∧ ∃ _ : IsDominant ((C.bridge i).P.toBase 0),
        v'.comap (functionFieldMap ((C.bridge i).P.toBase 0)) =
          w.comap (functionFieldMap (T.f i)))
    {a a' : ℝ} (ha : IsValuationLogDiscrepancy (C.junction i).sY (C.junction i).Θ v a)
    (ha' : IsValuationLogDiscrepancy ((C.bridge i).P.modelStructure 0)
      ((C.bridge i).P.boundary 0) v' a') : a ≤ a' := by
  haveI := (T.isFourfoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
  haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_minus.isDominant
  haveI := (C.junction i).isBirationalMorphism.isDominant
  obtain ⟨w, hw, hvw⟩ := hv
  obtain ⟨w', hw', _, hvw'⟩ := hv'
  obtain rfl := corresponds_unique hw' hw
  obtain ⟨_, hs⟩ := isDominant_toBase C i 0 (Nat.zero_le _)
  have hvv : v' = v := by
    refine Oai4C1.valuation_eq_of_comap_eq hs (hvw'.trans ?_)
    rw [← hvw]
    exact (comap_functionFieldMap_comp (C.junction i).p (T.f i) rfl v).symm
  subst hvv
  exact (C.bridge i).isDecreasedBoundary.le_of_isValuationLogDiscrepancy ha ha'

/-- **A bridge without steps**: the decreased pair `(Y_i, Θ_i')` is the next junction
`(Y_{i+1}, Θ_{i+1})` through `e : Y_i ≅ Y_{i+1}`. -/
private theorem le_of_end_zero (ξ : Valuation (T.X 0).functionField ℤᵐ⁰)
    (i : ℕ) (e : (C.junction i).Y ≅ (C.junction (i + 1)).Y)
    (he : e.hom ≫ (C.junction (i + 1)).sY = (C.junction i).sY)
    (hΘ : (C.bridge i).Θ' = inverseTransformDivisor e.hom (C.junction (i + 1)).Θ)
    (hπ : (C.junction i).p ≫ T.f i = e.hom ≫ (C.junction (i + 1)).p ≫ T.fp i)
    (v : Valuation (C.junction i).Y.functionField ℤᵐ⁰)
    (v' : Valuation (C.junction (i + 1)).Y.functionField ℤᵐ⁰)
    (hv : IsIncarnation C ξ ⟨i, none⟩ v) (hv' : IsIncarnation C ξ ⟨i + 1, none⟩ v')
    {a a' : ℝ} (ha : IsValuationLogDiscrepancy (C.junction i).sY (C.junction i).Θ v a)
    (ha' : IsValuationLogDiscrepancy (C.junction (i + 1)).sY (C.junction (i + 1)).Θ v' a') :
    a ≤ a' := by
  haveI := (T.isFourfoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
  haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_minus.isDominant
  haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_plus.isDominant
  haveI := (C.junction i).isBirationalMorphism.isDominant
  haveI := (C.junction (i + 1)).isBirationalMorphism.isDominant
  obtain ⟨w, hw, hvw⟩ := hv
  obtain ⟨w', ⟨ζ, hζ, hζw'⟩, hvw'⟩ := hv'
  obtain rfl := corresponds_unique hζ hw
  haveI : IsDominant e.hom := (isBirationalMorphism_of_isIso e.hom).isDominant
  -- the log discrepancy of `v` over the decreased pair
  obtain ⟨b, hb⟩ := exists_isValuationLogDiscrepancy (isPair_decreased C i) ha
  have h1 := (C.bridge i).isDecreasedBoundary.le_of_isValuationLogDiscrepancy ha hb
  -- the identification `e` carries `v` to `v'`
  have hb' := Oai4C1.CommonModel.isBirationalMorphism_comp
    (C.junction (i + 1)).isBirationalMorphism (T.isFourfoldStepDiagram i).isBirationalMorphism_plus
  haveI := hb'.isDominant
  have hev : v.comap (functionFieldMap e.hom) = v' := by
    refine Oai4C1.valuation_eq_of_comap_eq hb'.functionFieldMap_bijective.2 ?_
    calc (v.comap (functionFieldMap e.hom)).comap
          (functionFieldMap ((C.junction (i + 1)).p ≫ T.fp i))
        = v.comap (functionFieldMap (e.hom ≫ (C.junction (i + 1)).p ≫ T.fp i)) :=
          (comap_functionFieldMap_comp e.hom ((C.junction (i + 1)).p ≫ T.fp i) rfl v).symm
      _ = (v.comap (functionFieldMap (C.junction i).p)).comap (functionFieldMap (T.f i)) :=
          comap_functionFieldMap_comp (C.junction i).p (T.f i) hπ v
      _ = (v'.comap (functionFieldMap (C.junction (i + 1)).p)).comap
            (functionFieldMap (T.fp i)) := by
          rw [hvw, hvw']; exact hζw'.symm
      _ = v'.comap (functionFieldMap ((C.junction (i + 1)).p ≫ T.fp i)) :=
          (comap_functionFieldMap_comp (C.junction (i + 1)).p (T.fp i) rfl v').symm
  have hη : v'.comap (functionFieldMap (𝟙 (C.junction (i + 1)).Y)) =
      v.comap (functionFieldMap e.hom) := by
    rw [hev]
    exact Valuation.ext fun t => by rw [Valuation.comap_apply, MMP.Mori.functionFieldMap_id_apply]
  have hJ := (C.junction i).isQFactorial.1
  have hJ' := (C.junction (i + 1)).isQFactorial.1
  have h2 := le_of_comap_eq (fm := e.hom) (fp := 𝟙 (C.junction (i + 1)).Y)
    (sZ := (C.junction (i + 1)).sY)
    (B := (C.bridge i).Θ') hJ'
    (C.junction (i + 1)).isProjectiveVariety hJ hJ' he (Category.id_comp _)
    (isBirationalMorphism_of_isIso _) (isBirationalMorphism_of_isIso _)
    (fun P₁ => P₁.coheight_genericPoint) (C.junction (i + 1)).dim_eq
    (isCanonicalDivisor_four (C.bridge i).P.isCanonicalDivisor (C.junction i).dim_eq)
    (isQCartier_of_isQFactorial _ (C.junction i).isQFactorial _) (Or.inr e.hom.homeomorph.injective)
    (C.junction (i + 1)).isQFactorial (B' := (C.junction (i + 1)).Θ)
    (fun P₀ P₁ h => by
      rw [hΘ]
      exact (inverseTransformDivisor_apply_of_isIso e.hom h _).symm)
    hη hb ha'
  linarith

/-- **A flip of a bridge**, `V_k → T_k ← V_{k+1}` with `k + 1 < m_i`. -/
private theorem le_of_flip (ξ : Valuation (T.X 0).functionField ℤᵐ⁰)
    (i k : ℕ) (hk : k + 1 < (C.bridge i).P.m)
    (v : Valuation ((C.bridge i).P.model k).functionField ℤᵐ⁰)
    (v' : Valuation ((C.bridge i).P.model (k + 1)).functionField ℤᵐ⁰)
    (hv : haveI := (T.isFourfoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
      haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_minus.isDominant
      ∃ w, T.Corresponds i ξ w ∧ ∃ _ : IsDominant ((C.bridge i).P.toBase k),
        v.comap (functionFieldMap ((C.bridge i).P.toBase k)) =
          w.comap (functionFieldMap (T.f i)))
    (hv' : haveI := (T.isFourfoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
      haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_minus.isDominant
      ∃ w, T.Corresponds i ξ w ∧ ∃ _ : IsDominant ((C.bridge i).P.toBase (k + 1)),
        v'.comap (functionFieldMap ((C.bridge i).P.toBase (k + 1))) =
          w.comap (functionFieldMap (T.f i)))
    {a a' : ℝ} (ha : IsValuationLogDiscrepancy ((C.bridge i).P.modelStructure k)
      ((C.bridge i).P.boundary k) v a)
    (ha' : IsValuationLogDiscrepancy ((C.bridge i).P.modelStructure (k + 1))
      ((C.bridge i).P.boundary (k + 1)) v' a') : a ≤ a' := by
  have hk' : k < (C.bridge i).P.m := by omega
  have hS := (C.bridge i).P.isFourfoldStepDiagram k hk'
  haveI := (T.isFourfoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
  haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_minus.isDominant
  haveI := hS.isNormalVariety_target.1.toIsIntegral
  haveI : IsDominant ((C.bridge i).P.g k) := hS.isBirationalMorphism_minus.isDominant
  haveI hgp : IsDominant (X := (C.bridge i).P.model (k + 1)) ((C.bridge i).P.gp k) :=
    hS.isBirationalMorphism_plus.isDominant
  obtain ⟨w, hw, hd, hvw⟩ := hv
  obtain ⟨w', hw', hd', hvw'⟩ := hv'
  obtain rfl := corresponds_unique hw' hw
  obtain ⟨_, hs⟩ := isDominant_toBase C i k hk'.le
  have he := (C.bridge i).P.modelMap_eq k hk'
  have hp := (C.bridge i).P.πY_eq k hk'
  haveI : IsDominant ((C.bridge i).P.h k) := by
    haveI : IsDominant ((C.bridge i).P.g k ≫ (C.bridge i).P.h k) := by rw [← he]; exact hd
    exact IsDominant.of_comp ((C.bridge i).P.g k) _
  have hh := surjective_functionFieldMap_of_comp _ _ he.symm hs
  have hη : v'.comap (functionFieldMap (X := (C.bridge i).P.model (k + 1)) ((C.bridge i).P.gp k)) =
      v.comap (functionFieldMap ((C.bridge i).P.g k)) := by
    refine Oai4C1.valuation_eq_of_comap_eq hh ?_
    calc (v'.comap
          (functionFieldMap (X := (C.bridge i).P.model (k + 1)) ((C.bridge i).P.gp k))).comap
          (functionFieldMap ((C.bridge i).P.h k))
        = v'.comap (functionFieldMap ((C.bridge i).P.toBase (k + 1))) :=
          (comap_functionFieldMap_comp (A := (C.bridge i).P.model (k + 1))
            (c := (C.bridge i).P.toBase (k + 1)) ((C.bridge i).P.gp k) ((C.bridge i).P.h k)
            hp.symm v').symm
      _ = v.comap (functionFieldMap ((C.bridge i).P.toBase k)) := hvw'.trans hvw.symm
      _ = (v.comap (functionFieldMap ((C.bridge i).P.g k))).comap
            (functionFieldMap ((C.bridge i).P.h k)) :=
          comap_functionFieldMap_comp ((C.bridge i).P.g k) ((C.bridge i).P.h k) he.symm v
  have hZ := hS.isNormalVariety_target
  haveI : IsNormal ((C.bridge i).P.T k) := hZ.2
  haveI : LocallyOfFiniteType ((C.bridge i).P.sT k) := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian ((C.bridge i).P.T k) :=
    LocallyOfFiniteType.isLocallyNoetherian ((C.bridge i).P.sT k)
  haveI := isSeparated_toTerminal_of_isNormalVariety hZ
  haveI : IsSeparated ((C.bridge i).P.g k ≫ (C.bridge i).P.sT k) := by
    rw [hS.comp_eq_minus]; exact hS.isNormalVariety_minus.1.toIsSeparated
  haveI : IsSeparated ((C.bridge i).P.g k) :=
    IsSeparated.of_comp ((C.bridge i).P.g k) ((C.bridge i).P.sT k)
  haveI : IsProper ((C.bridge i).P.g k) :=
    isProper_of_isProjectiveMorphism _ hS.isProjectiveMorphism_minus
  haveI : IsProper (X := (C.bridge i).P.model (k + 1)) ((C.bridge i).P.gp k) := hS.isProper_plus
  exact le_of_comap_eq (Xp := (C.bridge i).P.model (k + 1)) (fm := (C.bridge i).P.g k)
    (fp := (C.bridge i).P.gp k) hZ hS.isProjectiveVariety_target
    hS.isNormalVariety_minus hS.isNormalVariety_plus hS.comp_eq_minus hS.comp_eq_plus
    hS.isBirationalMorphism_minus hS.isBirationalMorphism_plus
    (coheight_map_genericPoint hS.isSmallMorphism_plus.two_le_codimension) hS.dim_plus
    (isCanonicalDivisor_four hS.isCanonicalDivisor hS.dim_minus) hS.isQCartier_minus
    (Or.inl hS.hasRelativelyAmpleMultiple_minus) ((C.bridge i).P.isQFactorial (k + 1) hk.le)
    (fun P₀ P₁ h => by
      rw [(C.bridge i).P.boundary_succ_eq_flipTransform hk']
      exact flipTransform_apply_of_small_of_map_genericPoint hS.isBirationalMorphism_minus
        hS.isSmallMorphism_plus.two_le_codimension h _)
    hη ha ha'

/-- **The last flip of a bridge**, `V_k → T_k ← V_{k+1} ≅ Y_{i+1}` with `k + 1 = m_i`. -/
private theorem le_of_flip_end
    (ξ : Valuation (T.X 0).functionField ℤᵐ⁰)
    (i k : ℕ) (hk : k < (C.bridge i).P.m) (e : (C.bridge i).P.Y k ≅ (C.junction (i + 1)).Y)
    (he : e.hom ≫ (C.junction (i + 1)).sY = (C.bridge i).P.sY k)
    (hΘ : (C.bridge i).P.ΘY k = inverseTransformDivisor e.hom (C.junction (i + 1)).Θ)
    (hπ : (C.bridge i).P.πY k = e.hom ≫ (C.junction (i + 1)).p ≫ T.fp i)
    (v : Valuation ((C.bridge i).P.model k).functionField ℤᵐ⁰)
    (v' : Valuation (C.junction (i + 1)).Y.functionField ℤᵐ⁰)
    (hv : haveI := (T.isFourfoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
      haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_minus.isDominant
      ∃ w, T.Corresponds i ξ w ∧ ∃ _ : IsDominant ((C.bridge i).P.toBase k),
        v.comap (functionFieldMap ((C.bridge i).P.toBase k)) =
          w.comap (functionFieldMap (T.f i)))
    (hv' : IsIncarnation C ξ ⟨i + 1, none⟩ v')
    {a a' : ℝ} (ha : IsValuationLogDiscrepancy ((C.bridge i).P.modelStructure k)
      ((C.bridge i).P.boundary k) v a)
    (ha' : IsValuationLogDiscrepancy (C.junction (i + 1)).sY (C.junction (i + 1)).Θ v' a') :
    a ≤ a' := by
  have hS := (C.bridge i).P.isFourfoldStepDiagram k hk
  haveI := (T.isFourfoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
  haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_minus.isDominant
  haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_plus.isDominant
  haveI := (C.junction (i + 1)).isBirationalMorphism.isDominant
  haveI := hS.isNormalVariety_target.1.toIsIntegral
  haveI : IsDominant ((C.bridge i).P.g k) := hS.isBirationalMorphism_minus.isDominant
  haveI hgp : IsDominant ((C.bridge i).P.gp k) := hS.isBirationalMorphism_plus.isDominant
  obtain ⟨w, hw, hd, hvw⟩ := hv
  obtain ⟨w', ⟨ζ, hζ, hζw'⟩, hvw'⟩ := hv'
  obtain rfl := corresponds_unique hζ hw
  obtain ⟨_, hs⟩ := isDominant_toBase C i k hk.le
  have hmk := (C.bridge i).P.modelMap_eq k hk
  have hp := (C.bridge i).P.πY_eq k hk
  haveI : IsDominant ((C.bridge i).P.h k) := by
    haveI : IsDominant ((C.bridge i).P.g k ≫ (C.bridge i).P.h k) := by rw [← hmk]; exact hd
    exact IsDominant.of_comp ((C.bridge i).P.g k) _
  have hh := surjective_functionFieldMap_of_comp _ _ hmk.symm hs
  haveI : IsDominant e.inv := (isBirationalMorphism_of_isIso e.inv).isDominant
  obtain ⟨fp, hfpdef⟩ : ∃ fp : (C.junction (i + 1)).Y ⟶ (C.bridge i).P.T k,
      fp = e.inv ≫ (C.bridge i).P.gp k := ⟨_, rfl⟩
  haveI : IsDominant fp := by rw [hfpdef]; infer_instance
  have hc : fp ≫ (C.bridge i).P.h k = (C.junction (i + 1)).p ≫ T.fp i := by
    rw [hfpdef, Category.assoc, ← hp, hπ, e.inv_hom_id_assoc]
  have hη : v'.comap (functionFieldMap fp) = v.comap (functionFieldMap ((C.bridge i).P.g k)) := by
    refine Oai4C1.valuation_eq_of_comap_eq hh ?_
    calc (v'.comap (functionFieldMap fp)).comap (functionFieldMap ((C.bridge i).P.h k))
        = v'.comap (functionFieldMap ((C.junction (i + 1)).p ≫ T.fp i)) :=
          (comap_functionFieldMap_comp fp ((C.bridge i).P.h k) hc v').symm
      _ = (v'.comap (functionFieldMap (C.junction (i + 1)).p)).comap (functionFieldMap (T.fp i)) :=
          comap_functionFieldMap_comp (C.junction (i + 1)).p (T.fp i) rfl v'
      _ = v.comap (functionFieldMap ((C.bridge i).P.toBase k)) := by rw [hvw', hζw', hvw]
      _ = (v.comap (functionFieldMap ((C.bridge i).P.g k))).comap
            (functionFieldMap ((C.bridge i).P.h k)) :=
          comap_functionFieldMap_comp ((C.bridge i).P.g k) ((C.bridge i).P.h k) hmk.symm v
  have hZ := hS.isNormalVariety_target
  haveI : IsNormal ((C.bridge i).P.T k) := hZ.2
  haveI : LocallyOfFiniteType ((C.bridge i).P.sT k) := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian ((C.bridge i).P.T k) :=
    LocallyOfFiniteType.isLocallyNoetherian ((C.bridge i).P.sT k)
  haveI := isSeparated_toTerminal_of_isNormalVariety hZ
  haveI : IsSeparated ((C.bridge i).P.g k ≫ (C.bridge i).P.sT k) := by
    rw [hS.comp_eq_minus]; exact hS.isNormalVariety_minus.1.toIsSeparated
  haveI : IsSeparated ((C.bridge i).P.g k) :=
    IsSeparated.of_comp ((C.bridge i).P.g k) ((C.bridge i).P.sT k)
  haveI : IsProper ((C.bridge i).P.g k) :=
    isProper_of_isProjectiveMorphism _ hS.isProjectiveMorphism_minus
  haveI : IsProper ((C.bridge i).P.gp k) := hS.isProper_plus
  haveI : IsProper fp := by rw [hfpdef]; infer_instance
  -- the prime divisor of `V_{k+1}` under a prime divisor of `Y_{i+1}`
  have hP' : ∀ P₁ : MMP.Mori.PrimeDivisor (C.junction (i + 1)).Y,
      Order.coheight (e.inv P₁.genericPoint) = 1 := fun P₁ => by
    rw [coheight_eq_of_isOpenImmersion e.inv, P₁.coheight_genericPoint]
  have hJ' := (C.junction (i + 1)).isQFactorial.1
  exact le_of_comap_eq (fm := (C.bridge i).P.g k) (fp := fp) hZ hS.isProjectiveVariety_target
    hS.isNormalVariety_minus hJ' hS.comp_eq_minus
    (by rw [hfpdef, Category.assoc, hS.comp_eq_plus, ← he]; exact e.inv_hom_id_assoc _)
    hS.isBirationalMorphism_minus
    (by
      rw [hfpdef]
      exact Oai4C1.CommonModel.isBirationalMorphism_comp
        (isBirationalMorphism_of_isIso e.inv) hS.isBirationalMorphism_plus)
    (fun P₁ => by
      have hg : (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ (hP' P₁) :
          MMP.Mori.PrimeDivisor ((C.bridge i).P.Y k)).genericPoint = e.inv P₁.genericPoint :=
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
      have h := coheight_map_genericPoint hS.isSmallMorphism_plus.two_le_codimension
        (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ (hP' P₁))
      rw [hfpdef, Scheme.Hom.comp_apply]
      exact (congrArg (fun x => Order.coheight ((C.bridge i).P.gp k x)) hg).symm.trans h)
    (C.junction (i + 1)).dim_eq (isCanonicalDivisor_four hS.isCanonicalDivisor hS.dim_minus)
    hS.isQCartier_minus
    (Or.inl hS.hasRelativelyAmpleMultiple_minus) (C.junction (i + 1)).isQFactorial
    (fun P₀ P₁ h => by
      set P' : MMP.Mori.PrimeDivisor ((C.bridge i).P.Y k) :=
        AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ (hP' P₁)
      have hP'g : P'.genericPoint = e.inv P₁.genericPoint :=
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
      have hPe : e.hom P'.genericPoint = P₁.genericPoint := by
        rw [hP'g, ← Scheme.Hom.comp_apply, e.inv_hom_id]; rfl
      rw [← inverseTransformDivisor_apply_of_isIso e.hom hPe, ← hΘ, (C.bridge i).P.ΘY_eq k hk]
      refine flipTransform_apply_of_small_of_map_genericPoint hS.isBirationalMorphism_minus
        hS.isSmallMorphism_plus.two_le_codimension (h.trans ?_) _
      rw [hP'g, hfpdef, Scheme.Hom.comp_apply])
    hη ha ha'

/-- **One move.** The log discrepancy of `ξ` does not decrease from a model of the chain to the
next one. -/
private theorem le_of_next (ξ : Valuation (T.X 0).functionField ℤᵐ⁰) :
    ∀ (x : C.ModelIndex) (v : Valuation (C.model x).functionField ℤᵐ⁰)
      (v' : Valuation (C.model (C.next x)).functionField ℤᵐ⁰),
      IsIncarnation C ξ x v → IsIncarnation C ξ (C.next x) v' → ∀ {a a' : ℝ},
      IsValuationLogDiscrepancy (C.modelStructure x) (C.modelBoundary x) v a →
      IsValuationLogDiscrepancy (C.modelStructure (C.next x)) (C.modelBoundary (C.next x)) v' a' →
      a ≤ a'
  | ⟨i, none⟩, v => by
    by_cases h : 0 < (C.bridge i).P.m
    · have hx : C.next ⟨i, none⟩ = ⟨i, some ⟨0, h⟩⟩ := by simp only [next, h, ↓reduceDIte]
      rw [hx]
      intro v' hv hv' a a' ha ha'
      exact le_of_decrease C ξ i v v' hv hv' ha ha'
    · have hx : C.next ⟨i, none⟩ = ⟨i + 1, none⟩ := by simp only [next, h, ↓reduceDIte]
      rw [hx]
      intro v' hv hv' a a' ha ha'
      have key : ∀ (m : ℕ) (e : (C.bridge i).P.model m ≅ (C.junction (i + 1)).Y),
          e.hom ≫ (C.junction (i + 1)).sY = (C.bridge i).P.modelStructure m →
          (C.bridge i).P.boundary m = inverseTransformDivisor e.hom (C.junction (i + 1)).Θ →
          (C.bridge i).P.toBase m = e.hom ≫ (C.junction (i + 1)).p ≫ T.fp i → m = 0 →
          a ≤ a' := by
        rintro m e he hΘ hπ rfl
        exact le_of_end_zero C ξ i e he hΘ hπ v v' hv hv' ha ha'
      exact key _ (C.bridge i).e (C.bridge i).comp_sY (C.bridge i).endBoundary_eq
        (C.bridge i).toBase_end_eq (by omega)
  | ⟨i, some k⟩, v => by
    by_cases h : k.1 + 1 < (C.bridge i).P.m
    · have hx : C.next ⟨i, some k⟩ = ⟨i, some ⟨k.1 + 1, h⟩⟩ := by
        simp only [next, h, ↓reduceDIte]
      rw [hx]
      intro v' hv hv' a a' ha ha'
      exact le_of_flip C ξ i k.1 h v v' hv hv' ha ha'
    · have hx : C.next ⟨i, some k⟩ = ⟨i + 1, none⟩ := by simp only [next, h, ↓reduceDIte]
      rw [hx]
      intro v' hv hv' a a' ha ha'
      have key : ∀ (m : ℕ) (e : (C.bridge i).P.model m ≅ (C.junction (i + 1)).Y),
          e.hom ≫ (C.junction (i + 1)).sY = (C.bridge i).P.modelStructure m →
          (C.bridge i).P.boundary m = inverseTransformDivisor e.hom (C.junction (i + 1)).Θ →
          (C.bridge i).P.toBase m = e.hom ≫ (C.junction (i + 1)).p ≫ T.fp i → m = k.1 + 1 →
          a ≤ a' := by
        rintro m e he hΘ hπ rfl
        exact le_of_flip_end C ξ i k.1 k.2 e he hΘ hπ v v' hv hv' ha ha'
      exact key _ (C.bridge i).e (C.bridge i).comp_sY (C.bridge i).endBoundary_eq
        (C.bridge i).toBase_end_eq (by omega)

/-- `le_of_next` for a model `y` with `C.next x = y`. -/
private theorem le_of_next_eq {T : StabilizedSmallKltTail} (C : TerminalChain T)
    (ξ : Valuation (T.X 0).functionField ℤᵐ⁰) (x y : C.ModelIndex)
    (hxy : C.next x = y)
    (v : Valuation (C.model x).functionField ℤᵐ⁰)
    (v' : Valuation (C.model y).functionField ℤᵐ⁰)
    (hv : IsIncarnation C ξ x v) (hv' : IsIncarnation C ξ y v') {a a' : ℝ}
    (ha : IsValuationLogDiscrepancy (C.modelStructure x) (C.modelBoundary x) v a)
    (ha' : IsValuationLogDiscrepancy (C.modelStructure y) (C.modelBoundary y) v' a') :
    a ≤ a' := by
  subst hxy
  exact le_of_next C ξ x v v' hv hv' ha ha'

end Chain

section Statements

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

variable {T : StabilizedSmallKltTail}

/-- **Log discrepancies are nondecreasing along a terminal chain.** Let `ξ` be a valuation of
`k(X_0)`, and `v`, `v'` the valuations of the function fields of the consecutive models
`M_n = C.model (C.modelIndexSeq n)` and `M_{n+1}` that are `ξ` under the identification of
function fields (through `p_i` and `k(X_i)` for a junction `Y_i`, through `π_k : V_k ⟶ Z_i` and
`k(Z_i)` for a model `V_k` of the `i`-th bridge). Then `a(v; M_n, Θ^{M_n}) ≤ a(v'; M_{n+1},
Θ^{M_{n+1}})`. -/
@[mmp "prop_oai4_terminal_chain_f"]
public theorem le_of_isValuationLogDiscrepancy_succ (C : TerminalChain T) (n : ℕ)
    (ξ : Valuation (T.X 0).functionField ℤᵐ⁰)
    (v : Valuation (C.model (C.modelIndexSeq n)).functionField ℤᵐ⁰)
    (v' : Valuation (C.model (C.modelIndexSeq (n + 1))).functionField ℤᵐ⁰)
    (hv : IsIncarnation C ξ (C.modelIndexSeq n) v)
    (hv' : IsIncarnation C ξ (C.modelIndexSeq (n + 1)) v') {a a' : ℝ}
    (ha : IsValuationLogDiscrepancy (C.modelStructure (C.modelIndexSeq n))
      (C.modelBoundary (C.modelIndexSeq n)) v a)
    (ha' : IsValuationLogDiscrepancy (C.modelStructure (C.modelIndexSeq (n + 1)))
      (C.modelBoundary (C.modelIndexSeq (n + 1))) v' a') :
    a ≤ a' :=
  le_of_next_eq C ξ _ _ (Function.iterate_succ_apply' C.next n ⟨0, none⟩).symm v v' hv hv' ha ha'

/-- On a pair `(X, Δ)` over `ℂ`, the log discrepancy of `ord_Q`, `Q` a prime divisor of `X`, is
`1 - coeff_Q Δ`. -/
private theorem isValuationLogDiscrepancy_divisorialValuation {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {Δ : MMP.Mori.QDivisor X}
    (hP : MMP.Mori.IsPair sX Δ) (Q : MMP.Mori.PrimeDivisor X) :
    IsValuationLogDiscrepancy sX Δ Q.divisorialValuation (1 - (Δ.coeff Q : ℝ)) := by
  obtain ⟨hX, n, K, hK, -⟩ := id hP
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK
    (MMP.Mori.DivisorOver.ofPrimeDivisor ℂ hX Q)
  have hneg := ha.eq_neg_coeff_of_ofPrimeDivisor hX
  have h := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy ha
    (inferInstanceAs (IsProper (𝟙 X)))
  refine ⟨n, MMP.Mori.DivisorOver.ofPrimeDivisor ℂ hX Q, inferInstanceAs (IsProper (𝟙 X)), ?_, ?_⟩
  · ext g
    exact congrArg Q.divisorialValuation (MMP.Mori.functionFieldMap_id_apply g)
  · rw [hneg] at h
    convert h using 1
    push_cast
    ring

/-- Every model of a terminal chain is a pair with any boundary: it is `ℚ`-factorial and has a
canonical divisor. -/
private theorem isPair_model (C : TerminalChain T)
    (x : C.ModelIndex) (Δ : MMP.Mori.QDivisor (C.model x)) :
    MMP.Mori.IsPair (C.modelStructure x) Δ := by
  rcases x with ⟨i, _ | k⟩
  · have hQ : IsQFactorial (C.junction i).sY := (C.junction i).isQFactorial
    obtain ⟨n, hK⟩ := (C.bridge i).P.isCanonicalDivisor
    exact ⟨hQ.1, n, _, hK, isQCartier_of_isQFactorial _ hQ _⟩
  · have hQ := (C.bridge i).P.isQFactorial k k.2.le
    obtain ⟨n, hK⟩ := ((C.bridge i).P.isFourfoldStepDiagram k k.2).isCanonicalDivisor
    exact ⟨hQ.1, n, _, hK, isQCartier_of_isQFactorial _ hQ _⟩

/-- **One step.** The coefficient of the boundary at the centre of `ord_P` does not increase from
the model `M_n` to `M_{n+1}`: on both it is `1 - a(ord_P)`, and that log discrepancy does not
decrease (`le_of_isValuationLogDiscrepancy_succ`). -/
private theorem coeff_modelBoundary_succ_le (C : TerminalChain T) (n : ℕ)
    {P : MMP.Mori.PrimeDivisor (C.junction 0).Y}
    {Q : MMP.Mori.PrimeDivisor (C.model (C.modelIndexSeq n))}
    {Q' : MMP.Mori.PrimeDivisor (C.model (C.modelIndexSeq (n + 1)))}
    (hQ : C.IsPrimeDivisorCentre P _ Q) (hQ' : C.IsPrimeDivisorCentre P _ Q') :
    (C.modelBoundary (C.modelIndexSeq (n + 1))).coeff Q' ≤
      (C.modelBoundary (C.modelIndexSeq n)).coeff Q := by
  haveI := (C.junction 0).isBirationalMorphism.isDominant
  have key := le_of_isValuationLogDiscrepancy_succ C n (P.valuationOver (C.junction 0).p) _ _
    ?_ ?_
    (isValuationLogDiscrepancy_divisorialValuation (isPair_model C _ _) Q)
    (isValuationLogDiscrepancy_divisorialValuation (isPair_model C _ _) Q')
  · exact_mod_cast (sub_le_sub_iff_left 1).mp key
  -- The centre hypotheses are `hQ`, `hQ'` once the model index is cased on; the statement of
  -- `le_of_isValuationLogDiscrepancy_succ` carries `ord_{Q'}` along in the first one.
  · generalize Q'.divisorialValuation = b
    revert Q
    generalize C.modelIndexSeq n = x
    rintro Q hQ
    rcases x with ⟨i, _ | k⟩ <;> exact hQ
  · revert Q'
    generalize C.modelIndexSeq (n + 1) = x
    rintro Q' hQ'
    rcases x with ⟨i, _ | k⟩ <;> exact hQ'

/-- Along the models `M_n = C.model (C.modelIndexSeq n)` of a terminal chain, the coefficient of
the boundary at the centre of `ord_P`, `P` a prime divisor of `Y_0`, is nonincreasing: if
`n ≤ m`, `Q` is the centre of `ord_P` on `M_n` and `Q'` is the centre of `ord_P` on `M_m`, then
`(Θ^{M_m}).coeff Q' ≤ (Θ^{M_n}).coeff Q`, centres in the sense of `IsPrimeDivisorCentre`. -/
@[mmp "prop_oai4_terminal_chain_e"]
public theorem coeff_modelBoundary_le_of_le (C : TerminalChain T)
    (P : MMP.Mori.PrimeDivisor (C.junction 0).Y) {n m : ℕ} (hnm : n ≤ m)
    (Q : MMP.Mori.PrimeDivisor (C.model (C.modelIndexSeq n)))
    (Q' : MMP.Mori.PrimeDivisor (C.model (C.modelIndexSeq m)))
    (hQ : C.IsPrimeDivisorCentre P (C.modelIndexSeq n) Q)
    (hQ' : C.IsPrimeDivisorCentre P (C.modelIndexSeq m) Q') :
    (C.modelBoundary (C.modelIndexSeq m)).coeff Q' ≤
      (C.modelBoundary (C.modelIndexSeq n)).coeff Q := by
  have he := isPrimeDivisorCentre_iff_primeDivisorEquivModel_eq C
  obtain rfl := (he _ P Q).mp hQ
  obtain rfl := (he _ P Q').mp hQ'
  exact antitone_nat_of_succ_le
    (f := fun n => (C.modelBoundary (C.modelIndexSeq n)).coeff
      (C.primeDivisorEquivModel (C.modelIndexSeq n) P))
    (fun n => coeff_modelBoundary_succ_le C n ((he _ P _).mpr rfl) ((he _ P _).mpr rfl)) hnm

/-- From a model `V_k` of the `i`-th bridge, the chain reaches the junction `Y_{i+1}`. -/
private theorem exists_ge_of_bridge (C : TerminalChain T) (i : ℕ) :
    ∀ (d n : ℕ) (k : Fin (C.bridge i).P.m), (C.bridge i).P.m = k.1 + 1 + d →
      C.modelIndexSeq n = ⟨i, some k⟩ → ∃ n' ≥ n, C.modelIndexSeq n' = ⟨i + 1, none⟩ := by
  intro d
  induction d with
  | zero =>
    intro n k hk hn
    refine ⟨n + 1, by omega, ?_⟩
    have h : ¬ k.1 + 1 < (C.bridge i).P.m := by omega
    rw [modelIndexSeq_succ, hn]
    simp only [next, h, ↓reduceDIte]
  | succ d ih =>
    intro n k hk hn
    have h : k.1 + 1 < (C.bridge i).P.m := by omega
    obtain ⟨n', hn', h'⟩ := ih (n + 1) ⟨k.1 + 1, h⟩ (by simp only; omega)
      (by rw [modelIndexSeq_succ, hn]; simp only [next, h, ↓reduceDIte])
    exact ⟨n', by omega, h'⟩

/-- From the junction `Y_i`, the chain reaches the junction `Y_{i+1}`. -/
private theorem exists_ge_succ (C : TerminalChain T) {i n : ℕ}
    (hn : C.modelIndexSeq n = ⟨i, none⟩) :
    ∃ n' ≥ n, C.modelIndexSeq n' = ⟨i + 1, none⟩ := by
  by_cases h : 0 < (C.bridge i).P.m
  · obtain ⟨n', hn', h'⟩ := exists_ge_of_bridge C i ((C.bridge i).P.m - 1) (n + 1) ⟨0, h⟩
      (by simp only; omega) (by rw [modelIndexSeq_succ, hn]; simp only [next, h, ↓reduceDIte])
    exact ⟨n', by omega, h'⟩
  · refine ⟨n + 1, by omega, ?_⟩
    rw [modelIndexSeq_succ, hn]
    simp only [next, h, ↓reduceDIte]

/-- Every later junction `Y_j`, `j ≥ i`, comes after the junction `Y_i` among the models. -/
private theorem exists_ge (C : TerminalChain T) {i n : ℕ}
    (hn : C.modelIndexSeq n = ⟨i, none⟩) {j : ℕ} (hij : i ≤ j) :
    ∃ n' ≥ n, C.modelIndexSeq n' = ⟨j, none⟩ := by
  induction j, hij using Nat.le_induction with
  | base => exact ⟨n, le_rfl, hn⟩
  | succ j _ ih =>
    obtain ⟨n', hn', h'⟩ := ih
    obtain ⟨n'', hn'', h''⟩ := exists_ge_succ C h'
    exact ⟨n'', by omega, h''⟩

/-- Every junction `Y_i` is one of the models of the chain. -/
private theorem exists_modelIndexSeq_eq (C : TerminalChain T) (i : ℕ) :
    ∃ n, C.modelIndexSeq n = ⟨i, none⟩ := by
  obtain ⟨n, -, h⟩ := exists_ge C (n := 0) rfl (Nat.zero_le i)
  exact ⟨n, h⟩

/-- Every label has a centre on every junction. -/
private theorem exists_isLabelCentre (C : TerminalChain T) (S : C.Label) (i : ℕ) :
    ∃ P, C.IsLabelCentre S ⟨i, none⟩ P :=
  ⟨_, (isPrimeDivisorCentre_iff_primeDivisorEquivModel_eq C ⟨i, none⟩ S.1 _).mpr rfl⟩

/-- A junction label coefficient is the boundary coefficient at a centre of the label. -/
private theorem exists_isLabelCentre_coeff_eq {C : TerminalChain T}
    {S : C.Label} {i : ℕ} {b : ℚ} (hb : C.IsJunctionLabelCoefficient S i b) :
    ∃ P, C.IsLabelCentre S ⟨i, none⟩ P ∧ (C.modelBoundary ⟨i, none⟩).coeff P = b := by
  rcases hb with h | ⟨h, -⟩
  · exact h
  · obtain ⟨P, hP⟩ := exists_isLabelCentre C S i
    exact (h P hP).elim

/-- The boundary coefficients of a junction are nonnegative. -/
private theorem coeff_modelBoundary_nonneg (C : TerminalChain T) (i : ℕ)
    (P : MMP.Mori.PrimeDivisor (C.junction i).Y) :
    0 ≤ (C.modelBoundary ⟨i, none⟩).coeff P :=
  (C.isKltTerminalPair_modelBoundary ⟨i, none⟩).1.1.1.nonneg P

/-- The coefficient of a label is nonincreasing along the junctions: if `i ≤ j`, then
`b_h^{(j)} ≤ b_h^{(i)}`. -/
private theorem coeff_le_of_le (C : TerminalChain T) (S : C.Label) {i j : ℕ} (hij : i ≤ j)
    {P : MMP.Mori.PrimeDivisor (C.junction i).Y} {P' : MMP.Mori.PrimeDivisor (C.junction j).Y}
    (hP : C.IsLabelCentre S ⟨i, none⟩ P) (hP' : C.IsLabelCentre S ⟨j, none⟩ P') :
    (C.modelBoundary ⟨j, none⟩).coeff P' ≤ (C.modelBoundary ⟨i, none⟩).coeff P := by
  obtain ⟨n, hn⟩ := exists_modelIndexSeq_eq C i
  obtain ⟨n', hnn', hn'⟩ := exists_ge C hn hij
  have h := fun Q Q' => C.coeff_modelBoundary_le_of_le S.1 hnn' Q Q'
  rw [hn, hn'] at h
  exact h P P' hP hP'

/-- A varying label `S_h` of a terminal chain has positive coefficient `b_h^{(i)} > 0` at every
junction `(Y_i, Θ_i)`. -/
@[mmp "lem_oai4_c1_varying_positive"]
public theorem IsVaryingLabel.pos_of_isJunctionLabelCoefficient {C : TerminalChain T}
    {S : C.Label} (hS : C.IsVaryingLabel S) {i : ℕ} {b : ℚ} (hb : C.IsJunctionLabelCoefficient S i b) :
    0 < b := by
  obtain ⟨P, hP, rfl⟩ := exists_isLabelCentre_coeff_eq hb
  refine (coeff_modelBoundary_nonneg C i P).lt_of_ne fun h0 => hS ⟨0, i, fun j hij => ?_⟩
  obtain ⟨P', hP'⟩ := exists_isLabelCentre C S j
  exact Or.inl ⟨P', hP', le_antisymm (h0 ▸ coeff_le_of_le C S hij hP hP')
    (coeff_modelBoundary_nonneg C j P')⟩

end Statements

end StabilizedSmallKltTail.TerminalChain

end MMP.Fourfold
