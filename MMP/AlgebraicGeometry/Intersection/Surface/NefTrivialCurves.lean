module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Intersection.Nef
public import MMP.AlgebraicGeometry.Intersection.OneCycles
public import MMP.AlgebraicGeometry.Singularities.Slc.NodeResidueForm
public import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
public import MMP.AlgebraicGeometry.Morphisms.Smooth.IrreducibleComponents
import MMP.AlgebraicGeometry.Intersection.Surface.Basic
import MMP.AlgebraicGeometry.Intersection.CartierRestriction
import MMP.AlgebraicGeometry.Intersection.Surface.Symmetry
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.Corollaries
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleExceptionalCurve
import MMP.AlgebraicGeometry.Divisor.AmpleSectionDivisor
import MMP.AlgebraicGeometry.Divisor.LocalSectionDivisor
import MMP.AlgebraicGeometry.Positivity.RelativeAmplePullbackTwist
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.Divisor.SmoothRDivisors
import MMP.AlgebraicGeometry.Divisor.OrderPullback
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback

/-!
# Numerically equivalent curves on which a nef divisor is trivial

Let `S` be a smooth projective surface over an algebraically closed field `k` of characteristic
zero and `N` a nef `ℚ`-divisor on `S` which is not numerically trivial. If two distinct integral
curves `B₁ ≠ B₂` satisfy `(N · B₁) = (N · B₂) = 0` and `B₁ ≡ B₂`, then `(N²) = 0` and
`B₁ ≡ c N` for some rational `c > 0`. Consequently, when `(N²) > 0`, the integral curves `B` with
`(N · B) = 0` have pairwise distinct numerical classes, and there are only countably many of them.

## Main results

* `MMP.Mori.selfIntersection_eq_zero_and_exists_numericallyEquivalent_smul_of_isNef`

## Implementation notes

Every prime divisor of the smooth surface `S` is Cartier
(`MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme`), so the intersection number `(C · C')`
of two integral curves is `MMP.Mori.Divisor.intersectionNumberOn` of `C` and `C'` against `S`
itself. The pairing of `ℚ`-divisors is its bilinear extension
`(A · B) = ∑_{C, C'} A(C) B(C') (C · C')`, written inline, as in
`MMP.Mori.exists_forall_isCartier_and_intersectionNumberOn_of_smooth`. Nefness, numerical
triviality and numerical equivalence are `MMP.Mori.QDivisor.IsNef`,
`MMP.Mori.QDivisor.IsNumericallyTrivial` and `MMP.Mori.QDivisor.NumericallyEquivalent`.

## References

* [KM92] J. Kollár et al., *Flips and abundance for algebraic threefolds*, Chapter 15.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

/-! ### The bilinear extension of a pairing to finitely supported functions -/

section Pairing

variable {α : Type*} (I : α → α → ℤ)

/-- The bilinear extension `(A · B) = ∑ A(C) B(C') I(C, C')` of a pairing `I`. -/
private noncomputable def qform (A B : α →₀ ℚ) : ℚ :=
  A.sum fun C a => B.sum fun C' b => a * b * I C C'

/-- `(A · B) = ∑_C A(C) ∑_{C'} B(C') I(C, C')`. -/
private theorem qform_eq_sum_left (A B : α →₀ ℚ) :
    qform I A B = A.sum fun C a => a * B.sum fun C' b => b * I C C' := by
  refine Finsupp.sum_congr fun C _ => ?_
  rw [Finsupp.mul_sum]
  exact Finsupp.sum_congr fun C' _ => by ring

/-- The extension of a symmetric pairing is symmetric. -/
private theorem qform_comm (hI : ∀ C C', I C C' = I C' C) (A B : α →₀ ℚ) :
    qform I A B = qform I B A := by
  rw [qform, qform, Finsupp.sum_comm]
  refine Finsupp.sum_congr fun C _ => Finsupp.sum_congr fun C' _ => ?_
  rw [hI]
  ring

/-- The extension is additive in the first variable. -/
private theorem qform_add_left (A A' B : α →₀ ℚ) :
    qform I (A + A') B = qform I A B + qform I A' B := by
  simp only [qform_eq_sum_left]
  exact Finsupp.sum_add_index' (fun _ => zero_mul _) fun _ _ _ => add_mul _ _ _

/-- The extension is homogeneous in the first variable. -/
private theorem qform_smul_left (c : ℚ) (A B : α →₀ ℚ) :
    qform I (c • A) B = c * qform I A B := by
  simp only [qform_eq_sum_left]
  rw [Finsupp.sum_smul_index fun _ => zero_mul _, Finsupp.mul_sum]
  exact Finsupp.sum_congr fun _ _ => by ring

/-- The extension is subtractive in the first variable. -/
private theorem qform_sub_left (A A' B : α →₀ ℚ) :
    qform I (A - A') B = qform I A B - qform I A' B := by
  rw [sub_eq_add_neg, qform_add_left, ← neg_one_smul ℚ A', qform_smul_left]
  ring

/-- `(A · B) = ∑_{C'} B(C') (A · C')`. -/
private theorem qform_eq_sum_right (A B : α →₀ ℚ) :
    qform I A B = B.sum fun C' b => b * A.sum fun C a => a * I C C' := by
  rw [qform, Finsupp.sum_comm]
  refine Finsupp.sum_congr fun C' _ => ?_
  rw [Finsupp.mul_sum]
  exact Finsupp.sum_congr fun C _ => by ring

/-- On two prime divisors the extension is the pairing itself. -/
private theorem qform_single_single (C C' : α) :
    qform I (Finsupp.single C 1) (Finsupp.single C' 1) = I C C' := by
  rw [qform, Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
  ring

/-- **The Hodge index argument.** Let `T` be the null space of the form, so that the form
satisfies the Hodge index theorem: `(A²) > 0` and `(A · B) = 0` give `(B²) ≤ 0`, with equality
exactly for `B ∈ T`. If `N ∉ T` with `(N²) ≥ 0` and `(N · H) ≥ 0` for some `H` with `(H²) > 0`,
and `B` with `(B · H) > 0` and `(B²) ≥ 0` is orthogonal to `N`, then `(N²) = 0` and
`B - c N ∈ T` for `c = (B · H) / (N · H) > 0`. -/
private theorem qform_hodge_index (hI : ∀ C C', I C C' = I C' C) (T : (α →₀ ℚ) → Prop)
    (hodge : ∀ A B, 0 < qform I A A → qform I A B = 0 →
      qform I B B ≤ 0 ∧ (qform I B B = 0 ↔ T B))
    (hT : ∀ D, T D → ∀ B, qform I D B = 0) {N H B : α →₀ ℚ} (hNN : 0 ≤ qform I N N)
    (hNH : 0 ≤ qform I N H) (hNT : ¬ T N) (hHH : 0 < qform I H H) (hBH : 0 < qform I B H)
    (hBB : 0 ≤ qform I B B) (hNB : qform I N B = 0) :
    qform I N N = 0 ∧ 0 < qform I B H / qform I N H ∧
      T (B - (qform I B H / qform I N H) • N) := by
  have hN0 : qform I N N = 0 := by
    refine le_antisymm (not_lt.1 fun hpos => ?_) hNN
    obtain ⟨hle, hiff⟩ := hodge N B hpos hNB
    have := hT B (hiff.1 (le_antisymm hle hBB)) H
    linarith
  have hNH' : 0 < qform I N H := lt_of_le_of_ne hNH fun h0 => hNT <|
    (hodge H N hHH (by rw [qform_comm I hI]; exact h0.symm)).2.1 hN0
  set c := qform I B H / qform I N H
  refine ⟨hN0, div_pos hBH hNH', ?_⟩
  have hHB : qform I H (B - c • N) = 0 := by
    rw [qform_comm I hI, qform_sub_left, qform_smul_left, div_mul_cancel₀ _ hNH'.ne', sub_self]
  have hBB' : qform I (B - c • N) (B - c • N) = qform I B B := by
    rw [qform_sub_left, qform_smul_left, qform_comm I hI B, qform_comm I hI N, qform_sub_left,
      qform_sub_left, qform_smul_left, qform_smul_left, qform_comm I hI B N, hNB, hN0]
    ring
  obtain ⟨hle, hiff⟩ := hodge H _ hHH hHB
  exact hiff.1 (le_antisymm hle (hBB' ▸ hBB))

end Pairing

/-! ### Prime divisors of a surface as proper curves -/

section Curves

open Order

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- The dimension of the reduced closed subscheme on `{x}⁻` is the height of `x`. -/
private theorem topologicalKrullDim_curveSubschemeAt (x : X) :
    topologicalKrullDim (curveSubschemeAt x) = (height x : WithBot ℕ∞) := by
  have h := MMP.Intersection.subvarietyDim_eq_height (MMP.Intersection.associatedSubvariety x)
  rw [MMP.Intersection.genericPoint_associatedSubvariety] at h
  exact h

/-- On an integral `k`-surface locally of finite type, `height x + coheight x = 2`. -/
private theorem height_add_coheight_eq_two [IsIntegral X] [LocallyOfFiniteType sX]
    (hdim : topologicalKrullDim X = 2) (x : X) : height x + coheight x = 2 := by
  let : X.Over (Spec (.of k)) := ⟨sX⟩
  have : LocallyOfFiniteType (X ↘ Spec (.of k)) := ‹LocallyOfFiniteType sX›
  have hpure : MMP.Intersection.IsPureDimensional X 2 := by
    intro Z hZ
    rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hZ
    subst hZ
    rw [(Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq, hdim]
    rfl
  exact MMP.Intersection.height_add_coheight_eq_of_isPureDimensional k hpure x

/-- The generic point of a prime divisor of a proper surface is the generic point of a proper
curve. -/
private theorem isProperCurve_genericPoint [IsProper sX] [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (hdim : topologicalKrullDim X = 2)
    (P : MMP.Mori.PrimeDivisor X) : IsProperCurve sX P.genericPoint := by
  refine isProperCurve_of_isProper sX ?_
  rw [topologicalKrullDim_curveSubschemeAt]
  have h := height_add_coheight_eq_two sX hdim P.genericPoint
  rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P] at h
  have h1 : height P.genericPoint = 1 :=
    WithTop.add_right_cancel ENat.one_ne_top (h.trans one_add_one_eq_two.symm)
  rw [h1]
  rfl

/-- The proper curve of a prime divisor of a proper surface. -/
private noncomputable def primeCurve [IsProper sX] [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] (hdim : topologicalKrullDim X = 2) (P : MMP.Mori.PrimeDivisor X) :
    ProperCurve sX :=
  ⟨P.genericPoint, isProperCurve_genericPoint sX hdim P⟩

variable [IsProper sX] [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  (hsm : IsSmoothScheme sX) (hdim : topologicalKrullDim X = 2)

include hsm in
/-- **Cutting down by a curve.** On a smooth proper surface the intersection number of two prime
divisors `P, P'` is the degree of `𝒪_X(P)` along the proper curve of `P'`. -/
private theorem intersectionNumberOn_eq_degreeOn (P P' : MMP.Mori.PrimeDivisor X)
    (hc : ∀ j, Divisor.IsCartier (![Finsupp.single P 1, Finsupp.single P' 1] j : Divisor X)) :
    Divisor.intersectionNumberOn k sX (𝟙 X) 2 hdim.le
        ![Finsupp.single P 1, Finsupp.single P' 1] hc =
      Divisor.degreeOn k sX (primeCurve sX hdim P').ι (primeCurve sX hdim P').dim_le
        (Finsupp.single P 1) (MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm _) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  set C := primeCurve sX hdim P'
  have hP := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm (Finsupp.single P 1)
  have hP' := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm (Finsupp.single P' 1)
  have := hP.isInvertibleModule_divisorialSheaf
  have := hP'.isInvertibleModule_divisorialSheaf
  have := MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsm P'
  obtain ⟨e⟩ := MMP.Threefold.Resolution.nonempty_divisorialSheaf_single_iso_invertibleSheaf' P'
    inferInstance hP'
  have hd : topologicalKrullDim X ≤ ((1 + 1 : ℕ) : WithBot ℕ∞) := by rw [hdim]; rfl
  have hinv : ∀ j : Fin 2, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (![Divisor.divisorialSheaf (Finsupp.single P' 1 : Divisor X),
        Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor X)] j) := by
    intro j; fin_cases j <;> assumption
  have h1 : Divisor.intersectionNumberOn k sX (𝟙 X) 2 hdim.le
        ![Finsupp.single P 1, Finsupp.single P' 1] hc =
      AlgebraicGeometry.intersectionNumber k sX (𝟙 X) 2 hd
        ![Divisor.divisorialSheaf (Finsupp.single P' 1 : Divisor X),
          Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor X)] := by
    have hinv' : ∀ j : Fin 2, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
        (Divisor.divisorialSheaf (![Finsupp.single P 1, Finsupp.single P' 1] j : Divisor X)) :=
      fun j => (hc j).isInvertibleModule_divisorialSheaf
    rw [Divisor.intersectionNumberOn, Snapper.sheafIntersectionNumber_eq_intersectionNumber,
      ← AlgebraicGeometry.intersectionNumber_comp_perm k sX (𝟙 X) 2 hd
        ![Divisor.divisorialSheaf (Finsupp.single P' 1 : Divisor X),
          Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor X)] (Equiv.swap 0 1)]
    exact AlgebraicGeometry.intersectionNumber_congr_family k sX (𝟙 X) 2 _
      (funext fun j => by fin_cases j <;> rfl)
  rw [h1]
  have hL : (Scheme.Modules.pullback (𝟙 X)).obj
      (![Divisor.divisorialSheaf (Finsupp.single P' 1 : Divisor X),
        Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor X)] 0) ≅
      (Stacks.Divisors.invertibleSheaf P'.idealSheaf : X.Modules) :=
    (Scheme.Modules.pullbackId X).app _ ≪≫ e
  rw [AlgebraicGeometry.intersectionNumber_eq_of_isEffectiveCartierDivisor' k sX (𝟙 X) 1
    hd _ P'.idealSheaf hL]
  rw [Divisor.degreeOn, degreeOn,
    ← AlgebraicGeometry.intersectionNumber_one_eq_invertibleCurveDegree k sX C.ι C.dim_le _]
  rw [AlgebraicGeometry.intersectionNumber_congr_family k sX _ 1 _
    (show (fun t : Fin 1 => ![Divisor.divisorialSheaf (Finsupp.single P' 1 : Divisor X),
        Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor X)] t.succ) =
      fun _ => Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor X) from
      funext fun t => by fin_cases t; rfl)]
  rw [← Snapper.sheafIntersectionNumber_eq_intersectionNumber]
  have hker : (P'.idealSheaf.subschemeι ≫ 𝟙 X).ker = C.ι.ker := by
    rw [Category.comp_id, Scheme.IdealSheafData.ker_subschemeι,
      Scheme.IdealSheafData.ker_subschemeι]
    exact (MMP.Mori.vanishingIdeal_closure_genericPoint_eq_idealSheaf P').symm
  exact (sheafIntersectionNumber_eq_of_ker_eq k sX _ _ hker 1 _ C.dim_le _).trans
    (Snapper.sheafIntersectionNumber_eq_intersectionNumber k sX C.ι 1 _ _)

omit [IsIntegral X] in
include hsm in
/-- On a smooth scheme the intersection number of a `ℚ`-divisor `D = ∑ a_P P` with a curve is
`∑ a_P deg_C 𝒪_X(P)`. -/
private theorem intersectionNumber_eq_sum {C : Scheme.{u}} (i : C ⟶ X) [IsProper (i ≫ sX)]
    (hd : topologicalKrullDim C ≤ 1) (D : QDivisor X) (hD : D.IsQCartier) :
    D.intersectionNumber k sX i hd hD = D.sum fun P a =>
      a * (Divisor.degreeOn k sX i hd (Finsupp.single P 1)
        (MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm _) : ℚ) := by
  have hq := MMP.Fourfold.isQCartier_of_isSmoothScheme hsm
  induction D using Finsupp.induction_linear with
  | zero =>
    rw [Finsupp.sum_zero_index, QDivisor.intersectionNumber_eq_of_smul k sX i hd 0 hD one_pos 0
      Divisor.isCartier_zero (by simp), Divisor.degreeOn_zero']
    simp
  | add f g hf hg =>
    rw [QDivisor.intersectionNumber_add' k sX i hd f g (hq f) (hq g) hD, hf (hq f), hg (hq g),
      Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  | single P a =>
    rw [Finsupp.sum_single_index (zero_mul _)]
    have hP := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm
      (Finsupp.single P 1 : Divisor X)
    have key : ∀ (D' : QDivisor X) (hD' : D'.IsQCartier),
        D' = a • Divisor.toQDivisor (Finsupp.single P 1) →
        D'.intersectionNumber k sX i hd hD' =
          a * (Divisor.degreeOn k sX i hd (Finsupp.single P 1) hP : ℚ) := by
      rintro _ hD' rfl
      rw [QDivisor.intersectionNumber_smul k sX i hd a _ (QDivisor.isQCartier_toQDivisor hP) hD',
        QDivisor.intersectionNumber_toQDivisor k sX i hd _ hP]
    refine key _ hD ?_
    rw [MMP.Threefold.Resolution.toQDivisor_single, Finsupp.smul_single, smul_eq_mul,
      Int.cast_one, mul_one]

end Curves

/-! ### Symmetry and an effective ample divisor -/

section Ample

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsProper sX]
  [IsLocallyNoetherian X] [IsNormal X]

/-- The intersection number of two Cartier divisors does not depend on their order. -/
private theorem intersectionNumberOn_comm (hd : topologicalKrullDim X ≤ (2 : ℕ))
    (D D' : Divisor X) (h : ∀ j, Divisor.IsCartier (![D, D'] j))
    (h' : ∀ j, Divisor.IsCartier (![D', D] j)) :
    Divisor.intersectionNumberOn k sX (𝟙 X) 2 hd ![D, D'] h =
      Divisor.intersectionNumberOn k sX (𝟙 X) 2 hd ![D', D] h' := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have hinv : ∀ j : Fin 2, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Divisor.divisorialSheaf (![D, D'] j)) := fun j => (h j).isInvertibleModule_divisorialSheaf
  have hinv' : ∀ j : Fin 2, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Divisor.divisorialSheaf (![D', D] j)) := fun j => (h' j).isInvertibleModule_divisorialSheaf
  rw [Divisor.intersectionNumberOn, Divisor.intersectionNumberOn,
    Snapper.sheafIntersectionNumber_eq_intersectionNumber,
    Snapper.sheafIntersectionNumber_eq_intersectionNumber,
    ← AlgebraicGeometry.intersectionNumber_comp_perm k sX (𝟙 X) 2 hd
      (fun j => Divisor.divisorialSheaf (![D', D] j)) (Equiv.swap 0 1)]
  exact AlgebraicGeometry.intersectionNumber_congr_family k sX (𝟙 X) 2 _
    (funext fun j => by fin_cases j <;> rfl)

omit [IsProper sX] in
/-- A projective variety carries an effective Cartier divisor of positive degree on every proper
curve. -/
private theorem exists_nonneg_forall_degreeOn_pos [MMP.Mori.IsProjectiveVariety k sX] :
    ∃ (H : Divisor X) (hH : H.IsCartier), 0 ≤ H ∧
      ∀ C : ProperCurve sX, 0 < H.degreeOn k sX C.ι C.dim_le hH := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have hX : AlgebraicGeometry.IsProjectiveVariety k sX := inferInstance
  obtain ⟨-, L, hLinv, hLamp⟩ := Stacks.HProjective.isQuasiProjective_of_isHQuasiProjective sX
    hX.isProjective.isHQuasiProjective
  have hL : Stacks.Ample.IsAmple X L :=
    Stacks.HProjective.isAmple_of_isRelativelyAmple_of_isAffine sX L hLamp
  obtain ⟨IX, hIX, -, -, n, hn, ⟨eX⟩⟩ :=
    MMP.Threefold.Resolution.exists_isEffectiveCartierDivisor_of_isAmple L hL isClosed_empty
      (Set.notMem_empty (genericPoint X))
  obtain ⟨H, hH0, hHc, ⟨eH⟩, -⟩ :=
    MMP.Threefold.Resolution.exists_divisor_of_isEffectiveCartierDivisor IX hIX
  have := hHc.isInvertibleModule_divisorialSheaf
  have hHamp : Stacks.Ample.IsAmple X H.divisorialSheaf :=
    (Stacks.RelativeVeryAmple.isAmple_congr _ _ (eX ≪≫ eH.symm)).mp
      (Stacks.AmplePositivePower.isAmple_tensorPowModule_of_isAmple L n hn hL)
  refine ⟨H, hHc, hH0, fun C => ?_⟩
  exact MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple hX.toIsVariety sX _
    (MMP.Threefold.Resolution.isRelativelyAmple_of_isAmple sX _ hHamp) C
    fun _ _ => Subsingleton.elim _ _

end Ample

/-! ### The pairing against the curves of prime divisors -/

section Degree

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsProper sX]
  [IsLocallyNoetherian X] [IsNormal X]

/-- `D ≡ D'` as soon as `D' - D` is numerically trivial. -/
private theorem numericallyEquivalent_of_isNumericallyTrivial_sub {D D' : QDivisor X}
    (hD : D.IsQCartier) (hD' : D'.IsQCartier) (h : (D' - D).IsNumericallyTrivial k sX) :
    D.NumericallyEquivalent k sX D' := by
  obtain ⟨hDD, h0⟩ := (QDivisor.isNumericallyTrivial_iff _).1 h
  refine ⟨hD, hD', fun C i _ _ _ hC => ?_⟩
  have key : ∀ (E : QDivisor X) (hE : E.IsQCartier), E = (D' - D) + D →
      E.intersectionNumber k sX i hC.le hE = D.intersectionNumber k sX i hC.le hD := by
    rintro _ hE rfl
    rw [QDivisor.intersectionNumber_add' k sX i hC.le _ _ hDD hD hE, h0 C i hC, zero_add]
  exact (key D' hD' (sub_add_cancel D' D).symm).symm

variable [IsIntegral X] (hsm : IsSmoothScheme sX) (hdim : topologicalKrullDim X = 2)

/-- The curve of a prime divisor is integral. -/
private theorem isIntegral_primeCurve (P : MMP.Mori.PrimeDivisor X) :
    IsIntegral (primeCurve sX hdim P).scheme :=
  StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _
    isIrreducible_singleton.closure

include hsm in
/-- On a smooth projective surface, `(A · B) = ∑_{C'} B(C') (A · C')`, where `(A · C')` is the
intersection number of `A` with the curve of the prime divisor `C'`. -/
private theorem qform_eq_sum_intersectionNumber
    (hc : ∀ C C' : MMP.Mori.PrimeDivisor X, ∀ j,
      Divisor.IsCartier (![Finsupp.single C 1, Finsupp.single C' 1] j : Divisor X))
    (A B : QDivisor X) :
    qform (fun C C' => Divisor.intersectionNumberOn k sX (𝟙 X) 2 hdim.le
        ![Finsupp.single C 1, Finsupp.single C' 1] (hc C C')) A B =
      B.sum fun P b => b * A.intersectionNumber k sX (primeCurve sX hdim P).ι
        (primeCurve sX hdim P).dim_le (MMP.Fourfold.isQCartier_of_isSmoothScheme hsm A) := by
  rw [qform_eq_sum_right]
  refine Finsupp.sum_congr fun P _ => ?_
  rw [intersectionNumber_eq_sum sX hsm]
  refine congrArg _ (Finsupp.sum_congr fun C _ => ?_)
  rw [intersectionNumberOn_eq_degreeOn sX hsm hdim C P]

end Degree

/-- **Two numerically equivalent `N`-trivial curves.** Let `X` be a smooth projective surface over
an algebraically closed field `k` of characteristic zero, `(C · C')` the intersection number of
integral curves and `(A · B) = ∑ A(C) B(C') (C · C')` its bilinear extension to `ℚ`-divisors. Let
`N` be a nef `ℚ`-divisor which is not numerically trivial. If `B₁ ≠ B₂` are integral curves with
`(N · B₁) = (N · B₂) = 0` and `B₁ ≡ B₂`, then `(N²) = 0` and `B₁ ≡ c N` for some rational
`c > 0`. In particular, if `(N²) > 0`, then only countably many integral curves `B` satisfy
`(N · B) = 0`. -/
@[mmp "lem_fa15_numerically_equivalent_trivial_curves"]
public theorem selfIntersection_eq_zero_and_exists_numericallyEquivalent_smul_of_isNef
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsProjectiveVariety k sX] [Smooth sX]
    (hdim : topologicalKrullDim X = 2) :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI : IsNormal (Spec (.of k)) :=
      isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed k)
    haveI : IsNormal X := isNormal_of_smooth sX
    let I : PrimeDivisor X → PrimeDivisor X → ℤ := fun C C' =>
      Divisor.intersectionNumberOn k sX (𝟙 X) 2 hdim.le
        ![Finsupp.single C 1, Finsupp.single C' 1] fun j => by
          fin_cases j <;>
            exact Threefold.Mori.isCartier_single_of_isSmoothScheme
              (Flips.isSmoothScheme_of_smooth sX) _
    let Q : QDivisor X → QDivisor X → ℚ := fun A B =>
      A.sum fun C a => B.sum fun C' b => a * b * I C C'
    ∀ N : QDivisor X, N.IsNef k sX → ¬ N.IsNumericallyTrivial k sX →
      (∀ B₁ B₂ : PrimeDivisor X, B₁ ≠ B₂ →
        Q N (Finsupp.single B₁ 1) = 0 → Q N (Finsupp.single B₂ 1) = 0 →
        QDivisor.NumericallyEquivalent k sX (Finsupp.single B₁ 1) (Finsupp.single B₂ 1) →
        Q N N = 0 ∧ ∃ c : ℚ, 0 < c ∧
          QDivisor.NumericallyEquivalent k sX (Finsupp.single B₁ 1) (c • N)) ∧
      (0 < Q N N → {B : PrimeDivisor X | Q N (Finsupp.single B 1) = 0}.Countable) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsNormal (Spec (.of k)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed k)
  have : IsNormal X := isNormal_of_smooth sX
  obtain ⟨_, hpa, hpb, hpc, Nsub, hNsub, -, hcount⟩ :=
    MMP.Mori.exists_forall_isCartier_and_intersectionNumberOn_of_smooth sX hdim
  intro I Q
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsIntegral X := (inferInstance : AlgebraicGeometry.IsProjectiveVariety k sX).toIsIntegral
  have hsm : IsSmoothScheme sX := MMP.Flips.isSmoothScheme_of_smooth sX
  have hq := MMP.Fourfold.isQCartier_of_isSmoothScheme hsm
  have hIsymm : ∀ C C', I C C' = I C' C := fun C C' =>
    intersectionNumberOn_comm sX hdim.le _ _ _ _
  have hQ : ∀ A B, Q A B = B.sum fun P b => b * A.intersectionNumber k sX
      (primeCurve sX hdim P).ι (primeCurve sX hdim P).dim_le (hq A) :=
    qform_eq_sum_intersectionNumber sX hsm hdim _
  have hQsingle : ∀ A P, Q A (Finsupp.single P 1) = A.intersectionNumber k sX
      (primeCurve sX hdim P).ι (primeCurve sX hdim P).dim_le (hq A) := fun A P => by
    rw [hQ, Finsupp.sum_single_index (by simp), one_mul]
  have hQtriv : ∀ D : QDivisor X, D.IsNumericallyTrivial k sX → ∀ B, Q D B = 0 := by
    intro D hD B
    obtain ⟨_, h⟩ := (QDivisor.isNumericallyTrivial_iff D).1 hD
    rw [hQ]
    refine Finset.sum_eq_zero fun P _ => ?_
    have := isIntegral_primeCurve sX hdim P
    exact mul_eq_zero_of_right _ (h _ _ (primeCurve sX hdim P).dim_eq)
  -- an effective ample divisor `H`
  obtain ⟨H, hHc, hH0, hHpos⟩ := exists_nonneg_forall_degreeOn_pos sX
  set Hq := Divisor.toQDivisor H
  have hdegH : ∀ P, 0 < Hq.intersectionNumber k sX (primeCurve sX hdim P).ι
      (primeCurve sX hdim P).dim_le (hq Hq) := fun P => by
    rw [QDivisor.intersectionNumber_toQDivisor k sX _ _ H hHc]
    exact_mod_cast hHpos _
  have hHq0 : ∀ P, 0 ≤ Hq P := fun P => by
    have h := Divisor.coeff_toQDivisor H P
    rw [DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply] at h
    rw [h]
    exact_mod_cast hH0 P
  have hQnefH : ∀ D : QDivisor X, D.IsNef k sX → 0 ≤ Q D Hq := fun D hD => by
    rw [hQ]
    refine Finset.sum_nonneg fun P _ => mul_nonneg (hHq0 P) ?_
    have := isIntegral_primeCurve sX hdim P
    exact hD.2 _ _ (primeCurve sX hdim P).dim_eq
  have hQHH : ∀ P : MMP.Mori.PrimeDivisor X, 0 < Q Hq Hq := by
    intro P
    have hne : Hq ≠ 0 := fun h0 => by
      have h := hQtriv 0 (QDivisor.NumericallyEquivalent.refl QDivisor.isQCartier_zero)
        (Finsupp.single P 1)
      rw [hQsingle, ← h0] at h
      exact (hdegH P).ne' h
    obtain ⟨C, hC⟩ := Finsupp.support_nonempty_iff.2 hne
    rw [hQ]
    exact Finset.sum_pos' (fun P _ => mul_nonneg (hHq0 P) (hdegH P).le) ⟨C, hC,
      mul_pos ((hHq0 C).lt_of_ne (Ne.symm (Finsupp.mem_support_iff.1 hC))) (hdegH C)⟩
  intro N hNnef hNnt
  have hpart1 : ∀ B₁ B₂ : MMP.Mori.PrimeDivisor X, B₁ ≠ B₂ →
      Q N (Finsupp.single B₁ 1) = 0 → Q N (Finsupp.single B₂ 1) = 0 →
      QDivisor.NumericallyEquivalent k sX (Finsupp.single B₁ 1) (Finsupp.single B₂ 1) →
      Q N N = 0 ∧ ∃ c : ℚ, 0 < c ∧
        QDivisor.NumericallyEquivalent k sX (Finsupp.single B₁ 1) (c • N) := by
    intro B₁ B₂ hne h1 _ heq
    -- `(B₁²) = (B₁ · B₂) ≥ 0`
    have hb1nn : 0 ≤ Q (Finsupp.single B₁ 1) (Finsupp.single B₁ 1) := by
      have := isIntegral_primeCurve sX hdim B₁
      rw [hQsingle, heq.intersectionNumber_eq _ (hq _) _ (primeCurve sX hdim B₁).dim_eq,
        ← hQsingle, show Q _ _ = qform I _ _ from rfl, qform_comm I hIsymm, qform_single_single]
      exact_mod_cast (hpa B₁ B₂ hne).1
    have hb1H : 0 < Q (Finsupp.single B₁ 1) Hq := by
      rw [show Q _ _ = qform I _ _ from rfl, qform_comm I hIsymm]
      exact (hdegH B₁).trans_eq (hQsingle Hq B₁).symm
    obtain ⟨hNN, hc, htriv⟩ := qform_hodge_index I hIsymm (QDivisor.IsNumericallyTrivial k sX)
      hpb hQtriv (hpc N hNnef) (hQnefH N hNnef) hNnt (hQHH B₁) hb1H hb1nn h1
    exact ⟨hNN, _, hc,
      (numericallyEquivalent_of_isNumericallyTrivial_sub sX (hq _) (hq _) htriv).symm⟩
  refine ⟨hpart1, fun hNN =>
    Set.MapsTo.countable_of_injOn (fun B _ => Set.mem_range_self B) ?_ hcount⟩
  intro B hB B' hB' heq
  by_contra hne
  have htriv := (hNsub _).1 (QuotientAddGroup.eq.1 heq)
  rw [map_add, map_neg, MMP.Threefold.Resolution.toQDivisor_single,
    MMP.Threefold.Resolution.toQDivisor_single, Int.cast_one, neg_add_eq_sub] at htriv
  exact hNN.ne' (hpart1 B B' hne hB hB'
    (numericallyEquivalent_of_isNumericallyTrivial_sub sX (hq _) (hq _) htriv)).1

end MMP.Mori
