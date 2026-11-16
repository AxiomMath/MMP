module

public import MMP.AlgebraicGeometry.MMP.Contraction.KltRayContraction
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.AmplePerturbationFiniteRays

/-!
# Negative relative steps over a projective base

Let `(X, B)` be a projective klt pair over an algebraically closed field `k` of characteristic
zero, with `B` an effective `ℚ`-divisor and `K` a canonical divisor of `X`, and let `f : X ⟶ S`
be a morphism of `k`-schemes to a projective variety `S`. If `K + B` is not nef over `S`, then
some `(K + B)`-negative extremal ray `R` of the absolute closed cone `NE̅(X)` is spanned by the
class of an integral curve contracted by `f`. The contraction `q : X ⟶ V` of `R` has a normal
projective target, `q_* 𝒪_X = 𝒪_V`, contracts exactly the curves with class in `R`, has relative
Picard number one and `-(K + B)` `q`-ample; `f` factors as `q ≫ h`, and every invertible sheaf of
degree zero on the curves contracted by `q` is the pull-back of an invertible sheaf on `V`.

The ray comes from the cone theorem applied to a `(K + B)`-negative curve contracted by `f`: the
pull-back of an ample divisor of `S` vanishes on that curve and is nonnegative on `NE̅(X)`, so one
of the negative extremal rays in its decomposition is spanned by a curve contracted by `f`. The
contraction and the descent of line bundles are the contraction theorem for that ray.

## Main results

* `MMP.Fourfold.exists_isContractionOfRay_comp_eq_of_not_isRelativelyNef`: the statement above.

## Implementation notes

* The source works over `ℂ`; the statement is over any algebraically closed field of
  characteristic zero, which `MMP.Fourfold.IsKltPair` records.
* Relative nefness of the `ℚ`-Cartier divisor `K + B` is `MMP.Mori.QDivisor.IsRelativelyNef`.
* The relative Picard number is one in both conventions: `MMP.Fourfold.relativePicardNumberN1`
  (codimension of `q^* N¹(V)_ℝ`) and `MMP.Flips.relativePicardNumber` (dimension of
  `N¹(X/V)`).
* Line bundles are invertible sheaves of `𝒪_X`-modules; numerical triviality on the contracted
  curves is vanishing of `MMP.Mori.OneCycle.degree` on each of them.
* The cone decomposition used is the finite one,
  `MMP.Mori.exists_finset_isRationalCurve_closedConeOfCurves_eq`
  (`NE̅(X) = NE̅(X)_{(K + B) + εH ≥ 0} + ∑ ℝ_{≥0}[Cⱼ]` for an ample `H` and `ε > 0`), since it
  records that each `[Cⱼ]` spans an extremal ray. Taking `ε (H · C) < -(K + B) · C` keeps `[C]`
  out of the first summand, so some `Cⱼ` occurs.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Theorem 3.7
-/

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori
open scoped Pointwise

namespace MMP.FourfoldProofs.MmpProjectiveRelativeKltNegativeStepProof

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}

/-- The value of `z ↦ (D · z)` on the class of a curve is the degree of the associated
`ℚ`-Cartier divisor on that curve. -/
private theorem curveForm_numericalClass_cycle [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] [QuasiCompact sX] (D : QDivisor X) (h : D.IsQCartier) (C : ProperCurve sX) :
    MMP.Fourfold.QDivisor.curveForm sX D h (OneCycle.numericalClass sX (C.cycle ℝ)) =
      (D.associatedCartier h).sum fun E c =>
        (c : ℝ) * ((E : Divisor X).degreeOn k sX C.ι C.dim_le E.2 : ℝ) := by
  simp only [MMP.Fourfold.QDivisor.curveForm, Finsupp.sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun E _ => ?_
  rw [LinearMap.smul_apply, NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle,
    smul_eq_mul]
  rfl

/-- A linear form nonnegative on a set is nonnegative on its cone hull. -/
private theorem nonneg_of_mem_hull {E : Type*} [AddCommGroup E] [Module ℝ E] (ℓ : E →ₗ[ℝ] ℝ)
    {s : Set E} (hs : ∀ x ∈ s, 0 ≤ ℓ x) {v : E} (hv : v ∈ PointedCone.hull ℝ s) : 0 ≤ ℓ v := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; positivity
  | smul c x _ hx => exact (map_smul ℓ (c : ℝ) x).symm ▸ mul_nonneg c.2 hx

/-- A linear form positive on a set vanishes on its cone hull only at `0`. -/
private theorem eq_zero_of_mem_hull {E : Type*} [AddCommGroup E] [Module ℝ E] (ℓ : E →ₗ[ℝ] ℝ)
    {s : Set E} (hs : ∀ x ∈ s, 0 < ℓ x) {v : E} (hv : v ∈ PointedCone.hull ℝ s)
    (hℓv : ℓ v = 0) : v = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact absurd hℓv (hs x hx).ne'
  | zero => rfl
  | add x y hx' hy' hx hy =>
    have := nonneg_of_mem_hull ℓ (fun x hx => (hs x hx).le) hx'
    have := nonneg_of_mem_hull ℓ (fun x hx => (hs x hx).le) hy'
    rw [map_add] at hℓv
    rw [hx (by linarith), hy (by linarith), add_zero]
  | smul c x _ hx =>
    change ℓ ((c : ℝ) • x) = 0 at hℓv
    rw [map_smul, smul_eq_mul] at hℓv
    rcases mul_eq_zero.mp hℓv with h | h
    · change (c : ℝ) • x = 0; rw [h, zero_smul]
    · change (c : ℝ) • x = 0; rw [hx h, smul_zero]

/-- Let `ℓ` be a linear form nonnegative on `N` and on `s`, and `x ∈ (N ∩ {g ≥ 0}) + ⟨s⟩₊`
with `ℓ x = 0` and `g x < 0`. Then `ℓ` vanishes at some point of `s`: otherwise the hull
component of `x` is `0`, which puts `x` itself in `{g ≥ 0}`. -/
private theorem exists_mem_eq_zero_of_mem_inter_add_hull {E : Type*} [AddCommGroup E]
    [Module ℝ E] (ℓ : E →ₗ[ℝ] ℝ) (g : E → ℝ) {N s : Set E} (hN : ∀ z ∈ N, 0 ≤ ℓ z)
    (hs : ∀ y ∈ s, 0 ≤ ℓ y) {x : E}
    (hx : x ∈ N ∩ {z | 0 ≤ g z} + (PointedCone.hull ℝ s : Set E)) (hℓx : ℓ x = 0)
    (hgx : g x < 0) : ∃ y ∈ s, ℓ y = 0 := by
  by_contra! hne
  obtain ⟨u, ⟨huN, hu⟩, v, hv, rfl⟩ := hx
  have hpos : ∀ y ∈ s, 0 < ℓ y := fun y hy => (hs y hy).lt_of_ne (hne y hy).symm
  have h1 := hN u huN
  have h2 := nonneg_of_mem_hull ℓ hs hv
  rw [map_add] at hℓx
  obtain rfl := eq_zero_of_mem_hull ℓ hpos hv (by linarith)
  simp only [add_zero] at hgx
  exact hgx.not_ge hu

/-- The pull-back of an ample invertible sheaf has nonnegative degree on every proper curve. -/
private theorem degree_pullback_nonneg {S : Scheme.{0}} {sS : S ⟶ Spec (.of k)} [IsSeparated sS]
    [LocallyOfFiniteType sS] (f : X ⟶ S) (hf : f ≫ sS = sX) (A : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 A]
    (hA : Scheme.Modules.IsAmple S A) (C : ProperCurve sX) :
    0 ≤ C.degree k ((Scheme.Modules.pullback f).obj A) := by
  rw [C.degree_pullback f hf A]
  split_ifs with h
  · set T : ProperCurve sS := ⟨f C.point, h⟩
    have := T.isCurve
    haveI : IsProper (T.ι ≫ sS) := T.isProper_ι_comp
    have hpos : 0 < T.degree k A :=
      invertibleCurveDegree_pos_of_isAmple_of_isCurve k (T.ι ≫ sS) T.dim_le _
        (isAmple_pullback_of_isFinite T.ι A hA)
    positivity
  · exact le_rfl

/-- The degree of the pull-back of an ample invertible sheaf is nonnegative on `NE̅(X)`. -/
private theorem degree_pullback_nonneg_of_mem_closedConeOfCurves [IsProper sX]
    {S : Scheme.{0}} {sS : S ⟶ Spec (.of k)} [IsSeparated sS] [LocallyOfFiniteType sS]
    (f : X ⟶ S) (hf : f ≫ sS = sX) (A : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 A]
    (hA : Scheme.Modules.IsAmple S A) {z : NumericalCurveClasses sX}
    (hz : z ∈ closedConeOfCurves sX) :
    0 ≤ NumericalCurveClasses.degree sX ((Scheme.Modules.pullback f).obj A) z := by
  rw [← SetLike.mem_coe, coe_closedConeOfCurves] at hz
  refine closure_minimal (fun y hy => nonneg_of_mem_hull _ ?_ hy)
    (isClosed_le continuous_const (NumericalCurveClasses.continuous_degree sX _)) hz
  rintro _ ⟨C, rfl⟩
  simp only [NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle]
  exact_mod_cast degree_pullback_nonneg f hf A hA C

/-- A projective normal variety carries an ample Cartier divisor: the Weil divisor of the zero
scheme of a regular section of a power of an ample invertible sheaf. -/
private theorem exists_isCartier_isAmple [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    [IsNormal X] (hX : MMP.Mori.IsProjectiveVariety k sX) :
    ∃ (H : Divisor X) (hH : H.IsCartier), H.IsAmple hH := by
  obtain ⟨-, L, hLinv, hLamp⟩ :=
    Stacks.HProjective.isQuasiProjective_of_isHQuasiProjective sX hX.isProjective.isHQuasiProjective
  have hL : Stacks.Ample.IsAmple X L :=
    Stacks.HProjective.isAmple_of_isRelativelyAmple_of_isAffine sX L hLamp
  obtain ⟨I, hI, -, -, m, hm, ⟨eX⟩⟩ :=
    MMP.Threefold.Resolution.exists_isEffectiveCartierDivisor_of_isAmple L hL isClosed_empty
      (Set.notMem_empty (genericPoint X))
  obtain ⟨H, -, hHc, ⟨eH⟩, -⟩ :=
    MMP.Threefold.Resolution.exists_divisor_of_isEffectiveCartierDivisor I hI
  haveI := hHc.isInvertibleModule_divisorialSheaf
  exact ⟨H, hHc, (Stacks.RelativeVeryAmple.isAmple_congr _ _ (eX ≪≫ eH.symm)).mp
    (Stacks.AmplePositivePower.isAmple_tensorPowModule_of_isAmple L m hm hL)⟩

/-- The relative Picard number of the contraction of the ray spanned by a curve of nonzero class
is one: the divisors numerically trivial over the target are the kernel of `D ↦ (D · C)`, a
nonzero linear form. -/
private theorem relativePicardNumber_eq_one [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {V : Scheme.{0}} {sV : V ⟶ Spec (.of k)} {q : X ⟶ V}
    {C : ProperCurve sX}
    (hq : MMP.Fourfold.IsContractionOfRay sX sV
      {w | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass sX (C.cycle ℝ) = w} q)
    (hC : OneCycle.numericalClass sX (C.cycle ℝ) ≠ 0) :
    MMP.Flips.relativePicardNumber sX q = 1 := by
  set ψ := (OneCycle.intersectionPairing (sX := sX)).flip (C.cycle ℝ)
  have hker : MMP.Flips.relativeNumericallyTrivialDivisors sX q = LinearMap.ker ψ := by
    ext D'
    rw [MMP.Flips.mem_relativeNumericallyTrivialDivisors, LinearMap.mem_ker]
    refine ⟨fun h => h C ((hq.isContractedBy_iff C).mpr ⟨1, zero_le_one, one_smul _ _⟩),
      fun h C' hC' => ?_⟩
    obtain ⟨c, -, hc⟩ := (hq.isContractedBy_iff C').mp hC'
    rw [← NumericalCurveClasses.intersectionNumber_numericalClass, ← hc, map_smul,
      NumericalCurveClasses.intersectionNumber_numericalClass, smul_eq_mul]
    change c * ψ D' = 0
    rw [h, mul_zero]
  have hne : (MMP.Fourfold.numericalPairing sX).flip (OneCycle.numericalClass sX (C.cycle ℝ))
      ≠ 0 := fun h0 =>
    hC (MMP.Fourfold.numericalPairing_flip_injective sX (h0.trans (map_zero _).symm))
  obtain ⟨d, hd⟩ := not_forall.mp fun h => hne (LinearMap.ext h)
  obtain ⟨D', rfl⟩ := Submodule.mkQ_surjective _ d
  replace hd : ψ D' ≠ 0 := hd
  have hsurj : Function.Surjective ψ := fun r =>
    ⟨(r / ψ D') • D', by rw [map_smul, smul_eq_mul, div_mul_cancel₀ r hd]⟩
  unfold MMP.Flips.relativePicardNumber MMP.Flips.RelativeNumericalDivisorClasses
  rw [hker, (LinearMap.quotKerEquivOfSurjective ψ hsurj).rank_eq, Module.rank_self]
  simp

end MMP.FourfoldProofs.MmpProjectiveRelativeKltNegativeStepProof

end

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori

namespace MMP.Fourfold

open MMP.FourfoldProofs.MmpProjectiveRelativeKltNegativeStepProof in
/-- **A negative step over a projective base from the absolute cone.** Let `(X, B)` be a
projective klt pair, `K` a canonical divisor and `f : X ⟶ S` a morphism to a projective variety
such that `K + B` is not `f`-nef. Then there is a `(K + B)`-negative extremal ray `R` of `NE̅(X)`
spanned by the class of a curve contracted by `f`, and a contraction `q : X ⟶ V` of `R` onto a
projective variety with relative Picard number one in both conventions, `-(K + B)` `q`-ample,
`f = q ≫ h` for some `h : V ⟶ S`, and such that every invertible sheaf of degree zero on the
curves contracted by `q` is isomorphic to `q^* M` for an invertible sheaf `M` on `V`. -/
@[mmp "thm_mmp_projective_relative_klt_negative_step"]
public theorem exists_isContractionOfRay_comp_eq_of_not_isRelativelyNef
    {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of k))
    (hX : MMP.Mori.IsProjectiveVariety k sX) {B : QDivisor X} (hklt : IsKltPair sX B)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    {S : Scheme.{0}} {sS : S ⟶ Spec (.of k)} (hS : MMP.Mori.IsProjectiveVariety k sS)
    {f : X ⟶ S} (hfS : f ≫ sS = sX)
    (hnef : ¬ (Divisor.toQDivisor K + B).IsRelativelyNef sX f) :
    ∃ R : Set (NumericalCurveClasses sX),
      IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R ∧
      (∃ C : ProperCurve sX, C.IsContractedBy f ∧
        R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass sX (C.cycle ℝ) = w}) ∧
      ∃ (V : Scheme.{0}) (sV : V ⟶ Spec (.of k)) (q : X ⟶ V),
        IsContractionOfRay sX sV R q ∧ MMP.Mori.IsProjectiveVariety k sV ∧
        relativePicardNumberN1 sX q = 1 ∧ MMP.Flips.relativePicardNumber sX q = 1 ∧
        (-(Divisor.toQDivisor K + B)).HasRelativelyAmpleMultiple q ∧
        (∃ h : V ⟶ S, q ≫ h = f ∧ h ≫ sS = sV) ∧
        ∀ (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L],
          (∀ C : ProperCurve sX, C.IsContractedBy q → OneCycle.degree ℝ sX L (C.cycle ℝ) = 0) →
          ∃ (M : V.Modules) (_ : SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 M),
            Nonempty (L ≅ (Scheme.Modules.pullback q).obj M) := by
  have hP := hklt.1
  haveI := hP.isAlgClosed
  haveI := hP.charZero
  haveI : AlgebraicGeometry.IsProjectiveVariety k sX := hX
  haveI : IsProper sX := isProper_of_isProjectiveMorphism _ hX.isProjective
  haveI : IsProper sS := isProper_of_isProjectiveMorphism _ hS.isProjective
  have hkm : MMP.Mori.IsKltPair sX n K B :=
    (MMP.Fourfold.isKltPair_iff_mori_isKltPair sX hK hP).mp hklt
  have hΔ : B.IsEffective := hP.nonneg
  set φ := MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + B) hkm.1.2.2
  -- a `(K + B)`-negative curve `C` contracted by `f`
  obtain ⟨C, hCf, hCneg⟩ : ∃ C : ProperCurve sX, C.IsContractedBy f ∧
      φ (OneCycle.numericalClass sX (C.cycle ℝ)) < 0 := by
    simp only [MMP.Mori.QDivisor.IsRelativelyNef, not_exists, not_forall, not_le] at hnef
    obtain ⟨C, hC, hlt⟩ := hnef hkm.1.2.2
    exact ⟨C, hC, by rw [curveForm_numericalClass_cycle]; exact hlt⟩
  -- the degree `ℓ` of the pull-back of an ample sheaf of `S`; `ℓ`-null curves are contracted
  obtain ⟨A, hAinv, hA⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety hS
  set ℓ := NumericalCurveClasses.degree sX ((Scheme.Modules.pullback f).obj A)
  have hℓcurve (C' : ProperCurve sX) : ℓ (OneCycle.numericalClass sX (C'.cycle ℝ)) =
      C'.degree k ((Scheme.Modules.pullback f).obj A) := by
    simp only [ℓ, NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle]
  have hℓf (C' : ProperCurve sX) (h : ℓ (OneCycle.numericalClass sX (C'.cycle ℝ)) = 0) :
      C'.IsContractedBy f :=
    MMP.ProgramBaseChange.isContractedBy_of_degree_pullback_eq_zero f hfS A hA C'
      (by rw [hℓcurve] at h; exact_mod_cast h)
  -- the cone theorem, with `ε (H · C) < -(K + B) · C`
  obtain ⟨H, hHc, hHa⟩ := exists_isCartier_isAmple hX
  have hH : (Divisor.toQDivisor H).IsAmple := ⟨1, one_pos, H, by simp, hHc, hHa⟩
  set a := φ (OneCycle.numericalClass sX (C.cycle ℝ))
  set b := MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor H)
    ⟨1, one_ne_zero, H, by simp, hHc⟩ (OneCycle.numericalClass sX (C.cycle ℝ))
  have hε : 0 < -a / (2 * (|b| + 1)) := div_pos (by linarith) (by positivity)
  obtain ⟨T, hT, hcone⟩ := exists_finset_isRationalCurve_closedConeOfCurves_eq hkm hΔ hε hH
  have hCmem := coneOfCurves_le_closedConeOfCurves sX (numericalClass_cycle_mem_coneOfCurves sX C)
  rw [← SetLike.mem_coe, hcone] at hCmem
  -- a curve `Cⱼ` of the cone theorem on which `ℓ` vanishes
  obtain ⟨_, ⟨Cj, hCjT, rfl⟩, hℓCj⟩ := exists_mem_eq_zero_of_mem_inter_add_hull ℓ _
    (fun z hz => degree_pullback_nonneg_of_mem_closedConeOfCurves f hfS A hA hz)
    (by rintro _ ⟨C', -, rfl⟩
        exact degree_pullback_nonneg_of_mem_closedConeOfCurves f hfS A hA
          (coneOfCurves_le_closedConeOfCurves sX (numericalClass_cycle_mem_coneOfCurves sX C')))
    hCmem (by rw [hℓcurve]; exact_mod_cast C.degree_pullback_eq_zero_of_isContractedBy f hfS hCf A)
    (by
      have hb : -a / (2 * (|b| + 1)) * b ≤ -a / (2 * (|b| + 1)) * (|b| + 1) :=
        mul_le_mul_of_nonneg_left ((le_abs_self b).trans (by linarith)) hε.le
      have hab : -a / (2 * (|b| + 1)) * (|b| + 1) = -a / 2 := by field_simp
      change a + -a / (2 * (|b| + 1)) * b < 0
      linarith)
  set R : Set (NumericalCurveClasses sX) :=
    {w | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass sX (Cj.cycle ℝ) = w}
  have hCjneg : φ (OneCycle.numericalClass sX (Cj.cycle ℝ)) < 0 := neg_pos.mp (hT Cj hCjT).2.1
  have hRext := (hT Cj hCjT).2.2.2
  have hR : MMP.Fourfold.IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R := by
    refine ⟨hkm.1.2.2, hRext, ?_⟩
    rintro u ⟨c, hc, rfl⟩ hu0
    rw [map_smul, smul_eq_mul]
    exact mul_neg_of_pos_of_neg (hc.lt_of_ne (by rintro rfl; exact hu0 (zero_smul _ _))) hCjneg
  have hmemR (C' : ProperCurve sX) (hC' : OneCycle.numericalClass sX (C'.cycle ℝ) ∈ R) :
      C'.IsContractedBy f := by
    obtain ⟨c, -, hc⟩ := hC'
    exact hℓf C' (by rw [← hc, map_smul, hℓCj, smul_zero])
  obtain ⟨-, V, sV, q, hq, hV, hρ, hamp⟩ :=
    MMP.Fourfold.exists_isContractionOfRay_of_isKltPair sX hX hklt hK hR
  refine ⟨R, hR, ⟨Cj, hmemR Cj ⟨1, zero_le_one, one_smul _ _⟩, rfl⟩, V, sV, q, hq, hV, hρ,
    relativePicardNumber_eq_one hq fun h0 => hCjneg.ne (by rw [h0, map_zero]), hamp, ?_, ?_⟩
  · -- the factorization of `f` through the contraction
    haveI : IsProper q := isProper_of_isProjectiveMorphism _ hq.isProjectiveMorphism
    haveI : Surjective q := ⟨hq.surjective⟩
    haveI : ∀ U, IsIso (q.c.app U) := fun U => hq.isIso_app U.unop
    haveI : IsIso q.c := NatIso.isIso_of_isIso_app _
    obtain ⟨h, hh, -⟩ := MMP.Mori.existsUnique_comp_eq_of_isContractedBy hX hV hS
      hq.isProjectiveMorphism hq.comp_eq hfS fun C' hC' =>
        hmemR C' ((hq.isContractedBy_iff C').mp hC')
    exact ⟨h, hh, (MMP.existsUnique_comp_eq_of_isIso_c q sX fun _ _ _ =>
      Subsingleton.elim _ _).unique (by rw [← Category.assoc, hh, hfS]) hq.comp_eq⟩
  · -- line bundles trivial on the contracted curves descend
    intro L _ hL
    obtain ⟨M, hM, e⟩ := exists_isInvertible_iso_pullback_of_isContractionOfFace hkm hΔ
      (F := R) ⟨hRext.1, hRext.1.2.2.1, hR.2.2⟩
      ⟨hX, hV, hq.comp_eq, hRext.1, hq.isContractedBy_iff, hq.isIso_app⟩ L fun C' hC' => by
        have := hL C' ((hq.isContractedBy_iff C').mpr hC')
        rw [OneCycle.degree_cycle] at this
        exact_mod_cast this
    exact ⟨M, hM, e⟩

end MMP.Fourfold

end
