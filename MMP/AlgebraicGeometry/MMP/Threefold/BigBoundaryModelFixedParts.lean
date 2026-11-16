module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.BasepointFree.UniformRelativeFreeness
public import MMP.AlgebraicGeometry.MMP.Threefold.MinimalModel.RealKltLogTerminalModel
public import MMP.AlgebraicGeometry.MMP.MinimalModel.FixedPartUniformity
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.FiniteGeneration
public import MMP.AlgebraicGeometry.MMP.Fourfold.Positivity
public import MMP.AlgebraicGeometry.MMP.Fourfold.StableBase
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
public import MMP.AlgebraicGeometry.Singularities.LogResolution.Basic
public import MMP.AlgebraicGeometry.Divisor.FloorSectionsExceptionalPullback
public import MMP.AlgebraicGeometry.Positivity.BigBirationalTransform
public import MMP.AlgebraicGeometry.Divisor.FloorSectionAlgebraFG
public import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
public import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
public import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
public import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import MMP.AlgebraicGeometry.Divisor.DivisorialPullback
public import MMP.AlgebraicGeometry.SpreadingOut.LocalEquations
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
public import MMP.AlgebraicGeometry.Singularities.Adjunction.CartierCodimTwo
public import MMP.AlgebraicGeometry.Morphisms.SteinFactorization

section

/-!
# Projective threefold big-boundary models and fixed parts

For a morphism `g : X ⟶ S` of projective complex varieties, `X` a normal `ℚ`-factorial
threefold and `Δ = A + B` an effective real klt boundary with `A` a relatively big
`ℚ`-Cartier `ℚ`-divisor, a pseudo-effective adjoint `K_X + Δ` has a `ℚ`-factorial klt log
terminal model `φ : X ⤏ Y` over `S`; the divisorial stable base primes of `K_X + Δ` persist near
`Δ`; the fixed parts of the divisible multiples of `K_X + Ξ` for `Ξ` near `Δ` in its smallest
rational affine hull consist of stable base primes of `K_X + Δ`; and for rational `Δ` the
floor-section algebra `⊕_m g_* 𝒪_X(⌊m(K_X + Δ)⌋)` is locally of finite type.

The model is the log terminal model of
`MMP.Fourfold.IsRealKltPair.exists_isNefWeakModel_of_isRelativelyPseudoEffective`. The two
neighbourhood statements are
`MMP.Fourfold.isInRelativeDivisorialStableBase_uniformity_of_isBirationalContraction` for the
rational affine family `D_t = K_X + ∑ tᵢ Pᵢ` over the primes `Pᵢ` of `K_X + Δ`, with the big core
`φ_* A`. For rational `Δ`, the adjoint `K_Y + φ_* Δ` has a relatively free Cartier multiple
(`MMP.Fourfold.QDivisor.IsRelativelyBig.exists_isRelativelyFreeDivisor_nsmul_of_isRelativelyNef`
on the singleton polytope), so its floor-section algebra is of finite type (over the Stein
factorization `Y ⟶ Y' ⟶ S`, whose middle term `Y'` is normal and finite over `S`); on the common
resolution `p : W ⟶ X`, `q : W ⟶ Y` the comparison `p^*(K_X + Δ) - q^*(K_Y + φ_* Δ)` is
effective and `q`-exceptional, so the floor sections of the two adjoints are identified through
the function field of `W` (`MMP.Mori.mem_divisorialSubmodule_roundDown_iff_of_eq_pullback_add`),
compatibly with the constants from `S`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
-/

namespace MMP.FourfoldProofs.FourfoldProjectiveThreefoldF3Proof

open CategoryTheory AlgebraicGeometry Opposite MMP.Fourfold MMP.Mori MMP.Flips

section

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### Divisor arithmetic -/

section Arithmetic

variable {X Y : Scheme.{0}}

/-- The birational transform commutes with a change of coefficients along an additive map. -/
private theorem transformDivisor_mapCoeffsAddMonoidHom {R S : Type*} [AddCommGroup R]
    [AddCommGroup S] (f : R →+ S) (φ : X.RationalMap Y) (D : DivisorWithCoeffs R X) :
    MMP.Mori.RationalMap.transformDivisor φ (DivisorWithCoeffs.mapCoeffsAddMonoidHom f D) =
      DivisorWithCoeffs.mapCoeffsAddMonoidHom f (MMP.Mori.RationalMap.transformDivisor φ D) := by
  classical
  induction D using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add D D' h h' => simp only [map_add, h, h']
  | single P r =>
    have h1 : ∀ (Z : Scheme.{0}) (Q : MMP.Mori.PrimeDivisor Z),
        DivisorWithCoeffs.mapCoeffsAddMonoidHom f (Finsupp.single Q r) =
          Finsupp.single Q (f r) := fun Z Q => by
      rw [DivisorWithCoeffs.mapCoeffsAddMonoidHom_apply]
      exact Finsupp.mapRange_single
    rw [h1, MMP.Mori.RationalMap.transformDivisor_single,
      MMP.Mori.RationalMap.transformDivisor_single]
    rcases MMP.Mori.RationalMap.transformPrimeDivisor φ P with _ | Q
    · exact (map_zero (DivisorWithCoeffs.mapCoeffsAddMonoidHom f)).symm
    · exact (h1 Y Q).symm

private theorem transformDivisor_toRDivisor (φ : X.RationalMap Y) (D : Divisor X) :
    MMP.Mori.RationalMap.transformDivisor φ (Divisor.toRDivisor D) =
      Divisor.toRDivisor (MMP.Mori.RationalMap.transformDivisor φ D) :=
  transformDivisor_mapCoeffsAddMonoidHom _ φ D

private theorem transformDivisor_qToRDivisor (φ : X.RationalMap Y) (D : QDivisor X) :
    MMP.Mori.RationalMap.transformDivisor φ (QDivisor.toRDivisor D) =
      QDivisor.toRDivisor (MMP.Mori.RationalMap.transformDivisor φ D) :=
  transformDivisor_mapCoeffsAddMonoidHom _ φ D

/-- The birational transform of an effective divisor is effective. -/
private theorem transformDivisor_nonneg {R : Type*} [AddCommMonoid R] [PartialOrder R]
    [IsOrderedAddMonoid R] (φ : X.RationalMap Y) {D : DivisorWithCoeffs R X} (hD : 0 ≤ D) :
    0 ≤ MMP.Mori.RationalMap.transformDivisor φ D := by
  classical
  rw [MMP.Mori.RationalMap.transformDivisor, DivisorWithCoeffs.mapPrimeDivisors,
    Finsupp.liftAddHom_apply]
  refine Finset.sum_nonneg fun P _ => ?_
  dsimp only
  rcases MMP.Mori.RationalMap.transformPrimeDivisor φ P with _ | Q
  · simp
  · exact Finsupp.single_nonneg.mpr (hD P)

private theorem transformDivisor_mono {R : Type*} [AddCommGroup R] [PartialOrder R]
    [IsOrderedAddMonoid R] (φ : X.RationalMap Y) {D D' : DivisorWithCoeffs R X} (hD : D ≤ D') :
    MMP.Mori.RationalMap.transformDivisor φ D ≤ MMP.Mori.RationalMap.transformDivisor φ D' := by
  have := transformDivisor_nonneg φ (sub_nonneg.mpr hD)
  rwa [map_sub, sub_nonneg] at this

private theorem qToRDivisor_nonneg {D : QDivisor X} (hD : 0 ≤ D) : 0 ≤ QDivisor.toRDivisor D :=
  fun P => by
    change (0 : ℝ) ≤ ((D P : ℚ) : ℝ)
    exact_mod_cast hD P

private theorem nonneg_of_qToRDivisor_nonneg {D : QDivisor X} (hD : 0 ≤ QDivisor.toRDivisor D) :
    0 ≤ D := fun P => by
  have : (0 : ℝ) ≤ ((D P : ℚ) : ℝ) := hD P
  exact_mod_cast this

/-- On a `ℚ`-factorial variety every `ℝ`-divisor is `ℝ`-Cartier: each prime divisor has a Cartier
multiple, and `D = ∑_P (D_P / m_P) · (m_P P)`. -/
private theorem isRCartier_of_isQFactorial [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} (hX : IsQFactorial sX) (D : RDivisor X) : RDivisor.IsRCartier D := by
  classical
  choose m hm hmC using fun P : MMP.Mori.PrimeDivisor X => hX.2 (Finsupp.single P 1)
  let e := D.support.equivFin
  refine ⟨D.support.card, fun i => D (e.symm i) / m (e.symm i),
    fun i => ((m (e.symm i) : ℕ) : ℤ) • Finsupp.single (e.symm i : MMP.Mori.PrimeDivisor X) 1,
    fun i => hmC _, fun Γ => ?_⟩
  let G : MMP.Mori.PrimeDivisor X → ℝ := fun x => if x = Γ then D x else 0
  have key : ∀ i, D (e.symm i) / m (e.symm i) *
      ((DivisorWithCoeffs.coeff (((m (e.symm i) : ℕ) : ℤ) •
        Finsupp.single (e.symm i : MMP.Mori.PrimeDivisor X) (1 : ℤ)) Γ : ℤ) : ℝ) =
        (fun x : D.support => G x.1) (e.symm i) := by
    intro i
    have hmx : ((m (e.symm i) : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (hm _).ne'
    rw [DivisorWithCoeffs.coeff_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
    simp only [G]
    by_cases h1 : (e.symm i : MMP.Mori.PrimeDivisor X) = Γ
    · rw [ite_eq_left h1, ite_eq_left h1]
      push_cast
      field_simp
    · rw [ite_eq_right h1, ite_eq_right h1]
      simp
  rw [Fintype.sum_equiv e.symm _ (fun x : D.support => G x.1) key,
    Finset.sum_coe_sort D.support G]
  simp only [G, Finset.sum_ite_eq', DivisorWithCoeffs.coeff_apply]
  split_ifs with h
  · rfl
  · exact Finsupp.notMem_support_iff.mp h

open Classical in
/-- The coefficients of a finite real combination of prime divisors. -/
private theorem coeff_sum_smul_single {n : ℕ} (PX : Fin n → MMP.Mori.PrimeDivisor X)
    (t : Fin n → ℝ) (P : MMP.Mori.PrimeDivisor X) :
    (∑ i, t i • Finsupp.single (PX i) (1 : ℝ) : RDivisor X).coeff P =
      ∑ i, if PX i = P then t i else 0 := by
  classical
  rw [DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  split_ifs <;> simp

private theorem coeff_sum_smul_single_self {n : ℕ} {PX : Fin n → MMP.Mori.PrimeDivisor X}
    (hPX : Function.Injective PX) (t : Fin n → ℝ) (j : Fin n) :
    (∑ i, t i • Finsupp.single (PX i) (1 : ℝ) : RDivisor X).coeff (PX j) = t j := by
  classical
  rw [coeff_sum_smul_single, Finset.sum_eq_single j (fun i _ hij => ite_eq_right (hPX.ne hij))
    (by simp), ite_eq_left rfl]

/-- A real divisor supported on the image of an enumeration `PX` of a finite set of primes is the
combination of the `PX i` with its own coefficients. -/
private theorem eq_sum_smul_single {n : ℕ} {PX : Fin n → MMP.Mori.PrimeDivisor X}
    (hPX : Function.Injective PX) (Ξ : RDivisor X) (hΞ : ∀ P, Ξ P ≠ 0 → ∃ i, PX i = P) :
    Ξ = ∑ i, Ξ (PX i) • Finsupp.single (PX i) (1 : ℝ) := by
  classical
  ext P
  change Ξ.coeff P = (∑ i, Ξ (PX i) • Finsupp.single (PX i) (1 : ℝ) : RDivisor X).coeff P
  by_cases h : ∃ i, PX i = P
  · obtain ⟨j, rfl⟩ := h
    rw [coeff_sum_smul_single_self hPX]
    rfl
  · have h0 : Ξ P = 0 := by
      by_contra h'
      exact h (hΞ P h')
    rw [coeff_sum_smul_single, DivisorWithCoeffs.coeff_apply, h0]
    exact (Finset.sum_eq_zero fun i _ => ite_eq_right fun e => h ⟨i, e⟩).symm

/-- An `ℝ`-Cartier divisor in the sense of `MMP.Fourfold.RDivisor.IsRCartier` is a real
combination of Cartier divisors in the sense of `MMP.Flips.IsCartierCombination`. -/
private theorem isCartierCombination_of_isRCartier [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X] {D : RDivisor X} (h : RDivisor.IsRCartier D) :
    MMP.Flips.IsCartierCombination D := by
  obtain ⟨m, r, C, hC, hD⟩ := h
  refine ⟨m, r, C, hC, ?_⟩
  ext P
  rw [hD P, DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul]
  rfl

end Arithmetic

/-! ### Coefficients along a common resolution of a contraction -/

section Transfer

/-- For an inverse `h` of `p`, the composite `p ∘ h` is the identity. -/
private theorem compHom_eq_id_of_isInverse {X W : Scheme.{0}} [IsReduced X] [IsReduced W]
    [IsSeparated (X ↘ ⊤_ Scheme)] {p : W ⟶ X} {h : X.RationalMap W}
    (hinv : MMP.Mori.RationalMap.IsInverse p.toRationalMap h) :
    h.compHom p = Scheme.Hom.toRationalMap (𝟙 X) := by
  obtain ⟨e, he1, he2⟩ := id hinv
  have hs : e.source.ι ≫ p = e.iso.hom ≫ e.target.ι :=
    ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
      (Scheme.PartialMap.toRationalMap_eq_iff.mp he1)).symm
  rw [← he2, ← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff,
    Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
  change e.iso.inv ≫ e.source.ι ≫ p = e.target.ι ≫ 𝟙 X
  rw [hs, Iso.inv_hom_id_assoc, Category.comp_id]

/-- **The point over a source prime.** Let `p : W ⟶ X` be proper with inverse `h` and
`q : W ⟶ Y` with `q ∘ h = φ`. If `φ_* Q = F`, a point of `W` lies over `η_Q` and over `η_F`: the
image of `η_Q` under a representative of `h` defined there. -/
private theorem exists_apply_eq_genericPoint_of_isInverse {X Y W : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsReduced W] [IsSeparated (X ↘ ⊤_ Scheme)]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {p : W ⟶ X} [IsProper p] {q : W ⟶ Y} {h : X.RationalMap W}
    {φ : X.RationalMap Y} (hinv : MMP.Mori.RationalMap.IsInverse p.toRationalMap h)
    (hq : h.compHom q = φ) {Q : MMP.Mori.PrimeDivisor X} {F : MMP.Mori.PrimeDivisor Y}
    (hQ : MMP.Mori.RationalMap.transformPrimeDivisor φ Q = some F) :
    ∃ w : W, q w = F.genericPoint ∧ p w = Q.genericPoint := by
  have hhp := compHom_eq_id_of_isInverse hinv
  have hdom : Q.genericPoint ∈ h.domain :=
    MMP.Flips.RationalMap.mem_domain_of_coheight_le_one (𝟙 X) p h hhp
      Q.coheight_genericPoint.le
  obtain ⟨g', hg'Q, hg'⟩ := Scheme.RationalMap.mem_domain.mp hdom
  refine ⟨g'.hom ⟨Q.genericPoint, hg'Q⟩,
    (MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some hQ (g'.compHom q)
      (by rw [Scheme.RationalMap.compHom_toRationalMap, hg', hq]) hg'Q).symm, ?_⟩
  have h1 : (g'.compHom p).toRationalMap = (Scheme.PartialMap.id X).toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg', hhp]
  have h2 := MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq
    (g := g'.compHom p) (g' := Scheme.PartialMap.id X) h1 hg'Q trivial
  change (g'.hom ≫ p) ⟨_, hg'Q⟩ = (X.topIso.hom ≫ 𝟙 X) ⟨_, trivial⟩ at h2
  refine (Scheme.Hom.comp_apply _ _ _).symm.trans (h2.trans ?_)
  rw [Category.comp_id, Scheme.topIso_hom]
  rfl

/-- Two points of `W` over the generic point of a prime divisor of `Y`, along a birational
morphism `q : W ⟶ Y` of normal integral schemes, coincide. -/
private theorem eq_of_apply_eq_genericPoint {W Y : Scheme.{0}} [IsIntegral W] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {q : W ⟶ Y} [IsSeparated q]
    (hqb : IsBirationalMorphism q) {F : MMP.Mori.PrimeDivisor Y} {w₁ w₂ : W}
    (h₁ : q w₁ = F.genericPoint) (h₂ : q w₂ = F.genericPoint) : w₁ = w₂ := by
  have := hqb.isDominant
  have := F.isDiscreteValuationRing_localRing
  have : ValuationRing (Y.presheaf.stalk (q w₁)) := by rw [h₁]; infer_instance
  have := MMP.Fourfold.isIso_stalkMap_of_map_eq_genericPoint hqb h₁
  have := MMP.Fourfold.isIso_stalkMap_of_map_eq_genericPoint hqb h₂
  exact MMP.Positivity.eq_of_isIso_stalkMap q hqb.functionFieldMap_bijective (h₂.trans h₁.symm)

/-- **The source prime of a target prime.** For a birational contraction `φ = q ∘ p⁻¹`, every
prime divisor `E` of `W` over a prime divisor `F` of `Y` lies over a prime divisor `Q` of `X`
with `φ_* Q = F`, the only such prime, so that `(φ_* D)(F) = D(Q)` for every divisor `D`. -/
private theorem exists_primeDivisor_of_apply_eq_genericPoint {X Y W : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [IsIntegral W] [IsSeparated (X ↘ ⊤_ Scheme)] [IsSeparated (Y ↘ ⊤_ Scheme)]
    {p : W ⟶ X} [IsProper p] {q : W ⟶ Y} [IsSeparated q] (hqb : IsBirationalMorphism q)
    {h : X.RationalMap W} {φ : X.RationalMap Y}
    (hinv : MMP.Mori.RationalMap.IsInverse p.toRationalMap h) (hq : h.compHom q = φ)
    (hcontr : ∀ F : MMP.Mori.PrimeDivisor Y, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F)
    {E : MMP.Mori.PrimeDivisor W} {F : MMP.Mori.PrimeDivisor Y}
    (hE : q E.genericPoint = F.genericPoint) :
    ∃ Q : MMP.Mori.PrimeDivisor X, p E.genericPoint = Q.genericPoint ∧
      ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X),
        MMP.Mori.RationalMap.transformDivisor φ D F = D Q := by
  obtain ⟨Q, hQ⟩ : ∃ Q, MMP.Mori.RationalMap.transformPrimeDivisor φ Q = some F := by
    have := hcontr F
    simpa [MMP.Flips.RationalMap.IsInverseExceptional] using this
  obtain ⟨w, hwq, hwp⟩ := exists_apply_eq_genericPoint_of_isInverse hinv hq hQ
  have hw : E.genericPoint = w := eq_of_apply_eq_genericPoint hqb hE hwq
  refine ⟨Q, hw ▸ hwp, fun D => ?_⟩
  refine MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hQ (fun Q' hQ' => ?_) D
  obtain ⟨w', hwq', hwp'⟩ := exists_apply_eq_genericPoint_of_isInverse hinv hq hQ'
  have hww : w = w' := eq_of_apply_eq_genericPoint hqb hwq hwq'
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hwp'.symm.trans (hww ▸ hwp))

/-- **The comparison of a contraction is exceptional.** Let `φ = q ∘ p⁻¹ : X ⤏ Y` be a
birational contraction with a common resolution `p : W ⟶ X`, `q : W ⟶ Y`. For an `ℝ`-Cartier
`D` on `X` and `D' = φ_* D`, the push-forward along `q` of `p^*D - q^*D'` vanishes: at a prime
divisor `E` of `W` over a prime `F` of `Y`, both pull-backs have the coefficient of the source
prime of `F` in `D`. -/
private theorem transformDivisor_sub_eq_zero_of_isInverse {X Y W : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    [IsSeparated (X ↘ ⊤_ Scheme)] [IsSeparated (Y ↘ ⊤_ Scheme)]
    {p : W ⟶ X} [IsProper p] {q : W ⟶ Y} [IsSeparated q] (hpb : IsBirationalMorphism p)
    (hqb : IsBirationalMorphism q) {h : X.RationalMap W} {φ : X.RationalMap Y}
    (hinv : MMP.Mori.RationalMap.IsInverse p.toRationalMap h) (hq : h.compHom q = φ)
    (hcontr : ∀ F : MMP.Mori.PrimeDivisor Y, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F)
    {D : RDivisor X} {D' : RDivisor Y} (hD' : MMP.Mori.RationalMap.transformDivisor φ D = D')
    {P Q : RDivisor W} (hP : MMP.Flips.IsRCartierPullback p D P)
    (hQ : MMP.Flips.IsRCartierPullback q D' Q) :
    MMP.Mori.RationalMap.transformDivisor (X := W) q.toRationalMap (P - Q) = 0 := by
  rw [MMP.Mori.RationalMap.transformDivisor]
  refine MMP.Fourfold.mapPrimeDivisors_eq_zero_of_forall _ fun E F hEF => ?_
  have hE := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff q E F).mp hEF
  obtain ⟨Q₀, hpE, hφ⟩ :=
    exists_primeDivisor_of_apply_eq_genericPoint hqb hinv hq hcontr hE
  have := MMP.Fourfold.isIso_stalkMap_of_map_eq_genericPoint hpb hpE
  have := MMP.Fourfold.isIso_stalkMap_of_map_eq_genericPoint hqb hE
  have h1 := MMP.Fourfold.coeff_eq_of_isRCartierPullback E Q₀ hpE hP
  have h2 := MMP.Fourfold.coeff_eq_of_isRCartierPullback E F hE hQ
  have h3 : D'.coeff F = D.coeff Q₀ := by rw [← hD']; exact hφ D
  change P.coeff E - Q.coeff E = 0
  rw [h1, h2, h3, sub_self]

end Transfer

/-! ### Stable base primes and fixed parts near `Δ` -/

section Neighbourhoods

/-- Membership in the smallest rational affine hull, in the coordinates of an enumeration `PX` of
a set of primes containing the support of `Δ`. -/
private theorem mem_rationalAffineHull_of_isInSmallestRationalAffineHull {X : Scheme.{0}}
    {n : ℕ} (PX : Fin n → MMP.Mori.PrimeDivisor X)
    {Δ Ξ : RDivisor X} (h : IsInSmallestRationalAffineHull Δ Ξ) :
    (fun i => Ξ (PX i)) ∈ rationalAffineHull (fun i => Δ (PX i)) := by
  classical
  intro f hf
  let c : MMP.Mori.PrimeDivisor X →₀ ℚ := ∑ j, Finsupp.single (PX j) (f.1 j)
  have hsum : ∀ Θ : RDivisor X, (c.sum fun P cP => (cP : ℝ) * Θ.coeff P) =
      ∑ j, (f.1 j : ℝ) * Θ (PX j) := by
    intro Θ
    change (∑ j, Finsupp.single (PX j) (f.1 j)).sum _ = _
    rw [← Finsupp.sum_finsetSum_index (fun _ => by simp) (fun _ _ _ => by push_cast; ring)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finsupp.sum_single_index (by simp)]
    rfl
  have h1 := h.2 c (-f.2) (by
    rw [hsum]
    have : ratAffineForm f (fun i => Δ (PX i)) = 0 := hf
    simp only [ratAffineForm] at this
    push_cast
    linarith)
  rw [hsum] at h1
  simp only [ratAffineForm]
  push_cast at h1
  linarith

variable {X Y W S : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
  [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral W]
  [IsLocallyNoetherian W] [IsNormal W] {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)}
  [QuasiCompact sY] {sS : S ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)} {g : X ⟶ S} {πY : Y ⟶ S}

/-- **The two neighbourhood statements.** For the log terminal model `φ : X ⤏ Y` of
`(X, Δ = A + B)` with its common resolution `p : W ⟶ X`, `q : W ⟶ Y`, the stable base primes of
`K + Δ` persist near `Δ` in the span of the primes of `Δ`, and the fixed primes of the divisible
multiples of `K + Ξ` near `Δ` in its smallest rational affine hull are stable base primes of
`K + Δ`: this is `isInRelativeDivisorialStableBase_uniformity_of_isBirationalContraction` for
the family `D_t = K + ∑ tᵢ Pᵢ`, with `Pᵢ` the primes of `K` and `Δ`, and the big core `φ_* A`. -/
private theorem exists_stableBase_and_fixedParts
    {K : Divisor X} {A : QDivisor X} {B : RDivisor X} {φ : X.RationalMap Y} {p : W ⟶ X}
    {q : W ⟶ Y} {h : X.RationalMap W} {GX GY : RDivisor W}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    (hg : g ≫ sS = sX) (hXQ : IsQFactorial sX)
    (hA0 : 0 ≤ A) (hA : A.IsRelativelyBig g) (hB0 : 0 ≤ B)
    (hWM : IsNefWeakModel sX sY sS g πY K (QDivisor.toRDivisor A + B) φ)
    (hKY : ∃ m : ℕ,
      MMP.Mori.Divisor.IsCanonicalDivisor sY m (MMP.Mori.RationalMap.transformDivisor φ K))
    (hYQ : IsQFactorial sY)
    (hYklt : IsRealKltPair sY
      (MMP.Mori.RationalMap.transformDivisor φ (QDivisor.toRDivisor A + B)))
    (hWv : MMP.Mori.IsVariety ℂ sW) (hpX : p ≫ sX = sW) (hqY : q ≫ sY = sW)
    (hpproj : IsProjectiveMorphism p) (hqproj : IsProjectiveMorphism q)
    (hpb : IsBirationalMorphism p) (hqb : IsBirationalMorphism q)
    (hinv : MMP.Mori.RationalMap.IsInverse p.toRationalMap h) (hhq : h.compHom q = φ)
    (hGX : MMP.Flips.IsRCartierPullback p
      (MMP.Flips.logCanonicalDivisor K (QDivisor.toRDivisor A + B)) GX)
    (hGY : MMP.Flips.IsRCartierPullback q
      (MMP.Flips.logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ K)
        (MMP.Mori.RationalMap.transformDivisor φ (QDivisor.toRDivisor A + B))) GY)
    (hE0 : ∀ P, 0 ≤ (GX - GY).coeff P) :
    (∃ ε : ℝ, 0 < ε ∧ ∀ Ξ : RDivisor X, Ξ.support ⊆ (QDivisor.toRDivisor A + B).support →
      0 ≤ Ξ → IsRealKltPair sX Ξ →
      (∀ P, |Ξ.coeff P - (QDivisor.toRDivisor A + B).coeff P| < ε) →
      ∀ G : MMP.Mori.PrimeDivisor X,
        IsInRelativeDivisorialStableBase g
          (MMP.Flips.logCanonicalDivisor K (QDivisor.toRDivisor A + B)) G →
          IsInRelativeDivisorialStableBase g (MMP.Flips.logCanonicalDivisor K Ξ) G) ∧
    (∃ ε : ℝ, 0 < ε ∧ ∃ r : ℕ, 0 < r ∧ ∀ Ξ : RDivisor X,
      IsInSmallestRationalAffineHull (QDivisor.toRDivisor A + B) Ξ →
      0 ≤ Ξ → IsRealKltPair sX Ξ →
      (∀ P, |Ξ.coeff P - (QDivisor.toRDivisor A + B).coeff P| < ε) →
      ∀ k : ℕ, 0 < k → ∀ D : Divisor X, D.IsCartier →
        (∀ P, (k : ℝ) / r * (MMP.Flips.logCanonicalDivisor K Ξ).coeff P = D.coeff P) →
        ∀ G : MMP.Mori.PrimeDivisor X, 0 < relativeFixedMultiplicity g ((r : ℤ) • D) G →
          IsInRelativeDivisorialStableBase g
            (MMP.Flips.logCanonicalDivisor K (QDivisor.toRDivisor A + B)) G) := by
  classical
  set Δ : RDivisor X := QDivisor.toRDivisor A + B with hΔdef
  -- instances
  have hXv := hWM.isNormalVariety_source
  have hYv := hWM.isNormalVariety_target
  have := hYv.1
  have := hWv
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  have := isSeparated_toTerminal_of_isNormalVariety hXv
  have := isSeparated_toTerminal_of_isNormalVariety hYv
  have : IsProper p := isProper_of_isProjectiveMorphism p hpproj
  have : IsSeparated q := by
    have : IsSeparated (q ≫ sY) := by rw [hqY]; infer_instance
    exact IsSeparated.of_comp q sY
  have : IsDominant p := hpb.isDominant
  have : IsDominant q := hqb.isDominant
  -- the coordinates: the primes of `K` and of `Δ`
  set KY := MMP.Mori.RationalMap.transformDivisor φ K with hKYdef
  let Sset : Finset (MMP.Mori.PrimeDivisor X) := K.support ∪ Δ.support
  let e := Sset.equivFin
  let PX : Fin Sset.card → MMP.Mori.PrimeDivisor X := fun i => (e.symm i).1
  have hPX : Function.Injective PX := fun i j hij => e.symm.injective (Subtype.ext hij)
  have hPXmem : ∀ P ∈ Sset, ∃ i, PX i = P := fun P hP => ⟨e ⟨P, hP⟩, by simp [PX]⟩
  let D : (Fin Sset.card → ℝ) → RDivisor X := fun t =>
    Divisor.toRDivisor K + ∑ i, t i • Finsupp.single (PX i) (1 : ℝ)
  let δ : Fin Sset.card → ℝ := fun i => Δ (PX i)
  have hΔsum : Δ = ∑ i, δ i • Finsupp.single (PX i) (1 : ℝ) :=
    eq_sum_smul_single hPX Δ fun P hP => hPXmem P
      (Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr hP))
  have hDδ : D δ = MMP.Flips.logCanonicalDivisor K Δ := by
    change Divisor.toRDivisor K + ∑ i, δ i • Finsupp.single (PX i) (1 : ℝ) =
      Divisor.toRDivisor K + Δ
    rw [← hΔsum]
  -- the family on `X`
  let a : Fin Sset.card → (Fin Sset.card → ℚ) × ℚ := fun i => (Pi.single i 1, (K (PX i) : ℚ))
  have hDcoeff : ∀ t i, (D t).coeff (PX i) = ratAffineForm (a i) t := by
    intro t i
    simp only [D, a, ratAffineForm, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor,
      coeff_sum_smul_single_self hPX]
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
    simp only [Pi.single_eq_same, Rat.cast_one, one_mul, Rat.cast_intCast,
      DivisorWithCoeffs.coeff_apply]
    ring
  have hDsupp : ∀ t, ↑(D t).support ⊆ Set.range PX := by
    intro t P hP
    by_contra hPr
    have hK0 : K P = 0 := by
      by_contra hK
      exact hPr (hPXmem P (Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr hK)))
    apply Finsupp.mem_support_iff.mp hP
    have hK0' : (K.coeff P : ℝ) = 0 := by rw [DivisorWithCoeffs.coeff_apply, hK0, Int.cast_zero]
    change (Divisor.toRDivisor K + ∑ i, t i • Finsupp.single (PX i) (1 : ℝ)).coeff P = 0
    rw [DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, hK0', zero_add,
      coeff_sum_smul_single]
    exact Finset.sum_eq_zero fun i _ => ite_eq_right fun e => hPr ⟨i, e⟩
  have hDc : ∀ t, RDivisor.IsRCartier (D t) := fun t => isRCartier_of_isQFactorial hXQ (D t)
  -- the family on `Y`
  let Γ : (Fin Sset.card → ℝ) → RDivisor Y := fun t =>
    MMP.Mori.RationalMap.transformDivisor φ (∑ i, t i • Finsupp.single (PX i) (1 : ℝ))
  let SY : Finset (MMP.Mori.PrimeDivisor Y) :=
    Finset.univ.biUnion fun i => (MMP.Mori.RationalMap.transformPrimeDivisor φ (PX i)).toFinset
  let eY := SY.equivFin
  let PY : Fin SY.card → MMP.Mori.PrimeDivisor Y := fun j => (eY.symm j).1
  let b : Fin SY.card → (Fin Sset.card → ℚ) × ℚ := fun j =>
    (fun i => if MMP.Mori.RationalMap.transformPrimeDivisor φ (PX i) = some (PY j) then 1 else 0,
      0)
  have hΓcoeffP : ∀ t (F : MMP.Mori.PrimeDivisor Y), (Γ t).coeff F =
      ∑ i, if MMP.Mori.RationalMap.transformPrimeDivisor φ (PX i) = some F then t i else 0 := by
    intro t F
    simp only [Γ, map_sum, DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← MMP.Mori.RationalMap.transformDivisorₗ_apply ℝ, map_smul,
      MMP.Mori.RationalMap.transformDivisorₗ_apply, MMP.Mori.RationalMap.transformDivisor_single]
    rcases hi : MMP.Mori.RationalMap.transformPrimeDivisor φ (PX i) with _ | Q
    · simp
    · by_cases hQ : Q = F
      · subst hQ
        simp
      · simp [hQ]
  have hΓcoeff : ∀ t j, (Γ t).coeff (PY j) = ratAffineForm (b j) t := by
    intro t j
    rw [hΓcoeffP]
    simp only [b, ratAffineForm, Rat.cast_zero, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  have hΓsupp : ∀ t, ↑(Γ t).support ⊆ Set.range PY := by
    intro t F hF
    have hF' : (Γ t).coeff F ≠ 0 := Finsupp.mem_support_iff.mp hF
    rw [hΓcoeffP] at hF'
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hF'
    have hiF : MMP.Mori.RationalMap.transformPrimeDivisor φ (PX i) = some F := by
      by_contra hne
      exact hi (ite_eq_right hne)
    have hFS : F ∈ SY := Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp [hiF]⟩
    exact ⟨eY ⟨F, hFS⟩, by simp [PY]⟩
  have hD' : ∀ t, MMP.Mori.RationalMap.transformDivisor φ (D t) = Divisor.toRDivisor KY + Γ t :=
    fun t => by simp only [D, Γ, map_add, transformDivisor_toRDivisor, KY]
  have hYc : ∀ t, RDivisor.IsRCartier (Divisor.toRDivisor KY + Γ t) := fun t =>
    isRCartier_of_isQFactorial hYQ _
  -- the pull-backs
  have hPex : ∀ t, ∃ G, MMP.Flips.IsRCartierPullback p (D t) G := fun t =>
    (MMP.Flips.existsUnique_isRCartierPullback p
      (isCartierCombination_of_isRCartier (hDc t))).exists
  choose P hP using hPex
  have hQex : ∀ t, ∃ G, MMP.Flips.IsRCartierPullback q (Divisor.toRDivisor KY + Γ t) G :=
    fun t => (MMP.Flips.existsUnique_isRCartierPullback q
      (isCartierCombination_of_isRCartier (hYc t))).exists
  choose Q hQ using hQex
  have hqE : ∀ t,
      MMP.Mori.RationalMap.transformDivisor (X := W) q.toRationalMap (P t - Q t) = 0 :=
    fun t => transformDivisor_sub_eq_zero_of_isInverse hpb hqb hinv hhq
      hWM.not_isInverseExceptional (hD' t) (hP t) (hQ t)
  -- the data at `δ`
  have hΓδ : Γ δ = MMP.Mori.RationalMap.transformDivisor φ Δ := by
    change MMP.Mori.RationalMap.transformDivisor φ (∑ i, δ i • Finsupp.single (PX i) (1 : ℝ)) = _
    rw [← hΔsum]
  have hPδ : P δ = GX := MMP.Flips.IsRCartierPullback.eq p (hP δ) (by rwa [hDδ])
  have hQδ : Q δ = GY := MMP.Flips.IsRCartierPullback.eq q (hQ δ) (by rwa [hΓδ])
  have hEδ : 0 ≤ P δ - Q δ := by
    rwa [hPδ, hQδ, Finsupp.le_def]
  have hΓ0 : 0 ≤ Γ δ := by
    rw [hΓδ]
    exact transformDivisor_nonneg φ (add_nonneg (qToRDivisor_nonneg hA0) hB0)
  have hΓklt : IsRealKltPair sY (Γ δ) := by rwa [hΓδ]
  obtain ⟨hG0, -, hGbig⟩ := isRelativelyBig_transformDivisor_of_isBirationalContraction sX sY sS
    hXv hX hYQ hWM.isProjectiveVariety_target hS g πY hg hWM.comp_eq_target φ hWM.isBirational
    hWM.isOver hWM.not_isInverseExceptional A hA0 (isQCartier_of_isQFactorial sX hXQ A) hA
  have hGΓ : QDivisor.toRDivisor (MMP.Mori.RationalMap.transformDivisor φ A) ≤ Γ δ := by
    rw [hΓδ, hΔdef, map_add, transformDivisor_qToRDivisor]
    exact le_add_of_nonneg_right (transformDivisor_nonneg φ hB0)
  have hnef : MMP.Flips.IsRelativelyNef ℂ sY πY (Divisor.toRDivisor KY + Γ δ) := by
    rw [hΓδ]
    exact hWM.isRelativelyNef
  obtain ⟨h1, r, hr, h2⟩ := isInRelativeDivisorialStableBase_uniformity_of_isBirationalContraction
    (sZ := sS) (sT := sW) hXQ hX hYQ hWM.isProjectiveVariety_target hS ⟨hWv, inferInstance⟩
    g πY hg hWM.comp_eq_target φ hWM.isBirational hWM.isOver hWM.not_isInverseExceptional
    p q hpproj hqproj hpb hqb hpX hqY h hinv hhq
    (V := Set.univ) ⟨∅, by simp⟩ D PX a hDcoeff hDsupp (fun t _ => hDc t)
    KY hKY Γ PY b hΓcoeff hΓsupp (fun t _ => hD' t) P Q (fun t _ => hP t) (fun t _ => hQ t)
    (fun t _ => hqE t) (Set.mem_univ δ) hΓ0 hΓklt _ hG0 hGbig hGΓ hEδ hnef
  rw [nhdsWithin_univ, Metric.eventually_nhds_iff] at h1
  obtain ⟨ε₁, hε₁, h1⟩ := h1
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h2
  obtain ⟨ε₂, hε₂, h2⟩ := h2
  -- the coordinates of a divisor supported on `Δ`
  have hcoord : ∀ Ξ : RDivisor X, Ξ.support ⊆ Δ.support →
      D (fun i => Ξ (PX i)) = MMP.Flips.logCanonicalDivisor K Ξ := by
    intro Ξ hΞ
    change Divisor.toRDivisor K + ∑ i, Ξ (PX i) • Finsupp.single (PX i) (1 : ℝ) =
      Divisor.toRDivisor K + Ξ
    rw [← eq_sum_smul_single hPX Ξ fun P hP => hPXmem P
      (Finset.mem_union_right _ (hΞ (Finsupp.mem_support_iff.mpr hP)))]
  have hdist : ∀ (Ξ : RDivisor X) (ε : ℝ), 0 < ε → (∀ P, |Ξ.coeff P - Δ.coeff P| < ε) →
      dist (fun i => Ξ (PX i)) δ < ε := fun Ξ ε hε hΞ =>
    (dist_pi_lt_iff hε).mpr fun i => by rw [Real.dist_eq]; exact hΞ (PX i)
  refine ⟨⟨ε₁, hε₁, fun Ξ hΞ _ _ hclose G hG => ?_⟩,
    ⟨ε₂, hε₂, r, hr, fun Ξ hΞ _ _ hclose k hk Dc hDc' hDk G hG => ?_⟩⟩
  · have := h1 (hdist Ξ ε₁ hε₁ hclose) G (by rwa [hDδ])
    rwa [hcoord Ξ hΞ] at this
  · have hmem := mem_rationalAffineHull_of_isInSmallestRationalAffineHull PX hΞ
    have hrk : Divisor.toRDivisor ((r : ℤ) • Dc) = (k : ℝ) • D (fun i => Ξ (PX i)) := by
      rw [hcoord Ξ hΞ.1]
      ext P
      have hkP := hDk P
      simp only [DivisorWithCoeffs.coeff_apply] at hkP
      have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
      change ((((r : ℤ) • Dc) P : ℤ) : ℝ) = (k : ℝ) * (MMP.Flips.logCanonicalDivisor K Ξ) P
      rw [Finsupp.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast, ← hkP]
      field_simp
    have := h2 (hdist Ξ ε₂ hε₂ hclose) hmem k hk Dc hDc' hrk G hG
    rwa [hDδ] at this

end Neighbourhoods

/-! ### Floor-section algebras -/

section Floor

variable {X : Scheme.{0}}

/-- `mK + ⌊mΔ⌋ = ⌊m(K + Δ)⌋` for an integral divisor `K`. -/
private theorem nsmul_add_roundDown_eq (K : Divisor X) (Δ : QDivisor X) (m : ℕ) :
    m • K + DivisorWithCoeffs.roundDown ((m : ℚ) • Δ) =
      DivisorWithCoeffs.roundDown ((m : ℚ) • (Divisor.toQDivisor K + Δ)) := by
  ext E
  simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_roundDown,
    DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor, smul_eq_mul, nsmul_eq_mul]
  have h : (m : ℚ) * (K.coeff E : ℚ) = (((m : ℤ) * K.coeff E : ℤ) : ℚ) := by push_cast; ring
  rw [mul_add, h, Int.floor_intCast_add]

/-- `⌊aM⌋ + ⌊bM⌋ ≤ ⌊(a + b)M⌋`. -/
private theorem roundDown_add_le_roundDown (M : QDivisor X) (a b : ℕ) :
    DivisorWithCoeffs.roundDown ((a : ℚ) • M) + DivisorWithCoeffs.roundDown ((b : ℚ) • M) ≤
      DivisorWithCoeffs.roundDown (((a + b : ℕ) : ℚ) • M) := by
  rw [Finsupp.le_def]
  intro E
  rw [← DivisorWithCoeffs.coeff_apply, ← DivisorWithCoeffs.coeff_apply,
    DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_roundDown,
    DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_roundDown,
    DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_smul,
    Nat.cast_add, add_smul]
  exact Int.le_floor_add _ _

private theorem zero_le_roundDown_natCast_zero (M : QDivisor X) :
    (0 : Divisor X) ≤ DivisorWithCoeffs.roundDown (((0 : ℕ) : ℚ) • M) := by
  rw [Finsupp.le_def]
  intro E
  rw [← DivisorWithCoeffs.coeff_apply, ← DivisorWithCoeffs.coeff_apply,
    DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul]
  simp [DivisorWithCoeffs.coeff_zero]

variable [IsLocallyNoetherian X] [IsNormal X]

/-- The floor-section algebra `⊕_{m ≥ 0} H⁰(V, 𝒪_X(⌊mM⌋)) tᵐ` of a `ℚ`-divisor, as a subring of
`𝒦_X(V)[t]`. -/
private def floorSubring (M : QDivisor X) (V : X.Opens) :
    Subring (Polynomial ((rationalFunctionsPresheaf X).obj (op V))) where
  carrier := {p | ∀ m : ℕ, p.coeff m ∈
    (DivisorWithCoeffs.roundDown ((m : ℚ) • M)).divisorialSubmodule V}
  zero_mem' := fun m => by rw [Polynomial.coeff_zero]; exact Submodule.zero_mem _
  add_mem' := fun hp hq m => by
    rw [Polynomial.coeff_add]; exact Submodule.add_mem _ (hp m) (hq m)
  neg_mem' := fun hp m => by rw [Polynomial.coeff_neg]; exact Submodule.neg_mem _ (hp m)
  one_mem' := fun m => by
    rw [Polynomial.coeff_one]
    split_ifs with h
    · subst h
      exact Divisor.divisorialSubmodule_mono (zero_le_roundDown_natCast_zero M) V
        (Divisor.IsDivisorialSection.one le_rfl V)
    · exact Submodule.zero_mem _
  mul_mem' := fun {p q} hp hq m => by
    rw [Polynomial.coeff_mul]
    refine Submodule.sum_mem _ fun x hx => ?_
    have hx : x.1 + x.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    subst hx
    exact Divisor.divisorialSubmodule_mono (roundDown_add_le_roundDown M x.1 x.2) V
      (Divisor.divisorialMul V ⟨_, hp x.1⟩ ⟨_, hq x.2⟩).2

private theorem mem_floorSubring {M : QDivisor X} {V : X.Opens}
    {p : Polynomial ((rationalFunctionsPresheaf X).obj (op V))} :
    p ∈ floorSubring M V ↔ ∀ m : ℕ, p.coeff m ∈
      (DivisorWithCoeffs.roundDown ((m : ℚ) • M)).divisorialSubmodule V :=
  Iff.rfl

/-- The constants `Γ(X, V) ⊆ 𝒦_X(V)` lie in the floor-section algebra. -/
private theorem C_mem_floorSubring (M : QDivisor X) (V : X.Opens) (s : Γ(X, V)) :
    Polynomial.C ((toRationalFunctionsPresheaf X).app (op V) s) ∈ floorSubring M V := fun m => by
  rw [Polynomial.coeff_C]
  split_ifs with h
  · subst h
    exact Divisor.divisorialSubmodule_mono (zero_le_roundDown_natCast_zero M) V
      (Divisor.isDivisorialSection_algebraMap le_rfl s)
  · exact Submodule.zero_mem _

end Floor

/-- Over an open with no point the rational functions form the zero ring. -/
private theorem subsingleton_rationalFunctionsPresheaf {X : Scheme.{0}} (V : X.Opens)
    (hV : ¬ (V : Set X).Nonempty) :
    Subsingleton (ToType ((rationalFunctionsPresheaf X).obj (op V))) :=
  ⟨fun _ _ => funext fun C => absurd ⟨_, C.2⟩ hV⟩

/-- **Finite generation along an isomorphism of coefficient rings.** Let `Θ : K₁ ≃ K₂` be a ring
isomorphism carrying the graded pieces `M₁ m` onto `M₂ m`, and the constants `C₁` onto `C₂`. If
the polynomials with coefficients in the `M₁ m` are generated by `C₁` and a finite set, and those
with coefficients in the `M₂ m` form a subring containing `C₂`, then the latter are generated by
`C₂` and a finite set. -/
private theorem exists_finset_eq_closure_of_ringEquiv {K₁ K₂ : Type*} [CommRing K₁]
    [CommRing K₂] (Θ : K₁ ≃+* K₂) (M₁ : ℕ → Set K₁) (M₂ : ℕ → Set K₂)
    (hM : ∀ m c, c ∈ M₁ m ↔ Θ c ∈ M₂ m) (R₂ : Subring (Polynomial K₂))
    (hR₂ : ∀ p, p ∈ R₂ ↔ ∀ m, p.coeff m ∈ M₂ m) (C₁ : Set (Polynomial K₁))
    (C₂ : Set (Polynomial K₂)) (hC : Polynomial.mapEquiv Θ '' C₁ = C₂) (hC₂ : C₂ ⊆ R₂)
    (G₁ : Finset (Polynomial K₁)) (hG₁ : ∀ p ∈ G₁, ∀ m, p.coeff m ∈ M₁ m)
    (hgen : ∀ p : Polynomial K₁, (∀ m, p.coeff m ∈ M₁ m) → p ∈ Subring.closure (C₁ ∪ ↑G₁)) :
    ∃ G₂ : Finset (Polynomial K₂),
      {p : Polynomial K₂ | ∀ m, p.coeff m ∈ M₂ m} = Subring.closure (C₂ ∪ ↑G₂) := by
  classical
  let Φ : Polynomial K₁ ≃+* Polynomial K₂ := Polynomial.mapEquiv Θ
  have hcoeff : ∀ (p : Polynomial K₁) m, (Φ p).coeff m = Θ (p.coeff m) := fun p m =>
    Polynomial.coeff_map _ _
  refine ⟨G₁.image Φ, Set.Subset.antisymm (fun p hp => ?_) (fun p hp => ?_)⟩
  · have hp₁ : ∀ m, (Φ.symm p).coeff m ∈ M₁ m := fun m => by
      rw [hM, ← hcoeff, Φ.apply_symm_apply]
      exact hp m
    have h2 : Φ (Φ.symm p) ∈
        (Subring.closure (C₁ ∪ ↑G₁)).map (Φ : Polynomial K₁ →+* Polynomial K₂) :=
      ⟨_, hgen _ hp₁, rfl⟩
    rw [RingHom.map_closure, Set.image_union, Φ.apply_symm_apply] at h2
    have hC' : (⇑(Φ : Polynomial K₁ →+* Polynomial K₂)) '' C₁ = C₂ := hC
    have hG' : (⇑(Φ : Polynomial K₁ →+* Polynomial K₂)) '' ↑G₁ = ↑(G₁.image Φ) := by simp
    rwa [hC', hG'] at h2
  · have hle : Subring.closure (C₂ ∪ ↑(G₁.image Φ)) ≤ R₂ := by
      refine Subring.closure_le.mpr (Set.union_subset hC₂ fun x hx => ?_)
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
      exact (hR₂ _).mpr fun m => by rw [hcoeff, ← hM]; exact hG₁ y hy m
    exact (hR₂ p).mp (hle hp)

/-! ### Rational functions over a nonempty open -/

section RationalFunctions

variable {X : Scheme.{0}} [IsIntegral X]

private theorem componentGenericPoint_mem_of_nonempty {V : X.Opens} (hV : (V : Set X).Nonempty)
    (Z : irreducibleComponents X) : componentGenericPoint X Z ∈ V := by
  obtain ⟨v, hv⟩ := hV
  exact (genericPoint_mem_iff Z V).mpr ⟨v, hv, MMP.Fourfold.mem_irreducibleComponent_of_irreducibleSpace Z v⟩

private theorem restrict_bijective (V : X.Opens) (hV : (V : Set X).Nonempty) :
    Function.Bijective ((rationalFunctionsPresheaf X).map (homOfLE le_top : V ⟶ ⊤).op).hom :=
  ⟨fun _ _ hab => funext fun Z =>
      congrFun hab ⟨Z.1, componentGenericPoint_mem_of_nonempty hV Z.1⟩,
    fun s => ⟨fun Z => s ⟨Z.1, componentGenericPoint_mem_of_nonempty hV Z.1⟩, rfl⟩⟩

/-- The function field of an integral scheme as its rational functions over a nonempty open. -/
private noncomputable def functionFieldEquiv (V : X.Opens) (hV : (V : Set X).Nonempty) :
    X.functionField ≃+* (rationalFunctionsPresheaf X).obj (op V) :=
  (rationalFunctionsEquivFunctionField X).symm.trans
    ((rationalFunctionsPresheafTopEquiv X).symm.trans
      (RingEquiv.ofBijective _ (restrict_bijective V hV)))

/-- The components of the rational function of the germ of a section at the generic point are its
germs at the generic points of the components. -/
private theorem rationalFunctionsEquivFunctionField_symm_germ (U : X.Opens) (s : Γ(X, U))
    (h : genericPoint X ∈ U) (Z : irreducibleComponents X) (hZ : componentGenericPoint X Z ∈ U) :
    (rationalFunctionsEquivFunctionField X).symm (X.presheaf.germ U (genericPoint X) h s) Z =
      X.presheaf.germ U (componentGenericPoint X Z) hZ s := by
  have : Finite (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  have hd : Dense (U : Set X) := U.isOpen.dense ⟨_, h⟩
  let D : Stacks.Chow.DenseOpen X := ⟨U, hd⟩
  have key : (rationalFunctionsEquivFunctionField X).symm (X.presheaf.germ U (genericPoint X) h s)
      = (Stacks.Chow.rationalFunctionsEquivStalks X).1 (Stacks.Chow.ofSection X D s) := by
    rw [RingEquiv.symm_apply_eq, ← (Stacks.Chow.rationalFunctionsEquivFunctionField X).2 D s h]
    change _ = (Stacks.Chow.rationalFunctionsEquivFunctionField X).1
      ((Stacks.Chow.rationalFunctionsEquivStalks X).1.symm _)
    rw [RingEquiv.symm_apply_apply]
  rw [key]
  exact (Stacks.Chow.rationalFunctionsEquivStalks X).2 D s Z hZ

private theorem functionFieldEquiv_germ (V : X.Opens) (hV : (V : Set X).Nonempty)
    [Nonempty V] (s : Γ(X, V)) :
    functionFieldEquiv V hV (X.germToFunctionField V s) =
      (toRationalFunctionsPresheaf X).app (op V) s := by
  funext Z
  exact rationalFunctionsEquivFunctionField_symm_germ V s _ Z.1 Z.2

end RationalFunctions

/-! ### The common resolution of the model -/

section Resolution

/-- The two composites `W ⟶ S` of a common resolution of a map over `S` agree. -/
private theorem comp_eq_comp_of_isInverse {X Y W S : Scheme.{0}} [IsReduced W] [IsReduced X]
    [IsSeparated (X ↘ ⊤_ Scheme)] [IsSeparated (S ↘ ⊤_ Scheme)] {g : X ⟶ S} {πY : Y ⟶ S}
    {φ : X.RationalMap Y} (hover : MMP.Flips.RationalMap.IsOver g πY φ) {p : W ⟶ X} {q : W ⟶ Y}
    {h : X.RationalMap W} (hinv : MMP.Mori.RationalMap.IsInverse p.toRationalMap h)
    (hhq : h.compHom q = φ) : p ≫ g = q ≫ πY := by
  obtain ⟨e, he1, he2⟩ := id hinv
  have hs : e.source.ι ≫ p = e.iso.hom ≫ e.target.ι :=
    ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
      (Scheme.PartialMap.toRationalMap_eq_iff.mp he1)).symm
  have h1 : ((e.symm.toPartialMap.compHom q).compHom πY).toRationalMap = g.toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap, Scheme.RationalMap.compHom_toRationalMap]
    change (e.symm.toRationalMap.compHom q).compHom πY = _
    rwa [he2, hhq]
  have h2 := (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp h1)
  change (e.iso.inv ≫ e.source.ι) ≫ q ≫ πY = e.target.ι ≫ g at h2
  have : IsDominant e.source.ι := Opens.isDominant_ι e.dense_source
  refine ext_of_isDominant_of_isSeparated (S ↘ ⊤_ Scheme) (Limits.terminal.hom_ext _ _)
    e.source.ι ?_
  rw [← Category.assoc, hs, Category.assoc, ← h2]
  simp

variable {X W : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X] [IsIntegral W]

/-- The generic point of `W` maps outside the support of a `ℚ`-Cartier `ℚ`-divisor on `X`. -/
private theorem map_componentGenericPoint_notMem_supp_of_isQCartier (f : W ⟶ X) [IsDominant f]
    {B : QDivisor X} (hB : B.IsQCartier) (Z : irreducibleComponents W) :
    f (componentGenericPoint W Z) ∉ B.supp := by
  obtain ⟨m, hm, L, hL, -⟩ := hB.exists_pos
  rw [← QDivisor.supp_eq_of_toQDivisor_eq (by exact_mod_cast hm.ne') hL]
  exact MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant f L Z

/-- The pull-back of a `ℚ`-Cartier `ℚ`-divisor is `ℚ`-Cartier. -/
private theorem isQCartier_pullback [CompactSpace X] [IsLocallyNoetherian W] [IsNormal W]
    [CompactSpace W] (f : W ⟶ X) [IsDominant f] {B : QDivisor X}
    (hB : B.IsQCartier)
    (hB' : ∀ Z : irreducibleComponents W, f (componentGenericPoint W Z) ∉ B.supp) :
    (B.pullback hB hB').IsQCartier := by
  obtain ⟨m, hm, L, hL, hLc⟩ := hB.exists_pos
  obtain ⟨L', hL', hp⟩ := QDivisor.isPullback_pullback hB hB' m hm L hL hLc
  refine ⟨m, by exact_mod_cast hm.ne', L', hL', ?_⟩
  rw [← hp.pullback_eq hLc]
  exact Divisor.IsCartier.isCartier_pullback hLc f _

/-- The real divisor of the pull-back of a `ℚ`-Cartier `ℚ`-divisor is its `ℝ`-Cartier pull-back. -/
private theorem qToRDivisor_pullback_eq [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    (f : W ⟶ X) [IsDominant f] {B : QDivisor X}
    (hB : B.IsQCartier)
    (hB' : ∀ Z : irreducibleComponents W, f (componentGenericPoint W Z) ∉ B.supp)
    {G : RDivisor W} (hG : MMP.Flips.IsRCartierPullback f (QDivisor.toRDivisor B) G) :
    QDivisor.toRDivisor (B.pullback hB hB') = G := by
  obtain ⟨m, hm, L, hL, hLc⟩ := hB.exists_pos
  obtain ⟨L', hL', hp⟩ := QDivisor.isPullback_pullback hB hB' m hm L hL hLc
  have h1 := MMP.Flips.isRCartierPullback_of_zsmul_eq f hm hLc hL.symm ⟨_, hp⟩
  refine Eq.trans ?_ (MMP.Flips.IsRCartierPullback.eq f h1 hG)
  ext E
  have h2 := congrArg (fun D : QDivisor W => D.coeff E) hL'
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul,
    Int.cast_natCast] at h2
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  change (((B.pullback hB hB') E : ℚ) : ℝ) = (1 / (m : ℝ)) * ((L' E : ℤ) : ℝ)
  rw [← DivisorWithCoeffs.coeff_apply, ← DivisorWithCoeffs.coeff_apply]
  have h3 : ((L'.coeff E : ℤ) : ℝ) = (m : ℝ) * ((B.pullback hB hB').coeff E : ℝ) := by
    exact_mod_cast congrArg (fun x : ℚ => (x : ℝ)) h2
  rw [h3]
  field_simp

end Resolution

/-- A `q`-exceptional divisor in the sense of `MMP.Flips.IsExceptionalPrimeDivisor` (centre of
codimension at least two) is exceptional in the sense of `MMP.Resolution.IsExceptionalDivisorFor`
(the image of each component has smaller dimension), for `q` birational between varieties of
dimension `n`. -/
private theorem isExceptionalDivisorFor_of_isExceptionalPrimeDivisor {W Y : Scheme.{0}}
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] {sY : Y ⟶ Spec (.of ℂ)}
    {sW : W ⟶ Spec (.of ℂ)} [MMP.Mori.IsVariety ℂ sY] [MMP.Mori.IsVariety ℂ sW] {q : W ⟶ Y}
    (hqb : IsBirationalMorphism q) {n : ℕ} (hn : topologicalKrullDim Y = n) {E : QDivisor W}
    (hE : ∀ P, E P ≠ 0 → MMP.Flips.IsExceptionalPrimeDivisor sY q P) :
    MMP.Resolution.IsExceptionalDivisorFor q E := by
  intro P hP
  obtain ⟨hYn, hf, hp, hex⟩ := hE P (Finsupp.mem_support_iff.mp hP)
  change topologicalKrullDim
    ((MMP.Flips.ProperDivisorOver.mk ⟨W, q, hYn, hf, P⟩ hp).center : Set Y) + 2 ≤
      topologicalKrullDim Y at hex
  rw [MMP.Flips.ProperDivisorOver.center_eq_toDivisorOver_center,
    MMP.Mori.DivisorOver.center_eq_closure_genericPoint] at hex
  have himg : closure (q.base '' P.support) = closure {q P.genericPoint} := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    apply le_antisymm
    · refine closure_minimal
        ((image_closure_subset_closure_image q.base.hom.continuous).trans ?_) isClosed_closure
      rw [Set.image_singleton]
    · exact closure_mono (by rw [← Set.image_singleton]; exact Set.image_mono subset_closure)
  rw [himg, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  have : LocallyOfFiniteType sW := inferInstance
  have h1 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sW P.genericPoint
  rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint,
    ← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY sW hqb, hn] at h1
  change topologicalKrullDim (closure {q P.genericPoint} : Set Y) + 2 ≤ topologicalKrullDim Y
    at hex
  rw [hn] at hex
  generalize topologicalKrullDim (closure {q P.genericPoint} : Set Y) = a at hex ⊢
  generalize topologicalKrullDim (closure {P.genericPoint} : Set W) = b at h1 ⊢
  induction b using WithBot.recBotCoe with
  | bot => exact absurd h1 (by simp)
  | coe b =>
    induction a using WithBot.recBotCoe with
    | bot => exact WithBot.bot_lt_coe b
    | coe a =>
      have h1' : b + 1 = (n : ℕ∞) := by exact_mod_cast h1
      rw [show (2 : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) from rfl] at hex
      have hex' : a + 2 ≤ (n : ℕ∞) := by exact_mod_cast hex
      have hb : b ≠ ⊤ := fun hb => by simp [hb] at h1'
      lift b to ℕ using hb
      have ha : a ≠ ⊤ := fun ha => by simp [ha] at hex'
      lift a to ℕ using ha
      have h1'' : b + 1 = n := by exact_mod_cast h1'
      have hex'' : a + 2 ≤ n := by exact_mod_cast hex'
      exact_mod_cast (show a < b by omega)

/-! ### Floor sections on the source and on the model -/

section Transport

variable {X Y W S : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
  [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral W]
  [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W]

omit [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W] in
/-- Germs of sections pulled back along equal morphisms agree. -/
private theorem germToFunctionField_app_congr {f f' : W ⟶ S} (h : f = f') (U : S.Opens)
    (s : Γ(S, U)) [Nonempty (f ⁻¹ᵁ U)] [Nonempty (f' ⁻¹ᵁ U)] :
    W.germToFunctionField (f ⁻¹ᵁ U) (f.app U s) =
      W.germToFunctionField (f' ⁻¹ᵁ U) (f'.app U s) := by
  subst h
  rfl

omit [CompactSpace X] in
/-- **Floor sections of a model through a common resolution.** Let `p : W ⟶ X`, `q : W ⟶ Y` be
proper birational morphisms of normal varieties with `p ≫ g = q ≫ πY` over `S`, and `D_X`, `D_Y`
`ℚ`-Cartier `ℚ`-divisors with `p^*D_X = q^*D_Y + E`, `E ≥ 0` `q`-exceptional. Over an open
`U ⊆ S` with `g⁻¹U` nonempty, the identification `k(Y) ≅ k(W) ≅ k(X)` of function fields gives a
ring isomorphism `𝒦_Y(πY⁻¹U) ≅ 𝒦_X(g⁻¹U)` which carries the sections of `⌊mD_Y⌋` onto those of
`⌊mD_X⌋` for every `m` and the constants of `Γ(S, U)` to the constants. -/
private theorem exists_ringEquiv_floorSections {sX : X ⟶ Spec (.of ℂ)}
    {sY : Y ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX)
    (hY : IsNormalVariety ℂ sY) (hW : IsNormalVariety ℂ sW) {p : W ⟶ X} {q : W ⟶ Y}
    [IsProper p] [IsProper q] [IsDominant p] [IsDominant q] (hpb : IsBirationalMorphism p)
    (hqb : IsBirationalMorphism q) (hpX : p ≫ sX = sW) (hqY : q ≫ sY = sW) {g : X ⟶ S}
    {πY : Y ⟶ S} (hpq : p ≫ g = q ≫ πY) (DX : QDivisor X) (DY : QDivisor Y)
    (hDX : DX.IsQCartier) (hDY : DY.IsQCartier)
    (hBp : ∀ Z : irreducibleComponents W, p (componentGenericPoint W Z) ∉ DX.supp)
    (hBq : ∀ Z : irreducibleComponents W, q (componentGenericPoint W Z) ∉ DY.supp)
    (hDWq : (DX.pullback hDX hBp).IsQCartier)
    (hE : 0 ≤ DX.pullback hDX hBp - DY.pullback hDY hBq)
    (hEx : MMP.Resolution.IsExceptionalDivisorFor q (DX.pullback hDX hBp - DY.pullback hDY hBq))
    (U : S.Opens) (hU : ((g ⁻¹ᵁ U : X.Opens) : Set X).Nonempty) :
    ∃ Θ : (rationalFunctionsPresheaf Y).obj (op (πY ⁻¹ᵁ U)) ≃+*
        (rationalFunctionsPresheaf X).obj (op (g ⁻¹ᵁ U)),
      (∀ (m : ℕ) c, c ∈ (DivisorWithCoeffs.roundDown ((m : ℚ) • DY)).divisorialSubmodule
          (πY ⁻¹ᵁ U) ↔
        Θ c ∈ (DivisorWithCoeffs.roundDown ((m : ℚ) • DX)).divisorialSubmodule (g ⁻¹ᵁ U)) ∧
      ∀ a : Γ(S, U), Θ ((toRationalFunctionsPresheaf Y).app (op (πY ⁻¹ᵁ U)) (πY.app U a)) =
        (toRationalFunctionsPresheaf X).app (op (g ⁻¹ᵁ U)) (g.app U a) := by
  -- the opens are nonempty
  obtain ⟨w, hw⟩ : ∃ w : W, p w ∈ g ⁻¹ᵁ U := p.denseRange.exists_mem_open (g ⁻¹ᵁ U).isOpen hU
  have hwW : w ∈ (p ≫ g) ⁻¹ᵁ U := hw
  have hUY : ((πY ⁻¹ᵁ U : Y.Opens) : Set Y).Nonempty := by
    refine ⟨q w, ?_⟩
    change (q ≫ πY) w ∈ U
    rwa [← hpq]
  have : Nonempty (g ⁻¹ᵁ U) := hU.to_subtype
  have : Nonempty (πY ⁻¹ᵁ U) := hUY.to_subtype
  have : Nonempty (p ⁻¹ᵁ (g ⁻¹ᵁ U)) := ⟨⟨w, hw⟩⟩
  have : Nonempty (q ⁻¹ᵁ (πY ⁻¹ᵁ U)) := ⟨⟨w, show (q ≫ πY) w ∈ U by rwa [← hpq]⟩⟩
  -- the identification of function fields
  let ιX := functionFieldEquiv (g ⁻¹ᵁ U) hU
  let ιY := functionFieldEquiv (πY ⁻¹ᵁ U) hUY
  let eq := RingEquiv.ofBijective (functionFieldMap q) hqb.functionFieldMap_bijective
  let ep := RingEquiv.ofBijective (functionFieldMap p) hpb.functionFieldMap_bijective
  let σ : Y.functionField ≃+* X.functionField := eq.trans ep.symm
  have hσ : ∀ y, functionFieldMap p (σ y) = functionFieldMap q y := fun y =>
    ep.apply_symm_apply (eq y)
  refine ⟨ιY.symm.trans (σ.trans ιX), fun m c => ?_, fun a => ?_⟩
  · obtain ⟨y, rfl⟩ := ιY.surjective c
    have hΘ : (ιY.symm.trans (σ.trans ιX)) (ιY y) = ιX (σ y) := by simp
    rw [hΘ]
    have Lq := MMP.Mori.mem_divisorialSubmodule_roundDown_iff_of_eq_pullback_add sW sY hW hY q
      hqb hqY (p ≫ g) πY hpq.symm (DX.pullback hDX hBp) DY hDWq hDY hBq _ hE hEx
      (by abel) U m y
    have Lp := MMP.Mori.mem_divisorialSubmodule_roundDown_iff_of_eq_pullback_add sW sX hW hX p
      hpb hpX (p ≫ g) g rfl (DX.pullback hDX hBp) DX hDWq hDX hBp 0 le_rfl
      (fun P hP => absurd hP (by simp)) (by rw [add_zero]) U m (σ y)
    rw [hσ] at Lp
    exact Lq.trans Lp.symm
  · -- the constants
    have h1 : (toRationalFunctionsPresheaf Y).app (op (πY ⁻¹ᵁ U)) (πY.app U a) =
        ιY (Y.germToFunctionField (πY ⁻¹ᵁ U) (πY.app U a)) :=
      (functionFieldEquiv_germ (πY ⁻¹ᵁ U) hUY _).symm
    have h2 : σ (Y.germToFunctionField (πY ⁻¹ᵁ U) (πY.app U a)) =
        X.germToFunctionField (g ⁻¹ᵁ U) (g.app U a) := by
      apply hpb.functionFieldMap_bijective.1
      rw [hσ, MMP.Spreading.functionFieldMap_germToFunctionField q (πY ⁻¹ᵁ U)
          (q ⁻¹ᵁ (πY ⁻¹ᵁ U)) le_rfl,
        MMP.Spreading.functionFieldMap_germToFunctionField p (g ⁻¹ᵁ U) (p ⁻¹ᵁ (g ⁻¹ᵁ U)) le_rfl,
        ← Scheme.Hom.app_eq_appLE, ← Scheme.Hom.app_eq_appLE]
      have : Nonempty ((q ≫ πY) ⁻¹ᵁ U) := ⟨⟨w, show (q ≫ πY) w ∈ U by rwa [← hpq]⟩⟩
      have : Nonempty ((p ≫ g) ⁻¹ᵁ U) := ⟨⟨w, hw⟩⟩
      have e1 : q.app (πY ⁻¹ᵁ U) (πY.app U a) = (q ≫ πY).app U a := by
        rw [Scheme.Hom.comp_app]; rfl
      have e2 : p.app (g ⁻¹ᵁ U) (g.app U a) = (p ≫ g).app U a := by
        rw [Scheme.Hom.comp_app]; rfl
      rw [e1, e2]
      exact germToFunctionField_app_congr hpq.symm U a
    rw [h1]
    simp only [RingEquiv.trans_apply, RingEquiv.symm_apply_apply]
    rw [h2]
    exact functionFieldEquiv_germ (g ⁻¹ᵁ U) hU _

end Transport

/-! ### Finite generation on the model -/

section Model

/-- **Finite generation of the floor-section algebra over a variety.** Let `f : Y ⟶ Z` be a
projective morphism from a normal variety to a variety over `ℂ`, and `D` a `ℚ`-divisor on `Y`
with `qD = B` for a relatively free Cartier divisor `B`. Over every affine open `V ⊆ Z` the
floor-section algebra `⨁_{m ≥ 0} H⁰(f⁻¹V, 𝒪_Y(⌊mD⌋)) tᵐ` is generated by `Γ(Z, V)` and finitely
many elements.

Through the Stein factorization `Y ⟶ W ⟶ Z`, with `W` normal and `κ : W ⟶ Z` finite, `B` is free
over `W`, so the algebra is of finite type over `Γ(W, κ⁻¹V)`
(`MMP.Fourfold.fg_roundDownSections_of_isRelativelyFreeDivisor`), and `Γ(W, κ⁻¹V)` is a finite
`Γ(Z, V)`-module: its finitely many module generators, as constants, are added to the generators.
-/
private theorem fg_roundDownSections_of_isRelativelyFreeDivisor_of_isVariety
    {Y Z : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ))
    (hZ : MMP.Mori.IsVariety ℂ sZ) [IsLocallyNoetherian Y] [IsNormal Y] (hY : IsNormalVariety ℂ sY)
    (f : Y ⟶ Z) (hf : IsProjective f) (hfk : f ≫ sZ = sY) {D : QDivisor Y} {q : ℕ} (hq : 0 < q)
    (B : Divisor Y) (hB : ∀ P, (B.coeff P : ℚ) = q * D.coeff P) (hBc : B.IsCartier)
    (hfree : IsRelativelyFreeDivisor f B) (V : Z.Opens) (hV : IsAffineOpen V) :
    ∃ G : Finset (Polynomial ((rationalFunctionsPresheaf Y).obj (op (f ⁻¹ᵁ V)))),
      (∀ p ∈ G, ∀ m : ℕ,
        p.coeff m ∈ (DivisorWithCoeffs.roundDown ((m : ℚ) • D)).divisorialSubmodule (f ⁻¹ᵁ V)) ∧
      ∀ p : Polynomial ((rationalFunctionsPresheaf Y).obj (op (f ⁻¹ᵁ V))),
        (∀ m : ℕ,
          p.coeff m ∈ (DivisorWithCoeffs.roundDown ((m : ℚ) • D)).divisorialSubmodule (f ⁻¹ᵁ V)) →
        p ∈ Subring.closure (Set.range (fun a : Γ(Z, V) =>
          Polynomial.C (algebraMap Γ(Y, f ⁻¹ᵁ V) _ (f.app V a))) ∪ ↑G) := by
  classical
  have : IsIntegral Y := hY.1.toIsIntegral
  have : QuasiCompact sY := hY.1.toQuasiCompact
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : IsProper f := hf.isProper
  obtain ⟨W, h, κ, ⟨hS⟩, -, -, -, -, hfin, hWv⟩ :=
    MMP.Resolution.Bridges.exists_steinFactorization_of_isNormalVariety sY sZ hY hZ f hfk
  have hcomp := hS.comp
  subst hcomp
  have := hWv.2
  have : LocallyOfFiniteType (κ ≫ sZ) := hWv.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (κ ≫ sZ)
  have hh : IsProjective h := IsProjective.of_comp h κ hf
  have hfree' : IsRelativelyFreeDivisor h B := isRelativelyFreeDivisor_of_forall_exists h fun x => by
    obtain ⟨U, hU, ψ, h1, h2⟩ := exists_coeff_add_ord_eq_zero_of_isRelativelyFree _ hBc hfree x
    exact ⟨κ ⁻¹ᵁ U, hU, ψ, h1, h2⟩
  obtain ⟨G, hG1, hG2⟩ := fg_roundDownSections_of_isRelativelyFreeDivisor sY (κ ≫ sZ) hY hWv h hh
    (by rw [← Category.assoc]; exact hfk) hq B hB hBc hfree' (κ ⁻¹ᵁ V) (hV.preimage κ)
  -- the module generators of `Γ(W, κ⁻¹V)` over `Γ(Z, V)`
  letI : Algebra Γ(Z, V) Γ(W, κ ⁻¹ᵁ V) := (κ.app V).hom.toAlgebra
  have hfinite : Module.Finite Γ(Z, V) Γ(W, κ ⁻¹ᵁ V) := κ.finite_app V hV
  obtain ⟨T, hT⟩ := hfinite.fg_top
  let c : Γ(W, κ ⁻¹ᵁ V) →+* Polynomial ((rationalFunctionsPresheaf Y).obj (op ((h ≫ κ) ⁻¹ᵁ V))) :=
    Polynomial.C.comp ((algebraMap Γ(Y, (h ≫ κ) ⁻¹ᵁ V)
      ((rationalFunctionsPresheaf Y).obj (op ((h ≫ κ) ⁻¹ᵁ V)))).comp (h.app (κ ⁻¹ᵁ V)).hom)
  have hcκ : ∀ a : Γ(Z, V), c (κ.app V a) =
      Polynomial.C (algebraMap Γ(Y, (h ≫ κ) ⁻¹ᵁ V)
      ((rationalFunctionsPresheaf Y).obj (op ((h ≫ κ) ⁻¹ᵁ V))) ((h ≫ κ).app V a)) := fun a => by
    have e : (h ≫ κ).app V a = h.app (κ ⁻¹ᵁ V) (κ.app V a) := by
      rw [Scheme.Hom.comp_app]; rfl
    rw [e]
    rfl
  let consts := Set.range (fun a : Γ(Z, V) =>
    Polynomial.C (algebraMap Γ(Y, (h ≫ κ) ⁻¹ᵁ V)
      ((rationalFunctionsPresheaf Y).obj (op ((h ≫ κ) ⁻¹ᵁ V))) ((h ≫ κ).app V a)))
  let G' : Finset (Polynomial ((rationalFunctionsPresheaf Y).obj (op ((h ≫ κ) ⁻¹ᵁ V)))) :=
    G ∪ T.image c
  have hc : ∀ b, c b ∈ Subring.closure (consts ∪ ↑G') := by
    intro b
    have hb : b ∈ Submodule.span Γ(Z, V) (T : Set Γ(W, κ ⁻¹ᵁ V)) := hT ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem x hx =>
      exact Subring.subset_closure (Or.inr (Finset.mem_coe.mpr
        (Finset.mem_union_right _ (Finset.mem_image_of_mem c hx))))
    | zero => rw [map_zero]; exact Subring.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Subring.add_mem _ hx hy
    | smul a x _ hx =>
      rw [Algebra.smul_def, map_mul]
      exact Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨a, (hcκ a).symm⟩)) hx
  refine ⟨G', fun p hp m => ?_, fun p hp => ?_⟩
  · rcases Finset.mem_union.mp hp with hp | hp
    · exact hG1 p hp m
    · obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hp
      exact C_mem_floorSubring D ((h ≫ κ) ⁻¹ᵁ V) (h.app (κ ⁻¹ᵁ V) t) m
  · refine (Subring.closure_le.mpr (Set.union_subset ?_ ?_)) (hG2 p hp)
    · rintro _ ⟨b, rfl⟩
      exact hc b
    · intro x hx
      exact Subring.subset_closure (Or.inr (Finset.mem_coe.mpr (Finset.mem_union_left _ hx)))

/-- **Finite generation on the model.** On the log terminal model `πY : Y ⟶ S`, with `K_Y + Γ`
nef over `S` and `Γ ≥ G` for a relatively big `G`, some multiple of `K_Y + Γ` is a relatively free
Cartier divisor (uniform freeness on the singleton polytope `{Γ}`), so its floor-section algebra is
of finite type over every affine open of `S`. -/
private theorem exists_finset_floor_model {Y S : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} [QuasiCompact sY]
    {sS : S ⟶ Spec (.of ℂ)} {πY : Y ⟶ S} (hY : IsNormalVariety ℂ sY)
    (hYp : MMP.Mori.IsProjectiveVariety ℂ sY) (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    (hπY : πY ≫ sS = sY) (hYQ : IsQFactorial sY) {KY : Divisor Y}
    (hKY : ∃ m : ℕ, MMP.Mori.Divisor.IsCanonicalDivisor sY m KY) {G Γq : QDivisor Y}
    (hG0 : 0 ≤ G) (hGbig : G.IsRelativelyBig πY) (hGΓ : G ≤ Γq) (hΓ0 : 0 ≤ Γq)
    (hΓklt : IsRealKltPair sY (QDivisor.toRDivisor Γq))
    (hnef : MMP.Flips.IsRelativelyNef ℂ sY πY
      (Divisor.toRDivisor KY + QDivisor.toRDivisor Γq))
    (U : S.Opens) (hU : IsAffineOpen U) :
    ∃ G : Finset (Polynomial ((rationalFunctionsPresheaf Y).obj (op (πY ⁻¹ᵁ U)))),
      (∀ p ∈ G, ∀ m : ℕ, p.coeff m ∈ (DivisorWithCoeffs.roundDown
        ((m : ℚ) • (Divisor.toQDivisor KY + Γq))).divisorialSubmodule (πY ⁻¹ᵁ U)) ∧
      ∀ p : Polynomial ((rationalFunctionsPresheaf Y).obj (op (πY ⁻¹ᵁ U))),
        (∀ m : ℕ, p.coeff m ∈ (DivisorWithCoeffs.roundDown
          ((m : ℚ) • (Divisor.toQDivisor KY + Γq))).divisorialSubmodule (πY ⁻¹ᵁ U)) →
        p ∈ Subring.closure (Set.range (fun a : Γ(S, U) =>
          Polynomial.C (algebraMap Γ(Y, πY ⁻¹ᵁ U) _ (πY.app U a))) ∪ ↑G) := by
  classical
  have : AlgebraicGeometry.IsProjectiveVariety ℂ sY := hYp
  have : AlgebraicGeometry.IsProjectiveVariety ℂ sS := hS
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have hDYq := isQCartier_of_isQFactorial sY hYQ (Divisor.toQDivisor KY + Γq)
  obtain ⟨N, hN, L, hL, hLc⟩ := hDYq.exists_pos
  have hVklt : IsKltPair sY Γq := by
    obtain ⟨n, hn⟩ := hKY
    exact ⟨⟨inferInstance, inferInstance, ⟨hY, n, KY, hn, hDYq⟩, hΓ0⟩,
      fun n D a h => hΓklt.2.2.2 n D a h⟩
  obtain ⟨VQ, -, -, hΓVQ, -, ⟨b, hb, hfree⟩, -⟩ :=
    QDivisor.IsRelativelyBig.exists_isRelativelyFreeDivisor_nsmul_of_isRelativelyNef sY sS hYQ
      πY hπY hKY hGbig hG0 {Γq}
      (fun Γ hΓ => by rw [Finset.mem_singleton.mp hΓ]; exact hΓ0)
      (fun Γ hΓ E => by
        rw [Finset.mem_singleton.mp hΓ]
        have := hΓklt.2.1 E
        rw [QDivisor.coeff_toRDivisor] at this
        exact_mod_cast this.le)
      (fun Γ hΓ => by rwa [Finset.mem_singleton.mp hΓ])
      (fun Γ hΓ => by rwa [Finset.mem_singleton.mp hΓ])
      (Δ := QDivisor.toRDivisor Γq) (subset_convexHull ℝ _ ⟨Γq, by simp, rfl⟩) hnef
  have hLR : (N : ℝ) • (Divisor.toRDivisor KY + QDivisor.toRDivisor Γq) = Divisor.toRDivisor L := by
    ext E
    have h1 := congrArg (fun D : QDivisor Y => D.coeff E) hL
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul,
      Int.cast_natCast, DivisorWithCoeffs.coeff_add] at h1
    change (N : ℝ) * ((KY E : ℤ) + ((Γq E : ℚ) : ℝ)) = ((L E : ℤ) : ℝ)
    rw [← DivisorWithCoeffs.coeff_apply, ← DivisorWithCoeffs.coeff_apply,
      ← DivisorWithCoeffs.coeff_apply]
    have h2 := congrArg (fun x : ℚ => (x : ℝ)) h1
    push_cast at h2
    linarith
  have hfree' := hfree _ hΓVQ (N : ℝ) (by exact_mod_cast hN) L hLc hLR
  have hπ : IsProjective πY := by
    have : IsSeparated sS := inferInstance
    refine IsProjective.of_comp πY sS ?_
    rw [hπY]
    exact ((AlgebraicGeometry.isProjectiveVariety_iff_isProjective' ℂ sY).mp hYp).2
  refine fg_roundDownSections_of_isRelativelyFreeDivisor_of_isVariety sY sS
    ((MMP.Mori.isProjectiveVariety_iff ℂ sS).mp hS).1 hY πY hπ hπY
    (q := b * N) (Nat.mul_pos hb hN) ((b : ℤ) • L) (fun P => ?_) (hLc.zsmul _) hfree' U hU
  have h1 := congrArg (fun D : QDivisor Y => D.coeff P) hL
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul,
    Int.cast_natCast] at h1
  rw [DivisorWithCoeffs.coeff_smul, smul_eq_mul, Int.cast_mul, h1]
  push_cast
  ring

end Model

/-! ### The canonical divisor of the model -/

section Canonical

/-- **The canonical divisor of a contraction.** For a birational contraction `φ = q ∘ p⁻¹` of
normal varieties with a common resolution `p : W ⟶ X`, `q : W ⟶ Y`, the push-forward `φ_* K` of a
canonical divisor of `X` is a canonical divisor of `Y`: with `K_W` a canonical divisor of `W`
with `p_* K_W = K`, both `φ_* K` and the canonical divisor `q_* K_W` have, at a prime `F` of `Y`,
the coefficient of `K_W` at the strict transform of `F`. -/
private theorem isCanonicalDivisor_transformDivisor_of_isInverse {X Y W : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y]
    [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral W] [CompactSpace W]
    [IsLocallyNoetherian W] [IsNormal W] {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)}
    {sW : W ⟶ Spec (.of ℂ)} (hXv : IsNormalVariety ℂ sX) (hYv : IsNormalVariety ℂ sY)
    (hWv : IsNormalVariety ℂ sW) {p : W ⟶ X} {q : W ⟶ Y} [IsProper p] [IsProper q]
    [IsDominant p] [IsDominant q] (hpb : IsBirationalMorphism p) (hqb : IsBirationalMorphism q)
    (hpX : p ≫ sX = sW) (hqY : q ≫ sY = sW) {h : X.RationalMap W} {φ : X.RationalMap Y}
    (hinv : MMP.Mori.RationalMap.IsInverse p.toRationalMap h) (hhq : h.compHom q = φ)
    (hcontr : ∀ F : MMP.Mori.PrimeDivisor Y, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F)
    {K : Divisor X} {n : ℕ} (hK : MMP.Mori.Divisor.IsCanonicalDivisor sX n K) {KY₀ : Divisor Y}
    (hKY₀ : MMP.Mori.Divisor.IsCanonicalDivisor sY n KY₀) :
    MMP.Mori.Divisor.IsCanonicalDivisor sY n (MMP.Mori.RationalMap.transformDivisor φ K) := by
  have := hXv.1
  have := hYv.1
  have := hWv.1
  have := isSeparated_toTerminal_of_isNormalVariety hXv
  have := isSeparated_toTerminal_of_isNormalVariety hYv
  have hdimW : topologicalKrullDim W = n := by
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX sW hpb]
    exact hK.topologicalKrullDim_eq
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor sW hWv hdimW
  have hWp : IsNormalVariety ℂ (p ≫ sX) := by rwa [hpX]
  have hWq : IsNormalVariety ℂ (q ≫ sY) := by rwa [hqY]
  have : LocallyOfFiniteType (p ≫ sX) := by rw [hpX]; infer_instance
  have : LocallyOfFiniteType (q ≫ sY) := by rw [hqY]; infer_instance
  obtain ⟨KW, hKW, hpKW⟩ := MMP.Fourfold.Oai4C1.Main.exists_isCanonicalDivisor_transformDivisor_eq
    hXv hWp hpb hK (by rwa [hpX])
  have hqKW := MMP.Fourfold.Oai4C1.Main.isCanonicalDivisor_transformDivisor hYv hWq hqb hKY₀
    (by rwa [hqY, ← hpX])
  have heq : MMP.Mori.RationalMap.transformDivisor φ K =
      MMP.Mori.RationalMap.transformDivisor (X := W) q.toRationalMap KW := by
    refine Finsupp.ext fun F => ?_
    obtain ⟨E, hE, -, htr⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hYv hWq hqb F
    rw [htr KW]
    obtain ⟨Q, hpE, hφ⟩ := exists_primeDivisor_of_apply_eq_genericPoint hqb hinv hhq hcontr hE
    rw [hφ K, ← hpKW]
    obtain ⟨E', hE', -, htr'⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hXv hWp hpb Q
    rw [htr' KW, AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (eq_of_apply_eq_genericPoint hpb hE' hpE)]
  rwa [heq]

end Canonical

/-! ### Finite generation of the floor-section algebra -/

section FiniteGeneration

/-- **Finite generation of the floor-section algebra.** -/
private theorem fg_floorSections_of_isNefWeakModel {X Y W S : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} [QuasiCompact sY] {sS : S ⟶ Spec (.of ℂ)}
    {sW : W ⟶ Spec (.of ℂ)} {g : X ⟶ S} {πY : Y ⟶ S}
    {K : Divisor X} {A : QDivisor X} {B : RDivisor X} {φ : X.RationalMap Y} {p : W ⟶ X}
    {q : W ⟶ Y} {h : X.RationalMap W} {GX GY : RDivisor W}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    (hg : g ≫ sS = sX) (hXQ : IsQFactorial sX) (hdim : topologicalKrullDim X = 3)
    (hA0 : 0 ≤ A) (hA : A.IsRelativelyBig g) (hB0 : 0 ≤ B)
    (hWM : IsNefWeakModel sX sY sS g πY K (QDivisor.toRDivisor A + B) φ)
    (hKY : ∃ m : ℕ,
      MMP.Mori.Divisor.IsCanonicalDivisor sY m (MMP.Mori.RationalMap.transformDivisor φ K))
    (hYQ : IsQFactorial sY)
    (hYklt : IsRealKltPair sY
      (MMP.Mori.RationalMap.transformDivisor φ (QDivisor.toRDivisor A + B)))
    (hWv : MMP.Mori.IsVariety ℂ sW) (hpX : p ≫ sX = sW) (hqY : q ≫ sY = sW)
    (hpproj : IsProjectiveMorphism p) (hqproj : IsProjectiveMorphism q)
    (hpb : IsBirationalMorphism p) (hqb : IsBirationalMorphism q)
    (hinv : MMP.Mori.RationalMap.IsInverse p.toRationalMap h) (hhq : h.compHom q = φ)
    (hGX : MMP.Flips.IsRCartierPullback p
      (MMP.Flips.logCanonicalDivisor K (QDivisor.toRDivisor A + B)) GX)
    (hGY : MMP.Flips.IsRCartierPullback q
      (MMP.Flips.logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ K)
        (MMP.Mori.RationalMap.transformDivisor φ (QDivisor.toRDivisor A + B))) GY)
    (hE0 : ∀ P, 0 ≤ (GX - GY).coeff P)
    (hEexc : ∀ P, (GX - GY).coeff P ≠ 0 → MMP.Flips.IsExceptionalPrimeDivisor sY q P)
    (Δq : QDivisor X) (hΔq : QDivisor.toRDivisor Δq = QDivisor.toRDivisor A + B)
    (U : S.Opens) (hU : IsAffineOpen U) :
    ∃ Gen : Finset (Polynomial ((rationalFunctionsPresheaf X).obj (op (g ⁻¹ᵁ U)))),
      {p : Polynomial ((rationalFunctionsPresheaf X).obj (op (g ⁻¹ᵁ U))) | ∀ m : ℕ,
          p.coeff m ∈ (m • K + DivisorWithCoeffs.roundDown ((m : ℚ) • Δq)).divisorialSubmodule
            (g ⁻¹ᵁ U)} =
        Subring.closure (Set.range (Polynomial.C.comp
            (((toRationalFunctionsPresheaf X).app (op (g ⁻¹ᵁ U))).hom.comp (g.app U).hom)) ∪
          ↑Gen) := by
  classical
  set Δ : RDivisor X := QDivisor.toRDivisor A + B with hΔdef
  -- instances
  have hXv := hWM.isNormalVariety_source
  have hYv := hWM.isNormalVariety_target
  have := hYv.1
  have := hWv
  have : MMP.Mori.IsVariety ℂ sX := hXv.1
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  have := isSeparated_toTerminal_of_isNormalVariety hXv
  have := isSeparated_toTerminal_of_isNormalVariety hYv
  have : AlgebraicGeometry.IsProjectiveVariety ℂ sS := hS
  have : IsSeparated (S ↘ ⊤_ Scheme) := by
    rw [show (S ↘ ⊤_ Scheme) = sS ≫ (Spec (.of ℂ) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have : IsProper p := isProper_of_isProjectiveMorphism p hpproj
  have : IsProper q := isProper_of_isProjectiveMorphism q hqproj
  have : IsDominant p := hpb.isDominant
  have : IsDominant q := hqb.isDominant
  have hWnv : IsNormalVariety ℂ sW := ⟨hWv, inferInstance⟩
  have hpq : p ≫ g = q ≫ πY := comp_eq_comp_of_isInverse hWM.isOver hinv hhq
  have hdimY : topologicalKrullDim Y = (3 : ℕ) := by
    rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY sW hqb,
      ← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX sW hpb, hdim]
    rfl
  -- the divisors
  set KY := MMP.Mori.RationalMap.transformDivisor φ K with hKYdef
  set Γq := MMP.Mori.RationalMap.transformDivisor φ Δq with hΓqdef
  have hΓR : QDivisor.toRDivisor Γq = MMP.Mori.RationalMap.transformDivisor φ Δ := by
    rw [hΓqdef, ← transformDivisor_qToRDivisor, hΔq]
  set DX := Divisor.toQDivisor K + Δq with hDXdef
  set DY := Divisor.toQDivisor KY + Γq with hDYdef
  have hDXq := isQCartier_of_isQFactorial sX hXQ DX
  have hDYq := isQCartier_of_isQFactorial sY hYQ DY
  have hset : {p : Polynomial ((rationalFunctionsPresheaf X).obj (op (g ⁻¹ᵁ U))) | ∀ m : ℕ,
      p.coeff m ∈ (m • K + DivisorWithCoeffs.roundDown ((m : ℚ) • Δq)).divisorialSubmodule
        (g ⁻¹ᵁ U)} = {p | ∀ m : ℕ, p.coeff m ∈
          (DivisorWithCoeffs.roundDown ((m : ℚ) • DX)).divisorialSubmodule (g ⁻¹ᵁ U)} := by
    ext p
    simp only [Set.mem_ofPred_eq, nsmul_add_roundDown_eq, DX]
  rw [hset]
  by_cases hU' : ((g ⁻¹ᵁ U : X.Opens) : Set X).Nonempty
  swap
  · have := subsingleton_rationalFunctionsPresheaf (g ⁻¹ᵁ U) hU'
    refine ⟨∅, Set.Subset.antisymm (fun p _ => ?_) (fun p _ m => ?_)⟩
    · rw [Subsingleton.elim p 0]
      exact Subring.zero_mem _
    · rw [Subsingleton.elim (p.coeff m) 0]
      exact Submodule.zero_mem _
  -- the pull-backs to `W`
  have hBp := map_componentGenericPoint_notMem_supp_of_isQCartier p hDXq
  have hBq := map_componentGenericPoint_notMem_supp_of_isQCartier q hDYq
  have hDWq := isQCartier_pullback p hDXq hBp
  have hRX : QDivisor.toRDivisor (DX.pullback hDXq hBp) = GX := by
    refine qToRDivisor_pullback_eq p hDXq hBp ?_
    have : QDivisor.toRDivisor DX = MMP.Flips.logCanonicalDivisor K Δ := by
      rw [hDXdef, map_add, QDivisor.toRDivisor_toQDivisor, hΔq]
      rfl
    rwa [this]
  have hRY : QDivisor.toRDivisor (DY.pullback hDYq hBq) = GY := by
    refine qToRDivisor_pullback_eq q hDYq hBq ?_
    have : QDivisor.toRDivisor DY = MMP.Flips.logCanonicalDivisor KY
        (MMP.Mori.RationalMap.transformDivisor φ Δ) := by
      rw [hDYdef, map_add, QDivisor.toRDivisor_toQDivisor, hΓR]
      rfl
    rwa [this]
  have hE : 0 ≤ DX.pullback hDXq hBp - DY.pullback hDYq hBq := by
    refine nonneg_of_qToRDivisor_nonneg ?_
    rwa [map_sub, hRX, hRY, Finsupp.le_def]
  have hEx : MMP.Resolution.IsExceptionalDivisorFor q
      (DX.pullback hDXq hBp - DY.pullback hDYq hBq) := by
    refine isExceptionalDivisorFor_of_isExceptionalPrimeDivisor (sY := sY) (sW := sW) hqb hdimY
      fun P hP => hEexc P ?_
    intro h0
    apply hP
    have h2 : QDivisor.toRDivisor (DX.pullback hDXq hBp - DY.pullback hDYq hBq) = GX - GY := by
      rw [map_sub, hRX, hRY]
    have h3 : (((DX.pullback hDXq hBp - DY.pullback hDYq hBq) P : ℚ) : ℝ) =
        (GX - GY).coeff P := by
      rw [← h2]; rfl
    rw [h0] at h3
    exact_mod_cast h3
  -- the isomorphism of floor sections
  obtain ⟨Θ, hΘm, hΘc⟩ := exists_ringEquiv_floorSections hXv hYv hWnv hpb hqb hpX hqY hpq DX DY
    hDXq hDYq hBp hBq hDWq hE hEx U hU'
  -- finite generation on the model
  obtain ⟨hG0, -, hGbig⟩ := isRelativelyBig_transformDivisor_of_isBirationalContraction sX sY sS
    hXv hX hYQ hWM.isProjectiveVariety_target hS g πY hg hWM.comp_eq_target φ hWM.isBirational
    hWM.isOver hWM.not_isInverseExceptional A hA0 (isQCartier_of_isQFactorial sX hXQ A) hA
  have hΔq0 : 0 ≤ Δq := nonneg_of_qToRDivisor_nonneg (by
    rw [hΔq]; exact add_nonneg (qToRDivisor_nonneg hA0) hB0)
  have hGΓ : MMP.Mori.RationalMap.transformDivisor φ A ≤ Γq := by
    rw [hΓqdef]
    refine transformDivisor_mono φ (sub_nonneg.mp (nonneg_of_qToRDivisor_nonneg ?_))
    rwa [map_sub, hΔq, add_sub_cancel_left]
  have hΓ0 : 0 ≤ Γq := transformDivisor_nonneg φ hΔq0
  have hΓklt : IsRealKltPair sY (QDivisor.toRDivisor Γq) := by rwa [hΓR]
  have hnef : MMP.Flips.IsRelativelyNef ℂ sY πY
      (Divisor.toRDivisor KY + QDivisor.toRDivisor Γq) := by
    rw [hΓR]
    exact hWM.isRelativelyNef
  obtain ⟨GenY, hGenY1, hGenY2⟩ := exists_finset_floor_model hYv hWM.isProjectiveVariety_target
    hS hWM.comp_eq_target hYQ hKY hG0 hGbig hGΓ hΓ0 hΓklt hnef U hU
  -- transport
  have hC : Polynomial.mapEquiv Θ '' Set.range (fun a : Γ(S, U) => Polynomial.C
      (algebraMap Γ(Y, πY ⁻¹ᵁ U) ((rationalFunctionsPresheaf Y).obj (op (πY ⁻¹ᵁ U)))
        (πY.app U a))) = Set.range (Polynomial.C.comp
          (((toRationalFunctionsPresheaf X).app (op (g ⁻¹ᵁ U))).hom.comp (g.app U).hom)) := by
    rw [← Set.range_comp]
    congr 1
    funext a
    simp only [Function.comp_apply, RingHom.comp_apply, Polynomial.mapEquiv_apply,
      Polynomial.map_C]
    exact congrArg Polynomial.C (hΘc a)
  exact exists_finset_eq_closure_of_ringEquiv Θ
    (fun m => ((DivisorWithCoeffs.roundDown ((m : ℚ) • DY)).divisorialSubmodule (πY ⁻¹ᵁ U) :
      Set _))
    (fun m => ((DivisorWithCoeffs.roundDown ((m : ℚ) • DX)).divisorialSubmodule (g ⁻¹ᵁ U) :
      Set _))
    (fun m c => hΘm m c) (floorSubring DX (g ⁻¹ᵁ U)) (fun p => mem_floorSubring) _ _ hC
    (by rintro _ ⟨a, rfl⟩; exact C_mem_floorSubring DX _ (g.app U a)) GenY hGenY1 hGenY2

end FiniteGeneration

/-- **Big-boundary models and fixed parts for projective threefolds.** Let `g : X ⟶ S` be a
morphism of projective varieties over `ℂ` with `X` a `ℚ`-factorial normal threefold with canonical
divisor `K`, and let `Δ = A + B` with `A ≥ 0` a relatively big `ℚ`-divisor and `B ≥ 0` an
`ℝ`-divisor such that `(X, Δ)` is klt and `K + Δ` is relatively pseudo-effective over `S`. Then:

* there is a `ℚ`-factorial klt nef weak model `φ : X ⇢ Y` of `(X, Δ)` over `S`;
* for `Ξ ≥ 0` supported in the support of `Δ`, klt and with coefficients sufficiently close to
  those of `Δ`, every prime divisor in the relative divisorial stable base of `K + Δ` lies in that
  of `K + Ξ`;
* there are `ε > 0` and `r > 0` such that for every klt `Ξ ≥ 0` in the smallest rational affine
  hull of `Δ` with coefficients within `ε` of those of `Δ`, every prime divisor with positive
  relative fixed multiplicity in `r • D`, for a Cartier divisor `D` with `D = (k / r)(K + Ξ)`,
  lies in the relative divisorial stable base of `K + Δ`;
* if `Δ` is a `ℚ`-divisor, then over every affine open `U ⊆ S` the algebra of polynomials whose
  `m`-th coefficient is a section of `𝒪_X(mK + ⌊mΔ⌋)` over `g⁻¹U` is generated by `Γ(S, U)` and
  finitely many elements. -/
theorem solution
    {X S : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)} {g : X ⟶ S} {K : Divisor X}
    {A : QDivisor X} {B : RDivisor X}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    (hg : g ≫ sS = sX) (hXQ : IsQFactorial sX) (hdim : topologicalKrullDim X = 3)
    (hK : ∃ n : ℕ, K.IsCanonicalDivisor sX n) (hA0 : 0 ≤ A) (hA : A.IsRelativelyBig g)
    (hB0 : 0 ≤ B) (hΔ : IsRealKltPair sX (QDivisor.toRDivisor A + B))
    (hpsef : ∃ (m : ℕ) (r : Fin m → ℝ) (E : Fin m → X.CartierDivisor) (w : Fin m → Divisor X),
      (∀ i, MMP.Intersection.IsWeilDivisorOfCartier (E i) (w i)) ∧
      logCanonicalDivisor K (QDivisor.toRDivisor A + B) =
        ∑ i, r i • Divisor.toRDivisor (w i) ∧
      KCartierDivisor.IsRelativelyPseudoEffective sX g (∑ i, Finsupp.single (E i) (r i))) :
    -- the log terminal model
    (∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (_ : IsNormal Y)
      (sY : Y ⟶ Spec (.of ℂ)) (_ : QuasiCompact sY) (πY : Y ⟶ S) (φ : X.RationalMap Y),
      IsNefWeakModel sX sY sS g πY K (QDivisor.toRDivisor A + B) φ ∧ IsQFactorial sY ∧
        IsRealKltPair sY (MMP.Mori.RationalMap.transformDivisor φ (QDivisor.toRDivisor A + B))) ∧
    -- persistence of the divisorial stable base primes near `Δ`
    (∃ ε : ℝ, 0 < ε ∧ ∀ Ξ : RDivisor X, Ξ.support ⊆ (QDivisor.toRDivisor A + B).support →
      0 ≤ Ξ → IsRealKltPair sX Ξ →
      (∀ P, |Ξ.coeff P - (QDivisor.toRDivisor A + B).coeff P| < ε) →
      ∀ G : MMP.Mori.PrimeDivisor X,
        IsInRelativeDivisorialStableBase g (logCanonicalDivisor K (QDivisor.toRDivisor A + B)) G →
          IsInRelativeDivisorialStableBase g (logCanonicalDivisor K Ξ) G) ∧
    -- the fixed parts along the smallest rational affine hull
    (∃ ε : ℝ, 0 < ε ∧ ∃ r : ℕ, 0 < r ∧ ∀ Ξ : RDivisor X,
      IsInSmallestRationalAffineHull (QDivisor.toRDivisor A + B) Ξ →
      0 ≤ Ξ → IsRealKltPair sX Ξ →
      (∀ P, |Ξ.coeff P - (QDivisor.toRDivisor A + B).coeff P| < ε) →
      ∀ k : ℕ, 0 < k → ∀ D : Divisor X, D.IsCartier →
        (∀ P, (k : ℝ) / r * (logCanonicalDivisor K Ξ).coeff P = D.coeff P) →
        ∀ G : MMP.Mori.PrimeDivisor X, 0 < relativeFixedMultiplicity g ((r : ℤ) • D) G →
          IsInRelativeDivisorialStableBase g
            (logCanonicalDivisor K (QDivisor.toRDivisor A + B)) G) ∧
    -- local finite generation of the floor-section algebra for rational `Δ`
    (∀ Δq : QDivisor X, QDivisor.toRDivisor Δq = QDivisor.toRDivisor A + B →
      ∀ U : S.Opens, IsAffineOpen U →
        ∃ Gen : Finset (Polynomial ((rationalFunctionsPresheaf X).obj (op (g ⁻¹ᵁ U)))),
          {p : Polynomial ((rationalFunctionsPresheaf X).obj (op (g ⁻¹ᵁ U))) | ∀ m : ℕ,
              p.coeff m ∈ (m • K + DivisorWithCoeffs.roundDown ((m : ℚ) • Δq)).divisorialSubmodule
                (g ⁻¹ᵁ U)} =
            Subring.closure (Set.range (Polynomial.C.comp
                (((toRationalFunctionsPresheaf X).app (op (g ⁻¹ᵁ U))).hom.comp (g.app U).hom)) ∪
              ↑Gen)) := by
  classical
  have hΔ0 : 0 ≤ QDivisor.toRDivisor A + B := add_nonneg (qToRDivisor_nonneg hA0) hB0
  obtain ⟨Y, iY, nY, normY, sY, qcY, πY, φ, hWM, hYQ, hYklt, W, iW, nW, normW, sW, p, q, h,
    hWv, -, hpX, hqY, hpproj, hqproj, hpb, hqb, hinv, hhq, GX, GY, hGX, hGY, hE0, hEexc, -⟩ :=
    IsRealKltPair.exists_isNefWeakModel_of_isRelativelyPseudoEffective hX hS hg hXQ hdim hK hΔ0
      hΔ hpsef
  have hKY : ∃ m : ℕ, MMP.Mori.Divisor.IsCanonicalDivisor sY m
      (MMP.Mori.RationalMap.transformDivisor φ K) := by
    have hXv := hWM.isNormalVariety_source
    have hYv := hWM.isNormalVariety_target
    have := hYv.1
    have := hWv
    have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
    have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
    have : IsProper p := isProper_of_isProjectiveMorphism p hpproj
    have : IsProper q := isProper_of_isProjectiveMorphism q hqproj
    have : IsDominant p := hpb.isDominant
    have : IsDominant q := hqb.isDominant
    obtain ⟨n, hKn⟩ := hK
    obtain ⟨n', KY₀, hKY₀, -⟩ := hYklt.2.2.1
    have hnn : n' = n := by
      have h1 := hKn.topologicalKrullDim_eq
      have h2 := hKY₀.topologicalKrullDim_eq
      rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY sW hqb,
        ← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX sW hpb, h1] at h2
      exact_mod_cast h2.symm
    subst hnn
    exact ⟨n', isCanonicalDivisor_transformDivisor_of_isInverse hXv hYv ⟨hWv, inferInstance⟩ hpb
      hqb hpX hqY hinv hhq hWM.not_isInverseExceptional hKn hKY₀⟩
  obtain ⟨h2, h3⟩ := exists_stableBase_and_fixedParts hX hS hg hXQ hA0 hA hB0 hWM hKY hYQ hYklt
    hWv hpX hqY hpproj hqproj hpb hqb hinv hhq hGX hGY hE0
  exact ⟨⟨Y, iY, nY, normY, sY, qcY, πY, φ, hWM, hYQ, hYklt⟩, h2, h3,
    fun Δq hΔq U hU => fg_floorSections_of_isNefWeakModel hX hS hg hXQ hdim hA0 hA hB0 hWM hKY hYQ
      hYklt hWv hpX hqY hpproj hqproj hpb hqb hinv hhq hGX hGY hE0 hEexc Δq hΔq U hU⟩

end

end MMP.FourfoldProofs.FourfoldProjectiveThreefoldF3Proof

end

section

/-!
# Projective threefold big-boundary models and fixed parts

Let `g : X ⟶ S` be a morphism of projective complex varieties, with `X` a normal `ℚ`-factorial
threefold with canonical divisor `K`, and let `Δ = A + B` be an effective real klt boundary on
`X`, where `A ≥ 0` is a `ℚ`-Cartier `ℚ`-divisor big over `S` and `B ≥ 0`. If `K + Δ` is
pseudo-effective over `S`, then:

* `(X, Δ)` has a log terminal model over `S`: a nef weak model `φ : X ⤏ Y` over `S` with `Y`
  projective and `ℚ`-factorial and `(Y, φ_* Δ)` klt;
* there is a neighbourhood of `Δ`, in the real span of the prime components of `Δ`, such that
  every divisorial stable base prime of `K + Δ` over `S` is one of `K + Ξ` for every effective
  klt boundary `Ξ` in it;
* there are an integer `r > 0` and a neighbourhood of `Δ` in the smallest rational affine hull
  of `Δ` such that, for every effective klt boundary `Ξ` in it and every `k > 0` with
  `k(K + Ξ)/r` integral Cartier, every prime divisor in the fixed part of `|k(K + Ξ)|` over `S`
  is a divisorial stable base prime of `K + Δ` over `S`;
* if `Δ` is rational, the graded `𝒪_S`-algebra `⊕_{m ≥ 0} g_* 𝒪_X(⌊m(K + Δ)⌋)` is locally of
  finite type: over every affine open `U ⊆ S`, its sections
  `⊕_{m ≥ 0} H⁰(g⁻¹U, ⌊m(K + Δ)⌋) tᵐ` form a finitely generated `Γ(U, 𝒪_S)`-algebra.

## Main results

* `MMP.Fourfold.IsRealKltPair.exists_isNefWeakModel_and_fixedParts_of_isRelativelyBig`.

## Implementation notes

The log terminal model is `MMP.Fourfold.IsNefWeakModel` (birational contraction, nef adjoint
over `S`, effective `q`-exceptional comparison on a common resolution), with `K_Y = φ_* K`,
together with `ℚ`-factoriality and kltness of the target. Pseudo-effectivity over `S` is
`MMP.Fourfold.KCartierDivisor.IsRelativelyPseudoEffective` of an `ℝ`-Cartier presentation
`∑ rᵢ Aᵢ` of `K + Δ`, as in
`MMP.Fourfold.IsRealKltPair.exists_isNefWeakModel_of_isRelativelyPseudoEffective`.

Neighbourhoods in the finite-dimensional coefficient spaces are taken for the maximum norm of
the coefficients, and the fixed part of `|rD|` over `S` is described prime by prime through
`MMP.Fourfold.relativeFixedMultiplicity`, as in
`MMP.Fourfold.BirationalFiniteGenerationProperty`. The sections over `U` of the floor-section
algebra are the polynomials in `𝒦_X(g⁻¹U)[t]` whose coefficient of `tᵐ` is a section of
`𝒪_X(mK + ⌊mΔ⌋)` over `g⁻¹U`; finite generation over `Γ(U, 𝒪_S)` is the equality of this set
with the subring generated by the image of `Γ(U, 𝒪_S)` and finitely many elements.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori MMP.Flips

/-- **Projective threefold big-boundary models and fixed parts.** Let `g : X ⟶ S` be a morphism
of projective complex varieties, `X` a normal `ℚ`-factorial threefold with canonical divisor `K`,
and `Δ = A + B` an effective real klt boundary with `A ≥ 0` a `ℚ`-Cartier `ℚ`-divisor big over
`S` and `B ≥ 0`. If `K + Δ` is pseudo-effective over `S`, then `(X, Δ)` has a `ℚ`-factorial klt
nef weak model over `S`; the divisorial stable base primes of `K + Δ` over `S` persist for all
effective klt boundaries near `Δ` in the span of its components; for some `r > 0` and all
effective klt boundaries `Ξ` near `Δ` in its smallest rational affine hull, every fixed prime of
`|k(K + Ξ)|` over `S` with `k(K + Ξ)/r` integral Cartier is a stable base prime of `K + Δ`;
and if `Δ` is rational the algebra `⊕_m g_* 𝒪_X(⌊m(K + Δ)⌋)` is finitely generated over every
affine open of `S`. -/
@[mmp "thm_fourfold_projective_threefold_f3"]
public theorem IsRealKltPair.exists_isNefWeakModel_and_fixedParts_of_isRelativelyBig
    {X S : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)} {g : X ⟶ S} {K : Divisor X}
    {A : QDivisor X} {B : RDivisor X}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    (hg : g ≫ sS = sX) (hXQ : IsQFactorial sX) (hdim : topologicalKrullDim X = 3)
    (hK : ∃ n : ℕ, K.IsCanonicalDivisor sX n) (hA0 : 0 ≤ A) (hA : A.IsRelativelyBig g)
    (hB0 : 0 ≤ B) (hΔ : IsRealKltPair sX (QDivisor.toRDivisor A + B))
    (hpsef : ∃ (m : ℕ) (r : Fin m → ℝ) (E : Fin m → X.CartierDivisor) (w : Fin m → Divisor X),
      (∀ i, MMP.Intersection.IsWeilDivisorOfCartier (E i) (w i)) ∧
      logCanonicalDivisor K (QDivisor.toRDivisor A + B) =
        ∑ i, r i • Divisor.toRDivisor (w i) ∧
      KCartierDivisor.IsRelativelyPseudoEffective sX g (∑ i, Finsupp.single (E i) (r i))) :
    -- the log terminal model
    (∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (_ : IsNormal Y)
      (sY : Y ⟶ Spec (.of ℂ)) (_ : QuasiCompact sY) (πY : Y ⟶ S) (φ : X.RationalMap Y),
      IsNefWeakModel sX sY sS g πY K (QDivisor.toRDivisor A + B) φ ∧ IsQFactorial sY ∧
        IsRealKltPair sY (MMP.Mori.RationalMap.transformDivisor φ (QDivisor.toRDivisor A + B))) ∧
    -- persistence of the divisorial stable base primes near `Δ`
    (∃ ε : ℝ, 0 < ε ∧ ∀ Ξ : RDivisor X, Ξ.support ⊆ (QDivisor.toRDivisor A + B).support →
      0 ≤ Ξ → IsRealKltPair sX Ξ →
      (∀ P, |Ξ.coeff P - (QDivisor.toRDivisor A + B).coeff P| < ε) →
      ∀ G : MMP.Mori.PrimeDivisor X,
        IsInRelativeDivisorialStableBase g (logCanonicalDivisor K (QDivisor.toRDivisor A + B)) G →
          IsInRelativeDivisorialStableBase g (logCanonicalDivisor K Ξ) G) ∧
    -- the fixed parts along the smallest rational affine hull
    (∃ ε : ℝ, 0 < ε ∧ ∃ r : ℕ, 0 < r ∧ ∀ Ξ : RDivisor X,
      IsInSmallestRationalAffineHull (QDivisor.toRDivisor A + B) Ξ →
      0 ≤ Ξ → IsRealKltPair sX Ξ →
      (∀ P, |Ξ.coeff P - (QDivisor.toRDivisor A + B).coeff P| < ε) →
      ∀ k : ℕ, 0 < k → ∀ D : Divisor X, D.IsCartier →
        (∀ P, (k : ℝ) / r * (logCanonicalDivisor K Ξ).coeff P = D.coeff P) →
        ∀ G : MMP.Mori.PrimeDivisor X, 0 < relativeFixedMultiplicity g ((r : ℤ) • D) G →
          IsInRelativeDivisorialStableBase g
            (logCanonicalDivisor K (QDivisor.toRDivisor A + B)) G) ∧
    -- local finite generation of the floor-section algebra for rational `Δ`
    (∀ Δq : QDivisor X, QDivisor.toRDivisor Δq = QDivisor.toRDivisor A + B →
      ∀ U : S.Opens, IsAffineOpen U →
        ∃ Gen : Finset (Polynomial ((rationalFunctionsPresheaf X).obj (op (g ⁻¹ᵁ U)))),
          {p : Polynomial ((rationalFunctionsPresheaf X).obj (op (g ⁻¹ᵁ U))) | ∀ m : ℕ,
              p.coeff m ∈ (m • K + DivisorWithCoeffs.roundDown ((m : ℚ) • Δq)).divisorialSubmodule
                (g ⁻¹ᵁ U)} =
            Subring.closure (Set.range (Polynomial.C.comp
                (((toRationalFunctionsPresheaf X).app (op (g ⁻¹ᵁ U))).hom.comp (g.app U).hom)) ∪
              ↑Gen)) :=
  MMP.FourfoldProofs.FourfoldProjectiveThreefoldF3Proof.solution hX hS hg hXQ hdim hK hA0 hA hB0 hΔ hpsef

end MMP.Fourfold

end
