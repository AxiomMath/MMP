module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.FiniteGeneration
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
public import MMP.AlgebraicGeometry.Singularities.FiniteLowDiscrepancyKlt
public import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
public import MMP.AlgebraicGeometry.MMP.Fourfold.CanonicalDifficulty
public import MMP.AlgebraicGeometry.Singularities.PairClasses
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
public import MMP.AlgebraicGeometry.MMP.Threefold.Discrepancy
public import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
public import MMP.AlgebraicGeometry.Singularities.DivisorOver
public import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
public import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
public import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
public import MMP.AlgebraicGeometry.Resolution.DisjoiningSequence
public import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction
public import MMP.AlgebraicGeometry.Resolution.ExceptionalDivisorPrime
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
public import MMP.AlgebraicGeometry.Curves.PluricanonicalSectionsSeparatePoints
public import MMP.AlgebraicGeometry.Singularities.SncLogDiscrepancyFormula

universe u

section

/-!
# Uniform finiteness of low discrepancies near a real klt pair

Let `B_i → B` be effective real boundaries on a normal `ℚ`-factorial projective variety `X`,
supported on a fixed finite set `T` of prime divisors, with `(X, B)` klt. Let `F = ∑_{P ∈ T} P`.
Klt is open on the fixed support, so `B⁺ = B + η F` is klt for some `η > 0`, and `B_i ≤ B⁺` for
all large `i`. Log discrepancies decrease when an effective `ℝ`-Cartier divisor is added to the
boundary, so every exceptional valuation with `a(E, X, B_i) ≤ 1` has `a(E, X, B⁺) ≤ 1`, and these
form a finite set. On a nef weak model `X ⤏ Z` of `(X, B_i)` the log discrepancies only increase,
`a(E, Z, B_Z) ≥ a(E, X, B_i)`. For a fixed valuation `E`, `a(E, X, B_i)` is an affine function of
the coefficients of `B_i`, so it converges to `a(E, X, B)`; and by crepancy `a(E, X, B)` is the log
discrepancy of `E` on any crepant real terminal model, where an exceptional valuation has log
discrepancy `> 1`.

## Main results

* `MMP.FourfoldProofs.FourfoldUniformLowDiscrepanciesNearKltProof.solution`.

## Implementation notes

* Klt is open along the fixed support (`exists_isRealKltPair_add`): on a log resolution of
  `T ∪ Supp B` the crepant boundary of `B + η F` is supported on the snc configuration, its
  coefficients are `1 - a(R, X, B) + η coeff_R(f^*F)`, which stay `< 1` for small `η`, and the snc
  formula then gives positive log discrepancies; `ℚ`-factoriality makes every real divisor
  `ℝ`-Cartier, so `K_X + B + η F` is `ℝ`-Cartier.
* The comparison on a nef weak model (`weakModel_isLogDiscrepancy`) is made on its common
  resolution `p : W ⟶ X`, `q : W ⟶ Z`: with `K_X = div(ω)`, a form `τ` on `Z` with
  `div(q^*τ) = div(p^*ω)` has `div(τ) = φ_* K_X`, because every prime divisor of `Z` is the
  transform of a prime divisor of `X` with which it has a common strict transform on `W`. Crepant
  invariance along `p` and along `q` reduces the comparison to the effective difference
  `p^*(K_X + B_i) - q^*(K_Z + B_Z)` on `W`.
* For a fixed valuation, `a(E, X, B_i) = a(E, X, B) - ∑_{P ∈ T} (b_{i,P} - b_P) coeff_E(f^*P)`
  with the pull-backs `f^*P` fixed, which gives the continuity in the coefficients
  (`exists_tendsto_isLogDiscrepancy`).

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
-/

open CategoryTheory AlgebraicGeometry Filter
open scoped WithZero

namespace MMP.FourfoldProofs.FourfoldUniformLowDiscrepanciesNearKltProof

open MMP MMP.Mori MMP.Fourfold

section Linear

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X]

/-- If every Weil divisor has a Cartier multiple, every `ℝ`-divisor is `ℝ`-Cartier:
`D = ∑_P (d_P / m_P) (m_P P)` with `m_P P` Cartier. -/
private theorem isRCartier_of_forall_isCartier_nsmul
    (hQ : ∀ D : Divisor X, ∃ m : ℕ, 0 < m ∧ ((m : ℤ) • D).IsCartier) (D : RDivisor X) :
    RDivisor.IsRCartier D := by
  classical
  choose m hm hmC using fun P : MMP.Mori.PrimeDivisor X => hQ (Finsupp.single P 1)
  let e := D.support.equivFin
  refine ⟨D.support.card, fun i => D (e.symm i) / m (e.symm i),
    fun i => ((m (e.symm i) : ℕ) : ℤ) • Finsupp.single (e.symm i).1 1, fun i => hmC _,
    fun Γ => ?_⟩
  change D Γ = _
  have key : ∀ P : MMP.Mori.PrimeDivisor X, D P / (m P : ℝ) *
      ((DivisorWithCoeffs.coeff (((m P : ℕ) : ℤ) • (Finsupp.single P (1 : ℤ)) : Divisor X) Γ :
        ℤ) : ℝ) =
        if P = Γ then D P else 0 := by
    intro P
    have hm0 : (m P : ℝ) ≠ 0 := by exact_mod_cast (hm P).ne'
    simp only [DivisorWithCoeffs.coeff_apply, Finsupp.smul_apply, Finsupp.single_apply,
      smul_eq_mul]
    split_ifs <;> simp [hm0]
  simp_rw [key]
  rw [e.symm.sum_comp (fun x : D.support => if x.1 = Γ then D x.1 else 0),
    Finset.sum_coe_sort D.support (fun x => if x = Γ then D x else 0)]
  simp only [Finset.sum_ite_eq', Finsupp.mem_support_iff]
  split_ifs with h
  · rfl
  · exact not_not.mp h

/-- On a `ℚ`-factorial variety every `ℝ`-divisor is `ℝ`-Cartier. -/
private theorem isRCartier_of_isQFactorial (hQ : IsQFactorial sX) (D : RDivisor X) :
    RDivisor.IsRCartier D :=
  isRCartier_of_forall_isCartier_nsmul hQ.2 D

/-- On a smooth variety every `ℝ`-divisor is `ℝ`-Cartier. -/
private theorem isRCartier_of_isSmoothScheme (hsm : MMP.Mori.IsSmoothScheme sX) (D : RDivisor X) :
    RDivisor.IsRCartier D :=
  isRCartier_of_forall_isCartier_nsmul
    (fun D => ⟨1, one_pos, by simpa using MMP.Fourfold.isCartier_of_isSmoothScheme hsm D⟩) D

/-- **Adding an `ℝ`-Cartier divisor to the boundary.** If `a = a(E, X, B)` and `G = f^*L` is a
pull-back of an `ℝ`-Cartier divisor `L` to the model of `E`, then
`a(E, X, B + L) = a - coeff_E G`. -/
private theorem isLogDiscrepancy_add {n : ℕ} {B L : RDivisor X} {E : DivisorOver k sX} {a : ℝ}
    (h : MMP.Intersection.IsLogDiscrepancy sX n B E a) {G : RDivisor E.Y}
    (hG : haveI := E.isLocallyNoetherian; haveI := E.isNormal
      MMP.Flips.IsRCartierPullback E.f L G) :
    MMP.Intersection.IsLogDiscrepancy sX n (B + L) E (a - G.coeff E.E) := by
  have := E.isLocallyNoetherian
  have := E.isNormal
  obtain ⟨hX, hp, ω, hω0, hK, m, r, C, C', hC, hrel, hpb, rfl⟩ := h
  obtain ⟨m', r', L₀, L₀', hL₀, rfl, hpb', rfl⟩ := hG
  refine ⟨hX, hp, ω, hω0, hK, m + m', Fin.append r r', Fin.append C L₀, Fin.append C' L₀', ?_,
    fun Γ => ?_, ?_, ?_⟩
  · intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa using hC i
    · simpa using hL₀ i
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, DivisorWithCoeffs.coeff_add,
      MMP.Fourfold.coeff_sum_smul_toRDivisor, ← hrel Γ]
    ring
  · intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa using hpb i
    · obtain ⟨hB, hp⟩ := hpb' i
      exact ⟨by simpa using hB, by simpa using hp⟩
  · rw [Fin.sum_univ_add, MMP.Fourfold.coeff_sum_smul_toRDivisor]
    simp only [Fin.append_left, Fin.append_right]
    ring

/-- A divisor over `X` carrying a log discrepancy has a proper, hence quasi-compact, model; an
`ℝ`-Cartier divisor on `X` pulls back to it, effectively if it is effective. -/
private theorem exists_isRCartierPullback {n : ℕ} {B : RDivisor X} {E : DivisorOver k sX}
    {a : ℝ} (h : MMP.Intersection.IsLogDiscrepancy sX n B E a) {L : RDivisor X}
    (hL : RDivisor.IsRCartier L) :
    haveI := E.isLocallyNoetherian; haveI := E.isNormal
    ∃ G : RDivisor E.Y, MMP.Flips.IsRCartierPullback E.f L G ∧ (0 ≤ L → 0 ≤ G) := by
  have := E.isLocallyNoetherian
  have := E.isNormal
  have := E.isIntegral
  have := E.isDominant
  have hX := h.1
  have : IsProper E.f := h.2.1
  have : CompactSpace X := hX.1.toQuasiCompact.compactSpace_of_compactSpace
  have : CompactSpace E.Y := QuasiCompact.compactSpace_of_compactSpace E.f
  obtain ⟨m, r, C, hC, hcoeff⟩ := id hL
  choose C' hC' using fun j => (hC j).exists_isPullback
    (map_componentGenericPoint_notMem_supp_of_isDominant E.f (C j))
  have hG : MMP.Flips.IsRCartierPullback E.f L (∑ j, r j • Divisor.toRDivisor (C' j)) := by
    refine ⟨m, r, C, C', hC, ?_, fun j => ⟨_, hC' j⟩, rfl⟩
    ext P
    rw [hcoeff P, MMP.Fourfold.coeff_sum_smul_toRDivisor]
  exact ⟨_, hG, fun h0 => (MMP.Fourfold.isEffective_of_isRCartierPullback E.f hL h0).2 _ hG⟩

/-- A divisor over a normal variety with a proper model has a log discrepancy for every boundary
`B` with `K_X + B` `ℝ`-Cartier. -/
private theorem exists_isLogDiscrepancy [PerfectField k] (hX : IsNormalVariety k sX) {n : ℕ}
    {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) {B : RDivisor X}
    (hKB : RDivisor.IsRCartier (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero K + B))
    (E : DivisorOver k sX) (hE : IsProper E.f) :
    ∃ a, MMP.Intersection.IsLogDiscrepancy sX n B E a := by
  have := E.isLocallyNoetherian
  have := E.isNormal
  have := E.isIntegral
  have := E.isDominant
  have : CompactSpace X := hX.1.toQuasiCompact.compactSpace_of_compactSpace
  have : CompactSpace E.Y := QuasiCompact.compactSpace_of_compactSpace E.f
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain ⟨m, r, C, hC, hcoeff⟩ := hKB
  choose C' hC' using fun j => MMP.Threefold.Bridges.exists_isPullback_of_isDominant E.f (hC j)
  refine ⟨_, hX, hE, ω, hω0, ⟨K, hK, fun Γ => (hω Γ).symm⟩, m, r, C, C', hC, fun Γ => ?_,
    fun j => ⟨_, hC' j⟩, rfl⟩
  rw [← hcoeff Γ, hω Γ]
  rfl

end Linear

section Lifting

open scoped WithZero
open MMP.Flips
open MMP.Mori hiding IsLogResolution exceptionalSet

/-- The valuation of a prime divisor `P` of `X`, viewed as a divisor over `X`, is `ord_P`. -/
private theorem valuation_ofPrimeDivisor {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    (P : MMP.Mori.PrimeDivisor X) :
    (DivisorOver.ofPrimeDivisor k hX P).valuation = P.divisorialValuation :=
  Valuation.ext fun φ => by
    change P.divisorialValuation (functionFieldMap (𝟙 X) φ) = _
    rw [functionFieldMap_id_apply]

/-- A divisor over a normal variety which is not exceptional has the valuation of a prime divisor
of the variety. -/
private theorem exists_primeDivisor_divisorialValuation_eq {k : Type u} [Field k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) (D : DivisorOver k sX) (hD : ¬ D.IsExceptional) :
    ∃ P : MMP.Mori.PrimeDivisor X, D.valuation = P.divisorialValuation := by
  obtain ⟨P, hP⟩ := MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hX D hD
  exact ⟨P, hP.trans (valuation_ofPrimeDivisor hX P)⟩

/-- A divisor over a normal variety is exceptional (in the sense of Kollár–Mori) if and only if
its center has codimension at least two. -/
private theorem divisorOver_isExceptional_iff_two_le_coheight {k : Type u} [Field k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) (D : DivisorOver k sX) :
    D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  have := D.isLocallyNoetherian
  have := D.isNormal
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (X ↘ ⊤_ Scheme) := by
    rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  unfold DivisorOver.IsExceptional
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  have hcl : TopologicalSpace.Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set X), D.center.isClosed⟩ := TopologicalSpace.Closeds.ext rfl
  rw [hcl, closedsCodimension_coe, MMP.Positivity.DivisorOver.codimension_center]

/-- By the valuative criterion, a valuation of `k(Y)` which is centred on a point of `X` is
centred on a point of `Y` when `f : Y ⟶ X` is proper and dominant. -/
private theorem exists_center_of_isProper {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    {f : Y ⟶ X} [IsProper f] [IsDominant f] (ξ : Valuation Y.functionField ℤᵐ⁰) (z : X)
    (hz : ∀ b : X.presheaf.stalk z, ξ (functionFieldMap f (algebraMap _ X.functionField b)) ≤ 1) :
    ∃ x : Y, (∀ a : Y.presheaf.stalk x, ξ (algebraMap _ Y.functionField a) ≤ 1) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk x),
        ξ (algebraMap _ Y.functionField a) < 1 := by
  let R := ξ.valuationSubring
  let φ : X.presheaf.stalk z →+* R :=
    ((functionFieldMap f).comp (algebraMap (X.presheaf.stalk z) X.functionField)).codRestrict R
      fun b => (ξ.mem_valuationSubring_iff _).2 (by rw [RingHom.comp_apply]; exact hz b)
  have hgen : genericPoint X ⤳ z := (genericPoint_spec X).specializes trivial
  have hex : ValuativeCriterion.Existence f := by
    have h : @IsProper _ _ f := inferInstance
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1.existence
  let S : ValuativeCommSq f :=
    { R := R
      K := Y.functionField
      i₁ := Y.fromSpecStalk (genericPoint Y)
      i₂ := Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk z
      commSq := ⟨by
        rw [← functionFieldMap_fromSpecStalk f,
          ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgen, ← Category.assoc,
          ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
        rfl⟩ }
  obtain ⟨⟨l, hl₁, -⟩⟩ := (hex S).exists_lift
  have hl₁' : Spec.map (CommRingCat.ofHom (algebraMap R Y.functionField)) ≫ l =
      Y.fromSpecStalk (genericPoint Y) := hl₁
  set x := l (IsLocalRing.closedPoint R)
  have hx : genericPoint Y ⤳ x := (genericPoint_spec Y).specializes trivial
  let g := Scheme.stalkClosedPointTo l
  have hg : g ≫ CommRingCat.ofHom (algebraMap R Y.functionField) =
      Y.presheaf.stalkSpecializes hx := by
    apply Spec.map_injective
    apply (cancel_mono (Y.fromSpecStalk x)).mp
    rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hl₁',
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hga : ∀ a : Y.presheaf.stalk x,
      algebraMap _ Y.functionField a = ((g.hom a : R) : Y.functionField) := fun a =>
    (congrArg (fun q => q.hom a) hg).symm
  refine ⟨x, fun a => ?_, fun a ha => ?_⟩
  · rw [hga]
    exact (g.hom a).2
  · rw [hga]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp
      (fun hu => (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit g.hom a hu))

/-- For a proper birational morphism `f : Y ⟶ X` from a normal variety, every divisor `D` over
`X` has the valuation of a divisor `E` over `Y`, read on `k(X)` through `f^*`: by the valuative
criterion the valuation ring of `ord_D` dominates the local ring of a point of `Y`. -/
private theorem exists_properDivisorOver_comap_eq {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral Y] {f : Y ⟶ X}
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) [IsProper f]
    (D : ProperDivisorOver k sX) :
    haveI : IsDominant f := hf.isDominant
    ∃ E : ProperDivisorOver k (f ≫ sX), E.valuation.comap (functionFieldMap f) = D.valuation := by
  have : IsDominant f := hf.isDominant
  have : IsNormal Y := hY.2
  have : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  have hbW := hf.functionFieldMap_bijective
  let e : X.functionField ≃+* Y.functionField := RingEquiv.ofBijective (functionFieldMap f) hbW
  let ξ : Valuation Y.functionField ℤᵐ⁰ := D.valuation.comap (e.symm : Y.functionField →+* _)
  have hξ : ξ.comap (functionFieldMap f) = D.valuation := by
    ext t
    exact congrArg D.valuation (e.symm_apply_apply t)
  obtain ⟨x, h1, h2⟩ := exists_center_of_isProper ξ (D.f D.E.genericPoint) fun b => by
    rw [show ξ (functionFieldMap f (algebraMap _ X.functionField b)) =
        D.valuation (algebraMap _ X.functionField b) by
      simpa only [Valuation.comap_apply] using
        congrArg (fun v => v (algebraMap _ X.functionField b)) hξ]
    exact MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D.toDivisorOver _ rfl _
  have : AlgebraicGeometry.IsVariety k (f ≫ sX) := hY.1
  have hdiv : MMP.Flips.IsDivisorOfFunctionField k (f ≫ sX) ξ := by
    have := D.isIntegral
    have := D.isNormal
    have := D.isLocallyNoetherian
    have := D.isDominant
    refine ⟨D.Y, D.f ≫ sX, D.isNormalVariety, D.E, ?_⟩
    let := MMP.Mori.functionFieldAlgebra sX
    let := MMP.Mori.functionFieldAlgebra (f ≫ sX)
    let := MMP.Mori.functionFieldAlgebra (D.f ≫ sX)
    let eP := MMP.Mori.functionFieldAlgEquiv sX f hbW
    let eY :=
      MMP.Mori.functionFieldAlgEquiv sX D.f D.isBirationalMorphism.functionFieldMap_bijective
    refine ⟨eP.symm.trans eY, ?_⟩
    ext t
    obtain ⟨s, rfl⟩ := hbW.2 t
    have hs := congrArg (fun v => v s) hξ
    simp only [Valuation.comap_apply] at hs
    have h1 : eP.symm (functionFieldMap f s) = s := eP.symm_apply_apply s
    change ξ (functionFieldMap f s) = D.E.divisorialValuation (eY (eP.symm (functionFieldMap f s)))
    rw [h1, hs]
    rfl
  obtain ⟨D', -, hv, -⟩ :=
    MMP.Flips.exists_properDivisorOver_isProjective_of_dominates (f ≫ sX) hdiv x h1 h2
  exact ⟨D', by rw [hv, hξ]⟩

/-- The valuation `ord_E` of a divisor `(Y, f, E)` over `X` has nonempty center on `X`. -/
private theorem hasNonemptyCenter_valuation {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] (E : ProperDivisorOver k sX) : HasNonemptyCenter k sX E.valuation := by
  haveI := E.isIntegral
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  haveI := E.isDominant
  refine ⟨⟨E.Y, E.f ≫ sX, E.isNormalVariety, E.E,
    functionFieldAlgEquiv sX E.f E.isBirationalMorphism.functionFieldMap_bijective, ?_⟩, E, rfl⟩
  rfl

end Lifting

section Dictionary

open MMP.Flips
open MMP.Mori hiding IsLogResolution exceptionalSet

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]

/-- A presentation of `div(ω) + B`, coefficientwise, is a presentation as `ℝ`-divisors. -/
private theorem toRDivisor_add_eq_sum_of_coeff {n : ℕ} {B : RDivisor X}
    {ω : RationalPluriForms sX n 1} {m : ℕ} {r : Fin m → ℝ} {C : Fin m → Divisor X}
    (h : ∀ Γ : Mori.PrimeDivisor X, (Γ.ordForm ω : ℝ) + B.coeff Γ = ∑ i, r i * (C i).coeff Γ) :
    Divisor.toRDivisor (divisorOfForm ω) + B = ∑ j, r j • Divisor.toRDivisor (C j) := by
  ext Γ
  change (Divisor.toRDivisor (divisorOfForm ω) + B).coeff Γ =
    (∑ j, r j • Divisor.toRDivisor (C j)).coeff Γ
  rw [Flips.coeff_sum_smul_toRDivisor, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor,
    coeff_divisorOfForm]
  exact h Γ

/-- A datum computing the discrepancy `a_ω(E, B)`, with `div(ω)` a canonical divisor, computes
the log discrepancy `1 + a_ω(E, B)`. -/
private theorem isLogDiscrepancy_one_add_of_isDiscrepancyWith {n : ℕ} {B : RDivisor X}
    {ω : RationalPluriForms sX n 1} {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X}
    {E : ProperDivisorOver k sX} {a : ℝ} (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    (h : IsDiscrepancyWith sX n B ω r L E a) :
    MMP.Intersection.IsLogDiscrepancy sX n B E.toDivisorOver (1 + a) := by
  obtain ⟨hX, -, hω0, hLc, hsum, L', hpb, rfl⟩ := h
  refine ⟨hX, E.isProper, ω, hω0, ⟨divisorOfForm ω, hK, fun Γ => rfl⟩, m, r, L, L', hLc,
    fun Γ => ?_, hpb, by ring⟩
  simpa only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, coeff_divisorOfForm,
    Flips.coeff_sum_smul_toRDivisor] using congrArg (fun D : RDivisor X => D.coeff Γ) hsum

/-- Every presentation of `div(ω) + B` by Cartier divisors computes a discrepancy on every
proper model. -/
private theorem exists_isDiscrepancyWith (hX : IsNormalVariety k sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) {B : RDivisor X} {ω : RationalPluriForms sX n 1}
    (hω0 : ω ≠ 0) {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} (hLc : ∀ j, (L j).IsCartier)
    (hsum : Divisor.toRDivisor (divisorOfForm ω) + B = ∑ j, r j • Divisor.toRDivisor (L j))
    (E : ProperDivisorOver k sX) : ∃ a, IsDiscrepancyWith sX n B ω r L E a := by
  have := E.isIntegral
  have := E.isLocallyNoetherian
  have := E.isNormal
  have := E.isDominant
  have : CompactSpace E.Y := by
    have := E.isNormalVariety.1
    exact QuasiCompact.compactSpace_of_compactSpace (E.f ≫ sX)
  choose L' hL' using fun j => MMP.Threefold.Bridges.exists_isPullback_of_isDominant E.f (hLc j)
  exact ⟨(E.toDivisorOver.ordPullback ω : ℝ) - ∑ j, r j * ((L' j).coeff E.E : ℝ), hX, hn, hω0,
    hLc, hsum, L', fun j => ⟨_, hL' j⟩, rfl⟩

/-- A discrepancy computed with a fixed canonical divisor `K` gives the log discrepancy of any
proper model of the valuation. -/
private theorem isLogDiscrepancy_of_isDiscrepancy [PerfectField k] {n : ℕ} {K : Divisor X}
    {B : RDivisor X} {E : ProperDivisorOver k sX} {a : ℝ}
    (h : IsDiscrepancy sX n K B E.valuation a) :
    MMP.Intersection.IsLogDiscrepancy sX n B E.toDivisorOver (1 + a) := by
  obtain ⟨hK, -, -, E', ω, m, r, L, hv, rfl, hw⟩ := h
  obtain ⟨hX, hn, hω0, hLc, hsum, -⟩ := id hw
  obtain ⟨c, hc⟩ := exists_isDiscrepancyWith hX hn hω0 hLc hsum E
  obtain rfl := hc.eq hw hv.symm
  exact isLogDiscrepancy_one_add_of_isDiscrepancyWith hK hc

/-- A log discrepancy `a` of a proper model `E` gives the discrepancy `a - 1` of its valuation,
computed with any canonical divisor `K` for which `K + B` is `ℝ`-Cartier. -/
private theorem isDiscrepancy_of_isLogDiscrepancy [PerfectField k] (hX : IsNormalVariety k sX)
    {n n' : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {B : RDivisor X}
    (hKB : IsCartierCombination (Divisor.toRDivisor K + B)) {E : ProperDivisorOver k sX} {a : ℝ}
    (h : MMP.Intersection.IsLogDiscrepancy sX n' B E.toDivisorOver a) :
    IsDiscrepancy sX n K B E.valuation (a - 1) := by
  have hn := hK.topologicalKrullDim_eq
  obtain ⟨-, -, ω', hω0', ⟨K', hK', hK'ω⟩, m', r', C, C', hCc, hsum', hpb, ha⟩ := h
  obtain rfl : n = n' := by
    have h' := hK'.topologicalKrullDim_eq
    rw [hn] at h'
    exact_mod_cast h'
  have hw' : IsDiscrepancyWith sX n B ω' r' C E (a - 1) :=
    ⟨hX, hn, hω0', hCc, toRDivisor_add_eq_sum_of_coeff hsum', C', hpb, by linarith⟩
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain rfl : divisorOfForm ω = K := DivisorWithCoeffs.ext' hω
  obtain ⟨m, r, L, hLc, hsum⟩ := hKB
  have hsum₁ : Divisor.toRDivisor (divisorOfForm ω) + B = ∑ j, r j • Divisor.toRDivisor (L j) := by
    simpa only [toRDivisor_eq_mapCoeffs] using hsum
  obtain ⟨c, hc⟩ := exists_isDiscrepancyWith hX hn hω0 hLc hsum₁ E
  rw [← hc.eq hw' rfl]
  exact ⟨hK, ⟨m, r, L, hLc, hsum⟩, hasNonemptyCenter_valuation E, E, ω, m, r, L, rfl, rfl, hc⟩

end Dictionary

section LogResolution

open CategoryTheory TopologicalSpace MMP.Mori MMP.Resolution
open AlgebraicGeometry hiding PrimeDivisor

/-! ### Snc closed subsets are snc divisors -/

/-- A member of an snc family with irreducible support is a prime divisor. -/
private theorem exists_primeDivisor_of_isSNCFamily {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {ι : Type*} {F : ι → X.IdealSheafData} (hF : IsSNCFamily s F)
    (i : ι) (hirr : IsIrreducible ((F i).support : Set X)) :
    ∃ P : MMP.Mori.PrimeDivisor X, P.idealSheaf = F i := by
  have hint := isIntegral_subscheme_of_isIrreducible s (F i) (hF.1 i).2.2 hirr
  refine ⟨⟨F i, hint, ?_⟩, rfl⟩
  have hcl := closure_subschemeι_genericPoint (F i)
  refine (hF.1 i).2.1 _ ⟨show closure _ ⊆ _ from hcl.le, fun V hV _ => ?_⟩
  exact show (V : Set X) ⊆ closure _ from hcl ▸ hV

/-- A divisor whose components are members of an snc family is snc. -/
private theorem isSNC_of_isSNCFamily {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {ι : Type*} {F : ι → X.IdealSheafData} (hF : IsSNCFamily s F)
    (D : MMP.Mori.DivisorWithCoeffs ℤ X) (hD : ∀ P ∈ D.support, ∃ i, F i = P.idealSheaf) :
    MMP.Mori.DivisorWithCoeffs.IsSNC s D := by
  choose g hg using hD
  refine ⟨fun P hP => ?_, fun x => ?_⟩
  · rw [← hg P hP]
    exact (hF.1 _).2.2
  · obtain ⟨n, w, c, hw, hc, hinj⟩ := hF.2 x
    have hmem : ∀ P : {P : MMP.Mori.PrimeDivisor X // P ∈ D.support ∧ x ∈ P.support},
        x ∈ (F (g P.1 P.2.1)).support := fun P => by rw [hg]; exact P.2.2
    refine ⟨n, w, fun P => c ⟨_, hmem P⟩, hw, fun P Q hPQ => ?_, fun P => ?_⟩
    · have h : g P.1 P.2.1 = g Q.1 Q.2.1 := congrArg Subtype.val (hinj hPQ)
      have : P.1.idealSheaf = Q.1.idealSheaf := by
        rw [← hg P.1 P.2.1, ← hg Q.1 Q.2.1, h]
      exact Subtype.ext (MMP.Mori.PrimeDivisor.ext_idealSheaf this)
    · have := hc ⟨_, hmem P⟩
      rwa [hg] at this

/-- A divisor with simple normal crossings in the sense of `IsSNCClosedSubset` is one in the
sense of `MMP.Mori.IsSNCSubset`. -/
private theorem isSNCSubset_of_isSNCClosedSubset {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [NoetherianSpace X] {S : Closeds X}
    (hS : IsSNCClosedSubset sX (S : Set X)) : IsSNCSubset sX S := by
  classical
  obtain ⟨-, h | ⟨-, hfin, hfam⟩⟩ := hS
  · exact Or.inl (Closeds.ext (by rw [h]; rfl))
  · right
    have : Fintype (componentsOf (S : Set X)) := hfin.fintype
    have hP : ∀ W : componentsOf (S : Set X), ∃ P : MMP.Mori.PrimeDivisor X,
        P.idealSheaf = componentsFamily (S : Set X) W := fun W =>
      exists_primeDivisor_of_isSNCFamily hfam W (by
        rw [coe_support_componentsFamily S.isClosed W]; exact W.2.1.1)
    choose P hP using hP
    have hPs : ∀ W, (P W).support = (W : Set X) := fun W => by
      change ((P W).idealSheaf.support : Set X) = _
      rw [hP, coe_support_componentsFamily S.isClosed W]
    refine ⟨Finset.univ.image P, ?_, ?_⟩
    · apply Set.Subset.antisymm
      · simp only [Finset.mem_image, Finset.mem_univ, true_and, Set.iUnion_exists,
          Set.iUnion_iUnion_eq', Set.iUnion_subset_iff]
        intro W
        rw [hPs]
        exact W.2.1.2
      · intro x hx
        obtain ⟨-, hcov⟩ := Aux.finite_and_cover_componentsOf S.isClosed
        obtain ⟨W, hW, hxW⟩ := Set.mem_sUnion.1 (hcov hx)
        refine Set.mem_biUnion (x := P ⟨W, hW⟩) (Finset.mem_image_of_mem _ (Finset.mem_univ _)) ?_
        rwa [hPs]
    · refine isSNC_of_isSNCFamily hfam _ fun Q hQ => ?_
      obtain ⟨E, hE, hQE⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hQ)
      have hQ' : Q = E := Finset.mem_singleton.1 (Finsupp.support_single_subset hQE)
      obtain ⟨W, -, rfl⟩ := Finset.mem_image.1 hE
      exact ⟨W, by rw [hQ', hP]⟩

/-! ### Existence of log resolutions -/

/-- **Log resolutions exist** in characteristic zero: the snc-preserving log resolution of the
reduced divisor `Supp D` is a log resolution of `(X, D)`. -/
private theorem exists_isLogResolution {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : IsNormalVariety k sX) (D : RDivisor X) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ X), MMP.Mori.IsLogResolution sX D g := by
  obtain ⟨Y, f, hres, hpure, hS, -⟩ :=
    MMP.Resolution.exists_isLogResolution_isIso_restrict_of_isSNCClosedSubset sX hX D.support
  have hYv : AlgebraicGeometry.IsVariety k (f ≫ sX) := hres.isVariety_source
  have : LocallyOfFiniteType (f ≫ sX) := hYv.toLocallyOfFiniteType
  have : QuasiCompact (f ≫ sX) := hYv.toQuasiCompact
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  have : AlgebraicGeometry.IsNoetherian Y := {}
  have hsupp_eq : (D.supp : Set X) = D.support.sup fun E => (E.idealSheaf.support : Set X) := by
    rw [DivisorWithCoeffs.supp, Closeds.coe_finset_sup]
    rfl
  rw [← hsupp_eq] at hS
  refine ⟨Y, f, ⟨⟨hres.isProjective.isProper, hres.isBirationalMorphism, hres.isSmoothScheme⟩,
    hpure, isSNCSubset_of_isSNCClosedSubset _ ?_⟩⟩
  simpa using hS

end LogResolution

section Configuration

open TopologicalSpace MMP.Resolution MMP.Fourfold.SNCWeight
open AlgebraicGeometry hiding PrimeDivisor

/-- A prime divisor lies in a closed set exactly when its generic point does. -/
private theorem support_subset_iff {Y : Scheme.{u}} (P : Mori.PrimeDivisor Y) {T : Set Y}
    (hT : IsClosed T) : (P.support : Set Y) ⊆ T ↔ P.genericPoint ∈ T := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact ⟨fun h => h (subset_closure rfl),
    fun h => closure_minimal (Set.singleton_subset_iff.mpr h) hT⟩

/-- A prime divisor lies in a finite union of prime divisors only if it is one of them. -/
private theorem mem_of_support_subset_iUnion {Y : Scheme.{u}} {s : Finset (Mori.PrimeDivisor Y)}
    {P : Mori.PrimeDivisor Y} (h : (P.support : Set Y) ⊆ ⋃ E ∈ s, (E.support : Set Y)) :
    P ∈ s := by
  obtain ⟨E, hE, hPE⟩ := PrimeDivisorUnion.exists_subset_of_isIrreducible
    (fun E _ => PrimeDivisorUnion.isClosed_support E)
    (PrimeDivisorUnion.isIrreducible_support P) h
  rwa [PrimeDivisorUnion.eq_of_support_subset hPE]

/-- The support of `∑_{E ∈ s} E` is `s`. -/
private theorem support_sum_single {Y : Scheme.{u}} (s : Finset (Mori.PrimeDivisor Y)) :
    (∑ E ∈ s, Finsupp.single E (1 : ℤ)).support = s := by
  classical
  ext P
  simp [Finsupp.mem_support_iff, Finsupp.finset_sum_apply, Finsupp.single_apply]

/-- The support of the reduced divisor of `s` is `s`. -/
private theorem support_reducedDivisorOf {Y : Scheme.{u}} (s : Finset (Mori.PrimeDivisor Y)) :
    (MMP.Intersection.reducedDivisorOf s).support = s := by
  classical
  ext P
  rw [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply,
    MMP.Intersection.coeff_reducedDivisorOf]
  split_ifs with h <;> simp [h]

/-- The coefficients of the reduced divisor of `s` are `0` or `1`. -/
private theorem coeff_reducedDivisorOf_eq_zero_or_eq_one {Y : Scheme.{u}}
    (s : Finset (Mori.PrimeDivisor Y)) (P : Mori.PrimeDivisor Y) :
    (MMP.Intersection.reducedDivisorOf s).coeff P = 0 ∨
      (MMP.Intersection.reducedDivisorOf s).coeff P = 1 := by
  classical
  rw [MMP.Intersection.coeff_reducedDivisorOf]
  split_ifs <;> simp

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (D : RDivisor X)

/-- The configuration `Ex(f) ∪ f⁻¹(Supp D)` of a morphism `f : Y ⟶ X`. -/
private def cfg {Y : Scheme.{u}} (f : Y ⟶ X) : Closeds Y :=
  Mori.exceptionalSet f ⊔ (DivisorWithCoeffs.supp D).preimage f.continuous

/-- The configuration of a Kollár–Mori log resolution is a finite union of prime divisors whose
reduced sum is snc. -/
private theorem exists_finset_cfg {Y : Scheme.{u}} {f : Y ⟶ X}
    (hlog : Mori.IsLogResolution sX D f) :
    ∃ s : Finset (Mori.PrimeDivisor Y), (⋃ E ∈ s, (E.support : Set Y)) = cfg D f ∧
      (MMP.Intersection.reducedDivisorOf s).IsSNC (f ≫ sX) := by
  classical
  rcases hlog.isSNCSubset with h | ⟨s, hs, hsnc⟩
  · refine ⟨∅, ?_, ?_⟩
    · change _ = ((Mori.exceptionalSet f ⊔ (DivisorWithCoeffs.supp D).preimage f.continuous :
        Closeds Y) : Set Y)
      rw [h]
      simp
    · haveI := hlog.isSmoothScheme.smooth
      rw [DivisorWithCoeffs.isSNC_iff_of_support_eq (D' := (0 : Divisor Y))
        (by rw [support_reducedDivisorOf]; rfl)]
      exact DivisorWithCoeffs.isSNC_zero _
  · exact ⟨s, hs, (DivisorWithCoeffs.isSNC_iff_of_support_eq
      ((support_reducedDivisorOf s).trans (support_sum_single s).symm)).mpr hsnc⟩

/-- If `f(η_E) = η_Q` and `f^♯ : 𝒪_{Y,Q} ⟶ 𝒪_{X,E}` is an isomorphism, then `v_E`, seen on
`k(Y)` through `f`, is `v_Q`. -/
private theorem valuationOver_eq_of_isIso {Y X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : Y ⟶ X) [IsDominant f]
    (E : Mori.PrimeDivisor Y) (Q : Mori.PrimeDivisor X)
    (heq : f E.genericPoint = Q.genericPoint) [IsIso (f.stalkMap E.genericPoint)] :
    E.valuationOver f = Q.divisorialValuation := by
  refine Valuation.ext fun t => ?_
  rw [Mori.PrimeDivisor.valuationOver_apply]
  by_cases ht : t = 0
  · rw [ht, map_zero, map_zero, map_zero]
  rw [Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ((map_ne_zero _).mpr ht),
    Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ht,
    MMP.Positivity.ord_functionFieldMap_of_isIso f E Q heq t]

/-- Outside `Ex(f)`, a prime divisor lies over a prime divisor with the same valuation. -/
private theorem exists_valuationOver_eq {Y X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : Y ⟶ X) [IsDominant f]
    (P : Mori.PrimeDivisor Y) (hP : P.genericPoint ∉ (Mori.exceptionalSet f : Set Y)) :
    ∃ Γ : Mori.PrimeDivisor X, f P.genericPoint = Γ.genericPoint ∧
      P.valuationOver f = Γ.divisorialValuation := by
  have hb : f P.genericPoint ∈ Mori.biregularLocus f := not_not.mp hP
  have hco : Order.coheight (f P.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f hb, P.coheight_genericPoint]
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco,
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm, ?_⟩
  have := MMP.Threefold.Resolution.isIso_stalkMap_of_mem_biregularLocus f hb
  exact valuationOver_eq_of_isIso f P _
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm

/-- The reduced sum of the configuration is an snc divisor in the sense of FA. -/
private theorem isSNCDivisor_reducedDivisorOf {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}
    {s : Finset (Mori.PrimeDivisor Y)} (hsnc : (MMP.Intersection.reducedDivisorOf s).IsSNC sY) :
    MMP.Flips.IsSNCDivisor sY (MMP.Intersection.reducedDivisorOf s) := by
  refine ⟨coeff_reducedDivisorOf_eq_zero_or_eq_one s, fun P hP => hsnc.1 P hP, fun p _ => ?_⟩
  obtain ⟨m, z, j, hz, hj, hI⟩ := hsnc.2 p
  exact ⟨m, z, j, hz, hj, hI⟩

end Configuration

section WeakModelHelpers

open TopologicalSpace

/-- An inverse of a proper birational morphism onto a normal variety is a morphism in codimension
one. -/
private theorem isMorphismInCodimOne_of_isInverse {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (g : Y ⟶ X)
    (hY : MMP.Mori.IsVariety k (g ≫ sX)) [IsProper g] {h : X.RationalMap Y}
    (hinv : MMP.Mori.RationalMap.IsInverse g.toRationalMap h) :
    MMP.Flips.RationalMap.IsMorphismInCodimOne h := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  have : IsSeparated sX := hX.1.toIsSeparated
  have : X.IsSeparated := ⟨by rw [← Limits.terminal.comp_from sX]; infer_instance⟩
  obtain ⟨e, he, hinv⟩ := hinv
  have key : e.iso.hom ≫ e.target.ι = e.source.ι ≫ g := by
    obtain ⟨W, hW, hWl, hWr, hEq⟩ := Scheme.PartialMap.toRationalMap_eq_iff.mp he
    have hWl' : W ≤ e.source := hWl
    have : IsDominant (Y.homOfLE hWl') := AlgebraicGeometry.Opens.isDominant_homOfLE hW _
    refine ext_of_isDominant (Y.homOfLE hWl') ?_
    simp only [Scheme.PartialMap.restrict_hom, Scheme.PartialIso.toPartialMap_hom,
      Scheme.Hom.toPartialMap_hom] at hEq
    refine hEq.trans ?_
    rw [Scheme.topIso_hom, Scheme.homOfLE_ι_assoc]
    exact Scheme.homOfLE_ι_assoc Y (show W ≤ ⊤ from hWr) g
  have hover : MMP.Flips.RationalMap.IsOver (𝟙 X) g h := by
    rw [MMP.Flips.RationalMap.IsOver, ← hinv]
    refine Scheme.PartialMap.toRationalMap_eq_iff.mpr
      ⟨e.target, e.dense_target, le_rfl, le_top, ?_⟩
    change X.homOfLE le_rfl ≫ (e.iso.inv ≫ e.source.ι) ≫ g = X.homOfLE _ ≫ X.topIso.hom ≫ 𝟙 X
    rw [Category.assoc, ← key, Iso.inv_hom_id_assoc]
    simp
  exact MMP.Flips.RationalMap.isMorphismInCodimOne_of_isOver hX (𝟙 X) g _ hover

/-- A partial isomorphism representing the rational map of `f` agrees with `f` on its source. -/
private theorem source_ι_comp_eq_of_toRationalMap_eq {X Y : Scheme.{u}} [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) : e.source.ι ≫ f = e.iso.hom ≫ e.target.ι :=
  ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp he)).symm

/-- A partial map representing the inverse of the rational map of `f` is a right inverse of `f`
on its domain. -/
private theorem apply_hom_eq_of_isInverse {X Y : Scheme.{u}} [IsReduced Y] [IsReduced X]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = e.symm.toRationalMap) {x : X} (hx : x ∈ g'.domain) :
    f (g'.hom ⟨x, hx⟩) = x := by
  have h1 : (g'.compHom f).toRationalMap = (Scheme.PartialMap.id X).toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg', ← Scheme.RationalMap.compHom_toRationalMap,
      Scheme.PartialMap.toRationalMap_eq_iff,
      Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
    change e.iso.inv ≫ e.source.ι ≫ f = e.target.ι ≫ 𝟙 X
    rw [source_ι_comp_eq_of_toRationalMap_eq f e he, Iso.inv_hom_id_assoc, Category.comp_id]
  have h2 := MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq
    (g := g'.compHom f) (g' := Scheme.PartialMap.id X) h1 hx trivial
  change (g'.hom ≫ f) ⟨x, hx⟩ = (X.topIso.hom ≫ 𝟙 X) ⟨x, trivial⟩ at h2
  refine (Scheme.Hom.comp_apply _ _ _).symm.trans (h2.trans ?_)
  rw [Category.comp_id, Scheme.topIso_hom]
  rfl

/-- The transform of a prime divisor `P` under a rational map defined at its generic point is the
closure of the image of that generic point. -/
private theorem coe_transform_eq_closure_singleton {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = φ) (P : Mori.PrimeDivisor X)
    (hP : P.genericPoint ∈ g'.domain) :
    (MMP.Mori.RationalMap.transform φ P.idealSheaf.support : Set Y) =
      closure {g'.hom ⟨P.genericPoint, hP⟩} := by
  have hZ : closure ((P.idealSheaf.support : Set X) ∩ g'.domain) = P.idealSheaf.support := by
    refine le_antisymm ?_ ?_
    · exact closure_minimal Set.inter_subset_left P.idealSheaf.support.isClosed
    · change P.support ⊆ _
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact closure_mono
        (Set.singleton_subset_iff.mpr ⟨Positivity.PrimeDivisor.genericPoint_mem_support' P, hP⟩)
  rw [← MMP.Positivity.closure_image_eq_transform g' hg' _ hZ, TopologicalSpace.Closeds.coe_closure]
  refine le_antisymm (closure_minimal ?_ isClosed_closure) (closure_mono ?_)
  · rintro _ ⟨q, hq, rfl⟩
    have hq' : P.genericPoint ⤳ g'.domain.ι q := by
      have : g'.domain.ι q ∈ P.support := hq
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
      exact specializes_iff_mem_closure.mpr this
    have h1 := (g'.domain.ι.isOpenEmbedding.isInducing.specializes_iff (y := q)
      (x := ⟨P.genericPoint, hP⟩)).mp (by rw [Scheme.Opens.ι_apply]; exact hq')
    exact specializes_iff_mem_closure.mp (h1.map g'.hom.continuous)
  · exact Set.singleton_subset_iff.mpr
      ⟨⟨P.genericPoint, hP⟩, Positivity.PrimeDivisor.genericPoint_mem_support' P, rfl⟩

private theorem genericPoint_eq_of_transformPrimeDivisor_eq_some {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : Mori.PrimeDivisor X}
    {E : Mori.PrimeDivisor Y} (h : Mori.RationalMap.transformPrimeDivisor φ P = some E)
    (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ) (hP : P.genericPoint ∈ g'.domain) :
    E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩ := by
  have h1 := Mori.RationalMap.support_transformPrimeDivisor h
  rw [coe_transform_eq_closure_singleton g' hg' P hP,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h1
  exact (inseparable_iff_closure_eq.2 h1).eq

/-- **Strict transforms along an inverse.** Let `p : W ⟶ X` be a proper birational morphism of
normal varieties and `h` an inverse of `p`. Every prime divisor `P` of `X` has a strict transform
`R` on `W`: `p(η_R) = η_P`, `p` is a local isomorphism at `η_R`, and `h` is defined at `η_P` with
`h(η_P) = η_R`. -/
private theorem exists_strictTransform {k : Type u} [Field k] {X W : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] (hX : IsNormalVariety k sX) (p : W ⟶ X) [IsProper p]
    (hW : IsNormalVariety k (p ≫ sX)) (hp : IsBirationalMorphism p) {h : X.RationalMap W}
    (hinv : MMP.Mori.RationalMap.IsInverse p.toRationalMap h) (P : MMP.Mori.PrimeDivisor X) :
    ∃ R : MMP.Mori.PrimeDivisor W, p R.genericPoint = P.genericPoint ∧
      IsIso (p.stalkMap R.genericPoint) ∧
      ∃ (g' : X.PartialMap W) (hP : P.genericPoint ∈ g'.domain), g'.toRationalMap = h ∧
        g'.hom ⟨P.genericPoint, hP⟩ = R.genericPoint := by
  have : IsDominant p := hp.isDominant
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (p ≫ sX) := hW.1.toIsSeparated
  have : IsSeparated (X ↘ ⊤_ Scheme) := by
    rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have : IsSeparated (W ↘ ⊤_ Scheme) := by
    rw [show (W ↘ ⊤_ Scheme) = (p ≫ sX) ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have hbij := hp.functionFieldMap_bijective
  have hcodim := isMorphismInCodimOne_of_isInverse hX p hW.1 hinv
  obtain ⟨e, he, he'⟩ := hinv
  have hdef : MMP.Mori.RationalMap.DefinedAt h P.genericPoint := by
    by_contra hnd
    have h2 := MMP.Mori.le_closedsCodimension_iff.mp hcodim
      (IrreducibleCloseds.closureSingleton P.genericPoint)
      (closure_minimal (Set.singleton_subset_iff.mpr hnd)
        (MMP.Mori.RationalMap.dom h).compl.isClosed)
    have h3 : codimension (IrreducibleCloseds.closureSingleton P.genericPoint) = 1 := by
      rw [codimension_eq_coheight, show IrreducibleCloseds.closureSingleton P.genericPoint =
        (irreducibleSetEquivPoints (α := X)).symm P.genericPoint from rfl,
        Order.coheight_orderIso, P.coheight_genericPoint]
    rw [h3] at h2
    exact absurd h2 (by decide)
  obtain ⟨g', hP, hg'⟩ := MMP.Mori.RationalMap.definedAt_iff.mp hdef
  obtain ⟨R, hR, hiso⟩ := MMP.Flips.exists_primeDivisor_isIso_stalkMap p hp P
  refine ⟨R, hR, hiso, g', hP, hg', ?_⟩
  have hy := apply_hom_eq_of_isInverse p e he g' (hg'.trans he'.symm) hP
  have := P.isDiscreteValuationRing_localRing
  have : ValuationRing (X.presheaf.stalk (p R.genericPoint)) := by rw [hR]; infer_instance
  have : ValuationRing (X.presheaf.stalk (p (g'.hom ⟨P.genericPoint, hP⟩))) := by
    rw [hy]; infer_instance
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing p hbij (g'.hom ⟨P.genericPoint, hP⟩)
  exact (MMP.Positivity.eq_of_isIso_stalkMap p hbij (hy.trans hR.symm)).symm

/-- **Prime divisors of a birational contraction.** Let `φ = q ∘ p⁻¹ : X ⤏ Z` be resolved by proper
birational morphisms `p : W ⟶ X`, `q : W ⟶ Z` of normal varieties, and assume no prime divisor of
`Z` is `φ⁻¹`-exceptional. Then every prime divisor `Q` of `Z` is `φ_* P` for exactly one prime
divisor `P` of `X`, and `P` and `Q` have a common strict transform `R` on `W`, along which `p` and
`q` are local isomorphisms. -/
private theorem exists_common_strictTransform {k : Type u} [Field k] {X Z W : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] (hX : IsNormalVariety k sX) (hZ : IsNormalVariety k sZ)
    (p : W ⟶ X) (q : W ⟶ Z) [IsProper p] [IsProper q] (hW : IsNormalVariety k (p ≫ sX))
    (hpb : IsBirationalMorphism p) (hqb : IsBirationalMorphism q) {h : X.RationalMap W}
    (hinv : MMP.Mori.RationalMap.IsInverse p.toRationalMap h) {φ : X.RationalMap Z}
    (hcomp : h.compHom q = φ)
    (hnie : ∀ F : MMP.Mori.PrimeDivisor Z, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F)
    (Q : MMP.Mori.PrimeDivisor Z) :
    ∃ (R : MMP.Mori.PrimeDivisor W) (P : MMP.Mori.PrimeDivisor X),
      q R.genericPoint = Q.genericPoint ∧ IsIso (q.stalkMap R.genericPoint) ∧
      p R.genericPoint = P.genericPoint ∧ IsIso (p.stalkMap R.genericPoint) ∧
      MMP.Mori.RationalMap.transformPrimeDivisor φ P = some Q ∧
      ∀ P', MMP.Mori.RationalMap.transformPrimeDivisor φ P' = some Q → P' = P := by
  have : IsDominant q := hqb.isDominant
  have : IsSeparated sZ := hZ.1.toIsSeparated
  have : IsSeparated (Z ↘ ⊤_ Scheme) := by
    rw [show (Z ↘ ⊤_ Scheme) = sZ ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have : IsSeparated q := inferInstance
  have hbij := hqb.functionFieldMap_bijective
  have := Q.isDiscreteValuationRing_localRing
  have hover : ∀ P, MMP.Mori.RationalMap.transformPrimeDivisor φ P = some Q →
      ∃ R : MMP.Mori.PrimeDivisor W, p R.genericPoint = P.genericPoint ∧
        IsIso (p.stalkMap R.genericPoint) ∧ q R.genericPoint = Q.genericPoint ∧
        IsIso (q.stalkMap R.genericPoint) := by
    intro P hPQ
    obtain ⟨R, hR, hiso, g', hP, hg', hgR⟩ := exists_strictTransform hX p hW hpb hinv P
    have hrep : (g'.compHom q).toRationalMap = φ := by
      rw [Scheme.RationalMap.compHom_toRationalMap, hg', hcomp]
    have hQ := genericPoint_eq_of_transformPrimeDivisor_eq_some hPQ (g'.compHom q) hrep hP
    have hqR : q R.genericPoint = Q.genericPoint := by
      rw [hQ, ← hgR]
      rfl
    have : ValuationRing (Z.presheaf.stalk (q R.genericPoint)) := by rw [hqR]; infer_instance
    exact ⟨R, hR, hiso, hqR, MMP.Positivity.isIso_stalkMap_of_valuationRing q hbij _⟩
  obtain ⟨P, hPQ⟩ : ∃ P, MMP.Mori.RationalMap.transformPrimeDivisor φ P = some Q := by
    by_contra hne
    push Not at hne
    exact hnie Q hne
  obtain ⟨R, hR, hisoR, hqR, hisoqR⟩ := hover P hPQ
  refine ⟨R, P, hqR, hisoqR, hR, hisoR, hPQ, fun P' hP' => ?_⟩
  obtain ⟨R', hR', -, hqR', hisoqR'⟩ := hover P' hP'
  have : ValuationRing (Z.presheaf.stalk (q R.genericPoint)) := by rw [hqR]; infer_instance
  have hRR : R.genericPoint = R'.genericPoint :=
    MMP.Positivity.eq_of_isIso_stalkMap q hbij (hqR'.trans hqR.symm)
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hR'.symm.trans (hRR ▸ hR))

private theorem partialMap_fromFunctionField_eq {X Y : Scheme.{u}} [IrreducibleSpace X]
    (g : X.PartialMap Y) (hx : genericPoint X ∈ g.domain) :
    g.fromFunctionField = g.domain.fromSpecStalkOfMem (genericPoint X) hx ≫ g.hom := rfl

/-- For a partial isomorphism `e` representing a dominant morphism `p : W ⟶ X` of integral
schemes, `Spec k(W) ⟶ Spec k(X) ⟶ W` along `e⁻¹` is the canonical map. -/
private theorem specMap_functionFieldMap_fromFunctionField_symm {W X : Scheme.{u}} [IsIntegral X]
    [IsIntegral W] (p : W ⟶ X) [IsDominant p] (e : W.PartialIso X)
    (he : e.toRationalMap = p.toRationalMap) :
    Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ e.symm.toRationalMap.fromFunctionField =
      W.fromSpecStalk (genericPoint W) := by
  have hW : genericPoint W ∈ e.source :=
    (genericPoint_specializes _).mem_open e.source.2 e.dense_source.nonempty.choose_spec
  have hX : genericPoint X ∈ e.target :=
    (genericPoint_specializes _).mem_open e.target.2 e.dense_target.nonempty.choose_spec
  have h1 := congrArg Scheme.RationalMap.fromFunctionField he
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap,
    Scheme.RationalMap.fromFunctionField_toRationalMap,
    partialMap_fromFunctionField_eq _ hW] at h1
  have h1' : e.source.fromSpecStalkOfMem (genericPoint W) hW ≫ e.iso.hom ≫ e.target.ι =
      W.fromSpecStalk (genericPoint W) ≫ p := by
    refine h1.trans ?_
    exact Scheme.PartialMap.fromSpecStalkOfMem_toPartialMap p _
  have c1 : e.source.fromSpecStalkOfMem (genericPoint W) hW ≫ e.iso.hom =
      Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫
        e.target.fromSpecStalkOfMem (genericPoint X) hX := by
    rw [← cancel_mono e.target.ι, Category.assoc, h1', Category.assoc,
      Scheme.Opens.fromSpecStalkOfMem_ι]
    exact (functionFieldMap_fromSpecStalk p).symm
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap,
    partialMap_fromFunctionField_eq _ hX]
  change Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫
    e.target.fromSpecStalkOfMem (genericPoint X) hX ≫ e.iso.inv ≫ e.source.ι = _
  rw [← Category.assoc, ← c1, Category.assoc, Iso.hom_inv_id_assoc,
    Scheme.Opens.fromSpecStalkOfMem_ι]

/-- If `h` is an inverse of a dominant morphism `a : A ⟶ X` of integral schemes and
`φ = b ∘ h` for a morphism `b : A ⟶ Z`, then `Spec k(A) ⟶ Spec k(X) ⟶ Z` along `φ` is
`Spec k(A) ⟶ A ⟶ Z`. -/
private theorem specMap_functionFieldMap_fromFunctionField_of_isInverse {X Z A : Scheme.{u}}
    [IsIntegral X] [IsIntegral A] (a : A ⟶ X) [IsDominant a] (b : A ⟶ Z) {h : X.RationalMap A}
    (hinv : MMP.Mori.RationalMap.IsInverse a.toRationalMap h) {φ : X.RationalMap Z}
    (hcomp : h.compHom b = φ) :
    Spec.map (CommRingCat.ofHom (functionFieldMap a)) ≫ φ.fromFunctionField =
      A.fromSpecStalk (genericPoint A) ≫ b := by
  obtain ⟨e, he1, he2⟩ := hinv
  rw [← hcomp, ← he2, MMP.Flips.RationalMap.fromFunctionField_compHom, ← Category.assoc,
    specMap_functionFieldMap_fromFunctionField_symm a e he1]

/-- **Valuations through a birational map.** Let `m : Spec k(X) ⟶ Z` be induced along `p : W ⟶ X`
and `q : W ⟶ Z` (with `p^*` bijective and `q^*` surjective) and along `a : A ⟶ X` and
`b : A ⟶ Z`. Valuations `μ` of `k(W)` and `μ'` of `k(A)` that agree on `k(Z)` agree on `k(X)`. -/
private theorem comap_eq_of_specMap_comp {X Z W A : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
    [IsIntegral W] [IsIntegral A] (m : Spec X.functionField ⟶ Z) (p : W ⟶ X) (q : W ⟶ Z)
    (a : A ⟶ X) (b : A ⟶ Z) [IsDominant p] [IsDominant q] [IsDominant a] [IsDominant b]
    (hp : Function.Bijective (functionFieldMap p)) (hq : Function.Surjective (functionFieldMap q))
    (hW : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ m =
      W.fromSpecStalk (genericPoint W) ≫ q)
    (hA : Spec.map (CommRingCat.ofHom (functionFieldMap a)) ≫ m =
      A.fromSpecStalk (genericPoint A) ≫ b)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (μ : Valuation W.functionField Γ)
    (μ' : Valuation A.functionField Γ)
    (h : μ.comap (functionFieldMap q) = μ'.comap (functionFieldMap b)) :
    μ.comap (functionFieldMap p) = μ'.comap (functionFieldMap a) := by
  let ep := RingEquiv.ofBijective (functionFieldMap p) hp
  let θ : Z.functionField →+* X.functionField := ep.symm.toRingHom.comp (functionFieldMap q)
  have hθ : ∀ s, functionFieldMap p (θ s) = functionFieldMap q s := fun s =>
    ep.apply_symm_apply _
  have hθs : Function.Surjective θ := ep.symm.surjective.comp hq
  have hθ' : (functionFieldMap p).comp θ = functionFieldMap q := RingHom.ext hθ
  have : IsIso (CommRingCat.ofHom (functionFieldMap p)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hp
  have hm : Spec.map (CommRingCat.ofHom θ) ≫ Z.fromSpecStalk (genericPoint Z) = m := by
    rw [← cancel_epi (Spec.map (CommRingCat.ofHom (functionFieldMap p))), hW, ← Category.assoc,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, hθ']
    exact functionFieldMap_fromSpecStalk q
  have hθA : (functionFieldMap a).comp θ = functionFieldMap b := by
    rw [← hm, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← functionFieldMap_fromSpecStalk b] at hA
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).mp hA))
  refine Valuation.ext fun t => ?_
  obtain ⟨s, rfl⟩ := hθs t
  rw [Valuation.comap_apply, Valuation.comap_apply, hθ, ← RingHom.comp_apply (functionFieldMap a) θ,
    hθA, ← Valuation.comap_apply, h, Valuation.comap_apply]

open MMP.Positivity in
/-- **Rational top forms descend along a birational morphism**: if `f^*` is bijective on function
fields, every rational top form on the source is the pull-back of one on the target. -/
private theorem exists_pullbackRationalPluriForms_eq {k : Type u} [Field k] [PerfectField k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX]
    [IsIntegral Y] (f : Y ⟶ X) [IsDominant f] (hbij : Function.Bijective (functionFieldMap f))
    {n : ℕ} (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = n)
    (ω₁ : RationalPluriForms (f ≫ sX) n 1) :
    ∃ τ : RationalPluriForms sX n 1, pullbackRationalPluriForms sX f τ = ω₁ ∧
      (ω₁ ≠ 0 → τ ≠ 0) := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX f hbij hd
  obtain ⟨g, hg⟩ := hbij.2
    ((ZTensorPower.basis (basisOfSpanSingleton hω.2.1 hω.2.2) 1).repr ω₁ ())
  let τ : RationalPluriForms sX n 1 :=
    g • ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) 1 ()
  have hpull : pullbackRationalPluriForms sX f τ = ω₁ := by
    change pullbackForms (K := X.functionField) (K' := Y.functionField) 1 _ = ω₁
    rw [pullbackForms_eq hω, pullbackFormsAlong]
    simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_eq_same, smul_eq_mul, mul_one]
    change functionFieldMap f g • _ = ω₁
    rw [hg]
    exact basis_unit_repr_smul _ ω₁
  refine ⟨τ, hpull, fun h0 hτ => h0 ?_⟩
  rw [← hpull, hτ]
  change pullbackForms (K := X.functionField) (K' := Y.functionField) 1 0 = 0
  rw [pullbackForms_eq hω, pullbackFormsAlong]
  simp

/-- `MMP.Flips.isDiscrepancy_comap_functionFieldMap_iff`, with the structure morphism of the
source given as any morphism equal to the composite. -/
private theorem isDiscrepancy_comap_iff_of_comp_eq {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX) {n : ℕ}
    {D : RDivisor X} {ω : RationalPluriForms sX n 1} (hω : ω ≠ 0)
    (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    (hKD : MMP.Flips.IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω) + D))
    {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    (f : Y ⟶ X) [IsProper f] {sY : Y ⟶ Spec (.of k)} [LocallyOfFiniteType sY]
    (hfs : f ≫ sX = sY) (hY : IsNormalVariety k sY) (hf : IsBirationalMorphism f)
    {D_Y : RDivisor Y}
    (hDY : haveI : IsDominant f := hf.isDominant
      MMP.Flips.IsRCartierPullback f (Divisor.toRDivisor (divisorOfForm ω) + D)
      (Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sX f ω)) + D_Y))
    (hKY : haveI : IsDominant f := hf.isDominant
      (divisorOfForm (pullbackRationalPluriForms sX f ω)).IsCanonicalDivisor sY n)
    (E : MMP.Flips.ProperDivisorOver k sY) (a : ℝ) :
    haveI : IsDominant f := hf.isDominant
    MMP.Flips.IsDiscrepancy sX n (divisorOfForm ω) D (E.valuation.comap (functionFieldMap f)) a ↔
      MMP.Flips.IsDiscrepancy sY n (divisorOfForm (pullbackRationalPluriForms sX f ω)) D_Y
        E.valuation a := by
  subst hfs
  exact MMP.Flips.isDiscrepancy_comap_functionFieldMap_iff hX hω hK hKD f hY hf hDY hKY E a

/-- `exists_properDivisorOver_comap_eq`, with the structure morphism of the source given as any
morphism equal to the composite. -/
private theorem exists_properDivisorOver_comap_eq_of_comp_eq {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral Y] {f : Y ⟶ X}
    {sY : Y ⟶ Spec (.of k)} (hfs : f ≫ sX = sY) (hY : IsNormalVariety k sY)
    (hf : IsBirationalMorphism f) [IsProper f] (D : MMP.Flips.ProperDivisorOver k sX) :
    haveI : IsDominant f := hf.isDominant
    ∃ E : MMP.Flips.ProperDivisorOver k sY,
      E.valuation.comap (functionFieldMap f) = D.valuation := by
  subst hfs
  exact exists_properDivisorOver_comap_eq hY hf D

/-- Exceptionality of a divisor over a normal variety depends only on its valuation. -/
private theorem isExceptional_of_valuation_eq {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) {D D' : DivisorOver k sX} (hv : D.valuation = D'.valuation)
    (hD : D.IsExceptional) : D'.IsExceptional := by
  rw [divisorOver_isExceptional_iff_two_le_coheight hX] at hD ⊢
  rw [← MMP.Positivity.DivisorOver.codimension_center] at hD ⊢
  rwa [← MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hX.1 hv]

/-- On a smooth normal variety, the divisor of a nonzero rational top form is canonical. -/
theorem isCanonicalDivisor_divisorOfForm_of_isSmoothScheme {k : Type u} [Field k]
    [PerfectField k] {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] {sY : Y ⟶ Spec (.of k)} [LocallyOfFiniteType sY]
    (hY : IsNormalVariety k sY) (hsm : IsSmoothScheme sY) {n : ℕ}
    (hn : topologicalKrullDim Y = n) {ω : RationalPluriForms sY n 1} (hω : ω ≠ 0) :
    (divisorOfForm ω).IsCanonicalDivisor sY n := by
  haveI := hY.1
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme sY hsm hn
  exact hK₀.of_linearlyEquivalent <| by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hY hK₀ hω

/-- The source of an `ℝ`-Cartier pull-back is a combination of Cartier divisors. -/
theorem isCartierCombination_of_isRCartierPullback {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X} {N : RDivisor X} {G : RDivisor Y}
    (h : MMP.Flips.IsRCartierPullback f N G) : MMP.Flips.IsCartierCombination N := by
  obtain ⟨m, r, L, -, hL, rfl, -, -⟩ := h
  exact ⟨m, r, L, hL, by simp only [MMP.Flips.toRDivisor_eq_mapCoeffs]⟩

end WeakModelHelpers

section Hard

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}}
  {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- The reduced divisor `∑_{P ∈ T} P` of a finite set of prime divisors, as an `ℝ`-divisor. -/
private noncomputable abbrev reducedRDivisor (T : Finset (MMP.Mori.PrimeDivisor X)) : RDivisor X :=
  ∑ P ∈ T, Finsupp.single P (1 : ℝ)

private theorem coeff_reducedRDivisor (T : Finset (MMP.Mori.PrimeDivisor X))
    (P : MMP.Mori.PrimeDivisor X) [Decidable (P ∈ T)] :
    (reducedRDivisor T).coeff P = if P ∈ T then 1 else 0 := by
  classical
  change (∑ Q ∈ T, Finsupp.single Q (1 : ℝ)) P = _
  rw [Finsupp.finset_sum_apply]
  simp only [Finsupp.single_apply, Finset.sum_ite_eq', ite_eq_left_iff]
  split_ifs <;> simp_all

private theorem reducedRDivisor_nonneg (T : Finset (MMP.Mori.PrimeDivisor X)) :
    0 ≤ reducedRDivisor T := fun P => by
  classical
  change (0 : ℝ) ≤ (reducedRDivisor T) P
  rw [← DivisorWithCoeffs.coeff_apply, coeff_reducedRDivisor]
  split_ifs <;> norm_num

private theorem coeff_add_smul_reducedRDivisor (B : RDivisor X) (η : ℝ)
    (T : Finset (MMP.Mori.PrimeDivisor X)) (P : MMP.Mori.PrimeDivisor X) [Decidable (P ∈ T)] :
    (B + η • reducedRDivisor T).coeff P = B.coeff P + if P ∈ T then η else 0 := by
  rw [DivisorWithCoeffs.coeff_add]
  change _ + (η • reducedRDivisor T) P = _
  rw [Finsupp.smul_apply, ← DivisorWithCoeffs.coeff_apply, coeff_reducedRDivisor]
  split_ifs <;> simp

private theorem coeff_add_smul_reducedRDivisor_eq_zero [DecidableEq (MMP.Mori.PrimeDivisor X)]
    (B : RDivisor X) (η : ℝ) (T : Finset (MMP.Mori.PrimeDivisor X)) {Γ : MMP.Mori.PrimeDivisor X}
    (h : (reducedRDivisor (T ∪ B.support)).coeff Γ = 0) :
    (B + η • reducedRDivisor T).coeff Γ = 0 := by
  classical
  rw [coeff_reducedRDivisor] at h
  have hΓT : Γ ∉ T ∪ B.support := fun hΓ => by simp [hΓ] at h
  rw [Finset.mem_union, not_or] at hΓT
  rw [coeff_add_smul_reducedRDivisor, if_neg hΓT.1, add_zero, DivisorWithCoeffs.coeff_apply]
  exact Finsupp.notMem_support_iff.mp hΓT.2

/-- For finitely many positive bounds `aᵢ`, eventually `η cᵢ < aᵢ` for every `i` as
`η → 0⁺`. -/
theorem eventually_forall_mul_lt {ι : Type*} (s : Finset ι) (c : ι → ℝ) {a : ι → ℝ}
    (ha : ∀ i ∈ s, 0 < a i) : ∀ᶠ η in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ i ∈ s, η * c i < a i := by
  refine (Filter.eventually_all_finset s).2 fun i hi => ?_
  have h0 : Tendsto (fun η : ℝ => η * c i) (nhds 0) (nhds (0 * c i)) := tendsto_id.mul_const _
  rw [zero_mul] at h0
  exact (h0.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds (ha i hi))

/-- A nonpositive sum `l + ∑ nᵢ cᵢ` with natural `l, nᵢ` and positive `cᵢ` forces
`l = 0` and every `nᵢ = 0`. -/
theorem eq_zero_of_add_sum_mul_nonpos {ι : Type*} {s : Finset ι} {l : ℕ} {nn : ι → ℕ}
    {c : ι → ℝ} (hc : ∀ i ∈ s, 0 < c i) (h : (l : ℝ) + ∑ i ∈ s, nn i * c i ≤ 0) :
    l = 0 ∧ ∀ i ∈ s, nn i = 0 := by
  have hnn : ∀ i ∈ s, 0 ≤ (nn i : ℝ) * c i := fun i hi =>
    mul_nonneg (Nat.cast_nonneg _) (hc i hi).le
  have hsum := Finset.sum_nonneg hnn
  have hl : (l : ℝ) = 0 := by linarith [Nat.cast_nonneg (α := ℝ) l]
  have hs0 : ∑ i ∈ s, (nn i : ℝ) * c i = 0 := by linarith
  refine ⟨by exact_mod_cast hl, fun i hi => ?_⟩
  rcases mul_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg hnn).mp hs0 i hi) with h | h
  · exact_mod_cast h
  · exact absurd h (hc i hi).ne'

/-- **Klt is open along a fixed support.** If `(X, B)` is a real klt pair on a `ℚ`-factorial
variety and `T` is a finite set of prime divisors, `(X, B + η ∑_{P ∈ T} P)` is klt for some
`η > 0`. -/
private theorem exists_isRealKltPair_add (hQ : IsQFactorial sX) {B : RDivisor X}
    (hB : IsRealKltPair sX B) (T : Finset (MMP.Mori.PrimeDivisor X)) :
    ∃ η : ℝ, 0 < η ∧ IsRealKltPair sX (B + η • reducedRDivisor T) := by
  classical
  obtain ⟨hX, hB1, ⟨n, K, hK, hKB⟩, hBklt⟩ := hB
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : CompactSpace X := hX.1.toQuasiCompact.compactSpace_of_compactSpace
  have hn : topologicalKrullDim X = n := hK.topologicalKrullDim_eq
  set D : RDivisor X := reducedRDivisor (T ∪ B.support)
  obtain ⟨Y, f, hlog⟩ := exists_isLogResolution sX hX D
  obtain ⟨hYnv, hYdim, -⟩ := hlog.toIsSmoothResolution.isNormalVariety hX
  have hfb := hlog.isBirationalMorphism
  haveI : IsProper f := hlog.isProper
  haveI : IsIntegral Y := hYnv.1.toIsIntegral
  haveI := hYnv.2
  haveI : LocallyOfFiniteType (f ≫ sX) := hYnv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  haveI : QuasiCompact (f ≫ sX) := hYnv.1.toQuasiCompact
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  haveI : IsDominant f := hfb.isDominant
  obtain ⟨s, hs, hsnc⟩ := exists_finset_cfg sX D hlog
  let toX : MMP.Mori.PrimeDivisor Y → DivisorOver k sX := fun R => ⟨Y, f, hYnv, hfb, R⟩
  choose aR haR using fun R =>
    exists_isLogDiscrepancy hX hK hKB (toX R) (inferInstance : IsProper f)
  have haR0 : ∀ R, 0 < aR R := fun R => hBklt _ _ _ (haR R)
  have hFc := isRCartier_of_isQFactorial hQ (reducedRDivisor T)
  obtain ⟨⟨GF, hGF⟩, -⟩ :=
    MMP.Fourfold.isEffective_of_isRCartierPullback f hFc (reducedRDivisor_nonneg T)
  have hev : ∀ᶠ η in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (∀ R ∈ s, η * GF.coeff R < aR R) ∧ ∀ P ∈ T, η < 1 - B.coeff P := by
    refine (eventually_forall_mul_lt s _ fun R _ => haR0 R).and
      ((Filter.eventually_all_finset T).2 fun P _ => ?_)
    exact eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds (by linarith [hB1 P]))
  obtain ⟨η, ⟨hηR, hηT⟩, hη⟩ := (hev.and self_mem_nhdsWithin).exists
  refine ⟨η, hη, hX, fun P => ?_, ⟨n, K, hK, isRCartier_of_isQFactorial hQ _⟩, ?_⟩
  · rw [coeff_add_smul_reducedRDivisor]
    split_ifs with hP
    · linarith [hηT P hP]
    · simpa using hB1 P
  set B' := B + η • reducedRDivisor T
  have haR' : ∀ R, MMP.Intersection.IsLogDiscrepancy sX n B' (toX R)
      (aR R - (η • GF).coeff R) := fun R =>
    isLogDiscrepancy_add (haR R) (MMP.Fourfold.isRCartierPullback_smul η hGF)
  intro n' E a hEa
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain rfl : divisorOfForm ω = K := DivisorWithCoeffs.ext' hω
  obtain ⟨m, r, L, hLc, hcoeff⟩ :=
    isRCartier_of_isQFactorial hQ (Divisor.toRDivisor (divisorOfForm ω) + B')
  have hsum : Divisor.toRDivisor (divisorOfForm ω) + B' = ∑ j, r j • Divisor.toRDivisor (L j) := by
    ext Γ
    rw [hcoeff Γ, MMP.Fourfold.coeff_sum_smul_toRDivisor]
  have hKD' : MMP.Flips.IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω) + B') :=
    ⟨m, r, L, hLc, by simpa only [MMP.Flips.toRDivisor_eq_mapCoeffs] using hsum⟩
  choose L' hL' using fun j => MMP.Threefold.Bridges.exists_isPullback_of_isDominant f (hLc j)
  set ωY := pullbackRationalPluriForms sX f ω with hωY
  set DY : RDivisor Y := ∑ j, r j • Divisor.toRDivisor (L' j) -
    Divisor.toRDivisor (divisorOfForm ωY) with hDY
  have hDYsum : Divisor.toRDivisor (divisorOfForm ωY) + DY =
      ∑ j, r j • Divisor.toRDivisor (L' j) := by
    rw [hDY]
    abel
  have hpb : MMP.Flips.IsRCartierPullback f (Divisor.toRDivisor (divisorOfForm ω) + B')
      (Divisor.toRDivisor (divisorOfForm ωY) + DY) :=
    ⟨m, r, L, L', hLc, hsum, fun j => ⟨_, hL' j⟩, hDYsum⟩
  have hωY0 : ωY ≠ 0 :=
    MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' f
      hfb.functionFieldMap_bijective
      (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn) hω0
  have hnY : topologicalKrullDim Y = n := hYdim.trans hn
  haveI : MMP.Mori.IsVariety k (f ≫ sX) := hYnv.1
  have hKY : (divisorOfForm ωY).IsCanonicalDivisor (f ≫ sX) n :=
    isCanonicalDivisor_divisorOfForm_of_isSmoothScheme hYnv hlog.isSmoothScheme hnY hωY0
  have hKDY : MMP.Flips.IsCartierCombination (Divisor.toRDivisor (divisorOfForm ωY) + DY) :=
    ⟨m, r, L', fun j => (hL' j).isCartier (hLc j), by
      simpa only [MMP.Flips.toRDivisor_eq_mapCoeffs] using hDYsum⟩
  have hcrep := MMP.Flips.isDiscrepancy_comap_functionFieldMap_iff hX hω0 hK hKD' f hYnv hfb hpb
    hKY
  have hprime : ∀ R : MMP.Mori.PrimeDivisor Y,
      MMP.Flips.IsDiscrepancy sX n (divisorOfForm ω) B' (R.valuationOver f) (-DY.coeff R) := by
    intro R
    let ER : MMP.Flips.ProperDivisorOver k (f ≫ sX) :=
      ⟨DivisorOver.ofPrimeDivisor k hYnv R, (inferInstance : IsProper (𝟙 Y))⟩
    have hER : ER.valuation = R.divisorialValuation := valuation_ofPrimeDivisor hYnv R
    have h1 := MMP.Flips.isDiscrepancy_divisorialValuation hYnv ωY hωY0 hKY hKDY R
    rw [← hER] at h1
    have h2 := (hcrep ER _).mpr h1
    rwa [hER] at h2
  have hcoef : ∀ R, 1 - DY.coeff R = aR R - (η • GF).coeff R := by
    intro R
    have h1 := isLogDiscrepancy_of_isDiscrepancy
      (E := MMP.Flips.ProperDivisorOver.mk (toX R) inferInstance) (hprime R)
    linarith [MMP.Threefold.Bridges.IsLogDiscrepancy.unique h1 (haR' R)]
  have hBS : ∀ R : MMP.Mori.PrimeDivisor Y, DY.coeff R ≠ 0 → R ∈ s := by
    intro R hR
    by_contra hRs
    apply hR
    have hRc : ¬ (R.support : Set Y) ⊆ cfg D f := fun h =>
      hRs (mem_of_support_subset_iUnion (hs ▸ h))
    rw [support_subset_iff R (cfg D f).isClosed] at hRc
    simp only [cfg, TopologicalSpace.Closeds.coe_sup, Set.mem_union,
      TopologicalSpace.Closeds.coe_preimage, Set.mem_preimage, not_or] at hRc
    obtain ⟨hRex, hRD⟩ := hRc
    obtain ⟨Γ, hΓ, hval⟩ := exists_valuationOver_eq f R hRex
    have h1 := hprime R
    rw [hval] at h1
    have h2 := MMP.Flips.IsDiscrepancy.eq_neg_coeff h1
    have hΓ0 : D.coeff Γ = 0 := by
      by_contra h0
      exact hRD (hΓ ▸ DivisorWithCoeffs.mem_supp_iff.mpr
        ⟨Γ, h0, MMP.Positivity.PrimeDivisor.genericPoint_mem_support' Γ⟩)
    have hΓ' : B'.coeff Γ = 0 := coeff_add_smul_reducedRDivisor_eq_zero B η T hΓ0
    linarith
  have hpos : ∀ R, 0 < 1 - DY.coeff R := by
    intro R
    by_cases hR : R ∈ s
    · rw [hcoef R]
      change 0 < aR R - (η • GF) R
      rw [Finsupp.smul_apply, smul_eq_mul, ← DivisorWithCoeffs.coeff_apply]
      linarith [hηR R hR]
    · rw [show DY.coeff R = 0 from not_ne_iff.mp fun h => hR (hBS R h)]
      norm_num
  let E₀ : MMP.Flips.ProperDivisorOver k sX := ⟨E, hEa.2.1⟩
  have hdX : MMP.Flips.IsDiscrepancy sX n (divisorOfForm ω) B' E₀.valuation (a - 1) :=
    isDiscrepancy_of_isLogDiscrepancy hX hK hKD' (E := E₀) hEa
  obtain ⟨ν, hν⟩ := exists_properDivisorOver_comap_eq hYnv hfb E₀
  have hdY := (hcrep ν (a - 1)).mp (by rwa [hν])
  by_cases hex : ν.toDivisorOver.IsExceptional
  · have hcod : 2 ≤ codimension ν.center := by
      rw [ν.center_eq_toDivisorOver_center, MMP.Positivity.DivisorOver.codimension_center]
      exact (divisorOver_isExceptional_iff_two_le_coheight hYnv _).mp hex
    have hBS' : ∀ R, DY.coeff R ≠ 0 → R ∈ (MMP.Intersection.reducedDivisorOf s).support :=
      fun R hR => by
        rw [support_reducedDivisorOf]
        exact hBS R hR
    obtain ⟨l, nn, hbeq, -, -, -, hcod2⟩ :=
      MMP.Flips.exists_logDiscrepancy_eq_add_sum_of_isSNCDivisor (f ≫ sX) hYnv.1
        hlog.isSmoothScheme (isSNCDivisor_reducedDivisorOf hsnc) hBS' ν (b := 1 + (a - 1))
        ⟨a - 1, hdY, rfl⟩
    rw [support_reducedDivisorOf] at hbeq hcod2
    by_contra! hneg
    obtain ⟨hl, hnR⟩ := eq_zero_of_add_sum_mul_nonpos (fun R _ => hpos R) (by linarith)
    rw [hl, Finset.sum_eq_zero hnR] at hcod2
    have := hcod.trans hcod2
    norm_num at this
  · obtain ⟨P, hP⟩ := exists_primeDivisor_divisorialValuation_eq hYnv ν.toDivisorOver hex
    rw [show ν.valuation = P.divisorialValuation from hP] at hdY
    linarith [hpos P, MMP.Flips.IsDiscrepancy.eq_neg_coeff hdY]

/-- **Log discrepancies increase on a nef weak model.** -/
private theorem weakModel_isLogDiscrepancy {S : Scheme.{u}} {Bi : RDivisor X}
    (sS : S ⟶ Spec (.of k)) (πX : X ⟶ S) (K : Divisor X)
    (Z : Scheme.{u}) [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    (sZ : Z ⟶ Spec (.of k)) [QuasiCompact sZ] (πZ : Z ⟶ S) (φ : X.RationalMap Z)
    (hφ : IsNefWeakModel sX sZ sS πX πZ K Bi φ)
    (E : DivisorOver k sX) (g : E.Y ⟶ Z) (hg : IsNormalVariety k (g ≫ sZ))
    (hgb : IsBirationalMorphism g) (f' : X.RationalMap E.Y)
    (hinv' : MMP.Mori.RationalMap.IsInverse E.f.toRationalMap f') (hcomp' : f'.compHom g = φ)
    (hE : E.IsExceptional) (n : ℕ) (a : ℝ)
    (ha : MMP.Intersection.IsLogDiscrepancy sZ n
      (MMP.Mori.RationalMap.transformDivisor φ Bi) ⟨E.Y, g, hg, hgb, E.E⟩ a) (ha1 : a ≤ 1) :
    ∃ (m : ℕ) (E' : DivisorOver k sX) (a' : ℝ), E'.IsExceptional ∧
      E'.valuation = E.valuation ∧
      MMP.Intersection.IsLogDiscrepancy sX m Bi E' a' ∧ a' ≤ 1 := by
  classical
  have hX := hφ.isNormalVariety_source
  have hZ := hφ.isNormalVariety_target
  obtain ⟨m, hK⟩ := hφ.isCanonicalDivisor
  obtain ⟨W, _, _, _, sW, p, q, h, hWv, hWsm, hpW, hqW, hpp, hqp, hpb, hqb, hinv, hcomp, GY, GZ,
    hGY, hGZ, hGeff, -⟩ := hφ.exists_resolution
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : CompactSpace X := hX.1.toQuasiCompact.compactSpace_of_compactSpace
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : CompactSpace Z := hZ.1.toQuasiCompact.compactSpace_of_compactSpace
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hpp
  haveI : IsProper q := isProper_of_isProjectiveMorphism q hqp
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  haveI : MMP.Mori.IsVariety k sW := hWv
  haveI : LocallyOfFiniteType sW := hWv.toLocallyOfFiniteType
  haveI : QuasiCompact sW := hWv.toQuasiCompact
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  have hWn : IsNormalVariety k sW := ⟨hWv, inferInstance⟩
  have hWnp : IsNormalVariety k (p ≫ sX) := by rwa [hpW]
  have hWnq : IsNormalVariety k (q ≫ sZ) := by rwa [hqW]
  haveI : LocallyOfFiniteType (q ≫ sZ) := hWnq.1.toLocallyOfFiniteType
  have hnX : topologicalKrullDim X = m := hK.topologicalKrullDim_eq
  have hnW : topologicalKrullDim W = m := by
    have := hX.1
    have := hWnp.1
    rw [← hnX]
    exact (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (p ≫ sX) hpb).symm
  have hnZ : topologicalKrullDim Z = m := by
    have := hZ.1
    have := hWnq.1
    rw [← hnW]
    exact MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ (q ≫ sZ) hqb
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain rfl : divisorOfForm ω = K := DivisorWithCoeffs.ext' hω
  set KW := divisorOfForm (pullbackRationalPluriForms sX p ω) with hKWdef
  have hdX := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hnX
  have hωW0 : pullbackRationalPluriForms sX p ω ≠ 0 :=
    MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' p
      hpb.functionFieldMap_bijective hdX hω0
  have hKWp : KW.IsCanonicalDivisor (p ≫ sX) m :=
    isCanonicalDivisor_divisorOfForm_of_isSmoothScheme hWnp (by rwa [hpW]) hnW hωW0
  have hKW : KW.IsCanonicalDivisor sW m := by rwa [← hpW]
  have hKWq : KW.IsCanonicalDivisor (q ≫ sZ) m := by rwa [hqW]
  obtain ⟨ω₁, hω₁0, hω₁⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hWnq hKWq
  have hdZ := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sZ) hnZ
  obtain ⟨τ, hτ, hτ0⟩ :=
    exists_pullbackRationalPluriForms_eq q hqb.functionFieldMap_bijective hdZ ω₁
  have hτ0 := hτ0 hω₁0
  have hqτ : divisorOfForm (pullbackRationalPluriForms sZ q τ) = KW := by
    rw [hτ]
    exact DivisorWithCoeffs.ext' hω₁
  have hτK : divisorOfForm τ =
      MMP.Mori.RationalMap.transformDivisor φ (divisorOfForm ω) := by
    refine Finsupp.ext fun Q => ?_
    obtain ⟨R, P, hqR, hqiso, hpR, hpiso, hPQ, huniq⟩ :=
      exists_common_strictTransform hX hZ p q hWnp hpb hqb hinv hcomp
        hφ.not_isInverseExceptional Q
    have e1 : (MMP.Mori.RationalMap.transformDivisor φ (divisorOfForm ω)) Q =
        (divisorOfForm ω) P :=
      MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hPQ huniq _
    rw [e1]
    change Q.ordForm τ = P.ordForm ω
    rw [← MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso q
        hqb.functionFieldMap_bijective hdZ R Q hqR τ, hτ, hω₁,
      ← MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso p
        hpb.functionFieldMap_bijective hdX R P hpR ω]
    rfl
  have hKτ : (divisorOfForm τ).IsCanonicalDivisor sZ m := by
    obtain ⟨-, -, ω', -, ⟨K', hK', -⟩, -⟩ := ha
    obtain rfl : n = m := by
      have := hK'.topologicalKrullDim_eq
      rw [hnZ] at this
      exact_mod_cast this.symm
    exact hK'.of_linearlyEquivalent <| by
      simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hZ hK' hτ0
  have hKDτ : MMP.Flips.IsCartierCombination (Divisor.toRDivisor (divisorOfForm τ) +
      MMP.Mori.RationalMap.transformDivisor φ Bi) := by
    rw [hτK]
    exact isCartierCombination_of_isRCartierPullback hGZ
  set DW : RDivisor W := GY - Divisor.toRDivisor KW with hDW
  set DW' : RDivisor W := GZ - Divisor.toRDivisor KW with hDW'
  have hpbX : MMP.Flips.IsRCartierPullback p (Divisor.toRDivisor (divisorOfForm ω) + Bi)
      (Divisor.toRDivisor KW + DW) := by
    rwa [hDW, add_sub_cancel]
  have hpbZ : MMP.Flips.IsRCartierPullback q (Divisor.toRDivisor (divisorOfForm τ) +
      MMP.Mori.RationalMap.transformDivisor φ Bi)
      (Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sZ q τ)) + DW') := by
    rwa [hqτ, hDW', add_sub_cancel, hτK]
  have hKD : MMP.Flips.IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω) + Bi) :=
    hφ.isCartierCombination
  have hcrepX := isDiscrepancy_comap_iff_of_comp_eq hX hω0 hK hKD p hpW hWn hpb hpbX hKW
  have hcrepZ := isDiscrepancy_comap_iff_of_comp_eq hZ hτ0 hKτ hKDτ q hqW hWn hqb hpbZ
    (by rwa [hqτ])
  have hKDW : MMP.Flips.IsCartierCombination (Divisor.toRDivisor KW + DW) := by
    obtain ⟨m', r', L, L', hLc, -, hpbL, heq⟩ := hpbX
    exact ⟨m', r', L', fun j => (hpbL j).2.isCartier (hLc j), by
      rw [heq]; simp only [MMP.Flips.toRDivisor_eq_mapCoeffs]⟩
  let EZ : MMP.Flips.ProperDivisorOver k sZ := ⟨⟨E.Y, g, hg, hgb, E.E⟩, ha.2.1⟩
  have hdZ' : MMP.Flips.IsDiscrepancy sZ m (divisorOfForm τ)
      (MMP.Mori.RationalMap.transformDivisor φ Bi) EZ.valuation (a - 1) :=
    isDiscrepancy_of_isLogDiscrepancy hZ hKτ hKDτ (E := EZ) ha
  obtain ⟨ν, hν⟩ := exists_properDivisorOver_comap_eq_of_comp_eq hqW hWn hqb EZ
  have hdW' := (hcrepZ ν (a - 1)).mp (by rwa [hν])
  rw [hqτ] at hdW'
  have hlW' := isLogDiscrepancy_of_isDiscrepancy hdW'
  obtain ⟨G, hG, hG0⟩ :=
    exists_isRCartierPullback hlW' (isRCartier_of_isSmoothScheme hWsm (DW - DW'))
  have hlW := isLogDiscrepancy_add hlW' hG
  rw [add_sub_cancel] at hlW
  have hGnn : 0 ≤ G.coeff ν.E := by
    refine hG0 (fun P => ?_) ν.E
    change (0 : ℝ) ≤ (DW - DW') P
    rw [hDW, hDW', sub_sub_sub_cancel_right]
    exact hGeff P
  have hdW := isDiscrepancy_of_isLogDiscrepancy hWn hKW hKDW (E := ν) hlW
  have hdX := (hcrepX ν _).mpr hdW
  have hvX : ν.valuation.comap (functionFieldMap p) = E.valuation := by
    have := E.isIntegral
    have := E.isDominant
    have := hgb.isDominant
    have := E.isNormal
    have := E.isLocallyNoetherian
    exact comap_eq_of_specMap_comp φ.fromFunctionField p q E.f g
      hpb.functionFieldMap_bijective hqb.functionFieldMap_bijective.2
      (specMap_functionFieldMap_fromFunctionField_of_isInverse p q hinv hcomp)
      (specMap_functionFieldMap_fromFunctionField_of_isInverse E.f g hinv' hcomp')
      ν.valuation E.E.divisorialValuation (by rw [hν]; rfl)
  rw [hvX] at hdX
  obtain ⟨-, -, -, E', -, -, -, -, hE'v, -, -⟩ := id hdX
  rw [← hE'v] at hdX
  refine ⟨m, E'.toDivisorOver, _, isExceptional_of_valuation_eq hX hE'v.symm hE, hE'v,
    isLogDiscrepancy_of_isDiscrepancy hdX, ?_⟩
  linarith

/-- **Low valuations are primes on a crepant terminal model.** If `a(E, X, B) ≤ 1` and
`h : Y ⟶ X` is a crepant real terminal model of `(X, B)`, the valuation of `E` is that of a prime
divisor of `Y`. -/
private theorem exists_primeDivisor_valuation_eq_of_isRealTerminalPair {B : RDivisor X} {m : ℕ}
    {E : DivisorOver k sX} {a : ℝ} (ha : MMP.Intersection.IsLogDiscrepancy sX m B E a)
    (ha1 : a ≤ 1) (Y : Scheme.{u}) [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (h : Y ⟶ X) (hY : IsNormalVariety k (h ≫ sX)) (hh : IsBirationalMorphism h)
    (KX : Divisor X) (KY : Divisor Y) (BY : RDivisor Y) (n : ℕ)
    (hproj : IsProjectiveMorphism h) (hKX : KX.IsCanonicalDivisor sX n)
    (hKY : KY.IsCanonicalDivisor (h ≫ sX) n)
    (hpush : MMP.Mori.RationalMap.transformDivisor h.toRationalMap KY = KX)
    (hpb : MMP.Flips.IsRCartierPullback h (MMP.Flips.logCanonicalDivisor KX B)
      (MMP.Flips.logCanonicalDivisor KY BY))
    (hterm : IsRealTerminalPair (h ≫ sX) BY) :
    ∃ P : MMP.Mori.PrimeDivisor Y, (⟨Y, h, hY, hh, P⟩ : DivisorOver k sX).valuation =
      E.valuation := by
  have : IsProper h := isProper_of_isProjectiveMorphism h hproj
  have hX : IsNormalVariety k sX := ha.1
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : CompactSpace X := hX.1.toQuasiCompact.compactSpace_of_compactSpace
  have : IsDominant h := hh.isDominant
  have : LocallyOfFiniteType (h ≫ sX) := hY.1.toLocallyOfFiniteType
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace h
  obtain ⟨ω, hω0, rfl, rfl⟩ :=
    MMP.Positivity.exists_divisorOfForm_eq_of_transformDivisor_eq hX hY hh hKX hKY hpush
  have hKD : MMP.Flips.IsCartierCombination
      (Divisor.toRDivisor (divisorOfForm ω) + B) :=
    isCartierCombination_of_isRCartierPullback hpb
  have hcrep := MMP.Flips.isDiscrepancy_comap_functionFieldMap_iff hX hω0 hKX hKD h hY hh hpb hKY
  let E₀ : MMP.Flips.ProperDivisorOver k sX := ⟨E, ha.2.1⟩
  obtain ⟨EY, hEY⟩ := exists_properDivisorOver_comap_eq hY hh E₀
  have hdX : MMP.Flips.IsDiscrepancy sX n (divisorOfForm ω) B E₀.valuation (a - 1) :=
    isDiscrepancy_of_isLogDiscrepancy hX hKX hKD (E := E₀) ha
  have hdY := (hcrep EY (a - 1)).mp (by rwa [hEY])
  have hlY := isLogDiscrepancy_of_isDiscrepancy hdY
  rw [add_sub_cancel] at hlY
  by_cases hex : EY.toDivisorOver.IsExceptional
  · have := hterm.2 n _ _ hex hlY
    linarith
  · obtain ⟨P, hP⟩ := exists_primeDivisor_divisorialValuation_eq hY EY.toDivisorOver hex
    refine ⟨P, ?_⟩
    change _ = E₀.valuation
    rw [← hEY]
    ext g
    change P.divisorialValuation (functionFieldMap h g) =
      EY.toDivisorOver.valuation (functionFieldMap h g)
    rw [hP]

/-- **Changing the boundary on a `ℚ`-factorial variety.** A divisor over `X` carrying a log
discrepancy for `B` carries one for every boundary `B'`, and it is at most the old one when
`B ≤ B'`. -/
private theorem exists_isLogDiscrepancy_of_isQFactorial (hQ : IsQFactorial sX) {n : ℕ}
    {B : RDivisor X} {E : DivisorOver k sX} {a : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sX n B E a) (B' : RDivisor X) :
    ∃ a', MMP.Intersection.IsLogDiscrepancy sX n B' E a' ∧
      ((∀ P, B.coeff P ≤ B'.coeff P) → a' ≤ a) := by
  obtain ⟨G, hG, hG0⟩ := exists_isRCartierPullback ha (isRCartier_of_isQFactorial hQ (B' - B))
  refine ⟨_, by simpa only [add_sub_cancel] using isLogDiscrepancy_add ha hG, fun hle => ?_⟩
  have : 0 ≤ G.coeff E.E := hG0 (fun P => by
    change (0 : ℝ) ≤ (B' - B) P
    rw [Finsupp.sub_apply, ← DivisorWithCoeffs.coeff_apply, ← DivisorWithCoeffs.coeff_apply,
      sub_nonneg]
    exact hle P) E.E
  linarith

/-- **Log discrepancies are continuous in the coefficients.** If the boundaries `B_i` are
supported on a fixed finite set `T` and converge coefficientwise to `B`, then a log discrepancy
`a(E, X, B)` is the limit of log discrepancies `a(E, X, B_i)`: with the pull-backs `f^*P`
fixed, `a(E, X, B_i) = a(E, X, B) - ∑_{P ∈ T} (b_{i,P} - b_P) coeff_E(f^*P)`. -/
private theorem exists_tendsto_isLogDiscrepancy (hQ : IsQFactorial sX)
    {T : Finset (MMP.Mori.PrimeDivisor X)} {Bs : ℕ → RDivisor X} (hT : ∀ i, (Bs i).support ⊆ T)
    {B : RDivisor X} (hlim : ∀ P, Tendsto (fun i => (Bs i).coeff P) atTop (nhds (B.coeff P)))
    {n : ℕ} {E : DivisorOver k sX} {a : ℝ}
    (haB : MMP.Intersection.IsLogDiscrepancy sX n B E a) :
    ∃ a' : ℕ → ℝ, (∀ i, MMP.Intersection.IsLogDiscrepancy sX n (Bs i) E (a' i)) ∧
      Tendsto a' atTop (nhds a) := by
  classical
  have := E.isLocallyNoetherian
  have := E.isNormal
  have hoff : ∀ i P, P ∉ T → (Bs i).coeff P = 0 := fun i P hP =>
    Finsupp.notMem_support_iff.mp fun h => hP (hT i h)
  choose G hG using fun P : T =>
    exists_isRCartierPullback haB (isRCartier_of_isQFactorial hQ (Finsupp.single P.1 1))
  set c : ℕ → T → ℝ := fun i P => (Bs i).coeff P - B.coeff P with hc
  have hdecomp : ∀ i, Bs i - B =
      ∑ P : T, c i P • Finsupp.single (P : MMP.Mori.PrimeDivisor X) (1 : ℝ) := by
    intro i
    ext Q
    rw [DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply, Finsupp.sub_apply,
      Finsupp.finset_sum_apply]
    simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero]
    by_cases hQ : Q ∈ T
    · rw [Finset.sum_eq_single ⟨Q, hQ⟩ (fun b _ hb => if_neg fun h => hb (Subtype.ext h))
        (by simp)]
      simp [hc, DivisorWithCoeffs.coeff_apply]
    · rw [Finset.sum_eq_zero fun (b : T) _ =>
        if_neg fun (h : (b : MMP.Mori.PrimeDivisor X) = Q) => hQ (h ▸ b.2)]
      have h1 := hoff i Q hQ
      have h2 : B.coeff Q = 0 := tendsto_nhds_unique (hlim Q) (by simp [hoff _ Q hQ])
      rw [DivisorWithCoeffs.coeff_apply] at h1 h2
      rw [h1, h2, sub_zero]
  have hpb : ∀ i, MMP.Flips.IsRCartierPullback E.f (Bs i - B) (∑ P : T, c i P • G P) := by
    intro i
    rw [hdecomp i]
    exact MMP.Fourfold.isRCartierPullback_sum _ _ _ fun P _ =>
      MMP.Fourfold.isRCartierPullback_smul _ (hG P).1
  refine ⟨fun i => a - (∑ P : T, c i P • G P).coeff E.E, fun i => by
    simpa only [add_sub_cancel] using isLogDiscrepancy_add haB (hpb i), ?_⟩
  have hcoeff : ∀ i, (∑ P : T, c i P • G P).coeff E.E = ∑ P : T, c i P * (G P).coeff E.E :=
    fun i => by
      rw [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply]
      rfl
  simp_rw [hcoeff]
  have : Tendsto (fun i => ∑ P : T, c i P * (G P).coeff E.E) atTop (nhds 0) := by
    rw [show (0 : ℝ) = ∑ P : T, 0 * (G P).coeff E.E by simp]
    refine tendsto_finset_sum _ fun P _ => Tendsto.mul_const _ ?_
    simpa [hc] using (hlim P).sub_const (B.coeff P)
  simpa using this.const_sub a

end Hard

/-- Uniform finiteness of low discrepancies near a real klt pair: for a normal `ℚ`-factorial
projective variety `X` and effective real boundaries `B_i → B` supported on a fixed finite set
`T`, with `(X, B)` klt, there is a finite set `𝓕` of exceptional valuations of `k(X)` containing
every exceptional `E` with `a(E, X, B_i) ≤ 1` for all large `i`; a valuation with nonnegative
codiscrepancy on a nef weak model of `(X, B_i)` has `a(E, X, B_i) ≤ 1`; and a valuation with
`a(E, X, B_i) ≤ 1` for infinitely many `i` has `a(E, X, B) ≤ 1` and is a prime divisor on every
crepant real terminal model of `(X, B)`. -/
theorem solution {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X S : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hQ : IsQFactorial sX) (hproj : MMP.Mori.IsProjectiveVariety k sX)
    {B : RDivisor X} (hB : IsRealKltPair sX B) (Bs : ℕ → RDivisor X)
    (hBs : ∀ i P, 0 ≤ (Bs i).coeff P) (T : Finset (MMP.Mori.PrimeDivisor X))
    (hT : ∀ i, (Bs i).support ⊆ T)
    (hlim : ∀ P, Tendsto (fun i => (Bs i).coeff P) atTop (nhds (B.coeff P))) :
    ∃ 𝓕 : Set (Valuation X.functionField ℤᵐ⁰), 𝓕.Finite ∧
      (∀ v ∈ 𝓕, ∃ E : DivisorOver k sX, E.IsExceptional ∧ E.valuation = v) ∧
      (∀ᶠ i in atTop, {v | ∃ (n : ℕ) (E : DivisorOver k sX) (a : ℝ),
          E.IsExceptional ∧ E.valuation = v ∧
            MMP.Intersection.IsLogDiscrepancy sX n (Bs i) E a ∧ a ≤ 1} ⊆ 𝓕) ∧
      (∀ (i : ℕ) (sS : S ⟶ Spec (.of k)) (πX : X ⟶ S) (K : Divisor X)
        (Z : Scheme.{u}) [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
        (sZ : Z ⟶ Spec (.of k)) [QuasiCompact sZ] (πZ : Z ⟶ S) (φ : X.RationalMap Z),
        IsNefWeakModel sX sZ sS πX πZ K (Bs i) φ →
        ∀ (E : DivisorOver k sX) (g : E.Y ⟶ Z) (hg : IsNormalVariety k (g ≫ sZ))
          (hgb : IsBirationalMorphism g) (f' : X.RationalMap E.Y),
          MMP.Mori.RationalMap.IsInverse E.f.toRationalMap f' → f'.compHom g = φ →
          E.IsExceptional →
          ∀ (n : ℕ) (a : ℝ),
            MMP.Intersection.IsLogDiscrepancy sZ n
              (MMP.Mori.RationalMap.transformDivisor φ (Bs i))
              ⟨E.Y, g, hg, hgb, E.E⟩ a → a ≤ 1 →
          ∃ (m : ℕ) (E' : DivisorOver k sX) (a' : ℝ), E'.IsExceptional ∧
            E'.valuation = E.valuation ∧
            MMP.Intersection.IsLogDiscrepancy sX m (Bs i) E' a' ∧ a' ≤ 1) ∧
      ∀ v : Valuation X.functionField ℤᵐ⁰,
        (∃ᶠ i in atTop, ∃ (n : ℕ) (E : DivisorOver k sX) (a : ℝ),
          E.IsExceptional ∧ E.valuation = v ∧
            MMP.Intersection.IsLogDiscrepancy sX n (Bs i) E a ∧ a ≤ 1) →
        (∀ (n : ℕ) (E : DivisorOver k sX) (a : ℝ), E.valuation = v →
          MMP.Intersection.IsLogDiscrepancy sX n B E a → a ≤ 1) ∧
        ∀ (Y : Scheme.{u}) [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (h : Y ⟶ X)
          (hY : IsNormalVariety k (h ≫ sX)) (hh : IsBirationalMorphism h)
          (KX : Divisor X) (KY : Divisor Y) (BY : RDivisor Y) (n : ℕ),
          IsProjectiveMorphism h → KX.IsCanonicalDivisor sX n →
          KY.IsCanonicalDivisor (h ≫ sX) n →
          MMP.Mori.RationalMap.transformDivisor h.toRationalMap KY = KX →
          MMP.Flips.IsRCartierPullback h (MMP.Flips.logCanonicalDivisor KX B)
            (MMP.Flips.logCanonicalDivisor KY BY) →
          IsRealTerminalPair (h ≫ sX) BY →
          ∃ P : MMP.Mori.PrimeDivisor Y, (⟨Y, h, hY, hh, P⟩ : DivisorOver k sX).valuation = v := by
  classical
  have hB0 : ∀ P, 0 ≤ B.coeff P := fun P => ge_of_tendsto' (hlim P) fun i => hBs i P
  obtain ⟨η, hη, hklt⟩ := exists_isRealKltPair_add hQ hB T
  set Bp := B + η • reducedRDivisor T
  have hBp : ∀ P, Bp.coeff P = B.coeff P + if P ∈ T then η else 0 :=
    fun P => coeff_add_smul_reducedRDivisor B η T P
  refine ⟨{v | ∃ (n : ℕ) (E : DivisorOver k sX) (a : ℝ), E.IsExceptional ∧ E.valuation = v ∧
      MMP.Intersection.IsLogDiscrepancy sX n Bp E a ∧ a ≤ 1},
    hklt.finite_setOf_isLogDiscrepancy_le_one, ?_, ?_,
    fun i sS πX K Z _ _ _ sZ _ πZ φ => weakModel_isLogDiscrepancy sS πX K Z sZ πZ φ, ?_⟩
  · rintro v ⟨n, E, a, hE, rfl, -⟩
    exact ⟨E, hE, rfl⟩
  · have hev : ∀ᶠ i in atTop, ∀ P ∈ T, (Bs i).coeff P < Bp.coeff P :=
      (Filter.eventually_all_finset T).2 fun P hP =>
        (hlim P).eventually (gt_mem_nhds (by rw [hBp]; simp [hP, hη]))
    filter_upwards [hev] with i hi
    rintro v ⟨n, E, a, hE, rfl, ha, ha1⟩
    obtain ⟨a', ha', hle⟩ := exists_isLogDiscrepancy_of_isQFactorial hQ ha Bp
    refine ⟨n, E, a', hE, rfl, ha', (hle fun P => ?_).trans ha1⟩
    by_cases hP : P ∈ T
    · exact (hi P hP).le
    · rw [DivisorWithCoeffs.coeff_apply (Bs i),
        Finsupp.notMem_support_iff.mp fun h => hP (hT i h), hBp]
      simp [hP, hB0 P]
  · intro v hv
    have part1 : ∀ (n : ℕ) (E : DivisorOver k sX) (a : ℝ), E.valuation = v →
        MMP.Intersection.IsLogDiscrepancy sX n B E a → a ≤ 1 := by
      intro n E a hEv haB
      obtain ⟨a', ha', htend⟩ := exists_tendsto_isLogDiscrepancy hQ hT hlim haB
      refine isClosed_Iic.mem_of_frequently_of_tendsto (hv.mono fun i hi => ?_) htend
      obtain ⟨n', E', b, -, hE'v, hb, hb1⟩ := hi
      rw [Set.mem_Iic, MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq (ha' i) hb
        (hEv.trans hE'v.symm)]
      exact hb1
    refine ⟨part1, fun Y _ _ _ h hY hh KX KY BY n hproj hKX hKY hpush hpb hterm => ?_⟩
    obtain ⟨i, n', E, a, -, rfl, ha, -⟩ := hv.exists
    obtain ⟨b, hb, -⟩ := exists_isLogDiscrepancy_of_isQFactorial hQ ha B
    exact exists_primeDivisor_valuation_eq_of_isRealTerminalPair hb (part1 _ _ _ rfl hb) Y h hY
      hh KX KY BY n hproj hKX hKY hpush hpb hterm

end MMP.FourfoldProofs.FourfoldUniformLowDiscrepanciesNearKltProof

end

section

/-!
# Uniform finiteness of low discrepancies near a real klt pair

Let `X` be a normal `ℚ`-factorial projective variety over an algebraically closed field of
characteristic zero, and let `B_i → B` be effective real boundaries on `X`, all supported on a
fixed finite set of prime divisors, with `(X, B)` klt. Then there is one finite set `𝓕` of
exceptional divisorial valuations of `k(X)` containing, for all large `i`, every exceptional
valuation `E` with `a(E, X, B_i) ≤ 1`. A valuation exceptional over `X` with nonnegative
codiscrepancy `1 - a(E, X_i, B_{X_i})` on a nef weak model `X_i` of `(X, B_i)` already has
`a(E, X, B_i) ≤ 1`, so `𝓕` contains these for all large `i` as well. A valuation occurring
for infinitely many `i` has `a(E, X, B) ≤ 1`, and is a prime divisor on every crepant real
terminal model of `(X, B)`.

## Main results

* `MMP.Fourfold.IsRealKltPair.exists_finite_eventually_setOf_isLogDiscrepancy_le_one_subset`.

## Implementation notes

The source works over `ℂ`; the statement is made over an algebraically closed field of
characteristic zero. Valuations are those of `k(X)`, realized by divisors `(Y, f, E)` over `X`
(`MMP.Mori.DivisorOver`). A valuation of `k(X)` is a divisor over a nef weak model
`φ : X ⤏ Z` through a model `Y` carrying morphisms `f : Y ⟶ X` and `g : Y ⟶ Z` with
`g ∘ f⁻¹ = φ`; the boundary on `Z` is `φ_* B_i`, as in `MMP.Fourfold.IsNefWeakModel`.
A crepant real terminal model of `(X, B)` is a projective birational `h : Y ⟶ X` from a normal
variety with a real terminal boundary `B_Y` and a canonical divisor `K_Y` with `h_* K_Y = K_X`
such that `K_Y + B_Y = h^*(K_X + B)` as `ℝ`-Cartier divisors.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Filter
open scoped WithZero

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X S : Scheme.{u}}
  {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- **Uniform finiteness of low discrepancies near a real klt pair.** Let `X` be a normal
`ℚ`-factorial projective variety and `B_i → B` effective real boundaries supported on a fixed
finite set `T` of prime divisors, with `(X, B)` klt. There is a finite set `𝓕` of exceptional
divisorial valuations of `k(X)` such that:
* for all large `i`, `𝓕` contains every exceptional valuation `E` with `a(E, X, B_i) ≤ 1`;
* for every `i` and every nef weak model `φ : X ⤏ Z` of `(X, B_i)`, every valuation `E`
  exceptional over `X` with nonnegative codiscrepancy on `Z`, `a(E, Z, φ_* B_i) ≤ 1`, has
  `a(E, X, B_i) ≤ 1` (so lies in `𝓕` for `i` large);
* a valuation `E` with `a(E, X, B_i) ≤ 1` for infinitely many `i` has `a(E, X, B) ≤ 1` and is
  the valuation of a prime divisor on every crepant real terminal model `h : Y ⟶ X` of `(X, B)`.
-/
@[mmp "lem_fourfold_uniform_low_discrepancies_near_klt"]
public theorem IsRealKltPair.exists_finite_eventually_setOf_isLogDiscrepancy_le_one_subset
    (hQ : IsQFactorial sX) (hproj : MMP.Mori.IsProjectiveVariety k sX)
    {B : RDivisor X} (hB : IsRealKltPair sX B) (Bs : ℕ → RDivisor X)
    (hBs : ∀ i P, 0 ≤ (Bs i).coeff P) (T : Finset (MMP.Mori.PrimeDivisor X))
    (hT : ∀ i, (Bs i).support ⊆ T)
    (hlim : ∀ P, Tendsto (fun i => (Bs i).coeff P) atTop (nhds (B.coeff P))) :
    ∃ 𝓕 : Set (Valuation X.functionField ℤᵐ⁰), 𝓕.Finite ∧
      (∀ v ∈ 𝓕, ∃ E : DivisorOver k sX, E.IsExceptional ∧ E.valuation = v) ∧
      (∀ᶠ i in atTop, {v | ∃ (n : ℕ) (E : DivisorOver k sX) (a : ℝ),
          E.IsExceptional ∧ E.valuation = v ∧
            MMP.Intersection.IsLogDiscrepancy sX n (Bs i) E a ∧ a ≤ 1} ⊆ 𝓕) ∧
      (∀ (i : ℕ) (sS : S ⟶ Spec (.of k)) (πX : X ⟶ S) (K : Divisor X)
        (Z : Scheme.{u}) [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
        (sZ : Z ⟶ Spec (.of k)) [QuasiCompact sZ] (πZ : Z ⟶ S) (φ : X.RationalMap Z),
        IsNefWeakModel sX sZ sS πX πZ K (Bs i) φ →
        ∀ (E : DivisorOver k sX) (g : E.Y ⟶ Z) (hg : IsNormalVariety k (g ≫ sZ))
          (hgb : IsBirationalMorphism g) (f' : X.RationalMap E.Y),
          MMP.Mori.RationalMap.IsInverse E.f.toRationalMap f' → f'.compHom g = φ →
          E.IsExceptional →
          ∀ (n : ℕ) (a : ℝ),
            MMP.Intersection.IsLogDiscrepancy sZ n
              (MMP.Mori.RationalMap.transformDivisor φ (Bs i))
              ⟨E.Y, g, hg, hgb, E.E⟩ a → a ≤ 1 →
          ∃ (m : ℕ) (E' : DivisorOver k sX) (a' : ℝ), E'.IsExceptional ∧
            E'.valuation = E.valuation ∧
            MMP.Intersection.IsLogDiscrepancy sX m (Bs i) E' a' ∧ a' ≤ 1) ∧
      ∀ v : Valuation X.functionField ℤᵐ⁰,
        (∃ᶠ i in atTop, ∃ (n : ℕ) (E : DivisorOver k sX) (a : ℝ),
          E.IsExceptional ∧ E.valuation = v ∧
            MMP.Intersection.IsLogDiscrepancy sX n (Bs i) E a ∧ a ≤ 1) →
        (∀ (n : ℕ) (E : DivisorOver k sX) (a : ℝ), E.valuation = v →
          MMP.Intersection.IsLogDiscrepancy sX n B E a → a ≤ 1) ∧
        ∀ (Y : Scheme.{u}) [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (h : Y ⟶ X)
          (hY : IsNormalVariety k (h ≫ sX)) (hh : IsBirationalMorphism h)
          (KX : Divisor X) (KY : Divisor Y) (BY : RDivisor Y) (n : ℕ),
          IsProjectiveMorphism h → KX.IsCanonicalDivisor sX n →
          KY.IsCanonicalDivisor (h ≫ sX) n →
          MMP.Mori.RationalMap.transformDivisor h.toRationalMap KY = KX →
          MMP.Flips.IsRCartierPullback h (MMP.Flips.logCanonicalDivisor KX B)
            (MMP.Flips.logCanonicalDivisor KY BY) →
          IsRealTerminalPair (h ≫ sX) BY →
          ∃ P : MMP.Mori.PrimeDivisor Y, (⟨Y, h, hY, hh, P⟩ : DivisorOver k sX).valuation = v :=
            MMP.FourfoldProofs.FourfoldUniformLowDiscrepanciesNearKltProof.solution hQ hproj hB Bs hBs T
              hT hlim

end MMP.Fourfold

end
