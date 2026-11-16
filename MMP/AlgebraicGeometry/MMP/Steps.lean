/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.AlgebraicGeometry.MMP.Termination.Defs
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import StacksFrontier.RingTheory.RegularLocalRing.AssociatedGradedPolynomial

/-!
# Steps of the minimal model program in *Flips and abundance*

Common models of a modification (FA 2.23) and relatively free divisors (FA 2.22.3); flipping and
flipped curves, the blow-up divisor of a regular subvariety, the sets of small log discrepancy and
Szabó's modified difficulty (FA 4.12.3, 4.13–4.15); contractions of extremal rays and sequences of
log flips (FA 7.1).

## Main definitions

* `MMP.Flips.IsCommonModel`: a common model `W` of a modification `φ : X ⤏ Y`, with proper
  birational morphisms `p : W ⟶ X`, `q : W ⟶ Y` and `q = φ ∘ p`.
* `MMP.Flips.IsFlippingCurve`, `MMP.Flips.IsFlippedCurveOf`: components of positive dimension of
  the fibres over closed points of a contraction, resp. of a flip.
* `MMP.Flips.maximalIdealOrder`, `MMP.Flips.IsBlowupDivisor`, `MMP.Flips.blowupDivisor`: the
  order function `max {n : φ ∈ 𝔪ⁿ}` of a local ring, and the blow-up divisor `E_W` of a
  subvariety `W` along which `X` is regular.
* `MMP.Flips.smallLogDiscrepancySet`, `MMP.Flips.smallLogDiscrepancySetOff`: `𝒮_t(X, D)` and
  `𝒮_t(X, D; B)`.
* `MMP.Flips.szaboDifficulty`: `d_{N,c}(X, D; B) ∈ ℕ ∪ {∞}`.
* `MMP.Flips.IsExtremalRayContraction`: `(K_X + B)`-negative contractions of an extremal ray.
* `MMP.Flips.SequenceOfLogFlips`: a sequence of log flips starting from an lc pair `(X₀, B₀)`
  on a `ℚ`-factorial threefold.

A divisor `L` is `g`-free for `g : Y ⟶ Z` when `g^* g_* 𝒪_Y(L) ⟶ 𝒪_Y(L)` is surjective: this is
Kollár–Mori's `MMP.Mori.IsRelativelyFreeCartier`, registered here under its FA label.

## Implementation notes

* Linear equivalence `mL ∼ φ^* M` of Cartier divisors is recorded as an isomorphism
  `𝒪_X(mL) ≅ φ^* 𝒪_Z(M)` of invertible sheaves; on a normal variety two Cartier divisors are
  linearly equivalent exactly when their invertible sheaves are isomorphic, and
  `𝒪_X(φ^* M) ≅ φ^* 𝒪_Z(M)`.
* The intersection number `L · C` with a curve contracted by `φ` is the degree of `𝒪_X(L)` on
  the curve (`MMP.Mori.Divisor.degreeOn`).
* The blow-up divisor `E_W` is characterized by a predicate on functions `K(X)^* → ℤ`; such a
  function is unique (`MMP.Flips.IsBlowupDivisor.unique`) and exists
  (`MMP.Flips.isBlowupDivisor_blowupDivisor`): `E_W(φ/ψ) = E_W(φ) - E_W(ψ)` is well defined
  because the order function of a regular local ring is multiplicative
  (`MMP.Flips.maximalIdealOrder_mul`), its associated graded ring being a polynomial ring over the
  residue field (Stacks 00NO).
* A sequence of log flips records its models as in `MMP.Flips.SequenceOfFlips`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.22.3, 2.23,
  4.12.3, 4.13, 4.14, 4.15, 7.1
* [Y. Kawamata, K. Matsuda, K. Matsuki, *Introduction to the minimal model problem*], 3-2-1
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped WithZero

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Flips

open MMP.Mori

/-! ### Relatively free divisors and common models -/

attribute [mmp "def_fa2_relatively_free"] MMP.Mori.IsRelativelyFreeCartier

section CommonModel

variable (k : Type u) [Field k] {X Y Z W : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k)) (sW : W ⟶ Spec (.of k))

/-- In the setting of FA 2.21 (proper morphisms `f : X ⟶ Z`, `g : Y ⟶ Z` of varieties and a
modification `φ : X ⤏ Y` of `f` into `g`), a *common model* of `φ` is a normal variety `W` with
proper birational morphisms `p : W ⟶ X` and `q : W ⟶ Y` such that `q = φ ∘ p` as maps: for a
representative `φ₀ : U ⟶ Y` of `φ` on a dense open `U ⊆ X`, the composite
`p⁻¹(U) ⟶ U ⟶ Y`, defined on the dense open `p⁻¹(U)`, is `q` as a map. FA writes
`f̃ = p`, `g̃ = q`. -/
@[mmp "def_fa2_common_resolution_data"]
structure IsCommonModel (f : X ⟶ Z) (g : Y ⟶ Z) (φ : X.RationalMap Y) (p : W ⟶ X) (q : W ⟶ Y) :
    Prop where
  /-- `X` is a variety. -/
  isVariety_X : Mori.IsVariety k sX
  /-- `Y` is a variety. -/
  isVariety_Y : Mori.IsVariety k sY
  /-- `Z` is a variety. -/
  isVariety_Z : Mori.IsVariety k sZ
  /-- `f` is a morphism of varieties. -/
  comp_f : f ≫ sZ = sX
  /-- `g` is a morphism of varieties. -/
  comp_g : g ≫ sZ = sY
  /-- `f` is proper. -/
  isProper_f : IsProper f
  /-- `g` is proper. -/
  isProper_g : IsProper g
  /-- `φ` is a modification of `f` into `g`. -/
  isModificationOf : IsModificationOf f g φ
  /-- `W` is a normal variety. -/
  isNormalVariety : IsNormalVariety k sW
  /-- `p` is a morphism of varieties. -/
  comp_p : p ≫ sX = sW
  /-- `q` is a morphism of varieties. -/
  comp_q : q ≫ sY = sW
  /-- `p` is proper. -/
  isProper_p : IsProper p
  /-- `q` is proper. -/
  isProper_q : IsProper q
  /-- `p` is birational. -/
  isBirationalMorphism_p : IsBirationalMorphism p
  /-- `q` is birational. -/
  isBirationalMorphism_q : IsBirationalMorphism q
  /-- `q = φ ∘ p` as maps. -/
  comp_eq : ∃ φ₀ : X.PartialMap Y, φ₀.toRationalMap = φ ∧
    ∃ hd : Dense ((p ⁻¹ᵁ φ₀.domain : W.Opens) : Set W),
      (Scheme.PartialMap.mk (p ⁻¹ᵁ φ₀.domain) hd
        (p.resLE φ₀.domain (p ⁻¹ᵁ φ₀.domain) le_rfl ≫ φ₀.hom)).toRationalMap =
        q.toRationalMap

end CommonModel

/-! ### Flipping and flipped curves -/

section Curves

variable (k : Type u) [Field k] {X Z : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  (sZ : Z ⟶ Spec (.of k))

/-- Let `φ : X ⟶ Z` be a proper morphism of varieties. A *flipping curve* of `φ` is an irreducible
component `C` of positive dimension of a fibre `φ⁻¹(z)` over a closed point `z ∈ Z`: a maximal
irreducible subset of `φ⁻¹(z)` with `dim C > 0`. -/
@[mmp "def_fa4_flipping_curve"]
def IsFlippingCurve (φ : X ⟶ Z) (C : Set X) : Prop :=
  Mori.IsVariety k sX ∧ Mori.IsVariety k sZ ∧ φ ≫ sZ = sX ∧ IsProper φ ∧
    ∃ z : Z, IsClosed ({z} : Set Z) ∧
      Maximal (fun S : Set X => IsIrreducible S ∧ S ⊆ {x | φ x = z}) C ∧
      0 < topologicalKrullDim C

variable {X' : Scheme.{u}} (sX' : X' ⟶ Spec (.of k)) [IsLocallyNoetherian X] [IsNormal X]
  [CompactSpace X] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']

/-- Let `φ⁺ : X⁺ ⟶ Z` be a flip of a small contraction `φ : X ⟶ Z` with respect to `E`, with
birational map `g : X ⤏ X⁺` over `Z` (`MMP.Flips.IsFlip`). A *flipped curve* is a flipping curve
of `φ⁺`. -/
@[mmp "def_fa4_flipped_curve"]
def IsFlippedCurveOf (E : RDivisor X) (φ : X ⟶ Z) (φp : X' ⟶ Z) (g : X.RationalMap X')
    (C : Set X') : Prop :=
  IsFlip k sX sZ sX' E φ φp g ∧ IsFlippingCurve k sX' sZ φp C

end Curves

/-! ### The blow-up divisor of a regular subvariety -/

section Blowup

variable {R : Type*} [CommRing R] [IsLocalRing R]

variable (R) in
/-- The *order function* of a local ring `(R, 𝔪)`: `ord(φ) = max {n ≥ 0 : φ ∈ 𝔪ⁿ}`, a maximum
for `φ ≠ 0` in a Noetherian local ring (`MMP.Flips.maximalIdealOrder_spec`). -/
def maximalIdealOrder (φ : R) : ℕ :=
  sSup {n : ℕ | φ ∈ IsLocalRing.maximalIdeal R ^ n}

/-- In a Noetherian local ring, for `φ ≠ 0`, `ord(φ)` is the largest `n` with `φ ∈ 𝔪ⁿ`:
`φ ∈ 𝔪^{ord φ}` and `φ ∉ 𝔪^{ord φ + 1}`. -/
theorem maximalIdealOrder_spec [IsNoetherianRing R] {φ : R} (hφ : φ ≠ 0) :
    φ ∈ IsLocalRing.maximalIdeal R ^ maximalIdealOrder R φ ∧
      φ ∉ IsLocalRing.maximalIdeal R ^ (maximalIdealOrder R φ + 1) := by
  set S := {n : ℕ | φ ∈ IsLocalRing.maximalIdeal R ^ n}
  have hbdd : BddAbove S := by
    by_contra h
    rw [not_bddAbove_iff] at h
    apply hφ
    have h0 := Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal R)
      (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    rw [← Ideal.mem_bot, ← h0, Submodule.mem_iInf]
    intro i
    obtain ⟨n, hn, hin⟩ := h i
    exact Ideal.pow_le_pow_right hin.le hn
  have hne : S.Nonempty := ⟨0, by simp [S]⟩
  refine ⟨Nat.sSup_mem hne hbdd, fun h => ?_⟩
  have : maximalIdealOrder R φ + 1 ≤ maximalIdealOrder R φ := le_csSup hbdd (show _ ∈ S from h)
  omega

/-- The class of `a ∈ Iⁿ` in the degree-`n` piece `Iⁿ/Iⁿ⁺¹` of the associated graded ring
vanishes exactly when `a ∈ Iⁿ⁺¹`. -/
theorem associatedGraded_classOfPow_eq_zero_iff {A : Type*} [CommRing A] (I : Ideal A)
    (n : ℕ) (a : ↥(I ^ n)) :
    AssociatedGraded.classOfPow I n a = 0 ↔ (a : A) ∈ I ^ (n + 1) := by
  change DirectSum.of _ n _ = 0 ↔ _
  rw [← map_zero (DirectSum.of (fun j => AssociatedGraded.piece (M := A) I j) n),
    (DirectSum.of_injective n).eq_iff]
  unfold AssociatedGraded.mk
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, AssociatedGraded.ring_power_eq]
  rfl

/-- The associated graded ring `⨁ₙ 𝔪ⁿ/𝔪ⁿ⁺¹` of a regular local ring is a domain: it is a
polynomial ring over the residue field (Stacks 00NO,
`IsRegularLocalRing.gradedRingEquivMvPolynomial`). -/
theorem isDomain_gradedRing_of_isRegularLocalRing (R : Type*) [CommRing R]
    [IsRegularLocalRing R] :
    IsDomain (AssociatedGraded.gradedRing (IsLocalRing.maximalIdeal R)) := by
  classical
  obtain ⟨s, hcard, hspan⟩ :=
    (IsNoetherian.noetherian (IsLocalRing.maximalIdeal R)).exists_span_finset_card_eq_spanFinrank
  have hxs : Ideal.ofList s.toList = IsLocalRing.maximalIdeal R := by
    rw [← hspan]; exact congrArg Ideal.span (by ext x; simp)
  have hmin : s.toList.length = (IsLocalRing.maximalIdeal R).spanFinrank := by simp [hcard]
  have hx : ∀ i : Fin s.toList.length, s.toList[i] ∈ IsLocalRing.maximalIdeal R := fun i => by
    rw [← hxs]; exact Ideal.subset_span (List.getElem_mem _)
  let e := IsRegularLocalRing.gradedRingEquivMvPolynomial s.toList hxs hmin hx
  exact e.symm.injective.isDomain e.symm.toRingHom

/-- If `φ` has order exactly `a` and `ψ` order exactly `b` in a regular local ring `(S, 𝔪)`, then
`φψ ∉ 𝔪^{a+b+1}`: the product of the nonzero initial forms of `φ` and `ψ` in the domain
`⨁ₙ 𝔪ⁿ/𝔪ⁿ⁺¹` is nonzero. -/
theorem mul_notMem_maximalIdeal_pow_add_succ {S : Type*} [CommRing S] [IsRegularLocalRing S]
    {a b : ℕ} {φ ψ : S}
    (hφ : φ ∈ IsLocalRing.maximalIdeal S ^ a) (hφ' : φ ∉ IsLocalRing.maximalIdeal S ^ (a + 1))
    (hψ : ψ ∈ IsLocalRing.maximalIdeal S ^ b) (hψ' : ψ ∉ IsLocalRing.maximalIdeal S ^ (b + 1)) :
    φ * ψ ∉ IsLocalRing.maximalIdeal S ^ (a + b + 1) := by
  have := isDomain_gradedRing_of_isRegularLocalRing S
  intro h
  have h0 := (associatedGraded_classOfPow_eq_zero_iff (IsLocalRing.maximalIdeal S) (a + b)
    ⟨φ * ψ, by simpa only [pow_add] using Ideal.mul_mem_mul hφ hψ⟩).2 h
  rw [AssociatedGraded.classOfPow_mul _ a b ⟨φ, hφ⟩ ⟨ψ, hψ⟩, mul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact hφ' ((associatedGraded_classOfPow_eq_zero_iff _ a _).1 h0)
  · exact hψ' ((associatedGraded_classOfPow_eq_zero_iff _ b _).1 h0)

/-- **The order function of a regular local ring is multiplicative**:
`ord(φψ) = ord(φ) + ord(ψ)` for `φ, ψ ≠ 0`. -/
@[mmp "lem_mmp_foundation_km_order_additive"]
theorem maximalIdealOrder_mul {S : Type*} [CommRing S] [IsRegularLocalRing S] {φ ψ : S}
    (hφ : φ ≠ 0) (hψ : ψ ≠ 0) :
    maximalIdealOrder S (φ * ψ) = maximalIdealOrder S φ + maximalIdealOrder S ψ := by
  have := IsRegularLocalRing.isDomain S
  obtain ⟨h1, h2⟩ := maximalIdealOrder_spec hφ
  obtain ⟨h3, h4⟩ := maximalIdealOrder_spec hψ
  have hne : φ * ψ ≠ 0 := mul_ne_zero hφ hψ
  obtain ⟨h5, h6⟩ := maximalIdealOrder_spec hne
  have hmem : φ * ψ ∈ IsLocalRing.maximalIdeal S ^
      (maximalIdealOrder S φ + maximalIdealOrder S ψ) := by
    rw [pow_add]; exact Ideal.mul_mem_mul h1 h3
  have hnot := mul_notMem_maximalIdeal_pow_add_succ h1 h2 h3 h4
  apply le_antisymm
  · by_contra hlt
    exact hnot (Ideal.pow_le_pow_right (by omega) h5)
  · by_contra hlt
    exact h6 (Ideal.pow_le_pow_right (by omega) hmem)

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]

/-- Let `X` be a normal variety and `W ⊆ X` an irreducible closed subset of codimension `c ≥ 2`
such that the local ring `𝒪_{X,η_W}` at the generic point `η_W` of `W` is regular, with maximal
ideal `𝔪_W`. The *blow-up divisor* `E_W : K(X)^* → ℤ` of `W` is the order function of
`𝒪_{X,η_W}`, `E_W(φ) = max {n ≥ 0 : φ ∈ 𝔪_Wⁿ}` for `0 ≠ φ ∈ 𝒪_{X,η_W}`, extended to `K(X)^*` by
`E_W(φ/ψ) = E_W(φ) - E_W(ψ)`: a function `E` is the blow-up divisor when `E(f) = ord(φ) - ord(ψ)`
whenever `f = φ/ψ` with `φ, ψ ≠ 0` in `𝒪_{X,η_W}` (taking `ψ = 1` gives `E(φ) = ord(φ)`). For a
curve `C` in a threefold this is the `E_C` of FA. -/
@[mmp "def_fa4_curve_blowup_divisor"]
def IsBlowupDivisor (W : IrreducibleCloseds X) (E : X.functionFieldˣ → ℤ) : Prop :=
  IsNormalVariety k sX ∧ 2 ≤ codimension W ∧
    IsRegularLocalRing (X.presheaf.stalk W.isIrreducible.genericPoint) ∧
    ∀ (f : X.functionFieldˣ) (φ ψ : X.presheaf.stalk W.isIrreducible.genericPoint),
      φ ≠ 0 → ψ ≠ 0 → (f : X.functionField) * algebraMap _ X.functionField ψ =
        algebraMap _ X.functionField φ →
      E f = (maximalIdealOrder _ φ : ℤ) - maximalIdealOrder _ ψ

variable {sX} in
/-- The blow-up divisor `E_W` is unique: every `f ∈ K(X)^*` is a quotient `φ/ψ` of nonzero elements
of `𝒪_{X,η_W}`. -/
@[mmp "def_fa4_curve_blowup_divisor"]
theorem IsBlowupDivisor.unique {W : IrreducibleCloseds X} {E E' : X.functionFieldˣ → ℤ}
    (hE : IsBlowupDivisor sX W E) (hE' : IsBlowupDivisor sX W E') : E = E' := by
  funext f
  set A := X.presheaf.stalk W.isIrreducible.genericPoint
  obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj (nonZeroDivisors A) (f : X.functionField)
  have hs : (s : A) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have ha : a ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_eq_zero] at h
    rcases h with h | h
    · exact f.ne_zero h
    · exact hs ((IsFractionRing.injective A X.functionField).eq_iff.mp (h.trans (map_zero _).symm))
  rw [hE.2.2.2 f a s ha hs h, hE'.2.2.2 f a s ha hs h]

variable (W : IrreducibleCloseds X)

/-- The *blow-up divisor* `E_W : K(X)^* → ℤ`, `E_W(φ/ψ) = ord(φ) - ord(ψ)`, computed from a
chosen presentation `f = φ/ψ` of `f` as a fraction of elements of `𝒪_{X,η_W}`. It is independent
of the presentation, and is the blow-up divisor of FA, when `𝒪_{X,η_W}` is regular
(`MMP.Flips.isBlowupDivisor_blowupDivisor`). For a curve `C` in a threefold this is the `E_C`
of FA. -/
@[mmp "def_fa4_curve_blowup_divisor"]
def blowupDivisor (f : X.functionFieldˣ) : ℤ :=
  let p := IsLocalization.surj (nonZeroDivisors (X.presheaf.stalk W.isIrreducible.genericPoint))
    (f : X.functionField)
  (maximalIdealOrder _ p.choose.1 : ℤ) -
    maximalIdealOrder _ (p.choose.2 : X.presheaf.stalk W.isIrreducible.genericPoint)

variable {sX W} in
/-- **Existence of the blow-up divisor.** When `X` is a normal variety, `W` has codimension
`≥ 2` and `𝒪_{X,η_W}` is regular, `E_W(φ/ψ) = ord(φ) - ord(ψ)` is well defined, by the
multiplicativity of the order function of a regular local ring
(`MMP.Flips.maximalIdealOrder_mul`): `blowupDivisor W` is the blow-up divisor of `W`. -/
@[mmp "def_fa4_curve_blowup_divisor"]
theorem isBlowupDivisor_blowupDivisor (hX : IsNormalVariety k sX) (hW : 2 ≤ codimension W)
    (hreg : IsRegularLocalRing (X.presheaf.stalk W.isIrreducible.genericPoint)) :
    IsBlowupDivisor sX W (blowupDivisor W) := by
  refine ⟨hX, hW, hreg, fun f φ ψ hφ hψ hf => ?_⟩
  have hinj := IsFractionRing.injective (X.presheaf.stalk W.isIrreducible.genericPoint)
    X.functionField
  obtain ⟨hp⟩ : Nonempty (_ = _) :=
    ⟨(IsLocalization.surj (nonZeroDivisors (X.presheaf.stalk W.isIrreducible.genericPoint))
      (f : X.functionField)).choose_spec⟩
  dsimp only [blowupDivisor]
  generalize (IsLocalization.surj (nonZeroDivisors (X.presheaf.stalk W.isIrreducible.genericPoint))
      (f : X.functionField)).choose = q at hp ⊢
  obtain ⟨a, s⟩ := q
  dsimp only at hp ⊢
  have hs : (s : X.presheaf.stalk W.isIrreducible.genericPoint) ≠ 0 :=
    nonZeroDivisors.coe_ne_zero s
  have ha : a ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_eq_zero] at hp
    rcases hp with h | h
    · exact f.ne_zero h
    · exact hs (hinj.eq_iff.mp (h.trans (map_zero _).symm))
  have hrel : a * ψ = φ * s := by
    apply hinj
    rw [map_mul, map_mul, ← hp, ← hf]
    ring
  have h := congrArg (maximalIdealOrder _) hrel
  rw [maximalIdealOrder_mul ha hψ, maximalIdealOrder_mul hφ hs] at h
  omega

variable {sX W} in
/-- A function `E : K(X)^* → ℤ` is the blow-up divisor of `W` exactly when the hypotheses of FA
hold and `E = E_W`. -/
@[mmp "def_fa4_curve_blowup_divisor"]
theorem isBlowupDivisor_iff {E : X.functionFieldˣ → ℤ} :
    IsBlowupDivisor sX W E ↔ (IsNormalVariety k sX ∧ 2 ≤ codimension W ∧
      IsRegularLocalRing (X.presheaf.stalk W.isIrreducible.genericPoint)) ∧
        E = blowupDivisor W :=
  ⟨fun hE => ⟨⟨hE.1, hE.2.1, hE.2.2.1⟩,
      hE.unique (isBlowupDivisor_blowupDivisor hE.1 hE.2.1 hE.2.2.1)⟩,
    fun ⟨⟨h1, h2, h3⟩, hE⟩ => hE ▸ isBlowupDivisor_blowupDivisor h1 h2 h3⟩

end Blowup

/-! ### Sets of small log discrepancy and Szabó's difficulty -/

section SmallLogDiscrepancy

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]

/-- Let `X` be a normal variety with canonical divisor `K` of dimension `n`, `D` a `ℚ`-divisor on
`X` with `K_X + D` `ℚ`-Cartier, and `t ∈ ℚ`. Then `𝒮_t(X, D)` is the set of exceptional divisors
`ν` of `K(X)` with nonempty center on `X` such that `a_ℓ(ν, X, D) < t`. An exceptional divisor of
`K(X)` with nonempty center is the valuation `ord_E` of an exceptional divisor `(Y, f, E)` over
`X`. -/
@[mmp "def_fa4_small_log_discrepancy_set"]
def smallLogDiscrepancySet (n : ℕ) (K : Divisor X) (D : QDivisor X)
    (_hX : IsNormalVariety k sX) (_hK : K.IsCanonicalDivisor sX n)
    (_hD : (Divisor.toQDivisor K + D).IsQCartier) (t : ℚ) :
    Set (Valuation X.functionField ℤᵐ⁰) :=
  {ν | HasNonemptyCenter k sX ν ∧
    (∃ E : ProperDivisorOver k sX, E.IsExceptional ∧ E.valuation = ν) ∧
    ∃ b : ℝ, IsLogDiscrepancy sX n K (QDivisor.toRDivisor D) ν b ∧ b < t}

/-- Let `X`, `D` be as in `MMP.Flips.smallLogDiscrepancySet`, `B ⊆ X` a closed subset and
`t ∈ ℚ`. Then `𝒮_t(X, D; B)` is the set of `ν ∈ 𝒮_t(X, D)` such that `Center_X(ν)` is not an
irreducible closed subset of codimension `2` of `X` contained in `B`. The center of `ν` is the
center `f(E)` of any divisor `(Y, f, E)` over `X` with `ord_E = ν` (all such centers agree); the
condition is imposed on every such realization. -/
@[mmp "def_fa4_small_log_discrepancy_set_off"]
def smallLogDiscrepancySetOff (n : ℕ) (K : Divisor X) (D : QDivisor X)
    (hX : IsNormalVariety k sX) (hK : K.IsCanonicalDivisor sX n)
    (hD : (Divisor.toQDivisor K + D).IsQCartier) (B : Closeds X) (t : ℚ) :
    Set (Valuation X.functionField ℤᵐ⁰) :=
  {ν ∈ smallLogDiscrepancySet sX n K D hX hK hD t | ∀ E : ProperDivisorOver k sX,
    E.valuation = ν → ¬ (codimension E.center = 2 ∧ (E.center : Set X) ⊆ B)}

/-- Let `X`, `D`, `B` be as in `MMP.Flips.smallLogDiscrepancySetOff`, `N ≥ 1` an integer and
`c ∈ ℚ`. Szabó's modified difficulty is
`d_{N,c}(X, D; B) = ∑_{i ∈ ℤ, i ≥ Nc} #𝒮_{2 - i/N}(X, D; B) ∈ ℕ ∪ {∞}`, a sum in `ℕ∞` (where every
family is summable, with sum the supremum of the finite partial sums). -/
@[mmp "def_fa4_szabo_difficulty"]
def szaboDifficulty (n : ℕ) (K : Divisor X) (D : QDivisor X)
    (hX : IsNormalVariety k sX) (hK : K.IsCanonicalDivisor sX n)
    (hD : (Divisor.toQDivisor K + D).IsQCartier) (B : Closeds X) (N : ℕ) (_hN : 1 ≤ N) (c : ℚ) :
    ℕ∞ :=
  ∑' i : {i : ℤ // (N : ℚ) * c ≤ i},
    (smallLogDiscrepancySetOff sX n K D hX hK hD B (2 - (i : ℚ) / N)).encard

end SmallLogDiscrepancy

/-! ### Contractions of extremal rays -/

section ExtremalRay

variable (k : Type u) [Field k] {X Z : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  (sZ : Z ⟶ Spec (.of k)) [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsLocallyNoetherian Z] [IsNormal Z]

/-- Let `X` be a normal variety with canonical divisor `K` of dimension `n` and `B` a `ℚ`-divisor
on `X` with `K_X + B` `ℚ`-Cartier. A *`(K_X + B)`-negative contraction of an extremal ray* is a
`(K_X + B)`-negative extremal contraction `φ : X ⟶ Z` onto a normal variety (a contraction with
`-(K_X + B)` `φ`-ample and `ρ(X/Z) = 1`, `MMP.Flips.IsNegativeExtremalContraction`) such that for
every Cartier divisor `L` on `X` with `L · C = 0` for every curve `C ⊆ X` contracted by `φ` there
are an integer `m > 0` and a Cartier divisor `M` on `Z` with `mL ∼ φ^* M`, recorded as an
isomorphism `𝒪_X(mL) ≅ φ^* 𝒪_Z(M)` of invertible sheaves. -/
@[mmp "def_fa7_extremal_ray_contraction"]
structure IsExtremalRayContraction (n : ℕ) (K : Divisor X) (B : QDivisor X) (φ : X ⟶ Z) :
    Prop where
  /-- `K` is a canonical divisor of `X`. -/
  isCanonicalDivisor : K.IsCanonicalDivisor sX n
  /-- `K_X + B` is `ℚ`-Cartier. -/
  isQCartier : (Divisor.toQDivisor K + B).IsQCartier
  /-- `φ` is a `(K_X + B)`-negative extremal contraction onto a normal variety. -/
  isNegativeExtremalContraction :
    IsNegativeExtremalContraction k sX sZ (logCanonicalDivisor K (QDivisor.toRDivisor B)) φ
  /-- A Cartier divisor `L` with `L · C = 0` for every curve `C` contracted by `φ` has a positive
  multiple `mL ∼ φ^* M` for a Cartier divisor `M` on `Z`. -/
  exists_pullback : ∀ (L : Divisor X) (hL : L.IsCartier),
    (haveI : QuasiCompact sX := quasiCompact_of_compactSpace sX
      ∀ C : ProperCurve sX, C.IsContractedBy φ → L.degreeOn k sX C.ι C.dim_le hL = 0) →
    ∃ m : ℕ, 0 < m ∧ ∃ M : Divisor Z, M.IsCartier ∧
      Nonempty (((m : ℤ) • L).divisorialSheaf ≅ (Scheme.Modules.pullback φ).obj M.divisorialSheaf)

end ExtremalRay

/-! ### Sequences of log flips -/

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]

/-- Let `X₀` be a normal `ℚ`-factorial threefold (every Weil divisor has a positive multiple which
is Cartier, as in `def_mmp_q_factorial`) with canonical divisor `K₀`, and `B₀` an effective
`ℚ`-divisor on `X₀` with `(X₀, B₀)` lc. A *sequence of log flips starting from `(X₀, B₀)`* consists
of `L ∈ {1, 2, 3, …} ∪ {∞}`, normal threefolds `X_i` (with canonical divisors `K_i`) with
`ℚ`-divisors `B_i` for `0 ≤ i < L`, and for every `i` with `i + 1 < L`:
1. a small `(K_{X_i} + B_i)`-negative contraction of an extremal ray `φ_i : X_i ⟶ Z_i` (in
   particular `K_{X_i} + B_i` is `ℚ`-Cartier);
2. a `(K_{X_i} + B_i)`-flip `φ_i⁺ : X_{i+1} ⟶ Z_i` of `φ_i`, with birational map
   `g_i = (φ_i⁺)⁻¹ ∘ φ_i : X_i ⤏ X_{i+1}` over `Z_i`, such that `B_{i+1} = g_{i*} B_i` is the
   birational transform of `B_i`.

The models are recorded as in `MMP.Flips.SequenceOfFlips`, with `(X_0, K_0, B_0)` the given
triple. -/
@[mmp "def_fa7_sequence_of_log_flips"]
structure SequenceOfLogFlips (K : Divisor X) (B : QDivisor X) where
  /-- `X₀` is a normal variety. -/
  isNormalVariety : IsNormalVariety k sX
  /-- `X₀` is `ℚ`-factorial. -/
  isQFactorial : ∀ D : Divisor X, ∃ m : ℕ, 0 < m ∧ ((m : ℤ) • D).IsCartier
  /-- `X₀` is a threefold. -/
  dim_eq : topologicalKrullDim X = 3
  /-- `B₀` is effective. -/
  isEffective : B.IsEffective
  /-- `(X₀, B₀)` is lc, with canonical divisor `K₀` of dimension `3`. -/
  isLogCanonical : IsLogCanonical sX 3 K (QDivisor.toRDivisor B)
  /-- The length `L ∈ {1, 2, …} ∪ {∞}`. -/
  length : ℕ∞
  /-- The length is at least `1`. -/
  one_le_length : 1 ≤ length
  /-- The models `(X_i, K_i, B_i)`, used for `i < L`. -/
  model : ℕ → FlipModel k
  /-- `(X_0, K_0, B_0) = (X₀, K₀, B₀)`. -/
  model_zero : model 0 = ⟨X, sX, K, B⟩
  /-- The models are normal varieties. -/
  isNormalVariety_model : ∀ i : ℕ, (i : ℕ∞) < length → IsNormalVariety k (model i).2.1
  /-- The models are threefolds. -/
  dim_model : ∀ i : ℕ, (i : ℕ∞) < length → topologicalKrullDim (model i).1 = 3
  /-- Each `X_i` is locally Noetherian. -/
  isLocallyNoetherian_model : ∀ i, IsLocallyNoetherian (model i).1
  /-- Each `X_i` is normal. -/
  isNormal_model : ∀ i, IsNormal (model i).1
  /-- Each `X_i` is quasi-compact. -/
  compactSpace_model : ∀ i, CompactSpace (model i).1
  /-- `K_i` is a canonical divisor of `X_i`. -/
  isCanonicalDivisor_model : ∀ i : ℕ, (i : ℕ∞) < length →
    haveI := isLocallyNoetherian_model i
    haveI := isNormal_model i
    (model i).2.2.1.IsCanonicalDivisor (model i).2.1 3
  /-- The bases `Z_i` of the contractions. -/
  base : ℕ → Scheme.{u}
  /-- The structure morphisms of the `Z_i`. -/
  baseStr : ∀ i, base i ⟶ Spec (.of k)
  /-- Each `Z_i` is locally Noetherian. -/
  isLocallyNoetherian_base : ∀ i, IsLocallyNoetherian (base i)
  /-- Each `Z_i` is normal. -/
  isNormal_base : ∀ i, IsNormal (base i)
  /-- The contractions `φ_i : X_i ⟶ Z_i`. -/
  contraction : ∀ i, (model i).1 ⟶ base i
  /-- The flips `φ_i⁺ : X_{i+1} ⟶ Z_i`. -/
  flip : ∀ i, (model (i + 1)).1 ⟶ base i
  /-- The birational maps `g_i : X_i ⤏ X_{i+1}`. -/
  flipMap : ∀ i, (model i).1.RationalMap (model (i + 1)).1
  /-- `φ_i` is a `(K_{X_i} + B_i)`-negative contraction of an extremal ray. -/
  isExtremalRayContraction : ∀ i : ℕ, ((i + 1 : ℕ) : ℕ∞) < length →
    haveI := isLocallyNoetherian_model i
    haveI := isNormal_model i
    haveI := compactSpace_model i
    haveI := isLocallyNoetherian_base i
    haveI := isNormal_base i
    IsExtremalRayContraction k (model i).2.1 (baseStr i) 3 (model i).2.2.1 (model i).2.2.2
      (contraction i)
  /-- `φ_i` is small. -/
  isSmall : ∀ i : ℕ, ((i + 1 : ℕ) : ℕ∞) < length →
    IsSmall k (baseStr i) (model i).2.1 (contraction i)
  /-- `φ_i⁺` is a flip of `φ_i` with respect to `K_{X_i} + B_i`, with birational map `g_i` over
  `Z_i`. -/
  isFlip : ∀ i : ℕ, ((i + 1 : ℕ) : ℕ∞) < length →
    haveI := isLocallyNoetherian_model i
    haveI := isNormal_model i
    haveI := compactSpace_model i
    haveI := isLocallyNoetherian_model (i + 1)
    haveI := isNormal_model (i + 1)
    haveI := compactSpace_model (i + 1)
    IsFlip k (model i).2.1 (baseStr i) (model (i + 1)).2.1
      (logCanonicalDivisor (model i).2.2.1 (QDivisor.toRDivisor (model i).2.2.2))
      (contraction i) (flip i) (flipMap i)
  /-- `B_{i+1} = g_{i*} B_i`. -/
  transform_eq : ∀ i : ℕ, ((i + 1 : ℕ) : ℕ∞) < length →
    (model (i + 1)).2.2.2 = Mori.RationalMap.transformDivisor (flipMap i) (model i).2.2.2

end MMP.Flips
