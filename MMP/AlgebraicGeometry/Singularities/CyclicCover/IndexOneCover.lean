/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.AlgebraicGeometry.Singularities.CyclicCover.Divisorial
public import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.IntersectionInvertibleSheaf

/-!
# The local index-one cover at a scheme point

Let `X` be a normal scheme, `x ∈ X` any scheme point (not necessarily closed) and `D` a Weil
divisor on `X`. The divisor `D` is *Cartier at `x`* if its restriction to some open
neighbourhood of `x` is Cartier, and `D` is *`ℚ`-Cartier at `x`* if some positive multiple `mD`
is Cartier at `x`; the least such `m` is the *(rational) Cartier index of `D` at `x`*.

If `m` is the index of `D` at `x`, index-one cover data consists of an affine open
neighbourhood `U` of `x` and a unit `φ` of `K(U)` with `mD|_U + div(φ) = 0`. The *index-one
cover* of `D` at `x` is then the cyclic cover defined by `(D|_U, m, φ)`,
`Spec_U (⊕_{i=0}^{m-1} 𝒪_U(-iD)) → U`, with `(a eᵢ)(b eⱼ) = ab eᵢ₊ⱼ` for `i + j < m` and
`= φab eᵢ₊ⱼ₋ₘ` for `i + j ≥ m`; the grading gives the action of `μ_m`. Nothing in the
construction requires `x` to be closed: the index and the trivialization `φ` are local at `x`.

For `X` integral, Cartierness at `x` is read on the local scheme `Spec 𝒪_{X,x}`: its prime
divisors are the prime divisors `E` of `X` through `x`, with the same local rings `𝒪_{X,E}`. If the
pull-back of `D` is the divisor of a rational function `f`, then `f ∈ K(X)` has `ord_E f = D_E`
along every `E` through `x`; on an affine neighbourhood of `x` only finitely many prime divisors
have `ord_E f ≠ D_E`, none of them through `x`, and removing them leaves a neighbourhood on which
`f` is a local equation of `D`.

## Main definitions

* `MMP.Flips.IsCartierAt`: `D` is Cartier on a neighbourhood of `x`.
* `MMP.Flips.IsQCartierAt`: some positive multiple of `D` is Cartier at `x`.
* `MMP.Flips.cartierIndexAt`: the Cartier index of `D` at `x`, the least `m ≥ 1` with `mD`
  Cartier at `x`.
* `MMP.Flips.primeDivisorFromSpecStalk`: the prime divisor of `X` through `x` defined by a prime
  divisor of `Spec 𝒪_{X,x}`.
* `MMP.Flips.stalkWeilDivisor`: the pull-back of a Weil divisor on `X` to `Spec 𝒪_{X,x}`.
* `MMP.Flips.IndexOneCoverData`: an affine open neighbourhood `U` of `x` with a unit `φ` of
  `K(U)` such that `mD|_U + div(φ) = 0`, `m` the Cartier index of `D` at `x`.
* `MMP.Flips.IndexOneCoverData.cover`, `MMP.Flips.IndexOneCoverData.toBase`: the index-one
  cover `Spec_U (⊕_{i<m} 𝒪_U(-iD)) → U`.
* `MMP.Flips.IndexOneCoverData.scalingIso`: the action of an `m`-th root of unity on the
  index-one cover.

## Main results

* `MMP.Flips.cartierIndexAt_pos`, `MMP.Flips.isCartierAt_cartierIndexAt_smul`,
  `MMP.Flips.cartierIndexAt_le`: the index is the least positive `m` with `mD` Cartier at `x`.
* `MMP.Flips.isCartierAt_of_forall_ord_eq`: `D` is Cartier at `x` if some `φ ∈ K(X)^×` has
  `ord_E φ = D_E` along every prime divisor `E` through `x`.
* `MMP.Flips.exists_primeDivisorFromSpecStalk_eq`: through
  `MMP.Flips.primeDivisorFromSpecStalk`, the prime divisors of `Spec 𝒪_{X,x}` are the prime
  divisors of `X` through `x`.
* `MMP.Flips.isCartierAt_of_mk_stalkWeilDivisor_eq_zero`: `D` is Cartier at `x` if its pull-back
  to `Spec 𝒪_{X,x}` has zero class in `Cl(Spec 𝒪_{X,x})`; in particular
  (`MMP.Flips.isCartierAt_smul_of_nsmul_eq_zero_weilDivisorClassGroup_stalk`) `mD` is Cartier at
  `x` for every `D` if `Cl(Spec 𝒪_{X,x})` is killed by `m`.
* `MMP.Flips.IndexOneCoverData.principalDivisor_add_smul_nonneg`: `div(φ) + mD|_U ≥ 0`.

## Implementation notes

The index-one cover is the cyclic cover `MMP.Mori.DivisorialCyclicCover.cover` of
`(D|_U, m, φ)`: the equality `mD|_U + div(φ) = 0` gives the effectivity `div(φ) + mD|_U ≥ 0`
that the cyclic cover needs. The cover lives over the open subscheme `U`, so `φ` is a rational
function of `U`; for `X` integral, `K(U) = K(X)`.

The class group of `Spec 𝒪_{X,x}` is `AlgebraicGeometry.weilDivisorClassGroup`, whose Weil
divisors are locally finite coefficient families and whose principal divisors use the order of
vanishing `AlgebraicGeometry.Scheme.ord`; on `X` divisors are finitely supported and orders are
those of the discrete valuations `MMP.Mori.PrimeDivisor.ord`. The two orders agree on a normal
integral scheme (`MMP.Positivity.exists_units_of_ne_zero`).

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 16.3
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 5.19
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Flips

open MMP.Mori

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]

/-! ### The Cartier index at a point -/

/-- A Weil divisor `D` is *Cartier at* a point `x` if its restriction `D|_U` to some open
neighbourhood `U` of `x` is Cartier. -/
@[mmp "def_fa16a_index_one_cover"]
def IsCartierAt (D : Divisor X) (x : X) : Prop :=
  ∃ U : X.Opens, x ∈ U ∧ Divisor.IsCartier (D.restrictOpen U)

/-- A Weil divisor `D` is *`ℚ`-Cartier at* `x` if some positive multiple `mD` is Cartier at
`x`. -/
@[mmp "def_fa16a_index_one_cover"]
def IsQCartierAt (D : Divisor X) (x : X) : Prop :=
  ∃ m : ℕ, 0 < m ∧ IsCartierAt (m • D) x

open Classical in
/-- The *(rational) Cartier index* of a Weil divisor `D` at a point `x` where it is
`ℚ`-Cartier: the least `m ≥ 1` such that `mD` is Cartier at `x`. -/
@[mmp "def_fa16a_index_one_cover"]
def cartierIndexAt (D : Divisor X) (x : X) (h : IsQCartierAt D x) : ℕ :=
  Nat.find h

/-- The Cartier index of `D` at `x` is positive. -/
theorem cartierIndexAt_pos {D : Divisor X} {x : X} (h : IsQCartierAt D x) :
    0 < cartierIndexAt D x h := by
  classical
  exact (Nat.find_spec h).1

/-- The multiple of `D` by its Cartier index at `x` is Cartier at `x`. -/
theorem isCartierAt_cartierIndexAt_smul {D : Divisor X} {x : X} (h : IsQCartierAt D x) :
    IsCartierAt (cartierIndexAt D x h • D) x := by
  classical
  exact (Nat.find_spec h).2

/-- The Cartier index of `D` at `x` is at most every positive `m` such that `mD` is Cartier
at `x`. -/
theorem cartierIndexAt_le {D : Divisor X} {x : X} (h : IsQCartierAt D x) {m : ℕ} (hm : 0 < m)
    (hmD : IsCartierAt (m • D) x) : cartierIndexAt D x h ≤ m := by
  classical
  exact Nat.find_min' h ⟨hm, hmD⟩

/-- The Cartier index of `D` at `x` is nonzero. -/
instance {D : Divisor X} {x : X} (h : IsQCartierAt D x) : NeZero (cartierIndexAt D x h) :=
  ⟨(cartierIndexAt_pos h).ne'⟩

/-! ### A local criterion for Cartierness -/

section Criterion

variable [IsIntegral X]

/-- A divisor with a local equation on an open neighbourhood `V` of `x` is Cartier at `x`. -/
theorem isCartierAt_of_isLocalEquation {D : Divisor X} {V : X.Opens} {x : X} (hx : x ∈ V)
    {φ : (RationalFunctions X)ˣ} (hφ : D.IsLocalEquation V φ) : IsCartierAt D x := by
  have : Nonempty V := ⟨⟨x, hx⟩⟩
  have : IsDominant V.ι := Opens.isDominant_ι (V.isOpen.dense ⟨x, hx⟩)
  refine ⟨V, hx, fun y => ?_⟩
  obtain ⟨g, hg, hφg⟩ := MMP.Positivity.exists_ord_eq_of_units φ
  obtain ⟨φ', hφ'⟩ := MMP.Positivity.exists_units_of_ne_zero
    ((map_ne_zero (functionFieldMap V.ι)).2 hg)
  refine ⟨⊤, trivial, φ', fun W _ => ?_⟩
  have hW : ((OpenWeilRestriction.primeDivisorMap V.ι W).support ∩ V).Nonempty := by
    rw [← MMP.Mori.PrimeDivisor.genericPoint_mem_iff]
    exact (congrArg (· ∈ V) (OpenWeilRestriction.genericPoint_primeDivisorMap V.ι W)).mpr
      W.genericPoint.2
  rw [DivisorWithCoeffs.coeff_restrictOpen, hφ _ hW, hφg, hφ',
    MMP.Positivity.ord_functionFieldMap_of_isIso V.ι W _
      (OpenWeilRestriction.genericPoint_primeDivisorMap _ _).symm]

/-- A unit `φ` of `K(X)` has nonzero order along only finitely many prime divisors meeting an
affine open `W`. -/
private theorem finite_ord_ne_zero_of_isAffineOpen {W : X.Opens} (hW : IsAffineOpen W)
    (φ : (RationalFunctions X)ˣ) :
    {E : Mori.PrimeDivisor X | (E.support ∩ (W : Set X)).Nonempty ∧ E.ord φ ≠ 0}.Finite := by
  rcases (W : Set X).eq_empty_or_nonempty with hne | ⟨w, hw⟩
  · convert Set.finite_empty
    ext E
    simp [hne]
  have : Nonempty W := ⟨⟨w, hw⟩⟩
  have : IsDominant W.ι := Opens.isDominant_ι (W.isOpen.dense ⟨w, hw⟩)
  have : CompactSpace W := isCompact_iff_compactSpace.mp hW.isCompact
  obtain ⟨g, hg, hφg⟩ := MMP.Positivity.exists_ord_eq_of_units φ
  obtain ⟨φ', hφ'⟩ := MMP.Positivity.exists_units_of_ne_zero
    ((map_ne_zero (functionFieldMap W.ι)).2 hg)
  refine ((finite_ord_ne_zero φ').image (OpenWeilRestriction.primeDivisorMap W.ι)).subset ?_
  rintro (E : Mori.PrimeDivisor X) ⟨hEW, hE⟩
  have hη : E.genericPoint ∈ Set.range W.ι.base := by
    rw [W.range_ι]
    exact (Mori.PrimeDivisor.genericPoint_mem_iff E W).2 hEW
  obtain ⟨E', rfl⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff W.ι E).2 hη
  refine ⟨E', ?_, rfl⟩
  change Mori.PrimeDivisor.ord E' φ' ≠ 0
  rwa [hφ', MMP.Positivity.ord_functionFieldMap_of_isIso W.ι E' _
    (OpenWeilRestriction.genericPoint_primeDivisorMap _ _).symm, ← hφg]

/-- If the orders of `φ` agree with the coefficients of `D` along every prime divisor through
`x`, then `φ` is a local equation of `D` on some open neighbourhood of `x`. -/
theorem exists_isLocalEquation_of_forall_ord_eq {D : Divisor X} {x : X}
    (φ : (RationalFunctions X)ˣ)
    (h : ∀ E : Mori.PrimeDivisor X, x ∈ E.support → D.coeff E = E.ord φ) :
    ∃ V : X.Opens, x ∈ V ∧ D.IsLocalEquation V φ := by
  obtain ⟨W, hW, hxW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  set Bad :=
    {E : Mori.PrimeDivisor X | (E.support ∩ (W : Set X)).Nonempty ∧ D.coeff E ≠ E.ord φ}
  have hfin : Bad.Finite := by
    refine ((D.support.finite_toSet).union (finite_ord_ne_zero_of_isAffineOpen hW φ)).subset ?_
    rintro E ⟨hEW, hE⟩
    by_cases h0 : E.ord φ = 0
    · exact Or.inl (Finsupp.mem_support_iff.mpr (h0 ▸ hE))
    · exact Or.inr ⟨hEW, h0⟩
  have hZ : IsClosed (⋃ E ∈ Bad, E.support) :=
    hfin.isClosed_biUnion fun E _ => E.idealSheaf.support.isClosed
  refine ⟨W ⊓ ⟨_, hZ.isOpen_compl⟩, ⟨hxW, fun hxZ => ?_⟩, fun E hE => ?_⟩
  · obtain ⟨E, hE, hxE⟩ := Set.mem_iUnion₂.mp hxZ
    exact hE.2 (h E hxE)
  · by_contra hne
    obtain ⟨y, hyE, hyW, hyZ⟩ := hE
    exact hyZ (Set.mem_biUnion ⟨⟨y, hyE, hyW⟩, hne⟩ hyE)

/-- **A local criterion for Cartierness.** If some unit `φ` of `K(X)` has order `D_E` along every
prime divisor `E` through `x`, then `D` is Cartier at `x`. -/
theorem isCartierAt_of_forall_ord_eq {D : Divisor X} {x : X} (φ : (RationalFunctions X)ˣ)
    (h : ∀ E : Mori.PrimeDivisor X, x ∈ E.support → D.coeff E = E.ord φ) : IsCartierAt D x :=
  have ⟨_, hx, hφ⟩ := exists_isLocalEquation_of_forall_ord_eq φ h
  isCartierAt_of_isLocalEquation hx hφ

end Criterion

/-! ### Prime divisors through a point and the local scheme -/

section Stalk

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- `Spec 𝒪_{X,x} ⟶ X` is dominant: its image, the generizations of `x`, contains the generic
point. -/
private theorem isDominant_fromSpecStalk [IrreducibleSpace X] (x : X) :
    IsDominant (X.fromSpecStalk x) := by
  refine ⟨Dense.mono ?_ (dense_iff_closure_eq.mpr (genericPoint_spec X))⟩
  rintro _ rfl
  rw [Scheme.range_fromSpecStalk]
  exact genericPoint_specializes x

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- The prime divisor of `X` whose generic point is the image of that of a prime divisor `Z` of
`Spec 𝒪_{X,x}` under `Spec 𝒪_{X,x} ⟶ X`, which preserves coheights. -/
def primeDivisorFromSpecStalk (x : X) (Z : Mori.PrimeDivisor (Spec (X.presheaf.stalk x))) :
    Mori.PrimeDivisor X :=
  .ofCoheightOne (X.fromSpecStalk x Z.genericPoint) <| by
    rw [Stacks.Chow.coheight_fromSpecStalk_eq_height, idealHeight_eq_coheight]
    exact Z.coheight_genericPoint

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- The generic point of `primeDivisorFromSpecStalk x Z` is the image of the generic point of `Z`
under `Spec 𝒪_{X,x} ⟶ X`. -/
theorem genericPoint_primeDivisorFromSpecStalk (x : X)
    (Z : Mori.PrimeDivisor (Spec (X.presheaf.stalk x))) :
    (primeDivisorFromSpecStalk x Z).genericPoint = X.fromSpecStalk x Z.genericPoint :=
  AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- Distinct prime divisors of `Spec 𝒪_{X,x}` give distinct prime divisors of `X`. -/
theorem primeDivisorFromSpecStalk_injective (x : X) :
    Function.Injective (primeDivisorFromSpecStalk x) := fun Z Z' h =>
  AlgebraicGeometry.PrimeDivisor.genericPoint_injective <|
    (X.fromSpecStalk x).isEmbedding.injective <| by
      rw [← genericPoint_primeDivisorFromSpecStalk, ← genericPoint_primeDivisorFromSpecStalk, h]

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- Every prime divisor of `X` through `x` comes from a prime divisor of `Spec 𝒪_{X,x}`. -/
theorem exists_primeDivisorFromSpecStalk_eq {x : X} {E : Mori.PrimeDivisor X}
    (hx : x ∈ E.support) : ∃ Z, primeDivisorFromSpecStalk x Z = E := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure] at hx
  obtain ⟨p, hp⟩ := Stacks.Chow.exists_fromSpecStalk_eq hx
  have hco : Order.coheight p = 1 := by
    rw [← idealHeight_eq_coheight, ← Stacks.Chow.coheight_fromSpecStalk_eq_height, hp]
    exact E.coheight_genericPoint
  refine ⟨.ofCoheightOne p hco, AlgebraicGeometry.PrimeDivisor.genericPoint_injective <|
    (genericPoint_primeDivisorFromSpecStalk x _).trans <|
      (congrArg _ (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne p hco)).trans hp⟩

omit [IsNormal X] in
/-- The pull-back of a Weil divisor `D` on `X` to `Spec 𝒪_{X,x}`: its coefficient along a prime
divisor `Z` is that of `D` along `primeDivisorFromSpecStalk x Z`. -/
def stalkWeilDivisor (x : X) : Divisor X →+ WeilDivisor (Spec (X.presheaf.stalk x)) where
  toFun D := ⟨fun Z => D.coeff (primeDivisorFromSpecStalk x Z), by
    rw [mem_weilDivisor_iff_finite_support]
    exact (D.support.finite_toSet.preimage (primeDivisorFromSpecStalk_injective x).injOn).subset
      fun Z hZ => Finsupp.mem_support_iff.mpr hZ⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The coefficient of `stalkWeilDivisor x D` along `Z` is that of `D` along
`primeDivisorFromSpecStalk x Z`. -/
@[simp]
theorem stalkWeilDivisor_apply (x : X) (D : Divisor X)
    (Z : Mori.PrimeDivisor (Spec (X.presheaf.stalk x))) :
    (stalkWeilDivisor x D).val Z = D.coeff (primeDivisorFromSpecStalk x Z) :=
  rfl

variable [IsIntegral X]

/-- **Cartierness from the local scheme.** If the pull-back of `D` to `Spec 𝒪_{X,x}` has zero
class in `Cl(Spec 𝒪_{X,x})`, then `D` is Cartier at `x`. -/
theorem isCartierAt_of_mk_stalkWeilDivisor_eq_zero {D : Divisor X} {x : X}
    (h : (stalkWeilDivisor x D : weilDivisorClassGroup (Spec (X.presheaf.stalk x))) = 0) :
    IsCartierAt D x := by
  set j := X.fromSpecStalk x
  have := IsNormal.stalk_normal x
  have : IsNormal (Spec (X.presheaf.stalk x)) :=
    isNormal_spec_of_isIntegrallyClosed (X.presheaf.stalk x)
  have : IsDominant j := isDominant_fromSpecStalk x
  obtain ⟨f, hf⟩ := (mk_eq_zero_iff _ _).mp h
  set e := (Stacks.Chow.rationalFunctionsEquivFunctionField (Spec (X.presheaf.stalk x))).val
  have hbij : Function.Bijective (functionFieldMap j) := by
    have := isIso_stalkMap_fromSpecStalk x (genericPoint (Spec (X.presheaf.stalk x)))
    exact ConcreteCategory.bijective_of_isIso
      ((X.presheaf.stalkCongr (Inseparable.of_eq (map_genericPoint_of_isDominant j).symm)).hom ≫
        j.stalkMap _)
  obtain ⟨g, hg⟩ := hbij.2 (e f)
  have hg0 : g ≠ 0 := fun h0 => (f.isUnit.map e.toRingHom).ne_zero <| by
    change e f = 0
    rw [← hg, h0, map_zero]
  obtain ⟨φ, hφ⟩ := MMP.Positivity.exists_units_of_ne_zero hg0
  refine isCartierAt_of_forall_ord_eq φ fun E hxE => ?_
  obtain ⟨Z, rfl⟩ := exists_primeDivisorFromSpecStalk_eq hxE
  have := isIso_stalkMap_fromSpecStalk x Z.genericPoint
  rw [hφ, ← MMP.Positivity.ord_functionFieldMap_of_isIso j Z _
    (genericPoint_primeDivisorFromSpecStalk x Z).symm, hg, ← stalkWeilDivisor_apply, ← hf,
    principalDivisor_apply]

/-- **Cartier multiples from a torsion local class group.** If `Cl(Spec 𝒪_{X,x})` is killed by
`m`, then `mD` is Cartier at `x` for every Weil divisor `D` on `X`. -/
theorem isCartierAt_smul_of_nsmul_eq_zero_weilDivisorClassGroup_stalk (x : X) (m : ℕ)
    (hm : ∀ c : weilDivisorClassGroup (Spec (X.presheaf.stalk x)), m • c = 0) (D : Divisor X) :
    IsCartierAt (m • D) x :=
  isCartierAt_of_mk_stalkWeilDivisor_eq_zero <| by
    rw [map_nsmul, QuotientAddGroup.mk_nsmul]
    exact hm _

end Stalk

/-! ### The index-one cover -/

/-- *Index-one cover data* of a Weil divisor `D` at a point `x` (any scheme point) where `D` is
`ℚ`-Cartier of index `m`: an affine open neighbourhood `U` of `x` and a unit `φ` of `K(U)` with
`mD|_U + div(φ) = 0`. -/
@[mmp "def_fa16a_index_one_cover"]
structure IndexOneCoverData (D : Divisor X) (x : X) (h : IsQCartierAt D x) where
  /-- The affine open neighbourhood `U` of `x`. -/
  U : X.affineOpens
  /-- `x` lies in `U`. -/
  mem : x ∈ U.1
  /-- The trivialization `φ ∈ K(U)^×` of `mD|_U`. -/
  φ : (RationalFunctions U.1.toScheme)ˣ
  /-- The trivialization identity `mD|_U + div(φ) = 0`, `m` the Cartier index of `D` at `x`. -/
  smul_restrictOpen_add_principalDivisor :
    cartierIndexAt D x h • D.restrictOpen U.1 + Mori.principalDivisor φ = 0

namespace IndexOneCoverData

variable {D : Divisor X} {x : X} {h : IsQCartierAt D x} (c : IndexOneCoverData D x h)

/-- `div(φ) + mD|_U ≥ 0`, the effectivity the cyclic cover of `(D|_U, m, φ)` requires. -/
theorem principalDivisor_add_smul_nonneg :
    0 ≤ Mori.principalDivisor c.φ + cartierIndexAt D x h • D.restrictOpen c.U.1 := by
  rw [add_comm, c.smul_restrictOpen_add_principalDivisor]

/-- **The index-one cover** `Z = Spec_U (⊕_{i=0}^{m-1} 𝒪_U(-iD))` of `D` at `x`: the cyclic
cover defined by `(D|_U, m, φ)`, with multiplication `(a eᵢ)(b eⱼ) = ab eᵢ₊ⱼ` for `i + j < m`
and `= φab eᵢ₊ⱼ₋ₘ` for `i + j ≥ m`. -/
@[mmp "def_fa16a_index_one_cover"]
abbrev cover : Scheme.{u} :=
  DivisorialCyclicCover.cover (cartierIndexAt D x h) (D.restrictOpen c.U.1)
    c.principalDivisor_add_smul_nonneg

/-- The structure morphism `Z → U` of the index-one cover. -/
@[mmp "def_fa16a_index_one_cover"]
abbrev toBase : c.cover ⟶ c.U.1.toScheme :=
  DivisorialCyclicCover.toBase (cartierIndexAt D x h) (D.restrictOpen c.U.1)
    c.principalDivisor_add_smul_nonneg

/-- **The action of `μ_m` on the index-one cover**: for an `m`-th root of unity `ζ` among the
units of `Γ(U, 𝒪_U)`, the automorphism of `Z` acting by `ζⁱ` on the degree-`i` summand
`𝒪_U(-iD)`. -/
@[mmp "def_fa16a_index_one_cover"]
abbrev scalingIso {ζ : Γ(c.U.1.toScheme, ⊤)ˣ} (hζ : ζ ^ cartierIndexAt D x h = 1) :
    c.cover ≅ c.cover :=
  DivisorialCyclicCover.scalingIso (cartierIndexAt D x h) (D.restrictOpen c.U.1)
    c.principalDivisor_add_smul_nonneg hζ

end IndexOneCoverData

end MMP.Flips
