module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Morphisms.Birational.Transform
public import MMP.AlgebraicGeometry.Divisor.Principal
public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import StacksFrontier.AlgebraicGeometry.FunctionField.DominantMap

/-!
# Divisorial valuations, divisors over a variety and their centers

Let `Y` be a normal variety and `E ⊆ Y` a prime divisor, with generic point `η_E`. The local
ring `𝒪_{Y,E} = 𝒪_{Y,η_E}` is a discrete valuation ring with fraction field the function field
`k(Y)`, and the *valuation of `E`* is the valuation `v_E` of `k(Y)` defined by this discrete
valuation ring; its valuation ring is `𝒪_{Y,E}`. Through a birational (more generally, a
dominant) morphism `f : Y ⟶ X` of integral schemes, `k(X)` embeds into `k(Y)`, and `v_E` is
regarded as a valuation of `k(X)`.

A *divisor over* a variety `X` is a triple `(Y, f, E)` with `f : Y ⟶ X` a (not necessarily
proper) birational morphism from a normal variety `Y` and `E ⊆ Y` a prime divisor. Its valuation
is `v_E`, regarded as a valuation of `k(X)`, and two divisors over `X` with the same valuation
are identified. A divisor over `X` is *exceptional* if `E` is `f`-exceptional, and every prime
divisor `D` of a normal variety `X` is a divisor over `X`, as `(X, 𝟙_X, D)`. The *center* of a
divisor `(Y, f, E)` over `X` is the irreducible closed subset `closure (f(E))` of `X`, the closure
of the point `f(η_E)`.

## Main definitions

* `MMP.Mori.PrimeDivisor.divisorialValuation`: the valuation `v_E` of `k(Y)` along a prime
  divisor `E`, with `MMP.Mori.PrimeDivisor.valuationOver` the same valuation regarded as a
  valuation of `k(X)` through a dominant morphism `Y ⟶ X`.
* `MMP.Mori.DivisorOver`: divisors `(Y, f, E)` over `X`, with their valuation
  `MMP.Mori.DivisorOver.valuation`, the identification `MMP.Mori.DivisorOver.valuationSetoid`
  and the type `MMP.Mori.DivisorOverClass` of divisors over `X` up to it.
* `MMP.Mori.DivisorOver.IsExceptional`: exceptional divisors over `X`.
* `MMP.Mori.DivisorOver.ofPrimeDivisor`: a prime divisor of a normal variety as a divisor over it.
* `MMP.Mori.DivisorOver.center`: the center `center_X E`.

## Main results

* `MMP.Mori.IsBirationalMorphism.isDominant`: a birational morphism is dominant.
* `MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff`: the valuation ring of `v_E` is
  `𝒪_{Y,E}`.
* `MMP.Mori.PrimeDivisor.divisorialValuation_eq_inv_ordHom`,
  `MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord`: `v_E` is the order of vanishing
  along `E`, `AlgebraicGeometry.Scheme.ord`, written multiplicatively.
* `MMP.Mori.DivisorOver.center_eq_closure_genericPoint`: the center is the closure of `f(η_E)`.

## Implementation notes

The valuation is a `Valuation (k(Y)) ℤᵐ⁰` in Mathlib's multiplicative convention: an element of
order `n` along `E` has valuation `exp (-n)`, so the valuation ring is `{g | v_E(g) ≤ 1}`. It is
the adic valuation of the discrete valuation ring `𝒪_{Y,E}` at its maximal ideal, and it is the
inverse of Mathlib's order of vanishing `AlgebraicGeometry.Scheme.ordHom`. It is defined for any
locally Noetherian normal integral scheme `Y`.

Kollár and Mori identify two divisors over `X` with the same valuation. Here the triples are the
terms of `MMP.Mori.DivisorOver`, and the identification is the kernel of
`MMP.Mori.DivisorOver.valuation`, with quotient `MMP.Mori.DivisorOverClass`.

The variety structure of `Y` is the composite `f ≫ s_X` with the structure morphism `s_X` of
`X`, which makes `f` a morphism of `k`-schemes. The type of divisors over `X` is defined for every
`k`-scheme `X`; that `X` is a variety is used where it is needed (the valuation needs `X`
integral, and a prime divisor of `X` is a divisor over `X` when `X` is a normal variety). The
valuation over `X` is defined through any dominant morphism; a birational morphism is dominant.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Remark 2.23,
  Definition 2.24
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Order
open scoped WithZero

universe u

namespace MMP.Mori

/-! ### Birational morphisms are dominant -/

/-- A birational morphism is dominant. -/
theorem IsBirationalMorphism.isDominant {X Y : Scheme.{u}} {f : Y ⟶ X}
    (hf : IsBirationalMorphism f) : IsDominant f := by
  obtain ⟨e, he⟩ := hf
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff] at he
  obtain ⟨W, hW, hWe, hWf, h⟩ := he
  have hWe' : W ≤ e.source := hWe
  have h₁ : IsDominant (Y.homOfLE hWe') := by
    have : IsDominant (Y.homOfLE hWe' ≫ e.source.ι) := by
      rw [Scheme.homOfLE_ι]; exact Opens.isDominant_ι hW
    exact IsDominant.of_comp_of_isOpenImmersion (Y.homOfLE hWe') e.source.ι
  have := Opens.isDominant_ι e.dense_target
  have h₂ : IsDominant (e.toPartialMap.restrict W hW hWe).hom :=
    inferInstanceAs (IsDominant (Y.homOfLE hWe' ≫ _ ≫ _))
  rw [h] at h₂
  have hWf' : W ≤ ⊤ := le_top
  have h₃ : IsDominant ((Y.homOfLE hWf' ≫ Y.topIso.hom) ≫ f) := by
    rw [Category.assoc]; exact h₂
  exact IsDominant.of_comp (Y.homOfLE hWf' ≫ Y.topIso.hom) f

/-! ### The valuation of a prime divisor -/

namespace PrimeDivisor

section Valuation

variable {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
  (E : PrimeDivisor Y)

/-- The *valuation* `v_E = v(E, Y)` of the function field `k(Y)` of a normal integral scheme
along a prime divisor `E`: the valuation of the discrete valuation ring `𝒪_{Y,E} ⊆ k(Y)`, whose
valuation ring is `𝒪_{Y,E}` (`MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff`). In
Mathlib's multiplicative convention an element of order `n` along `E` has valuation `exp (-n)`
(`MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord`). -/
@[mmp "def_km2b_divisorial_valuation"]
def divisorialValuation : Valuation Y.functionField ℤᵐ⁰ :=
  haveI := E.isDiscreteValuationRing_localRing
  (IsDiscreteValuationRing.maximalIdeal E.localRing).valuation Y.functionField

/-- On a discrete valuation ring every height one prime is the maximal ideal. -/
private theorem heightOneSpectrum_eq_maximalIdeal {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (w : IsDedekindDomain.HeightOneSpectrum R) :
    w = IsDiscreteValuationRing.maximalIdeal R :=
  IsDedekindDomain.HeightOneSpectrum.ext (IsLocalRing.eq_maximalIdeal w.isMaximal)

/-- The valuation ring of `v_E` is the local ring `𝒪_{Y,E}`: a rational function `g` has
`v_E(g) ≤ 1` exactly when it lies in `𝒪_{Y,E} ⊆ k(Y)`. -/
@[mmp "def_km2b_divisorial_valuation"]
theorem divisorialValuation_le_one_iff (g : Y.functionField) :
    E.divisorialValuation g ≤ 1 ↔ g ∈ (algebraMap E.localRing Y.functionField).range := by
  have := E.isDiscreteValuationRing_localRing
  refine ⟨fun hg => ?_, ?_⟩
  · exact IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
      Y.functionField g fun w => by
        rw [heightOneSpectrum_eq_maximalIdeal (R := E.localRing) w]; exact hg
  · rintro ⟨r, rfl⟩
    exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ r

/-- The maximal ideal of `𝒪_{Y,E}` is the set of `r` with `v_E(r) < 1`. -/
theorem divisorialValuation_algebraMap_lt_one_iff (r : E.localRing) :
    E.divisorialValuation (algebraMap E.localRing Y.functionField r) < 1 ↔
      r ∈ IsLocalRing.maximalIdeal E.localRing := by
  have := E.isDiscreteValuationRing_localRing
  exact IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem _ r

/-- `v_E` is the inverse of Mathlib's order of vanishing along `E`,
`AlgebraicGeometry.Scheme.ordHom`, which takes the value `exp n` on an element of order `n`. -/
theorem divisorialValuation_eq_inv_ordHom (g : Y.functionField) :
    E.divisorialValuation g = (Y.ordHom E.genericPoint E.coheight_genericPoint g)⁻¹ := by
  have := E.isDiscreteValuationRing_localRing
  have : Ring.KrullDimLE 1 E.localRing := krullDimLE_of_coheight_le E.coheight_genericPoint.le
  change _ = (Ring.ordFrac E.localRing g)⁻¹
  rw [Ring.ordFrac_eq_valuation_inv, inv_inv]
  rfl

/-- A nonzero rational function of order `n = AlgebraicGeometry.Scheme.ord g η_E` along `E` has
valuation `v_E(g) = exp (-n)`. -/
theorem divisorialValuation_eq_exp_neg_ord {g : Y.functionField} (hg : g ≠ 0) :
    E.divisorialValuation g = WithZero.exp (-Y.ord g E.genericPoint) := by
  rw [divisorialValuation_eq_inv_ordHom,
    (Scheme.ord_eq_iff E.coheight_genericPoint hg).mp rfl, WithZero.exp_neg]
  rfl

/-- `v_E` is normalized: a uniformizer `ϖ` of `𝒪_{Y,E}` has `v_E(ϖ) = exp (-1)`. -/
theorem divisorialValuation_algebraMap_of_irreducible {ϖ : E.localRing} (hϖ : Irreducible ϖ) :
    E.divisorialValuation (algebraMap E.localRing Y.functionField ϖ) = WithZero.exp (-1) := by
  have := E.isDiscreteValuationRing_localRing
  have : Ring.KrullDimLE 1 E.localRing := krullDimLE_of_coheight_le E.coheight_genericPoint.le
  rw [divisorialValuation_eq_inv_ordHom, WithZero.exp_neg,
    ← Ring.ordFrac_irreducible (K := Y.functionField) hϖ]
  rfl

variable {X : Scheme.{u}} [IsIntegral X]

/-- The valuation `v_E` of `k(Y)`, for a dominant morphism `f : Y ⟶ X` of integral schemes (for
instance a birational one, `MMP.Mori.IsBirationalMorphism.isDominant`), regarded as a valuation
of `k(X)` through the extension of function fields `f^* : k(X) → k(Y)`. -/
@[mmp "def_km2b_divisorial_valuation"]
def valuationOver (f : Y ⟶ X) [IsDominant f] : Valuation X.functionField ℤᵐ⁰ :=
  E.divisorialValuation.comap (functionFieldMap f)

/-- `v_E` over `X` sends `g ∈ k(X)` to `v_E(f^* g)`. -/
theorem valuationOver_apply (f : Y ⟶ X) [IsDominant f] (g : X.functionField) :
    E.valuationOver f g = E.divisorialValuation (functionFieldMap f g) := rfl

end Valuation

end PrimeDivisor

/-! ### Divisors over a variety -/

variable (k : Type u) [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- A *divisor over* a `k`-scheme `X` (a variety, in the source) is a triple `(Y, f, E)`, where
`f : Y ⟶ X` is a (not necessarily proper) birational morphism from a normal variety `Y` over `k`,
whose structure morphism is `f ≫ s_X`, and `E ⊆ Y` is a prime divisor. Two divisors over `X`
with the same valuation are identified by `MMP.Mori.DivisorOver.valuationSetoid`. -/
@[mmp "def_km2b_divisor_over"]
structure DivisorOver where
  /-- The normal variety `Y` on which the divisor lives. -/
  Y : Scheme.{u}
  /-- The birational morphism `f : Y ⟶ X`. -/
  f : Y ⟶ X
  /-- `Y`, with structure morphism `f ≫ s_X`, is a normal variety. -/
  isNormalVariety : IsNormalVariety k (f ≫ sX)
  /-- `f` is birational. -/
  isBirationalMorphism : IsBirationalMorphism f
  /-- The prime divisor `E ⊆ Y`. -/
  E : PrimeDivisor Y

namespace DivisorOver

variable {k sX} (D : DivisorOver k sX)

/-- The scheme `Y` of a divisor `(Y, f, E)` over `X` is integral. -/
theorem isIntegral : IsIntegral D.Y := D.isNormalVariety.1.toIsIntegral

/-- The scheme `Y` of a divisor `(Y, f, E)` over `X` is normal. -/
theorem isNormal : IsNormal D.Y := D.isNormalVariety.2

/-- The scheme `Y` of a divisor `(Y, f, E)` over `X` is locally Noetherian. -/
theorem isLocallyNoetherian : IsLocallyNoetherian D.Y :=
  haveI := D.isNormalVariety.1.toLocallyOfFiniteType
  LocallyOfFiniteType.isLocallyNoetherian (D.f ≫ sX)

/-- The morphism `f` of a divisor `(Y, f, E)` over `X` is dominant. -/
theorem isDominant : IsDominant D.f := D.isBirationalMorphism.isDominant

/-- The *valuation* `v(E, Y)` of a divisor `(Y, f, E)` over an integral scheme `X`, regarded as
a valuation of `k(X)` through the birational morphism `f`. -/
@[mmp "def_km2b_divisor_over"]
def valuation [IsIntegral X] : Valuation X.functionField ℤᵐ⁰ :=
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  D.E.valuationOver D.f

variable (k sX) in
/-- Kollár–Mori identify two divisors over `X` with the same valuation of `k(X)`: the kernel of
`MMP.Mori.DivisorOver.valuation`. -/
@[mmp "def_km2b_divisor_over"]
def valuationSetoid [IsIntegral X] : Setoid (DivisorOver k sX) :=
  Setoid.ker fun D : DivisorOver k sX => D.valuation

/-- Two divisors over `X` are related by `MMP.Mori.DivisorOver.valuationSetoid` if and only if
they have the same valuation. -/
theorem valuationSetoid_iff [IsIntegral X] {D D' : DivisorOver k sX} :
    valuationSetoid k sX D D' ↔ D.valuation = D'.valuation :=
  Iff.rfl

/-- A divisor `(Y, f, E)` over `X` is *exceptional over `X`* if `E` is `f`-exceptional. -/
@[mmp "def_km2b_divisor_over"]
def IsExceptional : Prop :=
  RationalMap.IsExceptional (X := D.Y) D.f.toRationalMap D.E

variable (k) in
/-- A prime divisor `P` of a normal variety `X` is a divisor over `X`, as `(X, 𝟙_X, P)`. -/
@[mmp "def_km2b_divisor_over"]
def ofPrimeDivisor (hX : IsNormalVariety k sX) (P : PrimeDivisor X) : DivisorOver k sX where
  Y := X
  f := 𝟙 X
  isNormalVariety := by rwa [Category.id_comp]
  isBirationalMorphism := isBirationalMorphism_of_isIso _
  E := P

/-- The prime divisor of `(X, 𝟙_X, P)` is `P`. -/
@[simp]
theorem ofPrimeDivisor_E (hX : IsNormalVariety k sX) (P : PrimeDivisor X) :
    (ofPrimeDivisor k hX P).E = P := rfl

/-! ### The center -/

/-- The image `f(E)` of the support of `E` under `f` is irreducible. -/
theorem isIrreducible_image_support : IsIrreducible (D.f '' D.E.support) := by
  rw [show (D.E.support : Set D.Y) = closure {D.E.genericPoint} from
    AlgebraicGeometry.PrimeDivisor.support_eq_closure D.E]
  exact isIrreducible_singleton.closure.image _ D.f.continuous.continuousOn

/-- The *center* `center_X E = closure (f(E))` of a divisor `(Y, f, E)` over `X`, an irreducible
closed subset of `X`; it is the closure of the point `f(η_E)`
(`MMP.Mori.DivisorOver.center_eq_closure_genericPoint`). -/
@[mmp "def_km2b_center"]
def center : IrreducibleCloseds X where
  carrier := closure (D.f '' D.E.support)
  isIrreducible' := D.isIrreducible_image_support.closure
  isClosed' := isClosed_closure

/-- The center of `(Y, f, E)` is, as a set, the closure of `f(E)`. -/
theorem coe_center : (D.center : Set X) = closure (D.f '' D.E.support) := rfl

/-- The center of `(Y, f, E)` is the closure of the image `f(η_E)` of the generic point of `E`. -/
theorem center_eq_closure_genericPoint :
    (D.center : Set X) = closure {D.f D.E.genericPoint} := by
  rw [coe_center, show (D.E.support : Set D.Y) = closure {D.E.genericPoint} from
    AlgebraicGeometry.PrimeDivisor.support_eq_closure D.E]
  refine le_antisymm ?_ (closure_mono ?_)
  · refine closure_minimal ?_ isClosed_closure
    refine (image_closure_subset_closure_image D.f.continuous).trans ?_
    rw [Set.image_singleton]
  · rw [Set.singleton_subset_iff]
    exact ⟨D.E.genericPoint, subset_closure rfl, rfl⟩

/-- `f(η_E)` is the generic point of the center of `(Y, f, E)`. -/
theorem isGenericPoint_center : IsGenericPoint (D.f D.E.genericPoint) (D.center : Set X) :=
  D.center_eq_closure_genericPoint.symm

end DivisorOver

variable [IsIntegral X]

/-- Divisors over `X`, two being identified when they have the same valuation of `k(X)`. -/
@[mmp "def_km2b_divisor_over"]
def DivisorOverClass : Type (u + 1) :=
  Quotient (DivisorOver.valuationSetoid k sX)

namespace DivisorOverClass

variable {k sX}

/-- The class of a divisor over `X`. -/
def mk (D : DivisorOver k sX) : DivisorOverClass k sX :=
  Quotient.mk (DivisorOver.valuationSetoid k sX) D

/-- Every class of divisors over `X` is the class of a divisor over `X`. -/
theorem mk_surjective : Function.Surjective (mk (k := k) (sX := sX)) :=
  Quotient.mk_surjective

/-- The valuation of `k(X)` of a class of divisors over `X`. -/
def valuation (D : DivisorOverClass k sX) : Valuation X.functionField ℤᵐ⁰ :=
  Quotient.lift (s := DivisorOver.valuationSetoid k sX) (·.valuation) (fun _ _ h => h) D

/-- The valuation of the class of `D` is the valuation of `D`. -/
@[simp]
theorem valuation_mk (D : DivisorOver k sX) : (mk D).valuation = D.valuation := rfl

/-- Two divisors over `X` have the same class if and only if they have the same valuation. -/
@[simp]
theorem mk_eq_mk_iff {D D' : DivisorOver k sX} :
    mk D = mk D' ↔ D.valuation = D'.valuation :=
  ⟨Quotient.exact (s := DivisorOver.valuationSetoid k sX),
    Quotient.sound (s := DivisorOver.valuationSetoid k sX)⟩

/-- A class of divisors over `X` is determined by its valuation. -/
theorem valuation_injective : Function.Injective (valuation (k := k) (sX := sX)) :=
  Setoid.kerLift_injective _

end DivisorOverClass

end MMP.Mori
