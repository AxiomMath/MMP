module

public import MMP.AlgebraicGeometry.Singularities.Snc.Basic
public import MMP.AlgebraicGeometry.Morphisms.Birational.RationalMap
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective

/-!
# Exceptional loci, resolutions and log resolutions (Lazarsfeld §4.1, §9.1)

Let `μ : X' ⟶ X` be a birational morphism of varieties over a field `k`.

* The *exceptional locus* `Exc(μ) ⊆ X'` is the set of points `x'` with no open neighbourhood `U`
  such that `μ(U)` is open in `X` and `μ|_U : U → μ(U)` is an isomorphism (Lazarsfeld §4.1.A).
* For `X'` normal, the *exceptional divisor* `except(μ)` is the reduced divisor `∑ E` over the
  prime divisors `E ⊆ Exc(μ)` (Lazarsfeld Def. 9.1.10).
* A *resolution of singularities* of `X` is a projective birational morphism from a non-singular
  variety; an *embedded* (*log*) *resolution* of an effective Cartier divisor `D` is a resolution
  whose exceptional locus is empty or of pure codimension one, such that `D' + E_μ` has SNC
  support for a pull-back `D'` of `D` and the reduced divisor `E_μ` with support `Exc(μ)`
  (Lazarsfeld Thm. 4.1.3).
* A *log resolution* of an `ℝ`-divisor `D` is a projective birational morphism from a
  non-singular variety such that `μ^*D` and `except(μ)` have jointly SNC support
  (Lazarsfeld Def. 9.1.10).

## Main definitions

* `MMP.Intersection.exceptionalLocus`, `MMP.Intersection.IsExceptionalDivisorSum`.
* `MMP.Intersection.primeDivisorSubvariety`, `MMP.Intersection.IsWeilDivisorOfCartier`,
  `MMP.Intersection.IsWeilRDivisorOf`, `MMP.Intersection.IsWeilPullback`: the Weil divisor of a
  Cartier (`ℝ`-)divisor, and the Weil divisor of a pull-back.
* `MMP.Intersection.IsReducedDivisorWithSupport`, `MMP.Intersection.IsPureCodimOne`.
* `MMP.Intersection.IsResolution`, `MMP.Intersection.IsEmbeddedResolution`,
  `MMP.Intersection.IsLogResolution`.

## Implementation notes

* A *non-singular variety* over `k` with structure morphism `s` is `MMP.Mori.IsVariety k s`
  together with `MMP.Mori.IsSmoothScheme s` (smoothness over `k`; Lazarsfeld works over `ℂ`).
  The variety `X'` is a `k`-scheme through `μ ≫ s_X`. A *projective* morphism is
  `AlgebraicGeometry.IsProjectiveMorphism` (a closed immersion into some `ℙⁿ_X` over `X`,
  Hartshorne's definition, which Lazarsfeld follows); a *birational* morphism is
  `MMP.Mori.IsBirationalMorphism`.
* The condition "`μ(U)` is open and `μ|_U : U → μ(U)` is an isomorphism" says exactly that the
  composite `U ↪ X' ⟶ X` is an open immersion. The exceptional locus is taken among all scheme
  points; it is closed, so it is determined by its closed points (Lazarsfeld's "points").
* `except(μ)` is given by the predicate `IsExceptionalDivisorSum μ E`, which fixes every
  coefficient of `E` (`1` on the prime divisors contained in `Exc(μ)`, `0` elsewhere), so `E` is
  unique when it exists; no convention for an infinite set of exceptional prime divisors is
  needed.
* Divisors on `X` in the sense of Lazarsfeld Ch. 1 are Cartier divisors
  (`AlgebraicGeometry.Scheme.CartierDivisor`) and `ℝ`-divisors `Div(X) ⊗ ℝ`
  (`MMP.Intersection.RCartierDivisor`), with pull-backs relative to a representation
  (`MMP.Intersection.IsPullback`, `MMP.Intersection.CartierDivisorWithCoeffs.IsPullback`). SNC
  conditions are read on Weil divisors: the Weil divisor `[A] = ∑ ord_P(A) P` of a Cartier
  divisor `A`, the order being Lazarsfeld's (Rem. 1.1.4, `MMP.Intersection.IsOrderAlong`) along
  the subvariety underlying each prime divisor, and extended `ℝ`-linearly. "`μ^*D`" is read as
  "some pull-back `D'` of `D`" together with its Weil divisor; both are determined by `D` when
  they exist, as Lazarsfeld's notation presumes.
* "The reduced divisor `E_μ` with support `Exc(μ)`" is `IsReducedDivisorWithSupport`. A
  subset `S ⊆ X` is *empty or of pure codimension one* when every irreducible component of `S` (a
  maximal irreducible subset) is the support of a prime divisor; this holds vacuously for `S`
  empty.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry

namespace MMP.Intersection

open MMP.Mori (Divisor RDivisor DivisorWithCoeffs)

variable {k : Type u} [Field k] {X X' : Scheme.{u}}

/-! ### Exceptional loci and exceptional divisors -/

/-- **The exceptional locus** `Exc(μ) ⊆ X'` (Lazarsfeld §4.1.A): the points `x'` with no open
neighbourhood `U` such that `μ(U)` is open in `X` and `μ|_U : U → μ(U)` is an isomorphism, i.e.
such that `U ↪ X' ⟶ X` is an open immersion. -/
@[mmp "def_p04_exceptional_locus"]
def exceptionalLocus (μ : X' ⟶ X) : Set X' :=
  {x' | ¬ ∃ U : X'.Opens, x' ∈ U ∧ IsOpenImmersion (U.ι ≫ μ)}

/-- A point `x'` lies in `Exc(μ)` if and only if no open neighbourhood `U` of `x'` makes
`U ↪ X' ⟶ X` an open immersion. -/
theorem mem_exceptionalLocus_iff {μ : X' ⟶ X} {x' : X'} :
    x' ∈ exceptionalLocus μ ↔ ∀ U : X'.Opens, x' ∈ U → ¬ IsOpenImmersion (U.ι ≫ μ) := by
  simp [exceptionalLocus]

open Classical in
/-- **The exceptional divisor** `except(μ)` (Lazarsfeld Def. 9.1.10): `E` is the reduced Weil
divisor `∑ E'` over the prime divisors `E' ⊆ X'` contained in `Exc(μ)`, i.e. its coefficient is
`1` on those prime divisors and `0` on all others (so `E = 0` if there are none). -/
@[mmp "def_p09a_exceptional_divisor_sum"]
def IsExceptionalDivisorSum (μ : X' ⟶ X) (E : Divisor X') : Prop :=
  ∀ P : MMP.Mori.PrimeDivisor X', E.coeff P = if P.support ⊆ exceptionalLocus μ then 1 else 0

/-- The exceptional divisor is unique. -/
theorem IsExceptionalDivisorSum.eq {μ : X' ⟶ X} {E E' : Divisor X'}
    (h : IsExceptionalDivisorSum μ E) (h' : IsExceptionalDivisorSum μ E') : E = E' :=
  MMP.Mori.DivisorWithCoeffs.ext' fun P => (h P).trans (h' P).symm

/-! ### The Weil divisor of a Cartier divisor -/

/-- The subvariety of `X` underlying a prime divisor: its integral closed subscheme. -/
def primeDivisorSubvariety (P : MMP.Mori.PrimeDivisor X) : Scheme.Subvariety X :=
  ⟨P.idealSheaf, P.integral⟩

/-- `w` is the Weil divisor `[A] = ∑_P ord_P(A) P` of the Cartier divisor `A`: every
coefficient `w_P` is an order of `A` along `P` (Lazarsfeld Rem. 1.1.4). -/
def IsWeilDivisorOfCartier (A : X.CartierDivisor) (w : Divisor X) : Prop :=
  ∀ P : MMP.Mori.PrimeDivisor X, IsOrderAlong A (primeDivisorSubvariety P) (w.coeff P)

/-- `w` is the Weil `ℝ`-divisor `[D] = ∑ cᵢ [Aᵢ]` of the `ℝ`-divisor `D = ∑ cᵢ Aᵢ`. -/
def IsWeilRDivisorOf (D : RCartierDivisor X) (w : RDivisor X) : Prop :=
  ∃ (m : ℕ) (c : Fin m → ℝ) (A : Fin m → X.CartierDivisor) (wA : Fin m → Divisor X),
    CartierDivisorWithCoeffs.IsRepresentation D c A ∧ (∀ i, IsWeilDivisorOfCartier (A i) (wA i)) ∧
      w = ∑ i, c i • MMP.Mori.Divisor.toRDivisor (wA i)

/-- `w` is the Weil `ℝ`-divisor of the pull-back `μ^*D` of an `ℝ`-divisor `D`: for some
representation `D = ∑ cᵢ Aᵢ` and pull-back `D'` relative to it, `w = [D']`. -/
def IsWeilPullback (μ : X' ⟶ X) (D : RCartierDivisor X) (w : RDivisor X') : Prop :=
  ∃ (m : ℕ) (c : Fin m → ℝ) (A : Fin m → X.CartierDivisor) (D' : RCartierDivisor X'),
    CartierDivisorWithCoeffs.IsPullback μ D c A D' ∧ IsWeilRDivisorOf D' w

/-- `E` is the reduced divisor with support `S`. -/
@[mmp "def_p04_embedded_resolution"]
def IsReducedDivisorWithSupport (E : Divisor X) (S : Set X) : Prop :=
  IsReducedEffective E ∧ (E.supp : Set X) = S

/-- A subset `S ⊆ X` is *empty or of pure codimension one*: every irreducible component of `S`
(a maximal irreducible subset of `S`) is the support of a prime divisor. -/
@[mmp "def_p04_embedded_resolution"]
def IsPureCodimOne (S : Set X) : Prop :=
  ∀ Z : Set X, Maximal (fun W => IsIrreducible W ∧ W ⊆ S) Z →
    ∃ P : MMP.Mori.PrimeDivisor X, P.support = Z

/-! ### Resolutions -/

variable (sX : X ⟶ Spec (.of k))

/-- **A resolution of singularities** (Lazarsfeld §4.1.A) of the variety `X` (over `k` by `s_X`)
is a projective birational morphism `μ : X' ⟶ X` with `X'` a non-singular variety. -/
@[mmp "def_p04_resolution_of_singularities"]
def IsResolution (μ : X' ⟶ X) : Prop :=
  MMP.Mori.IsVariety k sX ∧ MMP.Mori.IsVariety k (μ ≫ sX) ∧
    MMP.Mori.IsSmoothScheme (μ ≫ sX) ∧ IsProjectiveMorphism μ ∧
      MMP.Mori.IsBirationalMorphism μ

/-- **An embedded (log) resolution** (Lazarsfeld Thm. 4.1.3) of an effective Cartier divisor `D`
on the variety `X`: a resolution of singularities `μ : X' ⟶ X` such that `Exc(μ)` is empty or of
pure codimension one, and such that for some pull-back `D'` of `D` the divisor `D' + E_μ` has
simple normal crossing support, `E_μ` the reduced divisor with support `Exc(μ)`. -/
@[mmp "def_p04_embedded_resolution"]
def IsEmbeddedResolution (D : X.CartierDivisor) (μ : X' ⟶ X) : Prop :=
  IsEffective D ∧ IsResolution sX μ ∧ IsPureCodimOne (exceptionalLocus μ) ∧
    ∃ (D' : X'.CartierDivisor) (wD' Eμ : Divisor X'),
      IsPullback μ D D' ∧ IsWeilDivisorOfCartier D' wD' ∧
        IsReducedDivisorWithSupport Eμ (exceptionalLocus μ) ∧ HasSNCSupport (μ ≫ sX) (wD' + Eμ)

/-- **A log resolution of an `ℝ`-divisor** `D` on `X` (Lazarsfeld Def. 9.1.10): a projective
birational morphism `μ : X' ⟶ X` from a non-singular variety `X'` such that `μ^*D` and
`except(μ)` have jointly simple normal crossing support. -/
@[mmp "def_p09a_log_resolution_divisor"]
def IsLogResolution (D : RCartierDivisor X) (μ : X' ⟶ X) : Prop :=
  IsProjectiveMorphism μ ∧ MMP.Mori.IsBirationalMorphism μ ∧ MMP.Mori.IsVariety k (μ ≫ sX) ∧
    MMP.Mori.IsSmoothScheme (μ ≫ sX) ∧
    ∃ (F : RDivisor X') (E : Divisor X'), IsWeilPullback μ D F ∧ IsExceptionalDivisorSum μ E ∧
      HasJointSNCSupport (μ ≫ sX) ![F, MMP.Mori.Divisor.toRDivisor E]

end MMP.Intersection
