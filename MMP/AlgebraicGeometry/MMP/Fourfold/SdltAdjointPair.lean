/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.AlgebraicGeometry.Singularities.Slc.NormalizedSections
public import MMP.AlgebraicGeometry.Singularities.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.Scheme

/-!
# Demi-normal adjoint pairs with dlt normalization

A *projective demi-normal adjoint pair* `(T, Δ; L)` consists of a reduced, pure-dimensional,
projective scheme `T` which is `S₂`, seminormal and has only double normal crossings in
codimension one; a rational boundary `Δ` none of whose components is a component of the double
locus; and the adjoint `L = K_T + Δ`, required to be `ℚ`-invertible. On the normalization
`ν : ⨿ᵢ Tᵢ ⟶ T` the adjoint satisfies `ν^*L|_{Tᵢ} = K_{Tᵢ} + Cᵢ + Δᵢ`, where `Cᵢ` is the reduced
conductor and `Δᵢ` the strict transform of `Δ`, and `(Tᵢ, Cᵢ + Δᵢ)` is dlt. The equality includes
the residue identification on the double locus: the two branches through a codimension-one double
point carry opposite ordinary residues, so that the residues of an `m`-canonical generator differ
by `(-1)^m`; for even `m` there is no sign. Such a pair is an *sdlt adjoint pair*.

## Main definitions

* `MMP.Fourfold.adjointBoundaryCoeff`, `MMP.Fourfold.IsAdjointBoundary`: the boundary
  `Θᵢ = Cᵢ + Δᵢ` on the normalization component `Tᵢ`.
* `MMP.Fourfold.IsLogResiduePresentation`: a presentation `s = h (dz/z ∧ dν^*a)^{⊗m}` of a rational
  `m`-canonical form along a conductor component, with ordinary residue `h̄ (dā)^{⊗m}`.
* `MMP.Fourfold.IsAdjointGeneratorOn`: a local generator of `𝒪_T(m(K_T + Δ))` on an open `U`, read
  on the normalization.
* `MMP.Fourfold.IsSdltAdjointPair`: sdlt adjoint pairs.

## Implementation notes

The source works over `ℂ`; the definitions are stated over a field `k` (the structure morphism
`sT : T ⟶ Spec k`) and specialize to the source's for `k = ℂ`. The normalization is recorded as a
`MMP.Flips.NormalizationComponents` of `T`: normal varieties `Tᵢ` with morphisms `νᵢ : Tᵢ ⟶ T`
such that `⨿ᵢ Tᵢ ⟶ T` is the normalization of `T` up to isomorphism over `T`.

The canonical divisor `K_T` of the non-normal scheme `T` is not used directly. As in the classical
description of `ω_T` of a demi-normal scheme by forms on the normalization, a rational
`m`-canonical form on `T` is a family `s = (sᵢ)ᵢ` of rational `m`-canonical forms on the `Tᵢ`
(the normalization is an isomorphism at the generic points), and `𝒪_T(m(K_T + Δ))` is the sheaf of
those `s` with `div(sᵢ) + m(Cᵢ + Δᵢ) ≥ 0` whose residues along the two branches through each
codimension-one double point `Q` are identified with the sign `(-1)^m`. That `L = K_T + Δ` is
`ℚ`-invertible with `ν^*L|_{Tᵢ} = K_{Tᵢ} + Cᵢ + Δᵢ` including the residue identification is
therefore the statement that, for some `m > 0` with `mΔ` integral, every point of `T` has an open
neighbourhood `U` with a family `s` that generates `𝒪_{Tᵢ}(m(K_{Tᵢ} + Cᵢ + Δᵢ))` on `νᵢ⁻¹(U)` for
every `i` (`MMP.Mori.GeneratesOn`) and whose residues along opposite branches over the double
points in `U` differ by `(-1)^m`, and whose residue along every conductor component over a double
point of `U` is pulled back from `T` (this is what controls a conductor component glued to itself,
which has no second branch). Seminormality and `S₂` make these local generators exactly the
local generators of an invertible sheaf on `T`, the `m`-th power of the adjoint.

The residue of an `m`-canonical form `sᵢ` with a pole of order `m` along a conductor component `P`
of `Tᵢ` is a rational `m`-canonical form on `P`. It is not given as a map; it is encoded by
presentations (`MMP.Fourfold.IsLogResiduePresentation`). Near `Q = νᵢ(P)` choose functions
`a₁, …, a_{n-1}` on `T` and a local parameter `z` of `Tᵢ` at `P` with `dā₁ ∧ ⋯ ∧ dā_{n-1} ≠ 0` in
`Ω^{n-1}_{κ(P)/k}`; then `dz/z ∧ dν^*a₁ ∧ ⋯ ∧ dν^*a_{n-1}` generates the log forms along `P`, a
form with at most a pole of order `m` along `P` is `h (dz/z ∧ dν^*a)^{⊗m}` with `h ∈ 𝒪_{Tᵢ,P}`,
and its ordinary residue is `h̄ (dā)^{⊗m}`, `h̄` the value of `h` at the generic point of `P`.
Since the `aⱼ` are functions on `T`, the forms `(dā)^{⊗m}` on the two branches `P ⊆ Tᵢ`, `P' ⊆ Tⱼ`
over `Q` are both pulled back from the same form on `κ(Q)`. Opposite residues is then the condition
that there is a function `g` on `T` near `Q` with `h̄ = ν^*ḡ` on `P` and `h̄' = (-1)^m ν^*ḡ` on
`P'`. For even `m` the condition is sign-free, as in the source. Both residues are written with
`dz/z` in the first slot, so the sign coming from the order of the factors is the same on both
branches.

## References

* [J. Kollár, *Singularities of the minimal model program*][Kollar2013], Section 5.1
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori MMP.Flips

variable {k : Type u} [Field k] {T : Scheme.{u}} {sT : T ⟶ Spec (.of k)}
  {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
  (N : NormalizationComponents sT hT)

/-! ### The boundary `Cᵢ + Δᵢ` on the normalization -/

open scoped Classical in
/-- The coefficient of a prime divisor `P` of the normalization component `Tᵢ` in
`Θᵢ = Cᵢ + Δᵢ`: the coefficient `1` of the reduced conductor `Cᵢ` if `νᵢ(P)` lies in the double
locus of `T`, plus the coefficient of `νᵢ(P)` in `Δ` (the strict transform `Δᵢ`). -/
@[mmp "def_fourfold_sdlt_adjoint_pair"]
def adjointBoundaryCoeff (Δ : QWeilDivisor T) (i : N.ι) (P : Mori.PrimeDivisor (N.X i)) : ℚ :=
  (if (N.n i).base P.genericPoint ∈ (doubleIntersectionLocus T : Set T) then 1 else 0) +
    ∑ Γ ∈ Δ.support, if (N.n i).base P.genericPoint = Γ.1.genericPoint then Δ Γ else 0

/-- `Θ` is the boundary `Cᵢ + Δᵢ` on the normalization component `Tᵢ`: the sum of the reduced
conductor `Cᵢ` (the prime divisors of `Tᵢ` lying over the double locus of `T`, with coefficient
one) and the strict transform `Δᵢ` of `Δ`, characterized by its coefficients
(`MMP.Fourfold.adjointBoundaryCoeff`). -/
@[mmp "def_fourfold_sdlt_adjoint_pair"]
def IsAdjointBoundary (Δ : QWeilDivisor T) (i : N.ι) (Θ : QDivisor (N.X i)) : Prop :=
  ∀ P, Θ.coeff P = adjointBoundaryCoeff N Δ i P

/-! ### Residues along the conductor -/

/-- **A residue presentation along a conductor component.** Let `P` be a prime divisor of the
normalization component `Tᵢ` with `νᵢ(P)` in the open `V ⊆ T`, `a₁, …, a_{n-1}` and `g` functions
on `V`, `ε` a sign and `s` a rational `m`-canonical form on `Tᵢ` (of dimension `n`). Then
`(V, a, g, ε)` *presents the residue of `s` along `P` as `ε ḡ (dā)^{⊗m}`* if there are a local
parameter `z ∈ k(Tᵢ)` at `P` (`ord_P z = 1`) and `h ∈ 𝒪_{Tᵢ,P}` with
* `s = h (dz/z ∧ dν^*a₁ ∧ ⋯ ∧ dν^*a_{n-1})^{⊗m}`;
* `dā₁ ∧ ⋯ ∧ dā_{n-1} ≠ 0` in `Ω^{n-1}_{κ(P)/k}`, `āⱼ` the value of `ν^*aⱼ` at the generic point
  of `P`;
* `h̄ = ε ν^*ḡ` in `κ(P)`.

Then `s` has a pole of order at most `m` along `P` and its ordinary residue is
`h̄ (dā)^{⊗m} = ε ν^*(ḡ (dā)^{⊗m})`. -/
@[mmp "def_fourfold_sdlt_adjoint_pair"]
def IsLogResiduePresentation (n m : ℕ) (i : N.ι) (P : Mori.PrimeDivisor (N.X i)) (V : T.Opens)
    (hP : (N.n i).base P.genericPoint ∈ V) (a : Fin (n - 1) → Γ(T, V)) (g : Γ(T, V)) (ε : ℤ)
    (s : RationalPluriForms (N.n i ≫ sT) n m) : Prop :=
  letI := functionFieldAlgebra (N.n i ≫ sT)
  letI : Algebra k ((N.X i).residueField P.genericPoint) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (N.n i ≫ sT).appTop ≫
      (N.X i).Γevaluation P.genericPoint).hom.toAlgebra
  -- the pull-back `ν^*f` of a function `f` on `V`, as a germ at the generic point of `P`
  let pull : Γ(T, V) → (N.X i).presheaf.stalk P.genericPoint := fun f =>
    (N.X i).presheaf.germ ((N.n i) ⁻¹ᵁ V) P.genericPoint hP ((N.n i).app V f)
  ∃ (z : (N.X i).functionField) (h : (N.X i).presheaf.stalk P.genericPoint),
    (N.X i).ord z P.genericPoint = 1 ∧
    s = (algebraMap _ (N.X i).functionField h •
      (PiTensorProduct.tprod (N.X i).functionField (fun _ : Fin m =>
        exteriorPower.ιMulti (N.X i).functionField n (fun j : Fin n =>
          if hj : j.val = 0 then z⁻¹ • KaehlerDifferential.D k (N.X i).functionField z
          else KaehlerDifferential.D k (N.X i).functionField
            (algebraMap _ (N.X i).functionField (pull (a ⟨j.val - 1, by omega⟩))))) :
        TensorPower (N.X i).functionField m
          (⋀[(N.X i).functionField]^n Ω[(N.X i).functionField⁄k])) :
      RationalPluriForms (N.n i ≫ sT) n m) ∧
    exteriorPower.ιMulti ((N.X i).residueField P.genericPoint) (n - 1) (fun j =>
      KaehlerDifferential.D k ((N.X i).residueField P.genericPoint)
        ((N.X i).residue P.genericPoint (pull (a j)))) ≠ 0 ∧
    (N.X i).residue P.genericPoint h = (ε : (N.X i).residueField P.genericPoint) *
      (N.X i).residue P.genericPoint (pull g)

/-- **A local generator of `𝒪_T(m(K_T + Δ))` on `U`**, read on the normalization. A family
`s = (sᵢ)ᵢ` of rational `m`-canonical forms on the components `Tᵢ` (of dimension `n`) generates
`𝒪_T(m(K_T + Δ))` on the open `U ⊆ T`, the boundaries `Θᵢ = Cᵢ + Δᵢ` given, if
* for every `i`, `sᵢ` generates `𝒪_{Tᵢ}(m(K_{Tᵢ} + Θᵢ))` on `νᵢ⁻¹(U)`
  (`MMP.Mori.GeneratesOn`): this is `ν^*L|_{Tᵢ} = K_{Tᵢ} + Cᵢ + Δᵢ` over `U` at the level of `m`-th
  powers;
* (residue identification) for any two distinct prime divisors `P ⊆ Tᵢ`, `P' ⊆ Tⱼ` of the
  normalization lying over the same point `Q ∈ U` of the double locus of `T`, there are functions
  `a₁, …, a_{n-1}`, `g` on a neighbourhood `V` of `Q` presenting the residues of `sᵢ` along `P` as
  `ḡ (dā)^{⊗m}` and of `sⱼ` along `P'` as `(-1)^m ḡ (dā)^{⊗m}`
  (`MMP.Fourfold.IsLogResiduePresentation`): opposite branches have opposite ordinary residues. -/
@[mmp "def_fourfold_sdlt_adjoint_pair"]
def IsAdjointGeneratorOn (n m : ℕ) (Θ : ∀ i, QDivisor (N.X i)) (U : T.Opens)
    (s : ∀ i, RationalPluriForms (N.n i ≫ sT) n m) : Prop :=
  (∀ i, GeneratesOn (Θ i) m ((N.n i) ⁻¹ᵁ U) (s i)) ∧
    ∀ (i j : N.ι) (P : Mori.PrimeDivisor (N.X i)) (P' : Mori.PrimeDivisor (N.X j)),
      (N.n i).base P.genericPoint = (N.n j).base P'.genericPoint →
      (N.n i).base P.genericPoint ∈ U →
      (N.n i).base P.genericPoint ∈ (doubleIntersectionLocus T : Set T) →
      (⟨i, P.genericPoint⟩ : Σ i, N.X i) ≠ ⟨j, P'.genericPoint⟩ →
      ∃ (V : T.Opens) (hP : (N.n i).base P.genericPoint ∈ V)
        (hP' : (N.n j).base P'.genericPoint ∈ V) (a : Fin (n - 1) → Γ(T, V)) (g : Γ(T, V)),
        IsLogResiduePresentation N n m i P V hP a g 1 (s i) ∧
          IsLogResiduePresentation N n m j P' V hP' a g ((-1) ^ m) (s j)

/-! ### Sdlt adjoint pairs -/

/-- **Demi-normal adjoint pairs with dlt normalization; sdlt adjoint pairs.** Let `T` be a scheme
over `k` with normalization `ν : ⨿ᵢ Tᵢ ⟶ T` (recorded by `N`), `Δ` a `ℚ`-Weil divisor on `T` and
`Θᵢ` `ℚ`-divisors on the `Tᵢ`. Then `(T, Δ; L = K_T + Δ)` is an *sdlt adjoint pair* of dimension
`n`, with `Θᵢ = Cᵢ + Δᵢ`, if
* `T` is a reduced, separated scheme of finite type over `k` of pure dimension `n`
  (`MMP.Flips.IsNFold`), projective over `k`, `S₂`, seminormal, and has only double normal
  crossings in codimension one (`MMP.Flips.IsNcInCodimOne`);
* `Δ` is a boundary (coefficients in `[0, 1]`) none of whose components lies in the double locus
  `D` of `T`, i.e. whose support contains no component of the conductor;
* `Θᵢ` is the sum of the reduced conductor `Cᵢ` and the strict transform `Δᵢ` of `Δ`
  (`MMP.Fourfold.IsAdjointBoundary`), and `(Tᵢ, Θᵢ)` is dlt for some canonical divisor `K_{Tᵢ}`;
* the adjoint `L = K_T + Δ` is `ℚ`-invertible with `ν^*L|_{Tᵢ} = K_{Tᵢ} + Cᵢ + Δᵢ`, including the
  residue identification: there is `m > 0` with `mΔ` integral such that every point of `T` has an
  open neighbourhood `U` carrying a local generator of `𝒪_T(m(K_T + Δ))`
  (`MMP.Fourfold.IsAdjointGeneratorOn`), whose residues along opposite branches over the double
  locus differ by `(-1)^m`, and whose residue along every conductor component `P ⊆ Tᵢ` over a
  double point of `U` is pulled back from `T`: it is presented as `ḡ (dā)^{⊗m}` with `a`, `g`
  functions on `T` (`MMP.Fourfold.IsLogResiduePresentation` with sign `1`).

The last clause is not implied by the residue clause of `MMP.Fourfold.IsAdjointGeneratorOn`, which
only compares distinct branches and so says nothing along a conductor component glued to itself
by an involution `τ`. There the last clause asks that the residue descend to the double locus. That
fails when `τ` does not preserve the different, and then no multiple of `K_T + Δ` is Cartier
([Kollar2013], 5.13).

The `Θᵢ` are determined by `Δ` and `N`; they are arguments so that the dlt condition and the
generators can refer to them. -/
@[mmp "def_fourfold_sdlt_adjoint_pair"]
structure IsSdltAdjointPair (n : ℕ) (Δ : QWeilDivisor T) (Θ : ∀ i, QDivisor (N.X i)) : Prop where
  /-- `T` is a reduced, separated scheme of finite type over `k` of pure dimension `n`. -/
  isNFold : IsNFold sT n
  /-- `T` is projective over `k`. -/
  isProjectiveMorphism : IsProjectiveMorphism sT
  /-- `T` satisfies Serre's condition `S₂`. -/
  satisfiesS2 : SatisfiesS2 T
  /-- `T` is seminormal. -/
  isSeminormal : IsSeminormal T
  /-- `T` has only double normal crossings in codimension one. -/
  isNcInCodimOne : IsNcInCodimOne sT n
  /-- `Δ` is a boundary: its coefficients lie in `[0, 1]`. -/
  isBoundary : Δ.IsBoundary sT
  /-- No component of `Δ` lies in the double locus of `T`. -/
  genericPoint_not_mem_doubleIntersectionLocus :
    ∀ Γ ∈ Δ.support, Γ.1.genericPoint ∉ (doubleIntersectionLocus T : Set T)
  /-- Each `Θᵢ` is the boundary `Cᵢ + Δᵢ` on the normalization component `Tᵢ`. -/
  isAdjointBoundary : ∀ i, IsAdjointBoundary N Δ i (Θ i)
  /-- Each `(Tᵢ, Θᵢ)` is dlt for some canonical divisor `K_{Tᵢ}`. -/
  exists_isDltPair : ∀ i, ∃ K : Divisor (N.X i), IsDltPair (N.n i ≫ sT) n K (Θ i)
  /-- For some `m > 0` with `mΔ` integral, every point of `T` has an open neighbourhood `U`
  carrying a local generator of `𝒪_T(m(K_T + Δ))` whose residue along every conductor component
  over a double point of `U` is pulled back from `T`. -/
  exists_isAdjointGeneratorOn : ∃ m : ℕ, 0 < m ∧ (∀ Γ, ((m : ℚ) * Δ Γ).den = 1) ∧
    ∀ x : T, ∃ (U : T.Opens) (_ : x ∈ U) (s : ∀ i, RationalPluriForms (N.n i ≫ sT) n m),
      IsAdjointGeneratorOn N n m Θ U s ∧
        ∀ i (P : Mori.PrimeDivisor (N.X i)), (N.n i).base P.genericPoint ∈ U →
          (N.n i).base P.genericPoint ∈ (doubleIntersectionLocus T : Set T) →
          ∃ (V : T.Opens) (hP : (N.n i).base P.genericPoint ∈ V) (a : Fin (n - 1) → Γ(T, V))
            (g : Γ(T, V)), IsLogResiduePresentation N n m i P V hP a g 1 (s i)

end MMP.Fourfold
