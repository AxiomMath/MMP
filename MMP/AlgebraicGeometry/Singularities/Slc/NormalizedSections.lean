/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.AlgebraicGeometry.MMP.Abundance.Defs

/-!
# Pluricanonical sections on slc curves and normalized sections

The definition of FA 12.2.9 on normalized sections of `𝒪_C(m(K_C + Δ))` on an slc curve
`(C, Δ)`, together with the sheaf `𝒪_C(m(K_C + Δ)) = ω_C^{⊗m}(mΔ)` it is about.

## The dualizing sheaf of a nodal curve

The curve `C` of an slc curve is reduced, and every singular closed point of `C` is a node
(`MMP.Flips.IsDoubleNormalCrossingPoint`). The normalization `n : C̄ = ⨆ᵢ Cᵢ ⟶ C` is an
isomorphism at the generic points, so the total ring of fractions of `C` is `∏ᵢ k(Cᵢ)` and a
*rational (meromorphic) `m`-canonical form* on `C` is a family `(sᵢ)ᵢ` of rational `m`-canonical
forms `sᵢ` on the `Cᵢ` (`MMP.Mori.RationalPluriForms`); `n^*(s)|_{Cᵢ}` is `sᵢ`. As in the source,
`ω_C` is the dualizing sheaf of the curve `C`, which is smooth or has double normal crossings at
each of its points; it is the subsheaf of meromorphic forms which near a smooth point are the
regular forms, and near a node `xy = 0` are the multiples `h σ` (`h ∈ 𝒪_C`) of the residue form
`σ = dx/x = -dy/y`. Accordingly, `𝒪_C(m(K_C + Δ)) = ω_C^{⊗m}(mΔ)` is the subsheaf of meromorphic
`m`-canonical forms which near a smooth point `P` have order `≥ -mΔ_P`, and near a node `Q` are the
multiples `h σ^m`, `h ∈ 𝒪_{C,Q}` (`Δ` has no component at a node: the components of a boundary are
prime divisors along which `C` is regular).

A local ring `𝒪_{C,Q}` at a node consists of the pairs `(f, g)` of functions on the two branches
with `f(Q') = g(Q'')`, where `Q', Q''` are the two points of `C̄` over `Q`; on the branch `y = 0`
the form `h σ^m` is `f (dx/x)^m`, on the branch `x = 0` it is `(-1)^m g (dy/y)^m`. The forms
`h σ^m` are therefore the meromorphic forms `(s', s'')` near `Q', Q''` with poles of order `≤ m`
whose leading coefficients `c' = res_{Q'}(s')`, `c'' = res_{Q''}(s'')` with respect to
`(dz/z)^m` (`z` a local parameter; the leading coefficient does not depend on `z`) satisfy
`c'' = (-1)^m c'`: `s' - c' (dz'/z')^m` and `s'' - c'' (dz''/z'')^m` have poles of order `< m`.
The nodes are `k`-points (their completed local rings are `k[[x₀, x₁]]/(x₀x₁)` as `k`-algebras),
so `c', c'' ∈ k`.

## The normalization

The normalization of `C` is `MMP.Flips.slcCurveNormalization`, and the `Cᵢ` are the connected
components of `C̄`. They are recorded as a `MMP.Flips.NormalizationComponents` of `C`: a family of
normal varieties `Cᵢ` over `C` (with the structure maps through `C`) such that the induced
morphism `⨿ᵢ Cᵢ ⟶ C` is the normalization `C̄ ⟶ C` up to isomorphism over `C`. Each `Cᵢ` is
integral, hence connected, so the `Cᵢ` are the connected components of `C̄`.

## Main definitions

* `MMP.Flips.NormalizationComponents`: `n : C̄ = ⨆ᵢ Cᵢ ⟶ C` with the `Cᵢ` given individually.
* `MMP.Flips.NormalizationComponents.IsComponentBoundary`: the boundary `Δᵢ` on `Cᵢ`
  (FA 12.2.9, as in `MMP.Flips.IsSlcComponentBoundary`).
* `MMP.Flips.NormalizationComponents.slcPluricanonicalSections`: `Γ(C, 𝒪_C(m(K_C + Δ)))`.
* `MMP.Flips.NormalizationComponents.IsNormalizedSlcSection`: normalized sections on an slc
  curve (FA 12.2.9).

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 12.2.9,
  12.2.9.1
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Flips

open MMP.Mori

variable {k : Type u} [Field k] {C : Scheme.{u}} (sC : C ⟶ Spec (.of k))

/-- The normalization `n : C̄ = ⨆ᵢ Cᵢ ⟶ C` of a scheme `C` over `k`, with its connected components
`Cᵢ` given individually: a family of normal varieties `Cᵢ` with morphisms `nᵢ : Cᵢ ⟶ C` (each `Cᵢ`
a `k`-scheme through `nᵢ ≫ s_C`) such that the induced morphism `⨿ᵢ Cᵢ ⟶ C` is, up to an
isomorphism over `C`, the normalization `MMP.Flips.slcCurveNormalization C hC` (the relative
normalization of `C` in `⨿_η Spec κ(η)`, Stacks 035M, 035N). -/
structure NormalizationComponents
    (hC : ∀ U : C.Opens, IsCompact (U : Set C) → (irreducibleComponents U).Finite) where
  /-- The index set of the components. -/
  ι : Type u
  /-- The component `Cᵢ`. -/
  X : ι → Scheme.{u}
  /-- The restriction `nᵢ : Cᵢ ⟶ C` of the normalization to `Cᵢ`. -/
  n : ∀ i, X i ⟶ C
  /-- Each `Cᵢ` is a normal variety over `k`. -/
  isNormalVariety : ∀ i, IsNormalVariety k (n i ≫ sC)
  /-- `⨿ᵢ Cᵢ ⟶ C` is the normalization of `C`, up to isomorphism over `C`. -/
  exists_iso : ∃ φ : (∐ X) ≅ Stacks.AlgebraicGeometry.Normalization.normalizationScheme C hC,
    φ.hom ≫ slcCurveNormalization C hC = Sigma.desc n

namespace NormalizationComponents

variable {sC} {hC : ∀ U : C.Opens, IsCompact (U : Set C) → (irreducibleComponents U).Finite}
  (N : NormalizationComponents sC hC)

/-- Each component `Cᵢ` is an integral scheme. -/
instance (i : N.ι) : IsIntegral (N.X i) := (N.isNormalVariety i).1.toIsIntegral

/-- Each component `Cᵢ` is locally Noetherian. -/
instance (i : N.ι) : IsLocallyNoetherian (N.X i) :=
  haveI := (N.isNormalVariety i).1.toLocallyOfFiniteType
  LocallyOfFiniteType.isLocallyNoetherian (N.n i ≫ sC)

/-- Each component `Cᵢ` is a normal scheme. -/
instance (i : N.ι) : IsNormal (N.X i) := (N.isNormalVariety i).2

open scoped Classical in
/-- The coefficient of a prime divisor `P` of `Cᵢ` in the boundary `Δᵢ := n^*Δ|_{Cᵢ} + ∑_P P`
(FA 12.2.9): `1` if `nᵢ(P)` is a node of `C`, and otherwise the coefficient of `nᵢ(P)` in `Δ`.
This is the formula of `MMP.Flips.IsSlcComponentBoundary`, read on the component `Cᵢ`. -/
def componentBoundaryCoeff (Δ : QWeilDivisor C) (i : N.ι) (P : Mori.PrimeDivisor (N.X i)) : ℚ :=
  if IsDoubleNormalCrossingPoint sC 1 ((N.n i).base P.genericPoint) then 1
  else ∑ Γ ∈ Δ.support, if (N.n i).base P.genericPoint = Γ.1.genericPoint then Δ Γ else 0

/-- **The boundaries `Δᵢ`** (FA 12.2.9). For an slc curve `(C, Δ)` with normalization
`n : C̄ = ⨆ᵢ Cᵢ ⟶ C`, `Δᵢ := n^*Δ|_{Cᵢ} + ∑_P P`, the sum over the points `P ∈ Cᵢ` with `n(P)` a
node of `C`, as a `ℚ`-divisor on `Cᵢ` characterized by its coefficients
(`componentBoundaryCoeff`, the formula of `MMP.Flips.IsSlcComponentBoundary`). The hypothesis
that `(C, Δ)` is an slc curve is part of the predicate. -/
def IsComponentBoundary (Δ : QWeilDivisor C) (i : N.ι) (Δi : QDivisor (N.X i)) : Prop :=
  IsSlcCurve sC Δ ∧ ∀ P, Δi.coeff P = N.componentBoundaryCoeff Δ i P

/-- `c` is the *leading coefficient* of the rational `m`-canonical form `τ` on `Cᵢ` at the point
`P` with respect to `(dz/z)^m`: there is a local parameter `z` at `P` such that
`τ - c (dz/z)^m` has a pole of order `< m` at `P` (it is `0`, or of order `≥ 1 - m`). Since
`(dz/z)^m` has a pole of order exactly `m`, this says that `τ` has a pole of order `≤ m` at `P`
with leading term `c (dz/z)^m`; the leading coefficient does not depend on `z`. -/
def IsLeadingCoeff {m : ℕ} (i : N.ι) (P : Mori.PrimeDivisor (N.X i))
    (τ : RationalPluriForms (N.n i ≫ sC) 1 m) (c : k) : Prop :=
  letI := functionFieldAlgebra (N.n i ≫ sC)
  ∃ z : (N.X i).functionField, (N.X i).ord z P.genericPoint = 1 ∧
    (τ - algebraMap k (N.X i).functionField c • dlogPow (N.n i ≫ sC) z m = 0 ∨
      1 - (m : ℤ) ≤ P.ordForm (τ - algebraMap k (N.X i).functionField c •
        dlogPow (N.n i ≫ sC) z m))

/-- **The sections `Γ(C, 𝒪_C(m(K_C + Δ)))`** on an slc curve `(C, Δ)`, `m > 0`, `mΔ` integral
(FA 12.2.9). A rational `m`-canonical form on `C` is a family `s = (sᵢ)ᵢ` of rational
`m`-canonical forms on the components `Cᵢ` of the normalization (`n^*(s)|_{Cᵢ} = sᵢ`), and
`𝒪_C(m(K_C + Δ)) = ω_C^{⊗m}(mΔ)` is the subsheaf of the forms which near a smooth point `P` of
`C` have order `≥ -mΔ_P`, and near a node `Q` are the multiples `h σ^m`, `h ∈ 𝒪_{C,Q}`, of the
`m`-th power of the residue form `σ = dx/x = -dy/y` generating `ω_C` at `Q` (see the module
docstring). So `s` is a section over `C` if
* for every `i` and every point `P` of `Cᵢ`, `ord_P(sᵢ) + coeff_P(mΔᵢ) ≥ 0` (or `sᵢ = 0`): over a
  smooth point of `C` this is `ord_P(sᵢ) ≥ -mΔ_{n(P)}`, and over a node it says that `sᵢ` has a
  pole of order `≤ m` at `P` (the coefficient of `P` in `Δᵢ` is `1`);
* for every node `Q` of `C` and any two distinct points `Q' ∈ Cᵢ`, `Q'' ∈ Cⱼ` of `C̄` over `Q`, the
  leading coefficients satisfy `c'' = (-1)^m c'` (`IsLeadingCoeff`).

The hypotheses (`(C, Δ)` an slc curve, `m > 0`, `mΔ` integral) are not needed to state the
condition; they are part of `IsNormalizedSlcSection`. -/
@[mmp "def_fa12a_normalized_section_slc_curve"]
def slcPluricanonicalSections (Δ : QWeilDivisor C) (m : ℕ) :
    Set (∀ i : N.ι, RationalPluriForms (N.n i ≫ sC) 1 m) :=
  {s | (∀ i (P : Mori.PrimeDivisor (N.X i)), s i ≠ 0 →
      0 ≤ ((P.ordForm (s i) : ℤ) : ℚ) + m * N.componentBoundaryCoeff Δ i P) ∧
    ∀ (i j : N.ι) (P : Mori.PrimeDivisor (N.X i)) (P' : Mori.PrimeDivisor (N.X j)),
      (N.n i).base P.genericPoint = (N.n j).base P'.genericPoint →
      IsDoubleNormalCrossingPoint sC 1 ((N.n i).base P.genericPoint) →
      (⟨i, P.genericPoint⟩ : Σ i, N.X i) ≠ ⟨j, P'.genericPoint⟩ →
      ∃ c : k, N.IsLeadingCoeff i P (s i) c ∧ N.IsLeadingCoeff j P' (s j) ((-1) ^ m * c)}

/-- **Normalized sections on an slc curve** (FA Def. 12.2.9). Let `(C, Δ)` be an slc curve and
`m > 0` with `mΔ` integral. `s ∈ Γ(C, 𝒪(m(K_C + Δ)))` is *normalized* if
`n^*(s)|_{Cᵢ} ∈ Γ(Cᵢ, 𝒪(m(K_{Cᵢ} + Δᵢ)))` is normalized (FA 12.2.9, 12.2.9.1;
`MMP.Flips.IsNormalizedSection`, with respect to the fixed normalization datum `ε` for elliptic
curves) for every `i`.

The section `s` is a family of rational `m`-canonical forms on the components `Cᵢ` of the
normalization lying in `slcPluricanonicalSections` (so `n^*(s)|_{Cᵢ} = sᵢ`); `mΔ` integral means
that every coefficient of `mΔ` is an integer. `Δᵢ` is the boundary of `IsComponentBoundary`
and `mΔᵢ` the integral divisor `Gᵢ` of `MMP.Flips.IsNormalizedSection`. -/
@[mmp "def_fa12a_normalized_section_slc_curve"]
def IsNormalizedSlcSection (ε : EllipticNormalizationDatum k) (Δ : QWeilDivisor C) (m : ℕ)
    (s : ∀ i : N.ι, RationalPluriForms (N.n i ≫ sC) 1 m) : Prop :=
  IsSlcCurve sC Δ ∧ 0 < m ∧ (∀ Γ, ((m : ℚ) * Δ Γ).den = 1) ∧
    s ∈ N.slcPluricanonicalSections Δ m ∧
    ∀ i, ∃ (Δi : QDivisor (N.X i)) (Gi : Divisor (N.X i)),
      N.IsComponentBoundary Δ i Δi ∧ IsNormalizedSection ε (N.n i ≫ sC) Δi m Gi (s i)

end NormalizationComponents

end MMP.Flips
