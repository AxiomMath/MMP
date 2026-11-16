module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheaf
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialForms

/-!
# Canonical divisors and pairs

Let `X` be a normal variety of dimension `n` over a field `k`, with structure morphism
`f : X ⟶ Spec k`, and let `X_sm ⊆ X` be its smooth locus. The *canonical sheaf* of `X_sm` is
`ω_{X_sm} = ⋀ⁿ Ω_{X_sm/k}`, the `n`-th exterior power of the sheaf of relative differentials of
`X_sm ⟶ Spec k`. A divisor `K` on `X` is a *canonical divisor* if the restriction of its
divisorial sheaf to the smooth locus is isomorphic to the canonical sheaf,
`𝒪_X(K)|_{X_sm} ≅ ω_{X_sm}`, as `𝒪_{X_sm}`-modules. Kollár–Mori write `K_X` for any choice of
canonical divisor.

A *pair* `(X, Δ)` is a normal variety `X` together with a `ℚ`-divisor `Δ = ∑ aᵢ Dᵢ`, `aᵢ ∈ ℚ`,
such that `K_X + Δ` is `ℚ`-Cartier.

## Main definitions

* `MMP.Mori.canonicalSheaf`: `ω_{X_sm} = ⋀ⁿ Ω_{X_sm/k}`, an object of `X_sm.Modules`.
* `MMP.Mori.Divisor.IsCanonicalDivisor`: `K` is a canonical divisor of `X`.
* `MMP.Mori.IsPair`: `(X, Δ)` is a pair.

## Main results

* `MMP.Mori.Divisor.IsCanonicalDivisor.of_linearlyEquivalent`: a divisor linearly equivalent to a
  canonical divisor is canonical.
* `MMP.Mori.QDivisor.IsQCartier.add_of_linearlyEquivalent`: whether `K + Δ` is `ℚ`-Cartier
  depends only on the linear equivalence class of `K`.
* `MMP.Mori.IsPair.isQCartier_of_linearlyEquivalent`: for a pair `(X, Δ)`, `K + Δ` is
  `ℚ`-Cartier for every divisor `K` linearly equivalent to the chosen canonical divisor.

## Implementation notes

The sheaf of relative differentials is `AlgebraicGeometry.Scheme.Hom.relativeDifferentials`,
relative to the inverse image of the structure sheaf of the base, and its `n`-th exterior power is
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms`, the degree-`n` piece of the exterior
algebra of a sheaf of modules. The divisorial sheaf `𝒪_X(K)` is restricted along the open
immersion `X_sm ⟶ X`.

The dimension `n` is an argument of `MMP.Mori.Divisor.IsCanonicalDivisor`, and the predicate
asserts that `X` has dimension `n`; so the predicate is false for every `n` other than the
dimension of `X`, and for `n = dim X` it is the source's condition.

Kollár–Mori fix one canonical divisor `K_X`; a pair is defined here by the existence of a
canonical divisor `K` with `K + Δ` `ℚ`-Cartier. The two readings agree because canonical divisors
are linearly equivalent and `ℚ`-Cartierness of `K + Δ` depends only on the linear equivalence
class of `K` (`MMP.Mori.QDivisor.IsQCartier.add_of_linearlyEquivalent`). The coefficients of `Δ`
are arbitrary rationals: `Δ` is not assumed effective.

The predicates take the instances `IsLocallyNoetherian X`, `IsNormal X` (and `CompactSpace X`
where linear equivalence is used) that the divisorial sheaf and the theory of principal divisors
need; for a normal variety they all hold.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Notation 0.4,
  Definition 2.25
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace MMP.Mori

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The *canonical sheaf* `ω_{X_sm} = ⋀ⁿ Ω_{X_sm/k}` of the smooth locus `X_sm` of
`f : X ⟶ Spec k`: the `n`-th exterior power of the sheaf of relative differentials of
`X_sm ⟶ Spec k`. -/
@[mmp "def_km0_canonical_divisor"]
def canonicalSheaf (n : ℕ) : (smoothLocus f).toScheme.Modules :=
  Scheme.Hom.relativeDifferentialForms ((smoothLocus f).ι ≫ f) n

namespace Divisor

variable [IsLocallyNoetherian X] [IsNormal X]

/-- A divisor `K` on a normal scheme `X` of dimension `n` over `k` is a *canonical divisor* if
`X` has dimension `n` and the restriction of `𝒪_X(K)` to the smooth locus `X_sm` is isomorphic to
the canonical sheaf: `𝒪_X(K)|_{X_sm} ≅ ⋀ⁿ Ω_{X_sm/k}` as `𝒪_{X_sm}`-modules.

Over an imperfect field `k` the smooth locus can be empty, and then every divisor is a
canonical divisor; results that need canonical divisors to be unique up to linear equivalence
(KM 2.25) assume `[PerfectField k]` or `[IsAlgClosed k]`, as Kollár–Mori do. -/
@[mmp "def_km0_canonical_divisor"]
def IsCanonicalDivisor (n : ℕ) (K : Divisor X) : Prop :=
  topologicalKrullDim X = n ∧
    Nonempty (K.divisorialSheaf.restrict (smoothLocus f).ι ≅ canonicalSheaf f n)

variable {f}

/-- A scheme with a canonical divisor for dimension `n` has topological Krull dimension `n`. -/
theorem IsCanonicalDivisor.topologicalKrullDim_eq {n : ℕ} {K : Divisor X}
    (h : K.IsCanonicalDivisor f n) : topologicalKrullDim X = n :=
  h.1

/-- The isomorphism `𝒪_X(K)|_{X_sm} ≅ ω_{X_sm}` of a canonical divisor, chosen. -/
def IsCanonicalDivisor.iso {n : ℕ} {K : Divisor X} (h : K.IsCanonicalDivisor f n) :
    K.divisorialSheaf.restrict (smoothLocus f).ι ≅ canonicalSheaf f n :=
  h.2.some

/-- `K` is a canonical divisor if and only if `X` has dimension `n` and
`𝒪_X(K)|_{X_sm} ≅ ⋀ⁿ Ω_{X_sm/k}`. -/
theorem isCanonicalDivisor_iff {n : ℕ} {K : Divisor X} :
    K.IsCanonicalDivisor f n ↔ topologicalKrullDim X = n ∧
      Nonempty (K.divisorialSheaf.restrict (smoothLocus f).ι ≅ canonicalSheaf f n) :=
  Iff.rfl

/-- **Canonical divisors are stable under linear equivalence.** If `K` is a canonical divisor and
`K' ∼ K`, then `K'` is a canonical divisor. -/
theorem IsCanonicalDivisor.of_linearlyEquivalent [CompactSpace X] {n : ℕ} {K K' : Divisor X}
    (h : K.IsCanonicalDivisor f n) (h' : K'.LinearlyEquivalent K) : K'.IsCanonicalDivisor f n :=
  ⟨h.1, ⟨(Scheme.Modules.restrictFunctor (smoothLocus f).ι).mapIso h'.divisorialSheafIso ≪≫
    h.iso⟩⟩

/-- If `K' ∼ K`, then `K'` is a canonical divisor if and only if `K` is a canonical divisor. -/
theorem isCanonicalDivisor_iff_of_linearlyEquivalent [CompactSpace X] {n : ℕ} {K K' : Divisor X}
    (h : K'.LinearlyEquivalent K) : K'.IsCanonicalDivisor f n ↔ K.IsCanonicalDivisor f n :=
  ⟨fun hK' => hK'.of_linearlyEquivalent h.symm, fun hK => hK.of_linearlyEquivalent h⟩

end Divisor

namespace QDivisor

variable [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]

/-- If `K + Δ` is `ℚ`-Cartier and `K ∼ K'`, then `K' + Δ` is `ℚ`-Cartier. -/
theorem IsQCartier.add_of_linearlyEquivalent {K K' : Divisor X} {Δ : QDivisor X}
    (h : (Divisor.toQDivisor K + Δ).IsQCartier) (hK : K.LinearlyEquivalent K') :
    (Divisor.toQDivisor K' + Δ).IsQCartier := by
  obtain ⟨m, hm, D, hD, hC⟩ := h
  obtain ⟨φ, hφ⟩ := hK
  refine ⟨m, hm, D - m • principalDivisor φ, ?_,
    hC.sub ((Divisor.isCartier_principalDivisor φ).zsmul m)⟩
  rw [map_sub, map_zsmul, hD, ← hφ, map_sub, smul_add, smul_add, smul_sub]
  abel

/-- For linearly equivalent divisors `K ∼ K'`, `K + Δ` is `ℚ`-Cartier if and only if `K' + Δ` is
`ℚ`-Cartier. -/
theorem isQCartier_add_iff_of_linearlyEquivalent {K K' : Divisor X} {Δ : QDivisor X}
    (hK : K.LinearlyEquivalent K') :
    (Divisor.toQDivisor K + Δ).IsQCartier ↔ (Divisor.toQDivisor K' + Δ).IsQCartier :=
  ⟨fun h => h.add_of_linearlyEquivalent hK, fun h => h.add_of_linearlyEquivalent hK.symm⟩

end QDivisor

section Pair

variable [IsLocallyNoetherian X] [IsNormal X]

/-- A *pair* `(X, Δ)`: `X` is a normal variety over `k` and `Δ` is a `ℚ`-divisor on `X`, with
arbitrary rational coefficients, such that `K_X + Δ` is `ℚ`-Cartier for a canonical divisor `K_X`
of `X`. -/
@[mmp "def_km2a_pair"]
def IsPair (Δ : QDivisor X) : Prop :=
  IsNormalVariety k f ∧
    ∃ (n : ℕ) (K : Divisor X), K.IsCanonicalDivisor f n ∧
      (Divisor.toQDivisor K + Δ).IsQCartier

variable {f}

/-- If `(X, Δ)` is a pair, then `X` is a normal variety over `k`. -/
theorem IsPair.isNormalVariety {Δ : QDivisor X} (h : IsPair f Δ) : IsNormalVariety k f :=
  h.1

/-- For a pair `(X, Δ)`, `K + Δ` is `ℚ`-Cartier for every divisor `K` linearly equivalent to
the canonical divisor witnessing the pair. -/
theorem IsPair.isQCartier_of_linearlyEquivalent [CompactSpace X] {Δ : QDivisor X}
    (h : IsPair f Δ) :
    ∃ n : ℕ, ∃ K₀ : Divisor X, K₀.IsCanonicalDivisor f n ∧
      ∀ K : Divisor X, K.LinearlyEquivalent K₀ → (Divisor.toQDivisor K + Δ).IsQCartier := by
  obtain ⟨-, n, K₀, hK₀, hQ⟩ := h
  exact ⟨n, K₀, hK₀, fun K hK => hQ.add_of_linearlyEquivalent hK.symm⟩

/-- If `X` is a normal variety over `k`, `K` is a canonical divisor of `X` and `K + Δ` is
`ℚ`-Cartier, then `(X, Δ)` is a pair. -/
theorem isPair_of_isCanonicalDivisor {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hX : IsNormalVariety k f) (hK : K.IsCanonicalDivisor f n)
    (hQ : (Divisor.toQDivisor K + Δ).IsQCartier) : IsPair f Δ :=
  ⟨hX, n, K, hK, hQ⟩

end Pair

end MMP.Mori
