module

public import MMP.AlgebraicGeometry.Divisor.RestrictedSectionAlgebra
public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
public import MMP.AlgebraicGeometry.MMP.Fourfold.StableBase

/-!
# Graded restricted linear series and the section-lifting inequality

Fix a Noetherian complex algebra `A`, a finite morphism `g : T ⟶ Spec A` from a normal affine
complex variety `T`, and a smooth complex `d`-fold `S` with a projective birational morphism
`f : S ⟶ T`. Let `K` be a canonical divisor of `S`, let `Ω ≥ 0` be a rational boundary with
`(S, Ω)` klt, and let `q > 0` be such that `qΩ` is an integral Cartier divisor.

A *graded restricted series* is a family of finitely generated `A`-submodules
`V_m ⊆ H⁰(S, 𝒪_S(m(K + Ω)))`, for `q ∣ m`, whose direct sum `⊕ V_m tᵐ ⊆ K(S)[t]` is a graded
`A`-algebra (so `1 ∈ V_0` and `V_m V_n ⊆ V_{m+n}`), with `V_q ≠ 0`. Let `𝓛_m` be the divisors
`div s + m(K + Ω)` of the nonzero `s ∈ V_m`, let `F_m = Fix(𝓛_m)/m` be the normalized fixed
divisor, and put `F = inf_{n ≥ 1} F_{q n!}`, `Θ = Ω - Ω ∧ F` and `Θ_m = Ω - Ω ∧ F_m`, all
infima and minima taken coefficientwise.

The series has the *lifting property* if there is a rational `0 < ε < 1` such that for every
`k > 0` divisible by `q` and every `ℚ`-divisor `P` with `kP` integral Cartier and
`Ω ∧ (1 - ε/k)F ≤ P ≤ Ω`, multiplication by the canonical section `σ_{kP}` of `𝒪_S(kP)` maps
`H⁰(S, 𝒪_S(k(K + Ω - P)))` into `V_k`.

## Main definitions

* `MMP.Fourfold.restrictedSeriesBaseMap`: the ring map `A → Γ(T, 𝒪_T) → Γ(S, 𝒪_S) → K(S)`
  through which `K(S)` is an `A`-module.
* `MMP.Fourfold.IsGradedRestrictedSeries`: graded restricted series.
* `MMP.Fourfold.restrictedFixedMultiplicity`: the coefficient of `Fix(𝓛_m)` along a prime
  divisor.
* `MMP.Fourfold.restrictedNormalizedFixedPart`: the coefficients of `F_m = Fix(𝓛_m)/m`.
* `MMP.Fourfold.restrictedAsymptoticFixedPart`: the coefficients of `F = inf_{n ≥ 1} F_{q n!}`.
* `MMP.Fourfold.coeffwiseMin`: the coefficientwise minimum `Ω ∧ G` of a `ℚ`-divisor `Ω ≥ 0` and
  a family of coefficients in `[0, ∞]`.
* `MMP.Fourfold.restrictedClippedBoundary`, `MMP.Fourfold.restrictedClippedBoundaryAt`: the
  boundaries `Θ = Ω - Ω ∧ F` and `Θ_m = Ω - Ω ∧ F_m`.
* `MMP.Fourfold.HasRestrictedLiftingProperty`: the section-lifting inequality.

## Implementation notes

Sections of `𝒪_S(D)` are rational functions `s ∈ K(S)` with `s = 0` or `div s + D ≥ 0`
(`MMP.Fourfold.divisorialSections`). In this model the canonical section `σ_E` of an effective
divisor `E` is the rational function `1`, and the multiplication
`𝒪_S(D - E) ⊗ 𝒪_S(E) → 𝒪_S(D)` is the multiplication of `K(S)`; so the lifting property says
that the subset `H⁰(S, 𝒪_S(k(K + Ω - P)))` of `K(S)` is contained in `V_k`. This is an inclusion
of sets of sections, not of their divisors: a section and its multiple by a nonconstant unit are
different elements of `K(S)`.

The integral divisor `m(K + Ω)`, for `q ∣ m`, is written `m K + ⌊mΩ⌋`, as in
`MMP.Mori.Divisor.canonicalRingPiece`; the rounding is exact since `mΩ` is integral. Likewise
`k(K + Ω - P) = k K + ⌊k(Ω - P)⌋` when `q ∣ k` and `kP` is integral.

The family `V_m` is indexed by all `m ∈ ℕ`, with `V_m = 0` for `q ∤ m`; this is the extension by
zero of the source's family indexed by the multiples of `q`, and changes neither the direct sum
nor the fixed parts at admissible indices.

`K(S)` is an `A`-module through `MMP.Fourfold.restrictedSeriesBaseMap`. An `A`-submodule of
`K(S)` is the same as a submodule over the image subring of that map, and is finitely generated
over `A` exactly when it is over the image; the series is stated over the image subring.

The fixed part is recorded by its coefficients, in `ℕ∞` for `Fix(𝓛_m)` and in `[0, ∞]` for
`F_m` and `F`; the value `⊤` occurs only when `V_m = 0`. The coefficient of `Fix(𝓛_m)` along a
prime divisor `G` is the least order of vanishing along `G`
(`MMP.Fourfold.sectionVanishingOrder`) of a nonzero section in `V_m`, which is the minimum of the
coefficients of `G` in the divisors of `𝓛_m`.

## References

* The fourfold source, *Restricted rationality*, the definitions of a graded restricted linear
  series and of the section-lifting inequality.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori

/-- A prime divisor meets the whole scheme. -/
theorem primeDivisor_support_inter_top_nonempty {X : Scheme.{u}}
    (P : MMP.Mori.PrimeDivisor X) : (P.support ∩ ((⊤ : X.Opens) : Set X)).Nonempty :=
  ⟨P.genericPoint, by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl, trivial⟩

/-! ### The base ring -/

/-- The ring map `A ≅ Γ(Spec A, 𝒪) → Γ(T, 𝒪_T) → Γ(S, 𝒪_S) → K(S)` induced by
`g : T ⟶ Spec A` and `f : S ⟶ T`, through which `K(S)` and the sections of divisorial sheaves
on `S` are `A`-modules. -/
def restrictedSeriesBaseMap {A : Type} [CommRing A] {S T : Scheme.{0}}
    (g : T ⟶ Spec (.of A)) (f : S ⟶ T) : A →+* RationalFunctions S :=
  globalSectionsToRationalFunctions.comp
    (f.appTop.hom.comp (g.appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom))

/-! ### Graded restricted series -/

section Series

variable {A : Type} [CommRing A] [Algebra ℂ A] {S T : Scheme.{0}}
  [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
  (sS : S ⟶ Spec (.of ℂ)) (sT : T ⟶ Spec (.of ℂ)) (g : T ⟶ Spec (.of A)) (f : S ⟶ T)

/-- **A graded restricted linear series.** `A` is a Noetherian complex algebra, `g : T ⟶ Spec A`
is a finite morphism of complex schemes from a normal affine complex variety `T`, `S` is a smooth
complex variety of dimension `d` with canonical divisor `K` and a projective birational morphism
`f : S ⟶ T` over `ℂ`, `(S, Ω)` is a klt pair with `Ω ≥ 0` rational, and `q > 0` makes `qΩ` an
integral Cartier divisor. The family `V_m` of submodules of `K(S)`, over the image of `A`
(`MMP.Fourfold.restrictedSeriesBaseMap`), consists of finitely generated `A`-submodules
`V_m ⊆ H⁰(S, 𝒪_S(m(K + Ω)))` for `q ∣ m` (and `V_m = 0` otherwise) whose direct sum
`⊕ V_m tᵐ ⊆ K(S)[t]` is a graded `A`-algebra, that is `1 ∈ V_0` and `V_m V_n ⊆ V_{m+n}`, and
with `V_q ≠ 0`. -/
@[mmp "def_fourfold_graded_restricted_series"]
structure IsGradedRestrictedSeries (d : ℕ) (K : Divisor S) (Ω : QDivisor S) (q : ℕ)
    (V : ℕ → Submodule (restrictedSeriesBaseMap g f).range (RationalFunctions S)) : Prop where
  isNoetherianRing : IsNoetherianRing A
  isFinite : IsFinite g
  comp_spec_eq : g ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ A)) = sT
  isNormalVariety_target : IsNormalVariety ℂ sT
  isAffine_target : IsAffine T
  isNormalVariety_source : IsNormalVariety ℂ sS
  isSmoothScheme : IsSmoothScheme sS
  isCanonicalDivisor : K.IsCanonicalDivisor sS d
  comp_eq : f ≫ sT = sS
  isProjectiveMorphism : IsProjectiveMorphism f
  isBirationalMorphism : IsBirationalMorphism f
  isKltPair : IsKltPair sS Ω
  q_pos : 0 < q
  /-- The divisor `qΩ` is an integral Cartier divisor. -/
  isCartierDivisor_smul : ((q : ℤ) • Ω).IsCartierDivisor
  mem_divisorialSections : ∀ m, q ∣ m → ∀ s ∈ V m,
    s ∈ divisorialSections (m • K + DivisorWithCoeffs.roundDown ((m : ℚ) • Ω))
  eq_bot_of_not_dvd : ∀ m, ¬ q ∣ m → V m = ⊥
  /-- Each `V_m` is a finitely generated `A`-submodule. -/
  fg : ∀ m, (V m).FG
  one_mem : (1 : RationalFunctions S) ∈ V 0
  mul_mem : ∀ m n, ∀ s ∈ V m, ∀ t ∈ V n, s * t ∈ V (m + n)
  ne_bot : V q ≠ ⊥

end Series

/-! ### Fixed parts and clipped boundaries -/

section FixedPart

variable {S : Scheme.{0}} [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
  {R : Type*} [Semiring R] [Module R (RationalFunctions S)]

open scoped ENNReal

/-- The coefficient along a prime divisor `G` of the fixed divisor `Fix(𝓛_m)` of the linear
system `𝓛_m` of divisors `div s + m(K + Ω)` of the nonzero sections `s ∈ V_m` of
`𝒪_S(m(K + Ω))`: the least order of vanishing along `G` of such a section (`⊤` if `V_m = 0`). -/
@[mmp "def_fourfold_graded_restricted_series"]
def restrictedFixedMultiplicity (K : Divisor S) (Ω : QDivisor S)
    (V : ℕ → Submodule R (RationalFunctions S)) (m : ℕ) (G : MMP.Mori.PrimeDivisor S) : ℕ∞ :=
  ⨅ (s : RationalFunctions S) (_ : s ∈ V m)
    (hs : s ∈ divisorialSections (m • K + DivisorWithCoeffs.roundDown ((m : ℚ) • Ω)))
    (_ : s ≠ 0),
    sectionVanishingOrder (m • K + DivisorWithCoeffs.roundDown ((m : ℚ) • Ω)) G
      (primeDivisor_support_inter_top_nonempty G) ⟨(rationalFunctionsPresheafTopEquiv S).symm s, hs⟩

/-- The coefficient along `G` of the normalized fixed part `F_m = Fix(𝓛_m)/m`, in `[0, ∞]`. -/
@[mmp "def_fourfold_graded_restricted_series"]
def restrictedNormalizedFixedPart (K : Divisor S) (Ω : QDivisor S)
    (V : ℕ → Submodule R (RationalFunctions S)) (m : ℕ) (G : MMP.Mori.PrimeDivisor S) : ℝ≥0∞ :=
  (restrictedFixedMultiplicity K Ω V m G : ℝ≥0∞) / m

/-- The coefficient along `G` of the asymptotic fixed part `F = inf_{n ≥ 1} F_{q n!}`. -/
@[mmp "def_fourfold_graded_restricted_series"]
def restrictedAsymptoticFixedPart (K : Divisor S) (Ω : QDivisor S) (q : ℕ)
    (V : ℕ → Submodule R (RationalFunctions S)) (G : MMP.Mori.PrimeDivisor S) : ℝ≥0∞ :=
  ⨅ (n : ℕ) (_ : 1 ≤ n), restrictedNormalizedFixedPart K Ω V (q * n.factorial) G

/-- The coefficientwise minimum `Ω ∧ F` of a `ℚ`-divisor `Ω ≥ 0` and a family `F` of coefficients
in `[0, ∞]`, an `ℝ`-divisor supported on the support of `Ω`. (For a negative coefficient of `Ω`
the coefficient used is `0`.) -/
@[mmp "def_fourfold_graded_restricted_series"]
def coeffwiseMin {X : Scheme.{0}} (Ω : QDivisor X) (F : MMP.Mori.PrimeDivisor X → ℝ≥0∞) :
    RDivisor X :=
  Finsupp.onFinset Ω.support (fun G => (min (ENNReal.ofReal (Ω G : ℝ)) (F G)).toReal) fun G hG => by
    rw [Finsupp.mem_support_iff]
    rintro h
    simp [h] at hG

/-- The coefficient of `Ω ∧ F` along `G` is `min(Ω_G, F_G)`, computed in `[0, ∞]`. -/
theorem coeff_coeffwiseMin {X : Scheme.{0}} (Ω : QDivisor X) (F : MMP.Mori.PrimeDivisor X → ℝ≥0∞)
    (G : MMP.Mori.PrimeDivisor X) :
    (coeffwiseMin Ω F).coeff G = (min (ENNReal.ofReal (Ω.coeff G : ℝ)) (F G)).toReal :=
  rfl

/-- The clipped boundary `Θ = Ω - Ω ∧ F` of a graded restricted series, with
`F = inf_{n ≥ 1} F_{q n!}`. -/
@[mmp "def_fourfold_graded_restricted_series"]
def restrictedClippedBoundary (K : Divisor S) (Ω : QDivisor S) (q : ℕ)
    (V : ℕ → Submodule R (RationalFunctions S)) : RDivisor S :=
  QDivisor.toRDivisor Ω - coeffwiseMin Ω (restrictedAsymptoticFixedPart K Ω q V)

/-- The clipped boundary `Θ_m = Ω - Ω ∧ F_m` at the index `m` of a graded restricted series. -/
@[mmp "def_fourfold_graded_restricted_series"]
def restrictedClippedBoundaryAt (K : Divisor S) (Ω : QDivisor S)
    (V : ℕ → Submodule R (RationalFunctions S)) (m : ℕ) : RDivisor S :=
  QDivisor.toRDivisor Ω - coeffwiseMin Ω (restrictedNormalizedFixedPart K Ω V m)

end FixedPart

/-! ### The lifting property -/

section Lifting

variable {A : Type} [CommRing A] [Algebra ℂ A] {S T : Scheme.{0}}
  [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
  (sS : S ⟶ Spec (.of ℂ)) (sT : T ⟶ Spec (.of ℂ)) (g : T ⟶ Spec (.of A)) (f : S ⟶ T)

open scoped ENNReal

/-- **The section-lifting inequality for a graded restricted series.** The graded restricted
series `V` has the *lifting property* if there is a rational `0 < ε < 1` such that, for every
`k > 0` divisible by `q` and every `ℚ`-divisor `P` with `kP` integral Cartier and
`Ω ∧ (1 - ε/k)F ≤ P ≤ Ω` (coefficientwise, `F = inf_{n ≥ 1} F_{q n!}`), multiplication by the
canonical section `σ_{kP}` maps `H⁰(S, 𝒪_S(k(K + Ω - P)))` into `V_k`. In `K(S)` the canonical
section is the function `1`, so the condition is the inclusion of
`H⁰(S, 𝒪_S(k(K + Ω - P))) = H⁰(S, 𝒪_S(kK + ⌊k(Ω - P)⌋))` in `V_k`, as sets of sections. -/
@[mmp "def_fourfold_restricted_lifting_property"]
def HasRestrictedLiftingProperty (d : ℕ) (K : Divisor S) (Ω : QDivisor S) (q : ℕ)
    (V : ℕ → Submodule (restrictedSeriesBaseMap g f).range (RationalFunctions S)) : Prop :=
  IsGradedRestrictedSeries sS sT g f d K Ω q V ∧
    ∃ ε : ℚ, 0 < ε ∧ ε < 1 ∧ ∀ k : ℕ, 0 < k → q ∣ k → ∀ P : QDivisor S,
      ((k : ℤ) • P).IsCartierDivisor →
      coeffwiseMin Ω (fun G => ENNReal.ofReal (1 - (ε : ℝ) / k) *
          restrictedAsymptoticFixedPart K Ω q V G) ≤ QDivisor.toRDivisor P →
      P ≤ Ω →
      ∀ s ∈ divisorialSections (k • K + DivisorWithCoeffs.roundDown ((k : ℚ) • (Ω - P))),
        s ∈ V k

end Lifting

end MMP.Fourfold
