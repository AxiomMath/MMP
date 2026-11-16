module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.Divisor.Canonical.Basic
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
public import MMP.AlgebraicGeometry.Divisor.CartierLineBundle

/-!
# Basic notions of the minimal model program for fourfolds

The vocabulary of the minimal model program: relatively nef and relatively ample `ℚ`-Cartier
divisors, the spaces `N¹(X)_ℝ` and `N₁(X)_ℝ`, the closed cone of curves and its `D`-negative
extremal rays, contractions and small morphisms, pairs, simple normal crossing divisors and their
strata, and log resolutions with their crepant pull-backs. Most of these notions are those of
Kollár–Mori, formalized in `MMP.Mori`.

## Main definitions

* `MMP.Fourfold.KCartierDivisor.toReal`: a `ℚ`-Cartier divisor as an `ℝ`-Cartier divisor.
* `MMP.Fourfold.KCartierDivisor.IsRelativelyNefQ`,
  `MMP.Fourfold.KCartierDivisor.IsRelativelyAmpleQ`: `f`-nef and `f`-ample `ℚ`-Cartier divisors.
* `MMP.Fourfold.numericallyTrivialDivisors`, `MMP.Fourfold.NumericalDivisorClasses`: `N¹(X)_ℝ`.
* `MMP.Fourfold.numericalDivisorClass`: the class in `N¹(X)_ℝ` of an `ℝ`-Cartier divisor.
* `MMP.Fourfold.curvePairing`: the pairing `N₁(X)_ℝ → (Div(X)_ℝ → ℝ)`.
* `MMP.Fourfold.numericalPairing`: the intersection pairing `N¹(X)_ℝ × N₁(X)_ℝ → ℝ`.
* `MMP.Fourfold.IsNegativeExtremalRay`: a `D`-negative extremal ray of `NE̅(X)`.
* `MMP.Fourfold.IsContraction`, `MMP.Fourfold.IsContractionOfRay`: contractions, and the
  contraction of an extremal ray.
* `MMP.Fourfold.IsPair`: a pair `(X, B)` with effective boundary over an algebraically closed
  field of characteristic zero.
* `MMP.Fourfold.IsSmallMorphism`: small proper birational morphisms.
* `MMP.Fourfold.IsSNCStratum`: the strata of a simple normal crossing divisor.
* `MMP.Fourfold.IsLogResolution`: projective log resolutions of a pair.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Fourfold

open MMP.Mori

variable {k : Type u} [Field k] {X Z : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-! ### Relatively nef and relatively ample divisors -/

/-- A `ℚ`-Cartier divisor `∑ cⱼ Dⱼ` regarded as the `ℝ`-Cartier divisor with the same
coefficients. -/
def KCartierDivisor.toReal : KCartierDivisor ℚ X →+ KCartierDivisor ℝ X :=
  Finsupp.mapRange.addMonoidHom (Rat.castHom ℝ).toAddMonoidHom

/-- The coefficients of `KCartierDivisor.toReal D` are those of `D`, cast to `ℝ`. -/
theorem KCartierDivisor.toReal_apply (D : KCartierDivisor ℚ X) (E) :
    KCartierDivisor.toReal D E = (D E : ℝ) :=
  rfl

/-- A `ℚ`-Cartier divisor `D` on `X` is *nef over `Z`* (`f`-nef) for `f : X ⟶ Z` if
`(D · C) ≥ 0` for every integral curve `C ⊆ X` (proper over `k`) contracted by `f`. For `Z` a
point this is nefness. -/
@[mmp "def_oai4_bg_nef_ample_relative"]
def KCartierDivisor.IsRelativelyNefQ (f : X ⟶ Z) (D : KCartierDivisor ℚ X) : Prop :=
  MMP.Mori.KCartierDivisor.IsRelativelyNef sX f (KCartierDivisor.toReal D)

/-- A `ℚ`-Cartier divisor `D` on `X` is *ample over `Z`* (`f`-ample) for `f : X ⟶ Z` if some
positive multiple `mD` has integral coefficients and the Cartier divisor it defines is
`f`-ample, that is, its invertible sheaf `𝒪_X(mD)` is. For `Z` a point this is ampleness. -/
@[mmp "def_oai4_bg_nef_ample_relative"]
def KCartierDivisor.IsRelativelyAmpleQ (f : X ⟶ Z) (D : KCartierDivisor ℚ X) : Prop :=
  ∃ m : ℕ, 0 < m ∧ ∃ h : ∀ E, ∃ n : ℤ, ((m : ℚ) • D) E = n,
    MMP.Mori.IsRelativelyAmple f
      (MMP.CartierDivisor.sheaf (MMP.Mori.KCartierDivisor.realization ((m : ℚ) • D) h))

/-! ### The spaces `N¹(X)_ℝ` and `N₁(X)_ℝ` -/

/-- The `ℝ`-Cartier divisors on `X` that are *numerically trivial*: those `D` with
`(D · C) = 0` for every integral curve `C ⊆ X` proper over `k`. -/
def numericallyTrivialDivisors : Submodule ℝ (KCartierDivisor ℝ X) :=
  ⨅ C : ProperCurve sX, LinearMap.ker ((OneCycle.intersectionPairing (sX := sX)).flip
    (C.cycle ℝ))

variable {sX} in
/-- An `ℝ`-Cartier divisor is numerically trivial if and only if its intersection number with
every integral curve proper over `k` is zero. -/
theorem mem_numericallyTrivialDivisors {D : KCartierDivisor ℝ X} :
    D ∈ numericallyTrivialDivisors sX ↔
      ∀ C : ProperCurve sX, (C.cycle ℝ).intersectionNumber D = 0 := by
  simp [numericallyTrivialDivisors, OneCycle.intersectionNumber]

/-- The real vector space `N¹(X)_ℝ` of `ℝ`-Cartier divisors on `X` modulo numerical
equivalence: the quotient by the numerically trivial ones, those of degree zero on every integral
curve. Its partner `N₁(X)_ℝ` of real 1-cycles modulo numerical equivalence is
`MMP.Mori.NumericalCurveClasses`. -/
abbrev NumericalDivisorClasses : Type _ :=
  KCartierDivisor ℝ X ⧸ numericallyTrivialDivisors sX

/-- The class in `N¹(X)_ℝ` of an `ℝ`-Cartier divisor. -/
def numericalDivisorClass : KCartierDivisor ℝ X →ₗ[ℝ] NumericalDivisorClasses sX :=
  (numericallyTrivialDivisors sX).mkQ

/-- The intersection pairing `N₁(X)_ℝ → (Div(X)_ℝ → ℝ)`, `[Z] ↦ (D ↦ (Z · D))`, well defined since
numerically trivial 1-cycles have intersection number zero with every `ℝ`-Cartier divisor. -/
def curvePairing : NumericalCurveClasses sX →ₗ[ℝ] KCartierDivisor ℝ X →ₗ[ℝ] ℝ :=
  (OneCycle.numericallyTrivial sX).liftQ (OneCycle.intersectionPairing (sX := sX)).flip
    fun _ hZ => LinearMap.mem_ker.mpr <| LinearMap.ext fun D =>
      OneCycle.intersectionNumber_eq_zero_of_mem hZ D

/-- The pairing `curvePairing` evaluated on the class of a 1-cycle `Z` and a divisor `D` is the
intersection number `(Z · D)`. -/
theorem curvePairing_numericalClass (Z : OneCycle ℝ sX) (D : KCartierDivisor ℝ X) :
    curvePairing sX (OneCycle.numericalClass sX Z) D = Z.intersectionNumber D :=
  rfl

variable {sX} in
/-- A numerically trivial `ℝ`-Cartier divisor has intersection number zero with every real
1-cycle. -/
theorem intersectionNumber_eq_zero_of_mem_numericallyTrivialDivisors {D : KCartierDivisor ℝ X}
    (hD : D ∈ numericallyTrivialDivisors sX) (Z : OneCycle ℝ sX) :
    Z.intersectionNumber D = 0 := by
  rw [mem_numericallyTrivialDivisors] at hD
  induction Z using Finsupp.induction_linear with
  | zero => simp [OneCycle.intersectionNumber]
  | add Z Z' h h' =>
    simp only [OneCycle.intersectionNumber, map_add] at h h' ⊢
    rw [h, h', add_zero]
  | single C a =>
    have h := hD C
    simp only [OneCycle.intersectionNumber, ProperCurve.cycle] at h ⊢
    rw [← mul_one a, ← smul_eq_mul, ← Finsupp.smul_single, map_smul, h, smul_zero]

/-- **The intersection pairing** `N¹(X)_ℝ × N₁(X)_ℝ → ℝ`, `([D], [Z]) ↦ (D · Z)`. It separates
the points of `N¹(X)_ℝ` (`MMP.Fourfold.numericalPairing_injective`). -/
def numericalPairing : NumericalDivisorClasses sX →ₗ[ℝ] NumericalCurveClasses sX →ₗ[ℝ] ℝ :=
  (numericallyTrivialDivisors sX).liftQ (curvePairing sX).flip fun _ hD =>
    LinearMap.mem_ker.mpr <| Submodule.linearMap_qext _ <| LinearMap.ext fun Z =>
      intersectionNumber_eq_zero_of_mem_numericallyTrivialDivisors hD Z

/-- The intersection pairing of the classes of a divisor `D` and a 1-cycle `Z` is the
intersection number `(Z · D)`. -/
theorem numericalPairing_apply (D : KCartierDivisor ℝ X) (Z : OneCycle ℝ sX) :
    numericalPairing sX (numericalDivisorClass sX D) (OneCycle.numericalClass sX Z) =
      Z.intersectionNumber D :=
  rfl

/-- The pairing separates the points of `N¹(X)_ℝ`: a class pairing to zero with every curve is
zero. -/
theorem numericalPairing_injective : Function.Injective (numericalPairing sX) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro d hd
  obtain ⟨D, rfl⟩ := (numericallyTrivialDivisors sX).mkQ_surjective d
  refine (Submodule.Quotient.mk_eq_zero _).mpr (mem_numericallyTrivialDivisors.mpr fun C => ?_)
  exact LinearMap.congr_fun (LinearMap.mem_ker.mp hd) (OneCycle.numericalClass sX (C.cycle ℝ))

/-! ### Cones of curves and extremal rays -/

attribute [mmp "def_oai4_bg_cone_of_curves"] MMP.Mori.closedConeOfCurves
attribute [mmp "def_oai4_bg_extremal_ray"] MMP.Mori.IsExtremalRay

/-- An extremal ray `R` of `NE̅(X)` is *`D`-negative*, for a `ℚ`-Cartier divisor `D`, if
`(D · u) < 0` for every `0 ≠ u ∈ R`. -/
@[mmp "def_oai4_bg_extremal_ray"]
def IsNegativeExtremalRay (D : KCartierDivisor ℚ X) (R : Set (NumericalCurveClasses sX)) :
    Prop :=
  IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R ∧
    ∀ u ∈ R, u ≠ 0 → NumericalCurveClasses.intersectionNumber (KCartierDivisor.toReal D) u < 0

/-! ### Contractions -/

/-- A *contraction* `f : X ⟶ Z` is a projective surjective morphism of normal varieties over `k`
with `f_* 𝒪_X = 𝒪_Z`. -/
@[mmp "def_oai4_bg_contraction"]
structure IsContraction (sZ : Z ⟶ Spec (.of k)) (f : X ⟶ Z) : Prop where
  isNormalVariety_source : IsNormalVariety k sX
  isNormalVariety_target : IsNormalVariety k sZ
  comp_eq : f ≫ sZ = sX
  isProjectiveMorphism : IsProjectiveMorphism f
  surjective : Function.Surjective f
  /-- The map `𝒪_Z(U) → 𝒪_X(f⁻¹ U)` is an isomorphism for every open `U ⊆ Z`, that is,
  `f_* 𝒪_X = 𝒪_Z`. -/
  isIso_app : ∀ U : Z.Opens, IsIso (f.app U)

/-- A contraction is *of fibre type* if `dim Z < dim X`. -/
@[mmp "def_oai4_bg_contraction"]
def IsContraction.IsFibreType {sZ : Z ⟶ Spec (.of k)} {f : X ⟶ Z}
    (_ : IsContraction sX sZ f) : Prop :=
  topologicalKrullDim Z < topologicalKrullDim X

/-- A morphism `f : X ⟶ Z` is the *contraction of* a subset `R ⊆ N₁(X)_ℝ` (an extremal ray) if
it is a contraction contracting exactly the integral curves whose classes lie in `R`. -/
@[mmp "def_oai4_bg_contraction"]
structure IsContractionOfRay (sZ : Z ⟶ Spec (.of k)) (R : Set (NumericalCurveClasses sX))
    (f : X ⟶ Z) : Prop extends IsContraction sX sZ f where
  isContractedBy_iff : ∀ C : ProperCurve sX,
    C.IsContractedBy f ↔ OneCycle.numericalClass sX (C.cycle ℝ) ∈ R

/-! ### Pairs -/

section Pair

variable [IsLocallyNoetherian X] [IsNormal X]

/-- A *pair* `(X, B)` over `k`: `k` is algebraically closed of characteristic zero, `X` is a
normal variety over `k` and `B` is an effective `ℚ`-divisor on `X` such that `K_X + B` is
`ℚ`-Cartier. Whether `K_X + B` is `ℚ`-Cartier does not depend on the canonical divisor `K_X`
chosen (`MMP.Mori.QDivisor.isQCartier_add_iff_of_linearlyEquivalent`), so the source's
convention fixing all canonical divisors by one rational top form only selects a
representative. -/
@[mmp "def_oai4_bg_pair"]
structure IsPair (B : QDivisor X) : Prop where
  isAlgClosed : IsAlgClosed k
  /-- The field `k` has characteristic zero. -/
  charZero : CharZero k
  isPair : MMP.Mori.IsPair sX B
  nonneg : ∀ P, 0 ≤ B.coeff P

end Pair

/-! ### Small morphisms -/

/-- A proper birational morphism `f : X ⟶ Z` of normal varieties over `k` is *small* if its
exceptional locus has codimension at least two in `X` (this includes `Ex(f) = ∅`). -/
@[mmp "def_oai4_bg_small_morphism"]
structure IsSmallMorphism (sZ : Z ⟶ Spec (.of k)) (f : X ⟶ Z) : Prop where
  isNormalVariety_source : IsNormalVariety k sX
  isNormalVariety_target : IsNormalVariety k sZ
  comp_eq : f ≫ sZ = sX
  isProper : IsProper f
  isBirationalMorphism : IsBirationalMorphism f
  two_le_codimension : 2 ≤ closedsCodimension (exceptionalSet f)

/-! ### Simple normal crossing divisors -/

attribute [mmp "def_oai4_bg_snc_divisor"] MMP.Mori.DivisorWithCoeffs.IsSNC

/-- A *stratum* of a divisor `D = ∑ dⱼ Tⱼ` (an *snc stratum* when `D` is snc): an irreducible
component of an intersection `⋂_{j ∈ J} Tⱼ` of some of its prime divisors. -/
@[mmp "def_oai4_bg_snc_divisor"]
def IsSNCStratum {R : Type*} [Zero R] (D : DivisorWithCoeffs R X) (S : Set X) : Prop :=
  ∃ J ⊆ D.support,
    Maximal (fun T : Set X => IsIrreducible T ∧ T ⊆ ⋂ E ∈ J, (E.support : Set X)) S

/-! ### Log resolutions -/

/-- A *log resolution* of `(X, B)` is a projective birational morphism `π : W ⟶ X` from a smooth
variety whose exceptional locus is a divisor and such that `Ex(π) ∪ π⁻¹(Supp B)` is an snc
divisor; since `π⁻¹(Supp B) ⊆ Ex(π) ∪ π⁻¹_* Supp B`, this is the union of `Ex(π)` and the strict
transform of `Supp B`. -/
@[mmp "def_oai4_bg_log_resolution"]
structure IsLogResolution {W : Scheme.{u}} (B : QDivisor X) (π : W ⟶ X) : Prop extends
    MMP.Mori.IsLogResolution sX (QDivisor.toRDivisor B) π where
  isProjectiveMorphism : IsProjectiveMorphism π

attribute [mmp "def_oai4_bg_log_resolution"] MMP.Mori.IsCrepantBoundary

end MMP.Fourfold
