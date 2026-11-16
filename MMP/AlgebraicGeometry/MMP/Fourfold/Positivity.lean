module

public import MMP.AlgebraicGeometry.MMP.Fourfold.Defs
public import MMP.AlgebraicGeometry.Divisor.Cartier

/-!
# Big, semiample and pseudo-effective `ℚ`-Cartier divisors

For a morphism `f : X ⟶ Z` and a `ℚ`-Cartier divisor `D` on `X`: `D` is *big over `Z`* if some
positive multiple `mD` is an `f`-big Cartier divisor (the rank of `f_* 𝒪_X(kmD)` at the generic
point of `f(X)` grows like `k^{dim X - dim f(X)}`, that is, `D` is big on the generic fibre);
*semiample over `Z`* if some positive multiple `mD` is a Cartier divisor with
`f^* f_* 𝒪_X(mD) → 𝒪_X(mD)` surjective; and *pseudo-effective* if its class in `N¹(X)_ℝ` lies
in the closure of the cone spanned by the classes of effective Cartier divisors.

## Main definitions

* `MMP.Fourfold.KCartierDivisor.IsRelativelyBigQ`,
  `MMP.Fourfold.KCartierDivisor.IsRelativelySemiampleQ`.
* `MMP.Fourfold.NumericalDivisorClasses.instTopologicalSpace`: the topology of `N¹(X)_ℝ`.
* `MMP.Fourfold.effectiveCone`, `MMP.Fourfold.KCartierDivisor.IsPseudoEffectiveQ`.
* `MMP.Fourfold.RelativeNumericalDivisorClasses`,
  `MMP.Fourfold.KCartierDivisor.IsRelativelyPseudoEffective`:
  `N¹(X/Z)_ℝ` and relative pseudo-effectivity of `ℝ`-Cartier divisors.

## Implementation notes

The topology on `N¹(X)_ℝ` is the coarsest one making every `[D] ↦ (D · z)`, `z ∈ N₁(X)_ℝ`,
continuous. For a projective variety, `N¹(X)_ℝ` is finite-dimensional and the pairing with
`N₁(X)_ℝ` is perfect, so this is its vector-space topology.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

universe u

namespace MMP.Fourfold

open MMP.Mori

variable {k : Type u} [Field k] {X Z : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- A `ℚ`-Cartier divisor `D` on `X` (irreducible) is *big over `Z`* for `f : X ⟶ Z` if some
positive multiple `mD` has integral coefficients and the Cartier divisor it defines is `f`-big. -/
@[mmp "def_oai4_bg_big_pseff_semiample"]
def KCartierDivisor.IsRelativelyBigQ [IrreducibleSpace X] (f : X ⟶ Z) (D : KCartierDivisor ℚ X) :
    Prop :=
  ∃ m : ℕ, 0 < m ∧ ∃ h : ∀ E, ∃ n : ℤ, ((m : ℚ) • D) E = n,
    IsRelativelyBigCartier f (KCartierDivisor.realization ((m : ℚ) • D) h)

/-- A `ℚ`-Cartier divisor `D` on `X` is *semiample over `Z`* for `f : X ⟶ Z` if some positive
multiple `mD` has integral coefficients and the Cartier divisor it defines is `f`-generated:
`f^* f_* 𝒪_X(mD) → 𝒪_X(mD)` is surjective. -/
@[mmp "def_oai4_bg_big_pseff_semiample"]
def KCartierDivisor.IsRelativelySemiampleQ (f : X ⟶ Z) (D : KCartierDivisor ℚ X) : Prop :=
  ∃ m : ℕ, 0 < m ∧ ∃ h : ∀ E, ∃ n : ℤ, ((m : ℚ) • D) E = n,
    IsRelativelyFreeCartier f (KCartierDivisor.realization ((m : ℚ) • D) h)

/-- The topology of `N¹(X)_ℝ`: the coarsest one making every linear form `[D] ↦ (D · z)`,
`z ∈ N₁(X)_ℝ`, continuous. -/
instance NumericalDivisorClasses.instTopologicalSpace :
    TopologicalSpace (NumericalDivisorClasses sX) :=
  TopologicalSpace.induced (fun d z => numericalPairing sX d z) inferInstance

/-- The cone in `N¹(X)_ℝ` spanned by the classes of the effective Cartier divisors. -/
def effectiveCone : PointedCone ℝ (NumericalDivisorClasses sX) :=
  PointedCone.hull ℝ {d | ∃ E : X.CartierDivisor, MMP.Intersection.IsEffective E ∧
    d = numericalDivisorClass sX (KCartierDivisor.ofCartier ℝ E)}

/-- The class of an effective Cartier divisor lies in `effectiveCone`. -/
theorem numericalDivisorClass_ofCartier_mem_effectiveCone {E : X.CartierDivisor}
    (hE : MMP.Intersection.IsEffective E) :
    numericalDivisorClass sX (KCartierDivisor.ofCartier ℝ E) ∈ effectiveCone sX :=
  PointedCone.subset_hull ⟨E, hE, rfl⟩

/-- A `ℚ`-Cartier divisor `D` on `X` is *pseudo-effective* if its numerical class is a limit of
classes of effective `ℚ`-divisors: it lies in the closure of `effectiveCone`. -/
@[mmp "def_oai4_bg_big_pseff_semiample"]
def KCartierDivisor.IsPseudoEffectiveQ (D : KCartierDivisor ℚ X) : Prop :=
  numericalDivisorClass sX (KCartierDivisor.toReal D) ∈
    closure (effectiveCone sX : Set (NumericalDivisorClasses sX))

/-! ### Relative pseudo-effectivity -/

section Relative

variable (f : X ⟶ Z)

/-- The linear map `D ↦ (C ↦ (D · C))` from `ℝ`-Cartier divisors on `X` to the real functions on
the curves `C ⊆ X` (proper over `k`) contracted by `f : X ⟶ Z`. -/
def relativeDegreeMap :
    KCartierDivisor ℝ X →ₗ[ℝ] ({C : ProperCurve sX // C.IsContractedBy f} → ℝ) :=
  LinearMap.pi fun C => (OneCycle.intersectionPairing (sX := sX)).flip (C.1.cycle ℝ)

@[simp] theorem relativeDegreeMap_apply (D : KCartierDivisor ℝ X)
    (C : {C : ProperCurve sX // C.IsContractedBy f}) :
    relativeDegreeMap sX f D C = OneCycle.intersectionPairing (sX := sX) D (C.1.cycle ℝ) := rfl

/-- The real vector space `N¹(X/Z)_ℝ`: `ℝ`-Cartier divisors on `X` modulo those of degree zero
on every curve contracted by `f`. -/
abbrev RelativeNumericalDivisorClasses : Type _ :=
  KCartierDivisor ℝ X ⧸ LinearMap.ker (relativeDegreeMap sX f)

/-- The class in `N¹(X/Z)_ℝ` of an `ℝ`-Cartier divisor. -/
def relativeNumericalDivisorClass :
    KCartierDivisor ℝ X →ₗ[ℝ] RelativeNumericalDivisorClasses sX f :=
  (LinearMap.ker (relativeDegreeMap sX f)).mkQ

/-- The topology of `N¹(X/Z)_ℝ`: the coarsest one making every `[D] ↦ (D · C)`, `C` a curve
contracted by `f`, continuous. For a projective morphism of projective varieties `N¹(X/Z)_ℝ` is
finite-dimensional and this is its vector-space topology. -/
instance RelativeNumericalDivisorClasses.instTopologicalSpace :
    TopologicalSpace (RelativeNumericalDivisorClasses sX f) :=
  TopologicalSpace.induced ((LinearMap.ker (relativeDegreeMap sX f)).liftQ
    (relativeDegreeMap sX f) le_rfl) inferInstance

/-- The cone in `N¹(X/Z)_ℝ` generated by the classes of the effective `ℝ`-Cartier divisors
`∑ cⱼ Eⱼ` (`cⱼ ≥ 0`, `Eⱼ` effective Cartier divisors). -/
def relativeEffectiveCone : PointedCone ℝ (RelativeNumericalDivisorClasses sX f) :=
  PointedCone.hull ℝ {d | ∃ E : X.CartierDivisor, MMP.Intersection.IsEffective E ∧
    d = relativeNumericalDivisorClass sX f (KCartierDivisor.ofCartier ℝ E)}

/-- The class in `N¹(X/Z)_ℝ` of an effective Cartier divisor lies in `relativeEffectiveCone`. -/
theorem relativeNumericalDivisorClass_ofCartier_mem_relativeEffectiveCone
    {E : X.CartierDivisor} (hE : MMP.Intersection.IsEffective E) :
    relativeNumericalDivisorClass sX f (KCartierDivisor.ofCartier ℝ E) ∈
      relativeEffectiveCone sX f :=
  PointedCone.subset_hull ⟨E, hE, rfl⟩

/-- An `ℝ`-Cartier divisor `D` on `X` is *pseudo-effective over `Z`* for `f : X ⟶ Z` if its class
in `N¹(X/Z)_ℝ` lies in the closure of the cone generated by the effective `ℝ`-Cartier divisors. -/
@[mmp "def_fourfold_real_relative_pseudoeffective"]
def KCartierDivisor.IsRelativelyPseudoEffective (D : KCartierDivisor ℝ X) : Prop :=
  relativeNumericalDivisorClass sX f D ∈
    closure (relativeEffectiveCone sX f : Set (RelativeNumericalDivisorClasses sX f))

end Relative

end MMP.Fourfold
