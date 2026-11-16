module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.LogMinimalModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
public import MMP.AlgebraicGeometry.MMP.Models
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Charts.Descent
public import StacksFrontier.AlgebraicGeometry.RelativeProj.DegreeZeroFiniteType
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# Relative ample models and ample-model data

Let `π : M ⟶ Z` be a projective morphism of normal varieties and `L` a `ℚ`-Cartier divisor on
`M` which is semiample over `Z`; fix `k > 0` such that `kL` is Cartier and `π`-generated. The
*relative ample model* of `L` over `Z` is

`V = Proj_Z ⨁_{n ≥ 0} π_* 𝒪_M(nkL)`,

together with the induced morphism `q : M ⟶ V` over `Z`. On the open `M_a ⊆ π⁻¹(U)` where a
section `a ∈ H⁰(π⁻¹U, 𝒪_M(nkL))`, `n > 0`, generates `𝒪_M(nkL)`, the morphism `q` lands in the
basic open `D₊(a)` of the chart `Proj ⨁_m H⁰(π⁻¹U, 𝒪_M(mkL))` over an affine open `U ⊆ Z`, and is
given there by the ring map `t / aᵐ ↦ t / aᵐ` into the regular functions on `M_a`.

Let `(X, B)` be a projective lc fourfold pair over `ℂ` with rational boundary, `D = K_X + B`, and
`f : X ⟶ Z` a birational contraction onto a normal projective variety with `-D` `f`-ample. An
*ample-model datum* for `f` is a tuple `(M, B_M, q, V, B_V)` where `(M, B_M)` is a log minimal
model of `(X/Z, B)` with `K_M + B_M` semiample over `Z`, `q : M ⟶ V` is the relative ample model
of `K_M + B_M` over `Z`, and `B_V = q_* B_M`.

## Main definitions

* `MMP.Fourfold.DivisorialSectionAlgebra`: a quasi-coherent graded `𝒪_Z`-algebra together with an
  identification of its degree-`n` sections over every open `U ⊆ Z` with
  `H⁰(π⁻¹U, 𝒪_M(nD))`, compatible with restriction, the `𝒪_Z`-module structures, products and
  the unit; that is, a presentation of `⨁_{n ≥ 0} π_* 𝒪_M(nD)` as a graded `𝒪_Z`-algebra.
* `MMP.Fourfold.DivisorialSectionAlgebra.model`, `MMP.Fourfold.DivisorialSectionAlgebra.toBase`:
  its relative `Proj` and the structure morphism to `Z`.
* `MMP.Fourfold.DivisorialSectionAlgebra.generatingLocus`: the open `M_a` where a homogeneous
  section `a` generates `𝒪_M(nD)`.
* `MMP.Fourfold.DivisorialSectionAlgebra.IsInducedMorphism`: `q : M ⟶ Proj_Z` is the morphism
  induced by the algebra.
* `MMP.Fourfold.IsRelativeAmpleModel`: `(V, q)` is the relative ample model of `L` over `Z`.
* `MMP.Fourfold.IsAmpleModelDatum`: ample-model data of a birational contraction.

## Implementation notes

* `Proj_Z` is the Stacks project's relative `Proj` of a quasi-coherent, commutative,
  nonnegatively graded `𝒪_Z`-algebra (`Stacks.RelativeProj.Situation.relativeProj`, Tag 01NQ),
  glued from the projective spectra `Proj ⨁_n 𝒜_n(U)` over the affine opens `U` of `Z`. The
  graded algebra `⨁_n π_* 𝒪_M(nD)` is not constructed as such a sheaf: it is given by a
  `MMP.Fourfold.DivisorialSectionAlgebra`, a graded `𝒪_Z`-algebra with an isomorphism of graded
  `𝒪_Z`-algebras onto `⨁_n π_* 𝒪_M(nD)`, described on sections over each open `U ⊆ Z` through
  `𝒪_M(nD)(π⁻¹U) ⊆ 𝒦_M(π⁻¹U)` (`MMP.Mori.Divisor.divisorialSubmodule`). Any two such
  presentations are isomorphic graded algebras, so their relative `Proj` agree up to isomorphism
  over `Z`, and the relative ample model is a property of `(V, q)` up to isomorphism over `Z`.
* `𝒪_M(nkL)` is the divisorial sheaf of the Weil divisor `nD`, `D = kL`; for `D` Cartier on the
  normal scheme `M` it is the invertible sheaf of the Cartier divisor `nD`. That `D` is
  `π`-generated is `MMP.Fourfold.IsRelativelyFreeDivisor`.
* The morphism `q` induced by the algebra is characterised chart by chart: for every affine open
  `U ⊆ Z`, every `n > 0` and every `a ∈ 𝒜_n(U)`, the restriction of `q` to the generating locus
  `M_a` factors through the basic open `D₊(a)` of the chart over `U`, by the morphism
  `M_a ⟶ Spec 𝒜(U)_(a)` of a ring map `ψ` with `ψ(t / aᵐ) · aᵐ = t` in `𝒦_M(M_a)` for every
  `t ∈ 𝒜_{mn}(U)`. On an integral `M` the rational functions determine regular functions, so
  `ψ` is unique; the `M_a` with `n = 1` cover `M` because `D` is `π`-generated, so `q` is unique.
  This is the construction of the morphism `M ⟶ Proj_Z ⨁ π_* 𝒪_M(nD)` from the surjection
  `π^* π_* 𝒪_M(D) → 𝒪_M(D)` (Stacks, Section 01NS), written out on charts.
* The integer `k` is existentially quantified: the relative ample model does not depend on the
  choice of `k` (a Veronese subalgebra has the same relative `Proj`).
* The relative ample model is defined for any morphism `π : M ⟶ Z` from a locally Noetherian
  normal scheme; projectivity and the variety hypotheses of the source are not needed to state
  it. In the ample-model datum they are part of the log minimal model.
* The push-forward `B_V = q_* B_M` of a `ℚ`-divisor along the morphism `q` is its birational
  transform `MMP.Mori.RationalMap.transformDivisor` under `q` regarded as a rational map: the
  prime divisors of `M` mapped onto a prime divisor of `V` keep their coefficient, the ones
  contracted by `q` are dropped. For the birational morphism `q` this is the push-forward of
  cycles.
* The canonical divisors `K_X`, `K_M` are carried explicitly, as in
  `MMP.Fourfold.IsLogMinimalModel`, and `D = K_X + B`; the `f`-ampleness of `-D` is
  `MMP.Mori.QDivisor.HasRelativelyAmpleMultiple`.

## References

* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01NS](https://stacks.math.columbia.edu/tag/01NS)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori

/-! ### The graded algebra `⨁_{n ≥ 0} π_* 𝒪_M(nD)` -/

section SectionAlgebra

variable {M Z : Scheme.{u}} [IsLocallyNoetherian M] [IsNormal M]

/-- A presentation of the graded `𝒪_Z`-algebra `⨁_{n ≥ 0} π_* 𝒪_M(nD)` of a divisor `D` on `M`
along `π : M ⟶ Z`: a commutative graded `𝒪_Z`-algebra `𝒜`, vanishing in negative degrees, with
quasi-coherent homogeneous pieces, and for every `n ≥ 0` and every open `U ⊆ Z` an isomorphism
`𝒜_n(U) ≅ H⁰(π⁻¹U, 𝒪_M(nD)) ⊆ 𝒦_M(π⁻¹U)` which commutes with restriction, is `𝒪_Z(U)`-linear
(through `π^# : 𝒪_Z(U) → 𝒪_M(π⁻¹U)`), and sends products to products of rational functions and
the unit to `1`. -/
@[mmp "def_oai4_relative_ample_model"]
structure DivisorialSectionAlgebra (π : M ⟶ Z) (D : Divisor M) where
  /-- The graded `𝒪_Z`-algebra. -/
  algebra : SheafOfModules.GradedAlgebra Z.ringCatSheaf
  /-- Homogeneous multiplication is commutative. -/
  mul_comm (i j : ℤ) (U : (Opens Z)ᵒᵖ)
      (a : (algebra.piece i).val.obj U) (b : (algebra.piece j).val.obj U) :
    HEq ((algebra.mul i j).app U a b) ((algebra.mul j i).app U b a)
  /-- Negative homogeneous pieces vanish. -/
  negative_isZero (n : ℤ) (hn : n < 0) : Limits.IsZero (algebra.piece n)
  /-- Every homogeneous piece is quasi-coherent. -/
  isQuasicoherent (n : ℤ) : (algebra.piece n).IsQuasicoherent
  /-- The identification `𝒜_i(U) ≅ H⁰(π⁻¹U, 𝒪_M(iD))` for `i ≥ 0`. -/
  sectionEquiv (i : ℤ) (hi : 0 ≤ i) (U : Z.Opens) :
    (algebra.piece i).val.obj (op U) ≃+ (i • D).divisorialSubmodule (π ⁻¹ᵁ U)
  /-- The identification commutes with restriction. -/
  sectionEquiv_restrict (i : ℤ) (hi : 0 ≤ i) {U V : Z.Opens} (h : V ≤ U)
      (a : (algebra.piece i).val.obj (op U)) :
    sectionEquiv i hi V ((algebra.piece i).val.map (homOfLE h).op a) =
      (i • D).divisorialRestrict (homOfLE (π.preimage_mono h)) (sectionEquiv i hi U a)
  /-- The identification is `𝒪_Z(U)`-linear. -/
  sectionEquiv_smul (i : ℤ) (hi : 0 ≤ i) (U : Z.Opens) (r : Z.ringCatSheaf.obj.obj (op U))
      (a : (algebra.piece i).val.obj (op U)) :
    sectionEquiv i hi U (r • a) = π.app U r • sectionEquiv i hi U a
  /-- The identification is multiplicative. -/
  sectionEquiv_mul (i j : ℤ) (hi : 0 ≤ i) (hj : 0 ≤ j) (U : Z.Opens)
      (a : (algebra.piece i).val.obj (op U)) (b : (algebra.piece j).val.obj (op U)) :
    (sectionEquiv (i + j) (add_nonneg hi hj) U ((algebra.mul i j).app (op U) a b) :
        (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U))) =
      (sectionEquiv i hi U a : (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U))) *
        (sectionEquiv j hj U b : (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U)))
  /-- The identification sends the unit to `1`. -/
  sectionEquiv_one (U : Z.Opens) :
    ((sectionEquiv 0 le_rfl U (algebra.one.eval (op U)) :
        (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U))) = 1)

namespace DivisorialSectionAlgebra

variable {π : M ⟶ Z} {D : Divisor M} (A : DivisorialSectionAlgebra π D)

/-- The relative `Proj` situation of the algebra: the base `Z` with the graded algebra `𝒜`. -/
abbrev situation : Stacks.RelativeProj.Situation.{u} where
  base := Z
  algebra := A.algebra
  mul_comm := A.mul_comm
  negative_isZero := A.negative_isZero
  isQuasicoherent := A.isQuasicoherent

/-- The relative `Proj` `Proj_Z ⨁_{n ≥ 0} π_* 𝒪_M(nD)`. -/
@[mmp "def_oai4_relative_ample_model"]
def model : Scheme.{u} :=
  A.situation.relativeProj

/-- The structure morphism `Proj_Z ⨁_{n ≥ 0} π_* 𝒪_M(nD) ⟶ Z`. -/
def toBase : A.model ⟶ Z :=
  A.situation.relativeProjToBase

/-- The *generating locus* `M_a ⊆ π⁻¹U` of a section `a ∈ 𝒜_i(U) = H⁰(π⁻¹U, 𝒪_M(iD))`: the
union of the opens `W ⊆ π⁻¹U` on which `a` has an inverse in `H⁰(W, 𝒪_M(-iD))`, that is, on
which `a` generates `𝒪_M(iD)`. -/
def generatingLocus {i : ℤ} (hi : 0 ≤ i) {U : Z.Opens}
    (a : (A.algebra.piece i).val.obj (op U)) : M.Opens :=
  sSup {W : M.Opens | ∃ h : W ≤ π ⁻¹ᵁ U, ∃ b ∈ (-(i • D)).divisorialSubmodule W,
    (rationalFunctionsPresheaf M).map (homOfLE h).op
      (A.sectionEquiv i hi U a : (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U))) * b = 1}

/-- The generating locus `M_a` of a section `a ∈ 𝒜_i(U)` is contained in `π⁻¹U`. -/
theorem generatingLocus_le {i : ℤ} (hi : 0 ≤ i) {U : Z.Opens}
    (a : (A.algebra.piece i).val.obj (op U)) : A.generatingLocus hi a ≤ π ⁻¹ᵁ U :=
  sSup_le fun _ ⟨h, _⟩ => h

/-- A morphism `q : M ⟶ Proj_Z ⨁_{n ≥ 0} π_* 𝒪_M(nD)` is *the morphism induced by the
algebra* if it lies over `Z` and, for every affine open `U ⊆ Z`, every `n > 0` and every
`a ∈ 𝒜_n(U)`, its restriction to the generating locus `M_a` factors through the basic open
`D₊(a)` of the chart `Proj ⨁_m 𝒜_m(U)` over `U`, as the morphism `M_a ⟶ Spec 𝒜(U)_(a)` of a ring
map `ψ : 𝒜(U)_(a) → 𝒪_M(M_a)` sending `t / aᵐ` (`t ∈ 𝒜_{mn}(U)`) to the regular function whose
product with `aᵐ` is `t` in `𝒦_M(M_a)`. -/
@[mmp "def_oai4_relative_ample_model"]
structure IsInducedMorphism (q : M ⟶ A.model) : Prop where
  comp_toBase : q ≫ A.toBase = π
  factors (U : Z.affineOpens) (n : ℕ) (hn : 0 < n)
      (a : (A.algebra.piece (n : ℤ)).val.obj (op U.1)) :
    ∃ ψ : HomogeneousLocalization.Away (A.situation.sectionRingGrading U.1)
        (DirectSum.of (A.situation.sectionPieces U.1) n a) →+*
        Γ(M, A.generatingLocus (Int.natCast_nonneg n) a),
      (A.generatingLocus (Int.natCast_nonneg n) a).ι ≫ q =
          (A.generatingLocus (Int.natCast_nonneg n) a).toSpecΓ ≫
            Spec.map (CommRingCat.ofHom ψ) ≫
            Proj.awayι (A.situation.sectionRingGrading U.1)
              (DirectSum.of (A.situation.sectionPieces U.1) n a) ⟨a, rfl⟩ hn ≫
            A.situation.relativeProjChart U ∧
        ∀ (m : ℕ) (t : (A.algebra.piece ((m • n : ℕ) : ℤ)).val.obj (op U.1)),
          (toRationalFunctionsPresheaf M).app (op (A.generatingLocus (Int.natCast_nonneg n) a))
              (ψ (HomogeneousLocalization.Away.mk (A.situation.sectionRingGrading U.1) ⟨a, rfl⟩ m
                (DirectSum.of (A.situation.sectionPieces U.1) (m • n) t) ⟨t, rfl⟩)) *
              (rationalFunctionsPresheaf M).map
                (homOfLE (A.generatingLocus_le _ a)).op
                (A.sectionEquiv n (Int.natCast_nonneg n) U.1 a :
                  (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U.1))) ^ m =
            (rationalFunctionsPresheaf M).map (homOfLE (A.generatingLocus_le _ a)).op
              (A.sectionEquiv _ (Int.natCast_nonneg _) U.1 t :
                (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U.1)))

end DivisorialSectionAlgebra

end SectionAlgebra

/-! ### Relative ample models -/

section AmpleModel

variable {M Z V : Scheme.{u}} [IsLocallyNoetherian M] [IsNormal M]

/-- **Relative ample model.** For `π : M ⟶ Z` and a `ℚ`-divisor `L` on `M`, `p : V ⟶ Z` with
`q : M ⟶ V` is the *relative ample model* of `L` over `Z` if, for some `k > 0` such that
`D = kL` is a Cartier divisor which is `π`-generated (`π^* π_* 𝒪_M(D) → 𝒪_M(D)` surjective, so
`L` is semiample over `Z`), `V` is isomorphic over `Z` to `Proj_Z ⨁_{n ≥ 0} π_* 𝒪_M(nD)`, by an
isomorphism carrying `q` to the morphism induced by the algebra. -/
@[mmp "def_oai4_relative_ample_model"]
def IsRelativeAmpleModel (π : M ⟶ Z) (L : QDivisor M) (p : V ⟶ Z) (q : M ⟶ V) : Prop :=
  ∃ k : ℕ, 0 < k ∧ ∃ D : Divisor M, Divisor.toQDivisor D = (k : ℚ) • L ∧ D.IsCartier ∧
    IsRelativelyFreeDivisor π D ∧ ∃ (A : DivisorialSectionAlgebra π D) (e : V ≅ A.model),
      e.hom ≫ A.toBase = p ∧ A.IsInducedMorphism (q ≫ e.hom)

end AmpleModel

/-! ### Ample-model data of birational contractions -/

section AmpleModelDatum

variable {X Z M V : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
  [IsNormal X] [IsIntegral M] [CompactSpace M] [IsLocallyNoetherian M] [IsNormal M]

/-- **Ample-model datum of a birational contraction.** Let `(X, B)` be a projective lc fourfold
pair over `ℂ` with rational boundary `B` and canonical divisor `K`, `D = K + B`, and `f : X ⟶ Z`
a birational contraction onto a normal projective variety with `-D` `f`-ample. The tuple
`(M, B_M, q, V, B_V)` (with `π_M : M ⟶ Z`, the birational map `φ : X ⤏ M`, the canonical divisor
`K_M` and `p : V ⟶ Z`) is an *ample-model datum* for `f` if `(M, B_M)` is a log minimal model of
`(X/Z, B)` with `K_M + B_M` semiample over `Z` (a good log minimal model), `q : M ⟶ V` is the
relative ample model of `K_M + B_M` over `Z`, and `B_V = q_* B_M`. -/
@[mmp "def_oai4_c3_ample_model_datum"]
structure IsAmpleModelDatum (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ))
    (sM : M ⟶ Spec (.of ℂ)) [QuasiCompact sM] (K : Divisor X) (B : QDivisor X) (f : X ⟶ Z)
    (KM : Divisor M) (BM : QDivisor M) (φ : X.RationalMap M) (πM : M ⟶ Z) (q : M ⟶ V)
    (p : V ⟶ Z) (BV : QDivisor V) : Prop where
  /-- `X` is a projective variety over `ℂ`. -/
  isProjectiveVariety : MMP.Mori.IsProjectiveVariety ℂ sX
  /-- `X` has dimension `4`. -/
  dim_eq : topologicalKrullDim X = 4
  /-- `(X, B)` is a log canonical pair. -/
  isLogCanonicalPair : MMP.Intersection.IsLogCanonicalPair sX B
  /-- `K` is a canonical divisor of `X`. -/
  isCanonicalDivisor : ∃ n : ℕ, K.IsCanonicalDivisor sX n
  /-- `f` is a contraction. -/
  isContraction : IsContraction sX sZ f
  /-- `f` is birational. -/
  isBirationalMorphism : IsBirationalMorphism f
  /-- `Z` is a projective variety over `ℂ`. -/
  isProjectiveVariety_target : MMP.Mori.IsProjectiveVariety ℂ sZ
  /-- A positive multiple of `-(K + B)` is `f`-ample. -/
  hasRelativelyAmpleMultiple : (-(Divisor.toQDivisor K + B)).HasRelativelyAmpleMultiple f
  /-- `(M, B_M)` is a good log minimal model of `(X/Z, B)`. -/
  isGoodLogMinimalModel : IsGoodLogMinimalModel sX sZ sM f πM B KM BM φ
  /-- `q : M ⟶ V` is the relative ample model of `K_M + B_M` over `Z`. -/
  isRelativeAmpleModel : IsRelativeAmpleModel πM (Divisor.toQDivisor KM + BM) p q
  /-- `B_V = q_* B_M`. -/
  boundary_eq : BV = RationalMap.transformDivisor (X := M) q.toRationalMap BM

end AmpleModelDatum

end MMP.Fourfold
