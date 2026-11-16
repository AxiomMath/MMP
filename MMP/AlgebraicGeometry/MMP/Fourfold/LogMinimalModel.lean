module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.DltProgram
public import MMP.AlgebraicGeometry.MMP.Fourfold.Positivity
public import MMP.AlgebraicGeometry.Singularities.LogResolution.ReducedUnion

/-!
# Log minimal models, good log minimal models and Mori fibre spaces

Let `(X/Z, B)` be an lc pair projective over `Z`. Following Birkar, a *log minimal model* of
`(X/Z, B)` is a pair `(M/Z, B_M)` together with a birational map `φ : X ⤏ M` over `Z` such that
`B_M = φ_* B + ∑ F`, the sum running over the prime divisors `F` of `M` exceptional over `X`,
`(M, B_M)` is `ℚ`-factorial dlt, `K_M + B_M` is nef over `Z`, and `a(D; X, B) < a(D; M, B_M)` for
every prime divisor `D` of `X` contracted by `φ`. It is *good* if `K_M + B_M` is semiample over
`Z`. A *Mori fibre space* of `(X/Z, B)` is defined in the same way, the nefness of `K_M + B_M`
being replaced by a `(K_M + B_M)`-negative extremal contraction `M ⟶ M'` over `Z` with
`dim M' < dim M`.

## Main definitions

* `MMP.Fourfold.QDivisor.IsRelativelySemiample`: semiampleness over `Z` of a `ℚ`-divisor.
* `MMP.Fourfold.IsLogBirationalModelOver`: the data common to log minimal models and Mori fibre
  spaces of an lc pair.
* `MMP.Fourfold.IsLogMinimalModel`, `MMP.Fourfold.IsGoodLogMinimalModel`,
  `MMP.Fourfold.IsMoriFibreSpaceModel`: log minimal models (Birkar), good ones, and Mori fibre
  spaces of an lc pair.

## Implementation notes

* Divisors of `M` exceptional over `X` are the `φ⁻¹`-exceptional prime divisors
  (`MMP.Flips.RationalMap.IsInverseExceptional`): those that are not the birational transform of a
  prime divisor of `X`. A prime divisor of `X` is *contracted by `φ`* when it is `φ`-exceptional
  (`MMP.Mori.RationalMap.IsExceptional`).
* `a(D; X, B)` is the log discrepancy of `D` regarded as a divisor over `X`
  (`MMP.Mori.DivisorOver.ofPrimeDivisor`), and `a(D; M, B_M)` is the log discrepancy of any divisor
  over `M` realizing `D` through a birational inverse `M ⤏ X` of `φ` (`MMP.Flips.IsRealizedOver`).
  As in `MMP.Intersection.IsLogCanonicalPair`, a log discrepancy is a predicate on its value and
  the inequality is required of all values.
* The canonical divisor `K_M` is any canonical divisor of `M`: nefness, semiampleness and
  negativity of `K_M + B_M` only depend on its linear equivalence class.
* All notions are stated over an arbitrary field `k`.

## References

* [C. Birkar, *Existence of log canonical flips and a special LMMP*][BirkarLC], Section 2
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori

/-! ### Relative semiampleness of `ℚ`-divisors -/

section Semiample

variable {X Z : Scheme.{u}} [IsLocallyNoetherian X]

/-- A `ℚ`-divisor `D` on `X` is *semiample over `Z`* for `f : X ⟶ Z` if it is the Weil
`ℚ`-divisor of a `ℚ`-Cartier divisor `C = ∑ cⱼ Cⱼ` (`coeff_P D = ∑ cⱼ ord_P Cⱼ` for every prime
divisor `P`) which is semiample over `Z` (`MMP.Fourfold.KCartierDivisor.IsRelativelySemiampleQ`).
-/
def QDivisor.IsRelativelySemiample (f : X ⟶ Z) (D : QDivisor X) : Prop :=
  ∃ C : KCartierDivisor ℚ X,
    (∀ P : MMP.Mori.PrimeDivisor X,
      D.coeff P = C.sum fun E c => c * (MMP.Intersection.primeDivisorOrder P E : ℚ)) ∧
    KCartierDivisor.IsRelativelySemiampleQ f C

end Semiample

/-! ### Log minimal models and Mori fibre spaces of lc pairs -/

section LogMinimalModel

variable {k : Type u} [Field k] {X Z M : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  (sZ : Z ⟶ Spec (.of k)) (sM : M ⟶ Spec (.of k))
  [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [LocallyOfFiniteType sX]
  [IsIntegral M] [CompactSpace M] [IsLocallyNoetherian M] [IsNormal M] [LocallyOfFiniteType sM]
  [QuasiCompact sM]

open Classical in
/-- The data shared by a log minimal model and a Mori fibre space of an lc pair `(X/Z, B)`
projective over `Z` (by `π`). The pair `(M/Z, B_M)`, with `π_M : M ⟶ Z` projective and canonical
divisor `K_M`, and the birational map `φ : X ⤏ M` over `Z` satisfy:

* `B_M` is the birational transform `φ_* B` plus the reduced sum of the prime divisors of `M`
  exceptional over `X`;
* `(M, B_M)` is a `ℚ`-factorial dlt pair;
* `a(D; X, B) < a(D; M, B_M)` for every prime divisor `D` of `X` contracted by `φ`, where
  `a(D; M, B_M)` is computed on any divisor over `M` realizing `D` through a birational inverse
  `ψ : M ⤏ X` of `φ`. -/
structure IsLogBirationalModelOver (π : X ⟶ Z) (πM : M ⟶ Z) (B : QDivisor X) (KM : Divisor M)
    (BM : QDivisor M) (φ : X.RationalMap M) : Prop where
  isNormalVariety : IsNormalVariety k sX
  isLogCanonicalPair : MMP.Intersection.IsLogCanonicalPair sX B
  comp_eq : π ≫ sZ = sX
  isProjectiveMorphism : IsProjectiveMorphism π
  comp_eq_model : πM ≫ sZ = sM
  isProjectiveMorphism_model : IsProjectiveMorphism πM
  isBirational : MMP.Mori.RationalMap.IsBirational φ
  isOver : MMP.Flips.RationalMap.IsOver π πM φ
  coeff_boundary : ∀ F : MMP.Mori.PrimeDivisor M,
    BM.coeff F = (MMP.Mori.RationalMap.transformDivisor φ B).coeff F +
      if MMP.Flips.RationalMap.IsInverseExceptional φ F then 1 else 0
  isQFactorial : IsQFactorial sM
  isDltPair : MMP.Intersection.IsDltPair sM BM
  isCanonicalDivisor : ∃ n : ℕ, KM.IsCanonicalDivisor sM n
  logDiscrepancy_lt : ∀ D : MMP.Mori.PrimeDivisor X, MMP.Mori.RationalMap.IsExceptional φ D →
    ∀ (ψ : M.RationalMap X), MMP.Mori.RationalMap.IsInverse φ ψ →
    ∀ (E : MMP.Flips.ProperDivisorOver k sM), MMP.Flips.IsRealizedOver sM ψ D E →
    ∀ (n : ℕ) (a a' : ℝ),
      MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B)
        (DivisorOver.ofPrimeDivisor k isNormalVariety D) a →
      MMP.Intersection.IsLogDiscrepancy sM n (QDivisor.toRDivisor BM) E.toDivisorOver a' →
      a < a'

/-- **Log minimal model** (Birkar). Let `(X/Z, B)` be an lc pair projective over `Z` (by `π`).
A pair `(M/Z, B_M)` (by `π_M`, with canonical divisor `K_M`) with a birational map `φ : X ⤏ M`
over `Z` is a *log minimal model* of `(X/Z, B)` if `B_M` is the birational transform of `B` plus
the reduced sum of the prime divisors of `M` exceptional over `X`, `(M, B_M)` is `ℚ`-factorial
dlt, `K_M + B_M` is nef over `Z`, and `a(D; X, B) < a(D; M, B_M)` for every prime divisor `D` of
`X` contracted by `φ`. -/
@[mmp "def_oai4_bg_log_minimal_model"]
structure IsLogMinimalModel (π : X ⟶ Z) (πM : M ⟶ Z) (B : QDivisor X) (KM : Divisor M)
    (BM : QDivisor M) (φ : X.RationalMap M) : Prop extends
    IsLogBirationalModelOver sX sZ sM π πM B KM BM φ where
  isRelativelyNef : QDivisor.IsRelativelyNef sM πM (Divisor.toQDivisor KM + BM)

/-- **Good log minimal model** (Birkar). A log minimal model `(M/Z, B_M)` of `(X/Z, B)` is *good*
if `K_M + B_M` is semiample over `Z`. -/
@[mmp "def_oai4_bg_log_minimal_model"]
structure IsGoodLogMinimalModel (π : X ⟶ Z) (πM : M ⟶ Z) (B : QDivisor X) (KM : Divisor M)
    (BM : QDivisor M) (φ : X.RationalMap M) : Prop extends
    IsLogMinimalModel sX sZ sM π πM B KM BM φ where
  isRelativelySemiample : QDivisor.IsRelativelySemiample πM (Divisor.toQDivisor KM + BM)

/-- **Mori fibre space of an lc pair** (Birkar). Let `(X/Z, B)` be an lc pair projective over `Z`.
A pair `(M/Z, B_M)` with a birational map `φ : X ⤏ M` over `Z` is a *Mori fibre space* of
`(X/Z, B)`, with fibre-type contraction `g : M ⟶ M'` (`g_Z : M' ⟶ Z`), if it satisfies the
conditions of a log minimal model except nefness (`MMP.Fourfold.IsLogBirationalModelOver`) and,
instead, `g` is the contraction over `Z` of a `(K_M + B_M)`-negative extremal ray `R` of
`NE̅(M/Z)` with `dim M' < dim M`. -/
@[mmp "def_oai4_bg_log_minimal_model"]
structure IsMoriFibreSpaceModel {M' : Scheme.{u}} (sM' : M' ⟶ Spec (.of k)) (π : X ⟶ Z)
    (πM : M ⟶ Z) (B : QDivisor X) (KM : Divisor M) (BM : QDivisor M) (φ : X.RationalMap M)
    (R : Set (RelativeNumericalCurveClasses sM πM)) (g : M ⟶ M') (gZ : M' ⟶ Z) : Prop extends
    IsLogBirationalModelOver sX sZ sM π πM B KM BM φ where
  /-- `g` is the contraction over `Z` of the `(K_M + B_M)`-negative extremal ray `R`. -/
  isNegativeRelativeRayContraction :
    IsNegativeRelativeRayContraction sM πM sM' (Divisor.toQDivisor KM + BM) R g gZ
  /-- The base `M'` has strictly smaller dimension than `M`. -/
  dim_lt : topologicalKrullDim M' < topologicalKrullDim M

end LogMinimalModel

end MMP.Fourfold
