module

public import MMP.AlgebraicGeometry.MMP.Fourfold.Defs
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancy

/-!
# Steps of the minimal model program in the fourfold source

The fourfold source runs the minimal model program for projective lc pairs `(X, B)` with an
explicit list of *permitted steps*: the contraction `f : X ⟶ Z` of a `(K_X + B)`-negative
extremal ray with `ρ(X/Z) = 1`, followed by a small projective birational `f⁺ : X⁺ ⟶ Z` (a flip,
or `f` itself when `f` is small, or an isomorphism) such that `K_{X⁺} + B⁺` is `f⁺`-ample. A run
ends with a *Mori fibre space*. The relative Picard number of the source is the codimension of
`f^* N¹(Z)_ℝ` in `N¹(X)_ℝ`.

## Main definitions

* `MMP.Fourfold.IsQFactorial`: `ℚ`-factorial normal varieties.
* `MMP.Fourfold.pullbackNumericalClasses`, `MMP.Fourfold.relativePicardNumberN1`: `f^* N¹(Z)_ℝ`
  and `ρ(X/Z) = dim_ℝ N¹(X)_ℝ / f^* N¹(Z)_ℝ`.
* `MMP.Fourfold.QDivisor.curveForm`: the linear form `z ↦ (D · z)` on `N₁(X)_ℝ` of a
  `ℚ`-Cartier `ℚ`-divisor `D`.
* `MMP.Fourfold.IsNegativeExtremalRayOf`: a `D`-negative extremal ray, for a `ℚ`-Cartier
  `ℚ`-divisor `D`.
* `MMP.Fourfold.IsMoriFibreSpace`: a Mori fibre space structure on a projective lc pair.
* `MMP.Fourfold.IsPermittedStep`: a permitted step of the program.
* `MMP.Fourfold.Program`, `MMP.Fourfold.Program.IsMaximal`: programs and maximal programs.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori

variable {k : Type u} [Field k] {X Z : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-! ### `ℚ`-factoriality -/

section QFactorial

variable [IsLocallyNoetherian X] [IsNormal X]

/-- A normal variety `X` is *`ℚ`-factorial* if every Weil divisor `D` on `X` has a positive
integral multiple `mD` that is Cartier. -/
@[mmp "def_mmp_q_factorial"]
def IsQFactorial : Prop :=
  IsNormalVariety k sX ∧ ∀ D : Divisor X, ∃ m : ℕ, 0 < m ∧ ((m : ℤ) • D).IsCartier

end QFactorial

/-! ### The relative Picard number -/

/-- The subspace `f^* N¹(Z)_ℝ ⊆ N¹(X)_ℝ` for `f : X ⟶ Z`: the span of the classes of the Cartier
divisors `E` on `X` whose invertible sheaf `𝒪_X(E)` is the pull-back `f^* M` of an invertible
sheaf `M` on `Z`. For `X` integral every invertible sheaf on `X` is some `𝒪_X(E)`, so these are
the classes of the pull-backs `f^* D'` of the Cartier divisors `D'` on `Z`. -/
def pullbackNumericalClasses (f : X ⟶ Z) : Submodule ℝ (NumericalDivisorClasses sX) :=
  Submodule.span ℝ {d | ∃ (E : X.CartierDivisor) (M : Z.Modules)
    (_ : SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 M),
    Nonempty (MMP.CartierDivisor.sheaf E ≅ (Scheme.Modules.pullback f).obj M) ∧
      d = numericalDivisorClass sX (MMP.Mori.KCartierDivisor.ofCartier ℝ E)}

/-- The relative Picard number of the fourfold source, for a morphism `f : X ⟶ Z`:
`ρ(X/Z) = dim_ℝ (N¹(X)_ℝ / f^* N¹(Z)_ℝ) ∈ ℕ ∪ {∞}`. -/
@[mmp "def_oai4_bg_relative_picard_number"]
def relativePicardNumberN1 (f : X ⟶ Z) : ℕ∞ :=
  (Module.rank ℝ (NumericalDivisorClasses sX ⧸ pullbackNumericalClasses sX f)).toENat

/-! ### Negative extremal rays of `ℚ`-Cartier `ℚ`-divisors -/

section WeilForm

variable [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]

/-- The linear form `z ↦ (D · z)` on `N₁(X)_ℝ` of a `ℚ`-Cartier `ℚ`-divisor `D` on a normal
scheme: for the associated `ℚ`-Cartier divisor `⟨D⟩ = ∑ cⱼ Dⱼ` (`Dⱼ` Cartier divisors), the
form `∑ cⱼ deg 𝒪_X(Dⱼ)`. -/
def QDivisor.curveForm (D : QDivisor X) (h : D.IsQCartier) :
    NumericalCurveClasses sX →ₗ[ℝ] ℝ :=
  (D.associatedCartier h).sum fun E c =>
    haveI := (Divisor.mem_cartierSubgroup.mp E.2).isInvertibleModule_divisorialSheaf
    (c : ℝ) • NumericalCurveClasses.degree sX (E : Divisor X).divisorialSheaf

/-- An extremal ray `R` of `NE̅(X)` is *`D`-negative*, for a `ℚ`-Cartier `ℚ`-divisor `D`, if
`(D · u) < 0` for every `0 ≠ u ∈ R`. -/
def IsNegativeExtremalRayOf (D : QDivisor X) (R : Set (NumericalCurveClasses sX)) : Prop :=
  ∃ h : D.IsQCartier,
    IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R ∧
      ∀ u ∈ R, u ≠ 0 → QDivisor.curveForm sX D h u < 0

/-- A `ℚ`-Cartier `ℚ`-divisor `D` is *nef* if `(D · C) ≥ 0` for every integral curve `C ⊆ X`
proper over `k`. -/
def QDivisor.IsNefOnCurves (D : QDivisor X) : Prop :=
  ∃ h : D.IsQCartier, ∀ C : ProperCurve sX,
    0 ≤ QDivisor.curveForm sX D h (OneCycle.numericalClass sX (C.cycle ℝ))

end WeilForm

/-! ### Mori fibre spaces -/

section MoriFibreSpace

variable [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {T : Scheme.{u}}

/-- A *Mori fibre space structure* on a projective lc pair `(X, B)`, with canonical divisor `K`:
a projective surjective morphism `g : X ⟶ T` onto a normal projective variety `T` with
`g_* 𝒪_X = 𝒪_T` (a contraction), `ρ(X/T) = 1`, `dim T < dim X` and `-(K + B)` `g`-ample. -/
@[mmp "def_oai4_mori_fibre_space_endpoint"]
structure IsMoriFibreSpace (sT : T ⟶ Spec (.of k)) (K : Divisor X) (B : QDivisor X)
    (g : X ⟶ T) : Prop where
  isProjectiveVariety : MMP.Mori.IsProjectiveVariety k sX
  isLogCanonicalPair : MMP.Intersection.IsLogCanonicalPair sX B
  isCanonicalDivisor : ∃ n : ℕ, K.IsCanonicalDivisor sX n
  isContraction : IsContraction sX sT g
  isProjectiveVariety_target : MMP.Mori.IsProjectiveVariety k sT
  relativePicardNumber_eq_one : relativePicardNumberN1 sX g = 1
  dim_lt : topologicalKrullDim T < topologicalKrullDim X
  /-- The divisor `-(K + B)` is `g`-ample. -/
  hasRelativelyAmpleMultiple : (-(Divisor.toQDivisor K + B)).HasRelativelyAmpleMultiple g

end MoriFibreSpace

/-! ### Permitted steps -/

section PermittedStep

variable [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {X' : Scheme.{u}}
  [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']

/-- A *permitted step* `(X⁺, B⁺, f⁺)` for `(X, B, R, f)`. The setting: `(X, B)` is a projective lc
pair with canonical divisor `K`, `D = K + B`, `R` is a `D`-negative extremal ray of `NE̅(X)` and
`f : X ⟶ Z` is a birational contraction of `R` onto a normal projective variety, with
`ρ(X/Z) = 1` and `-D` `f`-ample. The step: `X⁺` is a normal projective variety,
`f⁺ : X⁺ ⟶ Z` is a small projective birational morphism (possibly an isomorphism),
`B⁺ = (f⁺)⁻¹_* f_* B` is the strict transform of `f_* B`, `(X⁺, B⁺)` is lc and `K_{X⁺} + B⁺` is
`f⁺`-ample, where `K_{X⁺} = (f⁺)⁻¹_* f_* K` (the canonical divisors of all models are cut out by
one rational top form). No condition is imposed on `ρ(X⁺/Z)`. -/
@[mmp "def_oai4_permitted_step"]
structure IsPermittedStep (sZ : Z ⟶ Spec (.of k)) (sX' : X' ⟶ Spec (.of k)) (K : Divisor X)
    (B : QDivisor X) (R : Set (NumericalCurveClasses sX)) (f : X ⟶ Z) (fp : X' ⟶ Z) :
    Prop where
  isProjectiveVariety : MMP.Mori.IsProjectiveVariety k sX
  isLogCanonicalPair : MMP.Intersection.IsLogCanonicalPair sX B
  isCanonicalDivisor : ∃ n : ℕ, K.IsCanonicalDivisor sX n
  isNegativeExtremalRayOf : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R
  isContractionOfRay : IsContractionOfRay sX sZ R f
  isProjectiveVariety_target : MMP.Mori.IsProjectiveVariety k sZ
  relativePicardNumber_eq_one : relativePicardNumberN1 sX f = 1
  /-- The divisor `-(K + B)` is `f`-ample. -/
  hasRelativelyAmpleMultiple : (-(Divisor.toQDivisor K + B)).HasRelativelyAmpleMultiple f
  isBirationalMorphism : IsBirationalMorphism f
  isProjectiveVariety_step : MMP.Mori.IsProjectiveVariety k sX'
  isSmallMorphism_step : IsSmallMorphism sX' sZ fp
  isProjectiveMorphism_step : IsProjectiveMorphism fp
  isLogCanonicalPair_step : MMP.Intersection.IsLogCanonicalPair sX' (flipTransform f fp B)
  /-- The divisor `K_{X⁺} + B⁺` is `f⁺`-ample. -/
  hasRelativelyAmpleMultiple_step :
    (Divisor.toQDivisor (flipTransform f fp K) + flipTransform f fp B).HasRelativelyAmpleMultiple
      fp

end PermittedStep

/-! ### Programs -/

section Program

/-- The sequence `X₀ = X, X₁ = Y₀, X₂ = Y₁, …` of the models of a program. -/
def modelSeq (X : Scheme.{u}) (Y : ℕ → Scheme.{u}) : ℕ → Scheme.{u}
  | 0 => X
  | i + 1 => Y i

/-- The structure morphisms of the models of a program. -/
def modelStr {Y : ℕ → Scheme.{u}} (sY : ∀ i, Y i ⟶ Spec (.of k)) :
    ∀ i, modelSeq X Y i ⟶ Spec (.of k)
  | 0 => sX
  | i + 1 => sY i

/-- The divisors `D₀ = D, D₁ = E₀, …` on the models of a program. -/
def divisorSeq {R : Type*} [Zero R] {Y : ℕ → Scheme.{u}} (D : DivisorWithCoeffs R X)
    (E : ∀ i, DivisorWithCoeffs R (Y i)) : ∀ i, DivisorWithCoeffs R (modelSeq X Y i)
  | 0 => D
  | i + 1 => E i

variable {Y : ℕ → Scheme.{u}}

/-- The models of a program are integral when `X` and every `Y i` are. -/
instance modelSeq.isIntegral [IsIntegral X] [∀ i, IsIntegral (Y i)] :
    ∀ i, IsIntegral (modelSeq X Y i)
  | 0 => ‹IsIntegral X›
  | i + 1 => inferInstanceAs (IsIntegral (Y i))

/-- The models of a program are quasi-compact when `X` and every `Y i` are. -/
instance modelSeq.compactSpace [CompactSpace X] [∀ i, CompactSpace (Y i)] :
    ∀ i, CompactSpace (modelSeq X Y i)
  | 0 => ‹CompactSpace X›
  | i + 1 => inferInstanceAs (CompactSpace (Y i))

/-- The models of a program are locally Noetherian when `X` and every `Y i` are. -/
instance modelSeq.isLocallyNoetherian [IsLocallyNoetherian X] [∀ i, IsLocallyNoetherian (Y i)] :
    ∀ i, IsLocallyNoetherian (modelSeq X Y i)
  | 0 => ‹IsLocallyNoetherian X›
  | i + 1 => inferInstanceAs (IsLocallyNoetherian (Y i))

/-- The models of a program are normal when `X` and every `Y i` are. -/
instance modelSeq.isNormal [IsNormal X] [∀ i, IsNormal (Y i)] :
    ∀ i, IsNormal (modelSeq X Y i)
  | 0 => ‹IsNormal X›
  | i + 1 => inferInstanceAs (IsNormal (Y i))

variable [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]

/-- A *program* from a projective lc pair `(X, B)`, with canonical divisor `K`: a number
`n ∈ ℕ ∪ {∞}` of birational steps; models `(X_i, B_i)`, `X₀ = X`, `X_{i+1} = Y i`, with canonical
divisors `K_i` (`K₀ = K`); for each `i < n` a `(K_i + B_i)`-negative extremal ray `R_i` of
`NE̅(X_i)` with birational contraction `f_i : X_i ⟶ Z_i` and a permitted step
`(X_{i+1}, B_{i+1}, f_i⁺)` for `(X_i, B_i, R_i, f_i)`, so that `B_{i+1}` is the strict transform
of `(f_i)_* B_i` and `K_{i+1} = (f_i⁺)⁻¹_* (f_i)_* K_i`; and, when `n < ∞`, optionally
(`hasFinal`) a final `(K_n + B_n)`-negative extremal ray `R_n` of `NE̅(X_n)` whose contraction
`g : X_n ⟶ T` (onto a normal projective variety, with `ρ(X_n/T) = 1` and `-(K_n + B_n)`
`g`-ample) is of fibre type, `dim T < dim X_n`. Every `(X_i, B_i)`, `i ≤ n`, is then a projective
lc pair. The data indexed by `i ≥ n` are unconstrained. -/
@[mmp "def_oai4_program"]
structure Program (K : Divisor X) (B : QDivisor X) where
  /-- The number of birational steps. -/
  n : ℕ∞
  /-- The models after the first: `X_{i+1} = Y i`. -/
  Y : ℕ → Scheme.{u}
  /-- The structure morphism of `X_{i+1}`. -/
  sY : ∀ i, Y i ⟶ Spec (.of k)
  [isIntegral : ∀ i, IsIntegral (Y i)]
  [compactSpace : ∀ i, CompactSpace (Y i)]
  [isLocallyNoetherian : ∀ i, IsLocallyNoetherian (Y i)]
  [isNormal : ∀ i, IsNormal (Y i)]
  /-- The canonical divisor `K_{i+1}` of `X_{i+1}`. -/
  KY : ∀ i, Divisor (Y i)
  /-- The boundary `B_{i+1}` on `X_{i+1}`. -/
  BY : ∀ i, QDivisor (Y i)
  /-- The extremal ray `R_i ⊆ N₁(X_i)`. -/
  R : ∀ i, Set (NumericalCurveClasses (modelStr sX sY i))
  /-- The target `Z_i` of the contraction of `R_i`. -/
  Z : ℕ → Scheme.{u}
  /-- The structure morphism of `Z_i`. -/
  sZ : ∀ i, Z i ⟶ Spec (.of k)
  /-- The contraction `f_i : X_i ⟶ Z_i` of `R_i`. -/
  f : ∀ i, modelSeq X Y i ⟶ Z i
  /-- The small morphism `f_i⁺ : X_{i+1} ⟶ Z_i` of the step. -/
  fp : ∀ i, Y i ⟶ Z i
  isProjectiveVariety : MMP.Mori.IsProjectiveVariety k sX
  isLogCanonicalPair : MMP.Intersection.IsLogCanonicalPair sX B
  isCanonicalDivisor : ∃ m : ℕ, K.IsCanonicalDivisor sX m
  isPermittedStep : ∀ i : ℕ, (i : ℕ∞) < n →
    IsPermittedStep (modelStr sX sY i) (sZ i) (sY i) (divisorSeq K KY i) (divisorSeq B BY i)
      (R i) (f i) (fp i)
  KY_eq : ∀ i : ℕ, (i : ℕ∞) < n → KY i = flipTransform (f i) (fp i) (divisorSeq K KY i)
  BY_eq : ∀ i : ℕ, (i : ℕ∞) < n → BY i = flipTransform (f i) (fp i) (divisorSeq B BY i)
  /-- Whether the program ends with a fibre-type ray. -/
  hasFinal : Prop
  /-- The final ray `R_n`, used when `hasFinal`. -/
  finalRay : Set (NumericalCurveClasses (modelStr sX sY n.toNat))
  /-- The target of the final contraction. -/
  T : Scheme.{u}
  /-- The structure morphism of `T`. -/
  sT : T ⟶ Spec (.of k)
  /-- The final contraction `g : X_n ⟶ T`. -/
  g : modelSeq X Y n.toNat ⟶ T
  final_spec : hasFinal → n ≠ ⊤ ∧
    IsNegativeExtremalRayOf (modelStr sX sY n.toNat)
      (Divisor.toQDivisor (divisorSeq K KY n.toNat) + divisorSeq B BY n.toNat) finalRay ∧
    IsContractionOfRay (modelStr sX sY n.toNat) sT finalRay g ∧
    MMP.Mori.IsProjectiveVariety k sT ∧ relativePicardNumberN1 (modelStr sX sY n.toNat) g = 1 ∧
    (-(Divisor.toQDivisor (divisorSeq K KY n.toNat) +
      divisorSeq B BY n.toNat)).HasRelativelyAmpleMultiple g ∧
    topologicalKrullDim T < topologicalKrullDim (modelSeq X Y n.toNat)

attribute [instance] Program.isIntegral Program.compactSpace Program.isLocallyNoetherian
  Program.isNormal

variable {sX} {K : Divisor X} {B : QDivisor X}

/-- A program with `n` birational steps is *maximal* if `n = ∞`, or `n < ∞` and
`D_n = K_{X_n} + B_n` is nef, or `n < ∞` and the program has a final fibre-type ray. -/
@[mmp "def_oai4_maximal_program"]
def Program.IsMaximal (P : Program sX K B) : Prop :=
  P.n = ⊤ ∨
    (P.n ≠ ⊤ ∧ QDivisor.IsNefOnCurves (modelStr sX P.sY P.n.toNat)
      (Divisor.toQDivisor (divisorSeq K P.KY P.n.toNat) + divisorSeq B P.BY P.n.toNat)) ∨
    P.hasFinal

end Program

end MMP.Fourfold
