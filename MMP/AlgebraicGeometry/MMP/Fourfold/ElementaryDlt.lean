module

public import MMP.AlgebraicGeometry.MMP.Fourfold.DltProgram
public import MMP.AlgebraicGeometry.MMP.Fourfold.Flip
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities

/-!
# Step diagrams and elementary dlt programs of projective pairs

A *step diagram* `(X⁻, B⁻) → Z ← (X⁺, B⁺)` consists of two normal projective complex fourfolds
with projective birational morphisms `f^±` onto a normal projective variety `Z`, `f⁺` small, such
that `-(K_{X⁻} + B⁻)` is `f⁻`-ample and `K_{X⁺} + B⁺` is `f⁺`-ample, `B⁺` being the strict
transform of `f⁻_* B⁻`.

For a projective `ℚ`-factorial dlt pair `(U, Δ)` with rational boundary and a
`(K_U + Δ)`-negative extremal ray `R` of `NE̅(U)` whose contraction `f : U ⟶ V` is birational,
the *elementary step* of `R` is the flip of `f` when `f` is small, and the divisorial contraction
`(U, Δ) ⟶ (V, f_* Δ)` otherwise. An *elementary dlt program* is a finite or infinite sequence of
projective `ℚ`-factorial dlt pairs in which each pair is the output of an elementary step of the
previous one; it is *over* `Z` when it is finite and every contraction factors through `Z`.

## Main definitions

* `MMP.Fourfold.IsFourfoldStepDiagram`: step diagrams of complex fourfolds.
* `MMP.Fourfold.IsProjectiveQFactorialDltPair`: projective `ℚ`-factorial dlt pairs with rational
  boundary and a chosen canonical divisor.
* `MMP.Fourfold.IsProjectiveElementaryDltStep`: the elementary step of a negative extremal ray
  of `NE̅(U)` with birational contraction.
* `MMP.Fourfold.ElementaryDltProgram`: elementary dlt programs.
* `MMP.Fourfold.RelativeElementaryDltProgram`: elementary dlt programs over a base `Z`.

## Implementation notes

The models of a program are indexed as in `MMP.Fourfold.Program`: `U₀ = U`, `U_{j+1} = Y j`,
with `n ∈ ℕ ∪ {∞}` steps; only the data indexed by `j ≤ n` (models) and `j < n` (steps) are
constrained. Each step `j` carries the contraction `f_j : U_j ⟶ V_j` of its ray and a morphism
`f_j⁺ : U_{j+1} ⟶ V_j`: for a flip, `f_j⁺` is the flip of `f_j`; for a divisorial contraction,
`f_j⁺` is an isomorphism, so that `U_{j+1}` is the target `V_j` of `f_j` up to isomorphism. In
both cases the next boundary is the birational transform `(f_j⁺)⁻¹_* (f_j)_* Δ_j`, the strict
transform of `Δ_j` for a flip and `(f_j)_* Δ_j` for a divisorial contraction. The canonical
divisors `K_j` of the models are any canonical divisors: negativity of a ray and ampleness only
depend on the class of `K_j + Δ_j`.

In a step diagram the canonical divisor of `X⁺` is `(f⁺)⁻¹_* f⁻_* K⁻`, as in
`MMP.Fourfold.IsThreefoldStepDiagram`: all canonical divisors are cut out by one rational top
form.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori

/-! ### Step diagrams of fourfolds -/

/- Note: `def_oai4_step_diagram` is the fourfold version of
`IsThreefoldStepDiagram` (`def_mmp_indexc_step_diagram`); the only difference is
`topologicalKrullDim X^± = 4` instead of `3`, so it is stated anew rather than registered. -/

section StepDiagram

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]

/-- A *step diagram* `(X⁻, B⁻) → Z ← (X⁺, B⁺)` of fourfolds: `X^±` are normal projective
fourfolds over `ℂ` with canonical divisors `K^±`, `Z` is a normal projective variety,
`f^± : X^± ⟶ Z` are projective birational morphisms over `ℂ` with `f^±_* 𝒪_{X^±} = 𝒪_Z`, `f⁺` is
small, `B⁻` is an effective `ℚ`-divisor, `B⁺ = (f⁺)⁻¹_* f⁻_* B⁻` and `K⁺ = (f⁺)⁻¹_* f⁻_* K⁻`,
`D^± = K^± + B^±` are `ℚ`-Cartier, `-D⁻` is `f⁻`-ample and `D⁺` is `f⁺`-ample. The positive pair
is not required to be lc. -/
@[mmp "def_oai4_step_diagram"]
structure IsFourfoldStepDiagram (sXm : Xm ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ))
    (sXp : Xp ⟶ Spec (.of ℂ)) (K : Divisor Xm) (B : QDivisor Xm) (fm : Xm ⟶ Z) (fp : Xp ⟶ Z) :
    Prop where
  isProjectiveVariety_minus : MMP.Mori.IsProjectiveVariety ℂ sXm
  isNormalVariety_minus : IsNormalVariety ℂ sXm
  dim_minus : topologicalKrullDim Xm = 4
  isProjectiveVariety_plus : MMP.Mori.IsProjectiveVariety ℂ sXp
  isNormalVariety_plus : IsNormalVariety ℂ sXp
  dim_plus : topologicalKrullDim Xp = 4
  isProjectiveVariety_target : MMP.Mori.IsProjectiveVariety ℂ sZ
  isNormalVariety_target : IsNormalVariety ℂ sZ
  comp_eq_minus : fm ≫ sZ = sXm
  comp_eq_plus : fp ≫ sZ = sXp
  isProjectiveMorphism_minus : IsProjectiveMorphism fm
  isProjectiveMorphism_plus : IsProjectiveMorphism fp
  isBirationalMorphism_minus : IsBirationalMorphism fm
  /-- `f⁻_* 𝒪_{X⁻} = 𝒪_Z`: the map `𝒪_Z(U) → 𝒪_{X⁻}(f⁻⁻¹ U)` is an isomorphism for every
  open `U`. -/
  isIso_app_minus : ∀ U : Z.Opens, IsIso (fm.app U)
  /-- `f⁺_* 𝒪_{X⁺} = 𝒪_Z`: the map `𝒪_Z(U) → 𝒪_{X⁺}(f⁺⁻¹ U)` is an isomorphism for every
  open `U`. -/
  isIso_app_plus : ∀ U : Z.Opens, IsIso (fp.app U)
  isSmallMorphism_plus : IsSmallMorphism sXp sZ fp
  isCanonicalDivisor : ∃ m : ℕ, K.IsCanonicalDivisor sXm m
  /-- `B⁻` is effective. -/
  nonneg : ∀ P, 0 ≤ B.coeff P
  /-- `D⁻ = K⁻ + B⁻` is `ℚ`-Cartier. -/
  isQCartier_minus : (Divisor.toQDivisor K + B).IsQCartier
  /-- `D⁺ = K⁺ + B⁺` is `ℚ`-Cartier. -/
  isQCartier_plus :
    MMP.Mori.QDivisor.IsQCartier
      (Divisor.toQDivisor (flipTransform fm fp K) + flipTransform fm fp B)
  /-- `-D⁻` is `f⁻`-ample. -/
  hasRelativelyAmpleMultiple_minus : (-(Divisor.toQDivisor K + B)).HasRelativelyAmpleMultiple fm
  /-- `D⁺ = K⁺ + B⁺` is `f⁺`-ample. -/
  hasRelativelyAmpleMultiple_plus : MMP.Mori.QDivisor.HasRelativelyAmpleMultiple
    (Divisor.toQDivisor (flipTransform fm fp K) + flipTransform fm fp B) fp

variable {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
  {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}

omit [IsIntegral Xm] [IsIntegral Xp] in
/-- The positive morphism `f⁺` of a step diagram is birational. -/
theorem IsFourfoldStepDiagram.isBirationalMorphism_plus
    (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) : IsBirationalMorphism fp :=
  h.isSmallMorphism_plus.isBirationalMorphism

omit [IsIntegral Xm] [IsIntegral Xp] in
/-- The positive morphism `f⁺` of a step diagram is proper. -/
theorem IsFourfoldStepDiagram.isProper_plus
    (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) : IsProper fp :=
  h.isSmallMorphism_plus.isProper

end StepDiagram

/-! ### Elementary dlt steps -/

section Step

variable {k : Type u} [Field k] {X V X' : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]

/-- A *projective `ℚ`-factorial dlt pair* `(X, Δ)` with rational boundary `Δ` and canonical
divisor `K`: `X` is a projective `ℚ`-factorial variety over `k`, `K` is a canonical divisor of
`X` and `(X, Δ)` is dlt. -/
structure IsProjectiveQFactorialDltPair (K : Divisor X) (Δ : QDivisor X) : Prop where
  isProjectiveVariety : MMP.Mori.IsProjectiveVariety k sX
  isQFactorial : IsQFactorial sX
  isCanonicalDivisor : ∃ m : ℕ, K.IsCanonicalDivisor sX m
  isDltPair : MMP.Intersection.IsDltPair sX Δ

/- Note: `IsElementaryDltStep` (`def_mmp_relative_dlt_program`) is
the relative step over a quasi-projective base `S`, with rays of `NE̅(X/S)`, `ρ(X/Z) = 1` built
into the contraction and a divisorial branch requiring `Ex(f)` to be a prime divisor; here the
step is absolute (rays of `NE̅(U)`, contractions `IsContractionOfRay`, flips `IsFlipOf` of
`def_oai4_bg_flip`) and the two branches are "`f` small" and "`f` not small", as in the
source. -/

variable [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']

/-- The *elementary step* `(X, Δ) ⇢ (X', Δ')` of a `(K + Δ)`-negative extremal ray `R` of
`NE̅(X)`, for a projective `ℚ`-factorial dlt pair `(X, Δ)` with rational boundary and canonical
divisor `K`: `f : X ⟶ V` is the contraction of `R`, `f` is birational, `f⁺ : X' ⟶ V` is a
morphism over `k`, `Δ' = (f⁺)⁻¹_* f_* Δ`, and

* if `f` is small, `f⁺` is a `(K + Δ)`-flip of `f` (so `Δ'` is the strict transform of `Δ`);
* otherwise `f⁺` is an isomorphism, so that `(X', Δ')` is the divisorial contraction
  `(V, f_* Δ)`, up to isomorphism. -/
@[mmp "def_oai4_elementary_dlt_step"]
structure IsProjectiveElementaryDltStep (sV : V ⟶ Spec (.of k)) (sX' : X' ⟶ Spec (.of k))
    (K : Divisor X) (Δ : QDivisor X) (R : Set (NumericalCurveClasses sX)) (f : X ⟶ V)
    (fp : X' ⟶ V) (Δ' : QDivisor X') : Prop where
  isProjectiveQFactorialDltPair : IsProjectiveQFactorialDltPair sX K Δ
  isNegativeExtremalRayOf : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + Δ) R
  isContractionOfRay : IsContractionOfRay sX sV R f
  isBirationalMorphism : IsBirationalMorphism f
  comp_eq : fp ≫ sV = sX'
  eq_flipTransform : Δ' = flipTransform f fp Δ
  flip_or_divisorial :
    (IsSmallMorphism sX sV f ∧ IsFlipOf sX sV sX' (Divisor.toQDivisor K + Δ) f fp) ∨
      (¬ IsSmallMorphism sX sV f ∧ IsIso fp)

variable {sX} {sV : V ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {K : Divisor X}
  {Δ : QDivisor X} {R : Set (NumericalCurveClasses sX)} {f : X ⟶ V} {fp : X' ⟶ V}
  {Δ' : QDivisor X'}

/-- The elementary step of a ray with small contraction is a flip. -/
theorem IsProjectiveElementaryDltStep.isFlipOf_of_isSmallMorphism
    (h : IsProjectiveElementaryDltStep sX sV sX' K Δ R f fp Δ') (hf : IsSmallMorphism sX sV f) :
    IsFlipOf sX sV sX' (Divisor.toQDivisor K + Δ) f fp := by
  rcases h.flip_or_divisorial with h | h
  · exact h.2
  · exact absurd hf h.1

/-- The elementary step of a ray whose contraction is not small is the divisorial contraction:
`f⁺` is an isomorphism. -/
theorem IsProjectiveElementaryDltStep.isIso_of_not_isSmallMorphism
    (h : IsProjectiveElementaryDltStep sX sV sX' K Δ R f fp Δ') (hf : ¬ IsSmallMorphism sX sV f) :
    IsIso fp := by
  rcases h.flip_or_divisorial with h | h
  · exact absurd h.1 hf
  · exact h.2

end Step

/-! ### Elementary dlt programs -/

section Program

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]

/-- An *elementary dlt program* from `(X, Δ)`, with canonical divisor `K`: a number
`n ∈ ℕ ∪ {∞}` of steps and models `(X_j, Δ_j)`, `X₀ = X`, `X_{j+1} = Y j`, `Δ₀ = Δ`, with
canonical divisors `K_j` (`K₀ = K`), such that every `(X_j, Δ_j)`, `j ≤ n`, is a projective
`ℚ`-factorial dlt pair with rational boundary and, for `j < n`, `(X_{j+1}, Δ_{j+1})` is the
output of the elementary step (`MMP.Fourfold.IsProjectiveElementaryDltStep`) of a
`(K_j + Δ_j)`-negative extremal ray `R_j` of `NE̅(X_j)` with birational contraction
`f_j : X_j ⟶ V_j`, by `f_j⁺ : X_{j+1} ⟶ V_j`. The data indexed by `j > n` (models) and `j ≥ n`
(steps) are unconstrained. -/
@[mmp "def_oai4_elementary_dlt_program"]
structure ElementaryDltProgram (K : Divisor X) (Δ : QDivisor X) where
  /-- The number of steps. -/
  n : ℕ∞
  /-- The models after the first: `X_{j+1} = Y j`. -/
  Y : ℕ → Scheme.{u}
  /-- The structure morphism `X_{j+1} ⟶ Spec k`. -/
  sY : ∀ j, Y j ⟶ Spec (.of k)
  [isIntegral : ∀ j, IsIntegral (Y j)]
  [compactSpace : ∀ j, CompactSpace (Y j)]
  [isLocallyNoetherian : ∀ j, IsLocallyNoetherian (Y j)]
  [isNormal : ∀ j, IsNormal (Y j)]
  /-- The canonical divisor `K_{j+1}` of `X_{j+1}`. -/
  KY : ∀ j, Divisor (Y j)
  /-- The boundary `Δ_{j+1}` on `X_{j+1}`. -/
  ΔY : ∀ j, QDivisor (Y j)
  /-- The extremal ray `R_j ⊆ N₁(X_j)`. -/
  R : ∀ j, Set (NumericalCurveClasses (modelStr sX sY j))
  /-- The target `V_j` of the contraction of `R_j`. -/
  V : ℕ → Scheme.{u}
  /-- The structure morphism `V_j ⟶ Spec k`. -/
  sV : ∀ j, V j ⟶ Spec (.of k)
  /-- The contraction `f_j : X_j ⟶ V_j` of `R_j`. -/
  f : ∀ j, modelSeq X Y j ⟶ V j
  /-- The morphism `f_j⁺ : X_{j+1} ⟶ V_j`: a flip, or an isomorphism. -/
  fp : ∀ j, Y j ⟶ V j
  isProjectiveQFactorialDltPair : ∀ j : ℕ, (j : ℕ∞) ≤ n →
    IsProjectiveQFactorialDltPair (modelStr sX sY j) (divisorSeq K KY j) (divisorSeq Δ ΔY j)
  isProjectiveElementaryDltStep : ∀ j : ℕ, (j : ℕ∞) < n →
    IsProjectiveElementaryDltStep (modelStr sX sY j) (sV j) (sY j) (divisorSeq K KY j)
      (divisorSeq Δ ΔY j) (R j) (f j) (fp j) (ΔY j)

attribute [instance] ElementaryDltProgram.isIntegral ElementaryDltProgram.compactSpace
  ElementaryDltProgram.isLocallyNoetherian ElementaryDltProgram.isNormal

/- Note: `RelativeDltProgram` (`def_mmp_relative_dlt_program`) runs
rays of the relative cone `NE̅(X/S)`; here the program is the absolute elementary dlt program
`ElementaryDltProgram` of `NE̅(U_k)` rays, finite, with the contractions factoring through `Z`,
as in the source. -/

/-- An *elementary dlt program over `Z`* from `(X, Δ)`, for a projective morphism
`h₀ : X ⟶ Z`: a finite elementary dlt program `(X_j, Δ_j)_{0 ≤ j ≤ m}` together with projective
morphisms `h_j : X_j ⟶ Z` (`X₀ = X`, by `h₀`) such that, for each `j < m`, the contraction
`f_j : X_j ⟶ V_j` of the `j`-th step satisfies `h_j = h_j' ∘ f_j` for a morphism
`h_j' : V_j ⟶ Z`, and `h_{j+1} = h_j' ∘ f_j⁺` is the composite of `X_{j+1} ⟶ V_j` with `h_j'`. -/
@[mmp "def_oai4_relative_elementary_dlt_program"]
structure RelativeElementaryDltProgram (K : Divisor X) (Δ : QDivisor X) {Z : Scheme.{u}}
    (h₀ : X ⟶ Z) extends ElementaryDltProgram sX K Δ where
  n_ne_top : n ≠ ⊤
  /-- The morphism `h_{j+1} : X_{j+1} ⟶ Z`. -/
  hY : ∀ j, Y j ⟶ Z
  /-- The morphism `h_j' : V_j ⟶ Z`. -/
  hV : ∀ j, V j ⟶ Z
  isProjectiveMorphism : ∀ j : ℕ, (j : ℕ∞) ≤ n → IsProjectiveMorphism (modelMap h₀ hY j)
  comp_hV : ∀ j : ℕ, (j : ℕ∞) < n → f j ≫ hV j = modelMap h₀ hY j
  hY_eq : ∀ j : ℕ, (j : ℕ∞) < n → hY j = fp j ≫ hV j

variable {sX} {K : Divisor X} {Δ : QDivisor X}

/-- The initial pair of an elementary dlt program is a projective `ℚ`-factorial dlt pair. -/
theorem ElementaryDltProgram.isProjectiveQFactorialDltPair_zero
    (P : ElementaryDltProgram sX K Δ) : IsProjectiveQFactorialDltPair sX K Δ :=
  P.isProjectiveQFactorialDltPair 0 bot_le

/-- The morphism `h₀ : X ⟶ Z` of an elementary dlt program over `Z` is projective. -/
theorem RelativeElementaryDltProgram.isProjectiveMorphism_zero {Z : Scheme.{u}} {h₀ : X ⟶ Z}
    (P : RelativeElementaryDltProgram sX K Δ h₀) : IsProjectiveMorphism h₀ :=
  P.isProjectiveMorphism 0 bot_le

end Program

end MMP.Fourfold
