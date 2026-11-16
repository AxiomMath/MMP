module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ElementaryDlt
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldStabilizedTail

/-!
# Crepant junctions of fourfold klt pairs and finite relative fourfold programs

Let `(X, B)` be a projective klt fourfold pair and `I` a finite set of valuations of `k(X)`,
exceptional over `X`, with log discrepancy `a(s; X, B) ≤ 1` for `s ∈ I`. A *crepant junction of
`(X, B)` extracting `I`* is a pair `(p, Θ)`: a projective birational morphism `p : Y ⟶ X` from a
normal projective `ℚ`-factorial variety such that `s ↦ E_s = c_Y(s)` is a bijection from `I`
onto the `p`-exceptional prime divisors of `Y`, and the boundary
`Θ = p⁻¹_* B + ∑_{s ∈ I} (1 - a(s; X, B)) E_s`.

Let `Z` be a normal projective variety and `(V, Θ)` a pair on a `ℚ`-factorial normal projective
fourfold with a projective morphism `V ⟶ Z`. A *finite relative program over `Z` from `(V, Θ)`*
is a sequence of step diagrams `(V_k, Θ_k) → T_k ← (V_{k+1}, Θ_{k+1})`, `0 ≤ k < m`, with
`(V_0, Θ_0) = (V, Θ)`, each `T_k` projective over `Z` compatibly with the maps `V_k ⟶ Z`, each
`V_k` `ℚ`-factorial, and each `g_k : V_k ⟶ T_k` the contraction of a `(K_{V_k} + Θ_k)`-negative
extremal ray of curves contracted over `Z`, with `ρ(V_k/T_k) = 1`. Its *end* is `(V_m, Θ_m)`.

## Main definitions

* `MMP.Fourfold.FourfoldCrepantJunction`: crepant junctions of projective klt fourfold pairs.
* `MMP.Fourfold.RelativeFourfoldProgram`: finite relative fourfold programs.
* `MMP.Fourfold.RelativeFourfoldProgram.model`, `MMP.Fourfold.RelativeFourfoldProgram.boundary`:
  the models `(V_k, Θ_k)` of a program.
* `MMP.Fourfold.RelativeFourfoldProgram.endModel`,
  `MMP.Fourfold.RelativeFourfoldProgram.endBoundary`: its end `(V_m, Θ_m)`.
* `MMP.Fourfold.RelativeFourfoldProgram.flipPartialIso`: the birational map
  `(g_k⁺)⁻¹ ∘ g_k : V_k ⤏ V_{k+1}` of a step.
* `MMP.Fourfold.RelativeFourfoldProgram.compositeMap`: the composite birational map
  `V_0 ⤏ V_m`.

## Implementation notes

* These are the fourfold analogues of `MMP.Fourfold.CrepantJunction` and
  `MMP.Fourfold.RelativeThreefoldProgram`, which are stated for threefolds; the conventions are
  the same. In a crepant junction, `Y` is a variety over `ℂ` through `p`, and `E_s = c_Y(s)` is
  stated as `ord_{E_s} = s` (as valuations of `k(X)`): a normalized divisorial valuation whose
  centre on the normal variety `Y` is a prime divisor `E` is `ord_E`, and conversely. The
  condition on `I` is `I ⊆ I(X, B)` (`MMP.Fourfold.lowDiscrepancySet`), whose members are the
  normalized divisorial valuations exceptional over `X` with `a(s; X, B) ≤ 1`. The log
  discrepancies `a(s; X, B)` enter through the predicate `MMP.Fourfold.IsValuationLogDiscrepancy`;
  they are rational because `B` is. The dimension of `Y` is recorded (it is that of `X`, since
  `p` is birational).
* The models of a program are `V₀ = V` and `V_{k+1} = Y k` (`MMP.Fourfold.modelSeq`); the data
  indexed by `k > m` (models) and `k ≥ m` (steps) are unconstrained. The canonical divisors `K_k`
  of the models are cut out by one rational top form: `K₀ = K` is a canonical divisor of `V` and
  `K_{k+1} = (g_k⁺)⁻¹_* (g_k)_* K_k`, the convention of `MMP.Fourfold.IsFourfoldStepDiagram`,
  which also forces `Θ_{k+1} = (g_k⁺)⁻¹_* (g_k)_* Θ_k`.
* "Each `T_k` projective over `Z` compatibly with the maps `V_k ⟶ Z`" is: morphisms
  `π_k : V_k ⟶ Z` (`π₀` the given projective morphism) and projective morphisms `h_k : T_k ⟶ Z`
  with `π_k = h_k ∘ g_k` and `π_{k+1} = h_k ∘ g_k⁺`.
* "A `(K_{V_k} + Θ_k)`-negative extremal ray of curves contracted over `Z`" is, as in
  `MMP.Fourfold.RelativeThreefoldProgram`, a `(K_k + Θ_k)`-negative extremal ray `R_k` of
  `NE̅(V_k)` spanned by the class of an integral curve contracted by `π_k`; `g_k` is the
  contraction of `R_k` (`MMP.Fourfold.IsContractionOfRay`).
* The birational map `(g_k⁺)⁻¹ ∘ g_k` of a step is the composite of chosen partial isomorphisms
  representing `g_k` and `g_k⁺` (both are birational morphisms); the composite birational map
  `V_0 ⤏ V_m` is the composite of these. Only their rational maps are meaningful.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

/-! ### Crepant junctions -/

section Junction

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  (sX : X ⟶ Spec (.of ℂ))

/-- A *crepant junction of `(X, B)` extracting `I`*, for fourfolds. The setting: `(X, B)` is a
projective klt fourfold pair over `ℂ` and `I` is a finite set of normalized divisorial valuations
of `k(X)`, exceptional over `X`, with `a(s; X, B) ≤ 1` for `s ∈ I`, that is, `I ⊆ I(X, B)`. The
junction: a projective birational morphism `p : Y ⟶ X` from a normal projective `ℚ`-factorial
variety `Y` (over `ℂ` through `p`) and prime divisors `E_s = c_Y(s)` of `Y`, `s ∈ I`, such that
`s ↦ E_s` is a bijection from `I` onto the `p`-exceptional prime divisors of `Y`, together with
the boundary `Θ = p⁻¹_* B + ∑_{s ∈ I} (1 - a(s; X, B)) E_s`. -/
@[mmp "def_oai4_crepant_junction"]
structure FourfoldCrepantJunction (B : QDivisor X)
    (I : Finset (Valuation X.functionField (WithZero (Multiplicative ℤ)))) where
  /-- The source `Y` of the extraction. -/
  Y : Scheme.{0}
  [isIntegral : IsIntegral Y]
  [isLocallyNoetherian : IsLocallyNoetherian Y]
  [isNormal : IsNormal Y]
  /-- The projective birational morphism `p : Y ⟶ X`. -/
  p : Y ⟶ X
  /-- The prime divisor `E_s = c_Y(s)` of `Y`. -/
  E : I → MMP.Mori.PrimeDivisor Y
  /-- The boundary `Θ` on `Y`. -/
  Θ : QDivisor Y
  isProjectiveVariety_base : MMP.Mori.IsProjectiveVariety ℂ sX
  dim_base : topologicalKrullDim X = 4
  isKltPair : IsKltPair sX B
  subset_lowDiscrepancySet : (I : Set _) ⊆ lowDiscrepancySet sX B
  isProjectiveVariety : MMP.Mori.IsProjectiveVariety ℂ (p ≫ sX)
  isQFactorial : IsQFactorial (p ≫ sX)
  dim_eq : topologicalKrullDim Y = 4
  isProjectiveMorphism : IsProjectiveMorphism p
  isBirationalMorphism : IsBirationalMorphism p
  valuation_eq : ∀ s : I,
    (⟨Y, p, isQFactorial.1, isBirationalMorphism, E s⟩ : DivisorOver ℂ sX).valuation = s
  injective : Function.Injective E
  /-- The `p`-exceptional prime divisors of `Y` are exactly the `E_s`, `s ∈ I`. -/
  isExceptional_iff : ∀ P : MMP.Mori.PrimeDivisor Y,
    RationalMap.IsExceptional (X := Y) p.toRationalMap P ↔ P ∈ Set.range E
  Θ_eq : ∃ a : I → ℚ, (∀ s : I, IsValuationLogDiscrepancy sX B s (a s)) ∧
    Θ = inverseTransformDivisor p B + ∑ s : I, Finsupp.single (E s) (1 - a s)

attribute [instance] FourfoldCrepantJunction.isIntegral
  FourfoldCrepantJunction.isLocallyNoetherian FourfoldCrepantJunction.isNormal

variable {sX} {B : QDivisor X}
  {I : Finset (Valuation X.functionField (WithZero (Multiplicative ℤ)))}

/-- The source of a crepant junction is quasi-compact: it is projective over `ℂ`. -/
instance FourfoldCrepantJunction.compactSpace (J : FourfoldCrepantJunction sX B I) :
    CompactSpace J.Y := by
  have := isProper_of_isProjectiveMorphism _ J.isProjectiveVariety.isProjective
  exact QuasiCompact.compactSpace_of_compactSpace (J.p ≫ sX)

/-- The structure morphism `Y ⟶ Spec ℂ` of the source of a crepant junction. -/
abbrev FourfoldCrepantJunction.sY (J : FourfoldCrepantJunction sX B I) : J.Y ⟶ Spec (.of ℂ) :=
  J.p ≫ sX

end Junction

/-! ### Finite relative programs -/

section RelativeProgram

variable {V Z : Scheme.{0}} [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V]
  (sV : V ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) (π : V ⟶ Z)

/-- A *finite relative program over `Z` from `(V, Θ)`*, with canonical divisor `K` of `V`, for
fourfolds. The setting: `Z` is a normal projective complex variety, `V` a `ℚ`-factorial normal
projective complex fourfold, `(V, Θ)` a pair (`MMP.Fourfold.IsPair`) and `π : V ⟶ Z` a projective
morphism over `ℂ`. The data: a number `m ∈ ℕ` of steps; models `V₀ = V`, `V_{k+1} = Y k` with
canonical divisors `K_k` (`K₀ = K`) and boundaries `Θ_k` (`Θ₀ = Θ`); morphisms `π_k : V_k ⟶ Z`
(`π₀ = π`); and for each `k < m` a step diagram `(V_k, Θ_k) → T_k ← (V_{k+1}, Θ_{k+1})` by `g_k`,
`g_k⁺` (`MMP.Fourfold.IsFourfoldStepDiagram`) with `K_{k+1}`, `Θ_{k+1}` the strict transforms of
`K_k`, `Θ_k`, a projective morphism `h_k : T_k ⟶ Z` over `ℂ` with `π_k = g_k ≫ h_k` and
`π_{k+1} = g_k⁺ ≫ h_k`, and an extremal ray `R_k` of `NE̅(V_k)`, such that every `V_k`, `k ≤ m`,
is `ℚ`-factorial and, for `k < m`, `R_k` is `(K_k + Θ_k)`-negative and spanned by the class `[C]`
of an integral curve `C` contracted by `π_k` (over `Z`), `g_k` is the contraction of `R_k` and
`ρ(V_k/T_k) = 1`. Its *end* is `(V_m, Θ_m)`
(`MMP.Fourfold.RelativeFourfoldProgram.endModel`,
`MMP.Fourfold.RelativeFourfoldProgram.endBoundary`). -/
@[mmp "def_oai4_relative_program"]
structure RelativeFourfoldProgram (K : Divisor V) (Θ : QDivisor V) where
  /-- The number `m` of steps. -/
  m : ℕ
  /-- The models after the first: `V_{k+1} = Y k`. -/
  Y : ℕ → Scheme.{0}
  /-- The structure morphism `V_{k+1} ⟶ Spec ℂ`. -/
  sY : ∀ k, Y k ⟶ Spec (.of ℂ)
  [isIntegral : ∀ k, IsIntegral (Y k)]
  [compactSpace : ∀ k, CompactSpace (Y k)]
  [isLocallyNoetherian : ∀ k, IsLocallyNoetherian (Y k)]
  [isNormal : ∀ k, IsNormal (Y k)]
  /-- The canonical divisor `K_{k+1}` of `V_{k+1}`. -/
  KY : ∀ k, Divisor (Y k)
  /-- The boundary `Θ_{k+1}` on `V_{k+1}`. -/
  ΘY : ∀ k, QDivisor (Y k)
  /-- The morphism `π_{k+1} : V_{k+1} ⟶ Z`. -/
  πY : ∀ k, Y k ⟶ Z
  /-- The base `T_k` of the `k`-th step diagram. -/
  T : ℕ → Scheme.{0}
  /-- The structure morphism `T_k ⟶ Spec ℂ`. -/
  sT : ∀ k, T k ⟶ Spec (.of ℂ)
  /-- The contraction `g_k : V_k ⟶ T_k`. -/
  g : ∀ k, modelSeq V Y k ⟶ T k
  /-- The morphism `g_k⁺ : V_{k+1} ⟶ T_k`. -/
  gp : ∀ k, Y k ⟶ T k
  /-- The projective morphism `h_k : T_k ⟶ Z`. -/
  h : ∀ k, T k ⟶ Z
  /-- The extremal ray `R_k ⊆ N₁(V_k)_ℝ`. -/
  R : ∀ k, Set (NumericalCurveClasses (modelStr sV sY k))
  isProjectiveVariety_base : MMP.Mori.IsProjectiveVariety ℂ sZ
  isNormalVariety_base : IsNormalVariety ℂ sZ
  isProjectiveVariety : MMP.Mori.IsProjectiveVariety ℂ sV
  dim_eq : topologicalKrullDim V = 4
  isPair : IsPair sV Θ
  isCanonicalDivisor : ∃ n : ℕ, K.IsCanonicalDivisor sV n
  comp_eq : π ≫ sZ = sV
  isProjectiveMorphism : IsProjectiveMorphism π
  isQFactorial : ∀ k ≤ m, IsQFactorial (modelStr sV sY k)
  isFourfoldStepDiagram : ∀ k < m,
    IsFourfoldStepDiagram (modelStr sV sY k) (sT k) (sY k) (divisorSeq K KY k)
      (divisorSeq Θ ΘY k) (g k) (gp k)
  KY_eq : ∀ k < m, KY k = flipTransform (g k) (gp k) (divisorSeq K KY k)
  ΘY_eq : ∀ k < m, ΘY k = flipTransform (g k) (gp k) (divisorSeq Θ ΘY k)
  comp_eq_base : ∀ k < m, h k ≫ sZ = sT k
  isProjectiveMorphism_base : ∀ k < m, IsProjectiveMorphism (h k)
  modelMap_eq : ∀ k < m, modelMap π πY k = g k ≫ h k
  πY_eq : ∀ k < m, πY k = gp k ≫ h k
  isNegativeExtremalRayOf : ∀ k < m,
    IsNegativeExtremalRayOf (modelStr sV sY k)
      (Divisor.toQDivisor (divisorSeq K KY k) + divisorSeq Θ ΘY k) (R k)
  exists_ray_eq : ∀ k < m, ∃ C : ProperCurve (modelStr sV sY k),
    C.IsContractedBy (modelMap π πY k) ∧
      R k = {u | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass _ (C.cycle ℝ) = u}
  isContractionOfRay : ∀ k < m, IsContractionOfRay (modelStr sV sY k) (sT k) (R k) (g k)
  relativePicardNumber_eq_one : ∀ k < m, relativePicardNumberN1 (modelStr sV sY k) (g k) = 1

attribute [instance] RelativeFourfoldProgram.isIntegral RelativeFourfoldProgram.compactSpace
  RelativeFourfoldProgram.isLocallyNoetherian RelativeFourfoldProgram.isNormal

namespace RelativeFourfoldProgram

variable {sV sZ π} {K : Divisor V} {Θ : QDivisor V} (P : RelativeFourfoldProgram sV sZ π K Θ)

/-- The model `V_k` of a finite relative program (`V₀ = V`, `V_{k+1} = Y k`). -/
abbrev model (k : ℕ) : Scheme.{0} := modelSeq V P.Y k

/-- The structure morphism `V_k ⟶ Spec ℂ` of the model `V_k`. -/
abbrev modelStructure (k : ℕ) : P.model k ⟶ Spec (.of ℂ) := modelStr sV P.sY k

/-- The canonical divisor `K_k` of the model `V_k`. -/
abbrev canonical (k : ℕ) : Divisor (P.model k) := divisorSeq K P.KY k

/-- The boundary `Θ_k` on the model `V_k`; the *models* of the program are the pairs
`(V_k, Θ_k)`, `k ≤ m`. -/
abbrev boundary (k : ℕ) : QDivisor (P.model k) := divisorSeq Θ P.ΘY k

/-- The morphism `π_k : V_k ⟶ Z`. -/
abbrev toBase (k : ℕ) : P.model k ⟶ Z := modelMap π P.πY k

/-- The variety `V_m` of the *end* `(V_m, Θ_m)` of the program. -/
abbrev endModel : Scheme.{0} := P.model P.m

/-- The boundary `Θ_m` of the *end* `(V_m, Θ_m)` of the program. -/
abbrev endBoundary : QDivisor P.endModel := P.boundary P.m

omit [IsIntegral V] in
/-- The boundary of the model `V_0` is `Θ`. -/
@[simp]
theorem boundary_zero : P.boundary 0 = Θ := rfl

omit [IsIntegral V] in
/-- The boundary `Θ_{k+1}` of the model `V_{k+1}` is `ΘY k`. -/
@[simp]
theorem boundary_succ (k : ℕ) : P.boundary (k + 1) = P.ΘY k := rfl

omit [IsIntegral V] in
/-- The boundary of each later model is the strict transform of the previous one. -/
theorem boundary_succ_eq_flipTransform {k : ℕ} (hk : k < P.m) :
    P.boundary (k + 1) = flipTransform (P.g k) (P.gp k) (P.boundary k) :=
  P.ΘY_eq k hk

/-- The birational map `(g_k⁺)⁻¹ ∘ g_k : V_k ⤏ V_{k+1}` of the `k`-th step, `k < m`, as the
composite of chosen partial isomorphisms representing the birational morphisms `g_k` and
`g_k⁺`. -/
def flipPartialIso (k : ℕ) (hk : k < P.m) : (P.model k).PartialIso (P.model (k + 1)) :=
  (P.isFourfoldStepDiagram k hk).isBirationalMorphism_minus.choose.trans
    (P.isFourfoldStepDiagram k hk).isBirationalMorphism_plus.choose.symm

/-- The composite birational map `ψ_k : V_0 ⤏ V_k` of the first `k ≤ m` steps, as a partial
isomorphism. -/
def compositePartialIso : ∀ k : ℕ, k ≤ P.m → V.PartialIso (P.model k)
  | 0, _ => Scheme.PartialIso.refl V
  | k + 1, hk => (compositePartialIso k (Nat.le_of_succ_le hk)).trans (P.flipPartialIso k hk)

/-- The composite birational map `V_0 ⤏ V_m` of a finite relative program. -/
def compositeMap : RationalMap V P.endModel :=
  (P.compositePartialIso P.m le_rfl).toRationalMap

omit [IsIntegral V] in
/-- The composite birational map of a finite relative program is birational. -/
theorem isBirational_compositeMap : RationalMap.IsBirational P.compositeMap :=
  ⟨_, rfl⟩

omit [IsIntegral V] in
/-- If a partial isomorphism `e : X ⤏ T` represents a morphism `g : X ⟶ T` from a reduced scheme
and `h : T ⟶ S` has separated target, then `e` lies over `g ≫ h` and `h`. -/
theorem _root_.MMP.Fourfold.PartialIso.isOver_comp_of_toRationalMap_eq
    {X T S : Scheme.{0}} [IsReduced X] [IsSeparated (S ↘ ⊤_ Scheme)] (e : X.PartialIso T)
    (g : X ⟶ T) (h : T ⟶ S) (he : e.toRationalMap = g.toRationalMap) :
    e.IsOver (g ≫ h) h := by
  have h1 : (e.toPartialMap.compHom h).toRationalMap = (g ≫ h).toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap]
    change e.toRationalMap.compHom h = _
    rw [he]
    rfl
  have h2 := (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp h1)
  exact (Category.assoc _ _ _).symm.trans h2

omit [IsIntegral V] in
/-- The step partial isomorphism `V_k ⤏ V_{k+1}` lies over `π_k` and `π_{k+1}`. -/
theorem isOver_flipPartialIso [IsSeparated (Z ↘ ⊤_ Scheme)] (k : ℕ) (hk : k < P.m) :
    (P.flipPartialIso k hk).IsOver (P.toBase k) (P.toBase (k + 1)) := by
  have hm := (P.isFourfoldStepDiagram k hk).isBirationalMorphism_minus.choose_spec
  have hp := (P.isFourfoldStepDiagram k hk).isBirationalMorphism_plus.choose_spec
  have h1 := MMP.Fourfold.PartialIso.isOver_comp_of_toRationalMap_eq _ _ (P.h k) hm
  have h2 := MMP.Fourfold.PartialIso.isOver_comp_of_toRationalMap_eq _ _ (P.h k) hp
  rw [← P.modelMap_eq k hk] at h1
  rw [← P.πY_eq k hk] at h2
  exact h1.trans h2.symm

omit [IsIntegral V] in
/-- The composite partial isomorphism `ψ_k : V_0 ⤏ V_k` lies over `π` and `π_k`. -/
theorem isOver_compositePartialIso [IsSeparated (Z ↘ ⊤_ Scheme)] :
    ∀ (k : ℕ) (hk : k ≤ P.m), (P.compositePartialIso k hk).IsOver π (P.toBase k)
  | 0, _ => by
    simp only [compositePartialIso, Scheme.PartialIso.IsOver, Scheme.PartialIso.refl_iso,
      Iso.refl_hom]
    rfl
  | k + 1, hk => (isOver_compositePartialIso k (Nat.le_of_succ_le hk)).trans
      (P.isOver_flipPartialIso k hk)

omit [IsIntegral V] in
/-- The composite birational map `V_0 ⤏ V_m` is a map over `Z`: `π_m ∘ ψ_m = π`. -/
theorem compHom_compositeMap :
    P.compositeMap.compHom (P.toBase P.m) = π.toRationalMap := by
  have : IsSeparated sZ := P.isProjectiveVariety_base.1.toIsSeparated
  have hsep : IsSeparated (Z ↘ ⊤_ Scheme) := by
    have : (Z ↘ ⊤_ Scheme) = sZ ≫ Limits.terminal.from (Spec (.of ℂ)) := Subsingleton.elim _ _
    rw [this]
    infer_instance
  have H := P.isOver_compositePartialIso P.m le_rfl
  set e := P.compositePartialIso P.m le_rfl
  rw [compositeMap, ← Scheme.RationalMap.compHom_toRationalMap,
    Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨e.source, e.dense_source, le_rfl, le_top, ?_⟩
  change V.homOfLE (le_rfl : e.source ≤ e.source) ≫ (e.iso.hom ≫ e.target.ι) ≫ P.toBase P.m =
    V.homOfLE (le_top : e.source ≤ ⊤) ≫ V.topIso.hom ≫ π
  rw [Category.assoc, H]
  simp

end RelativeFourfoldProgram

end RelativeProgram

end MMP.Fourfold
