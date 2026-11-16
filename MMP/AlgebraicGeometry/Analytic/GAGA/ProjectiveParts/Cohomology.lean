module

public import MMP.AlgebraicGeometry.Analytic.Analytification
public import MMP.Topology.Sheaves.Godement
public import MMP.AlgebraicGeometry.Analytic.GAGA.Hypercohomology
public import MMP.AlgebraicGeometry.Analytic.GAGA.ProjectiveCohomology
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentWeakSerre
public import MMP.AlgebraicGeometry.Analytic.GAGA.Stalks

/-!
# GAGA for the cohomology of coherent sheaves and complexes on a projective scheme over `ℂ`

Parts (1) and (2) of `MMP.Analytic.analytification_gaga_projective`, stated over named pieces.
Let `X` be a projective scheme over `ℂ` (via `sX : X ⟶ Spec ℂ`), `α_X : X^an → X` the comparison
map and `F ↦ F^an` the analytification of `𝒪_X`-modules (`MMP.Analytic.analytifyModule`).

## Main definitions

* `MMP.Analytic.comparisonIso`: the comparison isomorphism `H^q(X, F) ≅ H^q(X^an, F^an)` of a
  coherent `F`, whose underlying map is `MMP.Analytic.comparisonMap`.
* `MMP.Analytic.IsComplexLinearHom`: a map of underlying abelian sheaves of `𝒪_X`-modules is
  `ℂ`-linear.
* `MMP.Analytic.IsAnalyticLift`: a map `ψ : F^an ⟶ G^an` of abelian sheaves lifts `φ : F ⟶ G`,
  that is `ψ (s ⊗ 1) = φ s ⊗ 1`.
* `MMP.Analytic.godementTotalShortComplex`, `MMP.Analytic.godementTotalOfModules`: the short
  complex of total complexes of Godement sections of a short complex of sheaves (of modules);
  `MMP.Analytic.toSheafShortComplex`: the underlying short complex of abelian sheaves.
* `MMP.Analytic.toSheafCochainComplex`: the complex of abelian sheaves with terms `F p` and
  differentials `δ p`.
* `MMP.Analytic.IsZeroOutside`: a family `F : ℤ → C` vanishes outside `[a, b]`.

The hypercohomology comparison `MMP.Analytic.hypercohomologyComparison`, the identification
`MMP.Analytic.hypercohomologySingleIso : ℍ^n(T, G[-p]) ≅ H^{n-p}(T, G)` and their compatibility
`MMP.Analytic.hypercohomologyComparison_single` live in `GAGA/Hypercohomology.lean`.

## Main statements

* `MMP.Analytic.comparisonMap_naturality`: `c^q` is natural for compatible pairs `(φ, ψ)`.
* `MMP.Analytic.shortExact_godementTotalOfModules`,
  `MMP.Analytic.shortExact_godementTotalOfModules_analytify`: a short exact sequence of
  `𝒪_X`-modules, and its analytification, give short exact sequences of Godement total
  complexes.
* `MMP.Analytic.godementTotal_δ_comp_comparisonMap`: `c^q` commutes with the connecting maps.
* `MMP.Analytic.isIso_hypercohomologyComparison_of_isProjective`: GAGA for hypercohomology of
  bounded complexes of coherent sheaves with `ℂ`-linear differentials.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open MMP.Analytic.Analytification

namespace MMP.Analytic

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))

/-- Analytification of `𝒪_X`-modules is a left adjoint (of the pushforward along `α_X`). -/
instance instIsLeftAdjointAnalytifyModule : (analytifyModule sX).IsLeftAdjoint :=
  (SheafOfModules.pullbackPushforwardAdjunction.{0} (ringCatSheafHom sX)).isLeftAdjoint

/-! ### (1) Coherent cohomology -/

/-- **Serre's GAGA comparison isomorphism** `c^q_F : H^q(X, F) ≅ H^q(X^an, F^an)` of a coherent
`𝒪_X`-module `F` on a projective scheme `X` over `ℂ`; its underlying map is
`MMP.Analytic.comparisonMap sX F q` (`comparisonIso_hom`). -/
noncomputable def comparisonIso (hX : IsProjective sX) (F : X.Modules)
    (hF : Stacks.SheafOfModules.IsCoherent F) (q : ℤ) :
    (sheafCohomology _ q).obj ((SheafOfModules.toSheaf _).obj F) ≅
      (sheafCohomology (space sX) q).obj
        ((SheafOfModules.toSheaf _).obj ((analytifyModule sX).obj F)) :=
  haveI := isIso_comparisonMap_of_isProjective sX hX F hF q
  asIso (comparisonMap sX F q)

/-- The underlying map of `MMP.Analytic.comparisonIso` is `MMP.Analytic.comparisonMap`. -/
@[simp]
theorem comparisonIso_hom (hX : IsProjective sX) (F : X.Modules)
    (hF : Stacks.SheafOfModules.IsCoherent F) (q : ℤ) :
    (comparisonIso sX hX F hF q).hom = comparisonMap sX F q :=
  rfl

/-- A map `φ : F ⟶ G` of the underlying abelian sheaves of `𝒪_X`-modules is `ℂ`-linear, for the
`ℂ`-structure of `𝒪_X` given by `sX`. -/
def IsComplexLinearHom {F G : X.Modules}
    (φ : (SheafOfModules.toSheaf _).obj F ⟶ (SheafOfModules.toSheaf _).obj G) : Prop :=
  ∀ (U : X.Opens) (c : ℂ) (s : F.val.obj (op U)),
    φ.hom.app (op U)
        ((show X.ringCatSheaf.obj.obj (op U) from ComplexPoints.baseRingHom sX U c) • s) =
      (show X.ringCatSheaf.obj.obj (op U) from ComplexPoints.baseRingHom sX U c) •
        (show G.val.obj (op U) from φ.hom.app (op U) s)

/-- A map `ψ : F^an ⟶ G^an` of abelian sheaves on `X^an` lifts `φ : F ⟶ G`: `ψ (s ⊗ 1) = φ s ⊗ 1`,
that is `ι_F ≫ ψ = α_X⁻¹ φ ≫ ι_G` with `ι = MMP.Analytic.analytifyModuleι`. -/
def IsAnalyticLift {F G : X.Modules}
    (φ : (SheafOfModules.toSheaf _).obj F ⟶ (SheafOfModules.toSheaf _).obj G)
    (ψ : (SheafOfModules.toSheaf _).obj ((analytifyModule sX).obj F) ⟶
      (SheafOfModules.toSheaf _).obj ((analytifyModule sX).obj G)) : Prop :=
  analytifyModuleι sX F ≫ ψ =
    (TopCat.Sheaf.pullback AddCommGrpCat.{0} (toSchemeHom sX)).map φ ≫ analytifyModuleι sX G

/-- **Naturality of the GAGA comparison map** for a `ℂ`-linear `φ : F ⟶ G` and a lift
`ψ : F^an ⟶ G^an` of it. -/
theorem comparisonMap_naturality (hX : IsProjective sX) {F G : X.Modules}
    (φ : (SheafOfModules.toSheaf _).obj F ⟶ (SheafOfModules.toSheaf _).obj G)
    (ψ : (SheafOfModules.toSheaf _).obj ((analytifyModule sX).obj F) ⟶
      (SheafOfModules.toSheaf _).obj ((analytifyModule sX).obj G))
    (_hφ : IsComplexLinearHom sX φ) (hψ : IsAnalyticLift sX φ ψ) (q : ℤ) :
    comparisonMap sX F q ≫ (sheafCohomology (space sX) q).map ψ =
      (sheafCohomology _ q).map φ ≫ comparisonMap sX G q := by
  have : IsProper sX := hX.isProper
  exact (analytification_stalks sX).2.2.2.2.2.2.2.2.1 F G φ ψ hψ q

/-- The short complex of total complexes of Godement sections `Tot(Γ(T, G^•(S_i[0])))` of a short
complex `S` of abelian sheaves on `T`. -/
noncomputable def godementTotalShortComplex {T : TopCat.{0}}
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} T)) :
    ShortComplex (CochainComplex AddCommGrpCat.{0} ℤ) :=
  S.map (HomologicalComplex.single _ (ComplexShape.up ℤ) 0 ⋙
    (godementSections T).mapHomologicalComplex _ ⋙
    HomologicalComplex₂.totalFunctor AddCommGrpCat.{0} (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (c₁₂ := ComplexShape.up ℤ))

/-- The underlying short complex of abelian sheaves of a short complex of sheaves of modules. -/
noncomputable def toSheafShortComplex {T : TopCat.{0}}
    {R : Sheaf (Opens.grothendieckTopology T) RingCat.{0}}
    (S : ShortComplex (SheafOfModules.{0} R)) :
    ShortComplex (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) :=
  S.map (SheafOfModules.toSheaf R)

/-- `godementTotalShortComplex` of the underlying short complex of abelian sheaves of a short
complex of sheaves of modules. -/
noncomputable def godementTotalOfModules {T : TopCat.{0}}
    {R : Sheaf (Opens.grothendieckTopology T) RingCat.{0}}
    (S : ShortComplex (SheafOfModules.{0} R)) :
    ShortComplex (CochainComplex AddCommGrpCat.{0} ℤ) :=
  godementTotalShortComplex (toSheafShortComplex S)

/-- A short exact sequence of `𝒪_X`-modules gives a short exact sequence of Godement total
complexes. -/
theorem shortExact_godementTotalOfModules (hX : IsProjective sX) {S : ShortComplex X.Modules}
    (hS : S.ShortExact) : (godementTotalOfModules S).ShortExact := by
  have : IsProper sX := hX.isProper
  obtain ⟨h, -, -⟩ := (analytification_stalks sX).2.2.2.2.2.2.2.2.2.1.1 S hS
  exact h

/-- The analytification of a short exact sequence of `𝒪_X`-modules gives a short exact sequence
of Godement total complexes on `X^an`. -/
theorem shortExact_godementTotalOfModules_analytify (hX : IsProjective sX)
    {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    (godementTotalOfModules (S.map (analytifyModule sX))).ShortExact := by
  have : IsProper sX := hX.isProper
  obtain ⟨-, h, -⟩ := (analytification_stalks sX).2.2.2.2.2.2.2.2.2.1.1 S hS
  exact h

/-- **The GAGA comparison maps commute with the connecting maps** of a short exact sequence
`0 → F₁ → F₂ → F₃ → 0` of `𝒪_X`-modules and of its analytification. -/
theorem godementTotal_δ_comp_comparisonMap (hX : IsProjective sX) {S : ShortComplex X.Modules}
    (hS : S.ShortExact) (q : ℤ) :
    (shortExact_godementTotalOfModules sX hX hS).δ q (q + 1) rfl ≫
        comparisonMap sX S.X₁ (q + 1) =
      comparisonMap sX S.X₃ q ≫
        (shortExact_godementTotalOfModules_analytify sX hX hS).δ q (q + 1) rfl := by
  have : IsProper sX := hX.isProper
  obtain ⟨_, _, h⟩ := (analytification_stalks sX).2.2.2.2.2.2.2.2.2.1.1 S hS
  exact h q

/-! ### (2) Hypercohomology of bounded complexes -/

/-- The cochain complex of abelian sheaves with terms the underlying sheaves of the modules
`F p` and differentials `δ p`. -/
noncomputable def toSheafCochainComplex {T : TopCat.{0}}
    {R : Sheaf (Opens.grothendieckTopology T) RingCat.{0}} (F : ℤ → SheafOfModules.{0} R)
    (δ : ∀ p, (SheafOfModules.toSheaf R).obj (F p) ⟶ (SheafOfModules.toSheaf R).obj (F (p + 1)))
    (hδ : ∀ p, δ p ≫ δ (p + 1) = 0) :
    CochainComplex (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) ℤ :=
  CochainComplex.of (fun p => (SheafOfModules.toSheaf R).obj (F p)) δ hδ

/-- A family `F : ℤ → C` vanishes outside `[a, b]`. -/
def IsZeroOutside {C : Type*} [Category C] (F : ℤ → C) (a b : ℤ) : Prop :=
  ∀ p, p < a ∨ b < p → IsZero (F p)

/-- **GAGA for hypercohomology.** For a bounded complex `K^•` of coherent `𝒪_X`-modules with
`ℂ`-linear differentials on a projective `X` over `ℂ`, and a morphism of complexes
`ι : α_X⁻¹ K^• ⟶ K^{•,an}` with components `analytifyModuleι`, the induced map
`ℍ^n(X, K^•) → ℍ^n(X^an, K^{•,an})` is an isomorphism. -/
theorem isIso_hypercohomologyComparison_of_isProjective (hX : IsProjective sX)
    (F : ℤ → X.Modules) (hF : ∀ p, Stacks.SheafOfModules.IsCoherent (F p)) (a b : ℤ)
    (hb : IsZeroOutside F a b)
    (δ : ∀ p, (SheafOfModules.toSheaf _).obj (F p) ⟶ (SheafOfModules.toSheaf _).obj (F (p + 1)))
    (_hδℂ : ∀ p, IsComplexLinearHom sX (δ p)) (hδ : ∀ p, δ p ≫ δ (p + 1) = 0)
    (δan : ∀ p, (SheafOfModules.toSheaf _).obj ((analytifyModule sX).obj (F p)) ⟶
      (SheafOfModules.toSheaf _).obj ((analytifyModule sX).obj (F (p + 1))))
    (hδan : ∀ p, δan p ≫ δan (p + 1) = 0)
    (ι : (complexPullback (toSchemeHom sX)).obj (toSheafCochainComplex F δ hδ) ⟶
      toSheafCochainComplex (fun p => (analytifyModule sX).obj (F p)) δan hδan)
    (hι : ∀ p, ι.f p = analytifyModuleι sX (F p)) (n : ℤ) :
    IsIso (hypercohomologyComparison sX ι n) :=
  isIso_hypercohomologyComparison_of_isProjective_of_bounded sX hX F hF hb δ hδ δan hδan ι hι n

end MMP.Analytic
