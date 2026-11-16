module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Analytic.GAGA.ProjectiveParts.Cohomology
public import MMP.AlgebraicGeometry.Analytic.GAGA.ProjectiveParts.Picard
public import MMP.AlgebraicGeometry.Analytic.GAGA.Differentials
public import MMP.AlgebraicGeometry.Analytic.GAGA.Hypercohomology
import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportClopen

/-!
# GAGA for projective complex schemes

The four parts of GAGA for a projective scheme `X` over `ℂ` (possibly nonreduced), each stated as
a named proposition about named objects, and their conjunction
`MMP.Analytic.analytification_gaga_projective`.

1. `MMP.Analytic.GAGACohomology`: the comparison maps `c^q : H^q(X, F) → H^q(X^an, F^an)` of
   coherent `F` are isomorphisms (`MMP.Analytic.comparisonIso`), natural in complex-linear maps
   with an analytic lift, and compatible with connecting maps of short exact sequences.
2. `MMP.Analytic.GAGAHypercohomology`: the comparison map on hypercohomology of a bounded complex
   of coherent sheaves with complex-linear differentials is an isomorphism, and on a complex
   concentrated in one degree it is `c^q`.
3. `MMP.Analytic.GAGAPicard`: analytification induces the isomorphism
   `MMP.Analytic.picardEquiv : Pic X ≃* Pic X^an`, `[L] ↦ [L^an]`; locally trivial modules
   analytify to locally trivial ones, every analytic one is an analytification, and locally
   trivial modules with isomorphic analytifications are isomorphic.
4. `MMP.Analytic.GAGASmoothForms`: if `X` is smooth and `E` is a reduced snc divisor, every
   connected component `Y` (an open subscheme) is an algebraic complex manifold and has, at each
   closed point, algebraic coordinates adapted to `E` that are holomorphic coordinates, in which
   algebraic (logarithmic, twisted logarithmic) forms analytify to the holomorphic ones
   (`MMP.Analytic.analytification_smooth_differentials`).

## References

* [J.-P. Serre, *Géométrie algébrique et géométrie analytique*][serre1956].
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open MMP.Analytic.Analytification

namespace MMP.Analytic

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))

/-- **GAGA (1): coherent cohomology.** The comparison maps of coherent sheaves are isomorphisms,
natural in complex-linear maps `φ` with an analytic lift `ψ`, and they commute with the connecting
maps of short exact sequences. -/
def GAGACohomology (hX : IsProjective sX) : Prop :=
  (∀ (F : X.Modules), Stacks.SheafOfModules.IsCoherent F → ∀ q : ℤ,
    IsIso (comparisonMap sX F q)) ∧
  (∀ {F G : X.Modules} (φ : (SheafOfModules.toSheaf _).obj F ⟶ (SheafOfModules.toSheaf _).obj G)
    (ψ : (SheafOfModules.toSheaf _).obj ((analytifyModule sX).obj F) ⟶
      (SheafOfModules.toSheaf _).obj ((analytifyModule sX).obj G)),
    IsComplexLinearHom sX φ → IsAnalyticLift sX φ ψ → ∀ q : ℤ,
      comparisonMap sX F q ≫ (sheafCohomology (space sX) q).map ψ =
        (sheafCohomology _ q).map φ ≫ comparisonMap sX G q) ∧
  ∀ {S : ShortComplex X.Modules} (hS : S.ShortExact) (q : ℤ),
    (shortExact_godementTotalOfModules sX hX hS).δ q (q + 1) rfl ≫
        comparisonMap sX S.X₁ (q + 1) =
      comparisonMap sX S.X₃ q ≫
        (shortExact_godementTotalOfModules_analytify sX hX hS).δ q (q + 1) rfl

/-- **GAGA (2): hypercohomology.** For a bounded complex of coherent sheaves with complex-linear
differentials and the analytified complex, the comparison map on hypercohomology is an
isomorphism; on a sheaf placed in degree `p` it is the comparison map `c^{n-p}`. -/
def GAGAHypercohomology : Prop :=
  (∀ (F : ℤ → X.Modules), (∀ p, Stacks.SheafOfModules.IsCoherent (F p)) → ∀ a b : ℤ,
    IsZeroOutside F a b →
    ∀ (δ : ∀ p, (SheafOfModules.toSheaf _).obj (F p) ⟶ (SheafOfModules.toSheaf _).obj (F (p + 1))),
    (∀ p, IsComplexLinearHom sX (δ p)) → ∀ (hδ : ∀ p, δ p ≫ δ (p + 1) = 0)
    (δan : ∀ p, (SheafOfModules.toSheaf _).obj ((analytifyModule sX).obj (F p)) ⟶
      (SheafOfModules.toSheaf _).obj ((analytifyModule sX).obj (F (p + 1))))
    (hδan : ∀ p, δan p ≫ δan (p + 1) = 0)
    (ι : (complexPullback (toSchemeHom sX)).obj (toSheafCochainComplex F δ hδ) ⟶
      toSheafCochainComplex (fun p => (analytifyModule sX).obj (F p)) δan hδan),
    (∀ p, ι.f p = analytifyModuleι sX (F p)) → ∀ n : ℤ, IsIso (hypercohomologyComparison sX ι n)) ∧
  ∀ (F : X.Modules) (p n : ℤ),
    hypercohomologyComparison sX (singleAnalytifyModuleι sX F p) n ≫
        (hypercohomologySingleIso (space sX) p n).hom.app
          ((SheafOfModules.toSheaf _).obj ((analytifyModule sX).obj F)) =
      (hypercohomologySingleIso X.toPresheafedSpace.carrier p n).hom.app
          ((SheafOfModules.toSheaf _).obj F) ≫ comparisonMap sX F (n - p)

/-- **GAGA (3): Picard groups.** Analytification induces the isomorphism `picardEquiv` of Picard
groups, `[L] ↦ [L^an]`; it preserves local triviality, every locally trivial analytic module is
the analytification of a locally trivial algebraic one, and locally trivial modules with
isomorphic analytifications are isomorphic. -/
def GAGAPicard (hX : IsProjective sX) : Prop :=
  (∀ (L : X.Modules) [hL : Stacks.Ample.IsInvertibleModule X L],
    picardEquiv sX hX (Stacks.SheafPicardGroup.schemeClassOf X L) =
      @Stacks.SheafPicardGroup.classOf _ _ (Opens.grothendieckTopology (space sX))
        (structureSheaf sX).obj (ringCatSheaf sX).2 _ _ ((analytifyModule sX).obj L)
        (isInvertible_analytifyModule sX L hL)) ∧
  (∀ L : X.Modules, IsLocallyTrivial L → IsLocallyTrivial ((analytifyModule sX).obj L)) ∧
  (∀ M : SheafOfModules.{0} (ringCatSheaf sX), IsLocallyTrivial M →
    ∃ L : X.Modules, IsLocallyTrivial L ∧ Nonempty ((analytifyModule sX).obj L ≅ M)) ∧
  ∀ L L' : X.Modules, IsLocallyTrivial L → IsLocallyTrivial L' →
    Nonempty ((analytifyModule sX).obj L ≅ (analytifyModule sX).obj L') → Nonempty (L ≅ L')

/-- Part (4) on one smooth variety `Y` of dimension `n` over `ℂ` with a divisor `E'`: `Y^an` is
an algebraic complex manifold, and at every closed point there are algebraic coordinates adapted
to `E'` identifying (logarithmic, twisted logarithmic) analytified forms with holomorphic ones. -/
def SmoothFormsGAGA {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) (n : ℕ) (E' : Mori.Divisor Y) :
    Prop :=
  ∃ (hv : Mori.IsVariety ℂ sY) (hs : Mori.IsSmoothScheme sY) (hd : topologicalKrullDim Y = n),
    letI := smoothOfRelativeDimension_of_isSmoothScheme sY hv hs hd
    IsAlgebraicComplexManifold sY n ∧ ∀ y : Y, IsClosed {y} → HasAnalyticLogCoordinatesAt sY n E' y

/-- **GAGA (4): differential and logarithmic forms.** If `X` is smooth and `E` is a reduced snc
divisor, the connected components of `X` are open, and every connected component `Y`, as an open
subscheme `j : Y ⟶ X` with the restriction of `E`, satisfies `SmoothFormsGAGA`. -/
def GAGASmoothForms : Prop :=
  Mori.IsSmoothScheme sX → ∀ E : Mori.Divisor X, Intersection.IsReducedEffective E →
    E.IsSNC sX →
    (∀ x₀ : X, IsOpen (connectedComponent x₀)) ∧
    ∀ {Y : Scheme.{0}} (j : Y ⟶ X) [IsOpenImmersion j] (x₀ : X),
      Set.range j.base = connectedComponent x₀ → ∀ {n : ℕ}, topologicalKrullDim Y = n →
        SmoothFormsGAGA (j ≫ sX) n (Finsupp.comapDomain (OpenWeilRestriction.primeDivisorMap j) E
          (OpenWeilRestriction.primeDivisorMap_injective j).injOn)

/-- A projective scheme `X` over `ℂ` satisfies `GAGACohomology`. -/
theorem gagaCohomology_of_isProjective (hX : IsProjective sX) : GAGACohomology sX hX :=
  ⟨isIso_comparisonMap_of_isProjective sX hX, comparisonMap_naturality sX hX,
    godementTotal_δ_comp_comparisonMap sX hX⟩

/-- A projective scheme `X` over `ℂ` satisfies `GAGAHypercohomology`. -/
theorem gagaHypercohomology_of_isProjective (hX : IsProjective sX) : GAGAHypercohomology sX :=
  ⟨isIso_hypercohomologyComparison_of_isProjective sX hX,
    hypercohomologyComparison_single sX⟩

/-- A projective scheme `X` over `ℂ` satisfies `GAGAPicard`. -/
theorem gagaPicard_of_isProjective (hX : IsProjective sX) : GAGAPicard sX hX := by
  haveI : IsProper sX := hX.isProper
  exact ⟨fun L _ => picardEquiv_schemeClassOf sX hX L, isLocallyTrivial_analytify sX,
    exists_analytify_iso_of_isLocallyTrivial sX hX,
    nonempty_iso_of_nonempty_analytify_iso sX hX⟩

/-- A proper scheme `X` over `ℂ` satisfies `GAGASmoothForms`. -/
theorem gagaSmoothForms_of_isProper [IsProper sX] : GAGASmoothForms sX := by
  intro hsm E hEred hE
  haveI : Smooth sX := (Mori.isSmoothScheme_iff sX).1 hsm
  refine ⟨fun x₀ => Stacks.Chow.isOpen_connectedComponent_of_smooth sX x₀,
    fun {Y} j _ _ hj n hdim => ?_⟩
  have hY := isVariety_of_range_eq_connectedComponent sX hsm j hj
  have hYs : Mori.IsSmoothScheme (j ≫ sX) := (Mori.isSmoothScheme_iff _).2 inferInstance
  exact ⟨hY, hYs, hdim, analytification_smooth_differentials (j ≫ sX) hY hYs hdim _
    (fun P => hEred (OpenWeilRestriction.primeDivisorMap j P)) (isSNC_comapDomain sX E hE j)⟩

/-- **GAGA for projective complex schemes** (Serre). For a projective scheme `X` over `ℂ`,
possibly nonreduced: (1) coherent cohomology, (2) hypercohomology of bounded complexes,
(3) Picard groups and (4) differential and logarithmic forms on smooth `X` are those of `X^an`,
as stated in `GAGACohomology`, `GAGAHypercohomology`, `GAGAPicard` and `GAGASmoothForms`. -/
@[mmp "thm_mmp_gaga_projective"]
public theorem analytification_gaga_projective (hX : IsProjective sX) :
    GAGACohomology sX hX ∧ GAGAHypercohomology sX ∧ GAGAPicard sX hX ∧ GAGASmoothForms sX :=
  haveI : IsProper sX := hX.isProper
  ⟨gagaCohomology_of_isProjective sX hX, gagaHypercohomology_of_isProjective sX hX,
    gagaPicard_of_isProjective sX hX, gagaSmoothForms_of_isProper sX⟩

end MMP.Analytic

end
