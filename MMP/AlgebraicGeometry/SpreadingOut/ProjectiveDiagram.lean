module
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.FundamentalExactSequenceSectionsSupplement
public import MMP.Attr
public import MMP.AlgebraicGeometry.Geometrically.HyperplaneSectionIntegralFibres
public import MMP.AlgebraicGeometry.Positivity.RelativelyAmple
public import MMP.AlgebraicGeometry.MMP.Fourfold.Defs
public import MMP.AlgebraicGeometry.Divisor.Canonical.Basic
import MMP.AlgebraicGeometry.SpreadingOut.LocalEquations
import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.Unconditional
import MMP.RingTheory.DualizingComplex.FlatLocalExtension
import MMP.AlgebraicGeometry.Modules.CurveFibreLineBundle
import MMP.AlgebraicGeometry.Geometrically.BertiniGenericFibres
import MMP.AlgebraicGeometry.SpreadingOut.GenericFibreDimension
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.Deminormal.Basic
import MMP.AlgebraicGeometry.Singularities.Snc.LocalEquations
import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParameters
import MMP.AlgebraicGeometry.Morphisms.Smooth.SmoothFlagParameters
import MMP.AlgebraicGeometry.Resolution.SNCPullback
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeLineBundle
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Resolution.SNCRestriction
import MMP.RingTheory.Kaehler.PluriformProduct
import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCanonical
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector

/-!
# Spreading out finite projective diagrams in characteristic zero

Let `k₀ ⊆ K` be algebraically closed fields of characteristic zero, and let `X` be a finite
diagram of integral projective `K`-schemes, together with finitely many invertible sheaves on its
vertices. Then there is a finitely generated `k₀`-subalgebra `R ⊆ K` and a diagram `Y` of
projective `R`-schemes with base change to `K` isomorphic to `X`, carrying models of the
invertible sheaves, with the following properties. Every diagram morphism of the model is
projective. Flatness, surjectivity, being an isomorphism or a closed immersion, smoothness of the
morphisms and of the vertices, and relative ampleness of the specified sheaves, whenever they hold
over `K`, already hold over `Spec R`. Isomorphisms between the specified sheaves and pullbacks of
other specified sheaves are kept, and so is an isomorphism of a specified sheaf with the sheaf
`⋀ⁿ Ω` of top relative differential forms, so a specified canonical sheaf has the canonical sheaf
of the model as its model. Over every field-valued point `Spec L ⟶ Spec R` the base change
of the model has integral vertices of the dimensions of the vertices of `X`, normal where the
vertex of `X` is normal. Birationality and smallness of morphisms, when they hold over `K`, hold
there too, and so does every decomposition of a fibre product of vertices as a finite disjoint
union of vertices: in particular every pullback square of the diagram stays a pullback square.
A projective log resolution of a normal vertex, with a crepant boundary supported on images of
vertices, stays on every such fibre a projective log resolution with the crepant boundary of the
same coefficients.

## Main results

* `MMP.exists_fg_subalgebra_model_of_isProjective_of_finCategory`: the spreading-out theorem.

## Implementation notes

The diagram is a functor `X : J ⥤ Over (Spec K)` from a finite category. A closed subvariety of a
vertex is a vertex of its own, joined to the ambient variety by a closed immersion. Normality is
not assumed of the vertices. It is concluded on the fibres at exactly the vertices where it holds
over `K`, so the normal varieties and the possibly non-normal subvarieties fit in one diagram. The
fibre over a point `t : Spec L ⟶ Spec R` is the diagram `Y ⋙ Over.pullback t`. Quantifying over
all field-valued points, rather than only over residue fields, gives the geometric fibres at the
same time. A simple normal crossing divisor is retained through its components and the connected
components of their intersections, as vertices with closed immersions. The scheme-theoretic
intersection `E ×_Z E'` of two components is the disjoint union of the connected components
`W₁, …, Wₙ` chosen as vertices; this is the statement that the canonical morphism
`∐ₖ Wₖ ⟶ E ×_Z E'` is an isomorphism, and it is kept on every fibre. With `n = 1` it says that a
square of the diagram is a pullback square; with `E = E' = Z` and identity arrows it says that `Z`
is the disjoint union of the `Wₖ`. Together with smoothness and dimension of the components and
of the intersections this makes the divisor simple normal crossing on every fibre. The canonical
sheaf of a smooth vertex of dimension `n` is pinned as the top relative differential forms
`⋀ⁿ Ω_{X_j/K}` (`AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms`); a specified sheaf
isomorphic to it has a model isomorphic to `⋀ⁿ Ω_{Y_j/R}`, which commutes with base change to the
fibres.

Log resolutions and crepant boundaries are kept with the repository's divisor vocabulary
(`MMP.Fourfold.IsLogResolution`, `MMP.Mori.IsCrepantBoundary`). A `ℚ`-divisor `∑ₗ qₗ Pₗ` on a
normal vertex `Z` is presented by vertices `Cₗ` with arrows `Cₗ ⟶ Z` whose images are the prime
divisors `Pₗ`. If `μ : W ⟶ Z` is a projective log resolution of `(Z, ∑ qₗ Pₗ)` over `K` and
`∑ q'ₗ P'ₗ`, presented in the same way on `W`, is its crepant boundary for a canonical divisor of
`Z`, then on every fibre the images of the same arrows are prime divisors `Pₗ,ₛ` and `P'ₗ,ₛ`, the
fibre of `μ` is a projective log resolution of `(Z_s, ∑ qₗ Pₗ,ₛ)`, and `∑ q'ₗ P'ₗ,ₛ` is its crepant
boundary for some canonical divisor of `Z_s`, with the same coefficients. The canonical divisor
of a normal, possibly singular, fibre is part of the conclusion, through
`MMP.Mori.Divisor.IsCanonicalDivisor` inside the crepant boundary, and so are the Cartier
multiples of the adjoint divisors. The instances `IsIntegral`, `IsLocallyNoetherian` and
`IsNormal` on the fibre of the target are bound in this conclusion; they hold whenever the vertex
of `X` is normal.

The proof chooses the model `Y₀` over a first finitely generated subalgebra `R₀ ⊆ K` by the
finite coefficient model; the model over a larger `R` is the base change of `Y₀`. Every property
in the conclusion holds over all `R` beyond some `S ⊇ R₀`, and finitely many of them hold together
beyond a common one, since the finitely generated subalgebras of `K` form a directed set. The
properties of the fibres rest on the geometric integrality and normality of the generic fibres;
crepant boundaries are carried to the fibres through local equations of the Cartier multiples
`m (K + Δ)` and of their pull-backs, which spread to late fibres.

## References

* [EGA IV, 8.10, 9.7, 12.2]
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
-/

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace MMP.Spreading

/-! ### The properties of the model that rest on its fibres -/

section Properties

variable {k₀ K : Type u} [Field k₀] [Field K] [IsAlgClosed k₀] [IsAlgClosed K] [CharZero k₀]
  [Algebra k₀ K] {J : Type u} [SmallCategory J] [FinCategory J] {X : J ⥤ Over (Spec (.of K))}
  (hint : ∀ j, IsIntegral (X.obj j).left)
  {ι : Type u} [Finite ι] {v : ι → J} {𝓛 : ∀ i, (X.obj (v i)).left.Modules}
  [h𝓛 : ∀ i, Stacks.Ample.IsInvertibleModule _ (𝓛 i)]

/-- A finite diagram of integral projective `K`-schemes with finitely many invertible sheaves on
its vertices has a coefficient model `Model k₀ X v 𝓛`. -/
private lemma exists_model (hproj : ∀ j, IsProjective (X.obj j).hom) :
    Nonempty (Model k₀ X v 𝓛) := by
  classical
  have : Fintype J := FinCategory.fintypeObj
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨n, ιX, hιc, hιo⟩ := exists_common_embedding X hproj
  have hcoh : ∀ e : Discrete ι, SheafOfModules.IsCoherent (𝓛 e.as) := fun e => by
    have : IsLocallyNoetherian (X.obj (v e.as)).left := by
      have : FinitePresentation (X.obj (v e.as)).hom := by
        rw [← hιo]
        exact CoefficientModels.finitePresentation_of_isImmersion_projectiveSpaceOver K n _
      have : LocallyOfFinitePresentation (X.obj (v e.as)).hom := this.1
      exact LocallyOfFiniteType.isLocallyNoetherian (X.obj (v e.as)).hom
    exact Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible _ _
  obtain ⟨R, hR, Y, ιY, p, hp, N₀, θ₀, μY, himm, hover, hpb, -, hcl, -, -, -, -, -, -, -, -,
      hinv, -, -⟩ :=
    MMP.exists_fg_subalgebra_model_of_finCategory k₀ K X n ιX (fun j => inferInstance) hιo
      (Discrete.functor v) (fun e => 𝓛 e.as) hcoh (discreteμ X v _) (discreteμ_id X v _)
      (discreteμ_comp X v _)
  have : IsNoetherianRing R := CoefficientModels.isNoetherianRing_of_fg k₀ K ⟨R, hR⟩
  have hcl' : ∀ j, IsClosedImmersion (ιY j) := fun j => hcl j (hιc j)
  refine ⟨⟨⟨R, hR⟩, Y, p, ⟨hp, hpb⟩, fun i => N₀ ⟨i⟩, fun i => θ₀ ⟨i⟩,
    fun i => hinv ⟨i⟩ (h𝓛 i), fun j => ?_, fun j => ⟨n, ιY j, hcl' j, hover j⟩⟩⟩
  rw [← hover j]
  have hP := ProjectiveQuot.finitePresentation_projectiveSpaceOver n (Spec (.of R))
  have : LocallyOfFinitePresentation (projectiveSpaceOver n (Spec (.of R)) ↘ Spec (.of R)) :=
    hP.1
  have : QuasiCompact (projectiveSpaceOver n (Spec (.of R)) ↘ Spec (.of R)) := hP.2.1
  have : IsLocallyNoetherian (projectiveSpaceOver n (Spec (.of R))) :=
    LocallyOfFiniteType.isLocallyNoetherian (projectiveSpaceOver n (Spec (.of R)) ↘ Spec (.of R))
  have : CompactSpace (projectiveSpaceOver n (Spec (.of R))) :=
    QuasiCompact.compactSpace_of_compactSpace
      (projectiveSpaceOver n (Spec (.of R)) ↘ Spec (.of R))
  have : IsNoetherian (projectiveSpaceOver n (Spec (.of R))) := ⟨⟩
  have : TopologicalSpace.NoetherianSpace (Y.obj j).left := (ιY j).isEmbedding.noetherianSpace
  exact ⟨inferInstance, inferInstance, inferInstance⟩

variable (M : Model k₀ X v 𝓛)

/-- **Geometric integrality, dimension and normality of the fibres of a proper model.** Let
`f : Y ⟶ Spec R` be proper and locally of finite type over a finitely generated `k₀`-subalgebra
`R ⊆ K`, with integral base change `X` to `K`. Outside the zero set of one nonzero element of `R`
the fibres of `f` are geometrically integral of the dimension of `X`, and geometrically normal if
`X` is normal (Theorems
`MMP.exists_ne_zero_forall_geometricallyIntegral_fiber_of_isProper_of_generic`
and `MMP.exists_ne_zero_forall_geometrically_isNormal_fiber`). -/
private lemma exists_ne_zero_geometric (R : Subalgebra k₀ K) (hR : R.FG) {Y X' : Scheme.{u}}
    (f : Y ⟶ Spec (.of R)) [IsProper f] (p : X' ⟶ Y)
    (s : X' ⟶ Spec (.of K)) (hps : IsPullback p s f (κ R)) [IsIntegral X'] :
    ∃ r : R, r ≠ 0 ∧ ∀ y : Spec (.of R), r ∉ y.asIdeal →
      geometrically IsIntegral (f.fiberToSpecResidueField y) ∧
      geometrically (fun Z : Scheme.{u} => topologicalKrullDim Z = topologicalKrullDim X')
        (f.fiberToSpecResidueField y) ∧
      (IsNormal X' → geometrically IsNormal
        (f.fiberToSpecResidueField y)) := by
  classical
  have : Algebra.FiniteType k₀ R := (Subalgebra.fg_iff_finiteType _).mp hR
  -- the point `Spec K ⟶ Spec R` factors through the generic point
  let e := Scheme.SpecToEquivOfField K (Spec (.of R)) (κ R)
  have hκ : κ R = Spec.map e.2 ≫ (Spec (.of R)).fromSpecResidueField e.1 := by
    have := (Scheme.SpecToEquivOfField K (Spec (.of R))).symm_apply_apply (κ R)
    rw [← this]
    rfl
  have he : e.1 = genericPoint (Spec (.of R)) := by
    rw [genericPoint_eq_bot_of_affine]
    exact κ_apply_eq_bot R _
  -- `X'` is the base change of the generic fibre
  letI : Algebra ((Spec (.of R)).residueField e.1) K := e.2.hom.toAlgebra
  let ρ := (Spec (.of R)).fromSpecResidueField e.1
  let q : X' ⟶ pullback f ρ := pullback.lift p (s ≫ Spec.map e.2)
    (by rw [Category.assoc, ← hκ]; exact hps.w)
  have hsq : IsPullback q s (pullback.snd f ρ)
      (Spec.map (CommRingCat.ofHom (algebraMap ((Spec (.of R)).residueField e.1) K))) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f _)
    have h1 : q ≫ pullback.fst f ρ = p := pullback.lift_fst _ _ _
    rw [h1]
    exact hκ ▸ hps
  have hlft' : LocallyOfFiniteType (pullback.snd f ρ) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback f ρ) inferInstance
  have : CharZero K := charZero_of_injective_ringHom (algebraMap k₀ K).injective
  have : CharZero ((Spec (.of R)).residueField e.1) :=
    (RingHom.charZero_iff (algebraMap ((Spec (.of R)).residueField e.1) K).injective).mpr
      inferInstance
  have : PerfectField ((Spec (.of R)).residueField e.1) := PerfectField.ofCharZero
  have hgi : GeometricallyIntegral (f.fiberToSpecResidueField e.1) :=
    geometricallyIntegral_of_isPullback (F := (Spec (.of R)).residueField e.1) (K := K)
      (pullback.snd f ρ) s q hsq
  have hdim : topologicalKrullDim X' = topologicalKrullDim (f.fiber e.1) :=
    @topologicalKrullDim_baseChange ((Spec (.of R)).residueField e.1) K _ _ _ _ _ q
      s (pullback.snd f ρ) hsq hlft'
  obtain ⟨hq₁, hq₂⟩ := flat_surjective_specMap
    (algebraMap ((Spec (.of R)).residueField e.1) K)
  have hqf : Flat q := MorphismProperty.of_isPullback hsq.flip hq₁
  have hqs : Surjective q := MorphismProperty.of_isPullback hsq.flip hq₂
  obtain ⟨r₁, hr₁, H₁⟩ :=
    MMP.exists_ne_zero_forall_geometricallyIntegral_fiber_of_isProper_of_generic k₀ f (he ▸ hgi)
  obtain ⟨r₂, hr₂, H₂⟩ : ∃ r₂ : R, r₂ ≠ 0 ∧ (IsNormal X' →
      ∀ s : Spec (.of R), r₂ ∉ s.asIdeal →
        geometrically IsNormal (f.fiberToSpecResidueField s)) := by
    by_cases hn : IsNormal X'
    · have : IsNormal (f.fiber e.1) := isNormal_of_forall_exists_flat fun y =>
        ⟨X', q, hqf, hn, hqs.surj y⟩
      obtain ⟨r₂, hr₂, H₂⟩ :=
        MMP.exists_ne_zero_forall_geometrically_isNormal_fiber k₀ f (he ▸ this)
      exact ⟨r₂, hr₂, fun _ s hs => (H₂ s hs).1⟩
    · exact ⟨1, one_ne_zero, fun h => absurd h hn⟩
  refine ⟨r₁ * r₂, mul_ne_zero hr₁ hr₂, fun y hy => ?_⟩
  have hy₁ : r₁ ∉ y.asIdeal := fun h₁ => hy (y.asIdeal.mul_mem_right r₂ h₁)
  have hy₂ : r₂ ∉ y.asIdeal := fun h₂ => hy (y.asIdeal.mul_mem_left r₁ h₂)
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (fun Z : Scheme.{u} => topologicalKrullDim Z = topologicalKrullDim X') :=
    isClosedUnderIsomorphisms_topologicalKrullDim _
  refine ⟨(geometricallyIntegral_iff _).mp (H₁ y hy₁).1, ?_, fun hn => H₂ hn y hy₂⟩
  have hl : LocallyOfFiniteType (f.fiberToSpecResidueField y) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback f _) inferInstance
  have h₃ := @geometrically_topologicalKrullDim_eq _ _ _ (f.fiberToSpecResidueField y) hl
  rwa [(H₁ y hy₁).2, ← he, ← hdim] at h₃

include hint in
/-- **Geometric integrality, dimension and normality of the vertices** spread from `K` to all late
stages (Theorems `MMP.exists_ne_zero_forall_geometricallyIntegral_fiber_of_isProper_of_generic`
and `MMP.exists_ne_zero_forall_geometrically_isNormal_fiber` on the first stage, after inverting
one nonzero element). -/
private lemma Model.eventually_geometric (j : J) : M.Eventually fun S h =>
    geometrically IsIntegral ((M.stage h).obj j).hom ∧
    geometrically (fun Z : Scheme.{u} => topologicalKrullDim Z = topologicalKrullDim (X.obj j).left)
      ((M.stage h).obj j).hom ∧
    (IsNormal (X.obj j).left →
      geometrically IsNormal ((M.stage h).obj j).hom) := by
  have := hint j
  have : IsProper (M.Y.obj j).hom := isProper_of_isProjectiveMorphism _ (M.hproj j)
  have := (M.fp j).1
  obtain ⟨r, hr, H⟩ := exists_ne_zero_geometric M.R.1 M.R.2 (M.Y.obj j).hom (M.p j)
    (X.obj j).hom (M.cart.isPullback j)
  obtain ⟨S₀, h₀, H₀⟩ := exists_le_forall_notMem_asIdeal M.R r hr
  refine ⟨S₀, h₀, fun S h => ?_⟩
  have hU : Set.range (π (show M.R.1 ≤ S.1 from h₀.trans h)).base ⊆ {y | r ∉ y.asIdeal} := by
    rintro _ ⟨y, rfl⟩
    exact H₀ S h y
  have := isClosedUnderIsomorphisms_isIntegral
  have := isClosedUnderIsomorphisms_isNormal
  have := isClosedUnderIsomorphisms_topologicalKrullDim (topologicalKrullDim (X.obj j).left)
  exact ⟨geometrically_pullback_snd_of_fibers _ _ _ hU fun y hy => (H y hy).1,
    geometrically_pullback_snd_of_fibers _ _ _ hU fun y hy => (H y hy).2.1,
    fun hn => geometrically_pullback_snd_of_fibers _ _ _ hU fun y hy => (H y hy).2.2 hn⟩

include hint in
/-- **Prime divisors spread to prime divisors of the fibres.** The ideal sheaf of a prime divisor
`P` of a vertex over `K` is the inverse image of an ideal sheaf `𝓘₀` of the vertex at some stage,
whose inverse image in every integral fibre of the right dimension over every late stage is the
ideal sheaf of a prime divisor. -/
private lemma Model.exists_primeDivisor (j : J)
    (P : AlgebraicGeometry.PrimeDivisor (X.obj j).left) :
    ∃ (S₀ : CoefficientModels.FGSub k₀ K) (h₀ : M.R ≤ S₀)
      (𝓘₀ : ((M.stage h₀).obj j).left.IdealSheafData),
      𝓘₀.comap (M.cmp h₀ j) = P.idealSheaf ∧
      ∃ (S₂ : CoefficientModels.FGSub k₀ K) (h₂ : S₀ ≤ S₂), ∀ (S : CoefficientModels.FGSub k₀ K)
        (h : S₂ ≤ S) (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)),
        IsIntegral ((M.stage (h₀.trans (h₂.trans h)) ⋙ Over.pullback t).obj j).left →
        topologicalKrullDim ((M.stage (h₀.trans (h₂.trans h)) ⋙ Over.pullback t).obj j).left =
          topologicalKrullDim (X.obj j).left →
        ∃ Ps : AlgebraicGeometry.PrimeDivisor
            ((M.stage (h₀.trans (h₂.trans h)) ⋙ Over.pullback t).obj j).left,
          Ps.idealSheaf = 𝓘₀.comap (M.fibreMap h₀ (h₂.trans h) t j) := by
  classical
  have := hint j
  -- the dimension of the vertex
  have : IsProper (M.Y.obj j).hom := isProper_of_isProjectiveMorphism _ (M.hproj j)
  have : IsProper (X.obj j).hom :=
    MorphismProperty.of_isPullback (P := @IsProper) (M.cart.isPullback j) inferInstance
  have := M.locallyOfFiniteType_obj j
  obtain ⟨d, hd⟩ := Model.exists_topologicalKrullDim_eq hint M j
  obtain ⟨hd1, hPdim⟩ := topologicalKrullDim_support (X.obj j).hom hd P
  -- the closed subscheme and its model
  let iE := P.idealSheaf.subschemeι
  haveI : IsIntegral P.idealSheaf.subscheme := P.integral
  obtain ⟨S₀, h₀, E₀, e₀, q₀, he₀, hsq⟩ := M.exists_closedSubscheme j iE
  have hE : topologicalKrullDim P.idealSheaf.subscheme = ((d - 1 : ℕ) : WithBot ℕ∞) := by
    rw [← Stacks.AlgebraicGeometry.ComponentDegrees.topologicalKrullDim_range_eq iE,
        Scheme.IdealSheafData.range_subschemeι]
    exact hPdim
  have : IsProper ((M.stage h₀).obj j).hom :=
    MorphismProperty.of_isPullback (P := @IsProper) (IsPullback.of_hasPullback _ _)
      (inferInstance : IsProper (M.Y.obj j).hom)
  have := (M.finitePresentation_stage h₀ j).1
  let f := e₀ ≫ ((M.stage h₀).obj j).hom
  have hps : IsPullback q₀ (iE ≫ (X.obj j).hom) f (κ S₀.1) :=
    hsq.paste_vert ((M.isCartesian_cmp h₀).isPullback j)
  obtain ⟨r, hr, H⟩ := exists_ne_zero_geometric S₀.1 S₀.2 f q₀ _ hps
  obtain ⟨S₂, h₂, H₂⟩ := exists_le_forall_notMem S₀ r hr
  refine ⟨S₀, h₀, e₀.ker, ?_, S₂, h₂, fun S h L _ t hint' hdim' => ?_⟩
  · have hiso := hsq.flip.isoPullback_hom_fst
    rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
      ← Scheme.Hom.ker_comp_of_isIso hsq.flip.isoPullback.hom, hiso]
    exact Scheme.IdealSheafData.ker_subschemeι _
  · -- the fibre of the model of the prime divisor
    set fm := M.fibreMap h₀ (h₂.trans h) t j
    have hP := M.isPullback_fibreMap h₀ (h₂.trans h) t j
    have hQ := (IsPullback.of_hasPullback fm e₀).flip.paste_vert hP
    obtain ⟨hI, hD, -⟩ := fibre_of_exists_ne_zero_geometric f r H L
      (t ≫ π (show S₀.1 ≤ S.1 from h₂.trans h)) (H₂ S h L t)
    have := isClosedUnderIsomorphisms_isIntegral
    have := isClosedUnderIsomorphisms_topologicalKrullDim
      (topologicalKrullDim P.idealSheaf.subscheme)
    have hI' : IsIntegral (pullback (C := Scheme.{u}) fm e₀) :=
      ObjectProperty.prop_of_iso _ hQ.isoPullback.symm hI
    have hD' : topologicalKrullDim (pullback (C := Scheme.{u}) fm e₀) =
        topologicalKrullDim P.idealSheaf.subscheme :=
      ObjectProperty.prop_of_iso
        (fun Z : Scheme.{u} => topologicalKrullDim Z = topologicalKrullDim P.idealSheaf.subscheme)
        hQ.isoPullback.symm hD
    have hcl : IsClosedImmersion (pullback.fst fm e₀) :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion)
        (IsPullback.of_hasPullback fm e₀).flip he₀
    have hT : Set.range (pullback.fst fm e₀).base = fm ⁻¹' Set.range e₀.base :=
      Scheme.Pullback.range_fst _ _
    have := M.locallyOfFiniteType_fibre (h₀.trans (h₂.trans h)) t j
    haveI := hint'
    haveI := hI'
    obtain ⟨Ps, hPs⟩ := exists_primeDivisor_support_eq
      ((M.stage (h₀.trans (h₂.trans h)) ⋙ Over.pullback t).obj j).hom (hdim'.trans hd) hd1
      (pullback.fst fm e₀).isClosedEmbedding.isClosed_range
      (by
        rw [← Set.image_univ]
        exact (IrreducibleSpace.isIrreducible_univ _).image _
          (pullback.fst fm e₀).continuous.continuousOn)
      (by rw [Stacks.AlgebraicGeometry.ComponentDegrees.topologicalKrullDim_range_eq, hD', hE])
    refine ⟨Ps, ?_⟩
    -- both ideal sheaves are reduced with the same support
    have hker : e₀.ker.comap fm = (pullback.fst fm e₀).ker :=
      (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion e₀ fm).symm
    have hred : IsReduced ((pullback.fst fm e₀).ker.subscheme) := by
      have : IsIso (pullback.fst fm e₀).toImage := inferInstance
      exact isReduced_of_isOpenImmersion (inv (pullback.fst fm e₀).toImage)
    have hsupp : (pullback.fst fm e₀).ker.support = Ps.idealSheaf.support := by
      ext x
      rw [Scheme.Hom.support_ker, (pullback.fst fm e₀).isClosedEmbedding.isClosed_range.closure_eq]
      change x ∈ Set.range (pullback.fst fm e₀).base ↔ x ∈ Ps.support
      rw [hPs]
    haveI : IsReduced Ps.idealSheaf.subscheme := by
      haveI := Ps.integral
      infer_instance
    rw [hker, Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ hsupp]
    exact Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme Ps.idealSheaf _ rfl

include hint in
/-- **Finitely many prime divisors spread together**: `Model.exists_primeDivisor` for a finite
family of prime divisors of a vertex, with models at one common stage. -/
private lemma Model.exists_primeDivisor_family (j : J)
    (𝓔 : Finset (Mori.PrimeDivisor (X.obj j).left)) :
    ∃ (S₀ : CoefficientModels.FGSub k₀ K) (h₀ : M.R ≤ S₀)
      (𝓘 : Mori.PrimeDivisor (X.obj j).left → ((M.stage h₀).obj j).left.IdealSheafData),
      (∀ E ∈ 𝓔, (𝓘 E).comap (M.cmp h₀ j) = E.idealSheaf) ∧
      ∀ (S : CoefficientModels.FGSub k₀ K) (h : S₀ ≤ S) (L : Type u) [Field L]
        (t : Spec (.of L) ⟶ Spec (.of S.1)),
        IsIntegral ((M.stage (h₀.trans h) ⋙ Over.pullback t).obj j).left →
        topologicalKrullDim ((M.stage (h₀.trans h) ⋙ Over.pullback t).obj j).left =
          topologicalKrullDim (X.obj j).left →
        ∀ E ∈ 𝓔, ∃ Ps : Mori.PrimeDivisor ((M.stage (h₀.trans h) ⋙ Over.pullback t).obj j).left,
          Ps.idealSheaf = (𝓘 E).comap (M.fibreMap h₀ h t j) := by
  classical
  choose S₀ h₀ I hI S₂ h₂ H using fun E => M.exists_primeDivisor hint j E
  obtain ⟨T, hT⟩ := Finset.exists_le (insert M.R (𝓔.image S₂))
  have hRT : M.R ≤ T := hT _ (Finset.mem_insert_self _ _)
  have hET : ∀ E ∈ 𝓔, S₂ E ≤ T := fun E hE =>
    hT _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hE))
  let 𝓘 : Mori.PrimeDivisor (X.obj j).left → ((M.stage hRT).obj j).left.IdealSheafData :=
    fun E => if hE : E ∈ 𝓔 then (I E).comap (M.stageCmp (h₀ E) ((h₂ E).trans (hET E hE)) j)
      else ⊥
  refine ⟨T, hRT, 𝓘, fun E hE => ?_, fun S h L _ t hint' hdim' E hE => ?_⟩
  · simp only [𝓘, dif_pos hE]
    rw [← Scheme.IdealSheafData.comap_comp, M.cmp_stageCmp]
    exact hI E
  · obtain ⟨Ps, hPs⟩ := H E S ((hET E hE).trans h) L t hint' hdim'
    refine ⟨Ps, ?_⟩
    simp only [𝓘, dif_pos hE]
    rw [← Scheme.IdealSheafData.comap_comp, M.fibreMap_comp]
    exact hPs

open Classical in
include hint in
/-- **Simple normal crossing divisors spread to the fibres.** The components of a simple normal
crossing divisor over `K` have models at a stage whose fibres are the components of a simple normal
crossing divisor on every integral smooth fibre of the right dimension over every late stage. -/
private lemma Model.exists_isSNC (j : J) (𝓔 : Finset (Mori.PrimeDivisor (X.obj j).left))
    (hsnc : Mori.DivisorWithCoeffs.IsSNC (X.obj j).hom (∑ E ∈ 𝓔, Finsupp.single E (1 : ℤ))) :
    ∃ (S₀ : CoefficientModels.FGSub k₀ K) (h₀ : M.R ≤ S₀)
      (𝓘 : Mori.PrimeDivisor (X.obj j).left → ((M.stage h₀).obj j).left.IdealSheafData),
      (∀ E ∈ 𝓔, (𝓘 E).comap (M.cmp h₀ j) = E.idealSheaf) ∧
      ∃ (S₂ : CoefficientModels.FGSub k₀ K) (h₂ : S₀ ≤ S₂), ∀ (S : CoefficientModels.FGSub k₀ K)
        (h : S₂ ≤ S) (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)),
        IsIntegral ((M.stage (h₀.trans (h₂.trans h)) ⋙ Over.pullback t).obj j).left →
        topologicalKrullDim ((M.stage (h₀.trans (h₂.trans h)) ⋙ Over.pullback t).obj j).left =
          topologicalKrullDim (X.obj j).left →
        Smooth ((M.stage (h₀.trans (h₂.trans h)) ⋙ Over.pullback t).obj j).hom →
        ∃ ρ : 𝓔 → Mori.PrimeDivisor ((M.stage (h₀.trans (h₂.trans h)) ⋙ Over.pullback t).obj
            j).left,
          (∀ E, (ρ E).idealSheaf = (𝓘 E).comap (M.fibreMap h₀ (h₂.trans h) t j)) ∧
          Function.Injective ρ ∧
          Mori.DivisorWithCoeffs.IsSNC ((M.stage (h₀.trans (h₂.trans h)) ⋙ Over.pullback t).obj
              j).hom
            (∑ F ∈ Finset.univ.image ρ, Finsupp.single F (1 : ℤ)) := by
  classical
  have := hint j
  have : CharZero K := charZero_of_injective_ringHom (algebraMap k₀ K).injective
  have : PerfectField K := PerfectField.ofCharZero
  have hlftK := M.locallyOfFiniteType_obj j
  obtain ⟨S₀, h₀, 𝓘, h𝓘, Hfam⟩ := M.exists_primeDivisor_family hint j 𝓔
  -- the models of the intersections and their properties over `K`
  have hcomap : ∀ J ⊆ 𝓔, (J.sup 𝓘).comap (M.cmp h₀ j) = interIdeal J := fun J hJ => by
    rw [comap_finset_sup]
    exact Finset.sup_congr rfl fun E hE => h𝓘 E (hJ hE)
  have hJ : ∀ J : Finset (Mori.PrimeDivisor (X.obj j).left), ∃ (S₂ : CoefficientModels.FGSub k₀ K)
      (h₂ : S₀ ≤ S₂), J ⊆ 𝓔 → ∀ (S : CoefficientModels.FGSub k₀ K) (h : S₂ ≤ S) (L : Type u)
        [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)),
        IsIntegral ((M.stage (h₀.trans (h₂.trans h)) ⋙ Over.pullback t).obj j).left →
        topologicalKrullDim ((M.stage (h₀.trans (h₂.trans h)) ⋙ Over.pullback t).obj j).left =
          topologicalKrullDim (X.obj j).left →
        Mori.IsSmoothScheme (((J.sup 𝓘).comap (M.fibreMap h₀ (h₂.trans h) t j)).subschemeι ≫
          ((M.stage (h₀.trans (h₂.trans h)) ⋙ Over.pullback t).obj j).hom) ∧
        ∀ x ∈ ((J.sup 𝓘).comap (M.fibreMap h₀ (h₂.trans h) t j)).support,
          (J.card : ℕ∞) ≤ Order.coheight x := by
    intro J
    by_cases hJ𝓔 : J ⊆ 𝓔
    · obtain ⟨hsm, hco⟩ := interIdeal_of_isSNC (X.obj j).hom 𝓔 hsnc hJ𝓔
      obtain ⟨S₃, h₃, H₃⟩ := M.exists_isSmoothScheme_comap h₀ j (J.sup 𝓘)
        (by rwa [hcomap J hJ𝓔])
      obtain ⟨S₄, h₄, H₄⟩ := M.exists_le_coheight_comap hint h₀ j (J.sup 𝓘) J.card
        (by rwa [hcomap J hJ𝓔])
      obtain ⟨T, hT₃, hT₄⟩ := exists_ge_ge S₃ S₄
      exact ⟨T, h₃.trans hT₃, fun _ S h L _ t hI hD =>
        ⟨H₃ S (hT₃.trans h) L t, H₄ S (hT₄.trans h) L t hI hD⟩⟩
    · exact ⟨S₀, le_rfl, fun h => absurd h hJ𝓔⟩
  choose S₂ h₂ H using hJ
  obtain ⟨T, hT⟩ := Finset.exists_le (insert S₀ (𝓔.powerset.image S₂))
  have hS₀T : S₀ ≤ T := hT _ (Finset.mem_insert_self _ _)
  have hJT : ∀ J ∈ 𝓔.powerset, S₂ J ≤ T := fun J hJ =>
    hT _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hJ))
  refine ⟨S₀, h₀, 𝓘, h𝓘, T, hS₀T, fun S h L _ t hint' hdim' hsm => ?_⟩
  have := charZero_of_point t
  have : PerfectField L := PerfectField.ofCharZero
  haveI := hint'
  have := M.locallyOfFiniteType_fibre (h₀.trans (hS₀T.trans h)) t j
  have hfam := Hfam S (hS₀T.trans h) L t hint' hdim'
  choose ρ hρ using fun E : 𝓔 => hfam E.1 E.2
  have hJS := fun (J : Finset (Mori.PrimeDivisor (X.obj j).left)) (hJ : J ⊆ 𝓔) =>
    H J hJ S ((hJT J (Finset.mem_powerset.mpr hJ)).trans h) L t hint' hdim'
  -- the fibre of the intersection over a subfamily
  have hsupJ : ∀ s : Finset 𝓔, ((s.map (Function.Embedding.subtype _)).sup 𝓘).comap
      (M.fibreMap h₀ (hS₀T.trans h) t j) = s.sup fun E => (ρ E).idealSheaf := fun s => by
    rw [comap_finset_sup, Finset.sup_map]
    exact Finset.sup_congr rfl fun E _ => (hρ E).symm
  have hsub : ∀ s : Finset 𝓔, s.map (Function.Embedding.subtype _) ⊆ 𝓔 := fun s E hE => by
    obtain ⟨E', -, rfl⟩ := Finset.mem_map.mp hE
    exact E'.2
  have hinj : Function.Injective ρ := by
    intro E E' hEE'
    by_contra hne
    let s : Finset 𝓔 := {E, E'}
    have hcard : (s.map (Function.Embedding.subtype _)).card = 2 := by
      rw [Finset.card_map, Finset.card_pair hne]
    have hco := (hJS _ (hsub s)).2
    rw [hcard, hsupJ] at hco
    have hsup : (s.sup fun E => (ρ E).idealSheaf) = (ρ E).idealSheaf := by
      simp only [s, Finset.sup_insert, Finset.sup_singleton, hEE', sup_idem]
    rw [hsup] at hco
    have hmem : (ρ E).genericPoint ∈ (ρ E).idealSheaf.support := by
      change (ρ E).genericPoint ∈ (ρ E).support
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    have := hco _ hmem
    rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at this
    exact absurd this (by norm_num)
  refine ⟨ρ, hρ, hinj, isSNC_of_interIdeal _ hsm _ fun J' hJ' => ?_⟩
  let s : Finset 𝓔 := Finset.univ.filter fun E => ρ E ∈ J'
  have hJ's : J' = s.image ρ := by
    ext F
    simp only [s, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hF => by
      obtain ⟨E, -, rfl⟩ := Finset.mem_image.mp (hJ' hF)
      exact ⟨E, hF, rfl⟩, fun ⟨E, hE, hEF⟩ => hEF ▸ hE⟩
  have hint : interIdeal J' = ((s.map (Function.Embedding.subtype _)).sup 𝓘).comap
      (M.fibreMap h₀ (hS₀T.trans h) t j) := by
    rw [hsupJ, interIdeal, hJ's, Finset.sup_image]
    rfl
  have hcard : J'.card = (s.map (Function.Embedding.subtype _)).card := by
    rw [Finset.card_map, hJ's, Finset.card_image_of_injective _ hinj]
  rw [hint, hcard]
  exact hJS _ (hsub s)

include hint in
/-- **Prime divisors presented as images of arrows spread to the fibres**: if the image of an
arrow `a` of the diagram over `K` is the support of a prime divisor, the image of `a` on every
integral fibre of the right dimension over every late stage is the support of a prime divisor. -/
private lemma Model.eventually_range_primeDivisor {c j₀ : J} (a : c ⟶ j₀)
    (P : AlgebraicGeometry.PrimeDivisor (X.obj j₀).left)
    (hP : P.support = Set.range (X.map a).left.base) :
    M.Eventually fun S h => ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)),
      IsIntegral ((M.stage h ⋙ Over.pullback t).obj j₀).left →
      topologicalKrullDim ((M.stage h ⋙ Over.pullback t).obj j₀).left =
        topologicalKrullDim (X.obj j₀).left →
      ∃ Ps : AlgebraicGeometry.PrimeDivisor ((M.stage h ⋙ Over.pullback t).obj j₀).left,
        Ps.support = Set.range ((M.stage h ⋙ Over.pullback t).map a).left.base := by
  obtain ⟨S₀, h₀, 𝓘, h𝓘, S₂, h₂, H⟩ := M.exists_primeDivisor hint j₀ P
  have hK₁ : M.cmp h₀ j₀ ⁻¹' (𝓘.support : Set _) = P.support := by
    change _ = SetLike.coe P.idealSheaf.support
    rw [← h𝓘, Scheme.IdealSheafData.support_comap]
    rfl
  have hK₂ : M.cmp h₀ j₀ ⁻¹' (M.rangeClosed h₀ a : Set _) = Set.range (X.map a).left.base :=
    (range_snd_of_isPullback ((M.isCartesian_cmp h₀).isPullback_map a)).symm
  obtain ⟨S₃, h₃, H₃⟩ := M.exists_preimage_subset h₀ j₀ 𝓘.support (M.rangeClosed h₀ a)
    (by rw [hK₁, hK₂, hP])
  obtain ⟨S₄, h₄, H₄⟩ := M.exists_preimage_subset h₀ j₀ (M.rangeClosed h₀ a) 𝓘.support
    (by rw [hK₁, hK₂, hP])
  let T : CoefficientModels.FGSub k₀ K := ⟨S₂.1 ⊔ S₃.1 ⊔ S₄.1, (S₂.2.sup S₃.2).sup S₄.2⟩
  have hT₂ : S₂ ≤ T := (le_sup_left (a := S₂.1)).trans (le_sup_left (a := S₂.1 ⊔ S₃.1))
  have hT₃ : S₃ ≤ T := (le_sup_right (b := S₃.1)).trans (le_sup_left (a := S₂.1 ⊔ S₃.1))
  have hT₄ : S₄ ≤ T := le_sup_right (b := S₄.1)
  refine ⟨T, h₀.trans (h₂.trans hT₂), fun S hS L _ t hI hD => ?_⟩
  obtain ⟨Ps, hPs⟩ := H S (hT₂.trans hS) L t hI hD
  refine ⟨Ps, ?_⟩
  have e₃ := H₃ S (hT₃.trans hS) L t
  have e₄ := H₄ S (hT₄.trans hS) L t
  have hfm : Ps.support = M.fibreMap h₀ (h₂.trans (hT₂.trans hS)) t j₀ ⁻¹' (𝓘.support : Set _) := by
    change SetLike.coe Ps.idealSheaf.support = _
    rw [hPs, Scheme.IdealSheafData.support_comap]
    rfl
  rw [hfm, (range_snd_of_isPullback
    ((M.isCartesian_fibre h₀ (h₂.trans (hT₂.trans hS)) t).isPullback_map a))]
  exact Set.Subset.antisymm e₃ e₄

include hint in
/-- **Integrality, dimension and normality of the fibres.** -/
private lemma eventually_fibreVert : M.Eventually fun S h =>
    ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)),
      FibreVert X (M.stage h ⋙ Over.pullback t) := by
  have : Fintype J := FinCategory.fintypeObj
  exact (Model.Eventually.forall fun j => M.eventually_geometric hint j).mono
    fun S h H L _ t j => ⟨pullback_of_geometrically (H j).1 L t,
      pullback_of_geometrically (H j).2.1 L t,
      fun hn => pullback_of_geometrically ((H j).2.2 hn) L t⟩

/-- **The fibres of the model are proper.** -/
private lemma Model.isProper_fibre (S : CoefficientModels.FGSub k₀ K) (h : M.R ≤ S) (L : Type u)
    [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)) (j' : J) :
    IsProper ((M.stage h ⋙ Over.pullback t).obj j').hom := by
  have : IsProper (M.Y.obj j').hom := isProper_of_isProjectiveMorphism _ (M.hproj j')
  have h1 : IsProper ((M.stage h).obj j').hom :=
    MorphismProperty.of_isPullback (P := @IsProper) (IsPullback.of_hasPullback _ _) this
  exact MorphismProperty.of_isPullback (P := @IsProper) (IsPullback.of_hasPullback _ _) h1

/-- **The integral fibres of the model are varieties.** -/
private lemma Model.isVariety_fibre (S : CoefficientModels.FGSub k₀ K) (h : M.R ≤ S) (L : Type u)
    [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)) (j' : J)
    (hI : IsIntegral ((M.stage h ⋙ Over.pullback t).obj j').left) :
    Mori.IsVariety L ((M.stage h ⋙ Over.pullback t).obj j').hom := by
  have := M.isProper_fibre S h L t j'
  exact ⟨⟩

include hint in
/-- **Birationality and smallness on the fibres.** -/
private lemma eventually_fibreMor : M.Eventually fun S h =>
    ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)),
      FibreMor X (M.stage h ⋙ Over.pullback t) := by
  have : Fintype J := FinCategory.fintypeObj
  have H : M.Eventually fun S h => ∀ a : Σ j j' : J, j ⟶ j',
      ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)),
      (IrreducibleSpace ((M.stage h ⋙ Over.pullback t).obj a.1).left →
        IrreducibleSpace ((M.stage h ⋙ Over.pullback t).obj a.2.1).left →
        Mori.IsBirationalMorphism (X.map a.2.2).left →
        Mori.IsBirationalMorphism ((M.stage h ⋙ Over.pullback t).map a.2.2).left) ∧
      (2 ≤ Mori.closedsCodimension (Mori.exceptionalSet (X.map a.2.2).left) →
        IsIntegral ((M.stage h ⋙ Over.pullback t).obj a.1).left →
        topologicalKrullDim ((M.stage h ⋙ Over.pullback t).obj a.1).left =
          topologicalKrullDim (X.obj a.1).left →
        2 ≤ Mori.closedsCodimension
          (Mori.exceptionalSet ((M.stage h ⋙ Over.pullback t).map a.2.2).left)) := by
    refine Model.Eventually.forall fun ⟨j, j', g⟩ => ?_
    have hb : M.Eventually fun S h => ∀ (L : Type u) [Field L]
        (t : Spec (.of L) ⟶ Spec (.of S.1)),
        IrreducibleSpace ((M.stage h ⋙ Over.pullback t).obj j).left →
        IrreducibleSpace ((M.stage h ⋙ Over.pullback t).obj j').left →
        Mori.IsBirationalMorphism (X.map g).left →
        Mori.IsBirationalMorphism ((M.stage h ⋙ Over.pullback t).map g).left := by
      by_cases hg : Mori.IsBirationalMorphism (X.map g).left
      · exact (M.eventually_birational hint g hg).mono fun S h H L _ t hi hi' _ => H L t hi hi'
      · exact M.eventually_true.mono fun _ _ _ _ _ _ _ _ hg' => absurd hg' hg
    have hc : M.Eventually fun S h => ∀ (L : Type u) [Field L]
        (t : Spec (.of L) ⟶ Spec (.of S.1)),
        2 ≤ Mori.closedsCodimension (Mori.exceptionalSet (X.map g).left) →
        IsIntegral ((M.stage h ⋙ Over.pullback t).obj j).left →
        topologicalKrullDim ((M.stage h ⋙ Over.pullback t).obj j).left =
          topologicalKrullDim (X.obj j).left →
        2 ≤ Mori.closedsCodimension
          (Mori.exceptionalSet ((M.stage h ⋙ Over.pullback t).map g).left) := by
      by_cases hg : 2 ≤ Mori.closedsCodimension (Mori.exceptionalSet (X.map g).left)
      · exact (M.eventually_two_le_codimension hint g hg).mono
          fun S h H L _ t _ hi hd => H L t hi hd
      · exact M.eventually_true.mono fun _ _ _ _ _ _ hg' => absurd hg' hg
    exact (hb.and hc).mono fun S h H L _ t => ⟨H.1 L t, H.2 L t⟩
  refine (H.and (eventually_fibreVert hint M)).mono fun S h HH L _ t j j' g => ?_
  obtain ⟨H, HV⟩ := HH
  have hV := HV L t
  have hirr : ∀ j, IrreducibleSpace ((M.stage h ⋙ Over.pullback t).obj j).left := fun j =>
    have := (hV j).1
    inferInstance
  have hvar : ∀ j, IsVariety L ((M.stage h ⋙ Over.pullback t).obj j).hom := fun j =>
    M.isVariety_fibre S h L t j (hV j).1
  have hb := fun hg => (H ⟨j, j', g⟩ L t).1 (hirr j) (hirr j') hg
  refine ⟨hb, fun hs => ⟨⟨hvar j, (hV j).2.2 hs.isNormalVariety_source.2⟩,
    ⟨hvar j', (hV j').2.2 hs.isNormalVariety_target.2⟩, Over.w _, ?_,
    hb hs.isBirationalMorphism,
    (H ⟨j, j', g⟩ L t).2 hs.two_le_codimension (hV j).1 (hV j).2.1⟩⟩
  have := M.isProper_fibre S h L t j
  have := M.isProper_fibre S h L t j'
  have : IsProper (((M.stage h ⋙ Over.pullback t).map g).left ≫
      ((M.stage h ⋙ Over.pullback t).obj j').hom) := by rw [Over.w]; infer_instance
  exact IsProper.of_comp _ ((M.stage h ⋙ Over.pullback t).obj j').hom

include hint in
/-- **Log resolutions spread to the fibres**: a projective log resolution of a vertex over `K`
along a union of images of arrows is a projective log resolution on every late fibre along the
union of the images of the same arrows. -/
private lemma Model.eventually_logResolutionAlong {j₀ j : J} (μ : j ⟶ j₀)
    (σ : Finset (Σ c : J, c ⟶ j₀)) : M.Eventually fun S h =>
    ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)),
      FibreVert X (M.stage h ⋙ Over.pullback t) → FibreMor X (M.stage h ⋙ Over.pullback t) →
      IsNormal (X.obj j₀).left →
      ∀ (C : TopologicalSpace.Closeds (X.obj j₀).left)
        (Cs : TopologicalSpace.Closeds ((M.stage h ⋙ Over.pullback t).obj j₀).left),
      (C : Set (X.obj j₀).left) = ⋃ a ∈ σ, Set.range (X.map a.2).left.base →
      (Cs : Set ((M.stage h ⋙ Over.pullback t).obj j₀).left) =
        ⋃ a ∈ σ, Set.range ((M.stage h ⋙ Over.pullback t).map a.2).left.base →
      IsLogResolutionAlong (X.obj j₀).hom C (X.map μ).left →
      IsLogResolutionAlong ((M.stage h ⋙ Over.pullback t).obj j₀).hom Cs
        ((M.stage h ⋙ Over.pullback t).map μ).left := by
  classical
  have := hint j
  have := hint j₀
  have : CharZero K := charZero_of_injective_ringHom (algebraMap k₀ K).injective
  have : PerfectField K := PerfectField.ofCharZero
  have hPobj : ∀ i, IsProper (X.obj i).hom := fun i =>
    MorphismProperty.of_isPullback (P := @IsProper) (M.cart.isPullback i)
      (isProper_of_isProjectiveMorphism _ (M.hproj i))
  have hPmap : ∀ {a b : J} (g : a ⟶ b), IsProper (X.map g).left := fun {a b} g => by
    have := hPobj a
    have := hPobj b
    have : IsProper ((X.map g).left ≫ (X.obj b).hom) := by rw [Over.w]; infer_instance
    exact IsProper.of_comp _ (X.obj b).hom
  have hlftK : ∀ i, LocallyOfFiniteType (X.obj i).hom := M.locallyOfFiniteType_obj
  let C₀ : TopologicalSpace.Closeds (X.obj j₀).left := σ.sup fun a =>
    ⟨Set.range (X.map a.2).left.base,
      have := hPmap a.2
      (X.map a.2).left.isClosedMap.isClosed_range⟩
  have hC₀ : (C₀ : Set (X.obj j₀).left) = ⋃ a ∈ σ, Set.range (X.map a.2).left.base := by
    simp only [C₀, TopologicalSpace.Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion]
    rfl
  by_cases hN : IsNormal (X.obj j₀).left
  swap
  · exact M.eventually_true.mono fun S h _ L _ t _ _ hN' => absurd hN' hN
  by_cases hLR : IsLogResolutionAlong (X.obj j₀).hom C₀ (X.map μ).left
  swap
  · refine M.eventually_true.mono fun S h _ L _ t _ _ _ C Cs hC _ hLR' => absurd ?_ hLR
    rwa [show C = C₀ from TopologicalSpace.Closeds.ext (hC.trans hC₀.symm)] at hLR'
  obtain ⟨⟨_, hbir, hsmK⟩, hpure, hsncK, -⟩ := hLR
  have hw := Over.w (X.map μ)
  have := hlftK j
  have : LocallyOfFinitePresentation (X.obj j).hom :=
    instLocallyOfFinitePresentationOfIsLocallyNoetherianOfLocallyOfFiniteType _
  have hsmW : Smooth (X.obj j).hom := by
    rw [← hw]
    have : LocallyOfFinitePresentation ((X.map μ).left ≫ (X.obj j₀).hom) := by
      rw [hw]; infer_instance
    exact (Mori.isSmoothScheme_iff _).mp hsmK
  -- the components of the snc divisor `Ex(μ) ∪ μ⁻¹(C₀)` over `K`
  obtain ⟨𝓔, h𝓔cov, h𝓔snc⟩ : ∃ 𝓔 : Finset (Mori.PrimeDivisor (X.obj j).left),
      (⋃ E ∈ 𝓔, E.support) = ((Mori.exceptionalSet (X.map μ).left ⊔
        C₀.preimage (X.map μ).left.continuous : TopologicalSpace.Closeds _) : Set _) ∧
      Mori.DivisorWithCoeffs.IsSNC (X.obj j).hom (∑ E ∈ 𝓔, Finsupp.single E (1 : ℤ)) := by
    rcases hsncK with hbot | ⟨𝓔, h1, h2⟩
    · refine ⟨∅, by rw [hbot]; simp, isSNC_of_interIdeal _ hsmW ∅ fun J hJ => ?_⟩
      obtain rfl := Finset.subset_empty.mp hJ
      refine ⟨?_, fun x _ => by simp⟩
      have : (interIdeal (∅ : Finset (Mori.PrimeDivisor (X.obj j).left))) = ⊥ := Finset.sup_empty
      rw [this, isSmoothScheme_subscheme_iff]
      intro x _
      rw [stalk_bot]
      have := (MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk _).mp hsmW x
      exact IsRegularLocalRing.of_ringEquiv (RingEquiv.quotientBot _).symm
    · exact ⟨𝓔, h1, hw ▸ h2⟩
  -- consequences over `K`
  have hcovK : (Mori.exceptionalSet (X.map μ).left : Set (X.obj j).left) ∪
      (X.map μ).left.base ⁻¹' C₀ = ⋃ E ∈ 𝓔, E.support := by rw [h𝓔cov]; rfl
  have hdich : ∀ E ∈ 𝓔, E.support ⊆ (Mori.exceptionalSet (X.map μ).left : Set _) ∨
      E.support ⊆ (X.map μ).left.base ⁻¹' C₀ := fun E hE => by
    rw [← coe_primeIrreducibleCloseds]
    refine subset_or_subset_of_isIrreducible (primeIrreducibleCloseds E).isIrreducible
      (Mori.exceptionalSet (X.map μ).left).isClosed (C₀.isClosed.preimage (X.map μ).left.continuous)
      ?_
    rw [hcovK, coe_primeIrreducibleCloseds]
    exact Set.subset_biUnion_of_mem (u := fun E => E.support) hE
  let 𝓔ex := 𝓔.filter fun E => E.support ⊆ (Mori.exceptionalSet (X.map μ).left : Set _)
  have hexK : (Mori.exceptionalSet (X.map μ).left : Set (X.obj j).left) ⊆
      ⋃ E ∈ 𝓔ex, E.support :=
    subset_biUnion_of_isPureCodimOne hpure 𝓔 (by rw [← hcovK]; exact Set.subset_union_left)
  -- the models at a common stage
  obtain ⟨S₁, h₁, 𝓘, h𝓘, S₁', h₁', H₁⟩ := M.exists_isSNC hint j 𝓔 h𝓔snc
  obtain ⟨S₂, h₂, D, hD, S₂', h₂', H₂⟩ := M.exists_exceptionalSet_subset hint μ
  let T₀ : CoefficientModels.FGSub k₀ K := ⟨S₁.1 ⊔ S₂.1, S₁.2.sup S₂.2⟩
  have hT₁ : S₁ ≤ T₀ := le_sup_left (a := S₁.1)
  have hT₂ : S₂ ≤ T₀ := le_sup_right (b := S₂.1)
  have hR₀ : M.R ≤ T₀ := h₁.trans hT₁
  let 𝓘' : Mori.PrimeDivisor (X.obj j).left → ((M.stage hR₀).obj j).left.IdealSheafData :=
    fun E => (𝓘 E).comap (M.stageCmp h₁ hT₁ j)
  let D' : TopologicalSpace.Closeds ((M.stage hR₀).obj j).left :=
    D.preimage (M.stageCmp h₂ hT₂ j).continuous
  let C₀' : TopologicalSpace.Closeds ((M.stage hR₀).obj j₀).left :=
    σ.sup fun a => M.rangeClosed hR₀ a.2
  let C₀'' : TopologicalSpace.Closeds ((M.stage hR₀).obj j).left :=
    C₀'.preimage ((M.stage hR₀).map μ).left.continuous
  have h𝓘'supp : ∀ E, ((𝓘' E).support : Set _) = M.stageCmp h₁ hT₁ j ⁻¹' ((𝓘 E).support : Set _) :=
    fun E => by rw [Scheme.IdealSheafData.support_comap]; rfl
  have h𝓘' : ∀ E ∈ 𝓔, M.cmp hR₀ j ⁻¹' ((𝓘' E).support : Set _) = E.support := fun E hE => by
    change _ = SetLike.coe E.idealSheaf.support
    rw [h𝓘'supp, ← h𝓘 E hE, Scheme.IdealSheafData.support_comap]
    ext x
    simp only [Set.mem_preimage]
    rw [← Scheme.Hom.comp_apply, M.cmp_stageCmp]
    exact Iff.rfl
  have hD' : M.cmp hR₀ j ⁻¹' (D' : Set _) =
      (Mori.exceptionalSet (X.map μ).left : Set (X.obj j).left) := by
    rw [← hD, ← M.cmp_stageCmp h₂ hT₂ j]
    rfl
  have hC₀' : M.cmp hR₀ j₀ ⁻¹' (C₀' : Set _) = C₀ := by
    rw [hC₀]
    simp only [C₀', TopologicalSpace.Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion,
      Set.preimage_iUnion]
    refine Set.iUnion₂_congr fun a _ => ?_
    exact (range_snd_of_isPullback ((M.isCartesian_cmp hR₀).isPullback_map a.2)).symm
  have hC₀'' : M.cmp hR₀ j ⁻¹' (C₀'' : Set _) = (X.map μ).left.base ⁻¹' C₀ := by
    rw [← hC₀']
    change (M.cmp hR₀ j ≫ ((M.stage hR₀).map μ).left).base ⁻¹' _ = _
    rw [← (M.isCartesian_cmp hR₀).w μ]
    rfl
  -- inclusions over `K`, spread to the fibres
  obtain ⟨S₃, h₃, H₃⟩ := M.exists_preimage_subset hR₀ j D' (𝓔ex.sup fun E => (𝓘' E).support) (by
    rw [hD', preimage_coe_finset_sup]
    intro x hx
    obtain ⟨E, hE, hxE⟩ := Set.mem_iUnion₂.mp (hexK hx)
    exact Set.mem_iUnion₂.mpr ⟨E, hE, by rwa [h𝓘' E (Finset.mem_filter.mp hE).1]⟩)
  obtain ⟨S₄, h₄, H₄⟩ := M.exists_preimage_subset hR₀ j (D' ⊔ C₀'')
    (𝓔.sup fun E => (𝓘' E).support) (by
      rw [preimage_coe_finset_sup, TopologicalSpace.Closeds.coe_sup, Set.preimage_union, hD',
        hC₀'', hcovK]
      intro x hx
      obtain ⟨E, hE, hxE⟩ := Set.mem_iUnion₂.mp hx
      exact Set.mem_iUnion₂.mpr ⟨E, hE, by rwa [h𝓘' E hE]⟩)
  have hD3 : ∀ E, ∃ (S₆ : CoefficientModels.FGSub k₀ K) (h₆ : T₀ ≤ S₆), E ∈ 𝓔 →
      E.support ⊆ (X.map μ).left.base ⁻¹' C₀ → ∀ (S : CoefficientModels.FGSub k₀ K)
        (h : S₆ ≤ S) (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)),
        M.fibreMap hR₀ (h₆.trans h) t j ⁻¹' ((𝓘' E).support : Set _) ⊆
          M.fibreMap hR₀ (h₆.trans h) t j ⁻¹' (C₀'' : Set _) := by
    intro E
    by_cases hE : E ∈ 𝓔 ∧ E.support ⊆ (X.map μ).left.base ⁻¹' C₀
    · obtain ⟨S₆, h₆, H₆⟩ := M.exists_preimage_subset hR₀ j (𝓘' E).support C₀'' (by
        rw [h𝓘' E hE.1, hC₀'']; exact hE.2)
      exact ⟨S₆, h₆, fun _ _ => H₆⟩
    · exact ⟨T₀, le_rfl, fun h1 h2 => absurd ⟨h1, h2⟩ hE⟩
  choose S₆ h₆ H₆ using hD3
  have hE5 : ∀ E, ∃ (S₇ : CoefficientModels.FGSub k₀ K) (h₇ : T₀ ≤ S₇), E ∈ 𝓔ex →
      ∀ (S : CoefficientModels.FGSub k₀ K) (h : S₇ ≤ S) (L : Type u) [Field L]
        (t : Spec (.of L) ⟶ Spec (.of S.1)),
        IsIntegral ((M.stage (hR₀.trans (h₇.trans h)) ⋙ Over.pullback t).obj j₀).left →
        topologicalKrullDim ((M.stage (hR₀.trans (h₇.trans h)) ⋙ Over.pullback t).obj j₀).left =
          topologicalKrullDim (X.obj j₀).left →
        ∀ Ps : Mori.PrimeDivisor ((M.stage (hR₀.trans (h₇.trans h)) ⋙ Over.pullback t).obj j).left,
          Ps.idealSheaf = (𝓘' E).comap (M.fibreMap hR₀ (h₇.trans h) t j) →
          Ps.support ⊆ Mori.exceptionalSet
            ((M.stage (hR₀.trans (h₇.trans h)) ⋙ Over.pullback t).map μ).left := by
    intro E
    by_cases hE : E ∈ 𝓔ex
    · obtain ⟨S₇, h₇, H₇⟩ := M.exists_subset_exceptionalSet hint μ hbir hR₀ (𝓘' E) (by
        rw [Scheme.IdealSheafData.support_comap]
        change M.cmp hR₀ j ⁻¹' ((𝓘' E).support : Set _) ⊆ _
        rw [h𝓘' E (Finset.mem_filter.mp hE).1]
        exact (Finset.mem_filter.mp hE).2)
      exact ⟨S₇, h₇, fun _ => H₇⟩
    · exact ⟨T₀, le_rfl, fun h1 => absurd h1 hE⟩
  choose S₇ h₇ H₇ using hE5
  obtain ⟨S₅, h₅, H₅⟩ := eventually_smooth M
  obtain ⟨T, hT⟩ := Finset.exists_le ((insert S₁' (insert S₂' (insert S₃ (insert S₄
    (insert S₅ (insert T₀ (𝓔.image S₆ ∪ 𝓔.image S₇))))))))
  have hT₀T : T₀ ≤ T := hT T₀ (by simp)
  have hS₁'T : S₁' ≤ T := hT S₁' (by simp)
  have hS₂'T : S₂' ≤ T := hT S₂' (by simp)
  have hS₃T : S₃ ≤ T := hT S₃ (by simp)
  have hS₄T : S₄ ≤ T := hT S₄ (by simp)
  have hS₅T : S₅ ≤ T := hT S₅ (by simp)
  have hS₆T : ∀ E ∈ 𝓔, S₆ E ≤ T := fun E hE => hT _ (by
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, hE, rfl⟩)))))))
  have hS₇T : ∀ E ∈ 𝓔, S₇ E ≤ T := fun E hE => hT _ (by
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨E, hE, rfl⟩)))))))
  refine ⟨T, hR₀.trans hT₀T, fun S hS L _ t hV hM _ C Cs hC hCs _ => ?_⟩
  have hT₀S : T₀ ≤ S := hT₀T.trans hS
  let fm := M.fibreMap hR₀ hT₀S t j
  let fm₀ := M.fibreMap hR₀ hT₀S t j₀
  let Zs := M.stage (hR₀.trans hT₀S) ⋙ Over.pullback t
  let μs := (Zs.map μ).left
  haveI := (hV j).1
  haveI := (hV j₀).1
  -- smoothness, properness and projectivity of the fibre of `μ`
  have hsmS : Smooth ((M.stage (hR₀.trans hT₀S)).obj j).hom :=
    H₅ S (hS₅T.trans hS) j hsmW
  have hsmF : Smooth (Zs.obj j).hom :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ t) hsmS
  have hprμ : IsProper μs := by
    have := M.isProper_stage_map (hR₀.trans hT₀S) μ
    exact MorphismProperty.of_isPullback (P := @IsProper)
      ((isCartesian_pullback t (M.stage (hR₀.trans hT₀S))).isPullback_map μ)
      inferInstance
  have hprojμ : IsProjectiveMorphism μs := by
    have hP : ∀ i, IsProjectiveMorphism (Zs.obj i).hom := fun i =>
      IsProjectiveMorphism.baseChange (IsProjectiveMorphism.baseChange (M.hproj i) _) _
    have : IsSeparated (Zs.obj j₀).hom := (isProper_of_isProjectiveMorphism _ (hP j₀)).toIsSeparated
    refine IsProjectiveMorphism.of_comp μs (Zs.obj j₀).hom ?_
    rw [Over.w (Zs.map μ)]
    exact hP j
  -- the prime divisors of the fibre
  obtain ⟨ρ, hρ, hρinj, hρsnc⟩ := H₁ S (hS₁'T.trans hS) L t (hV j).1 (hV j).2.1 hsmF
  have hρsupp : ∀ E : 𝓔, (ρ E).support = fm ⁻¹' ((𝓘' E.1).support : Set _) := fun E => by
    change SetLike.coe (ρ E).idealSheaf.support = _
    rw [hρ, ← M.fibreMap_comp h₁ hT₁ hT₀S t j, Scheme.IdealSheafData.comap_comp,
      Scheme.IdealSheafData.support_comap]
    rfl
  -- the fibre of the boundary
  have hCs' : (Cs : Set (Zs.obj j₀).left) = fm₀ ⁻¹' (C₀' : Set _) := by
    rw [hCs, preimage_coe_finset_sup]
    refine Set.iUnion₂_congr fun a _ => ?_
    exact range_snd_of_isPullback ((M.isCartesian_fibre hR₀ hT₀S t).isPullback_map a.2)
  have hμCs : μs.base ⁻¹' (Cs : Set _) = fm ⁻¹' (C₀'' : Set _) := by
    rw [hCs']
    change (μs ≫ fm₀).base ⁻¹' _ = (fm ≫ ((M.stage hR₀).map μ).left).base ⁻¹' _
    rw [(M.isCartesian_fibre hR₀ hT₀S t).w μ]
    rfl
  -- the exceptional set of the fibre of `μ`
  have hExD : (Mori.exceptionalSet μs : Set (Zs.obj j).left) ⊆ fm ⁻¹' (D' : Set _) := by
    have := H₂ S (hS₂'T.trans hS) L t
    rw [← M.fibreMap_comp h₂ hT₂ hT₀S t j] at this
    exact this
  have hex : (Mori.exceptionalSet μs : Set (Zs.obj j).left) =
      ⋃ F ∈ (Finset.univ.filter fun E : 𝓔 => E.1 ∈ 𝓔ex).image ρ, F.support := by
    apply le_antisymm
    · intro x hx
      have hx' := H₃ S (hS₃T.trans hS) L t (hExD hx)
      rw [preimage_coe_finset_sup] at hx'
      obtain ⟨E, hE, hxE⟩ := Set.mem_iUnion₂.mp hx'
      refine Set.mem_iUnion₂.mpr ⟨ρ ⟨E, (Finset.mem_filter.mp hE).1⟩, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨⟨E, (Finset.mem_filter.mp hE).1⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hE⟩, rfl⟩
      · rwa [hρsupp]
    · refine Set.iUnion₂_subset fun F hF => ?_
      obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hF
      have hEex := (Finset.mem_filter.mp hE).2
      exact H₇ E.1 hEex S (hS₇T E.1 E.2 |>.trans hS) L t (hV j₀).1 (hV j₀).2.1 (ρ E)
        ((hρ E).trans (by
          rw [← M.fibreMap_comp h₁ hT₁ hT₀S t j, Scheme.IdealSheafData.comap_comp]))
  have hcov : (Mori.exceptionalSet μs : Set (Zs.obj j).left) ∪ μs.base ⁻¹' Cs =
      ⋃ F ∈ Finset.univ.image ρ, F.support := by
    apply le_antisymm
    · intro x hx
      have hx' : x ∈ fm ⁻¹' ((D' ⊔ C₀'' : TopologicalSpace.Closeds _) : Set _) := by
        rcases hx with hx | hx
        · exact Or.inl (hExD hx)
        · rw [hμCs] at hx
          exact Or.inr hx
      have hx'' := H₄ S (hS₄T.trans hS) L t hx'
      rw [preimage_coe_finset_sup] at hx''
      obtain ⟨E, hE, hxE⟩ := Set.mem_iUnion₂.mp hx''
      exact Set.mem_iUnion₂.mpr ⟨ρ ⟨E, hE⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _),
        by rwa [hρsupp]⟩
    · refine Set.iUnion₂_subset fun F hF => ?_
      obtain ⟨E, -, rfl⟩ := Finset.mem_image.mp hF
      rcases hdich E.1 E.2 with hEx | hEC
      · refine (H₇ E.1 (Finset.mem_filter.mpr ⟨E.2, hEx⟩) S (hS₇T E.1 E.2 |>.trans hS) L t
          (hV j₀).1 (hV j₀).2.1 (ρ E) ((hρ E).trans (by
            rw [← M.fibreMap_comp h₁ hT₁ hT₀S t j,
              Scheme.IdealSheafData.comap_comp]))).trans Set.subset_union_left
      · intro x hx
        right
        rw [hμCs]
        rw [hρsupp] at hx
        exact H₆ E.1 E.2 hEC S (hS₆T E.1 E.2 |>.trans hS) L t hx
  have hsnc' : Mori.DivisorWithCoeffs.IsSNC (μs ≫ (Zs.obj j₀).hom)
      (∑ F ∈ Finset.univ.image ρ, Finsupp.single F (1 : ℤ)) := by
    rw [Over.w (Zs.map μ)]
    exact hρsnc
  have hsm' : Smooth (μs ≫ (Zs.obj j₀).hom) := by
    rw [Over.w (Zs.map μ)]
    exact hsmF
  exact isLogResolutionAlong_of_cover _ Cs μs ((hM μ).1 hbir) hsm' hprojμ _ _ hex hcov hsnc'

include hint in
/-- **Models of finitely many prime divisors above a given stage.** -/
private lemma Model.exists_models {S₀ : CoefficientModels.FGSub k₀ K} (h₀ : M.R ≤ S₀) (j : J)
    (T : Finset (Mori.PrimeDivisor (X.obj j).left)) :
    ∃ (S₁ : CoefficientModels.FGSub k₀ K) (h₁ : S₀ ≤ S₁)
      (𝓘 : Mori.PrimeDivisor (X.obj j).left →
        ((M.stage (h₀.trans h₁)).obj j).left.IdealSheafData),
      (∀ E ∈ T, (𝓘 E).comap (M.cmp (h₀.trans h₁) j) = E.idealSheaf) ∧
      EvAbove S₁ fun S hS => ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)),
        IsIntegral ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).obj j).left →
        topologicalKrullDim ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).obj j).left =
          topologicalKrullDim (X.obj j).left →
        ∀ E ∈ T, ∃ Ps : Mori.PrimeDivisor
            ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).obj j).left,
          Ps.idealSheaf = (𝓘 E).comap (M.fibreMap (h₀.trans h₁) hS t j) := by
  obtain ⟨S₀', h₀', 𝓘', h𝓘', H'⟩ := M.exists_primeDivisor_family hint j T
  obtain ⟨S₁, h₀₁, h₀'₁⟩ := exists_ge_ge S₀ S₀'
  refine ⟨S₁, h₀₁, fun E => (𝓘' E).comap (M.stageCmp h₀' h₀'₁ j), fun E hE => ?_,
    ⟨S₁, le_rfl, fun S hS L _ t hI hd E hE => ?_⟩⟩
  · rw [← Scheme.IdealSheafData.comap_comp, M.cmp_stageCmp]
    exact h𝓘' E hE
  · obtain ⟨Ps, hPs⟩ := H' S (h₀'₁.trans hS) L t hI hd E hE
    refine ⟨Ps, ?_⟩
    rw [← Scheme.IdealSheafData.comap_comp, M.fibreMap_comp]
    exact hPs

include hint in
/-- **Crepant boundaries spread to the fibres.** -/
private lemma Model.eventually_crepantBoundary {j₀ j : J} (μ : j ⟶ j₀) : M.Eventually fun S h =>
    ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)),
      FibreVert X (M.stage h ⋙ Over.pullback t) → FibreMor X (M.stage h ⋙ Over.pullback t) →
      ∀ [IsLocallyNoetherian (X.obj j₀).left] [IsNormal (X.obj j₀).left] (n : ℕ)
        {m : ℕ} {c : Fin m → J} (ι : ∀ l, c l ⟶ j₀)
        (P : Fin m → Mori.PrimeDivisor (X.obj j₀).left) (q : Fin m → ℚ)
        {m' : ℕ} {c' : Fin m' → J} (ι' : ∀ l, c' l ⟶ j)
        (P' : Fin m' → Mori.PrimeDivisor (X.obj j).left) (q' : Fin m' → ℚ),
        haveI := hint j₀
        (∀ l, (P l).support = Set.range (X.map (ι l)).left.base) →
        (∀ l, (P' l).support = Set.range (X.map (ι' l)).left.base) →
        Fourfold.IsLogResolution (X.obj j₀).hom (∑ l, Finsupp.single (P l) (q l)) (X.map μ).left →
        (∃ (K₀ : Mori.Divisor (X.obj j₀).left) (hW : _) (hμ : _),
          Mori.IsCrepantBoundary (X.obj j₀).hom n K₀ (∑ l, Finsupp.single (P l) (q l))
            (X.map μ).left hW hμ (∑ l, Finsupp.single (P' l) (q' l))) →
        ∀ [IsIntegral ((M.stage h ⋙ Over.pullback t).obj j₀).left]
          [IsLocallyNoetherian ((M.stage h ⋙ Over.pullback t).obj j₀).left]
          [IsNormal ((M.stage h ⋙ Over.pullback t).obj j₀).left]
          (Ps : Fin m → Mori.PrimeDivisor ((M.stage h ⋙ Over.pullback t).obj j₀).left)
          (Ps' : Fin m' → Mori.PrimeDivisor ((M.stage h ⋙ Over.pullback t).obj j).left),
          (∀ l, (Ps l).support = Set.range ((M.stage h ⋙ Over.pullback t).map (ι l)).left.base) →
          (∀ l, (Ps' l).support =
            Set.range ((M.stage h ⋙ Over.pullback t).map (ι' l)).left.base) →
          Fourfold.IsLogResolution ((M.stage h ⋙ Over.pullback t).obj j₀).hom
            (∑ l, Finsupp.single (Ps l) (q l)) ((M.stage h ⋙ Over.pullback t).map μ).left →
          ∃ (Ks : Mori.Divisor ((M.stage h ⋙ Over.pullback t).obj j₀).left) (hW : _) (hμ : _),
            Mori.IsCrepantBoundary ((M.stage h ⋙ Over.pullback t).obj j₀).hom n Ks
              (∑ l, Finsupp.single (Ps l) (q l)) ((M.stage h ⋙ Over.pullback t).map μ).left hW hμ
              (∑ l, Finsupp.single (Ps' l) (q' l)) := by
  classical
  have := hint j₀
  have := hint j
  by_cases hgood : Nonempty (Mori.PrimeDivisor (X.obj j).left) ∧ IsLocallyNoetherian
      (X.obj j₀).left ∧
      IsNormal (X.obj j₀).left ∧ Mori.IsNormalVariety K (X.obj j₀).hom ∧
      Mori.IsNormalVariety K ((X.map μ).left ≫ (X.obj j₀).hom) ∧
      Mori.IsBirationalMorphism (X.map μ).left
  swap
  · obtain ⟨dW, hdW⟩ := Model.exists_topologicalKrullDim_eq hint M j
    refine ⟨M.R, le_rfl, fun S h => ?_⟩
    intro L _ t hV hM _ _ n m c ι P q m' c' ι' P' q' hP hP' hLR hCr _ _ _ Ps Ps' hPs hPs' hLRs
    obtain ⟨K₀, hW, hμ', hCr⟩ := hCr
    have := (hV j).1
    have hempty : IsEmpty (Mori.PrimeDivisor (X.obj j).left) := by
      rw [← not_nonempty_iff]
      intro hne
      exact hgood ⟨hne, inferInstance, inferInstance, (hCr hne.some).1, hW, hμ'⟩
    have hWs : Mori.IsNormalVariety L (((M.stage (le_rfl.trans h) ⋙ Over.pullback t).map μ).left ≫
        ((M.stage (le_rfl.trans h) ⋙ Over.pullback t).obj j₀).hom) := by
      rw [Over.w]
      exact ⟨M.isVariety_fibre S _ L t j (hV j).1, (hV j).2.2 hW.2⟩
    refine ⟨0, hWs, (hM μ).1 hμ', fun F => ?_⟩
    exfalso
    have hd0 : dW = 0 := by
      by_contra h0
      exact hempty.false (MMP.Positivity.nonempty_primeDivisor_of_topologicalKrullDim_eq hdW
          h0).some
    have hne : genericPoint ((M.stage (le_rfl.trans h) ⋙ Over.pullback t).obj j).left ≠
        F.genericPoint := fun e => by
      have := F.coheight_genericPoint
      rw [← e, Stacks.EtaleCohomology.coheight_genericPoint_eq_zero] at this
      exact absurd this (by decide)
    have := one_le_topologicalKrullDim_of_specializes_of_ne (genericPoint_specializes _) hne
    rw [(hV j).2.1, hdW, hd0] at this
    exact absurd this (by decide)
  obtain ⟨⟨F₀⟩, hLN, hNZ, hZ, hW, hμ⟩ := hgood
  haveI := hμ.isDominant
  have hW' : Mori.IsNormalVariety K (X.obj j).hom := by rwa [← Over.w (X.map μ)]
  have : LocallyOfFiniteType (X.obj j₀).hom := hZ.1.toLocallyOfFiniteType
  have : QuasiCompact (X.obj j₀).hom := hZ.1.toQuasiCompact
  have : CompactSpace (X.obj j₀).left := QuasiCompact.compactSpace_of_compactSpace (X.obj j₀).hom
  have : LocallyOfFiniteType (X.obj j).hom := hW'.1.toLocallyOfFiniteType
  have : QuasiCompact (X.obj j).hom := hW'.1.toQuasiCompact
  have : CompactSpace (X.obj j).left := QuasiCompact.compactSpace_of_compactSpace (X.obj j).hom
  have : IsLocallyNoetherian (X.obj j).left :=
    LocallyOfFiniteType.isLocallyNoetherian (X.obj j).hom
  have : IsNormal (X.obj j).left := hW'.2
  have hbij := hμ.functionFieldMap_bijective
  obtain ⟨N, hN⟩ := Model.exists_topologicalKrullDim_eq hint M j₀
  have hNW : topologicalKrullDim (X.obj j).left = N := by
    haveI := hZ.1
    haveI := hW.1
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (X.obj j₀).hom
      ((X.map μ).left ≫ (X.obj j₀).hom) hμ, hN]
  -- étale charts and the reference form on `Z`
  obtain ⟨UZ, hUZc, hUZs, hUZ⟩ := exists_smooth_open_of_isNormalVariety (X.obj j₀).hom hZ
  obtain ⟨UW, hUWc, hUWs, hUW⟩ := exists_smooth_open_of_isNormalVariety (X.obj j).hom hW'
  obtain ⟨SZ, hSZ, BZ, _, VZ, gZ, hVZa, hgZ, hgCZ, hVZne, hVZ⟩ :=
    M.exists_charts hint (le_refl M.R) j₀ hN UZ hUZc hUZs
  have hZ₀ : M.R ≤ SZ := (le_refl M.R).trans hSZ
  obtain ⟨b₀, hb₀⟩ := hVZ (genericPoint _)
    (hUZ _ ((Stacks.EtaleCohomology.coheight_genericPoint_eq_zero _).trans_le zero_le_one))
  haveI := hVZne b₀
  have hpbZ := (M.isCartesian_cmp hZ₀).isPullback j₀
  obtain ⟨ωK, hωK⟩ : ∃ ω : Mori.RationalTopForms (X.obj j₀).hom N,
      (letI := MMP.Mori.functionFieldAlgebra (X.obj j₀).hom
      ω = exteriorPower.ιMulti (X.obj j₀).left.functionField N fun i =>
        KaehlerDifferential.D K (X.obj j₀).left.functionField
          ((X.obj j₀).left.germToFunctionField (M.cmp hZ₀ j₀ ⁻¹ᵁ VZ b₀)
            ((M.cmp hZ₀ j₀).app (VZ b₀) (gZ b₀ (MvPolynomial.X i))))) := ⟨_, rfl⟩
  have hω0' := coordForm_ne_zero_of_isPullback hpbZ (hVZa b₀) (gZ b₀) (hgZ b₀) (hgCZ b₀)
  have hω0 : ωK ≠ 0 := by rwa [hωK]
  obtain ⟨T₀Zf, HZf⟩ := M.exists_form_spreading hint hZ₀ j₀ VZ gZ hVZa hgZ hgCZ hVZne
    (fun x hx => hVZ x (hUZ x hx)) (VZ b₀) (fun i => gZ b₀ (MvPolynomial.X i)) ωK hωK hω0
  -- étale charts and the pulled-back form on `W`
  obtain ⟨SW, hSW, BW, _, VW, gW, hVWa, hgW, hgCW, hVWne, hVW⟩ :=
    M.exists_charts hint hZ₀ j hNW UW hUWc hUWs
  have hW₀ : M.R ≤ SW := hZ₀.trans hSW
  have hsqK : M.cmp hW₀ j ≫ ((M.stage hW₀).map μ).left = (X.map μ).left ≫ M.cmp hW₀ j₀ :=
    ((M.isCartesian_cmp hW₀).w μ).symm
  have ePK : M.cmp hW₀ j ⁻¹ᵁ (((M.stage hW₀).map μ).left ⁻¹ᵁ
      (M.stageCmp hZ₀ hSW j₀ ⁻¹ᵁ VZ b₀)) = (X.map μ).left ⁻¹ᵁ (M.cmp hZ₀ j₀ ⁻¹ᵁ VZ b₀) := by
    have e : M.cmp hW₀ j ≫ ((M.stage hW₀).map μ).left ≫ M.stageCmp hZ₀ hSW j₀ =
        (X.map μ).left ≫ M.cmp hZ₀ j₀ := by
      rw [← Category.assoc, hsqK, Category.assoc, M.cmp_stageCmp]
    simp only [← Scheme.Hom.comp_preimage]
    exact congrArg (· ⁻¹ᵁ VZ b₀) e
  haveI : Nonempty (M.cmp hW₀ j₀ ⁻¹ᵁ (M.stageCmp hZ₀ hSW j₀ ⁻¹ᵁ VZ b₀)) := by
    rw [← Scheme.Hom.comp_preimage, M.cmp_stageCmp]; infer_instance
  haveI : Nonempty (M.cmp hW₀ j ⁻¹ᵁ (((M.stage hW₀).map μ).left ⁻¹ᵁ
      (M.stageCmp hZ₀ hSW j₀ ⁻¹ᵁ VZ b₀))) := by
    rw [ePK]
    obtain ⟨⟨y, hy⟩⟩ := ‹Nonempty (M.cmp hZ₀ j₀ ⁻¹ᵁ VZ b₀)›
    have hd : Dense (Set.range (X.map μ).left) := (X.map μ).left.denseRange
    obtain ⟨_, hz, ⟨w, rfl⟩⟩ := hd.inter_open_nonempty _ (M.cmp hZ₀ j₀ ⁻¹ᵁ VZ b₀).isOpen ⟨y, hy⟩
    exact ⟨⟨w, hz⟩⟩
  have gWK : ∀ i, (X.obj j).left.germToFunctionField _ ((M.cmp hW₀ j).app _
      (((M.stage hW₀).map μ).left.app _ ((M.stageCmp hZ₀ hSW j₀).app (VZ b₀)
        (gZ b₀ (MvPolynomial.X i))))) =
      AlgebraicGeometry.functionFieldMap (X.map μ).left
        ((X.obj j₀).left.germToFunctionField (M.cmp hZ₀ j₀ ⁻¹ᵁ VZ b₀)
          ((M.cmp hZ₀ j₀).app (VZ b₀) (gZ b₀ (MvPolynomial.X i)))) := fun i => by
    rw [germ_app_eq_functionFieldMap _ _ _ _ hsqK _ _,
      germToFunctionField_app_app_of_comp_eq _ _ _ (M.cmp_stageCmp hZ₀ hSW j₀)]
  obtain ⟨σWK, hσWK⟩ : ∃ σ : Mori.RationalTopForms (X.obj j).hom N,
      (letI := MMP.Mori.functionFieldAlgebra (X.obj j).hom
      σ = exteriorPower.ιMulti (X.obj j).left.functionField N fun i =>
        KaehlerDifferential.D K (X.obj j).left.functionField
          ((X.obj j).left.germToFunctionField _ ((M.cmp hW₀ j).app _
            (((M.stage hW₀).map μ).left.app _ ((M.stageCmp hZ₀ hSW j₀).app (VZ b₀)
              (gZ b₀ (MvPolynomial.X i))))))) := ⟨_, rfl⟩
  have hσW0 : σWK ≠ 0 := by
    rw [hσWK]
    simp only [gWK]
    exact ιMulti_functionFieldMap_ne_zero (X.obj j₀).hom (X.map μ).left hbij hN _ hω0'
      (X.obj j).hom (Over.w (X.map μ))
  obtain ⟨T₀Wf, HWf⟩ := M.exists_form_spreading hint hW₀ j VW gW hVWa hgW hgCW hVWne
    (fun x hx => hVW x (hUW x hx)) _ (fun i => ((M.stage hW₀).map μ).left.app _
      ((M.stageCmp hZ₀ hSW j₀).app (VZ b₀) (gZ b₀ (MvPolynomial.X i)))) σWK hσWK hσW0
  -- prime divisors presented by arrows
  have : Fintype J := FinCategory.fintypeObj
  let arrZ : (Σ c : J, c ⟶ j₀) → Finset (Mori.PrimeDivisor (X.obj j₀).left) := fun a =>
    if h : ∃ P : Mori.PrimeDivisor (X.obj j₀).left, P.support = Set.range (X.map a.2).left.base
    then {h.choose} else ∅
  let arrW : (Σ c : J, c ⟶ j) → Finset (Mori.PrimeDivisor (X.obj j).left) := fun a =>
    if h : ∃ P : Mori.PrimeDivisor (X.obj j).left, P.support = Set.range (X.map a.2).left.base
    then {h.choose} else ∅
  let TarrZ := Finset.univ.biUnion arrZ
  let TarrW := Finset.univ.biUnion arrW
  have hmemZ : ∀ (a : Σ c : J, c ⟶ j₀) (P : Mori.PrimeDivisor (X.obj j₀).left),
      P.support = Set.range (X.map a.2).left.base → P ∈ TarrZ := fun a P hP => by
    refine Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, ?_⟩
    have h : ∃ P : Mori.PrimeDivisor (X.obj j₀).left, P.support = Set.range (X.map a.2).left.base :=
      ⟨P, hP⟩
    simp only [arrZ, dif_pos h, Finset.mem_singleton]
    exact AlgebraicGeometry.PrimeDivisor.eq_of_support_eq (hP.trans h.choose_spec.symm)
  have hmemW : ∀ (a : Σ c : J, c ⟶ j) (P : Mori.PrimeDivisor (X.obj j).left),
      P.support = Set.range (X.map a.2).left.base → P ∈ TarrW := fun a P hP => by
    refine Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, ?_⟩
    have h : ∃ P : Mori.PrimeDivisor (X.obj j).left, P.support = Set.range (X.map a.2).left.base :=
      ⟨P, hP⟩
    simp only [arrW, dif_pos h, Finset.mem_singleton]
    exact AlgebraicGeometry.PrimeDivisor.eq_of_support_eq (hP.trans h.choose_spec.symm)
  -- the lattice of Cartier divisors supported on the arrow primes and the divisor of `ω`
  let T₁ := TarrZ ∪ (Mori.topFormDivisor (X.obj j₀).hom ωK).support
  have hT₁ω : ∀ E, E.ordForm (ωK.toPluriForms (X.obj j₀).hom) ≠ 0 → E ∈ T₁ := fun E hE =>
    Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr (by
      change (Mori.topFormDivisor (X.obj j₀).hom ωK).coeff E ≠ 0
      rwa [Mori.coeff_topFormDivisor]))
  obtain ⟨G, hG, hGspan⟩ := exists_finset_span_cartier T₁
  choose Sg hSg T₀Zg T₀Wg Hg using fun g : G =>
    M.exists_spread_cartier hint (le_refl M.R) μ g.1 (hG g.1 g.2).1
  let TZ := T₁ ∪ T₀Zf ∪ Finset.univ.biUnion T₀Zg
  let TW := TarrW ∪ T₀Wf ∪ Finset.univ.biUnion T₀Wg
  have hT₁Z : T₁ ⊆ TZ := fun E hE => Finset.mem_union_left _ (Finset.mem_union_left _ hE)
  have hTfZ : T₀Zf ⊆ TZ := fun E hE => Finset.mem_union_left _ (Finset.mem_union_right _ hE)
  have hTgZ : ∀ g, T₀Zg g ⊆ TZ := fun g E hE =>
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ _, hE⟩)
  have hTaW : TarrW ⊆ TW := fun E hE => Finset.mem_union_left _ (Finset.mem_union_left _ hE)
  have hTfW : T₀Wf ⊆ TW := fun E hE => Finset.mem_union_left _ (Finset.mem_union_right _ hE)
  have hTgW : ∀ g, T₀Wg g ⊆ TW := fun g E hE =>
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ _, hE⟩)
  -- a common stage and models
  obtain ⟨Sp, hSp⟩ := Finset.exists_le (insert SW (Finset.univ.image Sg))
  have hSWp : SW ≤ Sp := hSp _ (Finset.mem_insert_self _ _)
  have hgp : ∀ g, Sg g ≤ Sp := fun g =>
    hSp _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  have hp₀ : M.R ≤ Sp := hW₀.trans hSWp
  obtain ⟨S1Z, h1Z, 𝓘Z, h𝓘Z, EZ⟩ := M.exists_models hint hp₀ j₀ TZ
  obtain ⟨S1W, h1W, 𝓘W, h𝓘W, EW⟩ := M.exists_models hint (hp₀.trans h1Z) j TW
  have H1 : M.R ≤ S1W := (hp₀.trans h1Z).trans h1W
  let 𝓘Z' : Mori.PrimeDivisor (X.obj j₀).left → ((M.stage H1).obj j₀).left.IdealSheafData :=
    fun E => (𝓘Z E).comap (M.stageCmp (hp₀.trans h1Z) h1W j₀)
  have h𝓘Z' : ∀ E ∈ TZ, (𝓘Z' E).comap (M.cmp H1 j₀) = E.idealSheaf := fun E hE => by
    rw [M.comap_stageCmp_comap_cmp]; exact h𝓘Z E hE
  -- all the spreading statements at the stage of the models
  have eZf := HZf TZ hTfZ S1W (((hSW.trans hSWp).trans h1Z).trans h1W) 𝓘Z' h𝓘Z'
  have eWf := HWf TW hTfW S1W (hSWp.trans (h1Z.trans h1W)) 𝓘W h𝓘W
  have eG := EvAbove.forall_of_finite fun g : G =>
    Hg g TZ (hTgZ g) TW (hTgW g) S1W ((hgp g).trans (h1Z.trans h1W)) 𝓘Z' 𝓘W h𝓘Z' h𝓘W
  have eEZ := EZ.of_le h1W
  have eArrZ : EvAbove S1W fun S hS => ∀ (a : Σ c : J, c ⟶ j₀)
      (h : ∃ P : Mori.PrimeDivisor (X.obj j₀).left, P.support = Set.range (X.map a.2).left.base)
      (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)),
      M.fibreMap H1 hS t j₀ ⁻¹' ((𝓘Z' h.choose).support : Set _) =
        Set.range ((M.stage (H1.trans hS) ⋙ Over.pullback t).map a.2).left.base := by
    refine EvAbove.forall_of_finite fun a => ?_
    by_cases h : ∃ P : Mori.PrimeDivisor (X.obj j₀).left, P.support = Set.range
        (X.map a.2).left.base
    · exact (M.evAbove_range_eq H1 a.2 (h𝓘Z' _ (hT₁Z (Finset.mem_union_left _
        (hmemZ a _ h.choose_spec)))) h.choose_spec).mono fun S hS H h' L _ t => H L t
    · exact (EvAbove.true S1W).mono fun S hS _ h' => absurd h' h
  have eArrW : EvAbove S1W fun S hS => ∀ (a : Σ c : J, c ⟶ j)
      (h : ∃ P : Mori.PrimeDivisor (X.obj j).left, P.support = Set.range (X.map a.2).left.base)
      (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)),
      M.fibreMap H1 hS t j ⁻¹' ((𝓘W h.choose).support : Set _) =
        Set.range ((M.stage (H1.trans hS) ⋙ Over.pullback t).map a.2).left.base := by
    refine EvAbove.forall_of_finite fun a => ?_
    by_cases h : ∃ P : Mori.PrimeDivisor (X.obj j).left, P.support = Set.range (X.map a.2).left.base
    · exact (M.evAbove_range_eq H1 a.2 (h𝓘W _ (hTaW (hmemW a _ h.choose_spec)))
        h.choose_spec).mono fun S hS H h' L _ t => H L t
    · exact (EvAbove.true S1W).mono fun S hS _ h' => absurd h' h
  obtain ⟨S₂, h₂, HH⟩ := (((((eZf.and eWf).and eG).and eEZ).and EW).and eArrZ).and eArrW
  refine ⟨S₂, H1.trans h₂, fun S hS => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨HZf', HWf'⟩, HG⟩, HEZ⟩, HEW⟩, HAZ⟩, HAW⟩ := HH S hS
  intro L _ t hV hM _ _ n m c ι P q m' c' ι' P' q' hP hP' hLR hCr _ _ _ Ps Ps' hPs hPs' hLRs
  haveI : PerfectField L := perfectField_of_spec_hom (k₀ := k₀) (A := S.1) t
  obtain ⟨K₀, hW'', hμ'', hCr'⟩ := hCr
  have hnN : N = n := by
    have := (hCr' F₀).2.1.topologicalKrullDim_eq
    rw [hN] at this
    exact_mod_cast this
  subst hnN
  -- the fibres
  have hIW := (hV j).1
  have hdZ := (hV j₀).2.1
  have hdW := (hV j).2.1
  have hNWs := (hV j).2.2 inferInstance
  have hvZ := M.isVariety_fibre S _ L t j₀ inferInstance
  have hvW := M.isVariety_fibre S _ L t j hIW
  have : LocallyOfFiniteType ((M.stage ((H1.trans h₂).trans hS) ⋙ Over.pullback t).obj j₀).hom :=
    hvZ.toLocallyOfFiniteType
  have : QuasiCompact ((M.stage ((H1.trans h₂).trans hS) ⋙ Over.pullback t).obj j₀).hom :=
    hvZ.toQuasiCompact
  have : CompactSpace ((M.stage ((H1.trans h₂).trans hS) ⋙ Over.pullback t).obj j₀).left :=
    QuasiCompact.compactSpace_of_compactSpace
      ((M.stage ((H1.trans h₂).trans hS) ⋙ Over.pullback t).obj j₀).hom
  have : LocallyOfFiniteType ((M.stage ((H1.trans h₂).trans hS) ⋙ Over.pullback t).obj j).hom :=
    hvW.toLocallyOfFiniteType
  have : IsLocallyNoetherian ((M.stage ((H1.trans h₂).trans hS) ⋙ Over.pullback t).obj j).left :=
    LocallyOfFiniteType.isLocallyNoetherian
      ((M.stage ((H1.trans h₂).trans hS) ⋙ Over.pullback t).obj j).hom
  have hZs : Mori.IsNormalVariety L
      ((M.stage ((H1.trans h₂).trans hS) ⋙ Over.pullback t).obj j₀).hom := ⟨hvZ, inferInstance⟩
  have hWs : Mori.IsNormalVariety L
      (((M.stage ((H1.trans h₂).trans hS) ⋙ Over.pullback t).map μ).left ≫
        ((M.stage ((H1.trans h₂).trans hS) ⋙ Over.pullback t).obj j₀).hom) := by
    rw [Over.w]; exact ⟨hvW, hNWs⟩
  have hμs : Mori.IsBirationalMorphism
      ((M.stage ((H1.trans h₂).trans hS) ⋙ Over.pullback t).map μ).left := (hM μ).1 hμ
  haveI := hμs.isDominant
  -- the models are prime divisors on the fibres
  have hmZ : ∀ E ∈ TZ, ∃ Q : Mori.PrimeDivisor
      ((M.stage ((H1.trans h₂).trans hS) ⋙ Over.pullback t).obj j₀).left,
      Q.idealSheaf = (𝓘Z' E).comap (M.fibreMap H1 (h₂.trans hS) t j₀) := fun E hE => by
    obtain ⟨Q, hQ⟩ := HEZ L t inferInstance hdZ E hE
    exact ⟨Q, hQ.trans (M.comap_stageCmp_comap_fibreMap (hp₀.trans h1Z) h1W (h₂.trans hS) t j₀
      (𝓘Z E)).symm⟩
  have hmW : ∀ E ∈ TW, ∃ Q : Mori.PrimeDivisor
      ((M.stage ((H1.trans h₂).trans hS) ⋙ Over.pullback t).obj j).left,
      Q.idealSheaf = (𝓘W E).comap (M.fibreMap H1 (h₂.trans hS) t j) := fun E hE =>
    HEW L t hIW hdW E hE
  have hZS : SZ ≤ S := hSW.trans (hSWp.trans (h1Z.trans (h1W.trans (h₂.trans hS))))
  have hWS : SW ≤ S := hSWp.trans (h1Z.trans (h1W.trans (h₂.trans hS)))
  -- the form on the fibre of `Z`
  obtain ⟨hgenO, HZf2⟩ := HZf' L t hdZ hmZ
  haveI : Nonempty (M.fibreMap hZ₀ hZS t j₀ ⁻¹ᵁ VZ b₀) := ⟨⟨_, hgenO⟩⟩
  obtain ⟨ωs, hωs⟩ : ∃ ω : Mori.RationalTopForms
      ((M.stage ((H1.trans h₂).trans hS) ⋙ Over.pullback t).obj j₀).hom N,
      (letI := MMP.Mori.functionFieldAlgebra
        ((M.stage ((H1.trans h₂).trans hS) ⋙ Over.pullback t).obj j₀).hom
      ω = exteriorPower.ιMulti
        ((M.stage ((H1.trans h₂).trans hS) ⋙ Over.pullback t).obj j₀).left.functionField N
        fun i => KaehlerDifferential.D L
          ((M.stage ((H1.trans h₂).trans hS) ⋙ Over.pullback t).obj j₀).left.functionField
          (((M.stage ((H1.trans h₂).trans hS) ⋙ Over.pullback t).obj j₀).left.germToFunctionField
            (M.fibreMap hZ₀ hZS t j₀ ⁻¹ᵁ VZ b₀)
            ((M.fibreMap hZ₀ hZS t j₀).app (VZ b₀) (gZ b₀ (MvPolynomial.X i))))) := ⟨_, rfl⟩
  obtain ⟨hωs0, hZfs⟩ := HZf2 ωs hωs
  -- the form on the fibre of `W`
  obtain ⟨hgenOW, HWf2⟩ := HWf' L t hdW hmW
  haveI : Nonempty (M.fibreMap hW₀ hWS t j ⁻¹ᵁ (((M.stage hW₀).map μ).left ⁻¹ᵁ
      (M.stageCmp hZ₀ hSW j₀ ⁻¹ᵁ VZ b₀))) := ⟨⟨_, hgenOW⟩⟩
  obtain ⟨σs, hσs⟩ : ∃ σ : Mori.RationalTopForms
      ((M.stage ((H1.trans h₂).trans hS) ⋙ Over.pullback t).obj j).hom N,
      (letI := MMP.Mori.functionFieldAlgebra
        ((M.stage ((H1.trans h₂).trans hS) ⋙ Over.pullback t).obj j).hom
      σ = exteriorPower.ιMulti
        ((M.stage ((H1.trans h₂).trans hS) ⋙ Over.pullback t).obj j).left.functionField N
        fun i => KaehlerDifferential.D L
          ((M.stage ((H1.trans h₂).trans hS) ⋙ Over.pullback t).obj j).left.functionField
          (((M.stage ((H1.trans h₂).trans hS) ⋙ Over.pullback t).obj j).left.germToFunctionField
            _ ((M.fibreMap hW₀ hWS t j).app _ (((M.stage hW₀).map μ).left.app _
              ((M.stageCmp hZ₀ hSW j₀).app (VZ b₀) (gZ b₀ (MvPolynomial.X i))))))) := ⟨_, rfl⟩
  obtain ⟨-, hWfs⟩ := HWf2 σs hσs
  have hsqF : M.fibreMap hW₀ hWS t j ≫ ((M.stage hW₀).map μ).left =
      ((M.stage (hW₀.trans hWS) ⋙ Over.pullback t).map μ).left ≫ M.fibreMap hW₀ hWS t j₀ :=
    (M.fibreMap_naturality hW₀ hWS t μ).symm
  haveI : Nonempty (M.fibreMap hW₀ hWS t j₀ ⁻¹ᵁ (M.stageCmp hZ₀ hSW j₀ ⁻¹ᵁ VZ b₀)) := by
    rw [← Scheme.Hom.comp_preimage, M.fibreMap_comp]; infer_instance
  have gWs : ∀ i, ((M.stage ((H1.trans h₂).trans hS) ⋙ Over.pullback t).obj
      j).left.germToFunctionField
      _ ((M.fibreMap hW₀ hWS t j).app _ (((M.stage hW₀).map μ).left.app _
        ((M.stageCmp hZ₀ hSW j₀).app (VZ b₀) (gZ b₀ (MvPolynomial.X i))))) =
      AlgebraicGeometry.functionFieldMap
        ((M.stage ((H1.trans h₂).trans hS) ⋙ Over.pullback t).map μ).left
        (((M.stage ((H1.trans h₂).trans hS) ⋙ Over.pullback t).obj j₀).left.germToFunctionField
          (M.fibreMap hZ₀ hZS t j₀ ⁻¹ᵁ VZ b₀)
          ((M.fibreMap hZ₀ hZS t j₀).app (VZ b₀) (gZ b₀ (MvPolynomial.X i)))) := fun i => by
    rw [germ_app_eq_functionFieldMap _ _ _ _ hsqF _ _,
      germToFunctionField_app_app_of_comp_eq _ _ _ (M.fibreMap_comp hZ₀ hSW hWS t j₀)]
  have hWf : ∀ F : Mori.PrimeDivisor
      ((M.stage ((H1.trans h₂).trans hS) ⋙ Over.pullback t).obj j).left,
      F.ordForm (Mori.pullbackRationalPluriForms _
        ((M.stage ((H1.trans h₂).trans hS) ⋙ Over.pullback t).map μ).left
        (ωs.toPluriForms _)) =
      ∑ E ∈ TW, if F.idealSheaf = (𝓘W E).comap (M.fibreMap H1 (h₂.trans hS) t j) then
        E.ordForm (Mori.pullbackRationalPluriForms _ (X.map μ).left (ωK.toPluriForms _)) else 0 :=
            by
    intro F
    obtain ⟨ω's, hω's⟩ : ∃ ω : Mori.RationalTopForms
        (((M.stage ((H1.trans h₂).trans hS) ⋙ Over.pullback t).map μ).left ≫
          ((M.stage ((H1.trans h₂).trans hS) ⋙ Over.pullback t).obj j₀).hom) N,
        (letI := MMP.Mori.functionFieldAlgebra
          (((M.stage ((H1.trans h₂).trans hS) ⋙ Over.pullback t).map μ).left ≫
            ((M.stage ((H1.trans h₂).trans hS) ⋙ Over.pullback t).obj j₀).hom)
        ω = exteriorPower.ιMulti
          ((M.stage ((H1.trans h₂).trans hS) ⋙ Over.pullback t).obj j).left.functionField N
          fun i => KaehlerDifferential.D L
            ((M.stage ((H1.trans h₂).trans hS) ⋙ Over.pullback t).obj j).left.functionField
            (AlgebraicGeometry.functionFieldMap
              ((M.stage ((H1.trans h₂).trans hS) ⋙ Over.pullback t).map μ).left
              (((M.stage ((H1.trans h₂).trans hS) ⋙ Over.pullback t).obj
                  j₀).left.germToFunctionField
                (M.fibreMap hZ₀ hZS t j₀ ⁻¹ᵁ VZ b₀)
                ((M.fibreMap hZ₀ hZS t j₀).app (VZ b₀) (gZ b₀ (MvPolynomial.X i)))))) := ⟨_, rfl⟩
    rw [pullbackRationalPluriForms_ιMulti _ _ hμs.functionFieldMap_bijective (hdZ.trans hN) ωs
      hωs0 _ hωs ω's hω's, ordForm_congr_hom (Over.w _) _ ω's hω's σs
      (by rw [hσs]; simp only [gWs]; try rfl) F, hWfs F]
    refine Finset.sum_congr rfl fun E _ => ?_
    split_ifs
    · obtain ⟨ω'K, hω'K⟩ : ∃ ω : Mori.RationalTopForms ((X.map μ).left ≫ (X.obj j₀).hom) N,
          (letI := MMP.Mori.functionFieldAlgebra ((X.map μ).left ≫ (X.obj j₀).hom)
          ω = exteriorPower.ιMulti (X.obj j).left.functionField N fun i =>
            KaehlerDifferential.D K (X.obj j).left.functionField
              (AlgebraicGeometry.functionFieldMap (X.map μ).left
                ((X.obj j₀).left.germToFunctionField (M.cmp hZ₀ j₀ ⁻¹ᵁ VZ b₀)
                  ((M.cmp hZ₀ j₀).app (VZ b₀) (gZ b₀ (MvPolynomial.X i)))))) := ⟨_, rfl⟩
      rw [pullbackRationalPluriForms_ιMulti _ _ hbij hN ωK hω0 _ hωK ω'K hω'K,
        ordForm_congr_hom (Over.w (X.map μ)) _ ω'K hω'K σWK
            (by rw [hσWK]; simp only [gWK]; try rfl) E]
    · rfl
  -- the boundaries
  have hPT : ∀ l, P l ∈ T₁ := fun l => Finset.mem_union_left _ (hmemZ ⟨c l, ι l⟩ (P l) (hP l))
  have hP'T : ∀ l, P' l ∈ TW := fun l => hTaW (hmemW ⟨c' l, ι' l⟩ (P' l) (hP' l))
  have hPrel : ∀ l Γ, Γ.idealSheaf = (𝓘Z' (P l)).comap (M.fibreMap H1 (h₂.trans hS) t j₀) ↔
      Γ = Ps l := by
    intro l Γ
    have hh : ∃ Q : Mori.PrimeDivisor (X.obj j₀).left,
        Q.support = Set.range (X.map (⟨c l, ι l⟩ : Σ c : J, c ⟶ j₀).2).left.base := ⟨P l, hP l⟩
    have hch : hh.choose = P l :=
      AlgebraicGeometry.PrimeDivisor.eq_of_support_eq (hh.choose_spec.trans (hP l).symm)
    have hr := HAZ ⟨c l, ι l⟩ hh L t
    rw [hch] at hr
    exact idealSheaf_eq_comap_iff (hr.trans (hPs l).symm) (hmZ (P l) (hT₁Z (hPT l))) Γ
  have hP'rel : ∀ l F, F.idealSheaf = (𝓘W (P' l)).comap (M.fibreMap H1 (h₂.trans hS) t j) ↔
      F = Ps' l := by
    intro l F
    have hh : ∃ Q : Mori.PrimeDivisor (X.obj j).left,
        Q.support = Set.range (X.map (⟨c' l, ι' l⟩ : Σ c : J, c ⟶ j).2).left.base :=
      ⟨P' l, hP' l⟩
    have hch : hh.choose = P' l :=
      AlgebraicGeometry.PrimeDivisor.eq_of_support_eq (hh.choose_spec.trans (hP' l).symm)
    have hr := HAW ⟨c' l, ι' l⟩ hh L t
    rw [hch] at hr
    exact idealSheaf_eq_comap_iff (hr.trans (hPs' l).symm) (hmW (P' l) (hP'T l)) F
  -- spread local equations of the Cartier divisors of the lattice
  have hHG : ∀ g ∈ (G : Set (Mori.Divisor (X.obj j₀).left)),
      HasSpreadLocalEquations (X.map μ).left
        ((M.stage ((H1.trans h₂).trans hS) ⋙ Over.pullback t).map μ).left TZ
        (fun Γ E => Γ.idealSheaf = (𝓘Z' E).comap (M.fibreMap H1 (h₂.trans hS) t j₀)) TW
        (fun F E => F.idealSheaf = (𝓘W E).comap (M.fibreMap H1 (h₂.trans hS) t j)) g :=
    fun g hg => HG ⟨g, hg⟩ L t hdZ hdW hmZ hmW
  have hgood : ∀ D : Mori.Divisor (X.obj j₀).left, D.IsCartier → (∀ E, D.coeff E ≠ 0 → E ∈ T₁) →
      HasSpreadLocalEquations (X.map μ).left
        ((M.stage ((H1.trans h₂).trans hS) ⋙ Over.pullback t).map μ).left TZ
        (fun Γ E => Γ.idealSheaf = (𝓘Z' E).comap (M.fibreMap H1 (h₂.trans hS) t j₀)) TW
        (fun F E => F.idealSheaf = (𝓘W E).comap (M.fibreMap H1 (h₂.trans hS) t j)) D :=
    fun D hD hDT => HasSpreadLocalEquations.of_mem_span hHG (hGspan D hD hDT)
  refine ⟨Mori.topFormDivisor _ ωs, hWs, hμs, ?_⟩
  exact isCrepantBoundary_of_spreading (K := K) (L := L) hZ hN hW'' hμ'' hNW
    hZs (hdZ.trans hN) hWs hμs (hdW.trans hNW) TZ
    (fun Γ E => Γ.idealSheaf = (𝓘Z' E).comap (M.fibreMap H1 (h₂.trans hS) t j₀))
    (fun E Γ Γ' h h' => eq_of_idealSheaf_eq_comap h h') TW
    (fun F E => F.idealSheaf = (𝓘W E).comap (M.fibreMap H1 (h₂.trans hS) t j))
    hω0 hωs0 hZfs hWf T₁ hT₁Z hT₁ω hgood P q Ps hPT hPrel P' q' Ps' hP'T hP'rel K₀ hCr'

include hint in
/-- **Log resolutions and crepant boundaries along one morphism spread to the fibres.** -/
private lemma Model.eventually_crepantAt {j₀ j : J} (μ : j ⟶ j₀) : M.Eventually fun S h =>
    ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)),
      FibreVert X (M.stage h ⋙ Over.pullback t) → FibreMor X (M.stage h ⋙ Over.pullback t) →
      FibreCrepantAt X hint (M.stage h ⋙ Over.pullback t) μ := by
  classical
  have : Fintype J := FinCategory.fintypeObj
  -- prime divisors presented by images of arrows
  have hA : ∀ {i : J} (a : Σ c : J, c ⟶ i), M.Eventually fun S h =>
      ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)),
        FibreVert X (M.stage h ⋙ Over.pullback t) →
        ∀ P : Mori.PrimeDivisor (X.obj i).left, P.support = Set.range (X.map a.2).left.base →
          ∃ Ps : Mori.PrimeDivisor ((M.stage h ⋙ Over.pullback t).obj i).left,
            Ps.support = Set.range ((M.stage h ⋙ Over.pullback t).map a.2).left.base := by
    intro i a
    by_cases hP : ∃ P : Mori.PrimeDivisor (X.obj i).left,
        P.support = Set.range (X.map a.2).left.base
    · obtain ⟨P₀, hP₀⟩ := hP
      exact (M.eventually_range_primeDivisor hint a.2 P₀ hP₀).mono
        fun S h H L _ t hV _ _ => H L t (hV i).1 (hV i).2.1
    · exact M.eventually_true.mono fun S h _ L _ t _ P hP' => absurd ⟨P, hP'⟩ hP
  -- coincidences of images of arrows
  have hE : ∀ {i : J} (a b : Σ c : J, c ⟶ i), M.Eventually fun S h =>
      ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)),
        (Set.range (X.map a.2).left.base = Set.range (X.map b.2).left.base ↔
          Set.range ((M.stage h ⋙ Over.pullback t).map a.2).left.base =
            Set.range ((M.stage h ⋙ Over.pullback t).map b.2).left.base) := by
    intro i a b
    by_cases hab : Set.range (X.map a.2).left.base = Set.range (X.map b.2).left.base
    · exact ((M.eventually_range_subset a.2 b.2 hab.le).and
        (M.eventually_range_subset b.2 a.2 hab.ge)).mono
        fun S h H L _ t => ⟨fun _ => (H.1 L t).antisymm (H.2 L t), fun _ => hab⟩
    · by_cases h1 : Set.range (X.map a.2).left.base ⊆ Set.range (X.map b.2).left.base
      · have h2 : ¬ Set.range (X.map b.2).left.base ⊆ Set.range (X.map a.2).left.base :=
          fun h2 => hab (h1.antisymm h2)
        exact (M.eventually_range_not_subset b.2 a.2 h2).mono
          fun S h H L _ t => ⟨fun e => absurd e hab, fun e => absurd e.ge (H L t)⟩
      · exact (M.eventually_range_not_subset a.2 b.2 h1).mono
          fun S h H L _ t => ⟨fun e => absurd e hab, fun e => absurd e.le (H L t)⟩
  have h₁ := Model.Eventually.forall (fun a : Σ c : J, c ⟶ j₀ => hA a)
  have h₂ := Model.Eventually.forall (fun a : Σ c : J, c ⟶ j => hA a)
  have h₃ := Model.Eventually.forall
    (fun ab : (Σ c : J, c ⟶ j₀) × (Σ c : J, c ⟶ j₀) => hE ab.1 ab.2)
  have h₄ := Model.Eventually.forall
    (fun σ : Finset (Σ c : J, c ⟶ j₀) => M.eventually_logResolutionAlong hint μ σ)
  have h₅ := M.eventually_crepantBoundary hint μ
  refine ((((h₁.and h₂).and h₃).and h₄).and h₅).mono fun S h H L _ t hV hM => ?_
  obtain ⟨⟨⟨⟨H₁, H₂⟩, H₃⟩, H₄⟩, H₅⟩ := H
  intro _ _ n m c ι P q m' c' ι' P' q' hP hP' hLR hCr _ _ _
  choose Ps hPs using fun l => H₁ ⟨c l, ι l⟩ L t hV (P l) (hP l)
  choose Ps' hPs' using fun l => H₂ ⟨c' l, ι' l⟩ L t hV (P' l) (hP' l)
  have hcorr : ∀ l l', P l = P l' ↔ Ps l = Ps l' := fun l l' => by
    constructor
    · intro e
      refine AlgebraicGeometry.PrimeDivisor.eq_of_support_eq ?_
      rw [hPs, hPs]
      exact (H₃ (⟨c l, ι l⟩, ⟨c l', ι l'⟩) L t).mp (by rw [← hP, ← hP, e])
    · intro e
      refine AlgebraicGeometry.PrimeDivisor.eq_of_support_eq ?_
      rw [hP, hP]
      exact (H₃ (⟨c l, ι l⟩, ⟨c l', ι l'⟩) L t).mpr (by rw [← hPs, ← hPs, e])
  -- the log resolution on the fibre
  have hLRs : Fourfold.IsLogResolution ((M.stage h ⋙ Over.pullback t).obj j₀).hom
      (∑ l, Finsupp.single (Ps l) (q l)) ((M.stage h ⋙ Over.pullback t).map μ).left := by
    rw [isLogResolution_iff_along] at hLR ⊢
    let σ : Finset (Σ c : J, c ⟶ j₀) :=
      (Finset.univ.filter fun l => (∑ l, Finsupp.single (P l) (q l) :
        Mori.QDivisor (X.obj j₀).left).coeff (P l) ≠ 0).image fun l => ⟨c l, ι l⟩
    refine H₄ σ L t hV hM ‹_› _ _ ?_ ?_ hLR
    · rw [coe_supp_sum_single]
      ext x
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop, σ, Finset.mem_image,
        Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨l, hl, hx⟩
        exact ⟨⟨c l, ι l⟩, ⟨l, hl, rfl⟩, by rwa [← hP]⟩
      · rintro ⟨_, ⟨l, hl, rfl⟩, hx⟩
        exact ⟨l, hl, by rwa [hP]⟩
    · rw [coe_supp_sum_single]
      ext x
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop, σ, Finset.mem_image,
        Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨l, hl, hx⟩
        refine ⟨⟨c l, ι l⟩, ⟨l, ?_, rfl⟩, by rwa [← hPs]⟩
        rwa [coeff_sum_single_eq P Ps hcorr]
      · rintro ⟨_, ⟨l, hl, rfl⟩, hx⟩
        refine ⟨l, ?_, by rwa [hPs]⟩
        rwa [← coeff_sum_single_eq P Ps hcorr]
  exact ⟨Ps, Ps', hPs, hPs', hLRs, H₅ L t hV hM n ι P q ι' P' q' hP hP' hLR hCr Ps Ps' hPs hPs'
    hLRs⟩

/-- **Log resolutions and crepant boundaries on the fibres.** -/
private lemma eventually_fibreCrepant : M.Eventually fun S h =>
    ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)),
      FibreCrepant X hint (M.stage h ⋙ Over.pullback t) := by
  have : Fintype J := FinCategory.fintypeObj
  exact ((Model.Eventually.forall fun a : Σ j₀ j : J, j ⟶ j₀ =>
    M.eventually_crepantAt hint a.2.2).and
      ((eventually_fibreVert hint M).and (eventually_fibreMor hint M))).mono
    fun S h H L _ t j₀ j μ => H.1 ⟨j₀, j, μ⟩ L t (H.2.1 L t) (H.2.2 L t)

/-- **The fibres.** Over all late stages, every field-valued fibre of the model satisfies
`FibreVert`, `FibreMor`, `FibreDecomp` and `FibreCrepant`. -/
private lemma eventually_fibre : M.Eventually fun S h =>
    ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)),
      FibreVert X (M.stage h ⋙ Over.pullback t) ∧ FibreMor X (M.stage h ⋙ Over.pullback t) ∧
      FibreDecomp X (M.stage h ⋙ Over.pullback t) ∧
      FibreCrepant X hint (M.stage h ⋙ Over.pullback t) :=
  (((eventually_fibreVert hint M).and (eventually_fibreMor hint M)).and
    ((eventually_fibreDecomp hint M).and (eventually_fibreCrepant hint M))).mono
    fun S h ⟨⟨h₁, h₂⟩, h₃, h₄⟩ L _ t => ⟨h₁ L t, h₂ L t, h₃ L t, h₄ L t⟩

end Properties

end MMP.Spreading

@[expose] public section

namespace MMP

open MMP.Spreading in
/-- **Spreading out finite projective diagrams in characteristic zero.** Let `k₀ ⊆ K` be
algebraically closed fields of characteristic zero, `X` a finite diagram of integral projective
`K`-schemes and `𝓛 i` finitely many invertible sheaves on its vertices. There is a finitely
generated `k₀`-subalgebra `R ⊆ K` and a diagram `Y` of projective `R`-schemes, with base change to
`K` isomorphic to `X` and models `𝓜 i` of the sheaves, such that:
* every morphism of `Y` is projective and every vertex of `Y` is flat over `R`;
* flatness, surjectivity, isomorphism, closed immersion and smoothness of morphisms, smoothness of
  vertices, relative ampleness of the `𝓛 i`, isomorphisms `𝓛 i ≅ g^* 𝓛 i'`, and isomorphisms of an `𝓛 i`
  with the top relative differential forms `⋀ⁿ Ω`, are kept over `R`;
* over every field-valued point of `Spec R` the vertices are integral of the original dimensions,
  normal where `X` is normal, and birational or small morphisms of `X` stay so; decompositions of
  fibre products as disjoint unions of vertices are kept; and a projective log resolution of a
  normal vertex, with its crepant boundary on components presented by vertices, stays a projective
  log resolution with the crepant boundary of the same coefficients. -/
@[mmp "thm_mmp_projective_birational_spreading"]
public theorem exists_fg_subalgebra_model_of_isProjective_of_finCategory
    (k₀ K : Type u) [Field k₀] [Field K] [IsAlgClosed k₀] [IsAlgClosed K] [CharZero k₀]
    [Algebra k₀ K] {J : Type u} [SmallCategory J] [FinCategory J] (X : J ⥤ Over (Spec (.of K)))
    (hint : ∀ j, IsIntegral (X.obj j).left) (hproj : ∀ j, IsProjective (X.obj j).hom)
    {ι : Type u} [Finite ι] (v : ι → J) (𝓛 : ∀ i, (X.obj (v i)).left.Modules)
    [h𝓛 : ∀ i, Stacks.Ample.IsInvertibleModule _ (𝓛 i)] :
    ∃ (R : Subalgebra k₀ K), R.FG ∧
    ∃ (Y : J ⥤ Over (Spec (.of R)))
      (e : X ≅ Y ⋙ Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K))))
      (𝓜 : ∀ i, (Y.obj (v i)).left.Modules)
      (h𝓜 : ∀ i, Stacks.Ample.IsInvertibleModule _ (𝓜 i)),
      -- the model sheaves recover the given ones over `K`
      (∀ i, Nonempty (𝓛 i ≅ (Scheme.Modules.pullback
        ((e.hom.app (v i)).left ≫ pullback.fst (Y.obj (v i)).hom _)).obj (𝓜 i))) ∧
      -- projectivity and flatness of the model
      (∀ j, IsProjective (Y.obj j).hom ∧ Flat (Y.obj j).hom) ∧
      (∀ {j j'} (g : j ⟶ j'), IsProjective (Y.map g).left) ∧
      -- properties of vertices and morphisms valid over `K` hold over `R`
      (∀ j, Smooth (X.obj j).hom → Smooth (Y.obj j).hom) ∧
      (∀ {j j'} (g : j ⟶ j'),
        (Flat (X.map g).left → Flat (Y.map g).left) ∧
        (Surjective (X.map g).left → Surjective (Y.map g).left) ∧
        (IsIso (X.map g).left → IsIso (Y.map g).left) ∧
        (IsClosedImmersion (X.map g).left → IsClosedImmersion (Y.map g).left) ∧
        (Smooth (X.map g).left → Smooth (Y.map g).left)) ∧
      -- relative ampleness and isomorphisms of the specified sheaves are kept
      (∀ i, Mori.IsRelativelyAmple (X.obj (v i)).hom (𝓛 i) →
        @Mori.IsRelativelyAmple _ _ (Y.obj (v i)).hom (𝓜 i) (h𝓜 i)) ∧
      (∀ i {j'} (g : v i ⟶ j'), Mori.IsRelativelyAmple (X.map g).left (𝓛 i) →
        @Mori.IsRelativelyAmple _ _ (Y.map g).left (𝓜 i) (h𝓜 i)) ∧
      (∀ i i' (g : v i ⟶ v i'),
        Nonempty (𝓛 i ≅ (Scheme.Modules.pullback (X.map g).left).obj (𝓛 i')) →
        Nonempty (𝓜 i ≅ (Scheme.Modules.pullback (Y.map g).left).obj (𝓜 i'))) ∧
      -- a specified sheaf that is the top relative differential forms has such a model
      (∀ i (n : ℕ),
        Nonempty (𝓛 i ≅ Scheme.Hom.relativeDifferentialForms (X.obj (v i)).hom n) →
        Nonempty (𝓜 i ≅ Scheme.Hom.relativeDifferentialForms (Y.obj (v i)).hom n)) ∧
      -- every field-valued fibre of the model
      ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of R)),
        (∀ j, IsIntegral ((Y ⋙ Over.pullback t).obj j).left ∧
          topologicalKrullDim ((Y ⋙ Over.pullback t).obj j).left =
            topologicalKrullDim (X.obj j).left ∧
          (IsNormal (X.obj j).left → IsNormal ((Y ⋙ Over.pullback t).obj j).left)) ∧
        (∀ {j j'} (g : j ⟶ j'),
          (Mori.IsBirationalMorphism (X.map g).left →
            Mori.IsBirationalMorphism ((Y ⋙ Over.pullback t).map g).left) ∧
          (Fourfold.IsSmallMorphism (X.obj j).hom (X.obj j').hom (X.map g).left →
            Fourfold.IsSmallMorphism ((Y ⋙ Over.pullback t).obj j).hom
              ((Y ⋙ Over.pullback t).obj j').hom ((Y ⋙ Over.pullback t).map g).left)) ∧
        -- decompositions of fibre products as finite disjoint unions are kept
        (∀ {j₁ j₂ j : J} (f : j₁ ⟶ j) (g : j₂ ⟶ j) (n : ℕ) (w : Fin n → J)
          (a : ∀ k, w k ⟶ j₁) (b : ∀ k, w k ⟶ j₂) (h : ∀ k, a k ≫ f = b k ≫ g),
          IsIso (Sigma.desc fun k => pullback.lift (f := (X.map f).left) (g := (X.map g).left)
            (X.map (a k)).left (X.map (b k)).left
            (by rw [← Over.comp_left, ← Over.comp_left, ← X.map_comp, ← X.map_comp, h k])) →
          IsIso (Sigma.desc fun k => pullback.lift (f := ((Y ⋙ Over.pullback t).map f).left)
            (g := ((Y ⋙ Over.pullback t).map g).left)
            ((Y ⋙ Over.pullback t).map (a k)).left ((Y ⋙ Over.pullback t).map (b k)).left
            (by rw [← Over.comp_left, ← Over.comp_left, ← Functor.map_comp, ← Functor.map_comp,
              h k]))) ∧
        -- specified projective log resolutions keep their crepant boundaries
        (∀ {j₀ j : J} (μ : j ⟶ j₀) [IsLocallyNoetherian (X.obj j₀).left]
          [IsNormal (X.obj j₀).left] (n : ℕ)
          {m : ℕ} {c : Fin m → J} (ι : ∀ l, c l ⟶ j₀)
          (P : Fin m → Mori.PrimeDivisor (X.obj j₀).left) (q : Fin m → ℚ)
          {m' : ℕ} {c' : Fin m' → J} (ι' : ∀ l, c' l ⟶ j)
          (P' : Fin m' → Mori.PrimeDivisor (X.obj j).left) (q' : Fin m' → ℚ),
          haveI := hint j₀
          (∀ l, (P l).support = Set.range (X.map (ι l)).left.base) →
          (∀ l, (P' l).support = Set.range (X.map (ι' l)).left.base) →
          Fourfold.IsLogResolution (X.obj j₀).hom (∑ l, Finsupp.single (P l) (q l)) (X.map μ).left →
          (∃ (K₀ : Mori.Divisor (X.obj j₀).left) (hW : _) (hμ : _),
            Mori.IsCrepantBoundary (X.obj j₀).hom n K₀ (∑ l, Finsupp.single (P l) (q l))
              (X.map μ).left hW hμ (∑ l, Finsupp.single (P' l) (q' l))) →
          ∀ [IsIntegral ((Y ⋙ Over.pullback t).obj j₀).left]
            [IsLocallyNoetherian ((Y ⋙ Over.pullback t).obj j₀).left]
            [IsNormal ((Y ⋙ Over.pullback t).obj j₀).left],
          ∃ (Ps : Fin m → Mori.PrimeDivisor ((Y ⋙ Over.pullback t).obj j₀).left)
            (Ps' : Fin m' → Mori.PrimeDivisor ((Y ⋙ Over.pullback t).obj j).left),
            (∀ l, (Ps l).support = Set.range ((Y ⋙ Over.pullback t).map (ι l)).left.base) ∧
            (∀ l, (Ps' l).support = Set.range ((Y ⋙ Over.pullback t).map (ι' l)).left.base) ∧
            Fourfold.IsLogResolution ((Y ⋙ Over.pullback t).obj j₀).hom
              (∑ l, Finsupp.single (Ps l) (q l)) ((Y ⋙ Over.pullback t).map μ).left ∧
            ∃ (Ks : Mori.Divisor ((Y ⋙ Over.pullback t).obj j₀).left) (hW : _) (hμ : _),
              Mori.IsCrepantBoundary ((Y ⋙ Over.pullback t).obj j₀).hom n Ks
                (∑ l, Finsupp.single (Ps l) (q l)) ((Y ⋙ Over.pullback t).map μ).left hW hμ
                (∑ l, Finsupp.single (Ps' l) (q' l))) := by
  obtain ⟨M⟩ := exists_model (k₀ := k₀) (v := v) (𝓛 := 𝓛) hproj
  obtain ⟨S, hS, H⟩ := ((((((eventually_projective_flat M).and (eventually_smooth M)).and
    (eventually_morphisms M)).and (eventually_ample M)).and (eventually_sheafIso M)).and
    (eventually_differentials hint M)).and (eventually_fibre hint M)
  obtain ⟨⟨⟨⟨⟨⟨⟨H₁, H₂⟩, H₃⟩, H₄⟩, ⟨H₅, H₆⟩⟩, H₇⟩, H₈⟩, H₉⟩ := H S le_rfl
  obtain ⟨q, hq, hqp⟩ := M.isCartesian_stage (hS)
  refine ⟨S.1, S.2, M.stage (hS), hq.iso, M.stageN (hS),
    M.stageN_invertible (hS), fun i => ⟨?_⟩, H₁, H₂, H₃, H₄, H₅, H₆, H₇, H₈,
    fun L _ t => H₉ L t⟩
  exact (M.θ i).symm ≪≫ (Scheme.Modules.pullbackCongr (hqp (v i)).symm).app _ ≪≫
    ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
    (Scheme.Modules.pullbackCongr (hq.iso_hom_app_left_fst (v i))).symm.app _

end MMP

end
