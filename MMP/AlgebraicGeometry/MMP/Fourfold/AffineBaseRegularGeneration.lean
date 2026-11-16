module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Divisor.LinearSeries
public import StacksFrontier.AlgebraicGeometry.Cohomology.GlobalGeneration.Stalks
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.RegularityGlobalGeneration
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyAtTheTerminalObject
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.CohomologyPresheafComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.SpectralSpaces
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.DegreeZeroSections
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.HyperplaneRegularity
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceSectionMulShape
public import StacksFrontier.AlgebraicGeometry.TwistFlatness.Projective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensorBraidingGlue
public import StacksFrontier.AlgebraicGeometry.SelfBraidingInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjDegreeOneRepresents
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Dimension.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.HyperplaneRestrictionConstruction
public import StacksFrontier.AlgebraicGeometry.EtaleAlgebra.FlatBaseChange.AlgebraComparisonEpi
public import StacksFrontier.AlgebraicGeometry.Divisors.SectionPowerOpen
public import StacksFrontier.AlgebraicGeometry.InvertiblePushforwardPullback
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.StalkBridge
public import StacksFrontier.AlgebraicGeometry.Divisors.NonvanishingLocusRestrict
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.AlgebraicGeometry.ProjTwistFunctor.TensorExact
public import MMP.AlgebraicGeometry.Divisor.CartierLineBundle
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.HyperplaneTwistSequence
public import StacksFrontier.AlgebraicGeometry.AmpleProjectiveImmersion.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.ProjectiveSerreVanishing
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Coherent
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AmpleFormalSystemEmbeddedTuple
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ContractionMorphism
public import StacksFrontier.AlgebraicGeometry.RelativeSerreVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.CanonicalTensorProperSupport

/-!
# Cohomological generation over an affine base

Let `X ⟶ Z` be projective with `Z` affine, `dim X = n`, and `H` relatively very ample. The
statement in view is that a coherent `ℱ` with `Hⁱ(X, ℱ(mH)) = 0` for all `i > 0` and `m ≥ -n`
is globally generated: Castelnuovo–Mumford regularity over an affine base. This file proves
Mumford's multiplication theorem for regular coherent sheaves on `ℙᴺ_A` over an arbitrary ring `A`,
by the Koszul complex of the coordinates, hence regularity implies global generation on `ℙᴺ_A`, and
the pushforward step of the argument, and deduces the cohomological generation criterion over an
affine base.

The argument runs as follows. A closed immersion `ι : X ⟶ ℙᴺ_A` with `ι^*𝒪(1) ≅ 𝒪_X(H)` turns
`ℱ` into the coherent sheaf `𝒢 = ι_*ℱ` on `ℙᴺ_A`. The cohomology of `𝒢(m)` is that of `ℱ(mH)`,
and by Grothendieck's vanishing theorem it vanishes above `n`. So `𝒢` is `d`-regular for every
`d ≥ n` after twisting by `-n`, and Mumford's descent applies: `𝒢(d)` is globally generated for
`d ≫ 0` by Serre's theorem, and if the products of global sections of `𝒢(d)` with linear forms
fill `H⁰(𝒢(d + 1))`, global generation passes from `𝒢(d + 1)` down to `𝒢(d)`. Finally, global
generation of `ι_*ℱ` gives that of `ℱ`.

## Main definitions

  the products of global sections of `ℱ(d)` with global sections of `𝒪(1)`.
  `H⁰(ℙᴺ_A, 𝒢(d + 1))`.
* `MMP.Fourfold.KoszulAbs.kos`: the Koszul complex of a list of commuting operators `𝟭 ⟶ T` on an
  abelian category, as an iterated mapping cone.
* `MMP.Fourfold.HasTwistedKoszulChain`: the twisted Koszul complex of the coordinates of `ℙᴺ_A`,
  split into short exact sequences with the shape of terms the cohomological argument uses.

## Main results

* `MMP.Fourfold.isGeneratedByGlobalSections_projectiveTwist_of_mulSectionsClosure`: one step of
  the descent over an arbitrary ring `R`.
* `MMP.Fourfold.isGeneratedByGlobalSections_projectiveTwist_of_forall_mulSectionsClosure`: the
  whole descent, starting from Serre's theorem.
* `MMP.Fourfold.mulSectionsClosure_zero_eq_top`: the multiplication theorem on `ℙ⁰_R`.
* `MMP.Fourfold.isGeneratedByGlobalSections_projectiveTwist_of_regular`: Castelnuovo–Mumford
  regularity on `ℙⁿ_R`.
* `MMP.Fourfold.surjective_secF_map_of_shortExact`: if `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` is short exact and
  `H¹(ℱ₁) = 0`, then `H⁰(ℱ₂) ⟶ H⁰(ℱ₃)` is onto.
* `MMP.Fourfold.isZero_Hgroup_of_chain`: the cohomological chase through a chain of short exact
  sequences, as in the Koszul proof of Mumford's multiplication theorem.
* `MMP.Fourfold.mulSectionsClosure_eq_top_of_hasTwistedKoszulChain`: the multiplication theorem on
  `ℙᴺ_A`, for a module admitting a twisted Koszul chain.
* `MMP.Fourfold.KoszulAbs.isZero_homology_kos`: the Koszul complex of operators that generate
  (`⨁ X ⟶ T X` epi for every `X`) and commute (`τ (T Y) = T (τ Y)`) is acyclic, because each
  operator is null-homotopic on it
  (`MMP.Fourfold.KoszulAbs.nonempty_homotopy_kos`).
* `MMP.Fourfold.KoszulAbs.exists_koszul_chain`: the acyclic Koszul complex split into short exact
  sequences, with the shape of its terms.
* `MMP.Fourfold.hasTwistedKoszulChain`, `MMP.Fourfold.mulSectionsClosure_eq_top_of_regular`:
  **Mumford's multiplication theorem on `ℙᴺ_A` over an arbitrary ring `A`**, from the generation
  of `𝒪(1)` by the coordinate sections (`MMP.Fourfold.epi_coordFreeHom`) and the trivial
  self-braiding of `𝒪(1)` (`MMP.Fourfold.braiding_self_twistOver_one`).
* `MMP.Fourfold.isZero_Hgroup_of_topologicalKrullDim_le`: Grothendieck vanishing on a Noetherian
  scheme, in the spelling `Hgroup X.ringCatSheaf ⊤ i`.
* `MMP.Fourfold.isGloballyGenerated_of_isGeneratedByGlobalSections`: a module generated by a
  family of global sections (Stacks 03DE) is globally generated in the sense of Lazarsfeld 1.1.10,
  `MMP.Intersection.IsGloballyGenerated`.
* `MMP.Fourfold.isGloballyGenerated_of_pushforward` and
  `MMP.Fourfold.isGloballyGenerated_of_isGeneratedByGlobalSections_pushforward`: global generation
  descends along a morphism that is a topological embedding, in particular a closed immersion.
* `MMP.Fourfold.isGloballyGenerated_of_forall_isZero_Hgroup_twist`: **cohomological generation
  over an affine base**: if `Hⁱ(X, ℱ(mH)) = 0` for all `i > 0` and `m ≥ -dim X`, with `H`
  relatively very ample over an affine Noetherian `Z`, then the coherent sheaf `ℱ` is globally
  generated.
* `MMP.Fourfold.isGloballyGenerated_of_regular_of_isClosedImmersion`: the same for a closed
  subscheme of `ℙᴺ_R`.
* `MMP.Fourfold.projectiveTwistPushforwardIso`: `(ι_*ℱ)(d) ≅ ι_*(ℱ ⊗ L^{⊗ d})`, the projection
  formula.
* `MMP.Fourfold.nonempty_lineBundle_int_smul_iso`: `𝒪_X(mD) ≅ 𝒪_X(D)^{⊗ m}` for `m : ℤ`.

## Implementation notes

The Koszul complex of the coordinates is not formed with exterior powers, but as the mapping cone
of multiplication by the last coordinate on the Koszul complex of the others, in the abelian
category of modules, with `T` the twist by one and `τ` the multiplication by a coordinate section
(`MMP.Fourfold.twistOp`). The commutation `x_i x_j = x_j x_i` needed for the homotopies is the
single hypothesis `τ (T Y) = T (τ Y)`, which holds because `𝒪(1)` has trivial self-braiding; no
coherence between the regrouping isomorphisms `𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a + b)` is needed, since the
Koszul terms are `T`-powers of `𝒢(d - N)` and are compared with `𝒢(d - k)` only through
isomorphisms whose compatibility is never used, except for the last twist, where the naturality of
`τ` suffices.

The multiplication condition is phrased with an additive subgroup rather than a span over a base
field: over an arbitrary ring `R` the products of global sections of `ℱ(d)` with linear forms
generate `H⁰(ℱ(d + 1))` as an abelian group exactly when they generate it as a module over
`Γ(ℙⁿ_R, 𝒪)`, since that ring acts through the first factor. The descent step is the field-case
argument of `AlgebraicGeometry.isGeneratedByGlobalSections_projectiveTwist_of_span_mulSections`
with the field removed: nothing in it used more than surjectivity on sections over `⊤`.

## References

* [Stacks Project, Tag 08A3](https://stacks.math.columbia.edu/tag/08A3)
* [Stacks Project, Tag 08A7](https://stacks.math.columbia.edu/tag/08A7)
* [Stacks Project, Tag 08A8](https://stacks.math.columbia.edu/tag/08A8)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
* [Stacks Project, Tag 01AN](https://stacks.math.columbia.edu/tag/01AN)
* [Lazarsfeld, *Positivity in Algebraic Geometry I*, Theorem 1.8.5]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open TopologicalSpace Opposite AlgebraicGeometry
open MMP.Intersection (IsGloballyGenerated IsGloballyGeneratedAt)
open Stacks.AlgebraicGeometry.ProjTwistTensorPow
open Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication

universe u

namespace MMP.Fourfold

namespace KoszulAbs

section

open CategoryTheory.Preadditive HomologicalComplex

universe w v u₁

variable {C : Type u₁} [Category.{v} C] [Abelian C] [HasFiniteBiproducts C] (T : C ⥤ C) [T.Additive]

/-- Multiplication by a natural transformation, termwise on a complex. -/
def sigmaHom (τ : 𝟭 C ⟶ T) (X : CochainComplex C ℤ) :
    X ⟶ (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj X where
  f n := τ.app (X.X n)
  comm' i j _ := by simpa using (τ.naturality (X.d i j)).symm

/-- The cone of multiplication by `τ`. -/
noncomputable abbrev cone (τ : 𝟭 C ⟶ T) (X : CochainComplex C ℤ) : CochainComplex C ℤ :=
  homotopyCofiber (sigmaHom T τ X)

/-- In the cochain shape on `ℤ`, `i` is related to `i + 1`. -/
theorem up_rel (i : ℤ) : (ComplexShape.up ℤ).Rel i (i + 1) := rfl

omit [HasFiniteBiproducts C] in
open homotopyCofiber in
/-- Multiplication by `τ` is null-homotopic on the cone of multiplication by `τ`. -/
theorem nonempty_homotopy_sigma_cone_self (τ : 𝟭 C ⟶ T)
    (hτ : ∀ Y, τ.app (T.obj Y) = T.map (τ.app Y)) (X : CochainComplex C ℤ) :
    Nonempty (Homotopy (sigmaHom T τ (cone T τ X)) 0) := by
  let φ := sigmaHom T τ X
  refine ⟨{ hom := fun i j => if hij : (ComplexShape.up ℤ).Rel j i then
                sndX φ i ≫ T.map (inlX φ i j hij) else 0,
            zero := fun i j hij => dite_eq_right hij,
            comm := fun n => ?_ }⟩
  have hr : (ComplexShape.up ℤ).Rel n (n + 1) := up_rel n
  have hl : (ComplexShape.up ℤ).Rel (n - 1) n := by simp [ComplexShape.up]
  rw [dNext_eq _ hr, prevD_eq _ hl]
  simp only [dite_eq_left hr, dite_eq_left hl]
  have hr2 : (ComplexShape.up ℤ).Rel (n + 1) (n + 2) := by simp [ComplexShape.up]; ring
  apply ext_from_X φ (n + 1) n hr
  · have h1 : inlX φ (n + 1) n hr ≫ (cone T τ X).d n (n + 1) =
        -X.d (n + 1) (n + 2) ≫ inlX φ (n + 2) (n + 1) hr2 + φ.f (n + 1) ≫ inrX φ (n + 1) :=
      inlX_d φ n (n + 1) (n + 2) hr hr2
    have hn : inlX φ (n + 1) n hr ≫ (sigmaHom T τ (cone T τ X)).f n =
        τ.app (X.X (n + 1)) ≫ T.map (inlX φ (n + 1) n hr) :=
      τ.naturality (inlX φ (n + 1) n hr)
    rw [Preadditive.comp_add, Preadditive.comp_add]
    simp only [zero_f, comp_zero, add_zero]
    rw [hn, reassoc_of% h1]
    simp
    rfl
  · have h2 : inlX φ n (n - 1) hl ≫ (cone T τ X).d (n - 1) n =
        -X.d n (n + 1) ≫ inlX φ (n + 1) n hr + φ.f n ≫ inrX φ n :=
      inlX_d φ (n - 1) n (n + 1) hl hr
    have hn : inrX φ n ≫ (sigmaHom T τ (cone T τ X)).f n =
        τ.app (((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj X).X n) ≫ T.map (inrX φ n) :=
      τ.naturality (inrX φ n)
    have h3 : inrX φ n ≫ (cone T τ X).d n (n + 1) = T.map (X.d n (n + 1)) ≫ inrX φ (n + 1) :=
      inrX_d φ n (n + 1)
    rw [Preadditive.comp_add, Preadditive.comp_add]
    simp only [zero_f, comp_zero, add_zero]
    rw [hn, reassoc_of% h3]
    simp only [inrX_sndX_assoc, Category.assoc, Functor.mapHomologicalComplex_obj_d]
    rw [← T.map_comp (inlX φ n (n - 1) hl), h2]
    have h4 := hτ (X.X n)
    erw [h4]
    rw [← T.map_comp, T.map_add, T.map_neg]
    have : φ.f n = τ.app (X.X n) := rfl
    rw [this]
    simp only [Functor.map_comp]
    abel

omit [HasFiniteBiproducts C] in
open homotopyCofiber in
/-- If multiplication by `τ'` is null-homotopic on `X`, then it is null-homotopic on the cone of
multiplication by `τ` on `X`. -/
theorem nonempty_homotopy_sigma_cone (τ τ' : 𝟭 C ⟶ T)
    (hτ : ∀ Y, τ.app (T.obj Y) = T.map (τ.app Y))
    (hτ' : ∀ Y, τ'.app (T.obj Y) = T.map (τ'.app Y)) (X : CochainComplex C ℤ)
    (h : Homotopy (sigmaHom T τ' X) 0) :
    Nonempty (Homotopy (sigmaHom T τ' (cone T τ X)) 0) := by
  let φ := sigmaHom T τ X
  refine ⟨{ hom := fun i j => if hij : (ComplexShape.up ℤ).Rel j i then
                fstX φ i (i + 1) (up_rel i) ≫ (-(h.hom (i + 1) i)) ≫ T.map (inlX φ i j hij) +
                  sndX φ i ≫ T.map (h.hom i j) ≫ T.map (inrX φ j) else 0,
            zero := fun i j hij => dite_eq_right hij,
            comm := fun n => ?_ }⟩
  have hr : (ComplexShape.up ℤ).Rel n (n + 1) := up_rel n
  have hl : (ComplexShape.up ℤ).Rel (n - 1) n := by simp [ComplexShape.up]
  have hr2 : (ComplexShape.up ℤ).Rel (n + 1) (n + 1 + 1) := up_rel _
  rw [dNext_eq _ hr, prevD_eq _ hl]
  simp only [dite_eq_left hr, dite_eq_left hl]
  apply ext_from_X φ (n + 1) n hr
  · have hn : inlX φ (n + 1) n hr ≫ (sigmaHom T τ' (cone T τ X)).f n =
        τ'.app (X.X (n + 1)) ≫ T.map (inlX φ (n + 1) n hr) :=
      τ'.naturality (inlX φ (n + 1) n hr)
    have h1 : inlX φ (n + 1) n hr ≫ (cone T τ X).d n (n + 1) =
        -X.d (n + 1) (n + 1 + 1) ≫ inlX φ (n + 1 + 1) (n + 1) hr2 + φ.f (n + 1) ≫ inrX φ (n + 1) :=
      inlX_d φ n (n + 1) (n + 1 + 1) hr hr2
    have h2 : inlX φ n (n - 1) hl ≫ (cone T τ X).d (n - 1) n =
        -X.d n (n + 1) ≫ inlX φ (n + 1) n hr + φ.f n ≫ inrX φ n :=
      inlX_d φ (n - 1) n (n + 1) hl hr
    have h6 : T.map (inlX φ n (n - 1) hl) ≫ T.map ((cone T τ X).d (n - 1) n) =
        T.map (-X.d n (n + 1) ≫ inlX φ (n + 1) n hr + φ.f n ≫ inrX φ n) := by
      rw [← T.map_comp, h2]
    have hcn := h.comm (n + 1)
    rw [dNext_eq _ hr2, prevD_eq _ hr] at hcn
    simp only [Preadditive.comp_add, Preadditive.add_comp, zero_f, add_zero]
    rw [hn]
    simp only [reassoc_of% h1, inlX_fstX_assoc, inlX_sndX_assoc, zero_comp, inrX_sndX_assoc,
      inrX_fstX_assoc, add_zero, Category.assoc,
      Preadditive.add_comp, Preadditive.neg_comp, Preadditive.comp_neg, comp_zero,
      Functor.mapHomologicalComplex_obj_d]
    have hnat : φ.f (n + 1) ≫ T.map (h.hom (n + 1) n) =
        h.hom (n + 1) n ≫ T.map (φ.f n) := by
      have := τ.naturality (h.hom (n + 1) n)
      have h7 := hτ (X.X n)
      change h.hom (n + 1) n ≫ τ.app (T.obj (X.X n)) = τ.app (X.X (n + 1)) ≫
        T.map (h.hom (n + 1) n) at this
      rw [h7] at this
      exact this.symm
    have hcn' : τ'.app (X.X (n + 1)) = (X.d (n + 1) (n + 1 + 1) ≫
        (h.hom (n + 1 + 1) (n + 1) : X.X (n + 1 + 1) ⟶ T.obj (X.X (n + 1))) :
          X.X (n + 1) ⟶ T.obj (X.X (n + 1))) +
        ((h.hom (n + 1) n : X.X (n + 1) ⟶ T.obj (X.X n)) ≫ T.map (X.d n (n + 1)) :
          X.X (n + 1) ⟶ T.obj (X.X (n + 1))) := by
      simpa [sigmaHom] using hcn
    rw [h6, hcn']
    simp only [Preadditive.add_comp, Category.assoc, neg_neg, Functor.map_add, Functor.map_neg,
      Functor.map_comp, Preadditive.comp_add, Preadditive.comp_neg, neg_zero, zero_add]
    rw [reassoc_of% hnat]
    abel
  · have hn : inrX φ n ≫ (sigmaHom T τ' (cone T τ X)).f n =
        τ'.app (((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj X).X n) ≫ T.map (inrX φ n) :=
      τ'.naturality (inrX φ n)
    have h3 : inrX φ n ≫ (cone T τ X).d n (n + 1) = T.map (X.d n (n + 1)) ≫ inrX φ (n + 1) :=
      inrX_d φ n (n + 1)
    have h3' : inrX φ (n - 1) ≫ (cone T τ X).d (n - 1) n =
        T.map (X.d (n - 1) n) ≫ inrX φ n := inrX_d φ (n - 1) n
    have hcn := h.comm n
    rw [dNext_eq _ hr, prevD_eq _ hl] at hcn
    have h5 : T.map (inrX φ (n - 1)) ≫ T.map ((cone T τ X).d (n - 1) n) =
        T.map (T.map (X.d (n - 1) n)) ≫ T.map (inrX φ n) := by
      rw [← T.map_comp, h3', T.map_comp]
    simp only [Preadditive.comp_add, Preadditive.add_comp, zero_f, add_zero]
    rw [hn]
    simp only [reassoc_of% h3, inrX_fstX_assoc, zero_comp, inrX_sndX_assoc, zero_add,
      Category.assoc, Functor.mapHomologicalComplex_obj_d, comp_zero]
    rw [h5]
    have hcn' : τ'.app (X.X n) = (X.d n (n + 1) ≫
        (h.hom (n + 1) n : X.X (n + 1) ⟶ T.obj (X.X n)) : X.X n ⟶ T.obj (X.X n)) +
        ((h.hom n (n - 1) : X.X n ⟶ T.obj (X.X (n - 1))) ≫ T.map (X.d (n - 1) n) :
          X.X n ⟶ T.obj (X.X n)) := by
      simpa [sigmaHom] using hcn
    erw [hτ' (X.X n), hcn']
    simp only [Functor.map_add, Functor.map_comp, Preadditive.add_comp, Category.assoc]

omit [HasFiniteBiproducts C] in
/-- If the faithful additive functor `T` sends `H` to a zero object, `H` is zero. -/
theorem isZero_of_isZero_obj [T.Faithful] {H : C} (h : IsZero (T.obj H)) : IsZero H := by
  rw [IsZero.iff_id_eq_zero]
  apply T.map_injective
  rw [T.map_id, T.map_zero]
  exact h.eq_of_src _ _

/-- **The Koszul argument.** If multiplication by each of the generating `σ i` is null-homotopic
on a complex `K`, then `K` is acyclic. -/
theorem isZero_homology_of_homotopy [T.Faithful] [T.PreservesMonomorphisms] {m : ℕ}
    (σ : Fin m → (𝟭 C ⟶ T))
    (hgen : ∀ X : C, Epi (biproduct.desc fun i : Fin m => (σ i).app X :
      (⨁ fun _ : Fin m => X) ⟶ T.obj X))
    (K : CochainComplex C ℤ) (h : ∀ i, Homotopy (sigmaHom T (σ i) K) 0) {a n c : ℤ}
    (hr : (ComplexShape.up ℤ).Rel n c) (hl : (ComplexShape.up ℤ).Rel a n) :
    IsZero (K.sc' a n c).homology := by
  set S := K.sc' a n c with hS
  let ιc : S.cycles ⟶ K.X n := S.iCycles
  let αc : K.X a ⟶ S.cycles := S.toCycles
  have hz : ∀ i, (σ i).app S.homology = 0 := by
    intro i
    have hπ : S.homologyπ ≫ (σ i).app S.homology = (σ i).app S.cycles ≫ T.map S.homologyπ :=
      (σ i).naturality S.homologyπ
    have : Mono ιc := inferInstanceAs (Mono S.iCycles)
    have hmono : Mono (T.map ιc) := inferInstance
    have hcomm := (h i).comm n
    rw [dNext_eq _ hr, prevD_eq _ hl] at hcomm
    have key : (σ i).app S.cycles = (ιc ≫ (h i).hom n a) ≫ T.map αc := by
      apply (cancel_mono (T.map ιc)).1
      have hn : (σ i).app S.cycles ≫ T.map ιc = ιc ≫ (σ i).app (K.X n) :=
        ((σ i).naturality ιc).symm
      rw [hn]
      have hc : (σ i).app (K.X n) = (K.d n c ≫
          ((h i).hom c n : K.X c ⟶ T.obj (K.X n)) : K.X n ⟶ T.obj (K.X n)) +
          (((h i).hom n a : K.X n ⟶ T.obj (K.X a)) ≫ T.map (K.d a n) :
            K.X n ⟶ T.obj (K.X n)) := by
        simpa [sigmaHom] using hcomm
      rw [hc, Preadditive.comp_add]
      have hg : ιc ≫ K.d n c = 0 := S.iCycles_g
      rw [reassoc_of% hg, zero_comp, zero_add, Category.assoc, ← T.map_comp]
      have : αc ≫ ιc = K.d a n := S.toCycles_i
      rw [this, Category.assoc]
    have : S.homologyπ ≫ (σ i).app S.homology = 0 := by
      have hαπ : αc ≫ S.homologyπ = 0 := S.toCycles_comp_homologyπ
      rw [hπ, key, Category.assoc, ← T.map_comp αc, hαπ, T.map_zero, comp_zero]
    exact (cancel_epi S.homologyπ).1 (by rw [this, comp_zero])
  have hdesc : biproduct.desc (fun i : Fin m => (σ i).app S.homology) = 0 := by
    apply biproduct.hom_ext'
    intro i
    rw [biproduct.ι_desc, hz, comp_zero]
  have := hgen S.homology
  exact isZero_of_isZero_obj T (IsZero.of_epi_eq_zero _ hdesc)

/-- The iterated cone of a list of operators `τ`, applied to a complex concentrated in degree `0`:
the Koszul complex of `τ₀, …, τ_{m-1}` on `M`, a cochain complex in degrees `-m, …, 0`. -/
noncomputable def kos : List (𝟭 C ⟶ T) → C → CochainComplex C ℤ
  | [], M => (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M
  | τ :: l, M => cone T τ (kos l M)

/-- `T^j M`. -/
def tpow : ℕ → C → C
  | 0, M => M
  | j + 1, M => T.obj (tpow j M)

/-- The commutation hypothesis on a list of operators: `τ (T Y) = T (τ Y)`. -/
def CommList (l : List (𝟭 C ⟶ T)) : Prop :=
  ∀ τ ∈ l, ∀ Y : C, τ.app (T.obj Y) = T.map (τ.app Y)

omit [HasFiniteBiproducts C] in
/-- For commuting operators, multiplication by each operator of the list is null-homotopic on the
Koszul complex `kos T l M`. -/
theorem nonempty_homotopy_kos : ∀ (l : List (𝟭 C ⟶ T)) (M : C), CommList T l →
    ∀ i : Fin l.length, Nonempty (Homotopy (sigmaHom T (l.get i) (kos T l M)) 0)
  | [], _, _, i => i.elim0
  | τ :: l, M, hl, i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact nonempty_homotopy_sigma_cone_self T τ (hl τ (List.mem_cons_self))
        (kos T l M)
    · obtain ⟨h⟩ := nonempty_homotopy_kos l M (fun τ' hτ' => hl τ' (List.mem_cons_of_mem _ hτ')) j
      exact nonempty_homotopy_sigma_cone T τ (l.get j) (hl τ (List.mem_cons_self))
        (hl _ (List.mem_cons_of_mem _ (List.get_mem l j))) (kos T l M) h

/-- **The Koszul complex of operators that generate is acyclic.** -/
theorem isZero_homology_kos [T.Faithful] [T.PreservesMonomorphisms] (l : List (𝟭 C ⟶ T)) (M : C)
    (hl : CommList T l)
    (hgen : ∀ X : C, Epi (biproduct.desc fun i : Fin l.length => (l.get i).app X :
      (⨁ fun _ : Fin l.length => X) ⟶ T.obj X))
    {a b c : ℤ} (hbc : (ComplexShape.up ℤ).Rel b c) (hab : (ComplexShape.up ℤ).Rel a b) :
    IsZero ((kos T l M).sc' a b c).homology :=
  isZero_homology_of_homotopy T l.get hgen (kos T l M)
    (fun i => (nonempty_homotopy_kos T l M hl i).some) hbc hab

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

/-- `A` is a finite sum of copies of `Y` (and zero objects), up to isomorphism. -/
inductive IsFinSum (Y : C) : C → Prop
  | zero {A : C} : IsZero A → IsFinSum Y A
  | self : IsFinSum Y Y
  | of_iso {A B : C} : (A ≅ B) → IsFinSum Y B → IsFinSum Y A
  | biprod {A B : C} : IsFinSum Y A → IsFinSum Y B → IsFinSum Y (A ⊞ B)

omit [HasFiniteBiproducts C] in
/-- If `A` is a finite sum of copies of `Y`, then `T A` is a finite sum of copies of `T Y`. -/
theorem IsFinSum.map {Y A : C} (h : IsFinSum Y A) : IsFinSum (T.obj Y) (T.obj A) := by
  induction h with
  | zero hA => exact .zero (T.map_isZero hA)
  | self => exact .self
  | of_iso e _ ih => exact .of_iso (T.mapIso e) ih
  | biprod _ _ ih1 ih2 => exact .of_iso (T.mapBiprod _ _) (.biprod ih1 ih2)

omit [HasFiniteBiproducts C] in
/-- Being a finite sum of copies of `Y` depends only on `Y` up to isomorphism. -/
theorem IsFinSum.congr {Y Y' A : C} (e : Y ≅ Y') (h : IsFinSum Y A) : IsFinSum Y' A := by
  induction h with
  | zero hA => exact .zero hA
  | self => exact .of_iso e .self
  | of_iso e' _ ih => exact .of_iso e' ih
  | biprod _ _ ih1 ih2 => exact .biprod ih1 ih2

omit [HasFiniteBiproducts C] in
/-- If `A` is a finite sum of copies of `Y` and the additive functor `F` kills `Y`, then `F`
kills `A`. -/
theorem IsFinSum.isZero_obj {D : Type*} [Category D] [Preadditive D] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] {Y A : C} (h : IsFinSum Y A) (hY : IsZero (F.obj Y)) :
    IsZero (F.obj A) := by
  induction h with
  | zero hA => exact F.map_isZero hA
  | self => exact hY
  | of_iso e _ ih => exact ih.of_iso (F.mapIso e)
  | biprod _ _ ih1 ih2 =>
    exact ((biprod_isZero_iff _ _).2 ⟨ih1, ih2⟩).of_iso (F.mapBiprod _ _)

section Terms

open homotopyCofiber

omit [HasFiniteBiproducts C] in
/-- The terms of the Koszul complex vanish outside degrees `-m, …, 0`. -/
theorem isZero_kos_X : ∀ (l : List (𝟭 C ⟶ T)) (M : C) (n : ℤ),
    (0 < n ∨ n < -(l.length : ℤ)) → IsZero ((kos T l M).X n)
  | [], M, n, hn => by
    refine HomologicalComplex.isZero_single_obj_X _ _ _ _ ?_
    rcases hn with hn | hn
    · exact hn.ne'
    · simp at hn
      exact hn.ne
  | τ :: l, M, n, hn => by
    refine isZero_X (sigmaHom T τ (kos T l M)) n ?_ ?_
    · refine T.map_isZero (isZero_kos_X l M n ?_)
      rcases hn with hn | hn
      · exact Or.inl hn
      · right
        simp at hn
        omega
    · intro j hj
      have hj' : n + 1 = j := hj
      refine isZero_kos_X l M j ?_
      rcases hn with hn | hn
      · left
        omega
      · right
        simp at hn
        omega

omit [HasFiniteBiproducts C] in
/-- If `F.X j` is zero, then the projection `sndX φ i` from the homotopy cofiber is an
isomorphism. -/
theorem isIso_sndX_of_isZero {ι : Type*} {c : ComplexShape ι} [DecidableRel c.Rel]
    {F G : HomologicalComplex C c} (φ : F ⟶ G) [HasHomotopyCofiber φ] {i j : ι} (hij : c.Rel i j)
    (h : IsZero (F.X j)) : IsIso (sndX φ i) := by
  refine ⟨inrX φ i, ?_, inrX_sndX φ i⟩
  apply ext_to_X φ i j hij
  · exact h.eq_of_tgt _ _
  · simp

omit [HasFiniteBiproducts C] in
/-- If `G.X i` is zero, then the projection `fstX φ i j` from the homotopy cofiber is an
isomorphism. -/
theorem isIso_fstX_of_isZero {ι : Type*} {c : ComplexShape ι} [DecidableRel c.Rel]
    {F G : HomologicalComplex C c} (φ : F ⟶ G) [HasHomotopyCofiber φ] {i j : ι} (hij : c.Rel i j)
    (h : IsZero (G.X i)) : IsIso (fstX φ i j hij) := by
  refine ⟨inlX φ j i hij, ?_, inlX_fstX φ j i hij⟩
  apply ext_to_X φ i j hij
  · simp
  · exact h.eq_of_tgt _ _

omit [HasFiniteBiproducts C] in
/-- The degree-`0` term of `kos T l M` is isomorphic to `T^{length l} M`. -/
theorem nonempty_iso_kos_zero : ∀ (l : List (𝟭 C ⟶ T)) (M : C),
    Nonempty ((kos T l M).X 0 ≅ tpow T l.length M)
  | [], M => ⟨HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M⟩
  | τ :: l, M => by
    have h1 : IsZero ((kos T l M).X (0 + 1)) := isZero_kos_X T l M _ (Or.inl (by omega))
    have hi := isIso_sndX_of_isZero (sigmaHom T τ (kos T l M)) (up_rel 0) h1
    obtain ⟨e⟩ := nonempty_iso_kos_zero l M
    exact ⟨@asIso _ _ _ _ (sndX (sigmaHom T τ (kos T l M)) 0) hi ≪≫ T.mapIso e⟩

omit [HasFiniteBiproducts C] in
/-- The degree-`(-length l)` term of `kos T l M` is isomorphic to `M`. -/
theorem nonempty_iso_kos_last : ∀ (l : List (𝟭 C ⟶ T)) (M : C) (n : ℤ),
    n + l.length = 0 → Nonempty ((kos T l M).X n ≅ M)
  | [], M, n, h => by
    have : n = 0 := by simpa using h
    subst this
    exact ⟨HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M⟩
  | τ :: l, M, n, h => by
    have hz : IsZero (T.obj ((kos T l M).X n)) :=
      T.map_isZero (isZero_kos_X T l M n (Or.inr (by simp at h; omega)))
    have hi := isIso_fstX_of_isZero (sigmaHom T τ (kos T l M)) (up_rel n) hz
    obtain ⟨e⟩ := nonempty_iso_kos_last l M (n + 1) (by simp at h; omega)
    exact ⟨@asIso _ _ _ _ (fstX (sigmaHom T τ (kos T l M)) n (n + 1) (up_rel n)) hi ≪≫ e⟩

omit [HasFiniteBiproducts C] in
/-- The degree-`(-k)` term of `kos T l M` is a finite sum of copies of `T^{length l - k} M`. -/
theorem isFinSum_kos : ∀ (l : List (𝟭 C ⟶ T)) (M : C) (k : ℕ) (n : ℤ), n + k = 0 →
    k ≤ l.length → IsFinSum (tpow T (l.length - k) M) ((kos T l M).X n)
  | [], M, k, n, h, hk => by
    have hk0 : k = 0 := by simpa using hk
    subst hk0
    have : n = 0 := by simpa using h
    subst this
    exact .of_iso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M) .self
  | τ :: l, M, 0, n, h, hk => by
    have hn : n = 0 := by simpa using h
    subst hn
    obtain ⟨e⟩ := nonempty_iso_kos_zero T l M
    have h1 : IsZero ((kos T l M).X (0 + 1)) := isZero_kos_X T l M _ (Or.inl (by omega))
    have hi := isIso_sndX_of_isZero (sigmaHom T τ (kos T l M)) (up_rel 0) h1
    exact .of_iso (@asIso _ _ _ _ (sndX (sigmaHom T τ (kos T l M)) 0) hi ≪≫ T.mapIso e) .self
  | τ :: l, M, k + 1, n, h, hk => by
    have hk' : k ≤ l.length := by simp at hk; omega
    have hr : (ComplexShape.up ℤ).Rel n (n + 1) := up_rel n
    have : HasBinaryBiproduct ((kos T l M).X (n + 1)) (T.obj ((kos T l M).X n)) := inferInstance
    refine .of_iso (homotopyCofiber.XIsoBiprod (sigmaHom T τ (kos T l M)) n (n + 1) hr) ?_
    have e1 : (τ :: l).length - (k + 1) = l.length - k := by simp
    rw [e1]
    refine .biprod (isFinSum_kos l M k (n + 1) (by push_cast at h; omega) hk') ?_
    by_cases hkl : k + 1 ≤ l.length
    · rw [show l.length - k = (l.length - (k + 1)) + 1 by omega]
      exact (isFinSum_kos l M (k + 1) n (by push_cast at h; omega) hkl).map T
    · have hz : IsZero (T.obj ((kos T l M).X n)) :=
        T.map_isZero (isZero_kos_X T l M n (Or.inr (by simp at hk; push_cast at h; omega)))
      exact .zero hz

omit [HasFiniteBiproducts C] in
/-- If `X.X 1` is zero, the differential `(cone T τ X).X (-1) ⟶ (cone T τ X).X 0` is, up to
isomorphisms `X.X 0 ⊞ T (X.X (-1))` and `T (X.X 0)`, the map `biprod.desc (τ (X.X 0)) (T d)`. -/
theorem exists_iso_cone_d_eq_biprod_desc (τ : 𝟭 C ⟶ T) (X : CochainComplex C ℤ)
    (h1 : IsZero (X.X (0 + 1))) :
    ∃ (θ : (cone T τ X).X (-1) ≅ X.X 0 ⊞ T.obj (X.X (-1)))
      (θ₀ : (cone T τ X).X 0 ≅ T.obj (X.X 0)),
      θ.inv ≫ (cone T τ X).d (-1) 0 ≫ θ₀.hom =
        biprod.desc (τ.app (X.X 0)) (T.map (X.d (-1) 0)) := by
  have hr : (ComplexShape.up ℤ).Rel (-1) 0 := by simp [ComplexShape.up]
  have hi := isIso_sndX_of_isZero (sigmaHom T τ X) (up_rel 0) h1
  refine ⟨XIsoBiprod (sigmaHom T τ X) (-1) 0 hr, @asIso _ _ _ _ (sndX (sigmaHom T τ X) 0) hi, ?_⟩
  apply biprod.hom_ext'
  · have e1 : biprod.inl ≫ (XIsoBiprod (sigmaHom T τ X) (-1) 0 hr).inv =
        inlX (sigmaHom T τ X) 0 (-1) hr := inl_XIsoBiprod_inv _ _ _ hr
    erw [← Category.assoc, e1, biprod.inl_desc]
    have := d_sndX (sigmaHom T τ X) (-1) 0 hr
    change inlX (sigmaHom T τ X) 0 (-1) hr ≫ homotopyCofiber.d (sigmaHom T τ X) (-1) 0 ≫
      sndX (sigmaHom T τ X) 0 = _
    rw [this]
    simp only [Preadditive.comp_add, inlX_fstX_assoc, inlX_sndX_assoc, zero_comp, add_zero]
    rfl
  · have e1 : biprod.inr ≫ (XIsoBiprod (sigmaHom T τ X) (-1) 0 hr).inv =
        inrX (sigmaHom T τ X) (-1) := inr_XIsoBiprod_inv _ _ _ hr
    erw [← Category.assoc, e1, biprod.inr_desc]
    have := d_sndX (sigmaHom T τ X) (-1) 0 hr
    change inrX (sigmaHom T τ X) (-1) ≫ homotopyCofiber.d (sigmaHom T τ X) (-1) 0 ≫
      sndX (sigmaHom T τ X) 0 = _
    rw [this]
    simp

/-- The object `B` with `(kos l M).X (-1) ≅ B` that is built by recursion alongside the cone
construction. -/
noncomputable def kosB : List (𝟭 C ⟶ T) → C → C
  | [], M => (kos T [] M).X (-1)
  | _ :: l, M => tpow T l.length M ⊞ T.obj (kosB l M)

/-- The transported differential `(kos l M).X (-1) ⟶ (kos l M).X 0`. -/
noncomputable def kosD : (l : List (𝟭 C ⟶ T)) → (M : C) → (kosB T l M ⟶ tpow T l.length M)
  | [], M => (kos T [] M).d (-1) 0 ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).hom
  | τ :: l, M => biprod.desc (τ.app (tpow T l.length M)) (T.map (kosD l M))

omit [HasFiniteBiproducts C] in
/-- The differential `(kos T l M).X (-1) ⟶ (kos T l M).X 0` is `kosD T l M` up to isomorphisms
with `kosB T l M` and `T^{length l} M`. -/
theorem exists_iso_kos_d_eq_kosD : ∀ (l : List (𝟭 C ⟶ T)) (M : C),
    ∃ (εB : (kos T l M).X (-1) ≅ kosB T l M) (ε₀ : (kos T l M).X 0 ≅ tpow T l.length M),
      εB.inv ≫ (kos T l M).d (-1) 0 ≫ ε₀.hom = kosD T l M
  | [], M => ⟨Iso.refl _, HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M, by
      exact Category.id_comp _⟩
  | τ :: l, M => by
    obtain ⟨εB, ε₀, hε⟩ := exists_iso_kos_d_eq_kosD l M
    have h1 : IsZero ((kos T l M).X (0 + 1)) := isZero_kos_X T l M _ (Or.inl (by omega))
    obtain ⟨θ, θ₀, hθ⟩ := exists_iso_cone_d_eq_biprod_desc T τ (kos T l M) h1
    refine ⟨θ ≪≫ biprod.mapIso ε₀ (T.mapIso εB), θ₀ ≪≫ T.mapIso ε₀, ?_⟩
    change (θ ≪≫ biprod.mapIso ε₀ (T.mapIso εB)).inv ≫ (cone T τ (kos T l M)).d (-1) 0 ≫
      (θ₀ ≪≫ T.mapIso ε₀).hom = _
    simp only [Iso.trans_inv, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
    rw [reassoc_of% hθ]
    apply biprod.hom_ext'
    · simp only [biprod.mapIso_inv, biprod.inl_map_assoc, biprod.inl_desc_assoc, kosD]
      have := τ.naturality ε₀.inv
      change ε₀.inv ≫ τ.app _ = τ.app _ ≫ T.map ε₀.inv at this
      rw [reassoc_of% this, ← T.map_comp, Iso.inv_hom_id, T.map_id, Category.comp_id]
      exact (biprod.inl_desc _ _).symm
    · simp only [biprod.mapIso_inv, biprod.inr_map_assoc, biprod.inr_desc_assoc, kosD,
        Functor.mapIso_inv]
      rw [← hε]
      simp only [Functor.map_comp]
      exact (biprod.inr_desc _ _).symm

/-- An additive functor to abelian groups sends `biprod.desc f g` to the sum of `f` applied to the
first component and `g` applied to the second. -/
theorem map_biprod_desc_apply {D : Type*} [Category D] [Preadditive D] [HasBinaryBiproducts D]
    (F : D ⥤ AddCommGrpCat.{w}) [F.Additive] {P B Q : D} (f : P ⟶ Q) (g : B ⟶ Q)
    (u : F.obj (P ⊞ B)) :
    ConcreteCategory.hom (F.map (biprod.desc f g)) u =
      ConcreteCategory.hom (F.map f) (ConcreteCategory.hom (F.map biprod.fst) u) +
        ConcreteCategory.hom (F.map g) (ConcreteCategory.hom (F.map biprod.snd) u) := by
  rw [biprod.desc_eq, F.map_add, F.map_comp, F.map_comp]
  rfl

omit [HasFiniteBiproducts C] in
/-- Every element of the image of `kosD` under an additive functor to abelian groups lies in the
subgroup generated by the images of the operators `τ` of the list. -/
theorem map_kosD_apply_mem_closure : ∀ (L : List (𝟭 C ⟶ T)) (τ' : 𝟭 C ⟶ T) (M : C)
    (F : C ⥤ AddCommGrpCat.{w}) [F.Additive], CommList T (τ' :: L) →
    ∀ u : F.obj (kosB T (τ' :: L) M),
    ConcreteCategory.hom (F.map (kosD T (τ' :: L) M)) u ∈ AddSubgroup.closure
      {x : F.obj (tpow T (L.length + 1) M) | ∃ τ ∈ τ' :: L, ∃ y : F.obj (tpow T L.length M),
        x = ConcreteCategory.hom (F.map (τ.app (tpow T L.length M))) y}
  | [], τ', M, F, _, hl, u => by
    have key : ConcreteCategory.hom (F.map (kosD T (τ' :: []) M)) u =
        ConcreteCategory.hom (F.map (τ'.app (tpow T [].length M)))
          (ConcreteCategory.hom (F.map biprod.fst) u) +
        ConcreteCategory.hom (F.map (T.map (kosD T [] M)))
          (ConcreteCategory.hom (F.map biprod.snd) u) := map_biprod_desc_apply F _ _ u
    rw [key]
    refine AddSubgroup.add_mem _ (AddSubgroup.subset_closure ⟨τ', List.mem_cons_self, _, rfl⟩) ?_
    have hd : (kos T [] M).d (-1) 0 = 0 := by simp [kos]; rfl
    have : kosD T [] M = 0 := by
      unfold kosD
      rw [hd]
      exact zero_comp
    rw [this, T.map_zero, F.map_zero]
    exact AddSubgroup.zero_mem _
  | τ₂ :: L₂, τ', M, F, _, hl, u => by
    have key : ConcreteCategory.hom (F.map (kosD T (τ' :: τ₂ :: L₂) M)) u =
        ConcreteCategory.hom (F.map (τ'.app (tpow T (τ₂ :: L₂).length M)))
          (ConcreteCategory.hom (F.map biprod.fst) u) +
        ConcreteCategory.hom (F.map (T.map (kosD T (τ₂ :: L₂) M)))
          (ConcreteCategory.hom (F.map biprod.snd) u) := map_biprod_desc_apply F _ _ u
    rw [key]
    refine AddSubgroup.add_mem _ (AddSubgroup.subset_closure ⟨τ', List.mem_cons_self, _, rfl⟩) ?_
    have hl' : CommList T (τ₂ :: L₂) := fun τ hτ => hl τ (List.mem_cons_of_mem _ hτ)
    have ih := map_kosD_apply_mem_closure L₂ τ₂ M (T ⋙ F) hl'
      (ConcreteCategory.hom (F.map biprod.snd) u)
    refine AddSubgroup.closure_mono ?_ ih
    rintro x ⟨τ, hτ, y, rfl⟩
    refine ⟨τ, List.mem_cons_of_mem _ hτ, y, ?_⟩
    have := hl τ (List.mem_cons_of_mem _ hτ) (tpow T L₂.length M)
    change _ = ConcreteCategory.hom (F.map (τ.app (T.obj (tpow T L₂.length M)))) y
    rw [this]
    rfl

end Terms

section Chain

omit [HasFiniteBiproducts C] in
/-- For an epimorphism `f`, the short complex `0 ⟶ ker f ⟶ A ⟶ B ⟶ 0` is short exact. -/
theorem shortExact_kernelSequence {A B : C} (f : A ⟶ B) [Epi f] :
    (ShortComplex.kernelSequence f).ShortExact where
  exact := ShortComplex.kernelSequence_exact f
  mono_f := inferInstanceAs (Mono (kernel.ι f))
  epi_g := inferInstanceAs (Epi f)

/-- `0 ⟶ ker f ⟶ A ⟶ ker g` for `f ≫ g = 0`. -/
noncomputable def kerLiftSC {A B Q : C} (f : A ⟶ B) (g : B ⟶ Q) (w : f ≫ g = 0) : ShortComplex C :=
  ShortComplex.mk (kernel.ι f) (kernel.lift g f w)
    ((cancel_mono (kernel.ι g)).1 (by simp))

omit [HasFiniteBiproducts C] in
/-- If `A ⟶ B ⟶ Q` is exact, then `0 ⟶ ker f ⟶ A ⟶ ker g ⟶ 0` is short exact. -/
theorem shortExact_kerLiftSC {A B Q : C} (f : A ⟶ B) (g : B ⟶ Q) (w : f ≫ g = 0)
    (hex : (ShortComplex.mk f g w).Exact) : (kerLiftSC f g w).ShortExact where
  exact := by
    let φ : kerLiftSC f g w ⟶ ShortComplex.kernelSequence f :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := kernel.ι g
        comm₁₂ := by simp [kerLiftSC, ShortComplex.kernelSequence]
        comm₂₃ := by simp [kerLiftSC, ShortComplex.kernelSequence] }
    have h1 : Epi φ.τ₁ := inferInstanceAs (Epi (𝟙 _))
    have h2 : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 _))
    have h3 : Mono φ.τ₃ := inferInstanceAs (Mono (kernel.ι g))
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 (ShortComplex.kernelSequence_exact f)
  mono_f := inferInstanceAs (Mono (kernel.ι f))
  epi_g := (ShortComplex.exact_iff_epi_kernel_lift (ShortComplex.mk f g w)).1 hex

/-- The cycle objects `Z_k = ker (d^{-k})` of a cochain complex, `Z_0 = K^0`. -/
noncomputable def kosZ (K : CochainComplex C ℤ) : ℕ → C
  | 0 => K.X (-((0 : ℕ) : ℤ))
  | k + 1 => kernel (K.d (-((k + 1 : ℕ) : ℤ)) (-(k : ℤ)))

/-- The short complexes `0 ⟶ Z_{k+1} ⟶ K^{-(k+1)} ⟶ Z_k ⟶ 0`. -/
noncomputable def kosS (K : CochainComplex C ℤ) : ℕ → ShortComplex C
  | 0 => ShortComplex.kernelSequence (K.d (-((1 : ℕ) : ℤ)) (-((0 : ℕ) : ℤ)))
  | k + 1 => kerLiftSC (K.d (-((k + 2 : ℕ) : ℤ)) (-((k + 1 : ℕ) : ℤ)))
      (K.d (-((k + 1 : ℕ) : ℤ)) (-(k : ℤ))) (K.d_comp_d _ _ _)

/-- For commuting generating operators `τ :: L`, the Koszul complex `kos T (τ :: L) M` splits
into short exact sequences `S k` with kernels `Z (k + 1)`, cokernels `Z k`, middle terms finite
sums of copies of `T^{length L - k} M`, last kernel `Z (length L) ≅ M`, and with the image of
`(S 0).g` under any additive functor to abelian groups contained in the subgroup generated by the
images of the operators. -/
theorem exists_koszul_chain [T.Faithful] [T.PreservesMonomorphisms] (τ : 𝟭 C ⟶ T)
    (L : List (𝟭 C ⟶ T)) (hL : 1 ≤ L.length) (M : C) (hl : CommList T (τ :: L))
    (hgen : ∀ X : C, Epi (biproduct.desc fun i : Fin (τ :: L).length => ((τ :: L).get i).app X :
      (⨁ fun _ : Fin (τ :: L).length => X) ⟶ T.obj X)) :
    ∃ (Z : ℕ → C) (S : ℕ → ShortComplex C),
      (∀ k, k < L.length → (S k).ShortExact) ∧
      (∀ k, k < L.length → Nonempty ((S k).X₁ ≅ Z (k + 1))) ∧
      (∀ k, 1 ≤ k → k < L.length → Nonempty ((S k).X₃ ≅ Z k)) ∧
      (∀ k, 1 ≤ k → k < L.length → IsFinSum (tpow T (L.length - k) M) (S k).X₂) ∧
      Nonempty (Z L.length ≅ M) ∧
      ∃ e₃ : (S 0).X₃ ≅ tpow T (L.length + 1) M,
        ∀ (F : C ⥤ AddCommGrpCat.{w}) [F.Additive] (u : F.obj (S 0).X₂),
          ConcreteCategory.hom (F.map ((S 0).g ≫ e₃.hom)) u ∈ AddSubgroup.closure
            {x : F.obj (tpow T (L.length + 1) M) | ∃ τ' ∈ τ :: L,
              ∃ y : F.obj (tpow T L.length M),
                x = ConcreteCategory.hom (F.map (τ'.app (tpow T L.length M))) y} := by
  set K := kos T (τ :: L) M with hK
  have hac : ∀ {a b c : ℤ}, (ComplexShape.up ℤ).Rel a b → (ComplexShape.up ℤ).Rel b c →
      (K.sc' a b c).Exact := fun {a b c} hab hbc =>
    (ShortComplex.exact_iff_isZero_homology _).2
      (isZero_homology_kos T (τ :: L) M hl hgen hbc hab)
  have hz : ∀ n : ℤ, (0 < n ∨ n < -((τ :: L).length : ℤ)) → IsZero (K.X n) :=
    fun n hn => isZero_kos_X T (τ :: L) M n hn
  have hrel : ∀ k : ℕ, (ComplexShape.up ℤ).Rel (-((k + 1 : ℕ) : ℤ)) (-(k : ℤ)) := fun k => by
    simp [ComplexShape.up]
  have hrel0 : (ComplexShape.up ℤ).Rel (-((0 : ℕ) : ℤ)) 1 := by simp [ComplexShape.up]
  refine ⟨kosZ K, kosS K, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    cases k with
    | zero =>
      have hex := hac (hrel 0) hrel0
      have hg : (K.sc' (-((0 + 1 : ℕ) : ℤ)) (-((0 : ℕ) : ℤ)) 1).g = 0 :=
        (hz 1 (Or.inl one_pos)).eq_of_tgt _ _
      have : Epi (K.d (-((1 : ℕ) : ℤ)) (-((0 : ℕ) : ℤ))) :=
        (ShortComplex.exact_iff_epi _ hg).1 hex
      exact shortExact_kernelSequence _
    | succ k =>
      exact shortExact_kerLiftSC _ _ _ (hac (hrel (k + 1)) (hrel k))
  · intro k hk
    cases k <;> exact ⟨Iso.refl _⟩
  · intro k hk1 hk
    cases k with
    | zero => omega
    | succ k => exact ⟨Iso.refl _⟩
  · intro k hk1 hk
    cases k with
    | zero => omega
    | succ k =>
      have := isFinSum_kos T (τ :: L) M (k + 2) (-((k + 2 : ℕ) : ℤ)) (by simp)
        (by simp; omega)
      have e : (τ :: L).length - (k + 2) = L.length - (k + 1) := by simp
      rwa [e] at this
  · obtain ⟨n, hn⟩ : ∃ n, L.length = n + 1 := ⟨L.length - 1, by omega⟩
    rw [hn]
    have hr1 : (ComplexShape.up ℤ).Rel (-((n + 2 : ℕ) : ℤ)) (-((n + 1 : ℕ) : ℤ)) := hrel (n + 1)
    have hr0 : (ComplexShape.up ℤ).Rel (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) := hrel n
    have hr2 : (ComplexShape.up ℤ).Rel (-((n + 3 : ℕ) : ℤ)) (-((n + 2 : ℕ) : ℤ)) := hrel (n + 2)
    have hexE := hac hr1 hr0
    have hexM := hac hr2 hr1
    have hf0 : (K.sc' (-((n + 3 : ℕ) : ℤ)) (-((n + 2 : ℕ) : ℤ)) (-((n + 1 : ℕ) : ℤ))).f = 0 :=
      (hz _ (Or.inr (by simp [hn]; omega))).eq_of_src _ _
    have hmono : Mono (K.d (-((n + 2 : ℕ) : ℤ)) (-((n + 1 : ℕ) : ℤ))) :=
      (ShortComplex.exact_iff_mono _ hf0).1 hexM
    have hepi : Epi (kernel.lift (K.d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)))
        (K.d (-((n + 2 : ℕ) : ℤ)) (-((n + 1 : ℕ) : ℤ))) (K.d_comp_d _ _ _)) :=
      (ShortComplex.exact_iff_epi_kernel_lift _).1 hexE
    have hmono' : Mono (kernel.lift (K.d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)))
        (K.d (-((n + 2 : ℕ) : ℤ)) (-((n + 1 : ℕ) : ℤ))) (K.d_comp_d _ _ _)) :=
      mono_of_mono_fac (kernel.lift_ι _ _ _)
    obtain ⟨e⟩ := nonempty_iso_kos_last T (τ :: L) M (-((n + 2 : ℕ) : ℤ))
      (by simp [hn]; omega)
    have hiso : IsIso (kernel.lift (K.d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)))
        (K.d (-((n + 2 : ℕ) : ℤ)) (-((n + 1 : ℕ) : ℤ))) (K.d_comp_d _ _ _)) :=
      isIso_of_mono_of_epi _
    exact ⟨(@asIso _ _ _ _ (kernel.lift (K.d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)))
      (K.d (-((n + 2 : ℕ) : ℤ)) (-((n + 1 : ℕ) : ℤ))) (K.d_comp_d _ _ _)) hiso).symm ≪≫ e⟩
  · obtain ⟨εB, ε₀, hε⟩ := exists_iso_kos_d_eq_kosD T (τ :: L) M
    refine ⟨ε₀, ?_⟩
    intro F _ u
    have h1 := (Iso.inv_comp_eq εB).1 hε
    have h2 : (kosS K 0).g ≫ ε₀.hom = εB.hom ≫ kosD T (τ :: L) M := h1
    rw [h2]
    have e : F.map (εB.hom ≫ kosD T (τ :: L) M) = F.map εB.hom ≫ F.map (kosD T (τ :: L) M) :=
      F.map_comp _ _
    erw [e]
    exact map_kosD_apply_mem_closure T L τ M F hl _

omit [T.Additive] in
/-- Generation by a family `f : Fin n → (𝟭 C ⟶ T)` transfers to generation by the list
`List.ofFn f`. -/
theorem epi_desc_get_of_ofFn {n : ℕ} (f : Fin n → (𝟭 C ⟶ T)) (l : List (𝟭 C ⟶ T))
    (hl : l = List.ofFn f)
    (hf : ∀ X : C, Epi (biproduct.desc fun i : Fin n => (f i).app X :
      (⨁ fun _ : Fin n => X) ⟶ T.obj X)) :
    ∀ X : C, Epi (biproduct.desc fun i : Fin l.length => (l.get i).app X :
      (⨁ fun _ : Fin l.length => X) ⟶ T.obj X) := by
  subst hl
  intro X
  have hlen : (List.ofFn f).length = n := List.length_ofFn
  have key : ∀ (m : ℕ) (h : m = n) (g : Fin m → (𝟭 C ⟶ T)) (hg : ∀ i, g i = f (Fin.cast h i)),
      Epi (biproduct.desc fun i : Fin m => (g i).app X :
        (⨁ fun _ : Fin m => X) ⟶ T.obj X) := by
    intro m h
    subst h
    intro g hg
    have : g = f := funext hg
    subst this
    exact hf X
  exact key _ hlen (fun i => (List.ofFn f).get i) fun i => by simp; rfl

end Chain

end

end KoszulAbs

/-! ### Mumford's descent over an arbitrary ring -/

variable {R : Type u} [CommRing R] (n : ℕ)

/-- The additive subgroup of `H⁰(ℙⁿ_R, ℱ(d+1))` generated by the products `s · a` of a global
section `s` of `𝒪(1)` with a global section `a` of `ℱ(d)`. -/
def mulSectionsClosure (F : (projectiveSpaceOverRing n (.of R)).Modules) (d : ℤ) :
    AddSubgroup Γ(projectiveTwist n F (d + 1), ⊤) :=
  AddSubgroup.closure
    {t | ∃ (s : (twistOver n (Spec (.of R)) 1).sections) (a : Γ(projectiveTwist n F d, ⊤)),
      t = Scheme.Modules.Hom.app (twistSectionMul n (Spec (.of R)) F s d) ⊤ a}

/-- The map to `ℱ(m)` from the free module on all of its global sections; global generation of
`ℱ(m)` is that this map is an epimorphism. -/
def projectiveTwistFreeSectionsHom (F : (projectiveSpaceOverRing n (.of R)).Modules) (m : ℤ) :
    SheafOfModules.free (projectiveTwist n F m).sections ⟶ projectiveTwist n F m :=
  (projectiveTwist n F m).freeHomEquiv.symm id

/-- The twist by one of `MMP.Fourfold.projectiveTwistFreeSectionsHom`, followed by the comparison
`(ℱ(m)) ⊗ 𝒪(1) ≅ ℱ(m + 1)`. -/
def projectiveTwistFreeSectionsHomSucc (F : (projectiveSpaceOverRing n (.of R)).Modules) (m : ℤ) :
    projectiveTwist n (SheafOfModules.free (projectiveTwist n F m).sections) 1 ⟶
      projectiveTwist n F (m + 1) :=
  (Stacks.AlgebraicGeometry.ProjTwistFunctor.projectiveTwistFunctor n 1).map
      (projectiveTwistFreeSectionsHom n F m) ≫
    (twistAssocIso n (Spec (.of R)) F m).hom

/-- Multiplication by a linear form on `ℱ(m)` factors through the twisted map from the free
module. -/
theorem projectiveTwistFreeSectionsHom_comp_twistSectionMul
    (F : (projectiveSpaceOverRing n (.of R)).Modules) (m : ℤ)
    (s : (twistOver n (Spec (.of R)) 1).sections) :
    projectiveTwistFreeSectionsHom n F m ≫ twistSectionMul n (Spec (.of R)) F s m
      = mulSectionOne n (Spec (.of R))
            (SheafOfModules.free (projectiveTwist n F m).sections) s ≫
        projectiveTwistFreeSectionsHomSucc n F m :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun g => g ≫ (twistAssocIso n (Spec (.of R)) F m).hom)
        (mulSectionOne_naturality n (Spec (.of R)) (projectiveTwistFreeSectionsHom n F m) s)).trans
      (Category.assoc _ _ _))

/-- If the products of global sections of `ℱ(m)` with linear forms generate `H⁰(ℱ(m + 1))`, then
`MMP.Fourfold.projectiveTwistFreeSectionsHomSucc` is onto sections over `⊤`. -/
theorem surjective_app_top_projectiveTwistFreeSectionsHomSucc
    (F : (projectiveSpaceOverRing n (.of R)).Modules) (m : ℤ)
    (hspan : mulSectionsClosure n F m = ⊤) :
    Function.Surjective (Scheme.Modules.Hom.app (projectiveTwistFreeSectionsHomSucc n F m) ⊤) := by
  have hpi :
      Function.Surjective (Scheme.Modules.Hom.app (projectiveTwistFreeSectionsHom n F m) ⊤) :=
    surjective_app_top_of_surjective_sectionsMap _ (fun t =>
      ⟨SheafOfModules.freeSection t,
        SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
          (M := projectiveTwist n F m) id t⟩)
  let φ := Scheme.Modules.Hom.app (projectiveTwistFreeSectionsHomSucc n F m) ⊤
  have hle : mulSectionsClosure n F m ≤ φ.hom.range := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro x ⟨s, a, rfl⟩
    obtain ⟨b, rfl⟩ := hpi a
    refine ⟨Scheme.Modules.Hom.app (mulSectionOne n (Spec (.of R))
      (SheafOfModules.free (projectiveTwist n F m).sections) s) ⊤ b, ?_⟩
    have h := congrArg (fun g => Scheme.Modules.Hom.app g ⊤ b)
      (projectiveTwistFreeSectionsHom_comp_twistSectionMul n F m s)
    exact h.symm
  intro x
  have hx : x ∈ φ.hom.range := hle (hspan ▸ AddSubgroup.mem_top x)
  exact hx

/-- **One step of Mumford's descent, over an arbitrary ring.** If `ℱ(m + 1)` is globally generated
and the products of global sections of `ℱ(m)` with linear forms generate `H⁰(ℙⁿ_R, ℱ(m + 1))`,
then `ℱ(m)` is globally generated. -/
theorem isGeneratedByGlobalSections_projectiveTwist_of_mulSectionsClosure
    (F : (projectiveSpaceOverRing n (.of R)).Modules) (m : ℤ)
    (hgg : SheafOfModules.IsGeneratedByGlobalSections (projectiveTwist n F (m + 1)))
    (hspan : mulSectionsClosure n F m = ⊤) :
    SheafOfModules.IsGeneratedByGlobalSections (projectiveTwist n F m) := by
  have hepi : Epi (projectiveTwistFreeSectionsHomSucc n F m) :=
    epi_of_isGeneratedByGlobalSections_of_surjective _ hgg
      (surjective_sectionsMap_of_surjective_app_top _
        (surjective_app_top_projectiveTwistFreeSectionsHomSucc n F m hspan))
  have htwist : Epi ((Stacks.AlgebraicGeometry.ProjTwistFunctor.projectiveTwistFunctor n 1).map
      (projectiveTwistFreeSectionsHom n F m)) := by
    have hfac : (Stacks.AlgebraicGeometry.ProjTwistFunctor.projectiveTwistFunctor n 1).map
        (projectiveTwistFreeSectionsHom n F m)
        = projectiveTwistFreeSectionsHomSucc n F m ≫ (twistAssocIso n (Spec (.of R)) F m).inv :=
      (Iso.eq_comp_inv _).mpr rfl
    rw [hfac]
    exact @epi_comp _ _ _ _ _ _ hepi (twistAssocIso n (Spec (.of R)) F m).inv inferInstance
  have hπ : Epi (projectiveTwistFreeSectionsHom n F m) :=
    epi_of_epi_projectiveTwistFunctor_map n 1 _ htwist
  exact ⟨⟨(projectiveTwist n F m).sections, id, hπ⟩⟩

/-- **Mumford's descent over an arbitrary ring.** For a coherent `ℱ` on `ℙⁿ_R`, if for every
`d ≥ m` the products of global sections of `ℱ(d)` with linear forms generate
`H⁰(ℙⁿ_R, ℱ(d + 1))`, then `ℱ(m)` is globally generated. The descent starts at a twist that is
globally generated by Serre's theorem,
`Stacks.ProjectiveSpace.exists_isGeneratedByGlobalSections_projectiveTwist_of_isCoherent`. -/
theorem isGeneratedByGlobalSections_projectiveTwist_of_forall_mulSectionsClosure
    (F : (projectiveSpaceOverRing n (.of R)).Modules) [F.IsCoherent] (m : ℤ)
    (hspan : ∀ d : ℤ, m ≤ d → mulSectionsClosure n F d = ⊤) :
    SheafOfModules.IsGeneratedByGlobalSections (projectiveTwist n F m) := by
  obtain ⟨d₀, hd₀⟩ :=
    Stacks.ProjectiveSpace.exists_isGeneratedByGlobalSections_projectiveTwist_of_isCoherent n F
      inferInstance
  set M := max m d₀
  have key : ∀ j : ℕ, m ≤ M - j →
      SheafOfModules.IsGeneratedByGlobalSections (projectiveTwist n F (M - j)) := by
    intro j
    induction j with
    | zero =>
      intro _
      simpa using hd₀ M (le_max_right _ _)
    | succ j ih =>
      intro hj
      have h1 := ih (by push_cast at hj; omega)
      have he : M - ((j + 1 : ℕ) : ℤ) + 1 = M - j := by push_cast; ring
      exact isGeneratedByGlobalSections_projectiveTwist_of_mulSectionsClosure n F _
        (he ▸ h1) (hspan _ hj)
  have hM : m ≤ M := le_max_left _ _
  have := key (M - m).toNat (by omega)
  rwa [show M - ((M - m).toNat : ℤ) = m by omega] at this

/-! ### Grothendieck vanishing, and the regularity theorem on `ℙⁿ_R` -/

open Stacks.Cohomology.ModuleComparison
  (isZero_rightDerivedSections_iff_isZero_cohomologyPresheaf)
open Stacks.Cohomology.TerminalCohomology (subsingleton_H_iff_subsingleton_H'_top)
open Stacks.CohomologyVanishing (subsingleton_sheafCohomology_of_noetherianSpace_of_dim_le)

/-- **Grothendieck's vanishing theorem** ([Stacks, Tag 02UZ]) on a Noetherian scheme of dimension
at most `d`, for the cohomology `Hgroup X.ringCatSheaf ⊤ i` of an `𝒪_X`-module: it vanishes in
every degree `i > d`. -/
theorem isZero_Hgroup_of_topologicalKrullDim_le {X : Scheme.{u}} [IsNoetherian X]
    (F : X.Modules) {d i : ℕ} (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (hi : d < i) :
    IsZero (Hgroup X.ringCatSheaf ⊤ i F) := by
  refine (isZero_rightDerivedSections_iff_isZero_cohomologyPresheaf
    (J := Opens.grothendieckTopology (X : Type u)) (R := X.ringCatSheaf)
    (U := (⊤ : Opens (X : Type u))) (n := i) (F := F)).mpr ?_
  have hsub := (subsingleton_H_iff_subsingleton_H'_top
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) i).mp
    (subsingleton_sheafCohomology_of_noetherianSpace_of_dim_le (d := d) hdim hi _)
  exact @AddCommGrpCat.isZero_of_subsingleton _ hsub

/-- **The multiplication theorem on `ℙ⁰_R`.** There `𝒪(1)` is trivial and multiplication by its
generating section is an isomorphism `ℱ(d) ≅ ℱ(d + 1)`, so no regularity is needed. -/
theorem mulSectionsClosure_zero_eq_top (F : (projectiveSpaceOverRing 0 (.of R)).Modules)
    (d : ℤ) : mulSectionsClosure 0 F d = ⊤ := by
  set s := generatingSectionZero (Spec (.of R))
  have hiso : IsIso (twistSectionMul 0 (Spec (.of R)) F s d) :=
    isIso_twistSectionMul_zero (Spec (.of R)) F d
  refine eq_top_iff.2 fun t _ => AddSubgroup.subset_closure ⟨s,
    Scheme.Modules.Hom.app (inv (twistSectionMul 0 (Spec (.of R)) F s d)) ⊤ t, ?_⟩
  change t = Scheme.Modules.Hom.app (inv (twistSectionMul 0 (Spec (.of R)) F s d) ≫
    twistSectionMul 0 (Spec (.of R)) F s d) ⊤ t
  rw [IsIso.inv_hom_id]
  rfl

/-! ### The cohomological chase of the Koszul argument -/

attribute [local instance] HasDerivedCategory.standard

/-- **A short exact sequence with `H¹(ℱ₁) = 0` is exact on global sections.** If
`0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` is short exact on a scheme `X` and `H¹(X, ℱ₁) = 0`, then
`H⁰(X, ℱ₂) ⟶ H⁰(X, ℱ₃)` is onto. -/
theorem surjective_secF_map_of_shortExact {X : Scheme.{u}}
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (h1 : IsZero (Hgroup X.ringCatSheaf ⊤ 1 S.X₁)) :
    Function.Surjective (ConcreteCategory.hom ((secF X.ringCatSheaf ⊤).map S.g)) := by
  let D := Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (secF X.ringCatSheaf ⊤)
  have hex := D.scδ₁_exact hS 0
  have hg : (D.scδ₁ hS 0).g = 0 := h1.eq_of_tgt _ _
  have hepi : Epi (D.scδ₁ hS 0).f := (ShortComplex.exact_iff_epi _ hg).mp hex
  have hsurj : Function.Surjective (ConcreteCategory.hom ((Hfunctor X.ringCatSheaf ⊤ 0).map S.g)) :=
    (AddCommGrpCat.epi_iff_surjective _).mp hepi
  intro y
  obtain ⟨z, hz⟩ := (bijective_Hzero X.ringCatSheaf ⊤ S.X₃).2 y
  obtain ⟨x, hx⟩ := hsurj z
  refine ⟨ConcreteCategory.hom ((HzeroIso X.ringCatSheaf ⊤).hom.app S.X₂) x, ?_⟩
  exact (Hzero_map X.ringCatSheaf ⊤ S.g x).symm.trans (by rwa [hx])

/-- **The cohomological chase of the Koszul argument.** Let `Z₀, Z₁, …` be modules and `S k`
(`k < N`) short exact sequences `0 ⟶ (S k).X₁ ⟶ (S k).X₂ ⟶ (S k).X₃ ⟶ 0` with
`(S k).X₁ ≅ Z (k + 1)` and `(S k).X₃ ≅ Z k` for `k ≥ 1`. If `Hᵏ((S k).X₂) = 0` for
`1 ≤ k < N` and `Hᴺ(Z N) = 0`, then `Hᵏ(Z k) = 0` for `1 ≤ k ≤ N`. -/
theorem isZero_Hgroup_of_chain {X : Scheme.{u}} (N : ℕ) (Z : ℕ → X.Modules)
    (S : ℕ → ShortComplex X.Modules) (hS : ∀ k, k < N → (S k).ShortExact)
    (h1 : ∀ k, k < N → Nonempty ((S k).X₁ ≅ Z (k + 1)))
    (h3 : ∀ k, 1 ≤ k → k < N → Nonempty ((S k).X₃ ≅ Z k))
    (hT : ∀ k, 1 ≤ k → k < N → IsZero (Hgroup X.ringCatSheaf ⊤ k (S k).X₂))
    (hN : IsZero (Hgroup X.ringCatSheaf ⊤ N (Z N))) :
    ∀ k, 1 ≤ k → k ≤ N → IsZero (Hgroup X.ringCatSheaf ⊤ k (Z k)) := by
  let D := Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (secF X.ringCatSheaf ⊤)
  have key : ∀ m k : ℕ, k + m = N → 1 ≤ k → IsZero (Hgroup X.ringCatSheaf ⊤ k (Z k)) := by
    intro m
    induction m with
    | zero =>
      intro k hk _
      obtain rfl : k = N := by omega
      exact hN
    | succ m ih =>
      intro k hk hk1
      have hnext := ih (k + 1) (by omega) (by omega)
      have hkN : k < N := by omega
      have hleft : IsZero ((D.functor k).obj (S k).X₂) := hT k hk1 hkN
      obtain ⟨e1⟩ := h1 k hkN
      obtain ⟨e3⟩ := h3 k hk1 hkN
      have hright : IsZero ((D.functor (k + 1)).obj (S k).X₁) :=
        hnext.of_iso ((D.functor (k + 1)).mapIso e1)
      have h := (D.scδ₁_exact (hS k hkN) k).isZero_of_both_isZero hleft hright
      exact h.of_iso ((D.functor k).mapIso e3.symm)
  intro k hk1 hkN
  exact key (N - k) k (by omega) hk1

/-- Finite biproducts exist in the category of `𝒪_X`-modules of a scheme (it has finite
products, and it is preadditive). -/
theorem hasFiniteBiproducts_modules (X : Scheme.{u}) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- Finite biproducts exist in `SheafOfModules X.ringCatSheaf`, the category of `𝒪_X`-modules
of a scheme. -/
theorem hasFiniteBiproducts_sheafOfModules (X : Scheme.{u}) :
    HasFiniteBiproducts (SheafOfModules.{u} X.ringCatSheaf) :=
  hasFiniteBiproducts_modules X

attribute [local instance] hasFiniteBiproducts_modules hasFiniteBiproducts_sheafOfModules

/-- **A twisted Koszul chain for `𝒢` at `d`.** On `ℙᴺ_A` (with `N ≥ 1`), the twisted Koszul complex
of the coordinates
`0 ⟶ 𝒢(d - N) ⟶ ⋯ ⟶ 𝒢(d - 1)^{⊕ C(N+1, 2)} ⟶ 𝒢(d)^{⊕ (N+1)} ⟶ 𝒢(d + 1) ⟶ 0`
is exact, and here it is recorded split into short exact sequences `S k`, `k < N`,
`0 ⟶ Z (k+1) ⟶ T_k ⟶ Z k ⟶ 0` whose middle terms `T_k` (`1 ≤ k`) are finite sums of copies of
`𝒢(d - k)`, the last cycle module being `𝒢(d - N)`; the first sequence ends in `𝒢(d + 1)`, and
every global section of the middle term `T_0 = 𝒢(d)^{⊕ (N+1)}` goes, under the first map, to a sum
of products of global sections of `𝒢(d)` with global sections of `𝒪(1)`. -/
def HasTwistedKoszulChain (A : Type u) [CommRing A] (N : ℕ)
    (G : (projectiveSpaceOverRing N (.of A)).Modules) (d : ℤ) : Prop :=
  1 ≤ N → ∃ (Z : ℕ → (projectiveSpaceOverRing N (.of A)).Modules)
    (S : ℕ → ShortComplex (projectiveSpaceOverRing N (.of A)).Modules),
    (∀ k, k < N → (S k).ShortExact) ∧ (∀ k, k < N → Nonempty ((S k).X₁ ≅ Z (k + 1))) ∧
    (∀ k, 1 ≤ k → k < N → Nonempty ((S k).X₃ ≅ Z k)) ∧
    (∀ k : ℕ, 1 ≤ k → k < N → KoszulAbs.IsFinSum (projectiveTwist N G (d - k)) (S k).X₂) ∧
    Nonempty (Z N ≅ projectiveTwist N G (d - N)) ∧
    ∃ e₃ : (S 0).X₃ ≅ projectiveTwist N G (d + 1),
      ∀ u : (secF (projectiveSpaceOverRing N (.of A)).ringCatSheaf ⊤).obj (S 0).X₂,
        ConcreteCategory.hom ((secF (projectiveSpaceOverRing N (.of A)).ringCatSheaf ⊤).map
          ((S 0).g ≫ e₃.hom)) u ∈ mulSectionsClosure N G d

/-- **The multiplication theorem from a twisted Koszul chain.** If `G` has a twisted Koszul chain
at `d` and `Hⁱ(ℙᴺ_A, 𝒢(d - i)) = 0` for `1 ≤ i ≤ N`, then the products of global sections of
`𝒢(d)` with global sections of `𝒪(1)` generate `H⁰(ℙᴺ_A, 𝒢(d + 1))`. -/
theorem mulSectionsClosure_eq_top_of_hasTwistedKoszulChain (A : Type u) [CommRing A] (N : ℕ)
    (G : (projectiveSpaceOverRing N (.of A)).Modules) (d : ℤ)
    (hK : HasTwistedKoszulChain A N G d)
    (hreg : ∀ i : ℕ, 1 ≤ i → i ≤ N →
      IsZero (Hgroup (projectiveSpaceOverRing N (.of A)).ringCatSheaf ⊤ i
        (projectiveTwist N G (d - i)))) :
    mulSectionsClosure N G d = ⊤ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact mulSectionsClosure_zero_eq_top G d
  obtain ⟨Z, S, hS, h1, h3, hT, ⟨eN⟩, e₃, hcl⟩ := hK hN
  have hch := isZero_Hgroup_of_chain N Z S hS h1 h3 (fun k hk hkN =>
      (@KoszulAbs.IsFinSum.isZero_obj _ _ _ _ _ _ _
        (Hfunctor.{u, u, u} (projectiveSpaceOver N (Spec (.of A))).ringCatSheaf ⊤ k)
        ((Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
          (secF (projectiveSpaceOverRing N (.of A)).ringCatSheaf ⊤)).additive k) _ _
        (hT k hk hkN) (hreg k hk hkN.le)))
    (((hreg N hN le_rfl).of_iso ((Hfunctor.{u, u, u} _ ⊤ N).mapIso eN))) 1 le_rfl hN
  obtain ⟨e1⟩ := h1 0 hN
  have hsurj := surjective_secF_map_of_shortExact (S 0) (hS 0 hN)
    (hch.of_iso ((Hfunctor.{u, u, u} _ ⊤ 1).mapIso e1))
  let F : (projectiveSpaceOverRing N (.of A)).Modules ⥤ AddCommGrpCat.{u} :=
    secF (projectiveSpaceOverRing N (.of A)).ringCatSheaf ⊤
  have hs3 : Function.Surjective (ConcreteCategory.hom (F.map e₃.hom)) :=
    (ConcreteCategory.bijective_of_isIso (F.mapIso e₃).hom).2
  refine eq_top_iff.2 fun t _ => ?_
  obtain ⟨w, hw⟩ := hs3 t
  obtain ⟨u, hu⟩ := hsurj w
  have : t = ConcreteCategory.hom (F.map ((S 0).g ≫ e₃.hom)) u := by
    rw [F.map_comp]
    change t = ConcreteCategory.hom (F.map e₃.hom) (ConcreteCategory.hom (F.map (S 0).g) u)
    rw [hu, hw]
  rw [this]
  exact hcl u

/-! ### Two notions of global generation, and descent along an embedding -/

/-- **A module generated by a family of global sections is globally generated.** If a family of
global sections generates `ℱ` in the sense of [Stacks, Tag 03DE], then `ℱ` is globally
generated. -/
theorem isGloballyGenerated_of_isGeneratedByGlobalSections {X : Scheme.{u}} (F : X.Modules)
    (h : SheafOfModules.IsGeneratedByGlobalSections F) : IsGloballyGenerated F := by
  obtain ⟨σ⟩ := h
  have hσ := (generates_iff_stalkwise_generates X.ringCatSheaf F σ.s).mp σ.epi
  intro x _ U hxU t
  have hm := (hσ x).ge (Submodule.mem_top (x := TopCat.Presheaf.germ F.val.presheaf U x hxU t))
  obtain ⟨n, c, g, hcg⟩ := Submodule.mem_span_set'.mp hm
  choose j hj using fun i => (g i).2
  choose W hxW r hr using fun i => TopCat.Presheaf.exists_germ_eq X.ringCatSheaf.obj (x := x) (c i)
  let V : X.Opens := U ⊓ Finset.univ.inf W
  have hxV : x ∈ V := ⟨hxU, Finset.inf_induction (p := fun V : X.Opens => x ∈ V) trivial
    (fun _ ha _ hb => ⟨ha, hb⟩) (fun i _ => hxW i)⟩
  have hVU : V ≤ U := inf_le_left
  have hVW : ∀ i, V ≤ W i := fun i => inf_le_right.trans (Finset.inf_le (Finset.mem_univ i))
  let r' : Fin n → Γ(X, V) := fun i => X.presheaf.map (homOfLE (hVW i)).op (r i)
  let s' : Fin n → Γ(F, ⊤) := fun i => (σ.s (j i)).eval (op ⊤)
  have hgerm : TopCat.Presheaf.germ F.val.presheaf V x hxV (F.presheaf.map (homOfLE hVU).op t) =
      TopCat.Presheaf.germ F.val.presheaf V x hxV
        (∑ i, r' i • F.presheaf.map (homOfLE le_top).op (s' i)) := by
    erw [TopCat.Presheaf.germ_res_apply, ← hcg, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hs := PresheafOfModules.germ_ringCat_smul F.val x V hxV (r' i)
      (F.presheaf.map (homOfLE le_top).op (s' i))
    erw [hs]
    have hc : TopCat.Presheaf.germ X.ringCatSheaf.obj V x hxV (r' i) = c i := by
      rw [← hr i]
      exact TopCat.Presheaf.germ_res_apply X.ringCatSheaf.obj (homOfLE (hVW i)) x hxV (r i)
    have hg : TopCat.Presheaf.germ F.val.presheaf V x hxV
        (F.presheaf.map (homOfLE le_top).op (s' i)) = g i := by
      rw [← hj i]
      exact TopCat.Presheaf.Γgerm_res_apply F.val.presheaf x hxV (s' i)
    rw [hc, hg]
  obtain ⟨W', hxW', i1, i2, heq⟩ := TopCat.Presheaf.germ_eq F.val.presheaf x hxV hxV _ _ hgerm
  have hi : i1 = i2 := Subsingleton.elim _ _
  subst hi
  refine ⟨W', (i1 ≫ homOfLE hVU).le, hxW', n, s', fun i => X.presheaf.map i1.op (r' i), ?_⟩
  have h1 : F.presheaf.map (homOfLE (i1 ≫ homOfLE hVU).le).op t =
      F.presheaf.map i1.op (F.presheaf.map (homOfLE hVU).op t) := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl
  rw [h1]
  erw [heq, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  erw [PresheafOfModules.map_smul]
  congr 1
  change F.presheaf.map i1.op (F.presheaf.map (homOfLE le_top).op (s' i)) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl

/-- **Global generation at a point descends along an embedding.** If `f` is a topological
embedding and `f_*ℱ` is globally generated at `f(x)`, then `ℱ` is globally generated at `x`. -/
theorem isGloballyGeneratedAt_of_pushforward {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : Topology.IsInducing f.base) (F : X.Modules)
    (x : X) (h : IsGloballyGeneratedAt ((Scheme.Modules.pushforward f).obj F)
      {f.base x}) :
    IsGloballyGeneratedAt F {x} := by
  intro y hy U hxU t
  rw [Set.mem_singleton_iff] at hy
  subst hy
  obtain ⟨V, hV, hVU⟩ := hf.isOpen_iff.mp U.2
  let V' : Y.Opens := ⟨V, hV⟩
  have hU : f ⁻¹ᵁ V' = U := Opens.ext hVU
  let t' : Γ((Scheme.Modules.pushforward f).obj F, V') :=
    F.presheaf.map (homOfLE hU.le).op t
  obtain ⟨W, hWV, hxW, n, s, r, heq⟩ := h (f.base y) rfl V'
    (show y ∈ f ⁻¹ᵁ V' from hU ▸ hxU) t'
  have res : ∀ {A B C : X.Opens} (i : A ⟶ B) (j : B ⟶ C) (k : A ⟶ C) (u : Γ(F, C)),
      F.presheaf.map k.op u = F.presheaf.map i.op (F.presheaf.map j.op u) := by
    intro A B C i j k u
    rw [show k = i ≫ j from Subsingleton.elim _ _, op_comp, Functor.map_comp,
      ConcreteCategory.comp_apply]
  have hWU : f ⁻¹ᵁ W ≤ U := hU ▸ (Opens.map f.base).monotone hWV
  refine ⟨f ⁻¹ᵁ W, hWU, hxW, n,
    fun i => F.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤)).op (s i),
    fun i => f.app W (r i), ?_⟩
  have h1 : F.presheaf.map (homOfLE hWU).op t =
      ((Scheme.Modules.pushforward f).obj F).presheaf.map (homOfLE hWV).op t' := by
    simp only [t', Scheme.Modules.pushforward_obj_presheaf_map]
    exact res _ _ _ t
  rw [h1, heq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Scheme.Modules.pushforward_obj_presheaf_map]
  dsimp only
  have e := res (homOfLE (le_top : f ⁻¹ᵁ W ≤ ⊤)) (homOfLE (le_top : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤))
    ((Opens.map f.base).map (homOfLE le_top)) (s i)
  exact Eq.trans rfl (congrArg (fun m => f.app W (r i) • m) e)

/-- **Global generation descends along an embedding**: if `f` is a topological embedding and
`f_*ℱ` is globally generated, so is `ℱ`. -/
theorem isGloballyGenerated_of_pushforward {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : Topology.IsInducing f.base) (F : X.Modules)
    (h : IsGloballyGenerated ((Scheme.Modules.pushforward f).obj F)) :
    IsGloballyGenerated F := fun x _ =>
  isGloballyGeneratedAt_of_pushforward f hf F x
    (fun y _ => h y (Set.mem_univ y)) x rfl

/-- **Global generation descends along a closed immersion**: if `f_*ℱ` is generated by a family
of global sections, then `ℱ` is globally generated. -/
theorem isGloballyGenerated_of_isGeneratedByGlobalSections_pushforward {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsClosedImmersion f] (F : X.Modules)
    (h : SheafOfModules.IsGeneratedByGlobalSections ((Scheme.Modules.pushforward f).obj F)) :
    IsGloballyGenerated F :=
  isGloballyGenerated_of_pushforward f (f.isClosedEmbedding).isInducing F
    (isGloballyGenerated_of_isGeneratedByGlobalSections _ h)

/-! ### The Koszul operators on `ℙᴺ_A` -/

section Operators

open Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMulShape
  Stacks.AlgebraicGeometry.ProjectiveSpaceSectionFiniteFamily
  Stacks.AlgebraicGeometry.ProjTwistFunctor

attribute [local instance] MvPolynomial.gradedAlgebra
  Stacks.AlgebraicGeometry.ProjectiveSpaceSectionFiniteFamily.tensorMonoidal
  Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMulShape.tensorSymmetric

variable {A : Type u} [CommRing A] (N : ℕ)

/-- Multiplication by a global section of `𝒪(1)`, as a natural transformation from the identity
to the twist by one. -/
def twistOp (s : (twistOver N (Spec (.of A)) 1).sections) :
    𝟭 (projectiveSpaceOverRing N (.of A)).Modules ⟶ projectiveTwistFunctor (R := A) N 1 where
  app M := mulSectionOne N (Spec (.of A)) M s
  naturality {_ _} f := mulSectionOne_naturality N (Spec (.of A)) f s

/-- The tensor square of `𝒪(1)` has trivial self-braiding. -/
theorem braiding_self_twistOver_one (S : Scheme.{u}) :
    (β_ (twistOver N S 1) (twistOver N S 1)).hom = 𝟙 (twistOver N S 1 ⊗ twistOver N S 1) := by
  have h1 := Stacks.SheafOfModules.tensorObjIso_braiding (projectiveSpaceOver N S).presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (projectiveSpaceOver N S))
    (twistOver N S 1) (twistOver N S 1)
  have h0 := (Stacks.SelfBraidingInvertible.hasTrivialSelfBraiding
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (projectiveSpaceOver N S))
    (twistOver N S 1)).braiding_self
  erw [h0, Category.id_comp] at h1
  have h2 : (Stacks.SheafOfModules.Invertible.tensorProductBraiding
      (projectiveSpaceOver N S).presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (projectiveSpaceOver N S))
      (twistOver N S 1) (twistOver N S 1)).hom = 𝟙 _ :=
    (Iso.cancel_iso_hom_left (Stacks.SheafOfModules.tensorObjIso
      (projectiveSpaceOver N S).presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (projectiveSpaceOver N S))
      (twistOver N S 1) (twistOver N S 1)) _ _).1 (by erw [h1, Category.comp_id])
  exact h2

/-- Multiplication by `s` commutes with the twist by one: `s (ℱ(1)) = s(ℱ)(1)`. -/
theorem twistOp_app_obj (s : (twistOver N (Spec (.of A)) 1).sections)
    (Y : (projectiveSpaceOverRing N (.of A)).Modules) :
    (twistOp N s).app ((projectiveTwistFunctor (R := A) N 1).obj Y) =
      (projectiveTwistFunctor (R := A) N 1).map ((twistOp N s).app Y) := by
  have h := mulSection_whiskerRight N (Spec (.of A)) Y (twistOver N (Spec (.of A)) 1) s
  have hs : (swapRight N (Spec (.of A)) Y (twistOver N (Spec (.of A)) 1)).hom = 𝟙 _ := by
    rw [swapRight, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom,
      braiding_self_twistOver_one, whiskerLeft_id, Category.id_comp, Iso.hom_inv_id]
  rw [hs, Category.comp_id] at h
  change mulSectionOne N (Spec (.of A)) _ s = mulSectionOne N (Spec (.of A)) Y s ▷ _
  rw [mulSectionOne_eq_rightUnitor_inv_comp, mulSectionOne_eq_rightUnitor_inv_comp]
  exact h.symm

/-- The global section of `𝒪(1)` on `ℙᴺ_A` attached to the `i`-th coordinate. -/
noncomputable def coordSectionTop (i : Fin (N + 1)) : Γ(twistOver N (Spec (.of A)) 1, ⊤) :=
  pullbackGlobalSections (projectiveSpaceOver.toIntegralAtUniverse N (Spec (.of A)))
    (ProjectiveSpectrum.Proj.twistingSheaf
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) (ULift.{u} ℤ)) 1)
    (ProjectiveSpectrum.Proj.degreeSection _ 1
      ⟨MvPolynomial.X i, Stacks.SymmetricAway.X_mem_homogeneousSubmodule_one i⟩)

/-- Every point of `ℙᴺ_A` lies in the nonvanishing locus of some coordinate section of `𝒪(1)`. -/
theorem exists_mem_nonvanishingLocus_coordSectionTop (z : projectiveSpaceOver N (Spec (.of A))) :
    ∃ i, z ∈ Stacks.Ample.nonvanishingLocus (twistOver N (Spec (.of A)) 1)
      (coordSectionTop (A := A) N i) := by
  let f := projectiveSpaceOver.toIntegralAtUniverse N (Spec (.of A))
  obtain ⟨i, hi⟩ := Stacks.ProjectiveSpace.exists_mem_basicOpen_X (R := ULift.{u} ℤ)
    (σ := Fin (N + 1)) (f.base z)
  refine ⟨i, ?_⟩
  have h1 :=
    Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.nonvanishingLocus_degreeSection_eq_basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) (ULift.{u} ℤ))
      (adjoin_degreeOne_integralModel N)
      (d := 1) one_pos 1 ⟨MvPolynomial.X i, Stacks.SymmetricAway.X_mem_homogeneousSubmodule_one i⟩
  have h2 : f.base z ∈ Stacks.Ample.nonvanishingLocus
      (X := AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) (ULift.{u} ℤ)))
      (ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) (ULift.{u} ℤ)) 1)
      (ProjectiveSpectrum.Proj.degreeSection _ 1
        ⟨MvPolynomial.X i, Stacks.SymmetricAway.X_mem_homogeneousSubmodule_one i⟩) :=
    (Set.ext_iff.mp h1 (f.base z)).2 hi
  have h4 := Stacks.NonvanishingPullback.mem_nonvanishingLocus_pullback_iff f
    (ProjectiveSpectrum.Proj.twistingSheaf
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) (ULift.{u} ℤ)) 1)
    (ProjectiveSpectrum.Proj.degreeSection _ 1
        ⟨MvPolynomial.X i, Stacks.SymmetricAway.X_mem_homogeneousSubmodule_one i⟩) z
  have h5 := Stacks.AmpleFormalSystemLifting.pullbackGlobalSections_eq_pullbackGlobalSection f
    (ProjectiveSpectrum.Proj.twistingSheaf
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) (ULift.{u} ℤ)) 1)
    (ProjectiveSpectrum.Proj.degreeSection _ 1
        ⟨MvPolynomial.X i, Stacks.SymmetricAway.X_mem_homogeneousSubmodule_one i⟩)
  change z ∈ Stacks.Ample.nonvanishingLocus _ (pullbackGlobalSections f _ _)
  rw [h5]
  exact h4.2 h2

/-- The coordinate sections of `𝒪(1)`. -/
noncomputable def coordSection (i : Fin (N + 1)) : (twistOver N (Spec (.of A)) 1).sections :=
  sectionOfTop _ (coordSectionTop (A := A) N i)

/-- The map from the free module on the coordinates to `𝒪(1)`. -/
noncomputable def coordFreeHom :
    SheafOfModules.free (R := (projectiveSpaceOver N (Spec (.of A))).ringCatSheaf)
      (ULift.{u} (Fin (N + 1))) ⟶ twistOver N (Spec (.of A)) 1 :=
  (twistOver N (Spec (.of A)) 1).freeHomEquiv.symm (fun j => coordSection (A := A) N j.down)

/-- A morphism `φ : M ⟶ L` to an invertible module is an epimorphism if every point lies in the
nonvanishing locus of the image under `φ` of some local section of `M`. -/
theorem epi_of_forall_mem_nonvanishingLocusOn {Z : Scheme.{u}} {M L : Z.Modules}
    [Stacks.Ample.IsInvertibleModule Z L] (φ : M ⟶ L)
    (h : ∀ z : Z, ∃ (O : Z.Opens) (m : Γ(M, O)),
      z ∈ Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn L O (φ.app O m)) :
    Epi φ := by
  refine Stacks.FundamentalGroup.epi_of_isLocallySurjective φ fun W t x hx => ?_
  obtain ⟨O, m, hxO⟩ := h x
  let W' : Z.Opens := W ⊓ Stacks.SectionPowerOpen.nonvanishingOpenOn L O (φ.app O m)
  have hW'O : W' ≤ O := inf_le_right.trans
    (Stacks.SectionPowerOpen.nonvanishingOpenOn_le L O (φ.app O m))
  have hbij := Stacks.SheafOfModules.bijective_smul_of_forall_germ_notMem_maximalIdeal_smul_top
    L (φ.app O m) W' hW'O fun y hy =>
      (Stacks.NonvanishingPullback.mem_maximalSmul_iff _ _ _).not.mp hy.2.2
  obtain ⟨c, hc⟩ := hbij.2 (L.presheaf.map (homOfLE inf_le_left : W' ⟶ W).op t)
  refine ⟨W', inf_le_left, ⟨hx, hxO⟩, c • M.presheaf.map (homOfLE hW'O).op m, ?_⟩
  rw [Scheme.Modules.Hom.app_smul, ← hc]
  congr 1
  exact ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE hW'O).op) m

/-- The coordinate sections generate `𝒪(1)` on `ℙᴺ_A`. -/
theorem epi_coordFreeHom : Epi (coordFreeHom (A := A) N) := by
  refine epi_of_forall_mem_nonvanishingLocusOn _ fun z => ?_
  obtain ⟨i, hi⟩ := exists_mem_nonvanishingLocus_coordSectionTop (A := A) N z
  refine ⟨⊤, (SheafOfModules.freeSection (ULift.up i)).val (op ⊤), ?_⟩
  have h1 : Scheme.Modules.Hom.app (coordFreeHom (A := A) N) ⊤
      ((SheafOfModules.freeSection (ULift.up i)).val (op ⊤)) = coordSectionTop (A := A) N i := by
    have := SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
      (M := twistOver N (Spec (.of A)) 1)
      (fun j : ULift.{u} (Fin (N + 1)) => coordSection (A := A) N j.down)
      (ULift.up i)
    have h2 := congrArg (fun s => s.val (op ⊤)) this
    refine h2.trans ?_
    exact sectionOfTop_val_top _ _
  rw [h1, Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn_top]
  exact hi

/-- The functor `X ⊗ -` on modules over `ℙᴺ_A`. -/
noncomputable abbrev leftTensor (X : (projectiveSpaceOver N (Spec (.of A))).Modules) :
    (projectiveSpaceOver N (Spec (.of A))).Modules ⥤
      (projectiveSpaceOver N (Spec (.of A))).Modules :=
  (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ⟨(((projectiveSpaceOver N (Spec (.of A))).toRingedSpace)).presheaf,
      (((projectiveSpaceOver N (Spec (.of A))).toRingedSpace)).IsSheaf⟩).obj X

/-- The functor `X ⊗ -` preserves colimits. -/
theorem leftTensor_preservesColimits (X : (projectiveSpaceOver N (Spec (.of A))).Modules) :
    PreservesColimitsOfSize.{u, u} (leftTensor (A := A) N X) :=
  Stacks.SheafOfModules.TensorColimits.tensorLeft_preservesColimits.{u, u, u, u, u}
    (Opens.grothendieckTopology (projectiveSpaceOver N (Spec (.of A))))
    ⟨(((projectiveSpaceOver N (Spec (.of A))).toRingedSpace)).presheaf,
      (((projectiveSpaceOver N (Spec (.of A))).toRingedSpace)).IsSheaf⟩ X

/-- Multiplication by the coordinate sections `⨁ X ⟶ X(1)` is an epimorphism for every module
`X` on `ℙᴺ_A`. -/
theorem epi_desc_twistOp_coordSection (X : (projectiveSpaceOverRing N (.of A)).Modules) :
    Epi (biproduct.desc fun i : Fin (N + 1) => (twistOp (A := A) N (coordSection N i)).app X :
      (⨁ fun _ : Fin (N + 1) => X) ⟶ (projectiveTwistFunctor (R := A) N 1).obj X) := by
  have hc := leftTensor_preservesColimits (A := A) N X
  have hc0 : PreservesColimitsOfSize.{0, 0} (leftTensor (A := A) N X) :=
    preservesColimitsOfSize_of_univLE.{u, u, 0, 0} (leftTensor (A := A) N X)
  have hφ : @Epi (projectiveSpaceOver N (Spec (.of A))).Modules Scheme.Modules.instCategory _ _
      (coordFreeHom (A := A) N) := epi_coordFreeHom (A := A) N
  have hshape : PreservesColimitsOfShape (Discrete (ULift.{u} (Fin (N + 1))))
      (leftTensor (A := A) N X) := inferInstance
  have hepi : Epi ((leftTensor (A := A) N X).map (coordFreeHom (A := A) N)) :=
    (leftTensor (A := A) N X).map_epi (coordFreeHom (A := A) N)
  have hpc : PreservesColimit (Discrete.functor fun _ : ULift.{u} (Fin (N + 1)) =>
      SheafOfModules.unit (projectiveSpaceOver N (Spec (.of A))).ringCatSheaf)
      (leftTensor (A := A) N X) := hshape.preservesColimit
  let ψ : (⨁ fun _ : Fin (N + 1) => X) ⟶ (projectiveTwistFunctor (R := A) N 1).obj X :=
    biproduct.desc fun i : Fin (N + 1) => (twistOp (A := A) N (coordSection N i)).app X
  have hcol := @isColimitOfPreserves _ _ _ _ _ _ _ (leftTensor (A := A) N X) _
    (SheafOfModules.isColimitFreeCofan (R := (projectiveSpaceOver N (Spec (.of A))).ringCatSheaf)
      (ULift.{u} (Fin (N + 1)))) hpc
  let Λ := hcol.desc
    (Cocone.mk (⨁ fun _ : Fin (N + 1) => X)
      (Discrete.natTrans (fun j => (ρ_ X).hom ≫ biproduct.ι (fun _ : Fin (N + 1) => X) j.as.down)))
  have hfac : Λ ≫ ψ = (leftTensor (A := A) N X).map (coordFreeHom (A := A) N) := by
    refine hcol.hom_ext fun j => ?_
    have hΛ := hcol.fac (Cocone.mk (⨁ fun _ : Fin (N + 1) => X)
      (Discrete.natTrans fun j =>
        (ρ_ X).hom ≫ biproduct.ι (fun _ : Fin (N + 1) => X) j.as.down)) j
    erw [← Category.assoc, hΛ]
    have h1 : biproduct.ι (fun _ : Fin (N + 1) => X) j.as.down ≫ ψ =
        mulSectionOne N (Spec (.of A)) X (coordSection N j.as.down) := biproduct.ι_desc _ _
    have h2 : SheafOfModules.ιFree (R := (projectiveSpaceOver N (Spec (.of A))).ringCatSheaf)
        j.as ≫ coordFreeHom (A := A) N = sectionHom _ (coordSection N j.as.down) := by
      have e1 := SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply
        (M := twistOver N (Spec (.of A)) 1) (coordFreeHom (A := A) N) j.as
      have e2 : (twistOver N (Spec (.of A)) 1).freeHomEquiv (coordFreeHom (A := A) N) j.as =
          coordSection N j.as.down :=
        congrFun ((twistOver N (Spec (.of A)) 1).freeHomEquiv.apply_symm_apply
          (fun j : ULift.{u} (Fin (N + 1)) => coordSection (A := A) N j.down)) j.as
      exact e1.symm.trans (congrArg _ e2)
    have h3 : (leftTensor (A := A) N X).map (SheafOfModules.ιFree
        (R := (projectiveSpaceOver N (Spec (.of A))).ringCatSheaf) j.as) ≫
        (leftTensor (A := A) N X).map (coordFreeHom (A := A) N) =
        X ◁ sectionHom _ (coordSection N j.as.down) := by
      erw [← Functor.map_comp, h2]
      rfl
    change ((ρ_ X).hom ≫ biproduct.ι (fun _ : Fin (N + 1) => X) j.as.down) ≫ ψ =
      (leftTensor (A := A) N X).map (SheafOfModules.ιFree
        (R := (projectiveSpaceOver N (Spec (.of A))).ringCatSheaf) j.as) ≫
        (leftTensor (A := A) N X).map (coordFreeHom (A := A) N)
    erw [h3, Category.assoc, h1, mulSectionOne_eq_rightUnitor_inv_comp, Iso.hom_inv_id_assoc]
    rfl
  exact @epi_of_epi_fac _ _ _ _ _ Λ ψ _ hepi hfac

end Operators

/-! ### The twisted Koszul chain on `ℙᴺ_A` -/

section Chain

open Stacks.AlgebraicGeometry.ProjTwistFunctor

variable {A : Type u} [CommRing A] (N : ℕ)

/-- `T^j (𝒢(e)) ≅ 𝒢(e + j)` for the twist `T` by one. -/
theorem nonempty_iso_tpow_projectiveTwist
    (G : (projectiveSpaceOverRing N (.of A)).Modules) (e : ℤ) :
    ∀ j : ℕ, Nonempty (KoszulAbs.tpow (projectiveTwistFunctor (R := A) N 1) j
        (projectiveTwist N G e) ≅ projectiveTwist N G (e + j))
  | 0 => ⟨eqToIso (by rw [Nat.cast_zero, add_zero]; rfl)⟩
  | j + 1 => by
    obtain ⟨u⟩ := nonempty_iso_tpow_projectiveTwist G e j
    refine ⟨(projectiveTwistFunctor (R := A) N 1).mapIso u ≪≫
      twistAssocIso N (Spec (.of A)) G (e + j) ≪≫ eqToIso ?_⟩
    simp only [Nat.cast_succ]
    rw [add_assoc]

/-- The products of a coordinate section with the sections of `𝒢(d)`, transported along the
comparison `T (𝒢(d)) ≅ 𝒢(d + 1)`, lie in `MMP.Fourfold.mulSectionsClosure`. -/
theorem map_twistOp_mem_mulSectionsClosure
    (G : (projectiveSpaceOverRing N (.of A)).Modules) (d : ℤ)
    (s : (twistOver N (Spec (.of A)) 1).sections)
    (Q : (projectiveSpaceOverRing N (.of A)).Modules) (uQ : Q ≅ projectiveTwist N G d)
    (y : (secF (projectiveSpaceOverRing N (.of A)).ringCatSheaf ⊤).obj Q) :
    ConcreteCategory.hom ((secF (projectiveSpaceOverRing N (.of A)).ringCatSheaf ⊤).map
      ((projectiveTwistFunctor (R := A) N 1).map uQ.hom ≫
        (twistAssocIso N (Spec (.of A)) G d).hom))
      (ConcreteCategory.hom ((secF (projectiveSpaceOverRing N (.of A)).ringCatSheaf ⊤).map
        ((twistOp N s).app Q)) y) ∈ mulSectionsClosure N G d := by
  let F : (projectiveSpaceOverRing N (.of A)).Modules ⥤ AddCommGrpCat.{u} :=
    secF (projectiveSpaceOverRing N (.of A)).ringCatSheaf ⊤
  let ψ := (projectiveTwistFunctor (R := A) N 1).map uQ.hom ≫
    (twistAssocIso N (Spec (.of A)) G d).hom
  refine AddSubgroup.subset_closure ⟨s, ConcreteCategory.hom (F.map uQ.hom) y, ?_⟩
  have hnat := (twistOp (A := A) N s).naturality uQ.hom
  have hcomp : (twistOp (A := A) N s).app Q ≫ ψ =
      uQ.hom ≫ twistSectionMul N (Spec (.of A)) G s d := by
    have hnat' : (twistOp (A := A) N s).app Q ≫ (projectiveTwistFunctor (R := A) N 1).map uQ.hom =
        uQ.hom ≫ mulSectionOne N (Spec (.of A)) (projectiveTwist N G d) s := hnat.symm
    rw [twistSectionMul_eq_mulSectionOne_comp]
    have h1 : (twistOp (A := A) N s).app Q ≫ ψ =
        ((twistOp (A := A) N s).app Q ≫ (projectiveTwistFunctor (R := A) N 1).map uQ.hom) ≫
          (twistAssocIso N (Spec (.of A)) G d).hom := (Category.assoc _ _ _).symm
    rw [h1, hnat']
    exact Category.assoc _ _ _
  have e1 : ConcreteCategory.hom (F.map ψ) (ConcreteCategory.hom (F.map ((twistOp N s).app Q)) y) =
      ConcreteCategory.hom (F.map ((twistOp N s).app Q ≫ ψ)) y :=
    (ConcreteCategory.congr_hom (F.map_comp ((twistOp N s).app Q) ψ) y).symm
  have e2 := congrArg (fun m => ConcreteCategory.hom (F.map m) y) hcomp
  have e3 :=
    ConcreteCategory.congr_hom (F.map_comp uQ.hom (twistSectionMul N (Spec (.of A)) G s d)) y
  exact e1.trans (e2.trans e3)

/-- **Twisted Koszul chains exist** on `ℙᴺ_A`, for every ring `A`, module `𝒢` and twist `d`. -/
theorem hasTwistedKoszulChain (A : Type u) [CommRing A] (N : ℕ)
    (G : (projectiveSpaceOverRing N (.of A)).Modules) (d : ℤ) :
    HasTwistedKoszulChain A N G d := by
  intro hN
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  set T := projectiveTwistFunctor (R := A) (n + 1) 1 with hT
  let f : Fin (n + 2) → (𝟭 (projectiveSpaceOverRing (n + 1) (.of A)).Modules ⟶ T) :=
    fun i => twistOp (A := A) (n + 1) (coordSection (A := A) (n + 1) i)
  let τ := f 0
  obtain ⟨L, hLdef⟩ : ∃ L, L = List.ofFn (fun i : Fin (n + 1) => f i.succ) := ⟨_, rfl⟩
  have hlist : τ :: L = List.ofFn f := by rw [hLdef]; exact (List.ofFn_succ (f := f)).symm
  have hLlen : L.length = n + 1 := by rw [hLdef]; exact List.length_ofFn
  have hcomm : KoszulAbs.CommList T (τ :: L) := by
    intro τ' hτ' Y
    have hτ'' : τ' ∈ List.ofFn f := hlist ▸ hτ'
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hτ''
    exact twistOp_app_obj (n + 1) (coordSection (n + 1) i) Y
  have hgen := KoszulAbs.epi_desc_get_of_ofFn T f (τ :: L) hlist
    (fun X => epi_desc_twistOp_coordSection (A := A) (n + 1) X)
  let M := projectiveTwist (n + 1) G (d - ((n + 1 : ℕ) : ℤ))
  obtain ⟨Z, S, hS, h1, h3, hT', hZ, e₃, hcl⟩ :=
    KoszulAbs.exists_koszul_chain.{u, u, u + 1} T τ L (le_of_le_of_eq hN hLlen.symm) M hcomm hgen
  have hiso : ∀ (j : ℕ) (e e' : ℤ), e + j = e' →
      Nonempty (KoszulAbs.tpow T j (projectiveTwist (n + 1) G e) ≅ projectiveTwist (n + 1) G e') :=
    fun j e e' h => by
      obtain ⟨u⟩ := nonempty_iso_tpow_projectiveTwist (A := A) (n + 1) G e j
      exact ⟨u ≪≫ eqToIso (congrArg (projectiveTwist (n + 1) G) h)⟩
  obtain ⟨uQ⟩ := hiso L.length (d - ((n + 1 : ℕ) : ℤ)) d (by rw [hLlen]; push_cast; ring)
  have hlt : ∀ {k}, k < n + 1 → k < L.length := fun hk => lt_of_lt_of_eq hk hLlen.symm
  refine ⟨Z, S, fun k hk => hS k (hlt hk), fun k hk => h1 k (hlt hk),
    fun k hk1 hk => h3 k hk1 (hlt hk), ?_, ?_, ?_⟩
  · intro k hk1 hk
    have hk' := hlt hk
    obtain ⟨u⟩ := hiso (L.length - k) (d - ((n + 1 : ℕ) : ℤ)) (d - k) (by
      rw [Nat.cast_sub hk'.le, hLlen]; push_cast; ring)
    exact (hT' k hk1 hk').congr u
  · obtain ⟨u⟩ := hZ
    exact ⟨eqToIso (congrArg Z hLlen).symm ≪≫ u⟩
  · refine ⟨e₃ ≪≫ T.mapIso uQ ≪≫ twistAssocIso (n + 1) (Spec (.of A)) G d, ?_⟩
    intro u
    let F : (projectiveSpaceOverRing (n + 1) (.of A)).Modules ⥤ AddCommGrpCat.{u} :=
      secF (projectiveSpaceOverRing (n + 1) (.of A)).ringCatSheaf ⊤
    have hFadd : F.Additive := inferInstanceAs (secF _ ⊤).Additive
    have hc := hcl F u
    let ψ : T.obj (KoszulAbs.tpow T L.length M) ⟶ projectiveTwist (n + 1) G (d + 1) :=
      T.map uQ.hom ≫ (twistAssocIso (n + 1) (Spec (.of A)) G d).hom
    have hΦ : (S 0).g ≫ (e₃ ≪≫ T.mapIso uQ ≪≫ twistAssocIso (n + 1) (Spec (.of A)) G d).hom =
        ((S 0).g ≫ e₃.hom) ≫ ψ := by
      erw [Iso.trans_hom, Iso.trans_hom, Functor.mapIso_hom]
      exact (Category.assoc _ _ _).symm
    erw [hΦ, F.map_comp]
    change ConcreteCategory.hom (F.map ψ) (ConcreteCategory.hom (F.map ((S 0).g ≫ e₃.hom)) u) ∈ _
    refine AddSubgroup.closure_induction
      (p := fun x _ => ConcreteCategory.hom (F.map ψ) x ∈ mulSectionsClosure (n + 1) G d)
      ?_ ?_ ?_ ?_ hc
    · rintro x ⟨τ', hτ', y, rfl⟩
      have hτ'' : τ' ∈ List.ofFn f := hlist ▸ hτ'
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hτ''
      exact map_twistOp_mem_mulSectionsClosure (n + 1) G d (coordSection (n + 1) i)
        (KoszulAbs.tpow T L.length M) uQ y
    · rw [map_zero]
      exact zero_mem _
    · intro x y _ _ hx hy
      rw [map_add]
      exact add_mem hx hy
    · intro x _ hx
      rw [map_neg]
      exact neg_mem hx

end Chain

/-- **Mumford's multiplication theorem over an arbitrary ring** ([Stacks, Tag 08A7] with the field
replaced by a ring): for a coherent `𝒢` on `ℙᴺ_A` with `Hⁱ(ℙᴺ_A, 𝒢(d - i)) = 0` for `1 ≤ i ≤ N`,
the products of global sections of `𝒢(d)` with global sections of `𝒪(1)` generate
`H⁰(ℙᴺ_A, 𝒢(d + 1))`. -/
theorem mulSectionsClosure_eq_top_of_regular (A : Type u) [CommRing A] (N : ℕ)
    (G : (projectiveSpaceOverRing N (.of A)).Modules) [G.IsCoherent] (d : ℤ)
    (hreg : ∀ i : ℕ, 1 ≤ i → i ≤ N →
      IsZero (Hgroup (projectiveSpaceOverRing N (.of A)).ringCatSheaf ⊤ i
        (projectiveTwist N G (d - i)))) :
    mulSectionsClosure N G d = ⊤ :=
  mulSectionsClosure_eq_top_of_hasTwistedKoszulChain A N G d (hasTwistedKoszulChain A N G d) hreg

/-- **Castelnuovo–Mumford regularity on `ℙⁿ_R`.** If the coherent `ℱ` on `ℙⁿ_R`
is `d`-regular for every `d ≥ m`, then `ℱ(m)` is globally generated. -/
theorem isGeneratedByGlobalSections_projectiveTwist_of_regular
    (F : (projectiveSpaceOverRing n (.of R)).Modules) [F.IsCoherent] (m : ℤ)
    (hreg : ∀ d : ℤ, m ≤ d → ∀ i : ℕ, 1 ≤ i → i ≤ n →
      IsZero (Hgroup (projectiveSpaceOverRing n (.of R)).ringCatSheaf ⊤ i
        (projectiveTwist n F (d - i)))) :
    SheafOfModules.IsGeneratedByGlobalSections (projectiveTwist n F m) :=
  isGeneratedByGlobalSections_projectiveTwist_of_forall_mulSectionsClosure n F m
    fun d hd => mulSectionsClosure_eq_top_of_regular R n F d (hreg d hd)

/-! ### Cohomological generation over an affine base -/

section AffineBase

open Stacks.RelativeVeryAmple Stacks.Ample
open MMP.Intersection (twist)

variable {X : Scheme.{u}}

/-- `𝒪_X(0) ≅ 𝒪_X`. -/
theorem nonempty_lineBundle_zero_iso_unit :
    Nonempty (MMP.CartierDivisor.sheaf (0 : X.CartierDivisor) ≅ unitModule X) := by
  have m : tensorModules X (MMP.CartierDivisor.sheaf (0 : X.CartierDivisor))
      (MMP.CartierDivisor.sheaf 0) ≅ MMP.CartierDivisor.sheaf 0 :=
    MMP.CartierDivisorSheaf.sheafMulIso (0 : X.CartierDivisor) 0 ≪≫ eqToIso (by rw [add_zero])
  exact ⟨isoUnitModuleOfTensorSelfIso X _ m⟩

/-- `𝒪_X(kD) ≅ 𝒪_X(D)^{⊗ k}` for `k : ℕ`, with Stacks' tensor powers of an invertible module. -/
theorem nonempty_lineBundle_nat_smul_iso (D : X.CartierDivisor) (k : ℕ) :
    Nonempty (MMP.CartierDivisor.sheaf (k • D) ≅
      tensorPowModule X (MMP.CartierDivisor.sheaf D) (k : ℤ)) := by
  induction k with
  | zero =>
    obtain ⟨e⟩ := nonempty_lineBundle_zero_iso_unit (X := X)
    exact ⟨eqToIso (by rw [zero_smul]) ≪≫ e ≪≫
      (tensorPowModuleZeroIso X (MMP.CartierDivisor.sheaf D)).symm⟩
  | succ n ih =>
    obtain ⟨e⟩ := ih
    refine ⟨eqToIso (by rw [succ_nsmul]) ≪≫ (MMP.CartierDivisorSheaf.sheafMulIso (n • D) D).symm ≪≫
      tensorModulesMapIso X e (tensorPowModuleOneIso X (MMP.CartierDivisor.sheaf D)).symm ≪≫
      tensorPowModuleAddIso X (MMP.CartierDivisor.sheaf D) (n : ℤ) 1 ≪≫ tensorPowModuleCongr X _ (by
          push_cast; rfl)⟩

/-- `𝒪_X(mD) ≅ 𝒪_X(D)^{⊗ m}` for every integer `m`: in negative degrees both sides are tensor
inverses of the `|m|`-th power. -/
theorem nonempty_lineBundle_int_smul_iso (D : X.CartierDivisor) (m : ℤ) :
    Nonempty (MMP.CartierDivisor.sheaf (m • D) ≅
      tensorPowModule X (MMP.CartierDivisor.sheaf D) m) := by
  rcases m with k | k
  · simpa using nonempty_lineBundle_nat_smul_iso D k
  · have hk : Int.negSucc k = -((k + 1 : ℕ) : ℤ) := by push_cast; rfl
    rw [hk]
    obtain ⟨e⟩ := nonempty_lineBundle_nat_smul_iso D (k + 1)
    have e' : MMP.CartierDivisor.sheaf (((k + 1 : ℕ) : ℤ) • D) ≅ tensorPowModule X
        (MMP.CartierDivisor.sheaf D) ((k + 1 : ℕ) : ℤ) :=
      eqToIso (by rw [natCast_zsmul]) ≪≫ e
    refine ⟨isoOfTensorUnitIso X _ _ (MMP.CartierDivisor.sheaf (((k + 1 : ℕ) : ℤ) • D)) ?_ ?_⟩
    · exact MMP.CartierDivisorSheaf.sheafMulIso _ _ ≪≫ eqToIso (by rw [← add_smul]; simp) ≪≫
        (nonempty_lineBundle_zero_iso_unit (X := X)).some
    · exact tensorModulesMapIso X (Iso.refl _) e' ≪≫
        tensorPowModuleAddIso X (MMP.CartierDivisor.sheaf D) _ _ ≪≫ tensorPowModuleCongr X _ (show
            -((k + 1 : ℕ) : ℤ) + ((k + 1 : ℕ) : ℤ) = 0 by ring) ≪≫
        tensorPowModuleZeroIso X (MMP.CartierDivisor.sheaf D)

section Core

variable {R : Type u} [CommRing R] {N : ℕ} {X : Scheme.{u}}
  (ι : X ⟶ projectiveSpaceOverRing N (.of R)) [IsClosedImmersion ι]
  (L : X.Modules) [IsInvertibleModule X L]
  (hL : L ≅ (Scheme.Modules.pullback ι).obj (twistOver N (Spec (.of R)) 1))

/-- **The twists of a direct image along a closed immersion.** For a closed immersion `ι` into
`ℙᴺ_R` and an invertible `L` on the source identified with `ι^*𝒪(1)`, the projection formula gives
`(ι_*ℱ)(d) ≅ ι_*(ℱ ⊗ L^{⊗ d})` for every integer `d`. -/
def projectiveTwistPushforwardIso (F : X.Modules) (d : ℤ) :
    projectiveTwist N ((Scheme.Modules.pushforward ι).obj F) d ≅
      (Scheme.Modules.pushforward ι).obj (tensorModules X F (tensorPowModule X L d)) :=
  tensorModulesMapIso _ (Iso.refl _) (tensorPowModuleProjectiveTwistIso N (Spec (.of R)) d).symm ≪≫
    Stacks.AlgebraicGeometry.HyperplaneTwistSequence.pushforwardTwistModuleIso ι
      (twistOver N (Spec (.of R)) 1) F d ≪≫
    (Scheme.Modules.pushforward ι).mapIso (tensorModulesMapIso X (Iso.refl F)
      (Stacks.AlgebraicGeometry.HyperplaneTwistSequence.tensorPowModuleIsoOfIsoInt X _ L hL.symm d))

/-- **Cohomology along a closed immersion** ([Stacks, Tag 089W]): for a quasi-coherent `E` on the
source of a closed immersion `f`, `Hⁱ(Y, f_*E) = 0` if and only if `Hⁱ(X, E) = 0`. -/
theorem isZero_Hgroup_pushforward_iff {Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (E : X.Modules) (hE : E.IsQuasicoherent) (i : ℕ) :
    IsZero (Hgroup Y.ringCatSheaf ⊤ i ((Scheme.Modules.pushforward f).obj E)) ↔
      IsZero (Hgroup X.ringCatSheaf ⊤ i E) := by
  refine ⟨fun h => Stacks.Blowup.isZero_Hgroup_of_isZero_Hgroup_pushforward f E hE i h, fun h => ?_⟩
  have h1 := (Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
    X.ringCatSheaf ⊤ i E).2 h
  have h3 := (Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward f E i).isZero_iff.1
    (by rwa [ModuleCat.isZero_iff_subsingleton] at h1 ⊢)
  exact (Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
    Y.ringCatSheaf ⊤ i ((Scheme.Modules.pushforward f).obj E)).1
    (by rwa [ModuleCat.isZero_iff_subsingleton] at h3 ⊢)

include ι hL in
/-- **Cohomological generation for a closed subscheme of `ℙᴺ_R`.** Let `ι : X ⟶ ℙᴺ_R` be a closed
immersion, `R` Noetherian, `L ≅ ι^*𝒪(1)` an invertible sheaf on `X`, `dim X ≤ n`, and `ℱ` coherent
on `X` with `Hⁱ(X, ℱ ⊗ L^{⊗ m}) = 0` for all `i > 0` and `m ≥ -n`. Then `ℱ` is globally
generated. -/
theorem isGloballyGenerated_of_regular_of_isClosedImmersion [IsNoetherianRing R]
    (F : X.Modules) [F.IsCoherent] (n : ℕ) (hdim : topologicalKrullDim X ≤ (n : WithBot ℕ∞))
    (hvan : ∀ m : ℤ, -(n : ℤ) ≤ m → ∀ i : ℕ, 0 < i →
      IsZero (Hgroup X.ringCatSheaf ⊤ i (tensorModules X F (tensorPowModule X L m)))) :
    MMP.Intersection.IsGloballyGenerated F := by
  have hcompact : CompactSpace X := ι.isClosedEmbedding.compactSpace
  have : IsLocallyNoetherian X := isLocallyNoetherian_of_isClosedImmersion ι
  have : IsNoetherian X := ⟨⟩
  have hG : ((Scheme.Modules.pushforward ι).obj F).IsCoherent :=
    isCoherent_pushforward_of_isClosedImmersion ι F
  have hLcoh (d : ℤ) : (tensorPowModule X L d).IsCoherent :=
    Stacks.AlgebraicGeometry.RelativeSerreVanishing.isCoherent_tensorPowModule L d
  have hEq (d : ℤ) : (tensorModules X F (tensorPowModule X L d)).IsQuasicoherent :=
    haveI : (tensorModules X F (tensorPowModule X L d)).IsCoherent :=
      AlgebraicGeometry.isCoherent_tensorBifunctorObj F _ inferInstance (hLcoh d)
    isQuasicoherent_of_isCoherent _
  refine isGloballyGenerated_of_isGeneratedByGlobalSections_pushforward ι F ?_
  have h0 := isGeneratedByGlobalSections_projectiveTwist_of_regular N
    ((Scheme.Modules.pushforward ι).obj F) 0 ?_
  · obtain ⟨σ⟩ := h0
    refine ⟨SheafOfModules.GeneratingSections.equivOfIso ?_ σ⟩
    refine projectiveTwistPushforwardIso ι L hL F 0 ≪≫ (Scheme.Modules.pushforward ι).mapIso ?_
    exact tensorModulesMapIso X (Iso.refl F) (tensorPowModuleZeroIso X L) ≪≫ ρ_ F
  · intro d hd i hi1 hiN
    refine ((Hfunctor (projectiveSpaceOverRing N (.of R)).ringCatSheaf ⊤ i).mapIso
      (projectiveTwistPushforwardIso ι L hL F (d - i))).isZero_iff.2 ?_
    refine (isZero_Hgroup_pushforward_iff ι _ (hEq _) i).2 ?_
    by_cases hin : i ≤ n
    · exact hvan _ (by omega) i hi1
    · exact isZero_Hgroup_of_topologicalKrullDim_le _ hdim (by omega)

end Core

section Transport

open Stacks.AmpleProjectiveImmersion in
/-- **Changing the affine base to `Spec Γ(Z)`.** A closed immersion `ι : X ⟶ ℙᴺ_Z` into projective
space over an affine scheme `Z`, with `L ≅ ι^*𝒪(1)`, gives a closed immersion into `ℙᴺ_{Γ(Z)}` with
`L ≅ ι'^*𝒪(1)`. -/
theorem exists_isClosedImmersion_projectiveSpaceOverRing {X Z : Scheme.{u}} [IsAffine Z]
    {N : ℕ} (ι : X ⟶ projectiveSpaceOver N Z) [IsClosedImmersion ι] (L : X.Modules)
    (hL : L ≅ (Scheme.Modules.pullback ι).obj (twistOver N Z 1)) :
    ∃ ι' : X ⟶ projectiveSpaceOverRing N (.of Γ(Z, ⊤)), IsClosedImmersion ι' ∧
      Nonempty (L ≅ (Scheme.Modules.pullback ι').obj (twistOver N (Spec (.of Γ(Z, ⊤))) 1)) := by
  let e : Z ≅ Spec (.of Γ(Z, ⊤)) := Scheme.isoSpec Z
  let φ : projectiveSpaceOver N Z ⟶ projectiveSpaceOver N (Spec (.of Γ(Z, ⊤))) :=
    pullback.map _ _ _ _ e.hom (𝟙 _) (𝟙 _) (terminal.hom_ext _ _) (by simp)
  have : IsIso φ := by
    dsimp only [φ]
    infer_instance
  have hφ : φ ≫ pullback.snd _ _ = pullback.snd _ _ := by simp [φ]
  refine ⟨ι ≫ φ, inferInstance, ⟨hL ≪≫ ?_⟩⟩
  refine (Scheme.Modules.pullback ι).mapIso ?_ ≪≫ (Scheme.Modules.pullbackComp ι φ).app _
  exact ((Scheme.Modules.pullbackComp φ (pullback.snd _ _)).app
    (twistingSheafAtUniverse N) ≪≫ eqToIso (by rw [hφ])).symm

end Transport

open Stacks.AmpleProjectiveImmersion in
/-- **Cohomological generation over an affine base** (Castelnuovo-Mumford regularity for a
relatively very ample divisor). Let `f : X ⟶ Z` be proper with `Z` affine and Noetherian, let `H`
be a Cartier divisor on `X` that is very ample relative to `Z`, i.e. `𝒪_X(H)` is the pull-back of
`𝒪(1)` along an immersion `X ⟶ ℙᴺ_Z` over `Z` (Stacks 01VS), and let `dim X ≤ n`. If a coherent
sheaf `ℱ` has `Hⁱ(X, ℱ(mH)) = 0` for every `i > 0` and every `m ≥ -n`, then `ℱ` is generated by
its global sections. -/
@[mmp "lem_fourfold_affine_base_regular_generation"]
theorem isGloballyGenerated_of_forall_isZero_Hgroup_twist {X Z : Scheme.{u}} [IsAffine Z]
    [IsNoetherian Z] (f : X ⟶ Z) [IsProper f] (H : X.CartierDivisor)
    (hH : HasImmersionTwistOver f (MMP.CartierDivisor.sheaf H)) (n : ℕ)
    (hdim : topologicalKrullDim X ≤ (n : WithBot ℕ∞))
    (F : X.Modules) [F.IsCoherent]
    (hvan : ∀ m : ℤ, -(n : ℤ) ≤ m → ∀ i : ℕ, 0 < i →
      IsZero (Hgroup X.ringCatSheaf ⊤ i (twist F (m • H)))) :
    MMP.Intersection.IsGloballyGenerated F := by
  obtain ⟨N, ι, hι, hover, ⟨e⟩⟩ := hH
  have : IsClosedImmersion ι :=
    Stacks.AmpleFormalSystemEmbeddedTuple.isClosedImmersion_of_isImmersion_over (f := f) ι hι hover
  obtain ⟨ι', hι', ⟨e'⟩⟩ := exists_isClosedImmersion_projectiveSpaceOverRing ι
      (MMP.CartierDivisor.sheaf H) e
  have hZ : IsLocallyNoetherian Z := ‹IsNoetherian Z›.toIsLocallyNoetherian
  have : IsNoetherianRing Γ(Z, ⊤) :=
    @IsLocallyNoetherian.component_noetherian _ hZ (⟨⊤, isAffineOpen_top Z⟩ : Z.affineOpens)
  refine isGloballyGenerated_of_regular_of_isClosedImmersion ι' (MMP.CartierDivisor.sheaf H) e' F n
      hdim ?_
  intro m hm i hi
  refine ((Hfunctor X.ringCatSheaf ⊤ i).mapIso ?_).isZero_iff.1 (hvan m hm i hi)
  exact tensorModulesMapIso X (Iso.refl F) (nonempty_lineBundle_int_smul_iso H m).some

end AffineBase

end MMP.Fourfold

end
