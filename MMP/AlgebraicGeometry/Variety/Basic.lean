module

public import MMP.Attr
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Topology.Sheaves.CommRingCat
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.TotalQuotient
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Relative
public import StacksFrontier.AlgebraicGeometry.SegreEmbedding.PolyChart
public import StacksFrontier.Topology.Dimension.Codimension

/-!
# Basic notions on schemes (Fulton, Appendix B; Lazarsfeld's conventions)

This file collects the scheme-theoretic background of the intersection-theory part of the
library. Where Mathlib already has the notion, its declaration is used as is
(often in greater generality than the source, e.g. `IsProper` for any morphism of schemes).
Where the source's notion is specific, a small definition is built from Mathlib's API.

Several notions are the Stacks project's: birational morphisms (`AlgebraicGeometry.IsBirational`),
the sheaf of relative differentials (`AlgebraicGeometry.Scheme.Hom.relativeDifferentials`), the
codimension of an irreducible closed subset (`codimension`), the dehomogenisation isomorphism of
the affine charts of projective space, and the sheaf of total quotient rings.

## Main definitions

All declarations of this file are in the namespace `MMP.Intersection`; a name of Mathlib's
`AlgebraicGeometry` namespace keeps its tail, e.g. `MMP.Intersection.Scheme.Subvariety`. Since the
head namespace is not `AlgebraicGeometry.Scheme`, dot notation on a scheme or a morphism does not
reach them: write `Scheme.Subvariety X`, `Scheme.Hom.HasRelativeDimension f n`.

* `MMP.Intersection.IsAlgebraicScheme K X`: `X` is of finite type over `Spec K`.
* `MMP.Intersection.IsIntegralAlgebraicScheme K X`: a variety over `K` (Fulton), i.e. an
  integral algebraic scheme over `K`.
* `MMP.Intersection.IsSeparatedAlgebraicScheme K X`: `X` is separated and of finite type over
  `Spec K` (Lazarsfeld's "scheme").
* `MMP.Intersection.IsComplete K X`: `X` is proper over `Spec K`.
* `MMP.Intersection.Scheme.Subvariety X`: an integral closed subscheme of `X`,
  with its generic point, local ring `𝒪_{V,X}`, function field `R(V)`, codimension,
  image under a morphism and the induced embedding of function fields.
* `MMP.Intersection.Scheme.dimension`: the Krull dimension of the underlying space, and
  `MMP.Intersection.Scheme.dimensionOfClosed` for a closed subset.
* `MMP.Intersection.IsNormalVariety`, `MMP.Intersection.Scheme.integralNormalization`,
  `MMP.Intersection.ProjSpace` and its affine charts `MMP.Intersection.ProjSpace.affineChart`,
  `MMP.Intersection.Scheme.Hom.HasRelativeDimension`,
  `MMP.Intersection.Scheme.Hom.IsSmoothOfRelativeDimension`,
  `MMP.Intersection.Scheme.IdealSheafData.codim`,
  and the sheaves of units `MMP.Intersection.TopCat.Sheaf.units`,
  `MMP.Intersection.Scheme.structureSheafUnits`, `MMP.Intersection.Scheme.totalQuotientSheafUnits`.

The sheaf `𝒦_X` of total quotient rings (Fulton B.4.1) is the Stacks project's
`AlgebraicGeometry.Scheme.totalQuotientSheaf`: the sheafification of the presheaf of rings
`U ↦ S(U)⁻¹ 𝒪_X(U)`, where `S(U)` consists of the sections whose germs are non-zero-divisors in
every stalk. On an affine open of a locally Noetherian scheme, `S(U)` is the set of
non-zero-divisors of `A(U)`, so this is Fulton's sheaf associated to `U ↦ K(A(U))`.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory TopologicalSpace

namespace MMP.Intersection

open AlgebraicGeometry

/-- The sheaf of units `𝒢ˣ` of a sheaf of commutative rings `𝒢`. -/
def TopCat.Sheaf.units {T : TopCat.{u}} (F : TopCat.Sheaf CommRingCat.{u} T) :
    TopCat.Sheaf CommGrpCat.{u} T :=
  (sheafCompose _ (forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units)).obj F

/-! ### Schemes over a field -/

section OverField

variable (K : Type u) [Field K] (X : Scheme.{u}) [X.Over (Spec (.of K))]

/-- An *algebraic scheme over `K`* (Fulton B.1.1): a scheme whose structure morphism to
`Spec K` is of finite type, i.e. locally of finite type and quasi-compact. -/
@[mmp "def_b_algebraic_scheme"]
class IsAlgebraicScheme : Prop where
  /-- The structure morphism to `Spec K` is locally of finite type. -/
  locallyOfFiniteType : LocallyOfFiniteType (X ↘ Spec (.of K))
  /-- The structure morphism to `Spec K` is quasi-compact. -/
  quasiCompact : QuasiCompact (X ↘ Spec (.of K))

/-- A *scheme* in the convention of Lazarsfeld (Notation and Conventions, p. 1): a scheme whose
structure morphism to `Spec K` is separated and of finite type. Lazarsfeld takes `K = ℂ`; any
field is allowed here. That its "points" are its closed points is a convention of language, not
extra structure. -/
@[mmp "def_pab_scheme"]
class IsSeparatedAlgebraicScheme : Prop extends IsAlgebraicScheme K X where
  /-- The structure morphism to `Spec K` is separated. -/
  isSeparated : IsSeparated (X ↘ Spec (.of K))

/-- A *variety over `K`* (Fulton B.1.2): an algebraic scheme over `K` which is integral,
i.e. reduced and irreducible. Unlike the Stacks project's `AlgebraicGeometry.IsVariety`, it does
not require the structure morphism to be separated. -/
@[mmp "def_b_variety"]
class IsIntegralAlgebraicScheme : Prop extends IsAlgebraicScheme K X, IsIntegral X

/-- A scheme over `K` is *complete* (Fulton B.2.4) if its structure morphism to `Spec K` is
proper. -/
@[mmp "def_b_complete_scheme"]
abbrev IsComplete : Prop := IsProper (X ↘ Spec (.of K))

end OverField

/-! ### Projective space -/

section ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Projective space over a commutative ring `R` with homogeneous coordinates indexed by `ι`:
the scheme `Proj R[xᵢ : i ∈ ι]` for the grading by total degree. Fulton's `ℙⁿ_K`
(Fulton B.1.4) is `ProjSpace K (ULift (Fin (n + 1)))`. -/
@[mmp "def_b_projective_space"]
abbrev ProjSpace (R : Type u) [CommRing R] (ι : Type u) : Scheme.{u} :=
  Proj (MvPolynomial.homogeneousSubmodule ι R)

namespace ProjSpace

open Stacks.AlgebraicGeometry.PolyChart (chartIso chartVar X_mem_one)

variable (R : Type u) [CommRing R] {ι : Type u} [DecidableEq ι] (i : ι)

/-- The standard affine chart `𝔸_R^{ι ∖ {i}} ⟶ ℙ_R^ι` onto `D₊(xᵢ) = {xᵢ ≠ 0}` (Fulton B.1.4):
the dehomogenisation isomorphism `R[xₖ : k ≠ i] ≅ R[x]_{(xᵢ)}`, `xₖ ↦ xₖ / xᵢ`, of the Stacks
project, followed by Mathlib's open immersion `Spec R[x]_{(xᵢ)} ⟶ Proj R[x]`. For Fulton's
`ℙⁿ_K = ProjSpace K (ULift (Fin (n + 1)))` and `i = 0` this is `𝔸ⁿ ≅ {x₀ ≠ 0}`. -/
@[mmp "def_b_projective_space"]
def affineChart : 𝔸({k : ι // k ≠ i}; Spec (.of R)) ⟶ ProjSpace R ι :=
  (AffineSpace.SpecIso _ (.of R)).hom ≫
    Spec.map (chartIso R i).toCommRingCatIso.hom ≫
      Proj.awayι (MvPolynomial.homogeneousSubmodule ι R) (MvPolynomial.X i) (X_mem_one R i)
        one_pos

/-- The affine chart is an open immersion. -/
@[mmp "def_b_projective_space"]
instance isOpenImmersion_affineChart : IsOpenImmersion (affineChart R i) := by
  unfold affineChart
  infer_instance

/-- The image of the affine chart is the basic open `D₊(xᵢ) = {xᵢ ≠ 0}`. -/
@[mmp "def_b_projective_space"]
theorem opensRange_affineChart :
    (affineChart R i).opensRange =
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι R) (MvPolynomial.X i) :=
  (Scheme.Hom.opensRange_comp_of_isIso _ _).trans
    ((Scheme.Hom.opensRange_comp_of_isIso _ _).trans (Proj.opensRange_awayι _ _ _ _))

/-- The affine coordinate `xₖ` of the chart is the degree-zero fraction `xₖ / xᵢ`. -/
@[mmp "def_b_projective_space"]
theorem chartIso_symm_X (k : {k : ι // k ≠ i}) :
    (chartIso R i).symm (MvPolynomial.X k) =
      HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule ι R) (X_mem_one R i) 1
        (MvPolynomial.X k.1) (by simpa using MvPolynomial.isHomogeneous_X R k.1) := by
  simp [Stacks.AlgebraicGeometry.PolyChart.toAway, chartVar]

end ProjSpace

end ProjSpace

namespace Scheme

variable {X Y : Scheme.{u}}

/-! ### Dimension -/

/-- The *dimension* of a scheme (Fulton B.1.3): the supremum of the lengths of chains of
subvarieties, i.e. of irreducible closed subsets, which is the Krull dimension of the
underlying topological space. -/
@[mmp "def_b_dimension"]
abbrev dimension (X : Scheme.{u}) : WithBot ℕ∞ := topologicalKrullDim X

/-- The dimension of a closed subset `Z` of a scheme (Fulton B.1.3): the dimension of the
reduced closed subscheme it supports. -/
@[mmp "def_b_dimension"]
abbrev dimensionOfClosed (Z : Closeds X) : WithBot ℕ∞ :=
  dimension (Scheme.IdealSheafData.vanishingIdeal Z).subscheme

/-! ### The reduced induced subscheme structure -/

namespace IdealSheafData

/-- The reduced induced subscheme structure on an irreducible closed set is irreducible. -/
theorem irreducibleSpace_subscheme_vanishingIdeal {Z : Closeds X}
    (hZ : IsIrreducible (Z : Set X)) :
    IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
  Subtype.irreducibleSpace hZ

end IdealSheafData

/-! ### Subvarieties -/

/-- A *subvariety* of a scheme `X` (Fulton B.1.2): a closed subscheme of `X`, given by its
ideal sheaf, which is reduced and irreducible, i.e. integral. -/
@[mmp "def_b_subvariety"]
structure Subvariety (X : Scheme.{u}) where
  /-- The ideal sheaf cutting out the subvariety. -/
  ideal : X.IdealSheafData
  /-- The closed subscheme is integral (reduced and irreducible). -/
  isIntegral : IsIntegral ideal.subscheme

namespace Subvariety

variable (V : Subvariety X)

/-- The underlying closed subset of a subvariety. -/
def support : Set X := V.ideal.support

/-- The generic point of a subvariety, as a point of the ambient scheme. -/
def genericPoint : X :=
  haveI := V.isIntegral
  V.ideal.subschemeι (_root_.genericPoint V.ideal.subscheme)

/-- The generic point of a subvariety is a generic point of its support. -/
theorem isGenericPoint_genericPoint : IsGenericPoint V.genericPoint V.support := by
  have := V.isIntegral
  have h := (genericPoint_spec V.ideal.subscheme).image V.ideal.subschemeι.continuous
  rwa [Set.image_univ, V.ideal.range_subschemeι,
    V.ideal.support.isClosed.closure_eq] at h

/-- The support of a subvariety is irreducible. -/
theorem isIrreducible_support : IsIrreducible V.support :=
  V.isGenericPoint_genericPoint.isIrreducible

/-- The support of a subvariety is closed. -/
theorem isClosed_support : IsClosed V.support :=
  V.ideal.support.isClosed

/-- The underlying irreducible closed subset of a subvariety. -/
def toIrreducibleCloseds : IrreducibleCloseds X :=
  ⟨V.support, V.isIrreducible_support, V.isClosed_support⟩

/-- The *local ring of `X` along `V`* (Fulton B.1.2): the stalk `𝒪_{V,X}` of the structure
sheaf at the generic point of `V`. -/
@[mmp "def_b_local_ring_along_subvariety"]
abbrev localRing : CommRingCat := X.presheaf.stalk V.genericPoint

/-- The maximal ideal `𝔪_{V,X}` of the local ring of `X` along `V`. -/
@[mmp "def_b_local_ring_along_subvariety"]
abbrev maximalIdeal : Ideal V.localRing := IsLocalRing.maximalIdeal V.localRing

/-- The *function field* `R(V)` of a subvariety (Fulton B.1.2): the residue field
`𝒪_{V,X}/𝔪_{V,X}` of the local ring of `X` along `V`. -/
@[mmp "def_b_function_field"]
abbrev functionField : CommRingCat := X.residueField V.genericPoint

/-- The *codimension* `codim(V, X)` (Fulton B.1.3): the supremum of the lengths `d` of chains
of subvarieties `V = V₀ ⊊ V₁ ⊊ ⋯ ⊊ V_d ⊆ X`, i.e. the Stacks project's `codimension` (the
coheight among the irreducible closed subsets of `X`) of the support of `V`. -/
@[mmp "def_b_codimension"]
abbrev codim : ℕ∞ := codimension V.toIrreducibleCloseds

/-- The subvariety given by the reduced induced subscheme structure on an irreducible closed
subset. -/
def ofIsIrreducible (Z : Closeds X) (hZ : IsIrreducible (Z : Set X)) : Subvariety X where
  ideal := Scheme.IdealSheafData.vanishingIdeal Z
  isIntegral :=
    haveI := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal Z
    haveI := IdealSheafData.irreducibleSpace_subscheme_vanishingIdeal hZ
    isIntegral_of_irreducibleSpace_of_isReduced _

/-- The *image subvariety* `\overline{f(V)}` (Fulton B.2.2): the closure of `f(V)` with its
reduced induced closed subscheme structure. -/
@[mmp "def_b_image_of_subvariety"]
def image (f : X ⟶ Y) : Subvariety Y :=
  ofIsIrreducible ⟨closure (f '' V.support), isClosed_closure⟩
    (V.isIrreducible_support.image f f.continuous.continuousOn).closure

/-- A morphism maps the generic point of a subvariety to the generic point of its image. -/
theorem genericPoint_image (f : X ⟶ Y) : (V.image f).genericPoint = f V.genericPoint :=
  (V.image f).isGenericPoint_genericPoint.eq (V.isGenericPoint_genericPoint.image f.continuous)

/-- The *induced embedding of function fields* `f^* : R(W) ↪ R(V)` (Fulton B.2.2), for
`W = \overline{f(V)}`: the homomorphism of residue fields induced by the local homomorphism of
stalks `𝒪_{W,Y} → 𝒪_{V,X}`. -/
@[mmp "def_b_induced_function_field_embedding"]
def functionFieldMap (f : X ⟶ Y) : (V.image f).functionField ⟶ V.functionField :=
  (Y.residueFieldCongr (V.genericPoint_image f)).hom ≫ f.residueFieldMap V.genericPoint

end Subvariety

/-! ### Codimension of a closed subscheme (Lazarsfeld) -/

/-- The *codimension* of a closed subscheme `W` of `X` (Lazarsfeld, App. B): the minimum of
`dim 𝒪_{X,η}` over the generic points `η` of the irreducible components of `W`, which is `⊤`
when `W` is empty. -/
@[mmp "def_pab_codimension"]
def IdealSheafData.codim (W : X.IdealSheafData) : WithBot ℕ∞ :=
  ⨅ (η : W.subscheme) (_ : closure {η} ∈ irreducibleComponents W.subscheme),
    ringKrullDim (X.presheaf.stalk (W.subschemeι η))

/-! ### Morphisms -/

/-- A morphism `f : X ⟶ Y` *has relative dimension `n`* (Fulton B.2.5): for every subvariety
`V` of `Y` and every irreducible component `V'` of `f⁻¹(V)`, `dim V' = dim V + n`. -/
@[mmp "def_b_relative_dimension"]
def Hom.HasRelativeDimension (f : X ⟶ Y) (n : ℕ) : Prop :=
  ∀ V : Subvariety Y, ∀ V' ∈ irreducibleComponents (f ⁻¹' V.support),
    topologicalKrullDim V' = topologicalKrullDim V.support + n

/-- A morphism `f : X ⟶ Y` is *smooth of relative dimension `n`* in Fulton's sense (B.2.7):
`f` is flat of relative dimension `n`, locally of finite type and separated, and `Ω¹_{X/Y}` is
locally free of rank `n`. The last condition is stated affine-locally: on an affine open `V` of
`X` mapping into an affine open `U` of `Y`, `Ω¹_{X/Y}` is the sheaf associated to the module
`Ω_{Γ(V)/Γ(U)}`, which is required to be free of rank `n` around every point. -/
@[mmp "def_b_smooth_morphism"]
def Hom.IsSmoothOfRelativeDimension (f : X ⟶ Y) (n : ℕ) : Prop :=
  Flat f ∧ HasRelativeDimension f n ∧ LocallyOfFiniteType f ∧ IsSeparated f ∧
    ∀ x : X, ∃ (U : Y.Opens) (_ : IsAffineOpen U) (V : X.Opens) (_ : IsAffineOpen V) (_ : x ∈ V)
      (e : V ≤ f ⁻¹ᵁ U),
      letI := (f.appLE U V e).hom.toAlgebra
      Module.Free Γ(X, V) Ω[Γ(X, V)⁄Γ(Y, U)] ∧ Module.Finite Γ(X, V) Ω[Γ(X, V)⁄Γ(Y, U)] ∧
        Module.finrank Γ(X, V) Ω[Γ(X, V)⁄Γ(Y, U)] = n

end Scheme

/-! ### Normal varieties and normalization -/

/-- An integral scheme `X` is *normal* (Fulton B.2.6) if the coordinate ring of every nonempty
affine open subset is integrally closed in the function field `R(X)`. -/
@[mmp "def_b_normal_variety"]
def IsNormalVariety (X : Scheme.{u}) [IsIntegral X] : Prop :=
  ∀ U : X.Opens, IsAffineOpen U → ∀ [Nonempty U], IsIntegrallyClosedIn Γ(X, U) X.functionField

namespace Scheme

variable (X : Scheme.{u}) [IsIntegral X]

/-- The *normalization* `X̃` of an integral scheme `X` (Fulton B.2.6): the relative normalization
of `X` in `Spec R(X)`, glued from `Spec` of the integral closures of the coordinate rings `A(U)`
in `R(X)` over the affine opens `U` of `X`. -/
@[mmp "def_b_normalization"]
def integralNormalization : Scheme.{u} :=
  (X.fromSpecStalk (_root_.genericPoint X)).normalization

/-- The normalization morphism `X̃ ⟶ X`, induced by the inclusions `A(U) ⊆ \widetilde{A(U)}`. -/
@[mmp "def_b_normalization"]
def fromIntegralNormalization : integralNormalization X ⟶ X :=
  (X.fromSpecStalk (_root_.genericPoint X)).fromNormalization

end Scheme

/-! ### Total quotient rings and units -/

namespace Scheme

variable (X : Scheme.{u})

/-- The sheaf `𝒪_X^*` of units of the structure sheaf (Fulton B.4.1). -/
@[mmp "not_b_sheaf_of_units"]
abbrev structureSheafUnits : TopCat.Sheaf CommGrpCat.{u} X.carrier :=
  TopCat.Sheaf.units X.sheaf

/-- The sheaf `𝒦_X^*` of units of the sheaf of total quotient rings (Fulton B.4.1). -/
@[mmp "not_b_sheaf_of_units"]
abbrev totalQuotientSheafUnits : TopCat.Sheaf CommGrpCat.{u} X.carrier :=
  TopCat.Sheaf.units X.totalQuotientSheaf

end Scheme

end MMP.Intersection
