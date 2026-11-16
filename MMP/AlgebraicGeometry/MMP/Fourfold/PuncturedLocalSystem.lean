module

public import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting
public import MMP.AlgebraicGeometry.Analytic.BorelMoore
public import MMP.AlgebraicTopology.SingularCohomology.Relative
public import MMP.AlgebraicTopology.ComplexVectorBundle.FirstChernClass
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Functors

/-!
# The punctured local system along a singular curve, and the resolution local system

Let `Y` be a normal complex fourfold, `j : Y_reg ↪ Y` the inclusion of the smooth locus, and
`T ⊆ Sing Y` an irreducible curve. A *local-system open* of `T` is a connected smooth dense
Zariski-open `T° ⊆ T` on which the restriction of the sheaf `R²j_* ℚ_{Y_reg}` on `Y^an` is a
local system; this restriction is the *punctured local system* `𝒱_T = (R²j_* ℚ_{Y_reg})|_{T°}`.

Given moreover a resolution `π : Ỹ ⟶ Y` which is an isomorphism over `Y_reg`, a *`π`-adapted
open* is a local-system open `T°` on which `R²π_* ℚ_Ỹ` restricts to a local system, over whose
points the scheme fibres of `π` have dimension at most two, and over which
`Ỹ ×_Y T° ⟶ T°` is flat and projective. Its *resolution local system* is
`𝒲 = (R²π_* ℚ_Ỹ)|_{T°}`, and restriction of classes to `π⁻¹(Y_reg) ≅ Y_reg` gives the map
`r : R²π_* ℚ_Ỹ ⟶ R²π_* ℚ_{π⁻¹(Y_reg)} = R²j_* ℚ_{Y_reg}`, whose restriction to `T°` is
`r : 𝒲 ⟶ 𝒱_T`.

## Main definitions

* `MMP.Fourfold.higherDirectImage f q`: the higher direct image `R^q f_* ℚ_X` of the constant
  sheaf along a continuous map `f`, with its germs `MMP.Fourfold.higherDirectImageGerm`.
* `MMP.Fourfold.higherDirectImageRestriction p g h q`: for `g : U ⟶ X`, `p : X ⟶ Y` and
  `j = g ≫ p`, the map `R^q p_* ℚ_X ⟶ R^q j_* ℚ_U` induced by restriction of classes along `g`.
* `MMP.Fourfold.compactSupportCohomology R q F`: cohomology with compact supports `H^q_c(X, F)`.
* `MMP.Fourfold.IsLocalSystem`: a sheaf of `ℚ`-vector spaces which is locally isomorphic to the
  constant sheaf of a finite-dimensional vector space.
* `MMP.Analytic.ComplexPoints.analyticMap`: the realization `X^an ⟶ Y^an` of a morphism over `ℂ`,
  as a morphism of topological spaces.
* `MMP.Fourfold.IsLocalSystemOpen`, `MMP.Fourfold.curveLocalSystem`: local-system opens `T°` and
  the punctured local system `𝒱_T`, with its fibre `MMP.Fourfold.curveLocalSystemFibre`.
* `MMP.Fourfold.curveLocalSystemRank`: the rank `b_T = dim_ℚ H²_c(T°, 𝒱_T)`.
* `MMP.Fourfold.IsAdaptedOpen`: `π`-adapted opens.
* `MMP.Fourfold.resolutionLocalSystem`: the resolution local system `𝒲`, with its fibre
  `MMP.Fourfold.resolutionLocalSystemFibre`.
* `MMP.Fourfold.localSystemRestriction`: `r : 𝒲 ⟶ 𝒱_T`, with its fibres
  `MMP.Fourfold.localSystemRestrictionFibre`.
* `MMP.Fourfold.pointFibre`, `MMP.Fourfold.pointFibreChernClass`: the scheme fibre `F_t` over a
  `ℂ`-point `t` of `T°`, and `c₁(M) ∈ H²(F_t; ℚ)` of an invertible module on it.
* `MMP.Fourfold.IsPuncturedIndependent`: punctured-independent families of line bundles on the
  generic scheme fibre `F_{η_T}`.

## Main results

* `MMP.Analytic.ComplexPoints.continuous_realize`: realized maps are continuous.
* `MMP.Fourfold.regularSection_comp`: the inverse of `π` over `Y_reg` is a section of `π`.

## Implementation notes

* `R^q f_* ℚ_X` is the sheaf associated to the presheaf `V ↦ H^q(f⁻¹(V); ℚ)` of singular
  cohomology (`MMP.cohomologyWithSupports` with full support). On the complex
  analytic spaces considered, which are locally contractible, this is the derived functor higher
  direct image of the constant sheaf, by the comparison of singular and sheaf cohomology; the
  singular form is used because the first Chern classes are singular classes and the maps below
  are restrictions of singular classes.
* The restriction map `r` is induced by the maps `H^q(π⁻¹(V); ℚ) ⟶ H^q(j⁻¹(V); ℚ)` of pullback
  along `j⁻¹(V) ≅ π⁻¹(V) ∩ π⁻¹(Y_reg) ⊆ π⁻¹(V)`. It is formed for the section `g : Y_reg ⟶ Ỹ`
  of `π` over `Y_reg` (`MMP.Fourfold.regularSection`), whose realization composed with `π^an` is
  `j^an`.
* The analytic space of a scheme `X` over `ℂ` is its complex realization
  (`MMP.Analytic.ComplexPoints`); that of an open subscheme `U ⊆ X` is the complex realization
  of `U` with the structure morphism `U.ι ≫ s_X`. The restriction of a sheaf on `Y^an` to
  `T°` is its inverse image along the realization of `T° ⟶ Y`.
* The curve `T` carries its reduced structure, the closed subscheme cut out by its vanishing
  ideal (`MMP.Fourfold.curveScheme`); a Zariski-open `T° ⊆ T` is an open of that scheme, and
  "smooth" is smoothness of `T° ⟶ Spec ℂ`. Its points are the closed points and `η_T`, so the
  fibre condition is stated for every point of `T°`, with `F_y = Ỹ ×_Y Spec κ(y)` the scheme
  fibre at its image `y ∈ Y`.
* A local system is a locally constant sheaf of finite-dimensional `ℚ`-vector spaces: every
  point has an open neighbourhood `V` such that the inverse image of the sheaf along `V ↪ X` is
  isomorphic to the constant sheaf of a finite-dimensional `ℚ`-vector space.
* `H^q_c(X, F)` is the `q`-th right derived functor of the functor `Γ_c` of global sections whose
  germs vanish outside a compact set, computed by injective resolutions. On the Hausdorff spaces
  `T°(ℂ)` the support of a section is closed, so this is the condition that the support be
  compact. `b_T` is `Module.finrank`, which is `0` for an infinite-dimensional space; that
  `H²_c(T°, 𝒱_T)` is finite-dimensional for a local system on a smooth curve is a separate
  statement, not part of the definition.
* The fibre of a local system at a point `t` of `T°^an` is its stalk at `t`; a germ at `t` of a
  section of a sheaf on `Y^an` is carried to it by `MMP.Fourfold.stalkToPullbackStalk`.
* **Punctured independence.** The class `c₁(𝓛_i|_{F_t})` lies in `H²(F_t; ℚ)` and `r` starts at
  `𝒲_t`; the source passes from one to the other by proper base change, which identifies `𝒲_t`
  with `H²(F_t; ℚ)` through the restriction map
  `𝒲_t = colim_{V ∋ t} H²(π⁻¹(V); ℚ) ⟶ H²(F_t; ℚ)`. The condition is stated with that map,
  which exists without the theorem: for every `ℂ`-point `t` of `T¹` there are a neighbourhood `V`
  of `t` in `Y^an` and classes `α_i ∈ H²(π⁻¹(V); ℚ)` restricting to `c₁(𝓛_i|_{F_t})` on `F_t`
  whose germs `w_i ∈ 𝒲_t` have linearly independent images `r(w_i)` in `𝒱_{T,t}`. As the map
  from `H²(π⁻¹(V); ℚ)` to the stalk is onto in the colimit, and proper base change makes the
  restriction to `F_t` an isomorphism, `w_i` is then the class `c₁(𝓛_i|_{F_t})` of the source,
  and the condition is the source's.
* `F_t = Ỹ ×_Y Spec ℂ` is the scheme fibre over the `ℂ`-point `t`, a scheme over `ℂ` through its
  second projection, and `𝓛_i|_{F_t}` is the pullback of modules along `F_t ⟶ Ỹ ×_Y T¹`; its
  first Chern class is `MMP.Analytic.algebraicFirstChernClass`, carried to `ℚ`-coefficients. The
  closed points of `T¹` are its `ℂ`-points.
* "`𝓛_i` has generic fibre `L_i`" is stated over the generic point `ξ` of `T¹` (the point over
  `η_T`): the pullbacks of `𝓛_i` and `L_i` to `Ỹ ×_Y Spec κ(ξ)` are isomorphic, where
  `Ỹ ×_Y Spec κ(ξ) ⟶ F_{η_T}` is induced by the residue field map `K_T = κ(η_T) ⟶ κ(ξ)`. That
  map is an isomorphism (`T¹ ⟶ Y` is an immersion), so this is the source's condition.
* Line bundles are invertible modules (`SheafOfModules.IsInvertible`). Invertibility of the
  restrictions `𝓛_i|_{F_t}`, needed to form their Chern classes, is asked for alongside; it
  holds for the pullback of an invertible module.
* The definitions make sense without the standing assumptions of the source (normal fourfold,
  `T ⊆ Sing Y` an irreducible curve, `(Y, Θ, T, π)` a local setting); they are not imposed here,
  except that `π` is an isomorphism over `Y_reg`, which the restriction map uses.

## References

* [Kollár–Mori, *Birational geometry of algebraic varieties*]
* [Iversen, *Cohomology of sheaves*], II.5, III.1 and VII.1 for higher direct images, the
  comparison with singular cohomology and proper base change.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Opposite MMP

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

attribute [local instance] HasDerivedCategory.standard

namespace MMP.Fourfold

open MMP.Mori

/-! ### Higher direct images of the constant sheaf -/

section HigherDirectImage

/-- The singular cohomology `H^q(X; ℚ)` of a topological space. -/
abbrev rationalCohomology (X : TopCat.{0}) (q : ℕ) : ModuleCat.{0} ℚ :=
  cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) X Set.univ q

/-- The pullback `f^* : H^q(X; ℚ) ⟶ H^q(X'; ℚ)` along a continuous map `f : X' ⟶ X`. -/
def rationalCohomologyMap {X' X : TopCat.{0}} (f : X' ⟶ X) (q : ℕ) :
    rationalCohomology X q ⟶ rationalCohomology X' q :=
  relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) f (fun _ hx ↦ absurd (Set.mem_univ _) hx) q

/-- Pullback along the identity is the identity on `H^q(X; ℚ)`. -/
lemma rationalCohomologyMap_id (X : TopCat.{0}) (q : ℕ) :
    rationalCohomologyMap (𝟙 X) q = 𝟙 _ :=
  relativeSingularCohomology.map_id _ _ _ _ _

/-- Pullback along `g ≫ f` is pullback along `f` followed by pullback along `g`. -/
lemma rationalCohomologyMap_comp {X'' X' X : TopCat.{0}} (g : X'' ⟶ X') (f : X' ⟶ X) (q : ℕ) :
    rationalCohomologyMap (g ≫ f) q = rationalCohomologyMap f q ≫ rationalCohomologyMap g q :=
  relativeSingularCohomology.map_comp _ _ g f _ _ _

variable {X Y U : TopCat.{0}}

/-- The preimage `f⁻¹(V)` of an open `V ⊆ Y`, as a topological space. -/
abbrev preimageSpace (f : X ⟶ Y) (V : Opens Y) : TopCat.{0} :=
  TopCat.of (f ⁻¹' (V : Set Y))

/-- The inclusion `f⁻¹(V) ⟶ f⁻¹(W)` for opens `V ≤ W`. -/
def preimageInclusion (f : X ⟶ Y) {V W : Opens Y} (h : V ≤ W) :
    preimageSpace f V ⟶ preimageSpace f W :=
  TopCat.ofHom ⟨Set.inclusion (Set.preimage_mono h), continuous_inclusion _⟩

/-- The presheaf `V ↦ H^q(f⁻¹(V); ℚ)` on `Y`, for a continuous map `f : X ⟶ Y`. -/
def directImagePresheaf (f : X ⟶ Y) (q : ℕ) : TopCat.Presheaf (ModuleCat.{0} ℚ) Y where
  obj V := rationalCohomology (preimageSpace f V.unop) q
  map i := rationalCohomologyMap (preimageInclusion f i.unop.le) q
  map_id V := by
    rw [← rationalCohomologyMap_id]
    rfl
  map_comp i i' := by
    rw [← rationalCohomologyMap_comp]
    rfl

/-- The higher direct image `R^q f_* ℚ_X` of the constant sheaf along a continuous map
`f : X ⟶ Y`: the sheaf associated to the presheaf `V ↦ H^q(f⁻¹(V); ℚ)`. -/
def higherDirectImage (f : X ⟶ Y) (q : ℕ) : TopCat.Sheaf (ModuleCat.{0} ℚ) Y :=
  (presheafToSheaf (Opens.grothendieckTopology Y) (ModuleCat.{0} ℚ)).obj
    (directImagePresheaf f q)

/-- The germ at `y ∈ V` in `(R^q f_* ℚ_X)_y` of a class of `H^q(f⁻¹(V); ℚ)`. -/
def higherDirectImageGerm (f : X ⟶ Y) (q : ℕ) {V : Opens Y} (y : Y) (hy : y ∈ V) :
    rationalCohomology (preimageSpace f V) q ⟶
      ((TopCat.Sheaf.forget _ Y).obj (higherDirectImage f q)).stalk y :=
  (directImagePresheaf f q).germ V y hy ≫
    (TopCat.Presheaf.stalkFunctor _ y).map (toSheafify _ (directImagePresheaf f q))

/-- For continuous maps `g : U ⟶ X`, `p : X ⟶ Y` and `j = g ≫ p`, the restriction of `g` to
`j⁻¹(V) ⟶ p⁻¹(V)`. -/
def preimageRestrict (p : X ⟶ Y) (g : U ⟶ X) {j : U ⟶ Y} (h : g ≫ p = j) (V : Opens Y) :
    preimageSpace j V ⟶ preimageSpace p V :=
  TopCat.ofHom ⟨fun x ↦ ⟨g x.1, Set.mem_preimage.2 (by
      rw [← ConcreteCategory.comp_apply, h]; exact x.2)⟩,
    (g.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- The morphism of presheaves `H^q(p⁻¹(V); ℚ) ⟶ H^q(j⁻¹(V); ℚ)` given by pullback of classes
along `g`, for `j = g ≫ p`. -/
def directImageRestriction (p : X ⟶ Y) (g : U ⟶ X) {j : U ⟶ Y} (h : g ≫ p = j) (q : ℕ) :
    directImagePresheaf p q ⟶ directImagePresheaf j q where
  app V := rationalCohomologyMap (preimageRestrict p g h V.unop) q
  naturality V W i := by
    dsimp [directImagePresheaf]
    rw [← rationalCohomologyMap_comp, ← rationalCohomologyMap_comp]
    rfl

/-- The map `R^q p_* ℚ_X ⟶ R^q j_* ℚ_U` induced by restriction of classes along `g`, for
`j = g ≫ p`. -/
def higherDirectImageRestriction (p : X ⟶ Y) (g : U ⟶ X) {j : U ⟶ Y} (h : g ≫ p = j)
    (q : ℕ) : higherDirectImage p q ⟶ higherDirectImage j q :=
  (presheafToSheaf _ _).map (directImageRestriction p g h q)

/-- The canonical map `F_{f(x)} ⟶ (f^* F)_x` from the stalk of a sheaf to the stalk of its
inverse image, induced by the unit `F ⟶ f_* f^* F`. -/
def stalkToPullbackStalk (f : X ⟶ Y) (F : TopCat.Sheaf (ModuleCat.{0} ℚ) Y) (x : X) :
    ((TopCat.Sheaf.forget _ Y).obj F).stalk (f x) ⟶
      ((TopCat.Sheaf.forget _ X).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj F)).stalk
        x :=
  (TopCat.Presheaf.stalkFunctor _ (f x)).map ((TopCat.Sheaf.forget _ Y).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app F)) ≫
    TopCat.Presheaf.stalkPushforward _ f _ x

end HigherDirectImage

/-! ### Cohomology with compact supports -/

section CompactSupport

variable (R : Type) [CommRing R] {X : TopCat.{0}}

/-- The global sections with compact support of a sheaf of `R`-modules: the sections whose
germs vanish outside a compact subset. -/
def compactSupportSections (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    Submodule R (((TopCat.Sheaf.forget _ X).obj F).obj (op ⊤)) where
  carrier := {s | ∃ K : Set X, IsCompact K ∧ ∀ x ∉ K,
    ((TopCat.Sheaf.forget _ X).obj F).germ ⊤ x (Opens.mem_top x) s = 0}
  zero_mem' := ⟨∅, isCompact_empty, fun _ _ ↦ map_zero _⟩
  add_mem' := by
    rintro s t ⟨K, hK, hs⟩ ⟨L, hL, ht⟩
    refine ⟨K ∪ L, hK.union hL, fun x hx ↦ ?_⟩
    simp only [Set.mem_union, not_or] at hx
    rw [map_add, hs x hx.1, ht x hx.2, add_zero]
  smul_mem' := by
    rintro c s ⟨K, hK, hs⟩
    exact ⟨K, hK, fun x hx ↦ by rw [map_smul, hs x hx, smul_zero]⟩

/-- The functor `Γ_c` of global sections with compact support. -/
def compactSupportSectionsFunctor : TopCat.Sheaf (ModuleCat.{0} R) X ⥤ ModuleCat.{0} R where
  obj F := ModuleCat.of R (compactSupportSections R F)
  map {F G} φ := ModuleCat.ofHom
    { toFun := fun s ↦ ⟨((TopCat.Sheaf.forget _ X).map φ).app (op ⊤) s.1, by
        obtain ⟨K, hK, hs⟩ := s.2
        refine ⟨K, hK, fun x hx ↦ ?_⟩
        rw [← TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ x (Opens.mem_top x)
          ((TopCat.Sheaf.forget _ X).map φ) s.1, hs x hx]
        exact map_zero _⟩
      map_add' := fun s t ↦ Subtype.ext (map_add _ _ _)
      map_smul' := fun c s ↦ Subtype.ext (map_smul _ _ _) }
  map_id F := by ext s; rfl
  map_comp φ ψ := by ext s; rfl

/-- The functor `Γ_c` is additive. -/
instance compactSupportSectionsFunctor_additive :
    (compactSupportSectionsFunctor R (X := X)).Additive where
  map_add := by intros; ext s; rfl

/-- The cohomology with compact supports `H^q_c(X, F)`: the `q`-th cohomology of the right
derived functor of `Γ_c`, applied to `F` placed in degree `0`. -/
def compactSupportCohomology (q : ℤ) (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    ModuleCat.{0} R :=
  (DerivedCategory.Plus.homologyFunctor _ q).obj
    ((compactSupportSectionsFunctor R).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F))

end CompactSupport

/-! ### Local systems -/

/-- A *local system* on a topological space `X`: a sheaf of `ℚ`-vector spaces such that every
point has an open neighbourhood `V` on which it is isomorphic to the constant sheaf of a
finite-dimensional `ℚ`-vector space. -/
def IsLocalSystem {X : TopCat.{0}} (F : TopCat.Sheaf (ModuleCat.{0} ℚ) X) : Prop :=
  ∀ x : X, ∃ (V : Opens X) (_ : x ∈ V) (E : ModuleCat.{0} ℚ), FiniteDimensional ℚ E ∧
    Nonempty ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) V.inclusion').obj F ≅
      (constantSheaf (Opens.grothendieckTopology _) (ModuleCat.{0} ℚ)).obj E)

/-! ### Realized maps of complex points -/

end MMP.Fourfold

namespace MMP.Analytic.ComplexPoints

variable {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)}

/-- The realized map `X(ℂ) → Y(ℂ)` of a morphism over `ℂ` is continuous. -/
@[mmp "lem_mmp_realization_continuous"]
theorem continuous_realize (g : X ⟶ Y) (hg : g ≫ sY = sX) : Continuous (realize g hg) := by
  let : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  let : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  have : g.IsOver (Spec (.of ℂ)) := ⟨hg⟩
  exact (homeomorphUnderlyingSpace (X := Y)).symm.continuous.comp
    ((MMP.UnderlyingSpace.continuous_mapFun (K := ℂ) g).comp
      (homeomorphUnderlyingSpace (X := X)).continuous)

/-- The complex realization `X^an` of a scheme over `ℂ`, as a topological space. -/
abbrev analyticSpace (sX : X ⟶ Spec (.of ℂ)) : TopCat.{0} :=
  TopCat.of (ComplexPoints sX)

/-- The realization `X^an ⟶ Y^an` of a morphism `g : X ⟶ Y` over `ℂ`. -/
def analyticMap (g : X ⟶ Y) (hg : g ≫ sY = sX) : analyticSpace sX ⟶ analyticSpace sY :=
  TopCat.ofHom ⟨realize g hg, continuous_realize g hg⟩

/-- `analyticMap g hg` sends a point `x` to its image `realize g hg x`. -/
@[simp]
lemma analyticMap_apply (g : X ⟶ Y) (hg : g ≫ sY = sX) (x : ComplexPoints sX) :
    analyticMap g hg x = realize g hg x :=
  rfl

/-- The realization of a composite is the composite of the realizations. -/
lemma analyticMap_comp {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)} (g : X ⟶ Y) (hg : g ≫ sY = sX)
    (h : Y ⟶ Z) (hh : h ≫ sZ = sY) :
    analyticMap g hg ≫ analyticMap h hh =
      analyticMap (g ≫ h) (by rw [Category.assoc, hh, hg]) := by
  ext x
  change (x.hom ≫ g) ≫ h = x.hom ≫ g ≫ h
  exact Category.assoc _ _ _

end MMP.Analytic.ComplexPoints

namespace MMP.Fourfold

open MMP.Mori MMP.Analytic MMP.Analytic.ComplexPoints

/-! ### The punctured local system of a curve -/

section CurveLocalSystem

variable {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) (T : IrreducibleCloseds Y)

/-- The curve `T`, with its reduced structure: the closed subscheme of `Y` cut out by the
vanishing ideal of `T`. -/
abbrev curveScheme : Scheme.{0} :=
  (Scheme.IdealSheafData.vanishingIdeal ⟨(T : Set Y), T.isClosed⟩).subscheme

/-- The closed immersion `T ⟶ Y`. -/
abbrev curveι : curveScheme T ⟶ Y :=
  (Scheme.IdealSheafData.vanishingIdeal ⟨(T : Set Y), T.isClosed⟩).subschemeι

variable {T}

/-- The realization `T°^an ⟶ Y^an` of the inclusion of a Zariski-open `T° ⊆ T`. -/
def curveOpenInclusion (To : (curveScheme T).Opens) :
    analyticSpace (To.ι ≫ curveι T ≫ sY) ⟶ analyticSpace sY :=
  analyticMap (To.ι ≫ curveι T) (Category.assoc _ _ _)

/-- The realization `j^an : Y_reg^an ⟶ Y^an` of the inclusion of the smooth locus. -/
def regularInclusion : analyticSpace ((smoothLocus sY).ι ≫ sY) ⟶ analyticSpace sY :=
  analyticMap (smoothLocus sY).ι rfl

/-- The sheaf `R^q j_* ℚ_{Y_reg}` on `Y^an`, for `j : Y_reg ↪ Y` the smooth locus. -/
abbrev regularHigherDirectImage (q : ℕ) : TopCat.Sheaf (ModuleCat.{0} ℚ) (analyticSpace sY) :=
  higherDirectImage (regularInclusion sY) q

/-- The *punctured local system* `𝒱_T = (R²j_* ℚ_{Y_reg})|_{T°}` on a Zariski-open `T° ⊆ T`:
the inverse image of `R²j_* ℚ_{Y_reg}` along `T°^an ⟶ Y^an`. -/
@[mmp "def_oai4_curve_local_system"]
def curveLocalSystem (To : (curveScheme T).Opens) :
    TopCat.Sheaf (ModuleCat.{0} ℚ) (analyticSpace (To.ι ≫ curveι T ≫ sY)) :=
  (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) (curveOpenInclusion sY To)).obj
    (regularHigherDirectImage sY 2)

/-- A *local-system open* of the curve `T`: a connected smooth dense Zariski-open `T° ⊆ T` on
which `(R²j_* ℚ_{Y_reg})|_{T°}` is a local system. -/
@[mmp "def_oai4_curve_local_system"]
structure IsLocalSystemOpen (To : (curveScheme T).Opens) : Prop where
  /-- `T°` is connected. -/
  connectedSpace : ConnectedSpace To
  /-- `T°` is smooth over `ℂ`. -/
  smooth : Smooth (To.ι ≫ curveι T ≫ sY)
  /-- `T°` is dense in `T`. -/
  dense : Dense (To : Set (curveScheme T))
  /-- `(R²j_* ℚ_{Y_reg})|_{T°}` is a local system. -/
  isLocalSystem : IsLocalSystem (curveLocalSystem sY To)

/-- The fibre `𝒱_{T,t}` of the punctured local system at a point `t ∈ T°(ℂ)`: its stalk. -/
abbrev curveLocalSystemFibre (To : (curveScheme T).Opens)
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) : ModuleCat.{0} ℚ :=
  ((TopCat.Sheaf.forget _ _).obj (curveLocalSystem sY To)).stalk t

/-- The *rank* `b_T = dim_ℚ H²_c(T°, 𝒱_T)` of the punctured local system on a Zariski-open
`T° ⊆ T`, cohomology with compact supports being taken on `T°(ℂ)`. -/
@[mmp "def_oai4_curve_local_system_rank"]
def curveLocalSystemRank (To : (curveScheme T).Opens) : ℕ :=
  Module.finrank ℚ (compactSupportCohomology ℚ 2 (curveLocalSystem sY To))

end CurveLocalSystem

/-! ### Adapted opens and the resolution local system -/

section ResolutionLocalSystem

variable {Y Yt : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) {T : IrreducibleCloseds Y} (π : Yt ⟶ Y)

/-- The realization `π^an : Ỹ^an ⟶ Y^an` of the resolution. -/
def resolutionAnalyticMap : analyticSpace (π ≫ sY) ⟶ analyticSpace sY :=
  analyticMap π rfl

/-- The sheaf `R^q π_* ℚ_Ỹ` on `Y^an`. -/
abbrev resolutionHigherDirectImage (q : ℕ) :
    TopCat.Sheaf (ModuleCat.{0} ℚ) (analyticSpace sY) :=
  higherDirectImage (resolutionAnalyticMap sY π) q

/-- The restriction `(R²π_* ℚ_Ỹ)|_{T°}` of `R²π_* ℚ_Ỹ` to a Zariski-open `T° ⊆ T`. For a
`π`-adapted open this is the *resolution local system* `𝒲`. -/
@[mmp "def_oai4_c2_resolution_local_system"]
def resolutionLocalSystem (To : (curveScheme T).Opens) :
    TopCat.Sheaf (ModuleCat.{0} ℚ) (analyticSpace (To.ι ≫ curveι T ≫ sY)) :=
  (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) (curveOpenInclusion sY To)).obj
    (resolutionHigherDirectImage sY π 2)

/-- A *`π`-adapted open* of `T`: a local-system open `T° ⊆ T` such that
`(R²π_* ℚ_Ỹ)|_{T°}` is a local system, every scheme fibre `F_y` of `π` over a point of `T°`
has dimension at most two, and `Ỹ ×_Y T° ⟶ T°` is flat and projective. -/
@[mmp "def_oai4_c2_adapted_open"]
structure IsAdaptedOpen (To : (curveScheme T).Opens) : Prop extends IsLocalSystemOpen sY To where
  /-- `(R²π_* ℚ_Ỹ)|_{T°}` is a local system. -/
  isLocalSystem_resolution : IsLocalSystem (resolutionLocalSystem sY π To)
  /-- The scheme fibres of `π` over the points of `T°` have dimension at most two. -/
  topologicalKrullDim_fibre_le (t : To) :
    topologicalKrullDim (pointSettingFibre π ((curveι T).base t.1)) ≤ 2
  /-- `Ỹ ×_Y T° ⟶ T°` is flat. -/
  flat : Flat (pullback.snd π (To.ι ≫ curveι T))
  /-- `Ỹ ×_Y T° ⟶ T°` is projective. -/
  isProjectiveMorphism : IsProjectiveMorphism (pullback.snd π (To.ι ≫ curveι T))

/-- The fibre `𝒲_t` of `(R²π_* ℚ_Ỹ)|_{T°}` at a point `t ∈ T°(ℂ)`: its stalk. -/
abbrev resolutionLocalSystemFibre (To : (curveScheme T).Opens)
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) : ModuleCat.{0} ℚ :=
  ((TopCat.Sheaf.forget _ _).obj (resolutionLocalSystem sY π To)).stalk t

variable {π}

/-- The inverse `Y_reg ≅ π⁻¹(Y_reg) ⊆ Ỹ` of `π` over the smooth locus, for `π` an isomorphism
over `Y_reg`. -/
def regularSection (hπ : IsBiregular π (smoothLocus sY)) : (smoothLocus sY : Scheme.{0}) ⟶ Yt :=
  @inv _ _ _ _ (π ∣_ smoothLocus sY) hπ ≫ (π ⁻¹ᵁ smoothLocus sY).ι

/-- `regularSection` is a section of `π` over `Y_reg`: its composite with `π` is the inclusion
`Y_reg ⟶ Y`. -/
theorem regularSection_comp (hπ : IsBiregular π (smoothLocus sY)) :
    regularSection sY hπ ≫ π = (smoothLocus sY).ι := by
  unfold regularSection
  rw [Category.assoc, ← morphismRestrict_ι]
  have : IsIso (π ∣_ smoothLocus sY) := hπ
  exact IsIso.inv_hom_id_assoc _ _

/-- The realization of the section `Y_reg ⟶ Ỹ` of `π`, composed with `π^an`, is `j^an`. -/
theorem regularSection_analyticMap_comp (hπ : IsBiregular π (smoothLocus sY)) :
    analyticMap (regularSection sY hπ) (by rw [← Category.assoc, regularSection_comp]) ≫
      resolutionAnalyticMap sY π = regularInclusion sY := by
  ext x
  change (x.hom ≫ regularSection sY hπ) ≫ π = x.hom ≫ (smoothLocus sY).ι
  rw [Category.assoc, regularSection_comp]

/-- The map `R²π_* ℚ_Ỹ ⟶ R²π_* ℚ_{π⁻¹(Y_reg)} = R²j_* ℚ_{Y_reg}` induced by restriction of
classes to `π⁻¹(Y_reg) ≅ Y_reg`. -/
def resolutionRestriction (hπ : IsBiregular π (smoothLocus sY)) (q : ℕ) :
    resolutionHigherDirectImage sY π q ⟶ regularHigherDirectImage sY q :=
  higherDirectImageRestriction (resolutionAnalyticMap sY π)
    (analyticMap (regularSection sY hπ) (by rw [← Category.assoc, regularSection_comp]))
    (regularSection_analyticMap_comp sY hπ) q

/-- The restriction map `r : 𝒲 ⟶ 𝒱_T` on a Zariski-open `T° ⊆ T`: the restriction to `T°` of
the map `R²π_* ℚ_Ỹ ⟶ R²j_* ℚ_{Y_reg}` induced by restriction to `π⁻¹(Y_reg) ≅ Y_reg`. -/
@[mmp "def_oai4_c2_restriction_map"]
def localSystemRestriction (hπ : IsBiregular π (smoothLocus sY)) (To : (curveScheme T).Opens) :
    resolutionLocalSystem sY π To ⟶ curveLocalSystem sY To :=
  (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) (curveOpenInclusion sY To)).map
    (resolutionRestriction sY hπ 2)

/-- The fibre `r_t : 𝒲_t ⟶ 𝒱_{T,t}` of the restriction map at a point `t ∈ T°(ℂ)`. -/
def localSystemRestrictionFibre (hπ : IsBiregular π (smoothLocus sY))
    (To : (curveScheme T).Opens) (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) :
    resolutionLocalSystemFibre sY π To t ⟶ curveLocalSystemFibre sY To t :=
  (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) t).map
    ((TopCat.Sheaf.forget _ _).map (localSystemRestriction sY hπ To))

end ResolutionLocalSystem

/-! ### Punctured-independent families -/

section PuncturedIndependent

open MMP.Analytic

variable {Y Yt : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) {T : IrreducibleCloseds Y} (π : Yt ⟶ Y)

/-- The family `Ỹ ×_Y T° ⟶ T°` of a resolution over a Zariski-open `T° ⊆ T`. -/
abbrev adaptedFamily (To : (curveScheme T).Opens) : Scheme.{0} :=
  pullback π (To.ι ≫ curveι T)

/-- The generic scheme fibre `F_{η_T} = Ỹ ×_Y Spec K_T`. -/
abbrev genericFibre (T : IrreducibleCloseds Y) : Scheme.{0} :=
  pointSettingFibre π (localSettingGenericPoint T)

/-- The fibre `Ỹ ×_Y Spec κ(ξ)` over a point `ξ` of a Zariski-open `T° ⊆ T`, `κ(ξ)` being the
residue field of `T°` at `ξ`. -/
abbrev curveOpenFibre (To : (curveScheme T).Opens) (ξ : (To : Scheme.{0})) : Scheme.{0} :=
  pullback π ((To : Scheme.{0}).fromSpecResidueField ξ ≫ To.ι ≫ curveι T)

/-- The map `Ỹ ×_Y Spec κ(ξ) ⟶ Ỹ ×_Y T°`. -/
def curveOpenFibreToFamily (To : (curveScheme T).Opens) (ξ : (To : Scheme.{0})) :
    curveOpenFibre π To ξ ⟶ adaptedFamily π To :=
  pullback.map _ _ _ _ (𝟙 _) ((To : Scheme.{0}).fromSpecResidueField ξ) (𝟙 _) (by simp)
    (by simp)

/-- For a point `ξ ∈ T°` over `η_T`, the map `Ỹ ×_Y Spec κ(ξ) ⟶ Ỹ ×_Y Spec K_T = F_{η_T}`
induced by the residue field map `K_T = κ(η_T) ⟶ κ(ξ)` (an isomorphism). -/
def curveOpenFibreToGenericFibre (To : (curveScheme T).Opens) (ξ : (To : Scheme.{0}))
    (e : (To.ι ≫ curveι T).base ξ = localSettingGenericPoint T) :
    curveOpenFibre π To ξ ⟶ genericFibre π T :=
  pullback.map _ _ _ _ (𝟙 _)
    (Spec.map ((To.ι ≫ curveι T).residueFieldMap ξ) ≫ Spec.map (Y.residueFieldCongr e.symm).hom)
    (𝟙 _) (by simp) (by
      rw [Category.comp_id, Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField,
        Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField])

/-- The scheme fibre `F_t = Ỹ ×_Y Spec ℂ` of the resolution over a `ℂ`-point `t` of a
Zariski-open `T° ⊆ T`. -/
def pointFibre (To : (curveScheme T).Opens) (t : ComplexPoints (To.ι ≫ curveι T ≫ sY)) :
    Scheme.{0} :=
  pullback π (t.hom ≫ To.ι ≫ curveι T)

/-- The projection `F_t ⟶ Ỹ`. -/
def pointFibreFst (To : (curveScheme T).Opens) (t : ComplexPoints (To.ι ≫ curveι T ≫ sY)) :
    pointFibre sY π To t ⟶ Yt :=
  pullback.fst _ _

/-- The projection `F_t ⟶ Spec ℂ`. -/
def pointFibreSnd (To : (curveScheme T).Opens) (t : ComplexPoints (To.ι ≫ curveι T ≫ sY)) :
    pointFibre sY π To t ⟶ Spec (.of ℂ) :=
  pullback.snd _ _

/-- The pullback square of `F_t`: `F_t ⟶ Ỹ ⟶ Y` equals `F_t ⟶ Spec ℂ ⟶ T° ⟶ Y`. -/
lemma pointFibreFst_comp (To : (curveScheme T).Opens)
    (t : ComplexPoints (To.ι ≫ curveι T ≫ sY)) :
    pointFibreFst sY π To t ≫ π = pointFibreSnd sY π To t ≫ t.hom ≫ To.ι ≫ curveι T :=
  pullback.condition

/-- `F_t` is a scheme over `ℂ` through its second projection. -/
instance (To : (curveScheme T).Opens) (t : ComplexPoints (To.ι ≫ curveι T ≫ sY)) :
    (pointFibre sY π To t).Over (Spec (.of ℂ)) :=
  ⟨pointFibreSnd sY π To t⟩

/-- The inclusion `F_t ⟶ Ỹ ×_Y T°` of the fibre over `t`. -/
def pointFibreToFamily (To : (curveScheme T).Opens) (t : ComplexPoints (To.ι ≫ curveι T ≫ sY)) :
    pointFibre sY π To t ⟶ adaptedFamily π To :=
  pullback.map _ _ _ _ (𝟙 _) t.hom (𝟙 _) (by simp) (by simp)

/-- The projection `F_t ⟶ Ỹ` is a morphism over `ℂ`. -/
lemma pointFibreFst_comp_structure (To : (curveScheme T).Opens)
    (t : ComplexPoints (To.ι ≫ curveι T ≫ sY)) :
    pointFibreFst sY π To t ≫ π ≫ sY = pointFibre sY π To t ↘ Spec (.of ℂ) := by
  rw [reassoc_of% pointFibreFst_comp]
  simp only [Category.assoc, t.hom_comp_structure, Category.comp_id]
  rfl

/-- The realization `F_t(ℂ) ⟶ Ỹ^an` of the inclusion of the fibre. -/
def pointFibreAnalyticMap (To : (curveScheme T).Opens)
    (t : ComplexPoints (To.ι ≫ curveι T ≫ sY)) :
    analyticSpace (pointFibre sY π To t ↘ Spec (.of ℂ)) ⟶ analyticSpace (π ≫ sY) :=
  analyticMap (pointFibreFst sY π To t) (pointFibreFst_comp_structure sY π To t)

/-- `π^an` sends every point of `F_t(ℂ)` to the image of `t` in `Y^an`. -/
lemma resolutionAnalyticMap_pointFibreAnalyticMap (To : (curveScheme T).Opens)
    (t : ComplexPoints (To.ι ≫ curveι T ≫ sY))
    (x : analyticSpace (pointFibre sY π To t ↘ Spec (.of ℂ))) :
    resolutionAnalyticMap sY π (pointFibreAnalyticMap sY π To t x) =
      curveOpenInclusion sY To t := by
  ext1
  change (x.hom ≫ pointFibreFst sY π To t) ≫ π = t.hom ≫ To.ι ≫ curveι T
  have hx : x.hom ≫ pointFibreSnd sY π To t = 𝟙 _ := x.hom_comp_structure
  rw [Category.assoc, pointFibreFst_comp, reassoc_of% hx]

/-- For an open `V ⊆ Y^an` containing the image of `t`, the inclusion `F_t(ℂ) ⟶ π⁻¹(V)`. -/
def pointFibreInclusion (To : (curveScheme T).Opens)
    (t : ComplexPoints (To.ι ≫ curveι T ≫ sY)) {V : Opens (analyticSpace sY)}
    (hV : curveOpenInclusion sY To t ∈ V) :
    analyticSpace (pointFibre sY π To t ↘ Spec (.of ℂ)) ⟶
      preimageSpace (resolutionAnalyticMap sY π) V :=
  TopCat.ofHom ⟨fun x ↦ ⟨pointFibreAnalyticMap sY π To t x, Set.mem_preimage.2 (by
      rw [resolutionAnalyticMap_pointFibreAnalyticMap]; exact hV)⟩,
    (pointFibreAnalyticMap sY π To t).hom.continuous.subtype_mk _⟩

/-- The first Chern class `c₁(M) ∈ H²(F_t; ℚ)` of an invertible module on `F_t`, with rational
coefficients. -/
def pointFibreChernClass (To : (curveScheme T).Opens) (t : ComplexPoints (To.ι ≫ curveι T ≫ sY))
    (M : (pointFibre sY π To t).Modules)
    [SheafOfModules.IsInvertible (pointFibre sY π To t).presheaf
      (pointFibre sY π To t).ringCatSheaf.2 M] :
    rationalCohomology (analyticSpace (pointFibre sY π To t ↘ Spec (.of ℂ))) 2 :=
  singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass M)

variable {π}

/-- A family `L_1, …, L_b` of line bundles on the generic scheme fibre `F_{η_T}` is
*punctured-independent* if there are a `π`-adapted open `T¹` and line bundles
`𝓛_1, …, 𝓛_b` on `Ỹ ×_Y T¹` with generic fibres `L_1, …, L_b` such that, for every closed point
`t ∈ T¹`, the vectors `r(c₁(𝓛_i|_{F_t}))`, `1 ≤ i ≤ b`, are linearly independent in `𝒱_{T,t}`.

Here `c₁(𝓛_i|_{F_t}) ∈ H²(F_t; ℚ)` is carried to `𝒲_t` by the inverse of the base change map
`𝒲_t ⟶ H²(F_t; ℚ)`: the condition asks for classes `α_i ∈ H²(π⁻¹(V); ℚ)` on a neighbourhood `V`
of `t` restricting to `c₁(𝓛_i|_{F_t})` on `F_t`, whose germs in `𝒲_t` have linearly
independent images under `r`. -/
@[mmp "def_oai4_c2_punctured_independent"]
def IsPuncturedIndependent (hπ : IsBiregular π (smoothLocus sY)) {b : ℕ}
    (L : Fin b → (genericFibre π T).Modules) : Prop :=
  ∃ (T₁ : (curveScheme T).Opens) (_ : IsAdaptedOpen sY π T₁)
    (𝓛 : Fin b → (adaptedFamily π T₁).Modules),
    (∀ i, SheafOfModules.IsInvertible (adaptedFamily π T₁).presheaf
      (adaptedFamily π T₁).ringCatSheaf.2 (𝓛 i)) ∧
    (∃ (ξ : (T₁ : Scheme.{0})) (e : (T₁.ι ≫ curveι T).base ξ = localSettingGenericPoint T), ∀ i,
      Nonempty ((Scheme.Modules.pullback (curveOpenFibreToFamily π T₁ ξ)).obj (𝓛 i) ≅
        (Scheme.Modules.pullback (curveOpenFibreToGenericFibre π T₁ ξ e)).obj (L i))) ∧
    ∀ t : ComplexPoints (T₁.ι ≫ curveι T ≫ sY),
      ∃ (V : Opens (analyticSpace sY)) (hV : curveOpenInclusion sY T₁ t ∈ V)
        (α : Fin b → rationalCohomology (preimageSpace (resolutionAnalyticMap sY π) V) 2),
        (∀ i, ∃ _ : SheafOfModules.IsInvertible (pointFibre sY π T₁ t).presheaf
            (pointFibre sY π T₁ t).ringCatSheaf.2
            ((Scheme.Modules.pullback (pointFibreToFamily sY π T₁ t)).obj (𝓛 i)),
          (rationalCohomologyMap (pointFibreInclusion sY π T₁ t hV) 2).hom (α i) =
            pointFibreChernClass sY π T₁ t
              ((Scheme.Modules.pullback (pointFibreToFamily sY π T₁ t)).obj (𝓛 i))) ∧
        LinearIndependent ℚ fun i ↦ (localSystemRestrictionFibre sY hπ T₁ t).hom
          ((stalkToPullbackStalk (curveOpenInclusion sY T₁) (resolutionHigherDirectImage sY π 2)
            t).hom ((higherDirectImageGerm (resolutionAnalyticMap sY π) 2 _ hV).hom (α i)))

end PuncturedIndependent

end MMP.Fourfold
