module

public import MMP.Attr
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.Geometry.Manifold.Sheaf.Smooth
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Closed complex submanifolds and their structure sheaves

A *complex manifold* of dimension `n` is a Hausdorff, second countable topological space `M`
with an atlas of homeomorphisms onto open subsets of `ℂⁿ` whose transition maps are holomorphic.
It carries the sheaf of rings `𝒪_M` of functions that are holomorphic in charts.

A closed subset `Z ⊆ M` is a *closed complex submanifold* if every point `x ∈ Z` lies in the
domain `W` of a chart `φ : W → ℂⁿ` of `M` such that, for some `k`,
`φ(Z ∩ W) = φ(W) ∩ {y_{k+1} = ⋯ = y_n = 0}`.

For any subset `Z ⊆ M`, the holomorphic functions vanishing on `Z` form an ideal sheaf
`ℐ_Z ⊆ 𝒪_M`, a sheaf of `𝒪_M`-modules. The structure sheaf of `Z` is
`𝒪_Z = ι⁻¹(𝒪_M / ℐ_Z)`, where `ι : Z → M` is the inclusion and `𝒪_M / ℐ_Z` is the sheaf
quotient (the sheafification of the presheaf `U ↦ 𝒪_M(U) / ℐ_Z(U)`).

## Main definitions

* `MMP.Analytic.IsClosedComplexSubmanifold`: a closed subset with flattening charts, taken from
  the maximal holomorphic atlas of `M`.
* `MMP.Analytic.vanishingIdeal`: the ideal `ℐ_Z(U) ⊆ 𝒪_M(U)` of holomorphic functions on `U`
  vanishing on `Z ∩ U`.
* `MMP.Analytic.vanishingIdealSheaf`: the ideal sheaf `ℐ_Z`, as a sheaf of `𝒪_M`-modules.
* `MMP.Analytic.vanishingIdealSheaf.subtype`: its inclusion `ℐ_Z ⟶ 𝒪_M` as modules.
* `MMP.Analytic.quotientVanishingIdealPresheaf`: the presheaf of rings `U ↦ 𝒪_M(U) / ℐ_Z(U)`.
* `MMP.Analytic.quotientVanishingIdealSheaf`: the sheaf of rings `𝒪_M / ℐ_Z` on `M`.
* `MMP.Analytic.toQuotientVanishingIdealSheaf`: the quotient map `𝒪_M ⟶ 𝒪_M / ℐ_Z`.
* `MMP.Analytic.submanifoldInclusion`: the inclusion `ι : Z → M`, as a map of spaces.
* `MMP.Analytic.submanifoldStructureSheaf`: the sheaf of rings `𝒪_Z = ι⁻¹(𝒪_M / ℐ_Z)` on `Z`.

## Main results

* `MMP.Analytic.isSheaf_vanishingIdealPresheaf`: the vanishing ideals form a sheaf.

## Implementation notes

* A complex manifold of dimension `n` is expressed by Mathlib's classes: `[TopologicalSpace M]
  [T2Space M] [SecondCountableTopology M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ M]`. The constructions here only use the charted
  space structure, so the other hypotheses are not assumed.
* `𝒪_M` is Mathlib's `smoothSheafCommRing 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) M ℂ`, the sheaf
  of functions that are complex-`C^∞` in charts, written `𝒪[n, M]` (a scoped notation in
  `MMP.Analytic`). A complex-`C^∞` function on an open subset of `ℂⁿ` is complex-differentiable,
  and conversely a holomorphic function is complex analytic, hence complex-`C^∞`; so these are
  exactly the functions holomorphic in charts.
* The flattening chart of a closed submanifold is any member of the maximal atlas
  `IsManifold.maximalAtlas 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ M`, i.e. any chart holomorphically
  compatible with the atlas of `M`, not only a chart of the given atlas. The coordinates
  `y_{k+1}, …, y_n` are the coordinates of index `i ≥ k` in `Fin n`, and `φ(W)` is the target of
  the chart. The integer `k` may depend on the point.
* `ℐ_Z` and `𝒪_M / ℐ_Z` are defined for an arbitrary subset `Z`. The `𝒪_M`-module structure of
  `ℐ_Z` is over the sheaf of rings underlying `𝒪_M`, `holomorphicRingCatSheaf`, as Mathlib's
  sheaves of modules require.

## References

* [Serre, *Géométrie algébrique et géométrie analytique*]
* [Grauert–Remmert, *Coherent analytic sheaves*]
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped Manifold ContDiff

namespace MMP.Analytic

/-- The sheaf of holomorphic functions `𝒪_M` on a complex manifold `M` of dimension `n`,
Mathlib's sheaf of complex-`C^∞` functions. -/
scoped notation "𝒪[" n ", " M "]" =>
  smoothSheafCommRing 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) M ℂ

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]

variable (n) in
/-- A subset `Z` of a complex manifold `M` of dimension `n` is a *closed complex submanifold* if
it is closed and every `x ∈ Z` lies in the source `W` of a chart `φ` holomorphically compatible
with the atlas of `M` such that, for some `k`, `φ(Z ∩ W) = φ(W) ∩ {y | y_i = 0 for all i ≥ k}`. -/
@[mmp "def_mmp_gaga_closed_submanifold"]
def IsClosedComplexSubmanifold (Z : Set M) : Prop :=
  IsClosed Z ∧ ∀ x ∈ Z, ∃ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ M,
    x ∈ φ.source ∧ ∃ k : ℕ,
      φ '' (Z ∩ φ.source) = φ.target ∩ {y | ∀ i : Fin n, k ≤ (i : ℕ) → y i = 0}

variable (n) in
/-- The ideal of the holomorphic functions on an open set `U` that vanish on `Z ∩ U`. -/
def vanishingIdeal (Z : Set M) (U : Opens M) : Ideal (𝒪[n, M].presheaf.obj (op U)) where
  carrier := {f | ∀ x : U, (x : M) ∈ Z → f x = 0}
  add_mem' {f g} hf hg x hx := by
    change f.1 x + g.1 x = 0
    rw [hf x hx, hg x hx, add_zero]
  zero_mem' _ _ := rfl
  smul_mem' c f hf x hx := by
    change c.1 x * f.1 x = 0
    rw [hf x hx, mul_zero]

variable {Z : Set M}

/-- A section `f` of `𝒪_M` over `U` lies in `ℐ_Z(U)` iff `f x = 0` for every `x ∈ U ∩ Z`. -/
lemma mem_vanishingIdeal {U : Opens M} {f : 𝒪[n, M].presheaf.obj (op U)} :
    f ∈ vanishingIdeal n Z U ↔ ∀ x : U, (x : M) ∈ Z → f x = 0 := Iff.rfl

/-- The vanishing ideal of the empty set is the unit ideal. -/
@[simp]
lemma vanishingIdeal_empty (U : Opens M) : vanishingIdeal n (∅ : Set M) U = ⊤ :=
  Ideal.eq_top_iff_one _ |>.mpr fun _ hx => hx.elim

/-- The vanishing ideal is antitone in the subset: `Z ⊆ Z'` implies `ℐ_{Z'}(U) ≤ ℐ_Z(U)`. -/
lemma vanishingIdeal_anti_mono {Z' : Set M} (h : Z ⊆ Z') (U : Opens M) :
    vanishingIdeal n Z' U ≤ vanishingIdeal n Z U :=
  fun _ hf x hx => hf x (h hx)

/-- Restriction maps send vanishing functions to vanishing functions. -/
lemma map_mem_vanishingIdeal {U V : Opens M} (h : V ⟶ U) {f : 𝒪[n, M].presheaf.obj (op U)}
    (hf : f ∈ vanishingIdeal n Z U) : 𝒪[n, M].presheaf.map h.op f ∈ vanishingIdeal n Z V :=
  fun x hx => hf ⟨x.1, h.le x.2⟩ hx

variable (n Z) in
/-- The presheaf of abelian groups `U ↦ ℐ_Z(U)` of holomorphic functions vanishing on `Z`. -/
def vanishingIdealPresheaf : (Opens (TopCat.of M))ᵒᵖ ⥤ Ab where
  obj U := AddCommGrpCat.of (vanishingIdeal n Z U.unop)
  map {U V} h := AddCommGrpCat.ofHom
    { toFun := fun f => ⟨𝒪[n, M].presheaf.map h f.1, map_mem_vanishingIdeal h.unop f.2⟩
      map_zero' := by ext1; exact map_zero _
      map_add' := fun f g => by ext1; exact map_add _ _ _ }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The restriction maps of `ℐ_Z` are those of `𝒪_M` on underlying sections. -/
@[simp]
lemma vanishingIdealPresheaf_map_apply_coe {U V : (Opens (TopCat.of M))ᵒᵖ} (h : U ⟶ V)
    (f : (vanishingIdealPresheaf n Z).obj U) :
    ((vanishingIdealPresheaf n Z).map h f).1 = 𝒪[n, M].presheaf.map h f.1 := rfl

/-- The presheaf `U ↦ ℐ_Z(U)` of holomorphic functions vanishing on `Z` is a sheaf. -/
lemma isSheaf_vanishingIdealPresheaf :
    TopCat.Presheaf.IsSheaf (X := TopCat.of M) (vanishingIdealPresheaf n Z) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  let sf' : ∀ i, 𝒪[n, M].presheaf.obj (op (U i)) := fun i => (sf i).1
  have hsf' : TopCat.Presheaf.IsCompatible 𝒪[n, M].presheaf U sf' := fun i j =>
    congrArg Subtype.val (hsf i j)
  obtain ⟨s, hs, huniq⟩ := 𝒪[n, M].existsUnique_gluing U sf' hsf'
  have hmem : s ∈ vanishingIdeal n Z (iSup U) := by
    intro x hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp x.2
    have := congrArg (fun g : 𝒪[n, M].presheaf.obj (op (U i)) => g ⟨x.1, hi⟩) (hs i)
    exact this.trans ((sf i).2 ⟨x.1, hi⟩ hx)
  refine ⟨⟨s, hmem⟩, fun i => Subtype.ext (hs i), fun t ht => Subtype.ext ?_⟩
  exact huniq t.1 fun i => congrArg Subtype.val (ht i)

variable (n M) in
/-- The sheaf of rings underlying `𝒪_M`, over which sheaves of `𝒪_M`-modules are defined. -/
abbrev holomorphicRingCatSheaf : TopCat.Sheaf RingCat (TopCat.of M) :=
  (sheafCompose _ (forget₂ CommRingCat RingCat)).obj 𝒪[n, M]

/-- Each `ℐ_Z(U)` is a module over `𝒪_M(U)`, as an ideal of it. -/
instance (U : (Opens (TopCat.of M))ᵒᵖ) :
    Module ((holomorphicRingCatSheaf n M).obj.obj U) ((vanishingIdealPresheaf n Z).obj U) :=
  inferInstanceAs (Module (𝒪[n, M].presheaf.obj U) (vanishingIdeal n Z U.unop))

variable (n Z) in
/-- The ideal sheaf `ℐ_Z ⊆ 𝒪_M` of holomorphic functions vanishing on `Z`, as a sheaf of
`𝒪_M`-modules. -/
@[mmp "def_mmp_gaga_closed_submanifold"]
def vanishingIdealSheaf : SheafOfModules (holomorphicRingCatSheaf n M) where
  val := PresheafOfModules.ofPresheaf (vanishingIdealPresheaf n Z) fun _ _ h r m =>
    Subtype.ext (map_mul (𝒪[n, M].presheaf.map h).hom r m.1)
  isSheaf := isSheaf_vanishingIdealPresheaf

/-- The sections of `ℐ_Z` over `U` are the elements of the ideal `ℐ_Z(U)`. -/
lemma vanishingIdealSheaf_obj (U : (Opens (TopCat.of M))ᵒᵖ) :
    ((vanishingIdealSheaf n Z).val.obj U : Type) = vanishingIdeal n Z U.unop := rfl

variable (n Z) in
/-- The inclusion `ℐ_Z ⟶ 𝒪_M` of the ideal sheaf, as a morphism of sheaves of `𝒪_M`-modules. -/
def vanishingIdealSheaf.subtype :
    vanishingIdealSheaf n Z ⟶ SheafOfModules.unit (holomorphicRingCatSheaf n M) where
  val := PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom (vanishingIdeal n Z U.unop).subtype.toAddMonoidHom
      naturality _ _ _ := rfl }
    fun _ _ _ => rfl

/-- The inclusion `ℐ_Z ⟶ 𝒪_M` sends a section to its underlying section of `𝒪_M`. -/
@[simp]
lemma vanishingIdealSheaf.subtype_app_apply (U : (Opens (TopCat.of M))ᵒᵖ)
    (f : (vanishingIdealSheaf n Z).val.obj U) :
    (vanishingIdealSheaf.subtype n Z).val.app U f = f.1 := rfl

variable (n Z) in
/-- The presheaf of rings `U ↦ 𝒪_M(U) / ℐ_Z(U)`. -/
def quotientVanishingIdealPresheaf : TopCat.Presheaf CommRingCat (TopCat.of M) where
  obj U := CommRingCat.of (𝒪[n, M].presheaf.obj U ⧸ vanishingIdeal n Z U.unop)
  map h := CommRingCat.ofHom (Ideal.quotientMap _ (𝒪[n, M].presheaf.map h).hom
    fun _ hf => map_mem_vanishingIdeal h.unop hf)
  map_id _ := by
    ext
    rfl
  map_comp _ _ := by
    ext
    rfl

variable (n Z) in
/-- The quotient maps `𝒪_M(U) → 𝒪_M(U) / ℐ_Z(U)`, as a morphism of presheaves of rings. -/
def toQuotientVanishingIdealPresheaf : 𝒪[n, M].presheaf ⟶ quotientVanishingIdealPresheaf n Z where
  app U := CommRingCat.ofHom (Ideal.Quotient.mk (vanishingIdeal n Z U.unop))
  naturality _ _ _ := rfl

/-- The quotient map `𝒪_M(U) → 𝒪_M(U) / ℐ_Z(U)` sends `f` to its class. -/
@[simp]
lemma toQuotientVanishingIdealPresheaf_app_apply (U : (Opens (TopCat.of M))ᵒᵖ)
    (f : 𝒪[n, M].presheaf.obj U) :
    (toQuotientVanishingIdealPresheaf n Z).app U f = Ideal.Quotient.mk _ f := rfl

/-- The restriction maps of `U ↦ 𝒪_M(U) / ℐ_Z(U)` send the class of `f` to the class of the
restriction of `f`. -/
@[simp]
lemma quotientVanishingIdealPresheaf_map_mk {U V : (Opens (TopCat.of M))ᵒᵖ} (h : U ⟶ V)
    (f : 𝒪[n, M].presheaf.obj U) :
    (quotientVanishingIdealPresheaf n Z).map h (Ideal.Quotient.mk _ f) =
      Ideal.Quotient.mk _ (𝒪[n, M].presheaf.map h f) := rfl

variable (n Z) in
/-- The quotient sheaf of rings `𝒪_M / ℐ_Z` on `M`: the sheafification of the presheaf
`U ↦ 𝒪_M(U) / ℐ_Z(U)`. -/
@[mmp "def_mmp_gaga_closed_submanifold"]
def quotientVanishingIdealSheaf : TopCat.Sheaf CommRingCat (TopCat.of M) :=
  (presheafToSheaf _ _).obj (quotientVanishingIdealPresheaf n Z)

variable (n Z) in
/-- The quotient map `𝒪_M ⟶ 𝒪_M / ℐ_Z` of sheaves of rings. -/
def toQuotientVanishingIdealSheaf : 𝒪[n, M] ⟶ quotientVanishingIdealSheaf n Z :=
  (fullyFaithfulSheafToPresheaf _ _).preimage
    (toQuotientVanishingIdealPresheaf n Z ≫ toSheafify _ _)

/-- On presheaves, the quotient map `𝒪_M ⟶ 𝒪_M / ℐ_Z` is the quotient map followed by
sheafification. -/
lemma toQuotientVanishingIdealSheaf_hom :
    (toQuotientVanishingIdealSheaf n Z).hom =
      toQuotientVanishingIdealPresheaf n Z ≫ toSheafify _ _ :=
  (fullyFaithfulSheafToPresheaf _ _).map_preimage _

variable (Z) in
/-- The inclusion `ι : Z → M` of a subset, as a morphism of topological spaces. -/
def submanifoldInclusion : TopCat.of Z ⟶ TopCat.of M :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The inclusion `ι : Z → M` sends a point of `Z` to itself. -/
@[simp]
lemma submanifoldInclusion_apply (z : Z) : submanifoldInclusion Z z = (z : M) := rfl

variable (n Z) in
/-- The structure sheaf `𝒪_Z = ι⁻¹(𝒪_M / ℐ_Z)` of a subset `Z` of a complex manifold, a sheaf
of rings on `Z`. -/
@[mmp "def_mmp_gaga_closed_submanifold"]
def submanifoldStructureSheaf : TopCat.Sheaf CommRingCat (TopCat.of Z) :=
  (TopCat.Sheaf.pullback CommRingCat (submanifoldInclusion Z)).obj
    (quotientVanishingIdealSheaf n Z)

end MMP.Analytic
