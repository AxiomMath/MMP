module

public import MMP.AlgebraicGeometry.Variety.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.SymmetricAlgebraSheafFunctorial
public import StacksFrontier.AlgebraicGeometry.Reflexive.DualMap
public import StacksFrontier.AlgebraicGeometry.Coherent.SheafHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.DegreeOne
public import StacksFrontier.AlgebraicGeometry.ProjTwistCocycle.Pointwise
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OnSpaceMonoidal

/-!
# Vector bundles and projective bundles (Fulton B.3, B.5; Lazarsfeld)

This file defines vector bundles on schemes, both as geometric bundles with linear local
trivializations and through their sheaves of sections, together with projective bundles,
sub-bundles and fibres of `𝒪_X`-modules.

## Implementation notes

Two models of a vector bundle are formalized.

* **Geometric bundles (Fulton B.3.1).** `Scheme.VectorBundle X r` is a scheme `E` with
  `π : E ⟶ X` and a `Scheme.VectorBundleAtlas`: an open covering `{Uᵢ}` of `X` and isomorphisms
  `φᵢ : π⁻¹(Uᵢ) ≅ Uᵢ × 𝔸ʳ` over `Uᵢ` with linear transition maps. A morphism `π⁻¹(Uᵢ) ⟶ Uᵢ × 𝔸ʳ`
  over `Uᵢ` is the same as `r` functions on `π⁻¹(Uᵢ)` (`AffineSpace.homOverEquiv`), so a chart is
  stored as its coordinate functions `xᵢ₁, …, xᵢᵣ`, with `Scheme.chart` the morphism they define
  required to be an isomorphism. Since a morphism into `U × 𝔸ʳ` over `U` is determined by its
  coordinates, `φᵢ ∘ φⱼ⁻¹` is the linear map given by `gᵢⱼ ∈ GL_r(𝒪(Uᵢ ∩ Uⱼ))` exactly when
  `xᵢₖ = ∑ₗ π^*(gᵢⱼ)ₖₗ xⱼₗ` on `π⁻¹(Uᵢ ∩ Uⱼ)` (`Scheme.IsLinearTransition`). Sections and their
  local expressions `sᵢ = gᵢⱼ sⱼ` are stated for this model.
* **Bundles of modules.** Every other Fulton construction of B.3, B.5 is a formula in the sheaf
  of sections `ℰ`: `E^∨ = 𝔼(ℰ^∨)`, `E ⊗ F = 𝔼(ℰ ⊗ ℱ)`, `ℙ(E) = Proj(Sym ℰ^∨)`, homomorphisms and
  sub-bundles are maps of sheaves of sections. These are formalized on `𝒪_X`-modules, through
  `Scheme.Modules.bundle ℱ = 𝔼(ℱ) = Spec(Sym ℱ^∨)`, built from the Stacks project's relative
  spectrum `Scheme.Modules.vectorBundle` of `Sym` and its internal-Hom dual `dualSheaf`. The
  relative `Proj` and its twist `𝒪(1)` are the Stacks project's `relativeProj (symAlgebra ℱ)`
  and `twistOne`. Lazarsfeld's vector bundles are locally free modules of constant rank
  (`Scheme.Modules.IsLocallyFreeOfRank`), so his notions are stated on modules directly.

## Main definitions

All declarations of this file are in the namespace `MMP.Intersection` (so
`MMP.Intersection.Scheme.Modules.bundle`, not `AlgebraicGeometry.Scheme.Modules.bundle`); dot
notation on a scheme, a morphism or an `𝒪_X`-module does not reach them.

* `MMP.Intersection.Scheme.VectorBundleAtlas`, `MMP.Intersection.Scheme.VectorBundle`,
  `MMP.Intersection.Scheme.LineBundle`, `MMP.Intersection.Scheme.VectorBundle.trivial`,
  `MMP.Intersection.Scheme.VectorBundle.Section`.
* `MMP.Intersection.Scheme.Modules.bundle`, `bundleMap`, `dualBundle`, `tensorBundle`,
  `tensorZPow`, `lineBundlePow`.
* `MMP.Intersection.Scheme.Modules.projectiveBundle`, `projectiveBundleTwistOne`,
  `serreTwist`, `projectiveBundleOfLines`.
* `MMP.Intersection.Scheme.Modules.IsLocallyFreeOfRank`, `fiber`, `fiberMap`, `IsSubbundle`.
* `MMP.Intersection.Scheme.Hom.relativeTangentBundle`, `MMP.Intersection.Scheme.tangentBundle`.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

namespace MMP.Intersection.Scheme

variable {X E : Scheme.{u}}

/-- The restriction to `π ⁻¹ᵁ (U ⊓ V)` of a section over `π ⁻¹ᵁ U`. -/
abbrev resInfLeft (π : E ⟶ X) (U V : X.Opens) :
    Γ(E, π ⁻¹ᵁ U) ⟶ Γ(E, π ⁻¹ᵁ (U ⊓ V)) :=
  E.presheaf.map (homOfLE (π.preimage_mono inf_le_left)).op

/-- The restriction to `π ⁻¹ᵁ (U ⊓ V)` of a section over `π ⁻¹ᵁ V`. -/
abbrev resInfRight (π : E ⟶ X) (U V : X.Opens) :
    Γ(E, π ⁻¹ᵁ V) ⟶ Γ(E, π ⁻¹ᵁ (U ⊓ V)) :=
  E.presheaf.map (homOfLE (π.preimage_mono inf_le_right)).op

/-- The morphism `π⁻¹(U) ⟶ U × 𝔸ⁿ` over `U` given by `n` functions on `π⁻¹(U)`. -/
@[mmp "def_b_vector_bundle"]
def chart (π : E ⟶ X) (U : X.Opens) {n : Type u} (x : n → Γ(E, π ⁻¹ᵁ U)) :
    (π ⁻¹ᵁ U).toScheme ⟶ 𝔸(n; U) :=
  AffineSpace.homOfVector (π ∣_ U) fun m ↦ (π ⁻¹ᵁ U).topIso.inv (x m)

/-- The chart `chart π U x` is a morphism over `U`: composed with the projection `U × 𝔸ⁿ ⟶ U`
it is the restriction `π ∣_ U`. -/
@[reassoc (attr := simp)]
lemma chart_over (π : E ⟶ X) (U : X.Opens) {n : Type u} (x : n → Γ(E, π ⁻¹ᵁ U)) :
    chart π U x ≫ 𝔸(n; U) ↘ U = π ∣_ U :=
  AffineSpace.homOfVector_over _ _

/-- Two families of `n` functions on `π⁻¹(U)` and `π⁻¹(V)` are *related by the linear
transition `g`* on `U ∩ V` if `xₖ = ∑ₗ gₖₗ yₗ` on `π⁻¹(U ∩ V)`. -/
@[mmp "def_b_vector_bundle"]
def IsLinearTransition (π : E ⟶ X) {U V : X.Opens} {n : Type u} [Fintype n] [DecidableEq n]
    (x : n → Γ(E, π ⁻¹ᵁ U)) (y : n → Γ(E, π ⁻¹ᵁ V))
    (g : Matrix.GeneralLinearGroup n Γ(X, U ⊓ V)) : Prop :=
  ∀ k, resInfLeft π U V (x k) =
    ∑ l, π.app (U ⊓ V) ((g : Matrix n n Γ(X, U ⊓ V)) k l) * resInfRight π U V (y l)

/-- A *vector bundle atlas of rank `r`* on `π : E ⟶ X` (Fulton B.3.1). -/
@[mmp "def_b_vector_bundle"]
structure VectorBundleAtlas (π : E ⟶ X) (r : ℕ) where
  /-- The index type of the covering. -/
  ι : Type u
  /-- The trivializing opens. -/
  U : ι → X.Opens
  /-- The opens `Uᵢ` cover `X`. -/
  iSup_eq_top : ⨆ i, U i = ⊤
  /-- The coordinate functions of the chart `φᵢ`. -/
  coord : ∀ i, ULift.{u} (Fin r) → Γ(E, π ⁻¹ᵁ U i)
  /-- Each chart `φᵢ : π⁻¹(Uᵢ) ⟶ Uᵢ × 𝔸ʳ` is an isomorphism. -/
  isIso_chart : ∀ i, IsIso (chart π (U i) (coord i))
  /-- The transition functions. -/
  transition : ∀ i j, Matrix.GeneralLinearGroup (ULift.{u} (Fin r)) Γ(X, U i ⊓ U j)
  /-- The coordinates of the charts `φᵢ` and `φⱼ` are related by the linear transition
  `gᵢⱼ` on `Uᵢ ∩ Uⱼ`. -/
  isLinearTransition : ∀ i j, IsLinearTransition π (coord i) (coord j) (transition i j)

section Trivial

variable (n : Type u) (X)

/-- The coordinate functions of `X × 𝔸ⁿ` restricted to the preimage of an open `U ⊆ X`. -/
def trivialCoord (U : X.Opens) (m : n) : Γ(𝔸(n; X), (𝔸(n; X) ↘ X) ⁻¹ᵁ U) :=
  𝔸(n; X).presheaf.map (homOfLE le_top).op (AffineSpace.coord X m)

/-- The chart of `X × 𝔸ⁿ` over `U` given by the restricted coordinates, followed by the inclusion
`U × 𝔸ⁿ ⟶ X × 𝔸ⁿ`, is the inclusion of the preimage of `U`. -/
lemma chart_trivialCoord_comp_map (U : X.Opens) :
    chart (𝔸(n; X) ↘ X) U (trivialCoord X n U) ≫ AffineSpace.map n U.ι =
      ((𝔸(n; X) ↘ X) ⁻¹ᵁ U).ι := by
  apply AffineSpace.hom_ext
  · simp [AffineSpace.map_over, morphismRestrict_ι]
  · intro m
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.map_appTop_coord, chart,
      AffineSpace.homOfVector_appTop_coord, trivialCoord, ← CommRingCat.comp_apply]
    erw [← Functor.map_comp]
    rfl

/-- The chart of `X × 𝔸ⁿ` over `U` given by the restricted coordinates is an isomorphism. -/
instance isIso_chart_trivialCoord (U : X.Opens) :
    IsIso (chart (𝔸(n; X) ↘ X) U (trivialCoord X n U)) := by
  have P₁ := isPullback_morphismRestrict (𝔸(n; X) ↘ X) U
  have P₂ := AffineSpace.isPullback_map (n := n) U.ι
  have : chart (𝔸(n; X) ↘ X) U (trivialCoord X n U) = (P₁.isoIsPullback _ _ P₂.flip).hom := by
    apply P₂.flip.hom_ext
    · simp
    · rw [IsPullback.isoIsPullback_hom_snd, chart_trivialCoord_comp_map]
  rw [this]
  infer_instance

end Trivial

namespace VectorBundleAtlas

variable {π : E ⟶ X} {r : ℕ}

/-- Two atlases of `π : E ⟶ X` *define the same vector bundle* (Fulton B.3.1) if all mixed
transition maps `φᵢ ∘ φ'ⱼ⁻¹` are linear, i.e. given by some `GL(r)`-valued function on
`Uᵢ ∩ U'ⱼ`. -/
@[mmp "def_b_vector_bundle"]
def Compatible (A A' : VectorBundleAtlas π r) : Prop :=
  ∀ i j, ∃ g : Matrix.GeneralLinearGroup (ULift.{u} (Fin r)) Γ(X, A.U i ⊓ A'.U j),
    IsLinearTransition π (A.coord i) (A'.coord j) g

end VectorBundleAtlas

/-- A *vector bundle of rank `r`* on `X` (Fulton B.3.1): a scheme `E` with a morphism
`π : E ⟶ X` and an atlas of local trivializations `π⁻¹(Uᵢ) ≅ Uᵢ × 𝔸ʳ` over `Uᵢ` whose transition
maps are linear. Two bundles with the same `π` define the same bundle when their atlases are
`VectorBundleAtlas.Compatible`. -/
@[mmp "def_b_vector_bundle"]
structure VectorBundle (X : Scheme.{u}) (r : ℕ) where
  /-- The total space. -/
  E : Scheme.{u}
  /-- The projection. -/
  π : E ⟶ X
  /-- The atlas of local trivializations. -/
  atlas : VectorBundleAtlas π r

/-- A *line bundle* on `X` (Fulton B.3.5): a vector bundle of rank one. -/
@[mmp "def_b_line_bundle"]
abbrev LineBundle (X : Scheme.{u}) : Type (u + 1) := VectorBundle X 1

namespace VectorBundle

variable {r : ℕ}

/-- The coordinates of `X × 𝔸ⁿ` are related to themselves by the identity transition on `X`. -/
lemma isLinearTransition_trivialCoord (X : Scheme.{u}) (n : Type u) [Fintype n] [DecidableEq n] :
    IsLinearTransition (U := ⊤) (V := ⊤) (𝔸(n; X) ↘ X) (trivialCoord X n ⊤)
      (trivialCoord X n ⊤) 1 := fun k ↦ by
  rw [Finset.sum_eq_single k (fun l _ hl ↦ by
    rw [Units.val_one, Matrix.one_apply_ne (Ne.symm hl), map_zero, zero_mul])
    (fun h ↦ absurd (Finset.mem_univ k) h)]
  rw [Units.val_one, Matrix.one_apply_eq, map_one, one_mul]

/-- The trivial vector bundle `X × 𝔸ʳ` of rank `r`, with the one-chart atlas `{X}`. -/
@[mmp "not_b_trivial_line_bundle"]
def trivial (X : Scheme.{u}) (r : ℕ) : VectorBundle X r where
  E := 𝔸(ULift.{u} (Fin r); X)
  π := 𝔸(ULift.{u} (Fin r); X) ↘ X
  atlas :=
    { ι := PUnit.{u + 1}
      U := fun _ ↦ ⊤
      iSup_eq_top := iSup_const
      coord := fun _ ↦ trivialCoord X (ULift.{u} (Fin r)) ⊤
      isIso_chart := fun _ ↦ inferInstance
      transition := fun _ _ ↦ 1
      isLinearTransition := fun _ _ ↦ isLinearTransition_trivialCoord X _ }

/-- The trivial line bundle `1 = 𝒪_X = X × 𝔸¹` (Fulton B.3.3). -/
@[mmp "not_b_trivial_line_bundle"]
abbrev trivialLineBundle (X : Scheme.{u}) : LineBundle X := trivial X 1

variable {X : Scheme.{u}} (V : VectorBundle X r)

/-- A *section* of a vector bundle `π : E ⟶ X` (Fulton B.3.2): a morphism `s : X ⟶ E` with
`π ∘ s = id_X`. Its local expression in the chart `φᵢ` is `Section.localCoord`. -/
@[mmp "def_b_section_of_vector_bundle"]
structure Section where
  /-- The morphism `X ⟶ E`. -/
  s : X ⟶ V.E
  /-- The morphism is a section of the projection: `π ∘ s = id_X`. -/
  s_comp_π : s ≫ V.π = 𝟙 X

attribute [reassoc (attr := simp)] Section.s_comp_π

namespace Section

variable {V} (σ : V.Section)

/-- Every open `U ⊆ X` is contained in the preimage of `π⁻¹(U)` under a section `s`. -/
lemma le_preimage (U : X.Opens) : U ≤ σ.s ⁻¹ᵁ V.π ⁻¹ᵁ U := by
  intro x hx
  change V.π (σ.s x) ∈ U
  rw [← Scheme.Hom.comp_apply, σ.s_comp_π]
  exact hx

/-- The local expression `sᵢ = φᵢ ∘ s = (sᵢ₁, …, sᵢᵣ)` of a section on the trivializing open
`Uᵢ`, with `sᵢₘ ∈ 𝒪(Uᵢ)` (Fulton B.3.2). -/
@[mmp "def_b_section_of_vector_bundle"]
def localCoord (i : V.atlas.ι) (m : ULift.{u} (Fin r)) : Γ(X, V.atlas.U i) :=
  σ.s.appLE (V.π ⁻¹ᵁ V.atlas.U i) (V.atlas.U i) (σ.le_preimage _) (V.atlas.coord i m)

/-- Pulling back along a section `s` the pullback `π^* f` of a function `f` on `U` gives the
restriction of `f` to `W`. -/
lemma appLE_π_app (U W : X.Opens) (h : W ≤ σ.s ⁻¹ᵁ V.π ⁻¹ᵁ U) (hW : W ≤ U) (f : Γ(X, U)) :
    σ.s.appLE (V.π ⁻¹ᵁ U) W h (V.π.app U f) = X.presheaf.map (homOfLE hW).op f := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appLE σ.s V.π U W h]
  have key : ∀ (g : X ⟶ X) (_ : g = 𝟙 X) (h' : W ≤ g ⁻¹ᵁ U),
      g.appLE U W h' = X.presheaf.map (homOfLE hW).op := by
    rintro g rfl h'
    rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
    exact Category.id_comp _
  exact congrArg (fun φ : Γ(X, U) ⟶ Γ(X, W) ↦ φ f) (key _ σ.s_comp_π h)

/-- Pulling back along a section commutes with restriction from `π⁻¹(U)` to `π⁻¹(U ∩ U')`. -/
lemma appLE_resInfLeft (U U' : X.Opens) (x : Γ(V.E, V.π ⁻¹ᵁ U)) :
    σ.s.appLE (V.π ⁻¹ᵁ (U ⊓ U')) (U ⊓ U') (σ.le_preimage _) (resInfLeft V.π U U' x) =
      X.presheaf.map (homOfLE inf_le_left).op
        (σ.s.appLE (V.π ⁻¹ᵁ U) U (σ.le_preimage _) x) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE,
    Scheme.Hom.appLE_map]

/-- Pulling back along a section commutes with restriction from `π⁻¹(U')` to `π⁻¹(U ∩ U')`. -/
lemma appLE_resInfRight (U U' : X.Opens) (x : Γ(V.E, V.π ⁻¹ᵁ U')) :
    σ.s.appLE (V.π ⁻¹ᵁ (U ⊓ U')) (U ⊓ U') (σ.le_preimage _) (resInfRight V.π U U' x) =
      X.presheaf.map (homOfLE inf_le_right).op
        (σ.s.appLE (V.π ⁻¹ᵁ U') U' (σ.le_preimage _) x) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE,
    Scheme.Hom.appLE_map]

/-- On `Uᵢ ∩ Uⱼ` the local expressions of a section satisfy `sᵢ = gᵢⱼ sⱼ` (Fulton B.3.2). -/
@[mmp "def_b_section_of_vector_bundle"]
theorem localCoord_transition (i j : V.atlas.ι) (k : ULift.{u} (Fin r)) :
    X.presheaf.map (homOfLE inf_le_left).op (σ.localCoord i k) =
      ∑ l, (V.atlas.transition i j).1 k l *
        X.presheaf.map (homOfLE inf_le_right).op (σ.localCoord j l) := by
  have h := congrArg (σ.s.appLE (V.π ⁻¹ᵁ (V.atlas.U i ⊓ V.atlas.U j)) (V.atlas.U i ⊓ V.atlas.U j)
    (σ.le_preimage _)) (V.atlas.isLinearTransition i j k)
  simp only [map_sum, map_mul] at h
  simp only [localCoord, ← appLE_resInfLeft, ← appLE_resInfRight, h]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [σ.appLE_π_app _ _ _ le_rfl]
  simp

end Section

end VectorBundle

end MMP.Intersection.Scheme

/-! ### Bundles attached to `𝒪_X`-modules -/

namespace MMP.Intersection.Scheme.Modules

open Stacks.AlgebraicGeometry.ReflexiveModules (dualSheaf dualMap)
open MonoidalCategory

variable {X : Scheme.{u}}

/-- The dual of a module of finite presentation is quasi-coherent, so its vector bundle exists. -/
instance isQuasicoherent_dualSheaf (F : X.Modules) [F.IsFinitePresentation] :
    (dualSheaf F).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.InternalHomModules.isQuasicoherent_dualSheaf F inferInstance

/-- The bundle `𝔼(ℱ) = Spec(Sym ℱ^∨)` over `X` of an `𝒪_X`-module `ℱ` (Fulton B.3.2, B.5.5),
where `ℱ^∨ = 𝓗om(ℱ, 𝒪_X)`. It is defined whenever `ℱ^∨` is quasi-coherent, e.g. for `ℱ` of
finite presentation. When `ℱ` is locally free this is the vector bundle whose sheaf of sections
is `ℱ` (Fulton B.3.2); that comparison is not formalized here. -/
@[mmp "def_b_bundle_of_locally_free_sheaf"]
def bundle (F : X.Modules) [(dualSheaf F).IsQuasicoherent] : Scheme.{u} :=
  Scheme.Modules.vectorBundle X (dualSheaf F)

/-- The projection `𝔼(ℱ) ⟶ X`. -/
@[mmp "def_b_bundle_of_locally_free_sheaf"]
def bundleToBase (F : X.Modules) [(dualSheaf F).IsQuasicoherent] : bundle F ⟶ X :=
  Scheme.Modules.vectorBundleToBase X (dualSheaf F)

/-- The `X`-morphism `𝔼(ψ) : 𝔼(ℱ) ⟶ 𝔼(𝒢)` induced by `Sym(ψ^∨)` for `ψ : ℱ ⟶ 𝒢`. -/
@[mmp "def_b_bundle_of_locally_free_sheaf"]
def bundleMap {F G : X.Modules} [(dualSheaf F).IsQuasicoherent] [(dualSheaf G).IsQuasicoherent]
    (ψ : F ⟶ G) : bundle F ⟶ bundle G :=
  (Scheme.Modules.vectorBundleMap X (dualMap ψ)).left

/-- The morphism `𝔼(ψ) : 𝔼(ℱ) ⟶ 𝔼(𝒢)` commutes with the projections to `X`. -/
@[reassoc (attr := simp)]
lemma bundleMap_bundleToBase {F G : X.Modules} [(dualSheaf F).IsQuasicoherent]
    [(dualSheaf G).IsQuasicoherent] (ψ : F ⟶ G) :
    bundleMap ψ ≫ bundleToBase G = bundleToBase F :=
  Over.w (Scheme.Modules.vectorBundleMap X (dualMap ψ))

/-- The dual bundle `E^∨ = 𝔼(ℰ^∨)` of the bundle with sheaf of sections `ℰ` (Fulton B.3.3). -/
@[mmp "def_b_dual_bundle"]
abbrev dualBundle (E : X.Modules) [(dualSheaf (dualSheaf E)).IsQuasicoherent] : Scheme.{u} :=
  bundle (dualSheaf E)

/-- The tensor product `ℰ ⊗_{𝒪_X} ℱ` of `𝒪_X`-modules: the sheafified tensor product, with
unit `𝒪_X` (Stacks 01CA). -/
@[mmp "def_b_tensor_product_bundle"]
instance monoidalCategory : MonoidalCategory X.Modules :=
  Stacks.SheafOfModules.OnSpace.monoidal X.toRingedSpace

/-- The tensor product bundle `E ⊗ F = 𝔼(ℰ ⊗_{𝒪_X} ℱ)` of the bundles with sheaves of sections
`ℰ` and `ℱ` (Fulton B.3.3). -/
@[mmp "def_b_tensor_product_bundle"]
abbrev tensorBundle (E F : X.Modules) [(dualSheaf (E ⊗ F)).IsQuasicoherent] : Scheme.{u} :=
  bundle (E ⊗ F)

/-- The `n`-th tensor power `L^{⊗n}` of an `𝒪_X`-module, for `n : ℕ`; `L^{⊗0} = 𝒪_X`. -/
@[mmp "def_b_line_bundle_power", mmp "not_pab_dual_bundle"]
def tensorPow (L : X.Modules) : ℕ → X.Modules
  | 0 => 𝟙_ X.Modules
  | n + 1 => tensorPow L n ⊗ L

/-- `L^{⊗0}` is the unit `𝒪_X`. -/
@[simp]
lemma tensorPow_zero (L : X.Modules) : tensorPow L 0 = 𝟙_ X.Modules := rfl

/-- `L^{⊗(n+1)} = L^{⊗n} ⊗ L`. -/
lemma tensorPow_succ (L : X.Modules) (n : ℕ) : tensorPow L (n + 1) = tensorPow L n ⊗ L := rfl

/-- The `n`-th tensor power `L^{⊗n}` for `n : ℤ` (Fulton B.3.5, Lazarsfeld): the `n`-fold tensor
power of `L` for `n ≥ 0` and the `(-n)`-fold tensor power of the dual `L^∨` for `n < 0`. -/
@[mmp "def_b_line_bundle_power", mmp "not_pab_dual_bundle"]
def tensorZPow (L : X.Modules) : ℤ → X.Modules
  | .ofNat n => tensorPow L n
  | .negSucc n => tensorPow (dualSheaf L) (n + 1)

/-- For `n : ℕ`, the integer tensor power is the natural one. -/
@[simp]
lemma tensorZPow_natCast (L : X.Modules) (n : ℕ) : tensorZPow L n = tensorPow L n := rfl

/-- `L^{⊗0}` for the integer power is the unit `𝒪_X`. -/
@[simp]
lemma tensorZPow_zero (L : X.Modules) : tensorZPow L 0 = 𝟙_ X.Modules := rfl

/-- `L^{⊗(-(n+1))} = (L^∨)^{⊗(n+1)}`. -/
@[simp]
lemma tensorZPow_negSucc (L : X.Modules) (n : ℕ) :
    tensorZPow L (Int.negSucc n) = tensorPow (dualSheaf L) (n + 1) := rfl

/-- The line bundle `L^{⊗n} = 𝔼(ℒ^{⊗n})` for the line bundle with sheaf of sections `ℒ` and
`n : ℤ` (Fulton B.3.5). -/
@[mmp "def_b_line_bundle_power"]
abbrev lineBundlePow (L : X.Modules) (n : ℤ) [(dualSheaf (tensorZPow L n)).IsQuasicoherent] :
    Scheme.{u} :=
  bundle (tensorZPow L n)

/-! ### Projective bundles -/

open Stacks.AlgebraicGeometry.RelativeProj (relativeProj)
open Stacks.Tag01VMRelativeVeryAmple (symAlgebra)

/-- The projective bundle `ℙ(ℱ) = Proj_{𝒪_X}(Sym ℱ)` of one-dimensional quotients of a
quasi-coherent `𝒪_X`-module `ℱ` (Lazarsfeld, App. A; EGA II 4.1.1): the relative `Proj` of the
quasi-coherent graded `𝒪_X`-algebra `Sym(ℱ)`. -/
@[mmp "def_pab_projective_bundle"]
abbrev projectiveBundle (F : X.Modules) [F.IsQuasicoherent] : Scheme.{u} :=
  (relativeProj (symAlgebra F)).scheme

/-- The projection `ℙ(ℱ) ⟶ X`. -/
@[mmp "def_pab_projective_bundle"]
abbrev projectiveBundleToBase (F : X.Modules) [F.IsQuasicoherent] : projectiveBundle F ⟶ X :=
  (relativeProj (symAlgebra F)).toBase

/-- The Serre line bundle `𝒪_{ℙ(ℱ)}(1) = S(1)^∼` on `ℙ(ℱ)`, for `S = Sym(ℱ)`: the sheaf glued
from the twists `S(1)_{(t)}` over the charts `Proj Γ(U, S)` of the affine opens `U` of `X`. -/
abbrev projectiveBundleTwistOne (F : X.Modules) [F.IsQuasicoherent] :
    (projectiveBundle F).Modules :=
  Stacks.Tag01VMVeryAmple.twistOne F

/-- The Serre twist `𝒪_{ℙ(ℱ)}(m) = S(m)^∼` on `ℙ(ℱ) = Proj_{𝒪_X} S`, for `S = Sym(ℱ)` and
`m : ℤ` (Lazarsfeld, App. A): the quasi-coherent sheaf associated to the graded `S`-module
`S(m)`, `S(m)_k = S_{m+k}`. Over an affine open `U` of `X` it is the sheaf `S(m)^∼` on the chart
`Proj Γ(U, S)`, whose sections on `D_+(t)` for homogeneous `t ∈ Γ(U, S)` are the degree-zero
part `S(m)_{(t)}`; these are glued along the comparisons of the charts over nested affine opens,
which satisfy the cocycle condition in every degree. -/
@[mmp "def_pab_serre_line_bundle"]
def serreTwist (F : X.Modules) [F.IsQuasicoherent] (m : ℤ) : (projectiveBundle F).Modules :=
  Stacks.AlgebraicGeometry.ChartTransRelativeProj.gluedTwist (symAlgebra F) m
    (Stacks.AlgebraicGeometry.ProjTwistCocycle.isNestedCocycle (symAlgebra F) m)

/-- Over an affine open `U` of `X`, the Serre twist `𝒪_{ℙ(ℱ)}(m)` restricts along the chart
`Proj Γ(U, Sym ℱ) ⟶ ℙ(ℱ)` to the sheaf `S(m)^∼` associated to the graded module `S(m)` over
`S = Γ(U, Sym ℱ)`. -/
@[mmp "def_pab_serre_line_bundle"]
def serreTwistChartIso (F : X.Modules) [F.IsQuasicoherent] (m : ℤ) (U : X.Opens)
    (hU : IsAffineOpen U) :
    Scheme.Modules.restrict (serreTwist F m) ((relativeProj (symAlgebra F)).chart U hU) ≅
      ProjectiveSpectrum.Proj.twistingSheaf ((symAlgebra F).grading U) m :=
  Stacks.Tag01VMVeryAmple.gluedChartIso (symAlgebra F) m _ U hU

/-- In degree one the Serre twist is the Serre line bundle `𝒪_{ℙ(ℱ)}(1)`,
`projectiveBundleTwistOne ℱ`. -/
@[mmp "def_pab_serre_line_bundle"]
theorem serreTwist_one (F : X.Modules) [F.IsQuasicoherent] :
    serreTwist F 1 = projectiveBundleTwistOne F :=
  rfl

/-- The chart identification of `serreTwist ℱ 1` is that of `projectiveBundleTwistOne ℱ`. -/
theorem serreTwistChartIso_one (F : X.Modules) [F.IsQuasicoherent] (U : X.Opens)
    (hU : IsAffineOpen U) :
    serreTwistChartIso F 1 U hU = Stacks.Tag01VMVeryAmple.twistOneChartIso F U hU :=
  rfl

/-- The projective bundle of lines `ℙ(E) = Proj(Sym ℰ^∨)` of the vector bundle with sheaf of
sections `ℰ` (Fulton B.5.5), which is the bundle `ℙ_sub(E) = ℙ(E^*)` of one-dimensional
subspaces of Lazarsfeld. Its line bundle `𝒪_E(1)` is `projectiveBundleTwistOne (dualSheaf E)`. -/
@[mmp "def_b_projective_bundle", mmp "def_pab_projective_bundle_of_subspaces"]
abbrev projectiveBundleOfLines (E : X.Modules) [(dualSheaf E).IsQuasicoherent] : Scheme.{u} :=
  projectiveBundle (dualSheaf E)

/-- The projection `p : ℙ(E) ⟶ X` of the projective bundle of lines. -/
@[mmp "def_b_projective_bundle", mmp "def_pab_projective_bundle_of_subspaces"]
abbrev projectiveBundleOfLinesToBase (E : X.Modules) [(dualSheaf E).IsQuasicoherent] :
    projectiveBundleOfLines E ⟶ X :=
  projectiveBundleToBase (dualSheaf E)

/-- The line bundle `𝒪_E(1)` on the projective bundle of lines `ℙ(E) = Proj(Sym ℰ^∨)`
(Fulton B.5.5). -/
@[mmp "def_b_projective_bundle"]
abbrev projectiveBundleOfLinesTwistOne (E : X.Modules) [(dualSheaf E).IsQuasicoherent] :
    (projectiveBundleOfLines E).Modules :=
  projectiveBundleTwistOne (dualSheaf E)

/-! ### Locally free modules of constant rank (Lazarsfeld) -/

/-- An `𝒪_X`-module `E` is *locally free of rank `e`* (Lazarsfeld's vector bundle of rank `e`):
every point has an open neighbourhood `U` with `E|_U ≅ 𝒪_U^{⊕e}`. -/
@[mmp "def_pab_vector_bundle"]
def IsLocallyFreeOfRank (E : X.Modules) (e : ℕ) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty (E.restrict U.ι ≅ SheafOfModules.free (ULift.{u} (Fin e)))

/-- A *line bundle* in Lazarsfeld's sense: a locally free `𝒪_X`-module of rank one. -/
@[mmp "def_pab_vector_bundle"]
abbrev IsLineBundle (E : X.Modules) : Prop := IsLocallyFreeOfRank E 1

/-- The fibre `E(x) = E_x ⊗_{𝒪_{X,x}} κ(x)` of an `𝒪_X`-module at a point, realized as the
global sections of the pullback of `E` along `Spec κ(x) ⟶ X`. -/
@[mmp "def_pab_vector_bundle"]
def fiber (E : X.Modules) (x : X) : Type u :=
  Γ((Scheme.Modules.pullback (X.fromSpecResidueField x)).obj E, ⊤)

/-- The fibre is an abelian group under addition of global sections. -/
instance instAddCommGroupFiber (E : X.Modules) (x : X) : AddCommGroup (fiber E x) :=
  inferInstanceAs (AddCommGroup Γ((Scheme.Modules.pullback (X.fromSpecResidueField x)).obj E, ⊤))

/-- The fibre is a `κ(x)`-vector space, through `κ(x) ≅ Γ(Spec κ(x), ⊤)`. -/
instance instModuleFiber (E : X.Modules) (x : X) : Module (X.residueField x) (fiber E x) :=
  letI : Module Γ(Spec (X.residueField x), ⊤) (fiber E x) :=
    inferInstanceAs (Module _ Γ((Scheme.Modules.pullback (X.fromSpecResidueField x)).obj E, ⊤))
  Module.compHom _ (Scheme.ΓSpecIso (X.residueField x)).inv.hom

/-- The linear map `u(x) : E(x) ⟶ F(x)` induced on fibres by `u : E ⟶ F`. -/
@[mmp "def_pab_vector_bundle"]
def fiberMap {E F : X.Modules} (u : E ⟶ F) (x : X) :
    fiber E x →ₗ[X.residueField x] fiber F x where
  toFun := ((Scheme.Modules.pullback (X.fromSpecResidueField x)).map u).app ⊤
  map_add' := map_add _
  map_smul' _ _ := Scheme.Modules.Hom.app_smul _ _ _

/-- Evaluation of `fiberMap` on a fibre element. -/
@[simp]
lemma fiberMap_apply {E F : X.Modules} (u : E ⟶ F) (x : X) (v : fiber E x) :
    fiberMap u x v = ((Scheme.Modules.pullback (X.fromSpecResidueField x)).map u).app ⊤ v :=
  rfl

/-! ### Homomorphisms and sub-bundles -/

/-- A *sub-bundle* (Fulton B.3.3, B.5.6): a homomorphism `φ : ℱ ⟶ ℰ` of vector bundles, i.e. of
locally free `𝒪_X`-modules of finite constant rank, which is injective with locally free
cokernel. It is a *line sub-bundle* if moreover `ℱ` has rank one. -/
@[mmp "def_b_subbundle"]
structure IsSubbundle {F E : X.Modules} (φ : F ⟶ E) : Prop where
  /-- The source is locally free of some constant rank. -/
  exists_rank_source : ∃ r, IsLocallyFreeOfRank F r
  /-- The target is locally free of some constant rank. -/
  exists_rank_target : ∃ r, IsLocallyFreeOfRank E r
  /-- The homomorphism `φ` is injective. -/
  mono : Mono φ
  /-- The cokernel of `φ` is locally free. -/
  isLocallyFree_cokernel : (cokernel φ).IsLocallyFree

/-- A *line sub-bundle*: a sub-bundle of rank one (Fulton B.3.3). -/
@[mmp "def_b_subbundle"]
structure IsLineSubbundle {F E : X.Modules} (φ : F ⟶ E) : Prop extends IsSubbundle φ where
  /-- The source has rank one. -/
  isLocallyFreeOfRank_one : IsLocallyFreeOfRank F 1

end MMP.Intersection.Scheme.Modules

namespace MMP.Intersection.Scheme

open Stacks.AlgebraicGeometry.ReflexiveModules (dualSheaf)

variable {X Y : Scheme.{u}}

/-- The relative tangent bundle `T_{X/Y} = 𝔼((Ω¹_{X/Y})^∨)` of `f : X ⟶ Y` (Fulton B.2.7): the
bundle whose sheaf of sections is the dual of `Ω¹_{X/Y}`. Fulton takes `f` smooth of relative
dimension `n`; the construction makes sense whenever `(Ω¹_{X/Y})^∨∨` is quasi-coherent. -/
abbrev Hom.relativeTangentBundle (f : X ⟶ Y)
    [(dualSheaf (dualSheaf f.relativeDifferentials)).IsQuasicoherent] : Scheme.{u} :=
  Modules.bundle (dualSheaf f.relativeDifferentials)

/-- The tangent bundle `T_X = T_{X/Spec K}` of a scheme over a field `K` (Fulton B.2.7). -/
abbrev tangentBundle (K : Type u) [Field K] (X : Scheme.{u}) [X.Over (Spec (.of K))]
    [(dualSheaf (dualSheaf (X ↘ Spec (.of K)).relativeDifferentials)).IsQuasicoherent] :
    Scheme.{u} :=
  Hom.relativeTangentBundle (X ↘ Spec (.of K))

end MMP.Intersection.Scheme
