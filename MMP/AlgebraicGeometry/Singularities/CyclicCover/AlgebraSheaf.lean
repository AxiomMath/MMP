module

public import StacksFrontier.AlgebraicGeometry.RelativeSpec.QuasicoherentSquare
public import StacksFrontier.AlgebraicGeometry.TorsionQuasicoherent.Local

/-!
# Sheaves of algebras cut out of a sheaf of rings by a local condition

Let `X` be a scheme and `𝓕` a sheaf of commutative rings on `X` receiving a morphism
`ι : 𝒪_X ⟶ 𝓕`. A family of subrings `𝒜(U) ⊆ 𝓕(U)` which contains the image of `𝒪_X(U)`, is
stable under restriction and is *local* (a section of `𝓕` lying in `𝒜` locally lies in `𝒜`)
is a sheaf of commutative `𝒪_X`-algebras. Its underlying `𝒪_X`-module is quasi-coherent as soon
as, for every affine open `U` and every `a ∈ 𝒪_X(U)`, the restriction `𝒜(U) → 𝒜(D(a))` is the
localization away from `a`.

## Main definitions

* `MMP.Mori.LocalSubalgebra`: a local family of subrings `𝒜(U) ⊆ 𝓕(U)` containing the image
  of `𝒪_X(U)` and stable under restriction.
* `MMP.Mori.LocalSubalgebra.presheaf`, `MMP.Mori.LocalSubalgebra.toPresheaf`: the presheaf of
  rings `U ↦ 𝒜(U)` and its structure morphism from `𝒪_X`.
* `MMP.Mori.LocalSubalgebra.algebraSheaf`: `𝒜` as a sheaf of commutative `𝒪_X`-algebras.
* `MMP.Mori.LocalSubalgebra.restrictₗ`: the restriction `𝒜(U) → 𝒜(V)`, `V ⊆ U`, as a
  `𝒪_X(U)`-linear map.

## Main results

* `MMP.Mori.LocalSubalgebra.isSheaf`: `U ↦ 𝒜(U)` is a sheaf.
* `MMP.Mori.LocalSubalgebra.isQuasicoherent_algebraSheaf`: the localization criterion for the
  quasi-coherence of `𝒜`.

## References

* [Stacks Project, Tag 01LQ](https://stacks.math.columbia.edu/tag/01LQ)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace MMP.Mori

variable {X : Scheme.{u}}

/-- A *local family of subalgebras* of a presheaf of commutative rings `𝓕` under `𝒪_X`: subrings
`𝒜(U) ⊆ 𝓕(U)` containing the image of `𝒪_X(U)`, stable under restriction, and such that a
section of `𝓕` which lies in `𝒜` locally lies in `𝒜`. -/
structure LocalSubalgebra (F : TopCat.Presheaf CommRingCat.{u} X) (ι : X.presheaf ⟶ F) where
  /-- The subring `𝒜(U) ⊆ 𝓕(U)`. -/
  carrier (U : X.Opens) : Subring (F.obj (op U))
  /-- `𝒜(U)` contains the image of `𝒪_X(U)`. -/
  algebraMap_mem {U : X.Opens} (r : Γ(X, U)) : (ι.app (op U)).hom r ∈ carrier U
  /-- `𝒜` is stable under restriction. -/
  map_mem {U V : X.Opens} (i : V ⟶ U) {x : F.obj (op U)} (hx : x ∈ carrier U) :
    (F.map i.op).hom x ∈ carrier V
  /-- Membership in `𝒜` is local. -/
  mem_of_locally {U : X.Opens} {x : F.obj (op U)}
    (hx : ∀ y ∈ U, ∃ (V : X.Opens) (i : V ⟶ U), y ∈ V ∧ (F.map i.op).hom x ∈ carrier V) :
    x ∈ carrier U

namespace LocalSubalgebra

variable {F : TopCat.Presheaf CommRingCat.{u} X} {ι : X.presheaf ⟶ F} (A : LocalSubalgebra F ι)

/-- The restriction `𝒜(U) → 𝒜(V)` along an inclusion `V ⊆ U`. -/
def restrict {U V : X.Opens} (i : V ⟶ U) : A.carrier U →+* A.carrier V :=
  (F.map i.op).hom.restrict (A.carrier U) (A.carrier V) fun _ hx => A.map_mem i hx

/-- The restriction of `x ∈ 𝒜(U)` to `V` is the restriction of `x` as a section of `𝓕`. -/
@[simp]
theorem coe_restrict {U V : X.Opens} (i : V ⟶ U) (x : A.carrier U) :
    (A.restrict i x : F.obj (op V)) = (F.map i.op).hom x :=
  rfl

/-- The presheaf of commutative rings `U ↦ 𝒜(U)`. -/
def presheaf : TopCat.Presheaf CommRingCat.{u} X where
  obj U := CommRingCat.of (A.carrier U.unop)
  map i := CommRingCat.ofHom (A.restrict i.unop)
  map_id U := CommRingCat.hom_ext (RingHom.ext fun x => Subtype.ext
    (congrArg (fun f => f.hom x.1) (F.map_id U)))
  map_comp i j := CommRingCat.hom_ext (RingHom.ext fun x => Subtype.ext
    (congrArg (fun f => f.hom x.1) (F.map_comp i j)))

/-- The structure map `𝒪_X(U) → 𝒜(U)`. -/
def algebraMap (U : X.Opens) : Γ(X, U) →+* A.carrier U :=
  (ι.app (op U)).hom.codRestrict (A.carrier U) A.algebraMap_mem

/-- The structure map `𝒪_X(U) → 𝒜(U)`, viewed in `𝓕(U)`, is `ι`. -/
@[simp]
theorem coe_algebraMap (U : X.Opens) (r : Γ(X, U)) :
    (A.algebraMap U r : F.obj (op U)) = (ι.app (op U)).hom r :=
  rfl

/-- The structure maps `𝒪_X(U) → 𝒜(U)` commute with restriction along `V ⊆ U`. -/
theorem restrict_algebraMap {U V : X.Opens} (i : V ⟶ U) (r : Γ(X, U)) :
    A.restrict i (A.algebraMap U r) = A.algebraMap V ((X.presheaf.map i.op).hom r) :=
  Subtype.ext (congrArg (fun f => f.hom r) (ι.naturality i.op)).symm

/-- The structure morphism `𝒪_X ⟶ 𝒜`. -/
def toPresheaf : X.presheaf ⟶ A.presheaf where
  app U := CommRingCat.ofHom (A.algebraMap U.unop)
  naturality _ _ i := CommRingCat.hom_ext (RingHom.ext fun r =>
    (A.restrict_algebraMap i.unop r).symm)

/-- **A local family of subalgebras of a sheaf is a sheaf.** -/
theorem isSheaf (hF : F.IsSheaf) : A.presheaf.IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing] at hF ⊢
  intro κ U sf hsf
  obtain ⟨s, hs, huniq⟩ := hF U (fun i => ((show A.carrier (U i) from sf i) : F.obj (op (U i))))
    fun i j => congrArg Subtype.val (hsf i j)
  have hmem : s ∈ A.carrier (iSup U) := A.mem_of_locally fun y hy => by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
    refine ⟨U i, Opens.leSupr U i, hi, ?_⟩
    rw [hs i]
    exact (show A.carrier (U i) from sf i).2
  refine ⟨(⟨s, hmem⟩ : A.carrier (iSup U)), fun i => Subtype.ext (hs i), fun t ht => ?_⟩
  exact Subtype.ext (huniq _ fun i => congrArg Subtype.val (ht i))

/-- `𝒜` as a sheaf of commutative rings. -/
def sheaf (hF : F.IsSheaf) : TopCat.Sheaf CommRingCat.{u} X :=
  ⟨A.presheaf, A.isSheaf hF⟩

/-- `𝒜` as a sheaf of commutative `𝒪_X`-algebras. -/
def algebraSheaf (hF : F.IsSheaf) : Stacks.RelativeSpec.AlgebraSheaf X :=
  Under.mk (Y := A.sheaf hF) { hom := A.toPresheaf }

/-- The `𝒪_X(U)`-module structure on `𝒜(V)`, `V ⊆ U`, through the structure morphism and
restriction. -/
@[instance_reducible]
def moduleOfLE {U V : X.Opens} (h : V ≤ U) : Module Γ(X, U) (A.carrier V) :=
  Module.compHom (A.carrier V) ((A.algebraMap V).comp (X.presheaf.map (homOfLE h).op).hom)

/-- The `𝒪_X(U)`-module structure on `𝒜(U)` through the structure morphism. -/
@[instance_reducible]
def moduleSections (U : X.Opens) : Module Γ(X, U) (A.carrier U) :=
  Module.compHom (A.carrier U) (A.algebraMap U)

/-- The restriction `𝒜(U) → 𝒜(V)`, `V ⊆ U`, as an `𝒪_X(U)`-linear map. -/
def restrictₗ {U V : X.Opens} (h : V ≤ U) :
    letI := A.moduleSections U
    letI := A.moduleOfLE h
    A.carrier U →ₗ[Γ(X, U)] A.carrier V :=
  letI := A.moduleSections U
  letI := A.moduleOfLE h
  { toFun := A.restrict (homOfLE h)
    map_add' := map_add _
    map_smul' := fun r x => by
      change A.restrict (homOfLE h) (A.algebraMap U r * x) =
        A.algebraMap V ((X.presheaf.map (homOfLE h).op).hom r) * A.restrict (homOfLE h) x
      rw [map_mul, restrict_algebraMap] }

/-- **The localization criterion for quasi-coherence.** If for every affine open `U` and every
`a ∈ 𝒪_X(U)` the restriction `𝒜(U) → 𝒜(D(a))` is the localization away from `a`, then `𝒜` is a
quasi-coherent `𝒪_X`-algebra. -/
theorem isQuasicoherent_algebraSheaf (hF : F.IsSheaf)
    (h : ∀ U : X.Opens, IsAffineOpen U → ∀ a : Γ(X, U),
      letI := A.moduleSections U
      letI := A.moduleOfLE (X.basicOpen_le a)
      IsLocalizedModule.Away a (A.restrictₗ (X.basicOpen_le a))) :
    (A.algebraSheaf hF).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.TorsionQuasicoherent.isQuasicoherent_of_isLocalizedModule_restrictₗ _ h

end LocalSubalgebra

end MMP.Mori

end
