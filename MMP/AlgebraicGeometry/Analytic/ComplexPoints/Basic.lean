module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.Analysis.Complex.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic
/-!
# Complex schemes and their underlying spaces (Fulton, §19.1)

A *complex scheme* is an algebraic scheme `X` over `ℂ` which admits a closed imbedding into a
non-singular complex variety. Its *underlying space* is the set `X(ℂ)` of closed points of `X`
with the classical (analytic) topology, and a morphism of complex schemes induces a continuous
map of underlying spaces.

The classical topology makes sense over any algebraically closed topological field `K` (`ℂ`, or
`ℂ_p`), and for any scheme `X` over `K`: on the set of `K`-points `p : Spec K ⟶ X` over `K`, it
is the coarsest topology in which, for every open `U ⊆ X` and every section `g ∈ Γ(X, U)`, the
set of points landing in `U` is open and evaluation `p ↦ g(p) ∈ K` is continuous on it. For `X`
affine, embedded in `𝔸ⁿ` by generators `g₁, …, gₙ` of `Γ(X, X)`, it is the topology induced from
`Kⁿ`; in general the affine pieces are open and glue.

## Main definitions

* `MMP.IsComplexScheme X`: `X` is a complex scheme.
* `MMP.UnderlyingSpace K X`: the set `X(K)` of `K`-points of a scheme `X` over `K`,
  with the classical topology when `K` is a topological field.
* `MMP.UnderlyingSpace.eval`: the value `g(p) ∈ K` of a section `g ∈ Γ(X, U)` at a
  point `p ∈ U(K)`.
* `MMP.UnderlyingSpace.equivClosedPoints`: for `X` locally of finite type over an
  algebraically closed `K`, the `K`-points are the closed points of `X`.
* `MMP.UnderlyingSpace.map f`: the continuous map induced by a morphism `f` over
  `K`.

## Main results

* `MMP.UnderlyingSpace.isOpen_setOf_le_preimage`,
  `MMP.UnderlyingSpace.continuous_eval`: the defining properties of the classical
  topology.
* `MMP.UnderlyingSpace.eval_mapFun`: `g(f(p)) = (f^* g)(p)`.
* `MMP.UnderlyingSpace.map_id`, `map_comp`: functoriality.

## Implementation notes

Points of the underlying space are encoded as `K`-points `p : Spec K ⟶ X` with
`p ≫ (X → Spec K) = 𝟙`; for `X` locally of finite type over the algebraically closed field `K`
these are in bijection with the closed points of `X` (`equivClosedPoints`, which is Mathlib's
`AlgebraicGeometry.pointEquivClosedPoint`), the bijection sending `p` to the image of the unique
point of `Spec K`. On `K`-points a morphism over `K` acts by composition, so no separate argument
that morphisms of algebraic schemes send closed points to closed points is needed.

That a proper morphism induces a proper map of underlying spaces is proved downstream, as
`MMP.IsComplexScheme.isProperMap_map`, since it needs the compactness of `ℙⁿ(ℂ)`
and Chow's lemma.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace MMP

/-- A *complex scheme* (Fulton, §19.1): an algebraic scheme `X` over `ℂ` (its structure morphism
is locally of finite type and quasi-compact) which admits a closed imbedding over `ℂ` into a
non-singular complex variety, that is, a smooth variety over `ℂ` in the sense of
`AlgebraicGeometry.IsSmoothVariety` (integral, separated, of finite type and smooth). -/
class IsComplexScheme (X : Scheme.{0}) [X.Over (Spec (.of ℂ))] : Prop
    extends LocallyOfFiniteType (X ↘ Spec (.of ℂ)), QuasiCompact (X ↘ Spec (.of ℂ)) where
  exists_isClosedImmersion : ∃ (V : Scheme.{0}) (_ : V.Over (Spec (.of ℂ)))
    (_ : IsSmoothVariety ℂ (V ↘ Spec (.of ℂ))) (i : X ⟶ V),
      i.IsOver (Spec (.of ℂ)) ∧ IsClosedImmersion i

/-- A smooth variety over `ℂ` is a complex scheme: it imbeds in itself. -/
instance IsComplexScheme.of_isSmoothVariety (X : Scheme.{0}) [X.Over (Spec (.of ℂ))]
    [IsSmoothVariety ℂ (X ↘ Spec (.of ℂ))] : IsComplexScheme X where
  exists_isClosedImmersion := ⟨X, inferInstance, inferInstance, 𝟙 X, inferInstance, inferInstance⟩

/-- The point `Spec ℂ` is a smooth variety over `ℂ`, for any structure morphism `Spec ℂ ⟶ Spec ℂ`
equal to the identity. -/
theorem isSmoothVariety_of_eq_id {f : Spec (.of ℂ) ⟶ Spec (.of ℂ)} (h : f = 𝟙 _) :
    IsSmoothVariety ℂ f := by
  subst h
  exact { }

/-- The *underlying space* `X(K)` of a scheme `X` over a field `K` (Fulton, §19.1, for `K = ℂ`):
the `K`-points `p : Spec K ⟶ X` over `K`. When `K` is a topological field it carries the
classical topology (`MMP.UnderlyingSpace.instTopologicalSpace`); when `K` is
algebraically closed and `X` is locally of finite type over `K` it is the set of closed points of
`X` (`MMP.UnderlyingSpace.equivClosedPoints`). -/
def UnderlyingSpace (K : Type u) [Field K] (X : Scheme.{u}) [X.Over (Spec (.of K))] : Type u :=
  {p : Spec (.of K) ⟶ X // p ≫ X ↘ Spec (.of K) = 𝟙 _}

namespace UnderlyingSpace

variable {K : Type u} [Field K]

section Points

variable {X : Scheme.{u}} [X.Over (Spec (.of K))]

/-- The `K`-point underlying a point of `X(K)`. -/
def toHom (p : UnderlyingSpace K X) : Spec (.of K) ⟶ X := p.1

/-- A point of `X(K)` composed with the structure morphism of `X` is the identity of `Spec K`. -/
@[reassoc (attr := simp)]
lemma toHom_comp_over (p : UnderlyingSpace K X) : p.toHom ≫ X ↘ Spec (.of K) = 𝟙 _ := p.2

/-- Two points of `X(K)` with the same underlying `K`-point are equal. -/
@[ext]
lemma ext {p q : UnderlyingSpace K X} (h : p.toHom = q.toHom) : p = q := Subtype.ext h

/-- The value `g(p) ∈ K` of a section `g ∈ Γ(X, U)` at a point `p` of `X(K)` lying in `U`. -/
def eval {U : X.Opens} (p : UnderlyingSpace K X) (hp : ⊤ ≤ p.toHom ⁻¹ᵁ U) (g : Γ(X, U)) : K :=
  (Scheme.ΓSpecIso (.of K)).hom (p.toHom.appLE U ⊤ hp g)

/-- The points of `X(K)` lying in `U` and at which `g ∈ Γ(X, U)` takes a value in `W ⊆ K`. -/
def evalPreimage (U : X.Opens) (g : Γ(X, U)) (W : Set K) : Set (UnderlyingSpace K X) :=
  {p | ∃ hp : ⊤ ≤ p.toHom ⁻¹ᵁ U, eval p hp g ∈ W}

variable [TopologicalSpace K]

/-- The *classical topology* on `X(K)`: generated by the sets of points `p ∈ U(K)` with
`g(p) ∈ W`, for `U ⊆ X` open, `g ∈ Γ(X, U)` and `W ⊆ K` open. -/
instance instTopologicalSpace : TopologicalSpace (UnderlyingSpace K X) :=
  .generateFrom {S | ∃ (U : X.Opens) (g : Γ(X, U)) (W : Set K), IsOpen W ∧
    S = evalPreimage U g W}

/-- For `W ⊆ K` open, the set of points `p ∈ U(K)` with `g(p) ∈ W` is open. -/
lemma isOpen_evalPreimage (U : X.Opens) (g : Γ(X, U)) {W : Set K} (hW : IsOpen W) :
    IsOpen (evalPreimage U g W) :=
  isOpen_generateFrom_of_mem ⟨U, g, W, hW, rfl⟩

/-- The points of `X(K)` lying in an open `U ⊆ X` form an open set, `U(K)`. -/
lemma isOpen_setOf_le_preimage (U : X.Opens) :
    IsOpen {p : UnderlyingSpace K X | ⊤ ≤ p.toHom ⁻¹ᵁ U} := by
  convert isOpen_evalPreimage U 0 isOpen_univ using 1
  ext p
  simp [evalPreimage]

/-- Evaluation of a section `g ∈ Γ(X, U)` is continuous on `U(K)`. -/
lemma continuous_eval (U : X.Opens) (g : Γ(X, U)) :
    Continuous fun p : {p : UnderlyingSpace K X // ⊤ ≤ p.toHom ⁻¹ᵁ U} ↦ eval p.1 p.2 g := by
  refine continuous_def.mpr fun W hW ↦ ?_
  have : (fun p : {p : UnderlyingSpace K X // ⊤ ≤ p.toHom ⁻¹ᵁ U} ↦ eval p.1 p.2 g) ⁻¹' W =
      Subtype.val ⁻¹' evalPreimage U g W := by
    ext p
    exact ⟨fun h ↦ ⟨p.2, h⟩, fun ⟨_, h⟩ ↦ h⟩
  rw [this]
  exact (isOpen_evalPreimage U g hW).preimage continuous_subtype_val

end Points

section ClosedPoints

variable [IsAlgClosed K] (X : Scheme.{u}) [X.Over (Spec (.of K))]
  [LocallyOfFiniteType (X ↘ Spec (.of K))]

/-- For `X` locally of finite type over an algebraically closed field `K`, the points of `X(K)`
are the closed points of `X`: `p` corresponds to the image of the unique point of `Spec K`. -/
def equivClosedPoints : UnderlyingSpace K X ≃ closedPoints X :=
  pointEquivClosedPoint (X ↘ Spec (.of K))

/-- The closed point corresponding to `p ∈ X(K)` is the image under `p` of the unique point of
`Spec K`. -/
lemma equivClosedPoints_apply (p : UnderlyingSpace K X) :
    (equivClosedPoints X p : X) = p.toHom (IsLocalRing.closedPoint K) :=
  rfl

end ClosedPoints

section Map

variable {X Y Z : Scheme.{u}} [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]
  [Z.Over (Spec (.of K))]

/-- The map `X(K) → Y(K)` induced by a morphism `f : X ⟶ Y` over `K`: composition with `f`. -/
def mapFun (f : X ⟶ Y) [f.IsOver (Spec (.of K))] (p : UnderlyingSpace K X) :
    UnderlyingSpace K Y :=
  ⟨p.toHom ≫ f, by rw [Category.assoc, comp_over f (Spec (.of K)), p.toHom_comp_over]⟩

/-- The `K`-point underlying `mapFun f p` is `p` composed with `f`. -/
@[simp]
lemma toHom_mapFun (f : X ⟶ Y) [f.IsOver (Spec (.of K))] (p : UnderlyingSpace K X) :
    (mapFun f p).toHom = p.toHom ≫ f :=
  rfl

/-- `g(f(p)) = (f^* g)(p)` for a section `g ∈ Γ(Y, V)`. -/
lemma eval_mapFun (f : X ⟶ Y) [f.IsOver (Spec (.of K))] (p : UnderlyingSpace K X) {V : Y.Opens}
    (hp : ⊤ ≤ (mapFun f p).toHom ⁻¹ᵁ V) (g : Γ(Y, V)) :
    eval (mapFun f p) hp g = eval (U := f ⁻¹ᵁ V) p hp (f.app V g) := by
  simp only [eval, toHom_mapFun, Scheme.Hom.comp_appLE]
  rfl

/-- The preimage under `mapFun f` of the points of `V(K)` at which `g ∈ Γ(Y, V)` takes a value
in `W` is the set of points of `(f⁻¹ V)(K)` at which `f^* g` takes a value in `W`. -/
lemma mapFun_preimage_evalPreimage (f : X ⟶ Y) [f.IsOver (Spec (.of K))] (V : Y.Opens)
    (g : Γ(Y, V)) (W : Set K) :
    mapFun f ⁻¹' evalPreimage V g W = evalPreimage (f ⁻¹ᵁ V) (f.app V g) W := by
  ext p
  exact ⟨fun ⟨hp, h⟩ ↦ ⟨hp, by rwa [eval_mapFun f p hp g] at h⟩,
    fun ⟨hp, h⟩ ↦ ⟨hp, by rwa [eval_mapFun f p hp g]⟩⟩

variable [TopologicalSpace K]

/-- The map `X(K) → Y(K)` induced by a morphism over `K` is continuous for the classical
topologies. -/
lemma continuous_mapFun (f : X ⟶ Y) [f.IsOver (Spec (.of K))] :
    Continuous (mapFun (K := K) f) := by
  refine continuous_generateFrom_iff.mpr ?_
  rintro _ ⟨V, g, W, hW, rfl⟩
  rw [mapFun_preimage_evalPreimage]
  exact isOpen_evalPreimage _ _ hW

/-- A morphism `f : X ⟶ Y` over `K` induces a continuous map `X(K) → Y(K)` of underlying
spaces (Fulton, §19.1). -/
def map (f : X ⟶ Y) [f.IsOver (Spec (.of K))] : C(UnderlyingSpace K X, UnderlyingSpace K Y) :=
  ⟨mapFun f, continuous_mapFun f⟩

/-- The `K`-point underlying `map f p` is `p` composed with `f`. -/
@[simp]
lemma toHom_map (f : X ⟶ Y) [f.IsOver (Spec (.of K))] (p : UnderlyingSpace K X) :
    (map f p).toHom = p.toHom ≫ f :=
  rfl

/-- The identity of `X` induces the identity of `X(K)`. -/
lemma map_id : map (K := K) (𝟙 X) = ContinuousMap.id _ := by
  ext p : 1
  exact UnderlyingSpace.ext (Category.comp_id _)

/-- The map of underlying spaces induced by `f ≫ g` is the composite of those induced by `f`
and `g`. -/
lemma map_comp (f : X ⟶ Y) (g : Y ⟶ Z) [f.IsOver (Spec (.of K))] [g.IsOver (Spec (.of K))] :
    map (K := K) (f ≫ g) = (map g).comp (map f) := by
  ext p : 1
  exact UnderlyingSpace.ext (Category.assoc _ _ _).symm

/-- Under `equivClosedPoints`, the map of underlying spaces is the map of closed points. -/
lemma equivClosedPoints_map [IsAlgClosed K] [LocallyOfFiniteType (X ↘ Spec (.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K))] (f : X ⟶ Y) [f.IsOver (Spec (.of K))]
    (p : UnderlyingSpace K X) :
    (equivClosedPoints Y (map f p) : Y) = f (equivClosedPoints X p : X) :=
  rfl

end Map

end UnderlyingSpace

end MMP
