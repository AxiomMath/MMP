module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Parameter points of a family, and the fibres over them (Fulton, §10.1)

In a family over a base `T`, Fulton writes "`t ∈ T`" for a *regular closed point* `t` of `T`: a
closed point whose local ring `𝒪_{t,T}` is a regular local ring. For such a point, `κ(t)` is the
residue field of `𝒪_{t,T}`, `{t}` is the scheme `Spec κ(t)`, and `t : {t} → T` is the canonical
closed imbedding. For a morphism `p : 𝒴 → T`, the *fibre* of `𝒴` over `t` is
`Y_t = 𝒴 ×_T {t}`, with its inclusion `i_t : Y_t → 𝒴` and projection `p_t : Y_t → {t}`.

## Main definitions

* `MMP.ParameterPoint T`: the regular closed points `t ∈ T`.
* `MMP.ParameterPoint.residueField t`: the residue field `κ(t)`.
* `MMP.ParameterPoint.spec t`: the scheme `{t} = Spec κ(t)`.
* `MMP.ParameterPoint.ι t`: the canonical morphism `t : {t} → T`.
* `MMP.ParameterPoint.ofSection`: the parameter point through a rational section.
* `MMP.ParameterPoint.fibre p t`, `MMP.ParameterPoint.fibreι p t`,
  `MMP.ParameterPoint.fibreProj p t`: the fibre `Y_t`, `i_t : Y_t → 𝒴` and `p_t : Y_t → {t}`.
* `MMP.ParameterPoint.fibreOverBase`: the fibre of a `K`-scheme is a `K`-scheme through `i_t`.
* `MMP.ParameterPoint.fibreHomeo p t`: the homeomorphism between `Y_t` and `p⁻¹(t)`.
* `MMP.ParameterPoint.fibreMap f h t`: the morphism of fibres `f_t : X_t → Y_t` induced by a
  morphism `f : 𝒳 → 𝒴` over `T`.

## Main results

* `MMP.ParameterPoint.isClosedImmersion_ι`: `t : {t} → T` is a closed imbedding.
* `MMP.ParameterPoint.range_ι`: its image is the point `t`.
* `MMP.ParameterPoint.isIso_ι_comp_of_isAlgClosed`: over an algebraically closed field `K`,
  every parameter point of a scheme locally of finite type over `K` is `K`-rational:
  `{t} → T → Spec K` is an isomorphism.
* `MMP.ParameterPoint.exists_isIso_comp_ι_eq`: a `K`-rational section through a `K`-rational
  parameter point `t` factors through `t : {t} → T` by an isomorphism `Spec K ≅ {t}`.
* `MMP.ParameterPoint.isPullback_fibre`: `i_t`, `p_t`, `p` and `t : {t} → T` form a fibre square.
* `MMP.ParameterPoint.range_fibreι`: the image of `i_t` is `p⁻¹(t)`.
* `MMP.ParameterPoint.isPullback_fibreMap`: `X_t = 𝒳 ×_𝒴 Y_t`.

## Implementation notes

The residue field `κ(t)` is Mathlib's `AlgebraicGeometry.Scheme.residueField`, `t : {t} → T` is
`AlgebraicGeometry.Scheme.fromSpecResidueField`, and the fibre is Mathlib's scheme-theoretic
fibre `AlgebraicGeometry.Scheme.Hom.fiber p t.point`. A `K`-rational parameter point is one for
which `{t} → T → Spec K` is an isomorphism, i.e. `K → κ(t)` is an isomorphism.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §10.1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace MMP

/-- The *parameter points* `t ∈ T` of a scheme `T` (Fulton, §10.1): the regular closed points of
`T`, that is the closed points `t` whose local ring `𝒪_{t,T}` is a regular local ring. -/
@[ext]
structure ParameterPoint (T : Scheme.{u}) : Type u where
  /-- The parameter point given by a closed point `x` of `T` whose local ring `𝒪_{x,T}` is a
  regular local ring. -/
  ofIsClosed ::
  /-- The closed point of `T` underlying a parameter point `t`. -/
  point : T
  /-- The underlying point of a parameter point is a closed point of `T`. -/
  isClosed_point : IsClosed ({point} : Set T)
  /-- The local ring `𝒪_{t,T}` of a parameter point is a regular local ring. -/
  isRegularLocalRing_stalk : IsRegularLocalRing (T.presheaf.stalk point)

namespace ParameterPoint

attribute [instance] isRegularLocalRing_stalk

variable {T : Scheme.{u}}

/-- The underlying point of `ofIsClosed x hx hreg` is `x`. -/
@[simp]
theorem point_ofIsClosed (x : T) (hx : IsClosed ({x} : Set T))
    (hreg : IsRegularLocalRing (T.presheaf.stalk x)) : (ofIsClosed x hx hreg).point = x :=
  rfl

/-- A parameter point is determined by its underlying point of `T`. -/
theorem point_injective : Function.Injective (point : ParameterPoint T → T) :=
  fun _ _ h ↦ ParameterPoint.ext h

/-- A point `x` of `T` underlies a parameter point iff it is a closed point with regular local
ring. -/
theorem exists_point_eq_iff (x : T) :
    (∃ t : ParameterPoint T, t.point = x) ↔
      IsClosed ({x} : Set T) ∧ IsRegularLocalRing (T.presheaf.stalk x) := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t.isClosed_point, inferInstance⟩
  · rintro ⟨hx, hreg⟩
    exact ⟨ofIsClosed x hx hreg, rfl⟩

/-- The residue field `κ(t)` of the local ring `𝒪_{t,T}` of a parameter point. -/
abbrev residueField (t : ParameterPoint T) : CommRingCat.{u} := T.residueField t.point

/-- The scheme `{t} = Spec κ(t)` of a parameter point `t`. -/
abbrev spec (t : ParameterPoint T) : Scheme.{u} := Spec t.residueField

/-- The canonical morphism `t : {t} = Spec κ(t) → T` of a parameter point `t`. -/
abbrev ι (t : ParameterPoint T) : t.spec ⟶ T := T.fromSpecResidueField t.point

/-- The canonical morphism `t : {t} → T` is a closed imbedding. -/
instance isClosedImmersion_ι (t : ParameterPoint T) : IsClosedImmersion t.ι :=
  isClosed_singleton_iff_isClosedImmersion.1 t.isClosed_point

/-- The image of `t : {t} → T` is the point `t`. -/
theorem range_ι (t : ParameterPoint T) : Set.range t.ι = {t.point} :=
  T.range_fromSpecResidueField t.point

section Rational

variable (K : Type u) [Field K] [T.Over (Spec (.of K))]

/-- **Closed points over an algebraically closed field are rational.** For a scheme `T` locally of
finite type over an algebraically closed field `K` and a parameter point `t` of `T`, the composite
`{t} → T → Spec K` is an isomorphism, i.e. `κ(t) = K`. -/
theorem isIso_ι_comp_of_isAlgClosed [IsAlgClosed K] [LocallyOfFiniteType (T ↘ Spec (.of K))]
    (t : ParameterPoint T) : IsIso (t.ι ≫ T ↘ Spec (.of K)) := by
  rw [ι, ← SpecMap_residueFieldIsoBase_inv (T ↘ Spec (.of K)) t.point t.isClosed_point]
  infer_instance

/-- A `K`-rational section `P : Spec K → T` through a `K`-rational parameter point `t` factors as
an isomorphism `Spec K ≅ {t}` followed by `t : {t} → T`. -/
theorem exists_isIso_comp_ι_eq (P : Spec (.of K) ⟶ T) (hP : P ≫ T ↘ Spec (.of K) = 𝟙 _)
    (t : ParameterPoint T) (ht : t.point = P (IsLocalRing.closedPoint K))
    [IsIso (t.ι ≫ T ↘ Spec (.of K))] :
    ∃ s : Spec (.of K) ⟶ t.spec, IsIso s ∧ s ≫ t.ι = P := by
  obtain ⟨s, hs⟩ : ∃ s : Spec (.of K) ⟶ Spec (T.residueField t.point),
      s ≫ T.fromSpecResidueField t.point = P :=
    ht ▸ ⟨_, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K T P⟩
  refine ⟨s, ?_, hs⟩
  haveI : IsIso (s ≫ (t.ι ≫ T ↘ Spec (.of K))) := by
    rw [reassoc_of% hs, hP]; infer_instance
  exact IsIso.of_isIso_comp_right s (t.ι ≫ T ↘ Spec (.of K))

/-- The image of a `K`-rational section `P : Spec K → T` is a closed point. -/
theorem isClosed_singleton_of_section (P : Spec (.of K) ⟶ T) (hP : P ≫ T ↘ Spec (.of K) = 𝟙 _) :
    IsClosed ({P (IsLocalRing.closedPoint K)} : Set T) := by
  haveI : IsClosedImmersion P := isClosedImmersion_of_comp_eq_id (T ↘ Spec (.of K)) P hP
  have h := P.isClosedEmbedding.isClosedMap _ (IsLocalRing.isClosed_singleton_closedPoint K)
  convert h using 1
  exact (Set.image_singleton).symm

/-- **The parameter point of a rational section.** For a `K`-rational section `P : Spec K → T`
whose image has a regular local ring, the image of `P` is a parameter point of `T`. -/
def ofSection (P : Spec (.of K) ⟶ T) (hP : P ≫ T ↘ Spec (.of K) = 𝟙 _)
    (hreg : IsRegularLocalRing (T.presheaf.stalk (P (IsLocalRing.closedPoint K)))) :
    ParameterPoint T :=
  ofIsClosed (P (IsLocalRing.closedPoint K)) (isClosed_singleton_of_section K P hP) hreg

/-- The underlying point of `ofSection K P hP hreg` is the image of `P`. -/
@[simp]
theorem point_ofSection (P : Spec (.of K) ⟶ T) (hP : P ≫ T ↘ Spec (.of K) = 𝟙 _)
    (hreg : IsRegularLocalRing (T.presheaf.stalk (P (IsLocalRing.closedPoint K)))) :
    (ofSection K P hP hreg).point = P (IsLocalRing.closedPoint K) :=
  rfl

end Rational

section Fibre

variable {𝒴 : Scheme.{u}} (p : 𝒴 ⟶ T) (t : ParameterPoint T)

/-- The *fibre* `Y_t = 𝒴 ×_T {t}` of a morphism `p : 𝒴 → T` over a parameter point `t ∈ T`
(Fulton, §10.1). -/
abbrev fibre : Scheme.{u} := p.fiber t.point

/-- The projection `p_t : Y_t → {t}` of the fibre of `p` over `t`. -/
abbrev fibreProj : fibre p t ⟶ t.spec := p.fiberToSpecResidueField t.point

/-- The inclusion `i_t : Y_t → 𝒴` of the fibre of `p` over `t`. -/
abbrev fibreι : fibre p t ⟶ 𝒴 := p.fiberι t.point

/-- The fibre `Y_t` is a `κ(t)`-scheme, through `p_t : Y_t → {t} = Spec κ(t)`. -/
instance fibreOver : (fibre p t).Over t.spec := p.fiberOverSpecResidueField t.point

/-- The structure morphism of the `κ(t)`-scheme `Y_t` is `p_t : Y_t → {t}`. -/
theorem fibreOver_hom : (fibre p t ↘ t.spec) = fibreProj p t := rfl

section Base

variable (K : Type u) [Field K] [𝒴.Over (Spec (.of K))]

/-- The fibre `Y_t` is a scheme over the base field `K` of `𝒴`, through `i_t : Y_t → 𝒴`. -/
instance fibreOverBase : (fibre p t).Over (Spec (.of K)) :=
  ⟨fibreι p t ≫ 𝒴 ↘ Spec (.of K)⟩

/-- The inclusion `i_t : Y_t → 𝒴` is a morphism over `K`. -/
instance isOver_fibreι : (fibreι p t).IsOver (Spec (.of K)) :=
  ⟨rfl⟩

end Base

/-- The fibre `Y_t` is a fibre product: `i_t`, `p_t`, `p` and `t : {t} → T` form a fibre
square. -/
theorem isPullback_fibre : IsPullback (fibreι p t) (fibreProj p t) p t.ι :=
  IsPullback.of_hasPullback p t.ι

/-- The fibre square commutes: `i_t ≫ p = p_t ≫ t`. -/
@[reassoc]
theorem fibreι_comp : fibreι p t ≫ p = fibreProj p t ≫ t.ι :=
  p.fiber_fac t.point

/-- The inclusion `i_t : Y_t → 𝒴` of a fibre is a closed imbedding. -/
instance isClosedImmersion_fibreι : IsClosedImmersion (fibreι p t) :=
  inferInstanceAs (IsClosedImmersion (pullback.fst p t.ι))

/-- The image of `i_t : Y_t → 𝒴` is `p⁻¹(t)`. -/
theorem range_fibreι : Set.range (fibreι p t) = p ⁻¹' {t.point} :=
  p.range_fiberι t.point

/-- The fibre `Y_t` is homeomorphic to `p⁻¹(t)`. -/
def fibreHomeo : fibre p t ≃ₜ p ⁻¹' {t.point} :=
  p.fiberHomeo t.point

/-- The point of `p⁻¹(t)` corresponding to `x ∈ Y_t` is `i_t x`. -/
@[simp]
theorem fibreHomeo_apply (x : fibre p t) : (fibreHomeo p t x).1 = fibreι p t x :=
  p.fiberHomeo_apply t.point x

/-- `i_t` sends the preimage of `x ∈ p⁻¹(t)` under `fibreHomeo` back to `x`. -/
@[simp]
theorem fibreι_fibreHomeo_symm (x : p ⁻¹' {t.point}) :
    fibreι p t ((fibreHomeo p t).symm x) = x :=
  p.fiberι_fiberHomeo_symm t.point x

/-- Two morphisms into a fibre `Y_t` agree if they agree after `i_t` and after `p_t`. -/
theorem fibre_hom_ext {W : Scheme.{u}} {a b : W ⟶ fibre p t}
    (h₁ : a ≫ fibreι p t = b ≫ fibreι p t) (h₂ : a ≫ fibreProj p t = b ≫ fibreProj p t) :
    a = b :=
  pullback.hom_ext h₁ h₂

end Fibre

section FibreMap

variable {𝒳 𝒴 : Scheme.{u}} {p : 𝒳 ⟶ T} {q : 𝒴 ⟶ T} (f : 𝒳 ⟶ 𝒴) (h : f ≫ q = p)
  (t : ParameterPoint T)

/-- The morphism of fibres `f_t : X_t → Y_t` induced by a morphism `f : 𝒳 → 𝒴` of schemes over
`T` at a parameter point `t ∈ T` (Fulton, §10.1): the base change of `f` along `t : {t} → T`. -/
def fibreMap : fibre p t ⟶ fibre q t :=
  pullback.map p t.ι q t.ι f (𝟙 _) (𝟙 _) (by simp [h]) (by simp)

/-- `f_t` commutes with the inclusions of the fibres: `f_t ≫ i_t = i_t ≫ f`. -/
@[reassoc (attr := simp)]
theorem fibreMap_fibreι : fibreMap f h t ≫ fibreι q t = fibreι p t ≫ f :=
  pullback.lift_fst _ _ _

/-- `f_t` commutes with the projections to `{t}`: it is a morphism of `κ(t)`-schemes. -/
@[reassoc (attr := simp)]
theorem fibreMap_fibreProj : fibreMap f h t ≫ fibreProj q t = fibreProj p t :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The morphism of fibres `f_t : X_t → Y_t` is a morphism over `{t}`. -/
instance isOver_fibreMap : (fibreMap f h t).IsOver t.spec :=
  ⟨fibreMap_fibreProj f h t⟩

/-- `X_t = 𝒳 ×_𝒴 Y_t`: the morphism of fibres `f_t`, the inclusions `i_t` and `f` form a fibre
square. -/
theorem isPullback_fibreMap : IsPullback (fibreMap f h t) (fibreι p t) (fibreι q t) f := by
  have hr : IsPullback (fibreProj q t) (fibreι q t) t.ι q := (isPullback_fibre q t).flip
  have hbig : IsPullback (fibreMap f h t ≫ fibreProj q t) (fibreι p t) t.ι (f ≫ q) := by
    rw [fibreMap_fibreProj, h]
    exact (isPullback_fibre p t).flip
  exact IsPullback.of_right hbig (fibreMap_fibreι f h t) hr

/-- The morphism of fibres of the identity is the identity. -/
@[simp]
theorem fibreMap_id : fibreMap (𝟙 𝒳) (Category.id_comp p) t = 𝟙 _ :=
  fibre_hom_ext p t (by simp) (by simp)

/-- Taking fibres is functorial: `(g ∘ f)_t = g_t ∘ f_t`. -/
@[reassoc]
theorem fibreMap_comp {𝒵 : Scheme.{u}} {r : 𝒵 ⟶ T} (g : 𝒴 ⟶ 𝒵) (hg : g ≫ r = q) :
    fibreMap (f ≫ g) (by rw [Category.assoc, hg, h]) t = fibreMap f h t ≫ fibreMap g hg t :=
  fibre_hom_ext r t (by simp) (by simp)

end FibreMap

end ParameterPoint

end MMP
