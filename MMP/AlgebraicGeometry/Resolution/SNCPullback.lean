/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import MMP.RingTheory.RegularLocalRing.FlatRegularParameters
public import MMP.AlgebraicGeometry.Morphisms.Smooth.SmoothFlagParameters
public import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
public import MMP.AlgebraicGeometry.Resolution.SNCWithDivisorSmooth
public import StacksFrontier.AlgebraicGeometry.SyntomicBaseChange.FibreStalk
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.GeometricallyRegularNormal

/-!
# Smooth pull-back preserves the snc triples

Let `(X, I, E) ∈ 𝒯^snc`: `X` smooth of finite type over a field `k` of characteristic zero, `I`
nonzero at the generic points of `X` and `E = (E^1, …, E^s)` a divisor with ordered index set
whose sum is a simple normal crossing divisor. If `h : Y → X` is smooth and `Y` is of finite type
over `k`, then `(Y, h^*I, h⁻¹E) ∈ 𝒯^snc`.

Let `y ∈ Y` and `x = h(y)`. The map `𝒪_{X,x} → 𝒪_{Y,y}` is flat and local, and its closed fibre
`𝒪_{Y,y} / 𝔪_x 𝒪_{Y,y}` is the local ring at `y` of the fibre `h⁻¹(x)`, a scheme smooth over
`κ(x)`, hence regular. So if `z_1, …, z_n` are local coordinates at `x` with
`E^i = (z_{c(i)} = 0)` near `x`, then `h^*z_1, …, h^*z_n` extend to local coordinates at `y`, and
`h⁻¹E^i = (h^*z_{c(i)} = 0)` near `y`. A closed subscheme cut out near each of its points by one
member of a regular system of parameters has regular local rings, so it is reduced, smooth over a
perfect field, an effective Cartier divisor, and of pure codimension one: at the generic point
`η` of a component its local ring `𝒪_{Y,η} / (w)` has dimension zero, so `dim 𝒪_{Y,η} = 1`. For
the ideal, a flat morphism maps generic points of irreducible components of `Y` to generic
points of irreducible components of `X` (flat maps are generalizing), and a faithfully flat
local homomorphism is injective, so `(h^*I)_η = I_{h(η)} 𝒪_{Y,η} ≠ 0`.

## Main results

* `MMP.Resolution.isSNCFamily_comap_of_flat`: a simple normal crossing divisor pulls back to a
  simple normal crossing divisor along a morphism whose stalk maps are flat with regular closed
  fibres, the target being locally of finite type over a perfect field.
* `MMP.Resolution.isNonzeroAtGenericPoints_comap_of_flat`: along a flat morphism, the inverse
  image of an ideal sheaf nonzero at the generic points is nonzero at the generic points.
* `MMP.Resolution.isRegularLocalRing_closedFibre_of_smooth`: the closed fibres of the stalk maps
  of a smooth morphism are regular local rings.
* `MMP.Resolution.isPureCodimOne_support_of_stalk_eq_span_parameter` and its companions: closed
  subschemes locally cut out by one member of a regular system of parameters.
* `MMP.Resolution.pullback_mem_sncTriples`: smooth pull-back preserves `𝒯^snc`.

## Implementation notes

The pull-back of the snc divisor is stated for any morphism whose stalk maps are flat with
regular closed fibres, so that it applies also to field change `X_L → X`. The clauses on the
components of `h⁻¹E` (reduced, of pure codimension one, smooth) are deduced from the local
coordinates at the points of `Y`, not from the corresponding clauses for `E`.

Of the finite type of `Y` over `k`, only quasi-compactness of `Y → Spec k` is a hypothesis:
local finite type follows from that of `h` and of `X → Spec k`.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.24, 3.34.1, 3.35]
* [Stacks Project, Tag 00ON](https://stacks.math.columbia.edu/tag/00ON)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Resolution

/-! ### Local algebra -/

/-- The quotient of a regular local ring of dimension `m` by one member of a regular system of
parameters has dimension `m - 1`. -/
theorem ringKrullDim_quotient_span_singleton_of_isRegularSystemOfParameters {R : Type*}
    [CommRing R] [IsRegularLocalRing R] {m : ℕ} {w : Fin m → R}
    (hw : IsRegularSystemOfParameters w) (j : Fin m) :
    ringKrullDim (R ⧸ Ideal.span {w j}) = (m - 1 : ℕ) := by
  obtain ⟨-, hdim, -⟩ :=
    MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_quotient_image hw {j}
  have hs : w '' ((({j} : Finset (Fin m))) : Set (Fin m)) = {w j} := by simp
  rw [hs] at hdim
  simpa using hdim

/-- A member of a regular system of parameters of a Noetherian local ring is a
non-zero-divisor. -/
theorem isRegular_of_isRegularSystemOfParameters {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] {m : ℕ} {w : Fin m → R}
    (hw : IsRegularSystemOfParameters w) (j : Fin m) : IsRegular (w j) := by
  have := isRegularLocalRing_of_isRegularSystemOfParameters hw
  have := IsRegularLocalRing.isDomain R
  exact IsRegular.of_ne_zero (ne_zero_of_isRegularSystemOfParameters hw j)

/-! ### Closed subschemes cut out by one regular parameter -/

section Parameter

variable {Y : Scheme.{u}}

/-- A closed subscheme whose stalk ideal at each of its points is generated by one member of a
regular system of parameters is an effective Cartier divisor. -/
theorem isEffectiveCartierDivisor_of_stalk_eq_span_parameter [IsLocallyNoetherian Y]
    (D : Y.IdealSheafData)
    (hD : ∀ y ∈ D.support, ∃ (m : ℕ) (w : Fin m → Y.presheaf.stalk y) (j : Fin m),
      IsRegularSystemOfParameters w ∧ IdealSheafData.stalk D y = Ideal.span {w j}) :
    Stacks.Divisors.IsEffectiveCartierDivisor D :=
  isEffectiveCartierDivisor_of_stalk_regular_principal D fun y hy => by
    obtain ⟨m, w, j, hw, hy'⟩ := hD y hy
    exact ⟨w j, isRegular_of_isRegularSystemOfParameters hw j, hy'⟩

/-- A closed subscheme whose stalk ideal at each of its points is generated by one member of a
regular system of parameters has regular local rings. -/
theorem isRegularLocalRing_stalk_subscheme_of_stalk_eq_span_parameter [IsLocallyNoetherian Y]
    (D : Y.IdealSheafData)
    (hD : ∀ y ∈ D.support, ∃ (m : ℕ) (w : Fin m → Y.presheaf.stalk y) (j : Fin m),
      IsRegularSystemOfParameters w ∧ IdealSheafData.stalk D y = Ideal.span {w j})
    (z : D.subscheme) : IsRegularLocalRing (D.subscheme.presheaf.stalk z) := by
  have hz : D.subschemeι z ∈ D.support := by
    rw [← SetLike.mem_coe, ← D.range_subschemeι]
    exact ⟨z, rfl⟩
  obtain ⟨m, w, j, hw, hy'⟩ := hD _ hz
  have := isRegularLocalRing_of_isRegularSystemOfParameters hw
  apply isRegularLocalRing_stalk_subscheme_of_isRegularLocalRing_quotient
  rw [hy']
  exact isRegularLocalRing_quotient_span_singleton_of_isRegularSystemOfParameters hw j

/-- A closed subscheme whose stalk ideal at each of its points is generated by one member of a
regular system of parameters is reduced. -/
theorem isReduced_subscheme_of_stalk_eq_span_parameter [IsLocallyNoetherian Y]
    (D : Y.IdealSheafData)
    (hD : ∀ y ∈ D.support, ∃ (m : ℕ) (w : Fin m → Y.presheaf.stalk y) (j : Fin m),
      IsRegularSystemOfParameters w ∧ IdealSheafData.stalk D y = Ideal.span {w j}) :
    IsReduced D.subscheme := by
  have : ∀ z, _root_.IsReduced (D.subscheme.presheaf.stalk z) := fun z => by
    have := isRegularLocalRing_stalk_subscheme_of_stalk_eq_span_parameter D hD z
    have := IsRegularLocalRing.isDomain (D.subscheme.presheaf.stalk z)
    infer_instance
  exact isReduced_of_isReduced_stalk _

/-- A closed subscheme whose stalk ideal at each of its points is generated by one member of a
regular system of parameters is of pure codimension one. -/
theorem isPureCodimOne_support_of_stalk_eq_span_parameter [IsLocallyNoetherian Y]
    (D : Y.IdealSheafData)
    (hD : ∀ y ∈ D.support, ∃ (m : ℕ) (w : Fin m → Y.presheaf.stalk y) (j : Fin m),
      IsRegularSystemOfParameters w ∧ IdealSheafData.stalk D y = Ideal.span {w j}) :
    IsPureCodimOne D.support := by
  intro W hW
  set e := irreducibleSetEquivPoints (α := Y)
  have hWη : (W : Set Y) = closure {e W} := by
    conv_lhs => rw [← e.symm_apply_apply W]
    rfl
  have hηD : e W ∈ D.support := hW.1 (hWη ▸ subset_closure rfl)
  obtain ⟨z, hz⟩ : ∃ z, D.subschemeι z = e W := by
    rwa [← SetLike.mem_coe, ← D.range_subschemeι] at hηD
  have h1 : codimension W = Order.coheight (e W) := by
    change Order.coheight W = _
    rw [← Order.coheight_orderIso e W]
  rw [h1, ← hz]
  have hmax : IsMax z := by
    intro b hb
    rw [Scheme.le_iff_specializes] at hb ⊢
    have hb' : D.subschemeι b ⤳ e W := hz ▸ hb.map D.subschemeι.continuous
    have hbD : D.subschemeι b ∈ D.support := by
      rw [← SetLike.mem_coe, ← D.range_subschemeι]
      exact ⟨b, rfl⟩
    have hle : W ≤ e.symm (D.subschemeι b) := by
      rwa [← e.le_iff_le, e.apply_symm_apply, Scheme.le_iff_specializes]
    have hsub : ((e.symm (D.subschemeι b) : TopologicalSpace.IrreducibleCloseds Y) : Set Y) ⊆
        D.support := by
      change closure {D.subschemeι b} ⊆ _
      exact closure_minimal (Set.singleton_subset_iff.mpr hbD) D.support.isClosed
    have hge := hW.2 hsub hle
    rw [← e.le_iff_le, e.apply_symm_apply, Scheme.le_iff_specializes, ← hz] at hge
    exact D.subschemeι.isClosedEmbedding.isInducing.specializes_iff.mp hge
  have hz0 : ringKrullDim (D.subscheme.presheaf.stalk z) = 0 := by
    rw [ringKrullDim_stalk_eq_coheight, Order.coheight_eq_zero.mpr hmax]; rfl
  have hzD : D.subschemeι z ∈ D.support := hz ▸ hηD
  obtain ⟨m, w, j, hw, hy'⟩ := hD _ hzD
  have := isRegularLocalRing_of_isRegularSystemOfParameters hw
  have hdim := ringKrullDim_quotient_span_singleton_of_isRegularSystemOfParameters hw j
  rw [← hy', ringKrullDim_eq_of_ringEquiv (MMP.Flips.ResolutionInputs.stalkQuotientEquiv D z),
    hz0] at hdim
  have hm : m = 1 := by
    have := j.2
    have : m - 1 = 0 := by exact_mod_cast hdim.symm
    omega
  have h2 := hw.2
  rw [ringKrullDim_stalk_eq_coheight, hm] at h2
  exact_mod_cast h2

/-- Over a perfect field, a closed subscheme of a scheme locally of finite type whose stalk ideal
at each of its points is generated by one member of a regular system of parameters is smooth. -/
theorem isSmoothScheme_subscheme_of_stalk_eq_span_parameter {k : Type u} [Field k]
    [PerfectField k] (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (D : Y.IdealSheafData)
    (hD : ∀ y ∈ D.support, ∃ (m : ℕ) (w : Fin m → Y.presheaf.stalk y) (j : Fin m),
      IsRegularSystemOfParameters w ∧ IdealSheafData.stalk D y = Ideal.span {w j}) :
    IsSmoothScheme (D.subschemeι ≫ sY) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : LocallyOfFinitePresentation (D.subschemeι ≫ sY) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := D.subschemeι ≫ sY)).mpr
      inferInstance
  rw [isSmoothScheme_iff, MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk]
  exact isRegularLocalRing_stalk_subscheme_of_stalk_eq_span_parameter D hD

end Parameter

/-- The coordinate clause of a simple normal crossing divisor: at every point of `E^i`, the stalk
of `E^i` is generated by one member of a regular system of parameters. -/
theorem IsSNCFamily.exists_stalk_eq_span_parameter {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {Λ : Type*} {E : Λ → X.IdealSheafData} (hE : IsSNCFamily sX E)
    (i : Λ) : ∀ x ∈ (E i).support, ∃ (m : ℕ) (w : Fin m → X.presheaf.stalk x) (j : Fin m),
      IsRegularSystemOfParameters w ∧ IdealSheafData.stalk (E i) x = Ideal.span {w j} := by
  intro x hx
  obtain ⟨n, z, c, hz, hc, -⟩ := hE.2 x
  exact ⟨n, z, c ⟨i, hx⟩, hz, hc ⟨i, hx⟩⟩

/-! ### Pull-back along flat morphisms with regular closed fibres -/

section Pullback

variable {X Y : Scheme.{u}}

/-- A point lies on the inverse image `h⁻¹Z` exactly when its image lies on `Z`. -/
theorem mem_support_comap_iff (h : Y ⟶ X) (I : X.IdealSheafData) (y : Y) :
    y ∈ (I.comap h).support ↔ h y ∈ I.support := by
  rw [Scheme.IdealSheafData.support_comap]
  rfl

/-- The closed fibre `𝒪_{Y,y} / 𝔪_{h(y)} 𝒪_{Y,y}` of the stalk map of a smooth morphism
`h : Y → X` is a regular local ring: it is the local ring at `y` of the fibre `h⁻¹(h(y))`, a
scheme smooth over the residue field `κ(h(y))`. -/
theorem isRegularLocalRing_closedFibre_of_smooth (h : Y ⟶ X) [Smooth h] (y : Y) :
    letI := (h.stalkMap y).hom.toAlgebra
    IsRegularLocalRing (ClosedFibre (X.presheaf.stalk (h y)) (Y.presheaf.stalk y)) := by
  let := (h.stalkMap y).hom.toAlgebra
  have hs : Smooth (h.fiberToSpecResidueField (h y)) :=
    MorphismProperty.of_isPullback (P := @Smooth)
      (IsPullback.of_hasPullback h (X.fromSpecResidueField (h y))) ‹Smooth h›
  have hreg := ((isRegular_tfae (h.fiber (h y))).out 1 2).mp
    (@isRegular_of_smooth_over_field (X.residueField (h y)) _ _
      (h.fiberToSpecResidueField (h y)) hs)
  have := hreg.2 (h.asFiber y)
  exact IsRegularLocalRing.of_ringEquiv (quotientStalkEquivFiberStalk h y).symm

/-- **Coordinates pull back along a flat local map with regular closed fibre.** Let
`h : Y → X`, `y ∈ Y`, with `𝒪_{X,h(y)} → 𝒪_{Y,y}` flat and closed fibre regular. If
`z_1, …, z_n` are local coordinates at `h(y)` with `E^i = (z_{c(i)} = 0)` at `h(y)` for the `E^i`
through `h(y)`, `c` injective, then there are local coordinates at `y` (the `h^*z_m` followed by
lifts of coordinates of the closed fibre) with `h⁻¹E^i = (h^*z_{c(i)} = 0)` at `y` for the
`h⁻¹E^i` through `y`. -/
theorem exists_coordinates_comap_of_flat (h : Y ⟶ X) (y : Y)
    [IsNoetherianRing (X.presheaf.stalk (h y))] [IsNoetherianRing (Y.presheaf.stalk y)]
    (hflat : (h.stalkMap y).hom.Flat)
    (hfib : letI := (h.stalkMap y).hom.toAlgebra
      IsRegularLocalRing (ClosedFibre (X.presheaf.stalk (h y)) (Y.presheaf.stalk y)))
    {Λ : Type*} (E : Λ → X.IdealSheafData) {n : ℕ} {z : Fin n → X.presheaf.stalk (h y)}
    {c : {i // h y ∈ (E i).support} → Fin n} (hz : IsRegularSystemOfParameters z)
    (hE : ∀ i, IdealSheafData.stalk (E i.1) (h y) = Ideal.span {z (c i)})
    (hc : Function.Injective c) :
    ∃ (m : ℕ) (w : Fin m → Y.presheaf.stalk y)
      (c' : {i // y ∈ ((E i).comap h).support} → Fin m),
      IsRegularSystemOfParameters w ∧
        (∀ i, IdealSheafData.stalk ((E i.1).comap h) y = Ideal.span {w (c' i)}) ∧
        Function.Injective c' := by
  let := (h.stalkMap y).hom.toAlgebra
  have : IsLocalHom (algebraMap (X.presheaf.stalk (h y)) (Y.presheaf.stalk y)) :=
    inferInstanceAs (IsLocalHom (h.stalkMap y).hom)
  have : Module.Flat (X.presheaf.stalk (h y)) (Y.presheaf.stalk y) := hflat
  obtain ⟨s, bbar, hb⟩ := exists_isRegularSystemOfParameters
    (ClosedFibre (X.presheaf.stalk (h y)) (Y.presheaf.stalk y))
  choose b hbb using fun j => Ideal.Quotient.mk_surjective (bbar j)
  have hw := MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_append_of_flat hz hb
    (b := b) (funext hbb)
  have hmem : ∀ i : {i // y ∈ ((E i).comap h).support}, h y ∈ (E i.1).support :=
    fun i => (mem_support_comap_iff h _ y).1 i.2
  refine ⟨n + s, _, fun i => Fin.castAdd s (c ⟨i.1, hmem i⟩), hw, fun i => ?_,
    fun _ _ hij => Subtype.ext (congrArg Subtype.val (hc (Fin.castAdd_injective _ _ hij)) :)⟩
  rw [IdealSheafData.stalk_comap, hE ⟨i.1, hmem i⟩, Ideal.map_span, Set.image_singleton,
    Fin.append_left]
  rfl

/-- **Simple normal crossing divisors pull back along flat morphisms with regular closed
fibres.** Let `h : Y → X` be a morphism whose stalk maps are flat with regular closed fibres, `X`
locally Noetherian and `Y` locally of finite type over a perfect field `L`. If
`E = ∑ᵢ E^i` is a simple normal crossing divisor on `X` over a field `k`, then
`h⁻¹E = ∑ᵢ h⁻¹E^i` is a simple normal crossing divisor on `Y` over `L`. -/
theorem isSNCFamily_comap_of_flat {k L : Type u} [Field k] [Field L] [PerfectField L]
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of L)) [IsLocallyNoetherian X]
    [LocallyOfFiniteType sY] (h : Y ⟶ X) (hflat : ∀ y, (h.stalkMap y).hom.Flat)
    (hfib : ∀ y, letI := (h.stalkMap y).hom.toAlgebra
      IsRegularLocalRing (ClosedFibre (X.presheaf.stalk (h y)) (Y.presheaf.stalk y)))
    {Λ : Type*} {E : Λ → X.IdealSheafData} (hE : IsSNCFamily sX E) :
    IsSNCFamily sY (fun i => (E i).comap h) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have hcoord : ∀ y : Y, ∃ (n : ℕ) (z : Fin n → Y.presheaf.stalk y)
      (c : {i // y ∈ ((E i).comap h).support} → Fin n),
      IsRegularSystemOfParameters z ∧
        (∀ i, IdealSheafData.stalk ((E i.1).comap h) y = Ideal.span {z (c i)}) ∧
        Function.Injective c := by
    intro y
    obtain ⟨n, z, c, hz, hc, hinj⟩ := hE.2 (h y)
    exact exists_coordinates_comap_of_flat h y (hflat y) (hfib y) E hz hc hinj
  have hD : ∀ i, ∀ y ∈ ((E i).comap h).support, ∃ (m : ℕ) (w : Fin m → Y.presheaf.stalk y)
      (j : Fin m), IsRegularSystemOfParameters w ∧
        IdealSheafData.stalk ((E i).comap h) y = Ideal.span {w j} := by
    intro i y hy
    obtain ⟨n, z, c, hz, hc, -⟩ := hcoord y
    exact ⟨n, z, c ⟨i, hy⟩, hz, hc ⟨i, hy⟩⟩
  exact ⟨fun i => ⟨isReduced_subscheme_of_stalk_eq_span_parameter _ (hD i),
    isPureCodimOne_support_of_stalk_eq_span_parameter _ (hD i),
    isSmoothScheme_subscheme_of_stalk_eq_span_parameter sY _ (hD i)⟩, hcoord⟩

/-- In a quasi-sober space, `closure {x}` is an irreducible component exactly when every
generization of `x` is a specialization of `x`. -/
theorem closure_singleton_mem_irreducibleComponents_iff {T : Type*} [TopologicalSpace T]
    [QuasiSober T] (x : T) :
    closure {x} ∈ irreducibleComponents T ↔ ∀ ξ, ξ ⤳ x → x ⤳ ξ := by
  refine ⟨fun hx ξ hξ => specializes_iff_mem_closure.mpr
    (hx.2 isIrreducible_singleton.closure hξ.closure_subset (subset_closure rfl)),
    fun hx => ⟨isIrreducible_singleton.closure, fun S hS hxS => ?_⟩⟩
  have hg := hS.isGenericPoint_genericPoint_closure
  have hξx : hS.genericPoint ⤳ x := by
    rw [specializes_iff_mem_closure, hg.def]
    exact subset_closure (hxS (subset_closure rfl))
  calc S ⊆ closure S := subset_closure
    _ = closure {hS.genericPoint} := hg.def.symm
    _ ⊆ closure {x} := (hx _ hξx).closure_subset

/-- Under a generalizing map of quasi-sober spaces (for instance a flat morphism of schemes),
the image of the generic point of an irreducible component is the generic point of an
irreducible component. -/
theorem closure_singleton_image_mem_irreducibleComponents {T T' : Type*} [TopologicalSpace T]
    [TopologicalSpace T'] [QuasiSober T] [QuasiSober T'] {f : T → T'} (hf : Continuous f)
    (hgen : GeneralizingMap f) {η : T} (hη : closure {η} ∈ irreducibleComponents T) :
    closure {f η} ∈ irreducibleComponents T' := by
  rw [closure_singleton_mem_irreducibleComponents_iff] at hη ⊢
  intro ξ hξ
  obtain ⟨ξ', hξ', rfl⟩ := hgen hξ
  exact (hη ξ' hξ').map hf

/-- **The ideal clause pulls back along flat morphisms.** If `I` is nonzero at the generic
points of the irreducible components of `X` and `h : Y → X` is flat, then `h^*I` is nonzero at
the generic points of the irreducible components of `Y`. -/
theorem isNonzeroAtGenericPoints_comap_of_flat (h : Y ⟶ X) [Flat h] {I : X.IdealSheafData}
    (hI : IsNonzeroAtGenericPoints I) : IsNonzeroAtGenericPoints (I.comap h) := by
  intro η hη hbot
  apply hI (h η) (closure_singleton_image_mem_irreducibleComponents h.continuous
    (Flat.generalizingMap h) hη)
  let := (h.stalkMap η).hom.toAlgebra
  have : IsLocalHom (algebraMap (X.presheaf.stalk (h η)) (Y.presheaf.stalk η)) :=
    inferInstanceAs (IsLocalHom (h.stalkMap η).hom)
  have : Module.Flat (X.presheaf.stalk (h η)) (Y.presheaf.stalk η) := Flat.stalkMap h η
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := X.presheaf.stalk (h η))
    (B := Y.presheaf.stalk η)
  refine eq_bot_iff.2 fun a ha => Ideal.mem_bot.2 <|
    FaithfulSMul.algebraMap_injective (X.presheaf.stalk (h η)) (Y.presheaf.stalk η) ?_
  have : (h.stalkMap η).hom a ∈ IdealSheafData.stalk (I.comap h) η := by
    rw [IdealSheafData.stalk_comap]
    exact Ideal.mem_map_of_mem _ ha
  rw [hbot, Ideal.mem_bot] at this
  rwa [map_zero]

end Pullback

/-! ### Smooth pull-back of snc triples -/

/-- **Smooth pull-back preserves the domain `𝒯^snc`** (implicit in Kollár 3.34.1 and 3.35(4)).
Let `(X, I, E) ∈ 𝒯^snc` and `h : Y → X` a smooth morphism with `Y` of finite type over `k`. Then
`(Y, h^*I, h⁻¹E) ∈ 𝒯^snc`. (`Y → Spec k` is locally of finite type because `h` is; only its
quasi-compactness is assumed.) -/
@[mmp "lem_kr3b_smooth_pullback_snc"]
theorem pullback_mem_sncTriples {t : FieldBlowupTriple.{u}} (ht : t ∈ sncTriples)
    {Y : Scheme.{u}} (h : Y ⟶ t.X) [Smooth h] [QuasiCompact (h ≫ t.sX)] :
    t.pullback h ∈ sncTriples := by
  obtain ⟨hchar, hsm, hlft, -, hI, -, hE⟩ := ht
  have : IsLocallyNoetherian t.X := LocallyOfFiniteType.isLocallyNoetherian t.sX
  have : Smooth t.sX := (isSmoothScheme_iff _).1 hsm
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (h ≫ t.sX)
  have hY : IsSNCFamily (h ≫ t.sX) (fun i => (t.E.E i).comap h) :=
    isSNCFamily_comap_of_flat t.sX (h ≫ t.sX) h (fun y => Flat.stalkMap h y)
      (isRegularLocalRing_closedFibre_of_smooth h) hE
  show CharZero t.k ∧ IsSmoothScheme (h ≫ t.sX) ∧ LocallyOfFiniteType (h ≫ t.sX) ∧
    QuasiCompact (h ≫ t.sX) ∧ IsNonzeroAtGenericPoints (t.I.comap h) ∧
    (t.E.comap h).IsOrderedDivisor ∧ (t.E.comap h).IsSNC (h ≫ t.sX)
  exact ⟨hchar, (isSmoothScheme_iff _).2 inferInstance, inferInstance, inferInstance,
    isNonzeroAtGenericPoints_comap_of_flat h hI,
    fun i => ⟨isReduced_subscheme_of_stalk_eq_span_parameter _
        (hY.exists_stalk_eq_span_parameter i),
      isEffectiveCartierDivisor_of_stalk_eq_span_parameter _
        (hY.exists_stalk_eq_span_parameter i)⟩, hY⟩

end MMP.Resolution
